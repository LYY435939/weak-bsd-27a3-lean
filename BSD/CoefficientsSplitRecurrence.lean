import BSD.CoefficientsSplitDivision
import BSD.CoefficientsPrimeTheta

/-! Split-prime recurrences by inclusion-exclusion on the two primary divisors. -/

noncomputable section

open Finset

namespace EtaSplit

/-- Weighted inclusion-exclusion for two embedded copies of `Y` covering `X`,
    whose overlap is an embedded copy of `Z`.  The three pointwise weight
    identities yield the local prime-power recurrence over any commutative ring. -/
theorem sum_two_images_recurrence
    {X Y Z R : Type*} [DecidableEq X] [CommRing R]
    (sX : Finset X) (sY : Finset Y) (sZ : Finset Z)
    (f g : Y → X) (h : Z → X)
    (hf : Set.InjOn f (sY : Set Y)) (hg : Set.InjOn g (sY : Set Y))
    (hh : Set.InjOn h (sZ : Set Z))
    (hcover : sY.image f ∪ sY.image g = sX)
    (hoverlap : sY.image f ∩ sY.image g = sZ.image h)
    (w : X → R) (v : Y → R) (u : Z → R) (A B : R)
    (hfw : ∀ y ∈ sY, w (f y) = A * v y)
    (hgw : ∀ y ∈ sY, w (g y) = B * v y)
    (hhw : ∀ z ∈ sZ, w (h z) = (A * B) * u z) :
    ∑ x ∈ sX, w x =
      (A + B) * (∑ y ∈ sY, v y) - (A * B) * (∑ z ∈ sZ, u z) := by
  have hfSum : ∑ x ∈ sY.image f, w x = A * (∑ y ∈ sY, v y) := by
    rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y hy => hfw y hy)
    · exact hf
  have hgSum : ∑ x ∈ sY.image g, w x = B * (∑ y ∈ sY, v y) := by
    rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y hy => hgw y hy)
    · exact hg
  have hhSum : ∑ x ∈ sZ.image h, w x = (A*B) * (∑ z ∈ sZ, u z) := by
    rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z hz => hhw z hz)
    · exact hh
  have hincl := Finset.sum_union_inter (s₁ := sY.image f) (s₂ := sY.image g) (f := w)
  rw [hcover, hoverlap, hfSum, hgSum, hhSum] at hincl
  linear_combination hincl

/-- The weighted tally of a finite norm fiber. -/
def CMTally {F : ℤ → Type*} {R : Type*} [CommRing R]
    (weight : ∀ n, F n → R) (n : ℤ) : R := ∑ᶠ x : F n, weight n x

/-- Fiber-level assembly of the split-prime recurrence.  This theorem leaves the
lattice facts (injectivity, cover, overlap, multiplicativity of weight, and
conjugate product) as explicit hypotheses, with the same dependent types as
`multFiber`, `conjFiber`, `cover_fiber`, and `inter_fiber`. -/
theorem cmTally_split_recurrence
    {F : ℤ → Type*} {R : Type*} [CommRing R]
    (p n : ℤ) (z zbar : F p)
    (mult : ∀ {m n : ℤ}, F m → F n → F (m*n))
    (weight : ∀ n : ℤ, F n → R)
    [Finite (F n)] [Finite (F (p*n))] [Finite (F (p*(p*n)))]
    (hinj : ∀ {m k : ℤ} (x : F m), m ≠ 0 → Function.Injective (mult (n := k) x))
    (hp : p ≠ 0)
    (cover : ∀ v : F (p*(p*n)),
      (∃ y : F (p*n), mult z y = v) ∨ ∃ y : F (p*n), mult zbar y = v)
    (inter : ∀ v : F (p*(p*n)),
      ((∃ y : F (p*n), mult z y = v) ∧ (∃ y : F (p*n), mult zbar y = v)) ↔
        ∃ y : F n, mult z (mult zbar y) = v)
    (hmul : ∀ {m k : ℤ} (x : F m) (y : F k),
      weight (m*k) (mult x y) = weight m x * weight k y)
    (hproduct : weight p z * weight p zbar = (p : R)) :
    CMTally weight (p*(p*n)) = (weight p z + weight p zbar) * CMTally weight (p*n)
      - (p : R) * CMTally weight n := by
  classical
  let : Fintype (F n) := Fintype.ofFinite _
  let : Fintype (F (p*n)) := Fintype.ofFinite _
  let : Fintype (F (p*(p*n))) := Fintype.ofFinite _
  let f : F (p*n) → F (p*(p*n)) := mult z
  let g : F (p*n) → F (p*(p*n)) := mult zbar
  let h : F n → F (p*(p*n)) := fun y => mult z (mult zbar y)
  have hf : Function.Injective f := hinj z hp
  have hg : Function.Injective g := hinj zbar hp
  have hh : Function.Injective h := hf.comp (hinj zbar hp)
  have hc : (Finset.univ : Finset (F (p*n))).image f ∪ Finset.univ.image g = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact cover v
  have hi : (Finset.univ : Finset (F (p*n))).image f ∩ Finset.univ.image g =
      (Finset.univ : Finset (F n)).image h := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and]
    exact inter v
  have hrecur := sum_two_images_recurrence
    (Finset.univ : Finset (F (p*(p*n)))) (Finset.univ : Finset (F (p*n)))
    (Finset.univ : Finset (F n)) f g h hf.injOn hg.injOn hh.injOn hc hi
    (weight _) (weight _) (weight _) (weight p z) (weight p zbar)
    (by intro y hy; exact hmul z y)
    (by intro y hy; exact hmul zbar y)
    (by intro y hy; dsimp [h]; rw [hmul, hmul]; ring)
  rw [hproduct] at hrecur
  unfold CMTally
  rw [finsum_eq_finsetSum_of_support_subset (weight (p*(p*n))) (s := Finset.univ) (by simp),
      finsum_eq_finsetSum_of_support_subset (weight (p*n)) (s := Finset.univ) (by simp),
      finsum_eq_finsetSum_of_support_subset (weight n) (s := Finset.univ) (by simp)]
  exact hrecur

/-- Sum and product of the two conjugate weights, for an arbitrary cubic root. -/
theorem conjugate_weight_sum {R : Type*} [CommRing R] (w : R) (a b : ℤ) :
    ((a : R) + (b : R)*w) + (((a-b : ℤ) : R) + ((-b : ℤ) : R)*w) =
      ((2*a-b : ℤ) : R) := by
  push_cast
  ring

theorem conjugate_weight_mul {R : Type*} [CommRing R] (w : R)
    (hw : w^2 + w + 1 = 0) (a b : ℤ) :
    ((a : R) + (b : R)*w) * (((a-b : ℤ) : R) + ((-b : ℤ) : R)*w) =
      ((a^2-a*b+b^2 : ℤ) : R) := by
  push_cast
  linear_combination -(b : R)^2 * hw

end EtaSplit

namespace BSD.CMTheta
open BSD.CMSplit

/-- The Hecke recurrence at every split prime for the primary theta coefficients, with the
linear coefficient computed from the point count of the fixed elliptic curve. -/
theorem primaryCoeff_split_recurrence {R : Type*} [CommRing R] (w : R) (hw : w^2+w+1=0)
    {p : ℕ} [hp : Fact p.Prime] (hs : p%3=1) (n : ℤ) :
    primaryCoeff w ((p:ℤ)*((p:ℤ)*n)) = primaryCoeff w (p:ℤ) * primaryCoeff w ((p:ℤ)*n)
      - (p:R) * primaryCoeff w n := by
  obtain ⟨a,b,ha,hb,hn,ht⟩ := FermatCubic.split_trace_primary_representation hs
  let z : CMSplit.Fiber (p:ℤ) := ⟨(a,b),ha,hb,hn⟩
  have hprod : weight w z.val * weight w (conjFiber z).val = ((p:ℤ):R) :=
    (EtaSplit.conjugate_weight_mul w hw a b).trans (congrArg (fun t:ℤ => (t:R)) hn)
  have hsum : weight w z.val + weight w (conjFiber z).val = primaryCoeff w (p:ℤ) := by
    rw [primaryCoeff_split_prime w hs, ht]
    exact EtaSplit.conjugate_weight_sum w a b
  have h := EtaSplit.cmTally_split_recurrence (F := CMSplit.Fiber) (p:ℤ) n z (conjFiber z)
    (@multFiber) (fun _ v => weight w v.val) (@multFiber_injective)
    (by exact_mod_cast hp.out.ne_zero) (cover_fiber z n) (inter_fiber hs z n)
    (fun {m k} x y => weight_mul w hw x.val y.val) hprod
  change primaryCoeff w ((p:ℤ)*((p:ℤ)*n)) =
    (weight w z.val + weight w (conjFiber z).val) * primaryCoeff w ((p:ℤ)*n) -
      ((p:ℤ):R) * primaryCoeff w n at h
  simpa only [hsum,Int.cast_natCast] using h

end BSD.CMTheta
