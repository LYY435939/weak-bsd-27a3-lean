import BSD.CoefficientsPrimeTheta
import BSD.CoefficientsSplitDivision

noncomputable section
open Finset

namespace BSD.CMTheta

/-- Multiplication by a split prime coprime to the norm multiplies its primary theta
coefficient by the actual prime coefficient. -/
theorem primaryCoeff_split_mul_coprime
    {R : Type*} [CommRing R] (w : R) (hw : w^2+w+1=0)
    {p : ℕ} [hp : Fact p.Prime] (hs : p % 3 = 1) (n : ℤ)
    (hn : ¬(p:ℤ)∣n) :
    primaryCoeff w ((p:ℤ)*n) = primaryCoeff w (p:ℤ) * primaryCoeff w n := by
  classical
  obtain ⟨a,b,ha,hb,hnorm,htrace⟩ := FermatCubic.split_trace_primary_representation hs
  let z : CMSplit.Fiber (p:ℤ) := ⟨(a,b), ha,hb,hnorm⟩
  let zbar := CMSplit.conjFiber z
  let : Fintype (CMSplit.Fiber n) := Fintype.ofFinite _
  let : Fintype (CMSplit.Fiber ((p:ℤ)*n)) := Fintype.ofFinite _
  let f : CMSplit.Fiber n → CMSplit.Fiber ((p:ℤ)*n) := CMSplit.multFiber z
  let g : CMSplit.Fiber n → CMSplit.Fiber ((p:ℤ)*n) := CMSplit.multFiber zbar
  have hpz : (p:ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hf : Function.Injective f := CMSplit.multFiber_injective z hpz
  have hg : Function.Injective g := CMSplit.multFiber_injective zbar hpz
  have hc : (Finset.univ : Finset (CMSplit.Fiber n)).image f ∪ Finset.univ.image g =
      Finset.univ := by
    ext v
    simp only [mem_union, mem_image, mem_univ, true_and, iff_true]
    exact CMSplit.cover_any z n v
  have hd : Disjoint ((Finset.univ : Finset (CMSplit.Fiber n)).image f)
      (Finset.univ.image g) := by
    apply Finset.disjoint_left.mpr
    intro v hv1 hv2
    apply CMSplit.no_inter_fiber hs z n hn v
    simp only [mem_image, mem_univ, true_and] at hv1 hv2
    exact ⟨hv1,hv2⟩
  let W : CMSplit.Fiber ((p:ℤ)*n) → R := fun x => CMSplit.weight w x.val
  let V : CMSplit.Fiber n → R := fun x => CMSplit.weight w x.val
  have hfw (y : CMSplit.Fiber n) : W (f y) = CMSplit.weight w z.val * V y :=
    CMSplit.weight_mul w hw z.val y.val
  have hgw (y : CMSplit.Fiber n) : W (g y) = CMSplit.weight w zbar.val * V y :=
    CMSplit.weight_mul w hw zbar.val y.val
  have hsum : (∑ x : CMSplit.Fiber ((p:ℤ)*n), W x) =
      (CMSplit.weight w z.val + CMSplit.weight w zbar.val) *
      (∑ y : CMSplit.Fiber n, V y) := by
    rw [← hc, Finset.sum_union hd, Finset.sum_image hf.injOn, Finset.sum_image hg.injOn]
    simp_rw [hfw, hgw, ← Finset.mul_sum]
    ring
  have hweights : CMSplit.weight w z.val + CMSplit.weight w zbar.val = primaryCoeff w (p:ℤ) := by
    rw [primaryCoeff_split_prime w hs, htrace]
    change (a:R)+(b:R)*w + (((a-b:ℤ):R)+((-b:ℤ):R)*w) = ((2*a-b:ℤ):R)
    push_cast
    ring
  rw [hweights] at hsum
  change (∑ᶠ x : CMSplit.Fiber ((p:ℤ)*n), W x) = primaryCoeff w (p:ℤ) *
    (∑ᶠ y : CMSplit.Fiber n, V y)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  exact hsum

end BSD.CMTheta
