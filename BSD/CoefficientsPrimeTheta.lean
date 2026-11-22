import BSD.CoefficientsSplit
import BSD.CMThetaIdentity

/-! Prime coefficients of the sum over primary Eisenstein integers. -/

namespace BSD.FermatCubic

/-- The primary Eisenstein integers of norm a split prime form one conjugate pair of distinct
elements. Their trace is the Frobenius trace of the specified curve. -/
theorem split_primary_pairs {p : ℕ} [hp : Fact p.Prime] (hs : p % 3 = 1) :
    ∃ a b : ℤ, b ≠ 0 ∧ ((p : ℤ) + 1 - Nat.card (model (ZMod p)).toAffine.Point = 2*a-b) ∧
      ∀ c d : ℤ, (3 ∣ c-1 ∧ 3 ∣ d ∧ c^2-c*d+d^2=(p:ℤ)) ↔
        (c=a ∧ d=b) ∨ (c=a-b ∧ d= -b) := by
  obtain ⟨a,b,ha,hb,hn,ht⟩ := split_trace_primary_representation hs
  have hne : b ≠ 0 := by
    rintro rfl
    apply (Nat.prime_iff_prime_int.mp hp.out).not_isSquare
    exact ⟨a, by simpa [pow_two] using hn.symm⟩
  refine ⟨a,b,hne,ht, fun c d => ⟨?_, ?_⟩⟩
  · rintro ⟨hc,hd,hn'⟩
    have he := BSD.eisenstein_primary_trace_eq hp.out hn hn' ha hb hc hd
    have hsquare : d^2=b^2 := by
      have hx : 3*(d^2-b^2) = 0 := by
        linear_combination 4*(hn'-hn) + (2*a-b+2*c-d)*he
      omega
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hd' | hd'
    · exact Or.inl ⟨by omega, hd'⟩
    · exact Or.inr ⟨by omega, hd'⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨ha,hb,hn⟩
    · exact ⟨by omega, by omega, by linear_combination hn⟩

/-- The prime coefficient of the primary Eisenstein theta sum equals the point-count trace.
The terms containing the chosen root of unity cancel, so the identity holds for every weight
parameter in every commutative coefficient ring. -/
theorem finsum_primary_split {R : Type*} [CommRing R] (w : R) {p : ℕ} [Fact p.Prime]
    (hs : p % 3 = 1) :
    (∑ᶠ z : {z : ℤ × ℤ // 3 ∣ z.1-1 ∧ 3 ∣ z.2 ∧ z.1^2-z.1*z.2+z.2^2=(p:ℤ)},
      ((z.val.1 : R) + (z.val.2 : R)*w)) =
        (((p : ℤ) + 1 - Nat.card (model (ZMod p)).toAffine.Point : ℤ) : R) := by
  classical
  obtain ⟨a,b,hb,ht,hpairs⟩ := split_primary_pairs hs
  let S := {z : ℤ × ℤ // 3 ∣ z.1-1 ∧ 3 ∣ z.2 ∧ z.1^2-z.1*z.2+z.2^2=(p:ℤ)}
  let x : S := ⟨(a,b),(hpairs a b).mpr (Or.inl ⟨rfl,rfl⟩)⟩
  let y : S := ⟨(a-b,-b),(hpairs (a-b) (-b)).mpr (Or.inr ⟨rfl,rfl⟩)⟩
  have hxy : x ≠ y := by
    intro he
    have hb' : b = -b := congrArg (fun v : S => v.val.2) he
    omega
  let f (z : S) : R := (z.val.1 : R) + (z.val.2 : R)*w
  change (∑ᶠ z, f z) = _
  rw [finsum_eq_finsetSum_of_support_subset f (s := {x,y}) ?_, Finset.sum_pair hxy, ht]
  · change (a:R) + (b:R)*w + (((a-b:ℤ):R) + ((-b:ℤ):R)*w) = ((2*a-b:ℤ):R)
    push_cast
    ring
  · rintro ⟨⟨c,d⟩,hz⟩ _
    rcases (hpairs c d).mp hz with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Finset.mem_insert_self x _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)

end BSD.FermatCubic

namespace BSD.CMTheta

/-- The norm-p coefficient of the primary theta sum is the trace of the specified
elliptic curve at a split prime. -/
theorem primaryCoeff_split_prime {R : Type*} [CommRing R] (w : R) {p : ℕ} [Fact p.Prime]
    (hs : p % 3 = 1) :
    primaryCoeff w (p:ℤ) =
      (((p : ℤ) + 1 - Nat.card (FermatCubic.model (ZMod p)).toAffine.Point : ℤ) : R) :=
  FermatCubic.finsum_primary_split w hs

end BSD.CMTheta
