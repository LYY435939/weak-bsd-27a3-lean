import BSD.InertPrimes
import BSD.CMThetaIdentity
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

namespace BSD.FermatCubic

/-- Integral Eisenstein coordinates of prescribed norm, with residues `(1, 0)` modulo three. -/
def primaryThetaFiber (n : ℤ) :=
  {z : ℤ × ℤ // 3 ∣ z.1 - 1 ∧ 3 ∣ z.2 ∧ z.1 ^ 2 - z.1 * z.2 + z.2 ^ 2 = n}

/-- The linear-weighted coefficient contributed by all primary coordinates of norm `n`. -/
noncomputable def primaryThetaCoeff {R : Type*} [CommRing R] (w : R) (n : ℤ) : R :=
  ∑ᶠ z : primaryThetaFiber n, ((z.val.1 : R) + (z.val.2 : R) * w)

private theorem primary_fst_iff (a : ℤ) : 3 ∣ a - 1 ↔ (a : ZMod 3) = 1 := by
  rw [← sub_eq_zero, ← Int.cast_one (R := ZMod 3), ← Int.cast_sub,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  rfl

private theorem primary_snd_iff (b : ℤ) : 3 ∣ b ↔ (b : ZMod 3) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).symm

/-- The existing primary norm fiber supplies the finiteness instance. -/
theorem primaryThetaFiber_finite (n : ℤ) : Finite (primaryThetaFiber n) :=
  inferInstanceAs (Finite (CMTheta.PrimaryFiber n))

/-- If a prime is two modulo three and divides an Eisenstein norm, it divides both coordinates. -/
theorem inert_dvd_coords_of_dvd_norm {p : ℕ} [hp : Fact p.Prime] (hp₂ : p % 3 = 2)
    {a b : ℤ} (h : (p : ℤ) ∣ a ^ 2 - a * b + b ^ 2) :
    (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
  have hn : (a : ZMod p) ^ 2 - (a : ZMod p) * b + (b : ZMod p) ^ 2 = 0 := by
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_pow, Int.cast_mul] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
  have hcube : (-(a : ZMod p)) ^ 3 = (b : ZMod p) ^ 3 := by
    linear_combination -((a : ZMod p) + b) * hn
  have ha := neg_eq_iff_eq_neg.mp ((cube_bijective hp₂).injective hcube)
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 h
    rcases Nat.dvd_prime Nat.prime_three |>.mp hd with hp₁ | hp₃
    · exact hp.out.ne_one hp₁
    · omega
  have hb : (b : ZMod p) = 0 := by
    rw [ha] at hn
    have h : (3 : ZMod p) * (b : ZMod p) ^ 2 = 0 := by linear_combination hn
    exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h).resolve_left hthree)
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp (by simp [ha, hb]),
    (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb⟩

private theorem norm_scale (r a b : ℤ) :
    (r*a)^2 - (r*a)*(r*b) + (r*b)^2 = r^2*(a^2-a*b+b^2) := by ring

private theorem primary_mul_iff {s a b : ℤ} (hs : (s : ZMod 3) = 1) :
    (3 ∣ s*a-1 ∧ 3 ∣ s*b) ↔ (3 ∣ a-1 ∧ 3 ∣ b) := by
  simp only [primary_snd_iff, Int.cast_sub, Int.cast_one, Int.cast_mul, hs, one_mul]

/-- Scaling by `-p` gives every primary coordinate pair of norm `p²*n` exactly once. -/
noncomputable def primaryThetaFiber_inert_equiv {p : ℕ} [hp : Fact p.Prime]
    (hp₂ : p % 3 = 2) (n : ℤ) :
    primaryThetaFiber n ≃ primaryThetaFiber ((p : ℤ)^2 * n) := by
  let s : ℤ := -(p : ℤ)
  have hs : (s : ZMod 3) = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff' p 2 3).mpr hp₂
    simp only [s, Int.cast_neg, Int.cast_natCast, h]
    decide
  have hs₀ : s ≠ 0 := by
    simpa [s] using (show (p : ℤ) ≠ 0 by exact_mod_cast hp.out.ne_zero)
  have hs₂ : s ^ 2 = (p : ℤ)^2 := by simp [s]
  let scale (z : primaryThetaFiber n) : primaryThetaFiber ((p : ℤ)^2 * n) :=
    ⟨(s * z.val.1, s * z.val.2), by
      have h := (primary_mul_iff hs).mpr ⟨z.property.1, z.property.2.1⟩
      refine ⟨h.1, h.2, ?_⟩
      rw [norm_scale, z.property.2.2, hs₂]⟩
  refine Equiv.ofBijective scale ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    exact Prod.ext
      (mul_left_cancel₀ hs₀ (congrArg (fun z : primaryThetaFiber _ ↦ z.val.1) h))
      (mul_left_cancel₀ hs₀ (congrArg (fun z : primaryThetaFiber _ ↦ z.val.2) h))
  · rintro ⟨⟨a,b⟩, ha,hb,hn⟩
    have hnorm : (p : ℤ) ∣ a^2-a*b+b^2 := by
      rw [show a^2-a*b+b^2 = (p : ℤ)^2*n from hn, pow_two, mul_assoc]
      exact dvd_mul_right _ _
    obtain ⟨hpa,hpb⟩ := inert_dvd_coords_of_dvd_norm hp₂ hnorm
    obtain ⟨x, hx⟩ : s ∣ a := by simpa [s] using hpa
    obtain ⟨y, hy⟩ : s ∣ b := by simpa [s] using hpb
    change a = s*x at hx
    change b = s*y at hy
    have hxy : x^2-x*y+y^2 = n := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hs₀)
      change a^2-a*b+b^2 = _ at hn
      rwa [hx, hy, norm_scale, ← hs₂] at hn
    obtain ⟨ha',hb'⟩ := (primary_mul_iff (a := x) (b := y) hs).mp (hx ▸ hy ▸ ⟨ha,hb⟩)
    exact ⟨⟨(x,y), ha', hb', hxy⟩, Subtype.ext (Prod.ext hx.symm hy.symm)⟩

/-- For an inert prime, multiplying the norm by its square multiplies the coefficient by `-p`. -/
theorem primaryThetaCoeff_inert_mul_sq {R : Type*} [CommRing R] (w : R)
    {p : ℕ} [Fact p.Prime] (hp₂ : p % 3 = 2) (n : ℤ) :
    primaryThetaCoeff w ((p : ℤ)^2 * n) = -(p : R) * primaryThetaCoeff w n := by
  let e := primaryThetaFiber_inert_equiv hp₂ n
  let : Finite (primaryThetaFiber n) := primaryThetaFiber_finite n
  rw [primaryThetaCoeff, primaryThetaCoeff, ← finsum_comp_equiv e, mul_finsum' _ _ (Set.toFinite _)]
  apply congrArg finsum
  funext z
  change ((-(p : ℤ) * z.val.1 : ℤ) : R) + ((-(p : ℤ) * z.val.2 : ℤ) : R) * w =
      -(p : R) * ((z.val.1 : R) + (z.val.2 : R) * w)
  push_cast
  ring

/-- An inert prime appearing to exponent exactly one precludes a primary representation. -/
theorem primaryThetaFiber_inert_isEmpty {p : ℕ} [Fact p.Prime] (hp₂ : p % 3 = 2) {n : ℤ}
    (h : (p : ℤ) ∣ n) (h₂ : ¬ (p : ℤ)^2 ∣ n) : IsEmpty (primaryThetaFiber n) := by
  refine ⟨fun z ↦ h₂ ?_⟩
  obtain ⟨⟨a,b⟩, _, _, hn⟩ := z
  change a^2-a*b+b^2 = n at hn
  obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := inert_dvd_coords_of_dvd_norm hp₂ (hn.symm ▸ h)
  refine ⟨x^2-x*y+y^2, ?_⟩
  rw [← hn, hx, hy, norm_scale]

theorem primaryThetaCoeff_inert_zero_of_dvd_of_not_dvd_sq {R : Type*} [CommRing R] (w : R)
    {p : ℕ} [Fact p.Prime] (hp₂ : p % 3 = 2) {n : ℤ}
    (h : (p : ℤ) ∣ n) (h₂ : ¬ (p : ℤ)^2 ∣ n) : primaryThetaCoeff w n = 0 := by
  let := primaryThetaFiber_inert_isEmpty hp₂ h h₂
  exact finsum_of_isEmpty _

/-- All primary norms are one modulo three. -/
theorem primaryThetaFiber_norm_mod_three {n : ℤ} (z : primaryThetaFiber n) :
    (n : ZMod 3) = 1 := by
  obtain ⟨⟨a,b⟩,ha,hb,hn⟩ := z
  change a^2-a*b+b^2 = n at hn
  simp [← hn, (primary_fst_iff a).mp ha, (primary_snd_iff b).mp hb]

/-- No primary norm is divisible by the ramified prime three. -/
theorem primaryThetaFiber_ramified_isEmpty {n : ℤ} (h : 3 ∣ n) :
    IsEmpty (primaryThetaFiber n) :=
  ⟨fun z ↦ zero_ne_one
    (((primary_snd_iff n).mp h).symm.trans (primaryThetaFiber_norm_mod_three z))⟩

theorem primaryThetaCoeff_ramified_zero {R : Type*} [CommRing R] (w : R) {n : ℤ}
    (h : 3 ∣ n) : primaryThetaCoeff w n = 0 := by
  let := primaryThetaFiber_ramified_isEmpty h
  exact finsum_of_isEmpty _

/-- The only primary norm-one coordinates are `(1, 0)`. -/
theorem primaryThetaCoeff_one {R : Type*} [CommRing R] (w : R) :
    primaryThetaCoeff w 1 = 1 := by
  let one : primaryThetaFiber 1 := ⟨(1,0), by norm_num⟩
  have hunit (z : primaryThetaFiber 1) : z = one := by
    obtain ⟨⟨a,b⟩, ha,hb,hn⟩ := z
    change a^2-a*b+b^2 = 1 at hn
    have hb₀ : b = 0 := by
      obtain ⟨k, hk⟩ := hb
      change b = 3*k at hk
      by_contra h
      have hk₀ : k ≠ 0 := by intro hz; apply h; simp [hk, hz]
      have hk₁ : 1 ≤ k ^ 2 := by have := sq_pos_of_ne_zero hk₀; omega
      rw [hk] at hn
      nlinarith only [hn, hk₁, sq_nonneg (2*a-3*k)]
    have ha₁ : a = 1 := by
      have hasq : a^2 = 1 := by simpa [hb₀] using hn
      rcases sq_eq_one_iff.mp hasq with rfl | rfl
      · rfl
      · omega
    exact Subtype.ext (Prod.ext ha₁ hb₀)
  let : Unique (primaryThetaFiber 1) := ⟨⟨one⟩, hunit⟩
  rw [primaryThetaCoeff, finsum_unique]
  change ((1 : ℤ) : R) + ((0 : ℤ) : R) * w = 1
  simp

/-- The even powers of an inert prime have coefficient `(-p)^k`. -/
theorem primaryThetaCoeff_inert_pow_even {R : Type*} [CommRing R] (w : R)
    {p : ℕ} [Fact p.Prime] (hp₂ : p % 3 = 2) (k : ℕ) :
    primaryThetaCoeff w ((p : ℤ)^(2*k)) = (-(p : R))^k := by
  induction k with
  | zero => simpa using primaryThetaCoeff_one w
  | succ k ih =>
    rw [show 2*(k+1) = 2+2*k by omega, pow_add, primaryThetaCoeff_inert_mul_sq w hp₂, ih, pow_succ']

/-- The odd powers of an inert prime have coefficient zero. -/
theorem primaryThetaCoeff_inert_pow_odd {R : Type*} [CommRing R] (w : R)
    {p : ℕ} [hp : Fact p.Prime] (hp₂ : p % 3 = 2) (k : ℕ) :
    primaryThetaCoeff w ((p : ℤ)^(2*k+1)) = 0 := by
  induction k with
  | zero =>
    simp only [Nat.mul_zero, zero_add, pow_one]
    refine primaryThetaCoeff_inert_zero_of_dvd_of_not_dvd_sq w hp₂ dvd_rfl ?_
    intro h
    have h' : p^2 ∣ p^1 := by rw [pow_one]; exact_mod_cast h
    have := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h'
    omega
  | succ k ih =>
    rw [show 2*(k+1)+1 = 2+(2*k+1) by omega, pow_add,
      primaryThetaCoeff_inert_mul_sq w hp₂, ih, mul_zero]

/-- Every positive power of three has coefficient zero. -/
theorem primaryThetaCoeff_ramified_pow_succ {R : Type*} [CommRing R] (w : R) (k : ℕ) :
    primaryThetaCoeff w ((3 : ℤ)^(k+1)) = 0 :=
  primaryThetaCoeff_ramified_zero w (by rw [pow_succ']; exact dvd_mul_right _ _)

end BSD.FermatCubic
