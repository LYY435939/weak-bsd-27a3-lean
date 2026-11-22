import BSD.CMThetaIdentity
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Tactic

/-!
# Multiplicativity of the primary Eisenstein theta coefficients

The Euclidean algorithm splits a primary Eisenstein integer of norm m*n
into factors of coprime norms m and n. Normalizing the factors modulo 3
makes the decomposition unique. Multiplication then identifies the norm
fibers and the theta weight respects their products.
-/

namespace BSD.CMTheta

abbrev Eisenstein := QuadraticAlgebra ℤ (-1) (-1)

namespace Eisenstein

theorem norm_formula (z : Eisenstein) : z.norm = z.re ^ 2 - z.re * z.im + z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]
  ring

theorem norm_nonneg (z : Eisenstein) : 0 ≤ z.norm := by
  rw [norm_formula]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im, sq_nonneg (z.re - z.im)]

theorem norm_eq_zero_iff {z : Eisenstein} : z.norm = 0 ↔ z = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [norm_formula] at h
  have hre : z.re = 0 := by
    by_contra hne
    nlinarith [sq_pos_of_ne_zero hne, sq_nonneg z.im, sq_nonneg (z.re - z.im)]
  have him : z.im = 0 := by
    rw [hre] at h
    simpa using h
  exact QuadraticAlgebra.ext hre him

theorem norm_pos {z : Eisenstein} (hz : z ≠ 0) : 0 < z.norm :=
  lt_of_le_of_ne (norm_nonneg z) (Ne.symm (mt norm_eq_zero_iff.mp hz))

theorem norm_cast_eq_mul_star (z : Eisenstein) : (z.norm : Eisenstein) = z * star z := by
  simpa using QuadraticAlgebra.algebraMap_norm_eq_mul_star z

private def quotient (x y : Eisenstein) : Eisenstein :=
  ⟨round ((x * star y).re / (y.norm : ℚ)),
   round ((x * star y).im / (y.norm : ℚ))⟩

private def remainder (x y : Eisenstein) : Eisenstein :=
  x - y * quotient x y

private theorem small_norm {a b : ℚ} (ha : |a| ≤ 1/2) (hb : |b| ≤ 1/2) :
    a ^ 2 - a * b + b ^ 2 < 1 := by
  have haa : a ^ 2 ≤ (1/2 : ℚ) ^ 2 := by
    apply (sq_le_sq).2
    simpa using ha
  have hbb : b ^ 2 ≤ (1/2 : ℚ) ^ 2 := by
    apply (sq_le_sq).2
    simpa using hb
  have hab : |a * b| ≤ (1/2 : ℚ) * (1/2) := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) (by norm_num)
  linarith [neg_abs_le (a * b)]

private theorem norm_remainder_lt (x y : Eisenstein) (hy : y ≠ 0) :
    (remainder x y).norm < y.norm := by
  let k := (y.norm : ℚ)
  have hk : 0 < k := by
    change 0 < (y.norm : ℚ)
    exact_mod_cast norm_pos hy
  have hk0 : (y.norm : ℚ) ≠ 0 := hk.ne'
  let u := x * star y
  let q := quotient x y
  let r := remainder x y
  have hs : r * star y = u - (y.norm : Eisenstein) * q := by
    change (x - y * q) * star y = x * star y - (y.norm : Eisenstein) * q
    rw [sub_mul, norm_cast_eq_mul_star, mul_right_comm y q (star y)]
  have ha : (((r * star y).re : ℤ) : ℚ) / k = (u.re : ℚ) / k - q.re := by
    rw [hs]
    simp [k]
    field_simp [hk0]
  have hb : (((r * star y).im : ℤ) : ℚ) / k = (u.im : ℚ) / k - q.im := by
    rw [hs]
    simp [k]
    field_simp [hk0]
  have hae : |(((r * star y).re : ℤ) : ℚ) / k| ≤ 1/2 := by
    rw [ha]
    exact abs_sub_round _
  have hbe : |(((r * star y).im : ℤ) : ℚ) / k| ≤ 1/2 := by
    rw [hb]
    exact abs_sub_round _
  have he := small_norm hae hbe
  have he' : (((r * star y).norm : ℤ) : ℚ) / k ^ 2 < 1 := by
    convert he using 1
    rw [norm_formula]
    push_cast
    ring
  rw [map_mul, QuadraticAlgebra.norm_star] at he'
  push_cast at he'
  have he'' : (r.norm : ℚ) * k < k ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hk)).mp he' |>.trans_eq (one_mul _)
  have hi : (r.norm : ℚ) < k :=
    lt_of_mul_lt_mul_right (by simpa [pow_two] using he'') hk.le
  change (r.norm : ℚ) < (y.norm : ℚ) at hi
  exact_mod_cast hi

instance : EuclideanDomain Eisenstein :=
  { (inferInstance : CommRing Eisenstein), (inferInstance : Nontrivial Eisenstein) with
    quotient := quotient
    remainder := remainder
    quotient_zero := by intro x; apply QuadraticAlgebra.ext <;> simp [quotient]
    quotient_mul_add_remainder_eq := by intro x y; simp [remainder]
    r := fun x y ↦ x.norm.natAbs < y.norm.natAbs
    r_wellFounded := (measure fun x : Eisenstein ↦ x.norm.natAbs).wf
    remainder_lt := by
      intro x y hy
      have h := norm_remainder_lt x y hy
      exact Int.ofNat_lt.mp (by simpa [Int.natAbs_of_nonneg (norm_nonneg _)] using h)
    mul_left_not_lt := by
      intro x y hy
      rw [map_mul, Int.natAbs_mul]
      exact not_lt_of_ge (Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr (norm_pos hy).ne')) }


/-- The algebraic norm as a natural number. -/
def natNorm (z : Eisenstein) : ℕ := z.norm.natAbs

theorem natNorm_mul (x y : Eisenstein) : natNorm (x * y) = natNorm x * natNorm y := by
  simp [natNorm, map_mul, Int.natAbs_mul]

theorem natNorm_eq_iff {z : Eisenstein} {n : ℕ} : natNorm z = n ↔ z.norm = (n : ℤ) := by
  rw [← Int.natCast_inj, natNorm, Int.natAbs_of_nonneg (norm_nonneg _)]

theorem natNorm_dvd {x y : Eisenstein} (h : x ∣ y) : natNorm x ∣ natNorm y := by
  obtain ⟨q, rfl⟩ := h
  rw [natNorm_mul]
  exact dvd_mul_right _ _

theorem dvd_natNorm (z : Eisenstein) : z ∣ (natNorm z : Eisenstein) := by
  refine ⟨star z, ?_⟩
  rw [← norm_cast_eq_mul_star, ← Int.cast_natCast]
  exact congrArg (fun i : ℤ ↦ (i : Eisenstein)) (Int.natAbs_of_nonneg (norm_nonneg z))

/-- Coprime positive norms split an Eisenstein integer into two factors of the given norms. -/
theorem exists_mul_of_natNorm {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hc : m.Coprime n)
    {z : Eisenstein} (hz : natNorm z = m * n) :
    ∃ a b : Eisenstein, z = a * b ∧ natNorm a = m ∧ natNorm b = n := by
  let a := EuclideanDomain.gcd z (m : Eisenstein)
  have ham : a ∣ (m : Eisenstein) := EuclideanDomain.gcd_dvd_right ..
  have ha0 : a ≠ 0 := by
    intro h
    have hm' : (m : Eisenstein) = 0 := by simpa [h] using ham
    exact hm.ne' (by simpa using congrArg QuadraticAlgebra.re hm')
  obtain ⟨b, hab⟩ := EuclideanDomain.gcd_dvd_left z (m : Eisenstein)
  change z = a * b at hab
  have hzd : z ∣ (m : Eisenstein) * (n : Eisenstein) := by
    simpa [hz] using dvd_natNorm z
  have haz : z ∣ a * (n : Eisenstein) := by
    change z ∣ EuclideanDomain.gcd z (m : Eisenstein) * (n : Eisenstein)
    rw [EuclideanDomain.gcd_eq_gcd_ab, add_mul, mul_right_comm _ (EuclideanDomain.gcdB ..)]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) (dvd_mul_of_dvd_left hzd _)
  obtain ⟨q, hq⟩ := haz
  have hbn : b ∣ (n : Eisenstein) := by
    refine ⟨q, mul_left_cancel₀ ha0 ?_⟩
    simpa only [hab, mul_assoc] using hq
  have had : natNorm a ∣ m ^ 2 := by
    simpa [natNorm] using natNorm_dvd ham
  have hbd : natNorm b ∣ n ^ 2 := by
    simpa [natNorm] using natNorm_dvd hbn
  have hp : natNorm a * natNorm b = m * n := by
    rw [← natNorm_mul, ← hab, hz]
  have had' : natNorm a ∣ m :=
    (Nat.Coprime.coprime_dvd_left had (hc.pow_left 2)).dvd_of_dvd_mul_right
      (hp ▸ dvd_mul_right _ _)
  have hbd' : natNorm b ∣ n :=
    (Nat.Coprime.coprime_dvd_left hbd (hc.symm.pow_left 2)).dvd_of_dvd_mul_left
      (hp ▸ dvd_mul_left _ _)
  have hleA := Nat.le_of_dvd hm had'
  have hleB := Nat.le_of_dvd hn hbd'
  have heqA : natNorm a = m := by
    refine hleA.antisymm (le_of_not_gt fun h ↦ ?_)
    have hlt := (Nat.mul_le_mul_left _ hleB).trans_lt (Nat.mul_lt_mul_of_pos_right h hn)
    rw [hp] at hlt
    exact (lt_irrefl _) hlt
  exact ⟨a, b, hab, heqA, Nat.mul_left_cancel hm (heqA ▸ hp)⟩

abbrev EisensteinModThree := QuadraticAlgebra (ZMod 3) (-1) (-1)

def modThree : Eisenstein →+* EisensteinModThree where
  toFun z := ⟨z.re, z.im⟩
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_one' := by apply QuadraticAlgebra.ext <;> norm_num [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by apply QuadraticAlgebra.ext <;> simp
  map_mul' x y := by apply QuadraticAlgebra.ext <;> simp

def IsPrimary (z : Eisenstein) : Prop := modThree z = 1

theorem isPrimary_iff {z : Eisenstein} : IsPrimary z ↔ (3 ∣ z.re - 1) ∧ (3 ∣ z.im) := by
  rw [IsPrimary, QuadraticAlgebra.ext_iff]
  change (((z.re : ℤ) : ZMod 3) = 1 ∧ ((z.im : ℤ) : ZMod 3) = 0) ↔ _
  have ha := ZMod.intCast_zmod_eq_zero_iff_dvd (z.re - 1) 3
  have hb := ZMod.intCast_zmod_eq_zero_iff_dvd z.im 3
  norm_num at ha hb
  rw [← ha, ← hb]
  simp [sub_eq_zero]

theorem IsPrimary.mul {x y : Eisenstein} (hx : IsPrimary x) (hy : IsPrimary y) :
    IsPrimary (x * y) := by
  unfold IsPrimary at *
  rw [map_mul, hx, hy, one_mul]

private def sixUnits (i : Fin 6) : Eisenstein :=
  ![(⟨1,0⟩ : Eisenstein), ⟨-1,0⟩, ⟨0,1⟩, ⟨0,-1⟩, ⟨-1,-1⟩, ⟨1,1⟩] i

private theorem natNorm_sixUnits (i : Fin 6) : natNorm (sixUnits i) = 1 := by
  fin_cases i <;> decide

private theorem exists_inverse_lift (x : EisensteinModThree) (h : x.norm ≠ 0) :
    ∃ i : Fin 6, modThree (sixUnits i) * x = 1 := by
  obtain ⟨a,b⟩ := x
  fin_cases a <;> fin_cases b <;> revert h <;> decide

private theorem mul_star_of_natNorm_eq_one {z : Eisenstein} (h : natNorm z = 1) :
    z * star z = 1 := by
  rw [← norm_cast_eq_mul_star, natNorm_eq_iff.mp h]
  norm_num

theorem eq_one_of_primary_natNorm_eq_one {z : Eisenstein} (hz : IsPrimary z)
    (hn : natNorm z = 1) : z = 1 := by
  obtain ⟨ha,hb⟩ := isPrimary_iff.mp hz
  have hn' : z.re ^ 2 - z.re * z.im + z.im ^ 2 = 1 := by
    simpa [norm_formula] using natNorm_eq_iff.mp hn
  have hb0 : z.im = 0 := by
    obtain ⟨k,hk⟩ := hb
    by_contra hne
    have hk0 : k ≠ 0 := by
      intro h
      exact hne (by simp [hk,h])
    have hk1 : 1 ≤ k^2 := by have := sq_pos_of_ne_zero hk0; omega
    have hsq : (2 * z.re - z.im)^2 + 3*z.im^2 = 4 := by
      linear_combination 4 * hn'
    rw [hk] at hsq
    nlinarith only [hsq,hk1,sq_nonneg (2*z.re - 3*k)]
  have ha1 : z.re = 1 := by
    have hs : z.re ^ 2 = 1 := by simpa [hb0] using hn'
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · rw [h] at ha
      norm_num at ha
  exact QuadraticAlgebra.ext ha1 hb0

/-- Adjust the factors with inverse units to obtain primary factors. -/
theorem exists_primary_mul_of_natNorm {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hc : m.Coprime n) {z : Eisenstein} (hz : natNorm z = m * n) (hp : IsPrimary z) :
    ∃ a b : Eisenstein, z = a * b ∧ natNorm a = m ∧ natNorm b = n ∧
      IsPrimary a ∧ IsPrimary b := by
  obtain ⟨a,b,hab,ha,hb⟩ := exists_mul_of_natNorm hm hn hc hz
  have hprod : modThree a * modThree b = 1 := by
    rw [← map_mul, ← hab]
    exact hp
  have hna : (modThree a).norm ≠ 0 := by
    intro h
    have he := congrArg QuadraticAlgebra.norm hprod
    simp [map_mul,h] at he
  obtain ⟨i,hi⟩ := exists_inverse_lift (modThree a) hna
  let u := sixUnits i
  have hu := natNorm_sixUnits i
  have hstar : natNorm (star u) = 1 := by
    unfold natNorm
    rw [QuadraticAlgebra.norm_star]
    exact hu
  have he : z = (u * a) * (star u * b) := by
    rw [mul_mul_mul_comm, mul_star_of_natNorm_eq_one hu, one_mul, hab]
  have hpa : IsPrimary (u * a) := by
    rw [IsPrimary, map_mul]
    exact hi
  refine ⟨u * a, star u * b, he, ?_, ?_, hpa, ?_⟩
  · rw [natNorm_mul, hu, one_mul, ha]
  · rw [natNorm_mul, hstar, one_mul, hb]
  · unfold IsPrimary at hp hpa ⊢
    rw [he, map_mul, hpa, one_mul] at hp
    exact hp

private theorem natCast_isCoprime {m n : ℕ} (hc : m.Coprime n) :
    IsCoprime (m : Eisenstein) (n : Eisenstein) := by
  have h : IsCoprime (m : ℤ) (n : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by
    simpa using hc.gcd_eq_one)
  simpa using h.map (Int.castRingHom Eisenstein)

/-- Primary factors with prescribed coprime norms are uniquely determined. -/
theorem primary_mul_unique {m n : ℕ} (hm : 0 < m) (hc : m.Coprime n)
    {a b c d : Eisenstein} (ha : natNorm a = m) (hb : natNorm b = n)
    (hd : natNorm c = m) (hpa : IsPrimary a) (hpc : IsPrimary c) (h : a * b = c * d) :
    a = c ∧ b = d := by
  have hcn : c ∣ (m : Eisenstein) := by simpa only [hd] using dvd_natNorm c
  have hbn : b ∣ (n : Eisenstein) := by simpa only [hb] using dvd_natNorm b
  have hcb : IsCoprime c b := ((natCast_isCoprime hc).of_isCoprime_of_dvd_left hcn).of_isCoprime_of_dvd_right hbn
  have hca : c ∣ a := hcb.dvd_of_dvd_mul_right ⟨d, h⟩
  obtain ⟨u,hu⟩ := hca
  have hun : natNorm u = 1 := by
    apply Nat.mul_left_cancel hm
    rw [← hd, ← natNorm_mul, ← hu, ha, hd, mul_one]
  have hup : IsPrimary u := by
    unfold IsPrimary at hpa hpc ⊢
    simpa only [hu, map_mul, hpc, one_mul] using hpa
  have he : a = c := by rw [hu, eq_one_of_primary_natNorm_eq_one hup hun, mul_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hz : natNorm (0 : Eisenstein) = 0 := by simp [natNorm]
    exact hm.ne' (hd.symm.trans hz)
  exact ⟨he, mul_left_cancel₀ hc0 (he ▸ h)⟩


end Eisenstein

private def ofPrimaryFiber {n : ℤ} (z : PrimaryFiber n) : Eisenstein :=
  ⟨z.1.1, z.1.2⟩

private theorem ofPrimaryFiber_injective {n : ℤ} :
    Function.Injective (@ofPrimaryFiber n) := by
  intro x y h
  exact Subtype.ext (Prod.ext (congrArg QuadraticAlgebra.re h) (congrArg QuadraticAlgebra.im h))

private theorem ofPrimaryFiber_primary {n : ℤ} (z : PrimaryFiber n) :
    (ofPrimaryFiber z).IsPrimary :=
  Eisenstein.isPrimary_iff.mpr ⟨z.2.1, z.2.2.1⟩

private theorem ofPrimaryFiber_norm {n : ℕ} (z : PrimaryFiber n) :
    (ofPrimaryFiber z).natNorm = n := by
  apply Eisenstein.natNorm_eq_iff.mpr
  rw [Eisenstein.norm_formula]
  exact z.2.2.2

private def toPrimaryFiber {n : ℕ} (z : Eisenstein) (hp : z.IsPrimary) (hn : z.natNorm = n) :
    PrimaryFiber n :=
  let h := Eisenstein.isPrimary_iff.mp hp
  ⟨(z.re, z.im), h.1, h.2,
    (Eisenstein.norm_formula z).symm.trans (Eisenstein.natNorm_eq_iff.mp hn)⟩

private def primaryFiberMul {m n : ℕ} (z : PrimaryFiber m × PrimaryFiber n) :
    PrimaryFiber ((m * n : ℕ) : ℤ) :=
  toPrimaryFiber (ofPrimaryFiber z.1 * ofPrimaryFiber z.2)
    ((ofPrimaryFiber_primary z.1).mul (ofPrimaryFiber_primary z.2))
    (by rw [Eisenstein.natNorm_mul, ofPrimaryFiber_norm, ofPrimaryFiber_norm])

/-- Multiplication is a bijection from the product of primary norm fibers at coprime
positive integers to the primary fiber at their product. -/
noncomputable def primaryFiberMulEquiv {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hc : m.Coprime n) : PrimaryFiber m × PrimaryFiber n ≃ PrimaryFiber ((m * n : ℕ) : ℤ) :=
  Equiv.ofBijective primaryFiberMul ⟨by
    intro x y h
    have he : ofPrimaryFiber x.1 * ofPrimaryFiber x.2 = ofPrimaryFiber y.1 * ofPrimaryFiber y.2 :=
      congrArg ofPrimaryFiber h
    obtain ⟨h₁,h₂⟩ := Eisenstein.primary_mul_unique hm hc (ofPrimaryFiber_norm x.1)
      (ofPrimaryFiber_norm x.2) (ofPrimaryFiber_norm y.1) (ofPrimaryFiber_primary x.1)
      (ofPrimaryFiber_primary y.1) he
    exact Prod.ext (ofPrimaryFiber_injective h₁) (ofPrimaryFiber_injective h₂), by
    intro z
    obtain ⟨a,b,hab,ha,hb,hpa,hpb⟩ := Eisenstein.exists_primary_mul_of_natNorm hm hn hc
      (ofPrimaryFiber_norm z) (ofPrimaryFiber_primary z)
    refine ⟨(toPrimaryFiber a hpa ha, toPrimaryFiber b hpb hb), ?_⟩
    apply ofPrimaryFiber_injective
    exact hab.symm⟩

private def thetaWeight {R : Type*} [CommRing R] (w : R) (z : Eisenstein) : R :=
  (z.re : R) + (z.im : R) * w

private theorem thetaWeight_mul {R : Type*} [CommRing R] {w : R} (hw : w^2 + w + 1 = 0)
    (x y : Eisenstein) : thetaWeight w (x * y) = thetaWeight w x * thetaWeight w y := by
  simp only [thetaWeight, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  push_cast
  linear_combination - (x.im : R) * (y.im : R) * hw

/-- Primary theta coefficients are multiplicative on coprime positive indices. -/
theorem primaryCoeff_mul_of_coprime {R : Type*} [CommRing R] (w : R) (hw : w^2+w+1 = 0)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hc : m.Coprime n) :
    primaryCoeff w (m * n : ℤ) = primaryCoeff w m * primaryCoeff w n := by
  classical
  rw [← Nat.cast_mul]
  let := Fintype.ofFinite (PrimaryFiber m)
  let := Fintype.ofFinite (PrimaryFiber n)
  let := Fintype.ofFinite (PrimaryFiber ((m*n : ℕ) : ℤ))
  simp only [primaryCoeff, finsum_eq_sum_of_fintype]
  let f (n : ℤ) (z : PrimaryFiber n) : R := thetaWeight w (ofPrimaryFiber z)
  change ∑ z : PrimaryFiber ((m*n : ℕ) : ℤ), f _ z = (∑ z : PrimaryFiber m, f _ z) *
    ∑ z : PrimaryFiber n, f _ z
  calc
    _ = ∑ p : PrimaryFiber m × PrimaryFiber n, f _ (primaryFiberMulEquiv hm hn hc p) :=
      ((primaryFiberMulEquiv hm hn hc).sum_comp _).symm
    _ = ∑ p : PrimaryFiber m × PrimaryFiber n, f _ p.1 * f _ p.2 := by
      apply Finset.sum_congr rfl
      intro p _
      exact thetaWeight_mul hw _ _
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

end BSD.CMTheta
