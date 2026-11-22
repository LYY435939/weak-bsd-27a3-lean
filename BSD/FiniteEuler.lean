import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Finite Euler factors at the center

Deleting Euler factors amounts to multiplying by their local denominator
polynomials. A finite product of these polynomials is an analytic unit at
`s = 1`, so this multiplication preserves the meromorphic order.
-/

namespace BSD

/-- The local Euler variable `p^(-s)`. -/
noncomputable def eulerVariable (p : ℕ) (s : ℂ) : ℂ := (p : ℂ) ^ (-s)

/-- The inverse local factor at a good prime, with integer trace `a`. -/
noncomputable def goodInverseEulerFactor (p : ℕ) (a : ℤ) (s : ℂ) : ℂ :=
  1 - (a : ℂ) * eulerVariable p s + (p : ℂ) * (eulerVariable p s) ^ 2

/-- The reduction type at an Euler prime. In the good case, `N` is the
positive point count of the reduction, including its point at infinity. -/
inductive EulerFactorKind where
  | good (N : ℕ) (hN : 0 < N)
  | split
  | nonsplit
  | additive

/-- The local denominator, with good trace `p + 1 - N` and with the linear
denominators for split and nonsplit multiplicative reduction. -/
noncomputable def inverseLocalEulerFactor (p : ℕ) (kind : EulerFactorKind) (s : ℂ) : ℂ :=
  match kind with
  | .good N _ => goodInverseEulerFactor p ((p : ℤ) + 1 - (N : ℤ)) s
  | .split => 1 - eulerVariable p s
  | .nonsplit => 1 + eulerVariable p s
  | .additive => 1

@[simp] theorem eulerVariable_one (p : ℕ) :
    eulerVariable p 1 = (p : ℂ)⁻¹ := Complex.cpow_neg_one _

theorem analyticAt_eulerVariable {p : ℕ} (hp : p ≠ 0) (s : ℂ) :
    AnalyticAt ℂ (eulerVariable p) s := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  change AnalyticAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s
  simp only [Complex.cpow_def_of_ne_zero hpC]
  fun_prop

theorem goodInverseEulerFactor_one {p : ℕ} (hp : p ≠ 0) (a : ℤ) :
    goodInverseEulerFactor p a 1 = ((p : ℂ) + 1 - (a : ℂ)) / (p : ℂ) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  simp only [goodInverseEulerFactor, eulerVariable_one]
  field_simp; ring

theorem goodInverseEulerFactor_one_eq_pointCount_div {p N : ℕ} {a : ℤ}
    (hp : p ≠ 0) (ha : a = (p : ℤ) + 1 - (N : ℤ)) :
    goodInverseEulerFactor p a 1 = (N : ℂ) / (p : ℂ) := by
  rw [goodInverseEulerFactor_one hp, ha]
  push_cast
  ring

theorem analyticAt_inverseLocalEulerFactor {p : ℕ} (hp : p ≠ 0)
    (kind : EulerFactorKind) (s : ℂ) :
    AnalyticAt ℂ (inverseLocalEulerFactor p kind) s := by
  have hX := analyticAt_eulerVariable hp s
  cases kind with
  | good N hN =>
      change AnalyticAt ℂ (fun z =>
        1 - (((p : ℤ) + 1 - (N : ℤ) : ℤ) : ℂ) * eulerVariable p z
          + (p : ℂ) * (eulerVariable p z) ^ 2) s
      fun_prop
  | split =>
      exact analyticAt_const.sub hX
  | nonsplit =>
      exact analyticAt_const.add hX
  | additive =>
      exact analyticAt_const

theorem inverseLocalEulerFactor_one_ne_zero {p : ℕ} (hp : Nat.Prime p)
    (kind : EulerFactorKind) : inverseLocalEulerFactor p kind 1 ≠ 0 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpOne : (p : ℂ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hpNeg : (p : ℂ) + 1 ≠ 0 := by
    intro h
    have hp0 : (p : ℝ) + 1 = 0 := by simpa using congrArg Complex.re h
    have hpPos : 0 ≤ (p : ℝ) := by positivity
    linarith
  cases kind with
  | good N hN =>
      rw [inverseLocalEulerFactor, goodInverseEulerFactor_one_eq_pointCount_div hp.ne_zero rfl]
      exact div_ne_zero (by exact_mod_cast hN.ne') hpC
  | split =>
      change 1 - eulerVariable p 1 ≠ 0
      rw [eulerVariable_one, ← one_div]
      intro h
      exact hpOne (by simpa using (sub_eq_zero.mp h).symm)
  | nonsplit =>
      change 1 + eulerVariable p 1 ≠ 0
      rw [eulerVariable_one]
      intro h
      apply hpNeg
      have h' := congrArg (fun z : ℂ => z * (p : ℂ)) h
      simpa [add_mul, inv_mul_cancel₀ hpC] using h'
  | additive =>
      exact one_ne_zero

/-- The pointwise product of the local denominators at the selected indices. -/
noncomputable def finiteEulerProduct {ι : Type*} (S : Finset ι) (p : ι → ℕ)
    (kind : ι → EulerFactorKind) (s : ℂ) : ℂ :=
  ∏ i ∈ S, inverseLocalEulerFactor (p i) (kind i) s

theorem analyticAt_finiteEulerProduct {ι : Type*} (S : Finset ι) (p : ι → ℕ)
    (kind : ι → EulerFactorKind) (hp : ∀ i ∈ S, Nat.Prime (p i)) (s : ℂ) :
    AnalyticAt ℂ (finiteEulerProduct S p kind) s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      change AnalyticAt ℂ (fun z => ∏ i ∈ (∅ : Finset ι),
        inverseLocalEulerFactor (p i) (kind i) z) s
      simp only [Finset.prod_empty]
      exact analyticAt_const
  | insert i S hi ih =>
      have h₁ := analyticAt_inverseLocalEulerFactor (hp i (Finset.mem_insert_self i S)).ne_zero
        (kind i) s
      have h₂ := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      change AnalyticAt ℂ (fun z => ∏ j ∈ insert i S,
        inverseLocalEulerFactor (p j) (kind j) z) s
      simp only [Finset.prod_insert hi]
      exact h₁.mul h₂

theorem finiteEulerProduct_one_ne_zero {ι : Type*} (S : Finset ι) (p : ι → ℕ)
    (kind : ι → EulerFactorKind) (hp : ∀ i ∈ S, Nat.Prime (p i)) :
    finiteEulerProduct S p kind 1 ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i hi => inverseLocalEulerFactor_one_ne_zero (hp i hi) (kind i)

/-- Deleting finitely many Euler factors preserves the vanishing or pole order
at the center. The conclusion also covers the locally zero germ. -/
theorem meromorphicOrderAt_mul_finite_eulerProduct {ι : Type*} (S : Finset ι) (p : ι → ℕ)
    (kind : ι → EulerFactorKind) (hp : ∀ i ∈ S, Nat.Prime (p i)) (L : ℂ → ℂ) :
    meromorphicOrderAt (finiteEulerProduct S p kind * L) 1 = meromorphicOrderAt L 1 :=
  meromorphicOrderAt_mul_of_ne_zero (analyticAt_finiteEulerProduct S p kind hp 1)
    (finiteEulerProduct_one_ne_zero S p kind hp)

end BSD
