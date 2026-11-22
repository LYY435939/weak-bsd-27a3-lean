import BSD.CMComparison
import BSD.JacobiTriangular

/-! # The rank part of BSD for the Fermat cubic over ℚ

On the arithmetic side, the Euler coefficients of y² = x³ − 432 are
weighted counts of primary Eisenstein integers. On the analytic side,
Jacobi's triple product gives exactly those counts as the coefficients of
η(3z)²η(9z)². Its normalized Mellin transform is entire and positive at 1.
-/

namespace BSD.FermatCubic

/-- The Fourier coefficients of the level-27 eta product agree at every
index with Mathlib's Hasse–Weil coefficients of the fixed curve. -/
theorem LFunction_eq_etaCoeff (n : ℕ) : curve.LFunction n = EtaSupport.etaCoeff n := by
  let w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hp : IsPrimitiveRoot w 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  have hw : w ^ 2 + w + 1 = 0 := by
    have hmul : (w - 1) * (w ^ 2 + w + 1) = 0 := by linear_combination hp.pow_eq_one
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (hp.ne_one (by decide)))
  exact_mod_cast (primaryCoeff_eq_LFunction w hw n).symm.trans
    (MacdonaldA2.etaCoeff_eq_primary_of_jacobi w hw n JacobiTriangular.tendsto_jacobiPartial).symm

theorem arithmeticFourierExpansion : HasArithmeticFourierExpansion := by
  intro t ht
  simpa only [curveCoefficient, LFunction_eq_etaCoeff] using etaProductAxis_hasSum_etaCoeff t ht

/-- The explicit entire Mellin transform continues the curve's own L-series. -/
theorem etaL_continues : Continues curve etaL :=
  etaL_continues_of_expansion arithmeticFourierExpansion

theorem analytic_rank_zero : meromorphicOrderAt etaL 1 = 0 := by
  apply (meromorphicOrderAt_eq_nat_iff_iteratedDeriv (r := 0) (differentiable_etaL.analyticAt 1)).2
  exact ⟨by omega, by simpa only [iteratedDeriv_zero] using etaL_one_ne_zero⟩

/-- Weak BSD for the Fermat cubic, LMFDB 27.a3, over the rationals. -/
theorem weakBSD : RankPart curve := by
  refine ⟨etaL, etaL_continues, ?_⟩
  simpa only [algebraic_rank_zero, Nat.cast_zero] using analytic_rank_zero

end BSD.FermatCubic
