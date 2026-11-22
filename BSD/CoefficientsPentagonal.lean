import BSD.CoefficientsEta
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries

open Filter PowerSeries
open scoped Topology PowerSeries.WithPiTopology

namespace EtaSupport

private theorem tendsto_expanded_prod (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun N : ℕ ↦ ∏ j ∈ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (k * (j + 1))))
      atTop (𝓝 ((pentagonalSeries ℤ).expand k hk)) := by
  have hbase := (PowerSeries.WithPiTopology.hasProd_one_sub_X_pow ℤ).tendsto_prod_nat
  have hExpand : Tendsto
      (fun N : ℕ ↦ PowerSeries.expand k hk
        (∏ j ∈ Finset.range N, (1 - (X : ℤ⟦X⟧) ^ (j + 1))))
      atTop (𝓝 ((pentagonalSeries ℤ).expand k hk)) := by
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at hbase ⊢
    intro d
    simp only [coeff_expand]
    split
    · exact hbase (d / k)
    · exact tendsto_const_nhds
  simpa only [map_prod, map_sub, map_one, map_pow, expand_X, ← pow_mul] using hExpand

/-- The stabilized eta coefficients come from four Euler pentagonal series. -/
theorem etaSeries_eq_pentagonal :
    etaSeries = X * (pentagonalSeries ℤ).expand 3 (by decide) ^ 2 *
      (pentagonalSeries ℤ).expand 9 (by decide) ^ 2 := by
  have hEta : Tendsto etaTrunc atTop (𝓝 etaSeries) := by
    rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    apply tendsto_nhds_of_eventually_eq
    exact eventually_atTop.mpr ⟨d, fun N hN ↦ etaSeries_coeff_eq_trunc d N hN |>.symm⟩
  have hLim :=
    (tendsto_const_nhds (x := (X : ℤ⟦X⟧)) (f := atTop)).mul
      (((tendsto_expanded_prod 3 (by decide)).pow 2).mul
        ((tendsto_expanded_prod 9 (by decide)).pow 2))
  apply tendsto_nhds_unique hEta
  rw [mul_assoc]
  apply (show Tendsto etaTrunc atTop _ from hLim.congr ?_)
  intro N
  simp only [etaTrunc_eq_direct, Finset.prod_mul_distrib, Finset.prod_pow]

end EtaSupport
