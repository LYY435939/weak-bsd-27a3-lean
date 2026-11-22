import BSD.JacobiTripleProduct
import BSD.MacdonaldProduct


/-!
# Triangular normalization of Jacobi's triple product

The square form has a term of degree `D = m²` at Laurent weight `m`. For
each finite product, shifting degrees by `D = 2d + m` turns its three factors
into the Euler factor and the two factors with weights `1` and `-1`.
Taking one more positive-weight factor retains the term of degree zero.
The square identity thus gives `d = m(m-1)/2`. Evaluating the Laurent
variable at `-x` gives the alternating sign in the bilateral Jacobi series.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace BSD.JacobiTriangular

private abbrev L := LaurentPolynomial ℤ
private abbrev R := PowerSeries L

/-- A coefficient extended by zero to negative formal degrees. -/
private noncomputable def cf (f : R) (d m : ℤ) : ℤ :=
  if 0 ≤ d then (PowerSeries.coeff d.toNat f).coeff m else 0

private noncomputable def factor (n : ℕ) (k c : ℤ) : R :=
  1 + PowerSeries.C (AddMonoidAlgebra.single k c) * X ^ n

private theorem cf_factor (f : R) (n : ℕ) (k c d m : ℤ) :
    cf (f * factor n k c) d m = cf f d m + cf f (d-n) (m-k) * c := by
  by_cases hd : 0 ≤ d
  · lift d to ℕ using hd
    rw [show f * factor n k c = f + (f * C (AddMonoidAlgebra.single k c)) * X^n by
      simp only [factor]; ring]
    simp only [cf, Int.natCast_nonneg, if_true, Int.toNat_natCast, map_add,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, PowerSeries.coeff_mul_X_pow']
    by_cases hn : n ≤ d
    · have hdn : 0 ≤ (d : ℤ) - n := by omega
      have he : ((d : ℤ) - n).toNat = d-n := by omega
      simp only [if_pos hn, if_pos hdn, he, coeff_mul_C, AddMonoidAlgebra.coeff_mul_single_apply]
      rfl
    · have hdn : ¬ 0 ≤ (d : ℤ) - n := by omega
      simp only [if_neg hn, if_neg hdn, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, zero_mul]
  · have hdn : ¬ 0 ≤ d - n := by omega
    simp only [cf, if_neg hd, if_neg hdn, zero_mul, add_zero]

private def Shear (s t : R) : Prop := ∀ d m : ℤ, cf s (2*d+m) m = cf t d m

private theorem shear_one : Shear 1 1 := by
  intro d m
  by_cases hm : m = 0
  · subst m
    simp only [cf, add_zero, coeff_one]
    split_ifs <;> simp_all <;> omega
  · have hone : (1 : L).coeff m = 0 := by
      rw [← LaurentPolynomial.T_zero, LaurentPolynomial.T_apply, if_neg (Ne.symm hm)]
    simp only [cf, coeff_one]
    split_ifs <;> simp_all

private theorem Shear.factor {s t : R} (h : Shear s t) (u v : ℕ) (k c : ℤ)
    (he : (u : ℤ) = 2*v+k) : Shear (s * factor u k c) (t * factor v k c) := by
  intro d m
  simp only [cf_factor, h d m, show 2*d+m-u = 2*(d-v)+(m-k) by omega, h (d-v) (m-k)]

private noncomputable def blockProd (e a b : ℕ → ℕ) (N : ℕ) : R :=
  (∏ i ∈ Finset.range N, factor (e i) 0 (-1)) *
    (∏ i ∈ Finset.range (N+1), factor (a i) 1 1) *
    (∏ i ∈ Finset.range N, factor (b i) (-1) 1)

private theorem prefix_succ (e a b : ℕ → ℕ) (N : ℕ) :
    blockProd e a b (N+1) =
    ((blockProd e a b N * factor (e N) 0 (-1)) * factor (a (N+1)) 1 1) *
      factor (b N) (-1) 1 := by
  simp only [blockProd, Finset.prod_range_succ]
  ring

private noncomputable abbrev squarePrefix := blockProd (fun i ↦ 2*(i+1)) (fun i ↦ 2*i+1) (fun i ↦ 2*i+1)
private noncomputable abbrev triangularPrefix := blockProd (fun i ↦ i+1) id (fun i ↦ i+1)

private theorem shear_prefix (N : ℕ) : Shear (squarePrefix N) (triangularPrefix N) := by
  induction N with
  | zero =>
    simpa only [squarePrefix, triangularPrefix, blockProd, Finset.prod_range_zero,
      Finset.prod_range_succ, one_mul, mul_one, id_eq] using
      (shear_one.factor 1 0 1 1 (by decide))
  | succ N ih =>
    rw [squarePrefix, triangularPrefix, prefix_succ, prefix_succ]
    exact (((ih.factor _ _ 0 (-1) (by dsimp; omega)).factor _ _ 1 1
      (by dsimp)).factor _ _ (-1) 1 (by dsimp; omega))

private theorem factor_zero (n : ℕ) : factor n 0 (-1) = (1 - X^n : R) := by
  simp [factor, sub_eq_add_neg]

private theorem factor_unit (n : ℕ) (k : ℤ) :
    factor n k 1 = 1 + C (LaurentPolynomial.T k) * X^n := rfl

private theorem squarePrefix_poch (N : ℕ) : squarePrefix N =
    Jacobi.qPoch (Jacobi.q^2) (Jacobi.q^2) N *
      Jacobi.qPoch (-Jacobi.a * Jacobi.q) (Jacobi.q^2) (N+1) *
      Jacobi.qPoch (-Jacobi.aI * Jacobi.q) (Jacobi.q^2) N := by
  simp only [squarePrefix, blockProd, Jacobi.qPoch, factor_zero, factor_unit, Jacobi.q, Jacobi.a, Jacobi.aI]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_
  · apply Finset.prod_congr rfl
    intro i _
    rw [show 2*(i+1) = 2*i+2 by omega, pow_add, pow_mul]; ring
  · apply Finset.prod_congr rfl
    intro i _
    rw [pow_add, pow_mul]; ring
  · apply Finset.prod_congr rfl
    intro i _
    rw [pow_add, pow_mul]; ring

private theorem coeff_mul_congr_to {s t u v : R} (d : ℕ)
    (h : ∀ j ≤ d, coeff j s = coeff j t) (h' : ∀ j ≤ d, coeff j u = coeff j v) :
    coeff d (s*u) = coeff d (t*v) := by
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
  rw [h j.1 (by omega), h' j.2 (by omega)]

private theorem coeff_squarePrefix (d N : ℕ) (h : d < N) :
    coeff d (squarePrefix N) = coeff d Jacobi.lhs := by
  rw [squarePrefix_poch, Jacobi.lhs]
  apply coeff_mul_congr_to
  · intro j hj
    apply coeff_mul_congr_to
    · intro l hl
      simpa only [neg_neg, pow_two] using (Jacobi.lhs_coeff_stable (-Jacobi.q) l N (by omega)).symm
    · intro l hl
      simpa only [mul_comm Jacobi.q Jacobi.a, neg_mul] using
        (Jacobi.lhs_coeff_stable Jacobi.a l (N+1) (by omega)).symm
  · intro j hj
    simpa only [mul_comm Jacobi.q Jacobi.aI, neg_mul] using
      (Jacobi.lhs_coeff_stable Jacobi.aI j N (by omega)).symm

private theorem cf_factor_large (f : R) (n : ℕ) (k c d m : ℤ) (hn : d < n) :
    cf (f * factor n k c) d m = cf f d m := by
  rw [cf_factor]
  have hd : ¬ 0 ≤ d - n := by omega
  simp only [cf, if_neg hd, zero_mul, add_zero]

private theorem cf_triangularPrefix_stable (d N : ℕ) (hd : d ≤ N) (m : ℤ) :
    cf (triangularPrefix N) d m = cf (triangularPrefix d) d m := by
  induction N, hd using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [triangularPrefix, prefix_succ]
    rw [cf_factor_large _ _ _ _ _ _ (by omega),
      cf_factor_large _ _ _ _ _ _ (by dsimp; omega),
      cf_factor_large _ _ _ _ _ _ (by omega)]
    exact ih

private theorem square_eq_iff_tri (d : ℕ) (m : ℤ) :
    2*(d : ℤ)+m = (m.natAbs^2 : ℕ) ↔ d = MacdonaldA2.tri m := by
  have hs : ((m.natAbs ^ 2 : ℕ) : ℤ) = m^2 := by
    rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs]
  rw [hs]
  have h := MacdonaldA2.two_mul_tri m
  constructor
  · intro hd; exact_mod_cast (show (d : ℤ) = MacdonaldA2.tri m by nlinarith)
  · intro hd; subst d; nlinarith

/-- Coefficients of the ordinary triangular product before specializing its
Laurent variable to the negative of the Jacobi argument. -/
private theorem triangularPrefix_coeff (d N : ℕ) (hd : d ≤ N) (m : ℤ) :
    (coeff d (triangularPrefix N)).coeff m = if d = MacdonaldA2.tri m then 1 else 0 := by
  let D := 2*(d : ℤ)+m
  let K := max d (D.toNat+1)
  have hdK : d ≤ K := le_max_left _ _
  have hDK : D.toNat < K := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have he := (cf_triangularPrefix_stable d N hd m).trans (cf_triangularPrefix_stable d K hdK m).symm
  have hshear := (shear_prefix K (d : ℤ) m).symm
  change cf (triangularPrefix N) (d : ℤ) m = _
  rw [he, hshear]
  change cf (squarePrefix K) D m = _
  by_cases hD : 0 ≤ D
  · rw [cf, if_pos hD, coeff_squarePrefix _ _ hDK, Jacobi.jacobi_triple_product_coeff]
    have heq : D.toNat = m.natAbs^2 ↔ d = MacdonaldA2.tri m :=
      (show D.toNat = m.natAbs^2 ↔ D = (m.natAbs^2 : ℕ) by omega).trans (square_eq_iff_tri d m)
    simp only [heq]
  · rw [cf, if_neg hD, if_neg]
    intro heq
    have heD := (square_eq_iff_tri d m).mpr heq
    change D = _ at heD
    omega

private noncomputable def atNeg (x : ℂ) (hx : x ≠ 0) : L →+* ℂ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℂ) (Units.mk0 (-x) (neg_ne_zero.mpr hx))

private theorem atNeg_T (x : ℂ) (hx : x ≠ 0) (k : ℤ) :
    atNeg x hx (LaurentPolynomial.T k) = (-x)^k := by
  simp only [atNeg, LaurentPolynomial.eval₂_T, Units.val_zpow_eq_zpow_val, Units.val_mk0]

private theorem map_triangularPrefix (x : ℂ) (hx : x ≠ 0) (N : ℕ) :
    PowerSeries.map (atNeg x hx) (triangularPrefix N) = MacdonaldA2.jacobiPartial x N := by
  simp only [triangularPrefix, blockProd, factor_zero, factor_unit, map_mul, map_prod,
    map_add, map_one, map_sub, map_pow, PowerSeries.map_X, PowerSeries.map_C, atNeg_T,
    zpow_one, zpow_neg_one, inv_neg, map_neg, neg_mul, ← sub_eq_add_neg, id_eq,
    MacdonaldA2.jacobiPartial, MacdonaldA2.eulerPartial, MacdonaldA2.rootPair,
    Finset.prod_mul_distrib]
  rw [Finset.prod_range_succ' (fun i : ℕ ↦ (1-C x*X^i : ℂ⟦X⟧))]
  simp only [pow_zero, mul_one]
  ring

private theorem hasSum_eval (x : ℂ) (hx : x ≠ 0) (f : L) :
    HasSum (fun m : ℤ ↦ (f.coeff m : ℂ) * (-x)^m) (atNeg x hx f) := by
  have hs := congrArg (atNeg x hx) (AddMonoidAlgebra.sum_coeff_single f)
  simp only [Finsupp.sum, map_sum, LaurentPolynomial.single_eq_C_mul_T, map_mul, atNeg_T] at hs
  have hC (i : ℤ) : atNeg x hx (LaurentPolynomial.C i) = (i : ℂ) := by
    simp [atNeg]
  simp only [hC] at hs
  rw [← hs]
  apply hasSum_sum_of_ne_finset_zero
  intro m hm
  simp [Finsupp.notMem_support_iff.mp hm]

/-- The coefficient of degree `d` stabilizes as soon as the `d`-th block is present. -/
theorem jacobiPartial_coeff (x : ℂ) (hx : x ≠ 0) (d N : ℕ) (hd : d ≤ N) :
    coeff d (MacdonaldA2.jacobiPartial x N) = coeff d (MacdonaldA2.jacobiSeries x) := by
  rw [← map_triangularPrefix x hx N, PowerSeries.coeff_map]
  have h := hasSum_eval x hx (coeff d (triangularPrefix N))
  have h' := ((WithPiTopology.hasSum_iff_hasSum_coeff ℂ).mp (MacdonaldA2.summable_jacobiTerm x).hasSum) d
  apply h.unique
  apply h'.congr_fun
  intro m
  rw [triangularPrefix_coeff _ _ hd, MacdonaldA2.jacobiTerm, coeff_monomial]
  by_cases he : d = MacdonaldA2.tri m
  · simp only [if_pos he, Int.cast_one, one_mul, Int.cast_negOnePow]
    rw [← mul_zpow, neg_one_mul]
  · simp [he]

/-- Jacobi's triple product in triangular-exponent normalization. -/
theorem tendsto_jacobiPartial (x : ℂ) (hx : x ≠ 0) :
    Filter.Tendsto (MacdonaldA2.jacobiPartial x) Filter.atTop (𝓝 (MacdonaldA2.jacobiSeries x)) := by
  apply (WithPiTopology.tendsto_iff_coeff_tendsto ℂ _ _ _).mpr
  intro d
  exact tendsto_atTop_of_eventually_const (i₀ := d) (fun N hN ↦ jacobiPartial_coeff x hx d N hN)

end BSD.JacobiTriangular
