import BSD.MacdonaldA2
import BSD.CMThetaIdentity
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Product and weight extraction for the affine A₂ denominator

The coefficient ring is complex and the degree variable is formal. At each
degree only finitely many terms occur, including after grouping by Laurent weight.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace BSD.MacdonaldA2

private theorem finite_tri_le (d : ℕ) : {i : ℤ | tri i ≤ d}.Finite := by
  apply (Set.finite_Icc (-(2*(d : ℤ)+1)) (2*(d : ℤ)+1)).subset
  intro i hi
  have hle : (tri i : ℤ) ≤ d := by exact_mod_cast (show tri i ≤ d from hi)
  constructor <;> nlinarith only [hle, two_mul_tri i, sq_nonneg (i-1), sq_nonneg i]

private theorem summable_monomials {ι : Type*} (degree : ι → ℕ) (a : ι → ℂ)
    (h : ∀ d, {i | degree i ≤ d}.Finite) :
    Summable (fun i ↦ PowerSeries.monomial (degree i) (a i)) := by
  rw [WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  apply (h d).subset
  intro i hi
  by_contra hle
  apply hi
  have hne : d ≠ degree i := by
    intro heq
    exact hle (show degree i ≤ d by omega)
  simp [PowerSeries.coeff_monomial, hne]

/-- One bilateral Jacobi term at the specified root variable. -/
noncomputable def jacobiTerm (x : ℂ) (i : ℤ) : ℂ⟦X⟧ :=
  PowerSeries.monomial (tri i) ((i.negOnePow : ℤ) * x^i)

/-- The bilateral Jacobi series with triangular exponents. -/
noncomputable def jacobiSeries (x : ℂ) : ℂ⟦X⟧ := ∑' i, jacobiTerm x i

theorem summable_jacobiTerm (x : ℂ) : Summable (jacobiTerm x) :=
  summable_monomials tri _ finite_tri_le

private theorem summable_jacobiTerm_pair (x y : ℂ) :
    Summable (fun t : ℤ × ℤ ↦ jacobiTerm x t.1 * jacobiTerm y t.2) := by
  simp only [jacobiTerm, PowerSeries.monomial_mul_monomial]
  apply summable_monomials
  intro d
  apply ((finite_tri_le d).prod (finite_tri_le d)).subset
  intro i hi
  change tri i.1 + tri i.2 ≤ d at hi
  change tri i.1 ≤ d ∧ tri i.2 ≤ d
  exact ⟨by omega, by omega⟩

private theorem summable_jacobiTerm_triple (x y z : ℂ) :
    Summable (fun t : (ℤ × ℤ) × ℤ ↦ jacobiTerm x t.1.1 * jacobiTerm y t.1.2 *
      jacobiTerm z t.2) := by
  simp only [jacobiTerm, PowerSeries.monomial_mul_monomial]
  apply summable_monomials
  intro d
  apply (((finite_tri_le d).prod (finite_tri_le d)).prod (finite_tri_le d)).subset
  intro i hi
  change tri i.1.1 + tri i.1.2 + tri i.2 ≤ d at hi
  change (tri i.1.1 ≤ d ∧ tri i.1.2 ≤ d) ∧ tri i.2 ≤ d
  exact ⟨⟨by omega, by omega⟩, by omega⟩

/-- Expansion of the product as a summable family of Laurent monomials. -/
theorem hasSum_jacobiTerm_triple (x y z : ℂ) :
    HasSum (fun t : (ℤ × ℤ) × ℤ ↦ jacobiTerm x t.1.1 * jacobiTerm y t.1.2 *
      jacobiTerm z t.2) (jacobiSeries x * jacobiSeries y * jacobiSeries z) := by
  exact ((summable_jacobiTerm x).hasSum.mul (summable_jacobiTerm y).hasSum
    (summable_jacobiTerm_pair x y)).mul (summable_jacobiTerm z).hasSum
    (summable_jacobiTerm_triple x y z)

private def tripleToWeight : (ℤ × ℤ) × ℤ ≃ (ℤ × ℤ) × ℤ where
  toFun t := ((t.1.1+t.1.2, t.2-t.1.1), t.1.1)
  invFun t := ((t.2, t.1.1-t.2), t.1.2+t.2)
  left_inv := by rintro ⟨⟨a,b⟩,c⟩; simp
  right_inv := by rintro ⟨⟨a,b⟩,c⟩; simp

private theorem map_hasSum_int {ι : Type*} {f : ι → ℤ⟦X⟧} {g : ℤ⟦X⟧}
    (h : HasSum f g) : HasSum (fun i ↦ PowerSeries.map (Int.castRingHom ℂ) (f i))
      (PowerSeries.map (Int.castRingHom ℂ) g) := by
  rw [WithPiTopology.hasSum_iff_hasSum_coeff] at h ⊢
  intro d
  simp only [PowerSeries.coeff_map]
  exact (h d).map (Int.castRingHom ℂ).toAddMonoidHom continuous_of_discreteTopology

private theorem hasSum_weightTerm_complex (A C : ℤ) :
    HasSum (fun i ↦ PowerSeries.map (Int.castRingHom ℂ) (weightTerm A C i))
      (PowerSeries.map (Int.castRingHom ℂ) (weightCoeff A C)) :=
  map_hasSum_int (summable_weightTerm A C).hasSum

/-- Specialization of an A₂ Laurent weight to `(1,s,w)`. -/
noncomputable def weightValue (s w : ℂ) (A B : ℤ) : ℂ :=
  s^(1+B) * w^(2-A-B)

private theorem three_roots_weight (s w : ℂ) (hs : s ≠ 0) (hw : w ≠ 0) (A B i : ℤ) :
    PowerSeries.C (s*w^2) *
      (jacobiTerm (1/s) i * jacobiTerm (1/w) (A-i) * jacobiTerm (s/w) (B+i)) =
      PowerSeries.C (weightValue s w A B) *
        PowerSeries.map (Int.castRingHom ℂ) (weightTerm A B i) := by
  have hmap (d : ℕ) (a : ℤ) : PowerSeries.map (Int.castRingHom ℂ)
      (PowerSeries.monomial d a) = PowerSeries.monomial d (a : ℂ) := by
    simp [PowerSeries.monomial_eq_C_mul_X_pow]
  simp only [jacobiTerm, weightTerm, weightValue, hmap, ← PowerSeries.monomial_zero_eq_C,
    PowerSeries.monomial_mul_monomial, zero_add]
  congr 1
  simp only [Int.negOnePow_add, Units.val_mul, Int.cast_mul, div_eq_mul_inv, one_mul,
    mul_zpow, inv_zpow]
  rw [show (1+B : ℤ) = 1 + (-i) + (B+i) by ring,
    show (2-A-B : ℤ) = 2 + (-(A-i)) + (-(B+i)) by ring]
  simp only [zpow_add₀ hs, zpow_add₀ hw, zpow_neg, zpow_ofNat]
  ring

/-- The specialized product has the indicated Laurent-weight coefficients.
This groups the full triple sum, preserving all collisions of exponents. -/
theorem hasSum_jacobi_weight (s w : ℂ) (hs : s ≠ 0) (hw : w ≠ 0) :
    HasSum (fun t : ℤ × ℤ ↦ PowerSeries.C (weightValue s w t.1 t.2) *
        PowerSeries.map (Int.castRingHom ℂ) (weightCoeff t.1 t.2))
      (PowerSeries.C (s*w^2) *
        (jacobiSeries (1/s) * jacobiSeries (1/w) * jacobiSeries (s/w))) := by
  have h := (hasSum_jacobiTerm_triple (1/s) (1/w) (s/w)).mul_left (PowerSeries.C (s*w^2))
  have hr := tripleToWeight.symm.hasSum_iff.mpr h
  apply hr.prod_fiberwise
  intro t
  apply ((hasSum_weightTerm_complex t.1 t.2).mul_left
    (PowerSeries.C (weightValue s w t.1 t.2))).congr_fun
  intro i
  exact three_roots_weight s w hs hw t.1 t.2 i

/-- Euler's formal series is a unit, which permits cancellation of the common
factor appearing after multiplication of the three Jacobi identities. -/
theorem isUnit_eulerSeries_complex : IsUnit (pentagonalSeries ℂ) := by
  have h : (pentagonalSeries ℂ).coeff 0 = 1 := by
    simpa [pentagonal] using PowerSeries.coeff_pentagonalSeries_pentagonal ℂ 0
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff, h]
  exact isUnit_one

open Filter Finset
open scoped Topology

/-- Paired factors at positive degree for one root. -/
noncomputable def rootPair (x : ℂ) (T : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  (1 - PowerSeries.C x*T) * (1 - PowerSeries.C x⁻¹*T)

/-- The first `N` factors of the Euler product. -/
noncomputable def eulerPartial (N : ℕ) : ℂ⟦X⟧ :=
  ∏ j ∈ range N, (1 - X ^ (j+1))

/-- The first `N` factors of each infinite product in the Jacobi formula,
together with the factor `1 - x` at degree zero. -/
noncomputable def jacobiPartial (x : ℂ) (N : ℕ) : ℂ⟦X⟧ :=
  eulerPartial N * (PowerSeries.C (1-x) * ∏ j ∈ range N, rootPair x (X ^ (j+1)))

/-- The normalized denominator in the formal variable `p`, before `p = q^3`. -/
noncomputable def denominatorPartial (s w : ℂ) (N : ℕ) : ℂ⟦X⟧ :=
  PowerSeries.C ((s-1)*(w-1)*(w-s)) *
    ∏ j ∈ range N,
      let T : ℂ⟦X⟧ := X ^ (j+1)
      (1-T)^2 * rootPair (1/s) T * rootPair (1/w) T * rootPair (s/w) T

theorem euler_mul_denominatorPartial (s w : ℂ) (hs : s ≠ 0) (hw : w ≠ 0) (N : ℕ) :
    eulerPartial N * denominatorPartial s w N =
      PowerSeries.C (s*w^2) *
        (jacobiPartial (1/s) N * jacobiPartial (1/w) N * jacobiPartial (s/w) N) := by
  have hV : (s-1)*(w-1)*(w-s) = (s*w^2)*((1-1/s)*(1-1/w)*(1-s/w)) := by
    field_simp
  simp only [denominatorPartial, eulerPartial, jacobiPartial, prod_mul_distrib, prod_pow,
    hV, map_mul]
  ring


/-- The three exponents of the Laurent monomial indexed by its weight pair. -/
def weightCoordinates (t : ℤ × ℤ) : Fin 3 → ℤ := ![t.1,1+t.2,2-t.1-t.2]

private theorem sum_weightCoordinates (t : ℤ × ℤ) :
    ∑ j, weightCoordinates t j = 3 := by
  simp [weightCoordinates, Fin.sum_univ_three]
  ring

private theorem weightCoordinates_inverse (k : Fin 3 → ℤ) (h : ∑ j, k j = 3) :
    weightCoordinates (k 0, k 1 - 1) = k := by
  have h' : k 0 + k 1 + k 2 = 3 := by simpa [Fin.sum_univ_three, add_assoc] using h
  funext i
  fin_cases i <;> simp [weightCoordinates]
  omega

private def regularPairs : Set (ℤ × ℤ) :=
  {t | Function.Bijective (residue ∘ weightCoordinates t)}

private def regularPairEquiv : regularPairs ≃ RegularWeight where
  toFun t := ⟨weightCoordinates t.1, sum_weightCoordinates t.1, t.2⟩
  invFun k := ⟨(k.1 0, k.1 1 - 1), by
    show Function.Bijective (residue ∘ weightCoordinates (k.1 0, k.1 1 - 1))
    rw [weightCoordinates_inverse k.1 k.2.1]
    exact k.2.2⟩
  left_inv := by rintro ⟨⟨a,b⟩, _⟩; ext <;> simp [weightCoordinates]
  right_inv k := Subtype.ext (weightCoordinates_inverse k.1 k.2.1)

private theorem weylAlternant_sum (s w : ℂ) (u v : ℤ) :
    CMTheta.weylAlternant w s u v =
      ∑ σ : Equiv.Perm (Fin 3), σ.sign • (s^(exponents u v (σ 1)) * w^(exponents u v (σ 2))) := by
  unfold CMTheta.weylAlternant
  rw [← Matrix.det_transpose, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [Fin.prod_univ_three]
  generalize σ 0 = i
  generalize σ 1 = j
  generalize σ 2 = k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [exponents]

private theorem weyl_weightTerm_eq (s w : ℂ) (u v : ℤ) (σ : Equiv.Perm (Fin 3)) :
    PowerSeries.C (weightValue s w (exponents u v (σ 0)) (exponents u v (σ 1) - 1)) *
      PowerSeries.map (Int.castRingHom ℂ)
        (weightCoeff (exponents u v (σ 0)) (exponents u v (σ 1) - 1)) =
    pentagonalSeries ℂ * PowerSeries.monomial (CMTheta.exponent u v).toNat
      (σ.sign • (s^(exponents u v (σ 1)) * w^(exponents u v (σ 2)))) := by
  have hTot : exponents u v (σ 0) + exponents u v (σ 1) + exponents u v (σ 2) = 3 := by
    have h : ∑ j, exponents u v j = 3 := by simp [exponents, Fin.sum_univ_three]; ring
    simpa [Fin.sum_univ_three] using (Equiv.sum_comp σ (exponents u v)).trans h
  have hmap : PowerSeries.map (Int.castRingHom ℂ) (pentagonalSeries ℤ) =
      pentagonalSeries ℂ := by
    apply HasSum.unique (map_hasSum_int (WithPiTopology.hasSum_pentagonalSeries ℤ))
      ?_
    simpa [Int.coe_castRingHom] using WithPiTopology.hasSum_pentagonalSeries ℂ
  rw [weightCoeff_weyl]
  simp only [weightValue, show 1 + (exponents u v (σ 1) - 1) = exponents u v (σ 1) by omega,
    show 2 - exponents u v (σ 0) - (exponents u v (σ 1) - 1) = exponents u v (σ 2) by omega,
    CMTheta.exponent, Units.smul_def, map_zsmul, map_mul, map_pow, PowerSeries.map_X,
    hmap, PowerSeries.monomial_eq_C_mul_X_pow]
  ring

/-- Grouping the regular Laurent orbits produces the actual alternating
determinant, with one common Euler series factor per orbit. -/
theorem hasSum_weyl_mul_euler (s w : ℂ) (hs : s ≠ 0) (hw : w ≠ 0) :
    HasSum (fun t : ℤ × ℤ ↦ pentagonalSeries ℂ *
        PowerSeries.monomial (CMTheta.exponent t.1 t.2).toNat
          (CMTheta.weylAlternant w s t.1 t.2))
      (PowerSeries.C (s*w^2) *
        (jacobiSeries (1/s) * jacobiSeries (1/w) * jacobiSeries (s/w))) := by
  have h := hasSum_jacobi_weight s w hs hw
  have hreg := (hasSum_subtype_iff_of_support_subset (s := regularPairs) (by
    intro t ht
    by_contra hn
    apply ht
    have hzero := weightCoeff_of_not_regular (weightCoordinates t) (sum_weightCoordinates t) hn
    have hzero' : weightCoeff t.1 t.2 = 0 := by simpa [weightCoordinates] using hzero
    simp [hzero'])).mpr h
  let e := (Equiv.prodComm (ℤ × ℤ) (Equiv.Perm (Fin 3))).trans
    (regularOrbitEquiv.trans regularPairEquiv.symm)
  have hw := e.hasSum_iff.mpr hreg
  apply hw.prod_fiberwise
  intro t
  rw [weylAlternant_sum, map_sum, Finset.mul_sum]
  convert hasSum_fintype (fun σ : Equiv.Perm (Fin 3) ↦ pentagonalSeries ℂ *
        PowerSeries.monomial (CMTheta.exponent t.1 t.2).toNat
          (σ.sign • (s^(exponents t.1 t.2 (σ 1)) * w^(exponents t.1 t.2 (σ 2))))) using 1
  funext σ
  exact weyl_weightTerm_eq s w t.1 t.2 σ

private theorem dvd_mul_sub_one {R : Type*} [CommRing R] {T a b : R}
    (ha : T ∣ a - 1) (hb : T ∣ b - 1) : T ∣ a * b - 1 := by
  rw [show a*b-1=(a-1)*b+(b-1) by ring]
  exact dvd_add (dvd_mul_of_dvd_left ha _) hb

private theorem dvd_rootPair_sub_one (x : ℂ) (T : ℂ⟦X⟧) :
    T ∣ rootPair x T - 1 := by
  unfold rootPair
  apply dvd_mul_sub_one <;> (rw [sub_sub_cancel_left, ← neg_mul, mul_comm]; exact dvd_mul_right _ _)

private theorem dvd_denominatorPartial_succ_sub (s w : ℂ) (N : ℕ) :
    (X : ℂ⟦X⟧)^(N+1) ∣ denominatorPartial s w (N+1) - denominatorPartial s w N := by
  let T : ℂ⟦X⟧ := X^(N+1)
  have hT : T ∣ (1-T)^2-1 := by
    rw [pow_two]
    apply dvd_mul_sub_one <;> (rw [sub_sub_cancel_left]; exact dvd_neg.mpr dvd_rfl)
  have hdvd := dvd_mul_sub_one
    (dvd_mul_sub_one (dvd_mul_sub_one hT (dvd_rootPair_sub_one (1/s) T))
      (dvd_rootPair_sub_one (1/w) T)) (dvd_rootPair_sub_one (s/w) T)
  rw [show denominatorPartial s w (N+1) - denominatorPartial s w N =
      denominatorPartial s w N * ((1-T)^2*rootPair (1/s) T*rootPair (1/w) T*rootPair (s/w) T - 1) by
    simp only [denominatorPartial, Finset.prod_range_succ, T]
    ring]
  exact dvd_mul_of_dvd_right hdvd _

theorem denominatorPartial_coeff_stable (s w : ℂ) (d N : ℕ) (hN : d ≤ N) :
    PowerSeries.coeff d (denominatorPartial s w N) =
      PowerSeries.coeff d (denominatorPartial s w d) := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
      have hd := PowerSeries.X_pow_dvd_iff.mp (dvd_denominatorPartial_succ_sub s w N)
        d (by omega)
      rw [map_sub] at hd
      rw [sub_eq_zero.mp hd, ih]

/-- The stabilized normalized denominator, before replacing `p` by `q^3`. -/
noncomputable def denominatorSeries (s w : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun d ↦ PowerSeries.coeff d (denominatorPartial s w d)

theorem tendsto_denominatorPartial (s w : ℂ) :
    Tendsto (denominatorPartial s w) atTop (𝓝 (denominatorSeries s w)) := by
  rw [WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  apply tendsto_nhds_of_eventually_eq
  refine eventually_atTop.mpr ⟨d, fun N hN ↦ ?_⟩
  simpa [denominatorSeries] using denominatorPartial_coeff_stable s w d N hN

/-- The normalized Weyl sum before replacing `p` by `q^3`. -/
noncomputable def weylSeries (s w : ℂ) : ℂ⟦X⟧ :=
  ∑' t : ℤ × ℤ, PowerSeries.monomial (CMTheta.exponent t.1 t.2).toNat
    (CMTheta.weylAlternant w s t.1 t.2)

theorem hasSum_weylSeries (s w : ℂ) (hs : s ≠ 0) (hw : w ≠ 0) :
    HasSum (fun t : ℤ × ℤ ↦ PowerSeries.monomial (CMTheta.exponent t.1 t.2).toNat
      (CMTheta.weylAlternant w s t.1 t.2)) (weylSeries s w) := by
  obtain ⟨e, he⟩ := isUnit_eulerSeries_complex
  have h := (hasSum_weyl_mul_euler s w hs hw).mul_left (↑e⁻¹ : ℂ⟦X⟧)
  simp only [← he, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at h
  exact h.summable.hasSum

/-- The product and Weyl series agree once the one-dimensional Jacobi
identities are available in the triangular-exponent normalization. -/
theorem denominatorSeries_eq_weylSeries (s w : ℂ) (hs : s ≠ 0) (hw : w ≠ 0)
    (hJacobi : ∀ x : ℂ, x ≠ 0 →
      Tendsto (jacobiPartial x) atTop (𝓝 (jacobiSeries x))) :
    denominatorSeries s w = weylSeries s w := by
  have hE := (WithPiTopology.hasProd_one_sub_X_pow ℂ).tendsto_prod_nat
  change Tendsto eulerPartial atTop _ at hE
  have hL := hE.mul (tendsto_denominatorPartial s w)
  have hR := (tendsto_const_nhds (x := PowerSeries.C (s*w^2)) (f := (atTop : Filter ℕ))).mul
    (((hJacobi (1/s) (div_ne_zero one_ne_zero hs)).mul
      (hJacobi (1/w) (div_ne_zero one_ne_zero hw))).mul
      (hJacobi (s/w) (div_ne_zero hs hw)))
  have hEq := tendsto_nhds_unique
    (hL.congr (euler_mul_denominatorPartial s w hs hw)) hR
  have hW := ((hasSum_weylSeries s w hs hw).mul_left (pentagonalSeries ℂ)).unique
    (hasSum_weyl_mul_euler s w hs hw)
  exact isUnit_eulerSeries_complex.mul_left_cancel (hEq.trans hW.symm)

private theorem exponent_nonneg (u v : ℤ) : 0 ≤ CMTheta.exponent u v := by
  have hn : 0 ≤ CMTheta.norm (CMTheta.primaryCoords u v).1 (CMTheta.primaryCoords u v).2 := by
    unfold CMTheta.norm
    nlinarith [sq_nonneg (CMTheta.primaryCoords u v).1,
      sq_nonneg (CMTheta.primaryCoords u v).2,
      sq_nonneg ((CMTheta.primaryCoords u v).1 - (CMTheta.primaryCoords u v).2)]
  rw [CMTheta.norm_primaryCoords] at hn
  omega

private theorem hasSum_expand_shift {ι : Type*} {f : ι → ℂ⟦X⟧} {g : ℂ⟦X⟧}
    (h : HasSum f g) :
    HasSum (fun i ↦ X * (f i).expand 3 (by decide)) (X * g.expand 3 (by decide)) := by
  rw [WithPiTopology.hasSum_iff_hasSum_coeff] at h ⊢
  intro d
  cases d with
  | zero => simp [coeff_zero_eq_constantCoeff]
  | succ d =>
      simp only [coeff_succ_X_mul, coeff_expand]
      split_ifs with hd
      · exact h (d / 3)
      · exact hasSum_zero

private theorem coe_denominatorPoly (s w : ℂ) (N : ℕ) :
    (↑(CMTheta.denominatorPoly N w s) : ℂ⟦X⟧) =
      X * (denominatorPartial s w N).expand 3 (by decide) := by
  change Polynomial.coeToPowerSeries.ringHom (CMTheta.denominatorPoly N w s) = _
  simp only [CMTheta.denominatorPoly, CMTheta.denominatorTail, denominatorPartial, rootPair,
    map_mul, map_prod, map_sub, map_one, map_pow, PowerSeries.expand_C, PowerSeries.expand_X,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X,
    ← pow_mul, inv_div, div_one]
  ring

private theorem expand_shift_monomial (d : ℕ) (z : ℂ) :
    X * (PowerSeries.monomial d z).expand 3 (by decide) =
      PowerSeries.monomial (1+3*d) z := by
  simp only [PowerSeries.monomial_eq_C_mul_X_pow, map_mul, map_pow, PowerSeries.expand_C,
    PowerSeries.expand_X, ← pow_mul]
  calc
    X * (PowerSeries.C z * X ^ (3*d)) = PowerSeries.C z * (X ^ 1 * X ^ (3*d)) := by
      rw [pow_one]; ring
    _ = PowerSeries.C z * X^(1+3*d) := by rw [pow_add]

theorem coeff_expand_shift_weylSeries (s w : ℂ) (hs : s ≠ 0) (hw : w ≠ 0) (n : ℕ) :
    PowerSeries.coeff n (X * (weylSeries s w).expand 3 (by decide)) =
      ∑ᶠ t : CMTheta.WeylFiber n, CMTheta.weylAlternant w s t.1.1 t.1.2 := by
  classical
  have hSummed := hasSum_expand_shift (hasSum_weylSeries s w hs hw)
  rw [WithPiTopology.hasSum_iff_hasSum_coeff] at hSummed
  have h := hSummed n
  simp only [expand_shift_monomial] at h
  let A (t : ℤ × ℤ) := CMTheta.weylAlternant w s t.1 t.2
  let T (t : ℤ × ℤ) := coeff n (PowerSeries.monomial
    (1 + 3 * (CMTheta.exponent t.1 t.2).toNat) (A t))
  have hp (t : ℤ × ℤ) :
      1+3*(CMTheta.exponent t.1 t.2).toNat = n ↔
        1+3*CMTheta.exponent t.1 t.2 = (n : ℤ) := by
    have hnonneg := exponent_nonneg t.1 t.2
    omega
  have hsub : Function.support T ⊆ {t : ℤ × ℤ | 1+3*CMTheta.exponent t.1 t.2 = (n : ℤ)} := by
    intro t ht
    by_contra hn
    apply ht
    have hneq : n ≠ 1+3*(CMTheta.exponent t.1 t.2).toNat := by
      intro heq
      exact hn ((hp t).mp heq.symm)
    simp [T, PowerSeries.coeff_monomial, hneq]
  have ht := (hasSum_subtype_iff_of_support_subset hsub).mpr h
  have ht' : HasSum (fun t : CMTheta.WeylFiber n ↦ A t.1)
      (PowerSeries.coeff n (X * (weylSeries s w).expand 3 (by decide))) := by
    apply ht.congr_fun
    intro t
    have heq := (hp t.1).mpr t.2
    simp [T, PowerSeries.coeff_monomial, heq]
  let := Fintype.ofFinite (CMTheta.WeylFiber n)
  rw [finsum_eq_sum_of_fintype]
  exact ((hasSum_fintype (fun t : CMTheta.WeylFiber n ↦ A t.1)).unique ht').symm

/-- Each finite polynomial coefficient required for the theta identity follows
from the one-dimensional Jacobi identity in triangular normalization. -/
theorem denominatorPoly_coeff_eq_weyl (s w : ℂ) (hs : s ≠ 0) (hw : w ≠ 0) (n : ℕ)
    (hJacobi : ∀ x : ℂ, x ≠ 0 →
      Tendsto (jacobiPartial x) atTop (𝓝 (jacobiSeries x))) :
    (CMTheta.denominatorPoly n w s).coeff n =
      ∑ᶠ t : CMTheta.WeylFiber n, CMTheta.weylAlternant w s t.1.1 t.1.2 := by
  rw [← coeff_expand_shift_weylSeries s w hs hw n,
    ← denominatorSeries_eq_weylSeries s w hs hw hJacobi, ← Polynomial.coeff_coe,
    coe_denominatorPoly s w n]
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ d =>
      simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand]
      split_ifs
      · simpa [denominatorSeries] using
          (denominatorPartial_coeff_stable s w (d / 3) (d+1) (by omega))
      · rfl

/-- The Jacobi product identities imply the eta coefficient formula used by
the Fermat cubic proof. -/
theorem etaCoeff_eq_primary_of_jacobi (w : ℂ) (hw : w^2+w+1=0) (n : ℕ)
    (hJacobi : ∀ x : ℂ, x ≠ 0 →
      Tendsto (jacobiPartial x) atTop (𝓝 (jacobiSeries x))) :
    (EtaSupport.etaCoeff n : ℂ) = CMTheta.primaryCoeff w n := by
  apply CMTheta.etaCoeff_eq_primary_of_macdonald w hw n
  intro s hs
  apply denominatorPoly_coeff_eq_weyl s w hs _ n hJacobi
  intro hzero
  simp [hzero] at hw

end BSD.MacdonaldA2
