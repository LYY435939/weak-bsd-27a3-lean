import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Product-side functional equations for the affine A₂ denominator of
Rosengren–Schlosser, Corollary 6.2. -/

namespace BSD.MacdonaldA2

/-- The multiplicative q-Pochhammer symbol (x;p)∞. -/
noncomputable def poch (p x : ℂ) : ℂ := ∏' n : ℕ, (1 - x * p ^ n)

theorem multipliable_poch {p : ℂ} (hp : ‖p‖ < 1) (x : ℂ) :
    Multipliable (fun n : ℕ ↦ 1 - x * p ^ n) := by
  apply multipliable_one_add_of_summable (f := fun n : ℕ ↦ -(x * p ^ n))
  simpa only [norm_neg, norm_mul, norm_pow] using
    (summable_geometric_of_lt_one (norm_nonneg p) hp).mul_left ‖x‖

theorem poch_shift {p : ℂ} (hp : ‖p‖ < 1) (x : ℂ) :
    poch p x = (1 - x) * poch p (p*x) := by
  unfold poch
  rw [tprod_eq_zero_mul']
  · simp [pow_succ, mul_left_comm, mul_assoc, mul_comm]
  · simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using multipliable_poch hp (p*x)

/-- Multiplicative theta, with no (p;p)∞ prefactor. -/
noncomputable def theta (p x : ℂ) : ℂ := poch p x * poch p (p/x)

theorem theta_shift {p x : ℂ} (hp : ‖p‖ < 1) (hp0 : p ≠ 0) (hx : x ≠ 0) :
    theta p (p*x) = -x⁻¹ * theta p x := by
  unfold theta
  rw [show p/(p*x) = x⁻¹ by field_simp, poch_shift hp x, poch_shift hp x⁻¹]
  rw [div_eq_mul_inv]
  ring_nf
  field_simp
  ring

theorem theta_inv {p x : ℂ} (hp : ‖p‖ < 1) (hx : x ≠ 0) :
    theta p x⁻¹ = -x⁻¹ * theta p x := by
  unfold theta
  rw [poch_shift hp x, poch_shift hp x⁻¹]
  simp only [div_eq_mul_inv, inv_inv]
  ring_nf
  field_simp
  ring

/-- The elliptic replacement of the difference y-x. -/
noncomputable def difference (p x y : ℂ) : ℂ := y * theta p (x/y)

theorem difference_swap {p x y : ℂ} (hp : ‖p‖ < 1) (hx : x ≠ 0) (hy : y ≠ 0) :
    difference p y x = -difference p x y := by
  unfold difference
  rw [show y/x = (x/y)⁻¹ by simp, theta_inv hp (div_ne_zero hx hy)]
  field_simp

theorem difference_shift_left {p x y : ℂ} (hp : ‖p‖ < 1) (hp0 : p ≠ 0) (hx : x ≠ 0)
    (hy : y ≠ 0) : difference p (p*x) y = -(y/x) * difference p x y := by
  unfold difference
  rw [mul_div_assoc, theta_shift hp hp0 (div_ne_zero hx hy)]
  simp only [inv_div]
  ring

theorem difference_shift_right {p x y : ℂ} (hp : ‖p‖ < 1) (hp0 : p ≠ 0) (hx : x ≠ 0)
    (hy : y ≠ 0) : difference p x (p*y) = -(x/y) * difference p x y := by
  rw [difference_swap hp (mul_ne_zero hp0 hy) hx, difference_shift_left hp hp0 hy hx,
    difference_swap hp hx hy]
  ring

/-- The product W_A₂(x,y,z) from the elliptic Weyl denominator. -/
noncomputable def denominator (p x y z : ℂ) : ℂ :=
  difference p x y * difference p x z * difference p y z

theorem denominator_shift_x {p x y z : ℂ} (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    denominator p (p*x) y z = (y*z/x^2) * denominator p x y z := by
  simp only [denominator, difference_shift_left hp hp0 hx hy, difference_shift_left hp hp0 hx hz]
  ring

theorem denominator_shift_y {p x y z : ℂ} (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    denominator p x (p*y) z = (x*z/y^2) * denominator p x y z := by
  simp only [denominator, difference_shift_right hp hp0 hx hy, difference_shift_left hp hp0 hy hz]
  ring

theorem denominator_shift_z {p x y z : ℂ} (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    denominator p x y (p*z) = (x*y/z^2) * denominator p x y z := by
  simp only [denominator, difference_shift_right hp hp0 hx hz, difference_shift_right hp hp0 hy hz]
  ring

/-- Degree of the nth monomial in a Jacobi triple product. -/
def tri (n : ℤ) : ℕ := (n * (n-1) / 2).toNat

theorem two_mul_tri (n : ℤ) : 2 * (tri n : ℤ) = n*(n-1) := by
  have h : 0 ≤ n*(n-1) := by
    by_cases hn : 1 ≤ n
    · exact mul_nonneg (by omega) (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  rw [tri, Int.toNat_of_nonneg (Int.ediv_nonneg h (by decide))]
  exact Int.two_mul_ediv_two_of_even n.even_mul_pred_self

/-- In x₂x₃² times the three theta series with arguments
x₁/x₂, x₁/x₃, x₂/x₃, the terms at weight (A,1+C,2-A-C) form this fiber. -/
def weightFiberEquiv (A C : ℤ) :
    ℤ ≃ {n : ℤ × ℤ × ℤ // n.1+n.2.1 = A ∧ n.2.2-n.1 = C} where
  toFun i := ⟨(i, A-i, C+i), by simp⟩
  invFun n := n.1.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨i,j,k⟩,h1,h2⟩
    dsimp at h1 h2
    obtain rfl : j = A-i := by omega
    obtain rfl : k = C+i := by omega
    rfl

private theorem degree_translate_int (i u v : ℤ) :
    (tri i : ℤ) + tri (3*u-i) + tri (3*v+i) =
    pentagonal (i+v-u) + (3*(u^2+u*v+v^2)-2*u-v) := by
  have h₁ := two_mul_tri i
  have h₂ := two_mul_tri (3*u-i)
  have h₃ := two_mul_tri (3*v+i)
  have h₄ := two_mul_natCast_pentagonal (i+v-u)
  linarith

theorem degree_translate (i u v : ℤ) :
    tri i + tri (3*u-i) + tri (3*v+i) =
    pentagonal (i+v-u) + (3*(u^2+u*v+v^2)-2*u-v).toNat := by
  have h := degree_translate_int i u v
  have h0 := degree_translate_int (u-v) u v
  rw [show u-v+v-u = 0 by ring] at h0
  have hpos : 0 ≤ 3*(u^2+u*v+v^2)-2*u-v := by
    norm_num [pentagonal] at h0
    omega
  omega

open scoped PowerSeries.WithPiTopology

/-- The entire Laurent-weight coefficient of the three Jacobi series,
with the degree variable left formal, is Euler's product times a single
monomial. The exponent agrees with the rank-two Macdonald translation. -/
theorem hasSum_primary_weight (u v : ℤ) :
    HasSum (fun i : ℤ ↦ (Int.negOnePow (i+(3*u-i)+(3*v+i)) : PowerSeries ℤ) *
      PowerSeries.X ^ (tri i + tri (3*u-i) + tri (3*v+i)))
      (PowerSeries.pentagonalSeries ℤ *
        PowerSeries.X ^ (3*(u^2+u*v+v^2)-2*u-v).toNat) := by
  have h := (PowerSeries.WithPiTopology.hasSum_pentagonalSeries ℤ).mul_right
    (PowerSeries.X ^ (3*(u^2+u*v+v^2)-2*u-v).toNat)
  have h' := (Equiv.addRight (v-u)).hasSum_iff.mpr h
  apply h'.congr_fun
  intro i
  have hsign : (i+(3*u-i)+(3*v+i)).negOnePow = (i+v-u).negOnePow :=
    (Int.negOnePow_eq_iff _ _).2 ⟨2*u+v, by ring⟩
  simp only [Function.comp_apply, Equiv.coe_addRight, degree_translate, hsign, pow_add,
    add_sub_assoc, mul_assoc]

/-- Formal monomial of the product of the three bilateral Jacobi series at
a fixed Laurent weight and free summation index. -/
noncomputable def weightTerm (A C i : ℤ) : PowerSeries ℤ :=
  PowerSeries.monomial (tri i + tri (A-i) + tri (C+i)) (Int.negOnePow (i+(A-i)+(C+i)) : ℤ)

theorem summable_weightTerm (A C : ℤ) : Summable (weightTerm A C) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  apply (Set.finite_Icc (-(2*(d : ℤ)+1)) (2*(d : ℤ)+1)).subset
  intro i hi
  have hi' : d = tri i + tri (A-i) + tri (C+i) := by
    by_contra h
    exact hi (by simp [weightTerm, PowerSeries.coeff_monomial, h])
  have hle : (tri i : ℤ) ≤ d := by omega
  constructor <;> nlinarith only [hle, two_mul_tri i, sq_nonneg (i-1), sq_nonneg i]

private theorem weightTerm_reflect (A m i : ℤ) :
    weightTerm A (A+3*m+2) (-(2*m+1)-i) = -weightTerm A (A+3*m+2) i := by
  let j := -(2*m+1)-i
  let C := A+3*m+2
  have hd : tri j + tri (A-j) + tri (C+j) = tri i + tri (A-i) + tri (C+i) := by
    have h₁ := two_mul_tri j
    have h₂ := two_mul_tri (A-j)
    have h₃ := two_mul_tri (C+j)
    have h₄ := two_mul_tri i
    have h₅ := two_mul_tri (A-i)
    have h₆ := two_mul_tri (C+i)
    dsimp [j,C] at *
    zify
    linarith
  have hs : (j+(A-j)+(C+j)).negOnePow = -(i+(A-i)+(C+i)).negOnePow := by
    rw [← Int.negOnePow_succ]
    apply (Int.negOnePow_eq_iff _ _).2
    exact ⟨-m-1-i, by dsimp [j,C]; ring⟩
  change PowerSeries.monomial _ ((j+(A-j)+(C+j)).negOnePow : ℤ) = _
  rw [show tri (-(2*m+1)-i) + tri (A-(-(2*m+1)-i)) + tri (A+3*m+2+(-(2*m+1)-i)) = _
    from hd, hs]
  simp [weightTerm,C]

/-- Singular weights have all three exponents congruent modulo three.
Reflection exchanges their summands with opposite signs. -/
theorem hasSum_singular_weight (A m : ℤ) : HasSum (weightTerm A (A+3*m+2)) 0 := by
  let f := weightTerm A (A+3*m+2)
  have hs : Summable f := summable_weightTerm _ _
  have h₁ := ((Equiv.subLeft (-(2*m+1))).hasSum_iff.mpr hs.hasSum)
  have h₂ : HasSum (fun i ↦ -(f i)) (∑' i, f i) := by
    apply h₁.congr_fun
    exact fun i ↦ (weightTerm_reflect A m i).symm
  have heq := h₂.unique hs.hasSum.neg
  have hz : (∑' i, f i) = 0 := by
    ext n
    have hc := congrArg (PowerSeries.coeff n) heq
    rw [map_neg] at hc
    rw [map_zero]
    omega
  exact hz ▸ hs.hasSum

theorem tri_reflect (n : ℤ) : tri (1-n) = tri n := by
  have := two_mul_tri (1-n)
  have := two_mul_tri n
  zify
  linarith

/-- The Laurent-weight coefficient of the three Jacobi sums. -/
noncomputable def weightCoeff (A C : ℤ) : PowerSeries ℤ := ∑' i, weightTerm A C i

theorem weightCoeff_primary (u v : ℤ) :
    weightCoeff (3*u) (3*v) = PowerSeries.pentagonalSeries ℤ *
      PowerSeries.X ^ (3*(u^2+u*v+v^2)-2*u-v).toNat := by
  apply HasSum.tsum_eq
  apply (hasSum_primary_weight u v).congr_fun
  intro i
  simp [weightTerm, PowerSeries.monomial_eq_C_mul_X_pow]

theorem weightCoeff_singular (A m : ℤ) : weightCoeff A (A+3*m+2) = 0 :=
  (hasSum_singular_weight A m).tsum_eq

private theorem sign_flip (a b : ℤ) (h : Even (a-(b+1))) :
    a.negOnePow = -b.negOnePow := ((Int.negOnePow_eq_iff _ _).2 h).trans (Int.negOnePow_succ b)

theorem weightCoeff_swap12 (A C : ℤ) : weightCoeff (1+C) (A-1) = -weightCoeff A C := by
  have t (i : ℤ) : weightTerm (1+C) (A-1) (1-i) = -weightTerm A C i := by
    have hs := sign_flip ((1-i)+(1+C-(1-i))+(A-1+(1-i))) (i+(A-i)+(C+i))
      ⟨-i, by ring⟩
    unfold weightTerm
    rw [hs, tri_reflect, show 1+C-(1-i) = C+i by ring,
      show A-1+(1-i) = A-i by ring, add_right_comm (tri i)]
    simp
  unfold weightCoeff
  rw [← (Equiv.subLeft (1 : ℤ)).tsum_eq (weightTerm (1+C) (A-1))]
  simp only [Equiv.subLeft_apply, t, tsum_neg]

theorem weightCoeff_swap23 (A C : ℤ) : weightCoeff A (1-A-C) = -weightCoeff A C := by
  have t (i : ℤ) : weightTerm A (1-A-C) (A-i) = -weightTerm A C i := by
    have hs := sign_flip ((A-i)+(A-(A-i))+(1-A-C+(A-i))) (i+(A-i)+(C+i))
      ⟨-C-i, by ring⟩
    unfold weightTerm
    rw [hs, show A-(A-i) = i by ring, show 1-A-C+(A-i) = 1-(C+i) by ring,
      tri_reflect, add_comm (tri (A-i)) (tri i)]
    simp
  unfold weightCoeff
  rw [← (Equiv.subLeft A).tsum_eq (weightTerm A (1-A-C))]
  simp only [Equiv.subLeft_apply, t, tsum_neg]

private theorem swap_first_two (a b : ℤ) :
    weightCoeff b (a-1) = -weightCoeff a (b-1) := by
  simpa using weightCoeff_swap12 a (b-1)

private theorem swap_last_two (a b c : ℤ) (h : a+b+c = 3) :
    weightCoeff a (c-1) = -weightCoeff a (b-1) := by
  rw [show c-1 = 1-a-(b-1) by omega, weightCoeff_swap23]

private theorem swap_outer (a b c : ℤ) (h : a+b+c = 3) :
    weightCoeff c (b-1) = -weightCoeff a (b-1) := by
  rw [swap_first_two b c, swap_last_two b a c (by omega), swap_first_two a b, neg_neg]

private theorem weightCoeff_swap (k : Fin 3 → ℤ) (h : ∑ j, k j = 3)
    (i j : Fin 3) (hne : i ≠ j) :
    weightCoeff (k (Equiv.swap i j 0)) (k (Equiv.swap i j 1)-1) =
      -weightCoeff (k 0) (k 1-1) := by
  have hk : k 0 + k 1 + k 2 = 3 := by simpa [Fin.sum_univ_three, add_assoc] using h
  have h₁ := swap_first_two (k 0) (k 1)
  have h₂ := swap_last_two (k 0) (k 1) (k 2) hk
  have h₃ := swap_outer (k 0) (k 1) (k 2) hk
  fin_cases i <;> fin_cases j <;> first | exact False.elim (hne rfl) | exact h₁ | exact h₂ | exact h₃

theorem weightCoeff_permute (k : Fin 3 → ℤ) (h : ∑ j, k j = 3) (σ : Equiv.Perm (Fin 3)) :
    weightCoeff (k (σ 0)) (k (σ 1)-1) = σ.sign • weightCoeff (k 0) (k 1-1) := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap σ i j hne ih =>
    have hk : ∑ a, (k ∘ σ) a = 3 := (Equiv.sum_comp σ k).trans h
    have hs := weightCoeff_swap (k ∘ σ) hk i j hne
    simpa [Equiv.Perm.mul_apply, Function.comp_apply, Equiv.Perm.sign_swap hne, ih] using hs

/-- The integer exponents in the three columns of the A₂ alternant. -/
def exponents (u v : ℤ) : Fin 3 → ℤ := ![3*u,1+3*v,2-3*u-3*v]

/-- Every permutation contributes exactly the sign appearing in the Weyl alternant. -/
theorem weightCoeff_weyl (u v : ℤ) (σ : Equiv.Perm (Fin 3)) :
    weightCoeff (exponents u v (σ 0)) (exponents u v (σ 1) - 1) =
      σ.sign • (PowerSeries.pentagonalSeries ℤ *
        PowerSeries.X ^ (3*(u^2+u*v+v^2)-2*u-v).toNat) := by
  rw [weightCoeff_permute]
  · simp [exponents, weightCoeff_primary]
  · simp [exponents, Fin.sum_univ_three]; ring

/-- Residue class used to label the three columns. -/
def residue (a : ℤ) : Fin 3 := ⟨(a%3).toNat, by omega⟩

@[simp] theorem residue_exponents (u v : ℤ) (i : Fin 3) : residue (exponents u v i) = i := by
  apply Fin.ext
  fin_cases i <;> simp [exponents, residue]

/-- The ordering of a regular weight's coordinates is recovered from their residues. -/
def RegularWeight := {k : Fin 3 → ℤ // ∑ i, k i = 3 ∧ Function.Bijective (residue ∘ k)}

private def orbitWeight (w : Equiv.Perm (Fin 3) × ℤ × ℤ) : RegularWeight :=
  ⟨exponents w.2.1 w.2.2 ∘ w.1, by
    constructor
    · simp only [Function.comp_apply, Equiv.sum_comp, Fin.sum_univ_three]
      simp [exponents]; ring
    · simp [Function.comp_def]⟩

theorem orbitWeight_injective : Function.Injective orbitWeight := by
  rintro ⟨σ,u,v⟩ ⟨τ,a,b⟩ heq
  have h (i : Fin 3) : exponents u v (σ i) = exponents a b (τ i) := congrFun (Subtype.ext_iff.mp heq) i
  have hp : σ = τ := Equiv.ext fun i ↦ by simpa using congrArg residue (h i)
  subst τ
  have hu := h (σ.symm 0)
  have hv := h (σ.symm 1)
  simp [exponents] at hu hv
  obtain rfl : u = a := by omega
  obtain rfl : v = b := by omega
  rfl

theorem orbitWeight_surjective : Function.Surjective orbitWeight := by
  intro ⟨k,ht,hr⟩
  let σ := Equiv.ofBijective (residue ∘ k) hr
  let f := k ∘ σ.symm
  have hres (i : Fin 3) : residue (f i) = i := σ.apply_symm_apply i
  have htot : f 0 + f 1 + f 2 = 3 := by
    have := (Equiv.sum_comp σ.symm k).trans ht
    simpa [f, Fin.sum_univ_three, add_assoc] using this
  have h0 := congrArg Fin.val (hres 0)
  have h1 := congrArg Fin.val (hres 1)
  change ((f 0)%3).toNat = 0 at h0
  change ((f 1)%3).toNat = 1 at h1
  refine ⟨(σ, (f 0)/3, ((f 1)-1)/3), Subtype.ext ?_⟩
  ext i
  change exponents _ _ (σ i) = k i
  obtain ⟨j,rfl⟩ := σ.symm.surjective i
  rw [σ.apply_symm_apply]
  change exponents _ _ j = f j
  fin_cases j <;> simp [exponents] <;> omega

/-- Reindexing the entire regular Laurent lattice by a Weyl permutation and
two independent integral translations introduces neither omissions nor multiplicities. -/
noncomputable def regularOrbitEquiv : (Equiv.Perm (Fin 3) × ℤ × ℤ) ≃ RegularWeight :=
  Equiv.ofBijective orbitWeight ⟨orbitWeight_injective, orbitWeight_surjective⟩

@[simp] theorem regularOrbitEquiv_apply (σ : Equiv.Perm (Fin 3)) (u v : ℤ) (i : Fin 3) :
    (regularOrbitEquiv (σ,u,v)).1 i = exponents u v (σ i) := rfl

/-- The complementary lattice consists of the singular weights. -/
theorem weightCoeff_of_not_regular (k : Fin 3 → ℤ) (ht : ∑ i, k i = 3)
    (hs : ¬Function.Bijective (residue ∘ k)) : weightCoeff (k 0) (k 1 - 1) = 0 := by
  have hn : ¬Function.Injective (residue ∘ k) :=
    fun hi ↦ hs (Finite.injective_iff_bijective.mp hi)
  have ht' : k 0 + k 1 + k 2 = 3 := by simpa [Fin.sum_univ_three, add_assoc] using ht
  simp only [Function.Injective, not_forall, Function.comp_apply] at hn
  obtain ⟨i,j,hh⟩ := hn
  obtain ⟨he,hne⟩ := hh
  have hr := congrArg Fin.val he
  change ((k i)%3).toNat = ((k j)%3).toNat at hr
  have hr' : k i ≡ k j [ZMOD 3] := by
    change k i % 3 = k j % 3
    omega
  obtain ⟨t,hts⟩ := Int.modEq_iff_dvd.mp hr'
  have hdiv : 3 ∣ k 1 - k 0 := by
    have h01 (h : k 1-k 0=3*t) : 3 ∣ k 1-k 0 := ⟨t,h⟩
    have h10 (h : k 0-k 1=3*t) : 3 ∣ k 1-k 0 := ⟨-t,by linarith⟩
    have h02 (h : k 2-k 0=3*t) : 3 ∣ k 1-k 0 := ⟨1-k 0-t,by linarith⟩
    have h20 (h : k 0-k 2=3*t) : 3 ∣ k 1-k 0 := ⟨1-k 0+t,by linarith⟩
    have h12 (h : k 2-k 1=3*t) : 3 ∣ k 1-k 0 := ⟨k 1+t-1,by linarith⟩
    have h21 (h : k 1-k 2=3*t) : 3 ∣ k 1-k 0 := ⟨k 1-t-1,by linarith⟩
    fin_cases i <;> fin_cases j <;> first
      | exact False.elim (hne rfl)
      | exact h01 hts | exact h10 hts | exact h02 hts | exact h20 hts
      | exact h12 hts | exact h21 hts
  obtain ⟨d,hd⟩ := hdiv
  rw [show k 1-1 = k 0 + 3*(d-1) + 2 by omega, weightCoeff_singular]

end BSD.MacdonaldA2
