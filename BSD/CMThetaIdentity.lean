import BSD.CoefficientsEta
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# The rank-two lattice in the level-27 CM eta product

We specialize the finite alternant and the Euler factors in the affine
A₂ denominator formula (Rosengren–Schlosser, Corollary 6.2). These results
do not assume that denominator identity. The identity itself is needed to
identify the two sides as formal series.

For the paper proof, put p = q³, x = (1,s,w), w²+w+1 = 0 in the first
identity of [Rosengren–Schlosser, Corollary 6.2]
(https://www.mat.univie.ac.at/~schlosse/pdf/determinants-new.pdf).
In that identity the product is E(p)² times the ordinary Vandermonde
and the remaining factors recorded in `rootFactor`, where
E(p) = ∏_{j≥1}(1-pʲ). On grouping permutations by the residue of the
three translation coordinates modulo 3, its right side is
∑_{u,v} p^{exponent u v} weylAlternant(w,s,u,v).
Each p coefficient is a Laurent polynomial in s. Differentiate it at s = 1
and multiply by q. On the left the result is
(w−1)² q E(q³)² E(q⁹)² by `hasDerivAt_finiteDenominator`, since
factors above the requested degree do not affect it. On the right
`weylCoeff_eq_primary` gives (w−1)² primaryCoeff(w,n) at degree n.
Cancel the nonzero constant. This gives equality of the normalized
eta-product series and the primary theta series, conditional in Lean on
the affine denominator formula. The specialization does not require a
complex analytic interchange of an infinite sum and a derivative.
-/

namespace BSD.CMTheta

open Finset

def norm (a b : ℤ) : ℤ := a ^ 2 - a * b + b ^ 2

/-- The A₂ exponent after summing over the six permutations in Cor. 6.2. -/
def exponent (u v : ℤ) : ℤ := 3 * (u ^ 2 + u * v + v ^ 2) - 2 * u - v

def primaryCoords (u v : ℤ) : ℤ × ℤ := (1 - 3 * u - 3 * v, -3 * v)

/-- Twice the integer exponent of p in the affine Weyl sum. Its three
translation coordinates are u, v and -u-v, and its residues are 0,1,2. -/
theorem twice_exponent (u v : ℤ) :
    2 * exponent u v =
      3 * (u * (u - 1) + v * (v - 1) + (-u-v) * (-u-v-1)) +
      2 * (v + 2 * (-u-v)) := by unfold exponent; ring

theorem norm_primaryCoords (u v : ℤ) :
    norm (primaryCoords u v).1 (primaryCoords u v).2 = 1 + 3 * exponent u v := by
  unfold norm primaryCoords exponent
  dsimp
  ring

def PrimaryFiber (n : ℤ) := {z : ℤ × ℤ //
  (3 ∣ z.1 - 1) ∧ (3 ∣ z.2) ∧ norm z.1 z.2 = n}

def WeylFiber (n : ℤ) := {z : ℤ × ℤ // 1 + 3 * exponent z.1 z.2 = n}

/-- Every primary generator appears exactly once in the grouped Weyl sum,
including at norms divisible by a square. -/
def fiberEquiv (n : ℤ) : WeylFiber n ≃ PrimaryFiber n where
  toFun z := ⟨primaryCoords z.1.1 z.1.2,
    ⟨⟨-z.1.1-z.1.2, by simp [primaryCoords]; ring⟩,
     ⟨-z.1.2, by simp [primaryCoords]⟩, (norm_primaryCoords ..).trans z.2⟩⟩
  invFun z := ⟨((1 - z.1.1 + z.1.2) / 3, -(z.1.2 / 3)), by
    rcases z with ⟨⟨a,b⟩, ⟨⟨s,hs⟩, ⟨t,ht⟩, hn⟩⟩
    dsimp at hs ht hn ⊢
    rw [← norm_primaryCoords]
    apply Eq.trans _ hn
    congr 1 <;> simp [primaryCoords] <;> omega⟩
  left_inv := by
    rintro ⟨⟨u,v⟩, _⟩
    apply Subtype.ext
    apply Prod.ext <;> simp [primaryCoords] <;> omega
  right_inv := by
    rintro ⟨⟨a,b⟩, ⟨⟨s,hs⟩, ⟨t,ht⟩, _⟩⟩
    apply Subtype.ext
    apply Prod.ext <;> simp [primaryCoords] <;> omega

/-- Cofactor expansion of the derivative in the middle row at x=(1,1,w).
The monomial exponents in the last row reduce modulo three. -/
def alternantDeriv {R : Type*} [CommRing R] (w : R) (u v : ℤ) : R :=
  (3 * (u : R)) * (w - w^2) + (1 + 3 * (v : R)) * (w^2 - 1) +
  (2 - 3 * (u : R) - 3 * (v : R)) * (1 - w)

theorem alternantDeriv_eq {R : Type*} [CommRing R] (w : R)
    (hw : w^2 + w + 1 = 0) (u v : ℤ) :
    alternantDeriv w u v = (w - 1)^2 *
      ((primaryCoords u v).1 + ((primaryCoords u v).2 : R) * w) := by
  simp only [alternantDeriv, primaryCoords, Int.cast_sub, Int.cast_one, Int.cast_mul,
    Int.cast_ofNat, Int.cast_neg]
  linear_combination (3 * (v : R) * (w - 1)) * hw

/-- The six terms of the determinant before taking the derivative. -/
noncomputable def weylAlternant (w s : ℂ) (u v : ℤ) : ℂ :=
  Matrix.det !![1, 1, 1;
    s ^ (3*u), s ^ (1+3*v), s ^ (2-3*u-3*v);
    w ^ (3*u), w ^ (1+3*v), w ^ (2-3*u-3*v)]

theorem hasDerivAt_weylAlternant (w : ℂ) (hw : w^2 + w + 1 = 0) (u v : ℤ) :
    HasDerivAt (fun s ↦ weylAlternant w s u v) (alternantDeriv w u v) 1 := by
  have hw3 : w^3 = 1 := by linear_combination (w-1) * hw
  have hw0 : w ≠ 0 := by intro hz; simp [hz] at hw
  have h3 (k : ℤ) : w ^ (3*k) = 1 := by
    rw [zpow_mul]
    norm_num [hw3]
  have h1 : w ^ (1+3*v) = w := by rw [zpow_add₀ hw0, h3]; simp
  have h2 : w ^ (2-3*u-3*v) = w^2 := by
    rw [show 2-3*u-3*v = 2+3*(-u-v) by ring, zpow_add₀ hw0, h3]; simp
  have hd (k : ℤ) : HasDerivAt (fun s : ℂ ↦ s^k) (k : ℂ) 1 := by
    simpa using hasDerivAt_zpow k (1 : ℂ) (Or.inl one_ne_zero)
  have h := (((hd (3*u)).mul_const (w-w^2)).add
    ((hd (1+3*v)).mul_const (w^2-1))).add ((hd (2-3*u-3*v)).mul_const (1-w))
  have he (s : ℂ) : weylAlternant w s u v = s^(3*u)*(w-w^2) +
      s^(1+3*v)*(w^2-1) + s^(2-3*u-3*v)*(1-w) := by
    simp only [weylAlternant, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h3, h1, h2]
    ring
  simp_rw [he]
  simpa [alternantDeriv, Pi.add_def] using h

/-- The paired cyclotomic factors on the product side at x=(1,1,w). -/
theorem cubic_factor {R : Type*} [CommRing R] (w t : R) (hw : w^2 + w + 1 = 0) :
    (1 - t) * (1 - w*t) * (1 - w^2*t) = 1 - t^3 := by
  linear_combination (-(w-1) * t^3 + w * t^2 - t) * hw

theorem product_specialization {R : Type*} [CommRing R] (w p : R)
    (hw : w^2 + w + 1 = 0) (N : ℕ) :
    (∏ k ∈ range N, (1 - p^(k+1))^4 *
      ((1 - w*p^(k+1)) * (1 - w^2*p^(k+1)))^2) =
    ∏ k ∈ range N, (1-p^(k+1))^2 * (1-(p^(k+1))^3)^2 := by
  apply prod_congr rfl
  intro k _
  rw [← cubic_factor w (p^(k+1)) hw]
  ring

/-- The product factors remaining after factoring out the ordinary Vandermonde
from the Weyl denominator at x=(1,s,w). -/
noncomputable def rootFactor (p s w : ℂ) : ℂ :=
  (1-p)^2 * ((1-p/s)*(1-p*s)) * ((1-p/w)*(1-p*w)) *
    ((1-p*s/w)*(1-p*w/s))

noncomputable def finiteDenominator (p s w : ℂ) (N : ℕ) : ℂ :=
  (s-1)*(w-1)*(w-s) * ∏ k ∈ range N, rootFactor (p^(k+1)) s w

private theorem rootFactor_one (w p : ℂ) (hw : w^2 + w + 1 = 0) :
    rootFactor p 1 w = (1-p)^2 * (1-p^3)^2 := by
  have hw0 : w ≠ 0 := by intro hz; simp [hz] at hw
  have hinv : w⁻¹ = w^2 := by
    field_simp
    linear_combination -(w-1)*hw
  simp only [rootFactor, mul_one, div_eq_mul_inv, hinv]
  rw [← cubic_factor w p hw]
  ring

/-- The derivative of the actual finite Weyl product specializes to the eta
Euler factors, including the constant (w-1)² from the coalescing variables. -/
theorem hasDerivAt_finiteDenominator (p w : ℂ) (hw : w^2 + w + 1 = 0) (N : ℕ) :
    HasDerivAt (fun s ↦ finiteDenominator p s w N)
      ((w-1)^2 * ∏ k ∈ range N, (1-p^(k+1))^2*(1-(p^(k+1))^3)^2) 1 := by
  let g (s : ℂ) := (w-1)*(w-s) * ∏ k ∈ range N, rootFactor (p^(k+1)) s w
  have hw0 : w ≠ 0 := by intro hz; simp [hz] at hw
  have hg : DifferentiableAt ℂ g 1 := by
    dsimp [g, rootFactor]
    fun_prop (disch := norm_num [hw0])
  have hd := ((hasDerivAt_id (1 : ℂ)).sub_const 1).mul hg.hasDerivAt
  have hprod : (fun s ↦ finiteDenominator p s w N) = (fun s ↦ (id s - 1)*g s) := by
    funext s
    dsimp [finiteDenominator, g]
    ring
  rw [hprod]
  simpa [g, rootFactor_one w _ hw, sq, mul_assoc, Pi.mul_def] using hd

private theorem norm_bounds {a b n : ℤ} (h : norm a b = n) :
    (- (2*n+1) ≤ a ∧ a ≤ 2*n+1) ∧ (- (2*n+1) ≤ b ∧ b ≤ 2*n+1) := by
  unfold norm at h
  have hn : 0 ≤ n := by nlinarith [sq_nonneg (a-b), sq_nonneg a, sq_nonneg b]
  constructor <;> constructor <;>
    nlinarith [sq_nonneg (2*b-a), sq_nonneg (2*a-b),
      sq_nonneg (a-1), sq_nonneg (a+1), sq_nonneg (b-1), sq_nonneg (b+1)]

instance (n : ℤ) : Finite (PrimaryFiber n) := by
  let K := Finset.Icc (-(2*n+1)) (2*n+1)
  let f (z : PrimaryFiber n) : K × K :=
    let h := norm_bounds z.2.2.2
    (⟨z.1.1, Finset.mem_Icc.mpr h.1⟩, ⟨z.1.2, Finset.mem_Icc.mpr h.2⟩)
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z : K × K ↦ (z.1 : ℤ)) h)
    (congrArg (fun z : K × K ↦ (z.2 : ℤ)) h)

instance (n : ℤ) : Finite (WeylFiber n) :=
  Finite.of_injective (fiberEquiv n) (fiberEquiv n).injective

/-- The coefficient of the primary Eisenstein-integer theta series. -/
noncomputable def primaryCoeff {R : Type*} [CommRing R] (w : R) (n : ℤ) : R :=
  ∑ᶠ z : PrimaryFiber n, ((z.1.1 : R) + (z.1.2 : R)*w)

/-- Equality of the finite fiber sums at every integer exponent. -/
theorem weylCoeff_eq_primary {R : Type*} [CommRing R] (w : R)
    (hw : w^2 + w + 1 = 0) (n : ℤ) :
    (∑ᶠ z : WeylFiber n, alternantDeriv w z.1.1 z.1.2) =
      (w - 1)^2 * primaryCoeff w n := by
  unfold primaryCoeff
  classical
  let := Fintype.ofFinite (WeylFiber n)
  let := Fintype.ofFinite (PrimaryFiber n)
  simp only [finsum_eq_sum_of_fintype, alternantDeriv_eq w hw, ← Finset.mul_sum]
  congr 1
  exact (fiberEquiv n).sum_comp (fun z : PrimaryFiber n ↦ (z.1.1 : R) + (z.1.2 : R)*w)

noncomputable section

open Polynomial

/-- The finite *undifferentiated* Weyl product at x=(1,s,w), after p=q³
and the leading q, with the Vandermonde removed. q is the polynomial variable. -/
def denominatorTail (N : ℕ) (w s : ℂ) : Polynomial ℂ :=
  X * ∏ k ∈ range N,
    let T := (X : Polynomial ℂ)^(3*(k+1))
    (1 - T)^2 * ((1 - C (1/s)*T)*(1 - C s*T)) *
      ((1 - C (1/w)*T)*(1 - C w*T)) *
      ((1 - C (s/w)*T)*(1 - C (w/s)*T))

/-- The raw Weyl denominator including the ordinary Vandermonde. -/
def denominatorPoly (N : ℕ) (w s : ℂ) : Polynomial ℂ :=
  C ((s-1)*(w-1)*(w-s)) * denominatorTail N w s

private def CoeffDiff (f : ℂ → Polynomial ℂ) : Prop :=
  ∀ n, DifferentiableAt ℂ (fun s ↦ (f s).coeff n) 1

private theorem cd_const (p : Polynomial ℂ) : CoeffDiff (fun _ ↦ p) :=
  fun _ ↦ differentiableAt_const _

private theorem cd_C {f : ℂ → ℂ} (h : DifferentiableAt ℂ f 1) :
    CoeffDiff (fun s ↦ C (f s)) := by
  intro n
  cases n <;> simp [Polynomial.coeff_C, h]

private theorem cd_mul {f g : ℂ → Polynomial ℂ} (hf : CoeffDiff f) (hg : CoeffDiff g) :
    CoeffDiff (fun s ↦ f s * g s) := by
  intro n
  simp_rw [Polynomial.coeff_mul]
  apply DifferentiableAt.fun_sum
  intro i _
  exact (hf i.1).mul (hg i.2)

private theorem cd_sub {f g : ℂ → Polynomial ℂ} (hf : CoeffDiff f) (hg : CoeffDiff g) :
    CoeffDiff (fun s ↦ f s - g s) := by
  intro n
  simp_rw [Polynomial.coeff_sub]
  exact (hf n).sub (hg n)

private theorem cd_prod {ι : Type*} (I : Finset ι) (f : ι → ℂ → Polynomial ℂ)
    (h : ∀ i ∈ I, CoeffDiff (f i)) : CoeffDiff (fun s ↦ ∏ i ∈ I, f i s) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using cd_const 1
  | insert i I hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact cd_mul (h i (by simp)) (ih fun j hj ↦ h j (by simp [hj]))

private theorem cd_tail (N : ℕ) (w : ℂ) :
    CoeffDiff (denominatorTail N w) := by
  unfold denominatorTail
  apply cd_mul (cd_const _)
  apply cd_prod
  intro k _
  dsimp only
  repeat' first | apply cd_mul | apply cd_sub | exact cd_const _ | apply cd_C
  all_goals fun_prop (disch := norm_num)

private theorem denominatorTail_one (N : ℕ) (w : ℂ) (hw : w^2+w+1=0) :
    denominatorTail N w 1 = (EtaSupport.etaPoly N).map (Int.castRingHom ℂ) := by
  apply Polynomial.funext
  intro q
  simp only [denominatorTail, eval_mul, eval_X, eval_prod, eval_sub, eval_one, eval_pow, eval_C]
  rw [Polynomial.eval_map, EtaSupport.etaPoly_eval]
  apply congrArg (q * ·)
  apply Finset.prod_congr rfl
  intro k _
  have h := rootFactor_one w (q^(3*(k+1))) hw
  rw [← pow_mul, show 3*(k+1)*3=9*(k+1) by omega] at h
  simpa [rootFactor, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- Differentiating a fixed coefficient at s=1 produces the actual integral
eta coefficient defined from the stabilized Euler product in CoefficientsEta. -/
theorem hasDerivAt_denominatorCoeff (w : ℂ) (hw : w^2+w+1=0) {n N : ℕ} (hn : n ≤ N) :
    HasDerivAt (fun s ↦ (denominatorPoly N w s).coeff n)
      ((w-1)^2 * (EtaSupport.etaCoeff n : ℂ)) 1 := by
  have hd := (cd_tail N w n).hasDerivAt
  have he : (denominatorTail N w 1).coeff n = (EtaSupport.etaCoeff n : ℂ) := by
    rw [denominatorTail_one N w hw, Polynomial.coeff_map, Int.coe_castRingHom]
    congr 1
    rw [EtaSupport.etaCoeff, ← EtaSupport.etaTrunc_coeff_stable n N hn,
      ← EtaSupport.etaPoly_coe]
    simp
  have hv := ((((hasDerivAt_id (1 : ℂ)).sub_const 1).mul_const (w-1)).mul
    ((hasDerivAt_const (1 : ℂ) w).sub (hasDerivAt_id (1 : ℂ)))).mul hd
  simp only [denominatorPoly, Polynomial.coeff_C_mul]
  simpa [Pi.mul_def, sq, he, mul_assoc] using hv

/-- A single raw coefficient instance of the affine A₂ denominator identity
suffices. The hypothesis is before confluence and mentions neither primary
Eisenstein integers nor an eta product. -/
theorem etaCoeff_eq_primary_of_macdonald (w : ℂ) (hw : w^2+w+1=0) (n : ℕ)
    (h : ∀ s : ℂ, s ≠ 0 → (denominatorPoly n w s).coeff n =
      ∑ᶠ z : WeylFiber n, weylAlternant w s z.1.1 z.1.2) :
    (EtaSupport.etaCoeff n : ℂ) = primaryCoeff w n := by
  classical
  let := Fintype.ofFinite (WeylFiber n)
  have hR : HasDerivAt (fun s ↦ ∑ᶠ z : WeylFiber n, weylAlternant w s z.1.1 z.1.2)
      ((w-1)^2 * primaryCoeff w n) 1 := by
    rw [← weylCoeff_eq_primary w hw]
    simp_rw [finsum_eq_sum_of_fintype]
    exact HasDerivAt.fun_sum (fun i _ ↦ hasDerivAt_weylAlternant w hw i.1.1 i.1.2)
  have hL := hasDerivAt_denominatorCoeff w hw (le_refl n)
  have he : (fun s ↦ (denominatorPoly n w s).coeff n) =ᶠ[nhds (1 : ℂ)]
      (fun s ↦ ∑ᶠ z : WeylFiber n, weylAlternant w s z.1.1 z.1.2) := by
    filter_upwards [eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0)] with s hs
    exact h s hs
  have heq := (hL.congr_of_eventuallyEq he.symm).unique hR
  have hw1 : w-1 ≠ 0 := by intro hz; rw [sub_eq_zero.mp hz] at hw; norm_num at hw
  exact mul_left_cancel₀ (pow_ne_zero 2 hw1) heq

end

end BSD.CMTheta
