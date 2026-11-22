import BSD.CoefficientsCoprimeStep
import BSD.CoefficientsInertTheta
import BSD.CoefficientsSplitRecurrence
import BSD.PrimeRecurrence

/-! # The CM theta coefficients are the actual Hasse–Weil coefficients

This comparison concerns all natural indices. The raw Weyl denominator
formula appears only in the separate theorem connecting the eta product.
-/

namespace BSD.FermatCubic

open CMTheta

private theorem split_of_ne_three_not_inert (p : Nat.Primes) (h₃ : (p : ℕ) ≠ 3)
    (hi : (p : ℕ) % 3 ≠ 2) : (p : ℕ) % 3 = 1 := by
  have hnd : ¬ 3 ∣ (p : ℕ) := by
    intro hd
    rcases (Nat.dvd_prime p.2).1 hd with h | h
    · norm_num at h
    · exact h₃ h.symm
  omega

private theorem primaryCoeff_split_eq_trace {R : Type*} [CommRing R] (w : R)
    (p : Nat.Primes) (hs : (p : ℕ) % 3 = 1) :
    primaryCoeff w (p : ℕ) = (primeTrace p : R) := by
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨a,b,ha,hb,hn,ht⟩ := split_trace_primary_representation hs
  have h₃ : (p : ℕ) ≠ 3 := by omega
  have hi : (p : ℕ) % 3 ≠ 2 := by omega
  rw [primaryCoeff_split_prime w hs, ht, primeTrace, if_neg (not_or.mpr ⟨h₃,hi⟩),
    primaryTrace_eq p.2 hn ha hb]

/-- At every natural index, the primary lattice gives precisely the coefficient
defined by the Euler factors of the actual elliptic curve. -/
theorem primaryCoeff_eq_LFunction {R : Type*} [CommRing R] (w : R) (hw : w^2+w+1 = 0)
    (n : ℕ) : primaryCoeff w n = (curve.LFunction n : R) := by
  let f : ArithmeticFunction R := (curve.LFunction : ArithmeticFunction ℤ)
  let T (m : ℕ) : R := primaryCoeff w m
  apply eq_of_prime_recurrences f (weierstrass_LFunction_isMultiplicative curve).intCast
    T (fun p ↦ (primeTrace p : R)) (fun p ↦ (primeDet p : R)) _ _ _ _ _ _ n
  · intro p
    exact congrArg (fun a : ℤ ↦ (a : R)) (prime_recurrence p).1
  · intro p k
    simpa only [f, ArithmeticFunction.intCoe_apply, Int.cast_sub, Int.cast_mul] using
      congrArg (fun a : ℤ ↦ (a : R)) ((prime_recurrence p).2 k)
  · exact primaryThetaCoeff_ramified_zero w (by simp : (3 : ℤ) ∣ 0)
  · exact primaryThetaCoeff_one w
  · intro p m hm
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    have hm' : ¬ (p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hm
    simp only [T, Nat.cast_mul]
    by_cases h₃ : (p : ℕ) = 3
    · have hd : (3 : ℤ) ∣ (p : ℤ) * m := by rw [h₃]; exact dvd_mul_right _ _
      rw [show primaryCoeff w ((p : ℤ) * m) = 0 from primaryThetaCoeff_ramified_zero w hd]
      simp [primeTrace, h₃]
    by_cases hi : (p : ℕ) % 3 = 2
    · have h₂ : ¬ (p : ℤ)^2 ∣ (p : ℤ)*m := by
        rw [sq, mul_dvd_mul_iff_left (by exact_mod_cast p.2.ne_zero : (p : ℤ) ≠ 0)]
        exact hm'
      have hz : primaryCoeff w ((p : ℤ)*m) = 0 :=
        primaryThetaCoeff_inert_zero_of_dvd_of_not_dvd_sq w hi (dvd_mul_right _ _) h₂
      simpa [primeTrace, hi] using hz
    have hs := split_of_ne_three_not_inert p h₃ hi
    rw [primaryCoeff_split_mul_coprime w hw hs m hm', primaryCoeff_split_eq_trace w p hs]
  · intro p m
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    simp only [T, Nat.cast_mul]
    by_cases h₃ : (p : ℕ) = 3
    · have hd : (3 : ℤ) ∣ (p : ℤ)*((p : ℤ)*m) := by rw [h₃]; exact dvd_mul_right _ _
      rw [show primaryCoeff w ((p : ℤ)*((p : ℤ)*m)) = 0 from primaryThetaCoeff_ramified_zero w hd]
      simp [primeTrace, primeDet, h₃]
    by_cases hi : (p : ℕ) % 3 = 2
    · have hz : primaryCoeff w ((p : ℤ)^2*m) = -(p : R) * primaryCoeff w m :=
        primaryThetaCoeff_inert_mul_sq w hi (m : ℤ)
      rw [← mul_assoc, ← sq, hz]
      simp [primeTrace, primeDet, hi, h₃]
    have hs := split_of_ne_three_not_inert p h₃ hi
    rw [primaryCoeff_split_recurrence w hw hs, primaryCoeff_split_eq_trace w p hs]
    simp [primeDet, h₃]

/-- The affine A₂ denominator identity, before differentiation, suffices for
the rank part of BSD on the Fermat cubic. -/
theorem rankPart_of_macdonald (w : ℂ) (hw : w^2+w+1 = 0)
    (h : ∀ (n : ℕ) (s : ℂ), s ≠ 0 → (denominatorPoly n w s).coeff n =
      ∑ᶠ z : WeylFiber n, weylAlternant w s z.1.1 z.1.2) : RankPart curve := by
  apply rankPart_of_coefficient_identity
  intro n
  exact_mod_cast (primaryCoeff_eq_LFunction w hw n).symm.trans
    (etaCoeff_eq_primary_of_macdonald w hw n (h n)).symm

end BSD.FermatCubic
