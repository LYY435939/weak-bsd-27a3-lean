import BSD.CoefficientsSplit
import BSD.CMThetaIdentity

/-! Divisibility by a conjugate pair in the lattice of primary Eisenstein integers. -/

namespace BSD.CMSplit

abbrev Pair := ℤ × ℤ
def mul (x y : Pair) : Pair :=
  (x.1*y.1-x.2*y.2, x.1*y.2+x.2*y.1-x.2*y.2)
def conj (x : Pair) : Pair := (x.1-x.2,-x.2)
def norm (x : Pair) : ℤ := x.1^2-x.1*x.2+x.2^2
def primary (x : Pair) : Prop := 3 ∣ x.1-1 ∧ 3 ∣ x.2
abbrev Fiber (n : ℤ) := {z : Pair // 3 ∣ z.1-1 ∧ 3 ∣ z.2 ∧ norm z=n}

instance (n : ℤ) : Finite (Fiber n) := inferInstanceAs (Finite (CMTheta.PrimaryFiber n))

def weight {R : Type*} [CommRing R] (w : R) (x : Pair) : R := (x.1:R)+(x.2:R)*w

theorem weight_mul {R : Type*} [CommRing R] (w : R) (hw : w^2+w+1=0) (x y : Pair) :
    weight w (mul x y) = weight w x * weight w y := by
  simp only [weight,mul,Int.cast_add,Int.cast_sub,Int.cast_mul]
  linear_combination -(x.2:R)*(y.2:R)*hw

private theorem mul_assoc (x y z : Pair) : mul (mul x y) z = mul x (mul y z) := by
  ext <;> simp [mul] <;> ring

private theorem mul_comm (x y : Pair) : mul x y = mul y x := by
  ext <;> simp [mul] <;> ring

private theorem norm_mul (x y : Pair) : norm (mul x y) = norm x * norm y := by
  simp [norm,mul]
  ring

private theorem norm_conj (x : Pair) : norm (conj x) = norm x := by
  simp [norm,conj]
  ring

private theorem conj_conj (x : Pair) : conj (conj x) = x := by
  ext <;> simp [conj]

private theorem conj_mul (x : Pair) : mul (conj x) x = (norm x, 0) := by
  ext <;> simp [mul,conj,norm] <;> ring

private theorem primary_iff (x : Pair) : primary x ↔ (x.1 : ZMod 3) = 1 ∧ (x.2 : ZMod 3) = 0 := by
  have ha := ZMod.intCast_zmod_eq_zero_iff_dvd (x.1-1) 3
  have hb := ZMod.intCast_zmod_eq_zero_iff_dvd x.2 3
  norm_num only [Int.cast_sub,Int.cast_one,Nat.cast_ofNat,sub_eq_zero] at ha hb
  exact and_congr ha.symm hb.symm

private theorem primary_mul_iff {x : Pair} (hx : primary x) (y : Pair) : primary (mul x y) ↔ primary y := by
  obtain ⟨ha,hb⟩ := (primary_iff _).mp hx
  rw [primary_iff,primary_iff]
  simp [mul,ha,hb]

def multFiber {m n : ℤ} (x : Fiber m) (y : Fiber n) : Fiber (m*n) := by
  have hp := (primary_mul_iff (show primary x.val from ⟨x.2.1,x.2.2.1⟩) y.val).mpr
    ⟨y.2.1,y.2.2.1⟩
  exact ⟨mul x y, hp.1, hp.2, by rw [norm_mul, x.2.2.2, y.2.2.2]⟩

def conjFiber {m : ℤ} (x : Fiber m) : Fiber m :=
  ⟨conj x, by obtain ⟨a,b⟩ := x; obtain ⟨ha,hb,hn⟩ := b; exact ⟨by dsimp [conj]; omega,
    by dsimp [conj]; omega, (norm_conj _).trans hn⟩⟩

theorem multFiber_injective {m n : ℤ} (x : Fiber m) (hm : m≠0) :
    Function.Injective (multFiber (n:=n) x) := by
  intro y z h
  have he := congrArg (fun t : Fiber (m*n) => mul (conj x) t.val) h
  change mul (conj x) (mul x y) = mul (conj x) (mul x z) at he
  rw [← mul_assoc, ← mul_assoc, conj_mul, x.2.2.2] at he
  apply Subtype.ext
  exact Prod.ext (mul_left_cancel₀ hm (by simpa [mul] using congrArg Prod.fst he))
    (mul_left_cancel₀ hm (by simpa [mul] using congrArg Prod.snd he))

/-- If the second coordinate of the formal quotient vanishes modulo p, the first does too.
Clearing the norm denominator recovers an integral element of the preceding primary fiber. -/
private theorem divide_of_snd {p : ℕ} [hp : Fact p.Prime] {n : ℤ}
    (x : Fiber (p:ℤ)) (v : Fiber ((p:ℤ)*n))
    (hd : ((mul (conj x) v).2 : ZMod p) = 0) :
    ∃ y : Fiber n, multFiber x y = v := by
  let t := mul (conj x) v
  have hn : norm t = (p:ℤ) * ((p:ℤ)*n) := by
    rw [norm_mul, norm_conj, x.2.2.2, v.2.2.2]
  have hr := congrArg (fun a : ℤ => (a : ZMod p)) hn
  change (t.2 : ZMod p) = 0 at hd
  have hfst : (t.1 : ZMod p) = 0 := by
    simpa [norm,hd] using hr
  obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd t.1 p).mp hfst
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd t.2 p).mp hd
  let q : Pair := (a,b)
  have hpz : (p:ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have he : t = mul ((p:ℤ),0) q := Prod.ext (by simpa [mul,q] using ha)
    (by simpa [mul,q] using hb)
  have hz : mul x q = v.val := by
    have hu := congrArg (mul x.val) he
    change mul x.val (mul (conj x.val) v.val) = _ at hu
    rw [← mul_assoc, mul_comm x.val (conj x.val), conj_mul, x.2.2.2] at hu
    rw [← mul_assoc x.val, mul_comm x.val ((p:ℤ),0), mul_assoc] at hu
    exact Prod.ext (mul_left_cancel₀ hpz (by simpa [mul] using (congrArg Prod.fst hu).symm))
      (mul_left_cancel₀ hpz (by simpa [mul] using (congrArg Prod.snd hu).symm))
  have hqn : norm q = n := by
    apply mul_left_cancel₀ hpz
    rw [← x.2.2.2, ← norm_mul, hz, x.2.2.2, v.2.2.2]
  have hqp := (primary_mul_iff (show primary x.val from ⟨x.2.1,x.2.2.1⟩) q).mp
    (hz ▸ (show primary v.val from ⟨v.2.1,v.2.2.1⟩))
  exact ⟨⟨q,hqp.1,hqp.2,hqn⟩, Subtype.ext hz⟩

theorem cover_any {p : ℕ} [Fact p.Prime] (x : Fiber (p:ℤ)) (n : ℤ) (v : Fiber ((p:ℤ)*n)) :
    (∃ y : Fiber n, multFiber x y = v) ∨ ∃ y : Fiber n, multFiber (conjFiber x) y = v := by
  have hN := congrArg (fun a:ℤ => (a:ZMod p)) v.2.2.2
  have hM := congrArg (fun a:ℤ => (a:ZMod p)) x.2.2.2
  simp only [norm, Int.cast_sub, Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_self, zero_mul] at hN hM
  have hd : ((mul (conj x) v).2 : ZMod p)*((mul (conj (conjFiber x).val) v).2 : ZMod p) = 0 := by
    change ((mul (conj x) v).2 : ZMod p)*((mul (conj (conj x)) v).2 : ZMod p) = 0
    rw [conj_conj]
    simp only [mul,conj,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_neg]
    linear_combination -(x.val.2:ZMod p)^2*hN + (v.val.2:ZMod p)^2*hM
  exact (mul_eq_zero.mp hd).imp (divide_of_snd x v) (divide_of_snd (conjFiber x) v)

theorem cover_fiber {p : ℕ} [Fact p.Prime] (z : Fiber (p:ℤ)) (n : ℤ)
    (v : Fiber ((p:ℤ)*((p:ℤ)*n))) :
    (∃ y : Fiber ((p:ℤ)*n), multFiber z y=v) ∨
      ∃ y : Fiber ((p:ℤ)*n), multFiber (conjFiber z) y=v :=
  cover_any z _ v

private theorem trace_nonzero_mod {p : ℕ} [hp : Fact p.Prime] (hs : p % 3=1) (x : Fiber (p:ℤ)) :
    ((2*x.val.1-x.val.2:ℤ) : ZMod p) ≠ 0 := by
  let T := 2*x.val.1-x.val.2
  have hdiv3 : 3 ∣ T - 2 := by
    have h1 := x.prop.1
    have h2 := x.prop.2.1
    dsimp [T]; omega
  have hN : T^2+3*x.val.2^2=4*(p:ℤ) := by
    have he := x.prop.2.2
    unfold norm at he
    dsimp [T]
    linear_combination 4*he
  have hp5 : 5 ≤ p := by
    have h2 := hp.out.two_le
    have h4 : p ≠ 4 := fun he => (by decide : ¬ Nat.Prime 4) (he ▸ hp.out)
    omega
  have hpz : (4:ℤ) < p := by exact_mod_cast hp5
  intro hz
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd T p).mp hz
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
  have hk1 : 1 ≤ k^2 := by nlinarith [sq_pos_of_ne_zero hk0]
  have hbound : (p:ℤ)^2 ≤ T^2 := by
    rw [hk, mul_pow]
    exact le_mul_of_one_le_right (sq_nonneg _) hk1
  nlinarith [sq_nonneg x.val.2, mul_pos (by omega : 0<(p:ℤ)) (sub_pos.mpr hpz)]

private theorem snd_zero_of_both {p : ℕ} [Fact p.Prime] (hs : p%3=1)
    (x : Fiber (p:ℤ)) {n : ℤ} (v : Fiber ((p:ℤ)*n)) (y z : Fiber n)
    (hy' : mul x.val y.val = v.val) (hz' : mul (conj x.val) z.val = v.val) :
    (v.val.2 : ZMod p) = 0 := by
  have h1 : ((mul (conj x.val) v.val).2 : ZMod p) = 0 := by
    rw [← hy', ← mul_assoc, conj_mul, x.2.2.2]
    simp [mul]
  have h2 : ((mul x.val v.val).2 : ZMod p) = 0 := by
    rw [← hz', ← mul_assoc, mul_comm x.val (conj x.val), conj_mul, x.2.2.2]
    simp [mul]
  have ht := trace_nonzero_mod hs x
  have hd : (v.val.2 : ZMod p) = 0 := by
    apply (mul_eq_zero.mp (show ((2*x.val.1-x.val.2:ℤ):ZMod p) * (v.val.2:ZMod p)=0 by
      simp only [mul,conj,Int.cast_sub,Int.cast_add,Int.cast_neg,Int.cast_mul,Int.cast_ofNat] at h1 h2 ⊢
      linear_combination h1+h2)).resolve_left ht
  exact hd

/-- If the rational prime does not divide n, the two images in norm p*n are disjoint. -/
theorem no_inter_fiber {p : ℕ} [hp : Fact p.Prime] (hs : p%3=1)
    (x : Fiber (p:ℤ)) (n : ℤ) (hn : ¬(p:ℤ)∣n) (v : Fiber ((p:ℤ)*n)) :
    ¬((∃ y : Fiber n, multFiber x y=v) ∧ (∃ y : Fiber n, multFiber (conjFiber x) y=v)) := by
  rintro ⟨⟨y,hy⟩,⟨z,hz⟩⟩
  have hd := snd_zero_of_both hs x v y z (congrArg Subtype.val hy) (congrArg Subtype.val hz)
  have he := congrArg (fun a : ℤ => (a:ZMod p)) v.2.2.2
  have hc : (v.val.1:ZMod p)=0 := by simpa [norm,hd] using he
  obtain ⟨a,ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd v.val.1 p).mp hc
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd v.val.2 p).mp hd
  apply hn
  refine ⟨norm (a,b), ?_⟩
  apply mul_left_cancel₀ (show (p:ℤ) ≠ 0 by exact_mod_cast hp.out.ne_zero)
  rw [← v.2.2.2]
  simp [norm,ha,hb]
  ring

/-- A point lies in both images precisely when it is divisible by the rational prime. -/
theorem inter_fiber {p : ℕ} [hp : Fact p.Prime] (hs : p % 3=1) (x : Fiber (p:ℤ))
    (n : ℤ) (v : Fiber ((p:ℤ)*((p:ℤ)*n))) :
    ((∃ y : Fiber ((p:ℤ)*n), multFiber x y = v) ∧
     (∃ y : Fiber ((p:ℤ)*n), multFiber (conjFiber x) y=v)) ↔
     ∃ t : Fiber n, multFiber x (multFiber (conjFiber x) t)=v := by
  constructor
  · rintro ⟨⟨y,hy⟩,⟨z,hz⟩⟩
    have hy' : mul x.val y.val = v.val := congrArg Subtype.val hy
    have hz' : mul (conj x.val) z.val = v.val := congrArg Subtype.val hz
    have hd := snd_zero_of_both hs x v y z hy' hz'
    obtain ⟨t,he⟩ := divide_of_snd (conjFiber x) y (by
      change ((mul (conj (conj x.val)) y.val).2 : ZMod p)=0
      simpa only [conj_conj,hy'] using hd)
    exact ⟨t,he ▸ hy⟩
  · rintro ⟨t,rfl⟩
    refine ⟨⟨_,rfl⟩,⟨multFiber x t,Subtype.ext ?_⟩⟩
    change mul (conj x.val) (mul x.val t.val) = mul x.val (mul (conj x.val) t.val)
    rw [← mul_assoc, ← mul_assoc, mul_comm (conj x.val) x.val]

end BSD.CMSplit
