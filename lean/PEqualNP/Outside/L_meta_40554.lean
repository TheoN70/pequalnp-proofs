import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40554

def pat (p : Bool × Bool) (n : ℕ) : Bool :=
  if n % 3 = 0 then p.1 else if n % 3 = 1 then p.2 else xor p.1 p.2

theorem pat_rel (p : Bool × Bool) (n : ℕ) :
    xor (pat p n) (xor (pat p (n+1)) (pat p (n+2))) = false := by
  obtain ⟨u, v⟩ := p
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h
  · have h1 : (n+1) % 3 = 1 := by omega
    have h2 : (n+2) % 3 = 2 := by omega
    cases u <;> cases v <;> simp [pat, h, h1, h2]
  · have h1 : (n+1) % 3 = 2 := by omega
    have h2 : (n+2) % 3 = 0 := by omega
    cases u <;> cases v <;> simp [pat, h, h1, h2]
  · have h1 : (n+1) % 3 = 0 := by omega
    have h2 : (n+2) % 3 = 1 := by omega
    cases u <;> cases v <;> simp [pat, h, h1, h2]

theorem pat_congr (p : Bool × Bool) {n n' : ℕ} (h : n % 3 = n' % 3) : pat p n = pat p n' := by
  simp only [pat, h]

def InK {G : Type*} [AddCommGroup G] (a : G) (z : G → Bool) : Prop :=
  ∀ i, xor (z (i - a)) (xor (z i) (z (i + a))) = false

theorem bstep : ∀ p q r s : Bool, xor p (xor q r) = false → xor q (xor r s) = false → s = p := by
  decide

theorem bnext : ∀ p q r p' q' r' : Bool, xor p (xor q r) = false → xor p' (xor q' r') = false →
    p = p' → q = q' → r = r' := by
  decide

theorem ker_trivial {G : Type*} [AddCommGroup G] [Finite G] (a : G) (h3 : ¬ 3 ∣ addOrderOf a)
    (z : G → Bool) (hz : InK a z) : ∀ i, z i = false := by
  have step : ∀ i, z (i + a + a) = z (i - a) := by
    intro i
    have h1 := hz i
    have h2 := hz (i + a)
    rw [add_sub_cancel_right] at h2
    exact bstep _ _ _ _ h1 h2
  have per3 : ∀ j, z (j + 3 • a) = z j := by
    intro j
    have h := step (j + a)
    rw [add_sub_cancel_right] at h
    have e : j + 3 • a = j + a + a + a := by abel
    rw [e, h]
  have pern : ∀ (n : ℕ) (j : G), z (j + n • (3 • a)) = z j := by
    intro n
    induction n with
    | zero => intro j; simp
    | succ n ih => intro j; rw [succ_nsmul, ← add_assoc, per3, ih]
  have hex : ∃ n : ℕ, n • (3 • a) = a := by
    have hm : 0 < addOrderOf a := addOrderOf_pos a
    by_cases h1 : addOrderOf a = 1
    · refine ⟨0, ?_⟩
      rw [AddMonoid.addOrderOf_eq_one_iff] at h1
      simp [h1]
    · have hlt : 1 < addOrderOf a := by omega
      have cop : Nat.Coprime 3 (addOrderOf a) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
      obtain ⟨n, -, hn⟩ := Nat.exists_mul_mod_eq_one_of_coprime cop hlt
      refine ⟨n, ?_⟩
      rw [← mul_nsmul', ← mod_addOrderOf_nsmul, mul_comm, hn, one_nsmul]
  obtain ⟨n, hn⟩ := hex
  have per : ∀ j, z (j + a) = z j := by
    intro j
    have := pern n j
    rwa [hn] at this
  intro i
  have h := hz i
  have e := per (i - a)
  rw [sub_add_cancel] at e
  rw [per i, ← e] at h
  revert h
  generalize z i = p
  revert p; decide

theorem ker_bij {G : Type*} [AddCommGroup G] [Finite G] (a : G) (h3 : 3 ∣ addOrderOf a) :
    Nat.card {z : G → Bool // InK a z} = 4 ^ (Nat.card G / addOrderOf a) := by
  classical
  let H := AddSubgroup.zmultiples a
  let r : G ⧸ H → G := fun q => q.out
  have hout : ∀ q : G ⧸ H, ((r q : G) : G ⧸ H) = q := fun q => QuotientAddGroup.out_eq' q
  have hex : ∀ j : G, ∃ n : ℕ, n • a = j - r (j : G ⧸ H) := by
    intro j
    have h := hout (j : G ⧸ H)
    rw [QuotientAddGroup.eq] at h
    rw [neg_add_eq_sub] at h
    have h' := (mem_multiples_iff_mem_zmultiples).2 h
    exact (AddSubmonoid.mem_multiples_iff _ _).1 h'
  have hqa : ∀ j : G, ((j + a : G) : G ⧸ H) = (j : G ⧸ H) := by
    intro j
    rw [QuotientAddGroup.eq]
    simp [H]
  have hmod : ∀ n n' : ℕ, n • a = n' • a → n % 3 = n' % 3 := by
    intro n n' h
    have := (nsmul_eq_nsmul_iff_modEq).1 h
    exact this.of_dvd h3
  let Φ : {z : G → Bool // InK a z} → (G ⧸ H → Bool × Bool) :=
    fun z q => (z.1 (r q), z.1 (r q + a))
  have hinj : Function.Injective Φ := by
    intro z z' hzz
    apply Subtype.ext
    funext j
    have key : ∀ (b : G) (n : ℕ), z.1 b = z'.1 b → z.1 (b + a) = z'.1 (b + a) →
        z.1 (b + n • a) = z'.1 (b + n • a) ∧ z.1 (b + n • a + a) = z'.1 (b + n • a + a) := by
      intro b n h0 h1
      induction n with
      | zero => simpa using ⟨h0, h1⟩
      | succ n ih =>
        have e : b + (n + 1) • a = b + n • a + a := by rw [succ_nsmul, add_assoc]
        rw [e]
        refine ⟨ih.2, ?_⟩
        have h2 := z.2 (b + n • a + a)
        have h3 := z'.2 (b + n • a + a)
        rw [add_sub_cancel_right] at h2 h3
        exact bnext _ _ _ _ _ _ h2 h3 ih.1 ih.2
    obtain ⟨n, hn⟩ := hex j
    have hq := congrFun hzz (j : G ⧸ H)
    simp only [Φ, Prod.mk.injEq] at hq
    have := (key (r (j : G ⧸ H)) n hq.1 hq.2).1
    rw [hn, add_sub_cancel] at this
    exact this
  have hsurj : Function.Surjective Φ := by
    intro w
    let z : G → Bool := fun j => pat (w (j : G ⧸ H)) (Classical.choose (hex j))
    have zval : ∀ (j : G) (n : ℕ), n • a = j - r (j : G ⧸ H) → z j = pat (w (j : G ⧸ H)) n := by
      intro j n hn
      apply pat_congr
      apply hmod
      rw [Classical.choose_spec (hex j), hn]
    have zval1 : ∀ (j : G) (n : ℕ), n • a = j - r (j : G ⧸ H) →
        z (j + a) = pat (w (j : G ⧸ H)) (n + 1) := by
      intro j n hn
      have := zval (j + a) (n + 1) (by rw [hqa, succ_nsmul, hn]; abel)
      rwa [hqa] at this
    have hz : InK a z := by
      intro i
      obtain ⟨n, hn⟩ := hex (i - a)
      have e0 := zval (i - a) n hn
      have e1 := zval1 (i - a) n hn
      have hn1 : (n + 1) • a = (i - a + a) - r ((i - a + a : G) : G ⧸ H) := by
        rw [hqa, succ_nsmul, hn]; abel
      have e2 := zval1 (i - a + a) (n + 1) hn1
      rw [hqa] at e2
      rw [sub_add_cancel] at e1 e2
      rw [e0, e1, e2]
      exact pat_rel _ n
    refine ⟨⟨z, hz⟩, ?_⟩
    funext q
    have h0 : (0 : ℕ) • a = r q - r ((r q : G) : G ⧸ H) := by rw [hout]; simp
    have e0 := zval (r q) 0 h0
    have e1 := zval1 (r q) 0 h0
    rw [hout] at e0 e1
    show (z (r q), z (r q + a)) = w q
    rw [e0, e1]
    simp [pat]
  rw [Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩), Nat.card_fun]
  have hc : Nat.card G = Nat.card (G ⧸ H) * addOrderOf a := by
    rw [← Nat.card_zmultiples a]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hm : 0 < addOrderOf a := addOrderOf_pos a
  rw [hc, Nat.mul_div_cancel _ hm]
  simp


section core
variable {R : Type*} [CommRing R]

def rot (a : R) (x : R → Bool) (i : R) : Bool := x (i - a)
def mix (d : R) (x : R → Bool) (i : R) : Bool := xor (x (i - d)) (xor (x i) (x (i + d)))
def chi (x : R → Bool) (i : R) : Bool := xor (x i) (!(x (i+1)) && x (i+2))
def V (d a f : R) (x : R → Bool) (b : Bool) (i : R) : Bool :=
  xor (chi (fun t => xor (mix d (rot a x) t) b) i) (rot f x i)
def sg (d a f : R) (x : R → Bool) (j : R) : Bool :=
  xor (x j) (!(xor (mix d (rot a x) (j+f+1)) (mix d (rot a x) (j+f+2))))
def Tt (d : R) (y : R → Bool) (s : R) : Bool := xor (y (s - 2*d)) (xor (y s) (y (s + 2*d)))

theorem V_eq (d a f : R) (x : R → Bool) (b : Bool) (i : R) : V d a f x b i =
    xor (xor (xor (mix d (rot a x) i) b)
      (!(xor (mix d (rot a x) (i+1)) b) && xor (mix d (rot a x) (i+2)) b)) (x (i - f)) := rfl

theorem bA : ∀ p0 p1 p2 fy q0 q1 q2 fx : Bool,
    xor (xor (xor p0 true) (!(xor p1 true) && xor p2 true)) fy =
      xor (xor (xor q0 true) (!(xor q1 true) && xor q2 true)) fx →
    xor (xor (xor p0 false) (!(xor p1 false) && xor p2 false)) fy =
      xor (xor (xor q0 false) (!(xor q1 false) && xor q2 false)) fx →
    xor p1 q1 = xor p2 q2 := by decide

theorem bB : ∀ A fy fx : Bool, xor A fy = xor A fx → fy = fx := by decide

theorem bC : ∀ q0 q1 q2 fy fx : Bool,
    xor (xor (xor (!q0) false) (!(xor (!q1) false) && xor (!q2) false)) fy =
      xor (xor (xor q0 false) (!(xor q1 false) && xor q2 false)) fx →
    fy = xor fx (!(xor q1 q2)) := by decide

theorem bD : ∀ q0 q1 q2 b fx : Bool,
    xor (xor (xor (!q0) b) (!(xor (!q1) b) && xor (!q2) b)) (xor fx (!(xor q1 q2))) =
      xor (xor (xor q0 b) (!(xor q1 b) && xor q2 b)) fx := by decide

theorem bxe : ∀ p q : Bool, xor p q = false → p = q := by decide
theorem bxn : ∀ p q : Bool, xor p q = true → p = !q := by decide

theorem fiber (hgen : ∀ c : R → Bool, (∀ i, c (i+1) = c i) → ∀ i, c i = c 0) (d a f : R)
    (x y : R → Bool) (h : V d a f y = V d a f x) :
    y = x ∨ (y = sg d a f x ∧ ∀ t, mix d (rot a y) t = !(mix d (rot a x) t)) := by
  have hv : ∀ b i, V d a f y b i = V d a f x b i := fun b i => by rw [h]
  simp only [V_eq] at hv
  have hc : ∀ t, xor (mix d (rot a y) (t+1)) (mix d (rot a x) (t+1)) =
      xor (mix d (rot a y) t) (mix d (rot a x) t) := by
    intro t
    have := bA _ _ _ _ _ _ _ _ (hv true (t-1)) (hv false (t-1))
    rw [show t - 1 + 2 = t + 1 by ring, show t - 1 + 1 = t by ring] at this
    exact this.symm
  have hconst : ∀ t, xor (mix d (rot a y) t) (mix d (rot a x) t) =
      xor (mix d (rot a y) 0) (mix d (rot a x) 0) :=
    hgen (fun t => xor (mix d (rot a y) t) (mix d (rot a x) t)) hc
  cases hc0 : xor (mix d (rot a y) 0) (mix d (rot a x) 0)
  · left
    have hM : ∀ t, mix d (rot a y) t = mix d (rot a x) t := by
      intro t; have := hconst t; rw [hc0] at this; exact bxe _ _ this
    funext j
    have := hv false (j + f)
    simp only [hM, add_sub_cancel_right] at this
    exact bB _ _ _ this
  · right
    have hM : ∀ t, mix d (rot a y) t = !(mix d (rot a x) t) := by
      intro t; have := hconst t; rw [hc0] at this; exact bxn _ _ this
    refine ⟨?_, hM⟩
    funext j
    have := hv false (j + f)
    simp only [hM, add_sub_cancel_right] at this
    exact bC _ _ _ _ _ this

theorem conv (d a f : R) (x : R → Bool)
    (hQ : ∀ t, mix d (rot a (sg d a f x)) t = !(mix d (rot a x) t)) :
    V d a f (sg d a f x) = V d a f x := by
  funext b i
  have e : sg d a f x (i - f) =
      xor (x (i - f)) (!(xor (mix d (rot a x) (i+1)) (mix d (rot a x) (i+2)))) := by
    show xor (x (i - f)) (!(xor (mix d (rot a x) (i - f + f + 1)) (mix d (rot a x) (i - f + f + 2)))) = _
    rw [sub_add_cancel]
  rw [V_eq, V_eq, hQ, hQ, hQ, e]
  exact bD _ _ _ _ _

theorem bmm : ∀ a1 a2 a3 a4 a5 : Bool,
    xor (xor a1 (xor a2 a3)) (xor (xor a2 (xor a3 a4)) (xor a3 (xor a4 a5))) =
      xor a1 (xor a3 a5) := by decide

theorem mixmix (d : R) (p : R → Bool) (s : R) : mix d (mix d p) s = Tt d p s := by
  show xor (xor (p (s-d-d)) (xor (p (s-d)) (p (s-d+d))))
    (xor (xor (p (s-d)) (xor (p s) (p (s+d)))) (xor (p (s+d-d)) (xor (p (s+d)) (p (s+d+d))))) =
    xor (p (s - 2*d)) (xor (p s) (p (s+2*d)))
  rw [show s-d-d = s-2*d by ring, sub_add_cancel, add_sub_cancel_right,
    show s+d+d = s+2*d by ring]
  exact bmm _ _ _ _ _

theorem b9 : ∀ y1 y2 y3 m1 m2 m3 n1 n2 n3 : Bool,
    xor (xor y1 (!(xor m1 n1))) (xor (xor y2 (!(xor m2 n2))) (xor y3 (!(xor m3 n3)))) =
      xor (xor y1 (xor y2 y3)) (!(xor (xor m1 (xor m2 m3)) (xor n1 (xor n2 n3)))) := by
  decide

theorem mix_lin (d : R) (Y M : R → Bool) (c1 c2 : R) (t : R) :
    mix d (fun j => xor (Y j) (!(xor (M (j + c1)) (M (j + c2))))) t =
      xor (mix d Y t) (!(xor (mix d M (t + c1)) (mix d M (t + c2)))) := by
  show xor (xor (Y (t-d)) (!(xor (M (t-d+c1)) (M (t-d+c2)))))
      (xor (xor (Y t) (!(xor (M (t+c1)) (M (t+c2)))))
        (xor (Y (t+d)) (!(xor (M (t+d+c1)) (M (t+d+c2)))))) =
    xor (xor (Y (t-d)) (xor (Y t) (Y (t+d))))
      (!(xor (xor (M (t+c1-d)) (xor (M (t+c1)) (M (t+c1+d))))
        (xor (M (t+c2-d)) (xor (M (t+c2)) (M (t+c2+d))))))
  rw [show t - d + c1 = t + c1 - d by ring, show t-d+c2 = t+c2-d by ring,
    show t+d+c1 = t+c1+d by ring, show t+d+c2 = t+c2+d by ring]
  exact b9 _ _ _ _ _ _ _ _ _

theorem sg_mix (d a f : R) (x : R → Bool) (t : R) :
    mix d (rot a (sg d a f x)) t = xor (mix d (rot a x) t)
      (!(xor (Tt d (rot a x) (t + (f+1-a))) (Tt d (rot a x) (t + (f+2-a))))) := by
  have h : rot a (sg d a f x) = fun j => xor (rot a x j)
      (!(xor (mix d (rot a x) (j + (f+1-a))) (mix d (rot a x) (j + (f+2-a))))) := by
    funext j
    show xor (x (j - a)) (!(xor (mix d (rot a x) (j - a + f + 1)) (mix d (rot a x) (j-a+f+2)))) =
      xor (x (j-a)) (!(xor (mix d (rot a x) (j + (f+1-a))) (mix d (rot a x) (j + (f+2-a)))))
    rw [show j - a + f + 1 = j + (f+1-a) by ring, show j - a + f + 2 = j + (f+2-a) by ring]
  rw [h, mix_lin d (rot a x) (mix d (rot a x)), mixmix, mixmix]

theorem bq1 : ∀ r A B : Bool, xor r (!(xor A B)) = !r → B = A := by decide
theorem bq2 : ∀ r A : Bool, xor r (!(xor A A)) = !r := by decide

theorem Q_iff (hgen : ∀ c : R → Bool, (∀ i, c (i+1) = c i) → ∀ i, c i = c 0) (d a f : R)
    (x : R → Bool) :
    (∀ t, mix d (rot a (sg d a f x)) t = !(mix d (rot a x) t)) ↔
      ((∀ s, Tt d (rot a x) s = false) ∨ (∀ s, Tt d (rot a x) s = true)) := by
  have h1 : (∀ t, mix d (rot a (sg d a f x)) t = !(mix d (rot a x) t)) ↔
      ∀ s, Tt d (rot a x) (s+1) = Tt d (rot a x) s := by
    constructor
    · intro h s
      have := h (s - (f+1-a))
      rw [sg_mix, show s - (f+1-a) + (f+1-a) = s by ring,
        show s - (f+1-a) + (f+2-a) = s+1 by ring] at this
      exact bq1 _ _ _ this
    · intro h t
      rw [sg_mix, show t + (f+2-a) = t + (f+1-a) + 1 by ring, h]
      exact bq2 _ _
  rw [h1]
  constructor
  · intro h
    have hc := hgen _ h
    cases h0 : Tt d (rot a x) 0
    · left; intro s; rw [hc s, h0]
    · right; intro s; rw [hc s, h0]
  · rintro (h | h) s <;> rw [h, h]

variable [Fintype R] [DecidableEq R]

def fib (d a f : R) (x : R → Bool) : Finset (R → Bool) :=
  Finset.univ.filter (fun y => V d a f y = V d a f x)

theorem mem_fib (d a f : R) (x y : R → Bool) : y ∈ fib d a f x ↔ V d a f y = V d a f x := by
  simp [fib]

theorem fib_le (hgen : ∀ c : R → Bool, (∀ i, c (i+1) = c i) → ∀ i, c i = c 0) (d a f : R)
    (x : R → Bool) : (fib d a f x).card ≤ 2 := by
  have hsub : fib d a f x ⊆ {x, sg d a f x} := by
    intro y hy
    have hy' : V d a f y = V d a f x := (Finset.mem_filter.1 hy).2
    rcases fiber hgen d a f x y hy' with h | h
    · simp [h]
    · simp [h.1]
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem fib_two_iff (hgen : ∀ c : R → Bool, (∀ i, c (i+1) = c i) → ∀ i, c i = c 0) (d a f : R)
    (x : R → Bool) : (fib d a f x).card = 2 ↔
      ∀ t, mix d (rot a (sg d a f x)) t = !(mix d (rot a x) t) := by
  constructor
  · intro h
    obtain ⟨y, hy, hne⟩ := Finset.exists_mem_ne (by omega : 1 < (fib d a f x).card) x
    have hy' : V d a f y = V d a f x := (Finset.mem_filter.1 hy).2
    rcases fiber hgen d a f x y hy' with h | h
    · exact absurd h hne
    · rw [← h.1]; exact h.2
  · intro hQ
    apply le_antisymm (fib_le hgen d a f x)
    have hne : x ≠ sg d a f x := by
      intro he
      have := hQ 0
      rw [← he] at this
      revert this
      generalize mix d (rot a x) 0 = p
      revert p; decide
    rw [← Finset.card_pair hne]
    apply Finset.card_le_card
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · simp [fib]
    · simp [fib, conv d a f x hQ]

theorem card_filter_eq {α β : Type*} [Fintype α] (e : α ≃ β) (p : α → Prop) (q : β → Prop)
    [DecidablePred p] (h : ∀ x, p x ↔ q (e x)) :
    (Finset.univ.filter p).card = Nat.card {z // q z} := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (e.subtypeEquiv h)

def rotE (a : R) : (R → Bool) ≃ (R → Bool) where
  toFun := rot a
  invFun := fun x i => x (i + a)
  left_inv := by intro x; funext i; simp [rot]
  right_inv := by intro x; funext i; simp [rot]

def notE : (R → Bool) ≃ (R → Bool) where
  toFun := fun x i => !(x i)
  invFun := fun x i => !(x i)
  left_inv := by intro x; funext i; simp
  right_inv := by intro x; funext i; simp

theorem bn3 : ∀ p q r : Bool, xor p (xor q r) = true ↔ xor (!p) (xor (!q) (!r)) = false := by
  decide

theorem card_two (hgen : ∀ c : R → Bool, (∀ i, c (i+1) = c i) → ∀ i, c i = c 0) (d a f : R) :
    (Finset.univ.filter (fun x => (fib d a f x).card = 2)).card =
      2 * Nat.card {z : R → Bool // InK (2*d) z} := by
  have hf : Finset.univ.filter (fun x => (fib d a f x).card = 2) =
      Finset.univ.filter (fun x : R → Bool => ∀ s, Tt d (rot a x) s = false) ∪
      Finset.univ.filter (fun x : R → Bool => ∀ s, Tt d (rot a x) s = true) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro x _
    rw [fib_two_iff hgen, Q_iff hgen]
  have hd : Disjoint (Finset.univ.filter (fun x : R → Bool => ∀ s, Tt d (rot a x) s = false))
      (Finset.univ.filter (fun x : R → Bool => ∀ s, Tt d (rot a x) s = true)) := by
    rw [Finset.disjoint_filter]
    intro x _ h0 h1
    have := (h0 0).symm.trans (h1 0)
    exact Bool.false_ne_true this
  rw [hf, Finset.card_union_of_disjoint hd,
    card_filter_eq (rotE a) (fun x : R → Bool => ∀ s, Tt d (rot a x) s = false)
      (fun z => InK (2*d) z) (fun x => Iff.rfl),
    card_filter_eq ((rotE a).trans notE) (fun x : R → Bool => ∀ s, Tt d (rot a x) s = true)
      (fun z => InK (2*d) z) (fun x => forall_congr' (fun s => bn3 _ _ _))]
  ring

theorem image_card (hgen : ∀ c : R → Bool, (∀ i, c (i+1) = c i) → ∀ i, c i = c 0) (d a f : R) :
    2 * (Finset.univ.image (V d a f)).card +
      (Finset.univ.filter (fun x => (fib d a f x).card = 2)).card =
      2 * Fintype.card (R → Bool) := by
  have h1 := Finset.card_eq_sum_card_image (V d a f) Finset.univ
  have h2 := Finset.card_eq_sum_card_fiberwise
    (f := V d a f) (s := Finset.univ.filter (fun x => (fib d a f x).card = 2))
    (t := Finset.univ.image (V d a f)) (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))
  have hp : ∀ v ∈ Finset.univ.image (V d a f),
      ((Finset.univ.filter (fun x => (fib d a f x).card = 2)).filter
        (fun y => V d a f y = v)).card + 2 =
      2 * (Finset.univ.filter (fun y => V d a f y = v)).card := by
    intro v hv
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hv
    have hx : x ∈ fib d a f x := by simp [fib]
    have hpos : 0 < (fib d a f x).card := Finset.card_pos.2 ⟨x, hx⟩
    have hle := fib_le hgen d a f x
    have hsame : ∀ y, V d a f y = V d a f x → fib d a f y = fib d a f x := by
      intro y hy; unfold fib; rw [hy]
    by_cases h : (fib d a f x).card = 2
    · have : (Finset.univ.filter (fun x => (fib d a f x).card = 2)).filter
          (fun y => V d a f y = V d a f x) = fib d a f x := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [mem_fib]
        constructor
        · exact fun hy => hy.2
        · intro hy
          refine ⟨?_, hy⟩
          rw [hsame y hy]; exact h
      rw [this]
      show (fib d a f x).card + 2 = 2 * (fib d a f x).card
      omega
    · have : (Finset.univ.filter (fun x => (fib d a f x).card = 2)).filter
          (fun y => V d a f y = V d a f x) = ∅ := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨hy2, hy⟩
        rw [hsame y hy] at hy2
        exact h hy2
      rw [this]
      show (∅ : Finset (R → Bool)).card + 2 = 2 * (fib d a f x).card
      rw [Finset.card_empty]
      omega
  rw [Finset.card_univ] at h1
  rw [h1, Finset.mul_sum, ← Finset.sum_congr rfl hp, Finset.sum_add_distrib, ← h2,
    Finset.sum_const, smul_eq_mul]
  ring

theorem core (hgen : ∀ c : R → Bool, (∀ i, c (i+1) = c i) → ∀ i, c i = c 0) (d a f : R) :
    (∀ x, (fib d a f x).card ≤ 2) ∧
    (Finset.univ.filter (fun x => (fib d a f x).card = 2)).card =
      2 * Nat.card {z : R → Bool // InK (2*d) z} ∧
    (Finset.univ.image (V d a f)).card + Nat.card {z : R → Bool // InK (2*d) z} =
      2 ^ Fintype.card R := by
  refine ⟨fib_le hgen d a f, card_two hgen d a f, ?_⟩
  have h := image_card hgen d a f
  rw [card_two hgen d a f, Fintype.card_fun, Fintype.card_bool] at h
  omega

end core

theorem ker_count {G : Type*} [AddCommGroup G] [Finite G] (a : G) :
    Nat.card {z : G → Bool // InK a z} =
      if 3 ∣ addOrderOf a then 4 ^ (Nat.card G / addOrderOf a) else 1 := by
  split_ifs with h3
  · exact ker_bij a h3
  · have : Unique {z : G → Bool // InK a z} :=
      ⟨⟨⟨fun _ => false, fun i => rfl⟩⟩,
        fun z => Subtype.ext (funext (ker_trivial a h3 z.1 z.2))⟩
    exact Nat.card_unique


theorem hgen_z (m : ℕ) (c : ZMod (m+1) → Bool) (h : ∀ i, c (i+1) = c i) :
    ∀ i, c i = c 0 := by
  have hn : ∀ n : ℕ, c (n : ZMod (m+1)) = c 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, h, ih]
  intro i
  have := hn (ZMod.val i)
  rwa [ZMod.natCast_zmod_val] at this

theorem ix_plus (m : ℕ) (i : ZMod (m+1)) (n : ℕ) (h : (ZMod.val i + n) % (m+1) < m+1) :
    @Eq (ZMod (m+1)) (⟨(ZMod.val i + n) % (m+1), h⟩ : Fin (m+1)) (i + (n : ZMod (m+1))) := by
  have key : ∀ j : ZMod (m+1), ZMod.val j = (ZMod.val i + n) % (m+1) →
      j = i + (n : ZMod (m+1)) := by
    intro j hj
    apply ZMod.val_injective
    rw [ZMod.val_add, ZMod.val_natCast, hj]
    exact (Nat.add_mod_mod _ _ _).symm
  exact key _ rfl

theorem ix_minus (m : ℕ) (i : ZMod (m+1)) (a : ℕ)
    (h : (ZMod.val i + (m+1) - a % (m+1)) % (m+1) < m+1) :
    @Eq (ZMod (m+1)) (⟨(ZMod.val i + (m+1) - a % (m+1)) % (m+1), h⟩ : Fin (m+1))
      (i - (a : ZMod (m+1))) := by
  have key2 : ((ZMod.val i + (m+1) - a % (m+1)) % (m+1) + a % (m+1)) % (m+1) = ZMod.val i := by
    have h1 : a % (m+1) < m+1 := Nat.mod_lt a (Nat.succ_pos m)
    have h2 : ZMod.val i < m+1 := ZMod.val_lt i
    rw [Nat.mod_add_mod]
    have h3 : ZMod.val i + (m+1) - a % (m+1) + a % (m+1) = ZMod.val i + (m+1) := by omega
    rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt h2]
  have key : ∀ j : ZMod (m+1), ZMod.val j = (ZMod.val i + (m+1) - a % (m+1)) % (m+1) →
      j = i - (a : ZMod (m+1)) := by
    intro j hj
    rw [eq_sub_iff_add_eq]
    apply ZMod.val_injective
    rw [ZMod.val_add, ZMod.val_natCast, hj]
    exact key2
  exact key _ rfl

theorem ker_z (m : ℕ) (d : ℕ) :
    Nat.card {z : ZMod (m+1) → Bool // InK (2 * (d : ZMod (m+1))) z} =
      2 ^ (if 3 ∣ (m+1) / Nat.gcd (m+1) (2*d) then 2 * Nat.gcd (m+1) (2*d) else 0) := by
  have h2d : (2 * (d : ZMod (m+1))) = ((2*d : ℕ) : ZMod (m+1)) := by push_cast; rfl
  rw [ker_count, h2d, ZMod.addOrderOf_coe _ (Nat.succ_ne_zero m), Nat.card_zmod]
  split_ifs with h
  · rw [Nat.div_div_self (Nat.gcd_dvd_left _ _) (Nat.succ_ne_zero m), pow_mul]
    norm_num
  · rfl

end PEqualNP.Outside.L_meta_40554

theorem PEqualNP.Outside.L_meta_40554 : ∀ (k : Nat) (hk : 0 < k) (d ini fin : Nat),
  let W := Fin k → Bool
  let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (a : Nat) (x : W) (i : Fin k) => x (ix (i.val+k-a % k))
  let mix := fun (gap : Nat) (x : W) (i : Fin k) =>
    xor (x (ix (i.val+k-gap % k))) (xor (x i) (x (ix (i.val+gap))))
  let chi := fun (x : W) (i : Fin k) =>
    xor (x i) (!(x (ix (i.val+1))) && x (ix (i.val+2)))
  let view := fun (x : W) (b : Bool) (i : Fin k) =>
    xor (chi (fun t => xor (mix d (rot ini x) t) b) i) (rot fin x i)
  let keys : Finset W := Finset.univ
  let paired := fun x : W => (keys.filter (fun y => view y = view x)).card
  let g := Nat.gcd k (2*d)
  let e := if 3 ∣ k/g then 2*g else 0
  (∀ x, paired x ≤ 2) ∧
  (keys.filter (fun x => paired x = 2)).card = 2 * 2^e ∧
  (keys.image view).card + 2^e = 2^k := by
  intro k hk d ini fin
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero hk.ne'
  intro W ix rot mix chi view keys paired g e
  have hadd : ∀ (i : Fin (m+1)) (n : ℕ),
      ix (i.val + n) = @HAdd.hAdd (ZMod (m+1)) (ZMod (m+1)) (ZMod (m+1)) _ i (n : ZMod (m+1)) :=
    fun i n => PEqualNP.Outside.L_meta_40554.ix_plus m i n _
  have hsub : ∀ (i : Fin (m+1)) (a : ℕ), ix (i.val + (m+1) - a % (m+1)) =
      @HSub.hSub (ZMod (m+1)) (ZMod (m+1)) (ZMod (m+1)) _ i (a : ZMod (m+1)) :=
    fun i a => PEqualNP.Outside.L_meta_40554.ix_minus m i a _
  have hview : view = PEqualNP.Outside.L_meta_40554.V (R := ZMod (m+1))
      (d : ZMod (m+1)) (ini : ZMod (m+1)) (fin : ZMod (m+1)) := by
    funext x b i
    simp only [view, chi, mix, rot, hadd, hsub, Nat.cast_one, Nat.cast_ofNat]
    rfl
  obtain ⟨c1, c2, c3⟩ := PEqualNP.Outside.L_meta_40554.core
    (PEqualNP.Outside.L_meta_40554.hgen_z m) (d : ZMod (m+1)) (ini : ZMod (m+1)) (fin : ZMod (m+1))
  have hN : Nat.card {z : ZMod (m+1) → Bool //
      PEqualNP.Outside.L_meta_40554.InK (2 * (d : ZMod (m+1))) z} = 2 ^ e :=
    PEqualNP.Outside.L_meta_40554.ker_z m d
  refine ⟨?_, ?_, ?_⟩
  · intro x
    show (Finset.filter (fun y => view y = view x) Finset.univ).card ≤ 2
    rw [hview]
    exact c1 x
  · show (Finset.filter (fun x => (Finset.filter (fun y => view y = view x) Finset.univ).card = 2)
      Finset.univ).card = 2 * 2 ^ e
    rw [hview, ← hN]
    exact c2
  · show (Finset.image view Finset.univ).card + 2 ^ e = 2 ^ (m+1)
    rw [hview, ← hN]
    have h3 := c3
    rwa [ZMod.card] at h3
