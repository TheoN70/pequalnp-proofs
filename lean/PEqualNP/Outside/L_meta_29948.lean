import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29948
open PEqualNP.CircuitLowerBounds

namespace Quadratic29947Pair

private def orient (z : ℤ) : ℤ := if 0 ≤ z then 1 else -1

private theorem orient_mul (z : ℤ) : orient z * z = |z| := by
  by_cases h : 0 ≤ z
  · simp [orient,h,abs_of_nonneg h]
  · have neg := le_of_lt (lt_of_not_ge h)
    simp [orient,h,abs_of_nonpos neg]

private theorem oriented_bit (a z : ℤ) (ha : a = 1 ∨ a = -1) :
    orient z * a ≤ 1 := by
  rcases ha with rfl | rfl <;> unfold orient <;> split <;> norm_num

private theorem scale_le_abs (a b z : ℤ) : orient a * orient b * z ≤ |z| := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b <;>
    simp [orient,ha,hb,le_abs_self,neg_le_abs]

theorem paired_sum {X : Type*} [Fintype X] (f g : X → ℤ)
    (hf : ∀ x, f x = 1 ∨ f x = -1) (hg : ∀ x, g x = 1 ∨ g x = -1) :
    |∑ x, f x| + |∑ x, g x| ≤ (Fintype.card X : ℤ) + |∑ x, f x * g x| := by
  let a : ℤ := ∑ x, f x
  let b : ℤ := ∑ x, g x
  calc
    _ = orient a * a + orient b * b := by rw [orient_mul,orient_mul]
    _ = ∑ x, (orient a * f x + orient b * g x) := by
      simp only [a,b,Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ ∑ x, (1 + (orient a * orient b) * (f x * g x)) := by
      apply Finset.sum_le_sum
      intro x _
      have off : 0 ≤ (1 - orient a * f x) * (1 - orient b * g x) :=
        mul_nonneg (sub_nonneg.mpr (oriented_bit _ _ (hf x)))
          (sub_nonneg.mpr (oriented_bit _ _ (hg x)))
      nlinarith only [off]
    _ = (Fintype.card X : ℤ) + (orient a * orient b) * ∑ x, f x * g x := by
      simp [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := add_le_add_right (scale_le_abs _ _ _) _

end Quadratic29947Pair

namespace Quadratic29947Walsh

def character (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

theorem character_add (x y : ZMod 2) :
    character (x + y) = character x * character y := by
  have all : ∀ a b : ZMod 2, character (a + b) = character a * character b := by decide
  exact all x y

theorem character_bound (x : ZMod 2) : character x ≤ 1 := by
  unfold character
  split <;> decide

theorem sum_twist {A : Type*} [AddCommGroup A] [Fintype A] (f : A → ℤ) (h : A) :
    (∑ x, f (x + h)) = ∑ x, f x := by
  apply Fintype.sum_equiv (Equiv.addRight h)
  intro x
  rfl

theorem hom_sum {A : Type*} [AddCommGroup A] [Fintype A] (l : A →+ ZMod 2) :
    (∑ x, character (l x)) = if l = 0 then (Fintype.card A : ℤ) else 0 := by
  classical
  by_cases zero : l = 0
  · simp [zero,character]
  · obtain ⟨t, nonzero⟩ : ∃ t, l t ≠ 0 := by
      by_contra! h
      apply zero
      ext t
      exact h t
    have either : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    have one := (either (l t)).resolve_left nonzero
    have equiv := sum_twist (fun x => character (l x)) t
    simp only [l.map_add, character_add, one, show character 1 = -1 by decide,
      ← Finset.sum_mul] at equiv
    rw [if_neg zero]
    linarith

private theorem rearrange (a b c d e : ZMod 2) (h : a + b + c + d = e) :
    a + b = c + d + e := by
  have all : ∀ a b c d e : ZMod 2, a + b + c + d = e → a + b = c + d + e := by decide
  exact all a b c d e h

theorem square_identity {A : Type*} [AddCommGroup A] [Fintype A]
    (q : A → ZMod 2) (polar : A → A →+ ZMod 2)
    (hpolar : ∀ x h, q (x + h) + q x + q h + q 0 = polar h x) :
    (∑ x, character (q x)) ^ 2 =
      (Fintype.card A : ℤ) * ∑ h : A, if polar h = 0 then character (q h + q 0) else 0 := by
  classical
  rw [pow_two]
  calc
    _ = ∑ x : A, ∑ y : A, character (q x) * character (q y) := by
      simp only [Finset.sum_mul,Finset.mul_sum,mul_comm]
    _ = ∑ x : A, ∑ h : A, character (q x) * character (q (h + x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (sum_twist (fun y => character (q x) * character (q y)) x).symm
    _ = ∑ h : A, ∑ x : A, character (q h + q 0) * character (polar h x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro x _
      rw [← character_add, ← character_add, add_comm h x, add_comm (q x)]
      rw [rearrange _ _ _ _ _ (hpolar x h)]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      rw [← Finset.mul_sum,hom_sum]
      split <;> ring

theorem square_bound {A : Type*} [AddCommGroup A] [Fintype A]
    (q : A → ZMod 2) (polar : A → A →+ ZMod 2)
    (hpolar : ∀ x h, q (x + h) + q x + q h + q 0 = polar h x) :
    (∑ x, character (q x)) ^ 2 ≤
      (Fintype.card A : ℤ) * (Fintype.card {h : A // polar h = 0} : ℤ) := by
  classical
  rw [square_identity _ _ hpolar]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ h : A, if polar h = 0 then (1 : ℤ) else 0 := by
      apply Finset.sum_le_sum
      intro h _
      split <;> simp_all [character_bound]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast (Fintype.card_of_subtype (Finset.univ.filter fun h : A => polar h = 0)
        (fun h => by simp)).symm

theorem scaled_bound {A : Type*} [AddCommGroup A] [Fintype A]
    (q : A → ZMod 2) (polar : A → A →+ ZMod 2) (e : ℕ)
    (hpolar : ∀ x h, q (x + h) + q x + q h + q 0 = polar h x)
    (capacity : (Fintype.card {h : A // polar h = 0} : ℤ) * 2 ^ (2 * e) ≤ Fintype.card A) :
    2 ^ e * |∑ x, character (q x)| ≤ (Fintype.card A : ℤ) := by
  have power : ((2 : ℤ) ^ e) ^ 2 = 2 ^ (2 * e) := by rw [← pow_mul,Nat.mul_comm e 2]
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow,power,sq_abs]
  calc
    _ ≤ 2 ^ (2 * e) * ((Fintype.card A : ℤ) * Fintype.card {h : A // polar h = 0}) :=
      mul_le_mul_of_nonneg_left (square_bound q polar hpolar) (by positivity)
    _ = (Fintype.card A : ℤ) * ((Fintype.card {h : A // polar h = 0} : ℤ) * 2 ^ (2 * e)) := by ring
    _ ≤ _ := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left capacity (by positivity)

abbrev Inputs (n : ℕ) := Fin n → ZMod 2

theorem matrix_capacity (n e : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (polar : Inputs n → Inputs n →+ ZMod 2)
    (entry : ∀ h x, polar h x = dotProduct x (M.mulVec h))
    (rank : 2 * e ≤ M.rank) :
    (Fintype.card {h : Inputs n // polar h = 0} : ℤ) * 2 ^ (2 * e) ≤
      Fintype.card (Inputs n) := by
  classical
  have same (h : Inputs n) : polar h = 0 ↔ h ∈ LinearMap.ker M.mulVecLin := by
    rw [LinearMap.mem_ker]
    change polar h = 0 ↔ M.mulVec h = 0
    constructor
    · intro off
      funext i
      have atSingle : polar h (Pi.single i 1) = 0 := by simp [off]
      rw [entry, single_one_dotProduct] at atSingle
      exact atSingle
    · intro off
      ext x
      simp [entry,off]
  let identification : {h : Inputs n // polar h = 0} ≃ LinearMap.ker M.mulVecLin :=
    { toFun := fun x => ⟨x,(same x).mp x.property⟩
      invFun := fun x => ⟨x,(same x).mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have dim := M.mulVecLin.finrank_range_add_finrank_ker
  change M.rank + Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) =
      Module.finrank (ZMod 2) (Inputs n) at dim
  have room : Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) + 2 * e ≤
      Module.finrank (ZMod 2) (Inputs n) := by omega
  have cardinal : Fintype.card {h : Inputs n // polar h = 0} =
      Fintype.card (LinearMap.ker M.mulVecLin) := Fintype.card_congr identification
  rw [cardinal, Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker M.mulVecLin),
      Module.card_eq_pow_finrank (K := ZMod 2) (V := Inputs n), ZMod.card]
  push_cast
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) room

end Quadratic29947Walsh

namespace Quadratic29947Polar
abbrev F := ZMod 2

variable {V : Type*} [AddCommGroup V] [Module F V]

def polar (q : V → F) (x y : V) : F :=
  q (x + y) + q x + q y + q 0

theorem add_polar (f g : V → F) (x y : V) :
    polar (fun v => f v + g v) x y = polar f x y + polar g x y := by
  unfold polar
  ring

theorem sum_polar {I : Type*} (s : Finset I) (f : I → V → F) (x y : V) :
    polar (fun v => ∑ i ∈ s, f i v) x y = ∑ i ∈ s, polar (f i) x y := by
  simp only [polar, Finset.sum_add_distrib]

theorem affine_polar (L : V →ₗ[F] F) (b : F) (x y : V) :
    polar (fun v => b + L v) x y = 0 := by
  have all : ∀ b a c : F, (b + (a + c)) + (b + a) + (b + c) + (b + 0) = 0 := by decide
  simpa only [polar,map_add,map_zero] using all b (L x) (L y)

theorem product_polar (L P : V →ₗ[F] F) (b c : F) (x y : V) :
    polar (fun v => (b + L v) * (c + P v)) x y = L x * P y + L y * P x := by
  have all : ∀ b c l₁ l₂ p₁ p₂ : F,
      (b + (l₁ + l₂)) * (c + (p₁ + p₂)) + (b + l₁) * (c + p₁) +
        (b + l₂) * (c + p₂) + (b + 0) * (c + 0) = l₁ * p₂ + l₂ * p₁ := by decide
  simpa only [polar,map_add,map_zero] using all b c (L x) (L y) (P x) (P y)

theorem translated_form {I : Type*} (s : Finset I) (L P : I → V →ₗ[F] F)
    (aff : V →ₗ[F] F) (constant : F) (shift x y : V) :
    polar (fun v => constant + aff (shift + v) + ∑ i ∈ s, L i (shift + v) * P i (shift + v)) x y =
      ∑ i ∈ s, (L i x * P i y + L i y * P i x) := by
  rw [add_polar,sum_polar]
  have a : polar (fun v => constant + aff (shift + v)) x y = 0 := by
    simpa only [map_add, ← add_assoc] using affine_polar aff (constant + aff shift) x y
  rw [a, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [map_add] using product_polar (L i) (P i) (L i shift) (P i shift) x y

theorem common_polar {I : Type*} (s : Finset I) (L P : I → V →ₗ[F] F)
    (b c : Bool → I → F) (A : Bool → V → F)
    (aff : ∀ t, ∃ (k : F) (T : V →ₗ[F] F), ∀ v, A t v = k + T v)
    (x y : V) :
    polar (fun v => A false v + ∑ i ∈ s, (b false i + L i v) * (c false i + P i v)) x y =
      polar (fun v => A true v + ∑ i ∈ s, (b true i + L i v) * (c true i + P i v)) x y := by
  have none (t : Bool) : polar (A t) x y = 0 := by
    obtain ⟨k,T,h⟩ := aff t
    rw [funext h]
    exact affine_polar T k x y
  rw [add_polar,add_polar,none,none,zero_add,zero_add,sum_polar,sum_polar]
  simp only [product_polar]

end Quadratic29947Polar

namespace Quadratic29947Restriction
open Quadratic29947Walsh

theorem rank_restrict (n m : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Matrix (Fin n) (Fin m) (ZMod 2)) (independent : P.rank = m) :
    M.rank ≤ (P.transpose * M * P).rank + 2 * (n - m) := by
  have left := Matrix.rank_mul_ge P.transpose M
  have right := Matrix.rank_mul_ge (P.transpose * M) P
  have width := Matrix.rank_le_card_height P
  simp only [Matrix.rank_transpose,independent,Fintype.card_fin] at left right width
  omega

theorem rank_restrict_ge (n m r c : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Matrix (Fin n) (Fin m) (ZMod 2)) (independent : P.rank = m)
    (rank : M.rank = 2 * r) (codimension : n - m ≤ c) :
    2 * (r - c) ≤ (P.transpose * M * P).rank := by
  have bound := rank_restrict n m M P independent
  omega

theorem one_leaf (n r c m : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Matrix (Fin n) (Fin m) (ZMod 2)) (independent : P.rank = m)
    (rank : M.rank = 2 * r) (codimension : n - m ≤ c)
    (f g : Inputs m → ZMod 2) (polar : Inputs m → Inputs m →+ ZMod 2)
    (entries : ∀ h x, polar h x = dotProduct x ((P.transpose * M * P).mulVec h))
    (hpolar : ∀ x h, (f (x+h) + g (x+h)) + (f x + g x) +
      (f h + g h) + (f 0 + g 0) = polar h x) :
    2 ^ (r - c) * (|∑ x, character (f x)| + |∑ x, character (g x)|) ≤
      (2 ^ (r - c) + 1) * (Fintype.card (Inputs m) : ℤ) := by
  have restrictRank := rank_restrict_ge n m r c M P independent rank codimension
  have square := scaled_bound (fun x => f x + g x) polar (r - c) hpolar
    (matrix_capacity m (r - c) (P.transpose * M * P) polar entries restrictRank)
  have sign (a : ZMod 2) : character a = 1 ∨ character a = -1 := by
    unfold character
    split <;> simp
  have pair := Quadratic29947Pair.paired_sum (fun x => character (f x))
    (fun x => character (g x)) (fun x => sign _) (fun x => sign _)
  simp only [← character_add] at pair
  calc
    _ ≤ 2 ^ (r - c) * ((Fintype.card (Inputs m) : ℤ) + |∑ x, character (f x + g x)|) :=
      mul_le_mul_of_nonneg_left pair (by positivity)
    _ = 2 ^ (r - c) * (Fintype.card (Inputs m) : ℤ) + 2 ^ (r - c) * |∑ x, character (f x + g x)| := by ring
    _ ≤ _ := by rw [add_mul, one_mul]; gcongr

theorem combine_leaves {I : Type*} [Fintype I] (a b mass : I → ℤ) (e n : ℕ)
    (covers : (∑ i, mass i) = 2 ^ n)
    (leaf : ∀ i, 2 ^ e * (|a i| + |b i|) ≤ (2 ^ e + 1) * mass i) :
    2 ^ e * (|∑ i, a i| + |∑ i, b i|) ≤ (2 ^ e + 1) * 2 ^ n := by
  calc
    _ ≤ 2 ^ e * ((∑ i, |a i|) + (∑ i, |b i|)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i, 2 ^ e * (|a i| + |b i|) := by
      simp only [Finset.mul_sum,mul_add,Finset.sum_add_distrib]
    _ ≤ ∑ i, (2 ^ e + 1) * mass i := Finset.sum_le_sum fun i _ => leaf i
    _ = _ := by rw [← Finset.mul_sum,covers]

end Quadratic29947Restriction

namespace Quadratic29947Transport
open Quadratic29947Polar Quadratic29947Walsh Quadratic29947Restriction

theorem compose_polar {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] (q : W → ZMod 2) (L : V →ₗ[ZMod 2] W)
    (x y : V) : polar (fun v => q (L v)) x y = polar q (L x) (L y) := by
  simp [polar,map_add,map_zero]

theorem matrix_pullback (n m : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Matrix (Fin n) (Fin m) (ZMod 2)) (x y : Inputs m) :
    dotProduct x ((P.transpose * M * P).mulVec y) =
      dotProduct (P.mulVec x) (M.mulVec (P.mulVec y)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

def asAdd (m : ℕ) (M : Matrix (Fin m) (Fin m) (ZMod 2)) (y : Inputs m) :
    Inputs m →+ ZMod 2 where
  toFun x := dotProduct x (M.mulVec y)
  map_zero' := by simp
  map_add' _ _ := add_dotProduct _ _ _

theorem transported_leaf (n r c m : ℕ)
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (P : Matrix (Fin n) (Fin m) (ZMod 2))
    (independent : P.rank = m) (rank : M.rank = 2 * r) (codimension : n - m ≤ c)
    (Q : Bool → Inputs n → ZMod 2) (origin : Bool → Inputs n)
    (approx : Bool → Inputs m → ZMod 2)
    (shift : ∀ t x y, polar (fun u => Q t (origin t + u)) x y = polar (Q t) x y)
    (common : ∀ x y, polar (approx false) x y = polar (approx true) x y)
    (entries : ∀ x y, polar (fun v => Q false v + Q true v) x y = dotProduct x (M.mulVec y)) :
    let err := fun t u => Q t (origin t + P.mulVec u) + approx t u
    2 ^ (r - c) * (|∑ x, character (err false x)| + |∑ x, character (err true x)|) ≤
      (2 ^ (r - c) + 1) * (Fintype.card (Inputs m) : ℤ) := by
  dsimp only
  let err := fun t u => Q t (origin t + P.mulVec u) + approx t u
  apply one_leaf n r c m M P independent rank codimension (err false) (err true)
    (asAdd m (P.transpose * M * P)) (fun _ _ => rfl)
  intro x y
  change polar (fun u => err false u + err true u) x y =
    dotProduct x ((P.transpose * M * P).mulVec y)
  rw [add_polar]
  unfold err
  rw [add_polar,add_polar]
  have trans (t : Bool) :
      polar (fun u => Q t (origin t + P.mulVec u)) x y =
        polar (Q t) (P.mulVec x) (P.mulVec y) := by
    exact (compose_polar (fun u => Q t (origin t + u)) P.mulVecLin x y).trans
      (shift t _ _)
  rw [trans false,trans true, ← common, matrix_pullback, ← entries, add_polar]
  have cancel : ∀ a b d : ZMod 2, a + d + (b + d) = a + b := by decide
  apply cancel

end Quadratic29947Transport

namespace Quadratic29947Split

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

def split (L : V →ₗ[F] F) (u : V) (unit : L u = 1) (offset : F) :
    V ≃ F × LinearMap.ker L where
  toFun x := (offset + L x, ⟨x - L x • u, by simp [LinearMap.mem_ker,unit]⟩)
  invFun pair := pair.2.val + (pair.1 - offset) • u
  left_inv x := by
    simp only [add_sub_cancel_left,sub_add_cancel]
  right_inv := by
    rintro ⟨s,z⟩
    have off : L z.val = 0 := z.property
    have eval : L (z.val + (s - offset) • u) = s - offset := by
      simp [off,unit]
    apply Prod.ext
    · change offset + L (z.val + (s - offset) • u) = s
      rw [eval,add_sub_cancel]
    · apply Subtype.ext
      change z.val + (s - offset) • u - L (z.val + (s - offset) • u) • u = z.val
      rw [eval,add_sub_cancel_right]

theorem fixed (L : V →ₗ[F] F) (u : V) (unit : L u = 1) (offset desired : F)
    (z : LinearMap.ker L) : offset + L ((split L u unit offset).symm (desired,z)) = desired := by
  exact congrArg Prod.fst ((split L u unit offset).apply_symm_apply (desired,z))

theorem restricted_form (L P : V →ₗ[F] F) (u : V) (unit : L u = 1)
    (before shift desired : F) (z : LinearMap.ker L) :
    before + P ((split L u unit shift).symm (desired,z)) =
      (before + (desired - shift) * P u) + (P.comp (LinearMap.ker L).subtype) z := by
  change before + P (z.val + (desired - shift) • u) =
    (before + (desired - shift) * P u) + P z.val
  rw [map_add,map_smul]
  simp only [smul_eq_mul]
  abel

end Quadratic29947Split

namespace Quadratic29947Coordinates
open Quadratic29947Walsh
abbrev F := ZMod 2

noncomputable def kernelBasis {m : ℕ} (L : Inputs m →ₗ[F] F) :
    Inputs (Module.finrank F (LinearMap.ker L)) ≃ₗ[F] LinearMap.ker L :=
  (Module.finBasis F (LinearMap.ker L)).equivFun.symm

theorem one_dimension {m : ℕ} (L : Inputs m →ₗ[F] F) (u : Inputs m) (unit : L u = 1) :
    Module.finrank F (LinearMap.ker L) + 1 = m := by
  have surj : Function.Surjective L := by
    intro a
    exact ⟨a • u, by simp [unit]⟩
  have rank := L.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surj,finrank_top,Module.finrank_self] at rank
  simpa [Nat.add_comm] using rank

noncomputable def coordinates {m : ℕ} (L : Inputs m →ₗ[F] F) (u : Inputs m)
    (unit : L u = 1) (offset : F) :
    Inputs m ≃ F × Inputs (Module.finrank F (LinearMap.ker L)) :=
  (Quadratic29947Split.split L u unit offset).trans
    (Equiv.prodCongr (Equiv.refl F) (kernelBasis L).symm.toEquiv)

theorem coordinates_inverse {m : ℕ} (L : Inputs m →ₗ[F] F) (u : Inputs m)
    (unit : L u = 1) (offset a : F) (z : Inputs (Module.finrank F (LinearMap.ker L))) :
    (coordinates L u unit offset).symm (a,z) = (kernelBasis L z).val + (a - offset) • u := rfl

theorem sum_over_children {m : ℕ} (L : Inputs m →ₗ[F] F) (u : Inputs m)
    (unit : L u = 1) (offset : F) (g : Inputs m → ℤ) :
    (∑ x, g x) = ∑ a : F, ∑ z : Inputs (Module.finrank F (LinearMap.ker L)),
      g ((kernelBasis L z).val + (a - offset) • u) := by
  let equiv := coordinates L u unit offset
  have sum := Fintype.sum_equiv equiv g (fun pair => g (equiv.symm pair))
    (fun x => by rw [equiv.symm_apply_apply])
  rw [Fintype.sum_prod_type] at sum
  simpa only [equiv,coordinates_inverse] using sum

end Quadratic29947Coordinates

namespace Quadratic29947Affine
open PEqualNP.CircuitLowerBounds

abbrev F := ZMod 2

variable {V : Type*} [AddCommGroup V] [Module F V]

def paired (f : Bool → V → F) : Prop :=
  ∃ (offset : Bool → F) (linear : V →ₗ[F] F), ∀ t x, f t x = offset t + linear x

theorem constant (f : Bool → F) : paired (fun t (_ : V) => f t) :=
  ⟨f,0,by simp⟩

theorem plus {f g : Bool → V → F} (hf : paired f) (hg : paired g) :
    paired (fun t x => f t x + g t x) := by
  obtain ⟨bf,Lf,af⟩ := hf
  obtain ⟨bg,Lg,ag⟩ := hg
  refine ⟨fun t => bf t + bg t,Lf+Lg,?_⟩
  intro t x
  change f t x + g t x = bf t + bg t + (Lf + Lg) x
  rw [af,ag,LinearMap.add_apply]
  abel

theorem scale (a : F) {f : Bool → V → F} (hf : paired f) :
    paired (fun t x => a * f t x) := by
  obtain ⟨b,L,h⟩ := hf
  refine ⟨fun t => a * b t,a • L,?_⟩
  intro t x
  change a * f t x = a * b t + (a • L) x
  rw [h,LinearMap.smul_apply,smul_eq_mul,mul_add]

theorem affine_along_split
    (L : V →ₗ[F] F) (u : V) (unit : L u = 1) (b : Bool → F) (a : F)
    {f : Bool → V → F} (hf : paired f) :
    paired (fun t z => f t ((Quadratic29947Split.split L u unit (b t)).symm (a,z))) := by
  obtain ⟨start,P,expr⟩ := hf
  refine ⟨fun t => start t + (a - b t) * P u,P.comp (LinearMap.ker L).subtype,?_⟩
  intro t z
  change f t ((Quadratic29947Split.split L u unit (b t)).symm (a,z)) =
    start t + (a - b t) * P u + (P.comp (LinearMap.ker L).subtype) z
  rw [expr]
  exact Quadratic29947Split.restricted_form L P u unit _ _ _ _

theorem fixed_along_split
    (L : V →ₗ[F] F) (u : V) (unit : L u = 1) (b : Bool → F) (a : F) :
    ∀ t z, b t + L ((Quadratic29947Split.split L u unit (b t)).symm (a,z)) = a :=
  fun t z => Quadratic29947Split.fixed L u unit (b t) a z

def both (f g : Bool → V → F) : Prop :=
  paired (fun t x => f t x * g t x) ∧
    paired (fun t x => f t x + g t x + f t x * g t x)

private theorem nonzero_value (L : V →ₗ[F] F) (nonzero : L ≠ 0) : ∃ u, L u = 1 := by
  obtain ⟨u,hu⟩ : ∃ u, L u ≠ 0 := by
    by_contra! h
    apply nonzero
    ext u
    exact h u
  have values : ∀ a : F, a = 0 ∨ a = 1 := by decide
  exact ⟨u,(values (L u)).resolve_left hu⟩

private theorem split_product (L : V →ₗ[F] F) (u : V) (unit : L u = 1) (b : Bool → F)
    (f g : Bool → V → F) (form : ∀ t x, f t x = b t + L x)
    (hg : paired g) (a : F) :
    both
      (fun t z => f t ((Quadratic29947Split.split L u unit (b t)).symm (a,z)))
      (fun t z => g t ((Quadratic29947Split.split L u unit (b t)).symm (a,z))) := by
  let onLeaf := fun t z => ((Quadratic29947Split.split L u unit (b t)).symm (a,z))
  have first : (fun t z => f t (onLeaf t z)) = fun (_ : Bool) (_ : LinearMap.ker L) => a := by
    funext t z
    exact (form t _).trans (fixed_along_split L u unit b a t z)
  have second : paired (fun t z => g t (onLeaf t z)) := affine_along_split L u unit b a hg
  change both (fun t z => f t (onLeaf t z)) (fun t z => g t (onLeaf t z))
  rw [first]
  exact ⟨scale a second,plus (plus (constant fun _ => a) second) (scale a second)⟩

private theorem both_comm (f g : Bool → V → F) : both f g ↔ both g f := by
  unfold both
  simp only [mul_comm,add_comm (f _ _) (g _ _)]

theorem binary_step (f g : Bool → V → F) (hf : paired f) (hg : paired g) :
    both f g ∨ ∃ (L : V →ₗ[F] F) (u : V) (unit : L u = 1) (b : Bool → F),
      ∀ a : F, both
        (fun t z => f t ((Quadratic29947Split.split L u unit (b t)).symm (a,z)))
        (fun t z => g t ((Quadratic29947Split.split L u unit (b t)).symm (a,z))) := by
  obtain ⟨bf,Lf,fa⟩ := hf
  obtain ⟨bg,Lg,ga⟩ := hg
  by_cases lf : Lf = 0
  · by_cases lg : Lg = 0
    · left
      have ef : f = fun t (_ : V) => bf t := by
        funext t x
        simp [fa,lf]
      have eg : g = fun t (_ : V) => bg t := by
        funext t x
        simp [ga,lg]
      rw [ef,eg]
      exact ⟨constant fun t => bf t * bg t, constant fun t => bf t + bg t + bf t * bg t⟩
    · obtain ⟨u,hu⟩ := nonzero_value Lg lg
      exact Or.inr ⟨Lg,u,hu,bg,fun a => (both_comm _ _).mp
        (split_product Lg u hu bg g f ga ⟨bf,Lf,fa⟩ a)⟩
  · obtain ⟨u,hu⟩ := nonzero_value Lf lf
    exact Or.inr ⟨Lf,u,hu,bf,split_product Lf u hu bf f g fa ⟨bg,Lg,ga⟩⟩

def scalar (b : Bool) : F := if b then 1 else 0

theorem two_gate_laws :
    (∀ a b, scalar (GateOp.eval .and [a,b]) = scalar a * scalar b) ∧
    (∀ a b, scalar (GateOp.eval .or [a,b]) =
      scalar a + scalar b + scalar a * scalar b) ∧
    (∀ a b, scalar (GateOp.eval (.mod 2) [a,b]) = 1 + scalar a + scalar b) ∧
    (∀ a, scalar (GateOp.eval .not [a]) = 1 + scalar a) ∧
    (∀ a, scalar (GateOp.eval (.mod 2) [a]) = 1 + scalar a) := by decide

end Quadratic29947Affine

namespace Quadratic29947Chart
open Quadratic29947Walsh Quadratic29947Coordinates

structure Chart (n : ℕ) where
  dim : ℕ
  origin : Bool → Inputs n
  move : Inputs dim →ₗ[ZMod 2] Inputs n
  independent : Function.Injective move

def point {n : ℕ} (C : Chart n) (t : Bool) (x : Inputs C.dim) : Inputs n :=
  C.origin t + C.move x

def initial (n : ℕ) : Chart n :=
  ⟨n,fun _ => 0,LinearMap.id,fun _ _ h => h⟩

theorem initial_point (n : ℕ) (t : Bool) (x : Inputs n) : point (initial n) t x = x := by
  change 0 + x = x
  exact zero_add _

noncomputable def matrix {n : ℕ} (C : Chart n) : Matrix (Fin n) (Fin C.dim) (ZMod 2) :=
  LinearMap.toMatrix' C.move

theorem matrix_point {n : ℕ} (C : Chart n) (x : Inputs C.dim) :
    (matrix C).mulVec x = C.move x :=
  LinearMap.toMatrix'_mulVec _ _

theorem matrix_rank {n : ℕ} (C : Chart n) : (matrix C).rank = C.dim := by
  have same : (matrix C).mulVecLin = C.move :=
    LinearMap.ext fun x => matrix_point C x
  rw [Matrix.rank,same,LinearMap.finrank_range_of_inj C.independent]
  simp

noncomputable def child {n : ℕ} (C : Chart n) (L : Inputs C.dim →ₗ[ZMod 2] ZMod 2)
    (u : Inputs C.dim) (b : Bool → ZMod 2) (a : ZMod 2) : Chart n where
  dim := Module.finrank (ZMod 2) (LinearMap.ker L)
  origin t := C.origin t + C.move ((a - b t) • u)
  move := C.move.comp ((LinearMap.ker L).subtype.comp (kernelBasis L).toLinearMap)
  independent := C.independent.comp (Subtype.val_injective.comp (kernelBasis L).injective)

theorem child_point {n : ℕ} (C : Chart n) (L : Inputs C.dim →ₗ[ZMod 2] ZMod 2)
    (u : Inputs C.dim) (unit : L u = 1) (b : Bool → ZMod 2) (a : ZMod 2) (t : Bool)
    (z : Inputs (child C L u b a).dim) :
    point (child C L u b a) t z = point C t ((coordinates L u unit (b t)).symm (a,z)) := by
  change (C.origin t + C.move ((a - b t) • u)) + C.move (kernelBasis L z).val =
    C.origin t + C.move ((kernelBasis L z).val + (a - b t) • u)
  rw [map_add]
  abel

theorem child_dimension {n : ℕ} (C : Chart n) (L : Inputs C.dim →ₗ[ZMod 2] ZMod 2)
    (u : Inputs C.dim) (unit : L u = 1) (b : Bool → ZMod 2) (a : ZMod 2) :
    (child C L u b a).dim + 1 = C.dim :=
  one_dimension L u unit

theorem child_sum {n : ℕ} (C : Chart n) (L : Inputs C.dim →ₗ[ZMod 2] ZMod 2)
    (u : Inputs C.dim) (unit : L u = 1) (b : Bool → ZMod 2) (t : Bool) (f : Inputs n → ℤ) :
    (∑ x, f (point C t x)) =
      ∑ a : ZMod 2, ∑ z, f (point (child C L u b a) t z) := by
  refine (sum_over_children L u unit (b t) (fun x => f (point C t x))).trans ?_
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro z _
  exact congrArg f (child_point C L u unit b a t z).symm

theorem child_affine {n : ℕ} (C : Chart n) (L : Inputs C.dim →ₗ[ZMod 2] ZMod 2)
    (u : Inputs C.dim) (unit : L u = 1) (b : Bool → ZMod 2) (a : ZMod 2) (f : Bool → Inputs n → ZMod 2)
    (form : Quadratic29947Affine.paired (fun t x => f t (point C t x))) :
    Quadratic29947Affine.paired (fun t z => f t (point (child C L u b a) t z)) := by
  have same := Quadratic29947Affine.affine_along_split L u unit b a form
  obtain ⟨q,Z,eq⟩ := same
  refine ⟨q,Z.comp (kernelBasis L).toLinearMap,?_⟩
  intro t z
  change f t (point (child C L u b a) t z) = q t + Z (kernelBasis L z)
  rw [child_point C L u unit b a t z]
  exact eq t (kernelBasis L z)

end Quadratic29947Chart

namespace Quadratic29947Literal
open Quadratic29947Polar Quadratic29947Walsh

def quad {n : ℕ} (q : Inputs n → ZMod 2) : Prop :=
  ∃ (b : ZMod 2) (a : Inputs n) (M : Fin n → Fin n → ZMod 2), ∀ v,
    q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j

def dotLinear {n : ℕ} (a : Inputs n) : Inputs n →ₗ[ZMod 2] ZMod 2 where
  toFun v := dotProduct a v
  map_add' _ _ := dotProduct_add _ _ _
  map_smul' _ _ := dotProduct_smul _ _ _

theorem shift_invariant {n : ℕ} (q : Inputs n → ZMod 2) (h : quad q)
    (a x y : Inputs n) : polar (fun u => q (a + u)) x y = polar q x y := by
  obtain ⟨c,b,M,rep⟩ := h
  let L : Fin n × Fin n → Inputs n →ₗ[ZMod 2] ZMod 2 :=
    fun ij => M ij.1 ij.2 • LinearMap.proj ij.1
  let P : Fin n × Fin n → Inputs n →ₗ[ZMod 2] ZMod 2 := fun ij => LinearMap.proj ij.2
  have decomp : q = fun v => c + dotLinear b v + ∑ i : Fin n × Fin n, L i v * P i v := by
    funext v
    rw [Fintype.sum_prod_type,rep]
    rfl
  rw [decomp]
  have trans := translated_form Finset.univ L P (dotLinear b) c a x y
  have zero := translated_form Finset.univ L P (dotLinear b) c 0 x y
  simpa only [zero_add] using trans.trans zero.symm

theorem equality_character : ∀ a b : ZMod 2,
    (if a = b then (1 : ℤ) else -1) = character (a + b) := by decide

end Quadratic29947Literal

namespace Quadratic29947NormalForm
open Quadratic29947Polar

theorem twice : ∀ a : F, a + a = 0 := by decide
private theorem field_values : ∀ a : F, a = 0 ∨ a = 1 := by decide

variable {V : Type*} [AddCommGroup V] [Module F V]

def zeroPolarLinear (q : V → F) (zeroPolar : ∀ x y, polar q x y = 0) : V →ₗ[F] F where
  toFun x := q x + q 0
  map_add' x y := by
    have relation := zeroPolar x y
    have all : ∀ a b c d : F, a+b+c+d = 0 → a+d = (b+d)+(c+d) := by decide
    exact all _ _ _ _ relation
  map_smul' a x := by
    rcases field_values a with rfl | rfl
    · simp [twice]
    · simp

theorem affine_of_zero_polar (q : V → F) (zeroPolar : ∀ x y, polar q x y = 0) :
    ∃ (a : F) (L : V →ₗ[F] F), ∀ x, q x = a + L x := by
  refine ⟨q 0,zeroPolarLinear q zeroPolar,fun x => ?_⟩
  change q x = q 0 + (q x + q 0)
  rw [add_comm (q x) (q 0), ← add_assoc, twice, zero_add]

theorem split_quadratic {r : ℕ} (q : V → F) (L P : Fin r → V →ₗ[F] F)
    (decomp : ∀ x y, polar q x y = ∑ i, (L i x * P i y + L i y * P i x)) :
    ∃ (b : F) (A : V →ₗ[F] F), ∀ x, q x = b + A x + ∑ i, L i x * P i x := by
  let products := fun x => ∑ i, L i x * P i x
  have productForm (x y : V) :
      polar products x y = ∑ i, (L i x * P i y + L i y * P i x) := by
    change polar (fun z => ∑ i, L i z * P i z) x y = _
    rw [sum_polar]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [zero_add] using product_polar (L i) (P i) 0 0 x y
  have off (x y : V) : polar (fun v => q v + products v) x y = 0 := by
    rw [add_polar,decomp,productForm,twice]
  obtain ⟨a,A,affine⟩ := affine_of_zero_polar _ off
  refine ⟨a,A,?_⟩
  intro x
  have after : q x + products x = a + A x := affine x
  rw [← after,add_assoc,twice,add_zero]

end Quadratic29947NormalForm

namespace Quadratic29947ExactBias
open Quadratic29947Walsh
abbrev F := ZMod 2

theorem character_sum {I : Type*} (s : Finset I) (f : I → F) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [character]
  | insert a rest fresh ih =>
    rw [Finset.sum_insert fresh,Finset.prod_insert fresh,character_add,ih]

theorem one_pair : (∑ q : F × F, character (q.1 * q.2)) = 2 := by decide

theorem pair_atoms (j : ℕ) :
    (∑ z : Fin j → F × F, character (∑ i, (z i).1 * (z i).2)) = 2 ^ j := by
  simp only [character_sum]
  rw [← Fintype.sum_pow (fun q : F × F => character (q.1 * q.2))]
  rw [one_pair]

theorem exact_bias {A : Type*} [Fintype A] (j k : ℕ) (q : A → F)
    (coords : A ≃ (Fin j → F × F) × (Fin k → F))
    (form : ∀ x, q x = ∑ i, ((coords x).1 i).1 * ((coords x).1 i).2) :
    (2 : ℤ)^j * (∑ x, character (q x)) = 2 ^ (2 * j + k) := by
  have decomposition :
      (∑ x, character (q x)) =
        ∑ z : (Fin j → F × F) × (Fin k → F),
          character (∑ i, (z.1 i).1 * (z.1 i).2) :=
    Fintype.sum_equiv coords _ _ (fun x => congrArg character (form x))
  rw [decomposition,Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum,pair_atoms]
  simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ = (2 : ℤ)^j * 2^j * 2^k := by ring
    _ = (2 : ℤ)^(j + j + k) := by rw [pow_add,pow_add]
    _ = _ := by congr 1 <;> omega

theorem subset_bias {A : Type*} [Fintype A] (r k : ℕ) (S : Finset (Fin r)) (q : A → F)
    (coords : A ≃ (Fin r → F × F) × (Fin k → F))
    (form : ∀ x, q x = ∑ i ∈ S, ((coords x).1 i).1 * ((coords x).1 i).2) :
    (2 : ℤ)^S.card * (∑ x, character (q x)) = 2 ^ (2*r + k) := by
  classical
  let w (i : Fin r) (z : F × F) : ℤ := if i ∈ S then character (z.1 * z.2) else 1
  let a (i : Fin r) : ℤ := if i ∈ S then 2 else 1
  have count : (∏ i, a i) = (2 : ℤ)^S.card := by
    unfold a
    rw [Finset.prod_ite_mem_eq,Finset.prod_const]
  have term (z : Fin r → F × F) : character (∑ i ∈ S, (z i).1 * (z i).2) = ∏ i, w i (z i) := by
    rw [character_sum]
    unfold w
    rw [Finset.prod_ite_mem_eq]
  have product : (∏ i, a i * ∑ z, w i z) = (4 : ℤ)^r := by
    have pointwise (i : Fin r) : a i * (∑ z, w i z) = 4 := by
      by_cases h : i ∈ S
      · simp [a,w,h,one_pair]
      · simp [a,w,h,Fintype.card_prod,ZMod.card]
    simp only [pointwise,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have selected : (2 : ℤ)^S.card * (∑ z : Fin r → F × F, ∏ i, w i (z i)) = 4^r := by
    rw [← count, ← Fintype.prod_sum w, ← Finset.prod_mul_distrib]
    exact product
  have all : (∑ x, character (q x)) =
      ∑ p : (Fin r → F × F) × (Fin k → F), ∏ i, w i (p.1 i) := by
    apply Fintype.sum_equiv coords
    intro x
    rw [form,term]
  rw [all,Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
  have free : (Fintype.card (Fin k → F) : ℤ) = 2^k := by
    simp [Fintype.card_fun,ZMod.card]
  rw [free]
  calc
    _ = (2 : ℤ)^k * ((2 : ℤ)^S.card * (∑ z : Fin r → F × F, ∏ i, w i (z i))) := by ring
    _ = (2 : ℤ)^(2*r+k) := by rw [selected,pow_add,pow_mul]; norm_num [mul_comm]

end Quadratic29947ExactBias

namespace Quadratic29947Fiber
open Quadratic29947Walsh
abbrev F := ZMod 2

def bundle {n r : ℕ} (L R : Fin r → Inputs n →ₗ[F] F) : Inputs n →ₗ[F] (Fin r → F × F) where
  toFun x i := (L i x,R i x)
  map_add' x y := by
    funext i
    exact Prod.ext (map_add (L i) x y) (map_add (R i) x y)
  map_smul' a x := by
    funext i
    exact Prod.ext (map_smul (L i) a x) (map_smul (R i) a x)

theorem bundle_surjective {n r : ℕ} (L R : Fin r → Inputs n →ₗ[F] F)
    (independent : Function.Surjective (fun x : Inputs n => (fun i => L i x, fun i => R i x))) :
    Function.Surjective (bundle L R) := by
  intro xs
  obtain ⟨x,h⟩ := independent (fun i => (xs i).1, fun i => (xs i).2)
  refine ⟨x,?_⟩
  funext i
  exact Prod.ext (congrFun (congrArg Prod.fst h) i) (congrFun (congrArg Prod.snd h) i)

noncomputable def split_fibers {n r : ℕ} (G : Inputs n →ₗ[F] (Fin r → F×F))
    (surj : Function.Surjective G) : Inputs n ≃ (Fin r → F×F) × LinearMap.ker G where
  toFun x := (G x,⟨x - (surj (G x)).choose, by
    rw [LinearMap.mem_ker,map_sub,(surj (G x)).choose_spec,sub_self]⟩)
  invFun y := y.2.val + (surj y.1).choose
  left_inv x := sub_add_cancel _ _
  right_inv := by
    rintro ⟨y,z⟩
    have h : G (z.val + (surj y).choose) = y := by
      rw [map_add,(surj y).choose_spec,LinearMap.mem_ker.mp z.property,zero_add]
    apply Prod.ext h
    apply Subtype.ext
    change z.val + (surj y).choose -
      (surj (G (z.val + (surj y).choose))).choose = z.val
    rw [h,add_sub_cancel_right]

theorem coordinate_fibers {n r : ℕ} (L R : Fin r → Inputs n →ₗ[F] F)
    (independent : Function.Surjective (fun x : Inputs n => (fun i => L i x, fun i => R i x))) :
    ∃ (k : ℕ) (E : Inputs n ≃ ((Fin r → F×F) × (Fin k → F))),
      (2 : ℤ) ^ (2*r+k) = 2^n ∧ ∀ x i, (E x).1 i = (L i x,R i x) := by
  let G := bundle L R
  let K := LinearMap.ker G
  let k := Module.finrank F K
  let fibers := split_fibers G (bundle_surjective L R independent)
  let E := fibers.trans ((Equiv.refl _).prodCongr (Module.finBasis F K).equivFun.toEquiv)
  refine ⟨k,E,?_,fun x i => rfl⟩
  have card := Fintype.card_congr E
  have rate : 2^n = (4 : ℕ)^r * 2^k := by
    simpa [Inputs,Fintype.card_prod,Fintype.card_fun,ZMod.card] using card
  rw [pow_add,pow_mul]
  norm_num only
  exact_mod_cast rate.symm

end Quadratic29947Fiber

namespace Quadratic29947WitnessParts
open Quadratic29947Walsh Quadratic29947Literal
abbrev F := ZMod 2

theorem linear_coefficients {n : ℕ} (L : Inputs n →ₗ[F] F) (x : Inputs n) :
    L x = ∑ i : Fin n, L (Pi.single i (1 : F)) * x i := by
  classical
  have expansion : (∑ i : Fin n, x i • Pi.single i (1 : F)) = x := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply,eq_comm]
  conv_lhs => rw [← expansion]
  rw [map_sum]
  simp [mul_comm]

theorem added_products {n r : ℕ} (q : Inputs n → F) (shape : quad q)
    (L R : Fin r → Inputs n →ₗ[F] F) (J : Finset (Fin r)) :
    quad (fun x => q x + ∑ i ∈ J, L i x * R i x) := by
  classical
  obtain ⟨b,a,M,expression⟩ := shape
  let N : Fin n → Fin n → F := fun i j =>
    M i j + ∑ z ∈ J, L z (Pi.single i 1) * R z (Pi.single j 1)
  refine ⟨b,a,N,?_⟩
  intro x
  have term (z : Fin r) :
      L z x * R z x =
        ∑ i : Fin n, ∑ j : Fin n,
          L z (Pi.single i 1) * R z (Pi.single j 1) * x i * x j := by
    rw [linear_coefficients (L z),linear_coefficients (R z),Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have flip :
      (∑ z ∈ J, L z x * R z x) =
        ∑ i : Fin n, ∑ j : Fin n,
          (∑ z ∈ J, L z (Pi.single i 1) * R z (Pi.single j 1)) * x i * x j := by
    simp only [term,Finset.sum_mul]
    rw [Finset.sum_comm (s := J)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  change q x + (∑ i ∈ J, L i x * R i x) =
    b + dotProduct a x + ∑ i, ∑ j, N i j * x i * x j
  rw [expression,flip]
  simp only [N,add_mul,Finset.sum_add_distrib]
  ring

theorem split_indices (r c j : ℕ) (fit : j ≤ r-c) :
    ∃ P J T : Finset (Fin r), P.card = min r c ∧ J.card = j ∧
      T.card = (r-c)-j ∧ ∀ f : Fin r → F, (∑ i, f i) = (∑ i ∈ P, f i) + (∑ i ∈ J, f i) + ∑ i ∈ T, f i := by
  classical
  have enough : min r c ≤ (Finset.univ : Finset (Fin r)).card := by simp
  obtain ⟨P, inAll, pc⟩ := Finset.exists_subset_card_eq enough
  let S := (Finset.univ : Finset (Fin r)) \ P
  have sc : S.card = r-c := by
    rw [show S.card = r - min r c by simp [S,Finset.card_sdiff,inAll,pc]]
    omega
  obtain ⟨J, inS, jc⟩ := Finset.exists_subset_card_eq (show j ≤ S.card by rwa [sc])
  let T := S \ J
  refine ⟨P,J,T,pc,jc,by simp [T,Finset.card_sdiff,inS,sc,jc],?_⟩
  intro f
  have all := Finset.sum_sdiff (f := f) inAll
  have second := Finset.sum_sdiff (f := f) inS
  change (∑ i ∈ S, f i) + (∑ i ∈ P, f i) = ∑ i, f i at all
  change (∑ i ∈ T, f i) + (∑ i ∈ J, f i) = ∑ i ∈ S, f i at second
  rw [← all,← second]
  ring

end Quadratic29947WitnessParts

namespace Quadratic29947MatrixForm
open Quadratic29947Polar Quadratic29947Walsh Quadratic29947Literal Quadratic29947NormalForm
def fromMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : LinearMap.BilinForm F (Inputs n) where
  toFun x := dotLinear (M.mulVec x)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    have mv := map_add M.mulVecLin x y
    change M.mulVec (x+y) = M.mulVec x + M.mulVec y at mv
    change dotProduct (M.mulVec (x+y)) z = dotProduct (M.mulVec x) z + dotProduct (M.mulVec y) z
    rw [mv,add_dotProduct]
  map_smul' a x := by
    apply LinearMap.ext
    intro z
    have mv := map_smul M.mulVecLin a x
    change M.mulVec (a • x) = a • M.mulVec x at mv
    change dotProduct (M.mulVec (a • x)) z = a • dotProduct (M.mulVec x) z
    rw [mv,smul_dotProduct]

theorem matrix_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    Module.finrank F (LinearMap.range (fromMatrix M)) = M.rank := by
  classical
  have ker : LinearMap.ker (fromMatrix M) = LinearMap.ker M.mulVecLin := by
    ext x
    simp only [LinearMap.mem_ker]
    change fromMatrix M x = 0 ↔ M.mulVec x = 0
    constructor
    · intro h
      funext i
      have a : fromMatrix M x (Pi.single i 1) = 0 := by rw [h]; rfl
      change dotProduct (M.mulVec x) (Pi.single i 1) = 0 at a
      rw [dotProduct_single_one] at a
      exact a
    · intro off
      apply LinearMap.ext
      intro y
      change dotProduct (M.mulVec x) y = 0
      simp [off]
  have first := (fromMatrix M).finrank_range_add_finrank_ker
  have second := M.mulVecLin.finrank_range_add_finrank_ker
  rw [ker] at first
  exact Nat.add_right_cancel (first.trans second.symm)

theorem polar_compatible (n : ℕ) (d : Inputs n → F) (M : Matrix (Fin n) (Fin n) F)
    (entries : ∀ x y, polar d x y = dotProduct x (M.mulVec y)) :
    (∀ x y, polar d x y = fromMatrix M x y) ∧
    (∀ x, fromMatrix M x x = 0) ∧ (∀ x y, fromMatrix M x y = fromMatrix M y x) := by
  have exchanges (x y : Inputs n) : polar d x y = polar d y x := by
    unfold polar
    rw [add_comm x y]
    ring
  have agrees (x y : Inputs n) : polar d x y = fromMatrix M x y :=
    (exchanges x y).trans ((entries y x).trans (dotProduct_comm _ _))
  refine ⟨agrees,?_,?_⟩
  · intro x
    rw [← agrees,polar]
    have xx : x+x = 0 := funext fun i => twice (x i)
    rw [xx]
    have paired : ∀ a b : F, a+b+b+a=0 := by decide
    exact paired (d 0) (d x)
  · intro x y
    exact (agrees x y).symm.trans ((exchanges x y).trans (agrees y x))

end Quadratic29947MatrixForm

namespace Quadratic29947SymplecticStep

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def perpendicular (B : LinearMap.BilinForm K V) (e f : V) : Submodule K V :=
  LinearMap.ker (B e) ⊓ LinearMap.ker (B f)

def remainder (B : LinearMap.BilinForm K V) (e f : V) : V →ₗ[K] V :=
  LinearMap.id - (B f).smulRight e - (B e).smulRight f

theorem reconstructed (B : LinearMap.BilinForm K V) (e f v : V) :
    B f v • e + B e v • f + remainder B e f v = v := by
  change B f v • e + B e v • f + (v - B f v • e - B e v • f) = v
  abel

theorem remainder_perpendicular (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (ef : B e f = 1) (fe : B f e = 1) (v : V) :
    remainder B e f v ∈ perpendicular B e f := by
  change B e (v - B f v • e - B e v • f) = 0 ∧
    B f (v - B f v • e - B e v • f) = 0
  simp [map_sub, map_smul, smul_eq_mul, alt, ef, fe]

theorem split_pair (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (sym : ∀ v w, B v w = B w v) (ef : B e f = 1) (v w : V) :
    B v w =
      B f v * B e w + B e v * B f w +
        B (remainder B e f v) (remainder B e f w) := by
  have fe : B f e = 1 := (sym _ _).trans ef
  have hv := remainder_perpendicular B e f alt ef fe v
  have hw := remainder_perpendicular B e f alt ef fe w
  change B e (remainder B e f v) = 0 ∧ B f (remainder B e f v) = 0 at hv
  change B e (remainder B e f w) = 0 ∧ B f (remainder B e f w) = 0 at hw
  have he : B (remainder B e f v) e = 0 := (sym _ _).trans hv.1
  have hf : B (remainder B e f v) f = 0 := (sym _ _).trans hv.2
  calc
    B v w = B (B f v • e + B e v • f + remainder B e f v)
             (B f w • e + B e w • f + remainder B e f w) := by
               simp only [reconstructed]
    _ = _ := by
      simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, alt, ef, fe, hw.1, hw.2, he, hf] <;> ring

def coordinates (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (ef : B e f = 1) (fe : B f e = 1) :
    V ≃ₗ[K] (K × K × perpendicular B e f) where
  toFun v := ⟨B f v, B e v, ⟨remainder B e f v, remainder_perpendicular B e f alt ef fe v⟩⟩
  invFun x := x.1 • e + x.2.1 • f + x.2.2.val
  left_inv := reconstructed B e f
  right_inv := by
    rintro ⟨a,b,w⟩
    have hw := w.property
    change B e w.val = 0 ∧ B f w.val = 0 at hw
    have ha : B f (a • e + b • f + w.val) = a := by
      simp [map_add, map_smul, smul_eq_mul, alt, fe, hw.2]
    have hb : B e (a • e + b • f + w.val) = b := by
      simp [map_add, map_smul, smul_eq_mul, alt, ef, hw.1]
    refine Prod.ext ha (Prod.ext hb (Subtype.ext ?_))
    change a • e + b • f + w.val -
      B f (a • e + b • f + w.val) • e - B e (a • e + b • f + w.val) • f = w.val
    rw [ha,hb]
    abel
  map_add' x y := Prod.ext (map_add (B f) x y)
    (Prod.ext (map_add (B e) x y) (Subtype.ext (map_add (remainder B e f) x y)))
  map_smul' c x := Prod.ext (map_smul (B f) c x)
    (Prod.ext (map_smul (B e) c x) (Subtype.ext (map_smul (remainder B e f) c x)))

theorem dimension_step (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (ef : B e f = 1) (fe : B f e = 1) [Module.Finite K V] :
    Module.finrank K V = 2 + Module.finrank K (perpendicular B e f) := by
  rw [(coordinates B e f alt ef fe).finrank_eq, Module.finrank_prod, Module.finrank_prod]
  simp <;> omega

def radicalEquiv (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (sym : ∀ v w, B v w = B w v) (ef : B e f = 1) :
    LinearMap.ker B ≃ₗ[K] LinearMap.ker (B.restrict (perpendicular B e f)) where
  toFun w := by
    have van (z : V) : B w.val z = 0 := by
      exact congrArg (fun f : V →ₗ[K] K => f z) (LinearMap.mem_ker.mp w.property)
    have mem : w.val ∈ perpendicular B e f := by
      change B e w.val = 0 ∧ B f w.val = 0
      exact ⟨(sym _ _).trans (van e), (sym _ _).trans (van f)⟩
    refine ⟨⟨w.val,mem⟩,?_⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro z
    exact van z.val
  invFun w := by
    have fe := (sym f e).trans ef
    have van (z : perpendicular B e f) : B w.val.val z.val = 0 := by
      exact congrArg (fun f : perpendicular B e f →ₗ[K] K => f z) (LinearMap.mem_ker.mp w.property)
    have h := w.val.property
    change B e w.val.val = 0 ∧ B f w.val.val = 0 at h
    have fixed : remainder B e f w.val.val = w.val.val := by
      change w.val.val - B f w.val.val • e - B e w.val.val • f = w.val.val
      simp [h.1,h.2]
    refine ⟨w.val.val,?_⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro z
    have split := split_pair B e f alt sym ef w.val.val z
    have hz := van ⟨remainder B e f z, remainder_perpendicular B e f alt ef fe z⟩
    simpa [h.1,h.2,fixed] using split.trans (by simpa [h.1,h.2,fixed] using hz)
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

theorem rank_step (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (sym : ∀ v w, B v w = B w v) (ef : B e f = 1)
    [Module.Finite K V] :
    Module.finrank K (LinearMap.range B) =
      2 + Module.finrank K (LinearMap.range (B.restrict (perpendicular B e f))) := by
  have ambient := B.finrank_range_add_finrank_ker
  have residual := (B.restrict (perpendicular B e f)).finrank_range_add_finrank_ker
  have ker := (radicalEquiv B e f alt sym ef).finrank_eq
  have dim := dimension_step B e f alt ef ((sym _ _).trans ef)
  omega

end Quadratic29947SymplecticStep

namespace Quadratic29947SymplecticCoordinates
open Quadratic29947SymplecticStep

universe u v
variable {K : Type u} [Field K]

structure Coordinates {V : Type v} [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (r : ℕ) where
  left : Fin r → V →ₗ[K] K
  right : Fin r → V →ₗ[K] K
  product : ∀ x y, B x y =
    ∑ i : Fin r, (left i x * right i y + right i x * left i y)
  independent : Function.Surjective (fun x : V => (fun i => left i x, fun i => right i x))

theorem normalForm (r : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module K V] [Module.Finite K V],
      ∀ B : LinearMap.BilinForm K V,
        (∀ x, B x x = 0) → (∀ x y, B x y = B y x) →
          Module.finrank K (LinearMap.range B) = 2*r → Nonempty (Coordinates B r) := by
  induction r with
  | zero =>
    intro V _ _ _ B _ _ rank
    have zr : Module.finrank K (LinearMap.range B) = 0 := by simpa using rank
    have bottom : LinearMap.range B = ⊥ := Submodule.finrank_eq_zero.mp zr
    have van (x y : V) : B x y = 0 := by
      have mem := LinearMap.mem_range_self B x
      rw [bottom] at mem
      have eq : B x = 0 := by simpa using mem
      exact congrArg (fun f : V →ₗ[K] K => f y) eq
    refine ⟨{left := Fin.elim0, right := Fin.elim0, product := ?_, independent := ?_}⟩
    · intro x y
      simpa using van x y
    · intro z
      refine ⟨0,Prod.ext ?_ ?_⟩
      · funext i
        exact i.elim0
      · funext i
        exact i.elim0
  | succ r ih =>
    intro V _ _ _ B alt sym rank
    have nn : B ≠ 0 := by
      intro h
      have z : Module.finrank K (LinearMap.range B) = 0 :=
        Submodule.finrank_eq_zero.mpr (LinearMap.range_eq_bot.mpr h)
      omega
    obtain ⟨e,f0,notZero⟩ : ∃ e f, B e f ≠ 0 := by
      by_contra! h
      apply nn
      ext x y
      exact h x y
    let f : V := (B e f0)⁻¹ • f0
    have one : B e f = 1 := by
      simp [f, map_smul, smul_eq_mul, notZero]
    have other : B f e = 1 := (sym _ _).trans one
    let W := perpendicular B e f
    let pr : V →ₗ[K] W := (remainder B e f).codRestrict W
      (remainder_perpendicular B e f alt one other)
    have smaller : Module.finrank K (LinearMap.range (B.restrict W)) = 2*r := by
      have step := rank_step B e f alt sym one
      change Module.finrank K (LinearMap.range B) =
        2 + Module.finrank K (LinearMap.range (B.restrict W)) at step
      omega
    obtain ⟨prev⟩ := ih (B.restrict W) (fun x => alt x.val)
      (fun x y => sym x.val y.val) smaller
    refine ⟨⟨Fin.cons (B f) (fun i => (prev.left i).comp pr),
      Fin.cons (B e) (fun i => (prev.right i).comp pr), ?_, ?_⟩⟩
    · intro x y
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.comp_apply]
      have form := split_pair B e f alt sym one x y
      change B x y = B f x * B e y + B e x * B f y + B.restrict W (pr x) (pr y) at form
      exact form.trans (congrArg (fun t => B f x * B e y + B e x * B f y + t) (prev.product (pr x) (pr y)))
    · rintro ⟨a,b⟩
      obtain ⟨w,hw⟩ := prev.independent (Fin.tail a, Fin.tail b)
      let uv := coordinates B e f alt one other
      let x := uv.symm (a 0,b 0,w)
      have h := uv.apply_symm_apply (a 0,b 0,w)
      have hxL : B f x = a 0 := congrArg Prod.fst h
      have hxR : B e x = b 0 := congrArg (fun p : K × K × W => p.2.1) h
      have hpr : pr x = w := congrArg (fun p : K × K × W => p.2.2) h
      refine ⟨x,Prod.ext ?_ ?_⟩
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hxL
        · change prev.left j (pr x) = a j.succ
          rw [hpr]
          exact congrFun (congrArg Prod.fst hw) j
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hxR
        · change prev.right j (pr x) = b j.succ
          rw [hpr]
          exact congrFun (congrArg Prod.snd hw) j

end Quadratic29947SymplecticCoordinates

namespace Quadratic29947QuadraticCoordinates
open Quadratic29947SymplecticCoordinates

abbrev F := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module F V]
variable {B : LinearMap.BilinForm F V} {r : ℕ}

def quadraticPart (D : Coordinates B r) (x : V) : F :=
  ∑ i : Fin r, D.left i x * D.right i x

private theorem crossTerm : ∀ a b c d : F,
    (a+c)*(b+d)+a*b+c*d = a*d+b*c := by
  decide +kernel

theorem quadratic_polar (D : Coordinates B r) (x y : V) :
    quadraticPart D (x+y) + quadraticPart D x + quadraticPart D y = B x y := by
  rw [D.product]
  simp only [quadraticPart, ← Finset.sum_add_distrib, map_add]
  exact Finset.sum_congr rfl (fun i _ => crossTerm _ _ _ _)

private theorem scalarBalance : ∀ a b c z p q w d : F,
    c+a+b+z=d → w+p+q=d → c+z+w=(a+z+p)+(b+z+q) := by
  decide +kernel

private theorem cancelConstant : ∀ a b c : F, a=b+(a+b+c)+c := by
  decide +kernel

private theorem self_cancel : ∀ a : F, a+a=0 := by decide +kernel

def affineLinear (D : Coordinates B r) (q : V → F)
    (polar : ∀ u v, q (u+v)+q u+q v+q 0=B u v) : V →ₗ[F] F where
  toFun x := q x+q 0+quadraticPart D x
  map_add' x y := scalarBalance _ _ _ _ _ _ _ _ (polar x y) (quadratic_polar D x y)
  map_smul' c x := by
    have bits : ∀ c : F, c = 0 ∨ c = 1 := by decide +kernel
    rcases bits c with rfl | rfl
    · change q ((0 : F) • x) + q 0 + quadraticPart D ((0 : F) • x) =
        (0 : F) * (q x + q 0 + quadraticPart D x)
      simp [zero_smul, quadraticPart, self_cancel]
    · change q ((1 : F) • x) + q 0 + quadraticPart D ((1 : F) • x) =
        (1 : F) * (q x + q 0 + quadraticPart D x)
      rw [one_smul, one_mul]

theorem exact_decomposition (D : Coordinates B r) (q : V → F)
    (polar : ∀ u v, q (u+v)+q u+q v+q 0=B u v) (x : V) :
    q x = q 0 + affineLinear D q polar x + quadraticPart D x := by
  exact cancelConstant _ _ _

end Quadratic29947QuadraticCoordinates

namespace Quadratic29947SearchBuild
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def allowed (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

noncomputable def charged (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

structure Build (n : ℕ) where
  gates : List Gate
  legal : ∀ g ∈ gates, allowed g
  back : ∀ j (hj : j < gates.length), ∀ i ∈ gates[j].inputs, i < n + j

def Build.len {n : ℕ} (B : Build n) : ℕ := n + B.gates.length

noncomputable def Build.cost {n : ℕ} (B : Build n) : ℕ := B.gates.countP charged

def Build.wires {n : ℕ} (B : Build n) (x : Fin n → Bool) : List Bool :=
  (⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)

def Build.val {n : ℕ} (B : Build n) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (B.wires x).getD w false

private theorem fold_length (gs : List Gate) (init : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).length =
      init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp
    omega

theorem Build.wires_length {n : ℕ} (B : Build n) (x : Fin n → Bool) :
    (B.wires x).length = B.len := by
  simpa [Build.wires,Build.len,Circuit.wires] using fold_length B.gates (List.ofFn x)

def Build.empty (n : ℕ) : Build n :=
  ⟨[], by simp, by simp⟩

def Build.push {n : ℕ} (B : Build n) (g : Gate)
    (good : allowed g) (earlier : ∀ i ∈ g.inputs, i < B.len) : Build n where
  gates := B.gates ++ [g]
  legal := by
    intro g' mem
    rcases List.mem_append.mp mem with h | h
    · exact B.legal g' h
    · simpa only [List.mem_singleton.mp h] using good
  back := by
    intro j hj i hi
    by_cases old : j < B.gates.length
    · rw [List.getElem_append_left old] at hi
      exact B.back j old i hi
    · have now : j = B.gates.length := by simp at hj; omega
      subst j
      rw [List.getElem_append_right (le_refl _)] at hi
      simp only [Nat.sub_self,List.getElem_singleton] at hi
      exact earlier i hi

theorem Build.push_len {n : ℕ} (B : Build n) (g : Gate) (good) (earlier) :
    (B.push g good earlier).len = B.len + 1 := by
  simp [Build.push,Build.len,Nat.add_assoc]

theorem Build.push_cost {n : ℕ} (B : Build n) (g : Gate) (good) (earlier) :
    (B.push g good earlier).cost = B.cost + (if charged g then 1 else 0) := by
  simp [Build.push,Build.cost,List.countP_append,List.countP_cons]

theorem Build.push_wires {n : ℕ} (B : Build n) (g : Gate) (good) (earlier) (x) :
    (B.push g good earlier).wires x = B.wires x ++ [g.op.eval (g.inputs.map (B.val x))] := by
  simp only [Build.push,Build.wires,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rfl

theorem Build.push_old {n : ℕ} (B : Build n) (g : Gate) (good) (earlier)
    (x) (w : ℕ) (old : w < B.len) :
    (B.push g good earlier).val x w = B.val x w := by
  rw [Build.val,Build.push_wires]
  have bound : w < (B.wires x).length := by simpa only [B.wires_length] using old
  simp only [Build.val,List.getD,List.getElem?_append_left bound]

theorem Build.push_new {n : ℕ} (B : Build n) (g : Gate) (good) (earlier) (x) :
    (B.push g good earlier).val x B.len = g.op.eval (g.inputs.map (B.val x)) := by
  rw [Build.val,Build.push_wires]
  generalize h : B.wires x = w
  have len : w.length = B.len := h ▸ B.wires_length x
  rw [← len]
  simp [List.getD]

theorem Build.raw {n : ℕ} (B : Build n) (x : Fin n → Bool) (i : Fin n) :
    B.val x i = x i := by
  have aux (gs : List Gate) (init : List Bool) (j : ℕ) (bound : j < init.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).getD j false =
      init.getD j false := by
    induction gs generalizing init with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih _ (by simp; omega)]
      simp only [List.getD,List.getElem?_append_left bound]
  rw [Build.val,Build.wires,Circuit.wires,aux _ _ _ (by simp)]
  simp [List.getD,i.isLt]

theorem Build.readsBack {n : ℕ} (B : Build n) (out : ℕ) :
    ReadsBack n (⟨B.gates,out⟩ : Circuit) := by
  intro j hj i hi
  apply B.back j hj i
  simpa only [gateAt,List.getD_eq_getElem _ _ hj] using hi

inductive Expr (n : ℕ)
  | input (i : Fin n)
  | zero
  | neg (a : Expr n)
  | add (a b : Expr n)
  | mul (a b : Expr n)

def Expr.eval {n : ℕ} (x : Fin n → Bool) : Expr n → Bool
  | .input i => x i
  | .zero => false
  | .neg a => !(a.eval x)
  | .add a b => xor (a.eval x) (b.eval x)
  | .mul a b => (a.eval x) && (b.eval x)

def Expr.cost {n : ℕ} : Expr n → ℕ
  | .input _ | .zero => 0
  | .neg a => a.cost
  | .add a b => a.cost + b.cost
  | .mul a b => a.cost + b.cost + 1

def Extends {n : ℕ} (B C : Build n) : Prop :=
  B.len ≤ C.len ∧ ∀ x w, w < B.len → C.val x w = B.val x w

theorem extends_refl {n : ℕ} (B : Build n) : Extends B B :=
  ⟨le_rfl,fun _ _ _ => rfl⟩

theorem extends_trans {n : ℕ} {A B C : Build n} (ab : Extends A B) (bc : Extends B C) :
    Extends A C :=
  ⟨ab.1.trans bc.1, fun x w h => (bc.2 x w (h.trans_le ab.1)).trans (ab.2 x w h)⟩

theorem Build.push_extends {n : ℕ} (B : Build n) (g : Gate) (good) (earlier) :
    Extends B (B.push g good earlier) :=
  ⟨by rw [B.push_len]; omega, fun x w hw => B.push_old g good earlier x w hw⟩

private theorem or_zero (g : Gate) (l : g.inputs = []) :
    charged g = false := by
  simp [charged,l]

private theorem free_mod (i j : ℕ) : charged ⟨.mod 2,[i,j]⟩ = false := by
  simp [charged]

private theorem free_not (i : ℕ) : charged ⟨.not,[i]⟩ = false := by
  simp [charged]

private theorem paid_and (i j : ℕ) : charged ⟨.and,[i,j]⟩ = true := by
  simp [charged]

theorem compile {n : ℕ} (e : Expr n) (B : Build n) :
    ∃ (C : Build n) (w : ℕ),
      Extends B C ∧ w < C.len ∧ C.cost = B.cost + e.cost ∧
        ∀ x, C.val x w = e.eval x := by
  induction e generalizing B with
  | input i =>
    exact ⟨B,i,extends_refl B,by unfold Build.len; omega,by simp [Expr.cost],fun x => B.raw x i⟩
  | zero =>
    let g : Gate := ⟨.or,[]⟩
    have good : allowed g := by simp [g,allowed]
    have early : ∀ i ∈ g.inputs, i < B.len := by simp [g]
    let C := B.push g good early
    refine ⟨C,B.len,B.push_extends g good early,by simp [C,B.push_len],?_,?_⟩
    · dsimp only [C]; rw [B.push_cost,or_zero g rfl]; simp [Expr.cost]
    · intro x
      dsimp only [C]; rw [B.push_new]; rfl
  | neg a ha =>
    obtain ⟨A,i,ini,hi,price,eval⟩ := ha B
    let g : Gate := ⟨.not,[i]⟩
    have good : allowed g := by simp [g,allowed]
    have early : ∀ j ∈ g.inputs, j < A.len := by simpa [g]
    let C := A.push g good early
    refine ⟨C,A.len,extends_trans ini (A.push_extends g good early),by simp [C,A.push_len],?_,?_⟩
    · dsimp only [C]; rw [A.push_cost]; simp [g,free_not,price,Expr.cost]
    · intro x
      dsimp only [C]; rw [A.push_new]
      simpa [g,GateOp.eval,Expr.eval] using congrArg Bool.not (eval x)
  | add a b ha hb =>
    obtain ⟨A,i,ea,hi,pa,va⟩ := ha B
    obtain ⟨C,j,eb,hj,pb,vb⟩ := hb A
    have hci := hi.trans_le eb.1
    let modGate : Gate := ⟨.mod 2,[i,j]⟩
    have good : allowed modGate := by simp [modGate,allowed]
    have early : ∀ q ∈ modGate.inputs, q < C.len := by
      intro q h
      rcases (show q = i ∨ q = j from by simpa [modGate] using h) with rfl | rfl
      · exact hci
      · exact hj
    let D := C.push modGate good early
    let negGate : Gate := ⟨.not,[C.len]⟩
    have ngood : allowed negGate := by simp [negGate,allowed]
    have nearly : ∀ q ∈ negGate.inputs, q < D.len := by simp [negGate,D,C.push_len]
    refine ⟨D.push negGate ngood nearly,D.len,
      extends_trans (extends_trans ea eb)
        (extends_trans (C.push_extends modGate good early) (D.push_extends negGate ngood nearly)),
      by simp [D.push_len],?_,?_⟩
    · rw [D.push_cost,C.push_cost]
      simp [negGate,modGate,free_not,free_mod,pa,pb,Expr.cost,Nat.add_assoc]
    · intro x
      rw [D.push_new]
      change (!(D.val x C.len)) = _
      dsimp only [D]; rw [C.push_new]
      simp only [modGate,List.map_cons,List.map_nil,Expr.eval,eb.2 x i hi,va x,vb x]
      cases a.eval x <;> cases b.eval x <;> decide
  | mul a b ha hb =>
    obtain ⟨A,i,ea,hi,pa,va⟩ := ha B
    obtain ⟨C,j,eb,hj,pb,vb⟩ := hb A
    have hci := hi.trans_le eb.1
    let g : Gate := ⟨.and,[i,j]⟩
    have good : allowed g := by simp [g,allowed]
    have early : ∀ q ∈ g.inputs, q < C.len := by
      intro q h
      rcases (show q = i ∨ q = j from by simpa [g] using h) with rfl | rfl
      · exact hci
      · exact hj
    refine ⟨C.push g good early,C.len,extends_trans (extends_trans ea eb)
      (C.push_extends g good early),by simp [C.push_len],?_,?_⟩
    · rw [C.push_cost]
      simp [g,paid_and,pa,pb,Expr.cost,Nat.add_assoc]
    · intro x
      rw [C.push_new]
      simp [g,GateOp.eval,Expr.eval,eb.2 x i hi,va x,vb x]

end Quadratic29947SearchBuild

namespace Quadratic29947SearchBuild
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev F := ZMod 2

def scalar (b : Bool) : F := if b then 1 else 0

@[simp] theorem scalar_encode (v : F) : scalar (decide (v = 1)) = v := by decide +revert

@[simp] theorem scalar_add (a b : Bool) :
    scalar (xor a b) = scalar a + scalar b := by
  cases a <;> cases b <;> decide

@[simp] theorem scalar_mul (a b : Bool) :
    scalar (a && b) = scalar a * scalar b := by
  cases a <;> cases b <;> decide

@[simp] theorem scalar_neg (b : Bool) : scalar (!b) = 1 + scalar b := by
  cases b <;> decide

def Expr.fieldEval {n : ℕ} (e : Expr n) (x : Fin n → F) : F :=
  scalar (e.eval fun i => decide (x i = 1))

@[simp] theorem Expr.field_input {n : ℕ} (i : Fin n) (x : Fin n → F) :
    (Expr.input i).fieldEval x = x i := by simp [Expr.fieldEval,Expr.eval]

@[simp] theorem Expr.field_zero {n : ℕ} (x : Fin n → F) :
    (Expr.zero : Expr n).fieldEval x = 0 := rfl

@[simp] theorem Expr.field_add {n : ℕ} (a b : Expr n) (x : Fin n → F) :
    (a.add b).fieldEval x = a.fieldEval x + b.fieldEval x := by simp [Expr.fieldEval,Expr.eval]

@[simp] theorem Expr.field_mul {n : ℕ} (a b : Expr n) (x : Fin n → F) :
    (a.mul b).fieldEval x = a.fieldEval x * b.fieldEval x := by simp [Expr.fieldEval,Expr.eval]

@[simp] theorem Expr.field_neg {n : ℕ} (a : Expr n) (x : Fin n → F) :
    a.neg.fieldEval x = 1 + a.fieldEval x := by simp [Expr.fieldEval,Expr.eval]

def Expr.const {n : ℕ} (v : F) : Expr n :=
  if v = 1 then .neg .zero else .zero

@[simp] theorem Expr.const_cost {n : ℕ} (v : F) : (Expr.const v : Expr n).cost = 0 := by
  unfold Expr.const
  split <;> rfl

@[simp] theorem Expr.const_field {n : ℕ} (v : F) (x : Fin n → F) :
    (Expr.const v).fieldEval x = v := by
  unfold Expr.const
  split
  · simp_all
  · have eq : ∀ w : F, w ≠ 1 → w = 0 := by decide
    rw [Expr.field_zero,eq v ‹_›]

def Expr.sumFin {n : ℕ} : {m : ℕ} → (Fin m → Expr n) → Expr n
  | 0, _ => .zero
  | m+1, es => .add (es 0) (sumFin (fun i : Fin m => es i.succ))

@[simp] theorem Expr.sumFin_cost {n m : ℕ} (es : Fin m → Expr n) :
    (Expr.sumFin es).cost = ∑ i, (es i).cost := by
  induction m with
  | zero => simp [Expr.sumFin,Expr.cost]
  | succ m ih => rw [Expr.sumFin,Expr.cost,Fin.sum_univ_succ,ih]

@[simp] theorem Expr.sumFin_field {n m : ℕ} (es : Fin m → Expr n) (x : Fin n → F) :
    (Expr.sumFin es).fieldEval x = ∑ i, (es i).fieldEval x := by
  induction m with
  | zero => simp [Expr.sumFin]
  | succ m ih => rw [Expr.sumFin,Expr.field_add,Fin.sum_univ_succ,ih]

def Expr.linear {n m : ℕ} (wire : Fin m → Fin n) (a : Fin m → F) : Expr n :=
  Expr.sumFin fun i => if a i = 1 then .input (wire i) else .zero

@[simp] theorem Expr.linear_cost {n m : ℕ} (wire : Fin m → Fin n) (a : Fin m → F) :
    (Expr.linear wire a).cost = 0 := by
  rw [Expr.linear,Expr.sumFin_cost]
  apply Finset.sum_eq_zero
  intro i _
  split <;> rfl

@[simp] theorem Expr.linear_field {n m : ℕ} (wire : Fin m → Fin n) (a : Fin m → F)
    (x : Fin n → F) : (Expr.linear wire a).fieldEval x = ∑ i, a i * x (wire i) := by
  rw [Expr.linear,Expr.sumFin_field]
  apply Finset.sum_congr rfl
  intro i _
  split
  · simp_all
  · have eq : ∀ w : F, w ≠ 1 → w = 0 := by decide
    simp [eq (a i) ‹_›]

theorem compile_many {n m : ℕ} (es : Fin m → Expr n) (B : Build n) :
    ∃ (C : Build n) (w : Fin m → ℕ),
      Extends B C ∧ (∀ i, w i < C.len) ∧ C.cost = B.cost + (∑ i, (es i).cost) ∧
        ∀ i x, C.val x (w i) = (es i).eval x := by
  induction m generalizing B with
  | zero =>
    exact ⟨B,Fin.elim0,extends_refl B,(fun i => Fin.elim0 i),by simp,fun i => Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨A,u,eb,hu,pa,va⟩ := compile (es 0) B
    obtain ⟨C,v,ec,hv,pc,vc⟩ := ih (fun i => es i.succ) A
    refine ⟨C,Fin.cons u v,extends_trans eb ec,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hu.trans_le ec.1
      · simpa using hv j
    · rw [pc,pa,Fin.sum_univ_succ]
      omega
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro x
        simpa only [Fin.cons_zero,ec.2 x u hu] using va x
      · simpa only [Fin.cons_succ] using vc j

theorem exists_circuit {n m : ℕ} (out : Expr n) (taps : Fin m → Expr n) :
    ∃ (C : Circuit) (tap : Fin m → ℕ), ReadsBack n C ∧
      (∀ g ∈ C.gates, allowed g) ∧
      C.gates.countP charged = out.cost + ∑ i, (taps i).cost ∧
      C.output < n + C.size ∧ (∀ i, tap i < n + C.size) ∧
      (∀ x : Fin n → F,
        scalar (C.eval (List.ofFn (fun i => decide (x i = 1)))) = out.fieldEval x ∧
        ∀ i, scalar ((C.wires (List.ofFn (fun j => decide (x j = 1)))).getD (tap i) false) =
          (taps i).fieldEval x) := by
  obtain ⟨B,w,_,hw,price,hout⟩ := compile out (Build.empty n)
  obtain ⟨E,t,eb,ht,pt,vt⟩ := compile_many taps B
  refine ⟨⟨E.gates,w⟩,t,E.readsBack w,E.legal,?_,?_,?_,?_⟩
  · change E.cost = _
    rw [pt,price]
    simp [Build.cost,Build.empty]
  · simpa [Build.len,Circuit.size] using hw.trans_le eb.1
  · simpa [Build.len,Circuit.size] using ht
  · intro x
    constructor
    · change scalar (E.val (fun i => decide (x i = 1)) w) = _
      rw [eb.2 _ w hw,hout]
      rfl
    · intro i
      change scalar (E.val (fun j => decide (x j = 1)) (t i)) = _
      rw [vt]
      rfl

end Quadratic29947SearchBuild

open Quadratic29947Walsh

abbrev F := ZMod 2

theorem character_abs (x : F) : |character x| = 1 := by
  have all : ∀ a : F, |character a| = 1 := by decide
  exact all x

def scalar (b : Bool) : F := if b then 1 else 0

theorem two_gate_laws :
    (∀ a b, scalar (GateOp.eval .and [a,b]) = scalar a * scalar b) ∧
    (∀ a b, scalar (GateOp.eval .or [a,b]) =
      scalar a + scalar b + scalar a * scalar b) ∧
    (∀ a b, scalar (GateOp.eval (.mod 2) [a,b]) = 1 + scalar a + scalar b) ∧
    (∀ a, scalar (GateOp.eval .not [a]) = 1 + scalar a) ∧
    (∀ a, scalar (GateOp.eval (.mod 2) [a]) = 1 + scalar a) := by decide

section Wires
variable {V : Type*}

def read (stock : List (Bool → V → F)) (i : ℕ) : Bool → V → F :=
  stock.getD i (fun _ _ => 0)

def run (g : Gate) (stock : List (Bool → V → F)) (t : Bool) (x : V) : F :=
  scalar (g.op.eval (g.inputs.map fun i => decide (read stock i t x = 1)))

theorem encode_decide : ∀ a : F, scalar (decide (a = 1)) = a := by decide

theorem eval_binary_and (stock : List (Bool → V → F)) (a b : ℕ) (t : Bool) (x : V) :
    run ⟨.and,[a,b]⟩ stock t x = read stock a t x * read stock b t x := by
  simp only [run,List.map_cons,List.map_nil,two_gate_laws.1,encode_decide]

theorem eval_binary_or (stock : List (Bool → V → F)) (a b : ℕ) (t : Bool) (x : V) :
    run ⟨.or,[a,b]⟩ stock t x =
      read stock a t x + read stock b t x + read stock a t x * read stock b t x := by
  simp only [run,List.map_cons,List.map_nil,two_gate_laws.2.1,encode_decide]

def wires (tape : List Gate) (stock : List (Bool → V → F)) : List (Bool → V → F) :=
  tape.foldl (fun w g => w ++ [run g w]) stock

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_value (stock : List (Bool → V → F)) (w : List Bool)
    (t : Bool) (x : V) (agrees : stock.map (fun f => f t x) = w.map scalar) (i : ℕ) :
    read stock i t x = scalar (w.getD i false) := by
  have lengths := congrArg List.length agrees
  simp only [List.length_map] at lengths
  by_cases ok : i < stock.length
  · have ok' : i < w.length := by omega
    have eq := congrArg (fun xs : List F => xs.getD i 0) agrees
    simpa only [read,List.getD_eq_getElem _ _ ok,List.getD_eq_getElem _ _ ok',
      List.getD_eq_getElem _ _ (by simpa only [List.length_map] using ok :
        i < (stock.map fun f => f t x).length),
      List.getD_eq_getElem _ _ (by simpa only [List.length_map] using ok' :
        i < (w.map scalar).length),List.getElem_map] using eq
  · have out : stock.length ≤ i := by omega
    have out' : w.length ≤ i := by omega
    rw [read,List.getD_eq_default _ _ out,List.getD_eq_default _ _ out']
    rfl

theorem exact_wire (tape : List Gate) (stock : List (Bool → V → F))
    (w : List Bool) (t : Bool) (x : V)
    (agrees : stock.map (fun f => f t x) = w.map scalar) :
    (wires tape stock).map (fun f => f t x) = (tape.foldl boolStep w).map scalar := by
  induction tape generalizing stock w with
  | nil => exact agrees
  | cons g tape ih =>
    apply ih
    have inv : ∀ b : Bool, decide (scalar b = 1) = b := by decide
    have value : run g stock t x = scalar (g.op.eval (g.inputs.map fun i => w.getD i false)) := by
      simp only [run,read_value stock w t x agrees,inv]
    simp only [boolStep,List.map_append,List.map_cons,List.map_nil,agrees,value]

theorem circuit_wires (C : Circuit) (stock : List (Bool → V → F)) (w : List Bool)
    (t : Bool) (x : V) (agrees : stock.map (fun f => f t x) = w.map scalar) :
    (wires C.gates stock).map (fun f => f t x) = (C.wires w).map scalar :=
  exact_wire C.gates stock w t x agrees

end Wires

section Spectral
variable {V : Type*} [AddCommGroup V]

def Spec (c : ℕ) (f : Bool → V → F) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (coef : J → ℤ) (l : J → (V →+ F)) (b : J → Bool → F),
    (∀ t v, 2 ^ c * character (f t v) = ∑ j, coef j * character (l j v + b j t)) ∧
    ∑ j, |coef j| ≤ 4 ^ c

def IsAff (f : Bool → V → F) : Prop :=
  ∃ (l : V →+ F) (b : Bool → F), ∀ t v, f t v = l v + b t

theorem spec_aff {f : Bool → V → F} (h : IsAff f) : Spec 0 f := by
  obtain ⟨l,b,eq⟩ := h
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => l, fun _ => b, ?_, ?_⟩
  · intro t v
    simp [eq]
  · simp

theorem spec_step {c : ℕ} {f1 f2 f3 f4 g : Bool → V → F}
    (h1 : Spec c f1) (h2 : Spec c f2) (h3 : Spec c f3) (h4 : Spec c f4)
    (id : ∀ t v, 2 * character (g t v) =
      character (f1 t v) + character (f2 t v) + character (f3 t v) - character (f4 t v)) :
    Spec (c+1) g := by
  obtain ⟨J1,i1,c1,l1,b1,e1,n1⟩ := h1
  obtain ⟨J2,i2,c2,l2,b2,e2,n2⟩ := h2
  obtain ⟨J3,i3,c3,l3,b3,e3,n3⟩ := h3
  obtain ⟨J4,i4,c4,l4,b4,e4,n4⟩ := h4
  refine ⟨(J1 ⊕ J2) ⊕ (J3 ⊕ J4), inferInstance,
    Sum.elim (Sum.elim c1 c2) (Sum.elim c3 (fun j => - c4 j)),
    Sum.elim (Sum.elim l1 l2) (Sum.elim l3 l4),
    Sum.elim (Sum.elim b1 b2) (Sum.elim b3 b4), ?_, ?_⟩
  · intro t v
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_mul,
      Finset.sum_neg_distrib]
    rw [← e1 t v, ← e2 t v, ← e3 t v, ← e4 t v, pow_succ, mul_assoc, id]
    ring
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, abs_neg]
    rw [pow_succ]
    linarith

theorem spec_mono {c : ℕ} {f : Bool → V → F} (h : Spec c f) : Spec (c+1) f :=
  spec_step h h h h (fun t v => by ring)

def gens (stock : List (Bool → V → F)) : Set (Bool → V → F) :=
  {f | f ∈ stock} ∪ {f | ∃ b : Bool → F, f = fun t _ => b t}

def Inv (c : ℕ) (stock : List (Bool → V → F)) : Prop :=
  ∀ g ∈ Submodule.span F (gens stock), Spec c g

theorem const_mem (stock : List (Bool → V → F)) (b : Bool → F) :
    (fun t (_ : V) => b t) ∈ Submodule.span F (gens stock) :=
  Submodule.subset_span (Or.inr ⟨b, rfl⟩)

theorem read_mem (stock : List (Bool → V → F)) (i : ℕ) :
    read stock i ∈ Submodule.span F (gens stock) := by
  unfold read
  by_cases ok : i < stock.length
  · rw [List.getD_eq_getElem _ _ ok]
    exact Submodule.subset_span (Or.inl (List.getElem_mem ok))
  · rw [List.getD_eq_default _ _ (by omega)]
    exact const_mem stock fun _ => 0

theorem add_mem' {S : Submodule F (Bool → V → F)} {f g : Bool → V → F}
    (hf : f ∈ S) (hg : g ∈ S) : (fun t x => f t x + g t x) ∈ S :=
  S.add_mem hf hg

theorem free_mem (g : Gate) (stock : List (Bool → V → F))
    (arity : g.inputs.length ≤ 2)
    (basis : g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))
    (pay : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)) :
    run g stock ∈ Submodule.span F (gens stock) := by
  rcases g with ⟨op, args⟩
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ args.length = 1) at basis
  rcases args with _ | ⟨a,args⟩
  · exact const_mem stock fun _ => scalar (op.eval [])
  rcases args with _ | ⟨b, rest⟩
  · rcases basis with hw | hw | hw | ⟨hw,_⟩ <;> subst op
    · have semantic : ∀ b : Bool, scalar (GateOp.eval .and [b]) = scalar b := by decide
      unfold run
      simp only [List.map_cons,List.map_nil,semantic,encode_decide]
      exact read_mem stock a
    · have semantic : ∀ b : Bool, scalar (GateOp.eval .or [b]) = scalar b := by decide
      unfold run
      simp only [List.map_cons,List.map_nil,semantic,encode_decide]
      exact read_mem stock a
    · unfold run
      simp only [List.map_cons,List.map_nil,two_gate_laws.2.2.2.2,encode_decide]
      exact add_mem' (const_mem stock fun _ => 1) (read_mem stock a)
    · unfold run
      simp only [List.map_cons,List.map_nil,two_gate_laws.2.2.2.1,encode_decide]
      exact add_mem' (const_mem stock fun _ => 1) (read_mem stock a)
  have noMore : rest = [] := by
    have len : rest.length = 0 := by simpa using arity
    exact List.length_eq_zero_iff.mp len
  subst rest
  rcases basis with hw | hw | hw | ⟨hw, bad⟩ <;> subst op
  · exact False.elim (pay ⟨Or.inl rfl,rfl⟩)
  · exact False.elim (pay ⟨Or.inr rfl,rfl⟩)
  · unfold run
    simp only [List.map_cons,List.map_nil,two_gate_laws.2.2.1,encode_decide]
    exact add_mem' (add_mem' (const_mem stock fun _ => 1) (read_mem stock a)) (read_mem stock b)
  · cases bad

theorem gens_append (stock : List (Bool → V → F)) (h : Bool → V → F) :
    gens (stock ++ [h]) ⊆ insert h (gens stock) := by
  rintro f (mem | mem)
  · rcases List.mem_append.mp mem with old | new
    · exact Or.inr (Or.inl old)
    · exact Or.inl (by simpa using new)
  · exact Or.inr (Or.inr mem)

theorem inv_free {c : ℕ} (stock : List (Bool → V → F)) (h : Bool → V → F)
    (inv : Inv c stock) (mem : h ∈ Submodule.span F (gens stock)) :
    Inv c (stock ++ [h]) := by
  intro g hg
  apply inv
  have le : Submodule.span F (insert h (gens stock)) ≤ Submodule.span F (gens stock) :=
    Submodule.span_le.mpr (Set.insert_subset mem Submodule.subset_span)
  exact le (Submodule.span_mono (gens_append stock h) hg)

theorem key_and : ∀ p q z : F, 2 * character (p * q + z) =
    character z + character (z + p) + character (z + q) - character (z + p + q) := by decide

theorem key_or : ∀ p q z : F, 2 * character (p + q + p * q + z) =
    character (z + p + q) + character (z + q) + character (z + p) - character z := by decide

theorem inv_paid {c : ℕ} (stock : List (Bool → V → F)) (a b : ℕ) (isOr : Bool)
    (inv : Inv c stock) :
    Inv (c+1) (stock ++ [run ⟨if isOr then .or else .and,[a,b]⟩ stock]) := by
  intro g hg
  have hg' := Submodule.span_mono (gens_append stock _) hg
  obtain ⟨ε, z, hz, rfl⟩ := Submodule.mem_span_insert.mp hg'
  have either : ∀ e : F, e = 0 ∨ e = 1 := by decide
  have ra := read_mem stock a
  have rb := read_mem stock b
  rcases either ε with rfl | rfl
  · simpa using spec_mono (inv z hz)
  · cases isOr
    · refine spec_step (inv z hz) (inv _ (add_mem' hz ra)) (inv _ (add_mem' hz rb))
        (inv _ (add_mem' (add_mem' hz ra) rb)) ?_
      intro t v
      simp only [Pi.add_apply, one_smul, Bool.false_eq_true, ite_false,
        eval_binary_and]
      exact key_and _ _ _
    · refine spec_step (inv _ (add_mem' (add_mem' hz ra) rb)) (inv _ (add_mem' hz rb))
        (inv _ (add_mem' hz ra)) (inv z hz) ?_
      intro t v
      simp only [Pi.add_apply, one_smul, ite_true, eval_binary_or]
      exact key_or _ _ _

def allowed (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

def paid (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

noncomputable def price (gs : List Gate) : ℕ :=
  gs.countP (fun h => @decide (paid h) (Classical.propDecidable _))

theorem inv_gate {c : ℕ} (stock : List (Bool → V → F)) (g : Gate) (ok : allowed g)
    (inv : Inv c stock) :
    (paid g → Inv (c+1) (stock ++ [run g stock])) ∧
    (¬ paid g → Inv c (stock ++ [run g stock])) := by
  constructor
  · intro pay
    rcases g with ⟨op, args⟩
    obtain ⟨hop, len⟩ := pay
    change op = .and ∨ op = .or at hop
    change args.length = 2 at len
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp len
    rcases hop with rfl | rfl
    · exact inv_paid stock a b false inv
    · exact inv_paid stock a b true inv
  · intro pay
    exact inv_free stock _ inv (free_mem g stock ok.1 ok.2 pay)

theorem inv_wires (tape : List Gate) : ∀ (c : ℕ) (stock : List (Bool → V → F)),
    Inv c stock → (∀ g ∈ tape, allowed g) → Inv (c + price tape) (wires tape stock) := by
  induction tape with
  | nil =>
    intro c stock inv _
    simpa [price, wires] using inv
  | cons g tape ih =>
    intro c stock inv ok
    have step := inv_gate stock g (ok g (List.mem_cons_self ..)) inv
    have rest : ∀ h ∈ tape, allowed h := fun h mem => ok h (List.mem_cons_of_mem _ mem)
    by_cases pay : paid g
    · have next := ih (c+1) _ (step.1 pay) rest
      have count : price (g :: tape) = price tape + 1 := by
        simp [price, pay]
      rw [count]
      have same : c + (price tape + 1) = c + 1 + price tape := by omega
      rw [same]
      exact next
    · have next := ih c _ (step.2 pay) rest
      have count : price (g :: tape) = price tape := by
        simp [price, pay]
      rw [count]
      exact next

end Spectral

abbrev X (n : ℕ) := Fin (n+1) → F
abbrev U (n : ℕ) := Fin n → F

def yv (n : ℕ) (t : Bool) (u : U n) : X n := Fin.cons (if t then 1 else 0) u

def bits (m : ℕ) (u : Fin m → F) : List Bool := List.ofFn fun j : Fin m => decide (u j = 1)

def base (n : ℕ) : List (Bool → X n × U n → F) :=
  (List.ofFn fun i : Fin (n+1) => fun (_ : Bool) (v : X n × U n) => v.1 i) ++
  (List.ofFn fun i : Fin (n+1) => fun (t : Bool) (v : X n × U n) => yv n t v.2 i)

theorem base_agrees (n : ℕ) (t : Bool) (v : X n × U n) :
    (base n).map (fun f => f t v) =
      (bits (n+1) v.1 ++ bits (n+1) (yv n t v.2)).map scalar := by
  simp only [base, bits, List.map_append, List.map_ofFn]
  congr 1 <;>
  · apply congrArg List.ofFn
    funext j
    exact (encode_decide _).symm

theorem base_inv (n : ℕ) : Inv 0 (base n) := by
  intro g hg
  apply spec_aff
  induction hg using Submodule.span_induction with
  | mem f hf =>
    rcases hf with mem | ⟨b, rfl⟩
    · rcases List.mem_append.mp mem with m | m
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp m
        exact ⟨(Pi.evalAddMonoidHom _ i).comp (AddMonoidHom.fst _ _), fun _ => 0,
          fun t v => by simp⟩
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp m
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ⟨0, fun t => if t then 1 else 0, fun t v => by simp [yv]⟩
        · exact ⟨(Pi.evalAddMonoidHom _ j).comp (AddMonoidHom.snd _ _), fun _ => 0,
            fun t v => by simp [yv]⟩
    · exact ⟨0, b, fun t v => by simp⟩
  | zero => exact ⟨0, fun _ => 0, fun t v => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨l1,b1,e1⟩ := hf
    obtain ⟨l2,b2,e2⟩ := hg
    refine ⟨l1 + l2, fun t => b1 t + b2 t, fun t v => ?_⟩
    simp only [Pi.add_apply, e1, e2, AddMonoidHom.add_apply]
    abel
  | smul a f _ hf =>
    obtain ⟨l,b,e⟩ := hf
    rcases (by decide : ∀ e : F, e = 0 ∨ e = 1) a with rfl | rfl
    · exact ⟨0, fun _ => 0, fun t v => by simp⟩
    · exact ⟨l, b, fun t v => by simp [e]⟩

theorem output_value (n : ℕ) (C : Circuit) (t : Bool) (v : X n × U n) :
    read (wires C.gates (base n)) C.output t v =
      scalar (C.eval (bits (n+1) v.1 ++ bits (n+1) (yv n t v.2))) :=
  read_value _ _ t v (circuit_wires C _ _ t v (base_agrees n t v)) C.output

theorem circuit_spec (n : ℕ) (C : Circuit) (ok : ∀ g ∈ C.gates, allowed g) :
    Spec (price C.gates) (fun t (v : X n × U n) =>
      scalar (C.eval (bits (n+1) v.1 ++ bits (n+1) (yv n t v.2)))) := by
  have inv := inv_wires C.gates 0 (base n) (base_inv n) ok
  have out := inv _ (read_mem (wires C.gates (base n)) C.output)
  rw [zero_add] at out
  have eq : (fun t (v : X n × U n) =>
      scalar (C.eval (bits (n+1) v.1 ++ bits (n+1) (yv n t v.2)))) =
      read (wires C.gates (base n)) C.output := by
    funext t v
    exact (output_value n C t v).symm
  rw [eq]
  exact out

def num (n : ℕ) (Q : Bool → U n → F) (C : Circuit) (t : Bool) : ℤ :=
  ∑ x : X n, ∑ u : U n,
    if C.eval (bits (n+1) x ++ bits (n+1) (yv n t u)) = decide (x ⬝ᵥ yv n t u + Q t u = 1)
    then 1 else -1

theorem agree_character : ∀ (b : Bool) (a : F),
    (if b = decide (a = 1) then (1 : ℤ) else -1) = character (scalar b + a) := by decide

def dotHom (n : ℕ) (y : X n) : X n →+ F :=
  AddMonoidHom.mk' (fun x => x ⬝ᵥ y) (fun a b => add_dotProduct a b y)

theorem card_X (n : ℕ) : (Fintype.card (X n) : ℤ) = 2 ^ (n+1) := by
  simp [X]

theorem dotHom_inj (n : ℕ) (y y' : X n) (same : dotHom n y = dotHom n y') : y = y' := by
  funext i
  have at_i := DFunLike.congr_fun same (Pi.single i 1)
  simpa [dotHom] using at_i

theorem diag (n : ℕ) (l : X n × U n →+ F) (b : Bool → F) (Q : Bool → U n → F) :
    ∑ t : Bool, |∑ x : X n, ∑ u : U n,
      character (l (x,u) + b t) * character (x ⬝ᵥ yv n t u + Q t u)| ≤ 2 ^ (n+1) := by
  classical
  let hom : Bool × U n → (X n →+ F) :=
    fun p => l.comp (AddMonoidHom.inl _ _) + dotHom n (yv n p.1 p.2)
  have inner (t : Bool) (u : U n) :
      ∑ x : X n, character (l (x,u) + b t) * character (x ⬝ᵥ yv n t u + Q t u)
        = character (l (0,u) + b t + Q t u) *
          (if hom (t,u) = 0 then (2 : ℤ) ^ (n+1) else 0) := by
    have total := hom_sum (hom (t,u))
    rw [card_X] at total
    rw [← total, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [← character_add, ← character_add]
    congr 1
    have split : l (x,u) = l (x,0) + l (0,u) := by
      rw [← map_add]
      simp
    rw [split]
    simp only [hom, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.inl_apply,
      dotHom, AddMonoidHom.mk'_apply]
    ring
  have single : (Finset.univ.filter fun p : Bool × U n => hom p = 0).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have same : dotHom n (yv n p.1 p.2) = dotHom n (yv n q.1 q.2) := add_left_cancel (hp.trans hq.symm)
    have ys : yv n p.1 p.2 = yv n q.1 q.2 := dotHom_inj n _ _ same
    obtain ⟨t1,u1⟩ := p
    obtain ⟨t2,u2⟩ := q
    obtain ⟨head, tail⟩ := Fin.cons_inj.mp ys
    have bit : ∀ a c : Bool, (if a then (1 : F) else 0) = (if c then 1 else 0) → a = c := by
      decide
    exact Prod.ext (bit _ _ head) tail
  calc
    _ ≤ ∑ t : Bool, ∑ u : U n, (if hom (t,u) = 0 then (2 : ℤ) ^ (n+1) else 0) := by
      apply Finset.sum_le_sum
      intro t _
      rw [Finset.sum_comm]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      rw [inner, abs_mul, character_abs, one_mul]
      split <;> simp
    _ = ∑ p : Bool × U n, (if hom p = 0 then (2 : ℤ) ^ (n+1) else 0) := by
      rw [Fintype.sum_prod_type]
    _ = ((Finset.univ.filter fun p : Bool × U n => hom p = 0).card : ℤ) * 2 ^ (n+1) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * 2 ^ (n+1) := by
      gcongr
      exact_mod_cast single
    _ = _ := one_mul _

theorem upper_num (n : ℕ) (Q : Bool → U n → F) (C : Circuit)
    (ok : ∀ g ∈ C.gates, allowed g) :
    |num n Q C false| + |num n Q C true| ≤ 2 ^ (price C.gates + (n+1)) := by
  obtain ⟨J, _, coef, l, b, eq, norm⟩ := circuit_spec n C ok
  let G : J → Bool → ℤ := fun j t => ∑ x : X n, ∑ u : U n,
    character (l j (x,u) + b j t) * character (x ⬝ᵥ yv n t u + Q t u)
  have expand (t : Bool) : 2 ^ price C.gates * num n Q C t = ∑ j, coef j * G j t := by
    have h1 : ∑ j, coef j * G j t = ∑ x : X n, ∑ j, ∑ u : U n,
        coef j * (character (l j (x,u) + b j t) * character (x ⬝ᵥ yv n t u + Q t u)) := by
      simp only [G, Finset.mul_sum]
      exact Finset.sum_comm
    rw [h1, num, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [agree_character, character_add, ← mul_assoc, eq t (x,u), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have each (j : J) : |G j false| + |G j true| ≤ 2 ^ (n+1) := by
    have d := diag n (l j) (b j) Q
    rw [Fintype.sum_bool] at d
    linarith
  have bound (t : Bool) : 2 ^ price C.gates * |num n Q C t| ≤ ∑ j, |coef j| * |G j t| := by
    have pos : (0 : ℤ) ≤ 2 ^ price C.gates := by positivity
    rw [← abs_of_nonneg pos, ← abs_mul, expand]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    simp only [abs_mul]
  have sum : 2 ^ price C.gates * (|num n Q C false| + |num n Q C true|) ≤
      2 ^ price C.gates * 2 ^ (price C.gates + (n+1)) := by
    calc
      _ ≤ ∑ j, |coef j| * (|G j false| + |G j true|) := by
        simp only [mul_add, Finset.sum_add_distrib]
        exact add_le_add (bound false) (bound true)
      _ ≤ ∑ j, |coef j| * 2 ^ (n+1) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (each j) (abs_nonneg _)
      _ = (∑ j, |coef j|) * 2 ^ (n+1) := by rw [Finset.sum_mul]
      _ ≤ 4 ^ price C.gates * 2 ^ (n+1) := by gcongr
      _ = _ := by
        rw [show (4 : ℤ) = 2 * 2 by norm_num, mul_pow, pow_add]
        ring
  exact le_of_mul_le_mul_left sum (by positivity)

section Elim
variable {n : ℕ}

abbrev YF (n : ℕ) := Bool → U n → F

def PA (n : ℕ) : Set (YF n) :=
  {f | ∃ (b : Bool → F) (L : U n →ₗ[F] F), ∀ t u, f t u = b t + L u}

def spanY (ys : List (YF n)) : Submodule F (YF n) :=
  Submodule.span F ({f | f ∈ ys} ∪ PA n)

inductive YStock : ℕ → List (YF n) → Prop
  | nil : YStock 0 []
  | snoc (c : ℕ) (ys : List (YF n)) (f g : YF n) : YStock c ys → f ∈ spanY ys → g ∈ spanY ys →
      YStock (c+1) (ys ++ [fun t u => f t u * g t u])

theorem spanY_mono (ys : List (YF n)) (h : YF n) : spanY ys ≤ spanY (ys ++ [h]) :=
  Submodule.span_mono (Set.union_subset_union_left _ (fun _ hf => List.mem_append_left _ hf))

theorem spanY_new (ys : List (YF n)) (h : YF n) : h ∈ spanY (ys ++ [h]) :=
  Submodule.subset_span (Or.inl (by simp))

theorem spanY_const (ys : List (YF n)) (b : Bool → F) :
    (fun t (_ : U n) => b t) ∈ spanY ys :=
  Submodule.subset_span (Or.inr ⟨b, 0, fun t u => by simp⟩)

def Leaf {j : ℕ} (a : Fin j → X n) (φc : Fin j → YF n) (t : Bool) (x : X n) (u : U n) : Prop :=
  ∀ i, a i ⬝ᵥ x = φc i t u

theorem leaf_cons {j : ℕ} (a : Fin j → X n) (φc : Fin j → YF n) (l : X n) (p : YF n)
    (t : Bool) (x : X n) (u : U n) :
    Leaf (Fin.cons l a : Fin (j+1) → X n) (Fin.cons p φc : Fin (j+1) → YF n) t x u ↔
      l ⬝ᵥ x = p t u ∧ Leaf a φc t x u := by
  simp [Leaf, Fin.forall_fin_succ]

def Rep {j : ℕ} (a : Fin j → X n) (φc : Fin j → YF n) (ys : List (YF n))
    (f : Bool → X n × U n → F) : Prop :=
  ∃ (lam : X n) (φ : YF n), φ ∈ spanY ys ∧
    ∀ t x u, Leaf a φc t x u → f t (x,u) = lam ⬝ᵥ x + φ t u

variable {j : ℕ} {a : Fin j → X n} {φc : Fin j → YF n} {ys : List (YF n)}

theorem rep_add {f g : Bool → X n × U n → F} (hf : Rep a φc ys f) (hg : Rep a φc ys g) :
    Rep a φc ys (fun t v => f t v + g t v) := by
  obtain ⟨l1,p1,m1,e1⟩ := hf
  obtain ⟨l2,p2,m2,e2⟩ := hg
  refine ⟨l1 + l2, p1 + p2, Submodule.add_mem _ m1 m2, fun t x u leaf => ?_⟩
  simp only [e1 t x u leaf, e2 t x u leaf, add_dotProduct, Pi.add_apply]
  ring

theorem rep_const (b : Bool → F) : Rep a φc ys (fun t _ => b t) :=
  ⟨0, fun t _ => b t, spanY_const ys b, fun t x u _ => by simp⟩

theorem rep_span (stock : List (Bool → X n × U n → F)) (h : ∀ f ∈ stock, Rep a φc ys f) :
    ∀ f ∈ Submodule.span F (gens stock), Rep a φc ys f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with m | ⟨b, rfl⟩
    · exact h f m
    · exact rep_const b
  | zero => exact rep_const (fun _ => 0)
  | add f g _ _ hf hg => exact rep_add hf hg
  | smul c f _ hf =>
    rcases (by decide : ∀ e : F, e = 0 ∨ e = 1) c with rfl | rfl
    · rw [zero_smul]
      exact rep_const (fun _ => 0)
    · rw [one_smul]
      exact hf

theorem rep_mono_ys {f : Bool → X n × U n → F} (h : YF n) (hf : Rep a φc ys f) :
    Rep a φc (ys ++ [h]) f := by
  obtain ⟨l,p,m,e⟩ := hf
  exact ⟨l,p,spanY_mono ys h m,e⟩

theorem rep_cons {f : Bool → X n × U n → F} (l : X n) (p : YF n) (hf : Rep a φc ys f) :
    Rep (Fin.cons l a : Fin (j+1) → X n) (Fin.cons p φc : Fin (j+1) → YF n) ys f := by
  obtain ⟨l',p',m,e⟩ := hf
  exact ⟨l',p',m,fun t x u leaf => e t x u ((leaf_cons a φc l p t x u).mp leaf).2⟩

theorem rep_reduce {f : Bool → X n × U n → F} (inside : ∀ i, φc i ∈ spanY ys)
    (lam : X n) (φ : YF n) (mφ : φ ∈ spanY ys)
    (e : ∀ t x u, Leaf a φc t x u → f t (x,u) = lam ⬝ᵥ x + φ t u)
    (hl : lam ∈ Submodule.span F (Set.range a)) :
    ∃ ψ : YF n, ψ ∈ spanY ys ∧ ∀ t x u, Leaf a φc t x u → f t (x,u) = ψ t u := by
  obtain ⟨τ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hl
  refine ⟨(∑ i, τ i • φc i) + φ,
    Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (inside i)) mφ,
    fun t x u leaf => ?_⟩
  rw [e t x u leaf, sum_dotProduct]
  simp only [smul_dotProduct, leaf _, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]

theorem split_reps (stock : List (Bool → X n × U n → F)) (reps : ∀ f ∈ stock, Rep a φc ys f)
    (P Q W h : Bool → X n × U n → F) (hQ : Rep a φc ys Q) (hW : Rep a φc ys W)
    (eq : ∀ t v, h t v = P t v * Q t v + W t v)
    (lP : X n) (pP : YF n)
    (eP : ∀ t x u, Leaf a φc t x u → P t (x,u) = lP ⬝ᵥ x + pP t u) (σ : F) :
    ∀ f ∈ stock ++ [h], Rep (Fin.cons lP a : Fin (j+1) → X n)
      (Fin.cons (fun t u => σ + pP t u) φc : Fin (j+1) → YF n) ys f := by
  intro f mem
  rcases List.mem_append.mp mem with old | new
  · exact rep_cons _ _ (reps f old)
  · obtain rfl : f = h := by simpa using new
    have value : ∀ t x u, Leaf (Fin.cons lP a : Fin (j+1) → X n)
        (Fin.cons (fun t u => σ + pP t u) φc : Fin (j+1) → YF n) t x u → P t (x,u) = σ := by
      intro t x u leaf
      obtain ⟨first, rest⟩ := (leaf_cons a φc lP _ t x u).mp leaf
      rw [eP t x u rest, first]
      have cancel : ∀ s p : F, s + p + p = s := by decide
      exact cancel _ _
    have hQ' := rep_cons lP (fun t u => σ + pP t u) hQ
    have hW' := rep_cons lP (fun t u => σ + pP t u) hW
    rcases (by decide : ∀ e : F, e = 0 ∨ e = 1) σ with rfl | rfl
    · obtain ⟨l,p,m,e⟩ := hW'
      refine ⟨l,p,m,fun t x u leaf => ?_⟩
      rw [eq, value t x u leaf, zero_mul, zero_add, e t x u leaf]
    · obtain ⟨l,p,m,e⟩ := rep_add hQ' hW'
      refine ⟨l,p,m,fun t x u leaf => ?_⟩
      rw [eq, value t x u leaf, one_mul]
      exact e t x u leaf

theorem paid_cases (stock : List (Bool → X n × U n → F)) (reps : ∀ f ∈ stock, Rep a φc ys f)
    (inside : ∀ i, φc i ∈ spanY ys)
    (P Q W h : Bool → X n × U n → F) (hP : Rep a φc ys P) (hQ : Rep a φc ys Q)
    (hW : Rep a φc ys W) (eq : ∀ t v, h t v = P t v * Q t v + W t v) :
    (∃ f g : YF n, f ∈ spanY ys ∧ g ∈ spanY ys ∧
      ∀ w ∈ stock ++ [h], Rep a φc (ys ++ [fun t u => f t u * g t u]) w) ∨
    (∃ (lam : X n) (p : YF n), lam ∉ Submodule.span F (Set.range a) ∧ p ∈ spanY ys ∧
      ∀ σ : F, ∀ w ∈ stock ++ [h], Rep (Fin.cons lam a : Fin (j+1) → X n)
        (Fin.cons (fun t u => σ + p t u) φc : Fin (j+1) → YF n) ys w) := by
  obtain ⟨lP,pP,mP,eP⟩ := hP
  obtain ⟨lQ,pQ,mQ,eQ⟩ := hQ
  by_cases inP : lP ∈ Submodule.span F (Set.range a)
  · by_cases inQ : lQ ∈ Submodule.span F (Set.range a)
    · left
      obtain ⟨f, mf, ef⟩ := rep_reduce inside lP pP mP eP inP
      obtain ⟨g, mg, eg⟩ := rep_reduce inside lQ pQ mQ eQ inQ
      refine ⟨f, g, mf, mg, fun w mem => ?_⟩
      rcases List.mem_append.mp mem with old | new
      · exact rep_mono_ys _ (reps w old)
      · obtain rfl : w = h := by simpa using new
        obtain ⟨l,p,m,e⟩ := hW
        refine ⟨l, (fun t u => f t u * g t u) + p,
          Submodule.add_mem _ (spanY_new ys _) (spanY_mono ys _ m), fun t x u leaf => ?_⟩
        rw [eq, ef t x u leaf, eg t x u leaf, e t x u leaf]
        simp only [Pi.add_apply]
        ring
    · right
      refine ⟨lQ, pQ, inQ, mQ, fun σ => ?_⟩
      exact split_reps stock reps Q P W h ⟨lP,pP,mP,eP⟩ hW
        (fun t v => by rw [eq, mul_comm]) lQ pQ eQ σ
  · right
    refine ⟨lP, pP, inP, mP, fun σ => ?_⟩
    exact split_reps stock reps P Q W h ⟨lQ,pQ,mQ,eQ⟩ hW eq lP pP eP σ

open Classical in

noncomputable def Lsum {j : ℕ} (a : Fin j → X n) (φc : Fin j → YF n) (Q : Bool → U n → F)
    (out : Bool → X n × U n → F) (t : Bool) : ℤ :=
  ∑ x : X n, ∑ u : U n,
    if Leaf a φc t x u then character (out t (x,u) + (x ⬝ᵥ yv n t u + Q t u)) else 0

theorem lsum_congr (Q : Bool → U n → F) (out out' : Bool → X n × U n → F) (t : Bool)
    (same : ∀ x u, Leaf a φc t x u → out t (x,u) = out' t (x,u)) :
    Lsum a φc Q out t = Lsum a φc Q out' t := by
  unfold Lsum
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro u _
  split
  · rw [same x u ‹_›]
  · rfl

theorem lsum_split (Q : Bool → U n → F) (out : Bool → X n × U n → F) (t : Bool)
    (l : X n) (p : YF n) :
    Lsum a φc Q out t =
      Lsum (Fin.cons l a : Fin (j+1) → X n)
        (Fin.cons (fun t u => 0 + p t u) φc : Fin (j+1) → YF n) Q out t +
      Lsum (Fin.cons l a : Fin (j+1) → X n)
        (Fin.cons (fun t u => 1 + p t u) φc : Fin (j+1) → YF n) Q out t := by
  classical
  unfold Lsum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  simp only [leaf_cons]
  have two : ∀ v q : F, (v = 0 + q ∧ ¬ v = 1 + q) ∨ (¬ v = 0 + q ∧ v = 1 + q) := by decide
  by_cases leaf : Leaf a φc t x u
  · rcases two (l ⬝ᵥ x) (p t u) with ⟨yes, no⟩ | ⟨no, yes⟩
    · simp [leaf, yes, no]
    · simp [leaf, yes, no]
  · simp [leaf]

theorem character_sum {I : Type*} (s : Finset I) (f : I → F) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [character]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, character_add, ih]

theorem leaf_indicator (a : Fin j → X n) (φc : Fin j → YF n) (t : Bool) (x : X n) (u : U n)
    [Decidable (Leaf a φc t x u)] :
    (2 : ℤ) ^ j * (if Leaf a φc t x u then 1 else 0) =
      ∑ τ : Fin j → F, character (∑ i, τ i * (a i ⬝ᵥ x + φc i t u)) := by
  classical
  have one : ∀ z : F, (∑ b : F, character (b * z)) = if z = 0 then 2 else 0 := by decide
  have same : ∀ p q : F, p + q = 0 ↔ p = q := by decide
  have expand := Finset.prod_univ_sum (fun _ : Fin j => (Finset.univ : Finset F))
    (fun i b => character (b * (a i ⬝ᵥ x + φc i t u)))
  rw [Fintype.piFinset_univ] at expand
  simp only [character_sum]
  rw [← expand]
  simp only [one, Finset.prod_ite_zero, Finset.mem_univ, forall_true_left, same,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  by_cases leaf : Leaf a φc t x u
  · rw [if_pos leaf, if_pos (fun i => leaf i), mul_one]
  · rw [if_neg leaf, if_neg (fun all => leaf fun i => all i), mul_zero]

def dotL (n : ℕ) (w : X n) : X n × U n →+ F :=
  AddMonoidHom.mk' (fun v => w ⬝ᵥ v.1) (fun p q => by simp [dotProduct_add])

theorem base_small (a : Fin j → X n) (φc : Fin j → YF n) (Q : Bool → U n → F)
    (lam : X n) (φ : YF n) :
    |Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) false| +
      |Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) true| ≤ 2 ^ (n+1) := by
  classical
  let D : (Fin j → F) → Bool → ℤ := fun τ t => ∑ x : X n, ∑ u : U n,
    character (dotL n ((∑ i, τ i • a i) + lam) (x,u) + (fun _ : Bool => (0 : F)) t) *
      character (x ⬝ᵥ yv n t u + ((∑ i, τ i * φc i t u) + φ t u + Q t u))
  have expand (t : Bool) :
      2 ^ j * Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) t = ∑ τ, D τ t := by
    simp only [D, Lsum]
    rw [Finset.mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    have ind := leaf_indicator a φc t x u
    have move : (2 : ℤ) ^ j * (if Leaf a φc t x u then
        character (lam ⬝ᵥ x + φ t u + (x ⬝ᵥ yv n t u + Q t u)) else 0) =
        (2 ^ j * (if Leaf a φc t x u then 1 else 0)) *
          character (lam ⬝ᵥ x + φ t u + (x ⬝ᵥ yv n t u + Q t u)) := by
      split <;> ring
    rw [move, ind, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro τ _
    rw [← character_add, ← character_add]
    congr 1
    simp only [dotL, AddMonoidHom.mk'_apply, add_dotProduct, sum_dotProduct, smul_dotProduct,
      smul_eq_mul, mul_add, Finset.sum_add_distrib]
    ring
  have each (τ : Fin j → F) : |D τ false| + |D τ true| ≤ 2 ^ (n+1) := by
    have d := diag n (dotL n ((∑ i, τ i • a i) + lam)) (fun _ => 0)
      (fun t u => (∑ i, τ i * φc i t u) + φ t u + Q t u)
    rw [Fintype.sum_bool] at d
    linarith
  have bound (t : Bool) :
      2 ^ j * |Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) t| ≤ ∑ τ, |D τ t| := by
    have pos : (0 : ℤ) ≤ 2 ^ j := by positivity
    rw [← abs_of_nonneg pos, ← abs_mul, expand]
    exact Finset.abs_sum_le_sum_abs _ _
  have sum : 2 ^ j * (|Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) false| +
      |Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) true|) ≤ 2 ^ j * 2 ^ (n+1) := by
    calc
      _ ≤ ∑ τ : Fin j → F, (|D τ false| + |D τ true|) := by
        rw [mul_add, Finset.sum_add_distrib]
        exact add_le_add (bound false) (bound true)
      _ ≤ ∑ _τ : Fin j → F, (2 : ℤ) ^ (n+1) := Finset.sum_le_sum fun τ _ => each τ
      _ = _ := by simp
  exact le_of_mul_le_mul_left sum (by positivity)

end Elim

section ElimMain
variable {n : ℕ}

theorem paid_form (stock : List (Bool → X n × U n → F)) (g : Gate) (pay : paid g) :
    ∃ P Q W : Bool → X n × U n → F, P ∈ Submodule.span F (gens stock) ∧
      Q ∈ Submodule.span F (gens stock) ∧ W ∈ Submodule.span F (gens stock) ∧
      ∀ t v, run g stock t v = P t v * Q t v + W t v := by
  rcases g with ⟨op, args⟩
  obtain ⟨hop, len⟩ := pay
  change op = .and ∨ op = .or at hop
  change args.length = 2 at len
  obtain ⟨i1, i2, rfl⟩ := List.length_eq_two.mp len
  rcases hop with rfl | rfl
  · exact ⟨read stock i1, read stock i2, 0, read_mem stock i1, read_mem stock i2,
      Submodule.zero_mem _, fun t v => by rw [eval_binary_and]; simp⟩
  · exact ⟨read stock i1, read stock i2, fun t v => read stock i1 t v + read stock i2 t v,
      read_mem stock i1, read_mem stock i2, add_mem' (read_mem stock i1) (read_mem stock i2),
      fun t v => by rw [eval_binary_or]; ring⟩

theorem spanY_shift (ys : List (YF n)) (σ : F) (p : YF n) (mp : p ∈ spanY ys) :
    (fun t u => σ + p t u) ∈ spanY ys :=
  Submodule.add_mem _ (spanY_const ys fun _ => σ) mp

theorem cons_inside {j : ℕ} {φc : Fin j → YF n} {ys : List (YF n)}
    (inside : ∀ i, φc i ∈ spanY ys) (q : YF n) (h0 : q ∈ spanY ys) :
    ∀ i, (Fin.cons q φc : Fin (j+1) → YF n) i ∈ spanY ys := by
  intro i
  refine Fin.cases ?_ (fun i' => ?_) i
  · rw [Fin.cons_zero]
    exact h0
  · rw [Fin.cons_succ]
    exact inside i'

theorem elim (r : ℕ) (Q : Bool → U n → F)
    (full : ∀ (c : ℕ) (a : Fin (n+1) → X n) (φc : Fin (n+1) → YF n) (ys : List (YF n))
      (lam : X n) (φ : YF n),
      LinearIndependent F a → YStock c ys → (∀ i, φc i ∈ spanY ys) → φ ∈ spanY ys →
      2 ^ (r - c) * (|Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) false| +
        |Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) true|) ≤ (2 ^ (r - c) + 1) * 2 ^ n)
    (tape : List Gate) :
    ∀ (j c : ℕ) (a : Fin j → X n) (φc : Fin j → YF n) (ys : List (YF n))
      (stock : List (Bool → X n × U n → F)),
      LinearIndependent F a → YStock c ys → (∀ i, φc i ∈ spanY ys) →
      (∀ f ∈ stock, Rep a φc ys f) → (∀ g ∈ tape, allowed g) →
      ∀ out ∈ Submodule.span F (gens (wires tape stock)),
      2 ^ (r - (c + price tape - (n+1-j))) *
          (|Lsum a φc Q out false| + |Lsum a φc Q out true|) ≤
        (2 ^ (r - (c + price tape - (n+1-j))) + 1) * 2 ^ (2*n+1-j) := by
  induction tape with
  | nil =>
    intro j c a φc ys stock ind ystock inside reps _ out hout
    have depth : j ≤ n+1 := by
      have card := ind.fintype_card_le_finrank
      simpa using card
    obtain ⟨lam, φ, mφ, e⟩ := rep_span stock reps out hout
    have same (t : Bool) :
        Lsum a φc Q out t = Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) t :=
      lsum_congr Q _ _ t (fun x u leaf => e t x u leaf)
    rw [same false, same true]
    have p0 : price ([] : List Gate) = 0 := by simp [price]
    rw [p0]
    by_cases top : j = n+1
    · subst top
      have bound := full c a φc ys lam φ ind ystock inside mφ
      have e1 : c + 0 - (n+1-(n+1)) = c := by omega
      have e2 : 2*n+1-(n+1) = n := by omega
      rw [e1, e2]
      exact bound
    · have small := base_small a φc Q lam φ
      have le : (2 : ℤ) ^ (n+1) ≤ 2 ^ (2*n+1-j) := pow_le_pow_right₀ (by norm_num) (by omega)
      have pos : (0 : ℤ) ≤ 2 ^ (r - (c + 0 - (n+1-j))) := by positivity
      have posB : (0 : ℤ) ≤ 2 ^ (2*n+1-j) := by positivity
      calc
        _ ≤ 2 ^ (r - (c + 0 - (n+1-j))) * 2 ^ (2*n+1-j) :=
          mul_le_mul_of_nonneg_left (small.trans le) pos
        _ ≤ _ := by
          rw [add_mul, one_mul]
          linarith
  | cons g tape ih =>
    intro j c a φc ys stock ind ystock inside reps ok out hout
    have rest : ∀ h ∈ tape, allowed h := fun h mem => ok h (List.mem_cons_of_mem _ mem)
    have okg := ok g (List.mem_cons_self ..)
    change out ∈ Submodule.span F (gens (wires tape (stock ++ [run g stock]))) at hout
    by_cases pay : paid g
    · have count : price (g :: tape) = price tape + 1 := by simp [price, pay]
      rw [count]
      obtain ⟨P, Q', W, hP, hQ, hW, eq⟩ := paid_form stock g pay
      rcases paid_cases stock reps inside P Q' W (run g stock) (rep_span stock reps P hP)
        (rep_span stock reps Q' hQ) (rep_span stock reps W hW) eq with
        ⟨f, g', mf, mg, reps'⟩ | ⟨lam, p, notin, mp, reps'⟩
      · have next := ih j (c+1) a φc _ _ ind (YStock.snoc c ys f g' ystock mf mg)
          (fun i => spanY_mono ys _ (inside i)) reps' rest out hout
        have e : c + (price tape + 1) - (n+1-j) = c + 1 + price tape - (n+1-j) := by omega
        rw [e]
        exact next
      · have ind' : LinearIndependent F (Fin.cons lam a : Fin (j+1) → X n) :=
          linearIndependent_finCons.mpr ⟨ind, notin⟩
        have depth : j + 1 ≤ n+1 := by
          have card := ind'.fintype_card_le_finrank
          simpa using card
        have child (σ : F) := ih (j+1) c (Fin.cons lam a) (Fin.cons (fun t u => σ + p t u) φc)
          ys _ ind' ystock (cons_inside inside _ (spanY_shift ys σ p mp)) (reps' σ) rest out hout
        have c0 := child 0
        have c1 := child 1
        have e : c + (price tape + 1) - (n+1-j) = c + price tape - (n+1-(j+1)) := by omega
        have e2 : 2*n+1-j = (2*n+1-(j+1)) + 1 := by omega
        rw [e, e2, pow_succ, lsum_split Q out false lam p, lsum_split Q out true lam p]
        have pos : (0 : ℤ) ≤ 2 ^ (r - (c + price tape - (n+1-(j+1)))) := by positivity
        have tri := add_le_add (abs_add_le
          (Lsum (Fin.cons lam a : Fin (j+1) → X n)
            (Fin.cons (fun t u => 0 + p t u) φc : Fin (j+1) → YF n) Q out false)
          (Lsum (Fin.cons lam a : Fin (j+1) → X n)
            (Fin.cons (fun t u => 1 + p t u) φc : Fin (j+1) → YF n) Q out false))
          (abs_add_le
          (Lsum (Fin.cons lam a : Fin (j+1) → X n)
            (Fin.cons (fun t u => 0 + p t u) φc : Fin (j+1) → YF n) Q out true)
          (Lsum (Fin.cons lam a : Fin (j+1) → X n)
            (Fin.cons (fun t u => 1 + p t u) φc : Fin (j+1) → YF n) Q out true))
        have scaled := mul_le_mul_of_nonneg_left tri pos
        linarith
    · have count : price (g :: tape) = price tape := by simp [price, pay]
      rw [count]
      have hmem := free_mem g stock okg.1 okg.2 pay
      refine ih j c a φc ys _ ind ystock inside ?_ rest out hout
      intro f mem
      rcases List.mem_append.mp mem with old | new
      · exact reps f old
      · obtain rfl : f = run g stock := by simpa using new
        exact rep_span stock reps _ hmem

theorem base_reps (n : ℕ) :
    ∀ f ∈ base n, Rep (Fin.elim0 : Fin 0 → X n) (Fin.elim0 : Fin 0 → YF n) [] f := by
  intro f mem
  rcases List.mem_append.mp mem with m | m
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp m
    exact ⟨Pi.single i 1, 0, Submodule.zero_mem _, fun t x u _ => by simp⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp m
    refine Fin.cases ?_ (fun i' => ?_) i
    · exact ⟨0, fun t _ => if t then 1 else 0, spanY_const _ _, fun t x u _ => by simp [yv]⟩
    · exact ⟨0, fun _ u => u i', Submodule.subset_span (Or.inr ⟨fun _ => 0, LinearMap.proj i',
        fun t u => by simp⟩), fun t x u _ => by simp [yv]⟩

theorem root (r : ℕ) (Q : Bool → U n → F)
    (full : ∀ (c : ℕ) (a : Fin (n+1) → X n) (φc : Fin (n+1) → YF n) (ys : List (YF n))
      (lam : X n) (φ : YF n),
      LinearIndependent F a → YStock c ys → (∀ i, φc i ∈ spanY ys) → φ ∈ spanY ys →
      2 ^ (r - c) * (|Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) false| +
        |Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) true|) ≤ (2 ^ (r - c) + 1) * 2 ^ n)
    (C : Circuit) (ok : ∀ g ∈ C.gates, allowed g) :
    2 ^ (r - (price C.gates - (n+1))) * (|num n Q C false| + |num n Q C true|) ≤
      (2 ^ (r - (price C.gates - (n+1))) + 1) * 2 ^ (2*n+1) := by
  have h := elim r Q full C.gates 0 0 Fin.elim0 Fin.elim0 [] (base n)
    linearIndependent_empty_type YStock.nil (fun i => i.elim0) (base_reps n) ok _
    (read_mem (wires C.gates (base n)) C.output)
  have eqn (t : Bool) : Lsum (Fin.elim0 : Fin 0 → X n) (Fin.elim0 : Fin 0 → YF n) Q
      (read (wires C.gates (base n)) C.output) t = num n Q C t := by
    unfold Lsum num
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro u _
    have leaf : Leaf (Fin.elim0 : Fin 0 → X n) (Fin.elim0 : Fin 0 → YF n) t x u :=
      fun i => i.elim0
    rw [if_pos leaf, output_value, agree_character]
  simpa [eqn] using h

end ElimMain

section Full
open Quadratic29947Polar Quadratic29947Restriction Quadratic29947Transport Quadratic29947Chart
open Quadratic29947Coordinates
open Quadratic29947Affine (paired)
variable {n : ℕ}

def pullY (C : Chart n) (f : YF n) : Bool → Inputs C.dim → ZMod 2 :=
  fun t x => f t (point C t x)

theorem span_paired (C : Chart n) (ys : List (YF n)) (h : ∀ f ∈ ys, paired (pullY C f)) :
    ∀ f ∈ spanY ys, paired (pullY C f) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with m | ⟨b, L, eq⟩
    · exact h f m
    · refine ⟨fun t => b t + L (C.origin t), L.comp C.move, fun t x => ?_⟩
      simp only [pullY, point, eq, map_add, LinearMap.comp_apply]
      ring
  | zero => exact Quadratic29947Affine.constant fun _ => 0
  | add f g _ _ hf hg => exact Quadratic29947Affine.plus hf hg
  | smul c f _ hf => exact Quadratic29947Affine.scale c hf

def Covers (C : Chart n) (leaves : List (Chart n)) : Prop :=
  ∀ (t : Bool) (weight : Inputs n → ℤ),
    (∑ x, weight (point C t x)) = (leaves.map fun leaf => ∑ z, weight (point leaf t z)).sum

theorem refine_list (good : Chart n → Prop) : ∀ leaves : List (Chart n),
    (∀ D ∈ leaves, ∃ sub : List (Chart n), Covers D sub ∧
      ∀ E ∈ sub, D.dim ≤ E.dim + 1 ∧ good E) →
    ∃ out : List (Chart n),
      (∀ (t : Bool) (w : Inputs n → ℤ), (out.map fun E => ∑ z, w (point E t z)).sum =
        (leaves.map fun D => ∑ z, w (point D t z)).sum) ∧
      ∀ E ∈ out, ∃ D ∈ leaves, D.dim ≤ E.dim + 1 ∧ good E := by
  intro leaves
  induction leaves with
  | nil =>
    intro _
    exact ⟨[], fun _ _ => rfl, fun E hE => by simp at hE⟩
  | cons D rest ih =>
    intro h
    obtain ⟨sub, cover, goodSub⟩ := h D (List.mem_cons_self ..)
    obtain ⟨out, sums, goodOut⟩ := ih (fun D' m => h D' (List.mem_cons_of_mem _ m))
    refine ⟨sub ++ out, fun t w => ?_, fun E hE => ?_⟩
    · rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons, sums t w, ← cover t w]
    · rcases List.mem_append.mp hE with m | m
      · exact ⟨D, List.mem_cons_self .., goodSub E m⟩
      · obtain ⟨D', mD', g⟩ := goodOut E m
        exact ⟨D', List.mem_cons_of_mem _ mD', g⟩

theorem ypartition {c : ℕ} {ys : List (YF n)} (st : YStock c ys) (C : Chart n) :
    ∃ leaves : List (Chart n), Covers C leaves ∧
      ∀ D ∈ leaves, C.dim ≤ D.dim + c ∧ ∀ f ∈ ys, paired (pullY D f) := by
  induction st with
  | nil =>
    refine ⟨[C], fun t w => by simp, fun D hD => ?_⟩
    rw [List.mem_singleton] at hD
    subst hD
    exact ⟨by omega, fun f hf => by simp at hf⟩
  | snoc c ys f g _ hf hg ih =>
    obtain ⟨leaves, cover, each⟩ := ih
    obtain ⟨out, sums, goodOut⟩ := refine_list
      (fun E => ∀ f' ∈ ys ++ [fun t u => f t u * g t u], paired (pullY E f')) leaves (by
        intro D hD
        obtain ⟨_, old⟩ := each D hD
        have pf := span_paired D ys old f hf
        have pg := span_paired D ys old g hg
        rcases Quadratic29947Affine.binary_step (pullY D f) (pullY D g) pf pg with
          ok | ⟨L, p, unit, b, split⟩
        · refine ⟨[D], fun t w => by simp, fun E hE => ?_⟩
          rw [List.mem_singleton] at hE
          subst hE
          refine ⟨by omega, fun f' m => ?_⟩
          rcases List.mem_append.mp m with o | nw
          · exact old f' o
          · rw [List.mem_singleton] at nw
            subst nw
            exact ok.1
        · have key (a : ZMod 2) : (child D L p b a).dim + 1 = D.dim ∧
              ∀ f' ∈ ys ++ [fun t u => f t u * g t u], paired (pullY (child D L p b a) f') := by
            refine ⟨child_dimension D L p unit b a, fun f' m => ?_⟩
            rcases List.mem_append.mp m with o | nw
            · exact child_affine D L p unit b a f' (old f' o)
            · rw [List.mem_singleton] at nw
              subst nw
              obtain ⟨bias, part, same⟩ := (split a).1
              refine ⟨bias, part.comp (kernelBasis L).toLinearMap, ?_⟩
              intro t z
              simp only [pullY, child_point D L p unit b, LinearMap.comp_apply,
                LinearEquiv.coe_coe]
              exact same t (kernelBasis L z)
          refine ⟨[child D L p b 0, child D L p b 1], fun t w => ?_, fun E hE => ?_⟩
          · rw [child_sum D L p unit b t w]
            have casesF : (Finset.univ : Finset (ZMod 2)) = {0,1} := by decide
            rw [casesF, Finset.sum_insert (by decide), Finset.sum_singleton]
            simp
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
            rcases hE with rfl | rfl
            · exact ⟨by have := (key 0).1; omega, (key 0).2⟩
            · exact ⟨by have := (key 1).1; omega, (key 1).2⟩)
    refine ⟨out, fun t w => (cover t w).trans (sums t w).symm, fun E hE => ?_⟩
    obtain ⟨D, hD, dim, good⟩ := goodOut E hE
    exact ⟨by have := (each D hD).1; omega, fun f' m => good f' m⟩

private theorem index_sum {A : Type*} (xs : List A) (f : A → ℤ) :
    (∑ i : Fin xs.length, f xs[i]) = (xs.map f).sum := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map xs f)

theorem tap_upper (r c : ℕ) (Q : Bool → Inputs n → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (shape : ∀ t, Quadratic29947Literal.quad (Q t)) (rank : M.rank = 2*r)
    (polarEntries : ∀ x y, polar (fun u => Q false u + Q true u) x y = dotProduct x (M.mulVec y))
    {ys : List (YF n)} (st : YStock c ys) {m : ℕ} (Φ0 : YF n) (h0 : Φ0 ∈ spanY ys)
    (ℓ φ : Fin m → YF n) (hℓ : ∀ k, ℓ k ∈ PA n) (hφ : ∀ k, φ k ∈ spanY ys) :
    2 ^ (r-c) *
      (|∑ u, character (Q false u + (Φ0 false u + ∑ k, ℓ k false u * φ k false u))| +
       |∑ u, character (Q true u + (Φ0 true u + ∑ k, ℓ k true u * φ k true u))|) ≤
      (2 ^ (r-c) + 1) * 2 ^ n := by
  let G : YF n := fun t u => Φ0 t u + ∑ k, ℓ k t u * φ k t u
  obtain ⟨leaves, cover, each⟩ := ypartition st (initial n)
  let mass (i : Fin leaves.length) : ℤ := Fintype.card (Inputs (leaves[i]).dim)
  let part (t : Bool) (i : Fin leaves.length) : ℤ :=
    ∑ z, character (Q t (point leaves[i] t z) + G t (point leaves[i] t z))
  have total : ∑ i, mass i = 2 ^ n := by
    calc
      _ = ((leaves.map fun C => (Fintype.card (Inputs C.dim) : ℤ)).sum) := index_sum leaves _
      _ = ∑ x : Inputs n, (1 : ℤ) := by
        have h := cover false (fun _ => (1 : ℤ))
        change (∑ x : Inputs n, (1 : ℤ)) =
          (leaves.map fun C => ∑ z : Inputs C.dim, (1 : ℤ)).sum at h
        have massEq (C : Chart n) :
            (∑ z : Inputs C.dim, (1 : ℤ)) = (Fintype.card (Inputs C.dim) : ℤ) := by simp
        simp only [massEq] at h
        exact h.symm
      _ = _ := by simp [Inputs,Fintype.card_fun,ZMod.card]
  have decompose (t : Bool) : (∑ u, character (Q t u + G t u)) = ∑ i, part t i := by
    let f := fun u => character (Q t u + G t u)
    have source : (∑ x : Inputs n, f x) = ∑ x, f (point (initial n) t x) := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg f (initial_point n t x).symm
    exact source.trans ((cover t f).trans (index_sum leaves _).symm)
  change 2 ^ (r-c) * (|∑ u, character (Q false u + G false u)| +
    |∑ u, character (Q true u + G true u)|) ≤ _
  rw [decompose false,decompose true]
  apply combine_leaves (part false) (part true) mass (r-c) n total
  intro i
  let C := leaves[i]
  obtain ⟨codim,affine⟩ := each C (List.getElem_mem i.isLt)
  have fits : n - C.dim ≤ c := by
    change n ≤ C.dim + c at codim
    omega
  have allP := span_paired C ys affine
  have common : ∀ x y, polar (pullY C G false) x y = polar (pullY C G true) x y := by
    intro x y
    choose b L dy using fun k => allP (ℓ k) (Submodule.subset_span (Or.inr (hℓ k)))
    choose c' P dv using fun k => allP (φ k) (hφ k)
    let A := pullY C Φ0
    have off : ∀ t, ∃ (k : ZMod 2) (T : Inputs C.dim →ₗ[ZMod 2] ZMod 2),
        ∀ v, A t v = k + T v := by
      obtain ⟨start,T,eq⟩ := allP Φ0 h0
      exact fun t => ⟨start t,T,eq t⟩
    have terms (t : Bool) : pullY C G t =
        fun u => A t u + ∑ i, (b i t + L i u) * (c' i t + P i u) := by
      funext u
      change A t u + ∑ i, pullY C (ℓ i) t u * pullY C (φ i) t u = _
      simp only [dy,dv]
    rw [terms false,terms true]
    exact common_polar Finset.univ L P (fun t i => b i t) (fun t i => c' i t) A off x y
  have localBound := transported_leaf n r c C.dim M (matrix C)
    (matrix_rank C) rank fits Q C.origin (pullY C G)
    (fun t => Quadratic29947Literal.shift_invariant (Q t) (shape t) (C.origin t))
    common polarEntries
  change 2 ^ (r-c) * (|part false i| + |part true i|) ≤ (2 ^ (r-c) + 1) * mass i
  simpa only [part,mass,pullY,point,matrix_point,C] using localBound

def quadP {n : ℕ} (q : U n → F) : Prop :=
  ∃ (b : F) (a : U n) (M : Fin n → Fin n → F), ∀ v,
    q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j

theorem base_full (r : ℕ) (Q : Bool → U n → F) (M : Matrix (Fin n) (Fin n) F)
    (shape : ∀ t, quadP (Q t)) (rank : M.rank = 2*r)
    (hpolar : ∀ u v : U n, (Q false (u+v) + Q true (u+v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v))
    (c : ℕ) (a : Fin (n+1) → X n) (φc : Fin (n+1) → YF n) (ys : List (YF n))
    (lam : X n) (φ : YF n)
    (ind : LinearIndependent F a) (st : YStock c ys) (inside : ∀ i, φc i ∈ spanY ys)
    (mφ : φ ∈ spanY ys) :
    2 ^ (r - c) * (|Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) false| +
      |Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) true|) ≤ (2 ^ (r - c) + 1) * 2 ^ n := by
  classical
  let A : Matrix (Fin (n+1)) (Fin (n+1)) F := Matrix.of a
  have unitA : IsUnit A := Matrix.linearIndependent_row_iff_isUnit.mp ind
  have det := (Matrix.isUnit_iff_isUnit_det A).mp unitA
  have inv1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A det
  have inv2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A det
  have leafIff (t : Bool) (x : X n) (u : U n) :
      Leaf a φc t x u ↔ x = A⁻¹.mulVec (fun i => φc i t u) := by
    constructor
    · intro leaf
      have eq : A.mulVec x = fun i => φc i t u := funext leaf
      rw [← eq, Matrix.mulVec_mulVec, inv2, Matrix.one_mulVec]
    · intro hx i
      have eq : A.mulVec x = fun i => φc i t u := by
        rw [hx, Matrix.mulVec_mulVec, inv1, Matrix.one_mulVec]
      exact congrFun eq i
  let ℓ : Fin (n+1) → YF n := fun k t u => (Matrix.vecMul (yv n t u) A⁻¹) k
  let Φ0 : YF n := φ + ∑ k, (Matrix.vecMul lam A⁻¹ k) • φc k
  have value (t : Bool) : Lsum a φc Q (fun t v => lam ⬝ᵥ v.1 + φ t v.2) t =
      ∑ u, character (Q t u + (Φ0 t u + ∑ k, ℓ k t u * φc k t u)) := by
    unfold Lsum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    simp only [leafIff]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    congr 1
    rw [Matrix.dotProduct_mulVec, dotProduct_comm (A⁻¹.mulVec _) (yv n t u),
      Matrix.dotProduct_mulVec]
    simp only [Φ0, ℓ, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct]
    ring
  rw [value false, value true]
  refine tap_upper r c Q M shape rank hpolar st Φ0 ?_ ℓ φc ?_ inside
  · exact Submodule.add_mem _ mφ
      (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (inside k))
  · intro k
    refine ⟨fun t => (if t then 1 else 0) * A⁻¹ 0 k,
      ∑ j : Fin n, (A⁻¹ j.succ k) • LinearMap.proj j, fun t u => ?_⟩
    simp only [ℓ, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, yv, Fin.cons_zero, Fin.cons_succ,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

end Full

def legal (m : ℕ) (C : Circuit) : Prop :=
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C ∧
    (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))

def score (n : ℕ) (Q : Bool → U n → F) (C : Circuit) (t : Bool) : ℚ :=
  (∑ x : X n, ∑ u : U n,
    if C.eval (bits (n+1) x ++ bits (n+1) (yv n t u)) = decide (x ⬝ᵥ yv n t u + Q t u = 1)
    then (1 : ℚ) else -1) / 2 ^ (n+1+n)

def rho (n s : ℕ) : ℚ := if s < n+1 then 1 / 2 ^ (n-s) else 1

def total (n r s : ℕ) : ℚ := if s < n+1 then rho n s else 1 + 1 / 2 ^ (r-(s-(n+1)))

theorem score_num (n : ℕ) (Q : Bool → U n → F) (C : Circuit) (t : Bool) :
    score n Q C t = (num n Q C t : ℚ) / 2 ^ (n+1+n) := by
  simp only [score, num]
  push_cast
  rfl

theorem num_abs (n : ℕ) (Q : Bool → U n → F) (C : Circuit) (t : Bool) :
    |num n Q C t| ≤ 2 ^ (n+1+n) := by
  unfold num
  calc
    _ ≤ ∑ x : X n, ∑ u : U n, (1 : ℤ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      split <;> simp
    _ = _ := by
      simp [X, U, pow_add]

theorem score_abs (n : ℕ) (Q : Bool → U n → F) (C : Circuit) (t : Bool) :
    |score n Q C t| ≤ 1 := by
  rw [score_num, abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ (n+1+n)),
    div_le_one (by positivity)]
  exact_mod_cast num_abs n Q C t

theorem upper_small (n s : ℕ) (Q : Bool → U n → F) (C : Circuit)
    (ok : legal (2*(n+1)) C) (cheap : price C.gates ≤ s) :
    |score n Q C false| + |score n Q C true| ≤ 2 ^ s / 2 ^ n := by
  have ints := upper_num n Q C ok.2
  have mono : (2 : ℤ) ^ (price C.gates + (n+1)) ≤ 2 ^ (s + (n+1)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have rat : ((|num n Q C false| + |num n Q C true| : ℤ) : ℚ) ≤ ((2 ^ (s + (n+1)) : ℤ) : ℚ) :=
    Int.cast_le.mpr (ints.trans mono)
  push_cast at rat
  rw [score_num, score_num, abs_div, abs_div,
    abs_of_pos (by positivity : (0 : ℚ) < 2 ^ (n+1+n)), ← add_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    _ ≤ (2 : ℚ) ^ (s + (n+1)) * 2 ^ n := by gcongr
    _ = _ := by ring

theorem upper_large (n r s : ℕ) (Q : Bool → U n → F) (M : Matrix (Fin n) (Fin n) F)
    (shape : ∀ t, quadP (Q t)) (rank : M.rank = 2*r)
    (polar : ∀ u v : U n, (Q false (u+v) + Q true (u+v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v))
    (C : Circuit) (ok : legal (2*(n+1)) C) (cheap : price C.gates ≤ s) :
    |score n Q C false| + |score n Q C true| ≤ 1 + 1 / 2 ^ (r-(s-(n+1))) := by
  have ints := root r Q (fun c a φc ys lam φ ind st inside mφ =>
    base_full r Q M shape rank polar c a φc ys lam φ ind st inside mφ) C ok.2
  have hE : r - (s - (n+1)) ≤ r - (price C.gates - (n+1)) := by omega
  generalize r - (price C.gates - (n+1)) = E at ints hE
  have rat : ((2 : ℚ) ^ E) * (|(num n Q C false : ℚ)| + |(num n Q C true : ℚ)|) ≤
      (2 ^ E + 1) * 2 ^ (2*n+1) := by exact_mod_cast ints
  have pos : (0 : ℚ) < 2 ^ E := by positivity
  have h3 : (2 : ℚ) ^ (2*n+1) = 2 ^ (n+1+n) := by
    congr 1
    omega
  have h2 : (1 : ℚ) / 2 ^ E ≤ 1 / 2 ^ (r-(s-(n+1))) :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hE)
  have h1 : |(num n Q C false : ℚ)| + |(num n Q C true : ℚ)| ≤
      (1 + 1 / 2 ^ E) * 2 ^ (2*n+1) := by
    refine le_of_mul_le_mul_left ?_ pos
    calc
      _ ≤ ((2 : ℚ) ^ E + 1) * 2 ^ (2*n+1) := rat
      _ = _ := by field_simp
  rw [score_num, score_num, abs_div, abs_div,
    abs_of_pos (by positivity : (0 : ℚ) < 2 ^ (n+1+n)), ← add_div,
    div_le_iff₀ (by positivity), ← h3]
  calc
    _ ≤ (1 + 1 / 2 ^ E) * (2 : ℚ) ^ (2*n+1) := h1
    _ ≤ _ := by gcongr

theorem single (n r s : ℕ) (Q : Bool → U n → F) (M : Matrix (Fin n) (Fin n) F)
    (shape : ∀ t, quadP (Q t)) (rank : M.rank = 2*r)
    (polar : ∀ u v : U n, (Q false (u+v) + Q true (u+v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v))
    (C : Circuit) (ok : legal (2*(n+1)) C) (cheap : price C.gates ≤ s) :
    (∀ t, |score n Q C t| ≤ rho n s) ∧
      |score n Q C false| + |score n Q C true| ≤ total n r s := by
  by_cases hs : s < n+1
  · have small := upper_small n s Q C ok cheap
    have eq : (2 : ℚ) ^ s / 2 ^ n = 1 / 2 ^ (n-s) := by
      have split : (2 : ℚ) ^ n = 2 ^ (n-s) * 2 ^ s := by
        rw [← pow_add]
        congr 1
        omega
      rw [split]
      field_simp
    rw [eq] at small
    simp only [rho, total, if_pos hs]
    refine ⟨fun t => ?_, small⟩
    have nonneg := abs_nonneg (score n Q C false)
    have nonneg' := abs_nonneg (score n Q C true)
    cases t <;> linarith
  · simp only [rho, total, if_neg hs]
    exact ⟨fun t => score_abs n Q C t,
      upper_large n r s Q M shape rank polar C ok cheap⟩

theorem mix (p a b : Fin 3 → ℚ) (R T : ℚ) (pos : ∀ i, 0 ≤ p i) (one : (∑ i, p i) = 1)
    (ha : ∀ i, |a i| ≤ R) (hb : ∀ i, |b i| ≤ R) (hab : ∀ i, |a i| + |b i| ≤ T) :
    |∑ i, p i * a i| ≤ R ∧ |∑ i, p i * b i| ≤ R ∧
      |∑ i, p i * a i| + |∑ i, p i * b i| ≤ T := by
  have tri (c : Fin 3 → ℚ) : |∑ i, p i * c i| ≤ ∑ i, p i * |c i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_mul, abs_of_nonneg (pos i)]
  have cap (c : Fin 3 → ℚ) (B : ℚ) (h : ∀ i, c i ≤ B) : ∑ i, p i * c i ≤ B := by
    calc
      _ ≤ ∑ i, p i * B := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (pos i)
      _ = B := by rw [← Finset.sum_mul, one, one_mul]
  refine ⟨(tri a).trans (cap _ R ha), (tri b).trans (cap _ R hb), ?_⟩
  calc
    _ ≤ ∑ i, p i * |a i| + ∑ i, p i * |b i| := add_le_add (tri a) (tri b)
    _ = ∑ i, p i * (|a i| + |b i|) := by simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ T := cap _ T hab

section Vertex
open Quadratic29947SearchBuild (Expr)

theorem expr_circuit (n : ℕ) (E : Expr ((n+1)+(n+1))) :
    ∃ C : Circuit, legal (2*(n+1)) C ∧ price C.gates = E.cost ∧
      ∀ (x y : X n), scalar (C.eval (bits (n+1) x ++ bits (n+1) y)) =
        E.fieldEval (Fin.append x y) := by
  obtain ⟨C, tap, back, legalG, cost, _, _, ev⟩ :=
    Quadratic29947SearchBuild.exists_circuit E (Fin.elim0 : Fin 0 → Expr ((n+1)+(n+1)))
  refine ⟨C, ⟨by rw [two_mul]; exact back, fun h hh => legalG h hh⟩, ?_, fun x y => ?_⟩
  · change C.gates.countP Quadratic29947SearchBuild.charged = _
    simpa using cost
  · have value := (ev (Fin.append x y)).1
    have enc : List.ofFn (fun i => decide (Fin.append x y i = 1)) =
        bits (n+1) x ++ bits (n+1) y := by
      unfold bits
      rw [← List.ofFn_fin_append]
      congr 1
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
      · simp only [Fin.append_right]
    rw [enc] at value
    exact value

theorem num_expr (n : ℕ) (Q : Bool → U n → F) (C : Circuit) (E : Expr ((n+1)+(n+1)))
    (hE : ∀ (x y : X n), scalar (C.eval (bits (n+1) x ++ bits (n+1) y)) =
      E.fieldEval (Fin.append x y)) (t : Bool) :
    num n Q C t = ∑ x : X n, ∑ u : U n,
      character (E.fieldEval (Fin.append x (yv n t u)) + (x ⬝ᵥ yv n t u + Q t u)) := by
  unfold num
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro u _
  rw [agree_character, hE]

def uIdx (n : ℕ) (j : Fin n) : Fin ((n+1)+(n+1)) := Fin.natAdd (n+1) j.succ
def yIdx (n : ℕ) (i : Fin (n+1)) : Fin ((n+1)+(n+1)) := Fin.natAdd (n+1) i
def xIdx (n : ℕ) (i : Fin (n+1)) : Fin ((n+1)+(n+1)) := Fin.castAdd (n+1) i

def linE (n : ℕ) (L : Inputs n →ₗ[ZMod 2] ZMod 2) : Expr ((n+1)+(n+1)) :=
  Expr.linear (uIdx n) (fun i => L (Pi.single i 1))

theorem linE_eval {n : ℕ} (L : Inputs n →ₗ[ZMod 2] ZMod 2) (x : X n) (t : Bool) (u : U n) :
    (linE n L).fieldEval (Fin.append x (yv n t u)) = L u := by
  rw [linE, Quadratic29947SearchBuild.Expr.linear_field,
    Quadratic29947WitnessParts.linear_coefficients L u]
  apply Finset.sum_congr rfl
  intro i _
  simp only [uIdx, yv, Fin.append_right, Fin.cons_succ]

theorem linE_cost {n : ℕ} (L : Inputs n →ₗ[ZMod 2] ZMod 2) : (linE n L).cost = 0 := by
  simp [linE]

def tapVal {n m : ℕ} (b : ZMod 2) (a : Inputs n) (N : Fin n → Fin n → ZMod 2) (d0 : ZMod 2)
    (l : Inputs n →ₗ[ZMod 2] ZMod 2) (L R : Fin m → Inputs n →ₗ[ZMod 2] ZMod 2)
    (t : Bool) (x : Inputs n) : ZMod 2 :=
  (b + dotProduct a x + ∑ i, ∑ k, N i k * x i * x k) +
    (if t then 1 else 0) * (d0 + l x + ∑ i, L i x * R i x)

def bigE (n : ℕ) {m : ℕ} (σ τ b : ZMod 2) (a : Inputs n) (N : Fin n → Fin n → ZMod 2)
    (d0 : ZMod 2) (l : Inputs n →ₗ[ZMod 2] ZMod 2) (L R : Fin m → Inputs n →ₗ[ZMod 2] ZMod 2) :
    Expr ((n+1)+(n+1)) :=
  ((Expr.sumFin (fun i : Fin (n+1) => (Expr.input (yIdx n i)).mul ((Expr.input (xIdx n i)).add
      ((Fin.cons (((Expr.const d0).add (linE n l)).add
          (Expr.sumFin fun i => (linE n (L i)).mul (linE n (R i))))
        (fun i : Fin n => Expr.linear (uIdx n) (N i)) : Fin (n+1) → Expr ((n+1)+(n+1))) i)))).add
    ((Expr.const b).add (Expr.linear (uIdx n) a))).add
   ((Expr.const σ).add (Expr.linear (fun _ : Fin 1 => yIdx n 0) (fun _ => τ)))

theorem bigE_cost (n : ℕ) {m : ℕ} (σ τ b : ZMod 2) (a : Inputs n) (N : Fin n → Fin n → ZMod 2)
    (d0 : ZMod 2) (l : Inputs n →ₗ[ZMod 2] ZMod 2) (L R : Fin m → Inputs n →ₗ[ZMod 2] ZMod 2) :
    (bigE n σ τ b a N d0 l L R).cost = n + 1 + m := by
  simp [bigE, Quadratic29947SearchBuild.Expr.cost, Fin.sum_univ_succ, linE_cost]
  omega

theorem bigE_eval (n : ℕ) {m : ℕ} (σ τ b : ZMod 2) (a : Inputs n) (N : Fin n → Fin n → ZMod 2)
    (d0 : ZMod 2) (l : Inputs n →ₗ[ZMod 2] ZMod 2) (L R : Fin m → Inputs n →ₗ[ZMod 2] ZMod 2)
    (x : X n) (t : Bool) (u : U n) :
    (bigE n σ τ b a N d0 l L R).fieldEval (Fin.append x (yv n t u)) =
      x ⬝ᵥ yv n t u + tapVal b a N d0 l L R t u + (σ + τ * (if t then 1 else 0)) := by
  simp only [bigE, Quadratic29947SearchBuild.Expr.field_add,
    Quadratic29947SearchBuild.Expr.sumFin_field, Quadratic29947SearchBuild.Expr.field_mul,
    Quadratic29947SearchBuild.Expr.field_input, Quadratic29947SearchBuild.Expr.const_field,
    Quadratic29947SearchBuild.Expr.linear_field]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Quadratic29947SearchBuild.Expr.field_add,
    Quadratic29947SearchBuild.Expr.sumFin_field, Quadratic29947SearchBuild.Expr.field_mul,
    Quadratic29947SearchBuild.Expr.field_input,
    Quadratic29947SearchBuild.Expr.const_field, Quadratic29947SearchBuild.Expr.linear_field,
    linE_eval]
  simp only [yIdx, xIdx, uIdx, Fin.append_left, Fin.append_right, yv, Fin.cons_zero,
    Fin.cons_succ, Finset.univ_unique, Finset.sum_singleton, tapVal, dotProduct,
    Fin.sum_univ_succ]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_comm,
    mul_left_comm]
  abel

end Vertex

section Attain
open Quadratic29947Polar Quadratic29947Literal Quadratic29947Fiber
open Quadratic29947WitnessParts Quadratic29947MatrixForm Quadratic29947ExactBias
open Quadratic29947SymplecticCoordinates Quadratic29947QuadraticCoordinates

private theorem first_error : ∀ a b : ZMod 2, a + (a+b) = b := by decide

private theorem last_error : ∀ (a b k l p j t : ZMod 2),
    a+b = k+l+(p+j+t) → b+(a+j+(k+l+p)) = t := by decide

theorem tapform (n r c : ℕ) (Q : Bool → Inputs n → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (shape : ∀ t, Quadratic29947Literal.quad (Q t)) (rank : M.rank = 2*r)
    (entries : ∀ x y, polar (fun u => Q false u + Q true u) x y = dotProduct x (M.mulVec y))
    (j : ℕ) (fit : j ≤ r-c) :
    ∃ (b : ZMod 2) (a : Inputs n) (N : Fin n → Fin n → ZMod 2) (d0 : ZMod 2)
      (l : Inputs n →ₗ[ZMod 2] ZMod 2) (m : ℕ) (L R : Fin m → Inputs n →ₗ[ZMod 2] ZMod 2),
      m ≤ c ∧
      (2 : ℤ)^j * (∑ x, character (Q false x + tapVal b a N d0 l L R false x)) = 2^n ∧
      (2 : ℤ)^((r-c)-j) * (∑ x, character (Q true x + tapVal b a N d0 l L R true x)) = 2^n := by
  classical
  let d := fun x => Q false x + Q true x
  obtain ⟨formula,alternating,symmetric⟩ := polar_compatible n d M entries
  obtain ⟨coords⟩ := normalForm r (fromMatrix M) alternating symmetric ((matrix_rank M).trans rank)
  obtain ⟨k,E,scale,hE⟩ := coordinate_fibers coords.left coords.right coords.independent
  obtain ⟨P,J,T,pCount,jCount,tCount,parts⟩ := split_indices r c j fit
  have subsetSize : Fintype.card (↥P) = min r c := (Fintype.card_coe P).trans pCount
  let ei : Fin (min r c) ≃ ↥P := (Fintype.equivFinOfCardEq subsetSize).symm
  have pick (x : Inputs n) :
      (∑ i : Fin (min r c), coords.left (ei i).val x * coords.right (ei i).val x) =
        ∑ i ∈ P, coords.left i x * coords.right i x := by
    calc
      _ = ∑ i : ↥P, coords.left i.val x * coords.right i.val x :=
        Fintype.sum_equiv ei _ _ (fun _ => rfl)
      _ = _ := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach P (fun i : Fin r => coords.left i x * coords.right i x)
  obtain ⟨b,a,N,eBase⟩ := added_products (Q false) (shape false) coords.left coords.right J
  let l := affineLinear coords d formula
  refine ⟨b, a, N, d 0, l, min r c, fun i => coords.left (ei i).val,
    fun i => coords.right (ei i).val, min_le_right _ _, ?_, ?_⟩
  · have errFalse (x : Inputs n) : Q false x + tapVal b a N (d 0) l
        (fun i => coords.left (ei i).val) (fun i => coords.right (ei i).val) false x =
        ∑ i ∈ J, coords.left i x * coords.right i x := by
      have eb : Q false x + ∑ i ∈ J, coords.left i x * coords.right i x =
          b + dotProduct a x + ∑ i, ∑ k, N i k * x i * x k := eBase x
      simp only [tapVal, Bool.false_eq_true, ite_false, zero_mul, add_zero]
      rw [← eb]
      exact first_error _ _
    have aligned (x : Inputs n) : Q false x + tapVal b a N (d 0) l
        (fun i => coords.left (ei i).val) (fun i => coords.right (ei i).val) false x =
          ∑ i ∈ J, ((E x).1 i).1 * ((E x).1 i).2 := by
      simpa only [hE] using errFalse x
    have answer := subset_bias r k J _ E aligned
    rw [jCount,scale] at answer
    exact answer
  · have errTrue (x : Inputs n) : Q true x + tapVal b a N (d 0) l
        (fun i => coords.left (ei i).val) (fun i => coords.right (ei i).val) true x =
        ∑ i ∈ T, coords.left i x * coords.right i x := by
      have eb : Q false x + ∑ i ∈ J, coords.left i x * coords.right i x =
          b + dotProduct a x + ∑ i, ∑ k, N i k * x i * x k := eBase x
      have form := exact_decomposition coords d formula x
      change Q false x + Q true x = d 0 + l x + ∑ i, coords.left i x * coords.right i x at form
      rw [parts] at form
      simp only [tapVal, ite_true, one_mul]
      rw [← eb, pick]
      exact last_error _ _ _ _ _ _ _ form
    have aligned (x : Inputs n) : Q true x + tapVal b a N (d 0) l
        (fun i => coords.left (ei i).val) (fun i => coords.right (ei i).val) true x =
          ∑ i ∈ T, ((E x).1 i).1 * ((E x).1 i).2 := by
      simpa only [hE] using errTrue x
    have answer := subset_bias r k T _ E aligned
    rw [tCount,scale] at answer
    exact answer

end Attain

def sgn (b : Bool) : ℚ := if b then -1 else 1

theorem chi_sgn (f : Bool) : ((character (if f then 1 else 0) : ℤ) : ℚ) = sgn f := by
  cases f
  · simp [sgn, character]
  · have one : character (1 : ZMod 2) = -1 := by decide
    simp [sgn, one]

theorem sign_true : ∀ f g : Bool, (if f then (1 : ZMod 2) else 0) +
    ((if f then 1 else 0) + (if g then 1 else 0)) * 1 = if g then 1 else 0 := by decide

theorem vertex_j (n r s : ℕ) (Q : Bool → U n → F) (M : Matrix (Fin n) (Fin n) F)
    (shape : ∀ t, quadP (Q t)) (rank : M.rank = 2*r)
    (polar : ∀ u v : U n, (Q false (u+v) + Q true (u+v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v))
    (hs : n+1 ≤ s) (j : ℕ) (fit : j ≤ r - (s-(n+1))) (f g : Bool) :
    ∃ C : Circuit, legal (2*(n+1)) C ∧ price C.gates ≤ s ∧
      score n Q C false = sgn f * (1 / 2^j) ∧
      score n Q C true = sgn g * (1 / 2^((r-(s-(n+1)))-j)) := by
  obtain ⟨b,a,N,d0,l,m,L,R,hm,vF,vT⟩ := tapform n r (s-(n+1)) Q M shape rank polar j fit
  obtain ⟨C, hl, hc, hE⟩ := expr_circuit n (bigE n (if f then 1 else 0)
    ((if f then 1 else 0) + (if g then 1 else 0)) b a N d0 l L R)
  have numEq (t : Bool) : num n Q C t = 2^(n+1) *
      (character ((if f then 1 else 0) +
        ((if f then 1 else 0) + (if g then 1 else 0)) * (if t then 1 else 0)) *
        ∑ u : U n, character (Q t u + tapVal b a N d0 l L R t u)) := by
    rw [num_expr n Q C _ hE t]
    have inner (x : X n) (u : U n) :
        character ((bigE n (if f then 1 else 0) ((if f then 1 else 0) + (if g then 1 else 0))
          b a N d0 l L R).fieldEval (Fin.append x (yv n t u)) + (x ⬝ᵥ yv n t u + Q t u)) =
        character ((if f then 1 else 0) +
          ((if f then 1 else 0) + (if g then 1 else 0)) * (if t then 1 else 0)) *
          character (Q t u + tapVal b a N d0 l L R t u) := by
      rw [bigE_eval, ← character_add]
      congr 1
      have cancel : ∀ p q w z : ZMod 2, p + w + z + (p + q) = z + (q + w) := by decide
      exact cancel _ _ _ _
    simp only [inner, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [card_X]
    ring
  have pw : (2 : ℚ) ^ (n+1+n) = 2 ^ (n+1) * 2 ^ n := pow_add 2 (n+1) n
  refine ⟨C, hl, by rw [hc, bigE_cost]; omega, ?_, ?_⟩
  · have val : (2 : ℚ)^j * ((∑ u : U n, character (Q false u + tapVal b a N d0 l L R false u) : ℤ) : ℚ)
        = 2^n := by exact_mod_cast vF
    push_cast at val
    rw [score_num, numEq false]
    simp only [Bool.false_eq_true, ite_false, mul_zero, add_zero]
    push_cast
    rw [chi_sgn, pw]
    field_simp
    linear_combination (sgn f) * val
  · have val : (2 : ℚ)^((r-(s-(n+1)))-j) *
        ((∑ u : U n, character (Q true u + tapVal b a N d0 l L R true u) : ℤ) : ℚ) = 2^n := by
      exact_mod_cast vT
    push_cast at val
    rw [score_num, numEq true]
    simp only [ite_true, sign_true]
    push_cast
    rw [chi_sgn, pw]
    field_simp
    linear_combination (sgn g) * val

section Small
open Quadratic29947SearchBuild (Expr)

theorem card_lt (n s : ℕ) (hs : s ≤ n) :
    (Finset.univ.filter fun i : Fin n => (i : ℕ) < s).card = s := by
  have bij : (Finset.univ.filter fun i : Fin n => (i : ℕ) < s).card = (Finset.range s).card := by
    refine Finset.card_bij (fun (i : Fin n) _ => (i : ℕ)) ?_ ?_ ?_
    · intro i hi
      simpa using hi
    · intro i _ k _ h
      exact Fin.ext h
    · intro k hk
      have lt : k < s := by simpa using hk
      exact ⟨⟨k, by omega⟩, by simpa using lt, rfl⟩
  rw [bij, Finset.card_range]

theorem card_low (n s : ℕ) (hs : s ≤ n) :
    (Finset.univ.filter fun u : U n => ∀ i : Fin n, ¬ (i : ℕ) < s → u i = 0).card = 2 ^ s := by
  classical
  have same : (Finset.univ.filter fun u : U n => ∀ i : Fin n, ¬ (i : ℕ) < s → u i = 0) =
      Fintype.piFinset (fun i : Fin n => if (i : ℕ) < s then (Finset.univ : Finset F) else {0}) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : (i : ℕ) < s
      · simp [hi]
      · simp [hi, h i hi]
    · intro h i hi
      have at_i := h i
      simpa [hi] using at_i
  rw [same, Fintype.card_piFinset]
  have each : ∀ i : Fin n, (if (i : ℕ) < s then (Finset.univ : Finset F) else {0}).card =
      if (i : ℕ) < s then 2 else 1 := by
    intro i
    split <;> simp
  simp only [each]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one, card_lt n s hs]

def smallE (n s : ℕ) (σb : ZMod 2) (τb : Bool) (a : U n) (Mq : Fin n → Fin n → ZMod 2) :
    Expr ((n+1)+(n+1)) :=
  ((Expr.sumFin (fun i : Fin n => if (i : ℕ) < s then
      (Expr.input (uIdx n i)).mul ((Expr.input (xIdx n i.succ)).add
        ((Expr.const (a i)).add
          (Expr.linear (uIdx n) (fun k => if (k : ℕ) < s then Mq i k else 0))))
    else Expr.zero)).add (Expr.const σb)).add
  (Expr.linear (fun _ : Fin 1 => xIdx n 0) (fun _ => if τb then 1 else 0))

theorem smallE_cost (n s : ℕ) (hs : s ≤ n) (σb : ZMod 2) (τb : Bool) (a : U n)
    (Mq : Fin n → Fin n → ZMod 2) : (smallE n s σb τb a Mq).cost = s := by
  have each : ∀ i : Fin n, (if (i : ℕ) < s then
      (Expr.input (uIdx n i)).mul ((Expr.input (xIdx n i.succ)).add
        ((Expr.const (a i)).add
          (Expr.linear (uIdx n) (fun k => if (k : ℕ) < s then Mq i k else 0))))
    else (Expr.zero : Expr ((n+1)+(n+1)))).cost = if (i : ℕ) < s then 1 else 0 := by
    intro i
    split <;> simp [Quadratic29947SearchBuild.Expr.cost]
  simp only [smallE, Quadratic29947SearchBuild.Expr.cost,
    Quadratic29947SearchBuild.Expr.sumFin_cost, each,
    Quadratic29947SearchBuild.Expr.const_cost, Quadratic29947SearchBuild.Expr.linear_cost, add_zero]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_one,
    card_lt n s hs]

def smallW (n s : ℕ) (τb t : Bool) (u : U n) : X n :=
  Fin.cons ((if τb then 1 else 0) + (if t then 1 else 0))
    (fun i => if (i : ℕ) < s then 0 else u i)

def smallR (n s : ℕ) (σb : ZMod 2) (a : U n) (Mq : Fin n → Fin n → ZMod 2)
    (Q : Bool → U n → F) (t : Bool) (u : U n) : ZMod 2 :=
  (∑ i : Fin n, if (i : ℕ) < s then
      u i * (a i + ∑ k : Fin n, (if (k : ℕ) < s then Mq i k else 0) * u k) else 0) + σb + Q t u

theorem smallE_eval (n s : ℕ) (σb : ZMod 2) (τb : Bool) (a : U n) (Mq : Fin n → Fin n → ZMod 2)
    (Q : Bool → U n → F) (x : X n) (t : Bool) (u : U n) :
    (smallE n s σb τb a Mq).fieldEval (Fin.append x (yv n t u)) + (x ⬝ᵥ yv n t u + Q t u) =
      x ⬝ᵥ smallW n s τb t u + smallR n s σb a Mq Q t u := by
  have each : ∀ i : Fin n, (if (i : ℕ) < s then
      (Expr.input (uIdx n i)).mul ((Expr.input (xIdx n i.succ)).add
        ((Expr.const (a i)).add
          (Expr.linear (uIdx n) (fun k => if (k : ℕ) < s then Mq i k else 0))))
    else (Expr.zero : Expr ((n+1)+(n+1)))).fieldEval (Fin.append x (yv n t u)) =
      if (i : ℕ) < s then u i * (x i.succ + (a i +
        ∑ k : Fin n, (if (k : ℕ) < s then Mq i k else 0) * u k)) else 0 := by
    intro i
    split
    · simp only [Quadratic29947SearchBuild.Expr.field_mul,
        Quadratic29947SearchBuild.Expr.field_add, Quadratic29947SearchBuild.Expr.field_input,
        Quadratic29947SearchBuild.Expr.const_field, Quadratic29947SearchBuild.Expr.linear_field,
        uIdx, xIdx, yv, Fin.append_left, Fin.append_right, Fin.cons_succ]
    · rfl
  simp only [smallE, Quadratic29947SearchBuild.Expr.field_add,
    Quadratic29947SearchBuild.Expr.sumFin_field, each,
    Quadratic29947SearchBuild.Expr.const_field, Quadratic29947SearchBuild.Expr.linear_field]
  simp only [xIdx, Fin.append_left, Finset.univ_unique, Finset.sum_singleton, smallW, smallR,
    dotProduct, Fin.sum_univ_succ, yv, Fin.cons_zero, Fin.cons_succ]
  have point : ∀ (c : Prop) [Decidable c] (ui xi A : ZMod 2),
      (if c then ui * (xi + A) else 0) + xi * ui =
        xi * (if c then 0 else ui) + (if c then ui * A else 0) := by
    intro c _ ui xi A
    have both : ∀ ui xi A : ZMod 2, ui * (xi + A) + xi * ui = xi * 0 + ui * A := by decide
    split
    · exact both ui xi A
    · ring
  have sums : (∑ i : Fin n, (if (i : ℕ) < s then u i * (x i.succ + (a i +
        ∑ k : Fin n, (if (k : ℕ) < s then Mq i k else 0) * u k)) else 0)) +
      ∑ i : Fin n, x i.succ * u i =
      (∑ i : Fin n, x i.succ * (if (i : ℕ) < s then 0 else u i)) +
      ∑ i : Fin n, (if (i : ℕ) < s then
        u i * (a i + ∑ k : Fin n, (if (k : ℕ) < s then Mq i k else 0) * u k) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => point _ _ _ _
  linear_combination sums

end Small

def qq (n r s : ℕ) : ℚ := if s < n+1 then 0 else 1 / 2 ^ (r-(s-(n+1)))

theorem dotHom_zero_iff (n : ℕ) (w : X n) : dotHom n w = 0 ↔ w = 0 := by
  constructor
  · intro h
    apply dotHom_inj n w 0
    rw [h]
    ext x
    simp [dotHom]
  · rintro rfl
    ext x
    simp [dotHom]

theorem smallW_zero (n s : ℕ) (τb : Bool) (u : U n) :
    smallW n s τb τb u = 0 ↔ ∀ i : Fin n, ¬ (i : ℕ) < s → u i = 0 := by
  constructor
  · intro h i hi
    have at_i := congrFun h i.succ
    simpa [smallW, hi] using at_i
  · intro h
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [smallW, Fin.cons_zero, Pi.zero_apply]
      cases τb <;> decide
    · simp only [smallW, Fin.cons_succ, Pi.zero_apply]
      split
      · rfl
      · exact h i' ‹_›

theorem smallR_low (n s : ℕ) (b fb : ZMod 2) (a : U n) (Mq : Fin n → Fin n → ZMod 2)
    (Q : Bool → U n → F) (t : Bool) (u : U n)
    (eq : Q t u = b + dotProduct a u + ∑ i, ∑ j, Mq i j * u i * u j)
    (low : ∀ i : Fin n, ¬ (i : ℕ) < s → u i = 0) :
    smallR n s (b + fb) a Mq Q t u = fb := by
  have key : (∑ i : Fin n, if (i : ℕ) < s then
      u i * (a i + ∑ k : Fin n, (if (k : ℕ) < s then Mq i k else 0) * u k) else 0) =
      dotProduct a u + ∑ i, ∑ k, Mq i k * u i * u k := by
    have h1 : ∀ i k : Fin n, (if (k : ℕ) < s then Mq i k else 0) * u k = Mq i k * u k := by
      intro i k
      by_cases hk : (k : ℕ) < s
      · simp [hk]
      · simp [hk, low k hk]
    have h2 : ∀ i : Fin n, (if (i : ℕ) < s then u i * (a i + ∑ k : Fin n, Mq i k * u k) else 0) =
        u i * (a i + ∑ k : Fin n, Mq i k * u k) := by
      intro i
      by_cases hi : (i : ℕ) < s
      · simp [hi]
      · simp [hi, low i hi]
    simp only [h1]
    simp only [h2]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, dotProduct]
    have e1 : (∑ i : Fin n, u i * a i) = ∑ i : Fin n, a i * u i :=
      Finset.sum_congr rfl fun i _ => mul_comm (u i) (a i)
    have e2 : (∑ i : Fin n, ∑ k : Fin n, u i * (Mq i k * u k)) =
        ∑ i : Fin n, ∑ k : Fin n, Mq i k * u i * u k :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [e1, e2]
  unfold smallR
  rw [key, eq]
  have fin : ∀ p S b f' : ZMod 2, (p + S) + (b + f') + (b + p + S) = f' := by decide
  exact fin _ _ _ _

theorem vertex_small (n s : ℕ) (Q : Bool → U n → F) (shape : ∀ t, quadP (Q t))
    (hs : s < n+1) (τb f : Bool) :
    ∃ C : Circuit, legal (2*(n+1)) C ∧ price C.gates ≤ s ∧
      score n Q C τb = sgn f * (1 / 2^(n-s)) ∧ score n Q C (!τb) = 0 := by
  classical
  obtain ⟨b, a, Mq, eq⟩ := shape τb
  obtain ⟨C, hl, hc, hE⟩ := expr_circuit n (smallE n s (b + if f then 1 else 0) τb a Mq)
  have numEq (t : Bool) : num n Q C t =
      ∑ u : U n, character (smallR n s (b + if f then 1 else 0) a Mq Q t u) *
        (if smallW n s τb t u = 0 then (2 : ℤ)^(n+1) else 0) := by
    rw [num_expr n Q C _ hE t, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    have total := hom_sum (dotHom n (smallW n s τb t u))
    rw [card_X] at total
    simp only [dotHom_zero_iff] at total
    rw [← total, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [smallE_eval, character_add, mul_comm]
    rfl
  refine ⟨C, hl, by rw [hc, smallE_cost n s (by omega)], ?_, ?_⟩
  · have val : num n Q C τb = 2^s * 2^(n+1) * character (if f then 1 else 0) := by
      rw [numEq τb]
      have term (u : U n) : character (smallR n s (b + if f then 1 else 0) a Mq Q τb u) *
          (if smallW n s τb τb u = 0 then (2 : ℤ)^(n+1) else 0) =
          if (∀ i : Fin n, ¬ (i : ℕ) < s → u i = 0) then
            2^(n+1) * character (if f then 1 else 0) else 0 := by
        by_cases low : ∀ i : Fin n, ¬ (i : ℕ) < s → u i = 0
        · rw [if_pos ((smallW_zero n s τb u).mpr low), if_pos low,
            smallR_low n s b _ a Mq Q τb u (eq u) low]
          ring
        · rw [if_neg (fun h => low ((smallW_zero n s τb u).mp h)), if_neg low, mul_zero]
      simp only [term]
      rw [← Finset.sum_filter, Finset.sum_const, card_low n s (by omega)]
      simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    have pw : (2 : ℚ)^(n+1+n) = 2^(n+1) * (2^(n-s) * 2^s) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [score_num, val]
    push_cast
    rw [chi_sgn, pw]
    field_simp
  · have val : num n Q C (!τb) = 0 := by
      rw [numEq]
      apply Finset.sum_eq_zero
      intro u _
      have ne : smallW n s τb (!τb) u ≠ 0 := by
        intro h
        have h0 := congrFun h 0
        simp only [smallW, Fin.cons_zero, Pi.zero_apply] at h0
        revert h0
        cases τb <;> decide
      rw [if_neg ne, mul_zero]
    rw [score_num, val]
    simp

theorem vertices (n r s : ℕ) (Q : Bool → U n → F) (M : Matrix (Fin n) (Fin n) F)
    (shape : ∀ t, quadP (Q t)) (rank : M.rank = 2*r)
    (polar : ∀ u v : U n, (Q false (u+v) + Q true (u+v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v))
    (f g : Bool) :
    (∃ C : Circuit, legal (2*(n+1)) C ∧ price C.gates ≤ s ∧
      score n Q C false = sgn f * rho n s ∧ score n Q C true = sgn g * qq n r s) ∧
    (∃ C : Circuit, legal (2*(n+1)) C ∧ price C.gates ≤ s ∧
      score n Q C false = sgn f * qq n r s ∧ score n Q C true = sgn g * rho n s) := by
  by_cases hs : s < n+1
  · obtain ⟨C1, l1, c1, a1, b1⟩ := vertex_small n s Q shape hs false f
    obtain ⟨C2, l2, c2, a2, b2⟩ := vertex_small n s Q shape hs true g
    simp only [rho, qq, if_pos hs, mul_zero]
    exact ⟨⟨C1, l1, c1, a1, b1⟩, ⟨C2, l2, c2, b2, a2⟩⟩
  · have big : n+1 ≤ s := by omega
    obtain ⟨C1, l1, c1, a1, b1⟩ :=
      vertex_j n r s Q M shape rank polar big 0 (Nat.zero_le _) f g
    obtain ⟨C2, l2, c2, a2, b2⟩ :=
      vertex_j n r s Q M shape rank polar big _ le_rfl f g
    simp only [rho, qq, if_neg hs]
    exact ⟨⟨C1, l1, c1, by simpa using a1, by simpa using b1⟩,
      ⟨C2, l2, c2, by simpa using a2, by simpa using b2⟩⟩

theorem seg_fst (K : Set (ℚ × ℚ)) (hK : Convex ℚ K) (A y a : ℚ)
    (h1 : (A,y) ∈ K) (h2 : (-A,y) ∈ K) (ha : |a| ≤ A) : (a,y) ∈ K := by
  have bounds := abs_le.mp ha
  by_cases hA : A = 0
  · have : a = A := by rw [hA] at bounds ⊢; linarith [bounds.1, bounds.2]
    rw [this]
    exact h1
  · have pos : 0 < A := lt_of_le_of_ne (le_trans (abs_nonneg a) ha) (Ne.symm hA)
    have mem := hK h1 h2 (a := (a + A) / (2*A)) (b := (A - a) / (2*A))
      (div_nonneg (by linarith [bounds.1]) (by linarith))
      (div_nonneg (by linarith [bounds.2]) (by linarith)) (by field_simp; ring)
    have eq : ((a + A) / (2*A)) • ((A,y) : ℚ × ℚ) + ((A - a) / (2*A)) • ((-A,y) : ℚ × ℚ) =
        (a,y) := by
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        field_simp
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        field_simp
        ring
    rw [← eq]
    exact mem

theorem seg_snd (K : Set (ℚ × ℚ)) (hK : Convex ℚ K) (B x b : ℚ)
    (h1 : (x,B) ∈ K) (h2 : (x,-B) ∈ K) (hb : |b| ≤ B) : (x,b) ∈ K := by
  have bounds := abs_le.mp hb
  by_cases hB : B = 0
  · have : b = B := by rw [hB] at bounds ⊢; linarith [bounds.1, bounds.2]
    rw [this]
    exact h1
  · have pos : 0 < B := lt_of_le_of_ne (le_trans (abs_nonneg b) hb) (Ne.symm hB)
    have mem := hK h1 h2 (a := (b + B) / (2*B)) (b := (B - b) / (2*B))
      (div_nonneg (by linarith [bounds.1]) (by linarith))
      (div_nonneg (by linarith [bounds.2]) (by linarith)) (by field_simp; ring)
    have eq : ((b + B) / (2*B)) • ((x,B) : ℚ × ℚ) + ((B - b) / (2*B)) • ((x,-B) : ℚ × ℚ) =
        (x,b) := by
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        field_simp
        ring
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        field_simp
        ring
    rw [← eq]
    exact mem

theorem geo (p q : ℚ) (hq : 0 ≤ q) (hqp : q ≤ p) (K : Set (ℚ × ℚ)) (hK : Convex ℚ K)
    (hv : ∀ σ τ : ℚ, (σ = 1 ∨ σ = -1) → (τ = 1 ∨ τ = -1) →
      (σ*p, τ*q) ∈ K ∧ (σ*q, τ*p) ∈ K)
    (a b : ℚ) (ha : |a| ≤ p) (hb : |b| ≤ p) (hab : |a| + |b| ≤ p + q) : (a,b) ∈ K := by
  have corner (σ τ : ℚ) (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
      (σ * max |a| q, τ * (p + q - max |a| q)) ∈ K := by
    obtain ⟨m1, m2⟩ := hv σ τ hσ hτ
    have lo : q ≤ max |a| q := le_max_right _ _
    have hi : max |a| q ≤ p := max_le ha hqp
    by_cases same : p = q
    · have eqA : max |a| q = p := le_antisymm hi (same ▸ lo)
      rw [eqA]
      have : p + q - p = q := by ring
      rw [this]
      exact m1
    · have gap : 0 < p - q := by
        have := lt_of_le_of_ne hqp (Ne.symm same)
        linarith
      have mem := hK m1 m2 (a := (max |a| q - q) / (p - q)) (b := (p - max |a| q) / (p - q))
        (div_nonneg (by linarith) gap.le) (div_nonneg (by linarith) gap.le)
        (by field_simp; ring)
      have eq : ((max |a| q - q) / (p - q)) • ((σ*p, τ*q) : ℚ × ℚ) +
          ((p - max |a| q) / (p - q)) • ((σ*q, τ*p) : ℚ × ℚ) =
          (σ * max |a| q, τ * (p + q - max |a| q)) := by
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          field_simp
          ring
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          field_simp
          ring
      rw [← eq]
      exact mem
  have hA : |a| ≤ max |a| q := le_max_left _ _
  have hB : |b| ≤ p + q - max |a| q := by
    rcases le_total |a| q with small | big
    · rw [max_eq_right small]
      linarith
    · rw [max_eq_left big]
      linarith
  have c11 := corner 1 1 (Or.inl rfl) (Or.inl rfl)
  have c12 := corner 1 (-1) (Or.inl rfl) (Or.inr rfl)
  have c21 := corner (-1) 1 (Or.inr rfl) (Or.inl rfl)
  have c22 := corner (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at c11 c12 c21 c22
  exact seg_snd K hK _ a b (seg_fst K hK _ _ a c11 c21 hA) (seg_fst K hK _ _ a c12 c22 hA) hB

theorem three (S : Set (ℚ × ℚ)) (x : ℚ × ℚ) (hx : x ∈ convexHull ℚ S) :
    ∃ (z : Fin 3 → ℚ × ℚ) (w : Fin 3 → ℚ), (∀ i, z i ∈ S) ∧ (∀ i, 0 ≤ w i) ∧
      (∑ i, w i) = 1 ∧ (∑ i, w i • z i) = x := by
  obtain ⟨ι, _, z, w, hz, hind, hw, hsum, hcomb⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have card : Fintype.card ι ≤ 3 := by
    have c1 := hind.card_le_finrank_succ
    have c2 := Submodule.finrank_le (vectorSpan ℚ (Set.range z))
    have c3 : Module.finrank ℚ (ℚ × ℚ) = 2 := by simp
    omega
  have nonempty : Nonempty ι := by
    by_contra none
    rw [not_nonempty_iff] at none
    simp at hsum
  obtain ⟨i0⟩ := nonempty
  let emb : ι → Fin 3 := fun i => Fin.castLE card (Fintype.equivFin ι i)
  have inj : Function.Injective emb :=
    (Fin.castLE_injective card).comp (Fintype.equivFin ι).injective
  refine ⟨Function.extend emb z (fun _ => z i0), Function.extend emb w 0, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : ∃ i, emb i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [inj.extend_apply]
      exact hz ⟨i, rfl⟩
    · rw [Function.extend_apply' _ _ _ hj]
      exact hz ⟨i0, rfl⟩
  · intro j
    by_cases hj : ∃ i, emb i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [inj.extend_apply]
      exact (hw i).le
    · rw [Function.extend_apply' _ _ _ hj]
      rfl
  · rw [← hsum]
    symm
    apply Fintype.sum_of_injective emb inj
    · intro j hj
      exact Function.extend_apply' _ _ _ (by simpa using hj)
    · intro i
      rw [inj.extend_apply]
  · rw [← hcomb]
    symm
    apply Fintype.sum_of_injective emb inj
    · intro j hj
      rw [Function.extend_apply' w (0 : Fin 3 → ℚ) j (by simpa using hj)]
      simp
    · intro i
      rw [inj.extend_apply, inj.extend_apply]
theorem realize (n r s : ℕ) (Q : Bool → U n → F) (M : Matrix (Fin n) (Fin n) F)
    (shape : ∀ t, quadP (Q t)) (rank : M.rank = 2*r)
    (polar : ∀ u v : U n, (Q false (u+v) + Q true (u+v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v))
    (v : Bool → ℚ) (h0 : |v false| ≤ rho n s) (h1 : |v true| ≤ rho n s)
    (h01 : |v false| + |v true| ≤ total n r s) :
    ∃ (C : Fin 3 → Circuit) (p : Fin 3 → ℚ),
      (∀ i, legal (2*(n+1)) (C i) ∧ price (C i).gates ≤ s ∧ 0 ≤ p i) ∧
      (∑ i, p i) = 1 ∧ ∀ t, v t = ∑ i, p i * score n Q (C i) t := by
  let S : Set (ℚ × ℚ) := {z | ∃ C : Circuit, legal (2*(n+1)) C ∧ price C.gates ≤ s ∧
    z = (score n Q C false, score n Q C true)}
  have q_nonneg : 0 ≤ qq n r s := by
    unfold qq
    split <;> positivity
  have q_le : qq n r s ≤ rho n s := by
    unfold qq rho
    split
    · positivity
    · rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
  have tot : total n r s = rho n s + qq n r s := by
    unfold total qq rho
    split <;> simp
  have signs : ∀ σ : ℚ, (σ = 1 ∨ σ = -1) → ∃ f : Bool, σ = sgn f := by
    rintro σ (rfl | rfl)
    · exact ⟨false, by simp [sgn]⟩
    · exact ⟨true, by simp [sgn]⟩
  have hv : ∀ σ τ : ℚ, (σ = 1 ∨ σ = -1) → (τ = 1 ∨ τ = -1) →
      (σ * rho n s, τ * qq n r s) ∈ convexHull ℚ S ∧
      (σ * qq n r s, τ * rho n s) ∈ convexHull ℚ S := by
    intro σ τ hσ hτ
    obtain ⟨f, rfl⟩ := signs σ hσ
    obtain ⟨g, rfl⟩ := signs τ hτ
    obtain ⟨⟨C1, l1, c1, a1, b1⟩, ⟨C2, l2, c2, a2, b2⟩⟩ :=
      vertices n r s Q M shape rank polar f g
    exact ⟨subset_convexHull ℚ S ⟨C1, l1, c1, by rw [a1, b1]⟩,
      subset_convexHull ℚ S ⟨C2, l2, c2, by rw [a2, b2]⟩⟩
  have mem := geo (rho n s) (qq n r s) q_nonneg q_le (convexHull ℚ S) (convex_convexHull ℚ S)
    hv (v false) (v true) h0 h1 (by rw [← tot]; exact h01)
  obtain ⟨z, w, hz, hw, hsum, hcomb⟩ := three S _ mem
  choose C hl hc hzC using hz
  refine ⟨C, w, fun i => ⟨hl i, hc i, hw i⟩, hsum, fun t => ?_⟩
  have fst := congrArg Prod.fst hcomb
  have snd := congrArg Prod.snd hcomb
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, hzC]
    at fst snd
  cases t
  · exact fst.symm
  · exact snd.symm

theorem main (n r s : ℕ) (Q : Bool → U n → F) (M : Matrix (Fin n) (Fin n) F)
    (shape : ∀ t, quadP (Q t)) (rank : M.rank = 2*r)
    (polar : ∀ u v : U n, (Q false (u+v) + Q true (u+v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v)) :
    (∀ v : Bool → ℚ,
      (∃ (C : Fin 3 → Circuit) (p : Fin 3 → ℚ),
        (∀ i, legal (2*(n+1)) (C i) ∧ price (C i).gates ≤ s ∧ 0 ≤ p i) ∧
        (∑ i, p i) = 1 ∧ ∀ t, v t = ∑ i, p i * score n Q (C i) t) ↔
      |v false| ≤ rho n s ∧ |v true| ≤ rho n s ∧ |v false| + |v true| ≤ total n r s) ∧
    ((∃ C : Circuit, legal (2*(n+1)) C ∧ price C.gates ≤ s ∧ ∀ t, score n Q C t = 1) ↔
      n+1+r ≤ s) := by
  refine ⟨fun v => ⟨?_, fun h => realize n r s Q M shape rank polar v h.1 h.2.1 h.2.2⟩,
    ⟨?_, ?_⟩⟩
  · rintro ⟨C, p, each, one, val⟩
    have bounds := fun i => single n r s Q M shape rank polar (C i) (each i).1 (each i).2.1
    rw [val false, val true]
    exact mix p _ _ _ _ (fun i => (each i).2.2) one (fun i => (bounds i).1 false)
      (fun i => (bounds i).1 true) (fun i => (bounds i).2)
  · rintro ⟨C, ok, cheap, exact⟩
    have bound := (single n r s Q M shape rank polar C ok cheap).2
    rw [exact false, exact true] at bound
    norm_num at bound
    by_contra short
    by_cases hs : s < n+1
    · simp only [total, rho, if_pos hs] at bound
      have small : (1 : ℚ) / 2 ^ (n-s) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ (by norm_num)
      linarith
    · simp only [total, if_neg hs] at bound
      have pos : 0 < r - (s - (n+1)) := by omega
      have small : (1 : ℚ) / 2 ^ (r - (s - (n+1))) < 1 := by
        rw [div_lt_one (by positivity)]
        exact one_lt_pow₀ (by norm_num) (by omega)
      linarith
  · intro enough
    have hs : ¬ s < n+1 := by omega
    have zero : r - (s - (n+1)) = 0 := by omega
    obtain ⟨C, p, each, one, val⟩ := realize n r s Q M shape rank polar (fun _ => 1)
      (by simp [rho, hs]) (by simp [rho, hs]) (by simp [total, hs, zero])
    have gap : ∑ i, p i * ((1 - score n Q (C i) false) + (1 - score n Q (C i) true)) = 0 := by
      have f := val false
      have t := val true
      simp only [mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        one, ← f, ← t]
      norm_num
    have term (i : Fin 3) :
        0 ≤ p i * ((1 - score n Q (C i) false) + (1 - score n Q (C i) true)) := by
      have a := (abs_le.mp (score_abs n Q (C i) false)).2
      have b := (abs_le.mp (score_abs n Q (C i) true)).2
      exact mul_nonneg (each i).2.2 (by linarith)
    have each0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => term i).mp gap
    obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
      by_contra none
      simp only [not_exists, not_not] at none
      simp [none] at one
    refine ⟨C i, (each i).1, (each i).2.1, fun t => ?_⟩
    have z := each0 i (Finset.mem_univ i)
    have sumz := (mul_eq_zero.mp z).resolve_left hi
    have a := (abs_le.mp (score_abs n Q (C i) false)).2
    have b := (abs_le.mp (score_abs n Q (C i) true)).2
    cases t <;> linarith

end PEqualNP.Outside.L_meta_29948

theorem PEqualNP.Outside.L_meta_29948 : ∀ (n r s : ℕ),
  let F := ZMod 2
  let V := Fin n → F
  let quad := fun (q : V → F) =>
    ∃ (b : F) (a : V) (M : Fin n → Fin n → F), ∀ v,
      q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (n : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (n : ℕ) (u : Fin n → F) => List.ofFn (fun j : Fin n => decide (u j = 1))
  ∀ (Q : Bool → V → F) (M : Matrix (Fin n) (Fin n) F), (∀ t, quad (Q t)) →
    let d := fun u : V => Q false u + Q true u
    M.rank = 2*r → (∀ u v, d (u+v) + d u + d v + d 0 = dotProduct u (M.mulVec v)) →
    let k := n+1
    let score := fun (C : Circ) (t : Bool) =>
      (∑ x : Fin k → F, ∑ u : V,
        let y : Fin k → F := Fin.cons (if t then 1 else 0) u
        if C.eval (bits k x ++ bits k y) = decide (dotProduct x y + Q t u = 1)
        then (1 : ℚ) else -1) / 2^(k+n)
    let rho : ℚ := if s < k then 1 / 2^(n-s) else 1
    let total : ℚ := if s < k then rho else 1 + 1 / 2^(r-(s-k))
    (∀ v : Bool → ℚ,
      (∃ (C : Fin 3 → Circ) (p : Fin 3 → ℚ),
        (∀ i, legal (2*k) (C i) ∧ cost (C i) ≤ s ∧ 0 ≤ p i) ∧
        (∑ i, p i) = 1 ∧ ∀ t, v t = ∑ i, p i * score (C i) t) ↔
      |v false| ≤ rho ∧ |v true| ≤ rho ∧ |v false| + |v true| ≤ total) ∧
    ((∃ C : Circ, legal (2*k) C ∧ cost C ≤ s ∧ ∀ t, score C t = 1) ↔ k+r ≤ s) := by
  intro n r s
  dsimp only
  intro Q M shape rank polar
  exact PEqualNP.Outside.L_meta_29948.main n r s Q M shape rank polar
