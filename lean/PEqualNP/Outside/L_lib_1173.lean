import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1173

noncomputable def acc (n r : ℕ) (s : Fin r → Fin n → Fin n → Bool × Bool) (x : Fin r → Finset (Fin n)) : Bool :=
  (Finset.univ : Finset (Fin r)).toList.all (fun j =>
    (Finset.univ : Finset (Fin n)).toList.all (fun u =>
      (Finset.univ : Finset (Fin n)).toList.all (fun v =>
        !(decide (u < v)) || ((decide (u ∈ x j), decide (v ∈ x j)) != s j u v))))

noncomputable def rep (n r : ℕ) (A : Finset (Fin r → Finset (Fin n)))
    (s : Fin r → Fin n → Fin n → Bool × Bool) : Bool :=
  A.toList.any (fun x => acc n r s x)

theorem acc_iff {n r : ℕ} (s : Fin r → Fin n → Fin n → Bool × Bool) (x : Fin r → Finset (Fin n)) :
    acc n r s x = true ↔
      ∀ j u v, u < v → (decide (u ∈ x j), decide (v ∈ x j)) ≠ s j u v := by
  simp only [acc, List.all_eq_true, Finset.mem_toList, Finset.mem_univ, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne]
  constructor
  · intro h j u v huv
    rcases h j u v with h1 | h1
    · exact absurd huv h1
    · exact h1
  · intro h j u v
    by_cases huv : u < v
    · exact Or.inr (h j u v huv)
    · exact Or.inl huv

theorem rep_empty {n r : ℕ} (s : Fin r → Fin n → Fin n → Bool × Bool) : rep n r ∅ s = false := by
  simp [rep]

theorem rep_singleton {n r : ℕ} (s : Fin r → Fin n → Fin n → Bool × Bool)
    (w : Fin r → Finset (Fin n)) : rep n r {w} s = acc n r s w := by
  simp [rep]

theorem rep_of_mem {n r : ℕ} {s : Fin r → Fin n → Fin n → Bool × Bool}
    {A : Finset (Fin r → Finset (Fin n))} {x : Fin r → Finset (Fin n)}
    (hx : x ∈ A) (h : acc n r s x = true) : rep n r A s = true := by
  simp only [rep, List.any_eq_true, Finset.mem_toList]
  exact ⟨x, hx, h⟩

theorem card_block_le {n : ℕ} (p : Fin n → Fin n → Bool × Bool) :
    (Finset.univ.filter (fun S : Finset (Fin n) =>
      ∀ u v, u < v → (decide (u ∈ S), decide (v ∈ S)) ≠ p u v)).card ≤ n + 1 := by
  classical
  set F := Finset.univ.filter (fun S : Finset (Fin n) =>
      ∀ u v, u < v → (decide (u ∈ S), decide (v ∈ S)) ≠ p u v) with hF
  refine (Finset.card_le_card_shatterer F).trans ?_
  have hsub : F.shatterer ⊆
      (Finset.univ : Finset (Option (Fin n))).image (fun o => o.toFinset) := by
    intro T hT
    rw [Finset.mem_shatterer] at hT
    have hcard : T.card ≤ 1 := by
      by_contra hc
      push Not at hc
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hc
      wlog hlt : u < v generalizing u v
      · exact this v hv u hu huv.symm (lt_of_le_of_ne (not_lt.mp hlt) huv.symm)
      have ht : ((if (p u v).1 = true then {u} else ∅) ∪ (if (p u v).2 = true then {v} else ∅) :
          Finset (Fin n)) ⊆ T := by
        intro z hz
        rw [Finset.mem_union] at hz
        rcases hz with hz | hz
        · split_ifs at hz with h1
          · rw [Finset.mem_singleton] at hz; rw [hz]; exact hu
          · simp at hz
        · split_ifs at hz with h1
          · rw [Finset.mem_singleton] at hz; rw [hz]; exact hv
          · simp at hz
      obtain ⟨S, hS, hST⟩ := hT ht
      have hS' := (Finset.mem_filter.mp hS).2 u v hlt
      apply hS'
      have h1 : u ∈ S ↔ (p u v).1 = true := by
        have : u ∈ T ∩ S ↔ u ∈ S := by simp [hu]
        rw [← this, hST]
        by_cases a : (p u v).1 = true <;> by_cases b : (p u v).2 = true <;> simp [a, b, huv]
      have h2 : v ∈ S ↔ (p u v).2 = true := by
        have : v ∈ T ∩ S ↔ v ∈ S := by simp [hv]
        rw [← this, hST]
        by_cases a : (p u v).1 = true <;> by_cases b : (p u v).2 = true <;>
          simp [a, b, huv.symm]
      ext
      · by_cases a : (p u v).1 = true
        · simp [h1, a]
        · simp only [Bool.not_eq_true] at a; simp [h1, a]
      · by_cases a : (p u v).2 = true
        · simp [h2, a]
        · simp only [Bool.not_eq_true] at a; simp [h2, a]
    rw [Finset.mem_image]
    rcases Nat.lt_or_ge T.card 1 with h0 | h1
    · refine ⟨none, Finset.mem_univ _, ?_⟩
      have : T = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [this]
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (le_antisymm hcard h1)
      exact ⟨some a, Finset.mem_univ _, by simp [ha]⟩
  calc F.shatterer.card ≤ ((Finset.univ : Finset (Option (Fin n))).image
        (fun o => o.toFinset)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Option (Fin n))).card := Finset.card_image_le
    _ = n + 1 := by simp

theorem card_acc_le {n r : ℕ} (s : Fin r → Fin n → Fin n → Bool × Bool) :
    (Finset.univ.filter (fun x : Fin r → Finset (Fin n) => acc n r s x = true)).card
      ≤ (n + 1) ^ r := by
  classical
  have hsub : Finset.univ.filter (fun x : Fin r → Finset (Fin n) => acc n r s x = true) ⊆
      Fintype.piFinset (fun j : Fin r => Finset.univ.filter (fun S : Finset (Fin n) =>
        ∀ u v, u < v → (decide (u ∈ S), decide (v ∈ S)) ≠ s j u v)) := by
    intro x hx
    rw [Finset.mem_filter, acc_iff] at hx
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun u v huv => hx.2 j u v huv⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  calc _ ≤ (n + 1) ^ (Finset.univ : Finset (Fin r)).card :=
        Finset.prod_le_pow_card _ _ _ (fun j _ => card_block_le (s j))
    _ = (n + 1) ^ r := by simp

theorem exists_few {n r k : ℕ} (J : Finset (Fin k))
    (s : Fin k → Fin r → Fin n → Fin n → Bool × Bool) (c : ℕ)
    (h : J.card * (n + 1) ^ r < (c + 1) * (2 ^ n) ^ r) :
    ∃ w : Fin r → Finset (Fin n), (J.filter (fun j => acc n r (s j) w = true)).card ≤ c := by
  classical
  by_contra hcon
  push Not at hcon
  have h1 : (c + 1) * (2 ^ n) ^ r ≤ ∑ w : Fin r → Finset (Fin n),
      (J.filter (fun j => acc n r (s j) w = true)).card := by
    calc (c + 1) * (2 ^ n) ^ r = ∑ _w : Fin r → Finset (Fin n), (c + 1) := by
          simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun w _ => hcon w)
  have h2 : ∑ w : Fin r → Finset (Fin n), (J.filter (fun j => acc n r (s j) w = true)).card
      = ∑ j ∈ J, (Finset.univ.filter
          (fun w : Fin r → Finset (Fin n) => acc n r (s j) w = true)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h3 : ∑ j ∈ J, (Finset.univ.filter
      (fun w : Fin r → Finset (Fin n) => acc n r (s j) w = true)).card ≤ J.card * (n + 1) ^ r := by
    calc _ ≤ ∑ _j ∈ J, (n + 1) ^ r := Finset.sum_le_sum (fun j _ => card_acc_le (s j))
      _ = _ := by simp
  omega


theorem hamming {n t : ℕ} (hn : n + 1 = 2 ^ t) :
    ∃ C : Finset (Finset (Fin n)), C.card * 2 ^ t ≤ 2 ^ n ∧
      ∀ S : Finset (Fin n), ∃ c ∈ C, ∀ u v, u ≠ v → ((u ∈ S ↔ u ∈ c) ∨ (v ∈ S ↔ v ∈ c)) := by
  classical
  have hGc : Fintype.card (Fin t → ZMod 2) = 2 ^ t := by simp [ZMod.card]
  have hcard : Fintype.card (Fin n) = Fintype.card {g : Fin t → ZMod 2 // g ≠ 0} := by
    rw [Fintype.card_subtype_compl, hGc]
    simp
    omega
  let ε := Fintype.equivOfCardEq hcard
  let vec : Fin n → (Fin t → ZMod 2) := fun a => (ε a).1
  let synd : Finset (Fin n) → (Fin t → ZMod 2) := fun S => ∑ a ∈ S, vec a
  let flip : Finset (Fin n) → Fin n → Finset (Fin n) :=
    fun S a => if a ∈ S then S.erase a else insert a S
  have hG : ∀ g : Fin t → ZMod 2, g + g = 0 := fun g => by
    funext i; exact CharTwo.add_self_eq_zero (g i)
  have hflip : ∀ S a, synd (flip S a) = synd S + vec a := by
    intro S a
    by_cases ha : a ∈ S
    · have h1 : synd S = synd (S.erase a) + vec a := (Finset.sum_erase_add S vec ha).symm
      have h2 : flip S a = S.erase a := by simp [flip, ha]
      rw [h2, h1, add_assoc, hG, add_zero]
    · have h2 : flip S a = insert a S := by simp [flip, ha]
      rw [h2]
      show ∑ b ∈ insert a S, vec b = ∑ b ∈ S, vec b + vec a
      rw [Finset.sum_insert ha, add_comm]
  have hmem : ∀ S a u, u ∈ flip S a ↔ (u ∈ S ↔ u ≠ a) := by
    intro S a u
    by_cases ha : a ∈ S
    · by_cases hu : u = a
      · subst hu; simp [flip, ha]
      · simp [flip, ha, hu]
    · by_cases hu : u = a
      · subst hu; simp [flip, ha]
      · simp [flip, ha, hu]
  have hinv : ∀ S a, flip (flip S a) a = S := by
    intro S a
    ext u
    rw [hmem, hmem]
    tauto
  have hvec : ∀ (g : Fin t → ZMod 2) (h : g ≠ 0), vec (ε.symm ⟨g, h⟩) = g := by
    intro g h
    simp [vec]
  let Φ : Finset (Fin n) × (Fin t → ZMod 2) → Finset (Fin n) :=
    fun q => if h : q.2 = 0 then q.1 else flip q.1 (ε.symm ⟨q.2, h⟩)
  have hΦ : ∀ c g, synd c = 0 → synd (Φ (c, g)) = g := by
    intro c g hc
    by_cases h : g = 0
    · simp [Φ, h, hc]
    · simp only [Φ, dite_false, h]
      rw [hflip, hvec, hc, zero_add]
  refine ⟨Finset.univ.filter (fun S => synd S = 0), ?_, ?_⟩
  · have hinj : Set.InjOn Φ
        ((Finset.univ.filter (fun S => synd S = 0)) ×ˢ (Finset.univ : Finset (Fin t → ZMod 2)) :
          Finset (Finset (Fin n) × (Fin t → ZMod 2))) := by
      rintro ⟨c, g⟩ hcg ⟨c', g'⟩ hcg' heq
      have hc : synd c = 0 := by
        have := Finset.mem_coe.mp hcg; simp at this; exact this
      have hc' : synd c' = 0 := by
        have := Finset.mem_coe.mp hcg'; simp at this; exact this
      have hg : g = g' := by
        rw [← hΦ c g hc, ← hΦ c' g' hc', heq]
      subst hg
      by_cases h : g = 0
      · simp only [Φ, dite_true, h] at heq
        rw [heq]
      · simp only [Φ, dite_false, h] at heq
        have := congrArg (fun S => flip S (ε.symm ⟨g, h⟩)) heq
        simp only [hinv] at this
        rw [this]
    have := Finset.card_le_card_of_injOn Φ (t := Finset.univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
    rw [Finset.card_product, Finset.card_univ, hGc, Finset.card_univ] at this
    simpa using this
  · intro S
    by_cases h : synd S = 0
    · exact ⟨S, by simp [h], fun u v _ => Or.inl Iff.rfl⟩
    · refine ⟨flip S (ε.symm ⟨synd S, h⟩), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hflip, hvec, hG]
      · intro u v huv
        rw [hmem, hmem]
        by_cases hu : u = ε.symm ⟨synd S, h⟩
        · have hv : v ≠ ε.symm ⟨synd S, h⟩ := fun hv => huv (hu.trans hv.symm)
          right; tauto
        · left; tauto

theorem cover {n t : ℕ} (r : ℕ) (hn : n + 1 = 2 ^ t) :
    ∃ sig : ℕ → (Fin r → Fin n → Fin n → Bool × Bool), ∀ x : Fin r → Finset (Fin n),
      ∃ c < 2 ^ (r * (n - t)), acc n r (sig c) x = true := by
  classical
  obtain ⟨C, hC, hcov⟩ := hamming hn
  have htn : t ≤ n := by
    have := Nat.lt_two_pow_self (n := t)
    omega
  have hCcard : C.card ≤ 2 ^ (n - t) := by
    have h2 : 2 ^ n = 2 ^ (n - t) * 2 ^ t := by
      rw [← pow_add]; congr 1; omega
    rw [h2] at hC
    exact Nat.le_of_mul_le_mul_right hC (by positivity)
  have hD : (Fintype.piFinset (fun _ : Fin r => C)).card ≤ 2 ^ (r * (n - t)) := by
    rw [Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc C.card ^ r ≤ (2 ^ (n - t)) ^ r := Nat.pow_le_pow_left hCcard r
      _ = 2 ^ (r * (n - t)) := by rw [← pow_mul, mul_comm]
  refine ⟨fun c j u v =>
    (!decide (u ∈ ((Fintype.piFinset (fun _ : Fin r => C)).toList.getD c (fun _ => ∅)) j),
     !decide (v ∈ ((Fintype.piFinset (fun _ : Fin r => C)).toList.getD c (fun _ => ∅)) j)),
    fun x => ?_⟩
  choose f hf hf' using fun j => hcov (x j)
  have hfD : f ∈ Fintype.piFinset (fun _ : Fin r => C) := by
    rw [Fintype.mem_piFinset]; exact hf
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem (Finset.mem_toList.mpr hfD)
  have hi' : i < 2 ^ (r * (n - t)) := by
    rw [Finset.length_toList] at hi
    exact lt_of_lt_of_le hi hD
  refine ⟨i, hi', ?_⟩
  have hgetD : (Fintype.piFinset (fun _ : Fin r => C)).toList.getD i (fun _ => ∅) = f := by
    rw [List.getD_eq_getElem _ _ hi, hget]
  rw [acc_iff]
  intro j u v huv heq
  dsimp only at heq
  rw [hgetD] at heq
  simp only [Prod.mk.injEq] at heq
  have h3 := hf' j u v (ne_of_lt huv)
  by_cases h1 : u ∈ x j <;> by_cases h2 : u ∈ f j <;> by_cases h4 : v ∈ x j <;>
    by_cases h5 : v ∈ f j <;> simp_all

def histN {k : ℕ} (g : Fin k → List Bool → Bool) : ℕ → List Bool
  | 0 => []
  | m + 1 => histN g m ++ [if h : m < k then g ⟨m, h⟩ (histN g m) else false]

theorem foldl_take {k : ℕ} (g : Fin k → List Bool → Bool) (m : ℕ) (hm : m ≤ k) :
    ((List.finRange k).take m).foldl (fun hist j => hist ++ [g j hist]) [] = histN g m := by
  induction m with
  | zero => simp [histN]
  | succ m ih =>
    have hmk : m < k := hm
    rw [List.take_add_one]
    simp [List.foldl_append, ih (le_of_lt hmk), histN, hmk]

theorem foldl_eq {k : ℕ} (g : Fin k → List Bool → Bool) :
    (List.finRange k).foldl (fun hist j => hist ++ [g j hist]) [] = histN g k := by
  have h := foldl_take g k le_rfl
  rwa [List.take_of_length_le (by simp)] at h

theorem histN_length {k : ℕ} (g : Fin k → List Bool → Bool) (m : ℕ) :
    (histN g m).length = m := by
  induction m with
  | zero => simp [histN]
  | succ m ih => simp [histN, ih]

theorem card_lt_succ {k : ℕ} (F : Finset (Fin k)) (m : ℕ) (h : m < k) :
    (F.filter (fun j => j.val < m)).card + (if (⟨m, h⟩ : Fin k) ∈ F then 1 else 0)
      ≤ (F.filter (fun j => j.val < m + 1)).card := by
  split_ifs with hm
  · have hsub : insert (⟨m, h⟩ : Fin k) (F.filter (fun j => j.val < m))
        ⊆ F.filter (fun j => j.val < m + 1) := by
      intro j hj
      rw [Finset.mem_insert] at hj
      rw [Finset.mem_filter]
      rcases hj with rfl | hj
      · exact ⟨hm, Nat.lt_succ_self m⟩
      · rw [Finset.mem_filter] at hj
        exact ⟨hj.1, Nat.lt_succ_of_lt hj.2⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_insert_of_notMem (by simp)] at this
  · rw [add_zero]
    apply Finset.card_le_card
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, Nat.lt_succ_of_lt hj.2⟩

theorem hMpow {n t : ℕ} (r : ℕ) (hn : n + 1 = 2 ^ t) :
    2 ^ (r * (n - t)) * (n + 1) ^ r = (2 ^ n) ^ r := by
  have htn : t ≤ n := by
    have := Nat.lt_two_pow_self (n := t)
    omega
  rw [hn, ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htn
  simp only [Nat.add_sub_cancel_left]
  ring

theorem U1 {n t r e k : ℕ} (hn : n + 1 = 2 ^ t) (hk : (e + 1) * 2 ^ (r * (n - t)) + e ≤ k) :
    ∃ ask : Fin k → List Bool → (Fin r → Fin n → Fin n → Bool × Bool),
      ∃ answer : List Bool → Bool,
      ∀ (A : Finset (Fin r → Finset (Fin n))) (flips : Finset (Fin k)), flips.card ≤ e →
        answer ((List.finRange k).foldl (fun hist j =>
          hist ++ [rep n r A (ask j hist) != decide (j ∈ flips)]) ([] : List Bool))
          = decide A.Nonempty := by
  classical
  obtain ⟨sig, hsig⟩ := cover r hn
  refine ⟨fun _ hist => sig (hist.count false / (e + 1)),
    fun hist => decide (hist.count false < (e + 1) * 2 ^ (r * (n - t))), ?_⟩
  intro A flips hfl
  have hfold := foldl_eq (fun (j : Fin k) (hist : List Bool) =>
    rep n r A (sig (hist.count false / (e + 1))) != decide (j ∈ flips))
  dsimp only at hfold ⊢
  rw [hfold]
  generalize hg : (fun (j : Fin k) (hist : List Bool) =>
    rep n r A (sig (hist.count false / (e + 1))) != decide (j ∈ flips)) = g
  have hgv : ∀ j hist, g j hist =
      (rep n r A (sig (hist.count false / (e + 1))) != decide (j ∈ flips)) := by
    intro j hist; rw [← hg]
  have hlen := List.count_true_add_count_false (histN g k)
  rw [histN_length] at hlen
  have hfk : (flips.filter (fun j => j.val < k)).card ≤ flips.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst hA
    have hb : ∀ m, m ≤ k →
        (histN g m).count true ≤ (flips.filter (fun j => j.val < m)).card := by
      intro m
      induction m with
      | zero => intro _; simp [histN]
      | succ m ih =>
        intro hm
        have hmk : m < k := hm
        have h1 := ih (le_of_lt hmk)
        have h2 := card_lt_succ flips m hmk
        have h3 : g ⟨m, hmk⟩ (histN g m) = decide ((⟨m, hmk⟩ : Fin k) ∈ flips) := by
          rw [hgv, rep_empty]; simp
        simp only [histN, hmk, dite_true, List.count_append, h3]
        by_cases hmem : (⟨m, hmk⟩ : Fin k) ∈ flips
        · simp only [hmem, ite_true] at h2
          have hc1 : List.count true [decide ((⟨m, hmk⟩ : Fin k) ∈ flips)] = 1 := by simp [hmem]
          rw [hc1]; omega
        · simp only [hmem, ite_false] at h2
          have hc1 : List.count true [decide ((⟨m, hmk⟩ : Fin k) ∈ flips)] = 0 := by simp [hmem]
          rw [hc1]; omega
    have h1 := hb k le_rfl
    simp only [Finset.not_nonempty_empty, decide_false, decide_eq_false_iff_not, not_lt]
    omega
  · obtain ⟨x, hx⟩ := hA
    obtain ⟨c, hc, hacc⟩ := hsig x
    have hrep : rep n r A (sig c) = true := rep_of_mem hx hacc
    have hcinv : ∀ m, m ≤ k → min ((histN g m).count false - c * (e + 1)) (e + 1)
        ≤ (flips.filter (fun j => j.val < m)).card := by
      intro m
      induction m with
      | zero => intro _; simp [histN]
      | succ m ih =>
        intro hm
        have hmk : m < k := hm
        have h1 := ih (le_of_lt hmk)
        have h2 := card_lt_succ flips m hmk
        simp only [histN, hmk, dite_true, List.count_append]
        by_cases hq : (histN g m).count false / (e + 1) = c
        · have h3 : g ⟨m, hmk⟩ (histN g m) = !decide ((⟨m, hmk⟩ : Fin k) ∈ flips) := by
            rw [hgv, hq, hrep]; simp
          rw [h3]
          by_cases hmem : (⟨m, hmk⟩ : Fin k) ∈ flips
          · simp only [hmem, ite_true] at h2
            have hc1 : List.count false [!decide ((⟨m, hmk⟩ : Fin k) ∈ flips)] = 1 := by
              simp [hmem]
            rw [hc1]; omega
          · simp only [hmem, ite_false] at h2
            have hc1 : List.count false [!decide ((⟨m, hmk⟩ : Fin k) ∈ flips)] = 0 := by
              simp [hmem]
            rw [hc1]; omega
        · have hcases : (histN g m).count false < c * (e + 1) ∨
              c * (e + 1) + (e + 1) ≤ (histN g m).count false := by
            rcases Nat.lt_or_ge ((histN g m).count false) (c * (e + 1)) with h | h
            · left; exact h
            · right
              have h3 : c ≤ (histN g m).count false / (e + 1) :=
                (Nat.le_div_iff_mul_le (Nat.succ_pos e)).mpr h
              have h4 : c + 1 ≤ (histN g m).count false / (e + 1) := by omega
              have h5 := (Nat.le_div_iff_mul_le (Nat.succ_pos e)).mp h4
              rw [Nat.add_mul, Nat.one_mul] at h5
              exact h5
          have hmono : (flips.filter (fun j => j.val < m)).card
              ≤ (flips.filter (fun j => j.val < m + 1)).card := by
            split_ifs at h2 <;> omega
          have hc0 : List.count false [g ⟨m, hmk⟩ (histN g m)] ≤ 1 := by
            cases g ⟨m, hmk⟩ (histN g m) <;> simp
          omega
    have h1 := hcinv k le_rfl
    have hAne : A.Nonempty := ⟨x, hx⟩
    simp only [hAne, decide_true, decide_eq_true_eq]
    by_contra hcon
    push Not at hcon
    have h7 : c * (e + 1) + (e + 1) ≤ (e + 1) * 2 ^ (r * (n - t)) := by
      have : (c + 1) * (e + 1) ≤ 2 ^ (r * (n - t)) * (e + 1) :=
        Nat.mul_le_mul_right _ hc
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ (r * (n - t)))] at this
      exact this
    omega

theorem L1 {n t r e k : ℕ} (hn : n + 1 = 2 ^ t)
    (ask : Fin k → List Bool → (Fin r → Fin n → Fin n → Bool × Bool))
    (answer : List Bool → Bool)
    (hv : ∀ (A : Finset (Fin r → Finset (Fin n))) (flips : Finset (Fin k)), flips.card ≤ e →
        answer ((List.finRange k).foldl (fun hist j =>
          hist ++ [rep n r A (ask j hist) != decide (j ∈ flips)]) ([] : List Bool))
          = decide A.Nonempty) :
    (e + 1) * 2 ^ (r * (n - t)) + e ≤ k := by
  classical
  by_contra hcon
  push Not at hcon
  have hMp := hMpow r hn
  have hk' : (k - e) < (e + 1) * 2 ^ (r * (n - t)) := by
    have : 0 < (e + 1) * 2 ^ (r * (n - t)) := by positivity
    omega
  have hJ : (Finset.univ.filter (fun j : Fin k => j.val < k - e)).card ≤ k - e := by
    have := Finset.card_le_card_of_injOn (s := Finset.univ.filter (fun j : Fin k => j.val < k - e))
      (t := Finset.range (k - e)) (fun j : Fin k => j.val)
      (fun j hj => by
        have hj' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        exact Finset.mem_coe.mpr (Finset.mem_range.mpr hj'))
      (fun a _ b _ hab => Fin.ext hab)
    simpa using this
  have hlt : (Finset.univ.filter (fun j : Fin k => j.val < k - e)).card * (n + 1) ^ r
      < (e + 1) * (2 ^ n) ^ r := by
    calc _ ≤ (k - e) * (n + 1) ^ r := Nat.mul_le_mul_right _ hJ
      _ < (e + 1) * 2 ^ (r * (n - t)) * (n + 1) ^ r :=
          Nat.mul_lt_mul_of_pos_right hk' (by positivity)
      _ = _ := by rw [Nat.mul_assoc, hMp]
  obtain ⟨w, hw⟩ := exists_few _ (fun j : Fin k => ask j (List.replicate j.val false)) e hlt
  rw [Finset.filter_filter] at hw
  generalize hP : (Finset.univ.filter (fun j : Fin k => j.val < k - e ∧
      acc n r (ask j (List.replicate j.val false)) w = true)) = P at hw
  have hPmem : ∀ j : Fin k, j ∈ P ↔ (j.val < k - e ∧
      acc n r (ask j (List.replicate j.val false)) w = true) := by
    intro j; rw [← hP]; simp
  have hf1 := foldl_eq (fun (j : Fin k) (hist : List Bool) =>
    rep n r {w} (ask j hist) != decide (j ∈ P))
  generalize hg1 : (fun (j : Fin k) (hist : List Bool) =>
    rep n r {w} (ask j hist) != decide (j ∈ P)) = g1 at hf1
  have hg1v : ∀ j hist, g1 j hist = (acc n r (ask j hist) w != decide (j ∈ P)) := by
    intro j hist; rw [← hg1]; dsimp only; rw [rep_singleton]
  have hrepl : ∀ m, m ≤ k - e → m ≤ k → histN g1 m = List.replicate m false := by
    intro m
    induction m with
    | zero => intro _ _; simp [histN]
    | succ m ih =>
      intro hm hmk'
      have hmk : m < k := hmk'
      have h1 := ih (by omega) (le_of_lt hmk)
      have hm' : m < k - e := hm
      have h2 : g1 ⟨m, hmk⟩ (List.replicate m false) = false := by
        rw [hg1v]
        by_cases ha : acc n r (ask ⟨m, hmk⟩ (List.replicate m false)) w = true
        · have : (⟨m, hmk⟩ : Fin k) ∈ P := (hPmem _).mpr ⟨hm', ha⟩
          simp [ha, this]
        · have : (⟨m, hmk⟩ : Fin k) ∉ P := fun hc => ha ((hPmem _).mp hc).2
          simp only [Bool.not_eq_true] at ha
          simp [ha, this]
      simp only [histN, hmk, dite_true, h1, h2]
      exact (List.replicate_succ' ..).symm
  generalize hF2 : (Finset.univ.filter (fun j : Fin k => g1 j (histN g1 j.val) = true)) = F2
  have hF2mem : ∀ j : Fin k, j ∈ F2 ↔ g1 j (histN g1 j.val) = true := by
    intro j; rw [← hF2]; simp
  have hF2card : F2.card ≤ e := by
    have := Finset.card_le_card_of_injOn (s := F2) (t := Finset.range e)
      (fun j : Fin k => j.val - (k - e))
      (fun j hj => by
        have hj' := (hF2mem j).mp (Finset.mem_coe.mp hj)
        have hge : k - e ≤ j.val := by
          by_contra hlt'
          push Not at hlt'
          have h1 := hrepl j.val (le_of_lt hlt') (le_of_lt j.isLt)
          rw [h1] at hj'
          have hm' : j.val < k - e := hlt'
          have h2 : g1 j (List.replicate j.val false) = false := by
            rw [hg1v]
            by_cases ha : acc n r (ask j (List.replicate j.val false)) w = true
            · have : j ∈ P := (hPmem _).mpr ⟨hm', ha⟩
              simp [ha, this]
            · have : j ∉ P := fun hc => ha ((hPmem _).mp hc).2
              simp only [Bool.not_eq_true] at ha
              simp [ha, this]
          rw [h2] at hj'
          exact Bool.false_ne_true hj'
        have := j.isLt
        exact Finset.mem_coe.mpr (Finset.mem_range.mpr (show j.val - (k - e) < e by omega)))
      (fun a ha b hb hab => by
        have ha' := (hF2mem a).mp (Finset.mem_coe.mp ha)
        have hb' := (hF2mem b).mp (Finset.mem_coe.mp hb)
        have hgea : k - e ≤ a.val := by
          by_contra hlt'
          push Not at hlt'
          have h1 := hrepl a.val (le_of_lt hlt') (le_of_lt a.isLt)
          rw [h1, hg1v] at ha'
          by_cases hacc : acc n r (ask a (List.replicate a.val false)) w = true
          · have : a ∈ P := (hPmem _).mpr ⟨hlt', hacc⟩
            simp [hacc, this] at ha'
          · have : a ∉ P := fun hc => hacc ((hPmem _).mp hc).2
            simp only [Bool.not_eq_true] at hacc
            simp [hacc, this] at ha'
        have hgeb : k - e ≤ b.val := by
          by_contra hlt'
          push Not at hlt'
          have h1 := hrepl b.val (le_of_lt hlt') (le_of_lt b.isLt)
          rw [h1, hg1v] at hb'
          by_cases hacc : acc n r (ask b (List.replicate b.val false)) w = true
          · have : b ∈ P := (hPmem _).mpr ⟨hlt', hacc⟩
            simp [hacc, this] at hb'
          · have : b ∉ P := fun hc => hacc ((hPmem _).mp hc).2
            simp only [Bool.not_eq_true] at hacc
            simp [hacc, this] at hb'
        apply Fin.ext
        have hab' : a.val - (k - e) = b.val - (k - e) := hab
        omega)
    simpa using this
  have hf2 := foldl_eq (fun (j : Fin k) (hist : List Bool) =>
    rep n r ∅ (ask j hist) != decide (j ∈ F2))
  generalize hg2 : (fun (j : Fin k) (hist : List Bool) =>
    rep n r ∅ (ask j hist) != decide (j ∈ F2)) = g2 at hf2
  have hg2v : ∀ j hist, g2 j hist = decide (j ∈ F2) := by
    intro j hist; rw [← hg2]; dsimp only; rw [rep_empty]; simp
  have hsame : ∀ m, histN g2 m = histN g1 m := by
    intro m
    induction m with
    | zero => simp [histN]
    | succ m ih =>
      simp only [histN, ih]
      by_cases hmk : m < k
      · simp only [hmk, dite_true, hg2v]
        congr 2
        have := hF2mem ⟨m, hmk⟩
        cases hb : g1 ⟨m, hmk⟩ (histN g1 m)
        · simp [hb] at this; simp [this]
        · simp [hb] at this; simp [this]
      · simp [hmk]
  have e1 := hv {w} P hw
  have e2 := hv ∅ F2 hF2card
  rw [hf1] at e1
  rw [hf2, hsame] at e2
  rw [e1] at e2
  simp at e2

theorem foldl_map' {ι : Type} (f : ι → Bool) (l : List ι) (init : List Bool) :
    l.foldl (fun hist j => hist ++ [f j]) init = init ++ l.map f := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [List.foldl_cons, ih]

theorem U2 {n t r e k : ℕ} (hn : n + 1 = 2 ^ t) (hk : (2 * e + 1) * 2 ^ (r * (n - t)) ≤ k) :
    ∃ ask : Fin k → (Fin r → Fin n → Fin n → Bool × Bool),
      ∃ answer : List Bool → Bool,
      ∀ (A : Finset (Fin r → Finset (Fin n))) (flips : Finset (Fin k)), flips.card ≤ e →
        answer ((List.finRange k).foldl (fun hist j =>
          hist ++ [rep n r A (ask j) != decide (j ∈ flips)]) ([] : List Bool))
          = decide A.Nonempty := by
  classical
  obtain ⟨sig, hsig⟩ := cover r hn
  refine ⟨fun j => sig (j.val / (2 * e + 1)),
    fun hist => decide (∃ c < 2 ^ (r * (n - t)), e + 1 ≤ ((Finset.range (2 * e + 1)).filter
      (fun i => hist.getD (c * (2 * e + 1) + i) false = true)).card), ?_⟩
  intro A flips hfl
  have hfm := foldl_map' (fun j : Fin k => rep n r A (sig (j.val / (2 * e + 1))) != decide (j ∈ flips))
    (List.finRange k) []
  dsimp only at hfm ⊢
  rw [hfm, List.nil_append]
  have hget : ∀ (f : Fin k → Bool) (i : ℕ) (h : i < k),
      ((List.finRange k).map f).getD i false = f ⟨i, h⟩ := by
    intro f i h
    simp [List.getD_eq_getElem?_getD, h]
  have hidx : ∀ c, c < 2 ^ (r * (n - t)) → ∀ i, i < 2 * e + 1 → c * (2 * e + 1) + i < k := by
    intro c hc i hi
    have h1 : (c + 1) * (2 * e + 1) ≤ 2 ^ (r * (n - t)) * (2 * e + 1) :=
      Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ (r * (n - t)))] at h1
    omega
  have himg : (flips.image (fun j : Fin k => j.val)).card ≤ e :=
    Finset.card_image_le.trans hfl
  rcases A.eq_empty_or_nonempty with hA | hA
  · subst hA
    simp only [Finset.not_nonempty_empty, decide_false, decide_eq_false_iff_not]
    rintro ⟨c, hc, hcard⟩
    have := Finset.card_le_card_of_injOn
      (s := (Finset.range (2 * e + 1)).filter (fun i => ((List.finRange k).map
        (fun j : Fin k => rep n r ∅ (sig (j.val / (2 * e + 1))) != decide (j ∈ flips))).getD
          (c * (2 * e + 1) + i) false = true))
      (t := flips.image (fun j : Fin k => j.val)) (fun i => c * (2 * e + 1) + i)
      (fun i hi => by
        have hi' := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
        have hik := hidx c hc i (Finset.mem_range.mp hi'.1)
        have h2 := hi'.2
        rw [hget _ _ hik, rep_empty] at h2
        have h3 : (⟨c * (2 * e + 1) + i, hik⟩ : Fin k) ∈ flips := by simpa using h2
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨_, h3, rfl⟩))
      (fun a _ b _ hab => by
        have hab' : c * (2 * e + 1) + a = c * (2 * e + 1) + b := hab
        omega)
    omega
  · obtain ⟨x, hx⟩ := hA
    obtain ⟨c, hc, hacc⟩ := hsig x
    have hrep : rep n r A (sig c) = true := rep_of_mem hx hacc
    have hAne : A.Nonempty := ⟨x, hx⟩
    simp only [hAne, decide_true, decide_eq_true_eq]
    refine ⟨c, hc, ?_⟩
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.range (2 * e + 1)) (p := fun i => ((List.finRange k).map
        (fun j : Fin k => rep n r A (sig (j.val / (2 * e + 1))) != decide (j ∈ flips))).getD
          (c * (2 * e + 1) + i) false = true)
    rw [Finset.card_range] at hsplit
    have := Finset.card_le_card_of_injOn
      (s := (Finset.range (2 * e + 1)).filter (fun i => ¬ ((List.finRange k).map
        (fun j : Fin k => rep n r A (sig (j.val / (2 * e + 1))) != decide (j ∈ flips))).getD
          (c * (2 * e + 1) + i) false = true))
      (t := flips.image (fun j : Fin k => j.val)) (fun i => c * (2 * e + 1) + i)
      (fun i hi => by
        have hi' := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
        have hi2 := Finset.mem_range.mp hi'.1
        have hik := hidx c hc i hi2
        have h2 := hi'.2
        have hdiv : (c * (2 * e + 1) + i) / (2 * e + 1) = c :=
          Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)
        rw [hget _ _ hik] at h2
        dsimp only at h2
        rw [hdiv, hrep] at h2
        have h3 : (⟨c * (2 * e + 1) + i, hik⟩ : Fin k) ∈ flips := by simpa using h2
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨_, h3, rfl⟩))
      (fun a _ b _ hab => by
        have hab' : c * (2 * e + 1) + a = c * (2 * e + 1) + b := hab
        omega)
    omega

theorem L2 {n t r e k : ℕ} (hn : n + 1 = 2 ^ t)
    (ask : Fin k → (Fin r → Fin n → Fin n → Bool × Bool))
    (answer : List Bool → Bool)
    (hv : ∀ (A : Finset (Fin r → Finset (Fin n))) (flips : Finset (Fin k)), flips.card ≤ e →
        answer ((List.finRange k).foldl (fun hist j =>
          hist ++ [rep n r A (ask j) != decide (j ∈ flips)]) ([] : List Bool))
          = decide A.Nonempty) :
    (2 * e + 1) * 2 ^ (r * (n - t)) ≤ k := by
  classical
  by_contra hcon
  push Not at hcon
  have hMp := hMpow r hn
  have hlt : (Finset.univ : Finset (Fin k)).card * (n + 1) ^ r < (2 * e + 1) * (2 ^ n) ^ r := by
    rw [Finset.card_univ, Fintype.card_fin]
    calc k * (n + 1) ^ r < (2 * e + 1) * 2 ^ (r * (n - t)) * (n + 1) ^ r :=
          Nat.mul_lt_mul_of_pos_right hcon (by positivity)
      _ = _ := by rw [Nat.mul_assoc, hMp]
  obtain ⟨w, hw⟩ := exists_few _ ask (2 * e) hlt
  generalize hHs : (Finset.univ.filter (fun j : Fin k => acc n r (ask j) w = true)) = Hs at hw
  have hmemHs : ∀ j : Fin k, j ∈ Hs ↔ acc n r (ask j) w = true := by
    intro j; rw [← hHs]; simp
  obtain ⟨H1, hH1sub, hH1card⟩ := Finset.exists_subset_card_eq (min_le_right e Hs.card)
  have hH2card : (Hs \ H1).card ≤ e := by
    rw [Finset.card_sdiff_of_subset hH1sub, hH1card]
    omega
  have hH1e : H1.card ≤ e := by rw [hH1card]; exact min_le_left _ _
  have heqf : (fun (hist : List Bool) (j : Fin k) =>
      hist ++ [rep n r {w} (ask j) != decide (j ∈ H1)]) =
      (fun (hist : List Bool) (j : Fin k) =>
      hist ++ [rep n r ∅ (ask j) != decide (j ∈ Hs \ H1)]) := by
    funext hist j
    congr 2
    rw [rep_singleton, rep_empty]
    by_cases ha : acc n r (ask j) w = true
    · have hj : j ∈ Hs := (hmemHs j).mpr ha
      by_cases h1 : j ∈ H1 <;> simp [ha, h1, hj, Finset.mem_sdiff]
    · have hj : j ∉ Hs := fun hc => ha ((hmemHs j).mp hc)
      have h1 : j ∉ H1 := fun hc => hj (hH1sub hc)
      simp only [Bool.not_eq_true] at ha
      simp [ha, h1, hj, Finset.mem_sdiff]
  have e1 := hv {w} H1 hH1e
  have e2 := hv ∅ (Hs \ H1) hH2card
  rw [heqf] at e1
  rw [e1] at e2
  simp at e2

end PEqualNP.Outside.L_lib_1173

theorem PEqualNP.Outside.L_lib_1173 : ∀ (t r e k : Nat), 0 < t →
  let n := 2 ^ t - 1
  let Site := Fin n
  let Word := Fin r → Finset Site
  let Signing := Fin r → Site → Site → Bool × Bool
  let sites := (Finset.univ : Finset Site).toList
  let blocks := (Finset.univ : Finset (Fin r)).toList
  let reply := fun (A : Finset Word) (s : Signing) => A.toList.any (fun x =>
    blocks.all (fun j => sites.all (fun u => sites.all (fun v =>
      !(decide (u < v)) || ((decide (u ∈ x j), decide (v ∈ x j)) != s j u v)))))
  let valid := fun (ask : Fin k → List Bool → Signing) (answer : List Bool → Bool) =>
    ∀ (A : Finset Word) (flips : Finset (Fin k)), flips.card ≤ e →
      answer ((List.finRange k).foldl (fun hist j =>
        hist ++ [reply A (ask j hist) != decide (j ∈ flips)]) ([] : List Bool)) = decide A.Nonempty
  let M := 2 ^ (r * (n - t))
  ((∃ ask : Fin k → List Bool → Signing, ∃ answer, valid ask answer) ↔ (e + 1) * M + e ≤ k) ∧
  ((∃ ask : Fin k → Signing, ∃ answer, valid (fun j _ => ask j) answer) ↔ (2 * e + 1) * M ≤ k) := by
  intro t r e k ht
  have hn : (2 ^ t - 1) + 1 = 2 ^ t := by
    have := Nat.one_le_two_pow (n := t)
    omega
  intro n Site Word Signing sites blocks reply valid M
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨ask, answer, hv⟩
    exact PEqualNP.Outside.L_lib_1173.L1 hn ask answer hv
  · intro hk
    exact PEqualNP.Outside.L_lib_1173.U1 hn hk
  · rintro ⟨ask, answer, hv⟩
    exact PEqualNP.Outside.L_lib_1173.L2 hn ask answer hv
  · intro hk
    exact PEqualNP.Outside.L_lib_1173.U2 hn hk
