import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_825_aux
open PEqualNP.CircuitLowerBounds

noncomputable def pr (g : Gate) : Bool := @decide
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)
noncomputable def cost (gs : List Gate) : ℕ := gs.countP pr
def okg (g : Gate) : Prop := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))
def wr (gs : List Gate) (x : List Bool) : List Bool := (Circuit.mk gs 0).wires x
def RB (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j
def Good (n : ℕ) (gs : List Gate) : Prop := RB n gs ∧ ∀ g ∈ gs, okg g
def Rel (t : ℕ) (gs G' : List Gate) (α : ℕ → Bool) (m : ℕ → ℕ)
    (ok : Bool → (Fin t → Bool) → Prop) : Prop :=
  ∀ i < 1 + t + gs.length, m i < t + G'.length ∧ ∀ u z, ok u z →
    (wr gs (u :: List.ofFn z)).getD i false =
      xor (α i && u) ((wr G' (List.ofFn z)).getD (m i) false)
def P1 (t : ℕ) (gs : List Gate) : Prop := ∃ G' α m, Good t G' ∧ cost G' ≤ cost gs ∧
  Rel t gs G' α m (fun _ _ => True)
def P2 (t : ℕ) (gs : List Gate) (p : (Fin t → Bool) → Bool) : Prop :=
  ∀ b : Bool, ∃ G' α m c, Good t G' ∧ cost G' < cost gs ∧ c < t + G'.length ∧
    (∀ z, (wr G' (List.ofFn z)).getD c false = xor (p z) b) ∧
    Rel t gs G' α m (fun u z => u = xor (p z) b)

theorem wr_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wr (gs ++ [g]) x = wr gs x ++ [g.op.eval (g.inputs.map fun i => (wr gs x).getD i false)] := by
  simp [wr, Circuit.wires, List.foldl_append]

theorem wr_len (gs : List Gate) (x : List Bool) : (wr gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wr, Circuit.wires]
  | append_singleton gs g ih => rw [wr_snoc]; simp [ih]; omega

theorem getD_snoc_lt (G : List Gate) (g : Gate) (x : List Bool) (c : ℕ)
    (hc : c < x.length + G.length) :
    (wr (G ++ [g]) x).getD c false = (wr G x).getD c false := by
  rw [wr_snoc, List.getD_append _ _ _ _ (by rw [wr_len]; exact hc)]

theorem getD_snoc_eq (G : List Gate) (g : Gate) (x : List Bool) :
    (wr (G ++ [g]) x).getD (x.length + G.length) false =
      g.op.eval (g.inputs.map fun i => (wr G x).getD i false) := by
  rw [wr_snoc, List.getD_append_right _ _ _ _ (by rw [wr_len])]
  simp [wr_len]

theorem cost_snoc (gs : List Gate) (g : Gate) :
    cost (gs ++ [g]) = cost gs + (if pr g = true then 1 else 0) := by
  simp [cost, List.countP_append, List.countP_cons]

theorem Good_snoc (n : ℕ) (G : List Gate) (g : Gate) (hG : Good n G) (hg : okg g)
    (hin : ∀ i ∈ g.inputs, i < n + G.length) : Good n (G ++ [g]) := by
  refine ⟨fun j hj i hi => ?_, fun x hx => ?_⟩
  · by_cases h : j < G.length
    · rw [List.getD_append _ _ _ _ h] at hi
      exact hG.1 j h i hi
    · have hj' : j = G.length := by simp at hj; omega
      subst hj'
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      simp at hi
      exact hin i hi
  · rcases List.mem_append.1 hx with h | h
    · exact hG.2 x h
    · simp at h; subst h; exact hg

theorem Good_init (n : ℕ) (G : List Gate) (g : Gate) (h : Good n (G ++ [g])) :
    Good n G ∧ okg g ∧ ∀ i ∈ g.inputs, i < n + G.length := by
  refine ⟨⟨fun j hj i hi => ?_, fun x hx => h.2 x (by simp [hx])⟩, h.2 g (by simp), fun i hi => ?_⟩
  · have := h.1 j (by simp; omega) i
    rw [List.getD_append _ _ _ _ hj] at this
    exact this hi
  · have := h.1 G.length (by simp) i
    rw [List.getD_append_right _ _ _ _ (le_refl _)] at this
    simp at this
    exact this hi

theorem Rel_pad (t : ℕ) (gs G' : List Gate) (α : ℕ → Bool) (m : ℕ → ℕ)
    (ok : Bool → (Fin t → Bool) → Prop) (x : Gate) (hR : Rel t gs G' α m ok) :
    Rel t gs (G' ++ [x]) α m ok := by
  intro i hi
  obtain ⟨h1, h2⟩ := hR i hi
  refine ⟨by simp; omega, fun u z hok => ?_⟩
  rw [getD_snoc_lt _ _ _ _ (by simpa using h1)]
  exact h2 u z hok

theorem step (t : ℕ) (gs G' : List Gate) (α : ℕ → Bool) (m : ℕ → ℕ)
    (ok : Bool → (Fin t → Bool) → Prop) (g g' : Gate) (a : Bool)
    (hR : Rel t gs G' α m ok)
    (hv : ∀ u z, ok u z →
      g.op.eval (g.inputs.map fun i => (wr gs (u :: List.ofFn z)).getD i false) =
        xor (a && u) (g'.op.eval (g'.inputs.map fun i => (wr G' (List.ofFn z)).getD i false))) :
    Rel t (gs ++ [g]) (G' ++ [g'])
      (Function.update α (1 + t + gs.length) a)
      (Function.update m (1 + t + gs.length) (t + G'.length)) ok := by
  intro i hi
  by_cases h : i = 1 + t + gs.length
  · subst h
    refine ⟨by simp, fun u z hok => ?_⟩
    simp only [Function.update_self]
    have e1 := getD_snoc_eq gs g (u :: List.ofFn z)
    have e2 := getD_snoc_eq G' g' (List.ofFn z)
    simp only [List.length_cons, List.length_ofFn] at e1 e2
    rw [show 1 + t + gs.length = t + 1 + gs.length by omega, e1, e2]
    exact hv u z hok
  · have hi' : i < 1 + t + gs.length := by simp at hi; omega
    obtain ⟨h1, h2⟩ := hR i hi'
    simp only [Function.update_of_ne h]
    refine ⟨by simp; omega, fun u z hok => ?_⟩
    rw [getD_snoc_lt _ _ _ _ (by simp; omega), getD_snoc_lt _ _ _ _ (by simpa using h1)]
    exact h2 u z hok

theorem free_step (t : ℕ) (gs G' : List Gate) (α : ℕ → Bool) (m : ℕ → ℕ)
    (ok : Bool → (Fin t → Bool) → Prop) (g : Gate) (hG : Good t G')
    (hR : Rel t gs G' α m ok) (hg : okg g) (hin : ∀ i ∈ g.inputs, i < 1 + t + gs.length)
    (hfree : pr g = true → ∀ i ∈ g.inputs, α i = false) :
    ∃ g' α' m', Good t (G' ++ [g']) ∧ pr g' = pr g ∧
      Rel t (gs ++ [g]) (G' ++ [g']) α' m' ok := by
  refine ⟨⟨g.op, g.inputs.map m⟩, _, _, ?_, ?_,
    step t gs G' α m ok g ⟨g.op, g.inputs.map m⟩
      (g.inputs.foldr (fun i acc => xor (α i) acc) false) hR ?_⟩
  · refine Good_snoc t G' _ hG ?_ ?_
    · obtain ⟨h1, h2⟩ := hg
      exact ⟨by simpa using h1, by simpa using h2⟩
    · intro i hi
      simp only [List.mem_map] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      exact (hR k (hin k hk)).1
  · simp [pr]
  · intro u z hok
    obtain ⟨op, ins⟩ := g
    obtain ⟨hl, hop⟩ := hg
    simp only at hl hop hin hfree ⊢
    rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · rcases hop with rfl | rfl | rfl | ⟨rfl, h⟩ <;> simp_all [GateOp.eval]
    · have hi := (hR i (hin i (by simp))).2 u z hok
      simp only [List.map, List.foldr]
      rw [hi]
      rcases hop with rfl | rfl | rfl | ⟨rfl, h⟩ <;>
        cases α i <;> cases u <;> cases ((wr G' (List.ofFn z)).getD (m i) false) <;>
        simp [GateOp.eval]
    · have hi := (hR i (hin i (by simp))).2 u z hok
      have hj := (hR j (hin j (by simp))).2 u z hok
      simp only [List.map, List.foldr]
      rw [hi, hj]
      rcases hop with rfl | rfl | rfl | ⟨rfl, h⟩
      · have h1 := hfree (by simp [pr]) i (by simp)
        have h2 := hfree (by simp [pr]) j (by simp)
        simp [h1, h2, GateOp.eval]
      · have h1 := hfree (by simp [pr]) i (by simp)
        have h2 := hfree (by simp [pr]) j (by simp)
        simp [h1, h2, GateOp.eval]
      · cases α i <;> cases α j <;> cases u <;>
          cases ((wr G' (List.ofFn z)).getD (m i) false) <;>
          cases ((wr G' (List.ofFn z)).getD (m j) false) <;> simp [GateOp.eval]
      · simp at h
    · simp at hl

theorem val_snoc (t : ℕ) (G : List Gate) (g : Gate) (z : Fin t → Bool) :
    (wr (G ++ [g]) (List.ofFn z)).getD (t + G.length) false =
      g.op.eval (g.inputs.map fun i => (wr G (List.ofFn z)).getD i false) := by
  simpa using getD_snoc_eq G g (List.ofFn z)

theorem val_lt (t : ℕ) (G : List Gate) (g : Gate) (z : Fin t → Bool) (j : ℕ)
    (h : j < t + G.length) :
    (wr (G ++ [g]) (List.ofFn z)).getD j false = (wr G (List.ofFn z)).getD j false :=
  getD_snoc_lt _ _ _ _ (by simpa using h)

def Ext (G G2 : List Gate) : Prop := G.length ≤ G2.length ∧
  ∀ (x : List Bool) (j : ℕ), j < x.length + G.length →
    (wr G2 x).getD j false = (wr G x).getD j false

theorem Ext_refl (G : List Gate) : Ext G G := ⟨le_refl _, fun _ _ _ => rfl⟩
theorem Ext_snoc (G : List Gate) (g : Gate) : Ext G (G ++ [g]) :=
  ⟨by simp, fun x j h => getD_snoc_lt G g x j h⟩
theorem Ext_trans {A B C : List Gate} (h1 : Ext A B) (h2 : Ext B C) : Ext A C :=
  ⟨le_trans h1.1 h2.1, fun x j h => by
    rw [h2.2 x j (by have := h1.1; omega), h1.2 x j h]⟩

theorem Ext_val {t : ℕ} {A B : List Gate} (h : Ext A B) (z : Fin t → Bool) (j : ℕ)
    (hj : j < t + A.length) :
    (wr B (List.ofFn z)).getD j false = (wr A (List.ofFn z)).getD j false :=
  h.2 _ j (by simpa using hj)

theorem Rel_ext (t : ℕ) (gs G' G2 : List Gate) (α : ℕ → Bool) (m : ℕ → ℕ)
    (ok : Bool → (Fin t → Bool) → Prop) (hE : Ext G' G2) (hR : Rel t gs G' α m ok) :
    Rel t gs G2 α m ok := by
  intro i hi
  obtain ⟨h1, h2⟩ := hR i hi
  refine ⟨by have := hE.1; omega, fun u z hok => ?_⟩
  rw [Ext_val hE z _ h1]
  exact h2 u z hok

theorem Rel_mono (t : ℕ) (gs G' : List Gate) (α : ℕ → Bool) (m : ℕ → ℕ)
    (ok ok' : Bool → (Fin t → Bool) → Prop) (h : ∀ u z, ok' u z → ok u z)
    (hR : Rel t gs G' α m ok) : Rel t gs G' α m ok' :=
  fun i hi => ⟨(hR i hi).1, fun u z hok => (hR i hi).2 u z (h u z hok)⟩

theorem mat (t : ℕ) (gs G' : List Gate) (α : ℕ → Bool) (m : ℕ → ℕ)
    (ok : Bool → (Fin t → Bool) → Prop) (c : ℕ) (hG : Good t G') (hc : c < t + G'.length)
    (hcv : ∀ u z, ok u z → (wr G' (List.ofFn z)).getD c false = u)
    (hR : Rel t gs G' α m ok) (i : ℕ) (hi : i < 1 + t + gs.length) (e : Bool) :
    ∃ G'' k, Good t G'' ∧ cost G'' = cost G' ∧ Ext G' G'' ∧ k < t + G''.length ∧
      ∀ u z, ok u z → (wr G'' (List.ofFn z)).getD k false =
        xor ((wr gs (u :: List.ofFn z)).getD i false) (e && u) := by
  obtain ⟨h1, h2⟩ := hR i hi
  by_cases hx : xor (α i) e = false
  · refine ⟨G', m i, hG, rfl, Ext_refl _, h1, fun u z hok => ?_⟩
    rw [h2 u z hok]
    revert hx
    cases α i <;> cases e <;> cases u <;>
      cases ((wr G' (List.ofFn z)).getD (m i) false) <;> simp
  · have hG1 : Good t (G' ++ [Gate.mk (GateOp.mod 2) [m i, c]]) :=
      Good_snoc t G' _ hG (by simp [okg]) (by
        intro k hk; simp at hk; rcases hk with rfl | rfl <;> assumption)
    refine ⟨G' ++ [Gate.mk (GateOp.mod 2) [m i, c]] ++ [Gate.mk GateOp.not [t + G'.length]],
      t + (G' ++ [Gate.mk (GateOp.mod 2) [m i, c]]).length,
      Good_snoc t _ _ hG1 (by simp [okg]) (by simp), ?_,
      Ext_trans (Ext_snoc _ _) (Ext_snoc _ _), by simp, fun u z hok => ?_⟩
    · rw [cost_snoc, cost_snoc]; simp [pr]
    · rw [val_snoc]
      simp only [List.map]
      rw [val_snoc]
      simp only [List.map]
      rw [hcv u z hok, h2 u z hok]
      revert hx
      cases α i <;> cases e <;> cases u <;>
        cases ((wr G' (List.ofFn z)).getD (m i) false) <;> simp [GateOp.eval]

theorem pr_two (g : Gate) (h : pr g = true) :
    ∃ i j, g.inputs = [i, j] ∧ (g.op = .and ∨ g.op = .or) := by
  simp only [pr, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨op, ins⟩ := g
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩ <;> simp at h2
  exact ⟨i, j, rfl, h1⟩

theorem costly_step (t : ℕ) (gs G' : List Gate) (α : ℕ → Bool) (m : ℕ → ℕ)
    (p : (Fin t → Bool) → Bool) (b : Bool) (c : ℕ) (g : Gate) (hG : Good t G')
    (hc : c < t + G'.length)
    (hcv : ∀ z, (wr G' (List.ofFn z)).getD c false = xor (p z) b)
    (hR : Rel t gs G' α m (fun u z => u = xor (p z) b))
    (hin : ∀ i ∈ g.inputs, i < 1 + t + gs.length) (hpr : pr g = true) :
    ∃ G'' α' m' c', Good t G'' ∧ cost G'' = cost G' + 1 ∧ c' < t + G''.length ∧
      (∀ z, (wr G'' (List.ofFn z)).getD c' false = xor (p z) b) ∧
      Rel t (gs ++ [g]) G'' α' m' (fun u z => u = xor (p z) b) := by
  obtain ⟨i, j, hij, hop⟩ := pr_two g hpr
  obtain ⟨op, ins⟩ := g
  simp only at hij hop hin
  subst hij
  obtain ⟨G1, k1, hG1, hc1, hE1, hk1, hv1⟩ := mat t gs G' α m _ c hG hc
    (fun u z hok => by rw [hcv z]; exact hok.symm) hR i (hin i (by simp)) false
  have hR1 := Rel_ext t gs G' G1 α m _ hE1 hR
  obtain ⟨G2, k2, hG2, hc2, hE2, hk2, hv2⟩ := mat t gs G1 α m _ c hG1
    (by have := hE1.1; omega)
    (fun u z hok => by rw [Ext_val hE1 z _ hc, hcv z]; exact hok.symm) hR1 j
    (hin j (by simp)) false
  have hR2 := Rel_ext t gs G1 G2 α m _ hE2 hR1
  have hE := Ext_trans hE1 hE2
  refine ⟨G2 ++ [⟨op, [k1, k2]⟩], _, _, c,
    Good_snoc t G2 _ hG2 ⟨by simp, by rcases hop with h | h <;> simp [h]⟩ (by
      intro k hk; simp at hk; have := hE2.1; rcases hk with rfl | rfl <;> omega), ?_,
    by simp; have := hE.1; omega, fun z => ?_,
    step t gs G2 α m _ ⟨op, [i, j]⟩ ⟨op, [k1, k2]⟩ false hR2 ?_⟩
  · have hpr' : pr ⟨op, [k1, k2]⟩ = true := by
      simp only [pr, decide_eq_true_eq] at hpr ⊢; exact ⟨hpr.1, rfl⟩
    rw [cost_snoc, hc2, hc1, if_pos hpr']
  · rw [val_lt _ _ _ _ _ (by have := hE.1; omega), Ext_val hE z _ hc, hcv z]
  · intro u z hok
    simp only [List.map]
    rw [hv2 u z hok, Ext_val hE2 z _ hk1, hv1 u z hok]
    simp

theorem cwire (t : ℕ) (G' : List Gate) (hG : Good t G') (mi : ℕ) (hmi : mi < t + G'.length)
    (b : Bool) : ∃ G1 c, Good t G1 ∧ cost G1 = cost G' ∧ Ext G' G1 ∧ c < t + G1.length ∧
      ∀ z : Fin t → Bool, (wr G1 (List.ofFn z)).getD c false =
        xor ((wr G' (List.ofFn z)).getD mi false) b := by
  have hG1 : Good t (G' ++ [Gate.mk (GateOp.mod 2) [mi]]) :=
    Good_snoc t G' _ hG (by simp [okg]) (by simpa using hmi)
  cases b
  · refine ⟨G' ++ [Gate.mk (GateOp.mod 2) [mi]] ++ [Gate.mk GateOp.not [t + G'.length]],
      t + (G' ++ [Gate.mk (GateOp.mod 2) [mi]]).length,
      Good_snoc t _ _ hG1 (by simp [okg]) (by simp), ?_,
      Ext_trans (Ext_snoc _ _) (Ext_snoc _ _), by simp, fun z => ?_⟩
    · rw [cost_snoc, cost_snoc]; simp [pr]
    · rw [val_snoc]
      simp only [List.map]
      rw [val_snoc]
      simp only [List.map]
      cases ((wr G' (List.ofFn z)).getD mi false) <;> simp [GateOp.eval]
  · refine ⟨G' ++ [Gate.mk (GateOp.mod 2) [mi]], t + G'.length, hG1, ?_, Ext_snoc _ _, by simp,
      fun z => ?_⟩
    · rw [cost_snoc]; simp [pr]
    · rw [val_snoc]
      simp only [List.map]
      cases ((wr G' (List.ofFn z)).getD mi false) <;> simp [GateOp.eval]

theorem special_aux (t : ℕ) (gs G' : List Gate) (α : ℕ → Bool) (m : ℕ → ℕ) (g : Gate)
    (hG : Good t G') (hR : Rel t gs G' α m (fun _ _ => True))
    (i o : ℕ) (hi : i < 1 + t + gs.length) (ho : o < 1 + t + gs.length) (hα : α i = true)
    (isand : Bool)
    (hval : ∀ w : ℕ → Bool, g.op.eval (g.inputs.map w) =
      bif isand then (w i && w o) else (w i || w o)) :
    ∃ p : (Fin t → Bool) → Bool, ∀ b : Bool, ∃ G'' α' m' c, Good t G'' ∧
      cost G'' = cost G' ∧ c < t + G''.length ∧
      (∀ z, (wr G'' (List.ofFn z)).getD c false = xor (p z) b) ∧
      Rel t (gs ++ [g]) G'' α' m' (fun u z => u = xor (p z) b) := by
  refine ⟨fun z => (wr G' (List.ofFn z)).getD (m i) false, fun b => ?_⟩
  obtain ⟨G1, c, hG1, hc1, hE1, hc, hcv⟩ := cwire t G' hG (m i) (hR i hi).1 b
  have hR1 : Rel t gs G1 α m
      (fun u z => u = xor ((wr G' (List.ofFn z)).getD (m i) false) b) :=
    Rel_ext t gs G' G1 α m _ hE1 (Rel_mono t gs G' α m _ _ (fun _ _ _ => trivial) hR)
  obtain ⟨G2, k, hG2, hc2, hE2, hk, hv⟩ := mat t gs G1 α m _ c hG1 hc
    (fun u z hok => by rw [hcv z]; exact hok.symm) hR1 o ho false
  have hR2 := Rel_ext t gs G1 G2 α m _ hE2 hR1
  have hE := Ext_trans hE1 hE2
  obtain ⟨g', hg'1, hg'2, hg'3, hg'4⟩ : ∃ g' : Gate, okg g' ∧ pr g' = false ∧
      (∀ x ∈ g'.inputs, x = k) ∧ ∀ w : ℕ → Bool, g'.op.eval (g'.inputs.map w) =
        bif isand then (b && w k) else (b || w k) := by
    cases b <;> cases isand
    · exact ⟨⟨GateOp.or, [k]⟩, by simp [okg], by simp [pr], by simp, by simp [GateOp.eval]⟩
    · exact ⟨⟨GateOp.or, []⟩, by simp [okg], by simp [pr], by simp, by simp [GateOp.eval]⟩
    · exact ⟨⟨GateOp.and, []⟩, by simp [okg], by simp [pr], by simp, by simp [GateOp.eval]⟩
    · exact ⟨⟨GateOp.and, [k]⟩, by simp [okg], by simp [pr], by simp, by simp [GateOp.eval]⟩
  refine ⟨G2 ++ [g'], _, _, c,
    Good_snoc t G2 _ hG2 hg'1 (by intro x hx; rw [hg'3 x hx]; exact hk), ?_,
    by simp; have := hE2.1; omega, fun z => ?_,
    step t gs G2 α m _ g g' false hR2 ?_⟩
  · rw [cost_snoc, hc2, hc1]; simp [hg'2]
  · rw [val_lt _ _ _ _ _ (by have := hE2.1; omega), Ext_val hE2 z _ hc, hcv z]
  · intro u z hok
    rw [hval (fun i => (wr gs (u :: List.ofFn z)).getD i false),
      hg'4 (fun i => (wr G2 (List.ofFn z)).getD i false)]
    beta_reduce
    rw [hv u z hok, (hR i hi).2 u z trivial, hα]
    generalize (wr gs (u :: List.ofFn z)).getD o false = X
    have hok' : u = xor ((wr G' (List.ofFn z)).getD (m i) false) b := hok
    generalize (wr G' (List.ofFn z)).getD (m i) false = v at hok' ⊢
    subst hok'
    cases b <;> cases isand <;> cases v <;> cases X <;> simp

theorem special (t : ℕ) (gs G' : List Gate) (α : ℕ → Bool) (m : ℕ → ℕ) (g : Gate)
    (hG : Good t G') (hR : Rel t gs G' α m (fun _ _ => True))
    (hin : ∀ i ∈ g.inputs, i < 1 + t + gs.length) (hpr : pr g = true)
    (i : ℕ) (hi : i ∈ g.inputs) (hα : α i = true) :
    ∃ p : (Fin t → Bool) → Bool, ∀ b : Bool, ∃ G'' α' m' c, Good t G'' ∧
      cost G'' = cost G' ∧ c < t + G''.length ∧
      (∀ z, (wr G'' (List.ofFn z)).getD c false = xor (p z) b) ∧
      Rel t (gs ++ [g]) G'' α' m' (fun u z => u = xor (p z) b) := by
  obtain ⟨i1, i2, hij, hop⟩ := pr_two g hpr
  obtain ⟨op, ins⟩ := g
  simp only at hij hop hin hi
  subst hij
  have h1 := hin i1 (by simp)
  have h2 := hin i2 (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rcases hop with rfl | rfl
  · exact special_aux t gs G' α m _ hG hR i i2 h1 h2 hα true (by simp [GateOp.eval])
  · exact special_aux t gs G' α m _ hG hR i i2 h1 h2 hα false (by simp [GateOp.eval])
  · exact special_aux t gs G' α m _ hG hR i i1 h2 h1 hα true
      (by simp [GateOp.eval, Bool.and_comm])
  · exact special_aux t gs G' α m _ hG hR i i1 h2 h1 hα false
      (by simp [GateOp.eval, Bool.or_comm])

theorem main (t : ℕ) (gs : List Gate) (h : Good (1 + t) gs) :
    P1 t gs ∨ ∃ p, P2 t gs p := by
  induction gs using List.reverseRecOn with
  | nil =>
    left
    refine ⟨[] ++ [⟨GateOp.or, []⟩], fun i => decide (i = 0), fun i => if i = 0 then t else i - 1,
      Good_snoc t [] _ ⟨fun j hj => by simp at hj, fun g hg => by simp at hg⟩
        ⟨by simp, Or.inr (Or.inl rfl)⟩ (by simp), by simp [cost, pr], ?_⟩
    intro i hi
    refine ⟨by simp at hi ⊢; split <;> omega, fun u z _ => ?_⟩
    rcases i with _ | i
    · have e := getD_snoc_eq [] ⟨GateOp.or, []⟩ (List.ofFn z)
      simp only [List.length_ofFn, List.length_nil, Nat.add_zero] at e
      simp [e, wr, Circuit.wires, GateOp.eval]
    · have hi' : i < t := by simp at hi; omega
      rw [getD_snoc_lt _ _ _ _ (by simp; omega)]
      simp [wr, Circuit.wires]
  | append_singleton gs g ih =>
    obtain ⟨hgs, hg, hin⟩ := Good_init _ _ _ h
    rcases ih hgs with ⟨G', α, m, hG, hc, hR⟩ | ⟨p, hP⟩
    · by_cases hf : pr g = true → ∀ i ∈ g.inputs, α i = false
      · left
        obtain ⟨g', α', m', h1, h2, h3⟩ := free_step t gs G' α m _ g hG hR hg hin hf
        exact ⟨_, α', m', h1, by rw [cost_snoc, cost_snoc, h2]; omega, h3⟩
      · right
        push_neg at hf
        obtain ⟨hpr, i, hi, hα⟩ := hf
        obtain ⟨p, hp⟩ := special t gs G' α m g hG hR hin hpr i hi (by simpa using hα)
        refine ⟨p, fun b => ?_⟩
        obtain ⟨G'', α', m', c, h1, h2, h3, h4, h5⟩ := hp b
        exact ⟨G'', α', m', c, h1, by rw [cost_snoc, h2, if_pos hpr]; omega, h3, h4, h5⟩
    · right
      refine ⟨p, fun b => ?_⟩
      obtain ⟨G', α, m, c, hG, hc, hcl, hcv, hR⟩ := hP b
      by_cases hf : pr g = true → ∀ i ∈ g.inputs, α i = false
      · obtain ⟨g', α', m', h1, h2, h3⟩ := free_step t gs G' α m _ g hG hR hg hin hf
        refine ⟨_, α', m', c, h1, by rw [cost_snoc, cost_snoc, h2]; omega, by simp; omega,
          fun z => ?_, h3⟩
        rw [getD_snoc_lt _ _ _ _ (by simpa using hcl)]
        exact hcv z
      · push_neg at hf
        obtain ⟨G'', α', m', c', h1, h2, h3, h4, h5⟩ :=
          costly_step t gs G' α m p b c g hG hcl hcv hR hin hf.1
        exact ⟨G'', α', m', c', h1, by rw [cost_snoc, h2, if_pos hf.1]; omega, h3, h4, h5⟩

theorem outB (t : ℕ) (C : Circuit) (p : (Fin t → Bool) → Bool) (h : P2 t C.gates p) (b d : Bool) :
    ∃ D : Circuit, Good t D.gates ∧ cost D.gates < cost C.gates ∧
      ∀ z : Fin t → Bool, D.eval (List.ofFn z) =
        xor (C.eval (xor (p z) b :: List.ofFn z)) (d && xor (p z) b) := by
  obtain ⟨G', α, m, c, hG, hc, hcl, hcv, hR⟩ := h b
  have e1 : ∀ x, C.eval x = (wr C.gates x).getD C.output false := fun _ => rfl
  have e2 : ∀ (G : List Gate) (o : ℕ) (x : List Bool),
      (Circuit.mk G o).eval x = (wr G x).getD o false := fun _ _ _ => rfl
  by_cases ho : C.output < 1 + t + C.gates.length
  · obtain ⟨G2, k, hG2, hc2, hE2, hk, hv⟩ := mat t C.gates G' α m _ c hG hcl
      (fun u z hok => by rw [hcv z]; exact hok.symm) hR C.output ho d
    refine ⟨⟨G2, k⟩, hG2, by rw [hc2]; exact hc, fun z => ?_⟩
    rw [e1]
    exact hv _ z rfl
  · have h1 : ∀ x : List Bool, x.length = 1 + t →
        (wr C.gates x).getD C.output false = false := by
      intro x hx; apply List.getD_eq_default; rw [wr_len]; omega
    cases d
    · refine ⟨⟨G', t + G'.length⟩, hG, hc, fun z => ?_⟩
      rw [e1, h1 _ (by simp; omega)]
      have : (wr G' (List.ofFn z)).getD (t + G'.length) false = false := by
        apply List.getD_eq_default; rw [wr_len]; simp
      rw [e2, this]; simp
    · refine ⟨⟨G', c⟩, hG, hc, fun z => ?_⟩
      rw [e1, h1 _ (by simp; omega)]
      rw [e2, hcv z]; simp

theorem outA (t : ℕ) (C : Circuit) (h : P1 t C.gates) :
    ∃ (a : Bool) (E : Circuit), Good t E.gates ∧ cost E.gates ≤ cost C.gates ∧
      ∀ (u : Bool) (z : Fin t → Bool), C.eval (u :: List.ofFn z) =
        xor (a && u) (E.eval (List.ofFn z)) := by
  obtain ⟨G', α, m, hG, hc, hR⟩ := h
  by_cases ho : C.output < 1 + t + C.gates.length
  · refine ⟨α C.output, ⟨G', m C.output⟩, hG, hc, fun u z => ?_⟩
    exact (hR _ ho).2 u z trivial
  · refine ⟨false, ⟨G', t + G'.length⟩, hG, hc, fun u z => ?_⟩
    have h1 : (wr C.gates (u :: List.ofFn z)).getD C.output false = false := by
      apply List.getD_eq_default; rw [wr_len]; simp; omega
    have h2 : (wr G' (List.ofFn z)).getD (t + G'.length) false = false := by
      apply List.getD_eq_default; rw [wr_len]; simp
    have e1 : C.eval (u :: List.ofFn z) =
        (wr C.gates (u :: List.ofFn z)).getD C.output false := rfl
    have e2 : (Circuit.mk G' (t + G'.length)).eval (List.ofFn z) =
        (wr G' (List.ofFn z)).getD (t + G'.length) false := rfl
    rw [e1, e2, h1, h2]; rfl

end PEqualNP.Outside.L_lib_825_aux

theorem PEqualNP.Outside.L_lib_825 : ∀ t : ℕ,
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (nW : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack nW C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)))
  let cost := fun (C : Circ) =>
    C.gates.countP (fun g => @decide
      ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _))
  let Z := Fin t → Bool
  ∀ C : Circ, legal (1+t) C →
    (∃ (a : Bool) (E : Circ), legal t E ∧ cost E ≤ cost C ∧
      ∀ (u : Bool) (z : Z), C.eval (u :: List.ofFn z) =
        Bool.xor (a && u) (E.eval (List.ofFn z))) ∨
    (0 < cost C ∧ ∃ p : Z → Bool,
      ∀ (b d : Bool), ∃ D : Circ, legal t D ∧ cost D < cost C ∧
        ∀ z : Z, let u := Bool.xor (p z) b
          D.eval (List.ofFn z) = Bool.xor (C.eval (u :: List.ofFn z)) (d && u)) := by
  intro t Circ legal cost Z C hC
  have hG : PEqualNP.Outside.L_lib_825_aux.Good (1 + t) C.gates := hC
  rcases PEqualNP.Outside.L_lib_825_aux.main t C.gates hG with h | ⟨p, h⟩
  · left
    exact PEqualNP.Outside.L_lib_825_aux.outA t C h
  · right
    refine ⟨?_, p, fun b d => ?_⟩
    · obtain ⟨G', _, _, _, _, hc, _⟩ := h true
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) hc
    · exact PEqualNP.Outside.L_lib_825_aux.outB t C p h b d
