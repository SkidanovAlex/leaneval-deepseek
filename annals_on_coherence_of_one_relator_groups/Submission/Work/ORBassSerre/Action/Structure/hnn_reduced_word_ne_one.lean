import Mathlib
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORBassSerre.Action.Cocompact
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Seg.exists_finset_arrows
import Submission.Work.ORBassSerre.Tree.Walk.exists_consecutive_backtrack_of_closed_walk

namespace Work.ORBassSerre.Action.Structure

open Quiver

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-! ### Elementary facts about trees, stabilizers and the action on arrows -/

/-- Projection of the action on arrows (a form rewriting can use syntactically). -/
theorem total_smul_left (g : G) (X : Quiver.Total V) : (g • X).left = g • X.left :=
  Work.ORBassSerre.GraphAction.smul_left g X

/-- Projection of the action on arrows (a form rewriting can use syntactically). -/
theorem total_smul_right (g : G) (X : Quiver.Total V) : (g • X).right = g • X.right :=
  Work.ORBassSerre.GraphAction.smul_right g X

/-- The action on arrows commutes with reversal (a form rewriting can use syntactically). -/
theorem total_smul_reverse (g : G) (X : Quiver.Total V) :
    g • X.reverse = (g • X).reverse :=
  Work.ORBassSerre.GraphAction.smul_reverse g X

/-- Cancellation of a group element acting on arrows. -/
theorem smul_left_cancel' (g : G) {X Y : Quiver.Total V} (h : g • X = g • Y) : X = Y :=
  (smul_left_cancel_iff g).mp h

/-- The two spellings of the action on arrows agree. -/
theorem smulTotal_eq_smul (g : G) (X : Quiver.Total V) :
    Work.ORBassSerre.GraphAction.smulTotal g X = g • X := rfl

/-- No group element inverts an arrow. -/
theorem smul_ne_reverse {hninv : Work.ORBassSerre.ActsWithoutInversions G V} (g : G)
    (X : Quiver.Total V) : g • X ≠ X.reverse :=
  fun h => hninv g X (by rw [smulTotal_eq_smul]; exact h)

/-- In a tree, two arrows with the same endpoints are equal. -/
theorem total_ext_of_isTree {hT : Work.ORBassSerre.IsTree V} {X Y : Quiver.Total V}
    (h1 : X.left = Y.left) (h2 : X.right = Y.right) : X = Y :=
  Quiver.Total.ext h1 h2
    (Quiver.heq_of_homOfEq_ext h1 h2
      (Work.ORBassSerre.Tree.Seg.arrow_unique (hT := hT) Y.left Y.right
        (Quiver.homOfEq X.hom h1 h2) Y.hom))

/-- The stabilizer of an arrow equals the stabilizer of its reverse. -/
theorem stabilizer_reverse_eq (X : Quiver.Total V) :
    MulAction.stabilizer G X.reverse = MulAction.stabilizer G X := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, total_smul_reverse]
  constructor
  · intro h
    have h2 := congrArg Quiver.Total.reverse h
    simpa using h2
  · intro h
    rw [h]

theorem units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' : ((-1 : ℤˣ) : ℤ) = ((1 : ℤˣ) : ℤ) := congrArg (fun u : ℤˣ => (u : ℤ)) h
  simp at h'

theorem units_one_ne_neg_one : (1 : ℤˣ) ≠ -1 := fun h => units_neg_one_ne_one h.symm

/-- From `σ • w = v` we get `w = σ⁻¹ • v`. -/
theorem inv_smul_eq_of_smul_eq {σ : G} {v w : V} (hσ : σ • w = v) : w = σ⁻¹ • v := by
  have h := congrArg (fun x => σ⁻¹ • x) hσ
  simpa only [← mul_smul, inv_mul_cancel, one_smul] using h

/-! ### The walk attached to a word -/

/-- The step of the walk attached to a sign `ε`: the edge from `v` towards `σ ^ ε • v`. -/
noncomputable def walkStep (v w : V) (e : v ⟶ w) (σ : G) (ε : ℤˣ) : Quiver.Total V :=
  if ε = 1 then (σ • Quiver.Total.mk v w e).reverse else Quiver.Total.mk v w e

@[simp] theorem walkStep_one (v w : V) (e : v ⟶ w) (σ : G) :
    walkStep v w e σ 1 = (σ • Quiver.Total.mk v w e).reverse :=
  if_pos rfl

@[simp] theorem walkStep_neg_one (v w : V) (e : v ⟶ w) (σ : G) :
    walkStep v w e σ (-1) = Quiver.Total.mk v w e :=
  if_neg units_neg_one_ne_one

theorem walkStep_left {v w : V} {e : v ⟶ w} {σ : G} (hσ : σ • w = v) (ε : ℤˣ) :
    (walkStep v w e σ ε).left = v := by
  unfold walkStep
  split
  · rw [Quiver.Total.reverse_left, Work.ORBassSerre.GraphAction.smul_right_mk]
    exact hσ
  · rfl

theorem walkStep_right {v w : V} {e : v ⟶ w} {σ : G} (hσ : σ • w = v) (ε : ℤˣ) :
    (walkStep v w e σ ε).right = σ ^ (ε : ℤ) • v := by
  unfold walkStep
  split
  · rename_i hε
    rw [Quiver.Total.reverse_right, Work.ORBassSerre.GraphAction.smul_left_mk, hε]
    simp
  · rename_i hε
    have hε' : ε = -1 := by
      rcases Int.units_eq_one_or ε with h | h
      · exact absurd h hε
      · exact h
    subst hε'
    have hv : (((-1 : ℤˣ) : ℤ)) = -1 := by simp
    rw [hv, zpow_neg_one]
    exact inv_smul_eq_of_smul_eq hσ

/-- The sign of the `k`-th letter of `L` (defaulting to `1` beyond the end). -/
noncomputable def walkSign (L : List (ℤˣ × G)) (k : ℕ) : ℤˣ :=
  if h : k < L.length then (L[k]).1 else 1

/-- The product of the first `k` letters, prefixed by `h₀`. -/
noncomputable def walkPfx (h₀ σ : G) (L : List (ℤˣ × G)) (k : ℕ) : G :=
  h₀ * ((L.take k).map (fun p : ℤˣ × G => σ ^ (p.1 : ℤ) * p.2)).prod

/-- The `k`-th vertex of the walk. -/
noncomputable def walkVert (v : V) (h₀ σ : G) (L : List (ℤˣ × G)) (k : ℕ) : V :=
  walkPfx h₀ σ L k • v

/-- The `k`-th step of the walk, as an element of `Quiver.Total V`. -/
noncomputable def walkStepAt (v w : V) (e : v ⟶ w) (σ h₀ : G) (L : List (ℤˣ × G))
    (k : ℕ) : Quiver.Total V :=
  walkPfx h₀ σ L k • walkStep v w e σ (walkSign L k)

@[simp] theorem walkPfx_zero (h₀ σ : G) (L : List (ℤˣ × G)) :
    walkPfx h₀ σ L 0 = h₀ := by
  simp [walkPfx]

theorem walkPfx_succ (h₀ σ : G) (L : List (ℤˣ × G)) (k : ℕ) (hk : k < L.length) :
    walkPfx h₀ σ L (k + 1) = walkPfx h₀ σ L k * (σ ^ ((L[k]).1 : ℤ) * (L[k]).2) := by
  unfold walkPfx
  rw [← List.take_append_getElem hk, List.map_append, List.prod_append, List.map_singleton,
    List.prod_singleton, mul_assoc]

theorem walkPfx_length (h₀ σ : G) (L : List (ℤˣ × G)) :
    walkPfx h₀ σ L L.length = h₀ * (L.map (fun p : ℤˣ × G => σ ^ (p.1 : ℤ) * p.2)).prod := by
  simp [walkPfx]

theorem walkSign_of_lt (L : List (ℤˣ × G)) {k : ℕ} (hk : k < L.length) :
    walkSign L k = (L[k]).1 := by
  simp [walkSign, hk]

theorem walkVert_zero {v : V} (h₀ σ : G) (L : List (ℤˣ × G)) (hh : h₀ • v = v) :
    walkVert v h₀ σ L 0 = v := by
  simp [walkVert, hh]

theorem walkVert_length {v : V} (h₀ σ : G) (L : List (ℤˣ × G))
    (hx : h₀ * (L.map (fun p : ℤˣ × G => σ ^ (p.1 : ℤ) * p.2)).prod = 1) :
    walkVert v h₀ σ L L.length = v := by
  rw [walkVert, walkPfx_length, hx, one_smul]

theorem walkStepAt_eq {v w : V} {e : v ⟶ w} {σ h₀ : G} {L : List (ℤˣ × G)} {k : ℕ}
    (hk : k < L.length) :
    walkStepAt v w e σ h₀ L k = walkPfx h₀ σ L k • walkStep v w e σ ((L[k]).1) := by
  unfold walkStepAt
  rw [walkSign_of_lt L hk]

theorem walkStepAt_left {v w : V} {e : v ⟶ w} {σ h₀ : G} {L : List (ℤˣ × G)}
    (hσ : σ • w = v) {k : ℕ} (hk : k < L.length) :
    (walkStepAt v w e σ h₀ L k).left = walkVert v h₀ σ L k := by
  calc (walkStepAt v w e σ h₀ L k).left
      = (walkPfx h₀ σ L k • walkStep v w e σ ((L[k]).1)).left := by rw [walkStepAt_eq hk]
    _ = walkPfx h₀ σ L k • (walkStep v w e σ ((L[k]).1)).left := total_smul_left _ _
    _ = walkPfx h₀ σ L k • v := by rw [walkStep_left hσ]
    _ = walkVert v h₀ σ L k := rfl

theorem walkStepAt_right {v w : V} {e : v ⟶ w} {σ h₀ : G} {L : List (ℤˣ × G)}
    (hσ : σ • w = v)
    (hg : ∀ i : Fin L.length, (L.get i).2 ∈ MulAction.stabilizer G v) {k : ℕ}
    (hk : k < L.length) :
    (walkStepAt v w e σ h₀ L k).right = walkVert v h₀ σ L (k + 1) := by
  have hgv : (L[k]).2 • v = v := by
    have h1 := MulAction.mem_stabilizer_iff.mp (hg ⟨k, hk⟩)
    rwa [List.get_eq_getElem] at h1
  calc (walkStepAt v w e σ h₀ L k).right
      = (walkPfx h₀ σ L k • walkStep v w e σ ((L[k]).1)).right := by rw [walkStepAt_eq hk]
    _ = walkPfx h₀ σ L k • (walkStep v w e σ ((L[k]).1)).right := total_smul_right _ _
    _ = walkPfx h₀ σ L k • (σ ^ ((L[k]).1 : ℤ) • v) := by rw [walkStep_right hσ]
    _ = (walkPfx h₀ σ L k * σ ^ ((L[k]).1 : ℤ)) • v := (mul_smul _ _ _).symm
    _ = (walkPfx h₀ σ L k * (σ ^ ((L[k]).1 : ℤ) * (L[k]).2)) • v := by
          simp only [mul_smul, hgv]
    _ = walkPfx h₀ σ L (k + 1) • v := by rw [walkPfx_succ h₀ σ L k hk]
    _ = walkVert v h₀ σ L (k + 1) := rfl

/-! ### No immediate backtracking -/

/-- **The walk never immediately backtracks.**  Consecutive steps of the walk attached to a
reduced word are never mutually inverse. -/
theorem walkStepAt_no_backtrack {hT : Work.ORBassSerre.IsTree V}
    {hninv : Work.ORBassSerre.ActsWithoutInversions G V}
    {v w : V} {e : v ⟶ w} {σ h₀ : G} {L : List (ℤˣ × G)}
    (hσ : σ • w = v)
    (hg : ∀ i : Fin L.length, (L.get i).2 ∈ MulAction.stabilizer G v)
    (hchain : L.IsChain (fun a b => a.2 ∈ (if a.1 = 1 then
        MulAction.stabilizer G (Quiver.Total.mk v w e)
      else (MulAction.stabilizer G (Quiver.Total.mk v w e)).map (MulAut.conj σ).toMonoidHom)
      → a.1 = b.1))
    {k : ℕ} (hk : k + 1 < L.length)
    (hback : walkStepAt v w e σ h₀ L (k + 1) = (walkStepAt v w e σ h₀ L k).reverse) : False := by
  have hk1 : k < L.length := by omega
  have hgv : (L[k]).2 • v = v := by
    have h1 := MulAction.mem_stabilizer_iff.mp (hg ⟨k, hk1⟩)
    rwa [List.get_eq_getElem] at h1
  -- the cancellation step
  have hCL : (σ ^ ((L[k]).1 : ℤ) * (L[k]).2) • walkStep v w e σ ((L[k + 1]).1)
      = (walkStep v w e σ ((L[k]).1)).reverse := by
    rw [walkStepAt_eq hk, walkStepAt_eq hk1, ← total_smul_reverse, walkPfx_succ h₀ σ L k hk1,
      mul_smul] at hback
    exact smul_left_cancel' (walkPfx h₀ σ L k) hback
  -- the chain condition at the pair `(k, k+1)`
  have hrel : (L[k]).2 ∈ (if (L[k]).1 = 1 then
        MulAction.stabilizer G (Quiver.Total.mk v w e)
      else (MulAction.stabilizer G (Quiver.Total.mk v w e)).map (MulAut.conj σ).toMonoidHom)
      → (L[k]).1 = (L[k + 1]).1 :=
    (List.isChain_iff_getElem.mp hchain) k hk
  rcases Int.units_eq_one_or ((L[k]).1) with hε | hε
  · rcases Int.units_eq_one_or ((L[k + 1]).1) with hε' | hε'
    · -- signs `1, 1`: the element `σ * g` inverts the step
      have h := hCL
      rw [hε, hε'] at h
      refine smul_ne_reverse (hninv := hninv) (σ * (L[k]).2) (walkStep v w e σ 1) ?_
      simpa using h
    · -- signs `1, -1`: `g` fixes the fundamental edge
      have hstep : (σ * (L[k]).2) • Quiver.Total.mk v w e = σ • Quiver.Total.mk v w e := by
        have h := hCL
        rw [hε, hε'] at h
        simpa using h
      have hright := congrArg Quiver.Total.right hstep
      rw [total_smul_right, total_smul_right] at hright
      have hgw : (L[k]).2 • w = w := by
        have h3 := congrArg (fun x => σ⁻¹ • x) hright
        simpa [← mul_smul, mul_assoc] using h3
      have hgE : (L[k]).2 • Quiver.Total.mk v w e = Quiver.Total.mk v w e :=
        total_ext_of_isTree (hT := hT)
          (by rw [total_smul_left]; simpa using hgv)
          (by rw [total_smul_right]; simpa using hgw)
      have hmem : (L[k]).2 ∈ (if (L[k]).1 = 1 then
            MulAction.stabilizer G (Quiver.Total.mk v w e)
          else (MulAction.stabilizer G (Quiver.Total.mk v w e)).map
            (MulAut.conj σ).toMonoidHom) := by
        rw [hε, if_pos rfl]
        exact MulAction.mem_stabilizer_iff.mpr hgE
      have h := hrel hmem
      rw [hε, hε'] at h
      exact units_one_ne_neg_one h
  · rcases Int.units_eq_one_or ((L[k + 1]).1) with hε' | hε'
    · -- signs `-1, 1`: `g` fixes the conjugate edge
      have hstep : (σ⁻¹ * (L[k]).2) • (σ • Quiver.Total.mk v w e).reverse
          = (Quiver.Total.mk v w e).reverse := by
        have h := hCL
        rw [hε, hε'] at h
        simpa using h
      have hright := congrArg Quiver.Total.right hstep
      simp only [total_smul_right, Quiver.Total.reverse_right, total_smul_left] at hright
      have hgw : (L[k]).2 • (σ • v) = σ • v := by
        have h3 := congrArg (fun x => σ • x) hright
        simpa [← mul_smul, mul_assoc] using h3
      have hgE : (L[k]).2 • (σ • Quiver.Total.mk v w e) = σ • Quiver.Total.mk v w e :=
        total_ext_of_isTree (hT := hT)
          (by rw [total_smul_left, total_smul_left]; simpa using hgw)
          (by rw [total_smul_right, total_smul_right, hσ]; exact hgv)
      have hmem : (L[k]).2 ∈ (if (L[k]).1 = 1 then
            MulAction.stabilizer G (Quiver.Total.mk v w e)
          else (MulAction.stabilizer G (Quiver.Total.mk v w e)).map
            (MulAut.conj σ).toMonoidHom) := by
        rw [hε, if_neg units_neg_one_ne_one]
        rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj σ (Quiver.Total.mk v w e)]
        exact MulAction.mem_stabilizer_iff.mpr hgE
      have h := hrel hmem
      rw [hε, hε'] at h
      exact units_neg_one_ne_one h
    · -- signs `-1, -1`: the element `σ⁻¹ * g` inverts the step
      have h := hCL
      rw [hε, hε'] at h
      refine smul_ne_reverse (hninv := hninv) (σ⁻¹ * (L[k]).2) (walkStep v w e σ (-1)) ?_
      simpa using h


/-! ### The main theorem -/

theorem hnn_reduced_word_ne_one {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions G V) {v w : V} (e : v ⟶ w) (σ : G)
    (hσ : σ • w = v) (h₀ : G) (L : List (ℤˣ × G))
    (hh : h₀ ∈ MulAction.stabilizer G v)
    (hg : ∀ i : Fin L.length, (L.get i).2 ∈ MulAction.stabilizer G v)
    (hchain : L.IsChain (fun a b => a.2 ∈ (if a.1 = 1 then
        MulAction.stabilizer G (Quiver.Total.mk v w e)
      else (MulAction.stabilizer G (Quiver.Total.mk v w e)).map (MulAut.conj σ).toMonoidHom)
      → a.1 = b.1))
    (hne : h₀ ≠ 1 ∨ L ≠ []) :
    h₀ * (L.map (fun x => σ ^ (x.1 : ℤ) * x.2)).prod ≠ 1 := by
  intro hx
  have hL : L ≠ [] := by
    rcases hne with h | h
    · intro hnil
      apply h
      rw [hnil] at hx
      simpa using hx
    · exact h
  have hn : 0 < L.length := by
    cases L with
    | nil => exact absurd rfl hL
    | cons a t => simp
  have hh' : h₀ • v = v := MulAction.mem_stabilizer_iff.mp hh
  have hkey : ∃ k, k + 1 < L.length ∧
      walkStepAt v w e σ h₀ L (k + 1) = (walkStepAt v w e σ h₀ L k).reverse := by
    refine Work.ORBassSerre.Tree.Walk.exists_consecutive_backtrack_of_closed_walk
      (hT := hT) (n := L.length) hn (z := fun k => walkVert v h₀ σ L k)
      (F := fun k => walkStepAt v w e σ h₀ L k) ?_ ?_ ?_
    · exact fun k hk => walkStepAt_left hσ hk
    · exact fun k hk => walkStepAt_right hσ hg hk
    · exact (walkVert_length h₀ σ L hx).trans (walkVert_zero h₀ σ L hh').symm
  obtain ⟨k, hk, hback⟩ := hkey
  exact walkStepAt_no_backtrack (hT := hT) (hninv := hninv) hσ hg hchain hk hback

end Work.ORBassSerre.Action.Structure
