/-
Definitions for `Work.EQ.FanTri.fan_split`.

We work with the walk of `Work.EQ.charValDefs` (`stAux`, `stp`) read from state `0` along the
letters of a word.  `wstate u t` is the state after the first `t` letters of `u`; `VisU u` counts
the times `t ∈ [1, |u|]` at which that state is nonzero.  A word is decomposed into *gap lengths*
(blocks `true^{a_i}`, along which the walk rests at `0`) and *trips* `σ_i` (maximal positive
excursions), and `asm a σ = true^{a₀} σ₁ true^{a₁} σ₂ …`.
-/
import Mathlib
import Submission.Work.EQ.FanTri.Base
import Submission.Work.EQ.charValDefs

namespace Work.EQ.FanTri

open Work.EQ

noncomputable section
open Classical

/-- The state reached after reading the first `t` letters of `u`, starting from state `0`. -/
def wstate (u : List Bool) (t : ℕ) : ℕ := stAux (u.take t) 0

/-- Number of times `t ∈ [1, |u|]` at which the walk of `u` (from `0`) is not at `0`. -/
def VisU (u : List Bool) : ℕ := ((Finset.Icc 1 u.length).filter (fun t => wstate u t ≠ 0)).card

/-- Assemble a word from gap lengths and trips: `asm [a₀, a₁, …] [σ₁, σ₂, …]` is
`true^{a₀} σ₁ true^{a₁} σ₂ …`. -/
def asm : List ℕ → List (List Bool) → List Bool
  | [], _ => []
  | g :: _, [] => List.replicate g true
  | g :: gs, τ :: ts => List.replicate g true ++ τ ++ asm gs ts

/-- The length of the first trip of a word: the least `t ≥ 1` at which the walk returns to `0`,
or the length of the whole word if there is no such `t`. -/
def tripLen (r : List Bool) : ℕ :=
  if h : ∃ t, 1 ≤ t ∧ wstate r t = 0 then Nat.find h else r.length

@[simp] lemma wstate_zero (u : List Bool) : wstate u 0 = 0 := by
  simp [wstate]

lemma wstate_of_le {u : List Bool} {t : ℕ} (h : u.length ≤ t) : wstate u t = stAux u 0 := by
  unfold wstate
  rw [List.take_of_length_le h]

lemma wstate_take_le {u : List Bool} {t l : ℕ} (h : t ≤ l) :
    wstate (u.take l) t = wstate u t := by
  unfold wstate
  rw [List.take_take, min_eq_left h]

lemma wstate_append (p q : List Bool) (t : ℕ) :
    wstate (p ++ q) (p.length + t) = stAux (q.take t) (stAux p 0) := by
  have h1 : (p ++ q).take (p.length + t) = p ++ q.take t := by
    rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  unfold wstate
  rw [h1, stAux_append]

lemma wstate_succ {u : List Bool} {t : ℕ} (h : t < u.length) :
    wstate u (t + 1) = stp (u.get ⟨t, h⟩) (wstate u t) := by
  have h1 : u.take (t + 1) = u.take t ++ [u.get ⟨t, h⟩] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h]
    rfl
  unfold wstate
  rw [h1, stAux_append]
  rfl

lemma stp_true_sub (m : ℕ) : stp true m = m - 1 := by
  by_cases hm : m = 0
  · subst hm; simp [stp]
  · simp [stp, hm]

lemma stAux_replicate_true (n m : ℕ) : stAux (List.replicate n true) m = m - n := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, stAux_cons, ih, stp_true_sub]
      omega

lemma wstate_replicate_true (n t : ℕ) : wstate (List.replicate n true) t = 0 := by
  unfold wstate
  rw [List.take_replicate, stAux_replicate_true]
  omega

lemma VisU_replicate_true (n : ℕ) : VisU (List.replicate n true) = 0 := by
  unfold VisU
  simp [wstate_replicate_true]

lemma tripLen_pos (r : List Bool) : 1 ≤ tripLen r := by
  unfold tripLen
  split_ifs with h
  · exact (Nat.find_spec h).1
  · by_contra hc
    push Not at hc
    have hr0 : r = [] := List.length_eq_zero_iff.mp (by omega)
    subst hr0
    exact h ⟨1, le_refl 1, by simp [wstate]⟩

lemma tripLen_le {r : List Bool} (hr : r ≠ []) : tripLen r ≤ r.length := by
  unfold tripLen
  split_ifs with h
  · by_contra hlt
    push Not at hlt
    have h3 : stAux r 0 = 0 := by
      rw [← wstate_of_le (le_of_lt hlt), (Nat.find_spec h).2]
    have h4 : wstate r r.length = 0 := by rw [wstate_of_le (le_refl _), h3]
    exact (Nat.find_min h hlt) ⟨Nat.succ_le_of_lt (List.length_pos_iff.mpr hr), h4⟩
  · exact le_refl _

lemma tripLen_le_length (r : List Bool) : tripLen r ≤ r.length ∨ r = [] := by
  by_cases hr : r = []
  · exact Or.inr hr
  · exact Or.inl (tripLen_le hr)

/-- Decompose a word into a list of gap lengths and a list of trips. -/
def decomp : List Bool → List ℕ × List (List Bool)
  | u =>
    let g := (u.takeWhile (fun c => c)).length
    let r := u.dropWhile (fun c => c)
    if hr : r = [] then ([g], [])
    else
      let l := tripLen r
      let d := decomp (r.drop l)
      (g :: d.1, r.take l :: d.2)
termination_by u => u.length
decreasing_by
  all_goals
    simp_wf
    rename_i a
    have hne : a.dropWhile (fun c => c) ≠ [] := hr
    have h3 : 1 ≤ (a.dropWhile (fun c => c)).length :=
      Nat.succ_le_of_lt (List.length_pos_iff.mpr hne)
    have h1 : 1 ≤ tripLen (a.dropWhile (fun c => c)) := tripLen_pos _
    have h2 : (a.dropWhile (fun c => c)).length ≤ a.length := List.length_dropWhile_le _ _
    omega

/-- The specification of a gap/trip decomposition of `u`. -/
def DecSpec (u : List Bool) (a : List ℕ) (σ : List (List Bool)) : Prop :=
  a.length = σ.length + 1 ∧
  u = asm a σ ∧
  (∀ (i : ℕ) (τ : List Bool), σ[i]? = some τ → wstate τ 1 ≠ 0) ∧
  (∀ (i : ℕ) (τ : List Bool), σ[i]? = some τ →
      ∀ t : ℕ, 1 ≤ t → t < τ.length → wstate τ t ≠ 0) ∧
  (∀ (i : ℕ) (τ : List Bool), σ[i]? = some τ → i + 1 < σ.length →
      wstate τ τ.length = 0) ∧
  (∀ (i : ℕ) (τ : List Bool) (g : ℕ), σ[i]? = some τ → a[i + 1]? = some g →
      i + 1 = σ.length → (wstate τ τ.length = 0 ∨ g = 0))

lemma DecSpec.len {u : List Bool} {a : List ℕ} {σ : List (List Bool)} (h : DecSpec u a σ) :
    a.length = σ.length + 1 := h.1

lemma DecSpec.concat {u : List Bool} {a : List ℕ} {σ : List (List Bool)} (h : DecSpec u a σ) :
    u = asm a σ := h.2.1

lemma DecSpec.pos {u : List Bool} {a : List ℕ} {σ : List (List Bool)} (h : DecSpec u a σ) :
    ∀ (i : ℕ) (τ : List Bool), σ[i]? = some τ → wstate τ 1 ≠ 0 := h.2.2.1

lemma DecSpec.interior {u : List Bool} {a : List ℕ} {σ : List (List Bool)} (h : DecSpec u a σ) :
    ∀ (i : ℕ) (τ : List Bool), σ[i]? = some τ →
      ∀ t : ℕ, 1 ≤ t → t < τ.length → wstate τ t ≠ 0 := h.2.2.2.1

lemma DecSpec.closed {u : List Bool} {a : List ℕ} {σ : List (List Bool)} (h : DecSpec u a σ) :
    ∀ (i : ℕ) (τ : List Bool), σ[i]? = some τ → i + 1 < σ.length →
      wstate τ τ.length = 0 := h.2.2.2.2.1

lemma DecSpec.last {u : List Bool} {a : List ℕ} {σ : List (List Bool)} (h : DecSpec u a σ) :
    ∀ (i : ℕ) (τ : List Bool) (g : ℕ), σ[i]? = some τ → a[i + 1]? = some g →
      i + 1 = σ.length → (wstate τ τ.length = 0 ∨ g = 0) := h.2.2.2.2.2

end

end Work.EQ.FanTri
