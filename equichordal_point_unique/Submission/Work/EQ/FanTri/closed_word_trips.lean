import Mathlib
import Submission.Work.EQ.FanTri.fan_split_defs
import Submission.Work.EQ.FanTri.decomp_spec
import Submission.Work.EQ.FanTri.dec_counts
import Submission.Work.EQ.FanTri.fan_split

namespace Work.EQ.FanTri

open Work.EQ

/-- **Combinatorial core.**  Let `a` be a gap list and `σ` a trip list with
`a.length = σ.length + 1`, so that `asm a σ = true^{a₀} σ₁ … σₙ true^{aₙ}`.  If the assembled
word is closed (`stAux (asm a σ) 0 = 0`), every trip but the last returns to `0`
(hypothesis `hclosed`) and the last trip either returns to `0` or is followed by an empty gap
(hypothesis `hlast`, exactly the last clause of `DecSpec`), then *every* trip returns to `0`.

Induction on `σ`.  If `σ = [τ₀]` then `a = [g, g']` and `hcl` reads
`stAux τ₀ 0 - g' = 0`; with `hlast` (`wstate τ₀ τ₀.length = 0 ∨ g' = 0`) the claim follows.
If `σ = τ₀ :: σ'` with `σ' ≠ []`, then `τ₀` is not the last trip, so it returns to `0` by
`hclosed`; the walk of `true^{g} ++ τ₀ ++ asm a' σ'` therefore ends where the walk of
`asm a' σ'` ends, and the induction hypothesis applies to `(a', σ')` with the shifted
hypotheses. -/
lemma closed_trips_aux : ∀ (σ : List (List Bool)) (a : List ℕ),
    a.length = σ.length + 1 →
    Work.EQ.stAux (asm a σ) 0 = 0 →
    (∀ (i : ℕ) (τ : List Bool), σ[i]? = some τ → i + 1 < σ.length → wstate τ τ.length = 0) →
    (∀ (i : ℕ) (τ : List Bool) (g : ℕ), σ[i]? = some τ → a[i + 1]? = some g →
      i + 1 = σ.length → (wstate τ τ.length = 0 ∨ g = 0)) →
    ∀ τ ∈ σ, wstate τ τ.length = 0 := by
  intro σ
  induction σ with
  | nil => intro a _ _ _ _ τ hτ; simp at hτ
  | cons τ₀ σ' ih =>
    intro a hlen hcl hclosed hlast τg hτg
    cases a with
    | nil => simp at hlen
    | cons g a' =>
      have hlen' : a'.length = σ'.length + 1 := by
        simp only [List.length_cons] at hlen; omega
      by_cases hnil : σ' = []
      · -- the trip `τ₀` is the last trip
        subst hnil
        obtain ⟨g', rfl⟩ := List.length_eq_one_iff.mp (by simpa using hlen')
        rw [List.mem_singleton] at hτg
        rw [hτg]
        have hsub : wstate τ₀ τ₀.length - g' = 0 := by
          simp only [asm, Work.EQ.stAux_append, stAux_replicate_true, Nat.zero_sub] at hcl
          rw [stAux_eq_wstate] at hcl
          exact hcl
        rcases hlast 0 τ₀ g' (by simp) (by simp) (by simp) with h0 | h0
        · exact h0
        · omega
      · -- `τ₀` is not the last trip
        have hτ₀ : wstate τ₀ τ₀.length = 0 := by
          refine hclosed 0 τ₀ (by simp) ?_
          simp only [List.length_cons]
          have := List.length_pos_iff.mpr hnil
          omega
        have hcl' : Work.EQ.stAux (asm a' σ') 0 = 0 := by
          simp only [asm, Work.EQ.stAux_append, stAux_replicate_true, Nat.zero_sub] at hcl
          rw [stAux_eq_wstate, hτ₀] at hcl
          exact hcl
        have hclosed' : ∀ (i : ℕ) (τ : List Bool), σ'[i]? = some τ → i + 1 < σ'.length →
            wstate τ τ.length = 0 := by
          intro i τ h1 h2
          refine hclosed (i + 1) τ ?_ ?_
          · simpa using h1
          · simp only [List.length_cons]; omega
        have hlast' : ∀ (i : ℕ) (τ : List Bool) (g : ℕ), σ'[i]? = some τ → a'[i + 1]? = some g →
            i + 1 = σ'.length → (wstate τ τ.length = 0 ∨ g = 0) := by
          intro i τ g'' h1 h2 h3
          refine hlast (i + 1) τ g'' ?_ ?_ ?_
          · simpa using h1
          · rw [List.getElem?_cons_succ]; exact h2
          · simp only [List.length_cons]; omega
        rcases List.mem_cons.mp hτg with rfl | hmem
        · exact hτ₀
        · exact ih a' hlen' hcl' hclosed' hlast' τg hmem

/-- **Every trip of a closed word returns to `0`.**  If `u` is a closed walk (`stAux u 0 = 0`)
with gap/trip decomposition `DecSpec u a σ`, then *every* trip of `σ` returns to `0` — including
the last one, for which `DecSpec` only gives `wstate τ τ.length = 0 ∨ a.getLast? = some 0`: in the
second case the last gap is empty, so `u` ends with the last trip and the state at the end of `u`
is that of the last trip.

Route: for non-last trips use the `DecSpec` clause; for the last trip split off the final gap with
`asm_take_last` (`Submission/Work/EQ/FanTri/FanSplit2Defs.lean`) or `asm_split`, note that the
preceding part ends at `0` because all its trips return (`wstate_asm_zero`,
`Submission/Work/EQ/FanTri/fan_split.lean`), and conclude from `stAux u 0 = 0` together with
`stAux (replicate n true) m = m - n`. -/
theorem closed_word_trips {u : List Bool} (hcl : Work.EQ.stAux u 0 = 0) (a : List ℕ)
    (σ : List (List Bool)) (h : Work.EQ.FanTri.DecSpec u a σ) :
    ∀ τ ∈ σ, Work.EQ.FanTri.wstate τ τ.length = 0 := by
  refine closed_trips_aux σ a h.len ?_ h.closed h.last
  rw [← h.concat]
  exact hcl

end Work.EQ.FanTri
