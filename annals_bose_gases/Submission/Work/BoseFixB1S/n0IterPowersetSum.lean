import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1S.n0SpectralAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.n0IterPowersetSum`

The **expansion / partition-of-unity identity** for the slot iteration `n0Iter`.

For a *nodup* slot list `l`, summing the iteration `n0Iter volA A (fun i => decide (i ∈ S)) l Ψ`
over **all** subsets `S ⊆ l.toFinset` — i.e. over all `2^{|l|}` choices of, at each slot, either
the projection `P_{B,i}` (when `i ∈ S`) or the single-slot complement `1 − P_{B,i}` (when `i ∉ S`) —
returns `Ψ`:

`∑_{S ⊆ l.toFinset} n0Iter volA A (fun i => decide (i ∈ S)) l Ψ = Ψ`.

This is pure `AddCommMonoid`/composition algebra: it uses **no** property of `P_{B,i}` at all (not
even idempotence).  Writing `l = i :: l'`, `n0Iter` acts by applying at the head slot either `P_i`
or `1 − P_i` *by composition* and then recursing on `l'`.  Splitting the subsets of
`insert i l'.toFinset = (i :: l').toFinset` into those containing `i` and those not
(`Finset.sum_powerset_insert`, using `Nodup` to get `i ∉ l'.toFinset`) and applying the induction
hypothesis to `l'` twice — once at `1 − P_i` and once at `P_i` — gives
`(1 − P_i)Ψ + P_iΨ = Ψ` pointwise.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Unfolding `n0Iter` at a head slot on which the branch function is `true`
(so the head projection `P_{B,i}` — i.e. `boxPInd` — is applied by composition). -/
theorem n0IterPowersetSum_cons_true {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool)
    (i : Fin N) (l : List (Fin N)) (Ψ : X N → ℝ) (h : b i = true) :
    n0Iter volA A b (i :: l) Ψ
      = n0Iter volA A b l (fun x => UBBInputs8.boxPInd volA A i Ψ x) := by
  rw [n0Iter]; simp [h]

/-- Unfolding `n0Iter` at a head slot on which the branch function is `false`
(so the single-slot complement `1 − P_{B,i}` is applied by composition). -/
theorem n0IterPowersetSum_cons_false {N : ℕ} (volA : ℝ) (A : Set E3) (b : Fin N → Bool)
    (i : Fin N) (l : List (Fin N)) (Ψ : X N → ℝ) (h : b i = false) :
    n0Iter volA A b (i :: l) Ψ
      = n0Iter volA A b l (fun x => Ψ x - UBBInputs8.boxPInd volA A i Ψ x) := by
  rw [n0Iter]; simp [h]

theorem n0IterPowersetSum {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) :
    ∀ (l : List (Fin N)), l.Nodup → ∀ Ψ : Submission.BoseGases.X N → ℝ,
      (∑ S ∈ l.toFinset.powerset,
        Work.BoseFixB1S.n0Iter volA A (fun i => decide (i ∈ S)) l Ψ) = Ψ := by
  intro l
  induction l with
  | nil =>
    intro _ Ψ
    rw [List.toFinset_nil, Finset.powerset_empty, Finset.sum_singleton]
    rw [n0Iter]
  | cons i l' ih =>
    intro hl Ψ
    obtain ⟨hi_notmem, hl'⟩ := List.nodup_cons.mp hl
    have hi : i ∉ l'.toFinset := by rwa [List.mem_toFinset]
    have IH := ih hl'
    rw [List.toFinset_cons, Finset.sum_powerset_insert hi]
    -- the subsets of `l'.toFinset` split off from those of `insert i l'.toFinset`
    have hA : (∑ t ∈ l'.toFinset.powerset,
        n0Iter volA A (fun i => decide (i ∈ t)) (i :: l') Ψ)
        = (fun x => Ψ x - UBBInputs8.boxPInd volA A i Ψ x) := by
      rw [← IH (fun x => Ψ x - UBBInputs8.boxPInd volA A i Ψ x)]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_powerset] at ht
      have hmem : i ∉ t := fun hc => hi (ht hc)
      exact n0IterPowersetSum_cons_false volA A (fun j => decide (j ∈ t)) i l' Ψ
        (by simp [hmem])
    have hB : (∑ t ∈ l'.toFinset.powerset,
        n0Iter volA A (fun i_1 => decide (i_1 ∈ insert i t)) (i :: l') Ψ)
        = (fun x => UBBInputs8.boxPInd volA A i Ψ x) := by
      rw [← IH (fun x => UBBInputs8.boxPInd volA A i Ψ x)]
      apply Finset.sum_congr rfl
      intro t ht
      rw [n0IterPowersetSum_cons_true volA A (fun j => decide (j ∈ insert i t)) i l' Ψ
        (by simp)]
      -- the branch functions agree on `l'` because `i ∉ l'`
      apply n0Iter_congr
      intro j hj
      have hjne : j ≠ i := fun h => hi (h ▸ List.mem_toFinset.mpr hj)
      have hiff : (j ∈ insert i t) ↔ (j ∈ t) := by
        rw [Finset.mem_insert]
        exact ⟨fun h => h.elim (fun hji => absurd hji hjne) id, Or.inr⟩
      exact decide_eq_decide.mpr hiff
    rw [hA, hB]
    funext x
    simp

end Work.BoseFixB1S
