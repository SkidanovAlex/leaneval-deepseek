import Mathlib
import Submission.ModelStarBoundary7
import Submission.ModelStarShell
import Submission.Commons.Analysis.Complex.exp_I_mul_eq_of_norm_one

/-!
# ModelStarTipBound -- the model map's spike-tip maximum is at least 4^(1/s)

STATUS: verified research-isolate milestone (stage 6 of the model-map
boundary programme): 0 sorries; axiom-clean [propext, Classical.choice,
Quot.sound]; unimported module (does NOT import `Submission.lean`).

SETTING (the forward/easy half of Eremenko's KL-dubinin equivalence): the
model map F(z) = z·∏_k (1 − z_k·z^{-1})^(2 r_k) with unit junctions
z_k = eAngle (φ k) sorted on [0, 2π), weights r_k ≥ 0 with Σ r_k = 1
bounds the unit circle to the boundary of a hedgehog.  Each open arc of
the circle between consecutive junctions is swept onto a segment
[0, m_j]·u_j (ModelStarBoundary5/6/7: arc_sweeps_segment,
closed_arc_sweeps_segment, wrap_sweep_closed), where the TIP LENGTH m_j
is the arc maximum of the sweep factor ρ(t) = ‖F(eAngle t)‖ =
∏_k ‖1 − eAngle (φ k − t)‖^(2 r k).

THEOREM (`max_tip_ge_four_rpow_inv`, below): unit junctions
`z₀ k = eAngle (φ k)`, weights `0 < r k` with `Σ r k = 1` -- the maximum
of the tip lengths m_j over all s arcs (the s−1 consecutive index arcs
`(φ j, φ (j+1))` plus the wrap-around arc `(φ (s−1), φ 0 + 2π)`) is at
least 4^(1/s):

    ∃ j : Fin s, 4^(1/s) ≤ tip hs φ r j .

(No sortedness/monotonicity of φ is needed for the inequality itself --
the index/order bookkeeping finds, for any representative τ of the KL
point, a consecutive-index interval bracketing τ in VALUE, or the wrap
interval; sorted φ is of course the situation where the arcs are the
genuine cyclically-ordered junction arcs of the model star.)

PROOF (a two-line idea + bookkeeping):
  1. `ModelStarShell.modelF_unit_sup_ge_four_rpow_inv` (KL, PROVED) gives
     a unit point w₀ with 4^(1/s) ≤ ‖F w₀‖; write w₀ = eAngle σ.
  2. By the boundary identity ρ(t) = ‖F(eAngle t)‖ we get
     0 < 4^(1/s) ≤ ρ σ, so σ (indeed every representative τ ≡ σ mod 2π)
     is NOT a junction angle (ρ vanishes there when 0 < r k).
  3. Shift σ into the fundamental domain [φ 0, φ 0 + 2π): τ := σ − 2πz
     with z := ⌊(σ − φ 0)/(2π)⌋; ρ is 2π-periodic (ρ(τ) = ρ(σ) > 0), and
     τ ∈ [φ 0, φ 0 + 2π), τ ∉ {φ k}.  Hence τ lies strictly inside one of
     the s open arcs (consecutive intervals (φ j, φ (j+1)) for j < s−1,
     plus the wrap (φ (s−1), φ 0 + 2π)): j found by the least-index
     argument (Finset.min' of the filter {j | τ < φ j}, or the wrap when
     the filter is empty).
  4. ρ τ ≤ sSup(ρ '' that arc) = tip j (image membership + the uniform
     bound `ModelStarBoundary5.rho_le_uniform_bound` for BddAbove), so
     4^(1/s) ≤ ρ σ = ρ τ ≤ tip j.

NOTE (framework value only): this does NOT close the gate
`Step3.sym_maximality` -- it is the model-side/sharpness half of the
KL-dubinin equivalence (the converse E1–E5 needs the exterior
conformality of F, still open).  It machine-checks the exact statement
E5 must prove for the GENERAL exterior map of a cap-1 star once E1–E4
are in place: "the maximum tip length over the arcs is the circle maximum
of ‖Φ‖, hence ≥ 4^(1/s)·cap".
-/

noncomputable section

open scoped Real BigOperators Topology
open Set Filter Complex
open Submission.ModelStarBoundary2
open Submission.ModelStarBoundary3
open Submission.ModelStarBoundary4
open Submission.ModelStarBoundary5
open Submission.ModelStarBoundary6
open Submission.ModelStarBoundary7

namespace Submission.ModelStarTipBound

/-- ρ is invariant under integer multiples of the period 2π (in the
additive variable): `ρ(t + 2πz) = ρ(t)` for every integer z. -/
lemma rho_int_periodic {s : ℕ} (φ r : Fin s → ℝ) (t : ℝ) (z : ℤ) :
    rho φ r (t + (2 * Real.pi) * (z : ℝ)) = rho φ r t := by
  have hper : Function.Periodic (fun u : ℝ => rho φ r u) (2 * Real.pi) := by
    intro u
    exact rho_two_pi_periodic φ r u
  have hz := Function.Periodic.int_mul hper z
  simpa [mul_comm, mul_left_comm, mul_assoc] using hz t

/-- eAngle is invariant under integer multiples of the period 2π. -/
lemma eAngle_int_add (x : ℝ) (z : ℤ) :
    eAngle (x + (2 * Real.pi) * (z : ℝ)) = eAngle x := by
  have hper : Function.Periodic eAngle (2 * Real.pi) := by
    intro u
    exact eAngle_add_two_pi u
  have hz := Function.Periodic.int_mul hper z
  simpa [mul_comm, mul_left_comm, mul_assoc] using hz x

/-- `2π > 0`. -/
lemma two_pi_pos : 0 < 2 * Real.pi := by
  exact mul_pos (by norm_num) Real.pi_pos

/-- **Tip length of arc `j`.**  For `0 < s`, `j : Fin s`: if `j` is not the
last index (`j.val + 1 < s`) the arc is the consecutive interval
`(φ j, φ (j+1))` between consecutive junctions; otherwise (the wrap-around
arc) it is `(φ (s−1), φ 0 + 2π)`.  The tip is the maximum of the sweep
factor ρ over the open arc (i.e. the supremum of the boundary modulus
`‖F‖` over that arc). -/
noncomputable def tip {s : ℕ} (hs : 0 < s) (φ r : Fin s → ℝ) (j : Fin s) : ℝ :=
  if h : j.val + 1 < s then
    sSup (rho φ r '' Ioo (φ j) (φ ⟨j.val + 1, h⟩))
  else
    sSup (rho φ r '' Ioo (φ (wrapLast s hs)) (φ ⟨0, hs⟩ + 2 * Real.pi))

/-- A positive sweep value forces the point off every junction (as a real
number): if `τ = φ k` and `0 < r k` then `ρ τ = 0`. -/
lemma rho_eq_zero_of_eq_junction {s : ℕ} {z₀ : Fin s → ℂ} {φ r : Fin s → ℝ}
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k)) {τ : ℝ} {k : Fin s}
    (hrk : 0 < r k) (hτk : τ = φ k) : rho φ r τ = 0 := by
  rw [hτk]
  rw [rho_eq_norm_boundary z₀ φ r hz₀e (t := φ k)]
  rw [modelF_junction_value_zero z₀ r φ hz₀e (j := k) hrk]
  norm_num

/-- The uniform upper bound of ρ gives `BddAbove` for every arc image. -/
lemma bddAbove_rho_arc {s : ℕ} (φ r : Fin s → ℝ) (hr : ∀ k : Fin s, 0 ≤ r k)
    (a b : ℝ) : BddAbove (rho φ r '' Ioo a b) := by
  refine ⟨∏ k : Fin s, (2 : ℝ) ^ (2 * r k), ?_⟩
  intro y hy
  rcases hy with ⟨t, ht, rfl⟩
  exact rho_le_uniform_bound φ r hr t

/-- **The model-star tip maximum is at least 4^(1/s).**  Model data:
unit junctions `z₀ k = eAngle (φ k)` with sorted angles in `[0, 2π)`,
weights `0 < r k`, `Σ r k = 1`.  Then for some arc (i.e. for some
`j : Fin s`) the tip length `tip hs φ r j` of the model hedgehog is at
least `4^(1/s)`.  (Combined with ModelStarBoundary6/7's closed-arc sweeps
each such tip is attained by the boundary map, so the model star -- the
image of the unit circle under `modelF z₀ r` -- has a spike of length at
least `4^(1/s)`; the boundary correspondence shows that image is the
model hedgehog, cap 1.) -/
theorem max_tip_ge_four_rpow_inv {s : ℕ} (hs : 0 < s) (z₀ : Fin s → ℂ) (r φ : Fin s → ℝ)
    (hz₀e : ∀ k : Fin s, z₀ k = eAngle (φ k))
    (hsum : (∑ k : Fin s, r k) = 1)
    (hrpos : ∀ k : Fin s, 0 < r k) :
    ∃ j : Fin s, (4 : ℝ) ^ (1 / (s : ℝ)) ≤ tip hs φ r j := by
  classical
  have hrnonneg : ∀ k : Fin s, 0 ≤ r k := fun k => le_of_lt (hrpos k)
  have hz₀unit : ∀ k : Fin s, ‖z₀ k‖ = 1 := by
    intro k
    rw [hz₀e k]
    exact eAngle_norm (φ k)
  -- (1) KL point
  rcases (Submission.ModelStarShell.modelF_unit_sup_ge_four_rpow_inv hs z₀ hz₀unit r hrnonneg hsum)
    with ⟨w₀, hw₀unit, hw₀bound⟩
  rcases (Commons.Analysis.Complex.exp_I_mul_eq_of_norm_one hw₀unit) with ⟨σ, hσ⟩
  have hσe : eAngle σ = w₀ := by
    simpa [eAngle] using hσ
  -- ρ(σ) = ‖F w₀‖ ≥ 4^(1/s) > 0
  have h4pos : 0 < (4 : ℝ) ^ (1 / (s : ℝ)) := by
    exact Real.rpow_pos_of_pos (by norm_num) (1 / (s : ℝ))
  have hρσge : (4 : ℝ) ^ (1 / (s : ℝ)) ≤ rho φ r σ := by
    rw [rho_eq_norm_boundary z₀ φ r hz₀e (t := σ)]
    simpa [hσe] using hw₀bound
  have hρσpos : 0 < rho φ r σ := lt_of_lt_of_le h4pos hρσge
  -- (2) shift σ into the fundamental domain [φ 0, φ 0 + 2π)
  let φ₀ : ℝ := φ ⟨0, hs⟩
  let y : ℝ := (σ - φ₀) / (2 * Real.pi)
  let z : ℤ := Int.floor y
  let τ : ℝ := σ - (2 * Real.pi) * (z : ℝ)
  have hy1 : (z : ℝ) ≤ y := by
    dsimp [z]
    exact Int.floor_le y
  have hy2 : y < (z : ℝ) + 1 := by
    dsimp [z]
    exact Int.lt_floor_add_one y
  have h2ple : (z : ℝ) * (2 * Real.pi) ≤ σ - φ₀ := by
    have hm := (le_div_iff₀ two_pi_pos).mp hy1
    simpa [mul_comm] using hm
  have h2plt : σ - φ₀ < ((z : ℝ) + 1) * (2 * Real.pi) := by
    have hm := (div_lt_iff₀ two_pi_pos).mp hy2
    simpa [mul_comm] using hm
  have hτlo : φ₀ ≤ τ := by
    dsimp [τ]
    have h := h2ple
    linarith
  have hτlt : τ < φ₀ + 2 * Real.pi := by
    dsimp [τ]
    have h := h2plt
    linarith
  have hστ : σ = τ + (2 * Real.pi) * (z : ℝ) := by
    dsimp [τ]
    ring
  have hρτeq : rho φ r σ = rho φ r τ := by
    rw [hστ]
    exact rho_int_periodic φ r τ z
  have hρτpos : 0 < rho φ r τ := by
    rwa [← hρτeq]
  -- τ is not at a junction
  have hτne : ∀ k : Fin s, τ ≠ φ k := by
    intro k hk
    have h0 : rho φ r τ = 0 := rho_eq_zero_of_eq_junction hz₀e (hrpos k) hk
    exact (ne_of_gt hρτpos) h0
  have hτgtφ0 : φ₀ < τ := by
    apply lt_of_le_of_ne hτlo
    intro heq
    exact (hτne ⟨0, hs⟩) (by simpa [φ₀] using heq.symm)
  -- (3) partition: which arc contains τ ?
  let B : Finset (Fin s) := Finset.univ.filter (fun j : Fin s => τ < φ j)
  by_cases hB : B.Nonempty
  · -- consecutive-arc case: least index j with τ < φ j, then jj := j−1
    let j : Fin s := B.min' hB
    have hjB : j ∈ B := Finset.min'_mem B hB
    have hjτ : τ < φ j := by
      simpa [B] using (Finset.mem_filter.mp hjB).2
    have hj0 : j ≠ ⟨0, hs⟩ := by
      intro h0
      have hjτ0 : τ < φ ⟨0, hs⟩ := by simpa [h0] using hjτ
      have hτ0lt : φ ⟨0, hs⟩ < τ := by simpa [φ₀] using hτgtφ0
      exact (lt_asymm hτ0lt) hjτ0
    have hjval1 : 1 ≤ j.val := by
      by_contra h
      have hjv : j.val = 0 := by omega
      exact hj0 (Fin.ext hjv)
    have hjjval : j.val - 1 < s := by omega
    let jj : Fin s := ⟨j.val - 1, hjjval⟩
    have hjjc : jj.val + 1 < s := by
      dsimp [jj]
      omega
    have hjjltj : jj < j := by
      rw [Fin.lt_def]
      dsimp [jj]
      omega
    have hjjB : jj ∉ B := by
      intro hmem
      have hle := Finset.min'_le B jj hmem
      exact (not_le_of_gt hjjltj) hle
    have hφjjle : φ jj ≤ τ := by
      have hnot : ¬ τ < φ jj := by
        intro hlt
        exact hjjB (by simpa [B] using hlt)
      exact le_of_not_gt hnot
    have hφjjlt : φ jj < τ := lt_of_le_of_ne hφjjle (Ne.symm (hτne jj))
    have hτIoo : τ ∈ Ioo (φ jj) (φ j) := ⟨hφjjlt, hjτ⟩
    have hmem : rho φ r τ ∈ rho φ r '' Ioo (φ jj) (φ j) := ⟨τ, hτIoo, rfl⟩
    have hbdd : BddAbove (rho φ r '' Ioo (φ jj) (φ j)) := bddAbove_rho_arc φ r hrnonneg (φ jj) (φ j)
    have hle : rho φ r τ ≤ sSup (rho φ r '' Ioo (φ jj) (φ j)) := le_csSup hbdd hmem
    refine ⟨jj, ?_⟩
    dsimp [tip]
    rw [dif_pos hjjc]
    have hjsub : (⟨jj.val + 1, hjjc⟩ : Fin s) = j := by
      apply Fin.ext
      dsimp [jj]
      omega
    rw [hjsub]
    -- 4^(1/s) ≤ ρσ = ρτ ≤ sSup
    exact le_trans (by simpa [hρτeq] using hρσge) hle
  · -- wrap-around case: τ lies in (φ (s−1), φ 0 + 2π)
    have hnone : ∀ k : Fin s, k ∉ B := by
      intro k hkB
      exact hB ⟨k, hkB⟩
    have hφle : ∀ k : Fin s, φ k ≤ τ := by
      intro k
      have hnot : ¬ τ < φ k := by
        intro hlt
        exact hnone k (by simpa [B] using hlt)
      exact le_of_not_gt hnot
    have hφlastle : φ (wrapLast s hs) ≤ τ := hφle (wrapLast s hs)
    have hφlastlt : φ (wrapLast s hs) < τ :=
      lt_of_le_of_ne hφlastle (Ne.symm (hτne (wrapLast s hs)))
    have hτwrap : τ ∈ Ioo (φ (wrapLast s hs)) (φ ⟨0, hs⟩ + 2 * Real.pi) := by
      constructor
      · exact hφlastlt
      · dsimp [φ₀] at hτlt
        simpa [φ₀] using hτlt
    have hmem2 : rho φ r τ ∈ rho φ r '' Ioo (φ (wrapLast s hs)) (φ ⟨0, hs⟩ + 2 * Real.pi) :=
      ⟨τ, hτwrap, rfl⟩
    have hbdd2 : BddAbove (rho φ r '' Ioo (φ (wrapLast s hs)) (φ ⟨0, hs⟩ + 2 * Real.pi)) :=
      bddAbove_rho_arc φ r hrnonneg (φ (wrapLast s hs)) (φ ⟨0, hs⟩ + 2 * Real.pi)
    have hle2 : rho φ r τ ≤
        sSup (rho φ r '' Ioo (φ (wrapLast s hs)) (φ ⟨0, hs⟩ + 2 * Real.pi)) :=
      le_csSup hbdd2 hmem2
    refine ⟨wrapLast s hs, ?_⟩
    dsimp [tip]
    rw [dif_neg]
    · have hle3 : (4 : ℝ) ^ (1 / (s : ℝ)) ≤
          sSup (rho φ r '' Ioo (φ (wrapLast s hs)) (φ ⟨0, hs⟩ + 2 * Real.pi)) := by
        exact le_trans (by simpa [hρτeq] using hρσge) hle2
      exact hle3
    · intro hc
      have hv : (wrapLast s hs).val = s - 1 := rfl
      have hc' : s - 1 + 1 < s := by simpa [hv] using hc
      omega
