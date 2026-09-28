import Mathlib
import Submission.Work.HP.GonLib
import Submission.Work.HP.FM.RecDefs
import Submission.Work.HP.FM.latStepAux
import Submission.Work.HP.LatRecurse.ncard_int_interval
import Submission.Work.HP.LatRecurse.ncard_fiber_le

/-!
# Fibre count for one Schmidt recursion step (the `EEupper` interface)

Given a `RecData D` (an injective real presentation `D.Φ` of a rank-`R` lattice, a primitive
coefficient vector `D.u`, and a complementary family `D.v` completing `u` to a `ℤ`-basis of
`ℤ^R`), we bound the number of lattice points of `D.Φ` of norm `≤ T` in terms of those of the
projected presentation `D.step = latStep D.Φ D.u D.v`:

`#(latSet D.Φ T) ≤ (2T/‖D.p‖ + 1) · #(latSet D.step T)`,   `D.p = D.Φ u`.

The proof is the usual fibre count.  Writing `x ∈ ℤ^R` in the `ℤ`-basis `(u, v)` as
`x = a • u + Σ w_i v_i`, Pythagoras gives

`‖Φ x‖² = ‖D.step w‖² + (⟪Φ (Σ w_i v_i), p⟫/‖p‖² + a)² ‖p‖²`,

so for fixed `w` the integer `a` lies in an interval of length `2T/‖p‖`, whence the fibre over
`w` has at most `⌊2T/‖p‖⌋ + 1` elements.  Summing over the possible `w` (which lie in
`latSet D.step T`) yields the statement.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.EEupper

theorem latStepCountB {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} (D : Work.HP.FM.RecData R ι) {T : ℝ} (hT : 0 ≤ T) :
    (Work.HP.latCount D.Φ T : ℝ) ≤ (2 * T / ‖D.p‖ + 1) * (Work.HP.latCount D.step T : ℝ) := by
  classical
  have hp : 0 < ‖D.p‖ := D.norm_p_pos
  set K : ℕ := Nat.floor (2 * (T / ‖D.p‖)) + 1 with hKdef
  set S : Set (ℤ × (Fin (R - 1) → ℤ)) := D.coords '' Work.HP.latSet D.Φ T with hSdef
  have hKle : (K : ℝ) ≤ 2 * T / ‖D.p‖ + 1 := by
    have h0 : (0 : ℝ) ≤ 2 * (T / ‖D.p‖) := by positivity
    have h1 : ((Nat.floor (2 * (T / ‖D.p‖)) : ℕ) : ℝ) ≤ 2 * (T / ‖D.p‖) := Nat.floor_le h0
    have h2 : 2 * (T / ‖D.p‖) = 2 * T / ‖D.p‖ := by ring
    simp only [hKdef]
    push_cast
    linarith
  have hfiber : ∀ w : Fin (R - 1) → ℤ, {a : ℤ | (a, w) ∈ S}.ncard ≤ K := by
    intro w
    have hsub : {a : ℤ | (a, w) ∈ S} ⊆
        {a : ℤ | |(a : ℝ) +
          inner ℝ (D.Φ (fun k => ((∑ j, w j • D.v j) k : ℝ))) D.p / ‖D.p‖ ^ 2| ≤ T / ‖D.p‖} := by
      intro a ha
      rw [hSdef] at ha
      have hy : D.decompFun (a, w) ∈ Work.HP.latSet D.Φ T := (D.mem_coords_image _ a w).mp ha
      rw [Work.HP.latSet, Set.mem_ofPred_eq] at hy
      have hsq : ‖D.Φ (fun k => ((D.decompFun (a, w)) k : ℝ))‖ ^ 2 =
          ‖D.step (fun j => (w j : ℝ))‖ ^ 2 +
            (inner ℝ (D.Φ (fun k => ((∑ j, w j • D.v j) k : ℝ))) D.p / ‖D.p‖ ^ 2 + (a : ℝ)) ^ 2
              * ‖D.p‖ ^ 2 := by
        have h1 : D.Φ (fun k => ((D.decompFun (a, w)) k : ℝ)) =
            (a : ℝ) • D.p + D.Φ (fun k => ((∑ j, w j • D.v j) k : ℝ)) :=
          D.Phi_cast_bij a w
        rw [h1, add_comm]
        rw [Work.HP.norm_sq_add_smul D.p (a : ℝ) (D.Φ (fun k => ((∑ j, w j • D.v j) k : ℝ)))]
        rw [show Work.HP.projU D.p (D.Φ (fun k => ((∑ j, w j • D.v j) k : ℝ))) =
            D.step (fun j => (w j : ℝ)) from (D.step_cast w).symm]
      have hT2 : ‖D.Φ (fun k => ((D.decompFun (a, w)) k : ℝ))‖ ^ 2 ≤ T ^ 2 := by
        nlinarith [hy, norm_nonneg (D.Φ (fun k => ((D.decompFun (a, w)) k : ℝ))), hT]
      rw [hsq] at hT2
      have hkey2 : (inner ℝ (D.Φ (fun k => ((∑ j, w j • D.v j) k : ℝ))) D.p / ‖D.p‖ ^ 2
            + (a : ℝ)) ^ 2 * ‖D.p‖ ^ 2 ≤ T ^ 2 := by
        linarith [hT2, sq_nonneg ‖D.step (fun j => (w j : ℝ))‖]
      have h5 : |inner ℝ (D.Φ (fun k => ((∑ j, w j • D.v j) k : ℝ))) D.p / ‖D.p‖ ^ 2 + (a : ℝ)|
            * ‖D.p‖ ≤ T := by
        have h6 : (|inner ℝ (D.Φ (fun k => ((∑ j, w j • D.v j) k : ℝ))) D.p / ‖D.p‖ ^ 2
              + (a : ℝ)| * ‖D.p‖) ^ 2 ≤ T ^ 2 := by
          rw [mul_pow, sq_abs]; exact hkey2
        have h7 := sq_le_sq.mp h6
        rwa [abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)), abs_of_nonneg hT] at h7
      show |(a : ℝ) + inner ℝ (D.Φ (fun k => ((∑ j, w j • D.v j) k : ℝ))) D.p / ‖D.p‖ ^ 2|
          ≤ T / ‖D.p‖
      rw [add_comm (a : ℝ), le_div_iff₀ hp]
      exact h5
    refine le_trans (Set.ncard_le_ncard hsub (Work.HP.FM.finite_int_abs_add_le _ _)) ?_
    exact Work.HP.FM.ncard_le_int_interval (c :=
      inner ℝ (D.Φ (fun k => ((∑ j, w j • D.v j) k : ℝ))) D.p / ‖D.p‖ ^ 2)
      (M := T / ‖D.p‖) (by positivity) (fun a ha => ha)
  have hcard2 : S.ncard ≤ K * (S.image Prod.snd).ncard :=
    Work.HP.LatRecurse.ncard_fiber_le S K hfiber
  have hcard3 : (S.image Prod.snd).ncard ≤ (Work.HP.latSet D.step T).ncard := by
    refine Set.ncard_le_ncard ?_ ?_
    · rintro w ⟨q, hq, rfl⟩
      rw [hSdef] at hq
      have hy : D.decompFun q ∈ Work.HP.latSet D.Φ T := (D.mem_coords_image _ q.1 q.2).mp hq
      have hc : D.coords (D.decompFun q) = q := D.coords_decompFun q.1 q.2
      have hmem := D.coords_snd_mem_latSet_step hy
      rwa [hc] at hmem
    · exact Work.HP.latVec_finite D.step D.step_injective T
  have hmain : S.ncard ≤ K * (Work.HP.latSet D.step T).ncard :=
    le_trans hcard2 (Nat.mul_le_mul_left K hcard3)
  have hcard1 : (Work.HP.latCount D.Φ T : ℝ) = (S.ncard : ℝ) := by
    rw [Work.HP.latCount, hSdef, Set.ncard_image_of_injective _ D.coords_injective]
  rw [hcard1]
  calc (S.ncard : ℝ) ≤ (K : ℝ) * (Work.HP.latCount D.step T : ℝ) := by
        rw [Work.HP.latCount]; exact_mod_cast hmain
    _ ≤ (2 * T / ‖D.p‖ + 1) * (Work.HP.latCount D.step T : ℝ) :=
        mul_le_mul_of_nonneg_right hKle (Nat.cast_nonneg _)


end Work.EEupper
