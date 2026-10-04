import Mathlib
import Submission.Work.Diff.Alg.Pinch.Chat_ray_thin
import Submission.Work.Diff.Alg.Pinch.Chat_margin
import Submission.Work.Diff.Alg.Pinch.ChatDefs
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound
import Submission.Work.Diff.Alg.Pinch.Ccone_norm_le_scal
import Submission.Work.Diff.Alg.Pinch.Ccone_mono_ge_half

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The structure of the Brendle–Schoen pinching family `Ĉ(s)`

Brendle–Schoen (arXiv 0705.0766, §3) construct a one-parameter family of closed convex
`O(n)`-invariant cones `Ĉ(s)` of algebraic curvature tensors, `s > 0`, each transversally invariant
under Hamilton's ODE `R' = Q(R)`, which shrinks (in the appropriate sense) to the ray `ℝ₊ · Iso n`
as `s → ∞`.  This file records three structural facts about the family
`Chat n s = Ĉ(s)` of `Submission/Work/Diff/Alg/Pinch/Chat.lean`:

1. **Uniform shape.**  For every `ε > 0` the cone `Ĉ(ε)` has bounded shape: there is a constant
   `C > 0` with `‖R‖ ≤ C · scalAlg R` for all `R ∈ Ĉ(ε)`.  (So the Euclidean norm of a tensor in
   the cone is controlled by its scalar curvature; the cone contains no nonzero tensor of
   nonpositive scalar curvature.)
2. **Monotonicity on the second branch.**  For `1/2 ≤ s ≤ s'` the family is decreasing:
   `Ĉ(s') ⊆ Ĉ(s)`.  (On the first branch `0 < s ≤ 1/2` this is *false* — see
   `Submission/Work/Diff/Alg/Pinch/Chat_mono_counterexample.lean` — which is why the hypothesis
   `1/2 ≤ s` is essential.)
3. **The intersection of the whole family is the ray `ℝ≥0 · Iso n`.**  A tensor lying in `Ĉ(s)` for
   all `s ≥ 1` must be a nonnegative multiple of the round-sphere tensor.

## Proofs

For `s ≥ 1/2` the definition of `Chat` reduces to the second branch
`Ĉ(s) = ℓ_{s,1/2}(D(p_s))`, `p_s = 1 - 4/((n-2) + 8s)` (`Chat_eq_Ccone_ge_half`; the two branches
agree at `s = 1/2`).

1. Immediate from `Work.Diff.Alg.Pinch.Ccone_norm_le_scal` applied to the parameters of the
   branch containing `ε` (the coefficient `1 + 2(n-1)a` of `scalAlg` under `ℓ_{a,b}` is positive,
   and `Dpic p` forces `scalAlg ≥ 0`).
2. `Work.Diff.Alg.Pinch.Ccone_mono_ge_half`: writing `R = ℓ_{s',1/2}X` with `X ∈ Dpic p_{s'}`, the
   preimage of `R` under `ℓ_{s,1/2}` is `Y = X + t·Iso n` with `t = 2(s'-s)·scal X/(n(1+2(n-1)s))`,
   and `Y ∈ Dpic p_s`: since `p_s ≤ p_{s'}` and `scal X ≥ 0`, the extra `Iso`-direction only helps
   the `RicPinch` condition, while `InPIC2` and `IsAlgCurv` are preserved by the nonnegative
   combination with `Iso n`.
3. `Work.Diff.Alg.Pinch.Chat_ray_thin` bounds the distance of every `R ∈ Ĉ(s)` to the ray
   `ℝ · Iso n` by `θ s · ‖R‖` with `θ s → 0`; a tensor lying in all `Ĉ(s)`, `s ≥ 1`, therefore has
   distance `0` from the ray, which is closed.  The sign of the multiple is read off from
   `scalAlg ≥ 0` (a consequence of `InPIC2`, via `(inPIC2_metric_basic n).2.2`).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## The second branch at `s = 1/2`, and the two branches agree there -/

/-- At `s = 1/2` the `a`-parameter of the first branch is `1/2`. -/
private lemma chatA_half (n : ℕ) : chatA n (1 / 2) = 1 / 2 := by
  have hD : (2 : ℝ) * (1 + ((n : ℝ) - 2) * (1 / 4)) ≠ 0 := by
    have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    intro hc
    have h0 : 1 + ((n : ℝ) - 2) * (1 / 4) = 0 := by
      rcases mul_eq_zero.mp hc with h1 | h2
      · norm_num at h1
      · exact h2
    nlinarith
  rw [chatA, show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num, div_eq_iff hD]
  ring

/-- At `s = 1/2` the `p`-parameter of the first branch equals the second-branch value. -/
private lemma chatP_half (n : ℕ) : chatP n (1 / 2) = 1 - 4 / ((n : ℝ) - 2 + 8 * (1 / 2)) := by
  have h1 : (1 : ℝ) + ((n : ℝ) - 2) * (1 / 4) ≠ 0 := by
    have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    intro hc; nlinarith
  have h2 : ((n : ℝ) - 2 + 8 * (1 / 2)) ≠ 0 := by
    have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    intro hc; nlinarith
  have hfrac : 1 / (1 + ((n : ℝ) - 2) * (1 / 4)) = 4 / ((n : ℝ) - 2 + 8 * (1 / 2)) := by
    rw [div_eq_div_iff h1 h2]; ring
  rw [chatP, show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num, hfrac]

/-- For `1 / 2 ≤ s` the Brendle–Schoen cone is the second-branch Böhm–Wilking cone
`Ĉ(s) = ℓ_{s,1/2}(D(p))` with `p = 1 - 4/((n-2) + 8s)`.  (The two branches agree at `s = 1/2`.) -/
lemma Chat_eq_Ccone_ge_half (n : ℕ) {s : ℝ} (hs : 1 / 2 ≤ s) :
    Chat n s = Ccone (n := n) s (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * s)) := by
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    rw [Chat_eq_Ccone n le_rfl, chatA_half, chatP_half]
  · rw [Chat, ite_eq_right (not_le.mpr h)]

/-! ## The intersection of the family is the ray `ℝ≥0 · Iso n` -/

/-- The family `Chat n s` is decreasing on the second branch, so the intersection over `s ≥ 1`
equals the "limit cone".  The ray `ℝ · Iso n` is closed, and `Chat_ray_thin` says that every
`R ∈ Chat n s` is within `θ s · ‖R‖` of it with `θ s → 0`; consequently any `R` lying in all the
cones `Chat n s`, `s ≥ 1`, lies on the ray.  Its sign is then fixed by `scalAlg ≥ 0`. -/
lemma Chat_inter_ray (n : ℕ) (hn : 2 ≤ n) {R : Curv4 n}
    (hR : ∀ s : ℝ, 1 ≤ s → R ∈ Chat n s) : ∃ c : ℝ, 0 ≤ c ∧ R = c • Iso n := by
  obtain ⟨θ, _hθpos, hθsmall, hthin⟩ := Chat_ray_thin n hn
  have hzero : Metric.infDist R (Set.range fun μ : ℝ => μ • Iso n) = 0 := by
    refine le_antisymm ?_ Metric.infDist_nonneg
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    obtain ⟨S, hS⟩ := hθsmall (δ / (‖R‖ + 1)) (by positivity)
    have hs1 : (1 : ℝ) ≤ max S 1 := le_max_right _ _
    have hs0 : (0 : ℝ) < max S 1 := lt_of_lt_of_le one_pos hs1
    have h1 : Metric.infDist R (Set.range fun μ : ℝ => μ • Iso n) ≤ θ (max S 1) * ‖R‖ :=
      hthin (max S 1) hs0 R (hR (max S 1) hs1)
    have h2 : θ (max S 1) ≤ δ / (‖R‖ + 1) := hS (max S 1) (le_max_left _ _)
    have h3 : θ (max S 1) * ‖R‖ ≤ (δ / (‖R‖ + 1)) * ‖R‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg R)
    have h4 : (δ / (‖R‖ + 1)) * ‖R‖ ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < ‖R‖ + 1)]
      nlinarith [norm_nonneg R, hδ.le]
    linarith
  have hnonempty : (Set.range fun μ : ℝ => μ • Iso n).Nonempty := ⟨0, ⟨0, by simp⟩⟩
  have hmem : R ∈ closure (Set.range fun μ : ℝ => μ • Iso n) :=
    (Metric.mem_closure_iff_infDist_zero hnonempty).mpr hzero
  have hclosed : IsClosed (Set.range fun μ : ℝ => μ • Iso n) := by
    rw [← show (Submodule.span ℝ ({Iso n} : Set (Curv4 n)) : Set (Curv4 n)) =
        Set.range (fun μ : ℝ => μ • Iso n) from by
      ext x; simp [Submodule.mem_span_singleton, Set.mem_range]]
    exact Submodule.closed_of_finiteDimensional _
  rw [hclosed.closure_eq] at hmem
  obtain ⟨c, rfl⟩ := hmem
  refine ⟨c, ?_, rfl⟩
  -- the sign of the multiple, from `scalAlg ≥ 0` on the cone
  have hR1 : (c • Iso n) ∈ Chat n 1 := hR 1 le_rfl
  rw [Chat_eq_Ccone_ge_half n (by norm_num : (1 : ℝ) / 2 ≤ 1)] at hR1
  obtain ⟨X, hX, hXR⟩ := hR1
  have hσ : 0 ≤ scalAlg X := (inPIC2_metric_basic n).2.2 X hX.2.1
  have hcoeff : 0 ≤ 1 + 2 * ((n : ℝ) - 1) * (1 : ℝ) := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hscal : 0 ≤ scalAlg (c • Iso n) := by
    rw [← hXR, scalAlg_ell]
    exact mul_nonneg hcoeff hσ
  have hIso_pos : 0 < scalAlg (Iso n) := by
    rw [scalAlg_iso]
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  rw [scalAlg_smul] at hscal
  exact nonneg_of_mul_nonneg_left hscal hIso_pos

/-! ## The structure theorem -/

theorem Chat_family_structure (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    (∃ C : ℝ, 0 < C ∧ ∀ R : Submission.Diff.Alg.Curv4 n,
      R ∈ Work.Diff.Alg.Pinch.Chat n ε → ‖R‖ ≤ C * Submission.Diff.Alg.scalAlg R) ∧
    (∀ s s' : ℝ, 1 / 2 ≤ s → s ≤ s' →
      Work.Diff.Alg.Pinch.Chat n s' ⊆ Work.Diff.Alg.Pinch.Chat n s) ∧
    (∀ R : Submission.Diff.Alg.Curv4 n, (∀ s : ℝ, 1 ≤ s → R ∈ Work.Diff.Alg.Pinch.Chat n s) →
      ∃ c : ℝ, 0 ≤ c ∧ R = c • Submission.Diff.Alg.Iso n) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (1) `‖R‖ ≤ C · scalAlg R` on `Ĉ(ε)`
    rcases le_or_gt ε (1 / 2) with hε2 | hε2
    · obtain ⟨C, hCpos, hC⟩ :=
        Ccone_norm_le_scal n hn (chatA n ε) ε (chatP n ε) (chatA_nonneg hn hε.le)
      exact ⟨C, hCpos, fun R hR => hC R (by rwa [Chat_eq_Ccone n hε2] at hR)⟩
    · obtain ⟨C, hCpos, hC⟩ :=
        Ccone_norm_le_scal n hn ε (1 / 2) (1 - 4 / ((n : ℝ) - 2 + 8 * ε)) hε.le
      exact ⟨C, hCpos, fun R hR =>
        hC R (by rwa [Chat_eq_Ccone_ge_half n hε2.le] at hR)⟩
  · -- (2) monotonicity for `1/2 ≤ s ≤ s'`
    intro s s' hs hss' R hR
    have hs' : 1 / 2 ≤ s' := le_trans hs hss'
    rw [Chat_eq_Ccone_ge_half n hs'] at hR
    rw [Chat_eq_Ccone_ge_half n hs]
    exact Ccone_mono_ge_half n hn s s' hs hss' hR
  · -- (3) the intersection of the family is the ray `ℝ≥0 · Iso`
    intro R hR
    exact Chat_inter_ray n hn hR

end Work.Diff.Alg.Pinch
