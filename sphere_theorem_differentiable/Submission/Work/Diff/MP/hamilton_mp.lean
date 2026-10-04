import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.MP.TruncKit
import Submission.Work.Diff.MP.TruncDefs
import Submission.Work.Diff.MP.Defs
import Submission.Work.Diff.MP.curv_frobNorm_bound
import Submission.Work.Diff.MP.max_principle_lsc
import Submission.Work.Diff.MP.frobDot_rot
import Submission.Work.Diff.MP.trunc_push_growing
import Submission.Work.Diff.MP.frob_nearest_supporting
import Submission.Work.Diff.MP.frobInfDist_rmFrame_eq
import Submission.Work.Diff.MP.hessAt_nonpos_of_isLocalMax
import Submission.Work.Diff.MP.sup_dist_regular
import Submission.Work.Diff.MP.trunc_model

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Hamilton's maximum principle for time-dependent invariant families (`Work.Diff.MP.hamilton_mp`)

Target: `PinchingPreserved I M` from `LCSmooth`, `LCVariation`, `CurvEvolution` and
`LapRmFrameParallel`.  The vocabulary used below (`frobDot`, `frobDist`, `frobInfDist`, `frobBall`,
`rmFrame_mem_of_rmC_mem`, ...) lives in `Submission.Work.Diff.MP.Basic`; the analysis pieces proved
by the delegated lemmas are in the sibling modules
`Submission.Work.Diff.MP.{frobDot_rot, isCompact_frobBall, frob_nearest_supporting,
frobDot_nonpos_of_frobDist_min, dini_first_exit, ode_push_forward_of_invariant,
hessAt_nonpos_of_isLocalMax, frobInfDist_rmFrame_eq, max_principle}`.

See `Submission/Work/Diff/MP/NOTES.md` for the design of the proof.  The geometric inputs are the
delegated lemmas of this area: the curvature bound (`curv_frobNorm_bound`), the truncation data
(`trunc_push_growing`), the regularity of the truncated supremum (`sup_dist_regular`) and the local
orthonormal-frame model (`trunc_model`, built from the square-root frame `e s = Γ s^{-1/2} Ef`).

NOTE on module dependencies: the sibling modules must import `Basic` (not this file) so that this
file can import them; otherwise there is an import cycle.
-/

set_option maxHeartbeats 8000000

namespace Work.Diff.MP

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric





/-! ## The truncated radius function

`growRad ϱ Λ` has a pole at `1/Λ`; the regularity lemmas (`sup_dist_regular`) need a radius
function that agrees with it on the shot `[0, ε]` (`ε ≤ 1/(2Λ)`) and is continuous and positive
everywhere, so we freeze it at `ε`: `truncRad ϱ Λ ε s = growRad ϱ Λ (min s ε)`. -/

/-- The truncated radius function: `growRad ϱ Λ` on `(-∞, ε]`, constant afterwards. -/
noncomputable def truncRad (ϱ Λ ε : ℝ) : ℝ → ℝ := fun s => growRad ϱ Λ (min s ε)

theorem truncRad_of_le {ϱ Λ ε s : ℝ} (h : s ≤ ε) : truncRad ϱ Λ ε s = growRad ϱ Λ s := by
  simp only [truncRad, min_eq_left h]

theorem truncRad_self {ϱ Λ ε : ℝ} : truncRad ϱ Λ ε ε = growRad ϱ Λ ε := by
  simp only [truncRad, min_self]

/-- `1 - Λ u ≥ 1/2` on `u ≤ ε` when `ε ≤ 1/(2Λ)`. -/
theorem one_sub_mul_pos {Λ ε u : ℝ} (hΛ : 0 < Λ) (hεΛ : ε ≤ 1 / (2 * Λ)) (hu : u ≤ ε) :
    (0 : ℝ) < 1 - Λ * u := by
  have h2 : Λ * ε ≤ 1 / 2 := by
    have h : Λ * ε ≤ Λ * (1 / (2 * Λ)) := mul_le_mul_of_nonneg_left hεΛ hΛ.le
    have h3 : Λ * (1 / (2 * Λ)) = 1 / 2 := by field_simp
    linarith [h, h3.le, h3.ge]
  have h3 : Λ * u ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_left hu hΛ.le) h2
  linarith

theorem truncRad_pos {ϱ Λ ε : ℝ} (hϱ : 0 < ϱ) (hΛ : 0 < Λ) (hεΛ : ε ≤ 1 / (2 * Λ)) :
    ∀ s, 0 < truncRad ϱ Λ ε s := by
  intro s
  exact div_pos hϱ (one_sub_mul_pos hΛ hεΛ (min_le_right s ε))

theorem truncRad_mono {ϱ Λ ε s : ℝ} (hϱ : 0 < ϱ) (hΛ : 0 < Λ) (hεΛ : ε ≤ 1 / (2 * Λ))
    (hs : s ≤ ε) : truncRad ϱ Λ ε s ≤ truncRad ϱ Λ ε ε := by
  have h1 : min s ε ≤ ε := min_le_right s ε
  have h4 : 1 - Λ * min ε ε ≤ 1 - Λ * min s ε := by
    rw [min_self]
    nlinarith [h1, hΛ]
  have h6 : 0 < 1 - Λ * min ε ε := one_sub_mul_pos hΛ hεΛ (min_le_right ε ε)
  simp only [truncRad]
  exact div_le_div_of_nonneg_left hϱ.le h6 h4

theorem continuous_truncRad (ϱ Λ ε : ℝ) (hΛ : 0 < Λ) (hεΛ : ε ≤ 1 / (2 * Λ)) :
    Continuous (truncRad ϱ Λ ε) := by
  have hmem : ∀ s : ℝ, min s ε ∈ Set.Iic ε := fun s => min_le_right s ε
  have hcon : ContinuousOn (growRad ϱ Λ) (Set.Iic ε) := by
    unfold growRad
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
    · intro u hu
      exact ne_of_gt (one_sub_mul_pos hΛ hεΛ hu)
  exact hcon.comp_continuous (continuous_id.min continuous_const) hmem


/-- The growth rate of the truncation is at most `2ϱ` on the shot. -/
theorem growRad_le_two' {ϱ Λ ε : ℝ} (hϱ : 0 < ϱ) (hΛ : 0 < Λ) (hεΛ : ε ≤ 1 / (2 * Λ)) :
    growRad ϱ Λ ε ≤ 2 * ϱ := by
  have h2 : Λ * ε ≤ 1 / 2 := by
    have h9 : Λ * ε ≤ Λ * (1 / (2 * Λ)) := mul_le_mul_of_nonneg_left hεΛ hΛ.le
    have h10 : Λ * (1 / (2 * Λ)) = 1 / 2 := by field_simp
    linarith [h9, h10.le, h10.ge]
  have h11 : (0 : ℝ) < 1 - Λ * ε := by linarith
  rw [growRad, div_le_iff₀ h11]
  nlinarith [hϱ, h2]

/-- A uniform bound for `Q` on the Frobenius ball of radius `2ϱ`. -/
theorem frobNorm_Q_le (n : ℕ) (ϱ : ℝ) (hϱ : 0 ≤ ϱ) {R : Curv4 n} (hR : frobNorm R ≤ 2 * ϱ) :
    frobNorm (Q R) ≤ (n : ℝ) ^ 2 * (5 * (n : ℝ) ^ 2 * (2 * ϱ) ^ 2) := by
  have hR2 : ‖R‖ ≤ 2 * ϱ := le_trans (norm_le_frobNorm R) hR
  have h0 : ‖Q R - Q (0 : Curv4 n)‖ ≤ 5 * (n : ℝ) ^ 2 * (‖R‖ + ‖(0 : Curv4 n)‖) * ‖R - 0‖ :=
    Q_sub_norm_le n R 0
  have hQ0 : Q (0 : Curv4 n) = 0 := by
    funext i j k l
    simp [Submission.Diff.Alg.Q]
  rw [hQ0, sub_zero, sub_zero, norm_zero, add_zero] at h0
  have h3 : ‖R‖ * ‖R‖ ≤ (2 * ϱ) * (2 * ϱ) :=
    mul_le_mul hR2 hR2 (norm_nonneg _) (by linarith)
  have h4 : (0 : ℝ) ≤ 5 * (n : ℝ) ^ 2 := by positivity
  have h5 : 5 * (n : ℝ) ^ 2 * ‖R‖ * ‖R‖ ≤ 5 * (n : ℝ) ^ 2 * ((2 * ϱ) * (2 * ϱ)) := by
    nlinarith [h3, h4, norm_nonneg R]
  calc frobNorm (Q R) ≤ (n : ℝ) ^ 2 * ‖Q R‖ := frobNorm_le_mul_norm _
    _ ≤ (n : ℝ) ^ 2 * (5 * (n : ℝ) ^ 2 * ((2 * ϱ) * (2 * ϱ))) :=
        mul_le_mul_of_nonneg_left (le_trans h0 h5) (by positivity)
    _ = (n : ℝ) ^ 2 * (5 * (n : ℝ) ^ 2 * (2 * ϱ) ^ 2) := by ring

/-- The `Q`-Lipschitz bound on a Frobenius ball, with the explicit constant. -/
theorem Q_lipschitz_ball (n : ℕ) (M₀ : ℝ) (hM₀ : 0 ≤ M₀) :
    ∀ R S : Curv4 n, frobNorm R ≤ M₀ → frobNorm S ≤ M₀ →
      frobDist (Q R) (Q S) ≤ (5 * (n : ℝ) ^ 4 * (2 * M₀)) * frobDist R S := by
  intro R S hR hS
  have h2 : frobNorm (Q R - Q S) ≤ (n : ℝ) ^ 2 * ‖Q R - Q S‖ := frobNorm_le_mul_norm _
  have h3 : ‖Q R - Q S‖ ≤ 5 * (n : ℝ) ^ 2 * (‖R‖ + ‖S‖) * ‖R - S‖ := Q_sub_norm_le n R S
  have h4 : ‖R‖ ≤ M₀ := le_trans (norm_le_frobNorm R) hR
  have h5 : ‖S‖ ≤ M₀ := le_trans (norm_le_frobNorm S) hS
  have h6 : ‖R - S‖ ≤ frobDist R S := norm_le_frobNorm (R - S)
  have h7 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  calc frobDist (Q R) (Q S) = frobNorm (Q R - Q S) := rfl
    _ ≤ (n : ℝ) ^ 2 * ‖Q R - Q S‖ := h2
    _ ≤ (n : ℝ) ^ 2 * (5 * (n : ℝ) ^ 2 * (‖R‖ + ‖S‖) * ‖R - S‖) :=
        mul_le_mul_of_nonneg_left h3 h7
    _ ≤ (n : ℝ) ^ 2 * (5 * (n : ℝ) ^ 2 * (M₀ + M₀) * frobDist R S) := by
        apply mul_le_mul_of_nonneg_left _ h7
        have h9 : ‖R‖ + ‖S‖ ≤ M₀ + M₀ := add_le_add h4 h5
        have h11 : (0 : ℝ) ≤ 5 * (n : ℝ) ^ 2 := by positivity
        have h12 : (0 : ℝ) ≤ ‖R - S‖ := norm_nonneg _
        calc 5 * (n : ℝ) ^ 2 * (‖R‖ + ‖S‖) * ‖R - S‖
            ≤ 5 * (n : ℝ) ^ 2 * (M₀ + M₀) * ‖R - S‖ := by
              apply mul_le_mul_of_nonneg_right _ h12
              apply mul_le_mul_of_nonneg_left h9 h11
          _ ≤ 5 * (n : ℝ) ^ 2 * (M₀ + M₀) * frobDist R S := by
              apply mul_le_mul_of_nonneg_left h6
              positivity
    _ = (5 * (n : ℝ) ^ 4 * (2 * M₀)) * frobDist R S := by ring


/-! ## One shot of the bootstrap

This is the heart of the assembly: given the conclusion at time `τ`, the time-dependent maximum
principle (`max_principle_lsc`) applied on the shot `[τ, min (τ+ε) T'']` to the truncated family
`F t ∩ frobBall (truncRad ϱ Λ ε (t - τ))` propagates it to the whole shot.

The three geometric inputs of `max_principle_lsc` beyond the truncation are taken as explicit
hypotheses, because they are the (separately delegated) content of
* `trunc_push_growing` (the one-step push, `hpush` below) and the non-emptiness `hne`,
* `sup_dist_regular` (lower semicontinuity `hlsc` and right upper semicontinuity `hrusc` of the
  supremum of the distance), and
* `trunc_model` (the orthonormal-frame model `hmodel`). -/
theorem pinching_shot
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [Nonempty M]
    (hLC : LCSmooth I M) (hLP : LapRmFrameParallel I M)
    {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    {F : ℝ → Set (Curv4 (Module.finrank ℝ E))} (hF : IsInvariantFamily F)
    {ρ₁ ϱ Λ ε τ T'' C C' : ℝ}
    (hρ₁ : ∀ x : M, frobNorm (rmC (G τ) x) ≤ ρ₁)
    (hρϱ : ρ₁ + 1 ≤ ϱ)
    (hϱ : 0 < ϱ) (hΛ : 0 < Λ) (hε : 0 < ε) (hεΛ : ε ≤ 1 / (2 * Λ))
    (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hQlip : ∀ R S : Curv4 (Module.finrank ℝ E),
      frobNorm R ≤ 2 * ϱ → frobNorm S ≤ 2 * ϱ → frobDist (Q R) (Q S) ≤ C * frobDist R S)
    (hτ0 : 0 ≤ τ) (hτT'' : τ < T'') (hT''T : T'' < T)
    (hP : ∀ t ∈ Set.Icc 0 τ, CurvIn (G t) (F t))
    (hpush : ∀ t ∈ Set.Ico τ T'', ∀ h : ℝ, 0 < h → h ≤ min (τ + ε) T'' - t →
      ∀ S ∈ F t ∩ frobBall (truncRad ϱ Λ ε (t - τ)),
        ∃ S' ∈ F (t + h) ∩ frobBall (truncRad ϱ Λ ε (t + h - τ)),
          frobDist S' (S + h • Q S) ≤ C' * h ^ 2)
    (hne : ∀ t ∈ Set.Icc τ (min (τ + ε) T''),
      (F t ∩ frobBall (truncRad ϱ Λ ε (t - τ))).Nonempty)
    (hlsc : ∀ t ∈ Set.Icc τ (min (τ + ε) T''), ∀ ε' > 0, ∃ δ > 0,
      ∀ s ∈ Set.Icc τ (min (τ + ε) T''), |s - t| ≤ δ →
        truncSup G F (fun u => truncRad ϱ Λ ε (u - τ)) t
          ≤ truncSup G F (fun u => truncRad ϱ Λ ε (u - τ)) s + ε')
    (hrusc : ∀ t ∈ Set.Ico τ (min (τ + ε) T''), ∀ ε' > 0, ∃ δ > 0,
      ∀ h : ℝ, 0 < h → h ≤ δ → t + h ≤ min (τ + ε) T'' →
        truncSup G F (fun u => truncRad ϱ Λ ε (u - τ)) (t + h)
          ≤ truncSup G F (fun u => truncRad ϱ Λ ε (u - τ)) t + ε')
    (hmodel : ∀ t ∈ Set.Ioo τ (min (τ + ε) T''), ∀ x : M,
      ∃ (δ : ℝ) (_ : 0 < δ) (U : Set M) (_ : U ∈ nhds x)
        (Rl dRl : ℝ → M → Curv4 (Module.finrank ℝ E)),
        (∀ s ∈ Set.Icc t (t + δ), ∀ y ∈ U,
          truncDist G F (fun u => truncRad ϱ Λ ε (u - τ)) s y
            = frobInfDist (Rl s y) (F s ∩ frobBall (truncRad ϱ Λ ε (s - τ)))) ∧
        ContinuousOn (fun p : ℝ × M => (Rl p.1 p.2, dRl p.1 p.2))
          (Set.prod (Set.Icc t (t + δ)) U) ∧
        (∀ ε' > 0, ∃ δ' > 0, ∀ h : ℝ, 0 < h → h ≤ δ' → ∀ y ∈ U,
          frobDist (Rl (t + h) y) (Rl t y + h • (dRl t y + Q (Rl t y))) ≤ ε' * h) ∧
        (∀ ℓ : Curv4 (Module.finrank ℝ E), frobNorm ℓ ≤ 1 →
          (∀ z ∈ U, frobDot ℓ (Rl t z) ≤ frobDot ℓ (Rl t x)) → frobDot ℓ (dRl t x) ≤ 0) ∧
        (∀ y ∈ U, ∀ S ∈ F t ∩ frobBall (truncRad ϱ Λ ε (t - τ)),
          frobDist (Q (Rl t y)) (Q S) ≤ C * frobDist (Rl t y) S)) :
    ∀ t ∈ Set.Icc 0 (min (τ + ε) T''), CurvIn (G t) (F t) := by
  intro t ht
  by_cases hle : t ≤ τ
  · exact hP t ⟨ht.1, hle⟩
  · push_neg at hle
    set b : ℝ := min (τ + ε) T'' with hb
    have hbτ : τ ≤ b := le_min (by linarith) hτT''.le
    have hbt : t ≤ b := ht.2
    have htτ : τ < t := hle
    -- the non-emptiness at the initial time of the shot
    have htr : truncRad ϱ Λ ε (τ - τ) = ϱ := by
      have h1 : (τ - τ : ℝ) ≤ ε := by linarith
      rw [truncRad_of_le h1]
      simp only [growRad, sub_self, mul_zero, sub_zero, div_one]
    have hcurvτ : ∀ x : M, rmC (G τ) x ∈ F τ ∩ frobBall (truncRad ϱ Λ ε (τ - τ)) := by
      intro x
      refine ⟨?_, ?_⟩
      · have hCτ : CurvIn (G τ) (F τ) := hP τ ⟨hτ0, le_rfl⟩
        exact hCτ x (onFrame (G τ) x) (Work.Diff.GE.isONFrame_onFrame (G τ) x)
      · rw [htr]
        exact le_trans (hρ₁ x) (by linarith [hρϱ])
    have hKne0 : (F τ ∩ frobBall (truncRad ϱ Λ ε (τ - τ))).Nonempty :=
      ⟨rmC (G τ) (Classical.arbitrary M), hcurvτ _⟩
    -- the maximum principle on the shot
    have hconcl : ∀ s ∈ Set.Icc τ b, ∀ x : M,
        truncDist G F (fun u => truncRad ϱ Λ ε (u - τ)) s x = 0 :=
      max_principle_lsc (n := Module.finrank ℝ E) (X := M)
        (fun s : ℝ => F s ∩ frobBall (truncRad ϱ Λ ε (s - τ)))
        (fun s x => truncDist G F (fun u => truncRad ϱ Λ ε (u - τ)) s x)
        hbτ hC
        (fun s _ => (isClosed_fibre_of_isClosed_track hF.1 s).inter (isClosed_frobBall _))
        (fun s _ => (hF.2.1 s).inter (convex_frobBall _))
        (fun s hs => hne s ⟨hs.1, by rw [hb]; exact hs.2⟩)
        (fun s hs => ⟨truncRad ϱ Λ ε ε, fun S hS => le_trans hS.2
          (truncRad_mono hϱ hΛ hεΛ (by
            have := hs.2
            rw [hb] at this
            linarith [min_le_left (τ + ε) T'']))⟩)
        (fun s _ x => frobInfDist_nonneg _ _)
        (fun s _ => (continuous_frobInfDist_truncFam (I := I) (M := M) hLC hLP (G s) hF
          (fun u => truncRad ϱ Λ ε (u - τ)) s).continuousOn)
        (fun s hs => hlsc s ⟨hs.1, by rw [hb]; exact hs.2⟩)
        (fun s hs => hrusc s ⟨hs.1, by rw [hb]; exact hs.2⟩)
        (fun s hs => by
          refine ⟨min (τ + ε) T'' - s, by
            have h1 := hs.2
            rw [hb] at h1
            linarith, C', fun h hh hle' S hS => ?_⟩
          obtain ⟨S', hS'1, hS'2⟩ := hpush s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩ h hh hle' S hS
          exact ⟨S', hS'1, hS'2⟩)
        (fun s hs x => by
          obtain ⟨δ, hδ, U, hU, Rl, dRl, h1, h2, h3, h4, h5⟩ :=
            hmodel s ⟨hs.1, by rw [hb] at hs; exact hs.2⟩ x
          exact ⟨δ, hδ, U, hU, Rl, dRl, h1, h2, h3, h4, h5⟩)
        (fun x => frobInfDist_eq_zero_of_mem (hcurvτ x))
    intro x e he
    have hmem : rmC (G t) x ∈ F t ∩ frobBall (truncRad ϱ Λ ε (t - τ)) :=
      mem_of_frobInfDist_eq_zero
        ((isClosed_fibre_of_isClosed_track hF.1 t).inter (isClosed_frobBall _))
        (hne t ⟨htτ.le, hbt⟩)
        (hconcl t ⟨htτ.le, hbt⟩ x)
    exact rmFrame_mem_of_rmC_mem hLC (G t) x (F t) (fun A hA R hR => hF.2.2.2.1 t A hA R hR)
      e he hmem.1

/-! ## The bootstrap

Given the one-shot extension `hshot` (with a *uniform* shot length `ε`), the usual supremum
argument gives the conclusion on `[0,β]` for every `β < T''`: let
`A := {β | 0 ≤ β ∧ β ≤ T'' ∧ CurvIn on [0,β]}`; `0 ∈ A`, and `hshot` extends any `β ∈ A` with
`β < T''` to `min (β+ε) T'' ∈ A`, so `sSup A = T''` and every `β < T''` lies in `A`. -/
theorem pinching_all
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {G : ℝ → SMet I M} {F : ℝ → Set (Curv4 (Module.finrank ℝ E))}
    {ε T'' : ℝ} (hε : 0 < ε) (hT''0 : 0 ≤ T'')
    (h0 : CurvIn (G 0) (F 0))
    (hshot : ∀ τ : ℝ, 0 ≤ τ → τ < T'' → (∀ t ∈ Set.Icc 0 τ, CurvIn (G t) (F t)) →
      ∀ t ∈ Set.Icc 0 (min (τ + ε) T''), CurvIn (G t) (F t)) :
    ∀ t ∈ Set.Ico 0 T'', CurvIn (G t) (F t) := by
  classical
  set A : Set ℝ := {β : ℝ | 0 ≤ β ∧ β ≤ T'' ∧ ∀ t ∈ Set.Icc 0 β, CurvIn (G t) (F t)} with hA
  have hA0 : (0 : ℝ) ∈ A := by
    refine ⟨le_rfl, hT''0, ?_⟩
    intro t ht
    rw [Set.mem_Icc] at ht
    have htz : t = 0 := le_antisymm ht.2 ht.1
    rw [htz]
    exact h0
  have hAne : A.Nonempty := ⟨0, hA0⟩
  have hAbdd : BddAbove A := ⟨T'', fun β hβ => hβ.2.1⟩
  have hβ₀le : sSup A ≤ T'' := csSup_le hAne (fun β hβ => hβ.2.1)
  have hkey : sSup A = T'' := by
    by_contra hne
    have hlt : sSup A < T'' := lt_of_le_of_ne hβ₀le hne
    have hδpos : 0 < min (T'' - sSup A) ε := lt_min (by linarith) hε
    obtain ⟨β, hβA, hβgt⟩ := exists_lt_of_lt_csSup hAne
      (show sSup A - min (T'' - sSup A) ε / 2 < sSup A by linarith)
    rcases lt_or_ge β T'' with hβlt | hβge
    · have hstep : min (β + ε) T'' ∈ A :=
        ⟨le_min (by linarith [hβA.1, hε]) hT''0, min_le_right _ _,
          hshot β hβA.1 hβlt hβA.2.2⟩
      have hle : min (β + ε) T'' ≤ sSup A := le_csSup hAbdd hstep
      have hgt : sSup A < min (β + ε) T'' := by
        refine lt_min ?_ hlt
        have h2 : min (T'' - sSup A) ε ≤ ε := min_le_right _ _
        linarith
      linarith
    · have hβT'' : β = T'' := le_antisymm hβA.2.1 hβge
      have : T'' ≤ sSup A := hβT'' ▸ le_csSup hAbdd hβA
      linarith
  intro t ht
  have htlt : t < sSup A := by rw [hkey]; exact ht.2
  obtain ⟨β, hβA, hβgt⟩ := exists_lt_of_lt_csSup hAne htlt
  exact hβA.2.2 t ⟨ht.1, le_of_lt hβgt⟩

/-! ## The push data of the growing truncation -/
theorem trunc_push_data (n : ℕ) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / (2 * Λ) ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (F : ℝ → Set (Curv4 n)), ODEInvariantFamily F → ∀ (a b : ℝ), b ≤ a + ε →
        (F a ∩ frobBall ϱ).Nonempty →
        (∀ t ∈ Set.Icc a b, (F t ∩ frobBall (truncRad ϱ Λ ε (t - a))).Nonempty) ∧
        (∀ t ∈ Set.Ico a b, ∀ h : ℝ, 0 < h → h ≤ b - t →
          ∀ S ∈ F t ∩ frobBall (truncRad ϱ Λ ε (t - a)),
            ∃ S' ∈ F (t + h) ∩ frobBall (truncRad ϱ Λ ε (t + h - a)),
              frobDist S' (S + h • Q S) ≤ C' * h ^ 2) := by
  obtain ⟨Λ, hΛ, ε, hε, hεΛ, C', hC', hgen⟩ := trunc_push_growing n ϱ hϱ
  refine ⟨Λ, hΛ, ε, hε, hεΛ, C', hC', ?_⟩
  have hconv : ∀ (F : ℝ → Set (Curv4 n)) (a t : ℝ), t - a ≤ ε →
      truncFam F ϱ Λ a t = F t ∩ frobBall (truncRad ϱ Λ ε (t - a)) := by
    intro F a t ht
    rw [truncFam_eq, truncRad_of_le ht]
  intro F hF a b hb hne
  have htr0 : truncRad ϱ Λ ε (a - a) = ϱ := by
    rw [truncRad_of_le (by linarith)]
    simp only [growRad, sub_self, mul_zero, sub_zero, div_one]
  have hne' : (truncFam F ϱ Λ a a).Nonempty := by
    obtain ⟨S, hS⟩ := hne
    refine ⟨S, ?_⟩
    have h1 : truncFam F ϱ Λ a a = F a ∩ frobBall (truncRad ϱ Λ ε (a - a)) := hconv F a a (by linarith)
    rw [h1, htr0]
    exact hS
  obtain ⟨hneEd, hpushEd⟩ := hgen F hF a hne'
  constructor
  · intro t ht
    rw [← hconv F a t (by linarith [ht.2, hb])]
    exact hneEd t ⟨ht.1, by linarith [ht.2, hb]⟩
  · intro t ht h hh hle S hS
    have hta : t < a + ε := lt_of_lt_of_le ht.2 hb
    have hS' : S ∈ truncFam F ϱ Λ a t := by
      rw [hconv F a t (by linarith [hta.le])]
      exact hS
    have hhe : h ≤ ε - (t - a) := by linarith
    obtain ⟨S', hS'1, hS'2⟩ := hpushEd t ⟨ht.1, hta⟩ h hh hhe S hS'
    have h2 : truncFam F ϱ Λ a (t + h) = F (t + h) ∩ frobBall (truncRad ϱ Λ ε (t + h - a)) :=
      hconv F a (t + h) (by linarith)
    exact ⟨S', by rw [← h2]; exact hS'1, hS'2⟩

/-- The `O(h)` Lipschitz form of the one-step push (the input shape of `sup_dist_regular`). -/
theorem trunc_push_data_two (n : ℕ) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / (2 * Λ) ∧ ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (F : ℝ → Set (Curv4 n)), ODEInvariantFamily F → ∀ (a b : ℝ), b ≤ a + ε →
        (F a ∩ frobBall ϱ).Nonempty →
        (∀ t ∈ Set.Icc a b, (F t ∩ frobBall (truncRad ϱ Λ ε (t - a))).Nonempty) ∧
        (∀ t ∈ Set.Ico a b, ∀ h : ℝ, 0 < h → h ≤ b - t →
          ∀ S ∈ F t ∩ frobBall (truncRad ϱ Λ ε (t - a)),
            ∃ S' ∈ F (t + h) ∩ frobBall (truncRad ϱ Λ ε (t + h - a)),
              frobDist S' (S + h • Q S) ≤ C' * h ^ 2 ∧
              frobDist S' S ≤ (C' * ε + (n : ℝ) ^ 2 * (5 * (n : ℝ) ^ 2 * (2 * ϱ) ^ 2)) * h) := by
  obtain ⟨Λ, hΛ, ε, hε, hεΛ, C', hC', hdata⟩ := trunc_push_data n ϱ hϱ
  refine ⟨Λ, hΛ, ε, hε, hεΛ, C', hC', ?_⟩
  intro F hF a b hb hne
  obtain ⟨hneD, hpushD⟩ := hdata F hF a b hb hne
  refine ⟨hneD, ?_⟩
  intro t ht h hh hle S hS
  obtain ⟨S', hS'1, hS'2⟩ := hpushD t ht h hh hle S hS
  refine ⟨S', hS'1, hS'2, ?_⟩
  have hSa : frobNorm S ≤ 2 * ϱ := by
    have h1 : frobNorm S ≤ truncRad ϱ Λ ε (t - a) := hS.2
    have h2 : truncRad ϱ Λ ε (t - a) ≤ truncRad ϱ Λ ε ε :=
      truncRad_mono hϱ hΛ hεΛ (by linarith [hb, ht.1])
    have h3 : truncRad ϱ Λ ε ε = growRad ϱ Λ ε := truncRad_self
    have h4 : growRad ϱ Λ ε ≤ 2 * ϱ := growRad_le_two' hϱ hΛ hεΛ
    linarith
  have hQ : frobNorm (Q S) ≤ (n : ℝ) ^ 2 * (5 * (n : ℝ) ^ 2 * (2 * ϱ) ^ 2) :=
    frobNorm_Q_le n ϱ hϱ.le hSa
  have hleε : h ≤ ε := by linarith [hle, hb, ht.1]
  have hsq : h ^ 2 ≤ ε * h := by nlinarith [hh, hleε]
  have h1 : frobDist S' S
      ≤ C' * h ^ 2 + h * ((n : ℝ) ^ 2 * (5 * (n : ℝ) ^ 2 * (2 * ϱ) ^ 2)) := by
    have h2 : frobDist S' S ≤ frobDist S' (S + h • Q S) + frobDist (S + h • Q S) S :=
      frobDist_triangle S' (S + h • Q S) S
    have h3 : frobDist (S + h • Q S) S = h * frobNorm (Q S) := by
      rw [frobDist, show S + h • Q S - S = h • Q S by abel, frobNorm_smul, abs_of_pos hh]
    rw [h3] at h2
    have h4 : h * frobNorm (Q S) ≤ h * ((n : ℝ) ^ 2 * (5 * (n : ℝ) ^ 2 * (2 * ϱ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hQ hh.le
    linarith [h2, hS'2, h4]
  calc frobDist S' S ≤ C' * h ^ 2 + h * ((n : ℝ) ^ 2 * (5 * (n : ℝ) ^ 2 * (2 * ϱ) ^ 2)) := h1
    _ ≤ C' * ε * h + h * ((n : ℝ) ^ 2 * (5 * (n : ℝ) ^ 2 * (2 * ϱ) ^ 2)) := by
        nlinarith [hC', hsq]
    _ = (C' * ε + (n : ℝ) ^ 2 * (5 * (n : ℝ) ^ 2 * (2 * ϱ) ^ 2)) * h := by ring


/-! ## The two ends of the assembly (proved)

The maximum-principle argument on the truncated family `F t ∩ frobBall ρ` is applied between these
two statements: the distance vanishes at the initial time, and a vanishing distance gives membership
in every orthonormal frame. -/

/-- At time `0` the truncated distance vanishes, as soon as every curvature value at time `0` lies in
the truncating ball. -/
theorem dist_zero_at_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {G : ℝ → SMet I M} {F : ℝ → Set (Curv4 (Module.finrank ℝ E))} {ρ : ℝ}
    (h0 : CurvIn (G 0) (F 0)) (hρ : ∀ x : M, rmC (G 0) x ∈ frobBall (n := Module.finrank ℝ E) ρ) :
    ∀ x : M, frobInfDist (rmC (G 0) x) (F 0 ∩ frobBall (n := Module.finrank ℝ E) ρ) = 0 :=
  fun x => frobInfDist_eq_zero_of_mem ⟨rmC_mem_of_curvIn h0 x, hρ x⟩

/-- If the truncated distance to `F t` vanishes everywhere, then the curvature of `G t` lies in `F t`
in *every* orthonormal frame (`O(n)`-invariance of the family). -/
theorem curvIn_of_dist_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {F : ℝ → Set (Curv4 (Module.finrank ℝ E))}
    (hF : IsInvariantFamily F) {ρ t : ℝ}
    (hKne : (F t ∩ frobBall (n := Module.finrank ℝ E) ρ).Nonempty)
    (h : ∀ x : M, frobInfDist (rmC (G t) x) (F t ∩ frobBall (n := Module.finrank ℝ E) ρ) = 0) :
    CurvIn (G t) (F t) := by
  intro x e he
  have hmem : rmC (G t) x ∈ F t ∩ frobBall (n := Module.finrank ℝ E) ρ :=
    mem_of_frobInfDist_eq_zero
      ((isClosed_fibre_of_isClosed_track hF.1 t).inter (isClosed_frobBall ρ)) hKne (h x)
  exact rmFrame_mem_of_rmC_mem hLC (G t) x (F t)
    (fun A hA R hR => hF.2.2.2.1 t A hA R hR) e he hmem.1

/-! ## The final assembly

`hamilton_mp` is the composition of
* the curvature bound `curv_frobNorm_bound` (the radius `ρ₁`),
* the truncation data `trunc_push_data_two` (the constants `Λ, ε, C'`, the non-emptiness of the
  truncated fibres and the one-step push in both its `O(h²)` and its `O(h)` form),
* the regularity provider `hsup` (lower semicontinuity and right upper semicontinuity of
  `t ↦ truncSup G F Υ`, provided by `sup_dist_regular`), and
* the model provider `hmodel` (provided by `trunc_model`),

through the one-shot lemma `pinching_shot` and the bootstrap `pinching_all`.

The two providers are kept as explicit hypotheses (rather than imported theorems) so that this file
does not have to import the heavy geometric modules while the assembly is being developed; the final
theorem instantiates them by `sup_dist_regular` and `trunc_model`.

Note: `trunc_model`'s curvature bound `hρ₁ : ∀ s ∈ Ico 0 T, …` is *global in the horizon* `T` of the
flow, which the assembly does not have (the flow is only bounded on compact subintervals of `[0,T)`);
the assembly therefore applies it with the *shrunken* horizon `T'' = (t+T)/2 < T`, for which the
bound is available from `curv_frobNorm_bound`, and only uses the model on the window
`Ioo τ (τ + ε)` with `τ + ε ≤ T''`. -/
theorem hamilton_mp_of_providers
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLP : LapRmFrameParallel I M)
    (hsup : ∀ {G : ℝ → SMet I M} {T : ℝ}, IsRicciFlow G T →
      ∀ {F : ℝ → Set (Curv4 (Module.finrank ℝ E))}, IsInvariantFamily F →
      ∀ {Υ : ℝ → ℝ}, Continuous Υ → ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      (∀ t ∈ Set.Icc a b, (F t ∩ frobBall (Υ t)).Nonempty) →
      (∀ t ∈ Set.Ico a b, ∃ δ > 0, ∃ C' : ℝ, ∀ h : ℝ, 0 < h → h ≤ δ →
        ∀ S ∈ F t ∩ frobBall (Υ t),
          ∃ S' ∈ F (t + h) ∩ frobBall (Υ (t + h)),
            frobDist S' (S + h • Q S) ≤ C' * h ^ 2 ∧
            frobDist S' S ≤ C' * h) →
      (∀ t ∈ Set.Icc a b, ∀ ε' > 0, ∃ δ > 0, ∀ s ∈ Set.Icc a b, |s - t| ≤ δ →
        truncSup G F Υ t ≤ truncSup G F Υ s + ε') ∧
      (∀ t ∈ Set.Ico a b, ∀ ε' > 0, ∃ δ > 0, ∀ h : ℝ, 0 < h → h ≤ δ → t + h ≤ b →
        truncSup G F Υ (t + h) ≤ truncSup G F Υ t + ε'))
    (hmodel : ∀ {G : ℝ → SMet I M} {T : ℝ}, IsRicciFlow G T →
      ∀ {F : ℝ → Set (Curv4 (Module.finrank ℝ E))}, IsInvariantFamily F →
      ∀ {ρ₁ ϱ Λ ε τ C : ℝ},
      (∀ s ∈ Set.Ico 0 T, ∀ x : M, frobNorm (rmC (G s) x) ≤ ρ₁) →
      0 < ϱ → ρ₁ + 1 ≤ ϱ → 0 < Λ → 0 < ε → ε ≤ 1 / (2 * Λ) →
      0 ≤ τ → τ < T → τ + ε ≤ T → 0 ≤ C →
      (∀ R S : Curv4 (Module.finrank ℝ E), frobNorm R ≤ 2 * ϱ → frobNorm S ≤ 2 * ϱ →
        frobDist (Q R) (Q S) ≤ C * frobDist R S) →
      ∀ t ∈ Set.Ioo τ (τ + ε), ∀ x : M,
        ∃ (δ : ℝ) (_ : 0 < δ) (U : Set M) (_ : U ∈ nhds x)
          (Rl dRl : ℝ → M → Curv4 (Module.finrank ℝ E)),
          (∀ s ∈ Set.Icc t (t + δ), ∀ y ∈ U,
            truncDist G F (fun u => growRad ϱ Λ (u - τ)) s y
              = frobInfDist (Rl s y) (truncFam F ϱ Λ τ s)) ∧
          ContinuousOn (fun p : ℝ × M => (Rl p.1 p.2, dRl p.1 p.2))
            (Set.prod (Set.Icc t (t + δ)) U) ∧
          (∀ ε' > 0, ∃ δ' > 0, ∀ h : ℝ, 0 < h → h ≤ δ' → ∀ y ∈ U,
            frobDist (Rl (t + h) y) (Rl t y + h • (dRl t y + Q (Rl t y))) ≤ ε' * h) ∧
          (∀ ℓ : Curv4 (Module.finrank ℝ E), frobNorm ℓ ≤ 1 →
            (∀ z ∈ U, frobDot ℓ (Rl t z) ≤ frobDot ℓ (Rl t x)) → frobDot ℓ (dRl t x) ≤ 0) ∧
          (∀ y ∈ U, ∀ S ∈ F t ∩ frobBall (growRad ϱ Λ (t - τ)),
            frobDist (Q (Rl t y)) (Q S) ≤ C * frobDist (Rl t y) S)) :
    PinchingPreserved I M := by
  intro F hF G T hflow h0 t ht
  by_cases hM : Nonempty M
  · haveI : Nonempty M := hM
    -- the horizon
    set T'' : ℝ := (t + T) / 2 with hT''
    have hT''0 : 0 ≤ T'' := by rw [hT'']; linarith [ht.1, ht.2]
    have hT''T : T'' < T := by rw [hT'']; linarith [ht.2]
    have htT'' : t < T'' := by rw [hT'']; linarith [ht.2]
    -- the constants
    obtain ⟨ρ₁, hρ₁pos, hρ₁bd⟩ := curv_frobNorm_bound G T T'' hflow hT''T
    have hsub'' : Set.Ico 0 T'' ⊆ Set.Ico 0 T := fun s hs => ⟨hs.1, lt_of_lt_of_le hs.2 hT''T.le⟩
    have hflow'' : IsRicciFlow G T'' :=
      ⟨hflow.1.mono (Set.prod_mono hsub'' Subset.rfl),
        fun s hs x u v => (hflow.2 s (hsub'' hs) x u v).mono hsub''⟩
    have hρ'' : ∀ s ∈ Set.Ico 0 T'', ∀ x : M, frobNorm (rmC (G s) x) ≤ ρ₁ :=
      fun s hs x => hρ₁bd s ⟨hs.1, hs.2.le⟩ x
    set ϱ : ℝ := ρ₁ + 1 with hϱdef
    have hϱ : 0 < ϱ := by rw [hϱdef]; linarith
    have hρϱ : ρ₁ + 1 ≤ ϱ := le_of_eq hϱdef.symm
    obtain ⟨Λ, hΛ, ε, hε, hεΛ, C', hC', hpushdata⟩ :=
      trunc_push_data_two (Module.finrank ℝ E) ϱ hϱ
    set C : ℝ := 5 * ((Module.finrank ℝ E : ℕ) : ℝ) ^ 4 * (2 * (2 * ϱ)) with hCdef
    have hC : 0 ≤ C := by rw [hCdef]; positivity
    have hQlip : ∀ R S : Curv4 (Module.finrank ℝ E), frobNorm R ≤ 2 * ϱ → frobNorm S ≤ 2 * ϱ →
        frobDist (Q R) (Q S) ≤ C * frobDist R S := by
      intro R S hR hS
      rw [hCdef]
      exact Q_lipschitz_ball _ _ (by linarith) R S hR hS
    -- the one-shot extension
    have hshot : ∀ τ : ℝ, 0 ≤ τ → τ < T'' → (∀ s ∈ Set.Icc 0 τ, CurvIn (G s) (F s)) →
        ∀ s ∈ Set.Icc 0 (min (τ + ε) T''), CurvIn (G s) (F s) := by
      intro τ hτ0 hτT'' hP
      set b : ℝ := min (τ + ε) T'' with hb
      have hbT : b ≤ T'' := by rw [hb]; exact min_le_right _ _
      have hbTfull : b < T := lt_of_le_of_lt hbT hT''T
      have hbτε : b ≤ τ + ε := by rw [hb]; exact min_le_left _ _
      have hab : τ ≤ b := by rw [hb]; exact le_min (by linarith) hτT''.le
      -- non-emptiness at the base time
      have hne0 : (F τ ∩ frobBall ϱ).Nonempty := by
        obtain ⟨x₀⟩ := hM
        refine ⟨rmC (G τ) x₀, ?_, ?_⟩
        · exact hP τ ⟨hτ0, le_rfl⟩ x₀ (onFrame (G τ) x₀)
            (Work.Diff.GE.isONFrame_onFrame (G τ) x₀)
        · exact le_trans (hρ₁bd τ ⟨hτ0, hτT''.le⟩ x₀) (by rw [hϱdef]; linarith)
      obtain ⟨hneEd, hpushEd⟩ := hpushdata F hF.2.2.2.2 τ b hbτε hne0
      -- the regularity of the truncated supremum
      have hΥ : Continuous (fun u : ℝ => truncRad ϱ Λ ε (u - τ)) :=
        (continuous_truncRad ϱ Λ ε hΛ hεΛ).comp (continuous_id.sub continuous_const)
      set n2 : ℝ := ((Module.finrank ℝ E : ℕ) : ℝ) ^ 2 *
        (5 * ((Module.finrank ℝ E : ℕ) : ℝ) ^ 2 * (2 * ϱ) ^ 2) with hn2def
      have hn2 : 0 ≤ n2 := by rw [hn2def]; positivity
      set Cab : ℝ := C' + (C' * ε + n2) with hCabdef
      have hC'le : C' ≤ Cab := by rw [hCabdef]; linarith [mul_nonneg hC' hε.le, hn2]
      have hC2le : C' * ε + n2 ≤ Cab := by rw [hCabdef]; linarith [hC']
      have hreg := hsup hflow hF hΥ hτ0 hab hbTfull
        (fun s hs => hneEd s hs)
        (fun s hs => by
          refine ⟨b - s, by linarith [hs.2], Cab, ?_⟩
          intro h hh hle S hS
          obtain ⟨S', hS'1, hS'2, hS'3⟩ := hpushEd s hs h hh hle S hS
          refine ⟨S', hS'1, ?_, ?_⟩
          · exact le_trans hS'2 (mul_le_mul_of_nonneg_right hC'le (sq_nonneg h))
          · exact le_trans hS'3 (mul_le_mul_of_nonneg_right hC2le hh.le))
      -- the local model
      set ε' : ℝ := b - τ with hε'def
      have hτb : τ < b := by rw [hb]; exact lt_min (by linarith) hτT''
      have hε'pos : 0 < ε' := by rw [hε'def]; linarith [hτb]
      have hε'ε : ε' ≤ ε := by rw [hε'def]; linarith [hbτε]
      have hε'Λ : ε' ≤ 1 / (2 * Λ) := le_trans hε'ε hεΛ
      have hτε' : τ + ε' = b := by rw [hε'def]; ring
      have hmodel' : ∀ s ∈ Set.Ioo τ b, ∀ x : M,
          ∃ (δ : ℝ) (_ : 0 < δ) (U : Set M) (_ : U ∈ nhds x)
            (Rl dRl : ℝ → M → Curv4 (Module.finrank ℝ E)),
            (∀ s' ∈ Set.Icc s (s + δ), ∀ y ∈ U,
              truncDist G F (fun u => truncRad ϱ Λ ε (u - τ)) s' y
                = frobInfDist (Rl s' y) (F s' ∩ frobBall (truncRad ϱ Λ ε (s' - τ)))) ∧
            ContinuousOn (fun p : ℝ × M => (Rl p.1 p.2, dRl p.1 p.2))
              (Set.prod (Set.Icc s (s + δ)) U) ∧
            (∀ ε'' > 0, ∃ δ' > 0, ∀ h : ℝ, 0 < h → h ≤ δ' → ∀ y ∈ U,
              frobDist (Rl (s + h) y) (Rl s y + h • (dRl s y + Q (Rl s y))) ≤ ε'' * h) ∧
            (∀ ℓ : Curv4 (Module.finrank ℝ E), frobNorm ℓ ≤ 1 →
              (∀ z ∈ U, frobDot ℓ (Rl s z) ≤ frobDot ℓ (Rl s x)) → frobDot ℓ (dRl s x) ≤ 0) ∧
            (∀ y ∈ U, ∀ S ∈ F s ∩ frobBall (truncRad ϱ Λ ε (s - τ)),
              frobDist (Q (Rl s y)) (Q S) ≤ C * frobDist (Rl s y) S) := by
        intro s hs x
        have hsε' : s - τ < ε' := by rw [hε'def]; linarith [hs.2]
        have hsε : s - τ < ε := lt_of_lt_of_le hsε' hε'ε
        obtain ⟨δ, hδ, U, hU, Rl, dRl, h1, h2, h3, h4, h5⟩ :=
          hmodel hflow'' hF hρ'' hϱ hρϱ hΛ hε'pos hε'Λ hτ0
            hτT''
            (by rw [hτε']; exact hbT)
            hC hQlip s ⟨hs.1, by rw [hε'def]; linarith [hs.2]⟩ x
        set δ' : ℝ := min δ (b - s) with hδ'def
        have hδ'pos : 0 < δ' := lt_min hδ (by linarith [hs.2])
        have hδ'δ : δ' ≤ δ := min_le_left _ _
        have hδ'b : δ' ≤ b - s := min_le_right _ _
        have hsub : ∀ s' ∈ Set.Icc s (s + δ'),
            s' ∈ Set.Icc s (s + δ) ∧ s' - τ ≤ ε := by
          intro s' hs'
          refine ⟨⟨hs'.1, by linarith [hs'.2, hδ'δ]⟩, ?_⟩
          have h6 : s' ≤ b := by linarith [hs'.2, hδ'b]
          linarith [hbτε]
        refine ⟨δ', hδ'pos, U, hU, Rl, dRl, ?_, ?_, ?_, h4, ?_⟩
        · intro s' hs' y hy
          obtain ⟨hs'', h7⟩ := hsub s' hs'
          have h9 : truncDist G F (fun u => truncRad ϱ Λ ε (u - τ)) s' y
              = truncDist G F (fun u => growRad ϱ Λ (u - τ)) s' y := by
            simp only [truncDist, truncRad_of_le h7]
          rw [h9, h1 s' hs'' y hy]
          simp only [truncFam_eq, truncRad_of_le h7]
        · exact h2.mono (Set.prod_mono (fun s' hs' => (hsub s' hs').1) (Subset.refl _))
        · intro ε'' hε''
          obtain ⟨δ'', hδ'', hδ''exp⟩ := h3 ε'' hε''
          exact ⟨δ'', hδ'', hδ''exp⟩
        · intro y hy S hS
          have h6 : truncRad ϱ Λ ε (s - τ) = growRad ϱ Λ (s - τ) := truncRad_of_le hsε.le
          rw [h6] at hS
          exact h5 y hy S hS
      -- the shot
      exact pinching_shot hLC hLP hflow hF
        (fun x => hρ₁bd τ ⟨hτ0, hτT''.le⟩ x)
        hρϱ hϱ hΛ hε hεΛ hC hC' hQlip hτ0 hτT''
        hT''T
        hP
        (fun s hs h hh hle S hS => by
          have hs' : s ∈ Set.Ico τ b := by
            refine ⟨hs.1, ?_⟩
            have h1 : 0 < min (τ + ε) T'' - s := lt_of_lt_of_le hh hle
            have h2 : b = min (τ + ε) T'' := hb
            linarith
          obtain ⟨S', hS'1, hS'2, -⟩ :=
            hpushEd s hs' h hh (by linarith [hb, hle]) S hS
          exact ⟨S', hS'1, hS'2⟩)
        (fun s hs => hneEd s hs)
        (fun s hs => hreg.1 s hs)
        (fun s hs => hreg.2 s hs)
        hmodel'
    exact pinching_all hε hT''0 h0 hshot t ⟨ht.1, htT''⟩
  · exact fun x => (hM ⟨x⟩).elim

/-! ## The target theorem

The statement (unchanged, as requested).  The proof is the assembly described in `NOTES.md`:
Chow–Lu's time-dependent maximum principle (`Submission.Work.Diff.MP.max_principle`) applied to the
truncated family `F t ∩ frobBall ρ` with `d t x = frobInfDist (rmC (G t) x) (F t ∩ frobBall ρ)`. -/
theorem hamilton_mp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M) (hCE : CurvEvolution I M)
    (hLP : LapRmFrameParallel I M) :
    PinchingPreserved I M :=
  hamilton_mp_of_providers hLC hLP
    (fun {G T} hflow {F} hF {Υ} hΥ {a b} ha hab hbT hKne hpush =>
      sup_dist_regular hLC hLP hflow hF hΥ ha hab hbT hKne hpush)
    (fun {G T} hflow {F} hF {ρ₁ ϱ Λ ε τ C} hρ hϱ hρϱ hΛ hε hεΛ hτ0 hτT hεT hC hQlip =>
      fun t ht x => by
        obtain ⟨δ, hδ, hδT, U, hU, Rl, dRl, h1, h2, h3, h4, h5⟩ :=
          trunc_model hLC hCE hLP hflow hF hρ hϱ hρϱ hΛ hε hεΛ hτ0 hτT hεT hC hQlip t ht x
        exact ⟨δ, hδ, U, hU, Rl, dRl, h1, h2, h3, h4, h5⟩)

end Work.Diff.MP
