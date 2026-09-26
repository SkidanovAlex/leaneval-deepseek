import Mathlib
import Submission.Work.Drive.Mono.CutTransverse

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set

/-- **Compactness in one real variable.**  If a continuous nonnegative function `f` on a compact
set `B` vanishes nowhere outside a set `A`, then on the part of `B` that stays at distance at least
`ρ > 0` from `A` the function `f` is bounded below by a positive constant.

(The set of parameters at distance at least `ρ` from `A` is closed, since it is the intersection,
over the arbitrary index set `A`, of the closed sets `{t | ρ ≤ |t - t'|}`.) -/
theorem exists_pos_le_of_far_from {B A : Set ℝ} {f : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hB : IsCompact B) (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    (hkey : ∀ t ∈ B, f t = 0 → t ∈ A) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ B, (∀ t' ∈ A, ρ ≤ |t - t'|) → m ≤ f t := by
  have hclosed : IsClosed {t : ℝ | t ∈ B ∧ ∀ t' ∈ A, ρ ≤ |t - t'|} := by
    have heq : {t : ℝ | t ∈ B ∧ ∀ t' ∈ A, ρ ≤ |t - t'|}
        = B ∩ ⋂ (t' : ℝ) (_ : t' ∈ A), {t : ℝ | ρ ≤ |t - t'|} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [heq]
    exact hB.isClosed.inter
      (isClosed_iInter fun t' => isClosed_iInter fun _ =>
        isClosed_le continuous_const (continuous_abs.comp (continuous_id.sub continuous_const)))
  by_cases hne : {t : ℝ | t ∈ B ∧ ∀ t' ∈ A, ρ ≤ |t - t'|}.Nonempty
  · obtain ⟨t₀, ht₀, hmin⟩ :=
      (hB.of_isClosed_subset hclosed (fun t ht => ht.1)).exists_isMinOn hne hf.continuousOn
    refine ⟨f t₀, ?_, fun t ht hfar => hmin ⟨ht, hfar⟩⟩
    rcases eq_or_lt_of_le (hf0 t₀) with h | h
    · exfalso
      have hA : t₀ ∈ A := hkey t₀ ht₀.1 h.symm
      have hd := ht₀.2 t₀ hA
      rw [sub_self, abs_zero] at hd
      linarith
    · exact h
  · -- the admissible set is empty and the conclusion is vacuous
    exact ⟨1, one_pos, fun t ht hfar => absurd ⟨t, ht, hfar⟩ hne⟩

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set in
open scoped ENNReal Topology in
/-- Parameters of one period at which the knot is in the closed box and at distance at least `ρ` from every flat crossing of the level inside the closed box have flat value bounded away from the level (compactness; the separating set is closed in `[0, 2π]`). -/
theorem exists_margin_off_flatCrossings (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) {s u ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ m : ℝ, 0 < m ∧ ∀ t : ℝ, t ∈ Set.Icc 0 (2 * Real.pi) →
      K.curve t ∈ closure (Submission.PBox s c σ) →
      (∀ t' : ℝ, t' ∈ Set.Icc 0 (2 * Real.pi) →
        K.curve t' ∈ closure (Submission.PBox s c σ) →
        (K.curve t') (σ 2) = c (σ 2) + u → ρ ≤ |t - t'|) →
      m ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)| := by
  -- the curve and its `σ 2`-coordinate are continuous; the deviation from the level is continuous
  have hcont : Continuous K.curve := K.smooth.continuous
  have hcoord : Continuous fun t : ℝ => (K.curve t) (σ 2) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).comp hcont
  have hfcont : Continuous fun t : ℝ => |(K.curve t) (σ 2) - (c (σ 2) + u)| :=
    continuous_abs.comp (hcoord.sub continuous_const)
  -- the parameters inside the closed box during one period form a compact set
  have hBcomp : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi) ∩
      {t : ℝ | K.curve t ∈ closure (Submission.PBox s c σ)}) :=
    isCompact_Icc.inter_right (isClosed_closure.preimage hcont)
  obtain ⟨m, hm0, hm⟩ := exists_pos_le_of_far_from
    (B := Set.Icc (0 : ℝ) (2 * Real.pi) ∩
      {t : ℝ | K.curve t ∈ closure (Submission.PBox s c σ)})
    (A := (Set.Icc (0 : ℝ) (2 * Real.pi) ∩
        {t : ℝ | K.curve t ∈ closure (Submission.PBox s c σ)})
      ∩ {t : ℝ | (K.curve t) (σ 2) = c (σ 2) + u})
    (f := fun t : ℝ => |(K.curve t) (σ 2) - (c (σ 2) + u)|)
    hρ hBcomp hfcont (fun t => abs_nonneg _) (by
      -- a parameter of the closed box where the deviation vanishes is a flat crossing
      rintro t ⟨ht, htbox⟩ hzero
      exact ⟨⟨ht, htbox⟩, sub_eq_zero.mp (abs_eq_zero.mp hzero)⟩)
  refine ⟨m, hm0, fun t ht htbox hfar => hm t ⟨ht, htbox⟩ ?_⟩
  rintro t' ⟨⟨ht'Icc, ht'box⟩, ht'lev⟩
  exact hfar t' ht'Icc ht'box ht'lev

end Work.Drive.Mono
