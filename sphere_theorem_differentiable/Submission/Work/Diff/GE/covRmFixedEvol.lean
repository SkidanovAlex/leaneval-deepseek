import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.GE.covRmFixedEvolDefs
import Submission.Work.Diff.GE.covRm_norm_bound
import Submission.Work.Diff.GE.frame_evol_of_fixed
import Submission.Work.Diff.GE.reaction_map_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Assembly: the fixed-vector evolution of `∇Rm`, interior plus boundary
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- Arithmetic: multiplying a nonnegative product by `max C₁ C₂` dominates multiplying by `C₁`. -/
theorem const_mul_le_max_mul (C₁ C₂ a b P : ℝ) (h : 0 ≤ a * b * P) :
    C₁ * a * b * P ≤ max C₁ C₂ * a * b * P := by
  have hm := mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) h
  calc C₁ * a * b * P = C₁ * (a * b * P) := by ring
    _ ≤ max C₁ C₂ * (a * b * P) := hm
    _ = max C₁ C₂ * a * b * P := by ring

/-- Arithmetic: the same for the second constant. -/
theorem const_mul_le_max_mul' (C₁ C₂ a b P : ℝ) (h : 0 ≤ a * b * P) :
    C₂ * a * b * P ≤ max C₁ C₂ * a * b * P := by
  have hm := mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) h
  calc C₂ * a * b * P = C₂ * (a * b * P) := by ring
    _ ≤ max C₁ C₂ * (a * b * P) := hm
    _ = max C₁ C₂ * a * b * P := by ring

/-- **The fixed-vector evolution of `∇Rm`**, interior plus boundary, from the two endpoint
statements. -/
theorem covRm_fixed_evol_abs
    (F : Curv4 (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E))
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hInt : ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ioo 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x,
      HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d)
        (covRmTimeDeriv F G t x v a b c d) (Set.Ico 0 T) t ∧
      |covRmTimeDeriv F G t x v a b c d - lapCovRmAt (G t) x v a b c d|
        ≤ C₁ * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)))
    (hZero : ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
      HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d) D (Set.Ico 0 T) 0 ∧
      |D - lapCovRmAt (G 0) x v a b c d|
        ≤ C₂ * Real.sqrt (rmNormSq (G 0) x) * Real.sqrt (dRmNormSq (G 0) x)
            * (Real.sqrt ((G 0).inner x v v) * Real.sqrt ((G 0).inner x a a)
              * Real.sqrt ((G 0).inner x b b) * Real.sqrt ((G 0).inner x c c)
              * Real.sqrt ((G 0).inner x d d))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
      HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d) D (Set.Ico 0 T) t ∧
      |D - lapCovRmAt (G t) x v a b c d|
        ≤ C * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)) := by
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, ?_⟩
  intro G T hGF t ht x v a b c d
  have hX : 0 ≤ Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)
      * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
        * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
        * Real.sqrt ((G t).inner x d d)) := by positivity
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    obtain ⟨D, hD, hb⟩ := hZero G T hGF x v a b c d
    exact ⟨D, hD, le_trans hb (const_mul_le_max_mul' C₁ C₂ _ _ _ hX)⟩
  · obtain ⟨hD, hb⟩ := hInt G T hGF t ⟨hpos, ht.2⟩ x v a b c d
    exact ⟨covRmTimeDeriv F G t x v a b c d, hD, le_trans hb (const_mul_le_max_mul C₁ C₂ _ _ _ hX)⟩

/-- **The final assembly**: the absolute-value moving-frame estimate for `∇Rm`, from the two
endpoint statements of the fixed-vector evolution.  The target statement
`Work.Diff.GE.covRm_frame_evol_abs` is this lemma applied to
`Work.Diff.GE.covRm_fixed_evol_interior_final` (interior) and
`Work.Diff.GE.covRm_fixed_evol_zero` (endpoint, itself fed with
`Work.Diff.GE.covRm_fixed_evol_cont`). -/
theorem covRm_frame_evol_abs_of_pieces
    (hLC : LCSmooth I M) (hLV : LCVariation I M)
    (hInt : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (G : ℝ → SMet I M) (T : ℝ),
      IsRicciFlow G T → ∀ t ∈ Set.Ioo 0 T, ∀ x : M,
      ∀ v a b c d : TangentSpace I x,
      HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d)
        (Work.Diff.GE.covRmTimeDeriv Work.Diff.GE.reactionMap G t x v a b c d) (Set.Ico 0 T) t ∧
      |Work.Diff.GE.covRmTimeDeriv Work.Diff.GE.reactionMap G t x v a b c d
          - Work.Diff.GE.lapCovRmAt (G t) x v a b c d|
        ≤ C₁ * Real.sqrt (rmNormSq (G t) x)
            * Real.sqrt (dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
              * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
              * Real.sqrt ((G t).inner x d d)))
    (hZero : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (G : ℝ → SMet I M) (T : ℝ),
      IsRicciFlow G T → ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
      HasDerivWithinAt (fun s ↦ covRm (G s) x v a b c d) D (Set.Ico 0 T) 0 ∧
      |D - Work.Diff.GE.lapCovRmAt (G 0) x v a b c d|
        ≤ C₂ * Real.sqrt (rmNormSq (G 0) x)
            * Real.sqrt (dRmNormSq (G 0) x)
            * (Real.sqrt ((G 0).inner x v v) * Real.sqrt ((G 0).inner x a a)
              * Real.sqrt ((G 0).inner x b b) * Real.sqrt ((G 0).inner x c c)
              * Real.sqrt ((G 0).inner x d d))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ),
      IsRicciFlow G T → ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      ∀ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
        (edot : Fin (Module.finrank ℝ E) → TangentSpace I x) (K : ℝ), 0 ≤ K →
      (∀ᶠ s in nhdsWithin t (Set.Ico 0 T), IsONFrame (G s) x (e s)) →
      (∀ i, HasDerivWithinAt (fun s ↦ e s i) (edot i) (Set.Ico 0 T) t) →
      (∀ i, (G t).inner x (edot i) (edot i) ≤ K * rmNormSq (G t) x) →
      ∀ m i j k l : Fin (Module.finrank ℝ E), ∃ D : ℝ,
        HasDerivWithinAt
          (fun s ↦ covRm (G s) x (e s m) (e s i) (e s j) (e s k) (e s l)) D
          (Set.Ico 0 T) t ∧
        |D - Work.Diff.GE.lapCovRmAt (G t) x (e t m) (e t i) (e t j) (e t k) (e t l)|
          ≤ C * (1 + K) * Real.sqrt (rmNormSq (G t) x)
              * Real.sqrt (dRmNormSq (G t) x) := by
  obtain ⟨C₁, hC₁, hInt'⟩ := hInt
  obtain ⟨C₂, hC₂, hZero'⟩ := hZero
  obtain ⟨C₀, hC₀, hfix⟩ := covRm_fixed_evol_abs
    (Work.Diff.GE.reactionMap : Curv4 (Module.finrank ℝ E) →
      Curv4 (Module.finrank ℝ E)) C₁ C₂ hC₁ hC₂ hInt' hZero'
  exact frame_evol_of_fixed hLC hLV C₀ hC₀ hfix (covRm_norm_bound hLC)

end Work.Diff.GE
