import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.cInfKnot

/-!
# The easy clauses of the glued sweep family

`Work.Drive.sweepGlue F G s t = F t (gluePsi (2s))` for `s ≤ 1/2` and
`= G t (gluePsi (2s-1))` for `s ≥ 1/2`, an "eased" concatenation of two one-parameter families of
knots joining at the common slice `F · 1 = G · 0`.

Here we record the *elementary* consequences of the definition which need only the basic facts
about the easing function `gluePsi s = s²(3-2s)` (namely `gluePsi 0 = 0`, `gluePsi 1 = 1` and
`gluePsi '' [0,1] ⊆ [0,1]`): the resulting family is `period`-periodic in `t` whenever `F, G` are,
every slice over `s ∈ [0,1]` is a `C^∞` knot whenever all slices of `F` and `G` are, and the two
end slices recover `F · 0` and `G · 1`.  (The only non-elementary clause of
`Work.Drive.sweepGlue_clauses` is the joint `C¹`-smoothness in `(s,t)`, which is what the easing
`gluePsi` is for.)
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

private lemma gluePsi_zero : gluePsi 0 = 0 := by norm_num [gluePsi]

private lemma gluePsi_one : gluePsi 1 = 1 := by norm_num [gluePsi]

private lemma gluePsi_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    gluePsi s ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hs0, hs1⟩ := hs
  constructor
  · simp only [gluePsi]
    nlinarith [sq_nonneg s]
  · simp only [gluePsi]
    nlinarith [mul_nonneg (sq_nonneg (1 - s)) (by linarith : (0 : ℝ) ≤ 1 + 2 * s)]

theorem sweepGlue_easy_clauses {F G : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hjun : ∀ t : ℝ, F t 1 = G t 0)
    (hFsl : ∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => F t s))
    (hGsl : ∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => G t s))
    (hFper : ∀ s t : ℝ, F (t + LeanEval.KnotTheory.Quadrisecant.period) s = F t s)
    (hGper : ∀ s t : ℝ, G (t + LeanEval.KnotTheory.Quadrisecant.period) s = G t s) :
    (∀ s t : ℝ, Work.Drive.sweepGlue F G s (t + LeanEval.KnotTheory.Quadrisecant.period)
      = Work.Drive.sweepGlue F G s t) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, Work.Drive.IsCInfKnot (fun t : ℝ => Work.Drive.sweepGlue F G s t)) ∧
    (∀ t : ℝ, Work.Drive.sweepGlue F G 0 t = F t 0) ∧
    (∀ t : ℝ, Work.Drive.sweepGlue F G 1 t = G t 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t
    unfold sweepGlue
    by_cases h : s ≤ 1 / 2
    · rw [if_pos h, if_pos h, hFper]
    · rw [if_neg h, if_neg h, hGper]
  · intro s hs
    by_cases h : s ≤ 1 / 2
    · have hc : gluePsi (2 * s) ∈ Set.Icc (0 : ℝ) 1 :=
        gluePsi_mem_Icc ⟨by linarith [hs.1], by linarith [h]⟩
      have hfun : (fun t : ℝ => sweepGlue F G s t) = fun t : ℝ => F t (gluePsi (2 * s)) := by
        funext t
        unfold sweepGlue
        rw [if_pos h]
      rw [hfun]
      exact hFsl (gluePsi (2 * s)) hc
    · have hc : gluePsi (2 * s - 1) ∈ Set.Icc (0 : ℝ) 1 :=
        gluePsi_mem_Icc ⟨by linarith [h], by linarith [hs.2]⟩
      have hfun : (fun t : ℝ => sweepGlue F G s t)
          = fun t : ℝ => G t (gluePsi (2 * s - 1)) := by
        funext t
        unfold sweepGlue
        rw [if_neg h]
      rw [hfun]
      exact hGsl (gluePsi (2 * s - 1)) hc
  · intro t
    unfold sweepGlue
    rw [if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num [gluePsi]
  · intro t
    unfold sweepGlue
    rw [if_neg (by norm_num : ¬ ((1 : ℝ) ≤ 1 / 2))]
    norm_num [gluePsi]

end Work.Drive
