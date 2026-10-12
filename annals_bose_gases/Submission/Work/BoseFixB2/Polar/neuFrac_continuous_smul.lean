import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixB2.Polar.additive_bddAbove_continuous
import Submission.Work.BoseFixB2.Polar.neuFracDefect_bddAbove
import Submission.Work.BoseFixB2.Polar.neuFracDefect_midpoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Polar.neuFrac_continuous_smul` — `t ↦ neuFrac(t·f + g)` is continuous

For ℓ > 0, a² > 0, ℓu the centre of the moving box `Λ(u) = lamBox ℓ u`, and **smooth**
`f, g : ℝ³ → ℝ`, the map

`t ↦ Q(t·f + g)`,   `Q(φ) = neuFrac ℓ a² u φ`,

is continuous.

## The argument

Write `R(t) := neuFracDefect ℓ a² u f g t = Q(t·f + g) − t²·Q(f) − Q(g)`
(`Work.BoseFixB2.Polar.neuFracSmulAddDef`).  Then

`Q(t·f + g) = R(t) + t²·Q(f) + Q(g)`

is continuous as soon as `R` is, and `R` is handled by two facts proved in sibling modules:

* **`R` is additive**: squaring the parallelogram law
  `Work.BoseFixB2.Polar.neuFrac_parallelogram` (`Q` is a quadratic form in `φ`) with the
  `2`-homogeneity `Work.BoseKinLoc.NeuFrac.neuFrac_const_mul` gives the *midpoint* identity
  `R(s+t) + R(s−t) = 2R(s)` (`Work.BoseFixB2.Polar.neuFracDefect_midpoint`); together with
  `R(0) = 0` that identity forces additivity:
  `R(s+t) = 2R((s+t)/2) = R(s) + R(t)`.
* **`R` is bounded above near `0`**: `Q(φ) ≤ ∫_Λ φ²` (the Dirichlet trial `g = 0`), so on
  `|t| ≤ 1` the defect is bounded by the `t`-independent constant `∫_Λ(|f|+|g|)² + |Q(f)| + |Q(g)|`
  (`Work.BoseFixB2.Polar.neuFracDefect_bddAbove`).

Finally, an additive `R : ℝ → ℝ` that is bounded above on a neighbourhood of `0` is continuous
(`Work.BoseFixB2.Polar.additive_bddAbove_continuous`): additivity makes the one-sided bound
two-sided on a symmetric neighbourhood, so `R` is bounded near `0` and hence continuous.

The smoothness of `f` and `g` is used twice: it makes every state `t·f + g` continuous (so
every integral appearing in the trial functional is an honest Bochner integral, and the trial
set is bounded below), and it is needed for the parallelogram law
`Work.BoseFixB2.Polar.neuFrac_parallelogram`.
-/

noncomputable section

namespace Work.BoseFixB2.Polar

set_option autoImplicit false

/-- The quadratic defect of `neuFrac` at `t = 0` vanishes: `Q(g) − 0·Q(f) − Q(g) = 0`. -/
lemma neuFracDefect_zero {ℓ a2 : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    (f g : EuclideanSpace ℝ (Fin 3) → ℝ) : neuFracDefect ℓ a2 u f g 0 = 0 := by
  have hsg : smulAdd 0 f g = g := by
    funext z
    simp [smulAdd]
  simp only [neuFracDefect, hsg]
  ring

/-- `Q(t·f + g)` rewritten through the quadratic defect. -/
lemma neuFrac_smulAdd_eq_defect {ℓ a2 : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    (f g : EuclideanSpace ℝ (Fin 3) → ℝ) (t : ℝ) :
    Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => t * f z + g z)
      = neuFracDefect ℓ a2 u f g t + t ^ 2 * Work.BoseKinLoc.neuFrac ℓ a2 u f
        + Work.BoseKinLoc.neuFrac ℓ a2 u g := by
  have hsg : smulAdd t f g = fun z => t * f z + g z := rfl
  simp only [neuFracDefect, hsg]
  ring

/-- The midpoint identity for the defect makes it additive. -/
lemma neuFracDefect_add_of_midpoint {ℓ a2 : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hmid : ∀ s t : ℝ, neuFracDefect ℓ a2 u f g (s + t) + neuFracDefect ℓ a2 u f g (s - t)
      = 2 * neuFracDefect ℓ a2 u f g s)
    (h0 : neuFracDefect ℓ a2 u f g 0 = 0) :
    ∀ s t : ℝ, neuFracDefect ℓ a2 u f g (s + t)
      = neuFracDefect ℓ a2 u f g s + neuFracDefect ℓ a2 u f g t := by
  intro s t
  have h1 := hmid ((s + t) / 2) ((s + t) / 2)
  have h2 := hmid ((s + t) / 2) ((s - t) / 2)
  have e1 : (s + t) / 2 + (s + t) / 2 = s + t := by ring
  have e2 : (s + t) / 2 - (s + t) / 2 = (0 : ℝ) := by ring
  have e3 : (s + t) / 2 + (s - t) / 2 = s := by ring
  have e4 : (s + t) / 2 - (s - t) / 2 = t := by ring
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  rw [h0, add_zero] at h1
  linarith

theorem neuFrac_continuous_smul {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (u : EuclideanSpace ℝ (Fin 3)) {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous fun t : ℝ => Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => t * f z + g z) := by
  have hmid := neuFracDefect_midpoint (ℓ := ℓ) (a2 := a2) hℓ ha2 u hf hg
  have h0 : neuFracDefect ℓ a2 u f g 0 = 0 := neuFracDefect_zero u f g
  have hadd : ∀ s t : ℝ, neuFracDefect ℓ a2 u f g (s + t)
      = neuFracDefect ℓ a2 u f g s + neuFracDefect ℓ a2 u f g t :=
    neuFracDefect_add_of_midpoint u hmid h0
  obtain ⟨M, hM⟩ := neuFracDefect_bddAbove (ℓ := ℓ) (a2 := a2) hℓ ha2 u hf hg
  have hcontR : Continuous (neuFracDefect ℓ a2 u f g) :=
    additive_bddAbove_continuous hadd ⟨M, 1, by norm_num, fun t ht => hM t ht⟩
  have hfun : (fun t : ℝ => Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => t * f z + g z))
      = fun t : ℝ => neuFracDefect ℓ a2 u f g t + t ^ 2 * Work.BoseKinLoc.neuFrac ℓ a2 u f
          + Work.BoseKinLoc.neuFrac ℓ a2 u g := by
    funext t
    exact neuFrac_smulAdd_eq_defect u f g t
  rw [hfun]
  exact (hcontR.add ((continuous_id.pow 2).mul continuous_const)).add continuous_const

end Work.BoseFixB2.Polar
