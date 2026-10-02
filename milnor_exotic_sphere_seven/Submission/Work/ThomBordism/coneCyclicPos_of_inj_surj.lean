import Mathlib
import Submission.Work.ThomBordism.chainSetup_cone
import Submission.Work.ThomBordism.coneCyclicPos_of_inj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- **Cyclicity at `m` from injectivity and surjectivity of `ψ` at `m + 1`.**

This is the converse of the two extractions `coneCyclicPos_inj` and `coneCyclicPos_surj`: if every
cone-`(m+1)`-cycle has its base component a coboundary (`hinj`) and every `Tot`-cycle in degree
`(m+1) + n` is hit by `coneD m` with vanishing base component (`hsurj`), then the cone is cyclic at
degree `m + 1`.

Combining the two.  Given a cone-`(m+1)`-cycle `p = (a, b)`, `coneCyclicPos_of_inj` splits it as

  `(a, b) = (0, b') + coneD m q`,   with `(0, b')` again a cone-cycle;

the second component of that cycle condition is `totShiftD (m+1) b' = 0`, so `hsurj` gives
`q'` with `coneD m q' = (0, b')`, and then `(a, b) = coneD m (q' + q)` by additivity of `coneD`
(`coneD_add`). -/
theorem coneCyclicPos_of_inj_surj {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) (m : ℕ)
    (hinj : ∀ (a : Work.ThomBordism.BaseC W ((m + 1) + 1))
      (b : Work.ThomBordism.TotC Z W ((m + 1) + n)),
      Work.ThomBordism.ConeCycle Z n U τ W hW (m + 1) (a, b) →
        ∃ a' : Work.ThomBordism.BaseC W (m + 1),
          Work.Cohomology.cochainDiffLM ℤ (Work.ThomBordism.baseSSet W) (m + 1) a' = -a)
    (hsurj : ∀ b : Work.ThomBordism.TotC Z W ((m + 1) + n),
      Work.ThomBordism.totShiftD Z n W (m + 1) b = 0 →
        ∃ q : Work.ThomBordism.ConeC Z n W m,
          Work.ThomBordism.coneD Z n U τ W hW m q = (0, b)) :
    Work.ThomBordism.ConeCyclicPos Z n U τ W hW m := by
  intro p hp
  obtain ⟨a, b⟩ := p
  -- Split the cycle as `(0, b') + coneD m q` using the injectivity half.
  obtain ⟨q, b', hcyc', hsplit⟩ :=
    coneCyclicPos_of_inj Z n U τ W hW m hinj hp
  -- `b'` is a `Tot`-cycle, so the surjectivity half applies to it.
  have hb' : totShiftD Z n W (m + 1) b' = 0 := by
    have hs := coneCycle_snd Z n U τ W hW m hcyc'
    simpa only [map_zero, zero_add] using hs
  obtain ⟨q', hq'⟩ := hsurj b' hb'
  refine ⟨q' + q, ?_⟩
  rw [coneD_add, hq']
  exact hsplit.symm

end

end Work.ThomBordism
