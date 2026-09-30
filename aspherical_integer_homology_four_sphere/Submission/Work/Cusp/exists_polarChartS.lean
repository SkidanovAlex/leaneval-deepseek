/-
# The shifted polar chart `Θ_v^{(c)}` as an `OpenPartialHomeomorph`

`ThetaPolarS v c p y` (`Work.Cusp.Charts`) is the polar chart of the `v`-th cusp with the angle
coordinate read off the `c`-shifted *lift* `uS c p = c + Int.fract (u p - c)` of the perimeter
parameter instead of the perimeter parameter `u p` itself.  The two charts `ThetaPolar` and
`ThetaPolarS` describe the same points of the filling piece (they differ by a multiple of `2π` in
the angle, hence by a lattice translation of the UHS coordinate), but the shifted version is
continuous on the `c`-shifted wedges `wedgeS c k`, where the unshifted one jumps.

This file assembles the chart as an `OpenPartialHomeomorph`:

* the source `polarSourceS v c k B` and the target `polarTargetS v c k B` are open
  (`isOpen_polarSourceS`, `isOpen_polarTargetS`);
* `ThetaPolarS v c` is continuous on the source (`ThetaPolarS_continuousOn`, restricted) and its
  explicit inverse `cuspInvInner v` is continuous on the target (`continuous_cuspInvInner`,
  restricted);
* the two round-trip identities are `cuspInvInner_ThetaPolarS`
  (`cuspInvInner v (ThetaPolarS v c p y) = (p,y)`, the left inverse) and
  `ThetaPolarS_cuspInvInner` (`ThetaPolarS v c (cuspInvInner v q) = q` on the polar box with
  `uqOf v q - c ∈ [0,1)`, the right inverse);
* `uqOf v (ThetaPolarS v c p y) = uS c p` (`uqOf_ThetaPolarS`) is what makes the source map into
  the target, and `cuspInvInner_nrm_gt` (the recovered layer parameter is `> 1/24`) is what makes
  the inverse map the target back into the source.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.ThetaPolarS_continuousOn
import Submission.Work.Cusp.ThetaPolarS_cuspInvInner
import Submission.Work.Cusp.cuspInvInner_ThetaPolar
import Submission.Work.Cusp.cuspInvInner_continuousOn
import Submission.Work.Cusp.cuspInvInner_uqOf
import Submission.Work.Cusp.isOpen_wedgeS
import Submission.Work.Cusp.isOpen_polarSourceS
import Submission.Work.Cusp.isOpen_polarTargetS
import Submission.Work.Cusp.uqOf_ThetaPolarS
import Submission.Work.Cusp.cuspInvInner_nrm_gt
import Submission.Work.Cusp.cuspInvInner_ThetaPolarS

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- `Int.fract (Int.fract x - c) = Int.fract (x - c)`: the fractional part of `x` differs from `x`
by the integer `⌊x⌋`, and `Int.fract` is invariant under integer translations. -/
private lemma fract_fract_sub (x c : ℝ) : Int.fract (Int.fract x - c) = Int.fract (x - c) := by
  have h : x - c = (Int.fract x - c) + ((⌊x⌋ : ℤ) : ℝ) := by
    have h1 := Int.floor_add_fract x
    linarith
  rw [h, Int.fract_add_intCast]

theorem exists_polarChartS (v : Fin 5) (c : ℝ) (k : Fin 4) (B : Set E4) (hB : IsOpen B)
    (hBs : B ⊆ polarBox) :
    ∃ Φ : OpenPartialHomeomorph (E2 × E2) E4,
      Φ.source = polarSourceS v c k B ∧ Φ.target = polarTargetS v c k B ∧
        ∀ z, Φ z = ThetaPolarS v c z.1 z.2 := by
  refine ⟨{ toFun := fun z => ThetaPolarS v c z.1 z.2
            invFun := cuspInvInner v
            source := polarSourceS v c k B
            target := polarTargetS v c k B
            map_source' := ?_
            map_target' := ?_
            left_inv' := ?_
            right_inv' := ?_
            continuousOn_toFun := ?_
            continuousOn_invFun := ?_
            open_source := ?_
            open_target := ?_ }, rfl, rfl, ?_⟩
  · -- `ThetaPolarS` maps the source into the target
    intro z hz
    obtain ⟨hzw, hzn, hzB⟩ := hz
    refine ⟨hzB, ?_, ?_⟩
    · rw [uqOf_ThetaPolarS v c z.1 z.2]
      have h1 : uS c z.1 - c = Int.fract (u z.1 - c) := by rw [uS]; ring
      rw [h1, Set.mem_Ico]
      exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · rw [uqOf_ThetaPolarS v c z.1 z.2]
      have h1 : uS c z.1 - c = Int.fract (u z.1 - c) := by rw [uS]; ring
      have h2 : Int.fract (Int.fract (u z.1 - c)) = Int.fract (u z.1 - c) :=
        Int.fract_eq_self.mpr ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      rw [h1, h2]
      exact hzw.2
  · -- `cuspInvInner` maps the target back into the source
    intro q hq
    obtain ⟨hqB, hqu, hqf⟩ := hq
    have hqbox : q ∈ polarBox := hBs hqB
    have hnrm := cuspInvInner_nrm_gt v q hqbox
    refine ⟨?_, hnrm, ?_⟩
    · rw [wedgeS]
      refine ⟨lt_trans (by norm_num) hnrm, ?_⟩
      have hu : u (cuspInvInner v q).1 = Int.fract (uqOf v q) := cuspInvInner_uqOf v q hqbox
      rw [hu, fract_fract_sub]
      exact hqf
    · rw [ThetaPolarS_cuspInvInner v c q hqbox hqu]
      exact hqB
  · -- left inverse
    intro z hz
    exact cuspInvInner_ThetaPolarS v c z.1 z.2
  · -- right inverse
    intro q hq
    obtain ⟨hqB, hqu, _⟩ := hq
    exact ThetaPolarS_cuspInvInner v c q (hBs hqB) hqu
  · -- continuity of the chart
    refine (ThetaPolarS_continuousOn v c k).mono ?_
    intro z hz
    exact hz.1
  · -- continuity of the inverse
    exact (continuous_cuspInvInner v).continuousOn
  · -- the source is open
    exact isOpen_polarSourceS v c k B hB
  · -- the target is open
    exact isOpen_polarTargetS v c k B hB
  · -- the chart map
    intro z
    rfl

end Work.Cusp
