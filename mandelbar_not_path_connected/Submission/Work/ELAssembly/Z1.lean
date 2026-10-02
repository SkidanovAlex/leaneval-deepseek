/-
# `ELAssembly` — the nest at `z₁`: from `ELNest.NestData` to `Work.ELRig.Z1Nest`

`Work.ELRig.Z1Nest hN z₁ Pa` is the bundle of the nest at the parabolic point that the
equator-leak argument (`Work.EL.equatorLeak_parity`) consumes.  This file *assembles* it from the
(now nonempty, band-free) interface `Work.ELNest.NestData c`, so that a caller only has to
produce a `NestData`.

Everything of `Z1Nest` except the two-sidedness of the level-`n` pairs is a field of `NestData` or
one of the theorems collected by `Work.ELNest.Z1_facts`; the two-sidedness of each level comes
from `Work.ELTop.pairSides` (ELTop's T6) and needs the non-degeneracy
`arcLen (Qp n).a (Qp n).b ≠ 0` of the two angles of the level-`n` pair, a rational check of the
certificate (`arcLen_bAng_ne_zero` below, once the two angles are identified with `βₙ'` and
`βₙ + 1`).
-/
import Mathlib
import Submission.Work.ELNest.Facts
import Submission.Work.ELNest.Nest_coLand
import Submission.Work.ELNest.bAng_range
import Submission.Work.ELTop.RigInput
import Submission.Work.ELRig.Inputs
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

variable {c : ℂ}

/-- **The non-degeneracy of the angles of the `z₁`-nest.**  The two angles `βₙ + 1` and `βₙ'` of
the level-`n` pair are distinct modulo `1`. -/
theorem arcLen_bAng_ne_zero (n : ℕ) :
    Work.EL.arcLen (Work.ELNest.bAng' n) (Work.ELNest.bAng n + 1) ≠ 0 := by
  have hb0 : 0 < Work.ELNest.bAng n := (Work.ELNest.bAng_range n).1.1
  have h1 : Work.ELNest.bAng n < Work.ELNest.alpha1 := (Work.ELNest.bAng_range n).1.2
  have h2 : Work.ELNest.alpha2 < Work.ELNest.bAng' n := (Work.ELNest.bAng_range n).2.1
  have h3 : Work.ELNest.alpha1 < Work.ELNest.alpha2 := by
    norm_num [Work.ELNest.alpha1, Work.ELNest.alpha2]
  have hlt' : Work.ELNest.bAng n < Work.ELNest.bAng' n := lt_trans h1 (lt_trans h3 h2)
  have hA : Work.ELNest.bAng' n < 1 := by
    have h := (Work.ELNest.bAng_range n).2.2
    have h' : Work.ELNest.beta0' < 1 := by norm_num [Work.ELNest.beta0']
    linarith
  have hpos : 0 < (Work.ELNest.bAng n + 1) - Work.ELNest.bAng' n := by linarith
  have hlt : (Work.ELNest.bAng n + 1) - Work.ELNest.bAng' n < 1 := by linarith
  rw [Work.EL.arcLen, Int.fract_eq_self.mpr ⟨le_of_lt hpos, hlt⟩]
  exact ne_of_gt hpos

/-- **The nest at `z₁`.**  From a `NestData` and the non-degeneracy of the level-`n` angles, the
bundle `Work.ELRig.Z1Nest` that the equator-leak argument consumes. -/
noncomputable def toZ1Nest (S : Work.ELNest.NestData c) (hJ : Work.Top.JordanForm)
    (hnd : ∀ n : ℕ, Work.EL.arcLen (S.Qp n).a (S.Qp n).b ≠ 0) :
    Work.EL.Z1Nest S.d.hN S.d.z₁ S.fl.Pa where
  P0 := S.P0
  P0_spec := ⟨S.P0a, S.P0b, S.P0y⟩
  sides_P0 := S.sides_P0
  Q := S.Qp
  sides_Q := fun n => Work.ELTop.pairSides S.d.hN hJ (S.Qp n) (hnd n)
  shrinks := Work.ELNest.Qnest_shrinks S
  z1_near_Q := S.z1_near_Q
  Q_ne_z1 := S.Qne
  shift := Work.ELNest.Qp_shift S
  base_shift := S.base_shift
  SP := Work.ELNest.sidePreserve S
  Pa_far := S.Pa_far

/-- The same, with the non-degeneracy of the level-`n` angles supplied by the certificate
identifications `(Qp n).a = βₙ'`, `(Qp n).b = βₙ + 1`. -/
noncomputable def toZ1Nest_of_angles (S : Work.ELNest.NestData c) (hJ : Work.Top.JordanForm)
    (hQa : ∀ n : ℕ, (S.Qp n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (S.Qp n).b = Work.ELNest.bAng n + 1) :
    Work.EL.Z1Nest S.d.hN S.d.z₁ S.fl.Pa :=
  toZ1Nest S hJ fun n => by
    rw [hQa n, hQb n]
    exact arcLen_bAng_ne_zero n

end Work.ELAssembly
