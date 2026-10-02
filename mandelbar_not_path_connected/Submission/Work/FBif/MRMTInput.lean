/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif` — the gluing datum and the MRMT consumption (FBif, part 3b)

`Work.FBif.Straightening` is the abstract form of the straightening of the perturbed family.
This module states the
*granular* datum from which it follows: the gluing construction of FBif (a C¹ map equal to the
perturbation near the parabolic cycle and to the model `T_c` outside a bounded set, together with
its invariant Beltrami coefficient), fed into the consumer API of MRMT
(`Submission.Work.MRMT.Found`, which is proved and axiom-clean), together with Liouville's
theorem (`Work.FBif.antiholo_of_norm_sub_sq_bounded`).

The corresponding reduction is `Work.FBif.straightening_of_gluingFamily`, and the datum itself
is *constructed* in `FBif/GlueAssembly.lean` (`Work.FBif.exists_gluingDatum_scaled`), so that the
statement `Work.FBif.GluingDatum` is no longer a hypothesis of the area.
-/
import Submission.Work.MRMT.Found.M
import Submission.Work.FBif.Liouville

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function MeasureTheory
open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The FBif gluing datum.**  For a given accuracy `ε > 0`, a fixed far radius `R` and a fixed
cycle-neighbourhood radius `δ'`:

* `F` is the *glued* map — C¹, equal to the perturbation `perturb c q ε` along the parabolic
  cycle (for the fifth iterate, see `agree5`), and equal to the model `T_c` outside `ball 0 R`
  (`asymp`), so that `F` has the asymptotics of `z ↦ z̄² + c` at infinity;
* `μ` is the invariant Beltrami coefficient of `F` (`hinv`), admissible in the sense of
  `Work.MRMT.Found.Admissible`, supported in `ball 0 R` and with essential bound `≤ ε`; `S` is
  the exceptional (critical) set on which `F` fails to be orientation reversing;
* `decay` is the quantitative normalisation of `MRMT M1`: `principal μ z = z + O(C/‖z‖)` with
  `C ≤ ε`.  (MRMT proves this with the explicit constant `rcCd k R`, where `k ≤ ε` is the
  essential bound of `μ`; see `Work.MRMT.Found.record_uniform_qc_family`.)

From such a family (one datum for every `ε > 0`) the straightening follows:
`Work.FBif.straightening_of_gluingFamily`.  MRMT `M2″` (`principal_conj_contDiff`) makes
`Φ_ε ∘ F_ε ∘ Φ_ε⁻¹` entire antiholomorphic, Liouville's theorem turns it into a quadratic
antipolynomial `T_{c_ε}`, `agree5` transfers the fifth-iterate conjugacy to the perturbed map,
MRMT `M6` (`tendsto_principal`) gives `Φ_ε → id`, and `decay` (with `C ≤ ε`) gives `c_ε → c` and
`Φ_ε⁻¹ → id`. -/
structure GluingDatum (c : ℂ) (z₁ : ℂ) (q : ℂ → ℂ) (δ' R : ℝ) (ε : ℝ) where
  /-- the glued C¹ map. -/
  F : ℂ → ℂ
  /-- its invariant Beltrami coefficient. -/
  μ : ℂ → ℂ
  /-- `μ` is admissible. -/
  adm : Work.MRMT.Found.Admissible μ
  /-- the fixed far radius. -/
  hR : 0 < R
  /-- `μ` is supported in `ball 0 R`. -/
  supp : Function.support μ ⊆ Metric.closedBall 0 R
  /-- `μ` is small: its essential bound is at most `ε`. -/
  small : ∃ k : ℝ, 0 ≤ k ∧ k ≤ ε ∧ ∀ᵐ z ∂volume, ‖μ z‖ ≤ k
  /-- the quantitative normalisation of the principal solution. -/
  decay : ∃ C : ℝ, 0 ≤ C ∧ C ≤ ε ∧ ∀ z : ℂ, R ≤ ‖z‖ →
    ‖Work.MRMT.Found.principal μ z - z‖ ≤ C / ‖z‖
  /-- the glued map is C¹. -/
  contDiff : ContDiff ℝ 1 F
  /-- the exceptional set of `F` (the critical point). -/
  S : Set ℂ
  /-- `S` is discrete. -/
  hS : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, w ∉ S
  /-- `F` is orientation reversing off `S`. -/
  hrev : ∀ z ∉ S, ‖Work.MRMT.dz F z‖ < ‖Work.MRMT.dzbar F z‖
  /-- `μ` is invariant under `F`. -/
  hinv : ∀ᵐ z ∂volume, μ z = Work.MRMT.Found.pullRev μ F z
  /-- far away, `F` is the model map `T_c`. -/
  asymp : ∀ z : ℂ, R ≤ ‖z‖ → F z = Tantibar c z
  /-- near the parabolic point, the fifth iterate of `F` is that of the perturbation. -/
  agree5 : ∀ z : ℂ, ‖z - z₁‖ ≤ δ' → (F^[5]) z = ((perturb c q ε)^[5]) z

end Work.FBif

end
