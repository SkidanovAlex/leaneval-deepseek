import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeSets
import Submission.Work.ThomBordism.KeyLocal.tau_eq_pm_stdModelGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

/-!
# The chart-piece vocabulary of the KeyLocal last mile

Two objects shared by the pieces of the last-mile plan `_kl/NOTE_SESSION10.md`:

* `tChartA` — the tangential coordinate map of the chart piece `tubeBaseSet E C ND i`, namely the
  translated chart of the normal datum's cover chart composed with the foot map of the tube;
* `tauSign` — the *universal* sign `τ₀ = ±1` with `FrameSigns.tau = τ₀ • stdModelGen 8`
  (`KeyLocal.tau_eq_pm_stdModelGen`, PROVED).  It is a single integer because `tau` is a fixed
  element of a free rank-one `ℤ`-module; this is what makes the sign of the last-mile comparison
  *uniform* without ever being computed.
-/

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.FrameSigns

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The tangential coordinate map of the chart piece.**  On the part of the tube over the cover
chart `i` of the normal datum, the translated chart map composed with the foot. -/
def tChartA (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    C(↥(tubeBaseSet E C ND i), Work.Tubular.Euc 8) :=
  (FrameSigns.chartTrans V i.1 x (ND.baseSet_sub i.1 i.2 x hx)).comp (tubeFootSrc E C ND i)

@[simp] theorem tChartA_apply (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i)
    (y : ↥(tubeBaseSet E C ND i)) :
    tChartA E C ND i x hx y
      = FrameSigns.chartTrans V i.1 x (ND.baseSet_sub i.1 i.2 x hx)
          (tubeFootSrc E C ND i y) := rfl

/-- **The universal sign of the frame-signature model class.**  `FrameSigns.tau` is a `±1`-multiple
of the determinate standard generator `stdModelGen 8`; `tauSign` is *the* multiplier (well defined
because `tau` is a fixed class). -/
noncomputable def tauSign : ℤ :=
  Classical.choose (Work.ThomBordism.KeyLocal.tau_eq_pm_stdModelGen)

theorem tauSign_spec : (tauSign = 1 ∨ tauSign = -1) ∧
    FrameSigns.tau = tauSign • Work.ThomBordism.stdModelGen 8 :=
  Classical.choose_spec (Work.ThomBordism.KeyLocal.tau_eq_pm_stdModelGen)

theorem tauSign_eq_one_or_neg_one : tauSign = 1 ∨ tauSign = -1 := tauSign_spec.1

theorem tau_eq_tauSign_smul_stdModelGen :
    FrameSigns.tau = tauSign • Work.ThomBordism.stdModelGen 8 := tauSign_spec.2

end

end Work.ThomBordism.KeyLocal
