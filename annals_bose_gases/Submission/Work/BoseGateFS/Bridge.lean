import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseGateFS.Assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.Bridge` — my gate interface is the design's `Q3KernelFS`

`Submission/Work/BoseBoxFock/Defs.lean` (subproject BoseBoxFock, node D-FS) fixes
the vocabulary of the honest box model and states the corrected gate as
`Work.BoseBoxFock.Q3KernelFS`.  `BoxGateFS` carries the *same* gate as
`Work.BoseGateFS.GateKernelFS` so that the gate can be assembled without
depending on the (parallel) D-FS module.  The two are field-for-field identical —
in particular `Work.BoseGateFS.rHi` and `Work.BoseBoxFock.RHi` are the same
predicate — so the bridge is the identity on the fields.

The consequence used downstream is `GateInput.toQ3KernelFS`: the honest §10
bundle of `BoseGateFS` produces the design's `Q3KernelFS` at `KzEnvAt E ρ`, which
is exactly what `honestGateAtFS_of_bundle` (below) feeds into `HonestGateAtFS`.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

/-- `rHi` is the design's `RHi`. -/
theorem rHi_eq_RHi (F : FockData Mode) (E : Q3Env Mode) :
    rHi F E = Work.BoseBoxFock.RHi F E := rfl

/-- **The gate, in the design's vocabulary.** -/
theorem GateKernelFS.toQ3KernelFS (h : GateKernelFS K₀ F T E) :
    Work.BoseBoxFock.Q3KernelFS K₀ F T E where
  W1_le := h.W1_le
  W1_even := h.W1_even
  A_even := h.A_even
  B_even := h.B_even
  B_eq := h.B_eq
  AB := h.AB
  A_ge := h.A_ge
  fL_nonneg := h.fL_nonneg
  fL_le_one := h.fL_le_one
  fL_even := h.fL_even
  fL_supp2 := h.fL_supp2
  kmom_subW := h.kmom_subW
  kmom_subL := h.kmom_subL
  hasKernelW := h.hasKernelW
  hasKernel_noWrap := h.hasKernel_noWrap
  hatChiSq_le := h.hatChiSq_le
  hatChi_le := h.hatChi_le
  hatChi_even := h.hatChi_even
  hatChiSq_even := h.hatChiSq_even
  hatChi_small := h.hatChi_small
  ccrX_small := h.ccrX_small
  hatChiSq_form := h.hatChiSq_form
  count_PL := h.count_PL
  sum_hatChiSq := h.sum_hatChiSq
  tail_hatChiSq := h.tail_hatChiSq
  sum_W1sq := h.sum_W1sq
  alpha_lip := h.alpha_lip
  W1omega0_nonneg := h.W1omega0_nonneg
  W1omega0_le := h.W1omega0_le
  intOne := h.intOne
  q2exLowerR := h.q2exLowerR

/-- **The honest §10 bundle gives the design's gate** at the re-pointed
environment (the τ-free χ/`f_L`/lattice rows are supplied by the caller, exactly
as in `Work.BoseK15.Q3Kernel'_of_box`). -/
theorem GateInput.toQ3KernelFS (h : GateInput K₀ F T E)
    (hhatChi_small : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * eta E)
    (hccrX_small : ∀ s q : Mode, E.fL s ≠ 0 → F.PHq E.KH E.aScat q →
      |T.ccrX s q| ≤ K₀ * eta E)
    (hsum : ∑ s ∈ excited Mode, |E.hatChiSq s| ≤ K₀)
    (htail : ∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
      ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ)))
    (hform_upper : ∀ (S : Finset Mode) (c : Mode → ℝ) (w : Mode → F.H),
      (∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s))
        ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (w s) (w s))
    (hcount : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ)
      ≤ K₀ * (E.Kl * E.KL) ^ 3)
    (hsumW1sq : E.ell ^ (-(3 : ℝ)) *
        ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
      ≤ K₀ * E.aScat)
    (hℓ : 0 < E.ell) (ρ : ℝ) (hρ : AdmRho E ρ) :
    Work.BoseBoxFock.Q3KernelFS K₀ F T (KzEnvAt E ρ) :=
  (GateInput.toGateKernelFS ρ h hhatChi_small hccrX_small hsum htail hform_upper hcount
    hsumW1sq hℓ hρ).toQ3KernelFS

end Work.BoseGateFS
