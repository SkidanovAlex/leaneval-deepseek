import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseGateAll.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateAll.Assembly` — `GateInputAll → Q3KernelFSAll`

The port of `Submission/Work/BoseGateFS/Assembly.lean` (`GateInput.toGateKernelFS`)
and `Bridge.lean` (`GateKernelFS.toQ3KernelFS`, `GateInput.toQ3KernelFS`) to the
`All` vocabulary: from the honest §10 bundle `GateInputAll` we produce the frozen
gate `Work.BoseBoxFock.Q3KernelFSAll` at the re-pointed environment
`KzEnvAt E ρ`.

Every field of `Q3KernelFSAll` except the last is transcribed verbatim from
`GateInput.toGateKernelFS` (the `All` gate's field list is that of `Q3KernelFS`).
The last field is where the two chains differ:

* the corpus's `GateInput.q2exLowerR` is stated with the **reserve**
  `½⟨dNumOpR (rHi ∖ P_H^q)⟩` already on its right-hand side and against `Q2ex`;
* `GateInputAll.q2exLowerR` is stated **reserve-free** against the corrected
  `Q2exAll`.  The reserve of the frozen `Q3KernelFSAll.q2exLowerR` is therefore
  added *here*, by `Work.BoseGateFS.Reserve.qw_dNumOpR_nonneg` — the
  `Reserve.qw_dNumOpR_nonneg` step of the design's recipe (`BOSE_ALL_DESIGN.md`
  item 6).  The positivity of `dNumOpR` needs `|ℬ_k| ≤ 𝒜_k`, which is exactly the
  `AB` field established two lines above (`AB_global_kzAll`).
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateAll

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

namespace GateInputAll

lemma A_kz (h : GateInputAll K₀ F T E) (ρ : ℝ) (k : Mode) :
    (KzEnvAt E ρ).A k = E.tau k + ρ * E.W1 k := rfl

lemma B_kz (h : GateInputAll K₀ F T E) (ρ : ℝ) (k : Mode) :
    (KzEnvAt E ρ).B k = ρ * E.W1 k := rfl

lemma rho_kz (h : GateInputAll K₀ F T E) {ρ : ℝ} (hρ : 0 ≤ ρ) (hℓ : 0 < E.ell) :
    (KzEnvAt E ρ).rho = ρ := by
  rw [Work.BoseB7.Q3Env.rho, Work.BoseB7.rhoZ]
  show (Real.sqrt (ρ * E.ell ^ 3)) ^ 2 / E.ell ^ 3 = ρ
  rw [Real.sq_sqrt (by positivity), mul_div_assoc, div_self (pow_ne_zero 3 (ne_of_gt hℓ)),
    mul_one]

lemma kmom_neg (h : GateInputAll K₀ F T E) (k : Mode) : F.kmom (-k) = -F.kmom k :=
  h.kink.kmom_neg k

lemma tau_even_m (h : GateInputAll K₀ F T E) (k : Mode) : E.tau (-k) = E.tau k := by
  rw [h.tau_eq (-k), h.tau_eq k, kmom_neg h k, h.tau_even]

lemma W1_even_m (h : GateInputAll K₀ F T E) (k : Mode) : E.W1 (-k) = E.W1 k :=
  h.kink.W1_even k

/-- **The global `|ℬ| ≤ 𝒜`** (the `All` twin of `GateInput.AB_global_kz`). -/
lemma AB_global_kzAll (ρ : ℝ) (h : GateInputAll K₀ F T E) (hρ : AdmRho E ρ) :
    ∀ k : Mode, |(KzEnvAt E ρ).B k| ≤ (KzEnvAt E ρ).A k := by
  intro k
  by_cases hk : F.PHq E.KH E.aScat k
  · have h2 := h.ABq ρ hρ k hk
    rw [A_kz h ρ k, B_kz h ρ k] at h2
    have h3 : (0 : ℝ) ≤ |ρ * E.W1 k| := abs_nonneg _
    show |ρ * E.W1 k| ≤ E.tau k + ρ * E.W1 k
    linarith
  · have hk' : ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) := le_of_lt (not_le.mp hk)
    have hW : (0 : ℝ) ≤ E.W1 k := h.W1low k hk'
    have htau : (0 : ℝ) ≤ E.tau k := by
      rw [h.tau_eq k]; exact h.tau_nonneg _
    have hρnn : (0 : ℝ) ≤ ρ := hρ.1
    have hBnn : (0 : ℝ) ≤ ρ * E.W1 k := mul_nonneg hρnn hW
    show |ρ * E.W1 k| ≤ E.tau k + ρ * E.W1 k
    rw [abs_of_nonneg hBnn]
    linarith

/-- **The `All` gate at the re-pointed environment.**  Same proof as
`GateInput.toGateKernelFS`; only the last field changes (the reserve is added by
nonnegativity, since `GateInputAll.q2exLowerR` is reserve-free). -/
theorem toQ3KernelFSAll (ρ : ℝ) (h : GateInputAll K₀ F T E)
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
    (hℓ : 0 < E.ell) (hρ : AdmRho E ρ) :
    Work.BoseBoxFock.Q3KernelFSAll K₀ F T (KzEnvAt E ρ) where
  W1_le := fun k => by
    show |E.W1 k| ≤ K₀ * E.aScat
    exact h.kink.W1_le k
  W1_even := fun k => by
    show E.W1 (-k) = E.W1 k
    exact W1_even_m h k
  A_even := fun k => by
    show E.tau (-k) + ρ * E.W1 (-k) = E.tau k + ρ * E.W1 k
    rw [tau_even_m h k, W1_even_m h k]
  B_even := fun k => by
    show ρ * E.W1 (-k) = ρ * E.W1 k
    rw [W1_even_m h k]
  B_eq := fun k => by
    rw [rho_kz h hρ.1 hℓ]
    rfl
  AB := AB_global_kzAll ρ h hρ
  A_ge := fun q hq => h.A_ge ρ hρ q hq
  fL_nonneg := fun s => by
    show (0 : ℝ) ≤ E.fL s
    exact h.kink.fL_nonneg s
  fL_le_one := fun s => by
    show E.fL s ≤ 1
    exact h.kink.fL_le_one s
  fL_even := fun s => by
    show E.fL (-s) = E.fL s
    exact h.kink.fL_even s
  fL_supp2 := fun s hs => by
    show ‖F.kmom s‖ ≤ 2 * (E.KL * Real.sqrt (E.mu * E.aScat))
    exact h.kink.fL_supp2 s hs
  kmom_subW := fun s k hs hk hW => h.kink.kmom_subW s k hs hk hW
  kmom_subL := fun s s' hs hs' => h.kink.kmom_subL s s' hs hs'
  hasKernelW := fun i j hi hj hW => by
    show F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
    exact h.kink.hasKernelW i j hi hj hW
  hasKernel_noWrap := fun i j hij => by
    have hwrap : Work.BoseK15.NoWrap F.kmom i j := hij
    show F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j
    exact Work.BoseK15.hasKernel_of_noWrap F.kmom h.boxKernel
      h.kink.hatChiSq_eq h.kink.hatChi_eq hwrap
  hatChiSq_le := fun s => by
    show |E.hatChiSq s| ≤ 1
    exact h.kink.hatChiSq_le s
  hatChi_le := fun s => by
    show |E.hatChi s| ≤ 1
    exact h.kink.hatChi_le s
  hatChi_even := fun s => by
    show E.hatChi (-s) = E.hatChi s
    exact h.kink.hatChi_even s
  hatChiSq_even := fun s => by
    show E.hatChiSq (-s) = E.hatChiSq s
    exact h.kink.hatChiSq_even s
  hatChi_small := hhatChi_small
  ccrX_small := hccrX_small
  hatChiSq_form := fun S c w hguard => by
    refine ⟨?_, hform_upper S c w⟩
    show (0 : ℝ) ≤ ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s)
    exact h.kink.hatChiSq_form_psd S c w hguard
  count_PL := hcount
  sum_hatChiSq := hsum
  tail_hatChiSq := htail
  sum_W1sq := hsumW1sq
  alpha_lip := fun p q hp hq => h.alpha_lip ρ hρ p q hp hq
  W1omega0_nonneg := by
    show (0 : ℝ) ≤ E.W1omega0
    exact h.kink.W1omega0_nonneg
  W1omega0_le := by
    show E.W1omega0 ≤ K₀ * E.aScat
    exact h.kink.W1omega0_le
  intOne := by
    rw [rho_kz h hρ.1 hℓ]
    show |ρ * E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.W1 k * (KzEnvAt E ρ).alpha k| ≤ K₀ * ρ * E.aScat * E.KH⁻¹
    exact h.intOne ρ hρ
  q2exLowerR := fun Ψ hΨ => by
    -- **the reserve of the frozen `Q3KernelFSAll.q2exLowerR` is free**
    -- (`Reserve.qw_dNumOpR_nonneg` at the `AB` established above), so the
    -- reserve-free row of `GateInputAll` gives the field.
    have hAB := AB_global_kzAll ρ h hρ
    have hpos : 0 ≤ F.qw Ψ (F.dNumOpR (KzEnvAt E ρ)
        (fun k => Work.BoseBoxFock.RHi F (KzEnvAt E ρ) k
          ∧ ¬ F.PHq (KzEnvAt E ρ).KH (KzEnvAt E ρ).aScat k)) :=
      qw_dNumOpR_nonneg (F := F) (E := KzEnvAt E ρ) hAB _ Ψ
    have hrow := h.q2exLowerR ρ hρ Ψ hΨ
    have hgoal : 2 * ρ * E.W1omega0 * F.qw Ψ (T.Gop E)
        ≤ F.qw Ψ (F.Q2exAll (KzEnvAt E ρ)) + (E.b / 400) * F.qw Ψ (T.gapOpT (KzEnvAt E ρ))
          + (1 / 2) * F.qw Ψ (F.dNumOpR (KzEnvAt E ρ)
              (fun k => Work.BoseBoxFock.RHi F (KzEnvAt E ρ) k
                ∧ ¬ F.PHq (KzEnvAt E ρ).KH (KzEnvAt E ρ).aScat k)) := by
      linarith
    rw [rho_kz h hρ.1 hℓ]
    exact hgoal

end GateInputAll

end Work.BoseGateAll
