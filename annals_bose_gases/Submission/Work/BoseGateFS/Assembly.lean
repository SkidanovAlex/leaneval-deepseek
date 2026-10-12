import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseGateFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.Assembly` — `GateInput` gives the corrected gate

The step `GateInput K₀ F T E → GateKernelFS K₀ F T (KzEnvAt E ρ)`.  All the
τ-free rows of the gate are *fields* of the corrected bundle `KinkFS` (the
potential bound, the `f_L` profile, the χ-pins, the guarded label arithmetic,
the kernel identity and the PSD half of the `χ̂²`-form); what is added here is

* the `ρ`-dependence: `A = τ + ρŴ₁`, `B = ρŴ₁` at `KzEnvAt E ρ`, with `ρ_z = ρ`;
* the **global `|ℬ| ≤ 𝒜`**, assembled from the honest `P_H^q` row `ABq` and the
  low-momentum positivity `W1low`, exactly as in `Work.BoseK15.AB_global` (with
  `τ̃ ≥ 0` in place of FS's explicit `τ`; `τ̃ ≥ 0` is the bundle's τ̃-pin);
* the kernel identity on non-wrapping pairs, from the box-model equation
  `boxKernel` plus the two χ-pins of the bundle
  (`Work.BoseK15.hasKernel_of_noWrap`).

The rows of the gate that are not fields of `KinkFS` are the explicit
hypotheses of `toGateKernelFS` — the eight τ-free FS §11/§12 rows.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

namespace GateInput

/-- `𝒜` of the re-pointed environment. -/
lemma A_kz (ρ : ℝ) (k : Mode) : (KzEnvAt E ρ).A k = E.tau k + ρ * E.W1 k := rfl

/-- `ℬ` of the re-pointed environment. -/
lemma B_kz (ρ : ℝ) (k : Mode) : (KzEnvAt E ρ).B k = ρ * E.W1 k := rfl

/-- `ρ_z = ρ` at the re-pointed environment. -/
lemma rho_kz {ρ : ℝ} (hρ : 0 ≤ ρ) (hℓ : 0 < E.ell) : (KzEnvAt E ρ).rho = ρ := by
  show Work.BoseB7.rhoZ (Real.sqrt (ρ * E.ell ^ 3)) E.ell = ρ
  rw [Work.BoseB7.rhoZ, Real.sq_sqrt (by positivity)]
  field_simp

/-- The mode momentum is odd (`F.kmom (-k) = -F.kmom k`). -/
lemma kmom_neg (h : GateInput K₀ F T E) (k : Mode) : F.kmom (-k) = -F.kmom k :=
  h.kink.kmom_neg k

/-- `χ̂` at the environment is the corpus `χ̂` at `ℓ • kmom`. -/
lemma hatChi_eq_mode (h : GateInput K₀ F T E) (k : Mode) :
    E.hatChi k = Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom k) :=
  h.kink.hatChi_eq k

/-- `χ̂²` at the environment is the corpus `χ̂²` at `ℓ • kmom`. -/
lemma hatChiSq_eq_mode (h : GateInput K₀ F T E) (k : Mode) :
    E.hatChiSq k = Work.BoseK15.corpusBox.hatChiSq (E.ell • F.kmom k) :=
  h.kink.hatChiSq_eq k

/-- `τ̃` is even at the modes. -/
lemma tau_even_m (h : GateInput K₀ F T E) (k : Mode) : E.tau (-k) = E.tau k := by
  rw [h.tau_eq (-k), h.tau_eq k, h.kink.kmom_neg k, h.tau_even]

/-- `Ŵ₁` is even at the modes. -/
lemma W1_even_m (h : GateInput K₀ F T E) (k : Mode) : E.W1 (-k) = E.W1 k :=
  h.kink.W1_even k

/-- **The global `|ℬ| ≤ 𝒜`** (adaptation of `Work.BoseK15.AB_global` to the
smoothed symbol: on the `P_H^q` complement only `τ̃ ≥ 0` is used, not FS's
explicit `τ`). -/
lemma AB_global_kz (ρ : ℝ) (h : GateInput K₀ F T E) (hρ : AdmRho E ρ) :
    ∀ k : Mode, |(KzEnvAt E ρ).B k| ≤ (KzEnvAt E ρ).A k := by
  intro k
  by_cases hk : F.PHq E.KH E.aScat k
  · have h2 := h.ABq ρ hρ k hk
    rw [A_kz, B_kz] at h2
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

/-- **The gate at the re-pointed environment.** -/
theorem toGateKernelFS (ρ : ℝ) (h : GateInput K₀ F T E)
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
    GateKernelFS K₀ F T (KzEnvAt E ρ) where
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
    rw [rho_kz (E := E) hρ.1 hℓ]
    rfl
  AB := AB_global_kz ρ h hρ
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
    rw [rho_kz (E := E) hρ.1 hℓ]
    show |ρ * E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.W1 k * (KzEnvAt E ρ).alpha k| ≤ K₀ * ρ * E.aScat * E.KH⁻¹
    exact h.intOne ρ hρ
  q2exLowerR := fun Ψ => by
    rw [rho_kz (E := E) hρ.1 hℓ]
    exact h.q2exLowerR ρ hρ Ψ

end GateInput

end Work.BoseGateFS
