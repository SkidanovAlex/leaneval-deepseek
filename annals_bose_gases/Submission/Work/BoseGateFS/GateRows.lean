import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseGateFS.Bridge
import Submission.Work.BoseGateFS.TauRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.GateRows` — the honest bundle from explicit rows

This is the "K15 re-delivery" of `BOSE_BOXFOCK_LEAD.md` §5.6 in its cleanest
form: the honest bundle `GateInput` of the design (τ̃-pin, `P_H^q` domination,
the three density-uniform FS §11 rows, and the τ-free bundle `KinkFS`) assembled from

* the **corrected τ-free bundle** `KinkFS K₀ F T E` — which carries the
  potential bound, the `f_L` profile, the χ-pins and the guarded label/kernel rows
  (`Defs.lean` §3bis);
* the τ̃-pins (`tau_eq`, nonnegativity, evenness) — inputs, because at the honest
  model `E.tau = τ̃` by definition;
* `FSParamsView E` (the scalars) for `0 ≤ ε_T ≤ 1` and `ℓ > 0`;
* the **`P_H^q` rows** `A_ge`/`ABq`, derived here from the kinetic domination
  `hτ` by `A_ge_of_taurad`;
* the honest §11/§12 rows `W1low`, `boxKernel`, `alpha_lip`, `intOne`,
  `q2exLowerR` (the last three density-uniform in `ρ`).

The conclusion `∃ K₀, GateInput K₀ F T E` at a *single absolute* `K₀` is then
`GateInput.toQ3KernelFS` → `Work.BoseBoxFock.Q3KernelFS`.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

/-- **The honest bundle from explicit rows.**  Every hypothesis is either a row of
a field of the τ-free bundle or one of the honest §11/§12 rows listed in
`BOSE_BOXFOCK_LEAD.md` §5.6. -/
def gateInput_of_rows (hK : KinkFS K₀ F T E)
    (hv : FSParamsView E)
    (tauF : EuclideanSpace ℝ (Fin 3) → ℝ)
    (htau : ∀ k : Mode, E.tau k = tauF (F.kmom k))
    (htau0 : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ tauF p)
    (htaue : ∀ p : EuclideanSpace ℝ (Fin 3), tauF (-p) = tauF p)
    (hτ : ∀ ρ : ℝ, AdmRho E ρ → ∀ q : Mode, F.PHq E.KH E.aScat q →
      ‖F.kmom q‖ ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤ E.tau q)
    (hW1low : ∀ k : Mode, ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) → 0 ≤ E.W1 k)
    (hbox : ∀ i j : Mode, F.ccrK i j
      = Work.BoseK15.corpusBox.hatChiSq (E.ell • (F.kmom i - F.kmom j))
        - Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom i)
          * Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom j))
    (hα : ∀ ρ : ℝ, AdmRho E ρ → ∀ p q : Mode, F.PHq E.KH E.aScat p →
      F.PHq E.KH E.aScat q →
      |(KzEnvAt E ρ).alpha p - (KzEnvAt E ρ).alpha q|
        ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖)
    (hint : ∀ ρ : ℝ, AdmRho E ρ →
      |ρ * E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ F.PHset E, E.W1 k * (KzEnvAt E ρ).alpha k|
        ≤ K₀ * ρ * E.aScat * E.KH⁻¹)
    (hq2 : ∀ ρ : ℝ, AdmRho E ρ → ∀ Ψ : F.H,
      2 * ρ * E.W1omega0 * F.qw Ψ (T.Gop E)
        ≤ F.qw Ψ (F.Q2ex (KzEnvAt E ρ)) + (E.b / 400) * F.qw Ψ (T.gapOpT (KzEnvAt E ρ))
          + (1 / 2) * F.qw Ψ (F.dNumOpR (KzEnvAt E ρ)
              (fun k => rHi F E k ∧ ¬ F.PHq E.KH E.aScat k))) :
    GateInput K₀ F T E where
  tauF := tauF
  tau_eq := htau
  tau_nonneg := htau0
  tau_even := htaue
  W1low := hW1low
  heT0 := by
    rw [hv.eT_eq]
    exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
  heT1 := by
    rw [hv.eT_eq]
    exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)
  A_ge := fun ρ hρ q hq =>
    (A_ge_of_taurad (E := E) (K₀ := K₀) (fun k => hK.W1_le k) hρ.1 (hτ ρ hρ)).1 q hq
  ABq := fun ρ hρ q hq =>
    (A_ge_of_taurad (E := E) (K₀ := K₀) (fun k => hK.W1_le k) hρ.1 (hτ ρ hρ)).2 q hq
  alpha_lip := hα
  intOne := hint
  q2exLowerR := hq2
  boxKernel := hbox
  kink := hK

/-- **The gate at the re-pointed environment, from the honest rows.**  This is the
content of the node GATE: the corrected gate `Q3KernelFS` at `KzEnvAt E ρ`,
assembled from the honest bundle. -/
theorem Q3KernelFS_of_rows (hK : KinkFS K₀ F T E)
    (hv : FSParamsView E)
    (tauF : EuclideanSpace ℝ (Fin 3) → ℝ)
    (htau : ∀ k : Mode, E.tau k = tauF (F.kmom k))
    (htau0 : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ tauF p)
    (htaue : ∀ p : EuclideanSpace ℝ (Fin 3), tauF (-p) = tauF p)
    (hτ : ∀ ρ : ℝ, AdmRho E ρ → ∀ q : Mode, F.PHq E.KH E.aScat q →
      ‖F.kmom q‖ ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤ E.tau q)
    (hW1low : ∀ k : Mode, ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) → 0 ≤ E.W1 k)
    (hbox : ∀ i j : Mode, F.ccrK i j
      = Work.BoseK15.corpusBox.hatChiSq (E.ell • (F.kmom i - F.kmom j))
        - Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom i)
          * Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom j))
    (hα : ∀ ρ : ℝ, AdmRho E ρ → ∀ p q : Mode, F.PHq E.KH E.aScat p →
      F.PHq E.KH E.aScat q →
      |(KzEnvAt E ρ).alpha p - (KzEnvAt E ρ).alpha q|
        ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖)
    (hint : ∀ ρ : ℝ, AdmRho E ρ →
      |ρ * E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ F.PHset E, E.W1 k * (KzEnvAt E ρ).alpha k|
        ≤ K₀ * ρ * E.aScat * E.KH⁻¹)
    (hq2 : ∀ ρ : ℝ, AdmRho E ρ → ∀ Ψ : F.H,
      2 * ρ * E.W1omega0 * F.qw Ψ (T.Gop E)
        ≤ F.qw Ψ (F.Q2ex (KzEnvAt E ρ)) + (E.b / 400) * F.qw Ψ (T.gapOpT (KzEnvAt E ρ))
          + (1 / 2) * F.qw Ψ (F.dNumOpR (KzEnvAt E ρ)
              (fun k => rHi F E k ∧ ¬ F.PHq E.KH E.aScat k)))
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
  GateInput.toQ3KernelFS (gateInput_of_rows hK hv tauF htau htau0 htaue hτ hW1low hbox
    hα hint hq2) hhatChi_small hccrX_small hsum htail hform_upper hcount hsumW1sq hℓ ρ hρ

end Work.BoseGateFS
