import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseGateAll.Assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateAll.Rows` — the `All` gate from explicit rows

The port of `Submission/Work/BoseGateFS/GateRows.lean`
(`gateInput_of_rows`, `Q3KernelFS_of_rows`): the τ-free bundle `KinkFS` plus the
explicit honest §11/§12 rows give the corrected bund1e `GateInputAll`, hence the
frozen `All` gate `Q3KernelFSAll` at `KzEnvAt E ρ`.

The only change with respect to the corpus is the `Q₂^ex` row, which is
`hq2All : ∀ ρ, AdmRho E ρ → ∀ Ψ, T.NWindow E.bigM Ψ →
2ρŴ₁ω(0)⟨Gop⟩ ≤ ⟨Q2exAll (KzEnvAt E ρ)⟩ + (b/400)⟨gapOpT⟩`, i.e. exactly the
content of `Work.BoseRowQ2.RowQ2AllRegimeN` (there is no reserve here; it is
added downstream in `GateInputAll.toQ3KernelFSAll`).
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateAll

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR
open Work.BoseBoxFock
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

/-- **The honest bundle from explicit rows, `All` form.**  Every hypothesis is
either a row of a field of the τ-free bundle `KinkFS` or one of the honest
§11/§12 rows — the `All` twin of `Work.BoseGateFS.gateInput_of_rows`. -/
def gateInputAll_of_rows (hK : KinkFS K₀ F T E) (hv : FSParamsView E)
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
    (hq2All : ∀ ρ : ℝ, AdmRho E ρ → ∀ Ψ : F.H, T.NWindow E.bigM Ψ →
      2 * ρ * E.W1omega0 * F.qw Ψ (T.Gop E)
        ≤ F.qw Ψ (F.Q2exAll (KzEnvAt E ρ)) + (E.b / 400) * F.qw Ψ (T.gapOpT (KzEnvAt E ρ))) :
    GateInputAll K₀ F T E where
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
  q2exLowerR := hq2All
  boxKernel := hbox
  kink := hK

/-- **The `All` gate at the re-pointed environment, from the honest rows.**  The
`All` twin of `Work.BoseGateFS.Q3KernelFS_of_rows`. -/
theorem q3KernelFSAll_of_rows (hK : KinkFS K₀ F T E)
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
    (hq2All : ∀ ρ : ℝ, AdmRho E ρ → ∀ Ψ : F.H, T.NWindow E.bigM Ψ →
      2 * ρ * E.W1omega0 * F.qw Ψ (T.Gop E)
        ≤ F.qw Ψ (F.Q2exAll (KzEnvAt E ρ)) + (E.b / 400) * F.qw Ψ (T.gapOpT (KzEnvAt E ρ)))
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
    Work.BoseBoxFock.Q3KernelFSAll K₀ F T (KzEnvAt E ρ) :=
  GateInputAll.toQ3KernelFSAll ρ
    (gateInputAll_of_rows hK hv tauF htau htau0 htaue hτ hW1low hbox hα hint hq2All)
    hhatChi_small hccrX_small hsum htail hform_upper hcount hsumW1sq hℓ hρ

end Work.BoseGateAll
