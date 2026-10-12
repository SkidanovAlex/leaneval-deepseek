import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseGateFS.GateHonest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.HonestRowsAssemble` — `HonestRows` from explicit rows

`HonestRows` (`GateHonest.lean`) is the row bundle the gate is proved from.  This
module gives the *only* way it is built: the τ-free bundle `KinkFS` of the
structural rows, the τ̃-pin, and the honest §11/§12 rows.

The split is deliberate.  `KinkFS` collects the rows that are *structural*
(about the potential, the χ-kernels, the `f_L` profile and the label arithmetic,
with the F1/F7 guards); it is a `Prop` and `KinkFS.mono` lowers its constant.  The
seven χ-sum rows and the §10/§11 rows (`hτ`, `hW1low`, `hbox`, `hα`, `hint`,
`hq2`) are kept as separate arguments because they are the ones whose constants
are *not* monotone in `K₀` for free, and because they are the rows that FS §11/§12
supply: this is the list a caller of the node has to discharge.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

/-- **`HonestRows` from the explicit rows.**  Every argument is one of the honest
rows of `BOSE_BOXFOCK_LEAD.md` §5.6 (or a field of the τ-free bundle). -/
def honestRows_of_rows (hK : KinkFS K₀ F T E) (hv : FSParamsView E)
    (hτ : ∀ ρ : ℝ, AdmRho E ρ → ∀ q : Mode, F.PHq E.KH E.aScat q →
      ‖F.kmom q‖ ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤ E.tau q)
    (hW1low : ∀ k : Mode, ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) → 0 ≤ E.W1 k)
    (hbox : ∀ i j : Mode, F.ccrK i j
      = Work.BoseK15.corpusBox.hatChiSq (E.ell • (F.kmom i - F.kmom j))
        - Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom i)
          * Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom j))
    (hα : ∀ ρ : ℝ, AdmRho E ρ → ∀ p q : Mode, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
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
      ≤ K₀ * E.aScat) :
    HonestRows K₀ F T E where
  hv := hv
  kink := hK
  hτ := hτ
  hW1low := hW1low
  hbox := hbox
  hα := hα
  hint := hint
  hq2 := hq2
  hatChi_small := hhatChi_small
  ccrX_small := hccrX_small
  sum_hatChiSq := hsum
  tail_hatChiSq := htail
  form_upper := hform_upper
  count_PL := hcount
  sum_W1sq := hsumW1sq

end Work.BoseGateFS
