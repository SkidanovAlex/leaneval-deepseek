import ChallengeDeps
import Submission.Work.BoseGateAll.Rows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateAll.Honest` — the `All` gate from the honest row bundle

The port of `Submission/Work/BoseGateFS/GateHonest.lean` §2–§4 and of
`HonestRowsAssemble.lean` to the corrected vocabulary:

* `honestRowsAll_of_rows` — the honest row bundle `HonestRowsAll` from the
  explicit rows (`honestRows_of_rows`, with the corrected `Q₂^{ex,all}` row);
* `q3KernelFSAll_tauSm` — the gate at one honest environment (`q3KernelFS_tauSm`);
* `q3KernelFSAll_of_honestRows` — the same from the bundle, with the `τ̃`-pin
  supplied as the honest model's `honE_tau` (`q3KernelFS_of_rows`);
* `honestGateAtFSAll_of_rows`, `honestGateFSAll_of_rows` — `HonestGateAtFSAll` and
  the node's `HonestGateFSAll` from the bundle at every admissible `μ`.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateAll

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR
open Work.BoseBoxFock
open Work.BoseBoxFix
open Work.BoseGateFS
open Work.UBB
open _root_.BoseGases Submission.BoseGases

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

/-! ## 1. The row bundle -/

/-- **`HonestRowsAll` from the explicit rows.**  Every argument is one of the
honest rows of `BOSE_BOXFOCK_LEAD.md` §5.6 (or a field of the τ-free bundle);
the `All` twin of `Work.BoseGateFS.honestRows_of_rows`. -/
def honestRowsAll_of_rows (hK : KinkFS K₀ F T E) (hv : FSParamsView E)
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
      ≤ K₀ * E.aScat) :
    HonestRowsAll K₀ F T E where
  hv := hv
  kink := hK
  hτ := hτ
  hW1low := hW1low
  hbox := hbox
  hα := hα
  hint := hint
  hq2 := hq2All
  hatChi_small := hhatChi_small
  ccrX_small := hccrX_small
  sum_hatChiSq := hsum
  tail_hatChiSq := htail
  form_upper := hform_upper
  count_PL := hcount
  sum_W1sq := hsumW1sq

/-! ## 2. The gate at one honest environment -/

/-- **The `All` gate at one honest environment.**  `q3KernelFS_tauSm` with the
corrected row `hq2All` (reserve-free, windowed) in place of the corpus's `hq2`. -/
theorem q3KernelFSAll_tauSm
    (htau : ∀ k : Mode, E.tau k = Work.BoseBoxFock.tauSm E.eT E.s E.d E.ell (F.kmom k))
    (hv : FSParamsView E)
    (hK : KinkFS K₀ F T E)
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
    (hℓ : 0 < E.ell) :
    ∀ ρ : ℝ, AdmRho E ρ → Work.BoseBoxFock.Q3KernelFSAll K₀ F T (KzEnvAt E ρ) := by
  intro ρ hρ
  have hE0 : (0 : ℝ) ≤ E.eT := by
    rw [hv.eT_eq]; exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
  have hE1 : E.eT ≤ 1 := by
    rw [hv.eT_eq]; exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)
  exact q3KernelFSAll_of_rows hK hv (fun p => Work.BoseBoxFock.tauSm E.eT E.s E.d E.ell p)
    htau (fun p => Work.BoseBoxFock.tauSm_nonneg _ _ _ _ hE0 hE1 p) (fun p => tauSm_even _ _ _ _ p)
    hτ hW1low hbox hα hint hq2All hhatChi_small hccrX_small hsum htail hform_upper hcount
    hsumW1sq hℓ ρ hρ

/-! ## 3. The gate from the row bundle -/

/-- The `τ̃`-pin at an environment whose `tau` is `tauSm`: the honest model's
(`q3KernelFS_of_rows`). -/
theorem q3KernelFSAll_of_honestRows
    (h : HonestRowsAll K₀ F T E)
    (htau : ∀ k : Mode, E.tau k = Work.BoseBoxFock.tauSm E.eT E.s E.d E.ell (F.kmom k)) :
    ∀ ρ : ℝ, AdmRho E ρ → Work.BoseBoxFock.Q3KernelFSAll K₀ F T (KzEnvAt E ρ) :=
  q3KernelFSAll_tauSm htau h.hv h.kink h.hτ h.hW1low h.hbox h.hα h.hint h.hq2
    h.hatChi_small h.ccrX_small h.sum_hatChiSq h.tail_hatChiSq h.form_upper h.count_PL
    h.sum_W1sq (Work.BoseB7.ell_pos E h.hv)

/-- **`HonestGateAtFSAll` from the honest row bundle at every admissible `μ`.** -/
theorem honestGateAtFSAll_of_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {HM : ∀ μ : ℝ, HonestModes v μ} {ε₀ K₀ b₀ : ℝ}
    (hK₀ : 0 ≤ K₀) (hb₀ : 0 < b₀)
    (hb : ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ ε₀ →
      b₀ ≤ (HonestBoxFam v h fc fu HM μ).E.b)
    (hadm : ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ ε₀ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      AdmRho (HonestBoxFam v h fc fu HM μ).E ρ)
    (hrows : ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ ε₀ →
      HonestRowsAll K₀ (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).T
        (HonestBoxFam v h fc fu HM μ).E) :
    HonestGateAtFSAll v h fc fu HM ε₀ K₀ b₀ :=
  ⟨hK₀, hb₀, hb, fun μ hμ hε ρ hρ =>
    q3KernelFSAll_of_honestRows (hrows μ hμ hε) (Work.BoseGateFS.honE_tau HM μ)
      ρ (hadm μ hμ hε ρ hρ)⟩

/-- **`HonestGateFSAll`**: one absolute pair `(K₀, b₀)`, one diluteness threshold
`εg` and one cube-size function `Ng`, such that the corrected gate holds at
*every* honest model with `Ng μ ≤ N`. -/
theorem honestGateFSAll_of_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {K₀ b₀ : ℝ} (hK₀ : 0 ≤ K₀) (hb₀ : 0 < b₀)
    (Ng : ℝ → ℕ) (εg : ℝ) (hεg0 : 0 < εg) (hεg1 : εg ≤ 1)
    (hb : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ εg → b₀ ≤ (HonestBoxFam v h fc fu HM μ).E.b)
    (hadm : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ εg → ∀ ρ : ℝ, CloseCondFS v μ ρ →
        AdmRho (HonestBoxFam v h fc fu HM μ).E ρ)
    (hrows : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ εg →
        HonestRowsAll K₀ (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).T
          (HonestBoxFam v h fc fu HM μ).E) :
    HonestGateFSAll v h fc fu K₀ b₀ :=
  ⟨Ng, εg, hεg0, hεg1, fun HM hN =>
    honestGateAtFSAll_of_rows hK₀ hb₀ (fun μ => hb HM hN μ) (fun μ => hadm HM hN μ)
      (fun μ => hrows HM hN μ)⟩

end Work.BoseGateAll
