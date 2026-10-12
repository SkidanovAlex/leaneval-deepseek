import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseGateFS.GateRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.GateHonest` — the gate at the honest model

The node GATE: the corrected gate `Work.BoseBoxFock.Q3KernelFS` at the honest box
model (`HonestModes` / `tildeDataHon` / `KzEnvHon`), and its
`HonestGateAtFS` / `HonestGateFS` packaging.

## The shape of the result

`BOSE_BOXFOCK_LEAD.md` §5.6 asks for `HonestGateFS` "re-run with" the four
repaired rows, `W1f := ζ·Ŵ₁`, `τ := τ̃`, `hW1decay` replaced, and the three
density-uniform FS §11 rows.  The rows that the honest §10 estimates take as
input are therefore hypotheses of the theorems here — exactly as in
`Work.BoseK15.Q3Kernel'_of_box`, whose hypothesis is the bundle `K15Input`.

* `q3KernelFS_tauSm` — **the gate at one honest environment**: given the τ-free
  bundle `KinkFS`, `FSParamsView`, the τ̃-pin `E.tau = tauSm`, the kinetic
  domination `hτ` on `P_H^q`, and the honest §11/§12 rows, the corrected gate holds
  at every admissible density `ρ`.
* `honestGateAtFS_of_rows` / `honestGateFS_of_rows` — the same at the honest
  family `HonestBoxFam`, packaged as `HonestGateAtFS` / `HonestGateFS`.
* `tauSm_nonneg`, `tauSm_even` — the τ̃-pins at the concrete symbol.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

/-! ## 1. The τ̃-pins at the concrete symbol -/

/-- `tauProf` is nonnegative (it dominates `(r-2)₊²`). -/
lemma tauProf_nonneg (r : ℝ) : 0 ≤ Work.BoseBoxFock.tauProf r := by
  have h : (max 0 (r - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf r :=
    Work.BoseBoxFock.tauProf_spec.2.2.1 r
  exact le_trans (sq_nonneg _) h

/-- `τ̃ ≥ 0`. -/
lemma tauSm_nonneg (eT s d ℓ : ℝ) (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1)
    (p : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Work.BoseBoxFock.tauSm eT s d ℓ p := by
  simp only [Work.BoseBoxFock.tauSm]
  have h1 : 0 ≤ (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖p‖ / (2 * s * ℓ)⁻¹) :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (tauProf_nonneg _)
  have h2 : 0 ≤ eT * ((2 * d * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖p‖ / (2 * d * s * ℓ)⁻¹) :=
    mul_nonneg (mul_nonneg heT0 (sq_nonneg _)) (tauProf_nonneg _)
  linarith

/-- `τ̃` is radial, hence even. -/
lemma tauSm_even (eT s d ℓ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.tauSm eT s d ℓ (-p) = Work.BoseBoxFock.tauSm eT s d ℓ p := by
  rw [Work.BoseBoxFock.tauSm, Work.BoseBoxFock.tauSm, norm_neg]

/-- `tauSm` is the `tauTilde` of `TauTilde.lean` at the chosen profile. -/
lemma tauSm_eq_tauTilde (eT s d ℓ : ℝ) (k : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.tauSm eT s d ℓ k = tauTilde Work.BoseBoxFock.tauProf eT s d ℓ k := rfl

/-! ## 2. The gate at one honest environment -/

/-- **The corrected gate at one honest environment.**  All rows are the honest
§11/§12 inputs listed in `BOSE_BOXFOCK_LEAD.md` §5.6; the `P_H^q` rows and the
transport from K15 are done in `GateRows.lean`. -/
theorem q3KernelFS_tauSm {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
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
    (hℓ : 0 < E.ell) :
    ∀ ρ : ℝ, AdmRho E ρ → Work.BoseBoxFock.Q3KernelFS K₀ F T (KzEnvAt E ρ) := by
  intro ρ hρ
  have hE0 : (0 : ℝ) ≤ E.eT := by
    rw [hv.eT_eq]; exact Work.BoseBox.fsXp_nonneg hv.t_pos.le
  have hE1 : E.eT ≤ 1 := by
    rw [hv.eT_eq]; exact Work.BoseBox.fsXp_le_one hv.t_pos hv.t_le_one (by norm_num)
  exact GateInput.toQ3KernelFS
    (gateInput_of_rows hK hv (fun p => Work.BoseBoxFock.tauSm E.eT E.s E.d E.ell p) htau
      (fun p => tauSm_nonneg _ _ _ _ hE0 hE1 p) (fun p => tauSm_even _ _ _ _ p)
      hτ hW1low hbox hα hint hq2)
    hhatChi_small hccrX_small hsum htail hform_upper hcount hsumW1sq hℓ ρ hρ

/-! ## 3. The honest row bundle and its packaging -/

/-- **The honest §11/§12 rows of the gate**, as a bundle: the τ-free bundle `KinkFS`
plus the two `P_H^q`-domination rows, the model equation and the five honest
§11/§12 rows, together with the eight τ-free rows consumed by
`GateInput.toQ3KernelFS`. -/
structure HonestRows {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (K₀ : ℝ) (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) where
  hv : FSParamsView E
  kink : KinkFS K₀ F T E
  hτ : ∀ ρ : ℝ, AdmRho E ρ → ∀ q : Mode, F.PHq E.KH E.aScat q →
    ‖F.kmom q‖ ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤ E.tau q
  hW1low : ∀ k : Mode, ‖F.kmom k‖ ≤ 1 / (4 * E.KH * E.aScat) → 0 ≤ E.W1 k
  hbox : ∀ i j : Mode, F.ccrK i j
    = Work.BoseK15.corpusBox.hatChiSq (E.ell • (F.kmom i - F.kmom j))
      - Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom i)
        * Work.BoseK15.corpusBox.hatChi (E.ell • F.kmom j)
  hα : ∀ ρ : ℝ, AdmRho E ρ → ∀ p q : Mode, F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
    |(KzEnvAt E ρ).alpha p - (KzEnvAt E ρ).alpha q|
      ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖
  hint : ∀ ρ : ℝ, AdmRho E ρ →
    |ρ * E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E, E.W1 k * (KzEnvAt E ρ).alpha k|
      ≤ K₀ * ρ * E.aScat * E.KH⁻¹
  hq2 : ∀ ρ : ℝ, AdmRho E ρ → ∀ Ψ : F.H,
    2 * ρ * E.W1omega0 * F.qw Ψ (T.Gop E)
      ≤ F.qw Ψ (F.Q2ex (KzEnvAt E ρ)) + (E.b / 400) * F.qw Ψ (T.gapOpT (KzEnvAt E ρ))
        + (1 / 2) * F.qw Ψ (F.dNumOpR (KzEnvAt E ρ)
            (fun k => rHi F E k ∧ ¬ F.PHq E.KH E.aScat k))
  hatChi_small : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * eta E
  ccrX_small : ∀ s q : Mode, E.fL s ≠ 0 → F.PHq E.KH E.aScat q → |T.ccrX s q| ≤ K₀ * eta E
  sum_hatChiSq : ∑ s ∈ excited Mode, |E.hatChiSq s| ≤ K₀
  tail_hatChiSq : ∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
    ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))
  form_upper : ∀ (S : Finset Mode) (c : Mode → ℝ) (w : Mode → F.H),
    (∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (w s') (w s))
      ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (w s) (w s)
  count_PL : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ)
    ≤ K₀ * (E.Kl * E.KL) ^ 3
  sum_W1sq : E.ell ^ (-(3 : ℝ)) *
      ∑ q ∈ (excited Mode).filter (F.PHq E.KH E.aScat), E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2
    ≤ K₀ * E.aScat

/-- The τ̃-pin at an environment whose `tau` is `tauSm`: the honest model's. -/
theorem q3KernelFS_of_rows {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : HonestRows K₀ F T E)
    (htau : ∀ k : Mode, E.tau k = Work.BoseBoxFock.tauSm E.eT E.s E.d E.ell (F.kmom k)) :
    ∀ ρ : ℝ, AdmRho E ρ → Work.BoseBoxFock.Q3KernelFS K₀ F T (KzEnvAt E ρ) :=
  q3KernelFS_tauSm htau h.hv h.kink h.hτ h.hW1low h.hbox h.hα h.hint h.hq2
    h.hatChi_small h.ccrX_small h.sum_hatChiSq h.tail_hatChiSq h.form_upper h.count_PL
    h.sum_W1sq (Work.BoseB7.ell_pos E h.hv)

/-- The τ̃-pin at the honest family. -/
theorem honE_tau {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    ∀ k : Lab (HM μ).N,
      (HonestBoxFam v h fc fu HM μ).E.tau k
        = Work.BoseBoxFock.tauSm (HonestBoxFam v h fc fu HM μ).E.eT
            (HonestBoxFam v h fc fu HM μ).E.s (HonestBoxFam v h fc fu HM μ).E.d
            (HonestBoxFam v h fc fu HM μ).E.ell
            ((HonestBoxFam v h fc fu HM μ).F.kmom k) := by
  intro k
  simp only [Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.KzEnvHon,
    Work.BoseFixR.KzEnvFs]

/-! ## 4. `HonestGateAtFS` and `HonestGateFS` -/

/-- **The honest gate at one family** (`HonestGateAtFS`), from the honest row
bundle at every admissible `μ`.  `K₀ ≥ 0` is the design's *one absolute*
constant; `b₀` is bounded by the environment's gap coefficient. -/
theorem honestGateAtFS_of_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {HM : ∀ μ : ℝ, HonestModes v μ} {ε₀ K₀ b₀ : ℝ}
    (hK₀ : 0 ≤ K₀) (hb₀ : 0 < b₀)
    (hb : ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ ε₀ →
      b₀ ≤ (HonestBoxFam v h fc fu HM μ).E.b)
    (hadm : ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ ε₀ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      AdmRho (HonestBoxFam v h fc fu HM μ).E ρ)
    (hrows : ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ ε₀ →
      HonestRows K₀ (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).T
        (HonestBoxFam v h fc fu HM μ).E) :
    HonestGateAtFS v h fc fu HM ε₀ K₀ b₀ :=
  ⟨hK₀, hb₀, hb, fun μ hμ hε ρ hρ =>
    q3KernelFS_of_rows (hrows μ hμ hε) (honE_tau HM μ) ρ (hadm μ hμ hε ρ hρ)⟩

/-- **`HonestGateFS`**: one absolute pair `(K₀, b₀)`, one diluteness threshold
`εg` and one cube-size function `Ng`, such that the corrected gate holds at
*every* honest model with `Ng μ ≤ N`. -/
theorem honestGateFS_of_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {K₀ b₀ : ℝ} (hK₀ : 0 ≤ K₀) (hb₀ : 0 < b₀)
    (Ng : ℝ → ℕ) (εg : ℝ) (hεg0 : 0 < εg) (hεg1 : εg ≤ 1)
    (hb : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ εg → b₀ ≤ (HonestBoxFam v h fc fu HM μ).E.b)
    (hadm : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ εg → ∀ ρ : ℝ, CloseCondFS v μ ρ →
        AdmRho (HonestBoxFam v h fc fu HM μ).E ρ)
    (hrows : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ εg →
        HonestRows K₀ (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).T
          (HonestBoxFam v h fc fu HM μ).E) :
    HonestGateFS v h fc fu K₀ b₀ :=
  ⟨Ng, εg, hεg0, hεg1, fun HM hN =>
    honestGateAtFS_of_rows hK₀ hb₀ (fun μ => hb HM hN μ) (fun μ => hadm HM hN μ)
      (fun μ => hrows HM hN μ)⟩

end Work.BoseGateFS
