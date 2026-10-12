import ChallengeDeps
import Submission.Work.BoseGateFS.KinkFSHonest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.GateThresholds` — the small-parameter bundle of the node

The node's remaining arithmetic: an explicit cube-size function `Ng` and an
explicit diluteness `εg ≤ 1` such that, for every honest mode choice `HM` with
`N ≥ Ng μ` and every `0 < μ` with `μa³ ≤ εg`, all the *threshold* conditions used
by the honest row derivations hold.  They are exactly FS's parameter conditions
(`sec:params`) instantiated at `t = μa³`:

* the **cube conditions** (`Ng`): `Λ_N ≥ 1`, `Λ_N ≥ 1/(4K_Ha)`,
  `4K_L√(μa) ≤ Λ_N` (design §2.3), and the no-wrap condition
  `ℓ(2K_L√(μa) + 2Λ_N)/(2π) ≤ N` (`LabAdd`/`HonRowsDecay`);
* the **diluteness conditions** (`εg`): `1 ≤ ℓ`, `1 ≤ K_Ha`, `R ≤ 2K_Ha`,
  `R ≤ ℓχ_{R₀}`, `ε_T ≤ 1/2`, `(μa³)^{3/323} ≤ 1/2`,
  `(2 d s ℓ)⁻¹ ≤ (4K_Ha)⁻¹` (the τ̃-Lipschitz régime `tauTilde_lip`),
  `3((1-ε_T)(2sℓ)⁻¹ + ε_T(2dsℓ)⁻¹) ≤ (4K_Ha)⁻¹` (same), and the two χ-rows'
  régime `K_L√(μa)·K_Ha ≤ 1/16` (`honE_ccrX_small`), `K_Ha/(sℓ) ≤ 1/32`
  (`exists_hon_tau`).

Everything is monotone in `εg` (`GateThresholds.mono`): shrinking `εg` preserves
every field, which is how the node folds its internally produced thresholds
(`tGe` of `exists_hon_tau`) into the caller's `εg`.

No `sorry`, no `axiom`.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

/-- **The node's small-parameter bundle.** -/
structure GateThresholds (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v)
    (fc fu : LowCut) (R : ℝ) where
  Ng : ℝ → ℕ
  εg : ℝ
  pos : 0 < εg
  le_one : εg ≤ 1
  /-- the cube conditions, `Ng`-controlled -/
  cube : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
    ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ εg →
      (1 ≤ uvRad (ellH v μ) (HM μ).N)
      ∧ (1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
          ≤ uvRad (ellH v μ) (HM μ).N)
      ∧ (4 * ((honE v h fc fu HM μ).KL
            * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))
          ≤ uvRad (ellH v μ) (HM μ).N)
      ∧ (ellH v μ * (2 * ((honE v h fc fu HM μ).KL
              * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))
            + 2 * uvRad (ellH v μ) (HM μ).N) / (2 * Real.pi) ≤ ((HM μ).N : ℝ))
  /-- the diluteness conditions, `εg`-controlled: exactly the rows that
  `exists_honestGateFS_of_fsRows` consumes — `1 ≤ ℓ`, the two régime rows of
  `honE_W1low` (`R ≤ 2K_Ha`, `R ≤ ℓχ_{R₀}`), the close window of
  `adm_of_closeCond'` (`(μa³)^{3/323} ≤ 1/2`), the χ-régime row of
  `honE_ccrX_small` (`K_L√(μa)·K_Ha ≤ 1/16`) and the smallness row of
  `exists_hon_tau` (`K_Ha/(sℓ) ≤ 1/32`). -/
  dil : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
    ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ εg →
      (1 ≤ ellH v μ)
      ∧ (R ≤ 2 * ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat))
      ∧ (R ≤ ellH v μ * Submission.BoseGases.chiR0)
      ∧ ((Work.BoseFixR.dil v μ) ^ (3 / 323 : ℝ) ≤ 1 / 2)
      ∧ ((honE v h fc fu HM μ).KL
            * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)
          * ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) ≤ 1 / 16)
      ∧ ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat
          / ((honE v h fc fu HM μ).s * (honE v h fc fu HM μ).ell) ≤ 1 / 32)
  /-- the `τ̃`-Lipschitz régime (`tauTilde_lip`), `ε_T`-controlled: it exhibits
  `ρ₀ = 1/(4K_Ha)` as an admissible lower threshold, which is what turns the
  kinetic symbol's Lipschitz row into the K3 row `alpha_lip` at the honest model
  (`(2 d s ℓ)⁻¹ ≤ (1/4)(4K_Ha)⁻¹` gives `(d s ℓ)⁻¹ ≤ ρ₀` and
  `3((1-ε_T)(2sℓ)⁻¹ + ε_T(2dsℓ)⁻¹) ≤ ρ₀`). -/
  dilTau : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
    ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ εg →
      (2 * (honE v h fc fu HM μ).d * (honE v h fc fu HM μ).s
          * (honE v h fc fu HM μ).ell)⁻¹
        ≤ (1 / 4) * (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)⁻¹
  /-- the régime `K_H a ≥ 1` of the per-mode bounds (`Work.BoseGateFS.perMode_bounds_le`,
  hence `alpha_lip_abs2`'s `hKHa`): it is the smallness `t^{549/1292} ≤ a v`, which holds
  for small diluteness. -/
  dilKH : ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
    ∀ μ : ℝ, 0 < μ → μ * a v ^ 3 ≤ εg →
      1 ≤ (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat

/-- **Monotonicity of the bundle in `εg`**: every field is a
`∀ μ, 0 < μ → μa³ ≤ εg → P μ` statement with `εg` only in the antecedent, so
shrinking `εg` preserves all of them. -/
def GateThresholds.mono {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {R : ℝ} (H : GateThresholds v h fc fu R) {εg' : ℝ}
    (h0 : 0 < εg') (hε : εg' ≤ H.εg) : GateThresholds v h fc fu R where
  Ng := H.Ng
  εg := εg'
  pos := h0
  le_one := le_trans hε H.le_one
  cube := fun HM hN μ hμ hμ' => H.cube HM hN μ hμ (le_trans hμ' hε)
  dil := fun HM hN μ hμ hμ' => H.dil HM hN μ hμ (le_trans hμ' hε)
  dilTau := fun HM hN μ hμ hμ' => H.dilTau HM hN μ hμ (le_trans hμ' hε)
  dilKH := fun HM hN μ hμ hμ' => H.dilKH HM hN μ hμ (le_trans hμ' hε)

end Work.BoseGateFS
