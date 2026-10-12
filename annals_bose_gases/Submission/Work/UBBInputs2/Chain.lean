import ChallengeDeps
import Submission.Work.UBBInputs2.Bogoliubov
import Submission.Work.UBBInputs2.LocPotential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs2.Chain` — the end-to-end chains

Two routes to the paper's `hpres` (the single remaining gap of
`Submission.theorem_1_2`) are delivered here, both `sorry`-free and both
running through the DELIVERED grand-canonical interface
`Work.UBB.Consumer.hpres_of_UBB` / `Work.UBB.Consumer.hpres_of_spectralH`:

## Route H (the GC route; residual (1) is *not* needed)

```
  DLSlideCovH (FS eq:BSsliding2 at the Hamiltonian)   --(Arith)--> AprioriNPlusH
        │
        ├── LocMatricesResidual (FS §7 lem:LocMatrices) --(Arith)--> SpectralInputH
        │                                                   ▲
  BogoliubovLowH / BogoliubovWindowedH (FS §9–11) ──────────┘
                                                            │
                                        Work.UBB.UBB_of_spectralH
                                                            ▼
                          UBB v η₀  ──Consumer.hpres_of_spectralH──▶  hpres
```

Importantly, **no word/Hamiltonian dictionary is used**: FS's own normalisation
(`eq:aprioriPsi` on `⟨Ψ,H_Λ(μ)Ψ⟩`, `eq:BSsliding2`, `eq:ToProve`) *is* the
Hamiltonian one, and the corpus's grand-canonical interface consumes the
Hamiltonian box energy `boxEnergy` directly.  So residual (1) — the corpus
word ↔ `𝓗` dictionary — is *eliminated*, not assumed, on this route; this is
exactly the "grand-canonical/pressure comparison" that FS use to pass from
`thm:LHY-Box` to `thm:LHY-Background` (`eq:CompareGC`).

`LocMatricesResidual` can be replaced by `AprioriNPlusH` (FS's a-priori route,
`eq:apriorinn+`) — that is `UBB_of_DLSlideCovH` below, i.e. FS's
`thm:aprioriHLambda` step 2 followed by §9–11.

## Route W (the corpus-word route, with the canonicalised bundle)

```
  KineticLocalisation  +  BoxSumBoundCanon   --(Canonical)-->  SlidingSumData
        │                                                           │
        └──────────────────────────────────────────────▶ DLSlideCov ──▶ AprioriNPlusCov
                                                                        │
  WordBridgeResidual ──▶ Work.UBB.WordBridge                            │
                    └──────────────┬────────────────────────────────────┘
                          Work.UBB.UBB_of_inputs / hpres_of_UBB
```

Here residual (1) *is* consumed (the corpus word must be identified with `𝓗`),
as is the covariant Bogoliubov input `BogoliubovLowCov`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs2

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Route H: the Hamiltonian/grand-canonical chain -/

/-- **`UBB` from the two Hamiltonian-carrier inputs**: the a-priori `n₊` window
(FS `eq:apriorinn+`) and FS §9–11 under that window. -/
theorem UBB_of_HInputs {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ} {W : ℕ → ℝ → ℝ}
    (hv : 0 ≤ v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (ha1 : AprioriNPlusH v h J W ε₀) (ha2 : BogoliubovLowH v h J W ε₀ η₀) :
    UBB v η₀ :=
  UBB_of_spectralH hv ha hε₀ hJ (spectralInputH_of_apriori_bog ha1 ha2)

/-- **`UBB` from the sliding input and FS §9–11** (FS's own route): the sliding
inequality `eq:BSsliding2` at the Hamiltonian gives the FS window
`fsWindow v b J K_B` (`Arith.cnPlus_le_fsWindow_of_H`), which is exactly the
window the Bogoliubov input consumes. -/
theorem UBB_of_DLSlideCovH {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ η₀ : ℝ}
    (hv : 0 ≤ v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀) (hb : 0 < b)
    (hR' : 0 ≤ R') (hslide : DLSlideCovH v h b K_B R' J ε₀)
    (hBog : BogoliubovLowH v h J (fsWindow v b J K_B) ε₀ η₀) :
    UBB v η₀ :=
  UBB_of_HInputs hv ha hJ hε₀ (cnPlus_le_fsWindow_of_H ha hb hR' hslide) hBog

/-- The same with FS §9–11 in its **gain form** (the sharp `lhyC` additive over
the free background). -/
theorem UBB_of_DLSlideCovH_gain {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ η₀ : ℝ}
    (hv : 0 ≤ v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀) (hb : 0 < b)
    (hR' : 0 ≤ R') (hslide : DLSlideCovH v h b K_B R' J ε₀)
    (hBog : BogoliubovGainH v h J (fsWindow v b J K_B) ε₀ η₀) :
    UBB v η₀ :=
  UBB_of_DLSlideCovH hv ha hJ hε₀ hb hR' hslide (bogoliubovLowH_of_gainH hBog)

/-- **`UBB` from `lem:LocMatrices` and the windowed Bogoliubov bound** (FS's
actual order of steps: localise `n₊` first, then Bogoliubov).  No a-priori
window input is needed: `lem:LocMatrices` produces the window. -/
theorem UBB_of_locMatrices {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ : ℝ}
    {W : ℕ → ℝ → ℝ}
    (hv : 0 ≤ v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hLM : LocMatricesResidual v h J W ε₀ η₀)
    (hB : BogoliubovWindowedH v h J W ε₀ η₀) :
    UBB v η₀ :=
  UBB_of_spectralH hv ha hε₀ hJ (spectralInputH_of_locMatrices hLM hB)

/-- **The paper's `hpres` from the Hamiltonian-carrier inputs** (Route H, the
grand-canonical route). -/
theorem hpres_of_HInputs {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K : ℝ} {W : ℕ → ℝ → ℝ}
    (hav : 0 < a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K)
    (ha1 : AprioriNPlusH v h J W ε₀) (ha2 : BogoliubovLowH v h J W ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_spectralH hv hv1 hR hv_supp hav hε₀ hJ hη₀ hη₀le hη hηlt hK
    (spectralInputH_of_apriori_bog ha1 ha2)

/-- **The paper's `hpres` from FS's own route**: the sliding inequality
`eq:BSsliding2` (at the Hamiltonian) plus FS §9–11.  Residual (1) is not
consumed. -/
theorem hpres_of_DLSlideCovH {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K b K_B R' : ℝ}
    (hav : 0 < a v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K)
    (hb : 0 < b) (hR' : 0 ≤ R')
    (hslide : DLSlideCovH v h b K_B R' J ε₀)
    (hBog : BogoliubovLowH v h J (fsWindow v b J K_B) ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_spectralH hv hv1 hR hv_supp hav hε₀ hJ hη₀ hη₀le hη hηlt hK
    (spectralInputH_of_apriori_bog (cnPlus_le_fsWindow_of_H ha hb hR' hslide) hBog)

/-- The same with FS §9–11 in **gain form**. -/
theorem hpres_of_DLSlideCovH_gain {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K b K_B R' : ℝ}
    (hav : 0 < a v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K)
    (hb : 0 < b) (hR' : 0 ≤ R')
    (hslide : DLSlideCovH v h b K_B R' J ε₀)
    (hBog : BogoliubovGainH v h J (fsWindow v b J K_B) ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_DLSlideCovH hv hv1 hR hv_supp hav ha hJ hε₀ hη₀ hη₀le hη hηlt hK hb hR'
    hslide (bogoliubovLowH_of_gainH hBog)

/-- **The paper's `hpres` from FS's `lem:LocMatrices` route**. -/
theorem hpres_of_locMatrices {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K : ℝ} {W : ℕ → ℝ → ℝ}
    (hav : 0 < a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K)
    (hLM : LocMatricesResidual v h J W ε₀ η₀)
    (hB : BogoliubovWindowedH v h J W ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_spectralH hv hv1 hR hv_supp hav hε₀ hJ hη₀ hη₀le hη hηlt hK
    (spectralInputH_of_locMatrices hLM hB)

/-! ## 2. Route W: the corpus-word chain with the canonicalised bundle -/

/-- **`DLSlideCov` from the shared kinetic localisation and the canonicalised
bundle** — the round-1 assembly with the canonicalised `BoxSumBound`. -/
theorem dlSlideCov_of_kinetic_and_canon {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} {d M : ℕ} (hM : 1 ≤ M) (hd : (0 : ℝ) < d)
    (hloc : KineticLocalisation d b)
    (hcanon : BoxSumBoundCanon v h b K_B R' J ε₀ d M) :
    DLSlideCov v h b K_B R' J ε₀ :=
  dlSlideCov_of_localisation_and_boxSum ((kineticLocalisation_iff_slidingLocalisation d b).mp hloc)
    (boxSumBound_of_canon hM hd hcanon)

/-- **`DLSlideCov` from `lem:LocPotential`'s word comparison and the kernel
bundle** — the `hpot`-discharged variant. -/
theorem dlSlideCov_of_kinetic_and_kernel {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} {d M : ℕ} {R0 : ℝ}
    (hM : 1 ≤ M) (hd : (0 : ℝ) < d) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0)
    (hR0 : 0 < R0) (hdR : ∀ L : ℝ, 1 ≤ L → R0 ≤ (L * (d : ℝ)) / 16)
    (hdRχ : ∀ L : ℝ, 1 ≤ L → R0 ≤ L * chiR0)
    (hint : ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
      Integrable (fun p : ℝ³ × X N =>
        Work.SmallBoxSliding.qLHSBIntegrand h M L d (dens N L) (Φ : X N → ℝ) p.1 p.2))
    (hintRef : ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
      IntegrableOn (Work.SmallBoxSliding.qLHSChiIntegrand h M L d (dens N L)
        (Φ : X N → ℝ)) (abox N L))
    (hloc : KineticLocalisation d b)
    (hK : BoxSumBoundKernel v h b K_B R' J ε₀ d M) :
    DLSlideCov v h b K_B R' J ε₀ :=
  dlSlideCov_of_kinetic_and_canon hM hd hloc
    (boxSumBoundCanon_of_kernel hv_supp hR0 hM hdR hdRχ hint hintRef hK)

/-- **`UBB` from the corpus-word inputs** (Route W): the canonicalised sliding
bundle, the shared kinetic localisation, the word/Hamiltonian dictionary and the
covariant Bogoliubov input. -/
theorem UBB_of_UBBInputs2 {v : ℝ³ → ℝ} {h : ScatSol v} {J ε₀ η₀ b K_B R' : ℝ}
    {d M : ℕ}
    (hM : 1 ≤ M) (hd : (0 : ℝ) < d)
    (hv : 0 ≤ v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hb : 0 < b) (hR' : 0 ≤ R')
    (hWB : WordBridgeResidual v h)
    (hloc : KineticLocalisation d b)
    (hcanon : BoxSumBoundCanon v h b K_B R' J ε₀ d M)
    (hBog : BogoliubovLowCov v h J (fsWindow v b J K_B) ε₀ η₀) :
    UBB v η₀ := by
  have hbridge := wordBridge_of_residual hv hWB
  have hcov : DLSlideCov v h b K_B R' J ε₀ := dlSlideCov_of_kinetic_and_canon hM hd hloc hcanon
  have ha1 : AprioriNPlusCov v h J (fsWindow v b J K_B) ε₀ :=
    aprioriNPlusCov_of_dlSlideCov hb ha hR' hcov
  exact UBB_of_inputs hε₀ ha hJ hbridge (spectralInput_of_cov ha1 hBog)

/-- **The paper's `hpres` from the corpus-word inputs** (the round-1 chain with
the canonicalised sliding bundle, at `R' = 0`, the only jointly satisfiable
value — `Shape.dlSlideCov_forces_Rprime_nonpos`). -/
theorem hpres_of_UBBInputs2 {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1) {R : ℝ}
    (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K b K_B : ℝ} {d M : ℕ}
    (hM : 1 ≤ M) (hd : (0 : ℝ) < d)
    (hav : 0 < a v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K)
    (hb : 0 < b) (hKB : 0 < K_B)
    (hWB : WordBridgeResidual v h)
    (hloc : KineticLocalisation d b)
    (hcanon : BoxSumBoundCanon v h b K_B 0 J ε₀ d M)
    (hBog : BogoliubovLowCov v h J (fsWindow v b J K_B) ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  hpres_of_UBB hv hv1 hR hv_supp hav hη₀ hη₀le hη hηlt hK
    (UBB_of_UBBInputs2 hM hd hv ha hJ hε₀ hb (le_refl 0) hWB hloc hcanon hBog)


/-! ## 3. Compatibility with round 1's hypothesis list -/

/-- **The round-1 interface, re-exported**: `hpres` from round 1's residual
list (`WordBridgeResidual`, `SlidingSumData`, `BogoliubovLowCov`) — so a caller
wired to `Work.UBBInputs.hpres_of_UBBInputs_r0` can switch to this chapter
without changing the hypothesis list, while the *reduced* lists are
`hpres_of_UBBInputs2` (Route W with the canonicalised bundle),
`hpres_of_DLSlideCovH` (Route H, no dictionary) and `hpres_of_locMatrices`
(FS's own order of steps). -/
theorem hpres_of_UBBInputs2_round1 {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    {R : ℝ} (hR : 0 ≤ R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {h : ScatSol v} {J ε₀ η₀ η K b K_B : ℝ} {d M : ℕ}
    (hav : 0 < a v) (ha : 0 ≤ a v) (hJ : lhyC ≤ J) (hε₀ : 0 < ε₀)
    (hη₀ : 0 < η₀) (hη₀le : η₀ ≤ 1 / 2) (hη : 0 < η) (hηlt : η < η₀) (hK : 0 < K)
    (hb : 0 < b) (hKB : 0 < K_B)
    (hWB : WordBridgeResidual v h)
    (hslide : Work.UBBInputs.SlidingSumData v h b K_B 0 J ε₀ d M)
    (hBog : BogoliubovLowCov v h J (fsWindow v b J K_B) ε₀ η₀) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
      lhyRhs (a v) K (1 / 2 + η) ρ
        ≤ gcPressure v ρmax (8 * π * (a v) * ρ) + 8 * π * (a v) * ρ * ρ :=
  Work.UBBInputs.hpres_of_UBBInputs_r0 hv hv1 hR hv_supp hav ha hJ hε₀ hη₀ hη₀le
    hη hηlt hK hb hKB hWB hslide hBog

end Work.UBBInputs2
