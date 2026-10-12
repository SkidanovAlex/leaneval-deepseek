import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.nomRouteCubeFree
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nodeB1B_of_perBoxFNomMu` — FS `thm:aprioribounds` from the one-slot
# nominal small-box row

Lead's task (session 6, after the `eq:appTB` exponent audit): the frozen §5 node

    `Work.BoseBoxFix.NodeB1B v h J`  =  FS `eq:apriorinn+`:
      `|n − μℓ³| ≤ C₁·nWindow`  ∧  `⟨n₊⟩ ≤ C₂·nPlusWindow·‖Φ‖²`

from **`Work.BoseB1Cube.PerBoxFNomMu v h R` alone** (FS `thm:smallbox` at the sliding box, nominal
spelling, one chemical-potential slot).  With it the root's `hB1` needs only `PerBoxFNomMu`, and both
`cubePerBox_holds` and `Work.BoseB1Cube.cubeCrudeBand_holds` leave the path.

## The decomposition used here

`NodeB1B`'s two conjuncts are named separately:

* `ParticleWindowMu` — the **sharp particle window**.  This is the content of FS's proof of
  `thm:aprioriHLambda` after `eq:aprioriRn+` (`final_v2.tex` l.4136–4190): the convexity step
  `eq:Rconvex`, the auxiliary potential `U(z) = C⁻¹∫_{I₋}(∬w_{1,B(u)})/|B(u)|·1_{B(u)}(z)du`, its two
  bounds (`U ≤ Cℓ⁻³`, `P_ΛUP_Λ = ℓ⁻³P_Λ`), the `P/Q` splitting `A ≥ (1−ε)PAP − ε⁻¹QAQ` and the
  choice `ε = K_B^{3/2}K_ℓ(μa³)^{1/4}`.  Every ingredient is on disk in the *nominal* spelling —
  `Work.BoseB1Cube.nomJensen_integrated` / `nomJensen_dens` (the pointwise Jensen
  `‖Φ‖²ψ(1,μ,nomDens(u)) ≤ nomBoxInner`), `Work.BoseB1Cube.ledgerNom` + `nomCountAbsorb`
  (`eq:aprioriRn+` and the cancellation against the low-state background),
  `Work.BoseB1Cube.countWindowOfNominal` (the one-sided count window), the convexity of
  `ψ(1,μ,·)` on `[0,∞)` — so this is a self-contained nominal assembly, **DELEGATED** as
  `Submission.Work.BoseB1Cube.particleWindowMu`.
* `NPlusWindowMu` — the **excited-particle window**, PROVED below
  (`nPlusWindowMu_of_perBoxFNomMu`): a short consequence of the ledger's gap row and the one-sided
  count window, using the PROVED `μ·(a v)·ℓ² = K_ℓ²`.

The final assembly is `nodeB1B_of_windows`; `nodeB1B_of_particleWindowMu` is the lead's requested
statement with the delegated sharp window taken as an explicit hypothesis (once that child lands,
the hypothesis is discharged and the statement is unconditional).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The two windows, named -/

/-- **The sharp particle window of FS `eq:apriorinn+`** (first conjunct), from the one-slot nominal
small-box row.  `Work.BoseBox.nWindow` is FS's `K_B^{3/2}K_ℓ(μa³)^{1/4}μℓ³`. -/
def ParticleWindowMu (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧
    ∀ (J : ℝ) (μ : ℝ), Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        0 < normB v μ n (Φ : X n → ℝ) → IsLowB v h J μ n Φ →
        |(n : ℝ) - μ * (sideAt μ (a v)) ^ 3|
          ≤ C₁ * Work.BoseBox.nWindow (paramsAt μ (a v)) μ (a v)

/-- **The excited-particle window of FS `eq:apriorinn+`** (second conjunct), from the one-slot
nominal small-box row.  `Work.BoseBox.nPlusWindow` is FS's `K_B³K_ℓ²(μa³)^{1/2}μℓ³`. -/
def NPlusWindowMu (v : E3 → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ C₂ : ℝ, 0 < ε₀ ∧ 0 ≤ C₂ ∧
    ∀ (J : ℝ) (μ : ℝ), Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        0 < normB v μ n (Φ : X n → ℝ) → IsLowB v h J μ n Φ →
        Submission.BoseGases.cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          ≤ C₂ * Work.BoseBox.nPlusWindow (paramsAt μ (a v)) μ (a v)
              * normB v μ n (Φ : X n → ℝ)

/-! ## 2. The excited window, from the ledger and the count window -/

/-- **`NPlusWindowMu` from `PerBoxFNomMu`.**

The nominal ledger (`Work.BoseB1Cube.ledgerNom`, `E = 1`) gives the gap row

    `(b/(2ℓ²))·⟨n₊⟩ ≤ C_A·(μ²aℓ³κ)·‖Φ‖² + (μaκ)·n·‖Φ‖²`      (`κ = K_B³(μa³)^{1/2}`),

and the one-sided count window (`countWindowOf_perBoxFNomSlots`, PROVED) is `n ≤ C·μℓ³`, so
`(μaκ)·n·‖Φ‖² ≤ C·(μ²aℓ³κ)·‖Φ‖²`.  Dividing by `b/(2ℓ²)` and using the PROVED
`μ·(a v)·ℓ² = K_ℓ²` gives exactly `C₂·nPlusWindow·‖Φ‖²`, `C₂ = 2(C_A + C)/b`. -/
theorem nPlusWindowMu_of_perBoxFNomMu {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v)
    (hMu : PerBoxFNomMu v h R) : NPlusWindowMu v h R := by
  obtain ⟨εμ, c₁, C, hεμ, hc₁, hC, hrowμ⟩ := hMu
  -- the two-slot row (definitionally `PerBoxFNomSlots`)
  have hperS : PerBoxFNomSlots v h R :=
    perBoxFNomSlots_of_perBoxFNomMu h hv hvrad hR hv_supp
      ⟨εμ, c₁, C, hεμ, hc₁, hC, hrowμ⟩
  obtain ⟨ε₀', c₁', C', hε₀', hc₁', hC', hbody⟩ := hperS
  have hperS' : PerBoxFNomSlots v h R := ⟨ε₀', c₁', C', hε₀', hc₁', hC', hbody⟩
  have hS : SlidingGoodCube v h := slidingGoodCube h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εL, CA, hεL, hCA0, hled⟩ :=
    ledgerNom (v := v) (h := h) (R := R) hv hv1 hvrad hR hv_supp hav
      (c₁ := c₁') (C := C') (E := 1) hc₁' hC' one_pos ⟨ε₀', hε₀', hbody⟩ hS
  obtain ⟨εW, CW, hεW, hCW0, hwin⟩ :=
    countWindow_of_perBoxFNomSlots h hv hv1 hvrad hR hv_supp hav hS hperS'
  refine ⟨min εL εW, 2 * (CA + 1 * CW) / Work.BoseBox.bValue, lt_min hεL hεW, ?_, ?_⟩
  · have hb : (0 : ℝ) < Work.BoseBox.bValue := by norm_num [Work.BoseBox.bValue]
    exact div_nonneg (by positivity) hb.le
  · intro J μ hAdm hJK n Φ hNB hlow
    have hμ : 0 < μ := adm_mu_pos hAdm
    have hav0 : 0 ≤ a v := (adm_a_pos hAdm).le
    have hℓ : 0 < sideAt μ (a v) := adm_ell_pos hAdm
    have hb : (0 : ℝ) < (paramsAt μ (a v)).b := paramsAt_b_pos μ (a v)
    have hN : 0 ≤ normB v μ n (Φ : X n → ℝ) := by
      rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      exact integral_nonneg fun x => sq_nonneg _
    have hKB : 0 ≤ (paramsAt μ (a v)).KB := by
      rw [KB_eq_fsXp μ (a v)]
      exact Work.BoseBox.fsXp_nonneg (t := μ * (a v) ^ 3) (c := -6) (by positivity)
    have hκ : 0 ≤ kappa v μ := by
      unfold kappa
      exact mul_nonneg (pow_nonneg hKB 3) (Real.rpow_nonneg (by positivity) _)
    have hD : 0 ≤ μ ^ 2 * (a v) * (sideAt μ (a v)) ^ 3 * kappa v μ :=
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav0) (pow_nonneg hℓ.le 3)) hκ
    have hAdmL : Adm v εL μ := Adm.mono hAdm (min_le_left _ _)
    have hAdmW : Adm v εW μ := Adm.mono hAdm (min_le_right _ _)
    obtain ⟨-, hgap⟩ := hled J μ hAdmL hJK n Φ hNB hlow
    have hn : (n : ℝ) ≤ CW * μ * (sideAt μ (a v)) ^ 3 := hwin J μ hAdmW hJK n Φ hNB hlow
    have hrow2 : (1 * (μ * a v * kappa v μ)) * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
        ≤ CW * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := by
      have h1 : (1 * (μ * a v * kappa v μ)) * (n : ℝ)
          ≤ (μ * a v * kappa v μ) * (CW * μ * (sideAt μ (a v)) ^ 3) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hn (mul_nonneg (mul_nonneg hμ.le hav0) hκ)
      calc (1 * (μ * a v * kappa v μ)) * (n : ℝ) * normB v μ n (Φ : X n → ℝ)
          ≤ ((μ * a v * kappa v μ) * (CW * μ * (sideAt μ (a v)) ^ 3))
              * normB v μ n (Φ : X n → ℝ) := mul_le_mul_of_nonneg_right h1 hN
        _ = CW * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ) := by ring
    have hmain : (paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2)
          * Submission.BoseGases.cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ (CA + 1 * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
            * normB v μ n (Φ : X n → ℝ) := by
      have hsum : CA * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ)
            + CW * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ)
          = (CA + 1 * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
              * normB v μ n (Φ : X n → ℝ) := by ring
      linarith [hgap, hrow2, hsum]
    -- divide by `b/(2ℓ²)`
    have hstep : Submission.BoseGases.cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
        ≤ (2 * (sideAt μ (a v)) ^ 2 / (paramsAt μ (a v)).b)
            * ((CA + 1 * CW) * (μ ^ 2 * a v * (sideAt μ (a v)) ^ 3 * kappa v μ)
                * normB v μ n (Φ : X n → ℝ)) := by
      have hne : (0 : ℝ) < 2 * (sideAt μ (a v)) ^ 2 / (paramsAt μ (a v)).b := by positivity
      have h2 := mul_le_mul_of_nonneg_left hmain hne.le
      have heq : (2 * (sideAt μ (a v)) ^ 2 / (paramsAt μ (a v)).b)
            * ((paramsAt μ (a v)).b / (2 * (sideAt μ (a v)) ^ 2)
              * Submission.BoseGases.cnPlus (sideAt μ (a v)) (Φ : X n → ℝ))
          = Submission.BoseGases.cnPlus (sideAt μ (a v)) (Φ : X n → ℝ) := by
        field_simp
      linarith [h2, heq.le, heq.ge]
    refine le_trans hstep (le_of_eq ?_)
    have hKl : μ * a v * (sideAt μ (a v)) ^ 2 = (paramsAt μ (a v)).Kl ^ 2 :=
      mu_mul_a_mul_ell_sq μ (a v) hμ hav
    have hk : kappa v μ
        = (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) := rfl
    rw [hk, Work.BoseBox.nPlusWindow, ← hKl, ← Work.BoseBox.sideAt,
      Work.BoseFixB1.paramsAt_b_eq μ (a v)]
    ring_nf

/-! ## 3. The assembly -/

/-- **`Work.BoseBoxFix.NodeB1B v h J` from the two windows** — the `ε₀`'s are combined by `min`; no
`lhyC ≤ J` hypothesis is needed by either window. -/
theorem nodeB1B_of_windows {v : E3 → ℝ} {h : ScatSol v} {R J : ℝ}
    (hp : ParticleWindowMu v h R) (hn : NPlusWindowMu v h R) :
    Work.BoseBoxFix.NodeB1B v h J := by
  obtain ⟨εp, C₁, hεp, hC₁, hpw⟩ := hp
  obtain ⟨εn, C₂, hεn, hC₂, hnw⟩ := hn
  refine ⟨C₁, C₂, min εp εn, hC₁, hC₂, lt_min hεp hεn, ?_⟩
  intro μ hAdm hJK n Φ hNB hlow
  exact ⟨hpw J μ (Adm.mono hAdm (min_le_left _ _)) hJK n Φ hNB hlow,
    hnw J μ (Adm.mono hAdm (min_le_right _ _)) hJK n Φ hNB hlow⟩

/-- **The lead's requested statement**, with the delegated sharp window `particleWindowMu` as the
only missing input (the excited window is PROVED above). -/
theorem nodeB1B_of_particleWindowMu {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v) {J : ℝ}
    (hp : ParticleWindowMu v h R) (hMu : PerBoxFNomMu v h R) :
    Work.BoseBoxFix.NodeB1B v h J :=
  nodeB1B_of_windows hp (nPlusWindowMu_of_perBoxFNomMu h hv hv1 hvrad hR hv_supp hav hMu)

end Work.BoseB1Cube
