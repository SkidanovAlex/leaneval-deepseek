import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.slidingBogPortPrescribedEps
import Submission.Work.BoseFixB1S.chiMass_le_const_mul_boxMass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.slidingBogPortCubeContDiff` — the carrier-free sharp port at the
# cube window, in the **clash-free import cone**

**Provenance.**  This is a copy of
`Submission/Work/BoseB1Cube/slidingBogPortPrescribedEpsSmallBContDiff.lean` (the carrier-free
`chiSmallB`-window form of FS `lm:appabogolubov` / `eq:simpleaprioribog` with the mass constant
prescribed) with exactly **one** change: the import of
`Submission.Work.BoseFixB1S.SharpAIGood` is dropped.

**Why the copy exists (a cone constraint, not new mathematics).**  The duplicate declaration
`Work.BoseFixB1S.goodState_finset_sum` (in both `BoseFixB1S/exclFunOpAux.lean` and
`BoseFixB1S/boxQCount_eq_sum_compT.lean`, see `NOTE_to_lead_dupGoodState.md`) splits the corpus's
import graph into two cones.  The per-size chapter's vocabulary (`Work.BoseB1Cube.cubeSmallNArb`,
whose cone contains `exclFunOpAux`) therefore **cannot** be loaded together with `SharpAIGood`
(machine-checked: `import Submission.Work.BoseB1Cube.cubeSmallNArb` together with
`import Submission.Work.BoseFixB1S.SharpAIGood` hard-errors at import time).  The theorem below uses
none of `SharpAIGood`'s declarations, so dropping the import keeps the proof intact while making the
statement importable in the per-size chapter's cone.  This is the same workaround the corpus already
uses for the payment (`BoseB1Cube/sharpJointCoreSelf`, `BoseB1Cube/paySurplusSlotFree`) and for the
slot telescopes.

**Statement.**  Identical to `Work.BoseB1Cube.slidingBogPortPrescribedEpsSmallBContDiff` (renamed
here to `slidingBogPortCubeContDiff`); see that file's docstring for the mathematics (FS
`eq:simpleaprioribog`: the pairing `bA2` plus the cube-windowed sliding spectral word
`bSpectralCube` dominate the credit
`-½(1+eps)·ĝω(0)·((n+1)n/V²)·‖Φ‖²·χmass - C·a·(μ+n/V)·n₊ - C·a·μ·‖Φ‖²`), and for the proof (the
`chiSmallB` re-run of the prescribed-`ε` chain).
-/


/-!
# `Work.BoseB1Cube.slidingBogPortCubeContDiff`

The **carrier-free** form of FS `lm:appbogolubov` / `eq:simpleaprioribog` at the sliding box in
the cube-windowed (`chiSmallB`) vocabulary: the twin of the PROVED
`Work.BoseFixB1B.slidingBogPortPrescribedEpsSmallB` in which the state class
`Work.BoseKinLoc.BoxState n ℓ` is replaced by the *arithmetic* carrier of FS's box-energy infimum,
a plain function `Φ : X n → ℝ` with `ContDiff ℝ ⊤ Φ` (no permutation symmetry, no nonvanishing).

Why the carrier must change: FS's descent `n = m n' + n''` slices the big state along a block
(`Work.BoseB1Cube.sbWordCube_descent_atSizes`), and the slices are `ContDiff` but not
permutation-invariant; `BoxState`'s `symm`/`nezero` fields are **unused** in the port's proof
(see `Submission/Work/BoseB1Cube/NOTE_to_lead_stateClass.md`), so re-running the chain verbatim at
the weaker carrier produces this theorem.

The proof is the proof of `slidingBogPortPrescribedEpsSmallB` with the two carrier-only edits:
the smoothness field `Φ.contDiff` becomes the hypothesis `hΦ : ContDiff ℝ ⊤ Φ`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal ContDiff

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.SmallBoxSliding Work.BoseBoxFix
  Work.BoseFixB1 Work.BoseFixB1S

theorem slidingBogPortCubeContDiff {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {eps : ℝ} (heps : 0 < eps) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          ContDiff ℝ (⊤ : ℕ∞) Φ →
          -((1 / 2) * ((1 + eps) * Submission.BoseGases.g0w0Mass h)
                * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
                * Work.BoseFixB1.bI v μ Φ
                * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
                    (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
              + C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
                  * Work.BoseFixB1.bQ v μ Φ u
              + C * (_root_.BoseGases.a v) * μ * Work.BoseFixB1.bI v μ Φ)
            ≤ Work.BoseFixB1S.bSpectralCube v μ Φ u
              + Work.BoseFixB1.bA2 v h μ Φ u := by
  classical
  obtain ⟨Kc, hKc0, hKcbound⟩ :=
    Work.BoseFixB1S.nuPairWNuIntegrable (v := v) h hv hv1 hvrad hR hv_supp hav
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨K1s, hK1s0, hK1sh⟩ :=
    Work.BoseFixB1S.slidingNewtonMassSharpB1 (v := v) (R := R) hv_supp hR hv hvrad hv1 h
      (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  obtain ⟨ε₁, hε₁pos, hreg⟩ :=
    Work.BoseFixB1S.admGoodSetRegime2 (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₃, hε₃pos, hε₃⟩ := Work.BoseFixGlue.Pot.ellB_ge (v := v) hav hR
  obtain ⟨ε₂, hε₂pos, hsmall⟩ :=
    Work.BoseFixB1B.exists_eps_twoFactorSmall (v := v) h hv hvrad hR hv_supp hav (eps := min eps 1 / 32) (K := K1s)
      (by positivity) hK1s0
  set D : ℝ := Submission.BoseGases.g0w0Mass (v := v) h with hDdef
  have hDpos : 0 < D := by
    rw [hDdef, ← Work.BoseFixB1B.PairMass_eq_g0w0Mass]
    exact Work.BoseFixB1B.pairMass_pos h hR hv hv1 hvrad hv_supp hav
  set δ : ℝ := min (1 / 2) (min eps 1 / 256) with hδdef
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδle : δ ≤ 1 / 2 := min_le_left _ _
  have hδsmall : 8 * δ ≤ min eps 1 / 32 := by
    have h : δ ≤ min eps 1 / 256 := min_le_right _ _
    linarith
  set θ : ℝ := min (1 / 4) (eps / (8 * (1 + eps))) with hθdef
  have hθpos : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθle : θ ≤ 1 / 2 := le_trans (min_le_left _ _) (by norm_num)
  have hθsmall : 1 + 3 * eps / 4 ≤ (1 - θ) * (1 + eps) := by
    have h1 : θ ≤ eps / (8 * (1 + eps)) := min_le_right _ _
    have h2 : (0:ℝ) < 1 + eps := by linarith
    have h3 : θ * (1 + eps) ≤ eps / 8 := by
      have h4 : (eps / (8 * (1 + eps))) * (1 + eps) = eps / 8 := by field_simp
      rw [← h4]
      exact mul_le_mul_of_nonneg_right h1 h2.le
    nlinarith [h3]
  set Ks : ℝ := max 1 (max (Kc / 2) (4 * Kc / min eps 1)) with hKsdef
  have hKs0 : 0 < Ks := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKsKc : Kc ≤ 2 * Ks := by
    have h1 : Kc / 2 ≤ Ks := le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  have hτ2 : Kc ^ 2 / (4 * Ks ^ 2) ≤ min eps 1 / 32 := by
    by_cases hKcz : Kc = 0
    · rw [hKcz, zero_pow (by norm_num : 2 ≠ 0), zero_div]
      exact div_nonneg (le_of_lt (lt_min heps one_pos)) (by norm_num)
    have hKcpos : 0 < Kc := lt_of_le_of_ne hKc0 (Ne.symm hKcz)
    have hKsge : 4 * Kc / min eps 1 ≤ Ks := le_trans (le_max_right _ _) (le_max_right _ _)
    have hminpos : 0 < min eps 1 := lt_min heps one_pos
    have h1 : Kc / (2 * Ks) ≤ min eps 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      rw [div_le_iff₀ hminpos] at hKsge
      nlinarith [hKsge]
    have h2 : 0 ≤ Kc / (2 * Ks) := by positivity
    have h3 : (Kc / (2 * Ks)) ^ 2 ≤ (min eps 1 / 8) ^ 2 := by
      exact pow_le_pow_left₀ h2 h1 2
    have h4 : (min eps 1 / 8) ^ 2 ≤ min eps 1 / 32 := by
      have h5 : min eps 1 ≤ 1 := min_le_right _ _
      have h7 : 0 < min eps 1 := hminpos
      nlinarith [h5, h7]
    have h8 : Kc ^ 2 / (4 * Ks ^ 2) = (Kc / (2 * Ks)) ^ 2 := by field_simp; ring
    rw [h8]
    linarith [h3, h4]
  set c0 : ℝ := (1 + eps) * D with hc0def
  have hc0pos : 0 < c0 := by rw [hc0def]; positivity
  set κ : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay
    Work.BoseBox.mValue with hκdef
  have hκ0 : 0 ≤ κ := mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
    (Submission.BoseGases.chiSmallDecay_nonneg _)
  set Kx : ℝ := max 1 (κ ^ 2) with hKxdef
  have hKxge1 : (1 : ℝ) ≤ Kx := le_max_left _ _
  have hKxpos : 0 < Kx := lt_of_lt_of_le zero_lt_one hKxge1
  have hκsq : κ ^ 2 ≤ Kx := le_max_right _ _
  set Ch : ℝ := 8 * (Kc ^ 4 * (_root_.BoseGases.a v)
    / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ)) with hChdef
  have hCh0 : 0 ≤ Ch := by
    rw [hChdef]
    refine mul_nonneg (by norm_num) ?_
    refine div_nonneg (mul_nonneg (pow_nonneg hKc0 4) hav.le) ?_
    positivity
  have hChcred : 8 * (Kc ^ 4 * (_root_.BoseGases.a v)
      / (576 * Real.pi ^ 4 * Ks ^ 2 * δ ^ 6 * c0 * θ)) ≤ Ch := hChdef.symm.le
  set C : ℝ := max (4 * Ks * κ ^ 2) (Ch * Kx) with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    have h4Ks : (0 : ℝ) ≤ 4 * Ks := by linarith [hKs0]
    exact le_trans (mul_nonneg h4Ks (sq_nonneg κ)) (le_max_left _ _)
  have hCCh : Ch * Kx ≤ C := le_max_right _ _
  have hτ1 : Kc ^ 2 / (4 * Ks ^ 2) ≤ 1 :=
    le_trans hτ2 (by have h := min_le_right eps 1; linarith)
  have hCκ : 4 * Ks * κ ^ 2 ≤ C := le_max_left _ _
  refine ⟨min (min ε₁ ε₂) (min ε₃ 1), C, lt_min (lt_min hε₁pos hε₂pos) (lt_min hε₃pos one_pos),
    hC0, ?_⟩
  intro μ hAdm n Φ u hu hΦ
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (le_trans (min_le_left _ _) (min_le_left _ _)), hAdm.2.2⟩
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (le_trans (min_le_left _ _) (min_le_right _ _)), hAdm.2.2⟩
  have hAdm₃ : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₃ :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _))
  obtain ⟨h16R, h16Rd, hdpos, hdle1, hVpos, hVcube, hVside, hmuV⟩ := hreg μ hAdm₁ u hu
  have hℓpos : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hμpos : 0 < μ := hAdm.1
  have hμa3le : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsm := hsmall μ hAdm₂
  have hInn : 0 ≤ Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.bI_nonneg v μ _
  have hχMnn : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ u
  have hD0 : 0 ≤ Submission.BoseGases.g0w0Mass (v := v) h := le_of_lt hDpos
  by_cases hn1 : n ≤ 1
  · have hA2z : Work.BoseFixB1.bA2 v h μ (Φ : Submission.BoseGases.X n → ℝ) u = 0 := by
      rw [Work.BoseFixB1.bA2, Work.BoseFixB1.boxA2]
      refine Finset.sum_eq_zero (fun p hp => ?_)
      exfalso
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      exact hne (Fin.ext (by omega))
    have h1 : 0 ≤ (1 / 2 : ℝ) * ((1 + eps) * Submission.BoseGases.g0w0Mass (v := v) h)
        * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
        * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
        * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u := by
      have h2 : 0 ≤ (1 + eps) * Submission.BoseGases.g0w0Mass (v := v) h :=
        mul_nonneg (by linarith [heps]) hD0
      have h3 : 0 ≤ ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2) := by positivity
      have h4 : 0 ≤ (1 / 2 : ℝ) * ((1 + eps) * Submission.BoseGases.g0w0Mass (v := v) h) :=
        mul_nonneg (by norm_num) h2
      exact mul_nonneg (mul_nonneg (mul_nonneg h4 h3) hInn) hχMnn
    have h5 : 0 ≤ Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
      rw [Work.BoseFixB1S.bSpectralCube]
      exact Work.BoseFixB1.tBwordKinInd_nonneg _
    have h6 : 0 ≤ C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
        * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
      have hμn : 0 ≤ μ + (n : ℝ) / Work.BoseFixB1.bV v μ u :=
        add_nonneg hμpos.le (div_nonneg (Nat.cast_nonneg n) hVpos.le)
      have hQ : 0 ≤ Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u :=
        Work.BoseFixB1.bQ_nonneg v μ _ u
      exact mul_nonneg (mul_nonneg (mul_nonneg hC0 hav.le) hμn) hQ
    have h7 : 0 ≤ C * (_root_.BoseGases.a v) * μ
        * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 hav.le) hμpos.le) hInn
    rw [hA2z]
    linarith
  · have hn2 : 2 ≤ n := by omega
    by_cases hI0 : Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) = 0
    · obtain ⟨_hflat0, hQ0, hA20⟩ :=
        Work.BoseFixB1.boxWords_eq_zero_of_bI_eq_zero (h := h) hΦ hI0
      have hspec : 0 ≤ Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
        rw [Work.BoseFixB1S.bSpectralCube]
        exact Work.BoseFixB1.tBwordKinInd_nonneg _
      have h1 : (1 / 2 : ℝ) * ((1 + eps) * Submission.BoseGases.g0w0Mass (v := v) h)
          * ((((n : ℝ) + 1) * (n : ℝ)) / (Work.BoseFixB1.bV v μ u) ^ 2)
          * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u = 0 := by
        rw [hI0]; ring
      have h4 : C * (_root_.BoseGases.a v) * (μ + (n : ℝ) / Work.BoseFixB1.bV v μ u)
          * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X n → ℝ) u = 0 := by rw [hQ0]; ring
      have h5 : C * (_root_.BoseGases.a v) * μ
          * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) = 0 := by rw [hI0]; ring
      rw [hA20, h1, h4, h5]
      linarith [hspec]
    · -- ## the main case
      have hIpos : 0 < Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X n → ℝ) :=
        lt_of_le_of_ne hInn (Ne.symm hI0)
      obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.cast_add, Nat.cast_one]
      -- ### the normalisation `Ψ := Φ/√(∫Φ²)`
      set t : ℝ := Real.sqrt (Work.BoseFixB1.bI v μ
        (Φ : Submission.BoseGases.X (N + 1) → ℝ)) with ht
      have htpos : 0 < t := Real.sqrt_pos.mpr hIpos
      have ht2 : t ^ 2 = Work.BoseFixB1.bI v μ
          (Φ : Submission.BoseGases.X (N + 1) → ℝ) := Real.sq_sqrt hInn
      have htne : t ≠ 0 := ne_of_gt htpos
      set Ψ : Submission.BoseGases.X (N + 1) → ℝ := fun x => t⁻¹ * Φ x with hΨdef
      have hΦeq : (Φ : Submission.BoseGases.X (N + 1) → ℝ) = fun x => t * Ψ x := by
        funext x; rw [hΨdef]; field_simp
      have hΨcd : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
        rw [hΨdef]; exact hΦ.const_smul t⁻¹
      have hbIval : Work.BoseFixB1.bI v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) = 1 := by
        have hstep : (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
            (fun x => t * Ψ x) x ^ 2)
            = t ^ 2 * (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
                (Ψ x) ^ 2) := by
          rw [← MeasureTheory.integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          ring
        have h2 : (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
            (Φ : Submission.BoseGases.X (N + 1) → ℝ) x ^ 2) = t ^ 2 := by
          change Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) = t ^ 2
          exact ht2.symm
        rw [← hΦeq, h2] at hstep
        have h3 : t ^ 2 * (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
            (Ψ x) ^ 2) = t ^ 2 * 1 := by rw [← hstep, mul_one]
        have h4 := mul_left_cancel₀ (pow_ne_zero 2 htne) h3
        change (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
          (Ψ x) ^ 2) = 1 at h4
        exact h4
      have hnormΨ : (∫ x in Submission.BoseGases.abox (N + 1) (Work.BoseFixB1.bSide v μ),
          (Ψ x) ^ 2) = 1 := by rw [← hbIval, Work.BoseFixB1.bI]
      -- ### the sliding data
      set ℓ : ℝ := Work.BoseFixB1.bSide v μ with hℓdef
      set dd : ℝ := Work.BoseFixB1.bD v μ with hddef
      set V : ℝ := Work.BoseFixB1.bV v μ u with hVdef
      set A : Set E3 := Work.BoseFixB1.bA v μ u with hAdef
      set Mv : ℕ := Work.BoseFixB1.bM v μ with hMvdef
      set χ : E3 → ℝ := Submission.BoseGases.chiSmallB Mv ℓ dd u with hχdef
      set 𝒲 : E3 → ℝ := Work.BoseFixB1B.wSmallInner Mv ℓ dd (Submission.BoseGases.g0 v h)
        with h𝒲def
      set c : ℝ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v) with hcdef
      set Xw : ℝ := ∫ z : E3, (χ z) ^ 2 with hXwdef
      set Xp : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).X with hXpdef
      have hMv48 : Mv = Work.BoseBox.mValue := by rw [hMvdef]; rfl
      have hℓpos' : 0 < ℓ := by rw [hℓdef]; exact hℓpos
      have hdpos' : 0 < dd := by rw [hddef]; exact hdpos
      have hdle1' : dd ≤ 1 := by rw [hddef]; exact hdle1
      have hVpos' : 0 < V := by rw [hVdef]; exact hVpos
      have hcpos : 0 < c := by rw [hcdef]; exact Work.BoseFixB1S.sbCut_pos hμpos hav
      have hAmeas : MeasurableSet A := by
        show MeasurableSet (Submission.BoseGases.dlBox ℓ dd u)
        exact Work.SmallBoxSliding.measurableSet_dlBox ℓ dd u
      have hAsub : A ⊆ Submission.BoseGases.acube ℓ := by
        show Submission.BoseGases.dlBox ℓ dd u ⊆ Submission.BoseGases.acube ℓ
        exact Work.SmallBoxSliding.dlBox_subset_acube ℓ dd u
      have hAvol : V = (MeasureTheory.volume A).toReal := by
        show Work.SmallBoxSliding.boxMass ℓ dd u
            = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ dd u)).toReal
        exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ dd u
      have hMv1 : 1 ≤ Mv := by rw [hMv48]; norm_num [Work.BoseBox.mValue]
      have hMv3 : 3 ≤ Mv := by rw [hMv48]; norm_num [Work.BoseBox.mValue]
      have hMv5 : 5 ≤ Mv := by rw [hMv48]; norm_num [Work.BoseBox.mValue]
      have hχc2 : ContDiff ℝ 2 χ := by
        show ContDiff ℝ 2 (Submission.BoseGases.chiSmallB Mv ℓ dd u)
        exact Work.BoseFixB1.chiSmallB_contDiff_two hMv3 u
      have hχs : HasCompactSupport χ := by
        show HasCompactSupport (Submission.BoseGases.chiSmallB Mv ℓ dd u)
        exact Submission.BoseGases.chiSmallB_hasCompactSupport hMv1 hℓpos' u
      have hχsupp : ∀ z, z ∉ A → χ z = 0 := by
        intro z hz
        show Submission.BoseGases.chiSmallB Mv ℓ dd u z = 0
        exact Work.BoseFixB1S.chiSmallB_eq_zero_of_notMem_dlBox hMv1 hℓpos' hdpos' u hz
      have hχnn : ∀ z, 0 ≤ χ z := fun z => by
        show 0 ≤ Submission.BoseGases.chiSmallB Mv ℓ dd u z
        exact Submission.BoseGases.chiSmallB_nonneg Mv ℓ dd u z
      have hκχ : ∀ z, |χ z| ≤ κ := by
        intro z
        show |Submission.BoseGases.chiSmallB Mv ℓ dd u z|
            ≤ Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
        have h1 := Work.SmallBoxSliding.abs_chiSmallB_le (M := Mv) (ℓ := ℓ) (d := dd) hMv1 u z
        have h2 : Submission.BoseGases.chiSmall Mv ((ℓ * dd)⁻¹ • z - u)
            ≤ Submission.BoseGases.chiSmallDecay Mv := by
          have h3 := Submission.BoseGases.chiSmall_decay_coord_le_decay hMv1 ((ℓ * dd)⁻¹ • z - u)
          rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg Mv _)] at h3
        rw [hMv48]
        calc |Submission.BoseGases.chiSmallB Mv ℓ dd u z|
            ≤ Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmall Mv ((ℓ * dd)⁻¹ • z - u) := h1
          _ ≤ Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue :=
              mul_le_mul_of_nonneg_left h2 Submission.BoseGases.chiSupAbs_nonneg
      -- ### the kernel data
      have h16Rℓ : 16 * R ≤ ℓ := by rw [hℓdef]; exact h16R
      have h16Rℓd : 16 * R ≤ ℓ * dd := by rw [hℓdef, hddef]; exact h16Rd
      obtain ⟨hsup0, hfin0, _hM10⟩ := hKcbound (ℓ := ℓ) (d := dd) hℓpos' hdpos' h16Rℓ h16Rℓd
      have h𝒲int : MeasureTheory.Integrable 𝒲 := by
        rw [h𝒲def]
        exact Work.BoseFixB1S.wSmallInner_integrable16 h hR hv hv1 hvrad hv_supp
          (le_trans (by norm_num) hMv5) hℓpos' hdpos' h16Rℓ h16Rℓd
      have hsup : ∀ q : E3, |Submission.BoseGases.pairW 𝒲 q| ≤ Kc * (_root_.BoseGases.a v) := by
        intro q
        rw [h𝒲def]
        exact hsup0 q
      have hfin : MeasureTheory.Integrable (fun q : E3 =>
          Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2) := by
        rw [h𝒲def]; exact hfin0
      -- the sharp Newtonian mass at the window
      have hχR0 : R ≤ ℓ * Submission.BoseGases.chiR0 := by
        have h := (hε₃ μ hμpos hAdm₃).2
        rwa [Work.BoseFixGlue.ℓB] at h
      have hJ0 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
          Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2)
          ≤ 2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)) * D := by
        rw [h𝒲def, hDdef]
        exact hK1sh (ℓ := ℓ) (d := dd) hℓpos' hdpos' (by linarith [h16Rℓd]) hχR0
      -- ### the two integrability inputs of the chain
      have hBle : ∀ q : E3, |Submission.BoseGases.pairW 𝒲 q / V|
          ≤ 1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
            + 2 * Ks * (_root_.BoseGases.a v) / V := by
        intro q
        have h := Work.BoseFixB1B.pairRung.hBle_of (n := N + 1) (V := V) (Ks := Ks)
          (av := _root_.BoseGases.a v) (c := c) (K := Kc) (𝒲 := 𝒲)
          hVpos' hav.le hKsKc hsup q
        have hcast : (1 : ℝ) / (((N + 1 : ℕ) : ℝ) + 1) = 1 / ((N : ℝ) + 2) := by
          rw [Nat.cast_add, Nat.cast_one]
          congr 1
          ring
        rw [hcast] at h
        exact h
      have hIntQ : MeasureTheory.Integrable (fun q : E3 =>
          (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
            + 2 * Ks * (_root_.BoseGases.a v) / V
            - Real.sqrt ((1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
                + 2 * Ks * (_root_.BoseGases.a v) / V) ^ 2
              - (Submission.BoseGases.pairW 𝒲 q / V) ^ 2)) / 2) := by
        have hh := Work.BoseFixB1B.pairRung.hIntK_of (n := N + 1) (V := V) (Ks := Ks)
          (av := _root_.BoseGases.a v) (c := c) (𝒲 := 𝒲) hVpos' hKs0 hav hcpos.le h𝒲int hfin
        have hIK : MeasureTheory.Integrable (fun q : E3 =>
            (Submission.BoseGases.pairW 𝒲 q / V) ^ 2 /
              (1 / ((N : ℝ) + 2) * Submission.BoseGases.fsKinCoeff c ‖q‖
                + 2 * Ks * (_root_.BoseGases.a v) / V)) := by
          refine hh.congr (Filter.Eventually.of_forall fun q => ?_)
          have hcast : (1 : ℝ) / (((N + 1 : ℕ) : ℝ) + 1) = 1 / ((N : ℝ) + 2) := by
            rw [Nat.cast_add, Nat.cast_one]
            congr 1
            ring
          rw [hcast]
        exact Work.BoseFixB1B.intQ_of_intK (N := N) (V := V) (Ks := Ks) (av := _root_.BoseGases.a v) (c := c)
          (𝒲 := 𝒲) hVpos' hKs0 hav hBle hIK
      have hintP : MeasureTheory.Integrable (fun q : E3 =>
          (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
              + 2 * Ks * (_root_.BoseGases.a v) / V) *
            Work.BoseFixB1.boxWinModePGen ℓ V A χ Ψ q) := by
        have hfsK : MeasureTheory.Integrable (fun q : E3 =>
            Submission.BoseGases.fsKinCoeff c ‖q‖ *
              Work.BoseFixB1.boxWinModePGen ℓ V A χ Ψ q) :=
          Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable (n := N + 1) (ℓ := ℓ) (d := dd)
            hℓpos' hdpos' hdle1' hMv5 u hVpos' hcpos hΨcd
        have hP : MeasureTheory.Integrable (fun q : E3 =>
            Work.BoseFixB1.boxWinModePGen ℓ V A χ Ψ q) :=
          (Work.BoseFixB1S.win.chiSmallB_windowIntegrable (n := N + 1) (ℓ := ℓ) (d := dd)
            hℓpos' hdpos' hdle1' hMv5 u hVpos' hΨcd).1
        have h1 := hfsK.const_mul (1 / ((N : ℝ) + 1 + 1))
        have h2 := hP.const_mul (2 * Ks * (_root_.BoseGases.a v) / V)
        refine (h1.add h2).congr (Filter.Eventually.of_forall fun q => ?_)
        simp only [Pi.add_apply]
        ring
      have hintR : MeasureTheory.Integrable (fun q : E3 =>
          (1 / V) * Submission.BoseGases.pairW 𝒲 q *
            Work.BoseFixB1.boxWinModeRGen ℓ V A χ Ψ q) := by
        have hh : MeasureTheory.Integrable (fun q : E3 =>
            Submission.BoseGases.pairW 𝒲 q * Work.BoseFixB1.boxWinModeRGen ℓ V A χ Ψ q) :=
          Work.BoseFixB1B.pairRung.winModeRGenMulPairWIntegrable (n := N + 1) (a := ℓ) (volA := V)
            hℓpos' hVpos' hAmeas hAsub hAvol hχc2 hχs hχsupp (fun z => hκχ z) h𝒲int hΨcd
        have h2 : (fun q : E3 => (1 / V) * (Submission.BoseGases.pairW 𝒲 q
              * Work.BoseFixB1.boxWinModeRGen ℓ V A χ Ψ q))
            = fun q : E3 => (1 / V) * Submission.BoseGases.pairW 𝒲 q
              * Work.BoseFixB1.boxWinModeRGen ℓ V A χ Ψ q := by
          funext q; ring
        rw [← h2]
        exact hh.const_mul (1 / V)
      have hIntK : MeasureTheory.Integrable (fun q : E3 =>
          (Submission.BoseGases.pairW 𝒲 q / V) ^ 2 /
            (1 / ((N : ℝ) + 1 + 1) * Submission.BoseGases.fsKinCoeff c ‖q‖
              + 2 * Ks * (_root_.BoseGases.a v) / V)) := by
        have hh := Work.BoseFixB1B.pairRung.hIntK_of (n := N + 1) (V := V) (Ks := Ks)
          (av := _root_.BoseGases.a v) (c := c) (𝒲 := 𝒲) hVpos' hKs0 hav hcpos.le h𝒲int hfin
        simpa only [Nat.cast_add, Nat.cast_one] using hh
      -- ### the sharp chain
      have hchain := Work.BoseFixB1B.chainA2SharpBeps (N := N) (by omega) (ℓ := ℓ) (volA := V) (c := c)
        (Kc := Kc) (Ks := Ks) (av := _root_.BoseGases.a v) (κ := κ) (μ := μ) (δ := δ)
        (Ac := A) (χ := χ) (𝒲 := 𝒲) (Ψ := Ψ)
        hℓpos' hVpos' hKs0 hav hcpos hKc0 hδpos hδle hKsKc hμpos.le hAmeas hAsub hAvol hχc2 hχs
        hχsupp hχnn hκχ hΨcd hnormΨ h𝒲int hsup hfin hintP hintR hIntK hIntQ
      -- ### the row arithmetic
      have hXw0 : 0 ≤ Xw := by rw [hXwdef]; exact integral_nonneg (fun z => sq_nonneg _)
      have hchiMκ : Work.SmallBoxSliding.chiMass Mv ℓ dd u
          ≤ κ ^ 2 * Work.SmallBoxSliding.boxMass ℓ dd u := by
        rw [hκdef]
        exact Work.BoseFixB1S.chiMass_le_const_mul_boxMass hMv1 hℓpos' hdpos' u
      have hXwle : Xw ≤ Kx * V := by
        rw [hXwdef]
        show (∫ z : E3, (Submission.BoseGases.chiSmallB Mv ℓ dd u z) ^ 2)
            ≤ Kx * Work.SmallBoxSliding.boxMass ℓ dd u
        rw [← Work.SmallBoxSliding.chiMass_def]
        exact le_trans hchiMκ (mul_le_mul_of_nonneg_right hκsq (le_of_lt hVpos'))
      have hSle : Work.BoseFixB1S.boxFlatCount V ℓ A Ψ ≤ (N : ℝ) + 1 := by
        have hh := Work.BoseFixB1S.boxFlatCount_le_NB1 (N := N + 1) hℓpos' hVpos' hAmeas hAsub
          hAvol hΨcd.continuous
        rw [hnormΨ, mul_one] at hh
        simpa only [Nat.cast_add, Nat.cast_one] using hh
      have hS0 : 0 ≤ Work.BoseFixB1S.boxFlatCount V ℓ A Ψ := by
        rw [Work.BoseFixB1S.boxFlatCount]
        exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
      have hJ00 : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
          Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2) := by
        refine mul_nonneg (by positivity) ?_
        exact integral_nonneg (fun q => div_nonneg (sq_nonneg _) (sq_nonneg _))
      have hmain : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ)
            * (2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)))
          ≤ 2 * (1 - θ) * c0 / D := by
        have hδ₀ : K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2) ≤ min eps 1 / 32 := by
          have h := hsmall μ hAdm₂
          simpa [hℓdef, hddef] using h
        set x : ℝ := min eps 1 / 32 with hxdef
        have hx0 : 0 ≤ x := by rw [hxdef]; positivity
        have hxle : x ≤ eps / 32 := by
          rw [hxdef]
          have h := min_le_left eps 1
          linarith
        have hxsmall : x ≤ 1 / 4 := by
          rw [hxdef]
          have h := min_le_right eps 1
          linarith
        have hA : 1 + Kc ^ 2 / (4 * Ks ^ 2) ≤ 1 + x := by
          simpa only [add_comm] using add_le_add_left hτ2 1
        have hB : 1 + 8 * δ ≤ 1 + x := by
          simpa only [add_comm] using add_le_add_left hδsmall 1
        have hC : 1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2) ≤ 1 + x := by
          simpa only [add_comm] using add_le_add_left hδ₀ 1
        have hcube : (1 + x) * (1 + x) * (1 + x) ≤ 1 + 4 * x := by
          have hx2 : x * x ≤ x / 4 := by nlinarith [hx0, hxsmall]
          have hx3 : x * x * x ≤ x / 16 := by nlinarith [hx2, hxsmall, hx0]
          nlinarith [hx0, hxsmall, hx2, hx3]
        have h4 : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ) ≤ (1 + x) * (1 + x) :=
          mul_le_mul hA hB (by positivity) (by nlinarith [hx0])
        have h5 : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ)
            * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2))
            ≤ (1 + x) * (1 + x) * (1 + x) :=
          mul_le_mul h4 hC (by positivity) (by nlinarith [hx0])
        have hprod : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ)
            * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)) ≤ 1 + eps / 8 := by
          have h6 : 4 * x ≤ eps / 8 := by linarith [hxle]
          have h7 : (1 + x) * (1 + x) * (1 + x) ≤ 1 + eps / 8 :=
            le_trans hcube (by linarith [h6])
          exact le_trans h5 h7
        have h34 : 1 + eps / 8 ≤ (1 - θ) * (c0 / D) := by
          have h6 : 1 + eps / 8 ≤ (1 - θ) * (1 + eps) := by linarith [hθsmall]
          have h7 : (1 + eps) ≤ c0 / D := by
            rw [hc0def, mul_div_assoc, div_self (ne_of_gt hDpos), mul_one]
          have h8 : 0 ≤ 1 - θ := by linarith [hθle]
          calc 1 + eps / 8 ≤ (1 - θ) * (1 + eps) := by linarith [h6]
            _ ≤ (1 - θ) * (c0 / D) := mul_le_mul_of_nonneg_left h7 h8
        have h9 : (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ)
            * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)) ≤ (1 - θ) * (c0 / D) :=
          le_trans hprod h34
        calc (1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ)
              * (2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)))
            = 2 * ((1 + Kc ^ 2 / (4 * Ks ^ 2)) * (1 + 8 * δ)
                * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2))) := by ring
          _ ≤ 2 * ((1 - θ) * (c0 / D)) := by linarith [h9]
          _ = 2 * (1 - θ) * c0 / D := by ring
      have hc6 : c ^ 6 * V ≤ μ := by
        have ha : (0:ℝ) < _root_.BoseGases.a v := hav
        have hXp0 : 0 < Xp := by
          rw [hXpdef]
          exact Work.BoseBox.fsXp_pos (mul_pos hμpos (pow_pos hav 3))
        have hXp1 : Xp ≤ 1 := by
          rw [hXpdef]
          exact Work.BoseBox.fsXp_le_one (mul_pos hμpos (pow_pos hav 3)) hμa3le (by norm_num)
        have hXpPow : Xp ^ 323 = μ * (_root_.BoseGases.a v) ^ 3 := by
          have ht0 : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμpos (pow_pos hav 3)
          have h3 : (Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1) ^ 323
              = μ * (_root_.BoseGases.a v) ^ 3 := by
            show ((μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 323)) ^ 323
                = μ * (_root_.BoseGases.a v) ^ 3
            rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
            norm_num
            try rw [Real.rpow_one]
          rw [hXpdef]
          exact h3
        have hc3 : c ^ 3 = ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 468 := by
          have h := Work.BoseFixB1S.sbCut_cube_eq (μ := μ) (α := _root_.BoseGases.a v) hav hμpos
          rw [← hcdef, ← hXpdef] at h
          exact h
        have hdl3 : (ℓ * dd) ^ 3 = (_root_.BoseGases.a v) ^ 3 * (Xp ^ 471)⁻¹ := by
          have h := Work.BoseFixB1.d_mul_sideAt_cube_eq (A := _root_.BoseGases.a v) (μ := μ)
            hav hμpos
          have h1 : ℓ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
            rw [hℓdef, Work.BoseFixB1.bSide]
          have h2 : dd = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := by
            rw [hddef, Work.BoseFixB1.bD]
          have h3 : Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-471 : ℝ)
              = (Xp ^ 471)⁻¹ := by
            have ht0 : (0:ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμpos (pow_pos hav 3)
            have hXeq : Xp = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1:ℝ)/323) := by
              show Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (1:ℝ)
                  = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1:ℝ)/323)
              rw [Work.BoseBox.fsXp]
            have hL : Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-471 : ℝ)
                = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((-471:ℝ)/323) := by
              rw [Work.BoseBox.fsXp]
            have hpow : ((μ * (_root_.BoseGases.a v) ^ 3) ^ ((1:ℝ)/323)) ^ 471
                = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((471:ℝ)/323) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt ht0)]
              norm_num
            rw [hL, hXeq,
              show (-471 : ℝ) / 323 = -((471 : ℝ) / 323) by ring,
              Real.rpow_neg (le_of_lt ht0), hpow]
          rw [h1, h2, mul_comm, h, h3]
        have hVle : V ≤ (ℓ * dd) ^ 3 := by rw [hVdef]; exact hVcube
        have h1 : c ^ 6 * V ≤ c ^ 6 * (ℓ * dd) ^ 3 :=
          mul_le_mul_of_nonneg_left hVle (by positivity)
        have heq : c ^ 6 * (ℓ * dd) ^ 3 = ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 465 := by
          have hne : Xp ≠ 0 := ne_of_gt hXp0
          have hane : (_root_.BoseGases.a v) ≠ 0 := ne_of_gt hav
          rw [show c ^ 6 = (c ^ 3) ^ 2 by ring, hc3, hdl3, pow_two]
          field_simp <;> ring_nf
        have h1' : c ^ 6 * V ≤ ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 465 := by
          rw [heq] at h1
          exact h1
        have h3 : Xp ^ 465 ≤ Xp ^ 323 :=
          pow_le_pow_of_le_one hXp0.le hXp1 (by norm_num)
        have h4 : ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 323 = μ := by
          rw [hXpPow]
          field_simp
        have h5 : 0 ≤ ((_root_.BoseGases.a v) ^ 3)⁻¹ := by positivity
        have h6 : ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 465
            ≤ ((_root_.BoseGases.a v) ^ 3)⁻¹ * Xp ^ 323 :=
          mul_le_mul_of_nonneg_left h3 h5
        linarith [h1', h6, h4]
      have hK1pos : 0 ≤ 2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2)) :=
        mul_nonneg (by norm_num)
          (add_nonneg (by norm_num) (mul_nonneg hK1s0 (add_nonneg (sq_nonneg _) (sq_nonneg _))))
      have hn0N : 0 ≤ (N : ℝ) + 1 := add_nonneg (Nat.cast_nonneg N) (by norm_num)
      set Y : ℝ := Xw / Kx with hYdef
      have hYeq : Xw = Kx * Y := by
        rw [hYdef]
        field_simp
      have hY0 : 0 ≤ Y := by
        rw [hYdef]; exact div_nonneg hXw0 (le_of_lt hKxpos)
      have hYle : Y ≤ V := by
        rw [hYdef, div_le_iff₀ hKxpos, mul_comm]
        exact hXwle
      have harith := Work.BoseFixB1B.epsRowArithBeps (n := (N : ℝ) + 1) (V := V)
        (av := _root_.BoseGases.a v) (c := c) (Kc := Kc) (Ks := Ks) (δ := δ)
        (K1 := 2 * (1 + K1s * ((R / ℓ) ^ 2 + (R / (ℓ * dd)) ^ 2))) (D := D) (c0 := c0)
        (S := Work.BoseFixB1S.boxFlatCount V ℓ A Ψ) (X := Y)
        (mu := μ) (C := Ch) (J0 := ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
          Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2)) (θ := θ)
        hVpos' hav hcpos hKs0 hKc0 hδpos hDpos hK1pos hc0pos hμpos hθpos hθle hτ1
        hn0N hS0 hSle hY0 hYle hJ00 hJ0 hCh0 hc6 hmain hChcred
      have harithKx : (1 / 2) * c0 * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Xw
            + Ch * Kx * (_root_.BoseGases.a v) * μ
          ≥ Work.BoseFixB1S.boxFlatCount V ℓ A Ψ * Xw
              * ((1 + Kc ^ 2 / (4 * Ks ^ 2))
                  * ( Kc ^ 2 * (_root_.BoseGases.a v) * c ^ 3
                        / (48 * Real.pi ^ 2 * Ks * V * δ ^ 3)
                    + (1 + 8 * δ) * ((N : ℝ) + 1 + 1) / (4 * V ^ 2)
                        * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
                            Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2)))) := by
        have h := mul_le_mul_of_nonneg_left harith (le_of_lt hKxpos)
        have e1 : Kx * ((1 / 2) * c0 * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Y
              + Ch * (_root_.BoseGases.a v) * μ)
            = (1 / 2) * c0 * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2) * Xw
              + Ch * Kx * (_root_.BoseGases.a v) * μ := by
          rw [hYeq]; ring
        have e2 : Kx * (Work.BoseFixB1S.boxFlatCount V ℓ A Ψ * Y
              * ((1 + Kc ^ 2 / (4 * Ks ^ 2))
                  * ( Kc ^ 2 * (_root_.BoseGases.a v) * c ^ 3
                        / (48 * Real.pi ^ 2 * Ks * V * δ ^ 3)
                    + (1 + 8 * δ) * ((N : ℝ) + 1 + 1) / (4 * V ^ 2)
                        * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
                            Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2)))))
            = Work.BoseFixB1S.boxFlatCount V ℓ A Ψ * Xw
              * ((1 + Kc ^ 2 / (4 * Ks ^ 2))
                  * ( Kc ^ 2 * (_root_.BoseGases.a v) * c ^ 3
                        / (48 * Real.pi ^ 2 * Ks * V * δ ^ 3)
                    + (1 + 8 * δ) * ((N : ℝ) + 1 + 1) / (4 * V ^ 2)
                        * (((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
                            Submission.BoseGases.pairW 𝒲 q ^ 2 / ‖q‖ ^ 2)))) := by
          rw [hYeq]; ring
        linarith [h, e1.le, e1.ge, e2.le, e2.ge]
      -- ### transport back to `Φ`
      have hscSpec : Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          = t ^ 2 * Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ := by
        show Work.UBBInputs8.tBwordKinInd ℓ A V χ c (Φ : Submission.BoseGases.X (N + 1) → ℝ)
            = t ^ 2 * Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ
        rw [hΦeq]
        exact Work.BoseFixB1.tBwordKinInd_mul ℓ V χ c t Ψ
      have hscA2 : Work.BoseFixB1.bA2 v h μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          = t ^ 2 * Work.BoseFixB1.bA2 v h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u := by
        rw [hΦeq]
        exact Work.BoseFixB1.bA2_mul v h μ t Ψ u
      have hscQ : Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          = t ^ 2 * Work.BoseFixB1.bQ v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u := by
        rw [hΦeq]
        exact Work.BoseFixB1.bQ_mul v μ t Ψ u
      have hscI : Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) = t ^ 2 := by
        rw [hΦeq, Work.BoseFixB1.bI_mul, hbIval, mul_one]
      have hQeq : Work.BoseFixB1.bQ v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
          = Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := rfl
      have hchiM : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u = Xw := by
        show (∫ z : E3, (Submission.BoseGases.chiSmallB Mv ℓ dd u z) ^ 2) = Xw
        rw [hXwdef]
      have hA2Bunf : Work.BoseFixB1.bA2 v h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
          = Work.BoseFixB1.boxA2 ℓ V A (fun x y => χ x * χ y * 𝒲 (x - y)) Ψ := by
        show Work.BoseFixB1.boxA2 ℓ V A (Submission.BoseGases.wSmall1Pair h Mv ℓ dd u) Ψ = _
        rw [Work.BoseFixB1B.pairRung.wSmall1Pair_kernel h Mv ℓ dd u]
        rfl
      have hspecΨ : Work.BoseFixB1S.bSpectralCube v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
          = Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ := rfl
      have hgoalΨ : -((1 / 2) * c0 * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2)
            * Work.BoseFixB1.bI v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
          + C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
              * Work.BoseFixB1.bQ v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
          + C * (_root_.BoseGases.a v) * μ
              * Work.BoseFixB1.bI v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ))
          ≤ Work.BoseFixB1S.bSpectralCube v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
            + Work.BoseFixB1.bA2 v h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u := by
        have h1 : Work.BoseFixB1.bI v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) = 1 := hbIval
        have h2 : Work.BoseFixB1.bQ v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
            = Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := hQeq
        have h3 : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
            (Work.BoseFixB1.bD v μ) u = Xw := hchiM
        have h4 : Work.BoseFixB1S.bSpectralCube v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
            = Work.UBBInputs8.tBwordKinInd ℓ A V χ c Ψ := rfl
        rw [h1, h2, h3, h4, hA2Bunf]
        -- the credit row pays the chain's `A₁`-loss, since `C ≥ 4 K_s`
        have hcred2 : (4 * Ks * κ ^ 2) * (_root_.BoseGases.a v)
            * ((μ + (((N : ℝ) + 1) / V)) * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ)
            ≤ C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
                * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := by
          have h6 : 0 ≤ (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
              * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := by
            have h7 : 0 ≤ Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := by
              rw [Work.UBBInputs8.cnPlusBoxInd]
              exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
            have h8 : 0 ≤ μ + (((N : ℝ) + 1) / V) :=
              add_nonneg hμpos.le (div_nonneg (by positivity) hVpos'.le)
            exact mul_nonneg (mul_nonneg hav.le h8) h7
          have h9 : (4 * Ks * κ ^ 2) ≤ C := hCκ
          calc (4 * Ks * κ ^ 2) * (_root_.BoseGases.a v)
                * ((μ + (((N : ℝ) + 1) / V)) * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ)
              = (4 * Ks * κ ^ 2) * ((_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
                  * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ) := by ring
            _ ≤ C * ((_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
                  * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ) :=
                mul_le_mul_of_nonneg_right h9 h6
            _ = C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
                  * Work.UBBInputs8.cnPlusBoxInd ℓ A V Ψ := by ring
        have hN2 : (N : ℝ) + 2 = (N : ℝ) + 1 + 1 := by ring
        have hXw' : (∫ z : E3, χ z ^ 2) = Xw := hXwdef.symm
        have hCCh' : Ch * Kx * (_root_.BoseGases.a v) * μ ≤ C * (_root_.BoseGases.a v) * μ := by
          have h2 : 0 ≤ (_root_.BoseGases.a v) * μ := mul_nonneg hav.le hμpos.le
          calc Ch * Kx * (_root_.BoseGases.a v) * μ
              = (Ch * Kx) * ((_root_.BoseGases.a v) * μ) := by ring
            _ ≤ C * ((_root_.BoseGases.a v) * μ) := mul_le_mul_of_nonneg_right hCCh h2
            _ = C * (_root_.BoseGases.a v) * μ := by ring
        rw [hN2, hXw'] at hchain
        linarith [hchain, harithKx, hcred2, hCCh']
      -- ### scale back
      have hgoal_eq : -((1 / 2) * ((1 + eps) * Submission.BoseGases.g0w0Mass (v := v) h)
            * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2)
            * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u
          + C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
              * Work.BoseFixB1.bQ v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          + C * (_root_.BoseGases.a v) * μ
              * Work.BoseFixB1.bI v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ))
          = t ^ 2 * (-((1 / 2) * c0 * ((((N : ℝ) + 1 + 1) * ((N : ℝ) + 1)) / V ^ 2)
              * Work.BoseFixB1.bI v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ)
              * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u
            + C * (_root_.BoseGases.a v) * (μ + (((N : ℝ) + 1) / V))
                * Work.BoseFixB1.bQ v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
            + C * (_root_.BoseGases.a v) * μ
                * Work.BoseFixB1.bI v μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ))) := by
        rw [hscI, hscQ, hbIval]
        rw [hc0def, hDdef]
        ring
      have hrhs : Work.BoseFixB1S.bSpectralCube v μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          + Work.BoseFixB1.bA2 v h μ (Φ : Submission.BoseGases.X (N + 1) → ℝ) u
          = t ^ 2 * (Work.BoseFixB1S.bSpectralCube v μ
              (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u
            + Work.BoseFixB1.bA2 v h μ (Ψ : Submission.BoseGases.X (N + 1) → ℝ) u) := by
        rw [hscSpec, hscA2, hspecΨ]; ring
      rw [hgoal_eq, hrhs]
      exact mul_le_mul_of_nonneg_left hgoalΨ (by positivity)

end Work.BoseB1Cube
