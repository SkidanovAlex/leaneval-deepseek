import ChallengeDeps
import Submission.Work.BoseFixR.FSParamsViewCanon
import Submission.Work.BoseFixR.HonestFamily
import Submission.Work.BoseFixR.HonestVacuum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/HonestFacts.lean` — the honest instance's proved arithmetic

The residuals `RB4box`/`RB5`/`RB67` are stated at the honest family
`KzHonestFamOrth` (`HonestFamily.lean`).  Their *view* (`RView`, `Defs.lean`) is a
list of twenty conjuncts, of which the following are **proved here**, from B4's
model alone:

* `KzEnvFs_rho` — the environment's condensate density is the chemical potential
  (`(KzEnvFs v h μ F fc).rho = μ`, from `z = √(μℓ³)` and `rhoZ`);
* `boxFockData_nPlus_le_totNumOp` — the Bessel inequality for the box χ-modes:
  `⟨n₊φ, φ⟩ ≤ ⟨N φ, φ⟩` for `n₊ = Σ_{k ≠ 0}a_k†a_k` and `N = totNumOp m`, from the
  orthonormality of the excited χ-mode family (`Work.BoseB4.bessel_le_totNumOp_v2`);
  this is the honest content of `RView`'s `n₊ ≤ N` conjunct (which is **not**
  derivable from `FockData`/`TildeData` for arbitrary mode data — see
  `RB4boxHonestFamFalse.lean`);
* `KzHonestFamOrth_nPlus_le_N` — that conjunct at the honest family
  `KzHonestFamOrth`;
* `KzHonestFamOrth_window` — the nonzero `𝓜`-window state `RB4box` demands
  (`TildeData.window_nonempty_of_vac` + `Work.BoseFixR.vac_killed`, at
  `𝓜 = bigM (paramsAt μ (a v)) (a v) μ ≥ 0`).

The remaining conjuncts of the view at `KzHonestFamOrth` are the *honest-instance*
obligations: `Nonempty (FSParamsView ·)` is `FSParamsViewCanon` (proved), the
scalar/kernel pins are the definitional unfolding of `KzEnvFs` (plus
`KzEnvFs_rho` for the `𝒜`/`ℬ` rows), and the §10 kernel gate
`∃ K₀ b₀, … Q3Kernel' K₀ (F μ) (T μ) (KzEnvAt (KzEnvFs …) ρ)` on `CloseCond` is
**BoseK15's instantiation** (`Work.BoseK15.Q3Kernel'_of_box` from
`Work.BoseK15.exists_K15Input_box`, which needs FS's primitive potential rows and
the box-model equations) — *uniformly in the re-pointed density* `ρ` in the close
region, which is what `thm:Kafz`'s `inf_z` over the close range needs.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The condensate density of the canonical environment -/

/-- `(KzEnvFs v h μ F fc).rho = μ`: `KzEnvFs` sets `z = √(μℓ³)`, and
`rho = z²/ℓ³`. -/
lemma KzEnvFs_rho {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : ScatSol v) {μ : ℝ}
    (hμ : 0 < μ) (hav : 0 < a v)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (fc : LowCut) :
    (KzEnvFs v h μ F fc).rho = μ := by
  rw [Work.BoseB7.Q3Env.rho, KzEnvFs]
  simp only
  have hℓ : 0 < sideAt μ (a v) := Work.BoseBox.sideAt_pos hμ hav
  rw [Work.BoseB7.rhoZ]
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-! ## 2. The Bessel conjunct `n₊ ≤ N` at the box mode system -/

/-- **The honest `n₊ ≤ N`** (`RView`'s conjunct): on B4's box mode system, with
the *excited* χ-modes orthonormal (`hf_orth`), the excited number operator
`n₊ = Σ_{k ≠ 0}a_k†a_k` is dominated by `totNumOp m = Σ_{l}a_l†a_l`.

The Gram hypothesis `hf` is not used in the proof — the content is the Bessel
inequality `Work.BoseB4.bessel_le_totNumOp_v2` for the orthonormal family
`f ·` restricted to the excited modes — but it is kept so that the statement is
the one `KzHonestFamOrth` carries. -/
theorem boxFockData_nPlus_le_totNumOp {ℓ : ℝ} {Mode : Type*} [AddCommGroup Mode]
    [Fintype Mode] [DecidableEq Mode] (kmom : Mode → EuclideanSpace ℝ (Fin 3))
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (m : ℕ) (f : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ Work.BoseK15.corpusBox.hatChiSq
          Work.BoseK15.corpusBox.hatChi (kmom i) (kmom j))
    (hf_orth : ∀ i j : Mode, i ≠ 0 → j ≠ 0 →
      Work.BoseB4.gram (f i) (f j) = if i = j then 1 else 0)
    (φ : (Work.BoseB4.boxFockData Work.BoseK15.corpusBox kmom hkmom m f hf).H) :
    (Work.BoseB4.boxFockData Work.BoseK15.corpusBox kmom hkmom m f hf).bp
        ((Work.BoseB4.boxFockData Work.BoseK15.corpusBox kmom hkmom m f hf).nPlus φ) φ
      ≤ (Work.BoseB4.boxFockData Work.BoseK15.corpusBox kmom hkmom m f hf).bp
        ((Work.BoseB4.totNumOp m) φ) φ := by
  have hg : ∀ s ∈ Work.BoseB7.excited Mode, ∀ t ∈ Work.BoseB7.excited Mode,
      Work.BoseB4.gram (f s) (f t) = if s = t then 1 else 0 := by
    intro s hs t ht
    exact hf_orth s t (by simpa [Work.BoseB7.excited] using hs)
      (by simpa [Work.BoseB7.excited] using ht)
  have hb := Work.BoseB4.bessel_le_totNumOp_v2 f (Work.BoseB7.excited Mode) hg φ
  have hgoal : ∀ (Φ : Work.BoseB4.RealFock m),
      (Work.BoseB4.bomb m) ((∑ i ∈ Work.BoseB7.excited Mode,
        (Work.BoseB4.creOf m (f i)) ∘ₗ (Work.BoseB4.annOf m (f i))) Φ) Φ
      = ∑ i ∈ Work.BoseB7.excited Mode,
          (Work.BoseB4.bomb m) (Work.BoseB4.annOf m (f i) Φ) (Work.BoseB4.annOf m (f i) Φ) := by
    intro Φ
    have hsplit : (∑ i ∈ Work.BoseB7.excited Mode,
          (Work.BoseB4.creOf m (f i)) ∘ₗ (Work.BoseB4.annOf m (f i))) Φ
        = ∑ i ∈ Work.BoseB7.excited Mode,
          Work.BoseB4.creOf m (f i) (Work.BoseB4.annOf m (f i) Φ) := by
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    rw [hsplit]
    simp only [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun s _ => Work.BoseB4.CreOf_annOf_adjoint (f s) _ Φ
  show (Work.BoseB4.bomb m) ((∑ i ∈ Work.BoseB7.excited Mode,
      (Work.BoseB4.creOf m (f i)) ∘ₗ (Work.BoseB4.annOf m (f i))) φ) φ
      ≤ (Work.BoseB4.bomb m) ((Work.BoseB4.totNumOp m) φ) φ
  rw [hgoal φ]
  exact hb

/-! ## 3. The two honest-instance facts at `KzHonestFamOrth` -/

/-- **RView's `n₊ ≤ N` conjunct at the honest family.**  This is what makes
`RB4box`'s view-conjunct true at `KzHonestFamOrth` (and false at
`KzHonestFam` with arbitrary mode data). -/
theorem KzHonestFamOrth_nPlus_le_N {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : ScatSol v)
    (fc : LowCut)
    (Mode : ℝ → Type) [(μ : ℝ) → AddCommGroup (Mode μ)]
    [(μ : ℝ) → Fintype (Mode μ)] [(μ : ℝ) → DecidableEq (Mode μ)]
    (kmom : ∀ μ, Mode μ → EuclideanSpace ℝ (Fin 3))
    (hkmom : ∀ μ (i : Mode μ), kmom μ (-i) = -kmom μ i)
    (m : ℕ) (f : ∀ μ, Mode μ → Fin m → ℝ)
    (hf : ∀ μ (i j : Mode μ), Work.BoseB4.gram (f μ i) (f μ j)
      = Work.BoseB7.ccrKernel (ell v μ) Work.BoseK15.corpusBox.hatChiSq
          Work.BoseK15.corpusBox.hatChi (kmom μ i) (kmom μ j))
    (hf_orth : ∀ μ (i j : Mode μ), i ≠ 0 → j ≠ 0 →
      Work.BoseB4.gram (f μ i) (f μ j) = if i = j then 1 else 0)
    (g : ∀ μ, Mode μ → Fin m → ℝ)
    (hg : ∀ μ (s t : Mode μ), s ≠ 0 → t ≠ 0 →
      Work.BoseB4.gram (g μ s) (g μ t) = if s = t then 1 else 0) (μ : ℝ) :
    ∀ φ : (KzHonestFamOrth v h fc Mode kmom hkmom m f hf hf_orth g hg μ).F.H,
      (KzHonestFamOrth v h fc Mode kmom hkmom m f hf hf_orth g hg μ).F.bp
          ((KzHonestFamOrth v h fc Mode kmom hkmom m f hf hf_orth g hg μ).F.nPlus φ) φ
      ≤ (KzHonestFamOrth v h fc Mode kmom hkmom m f hf hf_orth g hg μ).F.bp
          ((KzHonestFamOrth v h fc Mode kmom hkmom m f hf hf_orth g hg μ).T.N φ) φ := by
  intro φ
  exact boxFockData_nPlus_le_totNumOp (kmom μ) (hkmom μ) m (f μ) (hf μ) (hf_orth μ) φ

/-- **`RB4box`'s nonzero-window conjunct at the honest family.**  The honest
`T.N` is `totNumOp m`, whose kernel contains the Fock vacuum
(`Work.BoseFixR.vac_killed`), and `𝓜 = bigM (paramsAt μ (a v)) (a v) μ ≥ 0`
(`Work.BoseBox.bigM_pos_of_params`). -/
theorem KzHonestFamOrth_window {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : ScatSol v)
    (fc : LowCut)
    (Mode : ℝ → Type) [(μ : ℝ) → AddCommGroup (Mode μ)]
    [(μ : ℝ) → Fintype (Mode μ)] [(μ : ℝ) → DecidableEq (Mode μ)]
    (kmom : ∀ μ, Mode μ → EuclideanSpace ℝ (Fin 3))
    (hkmom : ∀ μ (i : Mode μ), kmom μ (-i) = -kmom μ i)
    (m : ℕ) (f : ∀ μ, Mode μ → Fin m → ℝ)
    (hf : ∀ μ (i j : Mode μ), Work.BoseB4.gram (f μ i) (f μ j)
      = Work.BoseB7.ccrKernel (ell v μ) Work.BoseK15.corpusBox.hatChiSq
          Work.BoseK15.corpusBox.hatChi (kmom μ i) (kmom μ j))
    (hf_orth : ∀ μ (i j : Mode μ), i ≠ 0 → j ≠ 0 →
      Work.BoseB4.gram (f μ i) (f μ j) = if i = j then 1 else 0)
    (g : ∀ μ, Mode μ → Fin m → ℝ)
    (hg : ∀ μ (s t : Mode μ), s ≠ 0 → t ≠ 0 →
      Work.BoseB4.gram (g μ s) (g μ t) = if s = t then 1 else 0)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    ∃ f₀ : (KzHonestFamOrth v h fc Mode kmom hkmom m f hf hf_orth g hg μ).F.H,
      (KzHonestFamOrth v h fc Mode kmom hkmom m f hf hf_orth g hg μ).T.NWindow
          (KzHonestFamOrth v h fc Mode kmom hkmom m f hf hf_orth g hg μ).E.bigM f₀
        ∧ f₀ ≠ 0 := by
  have hM : 0 ≤ (KzHonestFamOrth v h fc Mode kmom hkmom m f hf hf_orth g hg μ).E.bigM := by
    show 0 ≤ bigM (paramsAt μ (a v)) (a v) μ
    exact (Work.BoseBox.bigM_pos_of_params hμ hav).le
  refine Work.BoseB7A.TildeData.window_nonempty_of_vac _ hM ?_
  obtain ⟨f₀, hne, hkill⟩ := vac_killed m
  exact ⟨f₀, hne, hkill⟩

end Work.BoseFixR
