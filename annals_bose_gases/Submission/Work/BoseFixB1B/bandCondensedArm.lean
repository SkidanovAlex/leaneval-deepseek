import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.BandSdefs
import Submission.Work.BoseFixB1B.flatArmBandDefs
import Submission.Work.BoseFixR.SlabArmExcited
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.bandCondensedArm` — SKELETON (the statement is frozen; the body is open)

Status (read `Submission/Work/BoseFixB1B/FINDING_bandCondensedArm.md` first).

The statement below is the *condensed arm* of FS's rough per-box estimate
(`Papers/fournais_solovej/final_v2.tex`, l.4083) restricted to FS's `μ ↦ 4μ` band, with the
occupancy hypotheses `crudeThreshold ≤ occChi` (the state is *denser* in `B(u)` than the expected
density) and `boxQCount ≤ boxFlatCount` (the condensate dominates the excited count).

It is **TRUE** — it is a consequence of FS `thm:smallbox` at the sliding box — and it is
**equivalent in content to the corpus's central open residual**
`Work.BoseFixR.SlabCondensedHalf` (the same bound for *all* `u`); the 5-line adapter is in §2.4 of
the FINDING.  Every *clean* rough per-box statement on disk covers the *complementary* regimes:

* `Work.BoseFixR.PerBoxWordCrudeLow` — the **cap** case `occChi ≤ K(μχ_M+1)‖Φ‖²` (note: the
  inequality direction *opposite* to the target's hypothesis), for all `u`;
* `Work.BoseFixR.SlabArmExcited` — the excited case `n₊ ≥ cnt/2`;
* `Work.BoseFixB1B.sbCore` — `sbWord ≥ c'²μ(a v)n₊ − μ·kav·(a v)·occChi` (linear in the count).

The remaining content is the interpolation (the mean-field pair term plus the Bogoliubov pairing):
the rung-4 rung `Work.BoseFixB1.pairBlockSqLowerB2` (whose analytic core
`boxCrossPart_n0Completion` is delegated as `Work.BoseFixB1B.boxCrossPartN0Completion`, this
directory) and the rung-3 rung `Work.BoseFixB1B.LocalisedAppBogVol`
(`Submission/Work/BoseFixB1B/AppBogCalib.lean`, in flight in the corpus).

So: **do not** attempt the fibre/count route (`bandPerBoxCrude_of_inputs` needs the a-priori count
window `n ≤ Cμℓ³`, which is `sorryAx`-tainted here), and **do not** declare this node false: it is
true.  Close it by closing `SlabCondensedHalf` and applying the adapter.
-/

namespace Work.BoseFixB1B

open MeasureTheory

/-! ## The excited arm of the band-condensed bound (a piece, proved here)

`Work.BoseFixR.SlabArmExcited` (PROVED) pays the sliding word by the *definitional* gap payment of
`sbKin` whenever the excited count dominates the box occupancy (`(1/2)·cnt ≤ n₊`).  Here we
push that mechanism down to the threshold `2·n₊ ≥ S`, i.e. to the *full* range
`n₊ ≥ cnt/3` (since `cnt = S + n₊`), which is what the dichotomy of the target needs: the
remaining case is the flat one (`n₊ ≤ S/2`).

The only change with respect to `SlabArmExcited` is the constant: `cnt ≤ 3 n₊` in place of
`cnt ≤ 2 n₊`, which the free constant `c'` absorbs (`3 K_av C_χ + 1 ≤ c'²`). -/
theorem bandExcitedArm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ K : ℝ, 0 < ε₀ ∧ 0 < K ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          Work.BoseFixR.crudeThreshold v K μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1S.boxFlatCount
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ 2 * Work.BoseFixB1S.boxQCount
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ) →
          0 ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  -- ### the constants (all `v`-dependent but `μ`-independent)
  let Cs : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
  let Kav : ℝ := 16 * Real.pi * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
      / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue
  let csq : ℝ := 3 * Kav * Cs + 1
  let c' : ℝ := Real.sqrt csq
  have hCs0 : 0 ≤ Cs := by
    show (0 : ℝ) ≤ Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
    exact mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg Work.BoseBox.mValue)
  have hKav0 : 0 ≤ Kav := by
    show (0 : ℝ) ≤ 16 * Real.pi * Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue
      / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue
    refine div_nonneg ?_ (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos Work.BoseBox.mValue))
    exact mul_nonneg (mul_nonneg (by positivity)
      Submission.BoseGases.chiSupAbs_nonneg)
      (Submission.BoseGases.chiSmallDecay_nonneg Work.BoseBox.mValue)
  have hcsq0 : 0 < csq := by
    show (0 : ℝ) < 3 * Kav * Cs + 1
    have h0 : 0 ≤ 3 * Kav * Cs := mul_nonneg (mul_nonneg (by norm_num) hKav0) hCs0
    linarith
  have hc'0 : 0 ≤ c' := by
    show (0 : ℝ) ≤ Real.sqrt csq
    exact Real.sqrt_nonneg _
  have hc'2 : c' ^ 2 = csq := by
    show Real.sqrt csq ^ 2 = csq
    exact Real.sq_sqrt hcsq0.le
  have hkey : 3 * Kav * Cs ≤ c' ^ 2 := by
    rw [hc'2]
    show 3 * Kav * Cs ≤ 3 * Kav * Cs + 1
    linarith
  obtain ⟨εg, hεg, hgreg⟩ := Work.BoseFixB1.gapRegime_of_adm (v := v) hav (c' := c') hc'0
  obtain ⟨εr, hεr, hrreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min εg εr, 1, lt_min hεg hεr, one_pos, ?_⟩
  intro μ hAdm n Φ u hthr hflat
  -- ### the local notation
  let nps : ℝ := Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Φ : Submission.BoseGases.X n → ℝ)
  let Sloc : ℝ := Work.BoseFixB1S.boxFlatCount
      (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Φ : Submission.BoseGases.X n → ℝ)
  let cnt : ℝ := ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
          (fun _ => (1 : ℝ)) (x i)
  let fib : ℝ := Work.BoseFixB1.fibSum h Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ)
  let pair : ℝ := Work.BoseFixB1.pairSum v Work.BoseBox.mValue
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ)
  let sbk : ℝ := Work.BoseFixB1.sbKin (v := v) μ Work.BoseBox.mValue u
      (Φ : Submission.BoseGases.X n → ℝ)
  -- ### the basic facts about the admissible point
  have hAdmg : Work.BoseBoxFix.Adm v εg μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmr : Work.BoseBoxFix.Adm v εr μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  obtain ⟨hR16, hRχ⟩ := hrreg μ hAdm.1 hAdmr.2.1
  have hμ : 0 < μ := hAdm.1
  have hA0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ Work.BoseBox.mValue := by norm_num [Work.BoseBox.mValue]
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  -- ### the arm hypothesis, in the direction used: `cnt ≤ 3 nps`
  have hflat' : Sloc ≤ 2 * nps := hflat
  have hcnt_split : cnt = Sloc + nps := by
    rw [show cnt = (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
              (fun _ => (1 : ℝ)) (x i)) from rfl]
    rw [Work.BoseFixR.SlabCountSplit
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (u := u)
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hℓ hd hΦc]
    rfl
  have hcnt3 : cnt ≤ 3 * nps := by linarith
  -- ### the definitional excited-count payment
  have hgap := Work.BoseFixB1.sbKin_ge_mu_av_cnPlus (v := v) (μ := μ) (c' := c')
    (M := Work.BoseBox.mValue) (u := u) (Φ := (Φ : Submission.BoseGases.X n → ℝ))
    hA0 hμ.le hc'0 (mul_pos hd hℓ) (Work.BoseFixB1.adm_eT_pos hAdm)
    (hgreg μ hAdmg) (Work.BoseFixB1.tBwordKinInd_nonneg _)
  have h1 : c' ^ 2 * μ * _root_.BoseGases.a v * nps ≤ sbk := hgap
  -- ### the fibre loss
  have hfib := Work.BoseFixB1.fibSum_le (v := v) (h := h) (R0 := R) hv hvrad hR hv_supp
    (M := Work.BoseBox.mValue) hM1 hℓ hd hR16 hRχ u hΦc
  have hchi := Work.BoseFixR.chiSum_le_countIntegral (M := Work.BoseBox.mValue) hM1 hℓ hd u hΦc
  have hfib1 : fib ≤ Kav * _root_.BoseGases.a v * (Cs * cnt) := by
    refine le_trans hfib ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKav0 hA0)
    exact hchi
  have hfib2 : fib ≤ Kav * _root_.BoseGases.a v * (Cs * (3 * nps)) := by
    refine le_trans hfib1 ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hKav0 hA0)
    exact mul_le_mul_of_nonneg_left hcnt3 hCs0
  have hfibμ : μ * fib ≤ μ * (Kav * _root_.BoseGases.a v * (Cs * (3 * nps))) :=
    mul_le_mul_of_nonneg_left hfib2 hμ.le
  -- ### the pair term
  have hpair : 0 ≤ pair := Work.BoseFixB1.pairSum_nonneg (v := v) hv (M := Work.BoseBox.mValue)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (u := u)
    (Φ := (Φ : Submission.BoseGases.X n → ℝ))
  -- ### the arithmetic of the cancellation
  have h4 : 0 ≤ c' ^ 2 * μ * _root_.BoseGases.a v * nps
      - μ * (Kav * _root_.BoseGases.a v * (Cs * (3 * nps))) := by
    have hnps0 : 0 ≤ nps := by
      show 0 ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Φ : Submission.BoseGases.X n → ℝ)
      rw [Work.UBBInputs8.cnPlusBoxInd]
      exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
    have hfac : c' ^ 2 * μ * _root_.BoseGases.a v * nps
        - μ * (Kav * _root_.BoseGases.a v * (Cs * (3 * nps)))
        = μ * _root_.BoseGases.a v * nps * (c' ^ 2 - 3 * Kav * Cs) := by ring
    rw [hfac]
    exact mul_nonneg (mul_nonneg (mul_nonneg hμ.le hA0) hnps0) (by linarith [hkey])
  -- ### the split of the sliding word
  have hsb : Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = sbk + (-(μ * fib) + pair) := by
    rw [Work.BoseFixB1.sbWord]
    rw [Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1 hAdm
      hΦc u hR16 hRχ]
    simp only [Work.BoseFixB1.M_eq_mValue]
    rfl
  rw [hsb]
  linarith [h1, hfibμ, hpair, h4]

/-! ## The flat arm (the complement of the proved excited arm), as a hypothesis

`bandExcitedArm` (PROVED above) covers `boxFlatCount ≤ 2·boxQCount`; the missing case of the
target is its complement, i.e. `2·boxQCount ≤ boxFlatCount`, which is what `FlatArmBand` states.
`bandCondensedArm_of_flatArm` below assembles the target from the two arms; the only content that
remains is `FlatArmBand` itself (delegated as `Work.BoseFixB1B.bandFlatArm`). -/

/-- `crudeThreshold` is monotone in the constant `K` — pure arithmetic, no state hypothesis. -/
lemma crudeThreshold_mono_K {v : EuclideanSpace ℝ (Fin 3) → ℝ} {K K' μ : ℝ} {M : ℕ} {ℓ d : ℝ}
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hKK : K ≤ K')
    (hB : 0 ≤ μ * Work.SmallBoxSliding.chiMass M ℓ d u + 1)
    (hJ : 0 ≤ Work.BoseBoxFix.normB v μ n Φ) :
    Work.BoseFixR.crudeThreshold v K μ M ℓ d u Φ
      ≤ Work.BoseFixR.crudeThreshold v K' μ M ℓ d u Φ := by
  simp only [Work.BoseFixR.crudeThreshold]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKK hB) hJ

/-- **The target from the two arms.**  `bandExcitedArm` (PROVED) settles
`boxFlatCount ≤ 2·boxQCount` with the conclusion `0 ≤ sbWord`, whence the bound holds for every
constant `C ≥ 0`; the complementary case is `FlatArmBand`.  The constants are glued as
`ε₀ := min ε_flat ε_exc`, `K := max K_flat K_exc` (the threshold is monotone in `K`) and
`C := C_flat`. -/
theorem bandCondensedArm_of_flatArm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hflat : FlatArmBand v h) :
    ∃ ε₀ K C : ℝ, 0 < ε₀ ∧ 0 < K ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d (4 * μ) →
          Work.BoseFixR.crudeThreshold v K μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1S.boxQCount
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1S.boxFlatCount
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ) →
          -(C * (μ ^ 2 * _root_.BoseGases.a v
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * _root_.BoseGases.a v))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  obtain ⟨εf, Kf, Cf, hεf, hKf, hCf, harmF⟩ := hflat
  obtain ⟨εe, Ke, hεe, hKe, harmE⟩ := bandExcitedArm (v := v) h hv hv1 hvrad hR hv_supp hav
  refine ⟨min εf εe, max Kf Ke, Cf, lt_min hεf hεe,
    lt_of_lt_of_le hKf (le_max_left _ _), hCf, ?_⟩
  intro μ hAdm n Φ u hband hthr hflatH
  have hAdmf : Work.BoseBoxFix.Adm v εf μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdme : Work.BoseBoxFix.Adm v εe μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 < μ := hAdm.1
  have hX0 : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hB0 : 0 ≤ μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ
        (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1 := by
    linarith [mul_nonneg hμ.le hX0]
  have hJ0 : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg _
  by_cases hcase : Work.BoseFixB1S.boxFlatCount
        (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ 2 * Work.BoseFixB1S.boxQCount
        (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Φ : Submission.BoseGases.X n → ℝ)
  · -- the excited arm: `0 ≤ sbWord`, so every `C ≥ 0` works
    have hthrE : Work.BoseFixR.crudeThreshold v Ke μ
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ) :=
      le_trans (crudeThreshold_mono_K (K := Ke) (K' := max Kf Ke) (le_max_right _ _) hB0 hJ0) hthr
    have hword : 0 ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) :=
      harmE μ hAdme n Φ u hthrE hcase
    have hC0 : 0 ≤ Cf := hCf
    have hcoef : 0 ≤ Cf * (μ ^ 2 * _root_.BoseGases.a v
          * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * _root_.BoseGases.a v) :=
      mul_nonneg hC0 (add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) (le_of_lt hav)) hX0)
        (mul_nonneg hμ.le (le_of_lt hav)))
    have : -(Cf * (μ ^ 2 * _root_.BoseGases.a v
          * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * _root_.BoseGases.a v))
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 := by
      rw [neg_mul]
      exact neg_nonpos.mpr (mul_nonneg hcoef hJ0)
    linarith
  · -- the flat arm
    have hthrF : Work.BoseFixR.crudeThreshold v Kf μ
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ) :=
      le_trans (crudeThreshold_mono_K (K := Kf) (K' := max Kf Ke) (le_max_left _ _) hB0 hJ0) hthr
    have h2 : 2 * Work.BoseFixB1S.boxQCount
        (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.BoseFixB1S.boxFlatCount
        (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Φ : Submission.BoseGases.X n → ℝ) := le_of_lt (not_le.mp hcase)
    exact harmF μ hAdmf n Φ u hband hthrF h2

/-! ## The band cutoff domination (piece (H2) of the flat arm)

On the band the smooth cutoff obeys two bounds: `χ_{B(u)} ≤ bandS`
(`Work.BoseFixB1.chiSmallB_le_bandS`) and `χ_{B(u)} = 0` off `dlBox ℓ d u` (its support is in the
small box, `Work.SlotWord.chiSmallB_support_mem_dlBox`).  Hence `χ_{B(u)} ≤ bandS · 1_{dlBox}`,
and summing over the slots and integrating against `Φ²` gives the band count bound
`occChi ≤ bandS · cnt` — the quantitative ingress of the flat arm (it removes the particle number
that the naive `Cs`-bound, `chiSum_le_countIntegral`, leaves behind). -/

/-- On the band, the cutoff is dominated by `bandS` times its own box indicator. -/
theorem chiSmallB_le_bandS_indicator {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (hμ : 0 < μ) {u x : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.bandSet ℓ d μ) :
    Submission.BoseGases.chiSmallB M ℓ d u x
      ≤ Work.BoseFixB1.bandS M ℓ d μ
          * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
  · rw [Set.indicator_of_mem hx, mul_one]
    exact Work.BoseFixB1.chiSmallB_le_bandS hM hℓ hd hμ hu x
  · rw [Set.indicator_of_notMem hx, mul_zero]
    have h0 : Submission.BoseGases.chiSmallB M ℓ d u x = 0 := by
      by_contra hne
      exact hx (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hne)
    rw [h0]

/-- **The band count bound**: the `χ_{B(u)}`-weighted count is at most `bandS` times the
box-indicator count `Σᵢ ∫_{abox} Φ² 1_{B(u)}(xᵢ)`. -/
theorem occChi_le_bandS_count {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hμ : 0 < μ) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.bandSet ℓ d μ) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixR.occChi M ℓ d u Φ
      ≤ Work.BoseFixB1.bandS M ℓ d μ *
          (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) := by
  classical
  have hBmeas : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hBac : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hs0 : 0 ≤ Work.BoseFixB1.bandS M ℓ d μ := Work.BoseFixB1.bandS_nonneg M ℓ d μ
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiSmallB M ℓ d u z
        ≤ Work.BoseFixB1.bandS M ℓ d μ
            * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z :=
    fun z => chiSmallB_le_bandS_indicator hM hℓ hd hμ hu
  have hsum : ∀ x : Submission.BoseGases.X n,
      (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
        ≤ Work.BoseFixB1.bandS M ℓ d μ *
            ∑ i : Fin n, (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) := by
    intro x
    calc (∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
        ≤ ∑ i : Fin n, Work.BoseFixB1.bandS M ℓ d μ *
            (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) :=
          Finset.sum_le_sum fun i _ => hpt (x i)
      _ = Work.BoseFixB1.bandS M ℓ d μ *
            ∑ i : Fin n, (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) := by
          rw [Finset.mul_sum]
  have hGint : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
        ∑ i : Fin n, (Φ x) ^ 2
          * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    integrable_finsetSum (s := Finset.univ)
      (f := fun i (x : Submission.BoseGases.X n) => (Φ x) ^ 2
        * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i))
      (fun i _ => by
        have h1 := Work.BoseFixB1S.integrableOn_phi_sq_indicator
          (c := (1 : ℝ)) hℓ hBmeas hBac i hΦc
        rw [MeasureTheory.IntegrableOn] at h1
        simpa only [one_mul] using h1)
  have hmono : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseFixB1.bandS M ℓ d μ *
        (∑ i : Fin n, (Φ x) ^ 2
          * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun i _ => Submission.BoseGases.chiSmallB_nonneg M ℓ d u (x i)))
      (hGint.const_mul _) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    calc (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i)
        ≤ (Φ x) ^ 2 * (Work.BoseFixB1.bandS M ℓ d μ *
            ∑ i : Fin n, (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) :=
          mul_le_mul_of_nonneg_left (hsum x) (sq_nonneg _)
      _ = Work.BoseFixB1.bandS M ℓ d μ *
            ∑ i : Fin n, (Φ x) ^ 2
              * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) := by
          rw [← mul_assoc, mul_comm ((Φ x) ^ 2) (Work.BoseFixB1.bandS M ℓ d μ), mul_assoc,
            Finset.mul_sum]
  calc Work.BoseFixR.occChi M ℓ d u Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
          ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) := rfl
    _ ≤ ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseFixB1.bandS M ℓ d μ *
        (∑ i : Fin n, (Φ x) ^ 2
          * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) := hmono
    _ = Work.BoseFixB1.bandS M ℓ d μ *
          (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i)) := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [MeasureTheory.integral_finsetSum]
        exact fun i _ => by
          have h1 := Work.BoseFixB1S.integrableOn_phi_sq_indicator
            (c := (1 : ℝ)) hℓ hBmeas hBac i hΦc
          rw [MeasureTheory.IntegrableOn] at h1
          simpa only [one_mul] using h1

/-! ## The band-sharp core inequality (piece (H3) of the flat arm)

`sbCore` (PROVED) reads `sbWord ≥ c'²μ(a v)·n₊ − μ·kav·(a v)·occChi`.  On the band, (H2)
(`occChi_le_bandS_count`) replaces the `χ`-count by `bandS · cnt`, so the *fibre loss carries the
band factor* `bandS` and **no particle number survives** — this is what makes the flat arm's
residual a statement about the flat count `S = boxFlatCount` alone (use
`Work.BoseFixR.SlabCountSplit`, `cnt = S + n₊`, and flatness `n₊ ≤ S`). -/
theorem sbCoreBand {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (c' : ℝ) (hc' : 0 ≤ c') :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d (4 * μ) →
          c' ^ 2 * μ * (_root_.BoseGases.a v)
              * Work.BoseFixB1S.boxQCount
                  (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                  (Φ : Submission.BoseGases.X n → ℝ)
            - μ * kav * (_root_.BoseGases.a v)
              * (Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d (4 * μ)
                * ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                    ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
                      (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
                        (fun _ => (1 : ℝ)) (x i))
          ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  classical
  obtain ⟨ε₀, hε₀, hcore⟩ :=
    Work.BoseFixB1B.sbCore (v := v) h hv hv1 hvrad hR hv_supp hav c' hc'
  refine ⟨ε₀, hε₀, ?_⟩
  intro μ hAdm n Φ u hu
  have hμ : 0 < μ := hAdm.1
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hband := occChi_le_bandS_count
    (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := 4 * μ)
    (u := u) (n := n) (Φ := (Φ : Submission.BoseGases.X n → ℝ))
    hM hℓ hd (by linarith) hu hΦc
  have hchi : Work.BoseFixB1.chiSum (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d (4 * μ)
        * ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
                (fun _ => (1 : ℝ)) (x i) := by
    simpa only [Work.BoseFixR.occChi, Work.BoseFixB1.chiSum] using hband
  have hmono : μ * kav * (_root_.BoseGases.a v)
        * Work.BoseFixB1.chiSum (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : Submission.BoseGases.X n → ℝ)
      ≤ μ * kav * (_root_.BoseGases.a v)
        * (Work.BoseFixB1.bandS (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d (4 * μ)
            * ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 *
                  (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
                    (fun _ => (1 : ℝ)) (x i)) :=
    mul_le_mul_of_nonneg_left hchi
      (mul_nonneg (mul_nonneg (le_of_lt hμ) Work.BoseFixB1B.kav_nonneg) (le_of_lt hav))
  have hcore' := hcore μ hAdm n Φ u
  have hq : Work.BoseFixB1S.boxQCount
        (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        (Φ : Submission.BoseGases.X n → ℝ)
      = Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          (Φ : Submission.BoseGases.X n → ℝ) := rfl
  rw [hq]
  linarith [hcore', hmono]

theorem bandCondensedArm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ K C : ℝ, 0 < ε₀ ∧ 0 < K ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d (4 * μ) →
          Work.BoseFixR.crudeThreshold v K μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixR.occChi (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1S.boxQCount
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1S.boxFlatCount
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ) →
          -(C * (μ ^ 2 * _root_.BoseGases.a v
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * _root_.BoseGases.a v))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by sorry

end Work.BoseFixB1B
