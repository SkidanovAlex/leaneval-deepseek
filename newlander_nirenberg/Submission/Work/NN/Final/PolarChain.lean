/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The level-by-level `C^{k,α}` smoothness of the polar extension

This module proves that the iterated polar (radial Seeley) extension of a seed which is
`C^k` *and* has finite `C^{k,α}` norm on the larger polydisc `pd n ρ (3/2)` is `C^k` with finite
`C^{k,α}` norm on the chain regions `cvReg n ρ j` of `PolarChainDefs.lean`, and that the iterates
of the junk seed `polarReg n ρ hρ v` agree with those of an honest seed on the regions `Z_j`.
-/
import Mathlib
import Submission.Work.NN.Final.PolarChainDefs
import Submission.Work.NN.Final.holderNorm_comp_flatPoint
import Submission.Work.NN.Final.holderNorm_union_le_of_separated
import Submission.Work.NN.Final.PolarChainStep
import Submission.Work.NN.Final.PolarChainSeeley
import Submission.Work.NN.Final.iterExt_eq_iterateFrom
import Submission.Work.NN.Final.HolderCongr
import Submission.Work.CR.Flat.Holder.holderNorm_comp_le_of_contDiffOn
import Submission.Work.NN.PolarChain.polarChart_comp_cvAnn
import Submission.Work.NN.PolarChain.flatPoint_comp_cvFlat

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set Filter

namespace Work.NN.Final

variable {n : ℕ} {ρ : Fin n → ℝ}

/-! ## Structural lemmas for the chain regions -/

/-- The region `cvReg n ρ n` is contained in `pd n ρ 2`. -/
lemma cvReg_last_subset_pd_two (n : ℕ) (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) :
    cvReg n ρ n ⊆ pd n ρ 2 := by
  intro z hz
  rw [mem_cvReg] at hz
  rw [mem_pd]
  intro i
  have h := hz.1 i i.isLt
  have hc : chainC n n < 2 := by
    rw [chainC]
    have h1 : (n : ℝ) / (8 * ((n : ℝ) + 1)) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hp := hρ i
  nlinarith

/-- `chainD n j ≤ Real.exp 1` for `j ≤ n`. -/
lemma chainD_le_exp_one (n j : ℕ) (hj : j ≤ n) : chainD n j ≤ Real.exp 1 := by
  have h4 : (j : ℝ) / (8 * ((n : ℝ) + 1)) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    have : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hj
    linarith
  rw [chainD]
  have h3 : (2 : ℝ) + 1 / 8 < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num at h
    linarith
  linarith

/-- The inner region of level `j` is contained in the level-`(j+1)` chain region. -/
lemma cvInner_subset_cvReg_succ (hρ : ∀ i, 0 < ρ i) (j : Fin n) :
    cvInner n ρ j ⊆ cvReg n ρ ((j : ℕ) + 1) := by
  intro z hz
  rw [mem_cvInner] at hz
  obtain ⟨h1, hj, h3⟩ := hz
  rw [mem_cvReg]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
    · have hlt' := h1 i hlt
      have hmono : chainC n (j : ℕ) ≤ chainC n ((j : ℕ) + 1) := chainC_mono n (Nat.le_succ _)
      have hp := hρ i
      nlinarith
    · have hji : i = j := Fin.ext heq
      rw [hji]
      have hc : (1 : ℝ) < chainC n ((j : ℕ) + 1) := chainC_gt_one n ((j : ℕ) + 1)
      have hp := hρ j
      nlinarith
  · have hlt' := h3 i (by omega)
    have hmono : chainD n (j : ℕ) ≤ chainD n ((j : ℕ) + 1) := chainD_mono n (Nat.le_succ _)
    have hp := hρ i
    nlinarith

/-- The level-`j` chain region is covered by the inner region and the annulus region. -/
lemma cvReg_subset_cvInner_union_cvAnn (hρ : ∀ i, 0 < ρ i) (j : Fin n)
    (hj : (j : ℕ) ≤ n) :
    cvReg n ρ (j : ℕ) ⊆ cvInner n ρ j ∪ cvAnn n ρ j 1 := by
  intro z hz
  rw [mem_cvReg] at hz
  obtain ⟨h1, h2⟩ := hz
  rcases lt_or_ge ‖z j‖ (ρ j * (3 / 4)) with hlt | hge
  · refine Or.inl ?_
    rw [mem_cvInner]
    exact ⟨fun i hi => h1 i (by omega), hlt, fun i hi => h2 i (by omega)⟩
  · refine Or.inr ?_
    rw [mem_cvAnn]
    refine ⟨fun i hi => h1 i (by omega), ⟨?_, ?_⟩, fun i hi => h2 i (by omega)⟩
    · have hp := hρ j
      linarith
    · have hb := h2 j le_rfl
      have hexp := chainD_le_exp_one n (j : ℕ) hj
      have hp := hρ j
      nlinarith

/-! ## The logarithmic chart and the flat fibre map -/

/-- The chart is a section of the fibre map: `flatPoint` of `polarChart z` is `z`. -/
lemma flatPoint_polarChart' {j : Fin n} (hρ : 0 < ρ j) {z : Fin n → ℂ} (hz : z j ≠ 0) :
    flatPoint n ρ j (polarChart n ρ j z) = z := by
  rw [flatPoint, polarChart_apply, Function.update_eq_self_iff]
  have hr : 0 < ‖z j‖ := norm_pos_iff.mpr hz
  have hx : 0 < ρ j / ‖z j‖ := div_pos hρ hr
  have hexp : Real.exp (-Real.log (ρ j / ‖z j‖)) = (ρ j / ‖z j‖)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hx]
  have h2 : ρ j * (ρ j / ‖z j‖)⁻¹ / ‖z j‖ = 1 := by
    rw [inv_div]
    field_simp
  rw [hexp, h2, Complex.ofReal_one, one_mul]

/-- The global model of the flat fibre map agrees with it on the chain flat region. -/
lemma flatGlob_eq_flatPoint_cvFlat {j : Fin n} (hρ : 0 < ρ j) {p : (Fin n → ℂ) × ℝ}
    (hp : p.1 ∈ cvFlat n ρ j) :
    flatGlob n ρ j (ρ j / 4) p = flatPoint n ρ j p := by
  rw [mem_cvFlat] at hp
  obtain ⟨h1, ⟨hj1, hj2⟩, h3⟩ := hp
  have hε : (0 : ℝ) < ρ j / 4 := by linarith
  have hεj : ρ j / 4 < ‖p.1 j‖ := by linarith
  rw [flatGlob, flatPoint]
  congr 1
  have hstep : radialStep ((3 * (ρ j / 4)) / 8) ((3 * (ρ j / 4)) / 3) ‖p.1 j‖ = 1 := by
    refine radialStep_of_ge (by linarith) ?_
    linarith
  rw [ChartComp.u0, hstep, Complex.ofReal_one, one_mul, ChartComp.dirn, Complex.ofReal_div]
  ring

/-- The flat fibre map is `C^k` on the flat chain region with the height variable non-negative. -/
lemma contDiffOn_flatPoint_cvFlat {j : Fin n} (hρ : 0 < ρ j) (k : ℕ) :
    ContDiffOn ℝ (k : WithTop ENat) (flatPoint n ρ j)
      (cvFlat n ρ j ×ˢ {t : ℝ | 0 ≤ t}) := by
  have hε : (0 : ℝ) < ρ j / 4 := by linarith
  have h1 : ContDiffOn ℝ (k : WithTop ENat) (flatGlob n ρ j (ρ j / 4))
      (cvFlat n ρ j ×ˢ {t : ℝ | 0 ≤ t}) :=
    (((contDiff_flatGlob (n := n) (ρ := ρ) (j := j) (ε := ρ j / 4) hε).contDiffOn).of_le
      (ChartComp.natCast_le_top_nat k))
  exact h1.congr (fun p hp => (flatGlob_eq_flatPoint_cvFlat hρ hp.1).symm)

/-- The chart is `C^k` on the annulus region of the `j`-th step. -/
lemma contDiffOn_polarChart_cvAnn {j : Fin n} (hρ : 0 < ρ j) (k : ℕ) :
    ContDiffOn ℝ (k : WithTop ENat) (polarChart n ρ j) (cvAnn n ρ j 1) := by
  have hε : (0 : ℝ) < ρ j / 4 := by linarith
  have h1 : ContDiffOn ℝ (k : WithTop ENat) (polarGlob n ρ j (ρ j / 4)) (cvAnn n ρ j 1) :=
    ((contDiff_polarGlob (n := n) (ρ := ρ) (j := j) (ε := ρ j / 4) hε).contDiffOn).of_le
      (ChartComp.natCast_le_top_nat k)
  refine h1.congr (fun z hz => ?_)
  rw [mem_cvAnn] at hz
  obtain ⟨h1', ⟨hj1, hj2⟩, h3'⟩ := hz
  exact (polarGlob_eq_polarChart hε hρ (by linarith)).symm

/-- The chart maps the annulus region into the flat region, with the logarithmic coordinate
in `(-1, ∞)`. -/
lemma polarChart_mapsTo_cvFlat {j : Fin n} (hρ : 0 < ρ j) :
    Set.MapsTo (polarChart n ρ j) (cvAnn n ρ j 1)
      (cvFlat n ρ j ×ˢ {t : ℝ | -(1 : ℝ) < t}) := by
  intro z hz
  rw [mem_cvAnn] at hz
  obtain ⟨h1, ⟨hj1, hj2⟩, h3⟩ := hz
  have hr : 0 < ‖z j‖ := by linarith
  refine Set.mem_prod.mpr ⟨?_, ?_⟩
  · change z ∈ cvFlat n ρ j
    rw [mem_cvFlat]
    refine ⟨h1, ⟨by linarith, ?_⟩, h3⟩
    have hpos : 0 < ρ j := hρ
    calc ‖z j‖ < ρ j * Real.exp 1 := hj2
      _ < ρ j * 3 := mul_lt_mul_of_pos_left Real.exp_one_lt_three hpos
      _ = 3 * ρ j := by ring
  · change -(1 : ℝ) < Real.log (ρ j / ‖z j‖)
    have h3 : Real.exp (-1) * ‖z j‖ < ρ j := by
      calc Real.exp (-1) * ‖z j‖ < Real.exp (-1) * (ρ j * Real.exp 1) :=
            mul_lt_mul_of_pos_left hj2 (Real.exp_pos (-1))
        _ = ρ j := by
            rw [← mul_assoc, mul_comm (Real.exp (-1)) (ρ j), mul_assoc, ← Real.exp_add]
            simp
    have h2 : Real.exp (-1) < ρ j / ‖z j‖ := by
      rw [lt_div_iff₀ hr]
      calc Real.exp (-1) * ‖z j‖ = ‖z j‖ * Real.exp (-1) := by ring
        _ < ρ j := by rw [mul_comm ‖z j‖ (Real.exp (-1))]; exact h3
    have h5 := Real.log_lt_log (Real.exp_pos (-1)) h2
    rwa [Real.log_exp] at h5


/-! ## The level-by-level smoothness of the iterates -/

/-- **The iterates of an honest seed are `C^k` with finite `C^{k,α}` norm on the chain regions.**

If the seed `w` is `C^k` with finite `C^{k,α}` norm on the polydisc `pd n ρ 2`, then each
partial iterate `iterateFrom n ρ a b j w` (extending the coordinates `j, …, n-1`) is `C^k` with
finite `C^{k,α}` norm on `cvReg n ρ j`. -/
theorem iterateFrom_contDiffOn_cvReg {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j)
    {k : ℕ} {w : (Fin n → ℂ) → ℂ} (hw : ContDiffOn ℝ (k : WithTop ENat) w (pd n ρ 2))
    (hwfin : Work.CR.Flat.holderNorm k α w (pd n ρ 2) ≠ ⊤) :
    ∀ j ≤ n, ContDiffOn ℝ (k : WithTop ENat) (iterateFrom n ρ a b j w) (cvReg n ρ j) ∧
      Work.CR.Flat.holderNorm k α (iterateFrom n ρ a b j w) (cvReg n ρ j) ≠ ⊤ := by
  -- the one-step estimate
  obtain ⟨CS, hCS0, hCS⟩ := seeleyRegionEstimateNoGlue (E := Fin n → ℂ) hα0 hα1 hb hbT ha hsum
  have key : ∀ t, ∀ j, n - j = t → j ≤ n →
      ContDiffOn ℝ (k : WithTop ENat) (iterateFrom n ρ a b j w) (cvReg n ρ j) ∧
        Work.CR.Flat.holderNorm k α (iterateFrom n ρ a b j w) (cvReg n ρ j) ≠ ⊤ := by
    intro t
    induction t with
    | zero =>
      intro j hjeq hj
      have hjn : j = n := by omega
      rw [hjn, iterateFrom_of_le (le_refl n)]
      exact ⟨hw.mono (cvReg_last_subset_pd_two n ρ hρ),
        ne_top_of_le_ne_top hwfin
          (Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ 2) (isOpen_cvReg hρ n)
            (cvReg_last_subset_pd_two n ρ hρ) k α w)⟩
    | succ t ih =>
      intro j hjeq hj
      have hjlt : j < n := by omega
      have ihj : ContDiffOn ℝ (k : WithTop ENat) (iterateFrom n ρ a b (j + 1) w)
            (cvReg n ρ (j + 1)) ∧
          Work.CR.Flat.holderNorm k α (iterateFrom n ρ a b (j + 1) w) (cvReg n ρ (j + 1)) ≠ ⊤ :=
        ih (j + 1) (by omega) (by omega)
      obtain ⟨hΦsm, hΦfin⟩ := ihj
      rw [iterateFrom_of_lt hjlt]
      set jj : Fin n := ⟨j, hjlt⟩ with hjj
      set Φ : (Fin n → ℂ) → ℂ := iterateFrom n ρ a b (j + 1) w with hΦ
      have hΦsm' : ContDiffOn ℝ (k : WithTop ENat) Φ (cvReg n ρ ((jj : ℕ) + 1)) := hΦsm
      have hΦfin' : Work.CR.Flat.holderNorm k α Φ (cvReg n ρ ((jj : ℕ) + 1)) ≠ ⊤ := hΦfin
      obtain ⟨Cu, hCu0, hCu⟩ :=
        holderNorm_union_le_of_separated (E := Fin n → ℂ) hα0 (η := ρ jj / 4) (by linarith [hρ jj])
      -- the three sets
      have hAopen : IsOpen (cvInner n ρ jj) := isOpen_cvInner hρ jj
      have hBopen : IsOpen (cvAnn n ρ jj 1) := isOpen_cvAnn hρ jj 1
      obtain ⟨Cf, hCf0, hCf⟩ :=
        Work.NN.PolarChain.flatPoint_comp_cvFlat (n := n) (ρ := ρ) hρ hα0 hα1 jj
      obtain ⟨Cp, hCp0, hCp⟩ :=
        Work.NN.PolarChain.polarChart_comp_cvAnn (n := n) (ρ := ρ) hρ hα0 hα1 jj
      -- the input of the flat Seeley estimate
      have hg_sm : ContDiffOn ℝ (k : WithTop ENat) (flatPull n ρ jj Φ)
          (cvFlat n ρ jj ×ˢ {t : ℝ | 0 ≤ t}) :=
        hΦsm'.comp (contDiffOn_flatPoint_cvFlat (hρ jj) k) (flatPoint_mapsTo_cvReg hρ jj)
      have hgfin : Work.CR.Flat.holderNorm k α (flatPull n ρ jj Φ)
          (cvFlat n ρ jj ×ˢ {t : ℝ | 0 < t}) ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΦfin')
          (hCf k Φ hΦsm')
      obtain ⟨hsee_sm, hsee_bnd⟩ := hCS k 1 (by norm_num) (cvFlat n ρ jj) (flatPull n ρ jj Φ)
        (isOpen_cvFlat hρ jj) hg_sm hgfin
      -- the composite with the chart
      have hcomp_sm : ContDiffOn ℝ (k : WithTop ENat)
          (fun z => seeleyExt a b (flatPull n ρ jj Φ) (polarChart n ρ jj z)) (cvAnn n ρ jj 1) :=
        hsee_sm.comp (contDiffOn_polarChart_cvAnn (hρ jj) k) (polarChart_mapsTo_cvFlat (hρ jj))
      -- the identification of the extension with the composite on the annulus
      have hD2eq : ∀ z ∈ cvAnn n ρ jj 1,
          radialExt n ρ a b jj Φ z = seeleyExt a b (flatPull n ρ jj Φ) (polarChart n ρ jj z) := by
        intro z hz
        rw [mem_cvAnn] at hz
        obtain ⟨hh1, ⟨hh2, hh3⟩, hh4⟩ := hz
        have hzpos : 0 < ‖z jj‖ := by linarith [hρ jj]
        have hzne : z jj ≠ 0 := norm_pos_iff.mp hzpos
        rcases le_or_gt ‖z jj‖ (ρ jj) with hle | hgt
        · rw [radialExt_of_le hle]
          have hnn : 0 ≤ (polarChart n ρ jj z).2 := by
            rw [polarChart_apply]
            exact Real.log_nonneg (by rw [le_div_iff₀ hzpos]; simpa using hle)
          rw [seeleyExt_of_nonneg a b (flatPull n ρ jj Φ) hnn]
          simp only [flatPull_apply, ← polarChart_apply, flatPoint_polarChart' (hρ jj) hzne]
        · exact radialExt_seeleyExt_flat jj (hρ jj) a b Φ hzne
      -- smoothness on the two pieces
      have hD1 : ContDiffOn ℝ (k : WithTop ENat) (radialExt n ρ a b jj Φ) (cvInner n ρ jj) :=
        (hΦsm'.mono (cvInner_subset_cvReg_succ hρ jj)).congr
          (fun z hz => radialExt_of_le (by
            have h := (mem_cvInner.mp hz).2.1
            have hp := hρ jj
            linarith))
      have hD2 : ContDiffOn ℝ (k : WithTop ENat) (radialExt n ρ a b jj Φ) (cvAnn n ρ jj 1) :=
        hcomp_sm.congr (fun z hz => hD2eq z hz)
      have hUnion : ContDiffOn ℝ (k : WithTop ENat) (radialExt n ρ a b jj Φ)
          (cvInner n ρ jj ∪ cvAnn n ρ jj 1) :=
        radialEst_contDiffOn_union_of_isOpen hAopen hBopen hD1 hD2
      refine ⟨hUnion.mono (cvReg_subset_cvInner_union_cvAnn hρ jj hj), ?_⟩
      -- the finiteness
      have hsep : ∀ x ∈ cvInner n ρ jj, x ∉ cvAnn n ρ jj 1 →
          ∀ y ∈ cvAnn n ρ jj 1, y ∉ cvInner n ρ jj → ρ jj / 4 ≤ ‖x - y‖ := by
        intro x hx hxB y hy hyA
        have hxle : ‖x jj‖ ≤ ρ jj / 2 := by
          by_contra hcon
          refine hxB ?_
          rw [mem_cvAnn]
          refine ⟨(mem_cvInner.mp hx).1, ⟨lt_of_not_ge hcon, ?_⟩, (mem_cvInner.mp hx).2.2⟩
          have hx' := (mem_cvInner.mp hx).2.1
          have he := Real.exp_one_gt_two
          have hp := hρ jj
          nlinarith
        have hyge : ρ jj * (3 / 4) ≤ ‖y jj‖ := by
          by_contra hcon
          refine hyA ?_
          rw [mem_cvInner]
          exact ⟨(mem_cvAnn.mp hy).1, lt_of_not_ge hcon, (mem_cvAnn.mp hy).2.2⟩
        have h1 : ‖y jj - x jj‖ ≤ ‖y - x‖ := by
          simpa only [Pi.sub_apply] using norm_le_pi_norm (y - x) jj
        have h2 : ρ jj / 4 ≤ ‖y jj - x jj‖ := by
          have h3 : ‖y jj‖ - ‖x jj‖ ≤ ‖y jj - x jj‖ :=
            le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)
          have hp := hρ jj
          nlinarith
        rw [norm_sub_rev x y]
        linarith [h1, h2]
      have hbound := hCu k (radialExt n ρ a b jj Φ) (cvInner n ρ jj) (cvAnn n ρ jj 1)
        hAopen hBopen hUnion hsep
      refine ne_top_of_le_ne_top ?_ (le_trans
        (Work.CR.Flat.holderNorm_mono_set (hAopen.union hBopen) (isOpen_cvReg hρ j)
          (cvReg_subset_cvInner_union_cvAnn hρ jj hj) k α (radialExt n ρ a b jj Φ))
        hbound)
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((ENNReal.add_ne_top).mpr ⟨?_, ?_⟩)
      · exact ne_top_of_le_ne_top hΦfin'
          (le_trans (holderNorm_congr_of_isOpen hAopen
              (fun z hz => radialExt_of_le (by
                have h := (mem_cvInner.mp hz).2.1
                have hp := hρ jj
                linarith)) k α).le
            (Work.CR.Flat.holderNorm_mono_set (isOpen_cvReg hρ (j + 1)) hAopen
              (cvInner_subset_cvReg_succ hρ jj) k α Φ))
      · have hbnd : Work.CR.Flat.holderNorm k α (radialExt n ρ a b jj Φ) (cvAnn n ρ jj 1) ≤
            ENNReal.ofReal (Cp k) * (ENNReal.ofReal (CS k) * (ENNReal.ofReal (Cf k) *
              Work.CR.Flat.holderNorm k α Φ (cvReg n ρ ((jj : ℕ) + 1)))) := by
          calc Work.CR.Flat.holderNorm k α (radialExt n ρ a b jj Φ) (cvAnn n ρ jj 1)
              = Work.CR.Flat.holderNorm k α
                  (fun z => seeleyExt a b (flatPull n ρ jj Φ) (polarChart n ρ jj z))
                  (cvAnn n ρ jj 1) :=
                holderNorm_congr_of_isOpen hBopen (fun z hz => hD2eq z hz) k α
            _ ≤ ENNReal.ofReal (Cp k) * Work.CR.Flat.holderNorm k α
                  (seeleyExt a b (flatPull n ρ jj Φ))
                  (cvFlat n ρ jj ×ˢ {t : ℝ | -(1:ℝ) < t}) :=
                hCp k (seeleyExt a b (flatPull n ρ jj Φ)) hsee_sm
            _ ≤ ENNReal.ofReal (Cp k) * (ENNReal.ofReal (CS k) *
                  Work.CR.Flat.holderNorm k α (flatPull n ρ jj Φ)
                    (cvFlat n ρ jj ×ˢ {t : ℝ | 0 < t})) :=
                mul_le_mul' le_rfl hsee_bnd
            _ ≤ ENNReal.ofReal (Cp k) * (ENNReal.ofReal (CS k) * (ENNReal.ofReal (Cf k) *
                  Work.CR.Flat.holderNorm k α Φ (cvReg n ρ ((jj : ℕ) + 1)))) :=
                mul_le_mul' le_rfl (mul_le_mul' le_rfl (hCf k Φ hΦsm'))
        exact ne_top_of_le_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΦfin'))) hbnd
  intro j hj
  exact key (n - j) j rfl hj


/-! ## Agreement of the iterates of the junk seed with those of an honest seed -/

/-- On the region `Z_j = {i < j: ‖·‖ ≤ ρ i} ∩ {i ≥ j: ‖·‖ < 2 ρ i}` the iterates of two seeds
which agree on the closed polydisc coincide. -/
theorem iterateFrom_eqOn_of_eqOn_closed {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m) {v w : (Fin n → ℂ) → ℂ}
    (hvw : ∀ ζ : Fin n → ℂ, (∀ i, ‖ζ i‖ ≤ ρ i) → polarReg n ρ hρ v ζ = w ζ) :
    ∀ j, ∀ z : Fin n → ℂ,
      (∀ i : Fin n, (i : ℕ) < j → ‖z i‖ ≤ ρ i) →
      (∀ i : Fin n, j ≤ (i : ℕ) → ‖z i‖ < 2 * ρ i) →
      iterateFrom n ρ a b j (polarReg n ρ hρ v) z = iterateFrom n ρ a b j w z := by
  have hb1 : ∀ m : ℕ, 1 ≤ b m := fun m => le_trans (by norm_num) (hb m)
  have key : ∀ t, ∀ j, n - j = t → ∀ z : Fin n → ℂ,
      (∀ i : Fin n, (i : ℕ) < j → ‖z i‖ ≤ ρ i) →
      (∀ i : Fin n, j ≤ (i : ℕ) → ‖z i‖ < 2 * ρ i) →
      iterateFrom n ρ a b j (polarReg n ρ hρ v) z = iterateFrom n ρ a b j w z := by
    intro t
    induction t with
    | zero =>
      intro j hjeq z h1 h2
      have hjn : n ≤ j := by omega
      rw [iterateFrom_of_le hjn (polarReg n ρ hρ v), iterateFrom_of_le hjn w]
      exact hvw z (fun i => h1 i (by omega))
    | succ t ih =>
      intro j hjeq z h1 h2
      have hjlt : j < n := by omega
      rw [iterateFrom_of_lt hjlt, iterateFrom_of_lt hjlt]
      set jj : Fin n := ⟨j, hjlt⟩ with hjj
      rcases le_or_gt ‖z jj‖ (ρ jj) with hle | hgt
      · rw [radialExt_of_le hle, radialExt_of_le hle]
        exact ih (j + 1) (by omega) z
          (fun i hi => by
            rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
            · exact h1 i hlt
            · have hji : i = jj := Fin.ext heq
              rw [hji]; exact hle)
          (fun i hi => h2 i (by omega))
      · rw [radialExt_of_gt hgt, radialExt_of_gt hgt]
        refine tsum_congr fun m => ?_
        simp only [radialTerm]
        congr 2
        exact ih (j + 1) (by omega) (Function.update z jj (polarRefl n ρ b m jj z))
          (fun i hi => by
            rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
            · rw [Function.update_apply, if_neg (fun h : i = jj => (ne_of_lt hlt) (congrArg Fin.val h))]
              exact h1 i hlt
            · have hji : i = jj := Fin.ext heq
              rw [hji, Function.update_self]
              exact norm_polarRefl_le hρ hb1 m jj z)
          (fun i hi => by
            rw [Function.update_apply,
              if_neg (fun h : i = jj => (ne_of_lt (by omega : (j:ℕ) < (i:ℕ))) (congrArg Fin.val h).symm)]
            exact h2 i (by omega))
  intro j z h1 h2
  exact key (n - j) j rfl z h1 h2

/-! ## The `C^{k,α}` estimate for the iterates of the junk seed -/

/-- **The chain of one-step estimates.**  If `v` is `C^k` on `pd n ρ 3` with finite `C^{k,α}`
norm on `pd n ρ 1`, and `w` is an honest seed which agrees with `polarReg n ρ hρ v` on the closed
polydisc (with finite `C^{k,α}` norm on `pd n ρ 2`), then the zeroth iterate of the junk seed
satisfies the `C^{k,α}` estimate on `pd n ρ 2` in terms of the norm of `v` on `pd n ρ 1`. -/
theorem iterateFrom_polarReg_holderNorm_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j)
    {C : ℕ → ℝ} (hC0 : ∀ k, 0 < C k)
    (hC : ∀ (k : ℕ) (j : Fin n) (G : (Fin n → ℂ) → ℂ),
      ContDiffOn ℝ (k : WithTop ENat) G (oneSidedRegion n ρ (j : ℕ)) →
      Work.CR.Flat.holderNorm k α G (inRegion n ρ j) ≠ ⊤ →
      Work.CR.Flat.holderNorm k α (radialExt n ρ a b j G) (outRegion n ρ j)
        ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α G (inRegion n ρ j))
    {k : ℕ} {v w : (Fin n → ℂ) → ℂ}
    (hvsm : ContDiffOn ℝ (k : WithTop ENat) v (pd n ρ 3))
    (hvfin : Work.CR.Flat.holderNorm k α v (pd n ρ 1) ≠ ⊤)
    (hwsm : ContDiffOn ℝ (k : WithTop ENat) w (pd n ρ 2))
    (hwfin : Work.CR.Flat.holderNorm k α w (pd n ρ 2) ≠ ⊤)
    (hvw : ∀ ζ : Fin n → ℂ, (∀ i, ‖ζ i‖ ≤ ρ i) → polarReg n ρ hρ v ζ = w ζ) :
    Work.CR.Flat.holderNorm k α (iterateFrom n ρ a b 0 (polarReg n ρ hρ v)) (pd n ρ 2)
      ≤ ENNReal.ofReal ((C k) ^ n) * Work.CR.Flat.holderNorm k α v (pd n ρ 1) := by
  have hmod := iterateFrom_contDiffOn_cvReg (n := n) (ρ := ρ) hρ hα0 hα1 hb hbT ha hsum hwsm hwfin
  have hchain : ∀ t, ∀ j, n - j = t → j ≤ n →
      Work.CR.Flat.holderNorm k α (iterateFrom n ρ a b j (polarReg n ρ hρ v)) (stepRegion n ρ j)
          ≠ ⊤ ∧
      Work.CR.Flat.holderNorm k α (iterateFrom n ρ a b j (polarReg n ρ hρ v)) (stepRegion n ρ j)
        ≤ (ENNReal.ofReal (C k)) ^ (n - j) * Work.CR.Flat.holderNorm k α v (pd n ρ 1) := by
    intro t
    induction t with
    | zero =>
      intro j hjeq hj
      have hjn : j = n := by omega
      rw [hjn, iterateFrom_of_le (le_refl n), stepRegion_last]
      have heq : Work.CR.Flat.holderNorm k α (polarReg n ρ hρ v) (pd n ρ 1)
          = Work.CR.Flat.holderNorm k α v (pd n ρ 1) :=
        holderNorm_congr_of_isOpen (isOpen_pd ρ 1) (fun z hz => polarReg_of_mem hρ v hz) k α
      refine ⟨?_, ?_⟩
      · rw [heq]; exact hvfin
      · rw [heq, Nat.sub_self, pow_zero, one_mul]
    | succ t ih =>
      intro j hjeq hj
      have hjlt : j < n := by omega
      have ihj := ih (j + 1) (by omega) (by omega)
      obtain ⟨ihfin, ihbnd⟩ := ihj
      set jj : Fin n := ⟨j, hjlt⟩ with hjj
      -- (H1): the smoothness hypothesis, transported from the honest model
      have hΦsm : ContDiffOn ℝ (k : WithTop ENat) (iterateFrom n ρ a b (j + 1) w)
          (cvReg n ρ ((jj : ℕ) + 1)) := (hmod (j + 1) (by omega)).1
      have hH1 : ContDiffOn ℝ (k : WithTop ENat)
          (iterateFrom n ρ a b (j + 1) (polarReg n ρ hρ v)) (oneSidedRegion n ρ (j : ℕ)) := by
        refine (hΦsm.mono (oneSidedRegion_subset_cvReg_succ hρ (j : ℕ))).congr (fun z hz => ?_)
        rw [mem_oneSidedRegion] at hz
        obtain ⟨hz1, hz2⟩ := hz
        exact iterateFrom_eqOn_of_eqOn_closed hρ hb hvw (j + 1) z
          (fun i hi => hz1 i (by omega))
          (fun i hi => hz2 i (by omega))
      have hfin' : Work.CR.Flat.holderNorm k α
          (iterateFrom n ρ a b (j + 1) (polarReg n ρ hρ v)) (inRegion n ρ jj) ≠ ⊤ := by
        rw [← stepRegion_succ_eq_inRegion jj]
        exact ihfin
      have hstep := hC k jj (iterateFrom n ρ a b (j + 1) (polarReg n ρ hρ v)) hH1 hfin'
      have hmain : Work.CR.Flat.holderNorm k α
            (radialExt n ρ a b jj (iterateFrom n ρ a b (j + 1) (polarReg n ρ hρ v)))
            (outRegion n ρ jj)
          ≤ (ENNReal.ofReal (C k)) ^ (n - j) * Work.CR.Flat.holderNorm k α v (pd n ρ 1) := by
        calc Work.CR.Flat.holderNorm k α
              (radialExt n ρ a b jj (iterateFrom n ρ a b (j + 1) (polarReg n ρ hρ v)))
              (outRegion n ρ jj)
            ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α
                (iterateFrom n ρ a b (j + 1) (polarReg n ρ hρ v)) (inRegion n ρ jj) := hstep
          _ ≤ ENNReal.ofReal (C k) * ((ENNReal.ofReal (C k)) ^ (n - (j + 1)) *
                Work.CR.Flat.holderNorm k α v (pd n ρ 1)) :=
              mul_le_mul' le_rfl (by rw [← stepRegion_succ_eq_inRegion jj]; exact ihbnd)
          _ = (ENNReal.ofReal (C k)) ^ (n - j) * Work.CR.Flat.holderNorm k α v (pd n ρ 1) := by
              rw [show n - j = n - (j + 1) + 1 by omega, pow_succ]
              ring
      refine ⟨?_, ?_⟩
      · rw [iterateFrom_of_lt hjlt, stepRegion_eq_outRegion jj]
        exact ne_top_of_le_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin') hstep
      · rw [iterateFrom_of_lt hjlt, stepRegion_eq_outRegion jj]
        exact hmain
  obtain ⟨h0fin, h0bnd⟩ := hchain n 0 rfl (Nat.zero_le n)
  rw [stepRegion_zero, Nat.sub_zero] at h0bnd
  rwa [← ENNReal.ofReal_pow (le_of_lt (hC0 k))] at h0bnd

end Work.NN.Final


