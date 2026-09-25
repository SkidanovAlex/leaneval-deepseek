import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.polydiscCutoff
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Core.bmRow_holder
import Submission.Work.NN.Core.bmDefect_eq
import Submission.Work.NN.Core.bmDefect_gain
import Submission.Work.NN.Core.bmDefect_gain_smooth
import Submission.Work.NN.Core.bmDefectClosed
import Submission.Work.NN.Core.exists_telTwoDF
import Submission.Work.NN.Core.TelTwoDF.S2_smooth
import Submission.Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
import Submission.Work.NN.Core.TelTwoDF.holderNorm_bump_mul_le
import Submission.Work.NN.Final.bmPot_linear

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff
open Set
open Work.CR.Flat

/-! ## A loss-free telescoping with a *smoothness* clause

`Work.NN.Core.exists_telTwoDF` provides the parameterised (derivative-free) `(0,2)`-telescoping
with the solve clause and the loss-free `C^{k,α}` estimate, but its smoothness clause assumes the
data to be real-analytic (`ContDiffOn ℝ ⊤`, i.e. `ω` in this Mathlib), which is useless for the
application to the Bochner–Martinelli defect (a potential, never analytic).  The theorem below
records the same operator with the *smooth* hypothesis `ContDiffOn ℝ ∞` (all finite orders); the
proof is the proof of `exists_telTwoDF`, with the third clause replaced by
`Work.NN.Core.TelTwoDF.S2_smooth` (the data `χ · η` is globally `C^N` for every `N` when `η` is
`C^N` on `polydisc 0 ρ` and `tsupport χ ⊆ polydisc 0 ρ`). -/

theorem exists_telTwoDF_smooth {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j) :
    ∃ (T : (Fin n → Fin n → Cn n → ℂ) →ₗ[ℝ] (Fin n → Cn n → ℂ)) (C : ℕ → ℝ),
      (∀ k, 0 < C k) ∧
      (∀ η, (∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 ρ)) → IsAntisymmTwo η →
        IsClosedTwoOn ρ η →
        ∀ j l (z : Cn n), z ∈ polydisc 0 ρ' →
          dbarCoord j (T η l) z - dbarCoord l (T η j) z = η j l z) ∧
      (∀ (k : ℕ) (η : Fin n → Fin n → Cn n → ℂ),
        (∀ i l, ContDiffOn ℝ k (η i l) (polydisc 0 ρ)) → IsAntisymmTwo η → IsClosedTwoOn ρ η →
        ∀ j, holderNorm k α (T η j) (polydisc 0 ρ')
          ≤ ENNReal.ofReal (C k) * ∑ i, ∑ l, holderNorm k α (η i l) (polydisc 0 ρ)) ∧
      (∀ η, (∀ i l, ContDiffOn ℝ ∞ (η i l) (polydisc 0 ρ)) →
        ∀ j, ContDiffOn ℝ ∞ (T η j) (polydisc 0 ρ')) ∧
      (∀ (N : ℕ) (η : Fin n → Fin n → Cn n → ℂ),
        (∀ i l, ContDiffOn ℝ N (η i l) (polydisc 0 ρ)) →
        ∀ j, ContDiffOn ℝ N (T η j) (polydisc 0 ρ')) := by
  obtain ⟨G, Cdat, χ, hρ'e, hbC, hCρ, hχdiff, hχcpt, hχts, hχone⟩ :=
    Work.NN.Core.TelTwoDF.exists_setup hρ hρ' hlt
  -- The solution operator.
  set T : (Fin n → Fin n → Cn n → ℂ) →ₗ[ℝ] (Fin n → Cn n → ℂ) :=
    Work.NN.Core.TelTwoDF.TtwoDF G χ with hTdef
  -- Constants of the estimate.
  have hC2ex : ∀ k : ℕ, ∃ C2 : ENNReal, C2 ≠ ⊤ ∧
      ∀ η : Fin n → Fin n → Cn n → ℂ, (∀ i l, ContDiff ℝ k (η i l)) → ∀ j : Fin n,
        Work.CR.Flat.holderNorm k α (Work.NN.Core.TelTwoDF.S2 G η j)
          (Work.NN.Core.TelTwoDF.Eset G n)
          ≤ C2 * Work.NN.Core.TelTwoDF.datumSum k α G η := fun k =>
    Work.NN.Core.TelTwoDF.S2_holderNorm_E_le_of_transform hα hα1 k G
      (Work.NN.Core.TelTwoDF.dbarTransform_Eset_le hα hα1 k G)
  have hCBex : ∀ k : ℕ, ∃ CB : ℝ, 0 < CB ∧ ∀ u : Cn n → ℂ,
      ContDiffOn ℝ k u (Work.CR.Flat.polydisc 0 ρ) →
      Work.CR.Flat.holderNorm k α (fun z => χ z * u z) Set.univ
        ≤ ENNReal.ofReal CB * Work.CR.Flat.holderNorm k α u (Work.CR.Flat.polydisc 0 ρ) :=
    fun k => Work.NN.Core.TelTwoDF.holderNorm_bump_mul_le hα.le hα1.le k hρ χ
      (hχdiff.of_le (by exact_mod_cast le_top)) hχcpt
      (fun z hz => by
        obtain ⟨j, hj⟩ := hz
        refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
        have h1 := (Work.CR.Flat.mem_polydisc.mp (hχts hmem)) j
        simp only [Pi.zero_apply, sub_zero] at h1
        linarith)
  choose C2 hC2ne hC2spec using hC2ex
  choose CB hCBpos hCBspec using hCBex
  refine ⟨T, fun k => max 1 (C2 k).toReal * CB k, ?_, ?_, ?_, ?_, ?_⟩
  · -- positivity of the constants
    intro k
    exact mul_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) (hCBpos k)
  · -- clause (a): the telescoping solves the `(0,2)`-equation
    intro η hη hanti hclosed j l z hz
    set η' : Fin n → Fin n → Cn n → ℂ := fun i l y => χ y * η i l y with hη'def
    have hzk : ∀ k : Fin n, ‖z k‖ < ρ' k := fun k => by
      exact mem_polydisc_zero_iff.mp hz k
    have hmemC : ∀ k : Fin n, ‖z k‖ < Cdat k := fun k =>
      ((((hzk k).trans (hρ'e k)).trans (G.hea k)).trans (G.hab k)).trans (hbC k)
    have hχz : ∀ᶠ w in nhds z, χ w = 1 :=
      Filter.mem_of_superset ((Work.CR.Flat.isOpen_polydisc (0 : Cn n) Cdat).mem_nhds
          (mem_polydisc_zero_iff.mpr hmemC))
        (fun w hw => hχone w (mem_polydisc_zero_iff.mp hw))
    have hη'cd : ∀ i l, ContDiff ℝ 1 (η' i l) := fun i l =>
      Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ)
        (hχdiff.of_le (by exact_mod_cast le_top)) hχts (hη i l)
    have hanti' : ∀ i l y, η' i l y = - η' l i y := by
      intro i l y
      simp only [hη'def]
      rw [hanti i l y]
      ring
    have hcl : ∀ i l m' y, (∀ k : Fin n, ‖y k‖ < G.b k) →
        Work.CR.Flat.dbarCoord i (η' l m') y - Work.CR.Flat.dbarCoord l (η' i m') y
          + Work.CR.Flat.dbarCoord m' (η' i l) y = 0 := by
      intro i l m' y hy
      have hyC : ∀ k : Fin n, ‖y k‖ < Cdat k := fun k => (hy k).trans (hbC k)
      have hyρ : ∀ k : Fin n, ‖y k‖ < ρ k := fun k => (hyC k).trans (hCρ k)
      have hχy : ∀ᶠ w in nhds y, χ w = 1 :=
        Filter.mem_of_superset ((Work.CR.Flat.isOpen_polydisc (0 : Cn n) Cdat).mem_nhds
            (mem_polydisc_zero_iff.mpr hyC))
          (fun w hw => hχone w (mem_polydisc_zero_iff.mp hw))
      have e1 : Work.CR.Flat.dbarCoord i (η' l m') y
          = Work.CR.Flat.dbarCoord i (η l m') y :=
        dbarCoord_mul_eq_of_eventuallyEq_one hχy
      have e2 : Work.CR.Flat.dbarCoord l (η' i m') y
          = Work.CR.Flat.dbarCoord l (η i m') y :=
        dbarCoord_mul_eq_of_eventuallyEq_one hχy
      have e3 : Work.CR.Flat.dbarCoord m' (η' i l) y
          = Work.CR.Flat.dbarCoord m' (η i l) y :=
        dbarCoord_mul_eq_of_eventuallyEq_one hχy
      rw [e1, e2, e3]
      exact hclosed i l m' y (mem_polydisc_zero_iff.mpr hyρ)
    have hzE : z ∈ Work.NN.Core.TelTwoDF.solveSet G := fun k => (hzk k).trans (hρ'e k)
    have hsol := Work.NN.Core.TelTwoDF.S2_solves G hη'cd hanti' hcl j l z hzE
    have hTη : T η = Work.NN.Core.TelTwoDF.S2 G η' := by
      rw [hTdef]
      funext i y
      rfl
    rw [hTη, hsol]
    simp only [hη'def]
    rw [hχz.self_of_nhds, one_mul]
  · -- clause (b): the loss-free `C^{k,α}` estimate
    intro k η hη _hanti _hclosed j
    have hη'cd : ∀ i l, ContDiff ℝ k (fun y => χ y * η i l y) := fun i l =>
      Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ)
        (hχdiff.of_le (by exact_mod_cast le_top)) hχts (hη i l)
    have h2 := hC2spec k (fun i l y => χ y * η i l y) hη'cd j
    have hdatum : Work.NN.Core.TelTwoDF.datumSum k α G (fun i l y => χ y * η i l y)
        ≤ ENNReal.ofReal (CB k) *
            ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ) := by
      rw [Work.NN.Core.TelTwoDF.datumSum, Work.NN.Core.TelTwoDF.Eset_zero]
      calc ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (fun z => χ z * η i l z)
              (Work.CR.Flat.polydisc 0 G.b)
          ≤ ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (fun z => χ z * η i l z) Set.univ :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ =>
              Work.CR.Flat.holderNorm_mono_set isOpen_univ
                (Work.CR.Flat.isOpen_polydisc (0 : Cn n) G.b) (subset_univ _) k α _
        _ ≤ ∑ i, ∑ l, ENNReal.ofReal (CB k) *
              Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => hCBspec k _ (hη i l)
        _ = ENNReal.ofReal (CB k) *
              ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
    have hmono : Work.CR.Flat.holderNorm k α (T η j) (Work.CR.Flat.polydisc 0 ρ')
        ≤ Work.CR.Flat.holderNorm k α (T η j) (Work.NN.Core.TelTwoDF.Eset G n) := by
      refine Work.CR.Flat.holderNorm_mono_set (Work.NN.Core.TelTwoDF.isOpen_Eset G n)
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ') ?_ k α (T η j)
      intro y hy
      rw [Work.NN.Core.TelTwoDF.Eset_n, mem_polydisc_zero_iff]
      intro i
      exact lt_trans (mem_polydisc_zero_iff.mp hy i) (hρ'e i)
    have h1 : Work.CR.Flat.holderNorm k α (T η j) (Work.NN.Core.TelTwoDF.Eset G n)
        ≤ C2 k * Work.NN.Core.TelTwoDF.datumSum k α G (fun i l y => χ y * η i l y) := by
      have hTeq : T η = Work.NN.Core.TelTwoDF.S2 G (fun i l y => χ y * η i l y) := by
        rw [hTdef]
        funext i y
        rfl
      rw [hTeq]
      exact h2
    calc Work.CR.Flat.holderNorm k α (T η j) (Work.CR.Flat.polydisc 0 ρ')
        ≤ Work.CR.Flat.holderNorm k α (T η j) (Work.NN.Core.TelTwoDF.Eset G n) := hmono
      _ ≤ C2 k * Work.NN.Core.TelTwoDF.datumSum k α G (fun i l y => χ y * η i l y) := h1
      _ ≤ C2 k * (ENNReal.ofReal (CB k) *
            ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ)) :=
          mul_le_mul_right hdatum (C2 k)
      _ = (C2 k * ENNReal.ofReal (CB k)) *
            ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ) := by
          rw [mul_assoc]
      _ ≤ ENNReal.ofReal (max 1 (C2 k).toReal * CB k) *
            ∑ i, ∑ l, Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 ρ) := by
          refine mul_le_mul_left ?_ _
          calc C2 k * ENNReal.ofReal (CB k)
              = ENNReal.ofReal (C2 k).toReal * ENNReal.ofReal (CB k) := by
                rw [ENNReal.ofReal_toReal (hC2ne k)]
            _ = ENNReal.ofReal ((C2 k).toReal * CB k) := by
                rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
            _ ≤ ENNReal.ofReal (max 1 (C2 k).toReal * CB k) :=
                ENNReal.ofReal_le_ofReal
                  (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt (hCBpos k)))
  · -- clause (c): smoothness of `T η` for data smooth on `polydisc 0 ρ`
    intro η hη j
    have hη'cd : ∀ (N : ℕ) (i l : Fin n), ContDiff ℝ N (fun y => χ y * η i l y) :=
      fun N i l =>
        Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
          (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ)
          (hχdiff.of_le (by exact_mod_cast le_top)) hχts
          ((hη i l).of_le (by exact_mod_cast le_top))
    refine contDiffOn_infty.mpr fun N => ?_
    have hTeq : T η = Work.NN.Core.TelTwoDF.S2 G (fun i l y => χ y * η i l y) := by
      rw [hTdef]
      funext i y
      rfl
    rw [hTeq]
    exact Work.NN.Core.TelTwoDF.S2_smooth G hρ' hρ'e hη'cd j N
  · -- clause (d): `C^N`-regularity of `T η` for data of class `C^N` on `polydisc 0 ρ`
    intro N η hη j
    have hη'cd : ∀ i l, ContDiff ℝ N (fun y => χ y * η i l y) := fun i l =>
      Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ)
        (hχdiff.of_le (by exact_mod_cast le_top)) hχts (hη i l)
    have hTeq : T η = Work.NN.Core.TelTwoDF.S2 G (fun i l y => χ y * η i l y) := by
      rw [hTdef]
      funext i y
      rfl
    rw [hTeq]
    exact (Work.NN.Core.TelTwoDF.S2_contDiff_k G hη'cd j).contDiffOn

/-! ## Auxiliary lemmas for the assembly -/


/-- Subadditivity of `holderNorm` for a difference. -/
lemma holderNorm_sub_le' {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {α : ℝ} {Ω : Set X} (hΩ : UniqueDiffOn ℝ Ω) {f g : X → ℂ}
    (hf : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞) f Ω)
    (hg : ContDiffOn ℝ ((k : ℕ∞) : WithTop ℕ∞) g Ω) :
    Work.CR.Flat.holderNorm k α (f - g) Ω
      ≤ Work.CR.Flat.holderNorm k α f Ω + Work.CR.Flat.holderNorm k α g Ω := by
  have h1 : f - g = fun x => f x + (-g) x := rfl
  rw [h1]
  calc Work.CR.Flat.holderNorm k α (fun x => f x + -g x) Ω
      ≤ Work.CR.Flat.holderNorm k α f Ω + Work.CR.Flat.holderNorm k α (-g) Ω :=
        Work.CR.Flat.Holder.holderNorm_add_le hf hg.neg hΩ
    _ = Work.CR.Flat.holderNorm k α f Ω + Work.CR.Flat.holderNorm k α g Ω := by
        rw [Work.CR.Flat.Holder.holderNorm_neg hg hΩ]


section Aux

variable {n : ℕ}

/-- A compactly supported function vanishes outside a ball of positive radius. -/
lemma exists_radius_of_hasCompactSupport' {g : Cn n → ℂ} (hcs : HasCompactSupport g) :
    ∃ R : ℝ, 0 < R ∧ ∀ z, R ≤ ‖z‖ → g z = 0 := by
  obtain ⟨C, hC⟩ := hcs.isBounded.exists_norm_le
  refine ⟨max C 0 + 1, by positivity, fun z hz => ?_⟩
  by_contra hne
  have hz' : z ∈ tsupport g := subset_tsupport g (Function.mem_support.mpr hne)
  have h1 : ‖z‖ ≤ C := hC z hz'
  have h2 : C ≤ max C 0 := le_max_left _ _
  linarith

/-- The topological support of `∂̄_a χ` is contained in the (topological) support of `χ`. -/
lemma tsupport_dbarCoord_subset' {χ : Cn n → ℂ} (a : Fin n) :
    tsupport (fun z => dbarCoord a χ z) ⊆ tsupport χ := by
  refine closure_minimal ?_ (isClosed_tsupport χ)
  intro y hy
  by_contra h
  have h0 : χ =ᶠ[nhds y] (0 : Cn n → ℂ) := by
    filter_upwards [(isClosed_tsupport χ).compl_mem_nhds h] with w hw
    exact Function.notMem_support.mp fun hw' => hw (by rw [tsupport]; exact subset_closure hw')
  have hy0 : fderiv ℝ χ y = 0 := by
    have := h0.fderiv_eq (𝕜 := ℝ)
    simpa using this
  exact (Function.mem_support.mp hy) (by simp [dbarCoord, hy0])

/-- The topological support of `∂̄_a χ` is compact when that of `χ` is. -/
lemma hasCompactSupport_dbarCoord' {χ : Cn n → ℂ} (hcs : HasCompactSupport χ) (a : Fin n) :
    HasCompactSupport (fun w => dbarCoord a χ w) :=
  hcs.isCompact.of_isClosed_subset (isClosed_tsupport _) (tsupport_dbarCoord_subset' a)

/-- The `∂̄`-derivative of a smooth function is smooth. -/
lemma contDiff_dbarCoord_of' {χ : Cn n → ℂ} (hχ : ContDiff ℝ ∞ χ) (a : Fin n) :
    ContDiff ℝ ∞ (fun w => dbarCoord a χ w) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right le_rfl
  have h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ χ w (Pi.single a (1 : ℂ))) :=
    hfd.clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun w => fderiv ℝ χ w (Pi.single a (Complex.I : ℂ))) :=
    hfd.clm_apply contDiff_const
  have h3 : ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ χ w (Pi.single a (1 : ℂ))
      + Complex.I * fderiv ℝ χ w (Pi.single a (Complex.I : ℂ)))) :=
    contDiff_const.mul (h1.add (contDiff_const.mul h2))
  simpa only [dbarCoord] using h3

/-- `bmPot` of globally `C^m` compactly supported data is `C^m`. -/
lemma contDiff_bmPot' (hn : 0 < n) {m : ℕ} {f : Fin n → Cn n → ℂ}
    (hf : ∀ j, ContDiff ℝ m (f j)) (hfs : ∀ j, HasCompactSupport (f j)) :
    ContDiff ℝ m (fun z => Work.CR.Flat.Cauchy.bmPot f z) := by
  have hc := Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn hf hfs
  have hfun : (fun z => Work.CR.Flat.Cauchy.bmPot f z)
      = fun z => Work.CR.Flat.Cauchy.bmPotential f z :=
    funext fun z => (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot f z).symm
  rwa [hfun]

/-- `bmRow` of globally `C^m` compactly supported data is `C^m`. -/
lemma contDiff_bmRow' (hn : 0 < n) {m : ℕ} {η : Fin n → Fin n → Cn n → ℂ}
    (hη : ∀ i l, ContDiff ℝ m (η i l)) (hcs : ∀ i l, HasCompactSupport (η i l)) (i : Fin n) :
    ContDiff ℝ m (bmRow η i) := by
  rw [show bmRow η i = fun z => -((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) *
      Work.CR.Flat.Cauchy.bmPot (fun l => η i l) z from rfl]
  exact contDiff_const.mul (contDiff_bmPot' hn (fun l => hη i l) (fun l => hcs i l))

/-- `bmRow` of globally `C¹` compactly supported data is differentiable. -/
lemma differentiableAt_bmRow' (hn : 0 < n) {η : Fin n → Fin n → Cn n → ℂ}
    (hη : ∀ i l, ContDiff ℝ 1 (η i l)) (hcs : ∀ i l, HasCompactSupport (η i l))
    (i : Fin n) (z : Cn n) : DifferentiableAt ℝ (bmRow η i) z :=
  ((contDiff_bmRow' hn hη hcs i).differentiable one_ne_zero).differentiableAt

/-- Additivity of `∂̄_j` for sums (written as `w ↦ f w + g w`). -/
lemma dbarCoord_add_fun' (j : Fin n) {f g : Cn n → ℂ} {z : Cn n}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbarCoord j (fun w => f w + g w) z = dbarCoord j f z + dbarCoord j g z :=
  Work.CR.Flat.Polydisc.dbarCoord_add j f g z hf hg

/-- Additivity of `∂̄_j` for differences (written as `w ↦ f w - g w`). -/
lemma dbarCoord_sub_fun' (j : Fin n) {f g : Cn n → ℂ} {z : Cn n}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbarCoord j (fun w => f w - g w) z = dbarCoord j f z - dbarCoord j g z := by
  have hfd : fderiv ℝ (fun w => f w - g w) z = fderiv ℝ f z - fderiv ℝ g z := by
    rw [show (fun w => f w - g w) = f - g from rfl, fderiv_sub hf hg]
  simp only [dbarCoord, hfd, sub_apply]
  ring

/-- `∂̄_j` of a constant multiple. -/
lemma dbarCoord_const_mul' (j : Fin n) (c : ℂ) (u : Cn n → ℂ) (z : Cn n)
    (hu : DifferentiableAt ℝ u z) :
    dbarCoord j (fun w => c * u w) z = c * dbarCoord j u z := by
  have h := Work.CR.Flat.Polydisc.dbarCoord_mul j (fun _ : Cn n => c) u z
    (differentiableAt_const c) hu
  have h0 : dbarCoord j (fun _ : Cn n => c) z = 0 := by simp [dbarCoord]
  rw [h0, zero_mul, zero_add] at h
  exact h

end Aux

section Aux2

variable {n : ℕ}

/-- `bmPot` is additive in the family (continuous compactly supported data). -/
lemma bmPot_add' (hn : 0 < n) {f g : Fin n → Cn n → ℂ}
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j))
    (hfs : ∀ j, HasCompactSupport (f j)) (hgs : ∀ j, HasCompactSupport (g j)) :
    (fun z => Work.CR.Flat.Cauchy.bmPot (fun j => fun y => f j y + g j y) z)
      = (fun z => Work.CR.Flat.Cauchy.bmPot f z) + fun z => Work.CR.Flat.Cauchy.bmPot g z := by
  funext z
  have h := Work.NN.Final.bmPot_linear hn (1 : ℂ) (1 : ℂ) hf hg hfs hgs z
  have h1 : (fun j => fun y => (1 : ℂ) * f j y + (1 : ℂ) * g j y)
      = fun j => fun y => f j y + g j y := by
    funext j y; ring
  rw [h1] at h
  simpa using h

/-- `ℝ`-homogeneity of `bmPot` in the family. -/
lemma bmPot_real_smul' (hn : 0 < n) (c : ℝ) {f : Fin n → Cn n → ℂ}
    (hf : ∀ j, Continuous (f j)) (hfs : ∀ j, HasCompactSupport (f j)) :
    (fun z => Work.CR.Flat.Cauchy.bmPot (fun j => fun y => (c : ℂ) * f j y) z)
      = c • (fun z => Work.CR.Flat.Cauchy.bmPot f z) := by
  funext z
  have h := Work.NN.Final.bmPot_linear hn ((c : ℂ)) (0 : ℂ) hf hf hfs hfs z
  have h1 : (fun j => fun y => (c : ℂ) * f j y + (0 : ℂ) * f j y)
      = fun j => fun y => (c : ℂ) * f j y := by
    funext j y; ring
  rw [h1] at h
  simp only [zero_mul, add_zero, Pi.smul_apply, Complex.real_smul] at h ⊢
  exact h

end Aux2

section Aux3

variable {n : ℕ} {ρ : Fin n → ℝ}

/-- The components of `bmH` are additive in the datum. -/
lemma bmH_add' (χ : Cn n → ℂ) (η η' : Fin n → Fin n → Cn n → ℂ) (a b c : Fin n) (w : Cn n) :
    bmH χ (η + η') a b c w = bmH χ η a b c w + bmH χ η' a b c w := by
  rw [bmH_eq, bmH_eq, bmH_eq]
  simp only [Pi.add_apply]
  ring

/-- The components of `bmH` are `ℝ`-homogeneous in the datum. -/
lemma bmH_smul' (χ : Cn n → ℂ) (t : ℝ) (η : Fin n → Fin n → Cn n → ℂ) (a b c : Fin n) (w : Cn n) :
    bmH χ (t • η) a b c w = t • bmH χ η a b c w := by
  rw [bmH_eq, bmH_eq]
  simp only [Pi.smul_apply, Complex.real_smul]
  ring

/-- The components of `bmH χ η` are globally `C^m` when `η` is `C^m` on the polydisc. -/
lemma contDiff_bmH' {m : ℕ} {χ : Cn n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχts : tsupport χ ⊆ Work.CR.Flat.polydisc 0 ρ)
    {η : Fin n → Fin n → Cn n → ℂ} (hη : ∀ i l, ContDiffOn ℝ m (η i l) (Work.CR.Flat.polydisc 0 ρ))
    (j l i : Fin n) : ContDiff ℝ m (fun w => bmH χ η j l i w) := by
  have h0 : ∀ a b c : Fin n, ContDiff ℝ m (fun w => dbarCoord a χ w * η b c w) := fun a b c =>
    Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
      (Work.CR.Flat.isOpen_polydisc 0 ρ) ((contDiff_dbarCoord_of' hχ a).of_le (by simp))
      ((tsupport_dbarCoord_subset' a).trans hχts) (hη b c)
  have h1 : (fun w => bmH χ η j l i w)
      = fun w => dbarCoord i χ w * η j l w + dbarCoord j χ w * η l i w
          - dbarCoord l χ w * η j i w := by
    funext w
    rw [bmH_eq]
  rw [h1]
  exact ((h0 i j l).add (h0 j l i)).sub (h0 l j i)

/-- The components of `bmH χ η` have compact support when `χ` does. -/
lemma hasCompactSupport_bmH' {χ : Cn n → ℂ} (hcs : HasCompactSupport χ)
    (η : Fin n → Fin n → Cn n → ℂ) (a b c : Fin n) :
    HasCompactSupport (fun w => bmH χ η a b c w) := by
  have h1 : HasCompactSupport (fun w => dbarCoord c χ w * η a b w) :=
    (hasCompactSupport_dbarCoord' hcs c).mul_right
  have h2 : HasCompactSupport (fun w => dbarCoord a χ w * η b c w) :=
    (hasCompactSupport_dbarCoord' hcs a).mul_right
  have h3 : HasCompactSupport (fun w => dbarCoord b χ w * η a c w) :=
    (hasCompactSupport_dbarCoord' hcs b).mul_right
  have hfun : (fun w => bmH χ η a b c w)
      = fun w => dbarCoord c χ w * η a b w + dbarCoord a χ w * η b c w
          - dbarCoord b χ w * η a c w := by
    funext w
    rw [bmH_eq]
  rw [hfun]
  exact (h1.add h2).sub h3

end Aux3


/-! ## Antisymmetry and regularity of the Bochner–Martinelli defect

These two lemmas are the same statements as `Work.NN.Core.bmDefect_antisymm` and
`Work.NN.Core.bmDefect_contDiffOn` (proved in the sibling files of this directory); they are
restated here because those two files declare the same three public helper lemmas
(`tsupport_dbarCoord_subset`, `hasCompactSupport_dbarCoord`,
`dbarCoord_eq_zero_of_notMem_tsupport`) and therefore cannot be imported together. -/

/-- Antisymmetry of `bmH` in the first two indices for antisymmetric `η`. -/
private lemma bmH_antisymm' {n : ℕ} {χ : Cn n → ℂ} {η : Fin n → Fin n → Cn n → ℂ}
    (hanti : ∀ i l z, η i l z = - η l i z) (j l i : Fin n) (w : Cn n) :
    bmH χ η j l i w = - bmH χ η l j i w := by
  have h1 : η j l w = - η l j w := hanti j l w
  have h2 : η l i w = - η i l w := hanti l i w
  have h3 : η j i w = - η i j w := hanti j i w
  unfold bmH
  rw [h1, h2, h3]
  ring

/-- The defect of one Bochner–Martinelli step is antisymmetric for antisymmetric data. -/
lemma bmDefect_antisymm' {n : ℕ} (hn : 0 < n) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {χ : Cn n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hχcs : HasCompactSupport χ)
    (hχts : tsupport χ ⊆ Work.CR.Flat.polydisc 0 ρ)
    {η : Fin n → Fin n → Cn n → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) (η i l)
      (Work.CR.Flat.polydisc 0 ρ))
    (hanti : ∀ i l z, η i l z = - η l i z) :
    ∀ i l z, bmDefect χ η i l z = - bmDefect χ η l i z := by
  intro i l z
  have hcont : ∀ m : Fin n, Continuous (fun w => bmH χ η l i m w) := fun m =>
    contDiff_zero.mp (contDiff_bmH' hχ hχts (fun a b => (hη a b).of_le (by norm_num)) l i m)
  have hcs : ∀ m : Fin n, HasCompactSupport (fun w => bmH χ η l i m w) := fun m =>
    hasCompactSupport_bmH' hχcs η l i m
  have hlin := Work.NN.Final.bmPot_linear (n := n) hn (-1 : ℂ) (0 : ℂ)
    (f := fun m => fun w => bmH χ η l i m w) (g := fun m => fun w => bmH χ η l i m w)
    hcont hcont hcs hcs z
  have hfun : (fun m => fun w => bmH χ η i l m w)
      = fun m => fun w => (-1 : ℂ) * bmH χ η l i m w + 0 * bmH χ η l i m w := by
    funext m w
    rw [bmH_antisymm' hanti i l m w]
    ring
  rw [bmDefect_apply, bmDefect_apply, hfun, hlin]
  simp only [zero_mul, add_zero]
  rw [hanti i l z]
  ring

/-- **Regularity of the Bochner–Martinelli defect.**  For `χ` smooth with compact support in the
open polydisc `polydisc 0 ρ` and equal to `1` on the closed polydisc of radii `ρ'`, the defect
`bmDefect χ η` is `C^k` on `polydisc 0 ρ'` as soon as `η` is `C^k` on `polydisc 0 ρ`. -/
lemma bmDefect_contDiffOn' {n : ℕ} (hn : 0 < n) {k : ℕ} {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j)
    {χ : Cn n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hχcs : HasCompactSupport χ)
    (hχts : tsupport χ ⊆ Work.CR.Flat.polydisc 0 ρ)
    (hχone : ∀ z, (∀ j, ‖z j‖ ≤ ρ' j) → χ z = 1)
    {η : Fin n → Fin n → Cn n → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ k (η i l) (Work.CR.Flat.polydisc 0 ρ)) :
    ∀ i l, ContDiffOn ℝ k (bmDefect χ η i l) (Work.CR.Flat.polydisc 0 ρ') := by
  intro i l
  have hbmH : ∀ m : Fin n, ContDiff ℝ k (fun w => bmH χ η i l m w) := fun m =>
    contDiff_bmH' hχ hχts hη i l m
  have hbmHcs : ∀ m : Fin n, HasCompactSupport (fun w => bmH χ η i l m w) := fun m =>
    hasCompactSupport_bmH' hχcs η i l m
  have hF : ContDiff ℝ k (fun z => (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) *
      Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η i l m) z) := by
    have hbm : ContDiff ℝ k (Work.CR.Flat.Cauchy.bmPotential (fun m => bmH χ η i l m)) :=
      Work.CR.Flat.Cauchy.bmPotential_contDiff_of_hasCompactSupport hn hbmH hbmHcs
    have heq : (fun z => (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) *
        Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η i l m) z)
        = fun z => (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) *
            Work.CR.Flat.Cauchy.bmPotential (fun m => bmH χ η i l m) z := by
      funext z
      rw [← Work.CR.Flat.Cauchy.bmPotential_eq_bmPot]
    rw [heq]
    exact contDiff_const.mul hbm
  rw [(Work.CR.Flat.isOpen_polydisc 0 ρ').contDiffOn_iff]
  intro a ha
  set σ : Fin n → ℝ := fun j => ρ' j - ‖a j‖ with hσ
  have hσj : ∀ j, σ j = ρ' j - ‖a j‖ := fun j => congrFun hσ j
  have hVsub : Work.CR.Flat.polydisc a σ ⊆ {z | ∀ j, ‖z j‖ ≤ ρ' j} := by
    intro z hz j
    have h1 : ‖z j‖ ≤ ‖a j‖ + ‖z j - a j‖ := by
      have h := norm_add_le (a j) (z j - a j)
      have he : a j + (z j - a j) = z j := by ring
      rw [he] at h
      exact h
    have h2 : ‖z j - a j‖ < σ j := hz j
    rw [hσj j] at h2
    linarith
  have haj : ∀ j, ‖a j‖ < ρ' j := fun j => by simpa using ha j
  have hmem : a ∈ Work.CR.Flat.polydisc a σ := by
    intro j
    rw [sub_self, norm_zero, hσj j]
    exact sub_pos.mpr (haj j)
  have hχ1 : χ =ᶠ[nhds a] 1 := by
    filter_upwards [(Work.CR.Flat.isOpen_polydisc a σ).mem_nhds hmem] with y hy
    exact hχone y (hVsub hy)
  have hev : bmDefect χ η i l =ᶠ[nhds a]
      (fun z => (-((Work.CR.Flat.Cauchy.bmGamma n)⁻¹)) *
        Work.CR.Flat.Cauchy.bmPot (fun m => bmH χ η i l m) z) := by
    filter_upwards [hχ1] with z hz
    rw [bmDefect_apply, hz, Pi.one_apply]
    ring
  exact hF.contDiffAt.congr_of_eventuallyEq hev


/-- `0 ≤ n` in `ℕ∞ω`. -/
private lemma zero_le' (n : WithTop ℕ∞) : (0 : WithTop ℕ∞) ≤ n := zero_le

/-- `k ≤ k + 1` in `ℕ∞ω`. -/
private lemma natCast_le_succ' (k : ℕ) :
    ((k : ℕ) : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
  exact_mod_cast Nat.le_succ k

/-- `k ≤ k + 1` in `ℕ∞ω`. -/
private lemma natCast_le_add_one' (k : ℕ) :
    ((k : ℕ) : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) + 1 := by
  have h : ((k : ℕ) : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_succ k
  rwa [Nat.cast_add, Nat.cast_one] at h

/-- `1 ≤ k + 1` in `ℕ∞ω`. -/
private lemma one_le_natCast_add_one' (k : ℕ) :
    (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) + 1 := by
  have h : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  rwa [Nat.cast_add, Nat.cast_one] at h

/-- `1 ≤ k + 1` in `ℕ∞ω`, used to lower the regularity of `C^{k+1}` data to `C¹`. -/
private lemma one_le_succ' (k : ℕ) : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)

/-! ## The `(0,2)` interior `∂̄`-Poincaré lemma on a polydisc, at an arbitrary ratio -/

theorem open_poincare_two {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j) :
    ∃ (S2 : (Fin n → Fin n → Cn n → ℂ) →ₗ[ℝ] (Fin n → Cn n → ℂ)) (C : ℕ → ℝ),
      (∀ k, 0 < C k) ∧
      (∀ η, (∀ j l, ContDiff ℝ 1 (η j l)) → (∀ j l z, η j l z = - η l j z) →
        (∀ j l m z, dbarCoord j (η l m) z - dbarCoord l (η j m) z + dbarCoord m (η j l) z = 0) →
        ∀ j l (z : Cn n), z ∈ polydisc 0 ρ' →
          dbarCoord j (S2 η l) z - dbarCoord l (S2 η j) z = η j l z) ∧
      (∀ (k : ℕ) (η : Fin n → Fin n → Cn n → ℂ), (∀ j l, ContDiff ℝ (k + 1) (η j l)) →
        (∀ j l z, η j l z = - η l j z) →
        (∀ j l m z, dbarCoord j (η l m) z - dbarCoord l (η j m) z + dbarCoord m (η j l) z = 0) →
        ∀ j, holderNorm (k + 1) α (S2 η j) (polydisc 0 ρ')
          ≤ ENNReal.ofReal (C k) * ∑ j, ∑ l, holderNorm k α (η j l) (polydisc 0 ρ)) ∧
      (∀ η, (∀ j l, ContDiffOn ℝ ∞ (η j l) (polydisc 0 ρ)) →
        (∀ j l z, η j l z = - η l j z) →
        (∀ j l m z, z ∈ polydisc 0 ρ →
          dbarCoord j (η l m) z - dbarCoord l (η j m) z + dbarCoord m (η j l) z = 0) →
        ∀ j, ContDiffOn ℝ ∞ (S2 η j) (polydisc 0 ρ')) := by
  classical
  --# intermediate multi-radii
  set ρm : Fin n → ℝ := fun j => (ρ j + ρ' j) / 2 with hρmdef
  have hρmpos : ∀ j, 0 < ρm j := fun j => by
    rw [hρmdef]; linarith [hρ j, hρ' j]
  have hltm : ∀ j, ρ' j < ρm j := fun j => by
    rw [hρmdef]; linarith [hlt j]
  have hmρ : ∀ j, ρm j < ρ j := fun j => by
    rw [hρmdef]; linarith [hlt j]
  --# the loss-free telescoping for `ρ' < ρm`
  obtain ⟨T0, C0, hC0pos, hT0solve, hT0est, hT0smooth, hT0regN⟩ :=
    exists_telTwoDF_smooth (n := n) hα hα1 hρmpos hρ' hltm
  --# the cut-off
  have hKc : IsCompact {z : Cn n | ∀ k, ‖z k‖ ≤ ρm k} :=
    Work.NN.Core.TelTwoDF.isCompact_closedPolydisc ρm
  have hKU : {z : Cn n | ∀ k, ‖z k‖ ≤ ρm k} ⊆ polydisc 0 ρ := by
    intro z hz
    rw [Work.CR.Flat.mem_polydisc]
    intro k
    simp only [Pi.zero_apply, sub_zero]
    exact lt_of_le_of_lt (hz k) (hmρ k)
  obtain ⟨χ, Vb, hχdiff, hχcs, hχts, hVbo, hKVb, hχoneVb⟩ :=
    Work.NN.Core.exists_contDiff_bump_of_isCompact_subset hKc
      (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ) hKU
  have hχone : ∀ z : Cn n, (∀ j, ‖z j‖ ≤ ρm j) → χ z = 1 :=
    fun z hz => hχoneVb z (hKVb hz)
  have hχvan : ∀ z : Cn n, (∃ j, ρ j ≤ ‖z j‖) → χ z = 0 := by
    intro z hz
    refine Function.notMem_support.mp fun hmem => ?_
    obtain ⟨j, hj⟩ := hz
    have h1 : ‖z j‖ < ρ j := by
      have h2 := (Work.CR.Flat.mem_polydisc.mp (hχts (subset_tsupport χ hmem))) j
      simpa using h2
    linarith
  have hχCk : ∀ m : ℕ, ContDiff ℝ m χ := fun m => hχdiff.of_le (by exact_mod_cast le_top)
  --# constants
  have hK1ex : ∀ k : ℕ, ∃ K1 : ℝ, 0 < K1 ∧ ∀ ζ : Fin n → Fin n → Cn n → ℂ,
      (∀ j l, ContDiff ℝ (k + 1) (ζ j l)) →
      (∀ j l z, (∃ i, ρ i ≤ ‖z i‖) → ζ j l z = 0) →
      ∀ j, holderNorm (k + 1) α (bmRow ζ j) (polydisc 0 ρ)
        ≤ ENNReal.ofReal K1 * ∑ l, ∑ m, holderNorm k α (ζ l m) Set.univ := by
    intro k
    obtain ⟨K1, hK1pos, hK1spec⟩ := bmRow_holder hn hα hα1
      (c := (0 : Cn n)) (r := fun j => 2 * ρ j) (fun j => by linarith [hρ j]) k
    refine ⟨K1, hK1pos, fun ζ hζ hζv j => ?_⟩
    have h := hK1spec ζ hζ (fun j l z hz => hζv j l z (by
      obtain ⟨i, hi⟩ := hz
      refine ⟨i, ?_⟩
      have hi' : ρ i ≤ ‖z i - (0 : Cn n) i‖ := by
        rw [show 2 * ρ i / 2 = ρ i from by ring] at hi
        exact hi
      simpa using hi'))
    have hp : (polydisc (0 : Cn n) (fun j => 2 * ρ j / 2)) = polydisc 0 ρ := by
      congr 1
      funext j
      ring
    rw [hp] at h
    exact h j
  choose K1 hK1pos hK1spec using hK1ex
  have hKχex : ∀ k : ℕ, ∃ Kχ : ℝ, 0 < Kχ ∧ ∀ u : Cn n → ℂ,
      ContDiffOn ℝ k u (polydisc 0 ρ) →
      holderNorm k α (fun z => χ z * u z) Set.univ
        ≤ ENNReal.ofReal Kχ * holderNorm k α u (polydisc 0 ρ) := fun k =>
    Work.NN.Core.TelTwoDF.holderNorm_bump_mul_le hα.le hα1.le k hρ χ (hχCk (k + 1)) hχcs hχvan
  choose Kχ hKχpos hKχspec using hKχex
  have hKdefex : ∀ k : ℕ, ∃ Kdef : ℝ, 0 < Kdef ∧ ∀ ζ : Fin n → Fin n → Cn n → ℂ,
      (∀ i l, ContDiffOn ℝ (k + 1) (ζ i l) (polydisc 0 ρ)) →
      ∀ j m, holderNorm (k + 1) α (bmDefect χ ζ j m) (polydisc 0 ρm)
        ≤ ENNReal.ofReal Kdef * ∑ i, ∑ l, holderNorm k α (ζ i l) (polydisc 0 ρ) := fun k =>
    bmDefect_gain_smooth hn hα hα1 hρ hρmpos hmρ χ hχdiff hχcs hχts
      (fun z hz => hχone z (fun j => le_of_lt (by simpa using (Work.CR.Flat.mem_polydisc.mp hz) j))) k
  choose Kdef hKdefpos hKdefspec using hKdefex
  --# the subscript constants of the estimate
  let KM : ℕ → ℝ := fun k => (n : ℝ) * Kdef k
  let KK : ℕ → ℝ := fun k => (n : ℝ) * KM k
  --# the linear operator
  let V : Submodule ℝ (Fin n → Fin n → Cn n → ℂ) :=
    { carrier := {η | ∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 ρ)}
      zero_mem' := fun i l => contDiffOn_const
      add_mem' := fun hf hg i l => (hf i l).add (hg i l)
      smul_mem' := fun c f hf i l => ContDiffOn.const_smul c (hf i l) }
  have hbmRow_add : ∀ (η η' : Fin n → Fin n → Cn n → ℂ),
      (∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 ρ)) →
      (∀ i l, ContDiffOn ℝ 1 (η' i l) (polydisc 0 ρ)) →
      bmRow (fun a b w => χ w * (η + η') a b w)
        = bmRow (fun a b w => χ w * η a b w) + bmRow (fun a b w => χ w * η' a b w) := by
    intro η η' hη hη'
    funext i z
    have hcont : ∀ l : Fin n, Continuous (fun w => χ w * η i l w) := fun l =>
      contDiff_zero.mp (Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ) (hχCk 0) hχts
        ((hη i l).of_le (by norm_num)))
    have hcont' : ∀ l : Fin n, Continuous (fun w => χ w * η' i l w) := fun l =>
      contDiff_zero.mp (Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ) (hχCk 0) hχts
        ((hη' i l).of_le (by norm_num)))
    have hcs : ∀ l : Fin n, HasCompactSupport (fun w => χ w * η i l w) := fun l => hχcs.mul_right
    have hcs' : ∀ l : Fin n, HasCompactSupport (fun w => χ w * η' i l w) := fun l => hχcs.mul_right
    have hfam : (fun l : Fin n => fun w => χ w * (η i l w + η' i l w))
        = fun l => fun w => χ w * η i l w + χ w * η' i l w := by
      funext l w; ring
    have hpot := congrFun (bmPot_add' hn (f := fun l => fun w => χ w * η i l w)
      (g := fun l => fun w => χ w * η' i l w) hcont hcont' hcs hcs') z
    simp only [bmRow_apply, Pi.add_apply]
    rw [hfam, hpot]
    simp only [Pi.add_apply]
    ring
  have hbmRow_smul : ∀ (c : ℝ) (η : Fin n → Fin n → Cn n → ℂ),
      (∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 ρ)) →
      bmRow (fun a b w => χ w * (c • η) a b w) = c • bmRow (fun a b w => χ w * η a b w) := by
    intro c η hη
    funext i z
    have hcont : ∀ l : Fin n, Continuous (fun w => χ w * η i l w) := fun l =>
      contDiff_zero.mp (Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ) (hχCk 0) hχts
        ((hη i l).of_le (by norm_num)))
    have hcs : ∀ l : Fin n, HasCompactSupport (fun w => χ w * η i l w) := fun l => hχcs.mul_right
    have hfam : (fun l : Fin n => fun w => χ w * (c • η i l w))
        = fun l => fun w => (c : ℂ) * (χ w * η i l w) := by
      funext l w
      rw [Complex.real_smul]
      ring
    have hpot := congrFun (bmPot_real_smul' hn c hcont hcs) z
    simp only [bmRow_apply, Pi.smul_apply]
    rw [hfam, hpot]
    simp only [Pi.smul_apply, Complex.real_smul]
    ring
  have hdef_add : ∀ (η η' : Fin n → Fin n → Cn n → ℂ),
      (∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 ρ)) →
      (∀ i l, ContDiffOn ℝ 1 (η' i l) (polydisc 0 ρ)) →
      bmDefect χ (η + η') = bmDefect χ η + bmDefect χ η' := by
    intro η η' hη hη'
    funext j l z
    have hcontH : ∀ (θ : Fin n → Fin n → Cn n → ℂ),
        (∀ i l, ContDiffOn ℝ 1 (θ i l) (polydisc 0 ρ)) →
        ∀ i : Fin n, Continuous (fun w => bmH χ θ j l i w) := fun θ hθ i =>
      contDiff_zero.mp (contDiff_bmH' hχdiff hχts (fun a b => (hθ a b).of_le (by norm_num)) j l i)
    have hpot := congrFun (bmPot_add' hn (f := fun i w => bmH χ η j l i w)
      (g := fun i w => bmH χ η' j l i w) (hcontH η hη) (hcontH η' hη')
      (fun i => hasCompactSupport_bmH' hχcs η j l i)
      (fun i => hasCompactSupport_bmH' hχcs η' j l i)) z
    have hH : (fun i : Fin n => fun w => bmH χ (η + η') j l i w)
        = fun i => fun w => bmH χ η j l i w + bmH χ η' j l i w := by
      funext i w
      exact bmH_add' χ η η' j l i w
    simp only [bmDefect_apply, Pi.add_apply]
    rw [hH, hpot]
    simp only [Pi.add_apply]
    ring
  have hdef_smul : ∀ (c : ℝ) (η : Fin n → Fin n → Cn n → ℂ),
      (∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 ρ)) →
      bmDefect χ (c • η) = c • bmDefect χ η := by
    intro c η hη
    funext j l z
    have hcontH : ∀ i : Fin n, Continuous (fun w => bmH χ η j l i w) := fun i =>
      contDiff_zero.mp (contDiff_bmH' hχdiff hχts (fun a b => (hη a b).of_le (by norm_num)) j l i)
    have hpot := congrFun (bmPot_real_smul' hn c hcontH
      (fun i => hasCompactSupport_bmH' hχcs η j l i)) z
    have hH : (fun i : Fin n => fun w => bmH χ (c • η) j l i w)
        = fun i => fun w => (c : ℂ) * bmH χ η j l i w := by
      funext i w
      rw [bmH_smul' χ c η j l i w, Complex.real_smul]
    simp only [bmDefect_apply, Pi.smul_apply]
    rw [hH, hpot]
    simp only [Pi.smul_apply, Complex.real_smul]
    ring
  let A : V →ₗ[ℝ] (Fin n → Cn n → ℂ) :=
    { toFun := fun η => bmRow (fun a b w => χ w * (η : Fin n → Fin n → Cn n → ℂ) a b w)
      map_add' := fun η η' => by
        have h := hbmRow_add (η : Fin n → Fin n → Cn n → ℂ) (η' : Fin n → Fin n → Cn n → ℂ)
          η.2 η'.2
        simpa only [Submodule.coe_add] using h
      map_smul' := fun c η => by
        have h := hbmRow_smul c (η : Fin n → Fin n → Cn n → ℂ) η.2
        simpa only [Submodule.coe_smul, RingHom.id_apply] using h }
  let Dr : V →ₗ[ℝ] (Fin n → Fin n → Cn n → ℂ) :=
    { toFun := fun η => bmDefect χ (η : Fin n → Fin n → Cn n → ℂ)
      map_add' := fun η η' => by
        have h := hdef_add (η : Fin n → Fin n → Cn n → ℂ) (η' : Fin n → Fin n → Cn n → ℂ)
          η.2 η'.2
        simpa only [Submodule.coe_add] using h
      map_smul' := fun c η => by
        have h := hdef_smul c (η : Fin n → Fin n → Cn n → ℂ) η.2
        simpa only [Submodule.coe_smul, RingHom.id_apply] using h }
  let f : V →ₗ[ℝ] (Fin n → Cn n → ℂ) := A - T0.comp Dr
  obtain ⟨q, hq⟩ := V.exists_isCompl
  let ψ0 : q →ₗ[ℝ] (Fin n → Cn n → ℂ) := 0
  let S2 : (Fin n → Fin n → Cn n → ℂ) →ₗ[ℝ] (Fin n → Cn n → ℂ) :=
    LinearMap.ofIsCompl hq f ψ0
  have hS2apply : ∀ (η : Fin n → Fin n → Cn n → ℂ) (hη : η ∈ V),
      S2 η = bmRow (fun a b w => χ w * η a b w) - T0 (bmDefect χ η) := by
    intro η hη
    have h := LinearMap.ofIsCompl_apply_left hq (φ := f) (ψ := ψ0) ⟨η, hη⟩
    calc S2 η = f ⟨η, hη⟩ := h
      _ = bmRow (fun a b w => χ w * η a b w) - T0 (bmDefect χ η) := rfl
  refine ⟨S2, fun k => (K1 k * Kχ k + C0 (k + 1) * KK k) + 1, ?_, ?_, ?_, ?_⟩
  · --# positivity of the constants
    intro k
    have h1 : 0 < K1 k * Kχ k := mul_pos (hK1pos k) (hKχpos k)
    have h2 : 0 < KK k := by
      rw [show KK k = (n : ℝ) * KM k from rfl]
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      refine mul_pos hn' ?_
      rw [show KM k = (n : ℝ) * Kdef k from rfl]
      exact mul_pos hn' (hKdefpos k)
    have h3 : 0 < C0 (k + 1) * KK k := mul_pos (hC0pos (k + 1)) h2
    linarith
  · --# clause (a): the equation, for globally `C¹` and globally closed data
    intro η hη hanti hclosed j l z hz
    have hηV : η ∈ V := fun i l => (hη i l).contDiffOn
    rw [hS2apply η hηV]
    obtain ⟨R, hRpos, hχR⟩ := exists_radius_of_hasCompactSupport' hχcs
    have hbm := Work.NN.Core.bmDefect_eq hn hRpos χ (hχCk 1) hχR η hη hclosed j l z
    have hD1cd : ∀ i l, ContDiffOn ℝ 1 (bmDefect χ η i l) (polydisc 0 ρm) := fun i l =>
      bmDefect_contDiffOn' hn hρ hχdiff hχcs hχts hχone (fun i l => (hη i l).contDiffOn) i l
    have hD1anti : IsAntisymmTwo (bmDefect χ η) := fun i l z' =>
      bmDefect_antisymm' hn hρ hχdiff hχcs hχts
        (fun i l => (hη i l).contDiffOn.of_le (zero_le' _)) hanti i l z'
    have hD1cl : IsClosedTwoOn ρm (bmDefect χ η) := fun i l m z' _ =>
      bmDefectClosed hn hχdiff hχcs hη hanti hclosed i l m z'
    have hsol := hT0solve (bmDefect χ η) hD1cd hD1anti hD1cl j l z hz
    have hχη : ∀ a b : Fin n, ContDiff ℝ 1 (fun w => χ w * η a b w) := fun a b =>
      Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ) (hχCk 1) hχts ((hη a b).contDiffOn)
    have hAd : DifferentiableAt ℝ (bmRow (fun a b w => χ w * η a b w) l) z :=
      differentiableAt_bmRow' hn (fun a b => hχη a b) (fun a b => hχcs.mul_right) l z
    have hAd' : DifferentiableAt ℝ (bmRow (fun a b w => χ w * η a b w) j) z :=
      differentiableAt_bmRow' hn (fun a b => hχη a b) (fun a b => hχcs.mul_right) j z
    have hBd : DifferentiableAt ℝ (T0 (bmDefect χ η) l) z :=
      (((hT0regN 1 (bmDefect χ η) hD1cd l).differentiableOn one_ne_zero).differentiableAt
        ((Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ').mem_nhds hz))
    have hBd' : DifferentiableAt ℝ (T0 (bmDefect χ η) j) z :=
      (((hT0regN 1 (bmDefect χ η) hD1cd j).differentiableOn one_ne_zero).differentiableAt
        ((Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ').mem_nhds hz))
    change dbarCoord j (fun w => bmRow (fun a b w => χ w * η a b w) l w
          - T0 (bmDefect χ η) l w) z
        - dbarCoord l (fun w => bmRow (fun a b w => χ w * η a b w) j w
          - T0 (bmDefect χ η) j w) z = η j l z
    rw [dbarCoord_sub_fun' j (f := bmRow (fun a b w => χ w * η a b w) l)
          (g := T0 (bmDefect χ η) l) (z := z) hAd hBd,
        dbarCoord_sub_fun' l (f := bmRow (fun a b w => χ w * η a b w) j)
          (g := T0 (bmDefect χ η) j) (z := z) hAd' hBd']
    linear_combination hbm - hsol
  · --# clause (b): the gain of one derivative
    intro k η hη hanti hclosed j
    set Sη : ℝ≥0∞ := ∑ i, ∑ l, holderNorm k α (η i l) (polydisc 0 ρ) with hSηdef
    have hηV : η ∈ V := fun i l =>
      (hη i l).contDiffOn.of_le (one_le_natCast_add_one' k)
    have hχηC : ∀ a b : Fin n, ContDiff ℝ (k + 1) (fun w => χ w * η a b w) := fun a b =>
      Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ) (hχCk (k + 1)) hχts ((hη a b).contDiffOn)
    have hη0 : ∀ i l, ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) (η i l) (polydisc 0 ρ) := fun i l =>
      (hη i l).contDiffOn.of_le (zero_le' _)
    have hηg1 : ∀ i l, ContDiff ℝ 1 (η i l) := fun i l =>
      (hη i l).of_le (one_le_natCast_add_one' k)
    have hD1cd : ∀ i l, ContDiffOn ℝ (k + 1) (bmDefect χ η i l) (polydisc 0 ρm) := fun i l =>
      bmDefect_contDiffOn' hn hρ hχdiff hχcs hχts hχone (fun i l => (hη i l).contDiffOn) i l
    have hD1anti : IsAntisymmTwo (bmDefect χ η) := fun i l z' =>
      bmDefect_antisymm' hn hρ hχdiff hχcs hχts hη0 hanti i l z'
    have hD1cl : IsClosedTwoOn ρm (bmDefect χ η) := fun i l m z' _ =>
      bmDefectClosed hn hχdiff hχcs hηg1 hanti hclosed i l m z'
    have hKKpos : 0 < KK k := by
      rw [show KK k = (n : ℝ) * KM k from rfl]
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      refine mul_pos hn' ?_
      rw [show KM k = (n : ℝ) * Kdef k from rfl]
      exact mul_pos hn' (hKdefpos k)
    have hD1sum : ∑ i, ∑ l, holderNorm (k + 1) α (bmDefect χ η i l) (polydisc 0 ρm)
        ≤ ENNReal.ofReal (KK k) * Sη := by
      have hstep : ∀ i ∈ Finset.univ, (∑ l, holderNorm (k + 1) α (bmDefect χ η i l)
            (polydisc 0 ρm)) ≤ ENNReal.ofReal (KM k) * Sη := by
        intro i _
        have hb : ∀ l ∈ Finset.univ, holderNorm (k + 1) α (bmDefect χ η i l) (polydisc 0 ρm)
            ≤ ENNReal.ofReal (Kdef k) * Sη := fun l _ =>
          hKdefspec k η (fun i l => (hη i l).contDiffOn) i l
        calc ∑ l, holderNorm (k + 1) α (bmDefect χ η i l) (polydisc 0 ρm)
            ≤ ∑ _l : Fin n, (ENNReal.ofReal (Kdef k) * Sη) := Finset.sum_le_sum hb
          _ = (n : ℝ≥0∞) * (ENNReal.ofReal (Kdef k) * Sη) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = ENNReal.ofReal (KM k) * Sη := by
              rw [show KM k = (n : ℝ) * Kdef k from rfl, ← ENNReal.ofReal_natCast n,
                ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      calc ∑ i, ∑ l, holderNorm (k + 1) α (bmDefect χ η i l) (polydisc 0 ρm)
          ≤ ∑ _i : Fin n, (ENNReal.ofReal (KM k) * Sη) := Finset.sum_le_sum hstep
        _ = (n : ℝ≥0∞) * (ENNReal.ofReal (KM k) * Sη) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ENNReal.ofReal (KK k) * Sη := by
            rw [show KK k = (n : ℝ) * KM k from rfl, ← ENNReal.ofReal_natCast n,
              ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    have hT0b : holderNorm (k + 1) α (T0 (bmDefect χ η) j) (polydisc 0 ρ')
        ≤ ENNReal.ofReal (C0 (k + 1)) * (ENNReal.ofReal (KK k) * Sη) :=
      (hT0est (k + 1) (bmDefect χ η) hD1cd hD1anti hD1cl j).trans (mul_le_mul_right hD1sum _)
    have hAb : holderNorm (k + 1) α (bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ')
        ≤ ENNReal.ofReal (K1 k) * (ENNReal.ofReal (Kχ k) * Sη) := by
      have h1 : holderNorm (k + 1) α (bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ)
          ≤ ENNReal.ofReal (K1 k) * ∑ l, ∑ m, holderNorm k α (fun w => χ w * η l m w) Set.univ :=
        hK1spec k (fun a b w => χ w * η a b w) (fun a b => hχηC a b)
          (fun a b z' hz' => by rw [hχvan z' hz', zero_mul]) j
      have h2 : holderNorm (k + 1) α (bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ')
          ≤ holderNorm (k + 1) α (bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ) :=
        Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ)
          (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ')
          (Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hlt j))) (k + 1) α _
      have h3 : ∑ l, ∑ m, holderNorm k α (fun w => χ w * η l m w) Set.univ
          ≤ ∑ l, ∑ m, ENNReal.ofReal (Kχ k) * holderNorm k α (η l m) (polydisc 0 ρ) :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ =>
          hKχspec k (η l m) (((hη l m).contDiffOn).of_le (natCast_le_add_one' k))
      have h4 : ∑ l, ∑ m, ENNReal.ofReal (Kχ k) * holderNorm k α (η l m) (polydisc 0 ρ)
          = ENNReal.ofReal (Kχ k) * Sη := by
        rw [hSηdef, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
      calc holderNorm (k + 1) α (bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ')
          ≤ holderNorm (k + 1) α (bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ) := h2
        _ ≤ ENNReal.ofReal (K1 k) * ∑ l, ∑ m,
              holderNorm k α (fun w => χ w * η l m w) Set.univ := h1
        _ ≤ ENNReal.ofReal (K1 k) * (∑ l, ∑ m,
              ENNReal.ofReal (Kχ k) * holderNorm k α (η l m) (polydisc 0 ρ)) :=
            mul_le_mul_right h3 _
        _ = ENNReal.ofReal (K1 k) * (ENNReal.ofReal (Kχ k) * Sη) := by rw [h4]
    have hAcd : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
        (bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ') :=
      (contDiff_bmRow' hn (fun a b => hχηC a b) (fun a b => hχcs.mul_right) j).contDiffOn
    have hBcd : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (T0 (bmDefect χ η) j) (polydisc 0 ρ') :=
      hT0regN (k + 1) (bmDefect χ η) hD1cd j
    have hsplit := holderNorm_sub_le' (k := k + 1) (α := α) (Ω := polydisc 0 ρ')
      (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ').uniqueDiffOn hAcd hBcd
    rw [hS2apply η hηV]
    calc holderNorm (k + 1) α
            ((bmRow (fun a b w => χ w * η a b w) - T0 (bmDefect χ η)) j) (polydisc 0 ρ')
        ≤ holderNorm (k + 1) α (bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ')
          + holderNorm (k + 1) α (T0 (bmDefect χ η) j) (polydisc 0 ρ') := hsplit
      _ ≤ ENNReal.ofReal (K1 k) * (ENNReal.ofReal (Kχ k) * Sη)
          + ENNReal.ofReal (C0 (k + 1)) * (ENNReal.ofReal (KK k) * Sη) := add_le_add hAb hT0b
      _ = (ENNReal.ofReal (K1 k) * ENNReal.ofReal (Kχ k)
            + ENNReal.ofReal (C0 (k + 1)) * ENNReal.ofReal (KK k)) * Sη := by ring
      _ ≤ ENNReal.ofReal ((K1 k * Kχ k + C0 (k + 1) * KK k) + 1) * Sη := by
          refine mul_le_mul_left ?_ _
          rw [← ENNReal.ofReal_mul (hK1pos k).le, ← ENNReal.ofReal_mul (hC0pos (k + 1)).le,
            ← ENNReal.ofReal_add (mul_nonneg (hK1pos k).le (hKχpos k).le)
              (mul_nonneg (hC0pos (k + 1)).le hKKpos.le)]
          exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)
  · --# clause (c): smoothness, for data smooth (and closed) on `polydisc 0 ρ`
    intro η hη hanti hclosed j
    have hηV : η ∈ V := fun i l => (hη i l).of_le (by exact_mod_cast le_top)
    rw [hS2apply η hηV]
    have hχηC : ∀ (N : ℕ) (a b : Fin n), ContDiff ℝ N (fun w => χ w * η a b w) := fun N a b =>
      Work.NN.Core.TelTwoDF.contDiff_mul_of_contDiffOn_of_tsupport_subset
        (Work.CR.Flat.isOpen_polydisc (0 : Cn n) ρ) (hχCk N) hχts
        ((hη a b).of_le (by exact_mod_cast le_top))
    have hA : ContDiffOn ℝ ∞ (bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ') :=
      contDiffOn_infty.mpr fun N =>
        (contDiff_bmRow' hn (fun a b => hχηC N a b) (fun a b => hχcs.mul_right) j).contDiffOn
    have hD1sm : ∀ i l, ContDiffOn ℝ ∞ (bmDefect χ η i l) (polydisc 0 ρm) := fun i l =>
      contDiffOn_infty.mpr fun N =>
        bmDefect_contDiffOn' hn hρ hχdiff hχcs hχts hχone
          (fun i l => (hη i l).of_le (by exact_mod_cast le_top)) i l
    have hB : ContDiffOn ℝ ∞ (T0 (bmDefect χ η) j) (polydisc 0 ρ') :=
      hT0smooth (bmDefect χ η) hD1sm j
    exact hA.sub hB


end Work.NN.Core
