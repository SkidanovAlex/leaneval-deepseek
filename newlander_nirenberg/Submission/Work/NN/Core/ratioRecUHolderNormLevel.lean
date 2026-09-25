import Mathlib
import Submission.Work.NN.Ratio.Defs
import Submission.Work.NN.Core.TelTwoDF.S2Estimate
import Submission.Work.NN.Core.TelTwoDF.dbarTransform_Eset_le
import Submission.Work.NN.Core.TelTwoDF.cut_mul_Eset_le
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded
import Submission.Work.CR.Flat.Cauchy.contDiff_dbarTransform

/-!
# The `C^{k,α}` bound for the ratio telescoping solution operator `Geom.recU`

The `(0,1)`-telescoping solution operator `Work.NN.Ratio.Geom.recU` (flexible thresholds) is
estimated on the `C^{k,α}` scale: for `0 < α < 1` there is a constant `C k > 0` with

  `‖G.recU g‖_{C^{k,α}(polydisc 0 G.e)} ≤ C k · ∑_j ‖g j‖_{C^{k,α}(polydisc 0 G.b)}`

for every datum `g` with `C^k` components.

The recursion is derivative-free: each stage is a product with the fixed smooth cutoff `cutFbar`
(Leibniz, `Work.CR.Flat.Holder.holderNorm_mul_le`) followed by the one-variable Cauchy transform
`dbarTransform G.r`, which is bounded on `C^{k,α}` with no loss of derivatives
(`Work.NN.Core.TelTwoDF.dbarTransform_Eset_le`, applied to the scalar-radius geometry
`toGeom G he`).  Tracking the stage-`m` data on the mixed polydisc `Trk G he m` (radius `G.e` in
the already-processed coordinates, `G.b` in the others) and iterating the one-step bound over the
`n` stages gives the estimate.
-/

set_option maxHeartbeats 1600000

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core

namespace RatioHolderLevel

open Work.CR.Flat.Cauchy (dbarTransform)

variable {n : ℕ}

/-- The scalar-radius `TelTwoDF.Geom` attached to a ratio geometry `G`: all radii are constant
(`G.e`, `G.a`, `G.b`, `G.r`).  Requires `0 < G.e`. -/
def toGeom (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) : Work.NN.Core.TelTwoDF.Geom n where
  e := fun _ => G.e
  a := fun _ => G.a
  b := fun _ => G.b
  r := fun _ => G.r
  he := fun _ => he
  hea := fun _ => G.hea
  ha := fun _ => G.ha
  hab := fun _ => G.hab
  hr := fun _ => G.hr0
  hbr := fun _ => by linarith [G.hr]

/-- The stage-`m` tracking polydisc: the first `m` coordinates are tracked at the solving radius
`G.e`, the remaining ones at the support radius `G.b`. -/
abbrev Trk (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) (m : ℕ) : Set (Fin n → ℂ) :=
  Work.NN.Core.TelTwoDF.Eset (toGeom G he) m

lemma isOpen_Trk (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) (m : ℕ) : IsOpen (Trk G he m) :=
  Work.NN.Core.TelTwoDF.isOpen_Eset (toGeom G he) m

lemma Trk_zero (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) :
    Trk G he 0 = Work.CR.Flat.polydisc 0 (fun _ => G.b) :=
  Work.NN.Core.TelTwoDF.Eset_zero (toGeom G he)

lemma Trk_subset_b (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) (m : ℕ) :
    Trk G he m ⊆ Work.CR.Flat.polydisc 0 (fun _ => G.b) :=
  Work.NN.Core.TelTwoDF.Eset_subset_b (toGeom G he) m

lemma Trk_mono (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) {m m' : ℕ} (h : m ≤ m') :
    Trk G he m' ⊆ Trk G he m :=
  Work.NN.Core.TelTwoDF.Eset_mono (toGeom G he) h

lemma Trk_ne_top (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) (m : ℕ) {k : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ (k + 1) f) :
    Work.CR.Flat.holderNorm k α f (Trk G he m) ≠ ⊤ :=
  Work.NN.Core.TelTwoDF.holderNorm_ne_top_Eset (toGeom G he) m hα0 hα1 hf

/-- The solve polydisc `polydisc 0 G.e` is contained in every tracking polydisc of positive
stage. -/
lemma polydisc_e_subset_Trk_succ (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) (m : ℕ) :
    Work.CR.Flat.polydisc 0 (fun _ => G.e) ⊆ Trk G he (m + 1) := by
  intro z hz
  show z ∈ Work.NN.Core.TelTwoDF.Eset (toGeom G he) (m + 1)
  rw [Work.NN.Core.TelTwoDF.mem_Eset]
  intro kk
  have hzk : ‖z kk‖ < G.e := by simpa using hz kk
  have heb : G.e ≤ G.b := le_of_lt (lt_trans G.hea G.hab)
  have hkb : Work.NN.Core.TelTwoDF.Erad (toGeom G he) (m + 1) kk
      = if (kk : ℕ) < m + 1 then G.e else G.b := rfl
  rw [hkb]
  by_cases hk : (kk : ℕ) < m + 1
  · simpa [hk] using hzk
  · simpa [hk] using lt_of_lt_of_le hzk heb

/-- A bound for the sup-norm on the polydisc of radius `G.b`. -/
lemma norm_le_b (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) {z : Fin n → ℂ}
    (hz : z ∈ Work.CR.Flat.polydisc 0 (fun _ => G.b)) :
    ‖z‖ ≤ ∑ k : Fin n, G.b := by
  have h := Work.NN.Core.TelTwoDF.norm_le_of_mem_Eset (toGeom G he) 0 (z := z) ?_
  · exact h
  · rw [Work.NN.Core.TelTwoDF.Eset_zero]; exact hz

/-- A uniform bound on the `C^{k,α}`-norms of the cutoffs `cutFbar j` and `cutF j` on the
polydisc of radius `G.b`. -/
def cutSup (G : Work.NN.Ratio.Geom n) (k : ℕ) (α : ℝ) : ℝ≥0∞ :=
  (∑ j, Work.CR.Flat.holderNorm k α (G.cutFbar j) (Work.CR.Flat.polydisc 0 (fun _ => G.b)))
    + (∑ j, Work.CR.Flat.holderNorm k α (G.cutF j) (Work.CR.Flat.polydisc 0 (fun _ => G.b)))
    + 1

/-- The `C^{k,α}` constant of a product with one of the cutoffs. -/
def stepL (G : Work.NN.Ratio.Geom n) (k : ℕ) (α : ℝ) : ℝ≥0∞ :=
  ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * cutSup G k α

lemma cutSup_ne_top (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) {k : ℕ} {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    cutSup G k α ≠ ⊤ := by
  have hbd : ∀ f : (Fin n → ℂ) → ℂ, ContDiff ℝ (k + 1) f →
      Work.CR.Flat.holderNorm k α f (Work.CR.Flat.polydisc 0 (fun _ => G.b)) ≠ ⊤ :=
    fun f hf => Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded
      (Work.CR.Flat.isOpen_polydisc 0 (fun _ => G.b)) (fun z hz => norm_le_b G he hz)
      hα0 (le_of_lt hα1) hf
  have h1 : (∑ j, Work.CR.Flat.holderNorm k α (G.cutFbar j)
        (Work.CR.Flat.polydisc 0 (fun _ => G.b))) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ =>
      hbd _ ((G.contDiff_cutFbar j).of_le (Work.NN.Ratio.le_infty (k + 1)))
  have h2 : (∑ j, Work.CR.Flat.holderNorm k α (G.cutF j)
        (Work.CR.Flat.polydisc 0 (fun _ => G.b))) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun j _ =>
      hbd _ ((G.contDiff_cutF j).of_le (Work.NN.Ratio.le_infty (k + 1)))
  rw [cutSup]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨h1, h2⟩, by simp⟩

lemma stepL_ne_top (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) {k : ℕ} {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    stepL G k α ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by norm_num)))
    (cutSup_ne_top G he hα0 hα1)

/-- The stages of the recursion inherit `C^k` from the datum. -/
lemma recF_contDiff_k (G : Work.NN.Ratio.Geom n) {k : ℕ} {g : Fin n → (Fin n → ℂ) → ℂ}
    (hg : ∀ j, ContDiff ℝ k (g j)) : ∀ m, ∀ i, ContDiff ℝ k (G.recF g m i) := by
  have hbr : G.b < G.r := by
    have hb0 : 0 < G.b := lt_trans G.ha G.hab
    linarith [G.hr]
  intro m
  induction m with
  | zero => intro i; simpa using hg i
  | succ m ih =>
      intro i
      rcases Nat.lt_or_ge m n with h | h
      · rw [Work.NN.Ratio.Geom.recF_succ_of_lt (G := G) h]
        exact Work.CR.Flat.Cauchy.contDiff_dbarTransform hbr ⟨m, h⟩ k
          (((G.contDiff_cutFbar ⟨m, h⟩).of_le (Work.NN.Ratio.le_infty k)).mul (ih i))
          (fun y hy => by rw [G.cutFbar_eq_zero_of_ge hy, zero_mul])
      · have hrec : G.recF g (m + 1) = G.recF g m := by
          rw [Work.NN.Ratio.Geom.recF_succ (G := G)]
          exact dite_eq_right (not_lt.mpr h)
        rw [hrec]
        exact ih i

/-- A bound for the `C^{k,α}`-norm of one cutoff on any tracking polydisc. -/
lemma holderNorm_cut_le (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) {k : ℕ} {α : ℝ} (j : Fin n) :
    Work.CR.Flat.holderNorm k α (G.cutF j) (Trk G he (j : ℕ)) ≤ cutSup G k α ∧
    Work.CR.Flat.holderNorm k α (G.cutFbar j) (Trk G he (j : ℕ)) ≤ cutSup G k α := by
  constructor
  · calc Work.CR.Flat.holderNorm k α (G.cutF j) (Trk G he (j : ℕ))
        ≤ Work.CR.Flat.holderNorm k α (G.cutF j)
            (Work.CR.Flat.polydisc 0 (fun _ => G.b)) :=
          Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 (fun _ => G.b))
            (isOpen_Trk G he (j : ℕ)) (Trk_subset_b G he (j : ℕ)) k α (G.cutF j)
      _ ≤ ∑ l, Work.CR.Flat.holderNorm k α (G.cutF l)
            (Work.CR.Flat.polydisc 0 (fun _ => G.b)) :=
          Finset.single_le_sum (f := fun l => Work.CR.Flat.holderNorm k α (G.cutF l)
            (Work.CR.Flat.polydisc 0 (fun _ => G.b))) (fun _ _ => zero_le) (Finset.mem_univ j)
      _ ≤ cutSup G k α := by rw [cutSup]; exact le_add_right (le_add_left le_rfl)
  · calc Work.CR.Flat.holderNorm k α (G.cutFbar j) (Trk G he (j : ℕ))
        ≤ Work.CR.Flat.holderNorm k α (G.cutFbar j)
            (Work.CR.Flat.polydisc 0 (fun _ => G.b)) :=
          Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc 0 (fun _ => G.b))
            (isOpen_Trk G he (j : ℕ)) (Trk_subset_b G he (j : ℕ)) k α (G.cutFbar j)
      _ ≤ ∑ l, Work.CR.Flat.holderNorm k α (G.cutFbar l)
            (Work.CR.Flat.polydisc 0 (fun _ => G.b)) :=
          Finset.single_le_sum (f := fun l => Work.CR.Flat.holderNorm k α (G.cutFbar l)
            (Work.CR.Flat.polydisc 0 (fun _ => G.b))) (fun _ _ => zero_le) (Finset.mem_univ j)
      _ ≤ cutSup G k α := by rw [cutSup]; exact le_add_right (le_add_right le_rfl)

/-- Leibniz with one of the cutoffs, on a tracking polydisc. -/
lemma holderNorm_cut_mul_le (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) {k : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {ζ : (Fin n → ℂ) → ℂ} (j : Fin n)
    (hζ : ContDiff ℝ k ζ) (hζle : Work.CR.Flat.holderNorm k α ζ (Trk G he (j : ℕ)) ≤ cutSup G k α)
    {A : ℝ≥0∞} (hA : A ≠ ⊤) {F : (Fin n → ℂ) → ℂ} (hF : ContDiff ℝ k F)
    (hFA : Work.CR.Flat.holderNorm k α F (Trk G he (j : ℕ)) ≤ A) :
    Work.CR.Flat.holderNorm k α (fun y => ζ y * F y) (Trk G he (j : ℕ)) ≤ stepL G k α * A := by
  have hne1 : Work.CR.Flat.holderNorm k α ζ (Trk G he (j : ℕ)) ≠ ⊤ :=
    ne_top_of_le_ne_top (cutSup_ne_top G he hα0 hα1) hζle
  have hne2 : Work.CR.Flat.holderNorm k α F (Trk G he (j : ℕ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hA hFA
  calc Work.CR.Flat.holderNorm k α (fun y => ζ y * F y) (Trk G he (j : ℕ))
      ≤ ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * Work.CR.Flat.holderNorm k α ζ (Trk G he (j : ℕ))
          * Work.CR.Flat.holderNorm k α F (Trk G he (j : ℕ)) :=
        Work.CR.Flat.Holder.holderNorm_mul_le hζ.contDiffOn hF.contDiffOn
          (isOpen_Trk G he (j : ℕ)).uniqueDiffOn hne1 hne2
    _ ≤ ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * cutSup G k α * A := by gcongr
    _ = stepL G k α * A := rfl

/-- One step of the recursion is bounded on the `C^{k,α}` scale. -/
lemma step_bound (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {k : ℕ} :
    ∃ K : ℝ≥0∞, 1 ≤ K ∧ K ≠ ⊤ ∧
      ∀ (s : Fin n) (F : Fin n → (Fin n → ℂ) → ℂ) (A : ℝ≥0∞),
        (∀ i, ContDiff ℝ k (F i)) → A ≠ ⊤ →
        (∀ i, Work.CR.Flat.holderNorm k α (F i) (Trk G he (s : ℕ)) ≤ A) →
        ∀ i, Work.CR.Flat.holderNorm k α (G.stepData s F i) (Trk G he ((s : ℕ) + 1)) ≤ K * A := by
  obtain ⟨CT, _hCTpos, hCT⟩ :=
    Work.NN.Core.TelTwoDF.dbarTransform_Eset_le (n := n) hα0 hα1 k (toGeom G he)
  refine ⟨ENNReal.ofReal CT * stepL G k α + 1, le_add_left le_rfl, ?_, ?_⟩
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (stepL_ne_top G he hα0 hα1), by simp⟩
  · intro s F A hF hA hAb i
    have hcs : ContDiff ℝ k (fun y => G.cutFbar s y * F i y) :=
      ((G.contDiff_cutFbar s).of_le (Work.NN.Ratio.le_infty k)).mul (hF i)
    have hsupp : ∀ y : Fin n → ℂ, G.b ≤ ‖y s‖ → G.cutFbar s y * F i y = 0 :=
      fun y hy => by rw [G.cutFbar_eq_zero_of_ge hy, zero_mul]
    have hleib : Work.CR.Flat.holderNorm k α (fun y => G.cutFbar s y * F i y)
        (Trk G he (s : ℕ)) ≤ stepL G k α * A :=
      holderNorm_cut_mul_le G he hα0 hα1 s
        ((G.contDiff_cutFbar s).of_le (Work.NN.Ratio.le_infty k))
        (holderNorm_cut_le G he s).2 hA (hF i) (hAb i)
    calc Work.CR.Flat.holderNorm k α (G.stepData s F i) (Trk G he ((s : ℕ) + 1))
        = Work.CR.Flat.holderNorm k α (dbarTransform G.r s (fun y => G.cutFbar s y * F i y))
            (Trk G he ((s : ℕ) + 1)) := rfl
      _ ≤ ENNReal.ofReal CT * Work.CR.Flat.holderNorm k α
            (fun y => G.cutFbar s y * F i y) (Trk G he (s : ℕ)) := hCT s _ hcs hsupp
      _ ≤ ENNReal.ofReal CT * (stepL G k α * A) := mul_le_mul_right hleib _
      _ = (ENNReal.ofReal CT * stepL G k α) * A := by rw [mul_assoc]
      _ ≤ (ENNReal.ofReal CT * stepL G k α + 1) * A := by
          rw [add_mul, one_mul]; exact le_self_add

/-- The stage-`m` bound: the `C^{k,α}`-norms of the stage data grow at most geometrically. -/
lemma stage_bound (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {k : ℕ} :
    ∃ K : ℝ≥0∞, 1 ≤ K ∧ K ≠ ⊤ ∧
      ∀ (g : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ k (g j)) → ∀ A : ℝ≥0∞, A ≠ ⊤ →
        (∀ j, Work.CR.Flat.holderNorm k α (g j) (Trk G he 0) ≤ A) →
        ∀ (m : ℕ), m ≤ n → ∀ i,
          Work.CR.Flat.holderNorm k α (G.recF g m i) (Trk G he m) ≤ K ^ m * A := by
  obtain ⟨K, hK1, hKne, hK⟩ := step_bound (n := n) G he hα0 hα1 (k := k)
  refine ⟨K, hK1, hKne, ?_⟩
  intro g hg A hA hAb m
  induction m with
  | zero => intro _ i; simpa using hAb i
  | succ m ih =>
      intro hm i
      have hm' : m < n := by omega
      have hKmA : K ^ m * A ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hKne) hA
      have hdh : ∀ i, Work.CR.Flat.holderNorm k α (G.recF g m i) (Trk G he m) ≤ K ^ m * A :=
        fun i => ih (by omega) i
      have hcontm : ∀ i, ContDiff ℝ k (G.recF g m i) := fun i => recF_contDiff_k G hg m i
      rw [Work.NN.Ratio.Geom.recF_succ_of_lt (G := G) hm']
      calc Work.CR.Flat.holderNorm k α
            (G.stepData ⟨m, hm'⟩ (G.recF g m) i) (Trk G he (m + 1))
          ≤ K * (K ^ m * A) := hK ⟨m, hm'⟩ (G.recF g m) (K ^ m * A) hcontm hKmA hdh i
        _ = K ^ (m + 1) * A := by rw [pow_succ, ← mul_assoc, mul_comm K (K ^ m)]

/-- The bound for one summand of the explicit solution. -/
lemma psi_bound (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {k : ℕ} :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ (g : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ k (g j)) → ∀ A : ℝ≥0∞, A ≠ ⊤ →
        (∀ j, Work.CR.Flat.holderNorm k α (g j) (Trk G he 0) ≤ A) → ∀ j : Fin n,
          Work.CR.Flat.holderNorm k α (dbarTransform G.r j
              (fun y => G.cutF j y * G.recF g (j : ℕ) j y))
              (Work.CR.Flat.polydisc 0 (fun _ => G.e)) ≤ K * A := by
  obtain ⟨KS, hKS1, hKSne, hKS⟩ := stage_bound (n := n) G he hα0 hα1 (k := k)
  obtain ⟨CT, _hCTpos, hCT⟩ :=
    Work.NN.Core.TelTwoDF.dbarTransform_Eset_le (n := n) hα0 hα1 k (toGeom G he)
  refine ⟨ENNReal.ofReal CT * stepL G k α * KS ^ n + 1, ?_, ?_⟩
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (stepL_ne_top G he hα0 hα1)) (ENNReal.pow_ne_top hKSne), by simp⟩
  · intro g hg A hA hAb j
    have hjn : (j : ℕ) ≤ n := le_of_lt j.isLt
    have hstage := hKS g hg A hA hAb (j : ℕ) hjn j
    have hc : ContDiff ℝ k (fun y => G.cutF j y * G.recF g (j : ℕ) j y) :=
      ((G.contDiff_cutF j).of_le (Work.NN.Ratio.le_infty k)).mul
        (recF_contDiff_k G hg (j : ℕ) j)
    have hsupp : ∀ y : Fin n → ℂ, G.b ≤ ‖y j‖ → G.cutF j y * G.recF g (j : ℕ) j y = 0 :=
      fun y hy => by rw [G.cutF_eq_zero hy, zero_mul]
    have hleib : Work.CR.Flat.holderNorm k α
        (fun y => G.cutF j y * G.recF g (j : ℕ) j y) (Trk G he (j : ℕ))
        ≤ stepL G k α * (KS ^ (j : ℕ) * A) :=
      holderNorm_cut_mul_le G he hα0 hα1 j
        ((G.contDiff_cutF j).of_le (Work.NN.Ratio.le_infty k)) (holderNorm_cut_le G he j).1
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top hKSne) hA) (recF_contDiff_k G hg (j : ℕ) j) hstage
    calc Work.CR.Flat.holderNorm k α (dbarTransform G.r j
            (fun y => G.cutF j y * G.recF g (j : ℕ) j y))
            (Work.CR.Flat.polydisc 0 (fun _ => G.e))
        ≤ Work.CR.Flat.holderNorm k α (dbarTransform G.r j
            (fun y => G.cutF j y * G.recF g (j : ℕ) j y)) (Trk G he ((j : ℕ) + 1)) :=
          Work.CR.Flat.holderNorm_mono_set (isOpen_Trk G he ((j : ℕ) + 1))
            (Work.CR.Flat.isOpen_polydisc 0 (fun _ => G.e))
            (polydisc_e_subset_Trk_succ G he (j : ℕ)) k α _
      _ ≤ ENNReal.ofReal CT * Work.CR.Flat.holderNorm k α
            (fun y => G.cutF j y * G.recF g (j : ℕ) j y) (Trk G he (j : ℕ)) := hCT j _ hc hsupp
      _ ≤ ENNReal.ofReal CT * (stepL G k α * (KS ^ (j : ℕ) * A)) := mul_le_mul_right hleib _
      _ ≤ ENNReal.ofReal CT * (stepL G k α * (KS ^ n * A)) := by
          gcongr
      _ ≤ (ENNReal.ofReal CT * stepL G k α * KS ^ n + 1) * A := by
          rw [← mul_assoc, ← mul_assoc, add_mul, one_mul]
          exact le_self_add

/-- The `C^{k,α}` bound for the explicit solution operator. -/
lemma recU_bound (G : Work.NN.Ratio.Geom n) (he : 0 < G.e) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {k : ℕ} :
    ∃ K : ℝ≥0∞, 1 ≤ K ∧ K ≠ ⊤ ∧
      ∀ (g : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ k (g j)) → ∀ A : ℝ≥0∞, A ≠ ⊤ →
        (∀ j, Work.CR.Flat.holderNorm k α (g j) (Trk G he 0) ≤ A) →
        Work.CR.Flat.holderNorm k α (fun z => G.recU g z)
            (Work.CR.Flat.polydisc 0 (fun _ => G.e)) ≤ K * A := by
  obtain ⟨Kp, hKpne, hKp⟩ := psi_bound (n := n) G he hα0 hα1 (k := k)
  have hbr : G.b < G.r := by
    have hb0 : 0 < G.b := lt_trans G.ha G.hab
    linarith [G.hr]
  refine ⟨(n : ℝ≥0∞) * Kp + 1, le_add_left le_rfl, ?_, ?_⟩
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hKpne, by simp⟩
  · intro g hg A hA hAb
    have hsum : ∀ j : Fin n, Work.CR.Flat.holderNorm k α (dbarTransform G.r j
        (fun y => G.cutF j y * G.recF g (j : ℕ) j y))
        (Work.CR.Flat.polydisc 0 (fun _ => G.e)) ≤ Kp * A := fun j => hKp g hg A hA hAb j
    have hcont : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        ContDiffOn ℝ (k : ℕ∞ω) (dbarTransform G.r j
          (fun y => G.cutF j y * G.recF g (j : ℕ) j y))
          (Work.CR.Flat.polydisc 0 (fun _ => G.e)) := by
      intro j _
      have hc : ContDiff ℝ k (fun y => G.cutF j y * G.recF g (j : ℕ) j y) :=
        ((G.contDiff_cutF j).of_le (Work.NN.Ratio.le_infty k)).mul
          (recF_contDiff_k G hg (j : ℕ) j)
      exact (Work.CR.Flat.Cauchy.contDiff_dbarTransform hbr j k hc
        (fun y hy => by rw [G.cutF_eq_zero hy, zero_mul])).contDiffOn
    have hfun : (fun z => G.recU g z) = fun z => ∑ j : Fin n, dbarTransform G.r j
        (fun y => G.cutF j y * G.recF g (j : ℕ) j y) z := rfl
    calc Work.CR.Flat.holderNorm k α (fun z => G.recU g z)
          (Work.CR.Flat.polydisc 0 (fun _ => G.e))
        = Work.CR.Flat.holderNorm k α (fun z => ∑ j : Fin n, dbarTransform G.r j
            (fun y => G.cutF j y * G.recF g (j : ℕ) j y) z)
            (Work.CR.Flat.polydisc 0 (fun _ => G.e)) := by rw [hfun]
      _ ≤ ∑ j : Fin n, Work.CR.Flat.holderNorm k α (dbarTransform G.r j
            (fun y => G.cutF j y * G.recF g (j : ℕ) j y))
            (Work.CR.Flat.polydisc 0 (fun _ => G.e)) :=
          Work.CR.Flat.Holder.holderNorm_sum_le Finset.univ hcont
            (Work.CR.Flat.isOpen_polydisc 0 (fun _ => G.e)).uniqueDiffOn
      _ ≤ ∑ _j : Fin n, Kp * A := Finset.sum_le_sum fun j _ => hsum j
      _ = (n : ℝ≥0∞) * (Kp * A) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ((n : ℝ≥0∞) * Kp + 1) * A := by rw [← mul_assoc, add_mul, one_mul]; exact le_self_add

end RatioHolderLevel

theorem ratioRecUHolderNormLevel {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (G : Work.NN.Ratio.Geom n) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (g : Fin n → (Fin n → ℂ) → ℂ),
        (∀ j, ContDiff ℝ k (g j)) →
        Work.CR.Flat.holderNorm k α (fun z => G.recU g z)
            (Work.CR.Flat.polydisc 0 (fun _ => G.e))
          ≤ ENNReal.ofReal (C k) *
              ∑ j, Work.CR.Flat.holderNorm k α (g j)
                (Work.CR.Flat.polydisc 0 (fun _ => G.b)) := by
  classical
  by_cases he : 0 < G.e
  · have hb : ∀ k : ℕ, ∃ K : ℝ≥0∞, 1 ≤ K ∧ K ≠ ⊤ ∧
        ∀ (g : Fin n → (Fin n → ℂ) → ℂ), (∀ j, ContDiff ℝ k (g j)) → ∀ A : ℝ≥0∞, A ≠ ⊤ →
          (∀ j, Work.CR.Flat.holderNorm k α (g j) (RatioHolderLevel.Trk G he 0) ≤ A) →
          Work.CR.Flat.holderNorm k α (fun z => G.recU g z)
              (Work.CR.Flat.polydisc 0 (fun _ => G.e)) ≤ K * A :=
      fun k => RatioHolderLevel.recU_bound G he hα0 hα1 (k := k)
    refine ⟨fun k => (Classical.choose (hb k)).toReal + 1, fun k => by positivity, ?_⟩
    intro k g hg
    obtain ⟨hK1, hKne, hKb⟩ := Classical.choose_spec (hb k)
    have hCeq : ENNReal.ofReal ((Classical.choose (hb k)).toReal + 1)
        = Classical.choose (hb k) + 1 := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal hKne]
      norm_num
    rw [hCeq]
    set S : ℝ≥0∞ := ∑ j, Work.CR.Flat.holderNorm k α (g j)
      (Work.CR.Flat.polydisc 0 (fun _ => G.b)) with hS
    by_cases htop : S = ⊤
    · rw [htop, ENNReal.mul_top (by simp)]
      exact le_top
    · have hAb : ∀ j, Work.CR.Flat.holderNorm k α (g j)
          (RatioHolderLevel.Trk G he 0) ≤ S := by
        intro j
        rw [RatioHolderLevel.Trk_zero]
        exact Finset.single_le_sum (f := fun j => Work.CR.Flat.holderNorm k α (g j)
          (Work.CR.Flat.polydisc 0 (fun _ => G.b))) (fun _ _ => zero_le) (Finset.mem_univ j)
      have hmain := hKb g hg S htop hAb
      exact le_trans hmain (mul_le_mul_left le_self_add S)
  · refine ⟨fun _ => 1, fun _ => one_pos, ?_⟩
    intro k g hg
    have hzero : Work.CR.Flat.holderNorm k α (fun z => G.recU g z)
        (Work.CR.Flat.polydisc 0 (fun _ => G.e)) = 0 := by
      by_cases hn : n = 0
      · subst hn
        have hfun : (fun z => G.recU g z) = fun _ => (0 : ℂ) := by
          funext z
          simp [Work.NN.Ratio.Geom.recU]
        rw [hfun]
        simp [Work.CR.Flat.holderNorm, Work.CR.Flat.iterDerivNorm, Work.CR.Flat.holderSeminorm]
      · have hemp : Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => G.e)
            = (∅ : Set (Fin n → ℂ)) := by
          ext z
          constructor
          · intro hz
            have h := hz ⟨0, Nat.pos_of_ne_zero hn⟩
            simp only [Pi.zero_apply, sub_zero] at h
            linarith [norm_nonneg (z ⟨0, Nat.pos_of_ne_zero hn⟩), le_of_not_gt he]
          · intro hz
            exact absurd hz (by simp)
        rw [hemp]
        simp [Work.CR.Flat.holderNorm, Work.CR.Flat.iterDerivNorm, Work.CR.Flat.holderSeminorm]
    rw [hzero]
    exact zero_le

end Work.NN.Core
