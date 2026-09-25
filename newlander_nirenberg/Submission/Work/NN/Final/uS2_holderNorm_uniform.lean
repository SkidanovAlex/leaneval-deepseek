/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `C^{k,α}` estimate for the `(0,2)`-recursion operator `uS2` at every order `k`

`Work.NN.Final.uS2` is the explicit coordinate-by-coordinate solution operator of the
`(0,2)`-`∂̄`-equation `∂̄_j ψ_l - ∂̄_l ψ_j = η_{jl}` on the unit polydisc
(`Submission/Work/NN/Final/twoRec.lean`).  This file proves that for every `k` there is a
constant `C k > 0`, independent of the datum `η`, with

  `‖uS2 η j‖_{C^{k,α}(solveSet)} ≤ C k · ∑_{i,l} ‖η_{i l}‖_{C^{k,α}(P(0,1))}`

for every `η` with `C^k` components and every `j`.

## Route

The recursion `uStep s D = (1 - cutF s) · D + T_s (cutFbar s · D)` is *derivative free*: it is a
product with a fixed smooth cutoff plus a one-variable Cauchy transform `T_s` of a
fibre-supported function.  Consequently, for every `k`, one step of the recursion maps a
`C^{k,α}`-bound on the stage data `D` to a `C^{k,α}`-bound on the next stage:

* multiplication by the fixed cutoffs is bounded on `C^{k,α}` (Leibniz,
  `Work.CR.Flat.Holder.holderNorm_mul_le`, together with the finiteness of the `C^{k,α}` norms of
  the cutoffs on the bounded set `trackSet`,
  `Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded`);
* the Cauchy-transform step is bounded on `C^{k,α}` with no loss of derivatives
  (`Work.NN.Final.dbarTransform_holderNorm_le`).

Iterating the one-step bound over the `n` stages of the recursion (`stage_bound`), and once more
for the `(0,1)`-form `uPsi`, gives the estimate for each summand of `uS2`; the final assembly
sums the `n` summands and converts the `ℝ≥0∞`-valued constants into a real constant `C k`.
-/
import Mathlib
import Submission.Work.NN.Final.uS2_estimate
import Submission.Work.NN.Final.twoRec
import Submission.Work.NN.Final.uS2_smooth
import Submission.Work.NN.Final.dbarTransform_holderNorm_le
import Submission.Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Holder.holderNorm_add_le

set_option maxHeartbeats 1200000

noncomputable section
open scoped NNReal ENNReal ContDiff
open MeasureTheory Set

namespace Work.NN.Final
open Work.CR.Flat Work.CR.Flat.Cauchy

variable {n : ℕ}

/-! ## The tracked and solution sets -/

lemma trackSet_eq_polydisc {n : ℕ} :
    (trackSet : Set (Fin n → ℂ)) = polydisc 0 (fun _ => trTrack) := by
  ext z; simp [mem_polydisc]

lemma solveSet_eq_polydisc {n : ℕ} :
    (solveSet : Set (Fin n → ℂ)) = polydisc 0 (fun _ => eqRad) := by
  ext z; simp [mem_polydisc]

lemma isOpen_solveSet {n : ℕ} : IsOpen (solveSet : Set (Fin n → ℂ)) := by
  rw [solveSet_eq_polydisc]; exact isOpen_polydisc 0 _

lemma solveSet_subset_trackSet {n : ℕ} : (solveSet : Set (Fin n → ℂ)) ⊆ trackSet :=
  fun _ hz l => lt_trans (hz l) eqRad_lt_trTrack

lemma trackSet_subset_unit {n : ℕ} : (trackSet : Set (Fin n → ℂ)) ⊆ polydisc 0 (fun _ => 1) :=
  fun z hz l => by
    simpa using lt_trans (hz l) (by norm_num [trTrack] : trTrack < 1)

lemma norm_le_trTrack_of_mem_trackSet {n : ℕ} {z : Fin n → ℂ} (hz : z ∈ trackSet) :
    ‖z‖ ≤ trTrack := by
  have h : ‖z‖₊ ≤ (⟨trTrack, le_of_lt trTrack_pos⟩ : ℝ≥0) := by
    rw [Pi.nnnorm_def]
    exact Finset.sup_le_iff.mpr (fun b _ => by exact_mod_cast (le_of_lt (hz b)))
  exact_mod_cast h

/-! ## Preservation of finite smoothness by the recursion -/

lemma uStep_contDiff_k {k : ℕ} {s : Fin n}
    {D : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hD : ∀ i l, ContDiff ℝ k (D i l)) (i l : Fin n) :
    ContDiff ℝ k (uStep s D i l) := by
  by_cases hc : i = s ∨ l = s
  · have hfun : uStep s D i l = fun z => (1 - cutF s z) * D i l z := by
      funext z; rw [uStep_apply, if_pos hc]; ring
    rw [hfun]
    exact (((contDiff_const.sub (contDiff_cutF s)).of_le (by exact_mod_cast le_top)).mul (hD i l))
  · have hfun : uStep s D i l = fun z => (1 - cutF s z) * D i l z
        + dTLM s (fun y => cutFbar s y * D i l y) z := by
      funext z; rw [uStep_apply, if_neg hc]
    rw [hfun]
    refine ContDiff.add ((((contDiff_const.sub (contDiff_cutF s)).of_le
      (by exact_mod_cast le_top)).mul (hD i l))) ?_
    rw [dTLM_eq (((contDiff_cutFbar s).of_le (by exact_mod_cast le_top)).mul (hD i l)).continuous]
    exact contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho]) s k
      (((contDiff_cutFbar s).of_le (by exact_mod_cast le_top)).mul (hD i l))
      (fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul])

lemma uD_contDiff_k {k : ℕ} {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiff ℝ k (η i l)) :
    ∀ m ≤ n, ∀ i l, ContDiff ℝ k (uD η m i l) := by
  intro m
  induction m with
  | zero => intro _; simpa using hη
  | succ m ih =>
      intro hm i l
      have hm' : m < n := by omega
      rw [uD_succ_of_lt η hm']
      exact uStep_contDiff_k (fun i l => ih (by omega) i l) i l

/-! ## The cutoff constants -/

/-- A uniform bound for the `C^{k,α}` norms on `trackSet` of the three cutoff families occurring
in the recursion: `cutF s`, `cutFbar s` and `1 - cutF s`.  (The tracked set is bounded, so each
of these norms is finite: `Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded`.) -/
noncomputable def cutSup (k : ℕ) (α : ℝ) : ℝ≥0∞ :=
  (∑ s : Fin n, holderNorm k α (cutF s) trackSet)
    + (∑ s : Fin n, holderNorm k α (cutFbar s) trackSet)
    + (∑ s : Fin n, holderNorm k α (fun z => 1 - cutF s z) trackSet) + 1

/-- The `C^{k,α}` constant carried by a product with one of the cutoffs: the Leibniz constant
`(k+1) 2^{k+1}` times the bound `cutSup` for the cutoff norms. -/
noncomputable def stepL (k : ℕ) (α : ℝ) : ℝ≥0∞ :=
  ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * cutSup (n := n) k α

lemma cutSup_ne_top {k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    cutSup (n := n) k α ≠ ⊤ := by
  have hbd : ∀ ζ : (Fin n → ℂ) → ℂ, ContDiff ℝ (k + 1) ζ →
      holderNorm k α ζ trackSet ≠ ⊤ := fun ζ hζ =>
    Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded isOpen_trackSet
      (fun z hz => norm_le_trTrack_of_mem_trackSet hz) hα0 (le_of_lt hα1) hζ
  have h1 : (∑ s : Fin n, holderNorm k α (cutF s) trackSet) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun s _ => hbd _ ((contDiff_cutF s).of_le (by exact_mod_cast le_top))
  have h2 : (∑ s : Fin n, holderNorm k α (cutFbar s) trackSet) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun s _ =>
      hbd _ ((contDiff_cutFbar s).of_le (by exact_mod_cast le_top))
  have h3 : (∑ s : Fin n, holderNorm k α (fun z => 1 - cutF s z) trackSet) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun s _ =>
      hbd _ ((contDiff_const.sub (contDiff_cutF s)).of_le (by exact_mod_cast le_top))
  rw [cutSup]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨h1, h2⟩, h3⟩,
    by simp⟩

lemma stepL_ne_top {k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    stepL (n := n) k α ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by norm_num)))
    (cutSup_ne_top hα0 hα1)

lemma stepL_eq (k : ℕ) (α : ℝ) :
    stepL (n := n) k α = ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * cutSup (n := n) k α := rfl

lemma holderNorm_cutF_le_cutSup {k : ℕ} {α : ℝ} (s : Fin n) :
    holderNorm k α (cutF s) trackSet ≤ cutSup (n := n) k α := by
  have h1 : holderNorm k α (cutF s) trackSet
      ≤ ∑ s : Fin n, holderNorm k α (cutF s) trackSet :=
    Finset.single_le_sum (f := fun s : Fin n => holderNorm k α (cutF s) trackSet)
      (fun _ _ => zero_le) (Finset.mem_univ s)
  rw [cutSup]
  calc holderNorm k α (cutF s) trackSet ≤ ∑ s : Fin n, holderNorm k α (cutF s) trackSet := h1
    _ ≤ (∑ s : Fin n, holderNorm k α (cutF s) trackSet)
          + (∑ s : Fin n, holderNorm k α (cutFbar s) trackSet) := le_add_right le_rfl
    _ ≤ (∑ s : Fin n, holderNorm k α (cutF s) trackSet)
          + (∑ s : Fin n, holderNorm k α (cutFbar s) trackSet)
          + (∑ s : Fin n, holderNorm k α (fun z => 1 - cutF s z) trackSet) :=
        le_add_right le_rfl
    _ ≤ (∑ s : Fin n, holderNorm k α (cutF s) trackSet)
          + (∑ s : Fin n, holderNorm k α (cutFbar s) trackSet)
          + (∑ s : Fin n, holderNorm k α (fun z => 1 - cutF s z) trackSet) + 1 :=
        le_add_right le_rfl

lemma holderNorm_cutFbar_le_cutSup {k : ℕ} {α : ℝ} (s : Fin n) :
    holderNorm k α (cutFbar s) trackSet ≤ cutSup (n := n) k α := by
  have h1 : holderNorm k α (cutFbar s) trackSet
      ≤ ∑ s : Fin n, holderNorm k α (cutFbar s) trackSet :=
    Finset.single_le_sum (f := fun s : Fin n => holderNorm k α (cutFbar s) trackSet)
      (fun _ _ => zero_le) (Finset.mem_univ s)
  rw [cutSup]
  calc holderNorm k α (cutFbar s) trackSet
        ≤ ∑ s : Fin n, holderNorm k α (cutFbar s) trackSet := h1
    _ ≤ (∑ s : Fin n, holderNorm k α (cutF s) trackSet)
          + (∑ s : Fin n, holderNorm k α (cutFbar s) trackSet) := le_add_left le_rfl
    _ ≤ (∑ s : Fin n, holderNorm k α (cutF s) trackSet)
          + (∑ s : Fin n, holderNorm k α (cutFbar s) trackSet)
          + (∑ s : Fin n, holderNorm k α (fun z => 1 - cutF s z) trackSet) :=
        le_add_right le_rfl
    _ ≤ (∑ s : Fin n, holderNorm k α (cutF s) trackSet)
          + (∑ s : Fin n, holderNorm k α (cutFbar s) trackSet)
          + (∑ s : Fin n, holderNorm k α (fun z => 1 - cutF s z) trackSet) + 1 :=
        le_add_right le_rfl

lemma holderNorm_oneSubCutF_le_cutSup {k : ℕ} {α : ℝ} (s : Fin n) :
    holderNorm k α (fun z => 1 - cutF s z) trackSet ≤ cutSup (n := n) k α := by
  have h1 : holderNorm k α (fun z => 1 - cutF s z) trackSet
      ≤ ∑ s : Fin n, holderNorm k α (fun z => 1 - cutF s z) trackSet :=
    Finset.single_le_sum (f := fun s : Fin n => holderNorm k α (fun z => 1 - cutF s z) trackSet)
      (fun _ _ => zero_le) (Finset.mem_univ s)
  rw [cutSup]
  calc holderNorm k α (fun z => 1 - cutF s z) trackSet
        ≤ ∑ s : Fin n, holderNorm k α (fun z => 1 - cutF s z) trackSet := h1
    _ ≤ (∑ s : Fin n, holderNorm k α (cutF s) trackSet)
          + (∑ s : Fin n, holderNorm k α (cutFbar s) trackSet)
          + (∑ s : Fin n, holderNorm k α (fun z => 1 - cutF s z) trackSet) :=
        le_add_left le_rfl
    _ ≤ (∑ s : Fin n, holderNorm k α (cutF s) trackSet)
          + (∑ s : Fin n, holderNorm k α (cutFbar s) trackSet)
          + (∑ s : Fin n, holderNorm k α (fun z => 1 - cutF s z) trackSet) + 1 :=
        le_add_right le_rfl

/-- Leibniz with a cutoff whose `C^{k,α}` norm on `trackSet` is bounded by `cutSup`. -/
lemma holderNorm_cut_mul_le {k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ζ : (Fin n → ℂ) → ℂ} (hζ : ContDiff ℝ k ζ)
    (hζle : holderNorm k α ζ trackSet ≤ cutSup (n := n) k α)
    {B : ℝ≥0∞} (hB : B ≠ ⊤) {f : (Fin n → ℂ) → ℂ}
    (hf : ContDiff ℝ k f) (hfB : holderNorm k α f trackSet ≤ B) :
    holderNorm k α (fun y => ζ y * f y) trackSet ≤ stepL (n := n) k α * B := by
  rw [stepL_eq]
  have hne : holderNorm k α ζ trackSet ≠ ⊤ :=
    ne_top_of_le_ne_top (cutSup_ne_top hα0 hα1) hζle
  have hfne : holderNorm k α f trackSet ≠ ⊤ := ne_top_of_le_ne_top hB hfB
  refine le_trans (Work.CR.Flat.Holder.holderNorm_mul_le (k := k) (α := α) (f := ζ) (g := f)
    (Ω := trackSet) hζ.contDiffOn hf.contDiffOn isOpen_trackSet.uniqueDiffOn hne hfne) ?_
  refine le_trans (mul_le_mul_left (mul_le_mul_right hζle (((k : ℝ≥0∞) + 1) * 2 ^ (k + 1)))
    (holderNorm k α f trackSet)) ?_
  exact mul_le_mul_right hfB (((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * cutSup (n := n) k α)

/-! ## One step of the recursion -/

lemma step_bound {k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ≥0∞, 1 ≤ K ∧ K ≠ ⊤ ∧ ∀ (D : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiff ℝ k (D i l)) → ∀ (A : ℝ≥0∞), A ≠ ⊤ →
      (∀ i l, holderNorm k α (D i l) trackSet ≤ A) → ∀ (s : Fin n) (i l : Fin n),
        holderNorm k α (uStep s D i l) trackSet ≤ K * A := by
  obtain ⟨CT, _hCT0, hCT⟩ := dbarTransform_holderNorm_le (n := n) hα0 hα1 k
  refine ⟨(1 + stepL (n := n) k α + ENNReal.ofReal CT * stepL (n := n) k α) + 1,
    by simp, ?_, ?_⟩
  · refine ENNReal.add_ne_top.mpr ⟨?_, by simp⟩
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · exact ENNReal.add_ne_top.mpr ⟨by simp, stepL_ne_top hα0 hα1⟩
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (stepL_ne_top hα0 hα1)
  · intro D hD A hA hAb s i l
    -- the direct part
    have hdir : holderNorm k α (fun z => (1 - cutF s z) * D i l z) trackSet
        ≤ stepL (n := n) k α * A :=
      holderNorm_cut_mul_le (n := n) (ζ := fun z => 1 - cutF s z) (f := D i l) hα0 hα1
        ((contDiff_const.sub (contDiff_cutF s)).of_le (by exact_mod_cast le_top))
        (holderNorm_oneSubCutF_le_cutSup s) hA (hD i l) (hAb i l)
    -- the transform part
    have hT : holderNorm k α (dTLM s (fun y => cutFbar s y * D i l y)) trackSet
        ≤ ENNReal.ofReal CT * stepL (n := n) k α * A := by
      have hc : ContDiff ℝ k (fun y : Fin n → ℂ => cutFbar s y * D i l y) :=
        ((contDiff_cutFbar s).of_le (by exact_mod_cast le_top)).mul (hD i l)
      rw [dTLM_eq hc.continuous]
      refine le_trans (hCT s _ hc (fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul])) ?_
      refine le_trans (mul_le_mul_right (holderNorm_cut_mul_le (n := n) (ζ := cutFbar s)
        (f := D i l) hα0 hα1 ((contDiff_cutFbar s).of_le (by exact_mod_cast le_top))
        (holderNorm_cutFbar_le_cutSup s) hA (hD i l) (hAb i l)) (ENNReal.ofReal CT)) ?_
      exact le_of_eq (mul_assoc (ENNReal.ofReal CT) (stepL (n := n) k α) A).symm
    by_cases hc : i = s ∨ l = s
    · rw [show uStep s D i l = fun z => (1 - cutF s z) * D i l z from by
        funext z; rw [uStep_apply, if_pos hc, add_zero]]
      refine le_trans hdir ?_
      exact mul_le_mul_left (le_add_right (le_add_right (le_add_left le_rfl))) A
    · rw [show uStep s D i l = fun z => (1 - cutF s z) * D i l z
          + dTLM s (fun y => cutFbar s y * D i l y) z from by
        funext z; rw [uStep_apply, if_neg hc]]
      have hTcont : ContDiffOn ℝ (k : ℕ∞) (dTLM s (fun y => cutFbar s y * D i l y)) trackSet := by
        have hc' : ContDiff ℝ k (fun y : Fin n → ℂ => cutFbar s y * D i l y) :=
          ((contDiff_cutFbar s).of_le (by exact_mod_cast le_top)).mul (hD i l)
        rw [dTLM_eq hc'.continuous]
        exact (contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho]) s k hc'
          (fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul])).contDiffOn
      have hg1 : ContDiffOn ℝ (k : ℕ∞) (fun z => (1 - cutF s z) * D i l z) trackSet :=
        (((contDiff_const.sub (contDiff_cutF s)).of_le (by exact_mod_cast le_top)).mul
          (hD i l)).contDiffOn
      refine le_trans (Work.CR.Flat.Holder.holderNorm_add_le (k := k) (α := α)
        (f := fun z => (1 - cutF s z) * D i l z)
        (g := dTLM s (fun y => cutFbar s y * D i l y)) (Ω := trackSet)
        hg1 hTcont isOpen_trackSet.uniqueDiffOn) ?_
      refine le_trans (add_le_add hdir hT) ?_
      rw [← add_mul]
      refine mul_le_mul_left ?_ A
      calc stepL (n := n) k α + ENNReal.ofReal CT * stepL (n := n) k α
          ≤ (1 + stepL (n := n) k α) + ENNReal.ofReal CT * stepL (n := n) k α :=
            add_le_add (le_add_left le_rfl) le_rfl
        _ ≤ (1 + stepL (n := n) k α + ENNReal.ofReal CT * stepL (n := n) k α) + 1 :=
            le_add_right le_rfl

/-! ## Iterating the recursion -/

lemma stage_bound {k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ≥0∞, 1 ≤ K ∧ K ≠ ⊤ ∧ ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiff ℝ k (η i l)) → ∀ (A : ℝ≥0∞), A ≠ ⊤ →
      (∀ i l, holderNorm k α (η i l) trackSet ≤ A) →
      ∀ (m : ℕ) (hm : m ≤ n) (i l : Fin n),
        holderNorm k α (uD η m i l) trackSet ≤ K ^ m * A := by
  obtain ⟨K, hK1, hKne, hstep⟩ := step_bound (n := n) hα0 hα1
  refine ⟨K, hK1, hKne, fun η hη A hA hAb m => ?_⟩
  induction m with
  | zero =>
      intro _ i l
      simpa using hAb i l
  | succ m ih =>
      intro hm i l
      have hm' : m < n := by omega
      have hKmA : K ^ m * A ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hKne) hA
      have hdh : ∀ i l, holderNorm k α (uD η m i l) trackSet ≤ K ^ m * A :=
        fun i l => ih (by omega) i l
      rw [uD_succ_of_lt η hm']
      calc holderNorm k α (uStep ⟨m, hm'⟩ (uD η m) i l) trackSet
          ≤ K * (K ^ m * A) :=
            hstep (uD η m) (fun i l => uD_contDiff_k hη m (by omega) i l) (K ^ m * A) hKmA
              hdh ⟨m, hm'⟩ i l
        _ = K ^ (m + 1) * A := by
            rw [pow_succ, ← mul_assoc, mul_comm K (K ^ m)]

/-! ## The summands of the solution operator -/

lemma psi_bound {k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiff ℝ k (η i l)) → ∀ (A : ℝ≥0∞), A ≠ ⊤ →
      (∀ i l, holderNorm k α (η i l) trackSet ≤ A) →
      ∀ (σ : Fin n) (l : Fin n), holderNorm k α (uPsi η σ l) trackSet ≤ K * A := by
  obtain ⟨KS, hKS1, hKSne, hKS⟩ := stage_bound (n := n) hα0 hα1
  obtain ⟨CT, _hCT0, hCT⟩ := dbarTransform_holderNorm_le (n := n) hα0 hα1 k
  refine ⟨ENNReal.ofReal CT * stepL (n := n) k α * KS ^ n + 1, ?_, ?_⟩
  · refine ENNReal.add_ne_top.mpr ⟨?_, by simp⟩
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (stepL_ne_top hα0 hα1)) (ENNReal.pow_ne_top hKSne)
  · intro η hη A hA hAb σ l
    have hσn : (σ : ℕ) ≤ n := le_of_lt σ.isLt
    have hstage := hKS η hη A hA hAb (σ : ℕ) hσn σ l
    have hc : ContDiff ℝ k (fun y : Fin n → ℂ => cutF σ y * uD η (σ : ℕ) σ l y) :=
      ((contDiff_cutF σ).of_le (by exact_mod_cast le_top)).mul
        (uD_contDiff_k hη (σ : ℕ) hσn σ l)
    have hBne : KS ^ (σ : ℕ) * A ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hKSne) hA
    have hleib : holderNorm k α (fun y : Fin n → ℂ => cutF σ y * uD η (σ : ℕ) σ l y) trackSet
        ≤ stepL (n := n) k α * (KS ^ (σ : ℕ) * A) :=
      holderNorm_cut_mul_le (n := n) (ζ := cutF σ) (f := uD η (σ : ℕ) σ l) hα0 hα1
        ((contDiff_cutF σ).of_le (by exact_mod_cast le_top)) (holderNorm_cutF_le_cutSup σ) hBne
        (uD_contDiff_k hη (σ : ℕ) hσn σ l) hstage
    have hmono : stepL (n := n) k α * (KS ^ (σ : ℕ) * A)
        ≤ stepL (n := n) k α * (KS ^ n * A) :=
      mul_le_mul_right (mul_le_mul_left (pow_le_pow_right₀ hKS1 hσn) A)
        (stepL (n := n) k α)
    calc holderNorm k α (uPsi η σ l) trackSet
        = holderNorm k α (dTLM σ (fun y => cutF σ y * uD η (σ : ℕ) σ l y)) trackSet := rfl
      _ = holderNorm k α (dbarTransform trRho σ
            (fun y => cutF σ y * uD η (σ : ℕ) σ l y)) trackSet := by rw [dTLM_eq hc.continuous]
      _ ≤ ENNReal.ofReal CT * holderNorm k α
            (fun y => cutF σ y * uD η (σ : ℕ) σ l y) trackSet :=
          hCT σ _ hc (fun y hy => by rw [cutF_eq_zero hy, zero_mul])
      _ ≤ ENNReal.ofReal CT * (stepL (n := n) k α * (KS ^ n * A)) :=
          mul_le_mul_right (le_trans hleib hmono) (ENNReal.ofReal CT)
      _ ≤ (ENNReal.ofReal CT * stepL (n := n) k α * KS ^ n + 1) * A := by
          rw [← mul_assoc, ← mul_assoc, add_mul, one_mul]
          exact le_add_right le_rfl

/-! ## The estimate for the solution operator -/

lemma uS2_bound {k : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiff ℝ k (η i l)) → ∀ (A : ℝ≥0∞), A ≠ ⊤ →
      (∀ i l, holderNorm k α (η i l) trackSet ≤ A) → ∀ j : Fin n,
        holderNorm k α (uS2 η j) solveSet ≤ K * A := by
  obtain ⟨Kp, hKpne, hKp⟩ := psi_bound (n := n) hα0 hα1
  refine ⟨(n : ℝ≥0∞) * Kp + Kp + 1,
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top n)
      hKpne, hKpne⟩, by simp⟩, ?_⟩
  intro η hη A hA hAb j
  have hsum : ∀ σ : Fin n, holderNorm k α (uPsi η σ j) trackSet ≤ Kp * A :=
    fun σ => hKp η hη A hA hAb σ j
  have hcont : ∀ σ ∈ (Finset.univ : Finset (Fin n)),
      ContDiffOn ℝ (k : ℕ∞) (uPsi η σ j) trackSet := fun σ _ => by
    have hc : ContDiff ℝ k (fun y : Fin n → ℂ => cutF σ y * uD η (σ : ℕ) σ j y) :=
      ((contDiff_cutF σ).of_le (by exact_mod_cast le_top)).mul
        (uD_contDiff_k hη (σ : ℕ) (le_of_lt σ.isLt) σ j)
    rw [show uPsi η σ j = dTLM σ (fun y => cutF σ y * uD η (σ : ℕ) σ j y) from rfl,
      dTLM_eq hc.continuous]
    exact (contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho]) σ k hc
      (fun y hy => by rw [cutF_eq_zero hy, zero_mul])).contDiffOn
  have hfun : uS2 η j = fun z => ∑ σ : Fin n, uPsi η σ j z := by
    funext z; simp only [uS2, Finset.sum_apply]
  calc holderNorm k α (uS2 η j) solveSet
      ≤ holderNorm k α (uS2 η j) trackSet :=
        holderNorm_mono_set isOpen_trackSet isOpen_solveSet solveSet_subset_trackSet k α _
    _ = holderNorm k α (fun z => ∑ σ : Fin n, uPsi η σ j z) trackSet := by rw [hfun]
    _ ≤ ∑ σ : Fin n, holderNorm k α (uPsi η σ j) trackSet :=
        Work.CR.Flat.Holder.holderNorm_sum_le (n := n) (ι := Fin n) Finset.univ hcont
          isOpen_trackSet.uniqueDiffOn
    _ ≤ ∑ _σ : Fin n, Kp * A := Finset.sum_le_sum fun σ _ => hsum σ
    _ = (n : ℝ≥0∞) * (Kp * A) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ((n : ℝ≥0∞) * Kp + Kp + 1) * A := by
        rw [← mul_assoc]
        exact mul_le_mul_left (le_add_right (le_add_right le_rfl)) A

theorem uS2_holderNorm_uniform {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
        (∀ i l : Fin n, ContDiff ℝ k (η i l)) → ∀ j : Fin n,
          Work.CR.Flat.holderNorm k α (Work.NN.Final.uS2 η j) Work.CR.Flat.Cauchy.solveSet
            ≤ ENNReal.ofReal (C k) *
              ∑ i : Fin n, ∑ l : Fin n,
                Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 (fun _ => 1)) := by
  have hb : ∀ k : ℕ, ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiff ℝ k (η i l)) → ∀ (A : ℝ≥0∞), A ≠ ⊤ →
      (∀ i l, holderNorm k α (η i l) trackSet ≤ A) → ∀ j : Fin n,
        holderNorm k α (uS2 η j) solveSet ≤ K * A := fun k => uS2_bound (n := n) hα0 hα1
  refine ⟨fun k => (Classical.choose (hb k)).toReal + 1, ?_, ?_⟩
  · intro k
    have h1 : (0 : ℝ) ≤ (Classical.choose (hb k)).toReal := ENNReal.toReal_nonneg
    linarith
  · intro k η hη j
    obtain ⟨hKne, hKb⟩ := Classical.choose_spec (hb k)
    have hCeq : ENNReal.ofReal ((Classical.choose (hb k)).toReal + 1)
        = Classical.choose (hb k) + 1 := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal hKne]
      norm_num
    rw [hCeq]
    by_cases htop : (∑ i : Fin n, ∑ l : Fin n,
        holderNorm k α (η i l) (polydisc 0 (fun _ => 1))) = ⊤
    · rw [htop, ENNReal.mul_top (by simp)]
      exact le_top
    · have hAB : (∑ i : Fin n, ∑ l : Fin n, holderNorm k α (η i l) trackSet)
          ≤ (∑ i : Fin n, ∑ l : Fin n,
              holderNorm k α (η i l) (polydisc 0 (fun _ => 1))) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => ?_
        exact Work.CR.Flat.holderNorm_mono_set (isOpen_polydisc 0 (fun _ => 1)) isOpen_trackSet
          trackSet_subset_unit k α (η i l)
      have hAne : (∑ i : Fin n, ∑ l : Fin n, holderNorm k α (η i l) trackSet) ≠ ⊤ :=
        ne_top_of_le_ne_top htop hAB
      have hAb : ∀ i l, holderNorm k α (η i l) trackSet
          ≤ ∑ i : Fin n, ∑ l : Fin n, holderNorm k α (η i l) trackSet := by
        intro i l
        refine le_trans (Finset.single_le_sum
          (f := fun l' : Fin n => holderNorm k α (η i l') trackSet) (fun _ _ => zero_le)
          (Finset.mem_univ l)) ?_
        exact Finset.single_le_sum
          (f := fun i' : Fin n => ∑ l' : Fin n, holderNorm k α (η i' l') trackSet)
          (fun _ _ => zero_le) (Finset.mem_univ i)
      have hmain := hKb η hη (∑ i : Fin n, ∑ l : Fin n, holderNorm k α (η i l) trackSet)
        hAne hAb j
      refine le_trans hmain ?_
      refine le_trans (mul_le_mul_left (show Classical.choose (hb k) ≤ Classical.choose (hb k) + 1
        from le_add_right le_rfl)
        (∑ i : Fin n, ∑ l : Fin n, holderNorm k α (η i l) trackSet)) ?_
      exact mul_le_mul_right hAB (Classical.choose (hb k) + 1)

end Work.NN.Final
