import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolRec
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Final.uS2_holderNorm_uniform

/-!
# The `C^{k,α}` bound for the explicit solution operator `recU` (one-form telescope)

`Work.CR.Flat.Cauchy.recU` is the explicit coordinate-by-coordinate solution operator of the
`∂̄`-equation `∂̄ u = f` on the unit polydisc, built from the cutoff `cutF` and the one-variable
Cauchy-type transform `dbarTransform` (see `Submission/Work/CR/Flat/Cauchy/openSolRec.lean`).

The earlier estimate `Work.CR.Flat.Cauchy.recU_estimate_uniform` controls `recU f` only in
`C^{0,α}`.  This file proves the *no-loss* estimate at every order `k`: there is a constant
`C k > 0`, depending only on `n`, `α`, `k` and the fixed absolute constants of the cutoff
`openCut`, such that for every datum `g` of class `C^k`

  `‖recU g‖_{C^{k,α}(solveSet)} ≤ C k · ∑_j ‖g j‖_{C^{k,α}(P(0,1))}`.

## Route

The recursion `recF g (m+1) = stepData ⟨m⟩ (recF g m)` with
`stepData s F i = dbarTransform trRho s (cutFbar s · F i)` is derivative free, and each of its
ingredients is bounded on the `C^{k,α}` scale on the tracked polydisc `trackSet`:

* multiplication by the fixed cutoff `cutFbar s` (resp. `cutF s`) is bounded
  (`Work.NN.Final.holderNorm_cut_mul_le`, with the finiteness of the `C^{k,α}`-norms of the
  cutoffs on the bounded set `trackSet`, `Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded`);
* one step of the Cauchy transform is bounded with no loss of derivatives
  (`Work.NN.Final.dbarTransform_holderNorm_le`).

Iterating the one-step bound over the `n` stages of the recursion (`stage_bound`), bounding one
summand of `recU` (`psi_bound`) and summing the `n` summands gives `recU_bound`, in which the
data are measured on `trackSet ⊆ P(0,1)`; monotonicity of the `C^{k,α}`-norm in the domain and
the conversion of the `ℝ≥0∞`-valued constant into a real one finish the proof.
-/

set_option maxHeartbeats 1200000

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory
open Work.CR.Flat Work.CR.Flat.Cauchy

namespace Work.NN.Core

/-! ## Preservation of finite smoothness by the recursion -/

/-- One step of the recursion preserves `C^k`. -/
lemma stepData_contDiff_k {n : ℕ} {k : ℕ} {s : Fin n} {F : Fin n → (Fin n → ℂ) → ℂ}
    (hF : ∀ i, ContDiff ℝ k (F i)) (i : Fin n) :
    ContDiff ℝ k (Work.CR.Flat.Cauchy.stepData s F i) := by
  unfold Work.CR.Flat.Cauchy.stepData
  exact Work.CR.Flat.Cauchy.contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho])
    s k (((contDiff_cutFbar s).of_le (by exact_mod_cast le_top)).mul (hF i))
    (fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul])

/-- The data at every stage of the recursion are `C^k` when the original data are. -/
lemma recF_contDiff_k {n : ℕ} {k : ℕ} {g : Fin n → (Fin n → ℂ) → ℂ}
    (hg : ∀ j, ContDiff ℝ k (g j)) :
    ∀ m, m ≤ n → ∀ i, ContDiff ℝ k (Work.CR.Flat.Cauchy.recF g m i) := by
  intro m
  induction m with
  | zero => intro _ i; simpa using hg i
  | succ m ih =>
      intro _ i
      have hm' : m < n := by omega
      rw [Work.CR.Flat.Cauchy.recF_succ_of_lt g hm']
      exact stepData_contDiff_k (fun i => ih (by omega) i) i

/-! ## One step of the recursion is bounded on the `C^{k,α}` scale -/

lemma step_bound {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {k : ℕ} :
    ∃ K : ℝ≥0∞, 1 ≤ K ∧ K ≠ ⊤ ∧ ∀ (F : Fin n → (Fin n → ℂ) → ℂ),
      (∀ i, ContDiff ℝ k (F i)) → ∀ A, A ≠ ⊤ →
      (∀ i, holderNorm k α (F i) trackSet ≤ A) → ∀ (s i : Fin n),
        holderNorm k α (Work.CR.Flat.Cauchy.stepData s F i) trackSet ≤ K * A := by
  obtain ⟨CT, _hCT0, hCT⟩ := Work.NN.Final.dbarTransform_holderNorm_le (n := n) hα0 hα1 k
  refine ⟨ENNReal.ofReal CT * Work.NN.Final.stepL (n := n) k α + 1, ?_, ?_, ?_⟩
  · exact le_add_self
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (Work.NN.Final.stepL_ne_top (n := n) hα0 hα1), by simp⟩
  · intro F hF A hA hAb s i
    have hc : ContDiff ℝ k (fun y : Fin n → ℂ => cutFbar s y * F i y) :=
      ((contDiff_cutFbar s).of_le (by exact_mod_cast le_top)).mul (hF i)
    have hsupp : ∀ y : Fin n → ℂ, cutOut ≤ ‖y s‖ → cutFbar s y * F i y = 0 :=
      fun y hy => by rw [cutFbar_eq_zero_of_ge hy, zero_mul]
    have hleib : holderNorm k α (fun y : Fin n → ℂ => cutFbar s y * F i y) trackSet
        ≤ Work.NN.Final.stepL (n := n) k α * A :=
      Work.NN.Final.holderNorm_cut_mul_le (n := n) (ζ := cutFbar s) (f := F i) hα0 hα1
        ((contDiff_cutFbar s).of_le (by exact_mod_cast le_top))
        (Work.NN.Final.holderNorm_cutFbar_le_cutSup s) hA (hF i) (hAb i)
    calc holderNorm k α (Work.CR.Flat.Cauchy.stepData s F i) trackSet
        = holderNorm k α (dbarTransform trRho s (fun y => cutFbar s y * F i y)) trackSet := rfl
      _ ≤ ENNReal.ofReal CT * holderNorm k α (fun y => cutFbar s y * F i y) trackSet :=
          hCT s _ hc hsupp
      _ ≤ ENNReal.ofReal CT * (Work.NN.Final.stepL (n := n) k α * A) :=
          mul_le_mul_right hleib (ENNReal.ofReal CT)
      _ = (ENNReal.ofReal CT * Work.NN.Final.stepL (n := n) k α) * A := by rw [mul_assoc]
      _ ≤ (ENNReal.ofReal CT * Work.NN.Final.stepL (n := n) k α + 1) * A := by
          rw [add_mul, one_mul]; exact le_self_add

/-! ## Iterating the recursion -/

lemma stage_bound {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {k : ℕ} :
    ∃ K : ℝ≥0∞, 1 ≤ K ∧ K ≠ ⊤ ∧ ∀ (g : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ k (g j)) → ∀ A, A ≠ ⊤ →
      (∀ j, holderNorm k α (g j) trackSet ≤ A) → ∀ (m : ℕ) (_ : m ≤ n) (i : Fin n),
        holderNorm k α (Work.CR.Flat.Cauchy.recF g m i) trackSet ≤ K ^ m * A := by
  obtain ⟨K, hK1, hKne, hstep⟩ := step_bound (n := n) hα0 hα1 (k := k)
  refine ⟨K, hK1, hKne, fun g hg A hA hAb m => ?_⟩
  induction m with
  | zero => intro _ i; simpa using hAb i
  | succ m ih =>
      intro _ i
      have hm' : m < n := by omega
      have hKmA : K ^ m * A ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hKne) hA
      have hdh : ∀ i, holderNorm k α (Work.CR.Flat.Cauchy.recF g m i) trackSet ≤ K ^ m * A :=
        fun i => ih (by omega) i
      have hcontm : ∀ i, ContDiff ℝ k (Work.CR.Flat.Cauchy.recF g m i) :=
        fun i => recF_contDiff_k hg m (by omega) i
      rw [Work.CR.Flat.Cauchy.recF_succ_of_lt g hm']
      calc holderNorm k α
            (Work.CR.Flat.Cauchy.stepData ⟨m, hm'⟩ (Work.CR.Flat.Cauchy.recF g m) i) trackSet
          ≤ K * (K ^ m * A) :=
            hstep (Work.CR.Flat.Cauchy.recF g m) hcontm (K ^ m * A) hKmA hdh ⟨m, hm'⟩ i
        _ = K ^ (m + 1) * A := by rw [pow_succ, ← mul_assoc, mul_comm K (K ^ m)]

/-! ## One summand of `recU` -/

lemma psi_bound {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {k : ℕ} :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (g : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ k (g j)) → ∀ A, A ≠ ⊤ →
      (∀ j, holderNorm k α (g j) trackSet ≤ A) → ∀ j : Fin n,
        holderNorm k α (dbarTransform trRho j
            (fun y => cutF j y * Work.CR.Flat.Cauchy.recF g (j : ℕ) j y)) trackSet
          ≤ K * A := by
  obtain ⟨KS, hKS1, hKSne, hKS⟩ := stage_bound (n := n) hα0 hα1 (k := k)
  obtain ⟨CT, _hCT0, hCT⟩ := Work.NN.Final.dbarTransform_holderNorm_le (n := n) hα0 hα1 k
  refine ⟨ENNReal.ofReal CT * Work.NN.Final.stepL (n := n) k α * KS ^ n + 1, ?_, ?_⟩
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (Work.NN.Final.stepL_ne_top (n := n) hα0 hα1)) (ENNReal.pow_ne_top hKSne), by simp⟩
  · intro g hg A hA hAb j
    have hjn : (j : ℕ) ≤ n := le_of_lt j.isLt
    have hstage := hKS g hg A hA hAb (j : ℕ) hjn j
    have hc : ContDiff ℝ k
        (fun y : Fin n → ℂ => cutF j y * Work.CR.Flat.Cauchy.recF g (j : ℕ) j y) :=
      ((contDiff_cutF j).of_le (by exact_mod_cast le_top)).mul
        (recF_contDiff_k hg (j : ℕ) hjn j)
    have hBne : KS ^ (j : ℕ) * A ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hKSne) hA
    have hleib : holderNorm k α
          (fun y : Fin n → ℂ => cutF j y * Work.CR.Flat.Cauchy.recF g (j : ℕ) j y) trackSet
        ≤ Work.NN.Final.stepL (n := n) k α * (KS ^ (j : ℕ) * A) :=
      Work.NN.Final.holderNorm_cut_mul_le (n := n) (ζ := cutF j)
        (f := Work.CR.Flat.Cauchy.recF g (j : ℕ) j) hα0 hα1
        ((contDiff_cutF j).of_le (by exact_mod_cast le_top)) (Work.NN.Final.holderNorm_cutF_le_cutSup j)
        hBne (recF_contDiff_k hg (j : ℕ) hjn j) hstage
    have hmono : Work.NN.Final.stepL (n := n) k α * (KS ^ (j : ℕ) * A)
        ≤ Work.NN.Final.stepL (n := n) k α * (KS ^ n * A) :=
      mul_le_mul_right (mul_le_mul_left (pow_le_pow_right₀ hKS1 hjn) A)
        (Work.NN.Final.stepL (n := n) k α)
    have hsupp : ∀ y : Fin n → ℂ, cutOut ≤ ‖y j‖ →
        cutF j y * Work.CR.Flat.Cauchy.recF g (j : ℕ) j y = 0 :=
      fun y hy => by rw [cutF_eq_zero hy, zero_mul]
    calc holderNorm k α (dbarTransform trRho j
            (fun y => cutF j y * Work.CR.Flat.Cauchy.recF g (j : ℕ) j y)) trackSet
        ≤ ENNReal.ofReal CT * holderNorm k α
            (fun y => cutF j y * Work.CR.Flat.Cauchy.recF g (j : ℕ) j y) trackSet :=
          hCT j _ hc hsupp
      _ ≤ ENNReal.ofReal CT * (Work.NN.Final.stepL (n := n) k α * (KS ^ n * A)) :=
          mul_le_mul_right (le_trans hleib hmono) _
      _ ≤ (ENNReal.ofReal CT * Work.NN.Final.stepL (n := n) k α * KS ^ n + 1) * A := by
          rw [← mul_assoc, ← mul_assoc, add_mul, one_mul]
          exact le_self_add

/-! ## The bound for the whole solution operator -/

lemma recU_bound {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {k : ℕ} :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (g : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ k (g j)) → ∀ A, A ≠ ⊤ →
      (∀ j, holderNorm k α (g j) trackSet ≤ A) →
      holderNorm k α (fun z => Work.CR.Flat.Cauchy.recU g z) solveSet ≤ K * A := by
  obtain ⟨Kp, hKpne, hKp⟩ := psi_bound (n := n) hα0 hα1 (k := k)
  refine ⟨(n : ℝ≥0∞) * Kp + 1, ?_, ?_⟩
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hKpne, by simp⟩
  · intro g hg A hA hAb
    have hsum : ∀ j : Fin n,
        holderNorm k α (dbarTransform trRho j
            (fun y => cutF j y * Work.CR.Flat.Cauchy.recF g (j : ℕ) j y)) trackSet
          ≤ Kp * A := fun j => hKp g hg A hA hAb j
    have hcont : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        ContDiffOn ℝ (k : ℕ∞ω) (dbarTransform trRho j
          (fun y => cutF j y * Work.CR.Flat.Cauchy.recF g (j : ℕ) j y)) trackSet := by
      intro j _
      have hc : ContDiff ℝ k
          (fun y : Fin n → ℂ => cutF j y * Work.CR.Flat.Cauchy.recF g (j : ℕ) j y) :=
        ((contDiff_cutF j).of_le (by exact_mod_cast le_top)).mul
          (recF_contDiff_k hg (j : ℕ) (le_of_lt j.isLt) j)
      exact (contDiff_dbarTransform (b := cutOut) (by norm_num [cutOut, trRho]) j k hc
        (fun y hy => by rw [cutF_eq_zero hy, zero_mul])).contDiffOn
    have hfun : (fun z => Work.CR.Flat.Cauchy.recU g z) = fun z => ∑ j : Fin n,
        dbarTransform trRho j (fun y => cutF j y * Work.CR.Flat.Cauchy.recF g (j : ℕ) j y) z := by
      funext z; simp only [Work.CR.Flat.Cauchy.recU]
    calc holderNorm k α (fun z => Work.CR.Flat.Cauchy.recU g z) solveSet
        ≤ holderNorm k α (fun z => Work.CR.Flat.Cauchy.recU g z) trackSet :=
          holderNorm_mono_set Work.NN.Final.isOpen_trackSet Work.NN.Final.isOpen_solveSet
            Work.NN.Final.solveSet_subset_trackSet k α _
      _ = holderNorm k α (fun z => ∑ j : Fin n,
            dbarTransform trRho j (fun y => cutF j y * Work.CR.Flat.Cauchy.recF g (j : ℕ) j y) z)
              trackSet := by
          rw [hfun]
      _ ≤ ∑ j : Fin n, holderNorm k α
            (dbarTransform trRho j
              (fun y => cutF j y * Work.CR.Flat.Cauchy.recF g (j : ℕ) j y)) trackSet :=
          Work.CR.Flat.Holder.holderNorm_sum_le (n := n) Finset.univ hcont
            Work.NN.Final.isOpen_trackSet.uniqueDiffOn
      _ ≤ ∑ _j : Fin n, Kp * A := Finset.sum_le_sum fun j _ => hsum j
      _ = (n : ℝ≥0∞) * (Kp * A) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ((n : ℝ≥0∞) * Kp + 1) * A := by
          rw [← mul_assoc, add_mul, one_mul]; exact le_self_add

/-! ## The target theorem -/

theorem recUHolderNormLevel {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (g : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ k (g j)) →
      Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.Cauchy.recU g z)
        Work.CR.Flat.Cauchy.solveSet
        ≤ ENNReal.ofReal (C k) *
          ∑ j, Work.CR.Flat.holderNorm k α (g j) (Work.CR.Flat.polydisc 0 (fun _ => 1)) := by
  have hb : ∀ k : ℕ, ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (g : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ k (g j)) → ∀ A, A ≠ ⊤ →
      (∀ j, holderNorm k α (g j) trackSet ≤ A) →
      holderNorm k α (fun z => Work.CR.Flat.Cauchy.recU g z) solveSet ≤ K * A :=
    fun k => recU_bound (n := n) hα0 hα1 (k := k)
  refine ⟨fun k => (Classical.choose (hb k)).toReal + 1, ?_, ?_⟩
  · intro k
    have h1 : (0 : ℝ) ≤ (Classical.choose (hb k)).toReal := ENNReal.toReal_nonneg
    linarith
  · intro k g hg
    obtain ⟨hKne, hKb⟩ := Classical.choose_spec (hb k)
    have hCeq : ENNReal.ofReal ((Classical.choose (hb k)).toReal + 1)
        = Classical.choose (hb k) + 1 := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal hKne]
      norm_num
    rw [hCeq]
    by_cases htop : (∑ j : Fin n, holderNorm k α (g j) (polydisc 0 (fun _ => 1))) = ⊤
    · have hK1 : (1 : ℝ≥0∞) ≤ Classical.choose (hb k) + 1 := le_add_self
      rw [htop, ENNReal.mul_top (ne_of_gt (lt_of_lt_of_le zero_lt_one hK1))]
      exact le_top
    · have hAB : (∑ j : Fin n, holderNorm k α (g j) trackSet)
          ≤ (∑ j : Fin n, holderNorm k α (g j) (polydisc 0 (fun _ => 1))) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact holderNorm_mono_set (isOpen_polydisc 0 (fun _ => 1)) Work.NN.Final.isOpen_trackSet
          Work.NN.Final.trackSet_subset_unit k α (g j)
      have hAne : (∑ j : Fin n, holderNorm k α (g j) trackSet) ≠ ⊤ :=
        ne_top_of_le_ne_top htop hAB
      have hAb : ∀ j, holderNorm k α (g j) trackSet
          ≤ ∑ j : Fin n, holderNorm k α (g j) trackSet := fun j =>
        Finset.single_le_sum (f := fun j => holderNorm k α (g j) trackSet)
          (fun _ _ => zero_le) (Finset.mem_univ j)
      have hmain := hKb g hg (∑ j : Fin n, holderNorm k α (g j) trackSet) hAne hAb
      refine le_trans hmain ?_
      refine le_trans (mul_le_mul_left (show Classical.choose (hb k) ≤ Classical.choose (hb k) + 1
        from le_self_add) (∑ j : Fin n, holderNorm k α (g j) trackSet)) ?_
      exact mul_le_mul_right hAB (Classical.choose (hb k) + 1)

end Work.NN.Core
