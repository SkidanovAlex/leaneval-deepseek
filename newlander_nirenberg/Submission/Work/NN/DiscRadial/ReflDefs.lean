import Mathlib
import Submission.Work.NN.DiscRadial.Unfold
import Submission.Work.NN.DiscRadial.Setup
import Submission.Work.NN.DiscRadial.Comp
import Submission.Work.NN.DiscRadial.holderDerivTendsto_of_isOpen
import Submission.Work.CR.Flat.Holder

noncomputable section

namespace Work.NN.DiscRadial

open scoped Topology ContDiff NNReal ENNReal BigOperators
open Metric Set Filter
open Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The linear "reflection" `(y, σ) ↦ (y, -b σ)` of the unfolding, where `b = discScale i`. -/
def reflCLM (i : ℕ) : (X × ℂ) × ℝ →L[ℝ] (X × ℂ) × ℝ :=
  Work.NN.Final.eta (X := X × ℂ) (-(discScale i))

@[simp] lemma reflCLM_apply (i : ℕ) (q : (X × ℂ) × ℝ) :
    reflCLM (X := X) i q = (q.1, -(discScale i) * q.2) := rfl

/-- The reflected sum of the unfolding, without the cutoffs: on the region where the cutoffs are
`1` this is the unfolded extension `discUnfoldExt k g`. -/
def discUnfoldSum (k : ℕ) (g : X × ℂ → ℂ) : (X × ℂ) × ℝ → ℂ := fun q =>
  ∑ i ∈ Finset.range (k + 1), (discWt k i) • (discUnfold g) (reflCLM (X := X) i q)

@[simp] lemma discUnfoldSum_apply (k : ℕ) (g : X × ℂ → ℂ) (q : (X × ℂ) × ℝ) :
    discUnfoldSum (X := X) k g q =
      ∑ i ∈ Finset.range (k + 1), (discWt k i) • (discUnfold g) (reflCLM (X := X) i q) := rfl

/-! ## The chain rule for a function which is smooth only on an open set -/

/-- Composition with a continuous linear map on the right, for a function which is `C^n` only on an
open set. -/
lemma iteratedFDeriv_comp_clm_of_contDiffOn {G E : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℂ} {n : ℕ}
    (hf : ContDiffOn ℝ (n : WithTop ENat) f Ω) (L : G →L[ℝ] E) {x : G} (hx : L x ∈ Ω)
    {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv ℝ i (f ∘ ⇑L) x =
      (iteratedFDeriv ℝ i f (L x)).compContinuousLinearMap (fun _ => L) := by
  have hpre : IsOpen (L ⁻¹' Ω) := hΩ.preimage L.continuous
  have h1 : iteratedFDerivWithin ℝ i (f ∘ ⇑L) (L ⁻¹' Ω) x = iteratedFDeriv ℝ i (f ∘ ⇑L) x :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := L ⁻¹' Ω) (f := f ∘ ⇑L) i hpre hx
  have h2 : iteratedFDerivWithin ℝ i f Ω (L x) = iteratedFDeriv ℝ i f (L x) :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := f) i hΩ hx
  have h3 := L.iteratedFDerivWithin_comp_right (𝕜 := ℝ) (f := f) (s := Ω)
      (n := (n : WithTop ENat)) hf hΩ.uniqueDiffOn hpre.uniqueDiffOn (x := x) hx
      (by exact_mod_cast hi)
  rw [← h1, h3, h2]

/-! ## The moment identity for the reflections -/

/-- The multilinear moment identity: the weighted sum of the pull-backs of an `m`-multilinear form
along the reflections `eta (-(discScale i))` is the form itself. -/
theorem etaMoment {k m : ℕ} (hm : m ≤ k)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin m => (X × ℂ) × ℝ) ℂ) :
    ∑ i ∈ Finset.range (k + 1), (discWt k i) •
        Φ.compContinuousLinearMap
          (fun _ : Fin m => Work.NN.Final.eta (X := X × ℂ) (-(discScale i))) = Φ := by
  set lam : Fin (k + 1) → ℝ := fun i => discWt k (i : ℕ) with hlam
  set eps : Fin (k + 1) → ℝ := fun i => discScale (i : ℕ) with heps
  have ha : ∀ j ≤ m, ∑ i, lam i * (-(eps i)) ^ j = 1 := by
    intro j hj
    rw [hlam, heps, Fin.sum_univ_eq_sum_range
      (fun i => discWt k i * (-(discScale i)) ^ j) (k + 1)]
    exact discWt_moment k (le_trans hj hm)
  have h := finite_moment_tensor_clm (X := X × ℂ) (k := m) eps lam ha Φ
  simp only [hlam, heps] at h
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    discWt k i • Φ.compContinuousLinearMap
      (fun _ : Fin m => Work.NN.Final.eta (X := X × ℂ) (-(discScale i)))) (k + 1)] at h
  exact h

/-! ## The iterated derivatives of the reflected sum -/

/-- On the region where the reflected points lie in the open set `Ω`, the iterated derivatives of
the reflected sum are the weighted sums of the iterated derivatives of `discUnfold g` at the
reflected points, pulled back along the reflections. -/
lemma iteratedFDeriv_discUnfoldSum_eq {k m : ℕ} (hm : m ≤ k) {g : X × ℂ → ℂ}
    {Ω : Set ((X × ℂ) × ℝ)} (hΩ : IsOpen Ω)
    (hcd : ContDiffOn ℝ (k : WithTop ENat) (discUnfold g) Ω)
    {q : (X × ℂ) × ℝ} (hq : ∀ i ∈ Finset.range (k + 1), reflCLM (X := X) i q ∈ Ω) :
    iteratedFDeriv ℝ m (discUnfoldSum (X := X) k g) q =
      ∑ i ∈ Finset.range (k + 1), (discWt k i) •
        (iteratedFDeriv ℝ m (discUnfold g) (reflCLM (X := X) i q)).compContinuousLinearMap
          (fun _ => reflCLM (X := X) i) := by
  have hcdat : ∀ i ∈ Finset.range (k + 1),
      ContDiffAt ℝ (m : WithTop ENat) (discUnfold g) (reflCLM (X := X) i q) := by
    intro i hi
    exact (hcd.contDiffAt (hΩ.mem_nhds (hq i hi))).of_le (by exact_mod_cast hm)
  have hfun : discUnfoldSum (X := X) k g =
      fun q => ∑ i ∈ Finset.range (k + 1),
        ((discWt k i) • (fun z => discUnfold g (reflCLM (X := X) i z))) q := by
    funext q
    simp only [discUnfoldSum_apply, Pi.smul_apply]
  rw [hfun, iteratedFDeriv_fun_sum_apply]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hcomp : ContDiffAt ℝ (m : WithTop ENat)
        (fun z => discUnfold g (reflCLM (X := X) i z)) q :=
      (hcdat i hi).comp q ((reflCLM (X := X) i).contDiff.contDiffAt)
    rw [iteratedFDeriv_const_smul_apply hcomp]
    congr 1
    exact iteratedFDeriv_comp_clm_of_contDiffOn hΩ hcd (reflCLM (X := X) i) (hq i hi) hm
  · intro j hj
    exact ((hcdat j hj).comp q ((reflCLM (X := X) j).contDiff.contDiffAt)).const_smul (discWt k j)


/-! ## The moment identity in the form used below -/

/-- The moment identity for the reflections `reflCLM`. -/
theorem reflMoment {k m : ℕ} (hm : m ≤ k)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin m => (X × ℂ) × ℝ) ℂ) :
    ∑ i ∈ Finset.range (k + 1), (discWt k i) •
        Φ.compContinuousLinearMap (fun _ : Fin m => reflCLM (X := X) i) = Φ := by
  simpa only [reflCLM] using etaMoment (X := X) hm Φ

/-! ## The smallness estimates -/

/-- If `|σ| < min 1 ε / (2 * (k+2))` then `discScale i * |σ| < min 1 ε` for every `i ≤ k`. -/
lemma discScale_mul_abs_lt_min {k : ℕ} {ε : ℝ} (hε : 0 < ε) {σ : ℝ}
    (hσ : |σ| < min 1 ε / (2 * ((k : ℝ) + 2))) {i : ℕ} (hi : i ∈ Finset.range (k + 1)) :
    discScale i * |σ| < min 1 ε := by
  have hkpos : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hsc : discScale i ≤ (k : ℝ) + 2 := by
    rw [discScale]
    exact_mod_cast Nat.add_le_add_right (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) 2
  have h1 : discScale i * |σ| ≤ ((k : ℝ) + 2) * |σ| :=
    mul_le_mul_of_nonneg_right hsc (abs_nonneg σ)
  have h2 : ((k : ℝ) + 2) * |σ| < ((k : ℝ) + 2) * (min 1 ε / (2 * ((k : ℝ) + 2))) :=
    mul_lt_mul_of_pos_left hσ hkpos
  have h3 : ((k : ℝ) + 2) * (min 1 ε / (2 * ((k : ℝ) + 2))) = min 1 ε / 2 := by
    rw [← mul_div_assoc, mul_comm ((k : ℝ) + 2) (min 1 ε),
      mul_div_mul_right _ _ (ne_of_gt hkpos)]
  have h4 : min 1 ε / 2 < min 1 ε := by
    have hminpos : (0 : ℝ) < min 1 ε := lt_min (by norm_num) hε
    linarith
  linarith

/-- If `|σ| < min 1 ε / (2 * (k+2))` then all the cutoff arguments `discScale i * σ` have
modulus `< 1` for `i ≤ k`. -/
lemma abs_discScale_mul_lt_one {k : ℕ} {ε : ℝ} (hε : 0 < ε) {σ : ℝ}
    (hσ : |σ| < min 1 ε / (2 * ((k : ℝ) + 2))) {i : ℕ} (hi : i ∈ Finset.range (k + 1)) :
    |discScale i * σ| < 1 := by
  rw [abs_mul, abs_of_pos (discScale_pos i)]
  exact lt_of_lt_of_le (discScale_mul_abs_lt_min hε hσ hi) (min_le_left (1 : ℝ) ε)

/-- If `|q.2| < min 1 ε / (2 * (k+2))`, `q.1 ∈ W` and `q.2 < 0`, then all the reflected points
`reflCLM i q` (`i ≤ k`) lie in `W × (0,ε)`. -/
lemma reflCLM_mem_of_abs_snd_lt {k : ℕ} {W : Set (X × ℂ)} {ε : ℝ} (hε : 0 < ε)
    {q : (X × ℂ) × ℝ} (hσ : |q.2| < min 1 ε / (2 * ((k : ℝ) + 2)))
    (hq1 : q.1 ∈ W) (hq2 : q.2 < 0) :
    ∀ i ∈ Finset.range (k + 1), reflCLM (X := X) i q ∈ W ×ˢ Set.Ioo 0 ε := by
  intro i hi
  have hkey := discScale_mul_abs_lt_min hε hσ hi
  have hmul : -(discScale i) * q.2 = discScale i * |q.2| := by
    rw [abs_of_neg hq2]; ring
  simp only [reflCLM_apply, Set.mem_prod, Set.mem_Ioo]
  refine ⟨hq1, ?_, ?_⟩
  · rw [hmul]
    exact mul_pos (discScale_pos i) (abs_pos.mpr (ne_of_lt hq2))
  · rw [hmul]
    exact lt_of_lt_of_le hkey (min_le_right (1 : ℝ) ε)

end Work.NN.DiscRadial
