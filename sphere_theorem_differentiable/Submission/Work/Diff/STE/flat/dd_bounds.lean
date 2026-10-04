import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs
import Submission.Work.Diff.STE.flat.limit_aux
import Submission.Work.Diff.STE.flat.CSq_comp_xperiodic_le
import Submission.Work.Diff.STE.flat.towerExp_contDiff
import Submission.Work.Diff.STE.flat.towerExp_congr
import Submission.Work.Diff.STE.flat.towerExp_periodic
import Submission.Work.Diff.STE.flat.CSq_le_of_decay
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound
import Submission.Work.Diff.STE.flat.periodic_shift
import Submission.Work.Diff.STE.flat.jet_comp_l2
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.pd_seriesFun
import Submission.Work.Diff.STE.fourierCoeff_iterate_pd
import Submission.Work.Diff.STE.flat.jetP_iteratedFDeriv_bound
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Rapid decay of the coefficient families of the time-derivative tower

`Work.Diff.STE.flat.dd_bounds`: the rapid (faster than any polynomial) decay of the coefficient
family `cinf` of the limit solution is inherited by *every* level `dd Φ cinf j` of the formal
time-derivative tower of the DeTurck nonlinearity `Φ`, uniformly in `t ∈ [0, T)`.

The proof is a strong induction on the level `j`.  At level `j + 1` the family is the Fourier
coefficient family of the composed function `x ↦ towerExp Φ (j + 1) (x, Js x)`, where `Js` is the
tuple of spatial `2`-jets of the levels `0, …, j`; its coefficients are controlled by sup bounds on
the derivatives of that composition.  Those come from

* uniform sup bounds on the partial derivatives of the jets of the lower levels (from the decay
  hypothesis, via `sup_pdList_le` and `CSq_le_of_decay`),
* the Faà di Bruno/Leibniz count `comp_sup_bound` for the composition with the jet map,
* compactness of the (periodic) tower expression on the bounded set of possible jets, and
* the Fourier-coefficient decay estimate `fourierCoeff_weight_le`.

The nonlinearity `Φ` is used only through the globally smooth and periodic `Φ'`, which agrees with
it on the open set `V'` (`towerExp_congr`); this is what makes the tower expression smooth.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE
open Work.Diff.STE.Flat
open MeasureTheory
open scoped BigOperators ContDiff

noncomputable section

set_option maxHeartbeats 4000000

variable {n : ℕ}







/-! ## 1. Summability from rapid decay -/

lemma summable_wt_mul_norm_of_decay {γ : (Fin n → ℤ) → ℂ} {Cdec : ℝ} (N Mdec : ℕ)
    (hNM : N + n + 1 ≤ Mdec) (h : ∀ k : Fin n → ℤ, ‖γ k‖ * (Work.Diff.STE.wt k) ^ Mdec ≤ Cdec) :
    Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖γ k‖) := by
  have hcard : n < 2 * (Mdec - N) := by omega
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le N) (norm_nonneg _)) (fun k => ?_)
    ((Work.Diff.STE.flat.summable_wt_inv' (n := n) (s := Mdec - N) hcard).mul_left Cdec)
  have hw : 0 < (Work.Diff.STE.wt k) ^ Mdec := pow_pos (Work.Diff.STE.wt_pos k) Mdec
  have hle : ‖γ k‖ ≤ Cdec * ((Work.Diff.STE.wt k) ^ Mdec)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hw]
    exact h k
  have hsplit : (Work.Diff.STE.wt k) ^ Mdec
      = (Work.Diff.STE.wt k) ^ (Mdec - N) * (Work.Diff.STE.wt k) ^ N := by
    rw [← pow_add]; congr 1; omega
  have hxn : (Work.Diff.STE.wt k) ^ N ≠ 0 := pow_ne_zero _ (ne_of_gt (Work.Diff.STE.wt_pos k))
  calc (Work.Diff.STE.wt k) ^ N * ‖γ k‖
      ≤ (Work.Diff.STE.wt k) ^ N * (Cdec * ((Work.Diff.STE.wt k) ^ Mdec)⁻¹) :=
        mul_le_mul_of_nonneg_left hle (pow_nonneg (Work.Diff.STE.wt_pos k).le N)
    _ = Cdec * ((Work.Diff.STE.wt k) ^ N * ((Work.Diff.STE.wt k) ^ Mdec)⁻¹) := by ring
    _ = Cdec * ((Work.Diff.STE.wt k) ^ (Mdec - N))⁻¹ := by
        rw [hsplit]
        field_simp

lemma moments_of_decay {T : ℝ} (c : ℝ → (Fin n → ℤ) → MatC n)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      ‖c t k' a b‖ * (Work.Diff.STE.wt k') ^ M ≤ C) :
    ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) T → ∀ (a b : Fin n) (N : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c t k a b‖) := by
  intro t ht a b N
  obtain ⟨C, _hC0, hCb⟩ := hdec (N + n + 1)
  exact summable_wt_mul_norm_of_decay (n := n) (γ := fun k => c t k a b) N (N + n + 1) le_rfl
    (fun k => hCb t ht k a b)

lemma summable_moments_of_entries {c : (Fin n → ℤ) → MatC n}
    (hmom : ∀ (a b : Fin n) (N : ℕ),
      Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k a b‖))
    (N : ℕ) : Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖) := by
  have hentry : Summable (fun k : Fin n → ℤ =>
      ∑ a : Fin n, ∑ b : Fin n, (Work.Diff.STE.wt k) ^ N * ‖c k a b‖) :=
    summable_sum (fun a _ => summable_sum (fun b _ => hmom a b N))
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le N) (norm_nonneg _))
    (fun k => ?_) hentry
  have h1 : ‖c k‖ ≤ ∑ a : Fin n, ∑ b : Fin n, ‖c k a b‖ := by
    calc ‖c k‖ ≤ ∑ a : Fin n, ‖c k a‖ := by
          rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun a _ => norm_nonneg _)]
          intro a
          exact Finset.single_le_sum (fun a _ => norm_nonneg _) (Finset.mem_univ a)
      _ ≤ ∑ a : Fin n, ∑ b : Fin n, ‖c k a b‖ := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun b _ => norm_nonneg _)]
          intro b
          exact Finset.single_le_sum (fun b _ => norm_nonneg _) (Finset.mem_univ b)
  calc (Work.Diff.STE.wt k) ^ N * ‖c k‖
      ≤ (Work.Diff.STE.wt k) ^ N * (∑ a : Fin n, ∑ b : Fin n, ‖c k a b‖) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (Work.Diff.STE.wt_pos k).le N)
    _ = ∑ a : Fin n, ∑ b : Fin n, (Work.Diff.STE.wt k) ^ N * ‖c k a b‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

/-! ## 2. Smoothness helpers -/

lemma contDiff_pd_smooth {g : (Fin n → ℝ) → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd i g) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) := by fun_prop
  have h2 := h1.clm_apply (contDiff_const (c := Pi.single i (1 : ℝ)))
  show ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => (fderiv ℝ g x) (Pi.single i (1 : ℝ)))
  exact h2

lemma contDiff_pdList_smooth {g : (Fin n → ℝ) → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (l : List (Fin n)) : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdList l g) := by
  induction l with
  | nil => simpa [Work.Diff.STE.pdList] using hg
  | cons a l ih =>
      have h : Work.Diff.STE.pdList (a :: l) g = Work.Diff.STE.pd a (Work.Diff.STE.pdList l g) := rfl
      rw [h]
      exact contDiff_pd_smooth ih a

lemma contDiff_seriesFunM_entry {c : (Fin n → ℤ) → MatC n}
    (hmom : ∀ N : ℕ, Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖))
    (a b : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => seriesFunM c y a b) := by
  have h : (fun y : Fin n → ℝ => seriesFunM c y a b)
      = Work.Diff.STE.seriesFun (fun k : Fin n → ℤ => c k a b) := by
    funext y; rw [seriesFunM_apply]
  rw [h]
  refine Work.Diff.STE.contDiff_seriesFun _ (fun N => ?_)
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le N) (norm_nonneg _))
    (fun k => ?_) (hmom N)
  exact mul_le_mul_of_nonneg_left
    ((norm_le_pi_norm (c k a) b).trans (norm_le_pi_norm (c k) a))
    (pow_nonneg (Work.Diff.STE.wt_pos k).le N)

lemma contDiff_pdM_smooth {u : Torus n} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (c : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (pdM c u) := by
  refine contDiff_pi.mpr fun a => contDiff_pi.mpr fun b => ?_
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => u y a b) :=
    contDiff_pi.mp (contDiff_pi.mp hu a) b
  exact contDiff_pd_smooth h1 c

lemma contDiff_jetM_smooth {u : Torus n} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => jetM u x) := by
  have hval : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => u x) := hu
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => fun c : Fin n => pdM c u x) :=
    contDiff_pi.mpr fun c => contDiff_pdM_smooth hu c
  have hsec : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → ℝ => fun c d : Fin n => pdM c (pdM d u) x) := by
    refine contDiff_pi.mpr fun c => ?_
    exact contDiff_pi.mpr fun d => contDiff_pdM_smooth (contDiff_pdM_smooth hu d) c
  have hjet : (fun x : Fin n → ℝ => jetM u x)
      = fun x : Fin n → ℝ =>
          (u x, (fun c : Fin n => pdM c u x, fun c d : Fin n => pdM c (pdM d u) x)) := rfl
  rw [hjet]
  exact ContDiff.prodMk hval (hlin.prodMk hsec)

/-! ## 3. Pi/product decompositions -/

lemma norm_le_sum_proj_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {k : ℕ} (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ((i : ι) → F i)) :
    ‖Φ‖ ≤ ∑ i, ‖(ContinuousLinearMap.proj i).compContinuousMultilinearMap Φ‖ := by
  rw [ContinuousMultilinearMap.opNorm_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)]
  intro m
  have h1 : ‖Φ m‖ ≤ ∑ i, ‖((ContinuousLinearMap.proj i).compContinuousMultilinearMap Φ) m‖ := by
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    intro i
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.proj_apply]
    exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  calc ‖Φ m‖ ≤ ∑ i, ‖((ContinuousLinearMap.proj i).compContinuousMultilinearMap Φ) m‖ := h1
    _ ≤ ∑ i, ‖(ContinuousLinearMap.proj i).compContinuousMultilinearMap Φ‖ * ∏ s, ‖m s‖ :=
        Finset.sum_le_sum fun i _ => ContinuousMultilinearMap.le_opNorm _ m
    _ = (∑ i, ‖(ContinuousLinearMap.proj i).compContinuousMultilinearMap Φ‖) * ∏ s, ‖m s‖ :=
        (Finset.sum_mul ..).symm

lemma norm_iteratedFDeriv_le_sum_components {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {f : E → ((i : ι) → F i)} {x : E} {k : ℕ} {N : ℕ∞ω} (hf : ContDiffAt ℝ N f x)
    (hk : (k : ℕ∞ω) ≤ N) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ ∑ i, ‖iteratedFDeriv ℝ k (fun z => f z i) x‖ := by
  have key : ∀ i : ι, iteratedFDeriv ℝ k (fun z => f z i) x
      = (ContinuousLinearMap.proj i).compContinuousMultilinearMap (iteratedFDeriv ℝ k f x) := by
    intro i
    have h := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
      (ContinuousLinearMap.proj i) hf (i := k) hk
    simpa [Function.comp_def] using h
  simp only [key]
  exact norm_le_sum_proj_comp (iteratedFDeriv ℝ k f x)

lemma norm_iteratedFDeriv_prod_le_smooth {E J K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (w : E → J) (v : E → K) (x : E) (k : ℕ) {N : ℕ∞ω} (hw : ContDiffAt ℝ N w x)
    (hv : ContDiffAt ℝ N v x) (hk : (k : ℕ∞ω) ≤ N) :
    ‖iteratedFDeriv ℝ k (fun y => (w y, v y)) x‖
      ≤ ‖iteratedFDeriv ℝ k w x‖ + ‖iteratedFDeriv ℝ k v x‖ := by
  rw [iteratedFDeriv_prodMk hw hv hk, ContinuousMultilinearMap.opNorm_prod]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))








/-! ## 4. The decomposition of the jet tuple into scalar pieces -/

lemma jet_pi_decomp {c : (Fin n → ℤ) → MatC n} {x : Fin n → ℝ} {m : ℕ}
    (hval : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => seriesFunM c y))
    (hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => fun c' : Fin n => pdM c' (seriesFunM c) y))
    (hsec : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Fin n → ℝ => fun c' d : Fin n => pdM c' (pdM d (seriesFunM c)) y)) :
    ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => jetM (seriesFunM c) y) x‖ ≤
      (∑ a : Fin n, ∑ b : Fin n, ‖iteratedFDeriv ℝ m (fun y => seriesFunM c y a b) x‖)
      + (∑ c' : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdList [c']
            (fun z => seriesFunM c z a b) y) x‖)
      + (∑ c' : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdList [c', d]
            (fun z => seriesFunM c z a b) y) x‖) := by
  have hk : (m : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) := by simp
  -- (i) divide the jet into its value part and its (first, second) jet part
  have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ =>
      (fun c' : Fin n => pdM c' (seriesFunM c) y,
        fun c' d : Fin n => pdM c' (pdM d (seriesFunM c)) y)) := hlin.prodMk hsec
  have h1 := norm_iteratedFDeriv_prod_le_smooth (w := fun y : Fin n → ℝ => seriesFunM c y)
    (v := fun y : Fin n → ℝ => (fun c' : Fin n => pdM c' (seriesFunM c) y,
      fun c' d : Fin n => pdM c' (pdM d (seriesFunM c)) y)) x m hval.contDiffAt
    hpair.contDiffAt hk
  -- (ii) the value part
  have h2 : ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y) x‖
      ≤ ∑ a : Fin n, ∑ b : Fin n, ‖iteratedFDeriv ℝ m (fun y => seriesFunM c y a b) x‖ := by
    refine (norm_iteratedFDeriv_le_sum_components
      (f := fun y : Fin n → ℝ => seriesFunM c y) hval.contDiffAt hk).trans ?_
    refine Finset.sum_le_sum fun a _ => ?_
    exact norm_iteratedFDeriv_le_sum_components (f := fun y : Fin n → ℝ => seriesFunM c y a)
      ((contDiff_pi.mp hval a).contDiffAt) hk
  -- (iii) the (first, second) jet part
  have h3 : ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ =>
        (fun c' : Fin n => pdM c' (seriesFunM c) y,
          fun c' d : Fin n => pdM c' (pdM d (seriesFunM c)) y)) x‖
      ≤ (∑ c' : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdList [c']
            (fun z => seriesFunM c z a b) y) x‖)
        + (∑ c' : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdList [c', d]
            (fun z => seriesFunM c z a b) y) x‖) := by
    have hp := norm_iteratedFDeriv_prod_le_smooth
      (w := fun y : Fin n → ℝ => fun c' : Fin n => pdM c' (seriesFunM c) y)
      (v := fun y : Fin n → ℝ => fun c' d : Fin n => pdM c' (pdM d (seriesFunM c)) y)
      x m hlin.contDiffAt hsec.contDiffAt hk
    have h3a : ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => fun c' : Fin n =>
        pdM c' (seriesFunM c) y) x‖
        ≤ ∑ c' : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdList [c']
            (fun z => seriesFunM c z a b) y) x‖ := by
      refine (norm_iteratedFDeriv_le_sum_components
        (f := fun y : Fin n → ℝ => fun c' : Fin n => pdM c' (seriesFunM c) y)
        hlin.contDiffAt hk).trans ?_
      refine Finset.sum_le_sum fun c' _ => ?_
      have hc' : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => pdM c' (seriesFunM c) y) :=
        contDiff_pi.mp hlin c'
      refine (norm_iteratedFDeriv_le_sum_components
        (f := fun y : Fin n → ℝ => pdM c' (seriesFunM c) y) hc'.contDiffAt hk).trans ?_
      refine Finset.sum_le_sum fun a _ => ?_
      exact norm_iteratedFDeriv_le_sum_components
        (f := fun y : Fin n → ℝ => pdM c' (seriesFunM c) y a)
        ((contDiff_pi.mp hc' a).contDiffAt) hk
    have h3b : ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => fun c' d : Fin n =>
        pdM c' (pdM d (seriesFunM c)) y) x‖
        ≤ ∑ c' : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdList [c', d]
            (fun z => seriesFunM c z a b) y) x‖ := by
      refine (norm_iteratedFDeriv_le_sum_components
        (f := fun y : Fin n → ℝ => fun c' d : Fin n => pdM c' (pdM d (seriesFunM c)) y)
        hsec.contDiffAt hk).trans ?_
      refine Finset.sum_le_sum fun c' _ => ?_
      have hc' : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : Fin n → ℝ => fun d : Fin n => pdM c' (pdM d (seriesFunM c)) y) :=
        contDiff_pi.mp hsec c'
      refine (norm_iteratedFDeriv_le_sum_components
        (f := fun y : Fin n → ℝ => fun d : Fin n => pdM c' (pdM d (seriesFunM c)) y)
        hc'.contDiffAt hk).trans ?_
      refine Finset.sum_le_sum fun d _ => ?_
      have hd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => pdM c' (pdM d (seriesFunM c)) y) :=
        contDiff_pi.mp hc' d
      refine (norm_iteratedFDeriv_le_sum_components
        (f := fun y : Fin n → ℝ => pdM c' (pdM d (seriesFunM c)) y) hd.contDiffAt hk).trans ?_
      refine Finset.sum_le_sum fun a _ => ?_
      exact norm_iteratedFDeriv_le_sum_components
        (f := fun y : Fin n → ℝ => pdM c' (pdM d (seriesFunM c)) y a)
        ((contDiff_pi.mp hd a).contDiffAt) hk
    calc ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ =>
          (fun c' : Fin n => pdM c' (seriesFunM c) y,
            fun c' d : Fin n => pdM c' (pdM d (seriesFunM c)) y)) x‖
        ≤ _ + _ := hp
      _ ≤ _ + _ := add_le_add h3a h3b
  calc ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => jetM (seriesFunM c) y) x‖
      ≤ ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => seriesFunM c y) x‖
        + ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ =>
            (fun c' : Fin n => pdM c' (seriesFunM c) y,
              fun c' d : Fin n => pdM c' (pdM d (seriesFunM c)) y)) x‖ := h1
    _ ≤ (∑ a : Fin n, ∑ b : Fin n, ‖iteratedFDeriv ℝ m (fun y => seriesFunM c y a b) x‖)
        + ((∑ c' : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdList [c']
              (fun z => seriesFunM c z a b) y) x‖)
          + (∑ c' : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdList [c', d]
              (fun z => seriesFunM c z a b) y) x‖)) := add_le_add h2 h3
    _ = (∑ a : Fin n, ∑ b : Fin n, ‖iteratedFDeriv ℝ m (fun y => seriesFunM c y a b) x‖)
        + (∑ c' : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdList [c']
              (fun z => seriesFunM c z a b) y) x‖)
        + (∑ c' : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n,
            ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdList [c', d]
              (fun z => seriesFunM c z a b) y) x‖) := by ring








/-! ## 5. The auxiliary estimates -/











lemma pdList_replicate {n : ℕ} (i : Fin n) (k : ℕ) (g : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pdList (List.replicate k i) g = (Work.Diff.STE.pd i)^[k] g := by
  induction k with
  | zero => simp [Work.Diff.STE.pdList]
  | succ m ih =>
      have h : Work.Diff.STE.pdList (List.replicate (m + 1) i) g
          = Work.Diff.STE.pd i (Work.Diff.STE.pdList (List.replicate m i) g) := by
        rw [List.replicate_succ]; rfl
      rw [h, ih]
      exact (Function.iterate_succ_apply' (Work.Diff.STE.pd i) m g).symm

theorem fourierCoeff_weight_le {M : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ), 0 ≤ B → ∀ (h : (Fin n → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) h → Work.Diff.STE.Periodic1 h →
      (∀ x : Fin n → ℝ, (∀ i : Fin n, x i ∈ Set.Icc 0 1) → ‖h x‖ ≤ B) →
      (∀ x : Fin n → ℝ, (∀ i : Fin n, x i ∈ Set.Icc 0 1) →
        ‖iteratedFDeriv ℝ (2 * M) h x‖ ≤ B) →
      ∀ k : Fin n → ℤ,
        ‖Work.Diff.STE.fourierCoeff h k‖ * (Work.Diff.STE.wt k) ^ M ≤ C * B := by
  refine ⟨((n : ℝ) + 1) ^ M * (1 + (n : ℝ) / (2 * Real.pi) ^ (2 * M)), by positivity, ?_⟩
  intro B hB h hh hper hval hder k
  have hcube_sub : ∀ x ∈ Work.Diff.STE.unitCube (ι := Fin n), ∀ i : Fin n, x i ∈ Set.Icc (0:ℝ) 1 := by
    intro x hx i
    simp only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx
    exact ⟨le_of_lt (hx i).1, (hx i).2⟩
  have hBd : ∀ (g : (Fin n → ℝ) → ℂ), Continuous g →
      (∀ x ∈ Work.Diff.STE.unitCube (ι := Fin n), ‖g x‖ ≤ B) →
      ‖Work.Diff.STE.fourierCoeff g k‖ ≤ B := by
    intro g hg hgb
    have h1 : ‖Work.Diff.STE.fourierCoeff g k‖
        ≤ ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖g x‖ := by
      rw [Work.Diff.STE.fourierCoeff]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show ‖Work.Diff.STE.fourierExp (-k) x * g x‖ = ‖g x‖
      rw [norm_mul, Work.Diff.STE.norm_fourierExp, one_mul]
    have hconst : ∫ _x in Work.Diff.STE.unitCube (ι := Fin n), (B : ℝ) = B :=
      JetComp.integral_const_unitCube n B
    have h2 : ∫ x in Work.Diff.STE.unitCube (ι := Fin n), ‖g x‖
        ≤ ∫ _x in Work.Diff.STE.unitCube (ι := Fin n), (B : ℝ) := by
      refine MeasureTheory.setIntegral_mono_on ?_ ?_ ?_ ?_
      · exact JetComp.integrableOn_unitCube_of_continuous hg.norm
      · exact MeasureTheory.integrableOn_const (by rw [JetComp.vol_unitCube]; norm_num)
      · exact JetComp.measSet_unitCube n
      · intro x hx; exact hgb x hx
    rw [hconst] at h2
    exact h1.trans h2
  have h0 : ‖Work.Diff.STE.fourierCoeff h k‖ ≤ B :=
    hBd h hh.continuous (fun x hx => hval x (hcube_sub x hx))
  have hi : ∀ i : Fin n,
      ‖Work.Diff.STE.fourierCoeff ((Work.Diff.STE.pd i)^[2 * M] h) k‖ ≤ B := by
    intro i
    refine hBd _ (Work.Diff.STE.ste_contDiff_iterate_pd i (2 * M) hh).continuous
      (fun x hx => ?_)
    have h1 : (Work.Diff.STE.pd i)^[2 * M] h x
        = iteratedFDeriv ℝ (2 * M) h x (fun _ : Fin (2 * M) => Pi.single i (1 : ℝ)) := by
      rw [← Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv (2 * M) h hh x (fun _ => i)]
      rw [Work.Diff.STE.pdVec, List.ofFn_const, pdList_replicate]
    rw [h1]
    calc ‖iteratedFDeriv ℝ (2 * M) h x
            (fun _ : Fin (2 * M) => (Pi.single i (1 : ℝ) : Fin n → ℝ))‖
        ≤ ‖iteratedFDeriv ℝ (2 * M) h x‖
            * ∏ _ : Fin (2 * M), ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ (2 * M) h x‖ := by
          have hpi : ∀ j : Fin (2 * M), ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
            intro j
            refine le_antisymm ?_ ?_
            · rw [pi_norm_le_iff_of_nonneg zero_le_one]
              intro kk
              rw [Pi.single_apply]
              split_ifs <;> simp
            · have h := norm_le_pi_norm (Pi.single i (1 : ℝ) : Fin n → ℝ) i
              simpa using h
          rw [Finset.prod_congr rfl (fun j _ => hpi j), Finset.prod_const_one, mul_one]
      _ ≤ B := hder x (hcube_sub x hx)
  have hnorm : ∀ i : Fin n, ((((k i : ℤ)) : ℝ) ^ 2) ^ M * ‖Work.Diff.STE.fourierCoeff h k‖
      = ‖Work.Diff.STE.fourierCoeff ((Work.Diff.STE.pd i)^[2 * M] h) k‖
          / (2 * Real.pi) ^ (2 * M) := by
    intro i
    have h1 := Work.Diff.STE.ste_norm_iterate i (2 * M) h k hh (hper i)
    have h2 : ‖Work.Diff.STE.fourierCoeff ((Work.Diff.STE.pd i)^[2 * M] h) k‖
        = (2 * Real.pi) ^ (2 * M) * ((((k i : ℤ)) : ℝ) ^ 2) ^ M
            * ‖Work.Diff.STE.fourierCoeff h k‖ := by
      rw [h1]
      congr 2
      calc (2 * Real.pi * |(((k i : ℤ)) : ℝ)|) ^ (2 * M)
          = ((2 * Real.pi * |(((k i : ℤ)) : ℝ)|) ^ 2) ^ M := by rw [pow_mul]
        _ = ((2 * Real.pi) ^ 2 * |(((k i : ℤ)) : ℝ)| ^ 2) ^ M := by rw [mul_pow]
        _ = ((2 * Real.pi) ^ 2) ^ M * (|(((k i : ℤ)) : ℝ)| ^ 2) ^ M := by rw [mul_pow]
        _ = (2 * Real.pi) ^ (2 * M) * ((((k i : ℤ)) : ℝ) ^ 2) ^ M := by
            rw [pow_mul, sq_abs]
    have h3 : (0 : ℝ) < (2 * Real.pi) ^ (2 * M) := by positivity
    rw [h2]
    field_simp
  have hmain : ‖Work.Diff.STE.fourierCoeff h k‖ * (Work.Diff.STE.wt k) ^ M
      ≤ ((n : ℝ) + 1) ^ M * (1 + (n : ℝ) / (2 * Real.pi) ^ (2 * M)) * B := by
    have hwt := Work.Diff.STE.ste_wt_pow_le_card (ι := Fin n) M k
    have hwt' : (Work.Diff.STE.wt k) ^ M
        ≤ ((n : ℝ) + 1) ^ M * (1 + ∑ i : Fin n, ((((k i : ℤ)) : ℝ) ^ 2) ^ M) := by
      simpa using hwt
    calc ‖Work.Diff.STE.fourierCoeff h k‖ * (Work.Diff.STE.wt k) ^ M
        ≤ ‖Work.Diff.STE.fourierCoeff h k‖
            * (((n : ℝ) + 1) ^ M * (1 + ∑ i : Fin n, ((((k i : ℤ)) : ℝ) ^ 2) ^ M)) :=
          mul_le_mul_of_nonneg_left hwt' (norm_nonneg _)
      _ = ((n : ℝ) + 1) ^ M
            * (‖Work.Diff.STE.fourierCoeff h k‖
              * (1 + ∑ i : Fin n, ((((k i : ℤ)) : ℝ) ^ 2) ^ M)) := by ring
      _ = ((n : ℝ) + 1) ^ M
            * (‖Work.Diff.STE.fourierCoeff h k‖
              + ∑ i : Fin n, ((((k i : ℤ)) : ℝ) ^ 2) ^ M
                  * ‖Work.Diff.STE.fourierCoeff h k‖) := by
          congr 1
          rw [mul_add, mul_one, Finset.mul_sum]
          exact congrArg (fun z => ‖Work.Diff.STE.fourierCoeff h k‖ + z)
            (Finset.sum_congr rfl fun i _ => by ring)
      _ ≤ ((n : ℝ) + 1) ^ M
            * (B + ∑ i : Fin n, ‖Work.Diff.STE.fourierCoeff ((Work.Diff.STE.pd i)^[2 * M] h) k‖
                / (2 * Real.pi) ^ (2 * M)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add h0 ?_) (by positivity)
          exact Finset.sum_le_sum fun i _ => by rw [← hnorm i]
      _ ≤ ((n : ℝ) + 1) ^ M * (B + ∑ _i : Fin n, B / (2 * Real.pi) ^ (2 * M)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
          exact Finset.sum_le_sum fun i _ => by
            rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < (2 * Real.pi) ^ (2 * M))]
            exact hi i
      _ = ((n : ℝ) + 1) ^ M * (B + (n : ℝ) * (B / (2 * Real.pi) ^ (2 * M))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ((n : ℝ) + 1) ^ M * (1 + (n : ℝ) / (2 * Real.pi) ^ (2 * M)) * B := by ring
  calc ‖Work.Diff.STE.fourierCoeff h k‖ * (Work.Diff.STE.wt k) ^ M
      ≤ ((n : ℝ) + 1) ^ M * (1 + (n : ℝ) / (2 * Real.pi) ^ (2 * M)) * B := hmain








theorem pdList_bound_of_decay {T : ℝ} (c : ℝ → (Fin n → ℤ) → MatC n) (L : ℕ)
    (hmom : ∀ (t : ℝ), t ∈ Set.Ico (0 : ℝ) T → ∀ (a b : Fin n) (N : ℕ),
      Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖c t k a b‖))
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      ‖c t k' a b‖ * (wt k') ^ M ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (l : List (Fin n)), l.length ≤ L →
      ∀ (a b : Fin n) (x : Fin n → ℝ),
      ‖Work.Diff.STE.pdList l (fun y => seriesFunM (c t) y a b) x‖ ≤ D := by
  obtain ⟨C, hC0, hCb⟩ := Work.Diff.STE.flat.sup_pdList_le (n := n) (n + 1) L (by omega)
  obtain ⟨C', hC'0, hC'b⟩ := Work.Diff.STE.flat.CSq_le_of_decay (n := n) (τ := T) (n + 1 + L) c hdec
  refine ⟨C * Real.sqrt C', by positivity, ?_⟩
  intro t ht l hl a b x
  have hfun : (fun y : Fin n → ℝ => seriesFunM (c t) y a b)
      = Work.Diff.STE.seriesFun (fun k : Fin n → ℤ => c t k a b) := by
    funext y; rw [seriesFunM_apply]
  rw [hfun]
  calc ‖Work.Diff.STE.pdList l (Work.Diff.STE.seriesFun (fun k : Fin n → ℤ => c t k a b)) x‖
      ≤ C * Real.sqrt (Work.Diff.STE.CSq (n + 1 + L) (fun k : Fin n → ℤ => c t k a b)) :=
        hCb _ (fun N => hmom t ht a b N) l hl x
    _ ≤ C * Real.sqrt C' := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hC'b t ht a b)) hC0

lemma pdList_bound_all_levels {T : ℝ} (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (j L : ℕ)
    (hdec : ∀ i ≤ j, ∀ M' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ (k' : Fin n → ℤ) (a b : Fin n), ‖dd Φ cinf i t k' a b‖ * (Work.Diff.STE.wt k') ^ M' ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (i : Fin (j+1)) (l : List (Fin n)),
      l.length ≤ L → ∀ (a b : Fin n) (x : Fin n → ℝ),
      ‖Work.Diff.STE.pdList l (fun y => seriesFunM (dd Φ cinf (i:ℕ) t) y a b) x‖ ≤ D := by
  have hlev : ∀ i : Fin (j + 1), ∃ D : ℝ, 0 ≤ D ∧
      ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (l : List (Fin n)), l.length ≤ L →
        ∀ (a b : Fin n) (x : Fin n → ℝ),
        ‖Work.Diff.STE.pdList l (fun y => seriesFunM (dd Φ cinf (i:ℕ) t) y a b) x‖ ≤ D := by
    intro i
    have hi : (i : ℕ) ≤ j := by have := i.isLt; omega
    exact pdList_bound_of_decay (fun t => dd Φ cinf (i : ℕ) t) L
      (fun t ht a b N => moments_of_decay (fun t => dd Φ cinf (i:ℕ) t)
        (hdec (i:ℕ) hi) t ht a b N)
      (hdec (i : ℕ) hi)
  choose D hD0 hDb using hlev
  refine ⟨(Finset.univ : Finset (Fin (j+1))).sup' ⟨0, Finset.mem_univ 0⟩ D, ?_, ?_⟩
  · exact le_trans (hD0 0) (Finset.le_sup' D (Finset.mem_univ 0))
  · intro t ht i l hl a b x
    exact le_trans (hDb i t ht l hl a b x) (Finset.le_sup' D (Finset.mem_univ i))








theorem jetTup_deriv_bound {T : ℝ} (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (j M : ℕ)
    (hdec : ∀ i ≤ j, ∀ M' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ (k' : Fin n → ℤ) (a b : Fin n), ‖dd Φ cinf i t k' a b‖ * (Work.Diff.STE.wt k') ^ M' ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (m : ℕ), m ≤ M → ∀ x : Fin n → ℝ,
      ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => fun i : Fin (j+1) =>
        jetM (seriesFunM (dd Φ cinf (i:ℕ) t)) x) x‖ ≤ D := by
  obtain ⟨D0, hD00, hD0b⟩ := pdList_bound_all_levels Φ cinf j (M + 2) hdec
  refine ⟨(1 * ((((j : ℝ) + 1) * ((n : ℝ)^2 + (n : ℝ)^3 + (n : ℝ)^4)) * ((n : ℝ) + 1)^M) * D0),
    by positivity, ?_⟩
  intro t ht m hm x
  have hcard : ((Fintype.card (Fin m → Fin n) : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ M := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have h1 : n ^ m ≤ (n + 1) ^ M := by
      calc n ^ m ≤ (n + 1) ^ m := Nat.pow_le_pow_left (Nat.le_succ n) m
        _ ≤ (n + 1) ^ M := Nat.pow_le_pow_right (Nat.succ_pos n) hm
    exact_mod_cast h1
  have hmm : ∀ (i : Fin (j+1)) (N : ℕ), Summable (fun k : Fin n → ℤ =>
      (Work.Diff.STE.wt k) ^ N * ‖dd Φ cinf (i:ℕ) t k‖) := by
    intro i N
    have hi : (i : ℕ) ≤ j := by have := i.isLt; omega
    exact summable_moments_of_entries (fun a' b' N' =>
      moments_of_decay (fun t => dd Φ cinf (i:ℕ) t) (hdec (i:ℕ) hi) t ht a' b' N') N
  have hscalar : ∀ (i : Fin (j+1)) (l0 : List (Fin n)), l0.length ≤ 2 → ∀ (a b : Fin n),
      ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdList l0
        (fun z => seriesFunM (dd Φ cinf (i:ℕ) t) z a b) y) x‖
        ≤ ((Fintype.card (Fin m → Fin n) : ℕ) : ℝ) * D0 := by
    intro i l0 hl0 a b
    have hcd0 : ContDiff ℝ (⊤ : ℕ∞) (fun z => seriesFunM (dd Φ cinf (i:ℕ) t) z a b) :=
      contDiff_seriesFunM_entry (hmm i) a b
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun y => Work.Diff.STE.pdList l0
        (fun z => seriesFunM (dd Φ cinf (i:ℕ) t) z a b) y) :=
      contDiff_pdList_smooth hcd0 l0
    refine (norm_iteratedFDeriv_le_sum_pdVec m _ hcd x).trans ?_
    have hterm : ∀ l : Fin m → Fin n, ‖Work.Diff.STE.pdVec m l
        (fun y => Work.Diff.STE.pdList l0 (fun z => seriesFunM (dd Φ cinf (i:ℕ) t) z a b) y) x‖
        ≤ D0 := by
      intro l
      rw [Work.Diff.STE.pdVec]
      rw [show Work.Diff.STE.pdList (List.ofFn l) (Work.Diff.STE.pdList l0
            (fun z => seriesFunM (dd Φ cinf (i:ℕ) t) z a b))
          = Work.Diff.STE.pdList (List.ofFn l ++ l0)
            (fun z => seriesFunM (dd Φ cinf (i:ℕ) t) z a b) from by
        rw [Work.Diff.STE.pdList, Work.Diff.STE.pdList, Work.Diff.STE.pdList, List.foldr_append]]
      exact hD0b t ht i _ (by simp [List.length_ofFn]; omega) a b x
    calc ∑ l : Fin m → Fin n, ‖Work.Diff.STE.pdVec m l
          (fun y => Work.Diff.STE.pdList l0 (fun z => seriesFunM (dd Φ cinf (i:ℕ) t) z a b) y) x‖
        ≤ ∑ _l : Fin m → Fin n, D0 := Finset.sum_le_sum fun l _ => hterm l
      _ = ((Fintype.card (Fin m → Fin n) : ℕ) : ℝ) * D0 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- the per-level jet bound
  have hlevel : ∀ i : Fin (j+1),
      ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => jetM (seriesFunM (dd Φ cinf (i:ℕ) t)) y) x‖
        ≤ ((n:ℝ)^2 + (n:ℝ)^3 + (n:ℝ)^4) * (((Fintype.card (Fin m → Fin n) : ℕ) : ℝ) * D0) := by
    intro i
    have hval : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => seriesFunM (dd Φ cinf (i:ℕ) t) y) :=
      contDiff_pi.mpr fun a => contDiff_pi.mpr fun b =>
        contDiff_seriesFunM_entry (hmm i) a b
    have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => fun c' : Fin n =>
        pdM c' (seriesFunM (dd Φ cinf (i:ℕ) t)) y) :=
      contDiff_pi.mpr fun c' => contDiff_pdM_smooth hval c'
    have hsec : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => fun c' d : Fin n =>
        pdM c' (pdM d (seriesFunM (dd Φ cinf (i:ℕ) t))) y) :=
      contDiff_pi.mpr fun c' => contDiff_pi.mpr fun d =>
        contDiff_pdM_smooth (contDiff_pdM_smooth hval d) c'
    refine (jet_pi_decomp hval hlin hsec).trans ?_
    have hs1 : (∑ a : Fin n, ∑ b : Fin n, ‖iteratedFDeriv ℝ m
        (fun y => seriesFunM (dd Φ cinf (i:ℕ) t) y a b) x‖)
        ≤ (n : ℝ)^2 * (((Fintype.card (Fin m → Fin n) : ℕ) : ℝ) * D0) := by
      have := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin n))) =>
        Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin n))) =>
          hscalar i [] (by simp) a b))
      refine this.trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hs2 : (∑ c' : Fin n, ∑ a : Fin n, ∑ b : Fin n, ‖iteratedFDeriv ℝ m
        (fun y => Work.Diff.STE.pdList [c'] (fun z => seriesFunM (dd Φ cinf (i:ℕ) t) z a b) y) x‖)
        ≤ (n : ℝ)^3 * (((Fintype.card (Fin m → Fin n) : ℕ) : ℝ) * D0) := by
      have := Finset.sum_le_sum (fun c' (_ : c' ∈ (Finset.univ : Finset (Fin n))) =>
        Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin n))) =>
          Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin n))) =>
            hscalar i [c'] (by simp) a b)))
      refine this.trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hs3 : (∑ c' : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n, ‖iteratedFDeriv ℝ m
        (fun y => Work.Diff.STE.pdList [c', d] (fun z => seriesFunM (dd Φ cinf (i:ℕ) t) z a b) y) x‖)
        ≤ (n : ℝ)^4 * (((Fintype.card (Fin m → Fin n) : ℕ) : ℝ) * D0) := by
      have := Finset.sum_le_sum (fun c' (_ : c' ∈ (Finset.univ : Finset (Fin n))) =>
        Finset.sum_le_sum (fun d (_ : d ∈ (Finset.univ : Finset (Fin n))) =>
          Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin n))) =>
            Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin n))) =>
              hscalar i [c', d] (by simp) a b))))
      refine this.trans (le_of_eq ?_)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hstep := add_le_add (add_le_add hs1 hs2) hs3
    refine hstep.trans (le_of_eq ?_)
    ring
  -- assemble over the levels
  have hsum : ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => fun i : Fin (j+1) =>
        jetM (seriesFunM (dd Φ cinf (i:ℕ) t)) x) x‖
      ≤ ∑ _i : Fin (j+1), ((n:ℝ)^2 + (n:ℝ)^3 + (n:ℝ)^4) *
          (((Fintype.card (Fin m → Fin n) : ℕ) : ℝ) * D0) := by
    have hsmJ : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun x : Fin n → ℝ =>
        fun i : Fin (j+1) => jetM (seriesFunM (dd Φ cinf (i:ℕ) t)) x) x :=
      (contDiff_pi.mpr fun i => contDiff_jetM_smooth
        (contDiff_pi.mpr fun a => contDiff_pi.mpr fun b =>
          contDiff_seriesFunM_entry (hmm i) a b)).contDiffAt
    refine (norm_iteratedFDeriv_le_sum_components (f := fun x : Fin n → ℝ =>
      fun i : Fin (j+1) => jetM (seriesFunM (dd Φ cinf (i:ℕ) t)) x) hsmJ (by simp)).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    exact hlevel i
  calc _ ≤ ∑ _i : Fin (j+1), ((n:ℝ)^2 + (n:ℝ)^3 + (n:ℝ)^4) *
        (((Fintype.card (Fin m → Fin n) : ℕ) : ℝ) * D0) := hsum
    _ = ((j : ℝ) + 1) * (((n:ℝ)^2 + (n:ℝ)^3 + (n:ℝ)^4) *
        (((Fintype.card (Fin m → Fin n) : ℕ) : ℝ) * D0)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((j : ℝ) + 1) * (((n:ℝ)^2 + (n:ℝ)^3 + (n:ℝ)^4) * (((n : ℝ) + 1)^M * D0)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hcard hD00
    _ = _ := by ring








theorem towerExp_periodic' {n : ℕ}
    (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (hper : ∀ (x : Fin n → ℝ) (w : Jet n) (i : Fin n), Φ (x + Pi.single i 1, w) = Φ (x, w)) :
    ∀ (j : ℕ) (x : Fin n → ℝ) (Js : Fin j → Jet n) (i : Fin n),
      towerExp Φ j (x + Pi.single i 1, Js) = towerExp Φ j (x, Js) := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero => intro x Js i; rfl
  | one => intro x Js i; exact hper x (Js 0) i
  | more j ih ihs =>
      intro x Js i
      rw [towerExp_succ_succ (Φ := Φ) (j := j), towerExp_succ_succ (Φ := Φ) (j := j)]
      refine Finset.sum_congr rfl fun i' _ => ?_
      have hfun : (fun Js' : Fin (j+1) → Jet n => towerExp Φ (j+1) (x + Pi.single i 1, Js'))
          = (fun Js' : Fin (j+1) → Jet n => towerExp Φ (j+1) (x, Js')) :=
        funext fun Js' => ihs x Js' i
      rw [hfun]

theorem comp_sup_bound {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Ψ : (Fin n → ℝ) × F → G) (P : (Fin n → ℝ) → F) (s M : ℕ) (K A A' : ℝ)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hΨsm : ∀ x : Fin n → ℝ, ContDiffAt ℝ (↑(⊤ : ℕ∞)) Ψ (x, P x))
    (hPsm : ∀ x : Fin n → ℝ, ContDiffAt ℝ (↑(⊤ : ℕ∞)) P x)
    (hM : (s + 1) / 2 ≤ M)
    (hΨ : ∀ j ≤ s + 1, ∀ x, ‖iteratedFDeriv ℝ j Ψ (x, P x)‖ ≤ K)
    (hPsup : ∀ m ≤ M, ∀ x, ‖iteratedFDeriv ℝ m P x‖ ≤ A)
    (hS : ∀ x, ∑ k ∈ Finset.range (s + 2), ‖iteratedFDeriv ℝ k P x‖ ≤ A') :
    ∀ x, ‖iteratedFDeriv ℝ (s + 1) (fun y => Ψ (y, P y)) x‖
      ≤ (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) * K * (1 + A) ^ (s + 1) * (1 + A') := by
  intro x
  have hfb := JetComp.faaDiBruno_sum_le (g := Ψ) (f := fun y : Fin n → ℝ => (y, P y))
    (hΨsm x) ((contDiffAt_id (x := x)).prodMk (hPsm x)) (s + 1)
  have hrw : (Ψ ∘ fun y : Fin n → ℝ => (y, P y)) = (fun y : Fin n → ℝ => Ψ (y, P y)) := rfl
  rw [hrw] at hfb
  refine hfb.trans ?_
  have hterm : ∀ d : OrderedFinpartition (s + 1),
      ‖iteratedFDeriv ℝ d.length Ψ (x, P x)‖ *
        ∏ i, ‖iteratedFDeriv ℝ (d.partSize i) (fun y : Fin n → ℝ => (y, P y)) x‖
      ≤ K * ((1 + A) ^ (s + 1) * (1 + A')) := by
    intro d
    have hKd : ‖iteratedFDeriv ℝ d.length Ψ (x, P x)‖ ≤ K := hΨ d.length d.length_le x
    have hPd : ∏ i, ‖iteratedFDeriv ℝ (d.partSize i) (fun y : Fin n → ℝ => (y, P y)) x‖
        ≤ (1 + A) ^ (s + 1) * (1 + A') := by
      have hstep : ∏ i, ‖iteratedFDeriv ℝ (d.partSize i) (fun y : Fin n → ℝ => (y, P y)) x‖
          ≤ ∏ i, (1 + ‖iteratedFDeriv ℝ (d.partSize i) P x‖) :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => by
          have h1 := JetComp.norm_iteratedFDeriv_pair_le P x (d.partSize i)
            (d.partSize_pos i) (hPsm x)
          have h2 : max (1 : ℝ) ‖iteratedFDeriv ℝ (d.partSize i) P x‖
              ≤ 1 + ‖iteratedFDeriv ℝ (d.partSize i) P x‖ :=
            max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left zero_le_one)
          linarith)
      refine hstep.trans ?_
      refine (JetComp.prod_one_add_le P A hA x (fun k hk y => hPsup k hk y)
        (fun i => d.partSize i) (JetComp.sum_partSize d) d.length_le
        (fun i j hi hj => JetComp.high_block_unique hM _
          (JetComp.sum_partSize d) hi hj)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith [hS x]
    exact mul_le_mul hKd hPd (Finset.prod_nonneg fun i _ => norm_nonneg _) hK
  calc ∑ d : OrderedFinpartition (s + 1), ‖iteratedFDeriv ℝ d.length Ψ (x, P x)‖ *
        ∏ i, ‖iteratedFDeriv ℝ (d.partSize i) (fun y : Fin n → ℝ => (y, P y)) x‖
      ≤ ∑ _d : OrderedFinpartition (s + 1), K * ((1 + A) ^ (s + 1) * (1 + A')) :=
        Finset.sum_le_sum fun d _ => hterm d
    _ = (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) * (K * ((1 + A) ^ (s + 1) * (1 + A'))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card (OrderedFinpartition (s + 1)) : ℝ) * K * (1 + A) ^ (s + 1) * (1 + A') := by
        ring








private lemma periodicIn_seriesFunM_entry {c : (Fin n → ℤ) → MatC n} {i : Fin n} (a b : Fin n) :
    Work.Diff.STE.PeriodicIn i (fun y : Fin n → ℝ => seriesFunM c y a b) := by
  intro x
  show seriesFunM c (x + Pi.single i 1) a b = seriesFunM c x a b
  rw [seriesFunM_apply, seriesFunM_apply]
  exact Work.Diff.STE.periodic_seriesFun (fun k => c k a b) i x

private lemma periodicIn_pd' {f : (Fin n → ℝ) → ℂ} {i : Fin n} (hper : Work.Diff.STE.PeriodicIn i f)
    (c' : Fin n) : Work.Diff.STE.PeriodicIn i (Work.Diff.STE.pd c' f) := by
  intro x
  have h1 : (fun y : Fin n → ℝ => f (y + Pi.single i 1)) = f := funext hper
  have h2 : fderiv ℝ f (x + Pi.single i 1)
      = fderiv ℝ (fun y : Fin n → ℝ => f (y + Pi.single i 1)) x := by
    rw [fderiv_comp_add_right]
  simp only [Work.Diff.STE.pd]
  rw [h2, h1]

private lemma periodic_jetM {c : (Fin n → ℤ) → MatC n} :
    ∀ (i : Fin n) (x : Fin n → ℝ),
      jetM (seriesFunM c) (x + Pi.single i 1) = jetM (seriesFunM c) x := by
  intro i x
  unfold jetM
  congr 1
  · ext a b
    exact periodicIn_seriesFunM_entry (c := c) (i := i) a b x
  · congr 1
    · ext c' a b
      have h := periodicIn_pd' (periodicIn_seriesFunM_entry (c := c) (i := i) a b) c' x
      simpa only [pdM, Function.comp_apply] using h
    · ext c' d a b
      have h1 := periodicIn_seriesFunM_entry (c := c) (i := i) a b
      have h2 : Work.Diff.STE.PeriodicIn i (Work.Diff.STE.pd d (fun y => seriesFunM c y a b)) :=
        periodicIn_pd' h1 d
      have h3 := periodicIn_pd' h2 c' x
      simpa only [pdM, Function.comp_apply] using h3

















/-! ## The target theorem -/

theorem dd_bounds {n : ℕ} (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (T : ℝ) (hT : 0 < T)
    (Φ Φ' : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (hΦ' : ContDiff ℝ (⊤ : ℕ∞) Φ')
    (hper' : ∀ (x : Fin n → ℝ) (w : Work.Diff.STE.Flat.Jet n) (i : Fin n),
      Φ' (x + Pi.single i 1, w) = Φ' (x, w))
    (V' : Set (Work.Diff.STE.Flat.Jet n)) (hV' : IsOpen V')
    (hV'det : ∀ w : Work.Diff.STE.Flat.Jet n, w ∈ V' → (Work.Diff.STE.Flat.reMat w.1).det ≠ 0)
    (hagr : ∀ (x : Fin n → ℝ) (w : Work.Diff.STE.Flat.Jet n), w ∈ V' → Φ' (x, w) = Φ (x, w))
    (cinf : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hconf : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : Fin n → ℝ,
      Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (cinf t)) x ∈ V')
    (h0 : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      ‖cinf t k' a b‖ * (Work.Diff.STE.wt k') ^ M ≤ C) :
    ∀ (j M : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      ‖Work.Diff.STE.flat.dd Φ cinf j t k' a b‖ * (Work.Diff.STE.wt k') ^ M ≤ C := by

  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    intro j M
    exact ⟨0, le_rfl, fun t ht k' a b => Fin.elim0 a⟩
  have key : ∀ j : ℕ, ∀ i ≤ j, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Set.Ico (0:ℝ) T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
        ‖dd Φ cinf i t k' a b‖ * (wt k') ^ M ≤ C := by
    intro j
    induction j with
    | zero =>
        intro i hi M
        have hi0 : i = 0 := by omega
        subst hi0
        simpa using h0 M
    | succ j ih =>
        intro i hi M
        rcases Nat.lt_or_eq_of_le hi with hlt | heq
        · exact ih i (by omega) M
        · subst heq
          -- ============ the inductive step: level `j + 1` ============
          obtain ⟨D, hD0, hDb⟩ := jetTup_deriv_bound Φ cinf j (2 * M)
            (fun i hi M' => ih i hi M')
          have hDnorm : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Fin n → ℝ,
              ‖(fun i : Fin (j+1) => jetM (seriesFunM (dd Φ cinf (i:ℕ) t)) x)‖ ≤ D := by
            intro t ht x
            have h := hDb t ht 0 (Nat.zero_le _) x
            rwa [norm_iteratedFDeriv_zero] at h
          set cube : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1)
            with hcubedef
          haveI : ProperSpace (Fin (j+1) → Jet n) := FiniteDimensional.proper ℝ _
          set Kset : Set ((Fin n → ℝ) × (Fin (j+1) → Jet n)) :=
            cube ×ˢ Metric.closedBall (0 : Fin (j+1) → Jet n) D with hKsetdef
          have hKcomp : IsCompact Kset :=
            (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)).prod (isCompact_closedBall 0 D)
          have hKsc : ∀ (a b : Fin n), ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ Kset, ∀ m' ≤ 2 * M,
              ‖iteratedFDeriv ℝ m' (fun p : (Fin n → ℝ) × (Fin (j+1) → Jet n) =>
                towerExp Φ' (j+1) p a b) p‖ ≤ K := by
            intro a b
            refine compact_iteratedFDeriv_bound (fun p : (Fin n → ℝ) × (Fin (j+1) → Jet n) =>
              towerExp Φ' (j+1) p a b) isOpen_univ ?_ hKcomp (fun _ _ => trivial) (2 * M)
            exact (contDiff_pi.mp (contDiff_pi.mp (towerExp_contDiff Φ' hΦ' (j+1)) a) b).contDiffOn
          choose Ksc hKsc0 hKscb using hKsc
          set p0 : Fin n × Fin n := (⟨0, hn⟩, ⟨0, hn⟩) with hp0
          set Ksup : ℝ := (Finset.univ : Finset (Fin n × Fin n)).sup' ⟨p0, Finset.mem_univ p0⟩
            (fun p => Ksc p.1 p.2) with hKsupdef
          have hKsup_le : ∀ (a b : Fin n), Ksc a b ≤ Ksup := fun a b =>
            Finset.le_sup' (fun p : Fin n × Fin n => Ksc p.1 p.2) (Finset.mem_univ (a, b))
          have hKsup0 : 0 ≤ Ksup :=
            le_trans (hKsc0 ⟨0, hn⟩ ⟨0, hn⟩) (hKsup_le ⟨0, hn⟩ ⟨0, hn⟩)
          set Bder : ℝ := (Fintype.card (OrderedFinpartition (2 * M)) : ℝ) * Ksup * (1 + D) ^ (2 * M)
            * (1 + (2 * M + 1) * D) with hBderdef
          have hBder0 : 0 ≤ Bder := by rw [hBderdef]; positivity
          set B : ℝ := Ksup + Bder with hBdef
          have hB0 : 0 ≤ B := by rw [hBdef]; linarith
          have hKsup_le_B : Ksup ≤ B := by rw [hBdef]; linarith
          have hBder_le_B : Bder ≤ B := by rw [hBdef]; linarith
          obtain ⟨Csc, hCsc0, hCscb⟩ := fourierCoeff_weight_le (n := n) (M := M)
          refine ⟨Csc * B, by positivity, ?_⟩
          intro t ht k' a b
          set Jst : (Fin n → ℝ) → (Fin (j+1) → Jet n) :=
            fun x i => jetM (seriesFunM (dd Φ cinf (i:ℕ) t)) x with hJst
          have hmmJ : ∀ (i : Fin (j+1)) (N : ℕ), Summable (fun k : Fin n → ℤ =>
              (wt k) ^ N * ‖dd Φ cinf (i:ℕ) t k‖) := by
            intro i N
            have hi : (i : ℕ) ≤ j := by have := i.isLt; omega
            exact summable_moments_of_entries (fun a' b' N' =>
              moments_of_decay (fun t => dd Φ cinf (i:ℕ) t) (ih (i:ℕ) hi) t ht a' b' N') N
          have hsmJ : ContDiff ℝ (⊤ : ℕ∞) Jst := by
            rw [hJst]
            refine contDiff_pi.mpr fun i => contDiff_jetM_smooth ?_
            exact contDiff_pi.mpr fun a' => contDiff_pi.mpr fun b' =>
              contDiff_seriesFunM_entry (hmmJ i) a' b'
          -- the tower bound at an arbitrary point
          have hTower : ∀ (a b : Fin n) (x : Fin n → ℝ) (m' : ℕ), m' ≤ 2 * M →
              ‖iteratedFDeriv ℝ m' (fun p : (Fin n → ℝ) × (Fin (j+1) → Jet n) =>
                towerExp Φ' (j+1) p a b) (x, Jst x)‖ ≤ Ksup := by
            intro a b x m' hm'
            have hxmem : (fun i : Fin n => x i - ((⌊x i⌋ : ℤ) : ℝ)) ∈ cube := by
              rw [hcubedef]
              intro i _
              exact ⟨by have := Int.floor_le (x i); linarith,
                     by have := Int.lt_floor_add_one (x i); linarith⟩
            have hxeq : (fun i : Fin n => x i - ((⌊x i⌋ : ℤ) : ℝ))
                + (fun i : Fin n => (((fun j => ⌊x j⌋) i : ℤ) : ℝ)) = x := by
              funext i; simp
            have hshift := periodic_shift (fun p : (Fin n → ℝ) × (Fin (j+1) → Jet n) =>
                towerExp Φ' (j+1) p a b)
              (fun w i x' => congrArg (fun Mm : MatC n => Mm a b)
                (towerExp_periodic' Φ' hper' (j+1) x' w i))
              (fun i : Fin n => ⌊x i⌋) (Jst x) m'
              (fun i : Fin n => x i - ((⌊x i⌋ : ℤ) : ℝ))
            rw [hxeq] at hshift
            rw [hshift]
            refine le_trans (hKscb a b (_, Jst x) ⟨hxmem, ?_⟩ m' hm') (hKsup_le a b)
            rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
            exact hDnorm t ht x
          have hval : ∀ (a b : Fin n) (x : Fin n → ℝ),
              ‖(fun x => towerExp Φ' (j+1) (x, Jst x) a b) x‖ ≤ B := by
            intro a b x
            have h := hTower a b x 0 (Nat.zero_le _)
            rw [norm_iteratedFDeriv_zero] at h
            exact le_trans h hKsup_le_B
          have hcomp_bd : ∀ (a b : Fin n) (x : Fin n → ℝ),
              ‖iteratedFDeriv ℝ (2 * M) (fun x => towerExp Φ' (j+1) (x, Jst x) a b) x‖ ≤ B := by
            intro a b x
            rcases Nat.eq_zero_or_pos M with hM0 | hMpos
            · subst hM0
              rw [norm_iteratedFDeriv_zero]
              exact hval a b x
            · have hsMs : 2 * M - 1 + 1 = 2 * M := by omega
              have hres := comp_sup_bound
                (Ψ := fun p : (Fin n → ℝ) × (Fin (j+1) → Jet n) => towerExp Φ' (j+1) p a b)
                (P := Jst) (2 * M - 1) M Ksup D ((2 * M + 1) * D)
                hKsup0 hD0 (by positivity)
                (fun x' => ((contDiff_pi.mp (contDiff_pi.mp (towerExp_contDiff Φ' hΦ' (j+1)) a) b)).contDiffAt)
                (fun x' => hsmJ.contDiffAt)
                (by omega)
                (fun j' hj' x' => by rw [hsMs] at hj'; exact hTower a b x' j' hj')
                (fun m' hm' x' => hDb t ht m' (by omega) x')
                (fun x' => by
                  have h2M : 2 * M - 1 + 2 = 2 * M + 1 := by omega
                  rw [h2M]
                  calc ∑ k ∈ Finset.range (2 * M + 1), ‖iteratedFDeriv ℝ k Jst x'‖
                      ≤ ∑ _k ∈ Finset.range (2 * M + 1), D :=
                        Finset.sum_le_sum fun k hk => hDb t ht k (by
                          rw [Finset.mem_range] at hk; omega) x'
                    _ = (2 * M + 1) * D := by
                        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                        push_cast
                        ring)
                x
              rw [hsMs] at hres
              exact le_trans hres hBder_le_B
          -- apply the coefficient estimate
          have hchild : ∀ (k'' : Fin n → ℤ),
              ‖Work.Diff.STE.fourierCoeff (fun x => towerExp Φ' (j+1) (x, Jst x) a b) k''‖
                * (wt k'') ^ M ≤ Csc * B := by
            intro k''
            refine hCscb B hB0 _
              (((contDiff_pi.mp (contDiff_pi.mp (towerExp_contDiff Φ' hΦ' (j+1)) a) b)).comp
                (contDiff_id.prodMk hsmJ))
              ?_ (fun x hx => hval a b x) (fun x hx => hcomp_bd a b x) k''
            intro i x'
            have hJs : Jst (x' + Pi.single i 1) = Jst x' := by
              funext i'
              have hperj := periodic_jetM (c := fun k => dd Φ cinf (i':ℕ) t k) i x'
              simpa only [hJst] using hperj
            show towerExp Φ' (j+1) (x' + Pi.single i 1, Jst (x' + Pi.single i 1)) a b
                = towerExp Φ' (j+1) (x', Jst x') a b
            rw [hJs]
            exact congrArg (fun Mm : MatC n => Mm a b)
              (towerExp_periodic' Φ' hper' (j+1) x' (Jst x') i)
          -- identify `dd` with the Fourier coefficient
          have hdd : dd Φ cinf (j+1) t k' a b
              = Work.Diff.STE.fourierCoeff (fun x => towerExp Φ (j+1) (x, Jst x) a b) k' := by
            rw [dd_succ, fourierCoeffM_apply]
            congr 1
            funext x
            have hJsx : (fun i : Fin (j+1) =>
                jetM (seriesFunM (ddseq Φ cinf (j+1) t i)) x) = Jst x := by
              funext i
              rw [ddseq_apply]
            rw [hJsx]
          rw [hdd]
          have hfun : (fun x => towerExp Φ (j+1) (x, Jst x) a b)
              = (fun x => towerExp Φ' (j+1) (x, Jst x) a b) := by
            funext x
            have hJs0 : Jst x 0 ∈ V' := by
              rw [hJst]
              show jetM (seriesFunM (dd Φ cinf ((0 : Fin (j+1)) : ℕ) t)) x ∈ V'
              rw [show (((0 : Fin (j+1)) : ℕ)) = 0 from rfl, dd_zero]
              exact hconf t ht x
            rw [towerExp_congr Φ Φ' V' hV'
              (hshape.1.mono (by intro p hp; exact ⟨trivial, hV'det p.2 hp.2⟩))
              hΦ'.contDiffOn (fun x' w hw => (hagr x' w hw).symm) j x (Jst x) hJs0]
          rw [hfun]
          exact hchild k'
  intro j M
  exact key j j le_rfl M

end

end Work.Diff.STE.flat
