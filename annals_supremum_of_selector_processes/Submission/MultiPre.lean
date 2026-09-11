import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Multi
import Submission.MultiDeep
import Submission.MultiDeep2
import Submission.Pre

/-!
# TASK (child): prove `Submission.Multi.MSys.theorem_preprocessM` below.

## Goal: the MULTISET analogue of Submission/Pre.lean's theorem_preprocess.
Port Pre.lean's construction (cap / quantize / drop-high / obs2-trim) to multisets
`X → ℕ` with multiplicity `S x` and one level per coordinate `x` (all copies share it).

## THEOREM (final; keep name/signature):
theorem theorem_preprocessM (F : Set (X → ℕ)) (lam : (X → ℕ) → X → ℝ)
    (hFin : Set.Finite F)
    (hnonneg : ∀ S ∈ F, ∀ x : X, 0 ≤ lam S x)
    (hnonnegtot : ∀ S ∈ F, 1 ≤ mwtot lam S) :
    ∃ N : MSys X, N.FBoundedM ∧ N.TotBoundM ∧ N.FLegalM ∧
      (∀ S ∈ F, ∃ S' ∈ N.F, subM S' S) ∧
      (∀ S' ∈ N.F, ∃ S ∈ F, subM S' S ∧ ∀ x : X, 0 < S' x → lam S x ≥ wlev (N.lv S' x))
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Multi

open Sel.Deep

variable {X : Type*} [Fintype X]

/-- multiset total weight of S under per-element weights lam S -/
noncomputable def mwtot (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) : ℝ :=
  ∑ x : X, (S x : ℝ) * lam S x

lemma mwtot_nonneg {lam : (X → ℕ) → X → ℝ} {S : X → ℕ}
    (hlam : ∀ x, 0 ≤ lam S x) : 0 ≤ mwtot lam S := by
  unfold mwtot
  exact Finset.sum_nonneg (by intro x hx; exact mul_nonneg (by positivity) (hlam x))

namespace MSys

/-! ### per-coordinate preprocessing of one member (mirrors Pre.lean) -/

/-- capped per-copy weight min(λ,1) -/
def capv (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (x : X) : ℝ := min (lam S x) 1

/-- kept coordinate: has copies and capped weight big enough for level ≤ τ -/
def isKept (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (x : X) : Prop :=
  0 < S x ∧ 1 ≤ capv lam S x * (q : ℝ) ^ τ

/-- quantized level of coordinate x (junk level 0 for unkept coordinates) -/
noncomputable def lvx (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (x : X) : ℕ :=
  if isKept τ lam S x then Pre.qlev τ (capv lam S x) else 0

/-- kept coordinates, as a Finset -/
noncomputable def keepFinset (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) : Finset X :=
  (Finset.univ : Finset X).filter (fun x => isKept τ lam S x)

/-- multiplicity kept at level j -/
noncomputable def cS (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) : ℕ :=
  ((keepFinset τ lam S).filter (fun x => lvx τ lam S x = j)).sum (fun x => S x)

/-- kept-number at level j for member S -/
noncomputable def sL (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) : ℕ :=
  Pre.keepNum j (cS τ lam S j)

/-- kept decision at level j for member S -/
def keepL (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) : Prop :=
  Pre.keptLvlN j (cS τ lam S j)

/-- per-level class multiset (multiplicity of level-j copies kept as candidates) -/
noncomputable def clsM (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) : X → ℕ :=
  fun x => if isKept τ lam S x ∧ lvx τ lam S x = j then S x else 0

/-- level weight of the class -/
noncomputable def wL (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) : ℝ :=
  (cS τ lam S j : ℝ) * wlev j

/-! ### basic facts about capv / isKept / lvx / keepFinset -/

lemma capv_nonneg {lam : (X → ℕ) → X → ℝ} {S : X → ℕ} {x : X} (hlam : 0 ≤ lam S x) :
    0 ≤ capv lam S x := by
  unfold capv
  exact le_min hlam (by norm_num)

lemma capv_le_one (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (x : X) : capv lam S x ≤ 1 := by
  unfold capv
  exact min_le_right (lam S x) (1 : ℝ)

lemma capv_le_lam (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (x : X) : capv lam S x ≤ lam S x := by
  unfold capv
  exact min_le_left (lam S x) (1 : ℝ)

lemma isKept_iff (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (x : X) :
    isKept τ lam S x ↔ 0 < S x ∧ 1 ≤ capv lam S x * (q : ℝ) ^ τ := Iff.rfl

lemma mem_keepFinset_iff (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (x : X) :
    x ∈ keepFinset τ lam S ↔ isKept τ lam S x := by
  classical
  unfold keepFinset
  simp

lemma isKept_pos {τ : ℕ} {lam : (X → ℕ) → X → ℝ} {S : X → ℕ} {x : X}
    (h : isKept τ lam S x) : 0 < S x := h.1

lemma isKept_bound {τ : ℕ} {lam : (X → ℕ) → X → ℝ} {S : X → ℕ} {x : X}
    (h : isKept τ lam S x) : 1 ≤ capv lam S x * (q : ℝ) ^ τ := h.2

lemma capv_pos_of_kept {τ : ℕ} {lam : (X → ℕ) → X → ℝ} {S : X → ℕ} {x : X}
    (h : isKept τ lam S x) : 0 < capv lam S x := by
  have hb : 1 ≤ capv lam S x * (q : ℝ) ^ τ := isKept_bound h
  have hq : 0 < (q : ℝ) ^ τ := Pre.q_real_pow_pos τ
  have hv : capv lam S x ≥ (1 : ℝ) / (q : ℝ) ^ τ := by
    exact (div_le_iff₀ hq).2 hb
  have hpos : 0 < (1 : ℝ) / (q : ℝ) ^ τ := by positivity
  linarith

lemma lvx_eq_of_kept {τ : ℕ} {lam : (X → ℕ) → X → ℝ} {S : X → ℕ} {x : X}
    (h : isKept τ lam S x) : lvx τ lam S x = Pre.qlev τ (capv lam S x) := by
  classical
  unfold lvx
  simp [h]

lemma lvx_zero_of_not_kept {τ : ℕ} {lam : (X → ℕ) → X → ℝ} {S : X → ℕ} {x : X}
    (h : ¬ isKept τ lam S x) : lvx τ lam S x = 0 := by
  classical
  unfold lvx
  simp [h]

lemma lvx_le_tau_of_kept {τ : ℕ} {lam : (X → ℕ) → X → ℝ} {S : X → ℕ} {x : X}
    (h : isKept τ lam S x) : lvx τ lam S x ≤ τ := by
  rw [lvx_eq_of_kept h]
  exact Pre.qlev_le_bound (isKept_bound h)

lemma lvx_le_tau (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (x : X) :
    lvx τ lam S x ≤ τ := by
  by_cases h : isKept τ lam S x
  · exact lvx_le_tau_of_kept h
  · rw [lvx_zero_of_not_kept h]
    exact Nat.zero_le τ

lemma wlev_lvx_le_capv {τ : ℕ} {lam : (X → ℕ) → X → ℝ} {S : X → ℕ} {x : X}
    (h : isKept τ lam S x) : wlev (lvx τ lam S x) ≤ capv lam S x := by
  rw [lvx_eq_of_kept h]
  exact Pre.qlev_wlev_le (m := τ) (capv_pos_of_kept h) (isKept_bound h)

lemma capv_div_q_le_wlev_lvx {τ : ℕ} {lam : (X → ℕ) → X → ℝ} {S : X → ℕ} {x : X}
    (h : isKept τ lam S x) : capv lam S x / (q : ℝ) ≤ wlev (lvx τ lam S x) := by
  rw [lvx_eq_of_kept h]
  exact Pre.qlev_wlev_ge (m := τ) (capv_pos_of_kept h) (capv_le_one lam S x) (isKept_bound h)

/-- unkept positive coordinates have tiny capped weight -/
lemma capv_lt_wlev_of_not_kept {τ : ℕ} {lam : (X → ℕ) → X → ℝ} {S : X → ℕ} {x : X}
    (hx : 0 < S x) (hnot : ¬ isKept τ lam S x) : capv lam S x < wlev τ := by
  have hlt : capv lam S x * (q : ℝ) ^ τ < 1 := lt_of_not_ge (by
    intro hb
    exact hnot ⟨hx, hb⟩)
  have hqpos : 0 < (q : ℝ) ^ τ := Pre.q_real_pow_pos τ
  have hv : capv lam S x < (1 : ℝ) / (q : ℝ) ^ τ := by
    exact (lt_div_iff₀ hqpos).2 hlt
  simpa [wlev] using hv

noncomputable def keptCapSum (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) : ℝ :=
  ∑ x ∈ keepFinset τ lam S, (S x : ℝ) * capv lam S x

/-- kept level-weight (Σ multiplicity · wlev(level)) -/
noncomputable def keptWgt (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) : ℝ :=
  ∑ x ∈ keepFinset τ lam S, (S x : ℝ) * wlev (lvx τ lam S x)

/-- dropped coordinates sum -/
noncomputable def dropSum (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) : ℝ :=
  ∑ x ∈ (Finset.univ : Finset X).filter (fun x => ¬ isKept τ lam S x), (S x : ℝ) * capv lam S x

/-! ### cap and drop (multiset multiplicities) -/

/-- (∑ S x · capv x) ≥ 1 whenever (∑ S x · lam x) ≥ 1 and all lam ≥ 0 -/
lemma mwtot_cap_ge (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (hnon : ∀ x : X, 0 ≤ lam S x)
    (hge : 1 ≤ mwtot lam S) :
    1 ≤ ∑ x : X, (S x : ℝ) * capv lam S x := by
  classical
  by_cases hbig : ∃ x, 0 < S x ∧ 1 ≤ lam S x
  · rcases hbig with ⟨x0, hx0, hlam0⟩
    have hterm : 1 ≤ (S x0 : ℝ) * capv lam S x0 := by
      have hmin : capv lam S x0 = 1 := by
        unfold capv
        exact min_eq_right hlam0
      rw [hmin]
      have hS1 : (1 : ℝ) ≤ (S x0 : ℝ) := by exact_mod_cast hx0
      nlinarith
    have hcap_total : ∑ x : X, (S x : ℝ) * capv lam S x ≥ (S x0 : ℝ) * capv lam S x0 := by
      have hs := sum_univ_singleton_add (fun x => (S x : ℝ) * capv lam S x) x0
      rw [hs]
      have hpos : 0 ≤ ∑ x ∈ (Finset.univ.erase x0), (S x : ℝ) * capv lam S x := by
        exact Finset.sum_nonneg (by
          intro x hx
          exact mul_nonneg (by exact_mod_cast (Nat.zero_le (S x))) (capv_nonneg (hnon x)))
      linarith
    exact le_trans hterm hcap_total
  · have hsmall : ∀ x, 0 < S x → lam S x < 1 := by
      intro x hx
      exact lt_of_not_ge (by intro h; exact hbig ⟨x, hx, h⟩)
    have heq : (∑ x : X, (S x : ℝ) * capv lam S x) = mwtot lam S := by
      unfold mwtot
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hSx : S x = 0
      · simp [hSx, capv]
      · have hl : lam S x < 1 := hsmall x (Nat.pos_of_ne_zero hSx)
        have hmin : capv lam S x = lam S x := by unfold capv; exact min_eq_left (le_of_lt hl)
        rw [hmin]
    rw [heq]
    exact hge

/-- total capped weight splits into kept + dropped -/
lemma capv_sum_split (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) :
    (∑ x : X, (S x : ℝ) * capv lam S x) = keptCapSum τ lam S + dropSum τ lam S := by
  classical
  unfold keptCapSum dropSum keepFinset
  exact (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset X)
    (fun x => isKept τ lam S x) (fun x => (S x : ℝ) * capv lam S x)).symm

/-- dropped-coordinate term bound -/
lemma drop_term_le (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) {x : X}
    (hx : x ∈ (Finset.univ : Finset X).filter (fun x => ¬ isKept τ lam S x)) :
    (S x : ℝ) * capv lam S x ≤ (S x : ℝ) * wlev τ := by
  classical
  by_cases hS : S x = 0
  · simp [hS]
  · have hSpos : 0 < S x := Nat.pos_of_ne_zero hS
    have hn : ¬ isKept τ lam S x := (Finset.mem_filter.mp hx).2
    have hcv : capv lam S x ≤ wlev τ := le_of_lt (capv_lt_wlev_of_not_kept hSpos hn)
    exact mul_le_mul_of_nonneg_left hcv (by exact_mod_cast (Nat.zero_le (S x)))

/-- drop loss ≤ (sizeM S)·wlev τ ≤ (Bnd)·wlev τ -/
lemma drop_sum_le (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (Bnd : ℕ)
    (hsize : sizeM S ≤ Bnd) : dropSum τ lam S ≤ (Bnd : ℝ) * wlev τ := by
  classical
  unfold dropSum
  have hsumle : (∑ x ∈ (Finset.univ : Finset X).filter (fun x => ¬ isKept τ lam S x),
      (S x : ℝ) * capv lam S x) ≤
      ∑ x ∈ (Finset.univ : Finset X).filter (fun x => ¬ isKept τ lam S x),
        (S x : ℝ) * wlev τ := by
    exact Finset.sum_le_sum (fun x hx => drop_term_le τ lam S hx)
  let A : Finset X := (Finset.univ : Finset X).filter (fun x => ¬ isKept τ lam S x)
  calc
    (∑ x ∈ A, (S x : ℝ) * capv lam S x) ≤ ∑ x ∈ A, (S x : ℝ) * wlev τ := by
      simpa [A] using hsumle
    _ = (∑ x ∈ A, (S x : ℝ)) * wlev τ := by
      rw [Finset.sum_mul]
    _ ≤ (sizeM S : ℝ) * wlev τ := by
      have hle : (∑ x ∈ A, (S x : ℝ)) ≤ (sizeM S : ℝ) := by
        have hle' : (∑ x ∈ A, (S x : ℝ)) ≤ ∑ x : X, (S x : ℝ) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (s := A) (t := (Finset.univ : Finset X)) (f := fun x => (S x : ℝ))
            (by intro x hx; exact Finset.mem_univ x)
            (by intro x hx hnx; positivity)
        calc
          (∑ x ∈ A, (S x : ℝ)) ≤ ∑ x : X, (S x : ℝ) := hle'
          _ = (sizeM S : ℝ) := by
            unfold sizeM
            rw [Nat.cast_sum]
      exact mul_le_mul_of_nonneg_right hle (wlev_nonneg τ)
    _ ≤ (Bnd : ℝ) * wlev τ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) (wlev_nonneg τ)

/-- kept capped weight ≥ 1 − q⁻¹ (budget 1/q via (Bnd)·wlev τ ≤ q⁻¹) -/
lemma keptCap_ge (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (Bnd : ℕ)
    (hSnon : ∀ x : X, 0 ≤ lam S x) (hSge : 1 ≤ mwtot lam S)
    (hsize : sizeM S ≤ Bnd) (hτ : (Bnd : ℝ) * wlev τ ≤ (q : ℝ)⁻¹) :
    (1 : ℝ) - (q : ℝ)⁻¹ ≤ keptCapSum τ lam S := by
  classical
  have hcap : 1 ≤ ∑ x : X, (S x : ℝ) * capv lam S x := mwtot_cap_ge lam S hSnon hSge
  have hdrop : dropSum τ lam S ≤ (Bnd : ℝ) * wlev τ := drop_sum_le τ lam S Bnd hsize
  have hsplit := capv_sum_split τ lam S
  have hkeep : (1 : ℝ) - (Bnd : ℝ) * wlev τ ≤ keptCapSum τ lam S := by
    rw [hsplit] at hcap
    have hnonnegdrop : 0 ≤ dropSum τ lam S := by
      unfold dropSum
      exact Finset.sum_nonneg (by
        intro x hx
        exact mul_nonneg (by exact_mod_cast (Nat.zero_le (S x))) (capv_nonneg (hSnon x)))
    nlinarith
  have hbnd : (1 : ℝ) - (q : ℝ)⁻¹ ≤ (1 : ℝ) - (Bnd : ℝ) * wlev τ := by
    have hle : (Bnd : ℝ) * wlev τ ≤ (q : ℝ)⁻¹ := hτ
    linarith
  exact le_trans hbnd hkeep

/-! ### class (level) sums and quantization -/

/-- (Σ_{x ∈ A.filter (g = j)} c x) · w j summed over j = Σ_{x ∈ A} c x · w (g x) -/
lemma sum_fiber_mul (A : Finset X) (g : X → ℕ) (c : X → ℝ) (w : ℕ → ℝ) (m : ℕ)
    (hm : ∀ x ∈ A, g x ≤ m) :
    (∑ j ∈ Finset.range (m + 1), (∑ x ∈ A.filter (fun x => g x = j), c x) * w j)
      = ∑ x ∈ A, c x * w (g x) := by
  classical
  have hsplit : (∑ j ∈ Finset.range (m + 1), (∑ x ∈ A.filter (fun x => g x = j), c x) * w j)
      = ∑ j ∈ Finset.range (m + 1),
          (A.filter (fun x => g x = j)).sum (fun x => c x * w j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_mul]
  have hwj : (∑ j ∈ Finset.range (m + 1),
      (A.filter (fun x => g x = j)).sum (fun x => c x * w j))
      = (∑ j ∈ Finset.range (m + 1),
          (A.filter (fun x => g x = j)).sum (fun x => c x * w (g x))) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro x hx
    have hgj : g x = j := (Finset.mem_filter.mp hx).2
    rw [hgj]
  have hdisj : ((Finset.range (m + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun j => A.filter (fun x => g x = j)) := by
    intro j hj k hk hjk
    change Disjoint (A.filter (fun x => g x = j)) (A.filter (fun x => g x = k))
    rw [Finset.disjoint_left]
    intro x hx hik
    have hgj : g x = j := (Finset.mem_filter.mp hx).2
    have hgk : g x = k := (Finset.mem_filter.mp hik).2
    exact hjk (by rw [← hgj, hgk])
  have hunion : (Finset.range (m + 1)).biUnion (fun j => A.filter (fun x => g x = j)) = A := by
    ext x
    constructor
    · intro hx
      rcases (Finset.mem_biUnion.mp hx) with ⟨j, hj, hxj⟩
      exact (Finset.mem_filter.mp hxj).1
    · intro hx
      refine (Finset.mem_biUnion.mpr) ⟨g x, ?_, ?_⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hm x hx))
      · exact Finset.mem_filter.mpr ⟨hx, rfl⟩
  calc
    (∑ j ∈ Finset.range (m + 1), (∑ x ∈ A.filter (fun x => g x = j), c x) * w j)
        = ∑ j ∈ Finset.range (m + 1),
            (A.filter (fun x => g x = j)).sum (fun x => c x * w j) := hsplit
    _ = ∑ j ∈ Finset.range (m + 1),
        (A.filter (fun x => g x = j)).sum (fun x => c x * w (g x)) := hwj
    _ = ∑ x ∈ (Finset.range (m + 1)).biUnion (fun j => A.filter (fun x => g x = j)), c x * w (g x) := by
        rw [Finset.sum_biUnion hdisj]
    _ = ∑ x ∈ A, c x * w (g x) := by rw [hunion]

/-- class multiplicity cast -/
lemma cS_cast (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) :
    (cS τ lam S j : ℝ) = ∑ x ∈ (keepFinset τ lam S).filter (fun x => lvx τ lam S x = j), (S x : ℝ) := by
  classical
  unfold cS
  rw [Nat.cast_sum]

/-- sum over levels of class weight = kept level weight -/
lemma classSum_eq (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) :
    (∑ j ∈ Finset.range (τ + 1), (cS τ lam S j : ℝ) * wlev j) = keptWgt τ lam S := by
  classical
  have hm : ∀ x ∈ keepFinset τ lam S, lvx τ lam S x ≤ τ := by
    intro x hx
    exact lvx_le_tau_of_kept ((mem_keepFinset_iff τ lam S x).1 hx)
  have hfib := sum_fiber_mul (keepFinset τ lam S) (fun x => lvx τ lam S x)
    (fun x => (S x : ℝ)) wlev τ hm
  calc
    (∑ j ∈ Finset.range (τ + 1), (cS τ lam S j : ℝ) * wlev j)
        = ∑ j ∈ Finset.range (τ + 1),
            (∑ x ∈ (keepFinset τ lam S).filter (fun x => lvx τ lam S x = j), (S x : ℝ)) * wlev j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [cS_cast]
    _ = ∑ x ∈ keepFinset τ lam S, (S x : ℝ) * wlev (lvx τ lam S x) := hfib
    _ = keptWgt τ lam S := rfl

/-- kept level weight ≥ (1 − q⁻¹)·q⁻¹ -/
lemma keptWgt_ge (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (Bnd : ℕ)
    (hSnon : ∀ x : X, 0 ≤ lam S x) (hSge : 1 ≤ mwtot lam S)
    (hsize : sizeM S ≤ Bnd) (hτ : (Bnd : ℝ) * wlev τ ≤ (q : ℝ)⁻¹) :
    ((1 : ℝ) - (1 : ℝ) / (q : ℝ)) / (q : ℝ) ≤ keptWgt τ lam S := by
  classical
  have hcap : (1 : ℝ) - (q : ℝ)⁻¹ ≤ keptCapSum τ lam S := keptCap_ge τ lam S Bnd hSnon hSge hsize hτ
  have hqpos : (0 : ℝ) < (q : ℝ) := by norm_num [q]
  have hleterm : ∀ x ∈ keepFinset τ lam S,
      (S x : ℝ) * capv lam S x ≤ (q : ℝ) * ((S x : ℝ) * wlev (lvx τ lam S x)) := by
    intro x hx
    have hk : isKept τ lam S x := (mem_keepFinset_iff τ lam S x).1 hx
    have hge := capv_div_q_le_wlev_lvx (τ := τ) (lam := lam) (S := S) hk
    have hc : capv lam S x ≤ (q : ℝ) * wlev (lvx τ lam S x) := by
      rw [mul_comm]
      exact (div_le_iff₀ hqpos).1 hge
    calc
      (S x : ℝ) * capv lam S x ≤ (S x : ℝ) * ((q : ℝ) * wlev (lvx τ lam S x)) := by
        exact mul_le_mul_of_nonneg_left hc (by exact_mod_cast (Nat.zero_le (S x)))
      _ = (q : ℝ) * ((S x : ℝ) * wlev (lvx τ lam S x)) := by ring
  have hel : keptCapSum τ lam S ≤ (q : ℝ) * keptWgt τ lam S := by
    unfold keptCapSum keptWgt
    calc
      (∑ x ∈ keepFinset τ lam S, (S x : ℝ) * capv lam S x)
          ≤ ∑ x ∈ keepFinset τ lam S, (q : ℝ) * ((S x : ℝ) * wlev (lvx τ lam S x)) := by
            exact Finset.sum_le_sum (fun x hx => hleterm x hx)
      _ = (q : ℝ) * ∑ x ∈ keepFinset τ lam S, (S x : ℝ) * wlev (lvx τ lam S x) := by
          rw [Finset.mul_sum]
  have hqinv : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
  have hmain : ((1 : ℝ) - (q : ℝ)⁻¹) * (q : ℝ)⁻¹ ≤ keptWgt τ lam S := by
    calc
      ((1 : ℝ) - (q : ℝ)⁻¹) * (q : ℝ)⁻¹ ≤ keptCapSum τ lam S * (q : ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hcap hqinv
      _ ≤ keptWgt τ lam S := by
        calc
          keptCapSum τ lam S * (q : ℝ)⁻¹ ≤ ((q : ℝ) * keptWgt τ lam S) * (q : ℝ)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hel hqinv
          _ = keptWgt τ lam S := by
            field_simp [q_ne_zero]
  simpa [div_eq_mul_inv] using hmain

/-- class total weight ≥ (1 − q⁻¹)·q⁻¹ -/
lemma classSum_ge (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (Bnd : ℕ)
    (hSnon : ∀ x : X, 0 ≤ lam S x) (hSge : 1 ≤ mwtot lam S)
    (hsize : sizeM S ≤ Bnd) (hτ : (Bnd : ℝ) * wlev τ ≤ (q : ℝ)⁻¹) :
    ((1 : ℝ) - (1 : ℝ) / (q : ℝ)) / (q : ℝ) ≤
      ∑ j ∈ Finset.range (τ + 1), (cS τ lam S j : ℝ) * wlev j := by
  have hw := keptWgt_ge τ lam S Bnd hSnon hSge hsize hτ
  rw [classSum_eq]
  simpa [div_eq_mul_inv] using hw

/-- the drop-loss constant -/
noncomputable def D2m : ℝ := (200 : ℝ) * wlev 5 + (20 : ℝ) / ((q : ℝ) ^ 4)

/-- dropped levels j ≤ 4 contribute nothing -/
lemma wL_zero_of_notkeep_le4 (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) {j : ℕ}
    (hnot : ¬ keepL τ lam S j) (hj : j ≤ 4) : wL τ lam S j = 0 := by
  classical
  have hne : Pre.needExp j = 0 := Pre.needExp_zero_of_le4 hj
  have hc : cS τ lam S j = 0 := by
    by_contra hc0
    have h1 : 1 ≤ cS τ lam S j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hc0)
    have hq : (q : ℕ) ^ Pre.needExp j = 1 := by rw [hne]; norm_num
    have hk : keepL τ lam S j := by
      unfold keepL Pre.keptLvlN
      rw [hq]
      exact h1
    exact hnot hk
  unfold wL
  rw [hc]
  simp

/-- sL = 0 when not kept -/
lemma sL_zero_of_notkeep (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) {j : ℕ}
    (hnot : ¬ keepL τ lam S j) : sL τ lam S j = 0 := by
  classical
  unfold sL
  unfold keepL at hnot
  exact Pre.keepNum_eq_zero hnot

/-- drop loss (whole dropped levels) ≤ D2m -/
lemma dropLoss_le (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) :
    (∑ j ∈ (Finset.range (τ + 1)).filter (fun j => ¬ keepL τ lam S j),
        wL τ lam S j) ≤ D2m := by
  classical
  let rng : Finset ℕ := Finset.range (τ + 1)
  let notF : Finset ℕ := rng.filter (fun j => ¬ keepL τ lam S j)
  let high : Finset ℕ := rng.filter (fun j => 5 ≤ j)
  let highNot : Finset ℕ := rng.filter (fun j => 5 ≤ j ∧ ¬ keepL τ lam S j)
  have hD : (∑ j ∈ notF, wL τ lam S j) = ∑ j ∈ highNot, wL τ lam S j := by
    calc
      (∑ j ∈ notF, wL τ lam S j) = ∑ j ∈ notF.filter (fun j => 5 ≤ j), wL τ lam S j := by
        symm
        apply Finset.sum_subset
        · intro j hj
          exact (Finset.mem_filter.mp hj).1
        · intro j hj hn
          have hnot : ¬ keepL τ lam S j := (Finset.mem_filter.mp hj).2
          have hn5 : ¬ 5 ≤ j := by
            intro h5
            apply hn
            exact Finset.mem_filter.mpr ⟨hj, h5⟩
          exact wL_zero_of_notkeep_le4 τ lam S hnot (by omega)
      _ = ∑ j ∈ highNot, wL τ lam S j := by
        have hset : notF.filter (fun j => 5 ≤ j) = highNot := by
          ext j
          simp [notF, highNot, rng]
          tauto
        rw [hset]
  have hterm : ∀ j ∈ highNot,
      wL τ lam S j ≤ (100 : ℝ) * Sys.legalLower j * wlev j := by
    intro j hj
    have hnot : ¬ keepL τ lam S j := (Finset.mem_filter.mp hj).2.2
    have hle' : ¬ (q : ℕ) ^ Pre.needExp j ≤ cS τ lam S j := by
      simpa [keepL, Pre.keptLvlN] using hnot
    have hc : (cS τ lam S j : ℕ) ≤ (q : ℕ) ^ Pre.needExp j :=
      Nat.le_of_lt (lt_of_not_ge hle')
    have h1 : (cS τ lam S j : ℝ) * wlev j ≤ ((q : ℕ) ^ Pre.needExp j : ℝ) * wlev j := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (wlev_nonneg j)
    have h2 : ((q : ℕ) ^ Pre.needExp j : ℝ) * wlev j ≤ (100 : ℝ) * Sys.legalLower j * wlev j := by
      have hq := Pre.needExp_qpow_le j
      exact mul_le_mul_of_nonneg_right hq (wlev_nonneg j)
    unfold wL
    exact le_trans h1 h2
  have hD2 : (∑ j ∈ highNot, wL τ lam S j) ≤ ∑ j ∈ highNot, (100 : ℝ) * Sys.legalLower j * wlev j := by
    exact Finset.sum_le_sum (fun j hj => hterm j hj)
  have hsubset : highNot ⊆ high := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2.1⟩
  have hD3 : (∑ j ∈ highNot, (100 : ℝ) * Sys.legalLower j * wlev j) ≤
      ∑ j ∈ high, (100 : ℝ) * Sys.legalLower j * wlev j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro j hj hx
    exact mul_nonneg (mul_nonneg (by norm_num) (Pre.legalLower_nonneg j)) (wlev_nonneg j)
  have hD4 : (∑ j ∈ high, (100 : ℝ) * Sys.legalLower j * wlev j) ≤
      ∑ j ∈ Finset.Icc 5 τ, (100 : ℝ) * Sys.legalLower j * wlev j := by
    have hEq : high = Finset.Icc 5 τ := by
      ext j
      simp [high, rng, Finset.mem_Icc, Nat.succ_le_iff]
      tauto
    rw [hEq]
  have hD5 : (∑ j ∈ Finset.Icc 5 τ, (100 : ℝ) * Sys.legalLower j * wlev j) ≤ D2m := by
    let inv : ℕ → ℝ := fun j => (1 : ℝ) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2))
    have hterm0 : ∀ j ∈ Finset.Icc 5 τ,
        (100 : ℝ) * Sys.legalLower j * wlev j ≤ (100 : ℝ) * wlev j + (100 : ℝ) * inv j := by
      intro j hj
      have h0 := Pre.legalLower_mul_wlev_le j
      have hml : (100 : ℝ) * (Sys.legalLower j * wlev j) ≤
          (100 : ℝ) * (wlev j + (1 : ℝ) / (((q : ℝ) ^ 4) * ((j + 1 : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left h0 (by norm_num)
      have hL : (100 : ℝ) * Sys.legalLower j * wlev j = (100 : ℝ) * (Sys.legalLower j * wlev j) := by ring
      have hR : (100 : ℝ) * wlev j + (100 : ℝ) * inv j =
          (100 : ℝ) * (wlev j + inv j) := by ring
      rw [hL, hR]
      simpa [inv] using hml
    have hinv1 : ∀ j ∈ Finset.Icc 5 τ,
        inv j = (1 : ℝ) / ((q : ℝ) ^ 4) * (1 / ((j + 1 : ℝ) ^ 2)) := by
      intro j hj
      have hq4 : (q : ℝ) ^ 4 ≠ 0 := Pre.q_real_pow_ne_zero 4
      have hsq : ((j + 1 : ℝ) ^ 2) ≠ 0 := by positivity
      unfold inv
      field_simp [hq4, hsq]
    calc
      (∑ j ∈ Finset.Icc 5 τ, (100 : ℝ) * Sys.legalLower j * wlev j)
          ≤ ∑ j ∈ Finset.Icc 5 τ, ((100 : ℝ) * wlev j + (100 : ℝ) * inv j) := by
            exact Finset.sum_le_sum (fun j hj => hterm0 j hj)
      _ = (100 : ℝ) * (∑ j ∈ Finset.Icc 5 τ, wlev j) +
          (100 : ℝ) * (∑ j ∈ Finset.Icc 5 τ, inv j) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [← Finset.mul_sum]
            · rw [← Finset.mul_sum]
      _ ≤ (100 : ℝ) * (2 * wlev 5) + (100 : ℝ) * ((1 : ℝ) / ((q : ℝ) ^ 4) * (1 / 5)) := by
            have h1 := Pre.sum_wlev_high_le τ
            have h1m : (100 : ℝ) * (∑ j ∈ Finset.Icc 5 τ, wlev j) ≤ (100 : ℝ) * (2 * wlev 5) :=
              mul_le_mul_of_nonneg_left h1 (by norm_num)
            have h2sum : (∑ j ∈ Finset.Icc 5 τ, inv j) ≤ (1 : ℝ) / ((q : ℝ) ^ 4) * (1 / 5) := by
              calc
                (∑ j ∈ Finset.Icc 5 τ, inv j)
                    = ∑ j ∈ Finset.Icc 5 τ, (1 : ℝ) / ((q : ℝ) ^ 4) * (1 / ((j + 1 : ℝ) ^ 2)) := by
                      exact Finset.sum_congr rfl (fun j hj => hinv1 j hj)
                _ = (1 : ℝ) / ((q : ℝ) ^ 4) * (∑ j ∈ Finset.Icc 5 τ, 1 / ((j + 1 : ℝ) ^ 2)) := by
                      rw [Finset.mul_sum]
                _ ≤ (1 : ℝ) / ((q : ℝ) ^ 4) * (1 / 5) := by
                      have hs := Pre.sum_inv_sq_high_le τ
                      exact mul_le_mul_of_nonneg_left hs (by positivity)
            have h2m : (100 : ℝ) * (∑ j ∈ Finset.Icc 5 τ, inv j) ≤
                (100 : ℝ) * ((1 : ℝ) / ((q : ℝ) ^ 4) * (1 / 5)) :=
              mul_le_mul_of_nonneg_left h2sum (by norm_num)
            nlinarith
      _ = D2m := by
            unfold D2m
            norm_num [wlev, q]
  calc
    (∑ j ∈ (Finset.range (τ + 1)).filter (fun j => ¬ keepL τ lam S j), wL τ lam S j)
        = ∑ j ∈ notF, wL τ lam S j := rfl
    _ = ∑ j ∈ highNot, wL τ lam S j := hD
    _ ≤ ∑ j ∈ highNot, (100 : ℝ) * Sys.legalLower j * wlev j := hD2
    _ ≤ ∑ j ∈ high, (100 : ℝ) * Sys.legalLower j * wlev j := hD3
    _ ≤ ∑ j ∈ Finset.Icc 5 τ, (100 : ℝ) * Sys.legalLower j * wlev j := hD4
    _ ≤ D2m := hD5

/-- main per-S weight bound: Σ_j (sL j)·wlev j ≥ 10^{-8} -/
lemma perS_weight (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (Bnd : ℕ)
    (hSnon : ∀ x : X, 0 ≤ lam S x) (hSge : 1 ≤ mwtot lam S)
    (hsize : sizeM S ≤ Bnd) (hτ : (Bnd : ℝ) * wlev τ ≤ (q : ℝ)⁻¹) :
    ((10 : ℝ) ^ 8)⁻¹ ≤
      ∑ j ∈ Finset.range (τ + 1), (sL τ lam S j : ℝ) * wlev j := by
  classical
  let keptR : Finset ℕ := (Finset.range (τ + 1)).filter (fun j => keepL τ lam S j)
  have hq : (q : ℝ) ≠ 0 := q_ne_zero
  have hqinv : (0 : ℝ) ≤ (q : ℝ)⁻¹ := by positivity
  have hqinvpos : (0 : ℝ) < (q : ℝ)⁻¹ := by positivity
  have hT : ((1 : ℝ) - (1 : ℝ) / (q : ℝ)) / (q : ℝ) ≤
      ∑ j ∈ Finset.range (τ + 1), (cS τ lam S j : ℝ) * wlev j :=
    classSum_ge τ lam S Bnd hSnon hSge hsize hτ
  have hKwSk : (∑ j ∈ Finset.range (τ + 1), (sL τ lam S j : ℝ) * wlev j) =
      ∑ j ∈ keptR, (sL τ lam S j : ℝ) * wlev j := by
    have h1 : (∑ j ∈ Finset.range (τ + 1), (sL τ lam S j : ℝ) * wlev j)
        = ∑ j ∈ Finset.range (τ + 1),
            (if keepL τ lam S j then (sL τ lam S j : ℝ) * wlev j else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hk : keepL τ lam S j
      · simp [hk]
      · have hs : sL τ lam S j = 0 := sL_zero_of_notkeep τ lam S hk
        simp [hs, hk]
    calc
      (∑ j ∈ Finset.range (τ + 1), (sL τ lam S j : ℝ) * wlev j)
          = ∑ j ∈ Finset.range (τ + 1),
              (if keepL τ lam S j then (sL τ lam S j : ℝ) * wlev j else 0) := h1
      _ = ∑ j ∈ keptR, (sL τ lam S j : ℝ) * wlev j := by
          rw [Finset.sum_filter]
  have hlevel : (∑ j ∈ keptR, min ((cS τ lam S j : ℝ) * wlev j) 1 * (q : ℝ)⁻¹) ≤
      ∑ j ∈ keptR, (sL τ lam S j : ℝ) * wlev j := by
    apply Finset.sum_le_sum
    intro j hj
    have hk : keepL τ lam S j := (Finset.mem_filter.mp hj).2
    have hw := Pre.keepNum_weight (j := j) (c := cS τ lam S j) (by simpa [keepL, Pre.keptLvlN] using hk)
    have hw' : min ((cS τ lam S j : ℝ) * wlev j) 1 * (q : ℝ)⁻¹ ≤ (sL τ lam S j : ℝ) * wlev j := by
      have hd : min ((cS τ lam S j : ℝ) * wlev j) 1 / (q : ℝ) * (q : ℝ) = min ((cS τ lam S j : ℝ) * wlev j) 1 := by
        field_simp [hq]
      simpa [sL, div_eq_mul_inv] using hw
    exact hw'
  have hMk : (∑ j ∈ keptR, min ((cS τ lam S j : ℝ) * wlev j) 1) * (q : ℝ)⁻¹ ≤
      ∑ j ∈ keptR, (sL τ lam S j : ℝ) * wlev j := by
    rw [Finset.sum_mul]
    exact hlevel
  have hmin1 : min (∑ j ∈ keptR, (cS τ lam S j : ℝ) * wlev j) 1 ≤
      ∑ j ∈ keptR, min ((cS τ lam S j : ℝ) * wlev j) 1 := by
    apply Pre.sum_min_one_ge_min_sum (keptR) (fun j => (cS τ lam S j : ℝ) * wlev j)
    intro j hj
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le (cS τ lam S j))) (wlev_nonneg j)
  have hminWk : min (∑ j ∈ keptR, (cS τ lam S j : ℝ) * wlev j) 1 * (q : ℝ)⁻¹ ≤
      ∑ j ∈ keptR, (sL τ lam S j : ℝ) * wlev j := by
    calc
      min (∑ j ∈ keptR, (cS τ lam S j : ℝ) * wlev j) 1 * (q : ℝ)⁻¹
          ≤ (∑ j ∈ keptR, min ((cS τ lam S j : ℝ) * wlev j) 1) * (q : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hmin1 hqinv
      _ ≤ ∑ j ∈ keptR, (sL τ lam S j : ℝ) * wlev j := hMk
  let D : ℝ := ∑ j ∈ (Finset.range (τ + 1)).filter (fun j => ¬ keepL τ lam S j),
      (cS τ lam S j : ℝ) * wlev j
  have hpart : (∑ j ∈ keptR, (cS τ lam S j : ℝ) * wlev j) + D =
      ∑ j ∈ Finset.range (τ + 1), (cS τ lam S j : ℝ) * wlev j := by
    have hp := Finset.sum_filter_add_sum_filter_not (Finset.range (τ + 1))
      (fun j => keepL τ lam S j) (fun j => (cS τ lam S j : ℝ) * wlev j)
    unfold keptR D
    simpa using hp
  have hDle : D ≤ D2m := by
    unfold D
    simpa [wL] using (dropLoss_le τ lam S)
  have hWk : ((1 : ℝ) - (1 : ℝ) / (q : ℝ)) / (q : ℝ) - D2m ≤
      ∑ j ∈ keptR, (cS τ lam S j : ℝ) * wlev j := by
    have hWkeq : (∑ j ∈ keptR, (cS τ lam S j : ℝ) * wlev j) =
        (∑ j ∈ Finset.range (τ + 1), (cS τ lam S j : ℝ) * wlev j) - D := by
      rw [← hpart]
      ring
    rw [hWkeq]
    nlinarith [hT, hDle]
  have hminBig : ((10 : ℝ) ^ 6)⁻¹ ≤ min (∑ j ∈ keptR, (cS τ lam S j : ℝ) * wlev j) 1 := by
    have hnum : ((10 : ℝ) ^ 6)⁻¹ ≤ ((1 : ℝ) - (1 : ℝ) / (q : ℝ)) / (q : ℝ) - D2m := by
      unfold D2m
      norm_num [wlev, q]
    have hWk6 : ((10 : ℝ) ^ 6)⁻¹ ≤ ∑ j ∈ keptR, (cS τ lam S j : ℝ) * wlev j :=
      le_trans hnum hWk
    exact le_min hWk6 (by norm_num)
  have hconcl : ((10 : ℝ) ^ 8)⁻¹ ≤ (∑ j ∈ keptR, (sL τ lam S j : ℝ) * wlev j) := by
    calc
      ((10 : ℝ) ^ 8)⁻¹ ≤ ((10 : ℝ) ^ 6)⁻¹ * (q : ℝ)⁻¹ := by norm_num [q]
      _ ≤ min (∑ j ∈ keptR, (cS τ lam S j : ℝ) * wlev j) 1 * (q : ℝ)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hminBig hqinv
      _ ≤ ∑ j ∈ keptR, (sL τ lam S j : ℝ) * wlev j := hminWk
  rw [hKwSk]
  exact hconcl

/-- sL entries are legal on levels ≤ τ -/
lemma perS_legal (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) :
    ∀ j, j ≤ τ → Sys.LegalEntry (sL τ lam S j) j := by
  intro j hj
  unfold sL
  exact Pre.LegalEntry_keepNum (j := j) (c := cS τ lam S j)

/-! ### trimmed member of one S -/

/-- sub-multiset of any desired size -/
lemma exists_submultiset_size (m : X → ℕ) (k : ℕ) (hk : k ≤ sizeM m) :
    ∃ m' : X → ℕ, subM m' m ∧ sizeM m' = k := by
  classical
  revert m
  induction k with
  | zero =>
      intro m hk
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro x; exact Nat.zero_le (m x)
      · unfold sizeM; simp
  | succ k ih =>
      intro m hk
      have hmpos : 0 < sizeM m := by omega
      rcases (sizeM_pos_iff.mp hmpos) with ⟨x, hx⟩
      let m1 : X → ℕ := eraseOne m x
      have hsub1 : subM m1 m := subM_eraseOne m x
      have hs1 : sizeM m1 + 1 = sizeM m := sizeM_eraseOne_add m x hx
      have hk1 : k ≤ sizeM m1 := by omega
      rcases (ih m1 hk1) with ⟨m2, hsub2, hs2⟩
      let m' : X → ℕ := fun y => m2 y + if y = x then 1 else 0
      refine ⟨m', ?_, ?_⟩
      · intro y
        by_cases hy : y = x
        · subst y
          have hle2 := hsub2 x
          have hm1x : m1 x = m x - 1 := by simp [m1, eraseOne]
          rw [hm1x] at hle2
          have hx1 : 1 ≤ m x := hx
          unfold m'
          simp
          omega
        · have hle2 := hsub2 y
          have hm1y : m1 y = m y := by simp [m1, eraseOne_other m (x := x) hy]
          rw [hm1y] at hle2
          unfold m'
          simp [hy]
          exact hle2
      · have hs : sizeM m' = k + 1 := by
          have hsum2 : (∑ y : X, m2 y) = k := by
            simpa [sizeM] using hs2
          unfold m' sizeM
          rw [Finset.sum_add_distrib]
          have hid : (∑ y : X, (if y = x then (1 : ℕ) else 0)) = 1 := by
            simp [Finset.sum_ite_eq']
          rw [hid, hsum2]
        exact hs

/-- class multiset pointwise ≤ S -/
lemma clsM_le_S (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) (x : X) :
    clsM τ lam S j x ≤ S x := by
  unfold clsM
  by_cases h : isKept τ lam S x ∧ lvx τ lam S x = j <;> simp [h]

/-- class multiset is zero outside its class -/
lemma clsM_zero_of_not_cls (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) (x : X)
    (h : ¬ (isKept τ lam S x ∧ lvx τ lam S x = j)) : clsM τ lam S j x = 0 := by
  unfold clsM
  simp [h]

/-- |clsM j| = cS j -/
lemma sizeM_clsM_eq_cS (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) :
    sizeM (clsM τ lam S j) = cS τ lam S j := by
  classical
  have hcls : sizeM (clsM τ lam S j)
      = ∑ x ∈ (Finset.univ : Finset X).filter (fun x => isKept τ lam S x ∧ lvx τ lam S x = j), S x := by
    unfold sizeM clsM
    rw [← Finset.sum_filter]
  have hc : cS τ lam S j
      = ∑ x ∈ (Finset.univ : Finset X).filter (fun x => isKept τ lam S x ∧ lvx τ lam S x = j), S x := by
    unfold cS keepFinset
    congr 1
    ext x
    simp [Finset.mem_filter, and_assoc, and_left_comm, and_comm]
  rw [hcls, hc]

/-- sL j ≤ |clsM j| -/
lemma sL_le_sizeM_clsM (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) :
    sL τ lam S j ≤ sizeM (clsM τ lam S j) := by
  have hle : sL τ lam S j ≤ cS τ lam S j := by
    unfold sL
    exact Pre.keepNum_le_card (j := j) (c := cS τ lam S j)
  calc
    sL τ lam S j ≤ cS τ lam S j := hle
    _ = sizeM (clsM τ lam S j) := (sizeM_clsM_eq_cS τ lam S j).symm

/-- the level-j kept piece of the trim of S -/
noncomputable def piece (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) : X → ℕ :=
  Classical.choose (exists_submultiset_size (clsM τ lam S j) (sL τ lam S j) (sL_le_sizeM_clsM τ lam S j))

lemma piece_spec (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) :
    subM (piece τ lam S j) (clsM τ lam S j) ∧ sizeM (piece τ lam S j) = sL τ lam S j := by
  classical
  unfold piece
  exact Classical.choose_spec (exists_submultiset_size (clsM τ lam S j) (sL τ lam S j)
    (sL_le_sizeM_clsM τ lam S j))

/-- trimmed member (as a function) -/
noncomputable def trimM (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) : X → ℕ :=
  fun x => piece τ lam S (lvx τ lam S x) x

/-- trim ≤ S pointwise -/
lemma trimM_le (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (x : X) :
    trimM τ lam S x ≤ S x := by
  classical
  unfold trimM
  exact le_trans ((piece_spec τ lam S (lvx τ lam S x)).1 x) (clsM_le_S τ lam S (lvx τ lam S x) x)

/-- trimmed member ⊆ S -/
lemma trimM_subM (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) : subM (trimM τ lam S) S := by
  intro x
  exact trimM_le τ lam S x

/-- unkept coordinates have no kept copies -/
lemma trimM_eq_zero_of_not_kept (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) {x : X}
    (h : ¬ isKept τ lam S x) : trimM τ lam S x = 0 := by
  classical
  unfold trimM
  have hle := (piece_spec τ lam S (lvx τ lam S x)).1 x
  have hc : clsM τ lam S (lvx τ lam S x) x = 0 := by
    apply clsM_zero_of_not_cls
    intro hcls
    exact h hcls.1
  omega

/-- kept copies at level j of the trim total sL j -/
lemma levelCount_eq_sL (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) (j : ℕ) :
    (∑ x : X, if lvx τ lam S x = j then trimM τ lam S x else 0) = sL τ lam S j := by
  classical
  have hterm : ∀ x, (if lvx τ lam S x = j then trimM τ lam S x else 0)
      = (if lvx τ lam S x = j then piece τ lam S j x else 0) := by
    intro x
    unfold trimM
    by_cases h : lvx τ lam S x = j
    · simp [h]
    · simp [h]
  calc
    (∑ x : X, if lvx τ lam S x = j then trimM τ lam S x else 0)
        = ∑ x : X, (if lvx τ lam S x = j then piece τ lam S j x else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hterm x
    _ = ∑ x : X, piece τ lam S j x := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : lvx τ lam S x = j
          · simp [h]
          · have hp0 : piece τ lam S j x = 0 := by
              have hle := (piece_spec τ lam S j).1 x
              have hc : clsM τ lam S j x = 0 := by
                apply clsM_zero_of_not_cls
                intro hcls
                exact h hcls.2
              omega
            simp [h, hp0]
    _ = sizeM (piece τ lam S j) := rfl
    _ = sL τ lam S j := (piece_spec τ lam S j).2

/-- domination: kept coordinates have wlev(level) ≤ lam -/
lemma trim_dom (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (S : X → ℕ) {x : X}
    (hx : 0 < trimM τ lam S x) : lam S x ≥ wlev (lvx τ lam S x) := by
  classical
  have hk : isKept τ lam S x := by
    by_contra hk
    have hz : trimM τ lam S x = 0 := trimM_eq_zero_of_not_kept τ lam S hk
    omega
  exact le_trans (wlev_lvx_le_capv hk) (capv_le_lam lam S x)

/-! ### System assembly -/

/-- chosen preimage of a trimmed member -/
noncomputable def preS (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (fam : Set (X → ℕ)) (T : X → ℕ) : X → ℕ :=
  if h : ∃ S ∈ fam, trimM τ lam S = T then Classical.choose h else (fun _ => 0)

lemma preS_spec (τ : ℕ) (lam : (X → ℕ) → X → ℝ) (fam : Set (X → ℕ)) {T : X → ℕ}
    (hT : ∃ S ∈ fam, trimM τ lam S = T) :
    preS τ lam fam T ∈ fam ∧ trimM τ lam (preS τ lam fam T) = T := by
  classical
  unfold preS
  rw [dif_pos hT]
  exact Classical.choose_spec hT

/-- the output family as a Finset -/
noncomputable def theFl (fam : Set (X → ℕ)) (hFin : Set.Finite fam) (τ : ℕ)
    (lam : (X → ℕ) → X → ℝ) : Finset (X → ℕ) :=
  hFin.toFinset.image (fun S : X → ℕ => trimM τ lam S)

lemma trim_mem_theFl (fam : Set (X → ℕ)) (hFin : Set.Finite fam) (τ : ℕ)
    (lam : (X → ℕ) → X → ℝ) {S : X → ℕ} (hS : S ∈ fam) : trimM τ lam S ∈ theFl fam hFin τ lam := by
  classical
  unfold theFl
  exact Finset.mem_image.mpr ⟨S, hFin.mem_toFinset.mpr hS, rfl⟩

lemma theFl_mem_spec (fam : Set (X → ℕ)) (hFin : Set.Finite fam) (τ : ℕ)
    (lam : (X → ℕ) → X → ℝ) {T : X → ℕ} (hT : T ∈ theFl fam hFin τ lam) :
    ∃ S ∈ fam, trimM τ lam S = T := by
  classical
  unfold theFl at hT
  rcases Finset.mem_image.mp hT with ⟨S, hS, hEq⟩
  exact ⟨S, hFin.mem_toFinset.mp hS, hEq⟩

/-- the output system -/
noncomputable def theSys (fam : Set (X → ℕ)) (hFin : Set.Finite fam) (τ : ℕ)
    (lam : (X → ℕ) → X → ℝ) : MSys X :=
  { τ := τ
    lv := fun T x => lvx τ lam (preS τ lam fam T) x
    Fl := theFl fam hFin τ lam }

/-- sCount of a member = sL of its preimage -/
lemma theSys_sCount (fam : Set (X → ℕ)) (hFin : Set.Finite fam) (τ : ℕ)
    (lam : (X → ℕ) → X → ℝ) {T : X → ℕ}
    (hT : T ∈ (theSys fam hFin τ lam).Fl) (j : ℕ) :
    (theSys fam hFin τ lam).sCount T j = sL τ lam (preS τ lam fam T) j := by
  classical
  have hpre := preS_spec τ lam fam (theFl_mem_spec fam hFin τ lam hT)
  have hTx : ∀ x : X, T x = trimM τ lam (preS τ lam fam T) x := congrFun (hpre.2.symm)
  unfold MSys.sCount
  change (∑ x : X, if lvx τ lam (preS τ lam fam T) x = j then T x else 0) =
    sL τ lam (preS τ lam fam T) j
  have hEq : (∑ x : X, if lvx τ lam (preS τ lam fam T) x = j then T x else 0) =
      ∑ x : X, if lvx τ lam (preS τ lam fam T) x = j then trimM τ lam (preS τ lam fam T) x else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : lvx τ lam (preS τ lam fam T) x = j
    · simp [h, hTx x]
    · simp [h]
  rw [hEq]
  exact levelCount_eq_sL τ lam (preS τ lam fam T) j

/-- total weight of a member = Σ_j (sL j)·wlev j -/
lemma theSys_totalWeight (fam : Set (X → ℕ)) (hFin : Set.Finite fam) (τ : ℕ)
    (lam : (X → ℕ) → X → ℝ) {T : X → ℕ}
    (hT : T ∈ (theSys fam hFin τ lam).Fl) :
    (theSys fam hFin τ lam).totalWeightM T =
      ∑ j ∈ Finset.range (τ + 1), (sL τ lam (preS τ lam fam T) j : ℝ) * wlev j := by
  classical
  have hpre := preS_spec τ lam fam (theFl_mem_spec fam hFin τ lam hT)
  unfold MSys.totalWeightM MSys.weightM
  change (∑ j ∈ Finset.range ((theSys fam hFin τ lam).τ + 1),
      ((theSys fam hFin τ lam).countAt T T j : ℝ) * wlev j)
      = ∑ j ∈ Finset.range (τ + 1), (sL τ lam (preS τ lam fam T) j : ℝ) * wlev j
  calc
    (∑ j ∈ Finset.range ((theSys fam hFin τ lam).τ + 1),
        ((theSys fam hFin τ lam).countAt T T j : ℝ) * wlev j)
        = ∑ j ∈ Finset.range (τ + 1), ((theSys fam hFin τ lam).sCount T j : ℝ) * wlev j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hc := MSys.sCount_eq_countAt_self (theSys fam hFin τ lam) T j
          rw [hc]
    _ = ∑ j ∈ Finset.range (τ + 1), (sL τ lam (preS τ lam fam T) j : ℝ) * wlev j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hsc := theSys_sCount fam hFin τ lam hT j
          rw [hsc]

/-- τ budget: (Bnd)·wlev τ ≤ q⁻¹ for τ = logq(Bnd+1)+2 -/
lemma tau_budget (Bnd : ℕ) :
    (Bnd : ℝ) * wlev (Pre.logq (Bnd + 1) + 2) ≤ (q : ℝ)⁻¹ := by
  let m : ℕ := Pre.logq (Bnd + 1) + 1
  have hτ : Pre.logq (Bnd + 1) + 2 = m + 1 := by
    unfold m
    omega
  have hspec := Pre.logq_spec (Bnd + 1)
  have hB : Bnd < (q : ℕ) ^ m := by
    unfold m
    have h' : Bnd + 1 < (q : ℕ) ^ (Pre.logq (Bnd + 1) + 1) := by simpa using hspec
    omega
  have hBle : (Bnd : ℝ) ≤ (q : ℝ) ^ m := by
    have hBreal : (Bnd : ℝ) < (q : ℝ) ^ m := by
      exact_mod_cast hB
    exact le_of_lt hBreal
  rw [hτ]
  have hw : (q : ℝ) ^ m * wlev (m + 1) = (q : ℝ)⁻¹ := by
    rw [wlev_succ]
    have hwlev : (q : ℝ) ^ m * wlev m = 1 := by
      unfold wlev
      field_simp [q_ne_zero]
    have hre : (q : ℝ) ^ m * ((q : ℝ)⁻¹ * wlev m) = ((q : ℝ) ^ m * wlev m) * (q : ℝ)⁻¹ := by ring
    rw [hre, hwlev]
    simp
  have hmul := mul_le_mul_of_nonneg_right hBle (wlev_nonneg (m + 1))
  calc
    (Bnd : ℝ) * wlev (m + 1) ≤ (q : ℝ) ^ m * wlev (m + 1) := hmul
    _ = (q : ℝ)⁻¹ := hw

/-- FBoundedM of the output -/
lemma theSys_fbounded (fam : Set (X → ℕ)) (hFin : Set.Finite fam) (τ : ℕ)
    (lam : (X → ℕ) → X → ℝ) :
    (theSys fam hFin τ lam).FBoundedM := by
  classical
  unfold MSys.FBoundedM
  intro T hT x
  change lvx τ lam (preS τ lam fam T) x ≤ τ
  exact lvx_le_tau τ lam (preS τ lam fam T) x

/-- TotBoundM of the output -/
lemma theSys_totbound (fam : Set (X → ℕ)) (hFin : Set.Finite fam) (τ : ℕ)
    (lam : (X → ℕ) → X → ℝ) (Bnd : ℕ)
    (hB : ∀ S ∈ fam, sizeM S ≤ Bnd) (hτ : (Bnd : ℝ) * wlev τ ≤ (q : ℝ)⁻¹)
    (hnon : ∀ S ∈ fam, ∀ x : X, 0 ≤ lam S x) (hge : ∀ S ∈ fam, 1 ≤ mwtot lam S) :
    (theSys fam hFin τ lam).TotBoundM := by
  classical
  unfold MSys.TotBoundM
  intro T hT
  have hTfl : T ∈ theFl fam hFin τ lam := by
    simpa [MSys.F, theSys] using hT
  have hpre := preS_spec τ lam fam (theFl_mem_spec fam hFin τ lam hTfl)
  have hSge : 1 ≤ mwtot lam (preS τ lam fam T) := hge (preS τ lam fam T) hpre.1
  have hSnon : ∀ x : X, 0 ≤ lam (preS τ lam fam T) x := hnon (preS τ lam fam T) hpre.1
  have hsize : sizeM (preS τ lam fam T) ≤ Bnd := hB (preS τ lam fam T) hpre.1
  have hw := perS_weight τ lam (preS τ lam fam T) Bnd hSnon hSge hsize hτ
  have ht := theSys_totalWeight fam hFin τ lam hTfl
  rw [ht]
  exact hw

/-- FLegalM of the output -/
lemma theSys_flegal (fam : Set (X → ℕ)) (hFin : Set.Finite fam) (τ : ℕ)
    (lam : (X → ℕ) → X → ℝ)
    (hnon : ∀ S ∈ fam, ∀ x : X, 0 ≤ lam S x) (hge : ∀ S ∈ fam, 1 ≤ mwtot lam S) :
    (theSys fam hFin τ lam).FLegalM := by
  classical
  unfold MSys.FLegalM
  intro T hT j hj
  have hTfl : T ∈ theFl fam hFin τ lam := by
    simpa [MSys.F, theSys] using hT
  have hsc := theSys_sCount fam hFin τ lam hTfl j
  have hleg := perS_legal τ lam (preS τ lam fam T) j (by simpa [theSys] using hj)
  change Sys.LegalEntry ((theSys fam hFin τ lam).sCount T j) j
  rw [hsc]
  exact hleg

/-- (d): every original member has a trim -/
lemma theSys_cover (fam : Set (X → ℕ)) (hFin : Set.Finite fam) (τ : ℕ)
    (lam : (X → ℕ) → X → ℝ) :
    ∀ S ∈ fam, ∃ T ∈ (theSys fam hFin τ lam).F, subM T S := by
  classical
  intro S hS
  refine ⟨trimM τ lam S, ?_, trimM_subM τ lam S⟩
  unfold MSys.F theSys
  exact trim_mem_theFl fam hFin τ lam hS

/-- (e): domination from each trim back to its original -/
lemma theSys_dom (fam : Set (X → ℕ)) (hFin : Set.Finite fam) (τ : ℕ)
    (lam : (X → ℕ) → X → ℝ) :
    ∀ T ∈ (theSys fam hFin τ lam).F, ∃ S ∈ fam, subM T S ∧ ∀ x : X, 0 < T x → lam S x ≥ wlev ((theSys fam hFin τ lam).lv T x) := by
  classical
  intro T hT
  have hTfl : T ∈ theFl fam hFin τ lam := by
    simpa [MSys.F, theSys] using hT
  have hpre := preS_spec τ lam fam (theFl_mem_spec fam hFin τ lam hTfl)
  refine ⟨preS τ lam fam T, hpre.1, ?_⟩
  constructor
  · intro x
    simpa [hpre.2] using (trimM_le τ lam (preS τ lam fam T) x)
  · intro x hx
    change lam (preS τ lam fam T) x ≥ wlev (lvx τ lam (preS τ lam fam T) x)
    exact trim_dom τ lam (preS τ lam fam T) (by
      simpa [hpre.2] using hx)

/-- multiset pre-processing: arbitrary weighted multiset family -> layered legal MSys -/
theorem theorem_preprocessM (F : Set (X → ℕ)) (lam : (X → ℕ) → X → ℝ)
    (hFin : Set.Finite F)
    (hnonneg : ∀ S ∈ F, ∀ x : X, 0 ≤ lam S x)
    (hnonnegtot : ∀ S ∈ F, 1 ≤ mwtot lam S) :
    ∃ N : MSys X, N.FBoundedM ∧ N.TotBoundM ∧ N.FLegalM ∧
      (∀ S ∈ F, ∃ S' ∈ N.F, subM S' S) ∧
      (∀ S' ∈ N.F, ∃ S ∈ F, subM S' S ∧ ∀ x : X, 0 < S' x → lam S x ≥ wlev (N.lv S' x)) := by
  classical
  let B : ℕ := Classical.choose (sizeM_le_of_finite hFin)
  let τ : ℕ := Pre.logq (B + 1) + 2
  have hB : ∀ S ∈ F, sizeM S ≤ B := by
    intro S hS
    exact (Classical.choose_spec (sizeM_le_of_finite hFin)) S hS
  have hτB : (B : ℝ) * wlev τ ≤ (q : ℝ)⁻¹ := by
    simpa [τ] using (tau_budget B)
  let N : MSys X := theSys F hFin τ lam
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [N] using (theSys_fbounded F hFin τ lam)
  · simpa [N] using (theSys_totbound F hFin τ lam B hB hτB hnonneg hnonnegtot)
  · simpa [N] using (theSys_flegal F hFin τ lam hnonneg hnonnegtot)
  · intro S hS
    simpa [N] using (theSys_cover F hFin τ lam S hS)
  · simpa [N] using (theSys_dom F hFin τ lam)

end MSys

end Multi
end Submission
