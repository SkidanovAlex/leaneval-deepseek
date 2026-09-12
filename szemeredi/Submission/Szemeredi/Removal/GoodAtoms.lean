import Mathlib
import Submission.Szemeredi.Removal.FullRegularity2
import Submission.Szemeredi.Removal.Atoms

/-!
# Good atoms (Tao, arXiv:math/0503572, Definition 3.1 and Lemma 3.2)

Two local conditions on an atom `Ae` of a σ-algebra `B_e`, relative to the atoms
of the lower-order σ-algebras:

* `LargeOk` (the `(e-large)` condition): `Ae` is not much smaller than the
  intersection of the boundary atoms;
* `RegOk` (the `(e-regularity)` condition): the conditional expectations of `1_Ae`
  with respect to the coarse and fine boundary algebras differ by little on the
  intersection of the lower-order atoms.

The two main results are the pointwise-decomposition identities and the two
measure estimates `avg (1_Ae · 1_{bad}) ≤ 1/log F(M) + 1/F(M)` (Tao, Lemma 3.2).
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {β γ Ω : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
  [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-- The product of the indicators of a tuple of sets. -/
noncomputable def prodT (T : β → Finset Ω) (x : Ω) : ℝ := ∏ i, SigAlg.indicator (T i) x

theorem prodT_nonneg (T : β → Finset Ω) (x : Ω) : 0 ≤ prodT T x :=
  Finset.prod_nonneg (fun i _ => SigAlg.indicator_nonneg (T i) x)

theorem prodT_le_one (T : β → Finset Ω) (x : Ω) : prodT T x ≤ 1 :=
  Finset.prod_le_one (fun i _ => SigAlg.indicator_nonneg (T i) x)
    (fun i _ => SigAlg.indicator_le_one (T i) x)

/-- A tuple of atoms, one for each index. -/
abbrev AtomFam (P : β → SigAlg Ω) := (i : β) → {s : Finset Ω // s ∈ (P i).atoms}

/-- The pointwise atom tuple of `x`. -/
noncomputable def atomFamOf (P : β → SigAlg Ω) (x : Ω) : AtomFam P :=
  fun i => ⟨(P i).block x, SigAlg.block_mem_atoms (P i) x⟩

/-- The product of the indicators of a tuple of atoms. -/
noncomputable def prodFam (P : β → SigAlg Ω) (A : AtomFam P) (x : Ω) : ℝ :=
  ∏ i, SigAlg.indicator ((A i).val) x

theorem prodFam_nonneg (P : β → SigAlg Ω) (A : AtomFam P) (x : Ω) : 0 ≤ prodFam P A x :=
  Finset.prod_nonneg (fun i _ => SigAlg.indicator_nonneg ((A i).val) x)

theorem prodFam_atomFamOf (P : β → SigAlg Ω) (x : Ω) : prodFam P (atomFamOf P x) x = 1 := by
  unfold prodFam
  refine Finset.prod_eq_one (fun i _ => ?_)
  show (if x ∈ (P i).block x then (1 : ℝ) else 0) = 1
  rw [if_pos ((P i).mem_block x)]

theorem prodFam_eq_zero_of_ne (P : β → SigAlg Ω) (A : AtomFam P) (x : Ω)
    (h : A ≠ atomFamOf P x) : prodFam P A x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, A i ≠ atomFamOf P x i := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  unfold prodFam
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  show (if x ∈ (A i).val then (1 : ℝ) else 0) = 0
  rw [if_neg]
  intro hx
  apply hi
  refine Subtype.ext ?_
  show (A i).val = (P i).block x
  exact (SigAlg.eq_of_mem_atoms (A i).2 hx).symm

theorem sum_prodFam (P : β → SigAlg Ω) (x : Ω) : (∑ A : AtomFam P, prodFam P A x) = 1 := by
  rw [Finset.sum_eq_single (atomFamOf P x)]
  · exact prodFam_atomFamOf P x
  · intro A _ hne
    exact prodFam_eq_zero_of_ne P A x hne
  · intro h
    exact absurd (Finset.mem_univ (atomFamOf P x)) h

/-- The `(e-large)` condition of Tao's Definition 3.1 (which depends only on the
tuple of boundary atoms). -/
noncomputable def LargeOk (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (T : β → Finset Ω)
    (Ae : Finset Ω) : Prop :=
  (1 / Real.log (F (M j))) * avg (prodT T) ≤ avg (fun x => SigAlg.indicator Ae x * prodT T x)

/-- The difference of conditional expectations appearing in the regularity condition
(with respect to the join of the *boundary* σ-algebras). -/
noncomputable def diff (P P' : β → SigAlg Ω) (Ae : Finset Ω) (x : Ω) : ℝ :=
  (SigAlg.iInf P' Finset.univ).condExp (SigAlg.indicator Ae) x
    - (SigAlg.iInf P Finset.univ).condExp (SigAlg.indicator Ae) x

/-- The `(e-regularity)` condition of Tao's Definition 3.1: the conditional
expectations (with respect to the boundary algebras, indexed by `β`) differ by
little on the intersection of the lower-order atoms (indexed by `γ`). -/
noncomputable def RegOk (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (T : γ → Finset Ω) (Ae : Finset Ω)
    (P P' : β → SigAlg Ω) : Prop :=
  avg (fun x => (diff P P' Ae x) ^ 2 * prodT T x) ≤ (1 / (F (M j))) * avg (prodT T)

/-- The largeness-failure predicate on an atom tuple. -/
noncomputable def LBadFam (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (Ae : Finset Ω)
    (P : β → SigAlg Ω) (A : AtomFam P) : Prop :=
  ¬ LargeOk F M j (fun i => (A i).val) Ae

/-- The regularity-failure predicate on an atom tuple. -/
noncomputable def RBadFam (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (Ae : Finset Ω)
    (P P' : β → SigAlg Ω) (Q : γ → SigAlg Ω) (A : AtomFam Q) : Prop :=
  ¬ RegOk F M j (fun i => (A i).val) Ae P P'

/-- The set of points at which the largeness condition fails for the pointwise
boundary tuple. -/
noncomputable def LBadSet (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (Ae : Finset Ω)
    (P : β → SigAlg Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun x => LBadFam F M j Ae P (atomFamOf P x))

/-- The set of points at which the regularity condition fails for the pointwise
lower-order atom tuple. -/
noncomputable def RBadSet (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (Ae : Finset Ω)
    (P P' : β → SigAlg Ω) (Q : γ → SigAlg Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun x => RBadFam F M j Ae P P' Q (atomFamOf Q x))

theorem mem_lBadSet {F : ℕ → ℕ} {M : ℕ → ℕ} {j : ℕ} {Ae : Finset Ω}
    {P : β → SigAlg Ω} {x : Ω} :
    x ∈ LBadSet F M j Ae P ↔ ¬ LargeOk F M j (fun i => (P i).block x) Ae := by
  classical
  unfold LBadSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_rBadSet {F : ℕ → ℕ} {M : ℕ → ℕ} {j : ℕ} {Ae : Finset Ω}
    {P P' : β → SigAlg Ω} {Q : γ → SigAlg Ω} {x : Ω} :
    x ∈ RBadSet F M j Ae P P' Q ↔ ¬ RegOk F M j (fun i => (Q i).block x) Ae P P' := by
  classical
  unfold RBadSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem lBad_fam_iff (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (Ae : Finset Ω)
    (P : β → SigAlg Ω) (x : Ω) :
    LBadFam F M j Ae P (atomFamOf P x) ↔ x ∈ LBadSet F M j Ae P := by
  classical
  simp only [LBadSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem rBad_fam_iff (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (Ae : Finset Ω)
    (P P' : β → SigAlg Ω) (Q : γ → SigAlg Ω) (x : Ω) :
    RBadFam F M j Ae P P' Q (atomFamOf Q x) ↔ x ∈ RBadSet F M j Ae P P' Q := by
  classical
  simp only [RBadSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Averaging a function multiplied by an `if … then … else 0`. -/
theorem avg_ite (c : Prop) [Decidable c] (f : Ω → ℝ) :
    avg (fun x => (if c then f x else 0)) = if c then avg f else 0 := by
  by_cases h : c
  · rw [if_pos h]
    congr 1
    funext x
    rw [if_pos h]
  · have hfun : (fun x => (if c then f x else 0)) = fun _ => (0 : ℝ) := by
      funext x; rw [if_neg h]
    rw [hfun, if_neg h]
    exact avg_const 0

/-- **Largeness failures are few** (first half of Tao, Lemma 3.2). -/
theorem avg_indicator_lBad_le (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (Ae : Finset Ω)
    (P : β → SigAlg Ω) (hF1 : 1 ≤ F (M j)) :
    avg (fun x => SigAlg.indicator Ae x * SigAlg.indicator (LBadSet F M j Ae P) x)
      ≤ 1 / Real.log (F (M j)) := by
  classical
  have hlog : 0 ≤ 1 / Real.log (F (M j)) :=
    div_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hF1))
  have hpt : ∀ x : Ω, SigAlg.indicator (LBadSet F M j Ae P) x
      = ∑ A : AtomFam P, (if LBadFam F M j Ae P A then prodFam P A x else 0) := by
    intro x
    rw [Finset.sum_eq_single (atomFamOf P x)]
    · have hiff := lBad_fam_iff F M j Ae P x
      rw [prodFam_atomFamOf]
      by_cases h : LBadFam F M j Ae P (atomFamOf P x)
      · have hx : x ∈ LBadSet F M j Ae P := hiff.mp h
        simp [SigAlg.indicator, h, hx]
      · have hx : x ∉ LBadSet F M j Ae P := fun hh => h (hiff.mpr hh)
        simp [SigAlg.indicator, h, hx]
    · intro A _ hne
      rw [prodFam_eq_zero_of_ne P A x hne]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hAv : avg (fun x => SigAlg.indicator Ae x * SigAlg.indicator (LBadSet F M j Ae P) x)
      = ∑ A : AtomFam P, (if LBadFam F M j Ae P A
          then avg (fun x => SigAlg.indicator Ae x * prodFam P A x) else 0) := by
    calc avg (fun x => SigAlg.indicator Ae x * SigAlg.indicator (LBadSet F M j Ae P) x)
        = avg (fun x => ∑ A : AtomFam P, (if LBadFam F M j Ae P A
              then SigAlg.indicator Ae x * prodFam P A x else 0)) := by
          congr 1
          funext x
          rw [hpt x, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun A _ => ?_)
          by_cases h : LBadFam F M j Ae P A <;> simp [h]
      _ = ∑ A : AtomFam P, avg (fun x => (if LBadFam F M j Ae P A
              then SigAlg.indicator Ae x * prodFam P A x else 0)) := avg_sum _
      _ = ∑ A : AtomFam P, (if LBadFam F M j Ae P A
              then avg (fun x => SigAlg.indicator Ae x * prodFam P A x) else 0) :=
          Finset.sum_congr rfl (fun A _ => avg_ite _ _)
  rw [hAv]
  calc (∑ A : AtomFam P, (if LBadFam F M j Ae P A
          then avg (fun x => SigAlg.indicator Ae x * prodFam P A x) else 0))
      ≤ ∑ A : AtomFam P, (if LBadFam F M j Ae P A
          then (1 / Real.log (F (M j))) * avg (prodFam P A) else 0) := by
        refine Finset.sum_le_sum (fun A _ => ?_)
        by_cases h : LBadFam F M j Ae P A
        · simp only [h, if_true]
          exact le_of_lt (not_le.mp h)
        · simp [h]
    _ ≤ ∑ A : AtomFam P, (1 / Real.log (F (M j))) * avg (prodFam P A) := by
        refine Finset.sum_le_sum (fun A _ => ?_)
        by_cases h : LBadFam F M j Ae P A
        · simp [h]
        · simp only [h, if_false]
          exact mul_nonneg hlog (avg_nonneg (fun x => prodFam_nonneg P A x))
    _ = (1 / Real.log (F (M j))) * ∑ A : AtomFam P, avg (prodFam P A) := by rw [Finset.mul_sum]
    _ = 1 / Real.log (F (M j)) := by
        have h1 : (∑ A : AtomFam P, avg (prodFam P A)) = 1 := by
          rw [← avg_sum]
          rw [show (fun x => ∑ A : AtomFam P, prodFam P A x) = fun _ => (1 : ℝ) from
            funext (sum_prodFam P)]
          exact avg_const 1
        rw [h1, mul_one]

/-- **Regularity failures are few** (second half of Tao, Lemma 3.2). -/
theorem avg_indicator_rBad_le (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (Ae : Finset Ω)
    (P P' : β → SigAlg Ω) (Q : γ → SigAlg Ω) (hF1 : 1 ≤ F (M j))
    (hP : ∀ f, (P f).Refines (P' f))
    (hpy : (SigAlg.iInf P' (Finset.univ : Finset β)).energy (SigAlg.indicator Ae) ≤
      (SigAlg.iInf P (Finset.univ : Finset β)).energy (SigAlg.indicator Ae)
        + (1 / (F (M j))) ^ 2) :
    avg (fun x => SigAlg.indicator Ae x * SigAlg.indicator (RBadSet F M j Ae P P' Q) x)
      ≤ 1 / (F (M j)) := by
  classical
  have hFpos : (0 : ℝ) < (F (M j) : ℝ) := by
    have : 0 < F (M j) := lt_of_lt_of_le Nat.zero_lt_one hF1
    exact_mod_cast this
  have hb2 : avg (fun x => (diff P P' Ae x) ^ 2) ≤ (1 / (F (M j))) ^ 2 := by
    have hpyth := SigAlg.energy_eq_energy_add (P := SigAlg.iInf P (Finset.univ : Finset β))
      (Q := SigAlg.iInf P' (Finset.univ : Finset β))
      (SigAlg.Refines.iInf_mono (s := (Finset.univ : Finset β)) (fun i _ => hP i))
      (SigAlg.indicator Ae)
    unfold diff
    linarith [hpyth, hpy]
  have hpt : ∀ x : Ω, SigAlg.indicator (RBadSet F M j Ae P P' Q) x
      = ∑ A : AtomFam Q, (if RBadFam F M j Ae P P' Q A then prodFam Q A x else 0) := by
    intro x
    rw [Finset.sum_eq_single (atomFamOf Q x)]
    · have hiff := rBad_fam_iff F M j Ae P P' Q x
      rw [prodFam_atomFamOf]
      by_cases h : RBadFam F M j Ae P P' Q (atomFamOf Q x)
      · have hx : x ∈ RBadSet F M j Ae P P' Q := hiff.mp h
        simp [SigAlg.indicator, h, hx]
      · have hx : x ∉ RBadSet F M j Ae P P' Q := fun hh => h (hiff.mpr hh)
        simp [SigAlg.indicator, h, hx]
    · intro A _ hne
      rw [prodFam_eq_zero_of_ne Q A x hne]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hAv : avg (fun x => SigAlg.indicator Ae x * SigAlg.indicator (RBadSet F M j Ae P P' Q) x)
      = ∑ A : AtomFam Q, (if RBadFam F M j Ae P P' Q A
          then avg (fun x => SigAlg.indicator Ae x * prodFam Q A x) else 0) := by
    calc avg (fun x => SigAlg.indicator Ae x * SigAlg.indicator (RBadSet F M j Ae P P' Q) x)
        = avg (fun x => ∑ A : AtomFam Q, (if RBadFam F M j Ae P P' Q A
              then SigAlg.indicator Ae x * prodFam Q A x else 0)) := by
          congr 1
          funext x
          rw [hpt x, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun A _ => ?_)
          by_cases h : RBadFam F M j Ae P P' Q A <;> simp [h]
      _ = ∑ A : AtomFam Q, avg (fun x => (if RBadFam F M j Ae P P' Q A
              then SigAlg.indicator Ae x * prodFam Q A x else 0)) := avg_sum _
      _ = ∑ A : AtomFam Q, (if RBadFam F M j Ae P P' Q A
              then avg (fun x => SigAlg.indicator Ae x * prodFam Q A x) else 0) :=
          Finset.sum_congr rfl (fun A _ => avg_ite _ _)
  rw [hAv]
  calc (∑ A : AtomFam Q, (if RBadFam F M j Ae P P' Q A
          then avg (fun x => SigAlg.indicator Ae x * prodFam Q A x) else 0))
      ≤ ∑ A : AtomFam Q, (if RBadFam F M j Ae P P' Q A
          then (F (M j) : ℝ) * avg (fun x => (diff P P' Ae x) ^ 2 * prodFam Q A x)
          else 0) := by
        refine Finset.sum_le_sum (fun A _ => ?_)
        by_cases h : RBadFam F M j Ae P P' Q A
        · simp only [h, if_true]
          have h' : (1 / (F (M j))) * avg (prodT (fun i => (A i).val))
              < avg (fun x => (diff P P' Ae x) ^ 2 * prodT (fun i => (A i).val) x) :=
            not_le.mp h
          have hle : avg (fun x => SigAlg.indicator Ae x * prodFam Q A x)
              ≤ avg (prodT (fun i => (A i).val)) := by
            refine avg_le_avg (fun x => ?_)
            rw [show prodT (fun i => (A i).val) x = prodFam Q A x from rfl]
            exact mul_le_of_le_one_left (prodFam_nonneg Q A x) (SigAlg.indicator_le_one Ae x)
          have h2 : avg (prodT (fun i => (A i).val))
              < (F (M j) : ℝ) * avg (fun x => (diff P P' Ae x) ^ 2
                  * prodT (fun i => (A i).val) x) := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ hFpos] at h'
            linarith [h']
          exact le_trans hle (le_of_lt h2)
        · simp [h]
    _ ≤ ∑ A : AtomFam Q, (F (M j) : ℝ) * avg (fun x => (diff P P' Ae x) ^ 2
          * prodFam Q A x) := by
        refine Finset.sum_le_sum (fun A _ => ?_)
        by_cases h : RBadFam F M j Ae P P' Q A
        · simp [h]
        · simp only [h, if_false]
          exact mul_nonneg (le_of_lt hFpos)
            (avg_nonneg (fun x => mul_nonneg (sq_nonneg _) (prodFam_nonneg Q A x)))
    _ = (F (M j) : ℝ) * ∑ A : AtomFam Q, avg (fun x => (diff P P' Ae x) ^ 2
          * prodFam Q A x) := by rw [Finset.mul_sum]
    _ = (F (M j) : ℝ) * avg (fun x => (diff P P' Ae x) ^ 2
          * ∑ A : AtomFam Q, prodFam Q A x) := by
        have hfun : (fun x => ∑ A : AtomFam Q, (diff P P' Ae x) ^ 2 * prodFam Q A x)
            = fun x => (diff P P' Ae x) ^ 2 * ∑ A : AtomFam Q, prodFam Q A x := by
          funext x
          rw [Finset.mul_sum]
        rw [← avg_sum, hfun]
    _ = (F (M j) : ℝ) * avg (fun x => (diff P P' Ae x) ^ 2 * 1) := by
        have hfun : (fun x => (diff P P' Ae x) ^ 2 * ∑ A : AtomFam Q, prodFam Q A x)
            = fun x => (diff P P' Ae x) ^ 2 * 1 := by
          funext x
          rw [sum_prodFam]
        rw [hfun]
    _ = (F (M j) : ℝ) * avg (fun x => (diff P P' Ae x) ^ 2) := by
        have hfun : (fun x => (diff P P' Ae x) ^ 2 * 1) = fun x => (diff P P' Ae x) ^ 2 := by
          funext x; rw [mul_one]
        rw [hfun]
    _ ≤ (F (M j) : ℝ) * (1 / (F (M j))) ^ 2 :=
        mul_le_mul_of_nonneg_left hb2 (le_of_lt hFpos)
    _ = 1 / (F (M j)) := by field_simp

/-- **Most atoms are good** (Tao, Lemma 3.2), combined form. -/
theorem avg_indicator_bad_le (F : ℕ → ℕ) (M : ℕ → ℕ) (j : ℕ) (Ae : Finset Ω)
    (P P' : β → SigAlg Ω) (Q : γ → SigAlg Ω) (hF1 : 1 ≤ F (M j))
    (hlb : avg (fun x => SigAlg.indicator Ae x * SigAlg.indicator (LBadSet F M j Ae P) x)
      ≤ 1 / Real.log (F (M j)))
    (hrb : avg (fun x => SigAlg.indicator Ae x * SigAlg.indicator (RBadSet F M j Ae P P' Q) x)
      ≤ 1 / (F (M j))) :
    avg (fun x => SigAlg.indicator Ae x
        * SigAlg.indicator (LBadSet F M j Ae P ∪ RBadSet F M j Ae P P' Q) x)
      ≤ 1 / Real.log (F (M j)) + 1 / (F (M j)) := by
  classical
  have hone : (1 : ℝ) ≤ 1 := le_refl 1
  have hsplit : ∀ x : Ω, SigAlg.indicator (LBadSet F M j Ae P ∪ RBadSet F M j Ae P P' Q) x
      ≤ SigAlg.indicator (LBadSet F M j Ae P) x
        + SigAlg.indicator (RBadSet F M j Ae P P' Q) x := by
    intro x
    by_cases h1 : x ∈ LBadSet F M j Ae P
    · have hI : SigAlg.indicator (LBadSet F M j Ae P) x = 1 := by
        simp [SigAlg.indicator, h1]
      rw [hI]
      linarith [SigAlg.indicator_nonneg (LBadSet F M j Ae P ∪ RBadSet F M j Ae P P' Q) x,
        SigAlg.indicator_le_one (LBadSet F M j Ae P ∪ RBadSet F M j Ae P P' Q) x,
        SigAlg.indicator_nonneg (RBadSet F M j Ae P P' Q) x]
    · by_cases h2 : x ∈ RBadSet F M j Ae P P' Q
      · have hI : SigAlg.indicator (RBadSet F M j Ae P P' Q) x = 1 := by
          simp [SigAlg.indicator, h2]
        rw [hI]
        linarith [SigAlg.indicator_nonneg (LBadSet F M j Ae P ∪ RBadSet F M j Ae P P' Q) x,
          SigAlg.indicator_le_one (LBadSet F M j Ae P ∪ RBadSet F M j Ae P P' Q) x,
          SigAlg.indicator_nonneg (LBadSet F M j Ae P) x]
      · have h3 : x ∉ LBadSet F M j Ae P ∪ RBadSet F M j Ae P P' Q := by
          simp only [Finset.mem_union, not_or]; exact ⟨h1, h2⟩
        have hI : SigAlg.indicator (LBadSet F M j Ae P ∪ RBadSet F M j Ae P P' Q) x = 0 := by
          simp [SigAlg.indicator, h3]
        rw [hI]
        linarith [SigAlg.indicator_nonneg (LBadSet F M j Ae P) x,
          SigAlg.indicator_nonneg (RBadSet F M j Ae P P' Q) x]
  calc avg (fun x => SigAlg.indicator Ae x
        * SigAlg.indicator (LBadSet F M j Ae P ∪ RBadSet F M j Ae P P' Q) x)
      ≤ avg (fun x => SigAlg.indicator Ae x
          * (SigAlg.indicator (LBadSet F M j Ae P) x
            + SigAlg.indicator (RBadSet F M j Ae P P' Q) x)) := by
        refine avg_le_avg (fun x => ?_)
        exact mul_le_mul_of_nonneg_left (hsplit x) (SigAlg.indicator_nonneg Ae x)
    _ = avg (fun x => SigAlg.indicator Ae x * SigAlg.indicator (LBadSet F M j Ae P) x
          + SigAlg.indicator Ae x * SigAlg.indicator (RBadSet F M j Ae P P' Q) x) := by
        congr 1; ext x; ring
    _ = avg (fun x => SigAlg.indicator Ae x * SigAlg.indicator (LBadSet F M j Ae P) x)
          + avg (fun x => SigAlg.indicator Ae x
              * SigAlg.indicator (RBadSet F M j Ae P P' Q) x) := avg_add _ _
    _ ≤ 1 / Real.log (F (M j)) + 1 / (F (M j)) := add_le_add hlb hrb

end Szemeredi.Removal
