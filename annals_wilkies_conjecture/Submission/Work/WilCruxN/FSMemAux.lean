import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.TSh
import Submission.Work.WilG4c.SliceC1FD
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.supBall_mem

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilCruxN.FSA

open WilkiesDesign WilkiesDesign.CG
open Work.WilG4c

/-! ## 1. Reading the graph atom -/

lemma mem_famGraph_snoc {p n : ℕ} (f : (Fin p → ℝ) → (Fin n → ℝ) → ℝ)
    (x : Fin (p + n) → ℝ) (u : ℝ) :
    Fin.snoc x u ∈ famGraph f ↔
      u = f (fun i : Fin p => x (Fin.castAdd n i)) (fun j : Fin n => x (Fin.natAdd p j)) := by
  rw [famGraph, graphOf, Set.mem_ofPred_eq]
  simp only [Fin.snoc_last, Fin.init_snoc]

/-! ## 2. The `ε`-`δ` form of the punctured limit -/

lemma punctured_limit_iff {b : ℕ} (g : (Fin b → ℝ) → ℝ) :
    Filter.Tendsto g (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < δ → |g z| < ε := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    have h1 : ∀ᶠ z in nhds (0 : Fin b → ℝ),
        z ∈ ({(0 : Fin b → ℝ)}ᶜ : Set (Fin b → ℝ)) → dist (g z) 0 < ε :=
      eventually_nhdsWithin_iff.mp (h ε hε)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp h1
    refine ⟨δ, hδ, fun z hz hzδ => ?_⟩
    have h2 := hδ' (show dist z (0 : Fin b → ℝ) < δ by simpa [dist_eq_norm] using hzδ)
      (by simpa using hz)
    simpa [Real.dist_eq] using h2
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    rw [eventually_nhdsWithin_iff]
    refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun z hz hz0 => ?_⟩
    have h2 := hδ' z (by simpa using hz0) (by simpa [dist_eq_norm] using hz)
    simpa [Real.dist_eq] using h2

lemma not_punctured_limit_iff {b : ℕ} (g : (Fin b → ℝ) → ℝ) :
    ¬ Filter.Tendsto g (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0) ↔
      ∃ ε > 0, ∀ δ > 0, ∃ z : Fin b → ℝ, z ≠ 0 ∧ ‖z‖ < δ ∧ ε ≤ |g z| := by
  rw [punctured_limit_iff]
  constructor
  · intro h
    push_neg at h
    exact h
  · rintro ⟨ε, hε, hδ⟩ h'
    obtain ⟨δ, hδpos, hδ'⟩ := h' ε hε
    obtain ⟨z, hz0, hzδ, hzε⟩ := hδ δ hδpos
    exact absurd (hδ' z hz0 hzδ) (not_lt.mpr hzε)

/-! ## 3. Squares and the sup norm -/

lemma sum_sq_eq_zero_iff {b : ℕ} (y : Fin b → ℝ) : (∑ j, (y j) ^ 2) = 0 ↔ y = 0 := by
  constructor
  · intro h
    funext j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun i : Fin b => (y i) ^ 2) (fun i _ => sq_nonneg (y i))).mp h
    exact sq_eq_zero_iff.mp (h2 j (Finset.mem_univ j))
  · intro h; simp [h]

lemma norm_lt_iff_forall_abs {b : ℕ} {z : Fin b → ℝ} {c : ℝ} (hz : z ≠ 0) :
    ‖z‖ < c ↔ ∀ j, |z j| < c := by
  have hj : ∃ j : Fin b, z j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hz (funext fun j => h j)
  constructor
  · intro h j
    have := norm_le_pi_norm z j
    rw [Real.norm_eq_abs] at this
    linarith
  · intro h
    obtain ⟨j, hj0⟩ := hj
    have hc : 0 < c := lt_of_lt_of_le (abs_pos.mpr hj0) (le_of_lt (h j))
    have hd : dist z (0 : Fin b → ℝ) = ‖z‖ := by rw [dist_eq_norm, sub_zero]
    rw [← hd, dist_pi_lt_iff hc]
    intro i
    simpa [Real.dist_eq] using h i

/-- The strictly-positive-radius form of the sup-norm ball, as a finite conjunction. -/
lemma forall_sq_lt_sq_iff_norm {b : ℕ} {z : Fin b → ℝ} {δ : ℝ} (hδ : 0 < δ) :
    (∀ j, (z j) ^ 2 < δ ^ 2) ↔ ‖z‖ < δ := by
  constructor
  · intro h
    have h' : ∀ j, |z j| < δ := fun j => by
      have hh := sq_lt_sq.mp (h j)
      rwa [abs_of_pos hδ] at hh
    have hd : dist z (0 : Fin b → ℝ) = ‖z‖ := by rw [dist_eq_norm, sub_zero]
    rw [← hd, dist_pi_lt_iff hδ]
    intro j; simpa [Real.dist_eq] using h' j
  · intro h j
    have h1 : |z j| < δ := by
      have hh := norm_le_pi_norm z j
      rw [Real.norm_eq_abs] at hh
      linarith
    rw [← abs_of_pos hδ] at h1
    exact sq_lt_sq.mpr h1

/-- Over `ℝ`, the equation `t ^ 2 * a = 1` has a solution `t` iff `a > 0`. -/
lemma sq_mul_eq_one_iff_pos {a : ℝ} : (∃ t : ℝ, t ^ 2 * a = 1) ↔ 0 < a := by
  constructor
  · rintro ⟨t, ht⟩
    nlinarith [sq_nonneg t, sq_nonneg a]
  · intro ha
    refine ⟨Real.sqrt a⁻¹, ?_⟩
    rw [Real.sq_sqrt (by positivity), inv_mul_cancel₀ (ne_of_gt ha)]

/-! ## 4. Two ball sets -/

/-- The set `{x : ℝ^b | ∀ j, |x j| < c}` (a ball of constant radius, possibly empty). -/
def ballConstSet (b : ℕ) (c : ℝ) : Set (Fin b → ℝ) := {v | ∀ j, |v j| < c}

theorem ballConstSet_mem (S : SOMin) (b F D : ℕ) (c : ℝ)
    (hF : b + 6 ≤ F) (hD : max 4 (4 * b) ≤ D) :
    ballConstSet b c ∈ S.Ω F D b := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have hset : ballConstSet 0 c = (Set.univ : Set (Fin 0 → ℝ)) := by
      ext v; simp [ballConstSet]
    rw [hset]
    exact Work.WilG5.mem_mono (Work.WilG5.univ_mem (S := S) (n := 0)) F D (by omega) (by omega)
  · by_cases hc : 0 < c
    · have hone : ∀ j : Fin b, {v : Fin b → ℝ | |v j| < c} ∈ S.Ω (b + 3) 4 b := by
        intro j
        set P : MvPolynomial (Fin (b + 1)) ℝ :=
          (MvPolynomial.X (Fin.last b)) ^ 2 *
            (MvPolynomial.C (c ^ 2) - (MvPolynomial.X (Fin.castSucc j)) ^ 2) - 1 with hPdef
        have hdeg : P.totalDegree ≤ 4 := by
          rw [hPdef]
          have hX2 : ∀ i : Fin (b + 1),
              ((MvPolynomial.X i) ^ 2 : MvPolynomial (Fin (b + 1)) ℝ).totalDegree ≤ 2 :=
            fun i => by rw [MvPolynomial.totalDegree_X_pow]
          have hC : (MvPolynomial.C (c ^ 2) : MvPolynomial (Fin (b + 1)) ℝ).totalDegree ≤ 2 := by
            rw [MvPolynomial.totalDegree_C]; norm_num
          have hsub : (MvPolynomial.C (c ^ 2) -
              (MvPolynomial.X (Fin.castSucc j)) ^ 2 : MvPolynomial (Fin (b + 1)) ℝ).totalDegree
              ≤ 2 := (MvPolynomial.totalDegree_sub _ _).trans (max_le hC (hX2 _))
          refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
          · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
            have := hX2 (Fin.last b)
            omega
          · rw [MvPolynomial.totalDegree_one]; norm_num
        have hev : ∀ (v : Fin b → ℝ) (t : ℝ), MvPolynomial.eval (Fin.snoc v t) P
            = t ^ 2 * (c ^ 2 - (v j) ^ 2) - 1 := by
          intro v t
          rw [hPdef]
          simp [Fin.snoc_last, Fin.snoc_castSucc]
        have hset : projLast {w : Fin (b + 1) → ℝ | MvPolynomial.eval w P = 0}
            = {v : Fin b → ℝ | |v j| < c} := by
          ext v
          simp only [projLast, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨t, ht⟩
            rw [hev v t] at ht
            have h2 : t ^ 2 * (c ^ 2 - (v j) ^ 2) = 1 := by linarith
            have hpos : 0 < c ^ 2 - (v j) ^ 2 := sq_mul_eq_one_iff_pos.mp ⟨t, h2⟩
            have hlt : (v j) ^ 2 < c ^ 2 := by linarith
            have := sq_lt_sq.mp hlt
            rwa [abs_of_pos hc] at this
          · intro hv
            have hlt : (v j) ^ 2 < c ^ 2 :=
              sq_lt_sq.mpr (by rwa [abs_of_pos hc] : |v j| < |c|)
            have hpos : 0 < c ^ 2 - (v j) ^ 2 := by linarith
            obtain ⟨t, ht⟩ := sq_mul_eq_one_iff_pos.mpr hpos
            exact ⟨t, by rw [hev v t, ht]; ring⟩
        have hproj : {v : Fin b → ℝ | |v j| < c} ∈ S.Ω (b + 3) 4 b := by
          have h := S.proj (Work.WilG1.Omega.mono (S.hyp (b + 1) P) le_rfl hdeg)
          rw [hset] at h
          exact Work.WilG1.Omega.mono h (by omega) le_rfl
        exact hproj
      have hinter := S.inter (F := b + 3) (n := b) (k := b)
        (D := fun _ : Fin b => 4)
        (A := fun j : Fin b => {v : Fin b → ℝ | |v j| < c}) hone
      have hset2 : (⋂ j : Fin b, {v : Fin b → ℝ | |v j| < c}) = ballConstSet b c := by
        ext v; simp [ballConstSet]
      rw [hset2] at hinter
      refine Work.WilG1.Omega.mono hinter (by omega) ?_
      have hsum : (∑ _ : Fin b, (4 : ℕ)) = 4 * b := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact Nat.mul_comm b 4
      rw [hsum]
      omega
    · have hset : ballConstSet b c = (∅ : Set (Fin b → ℝ)) := by
        ext v
        simp only [ballConstSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have h2 := h ⟨0, hb⟩
        have h3 : 0 ≤ |v ⟨0, hb⟩| := abs_nonneg _
        linarith
      rw [hset]
      exact Work.WilG5.mem_mono (Work.WilG5.empty_mem (S := S) (n := b)) F D (by omega)
        (by omega)

/-- The "sup ball" `{x : ℝ^{b+1} | ∀ i : Fin b, x i² < x_last²}`; the radius is the last
coordinate, so the inequality reads `|x i| < |x_last|`. -/
def supBallSet (b : ℕ) : Set (Fin (b + 1) → ℝ) :=
  {z | ∀ i : Fin b, z (Fin.castSucc i) ^ 2 < z (Fin.last b) ^ 2}

theorem supBallSet_mem (S : SOMin) (b F D : ℕ) (hF : b + 4 ≤ F) (hD : 4 * b ≤ D) :
    supBallSet b ∈ S.Ω F D (b + 1) := by
  refine Work.WilG5.mem_mono (Work.WilG1.Calc.supBall_mem (S := S) (n := b) 0) F D hF ?_
  simpa only [Polynomial.eval_C] using hD

/-! ## 5. Degree helpers -/

lemma td_X4 {N : ℕ} (i : Fin N) :
    (MvPolynomial.X i : MvPolynomial (Fin N) ℝ).totalDegree ≤ 4 := by
  rw [MvPolynomial.totalDegree_X]; norm_num

lemma td_negX4 {N : ℕ} (i : Fin N) :
    (-(MvPolynomial.X i) : MvPolynomial (Fin N) ℝ).totalDegree ≤ 4 := by
  rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_X]; norm_num

lemma td_C4 {N : ℕ} (c : ℝ) :
    (MvPolynomial.C c : MvPolynomial (Fin N) ℝ).totalDegree ≤ 4 := by
  rw [MvPolynomial.totalDegree_C]; norm_num

lemma td_negC4 {N : ℕ} (c : ℝ) :
    (-(MvPolynomial.C c) : MvPolynomial (Fin N) ℝ).totalDegree ≤ 4 := by
  rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_C]; norm_num

lemma td_sumsq {N b : ℕ} (w : Fin b → Fin N) :
    (∑ j : Fin b, (MvPolynomial.X (w j)) ^ 2 : MvPolynomial (Fin N) ℝ).totalDegree ≤ 8 := by
  refine MvPolynomial.totalDegree_finsetSum_le (fun j _ => ?_)
  rw [MvPolynomial.totalDegree_X_pow]; norm_num

/-! ## 6. A concrete atom -/

/-- `{x | (fun j => x (zi j)) ≠ 0}`. -/
def sumSqNe (S : SOMin) (F D : ℕ) {N b : ℕ} (zi : Fin b → Fin N) : PKS S F D N :=
  PKS.neg (PKS.poly (∑ j : Fin b, (MvPolynomial.X (zi j)) ^ 2) (td_sumsq zi))

theorem sumSqNe_Real (S : SOMin) (F D : ℕ) {N b : ℕ} (zi : Fin b → Fin N) :
    (sumSqNe S F D zi).Real = {x : Fin N → ℝ | (fun j => x (zi j)) ≠ 0} := by
  ext x
  rw [sumSqNe, PKS.Real_neg, PKS.Real_poly]
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, ne_eq]
  rw [show MvPolynomial.eval x (∑ j : Fin b, (MvPolynomial.X (zi j)) ^ 2)
      = ∑ j, (x (zi j)) ^ 2 from by simp]
  rw [sum_sq_eq_zero_iff]


end Work.WilCruxN.FSA
