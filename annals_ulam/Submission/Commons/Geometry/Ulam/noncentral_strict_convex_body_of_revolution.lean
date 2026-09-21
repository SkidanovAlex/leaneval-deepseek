import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Submission.Commons.Geometry.Ulam.isCompact_body_of_revolution
import Submission.Commons.Geometry.Ulam.interior_nonempty_body_of_revolution
import Submission.Commons.Geometry.Ulam.strictConvex_body_of_revolution

open MeasureTheory
open scoped ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false
set_option linter.style.haveILetI false

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Commons.Geometry.Ulam

/-- The radial profile used for the non-central body of revolution.  It is a cubic
polynomial, strictly concave on `[-1,2]`, vanishing at the endpoints and positive inside. -/
noncomputable def ulamProfile (t : ℝ) : ℝ :=
  (19 / 10 : ℝ) + (23 / 20 : ℝ) * t + (-(17 / 20 : ℝ)) * t ^ 2 +
    (-(1 / 10 : ℝ)) * t ^ 3

lemma ulamProfile_eq_factored (t : ℝ) :
    ulamProfile t = (t + 1) * (2 - t) * (19 / 20 + t / 10) := by
  unfold ulamProfile
  ring_nf

lemma ulamProfile_contDiff : ContDiff ℝ ∞ (fun t : ℝ => ulamProfile t) := by
  unfold ulamProfile
  fun_prop

lemma ulamProfile_continuousOn : ContinuousOn (fun t : ℝ => ulamProfile t) (Set.Icc (-1 : ℝ) 2) :=
  ulamProfile_contDiff.continuous.continuousOn

lemma ulamProfile_zero_left : ulamProfile (-1 : ℝ) = 0 := by
  rw [ulamProfile_eq_factored]
  norm_num

lemma ulamProfile_zero_right : ulamProfile (2 : ℝ) = 0 := by
  rw [ulamProfile_eq_factored]
  norm_num

lemma ulamProfile_nonneg_Icc {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 2) :
    0 ≤ ulamProfile t := by
  rw [ulamProfile_eq_factored]
  have ht1 : -1 ≤ t := ht.1
  have ht2 : t ≤ 2 := ht.2
  have h1 : 0 ≤ t + 1 := by linarith
  have h2 : 0 ≤ 2 - t := by linarith
  have h3 : 0 ≤ 19 / 20 + t / 10 := by nlinarith
  positivity

lemma ulamProfile_pos_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 2) :
    0 < ulamProfile t := by
  rw [ulamProfile_eq_factored]
  have ht1 : -1 < t := ht.1
  have ht2 : t < 2 := ht.2
  have h1 : 0 < t + 1 := by linarith
  have h2 : 0 < 2 - t := by linarith
  have h3 : 0 < 19 / 20 + t / 10 := by nlinarith
  positivity

lemma ulamProfile_deriv (t : ℝ) :
    deriv (fun x : ℝ => ulamProfile x) t =
      (23 / 20 : ℝ) + (-(17 / 10 : ℝ)) * t + (-(3 / 10 : ℝ)) * t ^ 2 := by
  unfold ulamProfile
  conv_lhs =>
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
  simp [deriv_const, deriv_id'', deriv_fun_pow]
  ring_nf

lemma ulamProfile_deriv2 (t : ℝ) :
    deriv^[2] ulamProfile t = -(17 / 10 : ℝ) + (-(3 / 5 : ℝ)) * t := by
  change deriv (deriv ulamProfile) t = _
  have hd : deriv ulamProfile = fun t =>
      (23 / 20 : ℝ) + (-(17 / 10 : ℝ)) * t + (-(3 / 10 : ℝ)) * t ^ 2 := by
    ext t
    exact ulamProfile_deriv t
  rw [hd]
  conv_lhs =>
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
  simp [deriv_const, deriv_id'', deriv_fun_pow]
  ring_nf

lemma ulamProfile_deriv2_neg {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 2) :
    deriv^[2] ulamProfile t < 0 := by
  rw [ulamProfile_deriv2]
  have ht1 : -1 ≤ t := ht.1
  have ht2 : t ≤ 2 := ht.2
  nlinarith

lemma ulamProfile_strictConcaveOn :
    StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 2) ulamProfile := by
  refine strictConcaveOn_of_deriv2_neg' (convex_Icc _ _) ulamProfile_continuousOn ?_
  intro t ht
  exact ulamProfile_deriv2_neg ht

/-- The compactly supported radial function used in the statement. -/
noncomputable def ulamF (t : ℝ) : ℝ :=
  if t ∈ Set.Icc (-1 : ℝ) 2 then ulamProfile t else 0

lemma ulamF_support_subset : Function.support ulamF ⊆ Set.Icc (-1 : ℝ) 2 := by
  rw [Function.support_subset_iff']
  intro t ht
  dsimp [ulamF]
  exact if_neg ht

lemma ulamF_eq_profile_of_mem {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 2) :
    ulamF t = ulamProfile t := by
  dsimp [ulamF]
  exact if_pos ht

lemma ulamF_contDiffOn : ContDiffOn ℝ ∞ ulamF (Set.Ioo (-1 : ℝ) 2) := by
  refine (ulamProfile_contDiff.contDiffOn).congr ?_
  intro t ht
  exact ulamF_eq_profile_of_mem (Set.Ioo_subset_Icc_self ht)

lemma ulamF_continuousOn : ContinuousOn ulamF (Set.Icc (-1 : ℝ) 2) := by
  refine (ulamProfile_contDiff.continuous.continuousOn).congr ?_
  intro t ht
  exact ulamF_eq_profile_of_mem ht

lemma ulamF_concaveOn : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 2) ulamF := by
  refine ulamProfile_strictConcaveOn.concaveOn.congr ?_
  intro t ht
  exact (ulamF_eq_profile_of_mem ht).symm

lemma ulamF_strictConcaveOn : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 2) ulamF := by
  refine ulamProfile_strictConcaveOn.congr ?_
  intro t ht
  exact (ulamF_eq_profile_of_mem ht).symm

lemma ulamF_nonneg_Icc {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 2) : 0 ≤ ulamF t := by
  rw [ulamF_eq_profile_of_mem ht]
  exact ulamProfile_nonneg_Icc ht

lemma ulamF_pos_Ioo {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 2) : 0 < ulamF t := by
  rw [ulamF_eq_profile_of_mem (Set.Ioo_subset_Icc_self ht)]
  exact ulamProfile_pos_Ioo ht

lemma ulamF_zero_left : ulamF (-1 : ℝ) = 0 := by
  rw [ulamF_eq_profile_of_mem (by norm_num [Set.mem_Icc])]
  exact ulamProfile_zero_left

lemma ulamF_zero_right : ulamF (2 : ℝ) = 0 := by
  rw [ulamF_eq_profile_of_mem (by norm_num [Set.mem_Icc])]
  exact ulamProfile_zero_right

/-- The index `1` in `Fin d` is not `0` when `3 ≤ d`. -/
lemma fin_one_ne_zero_of_three_le {d : ℕ} [NeZero d] (hd : 3 ≤ d) : (1 : Fin d) ≠ 0 := by
  intro h
  have hval : ((1 : Fin d) : ℕ) = ((0 : Fin d) : ℕ) := congrArg Fin.val h
  norm_num [Fin.val_one, Fin.val_zero] at hval
  omega

lemma fin_one_pos_of_three_le {d : ℕ} [NeZero d] (hd : 3 ≤ d) : 0 < (1 : Fin d) := by
  rw [Fin.pos_iff_ne_zero]
  exact fin_one_ne_zero_of_three_le hd

/-- The body of revolution generated by `ulamF`. -/
def ulamBody (d : ℕ) [NeZero d] : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x 0 ∈ Set.Icc (-1 : ℝ) 2 ∧ ∑ i > 0, (x i)^2 ≤ (ulamF (x 0))^2}

/-- The point with first coordinate `1` and tail `c` on the first tail basis vector. -/
noncomputable def ulamBoundaryPoint {d : ℕ} [NeZero d] (c : ℝ) : EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single (0 : Fin d) (1 : ℝ) + EuclideanSpace.single (1 : Fin d) c

lemma ulamBoundaryPoint_zero {d : ℕ} [NeZero d] (hd : 3 ≤ d) (c : ℝ) :
    (ulamBoundaryPoint c) (0 : Fin d) = 1 := by
  dsimp [ulamBoundaryPoint]
  simp [fin_one_ne_zero_of_three_le hd]

lemma ulamBoundaryPoint_tail_sum {d : ℕ} [NeZero d] (hd : 3 ≤ d) (c : ℝ) :
    (∑ i ∈ Finset.Ioi (0 : Fin d), ((ulamBoundaryPoint c) i)^2) = c^2 := by
  classical
  dsimp [ulamBoundaryPoint]
  have h0zero : ∀ i ∈ Finset.Ioi (0 : Fin d),
      (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) i = 0 := by
    intro i hi
    dsimp [EuclideanSpace.single]
    simp [Pi.single_apply]
    intro h
    have hlt : 0 < i := (Finset.mem_Ioi.mp hi)
    rw [h] at hlt
    exact lt_irrefl _ hlt
  calc
    (∑ i ∈ Finset.Ioi (0 : Fin d),
        ((EuclideanSpace.single (0 : Fin d) (1 : ℝ)) i +
          (EuclideanSpace.single (1 : Fin d) c) i)^2)
        = ∑ i ∈ Finset.Ioi (0 : Fin d),
            (((EuclideanSpace.single (0 : Fin d) (1 : ℝ)) i)^2 +
              2 * (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) i *
                (EuclideanSpace.single (1 : Fin d) c) i +
              ((EuclideanSpace.single (1 : Fin d) c) i)^2) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hz := h0zero i hi
          rw [hz]
          ring
    _ = ∑ i ∈ Finset.Ioi (0 : Fin d), ((EuclideanSpace.single (1 : Fin d) c) i)^2 := by
          apply Finset.sum_congr rfl
          intro i hi
          have hz := h0zero i hi
          rw [hz]
          ring
    _ = c^2 := by
          rw [Finset.sum_eq_single_of_mem (1 : Fin d) (by simp [fin_one_pos_of_three_le hd])]
          · dsimp [EuclideanSpace.single]
            simp
          · intro b hb hb1
            dsimp [EuclideanSpace.single]
            simp [hb1]

lemma ulamBoundaryPoint_tail_sum' {d : ℕ} [NeZero d] (hd : 3 ≤ d) (c : ℝ) :
    (∑ i ∈ Finset.Ioi (0 : Fin d), ((ulamBoundaryPoint c) i)^2) = c^2 := by
  simpa using ulamBoundaryPoint_tail_sum hd c

lemma single_zero_tail_sum {d : ℕ} [NeZero d] (t : ℝ) :
    (∑ i ∈ Finset.Ioi (0 : Fin d), ((EuclideanSpace.single (0 : Fin d) t) i)^2) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi_ne : i ≠ 0 := by
    intro h
    have hlt : 0 < i := (Finset.mem_Ioi.mp hi)
    rw [h] at hlt
    exact lt_irrefl _ hlt
  have hsingle : (EuclideanSpace.single (0 : Fin d) t) i = 0 := by
    dsimp [EuclideanSpace.single]
    simp [hi_ne]
  rw [hsingle]
  simp

lemma mem_ulamBody_single_zero {d : ℕ} [NeZero d] {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 2) :
    EuclideanSpace.single (0 : Fin d) t ∈ ulamBody d := by
  constructor
  · dsimp [EuclideanSpace.single]
    simpa using ht
  · have hsum := single_zero_tail_sum (d := d) t
    change (∑ i ∈ Finset.Ioi (0 : Fin d), ((EuclideanSpace.single (0 : Fin d) t) i)^2) ≤
      (ulamF (EuclideanSpace.single (0 : Fin d) t (0 : Fin d)))^2
    rw [hsum]
    dsimp [EuclideanSpace.single]
    exact sq_nonneg (ulamF t)

lemma mem_ulamBody_boundaryPoint_one {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    ulamBoundaryPoint (ulamProfile 1) ∈ ulamBody d := by
  constructor
  · rw [ulamBoundaryPoint_zero hd]
    norm_num [Set.mem_Icc]
  · have hsum := ulamBoundaryPoint_tail_sum' (d := d) hd (ulamProfile 1)
    change (∑ i ∈ Finset.Ioi (0 : Fin d), ((ulamBoundaryPoint (ulamProfile 1)) i)^2) ≤
      (ulamF ((ulamBoundaryPoint (ulamProfile 1)) (0 : Fin d)))^2
    rw [hsum]
    rw [ulamBoundaryPoint_zero hd]
    have hf : ulamF 1 = ulamProfile 1 := ulamF_eq_profile_of_mem (by norm_num [Set.mem_Icc])
    rw [hf]

lemma ulamProfile_zero_val : ulamProfile 0 = 19 / 10 := by
  unfold ulamProfile
  norm_num

lemma ulamProfile_one_val : ulamProfile 1 = 21 / 10 := by
  unfold ulamProfile
  norm_num

lemma mem_reflect_of_central_symm {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {p : E} (h : s - {p} = -(s - {p})) {x : E} (hx : x ∈ s) :
    (2 : ℝ) • p - x ∈ s := by
  have h1 : x - p ∈ s - {p} := by
    refine ⟨x, hx, p, ?_, rfl⟩
    simp
  have h2 : -(x - p) ∈ -(s - {p}) := by
    rw [Set.mem_neg]
    simpa using h1
  have h3 : -(x - p) ∈ s - {p} := by
    rw [h]
    exact h2
  rcases h3 with ⟨y, hy, z, hz, hy_eq⟩
  simp at hz
  subst z
  have hy_eq' : y - p = p - x := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hy_eq
  have hy_main : y = (2 : ℝ) • p - x := by
    rw [show (2 : ℝ) • p = p + p by simp [two_smul]]
    calc
      y = (y - p) + p := by abel_nf
      _ = (p - x) + p := by rw [hy_eq']
      _ = p + (p - x) := by abel_nf
      _ = p + p - x := by abel_nf
  simpa [hy_main] using hy

lemma not_centrally_symmetric_ulamBody {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    ¬ ∃ p : EuclideanSpace ℝ (Fin d), ulamBody d - {p} = -(ulamBody d - {p}) := by
  rintro ⟨p, hp⟩
  let vneg : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (0 : Fin d) (-1 : ℝ)
  let vpos : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (0 : Fin d) 2
  have hvneg : vneg ∈ ulamBody d := by
    dsimp [vneg]
    apply mem_ulamBody_single_zero
    norm_num [Set.mem_Icc]
  have hvpos : vpos ∈ ulamBody d := by
    dsimp [vpos]
    apply mem_ulamBody_single_zero
    norm_num [Set.mem_Icc]
  have hreflect : ∀ ⦃x : EuclideanSpace ℝ (Fin d)⦄, x ∈ ulamBody d → (2 : ℝ) • p - x ∈ ulamBody d := by
    intro x hx
    exact mem_reflect_of_central_symm (E := EuclideanSpace ℝ (Fin d)) (s := ulamBody d) hp hx
  have hrneg := hreflect hvneg
  have hrpos := hreflect hvpos
  have hrneg0 : ((2 : ℝ) • p - vneg) (0 : Fin d) = 2 * p 0 + 1 := by
    dsimp [vneg, EuclideanSpace.single]
    simp
  have hrpos0 : ((2 : ℝ) • p - vpos) (0 : Fin d) = 2 * p 0 - 2 := by
    dsimp [vpos, EuclideanSpace.single]
    simp
  have hp0_le : p 0 ≤ 1 / 2 := by
    have h := hrneg.1.2
    nlinarith [hrneg0, h]
  have hp0_ge : 1 / 2 ≤ p 0 := by
    have h := hrpos.1.1
    nlinarith [hrpos0, h]
  have hp0 : p 0 = 1 / 2 := le_antisymm hp0_le hp0_ge
  -- tail zero
  have htail_le : (∑ i ∈ Finset.Ioi (0 : Fin d), (2 * p i)^2) ≤ 0 := by
    have hmem := hrpos.2
    -- hmem : ∑ i > 0, (((2:ℝ) • p - vpos) i)^2 ≤ (ulamF (((2:ℝ) • p - vpos) 0))^2
    change (∑ i ∈ Finset.Ioi (0 : Fin d), (((2 : ℝ) • p - vpos) i)^2) ≤
      (ulamF (((2 : ℝ) • p - vpos) (0 : Fin d)))^2 at hmem
    -- simplify coordinates
    have hcoord : ((2 : ℝ) • p - vpos) (0 : Fin d) = -1 := by
      dsimp [vpos, EuclideanSpace.single]
      rw [hp0]
      norm_num
    have hcoord_tail : ∀ i ∈ Finset.Ioi (0 : Fin d), ((2 : ℝ) • p - vpos) i = 2 * p i := by
      intro i hi
      dsimp [vpos, EuclideanSpace.single]
      have hi_ne : i ≠ 0 := by
        intro h
        have hlt : 0 < i := (Finset.mem_Ioi.mp hi)
        rw [h] at hlt
        exact lt_irrefl _ hlt
      simp [hi_ne]
    rw [hcoord] at hmem
    have hf0 : ulamF (-1 : ℝ) = 0 := by
      dsimp [ulamF]
      rw [if_pos (by norm_num [Set.mem_Icc]), ulamProfile_zero_left]
    rw [hf0] at hmem
    norm_num at hmem
    have hcoord_tail' : ∀ i ∈ Finset.Ioi (0 : Fin d),
        (2 * p i - vpos i)^2 = (2 * p i)^2 := by
      intro i hi
      have hi_ne : i ≠ 0 := by
        intro h
        have hlt : 0 < i := (Finset.mem_Ioi.mp hi)
        rw [h] at hlt
        exact lt_irrefl _ hlt
      have hvpos : vpos i = 0 := by
        dsimp [vpos, EuclideanSpace.single]
        simp [hi_ne]
      rw [hvpos]
      ring
    simpa [Finset.sum_congr rfl hcoord_tail'] using hmem
  have hnonneg : ∀ i ∈ Finset.Ioi (0 : Fin d), 0 ≤ (2 * p i)^2 := by
    intro i hi; positivity
  have hsum_eq : (∑ i ∈ Finset.Ioi (0 : Fin d), (2 * p i)^2) = 0 :=
    le_antisymm htail_le (Finset.sum_nonneg hnonneg)
  have hterms : ∀ i ∈ Finset.Ioi (0 : Fin d), (2 * p i)^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_eq
  have hp_tail : ∀ i, i ≠ 0 → p i = 0 := by
    intro i hi
    have hi_mem : i ∈ Finset.Ioi (0 : Fin d) := by
      rw [Finset.mem_Ioi]
      exact Fin.pos_iff_ne_zero.mpr hi
    have hterm := hterms i hi_mem
    have htwo : 2 * p i = 0 := sq_eq_zero_iff.mp hterm
    nlinarith
  -- contradiction using boundary point at first coordinate 1
  let c : ℝ := ulamProfile 1
  let w : EuclideanSpace ℝ (Fin d) := ulamBoundaryPoint c
  have hw : w ∈ ulamBody d := by
    dsimp [w, c]
    apply mem_ulamBody_boundaryPoint_one hd
  have hr := hreflect hw
  have hr0 : ((2 : ℝ) • p - w) (0 : Fin d) = 0 := by
    have hw0 : w 0 = 1 := by
      dsimp [w]
      exact ulamBoundaryPoint_zero hd c
    rw [PiLp.sub_apply, PiLp.smul_apply, hw0, hp0]
    norm_num
  have hrtail : (∑ i ∈ Finset.Ioi (0 : Fin d), (((2 : ℝ) • p - w) i)^2) = c^2 := by
    have hcoord : ∀ i ∈ Finset.Ioi (0 : Fin d), ((2 : ℝ) • p - w) i = - (w i) := by
      intro i hi
      dsimp [w, ulamBoundaryPoint, EuclideanSpace.single]
      have hi_ne : i ≠ 0 := by
        intro h
        have hlt : 0 < i := (Finset.mem_Ioi.mp hi)
        rw [h] at hlt
        exact lt_irrefl _ hlt
      rw [hp_tail i hi_ne]
      simp [hi_ne]
    calc
      (∑ i ∈ Finset.Ioi (0 : Fin d), (((2 : ℝ) • p - w) i)^2)
          = ∑ i ∈ Finset.Ioi (0 : Fin d), (w i)^2 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hcoord i hi]
              ring
      _ = c^2 := by
              dsimp [w]
              apply ulamBoundaryPoint_tail_sum' hd c
  have hmem_tail : (∑ i ∈ Finset.Ioi (0 : Fin d), (((2 : ℝ) • p - w) i)^2) ≤
      (ulamF (((2 : ℝ) • p - w) (0 : Fin d)))^2 := by
    simpa using hr.2
  rw [hr0] at hmem_tail
  have hf0 : ulamF 0 = ulamProfile 0 := ulamF_eq_profile_of_mem (by norm_num [Set.mem_Icc])
  rw [hf0, ulamProfile_zero_val] at hmem_tail
  rw [hrtail] at hmem_tail
  have hc_sq_gt : (19 / 10 : ℝ)^2 < c^2 := by
    dsimp [c]
    rw [ulamProfile_one_val]
    norm_num
  nlinarith


lemma noncentral_strict_convex_body_of_revolution (hd : 3 ≤ d) : letI : NeZero d := ⟨by omega⟩
    ∃ R₁ R₂ : ℝ, ∃ f : ℝ → ℝ,
      f.support ⊆ Set.Icc (-R₁) R₂ ∧
      ContDiffOn ℝ ∞ f (Set.Ioo (-R₁) R₂) ∧
      ConcaveOn ℝ (Set.Icc (-R₁) R₂) f ∧
      let K : Set ℝᵈ := {x | x 0 ∈ Set.Icc (-R₁) R₂ ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
      StrictConvex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧
      ¬ ∃ p : ℝᵈ, K - {p} = -(K - {p}) := by
  haveI : NeZero d := ⟨by omega⟩
  refine ⟨1, 2, ulamF, ulamF_support_subset, ulamF_contDiffOn, ulamF_concaveOn, ?_⟩
  change StrictConvex ℝ (ulamBody d) ∧ IsCompact (ulamBody d) ∧
    (interior (ulamBody d)).Nonempty ∧
    ¬ ∃ p : ℝᵈ, ulamBody d - {p} = -(ulamBody d - {p})
  constructor
  · exact strictConvex_body_of_revolution (d := d) (R₁ := 1) (R₂ := 2) (f := ulamF)
      (fun t ht => ulamF_nonneg_Icc ht) ulamF_strictConcaveOn ulamF_continuousOn
      ulamF_zero_left ulamF_zero_right (fun t ht => ulamF_pos_Ioo ht)
  · constructor
    · exact isCompact_body_of_revolution (d := d) (R₁ := 1) (R₂ := 2) (f := ulamF)
        ulamF_continuousOn
    · constructor
      · exact interior_nonempty_body_of_revolution (d := d) (R₁ := 1) (R₂ := 2)
          (f := ulamF) (by norm_num) ulamF_contDiffOn.continuousOn
          (fun t ht => ulamF_pos_Ioo ht)
      · exact not_centrally_symmetric_ulamBody hd

end Commons.Geometry.Ulam
