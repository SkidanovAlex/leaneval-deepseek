import ChallengeDeps
import Submission.FUP.Weight
import Submission.Commons.Analysis.Calculus.cube_bump_deriv_bound
import Submission.Commons.Analysis.Calculus.cube_bump_deriv_bound_uniform
import Submission.Commons.Analysis.Calculus.cube_bump_deriv_bound_uniformW

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators
open Submission.FUP

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# The weight `ω_k` of §6.1

The paper takes a width-`W_k` cube cover of the dyadic annulus `A_k`, a smooth function `η_𝓠`
which is `1` on the inner half of `𝓠` and vanishes outside `𝓠`, and sets

  `ω_k = -(2^k/k^α) · Σ_{𝓠 ∈ 𝓢_{𝕐,k}} η_𝓠`.

This module builds the smooth sum `Ψ_k = Σ_{𝓠 ∈ 𝓢} η_𝓠` and proves its pointwise properties
(`0 ≤ Ψ_k ≤ 3^d`, `Ψ_k ≥ 1` on `Y ∩ A_k`, `supp Ψ_k ⊆ Y_k`).  The derivative estimates are
left to a later stage (they use the uniform bump bound
`Commons.Analysis.Calculus.cube_bump_deriv_bound_uniform`).
-/

/-- Centre of the `j`-th cube of the cover. -/
noncomputable def coverCenter (R W : ℝ) (j : Fin d → ℕ) : ℝᵈ :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => coverCoef R W j i + W / 2)

lemma coverCenter_apply (R W : ℝ) (j : Fin d → ℕ) (i : Fin d) :
    coverCenter R W j i = coverCoef R W j i + W / 2 := by
  have h : (EuclideanSpace.equiv (Fin d) ℝ) (coverCenter R W j)
      = fun i => coverCoef R W j i + W / 2 :=
    (EuclideanSpace.equiv (Fin d) ℝ).apply_symm_apply _
  simpa [equiv_apply] using congrFun h i

lemma mem_coverBoxHalf_iff (R W : ℝ) (j : Fin d → ℕ) (x : ℝᵈ) :
    x ∈ coverBoxHalf R W j ↔
      ∀ i : Fin d, |x i - coverCenter R W j i| ≤ W / 4 := by
  rw [mem_coverBoxHalf]
  constructor
  · intro h i
    rw [coverCenter_apply]
    exact abs_le.mpr ⟨by linarith [(h i).1], by linarith [(h i).2]⟩
  · intro h i
    have h' := h i
    rw [coverCenter_apply] at h'
    exact ⟨by linarith [(abs_le.mp h').1], by linarith [(abs_le.mp h').2]⟩

/-- The uniform derivative constant for the bumps of the cover.  It does **not** depend on the
width `W` of the cube (only on `d`), which is what allows summing the bumps over grids of
different widths with a single derivative constant. -/
noncomputable def coverBumpK (W : ℝ) (hW : 0 < W) : ℕ → ℝ :=
  Classical.choose (Commons.Analysis.Calculus.cube_bump_deriv_bound_uniformW d 3)

lemma coverBumpK_nonneg (W : ℝ) (hW : 0 < W) {a : ℕ} (ha : a ≤ 3) :
    0 ≤ coverBumpK (d := d) W hW a :=
  (Classical.choose_spec (Commons.Analysis.Calculus.cube_bump_deriv_bound_uniformW d 3)).1 a ha

/-- A chosen bump function for the `j`-th cube of the cover, with the *uniform* derivative
bound `K a · W^{-a}`. -/
noncomputable def coverBump (R W : ℝ) (hW : 0 < W) (N : ℕ) (j : Fin d → Fin N) : ℝᵈ → ℝ :=
  Classical.choose ((Classical.choose_spec
    (Commons.Analysis.Calculus.cube_bump_deriv_bound_uniformW d 3)).2
      W hW (coverCenter R W (fun i => (j i : ℕ))))

lemma coverBump_spec (R W : ℝ) (hW : 0 < W) (N : ℕ) (j : Fin d → Fin N) :
    ContDiff ℝ 3 (coverBump R W hW N j) ∧
      (∀ x : ℝᵈ, 0 ≤ coverBump R W hW N j x) ∧
      (∀ x : ℝᵈ, coverBump R W hW N j x ≤ 1) ∧
      (∀ x : ℝᵈ, (∀ i : Fin d,
          |x i - coverCenter R W (fun i => (j i : ℕ)) i| ≤ W / 4) →
        coverBump R W hW N j x = 1) ∧
      (∀ x : ℝᵈ, (∃ i : Fin d,
          W / 2 ≤ |x i - coverCenter R W (fun i => (j i : ℕ)) i|) →
        coverBump R W hW N j x = 0) ∧
      (∀ a ≤ 3, ∀ x, ‖iteratedFDeriv ℝ a (coverBump R W hW N j) x‖
          ≤ coverBumpK (d := d) W hW a * W ^ (-(a : ℝ))) :=
  Classical.choose_spec ((Classical.choose_spec
    (Commons.Analysis.Calculus.cube_bump_deriv_bound_uniformW d 3)).2
      W hW (coverCenter R W (fun i => (j i : ℕ))))

lemma coverBump_contDiff (R W : ℝ) (hW : 0 < W) (N : ℕ) (j : Fin d → Fin N) :
    ContDiff ℝ 3 (coverBump R W hW N j) :=
  (coverBump_spec R W hW N j).1

lemma coverBump_nonneg (R W : ℝ) (hW : 0 < W) (N : ℕ) (j : Fin d → Fin N) (x : ℝᵈ) :
    0 ≤ coverBump R W hW N j x := (coverBump_spec R W hW N j).2.1 x

lemma coverBump_le_one (R W : ℝ) (hW : 0 < W) (N : ℕ) (j : Fin d → Fin N) (x : ℝᵈ) :
    coverBump R W hW N j x ≤ 1 := (coverBump_spec R W hW N j).2.2.1 x

lemma coverBump_eq_one (R W : ℝ) (hW : 0 < W) (N : ℕ) (j : Fin d → Fin N) {x : ℝᵈ}
    (hx : ∀ i : Fin d, |x i - coverCenter R W (fun i => (j i : ℕ)) i| ≤ W / 4) :
    coverBump R W hW N j x = 1 := (coverBump_spec R W hW N j).2.2.2.1 x hx

/-- The bump vanishes outside the cube of the cover. -/
lemma coverBump_eq_zero_of_notMem (R W : ℝ) (hW : 0 < W) (N : ℕ) (j : Fin d → Fin N)
    {x : ℝᵈ} (hx : x ∉ coverBox R W (fun i => (j i : ℕ))) :
    coverBump R W hW N j x = 0 := by
  refine (coverBump_spec R W hW N j).2.2.2.2.1 x ?_
  by_contra h
  push Not at h
  refine hx ?_
  rw [mem_coverBox]
  intro i
  have hci := coverCenter_apply R W (fun i => (j i : ℕ)) i
  have hlt : |x i - coverCenter R W (fun i => (j i : ℕ)) i| < W / 2 := h i
  rw [abs_lt] at hlt
  constructor <;> linarith [hlt.1, hlt.2, hci]

/-- The iterated derivatives of the bumps also vanish outside the corresponding cube. -/
lemma iteratedFDeriv_coverBump_eq_zero_of_notMem (R W : ℝ) (hW : 0 < W) (N : ℕ)
    (j : Fin d → Fin N) {x : ℝᵈ} (hx : x ∉ coverBox R W (fun i => (j i : ℕ))) (a : ℕ) :
    iteratedFDeriv ℝ a (coverBump R W hW N j) x = 0 := by
  have hs : IsOpen ((coverBox R W (fun i => (j i : ℕ)))ᶜ) :=
    (isClosed_coverBox R W _).isOpen_compl
  have hx' : x ∈ (coverBox R W (fun i => (j i : ℕ)))ᶜ := hx
  have h1 : iteratedFDerivWithin ℝ a (coverBump R W hW N j)
      ((coverBox R W (fun i => (j i : ℕ)))ᶜ) x
      = iteratedFDeriv ℝ a (coverBump R W hW N j) x :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) a hs) hx'
  have h2 : Set.EqOn (coverBump R W hW N j) (0 : ℝᵈ → ℝ)
      ((coverBox R W (fun i => (j i : ℕ)))ᶜ) :=
    fun y hy => coverBump_eq_zero_of_notMem R W hW N j hy
  have h3 : iteratedFDerivWithin ℝ a (coverBump R W hW N j)
      ((coverBox R W (fun i => (j i : ℕ)))ᶜ) x
      = iteratedFDerivWithin ℝ a (0 : ℝᵈ → ℝ)
        ((coverBox R W (fun i => (j i : ℕ)))ᶜ) x :=
    iteratedFDerivWithin_congr h2 hx' a
  rw [← h1, h3, iteratedFDerivWithin_zero]
  rfl

lemma norm_iteratedFDeriv_coverBump_le (R W : ℝ) (hW : 0 < W) (N : ℕ)
    (j : Fin d → Fin N) {a : ℕ} (ha : a ≤ 3) (x : ℝᵈ) :
    ‖iteratedFDeriv ℝ a (coverBump R W hW N j) x‖
      ≤ coverBumpK (d := d) W hW a * W ^ (-(a : ℝ)) :=
  (coverBump_spec R W hW N j).2.2.2.2.2 a ha x

/-- The sum of the bump functions over the cubes meeting `Y ∩ A`. -/
noncomputable def psiK (R W : ℝ) (hW : 0 < W) (N : ℕ) (Y A : Set ℝᵈ) : ℝᵈ → ℝ :=
  fun x => ∑ j ∈ (Finset.univ.filter (fun j : Fin d → Fin N =>
      (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)), coverBump R W hW N j x

lemma psiK_nonneg (R W : ℝ) (hW : 0 < W) (N : ℕ) (Y A : Set ℝᵈ) (x : ℝᵈ) :
    0 ≤ psiK R W hW N Y A x :=
  Finset.sum_nonneg fun j _ => coverBump_nonneg R W hW N j x

lemma psiK_contDiff (R W : ℝ) (hW : 0 < W) (N : ℕ) (Y A : Set ℝᵈ) :
    ContDiff ℝ 3 (psiK R W hW N Y A) :=
  ContDiff.sum fun j _ => coverBump_contDiff R W hW N j

/-- `Ψ_k ≤ 3^d`: at most `3^d` cubes of the grid contain a given point. -/
lemma psiK_le (R W : ℝ) (hW : 0 < W) (N : ℕ) (Y A : Set ℝᵈ) (x : ℝᵈ) :
    psiK R W hW N Y A x ≤ 3 ^ d := by
  have h1 : psiK R W hW N Y A x
      ≤ ∑ j ∈ (Finset.univ.filter (fun j : Fin d → Fin N =>
          (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
          (if x ∈ coverBox R W (fun i => (j i : ℕ)) then (1:ℝ) else 0) := by
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : x ∈ coverBox R W (fun i => (j i : ℕ))
    · rw [if_pos hj]; exact coverBump_le_one R W hW N j x
    · rw [if_neg hj]
      rw [coverBump_eq_zero_of_notMem R W hW N j hj]
  have h2 : (∑ j ∈ (Finset.univ.filter (fun j : Fin d → Fin N =>
          (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
          (if x ∈ coverBox R W (fun i => (j i : ℕ)) then (1:ℝ) else 0))
      ≤ 3 ^ d := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h3 : ((Finset.univ.filter (fun j : Fin d → Fin N =>
          (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)).filter
          (fun j : Fin d → Fin N => x ∈ coverBox R W (fun i => (j i : ℕ)))).card ≤ 3 ^ d := by
      refine le_trans (Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.subset_univ _))) ?_
      rw [← Fintype.card_subtype]
      have h5 := card_coverBox_le R W hW N x
      rwa [Nat.card_eq_fintype_card] at h5
    exact_mod_cast h3
  exact le_trans h1 h2

/-- `Ψ_k ≥ 1` on `Y ∩ A`, provided the inner halves of the cubes cover `A`. -/
lemma one_le_psiK {R W a : ℝ} (hW : 0 < W) {N : ℕ} (hN : 0 < N)
    (h1 : a + W / 4 ≤ R) (h2 : a + R ≤ (N : ℝ) * (W / 2)) {Y A : Set ℝᵈ}
    (hA : A ⊆ cube (-a) a) {x : ℝᵈ} (hx : x ∈ Y ∩ A) :
    1 ≤ psiK R W hW N Y A x := by
  have hxpi : x ∈ cube (-a) a := hA hx.2
  have hmem : x ∈ ⋃ j : Fin d → Fin N, coverBoxHalf R W (fun i => (j i : ℕ)) :=
    pi_Icc_subset_iUnion_coverBoxHalf hW hN h1 h2 hxpi
  rcases Set.mem_iUnion.mp hmem with ⟨j, hj⟩
  have hS : (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty :=
    ⟨x, coverBoxHalf_subset_coverBox (le_of_lt hW) _ hj, hx⟩
  have hmem' : j ∈ (Finset.univ.filter (fun j : Fin d → Fin N =>
      (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, hS⟩
  have hone : coverBump R W hW N j x = 1 := by
    refine coverBump_eq_one R W hW N j fun i => ?_
    have := (mem_coverBoxHalf_iff R W (fun i => (j i : ℕ)) x).mp hj i
    rwa [coverCenter_apply] at this
  calc (1:ℝ) = coverBump R W hW N j x := hone.symm
    _ ≤ psiK R W hW N Y A x := Finset.single_le_sum
        (fun i _ => coverBump_nonneg R W hW N i x) hmem'

/-- The support of `Ψ_k` is contained in `Y_k`. -/
lemma psiK_eq_zero_of_notMem_yCover (R W : ℝ) (hW : 0 < W) (N : ℕ) (Y A : Set ℝᵈ) {x : ℝᵈ}
    (hx : x ∉ yCover R W N Y A) : psiK R W hW N Y A x = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_filter] at hj
  by_contra hne
  exact hx ⟨j, hj.2, by
    by_contra hcon
    exact hne (coverBump_eq_zero_of_notMem R W hW N j hcon)⟩

/-- **Regularity of `Ψ_k`.**  The `a`-th iterated derivative of `Ψ_k` is bounded by
`3^d · K_a · W^{-a}`, uniformly in `x` and in the set `Y`.  This is the estimate
`|D^a ω_k| ≲ W_k^{-a} 2^k k^{-α}` of §6.1. -/
lemma norm_iteratedFDeriv_psiK_le (R W : ℝ) (hW : 0 < W) (N : ℕ) (Y A : Set ℝᵈ)
    {a : ℕ} (ha : a ≤ 3) (x : ℝᵈ) :
    ‖iteratedFDeriv ℝ a (psiK R W hW N Y A) x‖
      ≤ (3 ^ d : ℝ) * coverBumpK (d := d) W hW a * W ^ (-(a : ℝ)) := by
  classical
  have hcd : ∀ j ∈ (Finset.univ.filter (fun j : Fin d → Fin N =>
      (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
      ContDiff ℝ a (coverBump R W hW N j) :=
    fun j _ => (coverBump_contDiff R W hW N j).of_le (by exact_mod_cast ha)
  have hpsi : psiK R W hW N Y A = fun x =>
      ∑ j ∈ (Finset.univ.filter (fun j : Fin d → Fin N =>
        (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
        coverBump R W hW N j x := rfl
  rw [hpsi, iteratedFDeriv_sum hcd, Finset.sum_apply]
  have hcnonneg : 0 ≤ coverBumpK (d := d) W hW a * W ^ (-(a : ℝ)) :=
    mul_nonneg (coverBumpK_nonneg W hW ha) (Real.rpow_nonneg (le_of_lt hW) _)
  calc ‖∑ j ∈ (Finset.univ.filter (fun j : Fin d → Fin N =>
          (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
          iteratedFDeriv ℝ a (coverBump R W hW N j) x‖
      ≤ ∑ j ∈ (Finset.univ.filter (fun j : Fin d → Fin N =>
          (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)),
          ‖iteratedFDeriv ℝ a (coverBump R W hW N j) x‖ := norm_sum_le _ _
    _ = ∑ j ∈ ((Finset.univ.filter (fun j : Fin d → Fin N =>
          (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)).filter
            (fun j : Fin d → Fin N => x ∈ coverBox R W (fun i => (j i : ℕ)))),
          ‖iteratedFDeriv ℝ a (coverBump R W hW N j) x‖ := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro j hjS hjnot
        have hP : x ∉ coverBox R W (fun i => (j i : ℕ)) := by
          intro hx
          exact hjnot (Finset.mem_filter.mpr ⟨hjS, hx⟩)
        rw [iteratedFDeriv_coverBump_eq_zero_of_notMem R W hW N j hP a, norm_zero]
    _ ≤ ∑ _j ∈ ((Finset.univ.filter (fun j : Fin d → Fin N =>
          (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)).filter
            (fun j : Fin d → Fin N => x ∈ coverBox R W (fun i => (j i : ℕ)))),
          (coverBumpK (d := d) W hW a * W ^ (-(a : ℝ))) :=
        Finset.sum_le_sum fun j _ => norm_iteratedFDeriv_coverBump_le R W hW N j ha x
    _ = (((Finset.univ.filter (fun j : Fin d → Fin N =>
          (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)).filter
            (fun j : Fin d → Fin N => x ∈ coverBox R W (fun i => (j i : ℕ)))).card : ℝ)
          * (coverBumpK (d := d) W hW a * W ^ (-(a : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 ^ d : ℝ) * (coverBumpK (d := d) W hW a * W ^ (-(a : ℝ))) := by
        have hcard : (((Finset.univ.filter (fun j : Fin d → Fin N =>
              (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)).filter
                (fun j : Fin d → Fin N => x ∈ coverBox R W (fun i => (j i : ℕ)))).card : ℝ)
            ≤ (3 ^ d : ℝ) := by
          have h3 : ((Finset.univ.filter (fun j : Fin d → Fin N =>
                (coverBox R W (fun i => (j i : ℕ)) ∩ (Y ∩ A)).Nonempty)).filter
                  (fun j : Fin d → Fin N => x ∈ coverBox R W (fun i => (j i : ℕ)))).card
              ≤ 3 ^ d := by
            refine le_trans (Finset.card_le_card
              (Finset.filter_subset_filter _ (Finset.subset_univ _))) ?_
            rw [← Fintype.card_subtype]
            have h5 := card_coverBox_le R W hW N x
            rwa [Nat.card_eq_fintype_card] at h5
          exact_mod_cast h3
        exact mul_le_mul_of_nonneg_right hcard hcnonneg
    _ = (3 ^ d : ℝ) * coverBumpK (d := d) W hW a * W ^ (-(a : ℝ)) := by ring

end Submission.FUP
