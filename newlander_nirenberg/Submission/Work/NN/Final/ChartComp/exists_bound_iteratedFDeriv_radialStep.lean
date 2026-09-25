import Mathlib
import Submission.Work.NN.Final.Chart

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

namespace Work.NN.Final.ChartComp

/-! ## Auxiliary lemmas

The radial cutoff `radialStep a b` is a fixed smooth function of one real variable which is
constant on a left ray and on a right ray.  In this file we show that any such function has
uniformly bounded iterated derivatives (this is the content of
`exists_bound_iteratedFDeriv_of_eventuallyConst`), and then specialise it to `radialStep`.
-/

/-- If `f : ℝ → F` agrees with a constant function in a neighbourhood of `x`, then all its
iterated differentials of order `≥ 1` at `x` vanish. -/
theorem iteratedFDeriv_eq_zero_of_eventually_eq_const {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F} {c : F} {x : ℝ} {m : ℕ}
    (hm : m ≠ 0) (hf : f =ᶠ[𝓝 x] fun _ => c) :
    iteratedFDeriv ℝ m f x = 0 := by
  rcases hf.exists_mem with ⟨u, hu_mem, hEqOn⟩
  rcases mem_nhds_iff.mp hu_mem with ⟨v, hv_sub, hv_open, hxv⟩
  have hEqOnv : EqOn f (fun _ => c) v := fun y hy => hEqOn (hv_sub hy)
  have h1 : iteratedFDerivWithin ℝ m f v x = iteratedFDerivWithin ℝ m f univ x := by
    simpa using iteratedFDerivWithin_inter_open (𝕜 := ℝ) (f := f) (s := (univ : Set ℝ))
      (n := m) hv_open hxv
  rw [← iteratedFDerivWithin_univ, ← h1, iteratedFDerivWithin_congr hEqOnv hxv m]
  simp [iteratedFDerivWithin_const_of_ne hm c v]

/-- A smooth function `f : ℝ → ℝ` which is constant on a left ray and on a right ray has
uniformly bounded iterated derivatives. -/
theorem exists_bound_iteratedFDeriv_of_eventuallyConst {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {A B cA cB : ℝ}
    (hA : ∀ r ≤ A, f r = cA) (hB : ∀ r ≥ B, f r = cB) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (m : ℕ) (r : ℝ), ‖iteratedFDeriv ℝ m f r‖ ≤ C m := by
  have hbound : ∀ m : ℕ, ∃ M : ℝ, ∀ r ∈ Icc (min A B) (max A B),
      ‖iteratedFDeriv ℝ m f r‖ ≤ M := fun m =>
    (isCompact_Icc (a := min A B) (b := max A B)).exists_bound_of_continuousOn
      ((hf.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).continuousOn)
  choose M hM using hbound
  have hMnonneg : ∀ m, 0 ≤ max (M m) (max ‖cA‖ ‖cB‖) := fun m =>
    le_trans (norm_nonneg cA)
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have hCpos : ∀ m, 0 < max (M m) (max ‖cA‖ ‖cB‖) + 1 := fun m => by
    have := hMnonneg m; linarith
  have hCbigA : ∀ m, ‖cA‖ ≤ max (M m) (max ‖cA‖ ‖cB‖) + 1 := fun m =>
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_add_of_nonneg_right zero_le_one)
  have hCbigB : ∀ m, ‖cB‖ ≤ max (M m) (max ‖cA‖ ‖cB‖) + 1 := fun m =>
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_add_of_nonneg_right zero_le_one)
  have hCbigM : ∀ m, M m ≤ max (M m) (max ‖cA‖ ‖cB‖) + 1 := fun m =>
    le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one)
  refine ⟨fun m => max (M m) (max ‖cA‖ ‖cB‖) + 1, hCpos, ?_⟩
  intro m r
  by_cases hrs : r ∈ Icc (min A B) (max A B)
  · exact le_trans (hM m r hrs) (hCbigM m)
  · rw [Set.mem_Icc] at hrs
    have hr' : r < min A B ∨ max A B < r := by
      rcases not_and_or.mp hrs with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    rcases hr' with hlt | hgt
    · have hrA : r ≤ A := le_trans (le_of_lt hlt) (min_le_left A B)
      have hev : f =ᶠ[𝓝 r] fun _ => cA := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
        exact hA y (le_trans (le_of_lt hy) (min_le_left A B))
      rcases eq_or_ne m 0 with hm | hm
      · rw [hm, norm_iteratedFDeriv_zero, hA r hrA]
        exact hCbigA 0
      · rw [iteratedFDeriv_eq_zero_of_eventually_eq_const hm hev, norm_zero]
        have := hMnonneg m; linarith
    · have hrB : r ≥ B := le_trans (le_max_right A B) (le_of_lt hgt)
      have hev : f =ᶠ[𝓝 r] fun _ => cB := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
        exact hB y (le_trans (le_max_right A B) (le_of_lt hy))
      rcases eq_or_ne m 0 with hm | hm
      · rw [hm, norm_iteratedFDeriv_zero, hB r hrB]
        exact hCbigB 0
      · rw [iteratedFDeriv_eq_zero_of_eventually_eq_const hm hev, norm_zero]
        have := hMnonneg m; linarith

/-! ## The cutoff `radialStep` is eventually constant -/

/-- `radialStep a b` is constant on the left ray `(-∞, min a b]`. -/
theorem radialStep_eq_min (a b : ℝ) :
    ∀ r ≤ min a b, Work.NN.Final.radialStep a b r
      = Work.NN.Final.radialStep a b (min a b) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · intro r hr
    rw [min_eq_left (le_of_lt hab)] at hr ⊢
    rw [Work.NN.Final.radialStep_of_le hab hr, Work.NN.Final.radialStep_of_le hab le_rfl]
  · subst hab
    intro r hr
    simp only [min_self, Work.NN.Final.radialStep, Work.NN.Final.smoothCut,
      sub_self, div_zero]
  · intro r hr
    rw [min_eq_right (le_of_lt hab)] at hr ⊢
    have hb : b - a < 0 := by linarith
    have h1 : 1 ≤ (r - a) / (b - a) := by
      rw [le_div_iff_of_neg hb, one_mul]
      linarith
    have h2 : 1 ≤ (b - a) / (b - a) := by
      rw [div_self (ne_of_lt hb)]
    simp only [Work.NN.Final.radialStep, Work.NN.Final.smoothCut]
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2]

/-- `radialStep a b` is constant on the right ray `[max a b, ∞)`. -/
theorem radialStep_eq_max (a b : ℝ) :
    ∀ r ≥ max a b, Work.NN.Final.radialStep a b r
      = Work.NN.Final.radialStep a b (max a b) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · intro r hr
    rw [max_eq_right (le_of_lt hab)] at hr ⊢
    rw [Work.NN.Final.radialStep_of_ge hab hr, Work.NN.Final.radialStep_of_ge hab le_rfl]
  · subst hab
    intro r hr
    simp only [max_self, Work.NN.Final.radialStep, Work.NN.Final.smoothCut,
      sub_self, div_zero]
  · intro r hr
    rw [max_eq_left (le_of_lt hab)] at hr ⊢
    have hb : b - a < 0 := by linarith
    have h1 : (r - a) / (b - a) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hb)
    have h2 : (a - a) / (b - a) ≤ 0 := by simp
    simp only [Work.NN.Final.radialStep, Work.NN.Final.smoothCut]
    rw [Real.smoothTransition.zero_of_nonpos h1, Real.smoothTransition.zero_of_nonpos h2]

/-! ## The main statement -/

theorem exists_bound_iteratedFDeriv_radialStep (a b : ℝ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (m : ℕ) (r : ℝ), ‖iteratedFDeriv ℝ m (Work.NN.Final.radialStep a b) r‖ ≤ C m := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Final.radialStep a b) := by
    have h : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => (r - a) / (b - a)) := by fun_prop
    exact Work.NN.Final.smoothCut_contDiff.comp h
  exact exists_bound_iteratedFDeriv_of_eventuallyConst hf
    (A := min a b) (B := max a b)
    (cA := Work.NN.Final.radialStep a b (min a b))
    (cB := Work.NN.Final.radialStep a b (max a b))
    (radialStep_eq_min a b) (radialStep_eq_max a b)

end Work.NN.Final.ChartComp
