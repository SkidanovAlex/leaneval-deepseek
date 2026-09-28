import Mathlib
import Submission.Work.HP.DN.Defs
import Submission.Work.HP.DN.ConeAux
import Submission.Work.HP.tau_basic
import Submission.Work.HP.evaldefs
import Submission.Work.HP.eval_bounds

/-!
# `Work.HP.DN.realSolCone_facts_alt`

The real-soluble cone `realSolCone d n = {t | ∃ x ≠ 0, formEvalR d n t x = 0}` is closed, positively
scale-invariant, and the frontier of its intersection with the Euclidean unit ball is null.

The route here (the one in the statement's comment) is:

* for `d` odd the cone is the whole space: `f(-x) = -f(x)` and the intermediate value theorem on the
  great circle `θ ↦ cos θ • e₀ + sin θ • e₂` give a nonzero zero;
* for `d` even the complement of the cone is the union of the two convex cones `posCone` and
  `negCone` of forms that are strictly positive (resp. negative) on the punctured space (a form with
  a strictly negative and a strictly positive value on nonzero inputs has a nonzero zero by the
  intermediate value theorem on the segment joining the two points, which cannot pass through the
  origin because an even form does not change sign under `x ↦ -x`).  Hence
  `frontier cone ⊆ frontier posCone ∪ frontier negCone`, a union of null sets by
  `Convex.addHaar_frontier`, and the frontier of the Euclidean unit ball is null for the same
  convexity reason; `frontier (s ∩ t) ⊆ frontier s ∪ frontier t` finishes the argument.

Closedness does not need the parity split: `realSolCone` is the set of coefficient vectors with a
zero on the Euclidean unit sphere, which is the projection along the compact sphere of a closed
subset of a product (`Work.HP.isClosed_IPt_aux`), and scaling by a positive constant identifies the
two formulations.
-/

set_option autoImplicit false

noncomputable section

open Filter Finset MeasureTheory Pointwise

namespace Work.HP.DN

open Work.HP

/-! ## Elementary helpers -/

private lemma frontier_union_subset_aux {α : Type*} [TopologicalSpace α] (s t : Set α) :
    frontier (s ∪ t) ⊆ frontier s ∪ frontier t :=
  (frontier_union_subset s t).trans
    (Set.union_subset_union Set.inter_subset_left Set.inter_subset_right)

private lemma frontier_inter_subset_aux {α : Type*} [TopologicalSpace α] (s t : Set α) :
    frontier (s ∩ t) ⊆ frontier s ∪ frontier t :=
  (frontier_inter_subset s t).trans
    (Set.union_subset_union Set.inter_subset_left Set.inter_subset_right)

/-- An even power of a nonzero real number is positive. -/
private lemma pow_pos_of_even_aux {d : ℕ} (heven : Even d) {c : ℝ} (hc : c ≠ 0) :
    0 < c ^ d := by
  obtain ⟨k, hk⟩ := heven
  rw [hk, pow_add, ← pow_two]
  exact sq_pos_of_ne_zero (pow_ne_zero k hc)

private lemma rNorm_inv_smul_of_ne_zero {n : ℕ} {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) :
    rNorm ((rNorm x)⁻¹ • x) = 1 := by
  have hne : rNorm x ≠ 0 := fun h => hx (rNorm_eq_zero.mp h)
  have hpos : 0 < rNorm x := lt_of_le_of_ne (rNorm_nonneg x) (Ne.symm hne)
  rw [rNorm_smul', abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hne]

/-! ## The intermediate value input -/

/-- For even `d`, a degree-`d` form taking a strictly negative value at one nonzero point and a
strictly positive value at another has a nonzero real zero: on the segment joining the two points
the form changes sign, and the segment cannot pass through the origin, since `f_t(c • x) =
c ^ d * f_t x` with `d` even forces equal signs on a line through the origin. -/
private lemma exists_zero_of_signs_aux (d n : ℕ) (heven : Even d) (t : Mon d n → ℝ)
    {x y : Fin (n + 1) → ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : formEvalR d n t x < 0) (h2 : 0 < formEvalR d n t y) :
    ∃ z : Fin (n + 1) → ℝ, z ≠ 0 ∧ formEvalR d n t z = 0 := by
  -- `x` and `y` are linearly independent: on the line `ℝ x` the form keeps the sign of `f_t x`
  have hind : ∀ c : ℝ, y ≠ c • x := by
    intro c hc
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [zero_smul] at hc
      exact hy hc
    · have hv : formEvalR d n t y = c ^ d * formEvalR d n t x := by
        rw [hc, formEvalR_homogeneous]
      have hp : 0 < c ^ d := pow_pos_of_even_aux heven hc0
      have hmul : c ^ d * formEvalR d n t x < 0 := mul_neg_of_pos_of_neg hp h1
      rw [hv] at h2
      linarith
  have hcont : Continuous fun s : ℝ => formEvalR d n t ((1 - s) • x + s • y) :=
    (continuous_formEvalR_vec d n t).comp (by fun_prop)
  have hmem : (0 : ℝ) ∈ Set.Icc (formEvalR d n t ((1 - (0 : ℝ)) • x + (0 : ℝ) • y))
      (formEvalR d n t ((1 - (1 : ℝ)) • x + (1 : ℝ) • y)) := by
    have e0 : formEvalR d n t ((1 - (0 : ℝ)) • x + (0 : ℝ) • y) = formEvalR d n t x := by simp
    have e1 : formEvalR d n t ((1 - (1 : ℝ)) • x + (1 : ℝ) • y) = formEvalR d n t y := by simp
    rw [e0, e1]
    exact ⟨le_of_lt h1, le_of_lt h2⟩
  obtain ⟨s, hs, hszero⟩ :=
    (intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn) hmem
  refine ⟨(1 - s) • x + s • y, ?_, hszero⟩
  intro hzero
  have hs0 : 0 < s := by
    rcases lt_or_eq_of_le hs.1 with h | h
    · exact h
    · exfalso
      rw [h.symm, zero_smul, add_zero, sub_zero, one_smul] at hzero
      exact hx hzero
  have hs1 : s < 1 := by
    rcases lt_or_eq_of_le hs.2 with h | h
    · exact h
    · exfalso
      rw [h, sub_self, zero_smul, one_smul, zero_add] at hzero
      exact hy hzero
  have hsy : s • y = -((1 - s) • x) := by
    have h := add_eq_zero_iff_eq_neg.mp hzero
    rw [h, neg_neg]
  have hy_eq : y = (-(s⁻¹ * (1 - s))) • x := by
    calc y = (1 : ℝ) • y := (one_smul _ _).symm
      _ = (s⁻¹ * s) • y := by rw [inv_mul_cancel₀ (ne_of_gt hs0)]
      _ = s⁻¹ • (s • y) := by rw [smul_smul]
      _ = s⁻¹ • (-((1 - s) • x)) := by rw [hsy]
      _ = (-(s⁻¹ * (1 - s))) • x := by rw [smul_neg, smul_smul, ← neg_smul]
  exact hind _ hy_eq

/-- For even `d`, a form with no nonzero zero cannot take values of both strict signs. -/
private lemma no_opposite_signs_aux (d n : ℕ) (heven : Even d) {t : Mon d n → ℝ}
    (hne : ∀ x : Fin (n + 1) → ℝ, x ≠ 0 → formEvalR d n t x ≠ 0) :
    ¬ ∃ x y : Fin (n + 1) → ℝ, x ≠ 0 ∧ y ≠ 0 ∧
      formEvalR d n t x < 0 ∧ 0 < formEvalR d n t y := by
  rintro ⟨x, y, hx, hy, h1, h2⟩
  obtain ⟨z, hz, hfz⟩ := exists_zero_of_signs_aux d n heven t hx hy h1 h2
  exact hne z hz hfz

/-! ## The two convex cones and the complement of the real-soluble cone -/

private lemma convex_unitBallR_aux {ι : Type*} [Fintype ι] : Convex ℝ (unitBallR ι) := by
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  simp only [unitBallR, Set.mem_setOf_eq] at hx hy ⊢
  have h1 : rNorm (a • x + b • y) ≤ a * rNorm x + b * rNorm y := by
    refine (rNorm_add_le _ _).trans ?_
    rw [rNorm_smul', rNorm_smul', abs_of_pos ha, abs_of_pos hb]
  have h2 : a * rNorm x + b * rNorm y ≤ 1 := by
    have := add_le_add (mul_le_mul_of_nonneg_left hx ha.le) (mul_le_mul_of_nonneg_left hy hb.le)
    rw [mul_one, mul_one, hab] at this
    exact this
  linarith

private lemma convex_posCone_aux (d n : ℕ) : Convex ℝ (posCone d n) := by
  rw [convex_iff_forall_pos]
  intro t ht t' ht' a b ha hb hab
  intro x hx
  have hcomp : formEvalR d n (a • t + b • t') x
      = a * formEvalR d n t x + b * formEvalR d n t' x := by
    rw [formEvalR_add_coeff, formEvalR_smul, formEvalR_smul]
  rw [hcomp]
  have h1 := ht x hx
  have h2 := ht' x hx
  nlinarith [mul_pos ha h1, mul_pos hb h2]

private lemma convex_negCone_aux (d n : ℕ) : Convex ℝ (negCone d n) := by
  rw [convex_iff_forall_pos]
  intro t ht t' ht' a b ha hb hab
  intro x hx
  have hcomp : formEvalR d n (a • t + b • t') x
      = a * formEvalR d n t x + b * formEvalR d n t' x := by
    rw [formEvalR_add_coeff, formEvalR_smul, formEvalR_smul]
  rw [hcomp]
  have h1 := ht x hx
  have h2 := ht' x hx
  have ha1 : a * formEvalR d n t x < 0 := mul_neg_of_pos_of_neg ha h1
  have hb2 : b * formEvalR d n t' x < 0 := mul_neg_of_pos_of_neg hb h2
  linarith

/-- For even `d` the complement of the real-soluble cone is the union of the two convex cones of
forms that are strictly positive, resp. strictly negative, on the punctured space. -/
private lemma realSolCone_compl_eq_cones (d n : ℕ) (heven : Even d) :
    (realSolCone d n)ᶜ = posCone d n ∪ negCone d n := by
  ext t
  constructor
  · intro ht
    have hne : ∀ x : Fin (n + 1) → ℝ, x ≠ 0 → formEvalR d n t x ≠ 0 :=
      fun x hx hf => ht ⟨x, hx, hf⟩
    obtain ⟨x₀, hx₀⟩ := exists_ne_zero_vec n
    rcases lt_or_gt_of_ne (hne x₀ hx₀) with hlt | hgt
    · right
      intro x hx
      rcases lt_trichotomy (formEvalR d n t x) 0 with h | h | h
      · exact h
      · exact absurd h (hne x hx)
      · exact absurd ⟨x₀, x, hx₀, hx, hlt, h⟩ (no_opposite_signs_aux d n heven hne)
    · left
      intro x hx
      rcases lt_trichotomy (formEvalR d n t x) 0 with h | h | h
      · exact absurd ⟨x, x₀, hx, hx₀, h, hgt⟩ (no_opposite_signs_aux d n heven hne)
      · exact absurd h (hne x hx)
      · exact h
  · rintro (ht | ht)
    · intro hcon
      obtain ⟨x, hx, hf⟩ := hcon
      exact absurd hf (ne_of_gt (ht x hx))
    · intro hcon
      obtain ⟨x, hx, hf⟩ := hcon
      exact absurd hf (ne_of_lt (ht x hx))

/-! ## The odd case: the cone is everything -/

private lemma realSolCone_eq_univ_of_odd_aux (d n : ℕ) (hn : 1 ≤ n) (hodd : Odd d) :
    realSolCone d n = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  let i₀ : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  let i₁ : Fin (n + 1) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by
    intro h
    have h2 : (0 : ℕ) = 1 := congrArg Fin.val h
    exact absurd h2 (by norm_num)
  let e₀ : Fin (n + 1) → ℝ := Pi.single i₀ 1
  let e₁ : Fin (n + 1) → ℝ := Pi.single i₁ 1
  have hcoord₀ : ∀ θ : ℝ, (Real.cos θ • e₀ + Real.sin θ • e₁) i₀ = Real.cos θ := by
    intro θ
    simp [e₀, e₁, h01]
  have hcoord₁ : ∀ θ : ℝ, (Real.cos θ • e₀ + Real.sin θ • e₁) i₁ = Real.sin θ := by
    intro θ
    simp [e₀, e₁, Ne.symm h01]
  have hne : ∀ θ : ℝ, Real.cos θ • e₀ + Real.sin θ • e₁ ≠ 0 := by
    intro θ hzero
    have hc : Real.cos θ = 0 := by rw [← hcoord₀ θ]; exact congrFun hzero i₀
    have hs : Real.sin θ = 0 := by rw [← hcoord₁ θ]; exact congrFun hzero i₁
    have hsq := Real.cos_sq_add_sin_sq θ
    rw [hc, hs] at hsq
    norm_num at hsq
  have hcont : Continuous fun θ : ℝ => formEvalR d n t (Real.cos θ • e₀ + Real.sin θ • e₁) :=
    (continuous_formEvalR_vec d n t).comp
      ((Real.continuous_cos.smul continuous_const).add
        (Real.continuous_sin.smul continuous_const))
  have h0 : formEvalR d n t (Real.cos 0 • e₀ + Real.sin 0 • e₁) = formEvalR d n t e₀ := by simp
  have hπ : formEvalR d n t (Real.cos Real.pi • e₀ + Real.sin Real.pi • e₁)
      = -formEvalR d n t e₀ := by
    have hvec : Real.cos Real.pi • e₀ + Real.sin Real.pi • e₁ = -e₀ := by
      rw [Real.cos_pi, Real.sin_pi]; simp
    rw [hvec, show (-e₀ : Fin (n + 1) → ℝ) = (-1 : ℝ) • e₀ from (neg_one_smul ℝ e₀).symm,
      formEvalR_homogeneous, hodd.neg_one_pow, neg_one_mul]
  by_cases hle : formEvalR d n t e₀ ≤ 0
  · have hmem : (0 : ℝ) ∈ Set.Icc (formEvalR d n t (Real.cos 0 • e₀ + Real.sin 0 • e₁))
        (formEvalR d n t (Real.cos Real.pi • e₀ + Real.sin Real.pi • e₁)) := by
      rw [h0, hπ]
      exact ⟨hle, neg_nonneg.mpr hle⟩
    obtain ⟨θ, -, hθg⟩ :=
      (intermediate_value_Icc Real.pi_pos.le hcont.continuousOn) hmem
    exact ⟨Real.cos θ • e₀ + Real.sin θ • e₁, hne θ, hθg⟩
  · have hgt : 0 < formEvalR d n t e₀ := not_le.mp hle
    have hmem : (0 : ℝ) ∈ Set.Icc (formEvalR d n t (Real.cos Real.pi • e₀ + Real.sin Real.pi • e₁))
        (formEvalR d n t (Real.cos 0 • e₀ + Real.sin 0 • e₁)) := by
      rw [h0, hπ]
      exact ⟨by linarith, le_of_lt hgt⟩
    obtain ⟨θ, -, hθg⟩ :=
      (intermediate_value_Icc' Real.pi_pos.le hcont.continuousOn) hmem
    exact ⟨Real.cos θ • e₀ + Real.sin θ • e₁, hne θ, hθg⟩

/-! ## Closedness -/

/-- `realSolCone` is the set of coefficient vectors with a zero on the Euclidean unit sphere. -/
private lemma realSolCone_eq_IPt (d n : ℕ) :
    realSolCone d n = {a : Mon d n → ℝ | IPt d n a} := by
  ext a
  constructor
  · rintro ⟨x, hxne, hx0⟩
    exact ⟨(rNorm x)⁻¹ • x, rNorm_inv_smul_of_ne_zero hxne,
      by rw [formEvalR_homogeneous, hx0, mul_zero]⟩
  · rintro ⟨x, hx1, hx0⟩
    refine ⟨x, ?_, hx0⟩
    intro hzero
    rw [hzero] at hx1
    rw [show rNorm (0 : Fin (n + 1) → ℝ) = 0 from by simp [rNorm]] at hx1
    exact one_ne_zero hx1.symm

private lemma isClosed_realSolCone (d n : ℕ) : IsClosed (realSolCone d n) := by
  rw [realSolCone_eq_IPt]
  exact isClosed_IPt_aux d n

private lemma realSolCone_scale (d n : ℕ) :
    ∀ (s : ℝ) (t : Mon d n → ℝ), 0 < s → (t ∈ realSolCone d n ↔ s • t ∈ realSolCone d n) := by
  intro s t hs
  constructor
  · rintro ⟨x, hx, hf⟩
    exact ⟨x, hx, by rw [formEvalR_smul, hf, mul_zero]⟩
  · rintro ⟨x, hx, hf⟩
    refine ⟨x, hx, ?_⟩
    have h : formEvalR d n (s • t) x = s * formEvalR d n t x := formEvalR_smul d n t x s
    rw [h] at hf
    exact (mul_eq_zero.mp hf).resolve_left (ne_of_gt hs)

/-! ## The main statement -/

/-- The real-soluble cone `realSolCone d n = {t | ∃ x ≠ 0, formEvalR d n t x = 0}` is closed,
positively scale-invariant, and the frontier of its intersection with the Euclidean unit ball is
null. Route: `d` odd gives the whole space (`f t (-x) = -f t x` plus IVT on a great circle), and
the frontier of the unit ball (the Euclidean sphere) is null. For `d` even put
`m t = inf (f t '' sphere)` and `M t = sup (f t '' sphere)`, both continuous in `t`; connectedness
of the sphere and IVT give `realSolCone d n = {t | m t ≤ 0 ∧ 0 ≤ M t}`, whose interior contains
`{m < 0 ∧ 0 < M}`, so the frontier is inside `{m = 0} ∪ {M = 0} ∪ {rNorm = 1}`. `{M = 0} = -{m = 0}`
since `f (-t) = -f t`. Let `u` be the coefficient vector of `∑ i, X_i ^ d`; then `inf (f u '' sphere) =: c > 0`
and `m (t + s • u) ≥ m t + s * c`, so the translates `{m = 0} + s • u` (`0 < s < 1`) are pairwise
disjoint sets of equal measure inside a fixed ball; a finite subfamily gives `n * volume ≤ volume (ball)`,
hence `volume {t | m t = 0} = 0` (using positive scale-invariance of `{m = 0}` for the radii).-/
theorem realSolCone_facts_alt (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) :
    IsClosed (realSolCone d n) ∧
    (∀ (s : ℝ) (t : Mon d n → ℝ), 0 < s → (t ∈ realSolCone d n ↔ s • t ∈ realSolCone d n)) ∧
    volume (frontier (realSolCone d n ∩ unitBallR (Mon d n))) = 0 := by
  haveI : (volume : Measure (Mon d n → ℝ)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi (Mon d n)
  refine ⟨isClosed_realSolCone d n, realSolCone_scale d n, ?_⟩
  rcases Nat.even_or_odd d with heven | hodd
  · have hC : realSolCone d n = (posCone d n ∪ negCone d n)ᶜ := by
      rw [← realSolCone_compl_eq_cones d n heven, compl_compl]
    have hfront : volume (frontier (realSolCone d n)) = 0 := by
      rw [hC, frontier_compl]
      refine measure_mono_null (frontier_union_subset_aux _ _) ?_
      exact measure_union_null
        (Convex.addHaar_frontier (μ := volume) (convex_posCone_aux d n))
        (Convex.addHaar_frontier (μ := volume) (convex_negCone_aux d n))
    have hball : volume (frontier (unitBallR (Mon d n))) = 0 :=
      Convex.addHaar_frontier (μ := volume) (convex_unitBallR_aux (ι := Mon d n))
    exact measure_mono_null (frontier_inter_subset_aux _ _)
      (measure_union_null hfront hball)
  · have hC : realSolCone d n = Set.univ := realSolCone_eq_univ_of_odd_aux d n hn hodd
    rw [hC, Set.univ_inter]
    exact Convex.addHaar_frontier (μ := volume) (convex_unitBallR_aux (ι := Mon d n))

end Work.HP.DN
