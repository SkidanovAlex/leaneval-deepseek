import Mathlib

/-!
# The genericity engine of the linear class rows: analytic non-vanishing conditions are dense

`Work.Drive.classRowsLin_openDense` asks for an open set of design parameters, dense at every point of
the closed unit ball, on which five class-level rows (expressed by non-vanishing conditions on the
*transported linear plane charts*) hold.  Every one of those rows is, after transport, a conjunction
of conditions of the form `f ≠ 0` for an explicit function `f : 𝔼¹² → ℝ` that is

* *analytic* (it is a determinant, or an inner product against a normal, of vectors that depend
  *affinely* on the parameter — `classEquiv τ = 1 + classGen τ` is affine in `τ`), and
* *not identically zero*, with an explicit witness: at the **diagonal** `t = 0` (where all three
  transports are trivial) the untransported lemmas (`Work.Drive.linIncidence_linBase`, the general
  position of `linBase A`) hold.

This file provides the two lemmas that convert such data into the required open dense-at-ball set.
The engine is the *identity principle* for analytic functions
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`): an everywhere-analytic function which
vanishes on a ball vanishes identically, so its non-vanishing set is dense — and open, by continuity.
-/

namespace Work.Drive

open scoped Topology

noncomputable section

/-- **Density at every point of the closed unit ball.** -/
def DenseAtBall {n : ℕ} (R : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ → ∃ y, y ∈ R ∧ ‖y - x‖ < δ

/-- **A point of the closed unit ball has strictly interior points arbitrarily close to it.** -/
theorem exists_norm_lt_one_near {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) : ∃ x' : EuclideanSpace ℝ (Fin n), ‖x'‖ < 1 ∧ ‖x' - x‖ < δ := by
  by_cases h : ‖x‖ < 1
  · exact ⟨x, h, by rw [sub_self, norm_zero]; exact hδ⟩
  · have h1 : ‖x‖ = 1 := le_antisymm hx (not_lt.mp h)
    set ε : ℝ := min (δ / 2) (1 / 2) with hεdef
    have hεpos : 0 < ε := lt_min (by linarith) (by norm_num)
    have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    refine ⟨(1 - ε) • x, ?_, ?_⟩
    · have hnorm : ‖((1 - ε : ℝ))‖ = 1 - ε := by
        rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [norm_smul, hnorm, h1, mul_one]
      linarith
    · have hsub : (1 - ε) • x - x = (-ε) • x := by
        rw [sub_smul, one_smul]
        module
      have hnorm : ‖((-ε : ℝ))‖ = ε := by
        rw [Real.norm_eq_abs, abs_neg, abs_of_pos hεpos]
      rw [hsub, norm_smul, hnorm, h1, mul_one]
      linarith

/-- **The non-vanishing set of a nowhere-locally-zero function is dense, at every point.**  If `f` is
analytic everywhere and `f x₀ ≠ 0` for some `x₀`, then every ball contains a point at which `f` does
not vanish.  (Otherwise `f = 0` on a ball, hence — by the identity principle on the connected space
`𝔼ⁿ` — `f = 0` everywhere.) -/
theorem exists_near_ne_zero_of_analyticAt {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ x, AnalyticAt ℝ f x) (h : ∃ x, f x ≠ 0) (x : EuclideanSpace ℝ (Fin n)) {ε : ℝ}
    (hε : 0 < ε) : ∃ y, ‖y - x‖ < ε ∧ f y ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hball : f =ᶠ[𝓝 x] 0 := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x hε) ?_
    intro y hy
    exact hcon y (by rwa [Metric.mem_ball, dist_eq_norm] at hy)
  have heq : Set.EqOn f 0 Set.univ :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (fun y _ => hf y)
      (fun y _ => analyticAt_const) isPreconnected_univ (Set.mem_univ x) hball
  obtain ⟨x₀, hx₀⟩ := h
  exact hx₀ (by simpa using heq (Set.mem_univ x₀))

/-- **The non-vanishing set of an everywhere-analytic, not identically zero function is open and
dense at every point of the closed unit ball.**  This is the form consumed by the row producers: any
finite *conjunction* of such conditions is again open and dense-at-ball, and so is any *disjunction*
(a union of such sets). -/
theorem isOpen_denseAtBall_ne_zero {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ∀ x, AnalyticAt ℝ f x) (h : ∃ x, f x ≠ 0) :
    IsOpen {x | f x ≠ 0} ∧ DenseAtBall {x | f x ≠ 0} := by
  have hcont : Continuous f :=
    continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  refine ⟨isOpen_ne_fun hcont continuous_const, fun x _ ε hε => ?_⟩
  obtain ⟨y, hy, hyf⟩ := exists_near_ne_zero_of_analyticAt hf h x hε
  exact ⟨y, hyf, hy⟩


/-- **A finite family of open sets dense at every point of the closed unit ball has a common point in
every ball around any point of the *open* unit ball.**  (The induction keeps every intermediate point
inside the ball `B (x, (1 - ‖x‖)/2) ⊆ closedBall 0 1`, where the density hypothesis is available.)
This is the self-contained form (only `Mathlib` is imported, so the module is clash-free) of the
combination step of the row producers: conjunctions of non-vanishing conditions. -/
theorem exists_mem_iInter_near_of_denseAtBall {n : ℕ} {ι : Type*} [Fintype ι]
    {R : ι → Set (EuclideanSpace ℝ (Fin n))} (hopen : ∀ i, IsOpen (R i))
    (hdense : ∀ i, DenseAtBall (R i)) {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1)
    (ε : ℝ) (hε : 0 < ε) : ∃ y, ‖y - x‖ < ε ∧ ∀ i, y ∈ R i := by
  classical
  set r : ℝ := (1 - ‖x‖) / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hxr : ‖x‖ + r < 1 := by rw [hrdef]; linarith
  set ε₁ : ℝ := min ε r with hε₁def
  have hε₁pos : 0 < ε₁ := lt_min hε hrpos
  have hε₁ε : ε₁ ≤ ε := min_le_left _ _
  have hε₁r : ε₁ ≤ r := min_le_right _ _
  have key : ∀ S : Finset ι, ∃ y, ‖y - x‖ < ε₁ ∧ ∀ i ∈ S, y ∈ R i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨x, by simpa using hε₁pos, by simp⟩
    | insert i S hi ih =>
        obtain ⟨y, hyx, hyS⟩ := ih
        have hy1 : ‖y‖ ≤ 1 := by
          have h : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
            have h2 := norm_add_le (y - x) x
            rwa [sub_add_cancel] at h2
          linarith
        have hOpenS : IsOpen (⋂ j ∈ S, R j) := isOpen_biInter_finset (fun j _ => hopen j)
        have hyMem : y ∈ ⋂ j ∈ S, R j := Set.mem_iInter₂.mpr hyS
        obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ := Metric.isOpen_iff.mp hOpenS y hyMem
        obtain ⟨y', hy'P, hy'y⟩ := hdense i y hy1 (min δ₂ (ε₁ - ‖y - x‖))
          (lt_min hδ₂pos (by linarith))
        refine ⟨y', ?_, ?_⟩
        · have h1 : ‖y' - y‖ < ε₁ - ‖y - x‖ := lt_of_lt_of_le hy'y (min_le_right _ _)
          have h2 : ‖y' - x‖ ≤ ‖y' - y‖ + ‖y - x‖ := by
            have h3 := norm_add_le (y' - y) (y - x)
            rwa [sub_add_sub_cancel] at h3
          linarith
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hjS
          · exact hy'P
          · have hmem : y' ∈ ⋂ j ∈ S, R j := hδ₂sub (by
              rw [Metric.mem_ball, dist_eq_norm]
              exact lt_of_lt_of_le hy'y (min_le_left _ _))
            exact Set.mem_iInter₂.mp hmem j hjS
  obtain ⟨y, hy, hyall⟩ := key Finset.univ
  exact ⟨y, lt_of_lt_of_le hy hε₁ε, fun i => hyall i (Finset.mem_univ i)⟩

end

end Work.Drive
