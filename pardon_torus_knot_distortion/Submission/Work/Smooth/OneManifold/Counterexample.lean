import Mathlib
import Submission.Work.Smooth.OneManifold.Basic

/-!
# The literal target is false: the figure eight

`Work.Smooth.Morse.CompactOneManifoldInput ψ` claims that every compact `Z` with
`Work.Smooth.Morse.IsLocalArc ψ Z` is a finite disjoint union of embedded circles of the surface
`F = torus ψ`.  That statement is **false**: the hypothesis `IsLocalArc` allows the neighbourhood
`U = Set.univ`, so it holds for `Z = Set.range γ` for every injective continuous `γ : ℝ → ℝ³`
(`Work.Smooth.OneManifold.isLocalArc_range_of_injective_continuous`), and such a `Z` need not be a
circle union.

The witness here is the **figure eight**: two unit circles tangent at a point, placed in the plane
`z = 100` so that it misses the surface.  It is the image of the injective continuous lemniscate
parametrisation

`γ t = (2 |cos θ| cos θ, 2 |cos θ| sin θ, 100)`,   `θ = π/2 + 2 arctan t`,

whose two branches trace the two circles minus the tangency point `(0,0,100)`, that point being
`γ 0`.

## Main results

* `figureEightParam_range` — the range of `γ` is the figure eight;
* `figureEightParam_injective` — `γ` is injective;
* `figureEight_isCompact` — the figure eight is compact;
* `exists_compact_isLocalArc_not_isCircleUnion` — a compact `IsLocalArc` set which is not a circle
  union;
* `not_compactOneManifoldInput` — the literal statement `∀ ψ, CompactOneManifoldInput ψ` is false.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

/-! ## The auxiliary curve -/

/-- The identity diffeomorphism of `ℝ³`. -/
def idDiffeo : Submission.Diffeo where
  toFun := id
  invFun := id
  smooth_toFun := contDiff_id
  smooth_invFun := contDiff_id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The angle parameter of the lemniscate: a homeomorphism `ℝ → (-π/2, 3π/2)`. -/
def figTheta (t : ℝ) : ℝ := Real.pi / 2 + 2 * Real.arctan t

theorem figTheta_strictMono : StrictMono figTheta := by
  intro a b hab
  have h := Real.arctan_lt_arctan_iff.mpr hab
  simp only [figTheta]
  linarith

theorem figTheta_injective : Function.Injective figTheta := figTheta_strictMono.injective

theorem figTheta_mem (t : ℝ) : figTheta t ∈ Set.Ioo (-(Real.pi / 2)) (3 * Real.pi / 2) := by
  have h1 := Real.arctan_lt_pi_div_two t
  have h2 := Real.neg_pi_div_two_lt_arctan t
  constructor <;> simp only [figTheta] <;> linarith

/-- The lemniscate point of angle `θ`, i.e. `(2 |cos θ| cos θ, 2 |cos θ| sin θ, 100)`. -/
def figPoint (θ : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then 2 * |Real.cos θ| * Real.cos θ
    else if i.val = 1 then 2 * |Real.cos θ| * Real.sin θ
    else 100)

@[simp] theorem figPoint_apply_zero (θ : ℝ) :
    figPoint θ 0 = 2 * |Real.cos θ| * Real.cos θ := by
  rw [figPoint, WithLp.ofLp_toLp]
  simp

@[simp] theorem figPoint_apply_one (θ : ℝ) :
    figPoint θ 1 = 2 * |Real.cos θ| * Real.sin θ := by
  rw [figPoint, WithLp.ofLp_toLp]
  simp

@[simp] theorem figPoint_apply_two (θ : ℝ) : figPoint θ 2 = 100 := by
  rw [figPoint, WithLp.ofLp_toLp]
  simp

theorem continuous_figPoint : Continuous figPoint := by
  have h : Continuous (fun θ : ℝ => fun i : Fin 3 =>
      (if i.val = 0 then 2 * |Real.cos θ| * Real.cos θ
       else if i.val = 1 then 2 * |Real.cos θ| * Real.sin θ else 100 : ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp h

/-- The figure-eight parametrisation. -/
def figureEightParam (t : ℝ) : R3 := figPoint (figTheta t)

@[simp] theorem figureEightParam_apply_zero (t : ℝ) :
    figureEightParam t 0 = 2 * |Real.cos (figTheta t)| * Real.cos (figTheta t) := rfl

@[simp] theorem figureEightParam_apply_one (t : ℝ) :
    figureEightParam t 1 = 2 * |Real.cos (figTheta t)| * Real.sin (figTheta t) := rfl

@[simp] theorem figureEightParam_apply_two (t : ℝ) : figureEightParam t 2 = 100 := rfl

theorem continuous_figureEightParam : Continuous figureEightParam :=
  continuous_figPoint.comp (by unfold figTheta; fun_prop)

/-! ## The two branches in double-angle form -/

theorem two_mul_cos_sq (θ : ℝ) : 2 * Real.cos θ * Real.cos θ = 1 + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]; ring

theorem two_mul_cos_sin (θ : ℝ) : 2 * Real.cos θ * Real.sin θ = Real.sin (2 * θ) := by
  rw [Real.sin_two_mul]; ring

theorem cos_eq_one_sub_two_sin_sq (w : ℝ) : Real.cos w = 1 - 2 * Real.sin (w / 2) * Real.sin (w / 2) := by
  have h := Real.sin_sq_add_cos_sq (w / 2)
  have h2 := Real.cos_two_mul (w / 2)
  rw [show 2 * (w / 2) = w from by ring] at h2
  nlinarith [h, h2]

theorem sin_eq_two_sin_mul_cos (w : ℝ) : Real.sin w = 2 * Real.sin (w / 2) * Real.cos (w / 2) := by
  have h2 := Real.sin_two_mul (w / 2)
  rw [show 2 * (w / 2) = w from by ring] at h2
  exact h2

/-! ## The figure eight as a set -/

/-- The figure eight: the union of the circles of radius `1` with centres `(1,0,100)` and
`(-1,0,100)`, tangent at `(0,0,100)`. -/
def figureEight : Set R3 :=
  {p | p 2 = 100 ∧ (((p 0 - 1) ^ 2 + (p 1) ^ 2 = 1) ∨ ((p 0 + 1) ^ 2 + (p 1) ^ 2 = 1))}

theorem mem_figureEight {p : R3} :
    p ∈ figureEight ↔
      p 2 = 100 ∧ (((p 0 - 1) ^ 2 + (p 1) ^ 2 = 1) ∨ ((p 0 + 1) ^ 2 + (p 1) ^ 2 = 1)) :=
  Iff.rfl

theorem figureEight_subset_ball : figureEight ⊆ Metric.closedBall (0 : R3) 101 := by
  intro p hp
  rw [mem_figureEight] at hp
  obtain ⟨h2, h | h⟩ := hp
  · have hx : (p 0) ^ 2 ≤ 4 := by nlinarith [h, sq_nonneg (p 1 : ℝ)]
    have hy : (p 1) ^ 2 ≤ 1 := by nlinarith [h, sq_nonneg (p 0 - 1 : ℝ)]
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnorm : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
      simp [Real.norm_eq_abs, sq_abs]
    have hz : (p 2) ^ 2 = 100 ^ 2 := by rw [h2]
    have h101 : ‖p‖ ≤ 101 := by nlinarith [norm_nonneg p]
    simpa using h101
  · have hx : (p 0) ^ 2 ≤ 4 := by nlinarith [h, sq_nonneg (p 1 : ℝ)]
    have hy : (p 1) ^ 2 ≤ 1 := by nlinarith [h, sq_nonneg (p 0 + 1 : ℝ)]
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnorm : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
      simp [Real.norm_eq_abs, sq_abs]
    have hz : (p 2) ^ 2 = 100 ^ 2 := by rw [h2]
    have h101 : ‖p‖ ≤ 101 := by nlinarith [norm_nonneg p]
    simpa using h101

theorem figureEight_isCompact : IsCompact figureEight := by
  have hclosed : IsClosed figureEight := by
    have h1 : IsClosed {p : R3 | p 2 = 100} :=
      isClosed_eq (by fun_prop) continuous_const
    have h2 : IsClosed {p : R3 | (p 0 - 1) ^ 2 + (p 1) ^ 2 = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    have h3 : IsClosed {p : R3 | (p 0 + 1) ^ 2 + (p 1) ^ 2 = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    have h4 : figureEight = ({p : R3 | p 2 = 100} ∩ {p : R3 | (p 0 - 1) ^ 2 + (p 1) ^ 2 = 1}) ∪
        ({p : R3 | p 2 = 100} ∩ {p : R3 | (p 0 + 1) ^ 2 + (p 1) ^ 2 = 1}) := by
      ext p
      simp only [mem_figureEight, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
      tauto
    rw [h4]
    exact (h1.inter h2).union (h1.inter h3)
  exact (Metric.isCompact_iff_isClosed_bounded).mpr
    ⟨hclosed, Metric.isBounded_closedBall.subset figureEight_subset_ball⟩

/-! ## The unit circle -/

theorem exists_cos_sin_eq {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = b := by
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have ha : -1 ≤ a ∧ a ≤ 1 := by
    have := (sq_le_one_iff_abs_le_one (a := a)).mp ha2
    rwa [abs_le] at this
  rcases lt_or_ge b 0 with hb | hb
  · refine ⟨-Real.arccos a, by rw [Real.cos_neg, Real.cos_arccos ha.1 ha.2], ?_⟩
    rw [Real.sin_neg, Real.sin_arccos]
    have h1 : 1 - a ^ 2 = b ^ 2 := by linarith
    rw [h1, Real.sqrt_sq_eq_abs, abs_of_neg hb]
    ring
  · refine ⟨Real.arccos a, Real.cos_arccos ha.1 ha.2, ?_⟩
    rw [Real.sin_arccos]
    have h1 : 1 - a ^ 2 = b ^ 2 := by linarith
    rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonneg hb]

/-- The angle of a unit vector, taken in an interval `(c, c + 2π)` of length `2π`. -/
theorem exists_cos_sin_eq_Ioo_of {a b c : ℝ} (h : a ^ 2 + b ^ 2 = 1)
    (hne : ¬ (Real.cos c = a ∧ Real.sin c = b)) :
    ∃ θ ∈ Set.Ioo c (c + 2 * Real.pi), Real.cos θ = a ∧ Real.sin θ = b := by
  obtain ⟨θ₀, hc, hs⟩ := exists_cos_sin_eq h
  set n : ℤ := ⌊(θ₀ - c) / (2 * Real.pi)⌋ with hn
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 : (n : ℝ) * (2 * Real.pi) ≤ θ₀ - c := by
    have hf : (n : ℝ) ≤ (θ₀ - c) / (2 * Real.pi) := by
      rw [hn]; exact Int.floor_le _
    have := mul_le_mul_of_nonneg_right hf (le_of_lt h2π)
    rwa [div_mul_cancel₀ _ (ne_of_gt h2π)] at this
  have h2 : θ₀ - c < ((n : ℝ) + 1) * (2 * Real.pi) := by
    have hf : (θ₀ - c) / (2 * Real.pi) < ((n : ℝ) + 1) := by
      rw [hn]; exact Int.lt_floor_add_one _
    have := mul_lt_mul_of_pos_right hf h2π
    rwa [div_mul_cancel₀ _ (ne_of_gt h2π)] at this
  refine ⟨θ₀ - (n : ℝ) * (2 * Real.pi), ?_, ?_, ?_⟩
  · have h3 : c ≤ θ₀ - (n : ℝ) * (2 * Real.pi) := by linarith
    have h4 : θ₀ - (n : ℝ) * (2 * Real.pi) < c + 2 * Real.pi := by linarith
    have h5 : θ₀ - (n : ℝ) * (2 * Real.pi) ≠ c := by
      intro heq
      apply hne
      constructor
      · rw [← hc, ← heq]
        exact Real.cos_sub_int_mul_two_pi θ₀ n
      · rw [← hs, ← heq]
        exact Real.sin_sub_int_mul_two_pi θ₀ n
    exact ⟨lt_of_le_of_ne h3 (Ne.symm h5), h4⟩
  · rw [Real.cos_sub_int_mul_two_pi]; exact hc
  · rw [Real.sin_sub_int_mul_two_pi]; exact hs

/-! ## The two branches of the parametrisation -/

theorem figureEightParam_first {u : ℝ} (hu : u ∈ Set.Ioo (-Real.pi) Real.pi) :
    figureEightParam (Real.tan ((u - Real.pi) / 4)) =
      WithLp.toLp 2 (fun i : Fin 3 =>
        if i.val = 0 then 1 + Real.cos u else if i.val = 1 then Real.sin u else 100) := by
  have h1 : -(Real.pi / 2) < (u - Real.pi) / 4 := by linarith [hu.1]
  have h2 : (u - Real.pi) / 4 < Real.pi / 2 := by linarith [hu.2]
  have hth : figTheta (Real.tan ((u - Real.pi) / 4)) = u / 2 := by
    unfold figTheta
    rw [Real.arctan_tan h1 h2]
    ring
  have hpos : 0 < Real.cos (u / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hu.1], by linarith [hu.2]⟩
  apply WithLp.ofLp_injective
  funext i
  simp only [figureEightParam, hth, WithLp.ofLp_toLp]
  fin_cases i
  · show (figPoint (u / 2)).ofLp (0 : Fin 3) = (1 : ℝ) + Real.cos u
    rw [figPoint_apply_zero, abs_of_pos hpos, two_mul_cos_sq,
      show 2 * (u / 2) = u from by ring]
  · show (figPoint (u / 2)).ofLp (1 : Fin 3) = Real.sin u
    rw [figPoint_apply_one, abs_of_pos hpos, two_mul_cos_sin,
      show 2 * (u / 2) = u from by ring]
  · show (figPoint (u / 2)).ofLp (2 : Fin 3) = (100 : ℝ)
    rw [figPoint_apply_two]

theorem figureEightParam_second {w : ℝ} (hw : w ∈ Set.Ioo 0 (2 * Real.pi)) :
    figureEightParam (Real.tan (w / 4)) =
      WithLp.toLp 2 (fun i : Fin 3 =>
        if i.val = 0 then -1 + Real.cos w else if i.val = 1 then Real.sin w else 100) := by
  have h1 : -(Real.pi / 2) < w / 4 := by linarith [hw.1, Real.pi_pos]
  have h2 : w / 4 < Real.pi / 2 := by linarith [hw.2, Real.pi_pos]
  have hth : figTheta (Real.tan (w / 4)) = (w + Real.pi) / 2 := by
    unfold figTheta
    rw [Real.arctan_tan h1 h2]
    ring
  have hcos : Real.cos ((w + Real.pi) / 2) = -Real.sin (w / 2) := by
    rw [show (w + Real.pi) / 2 = w / 2 + Real.pi / 2 from by ring, Real.cos_add,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hsin : Real.sin ((w + Real.pi) / 2) = Real.cos (w / 2) := by
    rw [show (w + Real.pi) / 2 = w / 2 + Real.pi / 2 from by ring, Real.sin_add,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hsinpos : 0 < Real.sin (w / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hw.1]) (by linarith [hw.2])
  have hneg : Real.cos ((w + Real.pi) / 2) < 0 := by rw [hcos]; linarith
  have habs : |Real.cos ((w + Real.pi) / 2)| = -Real.cos ((w + Real.pi) / 2) := abs_of_neg hneg
  have hcosw : Real.cos w = 1 - 2 * Real.sin (w / 2) * Real.sin (w / 2) :=
    cos_eq_one_sub_two_sin_sq w
  have hsinw : Real.sin w = 2 * Real.sin (w / 2) * Real.cos (w / 2) :=
    sin_eq_two_sin_mul_cos w
  apply WithLp.ofLp_injective
  funext i
  simp only [figureEightParam, hth, WithLp.ofLp_toLp]
  fin_cases i
  · show (figPoint ((w + Real.pi) / 2)).ofLp (0 : Fin 3) = -1 + Real.cos w
    rw [figPoint_apply_zero, habs, hcos, hcosw]
    ring
  · show (figPoint ((w + Real.pi) / 2)).ofLp (1 : Fin 3) = Real.sin w
    rw [figPoint_apply_one, habs, hcos, hsin, hsinw]
    ring
  · show (figPoint ((w + Real.pi) / 2)).ofLp (2 : Fin 3) = (100 : ℝ)
    rw [figPoint_apply_two]

/-! ## The range -/

theorem range_figureEightParam_subset : Set.range figureEightParam ⊆ figureEight := by
  rintro p ⟨t, rfl⟩
  refine ⟨figureEightParam_apply_two t, ?_⟩
  rcases lt_or_ge (Real.cos (figTheta t)) 0 with hc | hc
  · right
    have h0 : figureEightParam t 0 = -(2 * Real.cos (figTheta t) ^ 2) := by
      rw [figureEightParam_apply_zero, abs_of_neg hc]; ring
    have h1 : figureEightParam t 1 = -(2 * Real.cos (figTheta t) * Real.sin (figTheta t)) := by
      rw [figureEightParam_apply_one, abs_of_neg hc]; ring
    rw [h0, h1]
    nlinarith [Real.sin_sq_add_cos_sq (figTheta t)]
  · left
    have h0 : figureEightParam t 0 = 2 * Real.cos (figTheta t) ^ 2 := by
      rw [figureEightParam_apply_zero, abs_of_nonneg hc]; ring
    have h1 : figureEightParam t 1 = 2 * Real.cos (figTheta t) * Real.sin (figTheta t) := by
      rw [figureEightParam_apply_one, abs_of_nonneg hc]
    rw [h0, h1]
    nlinarith [Real.sin_sq_add_cos_sq (figTheta t)]

theorem figureEight_subset_range : figureEight ⊆ Set.range figureEightParam := by
  intro p hp
  rw [mem_figureEight] at hp
  obtain ⟨h2, hcases⟩ := hp
  rcases hcases with h1 | h1
  · by_cases hzero : p 0 = 0 ∧ p 1 = 0
    · obtain ⟨hx, hy⟩ := hzero
      refine ⟨0, ?_⟩
      apply WithLp.ofLp_injective
      funext i
      simp only [figureEightParam, figTheta, Real.arctan_zero, mul_zero, add_zero, WithLp.ofLp_toLp]
      fin_cases i
      · show (figPoint (Real.pi / 2)).ofLp (0 : Fin 3) = p 0
        rw [figPoint_apply_zero, Real.cos_pi_div_two, abs_zero, mul_zero, hx]
      · show (figPoint (Real.pi / 2)).ofLp (1 : Fin 3) = p 1
        rw [figPoint_apply_one, Real.cos_pi_div_two, abs_zero, mul_zero, zero_mul, hy]
      · show (figPoint (Real.pi / 2)).ofLp (2 : Fin 3) = p 2
        rw [figPoint_apply_two, h2]
    · have hne : ¬ (Real.cos (-Real.pi) = p 0 - 1 ∧ Real.sin (-Real.pi) = p 1) := by
        rintro ⟨hx, hy⟩
        rw [Real.cos_neg, Real.cos_pi] at hx
        rw [Real.sin_neg, Real.sin_pi] at hy
        exact hzero ⟨by linarith, by linarith⟩
      obtain ⟨u, hu, hcu, hsu⟩ := exists_cos_sin_eq_Ioo_of (c := -Real.pi) h1 hne
      have hu' : u ∈ Set.Ioo (-Real.pi) Real.pi := by
        rw [show -Real.pi + 2 * Real.pi = Real.pi from by ring] at hu
        exact hu
      refine ⟨Real.tan ((u - Real.pi) / 4), ?_⟩
      rw [figureEightParam_first hu']
      apply WithLp.ofLp_injective
      funext i
      simp only [WithLp.ofLp_toLp]
      fin_cases i
      · show (1 : ℝ) + Real.cos u = p 0
        rw [hcu]; ring
      · show Real.sin u = p 1
        rw [hsu]
      · show (100 : ℝ) = p 2
        rw [h2]
  · by_cases hzero : p 0 + 1 = 1 ∧ p 1 = 0
    · obtain ⟨hx, hy⟩ := hzero
      refine ⟨0, ?_⟩
      apply WithLp.ofLp_injective
      funext i
      simp only [figureEightParam, figTheta, Real.arctan_zero, mul_zero, add_zero, WithLp.ofLp_toLp]
      fin_cases i
      · show (figPoint (Real.pi / 2)).ofLp (0 : Fin 3) = p 0
        rw [figPoint_apply_zero, Real.cos_pi_div_two, abs_zero, mul_zero]
        linarith
      · show (figPoint (Real.pi / 2)).ofLp (1 : Fin 3) = p 1
        rw [figPoint_apply_one, Real.cos_pi_div_two, abs_zero, mul_zero, zero_mul]
        linarith
      · show (figPoint (Real.pi / 2)).ofLp (2 : Fin 3) = p 2
        rw [figPoint_apply_two, h2]
    · have hne : ¬ (Real.cos 0 = p 0 + 1 ∧ Real.sin 0 = p 1) := by
        rintro ⟨hx, hy⟩
        rw [Real.cos_zero] at hx
        rw [Real.sin_zero] at hy
        exact hzero ⟨by linarith, by linarith⟩
      obtain ⟨w, hw, hcw, hsw⟩ := exists_cos_sin_eq_Ioo_of (c := 0) h1 hne
      have hw' : w ∈ Set.Ioo 0 (2 * Real.pi) := by
        rw [zero_add] at hw
        exact hw
      refine ⟨Real.tan (w / 4), ?_⟩
      rw [figureEightParam_second hw']
      apply WithLp.ofLp_injective
      funext i
      simp only [WithLp.ofLp_toLp]
      fin_cases i
      · show (-1 : ℝ) + Real.cos w = p 0
        rw [hcw]; ring
      · show Real.sin w = p 1
        rw [hsw]
      · show (100 : ℝ) = p 2
        rw [h2]

theorem range_figureEightParam : Set.range figureEightParam = figureEight :=
  Set.Subset.antisymm range_figureEightParam_subset figureEight_subset_range

/-! ## Injectivity -/

theorem figureEightParam_injective : Function.Injective figureEightParam := by
  intro t t' h
  set θ := figTheta t with hθ
  set θ' := figTheta t' with hθ'
  have hmem : θ ∈ Set.Ioo (-(Real.pi / 2)) (3 * Real.pi / 2) := by
    rw [hθ]; exact figTheta_mem t
  have hmem' : θ' ∈ Set.Ioo (-(Real.pi / 2)) (3 * Real.pi / 2) := by
    rw [hθ']; exact figTheta_mem t'
  have hc : 2 * |Real.cos θ| * Real.cos θ = 2 * |Real.cos θ'| * Real.cos θ' := by
    have hh := congrArg (fun p : R3 => p 0) h
    simp only [figureEightParam] at hh
    rw [← hθ, ← hθ'] at hh
    simpa only [figPoint_apply_zero] using hh
  have hs : 2 * |Real.cos θ| * Real.sin θ = 2 * |Real.cos θ'| * Real.sin θ' := by
    have hh := congrArg (fun p : R3 => p 1) h
    simp only [figureEightParam] at hh
    rw [← hθ, ← hθ'] at hh
    simpa only [figPoint_apply_one] using hh
  have key : ∀ x : ℝ, (2 * |Real.cos x|) ^ 2 =
      (2 * |Real.cos x| * Real.cos x) ^ 2 + (2 * |Real.cos x| * Real.sin x) ^ 2 := by
    intro x
    have hsin := Real.sin_sq_add_cos_sq x
    have habs2 : |Real.cos x| ^ 2 = Real.cos x ^ 2 := sq_abs _
    nlinarith [hsin, habs2]
  have hnorm : (2 * |Real.cos θ|) ^ 2 = (2 * |Real.cos θ'|) ^ 2 := by
    rw [key θ, key θ', hc, hs]
  have hle : 0 ≤ 2 * |Real.cos θ| := by positivity
  have hle' : 0 ≤ 2 * |Real.cos θ'| := by positivity
  have habs : 2 * |Real.cos θ| = 2 * |Real.cos θ'| := by
    have := (sq_eq_sq_iff_abs_eq_abs (2 * |Real.cos θ|) (2 * |Real.cos θ'|)).mp hnorm
    rwa [abs_of_nonneg hle, abs_of_nonneg hle'] at this
  have hθθ' : θ = θ' := by
    by_cases h0 : Real.cos θ = 0
    · have h0' : Real.cos θ' = 0 := by
        have := habs
        rw [h0] at this
        simp only [abs_zero, mul_zero] at this
        have hz : |Real.cos θ'| = 0 := by linarith
        rwa [abs_eq_zero] at hz
      have hπ : θ = Real.pi / 2 := by
        obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp h0
        rw [hk] at hmem ⊢
        have hk1 : (-1 : ℝ) < 2 * (k : ℝ) + 1 := by nlinarith [hmem.1, Real.pi_pos]
        have hk2 : 2 * (k : ℝ) + 1 < 3 := by nlinarith [hmem.2, Real.pi_pos]
        have hk1z : (-1 : ℤ) < 2 * k + 1 := by exact_mod_cast hk1
        have hk2z : 2 * k + 1 < (3 : ℤ) := by exact_mod_cast hk2
        have hk0 : k = 0 := by omega
        rw [hk0]; ring
      have hπ' : θ' = Real.pi / 2 := by
        obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp h0'
        rw [hk] at hmem' ⊢
        have hk1 : (-1 : ℝ) < 2 * (k : ℝ) + 1 := by nlinarith [hmem'.1, Real.pi_pos]
        have hk2 : 2 * (k : ℝ) + 1 < 3 := by nlinarith [hmem'.2, Real.pi_pos]
        have hk1z : (-1 : ℤ) < 2 * k + 1 := by exact_mod_cast hk1
        have hk2z : 2 * k + 1 < (3 : ℤ) := by exact_mod_cast hk2
        have hk0 : k = 0 := by omega
        rw [hk0]; ring
      rw [hπ, hπ']
    · have hcos_eq : Real.cos θ = Real.cos θ' := by
        have hcl : 0 < |Real.cos θ| := abs_pos.mpr h0
        have h2 : |Real.cos θ| = |Real.cos θ'| := by linarith [habs]
        have h1 : |Real.cos θ| * Real.cos θ = |Real.cos θ| * Real.cos θ' := by
          have hh := hc
          rw [← h2] at hh
          linarith
        exact mul_left_cancel₀ (ne_of_gt hcl) h1
      have hsin_eq : Real.sin θ = Real.sin θ' := by
        have hcl : 0 < |Real.cos θ| := abs_pos.mpr h0
        have h2 : |Real.cos θ| = |Real.cos θ'| := by linarith [habs]
        have h1 : |Real.cos θ| * Real.sin θ = |Real.cos θ| * Real.sin θ' := by
          have hh := hs
          rw [← h2] at hh
          linarith
        exact mul_left_cancel₀ (ne_of_gt hcl) h1
      obtain ⟨k, hk⟩ := (Work.Core.cos_sin_eq_iff_exists_int θ θ').mp ⟨hcos_eq, hsin_eq⟩
      have hkabs : |((k : ℝ)) * (2 * Real.pi)| < 2 * Real.pi := by
        have h4 : (k : ℝ) * (2 * Real.pi) = θ - θ' := by linarith [hk]
        rw [h4, abs_lt]
        constructor <;> linarith [hmem.1, hmem.2, hmem'.1, hmem'.2]
      have hk0 : k = 0 := by
        have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
        have h1 : |((k : ℝ))| < 1 := by
          have hk' := hkabs
          rw [abs_mul, abs_of_pos h2π] at hk'
          nlinarith [hk', h2π]
        have h2 : |(k : ℤ)| < 1 := by exact_mod_cast h1
        rw [abs_lt] at h2
        omega
      rw [hk0] at hk
      simpa using hk
  exact figTheta_injective (by rw [← hθ, ← hθ', hθθ'])

/-! ## The counterexample -/

theorem exists_compact_isLocalArc_not_isCircleUnion :
    ∃ ψ : Submission.Diffeo, ∃ Z : Set R3, IsCompact Z ∧ Work.Smooth.Morse.IsLocalArc ψ Z ∧
      ¬ IsCircleUnion ψ Z := by
  refine ⟨idDiffeo, figureEight, figureEight_isCompact, ?_, ?_⟩
  · rw [← range_figureEightParam]
    exact isLocalArc_range_of_injective_continuous idDiffeo continuous_figureEightParam
      figureEightParam_injective
  · intro h
    have hmem : figureEightParam 0 ∈ figureEight := by
      rw [← range_figureEightParam]
      exact Set.mem_range_self 0
    have hcarrier := h.subset_carrier hmem
    obtain ⟨p, hp⟩ := hcarrier
    have hcoord : ((Work.Smooth.Morse.torus idDiffeo).psi p.1 p.2) 2 = Real.sin p.2 := by
      rw [Work.Smooth.Morse.torus, Work.CoreTopology.ParamTorus.mapHomeomorph_psi]
      exact Work.Core.torusMap_apply_two p.1 p.2
    have hz : (figureEightParam 0) 2 = 100 := figureEightParam_apply_two 0
    rw [← hp] at hz
    rw [hcoord] at hz
    have := Real.sin_le_one p.2
    linarith

/-- **The literal statement is false.**  `Work.Smooth.Morse.CompactOneManifoldInput` is refuted by
the figure eight (`exists_compact_isLocalArc_not_isCircleUnion`). -/
theorem not_compactOneManifoldInput :
    ¬ (∀ ψ : Submission.Diffeo, Work.Smooth.Morse.CompactOneManifoldInput ψ) := by
  intro h
  obtain ⟨ψ, Z, hcomp, harc, hnot⟩ := exists_compact_isLocalArc_not_isCircleUnion
  exact hnot (h ψ Z hcomp harc)

end

end Work.Smooth.OneManifold
