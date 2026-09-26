import Submission.Work.CoreTopology.infDist_standard_carrier

/-!
# The two sides of the standard torus

The standard torus of revolution `Σ = standard.carrier` is the level set `torusHeight = 1` of
the height function `torusHeight x = (r - 2)² + x 2²` (`r = √(x 0² + x 1²)`).  Its complement is
therefore the disjoint union of the two open sets

* `solidTorus   = {x | torusHeight x < 1}` — the bounded side, the solid torus `T`;
* `torusExterior = {x | 1 < torusHeight x}` — the unbounded side,

and every connected subset of `ℝ³` avoiding `Σ` lies entirely in one of them.

This one-sidedness is the first ingredient of the "push the inner disc through the inessential
disc" argument: it is what makes it meaningful to say that a piece of a disc crossing `Σ` lies
*inside* or *outside*, and hence what "push it across" means.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- **The bounded side of the standard torus**: the solid torus. -/
def solidTorus : Set R3 := {x | torusHeight x < 1}

/-- **The unbounded side of the standard torus**. -/
def torusExterior : Set R3 := {x | 1 < torusHeight x}

theorem mem_solidTorus_iff {x : R3} : x ∈ solidTorus ↔ torusHeight x < 1 := Iff.rfl

theorem mem_torusExterior_iff {x : R3} : x ∈ torusExterior ↔ 1 < torusHeight x := Iff.rfl

/-- The torus is the level set `torusHeight = 1`. -/
theorem mem_carrier_iff_torusHeight_eq_one {x : R3} :
    x ∈ standard.carrier ↔ torusHeight x = 1 := (torusHeight_eq_one_iff x).symm

/-- The complement of the torus is exactly the union of the two sides. -/
theorem compl_carrier_eq : (standard.carrier)ᶜ = solidTorus ∪ torusExterior := by
  ext x
  rw [Set.mem_compl_iff, mem_carrier_iff_torusHeight_eq_one, Set.mem_union, mem_solidTorus_iff,
    mem_torusExterior_iff]
  constructor
  · intro h
    rcases lt_trichotomy (torusHeight x) 1 with h1 | h1 | h1
    · exact Or.inl h1
    · exact absurd h1 h
    · exact Or.inr h1
  · rintro (h | h)
    · exact ne_of_lt h
    · exact ne_of_gt h

theorem solidTorus_disjoint_torusExterior : Disjoint solidTorus torusExterior := by
  rw [Set.disjoint_left]
  intro x h1 h2
  rw [mem_solidTorus_iff] at h1
  rw [mem_torusExterior_iff] at h2
  exact absurd h2 (not_lt.mpr (le_of_lt h1))

theorem solidTorus_subset_compl : solidTorus ⊆ (standard.carrier)ᶜ := by
  rw [compl_carrier_eq]; exact subset_union_left

theorem torusExterior_subset_compl : torusExterior ⊆ (standard.carrier)ᶜ := by
  rw [compl_carrier_eq]; exact subset_union_right

theorem isOpen_solidTorus : IsOpen solidTorus :=
  isOpen_lt (continuous_torusHeight) continuous_const

theorem isOpen_torusExterior : IsOpen torusExterior :=
  isOpen_lt continuous_const (continuous_torusHeight)

/-- The solid torus is bounded (it sits in the ball of radius `4` about the origin): indeed
`torusHeight x < 1` forces `r < 3` and `|x 2| < 1`, whence `‖x‖² = r² + x 2² < 10 < 16`. -/
theorem solidTorus_subset_ball : solidTorus ⊆ Metric.ball (0 : R3) 4 := by
  intro x hx
  rw [mem_solidTorus_iff, torusHeight_apply] at hx
  have h2 : horizRadius x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by rw [horizRadius_sq, horizRadiusSq_apply]
  have h3 : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
  have hz2 : x 2 ^ 2 < 1 := by nlinarith [hx, sq_nonneg (horizRadius x - 2)]
  have hr2 : (horizRadius x - 2) ^ 2 < 1 := by nlinarith [hx, sq_nonneg (x 2)]
  have habs : |horizRadius x - 2| < 1 := by
    have h : (horizRadius x - 2) ^ 2 < (1 : ℝ) ^ 2 := by simpa using hr2
    simpa using (sq_lt_sq).mp h
  have hr3 : horizRadius x < 3 := by linarith [(abs_lt.mp habs).2]
  have hr0 : 0 ≤ horizRadius x := Real.sqrt_nonneg _
  have hz1 : |x 2| < 1 := by
    have h : x 2 ^ 2 < (1 : ℝ) ^ 2 := by simpa using hz2
    simpa using (sq_lt_sq).mp h
  have hz1' : x 2 < 1 := (abs_lt.mp hz1).2
  have hz1'' : -1 < x 2 := (abs_lt.mp hz1).1
  rw [Metric.mem_ball, dist_zero_right]
  nlinarith [h2, h3, hr3, hr0, hz1', hz1'']

/-! ## The meridian radius `R = ‖meridVec x‖`

The torus is the level set `R = 1` of the meridian radius `R x = ‖meridVec x‖`, where
`meridVec x = ⟨r - 2, x 2⟩` is the position of `x` in the meridian half-plane.  This is the
coordinate in which a disc crossing `Σ` is pushed across it. -/

/-- The square of the meridian radius is the height function. -/
theorem norm_meridVec_sq (x : R3) : ‖meridVec x‖ ^ 2 = torusHeight x := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, meridVec_re, meridVec_im,
    torusHeight_apply]
  ring

/-- The torus is the level set `R = 1`. -/
theorem norm_meridVec_eq_one_iff {x : R3} :
    ‖meridVec x‖ = 1 ↔ x ∈ standard.carrier := by
  rw [mem_carrier_iff_torusHeight_eq_one, ← norm_meridVec_sq]
  constructor
  · intro h; rw [h]; norm_num
  · intro h
    have h2 : ‖meridVec x‖ = 1 := by
      rcases sq_eq_one_iff.mp h with h' | h'
      · exact h'
      · nlinarith [norm_nonneg (meridVec x)]
    simpa using h2

/-- The two sides in terms of the meridian radius. -/
theorem mem_solidTorus_iff_norm_meridVec {x : R3} : x ∈ solidTorus ↔ ‖meridVec x‖ < 1 := by
  rw [mem_solidTorus_iff, ← norm_meridVec_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg (meridVec x)]

theorem mem_torusExterior_iff_norm_meridVec {x : R3} : x ∈ torusExterior ↔ 1 < ‖meridVec x‖ := by
  rw [mem_torusExterior_iff, ← norm_meridVec_sq]
  constructor <;> intro h <;> nlinarith [norm_nonneg (meridVec x)]

/-- The distance to the torus is the distance from the meridian radius to `1`. -/
theorem infDist_standard_carrier_meridVec (x : R3) :
    Metric.infDist x standard.carrier = |‖meridVec x‖ - 1| := by
  rw [infDist_standard_carrier, ← norm_meridVec_sq, Real.sqrt_sq (norm_nonneg (meridVec x))]

theorem horizVec_smul (c : ℝ) (y : R3) : horizVec (c • y) = c • horizVec y := by
  apply Complex.ext <;> simp [horizVec, PiLp.smul_apply]

theorem horizRadius_smul (c : ℝ) (y : R3) :
    horizRadius (c • y) = |c| * horizRadius y := by
  rw [← norm_horizVec (c • y), horizVec_smul, norm_smul, norm_horizVec, Real.norm_eq_abs]

theorem coord2_smul (c : ℝ) (y : R3) : (c • y) 2 = c * y 2 := by
  simp [PiLp.smul_apply]

theorem torusHeight_smul_torusMap (c θ φ : ℝ) :
    torusHeight (c • Work.Core.torusMap θ φ)
      = (|c| * (2 + Real.cos φ) - 2) ^ 2 + (c * Real.sin φ) ^ 2 := by
  rw [torusHeight_apply, horizRadius_smul, coord2_smul, torusMap_coord_two,
    horizRadius_torusMap]

/-- A point of the solid torus: the outer equator contracted by `1/2`. -/
theorem solidTorus_nonempty : solidTorus.Nonempty := by
  refine ⟨(1 / 2 : ℝ) • Work.Core.torusMap 0 0, ?_⟩
  rw [mem_solidTorus_iff, torusHeight_smul_torusMap, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  norm_num

/-- A point of the exterior. -/
theorem torusExterior_nonempty : torusExterior.Nonempty := by
  refine ⟨(4 : ℝ) • Work.Core.torusMap 0 0, ?_⟩
  rw [mem_torusExterior_iff, torusHeight_smul_torusMap, abs_of_pos (by norm_num : (0:ℝ) < 4)]
  norm_num

/-- **The one-sidedness of the torus.**  A preconnected subset of `ℝ³` avoiding the standard
torus lies entirely on one side. -/
theorem isPreconnected_subset_solidTorus_or_torusExterior {S : Set R3}
    (hS : IsPreconnected S) (hS' : S ⊆ (standard.carrier)ᶜ) :
    S ⊆ solidTorus ∨ S ⊆ torusExterior := by
  have hcov : S ⊆ solidTorus ∪ torusExterior := hS'.trans (le_of_eq compl_carrier_eq)
  exact Or.imp (fun h => h) (fun h => h)
    (IsPreconnected.subset_or_subset isOpen_solidTorus isOpen_torusExterior
      solidTorus_disjoint_torusExterior hcov hS)

/-- A preconnected set avoiding the torus and meeting the solid torus lies in it. -/
theorem subset_solidTorus_of_mem {S : Set R3} (hS : IsPreconnected S)
    (hS' : S ⊆ (standard.carrier)ᶜ) {x : R3} (hx : x ∈ S) (hxs : torusHeight x < 1) :
    S ⊆ solidTorus := by
  rcases isPreconnected_subset_solidTorus_or_torusExterior hS hS' with h | h
  · exact h
  · exact absurd (h hx) (by rw [mem_torusExterior_iff]; exact not_lt.mpr (le_of_lt hxs))

/-- A preconnected set avoiding the torus and meeting the exterior lies in it. -/
theorem subset_torusExterior_of_mem {S : Set R3} (hS : IsPreconnected S)
    (hS' : S ⊆ (standard.carrier)ᶜ) {x : R3} (hx : x ∈ S) (hxs : 1 < torusHeight x) :
    S ⊆ torusExterior := by
  rcases isPreconnected_subset_solidTorus_or_torusExterior hS hS' with h | h
  · exact absurd (h hx) (by rw [mem_solidTorus_iff]; exact not_lt.mpr (le_of_lt hxs))
  · exact h

end

end Work.CoreTopology
