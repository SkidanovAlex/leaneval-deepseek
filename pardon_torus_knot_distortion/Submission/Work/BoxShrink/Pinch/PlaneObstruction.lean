import Submission.Work.BoxShrink.Pinch.Bridge

/-!
# The plane dictionary alone cannot prove the push-off

`Bridge.lean` shows that the winding vectors of loops of a parametrised torus are exactly the
lattice periods realised by paths of the parameter plane (`PeriodRealised`), and that the whole
`ℚ`-submodule `Work.SurgeryInvariance.WindingSpan P X` is the span of those periods
(`periodSpan_eq_windingSpan`).  Hence the push-off of `Work.BoxShrink.Bubble.PushOffHalf` is, read
in the plane, a statement of the following shape.

**(⋆)**  `dim span {periods realised by Ω} ≤ dim span {periods realised by Ω ∖ {g = 0}} + 1`,
where `Ω = Φ⁻¹ (boxRegion)` and `g` is the pull-back of the cutting plane's coordinate — together
with the hypotheses that neither the boundary `∂Ω` (the sphere trace) nor the slice
`Ω ∩ {g = 0}` realises a nonzero period.

This module isolates a *plane-level obstruction*: the family of pairs `(Ω, g)` for which (⋆) fails
is nonempty, with `Ω` open, periodic and `Ω ∖ {g = 0}` period-free.  The example is the complement
of a periodic family of discs at the lattice points `πℤ²` (a periodic sublevel set of
`sin²q₁ + sin²q₂`), cut by the periodic function `g = sin q₁ · sin q₂`, whose zero set is the grid
`{q₁ ∈ πℤ} ∪ {q₂ ∈ πℤ}`:

* `Ω` realises the two independent periods `(1,0)` and `(0,1)` — the lines `q₂ = π/2`, `q₁ = π/2`
  lie inside `Ω` (`gridComplement_period_one_zero`, `gridComplement_period_zero_one`);
* `Ω ∖ {g = 0}` realises *no* period at all: its points avoid the grid, so each connected subset of
  it lies in one of the squares `(mπ, (m+1)π) × (nπ, (n+1)π)` of side `π < 2π`
  (`gridComplement_slice_no_period`).

So a proof of the push-off cannot consist of a purely plane-theoretic argument applied to the pair
of preimages: the geometry of the box, the plane and the embedding `Φ` — which determine *which*
pairs `(Ω, g)` occur — is indispensable.  This is not an artefact of the formalisation: at the
standard small box (`BubbleHalfRefuted.lean`) the box region is an annular band whose boundary, the
sphere trace, is itself essential, which is exactly the escape route closed by the hypothesis
`¬ P.ContainsEssentialLoop (sphereSet c σ s)`; the example above is the plane-level shadow of that
configuration.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-! ## Periods realised by a set of the plane -/

/-- **A lattice period realised by a set of the parameter plane.**  The plane-side counterpart of
`PeriodRealised`: a continuous path periodic up to `2π(k,l)` whose image lies in `Y`. -/
def PlanePeriod (Y : Set (ℝ × ℝ)) (k l : ℤ) : Prop :=
  ∃ q : ℝ → ℝ × ℝ, Continuous q ∧
    (∀ t : ℝ, q (t + 1) = q t + Work.TorusCover.periodShift (k, l)) ∧
    ∀ t : ℝ, q t ∈ Y

theorem planePeriod_mono {Y Z : Set (ℝ × ℝ)} (h : Y ⊆ Z) {k l : ℤ}
    (hk : PlanePeriod Y k l) : PlanePeriod Z k l := by
  obtain ⟨q, hq, hper, hmem⟩ := hk
  exact ⟨q, hq, hper, fun t => h (hmem t)⟩

/-! ## Windows realise no nonzero period -/

/-- Two points of an open interval differ by less than the length of the interval. -/
theorem abs_sub_lt_of_mem_Ioo {u v a b : ℝ} (hu : u ∈ Set.Ioo a b) (hv : v ∈ Set.Ioo a b) :
    |v - u| < b - a := by
  rw [abs_lt]
  exact ⟨by linarith [hu.1, hu.2, hv.1, hv.2], by linarith [hu.1, hu.2, hv.1, hv.2]⟩

/-- A nonzero integer multiple of `2π` cannot be the difference of two points of an open interval
of length `< 2π`. -/
theorem int_mul_two_pi_eq_zero_of_mem_Ioo {m : ℤ} {u v p q : ℝ} (hpq : q - p < 2 * Real.pi)
    (hu : u ∈ Set.Ioo p q) (hv : v ∈ Set.Ioo p q) (h : v = u + (m : ℝ) * (2 * Real.pi)) : m = 0 := by
  by_contra hm
  have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
  have h2 : |(m : ℝ) * (2 * Real.pi)| = |(m : ℝ)| * (2 * Real.pi) := by
    rw [abs_mul]; simp [abs_of_pos Real.pi_pos]
  have h3 : |(m : ℝ) * (2 * Real.pi)| = |v - u| := by rw [h]; ring_nf
  have h4 := abs_sub_lt_of_mem_Ioo hu hv
  nlinarith [h1, Real.pi_pos]

/-- **A window contains no two points differing by a nonzero lattice vector.**  Both coordinates of
`y - x` are bounded by the side lengths of the rectangle, while a nonzero integer multiple of `2π`
has absolute value at least `2π`. -/
theorem window_no_lattice_pair {a b c d : ℝ} (hb : b - a < 2 * Real.pi)
    (hd : d - c < 2 * Real.pi) {x y : ℝ × ℝ} (hx : x ∈ Set.Ioo a b ×ˢ Set.Ioo c d)
    (hy : y ∈ Set.Ioo a b ×ˢ Set.Ioo c d) {k l : ℤ}
    (h : y = x + Work.TorusCover.periodShift (k, l)) : (k, l) = 0 := by
  rw [Set.mem_prod] at hx hy
  have hk1 : y.1 = x.1 + (k : ℝ) * (2 * Real.pi) := by
    rw [h, Work.TorusCover.periodShift]; rfl
  have hl1 : y.2 = x.2 + (l : ℝ) * (2 * Real.pi) := by
    rw [h, Work.TorusCover.periodShift]; rfl
  have hk : k = 0 := int_mul_two_pi_eq_zero_of_mem_Ioo hb hx.1 hy.1 hk1
  have hl : l = 0 := int_mul_two_pi_eq_zero_of_mem_Ioo hd hx.2 hy.2 hl1
  exact Prod.ext hk hl

/-- **A set confined to a window realises no nonzero period.** -/
theorem not_planePeriod_of_window {Y : Set (ℝ × ℝ)} {a b c d : ℝ}
    (hb : b - a < 2 * Real.pi) (hd : d - c < 2 * Real.pi)
    (hsub : Y ⊆ Set.Ioo a b ×ˢ Set.Ioo c d) {k l : ℤ} (hne : (k, l) ≠ 0) :
    ¬ PlanePeriod Y k l := by
  rintro ⟨q, -, hper, hmem⟩
  have h01 : q 1 = q 0 + Work.TorusCover.periodShift (k, l) := by simpa using hper 0
  exact hne (window_no_lattice_pair hb hd (hsub (hmem 0)) (hsub (hmem 1)) h01)

/-! ## The example: the complement of a periodic family of discs -/

/-- The complement of the periodic family of discs of squared radius `c` centred at the lattice
points `πℤ²`: the set on which `c < sin²q₁ + sin²q₂`. -/
def gridComplement (c : ℝ) : Set (ℝ × ℝ) := {q | c < Real.sin q.1 ^ 2 + Real.sin q.2 ^ 2}

/-- The periodic function whose zero set is the grid `{q₁ ∈ πℤ} ∪ {q₂ ∈ πℤ}`. -/
def gridFun (q : ℝ × ℝ) : ℝ := Real.sin q.1 * Real.sin q.2

theorem gridComplement_open (c : ℝ) : IsOpen (gridComplement c) :=
  isOpen_lt continuous_const
    (((Real.continuous_sin.comp continuous_fst).pow 2).add
      ((Real.continuous_sin.comp continuous_snd).pow 2))

/-- The example is periodic for the lattice of the parameter plane. -/
theorem gridComplement_periodic {c : ℝ} {x : ℝ × ℝ} (hx : x ∈ gridComplement c) {k l : ℤ} :
    x + Work.TorusCover.periodShift (k, l) ∈ gridComplement c := by
  simp only [gridComplement, Set.mem_setOf_eq, Work.TorusCover.periodShift, Prod.fst_add,
    Prod.snd_add]
  rw [Real.sin_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  exact hx

/-- **The first period of the example.**  The horizontal line `q₂ = π/2` lies in `gridComplement c`
for `c < 1`, so the period `(1,0)` is realised. -/
theorem gridComplement_period_one_zero {c : ℝ} (hc : c < 1) :
    PlanePeriod (gridComplement c) 1 0 := by
  refine ⟨fun t => (2 * Real.pi * t, Real.pi / 2), ?_, ?_, ?_⟩
  · exact (continuous_const.mul continuous_id).prodMk continuous_const
  · intro t
    rw [Work.TorusCover.periodShift]
    ext <;> simp <;> ring
  · intro t
    have h : Real.sin (Real.pi / 2) ^ 2 = 1 := by rw [Real.sin_pi_div_two]; norm_num
    have hnn : 0 ≤ Real.sin (2 * Real.pi * t) ^ 2 := sq_nonneg _
    show c < Real.sin (2 * Real.pi * t) ^ 2 + Real.sin (Real.pi / 2) ^ 2
    rw [h]; linarith

/-- **The second period of the example**: the vertical line `q₁ = π/2`. -/
theorem gridComplement_period_zero_one {c : ℝ} (hc : c < 1) :
    PlanePeriod (gridComplement c) 0 1 := by
  refine ⟨fun t => (Real.pi / 2, 2 * Real.pi * t), ?_, ?_, ?_⟩
  · exact continuous_const.prodMk (continuous_const.mul continuous_id)
  · intro t
    rw [Work.TorusCover.periodShift]
    ext <;> simp <;> ring
  · intro t
    have h : Real.sin (Real.pi / 2) ^ 2 = 1 := by rw [Real.sin_pi_div_two]; norm_num
    have hnn : 0 ≤ Real.sin (2 * Real.pi * t) ^ 2 := sq_nonneg _
    show c < Real.sin (Real.pi / 2) ^ 2 + Real.sin (2 * Real.pi * t) ^ 2
    rw [h]; linarith

/-! ## The slice of the example is period-free -/

/-- **The cell of a point at which `sin` does not vanish**: the interval `(mπ, (m+1)π)` with
`m = ⌊y/π⌋` contains `y`. -/
theorem cell_of_sin_ne_zero {y : ℝ} (hy : Real.sin y ≠ 0) :
    ((⌊y / Real.pi⌋ : ℤ) : ℝ) * Real.pi < y ∧
      y < ((⌊y / Real.pi⌋ : ℤ) : ℝ) * Real.pi + Real.pi := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hle : ((⌊y / Real.pi⌋ : ℤ) : ℝ) * Real.pi ≤ y := by
    have h := Int.floor_le (y / Real.pi)
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hπ)
    rwa [div_mul_cancel₀ _ (ne_of_gt hπ)] at h2
  have hlt : y < ((⌊y / Real.pi⌋ : ℤ) : ℝ) * Real.pi + Real.pi := by
    have h := Int.lt_floor_add_one (y / Real.pi)
    have h2 := mul_lt_mul_of_pos_right h hπ
    rw [div_mul_cancel₀ _ (ne_of_gt hπ)] at h2
    linarith
  exact ⟨lt_of_le_of_ne hle (fun heq => hy (by rw [← heq, Real.sin_int_mul_pi])), hlt⟩

/-- **A preconnected set on which `sin ∘ f` never vanishes lies in one cell of the grid.**  The
image `f '' S` is preconnected, hence an interval, and an interval avoiding the zeros of `sin`
cannot meet two consecutive cells. -/
theorem exists_cell_of_isPreconnected_proj {S : Set (ℝ × ℝ)} (hS : IsPreconnected S)
    (hne : S.Nonempty) (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    (hsin : ∀ x ∈ S, Real.sin (f x) ≠ 0) :
    ∃ m : ℤ, ∀ x ∈ S, (m : ℝ) * Real.pi < f x ∧ f x < (m : ℝ) * Real.pi + Real.pi := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨hcell1, hcell2⟩ := cell_of_sin_ne_zero (hsin x₀ hx₀)
  have hpre : IsPreconnected (f '' S) := hS.image f hf.continuousOn
  have hord := hpre.ordConnected
  refine ⟨⌊f x₀ / Real.pi⌋, ?_⟩
  intro x hx
  constructor
  · by_contra hcon
    push Not at hcon
    have hmem : ((⌊f x₀ / Real.pi⌋ : ℤ) : ℝ) * Real.pi ∈ f '' S :=
      hord.out ⟨x, hx, rfl⟩ ⟨x₀, hx₀, rfl⟩ ⟨hcon, le_of_lt hcell1⟩
    obtain ⟨y, hyS, hy⟩ := hmem
    exact hsin y hyS (by rw [hy]; exact Real.sin_int_mul_pi _)
  · by_contra hcon
    push Not at hcon
    have hmem : ((⌊f x₀ / Real.pi⌋ : ℤ) : ℝ) * Real.pi + Real.pi ∈ f '' S :=
      hord.out ⟨x₀, hx₀, rfl⟩ ⟨x, hx, rfl⟩ ⟨le_of_lt hcell2, hcon⟩
    obtain ⟨y, hyS, hy⟩ := hmem
    have hsin0 : Real.sin (((⌊f x₀ / Real.pi⌋ : ℤ) : ℝ) * Real.pi + Real.pi) = 0 := by
      have hcast : ((⌊f x₀ / Real.pi⌋ : ℤ) : ℝ) * Real.pi + Real.pi =
          (((⌊f x₀ / Real.pi⌋ : ℤ) + 1 : ℤ) : ℝ) * Real.pi := by push_cast; ring
      rw [hcast, Real.sin_int_mul_pi]
    exact hsin y hyS (by rw [hy]; exact hsin0)

/-- **A connected set on which both coordinates avoid the grid lies in a window.** -/
theorem exists_cell_of_isPreconnected {S : Set (ℝ × ℝ)} (hS : IsPreconnected S) (hne : S.Nonempty)
    (h1 : ∀ x ∈ S, Real.sin x.1 ≠ 0) (h2 : ∀ x ∈ S, Real.sin x.2 ≠ 0) :
    ∃ m n : ℤ, S ⊆ Set.Ioo ((m : ℝ) * Real.pi) ((m : ℝ) * Real.pi + Real.pi) ×ˢ
      Set.Ioo ((n : ℝ) * Real.pi) ((n : ℝ) * Real.pi + Real.pi) := by
  obtain ⟨m, hm⟩ := exists_cell_of_isPreconnected_proj hS hne (fun y : ℝ × ℝ => y.1)
    continuous_fst (fun x hx => h1 x hx)
  obtain ⟨n, hn⟩ := exists_cell_of_isPreconnected_proj hS hne (fun y : ℝ × ℝ => y.2)
    continuous_snd (fun x hx => h2 x hx)
  refine ⟨m, n, fun x hx => ?_⟩
  rw [Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo]
  exact ⟨hm x hx, hn x hx⟩

/-- **The slice of the example realises no nonzero period.**  Its points avoid the grid, so every
realising path — whose image is connected — lies in one of the squares of side `π`. -/
theorem gridComplement_slice_no_period {c : ℝ} {k l : ℤ} (hne : (k, l) ≠ 0) :
    ¬ PlanePeriod (gridComplement c ∩ {q | gridFun q ≠ 0}) k l := by
  rintro ⟨q, hq, hper, hmem⟩
  have hSl : IsPreconnected (Set.range q) := isPreconnected_range hq
  have hneS : (Set.range q).Nonempty := ⟨q 0, 0, rfl⟩
  have h1 : ∀ x ∈ Set.range q, Real.sin x.1 ≠ 0 := by
    rintro x ⟨t, rfl⟩ hzero
    have hg := (hmem t).2
    simp [gridFun, hzero] at hg
  have h2 : ∀ x ∈ Set.range q, Real.sin x.2 ≠ 0 := by
    rintro x ⟨t, rfl⟩ hzero
    have hg := (hmem t).2
    simp [gridFun, hzero] at hg
  obtain ⟨m, n, hsub⟩ := exists_cell_of_isPreconnected hSl hneS h1 h2
  have hb : ((m : ℝ) * Real.pi + Real.pi + 1) - ((m : ℝ) * Real.pi - 1) < 2 * Real.pi := by
    linarith [Real.pi_gt_three]
  have hd : ((n : ℝ) * Real.pi + Real.pi + 1) - ((n : ℝ) * Real.pi - 1) < 2 * Real.pi := by
    linarith [Real.pi_gt_three]
  have hwin : ∀ x ∈ Set.range q,
      x ∈ Set.Ioo ((m : ℝ) * Real.pi - 1) ((m : ℝ) * Real.pi + Real.pi + 1) ×ˢ
        Set.Ioo ((n : ℝ) * Real.pi - 1) ((n : ℝ) * Real.pi + Real.pi + 1) := by
    intro x hx
    have h' := hsub hx
    rw [Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo] at h' ⊢
    exact ⟨⟨by linarith [h'.1.1], by linarith [h'.1.2]⟩,
      ⟨by linarith [h'.2.1], by linarith [h'.2.2]⟩⟩
  have h01 : q 1 = q 0 + Work.TorusCover.periodShift (k, l) := by simpa using hper 0
  exact hne (window_no_lattice_pair hb hd (hwin _ ⟨0, rfl⟩) (hwin _ ⟨1, rfl⟩) h01)

/-! ## The obstruction -/

/-- **The obstruction.**  For `c < 1` the pair `(gridComplement c, gridFun)` of the plane — an open
periodic region and a periodic function — realises the two independent periods `(1,0)` and `(0,1)`,
while its slice `gridComplement c ∩ {gridFun ≠ 0}` realises none.  Hence the plane-level statement
`(⋆)` of the module docstring — the form in which the push-off would be argued from the two
preimages alone — is **false**. -/
theorem plane_obstruction {c : ℝ} (hc : c < 1) :
    PlanePeriod (gridComplement c) 1 0 ∧ PlanePeriod (gridComplement c) 0 1 ∧
      (∀ k l : ℤ, (k, l) ≠ 0 → ¬ PlanePeriod (gridComplement c ∩ {q | gridFun q ≠ 0}) k l) :=
  ⟨gridComplement_period_one_zero hc, gridComplement_period_zero_one hc,
    fun _ _ hne => gridComplement_slice_no_period hne⟩

/-! ## Agreement with the loop-level dictionary of `Bridge.lean` -/

/-- **The two notions of a realised period agree.**  `Bridge.lean`'s `PeriodRealised P X k l` and the
plane-level `PlanePeriod (Φ⁻¹ X) k l` are the same statement (a path of the plane with the shift
`2π(k,l)` whose image lies in the preimage of `X`), so the equivalence is definitional.  This is the
bridge by which a plane-level obstruction becomes a statement about the surface. -/
theorem periodRealised_iff_planePeriod {P : Work.CoreTopology.ParamTorus} (X : Set R3) (k l : ℤ) :
    PeriodRealised P X k l ↔ PlanePeriod (planePreimage P X) k l := Iff.rfl

end

end Work.BoxShrink.Pinch
