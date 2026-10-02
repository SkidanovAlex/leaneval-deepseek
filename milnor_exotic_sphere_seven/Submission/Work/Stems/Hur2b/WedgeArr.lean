import Mathlib
import Submission.Work.Stems.Hur2b.Assembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The wedge arrangement of six based cubes, and the fold fact

For six based `2`-cubes `cs 0, …, cs 5 : Ω²(X,x₀)` we build two arrangements of them in the square
and prove that the class of the “wedge” arrangement is the product of the classes of the contents.

* `rowArr cs` — the `1 × 6` row: the iterated concatenation in the first coordinate.  Its class is
  the product of the classes of the contents (`rowArr_class`), by `cl_transAt_zero`.
* `wedgeArr cs` — the contents placed on the six disjoint rectangles
  `[k/6, (k+1)/6] × [1/3, 2/3]`, and `x₀` on the rest.  It is the *squeeze* of the row arrangement
  into the middle band: `wedgeArr cs = rowArr cs ∘ squeeze`, where
  `squeeze (y₀,y₁) = (y₀, clamp (3 y₁ - 1))`.

The key point is that the squeeze is a continuous self-map of the square which is
* homotopic to the identity through boundary-preserving maps (`squeezeHom`), hence does not change
  the class of a based cube (`wedgeArr_homotopic_rowArr`);
* compatible with basedness: on the top and bottom edges of the square the clamped coordinate is
  `0` or `1`, so the contents — being based cubes — take the value `x₀` there.

The fold fact `wedgeArr_class` follows immediately.  This is the first, coordinate-free brick of the
“sum of the faces” argument: it is the model instance in which the six contents are genuinely
disjoint, which is exactly what a general concentration argument has to produce.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical
open Work.Stems.Hur2

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-! ## The class of a concatenation -/

/-- The class of a concatenation in the first coordinate is the product of the classes.  (Local
version of `cl_mul`, avoiding the `SimplyConnectedSpace` section variable of `Assembly`.) -/
theorem cl_transAt_zero (p q : GenLoop (Fin 2) X x₀) :
    cl x₀ (GenLoop.transAt 0 q p) = cl x₀ p * cl x₀ q := by
  rw [cl, cl, cl]
  exact (HomotopyGroup.mul_spec (N := Fin 2) (i := 0) (p := p) (q := q)).symm

/-- The class of a concatenation in the second coordinate is the product of the classes. -/
theorem cl_transAt_one (p q : GenLoop (Fin 2) X x₀) :
    cl x₀ (GenLoop.transAt 1 q p) = cl x₀ p * cl x₀ q := by
  rw [cl, cl, cl]
  exact (HomotopyGroup.mul_spec (N := Fin 2) (i := 1) (p := p) (q := q)).symm

/-! ## The `1 × 6` row arrangement -/

/-- The `1 × 6` row arrangement of six based cubes: the iterated concatenation in the first
coordinate, the contents read in the order `0, 1, …, 5` from the innermost nesting out. -/
noncomputable def rowArr (cs : Fin 6 → GenLoop (Fin 2) X x₀) : GenLoop (Fin 2) X x₀ :=
  GenLoop.transAt 0 (cs 5) <| GenLoop.transAt 0 (cs 4) <| GenLoop.transAt 0 (cs 3) <|
    GenLoop.transAt 0 (cs 2) <| GenLoop.transAt 0 (cs 1) (cs 0)

/-- **The class of the row arrangement is the product of the classes of the contents.** -/
theorem rowArr_class (cs : Fin 6 → GenLoop (Fin 2) X x₀) :
    cl x₀ (rowArr cs) = cl x₀ (cs 0) * cl x₀ (cs 1) * cl x₀ (cs 2) * cl x₀ (cs 3) *
      cl x₀ (cs 4) * cl x₀ (cs 5) := by
  rw [rowArr, cl_transAt_zero, cl_transAt_zero, cl_transAt_zero, cl_transAt_zero,
    cl_transAt_zero]

/-- The `2 × 3` **grid** arrangement of six based cubes: two rows in the second coordinate, three
columns in the first. -/
noncomputable def gridArr (cs : Fin 6 → GenLoop (Fin 2) X x₀) : GenLoop (Fin 2) X x₀ :=
  GenLoop.transAt 1 (GenLoop.transAt 0 (cs 2) (GenLoop.transAt 0 (cs 1) (cs 0)))
    (GenLoop.transAt 0 (cs 5) (GenLoop.transAt 0 (cs 4) (cs 3)))

/-- **The class of the grid arrangement is the product of the classes of the contents.** -/
theorem gridArr_class (cs : Fin 6 → GenLoop (Fin 2) X x₀) :
    cl x₀ (gridArr cs) = ∏ k : Fin 6, cl x₀ (cs k) := by
  rw [gridArr, cl_transAt_one, cl_transAt_zero, cl_transAt_zero, cl_transAt_zero,
    cl_transAt_zero, Fin.prod_univ_six]
  ac_rfl

/-! ## The squeeze into the middle band -/

/-- The clamping of `v : I` into the middle band: `v ↦ clamp (3 v - 1)`; it is `0` for `v ≤ 1/3`
and `1` for `v ≥ 2/3`. -/
noncomputable def bandC (v : unitInterval) : unitInterval := clamp (3 * (v : ℝ) - 1)

@[simp] theorem bandC_zero : bandC 0 = 0 := by
  rw [bandC, clamp_of_le_zero]; norm_num

@[simp] theorem bandC_one : bandC 1 = 1 := by
  rw [bandC, clamp_of_ge_one]; norm_num

theorem continuous_bandC : Continuous bandC :=
  continuous_clamp.comp (by fun_prop)

/-- `clamp` fixes the elements of `I`. -/
theorem clamp_coe (v : unitInterval) : clamp (v : ℝ) = v := by
  rw [clamp_of_mem v.2]

/-- The squeeze of the square onto its middle band `[0,1] × [1/3,2/3]`, keeping the first
coordinate: `y ↦ (y₀, clamp (3 y₁ - 1))`. -/
noncomputable def squeeze : C(IC 2, IC 2) :=
  ⟨fun y => pair2 (y 0) (bandC (y 1)), continuous_pair2 (continuous_apply 0)
    (continuous_bandC.comp (continuous_apply 1))⟩

theorem squeeze_apply (y : IC 2) : squeeze y = pair2 (y 0) (bandC (y 1)) := rfl

@[simp] theorem squeeze_coord_zero (y : IC 2) : squeeze y 0 = y 0 := by
  rw [squeeze_apply, pair2_zero]

@[simp] theorem squeeze_coord_one (y : IC 2) : squeeze y 1 = bandC (y 1) := by
  rw [squeeze_apply, pair2_one]

/-- Any element of `Fin 2` which is not `0` is `1`. -/
theorem eq_one_of_ne_zero {i : Fin 2} (h : i ≠ 0) : i = 1 := by
  fin_cases i <;> simp_all

/-- The squeeze maps the boundary of the square into itself. -/
theorem squeeze_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) :
    squeeze y ∈ Cube.boundary (Fin 2) := by
  obtain ⟨i, hi | hi⟩ := hy
  by_cases h : i = 0
  · refine ⟨0, Or.inl ?_⟩
    rw [squeeze_coord_zero, ← h]; exact hi
  · obtain rfl : i = 1 := eq_one_of_ne_zero h
    refine ⟨1, ?_⟩
    rw [squeeze_coord_one, hi, bandC_zero]
    exact Or.inl rfl
  · -- second case: `y i = 1`
    by_cases h : i = 0
    · refine ⟨0, Or.inr ?_⟩
      rw [squeeze_coord_zero, ← h]; exact hi
    · obtain rfl : i = 1 := eq_one_of_ne_zero h
      refine ⟨1, ?_⟩
      rw [squeeze_coord_one, hi, bandC_one]
      exact Or.inr rfl

/-- The linear homotopy from the squeeze to the identity, through maps preserving the boundary of
the square. -/
noncomputable def squeezeHom : C(IC 2 × unitInterval, IC 2) :=
  ⟨fun q => pair2 (q.1 0)
      (clamp ((1 - (q.2 : ℝ)) * (bandC (q.1 1) : ℝ) + (q.2 : ℝ) * (q.1 1 : ℝ))),
    continuous_pair2 (continuous_apply 0 |>.comp continuous_fst)
      (continuous_clamp.comp (by fun_prop))⟩

theorem squeezeHom_apply (y : IC 2) (t : unitInterval) :
    squeezeHom (y, t) = pair2 (y 0)
      (clamp ((1 - (t : ℝ)) * (bandC (y 1) : ℝ) + (t : ℝ) * (y 1 : ℝ))) := rfl

@[simp] theorem squeezeHom_coord_zero (y : IC 2) (t : unitInterval) :
    squeezeHom (y, t) 0 = y 0 := by
  rw [squeezeHom_apply, pair2_zero]

theorem squeezeHom_coord_one_eq_zero {y : IC 2} (h : y 1 = 0) (t : unitInterval) :
    squeezeHom (y, t) 1 = 0 := by
  rw [squeezeHom_apply, pair2_one, h, bandC_zero]
  have h0 : (1 - (t : ℝ)) * ((0 : unitInterval) : ℝ) + (t : ℝ) * ((0 : unitInterval) : ℝ) = 0 := by
    rw [coe_zero_I]; ring
  rw [h0, clamp_zero]

theorem squeezeHom_coord_one_eq_one {y : IC 2} (h : y 1 = 1) (t : unitInterval) :
    squeezeHom (y, t) 1 = 1 := by
  rw [squeezeHom_apply, pair2_one, h, bandC_one]
  have h1 : (1 - (t : ℝ)) * ((1 : unitInterval) : ℝ) + (t : ℝ) * ((1 : unitInterval) : ℝ) = 1 := by
    rw [coe_one_I]; ring
  rw [h1, clamp_one]

/-- On the boundary of the square the whole linear homotopy stays in the boundary. -/
theorem squeezeHom_boundary {y : IC 2} (hy : y ∈ Cube.boundary (Fin 2)) (t : unitInterval) :
    squeezeHom (y, t) ∈ Cube.boundary (Fin 2) := by
  obtain ⟨i, hi | hi⟩ := hy
  by_cases h : i = 0
  · refine ⟨0, Or.inl ?_⟩
    rw [squeezeHom_coord_zero, ← h]; exact hi
  · obtain rfl : i = 1 := eq_one_of_ne_zero h
    refine ⟨1, Or.inl ?_⟩
    rw [squeezeHom_coord_one_eq_zero hi t]
  · by_cases h : i = 0
    · refine ⟨0, Or.inr ?_⟩
      rw [squeezeHom_coord_zero, ← h]; exact hi
    · obtain rfl : i = 1 := eq_one_of_ne_zero h
      refine ⟨1, Or.inr ?_⟩
      rw [squeezeHom_coord_one_eq_one hi t]

theorem squeezeHom_zero (y : IC 2) : squeezeHom (y, 0) = squeeze y := by
  funext i
  by_cases h : i = 0
  · subst h
    rw [squeezeHom_coord_zero, squeeze_coord_zero]
  · obtain rfl : i = 1 := eq_one_of_ne_zero h
    simp only [squeezeHom_apply, squeeze_apply, pair2_one]
    apply Subtype.ext
    rw [show (1 - ((0 : unitInterval) : ℝ)) = 1 by rw [coe_zero_I]; ring, one_mul,
      coe_zero_I, zero_mul, add_zero, clamp_coe]

theorem squeezeHom_one (y : IC 2) : squeezeHom (y, 1) = y := by
  funext i
  by_cases h : i = 0
  · subst h
    rw [squeezeHom_coord_zero]
  · obtain rfl : i = 1 := eq_one_of_ne_zero h
    simp only [squeezeHom_apply, pair2_one]
    apply Subtype.ext
    rw [show (1 - ((1 : unitInterval) : ℝ)) = 0 by rw [coe_one_I]; ring, zero_mul, coe_one_I,
      one_mul, zero_add, clamp_coe]

/-! ## The wedge arrangement and the fold fact -/

/-- The **wedge arrangement**: the six contents on the six disjoint rectangles
`[k/6, (k+1)/6] × [1/3, 2/3]`, and `x₀` on the rest of the square.  Equivalently, the row
arrangement squeezed into the middle band. -/
noncomputable def wedgeArr (cs : Fin 6 → GenLoop (Fin 2) X x₀) : GenLoop (Fin 2) X x₀ :=
  ⟨(rowArr cs).1.comp squeeze, fun y hy => (rowArr cs).2 (squeeze y) (squeeze_boundary hy)⟩

/-- **The concentration.**  The squeeze is a boundary-preserving self-map of the square homotopic to
the identity through such maps, so squeezing a based cube into the middle band does not change its
class. -/
theorem wedgeArr_homotopic_rowArr (cs : Fin 6 → GenLoop (Fin 2) X x₀) :
    GenLoop.Homotopic (wedgeArr cs) (rowArr cs) := by
  refine ⟨⟨⟨fun q : unitInterval × IC 2 => (rowArr cs) (squeezeHom (q.2, q.1)), ?_⟩, ?_, ?_⟩, ?_⟩
  · exact (rowArr cs).1.continuous.comp
      (squeezeHom.continuous.comp (continuous_snd.prodMk continuous_fst))
  · intro y
    show (rowArr cs) (squeezeHom (y, 0)) = (rowArr cs) (squeeze y)
    rw [squeezeHom_zero]
  · intro y
    show (rowArr cs) (squeezeHom (y, 1)) = (rowArr cs) y
    rw [squeezeHom_one]
  · intro t y hy
    show (rowArr cs) (squeezeHom (y, t)) = (rowArr cs) (squeeze y)
    exact ((rowArr cs).2 (squeezeHom (y, t)) (squeezeHom_boundary hy t)).trans
      ((rowArr cs).2 (squeeze y) (squeeze_boundary hy)).symm

/-- **The fold fact.**  The class of the wedge arrangement of six based cubes is the product of
their classes. -/
theorem wedgeArr_class (cs : Fin 6 → GenLoop (Fin 2) X x₀) :
    cl x₀ (wedgeArr cs) = ∏ k : Fin 6, cl x₀ (cs k) := by
  rw [show cl x₀ (wedgeArr cs) = cl x₀ (rowArr cs) from
      Quotient.sound (wedgeArr_homotopic_rowArr cs),
    rowArr_class, Fin.prod_univ_six]

end Work.Stems.Hur2b
