import Mathlib
import Submission.Work.Isotopy.frame_matching_point

/-!
# The span-level frame map `σ`

The first piece of the single-point frame matching (see `frame_matching_point.lean` for the full
plan): for orthonormal `k`-frames `B C : Fin k → E` in a real inner product space, the explicit
linear map

`frameLinearMap B C : E →ₗ[ℝ] E`,   `x ↦ ∑ i, inner ℝ (B i) x • C i`

sends `B i` to `C i` and carries `span (Set.range B)` into `span (Set.range C)`.  Restricted to
the spans it is the forward half of the required `σ`; the mirror map
`frameLinearMap C B` is its inverse on the spans (next leaf).

The linear map is built as a finite sum of the rank-one maps
`ContinuousLinearMap.smulRight (innerSL ℝ (B i)) (C i)`, which avoids all additivity/smul
bookkeeping.
-/

namespace Work.Isotopy

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The explicit linear map `x ↦ ∑ i, inner ℝ (B i) x • C i`, as a sum of rank-one maps. -/
noncomputable def frameLinearMap {k : ℕ} (B C : Fin k → E) : E →ₗ[ℝ] E :=
  ∑ i, (innerSL ℝ (B i)).smulRight (C i)

/-- The computation rule for `frameLinearMap`. -/
theorem frameLinearMap_apply {k : ℕ} (B C : Fin k → E) (x : E) :
    frameLinearMap B C x = ∑ i, inner ℝ (B i) x • C i := by
  simp [frameLinearMap]

/-- The frame map sends the source frame to the target frame. -/
theorem frameLinearMap_apply_frame {k : ℕ} (B C : Fin k → E) (hB : Orthonormal ℝ B) (i : Fin k) :
    frameLinearMap B C (B i) = C i := by
  classical
  rw [frameLinearMap_apply]
  have h := orthonormal_iff_ite.mp hB
  rw [Finset.sum_eq_single i]
  · rw [h i i]; simp
  · intro j _ hj
    rw [h j i, if_neg hj, zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The frame map carries the source span into the target span. -/
theorem frameLinearMap_mem_span {k : ℕ} (B C : Fin k → E) {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range B)) :
    frameLinearMap B C x ∈ Submodule.span ℝ (Set.range C) := by
  rw [frameLinearMap_apply]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))

/-- **The orthonormal expansion on the span.**  `frameLinearMap B B` is the identity on
`span ℝ (Set.range B)`: for an orthonormal family, `∑ i, inner ℝ (B i) x • B i = x` as soon as `x`
lies in the span.  This is the expansion that makes `frameLinearMap C B` the inverse of
`frameLinearMap B C` between the two spans. -/
theorem frameLinearMap_id_on_span {k : ℕ} (B : Fin k → E) (hB : Orthonormal ℝ B) :
    ∀ x ∈ Submodule.span ℝ (Set.range B), frameLinearMap B B x = x := by
  have hle : Submodule.span ℝ (Set.range B) ≤
      LinearMap.eqLocus (frameLinearMap B B) (LinearMap.id : E →ₗ[ℝ] E) := by
    rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact frameLinearMap_apply_frame B B hB i
  exact hle


/-- **The composition identity.**  `frameLinearMap C B ∘ frameLinearMap B C = frameLinearMap B B`
(for `C` orthonormal): expanding the inner sum and collapsing it with the orthonormality of `C`
shows that the mirror map is a left inverse of `frameLinearMap B C`, hence — with
`frameLinearMap_id_on_span` — an inverse between the two spans. -/
theorem frameLinearMap_comp {k : ℕ} (B C : Fin k → E) (hC : Orthonormal ℝ C) (x : E) :
    frameLinearMap C B (frameLinearMap B C x) = frameLinearMap B B x := by
  classical
  simp only [frameLinearMap_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  rw [inner_sum]
  have hterm : ∀ i : Fin k, inner ℝ (C j) (inner ℝ (B i) x • C i)
      = inner ℝ (B i) x * inner ℝ (C j) (C i) := by
    intro i
    rw [inner_smul_right]
  simp only [hterm]
  have hCj := orthonormal_iff_ite.mp hC
  rw [Finset.sum_eq_single j]
  · rw [hCj j j, if_pos rfl, mul_one]
  · intro i _ hij
    rw [hCj j i, if_neg (fun hji => hij hji.symm), mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj


/-- **The span-level frame equivalence `σ`.**  For orthonormal `k`-frames `B`, `C` in a real inner
product space, `frameLinearMap B C` restricts to a linear equivalence from
`span ℝ (Set.range B)` onto `span ℝ (Set.range C)`, with inverse the restriction of the mirror map
`frameLinearMap C B`.  The two inverse identities are `frameLinearMap_comp` followed by
`frameLinearMap_id_on_span`. -/
noncomputable def frameSpanEquiv {k : ℕ} (B C : Fin k → E)
    (hB : Orthonormal ℝ B) (hC : Orthonormal ℝ C) :
    ↥(Submodule.span ℝ (Set.range B)) ≃ₗ[ℝ] ↥(Submodule.span ℝ (Set.range C)) where
  toFun x := ⟨frameLinearMap B C x.1, frameLinearMap_mem_span B C x.2⟩
  invFun y := ⟨frameLinearMap C B y.1, frameLinearMap_mem_span C B y.2⟩
  left_inv x := by
    refine Subtype.ext ?_
    show frameLinearMap C B (frameLinearMap B C x.1) = x.1
    rw [frameLinearMap_comp B C hC, frameLinearMap_id_on_span B hB x.1 x.2]
  right_inv y := by
    refine Subtype.ext ?_
    show frameLinearMap B C (frameLinearMap C B y.1) = y.1
    rw [frameLinearMap_comp C B hB, frameLinearMap_id_on_span C hC y.1 y.2]
  map_add' x y := by
    refine Subtype.ext ?_
    show frameLinearMap B C (x.1 + y.1) = frameLinearMap B C x.1 + frameLinearMap B C y.1
    rw [map_add]
  map_smul' a x := by
    refine Subtype.ext ?_
    show frameLinearMap B C (a • x.1) = a • frameLinearMap B C x.1
    rw [map_smul]


/-- **The complement half `τ`.**  The orthogonal complements of the two spans are linearly
equivalent, because the spans are (by `σ`) and the orthogonal decomposition
`finrank K + finrank Kᗮ = finrank E` then cancels. -/
noncomputable def frameComplementEquiv {k : ℕ} [FiniteDimensional ℝ E] (B C : Fin k → E)
    (hB : Orthonormal ℝ B) (hC : Orthonormal ℝ C) :
    ↥(Submodule.span ℝ (Set.range B))ᗮ ≃ₗ[ℝ] ↥(Submodule.span ℝ (Set.range C))ᗮ :=
  LinearEquiv.ofFinrankEq _ _ (by
    have h1 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ)
      (Submodule.span ℝ (Set.range B))
    have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ)
      (Submodule.span ℝ (Set.range C))
    have hsc : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range B))
        = Module.finrank ℝ ↥(Submodule.span ℝ (Set.range C)) :=
      (frameSpanEquiv B C hB hC).finrank_eq
    omega)

end Work.Isotopy

/-!
## Formalisation notes (this leaf)

* The inner-product *notation* `⟪x, y⟫` is not in scope in this file (it needs its own
  `open scoped`); the functional form `inner ℝ (B i) x` elaborates and simplifies exactly as well,
  and is what the summands use.
* Building the linear map as a finite sum of rank-one maps
  `(innerSL ℝ (B i)).smulRight (C i)` avoids all `map_add'`/`map_smul'` bookkeeping; the
  computation rule is a one-line `simp [frameLinearMap]`.
* In `Finset.sum_eq_single i` the side condition is `j ≠ i`, and the `if` from
  `orthonormal_iff_ite` is indexed by `j = i`, so the off-diagonal term is killed by `if_neg hj`
  (no `Eq.symm`).
-/


/-!
## Note on the orthonormal expansion (trap)

`Submodule.span_induction` in this revision takes its membership hypothesis **last**
(`(mem) (zero) (add) (smul) (h : x ∈ span R s)`), so the natural
`refine Submodule.span_induction hx ?_ ?_ ?_ ?_` mis-assigns and the goal degenerates.  The robust
route, used in `frameLinearMap_id_on_span`, is

`Submodule.span_le` on `LinearMap.eqLocus (frameLinearMap B B) (LinearMap.id : E →ₗ[ℝ] E)`:
prove the equality on the generators (`Set.range B`) and let `span_le` promote it to the whole span.
-/
