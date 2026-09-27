import Mathlib
import Submission.Work.Whitney.PushDefs

/-!
# The slab shear, and the single separation condition behind `HasAmbientPushData`

Two reusable bricks for the collar ("finger") push of the Whitney move.

## 1. The slab shear is a global `C^∞` diffeomorphism with an explicit inverse

The push of the collar construction has the shape

  `ψ y = y + κ y • e`   (`e` a *fixed* direction, `κ` constant along the lines `y + ℝ • e`),

i.e. a shear whose amplitude is constant along the displacement direction.  This is the "slab"
shape of `CutPush/README.md` §6 (the support `{κ ≠ 0}` is then a *slab*, unbounded along `e`).
It needs **no fold condition**: the inverse is the literal `σ y = y - κ y • e`, since `κ` does not
change when the point is moved along `e`.  (Compare `CutPush.Model.normalShear`, which is the same
statement in the tubular coordinates `(base, offset)`.)

## 2. The three clauses of `HasAmbientPushData` are one separation condition

For a witness `W₀ ⊆ W` and a diffeomorphism pair `(ψ, σ)` fixing the image of the frontier of `W₀`,
the placement clause and the two non-attainment clauses of `Work.Whitney.HasAmbientPushData` are
*equivalent* to the single condition

  `∀ x ∈ W₀, ∀ z : M, ψ (f x) ≠ f z ∨ z ∈ W₀`

(the pushed sheet meets the image of `M` only inside `W₀`), given only that the two double point
values are not themselves in `W₀`.  This is the form in which the geometric construction has to
deliver the interface, and the form in which the "landing beyond the cut" analysis of
`CutPush/SlabLinear.lean` is stated.
-/

namespace Work.Whitney

set_option linter.unusedVariables false

open scoped Manifold ContDiff
open Topology

variable {N : ℕ}

/-- **The slab shear is a left inverse.**  If `κ` is constant along the lines `y + ℝ • e`, then
`y ↦ y - κ y • e` is a left inverse of `y ↦ y + κ y • e`. -/
theorem slabShear_leftInverse (κ : EuclideanSpace ℝ (Fin N) → ℝ)
    (e : EuclideanSpace ℝ (Fin N))
    (h : ∀ y : EuclideanSpace ℝ (Fin N), ∀ t : ℝ, κ (y + t • e) = κ y) :
    Function.LeftInverse (fun y => y - κ y • e) (fun y => y + κ y • e) := by
  intro y
  have h1 : κ (y + κ y • e) = κ y := h y (κ y)
  show y + κ y • e - κ (y + κ y • e) • e = y
  rw [h1, add_sub_cancel_right]

/-- **The slab shear is a right inverse.**  Same hypothesis; the inverse is two-sided. -/
theorem slabShear_rightInverse (κ : EuclideanSpace ℝ (Fin N) → ℝ)
    (e : EuclideanSpace ℝ (Fin N))
    (h : ∀ y : EuclideanSpace ℝ (Fin N), ∀ t : ℝ, κ (y + t • e) = κ y) :
    Function.RightInverse (fun y => y - κ y • e) (fun y => y + κ y • e) := by
  intro y
  have h1 : κ (y - κ y • e) = κ y := by
    have h2 : κ (y + (-κ y) • e) = κ y := h y (-κ y)
    simpa [sub_eq_add_neg, neg_smul] using h2
  show y - κ y • e + κ (y - κ y • e) • e = y
  rw [h1, sub_add_cancel]

/-- **The slab shear is smooth.** -/
theorem contDiff_slabShear {κ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hκ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ) (e : EuclideanSpace ℝ (Fin N)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : EuclideanSpace ℝ (Fin N) => y + κ y • e) := by
  fun_prop

/-- The slab shear fixes every point where the amplitude vanishes, and its *inverse* does too. -/
theorem slabShear_fixed_of_amp_zero (κ : EuclideanSpace ℝ (Fin N) → ℝ)
    (e : EuclideanSpace ℝ (Fin N)) {y : EuclideanSpace ℝ (Fin N)} (hy : κ y = 0) :
    y + κ y • e = y := by rw [hy, zero_smul, add_zero]

/-- The slab shear only moves points inside `{κ ≠ 0}`. -/
theorem slabShear_eq_self_of_amp_eq (κ : EuclideanSpace ℝ (Fin N) → ℝ)
    (e : EuclideanSpace ℝ (Fin N)) {y : EuclideanSpace ℝ (Fin N)} (hy : κ y = 0) :
    (fun z => z + κ z • e) y = y := slabShear_fixed_of_amp_zero κ e hy

/-- **The slab shear's displacement is bounded by the amplitude bound**: `‖ψ y - y‖ = |κ y| ‖e‖`. -/
theorem slabShear_displacement (κ : EuclideanSpace ℝ (Fin N) → ℝ)
    (e : EuclideanSpace ℝ (Fin N)) (y : EuclideanSpace ℝ (Fin N)) :
    ‖(fun z => z + κ z • e) y - y‖ = |κ y| * ‖e‖ := by
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]

/-! ## The three clauses from one separation condition -/

/-- **`HasAmbientPushData` from the single separation condition.**

Given an open witness `W₀ ⊆ W` containing `p₂`, `q₂` and missing `p₁`, `q₁`, an open `O` containing
the image of the frontier of `W₀` on which `ψ` is the identity, a global mutually inverse pair
`(ψ, σ)` of smooth self-maps of the target, and the separation condition

`∀ x ∈ W₀, ∀ z : M, ψ (f x) = f z → z ∈ W₀`,

all the clauses of `Work.Whitney.HasAmbientPushData f W p₁ p₂ q₁ q₂` hold.  (The two double point
values are excluded by the condition itself, because `f p₁ = f p₂` with `p₂ ∈ W₀` and `p₁ ∉ W₀`.)
This is the exact form in which the collar construction has to deliver the interface; no `hclean`
or `hsep` is needed. -/
theorem hasAmbientPushData_of_separation {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (W₀ : Set M) (O : Set (EuclideanSpace ℝ (Fin (2 * n))))
    (ψ σ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    (hW₀o : IsOpen W₀) (hW₀W : W₀ ⊆ W) (hp₂ : p₂ ∈ W₀) (hq₂ : q₂ ∈ W₀)
    (hp₁ : p₁ ∉ W₀) (hq₁ : q₁ ∉ W₀)
    (hOo : IsOpen O) (hfront : f '' frontier W₀ ⊆ O) (hOid : ∀ y, y ∈ O → ψ y = y)
    (hσψ : ∀ y, σ (ψ y) = y) (hψσ : ∀ y, ψ (σ y) = y)
    (hψsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hσsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) σ)
    (hsep : ∀ x : M, x ∈ W₀ → ∀ z : M, ψ (f x) = f z → z ∈ W₀) :
    HasAmbientPushData f W p₁ p₂ q₁ q₂ := by
  refine ⟨W₀, O, ψ, σ, hW₀o, hW₀W, hp₂, hq₂, hp₁, hq₁, hOo, hfront, hOid, hσψ, hψσ,
    hψsm, hσsm, ?_, ?_, ?_⟩
  · -- placement
    rintro y ⟨u, ⟨x, hx, rfl⟩, rfl⟩
    rw [Set.mem_union]
    by_cases h : ψ (f x) ∈ f '' (Set.univ : Set M)
    · obtain ⟨z, -, hz⟩ := h
      exact Or.inl ⟨z, hsep x hx z hz.symm, hz⟩
    · exact Or.inr h
  · -- `f p₂ ∉ ψ '' (f '' W₀)`
    rintro ⟨y, ⟨x, hx, rfl⟩, hxy⟩
    have h1 : ψ (f x) = f p₁ := hxy.trans hfp.symm
    exact hp₁ (hsep x hx p₁ h1)
  · -- `f q₂ ∉ ψ '' (f '' W₀)`
    rintro ⟨y, ⟨x, hx, rfl⟩, hxy⟩
    have h1 : ψ (f x) = f q₁ := hxy.trans hfq.symm
    exact hq₁ (hsep x hx q₁ h1)


/-! ## The local collision estimate: no collision inside the cut

The flat model of the finger push (`CutPush/Model.lean`, `CutPush/SlabLinear.lean`) is the pair of
sheets `sheet₁ = graph h₁` and `sheet₂ = graph h₂` in `ℝⁿ × ℝⁿ`, pushed by the modulated
translation `(x, y) ↦ (x, y + χ x • w)`.  The collision equation of the pushed second sheet with
the first sheet is then

  `h₁ x = h₂ x + χ x • w`,   i.e.   `(h₁ - h₂) x = χ x • w`.

The *linear* core (`CutPush.SlabLinear`) reads `h₁ - h₂ = D` (a linear equivalence), where the
solutions are the fixed points of `x ↦ χ x • (D⁻¹ w)`.  The estimate below is the quantitative
nonlinear form used by the collar construction:

* the two sheets satisfy `‖(h₁ - h₂) u - A u‖ ≤ K ‖u‖²` on the ball of radius `ρ`
  (the quadratic sheet model produced by `Work.Whitney.lct_model_package_cont`),
* the linear part satisfies `‖A u‖ ≤ M ‖u‖`,
* the amplitude is `1` on the ball of radius `ρ` (the "core" of the collar contains the ball),
* and the displacement is longer than the sheet's dip: `(M + K ρ) ρ < ‖w‖`.

Then **every collision parameter lies outside the ball of radius `ρ`**.  In the construction the
ball of radius `ρ` is exactly the cut `K_P = σ₁ '' ball 0 ρ` (so a collision parameter outside it
means the preimage of the collision lies in `W₀`, i.e. the collision is an *old* intersection, not
a new one). -/

/-- **No collision inside the cut.**  If the amplitude is `1` on `ball 0 ρ` and the displacement
`w` is longer than the total sheet separation `(M + K ρ) ρ` on that ball, then no collision
parameter lies in `ball 0 ρ`. -/
theorem collision_param_not_mem_ball {n : ℕ}
    {h₁ h₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n)) {χ : EuclideanSpace ℝ (Fin n) → ℝ} {M K ρ : ℝ}
    (hρ : 0 < ρ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hχ1 : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ ρ → χ x = 1)
    (hlin : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ ≤ ρ → ‖h₁ u - h₂ u - A u‖ ≤ K * ‖u‖ ^ 2)
    (hAc : ∀ u : EuclideanSpace ℝ (Fin n), ‖A u‖ ≤ M * ‖u‖)
    (hw : (M + K * ρ) * ρ < ‖w‖)
    {x : EuclideanSpace ℝ (Fin n)} (hcoll : h₁ x = h₂ x + χ x • w) : ρ < ‖x‖ := by
  by_contra hx
  rw [not_lt] at hx
  have hdiff : h₁ x - h₂ x = w := by
    rw [hcoll, hχ1 x hx, one_smul, add_sub_cancel_left]
  have h1 : ‖h₁ x - h₂ x - A x‖ ≤ K * ‖x‖ ^ 2 := hlin x hx
  have h2 : ‖A x‖ ≤ M * ‖x‖ := hAc x
  have h3 : ‖h₁ x - h₂ x‖ ≤ M * ‖x‖ + K * ‖x‖ ^ 2 := by
    have hble := norm_add_le (h₁ x - h₂ x - A x) (A x)
    rw [sub_add_cancel] at hble
    linarith [h1, h2]
  have hxnn : 0 ≤ ‖x‖ := norm_nonneg _
  have h4 : M * ‖x‖ + K * ‖x‖ ^ 2 ≤ (M + K * ρ) * ρ := by
    have h5 : K * ‖x‖ ^ 2 ≤ K * ρ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hK
      nlinarith [hxnn, hx]
    have h6 : M * ‖x‖ ≤ M * ρ := mul_le_mul_of_nonneg_left hx hM
    nlinarith [h5, h6, hx, hρ]
  rw [hdiff] at h3
  linarith

/-! ## The collar bump

The amplitude of the collar push is a compactly supported smooth bump: `1` on a compact *core*
containing the pushed sheet near the two double points and the arc's image, `0` off a prescribed
open set on which the wall `f '' frontier W₀` lives, with values in `[0,1]`.  This is the
Euclidean smooth Urysohn lemma of Mathlib in the exact packaging the construction needs. -/

/-- **A smooth bump of compact support between a compact core and an open set.** -/
theorem exists_compactSupport_bump {N : ℕ} (C U : Set (EuclideanSpace ℝ (Fin N)))
    (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) (hUb : Bornology.IsBounded U) :
    ∃ χ : EuclideanSpace ℝ (Fin N) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧ (∀ y, y ∉ U → χ y = 0) ∧ (∀ y, y ∈ C → χ y = 1) := by
  classical
  -- a positive `cthickening` radius with everything inside `U`
  obtain ⟨δ, hδ, hδU⟩ := hC.exists_cthickening_subset_open hU hCU
  -- the smooth Urysohn function with support exactly the open thickening of `C`
  obtain ⟨f, hfsm, hfrange, hfsupp, hfC⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N)))
      (n := (⊤ : ℕ∞)) (s := Metric.thickening δ C) (t := C)
      Metric.isOpen_thickening hC.isClosed (Metric.self_subset_thickening hδ C)
  refine ⟨f, contMDiff_iff_contDiff.mp hfsm, ?_, ?_, ?_, ?_⟩
  · -- compact support: the topological support sits inside the compact `cthickening`
    have hsub : tsupport f ⊆ Metric.cthickening δ C := by
      intro y hy
      exact Metric.closure_thickening_subset_cthickening δ C (by rwa [tsupport, hfsupp] at hy)
    have hcomp : IsCompact (Metric.cthickening δ C) := hC.cthickening
    exact hcomp.of_isClosed_subset (isClosed_tsupport f) hsub
  · intro y
    exact hfrange (Set.mem_range_self y)
  · intro y hy
    have hyU : y ∉ Metric.thickening δ C :=
      fun hmem => hy (hδU (Metric.thickening_subset_cthickening δ C hmem))
    by_contra hne
    exact hyU (hfsupp ▸ (Function.mem_support.mpr hne))
  · intro y hy
    exact (hfC y).mp hy

end Work.Whitney
