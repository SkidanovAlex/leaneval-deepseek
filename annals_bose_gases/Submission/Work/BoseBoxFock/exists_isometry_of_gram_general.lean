import Mathlib.Analysis.InnerProductSpace.Subspace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open scoped BigOperators

set_option autoImplicit false

/-!
# `Work.BoseBoxFock.exists_isometry_of_gram_general`

If two finite families `u : ι → E` and `f : ι → F` of vectors in (possibly different)
inner product spaces over the same `RCLike` field `𝕜` have *the same Gram matrix*,
`⟪u i, u j⟫ = ⟪f i, f j⟫` for all `i j`, then the correspondence `u i ↦ f i` extends to a
**linear isometry** on the span of `u`.

This is the general-field, general-target version of `Work.BoseBoxFock.exists_isometry_of_gram`
(which is the ℝ-valued/coordinate case, and is *false* as stated there because `Fin m → ℝ`
carries the sup norm rather than the ℓ² norm; here the target `F` is a genuine
`InnerProductSpace`, so there is no such mismatch and the statement is true).

## The argument

`Ψ := Fintype.linearCombination 𝕜 u : (ι → 𝕜) →ₗ[𝕜] E` and `Φ := Fintype.linearCombination 𝕜 f`
send the coefficient vector `c` to `∑ i, c i • u i` resp. `∑ i, c i • f i`.  The Gram
hypothesis says exactly that `Ψ` and `Φ` define the same sesquilinear form on coefficients,

  `⟪Ψ c, Ψ d⟫ = ⟪Φ c, Φ d⟫`  for all `c d`,

so `ker Ψ = ker Φ`; hence `Φ` factors through `Ψ`.  Since `range Ψ = span 𝕜 (range u)`
(`Fintype.range_linearCombination`), the factorisation is a linear map `T` on the span of `u`.
Finally `T` preserves inner products (pull back through `Ψ` and use the form identity), so
`T.isometryOfInner` makes it a linear isometry, and on generators
`T ⟨u i, _⟩ = T (Ψ (Pi.single i 1)) = Φ (Pi.single i 1) = f i`.
-/

/-- The inner product of two `Fintype`-indexed linear combinations: for `c d : ι → 𝕜`,
`⟪∑ i, c i • x i, ∑ j, d j • x j⟫ = ∑ i, ∑ j, star (c i) * d j * ⟪x i, x j⟫`. -/
lemma inner_sum_smul {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x : ι → E) (c d : ι → 𝕜) :
    inner 𝕜 (∑ i, c i • x i) (∑ j, d j • x j)
      = ∑ i, ∑ j, star (c i) * d j * inner 𝕜 (x i) (x j) := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  ring

theorem exists_isometry_of_gram_general {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (u : ι → E) (f : ι → F)
    (h : ∀ i j, inner 𝕜 (u i) (u j) = inner 𝕜 (f i) (f j)) :
    ∃ T : (Submodule.span 𝕜 (Set.range u)) →ₗᵢ[𝕜] F,
      ∀ i, T ⟨u i, Submodule.subset_span (Set.mem_range_self i)⟩ = f i := by
  classical
  set V : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range u) with hVdef
  -- the coefficient maps into `E` resp. into `F`
  set Ψ : (ι → 𝕜) →ₗ[𝕜] E := Fintype.linearCombination 𝕜 u with hΨdef
  set Φ : (ι → 𝕜) →ₗ[𝕜] F := Fintype.linearCombination 𝕜 f with hΦdef
  have hΨapp : ∀ c : ι → 𝕜, Ψ c = ∑ i, c i • u i := fun c =>
    Fintype.linearCombination_apply 𝕜 u c
  have hΦapp : ∀ c : ι → 𝕜, Φ c = ∑ i, c i • f i := fun c =>
    Fintype.linearCombination_apply 𝕜 f c
  -- the Gram hypothesis: `Ψ` and `Φ` carry the same sesquilinear form on coefficients
  have hkey : ∀ c d : ι → 𝕜, inner 𝕜 (Ψ c) (Ψ d) = inner 𝕜 (Φ c) (Φ d) := by
    intro c d
    rw [hΨapp c, hΨapp d, hΦapp c, hΦapp d, inner_sum_smul u c d, inner_sum_smul f c d]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [h i j]
  -- hence the kernels agree, and `Φ` factors through `Ψ`
  have hker : ∀ c d : ι → 𝕜, Ψ c = Ψ d → Φ c = Φ d := by
    intro c d hcd
    have h1 : Ψ (c - d) = 0 := by rw [map_sub, hcd, sub_self]
    have h2 : inner 𝕜 (Φ (c - d)) (Φ (c - d)) = 0 := by rw [← hkey, h1]; simp
    have h3 : Φ (c - d) = 0 := by rwa [inner_self_eq_zero] at h2
    have h4 : Φ c - Φ d = 0 := by rw [← map_sub]; exact h3
    exact sub_eq_zero.mp h4
  have hmem : ∀ x : V, ∃ c : ι → 𝕜, Ψ c = (x : E) := by
    intro x
    have hx : (x : E) ∈ Ψ.range := by
      rw [hΨdef, Fintype.range_linearCombination]; exact x.2
    exact LinearMap.mem_range.mp hx
  -- the induced map on the span of `u`
  let g : V → F := fun x => Φ (Classical.choose (hmem x))
  have gspec : ∀ x : V, Ψ (Classical.choose (hmem x)) = (x : E) :=
    fun x => Classical.choose_spec (hmem x)
  have hadd : ∀ x y : V, g (x + y) = g x + g y := by
    intro x y
    have h1 : Ψ (Classical.choose (hmem x) + Classical.choose (hmem y)) = (x : E) + (y : E) := by
      rw [map_add, gspec x, gspec y]
    have h2 : Ψ (Classical.choose (hmem (x + y))) = (x : E) + (y : E) := by
      simpa using gspec (x + y)
    have h3 : Φ (Classical.choose (hmem (x + y)))
        = Φ (Classical.choose (hmem x) + Classical.choose (hmem y)) := hker _ _ (by rw [h2, h1])
    show Φ (Classical.choose (hmem (x + y))) = Φ (Classical.choose (hmem x))
      + Φ (Classical.choose (hmem y))
    rw [h3, map_add]
  have hsmul : ∀ (r : 𝕜) (x : V), g (r • x) = r • g x := by
    intro r x
    have h1 : Ψ (r • Classical.choose (hmem x)) = r • (x : E) := by rw [map_smul, gspec x]
    have h2 : Ψ (Classical.choose (hmem (r • x))) = r • (x : E) := by
      simpa using gspec (r • x)
    have h3 : Φ (Classical.choose (hmem (r • x))) = Φ (r • Classical.choose (hmem x)) :=
      hker _ _ (by rw [h2, h1])
    show Φ (Classical.choose (hmem (r • x))) = r • Φ (Classical.choose (hmem x))
    rw [h3, map_smul]
  let Tlin : V →ₗ[𝕜] F :=
    { toFun := g, map_add' := hadd, map_smul' := hsmul }
  have hTapply : ∀ x : V, Tlin x = Φ (Classical.choose (hmem x)) := fun x => rfl
  have hg_inner : ∀ x y : V, inner 𝕜 (Tlin x) (Tlin y) = inner 𝕜 x y := by
    intro x y
    rw [hTapply, hTapply, ← hkey, gspec x, gspec y, Submodule.coe_inner]
  refine ⟨Tlin.isometryOfInner hg_inner, ?_⟩
  intro i
  have hgen : Ψ (Pi.single i (1 : 𝕜)) = u i := by
    rw [hΨdef, Fintype.linearCombination_apply_single]; simp
  have hgenΦ : Φ (Pi.single i (1 : 𝕜)) = f i := by
    rw [hΦdef, Fintype.linearCombination_apply_single]; simp
  have h1 : Ψ (Classical.choose (hmem ⟨u i, Submodule.subset_span (Set.mem_range_self i)⟩))
      = u i := gspec _
  have h2 : Φ (Classical.choose (hmem ⟨u i, Submodule.subset_span (Set.mem_range_self i)⟩))
      = Φ (Pi.single i (1 : 𝕜)) := hker _ _ (by rw [h1, hgen])
  exact h2.trans hgenΦ

end Work.BoseBoxFock
