import Mathlib

/-!
# A smooth bump function that is `1` on a compact set and supported in an open set

If `K` is a compact subset of an open set `U` in a finite-dimensional real normed space `E`,
there is a `C^∞` function `f : E → ℝ` with `0 ≤ f ≤ 1`, `f = 1` on `K` and `tsupport f ⊆ U`.

The proof uses the smooth Urysohn lemma of the smooth partition-of-unity API
(`exists_contMDiffMap_zero_one_nhds_of_isClosed`): applied to the disjoint closed sets `Uᶜ` and `K`
it produces a smooth function vanishing on a whole neighbourhood of `Uᶜ` (so that its *closed*
support is contained in `U`) and equal to `1` on a neighbourhood of `K`.
-/

open scoped Manifold ContDiff
open Set Topology Filter

namespace Work.Drive.Whitney

/-- **Smooth Urysohn, compact-in-open form.**  For a compact set `K` inside an open set `U` of a
finite-dimensional real normed space there is an infinitely smooth `f : E → ℝ` with values in
`[0, 1]`, equal to `1` on `K` and whose (closed) support is contained in `U`. -/
theorem exists_contDiff_bump_of_isCompact_subset_isOpen {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x ∈ K, f x = 1) ∧ tsupport f ⊆ U := by
  obtain ⟨F, hF0, hF1, hF01⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, E)) hU.isClosed_compl hK.isClosed
      (Set.disjoint_left.mpr fun x hxUc hxK => hxUc (hKU hxK)) (n := ⊤)
  set f : E → ℝ := ⇑F with hf
  obtain ⟨V, hVopen, hVsub, hVzero⟩ := mem_nhdsSet_iff_exists.mp hF0
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · have := (ContMDiffMap.contMDiff F).contDiff
    simpa [f] using this
  · intro x
    exact ⟨(hF01 x).1, (hF01 x).2⟩
  · intro x hx
    exact hF1.self_of_nhdsSet x hx
  · have hs : Function.support f ⊆ Vᶜ := fun y hy hyV => hy (hVzero hyV)
    have hcl : tsupport f ⊆ Vᶜ := closure_minimal hs hVopen.isClosed_compl
    exact fun x hx => by_contra fun hxU => hcl hx (hVsub hxU)

/-- The requested lemma: in `ℝ × ℝ`, a compact set inside an open set admits a smooth bump
function `1` on the compact set with closed support inside the open set. -/
theorem bumpCompactOfOpen {K U : Set (ℝ × ℝ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ f : ℝ × ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x ∈ K, f x = 1) ∧ tsupport f ⊆ U :=
  exists_contDiff_bump_of_isCompact_subset_isOpen hK hU hKU

end Work.Drive.Whitney
