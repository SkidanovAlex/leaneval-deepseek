import Mathlib
import Submission.Work.PinchLemma3.ClosedDiscA.isOpenInCarrier_connectedComponentIn
import Submission.Work.PinchLemma3.ClosedDiscA.isPathConnected_connectedComponentIn_carrier
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.CoreTopology.Disk

/-!
# A curve which leaves the components of the two regions has vanishing winding

`Work.PinchLemma3.ClosedDiscA.windingOf_eq_zero_of_not_subset_components`:
let `A`, `B ⊆ ℝ³` be regions of the surface `F = P.carrier` of a parametrised torus which are
**open in the surface** (`IsOpenInCarrier`) and which carry **no essential loop**
(`WindingSpan P _ = ⊥`), and let `a₀ ∈ A`, `b₀ ∈ B` be base points such that

  `A ∩ B ⊆ connectedComponentIn A a₀`   and   `A ∩ B ⊆ connectedComponentIn B b₀`.

Then every closed curve `γ` of `F` whose image lies in `A ∪ B` but is *not* contained in the
union of the two distinguished components has vanishing winding vector.

The mathematical content is a purely topological fact about the two components
`α = connectedComponentIn A a₀`, `β = connectedComponentIn B b₀`: since

* `A ∩ B ⊆ α ∩ β`, the four pieces `α`, `A \ α`, `β`, `B \ β` of `A ∪ B` are pairwise disjoint
  except that `α` and `β` meet, and
* `A \ α` and `B \ β` are *open* in the surface: they are unions of connected components of the
  carrier-open sets `A`, `B`, and components of open subsets of the surface are open (the surface
  is locally connected);

the image of `γ`, which is connected (it is the image of `ℝ` under a continuous map), is
contained in one of these four pieces or in `α ∪ β`.  (Concretely: `γ`'s image is contained in
`α ∪ β`, or in `A`, or in `B` — because a preconnected set meeting `A \ α` in a point cannot
meet the complement of `A \ α`, which is a union of the open sets `Aᶜ`, `α`, `B \ β`, and of
`β ∪ A`; we use this "separation" twice, once with the pair `(A \ α, α ∪ B)` and once with the
pair `(B \ β, β ∪ A)`.)  In the first case the curve is contained in `A ⊆ F` (or in `B ⊆ F`) and
hence has vanishing winding vector because `WindingSpan P A = ⊥`; in the second case the
hypothesis `¬ range γ ⊆ α ∪ β` is contradicted.

## Layout of the file

* `windingOf_eq_zero_of_range_subset` — a closed curve whose image lies in a region of vanishing
  winding span has vanishing winding vector;
* `isOpen_diff_of_isOpen_of_comp_subset` — removing the connected components of the points of a
  carrier-open set which lie outside a fixed component keeps it open;
* `connectedComponentIn_preimage_subset_diff` — the connected component of a point of `K` at a
  point which is not in the component of `k₀` avoids that component (in the carrier);
* the main theorem.
-/

-- The two local instances below are genuinely used as typeclass instances.
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.PinchLemma3.ClosedDiscA

noncomputable section

/-- **A closed curve whose image lies in a region of vanishing winding span has vanishing winding
vector.**  The winding vector of `γ` is a winding vector of `X`, hence lies in `WindingSpan P X`,
which is `⊥`. -/
theorem windingOf_eq_zero_of_range_subset {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    (hV : Work.SurgeryInvariance.WindingSpan P X = ⊥)
    (γ : Work.CoreTopology.ClosedCurve P) (h : ∀ t : ℝ, γ t ∈ X) :
    Work.SurgeryInvariance.windingOf P γ = 0 := by
  have hm : ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
      (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) ∈
      Work.SurgeryInvariance.WindingSpan P X := Submodule.subset_span ⟨γ, h, rfl⟩
  rw [hV, Submodule.mem_bot] at hm
  exact (Work.SurgeryInvariance.intPair_cast_eq_zero_iff _).mp hm

/-- **Removing the components of a carrier-open set outside a fixed component keeps it open.**
If `A'` is open, `α' ⊆ A'` is a union of connected components of `A'` (as witnessed by the
hypothesis that the component of every point of `A' \ α'` lies in `A' \ α'`), and the ambient
space is locally connected, then `A' \ α'` is open: it is the union of the open sets
`connectedComponentIn A' x` for `x ∈ A' \ α'`. -/
theorem isOpen_diff_of_isOpen_of_comp_subset {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {A' α' : Set X} (hA'op : IsOpen A')
    (hcomp : ∀ x ∈ A', x ∉ α' → connectedComponentIn A' x ⊆ A' \ α') :
    IsOpen (A' \ α') := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hxA' : x ∈ A' := hx.1
  refine Filter.mem_of_superset
    ((IsOpen.connectedComponentIn (F := A') (x := x) hA'op).mem_nhds
      (mem_connectedComponentIn hxA')) ?_
  intro z hz
  exact hcomp x hxA' hx.2 hz

/-- **The component of a point of `K` at a point lying outside the component of `k₀` avoids that
component** (in the carrier `↥P.carrier`).  If `z` is connected to `x` inside
`Subtype.val ⁻¹' K` and its image in `ℝ³` lies in `connectedComponentIn K k₀`, then the image of
`z` is connected to `x` inside `K` and lies in the component of `k₀`, so `x` itself lies in that
component. -/
theorem connectedComponentIn_preimage_subset_diff {P : Work.CoreTopology.ParamTorus}
    {K : Set R3} (hKc : K ⊆ P.carrier) {k₀ : R3}
    {x : ↥P.carrier} (hx : (x : R3) ∈ K)
    (hxα : (x : R3) ∉ connectedComponentIn K k₀) :
    connectedComponentIn (Subtype.val ⁻¹' K : Set ↥P.carrier) x ⊆
      (Subtype.val ⁻¹' K : Set ↥P.carrier) \
        (Subtype.val ⁻¹' connectedComponentIn K k₀ : Set ↥P.carrier) := by
  intro z hz
  refine ⟨connectedComponentIn_subset _ _ hz, fun hzα => ?_⟩
  have himg : (z : R3) ∈ connectedComponentIn
      (Subtype.val '' (Subtype.val ⁻¹' K : Set ↥P.carrier)) (x : R3) :=
    ContinuousOn.image_connectedComponentIn_subset (f := (Subtype.val : ↥P.carrier → R3))
      continuous_subtype_val.continuousOn
      (show x ∈ (Subtype.val ⁻¹' K : Set ↥P.carrier) from hx) ⟨z, hz, rfl⟩
  have himageK : Subtype.val '' (Subtype.val ⁻¹' K : Set ↥P.carrier) = K :=
    Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hKc)
  rw [himageK] at himg
  have hzαK : (z : R3) ∈ connectedComponentIn K k₀ := hzα
  have heq : connectedComponentIn K (x : R3) = connectedComponentIn K k₀ := by
    rw [connectedComponentIn_eq himg, (connectedComponentIn_eq hzαK).symm]
  exact hxα (heq ▸ mem_connectedComponentIn hx)

theorem windingOf_eq_zero_of_not_subset_components {P : Work.CoreTopology.ParamTorus}
    {A B : Set LeanEval.KnotTheory.PardonDistortion.R3}
    {a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (hAop : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hBop : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (ha₀ : a₀ ∈ A) (hb₀ : b₀ ∈ B)
    (hABα : A ∩ B ⊆ connectedComponentIn A a₀)
    (hABβ : A ∩ B ⊆ connectedComponentIn B b₀)
    (hVA : Work.SurgeryInvariance.WindingSpan P A = ⊥)
    (hVB : Work.SurgeryInvariance.WindingSpan P B = ⊥)
    (γ : Work.CoreTopology.ClosedCurve P)
    (hγ : ∀ t : ℝ, γ t ∈ A ∪ B)
    (hnot : ¬ Set.range γ.γ ⊆ connectedComponentIn A a₀ ∪ connectedComponentIn B b₀) :
    Work.SurgeryInvariance.windingOf P γ = 0 := by
  classical
  -- the surface is locally connected, so components of carrier-open sets are open
  haveI : LocallyConnectedSpace ↥P.carrier := locallyConnected_carrier P
  -- the two components, and the curve lifted to the carrier
  set α : Set R3 := connectedComponentIn A a₀ with hα
  set β : Set R3 := connectedComponentIn B b₀ with hβ
  set γX : ℝ → ↥P.carrier := fun t => ⟨γ t, γ.mem t⟩ with hγX
  have hγXc : Continuous γX := γ.cont.subtype_mk γ.mem
  -- the four pieces `α`, `A \ α`, `β`, `B \ β`, lifted to the carrier
  set A' : Set ↥P.carrier := Subtype.val ⁻¹' A with hA'
  set B' : Set ↥P.carrier := Subtype.val ⁻¹' B with hB'
  set α' : Set ↥P.carrier := Subtype.val ⁻¹' α with hα'
  set β' : Set ↥P.carrier := Subtype.val ⁻¹' β with hβ'
  have hA'op : IsOpen A' := by rw [hA']; exact hAop
  have hB'op : IsOpen B' := by rw [hB']; exact hBop
  have hα'op : IsOpen α' := by
    rw [hα', hα]
    exact isOpenInCarrier_connectedComponentIn hAop hAc a₀
  have hβ'op : IsOpen β' := by
    rw [hβ', hβ]
    exact isOpenInCarrier_connectedComponentIn hBop hBc b₀
  -- `A \ α` and `B \ β` are unions of components of `A`, resp. `B`, hence open
  have hP2op : IsOpen (A' \ α') := by
    refine isOpen_diff_of_isOpen_of_comp_subset (A' := A') (α' := α') hA'op ?_
    intro x hxA hxα
    have hxK : (x : R3) ∈ A := by rw [hA'] at hxA; exact hxA
    have hxα' : (x : R3) ∉ connectedComponentIn A a₀ := by
      intro h; exact hxα (by rw [hα', hα]; exact h)
    rw [hA', hα']
    exact connectedComponentIn_preimage_subset_diff hAc hxK hxα'
  have hP4op : IsOpen (B' \ β') := by
    refine isOpen_diff_of_isOpen_of_comp_subset (A' := B') (α' := β') hB'op ?_
    intro x hxB hxβ
    have hxK : (x : R3) ∈ B := by rw [hB'] at hxB; exact hxB
    have hxβ' : (x : R3) ∉ connectedComponentIn B b₀ := by
      intro h; exact hxβ (by rw [hβ', hβ]; exact h)
    rw [hB', hβ']
    exact connectedComponentIn_preimage_subset_diff hBc hxK hxβ'
  -- the two pieces meet only inside the distinguished components
  have hABα' : A' ∩ B' ⊆ α' := by
    intro x hx
    rw [hA', hB'] at hx
    have hx' : (x : R3) ∈ A ∩ B := hx
    rw [hα', hα]
    exact hABα hx'
  have hABβ' : A' ∩ B' ⊆ β' := by
    intro x hx
    rw [hA', hB'] at hx
    have hx' : (x : R3) ∈ A ∩ B := hx
    rw [hβ', hβ]
    exact hABβ hx'
  -- the image of the lifted curve is preconnected
  have hS'pre : IsPreconnected (Set.range γX) := isPreconnected_range hγXc
  have hS'sub : Set.range γX ⊆ A' ∪ B' := by
    rintro x ⟨t, rfl⟩
    rw [hA', hB']
    simpa using hγ t
  -- the two covers by an "isolated" piece and the union of the remaining three
  have hcover1 : Set.range γX ⊆ (A' \ α') ∪ (α' ∪ B') := by
    rintro x ⟨t, rfl⟩
    rcases hS'sub ⟨t, rfl⟩ with h1 | h1
    · by_cases h2 : γX t ∈ α'
      · exact Or.inr (Or.inl h2)
      · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inr h1)
  have hcover2 : Set.range γX ⊆ (B' \ β') ∪ (β' ∪ A') := by
    rintro x ⟨t, rfl⟩
    rcases hS'sub ⟨t, rfl⟩ with h1 | h1
    · exact Or.inr (Or.inr h1)
    · by_cases h2 : γX t ∈ β'
      · exact Or.inr (Or.inl h2)
      · exact Or.inl ⟨h1, h2⟩
  -- the "isolated" piece is disjoint from the union of the other three
  have hI : ¬ ((Set.range γX ∩ (A' \ α')).Nonempty ∧
      (Set.range γX ∩ (α' ∪ B')).Nonempty) := by
    rintro ⟨⟨x, hx1, hx2⟩, ⟨y, hy1, hy2⟩⟩
    have h := hS'pre (A' \ α') (α' ∪ B') hP2op (hα'op.union hB'op) hcover1
      ⟨x, hx1, hx2⟩ ⟨y, hy1, hy2⟩
    obtain ⟨z, _hzs, hzu, hzv⟩ := h
    rcases hzv with hzv | hzv
    · exact hzu.2 hzv
    · exact hzu.2 (hABα' ⟨hzu.1, hzv⟩)
  have hII : ¬ ((Set.range γX ∩ (B' \ β')).Nonempty ∧
      (Set.range γX ∩ (β' ∪ A')).Nonempty) := by
    rintro ⟨⟨x, hx1, hx2⟩, ⟨y, hy1, hy2⟩⟩
    have h := hS'pre (B' \ β') (β' ∪ A') hP4op (hβ'op.union hA'op) hcover2
      ⟨x, hx1, hx2⟩ ⟨y, hy1, hy2⟩
    obtain ⟨z, _hzs, hzu, hzv⟩ := h
    rcases hzv with hzv | hzv
    · exact hzu.2 hzv
    · exact hzu.2 (hABβ' ⟨hzv, hzu.1⟩)
  rcases Set.eq_empty_or_nonempty (Set.range γX ∩ (α' ∪ B')) with hempty1 | hne1
  · -- the curve avoids `α ∪ B`, hence lies in `A`
    apply windingOf_eq_zero_of_range_subset hVA γ
    intro t
    have h1 : γX t ∈ Set.range γX := ⟨t, rfl⟩
    have h2 : γX t ∉ α' ∪ B' := by
      intro hcon
      have : γX t ∈ Set.range γX ∩ (α' ∪ B') := ⟨h1, hcon⟩
      rw [hempty1] at this
      exact this
    rcases hS'sub h1 with h3 | h3
    · by_cases h4 : γX t ∈ α'
      · exact absurd (Or.inl h4) h2
      · rw [hA'] at h3; exact h3
    · exact absurd (Or.inr h3) h2
  · rcases Set.eq_empty_or_nonempty (Set.range γX ∩ (β' ∪ A')) with hempty2 | hne2
    · -- the curve avoids `β ∪ A`, hence lies in `B`
      apply windingOf_eq_zero_of_range_subset hVB γ
      intro t
      have h1 : γX t ∈ Set.range γX := ⟨t, rfl⟩
      have h2 : γX t ∉ β' ∪ A' := by
        intro hcon
        have : γX t ∈ Set.range γX ∩ (β' ∪ A') := ⟨h1, hcon⟩
        rw [hempty2] at this
        exact this
      rcases hS'sub h1 with h3 | h3
      · exact absurd (Or.inr h3) h2
      · by_cases h4 : γX t ∈ β'
        · exact absurd (Or.inl h4) h2
        · rw [hB'] at h3; exact h3
    · -- the curve meets both `α ∪ B` and `β ∪ A`, so it is contained in `α ∪ β`
      exfalso
      have hPe2 : Set.range γX ∩ (A' \ α') = ∅ := by
        by_contra hne
        exact hI ⟨Set.nonempty_iff_ne_empty.mpr hne, hne1⟩
      have hPe4 : Set.range γX ∩ (B' \ β') = ∅ := by
        by_contra hne
        exact hII ⟨Set.nonempty_iff_ne_empty.mpr hne, hne2⟩
      apply hnot
      rintro z ⟨t, rfl⟩
      have h1 : γX t ∈ Set.range γX := ⟨t, rfl⟩
      rcases hS'sub h1 with h3 | h3
      · left
        by_contra h4
        have hneg : γX t ∉ α' := by rw [hα']; exact h4
        have : γX t ∈ Set.range γX ∩ (A' \ α') := ⟨h1, h3, hneg⟩
        rw [hPe2] at this
        exact this
      · right
        by_contra h4
        have hneg : γX t ∉ β' := by rw [hβ']; exact h4
        have : γX t ∈ Set.range γX ∩ (B' \ β') := ⟨h1, h3, hneg⟩
        rw [hPe4] at this
        exact this

end

end Work.PinchLemma3.ClosedDiscA
