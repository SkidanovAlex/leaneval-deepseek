import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.DiscPair.discPairExtension
import Submission.Work.Serre.DiscPair.cylPairDefs
import Submission.Work.Thom.relCohMap_comp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cellwise non-vanishing of the Thom class: the formal reduction

Let `q : C(X, Γ)` be a Serre fibration and `U` a relative class in
`H^n(cyl q, range (cylIncl q); ℚ)`.  For a subset `V ⊆ Γ` write

`U|_V ∈ H^n(π⁻¹V, (π⁻¹V) ∩ A)`,   `A := range (cylIncl q)`,   `π := cylRetract q`,

for the restriction of `U` to the part of the mapping cylinder lying over `V`.

The content of this file is the *monotonicity* of that restriction, in its sharpest form: for
`W ⊆ V` the restriction `U|_W` is the further restriction of `U|_V`, hence

  `U|_W ≠ 0`  ⟹  `U|_V ≠ 0`.

Consequences (proved below, and the reason the file exists):

* **cellwise non-vanishing from a boundary fibre** — for the crux of the CW-model Thom case
  (`Γ' = attachCells (D-2) Γ ι f`) and sets `W ⊆ V ⊆ Γ'` with `W` the preimage of a point
  `b ∈ V`, a non-zero fibre value of `U` at `b` forces `U|_V ≠ 0`.  Taking `V` the part of the
  cylinder over a (closed) cell and `b` a point of its attaching sphere — which lies in the *old*
  part `S = range (attachIncl …)`, where the induction hypothesis is available — this is the
  "CVN" statement of `Submission/Work/Serre/CWMODEL_CVN_NOTES.md` §3: the cellwise non-vanishing
  of the Thom class follows from its fibre values on the old part.  No transport of fibre values
  along paths and no monodromy input is used.

* **the descent to the old part** — for `b ∈ S` the fibre value of the extension `U` of the old
  class `U₀` equals the fibre value of `U₀` (functoriality of the restriction along
  `π⁻¹{b} ⊆ A₂ ⊆ cyl q`); this is what supplies the input of the previous bullet from the
  induction hypothesis over `S`.

Both statements are instances of the functoriality of `Work.Thom.relCohMap`
(`Work.Thom.relCohMap_comp`); the only geometric input is that the relevant subsets are nested.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Monotonicity of a non-zero relative restriction -/

/-- **Monotonicity of a non-zero relative restriction.**  For `A ⊆ X`, subsets `W ⊆ V ⊆ X` and a
class `u ∈ H^n(X,A;ℚ)`: if the restriction of `u` to the pair `(W, W ∩ A)` is non-zero, then so is
its restriction to the pair `(V, V ∩ A)`. -/
theorem relCohMap_restrict_ne_zero {X : Type} [TopologicalSpace X] (A : Set X) {W V : Set X}
    (hWV : W ⊆ V) (n : ℕ) (u : Work.Thom.RelCoh ℚ n X A)
    (h : (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥W, X))
          {x : ↥W | (x : X) ∈ A} A (fun _ hx => hx) ℚ n).hom u ≠ 0) :
    (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
      {x : ↥V | (x : X) ∈ A} A (fun _ hx => hx) ℚ n).hom u ≠ 0 := by
  intro h0
  -- the inclusion `W ⊆ V` as a map of pairs
  have hcomp := Work.Thom.relCohMap_comp
    ({x : ↥W | (x : X) ∈ A}) ({x : ↥V | (x : X) ∈ A}) A
    (⟨fun w => ⟨w.1, hWV w.2⟩,
        continuous_subtype_val.subtype_mk (fun w => hWV w.2)⟩ : C(↥W, ↥V))
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
    (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => hx) ℚ n
  have hkey : (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥W, X))
        {x : ↥W | (x : X) ∈ A} A (fun _ hx => hx) ℚ n).hom u
      = (Work.Thom.relCohMap
          (⟨fun w => ⟨w.1, hWV w.2⟩,
              continuous_subtype_val.subtype_mk (fun w => hWV w.2)⟩ : C(↥W, ↥V))
          {x : ↥W | (x : X) ∈ A} {x : ↥V | (x : X) ∈ A} (fun _ hx => hx) ℚ n).hom
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
          {x : ↥V | (x : X) ∈ A} A (fun _ hx => hx) ℚ n).hom u) := by
    have h2 := congrArg (fun f => (ModuleCat.Hom.hom f) u) hcomp
    exact h2.symm
  rw [hkey, h0, map_zero] at h
  exact h rfl

/-! ## The cellwise non-vanishing, from a fibre value -/

/-- **Cellwise non-vanishing of a relative class from one of its fibre values.**  Let
`π := cylRetract q : cyl q → Γ`, `A := range (cylIncl q)`, and let `W = π⁻¹{b} ⊆ V = π⁻¹V₀` be
nested sets (`b ∈ V₀`).  If the restriction of `u ∈ H^n(cyl q, A;ℚ)` to the fibre pair over `b` is
non-zero, then so is its restriction to the pair over `V₀`.

For the crux this is applied with `V₀` the (closed) cell and `b` a point of its attaching sphere:
`π⁻¹{b} ⊆ π⁻¹V₀` because `b ∈ V₀`, and the fibre value at `b` is supplied by the induction
hypothesis over the old part (`fibreRestriction_oldPart_descent` below). -/
theorem cellRestriction_ne_zero_of_fibre_ne_zero {Γ : Type} [TopologicalSpace Γ]
    {X : Type} [TopologicalSpace X] (q : C(X, Γ)) (V₀ : Set Γ) (b : Γ) (hb : b ∈ V₀) (n : ℕ)
    (u : Work.Thom.RelCoh ℚ n (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (h : (Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)), Work.Serre.cyl q))
          {x : ↥((Work.Serre.cylRetract q) ⁻¹' ({b} : Set Γ)) |
            (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
          (Set.range (Work.Serre.cylIncl q)) (fun _ hx => hx) ℚ n).hom u ≠ 0) :
    (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' V₀), Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' V₀) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q)) (fun _ hx => hx) ℚ n).hom u ≠ 0 :=
  relCohMap_restrict_ne_zero _ (Set.preimage_mono (Set.singleton_subset_iff.mpr hb)) n u h

/-! ## The descent to the old part -/

/-- **The descent of a fibre value to the old part.**  Let `A ⊆ A₂ ⊆ cyl q` be nested subsets
(`A := range (cylIncl q)`, `A₂` the part of the cylinder over the old part), `u ∈ H^n(cyl q, A;ℚ)`
and `u₀ := u|_{(A₂, A₂∩A)}`.  For any `W ⊆ A₂` the restriction of `u` to `(W, W∩A)` equals the
restriction of `u₀`; in particular the fibre values of `u` over the old part are those of `u₀`. -/
theorem fibreRestriction_oldPart_descent {Γ : Type} [TopologicalSpace Γ]
    {X : Type} [TopologicalSpace X] (q : C(X, Γ)) {A A₂ : Set (Work.Serre.cyl q)} (hA : A ⊆ A₂)
    {W : Set (Work.Serre.cyl q)} (hW : W ⊆ A₂) (n : ℕ)
    (u : Work.Thom.RelCoh ℚ n (Work.Serre.cyl q) A) :
    (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥W, Work.Serre.cyl q))
        {x : ↥W | (x : Work.Serre.cyl q) ∈ A} A (fun _ hx => hx) ℚ n).hom u
      = (Work.Thom.relCohMap
          (⟨fun w => ⟨w.1, hW w.2⟩,
              continuous_subtype_val.subtype_mk (fun w => hW w.2)⟩ : C(↥W, ↥A₂))
          {x : ↥W | (x : Work.Serre.cyl q) ∈ A} {x : ↥A₂ | (x : Work.Serre.cyl q) ∈ A}
          (fun _ hx => hx) ℚ n).hom
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A₂, Work.Serre.cyl q))
          {x : ↥A₂ | (x : Work.Serre.cyl q) ∈ A} A (fun _ hx => hx) ℚ n).hom u) := by
  have hcomp := Work.Thom.relCohMap_comp
    ({x : ↥W | (x : Work.Serre.cyl q) ∈ A}) ({x : ↥A₂ | (x : Work.Serre.cyl q) ∈ A}) A
    (⟨fun w => ⟨w.1, hW w.2⟩,
        continuous_subtype_val.subtype_mk (fun w => hW w.2)⟩ : C(↥W, ↥A₂))
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A₂, Work.Serre.cyl q))
    (fun _ hx => hx) (fun _ hx => hx) (fun _ hx => hx) ℚ n
  have h2 := congrArg (fun f => (ModuleCat.Hom.hom f) u) hcomp
  exact h2.symm

end

end Work.Serre
