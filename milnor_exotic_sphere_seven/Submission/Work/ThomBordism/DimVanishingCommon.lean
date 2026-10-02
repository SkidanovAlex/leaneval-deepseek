/-
# Common helpers for the dimension vanishing of the homology of a charted space

The target lemma `Work.ThomBordism.dimVanishingCharted` states that the singular homology of a
compact Hausdorff space charted over `ℝ^N` vanishes in degrees `> N`.  The proof covers `M` by
finitely many coordinate balls, and the vanishing is accumulated over the finite union with the
Mayer–Vietoris sequence.

This file collects the definitions and elementary lemmas that are shared by the individual pieces
of that proof:

* `singH` — the `n`-th singular homology with `ℤ` coefficients;
* `isZero_singH_of_homeo`, `isZero_singH_of_set_eq` — transport of vanishing along homeomorphisms;
* `homeoSubtypeOfSubset` — the canonical homeomorphism `A ≃ {x : ↥B | (x : α) ∈ A}` for `A ⊆ B`,
  used to compare the pieces of the cover with the corresponding subsets of their union;
* `chartImageHomeo` — the restriction of a chart to a subset of its source, as a homeomorphism
  onto its image;
* `chartBall` — the coordinate ball piece of the cover at a point, together with `isOpen_chartBall`
  and `mem_chartBall`.
-/
import Mathlib
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

/-- `H_n(X; ℤ)`, the `n`-th singular homology of `X` with `ℤ` coefficients. -/
abbrev singH (X : TopCat) (n : ℕ) : ModuleCat ℤ := (Work.Cohomology.singularChains ℤ X).homology n

/-- **Vanishing of singular homology is a homeomorphism invariant** (contravariant form): if the
`n`-th homology of `Y` vanishes then so does that of any space homeomorphic to `Y`. -/
theorem isZero_singH_of_homeo {X Y : TopCat} (e : X ≃ₜ Y) (n : ℕ) (h : IsZero (singH Y n)) :
    IsZero (singH X n) :=
  Work.Cohomology.isZero_homology_of_homotopyEquiv e.toHomotopyEquiv n h

/-- Vanishing of singular homology transports along an equality of the underlying sets. -/
theorem isZero_singH_of_set_eq {α : Type} [TopologicalSpace α] {S T : Set α} (h : S = T) (n : ℕ)
    (hS : IsZero (singH (TopCat.of ↥S) n)) : IsZero (singH (TopCat.of ↥T) n) :=
  isZero_singH_of_homeo (Homeomorph.setCongr h).symm n hS

/-- **The canonical homeomorphism of a subset with the corresponding subset of a larger set**:
for `A ⊆ B` the identity of `α` induces a homeomorphism `A ≃ {x : ↥B | (x : α) ∈ A}`. -/
def homeoSubtypeOfSubset {α : Type*} [TopologicalSpace α] {A B : Set α} (h : A ⊆ B) :
    ↥A ≃ₜ ↥{x : ↥B | (x : α) ∈ A} where
  toFun x := ⟨⟨x.1, h x.2⟩, x.2⟩
  invFun y := ⟨y.1.1, y.2⟩
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := by
    have h1 : Continuous fun x : ↥A => (⟨x.1, h x.2⟩ : ↥B) :=
      Continuous.subtype_mk continuous_subtype_val (fun x => h x.2)
    exact Continuous.subtype_mk h1 (fun x => x.2)
  continuous_invFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.2)

/-- **The restriction of a chart to a subset of its source**, as a homeomorphism onto the image. -/
def chartImageHomeo {M : TopCat} {E : Type*} [TopologicalSpace E]
    (e : OpenPartialHomeomorph M E) (W : Set M) (hW : W ⊆ e.source) : ↥W ≃ₜ ↥(e '' W) where
  toFun x := ⟨e x.1, Set.mem_image_of_mem (fun y => e y) x.2⟩
  invFun y := ⟨e.symm y.1, by
    obtain ⟨a, ha, hya⟩ := (Set.mem_image (fun y => e y) W y.1).mp y.2
    have h1 : e.symm y.1 = a := by rw [← hya]; exact e.left_inv (hW ha)
    rw [h1]; exact ha⟩
  left_inv x := by
    apply Subtype.ext
    exact e.left_inv (hW x.2)
  right_inv y := by
    obtain ⟨a, ha, hya⟩ := (Set.mem_image (fun y => e y) W y.1).mp y.2
    have hy : y.1 ∈ e.target := hya ▸ e.map_source (hW ha)
    apply Subtype.ext
    exact e.right_inv hy
  continuous_toFun :=
    Continuous.subtype_mk
      (e.continuousOn.comp_continuous continuous_subtype_val (fun x => hW x.2)) _
  continuous_invFun :=
    Continuous.subtype_mk
      (e.continuousOn_symm.comp_continuous continuous_subtype_val (fun y => by
        obtain ⟨a, ha, hya⟩ := (Set.mem_image (fun y => e y) W y.1).mp y.2
        rw [← hya]; exact e.map_source (hW ha))) _

variable {N : ℕ} {M : TopCat}

/-- **The coordinate ball piece of the cover at a point `z`**, for a choice of positive radius
`ρ`: the preimage under the chart at `z`, intersected with the chart source, of the metric ball of
radius `ρ z` around the image of `z`. -/
def chartBall (N : ℕ) {M : TopCat} [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (ρ : M → ℝ) (z : M) : Set M :=
  (chartAt (EuclideanSpace ℝ (Fin N)) z) ⁻¹'
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin N)) z) z) (ρ z)
    ∩ (chartAt (EuclideanSpace ℝ (Fin N)) z).source

variable [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]

/-- The coordinate ball piece is open. -/
theorem isOpen_chartBall (ρ : M → ℝ) (z : M) : IsOpen (chartBall N ρ z) := by
  rw [chartBall, Set.inter_comm]
  exact (chartAt (EuclideanSpace ℝ (Fin N)) z).isOpen_inter_preimage Metric.isOpen_ball

/-- The centre of a coordinate ball piece lies in it. -/
theorem mem_chartBall (ρ : M → ℝ) (z : M) (hρ : 0 < ρ z) : z ∈ chartBall N ρ z :=
  ⟨Metric.mem_ball_self hρ, mem_chart_source _ z⟩

end

end Work.ThomBordism
