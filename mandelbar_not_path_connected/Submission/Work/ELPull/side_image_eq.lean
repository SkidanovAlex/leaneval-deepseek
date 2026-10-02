import Mathlib
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.ELPull.side_image_eq`: the image of a side of a co-landing pair

This file proves the topological statement underlying the "side transfer" of the pull-back step
of the equator-leak argument: if `Tantibar c` maps the curve of a co-landing pair `G` into the
curve of a co-landing pair `Q`, and the side `pairSide hN G` of `G` does not meet the preimage
of the curve of `Q`, then `Tantibar c` maps that whole side onto the side of `Q` which it meets.

The mathematics is the following.  Write `f = Tantibar c`, `X = pairCurve hN G`,
`Y = pairCurve hN Q`, `S = pairSide hN G` and `C = arcSide hN Q q p`, so that

* `f '' X ⊆ Y` (`himg`),
* `S ∩ f ⁻¹' Y = ∅` (`hmiss`),
* some point of `S` is mapped into `C` (`hpt`).

The map `f = z ↦ z̄² + c` is continuous, an **open** map (the conjugation is a homeomorphism and
`z ↦ z²` is an open quotient map), and a **closed** map (it is a composition of the homeomorphism
`conj` with a polynomial, and polynomial maps over a proper normed ring are closed).

1. *Containment.*  `S` is a component of the complement of the closed set `X`, hence preconnected;
   since `f` is continuous, `f '' S` is preconnected, it avoids `Y` by `hmiss`, and it meets the
   component `C`; a preconnected subset of the complement of `Y` which meets a component of that
   complement is contained in it.  So `f '' S ⊆ C`.

2. *Surjectivity.*  `X` being closed, the component `S` of `Xᶜ` is open (ℂ is locally connected),
   so `f '' S` is open.  On the other hand `S` is a maximal preconnected subset of `Xᶜ`, hence
   `closure S ⊆ S ∪ X`; since `f` is closed, `closure (f '' S) = f '' closure S`, so
   `closure (f '' S) ⊆ f '' S ∪ Y`, i.e. `f '' S` is relatively closed in `C` (which avoids `Y`).
   A nonempty subset of the preconnected set `C` which is both relatively open and relatively
   closed must be all of `C`: `C ⊆ f '' S`.

Nothing dynamical is used beyond the three topological properties of `f` and the closedness of
the pair curve of `G` (`PB1Top.closed`).
-/

namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar)
open Set Function

noncomputable section

/-! ## The three topological properties of `Tantibar c`

`Tantibar c z = (starRingEnd ℂ z) ^ 2 + c = conj (z ^ 2 + conj c)`: it is the composition of the
homeomorphism `conj` with the quadratic polynomial `z ↦ z ^ 2 + conj c`. -/

private lemma continuous_tantibar (c : ℂ) : Continuous (Tantibar c) := by
  have h : Tantibar c = fun z : ℂ => (starRingEnd ℂ z) ^ 2 + c := rfl
  rw [h]; fun_prop

private lemma tantibar_eq_comp (c : ℂ) : Tantibar c
    = (starRingEnd ℂ : ℂ → ℂ) ∘ (fun z : ℂ => z ^ 2 + starRingEnd ℂ c) := by
  funext z
  simp [Tantibar, Function.comp, map_add, map_pow]

/-- Complex conjugation is a closed map: it is an involution, so the image of a set is its
preimage, and preimages of closed sets under a continuous map are closed. -/
private lemma isClosedMap_conj : IsClosedMap (starRingEnd ℂ : ℂ → ℂ) := by
  intro s hs
  have heq : (starRingEnd ℂ : ℂ → ℂ) '' s = (starRingEnd ℂ : ℂ → ℂ) ⁻¹' s := by
    ext w; constructor
    · rintro ⟨u, hu, rfl⟩; simpa using hu
    · intro hw; exact ⟨starRingEnd ℂ w, hw, by simp⟩
  rw [heq]; exact hs.preimage Complex.continuous_conj

/-- Complex conjugation is an open map, by the same involution argument. -/
private lemma sie_isOpenMap_conj : IsOpenMap (starRingEnd ℂ : ℂ → ℂ) := by
  intro U hU
  have heq : (starRingEnd ℂ : ℂ → ℂ) '' U = (starRingEnd ℂ : ℂ → ℂ) ⁻¹' U := by
    ext w; constructor
    · rintro ⟨u, hu, rfl⟩; simpa using hu
    · intro hw; exact ⟨starRingEnd ℂ w, hw, by simp⟩
  rw [heq]; exact hU.preimage Complex.continuous_conj

/-- `Tantibar c` is a closed map: a polynomial map is closed over a proper normed ring
(`Polynomial.isClosedMap_eval`), and conjugation is a closed map. -/
private lemma isClosedMap_tantibar (c : ℂ) : IsClosedMap (Tantibar c) := by
  have hp : IsClosedMap (fun z : ℂ => z ^ 2 + starRingEnd ℂ c) := by
    have hfun : (fun z : ℂ => z ^ 2 + starRingEnd ℂ c)
        = fun x : ℂ => Polynomial.eval x (Polynomial.X ^ 2 + Polynomial.C (starRingEnd ℂ c)) := by
      funext z; simp
    rw [hfun]
    exact Polynomial.isClosedMap_eval (Polynomial.X ^ 2 + Polynomial.C (starRingEnd ℂ c))
  rw [tantibar_eq_comp c]
  exact isClosedMap_conj.comp hp

/-- `Tantibar c` is an open map: `z ↦ z ^ 2` is an open quotient map
(`Complex.isOpenQuotientMap_pow`), translation is a homeomorphism (its image is the preimage
under the inverse translation), and conjugation is open. -/
private lemma isOpenMap_tantibar (c : ℂ) : IsOpenMap (Tantibar c) := by
  have hsq : IsOpenMap (fun z : ℂ => z ^ 2) := (Complex.isOpenQuotientMap_pow 2).isOpenMap
  have htr : IsOpenMap (fun w : ℂ => w + starRingEnd ℂ c) := by
    intro U hU
    have heq : (fun w : ℂ => w + starRingEnd ℂ c) '' U
        = (fun w : ℂ => w - starRingEnd ℂ c) ⁻¹' U := by
      ext w; constructor
      · rintro ⟨u, hu, rfl⟩; simpa using hu
      · intro hw; exact ⟨w - starRingEnd ℂ c, hw, by ring⟩
    rw [heq]; exact hU.preimage (by fun_prop)
  rw [tantibar_eq_comp c]
  exact sie_isOpenMap_conj.comp (htr.comp hsq)

/-! ## The closure of a component of an open set -/

/-- **The closure of a component of an open set stays inside the component or on its boundary.**
If `X` is open and `z` lies in the closure of the component `connectedComponentIn X y`, then
either `z` is in the component, or `z ∉ X`.

Indeed, if `z ∈ X` there is a ball about `z` inside `X`; since `z` is a limit point of the
component, that ball meets it, and then the component together with the ball is a preconnected
subset of `X` meeting the component, so it is contained in the component by maximality; hence
`z` itself lies in the component. -/
private lemma closure_connectedComponentIn_subset {X : Set ℂ} (hX : IsOpen X) (y : ℂ) :
    closure (connectedComponentIn X y) ⊆ connectedComponentIn X y ∪ Xᶜ := by
  intro z hz
  by_cases hzS : z ∈ connectedComponentIn X y
  · exact Or.inl hzS
  · refine Or.inr ?_
    intro hzX
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hX z hzX
    obtain ⟨c₁, hc₁S, hc₁d⟩ := Metric.mem_closure_iff.mp hz ε hε
    have hc₁B : c₁ ∈ Metric.ball z ε := by rw [Metric.mem_ball, dist_comm]; exact hc₁d
    have hconn : IsPreconnected (connectedComponentIn X y ∪ Metric.ball z ε) :=
      IsPreconnected.union c₁ hc₁S hc₁B isPreconnected_connectedComponentIn
        (convex_ball z ε).isPreconnected
    have hsub : connectedComponentIn X y ∪ Metric.ball z ε ⊆ X := by
      rintro w (hw | hw)
      · exact connectedComponentIn_subset X y hw
      · exact hball hw
    have hsub2 := hconn.subset_connectedComponentIn (Or.inl hc₁S) hsub
    have hz' : z ∈ connectedComponentIn X c₁ := hsub2 (Or.inr (Metric.mem_ball_self hε))
    rw [← connectedComponentIn_eq hc₁S] at hz'
    exact hzS hz'

/-! ## The abstract form of the statement -/

/-- **A side is mapped onto a side.**  Let `f : ℂ → ℂ` be continuous, open and closed, let `X`
be closed, and let `y₀`, `y₁` be points of `ℂ`.  If

* `f` maps `X` into `Y`,
* the component of `Xᶜ` at `y₀` does not meet `f ⁻¹' Y`,
* some point of that component is mapped into the component of `Yᶜ` at `y₁`,

then `f` maps the component of `Xᶜ` at `y₀` *onto* the component of `Yᶜ` at `y₁`. -/
private lemma image_connectedComponentIn_eq {f : ℂ → ℂ} (hfc : Continuous f) (hfo : IsOpenMap f)
    (hfm : IsClosedMap f) {X Y : Set ℂ} (hX : IsClosed X) (y₀ y₁ : ℂ)
    (himg : f '' X ⊆ Y) (hmiss : Disjoint (connectedComponentIn Xᶜ y₀) (f ⁻¹' Y))
    (hpt : ∃ x ∈ connectedComponentIn Xᶜ y₀, f x ∈ connectedComponentIn Yᶜ y₁) :
    f '' connectedComponentIn Xᶜ y₀ = connectedComponentIn Yᶜ y₁ := by
  set S : Set ℂ := connectedComponentIn Xᶜ y₀ with hS
  set C : Set ℂ := connectedComponentIn Yᶜ y₁ with hC
  obtain ⟨x, hxS, hxC⟩ := hpt
  have hSopen : IsOpen S := hX.isOpen_compl.connectedComponentIn
  have hSpre : IsPreconnected S := isPreconnected_connectedComponentIn
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  -- `f '' S` avoids the curve `Y`
  have hfS_Y : f '' S ⊆ Yᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    exact fun h => Set.disjoint_left.mp hmiss hz h
  -- the forward inclusion: a preconnected set meeting a component of `Yᶜ` lies in it
  have hfS_C : f '' S ⊆ C := by
    have h2 := hSpre.image f hfc.continuousOn
    have h3 := h2.subset_connectedComponentIn (show f x ∈ f '' S from ⟨x, hxS, rfl⟩) hfS_Y
    rwa [show connectedComponentIn Yᶜ (f x) = C from (connectedComponentIn_eq hxC).symm] at h3
  -- the closure of `f '' S` is the image of the closure of `S`, which is `S ∪ X` up to `X`
  have hcl_eq : closure (f '' S) = f '' closure S := hfm.closure_image_eq_of_continuous hfc S
  have hclS : closure S ⊆ S ∪ X := by
    simpa [hS, compl_compl] using closure_connectedComponentIn_subset hX.isOpen_compl y₀
  have hclsub : closure (f '' S) ∩ C ⊆ f '' S := by
    rintro w ⟨hwcl, hwC⟩
    rw [hcl_eq] at hwcl
    obtain ⟨z, hzcl, hzw⟩ := hwcl
    rcases hclS hzcl with hzS | hzX
    · exact ⟨z, hzS, hzw⟩
    · exact absurd (hzw ▸ himg ⟨z, hzX, rfl⟩) (connectedComponentIn_subset Yᶜ y₁ hwC)
  -- a relatively clopen nonempty subset of the preconnected set `C` is all of `C`
  have hCsub : C ⊆ f '' S :=
    hCpre.subset_of_closure_inter_subset (hfo S hSopen) ⟨f x, hxC, ⟨x, hxS, rfl⟩⟩ hclsub
  exact Set.Subset.antisymm hfS_C hCsub

end

theorem side_image_eq {c : ℂ} (hN : DynB c) (htop : PB1Top hN)
    (G Q : CoPair hN) (q p : ℝ)
    (himg : LeanEval.ComplexAnalysis.Tantibar c '' pairCurve hN G ⊆ pairCurve hN Q)
    (hmiss : Disjoint (pairSide hN G)
      (LeanEval.ComplexAnalysis.Tantibar c ⁻¹' pairCurve hN Q))
    (hpt : ∃ x ∈ pairSide hN G, LeanEval.ComplexAnalysis.Tantibar c x ∈ arcSide hN Q q p) :
    LeanEval.ComplexAnalysis.Tantibar c '' pairSide hN G = arcSide hN Q q p := by
  have h := image_connectedComponentIn_eq (f := Tantibar c)
    (X := pairCurve hN G) (Y := pairCurve hN Q)
    (y₀ := hN.rayPt (G.a + arcLen G.a G.b / 2) 2)
    (y₁ := hN.rayPt (q + arcLen q p / 2) 2)
    (continuous_tantibar c) (isOpenMap_tantibar c) (isClosedMap_tantibar c) (htop.closed G)
    himg hmiss hpt
  simpa [pairSide, arcSide] using h

end Work.ELPull
