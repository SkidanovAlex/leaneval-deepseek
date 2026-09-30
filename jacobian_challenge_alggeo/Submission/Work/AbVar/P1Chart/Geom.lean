/-
Area AV: base change of `P¹` along a field extension.
-/
import Mathlib
import Submission.Work.AbVar.P1Chart.ChartK
import Submission.Work.AbVar.P1Chart.Cover
import Submission.Work.AbVar.P1Chart.Eq
import Submission.Work.AbVar.ProjectiveLine

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization MvPolynomial

noncomputable section

universe u

namespace Work.AbVar.P1Chart

/-- The two standard affine charts `D₊(X₀)`, `D₊(X₁)` of `P¹ = Proj k[X₀,X₁]`. -/
noncomputable def twoChartCover (k : Type u) [Field k] : (Proj (P1Grading k)).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (P1Grading k)
    (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) k)) (m := fun _ => 1)
    (fun i => X_mem k i) (fun _ => Nat.one_pos) (irrelevant_le_span_X k)

/-- The `k`-algebra structure map of the `i`-th chart ring, written as the composite used by
`P1`. -/
lemma algebraMap_awayAlg_comp (k : Type u) [Field k] (i : Fin 2) :
    (algebraMap ↥(P1Grading k 0) (AX k i)).comp (Work.AbVar.p1BaseEquiv k).toRingHom
      = algebraMap k (AX k i) := by
  rw [HomogeneousLocalization.algebraMap_eq, p1BaseEquiv_toRingHom_eq,
    ProjectiveLine.algebraMap_awayAlg, ProjectiveLine.awayAlg]

/-- The chart `D₊(Xᵢ)` of `P¹`, pushed forward to `Spec k`, is `Spec` of the `k`-algebra structure
map of the chart ring. -/
theorem chart_eq (k : Type u) [Field k] (i : Fin 2) :
    (twoChartCover k).f i ≫ (Work.AbVar.P1 k).hom
      = Spec.map (CommRingCat.ofHom (algebraMap k (AX k i))) := by
  change Proj.awayι (P1Grading k) (MvPolynomial.X i) (X_mem k i) Nat.one_pos ≫
    (Work.AbVar.P1 k).hom = Spec.map (CommRingCat.ofHom (algebraMap k (AX k i)))
  rw [Work.AbVar.p1_hom k, ← Category.assoc, Proj.awayι_toSpecZero,
    ← HomogeneousLocalization.algebraMap_eq, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    algebraMap_awayAlg_comp]

/-- A topological space covered by two irreducible open subsets whose intersection is nonempty
is irreducible. -/
theorem irreducibleSpace_of_two_opens {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hUi : IsIrreducible U) (hVi : IsIrreducible V) (hne : (U ∩ V).Nonempty) :
    IrreducibleSpace X := by
  obtain ⟨p, hpU, hpV⟩ := hne
  have key : ∀ {s : Set X}, IsOpen s → s.Nonempty → (s ∩ U).Nonempty := by
    intro s hs hsne
    by_contra h
    have hU' : ∀ x ∈ s, x ∉ U := fun x hxs hxU => h ⟨x, hxs, hxU⟩
    have hsV : s ⊆ V := by
      intro x hx
      rcases (show x ∈ U ∪ V from hcov ▸ Set.mem_univ x) with h' | h'
      · exact absurd h' (hU' x hx)
      · exact h'
    haveI : IrreducibleSpace V := Subtype.irreducibleSpace hVi
    have h1 : ((Subtype.val : V → X) ⁻¹' s).Nonempty := by
      obtain ⟨x, hx⟩ := hsne
      exact ⟨⟨x, hsV hx⟩, hx⟩
    have h2 : ((Subtype.val : V → X) ⁻¹' U).Nonempty := ⟨⟨p, hpV⟩, hpU⟩
    obtain ⟨v, hvs, hvU⟩ := nonempty_preirreducible_inter
      (hs.preimage continuous_subtype_val) (hU.preimage continuous_subtype_val) h1 h2
    exact hU' v.1 hvs hvU
  have hPre : PreirreducibleSpace X :=
    PreirreducibleSpace.of_forall_nonempty_inter (fun s t hs ht hsne htne => by
      haveI : IrreducibleSpace U := Subtype.irreducibleSpace hUi
      obtain ⟨x, hxs, hxU⟩ := key hs hsne
      obtain ⟨y, hyt, hyU⟩ := key ht htne
      obtain ⟨z, hzs, hzt⟩ := nonempty_preirreducible_inter
        (s := (Subtype.val : U → X) ⁻¹' s) (t := (Subtype.val : U → X) ⁻¹' t)
        (hs.preimage continuous_subtype_val) (ht.preimage continuous_subtype_val)
        ⟨⟨x, hxU⟩, hxs⟩ ⟨⟨y, hyU⟩, hyt⟩
      exact ⟨z.1, hzs, hzt⟩)
  exact { toPreirreducibleSpace := hPre, toNonempty := ⟨p⟩ }

end Work.AbVar.P1Chart
