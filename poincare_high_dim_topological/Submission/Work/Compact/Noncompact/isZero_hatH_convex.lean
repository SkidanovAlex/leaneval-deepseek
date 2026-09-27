import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv
import Submission.Work.Compact.Noncompact.Convex.ball_compl_convex_homotopyEquiv_sphere
import Submission.Work.Compact.Noncompact.Convex.isZero_sphere_homology_of_le
import Submission.Work.Compact.Noncompact.Convex.isZero_relChains_ball_compl_convex_of

/-!
# Vanishing of the relative homology `H_k(M, M∖A)` of a compact convex piece of a chart, `k > n`

(Hatcher, *Algebraic Topology*, Lemma 3.27(b).)  For an `n`-manifold `M` (`n ≥ 1`), a chart
`e : M ⊇ e.source ≅ e.target ⊆ ℝⁿ`, and a compact convex `C ⊆ e.target`, the set
`A = e.source ∩ e⁻¹' C` is a compact piece of the chart, and `H_k(M, M∖A; ℤ) = 0` for every
`k > n`.  This is the "vanishing" half of Hatcher's Lemma 3.27 (the companion of the injectivity
`H_n(M, M∖A) → H_n(M, M∖{x})`, `Work.Compact.Noncompact.localHomology_injective`); it is the base
case `A` inside a single chart of the induction in `Work.Compact.Noncompact.eq_zero_of_forall_localMap_eq_zero`.

## Route

* `A = e.source ∩ e⁻¹' C = e.symm '' C` is compact (`isCompact_inter_preimage`), hence closed;
* **excision** (`Work.Cohomology.excision_relChainsMap_isIso`, relative small chains) replaces
  `M` by the chart source: `H_k(M, M∖A) ≅ H_k(e.source, e.source∖A)`;
* the **chart homeomorphism** `e` identifies the pair with `(e.target, e.target∖C)`
  (`Work.Cohomology.relChainsMapOf_homologyMap_isIso`, a homeomorphism of pairs is a
  quasi-isomorphism on relative chains);
* in the flat case (`isZero_relChains_open_compl_convex`: `U` open in `ℝⁿ`, `C ⊆ U` compact convex)
  two more excisions replace `(U, U∖C)` by `(ball c R, ball c R ∖ C)` for a ball containing `C`,
  the long exact sequence of the pair (`hPairδ_isIso'`) turns `H_k(ball, ball∖C)` into
  `H_{k-1}(ball c R ∖ C)` (`k ≥ 2` since `k > n ≥ 1` and the ball is contractible), and the convex
  set `C` is pushed radially inside the ball off itself onto a concentric sphere
  (`Work.Compact.Noncompact.Convex.ball_compl_convex_homotopyEquiv_sphere`), whose homology
  vanishes in degrees `≥ n` (`Work.Compact.Noncompact.Convex.isZero_sphere_homology_of_le`).

The degenerate case `C = ∅` gives `A = ∅`, i.e. the pair `(M, M)`, whose relative chain complex is
the cokernel of an isomorphism (`isZero_relChains_univ_homology`).
-/

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Compact.Noncompact

noncomputable section

/-! ## Utilities -/

lemma isIso_subtypeIncl_univ (X : TopCat) : IsIso (Work.Cohomology.subtypeIncl X Set.univ) := by
  refine ⟨TopCat.ofHom (Homeomorph.Set.univ X).symm, ?_, ?_⟩
  · ext x; rfl
  · ext x; rfl

lemma isZero_cokernel_of_isIso {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) [IsIso f] [HasCokernel f] : IsZero (cokernel f) := by
  rw [IsZero.iff_id_eq_zero]
  have h : cokernel.π f = 0 := (cancel_epi f).1 (by rw [cokernel.condition f, comp_zero])
  exact (cancel_epi (cokernel.π f)).1 (by rw [Category.comp_id, h, zero_comp])

lemma isZero_homology_of_isZero_complex {Z : ChainComplex (ModuleCat ℤ) ℕ} (h : IsZero Z)
    (k : ℕ) : IsZero (Z.homology k) := by
  have hX : IsZero (Z.X k) := by
    rw [IsZero.iff_id_eq_zero] at h ⊢
    have := congrArg (fun m : Z ⟶ Z => m.f k) h
    simpa using this
  exact ShortComplex.isZero_homology_of_isZero_X₂ (S := Z.sc k) hX

lemma isZero_relChains_univ_homology (X : TopCat) (k : ℕ) :
    IsZero ((Work.Cohomology.relChains X Set.univ).homology k) := by
  haveI : IsIso (Work.Cohomology.inclChains X Set.univ) := by
    haveI := isIso_subtypeIncl_univ X
    exact Functor.map_isIso _ (Work.Cohomology.subtypeIncl X Set.univ)
  exact isZero_homology_of_isZero_complex (isZero_cokernel_of_isIso _) k

lemma isCompact_inter_preimage {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCcpt : IsCompact C) (hCsub : C ⊆ e.target) :
    IsCompact (e.source ∩ e ⁻¹' C) := by
  rw [show e.source ∩ e ⁻¹' C = e.symm '' C from by
    ext x
    constructor
    · rintro ⟨hx, hxC⟩
      exact ⟨e x, hxC, e.left_inv hx⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨e.map_target (hCsub hy), ?_⟩
      show e (e.symm y) ∈ C
      rw [e.right_inv (hCsub hy)]
      exact hy]
  exact hCcpt.image_of_continuousOn (e.continuousOn_symm.mono hCsub)

/-! ## The flat statement -/

/-! ## The flat (Euclidean) case -/

theorem isZero_relChains_open_compl_convex {n k : ℕ} (hn : 1 ≤ n)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCvx : Convex ℝ C) (hCcpt : IsCompact C)
    (hCsub : C ⊆ U) (hk : n < k) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥U)
      {x : ↥U | (x : EuclideanSpace ℝ (Fin n)) ∈ Cᶜ}).homology k) := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · have hset : {x : ↥U | (x : EuclideanSpace ℝ (Fin n)) ∈ (∅ : Set (EuclideanSpace ℝ (Fin n)))ᶜ}
        = Set.univ := by
      ext x; simp
    rw [hset]
    exact isZero_relChains_univ_homology (TopCat.of ↥U) k
  · obtain ⟨c, hc⟩ := hCne
    obtain ⟨ρ, hρ⟩ : ∃ ρ, C ⊆ Metric.closedBall c ρ :=
      (Metric.isBounded_iff_subset_closedBall c).mp hCcpt.isBounded
    set R' : ℝ := max ρ 0 + 1 with hR'def
    set R : ℝ := R' + 1 with hRdef
    have hR'pos : 0 < R' := by rw [hR'def]; positivity
    have hR'R : R' < R := by rw [hRdef]; linarith
    have hRpos : 0 < R := by linarith
    have hCballR' : C ⊆ Metric.ball c R' := by
      intro x hx
      have h1 : dist x c ≤ ρ := Metric.mem_closedBall.mp (hρ hx)
      rw [Metric.mem_ball]
      have h2 : ρ ≤ max ρ 0 := le_max_left _ _
      rw [hR'def]
      linarith
    have hCballR : C ⊆ Metric.ball c R := by
      intro x hx
      have h1 := hCballR' hx
      rw [Metric.mem_ball] at h1 ⊢
      have h2 : R' ≤ R := le_of_lt hR'R
      linarith
    have hY : ∀ j : ℕ, n ≤ j → IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of {y : ↥(Metric.ball c R) // (y : EuclideanSpace ℝ (Fin n)) ∉ C})).homology j) := by
      intro j hj
      obtain ⟨e⟩ := Convex.ball_compl_convex_homotopyEquiv_sphere hCvx hc hR'pos hR'R hCballR'
      exact Work.Cohomology.isZero_homology_of_homotopyEquiv e j
        (Convex.isZero_sphere_homology_of_le hn c hR'pos hj)
    have hball := Convex.isZero_relChains_ball_compl_convex_of hn c hRpos hY hk
    have hCclosed : IsClosed C := hCcpt.isClosed
    have hAopen : IsOpen (Cᶜ : Set (EuclideanSpace ℝ (Fin n))) := hCclosed.isOpen_compl
    have hcov₁ : U ∪ Cᶜ = Set.univ := by
      ext x
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
      by_cases hx : x ∈ C
      · exact Or.inl (hCsub hx)
      · exact Or.inr hx
    have hcov₂ : Metric.ball c R ∪ Cᶜ = Set.univ := by
      ext x
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
      by_cases hx : x ∈ C
      · exact Or.inl (hCballR hx)
      · exact Or.inr hx
    haveI hiso₁ : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMap (TopCat.of (EuclideanSpace ℝ (Fin n))) U Cᶜ) k) :=
      Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (EuclideanSpace ℝ (Fin n))) U Cᶜ hU hAopen hcov₁ k
    haveI hiso₂ : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMap (TopCat.of (EuclideanSpace ℝ (Fin n)))
          (Metric.ball c R) Cᶜ) k) :=
      Work.Cohomology.excision_relChainsMap_isIso (TopCat.of (EuclideanSpace ℝ (Fin n))) (Metric.ball c R) Cᶜ
        Metric.isOpen_ball hAopen hcov₂ k
    refine IsZero.of_iso hball ?_
    exact asIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMap (TopCat.of (EuclideanSpace ℝ (Fin n))) U Cᶜ) k) ≪≫
      (asIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMap (TopCat.of (EuclideanSpace ℝ (Fin n)))
          (Metric.ball c R) Cᶜ) k)).symm


/-! ## The main statement -/

/-- Hatcher, *Algebraic Topology*, Lemma 3.27(b): for `M` an `n`-manifold (`n ≥ 1`), a chart `e`
and a compact convex `C` contained in the chart target `e.target`, the relative homology
`H_k(M, M∖A; ℤ)` with `A = e.source ∩ e⁻¹' C` vanishes for `k > n`. -/
theorem isZero_hatH_convex {n k : ℕ} (hn : 1 ≤ n) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCvx : Convex ℝ C) (hCcpt : IsCompact C)
    (hCsub : C ⊆ e.target) (hk : n < k) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains (TopCat.of M) ((e.source ∩ e ⁻¹' C)ᶜ)).homology k) := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · have hset : (e.source ∩ e ⁻¹' (∅ : Set (EuclideanSpace ℝ (Fin n))))ᶜ = (Set.univ : Set M) := by
      ext x; simp
    rw [hset]
    exact isZero_relChains_univ_homology (TopCat.of M) k
  · obtain ⟨c, hc⟩ := hCne
    set Ac : Set M := (e.source ∩ e ⁻¹' C)ᶜ with hAc
    have hA0cpt : IsCompact (e.source ∩ e ⁻¹' C) := isCompact_inter_preimage e hCcpt hCsub
    have hAcOpen : IsOpen Ac := hA0cpt.isClosed.isOpen_compl
    have hcovM : e.source ∪ Ac = Set.univ := by
      rw [hAc]
      ext x
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
      by_cases hx : x ∈ e.source
      · exact Or.inl hx
      · exact Or.inr (fun h => hx h.1)
    haveI hiso₁ : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMap (TopCat.of M) e.source Ac) k) :=
      Work.Cohomology.excision_relChainsMap_isIso (TopCat.of M) e.source Ac
        e.open_source hAcOpen hcovM k
    set A2 : Set ↥e.source := {y | (y : M) ∈ Ac} with hA2
    set B2 : Set ↥e.target := {ζ | (ζ : EuclideanSpace ℝ (Fin n)) ∈ Cᶜ} with hB2
    set φ : ↥e.source ≃ₜ ↥e.target := e.toHomeomorphSourceTarget with hφ
    have hφcoe : ∀ z : ↥e.source, ((φ z : ↥e.target) : EuclideanSpace ℝ (Fin n)) = e (z : M) :=
      fun z => rfl
    have himage : φ '' A2 = B2 := by
      ext ζ
      constructor
      · rintro ⟨z, hz, rfl⟩
        intro hcon
        exact hz ⟨z.2, hcon⟩
      · intro hζ
        refine ⟨φ.symm ζ, ?_, φ.apply_symm_apply ζ⟩
        intro hcon
        have h1 : (ζ : EuclideanSpace ℝ (Fin n)) = e (((φ.symm ζ : ↥e.source) : M)) := by
          rw [← hφcoe (φ.symm ζ), φ.apply_symm_apply]
        exact hζ (h1.symm ▸ hcon.2)
    let ψ : ↥A2 ≃ₜ ↥B2 := (Homeomorph.image φ A2).trans (Homeomorph.setCongr himage)
    have hψcoe : ∀ z : ↥A2, ((ψ z : ↥B2) : EuclideanSpace ℝ (Fin n)) =
        ((φ (z : ↥e.source) : ↥e.target) : EuclideanSpace ℝ (Fin n)) := fun z => rfl
    set f : TopCat.of ↥e.source ⟶ TopCat.of ↥e.target := TopCat.ofHom φ.toHomotopyEquiv.toFun with hf
    set g : TopCat.of ↥A2 ⟶ TopCat.of ↥B2 := TopCat.ofHom ψ.toHomotopyEquiv.toFun with hg
    have hw : Work.Cohomology.subtypeIncl (TopCat.of ↥e.source) A2 ≫ f =
        g ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥e.target) B2 := by
      have h : ∀ z : ↥A2, (Work.Cohomology.subtypeIncl (TopCat.of ↥e.source) A2 ≫ f) z =
          (g ≫ Work.Cohomology.subtypeIncl (TopCat.of ↥e.target) B2) z := by
        intro z
        exact Subtype.ext (hψcoe z).symm
      exact TopCat.hom_ext (ContinuousMap.ext h)
    have hfq : ∀ j, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥e.source) (TopCat.of ↥e.target) f) j) :=
      fun j => Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
        (X := TopCat.of ↥e.source) (Y := TopCat.of ↥e.target) φ.toHomotopyEquiv j
    have hgq : ∀ j, IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥A2) (TopCat.of ↥B2) g) j) :=
      fun j => Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
        (X := TopCat.of ↥A2) (Y := TopCat.of ↥B2) ψ.toHomotopyEquiv j
    haveI hiso₂ : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf (TopCat.of ↥e.source) (TopCat.of ↥e.target)
          A2 B2 f g hw) k) :=
      Work.Cohomology.relChainsMapOf_homologyMap_isIso (X := TopCat.of ↥e.source)
        (Y := TopCat.of ↥e.target) (A := A2) (B := B2) (f := f) (g := g) (w := hw) (n := k)
        hfq hgq
    have hflat := isZero_relChains_open_compl_convex hn e.open_target hCvx hCcpt hCsub hk
    refine IsZero.of_iso hflat ?_
    exact (asIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMap (TopCat.of M) e.source Ac) k)).symm ≪≫
      asIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf (TopCat.of ↥e.source) (TopCat.of ↥e.target)
          A2 B2 f g hw) k)

end

end Work.Compact.Noncompact
