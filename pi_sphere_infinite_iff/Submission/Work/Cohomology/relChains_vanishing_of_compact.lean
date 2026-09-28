import Mathlib
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.homology_vanishing_relative_compact

set_option synthInstance.maxHeartbeats 400000

/-!
# `H_i(M, M∖A) = 0` above the dimension, for `A` compact

For a topological space `M` charted by `ℝⁿ` (`n ≥ 1`), a compact subset `A ⊆ M` and `i > n`, the
relative singular homology `H_i(M, M∖A) = 0`.  This is Hatcher's Lemma 3.27 (b), the input to the
existence of fundamental classes; for `A = M` compact it says that a closed `n`-manifold has no
homology above degree `n`.

The proof assembles three ingredients.

* `isZero_relChains_union`: the Mayer–Vietoris step for the "excluded set" functor `A ↦ H_*(M, M∖A)`
  — the vanishing for `K`, `L` and `K ∩ L` in degrees `i` and `i+1` gives it for `K ∪ L` in degree
  `i`.  It is derived from the long exact sequence of the triple `Kᶜ ∩ Lᶜ ⊆ Kᶜ ⊆ M`
  (`relChainsPairModel`) and the two-cover excision lemma (`homologyTwoCover`).
* `isZero_relChains_of_subset_chartPiece`: the base case, a compact set inside an open piece of a
  chart.  This is `homology_vanishing_relative_compact` transported to the honest relative complex
  `relChains M Cᶜ` by `homologyTwoCover`.
* The chart pieces: for each point of `A` one picks a closed ball around it inside a chart, and
  `isZero_relChains_of_subset_pieces` inducts over any finite family of such chart pieces,
  splitting a compact set covered by the family into the part in the "old" pieces and the part in
  the new one.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable {M : TopCat}

/-- `H_i(M, M) = 0`: the relative chain complex of a space relative to itself is acyclic. -/
theorem isZero_relChains_univ (X : TopCat) (i : ℕ) :
    IsZero ((relChains X (Set.univ : Set X)).homology i) := by
  have hepi : Epi (inclChains X (Set.univ : Set X)) := by
    apply HomologicalComplex.epi_of_epi_f
    intro nn
    rw [ModuleCat.epi_iff_surjective]
    intro c
    have htop : LinearMap.range ((inclChains X (Set.univ : Set X)).f nn).hom = ⊤ := by
      refine mem_of_gen X nn _ ?_
      intro σ
      obtain ⟨σ', hσ'⟩ := exists_map_inclUX_of_range_subset (Set.univ : Set X)
        (Opposite.op (SimplexCategory.mk nn)) σ (Set.subset_univ _)
      refine ⟨gen (TopCat.of (Set.univ : Set X)) nn σ', ?_⟩
      have h := chainComplexMap_ι_apply (TopCat.toSSet.map (inclUX (Set.univ : Set X))) nn σ'
        (1 : ℤ)
      have h2 : (TopCat.toSSet.map (inclUX (Set.univ : Set X))).app (Opposite.op (SimplexCategory.mk nn)) σ' = σ :=
        hσ'
      rw [h2] at h
      exact h
    have hc : c ∈ LinearMap.range ((inclChains X (Set.univ : Set X)).f nn).hom := by
      rw [htop]; exact Submodule.mem_top
    exact LinearMap.mem_range.mp hc
  haveI hmono : Mono (inclChains X (Set.univ : Set X)) := mono_chainMap_subtypeIncl X _
  haveI : IsIso (inclChains X (Set.univ : Set X)) := isIso_of_mono_of_epi _
  have hq : QuasiIso (inclChains X (Set.univ : Set X)) := by
    rw [quasiIso_iff]
    intro j
    rw [quasiIsoAt_iff_isIso_homologyMap]
    infer_instance
  exact (HomologicalComplex.exactAt_iff_isZero_homology (relChains X (Set.univ : Set X)) i).mp
    ((hPairShort_shortExact X (Set.univ : Set X)).acyclic_X₃ hq i)

/-- **The Mayer–Vietoris (union) step for the excluded-set functor `A ↦ H_*(M, M∖A)`.**  If the
relative homology of `K`, `L` and `K ∩ L` vanishes in the degrees `i` and `i+1`, then that of
`K ∪ L` vanishes in degree `i`. -/
theorem isZero_relChains_union {K L : Set M} (hKc : IsClosed K) (hLc : IsClosed L) (i : ℕ)
    (hK0 : IsZero ((relChains M Kᶜ).homology i))
    (hK1 : IsZero ((relChains M Kᶜ).homology (i + 1)))
    (hL0 : IsZero ((relChains M Lᶜ).homology i))
    (hKL0 : IsZero ((relChains M (K ∩ L)ᶜ).homology i))
    (hKL1 : IsZero ((relChains M (K ∩ L)ᶜ).homology (i + 1))) :
    IsZero ((relChains M (K ∪ L)ᶜ).homology i) := by
  -- Step 1: `H_i(M, M∖(K∪L)) ≅ H_i` of the subspace model of the pair `(Kᶜ, (K∪L)ᶜ)`
  have hST : (K ∪ L)ᶜ ⊆ Kᶜ := Set.compl_subset_compl.mpr Set.subset_union_left
  have eV : Nonempty (((relChains M (K ∪ L)ᶜ).homology i) ≅
      ((relChains (TopCat.of ↥(Kᶜ)) {y : ↥(Kᶜ) | (y : M) ∈ (K ∪ L)ᶜ}).homology i)) := by
    obtain ⟨e1⟩ := homology_iso_of_triple (M := M) hST i hK0 hK1
    obtain ⟨e2⟩ := coker_inclChainsSub_homology_iso (M := M) hST i
    exact ⟨e1 ≪≫ e2⟩
  -- Step 2: the two-cover (excision) bridge
  have hU : IsOpen {y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Kᶜ} :=
    hKc.isOpen_compl.preimage continuous_subtype_val
  have hV : IsOpen {y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Lᶜ} :=
    hLc.isOpen_compl.preimage continuous_subtype_val
  have hcov : {y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Kᶜ} ∪ {y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Lᶜ}
      = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      by_cases hy : (y : M) ∈ K
      · right
        by_contra h
        exact y.2 ⟨hy, by simpa only [Set.mem_setOf_eq, Set.mem_compl_iff, not_not] using h⟩
      · left; exact hy
  obtain ⟨e2c⟩ := homologyTwoCover (TopCat.of ↥((K ∩ L)ᶜ))
    {y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Kᶜ} {y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Lᶜ} hU hV hcov i
  -- the homeomorphism between the two models of the pair `(Kᶜ, (K∪L)ᶜ)`
  let hE : ↥(Kᶜ : Set M) ≃ₜ ↥{y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Kᶜ} :=
    { toFun := fun v => ⟨⟨(v : M), fun hv => v.2 hv.1⟩, v.2⟩
      invFun := fun u => ⟨(u.1 : M), u.2⟩
      left_inv := fun v => by ext <;> rfl
      right_inv := fun u => by ext <;> rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hE' : ∀ v : ↥(Kᶜ : Set M),
      (v ∈ {y : ↥(Kᶜ) | (y : M) ∈ (K ∪ L)ᶜ} ↔
        hE v ∈ {u : ↥{y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Kᶜ} |
          (u : ↥((K ∩ L)ᶜ)) ∈ {y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Lᶜ}}) := by
    intro v
    have hEc : ((hE v : ↥((K ∩ L)ᶜ)) : M) = (v : M) := rfl
    show ¬ ((v : M) ∈ K ∪ L) ↔ ¬ (((hE v : ↥((K ∩ L)ᶜ)) : M) ∈ L)
    constructor
    · intro hv hL
      exact hv (Or.inr (hEc ▸ hL))
    · intro hv hcon
      rcases (Set.mem_union (v : M) K L).mp hcon with hK | hL
      · exact (hE v).2 (hEc ▸ hK)
      · exact hv (hEc ▸ hL)
  obtain ⟨eH⟩ := relChains_homeomorph (↥(Kᶜ : Set M))
    (↥{y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Kᶜ})
    {y : ↥(Kᶜ) | (y : M) ∈ (K ∪ L)ᶜ}
    {u : ↥{y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Kᶜ} |
        (u : ↥((K ∩ L)ᶜ)) ∈ {y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Lᶜ}}
    hE hE' i
  -- Step 3: the vanishing of the pair `((K∩L)ᶜ, Lᶜ)` via the triple sequence
  have hSP : Lᶜ ⊆ (K ∩ L)ᶜ := Set.compl_subset_compl.mpr Set.inter_subset_right
  have e3 : Nonempty (((relChains (TopCat.of ↥((K ∩ L)ᶜ))
        {y : ↥((K ∩ L)ᶜ) | (y : M) ∈ Lᶜ}).homology i) ≅ ((relChains M Lᶜ).homology i)) := by
    obtain ⟨f1⟩ := homology_iso_of_triple (M := M) hSP i hKL0 hKL1
    obtain ⟨f2⟩ := coker_inclChainsSub_homology_iso (M := M) hSP i
    exact ⟨(f1 ≪≫ f2).symm⟩
  obtain ⟨eV'⟩ := eV
  obtain ⟨e3'⟩ := e3
  exact IsZero.of_iso hL0 (eV' ≪≫ eH ≪≫ e2c.symm ≪≫ e3')

/-- **The base case**: a compact set inside an open piece of a chart has vanishing relative
homology above the dimension. -/
theorem isZero_relChains_of_subset_chartPiece {n : ℕ} (hn : 1 ≤ n) {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (c : M)
    (Q : Set (EuclideanSpace ℝ (Fin n))) (hQ : IsOpen Q)
    (hQt : Q ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) c).target) :
    ∀ (C : Set M), C ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) c) ⁻¹' Q
        ∩ (chartAt (EuclideanSpace ℝ (Fin n)) c).source → IsCompact C → ∀ i, n < i →
      IsZero ((relChains M Cᶜ).homology i) := by
  intro C hCW hCc i hi
  set W : Set M := (chartAt (EuclideanSpace ℝ (Fin n)) c) ⁻¹' Q
    ∩ (chartAt (EuclideanSpace ℝ (Fin n)) c).source with hWdef
  have hsub := homology_vanishing_relative_compact hn (M := M) c Q hQ hQt C hCW hCc i hi
  have hWopen : IsOpen W := by
    have h := (chartAt (EuclideanSpace ℝ (Fin n)) c).isOpen_inter_preimage hQ
    rwa [Set.inter_comm] at h
  have hcov : W ∪ Cᶜ = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      by_cases hy : y ∈ C
      · left; exact hCW hy
      · right; exact hy
  obtain ⟨e⟩ := homologyTwoCover M W Cᶜ hWopen hCc.isClosed.isOpen_compl hcov i
  exact IsZero.of_iso (ModuleCat.isZero_iff_subsingleton.mpr hsub) e

/-- **The induction over a finite family of chart pieces**: a compact set covered by finitely many
closed sets, each contained in an open piece of a chart, has vanishing relative homology above the
dimension. -/
theorem isZero_relChains_of_subset_pieces {n : ℕ} (hn : 1 ≤ n) {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (ι : Type) [DecidableEq ι] :
    ∀ (t : Finset ι) (K : ι → Set M),
      (∀ a, IsClosed (K a)) →
      (∀ a, ∃ (c : M) (Q : Set (EuclideanSpace ℝ (Fin n))), IsOpen Q ∧
        Q ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) c).target ∧
        K a ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) c) ⁻¹' Q ∩ (chartAt (EuclideanSpace ℝ (Fin n)) c).source) →
      ∀ (C : Set M), IsCompact C → C ⊆ ⋃ a ∈ t, K a → ∀ i, n < i →
        IsZero ((relChains M Cᶜ).homology i) := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty =>
      intro K _ _ C hCc hcov i hi
      have hC : C = (∅ : Set M) := by
        refine Set.subset_empty_iff.mp ?_
        intro x hx
        simpa using hcov hx
      rw [hC, Set.compl_empty]
      exact isZero_relChains_univ M i
  | insert a s has ih =>
      intro K hKcl hKpiece C hCc hcov i hi
      have hKacl : IsClosed (K a) := hKcl a
      have hKscl : IsClosed (⋃ b ∈ s, K b) :=
        Set.Finite.isClosed_biUnion s.finite_toSet (fun b _ => hKcl b)
      -- the two pieces
      have hC1 : IsCompact (C ∩ ⋃ b ∈ s, K b) := hCc.inter_right hKscl
      have hC2 : IsCompact (C ∩ K a) := hCc.inter_right hKacl
      have hsub1 : C ∩ (⋃ b ∈ s, K b) ⊆ ⋃ b ∈ s, K b := Set.inter_subset_right
      have h1 : IsZero ((relChains M (C ∩ ⋃ b ∈ s, K b)ᶜ).homology i) :=
        ih K (fun b => hKcl b) (fun b => hKpiece b) (C ∩ (⋃ b ∈ s, K b)) hC1 hsub1 i hi
      have h1' : IsZero ((relChains M (C ∩ ⋃ b ∈ s, K b)ᶜ).homology (i + 1)) :=
        ih K (fun b => hKcl b) (fun b => hKpiece b) (C ∩ (⋃ b ∈ s, K b)) hC1 hsub1 (i + 1)
          (by omega)
      have h2 : IsZero ((relChains M (C ∩ K a)ᶜ).homology i) := by
        obtain ⟨c, Q, hQ, hQt, hKsub⟩ := hKpiece a
        exact isZero_relChains_of_subset_chartPiece hn c Q hQ hQt (C ∩ K a)
          (Set.inter_subset_right.trans hKsub) hC2 i hi
      have h3 : IsZero ((relChains M ((C ∩ ⋃ b ∈ s, K b) ∩ (C ∩ K a))ᶜ).homology i) := by
        obtain ⟨c, Q, hQ, hQt, hKsub⟩ := hKpiece a
        refine isZero_relChains_of_subset_chartPiece hn c Q hQ hQt
          ((C ∩ ⋃ b ∈ s, K b) ∩ (C ∩ K a)) ?_ ?_ i hi
        · exact fun x hx => hKsub hx.2.2
        · exact (hC1.inter hC2)
      have h3' : IsZero ((relChains M ((C ∩ ⋃ b ∈ s, K b) ∩ (C ∩ K a))ᶜ).homology (i + 1)) := by
        obtain ⟨c, Q, hQ, hQt, hKsub⟩ := hKpiece a
        refine isZero_relChains_of_subset_chartPiece hn c Q hQ hQt
          ((C ∩ ⋃ b ∈ s, K b) ∩ (C ∩ K a)) ?_ ?_ (i + 1) (by omega)
        · exact fun x hx => hKsub hx.2.2
        · exact (hC1.inter hC2)
      have hmain := isZero_relChains_union (K := C ∩ ⋃ b ∈ s, K b) (L := C ∩ K a)
        (hC1.isClosed) (hC2.isClosed) i h1 h1' h2 h3 h3'
      have hset : (C ∩ ⋃ b ∈ s, K b) ∪ (C ∩ K a) = C := by
        have h2 : (C ∩ ⋃ b ∈ s, K b) ∪ (C ∩ K a)
            = C ∩ ((⋃ b ∈ s, K b) ∪ K a) := by
          rw [← Set.inter_union_distrib_left C (⋃ b ∈ s, K b) (K a)]
        rw [h2, Set.union_comm (⋃ b ∈ s, K b) (K a), ← Finset.set_biUnion_insert a s K]
        exact Set.inter_eq_left.mpr hcov
      rwa [hset] at hmain

/-- **`H_i(M, M∖A) = 0` above the dimension, for `A` compact** (Hatcher, Lemma 3.27 (b)). -/
theorem relChains_vanishing_of_compact {n : ℕ} (hn : 1 ≤ n) {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (A : Set M) (hAc : IsCompact A) :
    ∀ i, n < i → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.relChains M Aᶜ).homology i) := by
  classical
  -- a positive radius with the closed ball around `a` inside the chart target
  have hchoice : ∀ a : M, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) ρ
        ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target := by
    intro a
    have ha : (chartAt (EuclideanSpace ℝ (Fin n)) a) a
        ∈ (chartAt (EuclideanSpace ℝ (Fin n)) a).target :=
      (chartAt (EuclideanSpace ℝ (Fin n)) a).map_source (mem_chart_source _ a)
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      ((chartAt (EuclideanSpace ℝ (Fin n)) a).open_target.mem_nhds ha)
    refine ⟨ε / 2, by linarith, fun y hy => hεsub ?_⟩
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hy
    rw [dist_comm] at this ⊢
    linarith
  choose ρ hρpos hρsub using hchoice
  -- the closed chart pieces
  let K : M → Set M := fun a =>
    (chartAt (EuclideanSpace ℝ (Fin n)) a) ⁻¹'
        Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (ρ a / 2)
      ∩ (chartAt (EuclideanSpace ℝ (Fin n)) a).source
  have hKcl : ∀ a, IsClosed (K a) := by
    intro a
    have hsub' : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (ρ a / 2)
        ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target := fun y hy =>
      hρsub a (Metric.closedBall_subset_closedBall (by linarith [hρpos a]) hy)
    have hcomp : IsCompact (K a) := by
      have heq : K a = (chartAt (EuclideanSpace ℝ (Fin n)) a).symm ''
          Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (ρ a / 2) := by
        rw [OpenPartialHomeomorph.symm_image_eq_source_inter_preimage _ hsub', Set.inter_comm]
      rw [heq]
      exact (isCompact_closedBall _ _).image_of_continuousOn
        ((chartAt (EuclideanSpace ℝ (Fin n)) a).continuousOn_symm.mono hsub')
    exact hcomp.isClosed
  have hKpiece : ∀ a, ∃ (c : M) (Q : Set (EuclideanSpace ℝ (Fin n))), IsOpen Q ∧
      Q ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) c).target ∧
      K a ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) c) ⁻¹' Q
        ∩ (chartAt (EuclideanSpace ℝ (Fin n)) c).source := by
    intro a
    refine ⟨a, Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) a) a) (ρ a), Metric.isOpen_ball,
      fun y hy => hρsub a (Metric.ball_subset_closedBall hy), ?_⟩
    intro x hx
    exact ⟨by
      rw [Set.mem_preimage]
      exact Metric.closedBall_subset_ball (by linarith [hρpos a]) hx.1, hx.2⟩
  -- the open cover by the pieces
  have hcov : A ⊆ ⋃ a : ↥A, interior (K (a : M)) := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    have hneigh : (chartAt (EuclideanSpace ℝ (Fin n)) x) ⁻¹'
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) (ρ x / 2)
          ∩ (chartAt (EuclideanSpace ℝ (Fin n)) x).source ⊆ K x := by
      intro y hy
      exact ⟨by
        rw [Set.mem_preimage]
        exact Metric.ball_subset_closedBall hy.1, hy.2⟩
    have hopen : IsOpen ((chartAt (EuclideanSpace ℝ (Fin n)) x) ⁻¹'
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) (ρ x / 2)
          ∩ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) := by
      have h := (chartAt (EuclideanSpace ℝ (Fin n)) x).isOpen_inter_preimage
        (s := Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) x) x) (ρ x / 2))
        Metric.isOpen_ball
      rwa [Set.inter_comm] at h
    refine interior_maximal hneigh hopen ?_
    exact ⟨by rw [Set.mem_preimage]; exact Metric.mem_ball_self (by linarith [hρpos x]),
      mem_chart_source _ x⟩
  obtain ⟨t, ht⟩ := hAc.elim_finite_subcover (fun a : ↥A => interior (K (a : M)))
    (fun a => isOpen_interior) hcov
  intro i hi
  refine isZero_relChains_of_subset_pieces hn ↥A t (fun a => K (a : M))
    (fun a => hKcl (a : M)) (fun a => hKpiece (a : M)) A hAc ?_ i hi
  intro x hx
  rcases Set.mem_iUnion₂.mp (ht hx) with ⟨a, ha, hxa⟩
  exact Set.mem_iUnion₂.mpr ⟨a, ha, interior_subset hxa⟩

end

end Work.Cohomology
