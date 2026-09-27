import Mathlib
import Submission.Work.Compact.Noncompact.Basic
import Submission.Work.Compact.Noncompact.exists_homotopyEquiv_compl_closedBall

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.Compact.Noncompact

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

noncomputable section

lemma relMap_congr {X : TopCat} {A B : Set X} (h₁ h₂ : A ⊆ B) : relMap h₁ = relMap h₂ := by
  refine (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).1 ?_
  simp only [cokernel_π_relMap]

lemma relMapHom_congr {X : TopCat} {A B : Set X} (h₁ h₂ : A ⊆ B) (n : ℕ) :
    relMapHom h₁ n = relMapHom h₂ n :=
  congrArg (fun m => HomologicalComplex.homologyMap m n) (relMap_congr h₁ h₂)

lemma chainMap_id (X : TopCat) : Work.Cohomology.chainMap ℤ X X (𝟙 X) = 𝟙 _ := by
  show ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map (𝟙 X) = _
  exact CategoryTheory.Functor.map_id _ _

lemma relMap_eq_relChainsMapOf {X : TopCat} {A B : Set X} (h : A ⊆ B)
    (w : Work.Cohomology.subtypeIncl X A ≫ 𝟙 X = inclSet h ≫ Work.Cohomology.subtypeIncl X B) :
    relMap h = Work.Cohomology.relChainsMapOf X X A B (𝟙 X) (inclSet (X := X) h) w := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).1
  rw [cokernel_π_relMap h]
  unfold Work.Cohomology.relChainsMapOf
  rw [Work.Cohomology.cokernel_π_map, chainMap_id, Category.id_comp]

/-- `K = e.source ∩ e⁻¹' (closedBall c (ρ/2))`: the map `H_n(M, M∖K) → H_n(M, M∖{z})` is
injective for `z` in the chart source with `dist (e z) c < ρ/4`. -/
theorem localMap_injective_ball {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {c : EuclideanSpace ℝ (Fin n)} {ρ : ℝ} (hρ : 0 < ρ) (hsub : Metric.ball c ρ ⊆ e.target)
    {z : M} (hz : z ∈ e.source) (hzd : dist (e z) c < ρ / 4)
    (h : (e.source ∩ e ⁻¹' Metric.closedBall c (ρ / 2))ᶜ ⊆ ({z}ᶜ : Set M)) :
    Function.Injective (relMapHom (X := TopCat.of M)
      (A := (e.source ∩ e ⁻¹' Metric.closedBall c (ρ / 2))ᶜ) (B := ({z}ᶜ : Set M)) h n) := by
  obtain ⟨Φ, hΦ⟩ := exists_homotopyEquiv_compl_closedBall e hρ hsub hz hzd
  have hg_eq : inclSet (X := TopCat.of M) h = TopCat.ofHom Φ.toFun := by
    apply TopCat.ext
    intro w
    rw [TopCat.ofHom_apply]
    exact Subtype.ext (hΦ w).symm
  have hf : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of M) (𝟙 (TopCat.of M))) k) := by
    intro k
    rw [chainMap_id, HomologicalComplex.homologyMap_id]
    infer_instance
  have hgn : ∀ k, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of ↥((e.source ∩ e ⁻¹' Metric.closedBall c (ρ / 2))ᶜ))
        (TopCat.of ↥(({z}ᶜ : Set M))) (inclSet (X := TopCat.of M) h)) k) := by
    intro k
    rw [hg_eq]
    exact Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
      (X := TopCat.of ↥((e.source ∩ e ⁻¹' Metric.closedBall c (ρ / 2))ᶜ))
      (Y := TopCat.of ↥(({z}ᶜ : Set M))) Φ k
  have hw : Work.Cohomology.subtypeIncl (TopCat.of M)
        ((e.source ∩ e ⁻¹' Metric.closedBall c (ρ / 2))ᶜ)
      ≫ 𝟙 (TopCat.of M)
      = inclSet (X := TopCat.of M) h ≫ Work.Cohomology.subtypeIncl (TopCat.of M) (({z}ᶜ : Set M)) := by
    ext w; rfl
  have hiso : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of M)
        ((e.source ∩ e ⁻¹' Metric.closedBall c (ρ / 2))ᶜ) (({z}ᶜ : Set M))
        (𝟙 (TopCat.of M)) (inclSet (X := TopCat.of M) h) hw) n) :=
    Work.Cohomology.relChainsMapOf_homologyMap_isIso (X := TopCat.of M) (Y := TopCat.of M)
      ((e.source ∩ e ⁻¹' Metric.closedBall c (ρ / 2))ᶜ) (({z}ᶜ : Set M))
      (𝟙 (TopCat.of M)) (inclSet (X := TopCat.of M) h) hw n hf hgn
  have hrelmap := relMap_eq_relChainsMapOf h hw
  have : IsIso (relMapHom (X := TopCat.of M)
      (A := (e.source ∩ e ⁻¹' Metric.closedBall c (ρ / 2))ᶜ) (B := ({z}ᶜ : Set M)) h n) := by
    rw [relMapHom, hrelmap]
    exact hiso
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective
    (relMapHom (X := TopCat.of M)
      (A := (e.source ∩ e ⁻¹' Metric.closedBall c (ρ / 2))ᶜ) (B := ({z}ᶜ : Set M)) h n)).mp this |>.1

/-- The localization map at a point `y` factors through the relative homology of the complement of
any set `K` containing `y`. -/
lemma localMap_eq_relMapHom_relMapHom {n : ℕ} {M : Type} [TopologicalSpace M]
    (α : (Work.Cohomology.singularChains ℤ (TopCat.of M)).homology n)
    {K : Set M} (y : M) (hyK : y ∈ K) :
    localMap (X := TopCat.of M) n y α
      = relMapHom (X := TopCat.of M) (A := Kᶜ) (B := ({y}ᶜ : Set M))
          (by rintro z hz hzy; exact hz (hzy ▸ hyK)) n
        (relMapHom (X := TopCat.of M) (A := (∅ : Set M)) (B := Kᶜ)
          (Set.empty_subset _) n
          (HomologicalComplex.homologyMap
            (cokernel.π (Work.Cohomology.inclChains (TopCat.of M) (∅ : Set M))) n α)) := by
  have hKy : Kᶜ ⊆ ({y}ᶜ : Set M) := by
    rintro z hz hzy
    exact hz (hzy ▸ hyK)
  have hcomp := relMapHom_comp (X := TopCat.of M) (A := (∅ : Set M)) (B := Kᶜ)
    (C := ({y}ᶜ : Set M)) (Set.empty_subset _) hKy n
  have heq : relMapHom (X := TopCat.of M) (A := (∅ : Set M)) (B := ({y}ᶜ : Set M))
        (Set.empty_subset _) n
      = relMapHom (X := TopCat.of M) (A := (∅ : Set M)) (B := Kᶜ) (Set.empty_subset _) n
        ≫ relMapHom (X := TopCat.of M) (A := Kᶜ) (B := ({y}ᶜ : Set M)) hKy n := by
    rw [relMapHom_congr (X := TopCat.of M) (A := (∅ : Set M)) (B := ({y}ᶜ : Set M))
      (Set.empty_subset _) ((Set.empty_subset Kᶜ).trans hKy) n, ← hcomp]
  have h0 : localMap (X := TopCat.of M) n y α
      = relMapHom (X := TopCat.of M) (A := (∅ : Set M)) (B := ({y}ᶜ : Set M))
          (Set.empty_subset _) n
        (HomologicalComplex.homologyMap
          (cokernel.π (Work.Cohomology.inclChains (TopCat.of M) (∅ : Set M))) n α) := rfl
  rw [h0, heq, ModuleCat.comp_apply]

/-- The vanishing locus `{x | localMap x α = 0}` is clopen, so over a connected `M` it is all of
`M` as soon as it is nonempty. -/
theorem forall_localMap_eq_zero_of_exists {n : ℕ} (hn : 1 ≤ n) {M : Type} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    (α : (Work.Cohomology.singularChains ℤ (TopCat.of M)).homology n)
    (h : ∃ x : M, localMap (X := TopCat.of M) n x α = 0) :
    ∀ x : M, localMap (X := TopCat.of M) n x α = 0 := by
  have key : ∀ x : M, ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, (localMap (X := TopCat.of M) n y α = 0
        ↔ localMap (X := TopCat.of M) n x α = 0) := by
    intro x
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
      chartAt (EuclideanSpace ℝ (Fin n)) x
    have hxsrc : x ∈ e.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) x
    obtain ⟨ρ, hρ, hρsub⟩ : ∃ ρ > 0, Metric.ball (e x) ρ ⊆ e.target :=
      Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hxsrc)
    refine ⟨e.source ∩ e ⁻¹' Metric.ball (e x) (ρ/4), ?_, ⟨hxsrc, ?_⟩, ?_⟩
    · exact e.isOpen_inter_preimage Metric.isOpen_ball
    · rw [Set.mem_preimage]
      exact Metric.mem_ball_self (by linarith)
    · intro y hy
      let C : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall (e x) (ρ/2)
      let K : Set M := e.source ∩ e ⁻¹' C
      have hzK : ∀ z, z ∈ e.source → dist (e z) (e x) < ρ/4 → z ∈ K := fun z hz hzd =>
        ⟨hz, by rw [Set.mem_preimage, Metric.mem_closedBall]; linarith⟩
      have hxK : x ∈ K := hzK x hxsrc (by rw [dist_self]; linarith)
      have hxd : dist (e x) (e x) < ρ/4 := by rw [dist_self]; linarith
      have hWsubK : e.source ∩ e ⁻¹' Metric.ball (e x) (ρ/4) ⊆ K := by
        intro z hz
        obtain ⟨hz1, hz2⟩ := hz
        rw [Set.mem_preimage] at hz2
        exact hzK z hz1 (by rw [Metric.mem_ball] at hz2; linarith)
      have hsubK : ∀ z (hz : z ∈ K), Kᶜ ⊆ ({z}ᶜ : Set M) := fun z hz => by
        rintro w hw hwz
        exact hw (hwz ▸ hz)
      have hKi : ∀ z (hz : z ∈ e.source) (hzd : dist (e z) (e x) < ρ/4),
          Function.Injective (relMapHom (X := TopCat.of M) (A := Kᶜ) (B := ({z}ᶜ : Set M))
            (hsubK z (hzK z hz hzd)) n) := by
        intro z hz hzd
        exact localMap_injective_ball e hρ hρsub hz hzd (hsubK z (hzK z hz hzd))
      let β : (RC (TopCat.of M) Kᶜ).homology n :=
        relMapHom (X := TopCat.of M) (A := (∅ : Set M)) (B := Kᶜ) (Set.empty_subset _) n
          (HomologicalComplex.homologyMap
            (cokernel.π (Work.Cohomology.inclChains (TopCat.of M) (∅ : Set M))) n α)
      have hfac : ∀ z (hz : z ∈ K), localMap (X := TopCat.of M) n z α
          = relMapHom (X := TopCat.of M) (A := Kᶜ) (B := ({z}ᶜ : Set M))
              (hsubK z hz) n β := by
        intro z hz
        exact localMap_eq_relMapHom_relMapHom α z hz
      have hβ : ∀ z (hz : z ∈ K) (hzd : dist (e z) (e x) < ρ/4),
          (localMap (X := TopCat.of M) n z α = 0 ↔ β = 0) := by
        intro z hz hzd
        constructor
        · intro hz0
          have h2 : relMapHom (X := TopCat.of M) (A := Kᶜ) (B := ({z}ᶜ : Set M))
                (hsubK z hz) n β
              = relMapHom (X := TopCat.of M) (A := Kᶜ) (B := ({z}ᶜ : Set M))
                (hsubK z hz) n 0 := by
            rw [← hfac z hz, map_zero]
            exact hz0
          exact hKi z hz.1 hzd h2
        · intro hβ0
          rw [hfac z hz, hβ0, map_zero]
      have hyd : dist (e y) (e x) < ρ/4 := by
        have h2 := hy.2
        rw [Set.mem_preimage, Metric.mem_ball] at h2
        exact h2
      exact (hβ y (hWsubK hy) hyd).trans (hβ x hxK hxd).symm
  have hopen : IsOpen {x : M | localMap (X := TopCat.of M) n x α = 0} := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨W, hWopen, hxW, hW⟩ := key x
    exact ⟨W, fun y hy => (hW y hy).mpr hx, hWopen, hxW⟩
  have hclosed : IsClosed {x : M | localMap (X := TopCat.of M) n x α = 0} := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨W, hWopen, hxW, hW⟩ := key x
    refine ⟨W, ?_, hWopen, hxW⟩
    intro y hy hy0
    exact hx ((hW y hy).mp hy0)
  have huniv : {x : M | localMap (X := TopCat.of M) n x α = 0} = Set.univ := by
    rcases (isClopen_iff.mp
      (⟨hclosed, hopen⟩ : IsClopen {x : M | localMap (X := TopCat.of M) n x α = 0}))
      with hh | hh
    · obtain ⟨x₀, hx₀⟩ := h
      exact absurd hh (Set.Nonempty.ne_empty ⟨x₀, hx₀⟩)
    · exact hh
  intro x
  have : x ∈ ({x : M | localMap (X := TopCat.of M) n x α = 0} : Set M) := by
    rw [huniv]
    exact Set.mem_univ x
  exact this

end

end Work.Compact.Noncompact
