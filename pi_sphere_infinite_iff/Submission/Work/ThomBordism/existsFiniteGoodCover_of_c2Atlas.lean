import Mathlib
import Submission.Work.ThomBordism.goodCover_of_chartStarConvex
import Submission.Work.ThomBordism.exists_starRefinement
import Submission.Work.ThomBordism.exists_convex_image_ball

set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Set Metric

/-- For a finite family of maps each `C²` at `p` with injective derivative at `p`, there is a
common radius `ε₀` such that for every `ε ≤ ε₀` the image of `ball p ε` under each map is convex. -/
theorem shift_family_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (f : ι → E → E) (p : E)
    (hf : ∀ i, ContDiffAt ℝ 2 (f i) p) (hinj : ∀ i, Function.Injective (fderiv ℝ (f i) p)) :
    ∃ ε₀, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ i, Convex ℝ (f i '' Metric.ball p ε) := by
  have hτdiff : ∀ i, ContDiffAt ℝ 2 (fun w : E => f i (p + w) - f i p) 0 := by
    intro i
    apply ContDiffAt.sub
    · have h2 : ContDiffWithinAt ℝ 2 (fun w : E => p + w) univ 0 := by
        rw [contDiffWithinAt_univ]; fun_prop
      have h1 := (hf i).comp_contDiffWithinAt_of_eq (s := univ) 0 h2 (by simp)
      rwa [contDiffWithinAt_univ] at h1
    · exact contDiffAt_const
  have hτ0 : ∀ i, (fun w : E => f i (p + w) - f i p) 0 = 0 := by intro i; simp
  have hshift : fderiv ℝ (fun w : E => p + w) 0 = ContinuousLinearMap.id ℝ E := by
    rw [show (fun w : E => p + w) = (fun w => p + id w) from rfl, fderiv_const_add, fderiv_id]
  have hτinj : ∀ i, Function.Injective (fderiv ℝ (fun w : E => f i (p + w) - f i p) 0) := by
    intro i
    have heq : fderiv ℝ (fun w : E => f i (p + w) - f i p) 0 = fderiv ℝ (f i) p := by
      rw [fderiv_sub_const]
      rw [show (fun w : E => f i (p + w)) = (f i) ∘ (fun w : E => p + w) from rfl, fderiv_comp]
      · rw [hshift]; simp
      · simpa using (hf i).differentiableAt
      · fun_prop
    rw [heq]; exact hinj i
  choose e hepos hemono using fun i =>
    Work.ThomBordism.convex_image_ball_of_contDiffAt (fun w : E => f i (p + w) - f i p)
      (hτdiff i) (hτ0 i) (hτinj i)
  by_cases hne : Nonempty ι
  · refine ⟨(Finset.univ : Finset ι).inf' Finset.univ_nonempty e, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]; exact fun i _ => hepos i
    · intro ε hε hεle i
      have hc : Convex ℝ ((fun w : E => f i (p + w) - f i p) '' Metric.ball 0 ε) :=
        hemono i ε hε (le_trans hεle (Finset.inf'_le e (Finset.mem_univ i)))
      have himg : (fun x : E => f i p + x) '' ((fun w : E => f i (p + w) - f i p) '' Metric.ball 0 ε)
          = f i '' Metric.ball p ε := by
        ext y
        simp only [Set.mem_image, Metric.mem_ball]
        constructor
        · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
          exact ⟨p + w, by simpa [dist_eq_norm, sub_eq_add_neg, add_assoc] using hw, by abel⟩
        · rintro ⟨z, hz, rfl⟩
          exact ⟨f i (p + (z - p)) - f i p, ⟨z - p, by simpa [dist_eq_norm] using hz, rfl⟩,
            by simp [sub_eq_add_neg]⟩
      rw [← himg]
      exact hc.translate (f i p)
  · exact ⟨1, one_pos, fun ε hε hεle i => absurd ⟨i⟩ hne⟩

/-- Local existence of a "good radius": at a point `p` of an open set `V` inside the chart of
`ψ β` and inside the charts of all `α ∈ A`, there is `ε > 0` with `ball p ε ⊆ V` and such that
the image of `ball p ε` under every transition `ψ α ∘ (ψ β)⁻¹` is convex. -/
theorem exists_local_good_radius
    {X : Type*} [TopologicalSpace X]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {m : ℕ} (ψ : Fin m → OpenPartialHomeomorph X E)
    (hC2 : ∀ i j, ContDiffOn ℝ 2 (fun u : E => ψ j ((ψ i).symm u))
      (ψ i '' ((ψ i).source ∩ (ψ j).source)))
    (hinj : ∀ i j, ∀ u ∈ ψ i '' ((ψ i).source ∩ (ψ j).source),
      Function.Injective (fderiv ℝ (fun v : E => ψ j ((ψ i).symm v)) u))
    (β : Fin m) (A : Finset (Fin m)) (V : Set E) (hVopen : IsOpen V) (p : E) (hp : p ∈ V)
    (hsub : ∀ α ∈ A, V ⊆ ψ β '' ((ψ β).source ∩ (ψ α).source)) :
    ∃ ε, 0 < ε ∧ ball p ε ⊆ V ∧
      ∀ α ∈ A, Convex ℝ ((fun u : E => ψ α ((ψ β).symm u)) '' ball p ε) := by
  have hfdiff : ∀ α : ↥A, ContDiffAt ℝ 2 (fun u : E => ψ (α:Fin m) ((ψ β).symm u)) p := by
    intro α
    have hpα : p ∈ ψ β '' ((ψ β).source ∩ (ψ (α:Fin m)).source) := hsub (α:Fin m) α.2 hp
    have hDopen : IsOpen (ψ β '' ((ψ β).source ∩ (ψ (α:Fin m)).source)) :=
      (ψ β).isOpen_image_source_inter (ψ (α:Fin m)).open_source
    exact (hC2 β (α:Fin m)).contDiffAt (hDopen.mem_nhds hpα)
  have hfinj : ∀ α : ↥A,
      Function.Injective (fderiv ℝ (fun u : E => ψ (α:Fin m) ((ψ β).symm u)) p) := by
    intro α
    exact hinj β (α:Fin m) p (hsub (α:Fin m) α.2 hp)
  obtain ⟨ε₀, hε₀pos, hε₀⟩ :=
    shift_family_convex (fun (α : ↥A) => fun u : E => ψ (α:Fin m) ((ψ β).symm u)) p hfdiff hfinj
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.isOpen_iff.mp hVopen p hp
  refine ⟨min ε₀ ε₁, lt_min hε₀pos hε₁pos, ?_, ?_⟩
  · intro y hy
    exact hε₁ (Metric.ball_subset_ball (min_le_right _ _) hy)
  · intro α hα
    exact hε₀ (min ε₀ ε₁) (lt_min hε₀pos hε₁pos) (min_le_left _ _) ⟨α, hα⟩

set_option maxHeartbeats 4000000 in
/-- **A finite `C²` atlas implies a finite good cover.** -/
theorem existsFiniteGoodCover_of_c2Atlas
    {n : ℕ} (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {m : ℕ} (ψ : Fin m → OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (hcov : (⋃ i, (ψ i).source) = Set.univ)
    (x : Fin m → X) (hx : ∀ i, x i ∈ (ψ i).source ∧ ψ i (x i) = 0)
    (hC2 : ∀ i j, ContDiffOn ℝ 2 (fun u : EuclideanSpace ℝ (Fin n) => ψ j ((ψ i).symm u))
      (ψ i '' ((ψ i).source ∩ (ψ j).source)))
    (hinj : ∀ i j, ∀ u ∈ ψ i '' ((ψ i).source ∩ (ψ j).source),
      Function.Injective (fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => ψ j ((ψ i).symm v)) u)) :
    ∃ (m' : ℕ) (U : Fin m' → Set X), (∀ i, IsOpen (U i)) ∧ (⋃ i, U i) = Set.univ ∧
      (∀ S : Finset (Fin m'), S.Nonempty → (⋂ i ∈ S, U i).Nonempty →
        ContractibleSpace ↥(⋂ i ∈ S, U i)) := by
  classical
  obtain ⟨κ, hκfin, W, r, hWopen, hWcov, hWsub, hWstar⟩ :=
    Work.ThomBordism.exists_starRefinement (fun i : Fin m => (ψ i).source)
      (fun i => (ψ i).open_source) hcov
  letI : Fintype κ := hκfin
  let A : κ → Finset (Fin m) := fun j => Finset.univ.filter (fun α => W j ⊆ (ψ α).source)
  have good_exists : ∀ (j : κ) (p : EuclideanSpace ℝ (Fin n)),
      p ∈ ψ (r j) '' W j →
      ∃ ε, 0 < ε ∧ ball p ε ⊆ ψ (r j) '' W j ∧
        ∀ α ∈ A j, Convex ℝ ((fun u => ψ α ((ψ (r j)).symm u)) '' ball p ε) := by
    intro j p hp
    refine exists_local_good_radius ψ hC2 hinj (r j) (A j) (ψ (r j) '' W j) ?_ p hp ?_
    · exact (ψ (r j)).isOpen_image_of_subset_source (hWopen j) (hWsub j)
    · intro α hα
      apply Set.image_mono
      intro c hc
      exact ⟨hWsub j hc, (Finset.mem_filter.mp hα).2 hc⟩
  let εg : κ → EuclideanSpace ℝ (Fin n) → ℝ := fun j p =>
    if h : p ∈ ψ (r j) '' W j then Classical.choose (good_exists j p h) else 1
  have hεg : ∀ (j : κ) (p : EuclideanSpace ℝ (Fin n)) (hp : p ∈ ψ (r j) '' W j),
      0 < εg j p ∧ ball p (εg j p) ⊆ ψ (r j) '' W j ∧
        ∀ α ∈ A j, Convex ℝ ((fun u => ψ α ((ψ (r j)).symm u)) '' ball p (εg j p)) := by
    intro j p hp
    have heq : εg j p = Classical.choose (good_exists j p hp) := by
      simp only [εg]; rw [dif_pos hp]
    rw [heq]
    exact Classical.choose_spec (good_exists j p hp)
  let good : κ × EuclideanSpace ℝ (Fin n) → Prop := fun jp => jp.2 ∈ ψ (r jp.1) '' W jp.1
  let U : κ × EuclideanSpace ℝ (Fin n) → Set X := fun jp =>
    if good jp then (ψ (r jp.1)).symm '' ball jp.2 (εg jp.1 jp.2) else ∅
  have hUdef : ∀ jp, U jp = if good jp then (ψ (r jp.1)).symm '' ball jp.2 (εg jp.1 jp.2) else ∅ :=
    fun jp => rfl
  have hUopen : ∀ jp, IsOpen (U jp) := by
    intro jp
    by_cases hg : good jp
    · rw [hUdef jp, if_pos hg]
      refine (ψ (r jp.1)).isOpen_image_symm_of_subset_target (Metric.isOpen_ball) ?_
      intro y hy
      have hb : y ∈ ψ (r jp.1) '' W jp.1 := (hεg jp.1 jp.2 hg).2.1 hy
      rw [← (ψ (r jp.1)).image_source_eq_target]
      exact Set.image_mono (hWsub jp.1) hb
    · rw [hUdef jp, if_neg hg]; exact isOpen_empty
  have hUcov : (⋃ jp, U jp) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro z
    have hz : z ∈ ⋃ j, W j := by rw [hWcov]; exact Set.mem_univ z
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    have hp : ψ (r j) z ∈ ψ (r j) '' W j := ⟨z, hj, rfl⟩
    refine Set.mem_iUnion.mpr ⟨(j, ψ (r j) z), ?_⟩
    rw [hUdef, if_pos hp]
    exact ⟨ψ (r j) z, Metric.mem_ball_self (hεg j (ψ (r j) z) hp).1,
      (ψ (r j)).left_inv (hWsub j hj)⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hUopen (by rw [hUcov])
  let jp : Fin T.card → κ × EuclideanSpace ℝ (Fin n) :=
    fun k => (T.equivFin.symm k : κ × EuclideanSpace ℝ (Fin n))
  refine ⟨T.card, fun k => U (jp k), fun k => hUopen (jp k), ?_, ?_⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro z
    have hz : z ∈ ⋃ i ∈ T, U i := hT (Set.mem_univ z)
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨i, hi, hzi⟩ := hz
    refine Set.mem_iUnion.mpr ⟨T.equivFin ⟨i, hi⟩, ?_⟩
    have hed : jp (T.equivFin ⟨i, hi⟩) = i := by simp only [jp]; rw [Equiv.symm_apply_apply]
    rw [hed]; exact hzi
  · apply Work.ThomBordism.goodCover_of_chartStarConvex
      (E := EuclideanSpace ℝ (Fin n)) (fun k => U (jp k))
    intro S hS hne
    obtain ⟨i₀, hi₀⟩ := hS
    obtain ⟨z₀, hz₀⟩ := hne
    rw [Set.mem_iInter₂] at hz₀
    have hgood_of : ∀ i, i ∈ S → good (jp i) := by
      intro i hi
      by_contra hg
      have hUemp : U (jp i) = (∅ : Set X) := by
        rw [hUdef]
        exact if_neg hg
      have hz : z₀ ∈ U (jp i) := hz₀ i hi
      rw [hUemp] at hz
      exact hz
    have hsub_W : ∀ i, i ∈ S → U (jp i) ⊆ W (jp i).1 := by
      intro i hi
      have hgu := hgood_of i hi
      rw [hUdef, if_pos hgu]
      intro y hy
      obtain ⟨w, hw, rfl⟩ := hy
      have h1 : w ∈ ψ (r (jp i).1) '' W (jp i).1 := (hεg (jp i).1 (jp i).2 hgu).2.1 hw
      obtain ⟨c, hcW, hcw⟩ := h1
      rw [← hcw, (ψ (r (jp i).1)).left_inv (hWsub (jp i).1 hcW)]
      exact hcW
    have hzW : ∀ i, i ∈ S → z₀ ∈ W (jp i).1 := fun i hi => hsub_W i hi (hz₀ i hi)
    have hchart : ∀ i, i ∈ S → W (jp i).1 ⊆ (ψ (r (jp i₀).1)).source := by
      intro i hi
      exact hWstar (jp i₀).1 (jp i).1 ⟨z₀, hzW i hi, hzW i₀ hi₀⟩
    refine ⟨ψ (r (jp i₀).1), ψ (r (jp i₀).1) z₀, ?_, ?_⟩
    · intro i hi
      exact (hsub_W i hi).trans (hchart i hi)
    · intro i hi
      have hgu := hgood_of i hi
      have himg : (ψ (r (jp i₀).1)) '' U (jp i)
          = (fun u => ψ (r (jp i₀).1) ((ψ (r (jp i).1)).symm u)) ''
              ball (jp i).2 (εg (jp i).1 (jp i).2) := by
        rw [hUdef, if_pos hgu, Set.image_image]
      have hmemA : r (jp i₀).1 ∈ A (jp i).1 := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hchart i hi⟩
      have hconv : Convex ℝ ((fun u => ψ (r (jp i₀).1) ((ψ (r (jp i).1)).symm u)) ''
          ball (jp i).2 (εg (jp i).1 (jp i).2)) :=
        (hεg (jp i).1 (jp i).2 hgu).2.2 (r (jp i₀).1) hmemA
      rw [himg]
      exact hconv.starConvex (himg ▸ ⟨z₀, hz₀ i hi, rfl⟩)

end Work.ThomBordism
