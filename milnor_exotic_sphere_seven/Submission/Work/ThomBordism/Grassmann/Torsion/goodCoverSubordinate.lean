import Mathlib
import Submission.Work.ThomBordism.existsFiniteGoodCover_of_c2Atlas
import Submission.Work.ThomBordism.exists_starRefinement
import Submission.Work.ThomBordism.goodCover_of_chartStarConvex
import Submission.Work.ThomBordism.exists_convex_image_ball

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# A finite good cover subordinate to a prescribed family

`Work.ThomBordism.existsFiniteGoodCover_of_c2Atlas` produces a finite good cover refining the
sources of a finite `C²` atlas.  This file records the (free) strengthening used by the annulus
chapter: the cover can moreover be *subordinated* to any family `W` containing the chart sources.
-/

namespace Work.ThomBordism.Grassmann.Torsion

open Set Metric

/-- **A finite `C²` atlas implies a finite good cover subordinate to `W`.** -/
theorem goodCoverSubordinate
    {n : ℕ} (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {m : ℕ} (ψ : Fin m → OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (hcov : (⋃ i, (ψ i).source) = Set.univ)
    (x : Fin m → X) (hx : ∀ i, x i ∈ (ψ i).source ∧ ψ i (x i) = 0)
    (hC2 : ∀ i j, ContDiffOn ℝ 2 (fun u : EuclideanSpace ℝ (Fin n) => ψ j ((ψ i).symm u))
      (ψ i '' ((ψ i).source ∩ (ψ j).source)))
    (hinj : ∀ i j, ∀ u ∈ ψ i '' ((ψ i).source ∩ (ψ j).source),
      Function.Injective (fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => ψ j ((ψ i).symm v)) u))
    (W : Fin m → Set X) (hW : ∀ i, (ψ i).source ⊆ W i) :
    ∃ (m' : ℕ) (U : Fin m' → Set X) (r : Fin m' → Fin m),
      (∀ i, IsOpen (U i)) ∧ (⋃ i, U i) = Set.univ ∧
      (∀ S : Finset (Fin m'), S.Nonempty → (⋂ i ∈ S, U i).Nonempty →
        ContractibleSpace ↥(⋂ i ∈ S, U i)) ∧
      (∀ i, U i ⊆ W (r i)) := by
  classical
  obtain ⟨κ, hκfin, Ws, rs, hWsopen, hWscov, hWssub, hWsstar⟩ :=
    Work.ThomBordism.exists_starRefinement (fun i : Fin m => (ψ i).source)
      (fun i => (ψ i).open_source) hcov
  letI : Fintype κ := hκfin
  let A : κ → Finset (Fin m) := fun j => Finset.univ.filter (fun α => Ws j ⊆ (ψ α).source)
  have good_exists : ∀ (j : κ) (p : EuclideanSpace ℝ (Fin n)),
      p ∈ ψ (rs j) '' Ws j →
      ∃ ε, 0 < ε ∧ ball p ε ⊆ ψ (rs j) '' Ws j ∧
        ∀ α ∈ A j, Convex ℝ ((fun u => ψ α ((ψ (rs j)).symm u)) '' ball p ε) := by
    intro j p hp
    refine Work.ThomBordism.exists_local_good_radius ψ hC2 hinj (rs j) (A j) (ψ (rs j) '' Ws j)
      ?_ p hp ?_
    · exact (ψ (rs j)).isOpen_image_of_subset_source (hWsopen j) (hWssub j)
    · intro α hα
      apply Set.image_mono
      intro c hc
      exact ⟨hWssub j hc, (Finset.mem_filter.mp hα).2 hc⟩
  let εg : κ → EuclideanSpace ℝ (Fin n) → ℝ := fun j p =>
    if h : p ∈ ψ (rs j) '' Ws j then Classical.choose (good_exists j p h) else 1
  have hεg : ∀ (j : κ) (p : EuclideanSpace ℝ (Fin n)) (hp : p ∈ ψ (rs j) '' Ws j),
      0 < εg j p ∧ ball p (εg j p) ⊆ ψ (rs j) '' Ws j ∧
        ∀ α ∈ A j, Convex ℝ ((fun u => ψ α ((ψ (rs j)).symm u)) '' ball p (εg j p)) := by
    intro j p hp
    have heq : εg j p = Classical.choose (good_exists j p hp) := by
      simp only [εg]; rw [dif_pos hp]
    rw [heq]
    exact Classical.choose_spec (good_exists j p hp)
  let good : κ × EuclideanSpace ℝ (Fin n) → Prop := fun jp => jp.2 ∈ ψ (rs jp.1) '' Ws jp.1
  let U : κ × EuclideanSpace ℝ (Fin n) → Set X := fun jp =>
    if good jp then (ψ (rs jp.1)).symm '' ball jp.2 (εg jp.1 jp.2) else ∅
  have hUdef : ∀ jp, U jp = if good jp then (ψ (rs jp.1)).symm '' ball jp.2 (εg jp.1 jp.2) else ∅ :=
    fun jp => rfl
  have hUopen : ∀ jp, IsOpen (U jp) := by
    intro jp
    by_cases hg : good jp
    · rw [hUdef jp, if_pos hg]
      refine (ψ (rs jp.1)).isOpen_image_symm_of_subset_target (Metric.isOpen_ball) ?_
      intro y hy
      have hb : y ∈ ψ (rs jp.1) '' Ws jp.1 := (hεg jp.1 jp.2 hg).2.1 hy
      rw [← (ψ (rs jp.1)).image_source_eq_target]
      exact Set.image_mono (hWssub jp.1) hb
    · rw [hUdef jp, if_neg hg]; exact isOpen_empty
  have hUcov : (⋃ jp, U jp) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro z
    have hz : z ∈ ⋃ j, Ws j := by rw [hWscov]; exact Set.mem_univ z
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    have hp : ψ (rs j) z ∈ ψ (rs j) '' Ws j := ⟨z, hj, rfl⟩
    refine Set.mem_iUnion.mpr ⟨(j, ψ (rs j) z), ?_⟩
    rw [hUdef, if_pos hp]
    exact ⟨ψ (rs j) z, Metric.mem_ball_self (hεg j (ψ (rs j) z) hp).1,
      (ψ (rs j)).left_inv (hWssub j hj)⟩
  have hsub : ∀ k : κ × EuclideanSpace ℝ (Fin n), U k ⊆ Ws k.1 := by
    intro k
    by_cases hg : good k
    · rw [hUdef k, if_pos hg]
      intro y hy
      obtain ⟨w, hw, rfl⟩ := hy
      have h1 : w ∈ ψ (rs k.1) '' Ws k.1 := (hεg k.1 k.2 hg).2.1 hw
      obtain ⟨c, hcW, hcw⟩ := h1
      rw [← hcw, (ψ (rs k.1)).left_inv (hWssub k.1 hcW)]
      exact hcW
    · rw [hUdef k, if_neg hg]; exact Set.empty_subset _
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hUopen (by rw [hUcov])
  let jp : Fin T.card → κ × EuclideanSpace ℝ (Fin n) :=
    fun k => (T.equivFin.symm k : κ × EuclideanSpace ℝ (Fin n))
  have hsub' : ∀ k : Fin T.card, U (jp k) ⊆ Ws (jp k).1 := fun k => hsub (jp k)
  refine ⟨T.card, fun k => U (jp k), fun k => rs (jp k).1, fun k => hUopen (jp k), ?_, ?_, ?_⟩
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
    have hsub_W : ∀ i, i ∈ S → U (jp i) ⊆ Ws (jp i).1 := fun i _ => hsub' i
    have hzW : ∀ i, i ∈ S → z₀ ∈ Ws (jp i).1 := fun i hi => hsub_W i hi (hz₀ i hi)
    have hchart : ∀ i, i ∈ S → Ws (jp i).1 ⊆ (ψ (rs (jp i₀).1)).source := by
      intro i hi
      exact hWsstar (jp i₀).1 (jp i).1 ⟨z₀, hzW i hi, hzW i₀ hi₀⟩
    refine ⟨ψ (rs (jp i₀).1), ψ (rs (jp i₀).1) z₀, ?_, ?_⟩
    · intro i hi
      exact (hsub_W i hi).trans (hchart i hi)
    · intro i hi
      have hgu := hgood_of i hi
      have himg : (ψ (rs (jp i₀).1)) '' U (jp i)
          = (fun u => ψ (rs (jp i₀).1) ((ψ (rs (jp i).1)).symm u)) ''
              ball (jp i).2 (εg (jp i).1 (jp i).2) := by
        rw [hUdef, if_pos hgu, Set.image_image]
      have hmemA : rs (jp i₀).1 ∈ A (jp i).1 := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hchart i hi⟩
      have hconv : Convex ℝ ((fun u => ψ (rs (jp i₀).1) ((ψ (rs (jp i).1)).symm u)) ''
          ball (jp i).2 (εg (jp i).1 (jp i).2)) :=
        (hεg (jp i).1 (jp i).2 hgu).2.2 (rs (jp i₀).1) hmemA
      rw [himg]
      exact hconv.starConvex (himg ▸ ⟨z₀, hz₀ i hi, rfl⟩)
  · intro k
    exact (hsub' k).trans ((hWssub (jp k).1).trans (hW (rs (jp k).1)))

end Work.ThomBordism.Grassmann.Torsion
