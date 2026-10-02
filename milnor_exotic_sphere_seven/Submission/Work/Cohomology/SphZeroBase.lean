import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.SphDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The space `Sᵖ × S⁰`, its two components, and the sections of the projection

This module collects the elementary definitions used in the proof of
`Work.Cohomology.cohProdSphZero`: the two points of `S⁰ = sphSet 1`, the space `Sᵖ × S⁰` and the
two sections `y ↦ (y, ±1)` of the projection onto `Sᵖ`, together with the fact that a continuous
map from the standard simplex into `Sᵖ × S⁰` has constant second coordinate.
-/

namespace Work.Cohomology

open CategoryTheory Limits Work.Cohomology
open scoped Simplicial Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-! ## The two points of `S⁰ = sphSet 1` -/

/-- The point `1` of `S⁰`. -/
def s0N : ↥(sphSet 1) :=
  ⟨WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)), by
    show ‖WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ))‖ = 1
    rw [EuclideanSpace.norm_eq]; simp⟩

/-- The point `-1` of `S⁰`. -/
def s0S : ↥(sphSet 1) :=
  ⟨WithLp.toLp 2 (fun _ : Fin 1 => (-1 : ℝ)), by
    show ‖WithLp.toLp 2 (fun _ : Fin 1 => (-1 : ℝ))‖ = 1
    rw [EuclideanSpace.norm_eq]; simp⟩

lemma s0N_ne_s0S : s0N ≠ s0S := by
  intro h
  have hc := congrArg (fun x : ↥(sphSet 1) => (x : EuclideanSpace ℝ (Fin 1)) 0) h
  simp [s0N, s0S] at hc
  norm_num at hc

lemma s0_cover (x : ↥(sphSet 1)) : x = s0N ∨ x = s0S := by
  have hmem : ‖(x : EuclideanSpace ℝ (Fin 1))‖ = 1 := x.2
  have h1 : ‖(x : EuclideanSpace ℝ (Fin 1))‖ = |(x : EuclideanSpace ℝ (Fin 1)) 0| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs]
  rw [h1] at hmem
  have h2 : ((x : EuclideanSpace ℝ (Fin 1)) 0) ^ 2 = 1 := by
    have := sq_abs ((x : EuclideanSpace ℝ (Fin 1)) 0)
    nlinarith [abs_nonneg ((x : EuclideanSpace ℝ (Fin 1)) 0), hmem]
  rcases sq_eq_one_iff.mp h2 with h | h
  · left; ext i; fin_cases i; simpa [s0N] using h
  · right; ext i; fin_cases i; simpa [s0S] using h

lemma s0_finite : (sphSet 1).Finite := by
  have hfin : ({((s0N : ↥(sphSet 1)) : EuclideanSpace ℝ (Fin 1)),
      ((s0S : ↥(sphSet 1)) : EuclideanSpace ℝ (Fin 1))} : Set (EuclideanSpace ℝ (Fin 1))).Finite :=
    Set.Finite.insert _ (Set.finite_singleton _)
  refine hfin.subset (fun x hx => ?_)
  rcases s0_cover ⟨x, hx⟩ with hh | hh
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inl (congrArg Subtype.val hh)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (congrArg Subtype.val hh)

lemma s0_discrete : DiscreteTopology ↥(sphSet 1) := by
  rw [← isDiscrete_iff_discreteTopology]
  exact s0_finite.isDiscrete

/-! ## The spaces and the two sections -/

/-- `Sᵖ`. -/
abbrev SphY (p : ℕ) : TopCat := TopCat.of ↥(sphSet (p+1))

/-- `Sᵖ × S⁰`. -/
abbrev SphX (p : ℕ) : TopCat := TopCat.of (↥(sphSet (p+1)) × ↥(sphSet 1))

/-- The projection `Sᵖ × S⁰ ⟶ Sᵖ`. -/
def sProj (p : ℕ) : SphX p ⟶ SphY p := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The section `y ↦ (y, 1)` of the projection. -/
def sSec₁ (p : ℕ) : SphY p ⟶ SphX p :=
  TopCat.ofHom ⟨fun y => (y, s0N), continuous_id.prodMk continuous_const⟩

/-- The section `y ↦ (y, -1)` of the projection. -/
def sSec₂ (p : ℕ) : SphY p ⟶ SphX p :=
  TopCat.ofHom ⟨fun y => (y, s0S), continuous_id.prodMk continuous_const⟩

@[simp] lemma sSec₁_comp_sProj (p : ℕ) : sSec₁ p ≫ sProj p = 𝟙 (SphY p) := by
  apply TopCat.hom_ext; ext y; rfl

@[simp] lemma sSec₂_comp_sProj (p : ℕ) : sSec₂ p ≫ sProj p = 𝟙 (SphY p) := by
  apply TopCat.hom_ext; ext y; rfl

/-- A continuous map from the standard simplex into `Sᵖ × S⁰` has constant second coordinate. -/
lemma contMap_snd_const {n p : ℕ}
    (σ : C(↥(stdSimplex ℝ (Fin (n+1))), ↥(sphSet (p+1)) × ↥(sphSet 1))) :
    ∃ c : ↥(sphSet 1), ∀ t, (σ t).2 = c := by
  haveI : DiscreteTopology ↥(sphSet 1) := s0_discrete
  have hcont : Continuous (fun t : ↥(stdSimplex ℝ (Fin (n+1))) => (σ t).2) :=
    continuous_snd.comp σ.continuous
  refine ⟨(σ (Classical.arbitrary _)).2, fun t => ?_⟩
  exact PreconnectedSpace.constant (Y := ↥(sphSet 1))
    (inferInstance : PreconnectedSpace ↥(stdSimplex ℝ (Fin (n+1)))) hcont
    (x := t) (y := Classical.arbitrary _)

/-! ## The induced maps on `n`-simplices -/

/-- The map on `n`-simplices induced by the first section. -/
def sIdx₁ (p n : ℕ) :
    (TopCat.toSSet.obj (SphY p)).obj (Opposite.op ⦋n⦌) →
      (TopCat.toSSet.obj (SphX p)).obj (Opposite.op ⦋n⦌) :=
  fun a => (TopCat.toSSet.map (sSec₁ p)).app (Opposite.op ⦋n⦌) a

/-- The map on `n`-simplices induced by the second section. -/
def sIdx₂ (p n : ℕ) :
    (TopCat.toSSet.obj (SphY p)).obj (Opposite.op ⦋n⦌) →
      (TopCat.toSSet.obj (SphX p)).obj (Opposite.op ⦋n⦌) :=
  fun a => (TopCat.toSSet.map (sSec₂ p)).app (Opposite.op ⦋n⦌) a

/-- The map on `n`-simplices induced by the two sections, from the disjoint union of two copies
of the `n`-simplices of `Sᵖ`. -/
def sIdxSum (p n : ℕ) :
    (TopCat.toSSet.obj (SphY p)).obj (Opposite.op ⦋n⦌) ⊕
        (TopCat.toSSet.obj (SphY p)).obj (Opposite.op ⦋n⦌) →
      (TopCat.toSSet.obj (SphX p)).obj (Opposite.op ⦋n⦌) :=
  Sum.elim (sIdx₁ p n) (sIdx₂ p n)

@[simp] lemma sIdxSum_inl (p n : ℕ)
    (a : (TopCat.toSSet.obj (SphY p)).obj (Opposite.op ⦋n⦌)) :
    sIdxSum p n (Sum.inl a) = sIdx₁ p n a := rfl

@[simp] lemma sIdxSum_inr (p n : ℕ)
    (a : (TopCat.toSSet.obj (SphY p)).obj (Opposite.op ⦋n⦌)) :
    sIdxSum p n (Sum.inr a) = sIdx₂ p n a := rfl

end

end Work.Cohomology
