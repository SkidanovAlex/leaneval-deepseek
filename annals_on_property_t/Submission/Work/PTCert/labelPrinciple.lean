import Mathlib
import Submission.Work.PTCert.Interfaces

/-! Guidance from the project lead (the requester): ... (unchanged; see git history) -/

namespace Work.PTCert

open Submission.PTCert

/-! ### Auxiliary lemmas about `conjAvg` -/

section Aux

variable {G : Type} [Group G]

/-- `conjAvg` is additive in its second argument. -/
private lemma conjAvg_add (Sg : Finset G) (x y : MonoidAlgebra ℝ G) :
    conjAvg Sg (x + y) = conjAvg Sg x + conjAvg Sg y := by
  simp only [conjAvg, mul_add, add_mul, Finset.sum_add_distrib]

/-- `conjAvg` is `ℝ`-linear in its second argument. -/
private lemma conjAvg_smul (Sg : Finset G) (a : ℝ) (x : MonoidAlgebra ℝ G) :
    conjAvg Sg (a • x) = a • conjAvg Sg x := by
  simp only [conjAvg]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro s hs
  rw [mul_smul_comm, smul_mul_assoc]

/-- `conjAvg` packaged as an `ℝ`-linear map. -/
private noncomputable def conjLin (Sg : Finset G) :
    MonoidAlgebra ℝ G →ₗ[ℝ] MonoidAlgebra ℝ G where
  toFun := conjAvg Sg
  map_add' := conjAvg_add Sg
  map_smul' := conjAvg_smul Sg

private lemma conjLin_apply (Sg : Finset G) (x : MonoidAlgebra ℝ G) :
    conjLin Sg x = conjAvg Sg x := rfl

/-- **Reindexing / conjugation invariance.**  For `s ∈ Sg` with `Sg` a finite subgroup, the
`Sg`-average of `of s * x * of s⁻¹` equals that of `x`: the map `u ↦ u * s` is a bijection
of `Sg` (`t ↦ t * s⁻¹` is its inverse) and termwise
`of u * (of s * x * of s⁻¹) * of u⁻¹ = of (u * s) * x * of (u * s)⁻¹`. -/
private lemma conjAvg_conj (Sg : Finset G) (hSg : IsFinSubgroup Sg) {s : G} (hs : s ∈ Sg)
    (x : MonoidAlgebra ℝ G) :
    conjAvg Sg (MonoidAlgebra.of ℝ G s * x * MonoidAlgebra.of ℝ G s⁻¹) = conjAvg Sg x := by
  simp only [conjAvg]
  refine Finset.sum_nbij' (fun u => u * s) (fun v => v * s⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro u hu; exact hSg.2.1 u hu s hs
  · intro v hv; exact hSg.2.1 v hv s⁻¹ (hSg.2.2 s hs)
  · intro u _; simp [mul_assoc]
  · intro v _; simp [mul_assoc]
  · intro u _
    rw [mul_inv_rev, map_mul, map_mul]
    noncomm_ring

end Aux

/-- **(P2) Label principle.**  A finite linear combination of group elements whose terms
carry labels `lab t` and conjugators `s ∈ Sg` with `s * e t * s⁻¹ = r (lab t)`, and whose
coefficients sum to zero on every label, has zero `Sg`-average. -/
theorem labelPrinciple : LabelPrinciple := by
  intro G _ _ Sg hSg ι I c e lab r hconj hzero
  -- Each term's average only depends on its label.
  have hpt : ∀ t ∈ I, conjAvg Sg (MonoidAlgebra.of ℝ G (e t))
      = conjAvg Sg (MonoidAlgebra.of ℝ G (r (lab t))) := by
    intro t ht
    obtain ⟨s, hs, hsconj⟩ := hconj t ht
    have hof : MonoidAlgebra.of ℝ G (s * e t * s⁻¹)
        = MonoidAlgebra.of ℝ G (r (lab t)) := congrArg _ hsconj
    simp only [map_mul] at hof
    have h := conjAvg_conj (G := G) (Sg := Sg) hSg hs (MonoidAlgebra.of ℝ G (e t))
    rw [hof] at h
    exact h.symm
  -- Pull the average inside the linear combination.
  have h1 : conjAvg Sg (∑ t ∈ I, c t • MonoidAlgebra.of ℝ G (e t))
      = ∑ t ∈ I, c t • conjAvg Sg (MonoidAlgebra.of ℝ G (e t)) := by
    change conjLin Sg (∑ t ∈ I, c t • MonoidAlgebra.of ℝ G (e t))
      = ∑ t ∈ I, c t • conjAvg Sg (MonoidAlgebra.of ℝ G (e t))
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [map_smul]
    rfl
  have h2 : ∑ t ∈ I, c t • conjAvg Sg (MonoidAlgebra.of ℝ G (e t))
      = ∑ t ∈ I, c t • conjAvg Sg (MonoidAlgebra.of ℝ G (r (lab t))) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [hpt t ht]
  -- Group by label.
  have h3 : ∑ t ∈ I, c t • conjAvg Sg (MonoidAlgebra.of ℝ G (r (lab t)))
      = ∑ l ∈ I.image lab,
          ∑ t ∈ I.filter (fun t => lab t = l), c t • conjAvg Sg (MonoidAlgebra.of ℝ G (r l)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := I) (t := I.image lab) (g := lab)
        (fun i hi => Finset.mem_image_of_mem lab hi)
        (fun t => c t • conjAvg Sg (MonoidAlgebra.of ℝ G (r (lab t))))]
    refine Finset.sum_congr rfl ?_
    intro l _
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [Finset.mem_filter] at ht
    rw [ht.2]
  have h4 : ∑ l ∈ I.image lab,
      (∑ t ∈ I.filter (fun t => lab t = l), c t • conjAvg Sg (MonoidAlgebra.of ℝ G (r l))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro l _
    rw [← Finset.sum_smul, hzero l, zero_smul]
  rw [h1, h2, h3]
  exact h4

end Work.PTCert
