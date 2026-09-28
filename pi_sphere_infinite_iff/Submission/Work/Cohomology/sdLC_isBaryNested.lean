import Mathlib
import Submission.Work.Cohomology.Mesh

set_option synthInstance.maxHeartbeats 400000


set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **`stdSimplex.map` on uniform averages.**  Pushing the uniform average of a nonempty finite set
`S` of vertices forward along an *injective* map `f` gives the uniform average of the image
`S.image f`.  This is the combinatorial heart of `sdLC_isBaryNested`. -/
theorem stdSimplex_map_baryOf {ι η : Type*} [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η]
    (f : ι → η) (hf : Function.Injective f) (S : Finset ι) (hS : S.Nonempty) :
    stdSimplex.map f (baryOf S hS) = baryOf (S.image f) (hS.image f) := by
  ext z
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, baryOf_apply]
  rw [show (Finset.univ.filter (fun x => f x = z)).sum ⇑(baryOf S hS) =
      (Finset.univ.filter (fun x => f x = z)).sum
        (fun x => if x ∈ S then (S.card : ℝ)⁻¹ else 0) from
    Finset.sum_congr rfl (fun x _ => baryOf_apply S hS x)]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  by_cases hz : z ∈ Finset.image f S
  · obtain ⟨x₀, hx₀S, hx₀⟩ := Finset.mem_image.mp hz
    have hcard : ((Finset.univ.filter (fun x => f x = z)).filter (· ∈ S)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨x₀, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hfx, hxS⟩
        exact hf (by rw [hfx, hx₀])
      · intro h; subst h; exact ⟨hx₀, hx₀S⟩
    rw [hcard, if_pos hz, Finset.card_image_of_injective S hf]
    simp
  · rw [if_neg hz]
    have hempty : ((Finset.univ.filter (fun x => f x = z)).filter (· ∈ S)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx hxS
      exact hz (Finset.mem_image.mpr ⟨x, hxS, (Finset.mem_filter.mp hx).2⟩)
    rw [hempty]
    simp

/-- **Cone–embedding preserves `IsBaryNested`.**  If the vertex family `u` of `Δⁿ` is a nested chain
of uniform averages of the standard vertices, then so is the vertex family of `Δ^{n+1}` obtained by
coning `u` over the barycentre of `Δ^{n+1}` after pushing `u` forward along the `i`-th face
embedding `Fin.succAbove i`. -/
theorem isBaryNested_coneEmbed {n : ℕ}
    (u : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1))) (hu : IsBaryNested u)
    (i : Fin (n + 2)) :
    IsBaryNested (Fin.cons (bary (idVert (n + 1)))
      (fun j => stdSimplex.map (Fin.succAbove i) (u j))) := by
  obtain ⟨T, hT, hnest, hw⟩ := hu
  refine ⟨Fin.cases Finset.univ (fun j => (T j).image (Fin.succAbove i)), ?_, ?_, ?_⟩
  · intro l
    induction l using Fin.cases with
    | zero => exact Finset.univ_nonempty
    | succ j => exact (hT j).image _
  · intro a
    induction a using Fin.cases with
    | zero =>
      intro b _
      exact Finset.subset_univ _
    | succ a' =>
      intro b hab
      induction b using Fin.cases with
      | zero => exact absurd hab (not_le.mpr (Fin.succ_pos a'))
      | succ b' =>
        simp only [Fin.cases_succ]
        exact Finset.image_subset_image (hnest a' b' (Fin.succ_le_succ_iff.mp hab))
  · intro l
    induction l using Fin.cases with
    | zero =>
      rw [Fin.cons_zero]
      exact bary_eq_baryOf_univ (n + 1)
    | succ j =>
      rw [Fin.cons_succ, hw j]
      exact stdSimplex_map_baryOf (Fin.succAbove i) (Fin.succAbove_right_injective) (T j) (hT j)

/-- `sdLC_isBaryNested` for an arbitrary `n`, proved by induction on `n`. -/
private theorem sdLC_isBaryNested_aux : ∀ n : ℕ,
    ∀ w : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)),
      w ∈ (sdLC n).support → IsBaryNested w := by
  intro n
  induction n with
  | zero =>
    intro w hw
    rw [show sdLC 0 = Finsupp.single (idVert 0) (1 : ℤ) from rfl,
      Finsupp.support_single _ (by norm_num : (1 : ℤ) ≠ 0)] at hw
    rw [Finset.mem_singleton] at hw
    subst hw
    refine ⟨fun _ => Finset.univ, fun _ => Finset.univ_nonempty, ?_, ?_⟩
    · intro a b _
      exact Finset.subset_univ _
    · intro l
      haveI : Subsingleton (Fin (0 + 1)) := ⟨fun a b => Fin.ext (by omega)⟩
      exact Subsingleton.elim _ _
  | succ n ih =>
    intro w hw
    rw [show sdLC (n + 1) = coneLC (n + 1) n (bary (idVert (n + 1)))
        (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • embedLC n n i (sdLC n)) from rfl] at hw
    rw [show coneLC (n + 1) n (bary (idVert (n + 1)))
        (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • embedLC n n i (sdLC n))
        = Finsupp.mapDomain (coneVF (bary (idVert (n + 1))))
          (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • embedLC n n i (sdLC n)) from rfl] at hw
    obtain ⟨v, hv, hwv⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hw)
    obtain ⟨i, -, hvi⟩ := Finset.mem_biUnion.mp
      ((Finsupp.support_finsetSum (s := Finset.univ)
        (f := fun i : Fin (n + 2) => ((-1 : ℤ) ^ (i : ℕ)) • embedLC n n i (sdLC n))) hv)
    have hvi' : v ∈ (embedLC n n i (sdLC n)).support := Finsupp.support_smul hvi
    rw [show embedLC n n i (sdLC n) = Finsupp.mapDomain
        (fun u : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)) =>
          fun j => stdSimplex.map (Fin.succAbove i) (u j)) (sdLC n) from rfl] at hvi'
    obtain ⟨u, hu, hvu⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hvi')
    have hthis : IsBaryNested (Fin.cons (bary (idVert (n + 1)))
        (fun j => stdSimplex.map (Fin.succAbove i) (u j))) :=
      isBaryNested_coneEmbed u (ih u hu) i
    have hwv' : (Fin.cons (bary (idVert (n + 1))) v) = w := hwv
    rwa [hvu, hwv'] at hthis

theorem sdLC_isBaryNested (k : ℕ) (w : Fin (k + 1) → stdSimplex ℝ (Fin (k + 1)))
    (hw : w ∈ (sdLC k).support) : IsBaryNested w :=
  sdLC_isBaryNested_aux k w hw

end

end Work.Cohomology
