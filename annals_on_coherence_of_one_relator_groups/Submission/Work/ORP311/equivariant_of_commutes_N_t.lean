import Mathlib
import Submission.Work.ORP311.Defs
import Submission.Work.ORVonNeumann.Rep.vnDiag
import Submission.Work.ORVonNeumann.Rep.vnBlockUpperAdjointKernel

namespace Work.ORP311

open Work.ORVonNeumann.Rep

/-- `diagOp m 1` is the identity operator on `HSum m` (pointwise through the coordinates). -/
theorem diagOp_one_aux {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (m : ℕ) :
    diagOp (G := G) m (1 : G) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply hsum_ext
  intro i
  rw [hcoord_diagOp_apply, rightRegOp_one_apply]
  rfl

/-- A conjugation-cancellation lemma: if an operator `D` commutes with `U`, and `U'` is a
left inverse of `U` which is also a right inverse, then `D` commutes with `U'`. -/
theorem comp_inv_aux {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {m : ℕ}
    {D : HSum (G := G) m →L[ℂ] HSum (G := G) m}
    {U U' : HSum (G := G) m →L[ℂ] HSum (G := G) m}
    (hU'U : U'.comp U = 1) (hUU' : U.comp U' = 1) (hc : D.comp U = U.comp D) :
    D.comp U' = U'.comp D := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply]
  have hU'Ux : ∀ z, U' (U z) = z := fun z => congrArg (fun f => f z) hU'U
  have hUU'x : ∀ z, U (U' z) = z := fun z => congrArg (fun f => f z) hUU'
  have hx : D (U (U' x)) = U (D (U' x)) := congrArg (fun f => f (U' x)) hc
  calc D (U' x) = U' (U (D (U' x))) := (hU'Ux (D (U' x))).symm
    _ = U' (D (U (U' x))) := by rw [hx]
    _ = U' (D x) := by rw [hUU'x]

/-- **Commutation with the block diagonal right regular action propagates from `N` and `t`
to all of `G` when `G = N ⋊ ⟨t⟩`.**  The set of elements of `G` whose `diagOp` commutes with
`D` is a subgroup of `G` (using `diagOp_mul` and the cancellation lemma
`comp_inv_aux`); it contains `t` and every element of `N`, and by
`IsExtensionByZ` every element of `G` is a product `n * t ^ k`, hence lies in it. -/
theorem equivariant_of_commutes_N_t {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} (hext : Work.ORP311.IsExtensionByZ G N t) {m : ℕ} {D : Work.ORVonNeumann.Rep.HSum (G := G) m →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) m} (hn : ∀ n : ↥N, D.comp (Work.ORVonNeumann.Rep.diagOp (G := G) m (n : G)) = (Work.ORVonNeumann.Rep.diagOp (G := G) m (n : G)).comp D) (ht : D.comp (Work.ORVonNeumann.Rep.diagOp (G := G) m t) = (Work.ORVonNeumann.Rep.diagOp (G := G) m t).comp D) : Work.ORVonNeumann.Rep.Equivariant (G := G) D := by
  intro g
  let S : Subgroup G :=
    { carrier := {g : G | D.comp (diagOp (G := G) m g) = (diagOp (G := G) m g).comp D}
      mul_mem' := by
        intro a b ha hb
        show D.comp (diagOp (G := G) m (a * b)) = (diagOp (G := G) m (a * b)).comp D
        rw [← diagOp_mul, ← ContinuousLinearMap.comp_assoc, ha,
          ContinuousLinearMap.comp_assoc, hb, ← ContinuousLinearMap.comp_assoc]
      one_mem' := by
        show D.comp (diagOp (G := G) m (1 : G)) = (diagOp (G := G) m (1 : G)).comp D
        rw [diagOp_one_aux, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id,
          ContinuousLinearMap.id_comp]
      inv_mem' := by
        intro a ha
        show D.comp (diagOp (G := G) m a⁻¹) = (diagOp (G := G) m a⁻¹).comp D
        refine comp_inv_aux ?_ ?_ ha
        · rw [diagOp_mul, inv_mul_cancel]
          exact diagOp_one_aux m
        · rw [diagOp_mul, mul_inv_cancel]
          exact diagOp_one_aux m }
  have htS : t ∈ S := ht
  have hNS : ∀ n : ↥N, (n : G) ∈ S := fun n => hn n
  obtain ⟨n, k, hk⟩ := hext.1 g
  have hfin : g ∈ S := by
    rw [hk]
    exact S.mul_mem (hNS n) (S.zpow_mem htS k)
  exact hfin

end Work.ORP311
