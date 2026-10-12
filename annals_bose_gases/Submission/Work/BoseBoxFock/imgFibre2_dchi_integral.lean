import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.imgFibre2Aux
import Submission.Work.BoseBoxFock.imgFibreDG_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibre2_dchi_integral`

The `χ`-weighted Dirichlet identity for the **mirror** fibre: with the `p.2`-slot integral written
*inside* the fibres,

    ∫_{u ∈ boxL ℓ} ∫_{v ∈ boxL ℓ} χ_ℓ(u)² · (∫_{x' ∈ π(boxL ℓ)} Σ_j (∂_{p.1,j} G)(ins p u v x')²)
      = imgFibreDχ ℓ p G .

This is the mirror-fibre companion of `Work.BoseBoxFock.imgFibreDG_integral`: both sides are
integrals of the same function over the box `abox n ℓ`, read through the measure-preserving
coordinate insertion `Φ ((u,v),x') = insertCoord2 p u v x'`.  The only difference from the proved
`imgFibreDG_integral_gen` is the *order* of the two inner integrals (`v` before `x'`), which is
bridged by one Fubini swap (`MeasureTheory.integral_integral_swap`), the weight `χ_ℓ(u)²` being
pulled out of the `v`-integral, and the fact that `ins p u v x' p.1 = u`
(`insertCoord2_apply_fst`).

`sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The measure-theoretic core.**  For *any* continuous `f`, the `boxL × boxL`-integral of the
`χ`-weight against the `(x', v)`-fibre of `f` equals the χ-weighted content of `f` on `abox n ℓ`.
This is `imgFibreDG_integral_gen` with the `p.2`-slot integral written *before* the fibre integral
(one Fubini swap and one `integral_const_mul`). -/
theorem imgFibre2_dchi_integral_gen {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {f : Submission.BoseGases.X n → ℝ} (hf : Continuous f) :
    (∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
      (Submission.BoseGases.chiScale ℓ u) ^ 2
        * (∫ x' in Work.BoseBoxFock.boxPiSet (pairFib2 n p) ℓ, f (insertCoord2 p u v x')))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x p.1)) ^ 2 * f x := by
  classical
  have hpu : ∀ u : E3,
      (∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ u) ^ 2
            * (∫ x' in Work.BoseBoxFock.boxPiSet (pairFib2 n p) ℓ,
                f (insertCoord2 p u v x')))
      = (Submission.BoseGases.chiScale ℓ u) ^ 2
          * (∫ x' in Work.BoseBoxFock.boxPiSet (pairFib2 n p) ℓ,
              ∫ s in Work.BoseK15.corpusBox.boxL ℓ, f (insertCoord2 p u s x')) := by
    intro u
    have h1 : (∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ u) ^ 2
            * (∫ x' in Work.BoseBoxFock.boxPiSet (pairFib2 n p) ℓ,
                f (insertCoord2 p u v x')))
        = (Submission.BoseGases.chiScale ℓ u) ^ 2
            * (∫ v in Work.BoseK15.corpusBox.boxL ℓ,
                ∫ x' in Work.BoseBoxFock.boxPiSet (pairFib2 n p) ℓ,
                  f (insertCoord2 p u v x')) := by
      rw [← MeasureTheory.integral_const_mul ((Submission.BoseGases.chiScale ℓ u) ^ 2)
        (fun v : E3 =>
          ∫ x' in Work.BoseBoxFock.boxPiSet (pairFib2 n p) ℓ, f (insertCoord2 p u v x'))]
    have h2 : (∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ x' in Work.BoseBoxFock.boxPiSet (pairFib2 n p) ℓ,
            f (insertCoord2 p u v x'))
        = ∫ x' in Work.BoseBoxFock.boxPiSet (pairFib2 n p) ℓ,
            ∫ s in Work.BoseK15.corpusBox.boxL ℓ, f (insertCoord2 p u s x') := by
      have hL : (∫ v in Work.BoseK15.corpusBox.boxL ℓ,
            ∫ x' in Work.BoseBoxFock.boxPiSet (pairFib2 n p) ℓ,
              f (insertCoord2 p u v x'))
          = ∫ v : E3, (∫ x' : pairFib2 n p → E3, f (insertCoord2 p u v x')
              ∂(Measure.pi (fun _ : pairFib2 n p => boxMeas ℓ))) ∂(boxMeas ℓ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        exact setIntegral_boxPiSet_eq (fun x' : pairFib2 n p → E3 =>
          f (insertCoord2 p u v x'))
      have hR : (∫ x' in Work.BoseBoxFock.boxPiSet (pairFib2 n p) ℓ,
            ∫ s in Work.BoseK15.corpusBox.boxL ℓ, f (insertCoord2 p u s x'))
          = ∫ x' : pairFib2 n p → E3, (∫ s : E3, f (insertCoord2 p u s x') ∂(boxMeas ℓ))
              ∂(Measure.pi (fun _ : pairFib2 n p => boxMeas ℓ)) := by
        exact setIntegral_boxPiSet_eq (fun x' : pairFib2 n p → E3 =>
          ∫ s in Work.BoseK15.corpusBox.boxL ℓ, f (insertCoord2 p u s x'))
      rw [hL, hR]
      refine MeasureTheory.integral_integral_swap ?_
      have hc : Continuous (fun z : E3 × (pairFib2 n p → E3) =>
          f (insertCoord2 p u z.1 z.2)) :=
        hf.comp ((contDiff_insertCoord2_comp (P := E3 × (pairFib2 n p → E3)) p
          contDiff_const contDiff_fst contDiff_snd).continuous)
      exact integrable_boxPi_pair hℓ hc
    rw [h1, h2]
  calc (∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
      (Submission.BoseGases.chiScale ℓ u) ^ 2
        * (∫ x' in Work.BoseBoxFock.boxPiSet (pairFib2 n p) ℓ, f (insertCoord2 p u v x')))
      = ∫ u in Work.BoseK15.corpusBox.boxL ℓ,
          (Submission.BoseGases.chiScale ℓ u) ^ 2
            * (∫ x' in Work.BoseBoxFock.boxPiSet (pairFib2 n p) ℓ,
                ∫ s in Work.BoseK15.corpusBox.boxL ℓ, f (insertCoord2 p u s x')) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => hpu u)
    _ = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x p.1)) ^ 2 * f x :=
        imgFibreDG_integral_gen (n := n) (ℓ := ℓ) hℓ hp hf

theorem imgFibre2_dchi_integral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {G : Submission.BoseGases.X n → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    (∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
      (Submission.BoseGases.chiScale ℓ u) ^ 2
        * (∫ x' in Work.BoseBoxFock.boxPiSet (Work.BoseBoxFock.pairFib2 n p) ℓ,
            ∑ j : Fin 3,
              (fderiv ℝ G (Work.BoseBoxFock.insertCoord2 p u v x')
                (Work.BoseBoxFock.slotDirVec p.1 j)) ^ 2))
      = Work.BoseBoxFock.imgFibreDχ ℓ p G := by
  classical
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    rw [show (0 : WithTop ℕ∞) = ((0 : ℕ∞) : WithTop ℕ∞) from rfl]
    exact fun h => ENat.top_ne_zero (WithTop.coe_eq_coe.mp h)
  have hf : Continuous (fun x : Submission.BoseGases.X n =>
      ∑ j : Fin 3, (fderiv ℝ G x (slotDirVec p.1 j)) ^ 2) := by
    refine continuous_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => ?_)
    exact (((hG.continuous_fderiv_apply hne).comp
      (continuous_id.prodMk continuous_const))).pow 2
  have h := imgFibre2_dchi_integral_gen (n := n) (ℓ := ℓ) (p := p) hℓ hp
    (f := fun x : Submission.BoseGases.X n =>
      ∑ j : Fin 3, (fderiv ℝ G x (slotDirVec p.1 j)) ^ 2) hf
  simpa only [imgFibreDχ] using h

end Work.BoseBoxFock
