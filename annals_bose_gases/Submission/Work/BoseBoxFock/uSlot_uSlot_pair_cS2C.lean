import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.integral_conj_mul_aPC_aPC
import Submission.Work.BoseBoxFock.sum_univ_eq_diag_add_pairSet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.uSlot_uSlot_pair_cS2C`

The **pair row** of the box ↔ model dictionary: for the pinned condensate orbital
`u = e 0 = c · θ_Λ` (`conj c · c = ℓ⁻³`) and a box state `Θ` that is essentially bounded and
supported in the box, the pairing of `Θ` with the *square* of the condensate slot operator is
the sum of the condensate and pair-condensate counts,

    `Re ∫_box conj Θ · (Σ_i uSlot_i)(Σ_j uSlot_j) Θ = cS1C ℓ Θ + cS2C ℓ Θ`.

Mathematically, on the box the slot operator of `e 0` *is* the slot mean `aPC ℓ i`
(`uSlot_ae_eq_aPC`), so the left-hand side is

    `Σ_{i,j} ⟨Θ, P_i P_j Θ⟩`  with `P_k = aPC ℓ k` the orthogonal projection onto the functions
    constant in the `k`-th slot (`aPC_idem`, `aPC_sym_box`, `aPC_aQC_eq_zero`).

Each `P_iP_j` is again an orthogonal projection, so `⟨Θ, P_iP_jΘ⟩ = ‖P_iP_jΘ‖²`
(`integral_conj_mul_aPC_aPC`); splitting the double sum into its diagonal and off-diagonal parts
(`sum_univ_eq_diag_add_pairSet`) and using `P_iP_i = P_i` (`aPC_idem`) gives exactly
`Σ_i ∫ ‖P_iΘ‖² + Σ_{i≠j} ∫ ‖P_iP_jΘ‖² = cS1C ℓ Θ + cS2C ℓ Θ`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

theorem uSlot_uSlot_pair_cS2C {m d : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    {c : ℂ} (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹)
    (hun : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      e 0 z = c * Work.BoseK15.corpusBox.thetaFun ℓ z)
    {Θ : Work.BoseDict.Xn d → ℂ} (hΘm : MeasureTheory.MemLp Θ (⊤ : ENNReal))
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox d ℓ) :
    (Work.BoseDict.cIPn d Θ (fun x => Finset.sum Finset.univ (fun i : Fin d =>
        Finset.sum Finset.univ (fun j : Fin d =>
          Work.BoseBoxFock.uSlot (e 0) i (Work.BoseBoxFock.uSlot (e 0) j Θ) x)))).re
      = Work.BoseBoxFock.cS1C ℓ Θ + Work.BoseBoxFock.cS2C ℓ Θ := by
  classical
  cases d with
  | zero =>
    -- the two slot sums are empty
    have hz : Work.BoseDict.cIPn 0 Θ
        (fun x => ∑ i : Fin 0, ∑ j : Fin 0, uSlot (e 0) i (uSlot (e 0) j Θ) x) = 0 := by
      rw [Work.BoseDict.cIPn]
      simp
    rw [hz, Complex.zero_re]
    simp [cS1C, cS2C, Submission.BoseGases.pairSet]
  | succ n =>
    -- ## 0. the per-pair projection identity and the diagonal/off-diagonal split
    have hpair : ∀ i j : Fin (n + 1),
        MeasureTheory.IntegrableOn
            (fun x => (starRingEnd ℂ) (Θ x) * aPC ℓ i (aPC ℓ j Θ) x)
            (Submission.BoseGases.abox (n + 1) ℓ) MeasureTheory.volume
          ∧ (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (starRingEnd ℂ) (Θ x) * aPC ℓ i (aPC ℓ j Θ) x)
            = ((∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                ‖aPC ℓ i (aPC ℓ j Θ) x‖ ^ 2 : ℝ) : ℂ) := by
      intro i j
      exact integral_conj_mul_aPC_aPC hℓ hΘm hΘs i j
    have hcomb : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          ∫ x in Submission.BoseGases.abox (n + 1) ℓ, ‖aPC ℓ i (aPC ℓ j Θ) x‖ ^ 2)
        = (∑ i : Fin (n + 1),
            ∫ x in Submission.BoseGases.abox (n + 1) ℓ, ‖aPC ℓ i Θ x‖ ^ 2)
          + ∑ p ∈ Submission.BoseGases.pairSet (n + 1),
              ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                ‖aPC ℓ p.1 (aPC ℓ p.2 Θ) x‖ ^ 2 := by
      have hdiag : (∑ i : Fin (n + 1),
            ∫ x in Submission.BoseGases.abox (n + 1) ℓ, ‖aPC ℓ i (aPC ℓ i Θ) x‖ ^ 2)
          = ∑ i : Fin (n + 1),
            ∫ x in Submission.BoseGases.abox (n + 1) ℓ, ‖aPC ℓ i Θ x‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun x => ?_))
        show ‖aPC ℓ i (aPC ℓ i Θ) x‖ ^ 2 = ‖aPC ℓ i Θ x‖ ^ 2
        rw [show aPC ℓ i (aPC ℓ i Θ) x = aPC ℓ i Θ x from congrFun (aPC_idem hℓ i) x]
      calc (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            ∫ x in Submission.BoseGases.abox (n + 1) ℓ, ‖aPC ℓ i (aPC ℓ j Θ) x‖ ^ 2)
          = (∑ i : Fin (n + 1),
              ∫ x in Submission.BoseGases.abox (n + 1) ℓ, ‖aPC ℓ i (aPC ℓ i Θ) x‖ ^ 2)
            + ∑ p ∈ Submission.BoseGases.pairSet (n + 1),
                ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                  ‖aPC ℓ p.1 (aPC ℓ p.2 Θ) x‖ ^ 2 :=
            sum_univ_eq_diag_add_pairSet (fun p : Fin (n + 1) × Fin (n + 1) =>
              ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                ‖aPC ℓ p.1 (aPC ℓ p.2 Θ) x‖ ^ 2)
        _ = (∑ i : Fin (n + 1),
              ∫ x in Submission.BoseGases.abox (n + 1) ℓ, ‖aPC ℓ i Θ x‖ ^ 2)
            + ∑ p ∈ Submission.BoseGases.pairSet (n + 1),
                ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                  ‖aPC ℓ p.1 (aPC ℓ p.2 Θ) x‖ ^ 2 := by rw [hdiag]
    -- ## 1. the two slot sums agree a.e. on the box
    have hae : (fun x => ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          uSlot (e 0) i (uSlot (e 0) j Θ) x)
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)]
          (fun x => ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), aPC ℓ i (aPC ℓ j Θ) x) := by
      have h1 : ∀ i j : Fin (n + 1),
          (fun x => uSlot (e 0) i (uSlot (e 0) j Θ) x)
            =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)]
              (fun x => aPC ℓ i (aPC ℓ j Θ) x) := by
        intro i j
        exact (uSlot_ae_eq_aPC hℓ i hun hcc).trans
          (aPC_congr_ae_box i (uSlot_ae_eq_aPC hℓ j hun hcc))
      filter_upwards [Filter.eventually_all.mpr
        (fun i => Filter.eventually_all.mpr (fun j => h1 i j))] with x hx
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hx i j))
    -- ## 2. transfer to the slot means
    have hcIPn : Work.BoseDict.cIPn (n + 1) Θ
          (fun x => ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            uSlot (e 0) i (uSlot (e 0) j Θ) x)
        = Work.BoseDict.cIPn (n + 1) Θ
          (fun x => ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), aPC ℓ i (aPC ℓ j Θ) x) := by
      rw [Work.BoseDict.cIPn, Work.BoseDict.cIPn]
      refine MeasureTheory.integral_congr_ae ?_
      have hbox : ∀ᵐ x ∂(MeasureTheory.volume :
            MeasureTheory.Measure (Work.BoseDict.Xn (n + 1))),
          x ∈ Submission.BoseGases.abox (n + 1) ℓ →
            (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), uSlot (e 0) i (uSlot (e 0) j Θ) x)
              = (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), aPC ℓ i (aPC ℓ j Θ) x) :=
        (MeasureTheory.ae_restrict_iff'
          (Submission.BoseGases.abox_measurable (n + 1) ℓ)).mp hae
      filter_upwards [hbox] with x hx
      by_cases hxA : x ∈ Submission.BoseGases.abox (n + 1) ℓ
      · rw [hx hxA]
      · have hΘ0 : Θ x = 0 := by
          by_contra h
          exact hxA (hΘs (Function.mem_support.mpr h))
        rw [hΘ0, map_zero, zero_mul, zero_mul]
    -- ## 3. the box integral
    have hsetint : Work.BoseDict.cIPn (n + 1) Θ
          (fun x => ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), aPC ℓ i (aPC ℓ j Θ) x)
        = ∫ x in Submission.BoseGases.abox (n + 1) ℓ, (starRingEnd ℂ) (Θ x)
            * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), aPC ℓ i (aPC ℓ j Θ) x) := by
      rw [Work.BoseDict.cIPn]
      exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        have hΘ0 : Θ x = 0 := by
          by_contra h
          exact hx (hΘs (Function.mem_support.mpr h))
        rw [hΘ0, map_zero, zero_mul])).symm
    -- ## 4. expand the double sum inside the integral
    have hexp : (∫ x in Submission.BoseGases.abox (n + 1) ℓ, (starRingEnd ℂ) (Θ x)
          * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), aPC ℓ i (aPC ℓ j Θ) x))
        = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (starRingEnd ℂ) (Θ x) * aPC ℓ i (aPC ℓ j Θ) x := by
      rw [show (fun x => (starRingEnd ℂ) (Θ x)
            * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), aPC ℓ i (aPC ℓ j Θ) x))
          = fun x => ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              (starRingEnd ℂ) (Θ x) * aPC ℓ i (aPC ℓ j Θ) x from by
        funext x
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])]
      refine (MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin (n + 1)))
        (f := fun i x => ∑ j : Fin (n + 1),
          (starRingEnd ℂ) (Θ x) * aPC ℓ i (aPC ℓ j Θ) x)
        (fun i _ => MeasureTheory.integrable_finsetSum _
          (fun j _ => (hpair i j).1))).trans ?_
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact MeasureTheory.integral_finsetSum (Finset.univ : Finset (Fin (n + 1)))
        (f := fun j x => (starRingEnd ℂ) (Θ x) * aPC ℓ i (aPC ℓ j Θ) x)
        (fun j _ => (hpair i j).1)
    -- ## 5. take real parts
    have hre : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (starRingEnd ℂ) (Θ x) * aPC ℓ i (aPC ℓ j Θ) x).re
        = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              ‖aPC ℓ i (aPC ℓ j Θ) x‖ ^ 2 := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [(hpair i j).2, Complex.ofReal_re]
    -- ## 6. assembly
    rw [hcIPn, hsetint, hexp, hre, hcomb, cS1C, cS2C]

end Work.BoseBoxFock
