/-
# `ModalSol/Defs` — the modal weak solution of `bslOp α Ψ = F` as the limit of its partial sums

The solution constructed in `ModalSol/weakSolExists_slice.lean` is the mode series

  `Ψ(z,θ) = Σ_m acoeff α m F z · eFam m θ`,   `acoeff α m F = radGreen α m (cmode m F)`,

taken as the limit of its partial sums `psiTrunc α F N`.  Because that convergence is only
established later (from the tail bounds `ModalSol/TailBound/psiTrunc_tail`), the witness is
defined here as the infimum of the (at most singleton) set of limits of the partial sums,

  `Psi α F z θ = sInf {l | Tendsto (fun N => psiTrunc α F N z θ) atTop (nhds l)}`,

a total definition which needs no decidability and is the actual limit wherever the partial sums
converge.  The identifying property is recorded in `Psi_eq_of_tendsto`, from which everything
downstream is derived.

* `Psi_eq_of_tendsto` / `Psi_tendsto_of_cauchy`: the two forms in which the identifying property
  of the limit is used downstream;
* `psiTrunc_apply_zero`, `psiTrunc_apply_pi_half` and their limit versions `Psi_apply_zero`,
  `Psi_apply_pi_half`: the Dirichlet *values* of the witness, which are free because
  `eFam m 0 = eFam m (π/2) = 0` for every `m`;
* `exists_box_of_isCompact_subset_Q0`: a nonempty compact subset of the open quadrant is
  contained in a closed rectangle inside it.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSol

set_option autoImplicit false

/-! ## The witness of the existence statement -/

/-- **The modal weak solution**: the limit of the partial sums of the mode series
`Σ_m acoeff α m F z · eFam m θ` (with the junk value `sInf ∅ = 0` where the limit does not
exist — on the open quadrant it always does). -/
def Psi (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  sInf {l : ℝ | Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)
    Filter.atTop (nhds l)}

/-- The defining property of `Psi`: a converging sequence of partial sums has `Psi` as its
limit. -/
theorem Psi_eq_of_tendsto {α : ℝ} {F : ℝ → ℝ → ℝ} {z θ l : ℝ}
    (hl : Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)
      Filter.atTop (nhds l)) : Psi α F z θ = l := by
  have hset : {l' : ℝ | Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)
      Filter.atTop (nhds l')} = {l} := by
    ext l'
    constructor
    · intro h'
      exact tendsto_nhds_unique h' hl
    · intro h'
      rw [Set.mem_singleton_iff] at h'
      rw [h']
      exact hl
  rw [Psi, hset, csInf_singleton]

/-- From the Cauchy property of the partial sums, `Psi` is their limit. -/
theorem Psi_tendsto_of_cauchy {α : ℝ} {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hC : CauchySeq (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)) :
    Filter.Tendsto (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z θ)
      Filter.atTop (nhds (Psi α F z θ)) := by
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hC
  rw [Psi_eq_of_tendsto hl]
  exact hl

/-! ## The Dirichlet values -/

/-- The angular modes vanish at `θ = 0`. -/
theorem psiTrunc_apply_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ) (z : ℝ) :
    Work.FTS.PhiStar.Series.psiTrunc α F N z 0 = 0 := by
  rw [Work.FTS.PhiStar.Series.psiTrunc, Finset.sum_eq_zero]
  intro m _
  have h3 : Work.FTS.PhiStar.Gegenbauer.eFam m 0 = 0 := by
    have h4 : Work.FTS.PhiStar.Gegenbauer.eFam m 0
        = Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) 0 := by
      simp [Work.FTS.PhiStar.Gegenbauer.eFam]
    rw [h4, Work.FTS.PhiStar.Gegenbauer.gC_odd_zero]
  rw [h3, mul_zero]

/-- The angular modes vanish at `θ = π/2`. -/
theorem psiTrunc_apply_pi_half (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ) (z : ℝ) :
    Work.FTS.PhiStar.Series.psiTrunc α F N z (π / 2) = 0 := by
  rw [Work.FTS.PhiStar.Series.psiTrunc, Finset.sum_eq_zero]
  intro m _
  have h3 : Work.FTS.PhiStar.Gegenbauer.eFam m (π / 2) = 0 := by
    simp [Work.FTS.PhiStar.Gegenbauer.eFam]
  rw [h3, mul_zero]

/-- `Psi` vanishes at `θ = 0` (for every `z`). -/
theorem Psi_apply_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : Psi α F z 0 = 0 := by
  refine Psi_eq_of_tendsto ?_
  have h : (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z 0) = fun _ => (0 : ℝ) :=
    funext (fun N => psiTrunc_apply_zero α F N z)
  rw [h]
  exact tendsto_const_nhds

/-- `Psi` vanishes at `θ = π/2` (for every `z`). -/
theorem Psi_apply_pi_half (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) : Psi α F z (π / 2) = 0 := by
  refine Psi_eq_of_tendsto ?_
  have h : (fun N : ℕ => Work.FTS.PhiStar.Series.psiTrunc α F N z (π / 2)) = fun _ => (0 : ℝ) :=
    funext (fun N => psiTrunc_apply_pi_half α F N z)
  rw [h]
  exact tendsto_const_nhds

/-! ## A box around a compact subset of the quadrant -/

/-- A nonempty compact subset of the open quadrant is contained in a product of closed
intervals which is itself contained in the open quadrant. -/
theorem exists_box_of_isCompact_subset_Q0 {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hne : K.Nonempty) (hsub : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b c d : ℝ, 0 < a ∧ a ≤ b ∧ 0 < c ∧ c ≤ d ∧ d < π / 2 ∧
      K ⊆ Set.Icc a b ×ˢ Set.Icc c d := by
  have hfst : ∀ p ∈ K, (0 : ℝ) < p.1 := fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp (hsub hp)).1
  have hsnd0 : ∀ p ∈ K, (0 : ℝ) < p.2 :=
    fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp (hsub hp)).2.1
  have hsnd1 : ∀ p ∈ K, p.2 < π / 2 :=
    fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp (hsub hp)).2.2
  obtain ⟨a, ha0, ha⟩ := hK.exists_forall_le' continuous_fst.continuousOn hfst
  obtain ⟨c, hc0, hc⟩ := hK.exists_forall_le' continuous_snd.continuousOn hsnd0
  obtain ⟨pz, hpzK, hpzg⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
  obtain ⟨pθ, hpθK, hpθg⟩ := hK.exists_isMaxOn hne continuous_snd.continuousOn
  obtain ⟨p, hpK⟩ := hne
  refine ⟨a, pz.1, c, pθ.2, ha0, ha pz hpzK, hc0, hc pθ hpθK,
    lt_of_le_of_lt (hpθg hpθK) (hsnd1 pθ hpθK), ?_⟩
  intro q hq
  exact ⟨⟨ha q hq, hpzg hq⟩, ⟨hc q hq, hpθg hq⟩⟩

end Work.FTS.H2.ModalSol
