import Mathlib
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.HeteroGerm
import Submission.Work.EQ.HeteroChain
import Submission.Work.EQ.HeteroR
import Submission.Work.EQ.HeteroRit
import Submission.Work.EQ.fwdC_germC
import Submission.Work.EQ.germC_y_inverse
import Submission.Work.EQ.germC_facts

/-! ## The chain of `R`-iterates of the germ point and its real meaning -/

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

variable {a : ℝ} {h : ℂ → ℂ} {r : ℝ} {Γ : ℝ → ℂ}

/-- On real arguments the iterated backward branch map is the real connection. -/
theorem Rk_real (ha0 : 0 < a) (ha1 : a < 1) (hh : IsStableGerm a h r)
    (hΓ : IsHeteroclinic a h r Γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (j : ℕ) (t : ℝ), 0 < t → t < δ →
      Rk a h j t = Rpt (Γ ((eqLam a)⁻¹ ^ j * t)) := by
  obtain ⟨δ₁, hδ₁, hδne⟩ := h_lam_ne ha0 ha1 hh
  obtain ⟨hr, han, h0, hderiv, hreal, hFE⟩ := hh
  obtain ⟨-, _, him, hfun, ⟨ε, hε, hgerm⟩, -⟩ := hΓ
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlamne : eqLam a ≠ 0 := ne_of_gt hlam0
  refine ⟨min (min ε r) δ₁, by positivity, fun j t ht htd => ?_⟩
  have htε : t < ε := lt_of_lt_of_le htd (le_trans (min_le_left _ _) (min_le_left _ _))
  have htr : t < r := lt_of_lt_of_le htd (le_trans (min_le_left _ _) (min_le_right _ _))
  have htd' : t < δ₁ := lt_of_lt_of_le htd (min_le_right _ _)
  have hreal_t : (h (t : ℂ)).im = 0 := hreal t (by rw [abs_of_pos ht]; exact htr)
  have hreal_lt : (h ((eqLam a : ℂ) * (t : ℂ))).im = 0 := by
    have h := hreal (eqLam a * t) (by
      rw [abs_of_pos (by positivity)]
      calc eqLam a * t < eqLam a * r := mul_lt_mul_of_pos_left htr hlam0
        _ < r := by nlinarith [hr, hlam1])
    simpa [Complex.ofReal_mul] using h
  have hden : h ((eqLam a : ℂ) * (t : ℂ)) ≠ h (t : ℂ) := by
    simpa [Complex.ofReal_mul] using hδne t ht htd'
  have hbase : Rk a h 0 t = Rpt (Γ t) := by
    rw [Rk_zero, germC_real (a := a) (h := h) h0 (ne_of_gt ht) hreal_t hreal_lt hden,
      hgerm t ht htε]
  induction j with
  | zero => simpa using hbase
  | succ j ih =>
      have hpos : 0 < (eqLam a)⁻¹ ^ j * t := by positivity
      have hstep := gamma_backward_step (a := a) (h := h) (r := r) (Γ := Γ) hlam0 hlamne
        hfun him ((eqLam a)⁻¹ ^ j * t) hpos
      rw [Rk_succ, ih, ← hstep]
      congr 1
      rw [pow_succ']
      ring

end

end Work.EQ
