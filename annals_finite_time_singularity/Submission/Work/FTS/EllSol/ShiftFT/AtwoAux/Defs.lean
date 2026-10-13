import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs
import Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Cutoff
import Submission.Work.FTS.EllSol.Trunc.chiMulDerivs
import Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false


/-- `L_b u = ∂_t u - b·u`. -/
def uTrAtwo_L1 (b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t θ => Work.Spaces.pz u t θ - b * u t θ

/-- `L_b² u = ∂_t² u - 2b·∂_t u + b²·u`. -/
def uTrAtwo_L2 (b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t θ => Work.Spaces.pz (Work.Spaces.pz u) t θ - 2 * b * Work.Spaces.pz u t θ
    + b ^ 2 * u t θ

/-- The pointwise expression for `L_b² (phiTr N · Gc N b u)` on the strip, obtained from the
two derivative identities of `Aux2.gcDeriv`. -/
def uTrAtwo_W (N b : ℝ) (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  phiTr N p.1 * Work.FTS.EllSol.Trunc.chi N p.1 * uTrAtwo_L2 b u p.1 p.2
    + (phiTr N p.1 * deriv (Work.FTS.EllSol.Trunc.chi N) p.1
        + 2 * deriv (phiTr N) p.1 * Work.FTS.EllSol.Trunc.chi N p.1) * uTrAtwo_L1 b u p.1 p.2
    + deriv (deriv (phiTr N)) p.1 * Gc N b u p.1 p.2

/-- The pointwise identity `L_b² (uTr N b u) = W` on the open strip. -/
theorem uTr_L2_eq (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      uTrAtwo_L2 b (uTr N b u) t θ = uTrAtwo_W N b u (t, θ) := by
  intro t θ hθ
  have hd1 : Differentiable ℝ (fun s => Gc N b u s θ) := (Aux2.gcDeriv N b u hu).2.2.1 θ hθ
  have hd2 : Differentiable ℝ (fun s => Work.Spaces.pz (Gc N b u) s θ) :=
    (Aux2.gcDeriv N b u hu).2.2.2 θ hθ
  have hphi : Differentiable ℝ (phiTr N) := (phiTr_contDiff 1 N).differentiable (by norm_num)
  have hphi1 : Differentiable ℝ (deriv (phiTr N)) :=
    (phiTr_contDiff 2 N).differentiable_deriv_two
  have key : Work.Spaces.pz (Work.Spaces.pz (uTr N b u)) t θ
      = deriv (deriv (phiTr N)) t * Gc N b u t θ
        + 2 * deriv (phiTr N) t * Work.Spaces.pz (Gc N b u) t θ
        + phiTr N t * Work.Spaces.pz (Work.Spaces.pz (Gc N b u)) t θ :=
    Work.FTS.EllSol.Trunc.pz_pz_mul_slice (phiTr N) (Gc N b u) t θ hphi hphi1 hd1 hd2
  have key1 : Work.Spaces.pz (uTr N b u) t θ
      = deriv (phiTr N) t * Gc N b u t θ + phiTr N t * Work.Spaces.pz (Gc N b u) t θ :=
    Work.FTS.EllSol.Trunc.pz_mul_slice (phiTr N) (Gc N b u) t θ (hphi t) (hd1 t)
  rw [uTrAtwo_L2, uTrAtwo_W, uTrAtwo_L1, key, key1,
    (Aux2.gcDeriv N b u hu).1 t θ hθ, (Aux2.gcDeriv N b u hu).2.1 t θ hθ]
  simp only [uTrAtwo_L2, uTr]
  ring


/-- The a.e. version of `uTr_L2_eq` on the strip `ℝ × Iθ`. -/
theorem ae_uTr_L2_eq (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (fun p : ℝ × ℝ => uTrAtwo_L2 b (uTr N b u) p.1 p.2)
      =ᵐ[volume.restrict ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ)]
      (fun p : ℝ × ℝ => uTrAtwo_W N b u p) := by
  filter_upwards [ae_mem_Ioo_of_Iθ] with p hp
  exact uTr_L2_eq N b u hu p.1 p.2 hp

end

end Work.FTS.EllSol.ShiftFT
