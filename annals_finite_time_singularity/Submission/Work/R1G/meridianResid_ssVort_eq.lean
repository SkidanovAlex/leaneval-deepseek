import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.R1G.Defs
import Submission.Work.CoreResiduals.meridianEq_of_dynEqConst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.R1G

/-- **The pointwise meridian residual identity for the self-similar pair.**

Let `W = ssVort p λ F`, `ψ = ssPsi p λ Φ` be the self-similar vorticity/stream-function pair at a
modulation `λ` with `λ(t) > 0` and `λ'(t) = -κ`.  Then at `r > 0`, `z > 0`, `t > 0`, the meridian
residual (`Work.CoreResiduals.meridianResid`) is

  `(2 λ(t)²)⁻¹ · ( 2κ·(F + D_z F) + UVR p F Φ )`  at `(Z,Θ) = (ρ(r,z)^p/λ(t), arctan(z/r))`.

This is the exact chain-rule/algebra identity underlying
`Work.CoreResiduals.meridianEq_of_dynEqConst`, here stated as an equality rather than as a
vanishing criterion; the bracket is precisely the profile residual at the effective rate `2κ`
(`Work.R1G.profileResidGen`). -/
theorem meridianResid_ssVort_eq {p κ : ℝ} (hp : 0 < p) {lam : ℝ → ℝ} {F Φ : ℝ → ℝ → ℝ}
    {r z t : ℝ} (hr : 0 < r) (hz : 0 < z) (ht : 0 < t)
    (hlam : 0 < lam t) (hder : HasDerivAt lam (-κ) t)
    (hF : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => F q.1 q.2)
      (Work.Cyl.rhoP r z ^ p / lam t, Work.Cyl.thetaP r z))
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2)
      (Work.Cyl.rhoP r z ^ p / lam t, Work.Cyl.thetaP r z)) :
    Work.CoreResiduals.meridianResid (Work.CoreResiduals.ssVort p lam F)
        (Work.CoreResiduals.ssPsi p lam Φ) r z t
      = (2 * (lam t) ^ 2)⁻¹ *
          (2 * κ * (F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
              + Work.Spaces.Dz F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
            + Work.Construction.UVR p F Φ (Work.Cyl.rhoP r z ^ p / lam t)
                (Work.Cyl.thetaP r z)) := by
  have hlam_ne : lam t ≠ 0 := ne_of_gt hlam
  have hρpos : 0 < Work.Cyl.rhoP r z := Work.Cyl.rhoP_pos hr z
  have hρne : Work.Cyl.rhoP r z ≠ 0 := ne_of_gt hρpos
  have hρsq : Work.Cyl.rhoP r z ^ 2 = r ^ 2 + z ^ 2 := Work.Cyl.rhoP_sq r z
  have hrz : r ^ 2 + z ^ 2 ≠ 0 := by positivity
  have hFd : Work.Cyl.DiffAt2 F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z) :=
    hF.differentiableAt (by norm_num)
  have hΦd : Work.Cyl.DiffAt2 Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z) :=
    hΦ.differentiableAt (by norm_num)
  have htan : Real.tan (Work.Cyl.thetaP r z) = z / r :=
    Work.CoreResiduals.tan_thetaP_eq r z hr
  have hUVR := Work.CoreResiduals.UVR_polar_expand p r z (Work.Cyl.rhoP r z) F Φ
      (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
      (ne_of_gt hr) hρne (Work.Cyl.sin_thetaP hr z) (Work.Cyl.cos_thetaP hr z) htan
  have halg := Work.CoreResiduals.meridianResid_algebra (p := p) (κ := κ) (r := r) (z := z)
      (ρsq := Work.Cyl.rhoP r z ^ 2) (Z := Work.Cyl.rhoP r z ^ p / lam t)
      (f := F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      (f1 := Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      (f2 := Work.Cyl.pdZ F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      (g := Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      (g1 := Work.Cyl.pdR Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      (g2 := Work.Cyl.pdZ Φ (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z))
      (lam := lam t) (ne_of_gt hr) hlam_ne hrz hρsq
  have hDz : Work.Spaces.Dz F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z)
      = (Work.Cyl.rhoP r z ^ p / lam t)
          * Work.Cyl.pdR F (Work.Cyl.rhoP r z ^ p / lam t) (Work.Cyl.thetaP r z) := rfl
  unfold Work.CoreResiduals.meridianResid
  rw [Work.CoreResiduals.timeDeriv_ssVort_lam hlam_ne hder hFd,
      Work.CoreResiduals.pdZ_ssPsi_lam hr hlam_ne hΦd,
      Work.CoreResiduals.pdR_ssVort_lam hr hlam_ne hFd,
      Work.CoreResiduals.pdR_ssPsi_lam hr hlam_ne hΦd,
      Work.CoreResiduals.pdZ_ssVort_lam hr hlam_ne hFd]
  simp only [Work.CoreResiduals.ssVort, Work.CoreResiduals.ssPsi]
  rw [halg]
  rw [← hUVR]
  rw [hDz]

end Work.R1G
