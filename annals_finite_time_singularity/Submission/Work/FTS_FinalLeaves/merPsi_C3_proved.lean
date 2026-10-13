import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice
import Submission.Work.FTS.Physical.Clock.clockInv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `C³` regularity of the meridian slice of the reconstruction's stream function

`merPsi α A B Φ C r z t = ρ(r,z)² · A(τ)⁻¹ · Φ(ρ(r,z)^α/B(τ), θ(r,z), τ)`, `τ = clockInv C t`,
with `Φ = psiFire Φs E g` the **odd extension in `θ`** of the canonical stream function `PsiCan`.

This is the `C³` companion of `BSIdent.Defs.contDiffAt_merPsi_slice` (which is stated for the `C²`
class and applies the odd extension *inside* `merPsi`).  Here the odd extension is already part of
the profile, so the argument is the same branch analysis plus one extra differentiation order:

* off the degenerate set (`r > 0`, `z ≠ 0`) the angle `θ(r,z) = arctan(z/r)` is nonzero, and the
  sign of `θ` is constant near `(r,z)`;
* on the branch `θ > 0` the profile is `PsiCan` itself (`psiFire_of_pos`);
* on the branch `θ < 0` it is `θ ↦ -PsiCan(·, -θ)` with `-θ > 0` (`psiFire_of_neg`);
* in both cases the polar dictionary `(r,z) ↦ (ρ^α/B(τ), ±θ(r,z))` is `C³` at `(r,z)` (only
  `r > 0` is needed), so the composition with the `C³` hypothesis on `PsiCan` applies.
-/

open Filter Set
open scoped Topology

namespace Work.FTS_FinalLeaves

/-- Unfolding of `Work.FTS.MeridianDyn.merPsi` at a point (definitional). -/
private lemma merPsi_apply' (p : ℝ) (A B : ℝ → ℝ) (Φ : Work.FTS.Galerkin.Fam)
    (C : Work.FTS.Physical.PhysClock) (r z t : ℝ) :
    Work.FTS.MeridianDyn.merPsi p A B Φ C r z t
      = Work.Cyl.rhoP r z ^ 2 * (A (Work.FTS.Physical.clockInv C t))⁻¹
        * Φ (Work.Cyl.rhoP r z ^ p / B (Work.FTS.Physical.clockInv C t))
            (Work.Cyl.thetaP r z) (Work.FTS.Physical.clockInv C t) := rfl

/-- The **negative-angle branch** of `psiFire`: for `θ < 0` the odd extension reads
`-PsiCan (·, -θ)` (the cut `psiCut` is inactive because `-θ > 0`). -/
private lemma psiFire_of_neg {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {z θ τ : ℝ} (hθ : θ < 0) :
    Work.FTS.FinalV2.psiFire Φs E g z θ τ = - Work.FTS.Nonlin.PsiCan Φs E g z (-θ) τ := by
  simp only [Work.FTS.FinalV2.psiFire, Work.FTS.BSIdent.PhiOdd, Work.FTS.FinalV2.psiCut,
    if_neg (not_le.mpr hθ), if_pos (neg_pos.mpr hθ)]

/-- The polar dictionary is `C³` at every point of the half-plane `r > 0`: the radius
`ρ(r,z) = √(r²+z²)`, the self-similar argument `ρ^p/b` and the angle `θ(r,z) = arctan(z/r)`,
together with the geometric prefactor `ρ²`. -/
private lemma contDiffAt_polar (p b : ℝ) {r z : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ 3 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ 2) (r, z) ∧
    ContDiffAt ℝ 3 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ p / b) (r, z) ∧
    ContDiffAt ℝ 3 (fun q : ℝ × ℝ => Work.Cyl.thetaP q.1 q.2) (r, z) := by
  have hρ : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2) (r, z) := by
    have h1 : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r, z) := by fun_prop
    have h2 : (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r, z) ≠ 0 := by
      show r ^ 2 + z ^ 2 ≠ 0
      positivity
    have h3 := (Real.contDiffAt_sqrt (n := 3) h2).comp (r, z) h1
    simpa [Work.Cyl.rhoP, Function.comp_def] using h3
  refine ⟨?_, ?_, ?_⟩
  · simpa using hρ.pow 2
  · have h4 := hρ.rpow_const_of_ne (p := p) (Work.Cyl.rhoP_ne_zero hr z)
    simpa [div_eq_mul_inv] using
      h4.mul (contDiffAt_const (c := b⁻¹) :
        ContDiffAt ℝ 3 (fun _ : ℝ × ℝ => b⁻¹) (r, z))
  · have h1 : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => q.2 / q.1) (r, z) := by
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · simpa using hr.ne'
    have h3 := Real.contDiff_arctan.contDiffAt.comp (r, z) h1
    simpa [Work.Cyl.thetaP, Function.comp_def] using h3

theorem merPsi_C3_proved {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {A B : ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hC3 : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 3 (fun q : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g q.1 q.2 τ)
        Work.Construction.Qd)
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ) :
    ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      ContDiffAt ℝ 3 (fun p : ℝ × ℝ =>
        Work.FTS.MeridianDyn.merPsi α A B (Work.FTS.FinalV2.psiFire Φs E g) C p.1 p.2 t)
        (r, z) := by
  intro t ht r z hr hz
  -- the clock value and the hypotheses it feeds
  have hτ : 0 ≤ Work.FTS.Physical.clockInv C t :=
    Work.FTS.Physical.clockInv_nonneg C ⟨ht.1.le, ht.2⟩
  have hBτ : 0 < B (Work.FTS.Physical.clockInv C t) := hB _ hτ
  have hΨ := hC3 _ hτ
  -- the polar dictionary at `(r,z)`
  obtain ⟨hρ2, hρp, hθ⟩ := contDiffAt_polar α (B (Work.FTS.Physical.clockInv C t)) hr
  -- the self-similar argument is positive, the angle is non-zero and `< π/2`
  have hw : 0 < Work.Cyl.rhoP r z ^ α / B (Work.FTS.Physical.clockInv C t) :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hBτ
  have hθ0 : Work.Cyl.thetaP r z ≠ 0 := by
    simp only [Work.Cyl.thetaP]
    exact fun h => (div_ne_zero hz hr.ne') (Real.arctan_eq_zero_iff.mp h)
  have hθlt : Work.Cyl.thetaP r z < Real.pi / 2 := by
    simpa only [Work.Cyl.thetaP] using Real.arctan_lt_pi_div_two (z / r)
  have hθgt : -(Real.pi / 2) < Work.Cyl.thetaP r z := by
    simpa only [Work.Cyl.thetaP] using Real.neg_pi_div_two_lt_arctan (z / r)
  have hQd : Work.Construction.Qd = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := rfl
  rcases lt_or_gt_of_ne hθ0 with hneg | hpos
  · -- ### branch `θ(r,z) < 0`: the profile is `(w,φ) ↦ -PsiCan (w,-φ)`
    have hbase : ContDiffAt ℝ 3
        (fun p : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g p.1 p.2
          (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ α / B (Work.FTS.Physical.clockInv C t),
          -Work.Cyl.thetaP r z) :=
      hΨ.contDiffAt (by
        rw [hQd]
        exact (isOpen_Ioi.prod isOpen_Ioo).mem_nhds
          ⟨hw, by linarith, by linarith⟩)
    have hcomp : ContDiffAt ℝ 3 (fun q : ℝ × ℝ =>
        Work.FTS.Nonlin.PsiCan Φs E g
          (Work.Cyl.rhoP q.1 q.2 ^ α / B (Work.FTS.Physical.clockInv C t))
          (-(Work.Cyl.thetaP q.1 q.2)) (Work.FTS.Physical.clockInv C t)) (r, z) := by
      have h := hbase.comp (r, z) (hρp.prodMk hθ.neg)
      simpa [Function.comp_def] using h
    have hfinal : ContDiffAt ℝ 3 (fun q : ℝ × ℝ =>
        Work.Cyl.rhoP q.1 q.2 ^ 2 * (A (Work.FTS.Physical.clockInv C t))⁻¹ *
          -(Work.FTS.Nonlin.PsiCan Φs E g
            (Work.Cyl.rhoP q.1 q.2 ^ α / B (Work.FTS.Physical.clockInv C t))
            (-(Work.Cyl.thetaP q.1 q.2)) (Work.FTS.Physical.clockInv C t))) (r, z) :=
      (hρ2.mul (contDiffAt_const (c := (A (Work.FTS.Physical.clockInv C t))⁻¹) :
        ContDiffAt ℝ 3 (fun _ : ℝ × ℝ => (A (Work.FTS.Physical.clockInv C t))⁻¹)
          (r, z))).mul hcomp.neg
    refine hfinal.congr_of_eventuallyEq ?_
    have hnb : {q : ℝ × ℝ | Work.Cyl.thetaP q.1 q.2 < 0} ∈ 𝓝 (r, z) :=
      hθ.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hneg)
    filter_upwards [hnb] with q hq
    rw [merPsi_apply', psiFire_of_neg hq]
  · -- ### branch `0 < θ(r,z)`: the profile is `PsiCan` itself
    have hbase : ContDiffAt ℝ 3
        (fun p : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g p.1 p.2
          (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ α / B (Work.FTS.Physical.clockInv C t),
          Work.Cyl.thetaP r z) :=
      hΨ.contDiffAt (by
        rw [hQd]
        exact (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hw, hpos, hθlt⟩)
    have hcomp : ContDiffAt ℝ 3 (fun q : ℝ × ℝ =>
        Work.FTS.Nonlin.PsiCan Φs E g
          (Work.Cyl.rhoP q.1 q.2 ^ α / B (Work.FTS.Physical.clockInv C t))
          (Work.Cyl.thetaP q.1 q.2) (Work.FTS.Physical.clockInv C t)) (r, z) := by
      have h := hbase.comp (r, z) (hρp.prodMk hθ)
      simpa [Function.comp_def] using h
    have hfinal : ContDiffAt ℝ 3 (fun q : ℝ × ℝ =>
        Work.Cyl.rhoP q.1 q.2 ^ 2 * (A (Work.FTS.Physical.clockInv C t))⁻¹ *
          Work.FTS.Nonlin.PsiCan Φs E g
            (Work.Cyl.rhoP q.1 q.2 ^ α / B (Work.FTS.Physical.clockInv C t))
            (Work.Cyl.thetaP q.1 q.2) (Work.FTS.Physical.clockInv C t)) (r, z) :=
      (hρ2.mul (contDiffAt_const (c := (A (Work.FTS.Physical.clockInv C t))⁻¹) :
        ContDiffAt ℝ 3 (fun _ : ℝ × ℝ => (A (Work.FTS.Physical.clockInv C t))⁻¹)
          (r, z))).mul hcomp
    refine hfinal.congr_of_eventuallyEq ?_
    have hnb : {q : ℝ × ℝ | 0 < Work.Cyl.thetaP q.1 q.2} ∈ 𝓝 (r, z) :=
      hθ.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hpos)
    filter_upwards [hnb] with q hq
    rw [merPsi_apply', Work.FTS.FinalV2.psiFire_of_pos hq]

end Work.FTS_FinalLeaves
