/-
# `Work.FTS.Final.Recon.diffAt2_merProfile`

The meridian profile of the reconstructed vorticity,
`merProfile α A B g C r z t = A(τ)⁻¹ · F(ρ(r,z)^{3α}/B(τ), θ(r,z))`, `τ = clockInv C t`, is
**differentiable in `(r,z)`** at every point with `r > 0` (and `z ≠ 0`), provided the profile
family is `C⁴` in the self-similar variables on the open quadrant.

The mathematical content is the chain rule for the polar dictionary
`(r,z) ↦ (ρ(r,z)^{3α}/B(τ), θ(r,z))` (smooth off the axis `r > 0`, `θ = arctan(z/r)`) together
with the *interior* regularity of the odd extension `F = F_* + g` of the profile in the angle
`θ`: at a point with `θ(r,z) ≠ 0` (which is what `z ≠ 0` gives, since `r > 0`) the sign of `θ` is
constant on a neighbourhood, so the pointwise `if 0 ≤ θ` in `ConstructionInstance.profile` is
resolved and one is looking at `F_*(z,±θ) + g(z,±θ)` there.

The route follows the `C²` statement `Work.FTS.BSIdent.Defs.contDiffAt_merPsi_slice` for the
stream function (the same polar dictionary, the same odd-extension case split).

All the material below is `sorry`-free.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Final.Defs
import Submission.Work.FTS.Physical.Meridian

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter Set

namespace Work.FTS.Final.Recon

/-! ## The two ingredients of the profile `F = F_* + g` -/

/-- The singular profile `F_*(z,θ) = α·(Γ(θ)/c(α))·(2z/(1+z)²)` is `C²` at every point with
`z > 0` and `0 < θ < π/2`: the angular factor `Γ(θ) = (sinθ·cos²θ)^{α/3}` is a real power of a
strictly positive `C²` function there (`Real.contDiffAt_rpow_const`), and
`z ↦ 2z/(1+z)²` is `C²` at `z > 0` (its pole sits at `z = -1`). -/
lemma contDiffAt_Fstar₂ (p : ℝ) {Z Θ : ℝ} (hZ : 0 < Z) (hΘ : 0 < Θ) (hΘ1 : Θ < Real.pi / 2) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2) (Z, Θ) := by
  have hbase : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Real.sin q.2 * Real.cos q.2 ^ 2) (Z, Θ) := by
    fun_prop
  have hne : Real.sin Θ * Real.cos Θ ^ 2 ≠ 0 := by
    have h1 : 0 < Real.sin Θ := Real.sin_pos_of_pos_of_lt_pi hΘ (by linarith [hΘ1, Real.pi_pos])
    have h2 : 0 < Real.cos Θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hΘ, Real.pi_pos], hΘ1⟩
    positivity
  have hG' := (Real.contDiffAt_rpow_const (x := Real.sin Θ * Real.cos Θ ^ 2) (p := p / 3)
    (n := 2) (Or.inl hne)).comp (Z, Θ) hbase
  have hG : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Spaces.Gam p q.2) (Z, Θ) := by
    simpa [Work.Spaces.Gam, Function.comp_def] using hG'
  have hz : ContDiffAt ℝ 2 (fun z : ℝ => Work.FM.Fstar z) Z := by
    change ContDiffAt ℝ 2 (fun z : ℝ => 2 * z / (1 + z) ^ 2) Z
    fun_prop (disch := positivity)
  have hproj : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1) (Z, Θ) := by fun_prop
  have hF : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.FM.Fstar q.1) (Z, Θ) := by
    have := hz.comp (Z, Θ) hproj
    simpa [Function.comp_def] using this
  exact ((contDiffAt_const (c := p)).mul (hG.div_const (Work.Spaces.c p))).mul hF

/-- **Regularity of the odd extension of the profile in the angle, away from `θ = 0`.**

If the random part `gs` is `C²` at `(Z,|Θ|)`, then the odd extension
`profile p gs = if 0 ≤ θ then F_* + gs else -(F_*(·,-θ) + gs(·,-θ))` is `C²` at `(Z,Θ)` for every
`Z > 0` and `0 < |Θ| < π/2`.

At such a point the sign of the angle is locally constant, so the pointwise `if` reduces to one of
its two branches, and each branch is `C²` by `contDiffAt_Fstar₂` (evaluated at the angle `|Θ|`) and
the hypothesis on `gs`, composed with the smooth reflection `(Z,Θ) ↦ (Z,-Θ)` in the negative
case. -/
lemma contDiffAt_profile_of_ne {p : ℝ} {gs : ℝ → ℝ → ℝ} {Z Θ : ℝ}
    (hZ : 0 < Z) (hΘ : Θ ≠ 0) (hΘlo : -(Real.pi / 2) < Θ) (hΘhi : Θ < Real.pi / 2)
    (hgs : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => gs q.1 q.2) (Z, |Θ|)) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.ConstructionInstance.profile p gs q.1 q.2) (Z, Θ) := by
  have hflip : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (q.1, -q.2)) (Z, Θ) := by fun_prop
  rcases lt_trichotomy Θ 0 with hneg | hzero | hpos
  · -- the branch `θ < 0`: the profile is `-(F_*(·,-θ) + gs(·,-θ))`
    rw [abs_of_neg hneg] at hgs
    have hg : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => gs q.1 (-q.2)) (Z, Θ) := by
      have := hgs.comp (Z, Θ) hflip
      simpa [Function.comp_def] using this
    have hF' : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 (-q.2)) (Z, Θ) := by
      have h := (contDiffAt_Fstar₂ p hZ (by linarith) (by linarith)).comp (Z, Θ) hflip
      simpa [Function.comp_def] using h
    refine (hF'.add hg).neg.congr_of_eventuallyEq ?_
    have hnb : {q : ℝ × ℝ | q.2 < 0} ∈ nhds (Z, Θ) :=
      (isOpen_lt continuous_snd continuous_const).mem_nhds hneg
    filter_upwards [hnb] with q hq
    rw [Work.ConstructionInstance.profile_of_neg (not_le.mpr hq)]
  · exact absurd hzero hΘ
  · -- the branch `θ > 0`: the profile is `F_*(·,θ) + gs(·,θ)`
    rw [abs_of_pos hpos] at hgs
    have hF : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2) (Z, Θ) :=
      contDiffAt_Fstar₂ p hZ hpos hΘhi
    refine (hF.add hgs).congr_of_eventuallyEq ?_
    have hnb : {q : ℝ × ℝ | 0 < q.2} ∈ nhds (Z, Θ) :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds hpos
    filter_upwards [hnb] with q hq
    rw [Work.ConstructionInstance.profile_of_nonneg (le_of_lt hq)]

/-! ## The target -/

/-- **The meridian profile of the reconstruction is differentiable in the meridian variables.**

`merProfile α A B g C r z t = A(τ)⁻¹ · profile (3α) (g(·,·,τ)) (ρ(r,z)^{3α}/B(τ)) (θ(r,z))` with
`τ = clockInv C t`; off the axis (`r > 0`) and off the equatorial plane (`z ≠ 0`, so that
`θ(r,z) ≠ 0`) this is a composition of the smooth polar dictionary `(r,z) ↦ (ρ^{3α}/B, θ)` with
the profile, which is `C²` at the interior point of the appropriate branch
(`contDiffAt_profile_of_ne`), the `C²`-input on the slice `g(·,·,τ)` on the open quadrant coming
from the hypothesis `hreg`, and the positivity of `B τ` from `hB`. -/
theorem diffAt2_merProfile {α : ℝ} {A B : ℝ → ℝ} {g : Work.FTS.Galerkin.Fam}
    {C : Work.FTS.Physical.PhysClock}
    (hreg : ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0)
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) C.T) {r z : ℝ} (hr : 0 < r) (hz : z ≠ 0) :
    Work.Cyl.DiffAt2
      (fun r z => Work.FTS.Physical.merProfile α A B g C r z t) r z := by
  change DifferentiableAt ℝ (fun q : ℝ × ℝ => (A (Work.FTS.Physical.clockInv C t))⁻¹ *
      Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.thetaP q.1 q.2)) (r, z)
  set τ := Work.FTS.Physical.clockInv C t with hτdef
  have hτnn : 0 ≤ τ := by
    rw [hτdef]
    exact Work.FTS.Physical.clockInv_nonneg C ⟨ht.1.le, ht.2⟩
  have hBτ : 0 < B τ := hB τ hτnn
  have hgs : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Regularity.gSlice g τ))
      Work.FTS.EllipticEst.Q0 := hreg τ hτnn
  -- ### Step 1: the polar dictionary `(r,z) ↦ (ρ^{3α}/B, θ)` is `C²` at `(r,z)`
  have hρ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2) (r, z) := by
    have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r, z) := by fun_prop
    have h2 : (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2) (r, z) ≠ 0 := by
      show r ^ 2 + z ^ 2 ≠ 0
      positivity
    have h3 := (Real.contDiffAt_sqrt (n := 2) h2).comp (r, z) h1
    simpa [Work.Cyl.rhoP, Function.comp_def] using h3
  have hρp : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ) (r, z) := by
    have h4 := hρ.rpow_const_of_ne (p := Work.FTS.Regularity.pExp α) (Work.Cyl.rhoP_ne_zero hr z)
    simpa [div_eq_mul_inv] using
      h4.mul (contDiffAt_const (c := (B τ)⁻¹) : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (B τ)⁻¹) (r, z))
  have hθ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Work.Cyl.thetaP q.1 q.2) (r, z) := by
    have h1 : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.2 / q.1) (r, z) := by
      apply ContDiffAt.div
      · fun_prop
      · fun_prop
      · simpa using hr.ne'
    have h3 := Real.contDiff_arctan.contDiffAt.comp (r, z) h1
    simpa [Work.Cyl.thetaP, Function.comp_def] using h3
  -- ### Step 2: the self-similar argument is positive and `θ(r,z) ≠ 0`
  have hw : 0 < Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ :=
    div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hBτ
  have hθ0 : Work.Cyl.thetaP r z ≠ 0 := by
    simp only [Work.Cyl.thetaP]
    exact fun h => (div_ne_zero hz hr.ne') (Real.arctan_eq_zero_iff.mp h)
  have hθlo : -(Real.pi / 2) < Work.Cyl.thetaP r z := by
    simpa only [Work.Cyl.thetaP] using Real.neg_pi_div_two_lt_arctan (z / r)
  have hθhi : Work.Cyl.thetaP r z < Real.pi / 2 := by
    simpa only [Work.Cyl.thetaP] using Real.arctan_lt_pi_div_two (z / r)
  have habs_lt : |Work.Cyl.thetaP r z| < Real.pi / 2 := abs_lt.mpr ⟨hθlo, hθhi⟩
  have habs_pos : 0 < |Work.Cyl.thetaP r z| := abs_pos.mpr hθ0
  -- ### Step 3: the profile is `C²` at the interior point of the relevant branch
  have hmem : (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ,
      |Work.Cyl.thetaP r z|) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hw, habs_pos, habs_lt⟩
  have hgsabs : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.FTS.Regularity.gSlice g τ q.1 q.2)
      (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ, |Work.Cyl.thetaP r z|) :=
    (hgs.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).of_le (by norm_num)
  have hprof : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) q.1 q.2)
      (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B τ, Work.Cyl.thetaP r z) :=
    contDiffAt_profile_of_ne hw hθ0 hθlo hθhi hgsabs
  -- ### Step 4: compose with the polar dictionary and multiply by the amplitude
  have hcomp : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ)
        (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
        (Work.Cyl.thetaP q.1 q.2)) (r, z) := by
    have := hprof.comp (r, z) (hρp.prodMk hθ)
    simpa [Function.comp_def] using this
  have hmain : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => (A τ)⁻¹ * Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ)
        (Work.Cyl.rhoP q.1 q.2 ^ Work.FTS.Regularity.pExp α / B τ)
        (Work.Cyl.thetaP q.1 q.2)) (r, z) :=
    (contDiffAt_const (c := (A τ)⁻¹) : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (A τ)⁻¹) (r, z)).mul hcomp
  exact hmain.differentiableAt (by norm_num)

end Work.FTS.Final.Recon
