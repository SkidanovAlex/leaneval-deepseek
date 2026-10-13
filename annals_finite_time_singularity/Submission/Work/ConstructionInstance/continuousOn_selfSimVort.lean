import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.ConstructionInstance.SelfSim
import Submission.Work.ConstructionInstance.GCompDefs
import Submission.Work.ConstructionInstance.div_omega0_all
import Submission.Work.ConstructionInstance.profile_continuousAt_zero
import Submission.Work.ConstructionInstance.profile_continuousAt_pi_half
import Submission.Work.ConstructionInstance.exists_profile_abs_le_mul_z
import Submission.Work.ConstructionInstance.continuousAt_psi
import Submission.Work.ConstructionInstance.continuousAt_eTheta_of_radial_ne_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option linter.unusedVariables false

open Set Filter
open scoped Topology

namespace Work.ConstructionInstance

/-! ## Continuity of the cylindrical coordinates -/

theorem continuous_rho : Continuous (Work.Cyl.rho : R3 → ℝ) := by
  have h : (Work.Cyl.rho : R3 → ℝ) = fun x => ‖x‖ := funext Work.Cyl.rho_eq_norm
  rw [h]
  exact continuous_norm

theorem continuous_radial : Continuous (Work.Cyl.radial : R3 → ℝ) := by
  have h : (Work.Cyl.radial : R3 → ℝ) = fun x => Real.sqrt (x 0 ^ 2 + x 1 ^ 2) := by
    funext x
    rw [Work.Cyl.radial, Work.Cyl.radSq]
  rw [h]
  fun_prop

/-- `θ = arctan (x₃/r)` is continuous off the symmetry axis. -/
theorem continuousAt_theta_of_radial_ne_zero {x : R3} (hx : Work.Cyl.radial x ≠ 0) :
    ContinuousAt Work.Cyl.theta x := by
  have h1 : ContinuousAt (fun y : R3 => Work.Cyl.axial y / Work.Cyl.radial y) x := by
    refine ContinuousAt.div ?_ continuous_radial.continuousAt hx
    show ContinuousAt (fun y : R3 => y 2) x
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).continuousAt
  have h2 : ContinuousAt (fun y : R3 => Real.arctan (Work.Cyl.axial y / Work.Cyl.radial y)) x :=
    (Real.continuous_arctan.continuousAt).comp h1
  exact h2

/-! ## The profile at the exceptional angle `π/2` -/

theorem Fstar_pi_div_two {p : ℝ} (hp : p ≠ 0) (z : ℝ) :
    Work.Construction.Fstar p z (Real.pi / 2) = 0 := by
  have hbase : Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2 = 0 := by
    rw [Real.sin_pi_div_two, Real.cos_pi_div_two]
    norm_num
  rw [Work.Construction.Fstar, Work.Spaces.Gam, hbase,
    Real.zero_rpow (by positivity : p / 3 ≠ 0)]
  ring

theorem profile_pi_div_two {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (z : ℝ) :
    profile p g z (Real.pi / 2) = 0 := by
  rw [profile_of_nonneg (le_of_lt (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2)),
    Fstar_pi_div_two hp z, hvt.2 z, add_zero]

/-! ## The corrected angle `θ ⟶ psi` and the parity factor -/

/-- The sign of the axial coordinate (`= 1` on the closed half space `x₃ ≥ 0`).  It is bounded
by `1` everywhere and locally constant off the plane `x₃ = 0`, which is all the axis argument
needs: the profile factor vanishes there. -/
def sgnThird (x : R3) : ℝ := if 0 ≤ x 2 then 1 else -1

theorem abs_sgnThird_le_one (x : R3) : |sgnThird x| ≤ 1 := by
  rw [sgnThird]
  split <;> norm_num

/-- `psi` is the corrected angle: it agrees with `|θ|` off the axis and equals `π/2` on it,
where the profile vanishes.  Hence the profile at `θ x` is the parity factor `sgnThird x` times
the profile at `psi x`. -/
theorem profile_theta_eq_sgnThird_mul {p : ℝ} (hp : p ≠ 0) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (z : ℝ) (x : R3) :
    profile p g z (Work.Cyl.theta x) = sgnThird x * profile p g z (psi x) := by
  by_cases h : Work.Cyl.radial x = 0
  · have hθ : Work.Cyl.theta x = 0 := by
      rw [Work.Cyl.theta, Work.Cyl.axial, h, div_zero, Real.arctan_zero]
    have hψ : psi x = Real.pi / 2 := by rw [psi, h, zero_div, Real.arccos_zero]
    rw [hθ, hψ, profile_zero hp hvt.1, profile_pi_div_two hp hvt z, mul_zero]
  · have hpos : 0 < Work.Cyl.radial x :=
      lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm h)
    rw [psi_eq_abs_theta hpos]
    rcases lt_trichotomy (x 2) 0 with hlt | heq | hgt
    · have hy : x 2 / Work.Cyl.radial x < 0 := div_neg_of_neg_of_pos hlt hpos
      have hθneg : Work.Cyl.theta x < 0 := by
        have h1 : 0 < Real.arctan (-(x 2 / Work.Cyl.radial x)) := Real.arctan_pos.mpr (neg_pos.mpr hy)
        rw [Real.arctan_neg] at h1
        have h2 : Work.Cyl.theta x = Real.arctan (x 2 / Work.Cyl.radial x) := by
          rw [Work.Cyl.theta, Work.Cyl.axial]
        rw [h2]
        linarith
      rw [profile_of_neg (not_le.mpr hθneg), abs_of_neg hθneg,
        profile_of_nonneg (neg_nonneg.mpr hθneg.le), sgnThird, ite_eq_right (not_le.mpr hlt)]
      ring
    · have hθ0 : Work.Cyl.theta x = 0 := by
        rw [Work.Cyl.theta, Work.Cyl.axial, heq, zero_div, Real.arctan_zero]
      rw [hθ0, abs_zero, profile_zero hp hvt.1, sgnThird, ite_eq_left (le_of_eq heq.symm)]
      ring
    · have hy : 0 < x 2 / Work.Cyl.radial x := div_pos hgt hpos
      have hθpos : 0 < Work.Cyl.theta x := by
        rw [Work.Cyl.theta, Work.Cyl.axial]
        exact Real.arctan_pos.mpr hy
      rw [abs_of_pos hθpos, sgnThird, ite_eq_left hgt.le, one_mul]

/-! ## A bounded factor times a vanishing continuous factor -/

/-- If `f` is continuous (within `s`) at `a` with `f a = 0`, and `g` is bounded by `1` on `s`,
then `f • g` is continuous (within `s`) at `a` — the point being that `g` itself may be
discontinuous there, as is the angular frame vector `e_θ` on the axis. -/
theorem ContinuousWithinAt.smul_of_eq_zero_of_norm_le_one {α : Type*} [TopologicalSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : α → ℝ} {g : α → E}
    {s : Set α} {a : α} (hf : ContinuousWithinAt f s a) (hf0 : f a = 0)
    (hg : ∀ x ∈ s, ‖g x‖ ≤ 1) :
    ContinuousWithinAt (fun x => f x • g x) s a := by
  rw [ContinuousWithinAt, hf0, zero_smul]
  refine squeeze_zero_norm' (a := fun x => ‖f x‖) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    calc ‖f x • g x‖ = ‖f x‖ * ‖g x‖ := norm_smul _ _
      _ ≤ ‖f x‖ * 1 := mul_le_mul_of_nonneg_left (hg x hx) (norm_nonneg _)
      _ = ‖f x‖ := mul_one _
  · have h : Tendsto f (𝓝[s] a) (𝓝 0) := by simpa [hf0] using hf.tendsto
    simpa using h.norm

theorem continuousOn_selfSimVort {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (hquad0 : ∀ θ : ℝ, g 0 θ = 0)
    (hsmooth : Work.Spaces.SmoothNbhd g) {L : ℝ} (hL : 0 < L)
    {lam : ℝ → ℝ} {T : ℝ} (hlam : ∀ t ∈ Work.ConstructionInstance.preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ Work.ConstructionInstance.preWindow T, HasDerivAt lam (deriv lam t) t)
    {R : ℝ} (hR : 0 ≤ R) :
    ContinuousOn (Function.uncurry (Work.ConstructionInstance.selfSimVort p g L lam))
      (Work.StabilityFar.coreRegion R ×ˢ Work.ConstructionInstance.preWindow T) := by
  set U : Set (R3 × ℝ) :=
    Work.StabilityFar.coreRegion R ×ˢ Work.ConstructionInstance.preWindow T with hU
  intro q₀ hq₀
  rw [hU] at hq₀
  have hlamq : 0 < lam q₀.2 := hlam q₀.2 hq₀.2
  have hlamc : ContinuousAt lam q₀.2 := (hlamdif q₀.2 hq₀.2).continuousAt
  -- the four factors: `λ⁻¹`, `χ`, the profile and the frame vector
  have hA : ContinuousWithinAt (fun q : R3 × ℝ => (lam q.2)⁻¹) U q₀ :=
    ((hlamc.comp continuous_snd.continuousAt).inv₀ (ne_of_gt hlamq)).continuousWithinAt
  have hB : ContinuousWithinAt (fun q : R3 × ℝ => Work.Stability.chi (Work.Cyl.rho q.1 / L)) U q₀ :=
    ((Work.Stability.chi_continuous.continuousAt).comp
      ((continuous_rho.comp continuous_fst).div_const L).continuousAt).continuousWithinAt
  -- the self-similar variable `ρ^p/λ` is continuous
  have hzc : ContinuousAt (fun q : R3 × ℝ => Work.Cyl.rho q.1 ^ p / lam q.2) q₀ :=
    (((continuous_rho.comp continuous_fst).continuousAt).rpow_const (Or.inr hp.le)).div
      (hlamc.comp continuous_snd.continuousAt) (ne_of_gt hlamq)
  -- the profile factor `profile p g (ρ^p/λ) (θ x)`
  have hCcont : ContinuousWithinAt
      (fun q : R3 × ℝ => profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1))
      U q₀ := by
    have hzp : -1 < Work.Cyl.rho q₀.1 ^ p / lam q₀.2 := by
      have h0 : 0 ≤ Work.Cyl.rho q₀.1 ^ p / lam q₀.2 :=
        div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg q₀.1) p) hlamq.le
      linarith
    rcases eq_or_ne (Work.Cyl.radial q₀.1) 0 with hr0 | hr0
    · rcases eq_or_ne q₀.1 0 with hx0 | hx0
      · -- the origin: the profile vanishes linearly in the self-similar variable
        obtain ⟨K, _hK0, hK⟩ := exists_profile_abs_le_mul_z hp hp1 hquad0 hsmooth
        have hztend : Tendsto (fun q : R3 × ℝ => Work.Cyl.rho q.1 ^ p / lam q.2)
            (𝓝[U] q₀) (𝓝 0) := by
          have hval : Work.Cyl.rho q₀.1 ^ p / lam q₀.2 = 0 := by
            rw [hx0]
            simp [Work.Cyl.rho_eq_norm, Real.zero_rpow hp.ne']
          have hle : 𝓝[U] q₀ ≤ 𝓝 q₀ := nhdsWithin_le_nhds
          have h := hzc.tendsto.mono_left hle
          rwa [hval] at h
        have hsmall : ∀ᶠ q in 𝓝[U] q₀, Work.Cyl.rho q.1 ^ p / lam q.2 < 1 :=
          hztend.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))
        have hbound : ∀ᶠ q in 𝓝[U] q₀,
            ‖profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1)‖
              ≤ K * (Work.Cyl.rho q.1 ^ p / lam q.2) := by
          filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hq1
          rw [hU] at hq
          have hq0 : 0 ≤ Work.Cyl.rho q.1 ^ p / lam q.2 :=
            div_nonneg (Real.rpow_nonneg (Work.Cyl.rho_nonneg q.1) p) (hlam q.2 hq.2).le
          have hθle : |Work.Cyl.theta q.1| ≤ Real.pi / 2 := by
            rw [abs_le]
            exact ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
              le_of_lt (Real.arctan_lt_pi_div_two _)⟩
          rw [Real.norm_eq_abs]
          exact hK _ ⟨hq0, le_of_lt hq1⟩ _ hθle
        have hupper : Tendsto (fun q : R3 × ℝ => K * (Work.Cyl.rho q.1 ^ p / lam q.2))
            (𝓝[U] q₀) (𝓝 0) := by
          simpa using hztend.const_mul K
        have hCtend : Tendsto
            (fun q : R3 × ℝ => profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1))
            (𝓝[U] q₀) (𝓝 0) := squeeze_zero_norm' hbound hupper
        have hC0 : profile p g (Work.Cyl.rho q₀.1 ^ p / lam q₀.2) (Work.Cyl.theta q₀.1) = 0 := by
          rw [hx0]
          have hθ : Work.Cyl.theta (0 : R3) = 0 := by
            simp [Work.Cyl.theta, Work.Cyl.axial, Work.Cyl.radial, Work.Cyl.radSq]
          rw [hθ, profile_zero hp.ne' hvt.1]
        rw [ContinuousWithinAt, hC0]
        exact hCtend
      · -- the axis, away from the origin: `θ` is replaced by the continuous corrected angle
        -- `psi` (they differ only on the axis, where the profile vanishes)
        have hψmem : psi q₀.1 = Real.pi / 2 := by
          rw [psi, hr0, zero_div, Real.arccos_zero]
        have hval : profile p g (Work.Cyl.rho q₀.1 ^ p / lam q₀.2) (psi q₀.1) = 0 := by
          rw [hψmem]
          exact profile_pi_div_two hp.ne' hvt _
        have hψc : ContinuousAt
            (fun q : R3 × ℝ => profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (psi q.1)) q₀ := by
          have hψ : ContinuousAt (fun q : R3 × ℝ => psi q.1) q₀ :=
            (continuousAt_psi hx0).comp continuous_fst.continuousAt
          have hpair : ContinuousAt
              (fun q : R3 × ℝ => (Work.Cyl.rho q.1 ^ p / lam q.2, psi q.1)) q₀ :=
            hzc.prodMk hψ
          have hprof : ContinuousAt (Function.uncurry (profile p g))
              (Work.Cyl.rho q₀.1 ^ p / lam q₀.2, psi q₀.1) := by
            rw [hψmem]
            exact profile_continuousAt_pi_half hp hvt hsmooth hzp
          exact hprof.comp (f := fun q : R3 × ℝ =>
            (Work.Cyl.rho q.1 ^ p / lam q.2, psi q.1)) hpair
        have hsm : ContinuousWithinAt
            (fun q : R3 × ℝ =>
              profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (psi q.1) • sgnThird q.1) U q₀ :=
          ContinuousWithinAt.smul_of_eq_zero_of_norm_le_one hψc.continuousWithinAt hval
            (fun q _ => abs_sgnThird_le_one q.1)
        have hfun : (fun q : R3 × ℝ =>
              profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1))
            = fun q : R3 × ℝ =>
              sgnThird q.1 * profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (psi q.1) :=
          funext fun q => profile_theta_eq_sgnThird_mul hp.ne' hvt _ _
        have hfun' : (fun q : R3 × ℝ =>
              sgnThird q.1 * profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (psi q.1))
            = fun q : R3 × ℝ =>
              profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (psi q.1) • sgnThird q.1 := by
          funext q
          rw [smul_eq_mul, mul_comm]
        rw [hfun, hfun']
        exact hsm
    · -- off the axis: a composition of continuous maps
      have hθc : ContinuousAt (fun q : R3 × ℝ => Work.Cyl.theta q.1) q₀ :=
        (continuousAt_theta_of_radial_ne_zero hr0).comp continuous_fst.continuousAt
      have hpair : ContinuousAt
          (fun q : R3 × ℝ => (Work.Cyl.rho q.1 ^ p / lam q.2, Work.Cyl.theta q.1)) q₀ :=
        hzc.prodMk hθc
      have hθmem : Work.Cyl.theta q₀.1 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
      have hprof : ContinuousAt (Function.uncurry (profile p g))
          (Work.Cyl.rho q₀.1 ^ p / lam q₀.2, Work.Cyl.theta q₀.1) := by
        rcases eq_or_ne (Work.Cyl.theta q₀.1) 0 with h0 | h0
        · rw [h0]
          exact profile_continuousAt_zero hp hvt hsmooth hzp
        · exact (contDiffAt_uncurry_profile (Work.Stability.SmoothFar.of_smoothNbhd hsmooth)
            hzp hθmem h0).continuousAt
      exact (hprof.comp (f := fun q : R3 × ℝ =>
        (Work.Cyl.rho q.1 ^ p / lam q.2, Work.Cyl.theta q.1)) hpair).continuousWithinAt
  -- the frame vector: continuous off the axis, and multiplied by the vanishing profile factor
  -- on the axis (where `e_θ` jumps)
  have hCV : ContinuousWithinAt (fun q : R3 × ℝ =>
      (profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1)) • Work.Cyl.eTheta q.1)
      U q₀ := by
    rcases eq_or_ne (Work.Cyl.radial q₀.1) 0 with hr0 | hr0
    · have hθ0 : Work.Cyl.theta q₀.1 = 0 := by
        rw [Work.Cyl.theta, Work.Cyl.axial, hr0, div_zero, Real.arctan_zero]
      have hC0 : profile p g (Work.Cyl.rho q₀.1 ^ p / lam q₀.2) (Work.Cyl.theta q₀.1) = 0 := by
        rw [hθ0, profile_zero hp.ne' hvt.1]
      exact ContinuousWithinAt.smul_of_eq_zero_of_norm_le_one hCcont hC0
        (fun q _ => norm_eTheta_le_one q.1)
    · have hVc : ContinuousWithinAt (fun q : R3 × ℝ => Work.Cyl.eTheta q.1) U q₀ :=
        ((continuousAt_eTheta_of_radial_ne_zero hr0).comp
          continuous_fst.continuousAt).continuousWithinAt
      exact hCcont.smul hVc
  have hF : ContinuousWithinAt (fun q : R3 × ℝ => (lam q.2)⁻¹ •
      (Work.Stability.chi (Work.Cyl.rho q.1 / L) •
        ((profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1)) •
          Work.Cyl.eTheta q.1))) U q₀ :=
    hA.smul (hB.smul hCV)
  have hgoal : (Function.uncurry (selfSimVort p g L lam)) = fun q : R3 × ℝ => (lam q.2)⁻¹ •
      (Work.Stability.chi (Work.Cyl.rho q.1 / L) •
        ((profile p g (Work.Cyl.rho q.1 ^ p / lam q.2) (Work.Cyl.theta q.1)) •
          Work.Cyl.eTheta q.1)) := by
    funext q
    show selfSimVort p g L lam q.1 q.2 = _
    simp only [selfSimVort, omegaSz]
  rw [hgoal]
  exact hF

end Work.ConstructionInstance
