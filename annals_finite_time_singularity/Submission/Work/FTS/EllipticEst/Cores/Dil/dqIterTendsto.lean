/-
Copyright: work module for the Elgindi finite-time singularity project.

# The iterated difference quotient tends to the iterated radial derivative

For `g` of class `C^∞` on the open quadrant, `z > 0` and `θ ∈ (0,π/2)` the difference quotient
`dq c g z θ = (g (c z) θ - g z θ)/(c-1)` tends to the radial derivative
`D_z g z θ = z ∂_z g z θ` as `c → 1⁺` (`tendsto_dq_Dz`, in `DqTendsto.lean`).  This file
proves the *iterated* version

  `(dq c)^[j] f z θ  ⟶  (D_z)^[j] f z θ    (c → 1⁺)`,

which is the convergence hypothesis of the Fatou step `HkSq_zero_le_liminf` for the `j`-th
radially differentiated datum (`HkMem_dq_le`, `HkSqLimit`).

## The route

The difference quotient is *not* an average of `D_z g` along the affine family `z ↦ z(1+th)`
(the correct normalisation is the exponential one), so we introduce the **exponential dilation
average**

  `Bh c X z θ = ∫_0^1 X (z c^t) θ dt`.

The logarithmic substitution `u = z c^t` turns `dq` into the *average of the radial derivative
along the one parameter group* `t ↦ z c^t`:

  `dq c g z θ = (log c/(c-1)) · Bh c (D_z g) z θ`,   `(★)`

because `d/dt [g (z c^t) θ] = log c · D_z g (z c^t) θ` (the two factors `z` of the chain rule
become the correct weight `z c^t` only in the exponential parametrisation).  Since moreover
`D_z (dq c g) = dq c (D_z g)` pointwise on the open quadrant (both sides are the *same*
difference quotient of `z ∂_z g`), the identity `(★)` iterates:

  `(dq c)^[j] f = (log c/(c-1))^j · (Bh c)^[j] (D_z^[j] f)`   on the quadrant.

The operator `Bh c` is a convex average of the values of `X` over the interval `[z, z c^j]`
(`Bh_bounds`), so for a continuous `θ`-slice the iterate converges to `X z θ` (`BhIter_tendsto`,
the interval shrinking to the point `z`), and `(log c/(c-1))^j → 1` because `log'(1) = 1`.  The
product rule for limits then gives the theorem.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic
import Submission.Work.FTS.EllipticEst.Cores.Dil.DqTendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {f g X Y : ℝ → ℝ → ℝ}

/-! ## The exponential dilation average -/

/-- The exponential dilation average `Bh c X z θ = ∫_0^1 X (z c^t) θ dt`. -/
def Bh (c : ℝ) (X : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => ∫ t in (0 : ℝ)..1, X (z * c ^ t) θ

@[simp] theorem Bh_apply (c : ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Bh c X z θ = ∫ t in (0 : ℝ)..1, X (z * c ^ t) θ := rfl

/-- The normalisation `log c/(c-1)` comparing the difference quotient with the logarithmic
dilation. -/
def lam (c : ℝ) : ℝ := Real.log c / (c - 1)

/-! ## The angular slice of `Bh c X` composed with the exponential dilation -/

theorem continuousOn_rpow_pair {X : ℝ → ℝ → ℝ}
    (hX : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    {z c θ : ℝ} (hz : 0 < z) (hc : 0 < c) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousOn (fun t : ℝ => X (z * c ^ t) θ) (Set.uIcc 0 1) := by
  have hpair : ContinuousOn (fun t : ℝ => (z * c ^ t, θ)) (Set.uIcc 0 1) :=
    ((continuous_const.mul (Real.continuous_const_rpow (ne_of_gt hc))).prodMk
      continuous_const).continuousOn
  have hcomp := hX.comp hpair (fun t ht => Work.FTS.EllipticEst.mem_Q0.mpr
    ⟨mul_pos hz (Real.rpow_pos_of_pos hc t), hθ.1, hθ.2⟩)
  simpa only [Function.comp_def, Function.uncurry] using hcomp

/-! ## The base identity: `dq` is `lam · Bh` applied to the radial derivative -/

theorem dq_eq_lam_Bh {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {c : ℝ} (hc : 1 < c) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    dq c g z θ = lam c * Bh c (Work.Spaces.Dz g) z θ := by
  have hcpos : 0 < c := by linarith
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => g (z * c ^ s) θ)
        (Real.log c * Work.Spaces.Dz g (z * c ^ t) θ) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℝ => g u θ) (Work.Spaces.pz g (z * c ^ t) θ) (z * c ^ t) :=
      hg.hasDerivAt_slice hθ (mul_pos hz (Real.rpow_pos_of_pos hcpos t))
    have h2 : HasDerivAt (fun s : ℝ => z * c ^ s) (z * (c ^ t * Real.log c)) t :=
      ((Real.hasStrictDerivAt_const_rpow hcpos t).hasDerivAt).const_mul z
    have h3 := h1.comp t h2
    have hdeq : Work.Spaces.pz g (z * c ^ t) θ * (z * (c ^ t * Real.log c))
        = Real.log c * Work.Spaces.Dz g (z * c ^ t) θ := by
      rw [Work.Spaces.Dz]; ring
    simpa only [Function.comp_def, hdeq] using h3
  have hint : IntervalIntegrable
      (fun s : ℝ => Real.log c * Work.Spaces.Dz g (z * c ^ s) θ) volume 0 1 :=
    ContinuousOn.intervalIntegrable
      ((continuousOn_rpow_pair (hg.Dz).continuousOn hz hcpos hθ).const_mul _)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hlog : Real.log c * Bh c (Work.Spaces.Dz g) z θ = g (c * z) θ - g z θ := by
    rw [Bh, ← intervalIntegral.integral_const_mul]
    simpa only [Real.rpow_one, Real.rpow_zero, mul_one, mul_comm] using hFTC
  rw [show dq c g z θ = (g (c * z) θ - g z θ) / (c - 1) from rfl, lam, div_mul_eq_mul_div, hlog]

/-! ## Congruence and homogeneity of the iterates of `Bh` -/

theorem BhIter_congr {c : ℝ} (hc : 0 < c) {X Y : ℝ → ℝ → ℝ}
    (hXY : ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → X z θ = Y z θ) (i : ℕ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → (Bh c)^[i] X z θ = (Bh c)^[i] Y z θ := by
  induction i with
  | zero => exact hXY
  | succ i ih =>
    intro z θ hz hθ
    simp only [Function.iterate_succ_apply', Bh]
    apply intervalIntegral.integral_congr
    intro t ht
    exact ih (z * c ^ t) θ (mul_pos hz (Real.rpow_pos_of_pos hc t)) hθ

theorem Bh_const_mul (c μ : ℝ) (X : ℝ → ℝ → ℝ) (i : ℕ) :
    (Bh c)^[i] (fun z θ => μ * X z θ) = fun z θ => μ * (Bh c)^[i] X z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext z θ
    simp only [Bh]
    rw [intervalIntegral.integral_const_mul]

/-! ## The radial derivative of a difference quotient -/

theorem Dz_dq {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {c : ℝ} (hc : 1 < c) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.Dz (dq c g) z θ = dq c (Work.Spaces.Dz g) z θ := by
  intro z θ hz hθ
  have hp := pz_dq hg hc z θ hz hθ
  have hD : Work.Spaces.Dz (dq c g) z θ = z * Work.Spaces.pz (dq c g) z θ := rfl
  rw [hD, hp]
  show z * ((c * Work.Spaces.pz g (c * z) θ - Work.Spaces.pz g z θ) / (c - 1))
      = ((c * z) * Work.Spaces.pz g (c * z) θ - z * Work.Spaces.pz g z θ) / (c - 1)
  ring

theorem DzIter_dq {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {c : ℝ} (hc : 1 < c) (i : ℕ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.DzIter i (dq c g) z θ = dq c (Work.Spaces.DzIter i g) z θ := by
  induction i with
  | zero => intro z θ hz hθ; simp
  | succ i ih =>
    intro z θ hz hθ
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ]
    have hev : (fun z' : ℝ => Work.Spaces.DzIter i (dq c g) z' θ)
        =ᶠ[𝓝 z] (fun z' : ℝ => dq c (Work.Spaces.DzIter i g) z' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih z' θ hz' hθ
    have h1 : Work.Spaces.Dz (Work.Spaces.DzIter i (dq c g)) z θ
        = Work.Spaces.Dz (dq c (Work.Spaces.DzIter i g)) z θ := by
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [hev.deriv_eq]
    rw [h1, Dz_dq (hg.DzIter i) hc z θ hz hθ]

/-! ## The iterated identity -/

theorem dqIter_eq (c : ℝ) (hc : 1 < c) (j : ℕ) :
    ∀ (f : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f → ∀ z θ, 0 < z →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (dq c)^[j] f z θ
        = (lam c) ^ j * (Bh c)^[j] (Work.Spaces.DzIter j f) z θ := by
  induction j with
  | zero => intro f hf z θ hz hθ; simp
  | succ j ih =>
    intro f hf z θ hz hθ
    rw [Function.iterate_succ_apply,
      ih (dq c f) (smoothOpen_dq hf (by linarith : (0 : ℝ) < c)) z θ hz hθ]
    rw [BhIter_congr (by linarith : (0 : ℝ) < c)
      (X := Work.Spaces.DzIter j (dq c f)) (Y := dq c (Work.Spaces.DzIter j f))
      (fun z' θ' hz' hθ' => DzIter_dq hf hc j z' θ' hz' hθ') j z θ hz hθ]
    rw [BhIter_congr (by linarith : (0 : ℝ) < c)
      (X := dq c (Work.Spaces.DzIter j f))
      (Y := fun z θ => lam c * (Bh c) (Work.Spaces.DzIter (j + 1) f) z θ)
      (fun z' θ' hz' hθ' => dq_eq_lam_Bh (hf.DzIter j) hc hz' hθ') j z θ hz hθ]
    rw [Bh_const_mul]
    simp only [Function.iterate_succ_apply]
    rw [pow_succ]
    ring

/-! ## Continuity in the radial variable at a fixed angle -/

theorem continuousOn_comp_rpow {Y : ℝ → ℝ} {z c : ℝ} (hz : 0 < z) (hc : 0 < c)
    (hY : ContinuousOn Y (Set.Ioi 0)) :
    ContinuousOn (fun t : ℝ => Y (z * c ^ t)) (Set.uIcc 0 1) := by
  refine hY.comp (continuous_const.mul (Real.continuous_const_rpow (ne_of_gt hc))).continuousOn
    (fun t ht => mul_pos hz (Real.rpow_pos_of_pos hc t))

theorem Bh_slice_cont {X : ℝ → ℝ → ℝ} {c θ : ℝ} (hc : 1 < c)
    (hX : ContinuousOn (fun z => X z θ) (Set.Ioi 0)) :
    ContinuousOn (fun z => Bh c X z θ) (Set.Ioi 0) := by
  have hcpos : 0 < c := by linarith
  have hlogc_ne : Real.log c ≠ 0 := ne_of_gt (Real.log_pos hc)
  have hYc : Continuous (fun v : ℝ => X (Real.exp v) θ) :=
    hX.comp_continuous Real.continuous_exp (fun v => Real.exp_pos v)
  set Ψ : ℝ → ℝ := fun v => ∫ u in (0 : ℝ)..v, X (Real.exp u) θ with hΨdef
  have hΨderiv : ∀ v : ℝ, HasDerivAt Ψ (X (Real.exp v) θ) v := by
    intro v
    have hsm : StronglyMeasurableAtFilter (fun u : ℝ => X (Real.exp u) θ) (𝓝 v) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_univ hYc.continuousOn v trivial
    exact intervalIntegral.integral_hasDerivAt_right
      (hYc.continuousOn.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := v))
      hsm hYc.continuousAt
  have hΨcont : Continuous Ψ :=
    continuous_iff_continuousAt.mpr (fun v => (hΨderiv v).continuousAt)
  have hlogcont : ContinuousOn Real.log (Set.Ioi 0) := fun x hx =>
    (Real.continuousAt_log (ne_of_gt hx)).continuousWithinAt
  -- the value formula
  have hval : ∀ z ∈ Set.Ioi 0, Bh c X z θ
      = (Real.log c)⁻¹ * (Ψ (Real.log c + Real.log z) - Ψ (Real.log z)) := by
    intro z hz
    show (∫ t in (0 : ℝ)..1, X (z * c ^ t) θ) = _
    have hfun : (fun t : ℝ => X (z * c ^ t) θ)
        = fun t : ℝ => X (Real.exp (Real.log c * t + Real.log z)) θ := by
      funext t
      congr 1
      rw [Real.rpow_def_of_pos hcpos, Real.exp_add, Real.exp_log hz]
      ring
    rw [hfun]
    have hkey : (∫ t in (0 : ℝ)..1, X (Real.exp (Real.log c * t + Real.log z)) θ)
        = (Real.log c)⁻¹ * (∫ u in (Real.log z)..(Real.log c + Real.log z),
            X (Real.exp u) θ) := by
      have h := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
        (fun u : ℝ => X (Real.exp u) θ) hlogc_ne (Real.log z)
      simpa only [mul_zero, add_zero, zero_add, mul_one, smul_eq_mul] using h
    rw [hkey]
    congr 1
    have h := intervalIntegral.integral_interval_sub_left
      (hYc.continuousOn.intervalIntegrable (μ := volume) (a := (0 : ℝ))
        (b := Real.log c + Real.log z))
      (hYc.continuousOn.intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := Real.log z))
    rw [← h]
  have hcont : ContinuousOn
      (fun z => (Real.log c)⁻¹ * (Ψ (Real.log c + Real.log z) - Ψ (Real.log z)))
      (Set.Ioi 0) :=
    continuousOn_const.mul
      ((hΨcont.comp_continuousOn (continuousOn_const.add (hlogcont))).sub
        (hΨcont.comp_continuousOn hlogcont))
  refine hcont.congr (fun z hz => hval z hz)

theorem BhIter_slice_cont {c θ : ℝ} (hc : 1 < c) (i : ℕ) :
    ∀ (X : ℝ → ℝ → ℝ), ContinuousOn (fun z => X z θ) (Set.Ioi 0) →
      ContinuousOn (fun z => (Bh c)^[i] X z θ) (Set.Ioi 0) := by
  induction i with
  | zero => intro X hX; simpa using hX
  | succ i ih =>
    intro X hX
    simpa only [Function.iterate_succ_apply'] using
      Bh_slice_cont (X := (Bh c)^[i] X) hc (ih X hX)

/-! ## `Bh`-iterates are convex averages -/

theorem Bh_bounds {X : ℝ → ℝ → ℝ} {c θ : ℝ} (hc : 1 < c)
    (hX : ContinuousOn (fun z => X z θ) (Set.Ioi 0)) (i : ℕ) :
    ∀ z, 0 < z → ∀ m M,
      (∀ u ∈ Set.Icc z (z * c ^ (i : ℝ)), m ≤ X u θ ∧ X u θ ≤ M) →
      m ≤ (Bh c)^[i] X z θ ∧ (Bh c)^[i] X z θ ≤ M := by
  have hcpos : 0 < c := by linarith
  induction i with
  | zero =>
    intro z hz m M hb
    simpa using hb z (by simp [Real.rpow_zero])
  | succ i ih =>
    intro z hz m M hb
    have hstep : (Bh c)^[i + 1] X z θ = ∫ t in (0 : ℝ)..1, (Bh c)^[i] X (z * c ^ t) θ := by
      simp only [Function.iterate_succ_apply', Bh]
    rw [hstep]
    have hbd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        m ≤ (Bh c)^[i] X (z * c ^ t) θ ∧ (Bh c)^[i] X (z * c ^ t) θ ≤ M := by
      intro t ht
      refine ih (z * c ^ t) (mul_pos hz (Real.rpow_pos_of_pos hcpos t)) m M ?_
      intro u hu
      refine hb u ⟨?_, ?_⟩
      · exact le_trans (le_mul_of_one_le_right (le_of_lt hz)
          (Real.one_le_rpow (le_of_lt hc) ht.1)) hu.1
      · have h2 : (z * c ^ t) * c ^ (i : ℝ) ≤ z * c ^ ((i : ℝ) + 1) := by
          rw [mul_assoc, ← Real.rpow_add hcpos]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (le_of_lt hc) (by linarith [ht.2]))
            (le_of_lt hz)
        calc u ≤ (z * c ^ t) * c ^ (i : ℝ) := hu.2
          _ ≤ z * c ^ ((i : ℝ) + 1) := h2
          _ = z * c ^ ((i + 1 : ℕ) : ℝ) := by rw [Nat.cast_add, Nat.cast_one]
    have hint : IntervalIntegrable (fun t : ℝ => (Bh c)^[i] X (z * c ^ t) θ) volume 0 1 :=
      ContinuousOn.intervalIntegrable
        (continuousOn_comp_rpow hz hcpos (BhIter_slice_cont hc i X hX))
    constructor
    · calc m = ∫ t in (0 : ℝ)..1, (m : ℝ) := by simp
        _ ≤ ∫ t in (0 : ℝ)..1, (Bh c)^[i] X (z * c ^ t) θ :=
            intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const hint
              (fun t ht => (hbd t ht).1)
    · calc ∫ t in (0 : ℝ)..1, (Bh c)^[i] X (z * c ^ t) θ
          ≤ ∫ t in (0 : ℝ)..1, (M : ℝ) :=
            intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const
              (fun t ht => (hbd t ht).2)
        _ = M := by simp

/-! ## The limit of the iterates -/

theorem lam_tendsto : Filter.Tendsto lam (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hslope : Filter.Tendsto (slope Real.log 1) (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
    simpa using (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope
  have h1 : ∀ c : ℝ, c ≠ 1 → slope Real.log 1 c = lam c := by
    intro c hc
    rw [slope_def_module, lam]
    simp only [smul_eq_mul, Real.log_one, sub_zero]
    ring
  refine Filter.Tendsto.congr' ?_ (hslope.mono_left (nhdsWithin_mono 1 ?_))
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact h1 c (ne_of_gt hc)
  · intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hx

theorem lam_pow_tendsto (j : ℕ) :
    Filter.Tendsto (fun c : ℝ => lam c ^ j) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  simpa using lam_tendsto.pow j

theorem BhIter_tendsto {X : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hX : ContinuousOn (fun u => X u θ) (Set.Ioi 0)) (i : ℕ) :
    Filter.Tendsto (fun c : ℝ => (Bh c)^[i] X z θ) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (X z θ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcontz : ContinuousAt (fun u => X u θ) z := hX.continuousAt (isOpen_Ioi.mem_nhds hz)
  have hev : ∀ᶠ u in 𝓝 z, dist (X u θ) (X z θ) < ε / 2 :=
    (Metric.tendsto_nhds.mp hcontz.tendsto) (ε / 2) (by linarith)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  -- the smallness of the interval `[z, z c^i]`
  have hex : ∃ η > 0, z * ((1 + η) ^ (i : ℝ) - 1) < δ := by
    have hcont : ContinuousAt (fun η : ℝ => (1 + η) ^ (i : ℝ)) 0 :=
      (continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))
    have hT : Filter.Tendsto (fun η : ℝ => z * ((1 + η) ^ (i : ℝ) - 1)) (𝓝 0) (𝓝 0) := by
      have h2 : Filter.Tendsto (fun η : ℝ => (1 + η) ^ (i : ℝ)) (𝓝 0) (𝓝 1) := by
        simpa using hcont.tendsto
      have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 0) (𝓝 1) := tendsto_const_nhds
      simpa using ((h2.sub hone).const_mul z)
    have h3 := (Metric.tendsto_nhds.mp hT) δ hδpos
    rw [Metric.eventually_nhds_iff] at h3
    obtain ⟨r, hrpos, hr⟩ := h3
    refine ⟨min (r / 2) 1, by positivity, ?_⟩
    have hmem : min (r / 2) 1 ∈ Metric.ball (0 : ℝ) r := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      have := min_le_left (r / 2) 1
      linarith
    have h4 := hr hmem
    rw [Real.dist_eq, sub_zero] at h4
    have hpos : (0 : ℝ) ≤ min (r / 2) 1 := le_of_lt (by positivity)
    have hone : (1 : ℝ) ≤ 1 + min (r / 2) 1 := by linarith
    have hle : (1 : ℝ) ≤ (1 + min (r / 2) 1) ^ (i : ℝ) :=
      Real.one_le_rpow hone (Nat.cast_nonneg i)
    rw [abs_of_nonneg (mul_nonneg (le_of_lt hz) (by linarith))] at h4
    exact h4
  obtain ⟨η, hηpos, hηlt⟩ := hex
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds (1 : ℝ) hηpos] with c hc hcI
  have hc1 : 1 < c := hcI
  have hclt : c < 1 + η := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hc
    linarith [hc.2]
  have hbd : ∀ u ∈ Set.Icc z (z * c ^ (i : ℝ)),
      X z θ - ε / 2 ≤ X u θ ∧ X u θ ≤ X z θ + ε / 2 := by
    intro u hu
    have huz : dist u z < δ := by
      rw [Real.dist_eq]
      have h1 : u - z ≤ z * ((1 + η) ^ (i : ℝ) - 1) := by
        have h2 : z * c ^ (i : ℝ) ≤ z * (1 + η) ^ (i : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (le_of_lt (by linarith : (0 : ℝ) < c)) (le_of_lt hclt)
              (Nat.cast_nonneg i))
            (le_of_lt hz)
        have h3 : z * (1 + η) ^ (i : ℝ) = z * (1 + ((1 + η) ^ (i : ℝ) - 1)) := by ring
        linarith [hu.1, hu.2]
      rw [abs_of_nonneg (by linarith [hu.1])]
      linarith [hηlt]
    have hd := hδ huz
    rw [Real.dist_eq, abs_lt] at hd
    exact ⟨by linarith [hd.1], by linarith [hd.2]⟩
  have hb := Bh_bounds hc1 hX i z hz (X z θ - ε / 2) (X z θ + ε / 2) hbd
  rw [Real.dist_eq]
  rw [abs_lt]
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-! ## The target -/

theorem dqIterTendsto {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Filter.Tendsto (fun c : ℝ => (Work.FTS.EllipticEst.Cores.Dil.dq c)^[j] f z θ)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Work.Spaces.DzIter j f z θ)) := by
  have hslice : ContinuousOn (fun u => Work.Spaces.DzIter j f u θ) (Set.Ioi 0) :=
    ((hf.DzIter j).curry_z hθ).continuousOn
  refine Filter.Tendsto.congr' ?_ (by
    simpa using (lam_pow_tendsto j).mul (BhIter_tendsto hz hslice j))
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (dqIter_eq c hc j f hf z θ hz hθ).symm

end Work.FTS.EllipticEst.Cores.Dil
