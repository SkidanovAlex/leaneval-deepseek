import Submission.ModelArc
import Submission.ArcSeg
import Submission.ArcNB
import Mathlib
/-!
# Chart-level model two-sided arc minimality (child task)

Prove `Submission.ArcModel.arc_model_two_sided` completely.  The workspace provides:
- `Submission.ModelArc` with `region_flow_pkg` (uniform region flow with per-base containment),
  `flow_ball_cont`, `smooth_truncation_rad`, `flow_displacement_bound`, `exp_ray_geodesic`
  (real proof), and the geometry `mgLength`/`mgSpeed`, `model_normal_ball`, the per-base
  normal-ball machinery, `MinimalityWrap.radial_minimality`, `ExpCore`, `ModelExpC1`,
  `ModelSpeed.speed_const`, `ModelScale.flow_scaling`/`ModelFlowScale`, `ModelUniq.unique_geodesic`.
- READ `Submission/ModelNormalBall.lean` (per-base `model_normal_ball`, whose body you can
  re-run with the region flow at each base) and `Submission/ModelExpDiffeo2.lean`.

## Task theorem (do not change)
It says: short exponential arcs of the *chart exponential* (a local diffeo-like exponential map
`exp : E → E` defined on `ball 0 ρe` with `exp v = (Φ (x₀,(1/τe)•v) τe).1` for a genuine ODE
flow `Φ` of `odeField g`) are length-minimizing among C¹ staying curves:

    ∃ ρA > 0, ∀ W with ‖W‖ ≤ K, ∀ s ≤ t, |s| < ρA, |t| < ρA, ∀ C¹ c : ℝ → E,
      c 0 = exp (s•W) → c 1 = exp (t•W) → c stays in ball x₀ ρA →
      t - s ≤ mgLength g c 0 1.

## Mathematical route (suggested; real math, machine checked)
1. Prove that the chart-exp arc `λ ↦ exp(λ•W)` coincides (for |λ| ≤ ρA small) with the true
   geodesic trajectory `λ ↦ (Φ'(x₀,W) λ).1` of the region flow `Φ'` (use `hexpform`,
   flow scaling/homogeneity and ODE uniqueness; the velocities can be large (‖W‖ ≤ K) so
   `region_flow_pkg` with data radius ~ K+3 gives the trajectory window).
2. Uniform normal-ball data at interior bases `b = exp(s•W)`: re-run the `model_normal_ball`
   construction per base `b` with the region flow (per-base containment/hypotheses are provided
   by `region_flow_pkg`); make the radii explicit and uniform over `b` in a ball around `x₀`
   (uniform K0 bound over the region, `flow_map_contDiffOn`-type joint C¹ near `(x₀,0)`,
   explicit uniform inverse-function radius from `‖fderiv exp_b v - id‖ ≤ 1/2` + contraction).
3. Staying-minimality at base `b₀ = exp(sW)` (`MinimalityWrap.radial_minimality`) applied to
   curves staying in `ball b₀ δu` gives the two-sided bound; choose `ρA` small enough that
   `ball x₀ ρA ⊆ ball b₀ δu` for every relevant base.
4. speed along the arc is constant `√((g x₀) W W)` (speed_const), giving
   ‖exp_b₀⁻¹(exp(tW))‖_{g(b₀)} = t − s by the arc-identification (step 1) and homogeneity.

You may add helper lemmas/definitions above the theorem.  No unfinished proofs or new `axiom` declarations may remain.
Build with `lake build Submission.ArcModel`.
-/

open ContinuousLinearMap
open scoped ContDiff Topology BigOperators
open Set Metric Filter
open MeasureTheory intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace Submission.Model

/-! ## Arc identification: chart exponential agrees with the region-flow geodesic -/

/-- Ray agreement with large velocity data: if `Φ₁` is a flow of the geodesic field on the
radius-1 data ball and `Φ₂` on the radius-`R₂` data ball, both producing genuine geodesics,
then the `ρ₀`-flow slice of the scaled velocity `(1/ρ₀) • (t • w)` equals the `t`-flow of
velocity `w`. -/
lemma ray_agreement_big (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (ε₁ : ℝ) (hε₁ : 0 < ε₁) (hρε₁ : ρ₀ < ε₁)
    (Φ₁ : E × E → ℝ → E × E)
    (hΦ₁ : ∀ z ∈ closedBall (x₀, 0) 1, Φ₁ z 0 = z ∧
       ∀ t ∈ Icc (-ε₁) ε₁, HasDerivAt (Φ₁ z) (odeField g (Φ₁ z t)) t)
    (ε₂ : ℝ) (hε₂ : 0 < ε₂)
    (R₂ : ℝ) (hR₂ : 0 ≤ R₂)
    (Φ₂ : E × E → ℝ → E × E)
    (hΦ₂ : ∀ z ∈ closedBall (x₀, 0) R₂, Φ₂ z 0 = z ∧
       ∀ t ∈ Icc (-ε₂) ε₂, HasDerivAt (Φ₂ z) (odeField g (Φ₂ z t)) t)
    (hrest : Φ₁ (x₀, 0) ρ₀ = (x₀, 0))
    (w : E) (hw : ‖w‖ ≤ R₂) {t : ℝ} (ht : |t| < min (ρ₀ / 2) ε₂)
    (hthin : ‖(t / ρ₀) • w‖ ≤ 1) :
    (Φ₁ (x₀, (1 / ρ₀) • (t • w)) ρ₀).1 = (Φ₂ (x₀, w) t).1 := by
  have htρ : |t| < ρ₀ / 2 := lt_of_lt_of_le ht (min_le_left _ _)
  have htε₂ : |t| < ε₂ := lt_of_lt_of_le ht (min_le_right _ _)
  by_cases ht0 : t = 0
  · subst t
    have hz₀₂ : (x₀, w) ∈ closedBall (x₀, 0) R₂ := mem_pair_ball x₀ R₂ hR₂ w hw
    have hleft : (Φ₁ (x₀, 0) ρ₀).1 = x₀ := by
      simpa using congrArg Prod.fst hrest
    have hright : (Φ₂ (x₀, w) 0).1 = x₀ := by
      simpa using congrArg Prod.fst (hΦ₂ (x₀, w) hz₀₂).1
    simp [smul_zero, hleft, hright]
  · let a : E := (t / ρ₀) • w
    have ha : a = (1 / ρ₀) • (t • w) := by
      simp [a, smul_smul]
      ring_nf
    let c₁ : ℝ → E := fun s => (Φ₁ (x₀, a) s).1
    let vel₁ : ℝ → E := fun s => (Φ₁ (x₀, a) s).2
    let c₂ : ℝ → E := fun s => (Φ₂ (x₀, w) s).1
    let vel₂ : ℝ → E := fun s => (Φ₂ (x₀, w) s).2
    have hza : (x₀, a) ∈ closedBall (x₀, 0) 1 := by
      simpa [a] using mem_pair_ball x₀ (1 : ℝ) (by norm_num) ((t / ρ₀) • w) hthin
    have hzw : (x₀, w) ∈ closedBall (x₀, 0) R₂ := mem_pair_ball x₀ R₂ hR₂ w hw
    have hsplit₁ := split_flow_geodesic g hg hinv (x₀,0) hε₁ (closedBall (x₀,0) 1) Φ₁ hΦ₁ hza
    have hsplit₂ := split_flow_geodesic g hg hinv (x₀,0) hε₂ (closedBall (x₀,0) R₂) Φ₂ hΦ₂ hzw
    let s : ℝ := ρ₀ / t
    have hs : s ≠ 0 := div_ne_zero (ne_of_gt hρ₀) ht0
    have hsa : s • a = w := by
      dsimp [s, a]
      rw [smul_smul]
      have hmul : (ρ₀ / t) * (t / ρ₀) = 1 := by
        field_simp [ht0, ne_of_gt hρ₀]
      rw [hmul, one_smul]
    have hc10 : c₁ 0 = x₀ := by
      simpa [c₁] using (congrArg Prod.fst (hΦ₁ (x₀,a) hza).1)
    have hv10 : vel₁ 0 = a := by
      simpa [vel₁] using (congrArg Prod.snd (hΦ₁ (x₀,a) hza).1)
    have hc20 : c₂ 0 = x₀ := by
      simpa [c₂] using (congrArg Prod.fst (hΦ₂ (x₀,w) hzw).1)
    have hv20 : vel₂ 0 = s • a := by
      have hsnd : (Φ₂ (x₀, w) 0).2 = w := congrArg Prod.snd (hΦ₂ (x₀,w) hzw).1
      rw [hsa]
      simpa [vel₂, hsnd]
    have hc₁d : ∀ u ∈ Ioo (-ε₁) ε₁, HasDerivAt c₁ (vel₁ u) u := by
      intro u hu
      simpa [c₁, vel₁] using hsplit₁.1 u hu
    have hv₁d : ∀ u ∈ Ioo (-ε₁) ε₁,
        HasDerivAt vel₁ (accel (g (c₁ u)) (fderiv ℝ g (c₁ u)) (vel₁ u)) u := by
      intro u hu
      simpa [c₁, vel₁] using hsplit₁.2 u hu
    have hc₂d : ∀ u ∈ Ioo (-ε₂) ε₂, HasDerivAt c₂ (vel₂ u) u := by
      intro u hu
      simpa [c₂, vel₂] using hsplit₂.1 u hu
    have hv₂d : ∀ u ∈ Ioo (-ε₂) ε₂,
        HasDerivAt vel₂ (accel (g (c₂ u)) (fderiv ℝ g (c₂ u)) (vel₂ u)) u := by
      intro u hu
      simpa [c₂, vel₂] using hsplit₂.2 u hu
    have hscaling := flow_scaling (g := g) (hg := hg) (hinv := hinv)
      (ε₁ := ε₁) (hε₁ := hε₁) (ε₂ := ε₂) (hε₂ := hε₂)
      (c₁ := c₁) (vel₁ := vel₁) (c₂ := c₂) (vel₂ := vel₂) (x := x₀) (v := a) (s := s) (hs := hs)
      (hc₁ := hc10) (hv₁ := hv10) (hc₂ := hc20) (hv₂ := hv20)
      (hc₁d := hc₁d) (hv₁d := hv₁d) (hc₂d := hc₂d) (hv₂d := hv₂d)
    have hst : s * t = ρ₀ := by
      dsimp [s]
      field_simp [ht0, ne_of_gt hρ₀]
    have hmm : |t| < min ε₂ (ε₁ / |s|) := by
      have hltε₂ : |t| < ε₂ := htε₂
      have hs0 : 0 < |s| := abs_pos.mpr hs
      have hstabs : |s| * |t| < ε₁ := by
        have h1 : |s * t| = ρ₀ := by rw [hst, abs_of_pos hρ₀]
        have h2 : |s| * |t| = |s * t| := by rw [abs_mul]
        rw [h1] at h2
        rw [h2]
        exact hρε₁
      have hlt2s : |t| < ε₁ / |s| := by
        apply (lt_div_iff₀ hs0).mpr
        simpa [mul_comm] using hstabs
      exact lt_min hltε₂ hlt2s
    have htI : t ∈ Ioo (-min ε₂ (ε₁ / |s|)) (min ε₂ (ε₁ / |s|)) := by
      rcases abs_lt.mp hmm with ⟨h1, h2⟩
      exact ⟨h1, h2⟩
    have hconcl := hscaling t htI
    have hmain : c₂ t = c₁ (s * t) := hconcl.1
    have hgoal : c₁ ρ₀ = (Φ₁ (x₀, (1 / ρ₀) • (t • w)) ρ₀).1 := by
      dsimp [c₁]
      rw [← ha]
    have hc2 : c₂ t = (Φ₂ (x₀, w) t).1 := rfl
    calc
      (Φ₁ (x₀, (1 / ρ₀) • (t • w)) ρ₀).1 = c₁ ρ₀ := hgoal.symm
      _ = c₁ (s * t) := by rw [hst]
      _ = c₂ t := hmain.symm
      _ = (Φ₂ (x₀, w) t).1 := hc2



/-- The flow map of the geodesic field is differentiable at the rest point `(x₀, 0)` with the
affine derivative `w ↦ (w.1 + t • w.2, w.2)`, uniformly for small flow-times `t`. -/
lemma rest_flow_deriv_affine (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) (Tf : ℝ) (hTf : 0 < Tf)
    (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hΦ₀ : ∀ z ∈ closedBall (x₀, 0) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (x₀, 0) 2))
    (hLip : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall (x₀, 0) 1)) :
    ∃ T > 0, T < Tf ∧ ∀ t ∈ Icc (-T) T,
      ∃ L0 : E × E →L[ℝ] E × E,
        HasFDerivAt (fun z => Φ z t) L0 (x₀, 0) ∧
        ∀ w : E × E, L0 w = (w.1 + t • w.2, w.2) := by
  classical
  let z₀ : E × E := (x₀, 0)
  let hΦ₀can : ∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
      ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    exact ⟨(hΦ₀ z hz).1, (hΦ₀ z hz).2.1⟩
  let Tj : ℝ := Tf / 2
  have hTj : 0 < Tj := by dsimp [Tj]; positivity
  have hTjTf : Tj < Tf := by dsimp [Tj]; linarith
  have hrest : ∀ t ∈ Ioo (-Tf) Tf, Φ (x₀, 0) t = (x₀, 0) := by
    have hfr := flow_rest_point g hg hinv hTf (x₀ := x₀) (Φ := Φ) hΦ₀can
    simpa [z₀] using hfr
  let J : E × E → ℝ → E × E := fun w t => (w.1 + t • w.2, w.2)
  have hJ0 : ∀ w : E × E, J w 0 = w := by intro w; simp [J]
  have hJadd : ∀ t : ℝ, ∀ (a b : E × E), J (a + b) t = J a t + J b t := by
    intro t a b
    ext <;> simp [J, smul_add, add_assoc, add_comm, add_left_comm]
  have hJsmul : ∀ t : ℝ, ∀ (a : E × E) (c : ℝ), J (c • a) t = c • J a t := by
    intro t a c
    ext
    · simp [J, smul_add]
      rw [smul_smul, smul_smul]
      congr 1
      ring
    · simp [J]
  have hJd : ∀ w : E × E, ∀ t ∈ Ioo (-Tj) Tj,
      HasDerivAt (J w) ((fderiv ℝ (odeField g)) (Φ (x₀, 0) t) (J w t)) t := by
    intro w t ht
    have htTf : t ∈ Ioo (-Tf) Tf := by
      constructor <;> linarith [ht.1, ht.2, hTjTf]
    have hd1 : HasDerivAt (fun s : ℝ => w.1 + s • w.2) w.2 t := by
      have hsm : HasDerivAt (fun u : ℝ => u • w.2) w.2 t := by
        simpa using ((hasDerivAt_id t).smul_const w.2)
      have hadd : HasDerivAt (fun u : ℝ => w.1 + u • w.2) ((0 : E) + w.2) t :=
        (hasDerivAt_const t w.1).add hsm
      simpa using hadd
    have hd2 : HasDerivAt (fun _ : ℝ => w.2) (0 : E) t := hasDerivAt_const t w.2
    have hder : HasDerivAt (fun u : ℝ => (w.1 + u • w.2, w.2)) (w.2, (0 : E)) t :=
      hd1.prodMk hd2
    have hval : (fderiv ℝ (odeField g)) (Φ (x₀, 0) t) (J w t) = (w.2, (0 : E)) := by
      rw [hrest t htTf]
      have hfd := fderiv_odeField_rest g hg hinv x₀ (w.1 + t • w.2, w.2)
      simpa [J, z₀] using hfd
    exact hder.congr_deriv hval.symm
  rcases flow_fderiv_canonical g hg hinv z₀ Tf hTf Lf Φ hΦ₀can hLip Tj hTj hTjTf
      J hJ0 hJd hJadd hJsmul with ⟨T, hT0, hTltTf, hFD⟩
  refine ⟨T, hT0, hTltTf, ?_⟩
  intro t ht
  rcases hFD t ht with ⟨L, hFL, hLval⟩
  refine ⟨L, hFL, ?_⟩
  intro w
  simpa [J] using hLval w


/-- Chart exponential arcs agree with region-flow geodesics: for a second flow `Φ₂` of the
geodesic field whose data ball has radius `R₂ ≥ ‖w‖`, `exp (t • w)` equals the position at
time `t` of the flow trajectory from `(x₀, w)`, for small `|t|`. -/
lemma arc_eq_region (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) (ρe τe : ℝ)
    (hρe : 0 < ρe) (hτe : 0 < τe) (hρeτe : ρe ≤ τe / 4)
    (Φ₁ : E × E → ℝ → E × E)
    (hΦ₁ : ∀ z ∈ closedBall (x₀, 0) 2, Φ₁ z 0 = z ∧
       ∀ t ∈ Ioo (-((3 / 2) * τe)) (((3 / 2) * τe)),
         HasDerivAt (Φ₁ z) (odeField g (Φ₁ z t)) t)
    (exp : E → E)
    (hexpform : ∀ v ∈ ball (0 : E) ρe, exp v = (Φ₁ (x₀, (1 / τe) • v) τe).1)
    (ε₂ : ℝ) (hε₂ : 0 < ε₂) (R₂ : ℝ) (hR₂ : 0 < R₂)
    (Φ₂ : E × E → ℝ → E × E)
    (hΦ₂ : ∀ z ∈ closedBall (x₀, 0) R₂, Φ₂ z 0 = z ∧
       ∀ t ∈ Icc (-ε₂) ε₂, HasDerivAt (Φ₂ z) (odeField g (Φ₂ z t)) t) :
    ∃ ρg > 0, ∀ w : E, ‖w‖ ≤ R₂ → ∀ t : ℝ, |t| < ρg →
      exp (t • w) = (Φ₂ (x₀, w) t).1 := by
  classical
  let T0 : ℝ := (11 / 8) * τe
  have hT0 : 0 < T0 := by dsimp [T0]; positivity
  have hwin1 : Icc (-T0) T0 ⊆ Ioo (-((3 / 2) * τe)) (((3 / 2) * τe)) := by
    intro t ht
    have ht1 : -((11 / 8) * τe) ≤ t := by simpa [T0] using ht.1
    have ht2 : t ≤ (11 / 8) * τe := by simpa [T0] using ht.2
    constructor
    · nlinarith [ht1, hτe]
    · nlinarith [ht2, hτe]
  have hΦ₁₁ : ∀ z ∈ closedBall (x₀, 0) 1, Φ₁ z 0 = z ∧
      ∀ t ∈ Icc (-T0) T0, HasDerivAt (Φ₁ z) (odeField g (Φ₁ z t)) t := by
    intro z hz
    have hz2 : z ∈ closedBall (x₀, 0) 2 := closedBall_subset_closedBall (by norm_num) hz
    constructor
    · exact (hΦ₁ z hz2).1
    · intro t ht
      exact (hΦ₁ z hz2).2 t (hwin1 ht)
  have hτeT0 : τe < T0 := by dsimp [T0]; nlinarith [hτe]
  have hτmem : τe ∈ Ioo (-T0) T0 := by
    constructor
    · change -(11 / 8 * τe) < τe
      nlinarith [hτe]
    · change τe < 11 / 8 * τe
      nlinarith [hτe]
  have hrest : Φ₁ (x₀, 0) τe = (x₀, 0) := by
    exact flow_rest_point g hg hinv (hT := hT0) (x₀ := x₀) (Φ := Φ₁) hΦ₁₁ τe hτmem
  let ρg : ℝ := min (τe / 2) (min ε₂ (ρe / R₂))
  have hρg : 0 < ρg := by
    dsimp [ρg]
    exact lt_min (by positivity) (lt_min hε₂ (div_pos hρe hR₂))
  refine ⟨ρg, hρg, ?_⟩
  intro w hwR t ht
  have htρ : |t| < τe / 2 := lt_of_lt_of_le ht (by dsimp [ρg]; exact min_le_left _ _)
  have htε : |t| < ε₂ := lt_of_lt_of_le ht (by dsimp [ρg]; exact le_trans (min_le_right _ _) (min_le_left _ _))
  have htρe : |t| < ρe / R₂ := lt_of_lt_of_le ht (by
    dsimp [ρg]
    exact le_trans (min_le_right _ _) (min_le_right _ _))
  have hthin : ‖(t / τe) • w‖ ≤ 1 := by
    have hnorm : ‖(t / τe) • w‖ ≤ (|t| / τe) * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hτe]
    have hle1 : (|t| / τe) * ‖w‖ ≤ (|t| / τe) * R₂ := by
      exact mul_le_mul_of_nonneg_left hwR (div_nonneg (abs_nonneg t) (le_of_lt hτe))
    have hle2 : (|t| / τe) * R₂ < 1 := by
      have h1 : |t| * R₂ < ρe := by
        have hq : |t| < ρe / R₂ := htρe
        exact (lt_div_iff₀ hR₂).mp hq
      have hρeτe : ρe ≤ τe / 4 := hρeτe
      have h2 : |t| * R₂ < τe := by nlinarith
      calc
        (|t| / τe) * R₂ = (|t| * R₂) / τe := by ring
        _ < 1 := by
          rw [div_lt_one hτe]
          exact h2
    nlinarith
  have htw_mem : t • w ∈ ball (0 : E) ρe := by
    rw [mem_ball, dist_eq_norm, sub_zero]
    have hnorm : ‖t • w‖ ≤ |t| * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    have hlt : |t| * ‖w‖ < ρe := by
      have h1 : |t| * ‖w‖ ≤ |t| * R₂ := mul_le_mul_of_nonneg_left hwR (abs_nonneg t)
      have h2 : |t| * R₂ < ρe := (lt_div_iff₀ hR₂).mp htρe
      exact lt_of_le_of_lt h1 h2
    exact lt_of_le_of_lt hnorm hlt
  have hray := ray_agreement_big g hg hinv x₀ (ρ₀ := τe) hτe (ε₁ := T0) hT0 hτeT0
    (Φ₁ := Φ₁) hΦ₁₁ (ε₂ := ε₂) hε₂ (R₂ := R₂) (le_of_lt hR₂) (Φ₂ := Φ₂) hΦ₂
    hrest w hwR (by exact lt_min htρ htε) hthin
  have hlhs : exp (t • w) = (Φ₁ (x₀, (1 / τe) • (t • w)) τe).1 := by
    exact hexpform (t • w) htw_mem
  rw [hlhs, hray]



/-- Uniform model normal ball: on a whole ball of bases, the region-flow exponentials
`exp_b v := (Φ (b, τu⁻¹ • v) τu).1` give staying-curve radial minimality with a *uniform*
radius `δu`. -/
theorem uniform_normal_ball (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x₀ : E) (ρu τf : ℝ) (hρu : 0 < ρu) (hτf : 0 < τf)
    (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hPerBase : ∀ b ∈ ball x₀ ρu, ∀ z ∈ closedBall (b, 0) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (b, 0) 2))
    (hLip : ∀ t ∈ Icc (-τf) τf, ∀ b ∈ ball x₀ ρu,
       LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, 0) 1)) :
    ∃ ρB δu τu : ℝ, 0 < ρB ∧ 0 < δu ∧ 0 < τu ∧ ρB ≤ ρu ∧ δu ≤ τu ∧ 2 * τu ≤ τf ∧
      ∀ b ∈ ball x₀ ρB,
        ∀ v ∈ ball (0 : E) δu,
          (∀ c : ℝ → E, c 0 = b → c 1 = expOf b Φ τu v →
            (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O) →
            (∀ s ∈ Icc (0 : ℝ) 1, c s ∈ ball b δu) →
            Real.sqrt ((g b) v v) ≤ mgLength g c 0 1) := by
  exact uniform_normal_ball_aux g hg hinv hsym hpos x₀ ρu τf hρu hτf Lf Φ hPerBase hLip

/-- The segment of the flow-geodesic from `γ s` to `γ t` is the exponential ray of the
region flow at the base `γ s`: `exp_{γ s} ((t - s) • vel s) = γ t`. -/
lemma arc_segment_ident (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) {R0 τf : ℝ} (hR0 : 0 < R0)
    (hR0ge2 : (2 : ℝ) ≤ R0) (hτf : 0 < τf)
    (Φ : E × E → ℝ → E × E)
    (hΦ : ∀ z ∈ closedBall (x₀, 0) R0, Φ z 0 = z ∧
       (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (x₀, 0) (R0 + 1)))
    {w : E} (hw : ‖w‖ ≤ R0) {s t : ℝ} (hst : s ≤ t)
    (hs : |s| < τf / 8) (ht : |t| < τf / 8)
    {τu : ℝ} (hτu : 0 < τu) (hτuτf : 2 * τu ≤ τf)
    (hb0 : ‖(Φ (x₀, w) s).1 - x₀‖ ≤ R0 / 2)
    (hvel : ‖(t - s) • (Φ (x₀, w) s).2‖ ≤ τu) :
    expOf ((Φ (x₀, w) s).1) Φ τu ((t - s) • (Φ (x₀, w) s).2) = (Φ (x₀, w) t).1 := by
  exact arc_segment_ident_aux g hg hinv x₀ hR0 hR0ge2 hτf Φ hΦ (w := w) hw (s := s) (t := t) hst hs ht (τu := τu) hτu hτuτf hb0 hvel

end Submission.Model

namespace Submission.ArcModel

open Submission.Model

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

theorem arc_model_two_sided (g : E → Model.Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x₀ : E) (ρe τe : ℝ) (hρe : 0 < ρe) (hτe : 0 < τe) (hρeτe : ρe ≤ τe / 4)
    (Φ : E × E → ℝ → E × E)
    (hΦ : ∀ z ∈ closedBall (x₀, (0 : E)) 2, Φ z 0 = z ∧
       ∀ t ∈ Ioo (-((3 / 2) * τe)) (((3 / 2) * τe)),
         HasDerivAt (Φ z) (Model.odeField g (Φ z t)) t)
    (exp : E → E) (hexp0 : exp 0 = x₀)
    (hexpform : ∀ v ∈ ball (0 : E) ρe, exp v = (Φ (x₀, (1 / τe) • v) τe).1)
    (hExpC1 : ContDiffOn ℝ 1 exp (ball (0 : E) ρe))
    (K : ℝ) (hK : 0 < K) :
    ∃ ρA > 0, ∀ W : E, ‖W‖ ≤ K → Real.sqrt ((g x₀) W W) = 1 →
      ∀ s t : ℝ, s ≤ t → |s| < ρA → |t| < ρA →
      ∀ c : ℝ → E, c 0 = exp (s • W) → c 1 = exp (t • W) →
        (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O) →
        (∀ u ∈ Icc (0 : ℝ) 1, c u ∈ ball x₀ ρA) →
        t - s ≤ Model.mgLength g c 0 1 := by
  classical
  -- ---- region flow with data radius covering ‖W‖ ≤ K and one more unit ----
  let R0n : NNReal := ⟨K + 3, by positivity⟩
  let r0 : ℝ := K + 3
  have hr0def : (R0n : ℝ) = r0 := by rfl
  have hR0pos : 0 < r0 := by dsimp [r0]; linarith
  have hKleR0 : K ≤ r0 := by dsimp [r0]; linarith
  have hR0ge2 : (2 : ℝ) ≤ (R0n : ℝ) := by rw [hr0def]; linarith
  rcases Submission.Model.region_flow_pkg g hg hinv x₀ R0n hR0ge2 with
    ⟨τf, hτf, ρu, hρu, Lf, Φr, hΦrAll, hCon2r, hLip1r, hLipB, hPerB⟩
  -- uniform normal ball over the bases
  rcases uniform_normal_ball g hg hinv hsym hpos x₀ ρu τf hρu hτf Lf Φr hPerB hLipB with
    ⟨ρB, δu, τu, hρB, hδu, hτu, hρBρu, hδuτu, h2τuτf, hUNB⟩
  -- chart arc = region flow geodesic
  rcases arc_eq_region g hg hinv x₀ ρe τe hρe hτe hρeτe Φ hΦ exp hexpform τf hτf r0 hR0pos
      Φr (by intro z hz; exact ⟨(hΦrAll z hz).1, (hΦrAll z hz).2.1⟩) with ⟨ρg, hρg, hArcId⟩
  -- ---- constants controlling ρA ----
  let Rv : ℝ := r0 + 1
  have hRvpos : 0 < Rv := by dsimp [Rv]; linarith
  let ρA : ℝ := min ρg (min (τf / 8) (min (ρe / (2 * (K + 1))) (min (δu / (3 * (r0 + 2))) (min (ρB / (2 * (r0 + 1))) (min (r0 / (4 * (r0 + 1))) (min (R0n : ℝ) 1))))))
  have hρA : 0 < ρA := by
    dsimp [ρA]
    positivity
  refine ⟨ρA, hρA, ?_⟩
  intro W hWK hWunit s t hst hs ht c hc0 hc1 hcO hcStay
  have hWle : ‖W‖ ≤ r0 := by
    calc
      ‖W‖ ≤ K := hWK
      _ ≤ r0 := hKleR0
  have hmemW : (x₀, W) ∈ closedBall (x₀, (0 : E)) r0 := by
    apply mem_pair_ball x₀ r0 (le_of_lt hR0pos) W hWle
  -- geodesic position/velocity curves of the region flow
  let gamma : ℝ → E := fun l => (Φr (x₀, W) l).1
  let vel : ℝ → E := fun l => (Φr (x₀, W) l).2
  have hΦrAll' : ∀ z ∈ closedBall (x₀, (0 : E)) r0, Φr z 0 = z ∧
      ∀ l ∈ Icc (-τf) τf, HasDerivAt (Φr z) (odeField g (Φr z l)) l := by
    intro z hz
    exact ⟨(hΦrAll z hz).1, (hΦrAll z hz).2.1⟩
  have hsplit := Submission.Model.split_flow_geodesic g hg hinv (x₀, 0) hτf (closedBall (x₀, (0 : E)) r0) Φr hΦrAll' (z := (x₀, W)) hmemW
  let eps : ℝ := τf / 2
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hcgeo : ∀ l ∈ Ioo (-eps) eps, HasDerivAt gamma (vel l) l := by
    intro l hl
    have h1' : -(τf / 2) < l := by simpa [eps] using hl.1
    have h2' : l < τf / 2 := by simpa [eps] using hl.2
    have hl' : l ∈ Ioo (-τf) τf := by constructor <;> nlinarith [h1', h2', hτf]
    simpa [gamma, vel] using (hsplit.1 l hl')
  have hvgeo : ∀ l ∈ Ioo (-eps) eps,
      HasDerivAt vel (accel (g (gamma l)) (fderiv ℝ g (gamma l)) (vel l)) l := by
    intro l hl
    have h1' : -(τf / 2) < l := by simpa [eps] using hl.1
    have h2' : l < τf / 2 := by simpa [eps] using hl.2
    have hl' : l ∈ Ioo (-τf) τf := by constructor <;> nlinarith [h1', h2', hτf]
    simpa [gamma, vel] using (hsplit.2 l hl')
  have hspeed := speed_const g hg hinv hsym (ε := eps) heps (c := gamma) (v := vel) hcgeo hvgeo
  -- parameter smallness facts
  have hρA_ρg : ρA ≤ ρg := by dsimp [ρA]; exact min_le_left _ _
  have hρA_τf8 : ρA ≤ τf / 8 := by dsimp [ρA]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρA_ρe : ρA ≤ ρe / (2 * (K + 1)) := by
    dsimp [ρA]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρA_δu : ρA ≤ δu / (3 * (r0 + 2)) := by
    dsimp [ρA]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρA_ρB : ρA ≤ ρB / (2 * (r0 + 1)) := by
    dsimp [ρA]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hρA_r0 : ρA ≤ r0 / (4 * (r0 + 1)) := by
    dsimp [ρA]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hsA : |s| < ρA := hs
  have htA : |t| < ρA := ht
  have hslt : |s| < ρg := lt_of_lt_of_le hs hρA_ρg
  have htlt : |t| < ρg := lt_of_lt_of_le ht hρA_ρg
  have hsτ : |s| < τf / 8 := lt_of_lt_of_le hs hρA_τf8
  have htτ : |t| < τf / 8 := lt_of_lt_of_le ht hρA_τf8
  have hsw : |s| * ‖W‖ < ρe := by
    have h1 : |s| * ‖W‖ ≤ |s| * K := mul_le_mul_of_nonneg_left hWK (abs_nonneg s)
    have h2 : |s| * K < ρe := by
      have h3 : |s| < ρe / (2 * (K + 1)) := lt_of_lt_of_le hs hρA_ρe
      have hKp : 0 < 2 * (K + 1) := by positivity
      have h4 : |s| * (2 * (K + 1)) < ρe := (lt_div_iff₀ hKp).mp h3
      nlinarith
    nlinarith
  have htw : |t| * ‖W‖ < ρe := by
    have h1 : |t| * ‖W‖ ≤ |t| * K := mul_le_mul_of_nonneg_left hWK (abs_nonneg t)
    have h2 : |t| * K < ρe := by
      have h3 : |t| < ρe / (2 * (K + 1)) := lt_of_lt_of_le ht hρA_ρe
      have hKp : 0 < 2 * (K + 1) := by positivity
      have h4 : |t| * (2 * (K + 1)) < ρe := (lt_div_iff₀ hKp).mp h3
      nlinarith
    nlinarith
  -- ---- identification of the chart arc with the flow geodesic ----
  have harc_s : exp (s • W) = gamma s := by
    have hm : s • W ∈ ball (0 : E) ρe := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      have hnorm : ‖s • W‖ ≤ |s| * ‖W‖ := by rw [norm_smul, Real.norm_eq_abs]
      exact lt_of_le_of_lt hnorm hsw
    have hid := hArcId W hWle s hslt
    simpa [gamma] using hid
  have harc_t : exp (t • W) = gamma t := by
    have hm : t • W ∈ ball (0 : E) ρe := by
      rw [mem_ball, dist_eq_norm, sub_zero]
      have hnorm : ‖t • W‖ ≤ |t| * ‖W‖ := by rw [norm_smul, Real.norm_eq_abs]
      exact lt_of_le_of_lt hnorm htw
    have hid := hArcId W hWle t htlt
    simpa [gamma] using hid
  -- base point and velocity at s
  let b₀ : E := exp (s • W)
  have hb0gamma : b₀ = gamma s := by simpa [b₀] using harc_s
  have hvel0 : vel 0 = W := by
    simpa [vel] using (congrArg Prod.snd (hΦrAll (x₀, W) hmemW).1)
  have hgamma0 : gamma 0 = x₀ := by
    simpa [gamma] using (congrArg Prod.fst (hΦrAll (x₀, W) hmemW).1)
  -- speed conservation along the geodesic
  have hsq : ∀ l ∈ Ioo (-eps) eps, (g (gamma l)) (vel l) (vel l) = (g x₀) W W := by
    intro l hl
    have hf0 : (g (gamma 0)) (vel 0) (vel 0) = (g x₀) W W := by simp [hvel0, hgamma0]
    have hmain := const_deriv_value (ε := eps) heps
      (f := fun u : ℝ => (g (gamma u)) (vel u) (vel u)) (c := (0 : ℝ)) hspeed (t := l) hl
    calc
      (g (gamma l)) (vel l) (vel l) = (g (gamma 0)) (vel 0) (vel 0) := by
        have hmain' : (g (gamma l)) (vel l) (vel l) =
            (g (gamma 0)) (vel 0) (vel 0) + 0 * l := hmain
        nlinarith
      _ = (g x₀) W W := hf0
  have hspeed1 : Real.sqrt ((g (gamma s)) (vel s) (vel s)) = 1 := by
    have hsI' : s ∈ Ioo (-(τf / 2)) (τf / 2) := by
      constructor
      · have hb := (abs_le.mp (le_of_lt hsτ)).1
        nlinarith [hb, hτf]
      · have hb := (abs_le.mp (le_of_lt hsτ)).2
        nlinarith [hb, hτf]
    have hsI : s ∈ Ioo (-eps) eps := by simpa [eps] using hsI'
    rw [hsq s hsI]
    exact hWunit
  have hvelb : ‖(Φr (x₀, W) s).2‖ ≤ r0 + 1 := by
    have hcont : Φr (x₀, W) s ∈ closedBall (x₀, (0 : E)) (r0 + 1) := (hΦrAll (x₀, W) hmemW).2.2 s
    have hd : ‖(Φr (x₀, W) s) - (x₀, 0)‖ ≤ r0 + 1 := by
      simpa [dist_eq_norm] using mem_closedBall.mp hcont
    have hsub : ‖(Φr (x₀, W) s).2‖ ≤ ‖(Φr (x₀, W) s) - (x₀, (0 : E))‖ := by
      have hpair : ((Φr (x₀, W) s) - (x₀, (0 : E))).2 = (Φr (x₀, W) s).2 := by simp
      rw [← hpair]
      exact norm_snd_le (Φr (x₀, W) s - (x₀, (0 : E)))
    calc
      ‖(Φr (x₀, W) s).2‖ ≤ ‖(Φr (x₀, W) s) - (x₀, (0 : E))‖ := hsub
      _ ≤ r0 + 1 := hd
  have hvelbnd : ∀ u : ℝ, ‖vel u‖ ≤ r0 + 1 := by
    intro u
    have hcont : Φr (x₀, W) u ∈ closedBall (x₀, (0 : E)) (r0 + 1) := (hΦrAll (x₀, W) hmemW).2.2 u
    have hd : ‖(Φr (x₀, W) u) - (x₀, 0)‖ ≤ r0 + 1 := by
      simpa [dist_eq_norm] using mem_closedBall.mp hcont
    have hsub : ‖(Φr (x₀, W) u).2‖ ≤ ‖(Φr (x₀, W) u) - (x₀, (0 : E))‖ := by
      have hpair : ((Φr (x₀, W) u) - (x₀, (0 : E))).2 = (Φr (x₀, W) u).2 := by simp
      rw [← hpair]
      exact norm_snd_le (Φr (x₀, W) u - (x₀, (0 : E)))
    calc
      ‖vel u‖ = ‖(Φr (x₀, W) u).2‖ := rfl
      _ ≤ ‖(Φr (x₀, W) u) - (x₀, (0 : E))‖ := hsub
      _ ≤ r0 + 1 := hd
  have hgamma_deriv_at (u : ℝ) (hu : |u| < τf / 8) : HasDerivAt gamma (vel u) u := by
    have h1 : -(τf / 2) < u := by
      have hb := (abs_le.mp (le_of_lt hu)).1
      nlinarith [hb, hτf]
    have h2 : u < τf / 2 := by
      have hb := (abs_le.mp (le_of_lt hu)).2
      nlinarith [hb, hτf]
    exact hcgeo u (by simpa [eps] using ⟨h1, h2⟩)
  have hgamma_bound : ‖gamma s - x₀‖ ≤ (r0 + 1) * |s| := by
    by_cases hs0 : 0 ≤ s
    · have hmain : ‖gamma s - gamma 0‖ ≤ (r0 + 1) * (s - 0) := by
        have hfC : ∀ x ∈ Icc (0 : ℝ) s, HasDerivWithinAt gamma (vel x) (Icc (0 : ℝ) s) x := by
          intro x hx
          have hlt : |x| < τf / 8 := by
            have hx1 : 0 ≤ x := hx.1
            have hx2 : x ≤ s := hx.2
            have hle' : |x| ≤ |s| := by
              rw [abs_of_nonneg hx1, abs_of_nonneg hs0]
              linarith
            exact lt_of_le_of_lt hle' hsτ
          exact (hgamma_deriv_at x hlt).hasDerivWithinAt
        have hseg := norm_image_sub_le_of_norm_deriv_le_segment' (f := gamma)
          (f' := fun u => vel u) hfC (fun x hx => hvelbnd x)
        exact hseg s (right_mem_Icc.mpr hs0)
      have hmain' : ‖gamma s - x₀‖ ≤ (r0 + 1) * s := by
        simpa [hgamma0, sub_zero] using hmain
      rw [abs_of_nonneg hs0]
      exact hmain'
    · have hneg : s ≤ 0 := le_of_not_ge hs0
      have hmain : ‖gamma 0 - gamma s‖ ≤ (r0 + 1) * (0 - s) := by
        have hfC : ∀ x ∈ Icc s (0 : ℝ), HasDerivWithinAt gamma (vel x) (Icc s (0 : ℝ)) x := by
          intro x hx
          have hlt : |x| < τf / 8 := by
            have hx1 : s ≤ x := hx.1
            have hx2 : x ≤ 0 := hx.2
            have hle' : |x| ≤ |s| := by
              rw [abs_of_nonpos hx2, abs_of_nonpos hneg]
              linarith
            exact lt_of_le_of_lt hle' hsτ
          exact (hgamma_deriv_at x hlt).hasDerivWithinAt
        have hseg := norm_image_sub_le_of_norm_deriv_le_segment' (f := gamma)
          (f' := fun u => vel u) hfC (fun x hx => hvelbnd x)
        exact hseg 0 (show (0 : ℝ) ∈ Icc s 0 from ⟨hneg, le_rfl⟩)
      have hmain' : ‖gamma s - x₀‖ ≤ (r0 + 1) * (-s) := by
        simpa [hgamma0, norm_sub_rev] using hmain
      rw [abs_of_nonpos hneg]
      exact hmain'
  have hb0ball : b₀ ∈ ball x₀ ρB := by
    rw [mem_ball, dist_eq_norm]
    have hle : ‖b₀ - x₀‖ < ρB := by
      rw [hb0gamma]
      have h1 : ‖gamma s - x₀‖ ≤ (r0 + 1) * |s| := hgamma_bound
      have h2 : (r0 + 1) * |s| ≤ (r0 + 1) * ρA := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hs) (by positivity : 0 ≤ r0 + 1)
      have h3 : (r0 + 1) * ρA < ρB := by
        have hden : 0 < 2 * (r0 + 1) := by positivity
        have h4 : ρA * (2 * (r0 + 1)) ≤ ρB := (le_div_iff₀ hden).mp hρA_ρB
        have hstep : (r0 + 1) * ρA ≤ ρB / 2 := by nlinarith
        nlinarith
      linarith
    simpa [dist_eq_norm] using hle
  have hb0R0 : ‖(Φr (x₀, W) s).1 - x₀‖ ≤ r0 / 2 := by
    have h1 : ‖gamma s - x₀‖ ≤ (r0 + 1) * |s| := hgamma_bound
    have h2 : (r0 + 1) * |s| ≤ (r0 + 1) * ρA := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hs) (by positivity : 0 ≤ r0 + 1)
    have h3 : (r0 + 1) * ρA ≤ r0 / 2 := by
      have hden : 0 < 4 * (r0 + 1) := by positivity
      have h6 : ρA * (4 * (r0 + 1)) ≤ r0 := (le_div_iff₀ hden).mp hρA_r0
      nlinarith
    nlinarith
  have hb0memΦ : (x₀, W) ∈ closedBall (x₀, (0 : E)) r0 := hmemW
  -- the segment identification at the base b₀
  let v₀ : E := (t - s) • vel s
  have hvsmall : ‖v₀‖ ≤ 2 * ρA * (r0 + 1) := by
    have h1 : ‖v₀‖ ≤ |t - s| * ‖vel s‖ := by
      dsimp [v₀]
      rw [norm_smul, Real.norm_eq_abs]
    have hts : |t - s| ≤ |t| + |s| := by
      have h := norm_add_le t (-s)
      simpa [Real.norm_eq_abs, sub_eq_add_neg, abs_neg] using h
    have hts' : |t - s| ≤ 2 * ρA := by nlinarith [hts, hs, ht]
    have h2a : |t - s| * ‖vel s‖ ≤ (2 * ρA) * ‖vel s‖ := by
      exact mul_le_mul_of_nonneg_right hts' (norm_nonneg (vel s))
    have h2b : (2 * ρA) * ‖vel s‖ ≤ 2 * ρA * (r0 + 1) := by
      exact mul_le_mul_of_nonneg_left hvelb (by positivity : 0 ≤ 2 * ρA)
    nlinarith
  have hδu_big : 2 * ρA * (r0 + 1) < δu := by
    have hden : 0 < 3 * (r0 + 2) := by positivity
    have hle' : ρA * (3 * (r0 + 2)) ≤ δu := (le_div_iff₀ hden).mp hρA_δu
    have hlt' : 2 * ρA * (r0 + 1) < ρA * (3 * (r0 + 2)) := by nlinarith [hρA, hR0pos]
    nlinarith
  have hv0τu : ‖v₀‖ ≤ τu := by nlinarith [hvsmall, hδu_big, hδuτu]
  have hv0δu : ‖v₀‖ < δu := by nlinarith [hvsmall, hδu_big]
  have hv0δu' : v₀ ∈ ball (0 : E) δu := by
    rw [mem_ball, dist_eq_norm, sub_zero]
    exact hv0δu
  have hseg := arc_segment_ident g hg hinv x₀ hR0pos (by rw [← hr0def]; exact hR0ge2) hτf Φr
    (by intro z hz; exact hΦrAll z hz) (w := W) hWle hst hsτ htτ hτu h2τuτf
    (by simpa [gamma] using hb0R0) hv0τu
  have hb0b : b₀ = (Φr (x₀, W) s).1 := by
    simpa [gamma] using hb0gamma
  have harc_seg : expOf b₀ Φr τu v₀ = exp (t • W) := by
    have hm : expOf ((Φr (x₀, W) s).1) Φr τu ((t - s) • (Φr (x₀, W) s).2) = (Φr (x₀, W) t).1 := hseg
    have hb : b₀ = (Φr (x₀, W) s).1 := hb0b
    have hv : v₀ = (t - s) • (Φr (x₀, W) s).2 := rfl
    rw [hb, hv, hm]
    simpa [gamma] using harc_t.symm
  have hc1' : c 1 = expOf b₀ Φr τu v₀ := by
    rw [hc1]
    exact harc_seg.symm
  -- the staying curve lies in the normal ball of b₀
  have hb0d : ‖b₀ - x₀‖ ≤ (r0 + 1) * |s| := by
    rw [hb0gamma]
    exact hgamma_bound
  have hb0d' : ‖b₀ - x₀‖ ≤ (r0 + 1) * ρA := by
    exact le_trans hb0d (mul_le_mul_of_nonneg_left (le_of_lt hs) (by positivity : 0 ≤ r0 + 1))
  have hballx0b : ball x₀ ρA ⊆ ball b₀ δu := by
    intro y hy
    rw [mem_ball, dist_eq_norm]
    have hyb : ‖y - x₀‖ < ρA := by simpa [dist_eq_norm] using hy
    have hb0d'' : ‖x₀ - b₀‖ ≤ (r0 + 1) * ρA := by simpa [norm_sub_rev] using hb0d'
    have hle : ‖y - b₀‖ ≤ ‖y - x₀‖ + ‖x₀ - b₀‖ := by
      exact norm_sub_le_norm_sub_add_norm_sub y x₀ b₀
    have h2 : ‖y - x₀‖ + ‖x₀ - b₀‖ < δu := by
      have hden : 0 < 3 * (r0 + 2) := by positivity
      have hle' : ρA * (3 * (r0 + 2)) ≤ δu := (le_div_iff₀ hden).mp hρA_δu
      nlinarith [hyb, hb0d'', hρA, hR0pos]
    exact lt_of_le_of_lt hle h2
  have hcStayB : ∀ u ∈ Icc (0 : ℝ) 1, c u ∈ ball b₀ δu := by
    intro u hu
    exact hballx0b (hcStay u hu)
  -- per-base minimality at b₀
  have hmin := hUNB b₀ hb0ball v₀ hv0δu' c (by simpa [b₀] using hc0) hc1' hcO hcStayB
  -- metric norm of v₀ is t - s
  have hsqrtv : Real.sqrt ((g b₀) v₀ v₀) = t - s := by
    have hquad : (g b₀) v₀ v₀ = (t - s) ^ 2 * ((g b₀) (vel s) (vel s)) := by
      dsimp [v₀]
      rw [bilin_smul_left (g b₀) (t - s) (vel s) ((t - s) • vel s)]
      rw [bilin_smul_right (g b₀) (t - s) (vel s) (vel s)]
      ring
    have hunitq : (g b₀) (vel s) (vel s) = 1 := by
      have hsI' : s ∈ Ioo (-(τf / 2)) (τf / 2) := by
        constructor
        · have hb := (abs_le.mp (le_of_lt hsτ)).1
          nlinarith [hb, hτf]
        · have hb := (abs_le.mp (le_of_lt hsτ)).2
          nlinarith [hb, hτf]
      have hsI : s ∈ Ioo (-eps) eps := by simpa [eps] using hsI'
      have hb0q : (g b₀) (vel s) (vel s) = (g (gamma s)) (vel s) (vel s) := by
        rw [hb0gamma]
      have hnonneg : 0 ≤ (g x₀) W W := by
        by_cases hW0 : W = 0
        · simp [hW0]
        · exact le_of_lt (hpos x₀ W hW0)
      have hval : (g x₀) W W = 1 := by
        have hsqr2 : (Real.sqrt ((g x₀) W W)) ^ 2 = (g x₀) W W := Real.sq_sqrt hnonneg
        calc
          (g x₀) W W = (Real.sqrt ((g x₀) W W)) ^ 2 := hsqr2.symm
          _ = 1 := by rw [hWunit]; norm_num
      calc
        (g b₀) (vel s) (vel s) = (g (gamma s)) (vel s) (vel s) := hb0q
        _ = (g x₀) W W := hsq s hsI
        _ = 1 := hval
    have htsge : 0 ≤ t - s := by linarith
    have hquad' : (g b₀) v₀ v₀ = (t - s) ^ 2 := by
      rw [hquad, hunitq]
      ring
    have hnn : 0 ≤ (g b₀) v₀ v₀ := by
      by_cases hv0 : v₀ = 0
      · simp [hv0]
      · exact le_of_lt (hpos b₀ v₀ hv0)
    calc
      Real.sqrt ((g b₀) v₀ v₀) = Real.sqrt ((t - s) ^ 2) := by rw [hquad']
      _ = t - s := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg htsge]
  have hfin : t - s ≤ mgLength g c 0 1 := by
    rwa [← hsqrtv]
  exact hfin

end
end Submission.ArcModel
