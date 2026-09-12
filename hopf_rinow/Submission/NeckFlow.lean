import ChallengeDeps
import Submission.ModelArc
import Submission.ModelExpDiffeo2
import Submission.ModelExpC1
import Submission.ArcModel
import Submission.ModelFlowScale
import Submission.ModelUniq
import Submission.ModelSpeed
import Submission.NeckModel
import Mathlib

/-!
# A model geodesic ending at x0 is eventually an exp-ray (child task)

Prove COMPLETELY `flow_limit_ray` (replace the placeholder).

Model-level.  `g` C³ symmetric positive definite; `Φ` is a flow of the geodesic field
`Submission.Model.odeField g` near `(x0, 0)` over times `Ioo (-3τe/2) (3τe/2)` (exactly the
chart-normal data of `chart_normal_forward`), and `expm v := (Φ (x0, (1/τe)•v) τe).1` is the
model exponential at `x0` with `expm 0 = x0` and `ContDiffOn 1 expm (ball 0 ρe)`.

`(c, vel)` solves the model geodesic ODE on `(t1, b)`: HasDerivAt c (vel t) t and
HasDerivAt vel (accel ...) t, with constant model speed `cR > 0`, and `c t → x0` as `t → b⁻`.
Conclusion: near `b`, `c` is the exp-ray `t ↦ expm ((t-b) • w)` with `√((g x0) w w) = cR`.

## Why true / proof route

1. Speed is constant: `√((g (c t)) (vel t) (vel t)) = cR` is assumed.  Near `b`, `c t` is
   close to `x0`; since `g` is positive definite and continuous, on a small closed ball
   around `x0` there is `m > 0` with `(g y) X X ≥ m·‖X‖²`, so `‖vel t‖ ≤ cR/√m` for `t` near
   `b`.  (Finite-dimensional; use `quad_ellipsoid_bound` or continuity + compactness.)
2. `(c, vel)` is an integral curve of the smooth ODE `z' = odeField g z`; on `(t1,b)` the pair
   `(c,vel)` satisfies it (combine the two HasDerivAt).  Take `t0 < b` close to `b` with
   `(c t0, vel t0)` in the domain of the flow `Φ` (closedBall (x0,0) 2) and `b - t0 < τe`-ish.
   By ODE uniqueness (`Submission.Model.unique_geodesic`), for `t ∈ (t0,b)`:
   `(c t, vel t) = Φ (c t0, vel t0) (t - t0)`.
3. Extend past `b`: the flow from `(c t0, vel t0)` is defined on `Ioo (-3τe/2) (3τe/2)`; since
   `b - t0` is small the extension reaches `b` and beyond; the extended curve (call it `c̃`)
   is smooth and satisfies `c̃ t = (Φ (c t0, vel t0) (t-t0)).1` for `t` in an interval around
   `b`, and equals `c` on `(t0,b)`.
4. Limit velocity: because `vel` is bounded and `(c,vel)` satisfies the ODE with smooth field,
   `(c t, vel t)` has a limit as `t → b⁻`; let `w` be the second-component limit
   (take a convergent subsequence of a bounded sequence via finite-dimensionality, or prove
   uniform continuity from bounded `vel`-derivative; be careful and rigorous).
   Then `(c̃ b, c̃' b) = (x0, w)` and `c̃` is the flow curve of `Φ` through `(x0,w)` at time `b`
   (use the flow property/ODE uniqueness again with base `t0 → b⁻` and continuity of the flow
   in the initial data — `uniform_normal_ball`-type Lipschitz or `flow_exp_local_diffeomorphism`).
5. Identify with `expm`: `c̃ t = (Φ (x0, w) (t-b)).1` for `t` near `b`.  By flow scaling
   (`Submission.Model.flow_scaling`) and `hexpform`, `(Φ (x0, w) s).1 = expm (s • w)` for
   small `|s|` (with `s := t-b < 0` fine as long as `(t-b)•w ∈ ball 0 ρe`).  Hence
   `c t = expm ((t-b) • w)` on `(b-δ, b)`.  Finally `√((g x0) w w) = cR` from the constant
   speed and `c t → x0`, `vel t → w`.

Feel free to add helper lemmas.  You may assume `t1 < b` (open interval) and add any
natural regularity hypothesis needed for the boundedness constants (e.g. `hpos`).  Keep the
name `flow_limit_ray`.  No placeholders may remain.
-/

open scoped ENNReal Topology
open Set Filter Metric
open Bundle

namespace Submission
namespace NeckFlow

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

open Submission.Model
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- uniform coercivity of `g` on a small ball around `x0` -/
lemma g_coerce_near (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u) (x0 : E) :
    ∃ m δg : ℝ, 0 < m ∧ 0 < δg ∧
      (∀ y ∈ ball x0 δg, ∀ X : E, m * ‖X‖ ^ 2 ≤ (g y) X X) := by
  letI : NormedAddCommGroup (Bilin E) := inferInstance
  letI : NormedSpace ℝ (Bilin E) := inferInstance
  rcases Submission.quad_ellipsoid_bound (g x0) (hpos x0) with ⟨m0, hm00, hmb⟩
  have hm2 : 0 < m0 / 2 := by positivity
  have hgc : Continuous g := hg.continuous
  have hc : ∀ᶠ y in 𝓝 x0, dist (g y) (g x0) < m0 / 2 :=
    (Metric.tendsto_nhds.mp hgc.continuousAt) (m0 / 2) hm2
  rcases Metric.mem_nhds_iff.mp hc with ⟨δg, hδg0, hball⟩
  refine ⟨m0 / 2, δg, hm2, hδg0, ?_⟩
  intro y hy X
  have hclose : dist (g y) (g x0) < m0 / 2 := hball hy
  have hyg : ‖g y - g x0‖ ≤ m0 / 2 := by
    simpa [dist_eq_norm] using le_of_lt hclose
  have heqfun : g y = g x0 + (g y - g x0) := by
    ext w
    abel
  have hsplit : (g y) X X = (g x0) X X + ((g y - g x0) X) X := by
    rw [heqfun]
    simp
  have hnorm1 : ‖((g y - g x0) X) X‖ ≤ ‖(g y - g x0) X‖ * ‖X‖ :=
    ((g y - g x0) X).le_opNorm X
  have hnorm2 : ‖(g y - g x0) X‖ ≤ ‖g y - g x0‖ * ‖X‖ :=
    (g y - g x0).le_opNorm X
  have h1 : ‖((g y - g x0) X) X‖ ≤ ‖g y - g x0‖ * ‖X‖ ^ 2 := by
    calc
      ‖((g y - g x0) X) X‖ ≤ ‖(g y - g x0) X‖ * ‖X‖ := hnorm1
      _ ≤ (‖g y - g x0‖ * ‖X‖) * ‖X‖ := mul_le_mul_of_nonneg_right hnorm2 (norm_nonneg X)
      _ = ‖g y - g x0‖ * ‖X‖ ^ 2 := by ring
  have h1m : ‖((g y - g x0) X) X‖ ≤ (m0 / 2) * ‖X‖ ^ 2 := by
    calc
      ‖((g y - g x0) X) X‖ ≤ ‖g y - g x0‖ * ‖X‖ ^ 2 := h1
      _ ≤ (m0 / 2) * ‖X‖ ^ 2 := mul_le_mul_of_nonneg_right hyg (sq_nonneg ‖X‖)
  have hmain := hmb X
  have hL : (g x0) X X - ‖((g y - g x0) X) X‖ ≤ (g y) X X := by
    rw [hsplit]
    have hterm : -‖((g y - g x0) X) X‖ ≤ ((g y - g x0) X) X := by
      simpa using neg_le_neg (neg_le_abs (((g y - g x0) X) X))
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (add_le_add_left hterm ((g x0) X X))
  have hA : (m0 / 2) * ‖X‖ ^ 2 ≤ (g x0) X X - ‖((g y - g x0) X) X‖ := by
    calc
      (m0 / 2) * ‖X‖ ^ 2 = m0 * ‖X‖ ^ 2 - (m0 / 2) * ‖X‖ ^ 2 := by ring
      _ ≤ m0 * ‖X‖ ^ 2 - ‖((g y - g x0) X) X‖ := sub_le_sub_left h1m (m0 * ‖X‖ ^ 2)
      _ ≤ (g x0) X X - ‖((g y - g x0) X) X‖ := sub_le_sub_right hmain ‖((g y - g x0) X) X‖
  exact le_trans hA hL

/-- velocity is bounded on a left-neighbourhood of `b` -/
lemma bound_vel_near (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x0 : E) {cR : ℝ} (hcR : 0 < cR) {b t1 : ℝ} (ht1 : t1 < b)
    {c vel : ℝ → E}
    (hclim : Tendsto c (𝓝[Iio b] b) (𝓝 x0))
    (hcspeed : ∀ t ∈ Ioo t1 b, Real.sqrt ((g (c t)) (vel t) (vel t)) = cR) :
    ∃ t2 Mb : ℝ, t1 < t2 ∧ t2 < b ∧ 0 < Mb ∧
      (∀ t ∈ Ioo t2 b, ‖c t - x0‖ < 1 ∧ ‖vel t‖ ≤ Mb) := by
  classical
  rcases g_coerce_near g hg hpos x0 with ⟨m, δg, hm0, hδg0, hcoerce⟩
  let δ : ℝ := min δg 1
  have hδ0 : 0 < δ := by dsimp [δ]; exact lt_min hδg0 (by norm_num)
  have hδ_le : δ ≤ δg := by dsimp [δ]; exact min_le_left _ _
  have hδ_le1 : δ ≤ 1 := by dsimp [δ]; exact min_le_right _ _
  have hev : ∀ᶠ t in 𝓝[Iio b] b, dist (c t) x0 < δ :=
    (Metric.tendsto_nhds.mp hclim) δ hδ0
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hev with ⟨u, hu, hsub⟩
  rcases Metric.mem_nhds_iff.mp hu with ⟨ε, hε0, hball⟩
  have hε : 0 < ε := hε0
  let t2 : ℝ := (b + max t1 (b - ε)) / 2
  have hmax_lt_b : max t1 (b - ε) < b := by
    exact max_lt ht1 (by linarith)
  have ht2_gt : max t1 (b - ε) < t2 := by
    dsimp [t2]
    linarith
  have ht2b : t2 < b := by
    dsimp [t2]
    linarith
  have ht2_t1 : t1 < t2 := lt_of_le_of_lt (le_max_left t1 (b - ε)) ht2_gt
  have ht2_bε : b - ε < t2 := lt_of_le_of_lt (le_max_right t1 (b - ε)) ht2_gt
  let Mb : ℝ := Real.sqrt (cR ^ 2 / m) + 1
  have hMb0 : 0 < Mb := by
    dsimp [Mb]
    positivity
  refine ⟨t2, Mb, ht2_t1, ht2b, hMb0, ?_⟩
  intro t ht
  have ht_bε : b - ε < t := lt_trans ht2_bε ht.1
  have htb : t < b := ht.2
  have htball : t ∈ ball b ε := by
    simp [dist_eq_norm]
    have hlt : |t - b| < ε := by
      rw [abs_of_nonpos (by linarith : t - b ≤ 0)]
      linarith
    linarith
  have hmem : t ∈ u ∩ Iio b := ⟨hball htball, htb⟩
  have hdist : dist (c t) x0 < δ := hsub hmem
  have hcδ : ‖c t - x0‖ < δ := by simpa [dist_eq_norm] using hdist
  have hc1 : ‖c t - x0‖ < 1 := lt_of_lt_of_le hcδ hδ_le1
  constructor
  · exact hc1
  · have htI : t ∈ Ioo t1 b := ⟨lt_trans ht2_t1 ht.1, ht.2⟩
    have hsq : Real.sqrt ((g (c t)) (vel t) (vel t)) = cR := hcspeed t htI
    have hyball : c t ∈ ball x0 δg := by
      have hlt : ‖c t - x0‖ < δg := lt_of_lt_of_le hcδ hδ_le
      simpa [dist_eq_norm, mem_ball] using hlt
    have hco := hcoerce (c t) hyball (vel t)
    have hQnn : 0 ≤ (g (c t)) (vel t) (vel t) := by
      calc
        0 ≤ m * ‖vel t‖ ^ 2 := mul_nonneg (le_of_lt hm0) (sq_nonneg ‖vel t‖)
        _ ≤ (g (c t)) (vel t) (vel t) := hco
    have hQ : (g (c t)) (vel t) (vel t) = cR ^ 2 := by
      calc
        (g (c t)) (vel t) (vel t) = (Real.sqrt ((g (c t)) (vel t) (vel t))) ^ 2 := by
          rw [Real.sq_sqrt hQnn]
        _ = cR ^ 2 := by rw [hsq]
    have hqcR : m * ‖vel t‖ ^ 2 ≤ cR ^ 2 := by
      calc
        m * ‖vel t‖ ^ 2 ≤ (g (c t)) (vel t) (vel t) := hco
        _ = cR ^ 2 := hQ
    have hq2 : ‖vel t‖ ^ 2 ≤ cR ^ 2 / m := by
      exact (le_div_iff₀ hm0).mpr (by simpa [mul_comm] using hqcR)
    have hsqrt : ‖vel t‖ ≤ Real.sqrt (cR ^ 2 / m) := by
      have hmono := Real.sqrt_le_sqrt hq2
      have hleft : Real.sqrt (‖vel t‖ ^ 2) = ‖vel t‖ := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg (vel t))]
      simpa [hleft] using hmono
    dsimp [Mb]
    linarith

/-- Two solutions of the geodesic pair-ODE on an open interval that agree at an interior point
agree everywhere on the interval. -/
lemma pair_ode_eq_on (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {a b : ℝ} {z1 z2 : ℝ → E × E}
    (h1 : ∀ t ∈ Ioo a b, HasDerivAt z1 (odeField g (z1 t)) t)
    (h2 : ∀ t ∈ Ioo a b, HasDerivAt z2 (odeField g (z2 t)) t)
    {t0 : ℝ} (ht0 : t0 ∈ Ioo a b) (heq : z1 t0 = z2 t0) :
    ∀ t ∈ Ioo a b, z1 t = z2 t := by
  have hloc (t₁ : ℝ) (ht₁ : t₁ ∈ Ioo a b) (heq₁ : z1 t₁ = z2 t₁) :
      z1 =ᶠ[𝓝 t₁] z2 := by
    have hcd : ContDiffAt ℝ 1 (odeField g) (z1 t₁) := by
      exact odeField_contDiffAt g hg hinv (z1 t₁).1 (z1 t₁).2
    have hsf : HasStrictFDerivAt (odeField g) (fderiv ℝ (odeField g) (z1 t₁)) (z1 t₁) :=
      hcd.hasStrictFDerivAt one_ne_zero
    rcases hsf.exists_lipschitzOnWith with ⟨K, s0, hs0, hlip0⟩
    have hmem₁ : ∀ᶠ t in 𝓝 t₁, z1 t ∈ s0 :=
      (h1 t₁ ht₁).continuousAt.preimage_mem_nhds hs0
    have hmem₂ : ∀ᶠ t in 𝓝 t₁, z2 t ∈ s0 := by
      have hs0' : s0 ∈ 𝓝 (z2 t₁) := by rwa [heq₁] at hs0
      exact (h2 t₁ ht₁).continuousAt.preimage_mem_nhds hs0'
    have hder₁ : ∀ᶠ t in 𝓝 t₁, HasDerivAt z1 (odeField g (z1 t)) t := by
      filter_upwards [Ioo_mem_nhds ht₁.1 ht₁.2] with t ht
      exact h1 t ht
    have hder₂ : ∀ᶠ t in 𝓝 t₁, HasDerivAt z2 (odeField g (z2 t)) t := by
      filter_upwards [Ioo_mem_nhds ht₁.1 ht₁.2] with t ht
      exact h2 t ht
    exact ODE_solution_unique_of_eventually (v := fun _ => odeField g) (s := fun _ => s0)
      (Filter.Eventually.of_forall (fun _ => hlip0)) (hder₁.and hmem₁) (hder₂.and hmem₂) heq₁
  set u : Set ℝ := {t | z1 t = z2 t} ∩ Ioo a b
  have hu_open : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    intro t₁ ht₁
    have ht₁ag : z1 t₁ = z2 t₁ := ht₁.1
    have ht₁I : t₁ ∈ Ioo a b := ht₁.2
    have heq_t₁ : z1 =ᶠ[𝓝 t₁] z2 := hloc t₁ ht₁I ht₁ag
    apply (heq_t₁.and (Ioo_mem_nhds ht₁I.1 ht₁I.2)).mono
    intro t ht
    exact ⟨ht.1, ht.2⟩
  have hu_nonempty : (Ioo a b ∩ u).Nonempty := by
    refine ⟨t0, ht0, ?_⟩
    exact ⟨heq, ht0⟩
  have hu_closed : closure u ∩ Ioo a b ⊆ u := by
    intro t ht
    have htI : t ∈ Ioo a b := ht.2
    have htAg : z1 t = z2 t := by
      by_contra hne
      rcases t2_separation hne with ⟨U, V, hUo, hVo, hxU, hxV, hUV⟩
      have hpre1 : z1 ⁻¹' U ∈ 𝓝 t :=
        (h1 t htI).continuousAt.preimage_mem_nhds (hUo.mem_nhds hxU)
      have hpre2 : z2 ⁻¹' V ∈ 𝓝 t :=
        (h2 t htI).continuousAt.preimage_mem_nhds (hVo.mem_nhds hxV)
      let W : Set ℝ := z1 ⁻¹' U ∩ z2 ⁻¹' V
      have hW : W ∈ 𝓝 t := Filter.inter_mem hpre1 hpre2
      have hUVempty : U ∩ V = ∅ := by
        simpa [Set.disjoint_iff] using hUV
      have hWu : W ∩ u = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro s hs
        have hsW : s ∈ W := hs.1
        have hsu : s ∈ u := hs.2
        have hmemU : z1 s ∈ U := hsW.1
        have hmemV : z2 s ∈ V := hsW.2
        have hEq : z1 s = z2 s := hsu.1
        have hmemV' : z1 s ∈ V := by simpa [hEq] using hmemV
        have hx : z1 s ∈ U ∩ V := ⟨hmemU, hmemV'⟩
        rw [hUVempty] at hx
        simp at hx
      rcases (_root_.mem_nhds_iff.mp hW) with ⟨O, hOW, hOo, htO⟩
      have hclO : (O ∩ u).Nonempty := (_root_.mem_closure_iff.mp ht.1) O hOo htO
      have hOempty : O ∩ u = ∅ := by
        have hsubW : O ∩ u ⊆ W ∩ u := inter_subset_inter_left u hOW
        rw [hWu] at hsubW
        exact subset_empty_iff.mp hsubW
      rw [hOempty] at hclO
      exact not_nonempty_empty hclO
    exact ⟨htAg, htI⟩
  have hsub : Ioo a b ⊆ u := by
    exact isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := u)
      hu_open hu_nonempty hu_closed
  intro t ht
  have hmem := hsub ht
  exact hmem.1

/-- Main: model geodesic ending at x0 is eventually an exp-ray -/
theorem flow_limit_ray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x0 : E) {τe : ℝ} (hτe : 0 < τe)
    (Φ : E × E → ℝ → E × E)
    (hΦ : ∀ z ∈ closedBall (x0, 0) 2, Φ z 0 = z ∧
       ∀ t ∈ Ioo (-((3 / 2) * τe)) (((3 / 2) * τe)),
         HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    {ρe : ℝ} (hρe : 0 < ρe) (hρeτe : ρe ≤ τe / 4)
    (expm : E → E) (hexp0 : expm 0 = x0)
    (hexpform : ∀ v ∈ ball (0 : E) ρe, expm v = (Φ (x0, (1 / τe) • v) τe).1)
    {cR : ℝ} (hcR : 0 < cR)
    {b t1 : ℝ} (ht1 : t1 < b)
    {c vel : ℝ → E}
    (hcder : ∀ t ∈ Ioo t1 b, HasDerivAt c (vel t) t)
    (hvder : ∀ t ∈ Ioo t1 b,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
    (hclim : Tendsto c (𝓝[Iio b] b) (𝓝 x0))
    (hcspeed : ∀ t ∈ Ioo t1 b, Real.sqrt ((g (c t)) (vel t) (vel t)) = cR) :
    ∃ w : E, Real.sqrt ((g x0) w w) = cR ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo (b - δ) b, c t = expm ((t - b) • w) := by
  classical
  letI : NormedAddCommGroup (Bilin E) := inferInstance
  letI : NormedSpace ℝ (Bilin E) := inferInstance
  haveI : (𝓝[Iio b] b).NeBot := nhdsWithin_Iio_neBot (le_rfl : b ≤ b)
  let z : ℝ → E × E := fun t => (c t, vel t)
  have hzder (t : ℝ) (ht : t ∈ Ioo t1 b) : HasDerivAt z (odeField g (z t)) t := by
    dsimp [z]
    exact ((hcder t ht).prodMk (hvder t ht)).congr_deriv (by simp [odeField])
  rcases bound_vel_near g hg hpos x0 hcR ht1 hclim hcspeed with ⟨t2, Mb, ht2_t1, ht2b, hMb0, hbnd⟩
  let R0 : ℝ := Mb + 3
  have hR0nonneg : 0 ≤ R0 := by dsimp [R0]; linarith
  have hR0ge2 : (2 : ℝ) ≤ R0 := by dsimp [R0]; linarith
  rcases Submission.Model.region_flow_pkg g hg hinv x0 ⟨R0, hR0nonneg⟩ hR0ge2 with
    ⟨Tf, hTf, ρu, hρu, L, Φr, hΦrAll, hCon2r, hLip1, hLipB, hPB⟩
  let t0 : ℝ := (b + max t2 (b - Tf)) / 2
  have hmax_lt_b : max t2 (b - Tf) < b := by
    exact max_lt ht2b (by linarith)
  have ht0_gt : max t2 (b - Tf) < t0 := by dsimp [t0]; linarith
  have ht0b : t0 < b := by dsimp [t0]; linarith
  have ht0_gt2 : t2 < t0 := lt_of_le_of_lt (le_max_left t2 (b - Tf)) ht0_gt
  have ht0_gtbT : b - Tf < t0 := lt_of_le_of_lt (le_max_right t2 (b - Tf)) ht0_gt
  have ht0_t1 : t1 < t0 := lt_trans ht2_t1 ht0_gt2
  have ht0I : t0 ∈ Ioo t1 b := ⟨ht0_t1, ht0b⟩
  let u0 : ℝ := b - t0
  have hu0pos : 0 < u0 := by dsimp [u0]; linarith
  have hu0T : u0 < Tf := by dsimp [u0]; linarith
  let z0 : E × E := (c t0, vel t0)
  have hbnd_t0 := hbnd t0 ⟨ht0_gt2, ht0b⟩
  have hnorm_pair_le (a b0 : E) : ‖(a, b0)‖ ≤ ‖a‖ + ‖b0‖ := by
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg b0)) (le_add_of_nonneg_left (norm_nonneg a))
  have hz0mem : z0 ∈ closedBall (x0, (0 : E)) R0 := by
    rw [mem_closedBall, dist_eq_norm]
    have hnorm : ‖(c t0 - x0, vel t0)‖ ≤ ‖c t0 - x0‖ + ‖vel t0‖ := hnorm_pair_le _ _
    have hle1 : ‖c t0 - x0‖ + ‖vel t0‖ ≤ R0 := by
      dsimp [R0]
      nlinarith [hbnd_t0.1, hbnd_t0.2]
    have hfin : ‖(c t0 - x0, vel t0)‖ ≤ R0 := le_trans hnorm hle1
    dsimp [z0]
    simpa using hfin
  have hΦr0 : Φr z0 0 = z0 := (hΦrAll z0 hz0mem).1
  have hΦrder (s : ℝ) (hs : s ∈ Ioo (-Tf) Tf) :
      HasDerivAt (Φr z0) (odeField g (Φr z0 s)) s := by
    have hs' : s ∈ Icc (-Tf) Tf := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    exact (hΦrAll z0 hz0mem).2.1 s hs'
  let p0 : ℝ := min (Tf / 2) ((t0 - t1) / 2)
  have hp00 : 0 < p0 := by
    dsimp [p0]
    exact lt_min (by positivity) (by positivity)
  let a0 : ℝ := t0 - p0
  have hp0_le : p0 ≤ (t0 - t1) / 2 := by dsimp [p0]; exact min_le_right _ _
  have ha0_t1 : t1 < a0 := by
    dsimp [a0]
    linarith
  have ha0_t0 : a0 < t0 := by dsimp [a0]; linarith
  have hp0_Tf : p0 < Tf := by
    dsimp [p0]
    have h1 : Tf / 2 < Tf := by linarith
    exact lt_of_le_of_lt (min_le_left _ _) h1
  have hFder (t : ℝ) (ht : t ∈ Ioo a0 b) :
      HasDerivAt (fun s : ℝ => Φr z0 (s - t0)) (odeField g (Φr z0 (t - t0))) t := by
    have hsh : HasDerivAt (fun s : ℝ => s - t0) 1 t := (hasDerivAt_id t).sub_const t0
    have htm : t - t0 ∈ Ioo (-Tf) Tf := by
      constructor
      · have h1 : -p0 < t - t0 := by linarith [ht.1]
        have h2 : -Tf < -p0 := by linarith [hp0_Tf]
        linarith
      · have h1 : t - t0 < u0 := by dsimp [u0]; linarith [ht.2]
        linarith [hu0T]
    have hder_at : HasDerivAt (Φr z0) (odeField g (Φr z0 (t - t0))) (t - t0) := hΦrder (t - t0) htm
    have hc := HasDerivAt.scomp (x := t) (g₁ := fun u : ℝ => Φr z0 u) (hg := hder_at)
      (h := fun s : ℝ => s - t0) (h' := 1) (hh := hsh)
    simpa [one_smul, Function.comp_def] using hc
  have hzder2 (t : ℝ) (ht : t ∈ Ioo a0 b) : HasDerivAt z (odeField g (z t)) t := by
    exact hzder t ⟨lt_trans ha0_t1 ht.1, ht.2⟩
  have hEqFlow : ∀ t ∈ Ioo a0 b, z t = Φr z0 (t - t0) := by
    exact pair_ode_eq_on g hg hinv (a := a0) (b := b) (z1 := z) (z2 := fun t => Φr z0 (t - t0))
      hzder2 hFder ⟨ha0_t0, ht0b⟩ (by simpa [z, z0] using hΦr0.symm)
  have hzTend : Tendsto z (𝓝[Iio b] b) (𝓝 (Φr z0 u0)) := by
    have hu0memT : u0 ∈ Ioo (-Tf) Tf := ⟨by linarith, hu0T⟩
    have hcon : ContinuousAt (fun s : ℝ => Φr z0 s) u0 := (hΦrder u0 hu0memT).continuousAt
    have htend_id : Tendsto (fun t : ℝ => t) (𝓝[Iio b] b) (𝓝 b) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have htend : Tendsto (fun t : ℝ => t - t0) (𝓝[Iio b] b) (𝓝 (b - t0)) :=
      htend_id.sub tendsto_const_nhds
    have htend' : Tendsto (fun t : ℝ => t - t0) (𝓝[Iio b] b) (𝓝 u0) := by
      simpa [u0] using htend
    have hshift : Tendsto (fun t : ℝ => Φr z0 (t - t0)) (𝓝[Iio b] b) (𝓝 (Φr z0 u0)) :=
      hcon.tendsto.comp htend'
    have hset : Ioo t0 b ∈ 𝓝[Iio b] b := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Ioi t0, isOpen_Ioi.mem_nhds ht0b, ?_⟩
      intro x hx
      exact ⟨hx.1, hx.2⟩
    have heqEv : (fun t : ℝ => z t) =ᶠ[𝓝[Iio b] b] (fun t : ℝ => Φr z0 (t - t0)) := by
      filter_upwards [hset] with t ht
      have htI : t ∈ Ioo a0 b := ⟨lt_trans ha0_t0 ht.1, ht.2⟩
      exact hEqFlow t htI
    exact Tendsto.congr' heqEv.symm hshift
  let xw : E × E := Φr z0 u0
  have hxw1 : xw.1 = x0 := by
    have hfst : Tendsto (fun t : ℝ => (z t).1) (𝓝[Iio b] b) (𝓝 xw.1) :=
      (continuousAt_fst.tendsto).comp hzTend
    have hc1 : Tendsto (fun t : ℝ => (z t).1) (𝓝[Iio b] b) (𝓝 x0) := by
      simpa [z] using hclim
    exact tendsto_nhds_unique hfst hc1
  let w : E := xw.2
  have hxw : xw = (x0, w) := by
    dsimp [w]
    exact Prod.ext hxw1 rfl
  have hwMb : ‖w‖ ≤ Mb := by
    have hsnd : Tendsto (fun t : ℝ => (z t).2) (𝓝[Iio b] b) (𝓝 xw.2) :=
      (continuousAt_snd.tendsto).comp hzTend
    have hnormTend : Tendsto (fun t : ℝ => ‖(z t).2‖) (𝓝[Iio b] b) (𝓝 ‖xw.2‖) :=
      (continuous_norm.continuousAt.tendsto).comp hsnd
    have hset : Ioo t2 b ∈ 𝓝[Iio b] b := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Ioi t2, isOpen_Ioi.mem_nhds ht2b, ?_⟩
      intro x hx
      exact ⟨hx.1, hx.2⟩
    have hboundEv : ∀ᶠ t in 𝓝[Iio b] b, ‖(z t).2‖ ≤ Mb := by
      filter_upwards [hset] with t ht
      have hb := hbnd t ht
      dsimp [z]
      exact hb.2
    have h := le_of_tendsto hnormTend hboundEv
    dsimp [w]
    simpa using h
  have hxw0mem : (x0, w) ∈ closedBall (x0, (0 : E)) R0 := by
    rw [mem_closedBall, dist_eq_norm]
    have hnorm : ‖((0 : E), w)‖ ≤ ‖w‖ := by
      rw [Prod.norm_def]
      have h : max ‖(0 : E)‖ ‖w‖ ≤ ‖w‖ := max_le (by simp) (le_rfl)
      simpa using h
    have hfin : ‖((0 : E), w)‖ ≤ R0 := le_trans hnorm (by dsimp [R0]; linarith)
    simpa using hfin
  let δf : ℝ := (Tf - u0) / 2
  have hδf : 0 < δf := by dsimp [δf]; positivity
  have hD1der (τ : ℝ) (hτ : τ ∈ Ioo (-δf) δf) :
      HasDerivAt (fun s : ℝ => Φr z0 (u0 + s)) (odeField g (Φr z0 (u0 + τ))) τ := by
    have hsh : HasDerivAt (fun s : ℝ => u0 + s) 1 τ := (hasDerivAt_id τ).const_add u0
    have hτa : |τ| < δf := abs_lt.mpr hτ
    have hAbs : |u0 + τ| < Tf := by
      have hta : |u0 + τ| ≤ |u0| + |τ| := abs_add_le u0 τ
      have hu0abs : |u0| = u0 := abs_of_nonneg (le_of_lt hu0pos)
      have h1 : u0 + |τ| < Tf := by
        have h11 : u0 + |τ| < u0 + δf := by
          have hh := add_lt_add_left hτa u0
          simpa [add_comm, add_left_comm, add_assoc] using hh
        have h12 : u0 + δf < Tf := by dsimp [δf]; nlinarith [hu0T]
        linarith
      linarith
    have htm : u0 + τ ∈ Ioo (-Tf) Tf := abs_lt.mp hAbs
    have hder_at : HasDerivAt (Φr z0) (odeField g (Φr z0 (u0 + τ))) (u0 + τ) := hΦrder (u0 + τ) htm
    have hc := HasDerivAt.scomp (x := τ) (g₁ := fun u : ℝ => Φr z0 u) (hg := hder_at)
      (h := fun s : ℝ => u0 + s) (h' := 1) (hh := hsh)
    simpa [one_smul, Function.comp_def] using hc
  have hD2der (τ : ℝ) (hτ : τ ∈ Ioo (-δf) δf) :
      HasDerivAt (fun s : ℝ => Φr (x0, w) s) (odeField g (Φr (x0, w) τ)) τ := by
    have hτ' : τ ∈ Icc (-Tf) Tf := by
      constructor
      · have h1 : -δf ≤ τ := le_of_lt hτ.1
        have h2 : -δf ≥ -Tf := by dsimp [δf]; linarith [hu0pos, hu0T]
        linarith
      · have h1 : τ ≤ δf := le_of_lt hτ.2
        have h2 : δf ≤ Tf := by dsimp [δf]; linarith [hu0T]
        linarith
    exact (hΦrAll (x0, w) hxw0mem).2.1 τ hτ'
  have hD_eq : ∀ τ ∈ Ioo (-δf) δf, Φr z0 (u0 + τ) = Φr (x0, w) τ := by
    have heq0 : Φr z0 (u0 + 0) = Φr (x0, w) 0 := by
      have h1 : Φr z0 u0 = (x0, w) := by
        simpa [xw, w] using hxw
      rw [add_zero, h1]
      exact (hΦrAll (x0, w) hxw0mem).1.symm
    exact pair_ode_eq_on g hg hinv (a := -δf) (b := δf)
      (z1 := fun s : ℝ => Φr z0 (u0 + s)) (z2 := fun s : ℝ => Φr (x0, w) s)
      hD1der hD2der (by constructor <;> linarith) heq0
  -- speed identity: (g x0) w w = cR^2 via constancy of the metric speed on the flow curve
  have hsplit0 := split_flow_geodesic g hg hinv (x0, (0 : E)) hTf (closedBall (x0, 0) R0) Φr
    (fun z hz => ⟨(hΦrAll z hz).1, (hΦrAll z hz).2.1⟩) (z := z0) hz0mem
  let cF : ℝ → E := fun u => (Φr z0 u).1
  let vF : ℝ → E := fun u => (Φr z0 u).2
  have hcFd (t : ℝ) (ht : t ∈ Ioo (-Tf) Tf) : HasDerivAt cF (vF t) t := by
    simpa [cF, vF] using hsplit0.1 t ht
  have hvFd (t : ℝ) (ht : t ∈ Ioo (-Tf) Tf) :
      HasDerivAt vF (accel (g (cF t)) (fderiv ℝ g (cF t)) (vF t)) t := by
    simpa [cF, vF] using hsplit0.2 t ht
  have hsc0 := speed_const g hg hinv hsym (ε := Tf) hTf (c := cF) (v := vF) hcFd hvFd
  let S : ℝ → ℝ := fun u => (g (cF u)) (vF u) (vF u)
  have hSder (t : ℝ) (ht : t ∈ Ioo (-Tf) Tf) : HasDerivAt S 0 t := by
    have hh := hsc0 t ht
    simpa [S] using hh
  have hScont : ContinuousOn S (Icc 0 u0) := by
    have h1 : ContinuousOn S (Ioo (-Tf) Tf) := HasDerivAt.continuousOn hSder
    exact h1.mono (by
      intro x hx
      constructor
      · exact lt_of_lt_of_le (neg_neg_of_pos hTf) hx.1
      · exact lt_of_le_of_lt hx.2 hu0T)
  have hSff : ∀ x ∈ Ioo (0 : ℝ) u0, HasDerivAt S 0 x := by
    intro x hx
    have hx' : x ∈ Ioo (-Tf) Tf := by
      constructor
      · exact lt_trans (neg_neg_of_pos hTf) hx.1
      · exact lt_trans hx.2 hu0T
    exact hSder x hx'
  rcases exists_hasDerivAt_eq_slope S (fun _ : ℝ => 0) hu0pos hScont hSff with ⟨cc, hccI, hslope⟩
  have hSlope0 : (S u0 - S 0) / u0 = 0 := by
    simpa using hslope.symm
  have hSconst : S u0 = S 0 := by
    have hmul := congrArg (fun x : ℝ => x * u0) hSlope0
    rw [div_mul_cancel₀ _ (ne_of_gt hu0pos)] at hmul
    linarith
  have hS0val : S 0 = (g (c t0)) (vel t0) (vel t0) := by
    dsimp [S, cF, vF, z0]
    rw [hΦr0]
  have hnn0 : 0 ≤ (g (c t0)) (vel t0) (vel t0) := by
    by_cases hvel : vel t0 = 0
    · simp [hvel]
    · exact le_of_lt (hpos (c t0) (vel t0) hvel)
  have hS0cR2 : S 0 = cR ^ 2 := by
    rw [hS0val]
    have hsq0 : Real.sqrt ((g (c t0)) (vel t0) (vel t0)) = cR := hcspeed t0 ht0I
    calc
      (g (c t0)) (vel t0) (vel t0) = (Real.sqrt ((g (c t0)) (vel t0) (vel t0))) ^ 2 := by
        rw [Real.sq_sqrt hnn0]
      _ = cR ^ 2 := by rw [hsq0]
  have hΦu0 : Φr z0 u0 = (x0, w) := by
    simpa [xw, w] using hxw
  have hSuv : S u0 = (g x0) w w := by
    dsimp [S, cF, vF]
    rw [hΦu0]
  have hSpeed : (g x0) w w = cR ^ 2 := by
    have h1 : S u0 = S 0 := hSconst
    rw [hSuv, hS0cR2] at h1
    exact h1
  have hnn : 0 ≤ (g x0) w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact le_of_lt (hpos x0 w hw)
  have hspeedSqrt : Real.sqrt ((g x0) w w) = cR := by
    calc
      Real.sqrt ((g x0) w w) = Real.sqrt (cR ^ 2) := by rw [hSpeed]
      _ = cR := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt hcR)]
  -- flow-scaling infrastructure: a geodesic from (x0,w) (region flow) and one from small data (given flow)
  let ε₂ : ℝ := (5 / 4) * τe
  have hε₂0 : 0 < ε₂ := by dsimp [ε₂]; positivity
  have hε₂lt : ε₂ < (3 / 2) * τe := by dsimp [ε₂]; nlinarith
  have hΦs (z : E × E) (hz : z ∈ closedBall (x0, 0) 2) :
      Φ z 0 = z ∧ ∀ t ∈ Icc (-ε₂) ε₂, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    constructor
    · exact (hΦ z hz).1
    · intro t ht
      have ht' : t ∈ Ioo (-((3 / 2) * τe)) (((3 / 2) * τe)) := by
        constructor <;> nlinarith [ht.1, ht.2, hε₂lt]
      exact (hΦ z hz).2 t ht'
  let c₁ : ℝ → E := fun τ => (Φr (x0, w) τ).1
  let vel₁ : ℝ → E := fun τ => (Φr (x0, w) τ).2
  have hsplit1 := split_flow_geodesic g hg hinv (x0, (0 : E)) hTf (closedBall (x0, 0) R0) Φr
    (fun z hz => ⟨(hΦrAll z hz).1, (hΦrAll z hz).2.1⟩) (z := (x0, w)) hxw0mem
  have hc₁d (t : ℝ) (ht : t ∈ Ioo (-Tf) Tf) : HasDerivAt c₁ (vel₁ t) t := by
    simpa [c₁, vel₁] using hsplit1.1 t ht
  have hv₁d (t : ℝ) (ht : t ∈ Ioo (-Tf) Tf) :
      HasDerivAt vel₁ (accel (g (c₁ t)) (fderiv ℝ g (c₁ t)) (vel₁ t)) t := by
    simpa [c₁, vel₁] using hsplit1.2 t ht
  have hc₁0 : c₁ 0 = x0 := by
    have h1 := (hΦrAll (x0, w) hxw0mem).1
    simpa [c₁] using congrArg Prod.fst h1
  have hv₁0 : vel₁ 0 = w := by
    have h1 := (hΦrAll (x0, w) hxw0mem).1
    simpa [vel₁] using congrArg Prod.snd h1
  -- final delta
  let δs : ℝ := min (u0 / 2) (min (δf / 2) (min (Tf / 2) ((ρe / 2) / (‖w‖ + 1))))
  have hδs0 : 0 < δs := by
    dsimp [δs]
    positivity
  have hδs_u0 : δs ≤ u0 / 2 := by dsimp [δs]; exact min_le_left _ _
  have hδs_δf : δs ≤ δf / 2 := by dsimp [δs]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδs_Tf : δs ≤ Tf / 2 := by
    dsimp [δs]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδs_ρ : δs ≤ (ρe / 2) / (‖w‖ + 1) := by
    dsimp [δs]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨w, hspeedSqrt, ⟨δs, hδs0, ?_⟩⟩
  intro t ht
  have htb : t < b := ht.2
  have ht_gt : b - δs < t := ht.1
  let s : ℝ := t - b
  have hs_neg : s < 0 := by dsimp [s]; linarith
  have hs_abs : |s| < δs := by
    rw [abs_of_neg hs_neg]
    dsimp [s]
    linarith
  have hsTf : |s| < Tf := lt_of_lt_of_le hs_abs (le_trans hδs_Tf (by linarith))
  have hδs_le_δf : δs ≤ δf := le_trans hδs_δf (by dsimp [δf]; linarith)
  have hsmemδf : s ∈ Ioo (-δf) δf := by
    have h1 : |s| < δf := lt_of_lt_of_le hs_abs hδs_le_δf
    exact abs_lt.mp h1
  have ht_gt_t0 : t0 < t := by
    have h2 : δs ≤ (b - t0) / 2 := by simpa [u0] using hδs_u0
    have h1 : b - δs > t0 := by linarith
    linarith
  have ht_a0 : t ∈ Ioo a0 b := ⟨lt_trans ha0_t0 ht_gt_t0, htb⟩
  -- c t via the flow
  have hcFlow : c t = (Φr (x0, w) s).1 := by
    have hzEq := hEqFlow t ht_a0
    have hmain1 : (z t).1 = (Φr z0 (t - t0)).1 := congrArg Prod.fst hzEq
    have htshift : t - t0 = u0 + s := by dsimp [u0, s]; ring
    have hmain2 : (Φr z0 (t - t0)).1 = (Φr z0 (u0 + s)).1 := by rw [htshift]
    have hmain3 : (Φr z0 (u0 + s)).1 = (Φr (x0, w) s).1 := congrArg Prod.fst (hD_eq s hsmemδf)
    calc
      c t = (z t).1 := by simp [z]
      _ = (Φr z0 (t - t0)).1 := hmain1
      _ = (Φr z0 (u0 + s)).1 := hmain2
      _ = (Φr (x0, w) s).1 := hmain3
  -- the exponential-map identity for s
  let σ : ℝ := s / τe
  have hσ_ne : σ ≠ 0 := by dsimp [σ]; exact div_ne_zero (by linarith) (ne_of_gt hτe)
  have hsmulσ : σ • w = (1 / τe) • (s • w) := by
    dsimp [σ]
    rw [smul_smul]
    congr 1
    field_simp [hτe.ne']
  have hsw_norm : ‖s • w‖ < ρe := by
    have h1 : |s| * ‖w‖ ≤ |s| * (‖w‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
    have h2 : |s| * (‖w‖ + 1) < ρe := by
      have h3 : δs * (‖w‖ + 1) ≤ ρe / 2 := by
        have h4 : (ρe / 2) / (‖w‖ + 1) * (‖w‖ + 1) = ρe / 2 := by
          field_simp [ne_of_gt (by positivity : 0 < ‖w‖ + 1)]
        calc
          δs * (‖w‖ + 1) ≤ ((ρe / 2) / (‖w‖ + 1)) * (‖w‖ + 1) :=
            mul_le_mul_of_nonneg_right hδs_ρ (by positivity)
          _ = ρe / 2 := h4
      have h5 : |s| * (‖w‖ + 1) < δs * (‖w‖ + 1) :=
        mul_lt_mul_of_pos_right hs_abs (by positivity)
      linarith
    calc
      ‖s • w‖ = |s| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |s| * (‖w‖ + 1) := h1
      _ < ρe := h2
  have hsw_ball : s • w ∈ ball (0 : E) ρe := by
    simpa [dist_eq_norm] using hsw_norm
  have hnum : |s| * ‖w‖ < ρe := by
    have hx : ‖s • w‖ < ρe := hsw_norm
    simpa [norm_smul, Real.norm_eq_abs] using hx
  have hρe_bound : ρe / τe ≤ 1 / 4 := by
    rw [div_le_iff₀ hτe]
    have hqq : (1 / 4 : ℝ) * τe = τe / 4 := by ring
    rw [hqq]
    exact hρeτe
  have hσw_lt2 : ‖σ • w‖ < 2 := by
    have h1 : |s| * ‖w‖ / τe < 2 := by
      have h2 : |s| * ‖w‖ / τe ≤ ρe / τe := by
        field_simp [hτe.ne']
        exact le_of_lt hnum
      linarith
    calc
      ‖σ • w‖ = |s| * ‖w‖ / τe := by
        rw [norm_smul, Real.norm_eq_abs]
        dsimp [σ]
        rw [abs_div, abs_of_pos hτe]
        field_simp [hτe.ne']
      _ < 2 := h1
  have hzsmem : (x0, σ • w) ∈ closedBall (x0, (0 : E)) 2 := by
    rw [mem_closedBall, dist_eq_norm]
    have hnorm : ‖((0 : E), σ • w)‖ ≤ ‖σ • w‖ := by
      rw [Prod.norm_def]
      exact max_le (by simp) (le_rfl)
    have hfin : ‖((0 : E), σ • w)‖ < 2 := lt_of_le_of_lt hnorm hσw_lt2
    simpa using le_of_lt hfin
  have hsplit2 := split_flow_geodesic g hg hinv (x0, (0 : E)) hε₂0 (closedBall (x0, 0) 2) Φ hΦs
    (z := (x0, σ • w)) hzsmem
  let c₂ : ℝ → E := fun τ => (Φ (x0, σ • w) τ).1
  let vel₂ : ℝ → E := fun τ => (Φ (x0, σ • w) τ).2
  have hc₂d (τ : ℝ) (hτ : τ ∈ Ioo (-ε₂) ε₂) : HasDerivAt c₂ (vel₂ τ) τ := by
    simpa [c₂, vel₂] using hsplit2.1 τ hτ
  have hv₂d (τ : ℝ) (hτ : τ ∈ Ioo (-ε₂) ε₂) :
      HasDerivAt vel₂ (accel (g (c₂ τ)) (fderiv ℝ g (c₂ τ)) (vel₂ τ)) τ := by
    simpa [c₂, vel₂] using hsplit2.2 τ hτ
  have hc₂0 : c₂ 0 = x0 := by
    have h1 := (hΦs (x0, σ • w) hzsmem).1
    simpa [c₂] using congrArg Prod.fst h1
  have hv₂0 : vel₂ 0 = σ • w := by
    have h1 := (hΦs (x0, σ • w) hzsmem).1
    simpa [vel₂] using congrArg Prod.snd h1
  have hsc := flow_scaling (g := g) (hg := hg) (hinv := hinv) (ε₁ := Tf) (ε₂ := ε₂)
    (hε₁ := hTf) (hε₂ := hε₂0)
    (c₁ := c₁) (vel₁ := vel₁) (c₂ := c₂) (vel₂ := vel₂) (x := x0) (v := w) (s := σ) (hs := hσ_ne)
    (hc₁ := hc₁0) (hv₁ := hv₁0) (hc₂ := hc₂0) (hv₂ := hv₂0)
    (hc₁d := hc₁d) (hv₁d := hv₁d) (hc₂d := hc₂d) (hv₂d := hv₂d) τe
  have hτe_mem : τe ∈ Ioo (-min ε₂ (Tf / |σ|)) (min ε₂ (Tf / |σ|)) := by
    have hpos : 0 < min ε₂ (Tf / |σ|) := lt_min hε₂0 (div_pos hTf (abs_pos.mpr hσ_ne))
    constructor
    · linarith
    · exact lt_min (by dsimp [ε₂]; nlinarith) (by
        rw [lt_div_iff₀ (abs_pos.mpr hσ_ne)]
        have hσ_abs : |σ| = |s| / τe := by dsimp [σ]; rw [abs_div, abs_of_pos hτe]
        have hmul : τe * |σ| = |s| := by
          rw [hσ_abs]
          field_simp [hτe.ne']
        rw [hmul]
        exact hsTf)
  have hfs := hsc hτe_mem
  have hfs1 : c₂ τe = c₁ s := by
    have hmain := hfs.1
    have hσt : σ * τe = s := by dsimp [σ]; field_simp [hτe.ne']
    simpa [hσt] using hmain
  have hexp_eq : expm (s • w) = (Φ (x0, σ • w) τe).1 := by
    rw [hsmulσ]
    exact hexpform (s • w) hsw_ball
  have hfinal : c t = expm (s • w) := by
    calc
      c t = (Φr (x0, w) s).1 := hcFlow
      _ = c₁ s := by rfl
      _ = c₂ τe := hfs1.symm
      _ = (Φ (x0, σ • w) τe).1 := by rfl
      _ = expm (s • w) := hexp_eq.symm
  simpa [s] using hfinal


end
end NeckFlow
end Submission
