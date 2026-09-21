import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Window.WindowDefs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Window.TW_regular
import Submission.Work.OddVolterra.Smooth.Q_regularity
import Submission.Work.Anchor.ThetaM_contDiffOn_wide
import Submission.Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_of_le
import Submission.Commons.Analysis.Abel.continuousOn_abel_K

/-!
# Continuity of the truncated source `XW` of the odd window

`XW n h s = cs s • (Ξ n h s + ∫_σ in 19/20..1, thetac n h s σ (baseState σ))` is the source datum
fed to the long-interval fixed-point engine on the transition window: the paper's `Ξ` (whose last
two components are the derivative of a truncated Abel transform of `Q n h`) plus the frozen tail
of the `Θ`-integral, all cut off to the slope window by the bump `cs` (centred at `33/40`, support
inside `(13/20, 99/100)`).

The two non-trivial inputs are

* `s ↦ Ξ n h s` is continuous on `(13/20, 99/100)`: `Q n h` is continuous on `[13/20, 1]` and `C²`
  on every `[13/20, b]`, `b < 1`, and the derivative of the Abel transform of such a `Q` is
  continuous on compacts inside `(0,1)` (`xw_continuousOn_deriv_abel_transform`);
* `s ↦ ∫_σ in 19/20..1, thetac n h s σ (baseState σ)` is continuous there: on the region of use
  the clamped kernel `thetac` equals the manifest datum `ΘM` at the slope `max s σ`
  (`tw_thetac_eq`), and `ΘM` is `C^∞` on the region `Work.Anchor.Good`
  (`Work.Anchor.ThetaM_contDiffOn_Good`), so the parametric integral is continuous
  (`Commons.Analysis.Abel.continuousOn_intervalIntegral_of_continuousOn_compact`).

The pieces below are the same statements as in `Submission/Work/OddVolterra/Window/
window_data_regular.lean` (which cannot be imported here: its import closure contains modules that
were never materialised), kept under `xw_` names.

The cut-off `cs` then glues everything: a continuous `f` vanishing off `tsupport cs` times a
function continuous on a neighbourhood of `tsupport cs` is continuous.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra

/-! ## The ball profile -/

/-- On `|s| ≤ 21/20` the ball profile stays above `17/25`. -/
lemma xw_profileX_ge_17_25 {s : ℝ} (hs : |s| ≤ 21 / 20) :
    17 / 25 ≤ Commons.Geometry.Ulam.profileX s := by
  have hs2 : s ^ 2 ≤ (21 / 20 : ℝ) ^ 2 := by
    have h := abs_le.mp hs
    nlinarith [h.1, h.2]
  have hsq : Real.sqrt (1 + s ^ 2) ≤ 25 / 17 := by
    have hle : 1 + s ^ 2 ≤ (25 / 17 : ℝ) ^ 2 := by nlinarith [hs2]
    calc Real.sqrt (1 + s ^ 2) ≤ Real.sqrt ((25 / 17 : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 25 / 17 := Real.sqrt_sq (by norm_num)
  rw [Commons.Geometry.Ulam.profileX, le_div_iff₀ (Real.sqrt_pos.mpr (by positivity))]
  calc 17 / 25 * Real.sqrt (1 + s ^ 2) ≤ 17 / 25 * (25 / 17) :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 1 := by norm_num

lemma xw_contDiff_baseState : ContDiff ℝ (⊤ : ℕ∞) baseState := by
  have hpx : ContDiff ℝ (⊤ : ℕ∞) Commons.Geometry.Ulam.profileX :=
    Commons.Geometry.Ulam.RyaboginVolterra.contDiff_profileX
  have hdpx : ContDiff ℝ (⊤ : ℕ∞) (deriv Commons.Geometry.Ulam.profileX) := by
    have h := hpx.iterate_deriv 1
    simpa [Function.iterate_one] using h
  rw [show baseState = fun s : ℝ => ![
      Commons.Geometry.Ulam.profileX s, Commons.Geometry.Ulam.profileX s,
      deriv Commons.Geometry.Ulam.profileX s,
      deriv Commons.Geometry.Ulam.profileX s] from rfl]
  exact contDiff_pi.mpr (fun i => by
    fin_cases i <;> simp [hpx, hdpx])

lemma xw_continuous_baseState : Continuous baseState := xw_contDiff_baseState.continuous

/-- The continuous version of `xw_contDiff_smul_of_contDiffOn`. -/
lemma xw_continuous_smul_of_continuousOn {X : Type*} [TopologicalSpace X]
    {E : Type*} [TopologicalSpace E] [Zero E] [SMulWithZero ℝ E] [ContinuousSMul ℝ E]
    {f : X → ℝ} {g : X → E} {U : Set X} (hU : IsOpen U)
    (hf : Continuous f) (hg : ContinuousOn g U) (hsub : tsupport f ⊆ U) :
    Continuous (fun x => f x • g x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact hf.continuousAt.smul (hg.continuousAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport f := fun h => hx (hsub h)
    have hmem : (tsupport f)ᶜ ∈ 𝓝 x := (isClosed_tsupport f).isOpen_compl.mem_nhds hx'
    refine (continuousAt_const (y := (0 : E))).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with y hy
    have hy' : f y = 0 := by
      by_contra h
      exact hy (subset_tsupport f (Function.mem_support.mpr h))
    rw [hy', zero_smul]

/-- For a bump `h` supported in `[4/5, 9/10]` with `|h| ≤ 1/100`, the affine lines
`t ↦ s t + h s` stay strictly inside the unit semicircle on the fixed interval `[-X₁, X₁]`,
`X₁ = profileX 1 = 1/√2`. -/
lemma xw_psi_semicircle_pos_small {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ t : ℝ, |h t| ≤ 1 / 100) :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1))
        (Commons.Geometry.Ulam.profileX 1),
        0 < psi h Commons.Geometry.Ulam.semicircle s t := by
  intro s hs t ht
  obtain ⟨hs0, hs1⟩ := hs
  have hX2 : (Commons.Geometry.Ulam.profileX 1) ^ 2 = (1 : ℝ) / 2 := by
    rw [Commons.Geometry.Ulam.profileX_sq]; norm_num
  have hXpos : 0 < Commons.Geometry.Ulam.profileX 1 :=
    Commons.Geometry.Ulam.profileX_pos 1 (by norm_num)
  have hXlt : Commons.Geometry.Ulam.profileX 1 < 3 / 4 := by nlinarith
  have htabs : |t| ≤ Commons.Geometry.Ulam.profileX 1 := by
    rw [abs_le]; exact ⟨ht.1, ht.2⟩
  have ht2 : t ^ 2 ≤ (1 : ℝ) / 2 := by
    have h := mul_self_le_mul_self (abs_nonneg t) htabs
    have h2 : |t| * |t| = t ^ 2 := by rw [← sq, sq_abs]
    rw [h2] at h
    rw [← sq, hX2] at h
    exact h
  have hsem : Commons.Geometry.Ulam.semicircle t ^ 2 = 1 - t ^ 2 := by
    rw [Commons.Geometry.Ulam.semicircle, Real.sq_sqrt]; linarith
  have hpsi : psi h Commons.Geometry.Ulam.semicircle s t = 1 - t ^ 2 - (s * t + h s) ^ 2 := by
    simp only [psi, hsem, line]
  rw [hpsi]
  by_cases hsle : s ≤ 9 / 10
  · have hh : |h s| ≤ 1 / 100 := hsmall s
    have h1 : |s * t + h s| ≤ s * |t| + |h s| := by
      calc |s * t + h s| ≤ |s * t| + |h s| := abs_add_le _ _
        _ = s * |t| + |h s| := by rw [abs_mul, abs_of_pos hs0]
    have h6 : s * |t| < (9 / 10) * (3 / 4) := by
      have h5 : s * |t| ≤ (9 / 10) * Commons.Geometry.Ulam.profileX 1 :=
        mul_le_mul hsle htabs (abs_nonneg t) (by norm_num)
      nlinarith [h5, hXlt]
    have h2 : s * |t| + |h s| < 9 / 10 * (3 / 4) + 1 / 100 := by
      linarith [(abs_le.mp hh).2]
    have h3 : (s * t + h s) ^ 2 < (9 / 10 * (3 / 4) + 1 / 100) ^ 2 := by
      calc (s * t + h s) ^ 2 = |s * t + h s| ^ 2 := (sq_abs _).symm
        _ < _ := pow_lt_pow_left₀ (by linarith) (abs_nonneg _) (by norm_num)
    have h4 : (9 / 10 * (3 / 4) + 1 / 100 : ℝ) ^ 2 < 1 / 2 := by norm_num
    linarith
  · push_neg at hsle
    have hhs : h s = 0 := by
      by_contra hne
      have hmem : s ∈ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) :=
        hsupp (Function.mem_support.mpr hne)
      rw [Work.OddVolterra.tau] at hmem
      norm_num at hmem
      linarith [hmem.2]
    rw [hhs, add_zero]
    nlinarith [ht2, hs0, hs1, sq_nonneg s]

/-! ## Continuity of the derivative of the Abel transform

The last two components of the source `Xi` are `deriv (u ↦ ∫_u^1 Q v / √(v-u) dv)`.  The
following lemma shows that this is continuous on `(a,c) ⊂ (0,1)` for a function `Q` that is
continuous on `[a,1]` and `C¹` on `(a,e)` with `e > c`.

The proof splits the integral at a point `c'` with `c < c' < min e 1`:

* the piece `∫_{c'}^1 (√(v-u))⁻¹ Q v dv` has no singularity for `u ≤ c` (`v - u ≥ c' - c > 0`),
  so it may be differentiated under the integral sign;
* the piece `∫_u^{c'} (√(v-u))⁻¹ Q v dv = 2 √(c'-u) ∫_0^1 Q (u + (c'-u)t²) dt`, and the
  arguments `u + (c'-u)t²` all lie in `[u,c'] ⊂ (a,e)` where `Q` is `C¹`; the product rule and
  differentiation under the integral sign (the weight `1 - t²` vanishes at `t = 1`, so only
  interior points matter) give the derivative.
-/

theorem xw_continuousOn_deriv_abel_transform {a c e : ℝ} (ha : 0 < a) (hac : a < c)
    (hc1 : c < 1) (hce : c < e) {Q : ℝ → ℝ} (hQcont : ContinuousOn Q (Set.Icc a 1))
    (hQsmooth : ContDiffOn ℝ 1 Q (Set.Ioo a e)) :
    ContinuousOn (fun s : ℝ => deriv (fun u : ℝ => ∫ v in u..1, Q v / Real.sqrt (v - u)) s)
      (Set.Ioo a c) := by
  have hQderiv_cont : ContinuousOn (deriv Q) (Set.Ioo a e) :=
    hQsmooth.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hQderiv : ∀ w ∈ Set.Ioo a e, HasDerivAt Q (deriv Q w) w := by
    intro w hw
    exact ((hQsmooth.contDiffAt (isOpen_Ioo.mem_nhds hw)).differentiableAt (by norm_num)).hasDerivAt
  -- the split point
  set c' : ℝ := (c + min e 1) / 2 with hc'def
  have hcc' : c < c' := by rw [hc'def]; linarith [lt_min hce hc1]
  have hc'e : c' < e := by rw [hc'def]; linarith [min_le_left e 1]
  have hc'1 : c' < 1 := by rw [hc'def]; linarith [min_le_right e 1]
  have hc'a : a < c' := lt_trans hac hcc'
  -- the manifest pieces
  set F : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..1, Q (s + (c' - s) * u ^ 2) with hFdef
  set F' : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..1, deriv Q (s + (c' - s) * u ^ 2) * (1 - u ^ 2)
    with hF'def
  set G : ℝ → ℝ := fun s => ∫ v in c'..1, Q v / Real.sqrt (v - s) with hGdef
  set G' : ℝ → ℝ := fun s => ∫ v in c'..1, (2 * (Real.sqrt (v - s)) ^ 3)⁻¹ * Q v with hG'def
  set T : ℝ → ℝ := fun u => ∫ v in u..1, Q v / Real.sqrt (v - u) with hTdef
  set R : ℝ → ℝ := fun s => -(1 / Real.sqrt (c' - s)) * F s + 2 * Real.sqrt (c' - s) * F' s
    + G' s with hRdef
  -- the arguments of `Q` stay inside `(a,e)` on a closed subinterval of `(a,c)`
  have hargs : ∀ {s₁ s₂ s u : ℝ}, a < s₁ → s₂ < c → s ∈ Set.Icc s₁ s₂ →
      u ∈ Set.Icc (0 : ℝ) 1 → s + (c' - s) * u ^ 2 ∈ Set.Ioo a e := by
    intro s₁ s₂ s u hs₁ hs₂ hs hu
    have hu0 : 0 ≤ u ^ 2 := sq_nonneg u
    have hu1 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    have hsc' : s < c' := lt_trans (lt_of_le_of_lt hs.2 hs₂) hcc'
    have hnonneg : 0 ≤ (c' - s) * u ^ 2 := mul_nonneg (by linarith) hu0
    have hmul : (c' - s) * u ^ 2 ≤ c' - s := by
      have h := mul_le_mul_of_nonneg_left hu1 (by linarith : (0 : ℝ) ≤ c' - s)
      simpa using h
    exact ⟨by linarith [hs.1], by linarith⟩
  -- ## the two manifest derivatives
  have hF_deriv : ∀ s₀ ∈ Set.Ioo a c, HasDerivAt F (F' s₀) s₀ := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    set δ : ℝ := min (s₀ - a) (c - s₀) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min (by linarith) (by linarith))
    have hs₁a : a < s₀ - δ := by
      have h := min_le_left (s₀ - a) (c - s₀)
      rw [hδdef]; linarith
    have hs₂c : s₀ + δ < c := by
      have h := min_le_right (s₀ - a) (c - s₀)
      rw [hδdef]; linarith
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Q (p.1 + (c' - p.1) * p.2 ^ 2))
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
      refine hQsmooth.continuousOn.comp (by fun_prop) ?_
      rintro ⟨s, u⟩ ⟨hs, hu⟩
      exact hargs hs₁a hs₂c hs ⟨hu.1, hu.2⟩
    have hcont' : ContinuousOn (fun p : ℝ × ℝ =>
        deriv Q (p.1 + (c' - p.1) * p.2 ^ 2) * (1 - p.2 ^ 2))
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => deriv Q (p.1 + (c' - p.1) * p.2 ^ 2))
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
        refine hQderiv_cont.comp (by fun_prop) ?_
        rintro ⟨s, u⟩ ⟨hs, hu⟩
        exact hargs hs₁a hs₂c hs ⟨hu.1, hu.2⟩
      exact h1.mul (by fun_prop)
    have hpt : ∀ s ∈ Set.Icc (s₀ - δ) (s₀ + δ), ∀ u ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun y : ℝ => Q (y + (c' - y) * u ^ 2))
          (deriv Q (s + (c' - s) * u ^ 2) * (1 - u ^ 2)) s := by
      intro s hs u hu
      have hinner : HasDerivAt (fun y : ℝ => y + (c' - y) * u ^ 2) (1 - u ^ 2) s := by
        have h1 : HasDerivAt (fun y : ℝ => (c' - y) * u ^ 2) (-(u ^ 2)) s := by
          have h := ((hasDerivAt_id s).const_sub c').mul_const (u ^ 2)
          simpa using h
        have h2 : HasDerivAt (fun y : ℝ => y + (c' - y) * u ^ 2) (1 + -(u ^ 2)) s :=
          (hasDerivAt_id s).add h1
        exact h2.congr_deriv (by ring)
      have houter : HasDerivAt Q (deriv Q (s + (c' - s) * u ^ 2))
          (s + (c' - s) * u ^ 2) :=
        hQderiv _ (hargs hs₁a hs₂c hs ⟨hu.1, hu.2⟩)
      exact houter.comp s hinner
    have h := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_of_le
      (F := fun s u => Q (s + (c' - s) * u ^ 2))
      (F' := fun s u => deriv Q (s + (c' - s) * u ^ 2) * (1 - u ^ 2))
      (s₀ := s₀) (s₁ := s₀ - δ) (s₂ := s₀ + δ) (a := (0 : ℝ)) (b := 1)
      (by linarith) (by linarith) (by norm_num) hcont hcont' hpt
    simpa only [hFdef, hF'def] using h
  have hG_deriv : ∀ s₀ ∈ Set.Ioo a c, HasDerivAt G (G' s₀) s₀ := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    set δ : ℝ := min (s₀ - a) (c - s₀) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min (by linarith) (by linarith))
    have hs₂c : s₀ + δ < c := by
      have h := min_le_right (s₀ - a) (c - s₀)
      rw [hδdef]; linarith
    have hQbox : ContinuousOn Q (Set.Icc c' 1) :=
      hQcont.mono (fun x hx => ⟨le_trans hc'a.le hx.1, hx.2⟩)
    have hpos : ∀ s ∈ Set.Icc (s₀ - δ) (s₀ + δ), ∀ v ∈ Set.Icc c' 1, 0 < v - s := by
      intro s hs v hv
      have h2 := hs.2
      linarith [hv.1, hs₂c, hcc']
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Q p.2 / Real.sqrt (p.2 - p.1))
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) := by
      have hnum : ContinuousOn (fun p : ℝ × ℝ => Q p.2)
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) :=
        hQbox.comp (by fun_prop) (fun p hp => ⟨hp.2.1, hp.2.2⟩)
      have hden : ContinuousOn (fun p : ℝ × ℝ => Real.sqrt (p.2 - p.1))
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) := by fun_prop
      exact hnum.div hden (fun p hp => ne_of_gt (Real.sqrt_pos.mpr (hpos p.1 hp.1 p.2 hp.2)))
    have hcont' : ContinuousOn (fun p : ℝ × ℝ =>
        (2 * (Real.sqrt (p.2 - p.1)) ^ 3)⁻¹ * Q p.2)
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) := by
      have hnum : ContinuousOn (fun p : ℝ × ℝ => Q p.2)
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) :=
        hQbox.comp (by fun_prop) (fun p hp => ⟨hp.2.1, hp.2.2⟩)
      have hden : ContinuousOn (fun p : ℝ × ℝ => (2 * (Real.sqrt (p.2 - p.1)) ^ 3)⁻¹)
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) := by
        refine ContinuousOn.inv₀ (by fun_prop) ?_
        intro p hp
        have hp0 : 0 < p.2 - p.1 := hpos p.1 hp.1 p.2 hp.2
        exact ne_of_gt (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr hp0) 3))
      exact hden.mul hnum
    have hpt : ∀ s ∈ Set.Icc (s₀ - δ) (s₀ + δ), ∀ v ∈ Set.Icc c' 1,
        HasDerivAt (fun y : ℝ => Q v / Real.sqrt (v - y))
          ((2 * (Real.sqrt (v - s)) ^ 3)⁻¹ * Q v) s := by
      intro s hs v hv
      have hvs : 0 < v - s := hpos s hs v hv
      have hsne : Real.sqrt (v - s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hvs)
      have hlin : HasDerivAt (fun y : ℝ => v - y) (-1) s := (hasDerivAt_id s).const_sub v
      have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (v - s))) (v - s) :=
        Real.hasDerivAt_sqrt (ne_of_gt hvs)
      have hkey : (-((Real.sqrt (v - s)) ^ 2)⁻¹) * ((1 / (2 * Real.sqrt (v - s))) * (-1))
          = (2 * (Real.sqrt (v - s)) ^ 3)⁻¹ := by
        have hr2 : (Real.sqrt (v - s)) ^ 2 ≠ 0 := pow_ne_zero _ hsne
        have hr3 : 2 * (Real.sqrt (v - s)) ^ 3 ≠ 0 := by
          exact ne_of_gt (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr hvs) 3))
        field_simp
      have hk : HasDerivAt (fun y : ℝ => (Real.sqrt (v - y))⁻¹)
          ((2 * (Real.sqrt (v - s)) ^ 3)⁻¹) s :=
        ((hasDerivAt_inv hsne).comp s (hsqrt.comp s hlin)).congr_deriv hkey
      have hk' := hk.mul_const (Q v)
      refine hk'.congr_of_eventuallyEq ?_
      filter_upwards with y
      rw [div_eq_mul_inv, mul_comm]
    have h := Commons.Analysis.Calculus.intervalIntegral_hasDerivAt_of_continuousOn_of_le
      (F := fun s v => Q v / Real.sqrt (v - s))
      (F' := fun s v => (2 * (Real.sqrt (v - s)) ^ 3)⁻¹ * Q v)
      (s₀ := s₀) (s₁ := s₀ - δ) (s₂ := s₀ + δ) (a := c') (b := 1)
      (by linarith) (by linarith) (le_of_lt hc'1) hcont hcont' hpt
    simpa only [hGdef, hG'def] using h
  -- ## the splitting identity and the product rule for the moving piece
  have habel : ∀ s ≤ c',
      (∫ v in s..c', Q v / Real.sqrt (v - s)) = 2 * Real.sqrt (c' - s) * F s := by
    intro s hsc'
    have h := Commons.Analysis.Abel.intervalIntegral_abel_subst (x := s) (b := c') hsc'
      (K := fun _ v => Q v)
    have hcongr : (∫ v in s..c', Q v / Real.sqrt (v - s))
        = ∫ σ in s..c', (Real.sqrt (σ - s))⁻¹ * Q σ := by
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      rw [div_eq_mul_inv, mul_comm]
    rw [hcongr, hFdef]
    simpa only [smul_eq_mul] using h
  have hA_deriv : ∀ s₀ ∈ Set.Ioo a c,
      HasDerivAt (fun s : ℝ => ∫ v in s..c', Q v / Real.sqrt (v - s))
        (2 * Real.sqrt (c' - s₀) * F' s₀ - F s₀ / Real.sqrt (c' - s₀)) s₀ := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    have hs₀c' : s₀ < c' := lt_trans hs₀c hcc'
    have hne : c' - s₀ ≠ 0 := ne_of_gt (by linarith)
    have hr : Real.sqrt (c' - s₀) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
    have hsqrt : HasDerivAt (fun s : ℝ => 2 * Real.sqrt (c' - s))
        (-(1 / Real.sqrt (c' - s₀))) s₀ := by
      have h1 : HasDerivAt (fun s : ℝ => c' - s) (-1) s₀ := (hasDerivAt_id s₀).const_sub c'
      have h2 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (c' - s₀))) (c' - s₀) :=
        Real.hasDerivAt_sqrt hne
      have h3 := (h2.comp s₀ h1).const_mul 2
      refine h3.congr_deriv ?_
      field_simp
    have hprod : HasDerivAt (fun s : ℝ => 2 * Real.sqrt (c' - s) * F s)
        (2 * Real.sqrt (c' - s₀) * F' s₀ - F s₀ / Real.sqrt (c' - s₀)) s₀ :=
      (hsqrt.mul (hF_deriv s₀ ⟨hs₀a, hs₀c⟩)).congr_deriv (by rw [div_eq_mul_inv]; ring)
    refine hprod.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Iio.mem_nhds hs₀c'] with s hs
    exact habel s (le_of_lt hs)
  -- ## the derivative of `T`
  have hsplit : ∀ s ∈ Set.Ioo a c, T s = (∫ v in s..c', Q v / Real.sqrt (v - s)) + G s := by
    intro s hs
    obtain ⟨hsa, hsc⟩ := hs
    have hsc' : s ≤ c' := le_of_lt (lt_trans hsc hcc')
    have hcontQ : ContinuousOn Q (Set.uIcc s c') := by
      rw [Set.uIcc_of_le hsc']
      exact hQcont.mono (fun x hx => ⟨le_trans hsa.le hx.1, le_trans hx.2 hc'1.le⟩)
    have hg : ContinuousOn (fun v : ℝ => Q v - 0) (Set.uIcc s c') :=
      hcontQ.sub continuousOn_const
    have hint1 : IntervalIntegrable (fun v : ℝ => Q v / Real.sqrt (v - s)) volume s c' := by
      have h := (Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub
        (lt_trans hsc hcc')).smul_continuousOn hg
      have h2 : (fun v : ℝ => (Real.sqrt (v - s))⁻¹ • (Q v - 0))
          = fun v : ℝ => Q v / Real.sqrt (v - s) := by
        funext v
        rw [smul_eq_mul, sub_zero, div_eq_mul_inv, mul_comm]
      rw [← h2]
      exact h
    have hint2 : IntervalIntegrable (fun v : ℝ => Q v / Real.sqrt (v - s)) volume c' 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le (le_of_lt hc'1)]
      refine ContinuousOn.div ?_ ?_ ?_
      · exact hQcont.mono (fun x hx => ⟨le_trans hc'a.le hx.1, hx.2⟩)
      · exact (Real.continuous_sqrt.comp_continuousOn (continuousOn_id.sub continuousOn_const))
      · intro v hv
        exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hv.1, hsc, hcc']))
    have h := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    rw [hTdef, hGdef]
    exact h.symm
  have hT_deriv : ∀ s₀ ∈ Set.Ioo a c, HasDerivAt T (R s₀) s₀ := by
    intro s₀ hs₀
    have hsum := (hA_deriv s₀ hs₀).add (hG_deriv s₀ hs₀)
    have hR : (2 * Real.sqrt (c' - s₀) * F' s₀ - F s₀ / Real.sqrt (c' - s₀)) + G' s₀ = R s₀ := by
      simp only [hRdef, div_eq_mul_inv]
      ring
    refine (hsum.congr_of_eventuallyEq ?_).congr_deriv hR
    filter_upwards [isOpen_Ioo.mem_nhds hs₀] with s hs
    exact hsplit s hs
  -- ## continuity of the manifest derivative
  have hF_cont : ContinuousOn F (Set.Ioo a c) := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    set δ : ℝ := min (s₀ - a) (c - s₀) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min (by linarith) (by linarith))
    have hs₁a : a < s₀ - δ := by
      have h := min_le_left (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hs₂c : s₀ + δ < c := by
      have h := min_le_right (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hmem : Set.Icc (s₀ - δ) (s₀ + δ) ∈ 𝓝 s₀ :=
      Icc_mem_nhds (by linarith) (by linarith)
    have hcont : ContinuousOn (fun p : ℝ × ℝ => Q (p.1 + (c' - p.1) * p.2 ^ 2))
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      refine hQsmooth.continuousOn.comp (by fun_prop) ?_
      rintro ⟨s, u⟩ ⟨hs, hu⟩
      exact hargs hs₁a hs₂c hs ⟨hu.1, hu.2⟩
    have h := Commons.Analysis.Abel.continuousOn_intervalIntegral_of_continuousOn_compact
      (s := Set.Icc (s₀ - δ) (s₀ + δ)) isCompact_Icc (A := (0 : ℝ)) (B := 1)
      (by norm_num) (F := fun s u => Q (s + (c' - s) * u ^ 2)) hcont
    have h2 : ContinuousOn F (Set.Icc (s₀ - δ) (s₀ + δ)) := by
      simpa only [hFdef] using h
    exact (h2.continuousAt hmem).continuousWithinAt
  have hF'_cont : ContinuousOn F' (Set.Ioo a c) := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    set δ : ℝ := min (s₀ - a) (c - s₀) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min (by linarith) (by linarith))
    have hs₁a : a < s₀ - δ := by
      have h := min_le_left (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hs₂c : s₀ + δ < c := by
      have h := min_le_right (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hmem : Set.Icc (s₀ - δ) (s₀ + δ) ∈ 𝓝 s₀ :=
      Icc_mem_nhds (by linarith) (by linarith)
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        deriv Q (p.1 + (c' - p.1) * p.2 ^ 2) * (1 - p.2 ^ 2))
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      have h1 : ContinuousOn (fun p : ℝ × ℝ => deriv Q (p.1 + (c' - p.1) * p.2 ^ 2))
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc (0 : ℝ) 1) := by
        refine hQderiv_cont.comp (by fun_prop) ?_
        rintro ⟨s, u⟩ ⟨hs, hu⟩
        exact hargs hs₁a hs₂c hs ⟨hu.1, hu.2⟩
      exact h1.mul (by fun_prop)
    have h := Commons.Analysis.Abel.continuousOn_intervalIntegral_of_continuousOn_compact
      (s := Set.Icc (s₀ - δ) (s₀ + δ)) isCompact_Icc (A := (0 : ℝ)) (B := 1)
      (by norm_num) (F := fun s u => deriv Q (s + (c' - s) * u ^ 2) * (1 - u ^ 2)) hcont
    have h2 : ContinuousOn F' (Set.Icc (s₀ - δ) (s₀ + δ)) := by
      simpa only [hF'def] using h
    exact (h2.continuousAt hmem).continuousWithinAt
  have hG'_cont : ContinuousOn G' (Set.Ioo a c) := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    set δ : ℝ := min (s₀ - a) (c - s₀) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min (by linarith) (by linarith))
    have hs₂c : s₀ + δ < c := by
      have h := min_le_right (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hmem : Set.Icc (s₀ - δ) (s₀ + δ) ∈ 𝓝 s₀ :=
      Icc_mem_nhds (by linarith) (by linarith)
    have hQbox : ContinuousOn Q (Set.Icc c' 1) :=
      hQcont.mono (fun x hx => ⟨le_trans hc'a.le hx.1, hx.2⟩)
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (2 * (Real.sqrt (p.2 - p.1)) ^ 3)⁻¹ * Q p.2)
        (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.uIcc c' 1) := by
      rw [Set.uIcc_of_le (le_of_lt hc'1)]
      have hnum : ContinuousOn (fun p : ℝ × ℝ => Q p.2)
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) :=
        hQbox.comp (by fun_prop) (fun p hp => ⟨hp.2.1, hp.2.2⟩)
      have hden : ContinuousOn (fun p : ℝ × ℝ => (2 * (Real.sqrt (p.2 - p.1)) ^ 3)⁻¹)
          (Set.Icc (s₀ - δ) (s₀ + δ) ×ˢ Set.Icc c' 1) := by
        refine ContinuousOn.inv₀ (by fun_prop) ?_
        intro p hp
        have hp0 : 0 < p.2 - p.1 := by linarith [hp.2.1, hp.1.2, hs₂c, hcc']
        exact ne_of_gt (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr hp0) 3))
      exact hden.mul hnum
    have h := Commons.Analysis.Abel.continuousOn_intervalIntegral_of_continuousOn_compact
      (s := Set.Icc (s₀ - δ) (s₀ + δ)) isCompact_Icc (A := c') (B := 1)
      (le_of_lt hc'1) (F := fun s v => (2 * (Real.sqrt (v - s)) ^ 3)⁻¹ * Q v) hcont
    have h2 : ContinuousOn G' (Set.Icc (s₀ - δ) (s₀ + δ)) := by
      simpa only [hG'def] using h
    exact (h2.continuousAt hmem).continuousWithinAt
  have hR_cont : ContinuousOn R (Set.Ioo a c) := by
    intro s₀ hs₀
    obtain ⟨hs₀a, hs₀c⟩ := hs₀
    set δ : ℝ := min (s₀ - a) (c - s₀) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact half_pos (lt_min (by linarith) (by linarith))
    have hs₁a : a < s₀ - δ := by
      have h := min_le_left (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hs₂c : s₀ + δ < c := by
      have h := min_le_right (s₀ - a) (c - s₀); rw [hδdef]; linarith
    have hmem : Set.Icc (s₀ - δ) (s₀ + δ) ∈ 𝓝 s₀ :=
      Icc_mem_nhds (by linarith) (by linarith)
    have hsub : Set.Icc (s₀ - δ) (s₀ + δ) ⊆ Set.Ioo a c :=
      fun s hs => ⟨lt_of_lt_of_le hs₁a hs.1, lt_of_le_of_lt hs.2 hs₂c⟩
    have hFac : ContinuousOn F (Set.Icc (s₀ - δ) (s₀ + δ)) := hF_cont.mono hsub
    have hFac' : ContinuousOn F' (Set.Icc (s₀ - δ) (s₀ + δ)) := hF'_cont.mono hsub
    have hGac : ContinuousOn G' (Set.Icc (s₀ - δ) (s₀ + δ)) := hG'_cont.mono hsub
    have hsqrtc : ContinuousOn (fun s : ℝ => Real.sqrt (c' - s)) (Set.Icc (s₀ - δ) (s₀ + δ)) :=
      Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub continuousOn_id)
    have hne : ∀ s ∈ Set.Icc (s₀ - δ) (s₀ + δ), Real.sqrt (c' - s) ≠ 0 := by
      intro s hs
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hs.2, hs₂c, hcc']))
    have h1 : ContinuousOn (fun s : ℝ => -(1 / Real.sqrt (c' - s))) (Set.Icc (s₀ - δ) (s₀ + δ)) :=
      (continuousOn_const.div hsqrtc hne).neg
    have h2 : ContinuousOn (fun s : ℝ => 2 * Real.sqrt (c' - s) * F' s)
        (Set.Icc (s₀ - δ) (s₀ + δ)) :=
      (continuousOn_const.mul hsqrtc).mul hFac'
    have hA : ContinuousOn (fun s : ℝ => -(1 / Real.sqrt (c' - s)) * F s)
        (Set.Icc (s₀ - δ) (s₀ + δ)) :=
      h1.mul hFac
    have hK : ContinuousOn R (Set.Icc (s₀ - δ) (s₀ + δ)) := by
      rw [hRdef]
      exact (hA.add h2).add hGac
    exact (hK.continuousAt hmem).continuousWithinAt
  -- ## conclusion
  refine hR_cont.congr (fun s hs => ?_)
  exact (hT_deriv s hs).deriv

lemma xw_continuousOn_Xi (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContinuousOn (fun s : ℝ => Xi n h s) (Set.Ioo (13 / 20 : ℝ) (99 / 100)) := by
  have h0 : (0 : ℝ) < 13 / 20 := by norm_num
  have hlt1 : (99 / 100 : ℝ) < 1 := by norm_num
  have hlt : (99 / 100 : ℝ) < 997 / 1000 := by norm_num
  have hsmall0 : ∀ t : ℝ, |h t| ≤ 1 / 100 := fun t => by
    simpa using hsmall 0 (by norm_num) t
  have hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1))
        (Commons.Geometry.Ulam.profileX 1),
      0 < psi h Commons.Geometry.Ulam.semicircle s t :=
    xw_psi_semicircle_pos_small hsupp hsmall0
  obtain ⟨hQcont, hQsmooth⟩ := Work.OddVolterra.Smooth.Q_regularity n hn hh h0 hsupp hsmall0 hmid
  have hQtilde : ∀ i : Fin 2, ContinuousOn (fun s : ℝ =>
      deriv (fun u : ℝ => ∫ v in u..1, (Q n h v) i / Real.sqrt (v - u)) s)
      (Set.Ioo (13 / 20 : ℝ) (99 / 100)) := by
    intro i
    have hcont_i : ContinuousOn (fun v : ℝ => (Q n h v) i) (Set.Icc (13 / 20) 1) :=
      (continuous_apply i).comp_continuousOn hQcont
    have hsm2 : ContDiffOn ℝ 2 (Q n h) (Set.Icc (13 / 20) (999 / 1000)) :=
      hQsmooth (999 / 1000) (by norm_num) (by norm_num)
    have hsm2' : ContDiffOn ℝ 2 (Q n h) (Set.Ioo (13 / 20 : ℝ) (997 / 1000)) :=
      hsm2.mono (fun x hx => ⟨le_of_lt hx.1, by linarith [hx.2]⟩)
    have hsm1 : ContDiffOn ℝ 1 (fun v : ℝ => (Q n h v) i)
        (Set.Ioo (13 / 20 : ℝ) (997 / 1000)) :=
      ((contDiffOn_pi.mp hsm2') i).of_le (by norm_num)
    exact xw_continuousOn_deriv_abel_transform h0 (by norm_num) hlt1 hlt hcont_i hsm1
  have hfun : (fun s : ℝ => Xi n h s) = fun s : ℝ =>
      ![Commons.Geometry.Ulam.profileX 1, Commons.Geometry.Ulam.profileX 1,
        deriv (fun u : ℝ => ∫ v in u..1, (Q n h v) 0 / Real.sqrt (v - u)) s,
        deriv (fun u : ℝ => ∫ v in u..1, (Q n h v) 1 / Real.sqrt (v - u)) s] := by
    funext s
    simp [Xi, Qtilde]
  rw [hfun, continuousOn_pi]
  intro i
  fin_cases i
  · simpa using (continuousOn_const (c := Commons.Geometry.Ulam.profileX 1)
      (s := Set.Ioo (13 / 20 : ℝ) (99 / 100)))
  · simpa using (continuousOn_const (c := Commons.Geometry.Ulam.profileX 1)
      (s := Set.Ioo (13 / 20 : ℝ) (99 / 100)))
  · simpa using hQtilde 0
  · simpa using hQtilde 1



/-! ## The tail integral, with the frozen diagonal value -/

/-- Continuity of the frozen tail `s ↦ ∫_{19/20}^1 ΘM(s, max s σ, baseState σ) dσ`, the manifest
form of `s ↦ ∫_{19/20}^1 thetac n h s σ (baseState σ) dσ` on the window of use. -/
lemma xw_continuousOn_tail (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContinuousOn (fun s : ℝ =>
        ∫ σ in (19 / 20 : ℝ)..(1 : ℝ),
          KernelExt.ThetaM n h s (max s σ) (baseState σ))
      (Set.Ioo (13 / 20 : ℝ) (99 / 100)) := by
  have hmap : Continuous (fun p : ℝ × ℝ => (p.1, max p.1 p.2, baseState p.2)) :=
    continuous_fst.prodMk ((continuous_fst.max continuous_snd).prodMk
      (xw_continuous_baseState.comp continuous_snd))
  have hΘ : ContinuousOn (fun q : ℝ × ℝ × St => KernelExt.ThetaM n h q.1 q.2.1 q.2.2)
      Work.Anchor.Good := (Work.Anchor.ThetaM_contDiffOn_Good n hh hsmall).continuousOn
  have hK : ContinuousOn (fun p : ℝ × ℝ =>
      KernelExt.ThetaM n h p.1 (max p.1 p.2) (baseState p.2))
      (Set.Icc (13 / 20 : ℝ) (99 / 100) ×ˢ Set.uIcc (19 / 20 : ℝ) 1) := by
    refine hΘ.comp hmap.continuousOn ?_
    rintro ⟨s, σ⟩ ⟨hs, hσ⟩
    rw [Set.uIcc_of_le (by norm_num : (19 : ℝ) / 20 ≤ 1)] at hσ
    have hb0 : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
    have hb1 : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
    have hpx : 17 / 25 ≤ Commons.Geometry.Ulam.profileX σ :=
      xw_profileX_ge_17_25 (by rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2])
    refine ⟨by linarith [hs.1], by linarith [hs.2], ?_, ?_, ?_, ?_⟩
    · dsimp only
      linarith [hs.1, le_max_left s σ]
    · dsimp only
      exact max_lt (by linarith [hs.2]) (by linarith [hσ.2])
    · dsimp only
      rw [hb0, abs_of_nonneg (by linarith)]; linarith
    · dsimp only
      rw [hb1, abs_of_nonneg (by linarith)]; linarith
  have h := Commons.Analysis.Abel.continuousOn_intervalIntegral_of_continuousOn_compact
    (s := Set.Icc (13 / 20 : ℝ) (99 / 100)) isCompact_Icc (A := (19 / 20 : ℝ)) (B := 1)
    (by norm_num) (F := fun s σ => KernelExt.ThetaM n h s (max s σ) (baseState σ)) hK
  exact h.mono (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)

/-! ## The cut-off `cs` -/

/-- The support of the slope bump `cs` is contained in the window `(13/20, 99/100)`. -/
lemma xw_tsupport_cs_subset :
    tsupport (fun s : ℝ => (cs : ℝ → ℝ) s) ⊆ Set.Ioo (13 / 20 : ℝ) (99 / 100) := by
  have hsupp_cs : Function.support (fun s : ℝ => (cs : ℝ → ℝ) s) ⊆
      Set.Icc (wCenter - 4 / 25) (wCenter + 4 / 25) := by
    intro s hs
    have h : |s - wCenter| < 4 / 25 := by
      by_contra h
      exact hs (cs_eq_zero (le_of_not_gt h))
    rw [abs_lt] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hts := closure_minimal hsupp_cs isClosed_Icc
  refine fun s hs => ?_
  have h := hts hs
  rw [wCenter] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ## The main theorem -/

theorem XW_continuous (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    Continuous (Work.OddVolterra.Window.XW n h) := by
  have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall k (by omega) s
  have hU : IsOpen (Set.Ioo (13 / 20 : ℝ) (99 / 100)) := isOpen_Ioo
  have hXi : ContinuousOn (fun s : ℝ => Xi n h s) (Set.Ioo (13 / 20 : ℝ) (99 / 100)) :=
    xw_continuousOn_Xi n hn hh hsupp hsmall1
  have htail : ContinuousOn (fun s : ℝ =>
      ∫ σ in (19 / 20 : ℝ)..(1 : ℝ), thetac n h s σ (baseState σ))
      (Set.Ioo (13 / 20 : ℝ) (99 / 100)) := by
    refine (xw_continuousOn_tail n hh hsmall1).congr ?_
    intro s hs
    refine intervalIntegral.integral_congr (fun σ hσ => ?_)
    rw [Set.uIcc_of_le (by norm_num : (19 : ℝ) / 20 ≤ 1)] at hσ
    have hs3 : (3 / 5 : ℝ) ≤ s := by linarith [hs.1]
    have hσ3 : (3 / 5 : ℝ) ≤ σ := by linarith [hσ.1]
    have hpx : 17 / 25 ≤ Commons.Geometry.Ulam.profileX σ :=
      xw_profileX_ge_17_25 (by rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2])
    have hb0 : baseState σ 0 = Commons.Geometry.Ulam.profileX σ := rfl
    have hb1 : baseState σ 1 = Commons.Geometry.Ulam.profileX σ := rfl
    exact tw_thetac_eq n hn hh hsmall1 hs3 hσ3 (by rw [hb0]; linarith) (by rw [hb1]; linarith)
  have hF : ContinuousOn (fun s : ℝ => Xi n h s +
      ∫ σ in (19 / 20 : ℝ)..(1 : ℝ), thetac n h s σ (baseState σ))
      (Set.Ioo (13 / 20 : ℝ) (99 / 100)) := hXi.add htail
  have hcs : Continuous (fun s : ℝ => (cs : ℝ → ℝ) s) := ContDiffBump.continuous cs
  have hsm := xw_continuous_smul_of_continuousOn hU hcs hF xw_tsupport_cs_subset
  rw [show XW n h = fun s : ℝ => (cs : ℝ → ℝ) s •
      (Xi n h s + ∫ σ in wRight..(1 : ℝ), thetac n h s σ (baseState σ)) from rfl]
  exact hsm

end

end Work.OddVolterra.Window
