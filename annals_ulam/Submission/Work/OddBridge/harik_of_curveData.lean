import Mathlib
import Submission.Work.OddBridge.Defs
import Submission.Work.OddVolterra.Assembly
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Abel.abel_form_of_volterra_form
import Submission.Work.OddBridge.KvecM_contDiffOn_box
import Submission.Work.OddBridge.KvecM_eq_Kvec
import Submission.Work.OddBridge.Kden_radicand_pos_of_curve
import Submission.Work.OddBridge.abel_inversion_continuous_endpoint
import Submission.Work.OddBridge.abel_integral_Kvec_eq_KvecM
import Submission.Work.OddBridge.contDiffOn_Q_Ioo
import Submission.Work.OddBridge.hmid_of_curveData
import Submission.Work.OddBridge.dvi_of_volterra_regular
import Submission.Work.OddBridge.theta_row_integrable
import Submission.Work.OddVolterra.Smooth.E1_E2_continuousOn_Icc

/-!
# The Abel inversion `(arik)` of the transition-slope curve

Ryabogin's odd-dimensional case (Annals 195 (2022), `W3.tex`) produces, by the Volterra
construction of the transition-slope chapter, a curve `(x,y)` with `CurveData`, and then needs
the *Abel system* `(arik)`

`∫_s^1 K(s,σ,z(σ),z'(σ)) / √(σ-s) dσ = Q(s)`

for the perturbation `h` and the inhomogeneities `E₁`, `E₂`.  This file derives it from the
Volterra system `(hah44)` (`CurveData.volterra`) by Abel inversion (NRZ Lemma 8) and records it as
`Work.OddBridge.Harik`.

The chain is

* `volterra_row_zero`, `volterra_row_one` (`dvi_of_volterra_regular`): the last two rows of the
  Volterra system are the two scalar rows of `(dvi)`, `-G₂(s,s)ᵢ + ∫_s^1 ∂₁(G₂)ᵢ = Q̃ᵢ`;
* `G2_diag_eq`, `G2_deriv_eq` below: the two `KvecM ↔ Kvec` bridges replacing the paper's kernel
  (discontinuous at the diagonal) by the manifest one, componentwise;
* `abel_inversion_continuous_endpoint`: `(dvi) ⇒ (arik)` for the manifest kernel;
* `abel_integral_Kvec_eq_KvecM`: the Abel integral of the two kernels is the same.

The one analytic input, the interval integrability of the `Θ`-integrand, is
`Work.OddBridge.theta_row_integrable` (Lemma 8 of NRZ needs it to read the second component of the
vector-valued Volterra integral off componentwise).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option maxHeartbeats 2000000

namespace Work.OddBridge

open Work.OddVolterra

noncomputable section

/-! ## The tail of the support: `h` vanishes on `[1 - τ, ∞)` -/

/-- A continuous perturbation whose support lies in `[1 - 2τ, 1 - τ]` vanishes on `[1 - τ, ∞)`. -/
theorem eq_zero_of_support_ge {h : ℝ → ℝ} (hh : Continuous h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau)) :
    ∀ s : ℝ, 1 - tau ≤ s → h s = 0 := by
  intro s hs
  have hcont : ContinuousAt h s := hh.continuousAt
  have hright : Filter.Tendsto h (𝓝[Set.Ioi s] s) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : s < t := ht
    have hnotmem : t ∉ Function.support h := by
      intro hmem
      have hmem' := hsupp (Function.mem_support.mpr hmem)
      exact absurd hmem'.2 (by linarith)
    exact (Function.notMem_support.mp hnotmem).symm
  exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds) hright

/-! ## The two `KvecM ↔ Kvec` bridges, componentwise -/

/-- On the triangle `a ≤ s ≤ σ ≤ 1` the manifest kernel `KvecM` equals the paper's `Kvec`, for
the curve data of the transition-slope construction. -/
theorem kvecM_eq_kvec_of_curveData (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hdata : CurveData n h x y) {a : ℝ} (ha : 0 < a) :
    ∀ s σ : ℝ, a ≤ s → s ≤ σ → σ ≤ 1 →
      KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ) := by
  obtain ⟨hposy, hposx⟩ := Kden_radicand_pos_of_curve n hh hsupp hdata
  intro s σ has hsσ hσ1
  have hs0 : 0 < s := lt_of_lt_of_le ha has
  have hσ0 : 0 < σ := lt_of_lt_of_le hs0 hsσ
  have hs1 : s ≤ 1 := le_trans hsσ hσ1
  exact KvecM_eq_Kvec n hn hh hsσ _ _ _ _ (hposy s σ hs0 hσ0 hs1 hσ1)
    (hposx s σ hs0 hσ0 hs1 hσ1)

/-- **The diagonal bridge.**  `G₂(s,s,z)` computed with the paper's kernel is the `τ`-integral of
the manifest kernel, componentwise. -/
theorem G2_diag_eq (n : ℕ) {h x y : ℝ → ℝ} {a : ℝ}
    (hae : ∀ s σ : ℝ, a ≤ s → s ≤ σ → σ ≤ 1 →
      KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ))
    {s : ℝ} (has : a ≤ s) (hs1 : s ≤ 1) (i : Fin 2) :
    (G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) i =
      ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ *
        (KvecM n h s s (x s) (y s) (deriv x s) (deriv y s)) i := by
  rw [show (G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) i =
      ∫ τ in (0 : ℝ)..1,
        (Kvec n h (s + τ * (s - s)) s (x s) (y s) (deriv x s) (deriv y s)) i /
          Real.sqrt (τ * ((1 : ℝ) - τ)) from rfl]
  refine intervalIntegral.integral_congr (fun τ _ => ?_)
  have harg : s + τ * (s - s) = s := by ring
  rw [harg, hae s s has le_rfl hs1, div_eq_mul_inv, mul_comm]

/-- **The derivative bridge.**  On the neighbourhood `(a,σ)` of `s` the two functions agree, so
their derivatives at `s` do.  No regularity is needed. -/
theorem G2_deriv_eq (n : ℕ) {h x y : ℝ → ℝ} {a : ℝ}
    (hae : ∀ s σ : ℝ, a ≤ s → s ≤ σ → σ ≤ 1 →
      KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ))
    {s σ : ℝ} (hsa : a < s) (hsσ : s < σ) (hσ1 : σ ≤ 1) (i : Fin 2) :
    deriv (fun u : ℝ => (G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s =
      deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ *
        (KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo a σ from ⟨hsa, hsσ⟩)] with u hu
  rw [show (G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i =
      ∫ τ in (0 : ℝ)..1,
        (Kvec n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i /
          Real.sqrt (τ * ((1 : ℝ) - τ)) from rfl]
  refine intervalIntegral.integral_congr (fun τ hτ => ?_)
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
  have hτ0 : 0 ≤ τ := hτ.1
  have hτ1 : τ ≤ 1 := hτ.2
  have hsub : 0 ≤ σ - u := by linarith [hu.2]
  have hle_a : a ≤ u + τ * (σ - u) := by
    nlinarith [mul_nonneg hτ0 hsub, hu.1]
  have hle_σ : u + τ * (σ - u) ≤ σ := by
    nlinarith [mul_le_of_le_one_left hsub hτ1]
  rw [hae (u + τ * (σ - u)) σ hle_a hle_σ hσ1, div_eq_mul_inv, mul_comm]

/-! ## The two scalar rows of `(dvi)` -/

/-- **The scalar rows of `(dvi)`** in the manifest vocabulary: obtained from the last two rows of
the Volterra system by the two bridges above.  `hintTheta` is the interval integrability of the
`Θ`-integrand, which is what makes the corresponding component of the vector-valued Volterra
integral computable. -/
theorem dvi_row (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hdata : CurveData n h x y) {a : ℝ} (ha : 0 < a)
    (hvol : VolterraEqOn n h x y (Set.Ioo 0 1))
    (hintTheta : ∀ s ∈ Set.Ioo a 1, IntervalIntegrable
      (fun σ : ℝ => Theta n h s σ (stateOf x y σ)) volume s 1)
    (hae : ∀ s σ : ℝ, a ≤ s → s ≤ σ → σ ≤ 1 →
      KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) :
    ∀ i : Fin 2, ∀ s ∈ Set.Ioo a 1,
      - (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ *
          (KvecM n h s s (x s) (y s) (deriv x s) (deriv y s)) i)
        + (∫ σ in s..1, deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
            (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ *
            (KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s)
      = deriv (fun u : ℝ => ∫ v in u..1,
          (Real.sqrt (v - u))⁻¹ * (Q n h v) i) s := by
  intro i s hs
  have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans ha hs.1, hs.2⟩
  have hrow : - (G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) i
      = - (∫ σ in s..1,
            deriv (fun u : ℝ => (G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s)
        + (Qtilde n h s) i := by
    fin_cases i
    · simpa using volterra_row_zero n hvol hs01 (hintTheta s hs)
    · simpa using volterra_row_one n hvol hs01 (hintTheta s hs)
  set T1 : ℝ := ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ *
    (KvecM n h s s (x s) (y s) (deriv x s) (deriv y s)) i with hT1
  set T2 : ℝ := ∫ σ in s..1, deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
    (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ *
    (KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s with hT2
  set R : ℝ := deriv (fun u : ℝ => ∫ v in u..1,
    (Real.sqrt (v - u))⁻¹ * (Q n h v) i) s with hR
  have hdiag : (G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) i = T1 :=
    G2_diag_eq n hae (le_of_lt hs.1) (le_of_lt hs.2) i
  have hsecond : (∫ σ in s..1,
        deriv (fun u : ℝ => (G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i) s) = T2 := by
    refine intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2) (fun σ hσ => ?_)
    exact G2_deriv_eq n hae hs.1 hσ.1 (le_of_lt hσ.2) i
  have hfunQ : (fun u : ℝ => ∫ v in u..1, (Q n h v) i / Real.sqrt (v - u))
      = fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ * (Q n h v) i := by
    funext u
    refine intervalIntegral.integral_congr (fun v _ => ?_)
    rw [div_eq_mul_inv, mul_comm]
  have hQ : (Qtilde n h s) i = R := by
    have h1 : (Qtilde n h s) i = deriv (fun u : ℝ =>
        ∫ v in u..1, (Q n h v) i / Real.sqrt (v - u)) s := by
      fin_cases i <;> simp [Qtilde]
    rw [h1, hfunQ, hR]
  rw [hdiag, hsecond, hQ] at hrow
  linarith [hrow]


/-! ## The Abel system `(arik)` on a compact slope interval -/

/-- **The Abel inversion of the transition-slope curve.**  From the Volterra system `(hah44)`
(the field `volterra` of `CurveData`, together with the integrability of the `Θ`-integrand and the
continuity of `Q`), the Abel system `(arik)` holds on every compact subinterval of `(0,1)`. -/
theorem abel_of_curveData (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hdata : CurveData n h x y) {a : ℝ} (ha : 0 < a)
    (hintTheta : ∀ s ∈ Set.Ioo a 1, IntervalIntegrable
      (fun σ : ℝ => Theta n h s σ (stateOf x y σ)) volume s 1)
    (hQcont : ContinuousOn (Q n h) (Set.Icc a 1)) :
    ∀ i : Fin 2, ∀ s ∈ Set.Ioo a 1,
      (∫ σ in s..1, (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i /
          Real.sqrt (σ - s)) = (Q n h s) i := by
  have hmid := (hmid_of_curveData n hh hsupp hdata).1
  have hae := kvecM_eq_kvec_of_curveData n hn hh hsupp hdata ha
  have hae_lt : ∀ s σ : ℝ, a ≤ s → s < σ → σ ≤ 1 →
      KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ) :=
    fun s σ hs hsσ hσ1 => hae s σ hs (le_of_lt hsσ) hσ1
  have hdvi := dvi_row n hn hh hsupp hdata ha hdata.volterra hintTheta hae
  have hQcont_i : ∀ i : Fin 2, ContinuousOn (fun u : ℝ => (Q n h u) i) (Set.Icc a 1) := by
    intro i
    have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).continuous).comp_continuousOn hQcont
    simpa [Function.comp_def, ContinuousLinearMap.proj_apply] using h
  have hQsmooth_i : ∀ i : Fin 2, ∀ b : ℝ, a < b → b < 1 →
      ContDiffOn ℝ 2 (fun u : ℝ => (Q n h u) i) (Set.Icc a b) := by
    intro i b hab hb1
    have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) 1 :=
      fun t ht => ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb1⟩
    have hQ : ContDiffOn ℝ (⊤ : ℕ∞) (Q n h) (Set.Icc a b) :=
      (contDiffOn_Q_Ioo n hn hh hmid).mono hsub
    have hj : ContDiffOn ℝ (⊤ : ℕ∞) (fun v : Fin 2 → ℝ => v i) Set.univ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).contDiff.contDiffOn
    have hcomp := hj.comp hQ (fun u _ => Set.mem_univ _)
    refine (show ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => (Q n h u) i) (Set.Icc a b) from ?_).of_le
      (WithTop.coe_le_coe.mpr le_top)
    simpa [Function.comp_def, ContinuousLinearMap.proj_apply] using hcomp
  have hbox : ∀ i : Fin 2, ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => (KvecM n h p.1 p.2 (x p.2) (y p.2) (deriv x p.2) (deriv y p.2)) i)
      (Set.Icc a 1 ×ˢ Set.Icc a 1) := by
    obtain ⟨hposy, hposx⟩ := Kden_radicand_pos_of_curve n hh hsupp hdata
    have hposy' : ∀ s σ : ℝ, s ∈ Set.Icc a 1 → σ ∈ Set.Icc a 1 → 0 < Kden h s σ (y σ) :=
      fun s σ hs hσ => Real.sqrt_pos.mpr
        (hposy s σ (lt_of_lt_of_le ha hs.1) (lt_of_lt_of_le ha hσ.1) hs.2 hσ.2)
    have hposx' : ∀ s σ : ℝ, s ∈ Set.Icc a 1 → σ ∈ Set.Icc a 1 → 0 < Kden h s σ (-(x σ)) :=
      fun s σ hs hσ => Real.sqrt_pos.mpr
        (hposx s σ (lt_of_lt_of_le ha hs.1) (lt_of_lt_of_le ha hσ.1) hs.2 hσ.2)
    have hb := KvecM_contDiffOn_box (x := x) (y := y) n hh hdata.smooth_x hdata.smooth_y ha le_rfl
      hposy' hposx'
    intro i
    have hj : ContDiffOn ℝ 2 (fun v : Fin 2 → ℝ => v i) Set.univ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).contDiff.contDiffOn
    have hcomp := hj.comp hb (fun u _ => Set.mem_univ _)
    simpa [Function.comp_def, ContinuousLinearMap.proj_apply] using hcomp
  intro i s hs
  have habel := abel_inversion_continuous_endpoint (E := ℝ)
    (K := fun s σ => (KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i)
    (Q := fun s => (Q n h s) i) ha (hbox i) (hQcont_i i) (hQsmooth_i i) (by
      intro t ht
      have h := hdvi i t ht
      simpa only [smul_eq_mul] using h) s hs
  have hKi : (∫ σ in s..1, (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i /
        Real.sqrt (σ - s)) =
      (∫ σ in s..1, (KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i /
        Real.sqrt (σ - s)) := by
    fin_cases i
    · exact (abel_integral_Kvec_eq_KvecM n ha hae_lt (le_of_lt hs.1) (le_of_lt hs.2)).1
    · exact (abel_integral_Kvec_eq_KvecM n ha hae_lt (le_of_lt hs.1) (le_of_lt hs.2)).2
  refine hKi.trans ?_
  exact (intervalIntegral.integral_congr
    (fun σ _ => by simp only [smul_eq_mul]; rw [div_eq_mul_inv, mul_comm])).trans habel

/-! ## The continuity of `Q` on `[a,1]` -/

/-- `Q` is continuous on `[a,1]` for `a > 0`: its two components are `-E₁ + (momentRHS)⁽ⁿ⁺¹⁾`
and `-E₂`, and both `E₁`, `E₂` are continuous up to `1`. -/
theorem Q_continuousOn_Icc_of_curveData (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hdata : CurveData n h x y) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (Q n h) (Set.Icc a 1) := by
  have hmid := (hmid_of_curveData n hh hsupp hdata).1
  obtain ⟨hE1, hE2⟩ := Work.OddVolterra.Smooth.E1_E2_continuousOn_Icc n hn hh hsupp hmid ha
  have hmr : ContDiff ℝ (⊤ : ℕ∞) (momentRHS n) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => 1 + s ^ 2) := by fun_prop
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Real.sqrt (1 + s ^ 2)) :=
      ContDiff.sqrt h1 (fun x => by positivity)
    have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹) :=
      ContDiff.inv h2 (fun x => by positivity)
    unfold momentRHS
    exact ContDiff.mul contDiff_const h3
  have hRHS : ContinuousOn (fun s : ℝ => iteratedDeriv (n + 1) (momentRHS n) s)
      (Set.Icc a 1) := by
    simpa [iteratedDeriv_eq_iterate] using
      ((ContDiff.iterate_deriv (n + 1) hmr).continuous.continuousOn (s := Set.Icc a 1))
  have h0 : ContinuousOn (fun y : ℝ => -E1 n h y + iteratedDeriv (n + 1) (momentRHS n) y)
      (Set.Icc a 1) := (hE1.neg.add hRHS).congr (fun y _ => by simp)
  have h1 : ContinuousOn (fun y : ℝ => -E2 n h y) (Set.Icc a 1) :=
    (hE2.neg).congr (fun y _ => by simp)
  rw [continuousOn_pi]
  intro i
  fin_cases i
  · convert h0 using 1
    funext y; simp [Q]
  · convert h1 using 1
    funext y; simp [Q]

/-! ## The main theorem -/

theorem harik_of_curveData (n : ℕ) (hn : 1 ≤ n) {h x y : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    (hdata : Work.OddVolterra.CurveData n h x y) :
    Work.OddBridge.Harik n h x y := by
  rw [harik_iff]
  intro a c ha hac hc1 s hs
  set a' : ℝ := a / 2 with ha'def
  have ha' : 0 < a' := by rw [ha'def]; linarith
  have ha'a : a' < a := by rw [ha'def]; linarith
  have hs' : s ∈ Set.Ioo a' 1 := ⟨lt_of_lt_of_le ha'a hs.1, lt_of_le_of_lt hs.2 hc1⟩
  have hQcont := Q_continuousOn_Icc_of_curveData n hn hh hsupp hdata ha'
  have hintTheta : ∀ s ∈ Set.Ioo a' 1, IntervalIntegrable
      (fun σ : ℝ => Theta n h s σ (stateOf x y σ)) volume s 1 := by
    intro s hs
    exact theta_row_integrable n hn hh hsupp hdata ha' s hs
  have h := abel_of_curveData n hn hh hsupp hdata ha' hintTheta hQcont
  exact ⟨h 0 s hs', h 1 s hs'⟩

end

end Work.OddBridge
