import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12Calc
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Qang_le
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12dens_hasDerivAt
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FKDeriv
import Submission.Work.FTS_RegExport.RXT.STC.L12_sub_C4
import Submission.Work.FTS_RegExport.RXR1.hasDerivAt_of_tendsto_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.L12Deriv` — the `z`-derivative and the bounds of `L₁₂` along the approximants

The approximating families of `LimApprox` are class-`C` with uniformly bounded `ℋ⁴`-norm and
`ℋ⁴`-Lipschitz in the fake time.  This module turns those data into

* the derivative of `L₁₂ (F_* + slice (gn n) τ)` (via `FM.hasDerivAt_L12`, using the
  additivity `dens_add` of the density and the derivative formula `L12dens_hasDerivAt`);
* the `z`-derivative of `L₁₂` of the limit profile (passing to the limit with
  `RXR1.hasDerivAt_of_tendsto_deriv`);
* the uniform bounds and the fake-time Lipschitz bounds of `L₁₂` and of `FK`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- `L₁₂dens (F_* + u) = 2β/(1+s)² + L₁₂dens u` for `s > 0` (with the standing data of `u`). -/
theorem L12dens_Ftau_eq {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {u : ℝ → ℝ → ℝ} {C0 : ℝ}
    (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k u z θ| ≤ C0 * SW z)
    {s : ℝ} (hs : 0 < s) :
    Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.Fstar β z θ + u z θ) s
      = 2 * β / (1 + s) ^ 2 + Work.FM.L12dens Work.Spaces.K u s := by
  have h := dens_add (β := β) hβ hβ1 hC0 h4 hbd (u := u) hs
  simpa only [Work.Construction.L12dens] using h

/-- The reference density `2β/(1+s)²` is integrable on a tail. -/
theorem integrable_Fstar_dens {β : ℝ} (hβ : 0 < β) {a : ℝ} (ha : 0 < a) :
    Integrable (fun s : ℝ => 2 * β / (1 + s) ^ 2) (volume.restrict (Set.Ioi a)) := by
  have hp : Integrable (fun s : ℝ => s ^ (-(2 : ℝ))) (volume.restrict (Set.Ioi a)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-(2 : ℝ)) < -1) ha
  refine Integrable.mono' (hp.const_mul (2 * β)) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (s := Set.Ioi a) ?_ measurableSet_Ioi
    exact continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
      (fun s hs => pow_ne_zero 2 (ne_of_gt (by linarith [ha.trans hs] : (0 : ℝ) < 1 + s)))
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : 0 < s := ha.trans hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * β / (1 + s) ^ 2)]
    have h1 : 1 / (1 + s) ^ 2 ≤ 1 / s ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [hs0])
    calc 2 * β / (1 + s) ^ 2 = 2 * β * (1 / (1 + s) ^ 2) := by ring
      _ ≤ 2 * β * (1 / s ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * β * s ^ (-(2 : ℝ)) := by
          rw [Real.rpow_neg (le_of_lt hs0), Real.rpow_two, one_div]


/-! ## §2 The `z`-derivatives of `FK (F(τ))` and of `L₁₂ (F(τ))` -/

/-- **The `z`-jets of `FK` of the limit profile are the moments `Qlim · j`.** -/
theorem FK_DzIter_eq {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ) {Cw CB : ℝ}
    (hCw : 0 ≤ Cw) (hCB : 0 ≤ CB)
    (h4 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (h2 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hsl : ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB)
    (hjet : ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ)))
    {z : ℝ} (hz : 0 < z) {j : ℕ} (hj : j ≤ 2) :
    Work.Spaces.DzIter j (fun z _ => Work.Construction.FK (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z 0
      = Qlim α g τ j z := by
  have hFK : ∀ x : ℝ, 0 < x → Work.Construction.FK (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) x
      = Qlim α g τ 0 x := fun x hx => Qlim_eq_FK hα hτ hx
  have hd1 : ∀ x : ℝ, 0 < x → HasDerivAt (Qlim α g τ 0) (Qlim α g τ 1 x / x) x :=
    fun x hx => Qlim_hasDerivAt_1 (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet hx
  have hd2 : ∀ x : ℝ, 0 < x → HasDerivAt (Qlim α g τ 1) (Qlim α g τ 2 x / x) x :=
    fun x hx => Qlim_hasDerivAt_2 (α := α) hα hα13 hCw hCB h4 hbd h2 hsl hjet hx
  have hstep1 : ∀ x : ℝ, 0 < x →
      Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) x 0
      = Qlim α g τ 1 x := by
    intro x hx
    have hd : HasDerivAt (fun y => Work.Construction.FK (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) y)
        (Qlim α g τ 1 x / x) x :=
      (hd1 x hx).congr_of_eventuallyEq
        (by filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy; exact (hFK y hy))
    show x * deriv (fun y => Work.Construction.FK (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) y) x
      = Qlim α g τ 1 x
    rw [hd.deriv]
    field_simp
  have hstep2 : Work.Spaces.DzIter 2 (fun z _ => Work.Construction.FK (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z) z 0
      = Qlim α g τ 2 z := by
    have hcongr : (fun y => Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z) y 0) =ᶠ[𝓝 z] Qlim α g τ 1 := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact hstep1 y hy
    have hd : HasDerivAt (fun y => Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z) y 0) (Qlim α g τ 2 z / z) z :=
      (hd2 z hz).congr_of_eventuallyEq hcongr
    show z * deriv (fun y => Work.Spaces.DzIter 1 (fun z _ => Work.Construction.FK
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ) z) y 0) z = Qlim α g τ 2 z
    rw [hd.deriv]
    field_simp
  interval_cases j
  · show Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.RXT.GR α g) τ) z = Qlim α g τ 0 z
    exact hFK z hz
  · exact hstep1 z hz
  · exact hstep2


/-! ## §3 The derivative of `L₁₂` of the limit profile -/

/-- The `Ftau`-unfolding used throughout. -/
theorem Ftau_unfold (α : ℝ) (g : Fam) (τ : ℝ) :
    Work.Construction.Ftau α g τ
      = fun z θ => Work.Construction.Fstar α z θ + g z θ τ := rfl

/-- The derivative of the reference density `2β/(1+s)²`. -/
theorem hasDerivAt_Fstar_dens {β x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun s : ℝ => 2 * β / (1 + s) ^ 2) (-(4 * β / (1 + x) ^ 3)) x := by
  have h1 : HasDerivAt (fun s : ℝ => (1 + s) ^ 2) (2 * (1 + x)) x := by
    have h0 : HasDerivAt (fun s : ℝ => 1 + s) (1 : ℝ) x := by
      simpa only [id_eq, add_comm] using (hasDerivAt_id x).const_add 1
    have hp := h0.pow 2
    convert hp using 1
    ring
  have h2 : HasDerivAt (fun s : ℝ => 2 * β / (1 + s) ^ 2)
      ((0 * (1 + x) ^ 2 - 2 * β * (2 * (1 + x))) / ((1 + x) ^ 2) ^ 2) x :=
    (hasDerivAt_const x (2 * β)).div h1 (by positivity)
  convert h2 using 1
  field_simp
  ring

/-- **`L₁₂ (F(τ))` is differentiable with derivative `-L₁₂dens (F(τ))`**, by passing to the
limit in the corresponding statement for the approximants. -/
theorem L12_hasDerivAt {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {g : Fam} {τ : ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (h4 : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
      Work.FTS.EllipticEst.Q0)
    (hbd : ∀ (n : ℕ) (k : ℕ), k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => slice (gn n) τ z θ) Filter.atTop
        (𝓝 (slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ)))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x => Work.Construction.L12 (Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) x)
      (-(Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) z)) z := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hsplit : ∀ (n : ℕ) {s : ℝ}, 0 < s →
      Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) s
      = 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2
        + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s := by
    intro n s hs
    have h := dens_add (β := Work.FTS.Regularity.pExp α) hβ hβ1 hCw (h4 n) (hbd n)
      (u := slice (gn n) τ) hs
    rw [Ftau_unfold]
    exact h
  have hder : ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      HasDerivAt (fun y => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) y)
        (-(Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (gn n) τ) x)) x := by
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hxa : 0 < x / 2 := by linarith
    have hcontF : ContinuousAt (fun s : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2) x :=
      (hasDerivAt_Fstar_dens hx0).continuousAt
    have hcontU : ContinuousAt (fun s : ℝ => Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s) x :=
      (Work.FTS_RegExport.RXT.L12Iter.L12dens_continuousOn hCw (h4 n) (hbd n)).continuousAt
        (isOpen_Ioi.mem_nhds hx0)
    have hcontD : ContinuousAt (fun s : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) s) x :=
      (hcontF.add hcontU).congr (by
        filter_upwards [isOpen_Ioi.mem_nhds hx0] with s hs
        exact (hsplit n hs).symm)
    have hIntF : Integrable (fun s : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2)
        (volume.restrict (Set.Ioi (x / 2))) := integrable_Fstar_dens hβ hxa
    have hIntU : Integrable (fun s : ℝ => Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s)
        (volume.restrict (Set.Ioi (x / 2))) :=
      Work.FTS_RegExport.RXT.L12Iter.L12dens_integrableOn hCw (h4 n) (hbd n) hxa
    have hIntD : Integrable (fun s : ℝ => Work.FM.L12dens Work.Spaces.K
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) s)
        (volume.restrict (Set.Ioi (x / 2))) :=
      (hIntF.add hIntU).congr (by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
        exact (hsplit n (lt_trans hxa (by simpa using hs))).symm)
    exact Work.FM.hasDerivAt_L12 hIntD hcontD (by linarith)
  have hvdiff : ∀ n : ℕ, DifferentiableOn ℝ (fun x => -(Work.FM.L12dens Work.Spaces.K
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ) x))
      (Set.Ioo (z / 2) (2 * z)) := by
    intro n
    refine DifferentiableOn.neg ?_
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hd1 : HasDerivAt (fun s : ℝ => Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s)
        ((Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x)
          / x ^ 2) x := L12dens_hasDerivAt hCw (h4 n) (hbd n) hx0
    have hsum := (hasDerivAt_Fstar_dens (β := Work.FTS.Regularity.pExp α) hx0).add hd1
    refine (hsum.congr_of_eventuallyEq ?_).differentiableAt.differentiableWithinAt
    filter_upwards [isOpen_Ioi.mem_nhds hx0] with s hs
    show Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
      (gn n) τ) s
      = 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2
        + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s
    exact hsplit n hs
  have hMabs : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) x| ≤ M := by
    refine ⟨2 * Work.FTS.Regularity.pExp α + 3 * (Real.pi / 2) * Cw, by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    rw [hsplit n hx0]
    have h1 : |2 * Work.FTS.Regularity.pExp α / (1 + x) ^ 2| ≤ 2 * Work.FTS.Regularity.pExp α := by
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + x) ^ 2)]
      have h5 : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith
      nlinarith [h5, hβ]
    have h2 : |Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) x| ≤ 3 * (Real.pi / 2) * Cw := by
      have h := Work.FTS_RegExport.RXT.L12Iter.abs_L12dens_le hCw (h4 n) (hbd n) hx0
      have h3 : x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2 ≤ 1 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 + x) ^ 2)]
        by_cases hx1 : 1 ≤ x
        · have h4 : x ^ ((1 : ℝ) / 2) ≤ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
          have h5 : x ^ (1 : ℝ) = x := Real.rpow_one x
          have h6 : x ≤ 1 * (1 + x) ^ 2 := by nlinarith
          calc x ^ ((1 : ℝ) / 2) ≤ x ^ (1 : ℝ) := h4
            _ = x := h5
            _ ≤ 1 * (1 + x) ^ 2 := h6
        · have h4 : x ^ ((1 : ℝ) / 2) ≤ 1 :=
            Real.rpow_le_one hx0.le (not_le.mp hx1).le (by norm_num)
          have h6 : (1:ℝ) ≤ (1 + x) ^ 2 := by nlinarith
          linarith
      have h4' : (0:ℝ) ≤ 3 * (Real.pi / 2) * Cw := by positivity
      calc |Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) x|
          ≤ 3 * (Real.pi / 2) * Cw * (x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) := h
        _ ≤ 3 * (Real.pi / 2) * Cw * 1 := mul_le_mul_of_nonneg_left h3 h4'
        _ = 3 * (Real.pi / 2) * Cw := by ring
    calc |2 * Work.FTS.Regularity.pExp α / (1 + x) ^ 2
          + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) x|
        ≤ |2 * Work.FTS.Regularity.pExp α / (1 + x) ^ 2|
          + |Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) x| := abs_add_le _ _
      _ ≤ 2 * Work.FTS.Regularity.pExp α + 3 * (Real.pi / 2) * Cw := add_le_add h1 h2
  have hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |-(Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) x)| ≤ M := by
    obtain ⟨M, hM0, hMb⟩ := hMabs
    exact ⟨M, hM0, fun n x hx => by rw [abs_neg]; exact hMb n x hx⟩
  have hL : ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ, ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      |deriv (fun y => -(Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) y)) x| ≤ L := by
    refine ⟨4 * Work.FTS.Regularity.pExp α / (1 + z / 2) ^ 3
      + 6 * (Real.pi / 2) * Cw / (z / 2) ^ 2, by positivity, ?_⟩
    intro n x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have hd1 : HasDerivAt (fun s : ℝ => Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s)
        ((Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x)
          / x ^ 2) x := L12dens_hasDerivAt hCw (h4 n) (hbd n) hx0
    have hdF := hasDerivAt_Fstar_dens (β := Work.FTS.Regularity.pExp α) hx0
    have hsum : HasDerivAt (fun s : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2
        + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s)
        (-(4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3)
          + (Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x)
            / x ^ 2) x := hdF.add hd1
    have hsum' : HasDerivAt (fun y => Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) y)
        (-(4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3)
          + (Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x)
            / x ^ 2) x :=
      hsum.congr_of_eventuallyEq (by
        filter_upwards [isOpen_Ioi.mem_nhds hx0] with s hs
        show Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (gn n) τ) s
          = 2 * Work.FTS.Regularity.pExp α / (1 + s) ^ 2
            + Work.FM.L12dens Work.Spaces.K (slice (gn n) τ) s
        exact hsplit n hs)
    have hval : deriv (fun y => -(Work.FM.L12dens Work.Spaces.K (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) y)) x
        = -(-(4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3)
          + (Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x)
            / x ^ 2) := hsum'.neg.deriv
    rw [hval, abs_neg]
    have hQ1 : |Work.Elliptic.Qang (slice (gn n) τ) 1 x| ≤ 3 * (Real.pi / 2) * Cw := by
      have h := Qang_le hCw (h4 n) (hbd n) (k := 1) (by norm_num) hx0
      have h3 : SW x ≤ 1 := SW_le_one hx0
      have h5 : Cw * SW x ≤ Cw * 1 := mul_le_mul_of_nonneg_left h3 hCw
      have h6 : 3 * (Real.pi / 2) * (Cw * SW x) ≤ 3 * (Real.pi / 2) * Cw := by
        have := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ 3 * (Real.pi / 2))
        simpa using this
      linarith [h, h6]
    have hQ0 : |Work.Elliptic.Qang (slice (gn n) τ) 0 x| ≤ 3 * (Real.pi / 2) * Cw := by
      have h := Qang_le hCw (h4 n) (hbd n) (k := 0) (by norm_num) hx0
      have h3 : SW x ≤ 1 := SW_le_one hx0
      have h5 : Cw * SW x ≤ Cw * 1 := mul_le_mul_of_nonneg_left h3 hCw
      have h6 : 3 * (Real.pi / 2) * (Cw * SW x) ≤ 3 * (Real.pi / 2) * Cw := by
        have := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ 3 * (Real.pi / 2))
        simpa using this
      linarith [h, h6]
    have hnum : |(Work.Elliptic.Qang (slice (gn n) τ) 1 x
        - Work.Elliptic.Qang (slice (gn n) τ) 0 x) / x ^ 2|
        ≤ 6 * (Real.pi / 2) * Cw / (z / 2) ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < x ^ 2)]
      have h2 : |Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x|
          ≤ 6 * (Real.pi / 2) * Cw := by
        calc |Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x|
            = |Work.Elliptic.Qang (slice (gn n) τ) 1 x + -Work.Elliptic.Qang (slice (gn n) τ) 0 x| := by
              ring_nf
          _ ≤ |Work.Elliptic.Qang (slice (gn n) τ) 1 x| + |-Work.Elliptic.Qang (slice (gn n) τ) 0 x| :=
              abs_add_le _ _
          _ = |Work.Elliptic.Qang (slice (gn n) τ) 1 x| + |Work.Elliptic.Qang (slice (gn n) τ) 0 x| := by
              rw [abs_neg]
          _ ≤ 6 * (Real.pi / 2) * Cw := by linarith
      have hxd : (z / 2) ^ 2 ≤ x ^ 2 := by
        have h1 : z / 2 ≤ x := hx.1.le
        have h2y : 0 ≤ z / 2 := by linarith [hz]
        nlinarith
      exact div_le_div₀ (by positivity) h2 (by positivity) hxd
    have hFs4 : |4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3| ≤ 4 * Work.FTS.Regularity.pExp α / (1 + z / 2) ^ 3 := by
      rw [abs_of_nonneg (by positivity)]
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      have h1 : (1 + z / 2) ≤ (1 + x) := by linarith [hx.1]
      exact pow_le_pow_left₀ (by positivity) h1 3
    have hFs4b : 0 ≤ 4 * Work.FTS.Regularity.pExp α := by positivity
    have hFs4c : (0 : ℝ) < (1 + z / 2) ^ 3 := by positivity
    have hFs4d : (1 + z / 2) ^ 3 ≤ (1 + x) ^ 3 := by
      have h1 : (1 + z / 2) ≤ (1 + x) := by linarith [hx.1]
      exact pow_le_pow_left₀ (by positivity) h1 3
    calc |-(4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3)
          + (Work.Elliptic.Qang (slice (gn n) τ) 1 x - Work.Elliptic.Qang (slice (gn n) τ) 0 x)
            / x ^ 2|
        = |-(4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3)
            + ((Work.Elliptic.Qang (slice (gn n) τ) 1 x
              - Work.Elliptic.Qang (slice (gn n) τ) 0 x) / x ^ 2)| := rfl
      _ ≤ |4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3|
          + |(Work.Elliptic.Qang (slice (gn n) τ) 1 x
            - Work.Elliptic.Qang (slice (gn n) τ) 0 x) / x ^ 2| := by
          have h := abs_add_le (-(4 * Work.FTS.Regularity.pExp α / (1 + x) ^ 3))
            ((Work.Elliptic.Qang (slice (gn n) τ) 1 x
              - Work.Elliptic.Qang (slice (gn n) τ) 0 x) / x ^ 2)
          rwa [abs_neg] at h
      _ ≤ 4 * Work.FTS.Regularity.pExp α / (1 + z / 2) ^ 3
          + 6 * (Real.pi / 2) * Cw / (z / 2) ^ 2 := add_le_add hFs4 hnum
  have hu : ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      Filter.Tendsto (fun n => Work.Construction.L12 (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) x) Filter.atTop
        (𝓝 (Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) x)) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have h := L12_tendsto (β := Work.FTS.Regularity.pExp α)
      hβ hβ1 hCw h4 hbd (h := Work.FTS.RegExportIface.RXT.GR α g) hconv hx0
    simpa only [Work.Construction.Ftau, Work.FTS.Galerkin.slice] using h
  have hv : ∀ x ∈ Set.Ioo (z / 2) (2 * z),
      Filter.Tendsto (fun n => -(Work.Construction.L12dens (Work.Construction.Ftau
        (Work.FTS.Regularity.pExp α) (gn n) τ) x)) Filter.atTop
        (𝓝 (-(Work.Construction.L12dens (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.RegExportIface.RXT.GR α g) τ) x))) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1, hz]
    have h := dens_tendsto (β := Work.FTS.Regularity.pExp α) hβ hβ1 hCw h4 hbd
      (h := Work.FTS.RegExportIface.RXT.GR α g) hconv hx0
    exact h.neg
  exact Work.FTS_RegExport.RXR1.hasDerivAt_of_tendsto_deriv (a := z / 2) (b := 2 * z)
    (by linarith) hder hvdiff hM hL hu hv z ⟨by linarith, by linarith⟩

end Work.FTS_RegExport.RXT.Sys.L12FKaux
