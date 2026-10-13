import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.dq2_facts` — the second log-difference quotient (leaf E6b)

For `g : ℝ → ℝ` with `Dg z := z ∂_z g z` differentiable on `[L, ∞)` (`0 < L`), its
logarithmic derivative `D²g z := z ∂_z (Dg) z` bounded by `B` there and `D²g` continuous on
`[L, ∞)`:

* `|(g (e^{2h} z) - 2 g (e^h z) + g z) / h²| ≤ B` for every `h > 0`, `z ≥ L`;
* `(g (e^{2h} z) - 2 g (e^h z) + g z) / h² → D²g z` as `h → 0⁺`, for `z > L`.

## Route

Fix `z` and put `ψ s = g (z e^s)`.  Then `ψ' = Dg ∘ (z e^·)` and `ψ'' = D²g ∘ (z e^·)`, so
the difference considered is the second difference of the one-variable function `ψ`, and the
two conclusions are the two halves of §2 below:

`dq2_secondDiff_sub_le` — the sharp second-difference bound
`|ψ (2h) - 2 ψ h + ψ 0 - d h²| ≤ C h²` whenever `|c - d| ≤ C` on `[0, 2h]`, where `b = ψ'`
and `c = b'`.  The proof is integration by parts free: writing
`ψ (2h) - 2 ψ h + ψ 0 = ∫₀ʰ (b (u + h) - b u) du` (two applications of the fundamental
theorem, the substitution `∫_h^{2h} b = ∫₀ʰ b (· + h)`, and additivity of the interval
integral), the `d`-correction is an integral of the constant `d h` over `[0, h]`, and each
increment `b (u+h) - b u - d h = ∫_u^{u+h} (c - d)` is bounded by `C h` using
`|c - d| ≤ C`.

`dq2_secondDiff_tendsto` — the limit `(ψ (2h) - 2 ψ h + ψ 0)/h² → c 0` as `h → 0⁺`, which
follows from the bound applied with `d := c 0` and `C := ε/2`, the continuity of `c` at `0`
supplying `|c t - c 0| ≤ ε/2` on `[0, 2h]` for small `h`.

The passage from the hypotheses of `Dq2Facts` to those of the two lemmas needs the continuity
of `Dg` on `[L, ∞)`; that is `dq2_Dg_cont` below (mean value theorem: `|∂_z(Dg) u| ≤ B / L`),
the chain rule `dq2_psi_hasDerivAt` / `dq2_b_hasDerivAt`, and the two continuity statements
`dq2_b_cont` / `dq2_c_cont`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## §0 Elementary consequences of the hypotheses -/

/-- The exponential map `s ↦ z e^s` sends the strip `[0,T]` (`T ≥ 0`) into `[L, ∞)` for
`z ≥ L > 0`. -/
private lemma dq2_mapsTo (z L : ℝ) (hL : 0 < L) (hz : L ≤ z) (T : ℝ) :
    Set.MapsTo (fun s : ℝ => z * Real.exp s) (Set.Icc 0 T) (Set.Ici L) := by
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  have hexp : 1 ≤ Real.exp s := Real.one_le_exp hs0
  have hz0 : 0 ≤ z := le_trans (le_of_lt hL) hz
  have hmono : z * 1 ≤ z * Real.exp s := mul_le_mul_of_nonneg_left hexp hz0
  calc L ≤ z := hz
    _ = z * 1 := (mul_one z).symm
    _ ≤ z * Real.exp s := hmono

/-- **`Dg = z ∂_z g` is continuous on `[L, ∞)`**: it is `(B/L)`-Lipschitz there as soon as
`|z ∂_z(Dg) z| ≤ B` on `[L, ∞)`. -/
private lemma dq2_Dg_cont (g : ℝ → ℝ) (L B : ℝ) (hL : 0 < L)
    (hd : ∀ z, L ≤ z → DifferentiableAt ℝ g z ∧
      DifferentiableAt ℝ (fun z' => z' * deriv g z') z)
    (hB : ∀ z, L ≤ z → |z * deriv (fun z' => z' * deriv g z') z| ≤ B) :
    ContinuousOn (fun z => z * deriv g z) (Set.Ici L) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB L le_rfl)
  have hbnd : ∀ x ∈ Set.Ici L, ‖deriv (fun z => z * deriv g z) x‖ ≤ B / L := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hL hx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have h2 : |deriv (fun z => z * deriv g z) x|
        = |x * deriv (fun z' => z' * deriv g z') x| / x := by
      have hthis : deriv (fun z => z * deriv g z) x
          = x * deriv (fun z' => z' * deriv g z') x / x :=
        (mul_div_cancel_left₀ _ hxne).symm
      conv_lhs => rw [hthis]
      rw [abs_div, abs_of_pos hxpos]
    calc ‖deriv (fun z => z * deriv g z) x‖
        = |deriv (fun z => z * deriv g z) x| := by rw [Real.norm_eq_abs]
      _ = |x * deriv (fun z' => z' * deriv g z') x| / x := h2
      _ ≤ B / x := div_le_div_of_nonneg_right (hB x hx) (le_of_lt hxpos)
      _ ≤ B / L := div_le_div_of_nonneg_left hB0 hL hx
  have hlip : ∀ a b : ℝ, L ≤ a → L ≤ b →
      |b * deriv g b - a * deriv g a| ≤ (B / L) * |b - a| := by
    intro a b ha hb
    have hmain := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun z => z * deriv g z) (s := Set.Ici L)
      (fun x hx => (hd x hx).2) hbnd (convex_Ici L) ha hb
    simpa only [Real.norm_eq_abs] using hmain
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  refine ⟨ε / (B / L + 1), by positivity, ?_⟩
  intro y hy hxy
  have hC1 : 0 < B / L + 1 := by positivity
  have h : |y * deriv g y - x * deriv g x| ≤ (B / L + 1) * dist y x := by
    have h1 : |y * deriv g y - x * deriv g x| ≤ (B / L) * |y - x| := hlip x y hx hy
    have h2 : |y - x| = dist y x := (Real.dist_eq y x).symm
    calc |y * deriv g y - x * deriv g x| ≤ (B / L) * |y - x| := h1
      _ = (B / L) * dist y x := by rw [h2]
      _ ≤ (B / L + 1) * dist y x := by nlinarith [dist_nonneg (x := y) (y := x)]
  calc dist (y * deriv g y) (x * deriv g x) = |y * deriv g y - x * deriv g x| :=
        Real.dist_eq _ _
    _ ≤ (B / L + 1) * dist y x := h
    _ < (B / L + 1) * (ε / (B / L + 1)) := mul_lt_mul_of_pos_left hxy hC1
    _ = ε := by field_simp

/-! ## §1 The chain rule for the two composite functions -/

/-- `ψ s = g (z e^s)` has derivative `Dg (z e^s)` for `s ≥ 0`, `z ≥ L`. -/
private lemma dq2_psi_hasDerivAt (g : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hd : ∀ z, L ≤ z → DifferentiableAt ℝ g z ∧
      DifferentiableAt ℝ (fun z' => z' * deriv g z') z)
    {z : ℝ} (hz : L ≤ z) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun s' : ℝ => g (z * Real.exp s'))
      ((z * Real.exp s) * deriv g (z * Real.exp s)) s := by
  have hzL : L ≤ z * Real.exp s := dq2_mapsTo z L hL hz s ⟨hs, le_refl s⟩
  have h1 : HasDerivAt g (deriv g (z * Real.exp s)) (z * Real.exp s) :=
    (hd (z * Real.exp s) hzL).1.hasDerivAt
  have h2 : HasDerivAt (fun s' : ℝ => z * Real.exp s') (z * Real.exp s) s :=
    (Real.hasDerivAt_exp s).const_mul z
  have h3 := h1.comp s h2
  simpa only [Function.comp_def, mul_comm] using h3

/-- `b s = Dg (z e^s)` has derivative `D²g (z e^s)` (i.e. `z e^s ∂_z(Dg) (z e^s)`) for
`s ≥ 0`, `z ≥ L`. -/
private lemma dq2_b_hasDerivAt (g : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hd : ∀ z, L ≤ z → DifferentiableAt ℝ g z ∧
      DifferentiableAt ℝ (fun z' => z' * deriv g z') z)
    {z : ℝ} (hz : L ≤ z) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun s' : ℝ => (z * Real.exp s') * deriv g (z * Real.exp s'))
      ((z * Real.exp s) * deriv (fun z' => z' * deriv g z') (z * Real.exp s)) s := by
  have hzL : L ≤ z * Real.exp s := dq2_mapsTo z L hL hz s ⟨hs, le_refl s⟩
  have h1 : HasDerivAt (fun z' : ℝ => z' * deriv g z')
      (deriv (fun z' : ℝ => z' * deriv g z') (z * Real.exp s)) (z * Real.exp s) :=
    (hd (z * Real.exp s) hzL).2.hasDerivAt
  have h2 : HasDerivAt (fun s' : ℝ => z * Real.exp s') (z * Real.exp s) s :=
    (Real.hasDerivAt_exp s).const_mul z
  have h3 := h1.comp s h2
  simpa only [Function.comp_def, mul_comm] using h3

/-- Continuity of `s ↦ Dg (z e^s)` on `[0,T]`. -/
private lemma dq2_b_cont (g : ℝ → ℝ) (L B : ℝ) (hL : 0 < L)
    (hd : ∀ z, L ≤ z → DifferentiableAt ℝ g z ∧
      DifferentiableAt ℝ (fun z' => z' * deriv g z') z)
    (hB : ∀ z, L ≤ z → |z * deriv (fun z' => z' * deriv g z') z| ≤ B)
    {z : ℝ} (hz : L ≤ z) (T : ℝ) :
    ContinuousOn (fun s : ℝ => (z * Real.exp s) * deriv g (z * Real.exp s)) (Set.Icc 0 T) := by
  have hDg : ContinuousOn (fun z' : ℝ => z' * deriv g z') (Set.Ici L) :=
    dq2_Dg_cont g L B hL hd hB
  have h1 : ContinuousOn (fun s : ℝ => z * Real.exp s) (Set.Icc 0 T) :=
    (continuous_const.mul Real.continuous_exp).continuousOn
  exact hDg.comp h1 (dq2_mapsTo z L hL hz T)

/-- Continuity of `s ↦ D²g (z e^s)` on `[0,T]`. -/
private lemma dq2_c_cont (g : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hc : ContinuousOn (fun z => z * deriv (fun z' => z' * deriv g z') z) (Set.Ici L))
    {z : ℝ} (hz : L ≤ z) (T : ℝ) :
    ContinuousOn
      (fun s : ℝ => (z * Real.exp s) * deriv (fun z' => z' * deriv g z') (z * Real.exp s))
      (Set.Icc 0 T) := by
  have h1 : ContinuousOn (fun s : ℝ => z * Real.exp s) (Set.Icc 0 T) :=
    (continuous_const.mul Real.continuous_exp).continuousOn
  exact hc.comp h1 (dq2_mapsTo z L hL hz T)

/-! ## §2 The two one-variable second-difference lemmas -/

/-- **Second-difference bound.**  If `b = ψ'` and `c = b'` on `[0, 2h]` and `c` is
`C`-close to the constant `d` there, then `ψ (2h) - 2 ψ h + ψ 0` is `C h²`-close to `d h²`.

Proof: `ψ (2h) - 2 ψ h + ψ 0 = ∫₀ʰ (b (u + h) - b u) du`, and each increment is
`∫_u^{u+h} (c - d)` up to the correction `d h`. -/
private lemma dq2_secondDiff_sub_le (ψ b c : ℝ → ℝ) (h C d : ℝ) (hh : 0 < h)
    (hψ : ∀ t ∈ Set.Icc (0:ℝ) (2 * h), HasDerivAt ψ (b t) t)
    (hb : ∀ t ∈ Set.Icc (0:ℝ) (2 * h), HasDerivAt b (c t) t)
    (hbc : ContinuousOn b (Set.Icc (0:ℝ) (2 * h)))
    (hcc : ContinuousOn c (Set.Icc (0:ℝ) (2 * h)))
    (hcd : ∀ t ∈ Set.Icc (0:ℝ) (2 * h), |c t - d| ≤ C) :
    |ψ (2 * h) - 2 * ψ h + ψ 0 - d * h ^ 2| ≤ C * h ^ 2 := by
  have h2h : (0:ℝ) ≤ 2 * h := by linarith
  -- (A) the increments of `b`
  have hincr : ∀ u ∈ Set.Icc (0:ℝ) h, |b (u + h) - b u - d * h| ≤ C * h := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hmemu : ∀ x ∈ Set.uIcc u (u + h), x ∈ Set.Icc (0:ℝ) (2 * h) := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith : u ≤ u + h)] at hx
      exact ⟨le_trans hu1 hx.1, by linarith [hx.2, hu2]⟩
    have hint : IntervalIntegrable c volume u (u + h) :=
      (hcc.mono (fun x hx => hmemu x hx)).intervalIntegrable
    have hftc : (∫ x in u..(u + h), c x) = b (u + h) - b u :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hb x (hmemu x hx)) hint
    have hsub : (∫ x in u..(u + h), (c x - d)) = (b (u + h) - b u) - d * h := by
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hftc,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hbd : ∀ x ∈ Set.uIoc u (u + h), ‖c x - d‖ ≤ C := by
      intro x hx
      rw [Real.norm_eq_abs]
      exact hcd x (hmemu x (Set.uIoc_subset_uIcc hx))
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [Real.norm_eq_abs, hsub, show u + h - u = h by ring, abs_of_pos hh] at hbnd
    simpa using hbnd
  -- (B) the fundamental theorem pieces
  have hbcI : IntervalIntegrable b volume (0:ℝ) (2 * h) :=
    (hbc.mono (fun x hx => by rwa [Set.uIcc_of_le h2h] at hx)).intervalIntegrable
  have hbcIh : IntervalIntegrable b volume (0:ℝ) h :=
    (hbc.mono (fun x hx => by
      rw [Set.uIcc_of_le (le_of_lt hh)] at hx
      exact ⟨hx.1, by linarith [hx.2]⟩)).intervalIntegrable
  have hbch : IntervalIntegrable b volume h (2 * h) :=
    (hbc.mono (fun x hx => by
      rw [Set.uIcc_of_le (by linarith : h ≤ 2 * h)] at hx
      exact ⟨by linarith [hx.1], hx.2⟩)).intervalIntegrable
  have hψ1 : (∫ x in (0:ℝ)..(2 * h), b x) = ψ (2 * h) - ψ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hψ x (by rwa [Set.uIcc_of_le h2h] at hx)) hbcI
  have hψ2 : (∫ x in (0:ℝ)..h, b x) = ψ h - ψ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hψ x (by
        rw [Set.uIcc_of_le (le_of_lt hh)] at hx
        exact ⟨hx.1, by linarith [hx.2]⟩)) hbcIh
  have hsplit : (∫ x in (0:ℝ)..h, b x) + (∫ x in h..(2 * h), b x)
      = ∫ x in (0:ℝ)..(2 * h), b x :=
    intervalIntegral.integral_add_adjacent_intervals hbcIh hbch
  have hcomp : (∫ u in (0:ℝ)..h, b (u + h)) = ∫ x in h..(2 * h), b x := by
    have hh' := intervalIntegral.integral_comp_add_right (f := b) (a := (0:ℝ)) (b := h) (d := h)
    rw [show (0:ℝ) + h = h by ring, show h + h = 2 * h by ring] at hh'
    exact hh'
  have hck : IntervalIntegrable (fun u : ℝ => b (u + h)) volume (0:ℝ) h := by
    have hcont : ContinuousOn (fun u : ℝ => b (u + h)) (Set.uIcc (0:ℝ) h) := by
      rw [Set.uIcc_of_le (le_of_lt hh)]
      exact hbc.comp (continuous_id.add continuous_const).continuousOn
        (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    exact hcont.intervalIntegrable
  have hkey : (∫ u in (0:ℝ)..h, (b (u + h) - b u - d * h))
      = (ψ (2 * h) - 2 * ψ h + ψ 0) - d * h ^ 2 := by
    have e : (∫ x in h..(2 * h), b x) = ψ (2 * h) - ψ h := by
      have h1 : (∫ x in h..(2 * h), b x)
          = (∫ x in (0:ℝ)..(2 * h), b x) - (∫ x in (0:ℝ)..h, b x) := by
        calc (∫ x in h..(2 * h), b x)
            = ((∫ x in (0:ℝ)..h, b x) + (∫ x in h..(2 * h), b x))
                - (∫ x in (0:ℝ)..h, b x) := by ring
          _ = (∫ x in (0:ℝ)..(2 * h), b x) - (∫ x in (0:ℝ)..h, b x) := by rw [hsplit]
      rw [h1, hψ1, hψ2]
      ring
    rw [intervalIntegral.integral_sub (hck.sub hbcIh) intervalIntegrable_const,
      intervalIntegral.integral_sub hck hbcIh, intervalIntegral.integral_const, smul_eq_mul,
      hcomp, hψ2, e]
    ring
  have hbd : ∀ x ∈ Set.uIoc (0:ℝ) h, ‖b (x + h) - b x - d * h‖ ≤ C * h := by
    intro x hx
    rw [Real.norm_eq_abs]
    have hxI : x ∈ Set.Icc (0:ℝ) h := by
      have := Set.uIoc_subset_uIcc hx
      rwa [Set.uIcc_of_le (le_of_lt hh)] at this
    exact hincr x hxI
  calc |ψ (2 * h) - 2 * ψ h + ψ 0 - d * h ^ 2|
      = ‖∫ u in (0:ℝ)..h, (b (u + h) - b u - d * h)‖ := by rw [Real.norm_eq_abs, hkey]
    _ ≤ (C * h) * |h - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = C * h ^ 2 := by rw [sub_zero, abs_of_pos hh]; ring

/-- **Second-difference limit.**  If `b = ψ'` and `c = b'` on `[0,2]` with `c` continuous
there, then `(ψ (2h) - 2 ψ h + ψ 0)/h² → c 0` as `h → 0⁺`. -/
private lemma dq2_secondDiff_tendsto (ψ b c : ℝ → ℝ)
    (hψ : ∀ t ∈ Set.Icc (0:ℝ) 2, HasDerivAt ψ (b t) t)
    (hb : ∀ t ∈ Set.Icc (0:ℝ) 2, HasDerivAt b (c t) t)
    (hbc : ContinuousOn b (Set.Icc (0:ℝ) 2))
    (hcc : ContinuousOn c (Set.Icc (0:ℝ) 2)) :
    Filter.Tendsto (fun h => (ψ (2 * h) - 2 * ψ h + ψ 0) / h ^ 2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (c 0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 2 := ⟨le_rfl, by norm_num⟩
  have hcont : ContinuousWithinAt c (Set.Icc (0:ℝ) 2) 0 := hcc 0 h0
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ1, hδ1pos, hδ1⟩ := hcont (ε / 2) (by linarith)
  refine ⟨min 1 (δ1 / 2), lt_min one_pos (by linarith), ?_⟩
  intro h hh hdist
  have hdist' : h < min 1 (δ1 / 2) := by
    rwa [Real.dist_eq, sub_zero, abs_of_pos hh] at hdist
  have hh1 : h < 1 := lt_of_lt_of_le hdist' (min_le_left _ _)
  have hhδ : h < δ1 / 2 := lt_of_lt_of_le hdist' (min_le_right _ _)
  have hhpos : 0 < h := hh
  have hsub : ∀ t ∈ Set.Icc (0:ℝ) (2 * h), t ∈ Set.Icc (0:ℝ) 2 := fun t ht =>
    ⟨ht.1, by linarith [ht.2]⟩
  have hbd : ∀ t ∈ Set.Icc (0:ℝ) (2 * h), |c t - c 0| ≤ ε / 2 := by
    intro t ht
    have ht2 : dist t 0 < δ1 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsub t ht).1]
      linarith [ht.2, hhδ]
    have hlt : |c t - c 0| < ε / 2 := by
      have := hδ1 (hsub t ht) ht2
      rwa [Real.dist_eq] at this
    exact le_of_lt hlt
  have hkey := dq2_secondDiff_sub_le ψ b c h (ε / 2) (c 0) hhpos
    (fun t ht => hψ t (hsub t ht)) (fun t ht => hb t (hsub t ht))
    (hbc.mono (fun t ht => hsub t ht)) (hcc.mono (fun t ht => hsub t ht)) hbd
  rw [show dist ((ψ (2 * h) - 2 * ψ h + ψ 0) / h ^ 2) (c 0)
        = |(ψ (2 * h) - 2 * ψ h + ψ 0) / h ^ 2 - c 0| from Real.dist_eq _ _]
  have hfac : |(ψ (2 * h) - 2 * ψ h + ψ 0) / h ^ 2 - c 0|
      = |ψ (2 * h) - 2 * ψ h + ψ 0 - c 0 * h ^ 2| / h ^ 2 := by
    have hA : (ψ (2 * h) - 2 * ψ h + ψ 0) / h ^ 2 - c 0
        = (ψ (2 * h) - 2 * ψ h + ψ 0 - c 0 * h ^ 2) / h ^ 2 := by
      field_simp
    rw [hA, abs_div, abs_of_pos (pow_pos hhpos 2)]
  rw [hfac]
  have hpos : 0 < h ^ 2 := pow_pos hhpos 2
  calc |ψ (2 * h) - 2 * ψ h + ψ 0 - c 0 * h ^ 2| / h ^ 2
      ≤ (ε / 2 * h ^ 2) / h ^ 2 := div_le_div_of_nonneg_right hkey (le_of_lt hpos)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-! ## §3 The leaf `E6b` -/

theorem dq2_facts (g : ℝ → ℝ) (L B : ℝ) :
    Work.FTS_StreamBdry.SB25.Dq2Facts g L B := by
  unfold Work.FTS_StreamBdry.SB25.Dq2Facts
  intro hL hd hc hB
  constructor
  · -- the bound, from `dq2_secondDiff_sub_le` with `d = 0`, `C = B`
    intro h hh z hz
    have hbound := dq2_secondDiff_sub_le
      (fun s : ℝ => g (z * Real.exp s))
      (fun s : ℝ => (z * Real.exp s) * deriv g (z * Real.exp s))
      (fun s : ℝ => (z * Real.exp s) * deriv (fun z' => z' * deriv g z') (z * Real.exp s))
      h B 0 hh
      (fun t ht => dq2_psi_hasDerivAt g L hL hd hz ht.1)
      (fun t ht => dq2_b_hasDerivAt g L hL hd hz ht.1)
      (dq2_b_cont g L B hL hd hB hz (2 * h))
      (dq2_c_cont g L hL hc hz (2 * h))
      (fun t ht => by
        rw [sub_zero]
        exact hB (z * Real.exp t) (dq2_mapsTo z L hL hz (2 * h) ht))
    have hS : |g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z| ≤ B * h ^ 2 := by
      simp only [Real.exp_zero, mul_one, zero_mul, sub_zero] at hbound
      rw [mul_comm z (Real.exp (2 * h)), mul_comm z (Real.exp h)] at hbound
      exact hbound
    have hdiv : |(g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z) / h ^ 2|
        = |g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z| / h ^ 2 := by
      rw [abs_div, abs_of_pos (pow_pos hh 2)]
    rw [hdiv]
    calc |g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z| / h ^ 2
        ≤ (B * h ^ 2) / h ^ 2 := div_le_div_of_nonneg_right hS (le_of_lt (pow_pos hh 2))
      _ = B := by field_simp
  · -- the limit, from `dq2_secondDiff_tendsto`
    intro z hz
    have hz' : L ≤ z := le_of_lt hz
    have htend := dq2_secondDiff_tendsto
      (fun s : ℝ => g (z * Real.exp s))
      (fun s : ℝ => (z * Real.exp s) * deriv g (z * Real.exp s))
      (fun s : ℝ => (z * Real.exp s) * deriv (fun z' => z' * deriv g z') (z * Real.exp s))
      (fun t ht => dq2_psi_hasDerivAt g L hL hd hz' ht.1)
      (fun t ht => dq2_b_hasDerivAt g L hL hd hz' ht.1)
      (dq2_b_cont g L B hL hd hB hz' 2)
      (dq2_c_cont g L hL hc hz' 2)
    have htend' : Filter.Tendsto
        (fun h : ℝ => (g (z * Real.exp (2 * h)) - 2 * g (z * Real.exp h) + g z) / h ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (z * deriv (fun z' => z' * deriv g z') z)) := by
      simpa only [Real.exp_zero, mul_one] using htend
    rw [show (fun h : ℝ => (g (z * Real.exp (2 * h)) - 2 * g (z * Real.exp h) + g z) / h ^ 2)
        = (fun h : ℝ => (g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z) / h ^ 2)
        from by
          funext h
          rw [mul_comm z (Real.exp (2 * h)), mul_comm z (Real.exp h)]] at htend'
    exact htend'

end Work.FTS_StreamBdry.SB25
