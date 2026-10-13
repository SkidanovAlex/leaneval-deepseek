/-
# `𝒲^{4,∞}`-bound for the singular radial piece `Ḡ` of Elgindi's §Elliptic

Target (as requested): `Work.FTS.H2.PhiStarE.Gbar_wiln`, i.e.

`∃ C > 0, ∀ α ∈ (0,1],  WlInfMem α 4 (fun z θ => Gbar α (Fstar α) z) ∧
    WlInf α 4 (fun z θ => Gbar α (Fstar α) z) ≤ C * α`.

The function is independent of `θ`, so all angular terms of `WlInf` vanish and the
statement is the *one-variable* estimate

`|(1+z)^k ∂_z^k Ḡ(z)| ≤ C α`  for `0 ≤ z < ∞`, `k ≤ 4`,

where (with `N = 5/α ≥ 5`, `F_*(z) = 2z/(1+z)²`)

`Ḡ(z) = -(3/(4α)) z^{-N} ∫_0^z s^{(5-α)/α} (F_*)_*(s) ds
      = -(1/2) z^{-N} ∫_0^z s^N (1+s)^{-2} ds   (z ≥ 0)`.

The point of the estimate is a *cancellation*: the naive term-by-term bound of the
derivatives of `z^{-N} J(z)` produces factors `N^k` while the true size is `O(1/N)`.
The clean way to see it (and the one formalised here) is the change of variables
`s = z t`, which writes

`Ḡ(z) = -(1/2) · z · At N 0 z`,  `At N j z = ∫_0^1 t^{N+j} (1+zt)^{-(j+2)} dt`,

and then `(d/dz) At N j z = -(j+2) At N (j+1) z` (differentiation under the integral
sign), so that with `Pi N z = z · At N 0 z`,

`Pi^{(k)} z = (-1)^{k-1} k·k! At N (k-1) z + (-1)^k (k+1)! z At N k z`,

and every term is bounded by `O(1/N)` because `z^c At N j z = O(1/N)` for `c ≤ j+1`
(the exponent budget `c ≤ j+1` matches exactly what the Leibniz expansion produces).

The one subtlety is the endpoint `z = 0`, where `deriv`-iterates of `Ḡ` are *junk*: `deriv`
returns `0` at a point where the function is not differentiable, and `Ḡ` has a genuine
corner at `0` (the `rpow` of the negative base is governed by
`Real.rpow_def_of_nonpos`, which involves `cos(-Nπ)`, so the left branch is
`z ↦ c_N·(1/2)(-z)At N 0 (-z)` rather than a smooth continuation of the right one).
The argument used here avoids evaluating the corner: since `Ḡ` agrees with the smooth model
`Dk N 0 z = -(1/2)·z·At N 0 z` on all of `(0,∞)`, its `deriv`-iterates agree there too, and
`deriv_iter_value` shows that at `0` each iterate is either the junk value `0` or the model
value `Dk N k 0` — and both are dominated by the weighted bound `Dk_bound`
(`(1+z)^k·|Dk N k z| ≤ 3456/N` for `N ≥ 5`, all `z ≥ 0`, `k ≤ 4`).  No left-hand behaviour
of `Ḡ` is needed.

Assembly: `WlInf_radial` reduces `WlInf α 4` of a radial function to the sum of the five
radial sup-norms (the angular part of `WlInf` vanishes identically), each of which is
`≤ 3456α` by `gbar_iter_bound`; the constant `20000` absorbs the `5`-fold sum.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.H2.PhiStarE.GbarDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FM.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.PhiStarE

set_option autoImplicit false

/-! ## Reduction of `Elliptic.Fstar (Construction.Fstar α)` -/

theorem EllFstar_Fstar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Elliptic.Fstar (Work.Construction.Fstar α)
      = fun z => α * Work.FM.Fstar z / 3 := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  funext z
  rw [Work.Elliptic.Fstar]
  have hpoint : ∀ θ : ℝ,
      Work.Construction.Fstar α z θ * Work.Elliptic.sinCos2 θ
        = (α * Work.FM.Fstar z / (3 * Work.Spaces.c α))
            * (Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    intro θ
    simp only [Work.Construction.Fstar, Work.Elliptic.sinCos2, Work.Spaces.K]
    ring
  rw [setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
        (fun θ _ => hpoint θ)]
  rw [integral_const_mul]
  have hcint : (∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ)
      = Work.Spaces.c α := rfl
  rw [hcint]
  field_simp

/-! ## Differentiation of the basic family -/

/-- The `x`-derivative of the integrand of `At`:
`d/dx [t^a/(1+xt)^m] = -m·t^{a+1}/(1+xt)^{m+1}`. -/
theorem hasDerivAt_div_pow_exp (a : ℝ) (m : ℕ) (hm : 1 ≤ m) {t x : ℝ} (ht : 0 ≤ t)
    (ha : 0 ≤ a) (hx : 0 < 1 + x * t) :
    HasDerivAt (fun x : ℝ => t ^ a / (1 + x * t) ^ m)
      (-(m : ℝ) * (t ^ (a + 1) / (1 + x * t) ^ (m + 1))) x := by
  have hD : (1 + x * t) ≠ 0 := ne_of_gt hx
  have hden : HasDerivAt (fun x : ℝ => (1 + x * t) ^ m)
      ((m : ℝ) * (1 + x * t) ^ (m - 1) * t) x := by
    have h1 : HasDerivAt (fun x : ℝ => 1 + x * t) t x := by
      simpa using ((hasDerivAt_id x).mul_const t).const_add 1
    convert h1.pow m using 1
  have hnum : HasDerivAt (fun _ : ℝ => t ^ a) 0 x := hasDerivAt_const x _
  have h := hnum.div hden (pow_ne_zero m hD)
  have htp : t ^ a * t = t ^ (a + 1) := by
    rcases lt_or_eq_of_le ht with h0 | h0
    · rw [Real.rpow_add h0, Real.rpow_one]
    · subst h0
      rcases lt_or_eq_of_le ha with ha0 | ha0
      · rw [Real.zero_rpow (ne_of_gt ha0), Real.zero_rpow (by linarith : (a + 1) ≠ 0)]
        ring
      · subst ha0
        simp only [Real.rpow_zero, zero_add, Real.rpow_one]
        ring
  have hgen : ∀ (D T : ℝ), D ≠ 0 →
      (0 * D ^ m - T * ((m : ℝ) * D ^ (m - 1) * t)) / (D ^ m) ^ 2
        = -((m : ℝ) * (T * t / D ^ (m + 1))) := by
    intro D T _
    have key : D * D ^ m * D ^ (m - 1) = D ^ (m * 2) := by
      nth_rewrite 1 [show D = D ^ 1 from (pow_one D).symm]
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    field_simp
    ring_nf
    rw [key]
  have hv := hgen (1 + x * t) (t ^ a) hD
  rw [htp] at hv
  rw [hv] at h
  convert h using 1
  · ring

/-- `At N j` is differentiable on `z ≥ 0`, with `(At N j)' = -(j+2)·At N (j+1)`
(differentiation under the integral sign; the factor `1 + zt ≥ 1` keeps the
denominator away from zero). -/
theorem At_hasDerivAt (N : ℝ) (hN : 0 ≤ N) (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (At N j) (-((j : ℝ) + 2) * At N (j + 1) z) z := by
  have hS : Set.Ioi (-1/2 : ℝ) ∈ 𝓝 z :=
    isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith)
  have hzS : z ∈ Set.Ioi (-1/2 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hpos : ∀ x ∈ Set.Ioi (-1/2 : ℝ), ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < 1 + x * t := by
    intro x hx t ht
    simp only [Set.mem_Ioi] at hx
    nlinarith [ht.1, ht.2]
  have hcont : ∀ x ∈ Set.Ioi (-1/2 : ℝ),
      ContinuousOn (fun t : ℝ => t ^ (N + (j:ℝ)) / (1 + x * t) ^ (j + 2)) (Set.uIcc 0 1) := by
    intro x hx
    have hden : Continuous (fun t : ℝ => (1 + x * t) ^ (j + 2)) :=
      (continuous_const.add (continuous_const.mul continuous_id)).pow _
    have hnum : Continuous (fun t : ℝ => t ^ (N + (j:ℝ))) :=
      continuous_iff_continuousAt.mpr fun t =>
        Real.continuousAt_rpow_const t _ (Or.inr (by positivity))
    refine ContinuousOn.div hnum.continuousOn hden.continuousOn ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have := hpos x hx t ⟨ht.1, ht.2⟩
    positivity
  have hcont' : ∀ x ∈ Set.Ioi (-1/2 : ℝ),
      ContinuousOn (fun t : ℝ => t ^ (N + (j:ℝ) + 1) / (1 + x * t) ^ (j + 3))
        (Set.uIcc 0 1) := by
    intro x hx
    have hden : Continuous (fun t : ℝ => (1 + x * t) ^ (j + 3)) :=
      (continuous_const.add (continuous_const.mul continuous_id)).pow _
    have hnum : Continuous (fun t : ℝ => t ^ (N + (j:ℝ) + 1)) :=
      continuous_iff_continuousAt.mpr fun t =>
        Real.continuousAt_rpow_const t _ (Or.inr (by positivity))
    refine ContinuousOn.div hnum.continuousOn hden.continuousOn ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have := hpos x hx t ⟨ht.1, ht.2⟩
    positivity
  have hdiff : ∀ t ∈ Set.uIoc (0:ℝ) 1, ∀ x ∈ Set.Ioi (-1/2 : ℝ),
      HasDerivAt (fun x : ℝ => t ^ (N + (j:ℝ)) / (1 + x * t) ^ (j + 2))
        (-((j:ℝ)+2) * (t ^ (N + (j:ℝ) + 1) / (1 + x * t) ^ (j + 3))) x := by
    intro t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have hx' : 0 < 1 + x * t := hpos x hx t ⟨le_of_lt ht.1, ht.2⟩
    convert hasDerivAt_div_pow_exp (N + (j:ℝ)) (j+2) (by omega) (le_of_lt ht.1)
      (by positivity) hx' using 1
    push_cast
    ring
  have hbd : ∀ t ∈ Set.uIoc (0:ℝ) 1, ∀ x ∈ Set.Ioi (-1/2 : ℝ),
      ‖-((j:ℝ)+2) * (t ^ (N + (j:ℝ) + 1) / (1 + x * t) ^ (j + 3))‖
        ≤ ((j:ℝ)+2) * (2:ℝ)^(j+3) := by
    intro t ht x hx
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    simp only [Set.mem_Ioi] at hx
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hx' : 0 < 1 + x * t := by nlinarith
    have h1 : t ^ (N + (j:ℝ) + 1) ≤ 1 :=
      Real.rpow_le_one (le_of_lt ht0) ht1 (by positivity)
    have h2 : (1 : ℝ) / (1 + x * t) ^ (j + 3) ≤ (2:ℝ)^(j+3) := by
      rw [div_le_iff₀ (by positivity), ← mul_pow]
      exact one_le_pow₀ (by nlinarith)
    rw [norm_mul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ)+2)]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht0) _),
      abs_of_pos (by positivity : (0:ℝ) < (1 + x * t)^(j+3))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc t ^ (N + (j:ℝ) + 1) / (1 + x * t) ^ (j + 3)
        = t ^ (N + (j:ℝ) + 1) * (1 / (1 + x * t) ^ (j + 3)) := by ring
      _ ≤ 1 * (2:ℝ)^(j+3) := mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ = (2:ℝ)^(j+3) := by ring
  have hAt : At N (j+1) z
      = ∫ t in (0:ℝ)..1, t ^ (N + (j:ℝ) + 1) / (1 + z * t) ^ (j + 3) := by
    rw [At_def]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have h1 : N + ((j+1 : ℕ) : ℝ) = N + (j:ℝ) + 1 := by push_cast; ring
    have h2 : (j+1) + 2 = j + 3 := by omega
    rw [h1, h2]
  have hval : (∫ t in (0:ℝ)..1,
        -((j:ℝ)+2) * (t ^ (N + (j:ℝ) + 1) / (1 + z * t) ^ (j + 3)))
      = -((j:ℝ)+2) * At N (j+1) z := by
    rw [intervalIntegral.integral_const_mul, ← hAt]
  have hFmeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun t : ℝ => t ^ (N + (j:ℝ)) / (1 + x * t) ^ (j + 2))
        (volume.restrict (Set.uIoc (0:ℝ) 1)) := by
    filter_upwards [hS] with x hx
    exact ((hcont x hx).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hF'meas : AEStronglyMeasurable
      (fun t : ℝ => -((j:ℝ)+2) * (t ^ (N + (j:ℝ) + 1) / (1 + z * t) ^ (j + 3)))
        (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    (((hcont' z hzS).const_mul (-((j:ℝ)+2))).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  have key := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (𝕜 := ℝ)
    (F := fun x t => t ^ (N + (j:ℝ)) / (1 + x * t) ^ (j + 2))
    (F' := fun x t => -((j:ℝ)+2) * (t ^ (N + (j:ℝ) + 1) / (1 + x * t) ^ (j + 3)))
    (bound := fun _ : ℝ => ((j:ℝ)+2) * (2:ℝ)^(j+3))
    (x₀ := z) (a := 0) (b := 1) (s := Set.Ioi (-1/2 : ℝ))
    hS hFmeas ((hcont z hzS).intervalIntegrable) hF'meas
    (Filter.Eventually.of_forall hbd) intervalIntegrable_const
    (Filter.Eventually.of_forall hdiff)).2
  rw [hval] at key
  exact key

/-- `t ↦ t^a` is continuous for `a ≥ 0`. -/
theorem continuous_rpow_const_nonneg {a : ℝ} (ha : 0 ≤ a) :
    Continuous (fun t : ℝ => t ^ a) :=
  continuous_iff_continuousAt.mpr fun t => Real.continuousAt_rpow_const t a (Or.inr ha)

/-- The change of variables `s = z·t` in the basic integral:
`∫_0^z s^{N+j}(1+s)^{-(j+2)} ds = z^{N+j+1} · At N j z` for `z > 0`. -/
theorem At_subst (N : ℝ) (j : ℕ) {z : ℝ} (hz : 0 < z) :
    ∫ s in (0:ℝ)..z, s ^ (N + (j:ℝ)) / (1 + s) ^ (j + 2)
      = z ^ (N + (j:ℝ) + 1) * At N j z := by
  have hkey := intervalIntegral.mul_integral_comp_mul_left (a := (0:ℝ)) (b := (1:ℝ))
    (f := fun s : ℝ => s ^ (N + (j:ℝ)) / (1 + s) ^ (j + 2)) z
  simp only [mul_zero, mul_one] at hkey
  rw [← hkey]
  rw [At_def]
  have hpt : Set.EqOn (fun t : ℝ => (z * t) ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2))
      (fun t : ℝ => z ^ (N + (j:ℝ)) * (t ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2)))
      (Set.uIcc (0:ℝ) 1) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    dsimp only
    rw [Real.mul_rpow (le_of_lt hz) ht.1]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
  have hzpow : z ^ (N + (j:ℝ) + 1) = z ^ (N + (j:ℝ)) * z := by
    rw [show N + (j:ℝ) + 1 = (N + (j:ℝ)) + 1 from rfl, Real.rpow_add hz, Real.rpow_one]
  rw [hzpow]
  ring

/-- The basic bound `|z^c · At N j z| ≤ 2/N` for `N ≥ 2` and `0 ≤ c ≤ j+1`.  The
exponent budget `c ≤ j+1` is exactly what the Leibniz expansion of `(1+z)^k Pi^{(k)} z`
produces. -/
theorem At_bound (N : ℝ) (hN : 2 ≤ N) (j c : ℕ) (hc : c ≤ j + 1) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ c * At N j z| ≤ 2 / N := by
  have hNpos : (0:ℝ) < N := by linarith
  have hNj : (0:ℝ) < N + (j:ℝ) := by linarith [show (0:ℝ) ≤ (j:ℝ) from Nat.cast_nonneg j]
  have hexp0 : (0:ℝ) ≤ N + (j:ℝ) := le_of_lt hNj
  have hzpow : (0:ℝ) ≤ z ^ c := pow_nonneg hz c
  have hA0 : 0 ≤ At N j z := by
    rw [At_def]
    refine intervalIntegral.integral_nonneg (by norm_num) fun t ht => ?_
    exact div_nonneg (Real.rpow_nonneg ht.1 _)
      (pow_nonneg (by linarith [mul_nonneg hz ht.1]) _)
  rw [abs_of_nonneg (mul_nonneg hzpow hA0)]
  have hcont1 : ContinuousOn (fun t : ℝ => t ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2))
      (Set.uIcc 0 1) :=
    ContinuousOn.div (continuous_rpow_const_nonneg hexp0).continuousOn
      ((continuous_const.add (continuous_const.mul continuous_id)).pow _).continuousOn
      (fun t ht => by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
        exact pow_ne_zero _ (ne_of_gt (by linarith [mul_nonneg hz ht.1])))
  have hintegrable1 : IntervalIntegrable
      (fun t : ℝ => t ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2)) volume 0 1 :=
    hcont1.intervalIntegrable
  have hintegrable2 : IntervalIntegrable (fun t : ℝ => t ^ (N + (j:ℝ))) volume 0 1 :=
    (continuous_rpow_const_nonneg hexp0).intervalIntegrable 0 1
  have hintegrable3 : IntervalIntegrable (fun t : ℝ => t ^ (N - 2)) volume 0 1 :=
    (continuous_rpow_const_nonneg (by linarith : (0:ℝ) ≤ N - 2)).intervalIntegrable 0 1
  have hfin : 1 / (N - 1) ≤ 2 / N := by
    have h1 : (0:ℝ) < N - 1 := by linarith
    rw [div_le_iff₀ h1, show (2:ℝ) / N * (N - 1) = 2 * (N - 1) / N from by ring,
      le_div_iff₀ hNpos]
    linarith
  rcases le_or_gt z 1 with hz1 | hz1
  · have h1 : z ^ c ≤ 1 := pow_le_one₀ hz hz1
    have h2 : At N j z ≤ 1 / N := by
      have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
          t ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2) ≤ t ^ (N + (j:ℝ)) := by
        intro t ht
        rw [div_le_iff₀ (pow_pos (by linarith [mul_nonneg hz ht.1]) _)]
        have h3 : (1:ℝ) ≤ (1 + z * t) ^ (j + 2) :=
          one_le_pow₀ (by linarith [mul_nonneg hz ht.1])
        nlinarith [Real.rpow_nonneg ht.1 (N + (j:ℝ))]
      rw [At_def]
      have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
        hintegrable1 hintegrable2 hpt
      have hval : (∫ t in (0:ℝ)..1, t ^ (N + (j:ℝ))) = 1 / (N + (j:ℝ) + 1) := by
        rw [integral_rpow (Or.inl (by linarith))]
        rw [Real.one_rpow,
          Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < N + (j:ℝ) + 1))]
        simp only [sub_zero]
      rw [hval] at hmono
      have hle : 1 / (N + (j:ℝ) + 1) ≤ 1 / N := by
        apply one_div_le_one_div_of_le hNpos
        linarith [show (0:ℝ) ≤ (j:ℝ) from Nat.cast_nonneg j]
      linarith
    calc z ^ c * At N j z ≤ 1 * At N j z := mul_le_mul_of_nonneg_right h1 hA0
      _ = At N j z := one_mul _
      _ ≤ 1 / N := h2
      _ ≤ 2 / N := div_le_div_of_nonneg_right (by norm_num) (le_of_lt hNpos)
  · have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
        z ^ c * (t ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2)) ≤ t ^ (N - 2) := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · subst h0
        rw [Real.zero_rpow (ne_of_gt hNj), zero_div, mul_zero]
        exact Real.rpow_nonneg le_rfl _
      · have hc2 : c ≤ j + 2 := by omega
        have hmain : z ^ c * t ^ (j + 2) ≤ (1 + z * t) ^ (j + 2) := by
          have h1 : z ^ c ≤ z ^ (j + 2) := pow_le_pow_right₀ (le_of_lt hz1) hc2
          have h2 : z ^ c * t ^ (j + 2) ≤ z ^ (j + 2) * t ^ (j + 2) :=
            mul_le_mul_of_nonneg_right h1 (pow_nonneg (le_of_lt h0) _)
          rw [← mul_pow] at h2
          exact h2.trans (pow_le_pow_left₀ (mul_nonneg hz (le_of_lt h0))
            (by linarith [mul_nonneg hz (le_of_lt h0)]) _)
        have hp : t ^ (N + (j:ℝ)) = t ^ (N - 2) * t ^ (j + 2) := by
          rw [show N + (j:ℝ) = (N - 2) + ((j + 2 : ℕ) : ℝ) from by push_cast; ring]
          rw [Real.rpow_add h0, Real.rpow_natCast]
        rw [hp]
        calc z ^ c * (t ^ (N - 2) * t ^ (j + 2) / (1 + z * t) ^ (j + 2))
            = t ^ (N - 2) * (z ^ c * t ^ (j + 2) / (1 + z * t) ^ (j + 2)) := by ring
          _ ≤ t ^ (N - 2) * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.rpow_pos_of_pos h0 _))
              rw [div_le_one (pow_pos (by linarith [mul_nonneg hz (le_of_lt h0)]) _)]
              exact hmain
          _ = t ^ (N - 2) := mul_one _
    have hIntLHS : IntervalIntegrable
        (fun t : ℝ => z ^ c * (t ^ (N + (j:ℝ)) / (1 + z * t) ^ (j + 2))) volume 0 1 :=
      hintegrable1.const_mul _
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      hIntLHS hintegrable3 hpt
    have hval : (∫ t in (0:ℝ)..1, t ^ (N - 2)) = 1 / (N - 1) := by
      rw [integral_rpow (Or.inl (by linarith))]
      rw [Real.one_rpow,
        Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < N - 2 + 1))]
      simp only [sub_zero]
      congr 1
      ring
    rw [hval] at hmono
    rw [At_def, ← intervalIntegral.integral_const_mul]
    exact hmono.trans hfin

/-! ## The left branch `PhiL` and its derivatives -/

/-- The first three derivatives of `PhiL z = -(1/2)∫_0^z t/(1+t)^2 dt` on `(-1,∞)`. -/
theorem PhiL_derivs {z : ℝ} (hz : -1 < z) :
    HasDerivAt PhiL (-(1 / 2) * (z / (1 + z) ^ 2)) z ∧
      HasDerivAt (deriv PhiL) (-(1 / 2) * ((1 - z) / (1 + z) ^ 3)) z ∧
      HasDerivAt (deriv (deriv PhiL)) (-(1 / 2) * ((2 * z - 4) / (1 + z) ^ 4)) z := by
  have hq : ∀ w : ℝ, -1 < w →
      HasDerivAt (fun u : ℝ => ∫ t in (0:ℝ)..u, t / (1 + t) ^ 2) (w / (1 + w) ^ 2) w := by
    intro w hw
    have hcont : ContinuousOn (fun t : ℝ => t / (1 + t) ^ 2) (Set.uIcc 0 w) := by
      refine ContinuousOn.div continuousOn_id
        ((continuousOn_const.add continuousOn_id).pow 2) (fun t ht => ?_)
      have ht1 : -1 < t := lt_of_lt_of_le (lt_min (by norm_num) hw) ht.1
      exact pow_ne_zero 2 (ne_of_gt (by linarith))
    have hcat : ContinuousAt (fun t : ℝ => t / (1 + t) ^ 2) w := by
      refine ContinuousAt.div continuousAt_id
        ((continuousAt_const.add continuousAt_id).pow 2) ?_
      exact pow_ne_zero 2 (ne_of_gt (by linarith))
    have hmeas : StronglyMeasurableAtFilter (fun t : ℝ => t / (1 + t) ^ 2) (𝓝 w) volume :=
      ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
        (fun x hx => by
          rw [Set.mem_Ioi] at hx
          exact ContinuousAt.div continuousAt_id
            ((continuousAt_const.add continuousAt_id).pow 2)
            (pow_ne_zero 2 (ne_of_gt (by linarith : (0:ℝ) < 1 + x)))) w hw
    exact intervalIntegral.integral_hasDerivAt_right hcont.intervalIntegrable hmeas hcat
  have hF : ∀ w : ℝ, -1 < w → HasDerivAt PhiL (-(1 / 2) * (w / (1 + w) ^ 2)) w := by
    intro w hw
    have h1 := (hq w hw).const_mul (-(1 / 2))
    convert h1 using 1
    funext y
    rfl
  have hg1 : ∀ w : ℝ, -1 < w →
      HasDerivAt (fun u : ℝ => -(1 / 2) * (u / (1 + u) ^ 2))
        (-(1 / 2) * ((1 - w) / (1 + w) ^ 3)) w := by
    intro w hw
    have hne : (1 + w) ≠ 0 := by linarith
    have hden : HasDerivAt (fun u : ℝ => (1 + u) ^ 2) (2 * (1 + w) ^ 1 * 1) w := by
      have h0 := (hasDerivAt_id w).const_add 1
      convert h0.pow 2 using 1
      · funext u; simp
      · simp
    have hq' : HasDerivAt (fun u : ℝ => u / (1 + u) ^ 2)
        ((1 * (1 + w) ^ 2 - w * (2 * (1 + w) ^ 1 * 1)) / ((1 + w) ^ 2) ^ 2) w :=
      (hasDerivAt_id w).div hden (pow_ne_zero 2 hne)
    have hval : (1 * (1 + w) ^ 2 - w * (2 * (1 + w) ^ 1 * 1)) / ((1 + w) ^ 2) ^ 2
        = (1 - w) / (1 + w) ^ 3 := by
      field_simp
      ring
    rw [hval] at hq'
    exact hq'.const_mul (-(1 / 2))
  have hg2 : ∀ w : ℝ, -1 < w →
      HasDerivAt (fun u : ℝ => -(1 / 2) * ((1 - u) / (1 + u) ^ 3))
        (-(1 / 2) * ((2 * w - 4) / (1 + w) ^ 4)) w := by
    intro w hw
    have hne : (1 + w) ≠ 0 := by linarith
    have hnum : HasDerivAt (fun u : ℝ => 1 - u) (-1) w := by
      simpa using (hasDerivAt_id w).const_sub 1
    have hden : HasDerivAt (fun u : ℝ => (1 + u) ^ 3) (3 * (1 + w) ^ 2 * 1) w := by
      have h0 := (hasDerivAt_id w).const_add 1
      convert h0.pow 3 using 1
      · funext u; simp
      · simp
    have hq' : HasDerivAt (fun u : ℝ => (1 - u) / (1 + u) ^ 3)
        ((-1 * (1 + w) ^ 3 - (1 - w) * (3 * (1 + w) ^ 2 * 1)) / ((1 + w) ^ 3) ^ 2) w :=
      hnum.div hden (pow_ne_zero 3 hne)
    have hval : (-1 * (1 + w) ^ 3 - (1 - w) * (3 * (1 + w) ^ 2 * 1)) / ((1 + w) ^ 3) ^ 2
        = (2 * w - 4) / (1 + w) ^ 4 := by
      field_simp
      ring
    rw [hval] at hq'
    exact hq'.const_mul (-(1 / 2))
  refine ⟨hF z hz, ?_, ?_⟩
  · have hev : deriv PhiL =ᶠ[𝓝 z] fun w : ℝ => -(1 / 2) * (w / (1 + w) ^ 2) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact (hF w hw).deriv
    exact (hg1 z hz).congr_of_eventuallyEq hev
  · have hev2 : deriv (deriv PhiL) =ᶠ[𝓝 z] fun w : ℝ => -(1 / 2) * ((1 - w) / (1 + w) ^ 3) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      have hevw : deriv PhiL =ᶠ[𝓝 w] fun v : ℝ => -(1 / 2) * (v / (1 + v) ^ 2) := by
        filter_upwards [isOpen_Ioi.mem_nhds hw] with v hv
        exact (hF v hv).deriv
      rw [hevw.deriv_eq, (hg1 w hw).deriv]
    exact (hg2 z hz).congr_of_eventuallyEq hev2

/-! ## The reduction of `Ḡ` to the one-variable model -/

/-- On `z ≥ 0` the singular piece `Ḡ` is `-(1/2)·Pi (5/α) z`, i.e.
`-(1/2) z^{-5/α}∫_0^z s^{5/α}(1+s)^{-2} ds` after the change of variables. -/
theorem Gbar_eq_of_nonneg (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    Work.Elliptic.Gbar α (Work.Construction.Fstar α) z = -(1 / 2) * Pi (5 / α) z := by
  have hαne : α ≠ 0 := ne_of_gt hα
  rw [Work.Elliptic.Gbar, EllFstar_Fstar α hα hα1]
  have hpt : ∀ s ∈ Set.uIcc (0:ℝ) z,
      s ^ ((5 - α) / α) * (α * Work.FM.Fstar s / 3)
        = (2 * α / 3) * (s ^ (5 / α) / (1 + s) ^ 2) := by
    intro s hs
    rw [Set.uIcc_of_le hz] at hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · subst h0
      rw [Real.zero_rpow (div_ne_zero (by linarith) hαne),
        Real.zero_rpow (div_ne_zero (by norm_num) hαne), zero_mul, zero_div, mul_zero]
    · rw [Work.FM.Fstar]
      have hrw : s ^ ((5 - α) / α) * s = s ^ (5 / α) := by
        rw [show (5:ℝ) / α = ((5 - α) / α) + 1 from by field_simp; ring,
          Real.rpow_add h0, Real.rpow_one]
      rw [show s ^ ((5 - α) / α) * (α * (2 * s / (1 + s) ^ 2) / 3)
          = (2 * α / 3) * (s ^ ((5 - α) / α) * s / (1 + s) ^ 2) from by ring, hrw]
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
  rcases eq_or_lt_of_le hz with hz0 | hz0
  · subst hz0
    rw [intervalIntegral.integral_same, Pi_def]
    ring
  · have hsub := At_subst (5 / α) 0 hz0
    simp only [Nat.cast_zero, add_zero, zero_add] at hsub
    rw [hsub, Pi_def]
    have hzp : z ^ (-(5 / α)) * z ^ (5 / α + 1) = z := by
      rw [← Real.rpow_add hz0]
      norm_num
    rw [show - (3 / (4 * α)) * z ^ (-(5 / α))
          * ((2 * α / 3) * (z ^ (5 / α + 1) * At (5 / α) 0 z))
        = (-(3 / (4 * α)) * (2 * α / 3) * (z ^ (-(5 / α)) * z ^ (5 / α + 1)))
          * At (5 / α) 0 z from by ring, hzp]
    field_simp
    norm_num

/-! ## The derivative chain for `ρ = -(1/2)·Pi N` -/

/-- The `k`-th derivative of `ρ = -(1/2)·Pi N` for `k ≤ 4` (computed from
`(At N j)' = -(j+2)At N (j+1)` and the Leibniz rule). -/
def Dk (N : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun z => -(1 / 2) * (z * At N 0 z)
  | 1 => fun z => -(1 / 2) * (At N 0 z - 2 * z * At N 1 z)
  | 2 => fun z => -(1 / 2) * (-4 * At N 1 z + 6 * z * At N 2 z)
  | 3 => fun z => -(1 / 2) * (18 * At N 2 z - 24 * z * At N 3 z)
  | _ => fun z => -(1 / 2) * (-96 * At N 3 z + 120 * z * At N 4 z)

@[simp] theorem Dk_zero (N : ℝ) : Dk N 0 = fun z => -(1 / 2) * (z * At N 0 z) := rfl
@[simp] theorem Dk_one (N : ℝ) : Dk N 1 = fun z => -(1 / 2) * (At N 0 z - 2 * z * At N 1 z) := rfl
@[simp] theorem Dk_two (N : ℝ) :
    Dk N 2 = fun z => -(1 / 2) * (-4 * At N 1 z + 6 * z * At N 2 z) := rfl
@[simp] theorem Dk_three (N : ℝ) :
    Dk N 3 = fun z => -(1 / 2) * (18 * At N 2 z - 24 * z * At N 3 z) := rfl
@[simp] theorem Dk_four (N : ℝ) :
    Dk N 4 = fun z => -(1 / 2) * (-96 * At N 3 z + 120 * z * At N 4 z) := rfl

/-- `(z ↦ z·At N m z)' = At N m z - (m+2)·z·At N (m+1) z`. -/
theorem hasDerivAt_z_mul_At (N : ℝ) (hN : 0 ≤ N) (m : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun w : ℝ => w * At N m w)
      (At N m z - ((m : ℝ) + 2) * z * At N (m + 1) z) z := by
  have h1 : HasDerivAt (fun w : ℝ => w) 1 z := hasDerivAt_id z
  have h2 : HasDerivAt (fun w : ℝ => At N m w) (-((m : ℝ) + 2) * At N (m + 1) z) z :=
    At_hasDerivAt N hN m hz
  have h3 := h1.mul h2
  convert h3 using 1
  ring

/-- The derivative chain of the model function: `(Dk N k)' = Dk N (k+1)` for `k ≤ 3`. -/
theorem Dk_hasDerivAt (N : ℝ) (hN : 0 ≤ N) (k : ℕ) (hk : k ≤ 3) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (Dk N k) (Dk N (k + 1) z) z := by
  have key : ∀ (m m' : ℕ) (c1 c2 : ℝ),
      HasDerivAt (fun w : ℝ => c1 * At N m w + c2 * (w * At N m' w))
        (c1 * (-((m : ℝ) + 2) * At N (m + 1) z)
          + c2 * (At N m' z - ((m' : ℝ) + 2) * z * At N (m' + 1) z)) z := by
    intro m m' c1 c2
    exact ((At_hasDerivAt N hN m hz).const_mul c1).add
      ((hasDerivAt_z_mul_At N hN m' hz).const_mul c2)
  interval_cases k
  · have h := (key 0 0 (0:ℝ) 1).const_mul (-(1 / 2))
    rw [Dk_zero, Dk_one]
    convert h using 1
    · funext y; ring
    · ring
  · have h := (key 0 1 (1:ℝ) (-2)).const_mul (-(1 / 2))
    rw [Dk_one, Dk_two]
    convert h using 1
    · funext y; ring
    · ring
  · have h := (key 1 2 (-4:ℝ) 6).const_mul (-(1 / 2))
    rw [Dk_two, Dk_three]
    convert h using 1
    · funext y; ring
    · ring
  · have h := (key 2 3 (18:ℝ) (-24)).const_mul (-(1 / 2))
    rw [Dk_three, Dk_four]
    convert h using 1
    · funext y; ring
    · ring

/-- Weighted bound for the model integrals: `(1+z)^c z^e At N j z = O(1/N)` whenever the
total exponent budget `c + e ≤ j + 1` is respected. -/
theorem shift_bound (N : ℝ) (hN : 2 ≤ N) (c j e : ℕ) (hc : c + e ≤ j + 1) {z : ℝ}
    (hz : 0 ≤ z) :
    |(1 + z) ^ c * (z ^ e * At N j z)| ≤ 2 ^ (c + 1) / N := by
  have hNpos : (0:ℝ) < N := by linarith
  have h1z : (0:ℝ) ≤ 1 + z := by linarith
  have hsum : (1 + z) ^ c * (z ^ e * At N j z)
      = ∑ m ∈ Finset.range (c + 1),
          (c.choose m : ℝ) * (z ^ (c - m + e) * At N j z) := by
    rw [add_pow]
    simp only [one_pow, one_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    calc z ^ (c - m) * ↑(c.choose m) * (z ^ e * At N j z)
        = ↑(c.choose m) * (z ^ (c - m) * z ^ e * At N j z) := by ring
      _ = ↑(c.choose m) * (z ^ (c - m + e) * At N j z) := by rw [← pow_add]
  rw [hsum]
  have hterm : ∀ m ∈ Finset.range (c + 1),
      |(c.choose m : ℝ) * (z ^ (c - m + e) * At N j z)| ≤ (c.choose m : ℝ) * (2 / N) := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hmc : c - m + e ≤ j + 1 := by omega
    have h := At_bound N hN j (c - m + e) hmc hz
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c.choose m : ℝ))]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsc : (∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ)) = (2:ℝ) ^ c := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  rw [hsc]
  have h2 : ((2:ℝ) ^ c) * (2 / N) = 2 ^ (c + 1) / N := by
    rw [pow_succ]; ring
  rw [h2]

/-- Linear-combination estimate: `|-(1/2)(c₁x + c₂y)| ≤ (1/2)((|c₁|+|c₂|)·M)` when
`|x|, |y| ≤ M`. -/
theorem abs_half_lin {x y c1 c2 M : ℝ} (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |-(1 / 2) * (c1 * x + c2 * y)| ≤ (1 / 2) * ((|c1| + |c2|) * M) := by
  rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc |c1 * x + c2 * y| ≤ |c1 * x| + |c2 * y| := abs_add_le _ _
    _ = |c1| * |x| + |c2| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ |c1| * M + |c2| * M :=
        add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
    _ = (|c1| + |c2|) * M := by ring

/-- The weighted bound for the model derivatives: `|(1+z)^k Dk N k z| ≤ 3456/N` for `k ≤ 4`. -/
theorem Dk_bound (N : ℝ) (hN : 5 ≤ N) (k : ℕ) (hk : k ≤ 4) {z : ℝ} (hz : 0 ≤ z) :
    |(1 + z) ^ k * Dk N k z| ≤ 3456 / N := by
  have hN2 : (2:ℝ) ≤ N := by linarith
  have hNpos : (0:ℝ) < N := by linarith
  have hfinal : ∀ c : ℝ, c ≤ 3456 → c / N ≤ 3456 / N := fun c hc =>
    div_le_div_of_nonneg_right hc (le_of_lt hNpos)
  interval_cases k
  · rw [pow_zero, one_mul, Dk_zero]
    have h := At_bound N hN2 0 1 (by omega) hz
    rw [pow_one] at h
    have h2 : |-(1 / 2) * (z * At N 0 z)| = (1 / 2) * |z * At N 0 z| := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
    rw [h2]
    have h3 : (1 / 2) * |z * At N 0 z| ≤ (1 / 2) * (2 / N) := by linarith
    refine h3.trans ?_
    have h4 : (1 / 2) * (2 / N) = 1 / N := by ring
    rw [h4]
    exact hfinal 1 (by norm_num)
  · rw [Dk_one]
    have hA := shift_bound N hN2 1 0 0 (by omega) hz
    have hB := shift_bound N hN2 1 1 1 (by omega) hz
    simp only [pow_zero, pow_one, one_mul] at hA hB
    have hE : (1 + z) ^ 1 * (-(1 / 2) * (At N 0 z - 2 * z * At N 1 z))
        = -(1 / 2) * (1 * ((1 + z) ^ 1 * At N 0 z)
            + (-2) * ((1 + z) ^ 1 * (z * At N 1 z))) := by ring
    rw [hE]
    simp only [pow_one]
    refine (abs_half_lin (c1 := 1) (c2 := -2) hA hB).trans ?_
    have hc : (1 / 2) * ((|(1:ℝ)| + |(-2:ℝ)|) * (2 ^ (1 + 1) / N)) = 6 / N := by
      norm_num; ring_nf
    rw [hc]
    exact hfinal 6 (by norm_num)
  · rw [Dk_two]
    have hA := shift_bound N hN2 2 1 0 (by omega) hz
    have hB := shift_bound N hN2 2 2 1 (by omega) hz
    simp only [pow_zero, pow_one, one_mul] at hA hB
    have hE : (1 + z) ^ 2 * (-(1 / 2) * (-4 * At N 1 z + 6 * z * At N 2 z))
        = -(1 / 2) * ((-4) * ((1 + z) ^ 2 * At N 1 z)
            + 6 * ((1 + z) ^ 2 * (z * At N 2 z))) := by ring
    rw [hE]
    refine (abs_half_lin (c1 := -4) (c2 := 6) hA hB).trans ?_
    have hc : (1 / 2) * ((|(-4:ℝ)| + |(6:ℝ)|) * (2 ^ (2 + 1) / N)) = 40 / N := by
      norm_num; ring_nf
    rw [hc]
    exact hfinal 40 (by norm_num)
  · rw [Dk_three]
    have hA := shift_bound N hN2 3 2 0 (by omega) hz
    have hB := shift_bound N hN2 3 3 1 (by omega) hz
    simp only [pow_zero, pow_one, one_mul] at hA hB
    have hE : (1 + z) ^ 3 * (-(1 / 2) * (18 * At N 2 z - 24 * z * At N 3 z))
        = -(1 / 2) * (18 * ((1 + z) ^ 3 * At N 2 z)
            + (-24) * ((1 + z) ^ 3 * (z * At N 3 z))) := by ring
    rw [hE]
    refine (abs_half_lin (c1 := 18) (c2 := -24) hA hB).trans ?_
    have hc : (1 / 2) * ((|(18:ℝ)| + |(-24:ℝ)|) * (2 ^ (3 + 1) / N)) = 336 / N := by
      norm_num; ring_nf
    rw [hc]
    exact hfinal 336 (by norm_num)
  · rw [Dk_four]
    have hA := shift_bound N hN2 4 3 0 (by omega) hz
    have hB := shift_bound N hN2 4 4 1 (by omega) hz
    simp only [pow_zero, pow_one, one_mul] at hA hB
    have hE : (1 + z) ^ 4 * (-(1 / 2) * (-96 * At N 3 z + 120 * z * At N 4 z))
        = -(1 / 2) * ((-96) * ((1 + z) ^ 4 * At N 3 z)
            + 120 * ((1 + z) ^ 4 * (z * At N 4 z))) := by ring
    rw [hE]
    refine (abs_half_lin (c1 := -96) (c2 := 120) hA hB).trans ?_
    have hc : (1 / 2) * ((|(-96:ℝ)| + |(120:ℝ)|) * (2 ^ (4 + 1) / N)) = 3456 / N := by
      norm_num; ring_nf
    rw [hc]

/-- On `(0,∞)` the `deriv`-iterates of the model function `Dk N 0` are the `Dk N k`. -/
theorem EqOn_iter_Dk (N : ℝ) (hN : 0 ≤ N) (f : ℝ → ℝ) (hf : EqOn f (Dk N 0) (Set.Ioi 0)) :
    ∀ k ≤ 4, EqOn ((deriv^[k]) f) (Dk N k) (Set.Ioi 0) := by
  intro k _
  induction k with
  | zero => simpa using hf
  | succ k ih =>
      intro w hw
      have hk' : k ≤ 4 := le_trans (Nat.le_succ k) (by omega)
      have hk3 : k ≤ 3 := by omega
      have hprev := ih hk'
      rw [Function.iterate_succ_apply']
      have hev : (deriv^[k]) f =ᶠ[𝓝 w] Dk N k := by
        filter_upwards [isOpen_Ioi.mem_nhds hw] with y hy
        exact hprev hy
      rw [hev.deriv_eq, (Dk_hasDerivAt N hN k hk3 (le_of_lt hw)).deriv]

/-- The values at `z = 0`: each `deriv`-iterate at `0` is either the junk value `0` or the
model value `Dk N k 0`.  (Only the right-hand behaviour of `f` is used, so this is where the
non-differentiability of `Ḡ` at `z = 0` is absorbed.) -/
theorem deriv_iter_value (N : ℝ) (hN : 0 ≤ N) (f : ℝ → ℝ)
    (hf : EqOn f (Dk N 0) (Set.Ioi 0)) (hf0 : f 0 = 0) :
    ∀ k ≤ 4, (deriv^[k]) f 0 = 0 ∨ (deriv^[k]) f 0 = Dk N k 0 := by
  have hagree := EqOn_iter_Dk N hN f hf
  intro k _
  induction k with
  | zero => exact Or.inl hf0
  | succ k ih =>
      have hk4 : k ≤ 4 := le_trans (Nat.le_succ k) (by omega)
      have hk3 : k ≤ 3 := by omega
      have hprev := ih hk4
      have heq : (deriv^[k]) f =ᶠ[𝓝[>] (0:ℝ)] Dk N k := by
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact hagree k hk4 hw
      have hcont : ContinuousAt (Dk N k) 0 := (Dk_hasDerivAt N hN k hk3 le_rfl).continuousAt
      rw [Function.iterate_succ_apply']
      have hmono : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] (0:ℝ) := nhdsWithin_mono 0 fun x hx => ne_of_gt hx
      by_cases hcase : (deriv^[k]) f 0 = Dk N k 0
      · by_cases hd : DifferentiableAt ℝ ((deriv^[k]) f) 0
        · right
          have hslope : Tendsto (slope ((deriv^[k]) f) 0) (𝓝[>] (0:ℝ))
              (𝓝 (deriv ((deriv^[k]) f) 0)) :=
            (hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt).mono_left hmono
          have h2 : Tendsto (slope (Dk N k) 0) (𝓝[>] (0:ℝ)) (𝓝 (Dk N (k + 1) 0)) :=
            (hasDerivAt_iff_tendsto_slope.mp
              (Dk_hasDerivAt N hN k hk3 le_rfl)).mono_left hmono
          have h3 : slope ((deriv^[k]) f) 0 =ᶠ[𝓝[>] (0:ℝ)] slope (Dk N k) 0 := by
            filter_upwards [heq] with w hw
            simp only [slope_def_field, hw, hcase]
          exact tendsto_nhds_unique hslope (h2.congr' h3.symm)
        · left
          exact deriv_zero_of_not_differentiableAt hd
      · left
        rw [deriv_zero_of_not_differentiableAt]
        intro hd
        have hc : ContinuousAt ((deriv^[k]) f) 0 := hd.continuousAt
        have h1 : Tendsto ((deriv^[k]) f) (𝓝[>] (0:ℝ)) (𝓝 ((deriv^[k]) f 0)) :=
          hc.tendsto.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto ((deriv^[k]) f) (𝓝[>] (0:ℝ)) (𝓝 (Dk N k 0)) :=
          Tendsto.congr' heq.symm (hcont.tendsto.mono_left nhdsWithin_le_nhds)
        exact hcase (tendsto_nhds_unique h1 h2)

/-- `pzIter k` of a radial function is the `k`-th `deriv`-iterate. -/
theorem pzIter_radial (g : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z θ => g z) z θ = (deriv^[k]) g z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      simp only [ih]
      rw [Function.iterate_succ_apply']

/-- `DthIter j` of a radial function vanishes for `j ≥ 1`. -/
theorem DthIter_radial (g : ℝ → ℝ) (j : ℕ) (hj : 1 ≤ j) :
    Work.Spaces.DthIter j (fun z θ => g z) = fun _ _ => (0:ℝ) := by
  induction j with
  | zero => omega
  | succ j ih =>
      cases j with
      | zero =>
          funext z θ
          rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
          simp only [Work.Spaces.Dth, Work.Spaces.pth]
          rw [show deriv (fun θ' : ℝ => (fun z θ => g z) z θ') θ = 0 from deriv_const _ _,
            mul_zero]
      | succ j =>
          rw [Work.Spaces.DthIter_succ, ih (by omega)]
          funext z θ
          simp only [Work.Spaces.Dth, Work.Spaces.pth, Pi.zero_apply]
          rw [show deriv (fun θ' : ℝ => (0:ℝ)) θ = 0 from deriv_const _ _, mul_zero]

/-- `pzIter k` of the zero function is zero. -/
theorem pzIter_zero_fun (k : ℕ) :
    Work.Spaces.pzIter k (fun _ _ => (0:ℝ)) = fun _ _ => (0:ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Work.Spaces.pzIter_succ, ih]; funext z θ; simp [Work.Spaces.pz]

/-- `supAbs` of the zero function is `0`. -/
theorem supAbs_zero : Work.Spaces.supAbs (fun _ _ => (0:ℝ)) = 0 := by
  rw [Work.Spaces.supAbs]
  simp only [abs_zero]
  rw [show {y : ℝ | ∃ z ∈ Work.Spaces.Iz, ∃ θ ∈ Work.Spaces.Iθ, y = 0} = {0} from by
    ext y; constructor
    · rintro ⟨z, hz, θ, hθ, rfl⟩; rfl
    · intro hy
      exact ⟨0, by simp [Work.Spaces.Iz], 0,
        by simp [Work.Spaces.Iθ]; linarith [Real.pi_pos], hy⟩]
  exact csSup_singleton (0:ℝ)

/-- For a radial function the `𝒲^{4,∞}`-norm is the sum of the four radial sup-norms. -/
theorem WlInf_radial (α : ℝ) (g : ℝ → ℝ) :
    Work.Spaces.WlInf α 4 (fun z θ => g z)
      = ∑ k ∈ Finset.range 5,
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k (fun z θ => g z) z θ) := by
  rw [Work.Spaces.WlInf]
  have hzero : (∑ j ∈ Finset.range 5, ∑ k ∈ Finset.range 5,
      if 1 ≤ j ∧ k + j ≤ 4 then
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ => g z)) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      else 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun k hk => ?_
    by_cases hc : 1 ≤ j ∧ k + j ≤ 4
    · rw [if_pos hc]
      have h1 : Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => g z))
          = fun _ _ => (0:ℝ) := by
        rw [DthIter_radial g j hc.1, pzIter_zero_fun]
      simp only [h1, Pi.zero_apply, mul_zero, zero_mul, zero_div]
      exact supAbs_zero
    · rw [if_neg hc]
  rw [hzero, add_zero]

/-- The weighted pointwise bound for the `deriv`-iterates of the singular piece `Ḡ`. -/
theorem gbar_iter_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (hk : k ≤ 4) {z : ℝ}
    (hz : 0 ≤ z) :
    |(1 + z) ^ k * (deriv^[k]) (fun w => Work.Elliptic.Gbar α (Work.Construction.Fstar α) w) z|
      ≤ 3456 * α := by
  have hN5 : (5:ℝ) ≤ 5 / α := by
    rw [le_div_iff₀ hα]; linarith
  have hf : EqOn (fun w => Work.Elliptic.Gbar α (Work.Construction.Fstar α) w)
      (Dk (5 / α) 0) (Set.Ioi 0) := by
    intro w hw
    rw [Dk_zero]
    exact Gbar_eq_of_nonneg α hα hα1 (le_of_lt hw)
  have harith : 3456 / (5 / α) ≤ 3456 * α := by
    have h5 : α * (5 / α) = 5 := by field_simp
    rw [div_le_iff₀ (div_pos (by norm_num) hα),
      show (3456:ℝ) * α * (5 / α) = 3456 * (α * (5 / α)) from by ring, h5]
    linarith
  rcases eq_or_lt_of_le hz with hz0 | hz0
  · subst hz0
    have hf0 : (fun w => Work.Elliptic.Gbar α (Work.Construction.Fstar α) w) 0 = 0 := by
      change Work.Elliptic.Gbar α (Work.Construction.Fstar α) 0 = 0
      rw [Gbar_eq_of_nonneg α hα hα1 le_rfl, Pi_def]
      ring
    rcases deriv_iter_value (5 / α) (by linarith) _ hf hf0 k hk with h | h
    · rw [h]
      simp only [mul_zero, abs_zero]
      exact mul_nonneg (by norm_num) (le_of_lt hα)
    · rw [h]
      have hb := (Dk_bound (5 / α) hN5 k hk (le_refl (0:ℝ))).trans harith
      simpa only [add_zero, one_pow, one_mul] using hb
  · have hval := EqOn_iter_Dk (5 / α) (by linarith) _ hf k hk hz0
    rw [hval]
    exact (Dk_bound (5 / α) hN5 k hk hz).trans harith

theorem Gbar_wiln : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 4 (fun z θ => Work.Elliptic.Gbar α (Work.Construction.Fstar α) z) ∧
    Work.Spaces.WlInf α 4 (fun z θ => Work.Elliptic.Gbar α (Work.Construction.Fstar α) z) ≤ C * α := by
  refine ⟨20000, by norm_num, fun α hα hα1 => ⟨?_, ?_⟩⟩
  · refine ⟨fun k hk => ?_, fun j hj k hk hj1 hkj => ?_⟩
    · refine ⟨3456 * α, fun y hy => ?_⟩
      obtain ⟨z, hz, θ, hθ, rfl⟩ := hy
      show |(z + 1) ^ k * Work.Spaces.pzIter k
        (fun z θ => Work.Elliptic.Gbar α (Work.Construction.Fstar α) z) z θ| ≤ 3456 * α
      rw [pzIter_radial]
      have hb := gbar_iter_bound α hα hα1 k hk hz
      rw [show (1:ℝ) + z = z + 1 from by ring] at hb
      exact hb
    · refine ⟨0, fun y hy => ?_⟩
      obtain ⟨z, hz, θ, hθ, rfl⟩ := hy
      have h1 : Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ => Work.Elliptic.Gbar α (Work.Construction.Fstar α) z))
          = fun _ _ => (0:ℝ) := by
        rw [DthIter_radial _ j hj1, pzIter_zero_fun]
      simp only [h1, Pi.zero_apply, mul_zero, zero_mul, zero_div, abs_zero]
      exact le_refl 0
  · rw [WlInf_radial]
    calc ∑ k ∈ Finset.range 5, Work.Spaces.supAbs
            (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
              (fun z θ => Work.Elliptic.Gbar α (Work.Construction.Fstar α) z) z θ)
        ≤ ∑ k ∈ Finset.range 5, (3456 * α) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk4 : k ≤ 4 := by
            rw [Finset.mem_range] at hk; omega
          refine csSup_le ⟨|(0 + 1) ^ k * Work.Spaces.pzIter k
              (fun z θ => Work.Elliptic.Gbar α (Work.Construction.Fstar α) z) 0 0|,
              0, by simp [Work.Spaces.Iz], 0, ?_, rfl⟩ fun y hy => ?_
          · simp only [Work.Spaces.Iθ, Set.mem_Icc]
            exact ⟨le_rfl, by linarith [Real.pi_pos]⟩
          · obtain ⟨z, hz, θ, hθ, rfl⟩ := hy
            show |(z + 1) ^ k * Work.Spaces.pzIter k
              (fun z θ => Work.Elliptic.Gbar α (Work.Construction.Fstar α) z) z θ| ≤ 3456 * α
            rw [pzIter_radial]
            have hb := gbar_iter_bound α hα hα1 k hk4 hz
            rw [show (1:ℝ) + z = z + 1 from by ring] at hb
            exact hb
      _ = 5 * (3456 * α) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
      _ ≤ 20000 * α := by nlinarith [hα]

end Work.FTS.H2.PhiStarE
