import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.hetero_local
import Submission.Work.EQ.hetero_leaf
import Submission.Work.EQ.germPt_basic
import Submission.Work.EQ.germPt_eqU
import Submission.Work.EQ.arc_eqU_maps
import Submission.Work.EQ.loc_estimates
import Submission.Work.EQ.orb_sep
import Submission.Work.EQ.arc_near_A1

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## The leaf argument: the germ curve lies on the equichordal curve

Near `A₁ = -1/2` the two-step map `T = eqU ∘ eqU` has the invariant `χ` of `hetero_leaf.lean`.
Both the germ curve `t ↦ germPt a h t` and the open upper arc of the equichordal curve are
`T`-invariant curves converging to `A₁`, hence are contained in the level set `{χ = 0}`; since
the level sets of `χ` meet every horizontal line in at most one point (`orb_sep`), the two curves
agree near `A₁`.  This file proves that the germ curve lies on the arc for small `t`. -/

namespace Work.EQ

open Complex Filter
open scoped Topology

noncomputable section

variable {a : ℝ}

/-! ### Elementary facts -/

theorem eqLam_pos_hb {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; positivity

theorem eqLam_lt_one_hb {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

/-- The normalised curve as a subset of `ℂ`. -/
def arcSet (a : ℝ) (ρ : ℝ → ℝ) : Set ℂ := Set.range fun θ => polarPt (-(a / 2)) (ρ θ) θ

/-! ### From `loc_estimates` to a `LocData` package -/

theorem locData_nonempty {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : Nonempty (LocData a) := by
  obtain ⟨ρ, h, κ, C, hρ, hh, hκ, hκ1, hC, hCh, hCρ, hb1, hb2, hb3, hb4⟩ := loc_estimates ha0 ha1
  exact ⟨⟨ρ, h, κ, C, hρ, hh, hκ, hκ1, hC, hCh, hCρ, hb1, hb2, hb3, hb4⟩⟩

theorem small_thresh (d : LocData a) : ∃ y₀ : ℝ, 0 < y₀ ∧ ∀ y : ℝ, 0 < y → y ≤ y₀ → d.Small y := by
  set S := 1 / (1 - d.κ ^ 2) + 8 * d.C / (d.κ * (1 - d.κ ^ 2) ^ 2) with hSdef
  set T := d.κ * (1 - d.κ) ^ 2 / (32 * d.C) with hTdef
  have hSpos : 0 < S := by
    rw [hSdef]
    exact add_pos (one_div_pos.mpr d.one_sub_sq_pos)
      (div_pos (mul_pos (by norm_num) d.Cpos) (mul_pos d.κpos (pow_pos d.one_sub_sq_pos 2)))
  have hTpos : 0 < T := by
    rw [hTdef]
    exact div_pos (mul_pos d.κpos (pow_pos (by linarith [d.κlt]) 2)) (mul_pos (by norm_num) d.Cpos)
  have hApos : 0 < 1 / (8 * d.C * S) := one_div_pos.mpr (mul_pos (mul_pos (by norm_num) d.Cpos) hSpos)
  refine ⟨min 1 (min (Real.sqrt (1 / (8 * d.C * S))) T),
    lt_min one_pos (lt_min (Real.sqrt_pos.mpr hApos) hTpos), ?_⟩
  intro y hy0 hy
  have hy2 : y ≤ Real.sqrt (1 / (8 * d.C * S)) :=
    le_trans hy (le_trans (min_le_right _ _) (min_le_left _ _))
  have hy3 : y ≤ T := le_trans hy (le_trans (min_le_right _ _) (min_le_right _ _))
  have h1g : 2 * d.C * y ^ 2 * S ≤ 1 / 2 := by
    have hsq : y ^ 2 ≤ 1 / (8 * d.C * S) := by
      have h := pow_le_pow_left₀ (le_of_lt hy0) hy2 2
      rwa [Real.sq_sqrt (le_of_lt hApos)] at h
    calc 2 * d.C * y ^ 2 * S ≤ 2 * d.C * (1 / (8 * d.C * S)) * S :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by linarith [d.Cpos]))
            (le_of_lt hSpos)
      _ = 1 / 4 := by
          have hC0 : d.C ≠ 0 := ne_of_gt d.Cpos
          have hS0 : S ≠ 0 := ne_of_gt hSpos
          field_simp
          ring
      _ ≤ 1 / 2 := by norm_num
  have h2g : 2 * d.C * y / (1 - d.κ) ^ 2 ≤ d.κ / 8 := by
    have h1k : 0 < 1 - d.κ := by linarith [d.κlt]
    calc 2 * d.C * y / (1 - d.κ) ^ 2 ≤ 2 * d.C * T / (1 - d.κ) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (pow_nonneg (le_of_lt h1k) 2)
          exact mul_le_mul_of_nonneg_left hy3 (by linarith [d.Cpos])
      _ = d.κ / 16 := by
          rw [hTdef]
          have hC0 : d.C ≠ 0 := ne_of_gt d.Cpos
          field_simp
          ring
      _ ≤ d.κ / 8 := by linarith [d.κpos]
  rw [LocData.Small, ← hSdef]
  exact ⟨h1g, h2g⟩

/-! ### Coordinates centred at `A₁` and the bridge to `LocData` -/

/-- The point of `ℂ` with `A₁`-centred coordinates `(x,y)`. -/
def ofCoord (p : ℝ × ℝ) : ℂ := (-(1/2) : ℂ) + ((p.1 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * I

theorem ofCoord_re (p : ℝ × ℝ) : (ofCoord p).re = p.1 - 1 / 2 := by
  simp only [ofCoord, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, sub_re, Complex.neg_re, Complex.ofReal_ofNat]
  norm_num
  ring

theorem ofCoord_im (p : ℝ × ℝ) : (ofCoord p).im = p.2 := by
  simp [ofCoord]

theorem toCoord_ofCoord (p : ℝ × ℝ) : ((ofCoord p).re + 1 / 2, (ofCoord p).im) = p := by
  rw [ofCoord_re, ofCoord_im]
  simp

theorem ofCoord_toCoord (z : ℂ) : ofCoord (z.re + 1 / 2, z.im) = z := by
  rw [ofCoord]
  apply Complex.ext <;> simp

theorem eqU_ofCoord (p : ℝ × ℝ) : eqU a (ofCoord p) = ofCoord (locFn a p) := by
  have h : ofCoord p = (-(1/2) : ℂ) + (((p.1 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * I) := by
    rw [ofCoord]; ring
  rw [h, eqU_add, locU_eq]
  rw [ofCoord, locFn]
  ring

theorem eqU_iterate_ofCoord (p : ℝ × ℝ) (n : ℕ) :
    (eqU a)^[n] (ofCoord p) = ofCoord ((locFn a)^[n] p) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', eqU_ofCoord]

theorem iterate_mul_comm {α : Type*} (f : α → α) (n : ℕ) (x : α) :
    f^[n] (f x) = f (f^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]

theorem orb_eq_iterate (x y : ℝ) (n : ℕ) :
    LocData.orb a x y n = (locT a)^[n] (x, y) := by
  induction n with
  | zero => simp [LocData.orb]
  | succ n ih => rw [LocData.orb_succ, ih, Function.iterate_succ_apply']

theorem locFn_sq (q : ℝ × ℝ) : (locFn a)^[2] q = locT a q := rfl

theorem orb_eqU (p : ℝ × ℝ) (n : ℕ) :
    (eqU a)^[2 * n] (ofCoord p) = ofCoord (LocData.orb a p.1 p.2 n) := by
  have key : ∀ (q : ℝ × ℝ) (n : ℕ), (locFn a)^[2 * n] q = (locT a)^[n] q := by
    intro q n
    induction n generalizing q with
    | zero => simp
    | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 2 by ring, Function.iterate_add_apply, locFn_sq,
          ih (locT a q), iterate_mul_comm (locT a) n q, Function.iterate_succ_apply']
  rw [eqU_iterate_ofCoord, key p n, ← orb_eq_iterate]


/-! ### The upper arc under the half-map -/

/-- `eqU` maps a point of the open upper arc into the open upper arc. -/
theorem eqU_mem_arc {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ))
    {z : ℂ} (hz : z ∈ arcSet a ρ₁) (him : 0 < z.im) :
    eqU a z ∈ arcSet a ρ₁ ∧ 0 < (eqU a z).im := by
  obtain ⟨-, -, -, -, -, harcθ, -, -⟩ := arc_near_A1 ha0 ha1 hC hs₁ hs₂
  obtain ⟨hUmap, -, -⟩ := arc_eqU_maps ha0 ha1 hC hs₁ hs₂
  obtain ⟨θ, hθ0, hθπ, hθeq⟩ := harcθ z hz him
  subst hθeq
  obtain ⟨θ', hθ'0, hθ'π, hθ'eq⟩ := hUmap θ hθ0 hθπ
  refine ⟨⟨θ', hθ'eq.symm⟩, ?_⟩
  rw [hθ'eq]
  have hb := (polarPt_basic (c := -(a/2)) (r := ρ₁ θ') (θ := θ') (hC.2.2.1 θ')).1
  rw [hb]
  exact mul_pos (hC.2.2.1 θ') (Real.sin_pos_of_pos_of_lt_pi hθ'0 hθ'π)

/-- The parametrised arc point. -/
def arcPt (a : ℝ) (ρ₁ : ℝ → ℝ) (θ : ℝ) : ℂ := polarPt (-(a / 2)) (ρ₁ θ) θ

theorem arcPt_continuousAt {a : ℝ} {ρ₁ ρ₂ : ℝ → ℝ} (hC : NormEqCurve a ρ₁ ρ₂) (θ : ℝ) :
    ContinuousAt (fun s : ℝ => arcPt a ρ₁ s) θ := by
  have hfun : (fun s : ℝ => arcPt a ρ₁ s) =
      fun s => (((-(a / 2) : ℝ)) : ℂ) + ((ρ₁ s : ℝ) : ℂ) * Complex.exp (((s : ℂ) * I)) := by
    funext s
    rw [arcPt, polarPt]
  rw [hfun]
  exact ContinuousAt.add continuousAt_const
    ((Complex.continuous_ofReal.continuousAt.comp hC.1.continuousAt).mul
      (Complex.continuous_exp.continuousAt.comp
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)))

/-- Points of the open upper arc, with heights tending to `0` and `x`-deviations bounded by
`2ρ'`, converge to `A₁`. -/
theorem arc_tendsto_A1 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ))
    {ρ' : ℝ} (hρ' : 0 < ρ') (h2ρ'1 : 2 * ρ' < 1)
    {p : ℕ → ℂ} (harc : ∀ n, p n ∈ arcSet a ρ₁) (him : ∀ n, 0 < (p n).im)
    (hx : ∀ n, |(p n).re + 1 / 2| ≤ 2 * ρ')
    (hy : Filter.Tendsto (fun n => (p n).im) Filter.atTop (nhds 0)) :
    Filter.Tendsto p Filter.atTop (nhds ((-(1/2) : ℂ))) := by
  obtain ⟨hA1, -, -, -, -, harcθ, htrich, -⟩ := arc_near_A1 ha0 ha1 hC hs₁ hs₂
  choose θ hθ0 hθπ hθeq using fun n => harcθ (p n) (harc n) (him n)
  have hcont := arcPt_continuousAt hC Real.pi
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨ε, hε0, hε⟩ := Metric.continuousAt_iff.mp hcont δ hδ
  have hε'0 : 0 < min ε (Real.pi / 2) := lt_min hε0 (by linarith [Real.pi_pos])
  have hε'π : min ε (Real.pi / 2) < Real.pi := lt_of_le_of_lt (min_le_right _ _)
    (by linarith [Real.pi_pos])
  obtain ⟨η, hη0, hη⟩ := htrich (2 * ρ') (by linarith) h2ρ'1 (min ε (Real.pi / 2)) hε'0 hε'π
  have hev : ∀ᶠ n in Filter.atTop, (p n).im ≤ η := hy.eventually (eventually_le_nhds hη0)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  have hlt : θ n > Real.pi - min ε (Real.pi / 2) :=
    hη (θ n) (hθ0 n) (hθπ n) (by rw [← hθeq n]; exact hN n hn)
      (by rw [← hθeq n]; exact hx n)
  have hdist : dist (θ n) Real.pi < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hlt, hθπ n, min_le_left ε (Real.pi / 2), Real.pi_pos]
  have hfin := hε hdist
  simpa only [hθeq n, hA1, arcPt] using hfin

/-! ### `χ` vanishes on the arc in the box -/

/-- A bound for the `x`-coordinate of the orbit of a point of the small box. -/
theorem orb_x_le_small (d : LocData a) {x y ρ' h' : ℝ} (hx : |x| ≤ ρ') (hx2 : |x| ≤ 2 * d.ρ)
    (hy0 : 0 < y) (hyh : y ≤ h') (hh'h : h' ≤ d.h)
    (hdrift : d.C * h' ^ 2 / (1 - d.κ ^ 2) ≤ ρ') (n : ℕ) :
    |(LocData.orb a x y n).1| ≤ 2 * ρ' := by
  have hps : ∀ n, (LocData.orb a x y n).1 = x + ∑ k ∈ Finset.range n, LocData.incr a x y k := by
    intro n
    induction n with
    | zero => simp [LocData.orb]
    | succ n ih =>
        have hstep : (LocData.orb a x y (n + 1)).1 =
            (LocData.orb a x y n).1 + LocData.incr a x y n := by
          rw [LocData.incr, LocData.orb_succ]; ring
        rw [hstep, ih, Finset.sum_range_succ]
        ring
  have hyh' : y ≤ d.h := le_trans hyh hh'h
  have hterm : ∀ k, |LocData.incr a x y k| ≤ d.C * y ^ 2 * (d.κ ^ 2) ^ k :=
    fun k => LocData.abs_incr_le d x y hx2 hy0 hyh' k
  have hsumle : (∑ k ∈ Finset.range n, |LocData.incr a x y k|)
      ≤ d.C * y ^ 2 * (∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hterm k
  have hgeom : d.C * y ^ 2 * (∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k) ≤ d.C * h' ^ 2 / (1 - d.κ ^ 2) := by
    have h1 : (∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k) ≤ 1 / (1 - d.κ ^ 2) := by
      have h2 : (∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k) = (1 - (d.κ ^ 2) ^ n) / (1 - d.κ ^ 2) := by
        rw [geom_sum_eq (by nlinarith [d.κpos, d.κlt]) n]
        rw [div_eq_div_iff (by nlinarith [d.κpos, d.κlt]) (ne_of_gt d.one_sub_sq_pos)]
        ring
      rw [h2, div_le_div_iff_of_pos_right d.one_sub_sq_pos]
      have h3 : 0 ≤ (d.κ ^ 2) ^ n := by positivity
      linarith
    have hy2 : y ^ 2 ≤ h' ^ 2 := by nlinarith [hy0, hyh]
    calc d.C * y ^ 2 * (∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k)
        ≤ d.C * y ^ 2 * (1 / (1 - d.κ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (le_of_lt d.Cpos) (sq_nonneg y))
      _ = d.C * y ^ 2 / (1 - d.κ ^ 2) := by ring
      _ ≤ d.C * h' ^ 2 / (1 - d.κ ^ 2) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt d.one_sub_sq_pos)
          exact mul_le_mul_of_nonneg_left hy2 (le_of_lt d.Cpos)
  calc |(LocData.orb a x y n).1| = |x + ∑ k ∈ Finset.range n, LocData.incr a x y k| := by rw [hps]
    _ ≤ |x| + |∑ k ∈ Finset.range n, LocData.incr a x y k| := abs_add_le _ _
    _ ≤ |x| + ∑ k ∈ Finset.range n, |LocData.incr a x y k| := by
        have := Finset.abs_sum_le_sum_abs (fun k => LocData.incr a x y k) (Finset.range n)
        linarith
    _ ≤ ρ' + d.C * y ^ 2 * (∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k) := by linarith [hsumle]
    _ ≤ ρ' + d.C * h' ^ 2 / (1 - d.κ ^ 2) := by linarith [hgeom]
    _ ≤ 2 * ρ' := by linarith [hdrift]

/-- Points of the open upper arc inside the small box have `χ = 0`. -/
theorem arc_chi_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ))
    (d : LocData a) {ρ' h' : ℝ} (hρ' : 0 < ρ') (h2ρ'ρ : 2 * ρ' ≤ d.ρ) (h2ρ'1 : 2 * ρ' < 1)
    (hh' : h' ≤ d.h) (hdrift : d.C * h' ^ 2 / (1 - d.κ ^ 2) ≤ ρ')
    {z : ℂ} (hz : z ∈ arcSet a ρ₁) (hzim : 0 < z.im) (hzx : |z.re + 1 / 2| ≤ ρ')
    (hzy : z.im ≤ h') : LocData.chi a (z.re + 1 / 2) z.im = 0 := by
  have hUmem : ∀ w ∈ arcSet a ρ₁, 0 < w.im → eqU a w ∈ arcSet a ρ₁ ∧ 0 < (eqU a w).im :=
    fun w hw hwim => eqU_mem_arc ha0 ha1 hC hs₁ hs₂ hw hwim
  have hUiter : ∀ m : ℕ, (eqU a)^[m] z ∈ arcSet a ρ₁ ∧ 0 < ((eqU a)^[m] z).im := by
    intro m
    induction m with
    | zero => simpa using ⟨hz, hzim⟩
    | succ m ih => rw [Function.iterate_succ_apply']; exact hUmem _ ih.1 ih.2
  have horb : ∀ n, ofCoord (LocData.orb a (z.re + 1/2) z.im n) ∈ arcSet a ρ₁ ∧
      0 < (ofCoord (LocData.orb a (z.re + 1/2) z.im n)).im := by
    intro n
    have h := orb_eqU (a := a) (z.re + 1/2, z.im) n
    rw [ofCoord_toCoord] at h
    rw [← h]
    exact hUiter (2 * n)
  have hXρ : |z.re + 1/2| ≤ 2 * d.ρ := by linarith [hzx, h2ρ'ρ, d.ρpos]
  have hlim : Filter.Tendsto (fun n => (LocData.orb a (z.re + 1/2) z.im n).1) Filter.atTop
      (nhds (LocData.chi a (z.re + 1/2) z.im)) :=
    LocData.chi_eq_lim d _ _ hXρ hzim (le_trans hzy hh')
  -- heights tend to 0
  have hhtend : Filter.Tendsto (fun n => (LocData.orb a (z.re + 1/2) z.im n).2) Filter.atTop
      (nhds 0) := by
    have h0 : Filter.Tendsto (fun n => d.κ ^ n * z.im) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt d.κpos) d.κlt).mul_const z.im
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun n => (LocData.orb_y_pos d _ _ hXρ hzim (le_trans hzy hh') n).le)
      (fun n => LocData.orb_y_le d _ _ hXρ hzim (le_trans hzy hh') n)
  -- the corresponding parameters tend to `π`
  obtain ⟨-, -, -, -, -, harcθ, htrich, -⟩ := arc_near_A1 ha0 ha1 hC hs₁ hs₂
  have hθtend : ∀ ε : ℝ, 0 < ε → ε < Real.pi → ∃ N, ∀ n, N ≤ n →
      Real.pi - ε < Classical.choose (harcθ (ofCoord (LocData.orb a (z.re + 1/2) z.im n))
        (horb n).1 (horb n).2) := by
    intro ε hε0 hεπ
    obtain ⟨η, hη0, hη⟩ := htrich (2 * ρ') (by linarith) h2ρ'1 ε hε0 hεπ
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hhtend.eventually (eventually_le_nhds hη0))
    refine ⟨N, fun n hn => ?_⟩
    have h1 : (LocData.orb a (z.re + 1/2) z.im n).2 ≤ η := hN n hn
    have h2 : |(LocData.orb a (z.re + 1/2) z.im n).1| ≤ 2 * ρ' :=
      orb_x_le_small d hzx hXρ hzim hzy hh' hdrift n
    have h3 : (ofCoord (LocData.orb a (z.re + 1/2) z.im n)).im = (LocData.orb a (z.re + 1/2) z.im n).2 :=
      ofCoord_im _
    have h4 : |(ofCoord (LocData.orb a (z.re + 1/2) z.im n)).re + 1/2| =
        |(LocData.orb a (z.re + 1/2) z.im n).1| := by
      rw [ofCoord_re]; congr 1; ring
    refine hη _ (Classical.choose_spec (harcθ _ (horb n).1 (horb n).2)).1
      (Classical.choose_spec (harcθ _ (horb n).1 (horb n).2)).2.1 ?_ ?_
    · rw [← (Classical.choose_spec (harcθ _ (horb n).1 (horb n).2)).2.2, h3]; exact h1
    · rw [← (Classical.choose_spec (harcθ _ (horb n).1 (horb n).2)).2.2, h4]; exact h2
  -- convergence of the orbit to `A₁`
  have hconv : Filter.Tendsto (fun n => ofCoord (LocData.orb a (z.re + 1/2) z.im n)) Filter.atTop
      (nhds ((-(1/2)) : ℂ)) := by
    refine arc_tendsto_A1 ha0 ha1 hC hs₁ hs₂ hρ' h2ρ'1 (fun n => (horb n).1) (fun n => (horb n).2)
      (fun n => ?_) ?_
    · rw [ofCoord_re]
      have := orb_x_le_small d hzx hXρ hzim hzy hh' hdrift n
      rw [abs_le] at this ⊢
      constructor <;> linarith [this.1, this.2]
    · simpa only [ofCoord_im] using hhtend
  have hX0 : Filter.Tendsto (fun n => (LocData.orb a (z.re + 1/2) z.im n).1) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun n => (ofCoord (LocData.orb a (z.re + 1/2) z.im n)).re)
        Filter.atTop (nhds (-(1/2))) := by
      have hlin : Complex.re (-(1/2) : ℂ) = -(1/2) := by norm_num
      have hc : Filter.Tendsto (fun n => (ofCoord (LocData.orb a (z.re + 1/2) z.im n)).re)
          Filter.atTop (nhds (Complex.re (-(1/2) : ℂ))) :=
        Complex.continuous_re.continuousAt.tendsto.comp hconv
      rwa [hlin] at hc
    have h2 := h1.add (tendsto_const_nhds (x := (1/2 : ℝ)))
    have hre : ∀ n, (ofCoord (LocData.orb a (z.re + 1/2) z.im n)).re + 1/2 =
        (LocData.orb a (z.re + 1/2) z.im n).1 := by
      intro n; rw [ofCoord_re]; ring
    simpa only [hre, neg_add_cancel] using h2
  exact tendsto_nhds_unique hlim hX0


/-! ### `χ` vanishes on the germ curve -/

theorem germ_chi_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (d : LocData a) {ρ' h' : ℝ} (hρ' : 0 < ρ') (hρ'ρ : 2 * ρ' ≤ d.ρ)
    (hh'pos : 0 < h') (hh'h : h' ≤ d.h) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
      |(germPt a h t).re + 1 / 2| ≤ ρ' ∧ (germPt a h t).im ≤ h' ∧
      LocData.chi a ((germPt a h t).re + 1 / 2) (germPt a h t).im = 0 := by
  obtain ⟨ε₁, hε₁pos, -, hε₁im, hε₁tend⟩ := germPt_basic ha0 ha1 hh
  obtain ⟨ε₂, hε₂pos, hε₂eq⟩ := germPt_eqU ha0 ha1 hh
  -- the germ point is eventually in the box
  have hbox : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      |(germPt a h t).re + 1 / 2| ≤ ρ' ∧ (germPt a h t).im ≤ h' := by
    have hre : Filter.Tendsto (fun t : ℝ => (germPt a h t).re) (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (-(1/2))) := by
      have hc := Complex.continuous_re.continuousAt.tendsto.comp hε₁tend
      have hlin : Complex.re (((-(1/2) : ℝ)) : ℂ) = -(1/2) := by norm_num
      rwa [hlin] at hc
    have him : Filter.Tendsto (fun t : ℝ => (germPt a h t).im) (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds 0) := by
      have hc := Complex.continuous_im.continuousAt.tendsto.comp hε₁tend
      have hlin : Complex.im (((-(1/2) : ℝ)) : ℂ) = 0 := by norm_num
      rwa [hlin] at hc
    have h1 : Filter.Tendsto (fun t : ℝ => (germPt a h t).re + 1 / 2)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hsum := hre.add (tendsto_const_nhds (x := (1/2 : ℝ)))
      simpa using hsum
    have hev1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), |(germPt a h t).re + 1 / 2| ≤ ρ' :=
      (Metric.tendsto_nhds.mp h1 ρ' hρ').mono fun t ht => by
        rw [Real.dist_eq, sub_zero] at ht
        exact le_of_lt ht
    have hev2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), (germPt a h t).im ≤ h' :=
      (Metric.tendsto_nhds.mp him h' hh'pos).mono fun t ht => by
        rw [Real.dist_eq, sub_zero] at ht
        exact le_of_lt (abs_lt.mp ht).2
    exact hev1.and hev2
  rw [eventually_nhdsWithin_iff] at hbox
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hbox
  refine ⟨min δ (min ε₁ ε₂), lt_min hδpos (lt_min hε₁pos hε₂pos), fun t ht0 ht => ?_⟩
  have htδ : t < δ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht1 : t < ε₁ := lt_of_lt_of_le ht (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht2 : t < ε₂ := lt_of_lt_of_le ht (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hbox1, hbox2⟩ : |(germPt a h t).re + 1 / 2| ≤ ρ' ∧ (germPt a h t).im ≤ h' :=
    hδ (by rw [Real.dist_eq, abs_lt]; exact ⟨by linarith, by linarith⟩)
      (by rw [Set.mem_Ioi]; exact ht0)
  refine ⟨hbox1, hbox2, ?_⟩
  -- the two-step iterates of the germ point
  have hstep2 : ∀ u : ℝ, 0 < u → u < ε₂ → (eqU a)^[2] (germPt a h u) =
      germPt a h ((eqLam a) ^ 2 * u) := by
    intro u hu0 huε
    have hlamu0 : 0 < eqLam a * u := mul_pos (eqLam_pos_hb ha0 ha1) hu0
    have hlamue : eqLam a * u < ε₂ :=
      lt_of_lt_of_le (mul_lt_of_lt_one_left hu0 (eqLam_lt_one_hb ha0 ha1)) huε.le
    rw [show (eqU a)^[2] (germPt a h u) = eqU a (eqU a (germPt a h u)) from rfl,
      hε₂eq u hu0 huε, hε₂eq (eqLam a * u) hlamu0 hlamue, pow_two]
    ring_nf
  have hiter : ∀ (u : ℝ), 0 < u → u < ε₂ → ∀ n : ℕ,
      (eqU a)^[2 * n] (germPt a h u) = germPt a h ((eqLam a) ^ (2 * n) * u) := by
    intro u hu0 huε n
    induction n generalizing u with
    | zero => simp
    | succ n ih =>
        have hle : (eqLam a) ^ 2 ≤ 1 := pow_le_one₀ (le_of_lt (eqLam_pos_hb ha0 ha1))
          (le_of_lt (eqLam_lt_one_hb ha0 ha1))
        have hu'0 : 0 < (eqLam a) ^ 2 * u := mul_pos (pow_pos (eqLam_pos_hb ha0 ha1) 2) hu0
        have hu'ε : (eqLam a) ^ 2 * u < ε₂ := by
          calc (eqLam a) ^ 2 * u ≤ 1 * u := mul_le_mul_of_nonneg_right hle hu0.le
            _ = u := one_mul u
            _ < ε₂ := huε
        rw [show 2 * (n + 1) = 2 * n + 2 by ring, Function.iterate_add_apply, hstep2 u hu0 huε,
          ih _ hu'0 hu'ε]
        rw [← mul_assoc, ← pow_add]
  have horb : ∀ n : ℕ, ofCoord (LocData.orb a ((germPt a h t).re + 1 / 2) (germPt a h t).im n)
      = germPt a h ((eqLam a) ^ (2 * n) * t) := by
    intro n
    rw [← orb_eqU (a := a) ((germPt a h t).re + 1 / 2, (germPt a h t).im) n, ofCoord_toCoord]
    exact hiter t ht0 ht2 n
  -- the parameter tends to `0` and the iterates to `A₁`
  have hlam : Filter.Tendsto (fun n : ℕ => (eqLam a) ^ (2 * n) * t) Filter.atTop (nhds 0) := by
    have h2 : (eqLam a) ^ 2 < 1 := by
      nlinarith [eqLam_pos_hb ha0 ha1, eqLam_lt_one_hb ha0 ha1]
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0:ℝ) ≤ (eqLam a)^2) h2
    simpa only [pow_mul, zero_mul] using hp.mul_const t
  have hgt : Filter.Tendsto ((germPt a h) ∘ fun n : ℕ => (eqLam a) ^ (2 * n) * t) Filter.atTop
      (nhds (((-(1/2) : ℝ)) : ℂ)) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (eqLam a) ^ (2 * n) * t) Filter.atTop
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlam, Eventually.of_forall fun n =>
        mul_pos (pow_pos (eqLam_pos_hb ha0 ha1) _) ht0⟩
    exact hε₁tend.comp h1
  have hX : |(germPt a h t).re + 1 / 2| ≤ 2 * d.ρ := by linarith [hbox1, hρ'ρ, d.ρpos]
  have hY0 : 0 < (germPt a h t).im := hε₁im t ht0 ht1
  have hYh : (germPt a h t).im ≤ d.h := le_trans hbox2 hh'h
  have hlim := LocData.chi_eq_lim d _ _ hX hY0 hYh
  have hX0 : Filter.Tendsto (fun n => (LocData.orb a ((germPt a h t).re + 1 / 2)
      (germPt a h t).im n).1) Filter.atTop (nhds 0) := by
    have hconv : Filter.Tendsto (fun n => ofCoord (LocData.orb a ((germPt a h t).re + 1 / 2)
        (germPt a h t).im n)) Filter.atTop (nhds (((-(1/2) : ℝ)) : ℂ)) := by
      have heq : (fun n => ofCoord (LocData.orb a ((germPt a h t).re + 1 / 2)
          (germPt a h t).im n)) = (germPt a h) ∘ fun n : ℕ => (eqLam a) ^ (2 * n) * t := by
        funext n
        rw [Function.comp_apply]
        exact horb n
      rw [heq]
      exact hgt
    have hlin : Complex.re (((-(1/2) : ℝ)) : ℂ) = -(1/2) := by norm_num
    have h1 : Filter.Tendsto (fun n => (ofCoord (LocData.orb a ((germPt a h t).re + 1 / 2)
        (germPt a h t).im n)).re) Filter.atTop (nhds (-(1/2))) := by
      have hc : Filter.Tendsto (fun n => (ofCoord (LocData.orb a ((germPt a h t).re + 1 / 2)
          (germPt a h t).im n)).re) Filter.atTop (nhds (Complex.re (((-(1/2) : ℝ)) : ℂ))) :=
        Complex.continuous_re.continuousAt.tendsto.comp hconv
      rwa [hlin] at hc
    have h2 := h1.add (tendsto_const_nhds (x := (1/2 : ℝ)))
    have hre : ∀ n, (ofCoord (LocData.orb a ((germPt a h t).re + 1 / 2)
        (germPt a h t).im n)).re + 1 / 2 =
        (LocData.orb a ((germPt a h t).re + 1 / 2) (germPt a h t).im n).1 := by
      intro n; rw [ofCoord_re]; ring
    simpa only [hre, neg_add_cancel] using h2
  exact tendsto_nhds_unique hlim hX0

/-! ### The level sets of `χ` are separated -/

theorem chi_sep (d : LocData a) {ρ' : ℝ} (hρ' : 0 < ρ') (hρ'ρ : 2 * ρ' ≤ d.ρ) :
    ∃ y₀ : ℝ, 0 < y₀ ∧ y₀ ≤ d.h ∧ ∀ x₁ x₂ y : ℝ, |x₁| ≤ ρ' → |x₂| ≤ ρ' → x₁ < x₂ →
      0 < y → y ≤ y₀ → LocData.chi a x₁ y < LocData.chi a x₂ y := by
  obtain ⟨y₁, hy₁pos, hy₁small⟩ := small_thresh d
  refine ⟨min y₁ d.h, lt_min hy₁pos d.hpos, min_le_right _ _, ?_⟩
  intro x₁ x₂ y h1 h2 hlt hy0 hy
  have hyh : y ≤ d.h := le_trans hy (min_le_right _ _)
  have hs : d.Small y := hy₁small y hy0 (le_trans hy (min_le_left _ _))
  have h1' : |x₁| ≤ 2 * d.ρ := by linarith [h1, hρ'ρ, d.ρpos]
  have h2' : |x₂| ≤ 2 * d.ρ := by linarith [h2, hρ'ρ, d.ρpos]
  have hsep : ∀ n, (LocData.orb a x₂ y n).1 - (LocData.orb a x₁ y n).1 ≥ (x₂ - x₁) / 2 :=
    orb_sep d h1' h2' (le_of_lt hlt) hy0 hyh hs
  have hl1 := LocData.chi_eq_lim d x₁ y h1' hy0 hyh
  have hl2 := LocData.chi_eq_lim d x₂ y h2' hy0 hyh
  have hdiff : Filter.Tendsto (fun n => (LocData.orb a x₂ y n).1 - (LocData.orb a x₁ y n).1)
      Filter.atTop (nhds (LocData.chi a x₂ y - LocData.chi a x₁ y)) := hl2.sub hl1
  have hge : (x₂ - x₁) / 2 ≤ LocData.chi a x₂ y - LocData.chi a x₁ y :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hdiff (Eventually.of_forall hsep)
  linarith

/-! ### The germ curve lies on the arc -/

theorem germPt_mem_arc {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) (hs₁ : ∀ θ, ρ₁ (-θ) = ρ₁ θ) (hs₂ : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ))
    {h : ℂ → ℂ} {r : ℝ} (hh : IsStableGerm a h r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t < ε → germPt a h t ∈ arcSet a ρ₁ := by
  obtain ⟨d⟩ := locData_nonempty ha0 ha1
  obtain ⟨hA1, -, -, -, hAxis, harcθ, htrich, hcover⟩ := arc_near_A1 ha0 ha1 hC hs₁ hs₂
  -- the working box
  set ρ' := min (d.ρ / 2) (1 / 8) with hρ'def
  have hρ'pos : 0 < ρ' := lt_min (by linarith [d.ρpos]) (by norm_num)
  have h2ρ'ρ : 2 * ρ' ≤ d.ρ := by
    rw [hρ'def]
    have := min_le_left (d.ρ / 2) (1 / 8)
    linarith
  have h2ρ'1 : 2 * ρ' < 1 := by
    rw [hρ'def]
    have := min_le_right (d.ρ / 2) (1 / 8)
    linarith
  have hρ'1 : ρ' < 1 := by linarith
  -- the separation threshold
  obtain ⟨y₀, hy₀pos, hy₀h, hy₀sep⟩ := chi_sep d hρ'pos h2ρ'ρ
  -- the covering threshold
  obtain ⟨β, hβpos, hβ⟩ := hcover ρ' hρ'pos hρ'1
  -- the working height
  set h' := min (min y₀ (min (β / 2) (Real.sqrt (ρ' * (1 - d.κ ^ 2) / d.C)))) d.h with hh'def
  have hh'pos : 0 < h' := by
    rw [hh'def]
    refine lt_min (lt_min hy₀pos (lt_min (by linarith [hβpos]) (Real.sqrt_pos.mpr ?_))) d.hpos
    exact div_pos (mul_pos hρ'pos d.one_sub_sq_pos) d.Cpos
  have hh'h : h' ≤ d.h := min_le_right _ _
  have hh'y₀ : h' ≤ y₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hh'β : h' ≤ β / 2 := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hh'drift : d.C * h' ^ 2 / (1 - d.κ ^ 2) ≤ ρ' := by
    have hsqrt : h' ≤ Real.sqrt (ρ' * (1 - d.κ ^ 2) / d.C) :=
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have h0 : 0 ≤ ρ' * (1 - d.κ ^ 2) / d.C :=
      (div_pos (mul_pos hρ'pos d.one_sub_sq_pos) d.Cpos).le
    have hsq : h' ^ 2 ≤ ρ' * (1 - d.κ ^ 2) / d.C := by
      calc h' ^ 2 ≤ (Real.sqrt (ρ' * (1 - d.κ ^ 2) / d.C)) ^ 2 :=
            pow_le_pow_left₀ hh'pos.le hsqrt 2
        _ = ρ' * (1 - d.κ ^ 2) / d.C := Real.sq_sqrt h0
    have h1k : 0 < 1 - d.κ ^ 2 := d.one_sub_sq_pos
    calc d.C * h' ^ 2 / (1 - d.κ ^ 2) ≤ d.C * (ρ' * (1 - d.κ ^ 2) / d.C) / (1 - d.κ ^ 2) := by
          apply div_le_div_of_nonneg_right _ h1k.le
          exact mul_le_mul_of_nonneg_left hsq d.Cpos.le
      _ = ρ' := by
          field_simp
          exact mul_inv_cancel₀ (ne_of_gt d.Cpos)
  -- the germ threshold
  obtain ⟨ε, hεpos, hε⟩ := germ_chi_zero ha0 ha1 hh d hρ'pos h2ρ'ρ hh'pos hh'h
  obtain ⟨εg, hεg, -, himg, -⟩ := germPt_basic ha0 ha1 hh
  refine ⟨min ε εg, lt_min hεpos hεg, fun t ht0 ht => ?_⟩
  have htε : t < ε := lt_of_lt_of_le ht (min_le_left _ _)
  have htg : t < εg := lt_of_lt_of_le ht (min_le_right _ _)
  obtain ⟨hbox1, hbox2, hχg⟩ := hε t ht0 htε
  set y := (germPt a h t).im with hydef
  have hy0 : 0 < y := by
    rw [hydef]
    exact himg t ht0 htg
  have hyh' : y ≤ h' := by rw [hydef]; exact hbox2
  have hyy₀ : y ≤ y₀ := le_trans hyh' hh'y₀
  have hyβ : y < β := by
    have hle : y ≤ β / 2 := le_trans hyh' hh'β
    linarith [hβpos]
  obtain ⟨θ, hθ0, hθπ, hθim, hθre⟩ := hβ y hy0 hyβ
  have hθre' : |(arcPt a ρ₁ θ).re + 1 / 2| ≤ ρ' := by simpa [arcPt] using hθre
  have hχz : LocData.chi a ((arcPt a ρ₁ θ).re + 1 / 2) ((arcPt a ρ₁ θ).im) = 0 := by
    refine arc_chi_zero ha0 ha1 hC hs₁ hs₂ d hρ'pos h2ρ'ρ h2ρ'1 hh'h hh'drift ⟨θ, rfl⟩ ?_ hθre' ?_
    · rw [arcPt, hθim]; exact hy0
    · rw [arcPt, hθim]; exact hyh'
  have hχg' : LocData.chi a ((germPt a h t).re + 1 / 2) y = 0 := by
    rw [hydef]; exact hχg
  have hχz' : LocData.chi a ((arcPt a ρ₁ θ).re + 1 / 2) y = 0 := by
    rw [← hθim]; exact hχz
  have hxeq : (germPt a h t).re + 1 / 2 = (arcPt a ρ₁ θ).re + 1 / 2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h := hy₀sep _ _ y hbox1 hθre' hlt hy0 hyy₀
      rw [hχg', hχz'] at h
      exact absurd h (lt_irrefl 0)
    · have h := hy₀sep _ _ y hθre' hbox1 hlt hy0 hyy₀
      rw [hχg', hχz'] at h
      exact absurd h (lt_irrefl 0)
  refine ⟨θ, ?_⟩
  apply Complex.ext
  · simpa [arcPt] using hxeq.symm
  · simp [arcPt, hθim, hydef]

end

end Work.EQ
