import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.BusemannRay
import Submission.Work.Mostow.levYcFormula

/-!
# The "deep cusp" lemma

If an isometry `g` of `ℍⁿ` fixes a boundary point `ξ ∈ Sph n` (`bd g ξ = ξ`) and preserves the
Busemann function of `ξ` (`busemann ξ (g • u) = busemann ξ u`), then `g` has arbitrarily small
displacement: `∀ ε > 0, ∃ u, hdist u (g • u) < ε`.  Equivalently its translation length vanishes —
the hypothesis says precisely that `g` preserves every horosphere at `ξ`, so pushing a point far
out along the ray to `ξ` makes `g` move it by an arbitrarily small amount (this is the behaviour of
a parabolic element, or of an isometry with a fixed point).

## Proof

Work in the horospherical coordinates at `ξ`: the *level* `lev ξ u = tpart u - ⟪u,ξ⟫ = exp (busemann ξ u)`
and the *normalised flat coordinate* `yc ξ u = (lev ξ u)⁻¹ (u - ⟪u,ξ⟫ • ξ)`.  The classical formula
`Work.Mostow.levYcFormula` expresses the hyperbolic distance in these coordinates:

`cosh (hdist u v) = cosh (log (lev ξ u / lev ξ v)) + (lev ξ u * lev ξ v / 2) * ‖yc ξ u - yc ξ v‖²`.

Let `u_t = hray ξ t = sinh t • ξ` be the point at distance `t` on the ray from `0` to `ξ`.  Then
`lev ξ u_t = exp (-t)` and `yc ξ u_t = 0`, while `busemann ξ (g • 0) = 0` (so `lev ξ (g • 0) = 1`)
because the Busemann cocycle of `g` at `ξ` is `busemann ξ (g • 0)` and `hpres` forces it to vanish.

*Applying the formula to the pair `(g • 0, g • u_t)`* — where `hdist (g • 0) (g • u_t) = hdist 0 u_t = t`
and `log (lev ξ (g • 0) / lev ξ (g • u_t)) = t` — shows that the flat-coordinate term vanishes, i.e.
`yc ξ (g • u_t) = yc ξ (g • 0)`, a constant independent of `t`.

*Applying it to the pair `(u_t, g • u_t)`* then gives

`cosh (hdist u_t (g • u_t)) = 1 + (exp (-2t) / 2) * ‖yc ξ (g • 0)‖²`,

whose right-hand side tends to `1` as `t → ∞`; hence `hdist u_t (g • u_t) → 0`.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory

theorem deepCusp (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n) (hg : bd g ξ = ξ)
    (hpres : ∀ u : E n, busemann ξ (g • u) = busemann ξ u) :
    ∀ ε > 0, ∃ u : E n, hdist u (g • u) < ε := by
  intro ε hε
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  -- the level and flat coordinate of the point of the ray to `ξ`
  have hraylev : ∀ t : ℝ, lev ξ (hray ξ t) = Real.exp (-t) := fun t => by
    rw [hray, lev, tpart_sinh_smul ξ t hξn, real_inner_smul_left, real_inner_self_eq_norm_sq, hξn]
    norm_num
  have hrayyc : ∀ t : ℝ, yc ξ (hray ξ t) = 0 := fun t => by
    rw [yc, wc, hray, real_inner_smul_left, real_inner_self_eq_norm_sq, hξn]
    norm_num
  -- `g` preserves the level
  have hlevpres : ∀ u : E n, lev ξ (g • u) = lev ξ u := fun u => by
    rw [lev_eq_exp hξ (g • u), lev_eq_exp hξ u, hpres u]
  -- the Busemann cocycle of `g` at `ξ` vanishes, so `lev ξ (g • 0) = 1`
  have hbus0 : busemann ξ (g • 0) = 0 := by
    have hbus := hId.busemann_cocycle g ξ (0 : E n) hξ
    rw [hg] at hbus
    have hp := hpres (0 : E n)
    linarith
  have hlev0 : lev ξ (g • 0) = 1 := by
    rw [lev_eq_exp hξ (g • 0), hbus0, Real.exp_zero]
  -- `hdist 0 (hray ξ t) = t` for `t ≥ 0`
  have hdist0 : ∀ t : ℝ, 0 ≤ t → hdist 0 (hray ξ t) = t := fun t ht => by
    have h : Real.cosh (hdist 0 (hray ξ t)) = Real.cosh t := by
      rw [cosh_hdist_zero, hray, tpart_sinh_smul ξ t hξn]
    have h2 := congrArg Real.arcosh h
    rwa [Real.arcosh_cosh (hdist_nonneg 0 _), Real.arcosh_cosh ht] at h2
  -- the flat coordinate of `g • hray ξ t` is the constant `yc ξ (g • 0)`
  have hyckey : ∀ t : ℝ, 0 ≤ t → yc ξ (g • hray ξ t) = yc ξ (g • 0) := fun t ht => by
    have hf := levYcFormula hξ (g • 0) (g • hray ξ t)
    have hd : hdist (g • 0) (g • hray ξ t) = t := by
      rw [hId.isom_smul g 0 (hray ξ t)]; exact hdist0 t ht
    rw [hd, hlev0, hlevpres (hray ξ t), hraylev t] at hf
    have hlog : Real.log (1 / Real.exp (-t)) = t := by
      rw [one_div, Real.exp_neg, inv_inv, Real.log_exp]
    rw [hlog] at hf
    have hz : (Real.exp (-t) / 2) * ‖yc ξ (g • 0) - yc ξ (g • hray ξ t)‖ ^ 2 = 0 := by
      linarith
    have hpos : Real.exp (-t) / 2 ≠ 0 := by positivity
    have hnn : ‖yc ξ (g • 0) - yc ξ (g • hray ξ t)‖ = 0 := by
      have h2 : ‖yc ξ (g • 0) - yc ξ (g • hray ξ t)‖ ^ 2 = 0 :=
        (mul_eq_zero.mp hz).resolve_left hpos
      nlinarith [norm_nonneg (yc ξ (g • 0) - yc ξ (g • hray ξ t)), h2]
    have hsub : yc ξ (g • 0) - yc ξ (g • hray ξ t) = 0 := by
      rwa [norm_eq_zero] at hnn
    exact (sub_eq_zero.mp hsub).symm
  -- the exact hyperbolic-cosine identity along the ray
  have hmain : ∀ t : ℝ, 0 ≤ t →
      Real.cosh (hdist (hray ξ t) (g • hray ξ t)) =
        1 + (Real.exp (-(2*t))/2) * ‖yc ξ (g • 0)‖^2 := fun t ht => by
    have hf := levYcFormula hξ (hray ξ t) (g • hray ξ t)
    rw [hraylev t, hlevpres (hray ξ t), hraylev t, hrayyc t, hyckey t ht] at hf
    rw [div_self (Real.exp_ne_zero (-t)), Real.log_one, Real.cosh_zero] at hf
    rw [show Real.exp (-t) * Real.exp (-t) = Real.exp (-(2*t)) by
      rw [← Real.exp_add]; congr 1; ring] at hf
    rw [zero_sub, norm_neg] at hf
    linarith [hf]
  -- conclude: `hdist (hray ξ t) (g • hray ξ t) → 0`
  set c : ℝ := ‖yc ξ (g • 0)‖^2 with hc
  set D : ℝ := Real.cosh ε - 1 with hD
  have hDpos : 0 < D := by
    rw [hD]
    have := Real.one_lt_cosh.mpr (ne_of_gt hε)
    linarith
  have hlim : Filter.Tendsto (fun t : ℝ => Real.exp (-(2*t))) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun t : ℝ => (2:ℝ)*t) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop (by norm_num)
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h2
  have hbase : Filter.Tendsto (fun t : ℝ => (c/2) * Real.exp (-(2*t))) Filter.atTop (nhds 0) := by
    simpa using hlim.const_mul (c/2)
  have hlim2 : Filter.Tendsto (fun t : ℝ => (Real.exp (-(2*t))/2) * c) Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr (fun t => by ring) hbase
  have hev : ∀ᶠ t : ℝ in Filter.atTop, (Real.exp (-(2*t))/2) * c < D :=
    hlim2.eventually (Iio_mem_nhds hDpos)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
  refine ⟨hray ξ (max T 0), ?_⟩
  have ht0 : 0 ≤ max T 0 := le_max_right _ _
  have hTD : (Real.exp (-(2*(max T 0)))/2) * c < D := hT (max T 0) (le_max_left _ _)
  have hcosh : Real.cosh (hdist (hray ξ (max T 0)) (g • hray ξ (max T 0))) < Real.cosh ε := by
    rw [hmain (max T 0) ht0]
    rw [hD] at hTD
    linarith
  have habs := Real.cosh_lt_cosh.mp hcosh
  rwa [abs_of_nonneg (hdist_nonneg _ _), abs_of_pos hε] at habs

end Work.Mostow
