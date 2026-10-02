/-
Copyright: subproject `Submission/Work/FatouDeg/` of `mandelbar_not_path_connected`.

# The degenerate case of Fatou's theorem: the assembly

This file proves `Work.FatouParabolic2.FatouParabolicInput_degenerate` — Fatou's theorem on
parabolic cycles when the second derivative of the germ vanishes (the multi-petal / cusp case) —
from two ingredients:

* the petal + Fatou coordinate for the normal form `z ↦ z - z^m + z^(m+1) G z` at every exponent
  `m ≥ 3`, which is `Work.FatouDeg.Petal.fatouCoordSec3` (the port of the `MultiPetal` theory with
  `4 ≤ m` weakened to `3 ≤ m`);
* the Liouville/covering step `Work.MultiPetal.criticalOrbitInPetalNoPre`, which needs no exponent
  hypothesis at all.

The normalisation of the germ at the parabolic fixed point (`normalizeDeg`, the exponent-`3`
analogue of `Work.MultiPetal.normalizeParabolic`) enters as the hypothesis `NormalFormInput`, so
that the assembly here is independent of the proof of the normal form; the final theorem
`Work.FatouDeg.fatouParabolicInput_degenerate` applies it to `Work.FatouDeg.normalizeDeg`.
-/
import Mathlib
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouDeg.NormForm
import Submission.Work.FatouDeg.Petal.All
import Submission.Work.MultiPetal.criticalOrbitInPetalNoPre

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Filter
open scoped Topology

namespace Work.FatouDeg

noncomputable section

/-- **The normal-form input.**  The exact statement proved by `Work.FatouDeg.normalizeDeg`: at a
parabolic fixed point of a polynomial map of degree `≥ 2` whose second derivative vanishes, the
germ is, in a chart `z = z₀ + c w`, of the normal form `w ↦ w - w^m + w^(m+1) G(w)` with
`m ≥ 3`. -/
def NormalFormInput : Prop :=
  ∀ (F : ℂ → ℂ) (z₀ : ℂ), Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F →
    F z₀ = z₀ → deriv F z₀ = 1 → iteratedDeriv 2 F z₀ = 0 →
    ∃ (m : ℕ) (c : ℂ) (G : Polynomial ℂ), 3 ≤ m ∧ c ≠ 0 ∧
      ∀ w : ℂ, F (z₀ + c * w) = z₀ + c * (Polynomial.X - Polynomial.X ^ m
        + Polynomial.X ^ (m + 1) * G).eval w

/-- **The degenerate case of Fatou's theorem**, from the normal-form input.

Given a polynomial map `F` of degree `≥ 2` with a fixed point `z₀` of multiplier `1` at which the
second derivative vanishes, `normalizeDeg` conjugates `F` to `N = N_{m,G}` on the chart
`w ↦ z₀ + c w` with `m ≥ 3`.  The petal `Pa` of `N` (with its Fatou coordinate) and the
Liouville step `criticalOrbitInPetalNoPre` produce a critical point `w` of `N` whose orbit enters
`Pa`; pulling back along the chart gives a critical point `z₀ + c w` of `F` in the basin of `z₀`.

The critical point is a critical point of `F` by the chain rule applied to
`F (z₀ + c u) = z₀ + c N u`, and the basin is by the same identity iterated,
`F^[n] (z₀ + c u) = z₀ + c N^[n] u`, together with `N^[n] (N^[K] w) → 0` and
`Filter.tendsto_add_atTop_iff_nat`. -/
theorem fatouParabolicInput_degenerate_of (hnorm : NormalFormInput) :
    Work.FatouParabolic2.FatouParabolicInput_degenerate := by
  intro F z₀ hF hfix h1 h2
  obtain ⟨m, c, G, hm, hc, hconj⟩ := hnorm F z₀ hF hfix h1 h2
  set N : ℂ → ℂ := nf m G with hNdef
  -- the petal of the normal form, at `δ = 1`
  obtain ⟨Pa, φa, hPaopen, hPane, _hPaball, _hPa0, _hPasect, hPamap, hPatend, hPdiff, hPainj,
    hPaabel, hPastrip⟩ := Petal.fatouCoordSec3 m hm G one_pos
  -- the Liouville/covering step: a critical point of `N` whose orbit enters the petal
  obtain ⟨w, hwcrit, K, hK⟩ :=
    Work.MultiPetal.criticalOrbitInPetalNoPre (nf m G) (nf_isPoly m hm G) (nf_zero m hm G)
      (nf_deriv_zero m hm G) Pa φa hPaopen hPane hPamap hPatend hPdiff hPainj hPaabel hPastrip
  have hconj' : ∀ u : ℂ, F (z₀ + c * u) = z₀ + c * N u := fun u => hconj u
  refine ⟨z₀ + c * w, ?_, ?_⟩
  · -- the chain rule: `deriv F (z₀ + c w) = deriv N w = 0`
    have hFd : DifferentiableAt ℂ F (z₀ + c * w) :=
      (Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF) (z₀ + c * w)
    have hNd : DifferentiableAt ℂ N w :=
      (Work.FatouParabolic.Poly.isPolynomialMap_differentiable (nf_isPoly m hm G)) w
    have hin : HasDerivAt (fun u : ℂ => z₀ + c * u) c w :=
      (hasDerivAt_const_mul (x := w) c).const_add z₀
    have hd1 : deriv (fun u : ℂ => F (z₀ + c * u)) w = deriv F (z₀ + c * w) * c :=
      (hFd.hasDerivAt.comp w hin).deriv
    have hd2 : deriv (fun u : ℂ => z₀ + c * N u) w = c * deriv N w :=
      (((hNd.hasDerivAt.const_mul c).const_add z₀)).deriv
    have hfun : (fun u : ℂ => F (z₀ + c * u)) = fun u : ℂ => z₀ + c * N u := funext hconj'
    have hEq : deriv F (z₀ + c * w) * c = 0 := by
      have : deriv F (z₀ + c * w) * c = c * deriv N w := by
        rw [← hd1, hfun, hd2]
      rw [this, hwcrit, mul_zero]
    exact (mul_eq_zero.mp hEq).resolve_right hc
  · -- the basin: `F^[n] (z₀ + c w) = z₀ + c N^[n] w` and `N^[n] w → 0`
    have hiter : ∀ n : ℕ, (F^[n]) (z₀ + c * w) = z₀ + c * (N^[n]) w := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        exact hconj' _
    have hNtend : Tendsto (fun n : ℕ => (N^[n]) w) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (N^[n]) ((N^[K]) w)) atTop (𝓝 0) := hPatend _ hK
      have h2 : (fun n : ℕ => (N^[n]) ((N^[K]) w)) = fun n : ℕ => (N^[n + K]) w := by
        funext n
        exact (Function.iterate_add_apply N n K w).symm
      rw [h2] at h1
      exact (Filter.tendsto_add_atTop_iff_nat K).mp h1
    have h3 : Tendsto (fun n : ℕ => z₀ + c * (N^[n]) w) atTop (𝓝 (z₀ + c * 0)) :=
      (hNtend.const_mul c).const_add z₀
    rw [mul_zero, add_zero] at h3
    show Tendsto (fun n : ℕ => (F^[n]) (z₀ + c * w)) atTop (𝓝 z₀)
    exact h3.congr' (Filter.Eventually.of_forall fun n => (hiter n).symm)

end

end Work.FatouDeg
