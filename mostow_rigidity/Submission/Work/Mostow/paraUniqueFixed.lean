import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.BusemannLipschitz
import Submission.Work.Mostow.levMid

/-!
# Unique fixed boundary point of a parabolic isometry

A parabolic isometry `g` of `ℍⁿ` (no fixed point in `ℍⁿ`, infimal displacement `0`) fixes
**at most one** point of the boundary sphere `Sph n`.

The proof is the horospherical one.  Suppose `ξ ≠ η` are both fixed by `g`.

* Since `g` is parabolic and fixes `ξ`, the Busemann cocycle of `g` at `ξ` vanishes
  (`levFixOfParabolic` below): `busemann ξ (g • u) = busemann ξ u` for all `u`, i.e. `g`
  preserves the level function `lev ξ`.  The same holds for `η`.
* The point `p = (√(2(1-⟪ξ,η⟫)))⁻¹ • (ξ + η)` is the *unique* point of `ℍⁿ` whose two levels at
  `ξ` and `η` both equal `D = √((1-⟪ξ,η⟫)/2)` (`levPairUnique_aux`): the two horospheres at `ξ`
  and `η` of common level `D` meet tangentially, at the midpoint of the geodesic from `ξ` to `η`
  (`levMid` records that `p` does lie on them).
* Hence `g • p` again has both levels equal to `D`, so `g • p = p` — a fixed point of `g` in
  `ℍⁿ`, contradicting parabolicity.

The uniqueness computation is the Cauchy–Schwarz argument: summing the two level equations gives
`⟪u, ξ+η⟫ = 2 (tpart u - D)`, and Cauchy–Schwarz together with `‖ξ+η‖² = 2(1+⟪ξ,η⟫)` and
`‖u‖² = tpart u² - 1` forces `(D · tpart u - 1)² ≤ 0`.
-/

set_option maxHeartbeats 2000000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-- A parabolic element `g` with `bd g ξ = ξ` preserves every horosphere at `ξ`: it preserves
the Busemann level `lev ξ`.  (Bundled-hypothesis form of `Work.Mostow.bCocy_parabolic`.)

Indeed, by the Busemann cocycle, `busemann ξ (g • u) = busemann ξ u + busemann ξ (g • 0)` for
every `u`; if the additive constant `busemann ξ (g • 0)` were non-zero, `BusemannLipschitz`
would bound its absolute value by `hdist (g • u) u` for *every* `u`, contradicting the existence
of points with arbitrarily small displacement. -/
theorem levFixOfParabolic (hI : HypIsoData n) {g : PO n 1} (hg : IsParabolic g)
    {ξ : E n} (hξ : ξ ∈ Sph n) (hfix : bd g ξ = ξ) :
    ∀ u : E n, lev ξ (g • u) = lev ξ u := by
  have hcoc : ∀ v : E n, busemann ξ (g • v) = busemann ξ v + busemann ξ (g • (0 : E n)) := by
    intro v
    have h := hI.busemann_cocycle g ξ v hξ
    rwa [hfix] at h
  have hs : busemann ξ (g • (0 : E n)) = 0 := by
    by_contra hne
    have hpos : 0 < |busemann ξ (g • (0 : E n))| := abs_pos.mpr hne
    obtain ⟨v, hv⟩ := hg.2 _ hpos
    have h1 : |busemann ξ (g • v) - busemann ξ v| ≤ hdist (g • v) v :=
      BusemannLipschitz n ξ hξ (g • v) v
    rw [hcoc v, add_sub_cancel_left] at h1
    rw [hI.symm] at h1
    linarith
  intro u
  have h := hcoc u
  rw [lev_eq_exp hξ (g • u), lev_eq_exp hξ u, h, hs, add_zero]

/-- **Uniqueness of the horospherical midpoint.**  If `u` has the same Busemann level
`D = √((1-⟪ξ,η⟫)/2)` at two distinct boundary points `ξ ≠ η`, then `u` is the point
`(√(2(1-⟪ξ,η⟫)))⁻¹ • (ξ+η)`. -/
theorem levPairUnique_aux {ξ η u : E n}
    (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hne : ξ ≠ η)
    (h1 : lev ξ u = Real.sqrt ((1 - inner ℝ ξ η) / 2))
    (h2 : lev η u = Real.sqrt ((1 - inner ℝ ξ η) / 2)) :
    u = (Real.sqrt (2 * (1 - inner ℝ ξ η)))⁻¹ • (ξ + η) := by
  have hξn : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have hηn : ‖η‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hη
  have hβlt : inner ℝ ξ η < 1 := (inner_lt_one_iff_real_of_norm_eq_one hξn hηn).mpr hne
  set D : ℝ := Real.sqrt ((1 - inner ℝ ξ η) / 2) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by linarith)
  have hDsq : D ^ 2 = (1 - inner ℝ ξ η) / 2 := by
    rw [hDdef, Real.sq_sqrt (by linarith)]
  set t : ℝ := tpart u with htdef
  have h1' : inner ℝ u ξ = t - D := by
    have hh : tpart u - inner ℝ u ξ = D := h1
    rw [← htdef] at hh; linarith
  have h2' : inner ℝ u η = t - D := by
    have hh : tpart u - inner ℝ u η = D := h2
    rw [← htdef] at hh; linarith
  have hsig : inner ℝ u (ξ + η) = 2 * (t - D) := by
    rw [inner_add_right, h1', h2']; ring
  have hσnorm : ‖ξ + η‖ ^ 2 = 2 * (1 + inner ℝ ξ η) := by
    rw [norm_add_sq_real, hξn, hηn]; ring
  have hnormu : ‖u‖ ^ 2 = t ^ 2 - 1 := by
    have hh : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := by
      simp only [tpart]; rw [Real.sq_sqrt (by positivity)]
    rw [← htdef] at hh; linarith
  have hsq : (inner ℝ u (ξ + η))^2 ≤ ‖u‖^2 * ‖ξ+η‖^2 := by
    have hb : |inner ℝ u (ξ + η)| ≤ ‖u‖ * ‖ξ+η‖ := abs_real_inner_le_norm u (ξ + η)
    have h := mul_self_le_mul_self (abs_nonneg _) hb
    rw [← sq, ← sq, mul_pow, sq_abs] at h
    exact h
  have e1 : (inner ℝ u (ξ + η))^2 = 4*(t-D)^2 := by rw [hsig]; ring
  have e2 : ‖u‖^2 * ‖ξ+η‖^2 = (t^2-1) * (2*(1+inner ℝ ξ η)) := by rw [hnormu, hσnorm]
  have h2a : 4*(t-D)^2 ≤ (t^2-1) * (2*(1+inner ℝ ξ η)) := by rw [← e1, ← e2]; exact hsq
  have hkey : 4 * (D * t - 1)^2 ≤ 0 := by
    have h4 : 1 - inner ℝ ξ η = 2 * D^2 := by linarith [hDsq]
    nlinarith [h2a, h4, hDsq]
  have hDt : D * t = 1 := by
    have hnn : 0 ≤ (D*t-1)^2 := sq_nonneg _
    nlinarith [hkey, hnn]
  have hDσ : D * inner ℝ u (ξ + η) = 1 + inner ℝ ξ η := by
    rw [hsig]; nlinarith [hDt, hDsq]
  have hD2u : D^2 * ‖u‖^2 = (1 + inner ℝ ξ η)/2 := by
    rw [hnormu]; nlinarith [hDt, hDsq]
  have h2D : 2 * D = Real.sqrt (2 * (1 - inner ℝ ξ η)) := by
    have h2Dnn : 0 ≤ 2*D := by positivity
    have hsq2 : (2*D)^2 = 2*(1 - inner ℝ ξ η) := by rw [mul_pow, hDsq]; ring
    rw [← hsq2, Real.sqrt_sq h2Dnn]
  set c₀ : ℝ := (Real.sqrt (2 * (1 - inner ℝ ξ η)))⁻¹ with hc₀def
  have hc₀ : c₀ = (2*D)⁻¹ := by rw [hc₀def, ← h2D]
  have hc0pos : 0 < c₀ := by rw [hc₀]; positivity
  have hc0a : (2*D) * c₀ = 1 := by
    rw [hc₀]; exact mul_inv_cancel₀ (by positivity : (2*D) ≠ 0)
  have hc0b : (2*D)^2 * c₀^2 = 1 := by
    rw [← mul_pow (2*D) c₀ 2, hc0a, one_pow]
  have hc0c : (2*D)^2 * c₀ = 2*D := by
    rw [sq, mul_assoc, hc0a, mul_one]
  have hns : ‖c₀ • (ξ+η)‖^2 = c₀^2 * ‖ξ+η‖^2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0pos, mul_pow]
  have hexp : ‖u - c₀ • (ξ+η)‖^2
      = ‖u‖^2 - 2*(c₀ * inner ℝ u (ξ+η)) + c₀^2 * ‖ξ+η‖^2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, hns]
  have hA : (2*D)^2 * ‖u‖^2 = 2*(1 + inner ℝ ξ η) := by nlinarith [hD2u]
  have hB : (2*D)^2 * (c₀ * inner ℝ u (ξ+η)) = 2*(1 + inner ℝ ξ η) := by
    nlinarith [hc0c, hDσ]
  have hC : (2*D)^2 * (c₀^2 * ‖ξ+η‖^2) = 2*(1 + inner ℝ ξ η) := by
    nlinarith [hc0b, hσnorm]
  have key : (2*D)^2 * ‖u - c₀ • (ξ + η)‖^2 = 0 := by
    rw [hexp]
    nlinarith [hA, hB, hC]
  have hzero : ‖u - c₀ • (ξ + η)‖^2 = 0 := by
    have h4 : (2*D)^2 ≠ 0 := by positivity
    exact (mul_eq_zero.mp key).resolve_left h4
  have hz : ‖u - c₀ • (ξ + η)‖ = 0 := by
    have h := hzero; rw [sq] at h; exact mul_self_eq_zero.mp h
  exact sub_eq_zero.mp (by rw [← norm_eq_zero]; exact hz)

/-- **Uniqueness of the fixed boundary point of a parabolic isometry.** -/
theorem paraUniqueFixed {n : ℕ} (hA : Work.Mostow.POBasic n) (hI : Work.Mostow.HypIsoData n)
    {g : LeanEval.Geometry.MostowRigidity.PO n 1} (hg : Submission.Mostow.IsParabolic g)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hfix : Submission.Mostow.bd g ξ = ξ)
    {η : Submission.Mostow.E n} (hη : η ∈ Submission.Mostow.Sph n)
    (hfixη : Submission.Mostow.bd g η = η) : η = ξ := by
  by_contra hne
  have hne' : ξ ≠ η := fun h => hne h.symm
  have hlevξ := levFixOfParabolic hI hg hξ hfix
  have hlevη := levFixOfParabolic hI hg hη hfixη
  have hmid := levMid hξ hη hne'
  have hfixp : g • ((Real.sqrt (2 * (1 - inner ℝ ξ η)))⁻¹ • (ξ + η)) =
      (Real.sqrt (2 * (1 - inner ℝ ξ η)))⁻¹ • (ξ + η) := by
    refine levPairUnique_aux hξ hη hne' ?_ ?_
    · rw [hlevξ, hmid.1]
    · rw [hlevη, hmid.2]
  exact hg.1 _ hfixp

end Work.Mostow
