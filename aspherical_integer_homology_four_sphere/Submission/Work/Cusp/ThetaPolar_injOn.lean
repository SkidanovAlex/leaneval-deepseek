/-
# Injectivity of the polar chart `Θ_v` on the wedges

`ThetaPolar v p y = (r, θ, w₁, w₂)` is the inner (polar) chart of the `v`-th cusp
(`Work.Cusp.Basic`), a map `E2 × E2 → E4` on the cover `(p, y)` of the filling piece `W_v`:

* `r = radial v p y` is the metric radial coordinate (`2 r_J ‖p‖∞` in the core,
  `R₀ − log (collarHeight ‖p‖∞ (β (u p σ_v + y)))` in the collar),
* `θ = thetaAng v p y = 2π u(p) + 2π⟪y₂λ₂ + y₃λ₃, σ_v⟫/‖σ_v‖²` is the angle,
* `w = wOf v y = (⟪y₂λ₂+y₃λ₃, e₂⟫, ⟪y₂λ₂+y₃λ₃, e₃⟫)` is linear in the torus coordinate `y`.

This file proves that `Θ_v` is **injective** on `{z | z.1 ∈ wedge k}`, the union of the four open
wedges of directions of the filling square.  The proof is a recovery of `(p, y)` from the four
coordinates, in four independent steps:

* **`w` recovers `y`.**  `wOf v` is the matrix `G = (⟪λ_i, e_j⟫)` and `invY v` is its inverse
  (`invY_wOf`), so `wOf v` is injective (`wOf_injective`).
* **`θ` recovers `u(p)`.**  With `y` known, `θ = 2π u(p) + const` and `2π ≠ 0`
  (`u_eq_of_thetaAng_eq`).
* **`r` recovers `‖p‖∞`.**  With `y` and `u(p)` known the ceiling `b = β(u(p)σ_v + y)` is fixed, and
  the profile
  `t ↦ if t ≤ 1/2 then 2 r_J t else R₀ − log (collarHeight t b)`
  is strictly increasing on `(0,∞)`: it is the increasing linear map `2 r_J t` (value `≤ r_J = 3`)
  up to the junction `t = 1/2`, and `R₀ − log (collarHeight t b)` above it, which is strictly
  increasing because `t ↦ collarHeight t b` is strictly decreasing for `b < s_J` and equals `s_J`
  at `t = 1/2` (so that its values above the junction are `> r_J`).  Here `0 < β ≤ 3/2 < s_J`
  (`beta_pos`, `beta_le_max`, `betaMax_lt_sJ`).
* **`(‖p‖∞, u(p))` recovers `p`.**  `p = ‖p‖∞ • bnd p` (`smul_bnd`) and `u(p) = uPerim (bnd p)`
  is a coordinate on `∂Sq` (`nrmu_uPerim_injOn`); this needs only `‖p‖∞ ≠ 0` — the wedge hypothesis
  `wedge k = {p | 0 < ‖p‖∞ ∧ u(p) ∈ (k/4,(k+1)/4)}` supplies exactly that.

The wedge hypothesis is used only through `0 < nrm p`; the argument therefore proves the stronger
statement `Set.InjOn (fun z => ThetaPolar v z.1 z.2) {z | 0 < nrm z.1}` as an intermediate step.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.invY_wOf
import Submission.Work.Cusp.nrm_u_injOn
import Submission.Work.Cusp.radial_eq_inner
import Submission.Work.Cusp.radial_collar
import Submission.Work.Cusp.collarHeight_half
import Submission.Work.Cusp.collarHeight_pos
import Submission.Work.Cusp.collarHeight_strictAntiOn
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-! ### The four recovery steps -/

/-- **The radial coordinate of the polar chart, with the ceiling made explicit.**  The two branches
of `radial` are `2 r_J ‖p‖∞` in the inner region `‖p‖∞ ≤ 1/2` and `R₀ − log s` in the collar, where
the UHS height `s = collarS v p y` is by definition
`collarHeight ‖p‖∞ (β (cuspX v (u p) y))`.  This is the form in which the radial coordinate is seen
to determine `‖p‖∞` once `u(p)` and `y` are known. -/
theorem radial_eq_ite (v : Fin 5) (p y : E2) :
    radial v p y = if nrm p ≤ 1/2 then 2 * rJ * nrm p
      else R0 - Real.log (collarHeight (nrm p) (beta (cuspX v (u p) y))) := by
  rw [radial]
  split_ifs <;> rfl

/-- **`wOf v` is injective**: it is the invertible matrix `G = (⟪λ_i, e_j⟫)` of the change from the
torus coordinates `y = (y₂,y₃)` to the orthonormal `σ_v^⊥`-coordinates `w`, with inverse `invY v`
(`invY_wOf`). -/
theorem wOf_injective (v : Fin 5) : Function.Injective (wOf v) := by
  intro y1 y2 h
  rw [← invY_wOf v y1, h, invY_wOf v y2]

/-- **The angle coordinate recovers the perimeter parameter.**  If `thetaAng v p1 y1 =
thetaAng v p2 y2` and `y1 = y2` then `u p1 = u p2`: the phase correction
`2π⟪cuspY v y, σ_v⟫/‖σ_v‖²` is the same on both sides and `2π ≠ 0`. -/
theorem u_eq_of_thetaAng_eq {v : Fin 5} {p1 p2 y1 y2 : E2} (hy : y1 = y2)
    (h : thetaAng v p1 y1 = thetaAng v p2 y2) : u p1 = u p2 := by
  rw [thetaAng, thetaAng] at h
  rw [hy] at h
  have h' : 2 * π * u p1 = 2 * π * u p2 := add_right_cancel h
  exact mul_left_cancel₀ (by positivity : (2 : ℝ) * π ≠ 0) h'

/-- **The radial profile is strictly increasing in the layer parameter.**  For a ceiling
`b ∈ (0, s_J)` the piecewise function
`t ↦ if t ≤ 1/2 then 2 r_J t else R₀ − log (collarHeight t b)`
is injective on `ℝ`.

* below the junction it is the linear map `2 r_J t`, with values `< 2 r_J · (1/2) = r_J = 3`
  (strictly below at `t < 1/2`, and exactly `r_J` at the junction);
* above the junction `t ↦ collarHeight t b` is strictly decreasing with
  `collarHeight (1/2) b = s_J`, hence `log (collarHeight t b) < log s_J = 1/2` and
  `R₀ − log (collarHeight t b) > R₀ − 1/2 = r_J`;
* consequently the two branches cannot agree on opposite sides of the junction, and on each
  side separately the function is strictly increasing (the logarithm and `collarHeight` being
  injective). -/
theorem radialProfile_injOn {b t1 t2 : ℝ} (hb : 0 < b) (hb' : b < sJ)
    (h : (if t1 ≤ 1/2 then 2 * rJ * t1 else R0 - Real.log (collarHeight t1 b))
       = (if t2 ≤ 1/2 then 2 * rJ * t2 else R0 - Real.log (collarHeight t2 b))) :
    t1 = t2 := by
  have hrJ : 0 < rJ := by norm_num [rJ]
  have hR0 : R0 - 1/2 = rJ := by norm_num [R0, rJ]
  have hhalf : collarHeight (1/2) b = sJ := collarHeight_half b
  have hanti := collarHeight_strictAntiOn b hb hb'
  -- above the junction the collar height is below `s_J`, so the radial coordinate exceeds `r_J`
  have hgt : ∀ t : ℝ, 1/2 < t → rJ < R0 - Real.log (collarHeight t b) := by
    intro t ht
    have hlt : collarHeight t b < sJ := by
      have h' : collarHeight t b < collarHeight (1/2) b :=
        hanti (Set.mem_univ (1/2 : ℝ)) (Set.mem_univ t) ht
      rwa [hhalf] at h'
    have hlog : Real.log (collarHeight t b) < 1/2 := by
      have h' := Real.log_lt_log (collarHeight_pos t b hb) hlt
      rwa [sJ, Real.log_exp] at h'
    linarith
  -- below the junction the radial coordinate is at most `r_J`
  have hle : ∀ t : ℝ, t ≤ 1/2 → 2 * rJ * t ≤ rJ := by
    intro t ht
    calc 2 * rJ * t = (2 * rJ) * t := by ring
      _ ≤ (2 * rJ) * (1/2) :=
          mul_le_mul_of_nonneg_left ht (by linarith)
      _ = rJ := by ring
  by_cases hA : t1 ≤ 1/2
  · by_cases hB : t2 ≤ 1/2
    · -- both below the junction: the linear branch is injective
      rw [ite_eq_left hA, ite_eq_left hB] at h
      exact mul_left_cancel₀ (by norm_num [rJ] : (2 : ℝ) * rJ ≠ 0) h
    · -- `t1` below, `t2` above: impossible
      rw [ite_eq_left hA, ite_eq_right hB] at h
      have := hgt t2 (not_le.mp hB)
      have := hle t1 hA
      linarith
  · by_cases hB : t2 ≤ 1/2
    · -- `t1` above, `t2` below: impossible
      rw [ite_eq_right hA, ite_eq_left hB] at h
      have := hgt t1 (not_le.mp hA)
      have := hle t2 hB
      linarith
    · -- both above the junction: `collarHeight` is injective there
      rw [ite_eq_right hA, ite_eq_right hB] at h
      have hlog : Real.log (collarHeight t1 b) = Real.log (collarHeight t2 b) := by linarith
      have hc : collarHeight t1 b = collarHeight t2 b :=
        Real.log_injOn_pos (collarHeight_pos t1 b hb) (collarHeight_pos t2 b hb) hlog
      exact hanti.injOn (Set.mem_univ t1) (Set.mem_univ t2) hc

/-! ### Injectivity -/

/-- **`Θ_v` is injective on the positive layer strata.**  For points of the cover with `0 < ‖p‖∞`
the polar coordinates `(r,θ,w)` recover `(p,y)`: `w` recovers `y`, then `θ` recovers `u(p)`, then
`r` recovers `‖p‖∞`, and finally `(‖p‖∞, u p)` recovers `p`. -/
theorem ThetaPolar_injOn_pos (v : Fin 5) :
    Set.InjOn (fun z : E2 × E2 => ThetaPolar v z.1 z.2) {z | 0 < nrm z.1} := by
  intro z1 hz1 z2 hz2 h
  obtain ⟨p1, y1⟩ := z1
  obtain ⟨p2, y2⟩ := z2
  change ThetaPolar v p1 y1 = ThetaPolar v p2 y2 at h
  -- the polar coordinates of the two points
  have hw : wOf v y1 = wOf v y2 := by
    have h2 := congrArg (fun q : E4 => q 2) h
    have h3 := congrArg (fun q : E4 => q 3) h
    ext i
    fin_cases i
    · simpa [ThetaPolar] using h2
    · simpa [ThetaPolar] using h3
  have hr : radial v p1 y1 = radial v p2 y2 := by
    have h0 := congrArg (fun q : E4 => q 0) h
    simpa [ThetaPolar] using h0
  have hθ : thetaAng v p1 y1 = thetaAng v p2 y2 := by
    have h1 := congrArg (fun q : E4 => q 1) h
    simpa [ThetaPolar] using h1
  -- step 1: `w` recovers the torus coordinate `y`
  have hy : y1 = y2 := wOf_injective v hw
  -- step 2: `θ` recovers the perimeter parameter `u p` (the phase correction is now common)
  have hu : u p1 = u p2 := u_eq_of_thetaAng_eq hy hθ
  -- the layer norms are positive, so both points are nonzero
  have hn1 : 0 < nrm p1 := hz1
  have hn2 : 0 < nrm p2 := hz2
  have hp1ne : p1 ≠ 0 := by
    intro h0
    have : nrm p1 = 0 := by rw [h0]; simp [nrm]
    linarith
  have hp2ne : p2 ≠ 0 := by
    intro h0
    have : nrm p2 = 0 := by rw [h0]; simp [nrm]
    linarith
  -- step 3: `r` recovers the layer parameter `‖p‖∞` (the ceiling is the same on both sides)
  have hn : nrm p1 = nrm p2 := by
    have h' : (if nrm p1 ≤ 1/2 then 2 * rJ * nrm p1
          else R0 - Real.log (collarHeight (nrm p1) (beta (cuspX v (u p1) y1))))
        = (if nrm p2 ≤ 1/2 then 2 * rJ * nrm p2
          else R0 - Real.log (collarHeight (nrm p2) (beta (cuspX v (u p2) y2)))) := by
      rw [← radial_eq_ite v p1 y1, ← radial_eq_ite v p2 y2]
      exact hr
    rw [← hu, ← hy] at h'
    exact radialProfile_injOn (beta_pos _) (lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ) h'
  -- step 4: `(‖p‖∞, u p)` is a coordinate system on the rays out of the origin
  have hp : p1 = p2 := by
    have hb : bnd p1 = bnd p2 :=
      nrmu_uPerim_injOn (nrm_bnd hp1ne) (nrm_bnd hp2ne) hu
    calc p1 = nrm p1 • bnd p1 := (smul_bnd p1).symm
      _ = nrm p2 • bnd p2 := by rw [hn, hb]
      _ = p2 := smul_bnd p2
  rw [hp, hy]

/-- **The polar chart `Θ_v` is injective on each wedge of the filling square.**  The wedge
hypothesis `wedge k = {p | 0 < ‖p‖∞ ∧ u(p) ∈ (k/4,(k+1)/4)}` is used only through `0 < ‖p‖∞`
(note that `wedge` does not bound `‖p‖∞` from above), so this is the monotone restriction of
`ThetaPolar_injOn_pos` to `{z | z.1 ∈ wedge k} ⊆ {z | 0 < nrm z.1}`. -/
theorem ThetaPolar_injOn (v : Fin 5) (k : Fin 4) :
    Set.InjOn (fun z : E2 × E2 => ThetaPolar v z.1 z.2) {z | z.1 ∈ wedge k} := by
  refine (ThetaPolar_injOn_pos v).mono ?_
  intro z hz
  rw [wedge] at hz
  exact hz.1

end Work.Cusp
