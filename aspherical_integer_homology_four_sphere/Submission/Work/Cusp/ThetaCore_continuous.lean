/-
# Continuity of the core chart `ThetaCore`

`ThetaCore v p y = (r cos θ, r sin θ, w₁, w₂)` (`Work.Cusp.Basic`) is the *inner* (Cartesian) chart
of the `v`-th cusp of the filling piece, the polar chart `ThetaPolar v p y = (r, θ, w₁, w₂)`
followed by the polar-to-Cartesian map `(r, θ) ↦ r (cos θ, sin θ)`.

The angle coordinate `θ = thetaAng v p y = 2π u p + 2π⟪y₂λ₂+y₃λ₃, σ_v⟫/‖σ_v‖²` involves the
perimeter parameter `u p = uPerim (bnd p)`, which jumps by `1` on the ray through the corner
`(1,1)` of the square `Sq = [-1,1]²`.  Nevertheless `ThetaCore v` is continuous *everywhere*:

* on the ray through `(1,1)` the jump of `u` is exactly by `1`, so `cos (2π u p + φ)` and
  `sin (2π u p + φ)` are unchanged (their difference is a multiple of `2π`), and the radial
  coordinate is unchanged too because `σ_v ∈ Λ_v ⊂ ℤ³` is a period of the ceiling `β`
  (`beta_cuspX_eq`); this is proved by comparing with the *shifted* polar chart `ThetaPolarS v c`
  on a shifted wedge `wedgeS c k` (`ThetaPolarS_continuousOn`), which is open (`isOpen_wedgeS`)
  and covers every point of positive sup norm;
* at the origin `p = 0` the radial coordinate `2 r_J ‖p‖∞` vanishes and the (bounded) angular
  oscillation is killed by it.

The two facts together give continuity at every point, whence `Continuous`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.isOpen_wedgeS
import Submission.Work.Cusp.ThetaPolarS_continuousOn
import Submission.Work.Cusp.nrm_continuous
import Submission.Work.Cusp.nrm_nonneg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace Topology
open Filter

/-! ### The polar-to-Cartesian map -/

/-- The map `(r, θ, w₁, w₂) ↦ (r cos θ, r sin θ, w₁, w₂)` taking polar coordinates to the Cartesian
coordinates of the core chart. -/
def coreOf (q : E4) : E4 := !₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3]

lemma continuous_coreOf : Continuous coreOf := by
  show Continuous (fun q : E4 => !₂[q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2, q 3])
  fun_prop

/-! ### Componentwise convergence in `E4` -/

/-- Convergence in `E4` is componentwise (transport along the homeomorphism
`PiLp.homeomorph 2 _ : E4 ≃ₜ (Fin 4 → ℝ)`). -/
lemma tendsto_E4_iff {α : Type*} {l : Filter α} {f : α → E4} {a : E4} :
    Filter.Tendsto f l (nhds a) ↔ ∀ i : Fin 4, Filter.Tendsto (fun x => f x i) l (nhds (a i)) := by
  constructor
  · intro h i
    have h1 : Filter.Tendsto (fun x => (f x).ofLp) l (nhds a.ofLp) :=
      ((PiLp.continuous_ofLp 2 (fun _ : Fin 4 => ℝ)).tendsto a).comp h
    exact ((continuous_apply i).tendsto (a.ofLp)).comp h1
  · intro h
    have h1 : Filter.Tendsto (fun x => fun i : Fin 4 => f x i) l (nhds (fun i => a i)) :=
      tendsto_pi_nhds.mpr h
    have h2 : Filter.Tendsto (fun x => WithLp.toLp 2 (fun i : Fin 4 => f x i)) l
        (nhds (WithLp.toLp 2 (fun i : Fin 4 => a i))) :=
      ((PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).tendsto _).comp h1
    convert h2 using 1

/-! ### `ThetaCore` written with the shifted polar chart -/

/-- **`ThetaCore` is the polar-to-Cartesian map applied to the shifted polar chart.**  For every
shift `c` the two differ only in the angle coordinate, which changes by the integer multiple
`2π⌊u p − c⌋` of `2π`, so `cos` and `sin` are unchanged. -/
lemma ThetaCore_eq_coreOf (v : Fin 5) (c : ℝ) (p y : E2) :
    ThetaCore v p y = coreOf (ThetaPolarS v c p y) := by
  set m : ℤ := ⌊u p - c⌋ with hmdef
  have hsu : uS c p = u p - (m : ℝ) := by rw [uS_sub_floor, ← hmdef]
  have hom : u p = uS c p + (m : ℝ) := by rw [hsu]; ring
  have hang : thetaAng v p y = (2 * π * uS c p
      + 2 * π * (inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2)) + (m : ℝ) * (2 * π) := by
    unfold thetaAng
    rw [hom]
    ring
  have hS : (ThetaPolarS v c p y) 1
      = 2 * π * uS c p + 2 * π * (inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2) := by
    simp [ThetaPolarS, mul_div_assoc]
  have h0 : (ThetaPolarS v c p y) 0 = radial v p y := by simp [ThetaPolarS]
  have hcos : Real.cos (thetaAng v p y) = Real.cos ((ThetaPolarS v c p y) 1) := by
    rw [hS, hang, Real.cos_add_int_mul_two_pi]
  have hsin : Real.sin (thetaAng v p y) = Real.sin ((ThetaPolarS v c p y) 1) := by
    rw [hS, hang, Real.sin_add_int_mul_two_pi]
  dsimp only [ThetaCore, coreOf]
  rw [h0, hcos, hsin]
  ext i
  fin_cases i <;> simp [ThetaPolarS]

/-! ### Membership in a shifted wedge -/

/-- Every point of positive sup norm lies in the `(-1/8)`-shifted third wedge: `u p - (u p + 1/8)`
has fractional part `7/8 ∈ (3/4, 1)`.  This is the wedge on which we compare `ThetaCore v` with the
shifted polar chart. -/
lemma mem_wedgeS_of (p : E2) (hp : 0 < nrm p) :
    p ∈ wedgeS (u p + 1 / 8) (3 : Fin 4) := by
  rw [wedgeS]
  refine ⟨hp, ?_⟩
  have h1 : u p - (u p + 1 / 8) = -(1 / 8 : ℝ) := by ring
  rw [h1]
  have h2 : Int.fract (-(1 / 8) : ℝ) = 7 / 8 := by rw [Int.fract]; norm_num
  rw [h2]
  norm_num

/-! ### The main theorem -/

theorem ThetaCore_continuous (v : Fin 5) :
    Continuous (fun z : E2 × E2 => ThetaCore v z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  intro z0
  by_cases hpos : 0 < nrm z0.1
  swap
  · -- `z0.1 = 0`: the angular oscillation is killed by the vanishing radial coordinate
    have hnrm0 : nrm z0.1 = 0 := le_antisymm (le_of_not_gt hpos) (nrm_nonneg z0.1)
    have hnrm_t : Tendsto (fun z : E2 × E2 => nrm z.1) (𝓝 z0) (𝓝 0) := by
      have h : Tendsto (fun z : E2 × E2 => nrm z.1) (𝓝 z0) (𝓝 (nrm z0.1)) :=
        nrm_continuous.continuousAt.tendsto.comp continuous_fst.continuousAt.tendsto
      rwa [hnrm0] at h
    have h2r : (0 : ℝ) ≤ 2 * rJ := by rw [rJ]; norm_num
    have hradial0 : radial v z0.1 z0.2 = 0 := by
      rw [radial, ite_eq_left (by rw [hnrm0]; norm_num), hnrm0]
      ring
    have hR : Tendsto (fun z : E2 × E2 => 2 * rJ * nrm z.1) (𝓝 z0) (𝓝 0) := by
      have h := hnrm_t.const_mul (2 * rJ)
      rwa [mul_zero] at h
    refine tendsto_E4_iff.mpr (fun i => ?_)
    fin_cases i
    · -- first coordinate `r cos θ → 0`
      show Tendsto (fun z : E2 × E2 => (ThetaCore v z.1 z.2) 0) (𝓝 z0)
        (𝓝 ((ThetaCore v z0.1 z0.2) 0))
      have hz0 : (ThetaCore v z0.1 z0.2) 0 = 0 := by
        dsimp only [ThetaCore]; rw [hradial0]; simp
      rw [hz0]
      have hb : ∀ᶠ z : E2 × E2 in 𝓝 z0,
          ‖(ThetaCore v z.1 z.2) 0 - 0‖ ≤ 2 * rJ * nrm z.1 := by
        have hev : ∀ᶠ z : E2 × E2 in 𝓝 z0, nrm z.1 < 1 / 2 :=
          hnrm_t.eventually (eventually_lt_nhds (by norm_num))
        filter_upwards [hev] with z hz
        have hcomp : (ThetaCore v z.1 z.2) 0
            = (2 * rJ * nrm z.1) * Real.cos (thetaAng v z.1 z.2) := by
          dsimp only [ThetaCore]; rw [radial, ite_eq_left (le_of_lt hz)]; simp
        rw [hcomp, Real.norm_eq_abs, sub_zero, abs_mul,
          abs_of_nonneg (mul_nonneg h2r (nrm_nonneg z.1))]
        calc (2 * rJ * nrm z.1) * |Real.cos (thetaAng v z.1 z.2)|
            ≤ (2 * rJ * nrm z.1) * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (mul_nonneg h2r (nrm_nonneg z.1))
          _ = 2 * rJ * nrm z.1 := mul_one _
      exact tendsto_iff_norm_sub_tendsto_zero.mpr
        (squeeze_zero' (Eventually.of_forall (fun z => norm_nonneg _)) hb hR)
    · -- second coordinate `r sin θ → 0`
      show Tendsto (fun z : E2 × E2 => (ThetaCore v z.1 z.2) 1) (𝓝 z0)
        (𝓝 ((ThetaCore v z0.1 z0.2) 1))
      have hz0 : (ThetaCore v z0.1 z0.2) 1 = 0 := by
        dsimp only [ThetaCore]; rw [hradial0]; simp
      rw [hz0]
      have hb : ∀ᶠ z : E2 × E2 in 𝓝 z0,
          ‖(ThetaCore v z.1 z.2) 1 - 0‖ ≤ 2 * rJ * nrm z.1 := by
        have hev : ∀ᶠ z : E2 × E2 in 𝓝 z0, nrm z.1 < 1 / 2 :=
          hnrm_t.eventually (eventually_lt_nhds (by norm_num))
        filter_upwards [hev] with z hz
        have hcomp : (ThetaCore v z.1 z.2) 1
            = (2 * rJ * nrm z.1) * Real.sin (thetaAng v z.1 z.2) := by
          dsimp only [ThetaCore]; rw [radial, ite_eq_left (le_of_lt hz)]; simp
        rw [hcomp, Real.norm_eq_abs, sub_zero, abs_mul,
          abs_of_nonneg (mul_nonneg h2r (nrm_nonneg z.1))]
        calc (2 * rJ * nrm z.1) * |Real.sin (thetaAng v z.1 z.2)|
            ≤ (2 * rJ * nrm z.1) * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (mul_nonneg h2r (nrm_nonneg z.1))
          _ = 2 * rJ * nrm z.1 := mul_one _
      exact tendsto_iff_norm_sub_tendsto_zero.mpr
        (squeeze_zero' (Eventually.of_forall (fun z => norm_nonneg _)) hb hR)
    · -- third coordinate `w₁`: continuous in `y` alone
      show Tendsto (fun z : E2 × E2 => (ThetaCore v z.1 z.2) 2) (𝓝 z0)
        (𝓝 ((ThetaCore v z0.1 z0.2) 2))
      have hval : (ThetaCore v z0.1 z0.2) 2 = wOf v z0.2 0 := by
        dsimp only [ThetaCore]; simp
      have hfun : (fun z : E2 × E2 => (ThetaCore v z.1 z.2) 2) = fun z => wOf v z.2 0 := by
        funext z; dsimp only [ThetaCore]; simp
      rw [hval, hfun]
      have hY : Continuous (fun z : E2 × E2 => cuspY v z.2) :=
        (continuous_cuspY v).comp continuous_snd
      have hcont : Continuous (fun z : E2 × E2 => wOf v z.2 0) := by
        have h : Continuous (fun z : E2 × E2 => inner ℝ (cuspY v z.2) (frame2 v)) :=
          continuous_inner.comp (hY.prodMk continuous_const)
        simpa [wOf] using h
      exact hcont.continuousAt
    · -- fourth coordinate `w₂`
      show Tendsto (fun z : E2 × E2 => (ThetaCore v z.1 z.2) 3) (𝓝 z0)
        (𝓝 ((ThetaCore v z0.1 z0.2) 3))
      have hval : (ThetaCore v z0.1 z0.2) 3 = wOf v z0.2 1 := by
        dsimp only [ThetaCore]; simp
      have hfun : (fun z : E2 × E2 => (ThetaCore v z.1 z.2) 3) = fun z => wOf v z.2 1 := by
        funext z; dsimp only [ThetaCore]; simp
      rw [hval, hfun]
      have hY : Continuous (fun z : E2 × E2 => cuspY v z.2) :=
        (continuous_cuspY v).comp continuous_snd
      have hcont : Continuous (fun z : E2 × E2 => wOf v z.2 1) := by
        have h : Continuous (fun z : E2 × E2 => inner ℝ (cuspY v z.2) (frame3 v)) :=
          continuous_inner.comp (hY.prodMk continuous_const)
        simpa [wOf] using h
      exact hcont.continuousAt
  · -- `0 < ‖z0.1‖∞`: compare with the shifted polar chart on a shifted wedge
    have hmem : z0.1 ∈ wedgeS (u z0.1 + 1 / 8) (3 : Fin 4) := mem_wedgeS_of z0.1 hpos
    have hopen : IsOpen {z : E2 × E2 | z.1 ∈ wedgeS (u z0.1 + 1 / 8) (3 : Fin 4)} :=
      (isOpen_wedgeS _ _).preimage continuous_fst
    have hnhds : {z : E2 × E2 | z.1 ∈ wedgeS (u z0.1 + 1 / 8) (3 : Fin 4)} ∈ 𝓝 z0 :=
      hopen.mem_nhds hmem
    have hcont : ContinuousOn
        (fun z : E2 × E2 => coreOf (ThetaPolarS v (u z0.1 + 1 / 8) z.1 z.2))
        {z : E2 × E2 | z.1 ∈ wedgeS (u z0.1 + 1 / 8) (3 : Fin 4)} :=
      continuous_coreOf.comp_continuousOn (ThetaPolarS_continuousOn v _ _)
    exact (hcont.congr (fun z _ => ThetaCore_eq_coreOf v _ z.1 z.2)).continuousAt hnhds

end Work.Cusp
