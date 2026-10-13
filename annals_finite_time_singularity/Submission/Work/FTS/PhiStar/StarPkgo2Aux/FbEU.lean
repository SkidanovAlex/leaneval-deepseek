/-
# `FTS/PhiStar/StarPkgo2Aux/FbEU.lean` — the `𝒰`-slots of `Ycheck` in the flat class

This file proves `Work.FTS.PhiStar.StarPkgo2Aux.FbEU`: from a flat datum `Y` with
`Fb 6 (A·K) Y` (the *shifted* flat class of `CoreAux/Defs.lean`) and the flat bounds
`F0 6 A` of the elementary coefficient functions, the two `𝒰`-combinations

* `EUz α Y = -W₁`, `W₁ = 3Y + α(Y/(z+1) + D_zY)`, `D_zY = z ∂_zY`;
* `EU α Y = -(z/(z+1))·W₁`

both lie in `Fb 4` with constant `C·A⁴·K·(α+1)` (`C = 1024`), where `A` is the constant of
the *coefficient* bounds and `K` the `Y`-constant.

The proof is pure flat calculus:

* `F0_mul`/`F0_add`/`F0_zpz`/`Fb_zpz`/`Fb_add` (sibling files) give the closure of the flat
  classes under products, sums and `z ∂_z`;
* `Fb_const_mul_pk` — scalar multiples in `Fb` (constant `|c|·K`, using the *exact*
  identities `F0_const_mul`, `pth_const_mul` of `CoreAux/EVDefs.lean`);
* `Fb_mul_theta_only_pk` — multiplying by a factor depending on `z` alone (`(z+1)⁻¹`,
  `z/(z+1)`) needs no shifted half of `Fb`, because `∂_θ(g·f) = g·∂_θf` on `Q0`;
* `Fb_congr_pk` — `Fb` only sees the values on the open quadrant (locality of `deriv`).

The arithmetic is the elementary bookkeeping of the powers of `A`: the constants produced by
the chain are `3AK`, `16A²K`, `6AK` and then `48A²K`, `256αA³K`, `96αA²K`, all dominated by
`1024·A⁴·K·(α+1)` because `A ≥ 1` and `K, α ≥ 0`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_mul
import Submission.Work.FTS.PhiStar.CoreAux.F0_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_zpz
import Submission.Work.FTS.PhiStar.CoreAux.Fb_zpz
import Submission.Work.FTS.PhiStar.CoreAux.Fb_basic
import Submission.Work.FTS.PhiStar.CoreAux.Fb_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr
import Submission.Work.FTS.PhiStar.CoreAux.EVDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.StarPkgo2Aux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Smoothness of the elementary radial factors -/

private theorem smoothOpen_fst_pk : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z _ : ℝ => z)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z _ : ℝ => z) = fun p : ℝ × ℝ => p.1 := rfl
  rw [h]
  exact contDiffOn_fst

private theorem smoothOpen_inv_one_add_pk :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (z + 1)⁻¹) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z _ : ℝ => (z + 1)⁻¹)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z _ : ℝ => (z + 1)⁻¹)
      = fun p : ℝ × ℝ => (p.1 + 1)⁻¹ := rfl
  rw [h]
  refine ContDiffOn.inv (contDiffOn_fst.add contDiffOn_const) ?_
  intro p hp
  have hp1 : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  linarith

private theorem smoothOpen_z_div_one_add_pk :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (z + 1)) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z _ : ℝ => z / (z + 1))) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z _ : ℝ => z / (z + 1))
      = fun p : ℝ × ℝ => p.1 / (p.1 + 1) := rfl
  rw [h]
  refine ContDiffOn.div contDiffOn_fst (contDiffOn_fst.add contDiffOn_const) ?_
  intro p hp
  have hp1 : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  linarith

/-! ## Flat-calculus closure of `Fb` -/

/-- `Fb` only sees the values on the open quadrant. -/
private theorem Fb_congr_pk {n : ℕ} {K : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hg : Work.FTS.PhiStar.Fb n K g) : Work.FTS.PhiStar.Fb n K f :=
  ⟨Work.FTS.PhiStar.CoreAux.F0_congr h hg.f0,
    Work.FTS.PhiStar.CoreAux.F0_congr (Work.FTS.PhiStar.CoreAux.pth_congr_Q0 h) hg.fd⟩

/-- **Scalar multiples in `Fb`**: the constant is `|c|·K` (no loss, via the exact identities
`D_θ^i(c·f) = c·D_θ^i f` and `∂_θ(c·f) = c·∂_θ f`). -/
private theorem Fb_const_mul_pk {n : ℕ} {K c : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.PhiStar.Fb n K f) :
    Work.FTS.PhiStar.Fb n (|c| * K) (fun z θ => c * f z θ) :=
  ⟨Work.FTS.PhiStar.CoreAux.F0_const_mul c hf.f0, by
    rw [Work.FTS.PhiStar.CoreAux.pth_const_mul c f]
    exact Work.FTS.PhiStar.CoreAux.F0_const_mul c hf.fd⟩

/-- **Multiplication by a factor depending on `z` alone.**  If `g` is independent of `θ` and
`C^∞` on the open quadrant with `F0 n A g`, and `f` has `Fb n K`, then `g·f` has `Fb n`
with constant `2ⁿ·A·K`.  Only the `F0`-half of `Fb` is used for `g`: on `Q0`,
`∂_θ(g·f) = g·∂_θf` because the `θ`-slice of `g` is constant. -/
private theorem Fb_mul_theta_only_pk {n : ℕ} {A K : ℝ} {g f : ℝ → ℝ → ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hgθ : ∀ z θ θ' : ℝ, g z θ = g z θ')
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hfs : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.PhiStar.F0 n A g) (hf : Work.FTS.PhiStar.Fb n K f) :
    Work.FTS.PhiStar.Fb n ((2 : ℝ) ^ n * A * K) (fun z θ => g z θ * f z θ) := by
  refine ⟨Work.FTS.PhiStar.CoreAux.F0_mul hA hK hgs hfs hg hf.f0, ?_⟩
  have h2 : Work.FTS.PhiStar.F0 n ((2 : ℝ) ^ n * A * K)
      (fun z θ => g z θ * Work.Spaces.pth f z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul hA hK hgs hfs.pth hg hf.fd
  refine Work.FTS.PhiStar.CoreAux.F0_congr ?_ h2
  intro z θ hz hθ hθ'
  show Work.Spaces.pth (fun z θ => g z θ * f z θ) z θ = g z θ * Work.Spaces.pth f z θ
  have hfun : (fun θ' => g z θ' * f z θ') = (fun θ' => g z θ * f z θ') := by
    funext θ'
    rw [hgθ z θ' θ]
  simp only [Work.Spaces.pth]
  rw [hfun, deriv_const_mul_field]

/-! ## The arithmetic of the constants -/

/-- The constant of the two bounds. -/
private def CUS : ℝ := 1024

private theorem pow_le_four_pk {A : ℝ} (hA : 1 ≤ A) {p : ℕ} (hp : p ≤ 4) : A ^ p ≤ A ^ 4 :=
  pow_le_pow_right₀ hA hp

private theorem base_le_pk {A K α : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α) {p : ℕ}
    (hp : p ≤ 4) : A ^ p * K ≤ A ^ 4 * K * (α + 1) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have h1 : A ^ p * K ≤ A ^ 4 * K := mul_le_mul_of_nonneg_right (pow_le_four_pk hA hp) hK
  have h2 : A ^ 4 * K * 1 ≤ A ^ 4 * K * (α + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (pow_nonneg hA0 4) hK)
  calc A ^ p * K ≤ A ^ 4 * K := h1
    _ = A ^ 4 * K * 1 := by ring
    _ ≤ A ^ 4 * K * (α + 1) := h2

private theorem alpha_base_le_pk {A K α : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α) {p : ℕ}
    (hp : p ≤ 4) : α * (A ^ p * K) ≤ A ^ 4 * K * (α + 1) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have h1 : A ^ p * K ≤ A ^ 4 * K := mul_le_mul_of_nonneg_right (pow_le_four_pk hA hp) hK
  have h2 : α * (A ^ p * K) ≤ α * (A ^ 4 * K) := mul_le_mul_of_nonneg_left h1 hα
  have h3 : α * (A ^ 4 * K) ≤ (α + 1) * (A ^ 4 * K) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (pow_nonneg hA0 4) hK)
  calc α * (A ^ p * K) ≤ α * (A ^ 4 * K) := h2
    _ ≤ (α + 1) * (A ^ 4 * K) := h3
    _ = A ^ 4 * K * (α + 1) := by ring

private theorem coeff_base_le_pk {A K α c : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hc : 0 ≤ c) {p : ℕ} (hp : p ≤ 4) : c * A ^ p * K ≤ c * (A ^ 4 * K * (α + 1)) := by
  calc c * A ^ p * K = c * (A ^ p * K) := by ring
    _ ≤ c * (A ^ 4 * K * (α + 1)) :=
        mul_le_mul_of_nonneg_left (base_le_pk hA hK hα hp) hc

private theorem coeff_alpha_le_pk {A K α c : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hc : 0 ≤ c) {p : ℕ} (hp : p ≤ 4) : c * α * A ^ p * K ≤ c * (A ^ 4 * K * (α + 1)) := by
  calc c * α * A ^ p * K = c * (α * (A ^ p * K)) := by ring
    _ ≤ c * (A ^ 4 * K * (α + 1)) :=
        mul_le_mul_of_nonneg_left (alpha_base_le_pk hA hK hα hp) hc

/-! ## The main theorem -/

theorem FbEU : ∃ C : ℝ, 0 < C ∧ ∀ (α K A : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 1 ≤ A →
    Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) →
    Work.FTS.PhiStar.Fb 6 (A * K) Y →
    Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * K * (α + 1)) (Work.FTS.PhiStar.EUz α Y) ∧
    Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * K * (α + 1)) (Work.FTS.PhiStar.EU α Y) := by
  refine ⟨CUS, by norm_num [CUS], ?_⟩
  intro α K A Y hα hK hA hYs _hs1 _hs2 _hs3 _hs4 hzd hzi hY
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hS : (0 : ℝ) ≤ A * K := mul_nonneg hA0 hK
  -- the two radial coefficients, in the `z + 1` form matching `Wone`/`Yblk`
  have hzi' : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (z + 1)⁻¹) :=
    Work.FTS.PhiStar.CoreAux.F0_congr
      (f := fun z _ : ℝ => (z + 1)⁻¹) (g := fun z _ : ℝ => (1 + z)⁻¹)
      (fun z θ _ _ _ => by rw [add_comm (1 : ℝ) z]) hzi
  have hzd' : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => z / (z + 1)) :=
    Work.FTS.PhiStar.CoreAux.F0_congr
      (f := fun z _ : ℝ => z / (z + 1)) (g := fun z _ : ℝ => z / (1 + z))
      (fun z θ _ _ _ => by rw [add_comm (1 : ℝ) z]) hzd
  have hzi4 : Work.FTS.PhiStar.F0 4 A (fun z _ : ℝ => (z + 1)⁻¹) :=
    hzi'.mono (by norm_num) le_rfl
  have hzd4 : Work.FTS.PhiStar.F0 4 A (fun z _ : ℝ => z / (z + 1)) :=
    hzd'.mono (by norm_num) le_rfl
  have sFst : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) := smoothOpen_fst_pk
  have sInv : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (z + 1)⁻¹) :=
    smoothOpen_inv_one_add_pk
  have sRho : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (z + 1)) :=
    smoothOpen_z_div_one_add_pk
  -- the `Fb`-chain
  have hY4 : Work.FTS.PhiStar.Fb 4 (A * K) Y := hY.mono (by norm_num) le_rfl
  -- (a) `3·Y`
  have t3Y : Work.FTS.PhiStar.Fb 4 (3 * (A * K)) (fun z θ => 3 * Y z θ) := by
    have h := Fb_const_mul_pk (c := (3 : ℝ)) hY4
    rwa [show |(3 : ℝ)| = 3 by norm_num] at h
  -- (b) `Y·(z+1)⁻¹`
  have tInv : Work.FTS.PhiStar.Fb 4 (16 * A ^ 2 * K) (fun z θ => Y z θ * (z + 1)⁻¹) := by
    have h1 : Work.FTS.PhiStar.Fb 4 ((2 : ℝ) ^ 4 * A * (A * K))
        (fun z θ => (z + 1)⁻¹ * Y z θ) :=
      Fb_mul_theta_only_pk hA0 hS (fun z θ θ' => rfl) sInv hYs hzi4 hY4
    have h2 : Work.FTS.PhiStar.Fb 4 (16 * A ^ 2 * K) (fun z θ => (z + 1)⁻¹ * Y z θ) :=
      h1.mono le_rfl (le_of_eq (by ring))
    exact Fb_congr_pk (fun z θ _ _ _ => by ring) h2
  -- (c) `D_z Y = z·∂_z Y`
  have tZ : Work.FTS.PhiStar.Fb 4 (6 * (A * K)) (fun z θ => z * Work.Spaces.pz Y z θ) := by
    have h := (Work.FTS.PhiStar.CoreAux.Fb_zpz (n := 5) hS hYs hY).mono
      (show 4 ≤ 5 by norm_num) le_rfl
    have hc : (((5 : ℕ) : ℝ) + 1) * (A * K) = 6 * (A * K) := by norm_num
    rwa [hc] at h
  -- (d) the sum `Y·(z+1)⁻¹ + D_z Y`
  have sInvY : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Y z θ * (z + 1)⁻¹) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul hYs sInv
  have sZpY : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul sFst hYs.pz
  have tSum : Work.FTS.PhiStar.Fb 4 (16 * A ^ 2 * K + 6 * (A * K))
      (fun z θ => Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fb_add sInvY sZpY tInv tZ
  -- (e) `α·(Y·(z+1)⁻¹ + D_z Y)`
  have tAlpha : Work.FTS.PhiStar.Fb 4 (α * (16 * A ^ 2 * K + 6 * (A * K)))
      (fun z θ => α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ)) := by
    have h := Fb_const_mul_pk (c := α) tSum
    rwa [show |α| = α by exact abs_of_nonneg hα] at h
  -- (f) `W₁ = 3Y + α·(Y·(z+1)⁻¹ + D_z Y)`
  have s3Y : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 3 * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hYs 3
  have sAlpha : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul
      (Work.FTS.PhiStar.CoreAux.SmoothOpen.add sInvY sZpY) α
  have tW : Work.FTS.PhiStar.Fb 4 (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K)))
      (fun z θ => 3 * Y z θ + α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.Fb_add s3Y sAlpha t3Y tAlpha
  -- (g) `EUz α Y = -W₁`
  have hKW0 : (0 : ℝ) ≤ 3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K)) := by
    have h1 : (0 : ℝ) ≤ 16 * A ^ 2 * K + 6 * (A * K) := by positivity
    nlinarith [mul_nonneg hα h1, mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hS]
  have tNeg : Work.FTS.PhiStar.Fb 4 (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K)))
      (fun z θ => -(3 * Y z θ + α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ))) := by
    have h := Fb_const_mul_pk (c := (-1 : ℝ)) tW
    simpa only [abs_neg, abs_one, one_mul, neg_one_mul] using h
  have tEUz : Work.FTS.PhiStar.Fb 4 (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K)))
      (Work.FTS.PhiStar.EUz α Y) :=
    Fb_congr_pk (fun z θ _ _ _ => by
      simp only [Work.FTS.PhiStar.EUz, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk,
        div_eq_mul_inv]) tNeg
  -- (h) `EU α Y = (z/(z+1))·(-W₁)`
  have sNegW : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(3 * Y z θ + α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ))) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.congr
      (Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul
        (Work.FTS.PhiStar.CoreAux.SmoothOpen.add s3Y sAlpha) (-1))
      (fun z θ _ _ _ => by ring)
  have tEU : Work.FTS.PhiStar.Fb 4
      ((2 : ℝ) ^ 4 * A * (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K))))
      (fun z θ => (z / (z + 1)) *
        (-(3 * Y z θ + α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ)))) :=
    Fb_mul_theta_only_pk hA0 hKW0 (fun z θ θ' => rfl) sRho sNegW hzd4 tNeg
  have tEU' : Work.FTS.PhiStar.Fb 4
      ((2 : ℝ) ^ 4 * A * (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K))))
      (Work.FTS.PhiStar.EU α Y) :=
    Fb_congr_pk (fun z θ _ _ _ => by
      simp only [Work.FTS.PhiStar.EU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk,
        div_eq_mul_inv]
      ring) tEU
  -- the arithmetic
  have hT0 : (0 : ℝ) ≤ A ^ 4 * K * (α + 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hA0 4) hK) (by linarith)
  have hAbs : CUS * A ^ 4 * K * (α + 1) = CUS * (A ^ 4 * K * (α + 1)) := by ring
  have hKW : 3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K))
      ≤ CUS * A ^ 4 * K * (α + 1) := by
    have e1 : 3 * (A * K) ≤ 3 * (A ^ 4 * K * (α + 1)) := by
      have h := coeff_base_le_pk (A := A) (K := K) (α := α) (c := 3) hA hK hα
        (by norm_num) (p := 1) (by norm_num)
      calc 3 * (A * K) = 3 * A ^ 1 * K := by ring
        _ ≤ 3 * (A ^ 4 * K * (α + 1)) := h
    have e2 : α * (16 * A ^ 2 * K) ≤ 16 * (A ^ 4 * K * (α + 1)) := by
      have h := coeff_alpha_le_pk (A := A) (K := K) (α := α) (c := 16) hA hK hα
        (by norm_num) (p := 2) (by norm_num)
      calc α * (16 * A ^ 2 * K) = 16 * α * A ^ 2 * K := by ring
        _ ≤ 16 * (A ^ 4 * K * (α + 1)) := h
    have e3 : α * (6 * (A * K)) ≤ 6 * (A ^ 4 * K * (α + 1)) := by
      have h := coeff_alpha_le_pk (A := A) (K := K) (α := α) (c := 6) hA hK hα
        (by norm_num) (p := 1) (by norm_num)
      calc α * (6 * (A * K)) = 6 * α * A ^ 1 * K := by ring
        _ ≤ 6 * (A ^ 4 * K * (α + 1)) := h
    have step1 : 3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K))
        ≤ 25 * (A ^ 4 * K * (α + 1)) := by
      rw [mul_add]
      linarith [e1, e2, e3]
    have step2 : (25 : ℝ) * (A ^ 4 * K * (α + 1)) ≤ CUS * A ^ 4 * K * (α + 1) := by
      rw [hAbs]
      exact mul_le_mul_of_nonneg_right (by norm_num [CUS]) hT0
    linarith [step1, step2]
  have hKEU : (2 : ℝ) ^ 4 * A * (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K)))
      ≤ CUS * A ^ 4 * K * (α + 1) := by
    have hb : (2 : ℝ) ^ 4 * A * (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K)))
        = 48 * A ^ 2 * K + 256 * α * A ^ 3 * K + 96 * α * A ^ 2 * K := by ring
    rw [hb]
    have e1 : 48 * A ^ 2 * K ≤ 48 * (A ^ 4 * K * (α + 1)) :=
      coeff_base_le_pk (A := A) (K := K) (α := α) (c := 48) hA hK hα
        (by norm_num) (p := 2) (by norm_num)
    have e2 : 256 * α * A ^ 3 * K ≤ 256 * (A ^ 4 * K * (α + 1)) :=
      coeff_alpha_le_pk (A := A) (K := K) (α := α) (c := 256) hA hK hα
        (by norm_num) (p := 3) (by norm_num)
    have e3 : 96 * α * A ^ 2 * K ≤ 96 * (A ^ 4 * K * (α + 1)) :=
      coeff_alpha_le_pk (A := A) (K := K) (α := α) (c := 96) hA hK hα
        (by norm_num) (p := 2) (by norm_num)
    have step1 : 48 * A ^ 2 * K + 256 * α * A ^ 3 * K + 96 * α * A ^ 2 * K
        ≤ 400 * (A ^ 4 * K * (α + 1)) := by linarith [e1, e2, e3]
    have step2 : (400 : ℝ) * (A ^ 4 * K * (α + 1)) ≤ CUS * A ^ 4 * K * (α + 1) := by
      rw [hAbs]
      exact mul_le_mul_of_nonneg_right (by norm_num [CUS]) hT0
    linarith [step1, step2]
  exact ⟨tEUz.mono le_rfl hKW, tEU'.mono le_rfl hKEU⟩

end

end Work.FTS.PhiStar.StarPkgo2Aux
