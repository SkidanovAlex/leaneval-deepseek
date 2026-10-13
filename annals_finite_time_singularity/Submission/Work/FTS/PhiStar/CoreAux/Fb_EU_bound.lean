/-
# `FTS/PhiStar/CoreAux/Fb_EU_bound.lean` — the flat bounds on the `𝒰`-slots of `Ycheck`

The eleven fields of `StarPkgo2` are explicit algebraic combinations of `Ŷ = Ycheck α Φs`
and its mixed derivatives.  For `Ŷ` in the flat class `Fb 6 M` (see `CoreAux/Defs.lean`)
two of them are, on the open quadrant `Q0 = (0,∞)×(0,π/2)`,

* `EUz α Y = -W₁`, `W₁ = 3Y + α(Y/(z+1) + D_zY)`, `D_zY = z ∂_z Y`;
* `EU α Y = -(z/(z+1))·W₁`,

and this file proves that both lie in `Fb 4` with the constant
`C·A⁴·(K+1)·(α+1)`, where `A` is the constant of `Fb 6 (A(K+1)) Y` (the hypotheses on
`z/(1+z)` and `1/(1+z)` provide the `A`-bound for the two radial factors).

The proof is pure *flat calculus*:

* `F0_mul`/`Fb_add`/`F0_zpz`/`Fb_zpz` (all proved in the sibling files) give the closure of
  the flat classes under products, sums and `z ∂_z`;
* the new ingredient is `Fb_mul_theta_only_fts`: multiplying by a factor which depends on `z`
  only neither raises the order nor needs the shifted half of `Fb`, since
  `∂_θ(g·f) = g·∂_θ f` on `Q0`;
* `Fb_congr_fts` transfers all bounds between functions which agree pointwise on `Q0`.

The arithmetic is the elementary bookkeeping of the powers of `A`: the product of `Y`
(A-degree 1) with `z/(z+1)` (A-degree 1) has A-degree 2, and the extra factor `A` for
`EU` makes A-degree 3, so the final constant `10⁶·A⁴(K+1)(α+1)` is uniform in `A`.

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
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr
import Submission.Work.FTS.PhiStar.CoreAux.Fb_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.CoreAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `SmoothOpen` for the elementary factors -/

/-- Constants are smooth on the open quadrant. -/
theorem smoothOpen_const_fts (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ _ : ℝ => c) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun _ _ : ℝ => c)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun _ _ : ℝ => c) = fun _ : ℝ × ℝ => c := rfl
  rw [h]
  exact contDiffOn_const

/-- The radius `z ↦ z` is smooth on the open quadrant. -/
theorem smoothOpen_fst_fts :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z _ : ℝ => z)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z _ : ℝ => z) = fun p : ℝ × ℝ => p.1 := rfl
  rw [h]
  exact contDiffOn_fst

theorem smoothOpen_mul_fts {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [h]
  exact hf.mul hg

theorem smoothOpen_add_fts {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ + g z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ : ℝ => f z θ + g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p := rfl
  rw [h]
  exact hf.add hg

theorem smoothOpen_const_mul_fts (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => c * f z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ : ℝ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  rw [h]
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hf

theorem smoothOpen_inv_one_plus_z_fts :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z)⁻¹) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z _ : ℝ => (1 + z)⁻¹)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z _ : ℝ => (1 + z)⁻¹) = fun p : ℝ × ℝ => (1 + p.1)⁻¹ := rfl
  rw [h]
  refine ContDiffOn.inv (contDiffOn_const.add contDiffOn_fst) ?_
  intro p hp
  have hp1 : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  linarith

theorem smoothOpen_z_div_one_plus_z_fts :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z _ : ℝ => z / (1 + z))) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z _ : ℝ => z / (1 + z))
      = fun p : ℝ × ℝ => p.1 / (1 + p.1) := rfl
  rw [h]
  refine ContDiffOn.div contDiffOn_fst (contDiffOn_const.add contDiffOn_fst) ?_
  intro p hp
  have hp1 : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  linarith

/-! ## Locality and the θ-only product -/

/-- `∂_θ` (hence `F0`) only sees the values on the open quadrant. -/
theorem pth_congr_Q0_fts {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  intro z θ hz hθ hθ'
  have hnb : ∀ᶠ θ' in 𝓝 θ, 0 < θ' ∧ θ' < Real.pi / 2 :=
    isOpen_Ioo.mem_nhds ⟨hθ, hθ'⟩
  have heq : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') := by
    filter_upwards [hnb] with θ' hθ''
    exact h z θ' hz hθ''.1 hθ''.2
  simp only [Work.Spaces.pth]
  exact heq.deriv_eq

/-- **`Fb` is local**: two functions agreeing pointwise on the open quadrant are in the same
shifted flat class. -/
theorem Fb_congr_fts {n : ℕ} {K : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hg : Fb n K g) : Fb n K f :=
  ⟨F0_congr h hg.f0, F0_congr (pth_congr_Q0_fts h) hg.fd⟩

/-- **Multiplication by a factor which depends on `z` only.**  If `g` is `z`-only, `C^∞` on
the open quadrant, with `F0 n A g`, and `f` is `C^∞` there with `Fb n K f`, then `g·f` is in
`Fb n` with constant `2ⁿ·A·K`.

The `∂_θ`-half of `Fb` needs no shifted hypothesis on `g`: on `Q0`,
`∂_θ(g·f) = g·∂_θ f` because the `θ`-slice of `g` is constant. -/
theorem Fb_mul_theta_only_fts {n : ℕ} {A K : ℝ} {g f : ℝ → ℝ → ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hgθ : ∀ z θ θ' : ℝ, g z θ = g z θ')
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hfs : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : F0 n A g) (hf : Fb n K f) :
    Fb n ((2 : ℝ) ^ n * A * K) (fun z θ => g z θ * f z θ) := by
  refine ⟨F0_mul hA hK hgs hfs hg hf.f0, ?_⟩
  have h2 : F0 n ((2 : ℝ) ^ n * A * K) (fun z θ => g z θ * Work.Spaces.pth f z θ) :=
    F0_mul hA hK hgs hfs.pth hg hf.fd
  refine F0_congr ?_ h2
  intro z θ hz hθ hθ'
  show Work.Spaces.pth (fun z θ => g z θ * f z θ) z θ = g z θ * Work.Spaces.pth f z θ
  have hfun : (fun θ' => g z θ' * f z θ') = (fun θ' => g z θ * f z θ') := by
    funext θ'
    rw [hgθ z θ' θ]
  simp only [Work.Spaces.pth]
  rw [hfun, deriv_const_mul_field]

/-- A nonnegative constant belongs to `F0` with itself as bound. -/
theorem F0_const_fts {n : ℕ} {c : ℝ} (hc : 0 ≤ c) : F0 n c (fun _ _ : ℝ => c) := by
  have h : F0 n |c| (fun _ _ : ℝ => c) := F0.const n c
  rwa [abs_of_nonneg hc] at h

/-- `-1` belongs to `F0` with bound `1`. -/
theorem F0_const_neg_one_fts {n : ℕ} : F0 n 1 (fun _ _ : ℝ => (-1 : ℝ)) := by
  have h : F0 n |(-1 : ℝ)| (fun _ _ : ℝ => (-1 : ℝ)) := F0.const n (-1)
  rwa [show |(-1 : ℝ)| = 1 by norm_num] at h

/-! ## The arithmetic bookkeeping -/

/-- **Monomial comparison.**  For `A ≥ 1`, `K, α ≥ 0`, `j ≤ 4`, `m ≤ 1` and `0 ≤ c ≤ C`,
`c·αᵐ·Aʲ·(K+1) ≤ C·A⁴·(K+1)·(α+1)`. -/
theorem mono_bound_fts {c C A K α : ℝ} {j m : ℕ}
    (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α) (hj : j ≤ 4) (hm : m ≤ 1)
    (hc : 0 ≤ c) (hcC : c ≤ C) :
    c * α ^ m * A ^ j * (K + 1) ≤ C * A ^ 4 * (K + 1) * (α + 1) := by
  have hA0 : 0 ≤ A := by linarith
  have hK1 : 0 < K + 1 := by linarith
  have hα1 : 0 < α + 1 := by linarith
  have hC0 : 0 ≤ C := le_trans hc hcC
  have hpowA : A ^ j ≤ A ^ 4 := pow_le_pow_right₀ hA hj
  have hpowα : α ^ m ≤ α + 1 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      simpa using (by linarith : (1 : ℝ) ≤ α + 1)
    · have hm1 : m = 1 := by omega
      subst hm1
      simpa using (by linarith : α ≤ α + 1)
  have hCA : c * α ^ m ≤ C * (α + 1) :=
    mul_le_mul hcC hpowα (pow_nonneg hα m) hC0
  have hAK : A ^ j * (K + 1) ≤ A ^ 4 * (K + 1) :=
    mul_le_mul_of_nonneg_right hpowA hK1.le
  calc c * α ^ m * A ^ j * (K + 1) = (c * α ^ m) * (A ^ j * (K + 1)) := by ring
    _ ≤ (C * (α + 1)) * (A ^ 4 * (K + 1)) :=
        mul_le_mul hCA hAK (mul_nonneg (pow_nonneg hA0 j) hK1.le) (mul_nonneg hC0 hα1.le)
    _ = C * A ^ 4 * (K + 1) * (α + 1) := by ring

theorem Fb_EU_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α K A : ℝ) (Y : ℝ → ℝ → ℝ), 0 ≤ α → 0 ≤ K → 1 ≤ A → Work.FTS.EllipticEst.SmoothOpen Y → Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) → Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) → Work.FTS.PhiStar.Fb 6 (A * (K + 1)) Y → Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * (K + 1) * (α + 1)) (Work.FTS.PhiStar.EUz α Y) ∧ Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * (K + 1) * (α + 1)) (Work.FTS.PhiStar.EU α Y) := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro α K A Y hα hK hA hY hz1 hz2 hYb
  set M : ℝ := A * (K + 1) with hM
  have hA0 : 0 < A := by linarith
  have hAnn : 0 ≤ A := le_of_lt hA0
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  -- the arithmetic instantiation
  have quad : ∀ c C : ℝ, ∀ j m : ℕ, c ≤ C → 0 ≤ c → j ≤ 4 → m ≤ 1 →
      c * α ^ m * A ^ j * (K + 1) ≤ C * A ^ 4 * (K + 1) * (α + 1) :=
    fun c C j m hcC hc hj hm => mono_bound_fts hA hK hα hj hm hc hcC
  -- the two radial factors and `Y`
  have hInv4 : F0 4 A (fun z _ : ℝ => (1 + z)⁻¹) := hz2.mono (by norm_num) le_rfl
  have hDiv4 : F0 4 A (fun z _ : ℝ => z / (1 + z)) := hz1.mono (by norm_num) le_rfl
  have hY4 : Fb 4 M Y := hYb.mono (by norm_num) le_rfl
  have hYblk : Fb 4 (((5 : ℝ) + 1) * M) (fun z θ => z * Work.Spaces.pz Y z θ) :=
    (Fb_zpz (n := 5) hMnn hY hYb).mono (by norm_num) le_rfl
  have hYblknn : 0 ≤ ((5 : ℝ) + 1) * M := mul_nonneg (by norm_num) hMnn
  -- `(1+z)^{-1} · Y`
  have hInv : Fb 4 ((2 : ℝ) ^ 4 * A * M) (fun z θ => (1 + z)⁻¹ * Y z θ) :=
    Fb_mul_theta_only_fts (n := 4) (A := A) (g := fun z _ : ℝ => (1 + z)⁻¹) (f := Y)
      hAnn hMnn (fun z θ θ' => rfl) smoothOpen_inv_one_plus_z_fts hY hInv4 hY4
  have hInvnn : 0 ≤ (2 : ℝ) ^ 4 * A * M := mul_nonneg (mul_nonneg (by norm_num) hAnn) hMnn
  -- `α · ((1+z)^{-1} · Y)`
  have hA1 : Fb 4 ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M))
      (fun z θ => α * ((1 + z)⁻¹ * Y z θ)) :=
    Fb_mul_theta_only_fts (n := 4) (A := α) (g := fun _ _ : ℝ => α)
      (f := fun z θ => (1 + z)⁻¹ * Y z θ) hα hInvnn (fun z θ θ' => rfl)
      (smoothOpen_const_fts α) (smoothOpen_mul_fts smoothOpen_inv_one_plus_z_fts hY)
      (F0_const_fts hα) hInv
  -- `α · (z ∂_z Y)`
  have hA2 : Fb 4 ((2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M))
      (fun z θ => α * (z * Work.Spaces.pz Y z θ)) :=
    Fb_mul_theta_only_fts (n := 4) (A := α) (g := fun _ _ : ℝ => α)
      (f := fun z θ => z * Work.Spaces.pz Y z θ) hα hYblknn (fun z θ θ' => rfl)
      (smoothOpen_const_fts α) (smoothOpen_mul_fts smoothOpen_fst_fts hY.pz)
      (F0_const_fts hα) hYblk
  have hA12 : Fb 4 ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) + (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M))
      (fun z θ => α * ((1 + z)⁻¹ * Y z θ) + α * (z * Work.Spaces.pz Y z θ)) :=
    Fb_add (smoothOpen_const_mul_fts α (smoothOpen_mul_fts smoothOpen_inv_one_plus_z_fts hY))
      (smoothOpen_const_mul_fts α (smoothOpen_mul_fts smoothOpen_fst_fts hY.pz)) hA1 hA2
  have hA12' : Fb 4 ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) + (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M))
      (fun z θ => α * ((1 + z)⁻¹ * Y z θ + z * Work.Spaces.pz Y z θ)) :=
    Fb_congr_fts (fun z θ _ _ _ => by ring) hA12
  -- `3 Y`
  have hS3 : Fb 4 ((2 : ℝ) ^ 4 * 3 * M) (fun z θ => 3 * Y z θ) :=
    Fb_mul_theta_only_fts (n := 4) (A := 3) (g := fun _ _ : ℝ => 3) (f := Y)
      (by norm_num) hMnn (fun z θ θ' => rfl) (smoothOpen_const_fts 3) hY
      (F0_const_fts (by norm_num : (0 : ℝ) ≤ 3)) hY4
  -- the function `W'` (`Wone α Y` with the division replaced by the inverse)
  have hW' : Fb 4 ((2 : ℝ) ^ 4 * 3 * M + ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) + (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M)))
      (fun z θ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ + z * Work.Spaces.pz Y z θ)) :=
    Fb_add (smoothOpen_const_mul_fts 3 hY)
      (smoothOpen_const_mul_fts α (smoothOpen_add_fts
        (smoothOpen_mul_fts smoothOpen_inv_one_plus_z_fts hY)
        (smoothOpen_mul_fts smoothOpen_fst_fts hY.pz))) hS3 hA12'
  have hW'mnn : 0 ≤ (2 : ℝ) ^ 4 * 3 * M + ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) + (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M)) := by
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ 4 * 3 * M := mul_nonneg (mul_nonneg (by norm_num) (by norm_num)) hMnn
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) :=
      mul_nonneg (mul_nonneg (by norm_num) hα) hInvnn
    have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M) :=
      mul_nonneg (mul_nonneg (by norm_num) hα) hYblknn
    linarith
  have hW'smooth : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ + z * Work.Spaces.pz Y z θ)) :=
    smoothOpen_add_fts (smoothOpen_const_mul_fts 3 hY)
      (smoothOpen_const_mul_fts α (smoothOpen_add_fts
        (smoothOpen_mul_fts smoothOpen_inv_one_plus_z_fts hY)
        (smoothOpen_mul_fts smoothOpen_fst_fts hY.pz)))
  -- the `EUz` bound
  have hEUz : Fb 4 ((2 : ℝ) ^ 4 * 1 * ((2 : ℝ) ^ 4 * 3 * M + ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) + (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M))))
      (EUz α Y) := by
    refine Fb_congr_fts (g := fun z θ => (-1) * (3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ + z * Work.Spaces.pz Y z θ))) (fun z θ _ _ _ => ?_) ?_
    · simp only [EUz, Wone, Yblk, div_eq_mul_inv,
        show (z : ℝ) + 1 = 1 + z from by ring]
      ring
    · exact Fb_mul_theta_only_fts (n := 4) (A := 1) (g := fun _ _ : ℝ => (-1))
        (f := fun z θ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ + z * Work.Spaces.pz Y z θ))
        (by norm_num) hW'mnn (fun z θ θ' => rfl) (smoothOpen_const_fts (-1)) hW'smooth
        F0_const_neg_one_fts hW'
  -- the `EU` bound
  have hEU : Fb 4 ((2 : ℝ) ^ 4 * 1 * ((2 : ℝ) ^ 4 * A * ((2 : ℝ) ^ 4 * 3 * M + ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) + (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M)))))
      (EU α Y) := by
    have hEU1smooth : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (z / (1 + z)) * (3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ + z * Work.Spaces.pz Y z θ))) :=
      smoothOpen_mul_fts smoothOpen_z_div_one_plus_z_fts hW'smooth
    have hEU1 : Fb 4 ((2 : ℝ) ^ 4 * A * ((2 : ℝ) ^ 4 * 3 * M + ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) + (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M))))
        (fun z θ => (z / (1 + z)) * (3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ + z * Work.Spaces.pz Y z θ))) :=
      Fb_mul_theta_only_fts (n := 4) (A := A) (g := fun z _ : ℝ => z / (1 + z))
        (f := fun z θ => 3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ + z * Work.Spaces.pz Y z θ))
        hAnn hW'mnn (fun z θ θ' => rfl) smoothOpen_z_div_one_plus_z_fts hW'smooth hDiv4 hW'
    have hEU1nn : 0 ≤ (2 : ℝ) ^ 4 * A * ((2 : ℝ) ^ 4 * 3 * M + ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) + (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M))) :=
      mul_nonneg (mul_nonneg (by norm_num) hAnn) hW'mnn
    refine Fb_congr_fts (g := fun z θ => (-1) * ((z / (1 + z)) * (3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ + z * Work.Spaces.pz Y z θ)))) (fun z θ _ _ _ => ?_) ?_
    · simp only [EU, Wone, Yblk, div_eq_mul_inv,
        show (z : ℝ) + 1 = 1 + z from by ring]
      ring
    · exact Fb_mul_theta_only_fts (n := 4) (A := 1) (g := fun _ _ : ℝ => (-1))
        (f := fun z θ => (z / (1 + z)) * (3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ + z * Work.Spaces.pz Y z θ)))
        (by norm_num) hEU1nn (fun z θ θ' => rfl) (smoothOpen_const_fts (-1)) hEU1smooth
        F0_const_neg_one_fts hEU1
  -- the arithmetic
  have hEUz_le : (2 : ℝ) ^ 4 * 1 * ((2 : ℝ) ^ 4 * 3 * M + ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) + (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M)))
      ≤ 1000000 * A ^ 4 * (K + 1) * (α + 1) := by
    have heq : (2 : ℝ) ^ 4 * 1 * ((2 : ℝ) ^ 4 * 3 * M + ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) + (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M)))
        = 768 * (A * (K + 1)) + (4096 * α * (A * (A * (K + 1))) + 1536 * α * (A * (K + 1))) := by
      rw [hM]; ring
    rw [heq]
    have hX : (0 : ℝ) ≤ A ^ 4 * (K + 1) * (α + 1) := by positivity
    have h1 := quad 768 300000 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h2 := quad 4096 300000 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h3 := quad 1536 300000 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simp only [pow_zero, pow_one, one_mul, mul_one] at h1 h2 h3
    linarith
  have hEU_le : (2 : ℝ) ^ 4 * 1 * ((2 : ℝ) ^ 4 * A * ((2 : ℝ) ^ 4 * 3 * M + ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) + (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M))))
      ≤ 1000000 * A ^ 4 * (K + 1) * (α + 1) := by
    have heq : (2 : ℝ) ^ 4 * 1 * ((2 : ℝ) ^ 4 * A * ((2 : ℝ) ^ 4 * 3 * M + ((2 : ℝ) ^ 4 * α * ((2 : ℝ) ^ 4 * A * M) + (2 : ℝ) ^ 4 * α * (((5 : ℝ) + 1) * M))))
        = 12288 * (A * (A * (K + 1))) + (65536 * α * (A * (A * (A * (K + 1)))) + 24576 * α * (A * (A * (K + 1)))) := by
      rw [hM]; ring
    rw [heq]
    have hX : (0 : ℝ) ≤ A ^ 4 * (K + 1) * (α + 1) := by positivity
    have h1 := quad 12288 300000 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h2 := quad 65536 300000 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h3 := quad 24576 300000 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simp only [pow_zero, pow_one, one_mul, mul_one] at h1 h2 h3
    linarith
  exact ⟨hEUz.mono le_rfl hEUz_le, hEU.mono le_rfl hEU_le⟩

end Work.FTS.PhiStar.CoreAux
