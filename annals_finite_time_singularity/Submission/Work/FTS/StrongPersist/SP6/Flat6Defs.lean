/-
# `FTS/StrongPersist/SP6/Flat6Defs.lean` — the shared vocabulary of the order-six flat bounds

This file collects the definitions and the elementary API that the `FlatW 6`-bounds of the five
star fields (`EH`, `EVz`, `EV`, `EUz`, `EU`) are proved from.  Nothing here is a `sorry`.

## The target

The five fields are (on the open quadrant `Q0`)

* `EH α Y = 2Y + 2α sin²θ·(Y/(z+1) + D_zY) + D_θY`;
* `EVz Y = 2(cos²θ - 2 sin²θ)·Y + D_θY`,   `EV Y = (z/(z+1))·EVz Y`;
* `EUz α Y = -(3Y + α(Y/(z+1) + D_zY))`,  `EU α Y = (z/(z+1))·EUz α Y`,

with `D_zY = Yblk Y = z∂_zY` and `D_θY = Tblk Y = sin(2θ)∂_θY`.  They are *linear* in the three
blocks `Y`, `pth Y`, `Yblk Y`, so the flat calculus with the hypotheses

`F0 6 KY Y`,  `F0 6 (K + KY) (pth Y)`,  `F0 6 KD (Yblk Y)`

produces bounds that are *linear* in `KY`, `K` and `KD` — this is the reason the target constant
may be taken of the shape `C·(α+1)·(K + KY + KD)`.

## What is provided

* `pth_thetaOnly` — for a function of `θ` alone, `∂_θ` is the plain derivative;
* `coefFun` / `CoefBundle6s` — the ten coefficient functions (`sin²θ`, `cos²θ - 2 sin²θ`,
  `sin 2θ`, `cos 2θ`, their four `θ`-derivatives, `z/(1+z)`, `(1+z)⁻¹`) together with a single
  constant `A ≥ 1` such that each is `C^∞` on `Q0` and lies in `F0 6 A`.  `F0 6 A c` gives in
  particular `|(z+1)^k ∂_z^k D_θ^i c| ≤ A` (so also `|D_θ^i c| ≤ A`) for `k + i ≤ 6`;
* `atomData` — the bundle of the three block bounds above (plus the two *derived* block bounds
  `F0 5 (6(K+KY)) (Yblk (pth Y))` and `F0 5 (K+KY) (D_θ(pth Y))` that the `∂_θ`-slots need);
* `EHR/EHD`, `EVzR/EVzD`, `EVR/EVD`, `EUzR/EUzD`, `EUR/EUD` — the reassociated field
  expressions and their *candidate* `∂_θ`-derivative expressions, together with the pointwise
  identities `EHR = EH`, … (`ehEHR_eq` etc.).  The identity `pth (EHR α Y) = EHD α Y` on `Q0`
  is **not** proved here; it is the analytic step of the per-field proofs (it follows from the
  product rule `Fbq_pth_mul` on `Q0`, the coefficient derivatives `eh_pth_ph1`, `eh_pth_sin2`
  of `CoreAux/FbEHDefs.lean`, and `pth_zpz_smoothOpen`), and the consumer is free to use its own
  expression instead;
* `mono_const` — the arithmetic step that turns a bound of the shape `c·X`, `X ∈ {K, KY, KD}`,
  into `C·(α+1)·(K + KY + KD)`.

## The intended proof of a per-field bound

For a field `F` (say `EH α Y`), with `F := Σ_r coef_r · block_r` (`R`-expression):

1. `F0 6 F`: each summand `coef_r · block_r` is `F0_mul` of the coefficient (from `CoefBundle6s`
   and `F0_mul` for products such as `(1+z)⁻¹·sin²θ`) and the block (from `atomData`); sum with
   `F0_add` (each summand is `SmoothOpen`, by `smoothOpen_mul` of the two factors).
2. `F0 5 (pth F)`: on `Q0`, `pth F = D` (the `D`-expression), computed with the product rule
   `Fbq_pth_mul` / the sum rule `pth_add_Q0` / `pth_const_mul`, the coefficient derivatives
   `eh_pth_ph1`, `eh_pth_sin2`, and the two structural identities `pth_zpz_smoothOpen`
   (`pth (Yblk Y) = Yblk (pth Y)`) and `sin(2θ)·pth(pth Y) = D_θ(pth Y)` (definitional); then
   each summand of `D` is bounded by `F0_mul` against `atomData`, and the bound is transferred
   back with `F0_congr`.
3. `FlatW 6 F M` is `flatW6_of_F0 h1 h2` followed by `FlatW_mono`, and `FlatW_congr` transfers
   between `F` and the reassociated expression.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs
import Submission.Work.FTS.PhiStar.CoreAux.FbEHDefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_mul
import Submission.Work.FTS.PhiStar.CoreAux.F0_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_zpz
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr
import Submission.Work.FTS.PhiStar.CoreAux.Fb_basic
import Submission.Work.FTS.PhiStar.CoreAux.Fb_zpz
import Submission.Work.FTS.PhiStar.CoreAux.Fb_of_FlatW
import Submission.Work.FTS.PhiStar.FlatWApi.FlatW_add
import Submission.Work.FTS.PhiStar.FlatWApi.FlatW_congr
import Submission.Work.FTS.PhiStar.FlatWApi.FlatW_ycheckSmooth
import Submission.Work.FTS.StrongPersist.SP6.CoefBundle6
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `θ`-derivative of a function of `θ` alone -/

/-- For a function which depends on `θ` only, `∂_θ` is the plain derivative. -/
theorem pth_thetaOnly (φ : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (fun _ θ' => φ θ') z θ = deriv φ θ := rfl

/-! ## Two elementary transfers -/

/-- **Monotonicity of `FlatW` in its constant.** -/
theorem FlatW_mono6 {l : ℕ} {f : ℝ → ℝ → ℝ} {K K' : ℝ}
    (h : Work.FTS.VocabO2.FlatW l f K) (hle : K ≤ K') : Work.FTS.VocabO2.FlatW l f K' :=
  Work.FTS.PhiStar.FlatWApi.flatW_mono h hle

/-- **`FlatW 6` from the two `F0` components**: the first clause is the `i = 0` slot of
`F0 6`, the second is exactly `F0 5 (∂_θ f)`. -/
theorem flatW6_of_F0 {K : ℝ} {f : ℝ → ℝ → ℝ} (h1 : Work.FTS.PhiStar.F0 6 K f)
    (h2 : Work.FTS.PhiStar.F0 5 K (Work.Spaces.pth f)) :
    Work.FTS.VocabO2.FlatW 6 f K := by
  intro z θ hz hθ hθ'
  refine ⟨fun k hk => ?_, fun k i hki => h2 k i (by omega) z θ hz hθ hθ'⟩
  simpa using h1 k 0 (by omega) z θ hz hθ hθ'

/-- `∂_θ` respects agreement on the open quadrant (locality of `deriv`). -/
theorem pth_congr6 {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth f z θ = Work.Spaces.pth g z θ :=
  Work.FTS.PhiStar.CoreAux.pth_congr_Q0 h

/-! ## The ten coefficient functions and their bundle -/

/-- The ten coefficient functions of the order-six flat calculus: the four angular coefficients
`sin²θ`, `cos²θ - 2 sin²θ`, `sin 2θ`, `cos 2θ`; their four `θ`-derivatives; and the two radial
coefficients `z/(1+z)`, `(1+z)⁻¹`. -/
def coefFun : List (ℝ → ℝ → ℝ) :=
  [ fun _ θ => Real.sin θ ^ 2,
    fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2,
    fun _ θ => Real.sin (2 * θ),
    fun _ θ => Real.cos (2 * θ),
    fun _ θ => deriv (fun θ' => Real.sin θ' ^ 2) θ,
    fun _ θ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ,
    fun _ θ => deriv (fun θ' => Real.sin (2 * θ')) θ,
    fun _ θ => deriv (fun θ' => Real.cos (2 * θ')) θ,
    fun z _ => z / (1 + z),
    fun z _ => (1 + z)⁻¹ ]

/-- `∂_θ(sin²θ) = 2 sinθcosθ`. -/
theorem deriv_sin_sq (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin θ' ^ 2) θ = 2 * Real.sin θ * Real.cos θ := by
  have h := (Real.hasDerivAt_sin θ).pow 2
  simpa using h.deriv

/-- `∂_θ(cos²θ - 2 sin²θ) = -6 sinθcosθ`. -/
theorem deriv_cos_sq_sub (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ
      = -(6 * Real.sin θ * Real.cos θ) := by
  have h1 := (Real.hasDerivAt_cos θ).pow 2
  have h2 := ((Real.hasDerivAt_sin θ).pow 2).const_mul 2
  have h := h1.sub h2
  have hd := h.deriv
  have e : deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ
      = deriv ((Real.cos ^ 2) - fun y => 2 * (Real.sin ^ 2) y) θ := rfl
  rw [e, hd]
  ring_nf

/-- `∂_θ(sin 2θ) = 2 cos 2θ`. -/
theorem deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hd := h.deriv
  have e : deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = deriv (Real.sin ∘ HMul.hMul 2) θ := rfl
  rw [e, hd]
  ring

/-- `∂_θ(cos 2θ) = -2 sin 2θ`. -/
theorem deriv_cos_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.cos (2 * θ')) θ = -(2 * Real.sin (2 * θ)) := by
  have h := (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hd := h.deriv
  have e : deriv (fun θ' : ℝ => Real.cos (2 * θ')) θ = deriv (Real.cos ∘ HMul.hMul 2) θ := rfl
  rw [e, hd]
  ring

/-- **The coefficient bundle.**  There is a single constant `A ≥ 1` such that each of the ten
coefficient functions is `C^∞` on the open quadrant and lies in `F0 6 A`.

`F0 6 A c` gives in particular `|(z+1)^k ∂_z^k D_θ^i c| ≤ A` for `k + i ≤ 6` and hence, at
`k = 0`, `|D_θ^i c| ≤ A` — the form in which the coefficients are consumed pointwise. -/
theorem CoefBundle6s : ∃ A : ℝ, 1 ≤ A ∧ ∀ c ∈ coefFun,
    Work.FTS.PhiStar.F0 6 A c ∧ Work.FTS.EllipticEst.SmoothOpen c := by
  obtain ⟨A₀, hA₀1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := CoefBundle6
  -- smoothness of the four `θ`-derivative coefficients, via the explicit identities
  have s1 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin θ ^ 2) :=
    Work.FTS.PhiStar.CoreAux.eh_smooth_ph1
  have s2 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) :=
    Work.FTS.PhiStar.FlatWApi.smoothOpen_congr
      (Work.FTS.PhiStar.FlatWApi.smoothOpen_of_angular
        (fun n => by fun_prop))
      (fun _ θ _ _ _ => rfl)
  have s3 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin (2 * θ)) :=
    Work.FTS.PhiStar.CoreAux.eh_smooth_sin2
  have s4 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.cos (2 * θ)) :=
    Work.FTS.PhiStar.CoreAux.eh_smooth_cos2
  have e5 : (fun θ : ℝ => deriv (fun θ' => Real.sin θ' ^ 2) θ)
      = fun θ => 2 * Real.sin θ * Real.cos θ := by
    funext θ; exact deriv_sin_sq θ
  have e6 : (fun θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ)
      = fun θ => -(6 * Real.sin θ * Real.cos θ) := by
    funext θ; exact deriv_cos_sq_sub θ
  have e7 : (fun θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ)
      = fun θ => 2 * Real.cos (2 * θ) := by
    funext θ; exact deriv_sin_two θ
  have e8 : (fun θ : ℝ => deriv (fun θ' => Real.cos (2 * θ')) θ)
      = fun θ => -(2 * Real.sin (2 * θ)) := by
    funext θ; exact deriv_cos_two θ
  have s5 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => deriv (fun θ' => Real.sin θ' ^ 2) θ) := by
    rw [show (fun _ θ : ℝ => deriv (fun θ' => Real.sin θ' ^ 2) θ)
        = fun _ θ => 2 * Real.sin θ * Real.cos θ from by funext z θ; exact deriv_sin_sq θ]
    exact Work.FTS.PhiStar.FlatWApi.smoothOpen_of_angular (fun n => by fun_prop)
  have s6 : Work.FTS.EllipticEst.SmoothOpen
      (fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) := by
    rw [show (fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ)
        = fun _ θ => -(6 * Real.sin θ * Real.cos θ) from by funext z θ; exact deriv_cos_sq_sub θ]
    exact Work.FTS.PhiStar.FlatWApi.smoothOpen_of_angular (fun n => by fun_prop)
  have s7 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) := by
    rw [show (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ)
        = fun _ θ => 2 * Real.cos (2 * θ) from by funext z θ; exact deriv_sin_two θ]
    exact Work.FTS.PhiStar.FlatWApi.smoothOpen_of_angular (fun n => by fun_prop)
  have s8 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => deriv (fun θ' => Real.cos (2 * θ')) θ) := by
    rw [show (fun _ θ : ℝ => deriv (fun θ' => Real.cos (2 * θ')) θ)
        = fun _ θ => -(2 * Real.sin (2 * θ)) from by funext z θ; exact deriv_cos_two θ]
    exact Work.FTS.PhiStar.FlatWApi.smoothOpen_of_angular (fun n => by fun_prop)
  have s9 : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) :=
    Work.FTS.PhiStar.CoreAux.eh_smooth_rho
  have s10 : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (1 + z)⁻¹) :=
    Work.FTS.PhiStar.CoreAux.eh_smooth_rhoinv
  refine ⟨A₀, hA₀1, ?_⟩
  intro c hc
  simp only [coefFun, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨h1, s1⟩
  · exact ⟨h2, s2⟩
  · exact ⟨h3, s3⟩
  · exact ⟨h4, s4⟩
  · exact ⟨h5, s5⟩
  · exact ⟨h6, s6⟩
  · exact ⟨h7, s7⟩
  · exact ⟨h8, s8⟩
  · exact ⟨h9, s9⟩
  · exact ⟨h10, s10⟩

/-! ## The block bounds (the `atomData` bundle) -/

/-- **The block data.**  From the four hypotheses of the target (`FlatW 7 Y K`, `Fb 6 KY Y`,
`F0 6 KD (Yblk Y)`, `SmoothOpen Y`) one gets the bounds

* `F0 6 KY Y`, `F0 6 (K + KY) (pth Y)`, `F0 6 KD (Yblk Y)` — the three blocks;
* `F0 5 (6(K+KY)) (Yblk (pth Y))` — from `F0_zpz` applied to `F0 6 (K+KY) (pth Y)`;
* `F0 5 (K+KY) (D_θ(pth Y))` — from `F0_Dth` applied to `F0 6 (K+KY) (pth Y)`.

These are exactly the `F0`-facts used by the per-field estimates. -/
theorem atomData {K KY KD : ℝ} {Y : ℝ → ℝ → ℝ}
    (hK : 0 ≤ K) (hKY : 0 ≤ KY) (hKD : 0 ≤ KD) (hsm : Work.FTS.EllipticEst.SmoothOpen Y)
    (hW : Work.FTS.VocabO2.FlatW 7 Y K) (hFb : Work.FTS.PhiStar.Fb 6 KY Y)
    (hD : Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y)) :
    Work.FTS.PhiStar.F0 6 KY Y ∧
    Work.FTS.PhiStar.F0 6 (K + KY) (Work.Spaces.pth Y) ∧
    Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) ∧
    Work.FTS.PhiStar.F0 5 (6 * (K + KY)) (Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y)) ∧
    Work.FTS.PhiStar.F0 5 (K + KY) (Work.Spaces.Dth (Work.Spaces.pth Y)) := by
  have hK0 : (0 : ℝ) ≤ K + KY := by linarith
  have hP : Work.FTS.PhiStar.F0 6 (K + KY) (Work.Spaces.pth Y) :=
    (Work.FTS.PhiStar.CoreAux.F0_six_pth_of_FlatW hW).mono le_rfl (by linarith)
  have hZp : Work.FTS.PhiStar.F0 5 (6 * (K + KY))
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pth Y) z θ) :=
    (Work.FTS.PhiStar.CoreAux.F0_zpz (n := 5) hK0 hsm.pth hP).mono le_rfl (by norm_num)
  refine ⟨hFb.f0, hP, hD, ?_, ?_⟩
  · exact Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => rfl) hZp
  · exact Work.FTS.PhiStar.CoreAux.F0_Dth (n := 5) hP

/-! ## The arithmetic of the constant -/

/-- **Constant normalisation.**  A bound `c · X` with `0 ≤ c ≤ C`, `0 ≤ X ≤ K + KY + KD` is
dominated by `C · (α + 1) · (K + KY + KD)` for `α ≥ 0`. -/
theorem mono_const {C α K KY KD X c : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K) (hKY : 0 ≤ KY)
    (hKD : 0 ≤ KD) (hX0 : 0 ≤ X) (hX : X ≤ K + KY + KD) (hc0 : 0 ≤ c) (hcC : c ≤ C) :
    c * X ≤ C * (α + 1) * (K + KY + KD) := by
  have h1 : c * X ≤ C * X := mul_le_mul_of_nonneg_right hcC hX0
  have h2 : C * X ≤ C * (K + KY + KD) :=
    mul_le_mul_of_nonneg_left hX (le_trans hc0 hcC)
  have hC0 : (0 : ℝ) ≤ C := le_trans hc0 hcC
  have h3 : C * (K + KY + KD) ≤ C * (α + 1) * (K + KY + KD) := by
    have hsum : (0 : ℝ) ≤ K + KY + KD := by linarith
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hsum (by linarith)) hC0
  linarith

/-! ## The five fields: reassociated expressions and their `θ`-derivative expressions -/

/-- `EH α Y = 2Y + 2α sin²θ·(Y/(z+1) + D_zY) + D_θY`, reassociated into products of
coefficients with the three blocks `Y`, `Yblk Y`, `pth Y`. -/
def EHR (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  2 * Y z θ
    + (2 * α) * ((1 + z)⁻¹ * Real.sin θ ^ 2) * Y z θ
    + (2 * α) * Real.sin θ ^ 2 * Work.FTS.PhiStar.Yblk Y z θ
    + Real.sin (2 * θ) * Work.Spaces.pth Y z θ

/-- The candidate `∂_θ`-derivative of `EHR`: the product rule applied to the four summands. -/
def EHD (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  2 * Work.Spaces.pth Y z θ
    + (2 * α) * ((1 + z)⁻¹ * deriv (fun θ' => Real.sin θ' ^ 2) θ) * Y z θ
    + (2 * α) * ((1 + z)⁻¹ * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ
    + (2 * α) * deriv (fun θ' => Real.sin θ' ^ 2) θ * Work.FTS.PhiStar.Yblk Y z θ
    + (2 * α) * Real.sin θ ^ 2 * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ
    + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ
    + Work.Spaces.Dth (Work.Spaces.pth Y) z θ

/-- **`EHR` is `EH`** (pure reassociation, no quadrant hypothesis). -/
theorem ehEHR_eq (α : ℝ) (Y : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.PhiStar.EH α Y z θ = EHR α Y z θ := by
  simp only [Work.FTS.PhiStar.EH, Work.FTS.PhiStar.Tblk, EHR, Work.Construction.s2,
    div_eq_mul_inv]
  try ring

/-- `EVz Y = 2(cos²θ - 2 sin²θ)·Y + D_θY`, reassociated. -/
def EVzR (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Y z θ
    + Real.sin (2 * θ) * Work.Spaces.pth Y z θ

/-- The candidate `∂_θ`-derivative of `EVzR`. -/
def EVzD (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
    + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ
    + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ
    + Work.Spaces.Dth (Work.Spaces.pth Y) z θ

/-- **`EVzR` is `EVz`**. -/
theorem evzEVzR_eq (Y : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.PhiStar.EVz Y z θ = EVzR Y z θ := by
  simp only [Work.FTS.PhiStar.EVz, Work.FTS.PhiStar.Tblk, EVzR, Work.Construction.s2]
  try ring

/-- `EV Y = (z/(z+1))·EVz Y`. -/
def EVR (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => (z / (1 + z)) * EVzR Y z θ

/-- The candidate `∂_θ`-derivative of `EVR`.  It does not depend on `θ`, so the factor
`z/(1+z)` simply goes through. -/
def EVD (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => (z / (1 + z)) * EVzD Y z θ

/-- **`EVR` is `EV`**. -/
theorem evEVR_eq (Y : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.PhiStar.EV Y z θ = EVR Y z θ := by
  simp only [Work.FTS.PhiStar.EV, EVR]
  rw [evzEVzR_eq Y z θ, show z / (z + 1) = z / (1 + z) by rw [add_comm]]

/-- `EUz α Y = -(3Y + α(Y/(z+1) + D_zY))`, reassociated. -/
def EUzR (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -(3 * Y z θ + α * ((1 + z)⁻¹ * Y z θ) + α * Work.FTS.PhiStar.Yblk Y z θ)

/-- The candidate `∂_θ`-derivative of `EUzR`. -/
def EUzD (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  -(3 * Work.Spaces.pth Y z θ + α * ((1 + z)⁻¹ * Work.Spaces.pth Y z θ)
    + α * Work.FTS.PhiStar.Yblk (Work.Spaces.pth Y) z θ)

/-- **`EUzR` is `EUz`**. -/
theorem euzEUzR_eq (α : ℝ) (Y : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.PhiStar.EUz α Y z θ = EUzR α Y z θ := by
  simp only [Work.FTS.PhiStar.EUz, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, EUzR,
    div_eq_mul_inv]
  try ring

/-- `EU α Y = (z/(z+1))·EUz α Y`. -/
def EUR (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => (z / (1 + z)) * EUzR α Y z θ

/-- The candidate `∂_θ`-derivative of `EUR`. -/
def EUD (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => (z / (1 + z)) * EUzD α Y z θ

/-- **`EUR` is `EU`**. -/
theorem euEUR_eq (α : ℝ) (Y : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.PhiStar.EU α Y z θ = EUR α Y z θ := by
  simp only [Work.FTS.PhiStar.EU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk, EUR, EUzR,
    div_eq_mul_inv]
  try ring_nf

end Work.FTS.StrongPersist.SP6
