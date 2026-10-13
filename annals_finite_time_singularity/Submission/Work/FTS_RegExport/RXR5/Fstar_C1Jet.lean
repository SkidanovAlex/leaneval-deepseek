/-
# `Work.FTS_RegExport.RXR5.Fstar_C1Jet` — the static-profile `C1Jet` slots of `R5Parts`

The assembly `Work.FTS.RegPkgGal.Der.R5Parts_of_pieces` consumes three `C1Jet`-regularity slots
of the **static profile** `F_* = Work.Construction.Fstar (pExp α)`:

* `L₁₂(F_*)(z) = 2·pExp α/(1+z)` (radial, constant in `θ` and `τ`) — `Der.jet_L12_Fstar` plus
  the explicit `z`-derivative;
* `D_θF_* = sin(2θ)·∂_θF_*` — on the open quadrant this factors as
  `(pExp α)²·(q(θ)Γ(θ)/c)·F̂(z)` (`rl1Tools.FzShape`), and both endpoints `θ = 0, π/2` are zeros
  of the factorisation as well, so the factorisation is *global* on `Iθ`;
* `D_zF_* = z·∂_zF_*` — on `z > -1` it factors as `pzCoeff α θ · (z·F̂'(z))`
  (`rl1Tools.FzShape`), where `pzCoeff α θ = (pExp α)·(Γ(θ)/c)`.

Each of the last two slots is a product `f θ · g z` of an angular factor and a radial factor, so
the proof is packaged once and for all:

* `jet_of_bound_modulus` — a pointwise bound `M` and a "modulus" `A|Δz| + B|Δθ|^α` give a `Jet`
  with constant `max (2M) (A + B)` (the `2M` accounts for the modulus being applied to the
  *difference*; the `max` is `Regularity.join_rpow_le`);
* `c1jet_prod` — if in addition `z ↦ g z` is differentiable on `z > 0` with a uniform bound `Dg`
  on its derivative, the product is a `C1Jet` with constant
  `max (max (2·Mf·Mg) (Mf·Cg + Cf·Mg)) (Mf·Dg)`.

The numerical data of the three slots:

| slot | `Mf` | `Cf` | `Mg` | `Cg` | `Dg` | constant |
|---|---|---|---|---|---|---|
| `L₁₂F_*` | `2 pExp α` | `0` | `1` | `1` | `1` | `2 pExp α` |
| `D_θF_*` | `40/3` | `60` | `1/2` | `2` | `2` | `170/3` |
| `D_zF_*` | `10` | `30` | `1/2` | `8` | `8` | `95` |

The angular moduli are `DthCoeff_holder` (`q Γ` is `6`-Hölder: `q` is `2`-Lipschitz and `Γ` is
`3^α`-Hölder) and `pzCoeff_holder`; the radial data are `Moduli.fstarLip` (`2`-Lipschitz),
`deriv_FM_Fstar_abs_le` (`|F̂'| ≤ 2`), and `hhat_lip`/`hhat_abs_le`/`hasDerivAt_hhat` for
`z ↦ z·F̂'(z)` (`8`-Lipschitz, `≤ 1/2`, derivative `2(1-4z+z²)/(1+z)⁴`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Der.Defs
import Submission.Work.FTS.RegPkgGal.Der.C1JetFstar
import Submission.Work.FTS.RegPkgGal.Der.jet_L12_Fstar
import Submission.Work.FTS.Regularity.gammaFstarModuli
import Submission.Work.FTS.Regularity.pzFstarModuli
import Submission.Work.FTS.Regularity.regPkg_inhabited
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §1 The generic `Jet`/`C1Jet` constructions -/

/-- **Monotonicity of `Jet` in its constant.** -/
theorem jet_mono {α S N N' : ℝ} (h : N ≤ N') {f : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.Regularity.Jet α S N f) : Work.FTS.Regularity.Jet α S N' f :=
  ⟨le_trans H.1 h, fun z θ τ hz hθ hτ => le_trans (H.2.1 z θ τ hz hθ hτ) h,
    fun z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ' =>
      le_trans (H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ')
        (mul_le_mul_of_nonneg_right h (Real.rpow_nonneg (by positivity) α))⟩

/-- **A pointwise bound plus a `(z,θ)`-modulus give a `Jet`.**  A function `h` of `(z,θ)` which is
bounded by `M` on the strip and satisfies `|h z θ - h z' θ'| ≤ A|z - z'| + B|θ - θ'|^α` is a
`Jet` with constant `max (2M) (A + B)`: the `2M` accounts for the difference in the modulus, and
the `max` is `Regularity.join_rpow_le`. -/
theorem jet_of_bound_modulus {α S M A B : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B) {h : ℝ → ℝ → ℝ}
    (hb : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |h z θ| ≤ M)
    (hm : ∀ z z' θ θ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |h z θ - h z' θ'| ≤ A * |z - z'| + B * |θ - θ'| ^ α) :
    Work.FTS.Regularity.Jet α S (max (2 * M) (A + B)) (fun z θ _ => h z θ) := by
  refine Work.FTS.Regularity.Jet.of_bounded_holder (le_trans (by linarith) (le_max_left _ _))
    hα.le ?_ ?_
  · intro z θ hz hθ
    exact le_trans (hb z θ hz hθ) (le_trans (by linarith) (le_max_left _ _))
  · intro z z' θ θ' hz hz' hθ hθ'
    have hx2M : |h z θ - h z' θ'| ≤ 2 * M := by
      have h1 := hb z θ hz hθ
      have h2 := hb z' θ' hz' hθ'
      calc |h z θ - h z' θ'| ≤ |h z θ| + |h z' θ'| := by
            simpa using abs_sub_le (h z θ) 0 (h z' θ')
        _ ≤ M + M := add_le_add h1 h2
        _ = 2 * M := by ring
    exact Work.FTS.Regularity.join_rpow_le hα hα1 (by linarith) hA hB
      (abs_nonneg _) (abs_nonneg _) hx2M (hm z z' θ θ' hz hz' hθ hθ')

/-- **The bound and the `(z,θ)`-modulus of a product `f θ · g z`.**  The product is bounded by
`Mf·Mg`, and its modulus is `Mf·Cg·|Δz| + Cf·Mg·|Δθ|^α` (split the difference at `(z',θ)`). -/
theorem prod_bound_modulus {α Mf Mg Cf Cg : ℝ} (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) {f : ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ Mf) (hg : ∀ z, 0 ≤ z → |g z| ≤ Mg)
    (hfm : ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ, |f θ - f θ'| ≤ Cf * |θ - θ'| ^ α)
    (hgm : ∀ z, 0 ≤ z → ∀ z', 0 ≤ z' → |g z - g z'| ≤ Cg * |z - z'|) :
    (∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |f θ * g z| ≤ Mf * Mg) ∧
    (∀ z z' θ θ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
        |f θ * g z - f θ' * g z'| ≤ Mf * Cg * |z - z'| + Cf * Mg * |θ - θ'| ^ α) := by
  constructor
  · intro z θ hz hθ
    rw [abs_mul]
    exact mul_le_mul (hf θ hθ) (hg z hz) (abs_nonneg _) hMf
  · intro z z' θ θ' hz hz' hθ hθ'
    have hkey : f θ * g z - f θ' * g z' = f θ * (g z - g z') + (f θ - f θ') * g z' := by ring
    rw [hkey]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul]
    have h1 : |f θ| * |g z - g z'| ≤ Mf * (Cg * |z - z'|) :=
      mul_le_mul (hf θ hθ) (hgm z hz z' hz') (abs_nonneg _) hMf
    have h2 : |f θ - f θ'| * |g z'| ≤ (Cf * |θ - θ'| ^ α) * Mg :=
      mul_le_mul (hfm θ hθ θ' hθ') (hg z' hz') (abs_nonneg _)
        (mul_nonneg hCf (Real.rpow_nonneg (abs_nonneg _) α))
    calc |f θ| * |g z - g z'| + |f θ - f θ'| * |g z'|
        ≤ Mf * (Cg * |z - z'|) + (Cf * |θ - θ'| ^ α) * Mg := add_le_add h1 h2
      _ = Mf * Cg * |z - z'| + Cf * Mg * |θ - θ'| ^ α := by ring

/-- **The product `f θ · g z` is a `C1Jet`.**  `jet_of_bound_modulus` and `prod_bound_modulus`
give the `Jet` half, and the product rule gives the `z`-derivative half (bounded by `Mf·Dg`). -/
theorem c1jet_prod {α S Mf Mg Cf Cg Dg : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hDg : 0 ≤ Dg)
    {f : ℝ → ℝ} {g : ℝ → ℝ}
    (hfb : ∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ Mf)
    (hgb : ∀ z, 0 ≤ z → |g z| ≤ Mg)
    (hfm : ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ, |f θ - f θ'| ≤ Cf * |θ - θ'| ^ α)
    (hgm : ∀ z, 0 ≤ z → ∀ z', 0 ≤ z' → |g z - g z'| ≤ Cg * |z - z'|)
    (hgd : ∀ z, 0 < z → ∃ d, HasDerivAt g d z ∧ |d| ≤ Dg) :
    Work.FTS.RegPkgGal.C1Jet α S (max (max (2 * (Mf * Mg)) (Mf * Cg + Cf * Mg)) (Mf * Dg))
      (fun z θ _ => f θ * g z) := by
  have hMfMg : 0 ≤ Mf * Mg := mul_nonneg hMf hMg
  have hCfMg : 0 ≤ Cf * Mg := mul_nonneg hCf hMg
  have hMfCg : 0 ≤ Mf * Cg := mul_nonneg hMf hCg
  have hMfDg : 0 ≤ Mf * Dg := mul_nonneg hMf hDg
  have hbm := prod_bound_modulus (α := α) hMf hMg hCf hCg hfb hgb hfm hgm
  refine ⟨jet_mono (le_max_left _ _) (jet_of_bound_modulus hα hα1 hMfMg hMfCg hCfMg
      hbm.1 (fun z z' θ θ' hz hz' hθ hθ' => ?_)), ?_⟩
  · exact hbm.2 z z' θ θ' hz hz' hθ hθ'
  · intro τ _hτ θ hθ z hz
    obtain ⟨d, hd, hdb⟩ := hgd z hz
    exact ⟨f θ * d, hd.const_mul (f θ), by
      rw [abs_mul]
      exact le_trans (mul_le_mul (hfb θ hθ) hdb (abs_nonneg _) hMf) (le_max_right _ _)⟩

/-- **Transport of a `C1Jet` along a pointwise equality on the strip** (the `Jet` half by
`Jet.congr`, the `z`-derivative half by `HasDerivAt.congr_of_eventuallyEq`, using that
`Ioi 0` is a neighbourhood of each of its points). -/
theorem c1jet_congr {α S N : ℝ} {a b : ℝ → ℝ → ℝ → ℝ}
    (Ha : Work.FTS.RegPkgGal.C1Jet α S N a)
    (h : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → a z θ τ = b z θ τ) :
    Work.FTS.RegPkgGal.C1Jet α S N b := by
  refine ⟨Ha.jet.congr h, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨d, hd, hdb⟩ := Ha.zderiv τ hτ θ hθ z hz
  refine ⟨d, hd.congr_of_eventuallyEq ?_, hdb⟩
  filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
  exact (h z' θ τ hz'.le hθ hτ).symm

/-! ## §2 The angular data -/

/-- `Γ` at the profile exponent vanishes at `θ = 0`. -/
theorem gamP_zero {p : ℝ} (hp : 0 < p) : Work.Spaces.Gam p 0 = 0 := by
  rw [Work.Spaces.Gam]
  norm_num
  exact Real.zero_rpow (by positivity)

/-- `Γ` at the profile exponent vanishes at `θ = π/2`. -/
theorem gamP_pi_half {p : ℝ} (hp : 0 < p) : Work.Spaces.Gam p (π / 2) = 0 := by
  rw [Work.Spaces.Gam, Real.cos_pi_div_two]
  norm_num
  exact Real.zero_rpow (by positivity)

/-- `q(θ) = cos 2θ - 1/3` is bounded by `4/3`. -/
theorem qfun_abs_le {θ : ℝ} : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
  rw [Work.Spaces.qfun_apply]
  have h1 := Real.neg_one_le_cos (2 * θ)
  have h2 := Real.cos_le_one (2 * θ)
  rw [abs_le]
  constructor <;> linarith

/-- `q` is `2`-Lipschitz (`qfun θ = cos 2θ - 1/3`). -/
theorem qfun_lip (θ θ' : ℝ) : |Work.Spaces.qfun θ - Work.Spaces.qfun θ'| ≤ 2 * |θ - θ'| := by
  rw [Work.Spaces.qfun_apply, Work.Spaces.qfun_apply]
  have h := Real.abs_cos_sub_cos_le (2 * θ) (2 * θ')
  have h1 : (Real.cos (2 * θ) - 1 / 3) - (Real.cos (2 * θ') - 1 / 3)
      = Real.cos (2 * θ) - Real.cos (2 * θ') := by ring
  rw [h1]
  calc |Real.cos (2 * θ) - Real.cos (2 * θ')| ≤ |2 * θ - 2 * θ'| := h
    _ = 2 * |θ - θ'| := by
        rw [show 2 * θ - 2 * θ' = 2 * (θ - θ') by ring, abs_mul]
        norm_num

/-- The angular coefficient `q(θ)Γ(θ)` of `D_θF_*` is bounded by `4/3` on `Iθ`. -/
theorem qGam_abs_le {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.qfun θ * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ| ≤ 4 / 3 := by
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  obtain ⟨hg0, hg1⟩ := Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ hp hθ
  rw [abs_mul, abs_of_nonneg hg0]
  calc |Work.Spaces.qfun θ| * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
      ≤ (4 / 3) * 1 := mul_le_mul (qfun_abs_le (θ := θ)) hg1 hg0 (by norm_num)
    _ = 4 / 3 := by ring

/-- The angular coefficient `q(θ)Γ(θ)` of `D_θF_*` is `α`-Hölder on `Iθ` with constant `6`:
`q` is `2`-Lipschitz, `Γ` is `3^α`-Hölder and both are bounded. -/
theorem qGam_holder {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {θ θ' : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |Work.Spaces.qfun θ * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        - Work.Spaces.qfun θ' * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'|
      ≤ 6 * |θ - θ'| ^ α := by
  have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  obtain ⟨hg0, _⟩ := Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ hp hθ
  obtain ⟨hg0', hg1'⟩ := Work.Spaces.Gam_bounds (Work.FTS.Regularity.pExp α) θ' hp hθ'
  have hG := Work.FTS.Regularity.gam_three_holder hα hα13 hθ hθ'
  have hq := qfun_lip θ θ'
  have hkey : Work.Spaces.qfun θ * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
      - Work.Spaces.qfun θ' * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'
      = Work.Spaces.qfun θ * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ')
        + (Work.Spaces.qfun θ - Work.Spaces.qfun θ')
            * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ' := by ring
  rcases le_or_gt |θ - θ'| 1 with hcase | hcase
  · have hpow : |θ - θ'| ≤ |θ - θ'| ^ α :=
      Work.FTS.Regularity.self_le_rpow_of_le_one hα hα1 (abs_nonneg _) hcase
    have h3 : (3 : ℝ) ^ α ≤ 3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hα1
      simpa using h
    have hp0 : 0 ≤ |θ - θ'| ^ α := Real.rpow_nonneg (abs_nonneg _) α
    have h4 : (4 / 3) * (3 ^ α * |θ - θ'| ^ α) ≤ 4 * |θ - θ'| ^ α := by
      have := mul_le_mul_of_nonneg_right h3 hp0
      linarith
    rw [hkey]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul]
    have hb1 : |Work.Spaces.qfun θ| * |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          - Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'|
        ≤ (4 / 3) * (3 ^ α * |θ - θ'| ^ α) :=
      mul_le_mul (qfun_abs_le (θ := θ)) hG (abs_nonneg _) (by norm_num)
    have hb2 : |Work.Spaces.qfun θ - Work.Spaces.qfun θ'|
          * |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'| ≤ (2 * |θ - θ'|) * 1 := by
      have h2 : |Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'| ≤ 1 := by
        rw [abs_of_nonneg hg0']
        exact hg1'
      exact mul_le_mul hq h2 (abs_nonneg _) (by positivity)
    linarith [hb1, hb2, h4, hpow]
  · have hbig : (1 : ℝ) ≤ |θ - θ'| ^ α := Real.one_le_rpow hcase.le hα.le
    have htri : |Work.Spaces.qfun θ * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        - Work.Spaces.qfun θ' * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'| ≤ 8 / 3 := by
      calc _ ≤ |Work.Spaces.qfun θ * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ|
              + |Work.Spaces.qfun θ' * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'| := by
            simpa using abs_sub_le
              (Work.Spaces.qfun θ * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ) 0
              (Work.Spaces.qfun θ' * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ')
        _ ≤ 4 / 3 + 4 / 3 := add_le_add (qGam_abs_le hα hθ) (qGam_abs_le hα hθ')
        _ = 8 / 3 := by ring
    nlinarith [htri, hbig]

/-- The angular coefficient `A(θ) = (pExp α)²·(q(θ)Γ(θ)/c)` of `D_θF_*`. -/
noncomputable def DthCoeff (α : ℝ) : ℝ → ℝ :=
  fun θ => (Work.FTS.Regularity.pExp α) ^ 2
    * (Work.Spaces.qfun θ * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp α))

/-- The coefficient `A(θ)` split as `((pExp α)²/c)·(q Γ)`. -/
theorem DthCoeff_shape (α θ : ℝ) :
    DthCoeff α θ = (Work.FTS.Regularity.pExp α) ^ 2 / Work.Spaces.c (Work.FTS.Regularity.pExp α)
      * (Work.Spaces.qfun θ * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ) := by
  simp only [DthCoeff]
  ring

/-- The coefficient `(pExp α)²/c` of `DthCoeff` is at most `10` (`c ≥ 1/10`, `pExp α ≤ 1`). -/
theorem DthCoeff_coef_le {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    (Work.FTS.Regularity.pExp α) ^ 2 / Work.Spaces.c (Work.FTS.Regularity.pExp α) ≤ 10 := by
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hc := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hp hp1
  rw [div_le_iff₀ (by linarith [hc.1] : (0 : ℝ) < Work.Spaces.c (Work.FTS.Regularity.pExp α))]
  nlinarith [hc.1, hp1, hp.le]

/-- `|A(θ)| ≤ 40/3` on `Iθ`. -/
theorem DthCoeff_abs_le {α θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) : |DthCoeff α θ| ≤ 40 / 3 := by
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hc := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hp
    (Work.FTS.Regularity.pExp_le_one hα13)
  have hcpos : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by linarith [hc.1]
  rw [DthCoeff_shape, abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) hcpos.le)]
  calc (Work.FTS.Regularity.pExp α) ^ 2 / Work.Spaces.c (Work.FTS.Regularity.pExp α)
        * |Work.Spaces.qfun θ * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ|
      ≤ 10 * (4 / 3) := mul_le_mul (DthCoeff_coef_le hα hα13) (qGam_abs_le hα hθ)
          (abs_nonneg _) (by norm_num)
    _ = 40 / 3 := by ring

/-- `A` is `α`-Hölder on `Iθ` with constant `60`. -/
theorem DthCoeff_holder {α θ θ' : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) (hθ' : θ' ∈ Work.Spaces.Iθ) :
    |DthCoeff α θ - DthCoeff α θ'| ≤ 60 * |θ - θ'| ^ α := by
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hc := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp α) hp
    (Work.FTS.Regularity.pExp_le_one hα13)
  have hcpos : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp α) := by linarith [hc.1]
  have hshape : DthCoeff α θ - DthCoeff α θ'
      = (Work.FTS.Regularity.pExp α) ^ 2 / Work.Spaces.c (Work.FTS.Regularity.pExp α)
        * (Work.Spaces.qfun θ * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            - Work.Spaces.qfun θ' * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ') := by
    rw [DthCoeff_shape, DthCoeff_shape]
    ring
  rw [hshape, abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) hcpos.le)]
  calc (Work.FTS.Regularity.pExp α) ^ 2 / Work.Spaces.c (Work.FTS.Regularity.pExp α)
        * |Work.Spaces.qfun θ * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            - Work.Spaces.qfun θ' * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ'|
      ≤ 10 * (6 * |θ - θ'| ^ α) := mul_le_mul (DthCoeff_coef_le hα hα13)
          (qGam_holder hα hα13 hθ hθ') (abs_nonneg _) (by norm_num)
    _ = 60 * |θ - θ'| ^ α := by ring

/-! ## §3 The radial data -/

/-- The explicit form of `z ↦ z·F̂'(z)` on the physical half-line. -/
theorem hhat_eq {z : ℝ} (hz : 0 ≤ z) :
    z * deriv Work.FM.Fstar z = 2 * z * (1 - z) / (1 + z) ^ 3 := by
  rw [Work.FM.deriv_Fstar z (by linarith)]
  ring

/-- `|z·F̂'(z)| ≤ 1/2` on `z ≥ 0`. -/
theorem hhat_abs_le {z : ℝ} (hz : 0 ≤ z) : |z * deriv Work.FM.Fstar z| ≤ 1 / 2 := by
  rw [hhat_eq hz, abs_div, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hz,
    abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ 3)]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 3)]
  have h1 : |1 - z| ≤ 1 + z := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith [h1, hz, sq_nonneg (1 - z), sq_nonneg z]

/-- The derivative of the explicit form `y ↦ 2y(1-y)/(1+y)³` is `2(1-4y+y²)/(1+y)⁴`. -/
theorem hasDerivAt_hhat_explicit (x : ℝ) (hx : -1 < x) :
    HasDerivAt (fun y : ℝ => 2 * y * (1 - y) / (1 + y) ^ 3)
      (2 * (1 - 4 * x + x ^ 2) / (1 + x) ^ 4) x := by
  have hnum : HasDerivAt (fun y : ℝ => 2 * y * (1 - y)) (2 * (1 - 2 * x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id' (𝕜 := ℝ) x).const_sub 1
    have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id' (𝕜 := ℝ) x).const_mul 2
    convert h2.mul h1 using 1
    ring
  have hden : HasDerivAt (fun y : ℝ => (1 + y) ^ 3) (3 * (1 + x) ^ 2) x := by
    have h := (Work.FM.hasDerivAt_add_const 1 x).pow 3
    convert h using 1
    ring
  have hne : (1 + x) ^ 3 ≠ 0 := by
    have h1 : (0 : ℝ) < 1 + x := by linarith
    positivity
  have hdiv := hnum.div hden hne
  convert hdiv using 1
  · field_simp
    ring

/-- The derivative of `z ↦ z·F̂'(z)` at `z > 0`. -/
theorem hasDerivAt_hhat {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w * deriv Work.FM.Fstar w)
      (2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4) z := by
  have hz1 : -1 < z := by linarith
  have hev : (fun w : ℝ => w * deriv Work.FM.Fstar w)
      =ᶠ[𝓝 z] (fun y : ℝ => 2 * y * (1 - y) / (1 + y) ^ 3) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz1] with w hw
    rw [Work.FM.deriv_Fstar w hw]
    ring
  exact (hasDerivAt_hhat_explicit z hz1).congr_of_eventuallyEq hev

/-- `|2(1-4z+z²)/(1+z)⁴| ≤ 8` on `z ≥ 0`. -/
theorem hhat_deriv_abs_le {z : ℝ} (hz : 0 ≤ z) :
    |2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4| ≤ 8 := by
  have h1 : |1 - 4 * z + z ^ 2| ≤ 4 * (1 + z) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z, hz]
  rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ 4)]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 4)]
  nlinarith [h1, sq_nonneg (1 + z), hz]

/-- `z ↦ z·F̂'(z)` is `8`-Lipschitz on `z ≥ 0` (mean value theorem on `[0,∞)`). -/
theorem hhat_lip {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |z * deriv Work.FM.Fstar z - z' * deriv Work.FM.Fstar z'| ≤ 8 * |z - z'| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => 2 * y * (1 - y) / (1 + y) ^ 3)
    (f' := fun y : ℝ => 2 * (1 - 4 * y + y ^ 2) / (1 + y) ^ 4)
    (s := Set.Ici 0) (C := 8) (x := z') (y := z)
    (fun y hy =>
      (hasDerivAt_hhat_explicit y (by have := Set.mem_Ici.mp hy; linarith)).hasDerivWithinAt)
    (fun y hy => hhat_deriv_abs_le (Set.mem_Ici.mp hy))
    (convex_Ici 0) hz' hz
  rw [show z * deriv Work.FM.Fstar z - z' * deriv Work.FM.Fstar z'
      = 2 * z * (1 - z) / (1 + z) ^ 3 - 2 * z' * (1 - z') / (1 + z') ^ 3 from by
    rw [Work.FM.deriv_Fstar z (by linarith), Work.FM.deriv_Fstar z' (by linarith)]
    ring]
  simpa [Real.norm_eq_abs] using h

/-! ## §4 The pointwise factorisations of the profile's derivatives -/

/-- **`D_θF_* = DthCoeff α θ · F̂(z)` globally on `Iθ`.**  On the open quadrant this is
`rl1Tools.FzShape`; at the endpoints `θ = 0, π/2` both sides vanish (the `sin(2θ)` of `D_θ`, and
`Γ(θ) = 0`). -/
theorem Dth_Fstar_eq {α z θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Dth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      = DthCoeff α θ * Work.FM.Fstar z := by
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    rw [Work.Spaces.Dth, mul_zero, Real.sin_zero, zero_mul]
    simp only [DthCoeff, gamP_zero hp, mul_zero, zero_div, zero_mul]
  · rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · have h := (Work.FTS.Nonlinear.Pieces.rl1Tools.FzShape
        (Work.FTS.Regularity.pExp α) hp).2.1 z θ h0 h1
      rw [h]
      rfl
    · subst h1
      rw [Work.Spaces.Dth, show 2 * (π / 2) = π by ring, Real.sin_pi, zero_mul]
      simp only [DthCoeff, gamP_pi_half hp, mul_zero, zero_div, zero_mul]

/-- **`D_zF_* = pzCoeff α θ · (z·F̂'(z))` on `z ≥ 0`** (`rl1Tools.FzShape`). -/
theorem Dz_Fstar_eq {α z θ : ℝ} (hα : 0 < α) (hz : 0 ≤ z) :
    Work.Spaces.Dz (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      = Work.FTS.Regularity.pzCoeff α θ * (z * deriv Work.FM.Fstar z) := by
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hz1 : -1 < z := by linarith
  have h := (Work.FTS.Nonlinear.Pieces.rl1Tools.FzShape (Work.FTS.Regularity.pExp α) hp).2.2
    z θ hz1
  rw [h]
  rfl

/-- The explicit value of the `L₁₂`-image of the static profile. -/
theorem L12f_Fstar_eq {α z : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hz : 0 ≤ z) :
    Work.Coercivity.L12f (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z
      = 2 * Work.FTS.Regularity.pExp α / (1 + z) := by
  rw [show Work.Coercivity.L12f
        (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
      = Work.Construction.L12 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) from rfl,
    Work.Construction.L12_Fstar_eq (Work.FTS.Regularity.pExp_pos hα)
      (Work.FTS.Regularity.pExp_le_one hα13) hz]

/-! ## §5 The three `C1Jet` slots -/

/-- **The `L₁₂`-slot of the static profile.**  The `Jet` half is `Der.jet_L12_Fstar`; the
`z`-derivative half uses the explicit value `L₁₂(F_*)(z) = 2·pExp α/(1+z)`. -/
theorem C1Jet_L12f_Fstar {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S) :
    ∃ N : ℝ, 0 ≤ N ∧ Work.FTS.RegPkgGal.C1Jet α S N
      (fun z θ τ => Work.Coercivity.L12f
        (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z) := by
  obtain ⟨N, hNjet⟩ := Work.FTS.RegPkgGal.Der.jet_L12_Fstar hα hα13 hS
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  refine ⟨max N (2 * Work.FTS.Regularity.pExp α), ?_, jet_mono (le_max_left _ _) hNjet, ?_⟩
  · exact le_trans hNjet.1 (le_max_left _ _)
  · intro τ _hτ θ _hθ z hz
    have hz' : (0 : ℝ) < z := hz
    refine ⟨-(2 * Work.FTS.Regularity.pExp α) / (1 + z) ^ 2, ?_, ?_⟩
    · have hbase : HasDerivAt (fun z' : ℝ => 2 * Work.FTS.Regularity.pExp α / (1 + z'))
          (-(2 * Work.FTS.Regularity.pExp α) / (1 + z) ^ 2) z := by
        have h := Work.FM.hasDerivAt_div_add_const (2 * Work.FTS.Regularity.pExp α) 1 z
          (by linarith)
        simpa using h
      refine hbase.congr_of_eventuallyEq ?_
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
      exact L12f_Fstar_eq hα hα13 hz'.le
    · rw [abs_div, abs_neg,
        abs_of_nonneg (by have h := hp; positivity : (0 : ℝ) ≤ 2 * Work.FTS.Regularity.pExp α),
        abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ 2), div_le_iff₀ (by positivity)]
      nlinarith [hp.le, sq_nonneg z, hz', le_max_right N (2 * Work.FTS.Regularity.pExp α)]

/-- **The `D_θF_*`-slot of the static profile.** -/
theorem C1Jet_Dth_Fstar {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∃ N : ℝ, 0 ≤ N ∧ Work.FTS.RegPkgGal.C1Jet α S N
      (fun z θ τ => Work.Spaces.Dth
        (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ) := by
  have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
  have hgd : ∀ z : ℝ, 0 < z →
      ∃ d : ℝ, HasDerivAt (fun z => Work.FM.Fstar z) d z ∧ |d| ≤ 2 := by
    intro z hz
    refine ⟨deriv Work.FM.Fstar z, ?_, Work.FTS.Regularity.deriv_FM_Fstar_abs_le hz.le⟩
    rw [Work.FM.deriv_Fstar z (by linarith)]
    exact Work.FM.hasDerivAt_Fstar z (by linarith)
  have h := c1jet_prod (α := α) (S := S) hα hα1
    (Mf := 40 / 3) (Mg := 1 / 2) (Cf := 60) (Cg := 2) (Dg := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (f := DthCoeff α) (g := fun z => Work.FM.Fstar z)
    (fun θ hθ => DthCoeff_abs_le hα hα13 hθ)
    (fun z hz => Work.FTS.Regularity.fmFstar_abs_le_half hz)
    (fun θ hθ θ' hθ' => DthCoeff_holder hα hα13 hθ hθ')
    (fun z hz z' hz' => Work.FTS.Regularity.Moduli.fstarLip hz hz')
    hgd
  exact ⟨max (max (2 * (40 / 3 * (1 / 2))) (40 / 3 * 2 + 60 * (1 / 2))) (40 / 3 * 2),
    le_trans (le_trans (by norm_num) (le_max_left _ _)) (le_max_left _ _),
    c1jet_congr h (fun z θ τ hz hθ _ => (Dth_Fstar_eq hα hθ).symm)⟩

/-- **The `D_zF_*`-slot of the static profile.** -/
theorem C1Jet_Dz_Fstar {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∃ N : ℝ, 0 ≤ N ∧ Work.FTS.RegPkgGal.C1Jet α S N
      (fun z θ τ => Work.Spaces.Dz
        (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ) := by
  have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
  have hgd : ∀ z : ℝ, 0 < z → ∃ d : ℝ,
      HasDerivAt (fun w => w * deriv Work.FM.Fstar w) d z ∧ |d| ≤ 8 := by
    intro z hz
    exact ⟨2 * (1 - 4 * z + z ^ 2) / (1 + z) ^ 4, hasDerivAt_hhat hz, hhat_deriv_abs_le hz.le⟩
  have h := c1jet_prod (α := α) (S := S) hα hα1
    (Mf := 10) (Mg := 1 / 2) (Cf := 30) (Cg := 8) (Dg := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (f := Work.FTS.Regularity.pzCoeff α)
    (g := fun z => z * deriv Work.FM.Fstar z)
    (fun θ hθ => Work.FTS.Regularity.pzCoeff_abs_le hα hα13 hθ)
    (fun z hz => hhat_abs_le hz)
    (fun θ hθ θ' hθ' => Work.FTS.Regularity.pzCoeff_holder hα hα13 hθ hθ')
    (fun z hz z' hz' => hhat_lip hz hz')
    hgd
  exact ⟨max (max (2 * (10 * (1 / 2))) (10 * 8 + 30 * (1 / 2))) (10 * 8),
    le_trans (le_trans (by norm_num) (le_max_left _ _)) (le_max_left _ _),
    c1jet_congr h (fun z θ τ hz hθ _ => (Dz_Fstar_eq hα hz).symm)⟩

/-! ## §6 The target -/

theorem Fstar_C1Jet {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {S : ℝ} (hS : 0 < S) :
    ∃ N₉ N₁₀ N₁₁ : ℝ, 0 ≤ N₉ ∧ 0 ≤ N₁₀ ∧ 0 ≤ N₁₁ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₉
        (fun z θ τ => Work.Coercivity.L12f
          (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₁₀
        (fun z θ τ => Work.Spaces.Dth
          (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₁₁
        (fun z θ τ => Work.Spaces.Dz
          (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ) := by
  obtain ⟨N₉, hN₉0, hN₉⟩ := C1Jet_L12f_Fstar hα hα13 hS
  obtain ⟨N₁₀, hN₁₀0, hN₁₀⟩ := C1Jet_Dth_Fstar (α := α) (S := S) hα hα13
  obtain ⟨N₁₁, hN₁₁0, hN₁₁⟩ := C1Jet_Dz_Fstar (α := α) (S := S) hα hα13
  exact ⟨N₉, N₁₀, N₁₁, hN₉0, hN₁₀0, hN₁₁0, hN₉, hN₁₀, hN₁₁⟩

end Work.FTS_RegExport.RXR5
