import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS_StreamBdry.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB1.Engine` — the SB1′ structural argument

`sb1_gauge` (SB1′) says that on the open quadrant `Qd` every `C³` stream function whose `U`-slot is
bounded (`SlotBd`) differs from the particular solution `psiP` by a multiple of the gauge mode
`gaugeMode αG = z^{-3/αG}/cos θ`.

The argument, with `k = 3/αG`, `W := Ψ - psiP`:

1. the level-0 ODE `αG·D_zΨ + 3Ψ = -s2·U'(Ψ)` holds for `Ψ` **by definition** (`ode_of_Uprime`) and
   for `psiP` by `psiP_ode`; hence `αG·D_zW + 3W = 0`, so `z ↦ z^k W(z,θ)` is constant
   (`rpow_mul_const_of_hom`, `W_eq`);
2. differentiating that constancy in `θ` gives, for every `z ∈ (0,1)`,
   `z^k·V(W)(z,θ) = (1/2)^k·V(W)(1/2,θ)`; the left side is bounded by `z^k(M + C(θ))`
   (`SlotBd` for `V Ψ`, `VopPsiPBnd` for `V (psiP)`) while the right side is independent of `z`,
   so it vanishes and `V(W)(z,θ) = c'(θ) - tan θ·c(θ)` gives the `θ`-ODE `c' = tan θ·c`;
3. `θ ↦ c(θ)·cos θ` therefore has zero derivative on `(0,π/2)`, hence `c = κ/cos θ`, and
   `W = z^{-k}c(θ) = κ·gaugeMode`.

Everything is conditional on the three engine lemmas `PsiPOde`, `PsiPDiff`, `VopPsiPBnd`
(proved in `SB1/psiP_ode`, `SB1/psiP_diff`, `SB1/psiP_Vop_bnd`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB1

open Work.FTS.StreamBdryIface (Uprime SlotBd gaugeMode psiP)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## §0 Elementary facts -/

lemma isOpen_Qd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

lemma nhds_Qd {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Construction.Qd ∈ 𝓝 (z, θ) := isOpen_Qd.mem_nhds h

lemma Qd_nonempty : ((1 : ℝ), π / 4) ∈ Work.Construction.Qd :=
  mem_Qd.mpr ⟨by norm_num, by norm_num [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- The `z`-slices of a `C³` function are differentiable. -/
lemma diffAt_z_slice {Ψ : Fn} {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => Ψ z' θ) z := by
  have hc : ContDiffAt ℝ 3 (Function.uncurry Ψ) (z, θ) := h3.contDiffAt (nhds_Qd h)
  have hd : DifferentiableAt ℝ (Function.uncurry Ψ) (z, θ) :=
    hc.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (fun z' : ℝ => (z', θ)) z := by fun_prop
  simpa [Function.comp_def] using hd.comp z hg

/-- The `θ`-slices of a `C³` function are differentiable. -/
lemma diffAt_th_slice {Ψ : Fn} {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd) :
    DifferentiableAt ℝ (fun θ' => Ψ z θ') θ := by
  have hc : ContDiffAt ℝ 3 (Function.uncurry Ψ) (z, θ) := h3.contDiffAt (nhds_Qd h)
  have hd : DifferentiableAt ℝ (Function.uncurry Ψ) (z, θ) :=
    hc.differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  simpa [Function.comp_def] using hd.comp θ hg

/-- The `z`-slices of `psiP` are differentiable (engine hypothesis `PsiPDiff`). -/
lemma diffAt_z_psiP {αG M : ℝ} {Ψ : Fn} (hpdiff : PsiPDiff αG M Ψ) {z θ : ℝ}
    (h : (z, θ) ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (fun z' => psiP αG Ψ z' θ) z := (hpdiff z θ h).1

/-- The `θ`-slices of `psiP` are differentiable (engine hypothesis `PsiPDiff`). -/
lemma diffAt_th_psiP {αG M : ℝ} {Ψ : Fn} (hpdiff : PsiPDiff αG M Ψ) {z θ : ℝ}
    (h : (z, θ) ∈ Work.Construction.Qd) :
    DifferentiableAt ℝ (fun θ' => psiP αG Ψ z θ') θ := (hpdiff z θ h).2

/-- `pz` of the difference `Ψ - psiP`, pointwise. -/
lemma pz_sub_psiP {αG M : ℝ} {Ψ : Fn} {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hpdiff : PsiPDiff αG M Ψ) :
    Work.Spaces.pz (fun z' θ' => Ψ z' θ' - psiP αG Ψ z' θ') z θ
      = Work.Spaces.pz Ψ z θ - Work.Spaces.pz (psiP αG Ψ) z θ := by
  simp only [Work.Spaces.pz]
  rw [show (fun z' => Ψ z' θ - psiP αG Ψ z' θ)
      = ((fun z' => Ψ z' θ) - (fun z' => psiP αG Ψ z' θ)) from rfl,
    deriv_sub (diffAt_z_slice h h3) (diffAt_z_psiP hpdiff h)]

/-- `pth` of the difference `Ψ - psiP`, pointwise. -/
lemma pth_sub_psiP {αG M : ℝ} {Ψ : Fn} {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hpdiff : PsiPDiff αG M Ψ) :
    Work.Spaces.pth (fun z' θ' => Ψ z' θ' - psiP αG Ψ z' θ') z θ
      = Work.Spaces.pth Ψ z θ - Work.Spaces.pth (psiP αG Ψ) z θ := by
  simp only [Work.Spaces.pth]
  rw [show (fun θ' => Ψ z θ' - psiP αG Ψ z θ')
      = ((fun θ' => Ψ z θ') - (fun θ' => psiP αG Ψ z θ')) from rfl,
    deriv_sub (diffAt_th_slice h h3) (diffAt_th_psiP hpdiff h)]

/-- `V` of the difference is the difference of the `V`'s (definitional apart from `pth_sub`). -/
lemma Vop_sub_psiP {αG M : ℝ} {Ψ : Fn} {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hpdiff : PsiPDiff αG M Ψ) :
    Work.Construction.Vop (fun z' θ' => Ψ z' θ' - psiP αG Ψ z' θ') z θ
      = Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ := by
  rw [Work.Construction.Vop, Work.Construction.Vop, Work.Construction.Vop,
    pth_sub_psiP h h3 hpdiff]
  ring

/-! ## §1 The homogeneous ODE and the constancy in `z` -/

lemma rpow_mul_const_le {αG : ℝ} (hαG : 0 < αG) {f : ℝ → ℝ}
    (hf : ∀ z ∈ Ioi (0 : ℝ), DifferentiableAt ℝ f z)
    (hode : ∀ z ∈ Ioi (0 : ℝ), αG * z * deriv f z + 3 * f z = 0)
    {z₁ z₂ : ℝ} (h1 : 0 < z₁) (h2 : 0 < z₂) (hle : z₁ ≤ z₂) :
    z₁ ^ (3 / αG) * f z₁ = z₂ ^ (3 / αG) * f z₂ := by
  have hαG' : αG ≠ 0 := ne_of_gt hαG
  have hderiv : ∀ z ∈ uIcc z₁ z₂, HasDerivAt (fun z => z ^ (3 / αG) * f z) 0 z := by
    intro z hz
    rw [Set.uIcc_of_le hle] at hz
    have hzpos : 0 < z := lt_of_lt_of_le h1 hz.1
    have hzI : z ∈ Ioi (0 : ℝ) := hzpos
    have h1d : HasDerivAt (fun z : ℝ => z ^ (3 / αG))
        ((3 / αG) * z ^ (3 / αG - 1)) z :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hzpos))
    have h2d : HasDerivAt f (deriv f z) z := (hf z hzI).hasDerivAt
    refine (h1d.mul h2d).congr_deriv ?_
    have hp : z ^ (3 / αG) = z ^ (3 / αG - 1) * z := by
      rw [← Real.rpow_add_one (ne_of_gt hzpos)]
      norm_num
    have hbr : (3 / αG) * f z + z * deriv f z = 0 := by
      have h0 := hode z hzI
      have hz' : z * deriv f z = -(3 * f z) / αG := by
        rw [eq_div_iff hαG']
        linarith
      rw [hz']
      field_simp
      ring
    rw [hp]
    have hcl : (3 / αG) * z ^ (3 / αG - 1) * f z + z ^ (3 / αG - 1) * z * deriv f z
        = z ^ (3 / αG - 1) * ((3 / αG) * f z + z * deriv f z) := by ring
    rw [hcl, hbr, mul_zero]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume z₁ z₂)
  simp only [intervalIntegral.integral_zero] at hftc
  linarith

/-- The homogeneous ODE `αG·D_z f + 3f = 0` makes `z ↦ z^{3/αG} f z` constant. -/
lemma rpow_mul_const_of_hom {αG : ℝ} (hαG : 0 < αG) {f : ℝ → ℝ}
    (hf : ∀ z ∈ Ioi (0 : ℝ), DifferentiableAt ℝ f z)
    (hode : ∀ z ∈ Ioi (0 : ℝ), αG * z * deriv f z + 3 * f z = 0)
    {z₁ z₂ : ℝ} (h1 : 0 < z₁) (h2 : 0 < z₂) :
    z₁ ^ (3 / αG) * f z₁ = z₂ ^ (3 / αG) * f z₂ := by
  rcases le_total z₁ z₂ with hle | hle
  · exact rpow_mul_const_le hαG hf hode h1 h2 hle
  · exact (rpow_mul_const_le hαG hf hode h2 h1 hle).symm

/-- The homogeneous ODE for `W = Ψ - psiP` (difference of the two level-0 ODEs). -/
lemma W_hom {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {z θ : ℝ}
    (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ) :
    αG * z * deriv (fun z' => Ψ z' θ - psiP αG Ψ z' θ) z
      + 3 * (Ψ z θ - psiP αG Ψ z θ) = 0 := by
  have hpz := pz_sub_psiP (αG := αG) h h3 hpdiff
  have hA := ode_of_Uprime (αG := αG) Ψ h
  have hB := hode z θ h
  simp only [Work.Spaces.pz] at hpz hA hB
  rw [hpz]
  linarith

/-- The constant in `z`: `c(θ) = (1/2)^{3/αG}·W(1/2,θ)`. -/
def cfun (αG : ℝ) (Ψ : Fn) (θ : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ (3 / αG) * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ)

lemma half_mem_Qd {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    ((1 / 2 : ℝ), θ) ∈ Work.Construction.Qd :=
  mem_Qd.mpr ⟨by norm_num, hθ.1, hθ.2⟩

/-- **Constancy in `z`**: `Ψ - psiP = z^{-3/αG}·c(θ)`. -/
lemma W_eq {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {z θ : ℝ}
    (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ) :
    Ψ z θ - psiP αG Ψ z θ = z ^ (-(3 / αG)) * cfun αG Ψ θ := by
  have hθ : θ ∈ Ioo (0 : ℝ) (π / 2) := Qd_theta_mem h
  have hz : 0 < z := Qd_pos h
  have hf : ∀ z' ∈ Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => Ψ z' θ - psiP αG Ψ z' θ) z' := by
    intro z' hz'
    exact (diffAt_z_slice (mem_Qd.mpr ⟨hz', hθ.1, hθ.2⟩) h3).sub
      (diffAt_z_psiP hpdiff (mem_Qd.mpr ⟨hz', hθ.1, hθ.2⟩))
  have hode' : ∀ z' ∈ Ioi (0 : ℝ),
      αG * z' * deriv (fun z'' => Ψ z'' θ - psiP αG Ψ z'' θ) z'
        + 3 * (Ψ z' θ - psiP αG Ψ z' θ) = 0 :=
    fun z' hz' => W_hom hαG (mem_Qd.mpr ⟨hz', hθ.1, hθ.2⟩) h3 hode hpdiff
  have hc := rpow_mul_const_of_hom hαG hf hode' hz (by norm_num : (0 : ℝ) < 1 / 2)
  have hzk : z ^ (3 / αG) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hz _)
  have hW : Ψ z θ - psiP αG Ψ z θ = cfun αG Ψ θ / z ^ (3 / αG) := by
    rw [eq_div_iff hzk, mul_comm (Ψ z θ - psiP αG Ψ z θ)]
    simpa only [cfun] using hc
  rw [hW, Real.rpow_neg (le_of_lt hz), div_eq_mul_inv, mul_comm]

/-- The constancy, in the `z^k·W` form. -/
lemma rpow_mul_W_eq {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {z θ : ℝ}
    (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ) :
    z ^ (3 / αG) * (Ψ z θ - psiP αG Ψ z θ) = cfun αG Ψ θ := by
  have hθ : θ ∈ Ioo (0 : ℝ) (π / 2) := Qd_theta_mem h
  have hz : 0 < z := Qd_pos h
  have h1 := W_eq (αG := αG) (M := M) hαG h h3 hode hpdiff
  rw [h1]
  have hz' : z ^ (-(3 / αG)) * z ^ (3 / αG) = 1 := by
    rw [← Real.rpow_add hz]
    norm_num
  rw [← mul_assoc, mul_comm (z ^ (3 / αG)) (z ^ (-(3 / αG))), hz', one_mul]

/-! ## §2 The `θ`-ODE for the constant -/

/-- `cfun` is differentiable in `θ`. -/
lemma differentiableAt_cfun {αG M : ℝ} {Ψ : Fn} {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hpdiff : PsiPDiff αG M Ψ) : DifferentiableAt ℝ (cfun αG Ψ) θ := by
  have hmem := half_mem_Qd hθ
  have hd := (diffAt_th_slice hmem h3).sub (diffAt_th_psiP hpdiff hmem)
  have hc : DifferentiableAt ℝ
      (fun θ' => (1 / 2 : ℝ) ^ (3 / αG) * (Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ')) θ :=
    hd.const_mul _
  exact hc

/-- `|L| ≤ z^k·D` for all `z ∈ (0,1)` with `D ≥ 0`, `k > 0` forces `L = 0`. -/
lemma eq_zero_of_abs_le_rpow_mul {k L D : ℝ} (hk : 0 < k) (hD : 0 ≤ D)
    (h : ∀ z ∈ Ioo (0 : ℝ) 1, |L| ≤ z ^ k * D) : L = 0 := by
  have hmemI : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [show 𝓝[>] (0 : ℝ) = 𝓝 (0 : ℝ) ⊓ 𝓟 (Ioi 0) from rfl, mem_inf_principal]
    refine Filter.mem_of_superset (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)) ?_
    intro x hx
    simp only [mem_setOf_eq, mem_Iio] at hx ⊢
    intro h0
    exact ⟨h0, by linarith⟩
  have htend : Tendsto (fun z : ℝ => z ^ k * D) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun z : ℝ => z ^ k) 0 :=
      Real.continuousAt_rpow_const 0 k (Or.inr (le_of_lt hk))
    have h0 : (0 : ℝ) ^ k = 0 := Real.zero_rpow (ne_of_gt hk)
    have h1 : Tendsto (fun z : ℝ => z ^ k) (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) ^ k)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    rw [h0] at h1
    simpa using h1.mul_const D
  have hev : ∀ᶠ z in 𝓝[>] (0 : ℝ), |L| ≤ z ^ k * D :=
    Filter.mem_of_superset hmemI fun z hz => h z hz
  have hle : |L| ≤ 0 := ge_of_tendsto htend hev
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

/-- The heart of SB1′: `z^k·V(W)` is independent of `z`.  Proved by differentiating the constancy
of `W` in `θ`: both `W z` and `W (1/2)` are `z^{-k}c(θ)` resp. `(1/2)^{-k}c(θ)`. -/
lemma VopW_rpow_const {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {z θ : ℝ}
    (hz1 : z < 1) (h : (z, θ) ∈ Work.Construction.Qd)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ) :
    z ^ (3 / αG) * (Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ)
      = (1 / 2 : ℝ) ^ (3 / αG)
        * (Work.Construction.Vop Ψ (1 / 2) θ
            - Work.Construction.Vop (psiP αG Ψ) (1 / 2) θ) := by
  have hθ : θ ∈ Ioo (0 : ℝ) (π / 2) := Qd_theta_mem h
  have hz : 0 < z := Qd_pos h
  have hzhalf : ((1 / 2 : ℝ), θ) ∈ Work.Construction.Qd := half_mem_Qd hθ
  have hI : Ioo (0 : ℝ) (π / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hdc := differentiableAt_cfun (αG := αG) (M := M) hθ h3 hpdiff
  have hWz_ev : (fun θ' => Ψ z θ' - psiP αG Ψ z θ') =ᶠ[𝓝 θ]
      (fun θ' => z ^ (-(3 / αG)) * cfun αG Ψ θ') := by
    filter_upwards [hI] with θ' hθ'
    exact W_eq (αG := αG) (M := M) hαG (mem_Qd.mpr ⟨hz, hθ'.1, hθ'.2⟩) h3 hode hpdiff
  have hWh_ev : (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') =ᶠ[𝓝 θ]
      (fun θ' => (1 / 2 : ℝ) ^ (-(3 / αG)) * cfun αG Ψ θ') := by
    filter_upwards [hI] with θ' hθ'
    exact W_eq (αG := αG) (M := M) hαG (half_mem_Qd hθ') h3 hode hpdiff
  have hdz : deriv (fun θ' => Ψ z θ' - psiP αG Ψ z θ') θ
      = z ^ (-(3 / αG)) * deriv (cfun αG Ψ) θ := by
    rw [hWz_ev.deriv_eq]
    exact deriv_const_mul _ hdc
  have hdh : deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ
      = (1 / 2 : ℝ) ^ (-(3 / αG)) * deriv (cfun αG Ψ) θ := by
    rw [hWh_ev.deriv_eq]
    exact deriv_const_mul _ hdc
  have hzz : z ^ (-(3 / αG)) * z ^ (3 / αG) = 1 := by
    rw [← Real.rpow_add hz]
    norm_num
  have hhh : (1 / 2 : ℝ) ^ (-(3 / αG)) * (1 / 2 : ℝ) ^ (3 / αG) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
  have hkey1 : z ^ (3 / αG) * deriv (fun θ' => Ψ z θ' - psiP αG Ψ z θ') θ
      = (1 / 2 : ℝ) ^ (3 / αG)
        * deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ := by
    rw [hdz, hdh, ← mul_assoc, mul_comm (z ^ (3 / αG)) (z ^ (-(3 / αG))), hzz, one_mul,
      ← mul_assoc, mul_comm ((1 / 2 : ℝ) ^ (3 / αG)) ((1 / 2 : ℝ) ^ (-(3 / αG))), hhh, one_mul]
  have hkey2 : z ^ (3 / αG) * (Ψ z θ - psiP αG Ψ z θ)
      = (1 / 2 : ℝ) ^ (3 / αG) * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ) := by
    rw [rpow_mul_W_eq (αG := αG) (M := M) hαG h h3 hode hpdiff,
      rpow_mul_W_eq (αG := αG) (M := M) hαG hzhalf h3 hode hpdiff]
  have hL : Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ
      = deriv (fun θ' => Ψ z θ' - psiP αG Ψ z θ') θ
        - Real.tan θ * (Ψ z θ - psiP αG Ψ z θ) := by
    have hd := pth_sub_psiP (αG := αG) h h3 hpdiff
    simp only [Work.Spaces.pth] at hd
    rw [Work.Construction.Vop, Work.Construction.Vop, Work.Spaces.pth, Work.Spaces.pth]
    rw [hd]
    ring
  have hR : Work.Construction.Vop Ψ (1 / 2) θ - Work.Construction.Vop (psiP αG Ψ) (1 / 2) θ
      = deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ
        - Real.tan θ * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ) := by
    have hd := pth_sub_psiP (αG := αG) hzhalf h3 hpdiff
    simp only [Work.Spaces.pth] at hd
    rw [Work.Construction.Vop, Work.Construction.Vop, Work.Spaces.pth, Work.Spaces.pth]
    rw [hd]
    ring
  rw [hL, hR]
  rw [show z ^ (3 / αG) * (deriv (fun θ' => Ψ z θ' - psiP αG Ψ z θ') θ
        - Real.tan θ * (Ψ z θ - psiP αG Ψ z θ))
      = z ^ (3 / αG) * deriv (fun θ' => Ψ z θ' - psiP αG Ψ z θ') θ
        - Real.tan θ * (z ^ (3 / αG) * (Ψ z θ - psiP αG Ψ z θ)) from by ring]
  rw [show (1 / 2 : ℝ) ^ (3 / αG) * (deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ
        - Real.tan θ * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ))
      = (1 / 2 : ℝ) ^ (3 / αG) * deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ
        - Real.tan θ * ((1 / 2 : ℝ) ^ (3 / αG)
            * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ)) from by ring]
  rw [hkey1, hkey2]

/-- `V(W)` vanishes on the half-line `θ = 1/2`: the constant of integration is not a general
function of `θ` but `κ/cos θ`. -/
lemma VopW_half_eq_zero {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ)
    (hbnd : VopPsiPBnd αG M Ψ) :
    (1 / 2 : ℝ) ^ (3 / αG)
      * (Work.Construction.Vop Ψ (1 / 2) θ - Work.Construction.Vop (psiP αG Ψ) (1 / 2) θ)
      = 0 := by
  obtain ⟨C, hC⟩ := hbnd θ hθ
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC (1 / 2) ⟨by norm_num, by norm_num⟩)
  have hM0 : 0 ≤ M :=
    le_trans (abs_nonneg _)
      (SlotBd.V_le hslot (z := 1) (θ := π / 4) Qd_nonempty (j := 0) (by norm_num))
  have hbdd : ∀ z ∈ Ioo (0 : ℝ) 1,
      |(1 / 2 : ℝ) ^ (3 / αG)
        * (Work.Construction.Vop Ψ (1 / 2) θ
            - Work.Construction.Vop (psiP αG Ψ) (1 / 2) θ)| ≤ z ^ (3 / αG) * (M + C) := by
    intro z hz
    have hmem : (z, θ) ∈ Work.Construction.Qd := mem_Qd.mpr ⟨hz.1, hθ.1, hθ.2⟩
    have h1 := VopW_rpow_const (αG := αG) (M := M) hαG hz.2 hmem h3 hode hpdiff
    have h2 : |Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ|
        ≤ M + C := by
      refine (abs_sub _ _).trans ?_
      exact add_le_add (SlotBd.V_le hslot hmem (j := 0) (by norm_num)) (hC z hz)
    calc |(1 / 2 : ℝ) ^ (3 / αG)
          * (Work.Construction.Vop Ψ (1 / 2) θ
              - Work.Construction.Vop (psiP αG Ψ) (1 / 2) θ)|
        = |z ^ (3 / αG)
            * (Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ)| := by
          rw [← h1]
      _ = z ^ (3 / αG)
            * |Work.Construction.Vop Ψ z θ - Work.Construction.Vop (psiP αG Ψ) z θ| := by
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz.1 _)]
      _ ≤ z ^ (3 / αG) * (M + C) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt (Real.rpow_pos_of_pos hz.1 _))
  exact eq_zero_of_abs_le_rpow_mul (by positivity) (add_nonneg hM0 hC0) hbdd

/-- The `θ`-ODE for the constant of integration: `c'(θ) = tan θ·c(θ)`. -/
lemma deriv_cfun {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ)
    (hbnd : VopPsiPBnd αG M Ψ) :
    deriv (cfun αG Ψ) θ = Real.tan θ * cfun αG Ψ θ := by
  have hmem : ((1 / 2 : ℝ), θ) ∈ Work.Construction.Qd := half_mem_Qd hθ
  have hV := VopW_half_eq_zero (αG := αG) (M := M) hαG hθ h3 hslot hode hpdiff hbnd
  have h1 : deriv (cfun αG Ψ) θ
      = (1 / 2 : ℝ) ^ (3 / αG)
        * deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ := by
    rw [show cfun αG Ψ
        = (fun θ' => (1 / 2 : ℝ) ^ (3 / αG)
            * (Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ')) from rfl]
    exact deriv_const_mul _
      ((diffAt_th_slice hmem h3).sub (diffAt_th_psiP hpdiff hmem))
  have h2 : deriv (fun θ' => Ψ (1 / 2) θ' - psiP αG Ψ (1 / 2) θ') θ
      = (Work.Construction.Vop Ψ (1 / 2) θ
          - Work.Construction.Vop (psiP αG Ψ) (1 / 2) θ)
        + Real.tan θ * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ) := by
    have hd := pth_sub_psiP (αG := αG) hmem h3 hpdiff
    simp only [Work.Spaces.pth] at hd
    rw [hd, Work.Construction.Vop, Work.Construction.Vop, Work.Spaces.pth, Work.Spaces.pth]
    ring
  rw [h1, h2, mul_add, hV, zero_add]
  rw [show (1 / 2 : ℝ) ^ (3 / αG) * (Real.tan θ * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ))
      = Real.tan θ
        * ((1 / 2 : ℝ) ^ (3 / αG) * (Ψ (1 / 2) θ - psiP αG Ψ (1 / 2) θ)) from by ring]
  rfl

/-- **The constant is `κ/cos θ`**: `c(θ)·cos θ` is constant on `(0,π/2)`. -/
lemma cos_mul_cfun_const {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn} {θ : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ)
    (hbnd : VopPsiPBnd αG M Ψ) :
    cfun αG Ψ θ * Real.cos θ = cfun αG Ψ (π / 4) * Real.cos (π / 4) := by
  have hπ4 : π / 4 ∈ Ioo (0 : ℝ) (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  set d : ℝ → ℝ := fun t => cfun αG Ψ t * Real.cos t with hd
  have hderiv : ∀ t ∈ uIcc θ (π / 4), HasDerivAt d 0 t := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have ht' : t ∈ Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_of_lt_of_le hθ.1 ha, lt_of_le_of_lt hb hπ4.2⟩
      have hdiff := differentiableAt_cfun (αG := αG) (M := M) ht' h3 hpdiff
      have hcos : HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos t
      have hprod : HasDerivAt (fun t => cfun αG Ψ t * Real.cos t) 0 t := by
        refine (hdiff.hasDerivAt.mul hcos).congr_deriv ?_
        rw [deriv_cfun (αG := αG) (M := M) hαG ht' h3 hslot hode hpdiff hbnd,
          Real.tan_eq_sin_div_cos]
        have hct : Real.cos t ≠ 0 := ne_of_gt (cos_pos_of_Ioo ht')
        field_simp
        ring
      exact hprod
    · have ht' : t ∈ Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_of_lt_of_le hπ4.1 ha, lt_of_le_of_lt hb hθ.2⟩
      have hdiff := differentiableAt_cfun (αG := αG) (M := M) ht' h3 hpdiff
      have hcos : HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos t
      have hprod : HasDerivAt (fun t => cfun αG Ψ t * Real.cos t) 0 t := by
        refine (hdiff.hasDerivAt.mul hcos).congr_deriv ?_
        rw [deriv_cfun (αG := αG) (M := M) hαG ht' h3 hslot hode hpdiff hbnd,
          Real.tan_eq_sin_div_cos]
        have hct : Real.cos t ≠ 0 := ne_of_gt (cos_pos_of_Ioo ht')
        field_simp
        ring
      exact hprod
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume θ (π / 4))
  simp only [intervalIntegral.integral_zero] at hftc
  linarith

/-! ## §3 SB1′ -/

/-- **SB1′ from the three engine lemmas.** -/
theorem sb1_gauge_of_parts {αG M : ℝ} (hαG : 0 < αG) {Ψ : Fn}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M)
    (hode : PsiPOde αG M Ψ) (hpdiff : PsiPDiff αG M Ψ) (hbnd : VopPsiPBnd αG M Ψ) :
    ∃ κ : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Ψ z θ = psiP αG Ψ z θ + κ * gaugeMode αG z θ := by
  refine ⟨cfun αG Ψ (π / 4) * Real.cos (π / 4), ?_⟩
  intro z θ h
  have hθ : θ ∈ Ioo (0 : ℝ) (π / 2) := Qd_theta_mem h
  have hW := W_eq (αG := αG) (M := M) hαG h h3 hode hpdiff
  have hc := cos_mul_cfun_const (αG := αG) (M := M) hαG hθ h3 hslot hode hpdiff hbnd
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (cos_pos_of_Qd h)
  have hcf : cfun αG Ψ θ = (cfun αG Ψ (π / 4) * Real.cos (π / 4)) / Real.cos θ := by
    rw [eq_div_iff hcos]
    linarith [hc]
  have hΨ : Ψ z θ = psiP αG Ψ z θ + z ^ (-(3 / αG)) * cfun αG Ψ θ := by linarith [hW]
  rw [hΨ, hcf, gaugeMode]
  ring

end Work.FTS_StreamBdry.SB1
