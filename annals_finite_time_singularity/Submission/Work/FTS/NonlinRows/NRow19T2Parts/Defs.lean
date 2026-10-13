/-
# Row 19 in the `T2` vocabulary — the pointwise estimates

The piece of row 19 is `N₃^{**} = -2α·𝒱(Φ̃_*)·∂_zF_*` (`Work.FTS.Nonlin.N3ss`), and the row
asks for the `ℋ⁴`-honesty of `N₃^{**}` together with `|N₃^{**}|_{ℋ⁴} ≤ K α³`.

The whole estimate goes through `Work.FTS.NonlinRows.wtoHQ_of_pointwise_open`, applied to

  `Z := 𝒱(Φ̃_*)·∂_zF_*`     (`Z19` below),

which needs only the two pointwise families

* (η) `|(1+z)·w(z)·z^m·∂_z^m Z| ≤ 200000·W`, `m ≤ 4`;
* (γ) `|(1+z)·w(z)·z^l·∂_z^l D_θ^i Z| ≤ 200000·W·Φ(θ)`, `1 ≤ i`, `l+i ≤ 4`,

with `W = C·α·Λ`, `Λ = |A|_{𝒲^{4,∞}}`, `A := ((z+1)/z)·𝒱(Φ̃_*)` (the field
`VocabO2.StarPkgo2.VzW`) and `Φ(θ) = (α + sin 2θ)·sin(2θ)^{α/5}`.

The key point is the factorisation of `Z` on the open quadrant,

  `Z = (α/c(α))·Γ(θ)·A(z,θ)·H₂(z)`,   `H₂(z) = 2z²(1-z)/(1+z)⁴`,

whose factors carry the three estimates:

* `|(1+z)^c ∂_z^c A| ≤ Λ` (`WlInf_z_bound`) and `|(1+z)^c ∂_z^c D_θ^b A| ≤ Λ·Φ(θ)` for `b ≥ 1`
  (`Work.Spaces.factor_bound`);
* `|D_θ^a Γ| ≤ MΓ(a)·Γ` (`dthU_Gam_le`, `a ≥ 1`), together with `Γ ≤ 1` and `αΓ ≤ Φ`
  (`Gam_bounds`, `Gam_mul_weight_le`);
* `(1+z)w(z)z^m/(1+z)^{m-j}·|∂_z^jH₂| ≤ 10^7` (`Row19Prep.H2b_weight_le`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.Defs
import Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19aux
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.Defs
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.H2bBound
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.LocData.HkSq_const_mul
import Submission.Work.Coercivity.HkMem_congr_Ioi
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.Gam_mul_weight_le
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gam_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-! ## The vocabulary -/

/-- `A = ((z+1)/z)·𝒱(Φ̃_*)`: the weighted star coefficient whose `𝒲^{4,∞}`-membership (with
bound `≤ Cs·α`) is the field `VocabO2.StarPkgo2.VzW`. -/
def A19 (α : ℝ) (Φs : Fn) : Fn :=
  fun z θ => (z + 1) / z * Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ

/-- The `z`-only factor `H₂(z) = 2z²(1-z)/(1+z)⁴` of the row-19 piece, lifted to `Fn`. -/
def H2f : Fn := fun z _ => Work.FTS.Nonlinear.Open.Row19Prep.H2b z

/-- `c₁₉(θ) = (α/c(α))·Γ(θ)`: the angular factor of `Z19`. -/
def c19 (α : ℝ) : ℝ → ℝ := fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ

/-- `K₁₉ = A·H₂`: the `(z,θ)`-factor of `Z19`. -/
def K19 (α : ℝ) (Φs : Fn) : Fn := fun z θ => A19 α Φs z θ * H2f z θ

/-- The row-19 piece `Z = 𝒱(Φ̃_*)·∂_zF_*` in its factorised form. -/
def Z19 (α : ℝ) (Φs : Fn) : Fn := fun z θ => c19 α θ * K19 α Φs z θ

/-- `Φ(θ) = (α + sin 2θ)·sin(2θ)^{α/5}`: the angular weight of the `𝒲^{l,∞}`-norm. -/
def PhiAng (α θ : ℝ) : ℝ := (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)

/-- The angular factor attached to the `A`-derivatives of the (γ)-family: `1` for `b = 0` and
`Φ(θ)` for `b ≥ 1`. -/
def Psi19 (α : ℝ) (b : ℕ) (θ : ℝ) : ℝ := if b = 0 then 1 else PhiAng α θ

/-- `TB = Σ_{j<5} tBound j 0`, an upper bound for `tBound (a-1) 0`, `a ≤ 4`. -/
def TB19 : ℝ := ∑ j ∈ Finset.range 5, Work.Spaces.tBound j 0

/-- The angular-jet factor of `D_θ^a Γ`: `1` for `a = 0` and `α·TB` for `a ≥ 1`. -/
def MGa (α : ℝ) (a : ℕ) : ℝ := if a = 0 then 1 else α * TB19

/-! ## Elementary facts -/

lemma TB19_nonneg : 0 ≤ TB19 :=
  Finset.sum_nonneg fun j _ => Work.Spaces.tBound_nonneg j 0

lemma tBound_le_TB19 {a : ℕ} (ha : 1 ≤ a) (ha4 : a ≤ 4) : Work.Spaces.tBound (a - 1) 0 ≤ TB19 := by
  refine Finset.single_le_sum (f := fun j : ℕ => Work.Spaces.tBound j 0)
    (fun j _ => Work.Spaces.tBound_nonneg j 0) ?_
  rw [Finset.mem_range]
  omega

lemma MGa_nonneg {α : ℝ} (hα : 0 ≤ α) (a : ℕ) : 0 ≤ MGa α a := by
  rw [MGa]
  split_ifs with h
  · norm_num
  · exact mul_nonneg hα TB19_nonneg

lemma MGa_le {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (a : ℕ) : MGa α a ≤ 1 + TB19 := by
  rw [MGa]
  split_ifs with h
  · linarith [TB19_nonneg]
  · nlinarith [TB19_nonneg, hα, hα1]

lemma PhiAng_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ PhiAng α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    rw [Work.Spaces.Iθ] at hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [PhiAng]
  exact mul_nonneg (by linarith) (Real.rpow_nonneg hs _)

lemma Psi19_nonneg {α : ℝ} (hα : 0 < α) {b : ℕ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Psi19 α b θ := by
  rw [Psi19]
  split_ifs with h
  · norm_num
  · exact PhiAng_nonneg hα hθ

lemma Psi19_le_two {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {b : ℕ} {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : Psi19 α b θ ≤ 2 := by
  rw [Psi19]
  split_ifs with h
  · norm_num
  · rw [PhiAng]
    have hs : 0 ≤ Real.sin (2 * θ) := by
      rw [Work.Spaces.Iθ] at hθ
      exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have h2 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hs h1 (by linarith)
    have h3 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hs _
    nlinarith

/-- `α·Γ(θ) ≤ Φ(θ)` on `Iθ`. -/
lemma alpha_Gam_le_PhiAng {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    α * Work.Spaces.Gam α θ ≤ PhiAng α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := by
    rw [Work.Spaces.Iθ] at hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rw [PhiAng]
  rcases eq_or_lt_of_le hs with h | h
  · have hzero : Real.sin (2 * θ) = 0 := h.symm
    have hsc : Real.sin θ * Real.cos θ = 0 := by
      have h2 := Real.sin_two_mul θ
      rw [h2] at hzero
      linarith
    have hGam : Work.Spaces.Gam α θ = 0 := by
      rw [Work.Spaces.Gam]
      have hz : Real.sin θ * Real.cos θ ^ 2 = 0 := by
        rw [show Real.sin θ * Real.cos θ ^ 2 = (Real.sin θ * Real.cos θ) * Real.cos θ by ring,
          hsc, zero_mul]
      rw [hz]
      exact Real.zero_rpow (by linarith : α / 3 ≠ 0)
    rw [hGam, mul_zero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hs _)
  · have hw := Work.Spaces.Gam_mul_weight_le α θ hα hθ
    have hden : 0 < α + Real.sin (2 * θ) := by linarith
    have hkey : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
        ≤ α + Real.sin (2 * θ) := by
      rw [div_le_iff₀ hden] at hw
      simpa using hw
    have hs' : 0 < (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_pos_of_pos h _
    calc α * Work.Spaces.Gam α θ
        = α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            * ((Real.sin (2 * θ)) ^ (-(α / 5)))⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos h _)), mul_one]
      _ = α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
            * (Real.sin (2 * θ)) ^ (α / 5) := by
          rw [Real.rpow_neg h.le, inv_inv]
      _ ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
          mul_le_mul_of_nonneg_right hkey hs'.le

lemma Gam_nonneg' {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1

lemma Gam_le_one' {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2

/-! ## The equivalence of the two forms of `Z` on the open quadrant -/

theorem Z19_eq_Vs_Gs {α : ℝ} {Φs : Fn} (hα : 0 < α) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
      Z19 α Φs z θ
        = Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
            * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ := by
  intro z hz θ
  have hz1 : (-1 : ℝ) < z := by linarith
  have hH : Work.FTS.Nonlinear.Open.Row19Prep.H2b z
      = z / (z + 1) * Work.FTS.Nonlinear.FstarPkg.Hz z := by
    rw [Work.FTS.Nonlinear.Open.Row19Prep.H2b, Work.FTS.Nonlinear.FstarPkg.Hz]
    field_simp
    ring
  rw [Z19, K19, c19, A19, H2f, hH, Work.FTS.Nonlinear.Pieces.RNP.Gs,
    Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα hz1]
  field_simp

/-! ## The `z`-only Leibniz rule for `∂_z^k` -/

theorem pzIter_zOnly (r : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.pzIter k (fun z θ => r z) = fun z θ => deriv^[k] r z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      exact (congrFun (Function.iterate_succ_apply' deriv k r) z).symm

/-! ## Smoothness -/

theorem contDiffOn_H2b : ContDiffOn ℝ Work.Stability.smoothOrder
    Work.FTS.Nonlinear.Open.Row19Prep.H2b (Set.Ioi 0) := by
  have h : Work.FTS.Nonlinear.Open.Row19Prep.H2b
      = fun z : ℝ => 2 * z ^ 2 * (1 - z) / (1 + z) ^ 4 := rfl
  rw [h]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact ((contDiffOn_const (c := (2 : ℝ)).mul (contDiffOn_id.pow 2)).mul
      (contDiffOn_const.sub contDiffOn_id))
  · exact (contDiffOn_const.add contDiffOn_id).pow 4
  · intro z hz
    have hz1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity

theorem smoothOpen_H2f : Work.FTS.EllipticEst.SmoothOpen H2f :=
  Work.FTS.NonlinRows.smoothOpen_z_only contDiffOn_H2b

theorem contDiffOn_zdiv : ContDiffOn ℝ Work.Stability.smoothOrder
    (fun z : ℝ => (z + 1) / z) (Set.Ioi 0) := by
  refine ContDiffOn.div (contDiffOn_id.add contDiffOn_const) contDiffOn_id ?_
  intro z hz
  exact ne_of_gt (Set.mem_Ioi.mp hz)

theorem smoothOpen_A19 {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) : Work.FTS.EllipticEst.SmoothOpen (A19 α Φs) := by
  have hV : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_Vop (Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hs)
  have hz : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => (z + 1) / z) :=
    Work.FTS.NonlinRows.smoothOpen_z_only contDiffOn_zdiv
  exact hz.mul hV

theorem smoothOpen_c19 (α : ℝ) : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => c19 α θ) :=
  Work.FTS.NonlinRows.smoothOpen_theta_only
    (by
      have h := (Work.FTS.NonlinRows.contDiffOn_Gam α).const_smul (α / Work.Spaces.c α)
      have hfun : c19 α = fun y : ℝ => α / Work.Spaces.c α * Work.Spaces.Gam α y := by
        funext y; rw [c19]
      rw [hfun]
      exact h)

theorem smoothOpen_K19 {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) : Work.FTS.EllipticEst.SmoothOpen (K19 α Φs) :=
  (smoothOpen_A19 hα hα1 hs).mul smoothOpen_H2f

theorem smoothOpen_Z19 {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) : Work.FTS.EllipticEst.SmoothOpen (Z19 α Φs) :=
  (smoothOpen_c19 α).mul (smoothOpen_K19 hα hα1 hs)

/-! ## The angular jet bounds -/

/-- `|D_θ^a Γ| ≤ MΓ(a)·Γ` on `Iθ`, for `a ≤ 4`. -/
theorem dthU_Gam_le_MGa {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {a : ℕ} (ha : a ≤ 4) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[a] (fun t : ℝ => Work.Spaces.Gam α t) θ|
        ≤ MGa α a * Work.Spaces.Gam α θ := by
  intro θ hθ
  have hG := Gam_nonneg' hα hθ
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h
    rw [Function.iterate_zero_apply, MGa, if_pos rfl, one_mul, abs_of_nonneg hG]
  · rw [MGa, if_neg (Nat.pos_iff_ne_zero.mp h)]
    have hd := Work.Spaces.dthU_Gam_le a h α hα hα1 θ hθ
    have hb := tBound_le_TB19 h ha
    calc |Work.Spaces.dthU^[a] (fun t : ℝ => Work.Spaces.Gam α t) θ|
        ≤ α * Work.Spaces.tBound (a - 1) 0 * Work.Spaces.Gam α θ := hd
      _ ≤ α * TB19 * Work.Spaces.Gam α θ := by
          refine mul_le_mul_of_nonneg_right ?_ hG
          exact mul_le_mul_of_nonneg_left hb hα.le

/-- `|D_θ^a c₁₉| ≤ 10·α·MΓ(a)·Γ` on `Iθ`, for `a ≤ 4`. -/
theorem dthU_c19_le_MGa {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {a : ℕ} (ha : a ≤ 4) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[a] (c19 α) θ| ≤ 10 * α * MGa α a * Work.Spaces.Gam α θ := by
  intro θ hθ
  have hc : (0 : ℝ) < Work.Spaces.c α := by
    have := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have hk : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hc.le), div_le_iff₀ hc]
    nlinarith [(Work.Spaces.c_bounds α hα hα1).1]
  have hfun : c19 α = fun θ => (α / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
    funext t; rw [c19]
  rw [hfun, Work.Spaces.dthU_iter_const_mul]
  rw [abs_mul]
  calc |α / Work.Spaces.c α| * |Work.Spaces.dthU^[a] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ (10 * α) * (MGa α a * Work.Spaces.Gam α θ) :=
        mul_le_mul hk (dthU_Gam_le_MGa hα hα1 ha θ hθ) (abs_nonneg _) (by positivity)
    _ = 10 * α * MGa α a * Work.Spaces.Gam α θ := by ring

theorem WlInf_nonneg' (α : ℝ) (l : ℕ) (h : ℝ → ℝ → ℝ) (hmem : Work.Spaces.WlInfMem α l h) :
    0 ≤ Work.Spaces.WlInf α l h := by
  rw [Work.Spaces.WlInf]
  exact add_nonneg (Work.Spaces.wlZSum_nonneg α l h hmem) (Work.Spaces.wlThSum_nonneg α l h hmem)

/-- `∂_z^k` of the zero function is zero. -/
theorem pzIter_zero_fun (k : ℕ) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.pz, deriv_const]

/-- The constant of the pointwise families, chosen so that both the (η)- and the (γ)-bounds
of `Z19` fit into the `200000·W` shape required by `wtoHQ_of_pointwise_open`. -/
def CZ19 (C : ℝ) : ℝ := 10 ^ 20 * (1 + C) * (1 + TB19)

end Work.FTS.NonlinRows
