/-
# `Work.FTS.RegPkgGal.Der.zderiv_LGammaT`

The `C1Jet`-regularity of the linearized-with-transport coercivity operator `𝓛_Γ^T` of Elgindi's
paper (`Work.Coercivity.LGammaT`), evaluated on the `τ`-slice `g(·,·,τ)` of the profile
perturbation.

`C1Jet α S N h` (`Work.FTS.RegPkgGal.Der.Defs`) bundles, for the family
`h : (z,θ,τ) ↦ h z θ τ`, the `Jet α S N h`-data of `FTS.Regularity` (a uniform bound on the
strip `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]`, **and** the joint `α`-Hölder modulus for the metric
`|Δz| + |Δθ| + |Δτ|`) together with the `z`-differentiability of the slices `z ↦ h z θ τ` on
`z > 0`, with a derivative bounded by the same constant `N`.

The `Jet` half of the conclusion is the already proved `Work.FTS.RegPkgGal.Der.jet_LGammaT`
(the `Jet`-calculus applied to the five-term expansion of `𝓛_Γ^T`, with the six elementary
coefficient functions bounded and `α`-Hölder by `jet_coeff_all`).  What is added here is the
`z`-derivative half: from the five `z`-differentiability clauses of the hypotheses,

* `hg`: `z ↦ g z θ τ` is differentiable with `|d| ≤ N₁`,
* `hDzg`: `z ↦ D_z g(·,·,τ) z θ = z ∂_zg` is differentiable with `|d| ≤ N₂`,
* `hDthg`: `z ↦ D_θ g(·,·,τ) z θ = sin(2θ) ∂_θg` is differentiable with `|d| ≤ N₃`,
* `hL12`: `z ↦ L₁₂(g(·,·,τ))(z)` is differentiable with `|d| ≤ N₄`,
* `hL12T`: the transport projection `L₁₂(Transport g(·,·,τ))(0)` is differentiable with
  `|d| ≤ N₅` (it is `z`-independent, so the clause only bounds it),

the slice `z ↦ 𝓛_Γ^T(g(·,·,τ))(z,θ)` is differentiable on `z > 0`, with a derivative bounded by
`100·(N₁ + N₂ + N₃ + N₄ + N₅)`.

Note what is **not** needed: no second `z`-derivative of `g`.  `D_z g` is differentiated as a
whole (the hypothesis `hDzg`), exactly as in `zderiv_Nstar`, and `L₁₂`'s derivative is supplied
directly by `hL12` rather than reconstructed from `Qang`/`L12dens` (which would need
`SmoothQuad` and `HkMem α 4 g`, absent from this interface).  Every coefficient of the expansion
is a rational function of `z` with explicit `z`-derivative, bounded uniformly on `z > 0`:
`2/(1+z)` and `3/(1+z)` by `2`, respectively `3`; `2zΓ(θ)/(c(1+z)²)` by `10` (`jet_coeff_all`);
`2z²/(1+z)³·Γ(θ)/c` by `10`; and the two derivatives `(Γ(θ)/c)·2(1-z)/(1+z)³` and
`(Γ(θ)/c)·2z(2-z)/(1+z)⁴` by `20` each.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Der.Defs
import Submission.Work.FTS.RegPkgGal.Der.jet_LGammaT
import Submission.Work.FTS.RegPkgGal.Der.rhs_jet_aux
import Submission.Work.FTS.RegPkgGal.Der.jet_coeff_all
import Submission.Work.FTS.RegPkgGal.Der.ak_hasDerivAt_bound
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Helper lemmas -/

/-- **Monotonicity of the `Jet`-constant.** -/
theorem jet_mono_N {α S M N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (hMN : M ≤ N)
    (H : Work.FTS.Regularity.Jet α S M h) : Work.FTS.Regularity.Jet α S N h := by
  refine ⟨le_trans H.1 hMN, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    exact le_trans (H.2.1 z θ τ hz hθ hτ) hMN
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    refine le_trans (H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ') ?_
    exact mul_le_mul_of_nonneg_right hMN (Real.rpow_nonneg (by positivity) α)

/-- `z ↦ c/(1+z)` has derivative `-c/(1+z)²`. -/
theorem hasDerivAt_const_div_one_add (c : ℝ) {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (fun z' : ℝ => c / (1 + z')) (-(c / (1 + z) ^ 2)) z := by
  have hd : HasDerivAt (fun z' : ℝ => (1 : ℝ) + z') 1 z := by
    simpa [Pi.add_apply] using (hasDerivAt_id z).const_add (1 : ℝ)
  have hne : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  have h := (hasDerivAt_const (x := z) c).div hd hne
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `z ↦ 2z/(1+z)²` has derivative `2(1-z)/(1+z)³`. -/
theorem hasDerivAt_two_div_sq {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (fun z' : ℝ => 2 * z' / (1 + z') ^ 2) (2 * (1 - z) / (1 + z) ^ 3) z := by
  have h3 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by intro h; exact hz (by linarith))
  have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ 2) (2 * (1 + z)) z := by
    have h := Work.FTS.NonlinRows.AkRhoJetBasic.hasDerivAt_one_add_pow 2 z
    simpa using h
  have h := ((hasDerivAt_id z).const_mul 2).div h2 h3
  refine h.congr_deriv ?_
  simp only [id_eq]
  have h1z : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  field_simp
  ring

/-- The `L₁₂`-coefficient `2zΓ(θ)/(c(1+z)²)` of `𝓛_Γ^T` has derivative
`(Γ(θ)/c)·2(1-z)/(1+z)³`. -/
theorem hasDerivAt_L12coef {α : ℝ} {θ z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (fun w : ℝ => 2 * w * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + w) ^ 2))
      ((Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * (1 - z) / (1 + z) ^ 3)) z := by
  have hbase := hasDerivAt_two_div_sq hz
  have hc := hbase.const_mul (Work.Spaces.Gam α θ / Work.Spaces.c α)
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards with w
  rw [div_mul_div_comm]
  ring

/-- `|2(1-z)/(1+z)³| ≤ 2` for `z ≥ 0`. -/
theorem abs_deriv_two_div_sq_le {z : ℝ} (hz : 0 ≤ z) :
    |2 * (1 - z) / (1 + z) ^ 3| ≤ 2 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have habs : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ 3), div_le_iff₀ (by positivity)]
  have h2 : |2 * (1 - z)| ≤ 2 * (1 + z) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; linarith
  calc |2 * (1 - z)| ≤ 2 * (1 + z) := h2
    _ ≤ 2 * (1 + z) ^ 3 := by
        have h3 : (1 + z) ≤ (1 + z) ^ 3 := by
          have := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + z) (by norm_num : 1 ≤ 3)
          simpa using this
        linarith

/-- The six-term triangle inequality, in the left-nested association produced by
`HasDerivAt.add`/`HasDerivAt.sub`. -/
theorem abs_sum_six_le (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 := abs_add_le (a + b + c + d + e) f
  have h2 := abs_add_le (a + b + c + d) e
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b) c
  have h5 := abs_add_le a b
  have n1 := abs_nonneg a; have n2 := abs_nonneg b; have n3 := abs_nonneg c
  have n4 := abs_nonneg d; have n5 := abs_nonneg e; have n6 := abs_nonneg f
  calc |a + b + c + d + e + f| ≤ |a + b + c + d + e| + |f| := h1
    _ ≤ (|a + b + c + d| + |e|) + |f| := by linarith
    _ ≤ ((|a + b + c| + |d|) + |e|) + |f| := by linarith
    _ ≤ (((|a + b| + |c|) + |d|) + |e|) + |f| := by linarith
    _ ≤ ((((|a| + |b|) + |c|) + |d|) + |e|) + |f| := by linarith

/-! ## The `z`-derivative half -/

/-- **The `z`-derivative of `𝓛_Γ^T(g(·,·,τ))`.**  From the five `C1Jet` data of the datum `g`
(value, `D_z g`, `D_θ g`, `L₁₂(g)`, `L₁₂(Transport g)(0)`, each with its own `z`-derivative
bound) the slice `z ↦ 𝓛_Γ^T(g(·,·,τ))(z,θ)` is differentiable on `z > 0` with a derivative
bounded by `100·(N₁ + N₂ + N₃ + N₄ + N₅)`. -/
theorem zderiv_LGammaT_aux {α S N₁ N₂ N₃ N₄ N₅ : ℝ} {g : Work.FTS.RegPkgGal.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hg : Work.FTS.RegPkgGal.C1Jet α S N₁ g)
    (hDzg : Work.FTS.RegPkgGal.C1Jet α S N₂ (fun z θ τ => Work.Spaces.Dz (fun z θ => g z θ τ) z θ))
    (hDthg : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ => Work.Spaces.Dth (fun z θ => g z θ τ) z θ))
    (hL12 : Work.FTS.RegPkgGal.C1Jet α S N₄ (fun z θ τ => Work.Coercivity.L12f
      (Work.FTS.Regularity.gSlice g τ) z))
    (hL12T : Work.FTS.RegPkgGal.C1Jet α S N₅ (fun z θ τ => Work.Coercivity.L12f
      (fun z θ' => 3 * Work.Spaces.Dth (fun z θ => g z θ τ) z θ' / (1 + z)) 0)) :
    ∃ Nc : ℝ, 0 ≤ Nc ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d z ∧ |d| ≤ Nc := by
  have hgam := jca_gam_div_c_bdd (α := α) hα hα13
  have hcbb := (jca_zgam_facts (α := α) hα hα13).1
  have hAKb := (rhsJet_ak_bounds (α := α) hα hα13).1
  refine ⟨100 * (N₁ + N₂ + N₃ + N₄ + N₅),
    by linarith [hg.1.1, hDzg.1.1, hDthg.1.1, hL12.1.1, hL12T.1.1], ?_⟩
  intro τ hτ θ hθ z hz
  have hz0 : 0 < z := hz
  have hzn1 : z ≠ -1 := by intro h; linarith
  -- the five `z`-differentiability hypotheses and the five value bounds at `(z,θ,τ)`
  obtain ⟨d1, hd1, hb1⟩ := hg.2 τ hτ θ hθ z hz
  obtain ⟨d2, hd2, hb2⟩ := hDzg.2 τ hτ θ hθ z hz
  obtain ⟨d3, hd3, hb3⟩ := hDthg.2 τ hτ θ hθ z hz
  obtain ⟨d4, hd4, hb4⟩ := hL12.2 τ hτ θ hθ z hz
  have hG1 : |Work.FTS.Regularity.gSlice g τ z θ| ≤ N₁ := hg.1.2.1 z θ τ hz0.le hθ hτ
  have hG2 : |Work.Spaces.Dz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ N₂ :=
    hDzg.1.2.1 z θ τ hz0.le hθ hτ
  have hG3 : |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ| ≤ N₃ :=
    hDthg.1.2.1 z θ τ hz0.le hθ hτ
  have hG4 : |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z| ≤ N₄ :=
    hL12.1.2.1 z θ τ hz0.le hθ hτ
  have hG5 : |Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Regularity.gSlice g τ)) 0|
      ≤ N₅ := hL12T.1.2.1 z θ τ hz0.le hθ hτ
  -- the two coefficients whose derivatives occur in the expansion of `𝓛_Γ^T`
  set fc : ℝ := Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
    / Work.Spaces.c (Work.FTS.Regularity.pExp α) with hfc
  set cc : ℝ → ℝ := fun w => 2 * w * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
      / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + w) ^ 2) with hcc
  set ca : ℝ → ℝ := fun w => (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
      / Work.Spaces.c (Work.FTS.Regularity.pExp α)) * (2 * w ^ 2 / (1 + w) ^ 3) with hca
  have hfcb : |fc| ≤ 10 := by rw [hfc]; exact hgam θ hθ
  have hccb : |cc z| ≤ 10 := by rw [hcc]; exact hcbb z hz0.le θ hθ
  have hcab : |ca z| ≤ 10 := by rw [hca]; exact hAKb z hz0.le θ hθ
  have hccdb : |fc * (2 * (1 - z) / (1 + z) ^ 3)| ≤ 20 := by
    rw [abs_mul]
    calc |fc| * |2 * (1 - z) / (1 + z) ^ 3| ≤ 10 * 2 :=
          mul_le_mul hfcb (abs_deriv_two_div_sq_le hz0.le) (abs_nonneg _) (by norm_num)
      _ = 20 := by norm_num
  have hcadb : |fc * (2 * z * (2 - z) / (1 + z) ^ 4)| ≤ 20 := by
    rw [abs_mul]
    calc |fc| * |2 * z * (2 - z) / (1 + z) ^ 4| ≤ 10 * 2 :=
          mul_le_mul hfcb (abs_akPsi_deriv_le_two hz0) (abs_nonneg _) (by norm_num)
      _ = 20 := by norm_num
  have hφb : |-(2 / (1 + z) ^ 2)| ≤ 2 := by
    rw [abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [hz0]
  have hφvb : |2 / (1 + z)| ≤ 2 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
    linarith
  have hψb : |-(3 / (1 + z) ^ 2)| ≤ 3 := by
    rw [abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [hz0]
  have hψvb : |3 / (1 + z)| ≤ 3 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
    linarith
  -- the derivatives of the two coefficients
  have hccd : HasDerivAt cc (fc * (2 * (1 - z) / (1 + z) ^ 3)) z := by
    rw [hcc, hfc]
    exact hasDerivAt_L12coef (α := Work.FTS.Regularity.pExp α) (θ := θ) hzn1
  have hcad : HasDerivAt ca (fc * (2 * z * (2 - z) / (1 + z) ^ 4)) z := by
    rw [hca, hfc]
    exact (Work.FTS.NonlinRows.AkRhoJetBasic.hasDerivAt_akPsi hzn1).const_mul
      (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ / Work.Spaces.c (Work.FTS.Regularity.pExp α))
  -- the five slice derivatives
  have h1 : HasDerivAt (fun w : ℝ => Work.FTS.Regularity.gSlice g τ w θ) d1 z := hd1
  have h2 : HasDerivAt (fun w : ℝ => Work.Spaces.Dz (Work.FTS.Regularity.gSlice g τ) w θ) d2 z :=
    hd2
  have h3 : HasDerivAt (fun w : ℝ => Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) w θ) d3 z :=
    hd3
  have h4 : HasDerivAt (fun w : ℝ => Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) w) d4 z :=
    hd4
  have hP : HasDerivAt (fun w : ℝ => 2 / (1 + w)) (-(2 / (1 + z) ^ 2)) z :=
    hasDerivAt_const_div_one_add 2 hzn1
  have hQ : HasDerivAt (fun w : ℝ => 3 / (1 + w)) (-(3 / (1 + z) ^ 2)) z :=
    hasDerivAt_const_div_one_add 3 hzn1
  have hAa := hP.mul h1
  have hBb := hccd.mul h4
  have hCc := hQ.mul h3
  have hDd := hcad.mul (hasDerivAt_const (x := z)
    (Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Regularity.gSlice g τ)) 0))
  have hbig := ((((h1.add h2).sub hAa).sub hBb).sub hCc).add hDd
  -- the derivative, split into five blocks whose absolute values are bounded separately
  set A : ℝ := -(2 / (1 + z) ^ 2) * Work.FTS.Regularity.gSlice g τ z θ + 2 / (1 + z) * d1
    with hAdef
  set B : ℝ := fc * (2 * (1 - z) / (1 + z) ^ 3)
    * Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z + cc z * d4 with hBdef
  set C : ℝ := -(3 / (1 + z) ^ 2) * Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ
    + 3 / (1 + z) * d3 with hCdef
  set Dv : ℝ := fc * (2 * z * (2 - z) / (1 + z) ^ 4)
    * Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Regularity.gSlice g τ)) 0
    + ca z * 0 with hDvdef
  have hbA : |A| ≤ 2 * N₁ + 2 * N₁ := by
    rw [hAdef]
    calc |-(2 / (1 + z) ^ 2) * Work.FTS.Regularity.gSlice g τ z θ + 2 / (1 + z) * d1|
        ≤ |-(2 / (1 + z) ^ 2) * Work.FTS.Regularity.gSlice g τ z θ| + |2 / (1 + z) * d1| :=
          abs_add_le _ _
      _ = |-(2 / (1 + z) ^ 2)| * |Work.FTS.Regularity.gSlice g τ z θ| + |2 / (1 + z)| * |d1| := by
          simp only [abs_mul]
      _ ≤ 2 * N₁ + 2 * N₁ := add_le_add
          (mul_le_mul hφb hG1 (abs_nonneg _) (by norm_num))
          (mul_le_mul hφvb hb1 (abs_nonneg _) (by norm_num))
  have hbB : |B| ≤ 20 * N₄ + 10 * N₄ := by
    rw [hBdef]
    calc |fc * (2 * (1 - z) / (1 + z) ^ 3)
          * Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z + cc z * d4|
        ≤ |fc * (2 * (1 - z) / (1 + z) ^ 3)
            * Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z| + |cc z * d4| :=
          abs_add_le _ _
      _ = |fc * (2 * (1 - z) / (1 + z) ^ 3)|
            * |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z| + |cc z| * |d4| := by
          simp only [abs_mul]
      _ ≤ 20 * N₄ + 10 * N₄ := add_le_add
          (mul_le_mul hccdb hG4 (abs_nonneg _) (by norm_num))
          (mul_le_mul hccb hb4 (abs_nonneg _) (by norm_num))
  have hbC : |C| ≤ 3 * N₃ + 3 * N₃ := by
    rw [hCdef]
    calc |-(3 / (1 + z) ^ 2) * Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ
          + 3 / (1 + z) * d3|
        ≤ |-(3 / (1 + z) ^ 2) * Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
            + |3 / (1 + z) * d3| := abs_add_le _ _
      _ = |-(3 / (1 + z) ^ 2)| * |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
            + |3 / (1 + z)| * |d3| := by simp only [abs_mul]
      _ ≤ 3 * N₃ + 3 * N₃ := add_le_add
          (mul_le_mul hψb hG3 (abs_nonneg _) (by norm_num))
          (mul_le_mul hψvb hb3 (abs_nonneg _) (by norm_num))
  have hbDv : |Dv| ≤ 20 * N₅ := by
    have h0 : Dv = fc * (2 * z * (2 - z) / (1 + z) ^ 4)
        * Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Regularity.gSlice g τ)) 0 := by
      rw [hDvdef]; ring
    rw [h0, abs_mul]
    exact mul_le_mul hcadb hG5 (abs_nonneg _) (by norm_num)
  refine ⟨d1 + d2 - A - B - C + Dv, ?_, ?_⟩
  · -- the target function is exactly the sum of the five blocks
    refine hbig.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => ?_))
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    rw [LGammaT_eq_expansion]
  · -- the bound on the derivative
    have htri : |d1 + d2 - A - B - C + Dv| ≤ |d1| + |d2| + |A| + |B| + |C| + |Dv| := by
      have he : d1 + d2 - A - B - C + Dv = d1 + d2 + (-A) + (-B) + (-C) + Dv := by ring
      rw [he]
      simpa [abs_neg] using abs_sum_six_le d1 d2 (-A) (-B) (-C) Dv
    have h1' : 0 ≤ N₁ := hg.1.1
    have h2' : 0 ≤ N₂ := hDzg.1.1
    have h3' : 0 ≤ N₃ := hDthg.1.1
    have h4' : 0 ≤ N₄ := hL12.1.1
    have h5' : 0 ≤ N₅ := hL12T.1.1
    linarith [htri, hbA, hbB, hbC, hbDv, abs_nonneg d1, abs_nonneg d2, hb1, hb2]

/-! ## The requested theorem -/

theorem zderiv_LGammaT {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {N₁ N₂ N₃ N₄ N₅ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hg : Work.FTS.RegPkgGal.C1Jet α S N₁ g)
    (hDzg : Work.FTS.RegPkgGal.C1Jet α S N₂ (fun z θ τ => Work.Spaces.Dz (fun z θ => g z θ τ) z θ))
    (hDthg : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ => Work.Spaces.Dth (fun z θ => g z θ τ) z θ))
    (hL12 : Work.FTS.RegPkgGal.C1Jet α S N₄ (fun z θ τ => Work.Coercivity.L12f
      (Work.FTS.Regularity.gSlice g τ) z))
    (hL12T : Work.FTS.RegPkgGal.C1Jet α S N₅ (fun z θ τ => Work.Coercivity.L12f
      (fun z θ' => 3 * Work.Spaces.Dth (fun z θ => g z θ τ) z θ' / (1 + z)) 0)) :
    ∃ Nc : ℝ, Work.FTS.RegPkgGal.C1Jet α S Nc
      (fun z θ τ => Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) z θ) := by
  -- the `Jet` half — the five-term expansion with the coefficient estimates of `jet_coeff_all`
  obtain ⟨Nc₁, hJ⟩ := jet_LGammaT hα hα13 hS hg.1 hDzg.1 hDthg.1 hL12.1 hL12T.1
  -- the `z`-derivative half
  obtain ⟨Nc₂, -, hZ⟩ := zderiv_LGammaT_aux hα hα13 hS hg hDzg hDthg hL12 hL12T
  refine ⟨max Nc₁ Nc₂, ⟨jet_mono_N (le_max_left _ _) hJ, ?_⟩⟩
  intro τ hτ θ hθ z hz
  obtain ⟨d, hd, hb⟩ := hZ τ hτ θ hθ z hz
  exact ⟨d, hd, le_trans hb (le_max_right _ _)⟩

end Work.FTS.RegPkgGal.Der
