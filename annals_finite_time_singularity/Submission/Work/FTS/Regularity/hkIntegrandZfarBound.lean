/-
Copyright: work module for the Elgindi finite-time singularity project.

# The far-field `ℋ⁴`-bound for the cut-off profile at scale `4`

This file proves

`Work.FTS.Regularity.hkIntegrandZfarBound`: there is `C ≥ 0` such that for every
`z ≥ 4` and every `θ ∈ Iθ`,

`HkIntegrand (3α) 4 (fun z θ => -F_*(3α) z θ · (1 - χ(z/4))) z θ
    ≤ C · angMaj (3α) θ / (1+z)²`,

for `0 < α ≤ 1/3`.  This is the weighted `ℋ⁴`-bound of the *far part* of the
localised profile (`Work.Stability.zfar 4 (F_*(3α))`) that the localisation
chapter of the route (`FTS_AUDIT_LEAD.md`, node N9) needs: the profile is cut off
at scale `L = 4`, and `(1 - χ(z/4))` vanishes identically for `z ≥ 8`, so the
estimate is a far-field statement.

## Structure of the proof

The profile is a *separated product*:

`F_*(β) z θ = (β/c(β))·Γ(θ)·φ(z)`, `φ = FM.Fstar = 2z/(1+z)²`,

so with `A(θ) = -(β/c(β))·Γ(θ)` and `ψ(z) = φ(z)·(1 - χ(z/4))` the far part is
`f = A ⊗ ψ`, and the iterated operators separate:

* `D_z^i f = A(θ)·(Z^[i] ψ)(z)` (`Z = z∂_z`),
* `D_z^jD_θ^i f = (d^[i]A)(θ)·(Z^[j] ψ)(z)`.

Hence

`HkIntegrand β 4 f z θ = ∑_{i≤4} (A(θ)Z^iψ(z)·w/ sin(2θ)^{η/2})²
 + ∑_{1≤i, i+j≤4} ((d^iA)(θ)Z^jψ(z)·Wt)²`,

and the two sums are estimated term by term with the angular bounds
`|D_θ^iΓ| ≤ 100000·Γ` (`DthIter_Gam_abs_le`) and the radial bound
`|Z^jψ(z)| ≤ K/z` for `z ≥ 4`.

The radial bound is where the localisation enters: by the one-variable Leibniz
rule (`DzIter_mul_smoothQuad`) applied to the two factors `φ` and `1 - χ(·/4)`,

`Z^j ψ = ∑_{b≤j} binom(j,b)·(Z^bφ)·(Z^{j-b}(1-χ(·/4)))`,

and each factor is bounded by `1000/z` (`DzIter_FM_Fstar_abs_le`) and by the
`z`-independent constant of `DzIter_oneSubChi_bound`.  The weight `w(z)`
contributes `w² /z² = (1+z)⁴/z⁶ ≤ 4/(1+z)²` for `z ≥ 4`, which is exactly the
`/(1+z)²` decay requested.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.FTS.LocData.DzIter_oneSubChi_bound
import Submission.Work.FTS.LocData.DzIter_FM_Fstar_abs_le
import Submission.Work.FTS.LocData.Gam_le_sin_two_rpow
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Regularity

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. The far cut-off at scale `4` and its separated product structure -/

/-- The complementary far factor at scale `4`: `1 - χ(z/4)`. -/
noncomputable def zcut4 (z : ℝ) : ℝ := 1 - Work.Stability.chi (z / 4)

/-- The radial factor of the far part of `F_*` at scale `4`. -/
noncomputable def psi4 (z : ℝ) : ℝ := Work.FM.Fstar z * zcut4 z

/-- The angular factor `-(β/c(β))·Γ(θ)` of the profile `F_*(β)`. -/
noncomputable def angF (β : ℝ) (θ : ℝ) : ℝ :=
  -(β / Work.Spaces.c β) * Work.Spaces.Gam β θ

/-- The far part of the profile `F_*(β)` at scale `4`, as a function of `(z,θ)`. -/
noncomputable def fcut (β : ℝ) (z θ : ℝ) : ℝ :=
  -Work.Construction.Fstar β z θ * (1 - Work.Stability.chi (z / 4))

theorem zcut4_apply (z : ℝ) : zcut4 z = 1 - Work.Stability.chi (z / 4) := rfl

theorem psi4_apply (z : ℝ) : psi4 z = Work.FM.Fstar z * (1 - Work.Stability.chi (z / 4)) := rfl

theorem angF_apply (β θ : ℝ) : angF β θ = -(β / Work.Spaces.c β) * Work.Spaces.Gam β θ := rfl

theorem fcut_apply (β z θ : ℝ) :
    fcut β z θ = -Work.Construction.Fstar β z θ * (1 - Work.Stability.chi (z / 4)) := rfl

/-- **The far part of `F_*(β)` is the product of an angular and a radial factor.** -/
theorem fcut_eq_prod (β z θ : ℝ) : fcut β z θ = angF β θ * psi4 z := by
  simp only [fcut, angF, psi4, zcut4, Work.Construction.Fstar, Work.FM.Fstar]
  ring

/-! ## 2. Separation of variables for `D_z` and `D_θ` -/

/-- `Z = z∂_z` commutes with multiplication by a constant. -/
theorem Zop_const_mul (c : ℝ) (B : ℝ → ℝ) :
    Work.Spaces.Zop (fun z => c * B z) = fun z => c * Work.Spaces.Zop B z := by
  funext z
  simp only [Work.Spaces.Zop]
  rw [deriv_const_mul_field]
  ring

/-- The iterates of `Z = z∂_z` commute with multiplication by a constant. -/
theorem Zop_iter_const_mul (j : ℕ) (c : ℝ) (B : ℝ → ℝ) :
    (Work.Spaces.Zop^[j]) (fun z => c * B z) = fun z => c * (Work.Spaces.Zop^[j]) B z := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', Zop_const_mul]

/-- **`D_θ` on a separated product** acts on the `θ`-factor. -/
theorem DthIter_sep (i : ℕ) (A B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun z θ => A θ * B z) z θ = (Work.Spaces.dthU^[i]) A θ * B z :=
  Work.Spaces.DthIter_decomp i A B z θ

/-- **`D_z` on a separated product** acts on the `z`-factor. -/
theorem DzIter_sep (j : ℕ) (C B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter j (fun z θ => C θ * B z) z θ = C θ * (Work.Spaces.Zop^[j]) B z := by
  have h1 : (fun z' => Work.Spaces.DzIter j (fun z θ => C θ * B z) z' θ)
      = (fun z' => (Work.Spaces.Zop^[j]) (fun z => C θ * B z) z') := by
    funext z'
    exact congrFun (Work.FTS.LocData.Zop_iterate_slice j (fun z θ => C θ * B z) θ) z'
  rw [congrFun h1 z, congrFun (Zop_iter_const_mul j (C θ) B) z]

/-- The `z`-derivatives of the far part of `F_*(β)`. -/
theorem DzIter_fcut (β : ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter i (fcut β) z θ = angF β θ * (Work.Spaces.Zop^[i]) psi4 z := by
  have hprod : fcut β = fun z θ => angF β θ * psi4 z :=
    funext fun z => funext fun θ => fcut_eq_prod β z θ
  rw [hprod]
  exact DzIter_sep i (angF β) psi4 z θ

/-- The mixed derivatives of the far part of `F_*(β)`. -/
theorem mixed_fcut (β : ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fcut β) z θ
      = (Work.Spaces.dthU^[i]) (angF β) θ * (Work.Spaces.Zop^[j]) psi4 z := by
  have hprod : fcut β = fun z θ => angF β θ * psi4 z :=
    funext fun z => funext fun θ => fcut_eq_prod β z θ
  have hDth : Work.Spaces.DthIter i (fcut β)
      = fun z θ => (Work.Spaces.dthU^[i]) (angF β) θ * psi4 z := by
    rw [hprod]
    funext z θ
    exact DthIter_sep i (angF β) psi4 z θ
  rw [Work.Spaces.mixed, hDth]
  exact DzIter_sep j ((Work.Spaces.dthU^[i]) (angF β)) psi4 z θ

/-! ## 3. Smoothness of the two radial factors on `(-1,∞)` -/

theorem contDiffOn_zcut4 :
    ContDiffOn ℝ Work.Stability.smoothOrder zcut4 (Set.Ioi (-1)) := by
  have hsm : ContDiff ℝ Work.Stability.smoothOrder
      (fun x : ℝ => (1 : ℝ) - Work.Stability.chi x) :=
    contDiff_const.sub Work.Stability.chi_contDiff
  have h : ContDiff ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 1 - Work.Stability.chi (z / 4)) :=
    hsm.comp (contDiff_id.div_const 4)
  exact h.contDiffOn

theorem contDiffOn_FstarZ :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.FM.Fstar z)
      (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    (contDiff_const.mul contDiff_id).contDiffOn
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    ((contDiff_const.add contDiff_id).pow 2).contDiffOn
  have h : ContDiffOn ℝ Work.Stability.smoothOrder
      ((fun z : ℝ => 2 * z) / (fun z : ℝ => (1 + z) ^ 2)) (Set.Ioi (-1)) :=
    h1.div h2 (fun z hz => by
      have hz' : (-1 : ℝ) < z := hz
      have hpos : (0 : ℝ) < 1 + z := by linarith
      positivity)
  refine h.congr (fun z hz => ?_)
  show (2 * z) / (1 + z) ^ 2 = Work.FM.Fstar z
  rw [Work.FM.Fstar]

/-! ## 4. The radial bound `|Z^j ψ(z)| ≤ K/z` for `z ≥ 4`, `j ≤ 4` -/

theorem exists_Zop_iter_psi4_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 4 ≤ z →
      |(Work.Spaces.Zop^[j]) psi4 z| ≤ K / z := by
  obtain ⟨M0, hM0⟩ := Work.FTS.LocData.DzIter_oneSubChi_bound 4 (by norm_num)
  obtain ⟨C0, hC0⟩ := Work.FTS.LocData.DzIter_FM_Fstar_abs_le
  refine ⟨16 * (max C0 0) * (max M0 0), by positivity, fun j hj z hz4 => ?_⟩
  have hz1 : 1 ≤ z := by linarith
  have hzpos : 0 < z := by linarith
  have hzIz : z ∈ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hF : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' : ℝ => (fun z _ => Work.FM.Fstar z) z' (0 : ℝ)) (Set.Ioi (-1)) :=
    contDiffOn_FstarZ
  have hC : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z' : ℝ => (fun z _ => zcut4 z) z' (0 : ℝ)) (Set.Ioi (-1)) :=
    contDiffOn_zcut4
  have hleib := Work.FTS.LocData.DzIter_mul_smoothQuad (j := j)
    (f := fun z _ => Work.FM.Fstar z) (g := fun z _ => zcut4 z)
    (z := z) (θ := (0 : ℝ)) hzIz hF hC
  have hzop : (Work.Spaces.Zop^[j]) psi4 z
      = Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z * zcut4 z) z (0 : ℝ) :=
    (congrFun (Work.FTS.LocData.Zop_iterate_slice j
      (fun z _ => Work.FM.Fstar z * zcut4 z) (0 : ℝ)) z).symm
  rw [hzop, hleib]
  have hterm : ∀ b ∈ Finset.range (j + 1),
      |(j.choose b : ℝ) * (Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z (0 : ℝ)
          * Work.Spaces.DzIter (j - b) (fun z _ => zcut4 z) z (0 : ℝ))|
        ≤ (j.choose b : ℝ) * (max C0 0 / z * max M0 0) := by
    intro b hb
    have hbj : b ≤ j := by rw [Finset.mem_range] at hb; omega
    have hb4 : b ≤ 4 := by omega
    have hjb4 : j - b ≤ 4 := by omega
    have h1 : |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z (0 : ℝ)| ≤ max C0 0 / z :=
      le_trans (hC0 b hb4 z hz1 (0 : ℝ))
        (div_le_div_of_nonneg_right (le_max_left _ _) hzpos.le)
    have h2 : |Work.Spaces.DzIter (j - b) (fun z _ => zcut4 z) z (0 : ℝ)| ≤ max M0 0 :=
      le_trans (hM0 (j - b) hjb4 z hzIz (0 : ℝ)) (le_max_left _ _)
    have h3 : (0 : ℝ) ≤ max C0 0 / z := div_nonneg (le_max_right _ _) hzpos.le
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j.choose b : ℝ))]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul h1 h2 (abs_nonneg _) h3) (by positivity)
  calc |∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z (0 : ℝ)
          * Work.Spaces.DzIter (j - b) (fun z _ => zcut4 z) z (0 : ℝ))|
      ≤ ∑ b ∈ Finset.range (j + 1), |(j.choose b : ℝ)
          * (Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z (0 : ℝ)
            * Work.Spaces.DzIter (j - b) (fun z _ => zcut4 z) z (0 : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) * (max C0 0 / z * max M0 0) :=
        Finset.sum_le_sum hterm
    _ = (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) * (max C0 0 / z * max M0 0) := by
        rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ j * (max C0 0 / z * max M0 0) := by
        rw [show (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) = (2 : ℝ) ^ j from by
          have h := Nat.sum_range_choose j
          exact_mod_cast h]
    _ ≤ 16 * (max C0 0) * (max M0 0) / z := by
        have hA : (0 : ℝ) ≤ max C0 0 := le_max_right _ _
        have hM : (0 : ℝ) ≤ max M0 0 := le_max_right _ _
        have h2j : (2 : ℝ) ^ j ≤ 16 := by
          have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
          norm_num at h
          exact h
        rw [show (2 : ℝ) ^ j * (max C0 0 / z * max M0 0)
              = (2 : ℝ) ^ j * (max C0 0 * max M0 0) / z by ring]
        rw [show 16 * max C0 0 * max M0 0 / z = 16 * (max C0 0 * max M0 0) / z by ring]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2j (mul_nonneg hA hM)) hzpos.le

/-! ## 5. Angular bounds -/

/-- The iterates of `d_θ = sin(2θ)∂_θ` commute with multiplication by a constant. -/
theorem dthU_iter_const_mul (i : ℕ) (c : ℝ) (B : ℝ → ℝ) :
    (Work.Spaces.dthU^[i]) (fun θ => c * B θ) = fun θ => c * (Work.Spaces.dthU^[i]) B θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
        Work.Spaces.dthU_const_mul]

/-- **The angular factor and its angular derivatives**:
`|d_θ^i A(θ)| ≤ |β/c(β)|·100000·Γ(θ)` for `i ≤ 4`. -/
theorem dthU_iter_angF_abs_le {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) (i : ℕ) (hi : i ≤ 4) :
    |(Work.Spaces.dthU^[i]) (angF β) θ|
      ≤ |β / Work.Spaces.c β| * 100000 * Work.Spaces.Gam β θ := by
  have hconst : (Work.Spaces.dthU^[i]) (angF β)
      = fun θ => -(β / Work.Spaces.c β)
          * (Work.Spaces.dthU^[i]) (fun t => Work.Spaces.Gam β t) θ := by
    rw [show angF β = fun θ => -(β / Work.Spaces.c β) * Work.Spaces.Gam β θ from rfl]
    exact dthU_iter_const_mul i (-(β / Work.Spaces.c β)) (fun t => Work.Spaces.Gam β t)
  have hgam : |(Work.Spaces.dthU^[i]) (fun t => Work.Spaces.Gam β t) θ|
      ≤ 100000 * Work.Spaces.Gam β θ := by
    have h := Work.FTS.LocData.DthIter_Gam_abs_le i hi β hβ hβ1 hθ
    rwa [Work.FTS.LocData.DthIter_rad_eq i (fun t => Work.Spaces.Gam β t) 0 θ] at h
  rw [hconst, abs_mul, abs_neg]
  calc |β / Work.Spaces.c β| * |(Work.Spaces.dthU^[i]) (fun t => Work.Spaces.Gam β t) θ|
      ≤ |β / Work.Spaces.c β| * (100000 * Work.Spaces.Gam β θ) :=
        mul_le_mul_of_nonneg_left hgam (abs_nonneg _)
    _ = |β / Work.Spaces.c β| * 100000 * Work.Spaces.Gam β θ := by ring

/-! ## 6. Elementary weight inequalities -/

/-- `w(z)²/z² ≤ 4/(1+z)²` for `z ≥ 4`, where `w z = (1+z)²/z²`. -/
theorem w_sq_div_le (z : ℝ) (hz : 4 ≤ z) :
    (Work.Spaces.w z) ^ 2 / z ^ 2 ≤ 4 / (1 + z) ^ 2 := by
  have hzpos : (0 : ℝ) < z := by linarith
  have hzeq : (Work.Spaces.w z) ^ 2 / z ^ 2 = (1 + z) ^ 4 / z ^ 6 := by
    rw [Work.Spaces.w]
    field_simp
  rw [hzeq]
  have hkey : (1 + z) ^ 6 ≤ 4 * z ^ 6 := by
    have hle : 1 + z ≤ (5 / 4) * z := by linarith
    have h2 : (1 + z) ^ 6 ≤ ((5 / 4) * z) ^ 6 := pow_le_pow_left₀ (by linarith) hle 6
    have h3 : ((5 / 4) * z) ^ 6 = ((5 / 4 : ℝ) ^ 6) * z ^ 6 := by ring
    have h4 : ((5 / 4 : ℝ) ^ 6) ≤ 4 := by norm_num
    calc (1 + z) ^ 6 ≤ ((5 / 4) * z) ^ 6 := h2
      _ = ((5 / 4 : ℝ) ^ 6) * z ^ 6 := h3
      _ ≤ 4 * z ^ 6 := mul_le_mul_of_nonneg_right h4 (by positivity)
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 6)
    (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  rw [show (1 + z) ^ 4 * (1 + z) ^ 2 = (1 + z) ^ 6 by ring]
  exact hkey

/-! ## 7. The two sum bounds -/

/-- **The `D_z`-part of the far-field `ℋ⁴`-bound.** -/
theorem hkIntegrand_zfar_T1 {β : ℝ} (hβ : 0 < β) {K : ℝ}
    (hKb : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 4 ≤ z → |(Work.Spaces.Zop^[j]) psi4 z| ≤ K / z)
    {z : ℝ} (hz4 : 4 ≤ z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (∑ i ∈ Finset.range 5,
      (Work.Spaces.DzIter i (fcut β) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 5 * (4 * (β / Work.Spaces.c β) ^ 2 * K ^ 2
          * Work.FTS.LocData.angMaj β θ / (1 + z) ^ 2) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_mem_Icc
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hang : Work.Spaces.Gam β θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.FTS.LocData.angMaj β θ := by
    rw [Work.FTS.LocData.angMaj_apply]
    have h := mul_nonneg (sq_nonneg (Work.Spaces.Gam β θ))
      (Real.rpow_nonneg hs0 (-(Work.Spaces.gam β)))
    linarith
  have hang0 : 0 ≤ Work.FTS.LocData.angMaj β θ := Work.FTS.LocData.angMaj_nonneg hθ
  have hDpos : (0 : ℝ) < (1 + z) ^ 2 := by
    have h1z : (0 : ℝ) < 1 + z := by linarith
    positivity
  have hwfact := w_sq_div_le z hz4
  have hper : ∀ i ∈ Finset.range 5,
      (Work.Spaces.DzIter i (fcut β) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 4 * (β / Work.Spaces.c β) ^ 2 * K ^ 2 * Work.FTS.LocData.angMaj β θ
        / (1 + z) ^ 2 := by
    intro i hi
    have hi4 : i ≤ 4 := by rw [Finset.mem_range] at hi; omega
    rw [DzIter_fcut β i z θ]
    rw [show angF β θ * (Work.Spaces.Zop^[i]) psi4 z
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        = angF β θ * (((Work.Spaces.Zop^[i]) psi4 z * Work.Spaces.w z)
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) from by ring]
    rw [Work.Spaces.sq_mul_div_rpow (angF β θ)
      ((Work.Spaces.Zop^[i]) psi4 z * Work.Spaces.w z) (Real.sin (2 * θ))
      Work.Spaces.eta hs0 (by norm_num [Work.Spaces.eta])]
    have hA2 : (angF β θ) ^ 2 = (β / Work.Spaces.c β) ^ 2 * (Work.Spaces.Gam β θ) ^ 2 := by
      rw [angF_apply]; ring
    have hZs : ((Work.Spaces.Zop^[i]) psi4 z * Work.Spaces.w z) ^ 2
        ≤ K ^ 2 * (4 / (1 + z) ^ 2) := by
      have hw0 : 0 ≤ Work.Spaces.w z := by
        rw [Work.Spaces.w]
        exact div_nonneg (by positivity) (by positivity)
      have hle : |(Work.Spaces.Zop^[i]) psi4 z * Work.Spaces.w z|
          ≤ K / z * Work.Spaces.w z := by
        rw [abs_mul, abs_of_nonneg hw0]
        exact mul_le_mul_of_nonneg_right (hKb i hi4 z hz4) hw0
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hle 2
      have hkey : (K / z * Work.Spaces.w z) ^ 2
          = K ^ 2 * ((Work.Spaces.w z) ^ 2 / z ^ 2) := by ring
      calc ((Work.Spaces.Zop^[i]) psi4 z * Work.Spaces.w z) ^ 2
          ≤ (K / z * Work.Spaces.w z) ^ 2 := by simpa only [sq_abs] using hsq
        _ = K ^ 2 * ((Work.Spaces.w z) ^ 2 / z ^ 2) := hkey
        _ ≤ K ^ 2 * (4 / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left hwfact (sq_nonneg K)
    calc (angF β θ) ^ 2 * ((Work.Spaces.Zop^[i]) psi4 z * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        = (β / Work.Spaces.c β) ^ 2
          * (Work.Spaces.Gam β θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          * ((Work.Spaces.Zop^[i]) psi4 z * Work.Spaces.w z) ^ 2 := by
          rw [hA2]; ring
      _ ≤ (β / Work.Spaces.c β) ^ 2 * Work.FTS.LocData.angMaj β θ
          * (K ^ 2 * (4 / (1 + z) ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hang (sq_nonneg _)) hZs (by positivity)
            (mul_nonneg (sq_nonneg _) hang0)
      _ = 4 * (β / Work.Spaces.c β) ^ 2 * K ^ 2 * Work.FTS.LocData.angMaj β θ
          / (1 + z) ^ 2 := by ring
  calc (∑ i ∈ Finset.range 5,
        (Work.Spaces.DzIter i (fcut β) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∑ _i ∈ Finset.range 5, (4 * (β / Work.Spaces.c β) ^ 2 * K ^ 2
          * Work.FTS.LocData.angMaj β θ / (1 + z) ^ 2) := Finset.sum_le_sum hper
    _ = 5 * (4 * (β / Work.Spaces.c β) ^ 2 * K ^ 2
          * Work.FTS.LocData.angMaj β θ / (1 + z) ^ 2) := by
        rw [Finset.sum_const, Finset.card_range]
        norm_num

/-- **The mixed part of the far-field `ℋ⁴`-bound.** -/
theorem hkIntegrand_zfar_T2 {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {K : ℝ}
    (hKb : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 4 ≤ z → |(Work.Spaces.Zop^[j]) psi4 z| ≤ K / z)
    {z : ℝ} (hz4 : 4 ≤ z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 then
        (Work.Spaces.mixed j i (fcut β) z θ * Work.Spaces.Wt β z θ) ^ 2 else 0))
      ≤ 25 * (4 * (β / Work.Spaces.c β) ^ 2 * 100000 ^ 2 * K ^ 2
          * Work.FTS.LocData.angMaj β θ / (1 + z) ^ 2) := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_mem_Icc
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hang : Work.Spaces.Gam β θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam β))
      ≤ Work.FTS.LocData.angMaj β θ := by
    rw [Work.FTS.LocData.angMaj_apply]
    have h := mul_nonneg (sq_nonneg (Work.Spaces.Gam β θ))
      (Real.rpow_nonneg hs0 (-(Work.Spaces.eta)))
    linarith
  have hang0 : 0 ≤ Work.FTS.LocData.angMaj β θ := Work.FTS.LocData.angMaj_nonneg hθ
  have hsqGam : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam β / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam β)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
    congr 1
    ring
  have hDpos : (0 : ℝ) < (1 + z) ^ 2 := by
    have h1z : (0 : ℝ) < 1 + z := by linarith
    positivity
  have hwfact := w_sq_div_le z hz4
  have hper : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      (if 1 ≤ i ∧ i + j ≤ 4 then
        (Work.Spaces.mixed j i (fcut β) z θ * Work.Spaces.Wt β z θ) ^ 2 else 0)
      ≤ 4 * (β / Work.Spaces.c β) ^ 2 * 100000 ^ 2 * K ^ 2
          * Work.FTS.LocData.angMaj β θ / (1 + z) ^ 2 := by
    intro i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc]
      have hi4 : i ≤ 4 := by rw [Finset.mem_range] at hi; omega
      have hj4 : j ≤ 4 := by rw [Finset.mem_range] at hj; omega
      rw [mixed_fcut β j i z θ]
      simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
      rw [show (Work.Spaces.dthU^[i]) (angF β) θ * (Work.Spaces.Zop^[j]) psi4 z
            * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam β / 2)))
          = (Work.Spaces.dthU^[i]) (angF β) θ
            * (((Work.Spaces.Zop^[j]) psi4 z * Work.Spaces.w z)
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam β / 2))) from by ring]
      rw [mul_pow, mul_pow, hsqGam]
      have hAle : ((Work.Spaces.dthU^[i]) (angF β) θ) ^ 2
          ≤ (β / Work.Spaces.c β) ^ 2 * 100000 ^ 2 * (Work.Spaces.Gam β θ) ^ 2 := by
        have hb := dthU_iter_angF_abs_le hβ hβ1 hθ i hi4
        have h2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        rw [sq_abs] at h2
        refine le_trans h2 (le_of_eq ?_)
        rw [show (|β / Work.Spaces.c β| * 100000 * Work.Spaces.Gam β θ) ^ 2
              = |β / Work.Spaces.c β| ^ 2 * 100000 ^ 2 * (Work.Spaces.Gam β θ) ^ 2
            from by ring]
        rw [sq_abs]
      have hZs : ((Work.Spaces.Zop^[j]) psi4 z * Work.Spaces.w z) ^ 2
          ≤ K ^ 2 * (4 / (1 + z) ^ 2) := by
        have hw0 : 0 ≤ Work.Spaces.w z := by
          rw [Work.Spaces.w]
          exact div_nonneg (by positivity) (by positivity)
        have hle : |(Work.Spaces.Zop^[j]) psi4 z * Work.Spaces.w z|
            ≤ K / z * Work.Spaces.w z := by
          rw [abs_mul, abs_of_nonneg hw0]
          exact mul_le_mul_of_nonneg_right (hKb j hj4 z hz4) hw0
        have hsq := pow_le_pow_left₀ (abs_nonneg _) hle 2
        have hkey : (K / z * Work.Spaces.w z) ^ 2
            = K ^ 2 * ((Work.Spaces.w z) ^ 2 / z ^ 2) := by ring
        calc ((Work.Spaces.Zop^[j]) psi4 z * Work.Spaces.w z) ^ 2
            ≤ (K / z * Work.Spaces.w z) ^ 2 := by simpa only [sq_abs] using hsq
          _ = K ^ 2 * ((Work.Spaces.w z) ^ 2 / z ^ 2) := hkey
          _ ≤ K ^ 2 * (4 / (1 + z) ^ 2) := mul_le_mul_of_nonneg_left hwfact (sq_nonneg K)
      calc ((Work.Spaces.dthU^[i]) (angF β) θ) ^ 2
            * (((Work.Spaces.Zop^[j]) psi4 z * Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam β)))
          ≤ ((β / Work.Spaces.c β) ^ 2 * 100000 ^ 2 * (Work.Spaces.Gam β θ) ^ 2)
            * ((K ^ 2 * (4 / (1 + z) ^ 2))
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam β))) :=
            mul_le_mul hAle (mul_le_mul_of_nonneg_right hZs (by positivity))
              (by positivity) (by positivity)
        _ = ((β / Work.Spaces.c β) ^ 2 * 100000 ^ 2 * K ^ 2 * 4 / (1 + z) ^ 2)
            * (Work.Spaces.Gam β θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam β))) := by
            ring
        _ ≤ ((β / Work.Spaces.c β) ^ 2 * 100000 ^ 2 * K ^ 2 * 4 / (1 + z) ^ 2)
            * Work.FTS.LocData.angMaj β θ :=
            mul_le_mul_of_nonneg_left hang (div_nonneg (by positivity) hDpos.le)
        _ = 4 * (β / Work.Spaces.c β) ^ 2 * 100000 ^ 2 * K ^ 2
            * Work.FTS.LocData.angMaj β θ / (1 + z) ^ 2 := by ring
    · rw [if_neg hc]
      exact div_nonneg
        (mul_nonneg (by positivity :
          (0 : ℝ) ≤ 4 * (β / Work.Spaces.c β) ^ 2 * 100000 ^ 2 * K ^ 2) hang0) hDpos.le
  calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fcut β) z θ * Work.Spaces.Wt β z θ) ^ 2 else 0))
      ≤ ∑ _i ∈ Finset.range 5, ∑ _j ∈ Finset.range 5,
          (4 * (β / Work.Spaces.c β) ^ 2 * 100000 ^ 2 * K ^ 2
            * Work.FTS.LocData.angMaj β θ / (1 + z) ^ 2) :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hper i hi j hj))
    _ = 25 * (4 * (β / Work.Spaces.c β) ^ 2 * 100000 ^ 2 * K ^ 2
          * Work.FTS.LocData.angMaj β θ / (1 + z) ^ 2) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-! ## 8. Assembly -/

/-- The numerical assembly of the two sum bounds. -/
theorem zfar_const_arith {β K A D : ℝ}
    (hP : 0 ≤ (β / Work.Spaces.c β) ^ 2 * K ^ 2) (hA : 0 ≤ A) (hD : 0 < D) :
    5 * (4 * (β / Work.Spaces.c β) ^ 2 * K ^ 2 * A / D)
      + 25 * (4 * (β / Work.Spaces.c β) ^ 2 * 100000 ^ 2 * K ^ 2 * A / D)
      ≤ ((10 : ℝ) ^ 15 * (β / Work.Spaces.c β) ^ 2 * K ^ 2 + 1) * A / D := by
  have hq : 0 ≤ (β / Work.Spaces.c β) ^ 2 * K ^ 2 * A / D :=
    div_nonneg (mul_nonneg hP hA) hD.le
  rw [show 5 * (4 * (β / Work.Spaces.c β) ^ 2 * K ^ 2 * A / D)
        + 25 * (4 * (β / Work.Spaces.c β) ^ 2 * 100000 ^ 2 * K ^ 2 * A / D)
      = (20 + 100 * 100000 ^ 2) * ((β / Work.Spaces.c β) ^ 2 * K ^ 2 * A / D) by ring]
  rw [show ((10 : ℝ) ^ 15 * (β / Work.Spaces.c β) ^ 2 * K ^ 2 + 1) * A / D
      = (10 : ℝ) ^ 15 * ((β / Work.Spaces.c β) ^ 2 * K ^ 2 * A / D) + A / D by ring]
  have hnum : (20 : ℝ) + 100 * 100000 ^ 2 ≤ (10 : ℝ) ^ 15 := by norm_num
  have h1 : (20 + 100 * 100000 ^ 2) * ((β / Work.Spaces.c β) ^ 2 * K ^ 2 * A / D)
      ≤ (10 : ℝ) ^ 15 * ((β / Work.Spaces.c β) ^ 2 * K ^ 2 * A / D) :=
    mul_le_mul_of_nonneg_right hnum hq
  have h2 : 0 ≤ A / D := div_nonneg hA hD.le
  linarith

/-- **The far-field `ℋ⁴`-bound** for the profile cut off at scale `4`, `0 < β ≤ 1`. -/
theorem hkIntegrand_far_bound (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 4 ≤ z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand β 4 (fcut β) z θ
        ≤ C * Work.FTS.LocData.angMaj β θ / (1 + z) ^ 2 := by
  obtain ⟨K, hK0, hKb⟩ := exists_Zop_iter_psi4_bound
  refine ⟨(10 : ℝ) ^ 15 * (β / Work.Spaces.c β) ^ 2 * K ^ 2 + 1, ?_, ?_⟩
  · have h : 0 ≤ (10 : ℝ) ^ 15 * (β / Work.Spaces.c β) ^ 2 * K ^ 2 := by positivity
    linarith
  · intro z hz4 θ hθ
    have h1 := hkIntegrand_zfar_T1 hβ hKb hz4 hθ
    have h2 := hkIntegrand_zfar_T2 hβ hβ1 hKb hz4 hθ
    have hang0 : 0 ≤ Work.FTS.LocData.angMaj β θ := Work.FTS.LocData.angMaj_nonneg hθ
    simp only [Work.Spaces.HkIntegrand]
    refine le_trans (add_le_add h1 h2) ?_
    exact zfar_const_arith (by positivity) hang0 (by positivity)

/-! ## 9. The requested lemma -/

theorem hkIntegrandZfarBound {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 4 ≤ z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand (3 * α) 4
        (fun z θ => -Work.Construction.Fstar (3 * α) z θ * (1 - Work.Stability.chi (z / 4))) z θ
        ≤ C * Work.FTS.LocData.angMaj (3 * α) θ / (1 + z) ^ 2 := by
  obtain ⟨C, hC0, hCb⟩ := hkIntegrand_far_bound (3 * α) (by linarith) (by linarith)
  exact ⟨C, hC0, fun z hz θ hθ => hCb z hz θ hθ⟩

end Work.FTS.Regularity
