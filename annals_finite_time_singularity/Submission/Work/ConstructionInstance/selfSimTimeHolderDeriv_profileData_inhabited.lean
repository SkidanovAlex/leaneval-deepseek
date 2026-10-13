/-
# `SelfSimTimeHolderDeriv` for the inhabited `ProfileData` (the residual `hThDt`)

`Work.ConstructionInstance.SelfSimTimeHolderDeriv P` is the residual time-Hölder regularity of
`∂ₜω` of `NOTES.md` §3.5.  `selfSimTimeHolderDeriv_of_secondOrderData` reduces it to *second order*
data of the ansatz: the profile twice differentiable in `z` with a weighted box on `z²∂_z²F`, and
the modulation twice differentiable with a bound on `λ̄''`.

The inhabitant of `ProfileData` produced by `profileData_inhabited` has the **zero perturbation**
`g = 0`, `T = 2` and the affine modulation `λ̄(t) = 1 - t/2`.  For this datum the profile is, on
each angular branch, a *constant multiple* of the fundamental-model profile
`Work.FM.Fstar z = 2z/(1+z)²` (`Work.Construction.Fstar p z θ = p(Γ(θ)/c(p))·F_*(z)` together with
the odd extension in `θ`), so its second `z`-derivative is a constant multiple of

  `∂_z² F_*(z) = 4(z-2)/(1+z)⁴`,

and the weighted box `|z²∂_z²F| ≤ 80` is a two-line calculus estimate (`|z²(z-2)| ≤ 2(1+z)⁴` for
`z ≥ 0`, and `|Γ(θ)/c(p)| ≤ 10` on `Iθ`).  The modulation `1 - t/2` is affine, so `deriv λ̄` is the
constant `-1/2` and `deriv (deriv λ̄) = 0`.

## Contents

* `deriv_deriv_FM_Fstar`, `hasDerivAt_deriv_FM_Fstar`: the second derivative of `Work.FM.Fstar`.
* `pz_pz_profile_zeroPert`, `hasDerivAt_pz_profile_zeroPert`: the corresponding statements for the
  profile with zero perturbation.
* `zsq_pz_pz_profile_zeroPert_abs_le`: the weighted second-derivative box with constant `80`.
* `selfSimTimeHolderDeriv_profileData_inhabited`: the requested theorem, assembled through
  `selfSimTimeHolderDeriv_of_secondOrderData`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.ConstructionInstance.selfSimTimeHolderDeriv_of_secondOrderData
import Submission.Work.ConstructionInstance.profileData_inhabited
import Submission.Work.ConstructionInstance.Tie
import Submission.Work.ConstructionInstance.ConcreteData
import Submission.Work.FM.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter
open scoped Topology

namespace Work.ConstructionInstance

/-! ## The second `z`-derivative of the fundamental-model profile `F_*` -/

/-- `z ↦ 2(1-z)/(1+z)³`, the value of `deriv F_*` away from `z = -1`. -/
def FstarSlope (z : ℝ) : ℝ := 2 * (1 - z) / (1 + z) ^ 3

/-- `FstarSlope` is differentiable with derivative `4(z-2)/(1+z)⁴`. -/
theorem hasDerivAt_FstarSlope (z : ℝ) (hz : -1 < z) :
    HasDerivAt FstarSlope (4 * (z - 2) / (1 + z) ^ 4) z := by
  have hne : (1 + z) ^ 3 ≠ 0 := by
    have : (0 : ℝ) < 1 + z := by linarith
    positivity
  have hnum : HasDerivAt (fun z' : ℝ => 2 * (1 - z')) (-2) z := by
    have h : HasDerivAt (fun z' : ℝ => 1 - z') (-1) z := by
      simpa using (hasDerivAt_id z).const_sub 1
    simpa using h.const_mul 2
  have hden : HasDerivAt (fun z' : ℝ => (1 + z') ^ 3) (3 * (1 + z) ^ 2) z := by
    have h : HasDerivAt (fun z' : ℝ => 1 + z') 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    convert h.pow 3 using 1
    ring_nf
  have h := hnum.div hden hne
  unfold FstarSlope
  convert h using 1
  field_simp
  ring

/-- `deriv F_*` agrees with `FstarSlope` near any point of `(-1,∞)`. -/
theorem eventuallyEq_deriv_FM_Fstar (z : ℝ) (hz : -1 < z) :
    deriv Work.FM.Fstar =ᶠ[𝓝 z] FstarSlope := by
  refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) ?_
  intro z' hz'
  rw [FstarSlope, Work.FM.deriv_Fstar z' hz']

/-- `deriv F_*` is differentiable away from `z = -1`. -/
theorem hasDerivAt_deriv_FM_Fstar (z : ℝ) (hz : -1 < z) :
    HasDerivAt (deriv Work.FM.Fstar) (4 * (z - 2) / (1 + z) ^ 4) z :=
  (hasDerivAt_FstarSlope z hz).congr_of_eventuallyEq (eventuallyEq_deriv_FM_Fstar z hz)

/-- **The second derivative of the fundamental-model profile**: `∂_z²F_*(z) = 4(z-2)/(1+z)⁴`. -/
theorem deriv_deriv_FM_Fstar (z : ℝ) (hz : -1 < z) :
    deriv (deriv Work.FM.Fstar) z = 4 * (z - 2) / (1 + z) ^ 4 :=
  (hasDerivAt_deriv_FM_Fstar z hz).deriv

/-! ## The profile with the zero perturbation -/

/-- The angular coefficient of the profile with zero perturbation: on `θ ≥ 0` it is
`p·Γ(θ)/c(p)`, and `θ ↦ -θ` on the odd branch. -/
def thetaCoeff (p θ : ℝ) : ℝ :=
  if 0 ≤ θ then p * (Work.Spaces.Gam p θ / Work.Spaces.c p)
  else -(p * (Work.Spaces.Gam p (-θ) / Work.Spaces.c p))

/-- With the zero perturbation, the profile is the angular coefficient times `F_*`. -/
theorem profile_zeroPert_eq (p θ z : ℝ) :
    profile p (fun _ _ => (0 : ℝ)) z θ = thetaCoeff p θ * Work.FM.Fstar z := by
  rw [thetaCoeff]
  rcases le_or_gt 0 θ with h | h
  · rw [profile_of_nonneg h, ite_eq_left h, Work.Construction.Fstar]; ring
  · rw [profile_of_neg (not_le.mpr h), ite_eq_right (not_le.mpr h), Work.Construction.Fstar]; ring

/-- The `z`-derivative of the profile with zero perturbation. -/
theorem pz_profile_zeroPert (p θ z : ℝ) :
    Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ))) z θ
      = thetaCoeff p θ * deriv Work.FM.Fstar z := by
  rw [Work.Spaces.pz]
  have hfun : (fun z' => profile p (fun _ _ => (0 : ℝ)) z' θ)
      = fun z' => thetaCoeff p θ * Work.FM.Fstar z' :=
    funext (fun z' => profile_zeroPert_eq p θ z')
  rw [hfun, deriv_const_mul_field]

/-- The second `z`-derivative of the profile with zero perturbation. -/
theorem pz_pz_profile_zeroPert (p θ z : ℝ) :
    Work.Spaces.pz (Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ)))) z θ
      = thetaCoeff p θ * deriv (deriv Work.FM.Fstar) z := by
  rw [Work.Spaces.pz]
  have hfun : (fun z' => Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ))) z' θ)
      = fun z' => thetaCoeff p θ * deriv Work.FM.Fstar z' :=
    funext (fun z' => pz_profile_zeroPert p θ z')
  rw [hfun, deriv_const_mul_field]

/-- **The profile with zero perturbation is twice differentiable in `z`** with the second
`z`-derivative given by `pz (pz F)`. -/
theorem hasDerivAt_pz_profile_zeroPert {p θ z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ))) z' θ)
      (Work.Spaces.pz (Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ)))) z θ) z := by
  have hz1 : -1 < z := by linarith
  have hfun : (fun z' => Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ))) z' θ)
      = fun z' => thetaCoeff p θ * deriv Work.FM.Fstar z' :=
    funext (fun z' => pz_profile_zeroPert p θ z')
  have h1 : HasDerivAt (fun z' => thetaCoeff p θ * deriv Work.FM.Fstar z')
      (thetaCoeff p θ * (4 * (z - 2) / (1 + z) ^ 4)) z :=
    (hasDerivAt_deriv_FM_Fstar z hz1).const_mul (thetaCoeff p θ)
  rw [hfun, pz_pz_profile_zeroPert p θ z, deriv_deriv_FM_Fstar z hz1]
  exact h1

/-- **The weighted second-derivative box of the profile with zero perturbation**:
`|z²·∂_z²F| ≤ 80` on the quadrant, for `0 < p ≤ 1`. -/
theorem zsq_pz_pz_profile_zeroPert_abs_le {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |z ^ 2 * Work.Spaces.pz (Work.Spaces.pz (profile p (fun _ _ => (0 : ℝ)))) z θ| ≤ 80 := by
  intro z θ hz hθ
  rw [pz_pz_profile_zeroPert]
  have hz1 : -1 < z := by linarith
  rw [deriv_deriv_FM_Fstar z hz1]
  have hθnn : 0 ≤ θ := hθ.1
  have hk_eq : thetaCoeff p θ = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) := by
    rw [thetaCoeff, ite_eq_left hθnn]
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hGb := Work.Spaces.Gam_bounds p θ hp hθ
  have hkbound : |thetaCoeff p θ| ≤ 10 := by
    rw [hk_eq, abs_of_nonneg (mul_nonneg hp.le (div_nonneg hGb.1 hcpos.le))]
    have h1 : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
      rw [div_le_iff₀ hcpos]; nlinarith [hGb.2]
    nlinarith [hp1, hGb.1, hcpos]
  have hkey : z ^ 2 * |z - 2| ≤ 2 * (1 + z) ^ 4 := by
    have h1 : |z - 2| ≤ z + 2 := by
      rw [abs_le]; constructor <;> linarith
    calc z ^ 2 * |z - 2| ≤ z ^ 2 * (z + 2) := mul_le_mul_of_nonneg_left h1 (sq_nonneg z)
      _ ≤ 2 * (1 + z) ^ 4 := by nlinarith [sq_nonneg z, sq_nonneg (z ^ 2)]
  have h2 : |z ^ 2 * (4 * (z - 2) / (1 + z) ^ 4)| ≤ 8 := by
    have hpos : (0 : ℝ) < (1 + z) ^ 4 := by positivity
    rw [abs_mul, abs_of_nonneg (sq_nonneg z), abs_div, abs_of_pos hpos,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hreq : z ^ 2 * (4 * |z - 2| / (1 + z) ^ 4)
        = 4 * (z ^ 2 * |z - 2|) / (1 + z) ^ 4 := by ring
    rw [hreq, div_le_iff₀ hpos]
    nlinarith [hkey]
  calc |z ^ 2 * (thetaCoeff p θ * (4 * (z - 2) / (1 + z) ^ 4))|
      = |thetaCoeff p θ| * |z ^ 2 * (4 * (z - 2) / (1 + z) ^ 4)| := by
        rw [show z ^ 2 * (thetaCoeff p θ * (4 * (z - 2) / (1 + z) ^ 4))
              = thetaCoeff p θ * (z ^ 2 * (4 * (z - 2) / (1 + z) ^ 4)) by ring, abs_mul]
    _ ≤ 10 * 8 := by apply mul_le_mul hkbound h2 (abs_nonneg _) (by norm_num)
    _ = 80 := by norm_num

/-! ## The requested theorem -/

theorem selfSimTimeHolderDeriv_profileData_inhabited {α : NNReal} (hα : 0 < (α : ℝ))
    (hα13 : (α : ℝ) ≤ 1 / 3) :
    ∃ P : Work.ConstructionInstance.ProfileData α, P.T = 2 ∧
      Work.ConstructionInstance.SelfSimTimeHolderDeriv P := by
  obtain ⟨P, hg, hT, _hM, _hM1, _hK, _hCg, _hCg', _hL, hlamfun⟩ := profileData_inhabited hα hα13
  refine ⟨P, hT, ?_⟩
  have hp : 0 < profExp α := profExp_pos hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith
  refine selfSimTimeHolderDeriv_of_secondOrderData P ?_ (Cg'' := 80) (K₂ := 0) ?_ ?_ ?_
  · intro z θ hz
    rw [hg]
    exact hasDerivAt_pz_profile_zeroPert (p := profExp α) hz
  · intro z θ hz hθ
    rw [hg]
    exact zsq_pz_pz_profile_zeroPert_abs_le hp hp1 z θ hz hθ
  · intro t _ht
    have hlam_eq : P.lam = fun t : ℝ => 1 - t / 2 := funext hlamfun
    have hderiv : deriv P.lam = fun _ => -(1 / 2) := by
      rw [hlam_eq]
      funext t
      exact hderivval t
    rw [hderiv, deriv_const]
    exact hasDerivAt_const t (-(1 / 2))
  · intro t _ht
    have hlam_eq : P.lam = fun t : ℝ => 1 - t / 2 := funext hlamfun
    have hderiv : deriv P.lam = fun _ => -(1 / 2) := by
      rw [hlam_eq]
      funext t
      exact hderivval t
    rw [hderiv, deriv_const]
    norm_num

end Work.ConstructionInstance
