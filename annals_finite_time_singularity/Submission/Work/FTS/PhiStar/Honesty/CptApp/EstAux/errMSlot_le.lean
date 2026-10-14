import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.SmoothErr
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.StrongEps.LocUnif.D5.deriv_slot_lintegral_bounds
import Submission.Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.dthU_Gam
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.MixedSlotAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
/-! ## Elementary identities for the weights

`Wt α z θ = w z · sin(2θ)^{-γ/2}` with `γ = gam α`, so its square is
`w z ^ 2 · sin(2θ)^{-γ}`, the weight occurring in the second group of `Good`. -/

theorem ems_sq_rpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : (x ^ y) ^ 2 = x ^ (2 * y) := by
  rw [← Real.rpow_natCast (x := x ^ y) (n := 2)]
  rw [show ((2 : ℕ) : ℝ) = 2 from by norm_num]
  rw [← Real.rpow_mul hx]
  ring

theorem ems_Wt_sq {α z θ : ℝ} (hθ : 0 ≤ Real.sin (2 * θ)) :
    Work.Spaces.Wt α z θ ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, ems_sq_rpow hθ]
  congr 1
  ring

/-- The weight `w` vanishes at `z = 0`. -/
theorem ems_w_zero : Work.Spaces.w 0 = 0 := by
  rw [Work.Spaces.w]; norm_num

/-- `wTheta` vanishes where `sin(2θ) = 0` (`gam α ≠ 0`). -/
theorem ems_wTheta_zero_of_sin_eq_zero {α θ : ℝ} (hα : Work.Spaces.gam α ≠ 0)
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.wTheta α θ = 0 := by
  rw [Work.Spaces.wTheta, hs,
    Real.zero_rpow (neg_ne_zero.mpr (div_ne_zero hα (by norm_num)))]

/-! ## `omegaInd · HkIntegrand = omegaPart`, and the `Good`-majorants -/

theorem ems_omegaInd_mul_HkIntegrand (α : ℝ) (k n : ℕ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    omegaInd n z θ * Work.Spaces.HkIntegrand α k F z θ = omegaPart α k n F z θ := by
  rw [omegaInd, omegaPart]
  split_ifs with h <;> ring

theorem ems_omegaPart_le_Good (α : ℝ) (k n : ℕ) (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : omegaPart α k n F z θ ≤ Good α k n F z θ := by
  rw [Good]
  have h2 : 0 ≤ thShrink n θ
        * (∑ s ∈ Finset.range k, (Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    mul_nonneg (thShrink_nonneg n θ) (hkZsum_nonneg α k F z hθ)
  have h3 : 0 ≤ (∑ m ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
      * ((Work.Spaces.w z) ^ 2 * rhoProf α k θ) :=
    mul_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (rhoProf_nonneg α k hθ))
  exact le_trans (le_add_of_nonneg_right h2) (le_add_of_nonneg_right h3)

theorem ems_thShrink_sum_le_Good (α : ℝ) (k n : ℕ) (F : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    thShrink n θ
        * (∑ s ∈ Finset.range k, (Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ Good α k n F z θ := by
  rw [Good]
  have h1 : 0 ≤ omegaPart α k n F z θ := omegaPart_nonneg α k n F z θ
  have h3 : 0 ≤ (∑ m ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter m (fun z' _ : ℝ => mu n F z') z 0) ^ 2)
      * ((Work.Spaces.w z) ^ 2 * rhoProf α k θ) :=
    mul_nonneg (Finset.sum_nonneg fun m _ => sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (rhoProf_nonneg α k hθ))
  exact le_trans (le_add_of_nonneg_left h1) (le_add_of_nonneg_right h3)

/-- A single `z`-slot of the second group of `Good`, multiplied by `thShrink`. -/
theorem ems_zslot_le_thShrinkSum {α : ℝ} {k n s : ℕ} {F : ℝ → ℝ → ℝ} (hs : s < k)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    thShrink n θ * ((Work.Spaces.DzIter s F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ thShrink n θ * (∑ s' ∈ Finset.range k, (Work.Spaces.DzIter s' F z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  refine mul_le_mul_of_nonneg_left ?_ (thShrink_nonneg n θ)
  exact Finset.single_le_sum
    (f := fun s' => (Work.Spaces.DzIter s' F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
    (fun s' _ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _))
    (Finset.mem_range.mpr hs)

end Work.FTS.PhiStar.Honesty.CptApp.Est
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.errASlot_expand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The binomial expansion of the `z`-derivative of the `(χζ − 1)`-slot

`D_z = z ∂_z` is a derivation, hence its iterates satisfy the binomial (Leibniz) rule

`D_z^i (f · g) = ∑_{b ≤ i} C(i,b) · (D_z^b f · D_z^{i-b} g)`

as soon as both factors are `C^∞` on the open quadrant `(0,∞) × (0,π/2)`.  This file applies
the rule to the slot function `f = (χ_n(z) ζ_n(θ) − 1)` and to the datum `g = F`, which is
the binomial expansion consumed downstream by `errASlot_le` (`EstAux/errASlot_le.lean`).

The Leibniz rule itself is `Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz`, i.e. the version
stated in the open-quadrant class `Work.FTS.EllipticEst.SmoothOpen` (the class in which the
statement's hypothesis on `F` lives — the `C^∞`-order variant
`Work.FTS.LocData.DzIter_mul_smoothQuad` asks for smoothness on the *larger* set `(-1,∞)`,
which `SmoothOpen` does not provide).  Here the factor `χ_n(z) ζ_n(θ) − 1` is `C^∞` on the
whole plane (`Work.FTS.PhiStar.Honesty.CptApp.contDiff_chiR`, `…contDiff_zetaR`), and `F` is
`SmoothOpen` by hypothesis.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

theorem errASlot_expand {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (n i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter i (fun z θ => (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) z θ
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (Work.Spaces.DzIter b (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
            * Work.Spaces.DzIter (i - b) F z θ) := by
  have hG : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) := by
    refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun m => ?_
    exact ((Work.FTS.PhiStar.Honesty.CptApp.contDiff_chiR n m).contDiffOn.comp
        contDiffOn_fst (fun p _ => Set.mem_univ p.1)).mul
        ((Work.FTS.PhiStar.Honesty.CptApp.contDiff_zetaR n m).contDiffOn.comp contDiffOn_snd
          (fun p _ => Set.mem_univ p.2)) |>.sub contDiffOn_const
  exact Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i _ F hG hsm z θ hz hθ.1 hθ.2

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.errMSlot_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The moment slot of the approximation error

The error `err n F = approx n F - F` splits into three groups of terms
(see `CptApp/EstDefs.lean`): the `(χζ − 1)`-group, the localised-Hardy group, and the
moment correction `- chiR n z * lam n F z * rho θ = - mu n F z * rho θ`.

This file proves the pointwise bound for the moment group: for every `k` there is a
universal constant `C` with

  `(D_z^i (mu n F · rho) · w / sin(2θ)^{η/2})² ≤ C · Good α k n F z θ`

for all `i ≤ k`, `z ∈ Iz`, `θ ∈ Iθ`.

Mathematically the bound is the obvious one: `rho` does not depend on `z`, so the whole
`z`-derivative falls on `mu n F`; and the angular profile `rhoProf α k θ` of the third
group of `Good` contains, as its `i = 0` term, the quantity `(rho θ)² · sin(2θ)^{-η}`
which dominates the angular factor `rho θ² sin(2θ)^{-η}` coming from the weight
`w/sin(2θ)^{η/2}` squared.  Consequently the whole slot is absorbed by the third group of
`Good` alone, with the constant `1` (only the elementary nonnegativity of the first two
groups of `Good` is used).

The three ingredients are the lemmas

* `DzIter_mul_rho_eq` — the `z`-derivative of `mu n F · rho` is `rho` times the
  `z`-derivative of `mu n F` (evaluated at `θ = 0`, the `θ`-independence of `mu n F`);
* `sq_div_sin` — `(w / sin(2θ)^{η/2})² = w² · sin(2θ)^{-η}`;
* `rhoProf_ge` — `(rho θ)² · sin(2θ)^{-η} ≤ rhoProf α k θ`.
-/

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

/-! ## The three ingredients -/

/-- `D_z^i (mu n F · rho)` with a `θ`-only right factor: the derivative falls entirely on
the `z`-dependent factor, and the factor `D_z^i mu n F` is independent of `θ`, hence may be
evaluated at `θ = 0` (the form in which `Good` presents it). -/
theorem DzIter_mul_rho_eq (g : ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z θ => g z * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ
      = Work.Spaces.DzIter i (fun z' _ : ℝ => g z') z 0
        * Work.FTS.PhiStar.Honesty.CptApp.rho θ := by
  induction i generalizing z θ with
  | zero => rfl
  | succ i ih =>
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    have hfun : (fun z' => Work.Spaces.DzIter i (fun z θ => g z * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z' θ)
        = (fun z' => Work.Spaces.DzIter i (fun z' _ : ℝ => g z') z' 0
            * Work.FTS.PhiStar.Honesty.CptApp.rho θ) :=
      funext (fun z' => ih z' θ)
    rw [hfun, deriv_mul_const_field]
    ring

/-- The square of the radial/angular weight `w / sin(2θ)^{η/2}`. -/
theorem sq_div_sin (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.PhiStar.Honesty.CptApp.sin_two_nonneg_of_mem_Iθ hθ
  have hb : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = Real.sin (2 * θ) ^ Work.Spaces.eta := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    congr 1
    ring
  rw [div_pow, hb, div_eq_mul_inv, Real.rpow_neg hs]

/-- The angular factor of the moment slot is dominated by the angular profile `rhoProf`:
its `i = 0` term alone is `(rho θ)² · (sin(2θ)^{-γ} + sin(2θ)^{-η})`. -/
theorem rhoProf_ge (α : ℝ) (k : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.PhiStar.Honesty.CptApp.rho θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.PhiStar.Honesty.CptApp.sin_two_nonneg_of_mem_Iθ hθ
  rw [Work.FTS.PhiStar.Honesty.CptApp.rhoProf]
  have hmem : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.succ_pos k)
  have hnn : ∀ i ∈ Finset.range (k + 1),
      0 ≤ (Work.Spaces.DthIter i (fun _ θ' : ℝ => Work.FTS.PhiStar.Honesty.CptApp.rho θ') 0 θ) ^ 2
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) + (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
    fun i _ => mul_nonneg (sq_nonneg _) (add_nonneg (Real.rpow_nonneg hs _) (Real.rpow_nonneg hs _))
  have hsingle := Finset.single_le_sum hnn hmem
  simp only [Work.Spaces.DthIter_zero] at hsingle
  refine le_trans ?_ hsingle
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact le_add_of_nonneg_left (Real.rpow_nonneg hs _)

/-! ## The slot bound -/

theorem errMSlot_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
      Work.FTS.EllipticEst.SmoothOpen F →
      ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        (Work.Spaces.DzIter i (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
            * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  refine ⟨1, one_pos, ?_⟩
  intro α n F hα0 hα1 hn hsm i hi z hz θ hθ
  have hA := DzIter_mul_rho_eq (fun z => Work.FTS.PhiStar.Honesty.CptApp.mu n F z) i z θ
  have hB := sq_div_sin z hθ
  have hC := rhoProf_ge α k hθ
  have hWnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hSn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Real.rpow_nonneg (Work.FTS.PhiStar.Honesty.CptApp.sin_two_nonneg_of_mem_Iθ hθ) _
  set T : ℝ := ∑ m ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
    with hT
  have hD : (Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
      ≤ T := by
    rw [hT]
    exact Finset.single_le_sum
      (f := fun m => (Work.Spaces.DzIter m (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2)
      (fun m _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hTnn : 0 ≤ T := by
    rw [hT]; exact Finset.sum_nonneg (fun m _ => sq_nonneg _)
  have hstep : (Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
        * (Work.FTS.PhiStar.Honesty.CptApp.rho θ) ^ 2
        * (((Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ T * (((Work.Spaces.w z) ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ) := by
    have h1 : (Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
          * (Work.Spaces.w z) ^ 2 ≤ T * (Work.Spaces.w z) ^ 2 :=
      mul_le_mul_of_nonneg_right hD hWnn
    have h3 : 0 ≤ (Work.FTS.PhiStar.Honesty.CptApp.rho θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := mul_nonneg (sq_nonneg _) hSn
    have h4 : 0 ≤ T * (Work.Spaces.w z) ^ 2 := mul_nonneg hTnn hWnn
    calc (Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
          * (Work.FTS.PhiStar.Honesty.CptApp.rho θ) ^ 2
          * (((Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = ((Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
            * (Work.Spaces.w z) ^ 2)
          * ((Work.FTS.PhiStar.Honesty.CptApp.rho θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      _ ≤ (T * (Work.Spaces.w z) ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ :=
          mul_le_mul h1 hC h3 h4
      _ = T * (((Work.Spaces.w z) ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ) := by ring
  have hGood : T * (((Work.Spaces.w z) ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ)
      ≤ Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
    rw [hT, Work.FTS.PhiStar.Honesty.CptApp.Good]
    exact le_add_of_nonneg_left (add_nonneg
      (Work.FTS.PhiStar.Honesty.CptApp.omegaPart_nonneg α k n F z θ)
      (mul_nonneg (Work.FTS.PhiStar.Honesty.CptApp.thShrink_nonneg n θ)
        (Work.FTS.PhiStar.Honesty.CptApp.hkZsum_nonneg α k F z hθ)))
  calc (Work.Spaces.DzIter i (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z
          * Work.FTS.PhiStar.Honesty.CptApp.rho θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = ((Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0
            * Work.FTS.PhiStar.Honesty.CptApp.rho θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by rw [hA]
    _ = (Work.Spaces.DzIter i (fun z' _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.mu n F z') z 0) ^ 2
          * (Work.FTS.PhiStar.Honesty.CptApp.rho θ) ^ 2
          * (((Work.Spaces.w z) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
        rw [mul_pow, mul_pow, hB]
    _ ≤ T * (((Work.Spaces.w z) ^ 2) * Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ) := hstep
    _ ≤ Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := hGood
    _ = 1 * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by ring

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
end
