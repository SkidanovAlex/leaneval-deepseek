/-
# Row 19: the pointwise weighted bounds for the profile `D_zF_*` and its `D_θ`-iterates

`Work.FTS.Nonlinear.Pieces.RNP.Gs α = D_z F_*` is the radial profile of the row-19 piece
`N₃^{**} = -2α·V(Φ̃_*)·D_zF_*` (`Work.FTS.Nonlin.N3ss`).  This file proves the two pointwise
bounds used by the `ℋ⁴`-estimate of the row:

  `|D_z^m (D_zF_*)| ≤ C α · z/(1+z)²`,   `|D_z^m (D_θ^i D_zF_*)| ≤ C α · |D_θ^i Γ| · z/(1+z)²`

on the domain `Iz × Iθ` (`z ≥ 0`, `0 ≤ θ ≤ π/2`), `m ≤ 4`, `1 ≤ i ≤ 4`, with a universal
(α-independent) constant `C`.

## The route

Everything is driven by the *separated* form of the profile: for `z > -1` and every `θ`

  `D_zF_*(z,θ) = α·(Γ(θ)/c(α))·H(z)`,   `H = Hz = 2z(1-z)/(1+z)³`

(`Work.Construction.Dz_Fstar_eq`, `Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz`), an angular
factor times a radial factor.  Consequently

* `D_θ` only hits the angular factor (`Work.Spaces.DthIter_decomp`, redone by induction here
  against the concrete profile so that the `θ`-congruence of the slices is not needed), giving
  `D_θ^i (D_zF_*) = (α/c)·D_θ^i Γ·H` on `(0,π/2)`, and
* the Stirling expansion `D_z^m = ∑_{k≤m} S(m,k) z^k ∂_z^k`
  (`Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth`) plus the unconditional constant rule for the
  iterated derivative (`iteratedDeriv_const_mul`) pull the angular factor out of the radial
  operator.

At the two boundary angles `θ = 0, π/2` both sides of the second bound vanish (`D_θ` carries a
factor `sin 2θ`), so the angular factorisation is only needed on the *open* interval.

The single analytic input is the weighted bound for the radial factor
`|D_z^m (fun z _ => H z) z θ| ≤ C_H · z/(1+z)²` for `m ≤ 4`, proved in
`Submission/Work/FTS/Nonlinear/Pieces/RNP/row19/abs_DzIter_Hz_le.lean` from the closed form of
the iterated derivatives of `H`.

The constant `10` in front of `α` comes from `c(α) ≥ 1/10` (`Work.Spaces.c_bounds`) and
`0 ≤ Γ ≤ 1` (`Work.Spaces.Gam_bounds`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19aux
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.DzHzDefs
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.abs_DzIter_Hz_le
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Row19GsAux

open Work.FTS.Nonlinear.Pieces.RNP (Gs)

/-! ## Plumbing: `pzIter` as an iterated derivative, congruence, and the constant rule -/

/-- The iterated plain `z`-derivative is the `k`-fold derivative of the `θ`-slice. -/
theorem pzIter_eq_iter_deriv_aux (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter k f z θ = deriv^[k] (fun t => f t θ) z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pz]
    rw [show (fun z' : ℝ => Work.Spaces.pzIter k f z' θ) = deriv^[k] (fun t => f t θ) from
      funext (fun z' => ih z')]
    exact congrFun (Function.iterate_succ_apply' deriv k (fun t => f t θ)).symm z

/-- Iterated `deriv` respects eventual equality. -/
theorem iterDeriv_eventuallyEq {f g : ℝ → ℝ} {z : ℝ} (h : f =ᶠ[𝓝 z] g) (k : ℕ) :
    deriv^[k] f =ᶠ[𝓝 z] deriv^[k] g := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have h1 : deriv^[k + 1] f = deriv (deriv^[k] f) := by
      funext x; rw [Function.iterate_succ_apply']
    have h2 : deriv^[k + 1] g = deriv (deriv^[k] g) := by
      funext x; rw [Function.iterate_succ_apply']
    rw [h1, h2]
    exact ih.deriv

/-- Iterated `deriv` is a local operation. -/
theorem iterDeriv_congr_of_eventuallyEq {f g : ℝ → ℝ} {z : ℝ}
    (h : f =ᶠ[𝓝 z] g) (k : ℕ) : deriv^[k] f z = deriv^[k] g z :=
  (iterDeriv_eventuallyEq h k).eq_of_nhds

/-- The constant rule for the iterated derivative. -/
theorem iterDeriv_const_mul {c z : ℝ} (k : ℕ) (f : ℝ → ℝ)
    (hf : ContDiffAt ℝ ((k : ℕ∞) : WithTop ℕ∞) f z) :
    deriv^[k] (fun t => c * f t) z = c * deriv^[k] f z := by
  rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate]
  exact iteratedDeriv_const_mul c hf

/-- `Hz` is `C^k` near every `z > -1`, for every finite `k`. -/
theorem contDiffAt_Hz_finite (k : ℕ) {z : ℝ} (hz : -1 < z) :
    ContDiffAt ℝ ((k : ℕ∞) : WithTop ℕ∞) Work.FTS.Nonlinear.FstarPkg.Hz z :=
by
  have hle : ((k : ℕ∞) : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    rw [show Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞) from rfl]
    exact WithTop.coe_le_coe.mpr le_top
  exact (contDiffOn_Hz.of_le (m := ((k : ℕ∞) : WithTop ℕ∞)) hle).contDiffAt
    (isOpen_Ioi.mem_nhds hz)

/-! ## The separated form of the profile -/

/-- For `z > -1` the profile `D_zF_*` is the product of the angular factor `α·Γ(θ)/c` and the
radial factor `Hz`. -/
theorem Gs_eq_factor {α : ℝ} (hα : 0 < α) {z θ : ℝ} (hz : -1 < z) :
    Gs α z θ = (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
      * Work.FTS.Nonlinear.FstarPkg.Hz z := by
  change Work.Spaces.Dz (Work.Construction.Fstar α) z θ = _
  rw [Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα hz]
  ring

/-- The `z`-slices of `Gs α` are `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_slice_Gs {α : ℝ} (hα : 0 < α) (θ : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => Gs α z θ) (Set.Ioi (-1)) :=
  ((contDiffOn_const (c := α * Work.Spaces.Gam α θ / Work.Spaces.c α)).mul
      contDiffOn_Hz).congr
    (fun t ht => Gs_eq_factor hα ht)

/-- The iterated plain `z`-derivative of `Gs α` factors as the angular factor times the
`k`-th derivative of `Hz`. -/
theorem pzIter_Gs_factor {α : ℝ} (hα : 0 < α) (k : ℕ) {z θ : ℝ} (hz : -1 < z) :
    Work.Spaces.pzIter k (Gs α) z θ
      = (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
        * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z := by
  have hF : (fun t : ℝ => Gs α t θ)
      =ᶠ[𝓝 z] (fun t : ℝ => (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
        * Work.FTS.Nonlinear.FstarPkg.Hz t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    exact Gs_eq_factor hα ht
  rw [pzIter_eq_iter_deriv_aux,
    iterDeriv_congr_of_eventuallyEq (f := fun t : ℝ => Gs α t θ)
      (g := fun t : ℝ => (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
        * Work.FTS.Nonlinear.FstarPkg.Hz t) hF k]
  exact iterDeriv_const_mul k Work.FTS.Nonlinear.FstarPkg.Hz (contDiffAt_Hz_finite k hz)

/-- **The `D_z`-factorisation of the profile.**  The angular factor is a constant for the
radial operator `D_z`. -/
theorem DzIter_Gs_factor {α : ℝ} (hα : 0 < α) (m : ℕ) {z θ : ℝ} (hz : -1 < z) :
    Work.Spaces.DzIter m (Gs α) z θ
      = (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
        * Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ := by
  rw [Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth (h := Gs α) (θ := θ)
    (contDiffOn_slice_Gs hα θ) m z hz]
  rw [DzIter_Hz_eq_sum m z θ hz, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pzIter_Gs_factor hα k hz]
  ring

/-! ## The angular factorisation of the `D_θ`-iterates -/

/-- `D_θ^i` vanishes on the profile whenever `sin 2θ = 0`, for `i ≥ 1`. -/
theorem DthIter_succ_eq_zero_of_sin {f : ℝ → ℝ → ℝ} {θ : ℝ} (h : Real.sin (2 * θ) = 0)
    (j : ℕ) (z : ℝ) : Work.Spaces.DthIter (j + 1) f z θ = 0 := by
  rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, h, zero_mul]

/-- A `D_z`-iterate of a function whose `θ`-slice is identically zero vanishes. -/
theorem DzIter_eq_zero_of_slice_zero {g : ℝ → ℝ → ℝ} {θ : ℝ} (h : ∀ z, g z θ = 0)
    (m : ℕ) (z : ℝ) : Work.Spaces.DzIter m g z θ = 0 := by
  induction m generalizing z with
  | zero => exact h z
  | succ m ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    have hfun : (fun z' : ℝ => Work.Spaces.DzIter m g z' θ) = fun _ : ℝ => (0 : ℝ) :=
      funext (fun z' => ih z')
    rw [hfun]; simp

/-- **The `D_θ`-factorisation of the profile.**  On the open angular interval the angular
operator only sees the angular factor `α·Γ(θ)/c`; the radial factor `Hz` is a constant for
`D_θ`. -/
theorem DthIter_Gs_factor {α : ℝ} (hα : 0 < α) (i : ℕ) {z θ : ℝ} (hz : -1 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.DthIter i (Gs α) z θ
      = (α / Work.Spaces.c α)
        * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
        * Work.FTS.Nonlinear.FstarPkg.Hz z := by
  have hmain : ∀ i : ℕ, ∀ z θ : ℝ, -1 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.DthIter i (Gs α) z θ
        = Work.Spaces.dthU^[i] (fun t => α * Work.Spaces.Gam α t / Work.Spaces.c α) θ
          * Work.FTS.Nonlinear.FstarPkg.Hz z := by
    intro i
    induction i with
    | zero =>
      intro z θ hz hθ
      rw [Work.Spaces.DthIter_zero, Function.iterate_zero, id_eq]
      exact Gs_eq_factor hα hz
    | succ i ih =>
      intro z θ hz hθ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      have hev : (fun θ' : ℝ => Work.Spaces.DthIter i (Gs α) z θ')
          =ᶠ[𝓝 θ] (fun θ' : ℝ =>
            Work.Spaces.dthU^[i] (fun t => α * Work.Spaces.Gam α t / Work.Spaces.c α) θ'
              * Work.FTS.Nonlinear.FstarPkg.Hz z) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'
      rw [Filter.EventuallyEq.deriv_eq hev,
        Work.Spaces.deriv_mul_const' (Work.FTS.Nonlinear.FstarPkg.Hz z) θ
          (Work.Spaces.dthU^[i] (fun t => α * Work.Spaces.Gam α t / Work.Spaces.c α))]
      have hd : Work.Spaces.dthU^[i + 1]
            (fun t => α * Work.Spaces.Gam α t / Work.Spaces.c α) θ
          = Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[i]
              (fun t => α * Work.Spaces.Gam α t / Work.Spaces.c α)) θ := by
        rw [Function.iterate_succ_apply', Work.Spaces.dthU_apply]
      rw [hd]
      ring
  rw [hmain i z θ hz hθ]
  rw [show (fun t : ℝ => α * Work.Spaces.Gam α t / Work.Spaces.c α)
      = (fun t : ℝ => (α / Work.Spaces.c α) * Work.Spaces.Gam α t) from by
    funext t; ring]
  rw [Work.Spaces.dthU_iter_const_mul,
    Work.FTS.LocData.DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ]

/-- The `z`-slices of the `D_θ`-iterates of the profile are `C^∞` on `(-1,∞)` (in the open
angular class). -/
theorem contDiffOn_slice_DthIter_Gs {α : ℝ} (hα : 0 < α) (i : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z => Work.Spaces.DthIter i (Gs α) z θ) (Set.Ioi (-1)) :=
  ((contDiffOn_const (c := (α / Work.Spaces.c α)
      * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)).mul
    contDiffOn_Hz).congr
    (fun t ht => DthIter_Gs_factor hα i ht hθ)

/-- **The `D_z`-factorisation of the angular iterates of the profile.** -/
theorem DzIter_DthIter_Gs_factor {α : ℝ} (hα : 0 < α) (i m : ℕ) {z θ : ℝ}
    (hz : -1 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.DzIter m (Work.Spaces.DthIter i (Gs α)) z θ
      = ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
        * Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ := by
  have hpk : ∀ k : ℕ, Work.Spaces.pzIter k (Work.Spaces.DthIter i (Gs α)) z θ
      = ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
        * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z := by
    intro k
    have hF : (fun t : ℝ => Work.Spaces.DthIter i (Gs α) t θ)
        =ᶠ[𝓝 z] (fun t : ℝ => ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
          * Work.FTS.Nonlinear.FstarPkg.Hz t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
      exact DthIter_Gs_factor hα i ht hθ
    rw [pzIter_eq_iter_deriv_aux,
      iterDeriv_congr_of_eventuallyEq (f := fun t : ℝ => Work.Spaces.DthIter i (Gs α) t θ)
        (g := fun t : ℝ => ((α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ)
          * Work.FTS.Nonlinear.FstarPkg.Hz t) hF k]
    exact iterDeriv_const_mul k Work.FTS.Nonlinear.FstarPkg.Hz (contDiffAt_Hz_finite k hz)
  rw [Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth
      (h := Work.Spaces.DthIter i (Gs α)) (θ := θ)
      (contDiffOn_slice_DthIter_Gs hα i hθ) m z hz,
    DzIter_Hz_eq_sum m z θ hz, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hpk k]
  ring

end Row19GsAux

open Row19GsAux

theorem Gs_bounds : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    (∀ m : ℕ, m ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter m (Work.FTS.Nonlinear.Pieces.RNP.Gs α) z θ|
        ≤ C * α * (z / (1 + z) ^ 2)) ∧
    (∀ i m : ℕ, 1 ≤ i → i ≤ 4 → m ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter m (Work.Spaces.DthIter i (Work.FTS.Nonlinear.Pieces.RNP.Gs α))
          z θ|
        ≤ C * α * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
            * (z / (1 + z) ^ 2)) := by
  obtain ⟨CH, hCHpos, hCH⟩ := abs_DzIter_Hz_le
  refine ⟨10 * CH + 1, by linarith, fun α hα hα1 => ⟨?_, ?_⟩⟩
  · intro m hm z hz θ hθ
    have hz0 : (0 : ℝ) ≤ z := hz
    have hz1 : (-1 : ℝ) < z := by linarith
    have hw : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz0 (by positivity)
    have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have hcoef : |α * Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 * α := by
      rw [abs_div, abs_of_pos hcpos, abs_mul, abs_of_pos hα, abs_of_nonneg hG0]
      rw [div_le_iff₀ hcpos]
      nlinarith
    have hHz := hCH m hm z hz0 θ
    rw [DzIter_Gs_factor hα m hz1, abs_mul]
    calc |α * Work.Spaces.Gam α θ / Work.Spaces.c α|
            * |Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ|
        ≤ (10 * α) * (CH * (z / (1 + z) ^ 2)) :=
          mul_le_mul hcoef hHz (abs_nonneg _) (mul_nonneg (by norm_num) hα.le)
      _ ≤ (10 * CH + 1) * α * (z / (1 + z) ^ 2) := by nlinarith [hw, hCHpos]
  · intro i m hi1 hi4 hm z hz θ hθ
    have hz0 : (0 : ℝ) ≤ z := hz
    have hz1 : (-1 : ℝ) < z := by linarith
    have hw : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz0 (by positivity)
    have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · -- the origin angle: both the profile and its angular factor vanish
      subst h0
      have hzero : ∀ z' : ℝ, Work.Spaces.DthIter i
          (Work.FTS.Nonlinear.Pieces.RNP.Gs α) z' 0 = 0 := by
        intro z'
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        exact DthIter_succ_eq_zero_of_sin (by simp) j z'
      rw [DzIter_eq_zero_of_slice_zero hzero m z, abs_zero]
      have hR : 0 ≤ (10 * CH + 1) * α
          * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 0|
          * (z / (1 + z) ^ 2) := by positivity
      linarith
    rcases eq_or_lt_of_le hθ.2 with hpi | hpi
    · -- the right endpoint of the angular interval
      subst hpi
      have hzero : ∀ z' : ℝ, Work.Spaces.DthIter i
          (Work.FTS.Nonlinear.Pieces.RNP.Gs α) z' (Real.pi / 2) = 0 := by
        intro z'
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        exact DthIter_succ_eq_zero_of_sin
          (by rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]) j z'
      rw [DzIter_eq_zero_of_slice_zero hzero m z, abs_zero]
      have hR : 0 ≤ (10 * CH + 1) * α
          * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 (Real.pi / 2)|
          * (z / (1 + z) ^ 2) := by positivity
      linarith
    · -- the interior of the angular interval
      rw [DzIter_DthIter_Gs_factor hα i m hz1 ⟨h0, hpi⟩, abs_mul]
      have hcoef : |(α / Work.Spaces.c α)
          * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ 10 * α
          * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| := by
        rw [abs_mul, abs_div, abs_of_pos hcpos, abs_of_pos hα]
        rw [div_mul_eq_mul_div, div_le_iff₀ hcpos]
        have hC0 : (0 : ℝ) ≤ |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| :=
          abs_nonneg _
        nlinarith [mul_nonneg hα.le hC0]
      have hHz := hCH m hm z hz0 θ
      calc |(α / Work.Spaces.c α)
              * Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
            * |Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ|
          ≤ (10 * α * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|)
              * (CH * (z / (1 + z) ^ 2)) :=
            mul_le_mul hcoef hHz (abs_nonneg _) (by positivity)
        _ ≤ (10 * CH + 1) * α
              * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
              * (z / (1 + z) ^ 2) := by
            have hC0 : (0 : ℝ) ≤ |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| :=
              abs_nonneg _
            nlinarith [mul_nonneg (mul_nonneg hα.le hC0) hw, hCHpos]

end

end Work.FTS.Nonlinear.Pieces.RNP.row19
