import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.Lgs_sub` — additivity of the ground-state operator `Lgs`

`Lgs α u = -α²·D_z²u - 5α·D_z u - ∂_θ²u - (4 cos 2θ / sin 2θ - tan θ)·∂_θu` is a linear
combination of four (totalized) partial derivatives; the point of this file is that it is
therefore **additive**, `Lgs α (f - g) = Lgs α f - Lgs α g`, at every point where both
arguments are jointly `C²`.  (Nothing beyond `C²` is needed: `Lgs` itself contains no
derivative of the coefficient `4 cos 2θ / sin 2θ - tan θ`, so the failure of the
differentiability of `tan` at `θ = π/2`, which makes the `bslOp` version of this statement
false at `π/2`, is irrelevant here.)

The auxiliary lemmas below are stated generically and are reused by any later file that
needs linearity of the operators `∂_z, ∂_θ, D_z, ∂_z^i, ∂_θ^i` at a point of joint `C²`.
-/

noncomputable section

open scoped Real

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## Slices of a jointly smooth function -/

theorem Lgs_aux_slice_fst {f : ℝ → ℝ → ℝ} {z θ : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ n (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ n (fun z' => f z' θ) z := by
  have h1 : ContDiffAt ℝ n (fun z' : ℝ => (z', θ)) z := by fun_prop
  exact hf.comp z h1

theorem Lgs_aux_slice_snd {f : ℝ → ℝ → ℝ} {z θ : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ n (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ n (fun θ' => f z θ') θ := by
  have h1 : ContDiffAt ℝ n (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  exact hf.comp θ h1

/-! ## The definition of `Lgs`, unfolded -/

theorem Lgs_apply_expand (α : ℝ) (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS_StreamBdry.SB25.Lgs α u z θ
      = -(α ^ 2) * Work.Spaces.DzIter 2 u z θ - 5 * α * Work.Spaces.Dz u z θ
        - Work.Spaces.pthIter 2 u z θ
        - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * Work.Spaces.pth u z θ :=
  rfl

/-! ## Linearity of the first order operators -/

theorem Lgs_aux_pz_sub {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : DifferentiableAt ℝ (fun z' => X z' θ) z)
    (hY : DifferentiableAt ℝ (fun z' => Y z' θ) z) :
    Work.Spaces.pz (fun z θ => X z θ - Y z θ) z θ
      = Work.Spaces.pz X z θ - Work.Spaces.pz Y z θ := by
  simp only [Work.Spaces.pz]
  have h : (fun z' => X z' θ - Y z' θ) = (fun z' => X z' θ) - (fun z' => Y z' θ) := rfl
  rw [h, deriv_sub hX hY]

theorem Lgs_aux_pth_sub {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : DifferentiableAt ℝ (fun θ' => X z θ') θ)
    (hY : DifferentiableAt ℝ (fun θ' => Y z θ') θ) :
    Work.Spaces.pth (fun z θ => X z θ - Y z θ) z θ
      = Work.Spaces.pth X z θ - Work.Spaces.pth Y z θ := by
  simp only [Work.Spaces.pth]
  have h : (fun θ' => X z θ' - Y z θ') = (fun θ' => X z θ') - (fun θ' => Y z θ') := rfl
  rw [h, deriv_sub hX hY]

theorem Lgs_aux_Dz_sub {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : DifferentiableAt ℝ (fun z' => X z' θ) z)
    (hY : DifferentiableAt ℝ (fun z' => Y z' θ) z) :
    Work.Spaces.Dz (fun z θ => X z θ - Y z θ) z θ
      = Work.Spaces.Dz X z θ - Work.Spaces.Dz Y z θ := by
  simp only [Work.Spaces.Dz]
  rw [Lgs_aux_pz_sub hX hY]
  ring

/-! ## Linearity of the iterated operators -/

theorem Lgs_aux_pzIter_sub {i : ℕ} {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : ContDiffAt ℝ i (fun z' => X z' θ) z)
    (hY : ContDiffAt ℝ i (fun z' => Y z' θ) z) :
    Work.Spaces.pzIter i (fun z θ => X z θ - Y z θ) z θ
      = Work.Spaces.pzIter i X z θ - Work.Spaces.pzIter i Y z θ := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv,
    Work.Spaces.pzIter_eq_iteratedDeriv]
  have h : (fun z' => X z' θ - Y z' θ) = (fun z' => X z' θ) - (fun z' => Y z' θ) := rfl
  rw [h, iteratedDeriv_sub hX hY]

/-- `pthIter` is the iterated derivative of the `θ`-slice (the `θ`-analogue of
`Work.Spaces.pzIter_eq_iteratedDeriv`, which is only stated for `∂_z`). -/
theorem Lgs_aux_pthIter_eq_iteratedDeriv (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter k h z θ = iteratedDeriv k (fun θ' => h z θ') θ := by
  rw [iteratedDeriv_eq_iterate]
  induction k generalizing θ with
  | zero => rfl
  | succ n ih =>
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth]
      have hh : (fun θ' => Work.Spaces.pthIter n h z θ') = deriv^[n] (fun θ' => h z θ') := by
        funext θ'; exact ih θ'
      rw [hh, Function.iterate_succ_apply']

theorem Lgs_aux_pthIter_sub {i : ℕ} {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : ContDiffAt ℝ i (fun θ' => X z θ') θ)
    (hY : ContDiffAt ℝ i (fun θ' => Y z θ') θ) :
    Work.Spaces.pthIter i (fun z θ => X z θ - Y z θ) z θ
      = Work.Spaces.pthIter i X z θ - Work.Spaces.pthIter i Y z θ := by
  rw [Lgs_aux_pthIter_eq_iteratedDeriv, Lgs_aux_pthIter_eq_iteratedDeriv,
    Lgs_aux_pthIter_eq_iteratedDeriv]
  have h : (fun θ' => X z θ' - Y z θ') = (fun θ' => X z θ') - (fun θ' => Y z θ') := rfl
  rw [h, iteratedDeriv_sub hX hY]

/-- The second iterate of `D_z = z ∂_z`, expanded:
`D_z²h = z ∂_z h + z² ∂_z²h` (the Stirling numbers `S(2,1) = S(2,2) = 1`). -/
theorem Lgs_aux_DzIter_two_eq {h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h2 : ContDiffAt ℝ 2 (fun z' => h z' θ) z) :
    Work.Spaces.DzIter 2 h z θ
      = z * Work.Spaces.pz h z θ + z ^ 2 * Work.Spaces.pzIter 2 h z θ := by
  have hd : ContDiffAt ℝ 1 (deriv (fun z' => h z' θ)) z :=
    h2.derivWithin (m := 1) (by norm_num)
  have hdif : DifferentiableAt ℝ (fun z' : ℝ => Work.Spaces.pz h z' θ) z := by
    have hh := hd.differentiableAt (by norm_num)
    simpa [Work.Spaces.pz] using hh
  have hmul : deriv (fun z' : ℝ => z' * Work.Spaces.pz h z' θ) z
      = Work.Spaces.pz h z θ + z * Work.Spaces.pzIter 2 h z θ := by
    have h1 := deriv_mul (c := fun z' : ℝ => z') (d := fun z' : ℝ => Work.Spaces.pz h z' θ)
      differentiableAt_id hdif
    have hid : deriv (fun z' : ℝ => z') z = 1 := by simpa using deriv_id z
    rw [hid] at h1
    have hfun : (fun z' : ℝ => z' * Work.Spaces.pz h z' θ)
        = (fun z' : ℝ => z') * (fun z' : ℝ => Work.Spaces.pz h z' θ) := rfl
    rw [hfun, h1]
    simp [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  show z * deriv (fun z' : ℝ => z' * Work.Spaces.pz h z' θ) z
      = z * Work.Spaces.pz h z θ + z ^ 2 * Work.Spaces.pzIter 2 h z θ
  rw [hmul]
  ring

/-! ## The target -/

theorem Lgs_sub (α : ℝ) {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.FTS_StreamBdry.SB25.Lgs α (fun z' θ' => f z' θ' - g z' θ') z θ
      = Work.FTS_StreamBdry.SB25.Lgs α f z θ - Work.FTS_StreamBdry.SB25.Lgs α g z θ := by
  have hfz := Lgs_aux_slice_fst hf
  have hgz := Lgs_aux_slice_fst hg
  have hfθ := Lgs_aux_slice_snd hf
  have hgθ := Lgs_aux_slice_snd hg
  have hdfz : DifferentiableAt ℝ (fun z' => f z' θ) z := hfz.differentiableAt (by norm_num)
  have hdgz : DifferentiableAt ℝ (fun z' => g z' θ) z := hgz.differentiableAt (by norm_num)
  have hdfθ : DifferentiableAt ℝ (fun θ' => f z θ') θ := hfθ.differentiableAt (by norm_num)
  have hdgθ : DifferentiableAt ℝ (fun θ' => g z θ') θ := hgθ.differentiableAt (by norm_num)
  have hD2 : Work.Spaces.DzIter 2 (fun z' θ' => f z' θ' - g z' θ') z θ
      = Work.Spaces.DzIter 2 f z θ - Work.Spaces.DzIter 2 g z θ := by
    rw [Lgs_aux_DzIter_two_eq (h := fun z' θ' => f z' θ' - g z' θ') (hfz.sub hgz),
      Lgs_aux_DzIter_two_eq (h := f) hfz, Lgs_aux_DzIter_two_eq (h := g) hgz,
      Lgs_aux_pz_sub hdfz hdgz, Lgs_aux_pzIter_sub hfz hgz]
    ring
  have hD1 : Work.Spaces.Dz (fun z' θ' => f z' θ' - g z' θ') z θ
      = Work.Spaces.Dz f z θ - Work.Spaces.Dz g z θ :=
    Lgs_aux_Dz_sub hdfz hdgz
  have hT2 : Work.Spaces.pthIter 2 (fun z' θ' => f z' θ' - g z' θ') z θ
      = Work.Spaces.pthIter 2 f z θ - Work.Spaces.pthIter 2 g z θ :=
    Lgs_aux_pthIter_sub hfθ hgθ
  have hT1 : Work.Spaces.pth (fun z' θ' => f z' θ' - g z' θ') z θ
      = Work.Spaces.pth f z θ - Work.Spaces.pth g z θ :=
    Lgs_aux_pth_sub hdfθ hdgθ
  rw [Lgs_apply_expand, Lgs_apply_expand, Lgs_apply_expand]
  rw [hD2, hD1, hT2, hT1]
  ring

end Work.FTS_StreamBdry.SB25
