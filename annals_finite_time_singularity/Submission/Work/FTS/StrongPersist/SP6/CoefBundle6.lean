import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.F0_theta_coefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_z_coefs
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr
import Submission.Work.FTS.PhiStar.CoreAux.LopIter_continuousOn_of_contDiff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

/-!
# `FTS/StrongPersist/SP6/CoefBundle6` — the ten coefficient functions of `StarPkgo2` lie in `F0 6`

The flat class `Work.FTS.PhiStar.F0 n K f` bounds all the mixed weighted derivatives
`(z+1)^k ∂_z^k D_θ^i f` (`k + i ≤ n`) on the open quadrant.  The `SP6` assembly multiplies its
analytic data by ten coefficient functions: the four angular ones
`sin²θ, cos²θ - 2 sin²θ, sin 2θ, cos 2θ`, the four *derivatives* of the first four
(these are the angular coefficients of `∂_θ`-slots), and the two radial ones
`z/(1+z)`, `(1+z)⁻¹`.

`F0_theta_coefs` and `F0_z_coefs` already supply the first four and the last two, each with its
own positive constant.  The four derivative functions are *also* `θ`-only, so they are handled
by the same generic `θ`-only tool `CoreAux.exists_F0_of_theta_only_aux`: the derivative is first
identified with an explicit smooth trigonometric function (`deriv_sin_sq`, `deriv_cos_sq_sub`,
`deriv_sin_two`, `deriv_cos_two`), and `F0` is insensitive to replacing a function by another
one agreeing with it on the open quadrant (`CoreAux.F0_congr`).

Finally the finitely many positive constants are merged into a single `A ≥ 1`.  This is a pure
bookkeeping lemma: its value is that the `SP6` consumer gets one constant for all ten slots.
-/

/-- **A `θ`-only `C⁶` function lies in `F0 6`** with some positive constant.

This is the `m = 6` instance of the generic tool: for a `θ`-only datum every slot with a radial
derivative vanishes, and the purely angular slots are bounded by the suprema on the compact
interval `Iθ` of the continuous functions `Lop^[i] c`, `i ≤ 6`
(`LopIter_continuousOn_of_contDiff`). -/
private theorem F0_six_of_theta_smooth (c : ℝ → ℝ)
    (hc : ContDiff ℝ ((6 : ℕ∞) : WithTop ℕ∞) c) :
    ∃ A : ℝ, 0 < A ∧ Work.FTS.PhiStar.F0 6 A (fun _ θ => c θ) :=
  Work.FTS.PhiStar.CoreAux.exists_F0_of_theta_only_aux 6 c
    (fun i hi => Work.FTS.PhiStar.CoreAux.LopIter_continuousOn_of_contDiff 6 c hc i hi)

/-- **The `θ`-derivative of a `θ`-only function lies in `F0 6` as soon as the derivative is
identified with an explicit `C⁶` function.**

`F0` only sees the open quadrant (`CoreAux.F0_congr`), so the pointwise identity
`deriv c θ = d θ` transfers the `F0 6`-membership of the `θ`-only datum `d`. -/
private theorem F0_six_of_deriv {c d : ℝ → ℝ} (hd : ∀ θ, deriv c θ = d θ)
    (hs : ContDiff ℝ ((6 : ℕ∞) : WithTop ℕ∞) d) :
    ∃ A : ℝ, 0 < A ∧ Work.FTS.PhiStar.F0 6 A (fun _ θ => deriv c θ) := by
  obtain ⟨A, hA, hAd⟩ := F0_six_of_theta_smooth d hs
  exact ⟨A, hA, Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => hd θ) hAd⟩

/-- `deriv (sin²) = 2 sin θ cos θ`. -/
private lemma deriv_sin_sq (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin θ' ^ 2) θ = 2 * Real.sin θ * Real.cos θ := by
  have h := (Real.hasDerivAt_sin θ).pow 2
  simpa using h.deriv

/-- `deriv (cos² - 2 sin²) = -6 sin θ cos θ`. -/
private lemma deriv_cos_sq_sub (θ : ℝ) :
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

/-- `deriv (sin 2θ) = 2 cos 2θ`. -/
private lemma deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) := by
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hd := h.deriv
  have e : deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = deriv (Real.sin ∘ HMul.hMul 2) θ := rfl
  rw [e, hd]
  ring

/-- `deriv (cos 2θ) = -2 sin 2θ`. -/
private lemma deriv_cos_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.cos (2 * θ')) θ = -(2 * Real.sin (2 * θ)) := by
  have h := (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hd := h.deriv
  have e : deriv (fun θ' : ℝ => Real.cos (2 * θ')) θ = deriv (Real.cos ∘ HMul.hMul 2) θ := rfl
  rw [e, hd]
  ring

theorem CoefBundle6 : ∃ A : ℝ, 1 ≤ A ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => deriv (fun θ' => Real.sin θ' ^ 2) θ) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => deriv (fun θ' => Real.sin (2 * θ')) θ) ∧
    Work.FTS.PhiStar.F0 6 A (fun _ θ => deriv (fun θ' => Real.cos (2 * θ')) θ) ∧
    Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) ∧
    Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) := by
  obtain ⟨A₁, hA₁, h1, h2, h3, h4⟩ := Work.FTS.PhiStar.CoreAux.F0_theta_coefs 6
  obtain ⟨A₂, hA₂, h9, h10⟩ := Work.FTS.PhiStar.CoreAux.F0_z_coefs 6
  obtain ⟨A₃, hA₃, h5⟩ :=
    F0_six_of_deriv (c := fun θ' : ℝ => Real.sin θ' ^ 2)
      (fun θ => deriv_sin_sq θ) (by fun_prop)
  obtain ⟨A₄, hA₄, h6⟩ :=
    F0_six_of_deriv (c := fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2)
      (fun θ => deriv_cos_sq_sub θ) (by fun_prop)
  obtain ⟨A₅, hA₅, h7⟩ :=
    F0_six_of_deriv (c := fun θ' : ℝ => Real.sin (2 * θ')) (fun θ => deriv_sin_two θ) (by fun_prop)
  obtain ⟨A₆, hA₆, h8⟩ :=
    F0_six_of_deriv (c := fun θ' : ℝ => Real.cos (2 * θ')) (fun θ => deriv_cos_two θ) (by fun_prop)
  refine ⟨A₁ + A₂ + A₃ + A₄ + A₅ + A₆ + 1, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h1
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h2
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h4
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h3
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h5
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h6
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h7
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h8
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h9
  · exact Work.FTS.PhiStar.F0.mono le_rfl (by linarith) h10

end Work.FTS.StrongPersist.SP6
