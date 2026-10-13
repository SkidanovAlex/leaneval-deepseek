/-
# Helpers: the `SmoothInt` (weak) hypotheses of the `angmul` interface field

The interface field `Work.FTS.Nonlin.N4Norm.angmul` carries the hypothesis
`Work.Spaces.SmoothInt (fun _ θ => a θ)` on the angular profile, i.e. `a` is `C^∞` on the
*open* strip `(-1,∞) × (0,π/2)` together with `z`-smoothness down to `z = 0` at every angle.
This is strictly weaker than the analyticity hypothesis `∀ θ, ContDiffAt ℝ ⊤ a θ` used by
`Work.FTS.Nonlinear.N4Fields.angmul_field_smooth`; the facts collected here extract exactly
the consequences of `SmoothInt` that the pointwise estimates consume:

* `contDiffOn_snd_of_smoothInt` — the uncurried profile `p ↦ a p.2` is `C^∞` (genuine smooth
  order `Work.Stability.smoothOrder`) on the open quadrant `Q0`;
* `contDiffOn_ang_of_Q0` — conversely, `C^∞` on `Q0` of the uncurried profile gives `C^∞` of
  `a` on the angular interval `(0,π/2)`;
* `smoothInt_angDiv` — `SmoothInt` is preserved by dividing the profile by a constant (the
  rescaling `a = B·a'` used by the proof);
* `smoothOpen_angMul_On` — the `SmoothInt`-form of `smoothOpen_angMul`: multiplying a
  `SmoothOpen` function by a `C^∞`-on-`Q0` angular profile preserves `SmoothOpen`;
* `DthIter_angular_mul_expand_On` — the iterated Leibniz expansion
  `D_θ^i (a·D_z^j f) = ∑_{m≤i} C(i,m) (L^m a) D_θ^{i-m}(D_z^j f)` with only the *open-interval*
  smoothness of `a` (the proof of the analytic version
  `Work.FTS.EllipticEst.Blocks.DthIter_angular_mul_expand` already restricts to `(0,π/2)`).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.N4Fields

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Extracting the angular `C^∞`-data from `SmoothInt` -/

/-- For a profile which is constant in `z`, `SmoothInt` gives that the uncurried profile
`p ↦ a p.2` is `C^∞` (genuine smooth order) on the open quadrant `Q0 = (0,∞) × (0,π/2)`. -/
theorem contDiffOn_snd_of_smoothInt {a : ℝ → ℝ}
    (h : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => a θ)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0 := by
  have h1 := h.1
  refine (h1.mono ?_).of_le le_top
  intro p hp
  simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
  exact ⟨by linarith [hp.1], hp.2⟩

/-- If the uncurried angular profile is `C^∞` on the open quadrant, then the profile itself is
`C^∞` on `(0,π/2)` (evaluate along the line `z = 1`). -/
theorem contDiffOn_ang_of_Q0 {a : ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioo 0 (Real.pi / 2)) := by
  rw [isOpen_Ioo.contDiffOn_iff]
  intro θ hθ
  have hQ : ((1 : ℝ), θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨one_pos, hθ.1, hθ.2⟩
  have h1 : ContDiffAt ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      ((1 : ℝ), θ) :=
    h.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ)
  have h2 : ContDiffAt ℝ Work.Stability.smoothOrder (fun θ' : ℝ => ((1 : ℝ), θ')) θ := by
    fun_prop
  exact h1.comp θ h2

/-- Dividing a `z`-independent `SmoothInt` profile by a constant preserves `SmoothInt`
(the rescaling `a = B·a'` of the proof). -/
theorem smoothInt_angDiv {a : ℝ → ℝ}
    (h : Work.Spaces.SmoothInt (fun _ (θ : ℝ) => a θ)) (B : ℝ) :
    Work.Spaces.SmoothInt (fun _ (θ : ℝ) => a θ / B) := by
  constructor
  · have h1 := h.1
    exact h1.div_const B
  · intro θ hθ
    simpa only using (h.2 θ hθ).div_const B

/-! ## `SmoothOpen` of an angular multiple -/

/-- Multiplying a `SmoothOpen` function by an angular profile which is `C^∞` on the open
quadrant preserves `SmoothOpen`. -/
theorem smoothOpen_angMul_On {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => (fun z θ : ℝ => a θ * G z θ) p.1 p.2) Work.FTS.EllipticEst.Q0
  exact ha.mul hG

/-! ## The iterated Leibniz expansion with open-interval smoothness -/

/-- **Leibniz expansion of `D_θ^i` applied to an angular multiple of a `D_z`-iterate**, with
only the *open-interval* smoothness of the profile `a`: for `a` of class `C^∞` on `(0,π/2)`,
`f` smooth on the open quadrant, and `0 < z`, `θ ∈ (0,π/2)`,
`D_θ^i (a(θ) · D_z^j f (z,θ)) = ∑_{m ≤ i} C(i,m) · (L^m a)(θ) · D_θ^{i-m}(D_z^j f)(z,θ)`.
This is `Work.FTS.EllipticEst.Blocks.DthIter_angular_mul_expand` with the analyticity hypothesis
of `a` replaced by `C^∞` on `(0,π/2)` (which is what its proof uses). -/
theorem DthIter_angular_mul_expand_On {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioo 0 (Real.pi / 2)))
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DthIter i (fun z θ => a θ * Work.Spaces.DzIter j f z θ) z θ
      = ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
          * Work.Spaces.DthIter (i - m) (Work.Spaces.DzIter j f) z θ := by
  have hgOn : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ' => Work.Spaces.DzIter j f z θ') (Set.Ioo 0 (Real.pi / 2)) :=
    (hf.DzIter j).curry_θ hz
  have hmain := Work.FTS.LocData.Lop_iter_mul_eqOn_smooth a
    (fun θ' => Work.Spaces.DzIter j f z θ') (Set.Ioo 0 (Real.pi / 2)) isOpen_Ioo ha hgOn i
  rw [congrFun (Work.Spaces.DthIter_eq_iterate_Lop i
    (fun z θ => a θ * Work.Spaces.DzIter j f z θ) z) θ]
  have hfun : (fun θ' : ℝ => a θ' * Work.Spaces.DzIter j f z θ')
      = a * (fun θ' : ℝ => Work.Spaces.DzIter j f z θ') := rfl
  rw [hfun, hmain hθ]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← congrFun (Work.Spaces.DthIter_eq_iterate_Lop (i - m) (Work.Spaces.DzIter j f) z) θ]
  simp only [Work.FTS.EllipticEst.LopIter]
  ring

end Work.FTS.Nonlinear.N4Fields
