import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.DzCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TTSlot11Aux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The open-quadrant ingredients

Everything in this section is stated for data which are `C^∞` on the open quadrant
`Q0 = (0,∞) × (0,π/2)` (the class `Work.FTS.EllipticEst.SmoothOpen`) and is used at a point
`(z,θ)` of `Q0`.  All the statements are in the *internal* shape
`∀ z θ, 0 < z → 0 < θ → θ < π/2 → …` of the chapter. -/

/-- `z² ∂_z² Ψ = D_z² Ψ - D_z Ψ` at every point of the open quadrant, for `Ψ` which is `C^∞`
there.  (The open-quadrant counterpart of `Work.FTS.EllipticEst.Cert.DzAux.zsq_pzIter2_eqOn`,
which is stated for `SmoothNbhd`.) -/
theorem zsq_pzIter2_eq_open (Ψ : ℝ → ℝ → ℝ) (hΨ : SmoothOpen Ψ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.Dz Ψ z θ := by
  have hd1 : DifferentiableAt ℝ (fun z' => Ψ z' θ) z :=
    (hΨ.hasDerivAt_slice hθ hz).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Ψ z' θ) z :=
    (hΨ.hasDerivAt_slice_pzIter 1 hθ hz).differentiableAt
  exact Work.FTS.EllipticEst.zsq_pzIter2_eq Ψ hd1 hd2

/-- Two functions agreeing on the open quadrant have the same iterated `D_θ`-derivatives
there.  (Locality of `D_θ`; no smoothness is needed.) -/
theorem DthIter_congr_open {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i F z θ = Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; exact h z θ hz h1 h2
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun θ' => Work.Spaces.DthIter n F z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n G z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)]
          with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq]

/-- Two functions agreeing on the open quadrant have the same mixed derivatives there. -/
theorem mixed_congr_open {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i F z θ = Work.Spaces.mixed j i G z θ :=
  SmoothOpen.DzIter_congr (F := Work.Spaces.DthIter i F) (G := Work.Spaces.DthIter i G)
    (DthIter_congr_open h i) j

/-- The iterated `D_z`-operator is additive for `-` on the open quadrant for `SmoothOpen`
data.  (The subtraction counterpart of `Work.FTS.EllipticEst.SmoothOpen.DzIter_add`.) -/
theorem DzIter_sub_open {F G : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (hG : SmoothOpen G) (j : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j (fun z θ => F z θ - G z θ) z θ
        = Work.Spaces.DzIter j F z θ - Work.Spaces.DzIter j G z θ := by
  induction j with
  | zero => intro z θ hz h1 h2; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => F z θ - G z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n F z' θ - Work.Spaces.DzIter n G z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n F z' θ) z :=
        ((hF.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n G z' θ) z :=
        ((hG.DzIter n).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd : deriv (fun z' => Work.Spaces.DzIter n F z' θ - Work.Spaces.DzIter n G z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n F z' θ) z
            - deriv (fun z' => Work.Spaces.DzIter n G z' θ) z := deriv_sub hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- The iterated `D_θ`-operator is additive for `-` on the open quadrant for `SmoothOpen`
data. -/
theorem DthIter_sub_open {F G : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (hG : SmoothOpen G) (i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => F z θ - G z θ) z θ
        = Work.Spaces.DthIter i F z θ - Work.Spaces.DthIter i G z θ := by
  induction i with
  | zero => intro z θ hz h1 h2; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨h1, h2⟩
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => F z θ - G z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n F z θ' - Work.Spaces.DthIter n G z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n F z θ') θ :=
        (((hF.DthIter n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n G z θ') θ :=
        (((hG.DthIter n).curry_θ hz).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθ)
      have hd : deriv (fun θ' => Work.Spaces.DthIter n F z θ' - Work.Spaces.DthIter n G z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n F z θ') θ
            - deriv (fun θ' => Work.Spaces.DthIter n G z θ') θ := deriv_sub hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

/-- The mixed operators `D_z^j D_θ^i` are additive for `-` on the open quadrant for
`SmoothOpen` data. -/
theorem mixed_sub_open {F G : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (hG : SmoothOpen G) (j i : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => F z θ - G z θ) z θ
        = Work.Spaces.mixed j i F z θ - Work.Spaces.mixed j i G z θ := by
  intro z θ hz h1 h2
  have hcongr := SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i (fun z θ => F z θ - G z θ))
    (G := fun z θ => Work.Spaces.DthIter i F z θ - Work.Spaces.DthIter i G z θ)
    (fun z θ hz h1 h2 => DthIter_sub_open hF hG i z θ hz h1 h2) j z θ hz h1 h2
  have hadd := DzIter_sub_open (hF.DthIter i) (hG.DthIter i) j z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-- **`D_z^b` commutes with the mixed operator on the open quadrant**:
`mixed m i (D_z^b f) = mixed (m+b) i f` there, for `f` which is `C^∞` on the open quadrant.
This is the open-quadrant counterpart of the case `a = 0` of
`Work.Spaces.mixed_comm` (which is stated for `SmoothNbhd`). -/
theorem mixed_DzIter_open (f : ℝ → ℝ → ℝ) (hF : SmoothOpen f) (m i b : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed m i (Work.Spaces.DzIter b f) z θ
        = Work.Spaces.mixed (m + b) i f z θ := by
  intro z θ hz h1 h2
  have hloc := SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i (Work.Spaces.DzIter b f))
    (G := fun z θ => Work.Spaces.mixed b i f z θ)
    (fun z θ hz' h1' h2' => SmoothOpen.DthIter_DzIter_eq_mixed hF b i hz' ⟨h1', h2'⟩)
    m z θ hz h1 h2
  rw [show Work.Spaces.mixed m i (Work.Spaces.DzIter b f) z θ
      = Work.Spaces.DzIter m (Work.Spaces.DzIter b (Work.Spaces.DthIter i f)) z θ from hloc]
  rw [← Work.Spaces.DzIter_add_right m b (Work.Spaces.DthIter i f)]
  rfl

/-! ## The commutation `z²∂_z²(mixed m i f) = mixed m i (z²∂_z² f)` -/

/-- **The commutation `z²∂_z² (D_z^j D_θ^i f) = D_z^j D_θ^i (z²∂_z² f)` on the open quadrant.**

For `f` which is `C^n` on the open quadrant `(0,∞) × (0,π/2)` for every finite `n` (the class
`Work.FTS.EllipticEst.SmoothOpen` of `Submission/Work/FTS/EllipticEst/OpenQDefs.lean`), every
`j i : ℕ`, every `z > 0` and every `θ ∈ (0, π/2)`,

  `z² · ∂_z² (mixed j i f) (z,θ) = mixed j i (fun z θ => z² · ∂_z² f z θ) (z,θ)`,

where `mixed j i f = D_z^j D_θ^i f = Work.Spaces.DzIter j (Work.Spaces.DthIter i f)` and
`pzIter 2 = ∂_z²` (`Work.Spaces.pzIter 2`).

This is the open-quadrant counterpart of `Work.FTS.EllipticEst.Cert.DzAux.zsq_pzIter2_mixed`,
which is stated for `Work.Spaces.SmoothNbhd` (`C^ω` on a neighbourhood of the *closed* quadrant)
— strictly stronger than the hypothesis here.

Route: `z²∂_z²` commutes with `D_z = z∂_z` (`[z∂_z, z²∂_z²] = 0`, a direct product-rule
computation) and with `D_θ = sin(2θ)∂_θ` (Clairaut, the coefficient is independent of `z`); hence
`z²∂_z² (D_z^j D_θ^i f) = D_z^j (z²∂_z² (D_θ^i f)) = D_z^j D_θ^i (z²∂_z² f)` at the point.
Equivalently, follow `Cert.DzAux.zsq_pzIter2_mixed`: use `z²∂_z²ψ = D_z²ψ - D_zψ` (product rule,
for a `C²` function on the open quadrant), and the facts that `D_z^j` and `D_θ^i` are additive on
the open quadrant and commute with each other there (`Work.Spaces.DzIter_add_right`,
`Work.Spaces.DthIter_DzIter_eq_mixed_open` in
`Submission/Work/FTS/EllipticEst/SliceDecompDefs.lean`, and the local counterparts of
`Dz_sub_eqOn`/`mixed_sub_eqOn`/`mixed_congr`, which in `Cert/DzPsiAux.lean` are stated for
`SmoothNbhd` and must be redone for the open class with `ContDiffAt`/`ContDiffOn` on the open
quadrant — the pointwise calculus `Work.Spaces.pz_congr_of_isOpen`, `pth_congr_of_isOpen`,
`Work.Spaces.deriv_deriv_fst_snd` of `Submission/Work/Spaces/mixed_comm.lean` is available). -/
theorem zsq_pzIter2_mixed_open (f : ℝ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (m i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z θ
      = Work.Spaces.mixed m i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ := by
  have hF : SmoothOpen f := smoothOpen_of_forall hf
  have hA : SmoothOpen (Work.Spaces.mixed m i f) := hF.mixed m i
  -- the left-hand side is `D_z²(mixed m i f) - D_z(mixed m i f)`, which is
  -- `mixed (m+2) i f - mixed (m+1) i f`
  have hL : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z θ
      = Work.Spaces.mixed (m + 2) i f z θ - Work.Spaces.mixed (m + 1) i f z θ := by
    rw [zsq_pzIter2_eq_open (Work.Spaces.mixed m i f) hA hz hθ]
    have e1 : Work.Spaces.DzIter 2 (Work.Spaces.mixed m i f) z θ
        = Work.Spaces.mixed (m + 2) i f z θ := by
      show Work.Spaces.DzIter 2 (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ = _
      rw [← Work.Spaces.DzIter_add_right 2 m (Work.Spaces.DthIter i f)]
      rw [show 2 + m = m + 2 from by omega]
      rfl
    have e2 : Work.Spaces.Dz (Work.Spaces.mixed m i f) z θ
        = Work.Spaces.mixed (m + 1) i f z θ := by
      show Work.Spaces.DzIter 1 (Work.Spaces.DzIter m (Work.Spaces.DthIter i f)) z θ = _
      rw [← Work.Spaces.DzIter_add_right 1 m (Work.Spaces.DthIter i f)]
      rw [show 1 + m = m + 1 from by omega]
      rfl
    rw [e1, e2]
  -- the right-hand side, term by term
  have hR1 : Work.Spaces.mixed m i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ
      = Work.Spaces.mixed m i (fun z θ => Work.Spaces.DzIter 2 f z θ
          - Work.Spaces.Dz f z θ) z θ := by
    refine mixed_congr_open ?_ m i z θ hz hθ.1 hθ.2
    intro z θ hz' h1 h2
    exact zsq_pzIter2_eq_open f hF hz' ⟨h1, h2⟩
  have hR2 : Work.Spaces.mixed m i (fun z θ => Work.Spaces.DzIter 2 f z θ
          - Work.Spaces.Dz f z θ) z θ
      = Work.Spaces.mixed m i (Work.Spaces.DzIter 2 f) z θ
        - Work.Spaces.mixed m i (Work.Spaces.Dz f) z θ :=
    mixed_sub_open (hF.DzIter 2) hF.Dz m i z θ hz hθ.1 hθ.2
  have hR3 : Work.Spaces.mixed m i (Work.Spaces.DzIter 2 f) z θ
      = Work.Spaces.mixed (m + 2) i f z θ :=
    mixed_DzIter_open f hF m i 2 z θ hz hθ.1 hθ.2
  have hR4 : Work.Spaces.mixed m i (Work.Spaces.Dz f) z θ
      = Work.Spaces.mixed (m + 1) i f z θ :=
    mixed_DzIter_open f hF m i 1 z θ hz hθ.1 hθ.2
  rw [hL, hR1, hR2, hR3, hR4]

end Work.FTS.EllipticEst.TTSlot11Aux
