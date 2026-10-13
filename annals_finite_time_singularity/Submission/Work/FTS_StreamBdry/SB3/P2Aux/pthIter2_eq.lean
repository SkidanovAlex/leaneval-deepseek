import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Elliptic.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.bslOp_split

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB3.P2Aux

open scoped Real Topology

/-! ## Calculus helpers

The proof is the second-order product rule for `Q = sin 2θ · (Q / sin 2θ)` on the `θ`-slice,
combined with the ground-state identity `bslOp α Q = s2 · Lgs α (Q/s2)` of
`SB25.bslOp_split` (which supplies exactly the `Dz`-terms of the statement). -/

/-- `iteratedDeriv 2 f = deriv (deriv f)`. -/
private lemma iteratedDeriv_two_eq (f : ℝ → ℝ) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  have h : (2 : ℕ) = 1 + 1 := rfl
  rw [h, iteratedDeriv_succ, iteratedDeriv_one]

/-- `deriv s2 θ = 2 cos 2θ`. -/
private lemma deriv_s2_eq (θ : ℝ) :
    deriv Work.Construction.s2 θ = 2 * Real.cos (2 * θ) := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h3 : HasDerivAt (Real.sin ∘ fun θ' : ℝ => 2 * θ') (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ h2
    have h4 : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
    rw [h4] at h3
    convert h3 using 1
    funext x; rfl
  show deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ)
  exact h.deriv

/-- `iteratedDeriv 2 s2 θ = -4 s2 θ` (i.e. `s2'' = -4 s2`). -/
private lemma iteratedDeriv_two_s2 (θ : ℝ) :
    iteratedDeriv 2 Work.Construction.s2 θ = -4 * Work.Construction.s2 θ := by
  have h : HasDerivAt (fun θ' : ℝ => 2 * Real.cos (2 * θ')) (-4 * Real.sin (2 * θ)) θ := by
    have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h3 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-Real.sin (2 * θ) * 2) θ := by
      have hh := (Real.hasDerivAt_cos (2 * θ)).comp θ h2
      simpa only [Function.comp_def] using hh
    have h4 : HasDerivAt (fun θ' : ℝ => 2 * Real.cos (2 * θ'))
        (2 * (-Real.sin (2 * θ) * 2)) θ := h3.const_mul (2 : ℝ)
    have h5 : 2 * (-Real.sin (2 * θ) * 2) = -4 * Real.sin (2 * θ) := by ring
    rw [h5] at h4
    exact h4
  rw [iteratedDeriv_two_eq]
  have hd : deriv Work.Construction.s2 = fun θ' : ℝ => 2 * Real.cos (2 * θ') :=
    funext deriv_s2_eq
  rw [hd, h.deriv]
  rfl

/-- **Second-order product rule for `Q = s2 · u` on the `θ`-slice**:
`Q_{θθ} = -4 s2 u + 4 cos 2θ · u' + s2 · u_{θθ}`. -/
private lemma pthIter2_prod {Q : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hQ : ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ))
    (hsin : Work.Construction.s2 θ ≠ 0) :
    Work.Spaces.pthIter 2 Q z θ
      = -4 * Work.Construction.s2 θ * (Q z θ / Work.Construction.s2 θ)
        + 4 * Real.cos (2 * θ) * deriv (fun θ' => Q z θ' / Work.Construction.s2 θ') θ
        + Work.Construction.s2 θ
          * Work.Spaces.pthIter 2 (fun z θ' => Q z θ' / Work.Construction.s2 θ') z θ := by
  have hs2C : ContDiffAt ℝ 2 Work.Construction.s2 θ := by
    show ContDiffAt ℝ 2 (fun θ' : ℝ => Real.sin (2 * θ')) θ
    fun_prop
  have hA : ContDiffAt ℝ 2 (fun θ' : ℝ => Q z θ') θ := by
    have h := hQ.comp θ (ContDiffAt.prodMk contDiffAt_const contDiffAt_id)
    simpa only [Function.comp_def, Function.uncurry] using h
  have hB : ContDiffAt ℝ 2 (fun θ' : ℝ => Q z θ' / Work.Construction.s2 θ') θ :=
    hA.div hs2C hsin
  have hcont : ContinuousAt Work.Construction.s2 θ := hs2C.continuousAt
  have hev : (fun θ' : ℝ => Q z θ') =ᶠ[𝓝 θ]
      (Work.Construction.s2 * fun θ' : ℝ => Q z θ' / Work.Construction.s2 θ') := by
    filter_upwards [hcont.preimage_mem_nhds (isOpen_ne (x := (0 : ℝ)) |>.mem_nhds hsin)]
      with θ' hθ'
    exact (mul_div_cancel₀ (Q z θ') hθ').symm
  have h1 : Work.Spaces.pthIter 2 Q z θ = iteratedDeriv 2 (fun θ' : ℝ => Q z θ') θ := by
    rw [iteratedDeriv_two_eq]
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  have h2 : Work.Spaces.pthIter 2 (fun z θ' => Q z θ' / Work.Construction.s2 θ') z θ
      = iteratedDeriv 2 (fun θ' : ℝ => Q z θ' / Work.Construction.s2 θ') θ := by
    rw [iteratedDeriv_two_eq]
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  rw [h1, Filter.EventuallyEq.iteratedDeriv_eq 2 hev, iteratedDeriv_mul hs2C hB, h2]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.reduceSub, iteratedDeriv_zero]
  norm_num
  rw [deriv_s2_eq, iteratedDeriv_two_s2, Work.Construction.s2_eq]
  ring

/-- The second `θ`-derivative of `Q` in terms of `u := Q/s2` and `F = bslOp α Q`:
`Q_{θθ} = -4 s2 u + 2 sin^2 θ * u' - F - s2 * (α^2 DzIter 2 u + 5 α Dz u)`.
Product rule on `Q = s2 * u` together with `bslOp α Q = -s2 * Lgs α u` (equivalently
`bslOp_div_s2_hasDerivAt`, which is being proved in parallel at the sibling path). -/
theorem pthIter2_eq {α : ℝ} {Q F : ℝ → ℝ → ℝ}
    (hCt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ))
    (hlaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp α Q z θ = F z θ) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pthIter 2 Q z θ
        = -4 * Work.Construction.s2 θ * (Q z θ / Work.Construction.s2 θ)
          + 2 * Real.sin θ ^ 2 * deriv (fun θ' => Q z θ' / Work.Construction.s2 θ') θ
          - F z θ
          - Work.Construction.s2 θ
              * (α ^ 2 * Work.Spaces.DzIter 2 (fun z θ => Q z θ / Work.Construction.s2 θ) z θ
                  + 5 * α * Work.Spaces.Dz (fun z θ => Q z θ / Work.Construction.s2 θ) z θ) := by
  intro z θ hmem
  have hs2 : Work.Construction.s2 θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.s2_pos_of_Qd hmem)
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem)
  have hsplit : Work.Elliptic.bslOp α Q z θ
      = Work.Construction.s2 θ * Work.FTS_StreamBdry.SB25.Lgs α
          (fun z θ' => Q z θ' / Work.Construction.s2 θ') z θ :=
    Work.FTS_StreamBdry.SB25.bslOp_split α Q hmem (hCt z θ hmem)
  have hF : F z θ = Work.Construction.s2 θ * Work.FTS_StreamBdry.SB25.Lgs α
      (fun z θ' => Q z θ' / Work.Construction.s2 θ') z θ := by
    rw [← hlaw z θ hmem, hsplit]
  rw [pthIter2_prod (hCt z θ hmem) hs2, hF]
  simp only [Work.FTS_StreamBdry.SB25.Lgs, Work.Spaces.pth]
  rw [Work.Construction.s2_eq]
  have hc : Real.sin (2 * θ) * (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ)
      = 4 * Real.cos (2 * θ) - 2 * Real.sin θ ^ 2 := by
    have hs : Real.sin (2 * θ) ≠ 0 := by
      rw [← Work.Construction.s2_eq]; exact hs2
    rw [mul_sub, mul_div_cancel₀ _ hs]
    rw [mul_comm (Real.sin (2 * θ)) (Real.tan θ), ← Work.Construction.s2_eq θ,
      Work.FTS_StreamBdry.tan_mul_s2 hcos]
  linear_combination (-(deriv (fun θ' => Q z θ' / Work.Construction.s2 θ') θ)) * hc

end Work.FTS_StreamBdry.SB3.P2Aux
