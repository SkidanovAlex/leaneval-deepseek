import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.VocabO2
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.radial_slot_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

open MeasureTheory Set Filter
open scoped Topology Real

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The radial slots of `FlatW` on the closed rectangle, at arbitrary order

`VocabO2.FlatW l f K` is a statement about the **open** quadrant
`Q0 = (0,∞) × (0,π/2)`: it bounds `|(z+1)^k ∂_z^k f|` there (and the flat angular slots).
`RadialSlot6` extends its first family of slots (`k ≤ l`) to the closed rectangle
`Iz × Iθ = [0,∞) × [0,π/2]`, for **every** order `l`.

The extra points are harmless because `f` vanishes off `Q0`:

* for `θ = 0` or `θ = π/2` the whole `z`-slice of `f` is `0`, hence every iterated
  `z`-derivative vanishes on the slice (`pzIter_eq_zero_of_slice_zero`);
* for `z = 0` and `θ ∈ (0,π/2)` the slice `z' ↦ f z' θ` vanishes on `(-∞,0)`, so each iterated
  `z`-derivative vanishes at `0`: the derivative at the origin of a function vanishing on
  `(-∞,0]` is `0` (`deriv_eq_zero_of_eqOn_Iic_zero`).

This is the general-`l` form of `Work.FTS.PhiStar.radial_slot_le` (which fixes `l = 4`); the
argument never uses the value of `l`. -/

/-- A function which vanishes on the closed left half-line `(-∞,0]` has derivative `0` at the
origin.  (`deriv` is `0` at a point of non-differentiability, while at `0` differentiability
would force the one-sided difference quotients `-g 0 / h`, `h → 0⁻`, to have a finite limit,
hence `g 0 = 0` and derivative `0`.) -/
private lemma deriv_eq_zero_of_eqOn_Iic_zero {g : ℝ → ℝ} (h : ∀ x ≤ 0, g x = 0) :
    deriv g 0 = 0 := by
  have hc : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Iic 0) (0 : ℝ) :=
    hasDerivWithinAt_const 0 (Set.Iic 0) 0
  exact (hc.congr (fun y hy => h y hy) (h 0 le_rfl)).deriv_eq_zero
    (uniqueDiffWithinAt_Iic 0)

/-- If every `z`-slice of `f` at the angular value `θ` vanishes, then every iterated
`z`-derivative of `f` at `θ` vanishes. -/
private lemma pzIter_eq_zero_of_slice_zero {f : ℝ → ℝ → ℝ} {θ : ℝ} (hs : ∀ z, f z θ = 0) :
    ∀ j z, Work.Spaces.pzIter j f z θ = 0 := by
  intro j
  induction j with
  | zero => intro z; exact hs z
  | succ j ih =>
      intro z
      have hfun : (fun z' => Work.Spaces.pzIter j f z' θ) = fun _ => (0 : ℝ) := funext ih
      rw [Work.Spaces.pzIter_succ]
      show deriv (fun z' => Work.Spaces.pzIter j f z' θ) z = 0
      rw [hfun, deriv_const]

/-- If `f (·, θ)` vanishes on the open left half-line and at the origin, then all its iterated
`z`-derivatives vanish at every point of `(-∞,0]`. -/
private lemma pzIter_eq_zero_of_Iio_zero {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (hs : ∀ z < 0, f z θ = 0) (h0 : f 0 θ = 0) :
    ∀ j z, z ≤ 0 → Work.Spaces.pzIter j f z θ = 0 := by
  intro j
  induction j with
  | zero =>
      intro z hz
      rcases hz.eq_or_lt with h | h
      · rw [h]; simpa using h0
      · exact hs z h
  | succ j ih =>
      intro z hz
      have hφ : ∀ w ≤ 0, Work.Spaces.pzIter j f w θ = 0 := ih
      have hstep : deriv (fun z' => Work.Spaces.pzIter j f z' θ) z = 0 := by
        rcases hz.eq_or_lt with h | h
        · rw [h]
          exact deriv_eq_zero_of_eqOn_Iic_zero hφ
        · -- at `z < 0` the slice is identically zero on a neighbourhood of `z`
          have hev : (fun z' => Work.Spaces.pzIter j f z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
            filter_upwards [isOpen_Iio.mem_nhds h] with z' hz'
            exact hφ z' hz'.le
          rw [hev.deriv_eq, deriv_const]
      rw [Work.Spaces.pzIter_succ]
      show deriv (fun z' => Work.Spaces.pzIter j f z' θ) z = 0
      exact hstep

/-- **`RadialSlot6`.**  For a function which is `C^∞` on the open quadrant and vanishes off it,
the radial slots `|(z+1)^k ∂_z^k f| ≤ K`, `k ≤ l`, of `FlatW l` extend from `Q0` to the closed
rectangle `[0,∞) × [0,π/2]`. -/
theorem RadialSlot6 {l : ℕ} {f : ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hzero : ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0)
    (hF : Work.FTS.VocabO2.FlatW l f K) {k : ℕ} (hk : k ≤ l) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |(z + 1) ^ k * Work.Spaces.pzIter k f z θ| ≤ K := by
  intro z hz θ hθ
  have hz0 : 0 ≤ z := hz
  -- `(z', θ) ∈ Q0` forces `θ ∈ (0, π/2)`
  have hth : ∀ z' : ℝ, (z', θ) ∈ Work.FTS.EllipticEst.Q0 → 0 < θ ∧ θ < π / 2 :=
    fun z' hq => ⟨(Work.FTS.EllipticEst.mem_Q0.mp hq).2.1,
      (Work.FTS.EllipticEst.mem_Q0.mp hq).2.2⟩
  rcases hz0.eq_or_lt with hz_eq | hzpos
  · -- `z = 0`
    subst hz_eq
    by_cases hθint : θ ∈ Set.Ioo 0 (π / 2)
    · -- the slice `z' ↦ f z' θ` vanishes off the open quadrant, hence on `(-∞,0]`
      have hs : ∀ z' < 0, f z' θ = 0 := by
        intro z' hz'
        exact hzero z' θ (fun hq =>
          absurd (Work.FTS.EllipticEst.mem_Q0.mp hq).1 (not_lt.mpr hz'.le))
      have h0 : f 0 θ = 0 := hzero 0 θ (fun hq =>
        absurd (Work.FTS.EllipticEst.mem_Q0.mp hq).1 (lt_irrefl 0))
      have hk0 := pzIter_eq_zero_of_Iio_zero hs h0 k 0 le_rfl
      rw [hk0, mul_zero, abs_zero]
      exact hK
    · -- the whole `θ`-slice of `f` vanishes
      have hs : ∀ z', f z' θ = 0 := fun z' => hzero z' θ (fun hq => hθint (hth z' hq))
      have hk0 := pzIter_eq_zero_of_slice_zero hs k 0
      rw [hk0, mul_zero, abs_zero]
      exact hK
  · by_cases hθint : θ ∈ Set.Ioo 0 (π / 2)
    · -- the open quadrant: this is exactly the `k`-th slot of `FlatW`
      exact (hF z θ hzpos hθint.1 hθint.2).1 k hk
    · -- the whole `θ`-slice of `f` vanishes
      have hs : ∀ z', f z' θ = 0 := fun z' => hzero z' θ (fun hq => hθint (hth z' hq))
      have hk0 := pzIter_eq_zero_of_slice_zero hs k z
      rw [hk0, mul_zero, abs_zero]
      exact hK

end Work.FTS.StrongPersist.SP6
