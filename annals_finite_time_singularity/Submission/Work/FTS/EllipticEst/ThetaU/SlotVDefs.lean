/-
# The working class of the mixed-slot estimate `hkMixedSlot_pthU_le2`

The mixed-slot estimate of `Submission/Work/FTS/EllipticEst/ThetaU/hkMixedSlot_pthU_le2.lean`
bounds, pointwise, the `ℋ^k`-slots of

  `U = -3 ∂_θG - α D_z ∂_θG`

by the `ℋ^k`-integrand of `∂_θ²G`.  Its smoothness hypothesis is

  `∀ n, ContDiffOn ℝ n (uncurry G) (Ioi 0 ×ˢ Ioo (-1) (π/2+1))`

which is exactly `Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G` but, in this Mathlib, `ℕ∞`-orders
receive *analyticity* at the top `⊤`, while genuine `C^∞` is the order
`Work.Stability.smoothOrder = ((⊤ : ℕ∞) : ℕ∞ω)`.  All the smooth-calculus lemmas of the
localisation chapter (`Submission/Work/FTS/LocData/SmoothChain.lean`) are stated for
`ContDiffOn ℝ Work.Stability.smoothOrder` on an *arbitrary open set*, so this module

* names the open box `V = (0,∞) × (-1, π/2+1)` of the hypothesis,
* names the class `SmV f = ContDiffOn ℝ smoothOrder (uncurry f) V`,
* provides the bridge `SmoothOpenθ f ↔ SmV f` (`contDiffOn_infty`),
* transports the closure/all-the-way-down lemmas of `SmoothChain` (partials, `D_z`, `D_θ`,
  their iterates, mixed iterates, θ-slices) to `SmV`,
* and gives the locality (`congr`) lemmas for `D_z`, `D_θ` and their iterates on `V`.

These are the conventions in which the pieces of the proof of
`Work.FTS.EllipticEst.ThetaU.hkMixedSlot_pthU_le2` are stated.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.EllipticEst.ThetaU.Defs
import Submission.Work.FTS.EllipticEst.sinIter_weight_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

/-! ## The open box and the smooth class -/

/-- The open box `(0,∞) × (-1, π/2+1)` on which the smoothness hypothesis of the mixed-slot
estimate lives. -/
abbrev V : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)

theorem isOpen_V : IsOpen V := isOpen_Ioi.prod isOpen_Ioo

theorem mem_V {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    (z, θ) ∈ V := ⟨hz, hθ⟩

theorem mem_V_of_Iθ {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) : (z, θ) ∈ V := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact mem_V hz ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `f` is of class `C^∞` (the *genuine* smooth order `smoothOrder`, not analyticity) on the
open box `V`.  This is the class in which the whole proof is run. -/
abbrev SmV (f : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V

/-- The hypothesis of the target statement is exactly `SmV` (the two sets are the same term). -/
theorem SmoothOpenθ.toSmV {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) : SmV f :=
  (contDiffOn_infty).2 h

theorem SmV.toSmoothOpenθ {f : ℝ → ℝ → ℝ} (h : SmV f) : SmoothOpenθ f :=
  fun n => h.of_le (show ((n : ℕ∞) : WithTop ℕ∞) ≤ Work.Stability.smoothOrder from
    WithTop.coe_le_coe.mpr le_top)

/-- Order-`n` form of `SmV`. -/
theorem SmV.of_le_nat {f : ℝ → ℝ → ℝ} (h : SmV f) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry f) V :=
  h.of_le (show ((n : ℕ∞) : WithTop ℕ∞) ≤ Work.Stability.smoothOrder from
    WithTop.coe_le_coe.mpr le_top)

theorem SmV.contDiffAt {f : ℝ → ℝ → ℝ} (h : SmV f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry f) (z, θ) :=
  ContDiffOn.contDiffAt h (isOpen_V.mem_nhds (mem_V hz hθ))

/-! ## Closure of `SmV` -/

theorem SmV.pz {f : ℝ → ℝ → ℝ} (h : SmV f) : SmV (Work.Spaces.pz f) :=
  Work.FTS.LocData.contDiffOn_pz isOpen_V h

theorem SmV.pth {f : ℝ → ℝ → ℝ} (h : SmV f) : SmV (Work.Spaces.pth f) :=
  Work.FTS.LocData.contDiffOn_pth isOpen_V h

theorem SmV.Dz {f : ℝ → ℝ → ℝ} (h : SmV f) : SmV (Work.Spaces.Dz f) :=
  Work.FTS.LocData.contDiffOn_Dz isOpen_V h

theorem SmV.Dth {f : ℝ → ℝ → ℝ} (h : SmV f) : SmV (Work.Spaces.Dth f) :=
  Work.FTS.LocData.contDiffOn_Dth isOpen_V h

theorem SmV.DzIter {f : ℝ → ℝ → ℝ} (h : SmV f) (j : ℕ) :
    SmV (Work.Spaces.DzIter j f) :=
  Work.FTS.LocData.contDiffOn_DzIter isOpen_V h j

theorem SmV.DthIter {f : ℝ → ℝ → ℝ} (h : SmV f) (i : ℕ) :
    SmV (Work.Spaces.DthIter i f) :=
  Work.FTS.LocData.contDiffOn_DthIter isOpen_V h i

theorem SmV.mixed {f : ℝ → ℝ → ℝ} (h : SmV f) (j i : ℕ) :
    SmV (Work.Spaces.mixed j i f) :=
  Work.FTS.LocData.contDiffOn_mixed isOpen_V h j i

theorem SmV.pzIter {f : ℝ → ℝ → ℝ} (h : SmV f) (j : ℕ) : SmV (Work.Spaces.pzIter j f) := by
  induction j with
  | zero => simpa using h
  | succ j ih => simpa [Work.Spaces.pzIter] using ih.pz

theorem SmV.pthIter {f : ℝ → ℝ → ℝ} (h : SmV f) (i : ℕ) : SmV (Work.Spaces.pthIter i f) := by
  induction i with
  | zero => simpa using h
  | succ i ih => simpa [Work.Spaces.pthIter] using ih.pth

/-! ## Angular slices at a fixed level `z > 0` -/

/-- The angular slice of an `SmV` function is `C^∞` on the whole open angular interval. -/
theorem SmV.slice {f : ℝ → ℝ → ℝ} (h : SmV f) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => f z θ) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
  Work.FTS.LocData.contDiffOn_slice_θ h hz

theorem SmV.slice_pthIter {f : ℝ → ℝ → ℝ} (h : SmV f) (m : ℕ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.pthIter m f z θ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
  (h.pthIter m).slice hz

theorem SmV.slice_DzIter {f : ℝ → ℝ → ℝ} (h : SmV f) (m : ℕ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.DzIter m f z θ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
  (h.DzIter m).slice hz

theorem SmV.slice_mixed {f : ℝ → ℝ → ℝ} (h : SmV f) (j i : ℕ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.mixed j i f z θ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
  (h.mixed j i).slice hz

/-! ## Locality on `V` -/

theorem Dz_congr_V {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz g)) (Function.uncurry (Work.Spaces.Dz g')) V := by
  intro y hy
  have hp := Work.Spaces.pz_congr_of_isOpen isOpen_V h hy
  show y.1 * Work.Spaces.pz g y.1 y.2 = y.1 * Work.Spaces.pz g' y.1 y.2
  rw [hp]

theorem Dth_congr_V {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth g)) (Function.uncurry (Work.Spaces.Dth g')) V := by
  intro y hy
  have hp := Work.Spaces.pth_congr_of_isOpen isOpen_V h hy
  show Real.sin (2 * y.2) * Work.Spaces.pth g y.1 y.2
      = Real.sin (2 * y.2) * Work.Spaces.pth g' y.1 y.2
  rw [hp]

theorem DzIter_congr_V {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j g))
      (Function.uncurry (Work.Spaces.DzIter j g')) V := by
  induction j with
  | zero => exact h
  | succ j ih => exact Dz_congr_V ih

theorem DthIter_congr_V {g g' : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry g) (Function.uncurry g') V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i g))
      (Function.uncurry (Work.Spaces.DthIter i g')) V := by
  induction i with
  | zero => exact h
  | succ i ih => exact Dth_congr_V ih

/-! ## The angular profile `sinTwo` and the identification with `sinIter` -/

/-- `θ ↦ sin 2θ`, as a function of the two variables (constant in `z`). -/
abbrev sinTwo : ℝ → ℝ → ℝ := fun _ θ => Real.sin (2 * θ)

theorem sinTwo_apply (z θ : ℝ) : sinTwo z θ = Real.sin (2 * θ) := rfl

theorem contDiffOn_sinTwo_slice (z : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => sinTwo z θ)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
  ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn)

/-- The `D_θ`-iterates compose. -/
theorem DthIter_add_apply (a b : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter (a + b) g = Work.Spaces.DthIter a (Work.Spaces.DthIter b g) := by
  induction a with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_add, Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]

/-- `D_θ ∂_θ f = sin 2θ · ∂_θ²f`. -/
theorem DthIter_one_pth (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter 1 (Work.Spaces.pth f)
      = fun z θ => Real.sin (2 * θ) * Work.Spaces.pthIter 2 f z θ := rfl

/-- `D_θ^a (sin 2θ)` is the angular profile `sinIter a` of the elliptic chapter. -/
theorem DthIter_sinTwo_eq_sinIter (a : ℕ) : ∀ z θ,
    Work.Spaces.DthIter a sinTwo z θ = Work.FTS.EllipticEst.sinIter a θ := by
  induction a with
  | zero => intro z θ; simp [sinTwo, Work.FTS.EllipticEst.sinIter]
  | succ a ih =>
      intro z θ
      have h1 : Work.Spaces.DthIter (a + 1) sinTwo z θ
          = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter a sinTwo z θ') θ := rfl
      have h2 : Work.FTS.EllipticEst.sinIter (a + 1) θ
          = Real.sin (2 * θ)
              * deriv (fun θ' => Work.FTS.EllipticEst.sinIter a θ') θ := by
        show Real.sin (2 * θ)
            * deriv (fun θ' => Work.Spaces.DthIter a (fun _ θ'' => Real.sin (2 * θ'')) 0 θ') θ = _
        rw [show (fun θ' => Work.Spaces.DthIter a (fun _ θ'' => Real.sin (2 * θ'')) 0 θ')
            = (fun θ' => Work.FTS.EllipticEst.sinIter a θ') from funext fun θ' => ih 0 θ']
      rw [h1, h2]
      rw [show (fun θ' => Work.Spaces.DthIter a sinTwo z θ')
          = (fun θ' => Work.FTS.EllipticEst.sinIter a θ') from funext fun θ' => ih z θ']

end Work.FTS.EllipticEst.ThetaU
