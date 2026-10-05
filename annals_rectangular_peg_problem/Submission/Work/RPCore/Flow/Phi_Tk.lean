import Mathlib
import Submission.Work.RPCore.Flow.HamFlow

/-!
# The Hamiltonian flow commutes with the deck transformation (`Work.RPCore.Flow.Phi_Tk`)

The Hamiltonian `H` of a `CptPerHam` is invariant under the shift `Tk 1` of the angle `q₂` by `2π`,
and the deck transformation `T : z ↦ (z.1, Tk 1 z.2)` on `ℝ × PS` is a *translation* (addition of
the fixed vector `(0, tkShift)`).  Its derivative is therefore the identity, so the equivariance of
the autonomous field `clampedField` under `T` reduces to the plain identity

`clampedField Hh (T z) = clampedField Hh z`,

which follows from `hamVF_eq_of_Tk` (`clampedField_bounds`).

Consequently both `s ↦ clampFlow Hh s (T z)` and `s ↦ T (clampFlow Hh s z)` are integral curves of
`clampedField Hh` through the same point, so they agree by uniqueness of integral curves
(`Port.ODE.eq_of_isIntegralCurve`).  Reading this in the second factor gives the commutation
`Phi Hh a b (Tk 1 x) = Tk 1 (Phi Hh a b x)` of the two-time flow with the deck transformation.
-/

namespace Work.RPCore.Flow

open Work.RPV

/-- A fixed-time slice `x ↦ H s x` of a `C⁴` Hamiltonian is `C⁴`. -/
theorem contDiff_slice (Hh : CptPerHam) (s : ℝ) :
    ContDiff ℝ 4 (fun x : PS => Hh.H s x) :=
  Hh.smooth.comp (contDiff_const.prodMk contDiff_id)

/-- The clamped Hamiltonian at a fixed time is differentiable. -/
theorem clampHam_differentiable (Hh : CptPerHam) (t : ℝ) :
    Differentiable ℝ (clampHam Hh t) := by
  have h : ContDiff ℝ 4 (fun x : PS => Hh.H (clampPsi t) x) := contDiff_slice Hh _
  exact h.differentiable (by norm_num)

/-- The autonomous clamped field is invariant under the deck transformation `Tk 1`. -/
theorem clampedField_Tk (Hh : CptPerHam) (z : ℝ × PS) :
    clampedField Hh (z.1, Tk 1 z.2) = clampedField Hh z := by
  have hper : ∀ x, clampHam Hh z.1 (Tk 1 x) = clampHam Hh z.1 x := by
    intro x; simp only [clampHam]; rw [Hh.per]
  have h := hamVF_eq_of_Tk (clampHam_differentiable Hh z.1) hper z.2
  simp only [clampedField, autoVF, h]

/-- The clamped flow commutes with the deck transformation `z ↦ (z.1, Tk 1 z.2)`. -/
theorem clampFlow_Tk (Hh : CptPerHam) (t : ℝ) (z : ℝ × PS) :
    clampFlow Hh t (z.1, Tk 1 z.2)
      = ((clampFlow Hh t z).1, Tk 1 (clampFlow Hh t z).2) := by
  let T : ℝ × PS → ℝ × PS := fun w => (w.1, Tk 1 w.2)
  have hTw : ∀ w : ℝ × PS, T w = w + ((0 : ℝ), tkShift) := by
    intro w
    have h2 : w.2 + tkShift = Tk 1 w.2 := (Tk_one_eq_add w.2).symm
    ext <;> simp [T, h2]
  have h1 : IsIntegralCurve (fun s => clampFlow Hh s (T z)) (fun _ y => clampedField Hh y) :=
    clampFlow_curve Hh (T z)
  have h2 : IsIntegralCurve (fun s => T (clampFlow Hh s z)) (fun _ y => clampedField Hh y) := by
    intro s
    have hd : HasDerivAt (fun u => clampFlow Hh u z) (clampedField Hh (clampFlow Hh s z)) s :=
      clampFlow_curve Hh z s
    have hd2 : HasDerivAt (fun u => clampFlow Hh u z + ((0 : ℝ), tkShift))
        (clampedField Hh (clampFlow Hh s z)) s := hd.add_const _
    have hfun : (fun u => T (clampFlow Hh u z))
        = (fun u => clampFlow Hh u z + ((0 : ℝ), tkShift)) :=
      funext (fun u => hTw _)
    rw [hfun]
    convert hd2 using 1
    have hper : ∀ x, clampHam Hh (clampFlow Hh s z).1 (Tk 1 x)
        = clampHam Hh (clampFlow Hh s z).1 x := by
      intro x; simp only [clampHam]; rw [Hh.per]
    have hk := hamVF_eq_of_Tk (clampHam_differentiable Hh (clampFlow Hh s z).1) hper
      (clampFlow Hh s z).2
    have e1 : (clampFlow Hh s z + ((0 : ℝ), tkShift)).1 = (clampFlow Hh s z).1 := by simp
    have e2 : (clampFlow Hh s z + ((0 : ℝ), tkShift)).2 = Tk 1 (clampFlow Hh s z).2 := by
      rw [Prod.snd_add, show ((0 : ℝ), tkShift).2 = tkShift from rfl, ← Tk_one_eq_add]
    simp only [clampedField, autoVF, e1, e2, hk]
  have h0 : (fun s => clampFlow Hh s (T z)) 0 = (fun s => T (clampFlow Hh s z)) 0 := by
    simp [clampFlow_zero]
  have hEq := Port.ODE.eq_of_isIntegralCurve (clampedField_lipschitz Hh) h1 h2 h0
  have := congrFun hEq t
  simpa [T] using this

theorem Phi_Tk (Hh : Work.RPV.CptPerHam) (a b : ℝ) (x : Work.RPV.PS) :
    Work.RPCore.Phi Hh a b (Work.RPV.Tk 1 x) = Work.RPV.Tk 1 (Work.RPCore.Phi Hh a b x) := by
  have h := clampFlow_Tk Hh (b - a) (a, x)
  simp only [Work.RPCore.Phi]
  simpa using congrArg Prod.snd h

end Work.RPCore.Flow
