import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Sm2Split

/-!
# The `Sm4`/`Sm5` slices: `Sm4 = Sm4Ref + dSm4`, `Sm5 = Sm5Ref + dSm5`

Both summands reduce immediately to atoms already defined in `KPlus24Refs` / `PhiSplit`.

* `Sm4 = (Ufun - Uref) + Uref·(1 - E₄(z)³)`.  With `Ufun = UfunRef + dUfun`
  (`Ufun_eq_ref_add`) and `E₄(z)³ = E4Ref³ + dE4c` (`E4Fun_cube_ref_add`), this is
  `Sm4Ref + dUfun - Uref·dE4c`.  `Uref` is already an explicit expression in the `τ`-atoms and
  `S0z z`, so it needs no reference of its own.
* `Sm5 = -(Δ(z)·j(τ))·Θ₀`.  With the reference `Δ_ref = q·DqRef` of `Δ(z)` (the `q³`
  truncation, reusing `DqRef` from `Sm2Split`) and `dDelta = Δ(z) - Δ_ref`, this is
  `-(Δ_ref·j(τ))·Θ₀ - (dDelta·j(τ))·Θ₀`.

As before, every summand of `dSm4`/`dSm5` is one deviation (`dUfun`, `dE4c`, `dDelta`) times a
reference cofactor (`Uref`, `j(τ)`, `Θ₀`), i.e. already in `BoundQ` shape.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-! ## The reference of `Δ(z)` itself -/

/-- Reference value of `Δ(z)` (the `q³` truncation of its `q`-expansion). -/
def DeltaRef (z : ℍ) : ℂ := Work.Kernels.qParamFun z * DqRef z

/-- Deviation of `Δ(z)` from `DeltaRef`. -/
def dDelta (z : ℍ) : ℂ := Work.Kernels.DeltaFun z - DeltaRef z

lemma DeltaFun_ref_add (z : ℍ) :
    Work.Kernels.DeltaFun z = DeltaRef z + dDelta z := by
  simp only [dDelta]; ring

/-! ## `Sm4` -/

/-- The reference part of `K24F.Sm4`. -/
def Sm4Ref (τ z : ℍ) : ℂ :=
  (UfunRef τ z - Work.Asymptotics.K24F.Uref τ z)
    + Work.Asymptotics.K24F.Uref τ z * (1 - E4Ref z ^ 3)

/-- The deviation part of `K24F.Sm4`. -/
def dSm4 (τ z : ℍ) : ℂ :=
  dUfun τ z - Work.Asymptotics.K24F.Uref τ z * dE4c z

/-- **The `Sm4`-split**: `Sm4 = Sm4Ref + dSm4`, exactly. -/
lemma Sm4_eq_ref_add (τ z : ℍ) :
    Work.Asymptotics.K24F.Sm4 τ z = Sm4Ref τ z + dSm4 τ z := by
  have hU := Ufun_eq_ref_add τ z
  have hE4 := E4Fun_cube_ref_add z
  simp only [Work.Asymptotics.K24F.Sm4, Sm4Ref, dSm4]
  rw [hU, hE4]
  ring

/-! ## `Sm5` -/

/-- The reference part of `K24F.Sm5`. -/
def Sm5Ref (τ z : ℍ) : ℂ :=
  -(DeltaRef z * Work.Kernels.jInvariantFun τ) * Work.Asymptotics.K24F.Th0 τ z

/-- The deviation part of `K24F.Sm5`. -/
def dSm5 (τ z : ℍ) : ℂ :=
  -(dDelta z * Work.Kernels.jInvariantFun τ) * Work.Asymptotics.K24F.Th0 τ z

/-- **The `Sm5`-split**: `Sm5 = Sm5Ref + dSm5`, exactly. -/
lemma Sm5_eq_ref_add (τ z : ℍ) :
    Work.Asymptotics.K24F.Sm5 τ z = Sm5Ref τ z + dSm5 τ z := by
  have hD := DeltaFun_ref_add z
  simp only [Work.Asymptotics.K24F.Sm5, Sm5Ref, dSm5]
  rw [hD]
  ring

end

end Work.Asymptotics.KhatE1Core
