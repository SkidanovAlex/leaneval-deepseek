import Mathlib

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

/-- The standard additive character of `ZMod Q` agrees, at an integer frequency `n`,
with the `n`-th Fourier mode of the additive circle evaluated at `toAddCircle i`. -/
theorem StdAddCharFourier {Q : ℕ} [NeZero Q] (i : ZMod Q) (n : ℤ) :
    ZMod.stdAddChar (i * (n : ZMod Q)) = fourier n (ZMod.toAddCircle i : AddCircle (1 : ℝ)) := by
  have h : ZMod.toCircle (i * (n : ZMod Q))
      = AddCircle.toCircle (n • (ZMod.toAddCircle i : AddCircle (1 : ℝ))) := by
    rw [show i * (n : ZMod Q) = n • i by rw [mul_comm, zsmul_eq_mul],
      AddChar.map_zsmul_eq_zpow, AddCircle.toCircle_zsmul]
    rfl
  rw [ZMod.stdAddChar_apply, fourier_apply]
  exact congrArg (fun z : Circle => (z : ℂ)) h

end Work.KMTPlan.A6
