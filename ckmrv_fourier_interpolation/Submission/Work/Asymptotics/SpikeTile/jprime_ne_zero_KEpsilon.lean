import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.KPlus8FunnelAux
import Submission.Work.Asymptotics.SpikeCircle.divisorLowerDisc
import Submission.Work.Asymptotics.KfunClear_vanish_of_phiPair

namespace Work.Asymptotics.SpikeTile

/-- **`j'` does not vanish on the cusp-`0` neighbourhood `E = KEpsilon`.**

`E` is the part of the `Γ(2)`-fundamental domain `𝒟` on which `Im (S • w) ≥ 2`, i.e. the region
`{|w - i/4| ≤ 1/4} ∩ 𝒟`, a neighbourhood of the cusp `0`.  Every such `w` is `S`-equivalent to a
point `S • w` of height `≥ 2`; at height `≥ 2` the Eisenstein series `E₄` and `E₆` do not vanish
(`‖E₄ - 1‖ ≤ 1/2` from the `q`-expansion, and `E₆ ≠ 0` from `Δ · j = E₄³`), and the weight-`4`,
resp. weight-`6`, transformation law `E₄(S z) = z⁴E₄(z)`, `E₆(S z) = z⁶E₆(z)` transports this
back to `w`.  Since `j' = -2πi E₄²E₆/Δ` and `Δ ≠ 0` on `ℍ`
(`Work.Residues.jprime_ne_zero_iff`), the claim follows. -/
theorem jprime_ne_zero_KEpsilon {w : UpperHalfPlane} (hw : w ∈ Work.Asymptotics.KEpsilon) :
    Work.Residues.jprime w ≠ 0 := by
  rw [Work.Residues.jprime_ne_zero_iff]
  -- `S • w` has height at least `2`.
  obtain ⟨-, h2⟩ := Work.Asymptotics.S_smul_mem_funnel hw
  -- Non-vanishing of `E₄` and `E₆` at height `≥ 2`.
  have hE4S : Work.Kernels.E4Fun (ModularGroup.S • w) ≠ 0 := by
    intro h0
    have hle := Work.FunnelNumerics.E4_sub_one_le (ModularGroup.S • w) h2
    rw [h0, zero_sub, norm_neg, norm_one] at hle
    norm_num at hle
  have hE6S : Work.Kernels.E6Fun (ModularGroup.S • w) ≠ 0 :=
    Work.Asymptotics.SpikeCircle.E6Fun_ne_zero_im (ModularGroup.S • w) h2
  -- Transport back along `S` (weights `4` and `6`).
  refine mul_ne_zero ?_ ?_
  · intro h
    exact hE4S (by rw [Work.Residues.E4Fun_S_smul, h, mul_zero])
  · intro h
    exact hE6S (by rw [Work.Residues.E6Fun_S_smul, h, mul_zero])

end Work.Asymptotics.SpikeTile
