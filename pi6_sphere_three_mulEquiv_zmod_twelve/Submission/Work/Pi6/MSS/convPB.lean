import Mathlib
import Submission.Work.Pi6.MSS.Pages
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

/-- In the stable range (`t + 1 ≤ m`, i.e. `m > t`) the lower filtration index `t + 1 - m`
of `B_m^t` is `≤ 0`, hence `0`, and `F^0 = ⊤`: the source of the bounding map is the whole
of `C^{n-1}`, so `B_m^t = F^t C^n ∩ im d^{n-1}`. -/
theorem convPB (𝕜 : Type) [CommRing 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜) (m t n : ℕ)
    (hm : t + 1 ≤ m) :
    Work.Pi6.MSS.pB 𝕜 W m t n = W.F t n ⊓ (W.dPrev n).range := by
  have h0 : t + 1 - m = 0 := by omega
  rw [pB, h0, W.F_zero, Submodule.map_top]

end Work.Pi6.MSS
