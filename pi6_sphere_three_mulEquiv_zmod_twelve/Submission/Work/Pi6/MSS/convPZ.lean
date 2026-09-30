import Mathlib
import Submission.Work.Pi6.MSS.Pages
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The cycles above the `n`-th column: `Z_m^t = F^t C^n ∩ ker d`

For `W : CohFilt 𝕜` and `n + 2 ≤ t + m` the filtration step `F^{t+m}` is zero in cohomological
degree `n+1` (`CohFilt.F_top`, using that the filtration is decreasing), so the condition defining
the cycles,

`Z_m^t = F^t C^n ∩ d^{-1}(F^{t+m} C^{n+1})`  (`Work.Pi6.MSS.pZ`),

is vacuous: the cycles are exactly the elements of `F^t C^n` killed by `d`.  This is the form in
which the cycles enter the identification of the `E_∞` term of the total degree `n` (see
`Submission/Work/Pi6/MSS/convPage.lean`), where the relevant pages are `E_{n+2}` with `m = n+2` and
`t ≤ n`, hence `t + m ≥ n + 2`.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CohFilt

variable {𝕜 : Type} [CommRing 𝕜] (W : CohFilt 𝕜)

/-- Above the cohomological degree the filtration vanishes: `F^s C^n = ⊥` for `n + 1 ≤ s`.
(For `s = n + 1` this is the field `F_top` of `CohFilt`, and the filtration is decreasing.) -/
theorem F_eq_bot_of_lt (n s : ℕ) (h : n + 1 ≤ s) : W.F s n = ⊥ := by
  have hanti : Antitone (fun k => W.F k n) :=
    antitone_nat_of_succ_le (fun k => W.F_mono k n)
  have hle : W.F s n ≤ W.F (n + 1) n := hanti h
  rw [W.F_top n] at hle
  exact le_bot_iff.mp hle

/-- If `F^{t+m}` already vanishes in cohomological degree `n+1`, the cycles `Z_m^t` in degree `n`
are the intersection of `F^t C^n` with the kernel of the coboundary. -/
theorem pZ_eq_inf_ker (m t n : ℕ) (h : W.F (t + m) (n+1) = ⊥) :
    pZ 𝕜 W m t n = W.F t n ⊓ (W.d n).ker := by
  unfold pZ
  rw [h, Submodule.comap_bot]

end CohFilt

/-- `Z_m^t` in degree `n` is `F^t C^n ∩ ker d` as soon as `n + 2 ≤ t + m`, since then `F^{t+m}`
is zero in degree `n+1`. -/
theorem convPZ (𝕜 : Type) [CommRing 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜) (m t n : ℕ)
    (hm : n + 2 ≤ t + m) :
    Work.Pi6.MSS.pZ 𝕜 W m t n = W.F t n ⊓ (W.d n).ker :=
  CohFilt.pZ_eq_inf_ker (𝕜 := 𝕜) (W := W) m t n
    (CohFilt.F_eq_bot_of_lt (𝕜 := 𝕜) (W := W) (n+1) (t+m) (by omega))

end

end Work.Pi6.MSS
