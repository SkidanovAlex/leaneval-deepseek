import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.MainP.basic
import Submission.Work.MainP.TparFacts
import Submission.Work.MainP.AparFacts
import Submission.Work.MainP.PolyFacts
import Submission.Work.MainP.powTwoParams
import Submission.Work.MainP.resParams
import Submission.Work.MainP.lmaxPar
import Submission.Work.MainP.prodWindow

/-! Paper 5.1–5.3 parameter inequalities for all large `n` (pure arithmetic).

Assembly of `HvdH.MainParamsProp` from the pieces proved in the sibling modules:
* `basic.lean` : `bpar` facts and the threshold-free `eventual_bpar_ge`;
* `TparFacts` : `4n ≤ T·b < 8n`, `T < 2^(b+3)`, `r^d` bounds, `kT ≤ b+2`, `kT < p`;
* `AparFacts` : `α⁴ ≥ 12d²b ≥ 4dp`, `α² < p`, `2dα²+13 < b`;
* `PolyFacts` : `3dp² < T`, `3rp < n`, `K·p < n`;
* `powTwoParams`, `resParams`, `lmaxPar`, `prodWindow` : the structural conjuncts.

The threshold `n₂` is *not* written down (it is astronomically large): we produce it with
`Filter.eventually_atTop` from the two eventual facts `2^61 ≤ bpar n` and `(6K+1)^20 ≤ n`. -/

namespace Work.MainP

theorem mainParams : HvdH.MainParamsProp := by
  intro K
  have hb0 : ∀ᶠ n in Filter.atTop, 2 ^ 61 ≤ HvdH.bpar n := eventual_bpar_ge (2 ^ 61)
  have hK0 : ∀ᶠ n in Filter.atTop, (6 * K + 1) ^ 20 ≤ n :=
    Filter.eventually_atTop.mpr ⟨(6 * K + 1) ^ 20, fun _ hn => hn⟩
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.mp (hb0.and hK0)
  refine ⟨n₂, fun n ts ss hn hOK => ?_⟩
  obtain ⟨hb, hK⟩ := hn₂ n hn
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩ := TparFacts n hb
  obtain ⟨a1, a2, a3, a4, a5⟩ := AparFacts n hb
  have hb1 : 1 ≤ HvdH.bpar n := by omega
  have h100 : 100 ≤ HvdH.ppar n := by rw [HvdH.ppar]; omega
  have hTp : HvdH.Tpar n < 2 ^ HvdH.ppar n :=
    Nat.pow_lt_pow_right one_lt_two t8
  obtain ⟨p1, p2, p3⟩ := PolyFacts K n hb t1 t9 hK
  obtain ⟨w1, w2, w3⟩ := prodWindow n ts ss hOK t1 hb1
  exact ⟨powTwoParams n ts ss hOK (by omega) hTp h100,
    resParams n ts ss hOK h100 a5 a3 a2 (by omega) t7 hTp,
    lmaxPar n ts ss hOK t10,
    p2, p3, p1, a4, w2, w1, w3, t2, le_two_pow_bpar n, hb1, h100⟩

end Work.MainP
