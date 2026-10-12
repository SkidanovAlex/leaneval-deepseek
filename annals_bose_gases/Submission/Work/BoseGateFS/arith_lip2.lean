import Mathlib.Data.Real.Basic
import Submission.Work.BoseGateFS.arith_lip_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.arith_lip2`

The specialization of `Work.BoseGateFS.arith_lip_const` to `s = KH * a`: the
letter-Lipschitz arithmetic which dominates the two `192/2048` summands by the
single constant `10 ^ 12 (Cw + Cg + Cτ + 1) ^ 4 (1 + 1/cτ) ^ 4 (1 + 1/a) ^ 4`
times `(μ a³ KH²) * (KH a)`.

The general statement is proved in `arith_lip_const`, which carries `s` as a
parameter together with the identification `hsa : s = KH * a` (because it is
consumed there in the `s`-shaped form); the present lemma is that statement at
`s := KH * a`, with the identification `rfl`.
-/

namespace Work.BoseGateFS

theorem arith_lip2 {Cw Cg Cτ cτ ρ μ a KH : ℝ}
    (hCw : 0 ≤ Cw) (hCg : 0 ≤ Cg) (hCτ : 0 ≤ Cτ) (hcτ : 0 < cτ)
    (ha : 0 < a) (hKH : 0 < KH) (hμ : 0 ≤ μ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 3 * μ / 2)
    (hs : 1 ≤ KH * a) :
    192 * ρ * Cg * a * (KH * a) ^ 2 + 2048 * ρ * Cw * a * Cτ * (KH * a) ^ 3 ≤
      10 ^ 12 * (Cw + Cg + Cτ + 1) ^ 4 * (1 + 1 / cτ) ^ 4 * (1 + 1 / a) ^ 4
        * (μ * a ^ 3 * KH ^ 2) * (KH * a) :=
  arith_lip_const (s := KH * a) hCw hCg hCτ hcτ ha hμ hρ0 hρ hs rfl

end Work.BoseGateFS
