import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB7A.eta_mul_le
import Submission.Work.BoseB7A.smallness_conj8
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.arith_KH_a_div_ell_pow_le_eta` — `(aK_H/ℓ)^{2M̃_decay} ≤ η`

At FS's §10 parameter point (`Work.BoseB7.FSParamsView E`) every scalar of the
`Q3Env` is a monomial `fsXp t c = (μa³)^{c/323}` in the diluteness `t = μa³`
(`Work.BoseB7.FSParamsVals`), and the box side is the healing length
`ℓ = K_ℓ(μa)^{-1/2}` (FS `eq:def_ell`).  With

* `a/ℓ = (μa³)^{1/2}/K_ℓ = X^{163}` (`Work.BoseB7A.aScat_div_ell`),
* `K_H = X^{-549/4}` (`Work.BoseB7.KH_val`),

the quotient of the statement is the pure monomial

  `a K_H / ℓ = X^{163 - 549/4} = X^{103/4}`  (`aKH_div_ell_eq_fsXp`),

so, since `2·decayOrder = 52` (`Work.BoseK15.decayOrder = 26`),

  `(a K_H/ℓ)^{52} = X^{1339}`.

On the other side (`Work.BoseB7A.eta_eq`), with `K_ℓ = X^{-3/2}` and
`𝓁 = (μa³)K_H² = X^{97/2}` (FS `eq:DefLille`, `Work.BoseB7.lille_val`) and
`M̃ = ⌊M/2⌋ = 24` (`M = 48`),

  `η = (K_ℓ^{-2}𝓁)^{M̃} = (X^{103/2})^{24} = X^{1236}`.

The statement is therefore the single monotone comparison
`X^{1339} ≤ X^{1236}`, which is `Work.BoseBox.fsXp_le_fsXp` since `X ≤ 1`
(i.e. `t ≤ 1` is FS's diluteness range and `1236 ≤ 1339`).

This is the `(μa³)-`smallness row that lets the fixed-`n` estimates of the
small-box chapter absorb the `aK_H/ℓ` factors into the decay gain `η` of `χ̂` on
`P_H^q` (FS `lem:DecaychiHat` / `eq:DecayPH`).
-/

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A Work.BoseBox

/-- **The quotient `a·K_H/ℓ` at FS's parameter point**: it is the pure monomial
`X^{103/4}` with `X = (μa³)^{1/323}`.  (`a/ℓ = X^{163}` by
`Work.BoseB7A.aScat_div_ell`, `K_H = X^{-549/4}` by `Work.BoseB7.KH_val`, and
`163 - 549/4 = 103/4`.) -/
lemma aKH_div_ell_eq_fsXp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) :
    E.aScat * E.KH / E.ell = Work.BoseBox.fsXp hv.t (103 / 4) := by
  have ht : 0 < hv.t := hv.t_pos
  rw [show E.aScat * E.KH / E.ell = (E.aScat / E.ell) * E.KH by ring]
  rw [aScat_div_ell E hv, KH_val E hv, fsXp_mul ht]
  congr 1
  norm_num

theorem arith_KH_a_div_ell_pow_le_eta {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E) :
    (E.aScat * E.KH / E.ell) ^ (2 * Work.BoseK15.decayOrder) ≤ Work.BoseB7A.eta E := by
  have ht : 0 < hv.t := hv.t_pos
  -- the left-hand side is `X^{1339}`
  have hpow : (E.aScat * E.KH / E.ell) ^ (2 * Work.BoseK15.decayOrder) =
      Work.BoseBox.fsXp hv.t 1339 := by
    rw [aKH_div_ell_eq_fsXp E hv]
    rw [show (2 * Work.BoseK15.decayOrder) = 52 by norm_num [Work.BoseK15.decayOrder]]
    rw [fsXp_pow ht.le]
    congr 1
    norm_num
  -- the right-hand side is `X^{1236}`
  rw [hpow, eta_eq E hv]
  exact fsXp_le_fsXp ht hv.t_le_one (by norm_num)

end Work.BoseK15
