import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7A.Defs
import Submission.Work.BoseB7A.smallness_conj8
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.arith_aKH_div_dsell_le`

At FS's parameter point (`Work.BoseB7.FSParamsView E`, diluteness `t = μa³`,
`X = (μa³)^{1/323}`) the ratio

  `a·K_H/(d·s·ℓ)`

of the smallness hypotheses of §10 is a *pure monomial* in `X`: the scattering
length cancels against the healing length, `a/ℓ = X^{163}`
(`Work.BoseB7A.aScat_div_ell`, in `smallness_conj8`), and `K_H = X^{-549/4}`,
`d = X⁶`, `s = X`, so

  `a·K_H/(d·s·ℓ) = X^{163}·X^{-549/4}·X^{-7} = X^{75/4}`.

Hence it is `≤ 1/8` as soon as `X ≤ 1/2`, and `X = (μa³)^{1/323} ≤ (1/2)^{323·(1/323)} = 1/2`
whenever `t = μa³ ≤ (1/2)^{323}`:

  `a·K_H/(d·s·ℓ) = X^{75/4} ≤ (1/2)^{75/4} ≤ (1/2)³ = 1/8`.

(In particular the threshold `t ≤ 2^{-323}` is very far from optimal: the exact
threshold is `t ≤ 2^{-323}·... `, i.e. `X ≤ 2^{-4/75}`; only `X ≤ 1/2` is used,
which is the crude form recorded in the interface.)
-/

noncomputable section

namespace Work.BoseB7A

open Work.BoseB7 Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-- **The closed form of the ratio**: at FS's parameter point
`a·K_H/(d·s·ℓ) = X^{75/4}`, `X = fsXp hv.t 1 = (μa³)^{1/323}`. -/
lemma aKH_div_dsell_eq_fsXp (E : Q3Env Mode) (hv : FSParamsView E) :
    E.aScat * E.KH / (E.d * E.s * E.ell) = fsXp hv.t (75 / 4) := by
  have ht : 0 < hv.t := hv.t_pos
  -- `K_H/(d·s) = X^{-549/4 - 6 - 1} = X^{-577/4}`
  have hKHds : E.KH / (E.d * E.s) = fsXp hv.t (-(577 / 4)) := by
    rw [KH_val E hv, d_val E hv, hv.s_eq, div_eq_mul_inv, fsXp_mul ht, fsXp_inv ht,
      fsXp_mul ht]
    congr 1
    norm_num
  -- `a·K_H/(d·s·ℓ) = (a/ℓ)·(K_H/(d·s))`
  have hfac : E.aScat * E.KH / (E.d * E.s * E.ell)
      = (E.aScat / E.ell) * (E.KH / (E.d * E.s)) := by
    rw [div_mul_div_comm, mul_comm (E.d * E.s) E.ell]
  rw [hfac, aScat_div_ell E hv, hKHds, fsXp_mul ht]
  congr 1
  norm_num

theorem arith_aKH_div_dsell_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E)
    (ht : hv.t ≤ (1 / 2) ^ 323) :
    E.aScat * E.KH / (E.d * E.s * E.ell) ≤ 1 / 8 := by
  have ht0 : 0 < hv.t := hv.t_pos
  rw [aKH_div_dsell_eq_fsXp E hv]
  -- `X = fsXp hv.t 1 ≤ 1/2`
  have hX : fsXp hv.t 1 ≤ 1 / 2 := by
    have h1 : fsXp hv.t 1 ≤ fsXp ((1 / 2 : ℝ) ^ 323) 1 := by
      simp only [fsXp]
      exact Real.rpow_le_rpow ht0.le ht (by norm_num)
    have h2 : fsXp ((1 / 2 : ℝ) ^ 323) 1 = 1 / 2 := by
      simp only [fsXp]
      rw [← Real.rpow_natCast (1 / 2 : ℝ) 323,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    linarith [h1, h2]
  -- `X^{75/4} = fsXp hv.t (75/4)`
  have hXpow : fsXp hv.t (75 / 4) = (fsXp hv.t 1) ^ (75 / 4 : ℝ) := by
    rw [fsXp_rpow ht0.le]
    congr 1
    ring
  rw [hXpow]
  calc (fsXp hv.t 1) ^ (75 / 4 : ℝ) ≤ (1 / 2) ^ (75 / 4 : ℝ) :=
        Real.rpow_le_rpow (fsXp_pos ht0).le hX (by norm_num)
    _ ≤ (1 / 2 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
    _ = 1 / 8 := by norm_num

end Work.BoseB7A
