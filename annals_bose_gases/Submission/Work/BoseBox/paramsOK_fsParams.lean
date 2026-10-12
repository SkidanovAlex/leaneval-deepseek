import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.paramsOK_fsParams` — FS's parameter block satisfies every condition

The whole of `sec:params` of Fournais–Solovej reduces to exponent arithmetic for the
concrete choice `fsParams t` (`t = μa³`): every parameter of the block is the monomial
`fsXp t c = t^{c/323}` (`s = X`, `d = X⁶`, `ε_T = X^{23/4}`, `K_ℓ = X^{-3/2}`,
`K_B = X^{-6}`, `K_M = X^{-1}`, `K_H = X^{-8/3}`), and each of FS's conditions is a
comparison `f ≪ g` between two such monomials.

The content of this file:

* `rpow_eq_fsXp`, `fsXp_rpow'`, `fsXp_mul'` — the monomial calculus (products and
  powers of `fsXp` are again `fsXp`), used to normalise every side of every condition
  to a single `fsXp t a`;
* `muchLe_of_fsXp`, `muchLe_one_of_fsXp`, `muchLe_of_one_fsXp` — the single slack
  `ε = 1/2000 ≤ slack = 1/40` is enough for *all* of FS's `≪` conditions, so
  `muchLe_of_exp` reduces each of them to the exponent inequality
  `b + 323ε ≤ a` (`by norm_num`);
* `fsXp_flip` — the antitone comparison `fsXp t a ≤ fsXp t b` for `b ≤ a`, used for the
  three *outright* (non-`≪`) inequalities of `con:eTdK`;
* the `mon_*` normalisations, one per condition, and then the theorem.

Note the sharp arithmetic: the smallest exponent gap among the `≪`-conditions is
`1/4` (`con:rough1`), giving `ε ≤ 1/1292`; `1/2000` is comfortably below that.
-/

noncomputable section

set_option linter.unusedSimpArgs false

open scoped Real Topology BigOperators

namespace Work.BoseBox

/-- A plain power of `t` is a power of `X = (μa³)^{1/323}`: `t^c = X^{323c}`. -/
private lemma rpow_eq_fsXp {t c : ℝ} (ht : 0 ≤ t) : t ^ c = fsXp t (323 * c) := by
  conv_lhs => rw [delta_eq_fsXp ht]
  rw [fsXp_rpow ht]

/-- `(fsXp t c)^r = fsXp t (c·r)`, in the form used by `simp only`. -/
private lemma fsXp_rpow' {t c r : ℝ} (ht : 0 < t) : (fsXp t c) ^ r = fsXp t (c * r) :=
  fsXp_rpow ht.le c r

/-- `fsXp t c * fsXp t e = fsXp t (c+e)`, in the form used by `simp only`. -/
private lemma fsXp_mul' {t c e : ℝ} (ht : 0 < t) : fsXp t c * fsXp t e = fsXp t (c + e) :=
  fsXp_mul ht c e

/-- The master `≪`-reduction: a comparison of two `X`-powers whose exponents differ by
at least `323·(1/2000)` is a `MuchLe` with the fixed slack `ε = 1/2000`. -/
private lemma muchLe_of_fsXp {t a b : ℝ} (h0 : 0 < t) (h1 : t ≤ 1)
    (h : b + 323 * (1 / 2000) ≤ a) : MuchLe (fsXp t a) (fsXp t b) t := by
  refine ⟨1 / 2000, by norm_num, by norm_num [slack], ?_⟩
  exact muchLe_of_exp h0 h1 (by norm_num) (by norm_num [slack]) h

/-- `X^a ≪ 1` (the right-hand side `1` being `X^0`). -/
private lemma muchLe_one_of_fsXp {t a : ℝ} (h0 : 0 < t) (h1 : t ≤ 1)
    (h : 323 * (1 / 2000) ≤ a) : MuchLe (fsXp t a) 1 t := by
  rw [show (1 : ℝ) = fsXp t 0 by simp [fsXp]]
  exact muchLe_of_fsXp h0 h1 (by linarith)

/-- `1 ≪ X^b` (the left-hand side `1` being `X^0`); holds as soon as `b ≤ 0`. -/
private lemma muchLe_of_one_fsXp {t b : ℝ} (h0 : 0 < t) (h1 : t ≤ 1)
    (h : b + 323 * (1 / 2000) ≤ 0) : MuchLe 1 (fsXp t b) t := by
  rw [show (1 : ℝ) = fsXp t 0 by simp [fsXp]]
  exact muchLe_of_fsXp h0 h1 h

/-- The antitone comparison of two `X`-powers, for the outright inequalities. -/
private lemma fsXp_flip {t a b : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (h : b ≤ a) :
    fsXp t a ≤ fsXp t b :=
  fsXp_le_fsXp h0 h1 h

/-! ## The monomial normalisations, one per condition of `sec:params`

Each `mon_*` lemma states that one side of one of FS's conditions is the single
`X`-power `fsXp t <exponent>`; the tactics normalise the powers of `X` with
`fsXp_rpow'`/`fsXp_mul'`, the bare powers of `t` with `rpow_eq_fsXp`, and the natural
powers with `Real.rpow_natCast`, after which `norm_num` is pure exponent arithmetic. -/

private lemma mon_d5s {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).d ^ (-(5 : ℝ)) * (fsParams t).s ^ (((fsParams t).M : ℝ) + 1) =
      fsXp t 19 := by
  dsimp only [fsParams, mValue]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_dKl_sq {t : ℝ} (ht0 : 0 < t) :
    ((fsParams t).d * (fsParams t).Kl) ^ 2 = fsXp t 9 := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_eT_Kl {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).eT * (fsParams t).Kl ^ (-(2 : ℝ)) = fsXp t (35 / 4) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_eT {t : ℝ} : (fsParams t).eT = fsXp t (23 / 4) := rfl

private lemma mon_sdKl {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).s * (fsParams t).d * (fsParams t).Kl = fsXp t (11 / 2) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_sKl {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).s * (fsParams t).Kl = fsXp t (-(1 / 2)) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_KB_inv {t : ℝ} (ht0 : 0 < t) : (fsParams t).KB ^ (-(1 : ℝ)) = fsXp t 6 := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_KB {t : ℝ} : (fsParams t).KB = fsXp t (-6) := rfl

private lemma mon_KB3_Kl2 {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).KB ^ 3 * (fsParams t).Kl ^ 2 = fsXp t (-21) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_KB3_Kl5 {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).KB ^ 3 * (fsParams t).Kl ^ 5 = fsXp t (-(51 / 2)) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_KMt {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).KM * t ^ (-(1 / 4 : ℝ)) = fsXp t (-(327 / 4)) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_Kl3t {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).Kl ^ 3 * t ^ (-(1 / 2 : ℝ)) = fsXp t (-166) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_KM_Kl4 {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).KM * (fsParams t).Kl ^ 4 = fsXp t (-7) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_KH3 {t : ℝ} (ht0 : 0 < t) : (fsParams t).KH ^ 3 = fsXp t (-8) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_d_pow {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).d ^ (2 * ((fsParams t).M : ℝ) - 2) = fsXp t 564 := by
  dsimp only [fsParams, mValue]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_Kl_d2_inv_KH {t : ℝ} (ht0 : 0 < t) :
    ((fsParams t).Kl * (fsParams t).d ^ 2) ^ (-(1 : ℝ)) * (fsParams t).KH =
      fsXp t (-(79 / 6)) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_rough1 {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).KM * (fsParams t).Kl ^ 5 * (fsParams t).d ^ (-(12 : ℝ)) *
      t ^ (1 / 4 : ℝ) = fsXp t (1 / 4) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_rough2 {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).KM ^ 3 * (fsParams t).KH ^ 4 * (fsParams t).Kl ^ (-(1 : ℝ)) *
      (fsParams t).d ^ (-(12 : ℝ)) * t ^ (13 / 12 : ℝ) = fsXp t (1063 / 4) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_bogham {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).KM * (fsParams t).Kl ^ (-(3 / 2 : ℝ)) *
      ((fsParams t).Kl * (fsParams t).KH * t ^ (1 / 12 : ℝ)) ^ (((fsParams t).M : ℝ) - 5) =
      fsXp t (1959 / 2) := by
  dsimp only [fsParams, mValue]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_KellKM {t : ℝ} (ht0 : 0 < t) :
    ((fsParams t).Kl * (fsParams t).d ^ 2) ^ (-(3 : ℝ)) * (fsParams t).KM =
      fsXp t (-(65 / 2)) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_KellKH {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).Kl ^ 2 * (fsParams t).KH ^ 4 * (fsParams t).d ^ (-(6 : ℝ)) =
      fsXp t (-(149 / 3)) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_Q3error1 {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).KM * (fsParams t).Kl ^ (-(3 : ℝ)) * (fsParams t).KH ^ (-(2 : ℝ)) =
      fsXp t (53 / 6) := by
  dsimp only [fsParams]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

private lemma mon_Q3error3 {t : ℝ} (ht0 : 0 < t) :
    (fsParams t).KM * (fsParams t).Kl ^ (-(3 : ℝ)) * (fsParams t).d ^ (-(12 : ℝ)) *
      ((fsParams t).Kl ^ (-(2 : ℝ)) * (fsParams t).KH ^ 2 * t ^ (1 / 6 : ℝ)) ^
        (((fsParams t).M : ℝ) - 1) = fsXp t 2352 := by
  dsimp only [fsParams, mValue]
  simp only [fsXp_rpow' ht0, fsXp_mul' ht0, rpow_eq_fsXp ht0.le, ← Real.rpow_natCast]
  norm_num

/-! ## The theorem -/

/-- **FS's parameter choice satisfies every condition of `sec:params`** for small
diluteness `t = μa³`: all conditions hold for `0 < t ≤ 1` (hence eventually near
`0⁺`), with the single slack `ε = 1/2000` in every `≪`. -/
theorem paramsOK_fsParams :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), Work.BoseBox.ParamsOK (Work.BoseBox.fsParams t) t := by
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := le_of_lt ht.2
  refine
    { bsmall := ?_, d5s := ?_, eTdK := ?_, sKell := ?_, sdKellKB := ?_, KB := ?_, KBKell := ?_,
      KBellKM := ?_, Mlln := ?_, KMKellKH := ?_, KellKLd := ?_, KLKH := ?_, rough1 := ?_,
      rough2 := ?_, boghamerror := ?_, KellKM := ?_, KellKH := ?_, Q3error1 := ?_,
      Q3error3 := ?_ }
  · -- `con:b`: `b = bValue` is *the* universal coefficient.
    unfold Con_b
    exact le_refl _
  · -- `con:d5s`: `d^{-5}s^{49} = X^{19} ≪ 1`.
    unfold Con_d5s
    rw [mon_d5s ht0]
    exact muchLe_one_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:eTdK`: `X^{9} ≤ X^{35/4} ≤ X^{23/4} ≤ X^{11/2}`.
    unfold Con_eTdK
    refine ⟨?_, ?_, ?_⟩
    · rw [mon_dKl_sq ht0, mon_eT_Kl ht0]
      exact fsXp_flip ht0 ht1 (by norm_num)
    · rw [mon_eT_Kl ht0, mon_eT]
      exact fsXp_flip ht0 ht1 (by norm_num)
    · rw [mon_eT, mon_sdKl ht0]
      exact fsXp_flip ht0 ht1 (by norm_num)
  · -- `con:sKell`: `1 ≪ sK_ℓ = X^{-1/2}`.
    unfold Con_sKell
    rw [mon_sKl ht0]
    exact muchLe_of_one_fsXp ht0 ht1 (by norm_num)
  · -- `con:sdKellKB`: `K_B^{-1} = X^6 ≪ X^{11/2} = s d K_ℓ`.
    unfold Con_sdKellKB
    rw [mon_KB_inv ht0, mon_sdKl ht0]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:KB`: `K_B = X^{-6} ≪ t^{-1/6} = X^{-323/6}`.
    unfold Con_KB
    rw [mon_KB, rpow_eq_fsXp ht0.le]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:KBKell`: `K_B^3K_ℓ^2 = X^{-21} ≪ t^{-1/4} = X^{-323/4}`.
    unfold Con_KBKell
    rw [mon_KB3_Kl2 ht0, rpow_eq_fsXp ht0.le]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:KBellKM`: `K_B^3K_ℓ^5 = X^{-51/2} ≪ K_M t^{-1/4} = X^{-327/4}`.
    unfold Con_KBellKM
    rw [mon_KB3_Kl5 ht0, mon_KMt ht0]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:M<<n`: `K_M t^{-1/4} = X^{-327/4} ≪ K_ℓ^3 t^{-1/2} = X^{-166}`.
    unfold Con_Mlln
    rw [mon_KMt ht0, mon_Kl3t ht0]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:KMKellKH`: `K_MK_ℓ^4 = X^{-7} ≪ K_H^3 = X^{-8}`.
    unfold Con_KMKellKH
    rw [mon_KM_Kl4 ht0, mon_KH3 ht0]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:KellKLd`: `d^{2M-2} = X^{564} ≪ t^{1/2} = X^{323/2}`.
    unfold Con_KellKLd
    rw [mon_d_pow ht0, rpow_eq_fsXp ht0.le]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:KLKH`: `(K_ℓd^2)^{-1}K_H = X^{-79/6} ≪ t^{-1/12} = X^{-323/12}`.
    unfold Con_KLKH
    rw [mon_Kl_d2_inv_KH ht0, rpow_eq_fsXp ht0.le]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:rough1`: `K_MK_ℓ^5d^{-12}t^{1/4} = X^{1/4} ≪ 1`.
    unfold Con_rough1
    rw [mon_rough1 ht0]
    exact muchLe_one_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:rough2`: `K_M^3K_H^4K_ℓ^{-1}d^{-12}t^{13/12} = X^{1063/4} ≪ 1`.
    unfold Con_rough2
    rw [mon_rough2 ht0]
    exact muchLe_one_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:boghamerror`: `K_MK_ℓ^{-3/2}(K_ℓK_Ht^{1/12})^{43} = X^{1959/2} ≪ t^{1/2} = X^{323/2}`.
    unfold Con_boghamerror
    rw [mon_bogham ht0, rpow_eq_fsXp ht0.le]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:KellKM`: `(K_ℓd^2)^{-3}K_M = X^{-65/2} ≪ t^{-1/4} = X^{-323/4}`.
    unfold Con_KellKM
    rw [mon_KellKM ht0, rpow_eq_fsXp ht0.le]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:KellKH`: `K_ℓ^2K_H^4d^{-6} = X^{-149/3} ≪ t^{-1/3} = X^{-323/3}`.
    unfold Con_KellKH
    rw [mon_KellKH ht0, rpow_eq_fsXp ht0.le]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:Q3error1`: `K_MK_ℓ^{-3}K_H^{-2} = X^{53/6} ≪ t^{-1/12} = X^{-323/12}`.
    unfold Con_Q3error1
    rw [mon_Q3error1 ht0, rpow_eq_fsXp ht0.le]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)
  · -- `con:Q3error3`: `K_MK_ℓ^{-3}d^{-12}(K_ℓ^{-2}K_H^2t^{1/6})^{47} = X^{2352} ≪ t^{3/4} = X^{969/4}`.
    unfold Con_Q3error3
    rw [mon_Q3error3 ht0, rpow_eq_fsXp ht0.le]
    exact muchLe_of_fsXp ht0 ht1 (by norm_num)

end Work.BoseBox
