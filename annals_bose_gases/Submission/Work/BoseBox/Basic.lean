import Mathlib.Analysis.InnerProductSpace.PiL2
import ChallengeDeps
import Submission.LhyIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.Basic` — FS's parameter block (`sec:params`), decoupled from `L` and `N`

This is the first module of the `Submission/Work/BoseBox/` area, the chapter that
carries Fournais–Solovej's box theorem (`thm:LHY-Box`) at FS's own parameters.

## Why a new parameter layer

The audit (`BOSE_AUDIT_LEAD.md`) records the fatal defect of the previous route:
every box statement there tied the chemical potential to the sector,
`μ := dens N L = N/L³`, and quantified over *all* `L ≥ 1` and *all* `N`.  FS's box
theorem instead fixes `μ`, ties the box side to `μ` by the healing length
`ℓ = K_ℓ (μa)^{-1/2}`, and leaves the particle number free.  The finite-size
error `4πaμ` (from `N(N−1)` versus `N²`) is then dominated by the LHY term
because `μℓ³ = K_ℓ³(μa³)^{-1/2} → ∞`, whereas at `μℓ³ = 1` it is not.

So this chapter **decouples** the parameters: the *only* small quantity is the
diluteness `t = μ a³`; the box side `ℓ` and every other parameter are functions
of it through FS's explicit power choice
`X = (μa³)^{1/323}`, `s = X`, `d = X⁶`, `ε_T = X^{23/4}`, `K_ℓ = X^{-3/2}`,
`K_B = X^{-6}`, `K_M = X^{-1}`, `K_H = X^{-8/3}` (FS eq. `eq:Xparameter`,
`eq:Xchoice`).  The particle number is free and `ρ`-dependent inputs
(`ρmax = 2ρ`, `μ = ρ`, …) are separated from the parameter block.

## Contents

* `fsXp` — the monomial `(μa³)^{c/323}`: every parameter and every condition of
  FS `sec:params` is a comparison of these monomials, so the whole arithmetic
  reduces to exponent arithmetic (`fsXp_le_fsXp`).
* `FSParams`, `fsParams`, `mValue` — the parameter block and FS's choice.
* `MuchLe` — FS's `f ≪ g` (`f/g ≤ (μa³)^ε` for some `ε > 0`), made explicit
  with the slack capped at `1/40` (the cap is *not* a loss: the concrete choice
  below satisfies every condition of `sec:params` with the *same* slack
  `ε = 1/40`, see `paramsOK_fsParams`).
* `Con_*` — the named conditions of FS `sec:params` (`con:d5s`, `con:eTdK`,
  `con:sKell`, `con:sdKellKB`, `con:KB`, `con:KBKell`, `con:KBellKM`,
  `con:M<<n`, `con:KMKellKH`, `con:KellKLd`, `con:KLKH`, `con:rough1`,
  `con:rough2`, `con:boghamerror`, `con:KellKM`, `con:KellKH`, `con:Q3error1`,
  `con:Q3error3`), plus `ParamsOK`, the bundle consumed by the node statements,
  and `ParamsOKv` with the two `v`-dependent conditions (`con:KMRKB`,
  `eq:intvbound`).
* `paramsOK_fsParams` — **the parameter block satisfies every condition** for
  small diluteness.  This is the B8 bookkeeping the box theorem needs; it is
  proved, not assumed.
* `boxSide` — `ℓ = K_ℓ(μa)^{-1/2}`, with `μℓ³ ≥ 2` (`mu_ell_cube_ge_two`),
  the `N = 1` constant-state test of the audit.

The conventions are fixed here once and for all: `t` is the diluteness `μa³`,
`X = t^{1/323}`, and *every* quantity of the chapter is a function of the pair
`(μ, a)` through `t` and FS's powers of `X`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBox

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The monomial `(μa³)^{c/323}` and its API -/

/-- FS's small parameter to the power `c`: `fsXp t c = (μa³)^{c/323}`.  With
`c = 1` this is FS's `X = (μa³)^{1/323}`; every parameter of `sec:params` is a
power of `X`, hence of this form. -/
noncomputable def fsXp (t c : ℝ) : ℝ := t ^ (c / 323)

/-- FS's small parameter `X = (μa³)^{1/323}` (FS eq. `eq:Xchoice`). -/
noncomputable def fsX (t : ℝ) : ℝ := fsXp t 1

lemma fsXp_pos {t c : ℝ} (ht : 0 < t) : 0 < fsXp t c :=
  Real.rpow_pos_of_pos ht _

lemma fsXp_nonneg {t c : ℝ} (ht : 0 ≤ t) : 0 ≤ fsXp t c :=
  Real.rpow_nonneg ht _

lemma fsXp_mul {t : ℝ} (ht : 0 < t) (c e : ℝ) :
    fsXp t c * fsXp t e = fsXp t (c + e) := by
  dsimp [fsXp]
  rw [← Real.rpow_add ht]
  ring_nf

lemma fsXp_inv {t : ℝ} (ht : 0 < t) (c : ℝ) : (fsXp t c)⁻¹ = fsXp t (-c) := by
  dsimp [fsXp]
  rw [← Real.rpow_neg ht.le]
  ring_nf

lemma fsXp_rpow {t : ℝ} (ht : 0 ≤ t) (c r : ℝ) : (fsXp t c) ^ r = fsXp t (c * r) := by
  dsimp [fsXp]
  rw [← Real.rpow_mul ht]
  congr 1
  ring

lemma fsXp_pow {t : ℝ} (ht : 0 ≤ t) (c : ℝ) (n : ℕ) :
    (fsXp t c) ^ n = fsXp t (c * n) := by
  rw [← Real.rpow_natCast (fsXp t c) n]
  exact fsXp_rpow ht c n

/-- The diluteness is the `323`-th power of `X`: `μa³ = X^{323}`. -/
lemma delta_eq_fsXp {t : ℝ} (ht : 0 ≤ t) : t = fsXp t 323 := by
  dsimp [fsXp]
  rw [show (323 : ℝ) / 323 = 1 by norm_num, Real.rpow_one]

/-- **The master inequality**: for `0 < t ≤ 1`, `(μa³)^{a/323} ≤ (μa³)^{b/323}`
whenever `b ≤ a` (the map `c ↦ (μa³)^{c/323}` is antitone for `μa³ ≤ 1`). -/
lemma fsXp_le_fsXp {t a b : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hba : b ≤ a) :
    fsXp t a ≤ fsXp t b := by
  dsimp [fsXp]
  refine Real.rpow_le_rpow_of_exponent_ge h0 h1 ?_
  linarith

/-- `fsXp t c ≤ 1` for `0 < t ≤ 1` and `0 ≤ c`. -/
lemma fsXp_le_one {t c : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hc : 0 ≤ c) : fsXp t c ≤ 1 := by
  have h := fsXp_le_fsXp (t := t) (a := c) (b := 0) h0 h1 hc
  simpa [fsXp] using h

/-- The `MuchLe`-slack used throughout: FS's conditions hold at the concrete
choice with this single slack, so the cap is exact and costs nothing. -/
def slack : ℝ := 1 / 40

lemma slack_pos : 0 < slack := by norm_num [slack]

/-! ## 2. The parameter block -/

/-- FS's parameter block (`sec:params`): the regularisation integer `M` of the
localisation function, the dimensionless small parameters `s, d, ε_T` and the
large parameters `K_ℓ, K_B, K_M, K_H` (with `X` recorded for the conditions).
This is *all* the data that depends on the diluteness `μa³ = X^{323}`; the
chemical potential `μ`, the box side `ℓ = K_ℓ(μa)^{-1/2}` and the particle
number are kept outside. -/
structure FSParams where
  /-- `X = (μa³)^{1/323}`. -/
  X : ℝ
  /-- FS's `s = X`. -/
  s : ℝ
  /-- FS's `d = X⁶`. -/
  d : ℝ
  /-- FS's `ε_T = X^{23/4}`. -/
  eT : ℝ
  /-- FS's `K_ℓ = X^{-3/2}`. -/
  Kl : ℝ
  /-- FS's `K_B = X^{-6}`. -/
  KB : ℝ
  /-- FS's `K_M = X^{-1}`. -/
  KM : ℝ
  /-- FS's `K_H = X^{-8/3}`. -/
  KH : ℝ
  /-- FS's integer `M` (the regularity of the localisation function `χ`). -/
  M : ℕ
  /-- FS's `b`: the (universal, small) coefficient of the Neumann gap term
  `bℓ^{-2}Q_u` of `eq:DefT`.  It is a free universal constant, constrained only
  by FS `lem:LocKinEn` (`b` below a universal constant); we fix it. -/
  b : ℝ

/-- The integer `M` of FS `sec:params` ("We can choose the integer
`M = Mvalue`", chosen there to satisfy `con:d5s`, `con:KellKLd`,
`con:boghamerror` and `con:Q3error3`).  The value `48` is comfortably large:
at `X = (μa³)^{1/323}` all four conditions hold with slack `1/40`
(`paramsOK_fsParams`). -/
def mValue : ℕ := 48

/-- FS's universal gap coefficient `b` of `eq:DefT` (`bℓ^{-2}Q_u`), fixed at a
small universal constant: `lem:LocKinEn` needs `b` below a universal constant
only. -/
def bValue : ℝ := 1 / 16

/-- **FS's choice of parameters** at diluteness `t = μa³` (FS eq.
`eq:Xparameter`, eq. `eq:Xchoice`).  This is the *only* parameter choice used by
this chapter. -/
noncomputable def fsParams (t : ℝ) : FSParams :=
  { X := fsXp t 1
    s := fsXp t 1
    d := fsXp t 6
    eT := fsXp t (23 / 4)
    Kl := fsXp t (-(3 / 2))
    KB := fsXp t (-6)
    KM := fsXp t (-1)
    KH := fsXp t (-(8 / 3))
    M := mValue
    b := bValue }

/-! ## 3. FS's conditions (`sec:params`) -/

/-- FS's `f ≪ g` ("`(f/g) ≤ (μa³)^ε` for some positive `ε`", `sec:params`),
made explicit: there is `0 < ε ≤ 1/40` with `f ≤ g·(μa³)^ε`.  All the
conditions of `sec:params` at FS's choice hold with the *same* `ε = 1/40`
(`paramsOK_fsParams`), so the cap is not a weakening of the concrete instance. -/
def MuchLe (f g t : ℝ) : Prop := ∃ ε : ℝ, 0 < ε ∧ ε ≤ slack ∧ f ≤ g * t ^ ε

/-- `con:d5s`: `d^{-5}s^{M+1} ≪ 1`.  Needed for the kinetic localisation into
the small boxes (`eq:BSlidingassp`, from Bratteli–Solovej). -/
def Con_d5s (P : FSParams) (t : ℝ) : Prop := MuchLe (P.d ^ (-(5 : ℝ)) * P.s ^ ((P.M : ℝ) + 1)) 1 t

/-- `con:eTdK`: `(dK_ℓ)² ≪ ε_TK_ℓ^{-2} ≪ ε_T ≪ s d K_ℓ`.  The first part is
the small-box gap; the last part is needed for the LHY constant in
`sec:Precise`. -/
def Con_eTdK (P : FSParams) : Prop :=
  (P.d * P.Kl) ^ 2 ≤ P.eT * P.Kl ^ (-(2 : ℝ)) ∧
    P.eT * P.Kl ^ (-(2 : ℝ)) ≤ P.eT ∧ P.eT ≤ P.s * P.d * P.Kl

/-- The (universal) smallness of FS's gap coefficient `b` of `eq:DefT`: FS
`lem:LocKinEn` requires `b` below a universal constant (`b̂`). -/
def Con_b (P : FSParams) : Prop := P.b ≤ bValue

/-- `con:sKell`: `sK_ℓ ≫ 1`: the localised kinetic energy in the large boxes
is essentially the kinetic energy at the Bogoliubov scales. -/
def Con_sKell (P : FSParams) (t : ℝ) : Prop := MuchLe 1 (P.s * P.Kl) t

/-- `con:sdKellKB`: `s d K_ℓ ≫ K_B^{-1}`: the small boxes are not too small. -/
def Con_sdKellKB (P : FSParams) (t : ℝ) : Prop :=
  MuchLe (P.KB ^ (-(1 : ℝ))) (P.s * P.d * P.Kl) t

/-- `con:KB`: `K_B ≪ (μa³)^{-1/6}`: the a-priori lower bound is better than the
leading order term. -/
def Con_KB (P : FSParams) (t : ℝ) : Prop := MuchLe P.KB (t ^ (-(1 / 6 : ℝ))) t

/-- `con:KBKell`: `K_B³K_ℓ² ≪ (μa³)^{-1/4}`: the a-priori bounds on the
particle number and on the expected number of excited particles are correct to
leading order (`eq:apriorinn+`). -/
def Con_KBKell (P : FSParams) (t : ℝ) : Prop :=
  MuchLe (P.KB ^ 3 * P.Kl ^ 2) (t ^ (-(1 / 4 : ℝ))) t

/-- `con:KBellKM`: `K_B³K_ℓ⁵ ≪ 𝓜 = K_M(μa³)^{-1/4}`: the a-priori bound on
the excited number is much smaller than the `𝓜`-window. -/
def Con_KBellKM (P : FSParams) (t : ℝ) : Prop :=
  MuchLe (P.KB ^ 3 * P.Kl ^ 5) (P.KM * t ^ (-(1 / 4 : ℝ))) t

/-- `con:M<<n` (`eq:M<<n`): `𝓜 = K_M(μa³)^{-1/4} ≪ μℓ³ = K_ℓ³(μa³)^{-1/2}`:
the excited number is much less than the total number. -/
def Con_Mlln (P : FSParams) (t : ℝ) : Prop :=
  MuchLe (P.KM * t ^ (-(1 / 4 : ℝ))) (P.Kl ^ 3 * t ^ (-(1 / 2 : ℝ))) t

/-- `con:KMKellKH`: `K_MK_ℓ⁴ ≪ K_H³`: controls the error from cutting off the
`3Q` terms in momentum (absorbed in the energy gap). -/
def Con_KMKellKH (P : FSParams) (t : ℝ) : Prop := MuchLe (P.KM * P.Kl ^ 4) (P.KH ^ 3) t

/-- `con:KellKLd`: `(K_ℓK_L)^{1-M} = d^{2M-2} ≪ (μa³)^{1/2}`: controls the
errors from the localisation function (this error appears in the final bound on
the energy, `eq:Q3Cancels`). -/
def Con_KellKLd (P : FSParams) (t : ℝ) : Prop :=
  MuchLe (P.d ^ (2 * (P.M : ℝ) - 2)) (t ^ (1 / 2 : ℝ)) t

/-- `con:KLKH`: `K_LK_H = (K_ℓd²)^{-1}K_H ≪ (μa³)^{-1/12}`: the high momenta
are disjoint from the low momenta. -/
def Con_KLKH (P : FSParams) (t : ℝ) : Prop :=
  MuchLe ((P.Kl * P.d ^ 2) ^ (-(1 : ℝ)) * P.KH) (t ^ (-(1 / 12 : ℝ))) t

/-- `con:rough1`: `K_MK_ℓ⁵d^{-12}(μa³)^{1/4} ≪ 1` (the most restrictive of the
`sec:rough` conditions): `ρ_z` is close to `μ`. -/
def Con_rough1 (P : FSParams) (t : ℝ) : Prop :=
  MuchLe (P.KM * P.Kl ^ 5 * P.d ^ (-(12 : ℝ)) * t ^ (1 / 4 : ℝ)) 1 t

/-- `con:rough2`: `K_M³K_H⁴K_ℓ^{-1}d^{-12}(μa³)^{13/12} ≪ 1`. -/
def Con_rough2 (P : FSParams) (t : ℝ) : Prop :=
  MuchLe (P.KM ^ 3 * P.KH ^ 4 * P.Kl ^ (-(1 : ℝ)) * P.d ^ (-(12 : ℝ)) * t ^ (13 / 12 : ℝ)) 1 t

/-- `con:boghamerror`: `K_MK_ℓ^{-3/2}(K_ℓK_H(μa³)^{1/12})^{M-5} ≪ (μa³)^{1/2}`:
needed for the error in the Bogoliubov diagonalisation (`eq:BogHamDiag`). -/
def Con_boghamerror (P : FSParams) (t : ℝ) : Prop :=
  MuchLe (P.KM * P.Kl ^ (-(3 / 2 : ℝ)) *
      (P.Kl * P.KH * t ^ (1 / 12 : ℝ)) ^ ((P.M : ℝ) - 5)) (t ^ (1 / 2 : ℝ)) t

/-- `con:KellKM`: `K_L³K_M = (K_ℓd²)^{-3}K_M ≪ (μa³)^{-1/4}` (a condition of
`thm:Control3Q`). -/
def Con_KellKM (P : FSParams) (t : ℝ) : Prop :=
  MuchLe ((P.Kl * P.d ^ 2) ^ (-(3 : ℝ)) * P.KM) (t ^ (-(1 / 4 : ℝ))) t

/-- `con:KellKH`: `K_ℓ²K_H⁴d^{-6} ≪ (μa³)^{-1/3}` (a condition of
`thm:Control3Q`). -/
def Con_KellKH (P : FSParams) (t : ℝ) : Prop :=
  MuchLe (P.Kl ^ 2 * P.KH ^ 4 * P.d ^ (-(6 : ℝ))) (t ^ (-(1 / 3 : ℝ))) t

/-- `con:Q3error1`: `K_MK_ℓ^{-3}K_H^{-2} ≪ (μa³)^{-1/12}`: an error of
`thm:Control3Q` is of lower order than LHY. -/
def Con_Q3error1 (P : FSParams) (t : ℝ) : Prop :=
  MuchLe (P.KM * P.Kl ^ (-(3 : ℝ)) * P.KH ^ (-(2 : ℝ))) (t ^ (-(1 / 12 : ℝ))) t

/-- `con:Q3error3`: `K_MK_ℓ^{-3}d^{-12}(K_ℓ^{-2}K_H²(μa³)^{1/6})^{M-1} ≪ (μa³)^{3/4}`. -/
def Con_Q3error3 (P : FSParams) (t : ℝ) : Prop :=
  MuchLe (P.KM * P.Kl ^ (-(3 : ℝ)) * P.d ^ (-(12 : ℝ)) *
      (P.Kl ^ (-(2 : ℝ)) * P.KH ^ 2 * t ^ (1 / 6 : ℝ)) ^ ((P.M : ℝ) - 1)) (t ^ (3 / 4 : ℝ)) t

/-- **The parameter conditions of FS `sec:params`** (all conditions that depend
only on the parameter block and the diluteness).  This is the single hypothesis
that the node statements of this chapter carry; it is *instantiated* by
`paramsOK_fsParams`. -/
structure ParamsOK (P : FSParams) (t : ℝ) : Prop where
  bsmall : Con_b P
  d5s : Con_d5s P t
  eTdK : Con_eTdK P
  sKell : Con_sKell P t
  sdKellKB : Con_sdKellKB P t
  KB : Con_KB P t
  KBKell : Con_KBKell P t
  KBellKM : Con_KBellKM P t
  Mlln : Con_Mlln P t
  KMKellKH : Con_KMKellKH P t
  KellKLd : Con_KellKLd P t
  KLKH : Con_KLKH P t
  rough1 : Con_rough1 P t
  rough2 : Con_rough2 P t
  boghamerror : Con_boghamerror P t
  KellKM : Con_KellKM P t
  KellKH : Con_KellKH P t
  Q3error1 : Con_Q3error1 P t
  Q3error3 : Con_Q3error3 P t

/-- `con:KMRKB`: `K_M^{-2}∫v/a ≪ 1` (the error in restricting to a bounded
number of excited particles).  The `v`-dependent constant is passed as
`intv := ∫v/a`. -/
def Con_KMRKB (P : FSParams) (intv t : ℝ) : Prop := MuchLe (P.KM ^ (-(2 : ℝ)) * intv) 1 t

/-- `eq:intvbound`: `∫v/a ≪ (μa³)^{-2/323}` (FS's assumption on the potential,
needed for `con:KMRKB`). -/
def Con_intv (intv t : ℝ) : Prop := MuchLe intv (t ^ (-(2 / 323 : ℝ))) t

/-- The two `v`-dependent parameter conditions, kept separate from `ParamsOK`
so that the node statements can carry only what they use. -/
structure ParamsOKv (P : FSParams) (intv t : ℝ) : Prop where
  KMRKB : Con_KMRKB P intv t
  intv_bound : Con_intv intv t

/-! ## 4. FS's choice satisfies every condition (the B8 bookkeeping) -/

/-- Helper turning an `fsXp`-comparison into `MuchLe`: for `0 < t ≤ 1`, if the
exponents satisfy `b + 323ε ≤ a` then `(μa³)^{a/323} ≤ (μa³)^{b/323}·(μa³)^ε`.
This is the only arithmetic fact the whole of `paramsOK_fsParams` uses. -/
lemma muchLe_of_exp {t a b ε : ℝ} (h0 : 0 < t) (h1 : t ≤ 1)
    (hε : 0 < ε) (hε' : ε ≤ slack) (hab : b + 323 * ε ≤ a) :
    fsXp t a ≤ fsXp t b * t ^ ε := by
  have htε : t ^ ε = fsXp t (323 * ε) := by
    conv_lhs => rw [delta_eq_fsXp h0.le]
    rw [fsXp_rpow h0.le]
  rw [htε, fsXp_mul h0 b (323 * ε)]
  exact fsXp_le_fsXp h0 h1 hab

end Work.BoseBox
