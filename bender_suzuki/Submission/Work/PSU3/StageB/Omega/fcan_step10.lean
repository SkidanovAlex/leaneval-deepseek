/-
# `Work.PSU3.StageB.Omega.fcan_step10` — Peterfalvi II, Ch. VII §2 (10)

Peterfalvi II, Ch. VII §2, item **(10)** (p. 271): if `ω ∈ Q ∖ Q₀` satisfies
`f(ω) = (ω y)^ζ` with `y = zc α`, `a ∈ K` corresponds to `u ∈ F*` (`u = nm (κ a)`, i.e.
`zc u = s^a`) and `b ∈ K` corresponds to `v ∈ F*` with `v = α + u^{-1}`, then

  `f(ω s^a) = (f(ω s^b) s^a)^{ζ a^{-2}}`,

i.e., with `zetaExp u = ζ · a^{-1} · a^{-1}`,

  `f (ω · zc u) = (ζ a^{-2})⁻¹ · (f (ω · zc v) · zc u) · (ζ a^{-2})`.

The proof is the recursion **(2)** of §2 (`fcan_mul_zcQF`) together with `H3` for `ζ`
(`f (x^ζ) = f(x)^ζ`, since `t ζ t = ζ`), the additivity of `zc` on the fixed field, the fact
that `ζ` centralises `Q₀ ≅ F`, and the identity `a^{-2} · s^{a^{-1}} = s^{a} · a^{-2}`
(equivalently `ζ` centralises the element `a^{-1} s a = zc u`), which makes the two conjugations
in the recursion collapse.

The auxiliary lemmas above are the pieces of that computation:

* `zeta_comm_zcQF`, `zeta_comm_frameS` — `ζ` centralises `Q₀`;
* `zcQF_mul_zcQF_inv` — `zc (α + u^{-1}) = zc α · zc u^{-1}`;
* `zcQF_eq_sconjF` — `zc u = a^{-1} · s · a` and `zc u^{-1} = a · s · a^{-1}` for
  `a = kElF (τ u)`;
* `fcan_mul_zcQF_A` — §2 (2) with `t h(zc u) t` evaluated to `(a·a)⁻¹`;
* `fcan_mid_aux` — the shift of the `f`-argument from `ω` to `f (ω zc v)`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.Seq
import Submission.Work.PSU3.StageB.ThetaOmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## §1. `ζ` centralises `Q₀ ≅ F` -/

/-- `ζ` commutes with every element `zc u` of `Q₀`. -/
lemma zeta_comm_zcQF (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    (fr.ζ : G) * (zcQF fr u : G) = (zcQF fr u : G) * (fr.ζ : G) := by
  have h : (fr.ζ : G)⁻¹ * (zcQF fr u : G) * (fr.ζ : G) = (zcQF fr u : G) := by
    rw [zcQF_coe]
    exact fr.act_zc_ζ (fval u) u.2
  have h2 : (fr.ζ : G) * ((fr.ζ : G)⁻¹ * (zcQF fr u : G) * (fr.ζ : G)) =
      (fr.ζ : G) * (zcQF fr u : G) := congrArg (fun y => (fr.ζ : G) * y) h
  rw [← h2]
  group

/-- `ζ` commutes with the distinguished involution `s = zc 1`. -/
lemma zeta_comm_frameS (fr : CoarseFrame H Q t n) :
    (fr.ζ : G) * frameS fr = frameS fr * (fr.ζ : G) := by
  have h : (fr.ζ : G)⁻¹ * frameS fr * (fr.ζ : G) = frameS fr := by
    show (fr.ζ : G)⁻¹ * fr.zc 1 * (fr.ζ : G) = fr.zc 1
    exact fr.act_zc_ζ 1 (by simp)
  have h2 : (fr.ζ : G) * ((fr.ζ : G)⁻¹ * frameS fr * (fr.ζ : G)) =
      (fr.ζ : G) * frameS fr := congrArg (fun y => (fr.ζ : G) * y) h
  rw [← h2]
  group

/-! ## §2. The additivity of `zc` in the form used by the recursion -/

/-- `zc (α + u^{-1}) = zc α · zc u^{-1}`, i.e. the `Q₀`-form of the hypothesis `fval v =
fval α + (fval u)⁻¹`. -/
lemma zcQF_mul_zcQF_inv (fr : CoarseFrame H Q t n) {α u v : ↥(FX n)}
    (hv : fval v = fval α + (fval u)⁻¹) : zcQF fr v = zcQF fr α * zcQF fr u⁻¹ := by
  apply Subtype.ext
  have hfix : σE ((fval u)⁻¹) = (fval u)⁻¹ := by rw [map_inv₀, u.2]
  rw [Subgroup.coe_mul, zcQF_coe, zcQF_coe, zcQF_coe, hv,
    fr.zc_add (fval α) ((fval u)⁻¹) α.2 hfix, fval_inv]

/-! ## §3. `zc u` and `zc u⁻¹` as conjugates of `s` -/

/-- With `a = kElF (τ u)` (so that `zc u = s^a`): `zc u = a⁻¹ s a` and `zc u⁻¹ = a s a⁻¹`. -/
lemma zcQF_eq_sconjF (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    (zcQF fr u : G) = (kElF fr (tau hS fr u) : G)⁻¹ * frameS fr * (kElF fr (tau hS fr u) : G) ∧
    (zcQF fr u⁻¹ : G) =
      (kElF fr (tau hS fr u) : G) * frameS fr * (kElF fr (tau hS fr u) : G)⁻¹ := by
  constructor
  · have h1 : zcQF fr u = sconjF fr (tau hS fr u) := by
      rw [sconjF_eq_zcQF fr hS (tau hS fr u), nm_tau]
    rw [h1]
    rfl
  · have h1 : zcQF fr u⁻¹ = sconjF fr (tau hS fr u⁻¹) := by
      rw [sconjF_eq_zcQF fr hS (tau hS fr u⁻¹), nm_tau]
    have h2 : tau hS fr u⁻¹ = (tau hS fr u)⁻¹ := map_inv (tau hS fr) u
    rw [h2] at h1
    rw [h1]
    show (kElF fr ((tau hS fr u)⁻¹) : G)⁻¹ * frameS fr * (kElF fr ((tau hS fr u)⁻¹) : G) = _
    rw [kElF_inv]
    simp only [Subgroup.coe_inv]
    group

/-! ## §4. The recursion §2 (2) with `a = kElF (τ u)` -/

/-- **§2 (2)** with the `D`-factor evaluated: for `x ∈ Q#` and `u ∈ F*`,
`f (x · zc u) = a² · f (f(x) · zc u⁻¹) · (a²)⁻¹ · zc u⁻¹`, where `a = kElF (τ u)` — indeed
`h (zc u) = a²`, and `t (a²) t = a^{-2}` because `t` inverts `Ksub ∋ a`. -/
lemma fcan_mul_zcQF_A (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω1 : (ω : G) ≠ 1) (u : ↥(FX n))
    (hxu : ((ω * zcQF fr u : ↥Q) : G) ≠ 1) :
    (fcan hS.split (ω * zcQF fr u) : G) =
      ((kElF fr (tau hS fr u) : G) * (kElF fr (tau hS fr u) : G)) *
        (fcan hS.split (fcan hS.split ω * zcQF fr u⁻¹) : G) *
        ((kElF fr (tau hS fr u) : G) * (kElF fr (tau hS fr u) : G))⁻¹ *
        (zcQF fr u⁻¹ : G) := by
  have ha : ((kElF fr (tau hS fr u) : fr.KW) : G) ∈ Ksub H t := kElF_mem_Ksub fr (tau hS fr u)
  have ht : t * t = 1 := mul_self_eq_one hS.split
  have hc := (canon_zcQF_coe fr hS u).2.2
  have hconj : t * ((kElF fr (tau hS fr u) : G) * (kElF fr (tau hS fr u) : G)) * t =
      ((kElF fr (tau hS fr u) : G) * (kElF fr (tau hS fr u) : G))⁻¹ := by
    rw [conj_mul_self ht, tconj_eq_inv hS.split fr ha, mul_inv_rev]
  rw [fcan_mul_zcQF hS fr hω1 u hxu, hc, hconj]
  rw [inv_inv]

/-! ## §5. The shift of the `f`-argument -/

/-- `f (f(ω) · zc u⁻¹) = ζ⁻¹ · f (ω · zc v) · ζ`.  Indeed `f(ω) = ζ⁻¹ ω zc α ζ`, and
`zc α · zc u⁻¹ = zc v`, with `ζ` centralising `Q₀`; `H3` (for `ζ^t = ζ`) then pulls `ζ` out
of `f`. -/
lemma fcan_mid_aux (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} {α : ↥(FX n)} (hωf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    {u v : ↥(FX n)} (hv : fval v = fval α + (fval u)⁻¹)
    (hX : ((ω * zcQF fr v : ↥Q) : G) ≠ 1) :
    (fcan hS.split (fcan hS.split ω * zcQF fr u⁻¹) : G) =
      (fr.ζ : G)⁻¹ * (fcan hS.split (ω * zcQF fr v) : G) * (fr.ζ : G) := by
  have hZcm : zcQF fr v = zcQF fr α * zcQF fr u⁻¹ := zcQF_mul_zcQF_inv fr hv
  have hf : (fcan hS.split ω : G) = (fr.ζ : G)⁻¹ * ((ω : G) * (zcQF fr α : G)) * (fr.ζ : G) := by
    have hh := congrArg (fun z : ↥Q => (z : G)) hωf
    rw [qconj_coe, Subgroup.coe_mul] at hh
    exact hh
  have hcz' : (fr.ζ : G) * (zcQF fr u⁻¹ : G) = (zcQF fr u⁻¹ : G) * (fr.ζ : G) :=
    zeta_comm_zcQF fr u⁻¹
  have hmid : fcan hS.split ω * zcQF fr u⁻¹ =
      qconj hS.split ⟨(fr.ζ : G), zeta_mem_D fr⟩ (ω * zcQF fr v) := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, qconj_coe, hf]
    simp only [Subgroup.coe_mul]
    rw [show (zcQF fr v : G) = (zcQF fr α : G) * (zcQF fr u⁻¹ : G) from by
      rw [hZcm, Subgroup.coe_mul]]
    calc (fr.ζ : G)⁻¹ * ((ω : G) * (zcQF fr α : G)) * (fr.ζ : G) * (zcQF fr u⁻¹ : G)
        = (fr.ζ : G)⁻¹ * (ω : G) * (zcQF fr α : G) * ((fr.ζ : G) * (zcQF fr u⁻¹ : G)) := by
          group
      _ = (fr.ζ : G)⁻¹ * (ω : G) * (zcQF fr α : G) * ((zcQF fr u⁻¹ : G) * (fr.ζ : G)) := by
          rw [hcz']
      _ = (fr.ζ : G)⁻¹ * ((ω : G) * ((zcQF fr α : G) * (zcQF fr u⁻¹ : G))) * (fr.ζ : G) := by
          group
  rw [hmid, fcan_qconj hS.split hX ⟨(fr.ζ : G), zeta_mem_D fr⟩, t_zeta_t hS.split fr]

/-! ## §6. §2 (10) -/

theorem fcan_step10 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α))
    {u v : ↥(Work.PSU3.StageB.FX n)}
    (huv : Work.PSU3.StageB.fval v =
      Work.PSU3.StageB.fval α + (Work.PSU3.StageB.fval u)⁻¹)
    (h1 : ((ω * Work.PSU3.StageB.zcQF fr u : ↥Q) : G) ≠ 1) :
    (Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.zcQF fr u) : G) =
      ((Work.PSU3.StageB.zetaExp hS fr u : fr.KW) : G)⁻¹ *
        ((Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.zcQF fr v) *
            Work.PSU3.StageB.zcQF fr u : ↥Q) : G) *
        ((Work.PSU3.StageB.zetaExp hS fr u : fr.KW) : G) := by
  have hExp : ((zetaExp hS fr u : fr.KW) : G) =
      (fr.ζ : G) * (kElF fr (tau hS fr u) : G)⁻¹ * (kElF fr (tau hS fr u) : G)⁻¹ := by
    simp only [zetaExp, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hExp, Subgroup.coe_mul]
  set A : G := (kElF fr (tau hS fr u) : G) with hA
  set Z : G := (fr.ζ : G) with hZ
  set ZcU : G := (zcQF fr u : G) with hZcU
  set ZcU' : G := (zcQF fr u⁻¹ : G) with hZcU'
  set F : G := (fcan hS.split (ω * zcQF fr v) : G) with hF
  have hω1 : (ω : G) ≠ 1 := fun hc => hω (by rw [hc]; exact Q0_one_mem fr)
  have hX : ((ω * zcQF fr v : ↥Q) : G) ≠ 1 := by
    intro hc
    have hmem : (zcQF fr v : G) ∈ fr.Q0 := by
      rw [zcQF_coe]; exact fr.zc_mem (fval v) v.2
    have h2 : (ω : G) = ((ω * zcQF fr v : ↥Q) : G) * (zcQF fr v : G)⁻¹ := by
      rw [Subgroup.coe_mul]; group
    exact hω (by rw [h2, hc, one_mul]; exact fr.Q0.inv_mem hmem)
  have hrec := fcan_mul_zcQF_A hS fr hω1 u h1
  rw [← hA, ← hZcU'] at hrec
  have hmid := fcan_mid_aux hS fr hωf huv hX
  rw [← hZ, ← hF] at hmid
  obtain ⟨hZu, hZu'⟩ := zcQF_eq_sconjF hS fr u
  rw [← hZcU, ← hA] at hZu
  rw [← hZcU', ← hA] at hZu'
  -- `A` and `Z` commute (`a ∈ Ksub ≤ KW` is abelian)
  have hAZ : A * Z = Z * A := by
    rw [hA, hZ]
    exact KW_comm fr (kElF fr (tau hS fr u)) fr.ζ
  have h1Z : Z⁻¹ * A * Z = A := by
    calc Z⁻¹ * A * Z = Z⁻¹ * (A * Z) := by group
      _ = Z⁻¹ * (Z * A) := by rw [hAZ]
      _ = A := by group
  have h1ZA : Z⁻¹ * A⁻¹ * Z = A⁻¹ := by
    calc Z⁻¹ * A⁻¹ * Z = (Z⁻¹ * A * Z)⁻¹ := by group
      _ = A⁻¹ := by rw [h1Z]
  have hZs : Z * frameS fr = frameS fr * Z := by rw [hZ]; exact zeta_comm_frameS fr
  have h1s : Z⁻¹ * frameS fr * Z = frameS fr := by
    calc Z⁻¹ * frameS fr * Z = Z⁻¹ * (frameS fr * Z) := by group
      _ = Z⁻¹ * (Z * frameS fr) := by rw [hZs]
      _ = frameS fr := by group
  have hXZ : Z⁻¹ * (A⁻¹ * frameS fr * A) * Z = A⁻¹ * frameS fr * A := by
    calc Z⁻¹ * (A⁻¹ * frameS fr * A) * Z
        = (Z⁻¹ * A⁻¹ * Z) * (Z⁻¹ * frameS fr * Z) * (Z⁻¹ * A * Z) := by group
      _ = A⁻¹ * frameS fr * A := by rw [h1ZA, h1s, h1Z]
  -- the conjugation by `ζ a^{-2}` sends `zc u` to `zc u⁻¹`
  have hkey : (Z*A⁻¹*A⁻¹)⁻¹ * ZcU * (Z*A⁻¹*A⁻¹) = ZcU' := by
    rw [hZu, hZu']
    rw [show (Z*A⁻¹*A⁻¹)⁻¹ = A*A*Z⁻¹ from by
      simp only [mul_inv_rev, inv_inv]; group]
    rw [show A*A*Z⁻¹ * (A⁻¹ * frameS fr * A) * (Z*A⁻¹*A⁻¹)
          = A*A * (Z⁻¹ * (A⁻¹ * frameS fr * A) * Z) * A⁻¹*A⁻¹ from by group]
    rw [hXZ]
    group
  have hK : (Z*A⁻¹*A⁻¹) * ZcU' = ZcU * (Z*A⁻¹*A⁻¹) := by
    rw [← hkey]
    group
  calc (fcan hS.split (ω * zcQF fr u) : G)
      = (A*A) * (Z⁻¹ * F * Z) * (A*A)⁻¹ * ZcU' := by rw [hrec, hmid]
    _ = ((Z*A⁻¹*A⁻¹)⁻¹ * F * (Z*A⁻¹*A⁻¹)) * ZcU' := by
          rw [show (A*A)⁻¹ = A⁻¹ * A⁻¹ from by group]
          rw [show (Z*A⁻¹*A⁻¹)⁻¹ = A*A*Z⁻¹ from by
            simp only [mul_inv_rev, inv_inv]; group]
          group
    _ = (Z*A⁻¹*A⁻¹)⁻¹ * F * ((Z*A⁻¹*A⁻¹) * ZcU') := by group
    _ = (Z*A⁻¹*A⁻¹)⁻¹ * F * (ZcU * (Z*A⁻¹*A⁻¹)) := by rw [hK]
    _ = (Z*A⁻¹*A⁻¹)⁻¹ * (F * ZcU) * (Z*A⁻¹*A⁻¹) := by group

end Work.PSU3.StageB.Omega
