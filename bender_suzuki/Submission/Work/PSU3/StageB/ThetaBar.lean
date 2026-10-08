/-
# `Work.PSU3.StageB.ThetaBar` — Peterfalvi II, Ch. VII §3 (2)

The computation of `bar (f (ω s^a))` (Peterfalvi, *Le théorème de Bender–Suzuki II*,
Astérisque 142–143, Ch. VII §3, p. 276, step (2)):

$$\overline{f(\omega s^a)} = \frac{\bar\omega}{a^2+\zeta^{-1}} = \frac{\zeta\,\bar\omega}{1+\zeta a^2}.$$

The two ingredients are the two ways of computing `f (ω⁻¹ s^{a⁻¹})` from H6
(`canon_mul_fun`), namely `ThetaBarA` (Peterfalvi's §2 (2) with `(ω,a) ↦ (ω⁻¹,a⁻¹)`) and
`ThetaBarB` (Peterfalvi's §3 (1), i.e. §2 (3) with `(ω,a) ↦ (ω⁻¹,a⁻¹)`):

  `f (ω⁻¹ s^{a⁻¹}) = f (ω^{ζ⁻¹} s^a)^{a⁻²} s^a = f (ω^ζ s^a)^{ζ⁻³} ω^{ζ⁻¹}`,

which on taking `bar` gives `ζ⁻¹ a² \bar u = ζ⁻² \bar u + ζ⁻¹ \barω`, whence in
characteristic two `(1 + ζ a²) \bar u = ζ \barω`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Theta
import Submission.Work.PSU3.StageB.ThetaBarPrep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.ThmF
open Work.PSU3
open Classical

namespace Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Peterfalvi §2 (2) with `(ω,a) ↦ (ω⁻¹,a⁻¹)` -/

theorem ThetaBarA (fr : CoarseFrame H Q t n) (h : IsSplitRankOne H Q t)
    {ω : G} (hω : OmegaHyp fr ω)
    (hfω : (fcan h (omQ fr hω) : G) = (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G))
    (a : fr.KW) (ha : (a : G) ∈ Ksub H t) :
    fcan h ((omQ fr hω)⁻¹ * sconj fr a⁻¹ ((Ksub H t).inv_mem ha)) =
      qact fr h (a * a)
          (qact fr h fr.ζ⁻¹ (fcan h (omQ fr hω * sconj fr a ha))) *
        sconj fr a ha := by
  have hai : ((a⁻¹ : fr.KW) : G) ∈ Ksub H t := (Ksub H t).inv_mem ha
  have hx1 : (((omQ fr hω)⁻¹ : ↥Q) : G) ≠ 1 := by
    rw [Subgroup.coe_inv]
    exact fun h1 => omQ_ne_one fr hω (inv_eq_one.mp h1)
  have hSI1 : ((sconj fr a⁻¹ hai : ↥Q) : G) ≠ 1 := sconj_ne_one fr h a⁻¹ hai
  have hXY : (((omQ fr hω)⁻¹ * sconj fr a⁻¹ hai : ↥Q) : G) ≠ 1 :=
    ne_one_inv_mul_sconj_inv fr h hω a ha
  have h6 := (canon_mul_fun h hx1 hSI1 hXY).1
  have hc := canon_sconj_inv fr h a ha
  rw [t_conj_canon_sconj_inv fr h a ha, fcan_inv_omQ fr h hω hfω, hc.2.1, hc.1] at h6
  have hstep : qact fr h fr.ζ⁻¹ (omQ fr hω) * sconj fr a ha =
      qact fr h fr.ζ⁻¹ (omQ fr hω * sconj fr a ha) := by
    rw [qact_mul, qact_zeta_inv_of_mem_Q0 fr h (sconj_mem_Q0 fr a ha)]
  have hfx2 : fcan h (qact fr h fr.ζ⁻¹ (omQ fr hω * sconj fr a ha)) =
      qact fr h fr.ζ⁻¹ (fcan h (omQ fr hω * sconj fr a ha)) :=
    fcan_qact_zeta_inv fr h _ (ne_one_mul_sconj fr h hω a ha)
  apply Subtype.ext
  rw [h6, hstep, hfx2]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, qact_coe]

/-! ## Peterfalvi §3 (1): the second evaluation of `f (ω⁻¹ s^{a⁻¹})` -/

theorem ThetaBarB (fr : CoarseFrame H Q t n) (h : IsSplitRankOne H Q t)
    {ω : G} (hω : OmegaHyp fr ω)
    (hfω : (fcan h (omQ fr hω) : G) = (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G))
    (hzinv : (hcan h ((omQ fr hω)⁻¹) : G) =
      (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹)
    (a : fr.KW) (ha : (a : G) ∈ Ksub H t) :
    fcan h (sconj fr a⁻¹ ((Ksub H t).inv_mem ha) * (omQ fr hω)⁻¹) =
      qact fr h ((fr.ζ * fr.ζ)⁻¹) (fcan h (omQ fr hω * sconj fr a ha)) *
        qact fr h fr.ζ⁻¹ (omQ fr hω) := by
  have hai : ((a⁻¹ : fr.KW) : G) ∈ Ksub H t := (Ksub H t).inv_mem ha
  have hx1 : ((omQ fr hω : ↥Q) : G) ≠ 1 := omQ_ne_one fr hω
  have hxi1 : (((omQ fr hω)⁻¹ : ↥Q) : G) ≠ 1 := by
    rw [Subgroup.coe_inv]
    exact fun h1 => omQ_ne_one fr hω (inv_eq_one.mp h1)
  have hSI1 : ((sconj fr a⁻¹ hai : ↥Q) : G) ≠ 1 := sconj_ne_one fr h a⁻¹ hai
  have hXY : ((sconj fr a⁻¹ hai * (omQ fr hω)⁻¹ : ↥Q) : G) ≠ 1 :=
    ne_one_sconj_inv_mul fr h hω a ha
  have h6 := (canon_mul_fun h hSI1 hxi1 hXY).1
  -- `gcan (ω⁻¹) = (fcan ω)⁻¹ = ω^ζ`
  have hg : gcan h ((omQ fr hω)⁻¹) = qact fr h fr.ζ (omQ fr hω) := by
    have h1 : (gcan h ((omQ fr hω)⁻¹) : G) = ((fcan h (omQ fr hω) : ↥Q) : G)⁻¹ :=
      (canon_inv_fun h hx1).2.1
    have h2 : (fcan h (omQ fr hω) : G) = (qact fr h fr.ζ ((omQ fr hω)⁻¹) : G) := by
      rw [qact_coe, Subgroup.coe_inv]
      exact hfω
    apply Subtype.ext
    rw [h1, h2]
    simp only [Subgroup.coe_inv, qact_coe]
    group
  rw [hzinv, t_conj_zeta_inv_cube fr h, hg, (canon_sconj_inv fr h a ha).1,
    fcan_inv_omQ fr h hω hfω] at h6
  -- the middle factor: `s^a · ω^ζ = ω^ζ · s^a`
  have hstep2 : sconj fr a ha * qact fr h fr.ζ (omQ fr hω) =
      qact fr h fr.ζ (omQ fr hω * sconj fr a ha) := by
    have hcz : qact fr h fr.ζ (sconj fr a ha) = sconj fr a ha := by
      apply Subtype.ext
      simpa using zeta_conj_Q0 fr (sconj_mem_Q0 fr a ha)
    have hcomm : sconj fr a ha * qact fr h fr.ζ (omQ fr hω) =
        qact fr h fr.ζ (omQ fr hω) * sconj fr a ha := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact fr.Q0_central (sconj fr a ha) (sconj_mem_Q0 fr a ha)
        (qact fr h fr.ζ (omQ fr hω)) (qact fr h fr.ζ (omQ fr hω)).2
    calc sconj fr a ha * qact fr h fr.ζ (omQ fr hω)
        = qact fr h fr.ζ (omQ fr hω) * qact fr h fr.ζ (sconj fr a ha) := by rw [hcomm, hcz]
      _ = qact fr h fr.ζ (omQ fr hω * sconj fr a ha) :=
          (qact_mul fr h fr.ζ _ _).symm
  have hfx3 : fcan h (qact fr h fr.ζ (omQ fr hω * sconj fr a ha)) =
      qact fr h fr.ζ (fcan h (omQ fr hω * sconj fr a ha)) :=
    fcan_qact_zeta fr h _ (ne_one_mul_sconj fr h hω a ha)
  apply Subtype.ext
  rw [h6, hstep2, hfx3]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, qact_coe]
  group

/-! ## The division step -/

/-- The arithmetic of Peterfalvi's Ch. VII §3 (2): in a field of characteristic two, the equation
`A (c⁻¹ U) = c⁻¹ (c⁻¹ U) + c⁻¹ W` (with `c ≠ 0` and `W ≠ 0`) gives `U = cW/(1 + cA)`. -/
theorem ThetaBarDiv {F : Type*} [Field F] [CharP F 2] {c A U W : F} (hc : c ≠ 0)
    (hW : W ≠ 0)
    (h : A * (c⁻¹ * U) = c⁻¹ * (c⁻¹ * U) + c⁻¹ * W) :
    U = c * W / (1 + c * A) := by
  have htwo : (2 : F) = 0 := by
    have h' : ((2 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 2 2).mpr (dvd_refl 2)
    simpa using h'
  have hself : ∀ x : F, x + x = 0 := fun x => by rw [← two_mul, htwo, zero_mul]
  -- multiplying the hypothesis by `c²`: `c * A * U = U + c * W`
  have hcL : c * (A * (c⁻¹ * U)) = A * U := by
    calc c * (A * (c⁻¹ * U)) = (c * A) * (c⁻¹ * U) := (mul_assoc c A (c⁻¹ * U)).symm
      _ = ((c * A) * c⁻¹) * U := (mul_assoc (c * A) c⁻¹ U).symm
      _ = ((A * c) * c⁻¹) * U := by rw [mul_comm c A]
      _ = (A * (c * c⁻¹)) * U := by rw [mul_assoc A c c⁻¹]
      _ = (A * 1) * U := by rw [mul_inv_cancel₀ hc]
      _ = A * U := by rw [mul_one]
  have hcR1 : c * (c⁻¹ * (c⁻¹ * U) + c⁻¹ * W) = c⁻¹ * U + W := by
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hcR : c * (c * (c⁻¹ * (c⁻¹ * U) + c⁻¹ * W)) = U + c * W := by
    rw [hcR1, mul_add, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have h1 : c * A * U = U + c * W := by
    have h2 : c * (c * (A * (c⁻¹ * U))) =
        c * (c * (c⁻¹ * (c⁻¹ * U) + c⁻¹ * W)) := by rw [h]
    rw [hcL, hcR] at h2
    rwa [← mul_assoc] at h2
  -- hence `(1 + c * A) * U = c * W`
  have h3 : (1 + c * A) * U = c * W := by
    calc (1 + c * A) * U = U + c * A * U := by rw [add_mul, one_mul]
      _ = U + (U + c * W) := by rw [h1]
      _ = c * W := by rw [← add_assoc, hself U, zero_add]
  have hden : 1 + c * A ≠ 0 := by
    intro hzero
    have hcA : c * A = 1 := by
      have hh : 1 + (c * A + c * A) = c * A := by
        calc 1 + (c * A + c * A) = (1 + c * A) + c * A := (add_assoc 1 (c * A) (c * A)).symm
          _ = 0 + c * A := by rw [hzero]
          _ = c * A := zero_add _
      rw [hself (c * A), add_zero] at hh
      exact hh.symm
    have hcw : c * W = 0 := by
      rw [← h3, hcA, hself 1, zero_mul]
    rcases mul_eq_zero.mp hcw with h' | h'
    · exact absurd h' hc
    · exact hW h'
  rw [eq_div_iff hden, mul_comm]
  exact h3

theorem ThetaBar {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) (h : Submission.Blueprint.IsSplitRankOne H Q t)
    {ω : G} (hω : Work.PSU3.OmegaHyp fr ω)
    (hW : (Work.PSU3.StageB.hcan h (Work.PSU3.StageB.omQ fr hω) : G) ∈ Work.ThmF.W H t)
    (hfω : (Work.PSU3.StageB.fcan h (Work.PSU3.StageB.omQ fr hω) : G) =
      (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G))
    (hzinv : (Work.PSU3.StageB.hcan h ((Work.PSU3.StageB.omQ fr hω)⁻¹) : G) =
      (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹)
    (a : fr.KW) (ha : (a : G) ∈ Work.ThmF.Ksub H t) :
    Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan h
        (Work.PSU3.StageB.omQ fr hω * Work.PSU3.StageB.sconj fr a ha)))
      = ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) *
          Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.omQ fr hω)) /
        (1 + ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) *
          (((fr.κ a : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) ^ 2) := by
  have hA := ThetaBarA fr h hω hfω a ha
  have hB := ThetaBarB fr h hω hfω hzinv a ha
  -- `s^{a⁻¹}` lies in `Q₀ = Z(Q)`, so it commutes with `ω⁻¹`
  have hswap : (omQ fr hω)⁻¹ * sconj fr a⁻¹ ((Ksub H t).inv_mem ha) =
      sconj fr a⁻¹ ((Ksub H t).inv_mem ha) * (omQ fr hω)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (fr.Q0_central (sconj fr a⁻¹ ((Ksub H t).inv_mem ha))
      (sconj_mem_Q0 fr a⁻¹ _) (omQ fr hω)⁻¹ (Q.inv_mem (omQ fr hω).2)).symm
  -- the two evaluations of `f (ω⁻¹ s^{a⁻¹})` agree, giving the key identity
  have key : qact fr h (a * a)
        (qact fr h fr.ζ⁻¹ (fcan h (omQ fr hω * sconj fr a ha))) * sconj fr a ha =
      qact fr h ((fr.ζ * fr.ζ)⁻¹) (fcan h (omQ fr hω * sconj fr a ha)) *
        qact fr h fr.ζ⁻¹ (omQ fr hω) := by
    rw [← hA, ← hB, hswap]
  set U0 : E n := Multiplicative.toAdd (fr.bar (fcan h (omQ fr hω * sconj fr a ha))) with hU0
  set W0 : E n := Multiplicative.toAdd (fr.bar (omQ fr hω)) with hW0
  set c : E n := ((fr.κ fr.ζ : (E n)ˣ) : E n) with hcdef
  set A2 : E n := ((fr.κ a : (E n)ˣ) : E n) ^ 2 with hA2def
  -- take `bar` of the key identity
  have hbar' : A2 * (c⁻¹ * U0) = c⁻¹ * (c⁻¹ * U0) + c⁻¹ * W0 := by
    have h := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) key
    simp only [map_mul, Units.val_mul, toAdd_mul, qact_bar,
      bar_eq_one_of_mem_Q0 fr (sconj_mem_Q0 fr a ha), toAdd_one, add_zero] at h
    have e1 : ((fr.κ a : (E n)ˣ) : E n) * ((fr.κ a : (E n)ˣ) : E n) = A2 := by
      rw [hA2def, pow_two]
    have e2 : ((fr.κ fr.ζ⁻¹ : (E n)ˣ) : E n) = c⁻¹ := by
      rw [hcdef, map_inv, Units.val_inv_eq_inv_val]
    have e3 : ((fr.κ ((fr.ζ * fr.ζ)⁻¹) : (E n)ˣ) : E n) = c⁻¹ * c⁻¹ := by
      rw [hcdef, map_inv, map_mul, Units.val_inv_eq_inv_val, Units.val_mul, mul_inv_rev]
    rw [e1, e2, e3] at h
    rwa [mul_assoc] at h
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact Units.ne_zero _
  have hW0' : W0 ≠ 0 := by
    rw [hW0]
    intro hzero
    have h1 : fr.bar (omQ fr hω) = 1 := toAdd_eq_zero.mp hzero
    have h2 : ω ∈ fr.Q0 := (fr.bar_eq_one_iff (omQ fr hω)).mp h1
    exact hω.2.1 (by simpa [omQ_coe fr hω] using h2)
  exact ThetaBarDiv hc0 hW0' hbar'

end Work.PSU3.StageB
