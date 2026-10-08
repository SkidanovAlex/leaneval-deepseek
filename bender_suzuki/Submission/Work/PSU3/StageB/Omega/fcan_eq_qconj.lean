/-
# `Work.PSU3.StageB.Omega.fcan_eq_qconj` — Peterfalvi II, Ch. VII §2 (5)

Peterfalvi II, Ch. VII §2, item **(5)** (p. 269):

> `f(ω) = (ω y)^a`, `ω ∈ Q - Q₀`, `y ∈ Q₀` and `a ∈ D` imply `y ≠ 1` and `a ∉ K`.

The proof has two parts, exactly as in the source.

* `y ≠ 1`: if `y = 1` then `f` fixes the `D`-orbit of `ω`; but `j` (inversion) has no fixed
  point on the set of `D`-orbits of `Q - Q₀` (because `|D|` is odd while `x ↦ x⁻¹` has order
  `2` on a cyclic 2-subgroup `⟨x⟩` with `x² ≠ 1`), and `f` and `j` are conjugate as permutations
  of that orbit set (H2, H5).  This is `fceq_not_FcanQ_fixed` below.
* `a ∉ K`: the H2/H3 computation `f(ω y) = (f(ω) y^a)^{a⁻¹ a^{-t}}` together with §2 (4)
  (`fcan_shift_Q0`) gives `a⁻¹ a^{-t} ≠ 1`; since `t` inverts `K`, `a ∈ K` would give
  `a⁻¹ a^{-t} = 1`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.no_inv_of_mem_D
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

/-! ## The set of `D`-orbits of `Q ∖ Q₀`

`D` acts on `Q ∖ Q₀` by conjugation; `f` and `j` (inversion) map `D`-orbits to `D`-orbits and
satisfy `f² = j² = (f j)³ = 1` on the orbit set.  Since in `⟨s, u | s² = u² = (su)³ = 1⟩` the
two involutions are conjugate, `f` has a fixed point on the orbit set iff `j` does; but `j` has
none, by `no_inv_of_mem_D`. -/

/-- The elements of `Q` outside `Q₀`, on which `D` acts by conjugation. -/
abbrev fceq_Qout (fr : CoarseFrame H Q t n) : Type := {z : Q // (z : G) ∉ fr.Q0}

/-- The `D`-orbit relation on `Q ∖ Q₀`. -/
def fceq_Zrel (fr : CoarseFrame H Q t n) (z w : fceq_Qout fr) : Prop :=
  ∃ d : ↥(twoPoint H t), ((w : Q) : G) = (d : G) * ((z : Q) : G) * (d : G)⁻¹

theorem fceq_Zrel_refl (fr : CoarseFrame H Q t n) (z : fceq_Qout fr) : fceq_Zrel fr z z :=
  ⟨1, by simp⟩

theorem fceq_Zrel_symm {fr : CoarseFrame H Q t n} {z w : fceq_Qout fr} (h : fceq_Zrel fr z w) :
    fceq_Zrel fr w z := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d⁻¹, ?_⟩
  rw [Subgroup.coe_inv, hd]
  group

theorem fceq_Zrel_trans {fr : CoarseFrame H Q t n} {a b c : fceq_Qout fr} (h1 : fceq_Zrel fr a b)
    (h2 : fceq_Zrel fr b c) : fceq_Zrel fr a c := by
  obtain ⟨d, hd⟩ := h1
  obtain ⟨e, he⟩ := h2
  refine ⟨e * d, ?_⟩
  rw [Subgroup.coe_mul, he, hd]
  group

/-- The setoid of `D`-orbits of `Q ∖ Q₀`. -/
def fceq_Zsetoid (fr : CoarseFrame H Q t n) : Setoid (fceq_Qout fr) where
  r := fceq_Zrel fr
  iseqv := ⟨fceq_Zrel_refl fr, fun h => fceq_Zrel_symm h, fun h1 h2 => fceq_Zrel_trans h1 h2⟩

/-- The set of `D`-orbits of `Q ∖ Q₀`. -/
abbrev fceq_Y (fr : CoarseFrame H Q t n) : Type := Quotient (fceq_Zsetoid fr)

/-- `f` on `Q ∖ Q₀`. -/
noncomputable def fceq_QoutFcan (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (z : fceq_Qout fr) :
    fceq_Qout fr :=
  ⟨fcan hS.split z.1, fun h => z.2 ((fcan_mem_Q0_iff hS fr z.1).mp h)⟩

/-- Inversion on `Q ∖ Q₀`. -/
noncomputable def fceq_QoutInv (fr : CoarseFrame H Q t n) (z : fceq_Qout fr) : fceq_Qout fr :=
  ⟨z.1⁻¹, fun h => z.2 (by
    have h1 := (fr.Q0).inv_mem h
    simpa using h1)⟩

@[simp] theorem fceq_QoutFcan_coe (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (z : fceq_Qout fr) :
    ((fceq_QoutFcan hS fr z : Q) : G) = (fcan hS.split z.1 : G) := rfl

@[simp] theorem fceq_QoutInv_coe (fr : CoarseFrame H Q t n) (z : fceq_Qout fr) :
    ((fceq_QoutInv fr z : Q) : G) = ((z : Q) : G)⁻¹ := rfl

/-- `f` respects the `D`-orbit relation (H3): `f(z^d) = f(z)^{t d t}`. -/
theorem fceq_Zrel_QoutFcan (hS : PSU3Hyp H Q t) {fr : CoarseFrame H Q t n} {z w : fceq_Qout fr}
    (h : fceq_Zrel fr z w) : fceq_Zrel fr (fceq_QoutFcan hS fr z) (fceq_QoutFcan hS fr w) := by
  obtain ⟨d, hd⟩ := h
  have hz1 : ((z : Q) : G) ≠ 1 := fun hc => z.2 (by rw [hc]; exact Q0_one_mem fr)
  have hzw : w.1 = qconj hS.split ⟨(d : G)⁻¹, (twoPoint H t).inv_mem d.2⟩ z.1 := by
    apply Subtype.ext
    rw [qconj_coe]
    show ((w : Q) : G) = ((d : G)⁻¹)⁻¹ * ((z : Q) : G) * (d : G)⁻¹
    rw [hd]
    group
  have hq := fcan_qconj hS.split hz1 ⟨(d : G)⁻¹, (twoPoint H t).inv_mem d.2⟩
  refine ⟨⟨t * (d : G) * t, t_conj_mem_D hS d.2⟩, ?_⟩
  have hL : ((fceq_QoutFcan hS fr w : Q) : G) =
      (fcan hS.split (qconj hS.split ⟨(d : G)⁻¹, (twoPoint H t).inv_mem d.2⟩ z.1) : G) := by
    show (fcan hS.split w.1 : G) = _
    rw [hzw]
  rw [hL, hq]
  have h1 : (t * (d : G)⁻¹ * t)⁻¹ = t * (d : G) * t := by
    rw [Work.PSU3.RankOne.tdt_inv_eq (a := (d : G)⁻¹) (mul_self_eq_one hS.split), inv_inv]
  have h2 : (t * (d : G) * t)⁻¹ = t * (d : G)⁻¹ * t :=
    Work.PSU3.RankOne.tdt_inv_eq (a := (d : G)) (mul_self_eq_one hS.split)
  rw [h1, h2]
  simp only [fceq_QoutFcan_coe]

/-- Inversion respects the `D`-orbit relation. -/
theorem fceq_Zrel_QoutInv {fr : CoarseFrame H Q t n} {z w : fceq_Qout fr} (h : fceq_Zrel fr z w) :
    fceq_Zrel fr (fceq_QoutInv fr z) (fceq_QoutInv fr w) := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, ?_⟩
  rw [fceq_QoutInv_coe, fceq_QoutInv_coe, hd]
  group

/-- `f` as a map on the set of `D`-orbits of `Q ∖ Q₀`. -/
noncomputable def fceq_FcanQ (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) : fceq_Y fr → fceq_Y fr :=
  Quotient.map (fceq_QoutFcan hS fr) (fun _ _ h => fceq_Zrel_QoutFcan hS h)

/-- Inversion as a map on the set of `D`-orbits of `Q ∖ Q₀`. -/
noncomputable def fceq_JinvQ (fr : CoarseFrame H Q t n) : fceq_Y fr → fceq_Y fr :=
  Quotient.map (fceq_QoutInv fr) (fun _ _ h => fceq_Zrel_QoutInv h)

@[simp] theorem fceq_FcanQ_mk (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (z : fceq_Qout fr) :
    fceq_FcanQ hS fr (Quotient.mk (fceq_Zsetoid fr) z) = Quotient.mk (fceq_Zsetoid fr) (fceq_QoutFcan hS fr z) :=
  Quotient.map_mk _ _ z

@[simp] theorem fceq_JinvQ_mk (fr : CoarseFrame H Q t n) (z : fceq_Qout fr) :
    fceq_JinvQ fr (Quotient.mk (fceq_Zsetoid fr) z) = Quotient.mk (fceq_Zsetoid fr) (fceq_QoutInv fr z) :=
  Quotient.map_mk _ _ z

/-- H2: `f` is an involution on the orbit set. -/
theorem fceq_FcanQ_invol (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (y : fceq_Y fr) :
    fceq_FcanQ hS fr (fceq_FcanQ hS fr y) = y := by
  refine Quotient.inductionOn y ?_
  intro z
  rw [fceq_FcanQ_mk, fceq_FcanQ_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  show (fcan hS.split (fcan hS.split z.1) : G) = ((z : Q) : G)
  exact (fcan_fcan hS.split (fun hc => z.2 (by rw [hc]; exact Q0_one_mem fr))).1

/-- `j` is an involution on the orbit set. -/
theorem fceq_JinvQ_invol (fr : CoarseFrame H Q t n) (y : fceq_Y fr) : fceq_JinvQ fr (fceq_JinvQ fr y) = y := by
  refine Quotient.inductionOn y ?_
  intro z
  rw [fceq_JinvQ_mk, fceq_JinvQ_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  simp

/-- H5: `(f ∘ j)³ = 1` on the orbit set (it conjugates by `h(z) ∈ D`). -/
theorem fceq_FJ_cube (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (y : fceq_Y fr) :
    fceq_FcanQ hS fr (fceq_JinvQ fr (fceq_FcanQ hS fr (fceq_JinvQ fr (fceq_FcanQ hS fr (fceq_JinvQ fr y))))) = y := by
  refine Quotient.inductionOn y ?_
  intro z
  rw [fceq_JinvQ_mk, fceq_FcanQ_mk, fceq_JinvQ_mk, fceq_FcanQ_mk, fceq_JinvQ_mk, fceq_FcanQ_mk]
  refine Quotient.sound (fceq_Zrel_symm ⟨hcan hS.split z.1, ?_⟩)
  exact fcan_jjj hS.split (fun hc => z.2 (by rw [hc]; exact Q0_one_mem fr))

/-- If `f` has a fixed point on the orbit set, then so does `j`.

Pointwise form of the group-theoretic fact that in `⟨s, u | s² = u² = (su)³ = 1⟩` the two
involutions are conjugate: with `σ = f ∘ j` one has `j (σ x) = σ (σ (j x))`, and if `f y = y`
then `σ (j y) = y`, whence `j (σ y) = σ (σ (j y)) = σ y`. -/
theorem fceq_fixed_imp_J_fixed (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (y : fceq_Y fr)
    (h : fceq_FcanQ hS fr y = y) : ∃ y' : fceq_Y fr, fceq_JinvQ fr y' = y' := by
  let σ : fceq_Y fr → fceq_Y fr := fun x => fceq_FcanQ hS fr (fceq_JinvQ fr x)
  have hσ3 : ∀ x : fceq_Y fr, σ (σ (σ x)) = x := fun x => fceq_FJ_cube hS fr x
  have hJσ : ∀ x : fceq_Y fr, fceq_JinvQ fr (σ x) = σ (σ (fceq_JinvQ fr x)) := by
    intro x
    set a := fceq_JinvQ fr (σ x) with ha
    have h1 : σ a = fceq_JinvQ fr x := by
      rw [ha]
      show fceq_FcanQ hS fr (fceq_JinvQ fr (fceq_JinvQ fr (σ x))) = fceq_JinvQ fr x
      rw [fceq_JinvQ_invol]
      show fceq_FcanQ hS fr (fceq_FcanQ hS fr (fceq_JinvQ fr x)) = fceq_JinvQ fr x
      rw [fceq_FcanQ_invol]
    have h2 : σ (σ (σ a)) = σ (σ (fceq_JinvQ fr x)) := congrArg (fun z => σ (σ z)) h1
    rw [hσ3 a] at h2
    exact h2
  refine ⟨σ y, ?_⟩
  have hσJ : σ (fceq_JinvQ fr y) = y := by
    show fceq_FcanQ hS fr (fceq_JinvQ fr (fceq_JinvQ fr y)) = y
    rw [fceq_JinvQ_invol, h]
  rw [hJσ y, hσJ]

/-- `j` has no fixed point on the orbit set. -/
theorem fceq_not_J_fixed (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (y : fceq_Y fr) :
    fceq_JinvQ fr y ≠ y := by
  refine Quotient.inductionOn y ?_
  intro z h
  rw [fceq_JinvQ_mk] at h
  obtain ⟨d, hd⟩ := Quotient.exact h
  have hz2 : ((z : Q) : G) ^ 2 ≠ 1 := fun hc => z.2 ((fr.mem_Q0_iff z.1 z.1.2).mpr hc)
  have hd' : ((z : Q) : G) = (d : G) * ((z : Q) : G)⁻¹ * (d : G)⁻¹ := by
    simpa only [fceq_QoutInv_coe] using hd
  have key : (d : G)⁻¹ * ((z : Q) : G) * (d : G) = ((z : Q) : G)⁻¹ := by
    conv_lhs => rw [hd']
    group
  exact no_inv_of_mem_D hS z.1.2 hz2 d.2 key

/-- `f` has no fixed point on the orbit set: §2 (5), "`y ≠ 1`". -/
theorem fceq_not_FcanQ_fixed (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (y : fceq_Y fr) :
    fceq_FcanQ hS fr y ≠ y := by
  intro h
  obtain ⟨y', hy'⟩ := fceq_fixed_imp_J_fixed hS fr y h
  exact fceq_not_J_fixed hS fr y' hy'

/-! ## §2 (5) -/

theorem fcan_eq_qconj {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {y : ↥Q} (hy : (y : G) ∈ fr.Q0)
    {a : ↥(Submission.Blueprint.twoPoint H t)}
    (h : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split a (ω * y)) :
    ((y : G) ≠ 1) ∧ ((a : G) ∉ Work.ThmF.Ksub H t) := by
  have hy_ne : (y : G) ≠ 1 := by
    -- if `y = 1` then `f` fixes the `D`-orbit of `ω`, contradicting `fceq_not_FcanQ_fixed`
    intro hy1
    have hyeq : y = 1 := Subtype.ext hy1
    have h' : fcan hS.split ω = qconj hS.split a ω := by
      have h2 := h
      rw [hyeq, mul_one] at h2
      exact h2
    have hrel : fceq_Zrel fr ⟨ω, hω⟩ (fceq_QoutFcan hS fr ⟨ω, hω⟩) :=
      ⟨⟨(a : G)⁻¹, (twoPoint H t).inv_mem a.2⟩, by
        show (fcan hS.split ω : G) = ((a : G)⁻¹) * (ω : G) * ((a : G)⁻¹)⁻¹
        rw [h', qconj_coe]
        group⟩
    have hmk : Quotient.mk (fceq_Zsetoid fr) (fceq_QoutFcan hS fr ⟨ω, hω⟩) =
        Quotient.mk (fceq_Zsetoid fr) ⟨ω, hω⟩ := Quotient.sound (fceq_Zrel_symm hrel)
    have hF : fceq_FcanQ hS fr (Quotient.mk (fceq_Zsetoid fr) ⟨ω, hω⟩) =
        Quotient.mk (fceq_Zsetoid fr) ⟨ω, hω⟩ := by
      rw [fceq_FcanQ_mk]
      exact hmk
    exact fceq_not_FcanQ_fixed hS fr _ hF
  refine ⟨hy_ne, ?_⟩
  -- `a ∈ K` would give `a⁻¹ a^{-t} = 1`, whence `y = 1` by §2 (4)
  intro haK
  have hω1 : (ω : G) ≠ 1 := fun hc => hω (by rw [hc]; exact Q0_one_mem fr)
  have hyy : (y : G) * (y : G) = 1 := Q0_mul_self fr hy
  have hat : t * (a : G) * t = (a : G)⁻¹ := tconj_eq_inv hS.split fr haK
  have hct : t * (a : G)⁻¹ * t = (a : G) := by
    have h2 := Work.PSU3.RankOne.tdt_inv_eq (a := (a : G)) (mul_self_eq_one hS.split)
    rw [hat, inv_inv] at h2
    exact h2.symm
  -- `f(ω) = a⁻¹ (ω y) a` in coordinates
  have hf : (fcan hS.split ω : G) = (a : G)⁻¹ * (ω : G) * (y : G) * (a : G) := by
    have hh := congrArg (fun z : ↥Q => (z : G)) h
    rw [qconj_coe, Subgroup.coe_mul] at hh
    simpa only [mul_assoc] using hh
  -- §2 (2)/(H3): `f(ω y) = ω^{a^{-t}}`
  have hfu : (fcan hS.split (ω * y) : G) =
      (t * (a : G)⁻¹ * t)⁻¹ * (ω : G) * (t * (a : G)⁻¹ * t) := by
    have hfω1 : ((fcan hS.split ω : Q) : G) ≠ 1 := fcan_ne_one hS.split hω1
    have huy : qconj hS.split ⟨(a : G)⁻¹, (twoPoint H t).inv_mem a.2⟩ (fcan hS.split ω) =
        ω * y := by
      apply Subtype.ext
      rw [qconj_coe, Subgroup.coe_mul, hf]
      group
    have h3 := fcan_qconj hS.split (x := fcan hS.split ω) hfω1
      ⟨(a : G)⁻¹, (twoPoint H t).inv_mem a.2⟩
    rw [← huy, h3, (fcan_fcan hS.split hω1).1]
  -- the paper's identity: `ω^{a^{-t}} = f(ω) · y^a` when `a = a^{-t}`
  have hstep : (t * (a : G)⁻¹ * t)⁻¹ * (ω : G) * (t * (a : G)⁻¹ * t) =
      (fcan hS.split ω : G) * ((a : G)⁻¹ * (y : G) * (a : G)) := by
    rw [hct, hf]
    calc (a : G)⁻¹ * (ω : G) * (a : G)
        = (a : G)⁻¹ * (ω : G) * ((y : G) * (y : G)) * (a : G) := by rw [hyy, mul_one]
      _ = ((a : G)⁻¹ * (ω : G) * (y : G) * (a : G)) *
            ((a : G)⁻¹ * (y : G) * (a : G)) := by group
  have hfinal : fcan hS.split (ω * y) = fcan hS.split ω * qconj hS.split a y := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, qconj_coe, hfu, hstep]
  have hyaQ0 : ((qconj hS.split a y : Q) : G) ∈ fr.Q0 := by
    have h := conj_mem_Q0_of_mem_D hS fr ((twoPoint H t).inv_mem a.2) hy
    simpa [qconj_coe, Subgroup.coe_inv] using h
  exact hy_ne (fcan_shift_Q0 hS fr hω hy hyaQ0 hfinal)

end Work.PSU3.StageB.Omega
