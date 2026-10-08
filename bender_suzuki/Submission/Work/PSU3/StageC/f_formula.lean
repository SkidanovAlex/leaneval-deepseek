/-
# `Work.PSU3.StageC.f_formula` (C2 of the lead's design)

Peterfalvi II Ch. VII §3, pp. 275–277: in the fine coordinates `e : Q ≃* SZ (E n)` of the
case-c Suzuki group, the book's map `f` (`FRel H t x y`, i.e. `t x t = m · t · y`) is the
model map `f(x,y) = (x/y, 1/y)` (`Work.PSU3.fMapTot`).

The proof goes through the intermediate vocabulary set up in this file:

* the coordinate dictionary of `e` (`hex`, `hes`, `heq`): `e` carries the `KW`-action
  (`SZ.torusAct`), the centre `Q₀` (`e (zc y) = (0,y)`) and the element `s = zc 1`;
* the action of `t` on `K = J(D,t)` (inversion) and on `ζ` (trivial);
* the element `ω` of `OmegaHyp` together with its consequences (Ch. VII §3 (1)–(5)).

Layer 0 below contains the elementary structural facts about `Ksub`, `ζ` and the
`t`-conjugation of `KW`; the main theorem is at the end of the file.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.FMap
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.canon_exists
import Submission.Work.RankOneUniqueness.canon_unique
import Submission.Work.RankOneUniqueness.f_exists
import Submission.Work.RankOneUniqueness.f_unique
import Submission.Work.PSU3.RankOne.H16
import Submission.Work.PSU3.RankOne.canon_conj
import Submission.Work.PSU3.RankOne.canon_mul
import Submission.Work.PSU3.RankOne.canon_mul_ne_one
import Submission.Work.PSU3.StageC.e_zc_eq
import Submission.Work.PSU3.StageC.omega_y_coord
import Submission.Work.PSU3.StageC.f_formula_of_omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.PSU3.StageC

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Layer 0: `K = J(D,t)` is inverted by `t` -/

/-- `t * t = 1`. -/
theorem aux_t_mul_self (hS : Work.PSU3.PSU3Hyp H Q t) : t * t = 1 :=
  Work.RankOneUniqueness.mul_self_eq_one hS.split

/-- For the involution `t`, `t⁻¹ = t`. -/
theorem inv_t (hS : Work.PSU3.PSU3Hyp H Q t) : t⁻¹ = t :=
  Work.RankOneUniqueness.inv_eq_self hS.split

/-- Elements of `Ksub H t = ⟨J(D,t)⟩` commute: they lie in `KW`, whose `κ`-image lies in the
abelian group `(E n)ˣ`. -/
theorem Ksub_comm (fr : Work.PSU3.CoarseFrame H Q t n) :
    ∀ x ∈ Work.ThmF.Ksub H t, ∀ y ∈ Work.ThmF.Ksub H t, x * y = y * x := by
  intro x hx y hy
  have hxKW : x ∈ fr.KW := fr.K_le hx
  have hyKW : y ∈ fr.KW := fr.K_le hy
  have key : (⟨x, hxKW⟩ : fr.KW) * ⟨y, hyKW⟩ = ⟨y, hyKW⟩ * ⟨x, hxKW⟩ := by
    apply fr.κ_injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  exact congrArg Subtype.val key

/-- **`t` inverts `J(D,t)`** (Peterfalvi II Ch. VII §2 (1)): for `x ∈ Ksub H t`,
`t x t⁻¹ = x⁻¹`.  (`Kset H t` is a subgroup because it lies in the abelian `Ksub`.) -/
theorem t_conj_Ksub (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n) :
    ∀ x ∈ Work.ThmF.Ksub H t, t * x * t⁻¹ = x⁻¹ := by
  have ht : t * t = 1 := aux_t_mul_self hS
  have hcomm := Ksub_comm (t := t) (Q := Q) fr
  intro x hx
  refine Subgroup.closure_induction (k := Work.ThmF.Kset H t)
    (p := fun x _ => t * x * t⁻¹ = x⁻¹) ?_ ?_ ?_ ?_ hx
  · intro a ha
    exact (Work.ThmF.mem_Kset_iff.mp ha).2
  · simp
  · intro a b ha hb iha ihb
    have hcomm' : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
      have := congrArg (fun z : G => z⁻¹) (hcomm a ha b hb)
      simpa [mul_inv_rev] using this.symm
    rw [show t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) from by group, iha, ihb,
      mul_inv_rev, hcomm']
  · intro a ha iha
    rw [show t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ from by group, iha, inv_inv]

/-- `t` centralises `ζ` (since `ζ ∈ W ≤ C_D(t)`); in the form used below, `t ζ t = ζ`. -/
theorem aux_t_conj_zeta (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n) :
    t * (fr.ζ : G) * t = fr.ζ := by
  have ht : t * t = 1 := aux_t_mul_self hS
  have hmem : (fr.ζ : G) ∈ centD H t := Work.ThmF.W_le_centD H t fr.ζ_mem_W
  have hct : t * (fr.ζ : G) = (fr.ζ : G) * t :=
    (Subgroup.mem_centralizer_iff.mp hmem.2) t (by simp)
  rw [hct, mul_assoc, ht, mul_one]

/-- For an involution `t` (`t * t = 1`), conjugation by `t` is multiplicative. -/
theorem conj_mul_of_self (hS : Work.PSU3.PSU3Hyp H Q t) (a b : G) :
    (t * a * t) * (t * b * t) = t * (a * b) * t := by
  have ht : t * t = 1 := aux_t_mul_self hS
  calc (t * a * t) * (t * b * t) = t * a * (t * t) * b * t := by group
    _ = t * a * b * t := by rw [ht, mul_one]
    _ = t * (a * b) * t := by group

/-- Powers of `ζ` are centralised by `t`. -/
theorem aux_t_conj_zeta_pow (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (j : ℕ) : t * (fr.ζ : G) ^ j * t = (fr.ζ : G) ^ j := by
  have ht : t * t = 1 := aux_t_mul_self hS
  have hζ : t * (fr.ζ : G) * t = (fr.ζ : G) := aux_t_conj_zeta hS fr
  induction j with
  | zero => rw [pow_zero, mul_one, ht]
  | succ j ih =>
      rw [pow_succ,
        show t * ((fr.ζ : G) ^ j * (fr.ζ : G)) * t
            = (t * (fr.ζ : G) ^ j * t) * (t * (fr.ζ : G) * t)
          from (conj_mul_of_self hS _ _).symm,
        ih, hζ]

/-- **The `t`-conjugate of an element of `KW` still lies in `KW`**, and its `κ`-value is
`(σ (κ d))⁻¹ = κ(d)^{-q}` (Peterfalvi's `d^t ↔ d^{-q}`): for `d = k ζ^j` (`KW_gen`),
`t d t = k⁻¹ ζ^j` and `κ (k⁻¹ ζ^j) = (σ (κ d))⁻¹`. -/
theorem aux_tdt_KW (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n) (d : fr.KW) :
    ∃ d' : fr.KW, (d' : G) = t * (d : G) * t ∧
      ((fr.κ d' : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
        = (σE ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n))⁻¹ := by
  obtain ⟨k, hk, j, hdj⟩ := fr.KW_gen d
  have hkinv : t * (k : G) * t = (k : G)⁻¹ := by
    have h := t_conj_Ksub hS fr (k : G) hk
    have ht : t⁻¹ = t := inv_t hS
    rw [ht] at h
    exact h
  have hzpow : t * (fr.ζ : G) ^ j * t = (fr.ζ : G) ^ j :=
    aux_t_conj_zeta_pow hS fr j
  have hdt : (d : G) = (k : G) * (fr.ζ : G) ^ j := by
    rw [hdj]; rfl
  refine ⟨k⁻¹ * fr.ζ ^ j, ?_, ?_⟩
  · -- the group element
    rw [hdt]
    rw [show t * ((k : G) * (fr.ζ : G) ^ j) * t
        = (t * (k : G) * t) * (t * (fr.ζ : G) ^ j * t)
      from (conj_mul_of_self hS _ _).symm]
    rw [hkinv, hzpow]
    rfl
  · -- the field element
    have hkfix : σE ((fr.κ k : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
        = ((fr.κ k : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) :=
      (fr.mem_K_iff k).mp hk
    have hζnorm : ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
        * σE ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) = 1 := fr.ζ_norm
    have hσζ : σE ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
        = ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)⁻¹ :=
      eq_inv_of_mul_eq_one_right hζnorm
    have hd' : ((fr.κ (k⁻¹ * fr.ζ ^ j) : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
        = ((fr.κ k : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)⁻¹
          * (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) ^ j := by
      simp
    rw [hd']
    have hdn : ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
        = ((fr.κ k : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
          * (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) ^ j := by
      rw [hdj]; simp
    rw [hdn, map_mul, map_pow, hkfix, hσζ]
    simp only [mul_inv_rev, inv_pow, inv_inv]
    ring

/-! ## The main theorem (design node C2) -/

theorem f_formula {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) {ω : G}
    (hω : Work.PSU3.OmegaHyp fr ω)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (hω2 : ω ^ 2 = fr.zc ((fr.κ fr.ζ : Work.PSU3.E n) + (fr.κ fr.ζ : Work.PSU3.E n)⁻¹))
    (e : Q ≃* SZ (Work.PSU3.E n)) (μ : (Work.PSU3.E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x)) :
    ∀ x y : Q, (x : G) ≠ 1 → Work.RankOneUniqueness.FRel H t (x : G) (y : G) →
      e y = Work.PSU3.fMapTot (e x) := by
  -- C2 is assembled from its two halves:
  -- * `omega_y_coord` — the §3 (1)–(4) computation of the `ω`-coordinate;
  -- * `f_formula_of_omega` — the propagation from the `ω`-coset to all of `Q#`
  --   (§2 (5)–(8) counting + §3 (5)).
  exact f_formula_of_omega hS fr hω hsq hω2 e μ hex hes heq
    (omega_y_coord hS fr hω hsq hω2 e μ hex hes heq)

end Work.PSU3.StageC
