/-
# `Work.PSU3.StageB.Frame` — elementary consequences of `CoarseFrame`

This module collects the easy consequences of the frame axioms
(`Work.PSU3.CoarseFrame`) that Stages B and C need: `Q₀` is elementary abelian and central
in `Q`, `bar` is additive with kernel `Q₀`, `zc` is an additive bijection `F ≅ Q₀` with
`zc 0 = 1`, `s = zc 1` is a nontrivial involution satisfying `t s t = s t s`, and the
conjugates `s^a = a⁻¹ s a` of `s` by `a ∈ KW ∩ Ksub` are the elements `zc (nm (κ a))`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.RankOneUniqueness.f_unique
import Submission.Work.ThmF.Setup

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

namespace Work.PSU3.StageB

open Work.ThmF

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

section Involution

variable {a b : G}

/-- Conjugation by an involution is multiplicative (version with `t` on both sides). -/
lemma conj_mul_self {t : G} (ht : t * t = 1) (x y : G) :
    t * (x * y) * t = (t * x * t) * (t * y * t) := by
  have hi : t⁻¹ = t := inv_eq_iff_mul_eq_one.mpr ht
  have h := map_mul (MulAut.conj t) x y
  simpa only [MulAut.conj_apply, hi] using h

/-- If `t a t = a⁻¹` then `t a⁻¹ t = a`. -/
lemma conj_inv_of_conj_eq_inv {t a : G} (ht : t * t = 1) (h : t * a * t = a⁻¹) :
    t * a⁻¹ * t = a := by
  have hi : t⁻¹ = t := inv_eq_iff_mul_eq_one.mpr ht
  have h' : (t * a * t)⁻¹ = a := by rw [h, inv_inv]
  have h'' : (t * a * t)⁻¹ = t * a⁻¹ * t := by
    simp only [mul_inv_rev, hi]
    group
  rw [h''] at h'
  exact h'

/-- If `t a t = a⁻¹` then `a t a⁻¹ = a * a * t`. -/
lemma mul_t_inv_of_conj_eq_inv {t a : G} (ht : t * t = 1) (h : t * a * t = a⁻¹) :
    a * t * a⁻¹ = (a * a) * t := by
  have hswap : a * t = t * a⁻¹ := by
    calc a * t = (t * t) * (a * t) := by rw [ht, one_mul]
      _ = t * (t * a * t) := by group
      _ = t * a⁻¹ := by rw [h]
  have hc : t * a⁻¹ * t = a := conj_inv_of_conj_eq_inv ht h
  have h2 : t * (a⁻¹ * a⁻¹) * t = a * a := by
    rw [conj_mul_self ht, hc]
  have h3 : t * (a⁻¹ * a⁻¹) = (t * (a⁻¹ * a⁻¹) * t) * t := by
    rw [mul_assoc, ht, mul_one]
  calc a * t * a⁻¹ = t * a⁻¹ * a⁻¹ := by rw [hswap]
    _ = t * (a⁻¹ * a⁻¹) := by group
    _ = (t * (a⁻¹ * a⁻¹) * t) * t := h3
    _ = (a * a) * t := by rw [h2]

end Involution

section Basics

variable (fr : CoarseFrame H Q t n)

/-! ### `Q₀` is an elementary abelian central subgroup of `Q` -/

lemma Q0_one_mem : (1 : G) ∈ fr.Q0 :=
  (fr.mem_Q0_iff 1 Q.one_mem).mpr (by simp)

lemma Q0_sq_eq_one {z : G} (hz : z ∈ fr.Q0) : z ^ 2 = 1 :=
  (fr.mem_Q0_iff z (fr.Q0_le hz)).mp hz

lemma Q0_le_central (z : fr.Q0) (x : Q) : (z : G) * (x : G) = (x : G) * (z : G) :=
  fr.Q0_central z z.2 x x.2

lemma Q0_comm (x y : fr.Q0) : (x : G) * (y : G) = (y : G) * (x : G) :=
  fr.Q0_central x x.2 y (fr.Q0_le y.2)

/-- Every element of `Q₀` is an involution. -/
lemma Q0_inv_eq_self {z : G} (hz : z ∈ fr.Q0) : z⁻¹ = z := by
  have h : z * z = 1 := by simpa [pow_two] using Q0_sq_eq_one fr hz
  exact inv_eq_of_mul_eq_one_right h

lemma Q0_mul_self {z : G} (hz : z ∈ fr.Q0) : z * z = 1 := by
  simpa [pow_two] using Q0_sq_eq_one fr hz

/-! ### `bar` -/

lemma bar_one : fr.bar 1 = 1 := map_one _

lemma bar_mul (x y : Q) : fr.bar (x * y) = fr.bar x * fr.bar y := map_mul _ _ _

/-- `bar x = 1` exactly on `Q₀`. -/
lemma bar_eq_one_iff' (x : Q) : fr.bar x = 1 ↔ (x : G) ∈ fr.Q0 := fr.bar_eq_one_iff x

lemma bar_eq_one_of_mem_Q0 {x : Q} (hx : (x : G) ∈ fr.Q0) : fr.bar x = 1 :=
  (fr.bar_eq_one_iff x).mpr hx

lemma bar_ne_one_of_not_mem_Q0 {x : Q} (hx : (x : G) ∉ fr.Q0) : fr.bar x ≠ 1 :=
  fun h => hx ((fr.bar_eq_one_iff x).mp h)

/-- Two elements of `Q` with the same `bar` differ by an element of `Q₀`. -/
lemma mul_mem_Q0_of_bar_eq {x y : Q} (h : fr.bar x = fr.bar y) :
    ((x : G)⁻¹ * (y : G)) ∈ fr.Q0 := by
  have hbar : fr.bar (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, h]
    simp
  exact (fr.bar_eq_one_iff (x⁻¹ * y)).mp hbar

lemma bar_eq_of_mul_mem_Q0 {x y : Q} (h : ((x : G)⁻¹ * (y : G)) ∈ fr.Q0) :
    fr.bar x = fr.bar y := by
  have hb : fr.bar (x⁻¹ * y) = 1 := (fr.bar_eq_one_iff (x⁻¹ * y)).mpr h
  rw [map_mul, map_inv] at hb
  have hb' : fr.bar y = fr.bar x := by
    have := congrArg (fun z => fr.bar x * z) hb
    simpa [mul_assoc] using this
  exact hb'.symm

/-- Conversely, elements of `Q₀` are trivial in the quotient. -/
lemma bar_eq_iff_mul_mem_Q0 (x y : Q) :
    fr.bar x = fr.bar y ↔ ((x : G)⁻¹ * (y : G)) ∈ fr.Q0 :=
  ⟨mul_mem_Q0_of_bar_eq fr, bar_eq_of_mul_mem_Q0 fr⟩

/-! ### `zc` -/

lemma zc_zero : fr.zc 0 = 1 := by
  have h := fr.zc_add 0 0 (by simp) (by simp)
  rw [zero_add] at h
  have h2 : fr.zc 0 * fr.zc 0 = fr.zc 0 * 1 := by rw [← h, mul_one]
  exact mul_left_cancel h2

lemma zc_zero_mem : fr.zc 0 ∈ fr.Q0 := by rw [zc_zero]; exact Q0_one_mem fr

lemma zc_mem' {y : E n} (hy : σE y = y) : fr.zc y ∈ fr.Q0 := fr.zc_mem y hy

lemma zc_inj' {y y' : E n} (hy : σE y = y) (hy' : σE y' = y') (h : fr.zc y = fr.zc y') :
    y = y' := fr.zc_inj y y' hy hy' h

/-- `zc` restricted to the fixed field is injective. -/
lemma zc_injective_fixed :
    Function.Injective fun y : {y : E n // σE y = y} => fr.zc (y : E n) := by
  intro y y' h
  exact Subtype.ext (fr.zc_inj y y' y.2 y'.2 h)

/-- The unique element of the fixed field whose `zc`-image is a given element of `Q₀`. -/
noncomputable def frameZcPreimage (z : G) (hz : z ∈ fr.Q0) : E n :=
  Classical.choose (fr.zc_surj z hz)

lemma frameZcPreimage_fixed {z : G} (hz : z ∈ fr.Q0) : σE (frameZcPreimage fr z hz) = frameZcPreimage fr z hz :=
  (Classical.choose_spec (fr.zc_surj z hz)).1

lemma zc_frameZcPreimage {z : G} (hz : z ∈ fr.Q0) : fr.zc (frameZcPreimage fr z hz) = z :=
  (Classical.choose_spec (fr.zc_surj z hz)).2

/-! ### `s = zc 1`: the distinguished involution -/

/-- `s = zc 1`, the distinguished involution of the frame. -/
noncomputable def frameS : G := fr.zc 1

lemma frameS_mem_Q : frameS fr ∈ Q := fr.Q0_le (fr.zc_mem 1 (by simp))

lemma frameS_mem_Q0 : frameS fr ∈ fr.Q0 := fr.zc_mem 1 (by simp)

lemma frameS_sq_eq_one : frameS fr ^ 2 = 1 := Q0_sq_eq_one fr (frameS_mem_Q0 fr)

lemma zc_one_eq_frameS : fr.zc 1 = frameS fr := rfl

/-- `s ≠ 1`. -/
lemma frameS_ne_one : frameS fr ≠ 1 := by
  intro h
  have h0 : fr.zc 1 = fr.zc 0 := by rw [zc_zero]; exact h
  exact one_ne_zero (fr.zc_inj 1 0 (by simp) (by simp) h0)

lemma frameS_struct' : t * frameS fr * t = frameS fr * t * frameS fr := fr.s_struct

lemma eq_zero_of_zc_eq_one {y : E n} (hy : σE y = y) (h : fr.zc y = 1) : y = 0 := by
  have h0 : fr.zc y = fr.zc 0 := by rw [zc_zero]; exact h
  exact fr.zc_inj y 0 hy (by simp) h0

end Basics

/-! ## The conjugates `s^a` for `a ∈ Ksub ∩ KW` -/

section ConjS

/-- `KW` is abelian (it embeds in the abelian group `Eˣ` by `κ`). -/
lemma KW_comm (fr : CoarseFrame H Q t n) (a b : fr.KW) :
    (a : G) * (b : G) = (b : G) * (a : G) := by
  have h1 : (a * b : fr.KW) = b * a := by
    apply fr.κ_injective
    show fr.κ (a * b) = fr.κ (b * a)
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have h2 := congrArg (fun z : fr.KW => (z : G)) h1
  simpa using h2

/-- Every element of `Kset H t` lies in `KW` (via `Ksub ≤ KW`). -/
lemma mem_KW_of_mem_Kset (fr : CoarseFrame H Q t n) {x : G} (hx : x ∈ Kset H t) : x ∈ fr.KW :=
  fr.K_le (Kset_le_Ksub H t hx)

/-- For `a ∈ Ksub H t`, `t a t = a⁻¹`.  Indeed `Kset ⊆ KW` is closed under multiplication (all
its elements lie in the abelian group `KW`), hence is a subgroup containing `Kset`, so
`Ksub = ⟨Kset⟩ = Kset`. -/
theorem tconj_eq_inv (h : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n) {a : G}
    (ha : a ∈ Ksub H t) : t * a * t = a⁻¹ := by
  have ht : t * t = 1 := mul_self_eq_one h
  have hi : t⁻¹ = t := inv_eq_self h
  have key : ∀ x ∈ Ksub H t, x ∈ fr.KW ∧ t * x * t = x⁻¹ := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x ∈ fr.KW ∧ t * x * t = x⁻¹) ?_ ?_ ?_ ?_ hx
    · intro y hy
      refine ⟨mem_KW_of_mem_Kset fr hy, ?_⟩
      have hyi : t * y * t⁻¹ = y⁻¹ := hy.2
      rwa [hi] at hyi
    · exact ⟨(fr.KW).one_mem, by simpa using ht⟩
    · intro u v _ _ ihu ihv
      refine ⟨(fr.KW).mul_mem ihu.1 ihv.1, ?_⟩
      have hcomm : u * v = v * u := KW_comm fr ⟨u, ihu.1⟩ ⟨v, ihv.1⟩
      rw [conj_mul_self ht, ihu.2, ihv.2]
      calc u⁻¹ * v⁻¹ = (v * u)⁻¹ := by rw [mul_inv_rev]
        _ = (u * v)⁻¹ := by rw [hcomm]
    · intro u _ ihu
      refine ⟨(fr.KW).inv_mem ihu.1, ?_⟩
      rw [conj_inv_of_conj_eq_inv ht ihu.2, inv_inv]
  exact (key a ha).2

/-- `s^a = a⁻¹ s a = zc (nm (κ a))` for `a ∈ KW` with `a ∈ Ksub`. -/
lemma conj_s_eq_zc (fr : CoarseFrame H Q t n) {a : fr.KW} (ha : (a : G) ∈ Ksub H t) :
    (a : G)⁻¹ * frameS fr * (a : G) = fr.zc ((fr.nm (fr.κ a) : (E n)ˣ) : E n) := by
  have h := fr.act_zc_K a ha 1 (by simp)
  simpa [frameS] using h

/-- `s^a` lies in `Q₀`. -/
lemma conj_s_mem_Q0 (fr : CoarseFrame H Q t n) {a : fr.KW} (ha : (a : G) ∈ Ksub H t) :
    (a : G)⁻¹ * frameS fr * (a : G) ∈ fr.Q0 := by
  rw [conj_s_eq_zc fr ha]
  exact fr.zc_mem _ (fr.nm_F (fr.κ a) ((fr.mem_K_iff a).mp ha))

/-- The canonical data of `t (s^a) t`: it is `s^{a⁻¹} · a² · t · s^{a⁻¹}`. -/
lemma canon_conj_s (h : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n) {a : fr.KW}
    (ha : (a : G) ∈ Ksub H t) :
    Canon3 H Q t ((a : G)⁻¹ * frameS fr * (a : G)) ((a : G) * frameS fr * (a : G)⁻¹)
      ((a : G) * (a : G)) ((a : G) * frameS fr * (a : G)⁻¹) := by
  have ht : t * t = 1 := mul_self_eq_one h
  have hta : t * (a : G) * t = (a : G)⁻¹ := tconj_eq_inv h fr ha
  have hainv : ((a⁻¹ : fr.KW) : G) ∈ Ksub H t := (Ksub H t).inv_mem ha
  have hmem : (a : G) * frameS fr * (a : G)⁻¹ ∈ Q := by
    have heq : (a : G) * frameS fr * (a : G)⁻¹ =
        ((a⁻¹ : fr.KW) : G)⁻¹ * frameS fr * ((a⁻¹ : fr.KW) : G) := by
      simp [mul_assoc]
    rw [heq]
    exact fr.Q0_le (conj_s_mem_Q0 fr hainv)
  refine ⟨hmem, ?_, hmem, ?_⟩
  · have h2 : (a : G) * (a : G) = ((a * a : fr.KW) : G) := rfl
    rw [h2]
    exact fr.KW_le (a * a).2
  · rw [conj_mul_self ht ((a : G)⁻¹ * frameS fr) (a : G),
      conj_mul_self ht (a : G)⁻¹ (frameS fr), conj_inv_of_conj_eq_inv ht hta, frameS_struct' fr, hta]
    have hkey : (a : G) * (frameS fr * t * frameS fr) * (a : G)⁻¹ =
        ((a : G) * frameS fr * (a : G)⁻¹) * (((a : G) * (a : G)) * t) *
          ((a : G) * frameS fr * (a : G)⁻¹) := by
      rw [← mul_t_inv_of_conj_eq_inv ht hta]
      group
    rw [hkey]
    group

end ConjS

end Work.PSU3.StageB
