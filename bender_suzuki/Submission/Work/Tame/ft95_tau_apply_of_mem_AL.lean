import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.tau_apply_of_mem_AL_some
import Submission.Work.Tame.indFun_Lgrp_apply_of_mem_L0set

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.ft95_tau_apply_of_mem_AL` — Feit–Thompson 9.1, the value part

For `L` in one of the sets `𝔏_0, 𝔏_1, …, 𝔏_n` of Feit–Thompson p. 805 (indexed here by
`Idx n = Option (Fin n)`, `none` for `i = 0`) and `A` in the corresponding set `𝔄_L`
(`ALofIdx`), the Dade map of (9.4) satisfies `α^τ(A) = α(L)` whenever `α ∈ 𝓒₀(L̂)`.

The proof is the case split of the source's (9.4)–(9.7):

* `j = none` (`𝔎_0 = 1`): `𝔄_L = {L}` and `𝔏_0 = L0set Lhat`, so `α^τ(L) = α^*(L) = α(L)` by
  `indFun_Lgrp_apply_of_mem_L0set` (which is the source's `α^*(L) = |C(L) ∩ 𝔎_i|·α(L)` with
  `|C_X(L)| = |C_𝔏(L)|` for `L ∈ 𝔏_0`), while every correction term `(α_{i1} - α_{i2})^*(L)`
  vanishes at `L` because no conjugate of `L` lies in `Ñ_i^#`
  (`not_isConj_mem_hatNp_of_mem_L0set`), by `indFun_beta_eq_zero_of_forall_not_conj`;
* `j = some i`: `A = L·H` with `H ∈ 𝔎_i ∩ C(L)`, and `tau_apply_of_mem_AL_some` gives the value;
* the degenerate case `𝔇 = ∅` forces `n = 0` and there is no `some i`, so only the first case
  occurs.

The modules `tau_apply_of_mem_AL.lean` and `cfInner_tau_tau.lean` build on this one; it is
deliberately kept free of any dependency on them, so that no `import` cycle can arise.
-/

namespace Work.Tame

open Classical

/-- Conjugate elements have the same order. -/
theorem orderOf_eq_of_isConj {X : Type*} [Group X] {a b : X} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := h
  have hb : b = (c : X) * a * (c : X)⁻¹ := by
    calc b = (b * (c : X)) * (c : X)⁻¹ := by group
      _ = ((c : X) * a) * (c : X)⁻¹ := by rw [← hc.eq]
      _ = (c : X) * a * (c : X)⁻¹ := rfl
  rw [hb]
  exact (orderOf_injective (MulAut.conj (c : X)).toMonoidHom
    (MulAut.conj (c : X)).injective a).symm

/-- **Feit–Thompson 9.1, value part** (p. 805): `α^τ(A) = α(L)` for `A ∈ 𝔄_L`, `L ∈ 𝔏_j`,
`0 ≤ j ≤ n`. -/
theorem ft95_tau_apply_of_mem_AL {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hD : HasTameData Lhat n Hs)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) {j : Idx n} {L : ↥(Lgrp Lhat)}
    (hL : (L : X) ∈ LofIdx Lhat n Hs j)
    {A : X} (hA : A ∈ ALofIdx Lhat n Hs j (L : X)) :
    tau Lhat n Hs α A = α L := by
  rcases hD with hne | hn
  · cases j with
    | none =>
      have hAeq : A = (L : X) := by simpa only [ALofIdx, AL, Set.mem_singleton_iff] using hA
      rw [hAeq, tau_apply, indFun_Lgrp_apply_of_mem_L0set h hα hL,
        Finset.sum_eq_zero (fun i _ => indFun_beta_eq_zero_of_forall_not_conj h hne hα i
          (fun x => not_isConj_mem_hatNp_of_mem_L0set h hne hL)), add_zero]
    | some i =>
      obtain ⟨H, hH, hcomm, rfl⟩ := hA
      have hLeq : (⟨(L : X), h.sub_norm hL.1.1⟩ : ↥(Lgrp Lhat)) = L := Subtype.ext rfl
      rw [tau_apply_of_mem_AL_some h hne hα hL hH hcomm, hLeq]
  · subst hn
    cases j with
    | none =>
      have hAeq : A = (L : X) := by simpa only [ALofIdx, AL, Set.mem_singleton_iff] using hA
      rw [hAeq, tau_apply, indFun_Lgrp_apply_of_mem_L0set h hα hL,
        Finset.sum_eq_zero (fun i _ => i.elim0), add_zero]
    | some i => exact i.elim0

end Work.Tame
