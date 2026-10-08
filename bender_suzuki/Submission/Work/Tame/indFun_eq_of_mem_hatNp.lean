import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.mem_hatNp_iff
import Submission.Work.Tame.conj_mem_hatNp_and_notMem
import Submission.Work.Induction.indFun_TI_apply

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Ind_{𝔑_i}^𝔛 β` fixes the values of `β` on `Ñ_i^#`

Let `L̂` be tamely imbedded in the finite group `X` with supporting subgroups `𝔎_1, …, 𝔎_n`
(Feit–Thompson, Definition 9.1), and suppose `𝔇 ≠ ∅`.  Fix a supporting subgroup `K = 𝔎_i`,
write `𝔑_i = N(𝔎_i)` for its normalizer and `Ñ_i^# = hatNp (Hs i)`.

If `β` is a class function of `𝔑_i` which vanishes off `Ñ_i^#`, then at every `N ∈ Ñ_i^#`

`Ind_{𝔑_i}^𝔛 β (N) = β(N)`.

This is the mechanism Feit–Thompson invoke in the proof of Lemma 9.1 ("since `Ñ_i` is a T. I. set
in `𝔛` with `N(Ñ_i) = 𝔑_i` ...", p. 806, used for (9.7)): it is the value-level form of the
statement that the induced function `β^* = Ind_{𝔑_i}^𝔛 β` agrees with `β` on `Ñ_i^#`.  The same
argument applies to any `ψ` in place of `β` (see `Work.Tame.indFun_hatNp_apply`); here it is
stated for the class function `β` that Lemma 9.1 needs it for.

The proof only uses Definition 9.1(ii)(e), through
`Work.Tame.conj_mem_hatNp_and_notMem`:

* for `x ∈ 𝔑_i` the summand of the induction formula is `β (x N x⁻¹) = β N` because `β` is a class
  function of `𝔑_i`;
* for `x ∉ 𝔑_i` the element `x N x⁻¹` is not in `Ñ_i^#` (T. I. property), and the summand
  `β (x N x⁻¹)` vanishes by the hypothesis `hβv`.
-/

noncomputable section

open Classical

namespace Work.Tame

theorem indFun_eq_of_mem_hatNp {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty)
    (i : Fin n) {β : ↥(Lgrp (Hs i : Set X)) → ℂ} (hβc : CharCore.IsClassFun β)
    (hβv : ∀ N : ↥(Lgrp (Hs i : Set X)), (N : X) ∉ hatNp (Hs i) → β N = 0)
    {N : ↥(Lgrp (Hs i : Set X))} (hN : (N : X) ∈ hatNp (Hs i)) :
    Induction.indFun (Lgrp (Hs i : Set X)) β (N : X) = β N := by
  classical
  -- Definition 9.1(ii)(e): `𝔑_i = N(Ñ_i)` normalizes `Ñ_i^#`, and no element outside `𝔑_i`
  -- conjugates an element of `Ñ_i^#` into `Ñ_i^#`.
  obtain ⟨hmem, hnotMem⟩ := conj_mem_hatNp_and_notMem h hne i
  -- Each summand of the induction formula equals `β N` for `x ∈ 𝔑_i` and `0` otherwise.
  have hstep : ∀ x : X,
      (if hx : x * (N : X) * x⁻¹ ∈ Lgrp (Hs i : Set X) then
          β ⟨x * (N : X) * x⁻¹, hx⟩ else 0)
        = (if hx : x ∈ Lgrp (Hs i : Set X) then β N else 0) := by
    intro x
    by_cases hx : x ∈ Lgrp (Hs i : Set X)
    · -- `x ∈ 𝔑_i`: conjugation stays inside `Ñ_i^#`, and `β` is a class function.
      have hxN : x * (N : X) * x⁻¹ ∈ hatNp (Hs i) := hmem x hx (N : X) hN
      have hxNK : x * (N : X) * x⁻¹ ∈ Lgrp (Hs i : Set X) := (mem_hatNp_iff.mp hxN).1
      rw [dite_eq_left hxNK, dite_eq_left hx]
      have hkey : (⟨x * (N : X) * x⁻¹, hxNK⟩ : ↥(Lgrp (Hs i : Set X)))
          = ⟨x, hx⟩ * N * ⟨x, hx⟩⁻¹ := by
        ext
        simp [Subgroup.coe_mul]
      rw [hkey]
      exact hβc N ⟨x, hx⟩
    · -- `x ∉ 𝔑_i`: the conjugate of `N` lies outside `Ñ_i^#`, where `β` vanishes.
      rw [dite_eq_right hx]
      by_cases hxN : x * (N : X) * x⁻¹ ∈ Lgrp (Hs i : Set X)
      · rw [dite_eq_left hxN]
        have hnot : x * (N : X) * x⁻¹ ∉ hatNp (Hs i) := by
          intro hconj
          have hback := hnotMem x hx (x * (N : X) * x⁻¹) hconj
          rw [show x⁻¹ * (x * (N : X) * x⁻¹) * x = (N : X) from by group] at hback
          exact hback hN
        rw [hβv ⟨x * (N : X) * x⁻¹, hxN⟩ hnot]
      · rw [dite_eq_right hxN]
  rw [Induction.indFun_apply_def, Finset.sum_congr rfl (fun x _ => hstep x)]
  -- The sum is now constant over `𝔑_i`, of value `β N`.
  have hcard : Nat.card ↥(Lgrp (Hs i : Set X)) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨(1 : ↥(Lgrp (Hs i : Set X)))⟩, inferInstance⟩
  have hsum : (∑ x : X, (if hx : x ∈ Lgrp (Hs i : Set X) then β N else 0))
      = (Nat.card ↥(Lgrp (Hs i : Set X)) : ℂ) * β N := by
    have h₁ : (∑ x : X, (if hx : x ∈ Lgrp (Hs i : Set X) then β N else 0))
        = ∑ x : X, dite (x ∈ Lgrp (Hs i : Set X)) (fun _ => β N) (fun _ => 0) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hx : x ∈ Lgrp (Hs i : Set X) <;> simp [hx]
    rw [h₁, Induction.sum_dite_mem_subgroup (Lgrp (Hs i : Set X)) (fun _ => β N)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [hsum]
  have hne0 : (Nat.card ↥(Lgrp (Hs i : Set X)) : ℂ) ≠ 0 := by exact_mod_cast hcard
  rw [← mul_assoc, inv_mul_cancel₀ hne0, one_mul]

end Work.Tame
