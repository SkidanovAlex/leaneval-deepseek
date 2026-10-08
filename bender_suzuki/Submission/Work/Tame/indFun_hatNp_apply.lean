import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.mem_hatNp_iff
import Submission.Work.Tame.conj_mem_hatNp_and_notMem
import Submission.Work.Tame.beta_eq_zero_of_notMem_hatNp
import Submission.Work.Tame.alphaI2LM_apply_eq_card
import Submission.Work.Tame.projEC_mul
import Submission.Work.Tame.projEC_one
import Submission.Work.Tame.alphaI1_isClassFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The T. I.-set step of Feit–Thompson Lemma 9.1 (derivation of (9.7), p. 806)

Feit–Thompson, in the proof of Lemma 9.1, use that "since `Ñ_i` is a T. I. set in `𝔛` with
`N(Ñ_i) = 𝔑_i` we get that `(α_{i1} - α_{i2})^*(A) = (α_{i1} - α_{i2})(A)`" (9.7), and they use the
same mechanism for the terms with `j ≠ i`.  The general statement is:

* if `ψ` is a class function of `𝔑_i`, if `ψ` vanishes off `Ñ_i^#`, and if `A ∈ Ñ_i^#`, then
  `Ind_{𝔑_i}^𝔛 ψ (A) = ψ(A)`,

i.e. `indFun_hatNp_apply` below.  Its proof only uses Definition 9.1(ii)(e)
(`conj_mem_hatNp_and_notMem`: `𝔑_i = N(Ñ_i)`, `Ñ_i^#` is a T. I. set):
for `x ∈ 𝔑_i` the summand is `ψ(xAx⁻¹) = ψ(A)` (`ψ` is a class function), and for `x ∉ 𝔑_i` we have
`xAx⁻¹ ∉ Ñ_i^#`, so the summand vanishes (`hψv`).

The second result, `indFun_alphaI1I2_apply_of_mem_hatNp`, specialises this to
`ψ = α_{i1} - α_{i2}` using `alphaI2LM_apply_eq_card` ((9.5)): for `A ∈ Ñ_i^#`,

`Ind_{𝔑_i}^𝔛 (α_{i1} - α_{i2}) (A) = α(πA) - #{k ∈ 𝔎_i | k A k⁻¹ = πA} · α(πA)`.

For `A ∈ 𝔏_i` (so that `A ∈ Ñ_i^#` and `π A = A`, `alphaI1LM_apply`) this is exactly Feit–Thompson
(9.7) together with (9.5).
-/

noncomputable section

open Classical

namespace Work.Tame

variable {X : Type*} [Group X] [Fintype X]

/-- **The T. I.-set induction step of Feit–Thompson Lemma 9.1** (p. 806, (9.7)).  Let `L̂` be
tamely imbedded in `X` with `𝔇 ≠ ∅`, `i` an index, `ψ` a class function of `𝔑_i = N(𝔎_i)` which
vanishes off `Ñ_i^#`.  Then for `A ∈ Ñ_i^#` one has `Ind_{𝔑_i}^𝔛 ψ (A) = ψ(A)`. -/
theorem indFun_hatNp_apply {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) (i : Fin n)
    {ψ : ↥(Lgrp (Hs i : Set X)) → ℂ} (hψc : CharCore.IsClassFun ψ)
    (hψv : ∀ N : ↥(Lgrp (Hs i : Set X)), (N : X) ∉ hatNp (Hs i) → ψ N = 0)
    {A : X} (hA : A ∈ hatNp (Hs i)) :
    Induction.indFun (Lgrp (Hs i : Set X)) ψ A = ψ ⟨A, (mem_hatNp_iff.mp hA).1⟩ := by
  classical
  obtain ⟨hmem, hnotMem⟩ := conj_mem_hatNp_and_notMem h hne i
  have hA1 : A ≠ 1 := (mem_punct.mp hA).2
  have hAmem : A ∈ Lgrp (Hs i : Set X) := (mem_hatNp_iff.mp hA).1
  -- each summand of the induction formula is `ψ A` when `x ∈ 𝔑_i`, and `0` otherwise
  have hstep : ∀ x : X,
      (if hx : x * A * x⁻¹ ∈ Lgrp (Hs i : Set X) then ψ ⟨x * A * x⁻¹, hx⟩ else 0)
        = (if hx : x ∈ Lgrp (Hs i : Set X) then ψ ⟨A, hAmem⟩ else 0) := by
    intro x
    by_cases hx : x ∈ Lgrp (Hs i : Set X)
    · have hxA : x * A * x⁻¹ ∈ hatNp (Hs i) := hmem x hx A hA
      have hxAK : x * A * x⁻¹ ∈ Lgrp (Hs i : Set X) := (mem_hatNp_iff.mp hxA).1
      rw [dif_pos hxAK, dif_pos hx]
      -- `ψ` is a class function of `𝔑_i`
      have hkey : (⟨x * A * x⁻¹, hxAK⟩ : ↥(Lgrp (Hs i : Set X)))
          = ⟨x, hx⟩ * ⟨A, hAmem⟩ * ⟨x, hx⟩⁻¹ := by
        ext
        simp [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hkey]
      exact hψc ⟨A, hAmem⟩ ⟨x, hx⟩
    · rw [dif_neg hx]
      by_cases hxA : x * A * x⁻¹ ∈ Lgrp (Hs i : Set X)
      · rw [dif_pos hxA]
        -- `x * A * x⁻¹ ∉ Ñ_i^#`, otherwise it contradicts (ii)(e)
        have hnot : x * A * x⁻¹ ∉ hatNp (Hs i) := by
          intro hconj
          have hxA' : x⁻¹ * (x * A * x⁻¹) * x = A := by group
          have hmem' : x⁻¹ * (x * A * x⁻¹) * x ∈ hatNp (Hs i) := by rw [hxA']; exact hA
          exact hnotMem x hx (x * A * x⁻¹) hconj hmem'
        rw [hψv ⟨x * A * x⁻¹, hxA⟩ hnot]
      · rw [dif_neg hxA]
  rw [Induction.indFun_apply_def, Finset.sum_congr rfl (fun x _ => hstep x)]
  -- the sum is now a constant sum over `↥(Lgrp Lhat)`
  have hcard : Nat.card ↥(Lgrp (Hs i : Set X)) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  have hsum : (∑ x : X, (if hx : x ∈ Lgrp (Hs i : Set X) then ψ ⟨A, hAmem⟩ else 0))
      = (Nat.card ↥(Lgrp (Hs i : Set X)) : ℂ) * ψ ⟨A, hAmem⟩ := by
    have h₁ : (∑ x : X, (if hx : x ∈ Lgrp (Hs i : Set X) then ψ ⟨A, hAmem⟩ else 0))
        = ∑ x : X, dite (x ∈ Lgrp (Hs i : Set X)) (fun _ => ψ ⟨A, hAmem⟩) (fun _ => 0) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hx : x ∈ Lgrp (Hs i : Set X) <;> simp [hx]
    rw [h₁, Induction.sum_dite_mem_subgroup (Lgrp (Hs i : Set X)) (fun _ => ψ ⟨A, hAmem⟩)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [hsum]
  have hne0 : (Nat.card ↥(Lgrp (Hs i : Set X)) : ℂ) ≠ 0 := by
    exact_mod_cast hcard
  rw [← mul_assoc, inv_mul_cancel₀ hne0, one_mul]

/-- **Feit–Thompson (9.7) for the correction terms.**  With `ψ = α_{i1} - α_{i2}` (so that `ψ`
vanishes off `Ñ_i^#` by `beta_eq_zero_of_notMem_hatNp`) the previous lemma gives, at `A ∈ Ñ_i^#`,

`Ind_{𝔑_i}^𝔛 (α_{i1} - α_{i2}) (A) = (α_{i1} - α_{i2})(A) = α(π A) - c · α(π A)`,

where `c` is the number of `k ∈ 𝔎_i` with `k A k⁻¹ = π A` (`= 1` when `A ∉ Ñ_i^#`). -/
theorem indFun_alphaI1I2_apply_of_mem_hatNp {Lhat : Set X} {n : ℕ} {Hs : Fin n → Subgroup X}
    (h : IsTamelyImbedded Lhat n Hs) (hne : (Dset Lhat).Nonempty) (i : Fin n)
    {α : ↥(Lgrp Lhat) → ℂ} (hα : α ∈ C0 Lhat) {A : X} (hA : A ∈ hatNp (Hs i)) :
    Induction.indFun (Lgrp (Hs i : Set X))
        (alphaI1LM Lhat (Hs i) α - alphaI2LM Lhat (Hs i) α) A
      = alphaI1LM Lhat (Hs i) α ⟨A, (mem_hatNp_iff.mp hA).1⟩
        - alphaI2LM Lhat (Hs i) α ⟨A, (mem_hatNp_iff.mp hA).1⟩ := by
  classical
  have hsup : Lgrp (Hs i : Set X) = Hs i ⊔ (Lgrp Lhat ⊓ Lgrp (Hs i : Set X)) :=
    h.supp_prod hne i
  have hinf : Hs i ⊓ Lgrp Lhat = ⊥ := h.supp_inf hne i
  refine indFun_hatNp_apply h hne i ?_ ?_ hA
  · -- `ψ = α_{i1} - α_{i2}` is a class function of `𝔑_i`
    exact (alphaI1_isClassFun hsup hinf hα.1).sub (Induction.isClassFun_indFun _ _)
  · -- and it vanishes off `Ñ_i^#`
    intro N hN
    have := beta_eq_zero_of_notMem_hatNp h hne hα i hN
    simpa [Pi.sub_apply] using this

end Work.Tame
