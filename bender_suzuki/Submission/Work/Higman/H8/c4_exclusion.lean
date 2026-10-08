/-
# `c4_exclusion`: Higman 1963, Lemma 8, the case `C' = A` (the `C₄` case)

Target: `Work.Higman.H8.c4_exclusion` (statement unchanged, at the bottom of this file).
This is the last missing piece of Higman's `P' ≤ Ω₁` (`commutator_le_omega1`): the exclusion of
the `C₄` shape of the derived subgroup.  `no_square_of_maximal.lean` already imports this file.

## The proof

The full-strength form of Higman's Lemma 8 --- *if `A` is a normal abelian `ξ`-subgroup of a
Suzuki 2-group and `C > A` a normal `ξ`-subgroup covering `A` with `C ^ (2) ≤ A` and
`⁅C,C⁆ = A`, then `A` has exponent dividing `2`* --- is established in
`Submission/Work/Higman/MSA/lemma8_clean.lean` (`Work.Higman.MSA.lemma8_clean`, axiom-clean) on
top of the `𝔽₂[ξ]`-module package `Work.Higman.MSA.L8` and the multiplicative core
`Work.Higman.HS.core_mul` (Higman's §4 Lemma 6).

`c4_exclusion` is the `C = D` instance of that lemma:

* `A ≤ D ⊴ P` is `ξ`-invariant with `A ≠ D`, `D/A` minimal above `A` (`hcover`),
* `⁅D,D⁆ = A` (`hDd`), `[P,P] = A` (`hGs`) and every square of `P` lies in `A` (`hsq`), so that
  `D ^ (2) ≤ A`,
* `A ^ (2) = Ω₁(P) ≠ 1` (`htop`, `hA2ne`) and `A ≠ A ^ (2)` (`hAne2`).

`MSA.lemma8_clean` gives `a * a = 1` for every `a ∈ A`, i.e. `A ≤ Ω₁(P)`; with
`Ω₁(P) = A ^ (2) ≤ A` this forces `A = A ^ (2)`, contradicting `hAne2`.

## Remark

An earlier version of this file carried a long, self-contained development of the `𝔽₂[ξ]`-modules
`D/A` and `Ω₁(P)` with the maps `s`, `B`, `β` and a direct application of Higman's §4 Lemma 6.
That material has meanwhile been completed, in greater generality, in
`Submission/Work/Higman/MSA/` and `Submission/Work/Higman/HS/`, so it is no longer needed here;
the two helper declarations `xiSubAux`, `map_xi_subAux` are kept in case other modules refer to
them.
-/
import Mathlib
import Submission.Work.Higman.MSA.lemma8_clean
import Submission.Work.Higman.core_alt_pairing_new
import Submission.Work.Higman.no_square_derived
import Submission.Work.Higman.clo_setup
import Submission.Work.Higman.clo7_W_xi
import Submission.Work.Higman.nsd_transfer
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.powSub_normal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.H8.card_pow_of_irreducible
import Submission.Work.Higman.H8.pow4_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

-- `hGs`, `hA2ne` and the `A.Normal` instance of `map_xi_subAux` are hypotheses of the statement
-- (or of helper declarations) that the proof below does not need to mention.
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.Higman.H8

/-- The automorphism of `↥H` induced by `ξ` when `H` is `ξ`-invariant.
(Copied from `Submission/Work/Higman/xi_alt_pairing_false.lean`, which cannot be imported here
because it (transitively) imports this file.) -/
abbrev xiSubAux {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {H : Subgroup P} (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) : MulAut ↥H where
  toFun x := ⟨h.xi (x : P), by
    have hx := Subgroup.mem_map_of_mem ((h.xi : MulAut P).toMonoidHom) x.2
    rwa [hinv] at hx⟩
  invFun x := ⟨(h.xi : MulAut P).symm (x : P),
    Work.Higman.symm_mem_of_map_eq (h.xi : MulAut P) hinv x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

theorem xiSubAux_apply {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {H : Subgroup P} (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (x : ↥H) :
    ((xiSubAux h hinv x : ↥H) : P) = h.xi (x : P) := rfl

theorem xiSubAux_pow_apply {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {H : Subgroup P} (hinv : H.map (h.xi : MulAut P).toMonoidHom = H) (k : ℕ) (x : ↥H) :
    (((xiSubAux h hinv) ^ k) x : P) = (h.xi ^ k) (x : P) := by
  revert x
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih (xiSubAux h hinv x), xiSubAux_apply, pow_succ,
        MulAut.mul_apply]

/-- The automorphism of `↥D ⧸ A.subgroupOf D` induced by `ξ`. -/
theorem map_xi_subAux {P : Type} [Group P] [Finite P] {h : Work.Higman.IsSuzuki2Grp P}
    {A D : Subgroup P} [hAn : A.Normal]
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) :
    Subgroup.map (xiSubAux h hDinv : ↥D ≃* ↥D) (A.subgroupOf D) = A.subgroupOf D := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show ((xiSubAux h hDinv y : ↥D) : P) ∈ A
    rw [xiSubAux_apply]
    rw [← hAinv]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hy)
  · intro hx
    refine ⟨(xiSubAux h hDinv)⁻¹ x, ?_, by simp⟩
    show ((xiSubAux h hDinv)⁻¹ x : ↥D) ∈ A.subgroupOf D
    rw [Subgroup.mem_subgroupOf]
    have h2 : (((xiSubAux h hDinv)⁻¹ x : ↥D) : P) = (h.xi : MulAut P).symm (x : P) := rfl
    rw [h2]
    exact Work.Higman.symm_mem_of_map_eq (h.xi : MulAut P) hAinv
      (Subgroup.mem_subgroupOf.mp hx)

/-- **Higman 1963, Lemma 8, the case `C' = A`, in the `C₄` (unipotent) setting.** -/
theorem c4_exclusion {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A ≤ D) (hADne : D ≠ A)
    (hDd : ⁅D, D⁆ = A)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ D → E = A ∨ E = D)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA2ne : Work.Higman.powSub A 2 ≠ ⊥)
    (hAne2 : A ≠ Work.Higman.powSub A 2) :
    False := by
  -- Every square of `P` lies in `A`, hence `D ^ (2) ≤ A`.
  have hsqD : Work.Higman.powSub D 2 ≤ A := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  -- **Higman's Lemma 8** (`Submission/Work/Higman/MSA/lemma8_clean.lean`, proved and
  -- axiom-clean): in this configuration every element of `A` is an involution.
  have hexp : ∀ a ∈ A, a * a = 1 :=
    Work.Higman.MSA.lemma8_clean h hA hDn hDinv hAD (Ne.symm hADne) hcover hsqD hDd
  -- Hence `A ≤ Ω₁(P) = A ^ (2) ≤ A`, so `A = A ^ (2)`, contradicting `hAne2`.
  refine hAne2 (le_antisymm ?_ (Work.Higman.powSub_le (by norm_num)))
  intro a ha
  rw [htop]
  exact h.mem_omega1.mpr (by rw [pow_two]; exact hexp a ha)

end Work.Higman.H8
