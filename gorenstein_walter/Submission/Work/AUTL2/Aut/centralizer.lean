/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 : the centralizer of `PSL(2,q)` on the projective line is trivial

Step A6/transfer of the area `Submission/Work/AUTL2/` uses the fact that the permutation
group `pslImage F ≤ Sym(ℙ¹(F))` has trivial centralizer (`C_{Sym}(L) = 1` is the hypothesis
under which the conjugation map `N(L)/C(L) → Aut(L)` is injective). Here we prove it.

The argument is elementary and uses only the three standard Möbius elements
`transl b : x ↦ x + b`, `dil a : x ↦ a²x` and (implicitly) the fact that a permutation
commuting with the translation group is affine:

* a permutation `σ` commuting with `transl b` for every `b ∈ F` satisfies
  `σ (x + b) = σ x + b`; since `σ` is injective this forces `σ ∞ = ∞` and `σ x ≠ ∞` for
  finite `x`, so `σ` restricted to `F` is `x ↦ x + c` with `c = σ 0`;
* `σ` also commutes with `dil a` (`x ↦ a²x`, `a ∈ Fˣ`), whence `c = a² c`; as soon as some
  unit has `a² ≠ 1` (which holds e.g. if `F` has at least four elements) this gives `c = 0`,
  so `σ` fixes `F` pointwise and, being a bijection, also `∞`.

The main theorem `Work.AUTL2.Aut.centralizer` specialises this to `F = GaloisField p k`,
`p` odd, `p^k ≥ 5`.
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Mobius
import Submission.Work.AUTL2.Stabilizer

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.AUTL2.Aut

open Work.AUTL2

/-- **The centralizer of `PSL(2,F)` on `ℙ¹(F)` is trivial**, as soon as `F` contains a unit `a`
with `a² ≠ 1` (in particular, always when `F` has at least four elements).

A permutation `σ` of `ℙ¹(F)` commuting with the image of `PSL(2,F)` commutes with all the
translations `x ↦ x + b` and all the dilations `x ↦ a²x`; these two families already force
`σ = 1`. -/
theorem centralizer_pslImage_eq_bot {F : Type*} [Field F] [DecidableEq F]
    (h : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    Subgroup.centralizer (pslImage F : Set (Equiv.Perm (P1 F))) = ⊥ := by
  classical
  obtain ⟨a₀, ha₀, ha₀sq⟩ := h
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  rw [Subgroup.mem_centralizer_iff] at hσ
  -- `σ` commutes with every element of `pslImage F`, in particular with the translations
  -- and the dilations.
  have htr : ∀ b : F, σ * transl F b = transl F b * σ :=
    fun b => (hσ _ (transl_mem F b)).symm
  have key : ∀ (b : F) (x : P1 F), σ (transl F b x) = transl F b (σ x) := by
    intro b x
    have h1 := congrArg (fun f : Equiv.Perm (P1 F) => f x) (htr b)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h1
    exact h1
  -- Step 1: `σ` fixes `∞`.
  have hinf : σ ∞ = ∞ := by
    by_contra hne
    obtain ⟨p, hp⟩ := σ.surjective ∞
    have hp_ne : p ≠ ∞ := by
      intro hpp; rw [hpp] at hp; exact hne hp
    obtain ⟨x₀, hx₀'⟩ := OnePoint.ne_infty_iff_exists.1 hp_ne
    have hx₀ : σ (x₀ : P1 F) = ∞ := by rw [hx₀']; exact hp
    have h1 := key 1 (x₀ : P1 F)
    rw [hx₀, transl_infty] at h1
    have h2 : transl F 1 (x₀ : P1 F) = (x₀ : P1 F) := σ.injective (by rw [h1, hx₀])
    exact OnePoint.coe_ne_infty x₀ (transl_fixed F 1 one_ne_zero (x₀ : P1 F) h2)
  -- Step 2: `σ` maps the finite points to finite points.
  have hfin : ∀ x : F, ∃ y : F, σ (x : P1 F) = (y : P1 F) := by
    intro x
    have hne : σ (x : P1 F) ≠ ∞ := by
      intro hx
      have h1 := key 1 x
      rw [hx, transl_infty] at h1
      have h2 : transl F 1 (x : P1 F) = (x : P1 F) := σ.injective (by rw [h1, hx])
      exact OnePoint.coe_ne_infty x (transl_fixed F 1 one_ne_zero (x : P1 F) h2)
    obtain ⟨y, hy⟩ := OnePoint.ne_infty_iff_exists.1 hne
    exact ⟨y, hy.symm⟩
  choose d hd using hfin
  -- Step 3: the affine relation `σ (x + b) = σ x + b`.
  have hrel : ∀ x b : F, d (x + b) = d x + b := by
    intro x b
    have h1 := key b (x : P1 F)
    rw [transl_formula, hd x, transl_formula] at h1
    rw [hd (x + b)] at h1
    exact (OnePoint.some_eq_iff _ _).1 h1
  have hdx : ∀ x : F, d x = d 0 + x := by
    intro x; simpa using hrel 0 x
  -- Step 4: commuting with a dilation whose square is not `1` kills the translation part.
  have hc : d 0 = 0 := by
    have hdl : σ * dil F (Units.mk0 a₀ ha₀) = dil F (Units.mk0 a₀ ha₀) * σ :=
      (hσ _ (dil_mem F (Units.mk0 a₀ ha₀))).symm
    have h1 := congrArg (fun f : Equiv.Perm (P1 F) => f ((0 : F) : P1 F)) hdl
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h1
    rw [dil_formula, mul_zero, hd 0, dil_formula] at h1
    have h2 : d 0 = ((Units.mk0 a₀ ha₀ : Fˣ) : F) ^ 2 * d 0 :=
      (OnePoint.some_eq_iff _ _).1 h1
    have hu2 : ((Units.mk0 a₀ ha₀ : Fˣ) : F) ^ 2 - 1 ≠ 0 := by
      simpa using sub_ne_zero.mpr ha₀sq
    have h3 : (((Units.mk0 a₀ ha₀ : Fˣ) : F) ^ 2 - 1) * d 0 = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr h2.symm
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 hu2
    · exact h4
  -- Step 5: conclusion.
  have hσid : σ = 1 := by
    apply Equiv.ext
    rw [OnePoint.forall]
    refine ⟨?_, fun y => ?_⟩
    · rw [hinf, Equiv.Perm.one_apply]
    · rw [hd y, hdx y, hc, zero_add, Equiv.Perm.one_apply]
  exact hσid

/-- A finite field with at least four elements contains an element `a ≠ 0` with `a ^ 2 ≠ 1`:
the units with `a ^ 2 = 1` all satisfy `(a - 1) * (a + 1) = 0`, hence lie in `{1, -1}`, of
which there are at most two, while `Fˣ` has `|F| - 1 ≥ 3` elements. -/
theorem exists_sq_ne_one_of_card {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hcard : 4 ≤ Fintype.card F) : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  by_contra h
  have h' : ∀ a : F, a ≠ 0 → a ^ 2 = 1 := by
    intro a ha
    by_contra h2
    exact h ⟨a, ha, h2⟩
  have hunit : ∀ a : Fˣ, a = 1 ∨ a = -1 := by
    intro a
    have h0 : (a : F) ^ 2 = 1 := h' a (Units.ne_zero a)
    have h2 : (((a : F) - 1) * ((a : F) + 1)) = 0 := by
      have hh : ((a : F) - 1) * ((a : F) + 1) = (a : F) ^ 2 - 1 := by ring
      rw [hh, h0, sub_self]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · left; exact Units.ext (sub_eq_zero.1 h3)
    · right; exact Units.ext (add_eq_zero_iff_eq_neg.1 h3)
  have hsub : (Finset.univ : Finset Fˣ) ⊆ ({1, -1} : Finset Fˣ) := by
    intro a _
    rcases hunit a with h1 | h1 <;> simp [h1]
  have hle : Fintype.card Fˣ ≤ 2 := by
    have h4 := Finset.card_le_card hsub
    simp only [Finset.card_univ] at h4
    have h5 : ({1, -1} : Finset Fˣ).card ≤ 2 := by
      calc ({1, -1} : Finset Fˣ).card ≤ ({-1} : Finset Fˣ).card + 1 :=
            Finset.card_insert_le 1 ({-1} : Finset Fˣ)
        _ = 2 := by simp
    omega
  have h6 := Fintype.card_units F
  omega

/-- **Step A6 of the AUTL2 design**: the centralizer of `pslImage (GaloisField p k)` in the
symmetric group on the projective line is trivial, for `p` odd and `p ^ k ≥ 5`.

This is the hypothesis `C_Q(L) = 1` of the transfer argument, transported to the explicit
permutation model. -/
theorem centralizer (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    [DecidableEq (GaloisField p k)] (hp : Odd p) (hq : 5 ≤ p ^ k) :
    Subgroup.centralizer (Work.AUTL2.pslImage (GaloisField p k) :
      Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) = ⊥ := by
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  have h1 : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk
  have h2 : Nat.card (GaloisField p k) = Fintype.card (GaloisField p k) :=
    Nat.card_eq_fintype_card
  have hcard : 4 ≤ Fintype.card (GaloisField p k) := by omega
  exact centralizer_pslImage_eq_bot (F := GaloisField p k)
    (exists_sq_ne_one_of_card (F := GaloisField p k) hcard)

end Work.AUTL2.Aut
