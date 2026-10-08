import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.Lambda
import Submission.Work.BG.H0Conj
import Submission.Work.BG.CharBridge
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.lemma17_ii_aux
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedCharacter

/-!
# Area BG: infrastructure for Bender–Glauberman 1981, Lemma 1.7(iii)

This module collects the small structural facts needed for the proof of
`Work.BG.Lemma17iiiProp` (`Submission/Work/BG/lemma17_iii.lean`), in the vocabulary of
`Work.BG.Hyp12` and the conjugation action `ν ↦ ν^s` of `Work.BG.conjByH`:

* `Work.BG.U_conj_mem`, `Work.BG.U_conj_mem_inv` — **`H` normalises `U`**, which follows from
  the Hypothesis-1.2 condition `N_G(T) = H` with `T = H₀ ∖ U`: conjugating `u ∈ U ⊆ H₀` by
  `s ∈ H` stays in `H₀`, and cannot land in `T`, hence stays in `U`.  This is what makes the
  `s`-action descend to `H₀/U` and hence fixes the characters of `H₀/U`.
* `Work.BG.inner_induce_eq_inner_restrict_flip` — Frobenius reciprocity in the order needed by
  Lemma 1.7(iii), where the induced class function is the *second* argument of `inner`
  (`inner` is star-symmetric: `ClassFunction.inner_star_comm`).
* `Work.BG.inner_conjByH_eq` — `inner φ (ψ^s) = inner φ ψ` whenever `φ` is `s`-invariant: the
  inner product is invariant under the conjugation automorphism `conjMulEquiv P s`
  (`ClassFunction.inner_compHom_mulEquiv`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-! ### `H` normalises `U` -/

/-- **`H` normalises `U`.**  Since `N_G(T) = H` (Hypothesis 1.2) and `T = H₀ ∖ U`, an element
`s ∈ H` maps `u ∈ U ⊆ H₀` into `H₀` (as `H₀ ⊴ H`) and cannot map it into `T` (or `T` would
meet its conjugate), so it stays in `U`. -/
theorem U_conj_mem (P : Hyp12 G) (s : ↥P.H) {u : G} (hu : u ∈ P.U) :
    (s : G) * u * (s : G)⁻¹ ∈ P.U := by
  have hs : (s : G) ∈ Subgroup.normalizer (Tset P.H0 P.U : Set G) := by
    rw [P.normalizer_T]; exact s.2
  have hiff : ∀ x : G, x ∈ Tset P.H0 P.U ↔ (s : G) * x * (s : G)⁻¹ ∈ Tset P.H0 P.U :=
    Subgroup.mem_set_normalizer_iff.mp hs
  have hH0 : (s : G) * u * (s : G)⁻¹ ∈ P.H0 := H0_conj_mem P (P.U_le_H0 hu) s
  by_contra hU
  have hnot : u ∉ Tset P.H0 P.U := fun h => h.2 hu
  exact hnot ((hiff u).mpr (show (s : G) * u * (s : G)⁻¹ ∈ Tset P.H0 P.U from ⟨hH0, hU⟩))

/-- The same with `s⁻¹` (equivalently: conjugation by `s` preserves `U`). -/
theorem U_conj_mem_inv (P : Hyp12 G) (s : ↥P.H) {u : G} (hu : u ∈ P.U) :
    (s : G)⁻¹ * u * (s : G) ∈ P.U := by
  have h := U_conj_mem P s⁻¹ hu
  simpa using h

/-- Conjugation by `s ∈ H` preserves the normal subgroup `U` of `H₀`. -/
theorem mem_U_conj_iff (P : Hyp12 G) (s : ↥P.H) (u : G) :
    (s : G) * u * (s : G)⁻¹ ∈ P.U ↔ u ∈ P.U := by
  constructor
  · intro h
    have h' := U_conj_mem_inv P s h
    have heq : (s : G)⁻¹ * ((s : G) * u * (s : G)⁻¹) * (s : G) = u := by group
    rwa [heq] at h'
  · intro h
    exact U_conj_mem P s h

/-! ### Frobenius reciprocity with the induced class function on the right -/

/-- **Frobenius reciprocity, flipped.**  `⟨χ, θ^G⟩_G = ⟨χ|_{H₀}, θ⟩_{H₀}`: the library's
`ClassFunction.inner_induce_eq_inner_restrict` has the induced class function on the *left*,
and `ClassFunction.inner_star_comm` star-symmetry gives the mirrored form. -/
theorem inner_induce_eq_inner_restrict_flip (H : Subgroup G) [Fintype G] [Fintype H]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]
    (θ : ClassFunction ↥H ℂ) (χ : ClassFunction G ℂ) :
    ClassFunction.inner χ (ClassFunction.induce H θ) =
      ClassFunction.inner (ClassFunction.restrict H χ) θ := by
  calc ClassFunction.inner χ (ClassFunction.induce H θ)
      = star (ClassFunction.inner (ClassFunction.induce H θ) χ) :=
        ClassFunction.inner_star_comm _ _
    _ = star (ClassFunction.inner θ (ClassFunction.restrict H χ)) := by
        rw [ClassFunction.inner_induce_eq_inner_restrict]
    _ = ClassFunction.inner (ClassFunction.restrict H χ) θ := by
        rw [ClassFunction.inner_star_comm]
        exact star_star (ClassFunction.inner (ClassFunction.restrict H χ) θ)

/-! ### Invariance of `inner` under `ν ↦ ν^s` -/

theorem conjByH_one (P : Hyp12 G) (ν : ClassFunction ↥P.H0 ℂ) :
    conjByH P 1 ν = ν := by
  ext h
  show ν (conjMulEquiv P 1 h) = ν h
  exact congrArg ν (by apply Subtype.ext; rw [conjMulEquiv_apply]; simp)

/-- `inner φ (ψ^s) = inner φ ψ` for an `s`-invariant `φ`: both sides are the pairing with the
pullback along the conjugation isomorphism `conjMulEquiv P s`, and the inner product is
invariant under pullback along a group isomorphism. -/
theorem inner_conjByH_eq (P : Hyp12 G) [Fintype ↥P.H0]
    [Invertible (Nat.card ↥P.H0 : ℂ)]
    (s : ↥P.H) {φ : ClassFunction ↥P.H0 ℂ} (hφ : conjByH P s⁻¹ φ = φ)
    (ψ : ClassFunction ↥P.H0 ℂ) :
    ClassFunction.inner φ (conjByH P s ψ) = ClassFunction.inner φ ψ := by
  have h2 : conjByH P s⁻¹ (conjByH P s ψ) = ψ := by
    have hm := conjByH_mul P s s⁻¹ ψ
    rw [mul_inv_cancel, conjByH_one] at hm
    exact hm.symm
  calc ClassFunction.inner φ (conjByH P s ψ)
      = ClassFunction.inner (conjByH P s⁻¹ φ) (conjByH P s⁻¹ (conjByH P s ψ)) :=
        (ClassFunction.inner_compHom_mulEquiv (H := ↥P.H0) (G := ↥P.H0)
          (conjMulEquiv P s⁻¹) φ (conjByH P s ψ)).symm
    _ = ClassFunction.inner φ ψ := by rw [hφ, h2]

end Work.BG
