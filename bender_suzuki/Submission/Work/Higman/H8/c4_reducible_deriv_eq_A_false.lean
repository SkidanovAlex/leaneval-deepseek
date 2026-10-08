import Mathlib
import Submission.Work.Higman.MSA.lemma8_clean
import Submission.Work.Higman.H8.c4_sq_a2_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The `[E,E] = A` case of the `C₄` exclusion

This is the case of the `C₄` exclusion in which some `ξ`-invariant normal subgroup `E > A`
covering `A` has derived subgroup exactly `A`.  It is a short corollary of Higman's Lemma 8 in
the strong form (`Work.Higman.MSA.lemma8_clean`, axiom-clean): the conclusion of Lemma 8 is
`exp A ∣ 2`, i.e. `A ≤ Ω₁(P) = A² ≤ A`, contradicting `|A| = |Ω₁(P)|²` with
`|Ω₁(P)| ≥ 4`.
-/

namespace Work.Higman.H8

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-- **The `[E,E] = A` case of the `C₄` exclusion.**  Let `P` be a Suzuki 2-group, `A ⊴ P` a
`ξ`-invariant abelian normal subgroup with `Ω₁(P) ≤ A`, `A² = Ω₁(P)` and `|A| = |Ω₁(P)|²`, and
every square of `P` in `A`.  Let `E ⊴ P` be `ξ`-invariant with `A ≤ E`, `E ≠ A`, `E/A`
irreducible as a `ξ`-module (hypothesis `hcover`) and `[E,E] = A`.  Then `False`. -/
theorem c4_reducible_deriv_eq_A_false (h : Work.Higman.IsSuzuki2Grp P) {A E : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hEn : E.Normal) (hEinv : E.map (h.xi : MulAut P).toMonoidHom = E)
    (hAE : A ≤ E) (hEA : E ≠ A)
    (hcover : ∀ F : Subgroup P, F.Normal → F.map (h.xi : MulAut P).toMonoidHom = F →
      A ≤ F → F ≤ E → F = A ∨ F = E)
    (hEd : ⁅E, E⁆ = A) :
    False := by
  -- `E ^ (2) ≤ A`, since every square of `P` lies in `A`.
  have hE2 : Work.Higman.powSub E 2 ≤ A := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  -- Higman's Lemma 8 (strong form, axiom-clean): every element of `A` is an involution.
  have hexp : ∀ a ∈ A, a * a = 1 :=
    Work.Higman.MSA.lemma8_clean h hA hEn hEinv hAE hEA.symm hcover hE2 hEd
  -- Hence `A ≤ Ω₁(P) = A ^ (2) ≤ A`, so `|A| = |Ω₁(P)|`.
  have hAle : A ≤ Work.Higman.powSub A 2 := by
    rw [htop]
    intro a ha
    exact h.mem_omega1.mpr (by rw [pow_two]; exact hexp a ha)
  have hAeq : A = Work.Higman.powSub A 2 :=
    le_antisymm hAle (Work.Higman.powSub_le (n := 2) (by norm_num))
  have h1 : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
    congrArg (fun S : Subgroup P => Nat.card ↥S) hAeq
  have h2 : Nat.card ↥A = (Nat.card ↥A) ^ 2 := by
    rw [h1] at hcard
    rw [← htop] at hcard
    rw [h1]
    exact hcard
  have hge : 4 ≤ Nat.card ↥A := by
    rw [hAeq, htop]
    exact h.omega1_card_ge_four
  have hone : 1 < Nat.card ↥A := by omega
  have hlt : Nat.card ↥A < Nat.card ↥A * Nat.card ↥A :=
    calc Nat.card ↥A = Nat.card ↥A * 1 := (mul_one _).symm
      _ < Nat.card ↥A * Nat.card ↥A := Nat.mul_lt_mul_of_pos_left hone (by omega)
  have h3 : Nat.card ↥A * Nat.card ↥A = Nat.card ↥A := by
    rw [← pow_two]; exact h2.symm
  omega

end Work.Higman.H8
