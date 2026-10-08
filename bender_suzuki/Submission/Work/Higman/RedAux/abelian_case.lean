import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.MSA.exp_four
import Submission.Work.Higman.higman_lemma3_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

namespace Work.Higman.RedAux

/-- **The abelian sub-case of the `C₄` exclusion** (Higman 1963, Lemma 8, the configuration
`E' = 1`, `E² = A`, `E ≅ (ℤ/8)ⁿ`, `C_P(A) = E`).

`P` is a Suzuki 2-group, `A` a `ξ`-invariant abelian normal subgroup with `Ω₁(P) ≤ A`,
`[P,P] = A`, every square of `P` in `A`, `A⁴ = 1`, `A² = Ω₁(P)`, `|A| = |Ω₁(P)|²`, and
`A < E ≤ P` where `E` is `ξ`-invariant, abelian, with `E² = A` and `E/A` irreducible as a
`𝔽₂⟨ξ⟩`-module (no `ξ`-invariant `A ≤ F ≤ E` other than `A` and `E`).

These hypotheses force `|E| = |Ω₁(P)|³` and `E ≅ (ℤ/8)ⁿ`; the whole configuration is
contradictory (it would give a Suzuki 2-group of order `> |Ω₁(P)|³`). -/
theorem abelian_case {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A E : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : commutator P = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hAE : A ≤ E) (hEne : E ≠ A)
    (hEinv : E.map (h.xi : MulAut P).toMonoidHom = E)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : Work.Higman.powSub E 2 = A)
    (hEirr : ∀ F : Subgroup P, A ≤ F → F ≤ E → F.map (h.xi : MulAut P).toMonoidHom = F →
      F = A ∨ F = E) :
    False := by
  -- `[P,E] ≤ [P,P] = A ≤ E`.
  have hUE : ⁅(⊤ : Subgroup P), E⁆ ≤ A := by
    calc ⁅(⊤ : Subgroup P), E⁆ ≤ ⁅(⊤ : Subgroup P), ⊤⁆ := Subgroup.commutator_mono le_rfl le_top
      _ = commutator P := rfl
      _ = A := hGs
  -- hence `E` is normal: `g * e * g⁻¹ = ⁅g,e⁆ * e ∈ E`.
  have hEn : E.Normal :=
    Subgroup.Normal.mk fun n hn g => by
      have h1 : ⁅g, n⁆ ∈ E :=
        hAE (hUE (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hn))
      rw [show g * n * g⁻¹ = ⁅g, n⁆ * n from by rw [commutatorElement_def]; group]
      exact E.mul_mem h1 hn
  -- `E ≠ ⊤`, because `P` is non-abelian while `E` is abelian.
  have hEtop : E ≠ ⊤ := by
    intro htop'
    obtain ⟨x, y, hxy⟩ := h.noncomm
    exact hxy (hEab x (htop' ▸ Subgroup.mem_top x) y (htop' ▸ Subgroup.mem_top y))
  -- a minimal `ξ`-invariant normal subgroup `C` with `E < C ≤ P`
  obtain ⟨C, hCn, hCinv, hEC, -, hCE, hcover⟩ :=
    Work.Higman.MSA.exists_minimal_covering h (A := E) (M := ⊤) Subgroup.normal_top
      (by rw [Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]) le_top hEtop.symm
  -- `Φ(C) = E²`: squares of `C` and commutators of `C` lie in `A = E²`, and `E ≤ C`.
  have hPhi : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = Work.Higman.powSub E 2 := by
    refine le_antisymm (sup_le ?_ ?_) (le_sup_of_le_left (Work.Higman.powSub_mono hEC))
    · rw [Work.Higman.powSub, Subgroup.closure_le]
      rintro y ⟨x, -, rfl⟩
      rw [hE2]
      exact hsq x
    · calc ⁅C, C⁆ ≤ ⁅(⊤ : Subgroup P), ⊤⁆ := Subgroup.commutator_mono le_top le_top
        _ = commutator P := rfl
        _ = A := hGs
        _ = Work.Higman.powSub E 2 := hE2.symm
  -- Higman's Lemma 3 for the pair `E < C`: `E` has exponent dividing `4`.
  have hExp4 : ∀ a ∈ E, a ^ 4 = 1 :=
    Work.Higman.higman_lemma3_aux h ⟨hEn, hEinv, hEab⟩ hCn hCinv hEC hCE.symm hcover hPhi
  have hE4 : Work.Higman.powSub E 4 = ⊥ :=
    Work.Higman.MSA.powSub_four_bot_of_pow_four_eq_one hEab hExp4
  -- hence `A² = (E²)² = E⁴ = 1`, so `Ω₁(P) = 1`, contradicting `|Ω₁(P)| ≥ 4`.
  have hbot : Work.Higman.omega1 P = ⊥ := by
    rw [← htop]
    rw [← hE2, Work.Higman.powSub_powSub hEab 2 2, show (2 : ℕ) * 2 = 4 from by norm_num, hE4]
  have hcard1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [hbot, Subgroup.card_bot]
  have h4 := h.omega1_card_ge_four
  omega

end Work.Higman.RedAux
