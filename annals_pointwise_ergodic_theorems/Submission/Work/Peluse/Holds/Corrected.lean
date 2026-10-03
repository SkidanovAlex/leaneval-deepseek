/- Peluse/Holds/Corrected.lean — LEAD-OWNED, FROZEN 2026-10-03 (curric-46). Corrected §5 statements (CONCAT_AUDIT_LEAD.md). Never drop the existential non-degeneracy constants (collapsed-window failures). -/
import Mathlib
import Submission.Work.Peluse.UControl.peluseLadderStrong
import Submission.Work.Peluse.Concat.Defs
import Submission.Work.Peluse.UControl.piecePetSetup

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.C46

noncomputable section
open Work.Peluse Work.Peluse.UControl

/-- Corrected first half of Thm 3.5 (expansion + Lemma 4.10), short window.
Changes vs `Holds.ExpansionPETShort`: `C₀` before the witnesses; `A` existential. -/
def ExpansionPETShortA : Prop :=
  ∀ s : ℕ, 1 ≤ s → ∀ C₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 1 ≤ A ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
    ∀ (c : ℤ), 0 < c → ∀ K : ℕ, K₀ ≤ K →
      ∀ (N M₁ M₂ : ℕ) (b : Fin s → ℤ) (δ δ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
        (∀ i : Fin s, |b i| ≤ (C₀ : ℤ) * (N : ℤ) / (M₁ : ℤ)) →
        SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < δ → δ ≤ 1 → 0 < δ' → A * δ' ≤ δ ^ K → A ≤ (M₂ : ℝ) * (δ * δ') ^ K →
        δ ≤ ((M₂ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₂,
          boxNorm s (fun i : Fin s => arithIcc (c * (a : ℤ) + b i) M₁) (symIcc N) f →
        ∃ ωOf : Fin (2 ^ s - 1) → (Fin s → Bool),
          Function.Injective ωOf ∧ (∀ i : Fin (2 ^ s - 1), ωOf i ≠ 0) ∧
          C * δ ^ K ≤ Concat.boxAvg s M₁ c ωOf (⌊δ' * (M₂ : ℝ)⌋).toNat N f

/-- Corrected second half of Thm 3.5 (the `s` applications of Lemma 5.6).
Changes vs `Holds.ConcatBridgeShort`: `A` existential (kills the collapsed corner
A = γ = γ' = M₂ = 1); output window `⌊γ'·γ'·M₁M₂⌋` (Lemma 5.6 multiplies the input window
by `γ''M₁` with `γ''` small, here `γ''` comparable to `γ'`); unused `b, C₀` dropped; `2 ≤ s'`. -/
def ConcatBridgeShortA : Prop :=
  ∀ s : ℕ, 1 ≤ s → ∀ C₁ : ℝ, 0 < C₁ →
    ∃ s' : ℕ, 2 ≤ s' ∧ ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 1 ≤ A ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
    ∀ (c : ℤ), 0 < c → ∀ K : ℕ, K₀ ≤ K →
      ∀ (N M₁ M₂ : ℕ) (γ γ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
        SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < γ → γ ≤ 1 → 0 < γ' → A * γ' ≤ γ ^ K → A ≤ (M₂ : ℝ) * (γ * γ') ^ K →
        (∃ ωOf : Fin (2 ^ s - 1) → (Fin s → Bool),
          Function.Injective ωOf ∧ (∀ i : Fin (2 ^ s - 1), ωOf i ≠ 0) ∧
          C₁ * γ ^ K ≤ Concat.boxAvg s M₁ c ωOf (⌊γ' * (M₂ : ℝ)⌋).toNat N f) →
        C * (γ * γ') ^ K ≤
          uNorm s' (arithIcc c (⌊γ' * γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) (symIcc N) f

/-- Corrected Lemma 5.7.  Changes vs `PeluseLadderStrong`: `C₀·γ' ≤ γ^K`;
non-degeneracy on `M₂` (the parameter window), not on `M₁M₂`; loss `c·(γγ')^K`. -/
def PeluseLadderA : Prop :=
  ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ) (kω : SlotSet ι k → ℕ)
    (p : ι → (Fin n → ℤ) → ℤ) (D : ℕ),
    ∃ (K : ℕ) (C₀ : ℝ) (t' : ℕ) (c : ℝ),
      1 ≤ K ∧ 0 < C₀ ∧ 1 ≤ t' ∧ 0 < c ∧
      ∀ (A : Finset (Fin n → ℤ)) (M₁ M₂ N : ℕ) (γ γ' : ℝ) (f : (Fin n → ℤ) → ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N →
        ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ)) →
        0 < γ → γ ≤ 1 → 0 < γ' → C₀ * γ' ≤ γ ^ K →
        (∀ i a, a ∈ A → 0 < p i a) →
        (∀ i a, a ∈ A → p i a * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ)) →
        (∀ i a, a ∈ A → |p i a| * (M₁ : ℤ) * (M₂ : ℤ) ≤ (D : ℤ) * (N : ℤ)) →
        (∀ a ∈ A, ∀ x, ‖f a x‖ ≤ 1) → (∀ a ∈ A, SupportIn (f a) N) →
        C₀ * (γ * γ') ^ (-(K : ℤ)) ≤ (M₂ : ℝ) →
        γ ≤ ((A.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
              ∑ a ∈ A, ∑ a' ∈ paramBox (k := k) M₂,
                boxNorm (Fintype.card (FamIdx kω))
                  (fun j : Fin (Fintype.card (FamIdx kω)) =>
                    pDirFam p M₁ a a' ((Fintype.equivFin (FamIdx kω)).symm j)) (symIcc N) (f a) →
        ∀ s₀ : Slot ι k,
          c * (γ * γ') ^ K ≤
            ((A.card : ℝ))⁻¹ * ((paramBox (k := k) M₂).card : ℝ)⁻¹ *
              ∑ a ∈ A, ∑ b ∈ paramBox (k := k) M₂,
                boxNorm (Fintype.card (ConclIdx s₀ kω t'))
                  (fun j : Fin (Fintype.card (ConclIdx s₀ kω t')) =>
                    conclDir p M₁ M₂ γ' s₀ t' a b
                      ((Fintype.equivFin (ConclIdx s₀ kω t')).symm j))
                  (symIcc N) (f a)

/-- Corrected Prop 3.6 (the ladder's delivered window).  Hypotheses verbatim `Prop36S`;
window `max 1 (η^K δ'^d M^d / A)` with the same existential `K, A`. -/
def Prop36SW (P : Polynomial ℤ) : Prop :=
  ∀ D : IdxDatum, ∃ s : ℕ, 2 ≤ s ∧
    ∀ A₀ : ℝ, 1 ≤ A₀ → ∃ A : ℝ, 1 ≤ A ∧ ∃ K : ℕ, 1 ≤ K ∧
    ∀ (N M : ℕ) (f : ℤ → ℂ) (η δ' : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ M →
      (N : ℝ) ≤ A₀ * (M : ℝ) ^ P.natDegree →
      (M : ℝ) ^ P.natDegree ≤ A₀ * (N : ℝ) →
      0 < η → η ≤ 1 → 0 < δ' → A * δ' ≤ η ^ K →
      2 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
      A * (η * δ') ^ (-(K : ℤ)) ≤ (N : ℝ) →
      η ≤ D.famAvg P.natDegree (⌊δ' * (M : ℝ)⌋).toNat P.leadingCoeff N f →
      η ^ K ≤ A * uNormPow s
        (arithIcc (P.natDegree.factorial * P.leadingCoeff)
          (⌊max (1 : ℝ) (η ^ K * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree / A)⌋).toNat)
        (symIcc N) f

/-! Interfaces for the dispatch (stubs, typecheck only). -/
end
end Work.Peluse.C46
