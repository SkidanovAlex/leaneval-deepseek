import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory

/-!
# X1 (`ConstituentSumProp`): the constituent sum identity

For a finite group `K` and class functions `ε i ∈ ±Irr(K)` (`i : ι`),

`Σ_{χ ∈ Irr K} χ(g)²/χ(1) · (Σ_i ε i, χ) = Σ_i ε i(g)²/ε i(1)`.

This is pure character theory (linearity of `ClassFunction.inner` plus the first
orthogonality relation `irreducibleCharacter_inner_eq_ite`): expanding the inner
product turns it into `Σ_i Σ_χ χ(g)²/χ(1) · (ε i, χ)`, and for each `i` the inner
sum is `ε i(g)² / ε i(1)` because `ε i` is `±` an irreducible character — the sign
disappears in the numerator (`(-a)^2 = a^2`) and inverts twice in the denominator
(`a / -b = -(a / b)`).
-/

/-- Left-linearity of the class-function pairing over a `Finset.univ`-sum. -/
private lemma inner_univ_sum {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    {ι : Type} [Fintype ι] (ε : ι → ClassFunction K ℂ) (ψ : ClassFunction K ℂ) :
    ClassFunction.inner (∑ i, ε i) ψ = ∑ i, ClassFunction.inner (ε i) ψ := by
  have h := inner_sum_left (G := K) (s := Finset.univ) ε ψ
  simpa using h

/-- **X1, one constituent.** For `φ ∈ ±Irr(K)` and any `g`,
`Σ_χ χ(g)²/χ(1) · (φ, χ) = φ(g)²/φ(1)`. -/
private lemma constituent_term {K : Type} [Group K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    [Fintype (IrreducibleCharacter K)] (φ : ClassFunction K ℂ) (hφ : IsPmIrr φ) (g : K) :
    ∑ χ : IrreducibleCharacter K,
        (χ : ClassFunction K ℂ) g ^ 2 / (χ : ClassFunction K ℂ) 1 *
          ClassFunction.inner φ (χ : ClassFunction K ℂ) =
      φ g ^ 2 / φ 1 := by
  classical
  rcases hφ with hirr | hneg
  · -- `φ` is irreducible: `(φ, χ) = δ_{φ,χ}`, so only the `χ = φ` term survives.
    have hinner : ∀ χ : IrreducibleCharacter K,
        ClassFunction.inner φ (χ : ClassFunction K ℂ) =
          if χ = (⟨φ, hirr⟩ : IrreducibleCharacter K) then 1 else 0 := by
      intro χ
      have h := irreducibleCharacter_inner_eq_ite (⟨φ, hirr⟩ : IrreducibleCharacter K) χ
      rw [IrreducibleCharacter.coe_mk] at h
      rw [h]
      by_cases hc : (⟨φ, hirr⟩ : IrreducibleCharacter K) = χ
      · rw [ite_eq_left hc, ite_eq_left hc.symm]
      · rw [ite_eq_right hc,
          ite_eq_right (fun hh : χ = (⟨φ, hirr⟩ : IrreducibleCharacter K) => hc hh.symm)]
    rw [Finset.sum_eq_single (⟨φ, hirr⟩ : IrreducibleCharacter K)]
    · rw [hinner, ite_eq_left rfl, mul_one]
    · intro b _ hb
      rw [hinner b, ite_eq_right hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · -- `-φ` is irreducible: `(φ, χ) = -δ_{-φ,χ}`, so only the `χ = -φ` term survives.
    have hinner : ∀ χ : IrreducibleCharacter K,
        ClassFunction.inner φ (χ : ClassFunction K ℂ) =
          -(if χ = (⟨-φ, hneg⟩ : IrreducibleCharacter K) then 1 else 0) := by
      intro χ
      have h := irreducibleCharacter_inner_eq_ite (⟨-φ, hneg⟩ : IrreducibleCharacter K) χ
      rw [IrreducibleCharacter.coe_mk] at h
      have h2 := ClassFunction.inner_neg_left (G := K) (k := ℂ) φ (χ : ClassFunction K ℂ)
      rw [h2] at h
      have h3 : (if (⟨-φ, hneg⟩ : IrreducibleCharacter K) = χ then (1 : ℂ) else 0) =
          (if χ = (⟨-φ, hneg⟩ : IrreducibleCharacter K) then 1 else 0) := by
        by_cases hc : χ = (⟨-φ, hneg⟩ : IrreducibleCharacter K)
        · rw [ite_eq_left hc, ite_eq_left hc.symm]
        · rw [ite_eq_right hc,
            ite_eq_right (fun hh : (⟨-φ, hneg⟩ : IrreducibleCharacter K) = χ => hc hh.symm)]
      rw [h3] at h
      exact neg_eq_iff_eq_neg.mp h
    rw [Finset.sum_eq_single (⟨-φ, hneg⟩ : IrreducibleCharacter K)]
    · rw [hinner, ite_eq_left rfl]
      simp only [IrreducibleCharacter.coe_mk, ClassFunction.neg_apply, neg_sq, div_neg,
        neg_mul_neg, mul_one]
    · intro b _ hb
      rw [hinner b, ite_eq_right hb]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem constituentSum : Work.GW2.C16.ConstituentSumProp := by
  classical
  intro K _hK _hF _hInv _hIrr ι _hι ε hε g
  -- left-linearity of the pairing in the expanded `(Σ_i ε i, χ)`
  have hstep : ∀ χ : IrreducibleCharacter K,
      ClassFunction.inner (∑ i, ε i) (χ : ClassFunction K ℂ) =
        ∑ i, ClassFunction.inner (ε i) (χ : ClassFunction K ℂ) := by
    intro χ
    exact inner_univ_sum ε (χ : ClassFunction K ℂ)
  calc ∑ χ : IrreducibleCharacter K,
        (χ : ClassFunction K ℂ) g ^ 2 / (χ : ClassFunction K ℂ) 1 *
          ClassFunction.inner (∑ i, ε i) (χ : ClassFunction K ℂ)
      = ∑ χ : IrreducibleCharacter K,
          (χ : ClassFunction K ℂ) g ^ 2 / (χ : ClassFunction K ℂ) 1 *
            (∑ i, ClassFunction.inner (ε i) (χ : ClassFunction K ℂ)) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [hstep χ]
    _ = ∑ χ : IrreducibleCharacter K,
          ∑ i, (χ : ClassFunction K ℂ) g ^ 2 / (χ : ClassFunction K ℂ) 1 *
            ClassFunction.inner (ε i) (χ : ClassFunction K ℂ) := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i, ∑ χ : IrreducibleCharacter K,
          (χ : ClassFunction K ℂ) g ^ 2 / (χ : ClassFunction K ℂ) 1 *
            ClassFunction.inner (ε i) (χ : ClassFunction K ℂ) := by
        rw [Finset.sum_comm]
    _ = ∑ i, ε i g ^ 2 / ε i 1 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact constituent_term (ε i) (hε i) g

end Work.BG
