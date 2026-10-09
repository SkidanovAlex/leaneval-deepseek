/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proposition 7 (i) for the paper's own group `F(m)/F(m)^{(ν)} ⋊ G`

This is the end point of the concrete construction in `SemidirectData.lean`: Schmidt–Wingberg's
Proposition 7 (i) for the cohomology of the paper's own group
`Γ_m = F(m)/F(m)^{(i,j)} ⋊ G` with coefficients in `E(m,τ) ⊗ T`, where `E(m,τ)` is the graded
piece `F(m)^{(i,j)}/F(m)^{(i,j)+1}` and `T` is an `𝔽_p[G]`-module.

Unlike `Work.CohomologicalShrinking.exists_shrinking_H1_semidirect` (which is stated for an
abstract model `Z m` of `H₁(Γ_m, E⊗T)`), the group `Z m` here *is* the group homology of the
semidirect product built in this chapter, the exactness and the surjectivity of the
Hochschild–Serre sequence are *proved* (`SemidirectData.semidirectShrinkingData_of`), and the
operator maps produced are the paper's `Φ : F(m) ⇢ F(n)` acting on that homology via `flowZMap`.

The remaining inputs are the ones isolated in `semidirectShrinkingData_of`: the identification of
the image of the paper's `α` with the image of the corestriction, the naturality in the rank of
`α` and `β`, and the paper's recalled `H^{-2} = H₁` (as an isomorphism `γ`).
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.SemidirectData
import Submission.Work.CohomologicalShrinking.exists_bridge
import Submission.Work.CohomologicalShrinking.exists_natural_alpha
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

open scoped TensorProduct

universe u

variable {p : ℕ}

/-- **Proposition 7 (i) of Schmidt–Wingberg for the paper's own group** `F(m)/F(m)^{(ν)} ⋊ G`.
-/
theorem exists_shrinking_H1_semidirect_concrete (p : ℕ) [Fact p.Prime] (G : Type) [Group G]
    [Fintype G] {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (α : ∀ m : ℕ, (squareQuotient p G m ⊗[ZMod p] (E p G m i j ⊗[ZMod p] T)) →+
      (↑(groupHomology.H1 (flowRep p G m i j T)) : Type))
    (hαrange : ∀ m : ℕ, (α m).range = (flowHSα p G i j T m).range)
    (hαnat : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n)
      (x : squareQuotient p G m ⊗[ZMod p] (E p G m i j ⊗[ZMod p] T)),
      α n (Φ.h1Map p G T x) = flowZMap (p := p) G i j Φ T (α m x))
    (γ : ∀ m : ℕ, (↑(groupHomology.H1 (flowRepG p G m i j T)) : Type) →+
      Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G)))
    (hγinj : ∀ m, Function.Injective (γ m))
    (hγsurj : ∀ m, Function.Surjective (γ m))
    (hβnat : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n)
      (y : (↑(groupHomology.H1 (flowRep p G m i j T)) : Type)),
      (Φ.hm1Map p G (T ⊗[ZMod p] augIdeal p G))
          (γ m (flowHSβ p G i j T m y))
        = γ n (flowHSβ p G i j T n (flowZMap (p := p) G i j Φ T y)))
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → (↑(groupHomology.H1 (flowRep p G m i j T)) : Type),
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t, flowZMap (p := p) G i j Φ T (x k) = 0 := by
  obtain ⟨m₀, hm₀, h⟩ := exists_shrinking_H1_semidirect p G hj D T
    (fun m => groupHomology.H1 (flowRep p G m i j T))
    (semidirectShrinkingData_of p G T α hαrange hαnat γ hγinj hγsurj hβnat) t hn
  exact ⟨m₀, hm₀, fun m hm x => h m hm x⟩

/-- **Proposition 7 (i) of Schmidt–Wingberg for the paper's own group**, with the recalled
`H^{-2} = H_1` discharged by `Work.CohomologicalShrinking.exists_bridge`.

The only remaining input is the paper's map `α` (the universal coefficient formula combined with
Proposition 5), together with its two properties: its image is the image of the corestriction
(discharged unconditionally for the paper's `α` by `Work.CohomologicalShrinking.flowAlpha_range`,
for `ν ≥ (2,1)`), and its naturality in the rank. -/
theorem exists_shrinking_H1_semidirect_of_alpha (p : ℕ) [Fact p.Prime] (G : Type) [Group G]
    [Fintype G] {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (α : ∀ m : ℕ, (squareQuotient p G m ⊗[ZMod p] (E p G m i j ⊗[ZMod p] T)) →+
      (↑(groupHomology.H1 (flowRep p G m i j T)) : Type))
    (hαrange : ∀ m : ℕ, (α m).range = (flowHSα p G i j T m).range)
    (hαnat : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n)
      (x : squareQuotient p G m ⊗[ZMod p] (E p G m i j ⊗[ZMod p] T)),
      α n (Φ.h1Map p G T x) = flowZMap (p := p) G i j Φ T (α m x))
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → (↑(groupHomology.H1 (flowRep p G m i j T)) : Type),
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t, flowZMap (p := p) G i j Φ T (x k) = 0 := by
  obtain ⟨γ, hγinj, hγsurj, hβnat⟩ := exists_bridge p G i j T
  exact exists_shrinking_H1_semidirect_concrete p G hj D T α hαrange hαnat γ hγinj hγsurj
    hβnat t hn

/-- **Proposition 7 (i) of Schmidt–Wingberg for the paper's own group and classes, with no
remaining input besides Proposition 5.**

`G` is a finite group, `p` a prime, `ν = (i,j) ≥ (2,1)`, `T` a finitely generated `𝔽_p[G]`-module
and `D` a `Prop5Data` for the pair `(i,j)` (the paper's Proposition 5).  Then there is `m₀ ≥ n`
such that for all `m ≥ m₀` and all `x₁, …, x_t ∈ H₁(F(m)/F(m)^{(i,j)} ⋊ G, E(m,τ) ⊗ T)` there is a
surjective `G`-operator homomorphism `Φ : F(m) ⇢ F(n)` whose induced map `flowZMap Φ T` kills all
the `x_k`.

The recalled `H^{-2} = H_1` is discharged by `exists_bridge` and the paper's `α` (with its range
and its naturality in the rank) by `exists_natural_alpha`; the universal coefficient formula, the
Hochschild–Serre sequence and its exactness are proved in this chapter. -/
theorem exists_shrinking_H1_semidirect_paper (p : ℕ) [Fact p.Prime] (G : Type) [Group G]
    [Fintype G] {i j : ℕ} (hi : 2 ≤ i) (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ x : Fin t → (↑(groupHomology.H1 (flowRep p G m i j T)) : Type),
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t, flowZMap (p := p) G i j Φ T (x k) = 0 := by
  obtain ⟨α, hαrange, hαnat⟩ := exists_natural_alpha p G hi T
  exact exists_shrinking_H1_semidirect_of_alpha p G hj D T α hαrange hαnat t hn

end Work.CohomologicalShrinking
