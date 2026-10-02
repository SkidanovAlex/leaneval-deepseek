import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.nibbleWSetup
import Submission.Work.Deep.Kahn.nibbleAssembly

/-!
# The deterministic assembly of the one-round nibble (wasteful/residual construction)

This is the deterministic half of the one-round step in the form used by
`Work.Deep.Kahn.RegularisedNibbleStatement`: from a round outcome `ω` for which

* every uncoloured edge keeps at least `newLambda - ηΛ` colours in its **residual** list
  `Round.residual ω e = L e \ Round.lost ω e`, and
* every occurring pair `(x,γ)` has residual colour degree `Round.newColDeg ω x γ ≤ newDeg + ηD`,

it produces the data consumed by the next round:

* `𝓗₀ := Round.keptSub ω` and `φ := Round.keptColoring ω` (the kept edges and their colouring);
* `L' e := Round.residual ω e` (the wasteful update of Reed--Sudakov).

The five clauses of the conclusion are then the same as in `Work.Deep.Kahn.nibbleAssembly`,
except that `L e \ usedColours ω e` is replaced by `residual ω e` throughout.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

namespace Round

/-- **The residual colour-degree count is the `newColDeg`.**  The uncoloured edges through `x`
still carrying `γ` in their residual list are exactly the edges through `x` counted by
`Round.newColDeg ω x γ`; the map `E ↦ ⟨↑E, E.2.1⟩` realises the uncoloured subhypergraph
`𝓗 ∖ keptSub ω` inside `𝓗` and is injective. -/
lemma natCard_residual_le {n c K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    [Fintype 𝓗] [NeZero K] {L : 𝓗 → Finset (Fin c)} (ω : Space K 𝓗 L) (x : Fin n)
    (γ : Fin c) :
    Nat.card {E : ↥(𝓗 \ keptSub ω) // x ∈ (E : Set (Fin n)) ∧
        γ ∈ residual ω ⟨(E : Set (Fin n)), E.2.1⟩}
      ≤ newColDeg ω x γ := by
  classical
  set T := {e : 𝓗 // ¬ kept ω e ∧ x ∈ (e : Set (Fin n)) ∧ γ ∈ residual ω e}
  have hcardT : Nat.card T = newColDeg ω x γ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp [newColDeg]
  rw [← hcardT]
  refine Nat.card_le_card_of_injective
    (fun s : {E : ↥(𝓗 \ keptSub ω) // x ∈ (E : Set (Fin n)) ∧
        γ ∈ residual ω ⟨(E : Set (Fin n)), E.2.1⟩} =>
      (⟨⟨(s.1 : Set (Fin n)), s.1.2.1⟩, ?_⟩ : T)) ?_
  · obtain ⟨hx, hmem⟩ := s.2
    exact ⟨fun hk => s.1.2.2 (mem_keptSub.mpr ⟨s.1.2.1, hk⟩), hx, hmem⟩
  · intro s₁ s₂ h
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun z : T => ((z : 𝓗) : Set (Fin n))) h
    simpa using this

end Round

/-- **The deterministic assembly** of the one-round nibble step, in the wasteful (residual)
form. -/
theorem nibbleWAssembly {C : ℕ} (hC : 2 ≤ C) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∀ (n c : ℕ) (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) [Fintype 𝓗]
      (L : 𝓗 → Finset (Fin c)) (D Λ K : ℕ) [NeZero K],
      1 ≤ D → 1 ≤ Λ → 2 ≤ K → η * (K : ℝ) ≤ 1 →
      (16 : ℝ) * (C : ℝ) ≤ (1 + ε) * (K : ℝ) →
      𝓗.IsLinear →
      (∀ e : 𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) = C) →
      (∀ e : 𝓗, (L e).card = Λ) →
      (∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
        Nat.card {e : 𝓗 // x ∈ (e : Set (Fin n)) ∧ γ ∈ L e} = D) →
      (1 + ε) * (D : ℝ) ≤ (Λ : ℝ) → (Λ : ℝ) ≤ 10 * (C : ℝ) * (D : ℝ) →
      ∀ ω : Work.Deep.Kahn.Round.Space K 𝓗 L,
        (∀ e : 𝓗, ¬ Work.Deep.Kahn.Round.kept ω e →
          Work.Deep.Kahn.newLambda Λ C D K - η * (Λ : ℝ) ≤
            ((Work.Deep.Kahn.Round.residual ω e).card : ℝ)) →
        (∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
          ((Work.Deep.Kahn.Round.newColDeg ω x γ : ℕ) : ℝ) ≤
            Work.Deep.Kahn.newDeg Λ C D K + η * (D : ℝ)) →
        ∃ (𝓗₀ : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (hsub : 𝓗₀ ⊆ 𝓗)
          (φ : 𝓗₀.Coloring (Fin c))
          (L' : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type) → Finset (Fin c)),
          (∀ e : 𝓗₀, φ.labels e ∈ L ⟨(e : Set (Fin n)), hsub e.2⟩) ∧
          (∀ e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type),
              L' e ⊆ L ⟨(e : Set (Fin n)), e.2.1⟩) ∧
          (∀ e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type),
              Work.Deep.Kahn.newLambda Λ C D K - η * (Λ : ℝ) ≤ ((L' e).card : ℝ)) ∧
          (∀ e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type), ∀ f : 𝓗₀,
              (((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty → φ.labels f ∉ L' e)) ∧
          (∀ x : Fin n, ∀ γ : Fin c,
              ((Nat.card {e : ((𝓗 \ 𝓗₀ : Set (Set (Fin n))) : Type) //
                  x ∈ (e : Set (Fin n)) ∧ γ ∈ L' e} : ℕ) : ℝ) ≤
                Work.Deep.Kahn.newDeg Λ C D K + η * (D : ℝ)) := by
  intro n c 𝓗 instF L D Λ K instK hD hΛ hK2 hηK h16 hlin hsize hLcard hdeg hεD hΛ10
    ω hA hB
  classical
  refine ⟨Round.keptSub ω, Round.keptSub_subset ω, Round.keptColoring ω,
    (fun E => Round.residual ω ⟨(E : Set (Fin n)), E.2.1⟩), ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. the colour of a kept edge belongs to its list
    intro e
    exact Round.keptColoring_mem ω e
  · -- 2. the residual list is a subset of the old one
    intro E
    exact Round.residual_subset ω _
  · -- 3. the list-size estimate, which is the hypothesis `hA` at the uncoloured edge `E`
    intro E
    exact hA ⟨(E : Set (Fin n)), E.2.1⟩
      (Round.not_kept_of_not_mem_keptSub E.2.1 E.2.2)
  · -- 4. avoidance: the colour of a kept edge meeting `E` is lost at `E`
    intro E f hnon hmem
    rw [Round.mem_residual] at hmem
    exact hmem.2 ⟨(f : Set (Fin n)), f.2.choose⟩ (Round.kept_active f.2.choose_spec) rfl hnon
  · -- 5. the colour-degree estimate, transferred to the uncoloured subhypergraph
    intro x γ
    by_cases hpre : ∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e
    · exact le_trans (by exact_mod_cast Round.natCard_residual_le ω x γ) (hB x γ hpre)
    · have hempty : IsEmpty {E : ↥(𝓗 \ Round.keptSub ω) // x ∈ (E : Set (Fin n)) ∧
          γ ∈ Round.residual ω ⟨(E : Set (Fin n)), E.2.1⟩} :=
        ⟨fun s => by
          obtain ⟨hx, hmem⟩ := s.2
          exact hpre ⟨⟨(s.1 : Set (Fin n)), s.1.2.1⟩, hx, (Round.mem_residual.mp hmem).1⟩⟩
      rw [Nat.card_eq_zero.mpr (Or.inl hempty), Nat.cast_zero]
      have h1 : (0 : ℝ) ≤ newDeg Λ C D K := newDeg_nonneg (by omega)
      have h2 : (0 : ℝ) ≤ η * (D : ℝ) := mul_nonneg (le_of_lt hη) (by positivity)
      linarith

end Work.Deep.Kahn
