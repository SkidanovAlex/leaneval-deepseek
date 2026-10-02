import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Kahn.nibbleSetup

/-!
# The deterministic assembly of the one-round (colour-degree) nibble

`Work.Deep.Kahn.nibbleAssembly` is the *deterministic* half of the one-round step of the
semi-random (nibble) proof of Kahn's theorem
(Kang--Kelly--Kühn--Methuku--Osthus, Theorem 4.6 = `ErdosFaberLovaszConjecture.KahnStatement`;
Kahn 1996).  It takes a single round outcome `ω : Round.Space K 𝓗 L` of the regularised
instance and the two *per-round estimates* that the probabilistic analysis
(`Work.Deep.Kahn.roundUsedColours` for the lists, `Work.Deep.Kahn.roundResidual` for the
colour degrees) provides for `ω`, and produces the data consumed by the next round:

* `𝓗₀ := Round.keptSub ω` — the subhypergraph of *kept* edges, coloured in this round;
* `φ := Round.keptColoring ω` — the proper list-colouring of `𝓗₀` induced by the round;
* `L' e := L e \ Round.usedColours ω e` — the list of `e`, with the colours *used* at `e`
  by a kept edge removed.

The five clauses of the conclusion are then, in order:

1. **list-soundness of the colouring**: `φ.labels e ∈ L e` for every kept edge `e`
   (`Round.keptColoring_mem`);
2. **monotonicity of the new lists**: `L' e ⊆ L e`;
3. **the list-size estimate** `|L' e| ≥ newLambda Λ C D K - η Λ` for every uncoloured edge:
   this is exactly the hypothesis `hA` on `ω` (a kept edge is not in `𝓗 ∖ 𝓗₀`, and the
   statement of `hA` is phrased with `L e \ usedColours ω e`, which is `L' e`);
4. **the avoidance (soundness) clause** `φ.labels f ∉ L' e` whenever the kept edge `f`
   meets the uncoloured edge `e`: the colour `φ.labels f = colour ω f` is *used* at `e`
   (`Round.colour_mem_usedColours`), hence removed from `L' e`;
5. **the colour-degree estimate** `#{e : 𝓗 ∖ 𝓗₀ | x ∈ e, γ ∈ L' e} ≤ newDeg Λ C D K + η D`:
   the injection `E ↦ ⟨E, E.2.1⟩` identifies the uncoloured edges of `𝓗` with the edges of
   `𝓗 ∖ 𝓗₀`, and the count on the right is exactly `Round.residualCount ω x γ`, for which
   the hypothesis `hB` on `ω` gives the bound (when `(x,γ)` occurs at all; if it does not,
   both counts vanish and `newDeg ≥ 0` gives the claim).

The two branching cases of clause 5 are the only case analysis in the proof; everything else
is `Finset` bookkeeping.  The genuinely probabilistic content lives in the hypotheses `hA`
and `hB` on `ω`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace Work.Deep.Kahn

namespace Round

/-- **The colour of a kept edge that meets `e` is used at `e`.**  This is the bridge between
the colouring of `Round.keptSub ω` and the set `Round.usedColours ω e`, and it is what makes
the avoidance clause of `nibbleAssembly` work. -/
lemma colour_mem_usedColours {n c K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    [Fintype 𝓗] [NeZero K] {L : 𝓗 → Finset (Fin c)} {ω : Space K 𝓗 L} {f e : 𝓗}
    (hf : kept ω f) (hint : ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty) :
    colour ω f ∈ usedColours ω e := by
  classical
  unfold usedColours
  exact Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf, hint⟩, rfl⟩

/-- An edge lying in `𝓗 ∖ Round.keptSub ω` is not kept. -/
lemma not_kept_of_not_mem_keptSub {n c K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    [NeZero K] {L : 𝓗 → Finset (Fin c)} {ω : Space K 𝓗 L} {E : Set (Fin n)}
    (hE : E ∈ 𝓗) (h : E ∉ keptSub ω) : ¬ kept ω ⟨E, hE⟩ :=
  fun hk => h (mem_keptSub.mpr ⟨hE, hk⟩)

/-- **The colour-degree count of the uncoloured subhypergraph is the `residualCount`.**
The uncoloured edges through `x` still carrying `γ` in their (trimmed) list `L ∖ usedColours`
are exactly the edges through `x` counted by `Round.residualCount ω x γ`; the map
`E ↦ ⟨↑E, E.2.1⟩` realises the uncoloured subhypergraph `𝓗 ∖ keptSub ω` inside `𝓗` and is
injective. -/
lemma natCard_diff_le {n c K : ℕ} {𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    [Fintype 𝓗] [NeZero K] {L : 𝓗 → Finset (Fin c)} (ω : Space K 𝓗 L) (x : Fin n)
    (γ : Fin c) :
    Nat.card {E : ↥(𝓗 \ keptSub ω) // x ∈ (E : Set (Fin n)) ∧
        γ ∈ L ⟨(E : Set (Fin n)), E.2.1⟩ \ usedColours ω ⟨(E : Set (Fin n)), E.2.1⟩}
      ≤ residualCount ω x γ := by
  classical
  set S := {E : ↥(𝓗 \ keptSub ω) // x ∈ (E : Set (Fin n)) ∧
        γ ∈ L ⟨(E : Set (Fin n)), E.2.1⟩ \ usedColours ω ⟨(E : Set (Fin n)), E.2.1⟩}
  set T := {e : 𝓗 // ¬ kept ω e ∧ x ∈ (e : Set (Fin n)) ∧ γ ∈ L e ∧ γ ∉ usedColours ω e}
  have hcardT : Nat.card T = residualCount ω x γ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp [residualCount]
  rw [← hcardT]
  refine Nat.card_le_card_of_injective
    (fun s : S => (⟨⟨(s.1 : Set (Fin n)), s.1.2.1⟩, ?_⟩ : T)) ?_
  · obtain ⟨hx, hmem⟩ := s.2
    rw [Finset.mem_sdiff] at hmem
    exact ⟨fun hk => s.1.2.2 (mem_keptSub.mpr ⟨s.1.2.1, hk⟩), hx, hmem.1, hmem.2⟩
  · intro s₁ s₂ h
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun z : T => ((z : 𝓗) : Set (Fin n))) h
    simpa using this

end Round

/-- `newDeg` is nonnegative.  Both retention factors `retention` and `retentionU` lie in
`[0,1]`, and the two coefficients `1 - 1/K` (for `K ≥ 1`) and `1/K` are nonnegative; hence so
is the whole expression `newDeg = D · ((1 - 1/K) · retentionU + (1/K) · (1 - retention))`. -/
lemma newDeg_nonneg {C D Λ K : ℕ} (hK : 1 ≤ K) : 0 ≤ newDeg Λ C D K := by
  rw [newDeg, retention, retentionU]
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have h1 : (0 : ℝ) ≤ 1 / (K : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (1 / (K : ℝ)) / (Λ : ℝ) := by positivity
  have hle : (1 / (K : ℝ)) / (Λ : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos Λ with h | h
    · subst h; simp
    · have hΛ1 : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast h
      have hK1 : 1 / (K : ℝ) ≤ 1 := by
        rw [div_le_one hKpos]; exact_mod_cast hK
      have h0 : (0 : ℝ) < (Λ : ℝ) := by positivity
      rw [div_le_one h0]
      linarith
  have hbase : (0 : ℝ) ≤ 1 - (1 / (K : ℝ)) / (Λ : ℝ) := by linarith
  have hbase1 : 1 - (1 / (K : ℝ)) / (Λ : ℝ) ≤ 1 := by linarith
  have hretU : 0 ≤ (1 - (1 / (K : ℝ)) / (Λ : ℝ)) ^ (D * (C - 1)) := pow_nonneg hbase _
  have hret : (1 - (1 / (K : ℝ)) / (Λ : ℝ)) ^ (C * D) ≤ 1 := pow_le_one₀ hbase hbase1
  have hc1 : 0 ≤ 1 - 1 / (K : ℝ) := by
    have : 1 / (K : ℝ) ≤ 1 := by rw [div_le_one hKpos]; exact_mod_cast hK
    linarith
  have hD : (0 : ℝ) ≤ (D : ℝ) := by positivity
  have hmain : 0 ≤ (1 - 1 / (K : ℝ)) * (1 - (1 / (K : ℝ)) / (Λ : ℝ)) ^ (D * (C - 1)) +
      (1 / (K : ℝ)) * (1 - (1 - (1 / (K : ℝ)) / (Λ : ℝ)) ^ (C * D)) := by
    have h3 : 0 ≤ (1 / (K : ℝ)) * (1 - (1 - (1 / (K : ℝ)) / (Λ : ℝ)) ^ (C * D)) :=
      mul_nonneg h1 (by linarith)
    have h4 : 0 ≤ (1 - 1 / (K : ℝ)) * (1 - (1 / (K : ℝ)) / (Λ : ℝ)) ^ (D * (C - 1)) :=
      mul_nonneg hc1 hretU
    linarith
  exact mul_nonneg hD hmain

theorem nibbleAssembly {C : ℕ} (hC : 2 ≤ C) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
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
            ((L e \ Work.Deep.Kahn.Round.usedColours ω e).card : ℝ)) →
        (∀ x : Fin n, ∀ γ : Fin c, (∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e) →
          ((Work.Deep.Kahn.Round.residualCount ω x γ : ℕ) : ℝ) ≤
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
  intro n c 𝓗 instF L D Λ K instK hD hΛ hK2 hηK h16 hlin hsize hLcard hdeg hεD hΛ10 ω hA hB
  classical
  -- the kept subhypergraph, its colouring, and the trimmed lists
  refine ⟨Round.keptSub ω, Round.keptSub_subset ω, Round.keptColoring ω,
    (fun E => L ⟨(E : Set (Fin n)), E.2.1⟩ \ Round.usedColours ω ⟨(E : Set (Fin n)), E.2.1⟩),
    ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. the colour of a kept edge belongs to its list
    intro e
    exact Round.keptColoring_mem ω e
  · -- 2. the new list is a subset of the old one
    intro E
    exact Finset.sdiff_subset
  · -- 3. the list-size estimate, which is the hypothesis `hA` at the uncoloured edge `E`
    intro E
    exact hA ⟨(E : Set (Fin n)), E.2.1⟩
      (Round.not_kept_of_not_mem_keptSub E.2.1 E.2.2)
  · -- 4. avoidance: the colour of a kept edge meeting `E` is used at `E`
    intro E f hnon hmem
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 (Round.colour_mem_usedColours f.2.choose_spec hnon)
  · -- 5. the colour-degree estimate, transferred to the uncoloured subhypergraph
    intro x γ
    by_cases hpre : ∃ e : 𝓗, x ∈ (e : Set (Fin n)) ∧ γ ∈ L e
    · exact le_trans (by exact_mod_cast Round.natCard_diff_le ω x γ) (hB x γ hpre)
    · -- if `(x,γ)` occurs nowhere, the count on the left vanishes
      have hempty : IsEmpty {E : ↥(𝓗 \ Round.keptSub ω) // x ∈ (E : Set (Fin n)) ∧
          γ ∈ L ⟨(E : Set (Fin n)), E.2.1⟩ \ Round.usedColours ω ⟨(E : Set (Fin n)), E.2.1⟩} :=
        ⟨fun s => by
          obtain ⟨hx, hmem⟩ := s.2
          rw [Finset.mem_sdiff] at hmem
          exact hpre ⟨⟨(s.1 : Set (Fin n)), s.1.2.1⟩, hx, hmem.1⟩⟩
      rw [Nat.card_eq_zero.mpr (Or.inl hempty), Nat.cast_zero]
      have h1 : (0 : ℝ) ≤ newDeg Λ C D K := newDeg_nonneg (by omega)
      have h2 : (0 : ℝ) ≤ η * (D : ℝ) := mul_nonneg (le_of_lt hη) (by positivity)
      linarith

end Work.Deep.Kahn
