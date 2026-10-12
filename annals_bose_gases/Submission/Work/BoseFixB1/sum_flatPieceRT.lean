import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.a0FlatPieces
import Submission.Work.BoseFixB1.boxPInd_finset_sum
import Submission.Work.BoseFixB1.boxQInd_finset_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.sum_flatPieceRT` — completeness of the joint `(P,Q,R)`-flat decomposition

This is the **resolution of the identity on the whole box** for the `(P,Q,R)`-refined flat
pieces `Work.BoseFixB1.flatPieceRT` of `Submission/Work/BoseFixB1/a0FlatPieces.lean`.  With

`Pᵢ = UBBInputs8.boxPInd V A i`  (FS `eq:HBU` box projection),
`Qᵢ = UBBInputs8.boxQInd V A i = 1_A(·ᵢ)·Φ − PᵢΦ`  (its mean-free part),
`Rᵢ = flatPieceRT`'s `rInd A i`  (multiplication by `1_{·ᵢ ∉ A}`),

and the three-slot-set pieces

`Θ_{S,T} = (∏_{i∈S}Pᵢ)(∏_{i∈T}Qᵢ)(∏_{i∉S∪T}Rᵢ)` ,  `S, T : Finset (Fin N)` disjoint,

the statement is

  `Σ_{S} Σ_{T ⊆ Sᶜ} Θ_{S,T} Φ = Φ`

for every state `Φ`.  Unlike its `(P,Q)`-sibling `Work.BoseFixB1.sum_flatPiece` (which gives
`Σ_S Π_S = 1_{A^N}`), this identity is complete on the **whole** configuration space: the extra
family `Rᵢ = 1 − cᵢ` supplies exactly the missing `Aᶜ`-slots (see the module docstring of
`a0FlatPieces.lean` §2 for why `Σ_S Π_S = 1_{A^N}` alone is not enough for the rung-4 ledger:
`Θ_{S,T}` is the piece on which the *numbers* `n₀`, `n₊`, `n_R` are `|S|`, `|T|`,
`N − |S| − |T|` *everywhere*, not merely on `A^N`).

## The mathematics, and why nothing analytic is needed

The whole proof is combinatorial, at the level of the pointwise identity

`PᵢF x + QᵢF x + RᵢF x = F x`      (⋆)

which is *definitional* in the FS conventions: `QᵢF x = 1_A(xᵢ)F x − PᵢF x` and
`RᵢF x = 1_{Aᶜ}(xᵢ)F x = (1 − 1_A(xᵢ))F x`, so the three terms collapse to
`(1_A(xᵢ) + 1_{Aᶜ}(xᵢ))F x = F x`.  In particular **no additivity of the slot operators and no
integrability is used anywhere**: the sums over the pieces are never pushed inside `Pᵢ`/`Qᵢ`/`Rᵢ`;
the pieces are combined *after* being evaluated at `x`, where (⋆) is an identity of real numbers.
(Contrast the P/Q sibling, where the corresponding collapse needs the additivity of `boxQInd` on
box-bounded states, `Work.BoseFixB1.boxQInd_finset_sum`.)  Consequently the analytic hypotheses
`hℓ, hV, hA, hVeq, hAc, hΦc` of the theorem are **not used**: the identity holds for every set
`A`, every `V` and every state `Φ`; measurability, continuity and `A ⊆ acube ℓ` enter only in the
analytic estimates that consume this lemma.

The combinatorial engine is `pairPowersetInsert`: splitting the pairs of disjoint subsets of
`insert i t` according to the position of `i` (in `S`, in `T`, in neither) — the induction then
peels one slot at a time off `List.finRange N` and uses (⋆) at the head slot, exactly as
`Work.BoseFixB1.sum_flatPieceList` does with `Qᵢ + Pᵢ = cᵢ`.

## Route

* `sdiff_insert_eq`, `insert_sdiff_insert_eq` — the two set identities identifying the index sets
  of the three classes of pairs;
* `pairPowersetInsert` — the bisection of the double powerset sum at a new slot;
* `flatPieceRTList_congr` — the fold depends on the slot sets only through the membership pattern
  of the slots of its list;
* `rInd_add_boxQInd_add_boxPInd` — (⋆);
* `sum_flatPieceRTList` — the induction over a repetition-free slot list, giving
  `Σ_{S ⊆ l} Σ_{T ⊆ l\S} Θ_{S,T} Φ = Φ`;
* `sum_flatPieceRT` — the list `List.finRange N`, whose `toFinset` is `univ`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

local notation "𝔼3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

-- the analytic hypotheses of the statement are not used by the combinatorial identity
set_option linter.unusedVariables false

/-! ## 1. The index-set identities -/

/-- `(insert i t) \ S = insert i (t \ S)` when `i ∉ S`: for subsets of `insert i t` that do not
contain the new slot, complementing is the same as complementing in `t` and adding `i` back. -/
private theorem sdiff_insert_eq {α : Type*} [DecidableEq α] {t S : Finset α} {i : α} (hi : i ∉ S) :
    (insert i t) \ S = insert i (t \ S) := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 with rfl | h1
    · exact Or.inl rfl
    · exact Or.inr ⟨h1, h2⟩
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨Or.inl rfl, hi⟩
    · exact ⟨Or.inr h1, h2⟩

/-- `(insert i t) \ (insert i S) = t \ S` when `i ∉ t`: for subsets `S ⊆ t`, complementing
`insert i S` inside `insert i t` removes the new slot from both sides. -/
private theorem insert_sdiff_insert_eq {α : Type*} [DecidableEq α] {t S : Finset α} {i : α}
    (hi : i ∉ t) : (insert i t) \ (insert i S) = t \ S := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.elim (fun hji => absurd (Or.inl hji) h2) id, fun hS => h2 (Or.inr hS)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨Or.inr h1, fun h => h.elim ?_ h2⟩
    intro hji
    exact hi (hji ▸ h1)

/-! ## 2. The bisection of the double powerset sum at a new slot -/

/-- **Bisection of the double powerset sum at a new slot.**  If `i ∉ t`, then summing an
arbitrary family `f S T` over all *disjoint* pairs `(S,T)` of subsets of `insert i t` splits
according to the position of the new slot `i`: it can be outside `S ∪ T` (first summand), in `T`
(second summand) or in `S` (third summand), each time leaving a sum over the disjoint pairs of
subsets of `t`.

This is the three-way analogue of `Finset.sum_powerset_insert` and the combinatorial engine of
the `(P,Q,R)` resolution of the identity. -/
theorem pairPowersetInsert {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    {t : Finset α} {i : α} (hi : i ∉ t) (f : Finset α → Finset α → β) :
    (∑ S ∈ (insert i t).powerset, ∑ T ∈ ((insert i t) \ S).powerset, f S T)
      = (∑ S ∈ t.powerset, ∑ T ∈ (t \ S).powerset, f S T)
        + (∑ S ∈ t.powerset, ∑ T ∈ (t \ S).powerset, f S (insert i T))
        + (∑ S ∈ t.powerset, ∑ T ∈ (t \ S).powerset, f (insert i S) T) := by
  rw [Finset.sum_powerset_insert hi]
  -- the two halves: `i ∉ S` (both positions of `i` inside the inner index set) and `i ∈ S`
  have h1 : (∑ S ∈ t.powerset, ∑ T ∈ ((insert i t) \ S).powerset, f S T)
      = (∑ S ∈ t.powerset, ∑ T ∈ (t \ S).powerset, f S T)
        + (∑ S ∈ t.powerset, ∑ T ∈ (t \ S).powerset, f S (insert i T)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    have hiS : i ∉ S := fun h => hi (Finset.mem_powerset.mp hS h)
    have hiS' : i ∉ t \ S := fun h => hi (Finset.mem_sdiff.mp h).1
    rw [sdiff_insert_eq hiS, Finset.sum_powerset_insert hiS']
  have h2 : (∑ S ∈ t.powerset, ∑ T ∈ ((insert i t) \ (insert i S)).powerset,
        f (insert i S) T)
      = ∑ S ∈ t.powerset, ∑ T ∈ (t \ S).powerset, f (insert i S) T := by
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [insert_sdiff_insert_eq hi]
  rw [h1, h2]

/-! ## 3. The fold only sees the membership pattern of the slots of its list -/

/-- **The `(P,Q,R)`-flat pieces depend only on the membership pattern of the slots of the list.**
If `S₁` and `S₂` agree on every entry of `l`, and `T₁` and `T₂` do too, then
`flatPieceRTList V A l S₁ T₁ Ψ = flatPieceRTList V A l S₂ T₂ Ψ`. -/
theorem flatPieceRTList_congr {N : ℕ} (V : ℝ) (A : Set 𝔼3) (Ψ : X N → ℝ) :
    ∀ (l : List (Fin N)) (S₁ T₁ S₂ T₂ : Finset (Fin N)),
      (∀ j ∈ l, (j ∈ S₁ ↔ j ∈ S₂)) → (∀ j ∈ l, (j ∈ T₁ ↔ j ∈ T₂)) →
      flatPieceRTList V A l S₁ T₁ Ψ = flatPieceRTList V A l S₂ T₂ Ψ := by
  intro l
  induction l with
  | nil => intro S₁ T₁ S₂ T₂ _ _; rfl
  | cons i l ih =>
    intro S₁ T₁ S₂ T₂ hS hT
    rw [flatPieceRTList_cons, flatPieceRTList_cons]
    have hS' : ∀ j ∈ l, (j ∈ S₁ ↔ j ∈ S₂) := fun j hj => hS j (List.mem_cons_of_mem i hj)
    have hT' : ∀ j ∈ l, (j ∈ T₁ ↔ j ∈ T₂) := fun j hj => hT j (List.mem_cons_of_mem i hj)
    rw [ih S₁ T₁ S₂ T₂ hS' hT']
    have hiS : (i ∈ S₁) ↔ (i ∈ S₂) := hS i List.mem_cons_self
    have hiT : (i ∈ T₁) ↔ (i ∈ T₂) := hT i List.mem_cons_self
    by_cases h1 : i ∈ S₁
    · rw [if_pos h1, if_pos (hiS.mp h1)]
    · rw [if_neg h1, if_neg (fun h => h1 (hiS.mpr h))]
      by_cases h2 : i ∈ T₁
      · rw [if_pos h2, if_pos (hiT.mp h2)]
      · rw [if_neg h2, if_neg (fun h => h2 (hiT.mpr h))]

/-! ## 4. The pointwise identity `Rᵢ + Qᵢ + Pᵢ = 1` -/

/-- **The pointwise resolution of the identity at a single slot**: for every state `F` and every
configuration `x`,

  `RᵢF x + QᵢF x + PᵢF x = F x`,

i.e. `1_{xᵢ∉A}·F x + (1_A(xᵢ)·F x − PᵢF x) + PᵢF x = F x`.  Both identities are definitional
(`boxQInd_eq`, `rInd`); only `1_A + 1_{Aᶜ} = 1` is used. -/
theorem rInd_add_boxQInd_add_boxPInd {N : ℕ} (V : ℝ) (A : Set 𝔼3) (i : Fin N)
    (F : X N → ℝ) (x : X N) :
    rInd A i F x + Work.UBBInputs8.boxQInd V A i F x
      + Work.UBBInputs8.boxPInd V A i F x = F x := by
  have h : Aᶜ.indicator (fun _ => (1 : ℝ)) (x i) = 1 - A.indicator (fun _ => (1 : ℝ)) (x i) := by
    by_cases hx : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, Set.mem_compl_iff]
  rw [show Work.UBBInputs8.boxQInd V A i F x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * F x
        - Work.UBBInputs8.boxPInd V A i F x from rfl]
  simp only [rInd]
  rw [h]
  ring

/-! ## 5. The induction over a repetition-free slot list -/

/-- **Completeness of the `(P,Q,R)`-flat decomposition over a list of distinct slots.**  For a
list `l` without repetitions and every state `Ψ`,

  `Σ_{S ⊆ l} Σ_{T ⊆ l\S} flatPieceRTList V A l S T Ψ = Ψ`   pointwise.

The proof is the induction described in the module docstring: `pairPowersetInsert` splits the
double sum over the disjoint pairs of subsets of `insert i l.toFinset` into the three classes
according to the position of the head slot `i`; the head slot then acts as `Rᵢ`, `Qᵢ`, `Pᵢ`
respectively on the *same* tail piece (identified by `flatPieceRTList_congr`), and
`rInd_add_boxQInd_add_boxPInd` collapses the three contributions to the tail piece, leaving the
induction hypothesis on the tail list. -/
theorem sum_flatPieceRTList {N : ℕ} (V : ℝ) (A : Set 𝔼3) :
    ∀ (l : List (Fin N)) (Ψ : X N → ℝ) (x : X N), l.Nodup →
      (∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
          flatPieceRTList V A l S T Ψ x) = Ψ x := by
  intro l
  induction l with
  | nil =>
    intro Ψ x _
    simp
  | cons i l ih =>
    intro Ψ x hnd
    obtain ⟨hi, hnd'⟩ := List.nodup_cons.mp hnd
    have hlt : i ∉ l.toFinset := by simpa [List.mem_toFinset] using hi
    rw [List.toFinset_cons,
      pairPowersetInsert hlt (fun S T => flatPieceRTList V A (i :: l) S T Ψ x)]
    -- class 1: `i` in neither slot set — the head acts as `Rᵢ` on the tail piece
    have hsumR : (∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
          flatPieceRTList V A (i :: l) S T Ψ x)
        = ∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
            rInd A i (flatPieceRTList V A l S T Ψ) x := by
      refine Finset.sum_congr rfl (fun S hS => Finset.sum_congr rfl (fun T hT => ?_))
      have hiS : i ∉ S := fun h => hlt (Finset.mem_powerset.mp hS h)
      have hiT : i ∉ T := fun h => hlt ((Finset.mem_sdiff.mp (Finset.mem_powerset.mp hT h)).1)
      rw [flatPieceRTList_cons, if_neg hiS, if_neg hiT]
    -- class 2: `i ∈ T` — the head acts as `Qᵢ` on the (identical) tail piece
    have hsumQ : (∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
          flatPieceRTList V A (i :: l) S (insert i T) Ψ x)
        = ∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
            Work.UBBInputs8.boxQInd V A i (flatPieceRTList V A l S T Ψ) x := by
      refine Finset.sum_congr rfl (fun S hS => Finset.sum_congr rfl (fun T _ => ?_))
      have hiS : i ∉ S := fun h => hlt (Finset.mem_powerset.mp hS h)
      rw [flatPieceRTList_cons, if_neg hiS, if_pos (Finset.mem_insert_self i T)]
      rw [flatPieceRTList_congr V A Ψ l S (insert i T) S T (fun j _ => Iff.rfl) ?_]
      intro j hj
      rw [Finset.mem_insert]
      exact ⟨fun h => h.elim (fun hji => absurd (hji ▸ hj) hi) id, fun h => Or.inr h⟩
    -- class 3: `i ∈ S` — the head acts as `Pᵢ` on the (identical) tail piece
    have hsumP : (∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
          flatPieceRTList V A (i :: l) (insert i S) T Ψ x)
        = ∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
            Work.UBBInputs8.boxPInd V A i (flatPieceRTList V A l S T Ψ) x := by
      refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
      rw [flatPieceRTList_cons, if_pos (Finset.mem_insert_self i S)]
      rw [flatPieceRTList_congr V A Ψ l (insert i S) T S T ?_ (fun j _ => Iff.rfl)]
      intro j hj
      rw [Finset.mem_insert]
      exact ⟨fun h => h.elim (fun hji => absurd (hji ▸ hj) hi) id, fun h => Or.inr h⟩
    rw [hsumR, hsumQ, hsumP]
    -- collapse the three classes termwise with `Rᵢ + Qᵢ + Pᵢ = 1`
    have hcomb : (∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
          (rInd A i (flatPieceRTList V A l S T Ψ) x
            + Work.UBBInputs8.boxQInd V A i (flatPieceRTList V A l S T Ψ) x
            + Work.UBBInputs8.boxPInd V A i (flatPieceRTList V A l S T Ψ) x))
        = (∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
            rInd A i (flatPieceRTList V A l S T Ψ) x)
          + (∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
            Work.UBBInputs8.boxQInd V A i (flatPieceRTList V A l S T Ψ) x)
          + (∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
            Work.UBBInputs8.boxPInd V A i (flatPieceRTList V A l S T Ψ) x) := by
      simp only [Finset.sum_add_distrib]
    rw [← hcomb]
    have hcollapse : (∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
          (rInd A i (flatPieceRTList V A l S T Ψ) x
            + Work.UBBInputs8.boxQInd V A i (flatPieceRTList V A l S T Ψ) x
            + Work.UBBInputs8.boxPInd V A i (flatPieceRTList V A l S T Ψ) x))
        = ∑ S ∈ l.toFinset.powerset, ∑ T ∈ (l.toFinset \ S).powerset,
            flatPieceRTList V A l S T Ψ x := by
      refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
      exact rInd_add_boxQInd_add_boxPInd V A i (flatPieceRTList V A l S T Ψ) x
    rw [hcollapse]
    exact ih Ψ x hnd'

/-! ## 6. The theorem -/

/-- **Completeness of the joint `(P,Q,R)`-flat decomposition** (resolution of the identity on the
whole box): the refined flat pieces `Θ_{S,T} = (∏_{i∈S}Pᵢ)(∏_{i∈T}Qᵢ)(∏_{i∉S∪T}Rᵢ)` of
`Work.BoseFixB1.flatPieceRT` sum to the identity,

  `Σ_{S : Finset (Fin N)} Σ_{T ⊆ Sᶜ} Θ_{S,T} Φ = Φ`.

This is `sum_flatPieceRTList` at the list `List.finRange N` (repetition free, enumerating all
slots, with `toFinset = univ`) together with `Sᶜ = univ \ S`. -/
theorem sum_flatPieceRT {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    ∀ x : Submission.BoseGases.X N,
      (∑ S : Finset (Fin N), ∑ T ∈ Sᶜ.powerset,
          Work.BoseFixB1.flatPieceRT V A S T Φ x) = Φ x := by
  intro x
  have h := sum_flatPieceRTList V A (List.finRange N) Φ x (List.nodup_finRange N)
  simpa [flatPieceRT, List.toFinset_finRange, Finset.powerset_univ, Finset.compl_eq_univ_sdiff]
    using h

end Work.BoseFixB1
