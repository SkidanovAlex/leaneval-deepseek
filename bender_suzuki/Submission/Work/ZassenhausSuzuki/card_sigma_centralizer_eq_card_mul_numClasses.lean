import Mathlib
import Submission.Work.ZassenhausSuzuki.CountingDefs
import Submission.Work.ZassenhausSuzuki.card_sigma_fiber_over_class

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.ZassenhausSuzuki

/-!
# `card_sigma_centralizer_eq_card_mul_numClasses`

Let `G` be a finite group and `X ⊆ G` a conjugation-invariant set (a union of conjugacy classes).
Then
`Nat.card (Σ x : X, C_G(x)) = |G| * numClasses X`.

The sigma type splits over the conjugacy classes meeting `X`: it is the disjoint union, indexed by
the conjugacy classes `C` with `C ∩ X ≠ ∅` (that is, by the set whose cardinality defines
`numClasses X`), of the sigma types `Σ x ∈ X ∩ C, C_G(x)`.  Each of those fibres has cardinality
`|G|` — `X ∩ C = C`, all centralizers of elements of `C` are conjugate hence equinumerous, and
orbit–stabiliser for the conjugation action gives `|C| * |C_G(x)| = |G|`.  Hence the total is
`numClasses X * |G|`.  The reindexing equivalence is `sigmaCentralizerEquiv` below; the fibre count
is `Work.ZassenhausSuzuki.card_sigma_fiber_over_class`.
-/

/-- The sigma type `Σ x ∈ X, C_G(x)` is the disjoint union, over the conjugacy classes `C` meeting
`X`, of `Σ x ∈ X ∩ C, C_G(x)`. -/
private noncomputable def sigmaCentralizerEquiv {G : Type} [Group G] (X : Set G) :
    (Σ x : {x : G // x ∈ X}, ↥(Subgroup.centralizer ({x.1} : Set G)))
      ≃ Σ C : {C : ConjClasses G // (C.carrier ∩ X).Nonempty},
          Σ x : {x : {x : G // x ∈ X} // ConjClasses.mk x.1 = C.1},
            ↥(Subgroup.centralizer ({x.1.1} : Set G)) where
  toFun p := ⟨⟨ConjClasses.mk p.1.1, ⟨p.1.1, ConjClasses.mem_carrier_mk, p.1.2⟩⟩,
              ⟨⟨p.1, rfl⟩, p.2⟩⟩
  invFun q := ⟨q.2.1.1, q.2.2⟩
  left_inv p := by obtain ⟨x, h⟩ := p; rfl
  right_inv q := by
    obtain ⟨⟨C, hC⟩, ⟨⟨x, hx⟩, h⟩⟩ := q
    cases hx
    rfl

theorem card_sigma_centralizer_eq_card_mul_numClasses {G : Type} [Group G] [Finite G] (X : Set G)
    (hX : ∀ g : G, ∀ x : G, x ∈ X → g * x * g⁻¹ ∈ X) :
    Nat.card (Σ x : {x : G // x ∈ X}, ↥(Subgroup.centralizer ({x.1} : Set G)))
      = Nat.card G * Work.ZassenhausSuzuki.numClasses X := by
  classical
  haveI hY : Fintype {C : ConjClasses G // (C.carrier ∩ X).Nonempty} := Fintype.ofFinite _
  rw [Nat.card_congr (sigmaCentralizerEquiv X), Nat.card_sigma]
  rw [show (∑ C : {C : ConjClasses G // (C.carrier ∩ X).Nonempty},
          Nat.card (Σ x : {x : {x : G // x ∈ X} // ConjClasses.mk x.1 = C.1},
              ↥(Subgroup.centralizer ({x.1.1} : Set G))))
        = ∑ _C : {C : ConjClasses G // (C.carrier ∩ X).Nonempty}, Nat.card G from
      Finset.sum_congr rfl (fun C _ => card_sigma_fiber_over_class X hX C.1 C.2)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, mul_comm]
  rfl

end Work.ZassenhausSuzuki
