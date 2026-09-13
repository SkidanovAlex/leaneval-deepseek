import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_hyperplanes_between
import Submission.Commons.LinearAlgebra.Submodule.card_hyperplane_zmod_two
import Submission.Commons.LinearAlgebra.Submodule.card_superspaces_finrank_eq_quotient

namespace Commons.LinearAlgebra.Submodule

open Module

noncomputable section

set_option linter.style.haveILetI false

/-- **Superspaces of `C` of dimension `ℓ` meeting a fixed `ℓ`-space `L` exactly in `C`.**
Let `C ≤ L` be submodules of a finite `𝔽₂`-vector space `V` with `finrank C = ℓ - 1`,
`finrank L = ℓ` and `1 ≤ ℓ`.  Then the number of `ℓ`-dimensional submodules `L'` of `V`
with `L ⊓ L' = C` is `2 ^ (finrank V - finrank C) - 2`.

Indeed, an `ℓ`-dimensional `L'` with `L ⊓ L' = C` necessarily contains `C`, and
`L' ↦ L' ⧸ C` is a bijection onto the `1`-dimensional submodules `T` of `V ⧸ C` with
`T ≠ ((L ⧸ C))`, of which there are `(2 ^ (finrank V - finrank C) - 1) - 1`. -/
theorem card_superspaces_inf_eq_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (C L : Submodule (ZMod 2) V) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hCL : C ≤ L)
    (hC : Module.finrank (ZMod 2) C = ℓ - 1) (hL : Module.finrank (ZMod 2) L = ℓ) :
    Nat.card {L' : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) L' = ℓ ∧ L ⊓ L' = C} =
      2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) C) - 2 := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  haveI : Finite (V ⧸ C) := Finite.of_surjective C.mkQ C.mkQ_surjective
  -- Superspaces of `C` of dimension `ℓ` correspond to `1`-dimensional subspaces of `V ⧸ C`.
  have hsup : Nat.card {L' : Submodule (ZMod 2) V // C ≤ L' ∧
      Module.finrank (ZMod 2) L' = ℓ} =
      2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) C) - 1 := by
    have hA : Module.finrank (ZMod 2) C ≤ ℓ := by omega
    have h1 := card_superspaces_finrank_eq_quotient (K := ZMod 2) (V := V) C (ℓ := ℓ) hA
    have hsub : ℓ - Module.finrank (ZMod 2) C = 1 := by omega
    rw [h1]
    have h2 : Nat.card {T : Submodule (ZMod 2) (V ⧸ C) //
          Module.finrank (ZMod 2) T = ℓ - Module.finrank (ZMod 2) C} =
        Nat.card {T : Submodule (ZMod 2) (V ⧸ C) // Module.finrank (ZMod 2) T = 1} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun T => by rw [hsub])
    rw [h2, card_oneDim_zmod_two, Submodule.finrank_quotient]
  -- The fibres of `L' ↦ L ⊓ L'` over `C` are the `ℓ`-superspaces of `C` other than `L`.
  have hiff : ∀ L' : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) L' = ℓ ∧ L ⊓ L' = C) ↔
      (C ≤ L' ∧ Module.finrank (ZMod 2) L' = ℓ ∧ L' ≠ L) := by
    intro L'
    constructor
    · rintro ⟨hfin, hinf⟩
      refine ⟨?_, hfin, ?_⟩
      · rw [← hinf]; exact inf_le_right
      · intro hLL'
        rw [hLL', inf_idem] at hinf
        have hfc : Module.finrank (ZMod 2) L = Module.finrank (ZMod 2) C := by rw [hinf]
        rw [hL, hC] at hfc
        omega
    · rintro ⟨hle, hfin, hne⟩
      refine ⟨hfin, ?_⟩
      have h1 : C ≤ L ⊓ L' := le_inf hCL hle
      have h2 : L ⊓ L' ≤ L := inf_le_left
      have h3 : Module.finrank (ZMod 2) ↥(L ⊓ L') ≤ ℓ := by
        have := Submodule.finrank_mono h2; rw [hL] at this; exact this
      have h4 : ℓ - 1 ≤ Module.finrank (ZMod 2) ↥(L ⊓ L') := by
        have := Submodule.finrank_mono h1; rw [hC] at this; exact this
      have h5 : L ⊓ L' ≠ L := by
        intro h
        have hle' : L ≤ L' := h ▸ inf_le_right
        exact hne (Submodule.eq_of_le_of_finrank_eq hle' (by rw [hL, hfin])).symm
      have h6 : Module.finrank (ZMod 2) ↥(L ⊓ L') < ℓ := by
        by_contra hcon
        exact h5 (Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega))
      exact (Submodule.eq_of_le_of_finrank_eq h1 (by omega)).symm
  set α := {L' : Submodule (ZMod 2) V // C ≤ L' ∧ Module.finrank (ZMod 2) L' = ℓ} with hα
  have hcardα : Nat.card α =
      2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) C) - 1 := hsup
  have hnecard := natCard_subtype_ne_one (⟨L, hCL, hL⟩ : α)
  have hequiv2 : Nat.card {L' : Submodule (ZMod 2) V //
        C ≤ L' ∧ Module.finrank (ZMod 2) L' = ℓ ∧ L' ≠ L} =
      Nat.card {x : α // x ≠ (⟨L, hCL, hL⟩ : α)} := by
    apply Nat.card_congr
    exact
      { toFun := fun y => ⟨⟨y.1, y.2.1, y.2.2.1⟩,
          fun hx => y.2.2.2 (congrArg Subtype.val hx)⟩
        invFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2, fun hL' => x.2 (Subtype.ext hL')⟩
        left_inv := fun y => Subtype.ext rfl
        right_inv := fun x => Subtype.ext (Subtype.ext rfl) }
  calc Nat.card {L' : Submodule (ZMod 2) V //
          Module.finrank (ZMod 2) L' = ℓ ∧ L ⊓ L' = C}
      = Nat.card {L' : Submodule (ZMod 2) V //
          C ≤ L' ∧ Module.finrank (ZMod 2) L' = ℓ ∧ L' ≠ L} :=
        Nat.card_congr (Equiv.subtypeEquivRight hiff)
    _ = Nat.card {x : α // x ≠ (⟨L, hCL, hL⟩ : α)} := hequiv2
    _ = Nat.card α - 1 := hnecard
    _ = (2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) C) - 1) - 1 := by rw [hcardα]
    _ = 2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) C) - 2 := by
        have hp : 1 ≤ 2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) C) :=
          Nat.one_le_two_pow
        omega

/-- **Neighbours of an `ℓ`-space `L` that contain a subspace `W ≤ L`.**
Let `W ≤ L` be submodules of a finite `𝔽₂`-vector space `V` with `finrank W = i`,
`finrank L = ℓ` and `1 ≤ ℓ`.  Then the number of `ℓ`-dimensional submodules `L'` of `V`
satisfying `finrank (L ⊓ L') = ℓ - 1` and containing `W` equals
`(2 ^ (ℓ - i) - 1) * (2 ^ (finrank V - ℓ + 1) - 2)`.

Indeed, `L' ↦ L ⊓ L'` maps such `L'` onto the hyperplanes `C` of `L` containing `W`
(there are `2 ^ (ℓ - i) - 1` of them), and for each `C` the fibre consists of the
`ℓ`-superspaces of `C` meeting `L` exactly in `C` (there are `2 ^ (finrank V - ℓ + 1) - 2`
of them, by `card_superspaces_inf_eq_self`). -/
theorem card_neighbors_containing_of_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (W L : Submodule (ZMod 2) V) (i ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hWL : W ≤ L)
    (hW : Module.finrank (ZMod 2) W = i) (hL : Module.finrank (ZMod 2) L = ℓ) :
    Nat.card {L' : Submodule (ZMod 2) V // Module.finrank (ZMod 2) L' = ℓ ∧
        Module.finrank (ZMod 2) ↥(L ⊓ L') = ℓ - 1 ∧ W ≤ L'} =
      (2 ^ (ℓ - i) - 1) * (2 ^ (Module.finrank (ZMod 2) V - ℓ + 1) - 2) := by
  classical
  -- The hyperplanes of `L` containing `W`.
  let 𝒞 := {C : Submodule (ZMod 2) V // W ≤ C ∧ C ≤ L ∧ Module.finrank (ZMod 2) C = ℓ - 1}
  -- Their fibres under `C ↦ {L' // finrank L' = ℓ ∧ L ⊓ L' = C}`.
  let F : 𝒞 → Type _ := fun C => {L' : Submodule (ZMod 2) V //
      Module.finrank (ZMod 2) L' = ℓ ∧ L ⊓ L' = C.1}
  let T := {x : 𝒞 × Submodule (ZMod 2) V //
      Module.finrank (ZMod 2) x.2 = ℓ ∧ L ⊓ x.2 = x.1.1}
  haveI : Fintype 𝒞 := Fintype.ofFinite 𝒞
  -- The target set is the total space of the family of fibres.
  have e1 : {L' : Submodule (ZMod 2) V // Module.finrank (ZMod 2) L' = ℓ ∧
      Module.finrank (ZMod 2) ↥(L ⊓ L') = ℓ - 1 ∧ W ≤ L'} ≃ T :=
  { toFun := fun L' => ⟨(⟨L ⊓ L'.1, le_inf hWL L'.2.2.2, inf_le_left, L'.2.2.1⟩, L'.1),
      L'.2.1, rfl⟩
    invFun := fun x => ⟨x.1.2, x.2.1, by rw [x.2.2, x.1.1.2.2.2],
      x.1.1.2.1.trans (x.2.2 ▸ inf_le_right)⟩
    left_inv := fun L' => Subtype.ext rfl
    right_inv := fun x => Subtype.ext (Prod.ext (Subtype.ext x.2.2) rfl) }
  have e2 : T ≃ Σ C : 𝒞, F C :=
    Equiv.subtypeProdEquivSigmaSubtype
      (fun (C : 𝒞) (L' : Submodule (ZMod 2) V) =>
        Module.finrank (ZMod 2) L' = ℓ ∧ L ⊓ L' = C.1)
  -- Number of hyperplanes of `L` containing `W`.
  have hcardC_nat : Nat.card 𝒞 = 2 ^ (ℓ - i) - 1 := by
    have h := card_hyperplanes_between (V := V) W L ℓ hℓ hWL hL
    rw [hW] at h
    exact h
  have hcardC : Fintype.card 𝒞 = 2 ^ (ℓ - i) - 1 := by
    rw [← Nat.card_eq_fintype_card]; exact hcardC_nat
  -- Number of points in each fibre.
  have hfib : ∀ C : 𝒞, Nat.card (F C) =
      2 ^ (Module.finrank (ZMod 2) V - ℓ + 1) - 2 := by
    intro C
    have h := card_superspaces_inf_eq_self (V := V) C.1 L ℓ hℓ C.2.2.1 C.2.2.2 hL
    have hn : ℓ ≤ Module.finrank (ZMod 2) V := by
      have hl := Submodule.finrank_le L; rw [hL] at hl; exact hl
    have hexp : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) C.1 =
        Module.finrank (ZMod 2) V - ℓ + 1 := by omega
    rw [hexp] at h
    exact h
  calc Nat.card {L' : Submodule (ZMod 2) V // Module.finrank (ZMod 2) L' = ℓ ∧
        Module.finrank (ZMod 2) ↥(L ⊓ L') = ℓ - 1 ∧ W ≤ L'}
      = Nat.card (Σ C : 𝒞, F C) := Nat.card_congr (e1.trans e2)
    _ = ∑ C : 𝒞, Nat.card (F C) := Nat.card_sigma
    _ = ∑ C : 𝒞, (2 ^ (Module.finrank (ZMod 2) V - ℓ + 1) - 2) :=
        Finset.sum_congr rfl (fun C _ => hfib C)
    _ = Fintype.card 𝒞 * (2 ^ (Module.finrank (ZMod 2) V - ℓ + 1) - 2) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ = (2 ^ (ℓ - i) - 1) * (2 ^ (Module.finrank (ZMod 2) V - ℓ + 1) - 2) := by
        rw [hcardC]

end

end Commons.LinearAlgebra.Submodule
