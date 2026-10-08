/-
# BMAX — elementary API

Proved, `LocalToolkit`-free facts about the vocabulary of the contract file that the
maximal-subgroup argument of Bender 1970 §1.6/§1.7 (and its consumers in `CORE2A`,
`CORE2B`) uses over and over:

* `fittingIn A ≤ fstarIn A` and `layerIn A ≤ fstarIn A` (by definition of `F* = F·E`);
* `A ⇝ B` from `F*(A) ≤ B` (`BRel.of_fstar_le`) and monotonicity of `⇝`;
* **`Z(F*(A)) ≤ B` whenever `A ⇝ B`** (`BRel.zcenter_le`) — this is the step
  "put `W := Z(F*(Ĥ))`; then `W ≤ N_{F*(Ĥ)}(X) ≤ M`" of Bender 1981's proof of Lemma 2.4;
* the `Nat.card` facts for a coatomic (`= maximal`) subgroup, which is how `BenderCtx.ih`
  is applied to `Ĥ` and to `M`.
-/
import Submission.Work.BMAX.Thompson

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

variable {G : Type*} [Group G]

/-! ## 0. `F*` contains `F` and `E` -/

theorem fittingIn_le_fstarIn (A : Subgroup G) : fittingIn A ≤ fstarIn A := by
  simp only [fittingIn, fstarIn, fstar]
  exact Subgroup.map_mono le_sup_left

theorem layerIn_le_fstarIn (A : Subgroup G) : layerIn A ≤ fstarIn A := by
  simp only [layerIn, fstarIn, fstar]
  exact Subgroup.map_mono le_sup_right

/-- `F*(A) = F(A)·E(A)`, as a rewrite rule in the ambient group. -/
theorem fstarIn_eq_sup (A : Subgroup G) : fstarIn A = fittingIn A ⊔ layerIn A := by
  simp only [fstarIn, fittingIn, layerIn, fstar, Subgroup.map_sup]

theorem fstarIn_le_self (A : Subgroup G) : fstarIn A ≤ A := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem fittingIn_le_self (A : Subgroup G) : fittingIn A ≤ A :=
  le_trans (fittingIn_le_fstarIn A) (fstarIn_le_self A)

theorem layerIn_le_self (A : Subgroup G) : layerIn A ≤ A :=
  le_trans (layerIn_le_fstarIn A) (fstarIn_le_self A)

/-! ## 1. The relation `⇝` -/

/-- `F*(A) ≤ B` is the special case `X = ⊥` of `A ⇝ B`. -/
theorem BRel.of_fstar_le {A B : Subgroup G} (h : fstarIn A ≤ B) : BRel A B :=
  ⟨⊥, bot_le, fun _ hx => h hx.2⟩

/-- `A ⇝ A` always holds (take `X = ⊥`). -/
theorem BRel.self (A : Subgroup G) : BRel A A := BRel.of_fstar_le (fstarIn_le_self A)

theorem BRel.mono_right {A B C : Subgroup G} (h : BRel A B) (hBC : B ≤ C) : BRel A C :=
  ⟨h.choose, h.choose_spec.1, le_trans h.choose_spec.2 hBC⟩

/-- **`Z(F*(A)) ≤ B` whenever `A ⇝ B`.**  Indeed, if `X ≤ F(A)` witnesses `A ⇝ B`, then
`Z(F*(A))` centralizes `F*(A) ⊇ X`, hence normalizes `X`, hence lies in
`N_{F*(A)}(X) ≤ B`. This is the "`W := Z(F*(Ĥ))` lies in `M`" step of Bender 1981,
Lemma 2.4. -/
theorem BRel.zcenter_le {A B : Subgroup G} (h : BRel A B) : zcenterIn (fstarIn A) ≤ B := by
  obtain ⟨X, hX, hle⟩ := h
  have hXz : ∀ y ∈ X, y ∈ fstarIn A := fun y hy => fittingIn_le_fstarIn A (hX hy)
  refine fun z hz => hle ⟨?_, hz.1⟩
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [show z * x * z⁻¹ = x from by
      rw [hz.2 x (hXz x hx), mul_assoc, mul_inv_cancel, mul_one]]
    exact hx
  · have hx' : z * x * z⁻¹ ∈ fstarIn A := hXz (z * x * z⁻¹) hx
    have hcomm := hz.2 (z * x * z⁻¹) hx'
    have h2 : z * (z * x * z⁻¹) = z * x := by rw [hcomm]; group
    have hzx : z * x * z⁻¹ = x := by
      calc z * x * z⁻¹ = z⁻¹ * (z * (z * x * z⁻¹)) := by group
        _ = z⁻¹ * (z * x) := by rw [h2]
        _ = x := by group
    rw [hzx] at hx
    exact hx

/-! ## 2. `F_π` inside `F` -/

/-- `F_π(K) ≤ F(K)`. -/
theorem fittingPiIn_le_fittingIn (π : Set ℕ) (K : Subgroup G) : fittingPiIn π K ≤ fittingIn K := by
  rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  exact ⟨(z : ↥K), z.2, rfl⟩

/-! ## 3. Coatomic subgroups of a finite group -/

/-- A maximal subgroup of a finite group is smaller than the group.  This is what turns
`BenderCtx.ih` (all smaller groups are D-groups) into a statement about `Ĥ` and about any
maximal `M`. -/
theorem IsCoatom.card_lt_card [Finite G] {H : Subgroup G} (h : IsCoatom H) :
    Nat.card H < Nat.card G :=
  Subgroup.card_lt_card_of_ne_top h.ne_top

/-- The same, for a subgroup which is only known to be proper. -/
theorem card_lt_card_of_ne_top [Finite G] {H : Subgroup G} (h : H ≠ ⊤) :
    Nat.card H < Nat.card G :=
  Subgroup.card_lt_card_of_ne_top h

section BenderSetupFacts

variable {G : Type} [Group G] [Finite G]

/-- `Ĥ` is a proper subgroup of `G`. -/
theorem BenderSetup.Hhat_ne_top (B : BenderSetup G) : B.Hhat ≠ ⊤ := B.Hhat_coatom.ne_top

/-- `Ĥ` is smaller than `G`; hence Bender's induction hypothesis applies to it. -/
theorem BenderSetup.card_Hhat_lt_card_G (B : BenderSetup G) :
    Nat.card B.Hhat < Nat.card G :=
  Subgroup.card_lt_card_of_ne_top B.Hhat_ne_top

end BenderSetupFacts

end Work.GW2
