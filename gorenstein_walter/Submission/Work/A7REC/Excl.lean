/-
Area `A7REC`: the design-pass-8 contract for **C2 + C3** (Suzuki 1959 p. 270) and its assembly.

The lead's pass-8 design (`Submission/Work/_design_gw/Core8.lean` §1) splits C2+C3 into eight
elementary leaves inside the stabilizer `H`, with **no** `SmallerDGroups`, and with one new input:
*one class of involutions* (area `FUS`'s `InvolutionFusionProp`).

This file copies that contract into the area's namespace (the copy of `C8A7RecHyps` is the
already-present `A7RecHyps`, whose body is literally the same), proves the **assembly**
`A7IndexSevenFromChar1Prop` from the eight leaves, and wires it to the older statements
(`A7IndexSevenFromCharProp`).

Nothing here is character theory; the leaves are delegated one by one.
-/
import Submission.Work.A7REC.Assembly
import Submission.Work.A7REC.Basic.local

namespace Work.A7REC

open Subgroup

/-! ## 1. One class of involutions (the input from area `FUS`) -/

/-- One class of involutions.  Verbatim from `Core8.lean` §1 (`C8OneClass`); it comes from area
`FUS`'s `InvolutionFusionProp` (`G` simple of order `2520` has no normal subgroup of index `2`). -/
def OneInvClass (G : Type) [Group G] : Prop :=
  ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y

/-- The degree-`6` representation data: exactly the output of `A7Char6Prop`.  Verbatim from
`Core8.lean` §1 (`C8Rep6`). -/
def Rep6 {G : Type} [Group G] (U : Subgroup G) (z : G) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G W) : Prop :=
  Module.finrank ℂ W = 6 ∧ LinearMap.trace ℂ W (ρ z) = 2 ∧
    (∀ u ∈ U, u ≠ 1 → LinearMap.trace ℂ W (ρ u) = 3) ∧
    (∀ x : G, orderOf x = 7 → LinearMap.trace ℂ W (ρ x) = -1)

/-- **The Suzuki configuration** `(U, S', τ')`.  Verbatim from `Core8.lean` §1 (`C8ExclHyps`). -/
def ExclHyps {G : Type} [Group G] (U S' : Subgroup G) (τ : G) : Prop :=
  Nat.card U = 3 ∧ Nat.card S' = 8 ∧ τ ∈ S' ∧ orderOf τ = 2 ∧ (∀ x ∈ S', x * τ = τ * x) ∧
    U.map (MulAut.conj τ).toMonoidHom = U ∧ S' ⊓ centralizer (U : Set G) = ⊥

/-! ## 2. The eight leaves (verbatim from `Core8.lean` §1, with `A7RecHyps` for `C8A7RecHyps`) -/

/-- **C2**: the configuration `(S', τ')` exists, with `S'` a Sylow `2`-subgroup. -/
def A7ConfigProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
    A7RecHyps G S z U V → OneInvClass G →
    ∃ (S' : Sylow 2 G) (τ : G), ExclHyps U (S' : Subgroup G) τ

/-- **C3a**: a nonzero vector fixed by `U` and by `S'`; `dim Fix(τ') = 4`, `dim Fix(⟨U, τ'⟩) = 3`
and `dim Fix(S') ≥ 2`, all inside `Fix(τ')`. -/
def A7FixedVectorProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G)
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ G W)
    (S' : Subgroup G) (τ : G),
    A7RecHyps G S z U V → OneInvClass G → Rep6 U z ρ → ExclHyps U S' τ →
    ∃ m : W, m ≠ 0 ∧ (∀ u ∈ U, ρ u m = m) ∧ ∀ x ∈ S', ρ x m = m

/-- **C3b**: the stabilizer of `m` contains `U` and `S'`, and `7 ∣ [G : H]`. -/
def A7StabilizerProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G)
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ G W)
    (S' : Subgroup G) (m : W),
    A7RecHyps G S z U V → Rep6 U z ρ → m ≠ 0 → (∀ u ∈ U, ρ u m = m) →
    (∀ x ∈ S', ρ x m = m) →
    ∃ H : Subgroup G, U ≤ H ∧ S' ≤ H ∧ 7 ∣ H.index

/-- **Exclusion of `|H| = 24`** (design pass 8 §1.4, the kernel argument). -/
def A7Excl24Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (U S' H : Subgroup G) (τ : G),
    ExclHyps U S' τ → U ≤ H → S' ≤ H → Nat.card H ≠ 24

/-- No subgroup of order `9` has all of its nonidentity elements `G`-conjugate into `U`. -/
def NoNine (G : Type) [Group G] (U : Subgroup G) : Prop :=
  ∀ P : Subgroup G, Nat.card P = 9 → ∃ p ∈ P, p ≠ 1 ∧ ∀ g : G, ∀ u ∈ U, g * u * g⁻¹ ≠ p

/-- From the representation: such a `P` would give `30 = 9 · dim Fix(P)`. -/
def A7NoNineProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (U : Subgroup G) (z : G)
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ G W),
    Rep6 U z ρ → NoNine G U

/-- **Exclusion of `|H| = 72`** (same kernel argument, using `NoNine`). -/
def A7Excl72Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (U S' H : Subgroup G) (τ : G),
    ExclHyps U S' τ → NoNine G U → U ≤ H → S' ≤ H → Nat.card H ≠ 72

/-- Every involution centralizer has order `24` and contains exactly one subgroup of order `3`. -/
def InvCent (G : Type) [Group G] : Prop :=
  ∀ x : G, orderOf x = 2 → Nat.card (centralizer ({x} : Set G)) = 24 ∧
    ∀ A B : Subgroup G, A ≤ centralizer ({x} : Set G) → B ≤ centralizer ({x} : Set G) →
      Nat.card A = 3 → Nat.card B = 3 → A = B

/-- `InvCent` for the `A₇` configuration. -/
def A7InvCentProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
    A7RecHyps G S z U V → OneInvClass G → InvCent G

/-- **Exclusion of `|H| = 120`** (the four cases `n₃ = 1, 40, 4, 10`). -/
def A7Excl120Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (U S' H : Subgroup G) (τ : G),
    ExclHyps U S' τ → InvCent G → U ≤ H → S' ≤ H → Nat.card H ≠ 120

/-- `A7IndexSevenFromCharProp` with the one-class input made explicit.  Verbatim from
`Core8.lean` §1. -/
def A7IndexSevenFromChar1Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
    A7RecHyps G S z U V → OneInvClass G →
    (∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (ρ : Representation ℂ G W), Rep6 U z ρ) →
    ∃ H : Subgroup G, H.index = 7

/-! ## 3. The assembly (proved here) -/

/-- **The assembly of C2+C3.**  The eight pass-8 leaves give `A7IndexSevenFromChar1Prop`: the
configuration `(S', τ')`, the fixed vector `m`, its stabilizer `H ⊇ ⟨U, S'⟩` with `7 ∣ [G : H]`,
then `24 ∣ |H|` (as `|U| = 3` and `|S'| = 8` are coprime), so
`|H| ∈ {24, 72, 120, 360}` (`card_eq_of_dvd_24_and_index_dvd_seven`), the three exclusions, and
`|H| = 360` gives index `7` (`index_eq_seven_of_card_eq_360`). -/
theorem a7IndexSevenFromChar1_of_leaves (hC2 : A7ConfigProp) (hC3a : A7FixedVectorProp)
    (hC3b : A7StabilizerProp) (h24 : A7Excl24Prop) (h79 : A7NoNineProp) (h72 : A7Excl72Prop)
    (h120 : A7Excl120Prop) (hIC : A7InvCentProp) : A7IndexSevenFromChar1Prop := by
  intro G _ _ S z U V hyps hone hrep
  obtain ⟨W, hAC, hMod, hFD, ρ, hρ⟩ := hrep
  letI : AddCommGroup W := hAC
  letI : Module ℂ W := hMod
  letI : FiniteDimensional ℂ W := hFD
  obtain ⟨S'y, τ, hconf⟩ := hC2 G S z U V hyps hone
  obtain ⟨m, hm0, hmU, hmS'⟩ := hC3a G S z U V W ρ (S'y : Subgroup G) τ hyps hone hρ hconf
  obtain ⟨H, hUH, hS'H, h7⟩ := hC3b G S z U V W ρ (S'y : Subgroup G) m hyps hρ hm0 hmU hmS'
  have hnin : NoNine G U := h79 G U z W ρ hρ
  have hic : InvCent G := hIC G S z U V hyps hone
  -- `24 ∣ |H|`: `3 ∣ |H|` and `8 ∣ |H|` are coprime
  have h24dvd : 24 ∣ Nat.card H := by
    have h3 : 3 ∣ Nat.card H := by
      rw [← hconf.1]
      exact Subgroup.card_dvd_of_le (α := G) hUH
    have h8 : 8 ∣ Nat.card H := by
      rw [← hconf.2.1]
      exact Subgroup.card_dvd_of_le (α := G) hS'H
    have : (24 : ℕ) = 3 * 8 := by norm_num
    rw [this]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 3 8 by norm_num) h3 h8
  have hcases := Basic.card_eq_of_dvd_24_and_index_dvd_seven G (A7RecCtx.ofHyps hyps) h24dvd h7
  rcases hcases with h | h | h | h
  · exact absurd h (h24 G U (S'y : Subgroup G) H τ hconf hUH hS'H)
  · exact absurd h (h72 G U (S'y : Subgroup G) H τ hconf hnin hUH hS'H)
  · exact absurd h (h120 G U (S'y : Subgroup G) H τ hconf hic hUH hS'H)
  · exact ⟨H, index_eq_seven_of_card_eq_360 (A7RecCtx.ofHyps hyps) h⟩

/-- The pass-4 target `A7IndexSevenFromCharProp` follows from the assembled C2+C3 once the
one-class input is available for every group satisfying `A7RecHyps` (in the lead's assembly this is
`FUS`'s `InvolutionFusionProp`, restricted to `|G| = 2520`). -/
theorem A7IndexSevenFromCharProp_of_char1 (h : A7IndexSevenFromChar1Prop)
    (hone : ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (z : G) (U V : Subgroup G),
      A7RecHyps G S z U V → OneInvClass G) :
    A7IndexSevenFromCharProp := by
  intro G _ _ S z U V hyps _hsmall hrep
  exact h G S z U V hyps (hone G S z U V hyps) hrep

end Work.A7REC
