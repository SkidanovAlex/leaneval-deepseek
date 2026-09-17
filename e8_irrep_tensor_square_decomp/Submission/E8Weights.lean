import Mathlib.Algebra.Lie.SerreConstruction
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Span.Basic
set_option linter.unnecessarySimpa false

noncomputable section

/-!
# Highest-weight machinery for the Serre-constructed e₈ (first brick)

The eventual goal of this workspace is the theorem `e8_irrep_tensor_square_decomp`: existence of a
779247-dimensional irreducible representation of `LieAlgebra.e₈ ℂ` (the Serre construction) whose
tensor square has 40 isotypic components.  The intended witness is the irreducible module of
highest weight `ω₁ + ω₈`.

This file is the first brick of that development.  It contains:

1. `Submission.WeightModule` (generic, fully proved): for *any* ring `A`, any families
   `p : ι → A` ("positive generators") and `h : κ → A` ("diagonal generators") and any
   prescribed values `w : κ → A`, the cyclic left module

       M = A / J ,    J = A · span { p i ,  h j - w j } ,    v = 1 + J ,

   together with the three basic facts that make `v` a highest-weight vector:
   `p i • v = 0` (annihilation by the positive generators), `h j • v = w j • v`
   (diagonal action by the weight), and cyclicity (`M = A • v`).

2. `Submission.E8Weights` (the e₈ instance): the Serre generators `Hᵢ, Eᵢ, Fᵢ` of
   `LieAlgebra.e₈ ℂ`, their images in the enveloping algebra `U(e₈)`, the module
   `M(λ) = U(e₈)/J(λ)` and highest-weight vector `v(λ)` for a weight `λ : Fin 8 → ℂ`
   (given by its values on the simple coroots), and the three theorems above specialized
   to e₈.

Bricks completed in this file:
  * (generic) cyclic highest-weight module with annihilation, diagonal action and cyclicity,
  * (e₈ instance) the Serre generators `Hᵢ,Eᵢ,Fᵢ` in `e₈`, their images in `U(e₈)`, and `M(λ)`,
  * (Serre relations, all six families) `⁅Hᵢ,Hⱼ⁆ = 0` (`serreLie_HH`), `⁅Hᵢ,Eⱼ⁆ = AᵢⱼEⱼ`
    (`serreLie_H_E`), `⁅Hᵢ,Fⱼ⁆ = -AᵢⱼFⱼ` (`serreLie_H_F`), `⁅Eᵢ,Fⱼ⁆ = δᵢⱼHᵢ`
    (`serreLie_E_F`), and the `ad`-nilpotency relations
    `ad(Eᵢ)^(-Aᵢⱼ)⁅Eᵢ,Eⱼ⁆ = 0` / `ad(Fᵢ)^(-Aᵢⱼ)⁅Fᵢ,Fⱼ⁆ = 0` (`serreLie_adE`, `serreLie_adF`)
    in `e₈`, with the companion commutators `commutator_H_E` / `commutator_H_F` /
    `commutator_E_F` in `U(e₈)`, and the auxiliary power-through-quotient helper `ad_pow_mk`.
    The `e₈` used by the goal statement is thus now known to satisfy the complete Serre
    presentation, by construction of the defining ideal `J`.

Known next bricks (not in this file yet):
  * the weight `ω₁+ω₈` is now data (`omegaOnePlusOmegaEight`), with `M(ω₁+ω₈)`, its
    highest-weight vector `v₍ω₁+ω₈₎`, the annihilation / diagonal action / cyclicity theorems
    instantiated (`e_annihilates_omega`, `h_acts_omega`, `cyclic_omega`, plus the concrete
    `H₁`/`H₈`/off-diagonal eigen-forms),
  * (weight-shift floor) `h_mul_f_comm` (`HⱼFᵢ = FᵢHⱼ - AⱼᵢFᵢ` in `U(e₈)`, ℂ-scalar form) and
    `f_shift_eigen`: if `w` is a joint eigenvector of the commuting `{Hⱼ}` with eigenvalues `νⱼ`,
    then `Fᵢ • w` is a joint eigenvector with eigenvalues `νⱼ - Aⱼᵢ`,
  * (instantiation on `Mω`) `h_eigen_omega` (vω is a joint eigenvector with eigenvalues
    `(ω₁+ω₈)(Hⱼ) = δ₁ⱼ + δ₈ⱼ`), `f_lower_eigen_omega`
    (`Hⱼ • (Fᵢ • vω) = (δ₁ⱼ + δ₈ⱼ - Aⱼᵢ) • (Fᵢ • vω)`, the lowering law for the weight
    `ω₁ + ω₈ - αᵢ`), and `f_vω_not_highest` (the lowered joint spectrum differs from the highest
    weight at the diagonal `j = i`),
  * (word lowering) `wordAction` (iterated `F`-generators), the generic `f_word_eigen`
    (after any word `w`, joint eigenvalues become `νⱼ - ∑ᵢ₌w Aⱼᵢ`), and `f_word_eigen_omega`
    on `Mω` (the word vectors carry weights `ω₁ + ω₈ - ∑ᵢ₌w αᵢ`),
  * (joint weight spaces on `Mω`) `jointWeightSpace μ` (the ℂ-submodule of vectors on which every
    `Hⱼ` acts by `μ(Hⱼ)`), with `vω_mem_weightSpace`, `wordAction_mem_weightSpace` and
    `weightSpace_ne_of_ne` (distinct weights give disjoint spaces; the zero-separation argument
    uses only one coordinate and ℂ being a field — no PBW needed),
  * (PBW / triangular-decomposition anchor — the next library floor, not yet provable here) the
    normal-form statement that every element of `U(e₈)` is a finite ℂ-linear combination of
    products `(f-word)·(h-word)·(e-word)`, with the module-level consequence that each joint
    weight space of `Mω` is finite-dimensional, spanned by the vectors
    `wordAction w vω` with `∑ᵢ₌w αᵢ = ω₁+ω₈-μ`.  Its prerequisites (associated-graded /
    normal forms for `U(e₈)`, i.e. PBW for the Serre-constructed algebra) are absent from the
    current Mathlib snapshot and are recorded in the dependency note above.
  * (deeper theory, largely absent from Mathlib) maximal proper submodules of `M(λ)`,
    finite-dimensionality with dimension 779247, complete reducibility,
  * the decomposition of the tensor square and the count 40.

The generic part needs nothing about e₈ (only that `U(e₈)` is a ring, which it is as the
enveloping algebra of any Lie algebra), so it is reusable verbatim for the companion g₂
problem and for any other highest-weight construction.

The following dependency note records a checked obstruction (not a claim of a proof):

`Mω ≠ 0` (equivalently `1 ∉ J(ω₁+ω₈)`) is not yet provable with the current Mathlib snapshot.
The word-length (tensor-algebra) grading of `U(e₈)` separates the identity from any left ideal
generated by elements with representatives of degree `≥ 1`, so it handles `eᵢ` and the `hᵢ` with
`λ(Hᵢ) = 0`; but two of the generators of `J(ω₁+ω₈)` are `h₀ − 1` and `h₇ − 1`, which have
degree-0 representatives (`λ(H₀) = λ(H₇) = 1`), and there the graded argument fails — exactly as
it must: in `sl₂` the statement `1 ∉ Ue + U(h−1)` is a genuine PBW-normal-form fact (observe
`h − 1 = ef − fe − 1`).  Hence `Mω ≠ 0`, the maximal-submodule brick, and the whole weight-space
theory sit on the PBW / triangular-decomposition chapter for `U(e₈)`, which is not in Mathlib and
is the next body of library work.  The joint commutativity `commutator_HH` laid in this file is the
precondition those weight spaces need once the PBW floor exists.  The next provable floor-1
weight-theory lemmas (statements identified, not yet committed) are the eigen-shift identities
`hⱼ • (fᵢ • w) = (νⱼ − Aⱼᵢ) • (fᵢ • w)` for joint eigenvectors `w`, derived from
`commutator_H_F`, which become the weight-lowering machinery of the eventual weight decomposition.
-/

open CartanMatrix
open UniversalEnvelopingAlgebra

namespace Submission.WeightModule

variable {A : Type*} [Ring A]

/-- The left ideal of `A` generated by the positive elements and the differences `h j - w j`.
(As a `Submodule A A`, i.e. a left ideal, since `•` is left multiplication.) -/
def spanIdeal {ι κ : Type*} (p : ι → A) (h : κ → A) (w : κ → A) : Submodule A A :=
  Submodule.span A (Set.range p ∪ Set.range (fun j => h j - w j))

/-- The cyclic module `A / J`. -/
abbrev M {ι κ : Type*} (p : ι → A) (h : κ → A) (w : κ → A) : Type _ :=
  A ⧸ spanIdeal p h w

/-- The cyclic (highest-weight) vector `1 + J`. -/
def v {ι κ : Type*} (p : ι → A) (h : κ → A) (w : κ → A) : M p h w :=
  Submodule.Quotient.mk (p := spanIdeal p h w) 1

/-- The positive generators annihilate the cyclic vector. -/
theorem positive_annihilates {ι κ : Type*} (p : ι → A) (h : κ → A) (w : κ → A) (i : ι) :
    p i • v p h w = 0 := by
  unfold v
  have hconv : p i • Submodule.Quotient.mk (p := spanIdeal p h w) 1 =
      Submodule.Quotient.mk (p := spanIdeal p h w) (p i) := by
    rw [← Submodule.Quotient.mk_smul]
    simp
  rw [hconv, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (s := Set.range p ∪ Set.range (fun j => h j - w j))
    (Set.mem_union_left _ (Set.mem_range_self i))

/-- The diagonal generators act on the cyclic vector by the prescribed values. -/
theorem diagonal_acts {ι κ : Type*} (p : ι → A) (h : κ → A) (w : κ → A) (j : κ) :
    h j • v p h w = w j • v p h w := by
  unfold v
  have h₁ : h j • Submodule.Quotient.mk (p := spanIdeal p h w) 1 =
      Submodule.Quotient.mk (p := spanIdeal p h w) (h j) := by
    rw [← Submodule.Quotient.mk_smul]; simp
  have h₂ : w j • Submodule.Quotient.mk (p := spanIdeal p h w) 1 =
      Submodule.Quotient.mk (p := spanIdeal p h w) (w j) := by
    rw [← Submodule.Quotient.mk_smul]; simp
  rw [h₁, h₂, Submodule.Quotient.eq]
  exact Submodule.subset_span (s := Set.range p ∪ Set.range (fun j => h j - w j))
    (Set.mem_union_right _ (Set.mem_range_self j))

/-- The cyclic vector generates the module: every element is `u • v` for some `u : A`. -/
theorem cyclic_generates {ι κ : Type*} (p : ι → A) (h : κ → A) (w : κ → A) :
    ∀ m : M p h w, ∃ u : A, u • v p h w = m := by
  intro m
  rcases Submodule.Quotient.mk_surjective (spanIdeal p h w) m with ⟨a, rfl⟩
  refine ⟨a, ?_⟩
  unfold v
  rw [← Submodule.Quotient.mk_smul]
  simp

end Submission.WeightModule

namespace Submission.E8Weights

/-- The Serre-constructed exceptional Lie algebra of type E₈ over ℂ. -/
abbrev L : Type := LieAlgebra.e₈ ℂ

/-- The free Lie algebra on the E₈ Serre generators, of which `L` is the quotient by the
Serre relations (see `J`). -/
abbrev F : Type := FreeLieAlgebra ℂ (Generators (Fin 8))

/-- The ideal of `F` generated by the E₈ Serre relations. -/
abbrev J : LieIdeal ℂ F := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈

/-- The e₈ Serre generator `Hᵢ`, viewed inside the Serre-constructed Lie algebra. -/
def SerreH (i : Fin 8) : L := LieSubmodule.Quotient.mk (N := J) (FreeLieAlgebra.of ℂ (Generators.H i))

/-- The e₈ Serre generator `Eᵢ`, viewed inside the Serre-constructed Lie algebra. -/
def SerreE (i : Fin 8) : L := LieSubmodule.Quotient.mk (N := J) (FreeLieAlgebra.of ℂ (Generators.E i))

/-- The e₈ Serre generator `Fᵢ`, viewed inside the Serre-constructed Lie algebra. -/
def SerreF (i : Fin 8) : L := LieSubmodule.Quotient.mk (N := J) (FreeLieAlgebra.of ℂ (Generators.F i))

/-- The enveloping algebra `U(e₈)`. -/
abbrev U : Type := UniversalEnvelopingAlgebra ℂ L

/-- The simple-root images in `U(e₈)`; these are the positive generators of the highest-weight
machinery. -/
def e (i : Fin 8) : U := ι ℂ (SerreE i)

/-- The diagonal (Cartan) generator images in `U(e₈)`. -/
def h (i : Fin 8) : U := ι ℂ (SerreH i)

/-- The negative-root generator images in `U(e₈)`. -/
def f (i : Fin 8) : U := ι ℂ (SerreF i)

/-- A weight as a function `Fin 8 → ℂ` (its values on the simple coroots), lifted into
`U(e₈)`; `weightInU λ j` is `(λ j) • 1 ∈ U(e₈)`. -/
def weightInU (lam : Fin 8 → ℂ) (j : Fin 8) : U := algebraMap ℂ U (lam j)

/-- The highest-weight module `M(lam) = U(e₈) / J(lam)`, where `J(lam)` is the left ideal
generated by the positive generators and the differences `Hᵢ - lam(Hᵢ)`. -/
abbrev M (lam : Fin 8 → ℂ) : Type :=
  Submission.WeightModule.M e h (weightInU lam)

/-- The highest-weight vector `v(lam) = 1 + J(lam)`. -/
def v (lam : Fin 8 → ℂ) : M lam :=
  Submission.WeightModule.v e h (weightInU lam)

/-- `Eᵢ` annihilates the highest-weight vector: `Eᵢ • v(lam) = 0`. -/
theorem e_annihilates (lam : Fin 8 → ℂ) (i : Fin 8) : e i • v lam = 0 :=
  Submission.WeightModule.positive_annihilates e h (weightInU lam) i

/-- The diagonal generators act by the weight: `Hᵢ • v(lam) = lam(Hᵢ) • v(lam)`. -/
theorem h_acts (lam : Fin 8 → ℂ) (i : Fin 8) : h i • v lam = weightInU lam i • v lam :=
  Submission.WeightModule.diagonal_acts e h (weightInU lam) i

/-- `v(lam)` is a cyclic vector: every element of `M(lam)` is `u • v(lam)` for some
`u : U(e₈)`. -/
theorem cyclic (lam : Fin 8 → ℂ) : ∀ m : M lam, ∃ u : U, u • v lam = m :=
  Submission.WeightModule.cyclic_generates e h (weightInU lam)

/-- The highest weight `ω₁ + ω₈` of the intended representation, as a function of its values
on the simple coroots `Hᵢ`.  A fundamental weight is determined by `ωᵢ(Hⱼ) = δᵢⱼ`, so
`(ω₁+ω₈)(Hᵢ) = δ₁ᵢ + δ₈ᵢ` (Bourbaki numbering; in `Fin 8` indices `1` and `8` are `0` and `7`). -/
def omegaOnePlusOmegaEight : Fin 8 → ℂ :=
  fun i => (if i = 0 then 1 else 0 : ℂ) + (if i = 7 then 1 else 0)

@[simp] lemma omegaOnePlusOmegaEight_apply_zero : omegaOnePlusOmegaEight 0 = 1 := by
  simp [omegaOnePlusOmegaEight]

@[simp] lemma omegaOnePlusOmegaEight_apply_seven : omegaOnePlusOmegaEight 7 = 1 := by
  simp [omegaOnePlusOmegaEight]

lemma omegaOnePlusOmegaEight_apply_of_ne (i : Fin 8) (h0 : i ≠ 0) (h7 : i ≠ 7) :
    omegaOnePlusOmegaEight i = 0 := by
  simp [omegaOnePlusOmegaEight, h0, h7]

/-- The intended representation: the cyclic module `M(ω₁+ω₈) = U(e₈) / J(ω₁+ω₈)`. -/
abbrev Mω : Type := M omegaOnePlusOmegaEight

/-- The highest-weight vector of `M(ω₁+ω₈)`. -/
abbrev vω : Mω := v omegaOnePlusOmegaEight

/-- `Eᵢ` annihilates the highest-weight vector of the `ω₁+ω₈` module: `Eᵢ • v₍ω₁+ω₈₎ = 0`. -/
theorem e_annihilates_omega (i : Fin 8) : e i • vω = 0 :=
  e_annihilates omegaOnePlusOmegaEight i

/-- The diagonal generators act on `v₍ω₁+ω₈₎` by the weight values `(ω₁+ω₈)(Hᵢ) = δ₁ᵢ + δ₈ᵢ`. -/
theorem h_acts_omega (i : Fin 8) : h i • vω = weightInU omegaOnePlusOmegaEight i • vω :=
  h_acts omegaOnePlusOmegaEight i

/-- `M(ω₁+ω₈)` is cyclically generated by `v₍ω₁+ω₈₎`. -/
theorem cyclic_omega : ∀ m : Mω, ∃ u : U, u • vω = m :=
  cyclic omegaOnePlusOmegaEight

/-- The weight value at the first simple coroot: `(ω₁+ω₈)(H₁) = 1`, so `H₁ • v = v`. -/
lemma weight_omega_H_one : weightInU omegaOnePlusOmegaEight 0 = (1 : U) := by
  simp [weightInU]

/-- The weight value at the last simple coroot: `(ω₁+ω₈)(H₈) = 1`, so `H₈ • v = v`. -/
lemma weight_omega_H_eight : weightInU omegaOnePlusOmegaEight 7 = (1 : U) := by
  simp [weightInU]

/-- The weight value at the remaining simple coroots: `(ω₁+ω₈)(Hᵢ) = 0` for `i ≠ 1, 8`. -/
lemma weight_omega_of_ne (i : Fin 8) (h0 : i ≠ 0) (h7 : i ≠ 7) :
    weightInU omegaOnePlusOmegaEight i = 0 := by
  simp [weightInU, omegaOnePlusOmegaEight, h0, h7]

/-- Concretely: `H₁ • v₍ω₁+ω₈₎ = v₍ω₁+ω₈₎`. -/
theorem h₁_acts_omega : h 0 • vω = vω := by
  simpa [weight_omega_H_one] using h_acts_omega 0

/-- Concretely: `H₈ • v₍ω₁+ω₈₎ = v₍ω₁+ω₈₎`. -/
theorem h₈_acts_omega : h 7 • vω = vω := by
  simpa [weight_omega_H_eight] using h_acts_omega 7

/-- Concretely: `Hᵢ • v₍ω₁+ω₈₎ = 0` for `i ≠ 1, 8`. -/
theorem h_of_ne_acts_omega (i : Fin 8) (h0 : i ≠ 0) (h7 : i ≠ 7) : h i • vω = 0 := by
  simpa [weight_omega_of_ne i h0 h7] using h_acts_omega i



section SerreRelations

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- The relation element `⁅Hᵢ,Eⱼ⁆ - AᵢⱼEⱼ` of the E₈ Serre presentation lies in the Serre ideal
`J`, so it vanishes in `e₈`. -/
lemma HE_mem_J (i j : Fin 8) :
    CartanMatrix.Relations.HE ℂ CartanMatrix.E₈ (i, j) ∈ (J : Submodule ℂ F) := by
  exact LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)

/-- `HE ℂ E₈ (i,j)` is (definitionally) the commutator difference `⁅Hᵢ,Eⱼ⁆ - AᵢⱼEⱼ` in `F`. -/
lemma HE_eq (i j : Fin 8) :
    CartanMatrix.Relations.HE ℂ CartanMatrix.E₈ (i, j) =
      ⁅FreeLieAlgebra.of ℂ (Generators.H i), FreeLieAlgebra.of ℂ (Generators.E j)⁆
        - (CartanMatrix.E₈ i j) • FreeLieAlgebra.of ℂ (Generators.E j) := by
  rfl

/-- The first Serre relation in `e₈`: `⁅Hᵢ, Eⱼ⁆ = Aᵢⱼ • Eⱼ`. -/
lemma serreLie_H_E (i j : Fin 8) : ⁅SerreH i, SerreE j⁆ = (CartanMatrix.E₈ i j) • SerreE j := by
  unfold SerreH SerreE
  change LieSubmodule.Quotient.mk (N := J) ⁅FreeLieAlgebra.of ℂ (Generators.H i),
      FreeLieAlgebra.of ℂ (Generators.E j)⁆ =
      (CartanMatrix.E₈ i j) • LieSubmodule.Quotient.mk (N := J) (FreeLieAlgebra.of ℂ (Generators.E j))
  have hz : (CartanMatrix.E₈ i j) • LieSubmodule.Quotient.mk (N := J)
        (FreeLieAlgebra.of ℂ (Generators.E j)) =
      LieSubmodule.Quotient.mk (N := J) ((CartanMatrix.E₈ i j) • FreeLieAlgebra.of ℂ (Generators.E j)) := by
    simpa using (map_zsmul (f := Submodule.mkQ (J.toSubmodule)) (CartanMatrix.E₈ i j)
      (FreeLieAlgebra.of ℂ (Generators.E j)))
  rw [hz]
  rw [← sub_eq_zero]
  change LieSubmodule.Quotient.mk (N := J)
      (⁅FreeLieAlgebra.of ℂ (Generators.H i), FreeLieAlgebra.of ℂ (Generators.E j)⁆
        - (CartanMatrix.E₈ i j) • FreeLieAlgebra.of ℂ (Generators.E j)) = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  simpa [HE_eq] using HE_mem_J i j

/-- The corresponding commutator relation inside the enveloping algebra `U(e₈)`:
`Hᵢ Eⱼ - Eⱼ Hᵢ = Aᵢⱼ • Eⱼ`.  This is the form used when `Hᵢ, Eⱼ` act on a `U(e₈)`-module. -/
lemma commutator_H_E (i j : Fin 8) :
    (ι ℂ (SerreH i)) * (ι ℂ (SerreE j)) - (ι ℂ (SerreE j)) * (ι ℂ (SerreH i)) =
      (CartanMatrix.E₈ i j) • (ι ℂ (SerreE j)) := by
  rw [← Ring.lie_def]
  rw [← LieHom.map_lie (f := (ι ℂ))]
  rw [serreLie_H_E i j]
  simpa using (map_zsmul (f := (UniversalEnvelopingAlgebra.ι ℂ : L →ₗ[ℂ] U)) (CartanMatrix.E₈ i j) (SerreE j))

/-- The relation element `⁅Hᵢ,Fⱼ⁆ + AᵢⱼFⱼ` of the E₈ Serre presentation lies in `J`. -/
lemma HF_mem_J (i j : Fin 8) :
    CartanMatrix.Relations.HF ℂ CartanMatrix.E₈ (i, j) ∈ (J : Submodule ℂ F) := by
  exact LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)

/-- `HF ℂ E₈ (i,j)` is (definitionally) `⁅Hᵢ,Fⱼ⁆ + AᵢⱼFⱼ` in `F`. -/
lemma HF_eq (i j : Fin 8) :
    CartanMatrix.Relations.HF ℂ CartanMatrix.E₈ (i, j) =
      ⁅FreeLieAlgebra.of ℂ (Generators.H i), FreeLieAlgebra.of ℂ (Generators.F j)⁆
        + (CartanMatrix.E₈ i j) • FreeLieAlgebra.of ℂ (Generators.F j) := by
  rfl

/-- The Serre relation `⁅Hᵢ, Fⱼ⁆ = -Aᵢⱼ • Fⱼ` in `e₈`. -/
lemma serreLie_H_F (i j : Fin 8) : ⁅SerreH i, SerreF j⁆ = (-(CartanMatrix.E₈ i j)) • SerreF j := by
  unfold SerreH SerreF
  change LieSubmodule.Quotient.mk (N := J) ⁅FreeLieAlgebra.of ℂ (Generators.H i),
      FreeLieAlgebra.of ℂ (Generators.F j)⁆ =
      (-(CartanMatrix.E₈ i j)) • LieSubmodule.Quotient.mk (N := J) (FreeLieAlgebra.of ℂ (Generators.F j))
  have hz : (-(CartanMatrix.E₈ i j)) • LieSubmodule.Quotient.mk (N := J)
        (FreeLieAlgebra.of ℂ (Generators.F j)) =
      LieSubmodule.Quotient.mk (N := J) ((-(CartanMatrix.E₈ i j)) • FreeLieAlgebra.of ℂ (Generators.F j)) := by
    simpa using (map_zsmul (f := Submodule.mkQ (J.toSubmodule)) (-(CartanMatrix.E₈ i j))
      (FreeLieAlgebra.of ℂ (Generators.F j)))
  rw [hz]
  rw [← sub_eq_zero]
  change LieSubmodule.Quotient.mk (N := J)
      (⁅FreeLieAlgebra.of ℂ (Generators.H i), FreeLieAlgebra.of ℂ (Generators.F j)⁆
        - (-(CartanMatrix.E₈ i j)) • FreeLieAlgebra.of ℂ (Generators.F j)) = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  have hdeq : ⁅FreeLieAlgebra.of ℂ (Generators.H i), FreeLieAlgebra.of ℂ (Generators.F j)⁆
        - (-(CartanMatrix.E₈ i j)) • FreeLieAlgebra.of ℂ (Generators.F j) =
      CartanMatrix.Relations.HF ℂ CartanMatrix.E₈ (i, j) := by
    rw [HF_eq i j]
    simp [sub_eq_add_neg]
  simpa [← hdeq] using HF_mem_J i j

/-- The corresponding commutator relation inside `U(e₈)`:
`Hᵢ Fⱼ - Fⱼ Hᵢ = -Aᵢⱼ • Fⱼ`. -/
lemma commutator_H_F (i j : Fin 8) :
    (ι ℂ (SerreH i)) * (ι ℂ (SerreF j)) - (ι ℂ (SerreF j)) * (ι ℂ (SerreH i)) =
      (-(CartanMatrix.E₈ i j)) • (ι ℂ (SerreF j)) := by
  rw [← Ring.lie_def]
  rw [← LieHom.map_lie (f := (ι ℂ))]
  rw [serreLie_H_F i j]
  simpa using (map_zsmul (f := (ι ℂ : L →ₗ[ℂ] U)) (-(CartanMatrix.E₈ i j)) (SerreF j))

/-- The relation element of the `Eᵢ,Fⱼ` Serre presentation (`⁅Eᵢ,Fᵢ⁆ - Hᵢ` if `i = j`, and
`⁅Eᵢ,Fⱼ⁆` otherwise) lies in `J`. -/
lemma EF_mem_J (i j : Fin 8) :
    CartanMatrix.Relations.EF ℂ (i, j) ∈ (J : Submodule ℂ F) := by
  exact LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)

/-- `EF ℂ E₈ (i,j)` is (definitionally, up to the case split on `i = j`)
`⁅Eᵢ,Fⱼ⁆ - δᵢⱼHᵢ` in `F`. -/
lemma EF_eq (i j : Fin 8) :
    CartanMatrix.Relations.EF ℂ (i, j) =
      ⁅FreeLieAlgebra.of ℂ (Generators.E i), FreeLieAlgebra.of ℂ (Generators.F j)⁆
        - (if i = j then FreeLieAlgebra.of ℂ (Generators.H i) else 0) := by
  by_cases h : i = j
  · simp [CartanMatrix.Relations.EF, h]
  · simp [CartanMatrix.Relations.EF, h]

/-- The Serre relation `⁅Eᵢ, Fⱼ⁆ = δᵢⱼ • Hᵢ` in `e₈` (Kronecker δ). -/
lemma serreLie_E_F (i j : Fin 8) : ⁅SerreE i, SerreF j⁆ = if i = j then SerreH i else 0 := by
  by_cases h : i = j
  · subst h
    simp
    unfold SerreE SerreF SerreH
    change LieSubmodule.Quotient.mk (N := J) ⁅FreeLieAlgebra.of ℂ (Generators.E i),
        FreeLieAlgebra.of ℂ (Generators.F i)⁆ =
        LieSubmodule.Quotient.mk (N := J) (FreeLieAlgebra.of ℂ (Generators.H i))
    rw [← sub_eq_zero]
    change LieSubmodule.Quotient.mk (N := J)
        (⁅FreeLieAlgebra.of ℂ (Generators.E i), FreeLieAlgebra.of ℂ (Generators.F i)⁆
          - FreeLieAlgebra.of ℂ (Generators.H i)) = 0
    rw [LieSubmodule.Quotient.mk_eq_zero']
    have hdeq : ⁅FreeLieAlgebra.of ℂ (Generators.E i), FreeLieAlgebra.of ℂ (Generators.F i)⁆
          - FreeLieAlgebra.of ℂ (Generators.H i) =
        CartanMatrix.Relations.EF ℂ (i, i) := by
      simp [CartanMatrix.Relations.EF]
    simpa [← hdeq] using EF_mem_J i i
  · simp [h]
    unfold SerreE SerreF
    change LieSubmodule.Quotient.mk (N := J) ⁅FreeLieAlgebra.of ℂ (Generators.E i),
        FreeLieAlgebra.of ℂ (Generators.F j)⁆ = 0
    rw [LieSubmodule.Quotient.mk_eq_zero']
    have hdeq : ⁅FreeLieAlgebra.of ℂ (Generators.E i), FreeLieAlgebra.of ℂ (Generators.F j)⁆ =
        CartanMatrix.Relations.EF ℂ (i, j) := by
      simp [CartanMatrix.Relations.EF, h]
    simpa [hdeq] using EF_mem_J i j

/-- The corresponding commutator relation inside `U(e₈)`:
`Eᵢ Fⱼ - Fⱼ Eᵢ = δᵢⱼ Hᵢ`. -/
lemma commutator_E_F (i j : Fin 8) :
    (ι ℂ (SerreE i)) * (ι ℂ (SerreF j)) - (ι ℂ (SerreF j)) * (ι ℂ (SerreE i)) =
      if i = j then (ι ℂ (SerreH i)) else 0 := by
  rw [← Ring.lie_def]
  rw [← LieHom.map_lie (f := (ι ℂ))]
  rw [serreLie_E_F i j]
  by_cases h : i = j <;> simp [h]

/-- The `ad(Eᵢ)`-nilpotency relation generator of the E₈ Serre presentation lies in `J`. -/
lemma adE_mem_J (i j : Fin 8) :
    CartanMatrix.Relations.adE ℂ CartanMatrix.E₈ (i, j) ∈ (J : Submodule ℂ F) := by
  exact LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)

/-- `adE ℂ E₈ (i,j)` is (definitionally) `ad(Eᵢ)^(-Aᵢⱼ) ⁅Eᵢ,Eⱼ⁆` in `F`. -/
lemma adE_eq (i j : Fin 8) :
    CartanMatrix.Relations.adE ℂ CartanMatrix.E₈ (i, j) =
      ((LieAlgebra.ad ℂ F (FreeLieAlgebra.of ℂ (Generators.E i))) ^ (-(CartanMatrix.E₈ i j)).toNat)
        (⁅FreeLieAlgebra.of ℂ (Generators.E i), FreeLieAlgebra.of ℂ (Generators.E j)⁆) := by
  rfl

/-- The `ad(Fᵢ)`-nilpotency relation generator of the E₈ Serre presentation lies in `J`. -/
lemma adF_mem_J (i j : Fin 8) :
    CartanMatrix.Relations.adF ℂ CartanMatrix.E₈ (i, j) ∈ (J : Submodule ℂ F) := by
  exact LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)

/-- `adF ℂ E₈ (i,j)` is (definitionally) `ad(Fᵢ)^(-Aᵢⱼ) ⁅Fᵢ,Fⱼ⁆` in `F`. -/
lemma adF_eq (i j : Fin 8) :
    CartanMatrix.Relations.adF ℂ CartanMatrix.E₈ (i, j) =
      ((LieAlgebra.ad ℂ F (FreeLieAlgebra.of ℂ (Generators.F i))) ^ (-(CartanMatrix.E₈ i j)).toNat)
        (⁅FreeLieAlgebra.of ℂ (Generators.F i), FreeLieAlgebra.of ℂ (Generators.F j)⁆) := by
  rfl

/-- Adjoint powers pass through the quotient map from `F` to `e₈` (the only genuinely new
mechanism in the `ad`-relations: an induction over the power). -/
lemma ad_pow_mk (x y : F) (n : ℕ) :
    ((LieAlgebra.ad ℂ (F ⧸ J) (LieSubmodule.Quotient.mk (N := J) x)) ^ n)
        (LieSubmodule.Quotient.mk (N := J) y) =
      LieSubmodule.Quotient.mk (N := J) (((LieAlgebra.ad ℂ F x) ^ n) y) := by
  rw [Module.End.pow_apply, Module.End.pow_apply]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [ih]
      rfl

/-- The `ad`-nilpotency Serre relation in `e₈`:
`ad(Eᵢ)^(-Aᵢⱼ) ⁅Eᵢ,Eⱼ⁆ = 0` for all `i, j` (for `i ≠ j` this is the classical
`ad(Eᵢ)^{1-Aᵢⱼ} Eⱼ = 0`, and for `i = j` it is trivial since `⁅Eᵢ,Eᵢ⁆ = 0`). -/
lemma serreLie_adE (i j : Fin 8) :
    ((LieAlgebra.ad ℂ L (SerreE i)) ^ (-(CartanMatrix.E₈ i j)).toNat) (⁅SerreE i, SerreE j⁆) = 0 := by
  unfold SerreE
  change ((LieAlgebra.ad ℂ (F ⧸ J) (LieSubmodule.Quotient.mk (N := J) (FreeLieAlgebra.of ℂ (Generators.E i)))) ^
        (-(CartanMatrix.E₈ i j)).toNat)
      (LieSubmodule.Quotient.mk (N := J) ⁅FreeLieAlgebra.of ℂ (Generators.E i),
        FreeLieAlgebra.of ℂ (Generators.E j)⁆) = 0
  rw [ad_pow_mk (FreeLieAlgebra.of ℂ (Generators.E i))
      ⁅FreeLieAlgebra.of ℂ (Generators.E i), FreeLieAlgebra.of ℂ (Generators.E j)⁆
      (-(CartanMatrix.E₈ i j)).toNat]
  rw [LieSubmodule.Quotient.mk_eq_zero']
  have hdeq : ((LieAlgebra.ad ℂ F (FreeLieAlgebra.of ℂ (Generators.E i))) ^ (-(CartanMatrix.E₈ i j)).toNat)
        (⁅FreeLieAlgebra.of ℂ (Generators.E i), FreeLieAlgebra.of ℂ (Generators.E j)⁆) =
      CartanMatrix.Relations.adE ℂ CartanMatrix.E₈ (i, j) := (adE_eq i j).symm
  simpa [hdeq] using adE_mem_J i j

/-- The `ad`-nilpotency Serre relation in `e₈` for the negative generators:
`ad(Fᵢ)^(-Aᵢⱼ) ⁅Fᵢ,Fⱼ⁆ = 0`. -/
lemma serreLie_adF (i j : Fin 8) :
    ((LieAlgebra.ad ℂ L (SerreF i)) ^ (-(CartanMatrix.E₈ i j)).toNat) (⁅SerreF i, SerreF j⁆) = 0 := by
  unfold SerreF
  change ((LieAlgebra.ad ℂ (F ⧸ J) (LieSubmodule.Quotient.mk (N := J) (FreeLieAlgebra.of ℂ (Generators.F i)))) ^
        (-(CartanMatrix.E₈ i j)).toNat)
      (LieSubmodule.Quotient.mk (N := J) ⁅FreeLieAlgebra.of ℂ (Generators.F i),
        FreeLieAlgebra.of ℂ (Generators.F j)⁆) = 0
  rw [ad_pow_mk (FreeLieAlgebra.of ℂ (Generators.F i))
      ⁅FreeLieAlgebra.of ℂ (Generators.F i), FreeLieAlgebra.of ℂ (Generators.F j)⁆
      (-(CartanMatrix.E₈ i j)).toNat]
  rw [LieSubmodule.Quotient.mk_eq_zero']
  have hdeq : ((LieAlgebra.ad ℂ F (FreeLieAlgebra.of ℂ (Generators.F i))) ^ (-(CartanMatrix.E₈ i j)).toNat)
        (⁅FreeLieAlgebra.of ℂ (Generators.F i), FreeLieAlgebra.of ℂ (Generators.F j)⁆) =
      CartanMatrix.Relations.adF ℂ CartanMatrix.E₈ (i, j) := (adF_eq i j).symm
  simpa [hdeq] using adF_mem_J i j

/-- The relation element `⁅Hᵢ,Hⱼ⁆` of the E₈ Serre presentation lies in `J`. -/
lemma HH_mem_J (i j : Fin 8) :
    CartanMatrix.Relations.HH ℂ (i, j) ∈ (J : Submodule ℂ F) := by
  exact LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)

/-- `HH ℂ (i,j)` is (definitionally) `⁅Hᵢ,Hⱼ⁆` in `F`. -/
lemma HH_eq (i j : Fin 8) :
    CartanMatrix.Relations.HH ℂ (i, j) =
      ⁅FreeLieAlgebra.of ℂ (Generators.H i), FreeLieAlgebra.of ℂ (Generators.H j)⁆ := by
  rfl

/-- The Serre relation `⁅Hᵢ, Hⱼ⁆ = 0` in `e₈`: the diagonal generators commute. -/
lemma serreLie_HH (i j : Fin 8) : ⁅SerreH i, SerreH j⁆ = 0 := by
  unfold SerreH
  change LieSubmodule.Quotient.mk (N := J) ⁅FreeLieAlgebra.of ℂ (Generators.H i),
      FreeLieAlgebra.of ℂ (Generators.H j)⁆ = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  have hdeq : ⁅FreeLieAlgebra.of ℂ (Generators.H i), FreeLieAlgebra.of ℂ (Generators.H j)⁆ =
      CartanMatrix.Relations.HH ℂ (i, j) := (HH_eq i j).symm
  simpa [hdeq] using HH_mem_J i j

/-- The corresponding commutator relation inside `U(e₈)`: the diagonal generators commute,
`HᵢHⱼ = HⱼHᵢ`, which is the precondition for any joint-eigenvector (weight-space) argument
on the modules `M(λ)`. -/
lemma commutator_HH (i j : Fin 8) :
    (ι ℂ (SerreH i)) * (ι ℂ (SerreH j)) = (ι ℂ (SerreH j)) * (ι ℂ (SerreH i)) := by
  have hzero : ⁅ι ℂ (SerreH i), ι ℂ (SerreH j)⁆ = 0 := by
    rw [← LieHom.map_lie (f := (ι ℂ))]
    rw [serreLie_HH i j]
    rw [map_zero]
  have hcomm : (ι ℂ (SerreH i)) * (ι ℂ (SerreH j)) - (ι ℂ (SerreH j)) * (ι ℂ (SerreH i)) = 0 := by
    simpa [Ring.lie_def] using hzero
  exact sub_eq_zero.mp hcomm

end SerreRelations

section WeightShifts

variable {M : Type*} [AddCommGroup M] [Module U M] [Module ℂ M] [IsScalarTower ℂ U M]

/-- Ring identity used by the weight shift: `Hⱼ Fᵢ = Fᵢ Hⱼ - Aⱼᵢ Fᵢ` in `U(e₈)` (ℂ-scalar form). -/
lemma h_mul_f_comm (j i : Fin 8) :
    h j * f i = f i * h j - ((CartanMatrix.E₈ j i : ℂ) • f i) := by
  have hz : ((-(CartanMatrix.E₈ j i) : ℤ) • f i) = -(((CartanMatrix.E₈ j i : ℂ) • f i)) := by
    rw [neg_zsmul, Int.cast_smul_eq_zsmul]
  have hc : h j * f i - f i * h j = -(((CartanMatrix.E₈ j i : ℂ) • f i)) := by
    change (UniversalEnvelopingAlgebra.ι ℂ (SerreH j)) * (UniversalEnvelopingAlgebra.ι ℂ (SerreF i)) -
        (UniversalEnvelopingAlgebra.ι ℂ (SerreF i)) * (UniversalEnvelopingAlgebra.ι ℂ (SerreH j)) =
        -(((CartanMatrix.E₈ j i : ℂ) • (UniversalEnvelopingAlgebra.ι ℂ (SerreF i))))
    rw [commutator_H_F j i]
    rw [neg_zsmul, Int.cast_smul_eq_zsmul]
  rw [sub_eq_add_neg]
  rw [add_comm]
  exact sub_eq_iff_eq_add.mp hc

/-- The `Fᵢ` weight shift: if `w` is a joint eigenvector of the commuting family `{Hⱼ}` with
eigenvalues `νⱼ`, then `Fᵢ • w` is a joint eigenvector with eigenvalues `νⱼ - Aⱼᵢ`. -/
lemma f_shift_eigen (w : M) (ν : Fin 8 → ℂ) (hw : ∀ j, h j • w = ν j • w) (i j : Fin 8) :
    h j • (f i • w) = (ν j - (CartanMatrix.E₈ j i : ℂ)) • (f i • w) := by
  rw [← mul_smul]
  rw [h_mul_f_comm j i]
  rw [sub_smul, mul_smul]
  rw [hw]
  rw [smul_comm]
  rw [IsScalarTower.smul_assoc]
  rw [sub_smul]


/-- The action of a word of `F`-generators on a module element: `Fᵢ₀ • (Fᵢ₁ • ⋯ m)`
(i.e. letters are applied left-to-right, each to the result of the rest of the word). -/
def wordAction {M : Type*} [AddCommGroup M] [Module U M] : List (Fin 8) → M → M
  | [], m => m
  | i :: w, m => wordAction w (f i • m)

/-- Word lowering (generic): if `m` is a joint eigenvector of `{Hⱼ}` with eigenvalues `νⱼ`, then
after applying the word `w` of `F`-generators the result is still a joint eigenvector, with
eigenvalues `νⱼ - ∑ᵢ₌w Aⱼᵢ` at `Hⱼ`. -/
lemma f_word_eigen {M : Type*} [AddCommGroup M] [Module U M] [Module ℂ M]
    [IsScalarTower ℂ U M] (w : List (Fin 8)) (m : M) (ν : Fin 8 → ℂ)
    (hm : ∀ j, h j • m = ν j • m) (j : Fin 8) :
    h j • wordAction w m =
      (ν j - (w.map (fun i => (CartanMatrix.E₈ j i : ℂ))).sum) • wordAction w m := by
  have hrec : ∀ (w : List (Fin 8)) (m : M) (ν : Fin 8 → ℂ),
      (∀ j, h j • m = ν j • m) → ∀ j, h j • wordAction w m =
        (ν j - (w.map (fun i => (CartanMatrix.E₈ j i : ℂ))).sum) • wordAction w m := by
    intro w
    induction w with
    | nil =>
        intro m ν hm j
        simpa [wordAction] using hm j
    | cons i w ih =>
        intro m ν hm j
        rw [wordAction]
        have hfi : ∀ j', h j' • (f i • m) =
            (ν j' - (CartanMatrix.E₈ j' i : ℂ)) • (f i • m) :=
          fun j' => by simpa using f_shift_eigen m ν hm i j'
        have hsum : ((i :: w).map (fun i => (CartanMatrix.E₈ j i : ℂ))).sum =
            (CartanMatrix.E₈ j i : ℂ) + (w.map (fun i => (CartanMatrix.E₈ j i : ℂ))).sum := by
          simp [List.map_cons]
        rw [hsum]
        rw [show (ν j - ((CartanMatrix.E₈ j i : ℂ) +
            (w.map (fun i => (CartanMatrix.E₈ j i : ℂ))).sum)) =
            (ν j - (CartanMatrix.E₈ j i : ℂ)) - (w.map (fun i => (CartanMatrix.E₈ j i : ℂ))).sum by
          ring]
        exact ih (f i • m) (fun j' => ν j' - (CartanMatrix.E₈ j' i : ℂ)) hfi j
  exact hrec w m ν hm j

end WeightShifts

section MωWeightShift

/-- On `Mω`, the enveloping-algebra scalar action of `algebraMap ℂ U c` is the ℂ-action of `c`
(consequence of `IsScalarTower ℂ U Mω`). -/
lemma algebraMap_smul_Mω (c : ℂ) (m : Mω) : (algebraMap ℂ U c) • m = c • m := by
  calc
    (algebraMap ℂ U c) • m = (algebraMap ℂ U c * (1 : U)) • m := by simp
    _ = (c • (1 : U)) • m := by rw [← Algebra.smul_def]
    _ = c • ((1 : U) • m) := by rw [IsScalarTower.smul_assoc]
    _ = c • m := by simp

/-- The highest-weight vector `vω` is a joint eigenvector of the commuting diagonals `{Hⱼ}` with
eigenvalues `(ω₁+ω₈)(Hⱼ) = δ₁ⱼ + δ₈ⱼ`. -/
lemma h_eigen_omega (j : Fin 8) : h j • vω = (omegaOnePlusOmegaEight j : ℂ) • vω := by
  rw [h_acts_omega j]
  unfold weightInU
  exact algebraMap_smul_Mω (omegaOnePlusOmegaEight j) vω

/-- The lowering law on `Mω`: `Fᵢ` lowers the joint eigenvalues by the Cartan row `A₋ᵢ`,
so `Hⱼ • (Fᵢ • vω) = (δ₁ⱼ + δ₈ⱼ - Aⱼᵢ) • (Fᵢ • vω)`.  This is the weight of the vector
`Fᵢ • vω`: the weight `ω₁ + ω₈ - αᵢ`. -/
theorem f_lower_eigen_omega (i j : Fin 8) :
    h j • (f i • vω) = (omegaOnePlusOmegaEight j - (CartanMatrix.E₈ j i : ℂ)) • (f i • vω) := by
  exact f_shift_eigen (M := Mω) vω omegaOnePlusOmegaEight h_eigen_omega i j

/-- The lowered weights are never the highest weight, so `Fᵢ • vω` is a vector of a strictly
lower joint spectrum than `vω` (for every `i` there is a `j` — namely `j = i` — where the
eigenvalues differ, since `Aᵢᵢ = 2`). -/
lemma f_vω_not_highest (i : Fin 8) : omegaOnePlusOmegaEight i - (CartanMatrix.E₈ i i : ℂ) ≠
    omegaOnePlusOmegaEight i := by
  -- Aᵢᵢ = 2 so the lowered eigenvalue at Hᵢ is λ(Hᵢ) − 2 ≠ λ(Hᵢ)
  have hA : (CartanMatrix.E₈ i i : ℂ) = 2 := by
    rw [(show ∀ i, CartanMatrix.E₈ i i = 2 from CartanMatrix.E₈_diag)]
    norm_num
  rw [← sub_ne_zero]
  have hdiff : omegaOnePlusOmegaEight i - (CartanMatrix.E₈ i i : ℂ) - omegaOnePlusOmegaEight i =
      -(CartanMatrix.E₈ i i : ℂ) := by
    ring
  rw [hdiff, hA]
  norm_num


/-- Word lowering on `Mω`: after applying any word `w` of `F`-generators to the highest-weight
vector, the result is a joint eigenvector of `{Hⱼ}` with eigenvalues
`(ω₁+ω₈)(Hⱼ) - ∑ᵢ₌w Aⱼᵢ`; i.e. it carries the weight `ω₁ + ω₈ - ∑ᵢ₌w αᵢ`. -/
theorem f_word_eigen_omega (w : List (Fin 8)) (j : Fin 8) :
    h j • wordAction w vω =
      (omegaOnePlusOmegaEight j - (w.map (fun i => (CartanMatrix.E₈ j i : ℂ))).sum) •
        wordAction w vω := by
  exact f_word_eigen (M := Mω) w vω omegaOnePlusOmegaEight h_eigen_omega j

end MωWeightShift

section WeightSpaces

/-- The diagonal generators act on `Mω` as commuting ℂ-linear operators (each `h j` commutes
with the ℂ-action; pairwise commutation is `commutator_HH`). -/
lemma h_smul_comm (j : Fin 8) (c : ℂ) (x : Mω) : h j • (c • x) = c • (h j • x) := by
  calc
    h j • (c • x) = h j • ((algebraMap ℂ U c) • x) := by rw [algebraMap_smul_Mω]
    _ = (h j * algebraMap ℂ U c) • x := by rw [← mul_smul]
    _ = (algebraMap ℂ U c * h j) • x := by rw [Algebra.commutes]
    _ = (algebraMap ℂ U c) • (h j • x) := by rw [mul_smul]
    _ = c • (h j • x) := by rw [algebraMap_smul_Mω]

/-- The joint weight space of weight `μ` on `Mω`: vectors on which every diagonal generator
`Hⱼ` acts by the scalar `μ(Hⱼ)`.  It is a ℂ-submodule of `Mω`. -/
def jointWeightSpace (μ : Fin 8 → ℂ) : Submodule ℂ Mω where
  carrier := {m | ∀ j, h j • m = μ j • m}
  zero_mem' := by intro j; simp
  add_mem' := by
    intro x y hx hy j
    calc
      h j • (x + y) = h j • x + h j • y := by rw [smul_add]
      _ = μ j • x + μ j • y := by rw [hx j, hy j]
      _ = μ j • (x + y) := by rw [← smul_add]
  smul_mem' := by
    intro c x hx j
    calc
      h j • (c • x) = c • (h j • x) := h_smul_comm j c x
      _ = c • (μ j • x) := by rw [hx j]
      _ = μ j • (c • x) := by rw [smul_comm]

/-- The highest-weight vector `vω` has weight `ω₁+ω₈`: it lies in the joint weight space of
`ω₁+ω₈`. -/
lemma vω_mem_weightSpace : vω ∈ jointWeightSpace omegaOnePlusOmegaEight := by
  intro j
  exact h_eigen_omega j

/-- Every word of `F`-lowering operators applied to `vω` has the weight `ω₁+ω₈ - ∑ᵢ₌w αᵢ`:
it lies in the joint weight space of `μ_w`, where `μ_w(Hⱼ) = (ω₁+ω₈)(Hⱼ) - ∑ᵢ₌w Aⱼᵢ`. -/
lemma wordAction_mem_weightSpace (w : List (Fin 8)) :
    wordAction w vω ∈ jointWeightSpace
      (fun j => omegaOnePlusOmegaEight j - (w.map (fun i => (CartanMatrix.E₈ j i : ℂ))).sum) := by
  intro j
  exact f_word_eigen_omega w j

/-- If a joint weight `μ` differs from the highest weight `ω₁+ω₈`, then no weight-`μ` vector
can be the highest-weight vector — the joint spectra are disjoint at the coordinate where the
weights differ. -/
lemma weightSpace_ne_of_ne (μ : Fin 8 → ℂ) (j : Fin 8)
    (hne : μ j ≠ omegaOnePlusOmegaEight j) :
    Disjoint (jointWeightSpace μ) (jointWeightSpace omegaOnePlusOmegaEight) := by
  rw [disjoint_iff]
  ext x
  rw [Submodule.mem_inf, Submodule.mem_bot]
  constructor
  · intro hx
    rcases hx with ⟨hxA, hxB⟩
    have hA : h j • x = μ j • x := hxA j
    have hB : h j • x = omegaOnePlusOmegaEight j • x := hxB j
    have hEq : μ j • x = omegaOnePlusOmegaEight j • x := hA.symm.trans hB
    have hsub : (μ j - omegaOnePlusOmegaEight j) • x = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr hEq
    exact (smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)
  · intro hx0
    constructor <;> intro j' <;> simp [hx0]

end WeightSpaces





end Submission.E8Weights
