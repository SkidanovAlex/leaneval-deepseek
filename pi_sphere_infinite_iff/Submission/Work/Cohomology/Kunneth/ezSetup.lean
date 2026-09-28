import Mathlib
import Submission.Work.Cohomology.AlexanderWhitney
import Submission.Work.Cohomology.Kronecker

/-!
# The `(3,3)` Eilenberg–Zilber shuffle chain, with its linear extensions

The maximal simplices of the standard triangulation of the prism `Δ³ × Δ³` are the `(3,3)`
shuffles; the Eilenberg–Zilber shuffle chain of a pair of `3`-simplices `σ` of `X` and `τ` of `Y`
is the alternating sum of the corresponding `6`-simplices of the product simplicial set, in the
realisation as the tensor product `X ⊗ Y` (which is the categorical product of simplicial sets).

The sign is `(-1)^{#{N-steps before E-steps}}`, which is the convention under which the standard
boundary formula `∂ ∘ ∇ = ∇ ∘ ∂ + (-1)^p ∇ ∘ ∂` holds (verified combinatorially).

## Main definitions

* `Shuf`, `aNum`, `bNum`, `aHom`, `bHom`, `invCount`, `shufSign` — the shuffle data;
* `ezGen X Y σ τ` — the shuffle chain of a pair of simplices `σ`, `τ`;
* `ezGenL`, `ez` — its linear (resp. bilinear) extension to chains;
* `ezChain X Y σ τ` — the shuffle chain of a pair of `3`-chains.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Cohomology.Kunneth

noncomputable section

/-- A `(3,3)`-shuffle: the set of positions of the three `N`-steps among the six steps. -/
abbrev Shuf : Type := {S : Finset (Fin 6) // S.card = 3}

/-- The number of `N`-steps before the vertex `i`. -/
def bNum (S : Finset (Fin 6)) (i : Fin 7) : ℕ := (S.filter (fun j => j.val < i.val)).card

/-- The number of `E`-steps before the vertex `i`. -/
def aNum (S : Finset (Fin 6)) (i : Fin 7) : ℕ :=
  ((Finset.univ : Finset (Fin 6)).filter (fun j => j.val < i.val) \ S).card

lemma bNum_monotone (S : Finset (Fin 6)) : Monotone (bNum S) := by
  intro i j hij
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, lt_of_lt_of_le hx.2 hij⟩

lemma aNum_monotone (S : Finset (Fin 6)) : Monotone (aNum S) := by
  intro i j hij
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact ⟨lt_of_lt_of_le hx.1 hij, hx.2⟩

lemma bNum_le (S : Finset (Fin 6)) (i : Fin 7) : bNum S i ≤ S.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma aNum_le (S : Finset (Fin 6)) (i : Fin 7) : aNum S i ≤ 6 - S.card := by
  rw [aNum]
  have hsub : ((Finset.univ : Finset (Fin 6)).filter (fun j => j.val < i.val) \ S)
      ⊆ (Finset.univ : Finset (Fin 6)) \ S := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.2
  calc _ ≤ ((Finset.univ : Finset (Fin 6)) \ S).card := Finset.card_le_card hsub
    _ = 6 - S.card := by rw [Finset.card_sdiff, Finset.inter_univ]; simp

/-- The `E`-coordinate as a morphism `⦋6⦌ ⟶ ⦋3⦌`. -/
def aHom (S : Finset (Fin 6)) (hS : S.card = 3) : ⦋6⦌ ⟶ ⦋3⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨aNum S i, by
        have h := aNum_le S i
        have h3 : ⦋3⦌.len = 3 := rfl
        omega⟩
      monotone' := fun _ _ hij => by
        simp only [Fin.le_def]
        exact aNum_monotone S hij }

/-- The `N`-coordinate as a morphism `⦋6⦌ ⟶ ⦋3⦌`. -/
def bHom (S : Finset (Fin 6)) (hS : S.card = 3) : ⦋6⦌ ⟶ ⦋3⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨bNum S i, by
        have h := bNum_le S i
        have h3 : ⦋3⦌.len = 3 := rfl
        omega⟩
      monotone' := fun _ _ hij => by
        simp only [Fin.le_def]
        exact bNum_monotone S hij }

@[simp] lemma aHom_val (S : Finset (Fin 6)) (hS : S.card = 3) (i : Fin 7) :
    ((aHom S hS : ⦋6⦌ ⟶ ⦋3⦌) i).val = aNum S i := rfl

@[simp] lemma bHom_val (S : Finset (Fin 6)) (hS : S.card = 3) (i : Fin 7) :
    ((bHom S hS : ⦋6⦌ ⟶ ⦋3⦌) i).val = bNum S i := rfl

/-- The number of inversions of a shuffle: the pairs (an `N`-step before an `E`-step). -/
def invCount (S : Finset (Fin 6)) : ℕ :=
  ((Finset.univ : Finset (Fin 6)) \ S).sum (fun j => bNum S ⟨j.val, by omega⟩)

/-- The Eilenberg–Zilber sign of a shuffle. -/
def shufSign (S : Finset (Fin 6)) : ℤ := (-1 : ℤ) ^ invCount S

/-- The cell of the `(3,3)` Eilenberg–Zilber shuffle chain attached to a pair of `3`-simplices and
a shuffle: the product simplex `(σ ∘ a_S, τ ∘ b_S)`, ascribed at `(X ⊗ Y) _⦋6⦌` (so that later
statements and proofs speak about the *same* term, the product simplex being typed at the tensor
product and not at `X _⦋6⦌ × Y _⦋6⦌`). -/
def ezCell (X Y : SSet) (σ : X _⦋3⦌) (τ : Y _⦋3⦌) (S : Shuf) : (X ⊗ Y) _⦋6⦌ :=
  (X.map (aHom S.1 S.2).op σ, Y.map (bHom S.1 S.2).op τ)

/-- The `(3,3)` Eilenberg–Zilber shuffle chain of a pair of `3`-simplices: the sum over the
twenty shuffles `S` of `shufSign S • (σ ∘ a_S, τ ∘ b_S)`. -/
def ezGen (X Y : SSet) (σ : X _⦋3⦌) (τ : Y _⦋3⦌) :
    ((X ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X 6 :=
  ∑ z : Shuf, shufSign z.1 •
    ((X ⊗ Y).ιChainComplex (R := ModuleCat.of ℤ ℤ) (ezCell X Y σ τ z)).hom 1

/-- The shuffle chain of a simplex `σ` of `X` and a `3`-simplex `τ` of `Y`, as a linear map in
`τ`. -/
def ezGenR (X Y : SSet) (σ : X _⦋3⦌) :
    (Y.chainComplex (ModuleCat.of ℤ ℤ)).X 3 ⟶
      ModuleCat.of ℤ (((X ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X 6) :=
  (Y.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) 3).desc
    (Cofan.mk (ModuleCat.of ℤ (((X ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X 6))
      (fun τ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (ezGen X Y σ τ))))

/-- The shuffle chain as a bilinear map on the `3`-chains of `X` and `Y`. -/
def ez (X Y : SSet) :
    (X.chainComplex (ModuleCat.of ℤ ℤ)).X 3 ⟶
      ModuleCat.of ℤ ((Y.chainComplex (ModuleCat.of ℤ ℤ)).X 3 →ₗ[ℤ]
        ((X ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X 6) :=
  (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) 3).desc
    (Cofan.mk (ModuleCat.of ℤ ((Y.chainComplex (ModuleCat.of ℤ ℤ)).X 3 →ₗ[ℤ]
        ((X ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X 6))
      (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (ezGenR X Y σ).hom)))

/-- The Eilenberg–Zilber shuffle chain of a pair of `3`-chains. -/
def ezChain (X Y : SSet) (σ : (X.chainComplex (ModuleCat.of ℤ ℤ)).X 3)
    (τ : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X 3) :
    ((X ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X 6 :=
  (ez X Y).hom σ τ

/-- The defining property of `ezGenR` on a generator. -/
lemma ιChainComplex_ezGenR (X Y : SSet) (σ : X _⦋3⦌) (τ : Y _⦋3⦌) :
    Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) τ ≫ ezGenR X Y σ
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (ezGen X Y σ τ)) :=
  Cofan.IsColimit.fac _ _ _

/-- The value of `ezGenR` on a generator (a `3`-simplex). -/
lemma ezGenR_apply (X Y : SSet) (σ : X _⦋3⦌) (τ : Y _⦋3⦌) :
    (ezGenR X Y σ).hom ((Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom (1 : ℤ))
      = ezGen X Y σ τ := by
  have h := congrArg
    (fun (g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ (((X ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X 6))
      => g.hom (1 : ℤ)) (ιChainComplex_ezGenR X Y σ τ)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h

/-- The defining property of `ez` on a generator. -/
lemma ιChainComplex_ez (X Y : SSet) (σ : X _⦋3⦌) :
    X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ ez X Y
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (ezGenR X Y σ).hom) :=
  Cofan.IsColimit.fac _ _ _

/-- The shuffle chain evaluated on a generator of the first variable. -/
lemma ezChain_apply (X Y : SSet) (σ : X _⦋3⦌)
    (τ : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X 3) :
    ezChain X Y ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1) τ
      = (ezGenR X Y σ).hom τ := by
  have h := congrArg
    (fun (g : ModuleCat.of ℤ ℤ ⟶
        ModuleCat.of ℤ ((Y.chainComplex (ModuleCat.of ℤ ℤ)).X 3 →ₗ[ℤ]
          ((X ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X 6)) => g.hom (1 : ℤ))
    (ιChainComplex_ez X Y σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] at h
  rw [ezChain, h]

/-- The shuffle chain evaluated on a pair of generators. -/
lemma ezChain_gen (X Y : SSet) (σ : X _⦋3⦌) (τ : Y _⦋3⦌) :
    ezChain X Y ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)
      ((Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) τ).hom 1) = ezGen X Y σ τ := by
  rw [ezChain_apply, ezGenR_apply]

/-- The shuffle chain is additive in the first variable. -/
lemma ezChain_add_left (X Y : SSet) (u u' : (X.chainComplex (ModuleCat.of ℤ ℤ)).X 3)
    (τ : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X 3) :
    ezChain X Y (u + u') τ = ezChain X Y u τ + ezChain X Y u' τ := by
  show ((ez X Y).hom (u + u')) τ = ((ez X Y).hom u) τ + ((ez X Y).hom u') τ
  rw [map_add]
  rfl

/-- The shuffle chain is additive in the second variable. -/
lemma ezChain_add_right (X Y : SSet) (σ : (X.chainComplex (ModuleCat.of ℤ ℤ)).X 3)
    (v v' : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X 3) :
    ezChain X Y σ (v + v') = ezChain X Y σ v + ezChain X Y σ v' := by
  show ((ez X Y).hom σ) (v + v') = ((ez X Y).hom σ) v + ((ez X Y).hom σ) v'
  exact map_add ((ez X Y).hom σ) v v'

end

end Work.Cohomology.Kunneth
