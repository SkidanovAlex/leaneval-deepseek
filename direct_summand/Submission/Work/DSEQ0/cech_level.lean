import Mathlib
import Submission.Work.DSEQ0.CechImageModel
import Submission.Work.DSEQ0.comp_d_apply
import Submission.Work.DSEQ0.surjCech_vanishing

/-!
# The image-size filtration of the Čech complex

This file contains the tools for the image-size filtration argument for the Čech complex
`DSMap.cech A X f U`.

The main mathematical input is `Work.DSEQ0.surjCech_vanishing`: for a finite index type `ι` and
a module `M`, every `M`-valued cocycle on *surjective* `(n+1)`-tuples into `ι` which vanishes on
non-surjective tuples is a coboundary, provided `n ≥ card ι`.

Here we apply that statement to the graded pieces of the image-size filtration, i.e. to the
`k`-element subsets `S ⊆ ι`: the coefficient module is `coeff A X f U S = Γ(X, ⋂ i ∈ S, U i)` and
the tuples are the surjections `Fin (k+1) → ↥S`.

* `levelS_exists` is the crux for a single `k`-element subset `S`;
* `blockSol` is the chosen solution for the block `S`;
* `blockCochain` is the corresponding cochain of `DSMap.cech A X f U` in degree `k`, supported on
  the tuples whose image is `S`;
* `blockSum` is the sum of the `blockCochain`s over all `k`-element subsets;
* `comp_blockSum` computes its components: for a tuple `z` whose image is contained in a block
  `S₀` of size `k`, only the `S₀`-block contributes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

universe u

namespace Work.DSEQ0

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {ι : Type u} {f : X ⟶ Spec (.of A)}

/-! ## Tuples into `ι` and tuples into a subset -/

/-- A tuple into `ι` obtained from a function into a subset `S`. -/
def toTuple {S : Set ι} {n : ℕ} (g : Fin n → ↥S) : Fin n → ι := fun i => (g i : ι)

theorem range_toTuple_subset (S : Set ι) {n : ℕ} (g : Fin n → ↥S) :
    Set.range (toTuple g) ⊆ S := by
  rintro _ ⟨i, rfl⟩
  exact (g i).2

theorem toTuple_succAbove {S : Set ι} {n : ℕ} (g : Fin (n+1) → ↥S) (j : Fin (n+1)) :
    toTuple (g ∘ Fin.succAbove j) = toTuple g ∘ Fin.succAbove j := rfl

theorem toTuple_surjective_iff (S : Set ι) {n : ℕ} (g : Fin n → ↥S) :
    Set.range (toTuple g) = S ↔ Function.Surjective g := by
  constructor
  · intro h x
    have hx : (x : ι) ∈ Set.range (toTuple g) := by rw [h]; exact x.2
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, Subtype.ext (by simpa [toTuple] using hi)⟩
  · intro h
    ext x
    exact ⟨fun hx => range_toTuple_subset S g hx, fun hx => by
      obtain ⟨i, hi⟩ := h ⟨x, hx⟩
      exact ⟨i, by simpa [toTuple] using congrArg Subtype.val hi⟩⟩

theorem res_proof_irrel (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (S T : Set ι) (h h' : S ⊆ T) :
    res A X f U S T h = res A X f U S T h' := by
  unfold res
  congr 1

/-- The composition rule for `res`, in the form used below. -/
theorem res_comp' (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) {S T V : Set ι} (h : S ⊆ T) (h' : T ⊆ V) (h'' : S ⊆ V) :
    res A X f U S V h'' = res A X f U S T h ≫ res A X f U T V h' := by
  rw [res_comp, res_proof_irrel _ _ _ _ _ _ (h.trans h') h'']

/-- The canonical `S`-valued tuple underlying a tuple of `ι` whose range is `S`. -/
def toTupleS {m : ℕ} (z : Fin m → ι) (S : Set ι) (h : Set.range z = S) : Fin m → ↥S :=
  fun i => ⟨z i, h ▸ Set.mem_range_self i⟩

theorem toTuple_toTupleS {m : ℕ} (z : Fin m → ι) (S : Set ι) (h : Set.range z = S) :
    toTuple (toTupleS z S h) = z := rfl

theorem toTupleS_surjective {m : ℕ} (z : Fin m → ι) (S : Set ι) (h : Set.range z = S) :
    Function.Surjective (toTupleS z S h) := by
  intro s
  have hs : (s : ι) ∈ Set.range z := by rw [h]; exact s.2
  obtain ⟨i, hi⟩ := hs
  exact ⟨i, Subtype.ext hi⟩

theorem toTupleS_comp {m : ℕ} (y : Fin (m+2) → ι) (j : Fin (m+2))
    (hz : Set.range (y ∘ Fin.succAbove j) = Set.range y) :
    toTupleS (y ∘ Fin.succAbove j) (Set.range y) hz
      = toTupleS y (Set.range y) rfl ∘ Fin.succAbove j := by
  funext i
  exact Subtype.ext rfl

/-! ## The crux for a single block -/

/-- **The `k`-th step for a single `k`-element subset `S`.**  If `c` is a cocycle in degree `n`
which vanishes on tuples whose image has fewer than `k` elements, and `S` has `k` elements, then
the restriction of `c` to the block of tuples with image `S` is a coboundary (in the surjection
complex of `S`), with coefficients `coeff A X f U S`. -/
theorem levelS_exists [Finite ι] (U : ι → X.Opens) {S : Set ι} {n k : ℕ} (hS : S.ncard = k)
    (hk : k ≤ n) (c : (DSMap.cech A X f U).X n)
    (hsupp : ∀ y : Fin (n+1) → ι, (Set.range y).ncard < k → (comp A X f U n y).hom c = 0)
    (hc : ((DSMap.cech A X f U).d n (n+1)).hom c = 0) :
    ∃ bb : (Fin n → ↥S) → ↥(coeff A X f U S),
      (∀ g, ¬ Function.Surjective g → bb g = 0) ∧
      ∀ x : Fin (n+1) → ↥S,
        ∑ j : Fin (n+1), (-1 : ℤ) ^ (j : ℕ) • bb (x ∘ Fin.succAbove j) =
          (res A X f U (Set.range (toTuple x)) S (range_toTuple_subset S x)).hom
            ((comp A X f U n (toTuple x)).hom c) := by
  classical
  letI : Fintype ↥S := (Set.toFinite S).fintype
  let a : (Fin (n+1) → ↥S) → ↥(coeff A X f U S) := fun x =>
    (res A X f U (Set.range (toTuple x)) S (range_toTuple_subset S x)).hom
      ((comp A X f U n (toTuple x)).hom c)
  have ha0 : ∀ g, ¬ Function.Surjective g → a g = 0 := by
    intro g hg
    have hsub : Set.range (toTuple g) ⊂ S := by
      refine ⟨range_toTuple_subset S g, fun hle => hg ?_⟩
      exact (toTuple_surjective_iff S g).mp (Set.Subset.antisymm (range_toTuple_subset S g) hle)
    have hlt : (Set.range (toTuple g)).ncard < k := by
      rw [← hS]
      exact Set.ncard_lt_ncard hsub (Set.toFinite S)
    simp only [a]
    rw [hsupp (toTuple g) hlt, map_zero]
  have key : ∀ (x : Fin (n+2) → ↥S), Function.Surjective x →
      ∑ j : Fin (n+2), (-1 : ℤ) ^ (j : ℕ) • a (x ∘ Fin.succAbove j) = 0 := by
    intro x hx
    have hrange : Set.range (toTuple x) = S := (toTuple_surjective_iff S x).mpr hx
    have hcc : (comp A X f U (n+1) (toTuple x)).hom
        (((DSMap.cech A X f U).d n (n+1)).hom c) = 0 := by
      rw [hc, map_zero]
    rw [comp_d_apply U n c (toTuple x)] at hcc
    have hterm : ∀ j : Fin (n+2),
        a (x ∘ Fin.succAbove j)
          = (res A X f U (Set.range (toTuple x)) S hrange.le).hom
              ((res A X f U (Set.range (toTuple x ∘ Fin.succAbove j)) (Set.range (toTuple x))
                  (range_succAbove_subset (toTuple x) j)).hom
                ((comp A X f U n (toTuple x ∘ Fin.succAbove j)).hom c)) := by
      intro j
      simp only [a, toTuple_succAbove]
      rw [res_comp' A X f U (range_succAbove_subset (toTuple x) j) hrange.le
        (range_toTuple_subset S (x ∘ Fin.succAbove j))]
      rfl
    have h2 := congrArg (fun z => (res A X f U (Set.range (toTuple x)) S hrange.le).hom z) hcc
    simp only [map_zero] at h2
    have h3 : (res A X f U (Set.range (toTuple x)) S hrange.le).hom
        (∑ j : Fin (n+2), (-1 : ℤ) ^ (j : ℕ) •
          ((res A X f U (Set.range (toTuple x ∘ Fin.succAbove j)) (Set.range (toTuple x))
              (range_succAbove_subset (toTuple x) j)).hom
            ((comp A X f U n (toTuple x ∘ Fin.succAbove j)).hom c)))
        = ∑ j : Fin (n+2), (-1 : ℤ) ^ (j : ℕ) • a (x ∘ Fin.succAbove j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [map_zsmul, hterm j])
    rw [h3] at h2
    exact h2
  have ha : ∀ x : Fin (n+2) → ↥S,
      ∑ j : Fin (n+2), (-1 : ℤ) ^ (j : ℕ) • a (x ∘ Fin.succAbove j) = 0 := by
    intro x
    by_cases hx : Function.Surjective x
    · exact key x hx
    · have hzero : ∀ j : Fin (n+2), a (x ∘ Fin.succAbove j) = 0 := fun j =>
        ha0 _ (fun hconj => hx (hconj.of_comp))
      simp [hzero]
  obtain ⟨bb, hbb0, hbb⟩ := surjCech_vanishing (ι := ↥S) (M := ↥(coeff A X f U S)) n
    (by rw [Set.fintypeCard_eq_ncard, hS]; exact hk) a ha0 ha
  exact ⟨bb, hbb0, fun x => hbb x⟩

/-! ## Building cochains out of their components -/

/-- The morphism `A ⟶ M` corresponding to an element of `M`. -/
noncomputable def mkElem (A : Type u) [CommRing A] (M : ModuleCat.{u} A) (m : ↥M) :
    ModuleCat.of A A ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton A ↥M m)

theorem mkElem_apply (A : Type u) [CommRing A] (M : ModuleCat.{u} A) (m : ↥M) :
    (mkElem A M m).hom (1 : A) = m := by
  simp [mkElem, LinearMap.toSpanSingleton_apply]

/-- A cochain of the Čech complex in degree `n`, prescribed by its components, in the
"Pi model" of the product. -/
noncomputable def mkCochainPi (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (m : (z : Fin (n+1) → ι) →
      ↥((DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (z a)))))) :
    ↥(∏ᶜ (fun z : Fin (n+1) → ι =>
      (DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (z a)))))) :=
  (Pi.lift (f := fun z : Fin (n+1) → ι =>
      (DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (z a)))))
    (fun z => mkElem A _ (m z))).hom (1 : A)

/-- A cochain of the Čech complex in degree `n`, prescribed by its components. -/
noncomputable def mkCochain (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (m : (z : Fin (n+1) → ι) →
      ↥((DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (z a)))))) :
    ↥((DSMap.cech A X f U).X n) :=
  mkCochainPi A X f U n m

theorem comp_mkCochainPi (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (m : (z : Fin (n+1) → ι) →
      ↥((DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (z a))))))
    (z : Fin (n+1) → ι) :
    (Pi.π (fun z : Fin (n+1) → ι =>
        (DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (z a))))) z).hom
      (mkCochainPi A X f U n m) = m z := by
  rw [mkCochainPi, ← ModuleCat.comp_apply, Pi.lift_comp_π]
  exact mkElem_apply A _ (m z)

theorem comp_mkCochain (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (m : (z : Fin (n+1) → ι) →
      ↥((DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (z a))))))
    (z : Fin (n+1) → ι) :
    (comp A X f U n z).hom (mkCochain A X f U n m) = (termIso A X f U n z).hom (m z) :=
  congrArg (fun x => (termIso A X f U n z).hom x) (comp_mkCochainPi A X f U n m z)

/-! ## The blocks -/

section Block

variable [Fintype ι]

/-- The chosen solution of the block `S` of the `k`-th graded piece. -/
noncomputable def blockSol (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : ι → X.Opens) (k : ℕ) (c : (DSMap.cech A X f U).X (k+1))
    (hc : ((DSMap.cech A X f U).d (k+1) (k+2)).hom c = 0)
    (hsupp : ∀ y : Fin (k+2) → ι, (Set.range y).ncard < k →
      (comp A X f U (k+1) y).hom c = 0)
    (S : Set ι) (hS : S.ncard = k) : (Fin (k+1) → ↥S) → ↥(coeff A X f U S) :=
  Classical.choose (levelS_exists (U := U) (S := S) (n := k+1) (k := k) hS (Nat.le_succ k)
    c hsupp hc)

theorem blockSol_spec (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : ι → X.Opens) (k : ℕ) (c : (DSMap.cech A X f U).X (k+1))
    (hc : ((DSMap.cech A X f U).d (k+1) (k+2)).hom c = 0)
    (hsupp : ∀ y : Fin (k+2) → ι, (Set.range y).ncard < k →
      (comp A X f U (k+1) y).hom c = 0)
    (S : Set ι) (hS : S.ncard = k) :
    (∀ g, ¬ Function.Surjective g → blockSol A X f U k c hc hsupp S hS g = 0) ∧
    (∀ x : Fin (k+2) → ↥S,
      ∑ j : Fin (k+2), (-1 : ℤ) ^ (j : ℕ) •
          blockSol A X f U k c hc hsupp S hS (x ∘ Fin.succAbove j) =
        (res A X f U (Set.range (toTuple x)) S (range_toTuple_subset S x)).hom
          ((comp A X f U (k+1) (toTuple x)).hom c)) :=
  Classical.choose_spec (levelS_exists (U := U) (S := S) (n := k+1) (k := k) hS (Nat.le_succ k)
    c hsupp hc)

/-- The `S`-block of the `k`-th graded piece, as a cochain of the Čech complex in degree `k`. -/
noncomputable def blockCochain (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : ι → X.Opens) (k : ℕ) (c : (DSMap.cech A X f U).X (k+1))
    (hc : ((DSMap.cech A X f U).d (k+1) (k+2)).hom c = 0)
    (hsupp : ∀ y : Fin (k+2) → ι, (Set.range y).ncard < k →
      (comp A X f U (k+1) y).hom c = 0)
    (S : Set ι) (hS : S.ncard = k) : (DSMap.cech A X f U).X k := by
  classical
  exact mkCochain A X f U k (fun z : Fin (k+1) → ι =>
    dite (Set.range z = S)
      (fun hz => (termIso A X f U k z).inv
        (res A X f U S (Set.range z) (hz.symm ▸ Set.Subset.refl S)
          (blockSol A X f U k c hc hsupp S hS (toTupleS z S hz))))
      (fun _ => 0))

theorem comp_blockCochain (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : ι → X.Opens) (k : ℕ) (c : (DSMap.cech A X f U).X (k+1))
    (hc : ((DSMap.cech A X f U).d (k+1) (k+2)).hom c = 0)
    (hsupp : ∀ y : Fin (k+2) → ι, (Set.range y).ncard < k →
      (comp A X f U (k+1) y).hom c = 0)
    (S : Set ι) (hS : S.ncard = k) (z : Fin (k+1) → ι) :
    (comp A X f U k z).hom (blockCochain A X f U k c hc hsupp S hS)
      = dite (Set.range z = S)
          (fun hz => res A X f U S (Set.range z) (hz.symm ▸ Set.Subset.refl S)
            (blockSol A X f U k c hc hsupp S hS (toTupleS z S hz)))
          (fun _ => 0) := by
  rw [blockCochain, comp_mkCochain]
  by_cases hz : Set.range z = S
  · rw [dif_pos hz, dif_pos hz]
    exact Iso.inv_hom_id_apply _ _
  · rw [dif_neg hz, dif_neg hz, map_zero]

/-- The sum of the blocks over all `k`-element subsets of `ι`. -/
noncomputable def blockSum (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : ι → X.Opens) (k : ℕ) (c : (DSMap.cech A X f U).X (k+1))
    (hc : ((DSMap.cech A X f U).d (k+1) (k+2)).hom c = 0)
    (hsupp : ∀ y : Fin (k+2) → ι, (Set.range y).ncard < k →
      (comp A X f U (k+1) y).hom c = 0) : (DSMap.cech A X f U).X k := by
  classical
  exact ∑ S : {S : Set ι // S.ncard = k},
    blockCochain A X f U k c hc hsupp S.1 S.2

theorem comp_blockSum (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (U : ι → X.Opens) (k : ℕ) (c : (DSMap.cech A X f U).X (k+1))
    (hc : ((DSMap.cech A X f U).d (k+1) (k+2)).hom c = 0)
    (hsupp : ∀ y : Fin (k+2) → ι, (Set.range y).ncard < k →
      (comp A X f U (k+1) y).hom c = 0)
    (z : Fin (k+1) → ι) (S₀ : Set ι) (hS₀ : S₀.ncard = k) (hsub : Set.range z ⊆ S₀) :
    (comp A X f U k z).hom (blockSum A X f U k c hc hsupp)
      = (comp A X f U k z).hom (blockCochain A X f U k c hc hsupp S₀ hS₀) := by
  classical
  rw [blockSum, map_sum]
  refine Finset.sum_eq_single (⟨S₀, hS₀⟩ : {S : Set ι // S.ncard = k}) ?_ ?_
  · intro S _ hne
    have hne' : Set.range z ≠ S.1 := by
      intro hEq
      have h1 : (Set.range z).ncard = S.1.ncard := by rw [hEq]
      have h2 : S₀.ncard ≤ (Set.range z).ncard := by rw [hS₀, h1, S.2]
      have h3 : Set.range z = S₀ :=
        Set.eq_of_subset_of_ncard_le hsub h2 (Set.toFinite S₀)
      exact hne (Subtype.ext (by rw [← hEq, h3]))
    rw [comp_blockCochain, dif_neg hne']
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

end Block

end Work.DSEQ0
