import Mathlib
import Submission.Work.DSEQ0.cech_level

/-!
# The image-size filtration: raising the level and vanishing of the homology

Building on `Submission/Work/DSEQ0/cech_level.lean`, this file contains the actual
image-size filtration argument for the Čech complex `DSMap.cech A X f U`.

For a finite index type `ι` and a degree `m = K+1`:

* `gSol` is the crux `levelS_exists` applied to a `j`-element subset `S ⊆ ι`;
* `gCochain`/`gSum` assemble the block solutions into cochains in degree `K`;
* `level_raise` computes the differential of `gSum` on the tuples whose image has at most
  `j` elements;
* `cocycle_is_coboundary` runs the descending induction on the level and shows that every
  cocycle in degree `K+1 ≥ Nat.card ι` is a coboundary;
* `cech_homology_isZero_succ` concludes that `H^{K+1}` vanishes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

universe u

namespace Work.DSEQ0

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {ι : Type u} {f : X ⟶ Spec (.of A)}

/-! ## Extensionality -/

/-- Two elements of a product in `ModuleCat A` are equal as soon as all their components
are. -/
theorem pi_ext {β : Type u} {F : β → ModuleCat.{u} A} {x y : ↥(∏ᶜ F)}
    (h : ∀ b, (Pi.π F b).hom x = (Pi.π F b).hom y) : x = y := by
  have h1 : (ConcreteCategory.hom (ModuleCat.piIsoPi F).hom) x
      = (ConcreteCategory.hom (ModuleCat.piIsoPi F).hom) y := by
    funext b
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply, ModuleCat.piIsoPi_hom_ker_subtype_apply]
    exact h b
  have h2 := congrArg (ConcreteCategory.hom (ModuleCat.piIsoPi F).inv) h1
  rwa [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply,
      ← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply] at h2

/-- Two cochains of the Čech complex are equal as soon as all their components are. -/
theorem cech_ext (U : ι → X.Opens) {m : ℕ} {x y : ↥((DSMap.cech A X f U).X m)}
    (h : ∀ z : Fin (m+1) → ι, (comp A X f U m z).hom x = (comp A X f U m z).hom y) :
    x = y := by
  refine pi_ext (β := Fin (m+1) → ι)
    (F := fun z : Fin (m+1) → ι =>
      (DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (z a))))) (fun z => ?_)
  have h1 : (termIso A X f U m z).hom ((Pi.π (fun z : Fin (m+1) → ι =>
        (DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (z a))))) z).hom x)
      = (termIso A X f U m z).hom ((Pi.π (fun z : Fin (m+1) → ι =>
        (DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (z a))))) z).hom y) := by
    have hz := h z
    rwa [show (comp A X f U m z).hom x
          = (termIso A X f U m z).hom ((Pi.π (fun z : Fin (m+1) → ι =>
              (DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (z a))))) z).hom x) from rfl,
        show (comp A X f U m z).hom y
          = (termIso A X f U m z).hom ((Pi.π (fun z : Fin (m+1) → ι =>
              (DSMap.cechPresheaf A X f).obj (op (∏ᶜ (fun a => U (z a))))) z).hom y) from rfl] at hz
  have h2 := congrArg (fun w => (termIso A X f U m z).inv w) h1
  rwa [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply] at h2

/-! ## The blocks in a general degree -/

section General

variable [Fintype ι]

/-- The chosen solution of the block `S` of the `j`-th graded piece, in degree `m`. -/
noncomputable def gSol (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} [Fintype ι] (U : ι → X.Opens) (m j : ℕ) (hj : j ≤ m)
    (c : (DSMap.cech A X f U).X m)
    (hc : ((DSMap.cech A X f U).d m (m+1)).hom c = 0)
    (hsupp : ∀ y : Fin (m+1) → ι, (Set.range y).ncard < j → (comp A X f U m y).hom c = 0)
    (S : Set ι) (hS : S.ncard = j) : (Fin m → ↥S) → ↥(coeff A X f U S) :=
  Classical.choose (levelS_exists (U := U) (S := S) (n := m) (k := j) hS hj c hsupp hc)

theorem gSol_spec (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} [Fintype ι] (U : ι → X.Opens) (m j : ℕ) (hj : j ≤ m)
    (c : (DSMap.cech A X f U).X m)
    (hc : ((DSMap.cech A X f U).d m (m+1)).hom c = 0)
    (hsupp : ∀ y : Fin (m+1) → ι, (Set.range y).ncard < j → (comp A X f U m y).hom c = 0)
    (S : Set ι) (hS : S.ncard = j) :
    (∀ g, ¬ Function.Surjective g → gSol A X f U m j hj c hc hsupp S hS g = 0) ∧
    (∀ x : Fin (m+1) → ↥S,
      ∑ k : Fin (m+1), (-1 : ℤ) ^ (k : ℕ) •
          gSol A X f U m j hj c hc hsupp S hS (x ∘ Fin.succAbove k) =
        (res A X f U (Set.range (toTuple x)) S (range_toTuple_subset S x)).hom
          ((comp A X f U m (toTuple x)).hom c)) :=
  Classical.choose_spec (levelS_exists (U := U) (S := S) (n := m) (k := j) hS hj c hsupp hc)

/-- The `S`-block of the `j`-th graded piece, as a cochain of the Čech complex in degree `K`
(where the ambient degree of the cocycle is `K+1`). -/
noncomputable def gCochain (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} [Fintype ι] (U : ι → X.Opens) (K j : ℕ) (hj : j ≤ K+1)
    (c : (DSMap.cech A X f U).X (K+1))
    (hc : ((DSMap.cech A X f U).d (K+1) (K+2)).hom c = 0)
    (hsupp : ∀ y : Fin (K+2) → ι, (Set.range y).ncard < j →
      (comp A X f U (K+1) y).hom c = 0)
    (S : Set ι) (hS : S.ncard = j) : (DSMap.cech A X f U).X K := by
  classical
  exact mkCochain A X f U K (fun z : Fin (K+1) → ι =>
    dite (Set.range z = S)
      (fun hz => (termIso A X f U K z).inv
        (res A X f U S (Set.range z) (hz.symm ▸ Set.Subset.refl S)
          (gSol A X f U (K+1) j hj c hc hsupp S hS (toTupleS z S hz))))
      (fun _ => 0))

theorem comp_gCochain (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} [Fintype ι] (U : ι → X.Opens) (K j : ℕ) (hj : j ≤ K+1)
    (c : (DSMap.cech A X f U).X (K+1))
    (hc : ((DSMap.cech A X f U).d (K+1) (K+2)).hom c = 0)
    (hsupp : ∀ y : Fin (K+2) → ι, (Set.range y).ncard < j →
      (comp A X f U (K+1) y).hom c = 0)
    (S : Set ι) (hS : S.ncard = j) (z : Fin (K+1) → ι) :
    (comp A X f U K z).hom (gCochain A X f U K j hj c hc hsupp S hS)
      = dite (Set.range z = S)
          (fun hz => res A X f U S (Set.range z) (hz.symm ▸ Set.Subset.refl S)
            (gSol A X f U (K+1) j hj c hc hsupp S hS (toTupleS z S hz)))
          (fun _ => 0) := by
  rw [gCochain, comp_mkCochain]
  by_cases hz : Set.range z = S
  · rw [dif_pos hz, dif_pos hz]
    exact Iso.inv_hom_id_apply _ _
  · rw [dif_neg hz, dif_neg hz, map_zero]

/-- The sum of the blocks over all `j`-element subsets of `ι`. -/
noncomputable def gSum (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} [Fintype ι] (U : ι → X.Opens) (K j : ℕ) (hj : j ≤ K+1)
    (c : (DSMap.cech A X f U).X (K+1))
    (hc : ((DSMap.cech A X f U).d (K+1) (K+2)).hom c = 0)
    (hsupp : ∀ y : Fin (K+2) → ι, (Set.range y).ncard < j →
      (comp A X f U (K+1) y).hom c = 0) : (DSMap.cech A X f U).X K := by
  classical
  exact ∑ S : {S : Set ι // S.ncard = j},
    gCochain A X f U K j hj c hc hsupp S.1 S.2

theorem comp_gSum (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} [Fintype ι] (U : ι → X.Opens) (K j : ℕ) (hj : j ≤ K+1)
    (c : (DSMap.cech A X f U).X (K+1))
    (hc : ((DSMap.cech A X f U).d (K+1) (K+2)).hom c = 0)
    (hsupp : ∀ y : Fin (K+2) → ι, (Set.range y).ncard < j →
      (comp A X f U (K+1) y).hom c = 0)
    (z : Fin (K+1) → ι) (S₀ : Set ι) (hS₀ : S₀.ncard = j) (hsub : Set.range z ⊆ S₀) :
    (comp A X f U K z).hom (gSum A X f U K j hj c hc hsupp)
      = (comp A X f U K z).hom (gCochain A X f U K j hj c hc hsupp S₀ hS₀) := by
  classical
  rw [gSum, map_sum]
  refine Finset.sum_eq_single (⟨S₀, hS₀⟩ : {S : Set ι // S.ncard = j}) ?_ ?_
  · intro S _ hne
    have hne' : Set.range z ≠ S.1 := by
      intro hEq
      have h1 : (Set.range z).ncard = S.1.ncard := by rw [hEq]
      have h2 : S₀.ncard ≤ (Set.range z).ncard := by rw [hS₀, h1, S.2]
      have h3 : Set.range z = S₀ :=
        Set.eq_of_subset_of_ncard_le hsub h2 (Set.toFinite S₀)
      exact hne (Subtype.ext (by rw [← hEq, h3]))
    rw [comp_gCochain, dif_neg hne']
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

theorem comp_gSum_of_lt (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} [Fintype ι] (U : ι → X.Opens) (K j : ℕ) (hj : j ≤ K+1)
    (c : (DSMap.cech A X f U).X (K+1))
    (hc : ((DSMap.cech A X f U).d (K+1) (K+2)).hom c = 0)
    (hsupp : ∀ y : Fin (K+2) → ι, (Set.range y).ncard < j →
      (comp A X f U (K+1) y).hom c = 0)
    (z : Fin (K+1) → ι) (hz : (Set.range z).ncard < j) :
    (comp A X f U K z).hom (gSum A X f U K j hj c hc hsupp) = 0 := by
  classical
  rw [gSum, map_sum]
  refine Finset.sum_eq_zero (fun S _ => ?_)
  have hne : Set.range z ≠ S.1 := by
    intro hEq
    have h1 : (Set.range z).ncard = S.1.ncard := by rw [hEq]
    omega
  rw [comp_gCochain, dif_neg hne]

end General

/-! ## The level-raising step -/

section Raise

variable [Fintype ι]

/-- **The level-raising step.**  If `c` is a cocycle in degree `K+1` which vanishes on tuples
whose image has fewer than `j` elements, then the cochain `gSum` has the property that its
coboundary agrees with `c` on all tuples whose image has at most `j` elements. -/
theorem level_raise (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} [Fintype ι] (U : ι → X.Opens) (K j : ℕ) (hj : j ≤ K+1)
    (c : (DSMap.cech A X f U).X (K+1))
    (hc : ((DSMap.cech A X f U).d (K+1) (K+2)).hom c = 0)
    (hsupp : ∀ y : Fin (K+2) → ι, (Set.range y).ncard < j →
      (comp A X f U (K+1) y).hom c = 0) :
    ∀ y : Fin (K+2) → ι, (Set.range y).ncard ≤ j →
      (comp A X f U (K+1) y).hom
          (((DSMap.cech A X f U).d K (K+1)).hom (gSum A X f U K j hj c hc hsupp))
        = (comp A X f U (K+1) y).hom c := by
  intro y hy
  by_cases hlt : (Set.range y).ncard < j
  · rw [hsupp y hlt,
      comp_d_apply U K (gSum A X f U K j hj c hc hsupp) y]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [comp_gSum_of_lt A X f U K j hj c hc hsupp (y ∘ Fin.succAbove k)
      (lt_of_le_of_lt (Set.ncard_le_ncard (range_succAbove_subset y k) (Set.toFinite _)) hlt)]
    simp
  · have hNj : (Set.range y).ncard = j := by omega
    rw [comp_d_apply U K (gSum A X f U K j hj c hc hsupp) y]
    have hterm : ∀ k : Fin (K+2),
        (res A X f U (Set.range (y ∘ Fin.succAbove k)) (Set.range y)
            (range_succAbove_subset y k)).hom
          ((comp A X f U K (y ∘ Fin.succAbove k)).hom (gSum A X f U K j hj c hc hsupp))
        = gSol A X f U (K+1) j hj c hc hsupp (Set.range y) hNj
            (toTupleS y (Set.range y) rfl ∘ Fin.succAbove k) := by
      intro k
      rw [comp_gSum A X f U K j hj c hc hsupp (y ∘ Fin.succAbove k) (Set.range y) hNj
        (range_succAbove_subset y k)]
      rw [comp_gCochain]
      by_cases hz : Set.range (y ∘ Fin.succAbove k) = Set.range y
      · rw [dif_pos hz]
        rw [← ModuleCat.comp_apply, res_comp, res_self]
        simp only [ConcreteCategory.id_apply]
        rw [toTupleS_comp y k hz]
      · rw [dif_neg hz, map_zero]
        have hsurj : ¬ Function.Surjective
            (toTupleS y (Set.range y) rfl ∘ Fin.succAbove k) := by
          intro hs
          apply hz
          refine Set.Subset.antisymm (range_succAbove_subset y k) ?_
          intro s hs'
          obtain ⟨i, hi⟩ := hs ⟨s, hs'⟩
          exact ⟨i, congrArg Subtype.val hi⟩
        rw [(gSol_spec A X f U (K+1) j hj c hc hsupp (Set.range y) hNj).1 _ hsurj]
    rw [Finset.sum_congr rfl (fun k _ => by rw [hterm k])]
    have hsum := (gSol_spec A X f U (K+1) j hj c hc hsupp (Set.range y) hNj).2
      (toTupleS y (Set.range y) rfl)
    simpa only [toTuple_toTupleS, res_self, ConcreteCategory.id_apply] using hsum

end Raise

/-! ## Every cocycle in high degree is a coboundary -/

section Coboundary

variable [Fintype ι]

theorem cech_word (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} [Fintype ι] (U : ι → X.Opens) : True := trivial

theorem cocycle_is_coboundary (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} [Fintype ι] (U : ι → X.Opens) (K : ℕ) (hm : Nat.card ι ≤ K+1)
    (c : (DSMap.cech A X f U).X (K+1))
    (hc : ((DSMap.cech A X f U).d (K+1) (K+2)).hom c = 0) :
    ∃ b : (DSMap.cech A X f U).X K, ((DSMap.cech A X f U).d K (K+1)).hom b = c := by
  classical
  -- the level-`j` statement, universally quantified over the cocycle
  let P : ℕ → Prop := fun j => ∀ (c : (DSMap.cech A X f U).X (K+1)),
      ((DSMap.cech A X f U).d (K+1) (K+2)).hom c = 0 →
      (∀ y : Fin (K+2) → ι, (Set.range y).ncard < j → (comp A X f U (K+1) y).hom c = 0) →
      ∃ b : (DSMap.cech A X f U).X K, ((DSMap.cech A X f U).d K (K+1)).hom b = c
  have hbase : P (Nat.card ι) := by
    intro c' hc' hsupp'
    have hlr := level_raise A X f U K (Nat.card ι) hm c' hc' hsupp'
    refine ⟨gSum A X f U K (Nat.card ι) hm c' hc' hsupp', ?_⟩
    refine cech_ext (U := U) (fun y => ?_)
    refine hlr y ?_
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  have hstep : ∀ j, j ≤ K+1 → P (j+1) → P j := by
    intro j hj hnext c' hc' hsupp'
    have hlr := level_raise A X f U K j hj c' hc' hsupp'
    -- the new cocycle
    have hc'' : ((DSMap.cech A X f U).d (K+1) (K+2)).hom
        (c' - ((DSMap.cech A X f U).d K (K+1)).hom (gSum A X f U K j hj c' hc' hsupp')) = 0 := by
      rw [map_sub, hc', zero_sub, ← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
      simp
    have hsupp'' : ∀ y : Fin (K+2) → ι, (Set.range y).ncard < j+1 →
        (comp A X f U (K+1) y).hom
          (c' - ((DSMap.cech A X f U).d K (K+1)).hom (gSum A X f U K j hj c' hc' hsupp')) = 0 := by
      intro y hy
      rw [map_sub, hlr y (by omega), sub_self]
    obtain ⟨b₂, hb₂⟩ := hnext _ hc'' hsupp''
    refine ⟨gSum A X f U K j hj c' hc' hsupp' + b₂, ?_⟩
    rw [map_add, hb₂]
    abel
  have hkey : P 0 := by
    have hchain : ∀ d : ℕ, ∀ j : ℕ, j + d = Nat.card ι → P j := by
      intro d
      induction d with
      | zero =>
        intro j hj
        rw [show j = Nat.card ι from by omega]
        exact hbase
      | succ d ih =>
        intro j hj
        exact hstep j (by omega) (ih (j+1) (by omega))
    exact hchain (Nat.card ι) 0 (by omega)
  exact hkey c hc (fun y hy => absurd hy (by omega))

theorem cech_homology_isZero_succ (A : Type u) [CommRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) {ι : Type u} [Fintype ι] (U : ι → X.Opens)
    (K : ℕ) (hm : Nat.card ι ≤ K+1) :
    IsZero ((DSMap.cech A X f U).homology (K+1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' (DSMap.cech A X f U) K (K+1) (K+2) (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro x₂ hx₂
  obtain ⟨b, hb⟩ := cocycle_is_coboundary A X f U K hm x₂ hx₂
  exact ⟨b, hb⟩

end Coboundary

end Work.DSEQ0
