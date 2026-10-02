import Mathlib
import Submission.Work.PTGeometric.SourceFamily
import Submission.Work.PTGeometric.ConcreteCollapse
import Submission.Work.PTGeometric.isEmbedding_cubeToEuc
import Submission.Work.PTGeometric.mem_range_cubeToEuc
import Submission.Work.PTGeometric.sigmaCongr_homeo_spec
import Submission.Work.PTGeometric.sigmaProd_homeo_spec
import Submission.Work.PTGeometric.collapse_corePreimage_homeo_spec
import Submission.Work.PTGeometric.genLoopListConcat_preimage_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the *specified* homeomorphism of the core preimage of the `0`-end

This file proves `Work.PTGeometric.alphaFamily_corePreimage_homeo_spec`: the homeomorphism between
the core preimage of the `0`-end `alphaFamily G m` of the null-homotopy of a family and the disjoint
union `Σ a : Fin m × ι, (Fam a.2).pt` of the pieces can be *chosen* so that it reads off the block
data of the cube point: for every `z` in the preimage there is a cube point
`u : Fin (8+k) → unitInterval` with

* `(G.emb i).e y = cubeToEuc (8+k) G.R u` (the piece point is the cube point, under the embedding),
* `blockLoop G (equivFin ι i) (u ∘ finCongr) = alphaFamily G m z` (the block loop of the selected
  piece, read at the block reparametrisation `u`, is the value of the `0`-end at `z`),

where `H z = ⟨⟨s, i⟩, y⟩`.

The proof is the specified version of the block decomposition of an iterated concatenation
(`AFS.blockSpec` below), assembled exactly as in `Work.PTGeometric.alphaFamily_corePreimage_homeo`,
with `Work.PTGeometric.collapse_corePreimage_homeo_spec` supplying the coordinate reading of the
piece.  Everything is kept in the auxiliary namespace `Work.PTGeometric.AFS`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Topology unitInterval
open Function Set

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

namespace AFS

/-! ## Elementary homeomorphisms with computable values -/

/-- The identity homeomorphism `{x : {x // p x} // q x.1} ≃ₜ {x // p x ∧ q x}`. -/
def subtypeInterHomeo {α : Type*} [TopologicalSpace α] (p q : α → Prop) :
    {x : {x // p x} // q x.1} ≃ₜ {x : α // p x ∧ q x} where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun x => ⟨x.1.2, x.2⟩)
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk (fun x => x.2.1)).subtype_mk (fun x => x.2.2)

@[simp] theorem subtypeInterHomeo_coe {α : Type*} [TopologicalSpace α] (p q : α → Prop)
    (x : {x : {x // p x} // q x.1}) :
    ((subtypeInterHomeo p q x : {x : α // p x ∧ q x}) : α) = x.1.1 := rfl

@[simp] theorem subtypeInterHomeo_symm_coe {α : Type*} [TopologicalSpace α] (p q : α → Prop)
    (x : {x : α // p x ∧ q x}) :
    (((subtypeInterHomeo p q).symm x : {x : {x // p x} // q x.1}) : α) = x.1 := rfl

/-- Commuting the conjuncts of a subtype. -/
def subtypeAndCommHomeo {α : Type*} [TopologicalSpace α] (p q : α → Prop) :
    {x : α // p x ∧ q x} ≃ₜ {x : α // q x ∧ p x} where
  toFun x := ⟨x.1, x.2.2, x.2.1⟩
  invFun x := ⟨x.1, x.2.2, x.2.1⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk (fun x => ⟨x.2.2, x.2.1⟩)
  continuous_invFun := continuous_subtype_val.subtype_mk (fun x => ⟨x.2.2, x.2.1⟩)

@[simp] theorem subtypeAndCommHomeo_coe {α : Type*} [TopologicalSpace α] (p q : α → Prop)
    (x : {x : α // p x ∧ q x}) :
    ((subtypeAndCommHomeo p q x : {x : α // q x ∧ p x}) : α) = x.1 := rfl

/-- Dropping a redundant conjunct. -/
def subtypeAndDropHomeo {α : Type*} [TopologicalSpace α] (p q : α → Prop)
    (h : ∀ x, q x → p x) : {x : {x // p x} // q x.1} ≃ₜ {x : α // q x} where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, h x.1 x.2⟩, x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    (fun x => x.2)
  continuous_invFun := (continuous_subtype_val.subtype_mk (fun x => h x.1 x.2)).subtype_mk
    (fun x => x.2)

@[simp] theorem subtypeAndDropHomeo_coe {α : Type*} [TopologicalSpace α] (p q : α → Prop)
    (h : ∀ x, q x → p x) (x : {x : {x // p x} // q x.1}) :
    ((subtypeAndDropHomeo p q h x : {x : α // q x}) : α) = x.1.1 := rfl

@[simp] theorem subtypeAndDropHomeo_symm_coe {α : Type*} [TopologicalSpace α] (p q : α → Prop)
    (h : ∀ x, q x → p x) (x : {x : α // q x}) :
    (((subtypeAndDropHomeo p q h).symm x : {x : {x // p x} // q x.1}) : α) = x.1 := rfl

/-- Changing the predicate of a subtype along a pointwise iff. -/
def subtypeCongrHomeo {α : Type*} [TopologicalSpace α] {p q : α → Prop} (h : ∀ x, p x ↔ q x) :
    {x : α // p x} ≃ₜ {x : α // q x} where
  toFun x := ⟨x.1, (h x.1).1 x.2⟩
  invFun x := ⟨x.1, (h x.1).2 x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk (fun x => (h x.1).1 x.2)
  continuous_invFun := continuous_subtype_val.subtype_mk (fun x => (h x.1).2 x.2)

@[simp] theorem subtypeCongrHomeo_coe {α : Type*} [TopologicalSpace α] {p q : α → Prop}
    (h : ∀ x, p x ↔ q x) (x : {x : α // p x}) :
    ((subtypeCongrHomeo h x : {x : α // q x}) : α) = x.1 := rfl

/-- `Homeomorph.subtype` reads off the underlying point. -/
@[simp] theorem homeomorph_subtype_coe {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {p : X → Prop} {q : Y → Prop} (h : ∀ x, p x ↔ q (e x)) (x : {x // p x}) :
    (((e.subtype h) x : {y // q y}) : Y) = e x.1 := by
  simp [Homeomorph.subtype]

/-- **The explicit clopen splitting**: a space with a clopen set is the topological sum of that set
and its complement, with the identity on the underlying points. -/
def sumComplHomeo {Y : Type*} [TopologicalSpace Y] {s : Set Y} (hs : IsClopen s) :
    Y ≃ₜ (s ⊕ (sᶜ : Set Y)) :=
  letI : DecidablePred (· ∈ s) := Classical.decPred _
  ((Equiv.Set.sumCompl s).toHomeomorphOfContinuousClosed
    (continuous_sum_dom.mpr ⟨continuous_subtype_val, continuous_subtype_val⟩)
    (by
      intro C hC
      obtain ⟨h1, h2⟩ := isClosed_sum_iff.mp hC
      have himg : (Equiv.Set.sumCompl s) '' C =
          (Subtype.val '' (Sum.inl ⁻¹' C)) ∪ (Subtype.val '' (Sum.inr ⁻¹' C)) := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          rcases z with x | x
          · exact Or.inl ⟨x, hz, Equiv.Set.sumCompl_apply_inl s x⟩
          · exact Or.inr ⟨x, hz, Equiv.Set.sumCompl_apply_inr s x⟩
        · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
          · exact ⟨Sum.inl x, hx, Equiv.Set.sumCompl_apply_inl s x⟩
          · exact ⟨Sum.inr x, hx, Equiv.Set.sumCompl_apply_inr s x⟩
      rw [himg]
      exact ((hs.1.isClosedMap_subtype_val : IsClosedMap (Subtype.val : s → Y))
        (Sum.inl ⁻¹' C) h1).union
        ((hs.2.isClosed_compl.isClosedMap_subtype_val :
            IsClosedMap (Subtype.val : (sᶜ : Set Y) → Y))
          (Sum.inr ⁻¹' C) h2))).symm

theorem sumComplHomeo_apply_of_mem {Y : Type*} [TopologicalSpace Y] {s : Set Y} (hs : IsClopen s)
    (y : Y) (hy : y ∈ s) : sumComplHomeo hs y = Sum.inl ⟨y, hy⟩ := by
  letI : DecidablePred (· ∈ s) := Classical.decPred _
  show (Equiv.Set.sumCompl s).symm y = Sum.inl ⟨y, hy⟩
  rw [Equiv.symm_apply_eq]
  exact Equiv.Set.sumCompl_apply_inl s ⟨y, hy⟩

theorem sumComplHomeo_apply_of_not_mem {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (hs : IsClopen s) (y : Y) (hy : y ∉ s) : sumComplHomeo hs y = Sum.inr ⟨y, hy⟩ := by
  letI : DecidablePred (· ∈ s) := Classical.decPred _
  show (Equiv.Set.sumCompl s).symm y = Sum.inr ⟨y, hy⟩
  rw [Equiv.symm_apply_eq]
  exact Equiv.Set.sumCompl_apply_inr s ⟨y, hy⟩

/-- The `0`-th fibre of a sigma over `Fin (n+1)` splits off, explicitly. -/
def sigmaSuccHomeo {n : ℕ} {Y : Fin (n + 1) → Type*} [∀ k, TopologicalSpace (Y k)] :
    ((Σ k : Fin n, Y k.succ) ⊕ Y 0) ≃ₜ (Σ k : Fin (n + 1), Y k) where
  toFun := Sum.elim (fun p : Σ k : Fin n, Y k.succ => ⟨p.1.succ, p.2⟩) (fun y => ⟨0, y⟩)
  invFun := fun p => Fin.cases (motive := fun j => Y j → ((Σ k : Fin n, Y k.succ) ⊕ Y 0))
    Sum.inr (fun k y => Sum.inl ⟨k, y⟩) p.1 p.2
  left_inv := by rintro (⟨k, y⟩ | y) <;> rfl
  right_inv := by
    rintro ⟨j, y⟩
    revert y
    refine Fin.cases ?_ ?_ j
    · intro y; rfl
    · intro k y; rfl
  continuous_toFun := by
    rw [continuous_sum_dom]
    refine ⟨?_, continuous_sigmaMk⟩
    apply continuous_sigma
    intro k
    exact continuous_sigmaMk
  continuous_invFun := by
    apply continuous_sigma
    intro j
    exact continuous_finCases
      (z := (Sum.inr : Y 0 → ((Σ k : Fin n, Y k.succ) ⊕ Y 0)))
      (s := fun k (y : Y k.succ) => (Sum.inl ⟨k, y⟩ : ((Σ k : Fin n, Y k.succ) ⊕ Y 0)))
      continuous_inr (fun k => continuous_inl.comp continuous_sigmaMk) j

@[simp] theorem sigmaSuccHomeo_inl {n : ℕ} {Y : Fin (n + 1) → Type*} [∀ k, TopologicalSpace (Y k)]
    (p : Σ k : Fin n, Y k.succ) :
    sigmaSuccHomeo (Sum.inl p : ((Σ k : Fin n, Y k.succ) ⊕ Y 0)) =
      (⟨p.1.succ, p.2⟩ : Σ k : Fin (n+1), Y k) := rfl

@[simp] theorem sigmaSuccHomeo_inr {n : ℕ} {Y : Fin (n + 1) → Type*} [∀ k, TopologicalSpace (Y k)]
    (y : Y 0) : sigmaSuccHomeo (Sum.inr y : ((Σ k : Fin n, Y k.succ) ⊕ Y 0)) =
      (⟨0, y⟩ : Σ k : Fin (n+1), Y k) := rfl

@[simp] theorem homeomorph_sumCongr_inl {α β γ δ : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
    (e₁ : α ≃ₜ β) (e₂ : γ ≃ₜ δ) (x : α) :
    Homeomorph.sumCongr e₁ e₂ (Sum.inl x) = Sum.inl (e₁ x) := by
  simp [Homeomorph.sumCongr, Equiv.sumCongr_apply]

@[simp] theorem homeomorph_sumCongr_inr {α β γ δ : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
    (e₁ : α ≃ₜ β) (e₂ : γ ≃ₜ δ) (x : γ) :
    Homeomorph.sumCongr e₁ e₂ (Sum.inr x) = Sum.inr (e₂ x) := by
  simp [Homeomorph.sumCongr, Equiv.sumCongr_apply]

@[simp] theorem homeomorph_setCongr_coe {α : Type*} [TopologicalSpace α] {s t : Set α}
    (h : s = t) (x : s) : (((Homeomorph.setCongr h) x : t) : α) = (x : α) := rfl

/-- **The `Fin.succ` reindexing of the blocks of a list** (the tail of a cons), preserving the
reindexed point. -/
def succReindexHomeo {N : Type*} {X : Type} [TopologicalSpace X] {x : X}
    (g : GenLoop N X x) (l' : List (GenLoop N X x)) (A : Set X) :
    (Σ k : Fin l'.length, ↥((l'.get k) ⁻¹' A)) ≃ₜ
      (Σ k : Fin l'.length, ↥(((g :: l').get k.succ) ⁻¹' A)) where
  toFun := Sigma.map id (fun k (y : ↥((l'.get k) ⁻¹' A)) =>
    (⟨(y : N → Set.Icc (0 : ℝ) 1), by rw [List.get_cons_succ']; exact y.2⟩ :
      ↥(((g :: l').get k.succ) ⁻¹' A)))
  invFun := Sigma.map id (fun k (y : ↥(((g :: l').get k.succ) ⁻¹' A)) =>
    (⟨(y : N → Set.Icc (0 : ℝ) 1), by rw [← List.get_cons_succ']; exact y.2⟩ :
      ↥((l'.get k) ⁻¹' A)))
  left_inv := by rintro ⟨k, y⟩; rfl
  right_inv := by rintro ⟨k, y⟩; rfl
  continuous_toFun := Continuous.sigma_map (f₁ := id)
    (fun k => (continuous_subtype_val).subtype_mk
      (fun y => by rw [List.get_cons_succ']; exact y.2))
  continuous_invFun := Continuous.sigma_map (f₁ := id)
    (fun k => (continuous_subtype_val).subtype_mk
      (fun y => by rw [← List.get_cons_succ']; exact y.2))

/-! ## The explicit blocks of one concatenation -/

/-- **The first block of a concatenation**, as a homeomorphism from the first half of the cube (in
the preimage of `A`) onto the first factor's preimage. -/
def leftBlockHomeo {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}
    (i : N) (F g : GenLoop N X x) (A : Set X) :
    {t : ↥((GenLoop.transAt i F g) ⁻¹' A) |
        (((t.1 : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2} ≃ₜ ↥(F ⁻¹' A) :=
  (subtypeInterHomeo (p := fun t : N → Set.Icc (0 : ℝ) 1 => GenLoop.transAt i F g t ∈ A)
      (q := fun t : N → Set.Icc (0 : ℝ) 1 => (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2)).trans <|
    (subtypeAndCommHomeo
      (p := fun t : N → Set.Icc (0 : ℝ) 1 => GenLoop.transAt i F g t ∈ A)
      (q := fun t : N → Set.Icc (0 : ℝ) 1 => (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2)).trans <|
    (subtypeInterHomeo
      (p := fun t : N → Set.Icc (0 : ℝ) 1 => (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2)
      (q := fun t : N → Set.Icc (0 : ℝ) 1 => GenLoop.transAt i F g t ∈ A)).symm.trans <|
    (halfHomeoL i).subtype
      (p := fun t : {t : N → Set.Icc (0 : ℝ) 1 |
          (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2} =>
        GenLoop.transAt i F g (t : N → Set.Icc (0 : ℝ) 1) ∈ A)
      (q := fun u : N → Set.Icc (0 : ℝ) 1 => F u ∈ A)
      (fun t => by rw [genLoop_transAt_apply_of_le i F g t.2]; rfl)

/-- **The second block of a concatenation**, as a homeomorphism from the second half of the cube (in
the preimage of `A`) onto the second factor's preimage. -/
def rightBlockHomeo {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}
    (i : N) (F g : GenLoop N X x) (A : Set X) (hx : x ∉ A) :
    {t : ↥((GenLoop.transAt i F g) ⁻¹' A) |
        ¬ (((t.1 : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2} ≃ₜ ↥(g ⁻¹' A) :=
  (subtypeInterHomeo (p := fun t : N → Set.Icc (0 : ℝ) 1 => GenLoop.transAt i F g t ∈ A)
      (q := fun t : N → Set.Icc (0 : ℝ) 1 =>
        ¬ (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2)).trans <|
    (subtypeAndCommHomeo
      (p := fun t : N → Set.Icc (0 : ℝ) 1 => GenLoop.transAt i F g t ∈ A)
      (q := fun t : N → Set.Icc (0 : ℝ) 1 =>
        ¬ (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2)).trans <|
    ((subtypeInterHomeo
      (p := fun t : N → Set.Icc (0 : ℝ) 1 => ¬ (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2)
      (q := fun t : N → Set.Icc (0 : ℝ) 1 => GenLoop.transAt i F g t ∈ A)).symm.trans <|
      ((halfHomeoR i).subtype
        (p := fun t : {t : N → Set.Icc (0 : ℝ) 1 |
            ¬ (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2} =>
          GenLoop.transAt i F g (t : N → Set.Icc (0 : ℝ) 1) ∈ A)
        (q := fun u : {u : N → Set.Icc (0 : ℝ) 1 | ((u i : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 0} =>
          g (u : N → Set.Icc (0 : ℝ) 1) ∈ A)
        (fun t => by rw [genLoop_transAt_apply_of_gt i F g t.2]; rfl))).trans
      (subtypeAndDropHomeo
        (p := fun u : N → Set.Icc (0 : ℝ) 1 => ((u i : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 0)
        (q := fun u : N → Set.Icc (0 : ℝ) 1 => g u ∈ A)
        (fun u hu h0 => by
          have hb : u ∈ Cube.boundary N := ⟨i, Or.inl (Subtype.ext h0)⟩
          rw [GenLoop.boundary g u hb] at hu
          exact hx hu))


/-! ## The values of the two blocks -/

theorem leftBlockHomeo_apply {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}
    (i : N) (F g : GenLoop N X x) (A : Set X)
    (t : ↥((GenLoop.transAt i F g) ⁻¹' A))
    (ht : (((t.1 : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2) :
    ((leftBlockHomeo i F g A ⟨t, ht⟩ : ↥(F ⁻¹' A)) : N → Set.Icc (0 : ℝ) 1) =
      halfMapL i ⟨(t : N → Set.Icc (0 : ℝ) 1), ht⟩ := by
  have hz : (subtypeInterHomeo
        (p := fun t : N → Set.Icc (0 : ℝ) 1 =>
          (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2)
        (q := fun t : N → Set.Icc (0 : ℝ) 1 => GenLoop.transAt i F g t ∈ A)).symm
      ((subtypeAndCommHomeo
          (p := fun t : N → Set.Icc (0 : ℝ) 1 => GenLoop.transAt i F g t ∈ A)
          (q := fun t : N → Set.Icc (0 : ℝ) 1 =>
            (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2))
        ((subtypeInterHomeo
            (p := fun t : N → Set.Icc (0 : ℝ) 1 => GenLoop.transAt i F g t ∈ A)
            (q := fun t : N → Set.Icc (0 : ℝ) 1 =>
              (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2)) ⟨t, ht⟩))
      = (⟨⟨(t : N → Set.Icc (0 : ℝ) 1), ht⟩, t.2⟩ :
          {x : {x : N → Set.Icc (0 : ℝ) 1 |
              (((x i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2} |
            GenLoop.transAt i F g (x : N → Set.Icc (0 : ℝ) 1) ∈ A}) := rfl
  simp only [leftBlockHomeo, Homeomorph.trans_apply, hz, homeomorph_subtype_coe]
  rfl

theorem rightBlockHomeo_apply {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}
    (i : N) (F g : GenLoop N X x) (A : Set X) (hx : x ∉ A)
    (t : ↥((GenLoop.transAt i F g) ⁻¹' A))
    (ht : ¬ (((t.1 : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2) :
    ((rightBlockHomeo i F g A hx ⟨t, ht⟩ : ↥(g ⁻¹' A)) : N → Set.Icc (0 : ℝ) 1) =
      (halfMapR i ⟨(t : N → Set.Icc (0 : ℝ) 1), ht⟩ : {u : N → Set.Icc (0 : ℝ) 1 |
        ((u i : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 0}) := by
  have hz : (subtypeInterHomeo
        (p := fun t : N → Set.Icc (0 : ℝ) 1 =>
          ¬ (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2)
        (q := fun t : N → Set.Icc (0 : ℝ) 1 => GenLoop.transAt i F g t ∈ A)).symm
      ((subtypeAndCommHomeo
          (p := fun t : N → Set.Icc (0 : ℝ) 1 => GenLoop.transAt i F g t ∈ A)
          (q := fun t : N → Set.Icc (0 : ℝ) 1 =>
            ¬ (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2))
        ((subtypeInterHomeo
            (p := fun t : N → Set.Icc (0 : ℝ) 1 => GenLoop.transAt i F g t ∈ A)
            (q := fun t : N → Set.Icc (0 : ℝ) 1 =>
              ¬ (((t i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2)) ⟨t, ht⟩))
      = (⟨⟨(t : N → Set.Icc (0 : ℝ) 1), ht⟩, t.2⟩ :
          {x : {x : N → Set.Icc (0 : ℝ) 1 |
              ¬ (((x i : Set.Icc (0 : ℝ) 1)) : ℝ) ≤ 1 / 2} |
            GenLoop.transAt i F g (x : N → Set.Icc (0 : ℝ) 1) ∈ A}) := rfl
  simp only [rightBlockHomeo, Homeomorph.trans_apply, hz, homeomorph_subtype_coe,
    subtypeAndDropHomeo_coe, halfHomeoR, halfMapR]
  rfl


/-! ## The explicit split of one concatenation -/

theorem transAt_split_spec {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}
    (i : N) (F g : GenLoop N X x) {A : Set X} (hx : x ∉ A) :
    ∃ h : ↥((GenLoop.transAt i F g) ⁻¹' A) ≃ₜ ((F ⁻¹' A) ⊕ (g ⁻¹' A)),
      (∀ (t : ↥((GenLoop.transAt i F g) ⁻¹' A))
          (ht : (((t.1 : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2),
          h t = Sum.inl (leftBlockHomeo i F g A ⟨t, ht⟩)) ∧
      (∀ (t : ↥((GenLoop.transAt i F g) ⁻¹' A))
          (ht : ¬ (((t.1 : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2),
          h t = Sum.inr (rightBlockHomeo i F g A hx ⟨t, ht⟩)) := by
  classical
  set P := (GenLoop.transAt i F g) ⁻¹' A with hP
  set s : Set P := {t | (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2} with hs
  have hne : ∀ t : P, (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≠ 1 / 2 := by
    intro t ht
    have hle : (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 := le_of_eq ht
    have hp : Set.projIcc (0 : ℝ) 1 (by norm_num) (2 * (1 / 2 : ℝ)) =
        (1 : Set.Icc (0 : ℝ) 1) := by
      rw [show 2 * (1 / 2 : ℝ) = 1 by norm_num, Set.projIcc_right]
      rfl
    have hval : GenLoop.transAt i F g (t : N → Set.Icc (0 : ℝ) 1) =
        F (Function.update (t : N → Set.Icc (0 : ℝ) 1) i 1) := by
      rw [genLoop_transAt_apply_of_le i F g hle,
        show 2 * (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) = 2 * (1 / 2)
          by rw [ht]]
      exact congrArg F (congrArg (Function.update (t : N → Set.Icc (0 : ℝ) 1) i) hp)
    have hb : Function.update (t : N → Set.Icc (0 : ℝ) 1) i (1 : Set.Icc (0 : ℝ) 1) ∈
        Cube.boundary N := ⟨i, Or.inr (Function.update_self i (1 : Set.Icc (0 : ℝ) 1)
          (t : N → Set.Icc (0 : ℝ) 1))⟩
    have hmem : GenLoop.transAt i F g (t : N → Set.Icc (0 : ℝ) 1) ∈ A := t.2
    rw [hval, GenLoop.boundary F (Function.update (t : N → Set.Icc (0 : ℝ) 1) i 1) hb] at hmem
    exact hx hmem
  have hcoord : Continuous fun t : P =>
      (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) :=
    continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)
  have hscl : IsClopen s := by
    have hsplit : s = {t : P |
        (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) < 1 / 2} := by
      ext t
      rw [hs]
      exact ⟨fun h => lt_of_le_of_ne h (hne t),
        fun h => show (((t : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 from
          le_of_lt h⟩
    refine ⟨IsClosed.preimage hcoord isClosed_Iic, ?_⟩
    rw [hsplit]
    exact IsOpen.preimage hcoord isOpen_Iio
  refine ⟨(sumComplHomeo hscl).trans
    (Homeomorph.sumCongr (leftBlockHomeo i F g A) (rightBlockHomeo i F g A hx)), ?_, ?_⟩
  · intro t ht
    rw [Homeomorph.trans_apply, sumComplHomeo_apply_of_mem hscl t ht, homeomorph_sumCongr_inl]
  · intro t ht
    rw [Homeomorph.trans_apply, sumComplHomeo_apply_of_not_mem hscl t ht, homeomorph_sumCongr_inr]
    rfl


/-! ## The specified block decomposition of an iterated concatenation -/

/-- **The value of a point of the block decomposition**: the element of `X` that the block `k`
reads at its reparametrised cube point. -/
def blockVal {N : Type*} {X : Type} [TopologicalSpace X] {x : X} (l : List (GenLoop N X x))
    (A : Set X) (z : Σ k : Fin l.length, ↥((l.get k) ⁻¹' A)) : X :=
  (l.get z.1) (z.2 : N → Set.Icc (0 : ℝ) 1)

@[simp] theorem blockVal_apply {N : Type*} {X : Type} [TopologicalSpace X] {x : X}
    (l : List (GenLoop N X x)) (A : Set X) (k : Fin l.length) (u : ↥((l.get k) ⁻¹' A)) :
    blockVal l A ⟨k, u⟩ = (l.get k) (u : N → Set.Icc (0 : ℝ) 1) := rfl

/-- The value of a `List.get` on `List.ofFn`, at a raw cube point. -/
theorem ofFn_get_apply {N : Type*} {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}
    (f : Fin n → GenLoop N X x) (k : Fin (List.ofFn f).length) (u : N → Set.Icc (0 : ℝ) 1) :
    (List.get (List.ofFn f) k) u = (f (Fin.cast List.length_ofFn k)) u :=
  congrArg (fun g : GenLoop N X x => g u) (List.get_ofFn f k)

/-- The value of a `List.get` on `List.ofFn`, with the `finCongr` form of the index. -/
theorem ofFn_get_apply_finCongr {N : Type*} {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}
    (f : Fin n → GenLoop N X x) (k : Fin (List.ofFn f).length) (u : N → Set.Icc (0 : ℝ) 1) :
    ((List.ofFn f).get k) u = (f (finCongr List.length_ofFn k)) u := by
  rw [ofFn_get_apply, ← finCongr_apply]

/-- The value of a `List.get` on a constant `List.ofFn`, at a raw cube point. -/
theorem const_ofFn_get_apply {N : Type*} {X : Type} [TopologicalSpace X] {x : X} {n : ℕ}
    (g : GenLoop N X x) (k : Fin (List.ofFn (fun _ : Fin n => g)).length)
    (u : N → Set.Icc (0 : ℝ) 1) : ((List.ofFn (fun _ : Fin n => g)).get k) u = g u := by
  rw [ofFn_get_apply]

theorem blockSpec {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}
    (i : N) (l : List (GenLoop N X x)) {A : Set X} (hA : IsClosed A) (hx : x ∉ A) :
    ∃ h : ↥((genLoopListConcat i l) ⁻¹' A) ≃ₜ (Σ k : Fin l.length, ((l.get k) ⁻¹' A)),
      ∀ t : ↥((genLoopListConcat i l) ⁻¹' A),
        (l.get (h t).1) ((h t).2 : N → Set.Icc (0 : ℝ) 1) =
          genLoopListConcat i l (t : N → Set.Icc (0 : ℝ) 1) := by
  classical
  induction l with
  | nil =>
    rw [genLoopListConcat_nil]
    haveI : IsEmpty ↥((GenLoop.const : GenLoop N X x) ⁻¹' A) :=
      ⟨fun t => hx (by
        have h2 : (GenLoop.const : GenLoop N X x) (t : N → Set.Icc (0 : ℝ) 1) ∈ A := t.2
        rwa [GenLoop.const_apply] at h2)⟩
    haveI : IsEmpty (Σ k : Fin ([] : List (GenLoop N X x)).length,
        ((([] : List (GenLoop N X x)).get k) ⁻¹' A)) := ⟨fun p => Fin.elim0 p.1⟩
    exact ⟨Homeomorph.empty, fun t => isEmptyElim t⟩
  | cons g l' ih =>
    obtain ⟨ihH, ihP⟩ := ih
    obtain ⟨h1, h1L, h1R⟩ := transAt_split_spec (X := X) (x := x) i (genLoopListConcat i l') g
      (A := A) hx
    -- the reassembly of the two blocks of the tail, with the `Fin.succ` reindexing of the blocks
    set R : ((Σ k : Fin l'.length, ((l'.get k) ⁻¹' A)) ⊕ (g ⁻¹' A)) ≃ₜ
        (Σ k : Fin (l'.length + 1), (((g :: l').get k) ⁻¹' A)) :=
      (Homeomorph.sumCongr (succReindexHomeo g l' A)
          (Homeomorph.setCongr (by rw [List.get_cons_zero]))).trans
        (sigmaSuccHomeo (Y := fun k => ↥(((g :: l').get k) ⁻¹' A))) with hR
    have Rinl : ∀ p : Σ k : Fin l'.length, ↥((l'.get k) ⁻¹' A),
        R (Sum.inl p) = (⟨(succReindexHomeo g l' A p).1.succ, (succReindexHomeo g l' A p).2⟩ :
          Σ k : Fin (l'.length + 1), ↥(((g :: l').get k) ⁻¹' A)) := by
      intro p
      rw [hR, Homeomorph.trans_apply, homeomorph_sumCongr_inl, sigmaSuccHomeo_inl]
    have Rinr : ∀ v : ↥(g ⁻¹' A),
        R (Sum.inr v) = (⟨0, (Homeomorph.setCongr (by rw [List.get_cons_zero])) v⟩ :
          Σ k : Fin (l'.length + 1), ↥(((g :: l').get k) ⁻¹' A)) := by
      intro v
      rw [hR, Homeomorph.trans_apply, homeomorph_sumCongr_inr, sigmaSuccHomeo_inr]
    -- the values of the two reassembled blocks
    have h2block : ∀ p : Σ k : Fin l'.length, ↥((l'.get k) ⁻¹' A),
        blockVal (g :: l') A
            (⟨(succReindexHomeo g l' A p).1.succ, (succReindexHomeo g l' A p).2⟩ :
              Σ k : Fin (l'.length + 1), ↥(((g :: l').get k) ⁻¹' A))
          = (l'.get p.1) (p.2 : N → Set.Icc (0 : ℝ) 1) := by
      rintro ⟨k, y⟩
      rfl
    have h2Rblock : ∀ v : ↥(g ⁻¹' A),
        blockVal (g :: l') A (⟨0, (Homeomorph.setCongr (by rw [List.get_cons_zero])) v⟩ :
            Σ k : Fin (l'.length + 1), ↥(((g :: l').get k) ⁻¹' A))
          = g (v : N → Set.Icc (0 : ℝ) 1) := by
      intro v
      rfl
    -- the reindexing of the tail's own block decomposition
    set Kc : (↥((genLoopListConcat i l') ⁻¹' A) ⊕ ↥(g ⁻¹' A)) ≃ₜ
        ((Σ k : Fin l'.length, ((l'.get k) ⁻¹' A)) ⊕ (g ⁻¹' A)) :=
      Homeomorph.sumCongr ihH (Homeomorph.refl (g ⁻¹' A)) with hKc
    have Kcinl : ∀ p : ↥((genLoopListConcat i l') ⁻¹' A),
        Kc (Sum.inl p) = Sum.inl (ihH p) := by
      intro p
      rw [hKc, homeomorph_sumCongr_inl]
    have Kcinr : ∀ v : ↥(g ⁻¹' A), Kc (Sum.inr v) = Sum.inr v := by
      intro v
      rw [hKc, homeomorph_sumCongr_inr]
      rfl
    set Hc : ↥((genLoopListConcat i (g :: l')) ⁻¹' A) ≃ₜ
        (Σ k : Fin (l'.length + 1), (((g :: l').get k) ⁻¹' A)) :=
      h1.trans (Kc.trans R) with hHc
    refine ⟨Hc, ?_⟩
    intro t
    change blockVal (g :: l') A (Hc t) =
      genLoopListConcat i (g :: l') (t : N → Set.Icc (0 : ℝ) 1)
    by_cases ht : (((t.1 : N → Set.Icc (0 : ℝ) 1) i : Set.Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2
    · set u : ↥((genLoopListConcat i l') ⁻¹' A) :=
        leftBlockHomeo i (genLoopListConcat i l') g A ⟨t, ht⟩ with hu
      have h1t : h1 t = Sum.inl u := by rw [hu]; exact h1L t ht
      have key : blockVal (g :: l') A (Hc t) = blockVal (g :: l') A (R (Sum.inl (ihH u))) := by
        congr 1
        rw [hHc]
        change (Kc.trans R) (h1 t) = R (Sum.inl (ihH u))
        rw [h1t]
        change R (Kc (Sum.inl u)) = R (Sum.inl (ihH u))
        rw [Kcinl]
      rw [key, Rinl, h2block, ihP u]
      change genLoopListConcat i l' (u : N → Set.Icc (0 : ℝ) 1) =
        GenLoop.transAt i (genLoopListConcat i l') g (t : N → Set.Icc (0 : ℝ) 1)
      rw [genLoop_transAt_apply_of_le i (genLoopListConcat i l') g ht, hu,
        leftBlockHomeo_apply i (genLoopListConcat i l') g A t ht]
      rfl
    · set v : ↥(g ⁻¹' A) := rightBlockHomeo i (genLoopListConcat i l') g A hx ⟨t, ht⟩ with hv
      have h1t : h1 t = Sum.inr v := by rw [hv]; exact h1R t ht
      have key : blockVal (g :: l') A (Hc t) = blockVal (g :: l') A (R (Sum.inr v)) := by
        congr 1
        rw [hHc]
        change (Kc.trans R) (h1 t) = R (Sum.inr v)
        rw [h1t]
        change R (Kc (Sum.inr v)) = R (Sum.inr v)
        rw [Kcinr]
      rw [key, Rinr, h2Rblock, hv]
      change g (v : N → Set.Icc (0 : ℝ) 1) =
        GenLoop.transAt i (genLoopListConcat i l') g (t : N → Set.Icc (0 : ℝ) 1)
      rw [rightBlockHomeo_apply i (genLoopListConcat i l') g A hx t ht,
        genLoop_transAt_apply_of_gt i (genLoopListConcat i l') g ht]
      rfl


end AFS

/-! ## The specified core-preimage homeomorphism -/

theorem alphaFamily_corePreimage_homeo_spec {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) :
    ∃ H : ↥{z : Fin (k + 8) → Set.Icc (0 : ℝ) 1 |
        Work.PTGeometric.alphaFamily (D := D) (Fam := Fam) G m z ∈ G.core} ≃ₜ
      (Σ a : Fin m × ι, (Fam a.2).pt),
      ∀ z, ∃ u : Fin (8 + k) → unitInterval,
        (G.emb (H z).1.2).e (H z).2 = Work.Tubular.cubeToEuc (8 + k) G.R u ∧
        (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G
            (Fintype.equivFin ι (H z).1.2))
          (fun n => u (finCongr (Nat.add_comm k 8) n))
          = Work.PTGeometric.alphaFamily (D := D) (Fam := Fam) G m z := by
  classical
  let e0 : Fin (k + 8) := ⟨0, by omega⟩
  let e1 : Fin (k + 8) := ⟨1, by omega⟩
  -- the outer block decomposition and its reindexing
  obtain ⟨hO0, hO0val⟩ := AFS.blockSpec (N := Fin (k + 8)) (X := D.T) (x := D.t₀) e0
    (List.ofFn (fun _ : Fin m => blockInner G)) (A := G.core) G.isClosed_core G.t0_notMem_core
  obtain ⟨hO1, hO1val⟩ := sigmaCongr_homeo_spec
    (ι := Fin (List.ofFn (fun _ : Fin m => blockInner G)).length) (κ := Fin m)
    (X := fun kk => ↥(((List.ofFn (fun _ : Fin m => blockInner G)).get kk) ⁻¹' G.core))
    (Y := fun _ : Fin m => ↥((blockInner G) ⁻¹' G.core))
    (finCongr List.length_ofFn) (fun kk => Homeomorph.setCongr (by rw [List.get_ofFn]))
  have hO1snd : ∀ w : (Σ kk : Fin (List.ofFn (fun _ : Fin m => blockInner G)).length,
      ↥(((List.ofFn (fun _ : Fin m => blockInner G)).get kk) ⁻¹' G.core)),
      ((hO1 w).2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) = (w.2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) := by
    intro w
    refine (congrArg (fun z : (Σ _ : Fin m, ↥((blockInner G) ⁻¹' G.core)) =>
      ((z.2 : ↥((blockInner G) ⁻¹' G.core)) : Fin (k + 8) → Set.Icc (0 : ℝ) 1))
      (hO1val w)).trans ?_
    exact AFS.homeomorph_setCongr_coe _ _
  have hOsnd : ∀ z : ↥{z : Fin (k + 8) → Set.Icc (0 : ℝ) 1 |
        Work.PTGeometric.alphaFamily (D := D) (Fam := Fam) G m z ∈ G.core},
      (((hO0.trans hO1) z).2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
        = ((hO0 z).2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) := by
    intro z
    change ((hO1 (hO0 z)).2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) = _
    exact hO1snd (hO0 z)
  -- the inner block decomposition and its reindexing
  obtain ⟨hI0, hI0val⟩ := AFS.blockSpec (N := Fin (k + 8)) (X := D.T) (x := D.t₀) e1
    (List.ofFn (blockLoop G)) (A := G.core) G.isClosed_core G.t0_notMem_core
  obtain ⟨hI1, hI1val⟩ := sigmaCongr_homeo_spec
    (ι := Fin (List.ofFn (blockLoop G)).length) (κ := Fin (Fintype.card ι))
    (X := fun j => ↥(((List.ofFn (blockLoop G)).get j) ⁻¹' G.core))
    (Y := fun j : Fin (Fintype.card ι) => ↥((blockLoop G j) ⁻¹' G.core))
    (finCongr List.length_ofFn)
    (fun j => Homeomorph.setCongr (by rw [List.get_ofFn, ← finCongr_apply]))
  have hI1fst : ∀ w : (Σ j : Fin (List.ofFn (blockLoop G)).length,
      ↥(((List.ofFn (blockLoop G)).get j) ⁻¹' G.core)),
      (hI1 w).1 = (finCongr List.length_ofFn) w.1 := by
    intro w; rw [hI1val w]
  have hI1snd : ∀ w : (Σ j : Fin (List.ofFn (blockLoop G)).length,
      ↥(((List.ofFn (blockLoop G)).get j) ⁻¹' G.core)),
      ((hI1 w).2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) = (w.2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1) := by
    intro w
    refine (congrArg (fun z : (Σ j : Fin (Fintype.card ι), ↥((blockLoop G j) ⁻¹' G.core)) =>
      ((z.2 : ↥((blockLoop G z.1) ⁻¹' G.core)) : Fin (k + 8) → Set.Icc (0 : ℝ) 1))
      (hI1val w)).trans ?_
    exact AFS.homeomorph_setCongr_coe _ _
  -- the collapse homeomorphism of each piece
  have hColval : ∀ (j : Fin (Fintype.card ι)) (s : ↥((blockLoop G j) ⁻¹' G.core)),
      (G.emb ((Fintype.equivFin ι).symm j)).e
        ((Classical.choose (collapse_corePreimage_homeo_spec G
          ((Fintype.equivFin ι).symm j))) s)
        = Work.Tubular.cubeToEuc (8 + k) G.R
            (fun jj => (s : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
              ((finCongr (Nat.add_comm k 8)).symm jj)) :=
    fun j s => Classical.choose_spec
      (collapse_corePreimage_homeo_spec G ((Fintype.equivFin ι).symm j)) s
  -- the pieces of the final homeomorphism
  obtain ⟨hG3J, hG3Jval⟩ := sigmaCongr_homeo_spec
    (ι := Fin (Fintype.card ι)) (κ := Fin (Fintype.card ι))
    (X := fun j => ↥((blockLoop G j) ⁻¹' G.core))
    (Y := fun j => (Fam ((Fintype.equivFin ι).symm j)).pt)
    (Equiv.refl (Fin (Fintype.card ι)))
    (fun j => Classical.choose (collapse_corePreimage_homeo_spec G
      ((Fintype.equivFin ι).symm j)))
  obtain ⟨hG3, hG3val⟩ := sigmaCongr_homeo_spec (ι := Fin m) (κ := Fin m)
    (X := fun _ : Fin m => (Σ j : Fin (Fintype.card ι), ↥((blockLoop G j) ⁻¹' G.core)))
    (Y := fun _ : Fin m => (Σ j : Fin (Fintype.card ι), (Fam ((Fintype.equivFin ι).symm j)).pt))
    (Equiv.refl (Fin m)) (fun _ => hG3J)
  obtain ⟨hG2, hG2val⟩ := sigmaCongr_homeo_spec (ι := Fin m) (κ := Fin m)
    (X := fun _ : Fin m => ↥((blockInner G) ⁻¹' G.core))
    (Y := fun _ : Fin m => (Σ j : Fin (Fintype.card ι), ↥((blockLoop G j) ⁻¹' G.core)))
    (Equiv.refl (Fin m)) (fun _ => hI0.trans hI1)
  obtain ⟨hIx, hIxval⟩ := sigmaCongr_homeo_spec
    (ι := Fin (Fintype.card ι)) (κ := ι)
    (X := fun j => (Fam ((Fintype.equivFin ι).symm j)).pt) (Y := fun a => (Fam a).pt)
    ((Fintype.equivFin ι).symm) (fun j => Homeomorph.refl _)
  obtain ⟨hTl, hTlval⟩ := sigmaCongr_homeo_spec (ι := Fin m) (κ := Fin m)
    (X := fun _ : Fin m => (Σ j : Fin (Fintype.card ι), (Fam ((Fintype.equivFin ι).symm j)).pt))
    (Y := fun _ : Fin m => (Σ a : ι, (Fam a).pt))
    (Equiv.refl (Fin m)) (fun _ => hIx)
  obtain ⟨hPr, hPrval⟩ := sigmaProd_homeo_spec (m := m) (ι := ι) (Z := fun a => (Fam a).pt)
  -- the final homeomorphism
  refine ⟨(hO0.trans hO1).trans (hG2.trans (hG3.trans (hTl.trans hPr))), ?_⟩
  intro z
  set v : (Σ s : Fin m, ↥((blockInner G) ⁻¹' G.core)) := (hO0.trans hO1) z with hv
  set u : (Σ j : Fin (List.ofFn (blockLoop G)).length,
      ↥(((List.ofFn (blockLoop G)).get j) ⁻¹' G.core)) := hI0 v.2 with hu
  set u' : (Σ j : Fin (Fintype.card ι), ↥((blockLoop G j) ⁻¹' G.core)) := hI1 u with hu'
  have hG2v : hG2 v = (⟨v.1, u'⟩ :
      (Σ _ : Fin m, Σ j : Fin (Fintype.card ι), ↥((blockLoop G j) ⁻¹' G.core))) := by
    simp only [hG2val, Homeomorph.trans_apply, Equiv.refl_apply, hu, hu']
    rfl
  have hG3v : hG3 (hG2 v) = (⟨v.1, ⟨u'.1,
      (Classical.choose (collapse_corePreimage_homeo_spec G
        ((Fintype.equivFin ι).symm u'.1))) u'.2⟩⟩ :
      (Σ _ : Fin m, Σ j : Fin (Fintype.card ι), (Fam ((Fintype.equivFin ι).symm j)).pt)) := by
    simp only [hG2v, hG3val, hG3Jval, Equiv.refl_apply]
    rfl
  have hTlv : hTl (hG3 (hG2 v)) = (⟨v.1, ⟨(Fintype.equivFin ι).symm u'.1,
      (Classical.choose (collapse_corePreimage_homeo_spec G
        ((Fintype.equivFin ι).symm u'.1))) u'.2⟩⟩ :
      (Σ _ : Fin m, Σ a : ι, (Fam a).pt)) := by
    simp only [hG3v, hTlval, hIxval, Homeomorph.refl_apply, Equiv.refl_apply]
    rfl
  have hPrv : hPr (hTl (hG3 (hG2 v))) = (⟨(v.1, (Fintype.equivFin ι).symm u'.1),
      (Classical.choose (collapse_corePreimage_homeo_spec G
        ((Fintype.equivFin ι).symm u'.1))) u'.2⟩ :
      (Σ a : Fin m × ι, (Fam a.2).pt)) := by
    simp only [hTlv, hPrval]
  refine ⟨fun jj => ((u'.2 : ↥((blockLoop G u'.1) ⁻¹' G.core)) : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
      ((finCongr (Nat.add_comm k 8)).symm jj), ?_, ?_⟩
  · change (G.emb ((hPr (hTl (hG3 (hG2 v)))).1.2)).e (hPr (hTl (hG3 (hG2 v)))).2
      = Work.Tubular.cubeToEuc (8 + k) G.R _
    rw [hPrv]
    exact hColval u'.1 u'.2
  · change (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G
        (Fintype.equivFin ι ((hPr (hTl (hG3 (hG2 v)))).1.2)))
        (fun n => ((u'.2 : ↥((blockLoop G u'.1) ⁻¹' G.core)) : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
          ((finCongr (Nat.add_comm k 8)).symm (finCongr (Nat.add_comm k 8) n)))
      = Work.PTGeometric.alphaFamily (D := D) (Fam := Fam) G m z
    rw [hPrv]
    have hfin : (fun n : Fin (k + 8) =>
        ((u'.2 : ↥((blockLoop G u'.1) ⁻¹' G.core)) : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
          ((finCongr (Nat.add_comm k 8)).symm (finCongr (Nat.add_comm k 8) n)))
        = ((u'.2 : ↥((blockLoop G u'.1) ⁻¹' G.core)) : Fin (k + 8) → Set.Icc (0 : ℝ) 1) := by
      funext n
      rw [Equiv.symm_apply_apply]
    rw [hfin, Equiv.apply_symm_apply]
    -- reduce the two `set`s to the explicit terms
    have hup2 : ((u'.2 : ↥((blockLoop G u'.1) ⁻¹' G.core)) : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
        = (((hI1 u).2 : ↥((blockLoop G (hI1 u).1) ⁻¹' G.core)) :
            Fin (k + 8) → Set.Icc (0 : ℝ) 1) :=
      congrArg (fun z : (Σ j : Fin (Fintype.card ι), ↥((blockLoop G j) ⁻¹' G.core)) =>
        ((z.2 : ↥((blockLoop G z.1) ⁻¹' G.core)) : Fin (k + 8) → Set.Icc (0 : ℝ) 1)) hu'
    have hupair : (blockLoop G u'.1)
          ((u'.2 : ↥((blockLoop G u'.1) ⁻¹' G.core)) : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
        = (blockLoop G (hI1 u).1)
          (((hI1 u).2 : ↥((blockLoop G (hI1 u).1) ⁻¹' G.core)) :
            Fin (k + 8) → Set.Icc (0 : ℝ) 1) :=
      congrArg (fun z : (Σ j : Fin (Fintype.card ι), ↥((blockLoop G j) ⁻¹' G.core)) =>
        (blockLoop G z.1) ((z.2 : ↥((blockLoop G z.1) ⁻¹' G.core)) :
          Fin (k + 8) → Set.Icc (0 : ℝ) 1)) hu'
    rw [hupair, hI1snd, hI1fst,
      ← AFS.ofFn_get_apply_finCongr (blockLoop G) u.1
        ((u.2 : ↥(((List.ofFn (blockLoop G)).get u.1) ⁻¹' G.core)) :
          Fin (k + 8) → Set.Icc (0 : ℝ) 1)]
    have hupair2 : (((List.ofFn (blockLoop G)).get u.1)
          ((u.2 : ↥(((List.ofFn (blockLoop G)).get u.1) ⁻¹' G.core)) :
            Fin (k + 8) → Set.Icc (0 : ℝ) 1))
        = (((List.ofFn (blockLoop G)).get (hI0 v.2).1)
          (((hI0 v.2).2 : ↥(((List.ofFn (blockLoop G)).get (hI0 v.2).1) ⁻¹' G.core)) :
            Fin (k + 8) → Set.Icc (0 : ℝ) 1)) :=
      congrArg (fun z : (Σ j : Fin (List.ofFn (blockLoop G)).length,
          ↥(((List.ofFn (blockLoop G)).get j) ⁻¹' G.core)) =>
        (((List.ofFn (blockLoop G)).get z.1)
          ((z.2 : ↥(((List.ofFn (blockLoop G)).get z.1) ⁻¹' G.core)) :
            Fin (k + 8) → Set.Icc (0 : ℝ) 1))) hu
    rw [hupair2, hI0val v.2, hv, hOsnd z]
    change (blockInner G) ((hO0 z).2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1)
      = Work.PTGeometric.alphaFamily (D := D) (Fam := Fam) G m z
    rw [← AFS.const_ofFn_get_apply (blockInner G) (hO0 z).1
      ((hO0 z).2 : Fin (k + 8) → Set.Icc (0 : ℝ) 1)]
    exact hO0val z

end

end Work.PTGeometric