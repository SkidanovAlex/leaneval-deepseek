import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.CompletePartialOrder

open Module Submodule
open scoped BigOperators

noncomputable section

namespace Commons.Lattice.Module

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

namespace BasisExtensionPure

/-! Helpers: Fin block combinatorics, module-level basis-extension master lemma,
and ambient purity lemmas for the concrete lattice types. -/

/-- shift : Fin (o - n0) ↪ Fin o adding n0 -/
def shiftFin {n0 o : ℕ} (hno : n0 ≤ o) : Fin (o - n0) → Fin o :=
  fun k => ⟨n0 + k.val, by omega⟩

lemma shiftFin_injective {n0 o : ℕ} (hno : n0 ≤ o) : Function.Injective (shiftFin hno) := by
  intro a b h
  apply Fin.ext
  have hv : (n0 + a.val) = n0 + b.val := congrArg Fin.val h
  omega

def blockEquivFun {n0 o : ℕ} (hno : n0 ≤ o) : (Fin n0 ⊕ Fin (o - n0)) → Fin o :=
  Sum.elim (Fin.castLE hno) (shiftFin hno)

def blockEquivInv {n0 o : ℕ} (hno : n0 ≤ o) : Fin o → (Fin n0 ⊕ Fin (o - n0)) :=
  fun j => if hj : j.val < n0 then Sum.inl ⟨j.val, hj⟩ else Sum.inr ⟨j.val - n0, by omega⟩

lemma blockEquiv_left {n0 o : ℕ} (hno : n0 ≤ o) (t : Fin n0 ⊕ Fin (o - n0)) :
    blockEquivInv hno (blockEquivFun hno t) = t := by
  cases t with
  | inl i =>
    dsimp [blockEquivFun, blockEquivInv]
    simp
  | inr k =>
    dsimp [blockEquivFun, blockEquivInv, shiftFin]
    have hk : ¬ (n0 + k.val < n0) := by omega
    simp [hk]

lemma blockEquiv_right {n0 o : ℕ} (hno : n0 ≤ o) (j : Fin o) :
    blockEquivFun hno (blockEquivInv hno j) = j := by
  dsimp [blockEquivFun, blockEquivInv]
  by_cases hj : j.val < n0
  · simp [hj]
  · have hcast : (shiftFin hno ⟨j.val - n0, by omega⟩ : Fin o) = j := by
      apply Fin.ext
      simp [shiftFin]
      omega
    simp [hj, hcast]

def blockEquiv {n0 o : ℕ} (hno : n0 ≤ o) : (Fin n0 ⊕ Fin (o - n0)) ≃ Fin o where
  toFun := blockEquivFun hno
  invFun := blockEquivInv hno
  left_inv := blockEquiv_left hno
  right_inv := blockEquiv_right hno

lemma isCompl_range_castLE_range_shiftFin {o n0 : ℕ} (hno : n0 ≤ o) :
    IsCompl (Set.range (fun i : Fin n0 => Fin.castLE hno i)) (Set.range (shiftFin hno)) := by
  constructor
  · rw [Set.disjoint_left]
    intro j hjs hjt
    rcases hjs with ⟨i, hi⟩
    rcases hjt with ⟨k, hk⟩
    have hv1 : i.val = j.val := congrArg Fin.val hi
    have hv2 : n0 + k.val = j.val := congrArg Fin.val hk
    omega
  · rw [codisjoint_iff]
    ext j
    constructor
    · intro h; trivial
    · intro h
      by_cases hlt : j.val < n0
      · left
        refine ⟨⟨j.val, hlt⟩, ?_⟩
        apply Fin.ext
        rfl
      · right
        refine ⟨⟨j.val - n0, by omega⟩, ?_⟩
        apply Fin.ext
        simp [shiftFin]
        omega

/-- Master lemma: given an injective linear map `i : N →ₗ M` whose range is the span of an initial
block of the basis `bM` of `M`, and any basis `bN0` of `N`, extend `i ∘ bN0` to a basis of `M`. -/
lemma exists_basis_extend_of_range_block {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N]
    {o n0 : ℕ} (hno : n0 ≤ o)
    (i : N →ₗ[ℤ] M) (hi : i.ker = ⊥) (bM : Basis (Fin o) ℤ M) (bN0 : Basis (Fin n0) ℤ N)
    (hN : LinearMap.range i = span ℤ (Set.range fun j : Fin n0 => bM (Fin.castLE hno j))) :
    ∃ e : Basis (Fin o) ℤ M, ∀ j : Fin n0, (e (Fin.castLE hno j) : M) = i (bN0 j) := by
  classical
  let g₁ : Fin n0 → M := fun j => i (bN0 j)
  let g₂ : Fin (o - n0) → M := fun k => bM (shiftFin hno k)
  let fam : Fin n0 ⊕ Fin (o - n0) → M := Sum.elim g₁ g₂
  have hli₁ : LinearIndependent ℤ g₁ := by
    dsimp [g₁]
    change LinearIndependent ℤ (i ∘ bN0)
    exact (bN0.linearIndependent).map' i hi
  have hli₂ : LinearIndependent ℤ g₂ := by
    dsimp [g₂]
    exact bM.linearIndependent.comp (shiftFin hno) (shiftFin_injective hno)
  have hspan₁ : span ℤ (Set.range g₁) = LinearMap.range i := by
    calc
      span ℤ (Set.range g₁) = span ℤ (i '' Set.range bN0) := by
        congr 1
        change Set.range (i ∘ bN0) = i '' Set.range bN0
        rw [Set.range_comp]
      _ = Submodule.map i (span ℤ (Set.range bN0)) := (Submodule.map_span i (Set.range bN0)).symm
      _ = Submodule.map i ⊤ := by rw [bN0.span_eq]
      _ = LinearMap.range i := Submodule.map_top i
  have hspan₂ : span ℤ (Set.range g₂) = span ℤ (bM '' Set.range (shiftFin hno)) := by
    congr 1
    change Set.range (bM ∘ shiftFin hno) = bM '' Set.range (shiftFin hno)
    rw [Set.range_comp]
  have hNimg : LinearMap.range i = span ℤ (bM '' Set.range (fun j : Fin n0 => Fin.castLE hno j)) := by
    rw [hN]
    congr 1
    change Set.range (bM ∘ (fun j : Fin n0 => Fin.castLE hno j)) = bM '' Set.range (fun j : Fin n0 => Fin.castLE hno j)
    rw [Set.range_comp]
  have hst : IsCompl (Set.range (fun j : Fin n0 => Fin.castLE hno j)) (Set.range (shiftFin hno)) :=
    isCompl_range_castLE_range_shiftFin hno
  have hdisj : Disjoint (span ℤ (Set.range g₁)) (span ℤ (Set.range g₂)) := by
    rw [hspan₁, hNimg, hspan₂]
    exact (bM.linearIndependent.isCompl_span_image (h₂ := bM.span_eq) hst).disjoint
  have hspanfam : span ℤ (Set.range fam) = ⊤ := by
    calc
      span ℤ (Set.range fam) = span ℤ (Set.range g₁ ∪ Set.range g₂) := by
        congr 1
        ext x
        constructor
        · rintro ⟨t, rfl⟩
          cases t with
          | inl j => exact Or.inl ⟨j, rfl⟩
          | inr k => exact Or.inr ⟨k, rfl⟩
        · rintro (⟨j, rfl⟩ | ⟨k, rfl⟩)
          · exact ⟨Sum.inl j, rfl⟩
          · exact ⟨Sum.inr k, rfl⟩
      _ = span ℤ (Set.range g₁) ⊔ span ℤ (Set.range g₂) := Submodule.span_union (Set.range g₁) (Set.range g₂)
      _ = LinearMap.range i ⊔ span ℤ (Set.range g₂) := by rw [hspan₁]
      _ = ⊤ := by
        rw [hNimg, hspan₂]
        exact codisjoint_iff.mp (bM.linearIndependent.isCompl_span_image (h₂ := bM.span_eq) hst).codisjoint
  have hsp : ⊤ ≤ span ℤ (Set.range fam) := le_of_eq hspanfam.symm
  let bT : Basis (Fin n0 ⊕ Fin (o - n0)) ℤ M :=
    Basis.mk (LinearIndependent.sum_type hli₁ hli₂ hdisj) hsp
  let e : Basis (Fin o) ℤ M := bT.reindex (blockEquiv hno)
  refine ⟨e, ?_⟩
  intro j
  have hsym : (blockEquiv hno).symm (Fin.castLE hno j) = Sum.inl j :=
    (blockEquiv hno).left_inv (Sum.inl j)
  have hmain : (e (Fin.castLE hno j) : M) = (bT (Sum.inl j) : M) := by
    dsimp [e]
    rw [Basis.reindex_apply]
    rw [hsym]
  rw [hmain]
  have hbt : (bT (Sum.inl j) : M) = i (bN0 j) := by
    dsimp [bT]
    simp [fam, g₁]
  exact hbt

/-- The inclusion of a smaller lattice into a larger one, as a linear map. -/
def leMap {n : ℕ} (ℒ' ℒ : Submodule ℤ (E n)) (hle : ℒ' ≤ ℒ) : ℒ' →ₗ[ℤ] ℒ where
  toFun x := ⟨(x : E n), hle x.2⟩
  map_add' := by intro x y; ext; rfl
  map_smul' := by intro a x; ext; rfl

lemma leMap_ker {n : ℕ} (ℒ' ℒ : Submodule ℤ (E n)) (hle : ℒ' ≤ ℒ) :
    (leMap ℒ' ℒ hle).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  apply Subtype.ext
  have hv := congrArg (fun z : ℒ => (z : E n)) hxy
  simpa [leMap] using hv

lemma leMap_apply_val {n : ℕ} (ℒ' ℒ : Submodule ℤ (E n)) (hle : ℒ' ≤ ℒ) (x : ℒ') :
    (((leMap ℒ' ℒ hle) x : ℒ) : E n) = (x : E n) := rfl

/-- Ambient purity: if `a ≠ 0` and `a • x` lies in `ℒ'`, then `x` lies in `ℒ'` (given the
ambient-primitivity hypothesis `hprim`). -/
lemma ambient_mem_of_zsmul_mem {n : ℕ} (ℒ' ℒ : Submodule ℤ (E n)) (_hle : ℒ' ≤ ℒ)
    (x : ℒ) (a : ℤ) (ha : a ≠ 0)
    (hax : ((a • x : ℒ) : E n) ∈ ℒ')
    (hprim : ∀ x : E n, x ∈ ℒ' ↔ x ∈ ℒ ∧
       x ∈ Submodule.span ℝ (ℒ' : Set (E n))) :
    (x : E n) ∈ ℒ' := by
  have hxL : (x : E n) ∈ ℒ := x.2
  have haxL' : (a • (x : E n)) ∈ ℒ' := by simpa using hax
  have haxS : (a • (x : E n)) ∈ Submodule.span ℝ (ℒ' : Set (E n)) := subset_span haxL'
  have hcoeff : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hxeq : (x : E n) = (a : ℝ)⁻¹ • (a • (x : E n)) := by
    rw [← Int.cast_smul_eq_zsmul ℝ a (x : E n)]
    simp [hcoeff]
  have hxS : (x : E n) ∈ Submodule.span ℝ (ℒ' : Set (E n)) := by
    rw [hxeq]
    exact (Submodule.span ℝ (ℒ' : Set (E n))).smul_mem (a : ℝ)⁻¹ haxS
  exact (hprim (x : E n)).mpr ⟨hxL, hxS⟩

/-- Purity of the comap submodule `ℒ'.comap ℒ.subtype` in `ℒ`. -/
lemma comap_pure {n : ℕ} (ℒ' ℒ : Submodule ℤ (E n)) (hle : ℒ' ≤ ℒ)
    (hprim : ∀ x : E n, x ∈ ℒ' ↔ x ∈ ℒ ∧ x ∈ Submodule.span ℝ (ℒ' : Set (E n)))
    (x : ℒ) (a : ℤ) (ha : a ≠ 0)
    (hax : a • x ∈ ℒ'.comap (ℒ.subtype)) : x ∈ ℒ'.comap (ℒ.subtype) := by
  rw [Submodule.mem_comap] at hax ⊢
  exact ambient_mem_of_zsmul_mem ℒ' ℒ hle x a ha hax hprim

end BasisExtensionPure


open BasisExtensionPure

/-- Adapted-basis extension for a primitive submodule of a full-rank lattice. -/
theorem basis_extension_pure {n d : ℕ} (hd : d ≤ n)
    (ℒ' ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (hle : ℒ' ≤ ℒ)
    [Module.Free ℤ ℒ] [Module.Finite ℤ ℒ]
    [Module.Free ℤ ℒ'] [Module.Finite ℤ ℒ']
    (hrank : Module.finrank ℤ ℒ = n)
    (b' : Module.Basis (Fin d) ℤ ℒ')
    (hprim : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ ℒ' ↔ x ∈ ℒ ∧
       x ∈ Submodule.span ℝ (ℒ' : Set (EuclideanSpace ℝ (Fin n)))) :
    ∃ e : Module.Basis (Fin n) ℤ ℒ,
      ∀ i : Fin d, ((e (Fin.castLE hd i) : ℒ) : EuclideanSpace ℝ (Fin n)) =
                   ((b' i : ℒ') : EuclideanSpace ℝ (Fin n)) := by
  classical
  let L0 : Submodule ℤ ℒ := ℒ'.comap (ℒ.subtype)
  let leq : L0 ≃ₗ[ℤ] ℒ' := ℒ'.comapSubtypeEquivOfLe hle
  let i : ℒ' →ₗ[ℤ] ℒ := leMap ℒ' ℒ hle
  have hi : i.ker = ⊥ := leMap_ker ℒ' ℒ hle
  let bM0 : Basis (Fin n) ℤ ℒ := Module.finBasisOfFinrankEq ℤ ℒ hrank
  obtain ⟨n0, o, hno, bO, bN, a, hsnf⟩ :=
    Submodule.exists_smith_normal_form_of_le bM0 L0 (⊤ : Submodule ℤ ℒ) le_top
  let bM : Basis (Fin o) ℤ ℒ := bO.map (LinearEquiv.ofTop (⊤ : Submodule ℤ ℒ) rfl)
  have hsnf' : ∀ i0 : Fin n0, ((bN i0 : L0) : ℒ) = a i0 • bM (Fin.castLE hno i0) := by
    intro i0
    simpa [bM] using hsnf i0
  have ha_ne : ∀ i0 : Fin n0, a i0 ≠ 0 := by
    intro i0 h0
    apply (Basis.ne_zero bN i0)
    apply Subtype.ext
    have hrel : ((bN i0 : L0) : ℒ) = 0 := by
      simpa [h0] using hsnf i0
    exact hrel
  have hbMmem : ∀ i0 : Fin n0, bM (Fin.castLE hno i0) ∈ L0 := by
    intro i0
    apply comap_pure ℒ' ℒ hle hprim (bM (Fin.castLE hno i0)) (a i0) (ha_ne i0)
    rw [← hsnf' i0]
    exact (bN i0 : L0).2
  have hL0span : L0 = span ℤ (Set.range fun i0 : Fin n0 => bM (Fin.castLE hno i0)) := by
    apply le_antisymm
    · intro x hx
      rcases (Basis.mem_submodule_iff' bN).mp hx with ⟨c, hc⟩
      rw [hc]
      refine Submodule.sum_mem _ ?_
      intro i0 hi
      have hbNspan : ((bN i0 : L0) : ℒ) ∈
          span ℤ (Set.range fun j0 : Fin n0 => bM (Fin.castLE hno j0)) := by
        rw [hsnf' i0]
        exact (span ℤ (Set.range fun j0 : Fin n0 => bM (Fin.castLE hno j0))).smul_mem
          (a i0) (subset_span ⟨i0, rfl⟩)
      exact (span ℤ (Set.range fun j0 : Fin n0 => bM (Fin.castLE hno j0))).smul_mem (c i0) hbNspan
    · exact span_le.mpr (by
        intro y hy
        rcases hy with ⟨i0, rfl⟩
        exact hbMmem i0)
  have hrange : LinearMap.range i = L0 := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, rfl⟩
      rw [Submodule.mem_comap]
      change (y : E n) ∈ ℒ'
      exact (y : ℒ').2
    · intro hx
      refine ⟨⟨(x : E n), (Submodule.mem_comap.mp hx)⟩, ?_⟩
      ext
      rfl
  -- cardinality data of the SNF output
  have hfinO : Module.finrank ℤ ℒ = o := by
    simpa using (Module.finrank_eq_card_basis bM)
  have hEqO : o = n := by omega
  have hfinN0 : Module.finrank ℤ L0 = n0 := by
    simpa using (Module.finrank_eq_card_basis bN)
  have hfinL' : Module.finrank ℤ ℒ' = d := by
    simpa using (Module.finrank_eq_card_basis b')
  have hfinEq : Module.finrank ℤ L0 = Module.finrank ℤ ℒ' := LinearEquiv.finrank_eq leq
  have hEqN0 : n0 = d := by omega
  -- a block of length d in the basis bM
  have hdo : d ≤ o := by omega
  have hspan_d : span ℤ (Set.range fun j : Fin d => bM (Fin.castLE hdo j)) =
      span ℤ (Set.range fun i0 : Fin n0 => bM (Fin.castLE hno i0)) := by
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      have hj0 : j.val < n0 := by omega
      refine ⟨⟨j.val, hj0⟩, ?_⟩
      change bM (Fin.castLE hno ⟨j.val, hj0⟩) = bM (Fin.castLE hdo j)
      congr
    · rintro ⟨i0, rfl⟩
      have hi0d : i0.val < d := by omega
      refine ⟨⟨i0.val, hi0d⟩, ?_⟩
      change bM (Fin.castLE hdo ⟨i0.val, hi0d⟩) = bM (Fin.castLE hno i0)
      congr
  have hNmaster : LinearMap.range i =
      span ℤ (Set.range fun j : Fin d => bM (Fin.castLE hdo j)) := by
    rw [hrange, hL0span]
    exact hspan_d.symm
  obtain ⟨eM, heM⟩ :=
    exists_basis_extend_of_range_block (M := ℒ) (N := ℒ') (o := o) (n0 := d) hdo i hi bM b' hNmaster
  let e : Basis (Fin n) ℤ ℒ := eM.reindex (finCongr hEqO)
  refine ⟨e, ?_⟩
  intro u
  have hs : (finCongr hEqO).symm (Fin.castLE hd u) = Fin.castLE hdo u := by
    apply Fin.ext
    rfl
  have hm : (e (Fin.castLE hd u) : ℒ) = i (b' u) := by
    dsimp [e]
    rw [Basis.reindex_apply, hs]
    exact heM u
  have hval : ((e (Fin.castLE hd u) : ℒ) : E n) = ((b' u : ℒ') : E n) := by
    rw [hm]
    rfl
  exact hval


end Commons.Lattice.Module

end