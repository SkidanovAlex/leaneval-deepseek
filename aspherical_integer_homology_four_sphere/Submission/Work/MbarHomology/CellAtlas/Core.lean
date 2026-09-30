/-
# The filtration of a `Δ`-complex by the cells of a `CellAtlas`

This file sets up the combinatorial and homological substrate for
`CellAtlas.zMap_quasiIso`.  The atlas `A : CellAtlas K P C` organises the
simplices of the `Δ`-complex `K` by the cells of the finite chain complex `C`,
each cell `(n,e)` of `C` having a "root" face `A.root n e` of `P` and each simplex
`σ` a carrier `A.car σ` and a lift to the subdivision of `P` (`A.lift`).

The *skeletal* filtration of `K` is by the carrier dimension: the `n`-th level
consists of the chains supported on the simplices whose carrier has dimension
`≤ n`.  The cell-by-cell refinement of a level adds the cells of dimension `n+1`
one at a time.  Both are recorded by the predicate
`Work.MbarHomology.CellAtlas.InD`.

On the subdivided side the simplices are numbered, and the `Δ`-chain groups of
`K` are identified with the free modules `Fin (K.card k) →₀ ℤ` along
`CellAtlas.kIso`; the filtrations on `K` are the preimages of the support
conditions there.
-/
import Mathlib
import Submission.Work.MbarHomology.CellAtlas.Defs
import Submission.Work.Subdivision.API

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.MbarHomology

open CategoryTheory

noncomputable section

namespace CellAtlas

-- Pin the `ℤ`-module structures on free modules so that they agree with the ones
-- used by Mathlib's own `LinearEquiv` constructions.
attribute [local instance 2000] Pi.Function.module Finsupp.module

-- As in `Submission/Work/MbarHomology/CellAtlas/Defs.lean`: the generic
-- instances for the `ℤ`-action on an additive group would otherwise win the
-- synthesis of `SMul ℤ ↥M` and break `map_smul`.
attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

variable {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW}
  {C : Work.Certificates.FinChainCx}

/-! ## The refinement predicate -/

/-- The cells of `C`, indexed by their degree. -/
abbrev CellIdx (C : Work.Certificates.FinChainCx) := Σ k : ℕ, Fin (C.dim k)

/-- A cell `c` of `C` belongs to the level `(n,E)` of the refinement: either its
dimension is at most `n`, or it is the `(n+1)`-cell indexed by an element of `E`. -/
def InD (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) (c : CellIdx C) : Prop :=
  c.1 ≤ n ∨ ∃ f : Fin (C.dim (n + 1)), f ∈ E ∧ c = ⟨n + 1, f⟩

theorem inD_of_le {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))} {k : ℕ} (e : Fin (C.dim k))
    (h : k ≤ n) : InD (C := C) n E ⟨k, e⟩ :=
  Or.inl h

theorem InD.dim_le {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))} {c : CellIdx C}
    (h : InD (C := C) n E c) : c.1 ≤ n + 1 := by
  rcases h with h | ⟨f, -, rfl⟩
  · omega
  · simp

theorem InD.mono {n : ℕ} {E E' : Finset (Fin (C.dim (n + 1)))} (h : E ⊆ E')
    {c : CellIdx C} (hc : InD (C := C) n E c) : InD (C := C) n E' c := by
  rcases hc with hc | ⟨f, hf, hc⟩
  · exact Or.inl hc
  · exact Or.inr ⟨f, h hf, hc⟩

theorem inD_empty_iff {n : ℕ} {c : CellIdx C} :
    InD (C := C) n (∅ : Finset (Fin (C.dim (n + 1)))) c ↔ c.1 ≤ n := by
  constructor
  · intro h
    rcases h with h | ⟨f, hf, -⟩
    · exact h
    · exact absurd hf (Finset.notMem_empty f)
  · exact Or.inl

theorem inD_univ_iff {n k : ℕ} (e : Fin (C.dim k)) :
    InD (C := C) n (Finset.univ : Finset (Fin (C.dim (n + 1)))) ⟨k, e⟩ ↔ k ≤ n + 1 := by
  constructor
  · intro h; exact h.dim_le
  · intro h
    rcases lt_or_eq_of_le h with h' | h'
    · exact Or.inl (Nat.lt_succ_iff.mp h')
    · refine Or.inr ⟨h' ▸ e, Finset.mem_univ _, ?_⟩
      cases h'
      rfl

theorem inD_insert_iff {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))} {f₀ : Fin (C.dim (n + 1))}
    {c : CellIdx C} :
    InD (C := C) n (insert f₀ E) c ↔ InD (C := C) n E c ∨ c = ⟨n + 1, f₀⟩ := by
  constructor
  · intro h
    rcases h with h | ⟨f, hf, hc⟩
    · exact Or.inl (Or.inl h)
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact Or.inr hc
      · exact Or.inl (Or.inr ⟨f, hf, hc⟩)
  · rintro (h | h)
    · exact h.mono (Finset.subset_insert _ _)
    · exact Or.inr ⟨f₀, Finset.mem_insert_self _ _, h⟩

theorem inD_iff_of_ne {n k : ℕ} {E : Finset (Fin (C.dim (n + 1)))} (hk : k ≠ n + 1)
    (e : Fin (C.dim k)) : InD (C := C) n E ⟨k, e⟩ ↔ k ≤ n := by
  constructor
  · intro h
    rcases h with h | ⟨f, -, hf⟩
    · exact h
    · exact absurd (congrArg Sigma.fst hf) hk
  · exact Or.inl

/-! ## The filtration of the `C`-side

In degree `k` the chains of `C` are the functions `Fin (C.dim k) → ℤ`; the
filtration records the support condition coordinatewise. -/

/-- The generator of the `C`-chains in degree `k` attached to `b`. -/
abbrev cGen (C : Work.Certificates.FinChainCx) (k : ℕ) (b : Fin (C.dim k)) :
    C.toChainComplex.X k :=
  Pi.single b (1 : ℤ)

/-- The chains of `C` in degree `k` whose support lies in the level `(n,E)`. -/
def CMod (C : Work.Certificates.FinChainCx) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (k : ℕ) : Submodule ℤ (C.toChainComplex.X k) where
  carrier := {x | ∀ b : Fin (C.dim k), ¬ InD (C := C) n E ⟨k, b⟩ →
    (x : Fin (C.dim k) → ℤ) b = 0}
  zero_mem' := by intro b _; rfl
  add_mem' := by
    intro x y hx hy b hb
    show ((x + y : C.toChainComplex.X k) : Fin (C.dim k) → ℤ) b = 0
    rw [show ((x + y : C.toChainComplex.X k) : Fin (C.dim k) → ℤ) b
      = (x : Fin (C.dim k) → ℤ) b + (y : Fin (C.dim k) → ℤ) b from rfl,
      hx b hb, hy b hb, add_zero]
  smul_mem' := by
    intro c x hx b hb
    show ((c • x : C.toChainComplex.X k) : Fin (C.dim k) → ℤ) b = 0
    rw [show ((c • x : C.toChainComplex.X k) : Fin (C.dim k) → ℤ) b
      = c * (x : Fin (C.dim k) → ℤ) b from rfl, hx b hb, mul_zero]

theorem mem_CMod {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))} {k : ℕ}
    {x : C.toChainComplex.X k} :
    x ∈ CMod C n E k ↔ ∀ b : Fin (C.dim k), ¬ InD (C := C) n E ⟨k, b⟩ →
      (x : Fin (C.dim k) → ℤ) b = 0 := Iff.rfl

theorem CMod_mono {n : ℕ} {E E' : Finset (Fin (C.dim (n + 1)))} (h : E ⊆ E') (k : ℕ) :
    CMod C n E k ≤ CMod C n E' k := by
  intro x hx
  rw [mem_CMod] at hx ⊢
  exact fun b hb => hx b (fun hc => hb (InD.mono h hc))

theorem CMod_eq_of_iff {n : ℕ} {E E' : Finset (Fin (C.dim (n + 1)))} (k : ℕ)
    (h : ∀ e : Fin (C.dim k), InD (C := C) n E ⟨k, e⟩ ↔ InD (C := C) n E' ⟨k, e⟩) :
    CMod C n E k = CMod C n E' k := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_CMod] at hx ⊢
    exact fun b hb => hx b (fun hc => hb ((h b).mp hc))
  · intro x hx
    rw [mem_CMod] at hx ⊢
    exact fun b hb => hx b (fun hc => hb ((h b).mpr hc))

theorem CMod_d_apply (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) (k : ℕ)
    {x : C.toChainComplex.X (k + 1)} (hx : x ∈ CMod C n E (k + 1)) :
    ((C.toChainComplex).d (k + 1) k).hom x ∈ CMod C n E k := by
  rw [mem_CMod] at hx ⊢
  intro b hb
  by_cases hk : k ≤ n
  · exact absurd (inD_of_le (C := C) b hk) hb
  · have hx0 : x = 0 := by
      funext e
      exact hx e (fun hIn => by
        have h2 : (⟨k + 1, e⟩ : CellIdx C).1 ≤ n + 1 := hIn.dim_le
        simp only at h2
        omega)
    rw [hx0, map_zero]
    show ((0 : C.toChainComplex.X k) : Fin (C.dim k) → ℤ) b = 0
    rfl

/-- The level-`(n,E)` filtration of the chain complex of `C`. -/
def CSD (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) : Work.Subdivision.SubData C.toChainComplex where
  sub k := CMod C n E k
  d_mem k x hx := CMod_d_apply (C := C) n E k hx

@[simp] theorem CSD_sub (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) (k : ℕ) :
    (CSD (C := C) n E).sub k = CMod C n E k := rfl

/-- The expansion of a `C`-chain in the generators `cGen`. -/
theorem cGen_expand (C : Work.Certificates.FinChainCx) (k : ℕ) (x : C.toChainComplex.X k) :
    x = ∑ b : Fin (C.dim k), x b • cGen C k b := by
  have h : x = ∑ b : Fin (C.dim k), x b • (Pi.single b (1 : ℤ) : Fin (C.dim k) → ℤ) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  conv_lhs => rw [h]
  try rfl

/-! ## Finsupp and module-category helpers -/

/-- A `Finsupp` is the linear combination of its values on the standard basis. -/
theorem finsupp_eq_linearCombination_single {α : Type*} (y : α →₀ ℤ) :
    y = Finsupp.linearCombination ℤ (fun b : α => Finsupp.single b (1 : ℤ)) y := by
  conv_lhs => rw [← Finsupp.sum_single y]
  rw [Finsupp.linearCombination_apply]
  exact Finsupp.sum_congr fun b _ => by rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- A linear map commutes with the expansion of a `Finsupp` in the standard
basis. -/
theorem LinearMap.linearCombination_comp {ι α : Type*} {N : Type*} [AddCommMonoid N] [Module ℤ N]
    (f : (α →₀ ℤ) →ₗ[ℤ] N) (v : ι → (α →₀ ℤ)) (x : ι →₀ ℤ) :
    f (Finsupp.linearCombination ℤ v x) = Finsupp.linearCombination ℤ (fun i => f (v i)) x := by
  rw [Finsupp.linearCombination_apply]
  conv_rhs => rw [Finsupp.linearCombination_apply]
  rw [show x.sum (fun i a => a • v i) = ∑ i ∈ x.support, x i • v i from rfl, map_sum]
  rw [show x.sum (fun i a => a • f (v i)) = ∑ i ∈ x.support, x i • f (v i) from rfl]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]

/-- The value of a linear combination of a family of `Finsupp`s. -/
theorem linearCombination_apply_single_sum {ι α : Type*} [DecidableEq α]
    (M : ι → α →₀ ℤ) (x : ι →₀ ℤ) (a : α) :
    (Finsupp.linearCombination ℤ M x : α →₀ ℤ) a = ∑ i ∈ x.support, x i * (M i) a := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_apply]
  rw [show x.sum (fun i c => (c • M i) a) = ∑ i ∈ x.support, (x i • M i) a from rfl]
  exact Finset.sum_congr rfl fun i _ => by rw [Finsupp.smul_apply, smul_eq_mul]

theorem ModuleCat.hom_finset_sum {R : Type*} [Ring R] {M N : ModuleCat R} {ι : Type*}
    (s : Finset ι) (f : ι → (M ⟶ N)) : (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModuleCat.hom_add, ih]

theorem ModuleCat.hom_zsmul {R : Type*} [Ring R] {M N : ModuleCat R} (c : ℤ) (f : M ⟶ N) :
    (c • f).hom = c • f.hom := ModuleCat.hom_smul c f

theorem ModuleCat.hom_sum_apply {R : Type*} [Ring R] {M N : ModuleCat R} {ι : Type*}
    (f : ι → (M ⟶ N)) (s : Finset ι) (x : M) :
    ((∑ i ∈ s, f i : M ⟶ N)).hom x = ∑ i ∈ s, ((f i).hom x) := by
  rw [ModuleCat.hom_sum]
  exact LinearMap.sum_apply s (fun i => (f i).hom) x

theorem ModuleCat.hom_zsmul_apply {R : Type*} [Ring R] {M N : ModuleCat R} (c : ℤ)
    (f : M ⟶ N) (x : M) : ((c • f : M ⟶ N)).hom x = c • (f.hom x) := rfl

/-! ## The `K`-side, in the free-module model -/

/-- The free module on the `k`-simplices of `K`. -/
abbrev kMod (K : Work.DeltaHomology.DeltaCx) (k : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (Fin (K.card k) →₀ ℤ)

/-- The canonical isomorphism between the `k`-th `Δ`-chains of `K` and the free
module on its `k`-simplices. -/
noncomputable def kIso (K : Work.DeltaHomology.DeltaCx) (k : ℕ) : K.chainX k ≅ kMod K k :=
  Work.Subdivision.PolyCW.freeIso (Equiv.refl (Fin (K.card k)))

theorem kIso_chainι (K : Work.DeltaHomology.DeltaCx) (k : ℕ) (σ : Fin (K.card k)) :
    (kIso K k).hom ((K.chainι k σ) (1 : ℤ)) = Finsupp.single σ (1 : ℤ) := by
  have h : K.chainι k σ ≫ (kIso K k).hom = ModuleCat.ofHom (Finsupp.lsingle (M := ℤ) σ) := by
    rw [kIso]
    exact Limits.Sigma.ι_comp_desc _ σ
  rw [← ModuleCat.comp_apply, h]
  exact Finsupp.lsingle_apply σ (1 : ℤ)

theorem kIso_inv_single (K : Work.DeltaHomology.DeltaCx) (k : ℕ) (σ : Fin (K.card k)) :
    (kIso K k).inv (Finsupp.single σ (1 : ℤ)) = (K.chainι k σ) (1 : ℤ) := by
  calc (kIso K k).inv (Finsupp.single σ (1 : ℤ))
      = (kIso K k).inv ((kIso K k).hom ((K.chainι k σ) (1 : ℤ))) := by rw [kIso_chainι]
    _ = (K.chainι k σ) (1 : ℤ) := by
        rw [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]

/-- The boundary of the `Δ`-chain complex on a basis simplex, transported to the
free module on the simplices. -/
theorem kIso_chainD_chainι (K : Work.DeltaHomology.DeltaCx) (k : ℕ)
    (σ : Fin (K.card (k + 1))) :
    (kIso K k).hom ((K.chainD k).hom ((K.chainι (k + 1) σ) (1 : ℤ))) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (K.face σ i) (1 : ℤ) := by
  have h := Work.DeltaHomology.DeltaCx.ι_chainD K k σ
  have h1 : (kIso K k).hom ((K.chainD k).hom ((K.chainι (k + 1) σ) (1 : ℤ)))
      = ((K.chainι (k + 1) σ ≫ K.chainD k) ≫ (kIso K k).hom) (1 : ℤ) := by
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  have h2 : (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • K.chainι k (K.face σ i)) ≫
        (kIso K k).hom
      = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ModuleCat.ofHom (Finsupp.lsingle (M := ℤ) (K.face σ i)) := by
    rw [show (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • K.chainι k (K.face σ i)) ≫
          (kIso K k).hom
        = (∑ i ∈ (Finset.univ : Finset (Fin (k + 2))),
            (-1 : ℤ) ^ (i : ℕ) • K.chainι k (K.face σ i)) ≫ (kIso K k).hom from rfl]
    rw [Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp]
    congr 1
    rw [kIso]
    exact Limits.Sigma.ι_comp_desc _ (K.face σ i)
  rw [h1, h, h2]
  rw [show (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ModuleCat.ofHom (Finsupp.lsingle (M := ℤ) (K.face σ i)))
      = ∑ i ∈ (Finset.univ : Finset (Fin (k + 2))), ((-1 : ℤ) ^ (i : ℕ) •
        ModuleCat.ofHom (Finsupp.lsingle (M := ℤ) (K.face σ i))) from rfl]
  rw [ModuleCat.hom_sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ModuleCat.hom_zsmul_apply, ModuleCat.hom_ofHom, Finsupp.lsingle_apply]

/-- The transported boundary on the free module on the `k`-simplices. -/
noncomputable def kδCpt (K : Work.DeltaHomology.DeltaCx) (k : ℕ) :
    kMod K (k + 1) ⟶ kMod K k :=
  (kIso K (k + 1)).inv ≫ K.chainD k ≫ (kIso K k).hom

theorem kδCpt_single (K : Work.DeltaHomology.DeltaCx) (k : ℕ)
    (σ : Fin (K.card (k + 1))) :
    kδCpt K k (Finsupp.single σ (1 : ℤ)) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (K.face σ i) (1 : ℤ) := by
  rw [kδCpt, ModuleCat.comp_apply, ModuleCat.comp_apply, kIso_inv_single]
  exact kIso_chainD_chainι K k σ

/-- The coefficient of `τ` in the transported boundary of a simplex none of whose
faces is `τ` vanishes. -/
theorem InD.car_face (A : CellAtlas K P C) {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))}
    {k : ℕ} {σ : Fin (K.card (k + 1))} (hσ : InD (C := C) n E (A.car σ))
    (i : Fin (k + 2)) : InD (C := C) n E (A.car (K.face σ i)) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [(A.face_ne_last σ j).1]; exact hσ
  · refine Or.inl ?_
    have h1 : (A.car (K.face σ (Fin.last (k + 1)))).1 < (A.car σ).1 := A.face_last σ
    have h2 : (A.car σ).1 ≤ n + 1 := hσ.dim_le
    omega

/-! ## The filtration of the `K`-side -/

/-- The basis vectors attached to the level `(n,E)`. -/
def kSet (A : CellAtlas K P C) (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) (k : ℕ) :
    Set (kMod K k) :=
  {y | ∃ σ : Fin (K.card k), InD (C := C) n E (A.car σ) ∧ y = Finsupp.single σ (1 : ℤ)}

/-- The chains of the model in degree `k` supported on the level `(n,E)`. -/
def kSup (A : CellAtlas K P C) (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) (k : ℕ) :
    Submodule ℤ (kMod K k) :=
  Submodule.span ℤ (kSet A n E k)

theorem mem_kSup {A : CellAtlas K P C} {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))} {k : ℕ}
    {y : kMod K k} :
    y ∈ kSup A n E k ↔
      ∀ σ : Fin (K.card k), σ ∈ (y : Fin (K.card k) →₀ ℤ).support →
        InD (C := C) n E (A.car σ) := by
  rw [kSup, show kSet A n E k = {y : kMod K k |
      ∃ b ∈ {σ : Fin (K.card k) | InD (C := C) n E (A.car σ)},
        y = Finsupp.single b (1 : ℤ)} from by
    ext y
    exact ⟨fun ⟨σ, hσ, hy⟩ => ⟨σ, hσ, hy⟩, fun ⟨σ, hσ, hy⟩ => ⟨σ, hσ, hy⟩⟩,
    Work.Subdivision.Finsupp.mem_span_single_one_iff]
  constructor
  · intro h σ hσ
    by_contra hni
    exact hni (h hσ)
  · intro h σ hσ
    exact h σ hσ

/-- The level-`(n,E)` filtration of the chain module of `K`. -/
def KMod (A : CellAtlas K P C) (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) (k : ℕ) :
    Submodule ℤ (K.chainX k) :=
  (kSup A n E k).comap ((kIso K k).hom).hom

theorem mem_KMod {A : CellAtlas K P C} {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))} {k : ℕ}
    {y : K.chainX k} :
    y ∈ KMod A n E k ↔ (kIso K k).hom y ∈ kSup A n E k :=
  Submodule.mem_comap

theorem KMod_mono {A : CellAtlas K P C} {n : ℕ} {E E' : Finset (Fin (C.dim (n + 1)))}
    (h : E ⊆ E') (k : ℕ) : KMod A n E k ≤ KMod A n E' k := by
  intro y hy
  rw [mem_KMod] at hy ⊢
  rw [mem_kSup] at hy ⊢
  exact fun σ hσ => InD.mono h (hy σ hσ)

theorem kδCpt_mem_kSup (A : CellAtlas K P C) (n : ℕ) (E : Finset (Fin (C.dim (n + 1))))
    (k : ℕ) (z : kMod K (k + 1)) (hz : z ∈ kSup A n E (k + 1)) :
    kδCpt K k z ∈ kSup A n E k := by
  rw [kSup] at hz ⊢
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨σ, hσ, rfl⟩ := hy
      rw [kδCpt_single]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span ⟨K.face σ i, hσ.car_face A i, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z hy hz' ihy ihz => rw [map_add]; exact Submodule.add_mem _ ihy ihz
  | smul c y hy ihy => rw [map_smul]; exact Submodule.smul_mem _ _ ihy

theorem KMod_d_apply (A : CellAtlas K P C) (n : ℕ) (E : Finset (Fin (C.dim (n + 1))))
    (k : ℕ) {y : K.chainX (k + 1)} (hy : y ∈ KMod A n E (k + 1)) :
    (K.chainD k).hom y ∈ KMod A n E k := by
  rw [mem_KMod] at hy ⊢
  have hcomm : (kIso K k).hom ((K.chainD k).hom y) =
      kδCpt K k ((kIso K (k + 1)).hom y) := by
    have h1 : (kIso K (k + 1)).inv ((kIso K (k + 1)).hom y) = y := by
      rw [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]
    rw [kδCpt, ModuleCat.comp_apply, ModuleCat.comp_apply, h1]
  rw [hcomm]
  exact kδCpt_mem_kSup A n E k _ hy

/-- The level-`(n,E)` filtration of the chain complex of `K`. -/
def KSD (A : CellAtlas K P C) (n : ℕ) (E : Finset (Fin (C.dim (n + 1)))) :
    Work.Subdivision.SubData K.chain where
  sub k := KMod A n E k
  d_mem k y hy := by
    rw [Work.DeltaHomology.DeltaCx.chain_d]
    exact KMod_d_apply A n E k hy

@[simp] theorem KSD_sub (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (k : ℕ) : (KSD A n E).sub k = KMod A n E k := rfl

/-! ## The value of the atlas chain on a simplex -/

/-- The value of the atlas chain on a cell, transported to the free module. -/
noncomputable def kz (A : CellAtlas K P C) (k : ℕ) (e : Fin (C.dim k)) : kMod K k :=
  (kIso K k).hom (A.z k e)

theorem kz_eq (A : CellAtlas K P C) (k : ℕ) (e : Fin (C.dim k)) :
    kz A k e = ∑ s : Work.Subdivision.Simplex P.Cell k,
      if h : s (Fin.last k) = A.root k e then
        A.rootCoeff k e s • Finsupp.single ((A.liftEquiv k k e).symm ⟨s, h⟩).1 (1 : ℤ)
      else 0 := by
  rw [kz, z, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : s (Fin.last k) = A.root k e
  · rw [dif_pos h, map_smul, kIso_chainι, dif_pos h]
  · rw [dif_neg h, map_zero, dif_neg h]

theorem kz_support (A : CellAtlas K P C) (k : ℕ) (e : Fin (C.dim k)) :
    ∀ σ ∈ (kz A k e).support, A.car σ = ⟨k, e⟩ := by
  have hmem : kz A k e ∈ Submodule.span ℤ {y : Fin (K.card k) →₀ ℤ |
      ∃ σ ∈ {σ : Fin (K.card k) | A.car σ = ⟨k, e⟩}, y = Finsupp.single σ (1 : ℤ)} := by
    rw [kz_eq]
    refine Submodule.sum_mem _ fun s _ => ?_
    by_cases h : s (Fin.last k) = A.root k e
    · rw [dif_pos h]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
      exact ((A.liftEquiv k k e).symm ⟨s, h⟩).2
    · rw [dif_neg h]; exact Submodule.zero_mem _
  exact (Work.Subdivision.Finsupp.mem_span_single_one_iff (R := ℤ)).mp hmem

/-! ## The filtered atlas map -/

theorem kz_mem_kSup (A : CellAtlas K P C) {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))}
    {k : ℕ} {b : Fin (C.dim k)} (hb : InD (C := C) n E ⟨k, b⟩) :
    kz A k b ∈ kSup A n E k :=
  (mem_kSup (A := A)).mpr fun σ hσ => by
    rw [kz_support A k b σ hσ]
    exact hb

theorem kIso_zMap_expand (A : CellAtlas K P C) (h : A.BoundaryCompat) (k : ℕ)
    (x : C.toChainComplex.X k) :
    (kIso K k).hom (((A.zMap h).f k).hom x) =
      ∑ b : Fin (C.dim k), x b • kz A k b := by
  have key : (kIso K k).hom (((A.zMap h).f k).hom x)
      = ∑ b : Fin (C.dim k), x b • kz A k b := by
    have hstep : ((A.zMap h).f k).hom x = ∑ b : Fin (C.dim k), x b • A.z k b := by
      conv_lhs => rw [cGen_expand C k x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul]
      rw [show ((A.zMap h).f k) (cGen C k b) = A.z k b from A.zMapFun_piSingle k b]
      try rfl
    rw [hstep]
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul]
    rfl
  exact key

theorem levelHf (A : CellAtlas K P C) (h : A.BoundaryCompat) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) :
    ∀ k, CMod C n E k ≤ (KMod A n E k).comap ((A.zMap h).f k).hom := by
  intro k x hx
  show (kIso K k).hom (((A.zMap h).f k).hom x) ∈ kSup A n E k
  rw [kIso_zMap_expand A h k x]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : InD (C := C) n E ⟨k, b⟩
  · exact Submodule.smul_mem _ _ (kz_mem_kSup A hb)
  · rw [(mem_CMod.mp hx) b hb, zero_smul]
    exact Submodule.zero_mem _

/-- **The atlas map restricted to a level `(n,E)` of the refinement.** -/
noncomputable def levelMap (A : CellAtlas K P C) (h : A.BoundaryCompat) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) :
    (CSD (C := C) n E).chain ⟶ (KSD A n E).chain :=
  (CSD (C := C) n E).restrictMap (KSD A n E) (A.zMap h) (levelHf A h n E)

@[simp] theorem levelMap_f (A : CellAtlas K P C) (h : A.BoundaryCompat) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (k : ℕ) :
    (levelMap A h n E).f k = (CSD (C := C) n E).restrictCptMap (KSD A n E) (A.zMap h)
      (levelHf A h n E) k := rfl

/-! ## The piece of a single cell: the filtration away from its own degree -/

theorem CMod_insert_eq_of_ne {n : ℕ} {E : Finset (Fin (C.dim (n + 1)))} {f₀ : Fin (C.dim (n + 1))}
    {k : ℕ} (hk : k ≠ n + 1) : CMod C n (insert f₀ E) k = CMod C n E k :=
  CMod_eq_of_iff (C := C) k fun e => by
    rw [inD_insert_iff]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd (congrArg Sigma.fst h) hk
    · exact Or.inl

/-- The dimension of the carrier of a `k`-simplex is at least `k`. -/
theorem le_car (A : CellAtlas K P C) : ∀ (k : ℕ) (σ : Fin (K.card k)), k ≤ (A.car σ).1 := by
  intro k
  induction k with
  | zero => intro σ; exact Nat.zero_le _
  | succ k ih =>
      intro σ
      have h1 : (A.car (K.face σ (Fin.last (k + 1)))).1 < (A.car σ).1 := A.face_last σ
      have h2 : k ≤ (A.car (K.face σ (Fin.last (k + 1)))).1 := ih (K.face σ (Fin.last (k + 1)))
      omega

theorem kSet_insert_eq_of_ne {A : CellAtlas K P C} {n : ℕ}
    {E : Finset (Fin (C.dim (n + 1)))} {f₀ : Fin (C.dim (n + 1))} {k : ℕ} (hk : n + 1 < k) :
    kSet A n (insert f₀ E) k = kSet A n E k := by
  ext y
  constructor
  · rintro ⟨σ, hσ, hy⟩
    refine ⟨σ, ?_, hy⟩
    rw [inD_insert_iff] at hσ
    rcases hσ with h | h
    · exact h
    · have hk' : k ≤ (⟨n + 1, f₀⟩ : CellIdx C).1 := h ▸ le_car A k σ
      simp only at hk'
      omega
  · rintro ⟨σ, hσ, hy⟩
    exact ⟨σ, hσ.mono (Finset.subset_insert _ _), hy⟩

theorem KMod_insert_eq_of_ne {A : CellAtlas K P C} {n : ℕ}
    {E : Finset (Fin (C.dim (n + 1)))} {f₀ : Fin (C.dim (n + 1))} {k : ℕ} (hk : n + 1 < k) :
    KMod A n (insert f₀ E) k = KMod A n E k := by
  rw [KMod, KMod, kSup, kSup, kSet_insert_eq_of_ne (A := A) hk]

/-! ## The relative subcomplexes carried by a single new cell -/

/-- The relative subcomplex of the refined `C`-filtration carried by the new cell. -/
noncomputable abbrev CPiece (n : ℕ) (E : Finset (Fin (C.dim (n + 1))))
    (f₀ : Fin (C.dim (n + 1))) :
    Work.Subdivision.SubData ((CSD (C := C) n (insert f₀ E)).chain) :=
  (CSD (C := C) n (insert f₀ E)).comapChain (CMod C n E)
    (fun k => CMod_mono (Finset.subset_insert f₀ E) k)
    (fun k x hx => CMod_d_apply (C := C) n E k hx)

/-- The relative subcomplex of the refined `K`-filtration carried by the new cell. -/
noncomputable abbrev KPiece (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) :
    Work.Subdivision.SubData ((KSD A n (insert f₀ E)).chain) :=
  (KSD A n (insert f₀ E)).comapChain (KMod A n E)
    (fun k => KMod_mono (Finset.subset_insert f₀ E) k)
    (fun k x hx => by
      rw [Work.DeltaHomology.DeltaCx.chain_d]
      exact KMod_d_apply A n E k hx)

@[simp] theorem CPiece_sub (n : ℕ) (E : Finset (Fin (C.dim (n + 1))))
    (f₀ : Fin (C.dim (n + 1))) (k : ℕ) :
    (CPiece (C := C) n E f₀).sub k =
      (CMod C n E k).comap (Submodule.subtype ((CSD (C := C) n (insert f₀ E)).sub k)) := rfl

@[simp] theorem KPiece_sub (A : CellAtlas K P C) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) (k : ℕ) :
    (KPiece A n E f₀).sub k =
      (KMod A n E k).comap (Submodule.subtype ((KSD A n (insert f₀ E)).sub k)) := rfl

/-- The filtered atlas map carries the `C`-piece into the `K`-piece. -/
theorem pieceHf (A : CellAtlas K P C) (h : A.BoundaryCompat) (n : ℕ)
    (E : Finset (Fin (C.dim (n + 1)))) (f₀ : Fin (C.dim (n + 1))) :
    ∀ k, (CPiece (C := C) n E f₀).sub k ≤
      ((KPiece A n E f₀).sub k).comap ((levelMap A h n (insert f₀ E)).f k).hom := by
  intro k x hx
  rw [CPiece_sub] at hx
  rw [Submodule.mem_comap] at hx
  rw [KPiece_sub, Submodule.mem_comap]
  show (A.zMap h).f k ↑x ∈ KMod A n E k
  exact (levelHf A h n E k) hx


end CellAtlas

end

end Work.MbarHomology
