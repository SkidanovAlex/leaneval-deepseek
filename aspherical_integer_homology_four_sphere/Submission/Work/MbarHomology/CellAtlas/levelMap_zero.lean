import Mathlib
import Submission.Work.MbarHomology.CellAtlas.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The zero-th level of the `CellAtlas` refinement

The base case of the cell-by-cell induction computing the homology of a
`Δ`-complex `K` through a `CellAtlas K P C`: the restriction of the atlas chain
map to the level `(0, ∅)` -- the chains supported on the cells of `C` of
dimension `0`, respectively on the simplices of `K` whose carrier has dimension
`0` -- is a quasi-isomorphism.

Both filtered complexes are concentrated in degree `0`:

* on the `C`-side, `CMod C 0 ∅ 0 = ⊤` and `CMod C 0 ∅ k = ⊥` for `k ≥ 1`
  (`CMod_zero_empty_eq_bot`), since in degree `k` the level `(0, ∅)` contains a
  cell only when `k = 0`;
* on the `K`-side, `kSup A 0 ∅ k = ⊥` for `k ≥ 1` (`kSup_zero_empty_eq_bot`):
  a `k`-simplex with `k ≥ 1` whose carrier is a vertex would have to be a chain
  of `k + 1 ≥ 2` distinct faces of that vertex, impossible.

In degree `0` the atlas map sends the generator of the `0`-cell `e` to the
`0`-simplex of `K` lying over it (`kz_zero`), and the carriers give a bijection
between the `0`-cells and those simplices (`sigmaZero`); hence the degree-`0`
component is an isomorphism and the whole level map an isomorphism of chain
complexes, in particular a quasi-isomorphism.
-/

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Work.MbarHomology

open CategoryTheory

open Work.Subdivision

noncomputable section

namespace CellAtlas

-- Pin the `ℤ`-module structures on free modules so that they agree with the ones
-- used by Mathlib's own `LinearEquiv` constructions (see `Core.lean`).
attribute [local instance 2000] Pi.Function.module Finsupp.module
attribute [local instance 100] ZSMul.toSMul
attribute [local instance 100] instMulActionIntOfSubtractionMonoid

variable {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW}
  {C : Work.Certificates.FinChainCx}

/-! ## The level `(0, ∅)` on the `C`-side -/

theorem CMod_eq_top_of_le {n k : ℕ} (hk : k ≤ n) (E : Finset (Fin (C.dim (n + 1)))) :
    CMod C n E k = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [mem_CMod]
  intro b hb
  exact absurd (inD_of_le (C := C) b hk) hb

theorem CMod_zero_empty_eq_bot {k : ℕ} (hk : 1 ≤ k) :
    CMod C 0 (∅ : Finset (Fin (C.dim 1))) k = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [mem_CMod] at hx
  funext b
  exact hx b (by rw [inD_empty_iff]; change ¬ k ≤ 0; omega)

/-! ## The level `(0, ∅)` on the `K`-side -/

/-- There is no simplex of dimension `k ≥ 1` whose carrier is a `0`-cell: its
lift would be a chain of at least two distinct faces of a vertex. -/
theorem not_inD_zero_empty_car (A : CellAtlas K P C) {k : ℕ} (hk : 1 ≤ k)
    (σ : Fin (K.card k)) : ¬ InD (C := C) 0 (∅ : Finset (Fin (C.dim 1))) (A.car σ) := by
  intro hσ
  have hzero : (A.car σ).1 = 0 := by
    rw [inD_empty_iff] at hσ
    change (A.car σ).1 ≤ 0 at hσ
    omega
  have htop : A.lift σ (Fin.last k) = A.root (A.car σ).1 (A.car σ).2 := A.lift_top σ
  have hdimtop : P.dim (A.lift σ (Fin.last k)) = 0 := by
    rw [htop, A.dim_root, hzero]
  have h01 : (⟨0, by omega⟩ : Fin (k + 1)) < ⟨1, by omega⟩ := by
    rw [Fin.lt_def]; simp
  have hle : (⟨1, by omega⟩ : Fin (k + 1)) ≤ Fin.last k := by
    rw [Fin.le_def, Fin.val_last]; simp; omega
  have hmono : A.lift σ ⟨1, by omega⟩ ≤ A.lift σ (Fin.last k) :=
    (A.lift σ).strictMono.monotone hle
  have h1 : P.dim (A.lift σ ⟨1, by omega⟩) ≤ 0 := by
    have := P.dim_le hmono
    rw [hdimtop] at this
    exact this
  have h0 : P.dim (A.lift σ ⟨0, by omega⟩) < P.dim (A.lift σ ⟨1, by omega⟩) :=
    P.dim_lt' ((A.lift σ).strictMono h01)
  omega

theorem kSup_zero_empty_eq_bot (A : CellAtlas K P C) {k : ℕ} (hk : 1 ≤ k) :
    kSup A 0 (∅ : Finset (Fin (C.dim 1))) k = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  rw [mem_kSup] at hy
  refine Finsupp.ext fun σ => ?_
  by_contra hne
  exact (not_inD_zero_empty_car A hk σ) (hy σ (Finsupp.mem_support_iff.mpr hne))

theorem KMod_zero_empty_eq_bot (A : CellAtlas K P C) {k : ℕ} (hk : 1 ≤ k) :
    KMod A 0 (∅ : Finset (Fin (C.dim 1))) k = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  rw [mem_KMod] at hy
  rw [kSup_zero_empty_eq_bot A hk] at hy
  have h0 : (kIso K k).hom y = 0 := (Submodule.mem_bot ℤ).mp hy
  rw [show y = (kIso K k).inv ((kIso K k).hom y) from by
        rw [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply], h0, map_zero]

/-! ## The bijection between the `0`-cells and the simplices over them -/

/-- The unique `0`-simplex of `K` whose carrier is the `0`-cell `e`. -/
noncomputable def sigmaZero (A : CellAtlas K P C) (e : Fin (C.dim 0)) : Fin (K.card 0) :=
  ((A.liftEquiv 0 0 e).symm ⟨Work.Subdivision.Simplex.vertex (A.root 0 e), rfl⟩).1

theorem car_sigmaZero (A : CellAtlas K P C) (e : Fin (C.dim 0)) :
    A.car (sigmaZero A e) = ⟨0, e⟩ :=
  ((A.liftEquiv 0 0 e).symm ⟨Work.Subdivision.Simplex.vertex (A.root 0 e), rfl⟩).2

/-- A `0`-simplex is determined by its unique vertex. -/
theorem simplex_zero_eq_vertex {a : P.Cell} {s : Work.Subdivision.Simplex P.Cell 0}
    (h : s (Fin.last 0) = a) : s = Work.Subdivision.Simplex.vertex a := by
  ext i
  rw [Work.Subdivision.Simplex.vertex_apply]
  have hi : i = Fin.last 0 := by
    apply Fin.ext
    simp only [Fin.val_last]
    have := i.isLt
    omega
  rw [hi, h]

theorem lift_eq_vertex_of_car_zero (A : CellAtlas K P C) {σ : Fin (K.card 0)}
    {e : Fin (C.dim 0)} (h : A.car σ = ⟨0, e⟩) :
    A.lift σ = Work.Subdivision.Simplex.vertex (A.root 0 e) := by
  apply simplex_zero_eq_vertex
  have htop := A.lift_top σ
  rw [h] at htop
  exact htop

theorem eq_sigmaZero_of_car (A : CellAtlas K P C) {σ : Fin (K.card 0)} {e : Fin (C.dim 0)}
    (h : A.car σ = ⟨0, e⟩) : σ = sigmaZero A e := by
  have h1 : (A.liftFun 0 0 e) ⟨σ, h⟩ =
      (A.liftFun 0 0 e) ⟨sigmaZero A e, car_sigmaZero A e⟩ := by
    apply Subtype.ext
    simp only [liftFun]
    rw [lift_eq_vertex_of_car_zero A h, lift_eq_vertex_of_car_zero A (car_sigmaZero A e)]
  exact congrArg Subtype.val ((A.lift_bij 0 0 e).injective h1)

theorem sigmaZero_injective (A : CellAtlas K P C) : Function.Injective (sigmaZero A) := by
  intro e e' h
  have h2 : (⟨0, e⟩ : Sigma (fun n => Fin (C.dim n))) = ⟨0, e'⟩ := by
    rw [← car_sigmaZero A e, ← car_sigmaZero A e', h]
  exact eq_of_heq (Sigma.mk.injEq _ _ _ _ |>.mp h2 |>.2)

theorem exists_car_zero (A : CellAtlas K P C) {σ : Fin (K.card 0)}
    (hσ : InD (C := C) 0 (∅ : Finset (Fin (C.dim 1))) (A.car σ)) :
    ∃ e : Fin (C.dim 0), A.car σ = ⟨0, e⟩ := by
  rcases hcar : A.car σ with ⟨n, b⟩
  have hle : n ≤ 0 := by
    rw [hcar] at hσ
    exact (inD_empty_iff (C := C) (n := 0)).mp hσ
  have hn : n = 0 := Nat.le_zero.mp hle
  subst hn
  exact ⟨b, rfl⟩

/-! ## The value of the atlas chain in degree zero -/

theorem rootCoeff_zero_self (A : CellAtlas K P C) (e : Fin (C.dim 0)) :
    A.rootCoeff 0 e (Work.Subdivision.Simplex.vertex (A.root 0 e)) = 1 := by
  simp only [CellAtlas.rootCoeff, Work.Subdivision.PolyCW.subdivCell_zero]
  rw [Finsupp.single_eq_same]

/-- The atlas chain of a `0`-cell is the basis vector of the `0`-simplex over it. -/
theorem kz_zero (A : CellAtlas K P C) (e : Fin (C.dim 0)) :
    kz A 0 e = Finsupp.single (sigmaZero A e) (1 : ℤ) := by
  rw [kz_eq]
  rw [Finset.sum_eq_single (Work.Subdivision.Simplex.vertex (A.root 0 e))]
  · rw [dite_eq_left (Work.Subdivision.Simplex.vertex_apply (A.root 0 e) (Fin.last 0)),
      rootCoeff_zero_self A e, one_smul]
    congr 1
  · intro s _ hs
    rw [dite_eq_right (fun h => hs (simplex_zero_eq_vertex h))]
  · intro hb; exact absurd (Finset.mem_univ _) hb

/-! ## The degree-`0` component of the atlas map -/

/-- The degree-`0` component of the atlas map, transported to the free model on
the simplices of `K`. -/
noncomputable def kzComp (A : CellAtlas K P C) : C.toChainComplex.X 0 →ₗ[ℤ] kMod K 0 :=
  (ModuleCat.Hom.hom (kIso K 0).hom).comp (ModuleCat.Hom.hom (A.zMapFun 0))

theorem kzComp_piSingle (A : CellAtlas K P C) (e : Fin (C.dim 0)) :
    kzComp A (Pi.single e (1 : ℤ)) = Finsupp.single (sigmaZero A e) 1 := by
  change (ConcreteCategory.hom (kIso K 0).hom)
    ((ModuleCat.Hom.hom (A.zMapFun 0)) (Pi.single e (1 : ℤ))) = _
  rw [zMapFun_piSingle A 0 e]
  exact kz_zero A e

/-- The level-`(0, ∅)` free model is spanned by the images of the generators. -/
theorem kSup_zero_empty_le_map (A : CellAtlas K P C) (_h : A.BoundaryCompat) :
    kSup A 0 (∅ : Finset (Fin (C.dim 1))) 0 ≤ Submodule.map (kzComp A) ⊤ := by
  rw [kSup, Submodule.span_le]
  rintro z ⟨σ, hσ, rfl⟩
  obtain ⟨e, he⟩ := exists_car_zero A hσ
  refine Submodule.mem_map.mpr ⟨Pi.single e (1 : ℤ), Submodule.mem_top, ?_⟩
  rw [kzComp_piSingle, ← eq_sigmaZero_of_car A he]

theorem kz_sum_apply (A : CellAtlas K P C) (x : Fin (C.dim 0) → ℤ) (b₀ : Fin (C.dim 0)) :
    (∑ b, x b • kz A 0 b) (sigmaZero A b₀) = x b₀ := by
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single b₀]
  · rw [Finsupp.smul_apply, kz_zero, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro b _ hb
    rw [Finsupp.smul_apply, kz_zero,
      Finsupp.single_eq_of_ne (fun hh => hb (sigmaZero_injective A hh).symm), smul_eq_mul,
      mul_zero]
  · intro hb; exact absurd (Finset.mem_univ _) hb

theorem zMapFun_zero_injective (A : CellAtlas K P C) (h : A.BoundaryCompat) :
    Function.Injective (A.zMapFun 0).hom := by
  intro x y hxy
  have hx : (ConcreteCategory.hom (kIso K 0).hom)
      ((ModuleCat.Hom.hom (A.zMapFun 0)) x) = ∑ b, x b • kz A 0 b :=
    kIso_zMap_expand A h 0 x
  have hy : (ConcreteCategory.hom (kIso K 0).hom)
      ((ModuleCat.Hom.hom (A.zMapFun 0)) y) = ∑ b, y b • kz A 0 b :=
    kIso_zMap_expand A h 0 y
  have hsum : (∑ b, x b • kz A 0 b) = (∑ b, y b • kz A 0 b) := by
    rw [← hx, ← hy, hxy]
  funext b₀
  have h2 := congrArg (fun z : kMod K 0 => z (sigmaZero A b₀)) hsum
  rw [kz_sum_apply A (x : Fin (C.dim 0) → ℤ) b₀, kz_sum_apply A (y : Fin (C.dim 0) → ℤ) b₀]
    at h2
  exact h2

/-- In degree `0` the atlas map reaches the whole level `(0, ∅)`. -/
theorem KMod_zero_empty_le_map (A : CellAtlas K P C) (h : A.BoundaryCompat) :
    KMod A 0 (∅ : Finset (Fin (C.dim 1))) 0 ≤ Submodule.map (A.zMapFun 0).hom ⊤ := by
  intro y hy
  rw [mem_KMod] at hy
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.mp (kSup_zero_empty_le_map A h hy)
  rw [Submodule.mem_map]
  refine ⟨x, Submodule.mem_top, ?_⟩
  have h1 : (ConcreteCategory.hom (kIso K 0).hom)
      ((ModuleCat.Hom.hom (A.zMapFun 0)) x) = (ConcreteCategory.hom (kIso K 0).hom) y := by
    change kzComp A x = (ConcreteCategory.hom (kIso K 0).hom) y
    exact hx
  have h2 := congrArg (fun z => (kIso K 0).inv z) h1
  rwa [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply,
       ← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply] at h2

/-- The value of the degree-`0` component of the level map, on an element of the
level `(0, ∅)`. -/
theorem levelMap_zero_apply (A : CellAtlas K P C) (h : A.BoundaryCompat)
    (x : (CSD (C := C) 0 (∅ : Finset (Fin (C.dim 1)))).chain.X 0) :
    (Subtype.val (((levelMap A h 0 (∅ : Finset (Fin (C.dim 1)))).f 0) x) : K.chainX 0)
      = (ModuleCat.Hom.hom (A.zMapFun 0)) (Subtype.val x) := by
  have hf : ∀ k, (CSD (C := C) 0 (∅ : Finset (Fin (C.dim 1)))).sub k ≤
      Submodule.comap ((A.zMap h).f k).hom ((KSD A 0 ∅).sub k) :=
    levelHf A h 0 ∅
  have h1 : (levelMap A h 0 (∅ : Finset (Fin (C.dim 1)))).f 0
      = (CSD (C := C) 0 (∅ : Finset (Fin (C.dim 1)))).restrictCptMap (KSD A 0 ∅) (A.zMap h)
          hf 0 := rfl
  conv_lhs => rw [h1]
  change Subtype.val (ModuleCat.Hom.hom
      ((CSD (C := C) 0 (∅ : Finset (Fin (C.dim 1)))).restrictCptMap (KSD A 0 ∅) (A.zMap h)
        hf 0) x) = (ModuleCat.Hom.hom (A.zMapFun 0)) (Subtype.val x)
  rw [Work.Subdivision.SubData.restrictCptMap_apply, LinearMap.restrict_apply]
  rfl

/-! ## The degreewise isomorphism and the base case -/

theorem isIso_levelMap_zero_f0 (A : CellAtlas K P C) (h : A.BoundaryCompat) :
    IsIso ((levelMap A h 0 (∅ : Finset (Fin (C.dim 1)))).f 0) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply zMapFun_zero_injective A h
    have h1 := levelMap_zero_apply A h x
    have h2 := levelMap_zero_apply A h y
    rw [← h1, ← h2]
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨w, -, hw⟩ := Submodule.mem_map.mp (KMod_zero_empty_le_map A h y.2)
    refine ⟨⟨w, ?_⟩, ?_⟩
    · rw [CSD_sub, CMod_eq_top_of_le (C := C) (n := 0) (k := 0) (le_refl 0)
        (∅ : Finset (Fin (C.dim 1)))]
      exact Submodule.mem_top
    · apply Subtype.ext
      rw [levelMap_zero_apply]
      exact hw

theorem isIso_levelMap_zero_succ (A : CellAtlas K P C) (h : A.BoundaryCompat) (k : ℕ) :
    IsIso ((levelMap A h 0 (∅ : Finset (Fin (C.dim 1)))).f (k + 1)) := by
  have hbot : (CSD (C := C) 0 (∅ : Finset (Fin (C.dim 1)))).chain.X (k + 1)
      = ModuleCat.of ℤ ↥(⊥ : Submodule ℤ ↥(C.toChainComplex.X (k + 1))) := by
    rw [Work.Subdivision.SubData.chain_X,
      show (CSD (C := C) 0 (∅ : Finset (Fin (C.dim 1)))).sub (k + 1) = ⊥ from
        CMod_zero_empty_eq_bot (C := C) (k := k + 1) (by omega)]
    try rfl
  have hbot' : (KSD A 0 (∅ : Finset (Fin (C.dim 1)))).chain.X (k + 1)
      = ModuleCat.of ℤ ↥(⊥ : Submodule ℤ ↥(K.chainX (k + 1))) := by
    rw [Work.Subdivision.SubData.chain_X,
      show (KSD A 0 (∅ : Finset (Fin (C.dim 1)))).sub (k + 1) = ⊥ from
        KMod_zero_empty_eq_bot A (k := k + 1) (by omega)]
    try rfl
  haveI : Subsingleton ((CSD (C := C) 0 (∅ : Finset (Fin (C.dim 1)))).chain.X (k + 1)) := by
    rw [hbot]
    exact ⟨fun a b => Subtype.ext (by
      have ha : (a : ↥(C.toChainComplex.X (k + 1))) = 0 := (Submodule.mem_bot ℤ).mp a.2
      have hb : (b : ↥(C.toChainComplex.X (k + 1))) = 0 := (Submodule.mem_bot ℤ).mp b.2
      rw [ha, hb])⟩
  haveI : Subsingleton ((KSD A 0 (∅ : Finset (Fin (C.dim 1)))).chain.X (k + 1)) := by
    rw [hbot']
    exact ⟨fun a b => Subtype.ext (by
      have ha : (a : ↥(K.chainX (k + 1))) = 0 := (Submodule.mem_bot ℤ).mp a.2
      have hb : (b : ↥(K.chainX (k + 1))) = 0 := (Submodule.mem_bot ℤ).mp b.2
      rw [ha, hb])⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩

theorem levelMap_zero {K : Work.DeltaHomology.DeltaCx} {P : Work.Subdivision.PolyCW} {C : Work.Certificates.FinChainCx} (A : Work.MbarHomology.CellAtlas K P C) (h : A.BoundaryCompat) : QuasiIso (Work.MbarHomology.CellAtlas.levelMap A h 0 (∅ : Finset (Fin (C.dim 1)))) := by
  haveI hcomp : ∀ k, IsIso ((levelMap A h 0 (∅ : Finset (Fin (C.dim 1)))).f k) := by
    intro k
    cases k with
    | zero => exact isIso_levelMap_zero_f0 A h
    | succ k => exact isIso_levelMap_zero_succ A h k
  haveI : IsIso (levelMap A h 0 (∅ : Finset (Fin (C.dim 1)))) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact quasiIso_of_isIso _

end CellAtlas

end

end Work.MbarHomology
