import Mathlib
import Submission.Work.DSAMR.Defs

namespace Work.DSAMR

universe u

open CategoryTheory

/-! ### Transport of `I • ⊤` along `W`-linear maps and isomorphisms -/

/-- A `W`-linear map sends `I • ⊤` into `I • ⊤`. -/
theorem map_mem_smul_top {W : Type u} [CommRing W] {M N : Type u} [AddCommGroup M] [Module W M]
    [AddCommGroup N] [Module W N] (I : Ideal W) (f : M →ₗ[W] N) {x : M}
    (hx : x ∈ I • (⊤ : Submodule W M)) : f x ∈ I • (⊤ : Submodule W N) := by
  refine Submodule.smul_induction_on hx (fun r hr n _ => ?_) (fun a b ha hb => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr trivial
  · rw [map_add]; exact Submodule.add_mem _ ha hb

/-- An isomorphism of `W`-modules maps `I • ⊤` onto `I • ⊤`; hence membership transfers. -/
theorem iso_mem_smul_top_iff {W : Type u} [CommRing W] {M N : ModuleCat.{u} W} (I : Ideal W)
    (φ : M ≅ N) {x : M} : (φ.hom x ∈ I • (⊤ : Submodule W N)) ↔ x ∈ I • (⊤ : Submodule W M) := by
  constructor
  · intro h
    have h1 : φ.inv.hom (φ.hom x) ∈ I • (⊤ : Submodule W M) := map_mem_smul_top I φ.inv.hom h
    rwa [Iso.hom_inv_id_apply] at h1
  · intro h
    exact map_mem_smul_top I φ.hom.hom h

/-- **Transport of the almost acyclicity to the `ℤ`-indexed extension.**

`K` is a cochain complex of `W`-modules indexed by `ℕ` (as produced by `M5c`), `eK : W → K⁰` a
coaugmentation satisfying the frozen `DSMap.Mix2.AlmostAcyc` conditions, and `K' := K.extend
ComplexShape.embeddingUpNat` is the `ℤ`-indexed extension (`K'.X i = 0` for `i < 0`,
`K'.X i ≅ K.X i` for `i ≥ 0` via `K.extendXIso`, and `K'.d i j` is the conjugate of `K.d i j` by
these isomorphisms, `HomologicalComplex.extend_d_eq`).  With `e' := eK ≫ (K.extendXIso …).inv`
(the coaugmentation transported to the extended complex), the three `Work.DSAMR.AlmostAcycZ`
conditions hold for `(K', e')`.

This is the bridge between the frozen (ℕ-indexed) hypothesis of `modSplit_of_almostAcyc` and the
`ℤ`-indexed form in which the truncation/homotopy argument (`exists_coaug_lift`) is carried out.

Hints.  `K.extendXIso ComplexShape.embeddingUpNat (h : embeddingUpNat.f n = n') : K'.X n' ≅ K.X n`
with `embeddingUpNat.f n = (n : ℤ)`.  Membership in `I • ⊤` transfers along these `W`-linear
isomorphisms (`Submodule.map`/`LinearEquiv`-style: an iso maps `I • ⊤` onto `I • ⊤`).  For the
differentials use `HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat (i := n) (i := n+1)`
(followed by `Iso.inv_hom_id_assoc`/`Iso.hom_inv_id_apply`).  The index casts `((n+1 : ℕ) : ℤ) =
(n : ℤ) + 1` come from `Nat.cast_add`, `Nat.cast_one`. -/
theorem almostAcycZ_extend {W : Type u} [CommRing W] (ϖ : ℕ → W) (I : Ideal W)
    (K : CochainComplex (ModuleCat.{u} W) ℕ) (eK : ModuleCat.of W W ⟶ K.X 0)
    (hK : DSMap.Mix2.AlmostAcyc ϖ I K eK) :
    Work.DSAMR.AlmostAcycZ ϖ I (K.extend ComplexShape.embeddingUpNat)
      (CategoryTheory.CategoryStruct.comp eK
        (K.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).inv) := by
  let K' : CochainComplex (ModuleCat.{u} W) ℤ := K.extend ComplexShape.embeddingUpNat
  let φ0 : K'.X 0 ≅ K.X 0 := K.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl
  change AlmostAcycZ ϖ I K' (eK ≫ φ0.inv)
  refine ⟨?_, ?_, ?_⟩
  · -- condition (1): almost injectivity of `e`
    intro w hw k
    have hw' : φ0.inv.hom (eK.hom w) ∈ I • (⊤ : Submodule W (K'.X 0)) := hw
    have h2 : eK.hom w ∈ I • (⊤ : Submodule W (K.X 0)) := by
      have h := (iso_mem_smul_top_iff I φ0).mpr hw'
      rwa [Iso.inv_hom_id_apply] at h
    exact hK.1 w h2 k
  · -- condition (2): almost surjectivity of `e` on `H⁰`
    intro z hz k
    let φ1 : K'.X 1 ≅ K.X 1 := K.extendXIso ComplexShape.embeddingUpNat (i := 1) rfl
    have hd : (K'.d 0 1).hom z = φ1.inv.hom ((K.d 0 1).hom (φ0.hom.hom z)) := by
      rw [show (K'.d 0 1) = φ0.hom ≫ K.d 0 1 ≫ φ1.inv from
        HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat (i := 0) (j := 1) rfl rfl]
      simp [ModuleCat.hom_comp]
    have hz' : (K.d 0 1).hom (φ0.hom.hom z) ∈ I • (⊤ : Submodule W (K.X 1)) := by
      have hh : φ1.inv.hom ((K.d 0 1).hom (φ0.hom.hom z)) ∈ I • (⊤ : Submodule W (K'.X 1)) := by
        rw [← hd]; exact hz
      have h := (iso_mem_smul_top_iff I φ1).mpr hh
      rwa [Iso.inv_hom_id_apply] at h
    obtain ⟨w, hw⟩ := hK.2.1 (φ0.hom.hom z) hz' k
    refine ⟨w, ?_⟩
    have heq : ϖ k • z - (eK ≫ φ0.inv).hom w = φ0.inv.hom (ϖ k • φ0.hom.hom z - eK.hom w) := by
      have e1 : (eK ≫ φ0.inv).hom w = φ0.inv.hom (eK.hom w) := rfl
      have e2 : ϖ k • z = φ0.inv.hom (ϖ k • φ0.hom.hom z) := by
        conv_lhs => rw [← Iso.hom_inv_id_apply φ0 z]
        rw [map_smul]
      rw [e1, e2, ← map_sub]
    rw [heq]
    exact map_mem_smul_top I φ0.inv.hom hw
  · -- condition (3): almost acyclicity in degrees `≥ 1`
    intro q z hz k
    let hq : ComplexShape.embeddingUpNat.f q = (q:ℤ) := by simp [ComplexShape.embeddingUpNat_f]
    let hq1 : ComplexShape.embeddingUpNat.f (q+1) = (q:ℤ)+1 := by
      simp [ComplexShape.embeddingUpNat_f]
    let hq2 : ComplexShape.embeddingUpNat.f (q+2) = (q:ℤ)+2 := by
      simp [ComplexShape.embeddingUpNat_f]
    let φq : K'.X (q:ℤ) ≅ K.X q := K.extendXIso ComplexShape.embeddingUpNat (i := q) hq
    let φq1 : K'.X ((q:ℤ)+1) ≅ K.X (q+1) :=
      K.extendXIso ComplexShape.embeddingUpNat (i := q+1) hq1
    let φq2 : K'.X ((q:ℤ)+2) ≅ K.X (q+2) :=
      K.extendXIso ComplexShape.embeddingUpNat (i := q+2) hq2
    have hd2 : (K'.d ((q:ℤ)+1) ((q:ℤ)+2)).hom z =
        φq2.inv.hom ((K.d (q+1) (q+2)).hom (φq1.hom.hom z)) := by
      rw [show (K'.d ((q:ℤ)+1) ((q:ℤ)+2)) = φq1.hom ≫ K.d (q+1) (q+2) ≫ φq2.inv from
        HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat (i := q+1) (j := q+2) hq1 hq2]
      simp [ModuleCat.hom_comp]
    have hz' : (K.d (q+1) (q+2)).hom (φq1.hom.hom z) ∈ I • (⊤ : Submodule W (K.X (q+2))) := by
      have hh : φq2.inv.hom ((K.d (q+1) (q+2)).hom (φq1.hom.hom z)) ∈
          I • (⊤ : Submodule W (K'.X ((q:ℤ)+2))) := by
        rw [← hd2]; exact hz
      have h := (iso_mem_smul_top_iff I φq2).mpr hh
      rwa [Iso.inv_hom_id_apply] at h
    obtain ⟨y₀, hy⟩ := hK.2.2 q (φq1.hom.hom z) hz' k
    refine ⟨φq.inv.hom y₀, ?_⟩
    have heq : ϖ k • z - (K'.d (q:ℤ) ((q:ℤ)+1)).hom (φq.inv.hom y₀) =
        φq1.inv.hom (ϖ k • φq1.hom.hom z - (K.d q (q+1)).hom y₀) := by
      have h2 : (K'.d (q:ℤ) ((q:ℤ)+1)).hom (φq.inv.hom y₀) =
          φq1.inv.hom ((K.d q (q+1)).hom y₀) := by
        rw [show (K'.d (q:ℤ) ((q:ℤ)+1)) = φq.hom ≫ K.d q (q+1) ≫ φq1.inv from
          HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat (i := q) (j := q+1) hq hq1]
        simp [ModuleCat.hom_comp, Iso.inv_hom_id_apply]
      have h3 : ϖ k • z = φq1.inv.hom (ϖ k • φq1.hom.hom z) := by
        conv_lhs => rw [← Iso.hom_inv_id_apply φq1 z]
        rw [map_smul]
      rw [h2, h3, ← map_sub]
    rw [heq]
    exact map_mem_smul_top I φq1.inv.hom hy

end Work.DSAMR
