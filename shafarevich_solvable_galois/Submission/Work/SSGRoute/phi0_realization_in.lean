import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.phi1_level_limit
import Submission.Work.SSGRoute.phi1_class_level
import Submission.Work.SSGRoute.E4R3.inflC_injective
import Submission.Work.SSGRoute.phi_pair_natural
import Submission.Work.SSGRoute.phiPushClass
import Submission.Work.SSGRoute.phiAt_level_infl
import Submission.Work.SSGRoute.phi0_pairing_infl_eq_zero
import Submission.Work.SSGRoute.zeta_idele_class_pairing
import Submission.Work.SSGRoute.phi0_trivial_epi_in
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester): this file carries the E4Ω statement
`Work.SSGRoute.phi0_realization_in`, identical to `Work.SSGRoute.phi0_trivial_epi_in`.

# Analysis of E4Ω, and what is proved here

## 1. The colimit picture

Let `V := LevelCohLimit p = colim_{K ≤ L ≤ Ω} H²(Gal(L/k), 𝔽_p)` (`= Br(k)[p]`) and
`A := ClassLevelLimit = colim_{K ≤ L ≤ Ω} H²(Gal(L/k), C_L)`.

A family `lam` satisfying `hp` and `hcompat` gives one additive map
`lamColimIn p lam hcompat : V →+ A`; because inflation `H²(Gal(L/k),C_L) → H²(Gal(L'/k),C_{L'})` is
*injective* (`Work.SSGRoute.E4R3.inflC_injective`), the colimit maps `ClassLevelLimit.of L` are
injective (`ClassLevelLimit.of_injective` here), so a family is **determined by `lamColimIn`**.
`phi0_realization_in_of_lamColim_eq` converts the resulting single colimit identity
`lamColimIn lam = phiColimReal c` back into the levelwise conclusion of E4Ω.

## 2. The levelwise statement is false; the family statement is the one to prove

`Work.SSGRoute.phi_pair_natural` (PROVED) shows that the level-`L` pairing with a level-`L` class
`c` satisfies `inflC (h ∪ c) = (infl h) ∪ (push c)`; since `inflC` is injective, the level-`L`
pairing **kills** the classes that die at a higher level.  So a level-wise realisation statement
(`E4Ω.1`, `Chk384/Stmt.lean`) is false — the project's `DESIGN_FIX.md` records this — and E4Ω is a
statement about *compatible families*, not about single levels.

## 3. The route (R1 + linear algebra + local duality + R2)

* **R1** (`Work.SSGRoute.phi0_family_vanish_of_local`, PROVED) gives that `lam` kills the kernel of
  the localisation `Loc ∘ κ` (Hasse–Brauer–Noether + Kummer "dies at a higher level").
* Because the localisation lands in the *direct sum* `⊕_v Br(k_v)[p]` (a global Brauer class is
  ramified at finitely many places), a functional on it is `Σ_v a_v · pr_v` with `a : Place k → 𝔽_p`
  arbitrary — **no Albert–Brauer–Hasse–Noether is needed** for this; the extension of a functional
  from a subgroup is formal, and `Br(k_v)[p] ≅ ℤ/p`.
* **R2** (`Work.SSGRoute.zeta_idele_class_pairing`, PROVED) constructs the class `c₀ = cOfFunPlace a`
  of the `μ_p`-idèle `(ζ^{a w})_w` and identifies the `w'`-component of its pairing class with
  `(a w) • loc_{w'}(κ h)`.
* The **local functionals** `lamV v` (`phiColimReal` of the orbit-concentrated `μ_p`-idèle class,
  defined in this file) are the pieces out of which `Λ` is assembled:
  `Work.SSGRoute.phiColimReal_pairing_formula` (delegated; formal given R2 + Shapiro injectivity
  `Work.SSGRoute.ext_idele_shapiro`) gives
  `phiColimReal (cOfFunPlace a) = Σ_v a v • lamV v`.
* The remaining genuine arithmetic input is the **local nonvanishing criterion**: the level-`L`
  pairing of `h` with the orbit-`v`-concentrated `μ_p`-idèle class `lamV v` vanishes exactly when
  the Kummer class `κ_L h` is locally trivial at the places of `L` above `v`.  This is local Tate
  duality / non-degeneracy of the Hilbert-symbol pairing `Br(k_v)[p] × μ_p(k_v) → ℤ/p`, the
  documented missing layer of the project (`PT/localTatePairing_deg02.lean`,
  `PT/milne18_at_zero.lean`, `E7Fin`, the Poitou–Tate lane).

## 4. What is proved in this file

`classLevelMap_injective`, `ClassLevelLimit.of_injective`; `pushClass_eval_one_in`,
`pushClass_trans_in`; `lamColimIn`, `lamColimIn_of`; `pairingFamily`, `pairingFamily_compat`;
`placeUnder`, `orbInd`, `cOfFun`, `cOfFunPlace`, `phiColimReal`, `lamV`; and the reduction
`phi0_realization_in_of_lamColim_eq`.

`classLevelMap_injective` and `ClassLevelLimit.of_injective` are consumed by the sibling lanes
`LF/Descent`, `phi1_realization_triv`, `level_family_of_delta`, `phi1_mono_step_in`;
`phi0_realization_in_of_lamColim_eq` supplies the last step of the sibling E4 lane's proof (its
`phiColim` = this file's `phiColimReal`).
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option linter.unusedSectionVars false

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] [IsGalois k K]

/-- **The transition maps of the class-group level system are injective**:
inflation `H²(Gal(L/k),C_L) → H²(Gal(L'/k),C_{L'})` along `L ≤ L'` is injective
(`Work.SSGRoute.E4R3.inflC_injective`). -/
theorem classLevelMap_injective (L L' : Lvl k K Ω) (h : L ≤ L') :
    Function.Injective (classLevelMap (k := k) (K := K) (Ω := Ω) L L' h) := by
  intro x y hxy
  rw [classLevelMap_apply, classLevelMap_apply] at hxy
  letI : Algebra ↥L.1 ↥L'.1 := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower k ↥L.1 ↥L'.1 := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Work.SSGRoute.E4R3.inflC_injective k ↥L.1 ↥L'.1 hxy

/-- **The canonical maps of `A = colim_L H²(Gal(L/k), C_L)` are injective.**  (Their transition
maps are, by `classLevelMap_injective`; the colimit relation is `ClassLevelLimit.of_eq_zero_iff`.)
-/
theorem ClassLevelLimit.of_injective (L : Lvl k K Ω) :
    Function.Injective (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L) := by
  intro x y hxy
  have hsub : ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨L', hLL', hzero⟩ :=
    (ClassLevelLimit.of_eq_zero_iff (k := k) (K := K) (Ω := Ω) L (x - y)).mp hsub
  have hzero' : classLevelMap (k := k) (K := K) (Ω := Ω) L L' hLL' (x - y) = 0 := by
    rw [classLevelMap_apply]; exact hzero
  have hxy' : x - y = 0 :=
    classLevelMap_injective L L' hLL' (by rw [hzero', map_zero])
  exact sub_eq_zero.mp hxy'

/-! ## The colimit map of a compatible family

`lamColimIn` is the universal map `V = colim_L H²(Gal(L/k),𝔽_p) →+ A = colim_L H²(Gal(L/k),C_L)`
attached to a compatible family `lam`; `lamColimIn_of` computes it on the components.  (The same
construction is carried by `Work.SSGRoute.lamColim` in the E4 lane's file; it is reproduced here
under a private name so that this module does not depend on that lane's file.) -/

/-- **The colimit map attached to a compatible family.** -/
noncomputable def lamColimIn (p : ℕ) [Fact p.Prime] [IsGalois k K]
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2 →+ extH (classesK k L) 2)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L']
      [IsGalois k L'] (hLL : L ≤ L')
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflTrivIn (k := k) hLL (ZMod p) h)) :
    LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω) :=
  LevelCohLimit.lift p
    (fun L => (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L).comp (lam L.1))
    (fun L L' h x => by
      have h1 : classLevelMap (k := k) L L' h (lam L.1 x)
          = lam L'.1 (levelMap (k := k) (K := K) (Ω := Ω) p L L' h x) := by
        rw [classLevelMap_apply, levelMap_apply]
        exact hcompat L.1 L'.1 h x
      show ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L'
          (lam L'.1 (levelMap (k := k) (K := K) (Ω := Ω) p L L' h x))
        = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L (lam L.1 x)
      rw [← h1]
      exact ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) h (lam L.1 x))

@[simp] theorem lamColimIn_of (p : ℕ) [Fact p.Prime] [IsGalois k K]
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2 →+ extH (classesK k L) 2)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L']
      [IsGalois k L'] (hLL : L ≤ L')
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflTrivIn (k := k) hLL (ZMod p) h))
    (L : Lvl k K Ω) (x : LevelCoh (k := k) (K := K) (Ω := Ω) p L) :
    lamColimIn (k := k) (K := K) (Ω := Ω) p lam hcompat
        (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x)
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L (lam L.1 x) :=
  LevelCohLimit.lift_of p _ _ L x

/-! ## Transitivity of `pushClass` in the level -/

/-- **The value of `pushClass` on the generator**: pushing a level-`K` class to a level `L` and
evaluating at `1 ∈ 𝔽_p` gives the canonical inclusion `C_K → C_L` of the value at `1`. -/
theorem pushClass_eval_one_in (p : ℕ) [Fact p.Prime]
    {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K) :
    (pushClass k K L (ZMod p) c).hom (1 : ZMod p) = (classIncl k K L).hom (c.hom 1) := by
  simp only [pushClass, Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rfl

/-- **`pushClass` is transitive in the level**: pushing a level-`K` class first to `L` and then to
`L'` is pushing it directly to `L'`. -/
theorem pushClass_trans_in (p : ℕ) [Fact p.Prime]
    {k K L L' : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Field L'] [NumberField L']
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra k L'] [Algebra K L'] [IsScalarTower k K L']
    [Algebra L L'] [IsScalarTower k L L'] [IsScalarTower K L L']
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    [FiniteDimensional k L'] [IsGalois k L']
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K) :
    pushClass k L L' (ZMod p) (pushClass k K L (ZMod p) c) = pushClass k K L' (ZMod p) c := by
  haveI : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite k L L'
  haveI : IsGalois L L' := IsGalois.tower_top_of_isGalois k L L'
  apply zmod_trivial_hom_ext
  rw [pushClass_eval_one_in, pushClass_eval_one_in, pushClass_eval_one_in]
  exact classIncl_compat_apply (k := k) (K := K) (L := L) (L₂ := L') (c.hom 1)

/-! ## The pairing family of a level-`K` coefficient class -/

/-- **The pairing family `h ↦ h ∪ c` of a level-`K` coefficient class `c`.**  At the level `L` it is
the level-`L` Yoneda pairing with `pushClass k K L c`. -/
noncomputable def pairingFamily (p : ℕ) [Fact p.Prime]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K) :
    ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2 →+ extH (classesK k L) 2 :=
  fun L _instNF _instFD _instGal =>
    { toFun := fun h => phiTriv (k := k) (K := K) (L := L) (ZMod p)
        (Abelian.Ext.mk₀ c) h
      map_zero' := by
        simp only [phiTriv, phiAt, levelPair, yonedaPair]
        rw [Abelian.Ext.zero_comp, Abelian.Ext.zero_comp]
      map_add' := fun h₁ h₂ => by
        simp only [phiTriv, phiAt, levelPair, yonedaPair]
        rw [Abelian.Ext.add_comp, Abelian.Ext.add_comp] }

/-- **The pairing family of a level-`K` class is compatible with inflation.** -/
theorem pairingFamily_compat (p : ℕ) [Fact p.Prime]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K) :
    ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
      (hLL : L ≤ L') (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      inflCIn (k := k) hLL (pairingFamily (k := k) (K := K) (Ω := Ω) p c L h)
        = pairingFamily (k := k) (K := K) (Ω := Ω) p c L'
            (inflTrivIn (k := k) hLL (ZMod p) h) := by
  intro L _instNF _instFD _instGal L' _instNF' _instFD' _instGal' hLL h
  letI : Algebra ↥L ↥L' := (IntermediateField.inclusion hLL).toAlgebra
  haveI : IsScalarTower k ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  show inflC (k := k) (K := ↥L) (L := ↥L')
      (phiTriv (k := k) (K := K) (L := ↥L) (ZMod p) (Abelian.Ext.mk₀ c) h)
    = phiTriv (k := k) (K := K) (L := ↥L') (ZMod p) (Abelian.Ext.mk₀ c)
        (inflTriv (k := k) (K := ↥L) (L := ↥L') (ZMod p) h)
  rw [phiTriv_mk₀_pushClass p k K ↥L c h,
    phi_pair_natural p k ↥L ↥L' (pushClass k K ↥L (ZMod p) c) h,
    pushClass_trans_in (p := p) (k := k) (K := K) (L := ↥L) (L' := ↥L') c,
    ← phiTriv_mk₀_pushClass p k K ↥L' c
      (inflTriv (k := k) (K := ↥L) (L := ↥L') (ZMod p) h)]

/-! ## The local functionals `lamV v`

E4Ω is a statement about the *local* data of a compatible `p`-torsion family.  This section sets up
that data: the place `placeUnder w` of `k` under a place `w` of `K` (Galois-equivariant, by
uniqueness of the place below), the `Gal(K/k)`-invariant indicator `orbInd v` of the places of `K`
above a place `v` of `k`, the idèle class `cOfFun a` of the `μ_p`-idèle `(ζ^{a w})_w` of `K`
(R2, `Work.SSGRoute.zeta_idele_class_pairing`), and the resulting *local functional*

  `lamV v : V →+ A`  —  the `p`-torsion functional realised by the class of the `μ_p`-idèle which
  is `ζ` at the places of `K` above `v` and `1` elsewhere.

`Work.SSGRoute.local_functionals_span` (delegated) is the arithmetic content of E4Ω: every
`p`-torsion functional `V →+ A` is a finite linear combination of the `lamV v`.  Combined with the
pairing formula `Work.SSGRoute.zeta_idele_class_pairing` (R2, PROVED) — which identifies the level
values of `lamV v` with the local components `a w • loc(κ h)` — this gives E4Ω. -/

namespace Phi0Real

variable [FiniteDimensional k K]

/-- **The place of `k` under a place of `K`** (a choice; the value is unique). -/
noncomputable def placeUnder (w : NK.GlobalCFT.Place K) : NK.GlobalCFT.Place k :=
  Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := k) (L := K) w)

theorem placeUnder_liesOver (w : NK.GlobalCFT.Place K) :
    NK.GlobalCFT.Place.LiesOver w (placeUnder (k := k) (K := K) w) :=
  Classical.choose_spec
    (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := k) (L := K) w)

/-- **`placeUnder` is `Gal(K/k)`-equivariant** (the place below is unique). -/
theorem placeUnder_smul (σ : K ≃ₐ[k] K) (w : NK.GlobalCFT.Place K) :
    placeUnder (k := k) (K := K) (σ • w) = placeUnder (k := k) (K := K) w :=
  NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
    (placeUnder_liesOver (k := k) (K := K) (σ • w))
    ((NK.GlobalCFT.Place.liesOver_smul_iff (σ := σ) (w := w)
      (v := placeUnder (k := k) (K := K) w)).mpr (placeUnder_liesOver w))

/-- **The `Gal(K/k)`-invariant indicator of the places of `K` above a place `v` of `k`.** -/
noncomputable def orbInd (p : ℕ) (v : NK.GlobalCFT.Place k) :
    NK.GlobalCFT.Place K → ZMod p := by
  classical
  exact fun w => if placeUnder (k := k) (K := K) w = v then 1 else 0

theorem orbInd_smul (p : ℕ) (v : NK.GlobalCFT.Place k) (σ : K ≃ₐ[k] K)
    (w : NK.GlobalCFT.Place K) :
    orbInd (k := k) (K := K) p v (σ • w) = orbInd (k := k) (K := K) p v w := by
  classical
  show (if placeUnder (k := k) (K := K) (σ • w) = v then 1 else 0)
    = (if placeUnder (k := k) (K := K) w = v then 1 else 0)
  rw [placeUnder_smul]

end Phi0Real

section Realise

variable [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime] (ζ : k) (hζ : IsPrimitiveRoot ζ p)

/-- **The idèle class of the `μ_p`-idèle `(ζ^{a w})_w` of `K`** — R2's class `c₀`, attached to a
`Gal(K/k)`-invariant `a : Place K → 𝔽_p`. -/
noncomputable def cOfFun (a : NK.GlobalCFT.Place K → ZMod p)
    (ha : ∀ (σ : K ≃ₐ[k] K) w, a (σ • w) = a w) :
    Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K :=
  Classical.choose (zeta_idele_class_pairing (k := k) (K := K) (Ω := Ω) p ζ hζ a ha)

/-- The μ_p-idèle class of a function of the places of `k`, pulled back to the places of `K`. -/
noncomputable def cOfFunPlace (a : NK.GlobalCFT.Place k → ZMod p) :
    Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K :=
  cOfFun (k := k) (K := K) (Ω := Ω) p ζ hζ
    (fun w => a (Phi0Real.placeUnder (k := k) (K := K) w))
    (fun σ w => by
      show a (Phi0Real.placeUnder (k := k) (K := K) (σ • w))
        = a (Phi0Real.placeUnder (k := k) (K := K) w)
      rw [Phi0Real.placeUnder_smul])


/-- **The colimit functional of a level-`K` coefficient class**: `lamColimIn` of its pairing
family.  This is the map `c ↦ (h ↦ h ∪ c)` on the colimit `V = colim_L H²(Gal(L/k),𝔽_p)`. -/
noncomputable def phiColimReal (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K) :
    LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω) :=
  lamColimIn (k := k) (K := K) (Ω := Ω) p
    (pairingFamily (k := k) (K := K) (Ω := Ω) p c)
    (pairingFamily_compat (k := k) (K := K) (Ω := Ω) p c)

@[simp] theorem phiColimReal_of (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K)
    (L : Lvl k K Ω) (h : LevelCoh (k := k) (K := K) (Ω := Ω) p L) :
    phiColimReal (k := k) (K := K) (Ω := Ω) p c
        (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L h)
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
          (phiTriv (k := k) (K := K) (L := L.1) (ZMod p) (Abelian.Ext.mk₀ c) h) :=
  lamColimIn_of (k := k) (K := K) (Ω := Ω) p _ _ L h

/-- **The local functional `lamV v`**: the `p`-torsion functional `V →+ A` realised by the class
of the `μ_p`-idèle which is `ζ` at the places of `K` above `v` and `1` elsewhere. -/
noncomputable def lamV (v : NK.GlobalCFT.Place k) :
    LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω) :=
  phiColimReal (k := k) (K := K) (Ω := Ω) p
    (cOfFun (k := k) (K := K) (Ω := Ω) p ζ hζ (Phi0Real.orbInd (k := k) (K := K) p v)
      (fun σ w => Phi0Real.orbInd_smul (k := k) (K := K) p v σ w))

@[simp] theorem lamV_of (v : NK.GlobalCFT.Place k) (L : Lvl k K Ω)
    (h : LevelCoh (k := k) (K := K) (Ω := Ω) p L) :
    lamV (k := k) (K := K) (Ω := Ω) p ζ hζ v
        (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L h)
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
          (phiTriv (k := k) (K := K) (L := L.1) (ZMod p)
            (Abelian.Ext.mk₀ (cOfFun (k := k) (K := K) (Ω := Ω) p ζ hζ
              (Phi0Real.orbInd (k := k) (K := K) p v)
              (fun σ w => Phi0Real.orbInd_smul (k := k) (K := K) p v σ w))) h) :=
  phiColimReal_of (k := k) (K := K) (Ω := Ω) p _ L h

end Realise

/-! ## The reduction of E4Ω to the colimit identity -/

/-- **E4Ω follows from the single colimit identity.**  If for some level-`K` coefficient class `c`
the functional `lamColim` of the family `lam` agrees with the functional of the pairing family of
`c` on `V = colim_L H²(Gal(L/k), 𝔽_p)`, then the levelwise identity
`phiTriv (mk₀ c) h = lam L h` holds at every level.  (This uses the injectivity of the colimit maps
`ClassLevelLimit.of L`, `ClassLevelLimit.of_injective`.) -/
theorem phi0_realization_in_of_lamColim_eq (p : ℕ) [Fact p.Prime]
    (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2 →+ extH (classesK k L) 2)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
      (hLL : L ≤ L')
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflTrivIn (k := k) hLL (ZMod p) h))
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K)
    (hc : lamColimIn (k := k) (K := K) (Ω := Ω) p lam hcompat
      = lamColimIn (k := k) (K := K) (Ω := Ω) p
          (pairingFamily (k := k) (K := K) (Ω := Ω) p c)
          (pairingFamily_compat (k := k) (K := K) (Ω := Ω) p c)) :
    ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c) h = lam L h := by
  intro L _instNF _instFD _instGal h
  let Lv : Lvl k K Ω := ⟨L, inferInstance, inferInstance, inferInstance⟩
  have key : ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) Lv
        (phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c) h)
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) Lv (lam L h) := by
    have h1 : lamColimIn (k := k) (K := K) (Ω := Ω) p lam hcompat
          (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p Lv h)
        = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) Lv (lam L h) :=
      lamColimIn_of (k := k) (K := K) (Ω := Ω) p lam hcompat Lv h
    have h2 : lamColimIn (k := k) (K := K) (Ω := Ω) p
          (pairingFamily (k := k) (K := K) (Ω := Ω) p c)
          (pairingFamily_compat (k := k) (K := K) (Ω := Ω) p c)
          (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p Lv h)
        = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) Lv
            (pairingFamily (k := k) (K := K) (Ω := Ω) p c Lv h) :=
      lamColimIn_of (k := k) (K := K) (Ω := Ω) p
        (pairingFamily (k := k) (K := K) (Ω := Ω) p c)
        (pairingFamily_compat (k := k) (K := K) (Ω := Ω) p c) Lv h
    rw [← h1, hc, h2]
    rfl
  exact ClassLevelLimit.of_injective Lv key


/-! ## The target -/

/-- **E4Ω: base case `φ⁰` onto for `M = 𝔽_p` (trivial action), `μ_p ⊆ k`.**

A `p`-torsion family of functionals `lam_L : H²(Gal(L/k), 𝔽_p) →+ H²(Gal(L/k), C_L)` over the
levels `K ≤ L ≤ Ω` of a fixed algebraically closed `Ω ⊇ K`, compatible with inflation along
inclusions of levels, is the cup product with one `c ∈ Hom_G(𝔽_p, C_K)`, i.e. `φ⁰(c) = lam`.

This is the statement of `Work.SSGRoute.phi0_trivial_epi_in`, restated under a new name so that
the E5s lane (`Work.SSGRoute.exists_realization_of_delta_lam`) can consume it.  The statement is
identical, and the proof below is the sibling lane's theorem — the fleet proves E4Ω once, in the
`phi0_trivial_epi_in` lane, and this file carries the restated name together with the formal
reduction `phi0_realization_in_of_lamColim_eq` (the step from the colimit identity to the levelwise
conclusion) and the local-functional vocabulary `lamV` used by the `lamV_*` lemmas.

Route (the lead's R1/R2/R3 design, `DESIGN_FIX.md` section "E4Ω"). With
`κ_L : H²(Gal(L/k),𝔽_p) → H²(Gal(L/k),Lˣ)` the push-along of coefficients along `𝔽_p ≅ μ_p ⊆ Lˣ`,
compatibility of `lam` across levels forces `lam` to vanish on `{h : κ_L h locally trivial}`
(`Work.SSGRoute.phi0_family_vanish_of_local`, PROVED: Hasse–Brauer–Noether + Kummer "dies at a
higher level" + injectivity of inflation). Hence `lam` factors through the local Brauer group
`⊕_v Br(k_v)[p]`; extend by linear algebra (`Work.SSGRoute.addHom_extend_of_exponent`) and read off
one coefficient `a_v ∈ ℤ/p` per place (`Br(k_v)[p] ≅ ℤ/p`,
`NK.…natCard_groupCohomology_two_units_local_eq_finrank`; injectivity of `ι_v` is E8′
`Work.SSGRoute.brauer_single_place`, PROVED), giving a `Gal(K/k)`-invariant
`a : Place K → ZMod p`. The class `c₀` of the idèle `(ζ^{a w})_w` realises it
(`Work.SSGRoute.zeta_idele_class_pairing`, PROVED), and `Work.SSGRoute.ext_idele_shapiro` (PROVED)
compares the level values. -/
theorem phi0_realization_in (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2 →+ extH (classesK k L) 2)
    (hp : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2), p • lam L h = 0)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L] (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L'] (hLL : L ≤ L')
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflTrivIn (k := k) hLL (ZMod p) h)) :
    ∃ c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K,
      ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
        phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c) h = lam L h :=
  Work.SSGRoute.phi0_trivial_epi_in p k K Ω ζ hζ lam hp hcompat

end Work.SSGRoute
