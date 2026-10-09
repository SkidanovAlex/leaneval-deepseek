import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.phi1_level_limit
import Submission.Work.SSGRoute.phi1_class_level
import Submission.Work.SSGRoute.zeta_idele_class_pairing
import Submission.Work.SSGRoute.ext_idele_shapiro
import Submission.Work.SSGRoute.brauer_single_place
import Submission.Work.SSGRoute.phi_pair_natural
import Submission.Work.SSGRoute.phi1_classIncl_compat
import Submission.Work.SSGRoute.phiTriv_mk0_eq
import Submission.Work.SSGRoute.phiPushClass
import Submission.Work.SSGRoute.addHom_extend_of_exponent
import Submission.Work.SSGRoute.E4R3.inflC_injective
import Submission.Work.SSGRoute.E4R3.kummer_dies_at_higher_level_clean
import Submission.NK.GlobalCFT.GaloisAction
import Submission.Work.SSGRoute.phi1_level_trivial_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

LEAD NOTE (re-dispatch): the previous prover declared this FALSE; the designer REBUTTED it (DESIGN_FIX.md 'Addendum: E4Ω ker κ'). The statement is TRUE and UNCHANGED.
Claim (b) was right: every c-family kills ker κ_L (κ_L h = h ∪ ζ ∈ Br(L/k)).
Claim (a) is false exactly on ker κ_L: the colimit V = H²(G_k, μ_p) embeds in Br(k), and so does H²(Gal(L/k), Lˣ). So κ_L h = 0 implies h DIES at a higher level, and compatibility forces lam(h) = 0. Example: h₀ = χ∪χ over ℚ(√2) maps to (2,−1), which splits since −1 = N(1+√2); h₀ dies at ℚ(√2, i).
Every compatible family therefore kills ker κ_L. That is R1 (Work.SSGRoute.phi0_family_vanish_of_local), from compatibility and injectivity of inflation on H²(C).
ROUTE (DESIGN_FIX.md E4Ω section, R1/R2/R3): lam factors through the Brauer localisation; extend by linear algebra; read off each a_v via Br(k_v)[p] ≅ ℤ/p and E8′ (brauer_single_place, PROVED); realise with R2 (zeta_idele_class_pairing, PROVED). E2 ext_idele_shapiro is also PROVED.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 4000000

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

/-- **The colimit map attached to a compatible family.**  Given a family
`lam : ∀ L, H²(Gal(L/k), 𝔽_p) → H²(Gal(L/k), C_L)` compatible with inflation (`hcompat`), the
universal property of the level colimit `V = colim_L H²(Gal(L/k), 𝔽_p)` produces a single additive
map `V ⟶ A = colim_L H²(Gal(L/k), C_L)`. -/
noncomputable def lamColim (p : ℕ) [Fact p.Prime] [IsGalois k K]
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

@[simp] theorem lamColim_of (p : ℕ) [Fact p.Prime] [IsGalois k K]
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2 →+ extH (classesK k L) 2)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L']
      [IsGalois k L'] (hLL : L ≤ L')
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflTrivIn (k := k) hLL (ZMod p) h))
    (L : Lvl k K Ω) (x : LevelCoh (k := k) (K := K) (Ω := Ω) p L) :
    lamColim (k := k) (K := K) (Ω := Ω) p lam hcompat
        (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x)
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L (lam L.1 x) :=
  LevelCohLimit.lift_of p _ _ L x



/-! ## The realisation map attached to a level-`K` coefficient class

For `c : 𝔽_p ⟶ C_K` the family `L ↦ (h ↦ phiTriv (mk₀ c) h)` over the levels `K ≤ L ≤ Ω` is
compatible with inflation (`classIncl` is compatible with towers of levels, `phi_pair_natural`),
so it produces a single additive map `Φ(c) : V →+ A` on the level colimit.  `Φ` is additive in `c`.
-/

namespace Phi0

variable [FiniteDimensional k K] [IsGalois k K]

/-- The values of `pushClass` on the generator: pushing a level-`K` class to `L` and evaluating at
`1 ∈ 𝔽_p` is the canonical inclusion `C_K → C_L` of the value at `1`. -/
theorem pushClass_hom_one (p : ℕ) [Fact p.Prime]
    {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K) :
    (pushClass k K L (ZMod p) c).hom (1 : ZMod p) = (classIncl k K L).hom (c.hom 1) := by
  simp only [pushClass, Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  rfl

/-- `pushClass` is transitive in the level: pushing a level-`K` class to `L` and then to `L'` is
pushing it directly to `L'`.  (Two morphisms `𝔽_p ⟶ C_{L'}` agree as soon as they agree on the
generator `1`; there the statement is the compatibility of the canonical inclusions
`classIncl_compat_apply`.) -/
theorem pushClass_trans (p : ℕ) [Fact p.Prime]
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
  rw [pushClass_hom_one, pushClass_hom_one, pushClass_hom_one]
  exact classIncl_compat_apply (k := k) (K := K) (L := L) (L₂ := L') (c.hom 1)

/-- The pairing family of a level-`K` coefficient class `c`: at the level `L` it is the level-`L`
Yoneda pairing `h ↦ h ∪ pushClass k K L c`. -/
noncomputable def pairFam (p : ℕ) [Fact p.Prime]
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

@[simp] theorem pairFam_apply (p : ℕ) [Fact p.Prime]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K)
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2) :
    pairFam (k := k) (K := K) (Ω := Ω) p c L h
      = phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c) h := rfl

/-- The pairing family of a level-`K` class is compatible with inflation along `L ≤ L'`. -/
theorem pairFam_compat (p : ℕ) [Fact p.Prime]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K) :
    ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
      (hLL : L ≤ L') (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      inflCIn (k := k) hLL (pairFam (k := k) (K := K) (Ω := Ω) p c L h)
        = pairFam (k := k) (K := K) (Ω := Ω) p c L'
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
    pushClass_trans (p := p) (k := k) (K := K) (L := ↥L) (L' := ↥L') c,
    ← phiTriv_mk₀_pushClass p k K ↥L' c
      (inflTriv (k := k) (K := ↥L) (L := ↥L') (ZMod p) h)]

/-- **The realisation map of a level-`K` coefficient class**: the additive map `V →+ A` induced by
the compatible family `h ↦ h ∪ c`. -/
noncomputable def phiColim (p : ℕ) [Fact p.Prime]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K) :
    LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω) :=
  lamColim (k := k) (K := K) (Ω := Ω) p (pairFam (k := k) (K := K) (Ω := Ω) p c)
    (pairFam_compat (k := k) (K := K) (Ω := Ω) p c)

@[simp] theorem phiColim_of (p : ℕ) [Fact p.Prime]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K)
    (L : Lvl k K Ω) (h : LevelCoh (k := k) (K := K) (Ω := Ω) p L) :
    phiColim (k := k) (K := K) (Ω := Ω) p c
        (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L h)
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
          (phiTriv (k := k) (K := K) (L := L.1) (ZMod p) (Abelian.Ext.mk₀ c) h) :=
  lamColim_of (k := k) (K := K) (Ω := Ω) p _ _ L h

/-- **The value of the pairing on the generator of `𝔽_p` is additive in the coefficient class.** -/
theorem phiTriv_mk₀_add (p : ℕ) [Fact p.Prime]
    {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L]
    (c c' : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K)
    (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2) :
    phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ (c + c')) h
      = phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c) h
        + phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c') h := by
  simp only [phiTriv, phiAt, levelPair, yonedaPair, extRes, Abelian.Ext.mk₀_add,
    Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add]

/-- **`phiColim` is additive in the coefficient class.** -/
theorem phiColim_add (p : ℕ) [Fact p.Prime]
    (c c' : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K) :
    phiColim (k := k) (K := K) (Ω := Ω) p (c + c')
      = phiColim (k := k) (K := K) (Ω := Ω) p c
        + phiColim (k := k) (K := K) (Ω := Ω) p c' := by
  apply LevelCohLimit.hom_ext (k := k) (K := K) (Ω := Ω) p
  intro L
  apply AddMonoidHom.ext
  intro h
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply, phiColim_of]
  rw [phiTriv_mk₀_add, map_add]

end Phi0


/-! ## The place of `k` under a place of `K`, and the local functionals `λ_v`

E4Ω is a statement about the *local* data of a compatible `p`-torsion family.  This section sets up
that data: the place `placeUnder w` of `k` under a place `w` of `K` (Galois-equivariant by
uniqueness of the place below), the Galois-invariant indicator `orbInd v` of the places of `K` over
a place `v` of `k`, the idèle class `cOf f` of the `μ_p`-idèle `(ζ^{f_v})_v` (R2,
`zeta_idele_class_pairing`), and the resulting *local functional*

  `lamV v : V →+ A`,   `lamV v x` = the `v`-component of the `p`-torsion functional realised by
  `cOf (δ_v)`,

where `V = colim_L H²(Gal(L/k),𝔽_p)` and `A = colim_L H²(Gal(L/k),C_L)`.
-/

namespace Phi0

variable [FiniteDimensional k K] [IsGalois k K]

/-- **The place of `k` under a place of `K`** (a choice; the value is unique). -/
noncomputable def placeUnder (w : NK.GlobalCFT.Place K) : NK.GlobalCFT.Place k :=
  Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := k) (L := K) w)

theorem placeUnder_liesOver (w : NK.GlobalCFT.Place K) :
    NK.GlobalCFT.Place.LiesOver w (placeUnder (k := k) (K := K) w) :=
  Classical.choose_spec (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := k) (L := K) w)

/-- **`placeUnder` is Galois-equivariant.** -/
theorem placeUnder_smul (σ : K ≃ₐ[k] K) (w : NK.GlobalCFT.Place K) :
    placeUnder (k := k) (K := K) (σ • w) = placeUnder (k := k) (K := K) w :=
  NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
    (placeUnder_liesOver (k := k) (K := K) (σ • w))
    ((NK.GlobalCFT.Place.liesOver_smul_iff (σ := σ) (w := w)
      (v := placeUnder (k := k) (K := K) w)).mpr (placeUnder_liesOver w))

/-- **The Galois-invariant indicator of the places of `K` over a place `v` of `k`.** -/
noncomputable def orbInd (p : ℕ) (v : NK.GlobalCFT.Place k) : NK.GlobalCFT.Place K → ZMod p := by
  classical
  exact fun w => if placeUnder (k := k) (K := K) w = v then 1 else 0

theorem orbInd_smul (p : ℕ) (v : NK.GlobalCFT.Place k) (σ : K ≃ₐ[k] K)
    (w : NK.GlobalCFT.Place K) :
    orbInd (k := k) (K := K) p v (σ • w) = orbInd (k := k) (K := K) p v w := by
  have h : placeUnder (k := k) (K := K) (σ • w) = placeUnder (k := k) (K := K) w :=
    placeUnder_smul (k := k) (K := K) (σ := σ) w
  unfold orbInd
  rw [h]

end Phi0

section RealiseMu

variable [FiniteDimensional k K] [IsGalois k K] [IsAlgClosed Ω]
  (p : ℕ) [Fact p.Prime] (ζ : k) (hζ : IsPrimitiveRoot ζ p)

/-- **The idèle class of the `μ_p`-idèle `(ζ^{f (placeUnder w)})_w` of `K`**: R2's class `c₀` of a
Galois-invariant `𝔽_p`-valued function of the places of `K`, here written for the functions
`f ∘ placeUnder`, `f : Place k → 𝔽_p`. -/
noncomputable def Phi0.cOfFun (f : NK.GlobalCFT.Place k → ZMod p) :
    Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K :=
  muClassHom p k K ζ hζ (fun w => f (Phi0.placeUnder (k := k) (K := K) w))
    (fun σ w => by simp only [Phi0.placeUnder_smul])

/-- **The local functional at a place `v` of `k`**: the functional `V →+ A` realised by the
`μ_p`-idèle which is `ζ` at the places of `K` over `v` and `1` elsewhere. -/
noncomputable def Phi0.lamV (v : NK.GlobalCFT.Place k) :
    LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω) := by
  classical
  exact Phi0.phiColim (k := k) (K := K) (Ω := Ω) p
    (Phi0.cOfFun (k := k) (K := K) p ζ hζ (fun v' => if v' = v then 1 else 0))


end RealiseMu

/-! ## `p`-torsion of the colimit and of the realisation -/

section PTorsion

variable [FiniteDimensional k K] [IsGalois k K] [IsAlgClosed Ω]

/-- **`V` has exponent `p`.** -/
theorem Phi0.levelCohLimit_smul_p (p : ℕ) [Fact p.Prime]
    (x : LevelCohLimit (k := k) (K := K) (Ω := Ω) p) : p • x = 0 := by
  refine LevelCohLimit.induction (k := k) (K := K) (Ω := Ω) p
    (C := fun x => p • x = 0) ?_ x
  intro L y
  show p • (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L y) = 0
  rw [← map_nsmul (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L) p y,
    extH_trivial_zmodp_smul_eq_zero p y, map_zero]

/-- **The realisation of any coefficient class is `p`-torsion** (the source `V` has exponent `p`). -/
theorem Phi0.phiColim_smul_p (p : ℕ) [Fact p.Prime]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K)
    (x : LevelCohLimit (k := k) (K := K) (Ω := Ω) p) :
    p • (Phi0.phiColim (k := k) (K := K) (Ω := Ω) p c x) = 0 := by
  rw [← map_nsmul (Phi0.phiColim (k := k) (K := K) (Ω := Ω) p c) p x,
    Phi0.levelCohLimit_smul_p (k := k) (K := K) (Ω := Ω) p x, map_zero]

end PTorsion


/-! ## The `p`-torsion subgroup -/

/-- The `p`-torsion subgroup `A[p]` of an abelian group. -/
def pTor (p : ℕ) (A : Type*) [AddCommGroup A] : AddSubgroup A where
  carrier := {y | p • y = 0}
  zero_mem' := by simp
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [smul_neg, hx, neg_zero]

@[simp] theorem mem_pTor {p : ℕ} {A : Type*} [AddCommGroup A] {y : A} :
    y ∈ pTor p A ↔ p • y = 0 := Iff.rfl

/-- The `n`-fold multiple in `A[p]` is the `n`-fold multiple in `A`. -/
theorem pTor_coe_nsmul {p : ℕ} {A : Type*} [AddCommGroup A] (y : ↥(pTor p A)) (n : ℕ) :
    ((n • y : ↥(pTor p A)) : A) = n • (y : A) := rfl

end Work.SSGRoute
