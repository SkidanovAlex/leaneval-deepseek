import Mathlib
import Submission.Work.SSGRoute.PT.G1plusOwn.levelFree
import Submission.Work.SSGRoute.PT.G1plusOwn.levelRealization
import Submission.Work.SSGRoute.PT.G1plusOwn.finZH_surjective_own
import Submission.Work.SSGRoute.local_duality_ext_in
import Submission.Work.SSGRoute.local_ext_h1_bridge
import Submission.Work.SSGRoute.Z8.levelPair_vanish_of_vanish_closure
import Submission.Work.SSGRoute.PT.g1plus_iota
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.PT.G1plusLevelClauses
import Submission.Work.SSGRoute.PT.g1plus_finHalf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct Pointwise
open SSGRoute.PTExt CategoryTheory

namespace Work.SSGRoute.PT.G1plusOwn

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Clause (4)-left of `G1⁺`: perfectness of the finite half in the first variable

The local pairing at a finite place `A` (`pair (decomp k A)`, given abstractly with its value
formula `hpair` in terms of the local dictionary `βl`) is perfect in its *first* variable: a
locally constant `M`-cocycle `a` which pairs to zero with every locally constant `M^∨(1)`-cocycle
is a coboundary on `decomp k A`.

Route.  Contrapositive-free form: by the kernel clause `hβl_ker` of the dictionary it suffices to
show `βl A hA a = 0`.  Clause (i) of `Work.SSGRoute.local_duality_ext_in` (no left kernel of the
level pairing over *all* levels) reduces this to the vanishing, at every level `L ≥ K` and every
class `hc ∈ H¹(D_{w'}, M^∨(1))`, of `levelPair (finZF) (finZI) (βl A hA a) hc`.  At such a level
`hc` is `PT.finZH` of a locally constant cocycle `b` factoring through `L`
(`PT.G1pOwn.finZH_surjective_own`), and the value formula `hpair` together with the hypothesis `h`
turns the pairing into `pair (decomp k A) a b = 0`.  The class `βl A hA a` is `p`-torsion
(`hβl_add`), and `χ` (`hχinj`) and `iota` (`PT.iota_injective_of_ptorsion`) are injective on
`p`-torsion, so the level class itself vanishes.  Finally the canonical family at the level `L` is
transported to the abstract levels of clause (i) by `vanishAbstract_of_canonical`
(`Z8.levelPair_vanish_of_vanish_closure` plus `levelRealization`).
-/

/-- The `𝔽_p`-dual of `M ⊗ T` is finite (the `[Finite ·]` input at the Tate dual
`M^∨(1) = DualMod p (M ⊗ T)`). -/
theorem g1l_finite_dualMod_tensor (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [Finite M] :
    Finite (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) := by
  haveI : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (R := ZMod p) (M := T) (by rw [hT.1]; exact Nat.one_pos)
  let u : T ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.ofFinrankEq (R := ZMod p) T (ZMod p) (by rw [hT.1, Module.finrank_self])
  haveI hTfin : Finite T := Finite.of_injective u u.injective
  let isoE : M ≃ₗ[ZMod p] (M ⊗[ZMod p] T) :=
    (TensorProduct.rid (ZMod p) M).symm.trans
      ((TensorProduct.congr (LinearEquiv.refl (ZMod p) M) u).symm)
  haveI hMT : Finite (M ⊗[ZMod p] T) := Finite.of_injective isoE.symm isoE.symm.injective
  exact Finite.of_injective
    (fun f : Work.SSGRoute.DualMod p (M ⊗[ZMod p] T) => (f : (M ⊗[ZMod p] T) → ZMod p))
    (fun f g h => LinearMap.ext (fun x => congrFun h x))

/-- **The value of the local dictionary at a `p`-torsion cocycle is `p`-torsion.**  `β` is additive
on locally constant cocycles (`hadd`) and kills `0`; the coefficient module `M` is a
`ZMod p`-module, so `p • a = 0`. -/
theorem g1l_nsmul_beta_eq_zero
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    {V : Type} [AddCommGroup V] (β : ((Ω ≃ₐ[k] Ω) → M) → V)
    (A : ValuationSubring Ω)
    (hadd : ∀ b b' : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      β (b + b') = β b + β b')
    (h0 : β 0 = 0)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hla : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) :
    p • β a = 0 := by
  have hsm : ∀ n : ℕ, β (n • a) = n • β a := by
    intro n
    induction n with
    | zero => rw [zero_smul, zero_smul]; exact h0
    | succ n ih =>
      rw [add_nsmul, one_smul,
        hadd (n • a) a (Work.SSGRoute.PT.isCocycleOn_nsmul _ _ a n ha)
          (Work.SSGRoute.PT.isLocConstOn_nsmul _ a n hla) ha hla,
        ih, add_nsmul, one_smul]
  have hp : p • a = (0 : (Ω ≃ₐ[k] Ω) → M) := by
    funext σ
    exact Work.SSGRoute.PT.nsmul_eq_zero_of_zmod' p (a σ)
  rw [← hsm p, hp, h0]

/-- **The canonical family at the place `A`.**  For every level `L ≥ K` through which the place
under `A` is defined, the level pairing of the local dictionary class `βl A hA a` with *every*
class of `H¹(D_{w'}, M^∨(1))` vanishes.  The class is `PT.finZH` of a locally constant cocycle `b`
factoring through `L`, and the value formula `hpair` plus the vanishing hypothesis `h` give the
result because `χ` and `iota` are injective on `p`-torsion and `βl A hA a` is `p`-torsion. -/
theorem g1l_canonical_family
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → χ L hKL u = 0 → u = 0)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (βl : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ((Ω ≃ₐ[k] Ω) → M) →
        CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1)
    (hβl_add : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (b b' : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      βl A hA (b + b') = βl A hA b + βl A hA b')
    (hβl_ker : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
        (b : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (βl A hA b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
      ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hpair : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
        (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        pair (SSGRoute.decomp k A) a b =
          χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
              (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
              (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hla : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (h : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
      pair (SSGRoute.decomp k A) a b = 0) :
    ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (hKL : K ≤ L),
      letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
      letI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      letI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      ∀ (hc : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.PT.finZF hKL A hA)
        (Rep.res (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))) 1),
      SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
        (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a) hc = 0 := by
  classical
  intro L _ _ _ hKL hc
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- ## the class `hc` is realised by a locally constant cocycle on `decomp k A`
  obtain ⟨b, b₀, hb_coc, hb_lc, hb₀fac, hfinZH⟩ :=
    finZH_surjective_own p k Ω K T M A hA L hKL hc
  -- ## `βl A hA a` is `p`-torsion
  have h0 : βl A hA (0 : (Ω ≃ₐ[k] Ω) → M) = 0 :=
    (hβl_ker A hA 0 (fun g _ h _ => by simp)
      ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩).mpr ⟨0, fun g _ => by simp⟩
  have hy : p • βl A hA a = 0 :=
    g1l_nsmul_beta_eq_zero p k Ω K M (βl A hA) A (hβl_add A hA) h0 a ha hla
  -- ## the value formula and the vanishing hypothesis
  have hkey : χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
      (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
        (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
        (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb_coc b₀ hb₀fac))) = 0 := by
    rw [← hpair A hA a b hla hb_lc hb_coc L hKL b₀ hb₀fac]
    exact h b ⟨hb_coc, hb_lc⟩
  -- ## the arguments are `p`-torsion
  have hz : p • SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
      (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
      (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb_coc b₀ hb₀fac) = 0 := by
    rw [Work.SSGRoute.PT.pt_levelPair_nsmul_fst, hy, Work.SSGRoute.levelPair_zero]
  have hiz : p • Work.SSGRoute.PT.iota (k := k) (L := ↥L)
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
      (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
        (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
        (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb_coc b₀ hb₀fac)) = 0 :=
    Work.SSGRoute.PT.pt_iota_ptorsion p _ _ hz
  -- ## injectivity of `ι_w` and of `χ` on `p`-torsion
  have hzero : SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
      (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
      (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb_coc b₀ hb₀fac) = 0 :=
    Work.SSGRoute.PT.iota_injective_of_ptorsion p _ _ hz (hχinj L hKL _ hiz hkey)
  rw [← hfinZH hb_coc hb₀fac]
  exact hzero

/-- **The transfer**: the canonical family at the place cut out by `A` implies the abstract-level
vanishing (the hypothesis of clause (i) of `local_duality_ext_in`). -/
theorem vanishAbstract_of_canonical
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (y : Abelian.Ext
        (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
          (modRep (↥K ≃ₐ[k] ↥K) (DualMod p (M ⊗[ZMod p] T))))
        (localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))) 1)
    (hyp : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L),
        letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
        letI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
        letI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
        ∀ (h : extH (Rep.res (finZF hKL A hA)
            (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
              (modRep (↥K ≃ₐ[k] ↥K) (DualMod p (M ⊗[ZMod p] T))))) 1),
        levelPair (finZF hKL A hA) (finZI hKL A hA) y h = 0) :
    ∀ (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra ↥K L] [IsScalarTower k ↥K L]
      [FiniteDimensional k L] [IsGalois k L]
      (w' : NK.GlobalCFT.Place L)
      (hw' : NK.GlobalCFT.Place.LiesOver w' (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))
      (f : ↥(MulAction.stabilizer (L ≃ₐ[k] L) w') →*
        ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))))
      (hf : ∀ σ : ↥(MulAction.stabilizer (L ≃ₐ[k] L) w'),
        ((f σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))) : ↥K ≃ₐ[k] ↥K)
          = SSGRoute.PTExt.galRes k (↥K) L (σ : L ≃ₐ[k] L))
      (ι : Rep.res f (localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))) ⟶
        NK.HassePrinciple.localUnitsRep k L w')
      (hι : ∀ u : (NK.GlobalCFT.Place.localField ↥K
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))ˣ,
        (Rep.Hom.hom ι) (Additive.ofMul u) = Additive.ofMul
          (NK.GlobalCFT.Place.localAlgebraMapUnits w' (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) hw' u))
      (h : extH (Rep.res f
        (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
          (modRep (↥K ≃ₐ[k] ↥K) (DualMod p (M ⊗[ZMod p] T))))) 1),
      levelPair f ι y h = 0 := by
  intro L _ _ _ _ _ _ _ w' hw' f hf ι hι h
  obtain ⟨L₀, hFD₀, hGal₀, hKL₀, algL, hST1, hST2, hLies⟩ :=
    levelRealization k Ω K A hA L w' hw'
  letI : Algebra ↥K ↥L₀ := (IntermediateField.inclusion hKL₀).toAlgebra
  letI : Algebra L ↥L₀ := algL
  haveI : IsScalarTower k ↥K ↥L₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L₀ Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k L ↥L₀ := hST1
  haveI : IsScalarTower ↥K L ↥L₀ := hST2
  haveI : FiniteDimensional k ↥L₀ := hFD₀
  haveI : IsGalois k ↥L₀ := hGal₀
  haveI : FiniteDimensional L ↥L₀ := Module.Finite.of_restrictScalars_finite k L ↥L₀
  haveI : FiniteDimensional ↥K ↥L₀ := Module.Finite.of_restrictScalars_finite k ↥K ↥L₀
  let wc : NK.GlobalCFT.Place ↥L₀ := NK.GlobalCFT.Place.ofFinite (finQW L₀ A hA)
  have hwc : wc.LiesOver w' := hLies
  have hwc' : wc.LiesOver (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) := by
    have h1 : (finQW L₀ A hA).asIdeal.LiesOver (finQ K A hA).asIdeal :=
      finQW_liesOver (k := k) (Ω := Ω) (L := K) (L' := L₀) A hA hKL₀
    exact NK.GlobalCFT.Place.liesOver_ofFinite h1
  have hpinF : ∀ (fc : ↥(MulAction.stabilizer (↥L₀ ≃ₐ[k] ↥L₀) wc) →*
        ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))))
      (_hfc : ∀ σ : ↥(MulAction.stabilizer (↥L₀ ≃ₐ[k] ↥L₀) wc),
        ((fc σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))) : ↥K ≃ₐ[k] ↥K)
          = SSGRoute.PTExt.galRes k (↥K) (↥L₀) (σ : ↥L₀ ≃ₐ[k] ↥L₀)),
      fc = finZF hKL₀ A hA := by
    intro fc hfc
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    rw [hfc σ, finZF_spec hKL₀ A hA σ]
  have hpinI : ∀ (ιc : Rep.res (finZF hKL₀ A hA)
          (localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))) ⟶
        NK.HassePrinciple.localUnitsRep k ↥L₀ wc)
      (_hιc : ∀ u : (NK.GlobalCFT.Place.localField ↥K
          (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))ˣ,
        (Rep.Hom.hom ιc) (Additive.ofMul u) = Additive.ofMul
          (NK.GlobalCFT.Place.localAlgebraMapUnits wc (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) hwc' u)),
      ιc = finZI hKL₀ A hA := by
    intro ιc hιc
    have h1 : (Rep.Hom.hom ιc).toLinearMap =
        (Rep.Hom.hom (finZI hKL₀ A hA)).toLinearMap := by
      ext a
      obtain ⟨u, rfl⟩ := Additive.ofMul.surjective a
      exact (hιc u).trans (localUnitsMapAt_spec k ↥K ↥L₀
        (NK.GlobalCFT.Place.ofFinite (finQ K A hA)) wc hwc'
        (finZF hKL₀ A hA) (finZF_spec hKL₀ A hA) u).symm
    apply Rep.hom_ext
    exact Representation.IntertwiningMap.ext h1
  have hZ8 := Work.SSGRoute.Z8.levelPair_vanish_of_vanish_closure
    (k' := k) (K := ↥K) (w := NK.GlobalCFT.Place.ofFinite (finQ K A hA))
    (M := modRep (↥K ≃ₐ[k] ↥K) (DualMod p (M ⊗[ZMod p] T))) y L w' hw' ↥L₀ wc hwc hwc'
    (fun fc hfc ιc hιc hc => by
      obtain rfl := hpinF fc hfc
      obtain rfl := hpinI ιc hιc
      exact hyp L₀ hKL₀ hc)
  exact hZ8 f hf ι hι h

/-- **Perfectness of the finite half in the first variable** (interface restatement, v4_0215).

A locally constant `M`-cocycle `a` on the decomposition group of a finite place `A` of `Ω`, which
pairs to zero (through the place pairing `pair`, with its value formula `hpair` in terms of the
local dictionary `βl`) with every locally constant `M^∨(1)`-cocycle, is a coboundary.

The earlier statement of this node mentioned `G1pOwn.g1FinHalf`, the `Classical.choose` out of the
still-unproved `E1aClean.localDictionary_natural_family`, so no proof could be certified
(`#print axioms` traverses types); here `βl` and `pair` are variables with the clause list
`hβl_*` and the defining equation `hpair`.  The G1⁺ consumer instantiates
`βl := PT.finZB …` (clauses from `PT.finZB_spec`) and `pair := G1pOwn.g1FinHalf χ M`. -/
theorem g1FinHalf_perfect_left
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : Work.SSGRoute.PT.G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → χ L hKL u = 0 → u = 0)
    (hχcomp : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
        [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
        (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (βl : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ((Ω ≃ₐ[k] Ω) → M) →
        CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1)
    (hβl_add : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b b' : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
      βl A hA (b + b') = βl A hA b + βl A hA b')
    (hβl_ker : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (b : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      (βl A hA b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b))
    (hβl_onto : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) y,
      ∃ b : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ βl A hA b = y)
    (hβl_unr : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      ¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ b : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : (Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → b σ = 0) →
        SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (βl A hA b))
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hpair : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
      ∀ (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
        (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)),
        pair (SSGRoute.decomp k A) a b =
          χ L hKL (Work.SSGRoute.PT.iota (k := k) (L := ↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
              (Work.SSGRoute.PT.finZI hKL A hA) (βl A hA a)
              (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb b₀ hb₀))))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hla : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (h : ∀ b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) →
      pair (SSGRoute.decomp k A) a b = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a := by
  classical
  -- ## finiteness of the Tate dual `M^∨(1) = DualMod p (M ⊗ T)`
  haveI hXfin : Finite (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    g1l_finite_dualMod_tensor p k Ω K ζ hζ hζK T hT M
  haveI hMfin : Finite (↑(SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)))) :=
    inferInstanceAs (Finite (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)))
  have hMtor : ∀ m : Work.SSGRoute.DualMod p (M ⊗[ZMod p] T), p • m = 0 :=
    fun m => Work.SSGRoute.PT.nsmul_eq_zero_of_zmod' p m
  have hζi : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (by simpa using hζ)
      (RingHom.injective _)
  -- ## the canonical family, and its transport to the abstract levels of clause (i)
  have hcanon := g1l_canonical_family p k Ω K ζ hζ hζK T hT χ hχinj M βl hβl_add hβl_ker
    pair hpair A hA a ha hla h
  have htrans := vanishAbstract_of_canonical p k Ω K T M A hA (βl A hA a) hcanon
  -- ## clause (i) of local duality at the place of `K` under `A`
  have hy0 : βl A hA a = 0 :=
    (SSGRoute.local_duality_ext_in p k ↥K (⟨ζ, hζK⟩ : ↥K) hζi
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)))
      hMtor (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).1 (βl A hA a) htrans
  -- ## the kernel clause of the local dictionary
  exact (hβl_ker A hA a ha hla).mp hy0

end Work.SSGRoute.PT.G1plusOwn
