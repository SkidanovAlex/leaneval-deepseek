import Mathlib
import Submission.Work.SSGRoute.PT.g1plus_finHalf
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.PT.G1plusLevelClauses
import Submission.Work.SSGRoute.CokerPT.LevelClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

namespace Work.SSGRoute.PT.G1plusLevel

open CategoryTheory SSGRoute SSGRoute.PTExt
open scoped TensorProduct

/-! ## Additivity of the level class `[b]_L`

The second factor of `PT.finZZ` is the level class `PT.finZH … = PT.finLevelClass … b₀ …`, whose
defining body is an `ExtH1.gammaHom`-class (the `Rep`-transport in `finLevelClass` is along a
*definitional* equality).  Since `gammaHom ∘ H1π = gammaZ1` (`ExtH1.gammaHom_H1π`) and `gammaZ1`
is additive (`levelClass_add`), the level class is additive in `b₀`.  The two lemmas below record
this in the `finLevelClass`/`finZH` spelling used by `finZZ`. -/

/-- **Additivity of `PT.finLevelClass` in the factorised crossed homomorphism `b₀`**: at a fixed
level `L` the class `[b₀]_L = gammaHom (H1π b₀)` is additive.  (`finLevelClass` and `levelClass`
are the same class — `gammaHom (H1π ψ) = gammaZ1 ψ` — and `levelClass_add` is the `gammaZ1`
statement.) -/
theorem finLevelClass_add {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K L : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k L] [IsGalois k L] [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L]
    [IsScalarTower ↥K ↥L Ω] (hKL : K ≤ L)
    (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (f : ↥(_root_.SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      ↥(_root_.SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (hf : ∀ σ : ↥(_root_.SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      ((f σ : ↥(_root_.SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) : ↥K ≃ₐ[k] ↥K)
        = _root_.SSGRoute.PTExt.galRes k (↥K) (↥L) (σ : ↥L ≃ₐ[k] ↥L))
    (b₀ b₀' : (↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T))
    (h1 : ∀ g h : ↥(_root_.SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      b₀ ((g * h : ↥(_root_.SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))) : ↥L ≃ₐ[k] ↥L)
        = b₀ (g : ↥L ≃ₐ[k] ↥L)
          + (_root_.SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • b₀ (h : ↥L ≃ₐ[k] ↥L))
    (h2 : ∀ g h : ↥(_root_.SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      b₀' ((g * h : ↥(_root_.SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))) : ↥L ≃ₐ[k] ↥L)
        = b₀' (g : ↥L ≃ₐ[k] ↥L)
          + (_root_.SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • b₀' (h : ↥L ≃ₐ[k] ↥L))
    (h3 : ∀ g h : ↥(_root_.SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      (fun τ => b₀ τ + b₀' τ)
          ((g * h : ↥(_root_.SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))) : ↥L ≃ₐ[k] ↥L)
        = (fun τ => b₀ τ + b₀' τ) (g : ↥L ≃ₐ[k] ↥L)
          + (_root_.SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L))
            • (fun τ => b₀ τ + b₀' τ) (h : ↥L ≃ₐ[k] ↥L)) :
    finLevelClass p k Ω K T M L q w f hf (fun τ => b₀ τ + b₀' τ) h3
      = finLevelClass p k Ω K T M L q w f hf b₀ h1
        + finLevelClass p k Ω K T M L q w f hf b₀' h2 := by
  have e1 : finLevelClass p k Ω K T M L q w f hf (fun τ => b₀ τ + b₀' τ) h3
      = levelClass p k Ω K L hKL q w f hf M T (fun τ => b₀ τ + b₀' τ) h3 := by
    simp only [finLevelClass, levelClass]
    rw [Work.SSGRoute.ExtH1.gammaHom_H1π]
  have e2 : finLevelClass p k Ω K T M L q w f hf b₀ h1
      = levelClass p k Ω K L hKL q w f hf M T b₀ h1 := by
    simp only [finLevelClass, levelClass]
    rw [Work.SSGRoute.ExtH1.gammaHom_H1π]
  have e3 : finLevelClass p k Ω K T M L q w f hf b₀' h2
      = levelClass p k Ω K L hKL q w f hf M T b₀' h2 := by
    simp only [finLevelClass, levelClass]
    rw [Work.SSGRoute.ExtH1.gammaHom_H1π]
  rw [e1, e2, e3]
  exact levelClass_add p hKL q w f hf M T b₀ b₀' h1 h2 h3

/-- **Additivity of the level class `PT.finZH` in the cocycle `b`**: `finZH` is the class of the
factorisation `b₀` of `b|_H` through `Gal(L/k)`, so additivity is additivity of `finLevelClass`. -/
theorem finZH_add (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (b b' : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b')
    (hbadd : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (b + b'))
    (b₀ b₀' : (↥L ≃ₐ[k] ↥L) → SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hb₀' : ∀ σ ∈ SSGRoute.decomp k A, b' σ = b₀' (AlgEquiv.restrictNormalHom L σ))
    (hb₀add : ∀ σ ∈ SSGRoute.decomp k A,
      (b + b') σ = (fun τ => b₀ τ + b₀' τ) (AlgEquiv.restrictNormalHom L σ)) :
    finZH p K T M L hKL A hA (b + b') hbadd (fun τ => b₀ τ + b₀' τ) hb₀add
      = finZH p K T M L hKL A hA b hb b₀ hb₀
        + finZH p K T M L hKL A hA b' hb' b₀' hb₀' := by
  simp only [finZH]
  exact finLevelClass_add (K := K) (L := L) hKL p T M (finQ K A hA) (finQW L A hA)
    (finZF hKL A hA) (finZF_spec hKL A hA) b₀ b₀' _ _ _

/-- **Clause (2) of the finite half at a fixed level, in the `finZZ` vocabulary**: the level class `finZZ = levelPair finZF finZI (finZB a) (finZH …)` is additive in its second (cocycle) variable.  Together with `PT.chi_iota_levelPair_add_snd` (`PT/G1plusLevelClauses.lean`) this gives clause (2) of `G1⁺`'s finite half at a fixed level, which is what `H1Pair.PairClauses`'s second conjunct needs. -/
theorem finZZ_add_snd (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b b' : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b')
    (hbadd : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (b + b'))
    (b₀ b₀' : (↥L ≃ₐ[k] ↥L) → SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hb₀' : ∀ σ ∈ SSGRoute.decomp k A, b' σ = b₀' (AlgEquiv.restrictNormalHom L σ))
    (hb₀add : ∀ σ ∈ SSGRoute.decomp k A,
      (b + b') σ = (fun τ => b₀ τ + b₀' τ) (AlgEquiv.restrictNormalHom L σ)) :
    Work.SSGRoute.PT.finZZ p K ζ hζ hζK T hT M L hKL A hA a (b + b') hbadd
        (fun τ => b₀ τ + b₀' τ) hb₀add
      = Work.SSGRoute.PT.finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀
        + Work.SSGRoute.PT.finZZ p K ζ hζ hζK T hT M L hKL A hA a b' hb' b₀' hb₀' := by
  simp only [finZZ]
  rw [finZH_add p K T M L hKL A hA b b' hb hb' hbadd b₀ b₀' hb₀ hb₀' hb₀add]
  rw [Work.SSGRoute.levelPair_add_h]

end Work.SSGRoute.PT.G1plusLevel
