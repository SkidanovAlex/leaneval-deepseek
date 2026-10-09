import Mathlib
import Submission.Work.SSGRoute.PT.G1plusLevel.finZZ_add_snd
import Submission.Work.SSGRoute.PT.G1plusLevelClauses
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

namespace Work.SSGRoute.PT.G1plusLevel

/-- **Clause (2) of `G1⁺`'s finite half at a fixed level**: `finAtLevel` is additive in its second
(factorised cocycle) variable.

`finAtLevel … a b … = χ L hKL (iota r (finZZ … a b hb b₀ hb₀))` with
`finZZ = levelPair (finZF) (finZI) (finZB a) (finZH …)`.

Proof route (worked out; only the last step was left open):
1. re-introduce the tower instances `letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra`
   and the two `IsScalarTower`s (they are needed by `finZZ_add_snd`);
2. `have hZZ := finZZ_add_snd (p := p) (k := k) (Ω := Ω) (K := K) … (a := a) (b := b) (b' := b')
   …` (use *named* arguments: `k`/`Ω` are explicit arguments of that lemma);
3. `simp only [finAtLevel]`, `rw [hZZ]`, **then** `simp only [finZZ]` — unfolding `finZZ` before the
   final application is essential: with `finZZ` still folded, the unification of
   `chi_iota_levelPair_add_snd`'s implicit `Rep`-arguments sends Lean into a >4M-heartbeat defeq
   check (measured), while after unfolding it is immediate;
4. the `p`-torsion hypotheses of `chi_iota_levelPair_add_snd` are about the *level class*
   `finZH … b hb b₀ hb₀` (not about `levelPair`), and follow from
   `Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hpt _` where
   `hpt : ∀ x : ↥(Rep.res (finZF hKL A hA) (Rep.res (decompK …).subtype (modRep (↥K ≃ₐ[k] ↥K)
   (DualMod p (M ⊗[ZMod p] T))))), p • x = 0` is the pointwise `p`-torsion of the coefficient
   module (`fun x => nsmul_eq_zero_of_zmod p x`; pin the `Module (ZMod p)` instance for the
   `Rep.res`-carrier with a `letI`/`haveI` if instance search balks — the PT lane's files pin the
   same instances for `ptDual p M T`);
5. close with `chi_iota_levelPair_add_snd p (Place.ofFinite (finQW L A hA)) (χ L hKL) (hχadd L hKL)
   (finZF hKL A hA) (finZI hKL A hA) (finZB p K ζ hζ hζK T hT M A hA a)
   (finZH p K T M L hKL A hA b hb b₀ hb₀) (finZH p K T M L hKL A hA b' hb' b₀' hb₀') ht1 ht2`.

Note: the same statement exists as a `sorry` in
`Submission/Work/SSGRoute/G1plusClauses/finAtLevel_add_right.lean` (namespace
`Work.SSGRoute.G1plusClauses`, an abandoned orphan); this file is the live one. -/
theorem finAtLevel_add_right
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2 → ZMod p)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L)
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
    Work.SSGRoute.PT.finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L hKL a (b + b') hbadd
        (fun τ => b₀ τ + b₀' τ) hb₀add
      = Work.SSGRoute.PT.finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L hKL a b hb b₀ hb₀
        + Work.SSGRoute.PT.finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L hKL a b' hb' b₀' hb₀' := by
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- the level classes `[b]_L` and `[b']_L` are `p`-torsion (the coefficient module is a
  -- `ZMod p`-module)
  -- (the carrier of the `Rep.res`-coefficient module is *definitionally* the `ZMod p`-module
  -- `DualMod p (M ⊗ T)`, so the `ZMod p`-module instance is supplied by a type ascription rather
  -- than by instance search, which does not look through `Rep.res`)
  have hptor : ∀ x : DualMod p (TensorProduct (ZMod p) M T), p • x = 0 :=
    fun x => nsmul_eq_zero_of_zmod p x
  have ht1 : p • finZH p K T M L hKL A hA b hb b₀ hb₀ = 0 :=
    Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hptor _
  have ht2 : p • finZH p K T M L hKL A hA b' hb' b₀' hb₀' = 0 :=
    Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hptor _
  simp only [finAtLevel, finZZ]
  rw [finZH_add p K T M L hKL A hA b b' hb hb' hbadd b₀ b₀' hb₀ hb₀' hb₀add]
  exact chi_iota_levelPair_add_snd p (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) (χ L hKL)
    (hχadd L hKL) (finZF hKL A hA) (finZI hKL A hA)
    (finZB p K ζ hζ hζK T hT M A hA a)
    (finZH p K T M L hKL A hA b hb b₀ hb₀) (finZH p K T M L hKL A hA b' hb' b₀' hb₀')
    ht1 ht2

end Work.SSGRoute.PT.G1plusLevel
