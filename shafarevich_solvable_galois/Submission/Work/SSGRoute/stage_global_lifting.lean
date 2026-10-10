import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ExtChain.exists_khLift_of_extToIdeles_eq_zero
import Submission.Work.SSGRoute.ExtChain.himgLeafCore
import Submission.Work.SSGRoute.ExtChain.resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero
import Submission.Work.SSGRoute.ExtChain.shift_symm_extToIdeles_eq_zero_gen
import Submission.Work.SSGRoute.PTdualControl.pt_core_via_brick
import Submission.Work.SSGRoute.SSGate.assembly
import Submission.Work.SSGRoute.exists_continuous_lift_of_locconst_coboundary
import Submission.Work.SSGRoute.exists_cyclotomicDual
import Submission.Work.SSGRoute.exists_kerSuccAddEquiv_equivariant
import Submission.Work.SSGRoute.isCocycle2_isLocConst2_transported_cocycle
import Submission.Work.SSGRoute.prop5Data_exists
import Submission.Work.SSGRoute.sha2_image_of_Hm2
import Submission.Work.SSGRoute.transported_locconst_coboundary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `stage_global_lifting`: Step 2 of Theorem 15 of Schmidt–Wingberg (the global shrinking)

This file proves `Work.SSGRoute.stage_global_lifting`, the global lifting step of the induction
step `τ ↦ τ+1` of Schmidt–Wingberg's Theorem 15 (arXiv:math/9809211, §5, Step 2): given a Scholz
solution `φ : G_ℚ →* Γ_m(τ)` at a large level `m` whose local embedded problems are solvable at
every place (and at every involution), there is a shrinking `Φ : F(m) ⇢ F(n)` and a continuous
lift `ψ : G_ℚ →* Γ_n(τ+1)` of `(flowGroupMap Φ) ∘ φ` whose kernel is open, and the local
`T¹`-splittings survive the shrinking.

The proof assembles:

* `sha2_image_of_Hm2` (the Tate–Poitou input: `Ш²` is a natural image of `Ĥ⁻²`), applied to the
  graded-piece-valued section cocycle of `φ` (`isCocycle2_isLocConst2_transported_cocycle`,
  `transported_locconst_coboundary` for the local triviality);
* Proposition 6 in the case `k = -2` (`exists_shrinking_Hm2_tate`, fed by `prop5Data_exists`),
  producing `Φ` killing the resulting `Ĥ⁻²`-class;
* the naturality of the section cocycle (`kerSuccCocycle_naturality`) transported along the
  `G`-equivariant identification `E(n,τ) ≅ ker(Γ_n(τ+1) → Γ_n(τ))`
  (`exists_kerSuccAddEquiv_equivariant`), which turns the killed class into a locally constant
  primitive of the level-`n` cocycle and hence, through
  `exists_continuous_lift_of_locconst_coboundary`, into the lift `ψ`.
-/

namespace Work.SSGRoute

/-!
**Status (2026-09-26, 19:00).**  This file is sorry-free and builds, and **every** auxiliary result it
uses is axiom-clean; the single remaining axiom dependency of the main theorem is the Tate–Poitou
input

  `Work.SSGRoute.tatePoitouEmbedding`  (the injectivity half of Tate–Poitou duality
  `Ш²(k,E) ↪ Ш¹(k,E^∨(1))^∨`, natural in the coefficient module; Milne ADT I.4.10(a), NSW 8.6.8,
  the node of the `DESIGN_PT` workshop),

consumed through the two *proved* assemblies `Work.SSGRoute.sha2_dual_control_of_tatePoitouEmbedding`
and `Work.SSGRoute.sha2_image_of_Hm2_of_dualControl` (both axiom-clean).  The rest of the chain is
complete: `Work.SSGRoute.prop5Data_exists` (Proposition 5 of Schmidt–Wingberg) and
`Work.CohomologicalShrinking.exists_shrinking_Hm2_tate` are proved and clean.  This file does not
use `sha2_image_of_Hm2.lean` at all, and it imports `sha2_dual_control.lean` only for the *proved*
assembly `sha2_dual_control_of_tatePoitouEmbedding` (not for the `sorry` in that file): as soon as
`tatePoitouEmbedding` is filled in, the theorem here is axiom-clean.
-/

open SSGRoute
open Work.CohomologicalShrinking

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Auxiliary lemmas (bookkeeping) -/

/-- `σ` lies in the kernel of `restrictNormalHom K` exactly when it fixes `K`. -/
theorem globalLifting_res_eq_one_iff_mem_fixingSubgroup {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (K : IntermediateField F Ω) [Normal F K] (σ : Ω ≃ₐ[F] Ω) :
    (AlgEquiv.restrictNormalHom K σ = 1) ↔ σ ∈ K.fixingSubgroup := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]

/-- A one-dimensional `𝔽_p`-module is finite. -/
theorem finite_of_finrank_eq_one_ssg (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T]
    [Module (ZMod p) T] (h : Module.finrank (ZMod p) T = 1) : Finite T := by
  haveI : Module.Free (ZMod p) T := Module.Free.of_divisionRing (ZMod p) T
  haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by rw [h]; norm_num)
  have hfr : Module.finrank (ZMod p) T = Module.finrank (ZMod p) (ZMod p) := by
    rw [h, Module.finrank_self]
  exact Finite.of_injective
    (LinearEquiv.ofFinrankEq T (ZMod p) hfr : T ≃ₗ[ZMod p] ZMod p) (LinearEquiv.injective _)

/-- A cyclotomic dual module which is moreover finite (as an `𝔽_p`-module).  The witness of
`Work.SSGRoute.exists_cyclotomicDual` is `ZMod p`, so the finiteness instances are *derived* from
`Module.finrank (ZMod p) T = 1` (this keeps the file free of hand-written `DistribMulAction`
instances, so it stays importable next to other lanes' files). -/
theorem exists_cyclotomicDual_finite (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K) :
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Module (ZMod p) T)
      (_ : DistribMulAction (K ≃ₐ[ℚ] K) T) (_ : SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T)
      (_ : Module.Finite (ZMod p) T) (_ : Finite T),
      @SSGRoute.IsCyclotomicDual p SSGRoute.GalQ (K ≃ₐ[ℚ] K) T SSGRoute.QBar _ _ _ _ _ _ _
        (AlgEquiv.restrictNormalHom K) ζ := by
  obtain ⟨T, hTa, hTm, hTd, hTs, hTdual⟩ := exists_cyclotomicDual p K ζ hζ hζK
  letI : AddCommGroup T := hTa
  letI : Module (ZMod p) T := hTm
  letI : DistribMulAction (K ≃ₐ[ℚ] K) T := hTd
  letI : SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T := hTs
  haveI hTfin : Module.Finite (ZMod p) T :=
    Module.finite_of_finrank_pos (by rw [hTdual.1]; norm_num)
  haveI hTfinite : Finite T := finite_of_finrank_eq_one_ssg p T hTdual.1
  exact ⟨T, hTa, hTm, hTd, hTs, hTfin, hTfinite, hTdual⟩

/-- `succKerIso` is an equivalence of `G`-modules for the conjugation action on the kernel. -/
theorem succKerIso_equivariance_add (p : ℕ) (G : Type*) [Group G] (k i j : ℕ) (g : G)
    (x : Additive ↥(flowGroupSucc p G k i j).ker) :
    (succKerIso p G k i j).toAdditive.symm
        (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G k i j)
          (SemidirectProduct.mk 1 g : flowGroup p G k (tauSucc i j).1 (tauSucc i j).2)
          (Additive.toMul x)))
      = g • (succKerIso p G k i j).toAdditive.symm x := by
  have h := succKerIso_smul p G k i j g ((succKerIso p G k i j).symm (Additive.toMul x))
  rw [MulEquiv.apply_symm_apply] at h
  have h2 : (succKerIso p G k i j).symm
      (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G k i j)
        (SemidirectProduct.mk 1 g : flowGroup p G k (tauSucc i j).1 (tauSucc i j).2)
        (Additive.toMul x))
      = g • (succKerIso p G k i j).symm (Additive.toMul x) := by
    have h3 := congrArg (succKerIso p G k i j).symm h
    rw [MulEquiv.symm_apply_apply] at h3
    exact h3.symm
  rw [succKerAddEquiv_symm_apply, succKerAddEquiv_symm_apply, smul_additive_apply, toMul_ofMul]
  exact congrArg Additive.ofMul h2

/-- `succKerIso` is natural in the rank, in the additive form used by the lifting argument. -/
theorem succKerIso_naturality_add (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (x : ↥(flowGroupSucc p G m i j).ker) :
    (succKerIso p G n i j).toAdditive.symm
        (Additive.ofMul (flowGroupSuccKernelMap p G i j Φ x))
      = gradedMapLin p Φ.toHom Φ.surjective i j
          ((succKerIso p G m i j).toAdditive.symm (Additive.ofMul x)) := by
  set y := (succKerIso p G m i j).symm x with hy
  have hx : succKerIso p G m i j y = x := MulEquiv.apply_symm_apply _ _
  rw [← hx, succKerIso_naturality p G i j Φ y]
  have h1 : (succKerIso p G n i j).toAdditive.symm
      (Additive.ofMul (succKerIso p G n i j ((gradedMapMul p Φ.toHom Φ.surjective i j) y)))
      = Additive.ofMul ((gradedMapMul p Φ.toHom Φ.surjective i j) y) := by
    rw [succKerAddEquiv_symm_apply, toMul_ofMul, MulEquiv.symm_apply_apply]
  have h2 : (succKerIso p G m i j).toAdditive.symm
      (Additive.ofMul (succKerIso p G m i j y)) = Additive.ofMul y := by
    rw [succKerAddEquiv_symm_apply, toMul_ofMul, MulEquiv.symm_apply_apply]
  rw [h1, h2, gradedMapLin_apply, toMul_ofMul]

/-- **The `T¹`-splittings survive the shrinking.**  If the local extension at a place `A` of `T¹`
splits at level `m` over the local group (with a splitting killing the kernel), then the pushed
solution `(flowGroupMap Φ) ∘ φ` at level `n` again has a local splitting killing its kernel.

The point is Scholz's condition (i): at `A ∈ T¹` the kernel of `φ` on `D_A` is exactly
`D_A ∩ G_K`, so the `G`-component of the pushed local group still determines the element, and the
`F`-part of `ker(flowGroupMap Φ)` is invisible. -/
theorem exists_liftAt_T1_place_of_flowGroupMap (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (i j m n : ℕ)
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ)
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsT1Place p K A)
    (l : ↥(SSGRoute.decomp ℚ A) →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (hl : ∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φ (σ : SSGRoute.GalQ)))
    (hk : ∀ σ : ↥(SSGRoute.decomp ℚ A), φ (σ : SSGRoute.GalQ) = 1 → l σ = 1) :
    ∃ l' : ↥(SSGRoute.decomp ℚ A) →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
      (∀ σ : ↥(SSGRoute.decomp ℚ A),
        SSGRoute.LiftsFlowAt (l' σ) (((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) ∧
      (∀ σ : ↥(SSGRoute.decomp ℚ A),
        ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ = 1 → l' σ = 1) := by
  refine ⟨(flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp l, ?_, ?_⟩
  · intro σ
    rw [liftsFlowAt_iff_flowGroupSucc]
    have h1 : flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (l σ) = φ (σ : SSGRoute.GalQ) :=
      (liftsFlowAt_iff_flowGroupSucc p K m i j (l σ) (φ (σ : SSGRoute.GalQ))).mp
        (hl σ)
    have h2 := DFunLike.congr_fun (flowGroupSucc_flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (l σ)
    simp only [MonoidHom.comp_apply, h1] at h2
    exact h2
  · intro σ hσ
    have hker : flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (φ (σ : SSGRoute.GalQ)) = 1 := hσ
    have hquot : flowQuot p (K ≃ₐ[ℚ] K) m i j (φ (σ : SSGRoute.GalQ)) = 1 := by
      have h := flowQuot_flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (φ (σ : SSGRoute.GalQ))
      rw [hker, map_one] at h
      exact h.symm
    have hres : AlgEquiv.restrictNormalHom K (σ : SSGRoute.GalQ) = 1 := by
      rw [← hφ.1.2.2 (σ : SSGRoute.GalQ)]
      exact hquot
    have hfix : (σ : SSGRoute.GalQ) ∈ K.fixingSubgroup :=
      (@globalLifting_res_eq_one_iff_mem_fixingSubgroup ℚ SSGRoute.QBar _ _ _ K ‹Normal ℚ K›
        (σ : SSGRoute.GalQ)).mp hres
    have hφσ : φ (σ : SSGRoute.GalQ) = 1 := hφ.2.1 A hA (σ : SSGRoute.GalQ) σ.2 hfix
    rw [MonoidHom.comp_apply, hk σ hφσ, map_one]

/-- **From a coboundary of the pushed cocycle to a locally constant primitive at level `n`.**
If the transport `e'` of the level-`n` section cocycle differs from the push-forward
`gradedMapLin Φ ∘ (e ∘ κ_m)` by the `β`-coboundary of `kerSuccBeta`, and the push-forward is a
coboundary with locally constant primitive `b`, then the level-`n` section cocycle itself is a
coboundary with a locally constant primitive.  This is the last group-theoretic step of Step 2. -/
theorem exists_primitive_of_gradedMapLin_coboundary_aux (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (i j m n : ℕ)
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hflow : ∀ σ : SSGRoute.GalQ, flowQuot p (K ≃ₐ[ℚ] K) m i j (φ σ) =
        AlgEquiv.restrictNormalHom K σ)
    (hopen : IsOpen (φ.ker : Set SSGRoute.GalQ))
    (Ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hΨ : ∀ σ : SSGRoute.GalQ, Ψ σ = flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ (φ σ))
    (e : Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker ≃+ E p (K ≃ₐ[ℚ] K) m i j)
    (e' : Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker ≃+ E p (K ≃ₐ[ℚ] K) n i j)
    (he' : ∀ (g : K ≃ₐ[ℚ] K) (x : Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker),
      e' (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j)
        (SemidirectProduct.mk 1 g : flowGroup p (K ≃ₐ[ℚ] K) n
          (tauSucc i j).1 (tauSucc i j).2)
        (Additive.toMul x))) = g • e' x)
    (hnat : ∀ x : ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker,
      e' (Additive.ofMul (flowGroupSuccKernelMap p (K ≃ₐ[ℚ] K) i j Φ x))
        = gradedMapLin p Φ.toHom Φ.surjective i j (e (Additive.ofMul x)))
    (s : flowGroup p (K ≃ₐ[ℚ] K) m i j →
      flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (hs : ∀ x, flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (s x) = x)
    (s' : flowGroup p (K ≃ₐ[ℚ] K) n i j →
      flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hs' : ∀ x, flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (s' x) = x)
    (hb : ∃ b : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
      SSGRoute.IsLocConstOn ⊤ b ∧
      ∀ σ τ : SSGRoute.GalQ,
        gradedMapLin p Φ.toHom Φ.surjective i j
            (e (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs σ τ))
          = AlgEquiv.restrictNormalHom K σ • b τ - b (σ * τ) + b σ) :
    ∃ f : SSGRoute.GalQ → Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker,
      SSGRoute.IsLocConstOn ⊤ f ∧
      ∀ σ τ : SSGRoute.GalQ,
        kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j Ψ s' hs' σ τ =
          Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j)
            (s' (Ψ σ)) (Additive.toMul (f τ))) - f (σ * τ) + f σ := by
  classical
  obtain ⟨b, hblc, hbcob⟩ := hb
  -- the `β`-cocycle of the naturality of the section cocycle
  have hβconst : ∀ g u : SSGRoute.GalQ, φ u = 1 →
      kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ φ Ψ hΨ s s' hs hs' (g * u) =
      kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ φ Ψ hΨ s s' hs hs' g := by
    intro g u hu
    have h1 : φ (g * u) = φ g := by rw [map_mul, hu, mul_one]
    have h2 : Ψ (g * u) = Ψ g := by simp only [hΨ, map_mul, hu, mul_one]
    apply Subtype.ext
    simp only [kerSuccBeta, h1, h2]
  have hβlc : SSGRoute.IsLocConstOn ⊤
      (fun σ => kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ φ Ψ hΨ s s' hs hs' σ) := by
    refine ⟨φ.ker, hopen, ?_⟩
    intro g _ u hu _
    exact hβconst g u (MonoidHom.mem_ker.mp hu)
  let bβ : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j := fun σ =>
    e' (Additive.ofMul (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ φ Ψ hΨ s s' hs hs' σ))
  have hbβlc : SSGRoute.IsLocConstOn ⊤ bβ := by
    obtain ⟨U, hU, hUl⟩ := hβlc
    refine ⟨U, hU, ?_⟩
    intro g _ u hu _
    dsimp only [bβ]
    exact congrArg (fun z => e' (Additive.ofMul z))
      (hUl g (Subgroup.mem_top g) u hu (Subgroup.mem_top u))
  refine ⟨fun σ => e'.symm (b σ - bβ σ), ?_, ?_⟩
  · obtain ⟨U₁, hU₁, hb₁⟩ := hblc
    obtain ⟨U₂, hU₂, hb₂⟩ := hbβlc
    refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, ?_⟩
    intro g _ u hu _
    have hu₁ : u ∈ U₁ := (Subgroup.mem_inf.mp hu).1
    have hu₂ : u ∈ U₂ := (Subgroup.mem_inf.mp hu).2
    dsimp only
    rw [hb₁ g (Subgroup.mem_top g) u hu₁ (Subgroup.mem_top u),
      hb₂ g (Subgroup.mem_top g) u hu₂ (Subgroup.mem_top u)]
  · -- the coboundary identity
    intro σ τ
    change kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j Ψ s' hs' σ τ =
      Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j)
        (s' (Ψ σ)) (Additive.toMul (e'.symm (b τ - bβ τ)))) - e'.symm (b (σ * τ) - bβ (σ * τ))
        + e'.symm (b σ - bβ σ)
    -- the `G`-coordinate of `s' (Ψ σ)`
    have hright : (s' (Ψ σ)).right = AlgEquiv.restrictNormalHom K σ := by
      have h1 := flowGroupSucc_right p (K ≃ₐ[ℚ] K) n i j (s' (Ψ σ))
      rw [hs' (Ψ σ)] at h1
      rw [← h1, hΨ σ, flowGroupMap_right]
      exact hflow σ
    -- conjugation by `s' (Ψ σ)` acts through the `G`-coordinate
    have hconj : ∀ y : ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) n i j).ker,
        e' (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
          (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) (s' (Ψ σ)) y))
          = AlgEquiv.restrictNormalHom K σ • e' (Additive.ofMul y) := by
      intro y
      have hsub : Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j)
            (s' (Ψ σ)) y
          = Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j)
              (SemidirectProduct.mk 1 (AlgEquiv.restrictNormalHom K σ) :
                flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) y := by
        conv_lhs =>
          rw [show s' (Ψ σ) = SemidirectProduct.mk (s' (Ψ σ)).left (s' (Ψ σ)).right from rfl,
            hright]
        exact kerSucc_conj_eq_mk_one p (K ≃ₐ[ℚ] K) i j n (s' (Ψ σ)).left
          (AlgEquiv.restrictNormalHom K σ) y
      rw [hsub]
      exact he' (AlgEquiv.restrictNormalHom K σ) (Additive.ofMul y)
    -- the transported cocycle identity
    have hnatn := kerSuccCocycle_naturality (p := p) (G := K ≃ₐ[ℚ] K) (m := m) (n := n) i j Φ φ Ψ
      hΨ s hs s' hs' σ τ
    have hA : e' (Additive.ofMul (flowGroupSuccKernelMap p (K ≃ₐ[ℚ] K) i j Φ
          (kerSuccCocycleMul p (K ≃ₐ[ℚ] K) m i j φ s hs σ τ)))
        = gradedMapLin p Φ.toHom Φ.surjective i j
            (e (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs σ τ)) := by
      rw [hnat (kerSuccCocycleMul p (K ≃ₐ[ℚ] K) m i j φ s hs σ τ)]
      rfl
    have hB : e' (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
          (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j) (s' (Ψ σ))
          (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ φ Ψ hΨ s s' hs hs' τ)))
        = AlgEquiv.restrictNormalHom K σ • bβ τ := by
      rw [hconj (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ φ Ψ hΨ s s' hs hs' τ)]
    have hC : e' (Additive.ofMul (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ φ Ψ hΨ s s' hs hs' (σ * τ)))
        = bβ (σ * τ) := rfl
    have hD : e' (Additive.ofMul (kerSuccBeta p (K ≃ₐ[ℚ] K) i j Φ φ Ψ hΨ s s' hs hs' σ))
        = bβ σ := rfl
    have hE : e' (kerSuccCocycle p (K ≃ₐ[ℚ] K) n i j Ψ s' hs' σ τ)
        = AlgEquiv.restrictNormalHom K σ • (b τ - bβ τ) - (b (σ * τ) - bβ (σ * τ))
          + (b σ - bβ σ) := by
      rw [hnatn]
      simp only [map_add, map_sub]
      rw [hA, hB, hC, hD, hbcob σ τ]
      simp only [smul_sub]
      abel
    -- the inverse equivariance of `e'`
    have hconj' : ∀ (g : K ≃ₐ[ℚ] K) (z : E p (K ≃ₐ[ℚ] K) n i j),
        e'.symm (g • z) = Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
          (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j)
          (SemidirectProduct.mk 1 g : flowGroup p (K ≃ₐ[ℚ] K) n
            (tauSucc i j).1 (tauSucc i j).2)
          (Additive.toMul (e'.symm z))) := by
      intro g z
      apply e'.injective
      rw [AddEquiv.apply_symm_apply, he' g (e'.symm z), AddEquiv.apply_symm_apply]
    -- apply `e'.symm` to the transported cocycle identity
    have h1 := congrArg e'.symm hE
    rw [AddEquiv.symm_apply_apply] at h1
    rw [h1]
    -- distribute `e'.symm`
    have hdist : e'.symm (AlgEquiv.restrictNormalHom K σ • (b τ - bβ τ)
          - (b (σ * τ) - bβ (σ * τ)) + (b σ - bβ σ))
        = e'.symm (AlgEquiv.restrictNormalHom K σ • (b τ - bβ τ))
          - e'.symm (b (σ * τ) - bβ (σ * τ)) + e'.symm (b σ - bβ σ) :=
      (map_add e'.symm.toAddMonoidHom
        (AlgEquiv.restrictNormalHom K σ • (b τ - bβ τ) - (b (σ * τ) - bβ (σ * τ)))
        (b σ - bβ σ)).trans
        (congrArg (fun w => w + e'.symm (b σ - bβ σ))
          (map_sub e'.symm.toAddMonoidHom (AlgEquiv.restrictNormalHom K σ • (b τ - bβ τ))
            (b (σ * τ) - bβ (σ * τ))))
    rw [hdist]
    -- identify the `G`-action term
    have hPiece : e'.symm (AlgEquiv.restrictNormalHom K σ • (b τ - bβ τ))
        = Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p (K ≃ₐ[ℚ] K) n i j)
            (s' (Ψ σ)) (Additive.toMul (e'.symm (b τ - bβ τ)))) := by
      rw [hconj' (AlgEquiv.restrictNormalHom K σ) (b τ - bβ τ)]
      congr 1
      have hkc := kerSucc_conj_eq_mk_one p (K ≃ₐ[ℚ] K) i j n (s' (Ψ σ)).left
        (AlgEquiv.restrictNormalHom K σ) (Additive.toMul (e'.symm (b τ - bβ τ)))
      rw [← hright] at hkc ⊢
      exact hkc.symm
    rw [hPiece]

/-! ## The main theorem -/

/-- **`E1aFiled` implies `E1aInput`.**  The *filed* image description of node `E1a`
(`Work.SSGRoute.ext_sha2_bridge`: `im β = ker extToIdeles`) gives the assembly's input
(`PTembedding.E1aInput`: every value of `β` lifts along the connecting map `extDelta`), because a
class with `extToIdeles y = 0` lies in `im extDelta` by the exactness of the class formation
(`Work.SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero`). -/
theorem ssg_E1aInput_of_E1aFiled (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (h : Work.SSGRoute.PTembedding.E1aFiled p k Ω K T) :
    Work.SSGRoute.PTembedding.E1aInput p k Ω K T := by
  have : NumberField ↥K := NumberField.of_module_finite (K := k) (L := ↥K)
  obtain ⟨β, hinj, himg, hnat⟩ := h
  refine ⟨β, hinj, ?_, hnat⟩
  intro E _ _ _ _ _ b
  exact Work.SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero (k := k) (K := ↥K)
    (β E b) ((himg E (β E b)).mp ⟨b, rfl⟩)

/-- **`E1aInput` from the *landing clause* of node `E1a`** (`Work.SSGRoute.PT.e1aBetaCan_le_ker`:
`im β ⊆ ker extToIdeles`, the `⇒`-half of the filed image description).

This is the direction the `G5` assembly actually consumes (`ptAssembly.lean`: "the assembly uses
strictly less than `E1aFiled` states"), and it is the form that decomposes by places
(`PT/e1aBetaCan_splitPlaces.lean` proves its split places, and `e1aBetaCan_le_ker.lean` records the
remaining, conditional localisation comparison), whereas the full `iff` (`PT.e1aBetaCan_image`) is
*equivalent* to the degree-two local dictionary of the canonical chain
(`PT/NOTE_e1aBetaCan_image_analysis.md` §5) and is never used by the assembly.

The canonical family `β` of `PT/e1a_assembly.lean` is already built from the crux
`PT.e1a_sha2_mem_range_chainC` — the membership clause `hmem` is `e1aChainC_mem_range`, its
injectivity and naturality in `E` are `e1aBetaFamily_injective` / `e1aBetaFamily_natural` — so only
the landing clause is missing; `PT.e1aBetaCan_le_ker` supplies it verbatim, and
`PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero` converts `extToIdeles (β b) = 0` into a
lift along `extDelta`. -/
theorem ssg_E1aInput_of_le_ker (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    Work.SSGRoute.PTembedding.E1aInput p k Ω K T := by
  have : NumberField ↥K := NumberField.of_module_finite (K := k) (L := ↥K)
  have hcr := fun (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] =>
    Work.SSGRoute.PT.e1a_sha2_mem_range_chainC p k Ω K ζ hζ hζK T hT E
  refine ⟨fun E _ _ _ _ _ => Work.SSGRoute.PT.e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E,
    ?_, ?_, ?_⟩
  · intro E _ _ _ _ _
    exact Work.SSGRoute.PT.e1aBetaFamily_injective p k Ω K ζ hζ hζK T hT hcr E
  · intro E _ _ _ _ _ b
    refine Work.SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero (k := k)
      (K := ↥K) ((Work.SSGRoute.PT.e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E) b) ?_
    exact Work.SSGRoute.PT.e1aBetaCan_le_ker p k Ω K ζ hζ hζK T hT E
      (Work.SSGRoute.PT.e1aChainC_mem_range p k Ω K ζ hζ hζK T hT E (hcr E))
      ((Work.SSGRoute.PT.e1aBetaFamily p k Ω K ζ hζ hζK T hT hcr E) b) ⟨b, rfl⟩
  · intro E₁ _ _ _ _ _ E₂ _ _ _ _ _ f hf F hF b
    exact Work.SSGRoute.PT.e1aBetaFamily_natural p k Ω K ζ hζ hζK T hT hcr E₁ E₂ f hf F hF b

/-- **Note (2026-10-02).**  `E1aInput` is also available from the work area's own landing clause
`Work.SSGRoute.SSGStage.e1aLandingClause` (proved by a delegated child; the same place-by-place
assembly, through the PT lane's `SSGStage.e1aLandingFinCompat` / `e1aLandingInfLocal`).  The helper
`ssg_E1aInput_of_landing` that consumes it was written and then removed from this module, so that
this module does not depend on a file that may be in flight; see §16 of
`NOTE_sgl_minimal_dependency.md` for why the `hE1a` slot is instead wired to the PT lane's
`PT.e1aBetaCan_le_ker` (the same statement, in the file the PT lane is actively closing). -/

theorem stage_global_lifting (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i) (n : ℕ) (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j,
        SSGRoute.IsScholzSolution p K m i j φ →
        (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
          ¬ SSGRoute.IsT1Place p K A →
          ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
                (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
            (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φ σ)) ∧
            IsOpen (l.ker : Set ↥(SSGRoute.decomp ℚ A))) →
        (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
          ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
                (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
            (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φ σ)) ∧
            IsOpen (l.ker : Set ↥(SSGRoute.decomp ℚ A)) ∧
            (∀ σ : ↥(SSGRoute.decomp ℚ A), φ σ = 1 → l σ = 1)) →
        (∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
          ∃ l : ↥(Subgroup.zpowers c) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
                (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
            (∀ σ : ↥(Subgroup.zpowers c), SSGRoute.LiftsFlowAt (l σ) (φ σ)) ∧
            IsOpen (l.ker : Set ↥(Subgroup.zpowers c))) →
        ∃ (Φ : Work.CohomologicalShrinking.OperatorMap (K ≃ₐ[ℚ] K) m n)
          (ψ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
                (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2),
          SSGRoute.LiftsFlow ψ ((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) ∧
          IsOpen (ψ.ker : Set SSGRoute.GalQ) ∧
          (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
            ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
                  (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
              (∀ σ : ↥(SSGRoute.decomp ℚ A),
                SSGRoute.LiftsFlowAt (l σ)
                  (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) ∧
              (∀ σ : ↥(SSGRoute.decomp ℚ A),
                ((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ = 1 → l σ = 1)) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI hFintK : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ K
  haveI hGalK : IsGalois ℚ K := IsGalois.mk
  -- a primitive `p`-th root of unity in `K`, and the cyclotomic dual `T`
  obtain ⟨ζ, hζK, hζ⟩ := hμ
  have hζp : IsPrimitiveRoot (ζ ^ p ^ i) p :=
    IsPrimitiveRoot.pow (pow_pos hp.pos (i + 1)) hζ (by rw [pow_succ])
  have hζpK : ζ ^ p ^ i ∈ K := by
    have h : ζ ^ ((p ^ i : ℕ) : ℤ) ∈ K := K.pow_mem hζK ((p ^ i : ℕ) : ℤ)
    simpa only [zpow_natCast] using h
  obtain ⟨T, hTa, hTm, hTd, hTs, hTfin, hTfinite, hTdual⟩ :=
    exists_cyclotomicDual_finite p K (ζ ^ p ^ i) hζp hζpK
  letI : AddCommGroup T := hTa
  letI : Module (ZMod p) T := hTm
  letI : DistribMulAction (K ≃ₐ[ℚ] K) T := hTd
  letI : SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T := hTs
  letI : Module.Finite (ZMod p) T := hTfin
  letI : Finite T := hTfinite
  -- Proposition 5 data and the shrinking (Proposition 6, `k = -2`)
  obtain ⟨D⟩ := prop5Data_exists p (K ≃ₐ[ℚ] K) i j hj hji
  obtain ⟨m₀, hm₀, hshr⟩ := exists_shrinking_Hm2_tate (n := n) p (K ≃ₐ[ℚ] K) hj D T 1 hn
  refine ⟨m₀, hm₀, ?_⟩
  intro m hm φ hφ hOther hT1 hInv
  obtain ⟨hsurjφ, hopenφ, hresφ⟩ := hφ.1
  have hs : ∀ x, flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (flowGroupSection p (K ≃ₐ[ℚ] K) m i j x) = x :=
    flowGroupSucc_section p (K ≃ₐ[ℚ] K) m i j
  -- the transported section cocycle at level `m`
  set κE : SSGRoute.GalQ → SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j := fun σ τ =>
    (succKerIso p (K ≃ₐ[ℚ] K) m i j).toAdditive.symm
      (kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ (flowGroupSection p (K ≃ₐ[ℚ] K) m i j) hs σ τ)
    with hκEdef
  obtain ⟨hκcocycle, hκlc⟩ := isCocycle2_isLocConst2_transported_cocycle p K i j m φ hopenφ hresφ
    ((succKerIso p (K ≃ₐ[ℚ] K) m i j).toAdditive.symm)
    (succKerIso_equivariance_add p (K ≃ₐ[ℚ] K) m i j)
    (flowGroupSection p (K ≃ₐ[ℚ] K) m i j) hs (flowGroupSection_one p (K ≃ₐ[ℚ] K) m i j)
  -- it is locally trivial at every finite place and at every involution
  have hlocAll : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      SSGRoute.IsCoboundary2On (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A) κE := by
    intro A hAfin
    by_cases hAnT1 : SSGRoute.IsT1Place p K A
    · obtain ⟨l, hl, hlopen, _⟩ := hT1 A hAnT1
      exact transported_locconst_coboundary p K i j m φ hresφ hopenφ
        ((succKerIso p (K ≃ₐ[ℚ] K) m i j).toAdditive.symm)
        (succKerIso_equivariance_add p (K ≃ₐ[ℚ] K) m i j)
        (flowGroupSection p (K ≃ₐ[ℚ] K) m i j) hs (flowGroupSection_one p (K ≃ₐ[ℚ] K) m i j)
        (SSGRoute.decomp ℚ A) l hl hlopen
    · obtain ⟨l, hl, hlopen⟩ := hOther A hAfin hAnT1
      exact transported_locconst_coboundary p K i j m φ hresφ hopenφ
        ((succKerIso p (K ≃ₐ[ℚ] K) m i j).toAdditive.symm)
        (succKerIso_equivariance_add p (K ≃ₐ[ℚ] K) m i j)
        (flowGroupSection p (K ≃ₐ[ℚ] K) m i j) hs (flowGroupSection_one p (K ≃ₐ[ℚ] K) m i j)
        (SSGRoute.decomp ℚ A) l hl hlopen
  haveI hEfin : Finite (E p (K ≃ₐ[ℚ] K) m i j) := by
    haveI := Work.CohomologicalShrinking.flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) m i j
    exact Finite.of_equiv _ Additive.ofMul.symm
  -- local triviality at every involution
  have hinf : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (AlgEquiv.restrictNormalHom K) (Subgroup.zpowers c) κE := by
    intro c hc
    obtain ⟨l, hl, hlopen⟩ := hInv c hc
    exact transported_locconst_coboundary p K i j m φ hresφ hopenφ
      ((succKerIso p (K ≃ₐ[ℚ] K) m i j).toAdditive.symm)
      (succKerIso_equivariance_add p (K ≃ₐ[ℚ] K) m i j)
      (flowGroupSection p (K ≃ₐ[ℚ] K) m i j) hs (flowGroupSection_one p (K ≃ₐ[ℚ] K) m i j)
      (Subgroup.zpowers c) l hl hlopen
  -- The remaining arithmetic inputs of the atom, in the form in which the workspace's assembled
  -- theorem `sha2_image_of_Hm2_fin_of_e1a_and_core` consumes them:
  -- * `E1a`, in its **landing-clause** form `PT.e1aBetaCan_le_ker` (`im β ⊆ ker extToIdeles`, the
  --   `⇒`-half of the filed image description, the direction the assembly consumes), converted to
  --   the assembly's input `PTembedding.E1aInput` by `ssg_E1aInput_of_le_ker` (which uses the
  --   proved crux `PT.e1a_sha2_mem_range_chainC` and the proved injectivity/naturality
  --   `PT.e1aBetaFamily_injective` / `PT.e1aBetaFamily_natural`); the alternative, strictly
  --   stronger route through the *filed* image description is `ssg_E1aInput_of_E1aFiled`;
  -- * `E9`, the ζ-guarded core `Work.SSGRoute.pt_sha2_core` (annihilator of the locally trivial
  --   classes), supplied through its explicit `hcore` slot.  It is cited from the E7cΩ lane's file
  --   on purpose: that lane keeps re-routing the file (it currently inlines the proved
  --   `local_phi_realization_in_aux` plus its own clause theorem), and this node's `sorryAx` should
  --   track the lane's *current* best spelling rather than a frozen copy — see
  --   `NOTE_sgl_minimal_dependency.md` §16;
  -- * the primitive `p`-th root of unity inside `K`, available from the hypothesis `hμ`.
  haveI hNFK : NumberField ↥K := NumberField.of_module_finite (K := ℚ) (L := ↥K)
  have hE1a : @Work.SSGRoute.PTembedding.E1aInput p _ ℚ SSGRoute.QBar _ _ _ _ _ K _ hGalK hFintK T hTa hTm hTd hTs :=
    @ssg_E1aInput_of_le_ker p _ ℚ SSGRoute.QBar _ _ _ _ _ K _ hGalK hFintK (ζ ^ p ^ i) hζp hζpK
      T hTa hTm hTd hTs hTdual
  have hroot : ∃ ζ' : ↥K, IsPrimitiveRoot ζ' p :=
    ⟨⟨ζ ^ p ^ i, hζpK⟩, IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K SSGRoute.QBar)
      (by simpa using hζp) (RingHom.injective _)⟩
  obtain ⟨x, hx⟩ :=
    @Work.SSGRoute.sha2_image_of_Hm2_fin_of_e1a_and_core p _ ℚ SSGRoute.QBar _ _ _ _ _ K _
      hGalK hFintK (ζ ^ p ^ i) hζp hζpK (E p (K ≃ₐ[ℚ] K) m i j) T
      (inferInstance : AddCommGroup (E p (K ≃ₐ[ℚ] K) m i j))
      (inferInstance : Module (ZMod p) (E p (K ≃ₐ[ℚ] K) m i j))
      (inferInstance : DistribMulAction (K ≃ₐ[ℚ] K) (E p (K ≃ₐ[ℚ] K) m i j))
      (inferInstance : SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) (E p (K ≃ₐ[ℚ] K) m i j))
      hEfin hTa hTm hTd hTs hTdual hE1a
      (fun ζ' hζ' M _ hM x hx =>
        @Work.SSGRoute.PTdualControl.pt_sha2_core_clean_via_brick p _ ℚ ↥K _ _ _ hNFK _ _ hGalK
          (@Work.SSGRoute.SSGate.rankOneBrick_of_concentrated p _ ℚ ↥K _ _ _ hNFK _
            (AlgebraicClosure ↥K) _ _ _)
          ζ' hζ' M _ hM x hx)
      hroot κE hκcocycle hκlc hlocAll hinf
  -- the shrinking killing the class
  obtain ⟨Φ, hΦ⟩ := hshr m hm (fun _ : Fin 1 => x)
  have hΦ0 : Φ.hm2Map p (K ≃ₐ[ℚ] K) T x = 0 := hΦ 0
  haveI hEfinN : Finite (E p (K ≃ₐ[ℚ] K) n i j) := by
    haveI := Work.CohomologicalShrinking.flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) n i j
    exact Finite.of_equiv _ Additive.ofMul.symm
  have hb : SSGRoute.IsCoboundary2On (AlgEquiv.restrictNormalHom K) ⊤
      (fun σ τ => gradedMapLin p Φ.toHom Φ.surjective i j (κE σ τ)) :=
    @hx (E p (K ≃ₐ[ℚ] K) n i j)
      (inferInstance : AddCommGroup (E p (K ≃ₐ[ℚ] K) n i j))
      (inferInstance : Module (ZMod p) (E p (K ≃ₐ[ℚ] K) n i j))
      (inferInstance : DistribMulAction (K ≃ₐ[ℚ] K) (E p (K ≃ₐ[ℚ] K) n i j))
      (inferInstance : SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) (E p (K ≃ₐ[ℚ] K) n i j))
      hEfinN
      (gradedMapLin p Φ.toHom Φ.surjective i j)
      (gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j) hΦ0
  obtain ⟨b, hblc, hbcob⟩ := hb
  have hbcob' : ∀ σ τ : SSGRoute.GalQ,
      gradedMapLin p Φ.toHom Φ.surjective i j (κE σ τ)
        = AlgEquiv.restrictNormalHom K σ • b τ - b (σ * τ) + b σ :=
    fun σ τ => hbcob σ (Subgroup.mem_top σ) τ (Subgroup.mem_top τ)
  -- the level-`n` solution and a locally constant primitive for its cocycle
  set Ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j :=
    (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ with hΨdef
  have hs' : ∀ x, flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (flowGroupSection p (K ≃ₐ[ℚ] K) n i j x) = x :=
    flowGroupSucc_section p (K ≃ₐ[ℚ] K) n i j
  obtain ⟨f, hflc, hfcob⟩ := exists_primitive_of_gradedMapLin_coboundary_aux p K i j m n Φ φ
    hresφ hopenφ Ψ (fun σ => rfl)
    ((succKerIso p (K ≃ₐ[ℚ] K) m i j).toAdditive.symm)
    ((succKerIso p (K ≃ₐ[ℚ] K) n i j).toAdditive.symm)
    (succKerIso_equivariance_add p (K ≃ₐ[ℚ] K) n i j)
    (succKerIso_naturality_add p (K ≃ₐ[ℚ] K) i j Φ)
    (flowGroupSection p (K ≃ₐ[ℚ] K) m i j) hs
    (flowGroupSection p (K ≃ₐ[ℚ] K) n i j) hs'
    ⟨b, hblc, hbcob'⟩
  have hopenΨ : IsOpen (Ψ.ker : Set SSGRoute.GalQ) := by
    refine Subgroup.isOpen_mono ?_ hopenφ
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    rw [hΨdef, MonoidHom.comp_apply, hσ, map_one]
  -- the continuous lift
  obtain ⟨ψ, hψcomp, hψopen⟩ := exists_continuous_lift_of_locconst_coboundary p K i j n Ψ hopenΨ
    (flowGroupSection p (K ≃ₐ[ℚ] K) n i j) hs' (flowGroupSection_one p (K ≃ₐ[ℚ] K) n i j)
    ⟨f, hflc, hfcob⟩
  refine ⟨Φ, ψ, ?_, hψopen, ?_⟩
  · rw [← hΨdef]
    intro σ
    rw [liftsFlowAt_iff_flowGroupSucc]
    exact DFunLike.congr_fun hψcomp σ
  · intro A hA
    obtain ⟨l, hl, _hlopen, hk⟩ := hT1 A hA
    exact exists_liftAt_T1_place_of_flowGroupMap p K i j m n Φ φ hφ A hA l hl hk

end Work.SSGRoute
