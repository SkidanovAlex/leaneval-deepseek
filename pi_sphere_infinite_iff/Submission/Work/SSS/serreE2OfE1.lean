import Mathlib
import Submission.Work.SSS.Statements
import Submission.Work.SSS.TensorFG
import Submission.Work.SSS.serreFiltration
import Submission.Work.SSS.hZeroRetract
import Submission.Work.SSS.ExpTens
import Submission.Work.SSS.expTensHomologyZero
import Submission.Work.SSS.singularCoeffFG
import Submission.Work.SSS.tensorComplexIsoExpTens
import Submission.Work.SSS.E2Aux.finiteHomologyOfTensorComplex

/-!
# From the first page of the Serre spectral sequence to the E² page

Assuming the first page theorem `Work.SSS.SerreE1Statement` — the E¹ row complex of the Serre
filtration of `C_*(E)` is the normalized singular chain complex of the base tensored with the
homology of the fibre, `N_*(B) ⊗ H_t(F)` — we deduce `Work.SSS.SerreE2Statement`, the three
Serre-class statements about the E² page `E²_{s,t} ≅ H_s(B; H_t F)`:

* the bottom row is f.g. only if `H_n(B)` is (`H_0(F) ≅ ℤ^k`, `k ≥ 1`, splits off `H_n(B)` as a
  direct summand of `H_n(N_*(B) ⊗ H_0 F)`);
* `E²_{s,t}` is f.g. when `H_s(B)`, `H_{s-1}(B)` and `H_t(F)` are (the universal coefficient theorem
  `Work.SSS.tensorHomology`, proved here as `Work.SSS.E2Aux.tensorComplexHomologyFinite` from the
  naive tensor complex `Work.SSS.expTens`, `Work.SSS.tensorComplexIsoExpTens`, and the universal
  coefficient theorem `Work.SSS.expTensFG`, proved in `Submission/Work/SSS/singularCoeffFG.lean`);
* `E²_{0,t} ≅ H_0(N_*(B) ⊗ H_t F) ≅ H_0(N_*(B)) ⊗ H_t F ≅ H_t(F)` (`B` is path connected, so
  `H_0(N_*(B)) ≅ H_0(B) ≅ ℤ` by the singular `H_0` isomorphism).

The E² page is `H_s` of the E¹ row complex by definition (`Work.SSS.E2`), so each statement is
immediate from the E¹ isomorphism together with one of these three computations of homology.
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

noncomputable section

/-- The coproduct of copies of `ℤ` in `ModuleCat ℤ` is a free module (its underlying module is the
direct sum of the copies, `ι →₀ ℤ`, via `ModuleCat.finsuppCoconeIsColimit`). -/
theorem E2Aux.free_coprod_int (α : Type) :
    Module.Free ℤ ((∐ (fun _ : α => ModuleCat.of ℤ ℤ)) : ModuleCat ℤ) := by
  haveI : IsColimit (ModuleCat.finsuppCocone ℤ ℤ α) := ModuleCat.finsuppCoconeIsColimit ℤ ℤ α
  let e : (∐ (fun _ : α => ModuleCat.of ℤ ℤ) : ModuleCat ℤ) ≅ ModuleCat.of ℤ (α →₀ ℤ) :=
    (coproductIsCoproduct (fun _ : α => ModuleCat.of ℤ ℤ)).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ α)
  exact Module.Free.of_basis ((Module.Free.chooseBasis ℤ (α →₀ ℤ)).map e.toLinearEquiv.symm)

/-- **The normalized chain complex is degreewise free.**  In degree `n`, the normalized chain
complex of a simplicial set with `ℤ`-coefficients is a coproduct of copies of `ℤ`, one for each
nondegenerate `n`-simplex (`SSet.isColimitCofanNormalizedChainComplex`), hence free. -/
theorem E2Aux.normalizedChainComplex_free (X : SSet) (n : ℕ) :
    Module.Free ℤ ((X.normalizedChainComplex (ModuleCat.of ℤ ℤ)).X n) := by
  let F : X.nonDegenerate n → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
  let c₂ : Cofan F := Cofan.mk (∐ F) (Sigma.ι F)
  have h₂ : IsColimit c₂ := coproductIsCoproduct F
  have e : (∐ F) ≅ (X.normalizedChainComplex (ModuleCat.of ℤ ℤ)).X n :=
    IsColimit.coconePointUniqueUpToIso (F := Discrete.functor F) (s := c₂)
      (t := X.cofanNormalizedChainComplex (ModuleCat.of ℤ ℤ) n) h₂
      (X.isColimitCofanNormalizedChainComplex (ModuleCat.of ℤ ℤ) n)
  have e' : (∐ F) ≅ ModuleCat.of ℤ (X.nonDegenerate n →₀ ℤ) :=
    IsColimit.coconePointUniqueUpToIso (F := Discrete.functor F) (s := c₂)
      (t := ModuleCat.finsuppCocone ℤ ℤ (X.nonDegenerate n)) h₂
      (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (X.nonDegenerate n))
  exact Module.Free.of_basis ((Module.Free.chooseBasis ℤ (X.nonDegenerate n →₀ ℤ)).map
    (e'.toLinearEquiv.symm.trans e.toLinearEquiv))

/-- Finiteness of `ℤ`-modules transfers across an isomorphism. -/
theorem E2Aux.finite_of_iso {A B : ModuleCat ℤ} (e : A ≅ B) (h : Module.Finite ℤ A) :
    Module.Finite ℤ B := by
  haveI := h
  exact Module.Finite.equiv e.toLinearEquiv

/-- The normalized chain complex of the singular simplicial set of `B`, with `ℤ`-coefficients. -/
abbrev sNK (B : Type) [TopologicalSpace B] : ChainComplex (ModuleCat ℤ) ℕ :=
  (TopCat.toSSet.obj (TopCat.of B)).normalizedChainComplex (ModuleCat.of ℤ ℤ)

/-- **Finiteness transfer, normalized chains from singular homology.**  The normalized and the
unnormalized (alternating face map) chain complexes of a simplicial set are homotopy equivalent
(Mathlib's `SSet.homotopyEquivNormalizedChainComplex`), so their homologies are isomorphic and
finiteness transfers in either direction. -/
theorem E2Aux.finite_sNK_homology_of_finite_HZ (B : Type) [TopologicalSpace B] (n : ℕ)
    (h : Module.Finite ℤ (Work.PiS.HZ B n)) : Module.Finite ℤ ((sNK B).homology n) :=
  E2Aux.finite_of_iso (((SSet.homotopyEquivNormalizedChainComplex
    (TopCat.toSSet.obj (TopCat.of B)) (ModuleCat.of ℤ ℤ)).toHomologyIso n)) h

/-- Finiteness transfer in the reverse direction (see `E2Aux.finite_sNK_homology_of_finite_HZ`). -/
theorem E2Aux.finite_HZ_of_finite_sNK_homology (B : Type) [TopologicalSpace B] (n : ℕ)
    (h : Module.Finite ℤ ((sNK B).homology n)) : Module.Finite ℤ (Work.PiS.HZ B n) :=
  E2Aux.finite_of_iso (((SSet.homotopyEquivNormalizedChainComplex
    (TopCat.toSSet.obj (TopCat.of B)) (ModuleCat.of ℤ ℤ)).toHomologyIso n).symm) h

/-- `π₀(B)` being trivial at a point means `B` is path connected. -/
theorem E2Aux.pathConnectedSpace_of_subsingleton_pi_zero {B : Type} [TopologicalSpace B] (b₀ : B)
    (hb : Subsingleton (HomotopyGroup.Pi 0 B b₀)) : PathConnectedSpace B := by
  have hZ : Subsingleton (ZerothHomotopy B) :=
    ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := B) (x := b₀)).symm.injective
      (Subsingleton.elim _ _)⟩
  exact pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk b₀⟩, hZ⟩

/-- **`H_0` of the normalized chains is `ℤ` for a path connected space.**  The normalized chain
complex is homotopy equivalent to the singular chain complex, and for path connected `B` the
augmentation `TopCat.singularHomology₀ε` is an isomorphism `H_0(B; ℤ) ≅ ℤ`. -/
theorem E2Aux.normalizedHomologyZeroIsoInt (B : Type) [TopologicalSpace B]
    (hpc : PathConnectedSpace B) : Nonempty ((sNK B).homology 0 ≅ 𝟙_ (ModuleCat ℤ)) := by
  have hpc' : PathConnectedSpace (TopCat.of B) := hpc
  haveI : PathConnectedSpace (TopCat.of B) := hpc'
  haveI hiso : IsIso (TopCat.singularHomology₀ε (TopCat.of B) (ModuleCat.of ℤ ℤ)) := inferInstance
  exact ⟨Iso.trans ((SSet.homotopyEquivNormalizedChainComplex (TopCat.toSSet.obj (TopCat.of B))
      (ModuleCat.of ℤ ℤ)).toHomologyIso 0).symm
    (@asIso _ _ _ _ (TopCat.singularHomology₀ε (TopCat.of B) (ModuleCat.of ℤ ℤ)) hiso)⟩

/-- **Finiteness of `H_n(K ⊗ M)` for a degreewise free complex `K`** (the universal coefficient
theorem read in the Serre class of finitely generated abelian groups), on Mathlib's tensor complex
`Work.SSS.tensorComplex K M`. -/
theorem E2Aux.tensorComplexHomologyFinite (K : ChainComplex (ModuleCat ℤ) ℕ) (M : ModuleCat ℤ)
    (hK : ∀ n : ℕ, Module.Free ℤ (K.X n)) (hM : Module.Finite ℤ M) (n : ℕ)
    (h1 : Module.Finite ℤ (K.homology n)) (h2 : Module.Finite ℤ (K.homology (n - 1))) :
    Module.Finite ℤ ((Work.SSS.tensorComplex K M).homology n) := by
  obtain ⟨e⟩ := Work.SSS.tensorComplexIsoExpTens K M
  have hfin : Module.Finite ℤ ((Work.SSS.expTens K M).homology n) :=
    Work.SSS.expTensFG K M hK hM n h1 h2
  exact E2Aux.finite_of_iso
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso e).symm hfin

/-- **The E² page from the first page.**  Assuming the first page theorem `Work.SSS.serreE1` (the E¹
row complex of the Serre filtration is `N_*(B) ⊗ H_t(F)`, `N_*` the normalized chains of `Sing B`),
the E² page of the Serre filtration is `H_s(N_*(B) ⊗ H_t(F))`, and the three Serre-class statements
of `Work.SSS.SerreE2Statement` follow from the universal coefficient theorem
(`Work.SSS.tensorHomology`), from `H_0(F)` being free of positive rank, and from `B` being path
connected. -/
theorem serreE2OfE1 (hE1 : Work.SSS.SerreE1Statement) : Work.SSS.SerreE2Statement := by
  intro E B _ _ p e₀ hfib hconn
  obtain ⟨ξ, hξ⟩ := Work.SSS.serreFiltration E B p
  have hfree : ∀ n : ℕ, Module.Free ℤ ((sNK B).X n) :=
    fun n => E2Aux.normalizedChainComplex_free (TopCat.toSSet.obj (TopCat.of B)) n
  have hpc : PathConnectedSpace B :=
    E2Aux.pathConnectedSpace_of_subsingleton_pi_zero (p e₀) hconn.1
  refine ⟨ξ, ?_, ?_, ?_⟩
  · -- the bottom row: `H_n(B)` is a direct summand of `H_n(N_*(B) ⊗ H_0(F))`
    intro n hn
    obtain ⟨e₁⟩ := hE1 E B p e₀ hfib hconn ξ hξ 0
    have hE := (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso e₁
    have hfin : Module.Finite ℤ ((Work.SSS.tensorComplex (sNK B)
        (Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) 0)).homology n) :=
      E2Aux.finite_of_iso hE hn
    obtain ⟨aug, pt, hcomp⟩ :=
      Work.SSS.hZeroRetract (F := Work.StemsB.fibre p (p e₀)) ⟨e₀, rfl⟩
    exact E2Aux.finite_HZ_of_finite_sNK_homology B n
      (E2Aux.finiteHomologyOfTensorComplex pt aug hcomp n hfin)
  · -- `E²_{s,t}` is f.g. when `H_s(B)`, `H_{s-1}(B)` and `H_t(F)` are
    intro s t hBs hBs1 hFt
    obtain ⟨e₁⟩ := hE1 E B p e₀ hfib hconn ξ hξ t
    have hE := (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) s).mapIso e₁
    have hfin : Module.Finite ℤ ((Work.SSS.tensorComplex (sNK B)
        (Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) t)).homology s) :=
      E2Aux.tensorComplexHomologyFinite (sNK B) (Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) t)
        hfree hFt s (E2Aux.finite_sNK_homology_of_finite_HZ B s hBs)
        (E2Aux.finite_sNK_homology_of_finite_HZ B (s - 1) hBs1)
    exact E2Aux.finite_of_iso hE.symm hfin
  · -- the left column: `E²_{0,t} ≅ H_0(N_*(B)) ⊗ H_t(F) ≅ H_t(F)`
    intro t
    constructor
    · intro hFt
      obtain ⟨e₁⟩ := hE1 E B p e₀ hfib hconn ξ hξ t
      have hE := (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0).mapIso e₁
      obtain ⟨hz⟩ := E2Aux.normalizedHomologyZeroIsoInt B hpc
      have h0 : Module.Finite ℤ ((sNK B).homology 0) :=
        E2Aux.finite_of_iso hz.symm (Module.Finite.self ℤ)
      have hfin : Module.Finite ℤ ((Work.SSS.tensorComplex (sNK B)
          (Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) t)).homology 0) :=
        E2Aux.tensorComplexHomologyFinite (sNK B) (Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) t)
          hfree hFt 0 h0 h0
      exact E2Aux.finite_of_iso hE.symm hfin
    · intro hE2
      obtain ⟨e₁⟩ := hE1 E B p e₀ hfib hconn ξ hξ t
      have hE := (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0).mapIso e₁
      have hfin : Module.Finite ℤ ((Work.SSS.tensorComplex (sNK B)
          (Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) t)).homology 0) :=
        E2Aux.finite_of_iso hE hE2
      -- `H_0` of the tensor complex: go to the naive tensor complex
      -- (`Work.SSS.tensorComplexIsoExpTens`), use `H_0(K ⊗ M) ≅ H_0(K) ⊗ M`
      -- (`Work.SSS.expTensHomologyZero`, no flatness needed) and `H_0(N_*(B)) ≅ ℤ`.
      obtain ⟨ebr⟩ := Work.SSS.tensorComplexIsoExpTens (sNK B)
        (Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) t)
      obtain ⟨h0⟩ := Work.SSS.expTensHomologyZero (sNK B)
        (Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) t)
      obtain ⟨hz⟩ := E2Aux.normalizedHomologyZeroIsoInt B hpc
      have hiso : (Work.SSS.tensorComplex (sNK B)
          (Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) t)).homology 0 ≅
          Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) t :=
        ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 0).mapIso ebr)
          ≪≫ h0 ≪≫ MonoidalCategory.tensorIso hz (Iso.refl _) ≪≫ (λ_ _)
      exact E2Aux.finite_of_iso hiso hfin

end

end Work.SSS
