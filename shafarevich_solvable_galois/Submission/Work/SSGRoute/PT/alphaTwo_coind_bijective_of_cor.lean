import Mathlib
import Submission.Work.SSGRoute.PT.alphaTwo_base_case
import Submission.Work.SSGRoute.PT.AlphaPairing
import Submission.Work.SSGRoute.PT.alphaTwo_evalHom
import Submission.Work.SSGRoute.PT.frobenius_coindAux
import Submission.Work.SSGRoute.PT.shapiro_H0_coind
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base case of Milne's `α²`-dévissage: `α²(G, Coind^G_U M)` from the corestriction

This file proves `Work.SSGRoute.PT.alphaTwo_coind_bijective_of_cor`: for an open subgroup
`U ≤ G` of finite index, a `U`-module `M` and a `G`-module `C`, if

* post-composition with the corestriction `cor : H²(U,C) →+ H²(G,C)` is a bijection
  `Hom(M^U, H²(U,C)) → Hom(M^U, H²(G,C))` (Milne's condition `(β)`), and
* `α²(U, M) : H²(U, Hom_ℤ(M,C)) →+ Hom(M^U, H²(U,C))` is bijective,

then `α²(G, Coind^G_U M)` is bijective.  This is the *base case* of the `α²`-dévissage of Milne,
*Arithmetic Duality Theorems*, Theorem I.1.8, the `U`-input being the (trivial-action) base case
over `U`.

The mathematical content is the **Shapiro/cup square** (`(α)`)
`alphaTwo_coind_cor_shapiro`: under Shapiro's isomorphism in degrees `0` and `2` and the
Frobenius identification `Hom_ℤ(Coind^G_U M, C) ≅ Coind^G_U Hom_ℤ(M,C)`, the cup-product pairing
over `G` of the coinduced module is the corestriction of the cup-product pairing over `U`.  It is
assembled here from the three proved ingredients of `alphaTwo_base_case.lean`:

* `phiH2_mapH2_coindMap` / `mapH2_coindMap_shapiroEquiv_symm` — naturality of Shapiro's
  isomorphism in the coefficients;
* `evalHom_eq_trace_comp` — the coefficient identity `(α)(ii)`, i.e. Milne's "sum over the
  cosets `G/U`" computation;
* `alphaTwo_evalHom` — `α²` is cupping, i.e. `mapH2` of the coefficient evaluation.

The writing `Hom(M^U, H²(G,C)) ≅ Hom((Coind^G_U M)^G, H²(G,C))` used in the assembly is
Shapiro's lemma in degree `0` (`shapiroH0AddEquiv`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Classical

namespace Work.SSGRoute.PT

namespace AlphaTwoCoind

variable {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [DistribMulAction G M]
  {N : Type} [AddCommGroup N] [DistribMulAction G N]

/-- `mapH2` depends only on the underlying additive map, not on the proof of equivariance. -/
theorem mapH2_congr (φ : M →+ N) (h₁ h₂ : Work.GroupCohomology.IsEquivariant G φ) :
    Work.AbsoluteKummer.mapH2 φ h₁ = Work.AbsoluteKummer.mapH2 φ h₂ := by
  apply AddMonoidHom.ext
  intro x
  have key : ∀ c : Work.AbsoluteKummer.Z2 G M,
      Work.AbsoluteKummer.mapH2 φ h₁ (Work.AbsoluteKummer.H2π G M c)
        = Work.AbsoluteKummer.mapH2 φ h₂ (Work.AbsoluteKummer.H2π G M c) := by
    intro c
    exact (Work.AbsoluteKummer.mapH2_H2π φ h₁ c).trans
      ((congrArg (Work.AbsoluteKummer.H2π G N) (Subtype.ext rfl)).trans
        (Work.AbsoluteKummer.mapH2_H2π φ h₂ c).symm)
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype) x
  subst hc
  exact key c

/-- Functoriality of `mapH2` at an arbitrary element. -/
theorem mapH2_comp_apply {P : Type} [AddCommGroup P] [DistribMulAction G P]
    (φ : M →+ N) (ψ : N →+ P) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ) (z : Work.AbsoluteKummer.H2 G M) :
    Work.AbsoluteKummer.mapH2 ψ hψ (Work.AbsoluteKummer.mapH2 φ hφ z)
      = Work.AbsoluteKummer.mapH2 (ψ.comp φ) (hψ.comp hφ) z := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype) z
  subst hc
  exact (Work.AbsoluteKummer.mapH2_comp_H2π φ ψ hφ hψ c).symm

/-- `mapH2` of the identity is the identity. -/
theorem mapH2_id_apply (h : Work.GroupCohomology.IsEquivariant G (AddMonoidHom.id M))
    (x : Work.AbsoluteKummer.H2 G M) :
    Work.AbsoluteKummer.mapH2 (AddMonoidHom.id M) h x = x := by
  rw [mapH2_congr (AddMonoidHom.id M) h
    (Work.GroupCohomology.isEquivariant_id (G := G) (A := M))]
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype) x
  subst hc
  exact Work.AbsoluteKummer.mapH2_id_H2π c

/-- Transport of `mapH2` of an element along an equality of coefficient maps. -/
theorem mapH2_apply_eq_of_eq {M' : Type} [AddCommGroup M'] [DistribMulAction G M']
    (φ ψ : M →+ M') (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ) (h : φ = ψ)
    (x : Work.AbsoluteKummer.H2 G M) :
    Work.AbsoluteKummer.mapH2 φ hφ x = Work.AbsoluteKummer.mapH2 ψ hψ x := by
  cases h
  exact congrFun (congrArg DFunLike.coe (mapH2_congr φ hφ hψ)) x

/-- **`mapH2` of an equivariant additive bijection is a bijection.** -/
theorem mapH2_bijective_of_bijective {M' : Type} [AddCommGroup M'] [DistribMulAction G M']
    (φ : M →+ M') (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hb : Function.Bijective φ) :
    Function.Bijective (Work.AbsoluteKummer.mapH2 φ hφ) := by
  set F : M ≃+ M' := AddEquiv.ofBijective φ hb with hF
  have hFcoe : ∀ x : M, F x = φ x := fun x => rfl
  have hψ : Work.GroupCohomology.IsEquivariant G F.symm.toAddMonoidHom := by
    intro g n
    apply F.injective
    have h1 : F (F.symm (g • n)) = g • n := AddEquiv.apply_symm_apply F (g • n)
    have h2 : F (g • F.symm n) = g • n := by
      calc F (g • F.symm n) = φ (g • F.symm n) := hFcoe (g • F.symm n)
        _ = g • φ (F.symm n) := hφ g (F.symm n)
        _ = g • F (F.symm n) := by rw [hFcoe (F.symm n)]
        _ = g • n := by rw [AddEquiv.apply_symm_apply]
    exact h1.trans h2.symm
  have hleft : ∀ x : Work.AbsoluteKummer.H2 G M,
      Work.AbsoluteKummer.mapH2 F.symm.toAddMonoidHom hψ
        (Work.AbsoluteKummer.mapH2 φ hφ x) = x := by
    intro x
    have hcomp : F.symm.toAddMonoidHom.comp φ = AddMonoidHom.id M := by
      ext y
      show F.symm.toAddMonoidHom (φ y) = y
      calc F.symm.toAddMonoidHom (φ y) = F.symm (φ y) := rfl
        _ = F.symm (F y) := by rw [← hFcoe y]
        _ = y := AddEquiv.symm_apply_apply F y
    refine (mapH2_comp_apply φ F.symm.toAddMonoidHom hφ hψ x).trans ?_
    refine (mapH2_apply_eq_of_eq (F.symm.toAddMonoidHom.comp φ) (AddMonoidHom.id M)
      (hψ.comp hφ) (Work.GroupCohomology.isEquivariant_id (G := G) (A := M))
      hcomp x).trans ?_
    exact mapH2_id_apply _ x
  have hright : ∀ x : Work.AbsoluteKummer.H2 G M',
      Work.AbsoluteKummer.mapH2 φ hφ
        (Work.AbsoluteKummer.mapH2 F.symm.toAddMonoidHom hψ x) = x := by
    intro x
    have hcomp : φ.comp F.symm.toAddMonoidHom = AddMonoidHom.id M' := by
      ext y
      show φ (F.symm.toAddMonoidHom y) = y
      calc φ (F.symm.toAddMonoidHom y) = φ (F.symm y) := rfl
        _ = F (F.symm y) := by rw [hFcoe (F.symm y)]
        _ = y := AddEquiv.apply_symm_apply F y
    refine (mapH2_comp_apply F.symm.toAddMonoidHom φ hψ hφ x).trans ?_
    refine (mapH2_apply_eq_of_eq (φ.comp F.symm.toAddMonoidHom) (AddMonoidHom.id M')
      (hφ.comp hψ) (Work.GroupCohomology.isEquivariant_id (G := G) (A := M'))
      hcomp x).trans ?_
    exact mapH2_id_apply _ x
  constructor
  · intro x y hxy
    rw [← hleft x, ← hleft y, hxy]
  · intro y
    exact ⟨Work.AbsoluteKummer.mapH2 F.symm.toAddMonoidHom hψ y, hright y⟩

/-- **Precomposition with an additive equivalence is a bijection on homs.** -/
theorem precomp_addEquiv_bijective {L : Type} [AddCommGroup L] {M' : Type} [AddCommGroup M']
    {X : Type} [AddCommGroup X] (e : L ≃+ M') :
    Function.Bijective (fun ψ : M' →+ X => ψ.comp e.toAddMonoidHom) := by
  constructor
  · intro f g hfg
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    exact congrFun (congrArg DFunLike.coe hfg) y
  · intro f
    exact ⟨f.comp e.symm.toAddMonoidHom, by
      ext x
      exact congrArg f (AddEquiv.symm_apply_apply e x)⟩

end AlphaTwoCoind

section ShapiroCup

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Evaluation at `1` of a `G`-invariant element of the coinduced module, as an element of the
`U`-invariants: `(shapiroH0AddEquiv U n : M) = (n : Coind G U M) 1`. -/
theorem shapiroH0AddEquiv_coe (U : Subgroup G)
    {M : Type} [AddCommGroup M] [DistribMulAction U M]
    (n : ↥(Work.GroupCohomology.invariants G (Coind G U M))) :
    ((shapiroH0AddEquiv U n : M)) = (n : Coind G U M) 1 := rfl

/-- **The coefficient identity `(α)(ii)` in the `CoindMap` form.**  Evaluating the coefficient map
`ConjHom.evalHom n` at the Frobenius transport of `Φ` is the trace of the coinduced element
`g ↦ evalHom (n 1) ((psiAux U Φ) g)`. -/
theorem evalHom_eq_trace_coindMap
    (U : Subgroup G) [U.FiniteIndex] [Fintype (G ⧸ U)]
    {M : Type} [AddCommGroup M] [DistribMulAction U M]
    {C : Type} [AddCommGroup C] [DistribMulAction G C]
    (n : ↥(Work.GroupCohomology.invariants G (Coind G U M)))
    (Φ : ConjHom (Coind G U M) C) :
    trace U C (CoindMap U (ConjHom.evalHom (C := C) ((shapiroH0AddEquiv U n : M)))
        (evalHom_smul (C := C) ((shapiroH0AddEquiv U n : M)) (shapiroH0AddEquiv U n).2)
        ((frobeniusEquiv (M := M) (C := C) U) Φ))
      = (ConjHom.evalHom (C := C) (n : Coind G U M)) Φ := by
  have key : (ConjHom.evalHom (C := C) (n : Coind G U M)) Φ
      = Φ (n : Coind G U M) := rfl
  exact (evalHom_eq_trace_comp U M C (n : Coind G U M) n.2 Φ).symm.trans key.symm

/-- **The Shapiro/cup square** (Milne's condition `(α)`): the cup-product pairing of the coinduced
module over `G` is the corestriction of the cup-product pairing over `U`, under Shapiro's
isomorphisms in degrees `0` and `2` and the Frobenius identification of the coefficients. -/
theorem alphaTwo_coind_cor_shapiro
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    {M : Type} [AddCommGroup M] [DistribMulAction U M]
    {C : Type} [AddCommGroup C] [DistribMulAction G C]
    (x : Work.AbsoluteKummer.H2 G (ConjHom (Coind G U M) C))
    (n : ↥(Work.GroupCohomology.invariants G (Coind G U M))) :
    alphaTwo (G := G) (N := Coind G U M) (C := C) x n
      = corH2 U hUo C
          (alphaTwo (G := U) (N := M) (C := C)
            (shapiroEquiv U hUo (M := ConjHom M C)
              (Work.AbsoluteKummer.mapH2 (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
                (isEquivariant_frobeniusEquiv (M := M) (C := C) U) x))
            (shapiroH0AddEquiv U n)) := by
  have hfrob : Work.GroupCohomology.IsEquivariant G
      (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom :=
    isEquivariant_frobeniusEquiv (M := M) (C := C) U
  have hθ : Work.GroupCohomology.IsEquivariant U
      (ConjHom.evalHom (C := C) ((shapiroH0AddEquiv U n : M))) :=
    evalHom_smul (C := C) ((shapiroH0AddEquiv U n : M)) (shapiroH0AddEquiv U n).2
  have hcm : Work.GroupCohomology.IsEquivariant G
      (CoindMap U (ConjHom.evalHom (C := C) ((shapiroH0AddEquiv U n : M))) hθ) :=
    isEquivariant_coindMap U (ConjHom.evalHom (C := C) ((shapiroH0AddEquiv U n : M))) hθ
  -- `(α)(i)`: Shapiro naturality in the coefficients
  have hnat : Work.AbsoluteKummer.mapH2
        (CoindMap U (ConjHom.evalHom (C := C) ((shapiroH0AddEquiv U n : M))) hθ) hcm
        ((shapiroEquiv U hUo (M := ConjHom M C)).symm
          (shapiroEquiv U hUo (M := ConjHom M C)
            (Work.AbsoluteKummer.mapH2 (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
              hfrob x)))
      = (shapiroEquiv U hUo (M := C)).symm
          (Work.AbsoluteKummer.mapH2
            (ConjHom.evalHom (C := C) ((shapiroH0AddEquiv U n : M))) hθ
            (shapiroEquiv U hUo (M := ConjHom M C)
              (Work.AbsoluteKummer.mapH2 (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
                hfrob x))) :=
    congrFun (congrArg DFunLike.coe (mapH2_coindMap_shapiroEquiv_symm U hUo
      (ConjHom.evalHom (C := C) ((shapiroH0AddEquiv U n : M))) hθ))
      (shapiroEquiv U hUo (M := ConjHom M C)
        (Work.AbsoluteKummer.mapH2 (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom hfrob x))
  -- `(α)(ii)`: the coefficient identity
  have hcoeff : (trace U C).comp
        ((CoindMap U (ConjHom.evalHom (C := C) ((shapiroH0AddEquiv U n : M))) hθ).comp
          (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom)
      = ConjHom.evalHom (C := C) (n : Coind G U M) := by
    ext Φ
    exact evalHom_eq_trace_coindMap U n Φ
  -- unfold the two sides
  rw [alphaTwo_evalHom (x := x) (n := n)]
  rw [corH2_apply, alphaTwo_evalHom]
  symm
  refine (congrArg (Work.AbsoluteKummer.mapH2 (trace U C) (isEquivariant_trace U C)) hnat.symm).trans ?_
  refine (congrArg (Work.AbsoluteKummer.mapH2 (trace U C) (isEquivariant_trace U C))
    (congrArg
      (Work.AbsoluteKummer.mapH2
        (CoindMap U (ConjHom.evalHom (C := C) ((shapiroH0AddEquiv U n : M))) hθ) hcm)
      (AddEquiv.symm_apply_apply (shapiroEquiv U hUo (M := ConjHom M C))
        (Work.AbsoluteKummer.mapH2
          (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom hfrob x)))).trans ?_
  refine (congrArg (Work.AbsoluteKummer.mapH2 (trace U C) (isEquivariant_trace U C))
    (AlphaTwoCoind.mapH2_comp_apply (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
      (CoindMap U (ConjHom.evalHom (C := C) ((shapiroH0AddEquiv U n : M))) hθ)
      hfrob hcm x)).trans ?_
  exact (AlphaTwoCoind.mapH2_comp_apply
      ((CoindMap U (ConjHom.evalHom (C := C) ((shapiroH0AddEquiv U n : M))) hθ).comp
        (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom)
      (trace U C) (hcm.comp hfrob) (isEquivariant_trace U C) x).trans
    (AlphaTwoCoind.mapH2_apply_eq_of_eq
      ((trace U C).comp
        ((CoindMap U (ConjHom.evalHom (C := C) ((shapiroH0AddEquiv U n : M))) hθ).comp
          (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom))
      (ConjHom.evalHom (C := C) (n : Coind G U M))
      ((isEquivariant_trace U C).comp (hcm.comp hfrob))
      (evalHom_smul (C := C) (n : Coind G U M) n.2) hcoeff x)

end ShapiroCup

theorem alphaTwo_coind_bijective_of_cor
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    {M : Type} [AddCommGroup M] [DistribMulAction U M]
    {C : Type} [AddCommGroup C] [DistribMulAction G C]
    (hcor : Function.Bijective (fun φ : ↥(Work.GroupCohomology.invariants U M) →+
        Work.AbsoluteKummer.H2 U C =>
      (Work.SSGRoute.PT.corH2 U hUo C).comp φ))
    (hU : Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := U) (N := M) (C := C))) :
    Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := G)
      (N := Work.SSGRoute.PT.Coind G U M) (C := C)) := by
  -- Shapiro/Frobenius on `H²`
  have hPhi : Function.Bijective (fun x : Work.AbsoluteKummer.H2 G
        (ConjHom (Coind G U M) C) =>
      shapiroEquiv U hUo (M := ConjHom M C)
        (Work.AbsoluteKummer.mapH2
          (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
          (isEquivariant_frobeniusEquiv (M := M) (C := C) U) x)) :=
    (shapiroEquiv U hUo (M := ConjHom M C)).bijective.comp
      (AlphaTwoCoind.mapH2_bijective_of_bijective
        (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
        (isEquivariant_frobeniusEquiv (M := M) (C := C) U)
        (frobeniusEquiv (M := M) (C := C) U).bijective)
  -- post-composition with the corestriction
  have hSig : Function.Bijective (fun φ : ↥(Work.GroupCohomology.invariants U M) →+
        Work.AbsoluteKummer.H2 U C => (corH2 U hUo C).comp φ) := hcor
  -- precomposition with the degree-zero Shapiro isomorphism
  have hLam : Function.Bijective (fun ψ : ↥(Work.GroupCohomology.invariants U M) →+
        Work.AbsoluteKummer.H2 G C =>
      ψ.comp (shapiroH0AddEquiv U).toAddMonoidHom) :=
    AlphaTwoCoind.precomp_addEquiv_bijective (shapiroH0AddEquiv U)
  -- the Shapiro/cup square, pointwise
  have hsq : ∀ x : Work.AbsoluteKummer.H2 G (ConjHom (Coind G U M) C),
      alphaTwo (G := G) (N := Coind G U M) (C := C) x
        = (fun ψ : ↥(Work.GroupCohomology.invariants U M) →+ Work.AbsoluteKummer.H2 G C =>
            ψ.comp (shapiroH0AddEquiv U).toAddMonoidHom)
          ((fun φ : ↥(Work.GroupCohomology.invariants U M) →+ Work.AbsoluteKummer.H2 U C =>
              (corH2 U hUo C).comp φ)
            (alphaTwo (G := U) (N := M) (C := C)
              (shapiroEquiv U hUo (M := ConjHom M C)
                (Work.AbsoluteKummer.mapH2
                  (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
                  (isEquivariant_frobeniusEquiv (M := M) (C := C) U) x)))) := by
    intro x
    apply AddMonoidHom.ext
    intro n
    exact alphaTwo_coind_cor_shapiro U hUo x n
  -- the composite of the four bijections
  have hmain : Function.Bijective (fun x : Work.AbsoluteKummer.H2 G
        (ConjHom (Coind G U M) C) =>
      (fun ψ : ↥(Work.GroupCohomology.invariants U M) →+ Work.AbsoluteKummer.H2 G C =>
          ψ.comp (shapiroH0AddEquiv U).toAddMonoidHom)
        ((fun φ : ↥(Work.GroupCohomology.invariants U M) →+ Work.AbsoluteKummer.H2 U C =>
            (corH2 U hUo C).comp φ)
          (alphaTwo (G := U) (N := M) (C := C)
            (shapiroEquiv U hUo (M := ConjHom M C)
              (Work.AbsoluteKummer.mapH2
                (frobeniusEquiv (M := M) (C := C) U).toAddMonoidHom
                (isEquivariant_frobeniusEquiv (M := M) (C := C) U) x))))) :=
    hLam.comp (hSig.comp (hU.comp hPhi))
  rw [funext hsq]
  exact hmain

end Work.SSGRoute.PT
