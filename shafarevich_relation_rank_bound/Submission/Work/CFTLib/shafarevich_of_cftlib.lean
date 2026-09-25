import Mathlib
import Submission.CFTLib.ShafDeps
import Submission.Work.CFTLib.ProP.Galois
import Submission.Work.CFTLib.ProP.isGalois_maximalUnramifiedProPF
import Submission.Work.CFTLib.ProP.le_maximalUnramifiedProPF
import Submission.Work.CFTLib.ProP.maxAbelianSubextension
import Submission.Work.CFTLib.ProP.fg_of_finite_frattini
import Submission.Work.CFTLib.ProP.exists_finset_generates_maxUnramified
import Submission.Work.CFTLib.ProP.finrank_H1Fp_le_of_generating_finset
import Submission.Work.CFTLib.ProP.contMap_range_finrank_le_hrel
import Submission.Work.CFTLib.ProP.moduleFinite_groupCohomology_trivial
import Submission.Work.CFTLib.Bound
import Submission.Work.CFT.MaxProP.ContCohomology.FiniteLevel.H2FpCont_finite
import Submission.Work.CFTLib.ContCohomology.two_iso_H2FpCont

/-! Guidance from the project lead (the requester):

# Guidance: the shafarevich challenge from the library interfaces (profinite bookkeeping)

Hypotheses (in `Submission/CFTLib/Interfaces.lean`, do not edit): `CFTLib.RelShafBound` (inflation image
H²(Gal(K/F)) → H²(Gal(K'/F)) has dim ≤ dim H¹(Gal(K'/F)) + ρ whenever K ⊆ K' are finite Galois unramified
p-extensions of F and K' contains every unramified abelian p-extension of K) and `CFTLib.UnramifiedAbelianDegreeLe`
(unramified abelian L/K has [L:K] ≤ h_K). ρ = r₁+r₂−1+δ_p(F).
G := `MaxUnramifiedProPGaloisGroup F p` = Gal(F^{un,p}/F), F^{un,p} = `maximalUnramifiedProPF F p` ⊆ AlgebraicClosure F,
the compositum of finite Galois everywhere-unramified p-extensions (the challenge's `IsEverywhereUnramified`:
ramification index 1 at finite primes + real places stay real; bridge it to `CFTLib.IsUnramified`).
Plan:
1. Continuous H²(G,𝔽_p) with discrete 𝔽_p is the direct limit of H²(Gal(K/F),𝔽_p) over finite Galois
   unramified p-extensions K ⊆ F^{un,p} (inflation). Every continuous 2-cocycle factors through a finite quotient
   (the shafarevich fm1 run proved `exists_open_normal_cocycle_descends` — not in this workspace; reprove).
2. For such K, K' := the Galois closure over F of the compositum of all unramified abelian p-extensions of K
   inside F^{un,p}; it is finite (`hab` bounds each, and the compositum of the unramified abelian p-extensions
   of K is itself unramified abelian, so bounded) and lies in F^{un,p}. `hrel K K'` bounds the inflation image.
3. dim H²(G) ≤ sup_K dim image(H²(Gal(K/F)) → H²(Gal(K'/F))) ≤ sup_K d(Gal(K'/F)) + ρ ≤ d(G) + ρ, because an
   element of H²(G) comes from some K and its image in H²(G) factors through K' (inflation is functorial);
   and dim H¹(Gal(K/F),𝔽_p) = d(Gal(K/F)) ≤ generatorRank G (Burnside basis theorem for finite p-groups;
   generatorRank of the quotient ≤ that of G). Finite-dimensionality (H2Finite) comes out of the same bound
   provided generatorRank G is finite — G^{ab} is finite (it is a quotient of Cl(F)_p via `hab`) so d(G) < ∞
   (a pro-p group with finite Frattini quotient is finitely generated).
Delegate each step as a lemma. Useful Mathlib: `ContinuousCohomology`, `InfiniteGalois` (Krull topology,
open subgroups ↔ finite subextensions), `AlgEquiv.restrictNormalHom`.
-/

namespace Work.CFTLib

open scoped Classical
open Work.CFT.MaxProP

theorem shafarevich_of_cftlib (hrel : CFTLib.RelShafBound) (hab : CFTLib.UnramifiedAbelianDegreeLe)
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (_hpOdd : Odd p) :
    LeanEval.NumberTheory.H2Finite p (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) ∧
      (open Classical in
       LeanEval.NumberTheory.relationRank p (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) ≤
        LeanEval.NumberTheory.generatorRank (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) +
          (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F - 1) +
          (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0)) := by
  classical
  haveI hgalE : IsGalois F ↥(Work.CFTLib.ProP.E F p) :=
    Work.CFTLib.ProP.isGalois_maximalUnramifiedProPF F p
  haveI : CompactSpace (Work.CFTLib.ProP.GG F p) := inferInstance
  haveI : T2Space (Work.CFTLib.ProP.GG F p) := inferInstance
  haveI : TotallyDisconnectedSpace (Work.CFTLib.ProP.GG F p) := inferInstance
  haveI hne : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  obtain ⟨e⟩ := Work.CFTLib.ContCohomology.two_iso_H2FpCont p (Work.CFTLib.ProP.GG F p)
  obtain ⟨S, hScard, hSdense⟩ := Work.CFTLib.ProP.exists_finset_generates_maxUnramified F p hab
  refine Work.CFTLib.Shaf.h2Finite_and_relationRank_le_of_levelBound
    (p := p) (G := (Work.CFTLib.ProP.GG F p))
    (Φ := fun U => Work.CFTLib.Shaf.levelMap e U)
    (hnat := fun U V h x => Work.CFTLib.Shaf.levelMap_natural e h x)
    (hsurj := ?_) (hfin := ?_)
    (N := LeanEval.NumberTheory.generatorRank (Work.CFTLib.ProP.GG F p) +
      (NumberField.InfinitePlace.nrRealPlaces F + NumberField.InfinitePlace.nrComplexPlaces F - 1) +
      (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0))
    (hbound := ?_)
  · intro v
    refine Work.CFTLib.Shaf.exists_mem_range_levelMap e (p := p) (G := (Work.CFTLib.ProP.GG F p)) ?_ v
    intro z
    exact Work.CFT.MaxProP.H2FpCont.induction_on (p := p) (G := (Work.CFTLib.ProP.GG F p))
      (C := fun w => ∃ (U : Work.CFT.MaxProP.OpenNormal (Work.CFTLib.ProP.GG F p))
        (x : Work.CFT.MaxProP.H2FpContFamily p (Work.CFTLib.ProP.GG F p) U),
        Work.CFT.MaxProP.H2FpCont.of p (Work.CFTLib.ProP.GG F p) U x = w)
      z (fun U x => ⟨U, x, rfl⟩)
  · intro U
    haveI : Finite ((Work.CFTLib.ProP.GG F p) ⧸ U.carrier) := U.carrier.quotient_finite_of_isOpen U.isOpen
    haveI : Module.Finite (ZMod p) (Work.CFT.MaxProP.H2FpContFamily p (Work.CFTLib.ProP.GG F p) U) :=
      Work.CFTLib.ProP.moduleFinite_groupCohomology_trivial p 2 ((Work.CFTLib.ProP.GG F p) ⧸ U.carrier)
    exact inferInstance
  · intro U
    set K : IntermediateField F ↥(Work.CFTLib.ProP.E F p) :=
      IntermediateField.fixedField U.carrier with hKdef
    haveI hKfin : FiniteDimensional F K :=
      Work.CFTLib.ProP.fixedField_finiteDimensional hgalE U.isOpen
    haveI hKgal : IsGalois F K :=
      Work.CFTLib.ProP.fixedField_isGalois hgalE U.normal U.isOpen
    haveI hKnf : NumberField ↥K := NumberField.of_module_finite F ↥K
    obtain ⟨K', hle, hK'fin, hK'gal, hK'nf, hAlg, hTower, hcontains, huni, hp'⟩ :=
      Work.CFTLib.ProP.maxAbelianSubextension F p hab hgalE K
    letI : FiniteDimensional F K' := hK'fin
    letI : IsGalois F K' := hK'gal
    letI : NumberField ↥K' := hK'nf
    letI : Algebra ↥K ↥K' := hAlg
    letI : IsScalarTower F ↥K ↥K' := hTower
    haveI hU'norm : K'.fixingSubgroup.Normal :=
      (InfiniteGalois.normal_iff_isGalois K').mpr hK'gal
    have hU'open : IsOpen ((K'.fixingSubgroup : Subgroup (Work.CFTLib.ProP.GG F p)) : Set (Work.CFTLib.ProP.GG F p)) :=
      IntermediateField.fixingSubgroup_isOpen K'
    let U' : Work.CFT.MaxProP.OpenNormal (Work.CFTLib.ProP.GG F p) := ⟨K'.fixingSubgroup, hU'norm, hU'open⟩
    haveI : Finite ((Work.CFTLib.ProP.GG F p) ⧸ U'.carrier) := U'.carrier.quotient_finite_of_isOpen U'.isOpen
    haveI hfamGG : Module.Finite (ZMod p) (Work.CFT.MaxProP.H2FpContFamily p (Work.CFTLib.ProP.GG F p) U') :=
      Work.CFTLib.ProP.moduleFinite_groupCohomology_trivial p 2 ((Work.CFTLib.ProP.GG F p) ⧸ U'.carrier)
    haveI hfam : Module.Finite (ZMod p) (Work.CFT.MaxProP.H2FpContFamily p (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) U') := hfamGG
    have hfixedU' : IntermediateField.fixedField U'.carrier = K' :=
      InfiniteGalois.fixedField_fixingSubgroup K'
    have hfixK : K.fixingSubgroup = U.carrier := by
      show (IntermediateField.fixedField U.carrier).fixingSubgroup = U.carrier
      exact InfiniteGalois.fixingSubgroup_fixedField
        ⟨U.carrier, U.carrier.isClosed_of_isOpen U.isOpen⟩
    have hUU' : U ≤ U' := by
      rw [Work.CFT.MaxProP.OpenNormal.le_def]
      change K'.fixingSubgroup ≤ U.carrier
      rw [← hfixK]
      exact IntermediateField.fixingSubgroup_antitone hle
    have hC := Work.CFTLib.ProP.contMap_range_finrank_le_hrel F p hrel hgalE
      (K := ↥K) (K' := ↥K') U U' hUU' ⟨(AlgEquiv.refl : ↥K ≃ₐ[F] ↥K)⟩
      (by rw [hfixedU']; exact ⟨(AlgEquiv.refl : ↥K' ≃ₐ[F] ↥K')⟩) huni hp'
      (by
        intro L _ _ _ _ _ habL hpL huniL
        exact hcontains L habL hpL huniL)
    have hB := Work.CFTLib.ProP.finrank_H1Fp_le_of_generating_finset F p hgalE K' S hSdense
    have hΦ : Module.finrank (ZMod p) (LinearMap.range (Work.CFTLib.Shaf.levelMap e U)) ≤
        Module.finrank (ZMod p) (LinearMap.range (Work.CFT.MaxProP.contMap p (Work.CFTLib.ProP.GG F p) U U' hUU')) := by
      have hcomp : Work.CFTLib.Shaf.levelMap e U =
          (Work.CFTLib.Shaf.levelMap e U').comp (Work.CFT.MaxProP.contMap p (Work.CFTLib.ProP.GG F p) U U' hUU') :=
        LinearMap.ext (fun x => (Work.CFTLib.Shaf.levelMap_natural e hUU' x).symm)
      have hmap : LinearMap.range (Work.CFTLib.Shaf.levelMap e U) =
          (LinearMap.range (Work.CFT.MaxProP.contMap p (Work.CFTLib.ProP.GG F p) U U' hUU')).map
            (Work.CFTLib.Shaf.levelMap e U') := by
        rw [hcomp]
        exact LinearMap.range_comp _ _
      exact hmap ▸ Submodule.finrank_map_le _ _
    calc Module.finrank (ZMod p) (LinearMap.range (Work.CFTLib.Shaf.levelMap e U))
        ≤ Module.finrank (ZMod p)
            (LinearMap.range (Work.CFT.MaxProP.contMap p (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) U U' hUU')) := hΦ
      _ ≤ Module.finrank (ZMod p) (Work.Tower.Shafarevich.H1Fp p (↥K' ≃ₐ[F] ↥K')) +
            (NumberField.InfinitePlace.nrRealPlaces F +
              NumberField.InfinitePlace.nrComplexPlaces F - 1) + CFTLib.delta F p := hC
      _ ≤ S.card +
            (NumberField.InfinitePlace.nrRealPlaces F +
              NumberField.InfinitePlace.nrComplexPlaces F - 1) + CFTLib.delta F p := by
          omega
      _ = LeanEval.NumberTheory.generatorRank (LeanEval.NumberTheory.MaxUnramifiedProPGaloisGroup F p) +
            (NumberField.InfinitePlace.nrRealPlaces F +
              NumberField.InfinitePlace.nrComplexPlaces F - 1) +
            (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0) := by
          rw [hScard, show CFTLib.delta F p =
            (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0) from rfl]

end Work.CFTLib
