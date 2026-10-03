
import ChallengeDeps
import Submission.Work.ORCoherence.Imports
import Submission.Work.ORCoherence.Criterion
import Submission.Work.ORCoherence.Retract
import Submission.Work.ORCoherence.Presentation
import Submission.Work.ORCoherence.Lemma31
import Submission.Work.ORCoherence.Tor.torTwoVanishes_of_torVanishes
import Submission.Work.ORCoherence.Tensor.balanced_moduleFinite_finsupp
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Finiteness.Basic

/-!
# N10: the coherence criterion (JL Lemma 3.1, Prop 3.2, Cor 3.3)

This file contains the main theorem of the node:

`Work.ORCoherence.coherent_of_embeds_semisimple` :
if `f : R →+* S` is injective, `S` is an Artinian ring (e.g. semisimple Artinian, or a division
ring), `globalDim R ≤ 2` and the right `R`-module `S` has weak dimension at most one (encoded as
`TorTwoVanishes f`), then `R` is coherent.

Main interface for consumers:

* `Work.ORCoherence.Balanced f M` — the balanced tensor product `S ⊗[R] M`
  (`Submission/Work/ORCoherence/Defs.lean`), with `Balanced.tmul`, `Balanced.lift`,
  `Balanced.map` (`Map.lean`).
* `Work.ORCoherence.TorTwoVanishes f` (`Criterion.lean`) — the hypothesis `Tor₂^R(S, M) = 0` for
  every left `R`-module `M`, in the concrete form in which it is used: for every exact sequence
  `0 → P₂ → P₁ → P₀ → M → 0` of left `R`-modules with `P₀`, `P₁`, `P₂` projective, the induced
  map `S ⊗[R] P₂ → S ⊗[R] P₁` is injective.
* `Work.ORCoherence.Tor f n M` and `Work.ORCoherence.TorVanishes f` (`Tor.lean`) — the honest
  derived-functor `Tor_n^R(S, M)` and the hypothesis `Tor₂^R(S, M) = 0` for all `M`.
  The bridge `TorVanishes f → TorTwoVanishes f` is `torTwoVanishes_of_torVanishes`
  (`Submission/Work/ORCoherence/Tor/`).
* `Work.ORCoherence.globalDim R : WithBot ℕ∞` (`GlobalDim.lean`), with
  `globalDim_le_iff' R n : globalDim R ≤ n ↔ ∀ M, HasProjectiveDimensionLE M n`
  (`Presentation.lean`).
* `Work.ORCoherence.finite_of_balanced_finite_of_projective` (`Lemma31.lean`) — JL Lemma 3.1.
* `Work.ORCoherence.finite_syzygy_of_ker_balanced_fg` (`Prop32.lean`) — JL Proposition 3.2.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits
open scoped TensorProduct

namespace Work.ORCoherence

universe u

/-- **JL Corollary 3.3** (coherence criterion): if a ring `R` embeds in an Artinian ring `S`,
if `R` has global dimension at most two and the right `R`-module `S` has weak dimension at most
one (i.e. `Tor₂^R(S, M) = 0` for every left `R`-module `M`), then `R` is coherent. -/
theorem coherent_of_embeds_semisimple {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Injective f) [IsArtinianRing S] (hgl : globalDim R ≤ (2 : WithBot ℕ∞))
    (hw : TorTwoVanishes f) : Ring.Coherent R := by
  intro I hI
  obtain ⟨n, φ, hφ⟩ := exists_finsupp_linearMap_range_eq_of_fg R I hI
  haveI hproj : Projective (ModuleCat.of R ↥(LinearMap.ker φ)) :=
    projective_ker_of_hasProjectiveDimensionLE ((globalDim_le_iff' R 2).mp hgl) n φ
  let K : Submodule R (Fin n →₀ R) := LinearMap.ker φ
  let d₂ : ModuleCat.of R ↥K ⟶ ModuleCat.of R (Fin n →₀ R) := ModuleCat.ofHom K.subtype
  let d₁ : ModuleCat.of R (Fin n →₀ R) ⟶ ModuleCat.of R R := ModuleCat.ofHom φ
  let π₀ : ModuleCat.of R R ⟶ ModuleCat.of R (R ⧸ I) := ModuleCat.ofHom I.mkQ
  have h : d₂ ≫ d₁ = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    show φ (x : Fin n →₀ R) = 0
    exact x.2
  have h' : d₁ ≫ π₀ = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    show I.mkQ (φ x) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [← hφ]
    exact LinearMap.mem_range_self φ x
  haveI hm : Mono d₂ := (ModuleCat.mono_iff_injective d₂).mpr (fun a b hab =>
    Subtype.ext (show (a : Fin n →₀ R) = b from hab))
  have he : (ShortComplex.mk d₂ d₁ h).Exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    show LinearMap.range K.subtype = LinearMap.ker φ
    rw [Submodule.range_subtype]
  have he' : (ShortComplex.mk d₁ π₀ h').Exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    show LinearMap.range φ = LinearMap.ker I.mkQ
    rw [hφ, Submodule.ker_mkQ]
  haveI hπ : Epi π₀ := (ModuleCat.epi_iff_surjective π₀).mpr (Submodule.mkQ_surjective I)
  have hinj : Function.Injective ⇑(Balanced.map f d₂.hom) :=
    hw (ModuleCat.of R (R ⧸ I)) (ModuleCat.of R ↥K) (ModuleCat.of R (Fin n →₀ R))
      (ModuleCat.of R R) d₂ d₁ π₀ h h' hm he he' hπ
  have hfin₁ : Module.Finite S (Balanced f (Fin n →₀ R)) :=
    Tensor.balanced_moduleFinite_finsupp f (Fin n)
  haveI hfinR : Module.Finite S ↥(LinearMap.range (Balanced.map f d₂.hom)) :=
    Module.Finite.iff_fg.mpr (Submodule.FG.of_le hfin₁.fg_top le_top)
  have hfin₂ : Module.Finite S (Balanced f ↥K) :=
    Module.Finite.equiv (LinearEquiv.ofInjective (Balanced.map f d₂.hom) hinj).symm
  have hPK : Module.Finite R ↥K :=
    finite_of_balanced_finite_of_projective f hf (ModuleCat.of R ↥K) hfin₂
  have hKFG : K.FG := Module.Finite.iff_fg.mp hPK
  refine Module.finitePresentation_of_surjective
    (φ.codRestrict I (fun x => hφ ▸ LinearMap.mem_range_self φ x)) ?_ ?_
  · intro y
    have hy : y.1 ∈ LinearMap.range φ := by rw [hφ]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext (by simpa using hx)⟩
  · have hker : (φ.codRestrict I (fun x => hφ ▸ LinearMap.mem_range_self φ x)).ker = K := by
      ext x
      simp [K, LinearMap.mem_ker]
    rw [hker]
    exact hKFG

end Work.ORCoherence

namespace Work.ORCoherence

universe u

/-- **JL Corollary 3.3** with the hypotheses exactly as in the paper's semisimple setting:
`S` semisimple Artinian (we only use `IsArtinianRing S`). -/
theorem coherent_of_embeds_semisimple' {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Injective f) [IsSemisimpleRing S] (hgl : globalDim R ≤ (2 : WithBot ℕ∞))
    (hw : TorTwoVanishes f) : Ring.Coherent R :=
  coherent_of_embeds_semisimple f hf hgl hw

end Work.ORCoherence

namespace Work.ORCoherence

universe u

/-- **JL Corollary 3.3** in the case where `S` is a division ring: this is the form used when
`S = D_K(G')` is the Hughes-free division ring of a torsion-free one-relator group. -/
theorem coherent_of_embeds_division {R S : Type u} [Ring R] [DivisionRing S] (f : R →+* S)
    (hf : Function.Injective f) (hgl : globalDim R ≤ (2 : WithBot ℕ∞))
    (hw : TorTwoVanishes f) : Ring.Coherent R :=
  coherent_of_embeds_semisimple f hf hgl hw

end Work.ORCoherence

namespace Work.ORCoherence

universe u

/-- **JL Corollary 3.3** in the form of the design statement: the hypothesis on `S` is
`Tor₂^R(S, M) = 0` for every left `R`-module `M` (`TorVanishes f`), where `Tor` is the honest
left-derived functor of `S ⊗[R] -`. -/
theorem coherent_of_embeds_semisimple_of_tor {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Injective f) [IsArtinianRing S] (hgl : globalDim R ≤ (2 : WithBot ℕ∞))
    (hw : TorVanishes f) : Ring.Coherent R :=
  coherent_of_embeds_semisimple f hf hgl (Tor.torTwoVanishes_of_torVanishes f hw)

end Work.ORCoherence
