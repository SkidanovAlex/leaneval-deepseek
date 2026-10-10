import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.LocalReciprocityLubinTate.Target
import Submission.NK.LocalReciprocityLubinTate.Unramified.existenceTheorem_of_symbolTower
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_level_ge_of_towerCover
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_kernelCondition_of_reciprocityLaw
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_reciprocityLaw_of_symbolTower
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_symbolTower_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local reciprocity datum for a `p`-adic field, from the canonical Lubin–Tate symbol tower

The chapter's construction of the Lubin–Tate *symbol* tower
(`NK.LocalReciprocityLubinTate.Unramified.nonempty_symbolTower_adicCompletion`) produces, for
every uniformiser `π` of `F = 𝔭.adicCompletion K`, a nested family of finite abelian levels
`E_{m,n} = F^{ur}_{(m+1)!}·F(Λ_{π^{n+1}})` together with the canonical Artin symbols at each level
(surjective, with kernel the norm group, and compatible with restriction).

This file records the **two classical residues** in terms of which the remaining content of local
class field theory is organised, and derives the boundary theorem from them:

* `NormCorrespondence` — Hasse's *Normensatz*: the norm group determines the abelian extension
  (`NK.LocalReciprocityLubinTate.NormCorrespondence`);
* `NormInKernel` — the norm-compatibility of the Artin symbol: norms are annihilated by the symbol
  (`NK.LocalReciprocityLubinTate.NormInKernel`, at the constructed tower).

Everything else is proved here: the tower and its symbols, the norm groups `⟨π^{a m}⟩ · U^{n+1}`
(Honda's explicit reciprocity law), the norm index theorem, the existence theorem, the surjectivity
of the level symbols (which turns "norms are in the kernel" into "the kernel is the norm group"),
the covering of `F^{ab}` by the tower levels, and finally the reciprocity law, the norm residue
symbol and the Artin reciprocity datum.

## Main results

* `NK.LocalReciprocityLubinTate.adicSymbolTower` — the canonical symbol tower of a uniformiser;
* `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion_of_normInKernel` — the boundary
  theorem from `NormCorrespondence` and `NormInKernel`;
* `NK.LocalReciprocityLubinTate.kernelCondition_adicCompletion_of_normInKernel` — the same
  residues give the norm residue symbol with the correct level kernels.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate

universe u

noncomputable section

open IsDedekindDomain

/-- **The canonical Lubin–Tate symbol tower of a uniformiser of a `p`-adic field.**

This is the tower of the chapter's construction
(`NK.LocalReciprocityLubinTate.Unramified.nonempty_symbolTower_adicCompletion`), whose levels are
the composita of the unramified extension of degree `(m+1)!` with the `(n+1)`-st Lubin–Tate level,
equipped with the canonical Artin symbols.  It is recorded as a definition so that the residues
`NK.LocalReciprocityLubinTate.NormInKernel` can be stated for it. -/
noncomputable def adicSymbolTower (K : Type) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K)) :
    NK.LocalReciprocityLubinTate.LubinTateSymbolTower (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) π (fun m : ℕ => Nat.factorial (m + 1))
      (NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K))
      (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K)) :=
  Classical.choice (NK.LocalReciprocityLubinTate.Unramified.nonempty_symbolTower_adicCompletion Q hπ)

/-- **The degree sequence `a m = (m+1)!` is unbounded in divisibility**, which is what makes the
norm groups `⟨π^{a m}⟩ · U^{n+1}` of the tower cofinal among the finite-index subgroups of `Fˣ`. -/
theorem factorial_dvd_factorial_eventually (d : ℕ) (hd : d ≠ 0) :
    ∃ m : ℕ, d ∣ Nat.factorial (m + 1) :=
  ⟨d - 1, Nat.dvd_factorial (Nat.pos_of_ne_zero hd) (by omega)⟩

/-- **The norm residue symbol with the correct level kernels, from the two classical residues.**

Given

* `NormCorrespondence` (Hasse's *Normensatz*) and
* `NormInKernel` (the norm-compatibility of the Artin symbol) for the canonical tower,

there is a homomorphism `Fˣ →* Gal(F^{ab}/F)` whose composite with the restriction to every finite
abelian level `L ≤ F^{ab}` has kernel exactly the norm group `N_{L/F} Lˣ`.  This is
`NK.LocalArtin.KernelCondition`, and it is obtained here by restricting the canonical tower symbols
and comparing indices. -/
theorem kernelCondition_adicCompletion_of_normInKernel {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K))
    (hcorr : NK.LocalReciprocityLubinTate.NormCorrespondence (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)))
    (hnk : NK.LocalReciprocityLubinTate.NormInKernel (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) π (fun m : ℕ => Nat.factorial (m + 1))
      (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K)) (adicSymbolTower K Q hπ)) :
    Nonempty (NK.LocalArtin.KernelCondition (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) := by
  classical
  obtain ⟨hlaw⟩ :=
    NK.LocalReciprocityLubinTate.Unramified.nonempty_reciprocityLaw_of_symbolTower
      (F := Q.adicCompletion K) (F' := SeparableClosure (Q.adicCompletion K)) (π := π)
      (a := fun m : ℕ => Nat.factorial (m + 1)) (adicSymbolTower K Q hπ) hcorr
      (NormIndex.normIndex_adicCompletion Q) hnk
      (fun L _ _ hcomm =>
        NK.LocalReciprocityLubinTate.Unramified.exists_level_ge_of_symbolTower Q hπ
          (fun d hd => factorial_dvd_factorial_eventually d hd) (adicSymbolTower K Q hπ).toLubinTateTowerGen
          hcorr L hcomm)
  exact NK.LocalReciprocityLubinTate.Unramified.nonempty_kernelCondition_of_reciprocityLaw hlaw

/-- **The boundary theorem of the chapter, from the two classical residues.**

`NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) (SeparableClosure …)` — the canonical local
Artin reciprocity datum — follows from Hasse's norm correspondence and the norm-compatibility of the
Artin symbol; the Lubin–Tate tower, its canonical symbols, Honda's reciprocity law, the norm index
theorem, the existence theorem and the surjectivity of the level symbols are all theorems of this
chapter. -/
theorem artinReciprocity_adicCompletion_of_normInKernel {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K))
    (hcorr : NK.LocalReciprocityLubinTate.NormCorrespondence (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)))
    (hnk : NK.LocalReciprocityLubinTate.NormInKernel (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) π (fun m : ℕ => Nat.factorial (m + 1))
      (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K)) (adicSymbolTower K Q hπ)) :
    Nonempty (NK.LocalCFT.ArtinReciprocity (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) :=
  artinReciprocity_adicCompletion Q (kernelCondition_adicCompletion_of_normInKernel Q hπ hcorr hnk).some

end

end NK.LocalReciprocityLubinTate
