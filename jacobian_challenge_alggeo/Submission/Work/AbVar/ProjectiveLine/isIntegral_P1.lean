import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.ProjectiveLine

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The projective line is integral

`Work.AbVar.P1 k` is `Proj k[X₀, X₁]` with its standard grading by total degree, so its underlying
scheme is an instance of `AlgebraicGeometry.Proj`.  This file proves that this scheme is integral.

The argument is completely explicit, using only the description of `Proj` as the projective spectrum
of homogeneous prime ideals (no `Proj`-specific integrality results are needed):

* `k[X₀,X₁]` is a domain, so the zero ideal `⊥` is a prime homogeneous ideal, and it does not
  contain the irrelevant ideal `(X₀,X₁)`: this is the point `zeroPt k`.
* Every nonempty basic open `D₊(f)` contains `zeroPt k` (because `D₊(f)` nonempty forces `f ≠ 0`,
  i.e. `f ∉ ⊥`).  Since the `D₊(f)` form a basis of the Zariski topology, every nonempty open
  contains `zeroPt k`, whence `Proj k[X₀,X₁]` is irreducible.
* The stalk of `Proj` at a point `x` is the homogeneous localisation `AtPrime 𝒜 x`; it embeds into
  the ordinary localisation of `k[X₀,X₁]` at the prime `x`, which is reduced (it is a localisation
  of a domain).  Hence every stalk is reduced and `Proj k[X₀,X₁]` is reduced.

Integrality then follows from `IsIntegral ↔ IrreducibleSpace ∧ IsReduced`.
-/

set_option autoImplicit false

namespace Work.AbVar.ProjectiveLine

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

/-- The point of `Proj k[X₀,X₁]` corresponding to the zero ideal: the generic point of the
projective line.  It is a homogeneous prime ideal because `k[X₀,X₁]` is a domain, and it is relevant
because the irrelevant ideal `(X₀,X₁)` is nonzero. -/
def zeroPt (k : Type*) [Field k] :
    ProjectiveSpectrum (Work.AbVar.P1Grading k) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]
    exact Ideal.isPrime_bot
  not_irrelevant_le := by
    intro h
    have hX : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) ∈
        (HomogeneousIdeal.irrelevant (Work.AbVar.P1Grading k)) :=
      HomogeneousIdeal.mem_irrelevant_of_mem (𝒜 := Work.AbVar.P1Grading k) (i := 1)
        (by norm_num)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k 0))
    have hh : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) ∈
        (⊥ : HomogeneousIdeal (Work.AbVar.P1Grading k)).toIdeal :=
      (HomogeneousIdeal.mem_iff (I := ⊥)).mpr (h hX)
    rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at hh
    exact MvPolynomial.X_ne_zero 0 hh

/-- `zeroPt` is the point attached to the zero ideal. -/
lemma zeroPt_asHomogeneousIdeal (k : Type*) [Field k] :
    (zeroPt k).asHomogeneousIdeal = (⊥ : HomogeneousIdeal (Work.AbVar.P1Grading k)) := rfl

/-- The generic point belongs to every nonempty basic open set: a nonempty `D₊(f)` forces `f ≠ 0`,
and then `f ∉ (0)`. -/
lemma zeroPt_mem_basicOpen (k : Type*) [Field k] {f : MvPolynomial (Fin 2) k} (hf : f ≠ 0) :
    (zeroPt k) ∈ (↑(ProjectiveSpectrum.basicOpen (Work.AbVar.P1Grading k) f) :
      Set (ProjectiveSpectrum (Work.AbVar.P1Grading k))) := by
  rw [ProjectiveSpectrum.mem_coe_basicOpen]
  have hbot : (zeroPt k).asHomogeneousIdeal = (⊥ : HomogeneousIdeal (Work.AbVar.P1Grading k)) :=
    rfl
  rw [hbot]
  intro hmem
  exact hf ((HomogeneousIdeal.mem_iff (I := ⊥)).mp hmem)

/-- Every nonempty open subset of `Proj k[X₀,X₁]` contains the generic point `zeroPt k`. -/
lemma zeroPt_mem_of_isOpen_nonempty (k : Type*) [Field k]
    {U : Set (ProjectiveSpectrum (Work.AbVar.P1Grading k))} (hU : IsOpen U)
    (hne : U.Nonempty) : (zeroPt k) ∈ U := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨V, ⟨f, rfl⟩, hxV, hVU⟩ :=
    (ProjectiveSpectrum.isTopologicalBasis_basic_opens (Work.AbVar.P1Grading k)).exists_subset_of_mem_open
      hx hU
  have hf : f ≠ 0 := by
    rintro rfl
    rw [ProjectiveSpectrum.mem_coe_basicOpen] at hxV
    exact hxV (zero_mem _)
  exact hVU (zeroPt_mem_basicOpen k hf)

/-- `Proj k[X₀,X₁]` is irreducible. -/
lemma irreducibleSpace_P1 (k : Type*) [Field k] :
    IrreducibleSpace (Proj (Work.AbVar.P1Grading k)) :=
  { toPreirreducibleSpace :=
      PreirreducibleSpace.of_forall_nonempty_inter (fun _U _V hU hV hUne hVne =>
        ⟨zeroPt k, zeroPt_mem_of_isOpen_nonempty k hU hUne,
          zeroPt_mem_of_isOpen_nonempty k hV hVne⟩)
    toNonempty := ⟨zeroPt k⟩ }

/-- The stalk of `Proj k[X₀,X₁]` at any point is reduced, since it is isomorphic to a homogeneous
localisation which embeds into a localisation of the domain `k[X₀,X₁]`. -/
lemma isReduced_stalk_P1 (k : Type*) [Field k] (x : Proj (Work.AbVar.P1Grading k)) :
    _root_.IsReduced ((Proj (Work.AbVar.P1Grading k)).presheaf.stalk x) := by
  have hx : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hAt : _root_.IsReduced
      (HomogeneousLocalization.AtPrime (Work.AbVar.P1Grading k) x.asHomogeneousIdeal.toIdeal) := by
    refine isReduced_of_injective
      ({ toFun := HomogeneousLocalization.val,
         map_one' := HomogeneousLocalization.val_one,
         map_mul' := HomogeneousLocalization.val_mul,
         map_zero' := HomogeneousLocalization.val_zero } :
        HomogeneousLocalization.AtPrime (Work.AbVar.P1Grading k)
            x.asHomogeneousIdeal.toIdeal →*₀
          Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
      (HomogeneousLocalization.val_injective x.asHomogeneousIdeal.toIdeal.primeCompl)
  exact isReduced_of_injective (Proj.stalkIso' (Work.AbVar.P1Grading k) x).toMonoidWithZeroHom
    (fun a b hab => (Proj.stalkIso' (Work.AbVar.P1Grading k) x).injective hab)

/-- `Proj k[X₀,X₁]` is reduced. -/
lemma isReduced_P1 (k : Type*) [Field k] : IsReduced (Proj (Work.AbVar.P1Grading k)) := by
  have h : ∀ x : Proj (Work.AbVar.P1Grading k),
      _root_.IsReduced ((Proj (Work.AbVar.P1Grading k)).presheaf.stalk x) :=
    isReduced_stalk_P1 k
  exact isReduced_of_isReduced_stalk (Proj (Work.AbVar.P1Grading k))

/-- `Proj k[X₀,X₁]` is integral. -/
lemma isIntegral_proj_P1 (k : Type*) [Field k] :
    IsIntegral (Proj (Work.AbVar.P1Grading k)) := by
  have hIrr := irreducibleSpace_P1 k
  have hRed := isReduced_P1 k
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end

open CategoryTheory in
theorem isIntegral_P1 (k : Type*) [Field k] :
    AlgebraicGeometry.IsIntegral (Work.AbVar.P1 k).left := by
  show AlgebraicGeometry.IsIntegral (Proj (Work.AbVar.P1Grading k))
  exact isIntegral_proj_P1 k

end Work.AbVar.ProjectiveLine
