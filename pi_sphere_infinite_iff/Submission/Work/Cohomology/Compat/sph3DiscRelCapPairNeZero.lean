import Mathlib
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.relCochainDual
import Submission.Work.Cohomology.relCapH_kronH_cup
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.cupNatural
import Submission.Work.Cohomology.cupLeibniz
import Submission.Work.Cohomology.Kronecker
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.diskPairCohomologyTop
import Submission.Work.Cohomology.homotopyEquiv_prod_fst
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.Compat.kunnethEvalCompat

/-!
# The relative cap product of the pair `(S³×D⁴, S³×S³)` in bidegree `(4,3)` is nonzero

This is the "overlap case" input of `Work.Cohomology.Crux.vk_relCapPair_nonzero`.

## Structure of the proof

Everything reduces to the chain-level Künneth statement
`Work.Cohomology.kunnethEvalCompat` (the crux of the project, proved there
from `Work.Cohomology.Crux33.sph3DiscCupEval`): there are `3`-cocycles `θ'` on `S³ ⊆ D⁴` and `β` on
`S³`, and a `6`-cycle `a` of `A = PairAT = S³ × S³`, with

`⟨(pj2A^*θ') ⌣ (pj1A^*β), a⟩ ≠ 0`.

From this data we build, with `X = PairXT = S³ × D⁴`:

* a `3`-cochain `θ` on `D⁴` lifting `θ'` along the restriction (`surjective_restr`) and the relative
  cocycle `α := (sndXT)^*(dθ)` (the pullback of the differential of `θ` along the second projection);
  it vanishes on `A = S³ × S³` because `dθ' = 0` and it is a cocycle because `d² = 0`;
* the absolute cocycle `γ := (fstXT)^*β`;
* a `7`-chain `w` of `X` with `d w = (inclChains X A).f 6 a`; it exists because `H₆(X) = 0`
  (`X ≃ S³`).

The Leibniz rule (`cupLeibniz`) gives `α ⌣ γ = d((sndXT)^*θ ⌣ γ)`, hence, evaluating on the cycle
`w` and using `d w = incl_* a`, the naturality of the cup product under `A ⊆ X` and the identity
`restr((sndXT)^*θ) = pj2A^*θ'`,

`⟨α ⌣ γ, w⟩ = ⟨θ' ⌣ β, a⟩ ≠ 0`.

Therefore `α ⌢ w` is a cycle (the cap product of a relative cocycle with a relative cycle) on which
the cocycle `γ` does not vanish, so its homology class is nonzero: with `u := [α] ∈ H⁴(X,A)` and `c`
the relative class of `w` (`u ⌢ c` is represented by `α ⌢ w`), we get `u ⌢ c ≠ 0`, and `u ≠ 0`
because `u = 0` would force `u ⌢ c = 0`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.Cohomology.Compat

noncomputable section

/-- The projection of `PairXT = S³ × D⁴` onto its second factor. -/
abbrev sndXT : PairXT ⟶ Disc4T := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

/-- The projection of `PairXT = S³ × D⁴` onto its first factor. -/
abbrev fstXT : PairXT ⟶ Sph3T := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The inclusion `A ⊆ X` as a morphism of `TopCat`. -/
abbrev inclAX : TopCat.of PairAT ⟶ PairXT := subtypeIncl PairXT PairAT

/-! ## The vanishing of `H₆(S³ × D⁴)` -/

/-- `S³ × D⁴` is homotopy equivalent to `S³` (the disc is contractible), so its degree-`6`
homology vanishes. -/
theorem isZero_homology_six_PairXT : IsZero ((singularChains ℤ PairXT).homology 6) := by
  haveI : ContractibleSpace ↥Disc4T := diskUnit_isContractible 4
  obtain ⟨e⟩ := homologyIso_of_homotopyEquiv (homotopyEquiv_prod_fst ↥Sph3T ↥Disc4T).some 6
  exact IsZero.of_iso (sphereHomologyZero 3 6 (by norm_num) (by norm_num) (by norm_num)) e

/-! ## The two squares of `A = S³ × S³ ⊆ X = S³ × D⁴` -/

/-- The restriction of the second projection to the sphere bundle is the second projection of `A`
followed by the inclusion `S³ ⊆ D⁴`. -/
theorem subtypeIncl_sndXT :
    inclAX ≫ sndXT = pj2A ≫ subtypeIncl Disc4T (sphereInUnit 4) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rfl

/-- The restriction of the first projection to the sphere bundle is `pj1A`. -/
theorem subtypeIncl_fstXT : inclAX ≫ fstXT = pj1A := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rfl

/-! ## Naturality of the pullback with the differential (simplicial sets) -/

/-- The pullback of the coboundary is the coboundary of the pullback. -/
theorem cochainDiff_dualMap_sset (X Y : SSet) (f : X ⟶ Y) (n : ℕ)
    (φ : Cochain ℤ Y n) :
    (((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f (n + 1)).hom.dualMap
        (cochainDiff ℤ Y φ))
      = cochainDiff ℤ X
          ((((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n).hom.dualMap φ)) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.dualMap_apply, cochainDiff, LinearMap.comp_apply]
  congr 1
  exact LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).comm (n + 1) n)) x

/-- The pullback of the coboundary is the coboundary of the pullback (spaces). -/
theorem cochainDiff_pullbackHom (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (φ : Cochain ℤ (TopCat.toSSet.obj Y) n) :
    (cochainPullbackHom ℤ X Y f (n + 1)).hom (cochainDiff ℤ (TopCat.toSSet.obj Y) φ)
      = cochainDiff ℤ (TopCat.toSSet.obj X)
          ((cochainPullbackHom ℤ X Y f n).hom φ) :=
  cochainDiff_dualMap_sset (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
    (TopCat.toSSet.map f) n φ

/-! ## The pullback of the cup product (spaces) -/

/-- The pullback of an Alexander–Whitney product is the product of the pullbacks. -/
theorem cup_pullbackHom (X Y : TopCat) (f : X ⟶ Y) (n m : ℕ)
    (α : Cochain ℤ (TopCat.toSSet.obj Y) n) (β : Cochain ℤ (TopCat.toSSet.obj Y) m) :
    (cochainPullbackHom ℤ X Y f (n + m)).hom (cup ℤ (TopCat.toSSet.obj Y) α β)
      = cup ℤ (TopCat.toSSet.obj X)
          ((cochainPullbackHom ℤ X Y f n).hom α) ((cochainPullbackHom ℤ X Y f m).hom β) :=
  (cupNatural ℤ (TopCat.toSSet.map f) α β).symm

/-! ## Every `6`-cycle of `S³ × D⁴` bounds a `7`-chain -/

/-- A `6`-cycle of a chain complex is a boundary when the `6`-th homology vanishes. -/
theorem exists_chain_of_isCycle (C : ChainComplex (ModuleCat ℤ) ℕ)
    (h : IsZero (C.homology 6)) (z : C.X 6) (hz : C.d 6 5 z = 0) :
    ∃ w : C.X 7, z = C.d 7 6 w := by
  have hprev : (ComplexShape.down ℕ).prev 6 = 7 := ChainComplex.prev ℕ 6
  have hnext : (ComplexShape.down ℕ).next 6 = 5 := by
    have h1 : (ComplexShape.down ℕ).next (5 + 1) = 5 := ChainComplex.next_nat_succ 5
    simpa using h1
  have hex : (C.sc' 7 6 5).Exact :=
    (C.exactAt_iff' 7 6 5 hprev hnext).1 ((C.exactAt_iff_isZero_homology 6).2 h)
  have hker : LinearMap.range (C.d 7 6).hom = LinearMap.ker (C.d 6 5).hom :=
    ShortComplex.Exact.moduleCat_range_eq_ker hex
  have hz' : z ∈ LinearMap.ker (C.d 6 5).hom := LinearMap.mem_ker.mpr hz
  rw [← hker, LinearMap.mem_range] at hz'
  obtain ⟨w, hw⟩ := hz'
  exact ⟨w, hw.symm⟩

/-- Every `6`-cycle of `S³ × S³ ⊆ S³ × D⁴` is the boundary of a `7`-chain of `S³ × D⁴`. -/
theorem exists_seven_chain_boundary (a : (singularChains ℤ (TopCat.of PairAT)).X 6)
    (ha : (singularChains ℤ (TopCat.of PairAT)).d 6 5 a = 0) :
    ∃ w : (singularChains ℤ PairXT).X 7,
      (inclChains PairXT PairAT).f 6 a = (singularChains ℤ PairXT).d 7 6 w := by
  have hcomm := congrArg ModuleCat.Hom.hom ((inclChains PairXT PairAT).comm 6 5)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hcomm
  have hcyc : (singularChains ℤ PairXT).d 6 5 ((inclChains PairXT PairAT).f 6 a) = 0 :=
    (LinearMap.congr_fun hcomm a).trans (by simp only [LinearMap.comp_apply, ha, map_zero])
  exact exists_chain_of_isCycle (singularChains ℤ PairXT)
    (isZero_homology_six_PairXT) _ hcyc

/-! ## The cochain identities -/

/-- The two pullbacks of the restricted cochains agree with the restrictions of the pullbacks. -/
theorem restr_pullback_snd (θ : Cochain ℤ (TopCat.toSSet.obj Disc4T) 3) :
    (cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclAX 3).hom
        ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
      = (cochainPullbackHom ℤ (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3).hom
          (((restr ℤ Disc4T (sphereInUnit 4)).f 3).hom θ) := by
  have h1 : (cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclAX 3).hom
        ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
      = (cochainPullbackHom ℤ (TopCat.of PairAT) Disc4T (inclAX ≫ sndXT) 3).hom θ := by
    rw [cochainPullbackHom_comp]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have h2 : (cochainPullbackHom ℤ (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3).hom
        (((restr ℤ Disc4T (sphereInUnit 4)).f 3).hom θ)
      = (cochainPullbackHom ℤ (TopCat.of PairAT) Disc4T
          (pj2A ≫ subtypeIncl Disc4T (sphereInUnit 4)) 3).hom θ := by
    show (cochainPullbackHom ℤ (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3).hom
        ((cochainPullbackHom ℤ (TopCat.of (sphereInUnit 4)) Disc4T
          (subtypeIncl Disc4T (sphereInUnit 4)) 3).hom θ)
      = (cochainPullbackHom ℤ (TopCat.of PairAT) Disc4T
          (pj2A ≫ subtypeIncl Disc4T (sphereInUnit 4)) 3).hom θ
    rw [cochainPullbackHom_comp]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [h1, h2, subtypeIncl_sndXT]

/-- The pullback of `β` along the first projection restricts to the pullback along `pj1A`. -/
theorem restr_pullback_fst (β : Cochain ℤ (TopCat.toSSet.obj Sph3T) 3) :
    (cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclAX 3).hom
        ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β)
      = (cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β := by
  have h1 : (cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclAX 3).hom
        ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β)
      = (cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T (inclAX ≫ fstXT) 3).hom β := by
    rw [cochainPullbackHom_comp]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [h1, subtypeIncl_fstXT]

/-- The differential of the pullback of `θ` along the second projection. -/
theorem cochainDiff_pullback_snd (θ : Cochain ℤ (TopCat.toSSet.obj Disc4T) 3) :
    cochainDiff ℤ (TopCat.toSSet.obj PairXT)
        ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
      = (cochainPullbackHom ℤ PairXT Disc4T sndXT 4).hom
          (cochainDiff ℤ (TopCat.toSSet.obj Disc4T) θ) :=
  (cochainDiff_pullbackHom PairXT Disc4T sndXT 3 θ).symm

/-- The differential of the pullback of the cocycle `β` vanishes. -/
theorem cochainDiff_pullback_fst (β : Cochain ℤ (TopCat.toSSet.obj Sph3T) 3)
    (hβ : cochainDiff ℤ (TopCat.toSSet.obj Sph3T) β = 0) :
    cochainDiff ℤ (TopCat.toSSet.obj PairXT)
      ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β) = 0 := by
  rw [← cochainDiff_pullbackHom PairXT Sph3T fstXT 3 β, hβ]
  simp

/-- **The Leibniz step**: the cup product of the pullback of `dθ` with the pullback of the cocycle
`β` is the differential of the cup product of the pullbacks of `θ` and `β`. -/
theorem cup_diff_eq (θ : Cochain ℤ (TopCat.toSSet.obj Disc4T) 3)
    (β : Cochain ℤ (TopCat.toSSet.obj Sph3T) 3)
    (hβ : cochainDiff ℤ (TopCat.toSSet.obj Sph3T) β = 0) :
    cup ℤ (TopCat.toSSet.obj PairXT)
        ((cochainPullbackHom ℤ PairXT Disc4T sndXT 4).hom
          (cochainDiff ℤ (TopCat.toSSet.obj Disc4T) θ))
        ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β)
      = cochainDiff ℤ (TopCat.toSSet.obj PairXT)
          (cup ℤ (TopCat.toSSet.obj PairXT)
            ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
            ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β)) := by
  rw [cupLeibniz ℤ (TopCat.toSSet.obj PairXT)
    ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
    ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β)]
  rw [cochainDiff_pullback_snd θ, cochainDiff_pullback_fst β hβ]
  rw [show ((-1 : ℤ) ^ (3 : ℕ)) = -1 from by norm_num]
  rw [cup_zero_right']
  simp only [smul_zero, add_zero]

/-! ## The evaluated Künneth statement (the crux) transported to `X = S³ × D⁴` -/

/-- **The external-product nonvanishing for `(S³ × D⁴, S³ × S³)` in the evaluated form, with the
filling included.**

There are a `3`-cochain `θ` on the ball `D⁴` whose restriction to the boundary sphere `S³` is a
cocycle, a `3`-cocycle `β` on `S³`, a `7`-chain `w` of `S³ × D⁴` whose boundary comes from the
sphere bundle `S³ × S³`, and a `6`-cycle `a` of the sphere bundle with
`(inclChains PairXT PairAT).f 6 a = (singularChains ℤ PairXT).d 7 6 w`, such that the
Alexander–Whitney cup product of the pullbacks of `cochainDiff θ` and `β` along the second and first
projections of `S³ × D⁴` evaluates nontrivially on `w`.

This is the `(4,3)`-degree external-product statement for `S³ × (D⁴, S³)`; its mathematical content
is the nonvanishing of the Künneth pairing `H⁴(D⁴,S³) ⊗ H³(S³) → H⁷(S³ × D⁴, S³ × S³)`
(equivalently of the external product `H³(S³) ⊗ H³(S³) → H⁶(S³ × S³)`). -/
theorem mixedCupCycleEvalNeZero :
    ∃ (θ : Cochain ℤ (TopCat.toSSet.obj Disc4T) 3)
      (β : Cochain ℤ (TopCat.toSSet.obj Sph3T) 3)
      (w : (singularChains ℤ PairXT).X 7)
      (a : (singularChains ℤ (TopCat.of PairAT)).X 6),
      cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (sphereInUnit 4)))
          ((ModuleCat.Hom.hom ((restr ℤ Disc4T (sphereInUnit 4)).f 3)) θ) = 0
      ∧ cochainDiff ℤ (TopCat.toSSet.obj Sph3T) β = 0
      ∧ (inclChains PairXT PairAT).f 6 a
          = (singularChains ℤ PairXT).d 7 6 w
      ∧ kronecker ℤ (TopCat.toSSet.obj PairXT)
          (cup ℤ (TopCat.toSSet.obj PairXT)
            ((cochainPullbackHom ℤ PairXT Disc4T sndXT 4).hom
                (cochainDiff ℤ (TopCat.toSSet.obj Disc4T) θ))
            ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β))
          w ≠ 0 := by
  obtain ⟨θ', β, a, hθ', hβ, ha, hev⟩ := kunnethEvalCompat
  obtain ⟨θ, hθ⟩ := surjective_restr ℤ Disc4T (sphereInUnit 4) 3 θ'
  obtain ⟨w, hw⟩ := exists_seven_chain_boundary a ha
  refine ⟨θ, β, w, a, ?_, hβ, hw, ?_⟩
  · show cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (sphereInUnit 4)))
      ((ModuleCat.Hom.hom ((restr ℤ Disc4T (sphereInUnit 4)).f 3)) θ) = 0
    rw [hθ]; exact hθ'
  · -- the cochain of the statement is a coboundary
    have hd : cochainDiff ℤ (TopCat.toSSet.obj PairXT)
          (cup ℤ (TopCat.toSSet.obj PairXT)
            ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
            ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β))
        = cup ℤ (TopCat.toSSet.obj PairXT)
            ((cochainPullbackHom ℤ PairXT Disc4T sndXT 4).hom
              (cochainDiff ℤ (TopCat.toSSet.obj Disc4T) θ))
            ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β) :=
      (cup_diff_eq θ β hβ).symm
    rw [← hd]
    -- evaluate the coboundary on `w`
    have h1 : kronecker ℤ (TopCat.toSSet.obj PairXT)
        (cochainDiff ℤ (TopCat.toSSet.obj PairXT)
          (cup ℤ (TopCat.toSSet.obj PairXT)
            ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
            ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β))) w
        = kronecker ℤ (TopCat.toSSet.obj PairXT)
            (cup ℤ (TopCat.toSSet.obj PairXT)
              ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
              ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β))
            ((singularChains ℤ PairXT).d 7 6 w) := rfl
    rw [h1, ← hw]
    -- the pullback of the cup product along `A ⊆ X`
    have h2 : (cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclAX 6).hom
          (cup ℤ (TopCat.toSSet.obj PairXT)
            ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
            ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β))
        = cup ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
            ((cochainPullbackHom ℤ (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3).hom
              (((restr ℤ Disc4T (sphereInUnit 4)).f 3).hom θ))
            ((cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom β) := by
      have hcup := cup_pullbackHom (TopCat.of PairAT) PairXT inclAX 3 3
        ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
        ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β)
      rw [show (cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclAX 6).hom
            (cup ℤ (TopCat.toSSet.obj PairXT)
              ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
              ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β))
          = (cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclAX (3 + 3)).hom
              (cup ℤ (TopCat.toSSet.obj PairXT)
                ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
                ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β)) from rfl]
      rw [hcup, restr_pullback_snd θ, restr_pullback_fst β]
    have h3 : kronecker ℤ (TopCat.toSSet.obj PairXT)
          (cup ℤ (TopCat.toSSet.obj PairXT)
            ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
            ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β))
          ((inclChains PairXT PairAT).f 6 a)
        = kronecker ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
            ((cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclAX 6).hom
              (cup ℤ (TopCat.toSSet.obj PairXT)
                ((cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ)
                ((cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β))) a :=
      (cochainPullbackHom_apply ℤ (TopCat.of PairAT) PairXT inclAX 6 _ a).symm
    rw [h3, h2, hθ]
    exact hev

/-! ## The relative cap product in bidegree `(4,3)` -/

/-- A `7`-chain of `X` whose boundary lies in `C₆(A)` gives a class in `H₇(X,A)`, together with the
relation that its underlying relative chain is the image of the chain. -/
theorem iCycles_liftCycles_down (x : (relChains PairXT PairAT).X 7)
    (hx : (relChains PairXT PairAT).d 7 6 x = 0) :
    ∃ cc : (relChains PairXT PairAT).cycles 7,
      (ConcreteCategory.hom (HomologicalComplex.iCycles (relChains PairXT PairAT) 7)) cc = x := by
  have hk : (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ((relChains PairXT PairAT).X 7) x))
      ≫ (relChains PairXT PairAT).d 7 6 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show (ModuleCat.Hom.hom ((relChains PairXT PairAT).d 7 6))
      ((LinearMap.toSpanSingleton ℤ (↑((relChains PairXT PairAT).X 7)) x) 1) = 0
    rw [LinearMap.toSpanSingleton_apply_one]
    exact hx
  refine ⟨((relChains PairXT PairAT).liftCycles
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ((relChains PairXT PairAT).X 7) x))
    6 ((ComplexShape.down ℕ).next_eq' (i := 7) (j := 6) rfl) hk).hom 1, ?_⟩
  · have h := HomologicalComplex.liftCycles_i (relChains PairXT PairAT)
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ((relChains PairXT PairAT).X 7) x))
      6 ((ComplexShape.down ℕ).next_eq' (i := 7) (j := 6) rfl) hk
    have h2 := congrArg (fun (f : ModuleCat.of ℤ ℤ ⟶ (relChains PairXT PairAT).X 7) =>
      (ModuleCat.Hom.hom f) (1 : ℤ)) h
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply_one] using h2

/-- **The relative cap product of `(S³ × D⁴, S³ × S³)` in bidegree `(4,3)` is nonzero.** -/
theorem sph3DiscRelCapPairNeZero_of_eval :
    ∃ (u : relCohomology ℤ PairXT PairAT 4) (c : (relChains PairXT PairAT).homology 7),
      u ≠ 0 ∧ relCapPair PairXT PairAT 4 3 u c ≠ 0 := by
  obtain ⟨θ, β, w, a, hθ, hβ, hwa, hev⟩ := mixedCupCycleEvalNeZero
  -- the cochains
  set bt : Cochain ℤ (TopCat.toSSet.obj PairXT) 3 :=
    (cochainPullbackHom ℤ PairXT Disc4T sndXT 3).hom θ with hbt
  set α : Cochain ℤ (TopCat.toSSet.obj PairXT) 4 :=
    (cochainPullbackHom ℤ PairXT Disc4T sndXT 4).hom (cochainDiff ℤ (TopCat.toSSet.obj Disc4T) θ)
    with hα
  set γ : Cochain ℤ (TopCat.toSSet.obj PairXT) 3 :=
    (cochainPullbackHom ℤ PairXT Sph3T fstXT 3).hom β with hγ
  have hα_eq : α = cochainDiff ℤ (TopCat.toSSet.obj PairXT) bt :=
    (cochainDiff_pullback_snd θ).symm
  have hγ_coc : cochainDiff ℤ (TopCat.toSSet.obj PairXT) γ = 0 := cochainDiff_pullback_fst β hβ
  -- `α` is a relative cocycle
  have hαmem : α ∈ relKern ℤ PairXT PairAT 4 := by
    rw [relKern, LinearMap.mem_ker]
    show (ModuleCat.Hom.hom ((restr ℤ PairXT PairAT).f 4)) α = 0
    have e1 : (ModuleCat.Hom.hom ((restr ℤ PairXT PairAT).f 4)) α
        = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of PairAT))
            ((cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclAX 3).hom bt) := by
      have hr : (ModuleCat.Hom.hom ((restr ℤ PairXT PairAT).f 4))
          = (ModuleCat.Hom.hom
              (cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclAX (3 + 1))) := by
        rw [show (restr ℤ PairXT PairAT)
            = dualChainMap ℤ (TopCat.of PairAT) PairXT inclAX from rfl,
          Work.Cohomology.dualChainMap_f_hom]
        rfl
      rw [hr, hα_eq]
      exact cochainDiff_pullbackHom (TopCat.of PairAT) PairXT inclAX 3 bt
    rw [e1]
    have e2 : (cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclAX 3).hom bt
        = (cochainPullbackHom ℤ (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3).hom
            (((restr ℤ Disc4T (sphereInUnit 4)).f 3).hom θ) := restr_pullback_snd θ
    rw [e2]
    rw [← cochainDiff_pullbackHom (TopCat.of PairAT) (TopCat.of (sphereInUnit 4)) pj2A 3
      (((restr ℤ Disc4T (sphereInUnit 4)).f 3).hom θ)]
    rw [hθ, map_zero]
  have hαcoc : relDiffLM ℤ PairXT PairAT 4 ⟨α, hαmem⟩ = 0 := by
    apply Subtype.ext
    rw [relDiffLM_coe, Submodule.coe_zero, Work.Cohomology.singularCochain_d_apply ℤ PairXT α,
      hα_eq]
    exact cochainDiff_cochainDiff ℤ (TopCat.toSSet.obj PairXT) bt
  -- the relative cycle associated with `w`
  have hrel : (relChains PairXT PairAT).d 7 6 (relDualProj PairXT PairAT 7 w) = 0 := by
    show (ModuleCat.Hom.hom ((relChains PairXT PairAT).d 7 6))
      ((ModuleCat.Hom.hom (relDualProj PairXT PairAT 7)) w) = 0
    have hcomm := LinearMap.congr_fun (relDualProj_comm_lm PairXT PairAT 6) w
    simp only [LinearMap.comp_apply] at hcomm
    rw [hcomm]
    have hwa' : (ModuleCat.Hom.hom ((singularChains ℤ PairXT).d 7 6)) w
        = (ModuleCat.Hom.hom ((inclChains PairXT PairAT).f 6)) a := hwa.symm
    rw [hwa']
    exact relDualProj_incl_apply PairXT PairAT 6 a
  obtain ⟨cc, hcc⟩ := iCycles_liftCycles_down (relDualProj PairXT PairAT 7 w) hrel
  -- the classes
  let zα : (relComplex ℤ PairXT PairAT).cycles 4 := relCocycleOf ℤ PairXT PairAT ⟨α, hαmem⟩ hαcoc
  let u : relCohomology ℤ PairXT PairAT 4 :=
    (HomologicalComplex.homologyπ (relComplex ℤ PairXT PairAT) 4).hom zα
  let c : (relChains PairXT PairAT).homology 7 :=
    (HomologicalComplex.homologyπ (relChains PairXT PairAT) 7).hom cc
  -- the key evaluation
  have hkey : kronH ℤ (TopCat.toSSet.obj PairXT) 3
        (cohomologyClassOf ℤ (TopCat.toSSet.obj PairXT) γ hγ_coc)
        (relCapPair PairXT PairAT 4 3 u c)
      = kronecker ℤ (TopCat.toSSet.obj PairXT) (cup ℤ (TopCat.toSSet.obj PairXT) α γ) w := by
    show kronH ℤ (TopCat.toSSet.obj PairXT) 3
        (cohomologyClassOf ℤ (TopCat.toSSet.obj PairXT) γ hγ_coc)
        (relCapPair PairXT PairAT 4 3
          ((HomologicalComplex.homologyπ (relComplex ℤ PairXT PairAT) 4).hom zα)
          ((HomologicalComplex.homologyπ (relChains PairXT PairAT) 7).hom cc)) = _
    rw [relCapPair_apply PairXT PairAT 4 3 zα cc]
    rw [kronH_apply_sing PairXT γ hγ_coc]
    rw [relCapPairZ_iCycles PairXT PairAT 4 3 zα cc]
    rw [show (ConcreteCategory.hom (HomologicalComplex.iCycles (relComplex ℤ PairXT PairAT) 4))
        zα = ⟨α, hαmem⟩ from iCycles_relCocycleOf ℤ PairXT PairAT ⟨α, hαmem⟩ hαcoc]
    change γ ((ModuleCat.Hom.hom (relCapHalf ℤ PairXT PairAT ⟨α, hαmem⟩ 3))
        ((ModuleCat.Hom.hom (relChains_cokernelIso PairXT PairAT 7).hom)
          ((ConcreteCategory.hom (HomologicalComplex.iCycles (relChains PairXT PairAT) 7))
            cc)))
      = kronecker ℤ (TopCat.toSSet.obj PairXT) (cup ℤ (TopCat.toSSet.obj PairXT) α γ) w
    rw [hcc]
    change γ ((ModuleCat.Hom.hom (relCapHalf ℤ PairXT PairAT ⟨α, hαmem⟩ 3))
        ((ConcreteCategory.hom (relChains_cokernelIso PairXT PairAT 7).hom)
          ((ModuleCat.Hom.hom ((cokernel.π (inclChains PairXT PairAT)).f 7)) w)))
      = kronecker ℤ (TopCat.toSSet.obj PairXT) (cup ℤ (TopCat.toSSet.obj PairXT) α γ) w
    rw [relChains_cokernelIso_canon_apply PairXT PairAT 7 w]
    change γ ((ModuleCat.Hom.hom (relCapHalf ℤ PairXT PairAT ⟨α, hαmem⟩ 3))
        ((ModuleCat.Hom.hom (cokernel.π ((inclChains PairXT PairAT).f (4 + 3)))) w))
      = kronecker ℤ (TopCat.toSSet.obj PairXT) (cup ℤ (TopCat.toSSet.obj PairXT) α γ) w
    rw [relCapHalf_apply_incl PairXT PairAT (m := 3) ⟨α, hαmem⟩ w]
    exact kronecker_cap_cup ℤ (TopCat.toSSet.obj PairXT) α γ w
  refine ⟨u, c, ?_, ?_⟩
  · intro hu
    have h0 : relCapPair PairXT PairAT 4 3 u c = 0 := by
      rw [hu, LinearMap.map_zero (relCapPair PairXT PairAT 4 3)]
      exact LinearMap.zero_apply c
    have h1 : kronH ℤ (TopCat.toSSet.obj PairXT) 3
        (cohomologyClassOf ℤ (TopCat.toSSet.obj PairXT) γ hγ_coc)
        (relCapPair PairXT PairAT 4 3 u c) = 0 := by rw [h0, map_zero]
    rw [hkey] at h1
    exact hev h1
  · intro hcap
    have h1 : kronH ℤ (TopCat.toSSet.obj PairXT) 3
        (cohomologyClassOf ℤ (TopCat.toSSet.obj PairXT) γ hγ_coc)
        (relCapPair PairXT PairAT 4 3 u c) = 0 := by rw [hcap, map_zero]
    rw [hkey] at h1
    exact hev h1

/-! ## The assigned statement -/

/-- **The relative cap product of the pair `(S³ × D⁴, S³ × S³)` in bidegree `(4,3)` is nonzero.**

This is the "overlap case" input of `Work.Cohomology.Crux.vk_relCapPair_nonzero`: there are a
nonzero relative cohomology class `u ∈ H⁴(S³ × D⁴, S³ × S³)` and a relative homology class
`c ∈ H₇(S³ × D⁴, S³ × S³)` whose relative cap product `u ⌢ c ∈ H₃(S³ × D⁴)` is nonzero. -/
theorem sph3DiscRelCapPairNeZero :
    ∃ (u : Work.Cohomology.relCohomology ℤ Work.Cohomology.PairXT Work.Cohomology.PairAT 4)
      (c : (Work.Cohomology.relChains Work.Cohomology.PairXT Work.Cohomology.PairAT).homology 7),
      u ≠ 0 ∧ (Work.Cohomology.relCapPair Work.Cohomology.PairXT Work.Cohomology.PairAT 4 3 u c)
        ≠ 0 :=
  sph3DiscRelCapPairNeZero_of_eval

end

end Work.Cohomology.Compat
