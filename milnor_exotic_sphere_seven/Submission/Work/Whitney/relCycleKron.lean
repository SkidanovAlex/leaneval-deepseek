import Mathlib
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.Sd_isSmallChain
import Submission.Work.Cohomology.Kronecker
import Submission.Work.Whitney.sdIter_smallChain_local
import Submission.Work.Whitney.tcmSuspAux.pairing
import Submission.Work.Whitney.CutoffClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# A relative cochain on the small simplices of a subspace

The elementary input of both routes to the rank-one model product formula
(`Submission/Work/Whitney/rankOne_cup_model_NOTES.md` §39) is that a relative cochain
`u ∈ C^n(X,A)` pairs to zero with every chain carried by `A`:

  `u ∈ relKern ℤ X A n`, `IsSmallChain A ∅ c`  ⟹  `⟨u, c⟩ = 0`.

This is the "easy direction" of the well-definedness of the pairing of a relative class with a
relative cycle, and the first ingredient of the extension argument of §39 (route 1): it is what
makes `⟨d u, B⟩ = u(∂B) = 0` true for a chain `B` whose boundary is carried by `A`.

This file proves the two *pointwise* pieces:

* `exists_simplex_subtypeIncl_of_isSmall` — a simplex of `X` whose image lies in `A` comes from a
  simplex of the subspace `A` (the `Classical.choice`-free construction; the same pattern is used
  inline in `Submission/Work/Whitney/capEtaVanishing.lean`);
* `genEval_eq_zero_of_mem_relKern_of_isSmall` — the evaluation of a relative cochain on the
  generator of such a simplex vanishes (`genEval_eq_zero_of_mem_relKern`, `RelCap.lean`).

The chain-level upgrade (`IsSmallChain A ∅ c` in place of a single small simplex) is then the
"generators span" argument on the small complex `smallSSet A ∅`:
`SSet.chainComplex_hom_ext` reduces it to the two lemmas above, but the *spelling* of the induced
morphism has to match `Work.Cohomology.smallToSing_gen`'s statement; the exact goal state at which
the naive `rw [smallToSing_gen τ]` fails is recorded in `NOTES` §40 (the composite is displayed
fully unfolded as `(smallSSet A ∅).ιChainComplex τ ≫ (smallToSing A ∅).f n ≫ ModuleCat.ofHom ↑u`,
and `rw` refuses to match `(ConcreteCategory.hom ((smallToSing A ∅).f n)) (genSSet … τ)` against
it).  The fix is one `ModuleCat.hom_comp`/`LinearMap.comp_apply` normalisation *before*
`LinearMap.ext_ring`, not a mathematical gap.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- **A simplex whose image lies in the subspace `A` comes from a simplex of `A`.** -/
theorem exists_simplex_subtypeIncl_of_isSmall {A : Set X} {n : ℕ} {σ : Simplex X n}
    (hσ : IsSmall A (∅ : Set X) σ) :
    ∃ τ : Simplex (TopCat.of A) n, (TopCat.toSSet.map (subtypeIncl X A)).app
      (Opposite.op ⦋n⦌) τ = σ := by
  rw [isSmall_iff] at hσ
  rcases hσ with h | h
  · refine ⟨(TopCat.toSSetObjEquivOld (TopCat.of A) (Opposite.op ⦋n⦌)).symm
      ⟨fun z => (⟨(TopCat.toSSetObjEquivOld X (Opposite.op ⦋n⦌)) σ z,
          h (Set.mem_range_self z)⟩ : ↥A),
        Continuous.subtype_mk ((TopCat.toSSetObjEquivOld X (Opposite.op ⦋n⦌)) σ).continuous _⟩, ?_⟩
    apply (TopCat.toSSetObjEquivOld X (Opposite.op ⦋n⦌)).injective
    apply ContinuousMap.ext
    intro z
    rw [TopCat.toSSetObjEquivOld_map_apply, Equiv.apply_symm_apply]
    rfl
  · exfalso
    rcases Set.range_nonempty (fun z : (Delta n : TopCat) => sdMap n σ z) with ⟨y, hy⟩
    simpa using h hy

/-- **A relative cochain vanishes on the generator of a small simplex.** -/
theorem genEval_eq_zero_of_mem_relKern_of_isSmall (X : TopCat) {A : Set X} {n : ℕ}
    (u : ↥(relKern ℤ X A n)) {σ : Simplex X n} (hσ : IsSmall A (∅ : Set X) σ) :
    genEval ℤ (TopCat.toSSet.obj X)
      (show Cochain ℤ (TopCat.toSSet.obj X) n from u.1) σ = 0 := by
  obtain ⟨τ, hτ⟩ := exists_simplex_subtypeIncl_of_isSmall hσ
  have h2 := genEval_eq_zero_of_mem_relKern ℤ X A u.1 u.2 τ
  rw [hτ] at h2
  exact h2

/-- **(★): a relative cochain pairs to zero with every chain carried by the subspace.** -/
theorem kronecker_eq_zero_of_isSmallChain_of_mem_relKern (X : TopCat) {A : Set X} {n : ℕ}
    (u : ↥(relKern ℤ X A n)) (c : (singularChains ℤ X).X n)
    (hc : IsSmallChain A (∅ : Set X) c) :
    kronecker ℤ (TopCat.toSSet.obj X) (show Cochain ℤ (TopCat.toSSet.obj X) n from u.1) c = 0 := by
  classical
  obtain ⟨c', hc'⟩ := hc
  let Q : Submodule ℤ ↥((smallChains A (∅ : Set X)).X n) :=
    Submodule.comap ((smallToSing A (∅ : Set X)).f n).hom
      (LinearMap.ker (show Cochain ℤ (TopCat.toSSet.obj X) n from u.1))
  have hQ : Q = ⊤ := by
    refine mem_of_genSSet (smallSSet A (∅ : Set X)) n Q ?_
    intro τ
    show ((smallToSing A (∅ : Set X)).f n).hom (genSSet (smallSSet A (∅ : Set X)) n τ)
      ∈ LinearMap.ker (show Cochain ℤ (TopCat.toSSet.obj X) n from u.1)
    rw [smallToSing_gen τ, LinearMap.mem_ker]
    have hgen : (show Cochain ℤ (TopCat.toSSet.obj X) n from u.1) (gen X n τ.1) = 0 :=
      genEval_eq_zero_of_mem_relKern_of_isSmall X u τ.2
    exact hgen
  have hmem : c' ∈ Q := by rw [hQ]; exact Submodule.mem_top
  have hval : (show Cochain ℤ (TopCat.toSSet.obj X) n from u.1)
      (((smallToSing A (∅ : Set X)).f n).hom c') = 0 := hmem
  rw [← hc']
  exact hval

end

end Work.Cohomology

/-! ## Axiom check -/

#print axioms Work.Cohomology.exists_simplex_subtypeIncl_of_isSmall
#print axioms Work.Cohomology.genEval_eq_zero_of_mem_relKern_of_isSmall
#print axioms Work.Cohomology.kronecker_eq_zero_of_isSmallChain_of_mem_relKern

/-! ## Axiom check -/

#print axioms Work.Cohomology.exists_simplex_subtypeIncl_of_isSmall
#print axioms Work.Cohomology.genEval_eq_zero_of_mem_relKern_of_isSmall
#print axioms Work.Cohomology.kronecker_eq_zero_of_isSmallChain_of_mem_relKern

namespace Work.Cohomology
/-! ## (GAP): representative-independence of the pairing on a relative cycle

The single-set specialisation of `Work.Whitney.kronecker_pdABCohR_eq_of_homology_eq`
(`tcmSuspAux/pairing.lean`): two relative cocycles with the same class pair equally with a chain
whose boundary is carried by `A`.  The "pairing with a coboundary vanishes" input is now (★). -/

section Gap

/-- **(GAP).**  Two cocycles of `C^{k+1}(X,A)` with the same cohomology class pair equally with
every chain whose boundary is carried by `A`. -/
theorem kronecker_relComplex_eq_of_homology_eq {X : TopCat} (A : Set X) (k : ℕ)
    (γ γ' : (relComplex ℤ X A).X (k + 1))
    (hγ : (relComplex ℤ X A).d (k + 1) (k + 1 + 1) γ = 0)
    (hγ' : (relComplex ℤ X A).d (k + 1) (k + 1 + 1) γ' = 0)
    (h : (relComplex ℤ X A).homologyπ (k + 1) (cocycleOfK (relComplex ℤ X A) γ hγ)
        = (relComplex ℤ X A).homologyπ (k + 1) (cocycleOfK (relComplex ℤ X A) γ' hγ'))
    (Z : (singularChains ℤ X).X (k + 1))
    (hZ : IsSmallChain A (∅ : Set X) (((singularChains ℤ X).d (k + 1) k) Z)) :
    kronecker ℤ (TopCat.toSSet.obj X) (show Cochain ℤ (TopCat.toSSet.obj X) (k + 1) from γ.1) Z
      = kronecker ℤ (TopCat.toSSet.obj X)
          (show Cochain ℤ (TopCat.toSSet.obj X) (k + 1) from γ'.1) Z := by
  classical
  have hd : (relComplex ℤ X A).d (k + 1) (k + 1 + 1) (γ - γ') = 0 := by
    rw [map_sub, hγ, hγ', sub_self]
  have hcyc : cocycleOfK (relComplex ℤ X A) (γ - γ') hd
      = cocycleOfK (relComplex ℤ X A) γ hγ
        - cocycleOfK (relComplex ℤ X A) γ' hγ' := by
    apply (ModuleCat.mono_iff_injective ((relComplex ℤ X A).iCycles (k + 1))).mp inferInstance
    rw [map_sub, iCycles_cocycleOfK, iCycles_cocycleOfK, iCycles_cocycleOfK]
  have hzero : (relComplex ℤ X A).homologyπ (k + 1)
      (cocycleOfK (relComplex ℤ X A) (γ - γ') hd) = 0 := by
    rw [hcyc, map_sub, h, sub_self]
  obtain ⟨η, hη⟩ := pd_us_ab_resolve_exists_of_homologyπ_eq_zero (relComplex ℤ X A) k _ hzero
  have hη' : γ - γ' = (relComplex ℤ X A).d k (k + 1) η := by
    rw [hη, iCycles_cocycleOfK]
  have hcoe : (γ.1 - γ'.1 : Cochain ℤ (TopCat.toSSet.obj X) (k + 1))
      = cochainDiff ℤ (TopCat.toSSet.obj X) η.1 := by
    have h2 : ((γ - γ').1 : Cochain ℤ (TopCat.toSSet.obj X) (k + 1))
        = (((relComplex ℤ X A).d k (k + 1)) η).1 := congrArg Subtype.val hη'
    rw [show (γ.1 - γ'.1 : Cochain ℤ (TopCat.toSSet.obj X) (k + 1)) = (γ - γ').1 from rfl, h2,
      relComplex_d]
    simp only [relDiff, ModuleCat.hom_ofHom, relDiffLM_coe]
    exact singularCochain_d_apply ℤ (TopCat.of X)
      (show Cochain ℤ (TopCat.toSSet.obj X) k from η.1)
  have heval : kronecker ℤ (TopCat.toSSet.obj X)
      (cochainDiff ℤ (TopCat.toSSet.obj X) η.1) Z = 0 := by
    have hdZ : kronecker ℤ (TopCat.toSSet.obj X)
        (show Cochain ℤ (TopCat.toSSet.obj X) k from η.1)
        (((singularChains ℤ X).d (k + 1) k) Z) = 0 :=
      kronecker_eq_zero_of_isSmallChain_of_mem_relKern X η _ hZ
    have hgoal : kronecker ℤ (TopCat.toSSet.obj X)
        (cochainDiff ℤ (TopCat.toSSet.obj X) η.1) Z
        = kronecker ℤ (TopCat.toSSet.obj X)
            (show Cochain ℤ (TopCat.toSSet.obj X) k from η.1)
            (((singularChains ℤ X).d (k + 1) k) Z) := rfl
    rw [hgoal]
    exact hdZ
  have hsum : (show Cochain ℤ (TopCat.toSSet.obj X) (k + 1) from γ'.1)
      + cochainDiff ℤ (TopCat.toSSet.obj X) η.1
      = (show Cochain ℤ (TopCat.toSSet.obj X) (k + 1) from γ.1) := by
    rw [← hcoe]
    abel
  rw [← hsum]
  rw [kronecker_add, heval, add_zero]


/-- **The bridge between the two spellings of the relative differential.**  A relative cochain is a
cocycle for the differential of `relComplex ℤ X A` iff it is a cocycle for `relDiffLM`; the two are
`rfl`-equal but the `ModuleCat.Hom.hom` wrapper and the `relDiff`-definition stop `rw` from matching
across them (see `rankOne_cup_model_NOTES.md` §42b). -/
theorem relDiffLM_eq_zero_iff (X : TopCat) (A : Set X) (k : ℕ) (x : ↥(relKern ℤ X A k)) :
    ((ModuleCat.Hom.hom ((relComplex ℤ X A).d k (k + 1))) x = 0)
      ↔ relDiffLM ℤ X A k x = 0 := by
  constructor
  · intro h
    rwa [relComplex_d, relDiff, ModuleCat.hom_ofHom] at h
  · intro h
    rwa [relComplex_d, relDiff, ModuleCat.hom_ofHom]

/-- **Stokes by value**: the dual differential applied to `bt` evaluates on `W` as `bt (∂W)`.
Stated through `kronecker` (whose argument is a `Cochain`, which forces the necessary ascription) and
proved by unfolding `singularCochain_d_eq` — the carrier of
`(singularCochainComplex ℤ X).X ·` is not reducible to a function type for an application, so the
abbreviation has to be unfolded *inside the goal* (`rankOne_cup_model_NOTES.md` §42g/§42h). -/
theorem singularCochain_d_apply_value {X : TopCat} (n : ℕ)
    (bt : Cochain ℤ (TopCat.toSSet.obj X) n) (W : (singularChains ℤ X).X (n + 1)) :
    kronecker ℤ (TopCat.toSSet.obj X)
        (show Cochain ℤ (TopCat.toSSet.obj X) (n + 1) from
          (ModuleCat.Hom.hom ((singularCochainComplex ℤ X).d n (n + 1))) bt) W
      = kronecker ℤ (TopCat.toSSet.obj X) (show Cochain ℤ (TopCat.toSSet.obj X) n from bt)
          (((singularChains ℤ X).d (n + 1) n) W) := by
  rw [singularCochain_d_eq ℤ X n]
  rfl

/-- **The transgression pairing.**  Any cocycle representing `pairδ(X,A,n)([b])` evaluates on a
chain `W` with `A`-small boundary as `bt (∂W)`, for any lift `bt` of any cocycle representative `b`
of the class on `A`. -/
theorem kronecker_pairδ_apply {X : TopCat} (A : Set X) (n : ℕ)
    (b : Cochain ℤ (TopCat.toSSet.obj (TopCat.of A)) n)
    (hb : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of A)) b = 0)
    (bt : Cochain ℤ (TopCat.toSSet.obj X) n) (hbt : (restr ℤ X A).f n bt = b)
    (w : ↥(relKern ℤ X A (n + 1))) (hw : relDiffLM ℤ X A (n + 1) w = 0)
    (hcl : relClassOf ℤ X A w hw
      = pairδ ℤ X A n (cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of A)) b hb))
    (W : (singularChains ℤ X).X (n + 1))
    (hW : IsSmallChain A (∅ : Set X) (((singularChains ℤ X).d (n + 1) n) W)) :
    kronecker ℤ (TopCat.toSSet.obj X) (show Cochain ℤ (TopCat.toSSet.obj X) (n + 1) from w.1) W
      = kronecker ℤ (TopCat.toSSet.obj X) (show Cochain ℤ (TopCat.toSSet.obj X) n from bt)
          (((singularChains ℤ X).d (n + 1) n) W) := by
  classical
  obtain ⟨hmem, hcoc, hpair⟩ := Work.Sph3Disc.pdmc_pairδ_lift X A n b hb bt hbt
  have hwd : (ModuleCat.Hom.hom ((relComplex ℤ X A).d (n + 1) (n + 1 + 1))) w = 0 :=
    (relDiffLM_eq_zero_iff X A (n + 1) w).mpr hw
  have hcocd : (ModuleCat.Hom.hom ((relComplex ℤ X A).d (n + 1) (n + 1 + 1)))
      ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ = 0 :=
    (relDiffLM_eq_zero_iff X A (n + 1) _).mpr hcoc
  have h1 : (relComplex ℤ X A).homologyπ (n + 1) (cocycleOfK (relComplex ℤ X A) w hwd)
      = (relComplex ℤ X A).homologyπ (n + 1)
        (cocycleOfK (relComplex ℤ X A)
          ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ hcocd) := by
    rw [← relClassOf_eq_homologyπ_cocycleOfK ℤ X A w hw hwd,
      ← relClassOf_eq_homologyπ_cocycleOfK ℤ X A
        ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ hcoc hcocd]
    exact hcl.trans hpair
  have h2 := kronecker_relComplex_eq_of_homology_eq A n w
    ⟨((singularCochainComplex ℤ X).d n (n + 1)).hom bt, hmem⟩ hwd hcocd h1 W hW
  exact h2.trans (singularCochain_d_apply_value n bt W)

end Gap
end Work.Cohomology

/-! ## Axiom check (GAP) -/

#print axioms Work.Cohomology.singularCochain_d_apply_value
#print axioms Work.Cohomology.kronecker_pairδ_apply
#print axioms Work.Cohomology.relDiffLM_eq_zero_iff
#print axioms Work.Cohomology.kronecker_relComplex_eq_of_homology_eq
