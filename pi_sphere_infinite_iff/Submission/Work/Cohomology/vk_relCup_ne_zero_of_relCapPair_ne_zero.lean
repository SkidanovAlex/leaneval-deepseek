import Mathlib
import Submission.Work.Cohomology.cohomologyPairVk
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.RelCupTransfer
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.kronH_isIso
import Submission.Work.Cohomology.relCapH_kronH_cup
import Submission.Work.Milnor.homology_Vk

/-!
# The Thom class squares to a nonzero class

Let `X = Vk (-2)` be the total space of Milnor's disc bundle over `S⁴` and `A = Mk (-2)` its unit
sphere bundle.  The relative cohomology `H⁴(X,A;ℤ) ≅ ℤ` contains the Thom class, and this file
proves the *bridge* that turns the non-vanishing of the relative cap-product pairing

  `⌢ : H⁴(X,A) × H₈(X,A) ⟶ H₄(X)`

into the non-vanishing of the relative cup square `u ⌣ u ∈ H⁸(X,A;ℤ) ≅ ℤ`:

  `(∃ c, u ⌢ c ≠ 0)  ⟹  u ⌣ u ≠ 0`.

## The argument

Writing `u = [a]` for a relative cocycle `a` and choosing a relative cycle `c = [cc]` together with
an absolute chain lift `ẑ ∈ C₈(X)` of `cc`, the chain-level cap/cup identity
(`Work.Cohomology.relKronecker_cap_cup`) reads

  `⟨a, u ⌢ c⟩ = (u ⌣ u)(ẑ)`,

i.e. the absolute Kronecker pairing `⟨relIncl u, u ⌢ c⟩` of the image of `u` in `H⁴(X)` with the
cap-product class `u ⌢ c ∈ H₄(X)` equals the evaluation of `u ⌣ u` on `ẑ`.

* The left-hand side is nonzero: `H⁴(X) ≅ H₄(X) ≅ ℤ` and the absolute Kronecker pairing is
  unimodular (`kronH_isIso`), so a nonzero class in `H⁴(X)` pairs nontrivially with every nonzero
  class in `H₄(X)`; here `relIncl u ≠ 0` (`H³(A) = 0`) and `u ⌢ c ≠ 0` by hypothesis.
* If `u ⌣ u = 0`, then `relCup a a` is a relative coboundary, `relCup a a = δw`; evaluating on
  `ẑ` gives `(cochainDiff w)(ẑ) = w(dẑ)`, and `dẑ` is supported on `A` (its projection to
  `C₇(X,A)` is `d` of the relative cycle `cc`), where the relative cochain `w` vanishes.  So the
  right-hand side is `0`, a contradiction.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## `relClassOf = 0` means "is a relative coboundary" -/

/-- A relative cocycle whose class in `H⁸(X,A;ℤ)` vanishes is the differential of a relative
cochain of degree `7`. -/
lemma exists_relDiff_of_relClassOf_eq_zero (X : TopCat) (A : Set X)
    (a : relKern ℤ X A 8) (ha : relDiffLM ℤ X A 8 a = 0)
    (h : relClassOf ℤ X A a ha = 0) :
    ∃ w : (relComplex ℤ X A).X 7, (relComplex ℤ X A).d 7 8 w = a := by
  have hz : ((relComplex ℤ X A).homologyπ 8).hom (relCocycleOf ℤ X A a ha) = 0 := h
  have hp : (ComplexShape.up ℕ).prev 8 = 7 :=
    ComplexShape.prev_eq' (ComplexShape.up ℕ) (i := 8) (j := 7)
      (show (ComplexShape.up ℕ).Rel 7 8 from rfl)
  let S : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk ((relComplex ℤ X A).toCycles 7 8) ((relComplex ℤ X A).homologyπ 8)
      ((relComplex ℤ X A).toCycles_comp_homologyπ 7 8)
  have hS : S.Exact :=
    S.exact_of_g_is_cokernel ((relComplex ℤ X A).homologyIsCokernel 7 8 hp)
  have hrk : ((relComplex ℤ X A).toCycles 7 8).hom.range
      = ((relComplex ℤ X A).homologyπ 8).hom.ker :=
    ShortComplex.Exact.moduleCat_range_eq_ker hS
  have hz' : relCocycleOf ℤ X A a ha ∈ ((relComplex ℤ X A).homologyπ 8).hom.ker := by
    rw [LinearMap.mem_ker]; exact hz
  rw [← hrk] at hz'
  obtain ⟨w, hw⟩ := hz'
  refine ⟨w, ?_⟩
  have h3 := congrArg (fun (g : (relComplex ℤ X A).X 7 ⟶ (relComplex ℤ X A).X 8) => g.hom w)
    (HomologicalComplex.toCycles_i (relComplex ℤ X A) 7 8)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h3
  rw [← h3, hw, iCycles_relCocycleOf ℤ X A a ha]

/-! ## Computing `⟨relIncl u, u ⌢ c⟩` on representatives -/

/-- **The cap/cup pairing on representatives.**  For relative cocycles `a` (degree `n`) and `b`
(degree `m`), a relative cycle `cc` of degree `n+m` and an absolute chain lift `ẑ` of `cc`, the
absolute Kronecker pairing of the image of `b` in `H^m(X)` with `[a] ⌢ [cc]` is the evaluation of
`b` on the cap product `a.1 ⌢ ẑ`. -/
lemma kronH_relIncl_relCapPair (X : TopCat) (A : Set X) {n m : ℕ}
    (a : relKern ℤ X A n) (ha : relDiffLM ℤ X A n a = 0)
    (b : relKern ℤ X A m) (hb : relDiffLM ℤ X A m b = 0)
    (cc : (relChains X A).cycles (n + m))
    (zhat : (singularChains ℤ X).X (n + m))
    (hzhat : (cokernel.π ((inclChains X A).f (n + m))).hom zhat
              = (relChains_cokernelIso X A (n + m)).hom ((relChains X A).iCycles (n + m) cc)) :
    kronH ℤ (TopCat.toSSet.obj X) m
      ((HomologicalComplex.homologyMap (relIncl ℤ X A) m).hom (relClassOf ℤ X A b hb))
      ((relCapPair X A n m) (relClassOf ℤ X A a ha) (((relChains X A).homologyπ (n + m)) cc))
    = kronecker ℤ (TopCat.toSSet.obj X) (b.1 : Cochain ℤ (TopCat.toSSet.obj X) m)
        ((cap ℤ (TopCat.toSSet.obj X) (a.1 : Cochain ℤ (TopCat.toSSet.obj X) n) m) zhat) := by
  have hαc : relClassOf ℤ X A a ha
      = ((relComplex ℤ X A).homologyπ n) (relCocycleOf ℤ X A a ha) := rfl
  rw [relIncl_homologyMap_relClassOf ℤ X A b hb]
  rw [hαc]
  rw [relCapPair_apply X A n m (relCocycleOf ℤ X A a ha) cc]
  rw [kronH_apply_sing X (b.1 : Cochain ℤ (TopCat.toSSet.obj X) m)
    (relClassOf_cochainDiff ℤ X A b hb)
    (relCapPairZ X A n m (relCocycleOf ℤ X A a ha) cc)]
  rw [relCapPairZ_iCycles X A n m (relCocycleOf ℤ X A a ha) cc]
  rw [iCycles_relCocycleOf ℤ X A a ha]
  rw [← hzhat]
  exact congrArg (fun w => kronecker ℤ (TopCat.toSSet.obj X)
      (b.1 : Cochain ℤ (TopCat.toSSet.obj X) m) w)
    (relCapHalf_apply_incl X A a zhat)

/-! ## Vanishing of the coboundary term -/

/-- A relative `7`-cochain evaluated on an `8`-chain whose boundary dies in `C₇(X,A)` is zero: the
boundary is supported on `A`, where the relative cochain vanishes. -/
lemma relCochainDiff_apply_eq_zero (X : TopCat) (A : Set X)
    (w : relKern ℤ X A 7) (zhat : (singularChains ℤ X).X 8)
    (h : (cokernel.π ((inclChains X A).f 7)).hom ((singularChains ℤ X).d 8 7 zhat) = 0) :
    (cochainDiff ℤ (TopCat.toSSet.obj X) (w.1 : Cochain ℤ (TopCat.toSSet.obj X) 7)) zhat = 0 := by
  have hEx : (ShortComplex.mk ((inclChains X A).f 7) (cokernel.π ((inclChains X A).f 7))
      (cokernel.condition _)).Exact := ShortComplex.exact_cokernel ((inclChains X A).f 7)
  have hrk := ShortComplex.Exact.moduleCat_range_eq_ker hEx
  have hmem : ((singularChains ℤ X).d 8 7 zhat)
      ∈ ((cokernel.π ((inclChains X A).f 7)).hom).ker := by
    rw [LinearMap.mem_ker]; exact h
  rw [← hrk] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hw : ((inclChains X A).f 7).hom.dualMap (w.1) = 0 := by
    have h2 := w.2
    simp only [relKern, LinearMap.mem_ker] at h2
    change ((dualChainMap ℤ (TopCat.of A) X (subtypeIncl X A)).f 7).hom (w.1) = 0 at h2
    rw [dualChainMap_f_hom ℤ (TopCat.of A) X (subtypeIncl X A) 7] at h2
    exact h2
  have hcd : (cochainDiff ℤ (TopCat.toSSet.obj X) (w.1 : Cochain ℤ (TopCat.toSSet.obj X) 7)) zhat
      = kronecker ℤ (TopCat.toSSet.obj X) (w.1 : Cochain ℤ (TopCat.toSSet.obj X) 7)
          (((singularChains ℤ X).d 8 7) zhat) := rfl
  rw [hcd, ← hy]
  rw [show kronecker ℤ (TopCat.toSSet.obj X) (w.1 : Cochain ℤ (TopCat.toSSet.obj X) 7)
        (((inclChains X A).f 7).hom y)
      = (((inclChains X A).f 7).hom.dualMap (w.1)) y from rfl]
  rw [hw, LinearMap.zero_apply]

/-- The boundary of a lift `ẑ` of a relative cycle `cc` projects to `0` in `C₇(X,A)`. -/
lemma proj_d_zhat_eq_zero (X : TopCat) (A : Set X) (cc : (relChains X A).cycles 8)
    (zhat : (singularChains ℤ X).X 8)
    (hzhat : (cokernel.π ((inclChains X A).f 8)).hom zhat
              = (relChains_cokernelIso X A 8).hom ((relChains X A).iCycles 8 cc)) :
    (cokernel.π ((inclChains X A).f 7)).hom ((singularChains ℤ X).d 8 7 zhat) = 0 := by
  have hπ : ((cokernel.π (inclChains X A)).f 8) zhat = ((relChains X A).iCycles 8) cc := by
    apply (ModuleCat.mono_iff_injective ((relChains_cokernelIso X A 8).hom)).mp inferInstance
    rw [relChains_cokernelIso_canon_apply, hzhat]
  have hcomm : ((cokernel.π (inclChains X A)).f 7) (((singularChains ℤ X).d 8 7) zhat)
      = ((relChains X A).d 8 7) (((cokernel.π (inclChains X A)).f 8) zhat) :=
    (chainMap_comm_apply _ _ (cokernel.π (inclChains X A)) 8 7 zhat).symm
  have hzero : ((relChains X A).d 8 7) (((relChains X A).iCycles 8) cc) = 0 := by
    have h := congrArg (fun (g : (relChains X A).cycles 8 ⟶ (relChains X A).X 7) => g.hom cc)
      (HomologicalComplex.iCycles_d (relChains X A) 8 7)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have h1 : (relChains_cokernelIso X A 7).hom
      (((cokernel.π (inclChains X A)).f 7) (((singularChains ℤ X).d 8 7) zhat)) = 0 := by
    rw [hcomm, hπ, hzero, map_zero]
  rw [← h1, relChains_cokernelIso_canon_apply]

/-- If `relCup a a = δw` then the evaluation of the relative cup square on a lift `ẑ` of the
relative cycle `cc` vanishes. -/
lemma relCup_eval_zhat_eq_zero (X : TopCat) (A : Set X) (a : relKern ℤ X A 4)
    (w : (relComplex ℤ X A).X 7) (zhat : (singularChains ℤ X).X 8)
    (hw : (relComplex ℤ X A).d 7 8 w = relCup ℤ X A 4 4 a a)
    (hproj : (cokernel.π ((inclChains X A).f 7)).hom ((singularChains ℤ X).d 8 7 zhat) = 0) :
    kronecker ℤ (TopCat.toSSet.obj X)
      (((relCup ℤ X A 4 4 a a).1) : Cochain ℤ (TopCat.toSSet.obj X) 8) zhat = 0 := by
  have h1 : ((relCup ℤ X A 4 4 a a).1 : Cochain ℤ (TopCat.toSSet.obj X) 8)
      = cochainDiff ℤ (TopCat.toSSet.obj X) ((show relKern ℤ X A 7 from w).1) := by
    rw [← hw]
    rw [relComplex_d]
    change (relDiffLM ℤ X A 7 (show relKern ℤ X A 7 from w)).1
      = cochainDiff ℤ (TopCat.toSSet.obj X) (show relKern ℤ X A 7 from w).1
    rw [relDiffLM_coe_cochainDiff]
  rw [h1]
  simpa only [kronecker] using
    relCochainDiff_apply_eq_zero X A (show relKern ℤ X A 7 from w) zhat hproj

/-! ## `H³(A) = 0`, hence `H⁴(X,A) → H⁴(X)` is injective -/

/-- The unit sphere bundle `A = Mk (-2) ≃ S⁷` has vanishing degree-`3` singular cohomology. -/
lemma isZero_singularCohomology_vkPairA_three :
    IsZero (singularCohomology ℤ 3 (TopCat.of vkPairA)) := by
  obtain ⟨hmk⟩ := Work.Milnor.mkToVkRangeHomeomorph (-2)
  obtain ⟨e⟩ := cohomologyIso_of_homotopyEquiv hmk.symm.toHomotopyEquiv 3
  obtain ⟨e2⟩ := Work.Milnor.cohomology_Mk_minus_two 3
  have hfin : (if (3:ℕ) = 0 then 1 else 0) + (if (3:ℕ) = 7 then 1 else 0) = 0 := by norm_num
  have hz : IsZero (ModuleCat.of ℤ
      (Fin ((if (3:ℕ) = 0 then 1 else 0) + (if (3:ℕ) = 7 then 1 else 0)) → ℤ)) := by
    rw [hfin, ModuleCat.isZero_iff_subsingleton]; infer_instance
  exact IsZero.of_iso hz (e ≪≫ e2)

/-! ## Non-degeneracy of the absolute Kronecker pairing in degree `4` -/

/-- `ℤᵏ` for `k = 0, 1` is written as a function type; this is the unique generator of
`Fin 1 → ℤ`. -/
lemma finone_eq_smul (f : Fin 1 → ℤ) : f = f 0 • (Pi.single 0 1 : Fin 1 → ℤ) := by
  funext i
  fin_cases i
  simp

/-- **Non-degeneracy of the Kronecker pairing of `Vk (-2)` in degree `4`.**  Since
`H⁴(Vk(-2)) ≅ ℤ ≅ H₄(Vk(-2))` and the pairing is unimodular, a nonzero cohomology class pairs
nontrivially with a nonzero homology class. -/
lemma kronH_ne_zero_of_ne_zero_vkPairX
    (x : (singularCochainComplex ℤ vkPairX).homology 4)
    (y : (singularChains ℤ vkPairX).homology 4)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    kronH ℤ (TopCat.toSSet.obj vkPairX) 4 x y ≠ 0 := by
  have hfree : ∀ n, Module.Free ℤ ↥((singularChains ℤ vkPairX).homology n) := by
    intro n
    obtain ⟨e⟩ := Work.Milnor.homology_Vk (-2) n
    haveI : Module.Free ℤ
        ↥(ModuleCat.of ℤ (Fin ((if n = 0 then 1 else 0) + (if n = 4 then 1 else 0)) → ℤ)) :=
      inferInstance
    exact Module.Free.of_equiv e.toLinearEquiv.symm
  have hbij := kronH_isIso vkPairX hfree 4
  have hx' : kronH ℤ (TopCat.toSSet.obj vkPairX) 4 x ≠ 0 := by
    intro h
    refine hx (hbij.1 ?_)
    simp [h]
  obtain ⟨e⟩ := Work.Milnor.homology_Vk (-2) 4
  have hidx : (if (4:ℕ) = 0 then 1 else 0) + (if (4:ℕ) = 4 then 1 else 0) = 1 := by norm_num
  rw [hidx] at e
  let eL : (singularChains ℤ vkPairX).homology 4 ≃ₗ[ℤ] (Fin 1 → ℤ) := e.toLinearEquiv
  let φ : (singularChains ℤ vkPairX).homology 4 →ₗ[ℤ] ℤ :=
    kronH ℤ (TopCat.toSSet.obj vkPairX) 4 x
  let ψ : (Fin 1 → ℤ) →ₗ[ℤ] ℤ := φ.comp (eL.symm : (Fin 1 → ℤ) →ₗ[ℤ] _)
  have hψne : ψ ≠ 0 := by
    intro h0
    apply hx'
    have hφ : φ = ψ.comp (eL : _ →ₗ[ℤ] (Fin 1 → ℤ)) := by
      ext z
      simp only [ψ, LinearMap.comp_apply]
      congr 1
      exact (LinearEquiv.symm_apply_apply eL z).symm
    rw [show kronH ℤ (TopCat.toSSet.obj vkPairX) 4 x = φ from rfl, hφ, h0, LinearMap.zero_comp]
  have hψgen : ψ (Pi.single 0 1 : Fin 1 → ℤ) ≠ 0 := by
    intro h
    apply hψne
    apply LinearMap.ext
    intro f
    rw [LinearMap.zero_apply]
    calc ψ f = ψ (f 0 • (Pi.single 0 1 : Fin 1 → ℤ)) := congrArg ψ (finone_eq_smul f)
      _ = f 0 • ψ (Pi.single 0 1) := by rw [map_smul]
      _ = 0 := by rw [h, smul_zero]
  have ha : eL y ≠ 0 := by
    intro h; exact hy (eL.injective (by rw [h, map_zero]))
  have ha0 : (eL y) 0 ≠ 0 := by
    intro h
    apply ha
    funext i; fin_cases i
    simpa using h
  have hgoal : kronH ℤ (TopCat.toSSet.obj vkPairX) 4 x y = ψ (eL y) := by
    change φ y = ψ (eL y)
    simp only [ψ, LinearMap.comp_apply]
    congr 1
    exact (LinearEquiv.symm_apply_apply eL y).symm
  rw [hgoal, finone_eq_smul (eL y), map_smul, smul_eq_mul]
  exact mul_ne_zero ha0 hψgen

/-! ## The bridge -/

theorem vk_relCup_ne_zero_of_relCapPair_ne_zero
    (u : Work.Cohomology.relCohomology ℤ Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4)
    (h : ∃ c : (Work.Cohomology.relChains Work.Cohomology.vkPairX Work.Cohomology.vkPairA).homology 8,
      (Work.Cohomology.relCapPair Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4 4 u c) ≠ 0) :
    Work.Cohomology.relCupH' ℤ Work.Cohomology.vkPairX Work.Cohomology.vkPairA 4 4 u u ≠ 0 := by
  intro h0
  obtain ⟨c, hc⟩ := h
  -- `u ≠ 0`
  have hu : u ≠ 0 := by
    intro hu
    rw [hu] at hc
    exact hc (by simp)
  -- `relIncl u ≠ 0`
  haveI : Mono (HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4) :=
    mono_of_exact_of_isZero_src (pair_exact₁ ℤ vkPairX vkPairA 3)
      isZero_singularCohomology_vkPairA_three
  have hinj := (ModuleCat.mono_iff_injective
    (HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4)).mp inferInstance
  have hxu : (HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4).hom u ≠ 0 :=
    fun hh => hu (hinj (by simpa using hh))
  -- the left-hand side is nonzero
  have hne : kronH ℤ (TopCat.toSSet.obj vkPairX) 4
      ((HomologicalComplex.homologyMap (relIncl ℤ vkPairX vkPairA) 4).hom u)
      ((relCapPair vkPairX vkPairA 4 4 u) c) ≠ 0 :=
    kronH_ne_zero_of_ne_zero_vkPairX _ _ hxu hc
  -- replace `u` and `c` by representatives
  obtain ⟨a, ha, hua⟩ := exists_relClassOf ℤ vkPairX vkPairA 4 u
  obtain ⟨cc, hcc⟩ : ∃ cc : (relChains vkPairX vkPairA).cycles 8,
      (relChains vkPairX vkPairA).homologyπ 8 cc = c :=
    (ModuleCat.epi_iff_surjective ((relChains vkPairX vkPairA).homologyπ 8)).mp inferInstance c
  obtain ⟨zhat, hzhat⟩ : ∃ zhat : (singularChains ℤ vkPairX).X 8,
      (cokernel.π ((inclChains vkPairX vkPairA).f 8)).hom zhat
        = (relChains_cokernelIso vkPairX vkPairA 8).hom
            ((relChains vkPairX vkPairA).iCycles 8 cc) :=
    (ModuleCat.epi_iff_surjective (cokernel.π ((inclChains vkPairX vkPairA).f 8))).mp
      inferInstance _
  rw [← hua, ← hcc] at hne
  rw [kronH_relIncl_relCapPair vkPairX vkPairA a ha a ha cc zhat hzhat] at hne
  -- `relCup a a = δw` because `relCupH' u u = 0`
  have h0' : relClassOf ℤ vkPairX vkPairA (relCup ℤ vkPairX vkPairA 4 4 a a)
      (relDiffLM_relCup_of_cocycles ℤ vkPairX vkPairA a a ha ha) = 0 := by
    rw [← relCupH'_apply ℤ vkPairX vkPairA a a ha ha]
    rw [hua]
    exact h0
  obtain ⟨w, hw⟩ := exists_relDiff_of_relClassOf_eq_zero vkPairX vkPairA
    (relCup ℤ vkPairX vkPairA 4 4 a a)
    (relDiffLM_relCup_of_cocycles ℤ vkPairX vkPairA a a ha ha) h0'
  -- the right-hand side is zero
  have hzero : kronecker ℤ (TopCat.toSSet.obj vkPairX)
      (a.1 : Cochain ℤ (TopCat.toSSet.obj vkPairX) 4)
      ((cap ℤ (TopCat.toSSet.obj vkPairX) (a.1 : Cochain ℤ (TopCat.toSSet.obj vkPairX) 4) 4)
        zhat) = 0 := by
    rw [relKronecker_cap_cup ℤ vkPairX vkPairA a a zhat]
    exact relCup_eval_zhat_eq_zero vkPairX vkPairA a w zhat hw
      (proj_d_zhat_eq_zero vkPairX vkPairA cc zhat hzhat)
  exact hne hzero

end

end Work.Cohomology
