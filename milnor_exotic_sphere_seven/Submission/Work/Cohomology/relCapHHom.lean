import Mathlib
import Submission.Work.Cohomology.RelCap
import Submission.Work.Cohomology.relCapH
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.RelCupTransfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cap product pairing on homology

This file descends the relative cap product `relCapHalf` / `relCapZ`
(`Submission/Work/Cohomology/RelCap.lean`, `Submission/Work/Cohomology/relCapH.lean`) to a pairing
on homology

  `H^n(X,A;ℤ) →ₗ (H_{n+m}(X,A;ℤ) →ₗ H_m(X;ℤ))`

compatible with the cycle-level pairing `relCapZ`.  The two descent steps are:

* (homological variable) a relative boundary is killed: the cap product of a relative cocycle
  with a chain supported on `A` vanishes;
* (cohomological variable) a relative coboundary is killed, by the boundary formula `cap_d`.

## Main results

* `relCapZHom_toCycles_homologyπ` — the homological descent condition;
* `relCoboundary_homologyπ` — the cohomological descent condition;
* `relCapHomH`, `relCapHfun`, `relCapHMap` — the descended pairing;
* `relCapHHom` — the relative cap product pairing on homology.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## Elementary API for singular chain complexes -/

/-- The inclusion of the cycles of a chain complex is injective. -/
lemma iCycles_injective_C (R : Type) [CommRing R] (C : ChainComplex (ModuleCat R) ℕ) (m : ℕ) :
    Function.Injective (C.iCycles m).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- `toCycles` followed by `iCycles` is the differential, elementwise. -/
lemma toCycles_i_C (R : Type) [CommRing R] (C : ChainComplex (ModuleCat R) ℕ) (i j : ℕ)
    (y : C.X i) :
    (C.iCycles j).hom ((C.toCycles i j).hom y) = (C.d i j).hom y := by
  have h := HomologicalComplex.toCycles_i C i j
  have h' := congrArg (fun (g : C.X i ⟶ C.X j) => g.hom y) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h'

/-- `toCycles` followed by `homologyπ` vanishes. -/
lemma homologyπ_toCycles_C (R : Type) [CommRing R] (C : ChainComplex (ModuleCat R) ℕ) (i j : ℕ)
    (y : C.X i) :
    (C.homologyπ j).hom ((C.toCycles i j).hom y) = 0 := by
  have h := HomologicalComplex.toCycles_comp_homologyπ C i j
  have h' := congrArg (fun (g : C.X i ⟶ C.homology j) => g.hom y) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h'

/-- A cycle whose underlying chain is a boundary has vanishing homology class. -/
lemma homologyπ_eq_zero_of_iCycles_eq_d (R : Type) [CommRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (m : ℕ)
    (w : C.cycles m) (y : C.X (m+1)) (h : (C.iCycles m).hom w = (C.d (m+1) m).hom y) :
    (C.homologyπ m).hom w = 0 := by
  have htw : C.toCycles (m+1) m y = w := by
    apply iCycles_injective_C R C m
    rw [toCycles_i_C, h]
  rw [← htw]
  exact homologyπ_toCycles_C R C (m+1) m y

/-- A cycle whose underlying chain is a scalar multiple of a boundary has vanishing homology
class. -/
lemma homologyπ_eq_zero_of_iCycles_eq_smul_d (R : Type) [CommRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (m : ℕ)
    (w : C.cycles m) (y : C.X (m+1)) (c : R)
    (h : (C.iCycles m).hom w = c • (C.d (m+1) m).hom y) :
    (C.homologyπ m).hom w = 0 := by
  apply homologyπ_eq_zero_of_iCycles_eq_d R C m w (c • y)
  rw [h]
  exact (LinearMap.map_smul (C.d (m+1) m).hom c y).symm

/-- Transporting an element across an index equality and back is the identity. -/
lemma eqRec_self_symm_nat {X : ℕ → Type*} {a b : ℕ} (h : a = b) (w : X b) :
    h ▸ (h.symm ▸ w) = w := by cases h; rfl

/-- The differential of a chain complex evaluated on a transported element. -/
lemma chain_d_eqRec (C : ChainComplex (ModuleCat ℤ) ℕ) {a b j : ℕ} (h : a = b)
    (y : C.X b) :
    (C.d a j).hom (h.symm ▸ y) = (C.d b j).hom y := by cases h; rfl

/-- The elementwise form of the commutativity of a chain map with the differential. -/
lemma chainMap_comm_apply (A B : ChainComplex (ModuleCat ℤ) ℕ) (f : A ⟶ B) (i j : ℕ)
    (x : A.X i) :
    ((B.d i j)).hom (((f.f i)).hom x) = ((f.f j)).hom (((A.d i j)).hom x) := by
  have h := congrArg (fun (g : A.X i ⟶ B.X j) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.Hom.comm f i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-! ## The boundary formula for the cap product -/

/-- **The boundary formula for the cap product with a cocycle**, in the form used for the descent:
the cap product of the coboundary `δβ` with a chain is, up to sign, the differential of the cap
product of `β`. -/
lemma cap_coboundary_formula (R : Type) [CommRing R] (X : SSet) {k m : ℕ} (β : Cochain R X k)
    (x : (X.chainComplex (ModuleCat.of R R)).X (k+(m+1))) :
    (cap R X (cochainDiff R X β) m) ((capIdx k m) ▸ x)
      = (cap R X β m) (((X.chainComplex (ModuleCat.of R R)).d (k+(m+1)) (k+m)).hom x)
        - (-1:R)^k • ((X.chainComplex (ModuleCat.of R R)).d (m+1) m).hom
            ((cap R X β (m+1)) x) := by
  have h := cap_d R X (n := k) (m := m) β x
  rw [h]
  rw [smul_smul, neg_one_pow_mul_self, one_smul]
  abel


/-- **The boundary formula for the cap product with a cocycle**: the cap product of a cocycle with
a boundary is a (signed) boundary. -/
lemma cap_d_apply_cocycle (R : Type) [CommRing R] (X : SSet) {n m : ℕ} (γ : Cochain R X n)
    (hγ : cochainDiff R X γ = 0) (B : (X.chainComplex (ModuleCat.of R R)).X (n+(m+1))) :
    (cap R X γ m) (((X.chainComplex (ModuleCat.of R R)).d (n+(m+1)) (n+m)).hom B)
      = (-1:R)^n • ((X.chainComplex (ModuleCat.of R R)).d (m+1) m).hom
        ((cap R X γ (m+1)) B) := by
  have h := cap_d R X (n := n) (m := m) γ B
  rw [hγ] at h
  simp only [cap_zero, LinearMap.zero_apply, sub_zero] at h
  rw [h]
  rw [smul_smul, neg_one_pow_mul_self, one_smul]

/-- A cycle whose underlying chain is a `(-1)^n` multiple of a boundary has vanishing class. -/
lemma homologyπ_eq_zero_of_iCycles_eq_negOnePow_smul_d (R : Type) [CommRing R]
    (C : ChainComplex (ModuleCat R) ℕ) (m n : ℕ)
    (w : C.cycles m) (y : C.X (m+1))
    (h : (C.iCycles m).hom w = (-1:R)^n • (C.d (m+1) m).hom y) :
    (C.homologyπ m).hom w = 0 := by
  apply homologyπ_eq_zero_of_iCycles_eq_d R C m w ((-1:R)^n • y)
  rw [h]
  exact (LinearMap.map_smul (C.d (m+1) m).hom ((-1:R)^n) y).symm

/-! ## The relative cap product on cycles, computed -/


/-- The relative cap product of a relative cocycle with a relative cycle, computed on any lift of
the relative cycle to an absolute chain. -/
lemma relCapZHom_iCycles_hom_apply (X : TopCat) (A : Set X) (n m : ℕ)
    (z : (relComplex ℤ X A).cycles n) (c : (relChains X A).cycles (n+m))
    (x : (singularChains ℤ X).X (n+m))
    (hx : (cokernel.π ((inclChains X A).f (n+m))).hom x
        = (relChains_cokernelIso X A (n+m)).hom ((relChains X A).iCycles (n+m) c)) :
    (singularChains ℤ X).iCycles m (relCapZHom X A n m z c)
      = (cap ℤ (TopCat.toSSet.obj X) (((relComplex ℤ X A).iCycles n).hom z).1 m) x := by
  have h2 := congrArg (fun (g : (relChains X A).cycles (n+m) ⟶ (singularChains ℤ X).X m) => g.hom c)
    (relCapZHom_iCycles X A n m z)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [h2]
  rw [← hx]
  exact relCapHalf_apply_incl X A (((relComplex ℤ X A).iCycles n).hom z) x

/-! ## The homological descent: relative boundaries are killed -/

/-- **The homological descent condition.**  The cap product of a relative cocycle with a relative
boundary has vanishing homology class. -/
lemma relCapZHom_toCycles_homologyπ (X : TopCat) (A : Set X) (n m : ℕ)
    (z : (relComplex ℤ X A).cycles n) (b : (relChains X A).X (n+m+1)) :
    (singularChains ℤ X).homologyπ m
      (relCapZHom X A n m z ((relChains X A).toCycles (n+m+1) (n+m) b)) = 0 := by
  obtain ⟨B, hB⟩ : ∃ B : (singularChains ℤ X).X (n+m+1),
      (cokernel.π ((inclChains X A).f (n+m+1))).hom B
        = (relChains_cokernelIso X A (n+m+1)).hom b :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance _
  have hPB : ((cokernel.π (inclChains X A)).f (n+m+1)).hom B = b := by
    refine (ModuleCat.mono_iff_injective ((relChains_cokernelIso X A (n+m+1)).hom)).mp inferInstance ?_
    rw [relChains_cokernelIso_canon_apply]
    exact hB
  have hdrel : (relChains X A).d (n+m+1) (n+m) b
      = ((cokernel.π (inclChains X A)).f (n+m)).hom
          (((singularChains ℤ X).d (n+m+1) (n+m)).hom B) := by
    rw [← hPB]
    exact chainMap_comm_apply _ _ (cokernel.π (inclChains X A)) (n+m+1) (n+m) B
  have htc : (relChains X A).iCycles (n+m) ((relChains X A).toCycles (n+m+1) (n+m) b)
      = (relChains X A).d (n+m+1) (n+m) b := toCycles_i_C ℤ (relChains X A) (n+m+1) (n+m) b
  have hx : (cokernel.π ((inclChains X A).f (n+m))).hom
        (((singularChains ℤ X).d (n+m+1) (n+m)).hom B)
      = (relChains_cokernelIso X A (n+m)).hom
          ((relChains X A).iCycles (n+m) ((relChains X A).toCycles (n+m+1) (n+m) b)) := by
    rw [htc, hdrel, relChains_cokernelIso_canon_apply]
  have hkey := relCapZHom_iCycles_hom_apply X A n m z ((relChains X A).toCycles (n+m+1) (n+m) b)
    (((singularChains ℤ X).d (n+m+1) (n+m)).hom B) hx
  have hcoc : cochainDiff ℤ (TopCat.toSSet.obj X) (((relComplex ℤ X A).iCycles n).hom z).1 = 0 :=
    relClassOf_cochainDiff ℤ X A (((relComplex ℤ X A).iCycles n).hom z) (relDiffLM_iCycles X A n z)
  have hbd := cap_d_apply_cocycle ℤ (TopCat.toSSet.obj X) (m := m)
    (((relComplex ℤ X A).iCycles n).hom z).1 hcoc B
  exact homologyπ_eq_zero_of_iCycles_eq_negOnePow_smul_d ℤ (singularChains ℤ X) m n _
    ((cap ℤ (TopCat.toSSet.obj X) (((relComplex ℤ X A).iCycles n).hom z).1 (m+1)) B)
    (hkey.trans hbd)

/-! ## The cohomological descent: relative coboundaries are killed -/

/-- The cycle of `C^*(X,A)` associated with a relative cochain is the relative differential. -/
lemma relComplex_toCycles_iCycles (X : TopCat) (A : Set X) (k : ℕ)
    (β : (relComplex ℤ X A).X k) :
    ((relComplex ℤ X A).iCycles (k+1)).hom ((relComplex ℤ X A).toCycles k (k+1) β)
      = relDiffLM ℤ X A k β := by
  have h := iCycles_toCycles_K (relComplex ℤ X A) k (k+1) β
  rw [relComplex_d] at h
  exact h

/-- The underlying absolute cochain of the relative differential is the coboundary. -/
lemma relDiffLM_coe_cochainDiff (X : TopCat) (A : Set X) (k : ℕ)
    (β : (relComplex ℤ X A).X k) :
    (relDiffLM ℤ X A k β).1 = cochainDiff ℤ (TopCat.toSSet.obj X) β.1 := by
  rw [relDiffLM_coe, singularCochain_d_apply]

/-- `0 - u • D = (-u) • D`. -/
lemma zero_sub_smul_eq_neg_smul (R : Type) [Ring R] {M : Type} [AddCommGroup M] [Module R M]
    (u : R) (D : M) : (0 : M) - u • D = (-u) • D := by
  rw [zero_sub, neg_smul]

/-- **The cohomological descent condition.**  The cap product of a relative coboundary of degree
`k+1` with a relative cycle has vanishing homology class. -/
lemma relCoboundary_homologyπ (X : TopCat) (A : Set X) (k m : ℕ)
    (β : relKern ℤ X A k) (c : (relChains X A).cycles ((k+1)+m)) :
    (singularChains ℤ X).homologyπ m
      (relCapZHom X A (k+1) m ((relComplex ℤ X A).toCycles k (k+1) β) c) = 0 := by
  set α₀ : Cochain ℤ (TopCat.toSSet.obj X) k := β.1 with hα₀
  set γ₀ : Cochain ℤ (TopCat.toSSet.obj X) (k+1) := (relDiffLM ℤ X A k β).1 with hγ₀
  obtain ⟨y, hy⟩ : ∃ y : (singularChains ℤ X).X ((k+1)+m),
      (cokernel.π ((inclChains X A).f ((k+1)+m))).hom y
        = (relChains_cokernelIso X A ((k+1)+m)).hom ((relChains X A).iCycles ((k+1)+m) c) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance _
  set x : (singularChains ℤ X).X (k+(m+1)) := (capIdx k m).symm ▸ y with hxdef
  have hcast : (capIdx k m) ▸ x = y := by
    rw [hxdef]
    exact eqRec_self_symm_nat (X := fun n => (singularChains ℤ X).X n) (capIdx k m) y
  have hdx : ((singularChains ℤ X).d (k+(m+1)) (k+m)).hom x
      = ((singularChains ℤ X).d ((k+1)+m) (k+m)).hom y := by
    rw [hxdef]; exact chain_d_eqRec (singularChains ℤ X) (capIdx k m) y
  have hcyc : ((relChains X A).d ((k+1)+m) (k+m)).hom
      ((relChains X A).iCycles ((k+1)+m) c) = 0 := by
    have h := congrArg
      (fun (g : (relChains X A).cycles ((k+1)+m) ⟶ (relChains X A).X (k+m)) => g.hom c)
      (HomologicalComplex.iCycles_d (relChains X A) ((k+1)+m) (k+m))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hPy : ((cokernel.π (inclChains X A)).f ((k+1)+m)).hom y
      = (relChains X A).iCycles ((k+1)+m) c := by
    refine (ModuleCat.mono_iff_injective ((relChains_cokernelIso X A ((k+1)+m)).hom)).mp inferInstance ?_
    rw [relChains_cokernelIso_canon_apply]
    exact hy
  have hPd : ((cokernel.π (inclChains X A)).f (k+m)).hom
      (((singularChains ℤ X).d ((k+1)+m) (k+m)).hom y) = 0 :=
    Eq.trans (chainMap_comm_apply _ _ (cokernel.π (inclChains X A)) ((k+1)+m) (k+m) y).symm
      (Eq.trans (congrArg (fun w => ((relChains X A).d ((k+1)+m) (k+m)) w) hPy) hcyc)
  have hcoker_dx : (cokernel.π ((inclChains X A).f (k+m))).hom
      (((singularChains ℤ X).d (k+(m+1)) (k+m)).hom x) = 0 := by
    rw [hdx, ← relChains_cokernelIso_canon_apply, hPd, map_zero]
  have hkill : (cap ℤ (TopCat.toSSet.obj X) α₀ m)
      (((singularChains ℤ X).d (k+(m+1)) (k+m)).hom x) = 0 := by
    have h1 := relCapHalf_apply_incl X A β (((singularChains ℤ X).d (k+(m+1)) (k+m)).hom x)
    rw [hcoker_dx, map_zero] at h1
    rw [hα₀]
    exact h1.symm
  have hf := cap_coboundary_formula ℤ (TopCat.toSSet.obj X) (k := k) (m := m) α₀ x
  have hcoch : cochainDiff ℤ (TopCat.toSSet.obj X) α₀ = γ₀ := by
    rw [hα₀, hγ₀, relDiffLM_coe_cochainDiff]
  have hstep1 : (cap ℤ (TopCat.toSSet.obj X) γ₀ m) y
      = (cap ℤ (TopCat.toSSet.obj X) γ₀ m) ((capIdx k m) ▸ x) :=
    (congrArg (fun w => (cap ℤ (TopCat.toSSet.obj X) γ₀ m) w) hcast).symm
  have hstep2 : (cap ℤ (TopCat.toSSet.obj X) γ₀ m) ((capIdx k m) ▸ x)
      = (cap ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) α₀) m)
          ((capIdx k m) ▸ x) :=
    (congrArg (fun γ => (cap ℤ (TopCat.toSSet.obj X) γ m) ((capIdx k m) ▸ x)) hcoch).symm
  have hstep3 := hkill ▸ hf
  have hstep4 := zero_sub_smul_eq_neg_smul ℤ ((-1:ℤ)^k)
    ((((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (m+1) m).hom
      ((cap ℤ (TopCat.toSSet.obj X) α₀ (m+1)) x))
  have hkey := relCapZHom_iCycles_hom_apply X A (k+1) m
    ((relComplex ℤ X A).toCycles k (k+1) β) c y hy
  have hχ : (((relComplex ℤ X A).iCycles (k+1)).hom ((relComplex ℤ X A).toCycles k (k+1) β)).1
      = γ₀ := by
    rw [hγ₀]
    exact congrArg Subtype.val (relComplex_toCycles_iCycles X A k β)
  exact homologyπ_eq_zero_of_iCycles_eq_smul_d ℤ (singularChains ℤ X) m _
    ((cap ℤ (TopCat.toSSet.obj X) α₀ (m+1)) x) (-((-1:ℤ)^k))
    ((hkey.trans (congrArg (fun γ => (cap ℤ (TopCat.toSSet.obj X) γ m) y) hχ)).trans
      (hstep1.trans (hstep2.trans (hstep3.trans hstep4))))

/-! ## The homological descent of the relative cap product -/

/-- `H_{n+m}(X,A)` is the cokernel of the boundary map out of the `(n+m+1)`-cycles. -/
noncomputable def homCoker_rel (X : TopCat) (A : Set X) (n m : ℕ) :
    IsColimit (CokernelCofork.ofπ ((relChains X A).homologyπ (n+m))
      (HomologicalComplex.toCycles_comp_homologyπ (relChains X A) (n+m+1) (n+m))) :=
  (relChains X A).homologyIsCokernel (n+m+1) (n+m) (prev_down (n+m))

/-- The cap product of a fixed relative cocycle with a relative boundary vanishes in homology. -/
lemma relCapZHom_factor (X : TopCat) (A : Set X) (n m : ℕ)
    (z : (relComplex ℤ X A).cycles n) :
    (relChains X A).toCycles (n+m+1) (n+m) ≫ relCapZHom X A n m z
      ≫ (singularChains ℤ X).homologyπ m = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  exact relCapZHom_toCycles_homologyπ X A n m z b

/-- **The cap product of a relative cocycle with a relative chain**, descended to `H_{n+m}(X,A)`. -/
noncomputable def relCapHomH (X : TopCat) (A : Set X) (n m : ℕ)
    (z : (relComplex ℤ X A).cycles n) :
    (relChains X A).homology (n+m) ⟶ (singularChains ℤ X).homology m :=
  (homCoker_rel X A n m).desc
    (CokernelCofork.ofπ (relCapZHom X A n m z ≫ (singularChains ℤ X).homologyπ m)
      (relCapZHom_factor X A n m z))

/-- The computation rule for `relCapHomH`. -/
lemma homologyπ_comp_relCapHomH (X : TopCat) (A : Set X) (n m : ℕ)
    (z : (relComplex ℤ X A).cycles n) :
    (relChains X A).homologyπ (n+m) ≫ relCapHomH X A n m z
      = relCapZHom X A n m z ≫ (singularChains ℤ X).homologyπ m :=
  Cofork.IsColimit.π_desc (homCoker_rel X A n m)

/-- `relCapHomH` is additive in the relative cocycle. -/
lemma relCapHomH_add (X : TopCat) (A : Set X) (n m : ℕ)
    (z z' : (relComplex ℤ X A).cycles n) :
    relCapHomH X A n m (z + z') = relCapHomH X A n m z + relCapHomH X A n m z' := by
  apply Cofork.IsColimit.hom_ext (homCoker_rel X A n m)
  show (relChains X A).homologyπ (n+m) ≫ relCapHomH X A n m (z + z')
      = (relChains X A).homologyπ (n+m) ≫ relCapHomH X A n m z
        + (relChains X A).homologyπ (n+m) ≫ relCapHomH X A n m z'
  rw [homologyπ_comp_relCapHomH, homologyπ_comp_relCapHomH, homologyπ_comp_relCapHomH,
    relCapZHom_add, Preadditive.add_comp]

/-- `relCapHomH` is homogeneous in the relative cocycle. -/
lemma relCapHomH_smul (X : TopCat) (A : Set X) (n m : ℕ)
    (r : ℤ) (z : (relComplex ℤ X A).cycles n) :
    relCapHomH X A n m (r • z) = r • relCapHomH X A n m z := by
  apply Cofork.IsColimit.hom_ext (homCoker_rel X A n m)
  show (relChains X A).homologyπ (n+m) ≫ relCapHomH X A n m (r • z)
      = r • ((relChains X A).homologyπ (n+m) ≫ relCapHomH X A n m z)
  rw [homologyπ_comp_relCapHomH, homologyπ_comp_relCapHomH, relCapZHom_smul,
    CategoryTheory.Linear.smul_comp]

/-- `relCapHomH` vanishes on the zero relative cocycle. -/
lemma relCapHomH_zero (X : TopCat) (A : Set X) (n m : ℕ) :
    relCapHomH X A n m (0 : (relComplex ℤ X A).cycles n) = 0 := by
  apply Cofork.IsColimit.hom_ext (homCoker_rel X A n m)
  show (relChains X A).homologyπ (n+m) ≫ relCapHomH X A n m 0
      = (relChains X A).homologyπ (n+m) ≫ 0
  rw [homologyπ_comp_relCapHomH, comp_zero, relCapZHom_zero, zero_comp]

/-- The additive structure of `relCapHomH` in the relative cocycle. -/
noncomputable def relCapHfunAdd (X : TopCat) (A : Set X) (n m : ℕ) :
    ↥((relComplex ℤ X A).cycles n) →+
      (((relChains X A).homology (n+m)) →ₗ[ℤ] ((singularChains ℤ X).homology m)) where
  toFun z := (relCapHomH X A n m z).hom
  map_zero' := by rw [relCapHomH_zero, ModuleCat.hom_zero]
  map_add' z z' := by rw [← ModuleCat.hom_add, relCapHomH_add]

/-- **The cap product with a relative cocycle**, as a linear map into `H_{n+m}(X,A) → H_m(X)`. -/
noncomputable def relCapHfun (X : TopCat) (A : Set X) (n m : ℕ) :
    ((relComplex ℤ X A).cycles n) →ₗ[ℤ]
      (((relChains X A).homology (n+m)) →ₗ[ℤ] ((singularChains ℤ X).homology m)) where
  toFun z := (relCapHomH X A n m z).hom
  map_add' z z' := by rw [← ModuleCat.hom_add, relCapHomH_add]
  map_smul' r z := by
    rw [RingHom.id_apply]
    have h := AddMonoidHom.map_zsmul (relCapHfunAdd X A n m) r z
    convert h using 1
    · dsimp only [relCapHfunAdd]
      exact congrArg (fun w => (relCapHomH X A n m w).hom)
        (int_smul_eq_zsmul (inferInstance : Module ℤ ↥((relComplex ℤ X A).cycles n)) r z)
    · dsimp only [relCapHfunAdd]
      rfl

/-! ## The cohomological descent of the relative cap product -/

/-- The composite of the boundary map on relative cycles with `relCapHfun` vanishes. -/
lemma relCapHfun_desc (X : TopCat) (A : Set X) (n m : ℕ) :
    (relComplex ℤ X A).toCycles ((ComplexShape.up ℕ).prev n) n
      ≫ ModuleCat.ofHom (relCapHfun X A n m) = 0 := by
  rcases n with _ | k
  · have hp : (ComplexShape.up ℕ).prev 0 = 0 :=
      ComplexShape.prev_eq_self' (ComplexShape.up ℕ) 0 (by intro j hj; have hj' : j + 1 = 0 := hj; omega)
    have h0 : (relComplex ℤ X A).toCycles 0 0 = 0 := by
      apply (cancel_mono ((relComplex ℤ X A).iCycles 0)).mp
      rw [HomologicalComplex.toCycles_i, zero_comp]
      exact HomologicalComplex.shape (relComplex ℤ X A) 0 0 (by
        intro h; have h' : 0 + 1 = 0 := h; omega)
    rw [hp, h0, zero_comp]
  · have hp : (ComplexShape.up ℕ).prev (k+1) = k :=
      ComplexShape.prev_eq' (ComplexShape.up ℕ) (i := k+1) (j := k) rfl
    rw [hp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro β
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      ModuleCat.hom_zero, LinearMap.zero_apply]
    apply LinearMap.ext
    intro y
    obtain ⟨c, rfl⟩ :=
      (ModuleCat.epi_iff_surjective ((relChains X A).homologyπ (k+1+m))).mp inferInstance y
    have h := congrArg
      (fun (g : (relChains X A).cycles (k+1+m) ⟶ (singularChains ℤ X).homology m) =>
        (ModuleCat.Hom.hom g) c)
      (homologyπ_comp_relCapHomH X A (k+1) m ((relComplex ℤ X A).toCycles k (k+1) β))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h.trans (relCoboundary_homologyπ X A k m β c)

/-- `H^n(X,A)` is the cokernel of the boundary map out of the `(n-1)`-cocycles. -/
noncomputable def relCohomCoker (X : TopCat) (A : Set X) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ ((relComplex ℤ X A).homologyπ n)
      (HomologicalComplex.toCycles_comp_homologyπ (relComplex ℤ X A)
        ((ComplexShape.up ℕ).prev n) n)) :=
  (relComplex ℤ X A).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl

/-- **The relative cap product pairing** `H^n(X,A) →ₗ (H_{n+m}(X,A) →ₗ H_m(X))`. -/
noncomputable def relCapHMap (X : TopCat) (A : Set X) (n m : ℕ) :
    (relComplex ℤ X A).homology n ⟶
      ModuleCat.of ℤ ((relChains X A).homology (n+m) →ₗ[ℤ]
        (singularChains ℤ X).homology m) :=
  (relCohomCoker X A n).desc
    (CokernelCofork.ofπ (ModuleCat.ofHom (relCapHfun X A n m)) (relCapHfun_desc X A n m))

/-- The computation rule for `relCapHMap`. -/
lemma homologyπ_relCapHMap (X : TopCat) (A : Set X) (n m : ℕ) :
    (relComplex ℤ X A).homologyπ n ≫ relCapHMap X A n m
      = ModuleCat.ofHom (relCapHfun X A n m) :=
  Cofork.IsColimit.π_desc (relCohomCoker X A n)

/-- The computation rule for the cycle-level relative cap product. -/
lemma relCapZ_iCycles (X : TopCat) (A : Set X) (n m : ℕ)
    (z : (relComplex ℤ X A).cycles n) (c : (relChains X A).cycles (n+m)) :
    (singularChains ℤ X).iCycles m (relCapZ X A n m z c)
      = relCapHalf ℤ X A (((relComplex ℤ X A).iCycles n).hom z) m
          ((relChains_cokernelIso X A (n+m)).hom ((relChains X A).iCycles (n+m) c)) := by
  have h := congrArg
    (fun (g : (relChains X A).cycles (n+m) ⟶ (singularChains ℤ X).X m) => g.hom c)
    (relCapZHom_iCycles X A n m z)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- **The relative cap product pairing on homology** `H^n(X,A) × H_{n+m}(X,A) → H_m(X)`, together
with the cycle-level computation rule. -/
theorem relCapHHom (X : TopCat) (A : Set X) (n m : ℕ) :
    ∃ (capZ : (Work.Cohomology.relComplex ℤ X A).cycles n →ₗ[ℤ]
          ((Work.Cohomology.relChains X A).cycles (n + m) →ₗ[ℤ]
            (Work.Cohomology.singularChains ℤ X).cycles m))
      (capH : Work.Cohomology.relCohomology ℤ X A n →ₗ[ℤ]
          ((Work.Cohomology.relChains X A).homology (n + m) →ₗ[ℤ]
            (Work.Cohomology.singularChains ℤ X).homology m)),
      (∀ (z : (Work.Cohomology.relComplex ℤ X A).cycles n)
         (c : (Work.Cohomology.relChains X A).cycles (n + m)),
         (Work.Cohomology.singularChains ℤ X).iCycles m (capZ z c) =
           Work.Cohomology.relCapHalf ℤ X A
             (((Work.Cohomology.relComplex ℤ X A).iCycles n).hom z) m
             ((Work.Cohomology.relChains_cokernelIso X A (n + m)).hom
               ((Work.Cohomology.relChains X A).iCycles (n + m) c)))
      ∧ (∀ (z : (Work.Cohomology.relComplex ℤ X A).cycles n)
           (c : (Work.Cohomology.relChains X A).cycles (n + m)),
           capH (((Work.Cohomology.relComplex ℤ X A).homologyπ n).hom z)
               (((Work.Cohomology.relChains X A).homologyπ (n + m)).hom c) =
             ((Work.Cohomology.singularChains ℤ X).homologyπ m).hom (capZ z c)) := by
  refine ⟨relCapZ X A n m, (relCapHMap X A n m).hom, ?_, ?_⟩
  · intro z c
    exact relCapZ_iCycles X A n m z c
  · intro z c
    have h1 : (relCapHMap X A n m).hom (((relComplex ℤ X A).homologyπ n).hom z)
        = relCapHfun X A n m z := by
      have h := congrArg
        (fun (g : (relComplex ℤ X A).cycles n ⟶ ModuleCat.of ℤ
            ((relChains X A).homology (n+m) →ₗ[ℤ] (singularChains ℤ X).homology m)) => g.hom z)
        (homologyπ_relCapHMap X A n m)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] using h
    rw [h1]
    have h := congrArg
      (fun (g : (relChains X A).cycles (n+m) ⟶ (singularChains ℤ X).homology m) =>
        (ModuleCat.Hom.hom g) c)
      (homologyπ_comp_relCapHomH X A n m z)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h

end

end Work.Cohomology
