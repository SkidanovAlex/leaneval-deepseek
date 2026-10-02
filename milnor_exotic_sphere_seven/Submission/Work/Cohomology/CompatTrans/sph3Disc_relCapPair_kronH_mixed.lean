import Mathlib
import Submission.Work.Cohomology.sph3DiscMixedDefs
import Submission.Work.Cohomology.CompatTrans.diskPair_relCapPair_ne_zero
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.relCapH_kronH_cup
import Submission.Work.Cohomology.gradedComm
import Submission.Work.Cohomology.cupLeibniz
import Submission.Work.Cohomology.cup1Cast
import Submission.Work.Cohomology.relIncl_relCupH
import Submission.Work.Cohomology.relCupH
import Submission.Work.Cohomology.cupNatural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## Two elementary facts about relative cochains -/

/-- Elementwise naturality of a map of simplicial sets. -/
lemma app_map_naturality {X Y : SSet} (f : X ⟶ Y) {a b : ℕ} (φ : ⦋a⦌ ⟶ ⦋b⦌) (τ : X _⦋b⦌) :
    f.app (Opposite.op ⦋a⦌) (X.map φ.op τ) = Y.map φ.op (f.app (Opposite.op ⦋b⦌) τ) := by
  have h := f.naturality φ.op
  exact congrArg (fun (g : X.obj (Opposite.op ⦋b⦌) ⟶ Y.obj (Opposite.op ⦋a⦌)) => g τ) h

/-- `cup1` of a relative cochain is a relative cochain: the homotopy between `α ⌣ β` and
`β ⌣ α` vanishes on chains supported in `A` whenever `α` is relative. -/
lemma cup1_mem_relKern_left (R : Type) [CommRing R] (X : TopCat) (A : Set X) {n m : ℕ}
    {α : Cochain R (TopCat.toSSet.obj X) n} (hα : α ∈ relKern R X A n)
    (β : Cochain R (TopCat.toSSet.obj X) m) :
    cup1 R (TopCat.toSSet.obj X) n m α β ∈ relKern R X A (n + m - 1) := by
  rw [relKern, LinearMap.mem_ker, restr, dualChainMap_f_hom, chainMap_f_eq]
  apply genEval_ext (X := TopCat.toSSet.obj (TopCat.of A))
  intro τ
  have hz : genEval R (TopCat.toSSet.obj (TopCat.of A))
      (0 : Cochain R (TopCat.toSSet.obj (TopCat.of A)) (n + m - 1)) τ = 0 := by
    simp [genEval]
  erw [genEval_dualMap, genEval_cup1, hz]
  refine Finset.sum_eq_zero (fun s _ => ?_)
  have h0 : genEval R (TopCat.toSSet.obj X) α
      ((TopCat.toSSet.obj X).map (Fface n m s.val (by have := s.isLt; omega)).op
        ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n + m - 1⦌) τ)) = 0 := by
    rw [← app_map_naturality]
    exact genEval_eq_zero_of_mem_relKern R X A α hα _
  rw [h0, mul_zero, zero_mul]

/-- A relative cochain vanishes on a chain whose class in `C_*(X,A)` is zero. -/
lemma relKern_apply_eq_zero_of_relDualProj_eq_zero (X : TopCat) (A : Set X) {k : ℕ}
    (φ : relKern ℤ X A k) (z : (singularChains ℤ X).X k)
    (hz : relDualProj X A k z = 0) : relDualLM X k φ.1 z = 0 := by
  have hmem : z ∈ LinearMap.range ((inclChains X A).f k).hom := by
    rw [← relDualProj_ker X A k]
    exact LinearMap.mem_ker.mpr hz
  obtain ⟨y, hy⟩ := hmem
  rw [← hy]
  exact (relDualKern_iff X A k φ.1).1 φ.2 y

/-- **The mixed cap/cup identity on a relative cycle.**  For an absolute cocycle `β` of degree `3`,
a relative cocycle `α` of degree `4` and a chain `x` of degree `7` whose boundary is trivial in
relative homology, the Kronecker pairing of `β` with the cap product `x ⌢ α` equals the evaluation
of the mixed product `β ⌣ α` at `x`.  The two products `α ⌣ β` and `β ⌣ α` differ by a relative
coboundary (`cup1`), which vanishes on `x` because its boundary is trivial in `C_*(X,A)`. -/
lemma kronecker_cap_cup_comm (X : TopCat) (A : Set X)
    (β : Cochain ℤ (TopCat.toSSet.obj X) 3) (hβ : cochainDiff ℤ (TopCat.toSSet.obj X) β = 0)
    (α : relKern ℤ X A 4) (hα : relDiffLM ℤ X A 4 α = 0)
    (x : (singularChains ℤ X).X 7)
    (hx : relDualProj X A 6 (((singularChains ℤ X).d 7 6).hom x) = 0) :
    kronecker ℤ (TopCat.toSSet.obj X) β (cap ℤ (TopCat.toSSet.obj X) α.1 3 x)
      = kronecker ℤ (TopCat.toSSet.obj X) (cup ℤ (TopCat.toSSet.obj X) β α.1) x := by
  rw [kronecker_cap_cup]
  have hα' : cochainDiff ℤ (TopCat.toSSet.obj X) α.1 = 0 := relClassOf_cochainDiff ℤ X A α hα
  have hid := cup1Identity ℤ (TopCat.toSSet.obj X) 4 3 (by omega) (by omega) α.1 β hα' hβ
  have hcast1 : ((Nat.sub_add_cancel (by omega : 1 ≤ 4 + 3)) ▸
      (cochainDiff ℤ (TopCat.toSSet.obj X) (cup1 ℤ (TopCat.toSSet.obj X) 4 3 α.1 β) :
        Cochain ℤ (TopCat.toSSet.obj X) (4 + 3)))
      = cochainDiff ℤ (TopCat.toSSet.obj X) (cup1 ℤ (TopCat.toSSet.obj X) 4 3 α.1 β) := by
    rw [Subsingleton.elim (Nat.sub_add_cancel (by omega : 1 ≤ 4 + 3)) rfl]
  have hcast2 : (((Nat.add_comm 3 4 : 3 + 4 = 4 + 3)) ▸
      (cup ℤ (TopCat.toSSet.obj X) β α.1 : Cochain ℤ (TopCat.toSSet.obj X) (3 + 4)))
      = cup ℤ (TopCat.toSSet.obj X) β α.1 := by
    rw [Subsingleton.elim (Nat.add_comm 3 4 : 3 + 4 = 4 + 3) rfl]
  rw [hcast1, hcast2, show (-1:ℤ)^(4*3) = 1 from by norm_num, one_smul] at hid
  have hzero : kronecker ℤ (TopCat.toSSet.obj X)
      (cochainDiff ℤ (TopCat.toSSet.obj X) (cup1 ℤ (TopCat.toSSet.obj X) 4 3 α.1 β)) x = 0 := by
    show (cochainDiff ℤ (TopCat.toSSet.obj X)
      (cup1 ℤ (TopCat.toSSet.obj X) 4 3 α.1 β)) x = 0
    show (cup1 ℤ (TopCat.toSSet.obj X) 4 3 α.1 β)
      (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d 7 6 x) = 0
    exact relKern_apply_eq_zero_of_relDualProj_eq_zero X A
      ⟨cup1 ℤ (TopCat.toSSet.obj X) 4 3 α.1 β, cup1_mem_relKern_left ℤ X A α.2 β⟩ _ hx
  have h2 := congrArg (fun (γ : Cochain ℤ (TopCat.toSSet.obj X) (4+3)) =>
    kronecker ℤ (TopCat.toSSet.obj X) γ x) hid
  rw [hzero] at h2
  have h3 : ∀ (a b : Cochain ℤ (TopCat.toSSet.obj X) (4+3)),
      kronecker ℤ (TopCat.toSSet.obj X) (a - b) x
        = kronecker ℤ (TopCat.toSSet.obj X) a x
          - kronecker ℤ (TopCat.toSSet.obj X) b x := fun a b => rfl
  rw [h3] at h2
  linarith [h2]

/-! ## The main comparison -/

theorem sph3Disc_relCapPair_kronH_mixed (X : TopCat) (A : Set X)
    (e : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).homology 7 ≅
      ModuleCat.of ℤ (↥((Work.Cohomology.relChains X A).homology 7) →ₗ[ℤ] ℤ))
    (he : ∀ (z : ↥((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).cycles 7))
      (c : ↥((Work.Cohomology.relChains X A).cycles 7)),
      e.hom (((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).homologyπ 7) z)
          (((Work.Cohomology.relChains X A).homologyπ 7) c)
        = Work.Cohomology.dval (Work.Cohomology.relChains X A) 7
            (((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relChains X A)).iCycles 7) z)
            (((Work.Cohomology.relChains X A).iCycles 7) c))
    (b : Work.Cohomology.singularCohomology ℤ 3 X)
    (u : Work.Cohomology.relCohomology ℤ X A 4)
    (c : (Work.Cohomology.relChains X A).homology 7) :
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj X) 3 b
        (Work.Cohomology.relCapPair X A 4 3 u c)
      = e.hom ((HomologicalComplex.homologyMap (Work.Cohomology.relDualComplexIso X A).hom 7)
          (Work.Cohomology.mixedCup X A 3 4 b u)) c := by
  classical
  obtain ⟨β, hβ, rfl⟩ := exists_cohomologyClassOf ℤ (TopCat.toSSet.obj X) 3 b
  obtain ⟨α, hα, rfl⟩ := exists_relClassOf ℤ X A 4 u
  obtain ⟨cc, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((relChains X A).homologyπ 7)).mp inferInstance c
  -- a lift of the relative cycle to an absolute chain
  obtain ⟨xx, hxx⟩ : ∃ x : (singularChains ℤ X).X 7,
      relDualProj X A 7 x = ((relChains X A).iCycles 7) cc :=
    relDualProj_surjective X A 7 _
  have hstep : (relChains_cokernelIso X A 7).hom (((relChains X A).iCycles 7) cc)
      = (cokernel.π ((inclChains X A).f 7)).hom xx := by
    rw [← hxx]
    exact relChains_cokernelIso_canon_apply X A 7 xx
  -- the boundary of the lift is trivial in relative homology
  have hx : relDualProj X A 6 (((singularChains ℤ X).d 7 6).hom xx) = 0 := by
    have hcomm := LinearMap.congr_fun (relDualProj_comm_lm X A 6) xx
    simp only [LinearMap.comp_apply] at hcomm
    rw [← hcomm, hxx]
    have h := congrArg (fun (g : (relChains X A).cycles 7 ⟶ (relChains X A).X 6) => g.hom cc)
      (HomologicalComplex.iCycles_d (relChains X A) 7 6)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  -- the left hand side
  have hLHS : kronH ℤ (TopCat.toSSet.obj X) 3
        (cohomologyClassOf ℤ (TopCat.toSSet.obj X) β hβ)
        (relCapPair X A 4 3 (relClassOf ℤ X A α hα) (((relChains X A).homologyπ 7) cc))
      = kronecker ℤ (TopCat.toSSet.obj X) β (cap ℤ (TopCat.toSSet.obj X) α.1 3 xx) := by
    rw [show relClassOf ℤ X A α hα
        = ((relComplex ℤ X A).homologyπ 4) (relCocycleOf ℤ X A α hα) from rfl]
    rw [relCapPair_apply X A 4 3 (relCocycleOf ℤ X A α hα) cc]
    rw [kronH_apply_sing X β hβ (relCapPairZ X A 4 3 (relCocycleOf ℤ X A α hα) cc)]
    rw [relCapPairZ_iCycles X A 4 3 (relCocycleOf ℤ X A α hα) cc]
    rw [iCycles_relCocycleOf ℤ X A α hα]
    rw [hstep]
    rw [relCapHalf_apply_incl X A (m := 3) α xx]
    rfl
  -- the right hand side
  have hRHS : e.hom ((HomologicalComplex.homologyMap (relDualComplexIso X A).hom 7)
        (mixedCup X A 3 4 (cohomologyClassOf ℤ (TopCat.toSSet.obj X) β hβ)
          (relClassOf ℤ X A α hα))) (((relChains X A).homologyπ 7) cc)
      = kronecker ℤ (TopCat.toSSet.obj X) (cup ℤ (TopCat.toSSet.obj X) β α.1) xx := by
    obtain ⟨hmem, hmem2, hmixed⟩ := mixedCup_apply X A 3 4 β α hβ hα
    rw [hmixed]
    set z : (relComplex ℤ X A).cycles 7 :=
      relCocycleOf ℤ X A ⟨cup ℤ (TopCat.toSSet.obj X) β α.1, hmem⟩ hmem2 with hz
    have hcyc : ((dualComplex ℤ (relChains X A)).iCycles 7)
          ((HomologicalComplex.cyclesMap (relDualComplexIso X A).hom 7) z)
        = (relDualEquiv X A 7).symm (((relComplex ℤ X A).iCycles 7) z) := by
      have h := congrArg (fun (k : (relComplex ℤ X A).cycles 7 ⟶
          (dualComplex ℤ (relChains X A)).X 7) => (ModuleCat.Hom.hom k) z)
        (HomologicalComplex.cyclesMap_i (relDualComplexIso X A).hom 7)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      rw [h, relDualComplexIso_hom_f]
      exact relDualIso_inv_apply X A 7 (((relComplex ℤ X A).iCycles 7) z)
    have hnat2 : (ModuleCat.Hom.hom
          (HomologicalComplex.homologyMap (relDualComplexIso X A).hom 7))
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ X A) 7)) z)
        = (ModuleCat.Hom.hom
            (HomologicalComplex.homologyπ (dualComplex ℤ (relChains X A)) 7))
          ((HomologicalComplex.cyclesMap (relDualComplexIso X A).hom 7) z) := by
      have h := congrArg (fun (k : (relComplex ℤ X A).cycles 7 ⟶
          (dualComplex ℤ (relChains X A)).homology 7) => (ModuleCat.Hom.hom k) z)
        (HomologicalComplex.homologyπ_naturality (relDualComplexIso X A).hom 7)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    calc e.hom ((ModuleCat.Hom.hom
            (HomologicalComplex.homologyMap (relDualComplexIso X A).hom 7))
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ (relComplex ℤ X A) 7)) z))
          (((relChains X A).homologyπ 7) cc)
        = e.hom ((ModuleCat.Hom.hom
              (HomologicalComplex.homologyπ (dualComplex ℤ (relChains X A)) 7))
            ((HomologicalComplex.cyclesMap (relDualComplexIso X A).hom 7) z))
          (((relChains X A).homologyπ 7) cc) := by rw [hnat2]
      _ = dval (relChains X A) 7
            (((dualComplex ℤ (relChains X A)).iCycles 7)
              ((HomologicalComplex.cyclesMap (relDualComplexIso X A).hom 7) z))
            (((relChains X A).iCycles 7) cc) := he _ cc
      _ = dval (relChains X A) 7
            ((relDualEquiv X A 7).symm (((relComplex ℤ X A).iCycles 7) z))
            (((relChains X A).iCycles 7) cc) := by rw [hcyc]
      _ = dval (relChains X A) 7
            ((relDualEquiv X A 7).symm
              ⟨cup ℤ (TopCat.toSSet.obj X) β α.1, hmem⟩)
            (((relChains X A).iCycles 7) cc) := by rw [iCycles_relCocycleOf]
      _ = dval (relChains X A) 7
            ((relDualEquiv X A 7).symm
              ⟨cup ℤ (TopCat.toSSet.obj X) β α.1, hmem⟩)
            (relDualProj X A 7 xx) := by rw [← hxx]
      _ = relDualLM X 7 (cup ℤ (TopCat.toSSet.obj X) β α.1) xx := by
            have hE := LinearMap.congr_fun (relDualEquiv_symm_comp X A 7
              ⟨cup ℤ (TopCat.toSSet.obj X) β α.1, hmem⟩) xx
            rw [LinearMap.comp_apply] at hE
            exact hE
      _ = kronecker ℤ (TopCat.toSSet.obj X) (cup ℤ (TopCat.toSSet.obj X) β α.1) xx := rfl
  rw [hLHS, hRHS]
  exact kronecker_cap_cup_comm X A β hβ α hα xx hx

end

end Work.Cohomology
