import Mathlib
import Submission.Work.Gen.CruxDefs
import Submission.Work.Gen.PsiDataDefs
import Submission.Work.Gen.CohMap_fibreIncl_lhMap
import Submission.Work.LerayHirsch.FibreBasis
import Submission.Work.Cohomology.exists_smul_oneH
import Submission.Work.LerayHirsch.FibreZetaPow
import Submission.Work.LerayHirsch.FibreBasisOdd
import Submission.Work.Kunneth.PointMain
import Submission.Work.Kunneth.Bridge
import Submission.Work.Projective.pathConnectedSpace_CP
import Submission.Work.Gen.crx.Core
import Submission.Work.Whitney.ChernRelDefs
import Submission.Work.Kunneth.PointTopValue
import Submission.Work.Gen.eSymClass
import Submission.Work.Whitney.cupChern_one_right
import Submission.Work.LerayHirsch.whitneySumFormulaOfLerayHirsch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Gen

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-!
# The value of the top Leray–Hirsch coefficient of `ψ`

This module proves `Work.Gen.psiTopCoeff_value`, the fibre computation of the `ψ`-analysis
(`Submission/Work/Gen/NOTES_psi_delta.md` §2): the top coefficient of the Leray–Hirsch expansion of
`ψ` is the universal constant `Work.Gen.modelK n`.

The proof restricts the `ψ`-existence equation `(A)` (`hA`) to the fibre `ProjFibre W b` of
`P(W) → B`:

* the term `π^*x` vanishes (`x` has positive degree, `Work.Gen.CohMap_constFibre_eq_zero`);
* the term `ζ ⌣ ψ` becomes `(i_b^*ζ) ⌣ (i_b^*ψ)`, and `i_b^*ψ` is, by
  `Work.Gen.CohMap_fibreIncl_lhMap`, the top Leray–Hirsch summand
  `(const_b)^*ψ_{n-1} ⌣ (fibreIdent)^*(ζ^{n-1})`;
* the hypothesis `hQ` computes `i_b^*c_n(Q) = modelK n · i_b^*(ζ^n)`.

Since `(fibreIdent)^*(ζ^n) = (fibreIdent)^*(ζ) ⌣ (fibreIdent)^*(ζ^{n-1})`, the equation
therefore reads `(modelK n · 1) ⌣ w = ((const_b)^*ψ_{n-1}) ⌣ w` on the fibre, with
`w = i_b^*(ζ^n)`.  Pushing the whole equation forward to the model space `P(ε^{n+1})` along the
homeomorphism `fibreIdent` (so that `w` becomes `ζ^n`) and using that `i_b^*ψ_{n-1}` is a
*degree-`0`* class of a path-connected space — hence a multiple `k · 1`
(`Work.Cohomology.exists_smul_oneH`) — reduces it to `(modelK n) · ζ^n = k · ζ^n`, i.e. to
`Work.Kunneth.smul_zetaPow_injective`.  Pulling the resulting identity
`(fibreIdent)^*(ψ_{n-1}) = modelK n · 1` back along `fibreIdent` (`Work.Thom.CohMap_oneH`) gives
the claim.
-/

/-- The model projectivisation `P(ε^{m+2}) = ℂP^{m+1}` in which the fibre of `P(W) → B` for a rank
`m + 2` bundle `W` lives. -/
abbrev psiModel (m : ℕ) := Work.LerayHirsch.ProjSpace (Work.LerayHirsch.trivCore (m + 1 + 1))

/-- `Work.Gen.fibreIdent` is the explicit composite `projUniv ∘ projClassFibre`. -/
theorem psi_fibreIdent_eq {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    (Work.LerayHirsch.projUniv m).comp (Work.LerayHirsch.projClassFibre Z b)
      = Work.Gen.fibreIdent Z b := rfl

/-- **The two round trips of a homeomorphism on cohomology.**  For a homeomorphism `e : X ≃ₜ Y` the
pullback along `e` followed by the pullback along `e.symm` is the identity on the cohomology of
`Y`. -/
theorem psi_CohMap_homeo_symm_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (d : ℕ) (y : Work.Thom.Coh ℤ d Y) :
    (Work.Thom.CohMap (↑e.symm : C(Y, X)) ℤ d).hom
      ((Work.Thom.CohMap (↑e : C(X, Y)) ℤ d).hom y) = y := by
  rw [Work.Thom.CohMap_comp_apply (↑e.symm : C(Y, X)) (↑e : C(X, Y)) ℤ d y]
  have h : (↑e : C(X, Y)).comp (↑e.symm : C(Y, X)) = ContinuousMap.id Y :=
    ContinuousMap.ext (fun y => e.apply_symm_apply y)
  rw [h, Work.Thom.CohMap_id]
  rfl

/-- **The two round trips of a homeomorphism on cohomology** (the other order). -/
theorem psi_CohMap_comp_homeo_symm {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (d : ℕ) (x : Work.Thom.Coh ℤ d X) :
    (Work.Thom.CohMap (↑e : C(X, Y)) ℤ d).hom
      ((Work.Thom.CohMap (↑e.symm : C(Y, X)) ℤ d).hom x) = x := by
  rw [Work.Thom.CohMap_comp_apply (↑e : C(X, Y)) (↑e.symm : C(Y, X)) ℤ d x]
  have h : (↑e.symm : C(Y, X)).comp (↑e : C(X, Y)) = ContinuousMap.id X :=
    ContinuousMap.ext (fun x => e.symm_apply_apply x)
  rw [h, Work.Thom.CohMap_id]
  rfl

/-- **Pushing a pullback inside a degree cast and a graded product**: the pullback along `g` of
`cohTransport hd (cupChern 1 m A (cohTransport h0 (cupChern 0 m v zZ)))`.  The degrees are written
in the normalised form (`2 * (1 + m)`, `2 * m`, `2 * 0`) in which the naturality lemmas
`Work.Thom.cohTransport_CohMap` and `Work.Whitney.cupChern_CohMap` apply syntactically. -/
theorem psi_CohMap_cohTransport_cupChern {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    {m : ℕ} (g : C(F, E))
    (hd : 2 * (1 + m) = 2 * (m + 1)) (h0 : 2 * (0 + m) = 2 * m)
    (A : Work.Thom.Coh ℤ 2 E) (v : Work.Thom.Coh ℤ (2 * 0) E) (zZ : Work.Thom.Coh ℤ (2 * m) E) :
    (Work.Thom.CohMap g ℤ (2 * (m + 1))).hom
        (Work.Thom.cohTransport hd
          (Work.Whitney.cupChern 1 m A (Work.Thom.cohTransport h0 (Work.Whitney.cupChern 0 m v zZ))))
      = Work.Thom.cohTransport hd
          (Work.Whitney.cupChern 1 m ((Work.Thom.CohMap g ℤ 2).hom A)
            (Work.Thom.cohTransport h0
              (Work.Whitney.cupChern 0 m ((Work.Thom.CohMap g ℤ (2 * 0)).hom v)
                ((Work.Thom.CohMap g ℤ (2 * m)).hom zZ)))) := by
  rw [Work.Thom.cohTransport_CohMap, Work.Whitney.cupChern_CohMap,
    Work.Thom.cohTransport_CohMap, Work.Whitney.cupChern_CohMap]

/-- **Pushing a pullback inside a scalar multiple of a graded product with the hyperplane class.** -/
theorem psi_CohMap_zsmul_cupChern {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    {m : ℕ} (g : C(F, E)) (k : ℤ)
    (zZ : Work.Thom.Coh ℤ (2 * m) E) (A : Work.Thom.Coh ℤ 2 E) :
    (Work.Thom.CohMap g ℤ (2 * (m + 1))).hom (k • Work.Whitney.cupChern m 1 zZ A)
      = k • Work.Whitney.cupChern m 1 ((Work.Thom.CohMap g ℤ (2 * m)).hom zZ)
          ((Work.Thom.CohMap g ℤ 2).hom A) := by
  rw [Work.Thom.CohMap_zsmul, Work.Whitney.cupChern_CohMap]

open Work.TangentClasses Work.Thom in
/-- **The value at every point of the top Leray–Hirsch coefficient of `ψ` is the universal
constant `modelK n`.**  Restricting `(A)` (`hA`) to the fibre of `P(W) → B` over `b` gives
`i_b^*c_n(Q) = (const_b)^*(x) + (i_b^*ζ) ⌣ (i_b^*ψ)`, where the first term vanishes because `x` has
positive degree (`Work.Kunneth.subsingleton_coh_point_of_pos`), `i_b^*ψ` is
`(const_b)^*ψ_{n-1} ⌣ (fibreIdent)^*(ζ^{n-1})` (`Work.Gen.CohMap_fibreIncl_lhMap`), and
`i_b^*c_n(Q) = modelK n · i_b^*(ζ^n)` is the hypothesis `hQ` (the fibre model computation).  Since
`(fibreIdent)^*(ζ^n)` is the top power of the hyperplane class and `(const_b)^*ψ_{n-1}` has degree
`0`, the equality `(const_b)^*ψ_{n-1} ⌣ i_b^*(ζ^n) = (modelK n · 1) ⌣ i_b^*(ζ^n)` forces
`(const_b)^*ψ_{n-1} = modelK n · 1`: apply the inverse of the homeomorphism `fibreIdent` (injective
on cohomology), reduce a degree-`0` class on `P(ε^{n+1})` to a multiple of `1`
(`Work.Cohomology.exists_smul_oneH`, or `Work.Kunneth.exists_smul_oneHtop`), and cancel `ζ^n`
(`Work.Kunneth.smul_zetaPow_injective`). -/
theorem psiTopCoeff_value {n : ℕ} (hn : 1 ≤ n)
    {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι : Type} [Fintype ι]
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    (Q : VectorBundleCore ℂ (Work.LerayHirsch.ProjSpace W) (EuclideanSpace ℂ (Fin n))
          (ι × Fin (n + 1)))
    (ψ : Work.Thom.Coh ℤ (2 * (n - 1)) (Work.LerayHirsch.ProjSpace W))
    (x : Work.Thom.Coh ℤ (2 * n) B)
    (ψf : (j : {j : Fin (n + 1) // (j : ℕ) ≤ n - 1}) → Work.Thom.Coh ℤ (2 * ((n - 1) - (j : ℕ))) B)
    (hψ : Work.LerayHirsch.lhMap W (n - 1) ψf = ψ)
    (hA : Work.Thom.chernClass n n Q
        = (Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ (2 * n)).hom x
        + Work.Thom.cohTransport (Work.Gen.psiDataDegree n hn)
            (Work.Whitney.cupChern 1 (n - 1) (Work.LerayHirsch.zeta W) ψ))
    (hQ : ∀ b : B, (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl W b) ℤ (2 * n)).hom
        (Work.Thom.chernClass n n Q)
        = Work.Gen.modelK n • (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl W b) ℤ (2 * n)).hom
            (Work.LerayHirsch.zetaPow W n)) :
    ∀ b : B, (Work.Thom.CohMap (Work.Gen.constFibre W b) ℤ 0).hom
        (Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree (n := n)) (ψf Work.Gen.topCoeffIdx))
      = Work.Gen.modelK n • Work.Cohomology.oneH ℤ
          (Work.Whitney.ssB (Work.LerayHirsch.ProjFibre W b)) := by
  intro b
  -- write `n = m + 1`, so that `n - 1 = m` reduces definitionally
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- the value of the top coefficient at `b`
  set v : Work.Thom.Coh ℤ 0 (Work.LerayHirsch.ProjFibre W b) :=
    (Work.Thom.CohMap (Work.Gen.constFibre W b) ℤ 0).hom
      (Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree (n := m+1)) (ψf Work.Gen.topCoeffIdx)) with hv
  -- the fibre's hyperplane class powers
  set zZ : Work.Thom.Coh ℤ (2 * m) (Work.LerayHirsch.ProjFibre W b) :=
    (Work.Thom.CohMap (Work.Gen.fibreIdent W b) ℤ (2 * m)).hom
      (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (m + 1 + 1)) m) with hzZ
  -- the restriction of `ψ` to the fibre: only its top Leray–Hirsch summand survives
  have hpsi : (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl W b) ℤ (2 * m)).hom ψ
      = Work.Thom.cohTransport (by omega : 2 * (0 + m) = 2 * m)
          (Work.Whitney.cupChern 0 m v zZ) := by
    have h := Work.Gen.CohMap_fibreIncl_lhMap (n := m + 1) (by omega) W ψf b
    rw [hψ] at h
    exact h
  -- the restriction of `ζ`
  set A : Work.Thom.Coh ℤ 2 (Work.LerayHirsch.ProjFibre W b) :=
    (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl W b) ℤ 2).hom (Work.LerayHirsch.zeta W) with hAdef
  -- the `π^*x` term vanishes on the fibre
  have hzero : (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl W b) ℤ (2 * (m + 1))).hom
      ((Work.Thom.CohMap (Work.LerayHirsch.projMap W) ℤ (2 * (m + 1))).hom x) = 0 := by
    rw [Work.Thom.CohMap_comp_apply (Work.LerayHirsch.fibreIncl W b) (Work.LerayHirsch.projMap W)
      ℤ (2 * (m + 1)) x]
    have hmap : (Work.LerayHirsch.projMap W).comp (Work.LerayHirsch.fibreIncl W b)
        = Work.Gen.constFibre W b :=
      ContinuousMap.ext (fun y => Work.LerayHirsch.projMap_fibreIncl W b y)
    rw [hmap]
    exact Work.Gen.CohMap_constFibre_eq_zero W b (by omega : 1 ≤ 2 * (m + 1)) x
  -- **(A) restricted to the fibre**
  have hres : (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl W b) ℤ (2 * (m + 1))).hom
        (Work.Thom.chernClass (m + 1) (m + 1) Q)
      = Work.Thom.cohTransport (Work.Gen.psiDataDegree (m + 1) hn)
          (Work.Whitney.cupChern 1 m A (Work.Thom.cohTransport (by omega : 2 * (0 + m) = 2 * m)
            (Work.Whitney.cupChern 0 m v zZ))) := by
    rw [hA, Work.Thom.CohMap_add, hzero, zero_add, Work.Thom.cohTransport_CohMap,
      Work.Whitney.cupChern_CohMap, ← hAdef, ← hpsi]
    rfl
  -- `i_b^*ζ = (fibreIdent)^*ζ`
  have hAz : (Work.Thom.CohMap (Work.Gen.fibreIdent W b) ℤ 2).hom
      (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore (m + 1 + 1))) = A :=
    (Work.LerayHirsch.CohMap_comp_fibreIncl_zeta W b).trans hAdef.symm
  -- `i_b^*(ζ^{m+1}) = (fibreIdent)^*(ζ^m) ⌣ ζ`
  have hw : (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl W b) ℤ (2 * (m + 1))).hom
      (Work.LerayHirsch.zetaPow W (m + 1)) = Work.Whitney.cupChern m 1 zZ A := by
    rw [Work.LerayHirsch.CohMap_fibreIncl_zetaPow W b (m + 1), Work.LerayHirsch.zetaPow_succ,
      Work.Whitney.cupChern_CohMap, psi_fibreIdent_eq W b, ← hzZ, hAz]
  -- the equation on the fibre: `(modelK (m+1)) • w = A ⌣ (v ⌣ zZ)`
  have hEqF : Work.Gen.modelK (m + 1) • Work.Whitney.cupChern m 1 zZ A
      = Work.Thom.cohTransport (Work.Gen.psiDataDegree (m + 1) hn)
          (Work.Whitney.cupChern 1 m A (Work.Thom.cohTransport (by omega : 2 * (0 + m) = 2 * m)
            (Work.Whitney.cupChern 0 m v zZ))) := by
    rw [← hw]
    rw [← hres, hQ b]
  -- the homeomorphism of the fibre with the model space
  set eidH := (Work.LerayHirsch.fibreHomeo W b).trans (Work.LerayHirsch.projUnivHomeo (m + 1 + 1)) with heidH
  have hcoeEid : (↑eidH : C(Work.LerayHirsch.ProjFibre W b, psiModel m)) = Work.Gen.fibreIdent W b :=
    ContinuousMap.ext (fun t => rfl)
  -- the model space is path connected
  haveI hpcCP : PathConnectedSpace (Work.Projective.CP (m + 1)) :=
    Work.Projective.pathConnectedSpace_CP (m + 1)
  haveI hpcE : PathConnectedSpace (psiModel m) :=
    Work.Cohomology.pathConnectedSpace_of_homeomorph'
      (((Work.LerayHirsch.projUnivHomeo (m + 1 + 1)).symm).trans (Work.Kunneth.wkHomeo (m + 1)))
  -- the push-forward of `v` to the model space
  set U : Work.Thom.Coh ℤ 0 (psiModel m) :=
    (Work.Thom.CohMap (↑eidH.symm : C(psiModel m, Work.LerayHirsch.ProjFibre W b)) ℤ 0).hom v with hUdef
  obtain ⟨k, hk⟩ := Work.Cohomology.exists_smul_oneH (TopCat.of (psiModel m)) U
  have hPsiZZ : (Work.Thom.CohMap (↑eidH.symm : C(psiModel m, Work.LerayHirsch.ProjFibre W b)) ℤ (2*m)).hom zZ
      = Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (m+1+1)) m := by
    rw [hzZ, ← hcoeEid]
    exact psi_CohMap_homeo_symm_comp eidH (2*m) _
  have hPsiA : (Work.Thom.CohMap (↑eidH.symm : C(psiModel m, Work.LerayHirsch.ProjFibre W b)) ℤ 2).hom A
      = Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore (m+1+1)) := by
    rw [← hAz, ← hcoeEid]
    exact psi_CohMap_homeo_symm_comp eidH 2 _
  -- the top product of the model hyperplane class
  have hζζ : Work.Thom.cohTransport (Work.Gen.psiDataDegree (m + 1) hn)
      (Work.Whitney.cupChern 1 m (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore (m+1+1)))
        (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (m+1+1)) m))
      = Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (m+1+1)) (m + 1) := by
    rw [Work.LerayHirsch.zetaPow_succ (Work.LerayHirsch.trivCore (m+1+1)) m]
    rw [Work.Whitney.ChernRel.cupChern_comm m 1
      (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (m+1+1)) m)
      (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore (m+1+1)))]
  -- pushing `(★)` forward to the model space
  have h7 : Work.Gen.modelK (m + 1) • Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (m+1+1)) (m + 1)
      = Work.Thom.cohTransport (Work.Gen.psiDataDegree (m + 1) hn)
          (Work.Whitney.cupChern 1 m (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore (m+1+1)))
            (Work.Thom.cohTransport (by omega : 2 * (0 + m) = 2 * m)
              (Work.Whitney.cupChern 0 m U (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (m+1+1)) m)))) := by
    have h := congrArg (fun z => (Work.Thom.CohMap
      (↑eidH.symm : C(psiModel m, Work.LerayHirsch.ProjFibre W b)) ℤ (2 * (m + 1))).hom z) hEqF
    have hL : (Work.Thom.CohMap (↑eidH.symm : C(psiModel m, Work.LerayHirsch.ProjFibre W b)) ℤ (2 * (m + 1))).hom
          (Work.Gen.modelK (m + 1) • Work.Whitney.cupChern m 1 zZ A)
        = Work.Gen.modelK (m + 1) •
            Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (m+1+1)) (m + 1) := by
      rw [psi_CohMap_zsmul_cupChern, hPsiZZ, hPsiA,
        ← Work.LerayHirsch.zetaPow_succ (Work.LerayHirsch.trivCore (m+1+1)) m]
    have hR : (Work.Thom.CohMap (↑eidH.symm : C(psiModel m, Work.LerayHirsch.ProjFibre W b)) ℤ (2 * (m + 1))).hom
          (Work.Thom.cohTransport (Work.Gen.psiDataDegree (m + 1) hn)
            (Work.Whitney.cupChern 1 m A (Work.Thom.cohTransport (by omega : 2 * (0 + m) = 2 * m)
              (Work.Whitney.cupChern 0 m v zZ))))
        = Work.Thom.cohTransport (Work.Gen.psiDataDegree (m + 1) hn)
            (Work.Whitney.cupChern 1 m (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore (m+1+1)))
              (Work.Thom.cohTransport (by omega : 2 * (0 + m) = 2 * m)
                (Work.Whitney.cupChern 0 m U (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (m+1+1)) m)))) := by
      rw [psi_CohMap_cohTransport_cupChern, hPsiA, hPsiZZ]
    exact hL.symm.trans (h.trans hR)
  -- the right-hand side is `k • ζ^{m+1}`
  have h8 : Work.Thom.cohTransport (Work.Gen.psiDataDegree (m + 1) hn)
        (Work.Whitney.cupChern 1 m (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore (m+1+1)))
          (Work.Thom.cohTransport (by omega : 2 * (0 + m) = 2 * m)
            (Work.Whitney.cupChern 0 m U (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (m+1+1)) m))))
      = k • Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (m+1+1)) (m + 1) := by
    rw [hk, Work.Kunneth.cupChern_zsmul_left, Work.Thom.cohTransport_zsmul,
      Work.LerayHirsch.cohTransport_cupChern_one_left, Work.Gen.cupChern_zsmul_right,
      Work.Thom.cohTransport_zsmul, hζζ]
  -- cancellation of `ζ^{m+1}`
  have hkm : k = Work.Gen.modelK (m + 1) :=
    (Work.Kunneth.smul_zetaPow_injective (m + 1) (m + 1) le_rfl
      (Work.Gen.modelK (m + 1)) k (h7.trans h8)).symm
  have hU : U = Work.Gen.modelK (m + 1) • Work.Cohomology.oneH ℤ (Work.Whitney.ssB (psiModel m)) := by
    rw [hk, hkm]
  -- pull back to the fibre
  have h1 : v = (Work.Thom.CohMap
      (↑eidH : C(Work.LerayHirsch.ProjFibre W b, psiModel m)) ℤ 0).hom U :=
    (psi_CohMap_comp_homeo_symm eidH 0 v).symm
  rw [h1, hU, Work.Thom.CohMap_zsmul, Work.Thom.CohMap_oneH]

end

end Work.Gen
