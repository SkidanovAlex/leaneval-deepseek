import Mathlib
import Submission.Work.Pi6.MSS.e2Asm
import Submission.Work.Pi6.MSS.e2Bar
import Submission.Work.Pi6.MSS.e2Lbar
import Submission.Work.Pi6.MSS.e2Canon
import Submission.Work.Pi6.MSS.e2Canon_genN
import Submission.Work.Pi6.MSS.e2Psi_pairingN
import Submission.Work.Pi6.MSS.e2PsiCanonN
import Submission.Work.Pi6.MSS.e1SerreIso_genN_uni
import Submission.Work.Pi6.MSS.pairWcycleN
import Submission.Work.Pi6.MSS.genElemN_exists
import Submission.Work.Pi6.MSS.e2Lbar_pairElem
import Submission.Work.Pi6.MSS.e2L0_imd
import Submission.Work.Pi6.MSS.e2Psi_repr_ZB
import Submission.Work.Pi6.MSS.e2ColRho
import Submission.Work.Pi6.MSS.e2Row_exists
import Submission.Work.Pi6.MSS.E1B.homIsoH_inv
import Submission.Work.SSSR.homologyMap_cyclesMk
import Submission.Work.Pi6.MSS.mixedEvaluation
import Submission.Work.Pi6.MSS.CruxDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped TensorProduct Simplicial

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- `kappaF` is the Kronecker pairing with `triv`. -/
theorem e2pc_kappaF_value (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ)
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (m : Work.SSSR.coefM (R := 𝕜) p e₀ q) :
    kappaF 𝕜 E B p e₀ hfib hconn q f m
      = Work.Cohomology.kronH 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q f
          ((Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom.hom m) := by
  have key : ∀ (ψ : Work.SSSR.coefM (R := 𝕜) p e₀ q →ₗ[𝕜] 𝕜) (x : Work.SSSR.coefM (R := 𝕜) p e₀ q),
      (LinearEquiv.dualMap
        (Iso.toLinearEquiv (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).symm)).symm ψ x
        = ψ ((Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom.hom x) := by
    intro ψ x
    have h : (LinearEquiv.dualMap
        (Iso.toLinearEquiv (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).symm))
        ((LinearEquiv.dualMap
          (Iso.toLinearEquiv (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).symm)).symm ψ) = ψ :=
      LinearEquiv.apply_symm_apply _ _
    have h2 := congrArg (fun (g : Work.SSSR.coefM (R := 𝕜) p e₀ q →ₗ[𝕜] 𝕜) =>
      g ((Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).inv.hom x)) h
    rw [LinearEquiv.dualMap_apply] at h2
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h2
  simp only [kappaF, kappaFe, LinearEquiv.coe_trans, LinearEquiv.ofBijective_apply,
    LinearMap.comp_apply]
  exact key _ _

/-- `cruxEps` is a unit. -/
theorem e2pc_cruxEps_ne_zero (𝕜 : Type) [Field 𝕜] (s : ℕ) : cruxEps 𝕜 s ≠ 0 := by
  rw [cruxEps]
  intro h
  have h1 : Work.Pi6.MSSK.capSign 𝕜 s = 0 ∨
      ((Work.SSSR.iotaSign s : ℤ) : 𝕜) = 0 := mul_eq_zero.mp h
  rcases h1 with h1 | h1
  · rcases Work.Pi6.MSSK.capSign_eq_one_or_neg_one (R := 𝕜) s with h2 | h2 <;> rw [h2] at h1 <;> norm_num at h1
  · rcases Work.SSSR.iotaSign_or s with h2 | h2 <;> rw [h2] at h1 <;> norm_num at h1

/-- `cruxFibre` is the `triv`-transport of the fibre class. -/
theorem e2pc_cruxFibre_eq (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (n q : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).d q
      ((ComplexShape.down ℕ).next q))) z = 0) :
    cruxFibre 𝕜 p e₀ hfib hconn n q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z hz
      = (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).inv.hom
          ((ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).hom)
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ
              (Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))) q))
              (HomologicalComplex.cyclesMk (Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ)))
                z ((ComplexShape.down ℕ).next q) rfl hz))) := by
  rw [cruxFibre]
  rfl

/-- Linearity of `e1elt` in the argument. -/
theorem e2pc_e1elt_sum (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (n q : ℕ) {ι : Type} (t : Finset ι)
    (a : ι → 𝕜)
    (w : ι → ↥(Work.StemsB.fdZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q))) :
    e1elt 𝕜 p n q (∑ i ∈ t, a i • w i)
      = ∑ i ∈ t, a i • e1elt 𝕜 p n q (w i) := by
  let g : ↥(Work.StemsB.fdZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q)) →ₗ[𝕜]
      (Work.Pi6.MSS.Kg 𝕜 p n).homology (n + q) :=
    (ModuleCat.Hom.hom (e2Hb 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q)).inv).comp
      (Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q)).mkQ
  have hg : ∀ w : ↥(Work.StemsB.fdZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q)),
      e1elt 𝕜 p n q w = g w := fun w => rfl
  simp only [hg]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])

/-- Linearity of `e1elt` in the scalar. -/
theorem e2pc_e1elt_smul (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (n q : ℕ) (c : 𝕜)
    (w : ↥(Work.StemsB.fdZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q))) :
    e1elt 𝕜 p n q (c • w) = c • e1elt 𝕜 p n q w := by
  let g : ↥(Work.StemsB.fdZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q)) →ₗ[𝕜]
      (Work.Pi6.MSS.Kg 𝕜 p n).homology (n + q) :=
    (ModuleCat.Hom.hom (e2Hb 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q)).inv).comp
      (Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q)).mkQ
  have hg : ∀ w : ↥(Work.StemsB.fdZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q)),
      e1elt 𝕜 p n q w = g w := fun w => rfl
  simp only [hg]
  rw [map_smul]

/-- The cycle condition in the `E¹`-complex, transported along the chain map `e1SerreIso`. -/
theorem e2pc_e1SerreIso_d_eq_zero (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ)
    (x : ↥(Work.StemsB.fdZ 𝕜 (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q)) n)) :
    (ModuleCat.Hom.hom ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d n (n - 1)))
      ((e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f n x.1) = 0 := by
  have hnext : (ComplexShape.down ℕ).next n = n - 1 := Work.Cohomology.down_next n
  rw [show n - 1 = (ComplexShape.down ℕ).next n from hnext.symm]
  have hcomm := HomologicalComplex.Hom.comm (e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom n
    ((ComplexShape.down ℕ).next n)
  have h2 : (ModuleCat.Hom.hom ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d n ((ComplexShape.down ℕ).next n)))
      ((e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f n x.1)
      = (ModuleCat.Hom.hom ((e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f ((ComplexShape.down ℕ).next n)))
          ((ModuleCat.Hom.hom ((Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
            (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d n ((ComplexShape.down ℕ).next n))) x.1) := by
    have h := congrArg (fun (g : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).X n ⟶
        (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X ((ComplexShape.down ℕ).next n)) =>
      (ModuleCat.Hom.hom g) x.1) hcomm
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  rw [h2]
  have hx : (ModuleCat.Hom.hom ((Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d n ((ComplexShape.down ℕ).next n))) x.1 = 0 := by
    rw [hnext]; exact x.2
  rw [hx, map_zero]

/-- `e2mkQ` of the `e1SerreIso`-image of a cycle is `psiE2` of its homology class. -/
theorem e2pc_e2mkQ_e1SerreIso (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ)
    (x : ↥(Work.StemsB.fdZ 𝕜 (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q)) n))
    (hy : (ModuleCat.Hom.hom ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d n (n - 1)))
      ((e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f n x.1) = 0) :
    e2mkQ 𝕜 E B p n q ⟨(e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f n x.1, hy⟩
      = psiE2 𝕜 E B p e₀ hfib hconn q n
          ((Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM (R := 𝕜) p e₀ q)).homologyπ n
            ((Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM (R := 𝕜) p e₀ q)).cyclesMk
              x.1 ((ComplexShape.down ℕ).next n) rfl (by rw [Work.Cohomology.down_next]; exact x.2))) := by
  have hL : e2mkQ 𝕜 E B p n q ⟨(e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f n x.1, hy⟩
      = (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).homologyπ n
          ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).cyclesMk
            ((e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f n x.1)
            ((ComplexShape.down ℕ).next n) rfl (by rw [Work.Cohomology.down_next]; exact hy)) := by
    exact Work.Pi6.MSS.E1B.homIsoH_inv n ((e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f n x.1) hy
  have hR : psiE2 𝕜 E B p e₀ hfib hconn q n
      ((Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM (R := 𝕜) p e₀ q)).homologyπ n
        ((Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM (R := 𝕜) p e₀ q)).cyclesMk
          x.1 ((ComplexShape.down ℕ).next n) rfl (by rw [Work.Cohomology.down_next]; exact x.2)))
      = (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).homologyπ n
          ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).cyclesMk
            ((e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f n x.1)
            ((ComplexShape.down ℕ).next n) rfl (by rw [Work.Cohomology.down_next]; exact hy)) := by
    rw [psiE2]
    rw [← Work.SSSR.hmcm_homologyπ_map]
    rw [Work.SSSR.hmcm_cyclesMap_cyclesMk (e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom rfl x.1
      (by rw [Work.Cohomology.down_next]; exact x.2)
      (by rw [Work.Cohomology.down_next]; exact hy)]
  rw [hL, hR]

/-- The square of the trivialisation at the base point, as an automorphism of the coefficient
module. -/
noncomputable def e2pc_trivSq (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ) :
    Work.SSSR.coefM (R := 𝕜) p e₀ q ≃ₗ[𝕜] Work.SSSR.coefM (R := 𝕜) p e₀ q :=
  (Iso.toLinearEquiv (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀))).trans
    (Iso.toLinearEquiv (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)))

theorem e2pc_trivSq_apply (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ)
    (m : Work.SSSR.coefM (R := 𝕜) p e₀ q) :
    e2pc_trivSq 𝕜 p e₀ hfib hconn q m
      = (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom.hom
          ((Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom.hom m) := rfl

theorem e2pc_trivSq_symm_apply (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ)
    (m : Work.SSSR.coefM (R := 𝕜) p e₀ q) :
    (e2pc_trivSq 𝕜 p e₀ hfib hconn q).symm m
      = (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).inv.hom
          ((Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).inv.hom m) := by
  have h1 : (e2pc_trivSq 𝕜 p e₀ hfib hconn q).symm
      = (Iso.toLinearEquiv (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀))).symm.trans
        (Iso.toLinearEquiv (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀))).symm := by
    rw [e2pc_trivSq, LinearEquiv.trans_symm]
  rw [h1, LinearEquiv.trans_apply]
  rfl

/-- The fibre-factor automorphism `T₂` of `Ψ`: it conjugates `kappaF` by the square of `triv`. -/
noncomputable def e2pc_T2e (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ) :
    Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q ≃ₗ[𝕜]
      Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q :=
  (kappaFe 𝕜 E B p e₀ hfib hconn q).trans
    ((LinearEquiv.dualMap (e2pc_trivSq 𝕜 p e₀ hfib hconn q).symm).trans
      (kappaFe 𝕜 E B p e₀ hfib hconn q).symm)

theorem e2pc_kappaF_T2e (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ)
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    kappaF 𝕜 E B p e₀ hfib hconn q (e2pc_T2e 𝕜 p e₀ hfib hconn q f)
      = (kappaF 𝕜 E B p e₀ hfib hconn q f).comp
          (e2pc_trivSq 𝕜 p e₀ hfib hconn q).symm.toLinearMap := by
  show (kappaFe 𝕜 E B p e₀ hfib hconn q) ((e2pc_T2e 𝕜 p e₀ hfib hconn q) f) = _
  rw [show (e2pc_T2e 𝕜 p e₀ hfib hconn q) f
      = (kappaFe 𝕜 E B p e₀ hfib hconn q).symm
          ((LinearEquiv.dualMap (e2pc_trivSq 𝕜 p e₀ hfib hconn q).symm)
            ((kappaFe 𝕜 E B p e₀ hfib hconn q) f)) from rfl]
  rw [LinearEquiv.apply_symm_apply]
  ext x
  rw [LinearEquiv.dualMap_apply]
  rfl

theorem e2pc_kappaF_T2e_apply (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ)
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (m : Work.SSSR.coefM (R := 𝕜) p e₀ q) :
    kappaF 𝕜 E B p e₀ hfib hconn q (e2pc_T2e 𝕜 p e₀ hfib hconn q f) m
      = kappaF 𝕜 E B p e₀ hfib hconn q f ((e2pc_trivSq 𝕜 p e₀ hfib hconn q).symm m) := by
  rw [e2pc_kappaF_T2e]
  rfl

/-- **The key value rule of `T₂`**: on the trivialised fibre class attached to a simplex `σ` and a
fibre cycle `z`, `kappaF (T₂ f)` is the Kronecker pairing of `f` against `cruxFibre`. -/
theorem e2pc_kappaF_T2e_cruxFibre (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (q : ℕ)
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (s : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) s)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s σ))).d q
      ((ComplexShape.down ℕ).next q))) z = 0) :
    kappaF 𝕜 E B p e₀ hfib hconn q (e2pc_T2e 𝕜 p e₀ hfib hconn q f)
        ((Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s σ))).hom.hom
          ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ
            (Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s σ))) q))
            (HomologicalComplex.cyclesMk (Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s σ)))
              z ((ComplexShape.down ℕ).next q) rfl hz)))
      = Work.Cohomology.kronH 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q f
          (cruxFibre 𝕜 p e₀ hfib hconn s q
            (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s σ) z hz) := by
  rw [e2pc_kappaF_T2e_apply, e2pc_trivSq_symm_apply, e2pc_kappaF_value]
  rw [show (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).hom.hom
        ((Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).inv.hom
          ((Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).inv.hom
            ((Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s σ))).hom.hom
              ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ
                (Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s σ))) q))
                (HomologicalComplex.cyclesMk (Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s σ)))
                  z ((ComplexShape.down ℕ).next q) rfl hz)))))
      = (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)).inv.hom
          ((Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s σ))).hom.hom
            ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ
              (Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s σ))) q))
              (HomologicalComplex.cyclesMk (Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s σ)))
                z ((ComplexShape.down ℕ).next q) rfl hz))) from
    Iso.inv_hom_id_apply (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q (p e₀)) _]
  rw [e2pc_cruxFibre_eq]


/-- **The evaluation of the pairing on the generators.** -/
theorem e2pc_e2Lbar_gen (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s q : ℕ) (hq : q ≤ N) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (hE1 : ∀ (k : ℕ) (lam : Fin k → 𝕜) (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) s)
        (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).X q)
        (hz : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).d q
          ((ComplexShape.down ℕ).next q))) (z j) = 0)
        (hc : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p s).d (s + q) ((s + q) - 1)))
          (Work.Pi6.MSS.pairWchainN 𝕜 p hfib s q (σ j) (z j)) = 0),
        (Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s
            (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz)
          = (δ : ℤ) • (Work.Pi6.MSS.e2Hb 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).inv.hom
              ((Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).mkQ
                (Work.Pi6.MSS.pairWsumN 𝕜 p hfib s q k lam σ z hz hc)))
    (β : ↥(Work.Pi6.MSS.ZB 𝕜 B s)) (y : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (hf : Work.Pi6.MSS.rho 𝕜 E B p e₀ q
      (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).comap
        (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).subtype) y) = f)
    (k : ℕ) (lam : Fin k → 𝕜) (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) s)
    (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).X q)
    (hz : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).d q
      ((ComplexShape.down ℕ).next q))) (z j) = 0)
    (hcyc : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d s ((ComplexShape.down ℕ).next s)
        (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz) = 0) :
    Work.Pi6.MSS.e2Lbar 𝕜 E B p s q
        (Work.Pi6.MSS.e2Psi 𝕜 E B p e₀ (Work.Pi6.MSS.e2Row 𝕜 p)
          (Work.Pi6.MSS.e2ColAll 𝕜 p e₀ N hfib hconn hfin) s q
          (TensorProduct.tmul 𝕜 (Work.Pi6.MSS.clsB 𝕜 B s β) f))
        ⟨(Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s
            (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz),
          e2pc_e1SerreIso_d_eq_zero 𝕜 p e₀ hfib hconn s q
            ⟨Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz,
              LinearMap.mem_ker.mpr (by rw [← Work.Cohomology.down_next]; exact hcyc)⟩⟩
      = (δ : 𝕜) * cruxEps 𝕜 s * ∑ j : Fin k, lam j *
          (Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) β.1
            ((Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)).app
              (Opposite.op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s))) *
          (Work.Cohomology.kronH 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q f
            (cruxFibre 𝕜 p e₀ hfib hconn s q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j))
              (z j) (hz j))) := by
  have hcw : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p s).d (s + q) ((s + q) - 1)))
      (Work.Pi6.MSS.pairWchainN 𝕜 p hfib s q (σ j) (z j)) = 0 :=
    fun j => pairWcycleN 𝕜 E B p hfib s q (σ j) (z j) (hz j)
  have hE1j := hE1 k lam σ z hz hcw
  rw [e2Lbar_pairElem 𝕜 E B p e₀ N hfib hconn hfin s q hq β y f hf]
  have hval : ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s
      (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz))
      = (δ : 𝕜) • e1elt 𝕜 p s q
          (Work.Pi6.MSS.pairWsumN 𝕜 p hfib s q k lam σ z hz hcw) := by
    rw [hE1j, Int.cast_smul_eq_zsmul 𝕜 δ]
    rfl
  have hLval : e2L0 𝕜 E B p s q (Work.Pi6.MSS.pairElem 𝕜 p s q β y)
      ⟨(Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s
          (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz),
        e2pc_e1SerreIso_d_eq_zero 𝕜 p e₀ hfib hconn s q
          ⟨Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz,
            LinearMap.mem_ker.mpr (by rw [← Work.Cohomology.down_next]; exact hcyc)⟩⟩
      = (evZ 𝕜 p s (s + q) (hannSerre 𝕜 p))
          ⟨(Work.Pi6.MSS.pairElem 𝕜 p s q β y : (Work.Pi6.MSS.Wc 𝕜 p).C.X (s + q)),
            pZ_two_le_one 𝕜 p s (s + q) (Work.Pi6.MSS.pairElem 𝕜 p s q β y).2⟩
          ((Work.Pi6.MSS.e2Hb 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).hom.hom
            ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s
              (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz))) :=
    e2L0_evZ_apply 𝕜 p s q (Work.Pi6.MSS.pairElem 𝕜 p s q β y) _
  rw [hLval]
  have hmkQ : ∀ w : ↥(Work.StemsB.fdZ 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)),
      (Work.Pi6.MSS.e2Hb 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).hom.hom (e1elt 𝕜 p s q w)
        = (Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).mkQ w := by
    intro w
    rw [e1elt]
    exact Iso.inv_hom_id_apply (Work.Pi6.MSS.e2Hb 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)) _
  rw [hval]
  rw [show (Work.Pi6.MSS.e2Hb 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).hom.hom
        ((δ : 𝕜) • e1elt 𝕜 p s q (Work.Pi6.MSS.pairWsumN 𝕜 p hfib s q k lam σ z hz hcw))
      = (δ : 𝕜) • (Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).mkQ
          (Work.Pi6.MSS.pairWsumN 𝕜 p hfib s q k lam σ z hz hcw) from by
    rw [← e2pc_e1elt_smul]
    rw [hmkQ, map_smul]]
  rw [show (Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).mkQ
      (Work.Pi6.MSS.pairWsumN 𝕜 p hfib s q k lam σ z hz hcw)
      = ∑ j : Fin k, lam j • (Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).mkQ
          (Work.Pi6.MSS.pairWn 𝕜 p hfib s q (σ j) (z j) (hcw j)) from by
    show (Submodule.mkQ (Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)))
        (Work.Pi6.MSS.pairWsumN 𝕜 p hfib s q k lam σ z hz hcw) = _
    rw [Work.Pi6.MSS.pairWsumN]
    simp only [map_sum, map_smul]]
  rw [map_smul, map_sum, Finset.smul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul]
  have hpair : (evZ 𝕜 p s (s + q) (hannSerre 𝕜 p))
      ⟨(Work.Pi6.MSS.pairElem 𝕜 p s q β y : (Work.Pi6.MSS.Wc 𝕜 p).C.X (s + q)),
        pZ_two_le_one 𝕜 p s (s + q) (Work.Pi6.MSS.pairElem 𝕜 p s q β y).2⟩
      ((Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).mkQ
        (Work.Pi6.MSS.pairWn 𝕜 p hfib s q (σ j) (z j) (hcw j)))
      = Work.Pi6.MSS.pairRHSn 𝕜 p e₀ hfib hconn s q β y (σ j) (z j) (hz j) := by
    simpa only [Work.Pi6.MSS.pairElemOne] using
      Work.Pi6.MSS.e2Psi_pairingN 𝕜 E B p e₀ hfib hconn s q β y (σ j) (z j) (hz j) (hcw j)
  rw [hpair]
  rw [Work.Pi6.MSS.pairRHSn, hf]
  simp only [smul_eq_mul]
  ring


/-- `e2pc_e2Lbar_gen` in the form used by the final comparison: the evaluation at an arbitrary
`d¹`-cycle `v` whose underlying class is the `e1SerreIso`-image of the generator. -/
theorem e2pc_e2Lbar_gen_v (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s q : ℕ) (hq : q ≤ N) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (hE1 : ∀ (k : ℕ) (lam : Fin k → 𝕜) (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) s)
        (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).X q)
        (hz : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).d q
          ((ComplexShape.down ℕ).next q))) (z j) = 0)
        (hc : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p s).d (s + q) ((s + q) - 1)))
          (Work.Pi6.MSS.pairWchainN 𝕜 p hfib s q (σ j) (z j)) = 0),
        (Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s
            (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz)
          = (δ : ℤ) • (Work.Pi6.MSS.e2Hb 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).inv.hom
              ((Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p s) (s + q)).mkQ
                (Work.Pi6.MSS.pairWsumN 𝕜 p hfib s q k lam σ z hz hc)))
    (β : ↥(Work.Pi6.MSS.ZB 𝕜 B s)) (y : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q))
    (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (hf : Work.Pi6.MSS.rho 𝕜 E B p e₀ q
      (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).comap
        (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).subtype) y) = f)
    (k : ℕ) (lam : Fin k → 𝕜) (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) s)
    (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).X q)
    (hz : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).d q
      ((ComplexShape.down ℕ).next q))) (z j) = 0)
    (hcyc : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d s ((ComplexShape.down ℕ).next s)
        (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz) = 0)
    (v : ↥(Work.Pi6.MSS.e2KerD 𝕜 p s q))
    (hv : (v : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X s)
      = (Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s
          (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz)) :
    Work.Pi6.MSS.e2Lbar 𝕜 E B p s q
        (Work.Pi6.MSS.e2Psi 𝕜 E B p e₀ (Work.Pi6.MSS.e2Row 𝕜 p)
          (Work.Pi6.MSS.e2ColAll 𝕜 p e₀ N hfib hconn hfin) s q
          (TensorProduct.tmul 𝕜 (Work.Pi6.MSS.clsB 𝕜 B s β) f)) v
      = (δ : 𝕜) * cruxEps 𝕜 s * ∑ j : Fin k, lam j *
          (Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) β.1
            ((Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)).app
              (Opposite.op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s))) *
          (Work.Cohomology.kronH 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q f
            (cruxFibre 𝕜 p e₀ hfib hconn s q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j))
              (z j) (hz j))) := by
  have hvv : v = ⟨(Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s
      (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz),
      e2pc_e1SerreIso_d_eq_zero 𝕜 p e₀ hfib hconn s q
        ⟨Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz,
          LinearMap.mem_ker.mpr (by rw [← Work.Cohomology.down_next]; exact hcyc)⟩⟩ :=
    Subtype.ext hv
  rw [hvv]
  exact e2pc_e2Lbar_gen 𝕜 E B p e₀ N hfib hconn hfin s q hq δ hδ hE1 β y f hf k lam σ z hz hcyc

/-- The map `T` of the comparison: the identity on the base factor and `T₂` on the fibre factor,
scaled by the product of the two signs. -/
noncomputable def e2pc_Tmap (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (q s : ℕ)
    (δ : ℤ) :
    (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
        (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) →ₗ[𝕜]
      (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
        (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) :=
  ((δ : 𝕜) * cruxEps 𝕜 s) •
    (TensorProduct.map (LinearMap.id : Work.Pi6.Coh 𝕜 B s →ₗ[𝕜] Work.Pi6.Coh 𝕜 B s)
      (e2pc_T2e 𝕜 p e₀ hfib hconn q).toLinearMap)

theorem e2pc_Tmap_tmul (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (q s : ℕ)
    (δ : ℤ) (b : Work.Pi6.Coh 𝕜 B s) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q) :
    e2pc_Tmap 𝕜 p e₀ hfib hconn q s δ (TensorProduct.tmul 𝕜 b f)
      = ((δ : 𝕜) * cruxEps 𝕜 s) •
          TensorProduct.tmul 𝕜 b (e2pc_T2e 𝕜 p e₀ hfib hconn q f) := by
  simp only [e2pc_Tmap, LinearMap.smul_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq]
  rw [TensorProduct.smul_tmul']
  rfl

/-- The canonical pairing is compatible with scalar multiples of its argument. -/
theorem e2pc_e2Canon_smul (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s q : ℕ) (hq : q ≤ N) (c : 𝕜)
    (ξ : TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
        (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (w : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).homology s) :
    (Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq (c • ξ)) w
      = c * ((Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq ξ) w) := by
  rw [LinearEquiv.map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- **The canonical pairing on the generators, after applying `T₂` on the fibre factor.** -/
theorem e2pc_e2Canon_T_gen (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s q : ℕ) (hq : q ≤ N)
    (β : ↥(Work.Pi6.MSS.ZB 𝕜 B s)) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (k : ℕ) (lam : Fin k → 𝕜) (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) s)
    (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).X q)
    (hz : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).d q
      ((ComplexShape.down ℕ).next q))) (z j) = 0)
    (hcyc : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d s ((ComplexShape.down ℕ).next s)
        (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz) = 0)
    (v : ↥(Work.Pi6.MSS.e2KerD 𝕜 p s q))
    (hv : (v : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X s)
      = (Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s
          (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz)) :
    (Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq
        (TensorProduct.tmul 𝕜 (Work.Pi6.MSS.clsB 𝕜 B s β)
          (e2pc_T2e 𝕜 p e₀ hfib hconn q f)))
      (Work.Pi6.MSS.e2mkQ 𝕜 E B p s q v)
      = ∑ j : Fin k, lam j *
          (Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) β.1
            ((Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)).app
              (Opposite.op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s))) *
          (Work.Pi6.MSS.kappaF 𝕜 E B p e₀ hfib hconn q (e2pc_T2e 𝕜 p e₀ hfib hconn q f)
            (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
                (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).hom
              (ModuleCat.Hom.hom (HomologicalComplex.homologyπ
                  (Work.SSSR.fibreCC (R := 𝕜) p
                    (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))) q)
                (HomologicalComplex.cyclesMk
                  (Work.SSSR.fibreCC (R := 𝕜) p
                    (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j))))
                  (z j) ((ComplexShape.down ℕ).next q) rfl (hz j))))) := by
  have hx : Work.Pi6.MSS.e2mkQ 𝕜 E B p s q v
      = Work.Pi6.MSS.psiE2 𝕜 E B p e₀ hfib hconn q s
          (Work.Pi6.MSS.genCycN 𝕜 p e₀ hfib hconn s q k lam σ z hz hcyc) := by
    have hveq : v = ⟨(Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s
        (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz),
        e2pc_e1SerreIso_d_eq_zero 𝕜 p e₀ hfib hconn s q
          ⟨Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz,
            LinearMap.mem_ker.mpr (by rw [← Work.Cohomology.down_next]; exact hcyc)⟩⟩ :=
      Subtype.ext hv
    rw [hveq, Work.Pi6.MSS.genCycN]
    exact e2pc_e2mkQ_e1SerreIso 𝕜 p e₀ hfib hconn s q
      ⟨Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz,
        LinearMap.mem_ker.mpr (by rw [← Work.Cohomology.down_next]; exact hcyc)⟩ _
  rw [hx]
  exact Work.Pi6.MSS.e2Canon_genN 𝕜 E B p e₀ N hfib hconn hfin s q hq β
    (e2pc_T2e 𝕜 p e₀ hfib hconn q f) k lam σ z hz hcyc

/-- **The canonical pairing on the generators, with the fibre factor `T₂`-twisted and evaluated
against `cruxFibre`.** -/
theorem e2pc_e2Canon_T_gen_crux (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s q : ℕ) (hq : q ≤ N)
    (β : ↥(Work.Pi6.MSS.ZB 𝕜 B s)) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
    (k : ℕ) (lam : Fin k → 𝕜) (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) s)
    (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).X q)
    (hz : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)))).d q
      ((ComplexShape.down ℕ).next q))) (z j) = 0)
    (hcyc : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d s ((ComplexShape.down ℕ).next s)
        (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz) = 0)
    (v : ↥(Work.Pi6.MSS.e2KerD 𝕜 p s q))
    (hv : (v : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X s)
      = (Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s
          (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz)) :
    (Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq
        (TensorProduct.tmul 𝕜 (Work.Pi6.MSS.clsB 𝕜 B s β)
          (e2pc_T2e 𝕜 p e₀ hfib hconn q f)))
      (Work.Pi6.MSS.e2mkQ 𝕜 E B p s q v)
      = ∑ j : Fin k, lam j *
          (Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) β.1
            ((Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)).app
              (Opposite.op (SimplexCategory.mk s)) (Work.Pi6.MSSK.topS s))) *
          (Work.Cohomology.kronH 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q f
            (cruxFibre 𝕜 p e₀ hfib hconn s q
              (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) s (σ j)) (z j) (hz j))) := by
  rw [e2pc_e2Canon_T_gen 𝕜 E B p e₀ N hfib hconn hfin s q hq β f k lam σ z hz hcyc v hv]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [e2pc_kappaF_T2e_cruxFibre 𝕜 p e₀ hfib hconn q f s (σ j) (z j) (hz j)]


section Aux

/-- `e1SerreIso` cancels `e1SerreIso.inv`. -/
private lemma e2pc_inv_hom (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (q n : ℕ)
    (y : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X n) :
    (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f n))
      ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).inv.f n)) y) = y := by
  have h := congrArg (fun (g : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) ⟶
      (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q)) => (ModuleCat.Hom.hom (g.f n)) y)
    (Iso.inv_hom_id (Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q))
  rw [HomologicalComplex.id_f] at h
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] using h

/-- `e1SerreIso.inv` cancels `e1SerreIso`. -/
private lemma e2pc_hom_inv (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (q n : ℕ)
    (x : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q)).X n) :
    (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).inv.f n))
      ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f n)) x) = x := by
  have h := congrArg (fun (g : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q)) ⟶ (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q))) => (ModuleCat.Hom.hom (g.f n)) x)
    (Iso.hom_inv_id (Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q))
  rw [HomologicalComplex.id_f] at h
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] using h

/-- Each component of `e1SerreIso` is injective. -/
private lemma e2pc_hom_injective (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (q n : ℕ) :
    Function.Injective (fun x => (ModuleCat.Hom.hom
      ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f n)) x) := by
  intro a b hab
  have h2 := congrArg (fun w => (ModuleCat.Hom.hom
    ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).inv.f n)) w) hab
  simpa only [e2pc_hom_inv 𝕜 p e₀ hfib hconn q n] using h2

/-- The `d¹`-cycle condition transfers along `e1SerreIso.inv`. -/
private lemma e2pc_inv_d_eq_zero (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (q n : ℕ)
    (w : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X n)
    (hw : (ModuleCat.Hom.hom ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d n
      ((ComplexShape.down ℕ).next n))) w = 0) :
    (ModuleCat.Hom.hom ((Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d n ((ComplexShape.down ℕ).next n)))
      ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).inv.f n)) w) = 0 := by
  have hcomm := HomologicalComplex.Hom.comm (Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom
    n ((ComplexShape.down ℕ).next n)
  have h2 := congrArg (fun (g : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q)).X n ⟶
      (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X ((ComplexShape.down ℕ).next n)) =>
      (ModuleCat.Hom.hom g)
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).inv.f n)) w)) hcomm
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [e2pc_inv_hom 𝕜 p e₀ hfib hconn q n w] at h2
  have h3 : (ModuleCat.Hom.hom
      ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f ((ComplexShape.down ℕ).next n)))
      ((ModuleCat.Hom.hom ((Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d n ((ComplexShape.down ℕ).next n)))
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).inv.f n)) w))
      = (ModuleCat.Hom.hom
      ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f ((ComplexShape.down ℕ).next n))) 0 := by
    rw [← h2, hw, map_zero]
  exact (e2pc_hom_injective 𝕜 p e₀ hfib hconn q ((ComplexShape.down ℕ).next n)) h3

end Aux

/-- **The crux comparison of `e2Psi_bij`**: the pairing of the canonical map `Ψ` with the cycles
`e2KerD` agrees with the canonical pairing `e2Canon` up to a bijective twist `T` of the tensor
product.  The two pairings are compared on the generators (`e2Canon_genN`, `e2Psi_pairingN`) and
differ by the global scalar `cruxEps` (a product of `±1`, hence non-zero), so the witness is
`T = cruxEps 𝕜 (s+q) • LinearMap.id`. -/
theorem e2PsiCanon (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s q : ℕ) (hs : s ≤ N) (hq : q ≤ N) :
    ∃ T : (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
          (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) →ₗ[𝕜]
        (TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
          (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)),
      Function.Bijective T ∧
      ∀ (ξ : TensorProduct 𝕜 (Work.Pi6.Coh 𝕜 B s)
          (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
        (v : ↥(Work.Pi6.MSS.e2KerD 𝕜 p s q)),
        Work.Pi6.MSS.e2Lbar 𝕜 E B p s q
            (Work.Pi6.MSS.e2Psi 𝕜 E B p e₀ (Work.Pi6.MSS.e2Row 𝕜 p)
              (Work.Pi6.MSS.e2ColAll 𝕜 p e₀ N hfib hconn hfin) s q ξ) v
          = (Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq (T ξ))
              (Work.Pi6.MSS.e2mkQ 𝕜 E B p s q v) := by
  classical
  obtain ⟨δ, hδ, hE1⟩ := Work.Pi6.MSS.e1SerreIso_genN_uni 𝕜 E B p e₀ hfib hconn s q
  have hδ' : (δ : 𝕜) ≠ 0 := by rcases hδ with h | h <;> rw [h] <;> norm_num
  have hc0 : ((δ : 𝕜) * cruxEps 𝕜 s) ≠ 0 := mul_ne_zero hδ' (e2pc_cruxEps_ne_zero 𝕜 s)
  have hbij : Function.Bijective (e2pc_Tmap 𝕜 p e₀ hfib hconn q s δ) := by
    have hmap : Function.Bijective (TensorProduct.map
        (LinearMap.id : Work.Pi6.Coh 𝕜 B s →ₗ[𝕜] Work.Pi6.Coh 𝕜 B s)
        (e2pc_T2e 𝕜 p e₀ hfib hconn q).toLinearMap) := by
      have heq : TensorProduct.map
          (LinearMap.id : Work.Pi6.Coh 𝕜 B s →ₗ[𝕜] Work.Pi6.Coh 𝕜 B s)
          (e2pc_T2e 𝕜 p e₀ hfib hconn q).toLinearMap
          = (TensorProduct.congr (LinearEquiv.refl 𝕜 (Work.Pi6.Coh 𝕜 B s))
              (e2pc_T2e 𝕜 p e₀ hfib hconn q)).toLinearMap := by
        refine TensorProduct.ext' (fun a b => ?_)
        simp only [TensorProduct.map_tmul, LinearEquiv.coe_toLinearMap,
          TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearMap.id_coe, id_eq]
      rw [heq]
      exact (TensorProduct.congr _ _).bijective
    rw [e2pc_Tmap]
    constructor
    · intro x y hxy
      simp only [LinearMap.smul_apply] at hxy
      refine hmap.1 ?_
      have h2 := congrArg (fun z => ((δ : 𝕜) * cruxEps 𝕜 s)⁻¹ • z) hxy
      simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul] using h2
    · intro y
      obtain ⟨z, hz⟩ := hmap.2 (((δ : 𝕜) * cruxEps 𝕜 s)⁻¹ • y)
      refine ⟨z, ?_⟩
      simp only [LinearMap.smul_apply, hz]
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
  refine ⟨e2pc_Tmap 𝕜 p e₀ hfib hconn q s δ, hbij, ?_⟩
  intro ξ v
  have key : ∀ (β : ↥(Work.Pi6.MSS.ZB 𝕜 B s))
      (y : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q)),
      Work.Pi6.MSS.e2Lbar 𝕜 E B p s q
          (Work.Pi6.MSS.e2Psi 𝕜 E B p e₀ (Work.Pi6.MSS.e2Row 𝕜 p)
            (Work.Pi6.MSS.e2ColAll 𝕜 p e₀ N hfib hconn hfin) s q
            (TensorProduct.tmul 𝕜 (Work.Pi6.MSS.clsB 𝕜 B s β)
              (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
                (Submodule.mkQ
                  ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).comap
                    (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).subtype) y)))) v
        = (Work.Pi6.MSS.e2Canon 𝕜 E B p e₀ N hfib hconn hfin s q hq
            (e2pc_Tmap 𝕜 p e₀ hfib hconn q s δ
              (TensorProduct.tmul 𝕜 (Work.Pi6.MSS.clsB 𝕜 B s β)
                (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
                  (Submodule.mkQ
                    ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).comap
                      (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).subtype) y)))))
          (Work.Pi6.MSS.e2mkQ 𝕜 E B p s q v) := by
    intro β y
    obtain ⟨k, lam, σ, z, hz, hEq⟩ := Work.Pi6.MSS.genElemN_exists 𝕜 E B p e₀ hfib hconn s q
      ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).inv.f s))
        (v : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X s))
    have hv0 : (ModuleCat.Hom.hom ((Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).d s
        ((ComplexShape.down ℕ).next s)))
        (v : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X s) = 0 := by
      rw [Work.Cohomology.down_next]
      exact v.2
    have hcyc : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d s ((ComplexShape.down ℕ).next s)
        (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz) = 0 := by
      rw [hEq]
      exact e2pc_inv_d_eq_zero 𝕜 p e₀ hfib hconn q s _ hv0
    have hhom : (ModuleCat.Hom.hom
        ((Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s))
        (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn s q k lam σ z hz)
        = (v : (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q).X s) := by
      rw [hEq]
      exact e2pc_inv_hom 𝕜 p e₀ hfib hconn q s _
    have hA := e2pc_e2Lbar_gen_v 𝕜 E B p e₀ N hfib hconn hfin s q hq δ hδ hE1 β y
      (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
        (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).comap
          (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).subtype) y)) rfl
      k lam σ z hz hcyc v hhom.symm
    have hB := e2pc_e2Canon_T_gen_crux 𝕜 E B p e₀ N hfib hconn hfin s q hq β
      (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
        (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).comap
          (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).subtype) y))
      k lam σ z hz hcyc v hhom.symm
    rw [e2pc_Tmap_tmul]
    rw [e2pc_e2Canon_smul 𝕜 E B p e₀ N hfib hconn hfin s q hq ((δ : 𝕜) * cruxEps 𝕜 s)
      (TensorProduct.tmul 𝕜 (Work.Pi6.MSS.clsB 𝕜 B s β)
        (e2pc_T2e 𝕜 p e₀ hfib hconn q
          (Work.Pi6.MSS.rho 𝕜 E B p e₀ q
            (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).comap
              (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).subtype) y))))
      (Work.Pi6.MSS.e2mkQ 𝕜 E B p s q v)]
    rw [hB]
    rw [hA]
  refine TensorProduct.inductionOn ξ ?_ ?_
  · intro a b
    obtain ⟨β, rfl⟩ : ∃ β : ↥(Work.Pi6.MSS.ZB 𝕜 B s), Work.Pi6.MSS.clsB 𝕜 B s β = a := by
      have h : a ∈ (Work.Pi6.MSS.clsB 𝕜 B s).range := by
        rw [Work.Pi6.MSS.clsB_range_top]; exact Submodule.mem_top
      exact (LinearMap.mem_range).mp h
    obtain ⟨u, rfl⟩ : ∃ u, Work.Pi6.MSS.rho 𝕜 E B p e₀ q u = b :=
      Work.Pi6.MSS.rho_surjective 𝕜 E B p e₀ N q hfib hconn hfin hq b
    obtain ⟨y, rfl⟩ : ∃ y, Submodule.mkQ
        ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).comap
          (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q).subtype) y = u :=
      Submodule.mkQ_surjective _ u
    exact key β y
  · intro x y hx hy
    simp only [map_add, LinearMap.add_apply]
    rw [hx, hy]

end Work.Pi6.MSS
