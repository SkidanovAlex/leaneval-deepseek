import Mathlib
import Submission.Work.Pi6.MSS.e2PsiCanonN
import Submission.Work.Pi6.MSS.e1SerreIso_gen
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `e1SerreIso` on the canonical generators of `E¹`, uniformly in the filtration degree

`Work.Pi6.MSS.e1SerreIso` is the explicit isomorphism `N_*(B) ⊗ H_q(F) ≅ E¹_{*,q}` of the first
page of the Serre spectral sequence of a Serre fibration `p : E → B` with simply connected base.

`Work.Pi6.MSS.e1SerreIso_gen` computes this isomorphism on the canonical generators
`genElem = ∑_j λ_j ι_{σ_j}(triv_{σ_j}[z_j])` of `N_{s+1}(B) ⊗ H_q(F)`, but only in filtration
degrees `≥ 1` (its index `s` is the filtration degree and the total degree is `s + 1`).  The
comparison `Work.Pi6.MSS.e2Psi_canon` is needed in *all* degrees, in particular in degree `0`, so
here we reproduce the same computation with the total degree `n` as the parameter, and — the point
of the present file — with the sign made **uniform** in the presentation data
(`k`, `λ`, `σ`, `z`, `h_z`, `h_c`): there is a single `δ ∈ {1, -1}`, depending only on `(n, q)`,
such that the identity holds for every choice of the data.

The mathematical content is `Work.SSSR.exists_pieceAlpha` (the sign spec of the σ-piece
isomorphism `ε_σ = serreE1PieceIso`), which is a statement about an arbitrary simplex dimension:
`Work.Pi6.MSS.psiSig_generatorN` below is the degree-`n` version of
`Work.Pi6.MSS.psiSig_generator` (whose proof only ever used the degree-general ingredients, the
degree `k+1` appearing exclusively as a *spelling* of the simplex dimension).

The main theorem `e1SerreIso_genN_uni` is then obtained exactly as `e1SerreIso_gen` is: the sign of
`e1SerreIso` on degree `n` is the product of the chain-condition correction
`signCorr eps n` (`signCorr eps 0 = 1`) with the sign `c n` of the generator computation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Elementwise bookkeeping lemmas -/

/-- For an isomorphism `e : M ≅ N` of `𝕜`-modules, `e⁻¹ ∘ e = id` on elements. -/
private lemma iso_inv_hom_apply {𝕜 : Type} [Ring 𝕜] {M N : ModuleCat 𝕜} (e : M ≅ N) (y : M) :
    (ModuleCat.Hom.hom e.inv) ((ModuleCat.Hom.hom e.hom) y) = y := by
  have h := Iso.hom_inv_id e
  have h2 := congrArg (fun (f : M ⟶ M) => (ModuleCat.Hom.hom f) y) h
  simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using h2

/-- The class of a cycle in `Z_n ⧸ B_n`, read through `e2Hb`, is the homology class of the
cycle.  (This is `Work.Pi6.MSS.E1B.homIsoH_inv`, whose isomorphism is `e2Hb` by definition.) -/
private lemma e2Hb_inv_mkQ_eq (𝕜 : Type) [Field 𝕜] (K : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ)
    (w : ↥(Work.StemsB.fdZ 𝕜 K n)) :
    (e2Hb 𝕜 K n).inv.hom ((Work.StemsB.fdH 𝕜 K n).mkQ w)
      = K.homologyπ n (K.cyclesMk (w : K.X n) ((ComplexShape.down ℕ).next n) rfl
          (by rw [Work.Cohomology.down_next]; exact w.property)) :=
  Work.Pi6.MSS.E1B.homIsoH_inv n (w : K.X n) w.property

/-- The class map `e2Hb.inv ∘ mkQ` is `𝕜`-linear: it commutes with finite sums. -/
private lemma e2Hb_mkQ_sum (𝕜 : Type) [Field 𝕜] (K : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ)
    {ι : Type} (t : Finset ι) (a : ι → 𝕜) (w : ι → ↥(Work.StemsB.fdZ 𝕜 K n)) :
    (e2Hb 𝕜 K n).inv.hom ((Work.StemsB.fdH 𝕜 K n).mkQ (∑ j ∈ t, a j • w j))
      = ∑ j ∈ t, a j • (e2Hb 𝕜 K n).inv.hom
          ((Work.StemsB.fdH 𝕜 K n).mkQ (w j)) := by
  set g : ↥(Work.StemsB.fdZ 𝕜 K n) →ₗ[𝕜] K.homology n :=
    (ModuleCat.Hom.hom (e2Hb 𝕜 K n).inv).comp (Work.StemsB.fdH 𝕜 K n).mkQ with hg
  change g (∑ j ∈ t, a j • w j) = ∑ j ∈ t, a j • g (w j)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [map_smul])

/-- The `s`-th component of `e1SerreIso`, on elements, is the sign correction applied to the
comparison map `PsiG`. -/
private lemma e1SerreIso_hom_f_apply (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (q s : ℕ) (x : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM p e₀ q)).X s) :
    (e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f s x =
      (Work.SSSR.signCorr (Classical.choose (Work.SSSR.serreE1_chainCondition
        (R := 𝕜) p e₀ hfib hconn q)) s) •
      ((Work.SSSR.PsiG p e₀ hfib hconn q (e1cFilt 𝕜 p) rfl s) x) := rfl

/-! ## The generator computation in degree `n`: `PsiSig` on a single generator -/

/-- The degree-`n` generator computation for the comparison map `PsiSig`: there is a sign family
`c n = ±1` such that, for every nondegenerate `n`-simplex `σ` of the base and every cycle `z` of
the fibre over the first vertex of `σ`, the `σ`-component of `PsiSig` sends the class of `z`
(trivialised along `triv`) to `c n` times the class of the Eilenberg–Zilber chain `ι_σ z` pushed to
the graded piece `Kg n`.

This is `Work.Pi6.MSS.psiSig_generator` with the simplex dimension `k+1` replaced by a general
`n`; every ingredient of its proof the finite-filtration-degree parts aside is already general in
the simplex dimension. -/
def PsiSigGen (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (c : ℕ → ℤ) : Prop :=
  ∀ (n q : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).d q
      ((ComplexShape.down ℕ).next q))) z = 0)
    (hcyc : (ModuleCat.Hom.hom ((Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) n).d (n + q)
      ((ComplexShape.down ℕ).next (n + q))))
      ((ModuleCat.Hom.hom ((Work.SSSR.grFι 𝕜 (Work.SSSR.sSingP p) n).f (n + q)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
          (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f (n + q)))
          (Work.Pi6.MSS.cruxIota 𝕜 p hfib n q
            (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z))) = 0),
    (ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib hconn q n))
        ((CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) n =>
            Work.SSSR.coefM (R := 𝕜) p e₀ q) σ)
          ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).hom)
            ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).homologyπ q))
              ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).cyclesMk z
                ((ComplexShape.down ℕ).next q) rfl hz))))
      = c n • (Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) n).homologyπ (n + q)
          ((Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) n).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.grFι 𝕜 (Work.SSSR.sSingP p) n).f (n + q)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
                (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f (n + q)))
                (Work.Pi6.MSS.cruxIota 𝕜 p hfib n q
                  (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z)))
            ((ComplexShape.down ℕ).next (n + q)) rfl hcyc)

theorem psiSig_generatorN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) :
    ∃ c : ℕ → ℤ, (∀ n : ℕ, c n = 1 ∨ c n = -1) ∧ PsiSigGen 𝕜 E B p e₀ hfib hconn c := by
  obtain ⟨c, hc1, hal⟩ := Work.SSSR.exists_pieceAlpha (R := 𝕜) p hfib
  refine ⟨c, hc1, ?_⟩
  intro n q σ z hz hcyc
  have hy := Work.SSSR.IotaChain.iotaF_cycle (R := 𝕜) p hfib n q
    (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))
    (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) rfl z hz
  have hpinv := Work.SSSR.pieceInv_of_pieceAlpha (R := 𝕜) p hfib c hc1 hal n q
    (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z hz hy
  have hchain : (ModuleCat.Hom.hom ((Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) n σ).f (n+q)))
      ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
        n (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) rfl q)) z)
    = (ModuleCat.Hom.hom ((Work.SSSR.grFι 𝕜 (Work.SSSR.sSingP p) n).f (n+q)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f (n+q)))
        (Work.Pi6.MSS.cruxIota 𝕜 p hfib n q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z)) := by
    have h1 : (ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
        n (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))
        (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) rfl q)) z
      = (ModuleCat.Hom.hom ((Work.SSSR.pieceπ 𝕜 (Work.SSSR.sSingP p) n σ).f (n+q)))
        ((ModuleCat.Hom.hom (Work.SSSR.iotaT p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
          n (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))
          (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) rfl q)) z) := rfl
    rw [h1]
    exact Work.SSSR.thetaPhi_mapPhiY_apply_f_elem (Work.SSSR.sSingP p) n (n+q) σ _
  have hx' : (Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) n).d (n+q)
        ((ComplexShape.down ℕ).next (n+q))
        ((ModuleCat.Hom.hom ((Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) n σ).f (n+q)))
          ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
            n (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))
            (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) rfl q)) z)) = 0 := by
    rw [hchain]
    exact hcyc
  have hmap : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) n σ) (n+q)))
        ((Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p) (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ)).homologyπ (n+q)
          ((Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p) (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ)).cyclesMk
            ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
              n (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))
              (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) rfl q)) z)
            ((ComplexShape.down ℕ).next (n+q)) rfl hy))
      = (Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) n).homologyπ (n+q)
          ((Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) n).cyclesMk
            ((ModuleCat.Hom.hom ((Work.SSSR.grFι 𝕜 (Work.SSSR.sSingP p) n).f (n+q)))
              ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f (n+q)))
                (Work.Pi6.MSS.cruxIota 𝕜 p hfib n q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z)))
            ((ComplexShape.down ℕ).next (n+q)) rfl hcyc) :=
    ((Work.SSSR.homologyMap_cyclesMk
        (Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) n σ) (hj := rfl)
        (x := (ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
          n (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))
          (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) rfl q)) z)
        hy hx').symm).trans
      (Work.SSSR.homologyπ_cyclesMk_eq (hj := rfl) hchain hx' hcyc)
  have hpsi : (ModuleCat.Hom.hom (Work.SSSR.PsiCoef (R := 𝕜) p e₀ hfib hconn q n σ).hom)
        ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).hom)
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).cyclesMk z
              ((ComplexShape.down ℕ).next q) rfl hz)))
      = c n • (Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p) (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ)).homologyπ (n+q)
          ((Work.SSSR.pieceAlong 𝕜 (Work.SSSR.sSingP p) (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ)).cyclesMk
            ((ModuleCat.Hom.hom (Work.SSSR.iotaF p (Work.SSSR.liftFam p hfib) (Work.SSSR.liftFam_proj p hfib)
              n (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))
              (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) rfl q)) z)
            ((ComplexShape.down ℕ).next (n+q)) rfl hy) := by
    have hcoe : (ModuleCat.Hom.hom (Work.SSSR.PsiCoef (R := 𝕜) p e₀ hfib hconn q n σ).hom)
        ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).hom)
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).cyclesMk z
              ((ComplexShape.down ℕ).next q) rfl hz)))
        = (ModuleCat.Hom.hom (Work.SSSR.serreE1PieceIso p hfib n q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ)).inv)
            ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).inv)
              ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
                (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).hom)
                ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).homologyπ q))
                  ((Work.SSSR.fibreCC (R := 𝕜) p
                    (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).cyclesMk z
                    ((ComplexShape.down ℕ).next q) rfl hz)))) := rfl
    rw [hcoe, iso_inv_hom_apply]
    exact hpinv
  rw [← ModuleCat.comp_apply (CategoryTheory.Limits.Sigma.ι
        (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) n => Work.SSSR.coefM (R := 𝕜) p e₀ q) σ)
        (Work.SSSR.PsiSig p e₀ hfib hconn q n) _]
  rw [Work.SSSR.Sigma_ι_comp_PsiSig (R := 𝕜) p e₀ hfib hconn q n σ]
  rw [ModuleCat.comp_apply]
  rw [hpsi, map_zsmul, hmap]

/-! ## The generator computation in the `e2Hb` form -/

/-- **The comparison map `PsiSig` on a single canonical generator**, in the `E²`-coordinates of
`e2Hb`: for a nondegenerate `n`-simplex `σ` and a fibre cycle `z`, the `σ`-component of `PsiSig`
sends `(triv) [z]` to `c n` times the `e2Hb`-class of the graded-piece cycle `pairWn`. -/
theorem PsiSig_singleN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (c : ℕ → ℤ)
    (hgen : PsiSigGen 𝕜 E B p e₀ hfib hconn c)
    (n q : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).d q
      ((ComplexShape.down ℕ).next q))) z = 0)
    (hc : (ModuleCat.Hom.hom ((Kg 𝕜 p n).d (n + q) ((n + q) - 1)))
      (pairWchainN 𝕜 p hfib n q σ z) = 0) :
    (Work.SSSR.PsiSig p e₀ hfib hconn q n)
        ((CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) n =>
            Work.SSSR.coefM (R := 𝕜) p e₀ q) σ)
          ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).hom)
            ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).homologyπ q))
              ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).cyclesMk z
                ((ComplexShape.down ℕ).next q) rfl hz))))
      = c n • (e2Hb 𝕜 (Kg 𝕜 p n) (n + q)).inv.hom
          ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p n) (n + q)).mkQ
            (pairWn 𝕜 p hfib n q σ z hc)) := by
  have hcyc : (ModuleCat.Hom.hom ((Work.SSSR.grF (Work.SSSR.serF 𝕜 (Work.SSSR.sSingP p)) n).d (n + q)
      ((ComplexShape.down ℕ).next (n + q))))
      ((ModuleCat.Hom.hom ((Work.SSSR.grFι 𝕜 (Work.SSSR.sSingP p) n).f (n + q)))
        ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
          (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f (n + q)))
          (Work.Pi6.MSS.cruxIota 𝕜 p hfib n q
            (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z))) = 0 := by
    rw [Work.Cohomology.down_next]
    exact hc
  rw [hgen n q σ z hz hcyc]
  rw [e2Hb_inv_mkQ_eq 𝕜 (Kg 𝕜 p n) (n+q) (pairWn 𝕜 p hfib n q σ z hc)]
  congr 1

/-- **The comparison map `PsiSig` on the generator `genElemN`**: up to the sign `c n`, it is the
`e2Hb`-class of `pairWsumN`. -/
theorem PsiSig_genElemN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (c : ℕ → ℤ)
    (hgen : PsiSigGen 𝕜 E B p e₀ hfib hconn c)
    (n q k : ℕ) (lam : Fin k → 𝕜) (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).X q)
    (hz : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).d q
      ((ComplexShape.down ℕ).next q))) (z j) = 0)
    (hc : ∀ j : Fin k, (ModuleCat.Hom.hom ((Kg 𝕜 p n).d (n + q) ((n + q) - 1)))
      (pairWchainN 𝕜 p hfib n q (σ j) (z j)) = 0) :
    (Work.SSSR.PsiSig p e₀ hfib hconn q n)
        ((Work.SSSR.serreE1CoefIsoIso (Work.SSSR.sSing B)
          (Work.SSSR.coefM (R := 𝕜) p e₀ q) n).inv.hom
          (genElemN 𝕜 p e₀ hfib hconn n q k lam σ z hz))
      = c n • (e2Hb 𝕜 (Kg 𝕜 p n) (n + q)).inv.hom
          ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p n) (n + q)).mkQ
            (pairWsumN 𝕜 p hfib n q k lam σ z hz hc)) := by
  rw [genElemN, iso_inv_hom_apply, map_sum, pairWsumN]
  rw [e2Hb_mkQ_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_smul, PsiSig_singleN 𝕜 E B p e₀ hfib hconn c hgen]
  rw [smul_comm]

/-- `PsiG` on the degree-`n` generator, expressed through `PsiSig`. -/
private theorem PsiG_genElemN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (n q k : ℕ) (lam : Fin k → 𝕜) (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).X q)
    (hz : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).d q
      ((ComplexShape.down ℕ).next q))) (z j) = 0) :
    (Work.SSSR.PsiG p e₀ hfib hconn q (e1cFilt 𝕜 p) rfl n)
        (genElemN 𝕜 p e₀ hfib hconn n q k lam σ z hz)
      = (Work.SSSR.PsiSig p e₀ hfib hconn q n)
          ((Work.SSSR.serreE1CoefIsoIso (Work.SSSR.sSing B)
            (Work.SSSR.coefM (R := 𝕜) p e₀ q) n).inv.hom
            (genElemN 𝕜 p e₀ hfib hconn n q k lam σ z hz)) := by
  rw [Work.SSSR.PsiG_eq]
  simp only [ModuleCat.comp_apply, eqToHom_refl]
  exact ModuleCat.id_apply _ _

/-! ## The main theorem -/

/-- **`e1SerreIso` on the canonical generators of `E¹`, uniformly in the presentation.**

For a Serre fibration `p : E → B` with simply connected base and fixed `(n, q)` there is a single
sign `δ ∈ {1, -1}` such that for *every* finite presentation
`∑_j λ_j ι_{σ_j}(triv_{σ_j}[z_j])` of an element of `N_n(B) ⊗ H_q(F)` (with the `z_j` cycles of the
fibre), the degree-`n` component of `e1SerreIso` sends that generator to `δ` times the `E²`-class of
`∑_j λ_j pairW_{σ_j}(z_j)`.

This is the degree-general, uniform-sign form of `Work.Pi6.MSS.e1SerreIso_gen`; in particular it
covers the filtration degree `n = 0`, where the sign correction `signCorr eps 0` is `1` and the
whole sign comes from the generator computation `psiSig_generatorN`. -/
theorem e1SerreIso_genN_uni (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ) :
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧
      ∀ (k : ℕ) (lam : Fin k → 𝕜) (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) n)
        (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).X q)
        (hz : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).d q
          ((ComplexShape.down ℕ).next q))) (z j) = 0)
        (hc : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p n).d (n + q) ((n + q) - 1)))
          (Work.Pi6.MSS.pairWchainN 𝕜 p hfib n q (σ j) (z j)) = 0),
        (Work.Pi6.MSS.e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f n
            (Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn n q k lam σ z hz)
          = δ • (Work.Pi6.MSS.e2Hb 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q)).inv.hom
              ((Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q)).mkQ
                (Work.Pi6.MSS.pairWsumN 𝕜 p hfib n q k lam σ z hz hc)) := by
  obtain ⟨c, hc1, hgen⟩ := psiSig_generatorN 𝕜 E B p e₀ hfib hconn
  refine ⟨Work.SSSR.signCorr (Classical.choose (Work.SSSR.serreE1_chainCondition
      (R := 𝕜) p e₀ hfib hconn q)) n * c n, ?_, ?_⟩
  · have heps := (Classical.choose_spec (Work.SSSR.serreE1_chainCondition
      (R := 𝕜) p e₀ hfib hconn q)).1
    rcases Work.SSSR.signCorr_eq_one_or_neg _ heps n with h | h <;>
      rcases hc1 n with h' | h' <;> rw [h, h'] <;> norm_num
  · intro k lam σ z hz hc
    rw [e1SerreIso_hom_f_apply, PsiG_genElemN 𝕜 E B p e₀ hfib hconn n q k lam σ z hz,
      PsiSig_genElemN 𝕜 E B p e₀ hfib hconn c hgen n q k lam σ z hz hc]
    rw [smul_smul]

end

end Work.Pi6.MSS
