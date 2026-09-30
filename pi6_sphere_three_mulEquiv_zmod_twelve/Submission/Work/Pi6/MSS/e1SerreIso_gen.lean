import Mathlib
import Submission.Work.Pi6.MSS.e2FinalDefs
import Submission.Work.Pi6.MSS.E1B.homIsoH_inv
import Submission.Work.Pi6.MSS.psiSig_generator
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The comparison isomorphism `e1SerreIso` on the canonical generators of `E¹`

`Work.Pi6.MSS.e1SerreIso` is the explicit isomorphism
`N_*(B) ⊗ H_q(F) ≅ E¹_{*,q}` of the first page of the Serre spectral sequence of a Serre
fibration `p : E → B` with simply connected base, built by multiplying the explicit comparison
map `PsiG` by the sign correction `signCorr eps` coming from the chain condition
(`Work.SSSR.serreE1_chainCondition`).

Here we evaluate it on the canonical generators
`genElem = ∑_j λ_j ι_{σ_j}(triv_{σ_j}[z_j])` of `N_{s+1}(B) ⊗ H_q(F)`: the result is, up to a
sign, the class of the Eilenberg–Zilber chain `pairWsum = ∑_j λ_j pairW_{σ_j}(z_j)` in the graded
piece `Kg (s+1)` of the Serre filtration.  The sign depends only on `q` and `s + 1` (it is the
product of the sign correction of `serreE1` with the sign `c` produced by `psiSig_generator` and
`exists_pieceAlpha`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
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

/-- `iCycles` of `cyclesMk`, in the module-level form. -/
private lemma iCycles_cyclesMk_mod {𝕜 : Type} [Field 𝕜] {K : ChainComplex (ModuleCat 𝕜) ℕ} {a : ℕ}
    (x : K.X a) (j : ℕ) (hj : (ComplexShape.down ℕ).next a = j) (hx : (K.d a j).hom x = 0) :
    (K.iCycles a).hom (K.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := K) (x := x) (j := j) (hj := hj) (hx := hx)

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

/-- `PsiG` on the image of the coefficient isomorphism is `PsiSig`. -/
private lemma PsiG_genElem (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (q s n : ℕ) (lam : Fin n → 𝕜) (σ : Fin n → Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1))
    (z : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).X q)
    (hz : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).d q
      ((ComplexShape.down ℕ).next q) (z j) = 0) :
    (Work.SSSR.PsiG p e₀ hfib hconn q (e1cFilt 𝕜 p) rfl (s+1))
        (genElem 𝕜 p e₀ hfib hconn s q n lam σ z hz)
      = (Work.SSSR.PsiSig p e₀ hfib hconn q (s+1))
          ((Work.SSSR.serreE1CoefIsoIso (Work.SSSR.sSing B) (Work.SSSR.coefM p e₀ q) (s+1)).inv.hom
            (genElem 𝕜 p e₀ hfib hconn s q n lam σ z hz)) := by
  rw [Work.SSSR.PsiG_eq]
  simp only [ModuleCat.comp_apply, eqToHom_refl]
  exact ModuleCat.id_apply _ _

/-! ## The comparison map on a single generator -/

/-- `PsiSig` on a single canonical generator `ι_σ(triv_σ[z])`: the image is the class of `pairW`,
up to the sign `c` of `psiSig_generator`. -/
private lemma PsiSig_single (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (k q : ℕ) (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1))
    (z : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).X q)
    (hz : (Work.SSSR.fibreCC (R := 𝕜) p (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).d q
      ((ComplexShape.down ℕ).next q) z = 0) :
    (Work.SSSR.PsiSig p e₀ hfib hconn q (k+1))
      ((CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
          Work.SSSR.coefM p e₀ q) σ)
        ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
            (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).hom)
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat σ))).cyclesMk z
              ((ComplexShape.down ℕ).next q) rfl hz))))
    = (Classical.choose (psiSig_generator 𝕜 E B p e₀ hfib hconn)) (k+1) •
        (e2Hb 𝕜 (Kg 𝕜 p (k+1)) ((k+1)+q)).inv.hom
          ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p (k+1)) ((k+1)+q)).mkQ
            (pairW 𝕜 p hfib k q σ z hz)) := by
  obtain ⟨_hc1, hcgen⟩ := Classical.choose_spec (psiSig_generator 𝕜 E B p e₀ hfib hconn)
  rw [hcgen k q σ z hz (Kgpi_d_cruxIota_sndToR 𝕜 E B p hfib k q σ z hz)]
  rw [e2Hb_inv_mkQ_eq 𝕜 (Kg 𝕜 p (k+1)) ((k+1)+q) (pairW 𝕜 p hfib k q σ z hz)]
  congr 1

/-- **The comparison map `PsiSig` on the generator `genElem`**: up to the sign `c` of
`psiSig_generator`, it is the class of `pairWsum`. -/
private lemma PsiSig_genElem (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (q s n : ℕ) (lam : Fin n → 𝕜) (σ : Fin n → Work.SSSR.nIndex (Work.SSSR.sSing B) (s+1))
    (z : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).X q)
    (hz : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).d q
      ((ComplexShape.down ℕ).next q) (z j) = 0) :
    (Work.SSSR.PsiSig p e₀ hfib hconn q (s+1))
        ((Work.SSSR.serreE1CoefIsoIso (Work.SSSR.sSing B) (Work.SSSR.coefM p e₀ q) (s+1)).inv.hom
          (genElem 𝕜 p e₀ hfib hconn s q n lam σ z hz))
      = (Classical.choose (psiSig_generator 𝕜 E B p e₀ hfib hconn)) (s+1) •
        (e2Hb 𝕜 (Kg 𝕜 p (s+1)) ((s+1)+q)).inv.hom
          ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p (s+1)) ((s+1)+q)).mkQ
            (pairWsum 𝕜 p hfib s q n lam σ z hz)) := by
  rw [genElem, iso_inv_hom_apply, map_sum, pairWsum]
  simp only [map_smul, PsiSig_single]
  rw [e2Hb_mkQ_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [smul_comm]

/-! ## The theorem -/

theorem e1SerreIso_gen (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) :
    ∃ δ : ℕ → ℕ → ℤ, (∀ q n : ℕ, δ q n = 1 ∨ δ q n = -1) ∧
      ∀ (q s n : ℕ) (lam : Fin n → 𝕜)
        (σ : Fin n → Work.SSSR.nIndex (Work.SSSR.sSing B) (s + 1))
        (z : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).X q)
        (hz : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).d q
          ((ComplexShape.down ℕ).next q) (z j) = 0),
        (e1SerreIso 𝕜 E B p e₀ hfib hconn q).hom.f (s + 1)
            (genElem 𝕜 p e₀ hfib hconn s q n lam σ z hz)
          = δ q (s + 1) •
            (e2Hb 𝕜 (Kg 𝕜 p (s + 1)) ((s + 1) + q)).inv.hom
              ((Work.StemsB.fdH 𝕜 (Kg 𝕜 p (s + 1)) ((s + 1) + q)).mkQ
                (pairWsum 𝕜 p hfib s q n lam σ z hz)) := by
  refine ⟨fun q n => Work.SSSR.signCorr (Classical.choose (Work.SSSR.serreE1_chainCondition
      (R := 𝕜) p e₀ hfib hconn q)) n *
      (Classical.choose (psiSig_generator 𝕜 E B p e₀ hfib hconn)) n, ?_, ?_⟩
  · intro q n
    have heps : ∀ s : ℕ, (Classical.choose (Work.SSSR.serreE1_chainCondition
        (R := 𝕜) p e₀ hfib hconn q)) s = 1 ∨
        (Classical.choose (Work.SSSR.serreE1_chainCondition
          (R := 𝕜) p e₀ hfib hconn q)) s = -1 :=
      (Classical.choose_spec (Work.SSSR.serreE1_chainCondition
        (R := 𝕜) p e₀ hfib hconn q)).1
    have hc : ∀ s : ℕ, (Classical.choose (psiSig_generator 𝕜 E B p e₀ hfib hconn)) s = 1 ∨
        (Classical.choose (psiSig_generator 𝕜 E B p e₀ hfib hconn)) s = -1 :=
      (Classical.choose_spec (psiSig_generator 𝕜 E B p e₀ hfib hconn)).1
    dsimp only
    rcases Work.SSSR.signCorr_eq_one_or_neg _ heps n with h | h <;>
      rcases hc n with h' | h' <;> rw [h, h'] <;> norm_num
  · intro q s n lam σ z hz
    rw [e1SerreIso_hom_f_apply, PsiG_genElem, PsiSig_genElem]
    rw [smul_smul]

end

end Work.Pi6.MSS
