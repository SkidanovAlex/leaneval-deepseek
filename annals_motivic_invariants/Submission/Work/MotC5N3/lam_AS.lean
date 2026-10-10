import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotC2.aut_functionField
import Submission.Work.MotC5N3.TwistField.asTwistFieldTrue_basic
import Submission.Work.MotT.extend_algEquiv_of_linearDisjoint
import Submission.Work.MotC5N3.Nodes.shiftOf_eq_transAlgEquiv
import Submission.Work.MotC5N3.RigAS.twistFieldTrue_sup_asRoot
import Submission.Work.MotC5N3.LamAS.asPsi
import Submission.Work.MotC5N3.LamAS.asPsi_aux
import Submission.Work.MotC5N3.LamAS.asTransport
import Submission.Work.MotC5N3.LamAS.asIota_range
import Submission.Work.MotC5N3.LamAS.asML_c2
import Submission.Work.MotC5N3.LamAS.asSigmaLift_eq_trans
import Submission.Work.MotC5N3.LamAS.asSigmaLift_comm
import Submission.Work.MotC5N3.LamAS.asF_transfer
import Submission.Work.MotC5N3.LamAS.asF_linearDisjoint
import Submission.Work.MotC5N3.LamAS.asExtendTheta
import Submission.Work.MotC5N3.LamAS.asL2_isGalois
import Submission.Work.MotC5N3.LamAS.asExtension
import Submission.Work.MotC5N3.LamAS.asCompare
import Submission.Work.MotC5N3.LamAS.root_eq_asRoot_add
import Submission.Work.MotC5N3.LamAS.CoordNe.asTwistPoint_coords_ne
import Submission.Work.MotC5N3.LamAS.FixPsi.asPsi_fixes_asF
import Submission.Work.MotC5N3.LamAS.asDefect
import Submission.Work.MotC5N3.GenAux_sigmaS_pow_five_kleinField
import Submission.Work.MotC5N3.TwistField.kleinField_eq_adjoin_genXY
import Submission.Work.MotC2.FuncExt
import Submission.Work.MotC5N3.LamAS.lamAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000

namespace Work.MotC5N3

open Work.MotC5N3.LamAS
open Work.MotC5N3.LamAS.CoordNe
open Work.MotC5N3.LamAS.FixPsi

/-- **G-LAM** (node `lam_AS` at a general base field `K`): a `K`-algebra isomorphism
`θ : asTwistFieldTrue D f₁ τ₁ σS ≃ₐ[K] asTwistFieldTrue D f₂ τ₂ σS` between the two
Artin–Schreier twist fields of the same Klein datum `D` (with `ASGood D`) gives a `K`-point `y ≠ 0`
of the twist of the Klein curve by the class `f₁ - ε f₂` for some `ε = ±1`.

This is the `RatFunc 𝕜 ↦ K` fork of `Work.MotV5.Nodes.lam_AS`
(`Submission/Work/MotV5/Nodes/lam_AS.lean`, WP4 of `MOTIVIC_CHAR5_N3_LEAD.md` §6), whose base field
is `RatFunc 𝕜`, whose twisting classes are `fAS 𝕜` and `2 • fAS 𝕜`, and whose conclusion is the
vanishing of `Work.MotK.kleinP` on `Work.MotV.asCoord (asRoot (f₁ - ε f₂)) y`; here `K` is an
arbitrary `𝕜`-algebra field of characteristic `5`, `f₁, f₂ ∈ K` are arbitrary classes and the twist
fields are the generic `Work.MotC5N3.asTwistFieldTrue` of `Submission/Work/MotC5N3/Defs.lean`.
Both reviewers checked that the source chain is genuinely parametric in the twisting classes and in
the base field: `Work.MotV5.Nodes.exists_y_of_asRoot_mem` (the step extracting `y` from the
isomorphism) is already generic, as are `Work.MotC2.aut_functionField` and the `LamAS` tower
linear-disjointness results, and the unported middle files listed below only need the mechanical
`RatFunc 𝕜 ↦ K` substitution.

Route: fork into namespace `Work.MotC5N3` the module chain of the source —
`Submission/Work/MotV5/Alpha/CoeffAct.lean`, `Alpha/TwistTransport.lean`, `AsTwCoordAt.lean`,
`asCoord_asTwCoord.lean`, `GenAux_relfinrank_bot_adjoin_genX.lean`,
`GenAux_sigmaS_ne_one_on_kleinField.lean`, `LamAS/asML_c2.lean`, `LamAS/asPsi_aux.lean`,
`LamAS/asTransport.lean`, `LamAS/asSigmaLift_comm.lean`, `LamAS/asSigmaLift_eq_trans.lean`,
`LamAS/asExtendTheta.lean`, `LamAS/asExtension.lean`, `LamAS/asCompare.lean`,
`LamAS/asDefect.lean`, `LamAS/lamExtraction.lean`, `LamAS/coeffOm_conj_shiftOf.lean`,
`LamAS/exists_coeffAlgHom_induced.lean`, `CoordNe/asTwistPoint_coords_ne.lean`,
`FixPsi/asPsi_fixes_asF.lean`, `Nodes/lam_AS.lean` — replacing `RatFunc 𝕜` by `K`,
`Work.MotV.Kb 𝕜` by `Work.MotC5N3.KbA K`, `Work.MotV.Om D` by `Work.MotC5N3.OmA K D`,
`Work.MotV5.asTwistFieldTrue/asTwistAction/asFieldL/asRoot/ASTwistData` by their `Work.MotC5N3`
counterparts; `Work.MotV.asCoord` keeps its shape (it takes the root and the vector as arguments).
The files already forked under `Submission/Work/MotC5N3/{TwistField,LamAS,RigAS}/` (by the WP1 and
WP3 children) are the model for naming and layout, and `Submission/Work/MotC5N3/port.py` performs
the textual port.  No new hypothesis is needed beyond the ones displayed (unlike
`constantsOnly_K_AS`, the bundle `ASTwistData` carries `h5L`/`hneL`/`hpres`).

Deliverable: namespace `Work.MotC5N3`, file `Submission/Work/MotC5N3/lam_AS.lean` plus forked
support, sorry-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).  The result is
consumed by `Work.MotC5N3.rigidity_AS_val_of_lam` (`Submission/Work/MotC5N3/CharFive.lean`), whose
`LamASStatement` is this statement verbatim. -/
theorem lam_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ : K)
    (τ₁ τ₂ : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (σ₁ σ₂ : Work.MotC5N3.KbA K ≃ₐ[K] Work.MotC5N3.KbA K)
    (h1 : Work.MotC5N3.ASTwistData 𝕜 D f₁ τ₁ σS σ₁)
    (h2 : Work.MotC5N3.ASTwistData 𝕜 D f₂ τ₂ σS σ₂)
    (θ : ↥(Work.MotC5N3.asTwistFieldTrue D f₁ τ₁ σS) ≃ₐ[K]
      ↥(Work.MotC5N3.asTwistFieldTrue D f₂ τ₂ σS)) :
    ∃ (ε : ℤ) (_ : ε = 1 ∨ ε = -1) (y : Fin 5 → K), y ≠ 0 ∧
      ∀ k, Work.MotK.kleinP (algebraMap 𝕜 (Work.MotC5N3.KbA K) D.a)
        (algebraMap 𝕜 (Work.MotC5N3.KbA K) D.b)
        (Work.MotV.asCoord (Work.MotC5N3.asRoot (f₁ - algebraMap 𝕜 K ((ε : ℤ) : 𝕜) * f₂))
          (fun j => algebraMap K (Work.MotC5N3.KbA K) (y j))) k = 0 := by

  classical
  haveI hDec : DecidableEq ↥(asL2 f₁ f₂) := Classical.decEq _
  haveI hGal : IsGalois (K) ↥(asL2 f₁ f₂) := (asL2_isGalois K f₁ f₂).1
  haveI hFin : FiniteDimensional (K) ↥(asL2 f₁ f₂) := (asL2_isGalois K f₁ f₂).2
  haveI hEllD : D.E.IsElliptic := hD.1.elliptic
  haveI hEll : (asE2 D f₁ f₂).IsElliptic :=
    inferInstanceAs ((D.E.map (algebraMap 𝕜 ↥(asL2 f₁ f₂))).IsElliptic)
  have hRange := asIota_range 𝕜 D hD f₁ f₂
  have hσSΩ := sigmaS_mem_Omega D hD.1 f₁ f₂ σS h1.hσS
  obtain ⟨σS', hσS', -⟩ := asSigmaLift_ext D hD f₁ f₂ σS hRange hσSΩ
    (sigmaS_pow_five_eq_one D hD σS h1.hσS)
  have hcomm := asSigmaLift_comm 𝕜 D hD f₁ f₂ σS h1.hσS σS' hσS'
  -- ### the two Artin–Schreier roots
  set W₁ : ↥(asL2 f₁ f₂) :=
    ⟨Work.MotC5N3.asRoot f₁, asRoot_mem_asL2_left f₁ f₂⟩ with hW₁def
  set W₂ : ↥(asL2 f₁ f₂) :=
    ⟨Work.MotC5N3.asRoot f₂, asRoot_mem_asL2_right f₁ f₂⟩ with hW₂def
  have hW₁ : W₁ ^ 5 - W₁ = algebraMap (K) ↥(asL2 f₁ f₂) f₁ := by
    apply Subtype.ext
    change (W₁ : Work.MotC5N3.KbA K) ^ 5 - (W₁ : Work.MotC5N3.KbA K) = _
    rw [hW₁def, Work.MotC5N3.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (K) ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K) f₁
  have hW₂ : W₂ ^ 5 - W₂ = algebraMap (K) ↥(asL2 f₁ f₂) f₂ := by
    apply Subtype.ext
    change (W₂ : Work.MotC5N3.KbA K) ^ 5 - (W₂ : Work.MotC5N3.KbA K) = _
    rw [hW₂def, Work.MotC5N3.asRoot_spec]
    exact IsScalarTower.algebraMap_apply (K) ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K) f₂
  -- ### the extension of `θ`
  obtain ⟨hF1, hsup1, -⟩ := asF_transfer 𝕜 D hD f₁ f₂ f₁ τ₁ σS σ₁ h1 (Or.inl rfl) hRange
  obtain ⟨hF2, hsup2, -⟩ := asF_transfer 𝕜 D hD f₁ f₂ f₂ τ₂ σS σ₂ h2 (Or.inr rfl) hRange
  have hLI1 := asF_linearDisjoint 𝕜 D hD f₁ f₂ f₁ τ₁ σS σ₁ h1 (Or.inl rfl)
  have hLI2 := asF_linearDisjoint 𝕜 D hD f₁ f₂ f₂ τ₂ σS σ₂ h2 (Or.inr rfl)
  obtain ⟨Θ, hΘext⟩ := asExtendTheta 𝕜 D hD f₁ f₂ τ₁ τ₂ σS hF1 hF2 hLI1 hLI2 hsup1 hsup2 θ
  have hΘmem : ∀ x ∈ asF D f₁ f₂ f₁ τ₁ σS, Θ x ∈ asF D f₁ f₂ f₂ τ₂ σS := by
    intro x hx
    show asIota D f₁ f₂ (Θ x) ∈ Work.MotC5N3.asTwistFieldTrue D f₂ τ₂ σS
    rw [hΘext ⟨x, hx⟩ hx]
    exact (θ ⟨asIota D f₁ f₂ x, hx⟩).2
  -- ### node C2 over `L`
  obtain ⟨Q, ε₂, hQε⟩ := asML_c2 𝕜 D hD f₁ f₂ Θ
  obtain ⟨T, hσS'T, hT5, hTne⟩ := asSigmaLift_eq_trans 𝕜 D hD f₁ f₂ σS h1.hσS σS' hσS'
  -- ### the twisted Galois actions
  have hfix₁ : ∀ γ, ∀ x ∈ asF D f₁ f₂ f₁ τ₁ σS, asPsi D f₁ f₂ f₁ σS' W₁ hW₁ γ x = x :=
    fun γ => asPsi_fixes_asF 𝕜 D hD f₁ f₂ f₁ τ₁ σS σ₁ h1 (Or.inl rfl) hRange σS' hσS'
      hcomm W₁ hW₁ γ
  have hfix₂ : ∀ γ, ∀ x ∈ asF D f₁ f₂ f₂ τ₂ σS, asPsi D f₁ f₂ f₂ σS' W₂ hW₂ γ x = x :=
    fun γ => asPsi_fixes_asF 𝕜 D hD f₁ f₂ f₂ τ₂ σS σ₂ h2 (Or.inr rfl) hRange σS' hσS'
      hcomm W₂ hW₂ γ
  have hcomp : ∀ γ, Θ.restrictScalars (K) * (asPsi D f₁ f₂ f₁ σS' W₁ hW₁ γ) =
      (asPsi D f₁ f₂ f₂ σS' W₂ hW₂ γ) * Θ.restrictScalars (K) :=
    fun γ => asCompare 𝕜 D hD f₁ f₂ f₁ f₂ τ₁ τ₂ σS σS' W₁ W₂ hW₁ hW₂ γ Θ hΘmem hsup1
      (hfix₁ γ) (hfix₂ γ)
  have hdefect : ∀ γ, WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
        (F := ↥(asL2 f₁ f₂)) (K := ↥(asL2 f₁ f₂))
        (γ.restrictScalars 𝕜).toAlgHom Q - Q =
      ((-1 : ℤ) ^ (ε₂ : ℕ) * ((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) -
        ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T :=
    fun γ => asDefect 𝕜 D hD f₁ f₂ f₁ f₂ τ₁ τ₂ σS σS' W₁ W₂ hW₁ hW₂ ε₂ Q T hσS'T Θ hQε
      hcomp γ
  -- ### the twist property of `T`
  have hQshift : ∃ lam : Work.MotC2.Func (D.E.baseChange ↥(asL2 f₁ f₂)), lam ≠ 0 ∧
      ∀ i : Fin 5, Work.MotC2.transAlgEquiv (D.E.baseChange ↥(asL2 f₁ f₂)) T
        (Work.MotV.kleinCoord D ↥(asL2 f₁ f₂) i) =
          lam * Work.MotV.kleinCoord D ↥(asL2 f₁ f₂) (i + 1) := by
    obtain ⟨lam0, hlam0ne, hlam0⟩ := h1.hσS
    have hκ1 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 1 ≠ 0 := by
      intro h1'
      have h := hlam0 0
      rw [show (0 : Fin 5) + 1 = 1 from rfl, h1', mul_zero] at h
      exact hD.1.coord0_ne (Work.MotC5N3.KbA K) (σS.injective (by rw [h, map_zero]))
    have hκ0r : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 ∈ (asIota D f₁ f₂).fieldRange := by
      rw [← asIota_kleinCoord D f₁ f₂ 0]
      exact AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩
    have hκ1r : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 1 ∈ (asIota D f₁ f₂).fieldRange := by
      rw [← asIota_kleinCoord D f₁ f₂ 1]
      exact AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩
    have hσSκ0 : σS (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) ∈ (asIota D f₁ f₂).fieldRange := by
      rw [hRange]
      refine hσSΩ _ ?_
      rw [← asIota_kleinCoord D f₁ f₂ 0, ← hRange]
      exact AlgHom.mem_fieldRange.mpr ⟨_, rfl⟩
    have hlam : lam0 = σS (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) *
        (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 1)⁻¹ := by
      rw [hlam0 0]
      rw [show (0 : Fin 5) + 1 = 1 from rfl]
      field_simp
    have hmem : lam0 ∈ (asIota D f₁ f₂).fieldRange := by
      rw [hlam]
      exact mul_mem hσSκ0 (inv_mem hκ1r)
    obtain ⟨lam, hlam'⟩ := AlgHom.mem_fieldRange.mp hmem
    refine ⟨lam, ?_, ?_⟩
    · intro h0
      rw [h0, map_zero] at hlam'
      exact hlam0ne hlam'.symm
    · intro i
      apply asIota_injective D f₁ f₂
      rw [← hσS'T]
      calc asIota D f₁ f₂ (σS' (Work.MotV.kleinCoord D ↥(asL2 f₁ f₂) i))
          = σS (asIota D f₁ f₂ (Work.MotV.kleinCoord D ↥(asL2 f₁ f₂) i)) :=
            hσS' _
        _ = σS (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i) := by rw [asIota_kleinCoord]
        _ = lam0 * Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) (i + 1) := hlam0 i
        _ = asIota D f₁ f₂ (lam * Work.MotV.kleinCoord D ↥(asL2 f₁ f₂) (i + 1)) := by
            rw [map_mul, asIota_kleinCoord, hlam']
  -- ### the two branches of node C2
  have hmapQ : ∀ γ : ↥(asL2 f₁ f₂) ≃ₐ[K] ↥(asL2 f₁ f₂),
      WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
          (F := ↥(asL2 f₁ f₂)) (K := ↥(asL2 f₁ f₂)) γ.toAlgHom Q
        = WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
          (F := ↥(asL2 f₁ f₂)) (K := ↥(asL2 f₁ f₂))
          (γ.restrictScalars 𝕜).toAlgHom Q := fun γ => rfl
  have hε01 : ε₂ = 0 ∨ ε₂ = 1 := by fin_cases ε₂ <;> simp
  rcases hε01 with hε | hε
  · -- #### ε₂ = 0 : the class is `f₁ - f₂`
    have hpow : (-1 : ℤ) ^ (ε₂ : ℕ) = 1 := by rw [hε]; norm_num
    have hcf : (⟨Work.MotC5N3.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ : ↥(asL2 f₁ f₂)) ^ 5
        - ⟨Work.MotC5N3.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩
        = algebraMap (K) ↥(asL2 f₁ f₂) (f₁ - f₂) := by
      apply Subtype.ext
      change (Work.MotC5N3.asRoot (f₁ - f₂) : Work.MotC5N3.KbA K) ^ 5
        - (Work.MotC5N3.asRoot (f₁ - f₂) : Work.MotC5N3.KbA K) = _
      rw [Work.MotC5N3.asRoot_spec]
      exact IsScalarTower.algebraMap_apply (K) ↥(asL2 f₁ f₂)
        (Work.MotC5N3.KbA K) (f₁ - f₂)
    let d : (↥(asL2 f₁ f₂) ≃ₐ[K] ↥(asL2 f₁ f₂)) → Fin 5 :=
      fun γ => asShift D f₁ f₂ (f₁ - f₂) ⟨Work.MotC5N3.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ hcf γ
    have hd : ∀ γ, γ ⟨Work.MotC5N3.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩
        = ⟨Work.MotC5N3.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩
          + algebraMap ℤ ↥(asL2 f₁ f₂) (((d γ : Fin 5) : ℤ)) :=
      fun γ => asShift_spec D f₁ f₂ (f₁ - f₂)
        ⟨Work.MotC5N3.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ hcf γ
    have hdef0 : ∀ γ, WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
          (F := ↥(asL2 f₁ f₂)) (K := ↥(asL2 f₁ f₂))
          (γ.restrictScalars 𝕜).toAlgHom Q - Q =
        (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) -
          ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T := by
      intro γ
      have h := hdefect γ
      rw [hpow] at h
      simpa using h
    by_cases hQ0 : Q = 0
    · -- the trivial class
      have hd0 : ∀ γ, d γ = 0 := by
        intro γ
        have h := hdef0 γ
        rw [hQ0, WeierstrassCurve.Affine.Point.map_zero, sub_zero] at h
        have hz : (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) -
            ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T = 0 := h.symm
        have hdvd := five_dvd_of_zsmul_eq_zero hT5 hTne hz
        have hcast : algebraMap ℤ ↥(asL2 f₁ f₂) (((d γ : Fin 5) : ℤ))
            = algebraMap ℤ ↥(asL2 f₁ f₂)
              (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) -
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) := by
          rw [asShift_sub_eq D f₁ f₂ W₁ W₂
            ⟨Work.MotC5N3.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ hW₁ hW₂ hcf γ, map_sub]
        have hzero : algebraMap ℤ ↥(asL2 f₁ f₂) (((d γ : Fin 5) : ℤ)) = 0 := by
          rw [hcast]
          obtain ⟨c, hc⟩ := hdvd
          rw [hc, map_mul]
          have h5z : algebraMap ℤ ↥(asL2 f₁ f₂) (5 : ℤ) = 0 := by
            rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, map_natCast, CharP.cast_eq_zero]
          rw [h5z, zero_mul]
        have hdvd2 : (5 : ℤ) ∣ ((d γ : Fin 5) : ℤ) :=
          (CharP.intCast_eq_zero_iff ↥(asL2 f₁ f₂) 5 _).mp hzero
        obtain ⟨c, hc⟩ := hdvd2
        exact Fin.ext (by have := (d γ).isLt; omega)
      have hfixed : ∀ γ : ↥(asL2 f₁ f₂) ≃ₐ[K] ↥(asL2 f₁ f₂),
          γ ⟨Work.MotC5N3.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩
            = ⟨Work.MotC5N3.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ := by
        intro γ
        rw [hd γ, hd0 γ]
        simp
      obtain ⟨W, hW⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
        (⟨Work.MotC5N3.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ :
          ↥(asL2 f₁ f₂))).mpr hfixed
      have hWas : algebraMap (K) (Work.MotC5N3.KbA K) W = Work.MotC5N3.asRoot (f₁ - f₂) := by
        have h := congrArg (algebraMap ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K)) hW
        rw [← IsScalarTower.algebraMap_apply (K) ↥(asL2 f₁ f₂)
          (Work.MotC5N3.KbA K) W] at h
        exact h
      obtain ⟨y, hyne, hyk⟩ := exists_y_of_asRoot_mem 𝕜 D
        (fun ha => hD.1.ab_ne (by rw [ha, zero_mul])) (fun hb => hD.1.ab_ne (by rw [hb, mul_zero]))
        (f₁ - f₂) W hWas
      refine ⟨1, Or.inl rfl, y, hyne, fun k => ?_⟩
      have hpar : f₁ - algebraMap 𝕜 (K) ((1 : ℤ) : 𝕜) * f₂ = f₁ - f₂ := by simp
      rw [hpar]
      exact hyk k
    · -- the non-degenerate case: extract the Klein point of `C^AS_{f₁-f₂}`
      have hR : ∀ γ, WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
          (F := ↥(asL2 f₁ f₂)) (K := ↥(asL2 f₁ f₂)) γ.toAlgHom Q
          = Q + ((d γ : ℕ) • T) := by
        intro γ
        have h := hdef0 γ
        rw [← hmapQ γ] at h
        have hcast : algebraMap ℤ ↥(asL2 f₁ f₂) (((d γ : Fin 5) : ℤ))
            = algebraMap ℤ ↥(asL2 f₁ f₂)
              (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) -
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) := by
          rw [asShift_sub_eq D f₁ f₂ W₁ W₂
            ⟨Work.MotC5N3.asRoot (f₁ - f₂), asRoot_sub_mem f₁ f₂⟩ hW₁ hW₂ hcf γ, map_sub]
        have hsmul := smul_eq_of_intCast_eq hcast T hT5
        rw [sub_eq_iff_eq_add] at h
        rw [add_comm] at h
        rw [h, ← hsmul, natCast_zsmul]
      obtain ⟨y, hyne, hyk⟩ := Work.MotC5N3.LamAS.CoordNe.asTwistPoint_coords_ne D hD (f₁ - f₂)
        (asL2 f₁ f₂) (asRoot_sub_mem f₁ f₂) T Q hQ0 hQshift d hd hR
      refine ⟨1, Or.inl rfl, y, hyne, fun k => ?_⟩
      have hpar : f₁ - algebraMap 𝕜 (K) ((1 : ℤ) : 𝕜) * f₂ = f₁ - f₂ := by simp
      rw [hpar]
      exact hyk k
  · -- #### ε₂ = 1 : the class is `f₁ + f₂`
    have hpow : (-1 : ℤ) ^ (ε₂ : ℕ) = -1 := by rw [hε]; norm_num
    have hca : (⟨Work.MotC5N3.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ : ↥(asL2 f₁ f₂)) ^ 5
        - ⟨Work.MotC5N3.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩
        = algebraMap (K) ↥(asL2 f₁ f₂) (f₁ + f₂) := by
      apply Subtype.ext
      change (Work.MotC5N3.asRoot (f₁ + f₂) : Work.MotC5N3.KbA K) ^ 5
        - (Work.MotC5N3.asRoot (f₁ + f₂) : Work.MotC5N3.KbA K) = _
      rw [Work.MotC5N3.asRoot_spec]
      exact IsScalarTower.algebraMap_apply (K) ↥(asL2 f₁ f₂)
        (Work.MotC5N3.KbA K) (f₁ + f₂)
    let d : (↥(asL2 f₁ f₂) ≃ₐ[K] ↥(asL2 f₁ f₂)) → Fin 5 :=
      fun γ => asShift D f₁ f₂ (f₁ + f₂) ⟨Work.MotC5N3.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ hca γ
    have hd : ∀ γ, γ ⟨Work.MotC5N3.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩
        = ⟨Work.MotC5N3.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩
          + algebraMap ℤ ↥(asL2 f₁ f₂) (((d γ : Fin 5) : ℤ)) :=
      fun γ => asShift_spec D f₁ f₂ (f₁ + f₂)
        ⟨Work.MotC5N3.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ hca γ
    have hdef1 : ∀ γ, WeierstrassCurve.Affine.Point.map (W' := D.E) (S := 𝕜)
          (F := ↥(asL2 f₁ f₂)) (K := ↥(asL2 f₁ f₂))
          (γ.restrictScalars 𝕜).toAlgHom Q - Q =
        (-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
          ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T := by
      intro γ
      have h := hdefect γ
      rw [hpow] at h
      simpa using h
    by_cases hQ0 : Q = 0
    · -- the trivial class
      have hd0 : ∀ γ, d γ = 0 := by
        intro γ
        have h := hdef1 γ
        rw [hQ0, WeierstrassCurve.Affine.Point.map_zero, sub_zero] at h
        have hz : (-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
            ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T = 0 := h.symm
        have hdvd := five_dvd_of_zsmul_eq_zero hT5 hTne hz
        have hz0 : algebraMap ℤ ↥(asL2 f₁ f₂)
            (-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
              ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) = 0 := by
          obtain ⟨c, hc⟩ := hdvd
          rw [hc, map_mul]
          have h5z : algebraMap ℤ ↥(asL2 f₁ f₂) (5 : ℤ) = 0 := by
            rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, map_natCast, CharP.cast_eq_zero]
          rw [h5z, zero_mul]
        have hsum : algebraMap ℤ ↥(asL2 f₁ f₂)
            (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) +
              ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) = 0 := by
          have hneg : algebraMap ℤ ↥(asL2 f₁ f₂)
              (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) +
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ))
              = -algebraMap ℤ ↥(asL2 f₁ f₂)
                (-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
                  ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) := by
            rw [map_add, map_sub, map_neg]
            first | refl_ring1 | ring
          rw [hneg, hz0, neg_zero]
        have hcast : algebraMap ℤ ↥(asL2 f₁ f₂) (((d γ : Fin 5) : ℤ))
            = algebraMap ℤ ↥(asL2 f₁ f₂)
              (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) +
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) := by
          rw [asShift_add_eq D f₁ f₂ W₁ W₂
            ⟨Work.MotC5N3.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ hW₁ hW₂ hca γ]
          exact (map_add (algebraMap ℤ ↥(asL2 f₁ f₂))
            (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ))
            (((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ))).symm
        have hzero : algebraMap ℤ ↥(asL2 f₁ f₂) (((d γ : Fin 5) : ℤ)) = 0 := by
          rw [hcast, hsum]
        have hdvd2 : (5 : ℤ) ∣ ((d γ : Fin 5) : ℤ) :=
          (CharP.intCast_eq_zero_iff ↥(asL2 f₁ f₂) 5 _).mp hzero
        obtain ⟨c, hc⟩ := hdvd2
        exact Fin.ext (by have := (d γ).isLt; omega)
      have hfixed : ∀ γ : ↥(asL2 f₁ f₂) ≃ₐ[K] ↥(asL2 f₁ f₂),
          γ ⟨Work.MotC5N3.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩
            = ⟨Work.MotC5N3.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ := by
        intro γ
        rw [hd γ, hd0 γ]
        simp
      obtain ⟨W, hW⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
        (⟨Work.MotC5N3.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ :
          ↥(asL2 f₁ f₂))).mpr hfixed
      have hWas : algebraMap (K) (Work.MotC5N3.KbA K) W = Work.MotC5N3.asRoot (f₁ + f₂) := by
        have h := congrArg (algebraMap ↥(asL2 f₁ f₂) (Work.MotC5N3.KbA K)) hW
        rw [← IsScalarTower.algebraMap_apply (K) ↥(asL2 f₁ f₂)
          (Work.MotC5N3.KbA K) W] at h
        exact h
      obtain ⟨y, hyne, hyk⟩ := exists_y_of_asRoot_mem 𝕜 D
        (fun ha => hD.1.ab_ne (by rw [ha, zero_mul])) (fun hb => hD.1.ab_ne (by rw [hb, mul_zero]))
        (f₁ + f₂) W hWas
      refine ⟨-1, Or.inr rfl, y, hyne, fun k => ?_⟩
      have hpar : f₁ - algebraMap 𝕜 (K) (((-1 : ℤ)) : 𝕜) * f₂ = f₁ + f₂ := by simp
      rw [hpar]
      exact hyk k
    · -- the non-degenerate case
      have hR : ∀ γ, WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
          (F := ↥(asL2 f₁ f₂)) (K := ↥(asL2 f₁ f₂)) γ.toAlgHom (-Q)
          = -Q + ((d γ : ℕ) • T) := by
        intro γ
        have h := hdef1 γ
        rw [← hmapQ γ] at h
        have hcast : algebraMap ℤ ↥(asL2 f₁ f₂) (((d γ : Fin 5) : ℤ))
            = algebraMap ℤ ↥(asL2 f₁ f₂)
              (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) +
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) := by
          rw [asShift_add_eq D f₁ f₂ W₁ W₂
            ⟨Work.MotC5N3.asRoot (f₁ + f₂), asRoot_add_mem f₁ f₂⟩ hW₁ hW₂ hca γ]
          exact (map_add (algebraMap ℤ ↥(asL2 f₁ f₂))
            (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ))
            (((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ))).symm
        have hsmul := smul_eq_of_intCast_eq hcast T hT5
        have hz' : -(-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
              ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ))
            = ((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) +
              ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ) := by ring
        rw [sub_eq_iff_eq_add] at h
        calc WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
              (F := ↥(asL2 f₁ f₂)) (K := ↥(asL2 f₁ f₂)) γ.toAlgHom (-Q)
            = -WeierstrassCurve.Affine.Point.map (W' := D.E) (S := K)
              (F := ↥(asL2 f₁ f₂)) (K := ↥(asL2 f₁ f₂)) γ.toAlgHom Q :=
                map_neg _ _
          _ = -(Q + (-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T) := by rw [h, add_comm]
          _ = -Q + (-(-(((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ)) -
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ))) • T := by
                rw [neg_add, neg_zsmul]
          _ = -Q + (((asShift D f₁ f₂ f₁ W₁ hW₁ γ : Fin 5) : ℤ) +
                ((asShift D f₁ f₂ f₂ W₂ hW₂ γ : Fin 5) : ℤ)) • T := by rw [hz']
          _ = -Q + ((d γ : Fin 5) : ℤ) • T := by rw [← hsmul]
          _ = -Q + (d γ : ℕ) • T := by rw [natCast_zsmul]
      obtain ⟨y, hyne, hyk⟩ := Work.MotC5N3.LamAS.CoordNe.asTwistPoint_coords_ne D hD (f₁ + f₂)
        (asL2 f₁ f₂) (asRoot_add_mem f₁ f₂) T (-Q)
        (fun h0 => hQ0 (neg_eq_zero.mp h0)) hQshift d hd hR
      refine ⟨-1, Or.inr rfl, y, hyne, fun k => ?_⟩
      have hpar : f₁ - algebraMap 𝕜 (K) (((-1 : ℤ)) : 𝕜) * f₂ = f₁ + f₂ := by simp
      rw [hpar]
      exact hyk k



end Work.MotC5N3
