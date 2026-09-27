import Mathlib
import Submission.Work.Mostow.euclid_block_normal_form
import Submission.Work.Mostow.conj_fundamentalDomain
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.geeBlkAdaptLtDim
import Submission.Work.Mostow.geeSVblkRotN
import Submission.Work.Mostow.geeSVblkCastEq
import Submission.Work.Mostow.nrmStdMulAndRotNConj
import Submission.Work.Mostow.margulisPairDefs
import Submission.Work.Mostow.blk_hom
import Submission.Work.Mostow.ellipticAux
import Submission.Work.Mostow.rotCanonAux

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-!
# Adapting the standard stratum to the fixed stratum of a block isometry

If `b = blk k m 1 S ∈ Λ`, `2 ≤ k`, `1 ≤ m`, `0 < rotN S` and `S` has a *nonzero fixed vector*,
then `S` has a fixed space of dimension `r ≥ 1`, and the normal form of `S` exhibits `b` as a
block isometry with tangential dimension `k + r` and normal dimension `m - r < m` whose normal
part is fixed-point free, after conjugation by the normal coordinate change.

The two elementary ingredients proved here are
* `vblk_zero_eq'` : for the split at `0`, `vblk 0 _ R` is `R`;
* `one_le_vblkDim` : a nonzero fixed vector of `S` forces `1 ≤ r` in the normal form.
-/

/-- For the split at `0`, the value-split block map `vblk 0 _ R` is `R`. -/
lemma vblk_zero_eq' {m : ℕ} (hk : 0 ≤ m) (R : E (m - 0) ≃ₗᵢ[ℝ] E (m - 0)) (y : E m) :
    vblk 0 hk R y = R y := by
  apply WithLp.ofLp_injective
  funext i
  rw [vblk_ofLp_of_ge 0 hk R y i (Nat.not_lt_zero i.val)]
  have htail : tailOf 0 y = y := by
    apply WithLp.ofLp_injective
    funext j
    rw [tailOf_ofLp]
    exact congrArg y (Fin.ext (by simp))
  rw [htail]
  exact congrArg (fun i' : Fin (m - 0) => (R y).ofLp i') (Fin.ext (by simp))

/-- If `S` has a nonzero fixed vector and is, up to conjugation by `PS`, the value-split block
map `vblk r hr RS` with `RS` fixed-point free, then `1 ≤ r` (the fixed block is nontrivial). -/
lemma one_le_vblkDim {m : ℕ} {S : E m ≃ₗᵢ[ℝ] E m} (hnfv : ∃ w : E m, S w = w ∧ w ≠ 0)
    {r : ℕ} (hr : r ≤ m) (RS : E (m - r) ≃ₗᵢ[ℝ] E (m - r)) (PS : E m ≃ₗᵢ[ℝ] E m)
    (hRSfree : ∀ w : E (m - r), RS w = w → w = 0)
    (hPS : ∀ u : E m, PS (S (PS.symm u)) = vblk r hr RS u) : 1 ≤ r := by
  by_contra h
  have hr0 : r = 0 := by omega
  subst hr0
  obtain ⟨w, hw, hwne⟩ := hnfv
  have hPSw : PS w ≠ 0 := by
    intro h0
    refine hwne (PS.injective ?_)
    simp [h0]
  have h1 : vblk 0 hr RS (PS w) = PS w := by
    have h := hPS (PS w)
    rw [LinearIsometryEquiv.symm_apply_apply, hw] at h
    exact h.symm
  have h2 : RS (PS w) = PS w := by
    rw [← vblk_zero_eq' hr RS (PS w)]
    exact h1
  exact hPSw (hRSfree (PS w) h2)

theorem adaptFixedStratum (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) (hA : ∀ i : ℕ, 1 ≤ i → Submission.Mostow.POActionProp i) (hI : ∀ i : ℕ, 1 ≤ i → Submission.Mostow.HypIsometryProp i) : ∀ (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (k + m) 1)) (D : Set (Submission.Mostow.E (k + m))) (S : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m), _root_.IsDiscrete (Λ : Set (LeanEval.Geometry.MostowRigidity.PO (k + m) 1)) → MeasureTheory.IsFundamentalDomain Λ D (Submission.Mostow.volH (k + m)) → Submission.Mostow.blk k m 1 S ∈ Λ → 0 < Submission.Mostow.rotN S → (∃ w : Submission.Mostow.E m, S w = w ∧ w ≠ 0) → ∃ (j' m' : ℕ) (hj'm' : j' + m' = k + m) (Λ' : Subgroup (LeanEval.Geometry.MostowRigidity.PO (k + m) 1)) (D' : Set (Submission.Mostow.E (k + m))) (R' : Submission.Mostow.E m' ≃ₗᵢ[ℝ] Submission.Mostow.E m'), 2 ≤ j' ∧ 1 ≤ m' ∧ m' < m ∧ _root_.IsDiscrete (Λ' : Set (LeanEval.Geometry.MostowRigidity.PO (k + m) 1)) ∧ MeasureTheory.IsFundamentalDomain Λ' D' (Submission.Mostow.volH (k + m)) ∧ Submission.Mostow.volH (k + m) D' = Submission.Mostow.volH (k + m) D ∧ (hj'm' ▸ Submission.Mostow.blk j' m' 1 R' : LeanEval.Geometry.MostowRigidity.PO (k + m) 1) ∈ Λ' ∧ (∀ w : Submission.Mostow.E m', R' w = w → w = 0) ∧ Submission.Mostow.rotN R' ≤ Submission.Mostow.rotN S := by
  intro Λ D S hdisc hD hb hS hnfv
  classical
  have hAkm : POActionProp (k + m) := hA (k + m) (by omega)
  have hIkm : HypIsometryProp (k + m) := hI (k + m) (by omega)
  have hAk : POActionProp k := hA k (by omega)
  have hIk : HypIsometryProp k := hI k (by omega)
  have hP := POBasic.ofProp hAkm
  -- Euclidean block normal form of `S`
  obtain ⟨r, hr, RS, PS, hRSfree, hPS⟩ := euclid_block_normal_form m S
  have hrpos : 1 ≤ r := one_le_vblkDim hnfv hr RS PS hRSfree hPS
  have hrlt : r < m := geeBlkAdaptLtDim m r hr S RS PS hPS hS
  have eeq : (k + r) + (m - r) = k + m := by omega
  set RB : E m ≃ₗᵢ[ℝ] E m := PS * S * PS⁻¹ with hRBdef
  have hRB : ∀ u : E m, RB u = vblk r hr RS u := by
    intro u
    have h2 : RB u = PS (S (PS.symm u)) := by
      rw [hRBdef,
        show (PS⁻¹ : E m ≃ₗᵢ[ℝ] E m) = PS.symm from LinearIsometryEquiv.inv_def PS]
      simp
    rw [h2]; exact hPS u
  have hrotRB : rotN RB = rotN S := by
    rw [hRBdef]; exact rhd_rotN_conj PS S
  have hRSleS : rotN RS ≤ rotN S := (geeSVblkRotN m r hr RS RB hRB).trans_eq hrotRB
  have hcast : (eeq ▸ (blk (k + r) (m - r) 1 RS : PO ((k + r) + (m - r)) 1) : PO (k + m) 1)
      = (blk k m 1 RB : PO (k + m) 1) := geeSVblkCastEq k m r hr eeq RB RS hRB
  set Th : PO (k + m) 1 := blk k m 1 PS with hTdef
  have hhom := blk_hom k m hAk hIk hAkm hIkm
  have hThinv : Th⁻¹ = blk k m 1 PS⁻¹ := by
    rw [hTdef]
    refine inv_eq_of_mul_eq_one_right ?_
    have h := hhom.1 1 1 PS PS⁻¹
    rw [one_mul, mul_inv_cancel, hhom.2.1] at h
    exact h.symm
  have hblkmul : Th * blk k m 1 S * Th⁻¹ = blk k m 1 RB := by
    rw [hRBdef, hTdef, hThinv]
    rw [show blk k m 1 PS * blk k m 1 S = blk k m 1 (PS * S) from by
          rw [← hhom.1 1 1 PS S]; simp]
    rw [show blk k m 1 (PS * S) * blk k m 1 PS⁻¹ = blk k m 1 (PS * S * PS⁻¹) from by
          rw [← hhom.1 1 1 (PS * S) PS⁻¹]; simp]
  have hconj : Th * blk k m 1 S * Th⁻¹
      = (eeq ▸ (blk (k + r) (m - r) 1 RS : PO ((k + r) + (m - r)) 1) : PO (k + m) 1) := by
    rw [hcast]; exact hblkmul
  have hdisc' : IsDiscrete ((Λ.map (MulAut.conj Th).toMonoidHom : Subgroup (PO (k + m) 1)) :
      Set (PO (k + m) 1)) := by
    simpa using isDiscrete_map_conj (Γ := Λ) hdisc Th⁻¹
  have hFD := conj_fundamentalDomain (k + m) hAkm hIkm Λ D hD Th
  have hmpT : MeasurePreserving (fun u : E (k + m) => Th⁻¹ • u) (volH (k + m)) (volH (k + m)) :=
    hIkm.2.2.2.2.2.2.2.2.2.2.2.1 Th⁻¹
  have hvol : volH (k + m) ((fun u : E (k + m) => Th • u) '' D) = volH (k + m) D := by
    have himg : (fun u : E (k + m) => Th • u) '' D
        = (fun u : E (k + m) => Th⁻¹ • u) ⁻¹' D := by
      ext x; constructor
      · rintro ⟨d, hd, rfl⟩
        show Th⁻¹ • (Th • d) ∈ D
        rw [← hP.mul_smul, inv_mul_cancel, hP.one_smul]; exact hd
      · intro hx
        exact ⟨Th⁻¹ • x, hx, by
          show Th • (Th⁻¹ • x) = x
          rw [← hP.mul_smul, mul_inv_cancel, hP.one_smul]⟩
    rw [himg]
    exact hmpT.measure_preimage hD.nullMeasurableSet
  refine ⟨k + r, m - r, eeq, Λ.map (MulAut.conj Th).toMonoidHom,
    (fun u : E (k + m) => Th • u) '' D, RS, by omega, by omega, by omega, hdisc', hFD, hvol,
    ?_, hRSfree, hRSleS⟩
  exact Subgroup.mem_map.mpr
    ⟨blk k m 1 S, hb, (MulAut.conj_apply Th (blk k m 1 S)).trans hconj⟩

end

end Work.Mostow
