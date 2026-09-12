import Mathlib
import Submission.Work.Lattice.Prop5Assembly
import Submission.GeometryOfNumbers.PlaneFinrank

/-!
# The position of a saturated subgroup, and the scaled `Prop 5` extraction

Two small but useful additions to the §3 toolchain.

1. **The position is automatically at least the generic value.**  For a subgroup `V` of rank `j`
   the dimension formula gives `dim (realSpan V ⊓ L) ≥ j + ℓ − d` — no tightness needed.  Hence the
   hypothesis `k ≤ meetDim d ℓ V` of `Prop5Assembly.exists_family_of_tight_of_bounded` is
   *automatic* for any flag member of rank `j ≥ d − ℓ + k`; the binding hypothesis of that lemma
   is the *smallness* `(subDim V)·(blockConst + ε) ≤ δ` (i.e. `λ_{subDim V}(Λ) ≲ 1`).

2. **The scaled extraction.**  `exists_family_of_tight_of_scaled` is the version of
   `Prop5Assembly.exists_family_of_tight_of_bounded` with a general scale `M > 0` in the covering
   step: the extracted vectors then have `‖⋀^k v‖ ≤ (M(1+δ))^k` instead of `≤ 2`.  This is the
   form needed by the multi-member Prop-5 induction, where the vectors extracted at the flag member
   `V_{j_s}` have norms `≍ λ_{j_s}(Λ_t)` (large), and the *product* is controlled by the polygon
   accounting rather than by a fixed bound.

All declarations are sorry-free; module `Submission.Work.Lattice.PositionRank`, namespace
`Submission.PositionRank`.
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.PositionRank

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.WedgeBlocks
open Submission.WedgeBlockZero
open Submission.ExteriorCoordinates
open Submission.Prop5Block
open Submission.BlockFamilyCone
open Submission.Prop5Assembly
open Submission.PhiSlack
open Submission.PhiPolygon
open Submission.Prop42Upper
open Submission.UniformBddBelow
open Commons.Lattice.SuccessiveMinima
open Commons.Analysis.InnerProductSpace
open Commons.LinearAlgebra.ExteriorPower

/-- **The position of a subgroup is at least the generic value** `subDim V + ℓ − d`. -/
theorem meetDim_ge {d ℓ : ℕ} (hℓd : ℓ ≤ d) (V : Submodule ℤ (E d)) :
    subDim V + ℓ - d ≤ meetDim d ℓ V := by
  have hsup : Module.finrank ℝ ↥(realSpan V ⊔ modelX (d := d) ℓ : Submodule ℝ (E d)) ≤ d := by
    have h1 : Module.finrank ℝ ↥(realSpan V ⊔ modelX (d := d) ℓ : Submodule ℝ (E d)) ≤
        Module.finrank ℝ (E d) := Submodule.finrank_le _
    rwa [finrank_euclideanSpace, Fintype.card_fin] at h1
  have hL : Module.finrank ℝ ↥(modelX (d := d) ℓ) = ℓ :=
    Submission.PlaneFinrank.finrank_modelX (d := d) ℓ hℓd
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (realSpan V)
    (modelX (d := d) ℓ : Submodule ℝ (E d))
  have hsum : Module.finrank ℝ ↥(realSpan V) + ℓ ≤
      Module.finrank ℝ ↥(realSpan V ⊓ modelX (d := d) ℓ) + d := by
    calc Module.finrank ℝ ↥(realSpan V) + ℓ
        = Module.finrank ℝ ↥(realSpan V) + Module.finrank ℝ ↥(modelX (d := d) ℓ) := by rw [hL]
      _ = Module.finrank ℝ ↥(realSpan V ⊔ modelX (d := d) ℓ : Submodule ℝ (E d)) +
            Module.finrank ℝ ↥(realSpan V ⊓ modelX (d := d) ℓ) := hdim.symm
      _ = Module.finrank ℝ ↥(realSpan V ⊓ modelX (d := d) ℓ) +
            Module.finrank ℝ ↥(realSpan V ⊔ modelX (d := d) ℓ : Submodule ℝ (E d)) := by ring
      _ ≤ Module.finrank ℝ ↥(realSpan V ⊓ modelX (d := d) ℓ) + d :=
            Nat.add_le_add_left hsup _
  have hsd : subDim V = Module.finrank ℝ ↥(realSpan V) := rfl
  rw [meetDim, hsd]
  exact Nat.sub_le_iff_le_add.mpr hsum

/-- Consequence: a flag member of rank `j ≥ d − ℓ + k` has position at least `k`. -/
theorem meetDim_ge_of_rank {d ℓ : ℕ} (hℓd : ℓ ≤ d) {V : Submodule ℤ (E d)} {k : ℕ}
    (hrank : d - ℓ + k ≤ subDim V) : k ≤ meetDim d ℓ V := by
  have h1 := meetDim_ge (d := d) (ℓ := ℓ) hℓd V
  omega

/-- **The scaled `Prop 5` extraction.**  Same as
`Prop5Assembly.exists_family_of_tight_of_bounded` but with a general covering scale `M > 0`
(and with the position hypothesis replaced by the rank condition `d − ℓ + k ≤ subDim V`). -/
theorem exists_family_of_tight_of_scaled {d ℓ : ℕ} (hℓd : ℓ ≤ d) (Λ V : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    (hA : 0 ≤ A) (hVΛ : V ≤ Λ) (hV0 : V ≠ ⊥)
    (hVtight : phi A V = phiPolygon Λ A (subDim V))
    {k : ℕ} (hk : 0 < k) (_hkℓ : k ≤ ℓ) (hrank : d - ℓ + k ≤ subDim V)
    {M : ℝ} (hM : 0 < M)
    (hsmall : ∃ δ ε : ℝ, 0 < ε ∧ 0 ≤ δ ∧ (1 + δ) ^ k - 1 < 1 ∧
      (subDim V : ℝ) * (blockConst d A Λ V + ε) ≤ δ * M) :
    ∃ (δ : ℝ) (v : Fin k → E d), 0 ≤ δ ∧ (∀ i, v i ∈ V) ∧ LinearIndependent ℝ v ∧
      ‖exteriorPower.ιMulti ℝ k v‖ ≤ (M * (1 + δ)) ^ k ∧
      ∃ c : ℝ, 0 < c ∧ c * ‖exteriorPower.ιMulti ℝ k v‖ ≤
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k v) 0‖ := by
  classical
  obtain ⟨δ, ε, hε, hδ0, hsmallδ, hrad⟩ := hsmall
  have hpos : k ≤ meetDim d ℓ V := meetDim_ge_of_rank (d := d) (ℓ := ℓ) hℓd hrank
  obtain ⟨u, huON, huV, huL, -⟩ := exists_orthonormal_meet (d := d) ℓ V
  let σ : Fin k → E d := fun i => u (Fin.castLE hpos i)
  have hσON : Orthonormal ℝ σ := huON.comp (Fin.castLE hpos) (Fin.castLE_injective hpos)
  have hσL : ∀ i, σ i ∈ modelX (d := d) ℓ := fun i => huL _
  have hσV : ∀ i, σ i ∈ realSpan V := fun i => huV _
  have hbig : ‖exteriorPower.map k
      ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
      (exteriorPower.ιMulti ℝ k σ)‖ = 1 :=
    norm_map_modelProj_iMulti_of_mem hk σ hσON hσL
  have hδc : (1 + δ) ^ k - 1 < 1 := hsmallδ
  have hvpow : (1 + δ) ^ k < 2 := by linarith
  obtain ⟨v, hvV, hvM, hvcone⟩ :=
    exists_block_family_cone (d := d) Λ V hΛfin hA hVΛ hV0 hVtight
      (modelProjCL d ℓ)
      (fun x => by
        have h := norm_modelProj_le ℓ x
        simpa [modelProjCL] using h)
      (fun x => by
        simp only [modelProjCL]
        exact modelProj_idem ℓ x)
      (M := M) (δ := δ) (ε := ε) hM hε hδ0 (c := 1) (by simpa using hδc)
      hrad σ hσON hσV (by rw [hbig])
  have hvnorm : ∀ i, ‖v i‖ ≤ M * (1 + δ) := by
    intro i
    have h2 : ‖v i‖ ≤ ‖v i - M • σ i‖ + ‖M • σ i‖ := by
      have h3 : v i - M • σ i + M • σ i = v i := sub_add_cancel _ _
      have h4 := norm_add_le (v i - M • σ i) (M • σ i)
      rwa [h3] at h4
    have h5 : ‖M • σ i‖ = M := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hM, hσON.norm_eq_one, mul_one]
    linarith [hvM i, h5]
  -- independence: normalise the scale away and use the cone perturbation at unit scale
  have hw : ∀ i, ‖(M)⁻¹ • v i - σ i‖ ≤ δ := by
    intro i
    have h1 : (M)⁻¹ • v i - σ i = (M)⁻¹ • (v i - M • σ i) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hM.ne', one_smul]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hM]
    calc (M)⁻¹ * ‖v i - M • σ i‖ ≤ (M)⁻¹ * (δ * M) :=
          mul_le_mul_of_nonneg_left (hvM i) (inv_nonneg.mpr hM.le)
      _ = δ := by
        rw [mul_comm δ M, ← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul]
  have hwne : exteriorPower.ιMulti ℝ k (fun i => (M)⁻¹ • v i) ≠ 0 := by
    have hlow := norm_exteriorPower_map_sub_le (E := E d) (modelProjCL d ℓ)
      (fun x => norm_modelProj_le ℓ x) (fun x => modelProj_idem ℓ x) hδ0 σ
      (fun i => (M)⁻¹ • v i) (fun i => hσON.norm_eq_one i) hw
    rw [hbig] at hlow
    have hpos2 : (0 : ℝ) < 2 - (1 + δ) ^ k := by linarith
    intro hzero
    rw [hzero, map_zero, norm_zero] at hlow
    linarith
  have hwedge_ne : exteriorPower.ιMulti ℝ k v ≠ 0 := by
    intro hzero
    apply hwne
    have : (fun i => (M)⁻¹ • v i) = fun i => (M)⁻¹ • (v i) := rfl
    rw [show exteriorPower.ιMulti ℝ k (fun i => (M)⁻¹ • v i) =
        ((M)⁻¹ ^ k) • exteriorPower.ιMulti ℝ k v from by
      rw [AlternatingMap.map_smul_univ]; simp [Finset.prod_const, Finset.card_univ]]
    rw [hzero, smul_zero]
  refine ⟨δ, v, hδ0, hvV, iMulti_linearIndependent_of_ne_zero v hwedge_ne, ?_, ?_⟩
  · calc ‖exteriorPower.ιMulti ℝ k v‖
        ≤ ∏ i : Fin k, ‖v i‖ := exteriorPower_norm_wedge_le_prod v
      _ ≤ ∏ _i : Fin k, (M * (1 + δ)) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hvnorm i)
      _ = (M * (1 + δ)) ^ k := by simp
  · have hcc : (1 - ((1 + δ) ^ k - 1)) / (1 + δ) ^ k = (2 - (1 + δ) ^ k) / (1 + δ) ^ k := by
      ring_nf
    refine ⟨(2 - (1 + δ) ^ k) / (1 + δ) ^ k, div_pos (by linarith) (by positivity), ?_⟩
    have hblk : ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k v) 0‖ =
        ‖exteriorPower.map k ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
          (exteriorPower.ιMulti ℝ k v)‖ := by
      rw [blockElem_zero_eq_map_modelProj (d := d) (k := k) (ℓ := ℓ), modelProjCL_coe]
    rw [hblk, ← hcc]
    exact hvcone

end Submission.PositionRank

end
