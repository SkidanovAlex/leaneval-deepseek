import Mathlib
import Submission.Work.Lattice.PositionRank
import Submission.Work.Lattice.Prop42Upper

/-!
# Prop 5's batch extraction at the annulus scale

`Prop5Assembly.exists_family_of_tight_of_bounded` extracts `k` vectors from a tight flag member
with a norm bound `‖⋀^k v‖ ≤ 2`, but its smallness hypothesis
`(subDim V)·(blockConst + ε) ≤ δ` is *not* satisfiable at a fixed scale when
`successiveMinimum Λ (subDim V)` is large (as it is for the expanding blocks of the §3 flow).
The paper (Prop 5's proof) instead takes the vectors in the annulus `[10Cλ_{j_s}, 12Cλ_{j_s}]`,
`λ_{j_s} = successiveMinimum Λ (subDim V)`.

This module performs that step: it shows that the scaled extraction applies at the scale
`M := C₀ · successiveMinimum Λ (subDim V)` with a **constant** `C₀` depending only on `d`, `A`
and the member (through `blockConst`), because `blockConst` is proportional to
`successiveMinimum Λ (subDim V)` itself.  The output is quantitative:
`‖⋀^k v‖ ≤ (C · λ_{subDim V}(Λ))^k` with `C = 2^{1/k}·C₀`, together with the `π₊`-dominance
`c‖⋀^k v‖ ≤ ‖blockElem (⋀^k v) 0‖` and `ℝ`-independence.

Module `Submission.Work.Lattice.BatchExtraction`, namespace `Submission.BatchExtraction`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.BatchExtraction

open Submission.GraysonLattice
open Submission.GraysonData
open Submission.ExteriorCoordinates
open Submission.Prop5Block
open Submission.Prop5Assembly
open Submission.WedgeBlocks
open Submission.WedgeBlockZero
open Submission.UniformBddBelow
open Submission.PositionRank
open Submission.BlockFamilyCone
open Submission.PhiSlack
open Submission.PhiPolygon
open Submission.Prop42Upper
open Commons.Lattice.SuccessiveMinima

variable {d : ℕ}

/-- A nonzero subgroup has positive rank. -/
lemma subDim_pos_of_ne_bot {V : Submodule ℤ (E d)} (hV : V ≠ ⊥) : 0 < subDim V := by
  by_contra h
  have h0 : subDim V = 0 := by omega
  have hbot : realSpan V = ⊥ := (Submodule.finrank_eq_zero).mp h0
  apply hV
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hxspan : x ∈ realSpan V := Submodule.subset_span hx
  rw [hbot] at hxspan
  simpa using hxspan

/-- The rank of a subgroup of `ℝᵈ` is at most `d`. -/
lemma subDim_le_d (V : Submodule ℤ (E d)) : subDim V ≤ d := by
  have h1 : Module.finrank ℝ ↥(realSpan V) ≤ Module.finrank ℝ (E d) := Submodule.finrank_le _
  rwa [finrank_euclideanSpace, Fintype.card_fin] at h1

/-- **The batch extraction at the annulus scale.**  From a nonzero tight saturated flag member
`V ≤ Λ` of a full-rank lattice `Λ`, and `k ≤ ℓ` with `d − ℓ + k ≤ subDim V`, one extracts `k`
`ℝ`-independent vectors of `V` with the `π₊`-dominance and the norm bound
`‖⋀^k v‖ ≤ (C·λ_{subDim V}(Λ))^k`, `C` depending only on `d`, `A` and `V`. -/
theorem exists_batch_of_tight_flagMember {ℓ : ℕ} (hℓd : ℓ ≤ d) (Λ V : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    (hA : 0 ≤ A) (hVΛ : V ≤ Λ) (hV0 : V ≠ ⊥)
    (hVtight : phi A V = phiPolygon Λ A (subDim V))
    {k : ℕ} (hk : 0 < k) (hkℓ : k ≤ ℓ) (hrank : d - ℓ + k ≤ subDim V) :
    ∃ C : ℝ, 0 < C ∧ ∃ v : Fin k → E d, (∀ i, v i ∈ V) ∧ LinearIndependent ℝ v ∧
      (∃ c : ℝ, 0 < c ∧ c * ‖exteriorPower.ιMulti ℝ k v‖ ≤
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k v) 0‖) ∧
      ‖exteriorPower.ιMulti ℝ k v‖ ≤ (C * successiveMinimum (E := E d) Λ (subDim V)) ^ k := by
  classical
  have hj0 : 0 < subDim V := subDim_pos_of_ne_bot hV0
  have hjle : subDim V ≤ d := subDim_le_d V
  have hlam : 0 < successiveMinimum (E := E d) Λ (subDim V) :=
    prSum_lambda_pos Λ hΛfin hj0 hjle
  -- the fixed tolerance `δ₀`
  set δ₀ : ℝ := ((2 : ℝ) ^ ((1 : ℝ) / (k : ℝ)) - 1) / 2 with hδ0def
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hδ0pos : 0 < δ₀ := by
    rw [hδ0def]
    have h2pos : (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / (k : ℝ)) :=
      Real.one_lt_rpow (by norm_num) (by positivity)
    linarith
  have hδ0lt : (1 + δ₀) ^ k - 1 < 1 := by
    have h1 : 1 + δ₀ < (2 : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := by
      rw [hδ0def]
      have h2pos : (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / (k : ℝ)) :=
        Real.one_lt_rpow (by norm_num) (by positivity)
      linarith
    have h2 : (1 + δ₀) ^ k < ((2 : ℝ) ^ ((1 : ℝ) / (k : ℝ))) ^ k :=
      pow_lt_pow_left₀ h1 (by linarith) hk.ne'
    have h3 : ((2 : ℝ) ^ ((1 : ℝ) / (k : ℝ))) ^ k = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [mul_one_div, hkR.ne']
    linarith
  -- the scale `M = C₀·λ` with `C₀` absorbing `blockConst/λ`
  set D : ℝ := blockConst d A Λ V / successiveMinimum (E := E d) Λ (subDim V) with hDdef
  set C₀ : ℝ := max 1 (((subDim V : ℝ) * (D + 1)) / δ₀) with hC₀def
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hblk : blockConst d A Λ V = D * successiveMinimum (E := E d) Λ (subDim V) := by
    rw [hDdef]
    field_simp
  -- the stretched smallness inequality
  have hrad0 : (subDim V : ℝ) * (blockConst d A Λ V +
      successiveMinimum (E := E d) Λ (subDim V)) ≤
      δ₀ * (C₀ * successiveMinimum (E := E d) Λ (subDim V)) := by
    rw [hblk]
    have hEq : (subDim V : ℝ) * (D * successiveMinimum (E := E d) Λ (subDim V) +
        successiveMinimum (E := E d) Λ (subDim V)) =
        ((subDim V : ℝ) * (D + 1)) * successiveMinimum (E := E d) Λ (subDim V) := by ring
    rw [hEq]
    have h2 : ((subDim V : ℝ) * (D + 1)) / δ₀ ≤ C₀ := le_max_right _ _
    have h3 : δ₀ * (((subDim V : ℝ) * (D + 1)) / δ₀) ≤ δ₀ * C₀ :=
      mul_le_mul_of_nonneg_left h2 hδ0pos.le
    have h4 : δ₀ * (((subDim V : ℝ) * (D + 1)) / δ₀) = (subDim V : ℝ) * (D + 1) := by
      field_simp
    rw [h4] at h3
    calc ((subDim V : ℝ) * (D + 1)) * successiveMinimum (E := E d) Λ (subDim V)
        ≤ (δ₀ * C₀) * successiveMinimum (E := E d) Λ (subDim V) :=
          mul_le_mul_of_nonneg_right h3 hlam.le
      _ = δ₀ * (C₀ * successiveMinimum (E := E d) Λ (subDim V)) := by ring
  have hrad : (subDim V : ℝ) * (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
        Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
        successiveMinimum (E := E d) Λ (subDim V) +
      successiveMinimum (E := E d) Λ (subDim V)) ≤
      δ₀ * (C₀ * successiveMinimum (E := E d) Λ (subDim V)) := by
    simpa only [blockConst] using hrad0
  -- the canonical directions of `V ⊓ L`
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
  -- the block extraction at scale `M`
  obtain ⟨v, hvV, hvM, hvcone⟩ :=
    exists_block_family_cone (d := d) Λ V hΛfin hA hVΛ hV0 hVtight (modelProjCL d ℓ)
      (fun x => by
        have h := norm_modelProj_le ℓ x
        simpa [modelProjCL] using h)
      (fun x => by
        simp only [modelProjCL]
        exact modelProj_idem ℓ x)
      (M := C₀ * successiveMinimum (E := E d) Λ (subDim V)) (δ := δ₀)
      (ε := successiveMinimum (E := E d) Λ (subDim V)) (mul_pos hC₀pos hlam) hlam hδ0pos.le
      (c := 1) (by simpa using hδ0lt) hrad
      σ hσON hσV (by rw [hbig])
  set M : ℝ := C₀ * successiveMinimum (E := E d) Λ (subDim V) with hMdef
  have hMpos : 0 < M := mul_pos hC₀pos hlam
  -- norms of the individual vectors
  have hvnorm : ∀ i, ‖v i‖ ≤ M * (1 + δ₀) := by
    intro i
    have h2 : ‖v i‖ ≤ ‖v i - M • σ i‖ + ‖M • σ i‖ := by
      have h3 : v i - M • σ i + M • σ i = v i := sub_add_cancel _ _
      have h4 := norm_add_le (v i - M • σ i) (M • σ i)
      rwa [h3] at h4
    have h5 : ‖M • σ i‖ = M := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hMpos, hσON.norm_eq_one, mul_one]
    linarith [hvM i, h5]
  -- independence
  have hw : ∀ i, ‖(M)⁻¹ • v i - σ i‖ ≤ δ₀ := by
    intro i
    have h1 : (M)⁻¹ • v i - σ i = (M)⁻¹ • (v i - M • σ i) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hMpos.ne', one_smul]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hMpos]
    calc (M)⁻¹ * ‖v i - M • σ i‖ ≤ (M)⁻¹ * (δ₀ * M) :=
          mul_le_mul_of_nonneg_left (by simpa [hMdef] using hvM i) (inv_nonneg.mpr hMpos.le)
      _ = δ₀ := by
        rw [mul_comm δ₀ M, ← mul_assoc, inv_mul_cancel₀ hMpos.ne', one_mul]
  have hwne : exteriorPower.ιMulti ℝ k (fun i => (M)⁻¹ • v i) ≠ 0 := by
    have hlow := Commons.Analysis.InnerProductSpace.norm_exteriorPower_map_sub_le
      (E := E d) (modelProjCL d ℓ)
      (fun x => norm_modelProj_le ℓ x) (fun x => modelProj_idem ℓ x) hδ0pos.le σ
      (fun i => (M)⁻¹ • v i) (fun i => hσON.norm_eq_one i) hw
    rw [hbig] at hlow
    have hpos2 : (0 : ℝ) < 2 - (1 + δ₀) ^ k := by linarith
    intro hzero
    rw [hzero, map_zero, norm_zero] at hlow
    linarith
  have hwedge_ne : exteriorPower.ιMulti ℝ k v ≠ 0 := by
    intro hzero
    apply hwne
    have hsm : exteriorPower.ιMulti ℝ k (fun i => (M)⁻¹ • v i) =
        ((M)⁻¹ ^ k) • exteriorPower.ιMulti ℝ k v := by
      rw [AlternatingMap.map_smul_univ]
      simp [Finset.prod_const, Finset.card_univ]
    rw [hsm, hzero, smul_zero]
  refine ⟨(2 : ℝ) ^ ((1 : ℝ) / (k : ℝ)) * C₀, by positivity, v, hvV,
    Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero v hwedge_ne, ?_, ?_⟩
  · refine ⟨(2 - (1 + δ₀) ^ k) / (1 + δ₀) ^ k, div_pos (by linarith) (by positivity), ?_⟩
    have hcc : (1 - ((1 + δ₀) ^ k - 1)) / (1 + δ₀) ^ k =
        (2 - (1 + δ₀) ^ k) / (1 + δ₀) ^ k := by ring_nf
    have hblk2 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k v) 0‖ =
        ‖exteriorPower.map k ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
          (exteriorPower.ιMulti ℝ k v)‖ := by
      rw [blockElem_zero_eq_map_modelProj (d := d) (k := k) (ℓ := ℓ), modelProjCL_coe]
    rw [hblk2, ← hcc]
    exact hvcone
  · have h2k : ((2 : ℝ) ^ ((1 : ℝ) / (k : ℝ))) ^ k = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [mul_one_div, hkR.ne']
    have hprod : ‖exteriorPower.ιMulti ℝ k v‖ ≤ (M * (1 + δ₀)) ^ k := by
      calc ‖exteriorPower.ιMulti ℝ k v‖
          ≤ ∏ i : Fin k, ‖v i‖ :=
            Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod v
        _ ≤ ∏ _i : Fin k, (M * (1 + δ₀)) :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hvnorm i)
        _ = (M * (1 + δ₀)) ^ k := by simp
    have hstep : (M * (1 + δ₀)) ^ k ≤ M ^ k * 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (by linarith [hδ0lt]) (by positivity)
    have hfinal : M ^ k * 2 = ((2 : ℝ) ^ ((1 : ℝ) / (k : ℝ)) * C₀ *
        successiveMinimum (E := E d) Λ (subDim V)) ^ k := by
      rw [hMdef]
      conv_rhs => rw [mul_assoc, mul_pow, h2k]
      ring
    linarith [hprod, hstep, le_of_eq hfinal]

end Submission.BatchExtraction

end
