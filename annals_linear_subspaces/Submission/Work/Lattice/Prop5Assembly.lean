import Mathlib
import Submission.Work.Lattice.Prop5Block
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Commons.Analysis.InnerProductSpace.norm_exteriorPower_map_sub_le
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero

/-!
# Prop 5: the per-block output in the form the final assembly needs

`Submission.Prop5Block.exists_block_family_cone_meet` produces, from a tight saturated flag
member `V ≤ Λ` of position `r = meetDim d ℓ V`, a family of `r` lattice points of `V` close to
`M` times an orthonormal family of the `L`-part of `V`, with the `π₊`-dominance
`((1 - ((1+δ)^r - 1))/(1+δ)^r) · ‖⋀^r v‖ ≤ ‖blockElem (⋀^r v) 0‖`.

Here we record the **normalised form** used by the assembly (constant `M = 1`, i.e. `v` within
`δ` of the orthonormal directions), which turns the block output into a *rational* (once pushed
through the flow) `k`-plane of **bounded height** with **independent** directions and a positive
`π₊`-dominance constant:

* `norm_map_modelProj_iMulti_of_mem` — for any orthonormal family `σ : Fin k → ℝᵈ` with
  `σ i ∈ modelX ℓ`, `k > 0`: `‖⋀^k (modelProj ℓ) (ιMulti σ)‖ = 1`
  (the general form of `Prop5Block.norm_map_modelProj_iMulti_meet`);
* `exists_family_of_tight_of_bounded` — if `k ≤ ℓ`, the position of `V` is `≥ k`, and the
  *ambient* successive minimum of `Λ` at rank `subDim V` is small enough that
  `(subDim V) · (C(V,ε) + ε) < 2^(1/k) − 1` (where `C(V,ε)` is the covering constant of
  `BlockFamilyCone.exists_block_family_cone`), then there are `k` points `v i ∈ V` which are
  `ℝ`-independent, with `‖⋀^k v‖ ≤ 2`, `c·‖⋀^k v‖ ≤ ‖blockElem (⋀^k v) 0‖` for the explicit
  positive constant `c = (2 − (1+δ)^k)/(1+δ)^k`, `δ = (subDim V)·(C(V,ε) + ε)`.

All declarations are sorry-free; module `Submission.Work.Lattice.Prop5Assembly`, namespace
`Submission.Prop5Assembly`.
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Submission.Prop5Assembly

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.WedgeBlocks
open Submission.WedgeBlockZero
open Submission.ExteriorCoordinates
open Submission.BlockFamilyCone
open Submission.PhiSlack
open Submission.PhiPolygon
open Submission.Prop42Upper
open Submission.UniformBddBelow
open Submission.Prop5Block
open Commons.Lattice.SuccessiveMinima
open Commons.Analysis.InnerProductSpace
open Commons.LinearAlgebra.ExteriorPower

/-- The covering-radius constant of a tight flag member `V` of `Λ`, as it appears in the
hypothesis `hrad` of `BlockFamilyCone.exists_block_family_cone`
(note: `subDim` of `V`, unlike `BlockFamilyCone.flagConst`, which uses `subDim Λ`). -/
noncomputable def blockConst {d : ℕ} (d' : ℕ) (A : ℝ) (Λ V : Submodule ℤ (E d)) : ℝ :=
  ((2 : ℝ) ^ (2 * d') / unitBallVol (subDim V)) *
    Real.exp ((d' : ℝ) * (Kconst d' + 2 * A * (d' : ℝ) ^ 2)) *
    successiveMinimum (E := E d) Λ (subDim V)

/-- **The `π₊`-condition for an arbitrary orthonormal family inside `modelX ℓ`.**  If `σ : Fin k → ℝᵈ`
is orthonormal, `k > 0` and every `σ i` lies in `modelX ℓ`, then the block-`0` part of the wedge
is the wedge itself and has norm `1`. -/
theorem norm_map_modelProj_iMulti_of_mem {d k ℓ : ℕ} (hk : 0 < k) (σ : Fin k → E d)
    (hσ : Orthonormal ℝ σ) (hmem : ∀ i, σ i ∈ modelX (d := d) ℓ) :
    ‖exteriorPower.map k ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
        (exteriorPower.ιMulti ℝ k σ)‖ = 1 := by
  rw [modelProjCL_coe, exteriorPower.map_apply_ιMulti]
  have hcomp : (modelProj (d := d) ℓ) ∘ σ = σ := by
    funext i
    exact modelProj_fixes_mem ℓ (hmem i)
  rw [hcomp]
  exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal σ hσ hk

/-- **Prop 5, per-flag-member assembly.**  Let `V ≤ Λ` be a nonzero tight saturated flag member
of a full-rank lattice `Λ ≤ ℝᵈ`, let `k ≤ ℓ` with `k ≤ meetDim d ℓ V` (the position of `V` is at
least `k`), and suppose the *ambient* successive minimum of `Λ` at rank `subDim V` is small
enough: there is `ε > 0` with `(subDim V)·(blockConst d A Λ V + ε) < 2^(1/k) − 1`.

Then there are `k` points `v i ∈ V` which are `ℝ`-independent, with `‖⋀^k v‖ ≤ 2` and
`c·‖⋀^k v‖ ≤ ‖blockElem (⋀^k v) 0‖` for `c := (2 − (1+δ)^k)/(1+δ)^k > 0`,
`δ := (subDim V)·(blockConst d A Λ V + ε)`. -/
theorem exists_family_of_tight_of_bounded {d ℓ : ℕ} (hℓd : ℓ ≤ d) (Λ V : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    (hA : 0 ≤ A) (hVΛ : V ≤ Λ) (hV0 : V ≠ ⊥)
    (hVtight : phi A V = phiPolygon Λ A (subDim V))
    {k : ℕ} (hk : 0 < k) (hkℓ : k ≤ ℓ) (hpos : k ≤ meetDim d ℓ V)
    (hsmall : ∃ δ ε : ℝ, 0 < ε ∧ 0 ≤ δ ∧ δ < 2 ^ ((1 : ℝ) / (k : ℝ)) - 1 ∧
      (subDim V : ℝ) * (blockConst d A Λ V + ε) ≤ δ) :
    ∃ v : Fin k → E d, (∀ i, v i ∈ V) ∧ LinearIndependent ℝ v ∧
      ‖exteriorPower.ιMulti ℝ k v‖ ≤ 2 ∧
      ∃ c : ℝ, 0 < c ∧ c * ‖exteriorPower.ιMulti ℝ k v‖ ≤
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k v) 0‖ := by
  classical
  obtain ⟨δ, ε, hε, hδ0, hsmallδ, hrad⟩ := hsmall
  -- the canonical directions of `V`, restricted to `k` of them
  obtain ⟨u, huON, huV, huL, -⟩ := exists_orthonormal_meet (d := d) ℓ V
  let σ : Fin k → E d := fun i => u (Fin.castLE hpos i)
  have hσON : Orthonormal ℝ σ := huON.comp (Fin.castLE hpos) (Fin.castLE_injective hpos)
  have hσL : ∀ i, σ i ∈ modelX (d := d) ℓ := fun i => huL _
  have hσV : ∀ i, σ i ∈ realSpan V := fun i => huV _
  have hbig : (1 : ℝ) ≤ ‖exteriorPower.map k
      ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
      (exteriorPower.ιMulti ℝ k σ)‖ := by
    rw [norm_map_modelProj_iMulti_of_mem hk σ hσON hσL]
  have hδc : (1 + δ) ^ k - 1 < 1 := by
    have h1 : 1 + δ < (2 : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := by linarith
    have hpow : (1 + δ) ^ k < ((2 : ℝ) ^ ((1 : ℝ) / (k : ℝ))) ^ k :=
      pow_lt_pow_left₀ h1 (by linarith) (by omega : k ≠ 0)
    have hR : ((2 : ℝ) ^ ((1 : ℝ) / (k : ℝ))) ^ k = 2 := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / (k : ℝ))) k]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have h : ((1 : ℝ) / (k : ℝ)) * ((k : ℕ) : ℝ) = 1 := by
        field_simp
      rw [h, Real.rpow_one]
    rw [hR] at hpow
    linarith
  -- the block step (`BlockFamilyCone.exists_block_family_cone` with `P = modelProj ℓ`, `c = 1`)
  obtain ⟨v, hvV, hvM, hvcone⟩ :=
    exists_block_family_cone (d := d) Λ V hΛfin hA hVΛ hV0 hVtight
      (modelProjCL d ℓ)
      (fun x => by
        have h := norm_modelProj_le ℓ x
        simpa [modelProjCL] using h)
      (fun x => by
        simp only [modelProjCL]
        exact modelProj_idem ℓ x)
      (M := 1) (δ := δ) (ε := ε) one_pos hε hδ0 (c := 1) (by simpa using hδc)
      (by rw [mul_one]; exact hrad) σ hσON hσV hbig
  have hv1 : ∀ i, ‖v i - σ i‖ ≤ δ := by
    intro i
    simpa using hvM i
  have hvnorm : ∀ i, ‖v i‖ ≤ 1 + δ := by
    intro i
    have h2 : ‖v i‖ ≤ ‖v i - σ i‖ + ‖σ i‖ := by
      have := norm_add_le (v i - σ i) (σ i)
      have h3 : v i - σ i + σ i = v i := sub_add_cancel _ _
      rw [h3] at this
      exact this
    have h4 : ‖σ i‖ = 1 := hσON.norm_eq_one i
    linarith [hv1 i]
  -- `π₊(⋀^k v) ≠ 0`, hence the family is independent
  have hpos_cone : 0 < ‖exteriorPower.map k
      ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
      (exteriorPower.ιMulti ℝ k v)‖ := by
    have hlow := norm_exteriorPower_map_sub_le (E := E d) (modelProjCL d ℓ)
      (fun x => norm_modelProj_le ℓ x) (fun x => modelProj_idem ℓ x) hδ0 σ v
      (fun i => hσON.norm_eq_one i) hv1
    rw [norm_map_modelProj_iMulti_of_mem hk σ hσON hσL] at hlow
    have : (0 : ℝ) < 2 - (1 + δ) ^ k := by linarith
    linarith
  have hwedge_ne : exteriorPower.ιMulti ℝ k v ≠ 0 := by
    intro h0
    have h1 : exteriorPower.map k
        ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
        (exteriorPower.ιMulti ℝ k v) = 0 := by
      rw [h0, map_zero]
    rw [h1, norm_zero] at hpos_cone
    exact lt_irrefl _ hpos_cone
  refine ⟨v, hvV, iMulti_linearIndependent_of_ne_zero v hwedge_ne, ?_, ?_⟩
  · calc ‖exteriorPower.ιMulti ℝ k v‖
        ≤ ∏ i : Fin k, ‖v i‖ := exteriorPower_norm_wedge_le_prod v
      _ ≤ ∏ _i : Fin k, (1 + δ) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hvnorm i)
      _ = (1 + δ) ^ k := by simp
      _ ≤ 2 := by linarith [hδc]
  · have hcc : (1 - ((1 + δ) ^ k - 1)) / (1 + δ) ^ k = (2 - (1 + δ) ^ k) / (1 + δ) ^ k := by
      ring_nf
    refine ⟨(2 - (1 + δ) ^ k) / (1 + δ) ^ k, div_pos (by linarith) (by positivity), ?_⟩
    have hblk : ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k v) 0‖ =
        ‖exteriorPower.map k ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
          (exteriorPower.ιMulti ℝ k v)‖ := by
      rw [blockElem_zero_eq_map_modelProj (d := d) (k := k) (ℓ := ℓ), modelProjCL_coe]
    rw [hblk, ← hcc]
    exact hvcone

end Submission.Prop5Assembly
