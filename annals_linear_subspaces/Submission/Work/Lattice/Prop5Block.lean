import Mathlib
import Submission.Work.Lattice.BlockFamilyCone
import Submission.Commons.Analysis.InnerProductSpace.orthonormalBasis_self_of_finrank
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal

/-!
# Prop 5, the block step with the *canonical* directions

De Saxcé's §3 Proposition 5 extracts from a Harder–Narasimhan (tight, saturated) flag member
`V ≤ Λ` a family of lattice points of `V` whose `L`-parts dominate (`π₊`-dominance).  The
paper obtains the directions from Lemma 5; here we use instead the **canonical** directions:
an orthonormal basis

    `u : Fin r → ℝᵈ`   of   `realSpan V ⊓ modelX ℓ`,   `r = meetDim ℓ V`,

of the `L`-part of `realSpan V`.  For this choice the block-`0` norm of the wedge is *exactly*

    `‖⋀^r (modelProj ℓ) (ιMulti u)‖ = 1`,

because `modelProj ℓ` fixes each `u k ∈ modelX ℓ` and `u` is orthonormal, so the `π₊`-dominance
condition `c ≤ ‖⋀^r P (ιMulti u)‖` of `BlockFamilyCone.exists_block_family_cone` holds with
`c = 1` — hence Lemma 5 is not needed for the direction layer (only the constants in the
cone-perturbation step, `(1 - ((1+δ)^r - 1))/(1+δ)^r`, are affected, and they tend to `1`).

Everything here is *data-level*: no asymptotic (`t → ∞`) statement is proved, and no
optimality of the resulting `v` is claimed.

All declarations are sorry-free; module `Submission.Work.Lattice.Prop5Block`, namespace
`Submission.Prop5Block`.
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.Prop5Block

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
open Commons.Lattice.SuccessiveMinima

/-- The **position** of a saturated subgroup `V` of `ℝᵈ` w.r.t. the model plane `L = modelX ℓ`:
the dimension of the `L`-part of `realSpan V`.  This is the integer `ℓ_s` of de Saxcé's
Proposition 5 (the number of *contracting* directions of `V`). -/
noncomputable def meetDim (d : ℕ) (ℓ : ℕ) (V : Submodule ℤ (E d)) : ℕ :=
  Module.finrank ℝ (realSpan V ⊓ modelX (d := d) ℓ : Submodule ℝ (E d))

/-- **The canonical directions.**  There is an orthonormal family of `meetDim d ℓ V` vectors of
`ℝᵈ`, all of them lying in `modelX ℓ` and in `realSpan V`, and spanning `realSpan V ⊓ modelX ℓ`. -/
theorem exists_orthonormal_meet {d : ℕ} (ℓ : ℕ) (V : Submodule ℤ (E d)) :
    ∃ u : Fin (meetDim d ℓ V) → E d, Orthonormal ℝ u ∧
      (∀ k, u k ∈ realSpan V) ∧ (∀ k, u k ∈ modelX (d := d) ℓ) ∧
      Submodule.span ℝ (Set.range u) = realSpan V ⊓ modelX (d := d) ℓ := by
  classical
  obtain ⟨b, hbON, hbmem, hbspan⟩ :=
    Commons.Analysis.InnerProductSpace.orthonormalBasis_self_of_finrank
      (E := E d) (realSpan V ⊓ modelX (d := d) ℓ) (k := meetDim d ℓ V) rfl
  refine ⟨b, hbON, ?_, ?_, hbspan⟩
  · intro k
    exact (Submodule.mem_inf.mp (hbmem k)).1
  · intro k
    exact (Submodule.mem_inf.mp (hbmem k)).2

/-- The projection `modelProj ℓ : ℝᵈ →ₗ ℝᵈ`, regarded as a *continuous* linear map (so that it
can be fed to `BlockFamilyCone.exists_block_family_cone`). -/
noncomputable def modelProjCL (d : ℕ) (ℓ : ℕ) : E d →L[ℝ] E d :=
  LinearMap.toContinuousLinearMap (modelProj (d := d) ℓ)

@[simp] lemma modelProjCL_coe (d ℓ : ℕ) :
    ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d) = modelProj (d := d) ℓ := by
  unfold modelProjCL
  rw [LinearMap.coe_toContinuousLinearMap]

/-- `modelProj ℓ` fixes every vector of `modelX ℓ`. -/
lemma modelProj_fixes_mem {d : ℕ} (ℓ : ℕ) {x : E d} (hx : x ∈ modelX (d := d) ℓ) :
    modelProj (d := d) ℓ x = x := by
  unfold modelProj
  rw [Submission.WedgeGeneralE1.projMap_apply]
  exact Submodule.starProjection_eq_self_iff.mpr hx

/-- `modelProj ℓ` is a contraction. -/
lemma norm_modelProj_le {d : ℕ} (ℓ : ℕ) (x : E d) :
    ‖modelProj (d := d) ℓ x‖ ≤ ‖x‖ := by
  unfold modelProj
  rw [Submission.WedgeGeneralE1.projMap_apply]
  exact Submodule.norm_starProjection_apply_le (modelX (d := d) ℓ) x

/-- `modelProj ℓ` is idempotent. -/
lemma modelProj_idem {d : ℕ} (ℓ : ℕ) (x : E d) :
    modelProj (d := d) ℓ (modelProj (d := d) ℓ x) = modelProj (d := d) ℓ x := by
  apply modelProj_fixes_mem
  unfold modelProj
  rw [Submission.WedgeGeneralE1.projMap_apply]
  exact Submodule.starProjection_apply_mem (modelX (d := d) ℓ) x

/-- **The canonical directions satisfy the `π₊`-condition with constant `1`.**  For the
orthonormal family `u` of `realSpan V ⊓ modelX ℓ` (with `0 < r = meetDim d ℓ V`), the
block-`0` part of the wedge is the wedge itself, of norm `1`. -/
theorem norm_map_modelProj_iMulti_meet {d : ℕ} (ℓ : ℕ) {V : Submodule ℤ (E d)}
    (σ : Fin (meetDim d ℓ V) → E d) (hσON : Orthonormal ℝ σ)
    (hσmem : ∀ k, σ k ∈ modelX (d := d) ℓ) (hr : 0 < meetDim d ℓ V) :
    ‖exteriorPower.map (meetDim d ℓ V)
        ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
        (exteriorPower.ιMulti ℝ (meetDim d ℓ V) σ)‖ = 1 := by
  rw [modelProjCL_coe, exteriorPower.map_apply_ιMulti]
  have hcomp : (modelProj (d := d) ℓ) ∘ σ = σ := by
    funext k
    exact modelProj_fixes_mem ℓ (hσmem k)
  rw [hcomp]
  exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal σ hσON hr

/-- **Prop 5, block step with the canonical directions.**  Let `Λ ≤ ℝᵈ` be a full-rank lattice,
`V ≤ Λ` a nonzero tight saturated flag member, `r = meetDim d ℓ V > 0`, `P = modelProj ℓ` (the
orthogonal projection onto `L = modelX ℓ`, a contraction and idempotent), `M > 0`, `δ ≥ 0` with
`(1+δ)^r - 1 < 1` and the covering-radius condition `subDim V · (flagConst + ε) ≤ δ M`.  Then
there is an orthonormal family `u` of the `L`-part of `realSpan V` and a family `v` of lattice
points of `V` with `‖v k - M • u k‖ ≤ δ M` and the `π₊`-dominance
`((1 - ((1+δ)^r - 1))/(1+δ)^r) ‖⋀^r v‖ ≤ ‖π₊(⋀^r v)‖`. -/
theorem exists_block_family_cone_meet {d : ℕ} (ℓ : ℕ) (Λ V : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    (hA : 0 ≤ A) (hVΛ : V ≤ Λ) (hV0 : V ≠ ⊥)
    (hVtight : phi A V = phiPolygon Λ A (subDim V))
    {M δ ε : ℝ} (hM : 0 < M) (hε : 0 < ε) (hδ0 : 0 ≤ δ)
    (hr : 0 < meetDim d ℓ V) (hδc : (1 + δ) ^ (meetDim d ℓ V) - 1 < 1)
    (hrad : (subDim V : ℝ) *
      (((2 : ℝ) ^ (2 * d) / unitBallVol (subDim V)) *
        Real.exp ((d : ℝ) * (Kconst d + 2 * A * (d : ℝ) ^ 2)) *
        successiveMinimum (E := E d) Λ (subDim V) + ε) ≤ δ * M) :
    ∃ u : Fin (meetDim d ℓ V) → E d, Orthonormal ℝ u ∧ (∀ k, u k ∈ realSpan V) ∧
      (∀ k, u k ∈ modelX (d := d) ℓ) ∧
      ∃ v : Fin (meetDim d ℓ V) → E d, (∀ k, v k ∈ V) ∧
        (∀ k, ‖v k - M • u k‖ ≤ δ * M) ∧
        ((1 - ((1 + δ) ^ (meetDim d ℓ V) - 1)) / (1 + δ) ^ (meetDim d ℓ V)) *
            ‖exteriorPower.ιMulti ℝ (meetDim d ℓ V) v‖ ≤
          ‖blockElem (d := d) (k := meetDim d ℓ V) (ℓ := ℓ)
              (exteriorPower.ιMulti ℝ (meetDim d ℓ V) v) 0‖ := by
  classical
  obtain ⟨u, huON, huV, huL, -⟩ := exists_orthonormal_meet (d := d) ℓ V
  have hbig : (1 : ℝ) ≤ ‖exteriorPower.map (meetDim d ℓ V)
      ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
      (exteriorPower.ιMulti ℝ (meetDim d ℓ V) u)‖ := by
    rw [norm_map_modelProj_iMulti_meet ℓ u huON huL hr]
  obtain ⟨v, hvV, hvM, hvcone⟩ :=
    exists_block_family_cone (d := d) Λ V hΛfin hA hVΛ hV0 hVtight
      (modelProjCL d ℓ) (fun x => norm_modelProj_le ℓ x)
      (fun x => modelProj_idem ℓ x) hM hε hδ0 (c := 1) (by simpa using hδc) hrad
      u huON huV hbig
  refine ⟨u, huON, huV, huL, v, hvV, hvM, ?_⟩
  -- the block-0 part *is* the image under `⋀^r P`, so `hvcone` is exactly the claim
  have hblk : ‖exteriorPower.map (meetDim d ℓ V)
        ((modelProjCL d ℓ : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d)
        (exteriorPower.ιMulti ℝ (meetDim d ℓ V) v)‖ =
      ‖blockElem (d := d) (k := meetDim d ℓ V) (ℓ := ℓ)
          (exteriorPower.ιMulti ℝ (meetDim d ℓ V) v) 0‖ := by
    rw [modelProjCL_coe, blockElem_zero_eq_map_modelProj (d := d) (k := meetDim d ℓ V) (ℓ := ℓ)]
  rwa [hblk] at hvcone

end Submission.Prop5Block
