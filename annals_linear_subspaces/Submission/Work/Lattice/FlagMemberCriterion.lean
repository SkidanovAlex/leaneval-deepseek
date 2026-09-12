import Mathlib
import Submission.Work.Lattice.FlowLatticeImage
import Submission.Work.Lattice.MaxPhiFlag

/-!
# The flag of the §3 lattice, and the data/polygon identifications

`MaxPhiFlag.exists_tight_flag` produces the max-norm Harder–Narasimhan flag of a full-rank
lattice `Λ_t` at the angular ranks of its slacked polygon `maxphiPolygon Λ_t A`.  For the §3
extraction one needs the flag of `Λ_t = a_t s_x ℤᵈ`, and the translation of the two tightness
inputs into the vocabulary of `Submission.MaxPhiAccounting`'s flow data/polygon:

* `eEquiv ℓ t` — the flowed automorphism as a `LinearEquiv` (with `eEquiv_coe`);
* `phiPolygonT_eq_maxphiPolygon_imageSpan` — the flow polygon of `Λ₀ = imageSpan g` at time `t` is
  the intrinsic slacked polygon of `imageSpan (g.trans (eEquiv ℓ t))`;
* `blockStart_phiPolygonT_eq` / `numBlocks_phiPolygonT_eq` — the angular ranks agree;
* **`phiPolygonT_tight_at_flagRank`** — at the angular ranks of the flow polygon the polygon is
  *tight*: `phiPolygonT t (jb s) = phiData t (jb s)` (the `htight` input of
  `TangentCriterion.effPos_le_of_tangent`).

Module `Submission.Work.Lattice.FlagMemberCriterion`, namespace `Submission.FlagMemberCriterion`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real Filter
open scoped BigOperators Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Submission.FlagMemberCriterion

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.MaxNorm
open Submission.MaxNormPolygon
open Submission.FlowRateAsymptotic
open Submission.FlowDataMax
open Submission.ImageLattice
open Submission.MaxPhiPolygon
open Submission.MaxPhiFlag
open Submission.MaxPhi
open Submission.MaxRankData
open Submission.AngularRanks
open Submission.FlowLattice
open Submission.FlowLatticeImage
open Submission.TangentCriterion
open Submission.MaxPhiAccounting
open Submission.AngularTightness
open Submission.ActiveBlock
open Submission.MaxCovol
open Submission.LatticePolygon
open Submission.GraysonLattice
open Submission.AccountingOneSided

variable {d : ℕ}

/-- The exponential two-scale flow as a linear equivalence. -/
noncomputable def eEquiv (ℓ : ℕ) (t : ℝ) : RD d ≃ₗ[ℝ] RD d :=
  scaleMapEquiv (d := d) (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ
    (Real.exp_ne_zero _) (Real.exp_ne_zero _)

/-- The coefficients of `eEquiv` are those of the flow map. -/
lemma eEquiv_coe (ℓ : ℕ) (t : ℝ) :
    (eEquiv (d := d) ℓ t : RD d →ₗ[ℝ] RD d) = eFlow (d := d) ℓ t := by
  rw [eEquiv, eFlow_eq_scaleMapEquiv]

/-! ## The flow polygon is the intrinsic polygon of the flowed lattice -/

/-- **The flow polygon of `imageSpan g` at time `t` is the intrinsic slacked polygon of
`imageSpan (g.trans (eEquiv ℓ t))`.** -/
theorem phiPolygonT_eq_maxphiPolygon_imageSpan (g : RD d ≃ₗ[ℝ] RD d) (ℓ : ℕ) (t : ℝ) (A : ℝ)
    (i : ℕ) :
    phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t i =
      maxphiPolygon (d := d) (imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t))) A i := by
  have heq : (imageSpan (d := d) g).map ((eFlow (d := d) ℓ t).restrictScalars ℤ) =
      imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t)) := by
    rw [eEquiv, imageSpan_map_eq]
  have hfin : Module.finrank ℤ
      ((imageSpan (d := d) g).map ((eFlow (d := d) ℓ t).restrictScalars ℤ)) = d := by
    rw [heq]; exact finrank_imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t))
  have h := phiPolygonT_eq_maxphiPolygon (d := d) (imageSpan (d := d) g) ℓ A t hfin i
  rw [heq] at h
  exact h

/-- The angular ranks of the flow polygon and of the intrinsic polygon agree. -/
theorem blockStart_phiPolygonT_eq (g : RD d ≃ₗ[ℝ] RD d) (ℓ : ℕ) (t : ℝ) (A : ℝ) (s : ℕ) :
    blockStart d (phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t) s =
      blockStart d (maxphiPolygon (d := d) (imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t)))
        A) s :=
  (blockStart_congr (fun i _ => phiPolygonT_eq_maxphiPolygon_imageSpan (d := d) g ℓ t A i)) s

/-- The number of blocks of the flow polygon and of the intrinsic polygon agree. -/
theorem numBlocks_phiPolygonT_eq (g : RD d ≃ₗ[ℝ] RD d) (ℓ : ℕ) (t : ℝ) (A : ℝ) :
    numBlocks d (phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t) =
      numBlocks d (maxphiPolygon (d := d)
        (imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t))) A) :=
  (numBlocks_congr (fun i _ => phiPolygonT_eq_maxphiPolygon_imageSpan (d := d) g ℓ t A i))

/-- **Tightness of the flow polygon at its angular ranks.** -/
theorem phiPolygonT_tight_at_flagRank (g : RD d ≃ₗ[ℝ] RD d) (ℓ : ℕ) (t : ℝ) (A : ℝ) {s : ℕ}
    (hs1 : 1 ≤ s) (hsN : s < numBlocks d (phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t)) :
    phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t
        (blockStart d (phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t) s) =
      phiData (d := d) (imageSpan (d := d) g) ℓ A t
        (blockStart d (phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t) s) := by
  set H : Submodule ℤ (RD d) := imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t)) with hH
  have hfin : Module.finrank ℤ H = d := by
    rw [hH]; exact finrank_imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t))
  have hN : s < numBlocks d (maxphiPolygon (d := d) H A) := by
    rw [hH, ← numBlocks_phiPolygonT_eq (d := d) g ℓ t A]
    exact hsN
  have htight := maxphiPolygon_eq_data_at_angular H hfin A hs1 hN
  -- the angular ranks agree
  have hbs : blockStart d (phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t) s =
      blockStart d (maxphiPolygon (d := d) H A) s :=
    blockStart_phiPolygonT_eq (d := d) g ℓ t A s
  -- side conditions for the data identity
  have hk1 : 1 ≤ blockStart d (maxphiPolygon (d := d) H A) s :=
    le_trans hs1 (blockStart_n_ge d (maxphiPolygon (d := d) H A) s
      (le_trans (Nat.le_of_lt hN) (numBlocks_le (maxphiPolygon (d := d) H A))))
  have hkd : blockStart d (maxphiPolygon (d := d) H A) s ≤ d :=
    blockStart_le_d d (maxphiPolygon (d := d) H A) s
  rw [hbs]
  rw [phiPolygonT_eq_maxphiPolygon_imageSpan (d := d) g ℓ t A
      (blockStart d (maxphiPolygon (d := d) H A) s)]
  rw [phiData_eq_maxphiData (d := d) (imageSpan (d := d) g) ℓ A hk1 hkd]
  rw [show (imageSpan (d := d) g).map ((eFlow (d := d) ℓ t).restrictScalars ℤ) = H from by
    rw [hH, eEquiv, imageSpan_map_eq]]
  exact htight

/-! ## The data is attained by the flag member -/

/-- **A tight flag member attains the rank data, and its presentation family has a preimage in
`Λ₀ = imageSpan g` whose level function realises the data at every time.**

This is the `hatt` input of `TangentCriterion.effPos_le_of_tangent`. -/
theorem exists_preimage_of_tight {ℓ : ℕ} (g : RD d ≃ₗ[ℝ] RD d) (t : ℝ)
    (A : ℝ) {V : Submodule ℤ (RD d)}
    (hVΛ : V ≤ imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t)))
    (hV0 : V ≠ ⊥) (hV1 : 1 ≤ subDim V)
    (hVtight : maxPhi (d := d) (imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t)))
        (finrank_imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t))) A V hVΛ =
      maxphiData (d := d) (imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t))) A (subDim V)) :
    ∃ w : Fin (subDim V) → RD d, (∀ i, w i ∈ imageSpan (d := d) g) ∧
      LinearIndependent ℝ w ∧
      maxData (d := d) (imageSpan (d := d) g) ℓ t (subDim V) =
        flowLevel (d := d) ℓ (subDim_le_ambient V) (exteriorPower.ιMulti ℝ (subDim V) w) t ∧
      Submodule.span ℝ (Set.range (fun i => eFlow (d := d) ℓ t (w i))) = realSpan V := by
  classical
  set H : Submodule ℤ (RD d) := imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t)) with hH
  set M : Submodule ℤ (RD d) :=
    (imageSpan (d := d) g).map ((eFlow (d := d) ℓ t).restrictScalars ℤ) with hM
  have hMH : H = M := by rw [hH, hM, eEquiv, imageSpan_map_eq]
  have hfin : Module.finrank ℤ H = d := by
    rw [hH]; exact finrank_imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t))
  have hkd : subDim V ≤ d := subDim_le_ambient V
  -- the covolume of the tight member equals the rank data
  have hcov : maxCovol (d := d) H hfin V hVΛ = maxRankData (d := d) H (subDim V) hkd := by
    have h := hVtight
    rw [maxPhi, maxphiData, dif_pos hkd] at h
    linarith
  -- the preimage family
  have hpre : ∀ i : Fin (subDim V), ∃ x ∈ imageSpan (d := d) g,
      eFlow (d := d) ℓ t x = (presFam (d := d) H hfin V hVΛ hV0 i : RD d) := by
    intro i
    have hmem : (presFam (d := d) H hfin V hVΛ hV0 i : RD d) ∈ H :=
      presFam_mem (d := d) (Λ := H) (hΛfin := hfin) (X := V) (hXΛ := hVΛ) (hX0 := hV0) i
    have hmem' : (presFam (d := d) H hfin V hVΛ hV0 i : RD d) ∈ M := by
      rw [← hMH]; exact hmem
    exact Submodule.mem_map.mp hmem'
  choose w hwmem hweq using hpre
  have hli' : LinearIndependent ℝ (fun i => eFlow (d := d) ℓ t (w i)) := by
    rw [show (fun i => eFlow (d := d) ℓ t (w i)) =
        (fun i => (presFam (d := d) H hfin V hVΛ hV0 i : RD d)) from funext hweq]
    exact presFam_linearIndependent (d := d) (Λ := H) (hΛfin := hfin) (X := V) (hXΛ := hVΛ)
      (hX0 := hV0)
  have hwli : LinearIndependent ℝ w :=
    LinearIndependent.of_comp (eFlow (d := d) ℓ t) hli'
  refine ⟨w, hwmem, hwli, ?_, ?_⟩
  -- the level function of `w` realises the data
  have hchain : maxData (d := d) (imageSpan (d := d) g) ℓ t (subDim V) =
      Real.log (cnorm hkd (exteriorPower.map (subDim V) (eFlow (d := d) ℓ t)
        (exteriorPower.ιMulti ℝ (subDim V) w))) := by
    calc maxData (d := d) (imageSpan (d := d) g) ℓ t (subDim V)
        = flowMaxData (d := d) (imageSpan (d := d) g) ℓ t (subDim V) hkd :=
          maxData_apply_of (d := d) hV1 hkd
      _ = maxRankData (d := d) M (subDim V) hkd :=
          flowMaxData_eq_maxRankData (d := d) ℓ t (subDim V) hkd
      _ = maxRankData (d := d) H (subDim V) hkd := by rw [hMH]
      _ = maxCovol (d := d) H hfin V hVΛ := hcov.symm
      _ = Real.log (cnorm hkd (exteriorPower.ιMulti ℝ (subDim V)
            (presFam (d := d) H hfin V hVΛ hV0))) := by
          rw [maxCovol, dif_neg hV0]
      _ = Real.log (cnorm hkd (exteriorPower.ιMulti ℝ (subDim V)
            (fun i => eFlow (d := d) ℓ t (w i)))) := by
          rw [show (presFam (d := d) H hfin V hVΛ hV0) =
            (fun i => eFlow (d := d) ℓ t (w i)) from funext (fun i => (hweq i).symm)]
      _ = Real.log (cnorm hkd (exteriorPower.map (subDim V) (eFlow (d := d) ℓ t)
            (exteriorPower.ιMulti ℝ (subDim V) w))) := by
          rw [exteriorPower.map_apply_ιMulti]
          rfl
  · rw [flowLevel]
    exact hchain
  · rw [show (fun i => eFlow (d := d) ℓ t (w i)) =
        (fun i => (presFam (d := d) H hfin V hVΛ hV0 i : RD d)) from funext hweq,
      ← Submission.IntrinsicIndex.realSpan_span_range (d := d)
        (w := presFam (d := d) H hfin V hVΛ hV0)]
    exact congrArg realSpan (presFam_span (d := d) (Λ := H) (hΛfin := hfin) (X := V)
      (hXΛ := hVΛ) (hX0 := hV0)).symm

/-! ## The packaged criterion for a flag member -/

/-- **The capacity criterion for a tight flag member.**  Let `Λ_t = imageSpan (g.trans (eEquiv ℓ t))`
be the §3 flowed lattice, `V` a tight member at a rank `j = subDim V` which is an angular rank of
the flow polygon at time `t`, and assume the good-time hypothesis (all slacked slopes
differentiable at `t`) and the `BddBelow` of the flow data.  Then there are a family `w` in
`Λ₀ = imageSpan g` and a first active block `u` with

`effPos s ≤ j − u`,

i.e. the accounting capacity is at most the number of directions the member can supply. -/
theorem exists_activeBlock_and_effPos_le {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (g : RD d ≃ₗ[ℝ] RD d) (t : ℝ)
    (A : ℝ) {V : Submodule ℤ (RD d)}
    (hVΛ : V ≤ imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t)))
    (hV0 : V ≠ ⊥) (hV1 : 1 ≤ subDim V)
    (hVtight : maxPhi (d := d) (imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t)))
        (finrank_imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t))) A V hVΛ =
      maxphiData (d := d) (imageSpan (d := d) (g.trans (eEquiv (d := d) ℓ t))) A (subDim V))
    (hbdd : ∀ x, BddBelow (flowMaxDataSet (d := d) (imageSpan (d := d) g) ℓ x (subDim V)
      (subDim_le_ambient V)))
    (hdiff : ∀ i : Fin d, DifferentiableAt ℝ
      (fun x => phiSlope (d := d) (imageSpan (d := d) g) ℓ A x i.val) t)
    {s : ℕ} (hs1 : 1 ≤ s)
    (hsN : s < numBlocks d (phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t))
    (hbs : blockStart d (phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t) s = subDim V) :
    ∃ (w : Fin (subDim V) → RD d) (u : ℕ), (∀ i, w i ∈ imageSpan (d := d) g) ∧
      LinearIndependent ℝ w ∧
      IsFirstActiveBlock (d := d) ℓ (subDim_le_ambient V) t
        (exteriorPower.ιMulti ℝ (subDim V) w) u ∧
      effPos d ℓ (fun s => (blockStart d (phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t) s : ℝ))
        (phiLevelDeriv (d := d) (imageSpan (d := d) g) ℓ A t
          (blockStart d (phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t))) s
        ≤ (subDim V : ℝ) - (u : ℝ) ∧
      Submodule.span ℝ (Set.range (fun i => eFlow (d := d) ℓ t (w i))) = realSpan V := by
  classical
  have hkd : subDim V ≤ d := subDim_le_ambient V
  obtain ⟨w, hwmem, hwli, hatt, hspan⟩ :=
    exists_preimage_of_tight (d := d) (ℓ := ℓ) g t A hVΛ hV0 hV1 hVtight
  have hwne : exteriorPower.ιMulti ℝ (subDim V) w ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent _ hwli
  obtain ⟨u, hu⟩ := exists_isFirstActive (d := d) hℓ0 hℓd hkd hwne t
  refine ⟨w, u, hwmem, hwli, hu, ?_, hspan⟩
  -- the tightness at the angular rank
  have htight : phiPolygonT (d := d) (imageSpan (d := d) g) ℓ A t (subDim V) =
      phiData (d := d) (imageSpan (d := d) g) ℓ A t (subDim V) := by
    rw [← hbs]
    exact phiPolygonT_tight_at_flagRank (d := d) g ℓ t A hs1 hsN
  exact effPos_le_of_tangent hℓ0 hℓd (imageSpan (d := d) g) A hV1 hkd hbdd hwmem hwli hwne
    hatt htight hdiff hu hbs


end Submission.FlagMemberCriterion

end
