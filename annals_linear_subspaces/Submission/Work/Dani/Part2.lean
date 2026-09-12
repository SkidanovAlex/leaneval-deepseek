import Submission.Work.Dani.Endgame
import Submission.GeometryOfNumbers.WedgeGeneralE1
import Submission.GeometryOfNumbers.WedgeBlockZero
import Submission.GeometryOfNumbers.ModelCone
import Submission.GeometryOfNumbers.PlaneFinrank
import Submission.Bridge.ChallengeIsometry
import Submission.Work.ModelStar.ModelStarHeight
import Submission.GeometryOfNumbers.RationalSpan
import Submission.Commons.Analysis.InnerProductSpace.norm_exteriorPower_map_isometry
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent
import Submission.Work.Dani.OrthoRep

/-!
# Prop 1, part 2 (Dani correspondence, second point) in the coordinate model

De Saxcé's Proposition 1, part 2: given `t ≥ 0` and a pure tensor `w = ιMulti m` of an
independent integer family `m : Fin k → ℤᵈ` whose *flowed* image under `a_t ∘ s_x` is
dominated by its `L`-block (`π₊`-dominance), the rational `k`-plane `V = span(m)` satisfies

* `d(V, x) ≤ c⁻¹ · e^{−t(1/ℓ+1/(d−ℓ))}` — the **distance half**, and
* `H(V) ≤ (k+1)·c⁻¹·e^{t·k/ℓ}·‖a_t(s_x w)‖` — the **height half**,

where `x = s_x^{-1}x₀` (`modelX ℓ`).  Here we take `s_x` to be a **linear isometry**
(`s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ` with `x.map s = x₀`): the paper's change of representative
`x = P s_x` may always be chosen orthogonal, and this makes both halves exact:

* distance: `d(V,x) = d(V.map s, x₀)` (isometry invariance, `Submission.Bridge.Isometry`)
  and `V.map s = span(s ∘ m)` has wedge `⋀ᵏ(s)(ιMulti m)`, so the **general graph estimate**
  `planeResidual_pureTensor_le_blockRatio` (`Submission.WedgeGeneralE1`) bounds the distance by
  the block ratio `‖block₁‖/‖block₀‖`, which `π₊`-dominance (`Submission.DaniEndgame.ratio_one_le`)
  makes exponentially small;
* height: `H(V) ≤ ‖ιMulti m‖` (`Submission.ModelStarHeight.height_le_span_intPoints`) and
  `‖ιMulti m‖ = ‖⋀ᵏ(s)(ιMulti m)‖` (isometry, `norm_exteriorPower_map_isometry`), so
  `Submission.DaniEndgame.norm_le_of_dominated` applies directly.

All declarations are sorry-free; module `Submission.Work.Dani.Part2`, namespace
`Submission.DaniPart2`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real LinearSubspaces
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks

namespace Submission.DaniPart2

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- Reindexing invariance of the exterior norm: `ιMulti` over `Fin n` of a family reindexed
along `Fin.cast h` has the same norm as `ιMulti` over `Fin k`. -/
lemma norm_iMulti_reindex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n k : ℕ} (h : n = k) (v : Fin k → E) :
    ‖exteriorPower.ιMulti ℝ n (fun i => v (Fin.cast h i))‖ =
      ‖exteriorPower.ιMulti ℝ k v‖ := by
  subst h
  rfl

/-- **Prop 1, part 2 — distance half.**  For an isometry `s` with `x.map s = x₀ = modelX ℓ` and
an independent family `m : Fin k → ℝᵈ` whose `s`-image wedge is `π₊`-dominated at time `t`,
the challenge distance from `V = span(range m)` to `x` is at most `c⁻¹·e^{−t·S}`. -/
theorem distSubspaces_le_of_dominated {ℓ k : ℕ} (hk : 0 < k) (hkl : k ≤ ℓ) (hℓd : ℓ < d)
    (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ) (x : Submodule ℝ ℝᵈ)
    (hxmap : x.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) = modelX (d := d) ℓ)
    (m : Fin k → ℝᵈ) (hLI : LinearIndependent ℝ m)
    {t c : ℝ} (hc : 0 < c)
    (hdom : Submission.DaniEndgame.Dominates d ℓ k t c
      (exteriorPower.map k (s : ℝᵈ →ₗ[ℝ] ℝᵈ) (exteriorPower.ιMulti ℝ k m))) :
    LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) x ≤
      c⁻¹ * Real.exp (-(t * Submission.DaniEndgame.rate d ℓ)) := by
  classical
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hk hkl
  let sL : ℝᵈ →ₗ[ℝ] ℝᵈ := (s : ℝᵈ →ₗ[ℝ] ℝᵈ)
  let m' : Fin k → ℝᵈ := sL ∘ m
  let w : WK d k := exteriorPower.ιMulti ℝ k m
  let w' : WK d k := exteriorPower.ιMulti ℝ k m'
  have hw' : w' = exteriorPower.map k sL w := by
    dsimp only [w', w, m']
    exact (exteriorPower.map_apply_ιMulti sL m).symm
  have hdom' : Submission.DaniEndgame.Dominates d ℓ k t c w' := by
    rw [hw']; exact hdom
  -- the `s`-image family is independent
  have hLI' : LinearIndependent ℝ m' := by
    have hker : sL.ker = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro a b hab
      exact s.injective (by simpa [sL] using hab)
    have hd : Disjoint (Submodule.span ℝ (Set.range m)) sL.ker := by
      rw [hker]; exact disjoint_bot_right
    have h := LinearIndependent.map (f := sL) hLI hd
    simpa only [m'] using h
  have hw'ne : w' ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent m' hLI'
  -- `π₊`-dominance forces the `L`-block of the *unflowed* wedge to be nonzero
  have hw'0 : blockElem (d := d) (k := k) (ℓ := ℓ) w' 0 ≠ 0 := by
    intro h0
    have hflne : Submission.DaniEndgame.eFlowK d ℓ k t w' ≠ 0 := by
      have hinj : Function.Injective (fun z : WK d k => Submission.DaniEndgame.eFlowK d ℓ k t z) := by
        simpa [Submission.DaniEndgame.eFlowK, Submission.DaniEndgame.eFlow] using
          (Submission.ModelCone.map_twoScale_injective (d := d) (k := k)
            (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / (((d - ℓ : ℕ)) : ℝ))) ℓ
            (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _)))
      exact fun hz => hw'ne (hinj (by
        show Submission.DaniEndgame.eFlowK d ℓ k t w' = Submission.DaniEndgame.eFlowK d ℓ k t 0
        rw [hz, map_zero]))
    have hflowzero : blockElem (d := d) (k := k) (ℓ := ℓ)
        (Submission.DaniEndgame.eFlowK d ℓ k t w') 0 = 0 := by
      rw [Submission.DaniEndgame.blockElem_eFlowK (d := d) (k := k) (ℓ := ℓ)
        (u := 0) hℓ0 hℓd t w' (Nat.zero_le k), h0, smul_zero]
    have hle : c * ‖Submission.DaniEndgame.eFlowK d ℓ k t w'‖ ≤
        ‖blockElem (d := d) (k := k) (ℓ := ℓ)
          (Submission.DaniEndgame.eFlowK d ℓ k t w') 0‖ := hdom'
    rw [hflowzero, norm_zero] at hle
    have hnorm : ‖Submission.DaniEndgame.eFlowK d ℓ k t w'‖ = 0 := by
      nlinarith [norm_nonneg (Submission.DaniEndgame.eFlowK d ℓ k t w'), hc]
    exact hflne (norm_eq_zero.mp hnorm)
  have hbot : Submodule.span ℝ (Set.range m') ⊓ (modelX (d := d) ℓ)ᗮ = ⊥ :=
    Submission.WedgeBlockZero.inj_modelX_of_block0_ne_zero ℓ m' hLI' hw'0
  -- dimensions and nonzeroness
  have hfrV : Module.finrank ℝ (Submodule.span ℝ (Set.range m)) = k :=
    Submission.PlaneFinrank.finrank_span_range (d := d) m hLI
  have hfrX : Module.finrank ℝ x = ℓ := by
    have h1 : Module.finrank ℝ (x.map (s.toLinearEquiv : ℝᵈ →ₗ[ℝ] ℝᵈ)) =
        Module.finrank ℝ x :=
      s.toLinearEquiv.finrank_map_eq x
    have h2 : (x.map (s.toLinearEquiv : ℝᵈ →ₗ[ℝ] ℝᵈ)) = x.map sL := rfl
    rw [h2, hxmap] at h1
    rw [← h1, Submission.PlaneFinrank.finrank_modelX (d := d) ℓ (le_of_lt hℓd)]
  have hVn : Submodule.span ℝ (Set.range m) ≠ ⊥ :=
    Submission.PlaneFinrank.span_range_ne_bot (d := d) hk m hLI
  have hxn : x ≠ ⊥ := by
    intro h
    have hmap0 : x.map sL = ⊥ := by rw [h]; simp
    rw [hxmap] at hmap0
    exact Submission.PlaneFinrank.modelX_ne_bot (d := d) ℓ hℓ0 (le_of_lt hℓd) hmap0
  have hspan' : (Submodule.span ℝ (Set.range m)).map sL = Submodule.span ℝ (Set.range m') := by
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨m i, ⟨i, rfl⟩, rfl⟩
  have hfrV' : Module.finrank ℝ (Submodule.span ℝ (Set.range m')) = k := by
    rw [← hspan', LinearEquiv.finrank_map_eq]
    exact hfrV
  -- the chain
  have h1 : LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) x =
      LinearSubspaces.distSubspaces ((Submodule.span ℝ (Set.range m)).map sL)
        (modelX (d := d) ℓ) := by
    have hle : Module.finrank ℝ (Submodule.span ℝ (Set.range m)) ≤ Module.finrank ℝ x := by
      rw [hfrV, hfrX]; exact hkl
    have hiso := Submission.Bridge.Isometry.distSubspaces_map
      (Submodule.span ℝ (Set.range m)) x s hle hVn hxn
    rw [hxmap] at hiso
    exact hiso.symm
  have h2 : LinearSubspaces.distSubspaces ((Submodule.span ℝ (Set.range m)).map sL)
        (modelX (d := d) ℓ) ≤
      Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range m'))
        (modelX (d := d) ℓ) := by
    rw [hspan']
    refine Submission.Bridge.distSubspaces_le_planeResidual_of_le _ _ ?_ ?_ ?_
    · rw [hfrV', Submission.PlaneFinrank.finrank_modelX (d := d) ℓ (le_of_lt hℓd)]
      exact hkl
    · exact Submission.PlaneFinrank.span_range_ne_bot (d := d) hk m' hLI'
    · exact Submission.PlaneFinrank.modelX_ne_bot (d := d) ℓ hℓ0 (le_of_lt hℓd)
  have h3 : Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range m'))
        (modelX (d := d) ℓ) ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ /
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 0‖ :=
    Submission.WedgeGeneralE1.planeResidual_pureTensor_le_blockRatio ℓ hk m' hLI' hbot
  have h4 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ /
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 0‖ ≤
      c⁻¹ * Real.exp (-(t * Submission.DaniEndgame.rate d ℓ)) := by
    have hk1 : 1 ≤ k := hk
    have hle := Submission.DaniEndgame.ratio_one_le (d := d) (k := k) (ℓ := ℓ)
      hℓ0 hℓd hk1 hc hdom'
    have hpos : 0 < ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 0‖ := norm_pos_iff.mpr hw'0
    rw [div_le_iff₀ hpos]
    exact hle
  calc LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) x
      = LinearSubspaces.distSubspaces ((Submodule.span ℝ (Set.range m)).map sL)
          (modelX (d := d) ℓ) := h1
    _ ≤ Submission.ProjectionDistance.planeResidual (Submodule.span ℝ (Set.range m'))
          (modelX (d := d) ℓ) := h2
    _ ≤ ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ /
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 0‖ := h3
    _ ≤ c⁻¹ * Real.exp (-(t * Submission.DaniEndgame.rate d ℓ)) := h4

/-- **Prop 1, part 2 — height half.**  Under the same hypotheses (plus integrality of `m`), the
height of the rational plane `V = span(range m)` is at most
`(k+1)·c⁻¹·e^{t·k/ℓ}·‖a_t(s_x w)‖`. -/
theorem height_le_of_dominated {ℓ k : ℕ} (hk : 0 < k) (hkl : k ≤ ℓ) (hℓd : ℓ < d)
    (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ)
    (m : Fin k → ℝᵈ) (hmem : ∀ i, m i ∈ intPoints (d := d)) (hLI : LinearIndependent ℝ m)
    {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (hdom : Submission.DaniEndgame.Dominates d ℓ k t c
      (exteriorPower.map k (s : ℝᵈ →ₗ[ℝ] ℝᵈ) (exteriorPower.ιMulti ℝ k m)))
    (hV : IsRational (Submodule.span ℝ (Set.range m))) :
    LinearSubspaces.height (Submodule.span ℝ (Set.range m)) hV ≤
      ((k : ℝ) + 1) * c⁻¹ * Real.exp (t * (k : ℝ) / (ℓ : ℝ)) *
        ‖Submission.DaniEndgame.eFlowK d ℓ k t
          (exteriorPower.map k (s : ℝᵈ →ₗ[ℝ] ℝᵈ) (exteriorPower.ιMulti ℝ k m))‖ := by
  classical
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hk hkl
  let sL : ℝᵈ →ₗ[ℝ] ℝᵈ := (s : ℝᵈ →ₗ[ℝ] ℝᵈ)
  let V : Submodule ℝ ℝᵈ := Submodule.span ℝ (Set.range m)
  have hH := Submission.ModelStarHeight.height_le_span_intPoints (d := d) V hV
    (m := m) rfl hmem hLI
  -- `hH : height V hV ≤ ‖ιMulti ℝ (finrank V) (fun i => m (Fin.cast _ i))‖`
  have hfinV : Module.finrank ℝ V = k := Submission.PlaneFinrank.finrank_span_range (d := d) m hLI
  have hA : ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V)
        (fun i => m (Fin.cast hfinV i))‖ = ‖exteriorPower.ιMulti ℝ k m‖ :=
    norm_iMulti_reindex hfinV m
  have hB : ‖exteriorPower.ιMulti ℝ k m‖ =
      ‖exteriorPower.map k sL (exteriorPower.ιMulti ℝ k m)‖ := by
    have h := Commons.Analysis.InnerProductSpace.norm_exteriorPower_map_isometry (n := k) s
      (exteriorPower.ιMulti ℝ k m)
    simpa [sL] using h.symm
  have hC := Submission.DaniEndgame.norm_le_of_dominated (d := d) (k := k) (ℓ := ℓ)
    hℓ0 hℓd hk ht hc hdom
  calc LinearSubspaces.height V hV
      ≤ ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V)
          (fun i => m (Fin.cast hfinV i))‖ := hH
    _ = ‖exteriorPower.ιMulti ℝ k m‖ := hA
    _ = ‖exteriorPower.map k sL (exteriorPower.ιMulti ℝ k m)‖ := hB
    _ ≤ ((k : ℝ) + 1) * c⁻¹ * Real.exp (t * (k : ℝ) / (ℓ : ℝ)) *
          ‖Submission.DaniEndgame.eFlowK d ℓ k t
            (exteriorPower.map k (s : ℝᵈ →ₗ[ℝ] ℝᵈ) (exteriorPower.ιMulti ℝ k m))‖ := hC

/-- **Prop 1, part 2 (both halves)**, bundled. -/
theorem prop1_part2 {ℓ k : ℕ} (hk : 0 < k) (hkl : k ≤ ℓ) (hℓd : ℓ < d)
    (s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ) (x : Submodule ℝ ℝᵈ)
    (hxmap : x.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) = modelX (d := d) ℓ)
    (m : Fin k → ℝᵈ) (hmem : ∀ i, m i ∈ intPoints (d := d)) (hLI : LinearIndependent ℝ m)
    {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (hdom : Submission.DaniEndgame.Dominates d ℓ k t c
      (exteriorPower.map k (s : ℝᵈ →ₗ[ℝ] ℝᵈ) (exteriorPower.ιMulti ℝ k m))) :
    LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) x ≤
        c⁻¹ * Real.exp (-(t * Submission.DaniEndgame.rate d ℓ)) ∧
      ∀ hV : IsRational (Submodule.span ℝ (Set.range m)),
        LinearSubspaces.height (Submodule.span ℝ (Set.range m)) hV ≤
          ((k : ℝ) + 1) * c⁻¹ * Real.exp (t * (k : ℝ) / (ℓ : ℝ)) *
            ‖Submission.DaniEndgame.eFlowK d ℓ k t
              (exteriorPower.map k (s : ℝᵈ →ₗ[ℝ] ℝᵈ) (exteriorPower.ιMulti ℝ k m))‖ :=
  ⟨distSubspaces_le_of_dominated hk hkl hℓd s x hxmap m hLI hc hdom,
   fun hV => height_le_of_dominated hk hkl hℓd s m hmem hLI ht hc hdom hV⟩

/-- **Prop 1, part 2 for a general plane `x`** (the form used by the ★-pair): with the
orthogonal representative `s = orthRep hℓd x hx` of `x`, the hypotheses of Prop 1 part 2 give
the two bounds for the *rational* plane `V = span (range m)`. -/
theorem exists_dominated_pair {ℓ k : ℕ} (hk : 0 < k) (hkl : k ≤ ℓ) (hℓd : ℓ < d)
    (x : Submodule ℝ ℝᵈ) (hx : Module.finrank ℝ x = ℓ)
    (m : Fin k → ℝᵈ) (hmem : ∀ i, m i ∈ intPoints (d := d)) (hLI : LinearIndependent ℝ m)
    {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (hdom : Submission.DaniEndgame.Dominates d ℓ k t c
      (exteriorPower.map k
        (Submission.DaniOrthoRep.orthRep (ℓ := ℓ) (le_of_lt hℓd) x hx : ℝᵈ →ₗ[ℝ] ℝᵈ)
        (exteriorPower.ιMulti ℝ k m))) :
    ∃ hV : IsRational (Submodule.span ℝ (Set.range m)),
      LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) x ≤
        c⁻¹ * Real.exp (-(t * Submission.DaniEndgame.rate d ℓ)) ∧
      LinearSubspaces.height (Submodule.span ℝ (Set.range m)) hV ≤
        ((k : ℝ) + 1) * c⁻¹ * Real.exp (t * (k : ℝ) / (ℓ : ℝ)) *
          ‖Submission.DaniEndgame.eFlowK d ℓ k t
            (exteriorPower.map k
              (Submission.DaniOrthoRep.orthRep (ℓ := ℓ) (le_of_lt hℓd) x hx : ℝᵈ →ₗ[ℝ] ℝᵈ)
              (exteriorPower.ιMulti ℝ k m))‖ := by
  refine ⟨Submission.RationalSpan.isRational_span_of_mem_intPoints m hmem, ?_, ?_⟩
  · exact distSubspaces_le_of_dominated hk hkl hℓd _ x
      (Submission.DaniOrthoRep.orthRep_spec (ℓ := ℓ) (le_of_lt hℓd) x hx) m hLI hc hdom
  · exact height_le_of_dominated hk hkl hℓd _ m hmem hLI ht hc hdom
      (Submission.RationalSpan.isRational_span_of_mem_intPoints m hmem)

end Submission.DaniPart2
