import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR1.HJ.HJDefs
import Submission.Work.FTS_RegExport.RXR1.HJ.derivBoundZero
import Submission.Work.FTS_RegExport.RXR1.HJ.jetZsliceTendsto
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Filter Set
open scoped Topology

namespace Work.FTS_RegExport.RXR1

/-! ## The `R5Parts` fields at `τ = 0`: `O(z)` bound and bounded derivative of the right-hand side

The five pieces of `RHSo` are: `-(𝓛_Γ^T G)(0)`, the singular `-μ̄·AK` term, `N₀`, `N` and `N_*`.
The first four are termwise differentiable in `z` with a uniform bound (`R5Parts.hLz`, `hN₀z`,
`hNz`, `hNsz`) and jointly bounded with a joint Hölder modulus (`R5Parts.hJ`); the last one is the
explicit `AK`, controlled by `HJ.AKBounds`.  The right-hand side vanishes at `z = 0`
(`R5Parts.hRz0`), so the Lipschitz-in-`z` bound upgrades to an `O(z)` bound. -/

theorem exists_RHS_bound {αG S : ℝ} {G Φ : Work.FTS.Galerkin.Fam}
    (hαG : 0 < αG) (hαG13 : αG ≤ 1 / 3) (hS : 0 < S)
    (H : Work.FTS.RegPkgGal.R5Parts αG S G Φ) :
    ∃ NZ : ℝ, 0 ≤ NZ ∧
      (∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z → |RHSo αG G Φ z θ| ≤ NZ * z) ∧
      (∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
        ∃ d : ℝ, HasDerivAt (fun z' : ℝ => RHSo αG G Φ z' θ) d z ∧ |d| ≤ NZ) := by
  obtain ⟨NJ, hL, hN0, hN, hNs⟩ := H.hJ
  obtain ⟨M, hM0, hMb⟩ := H.hmb
  obtain ⟨NZ1, hNZ1, hLz⟩ := H.hLz
  obtain ⟨NZ2, hNZ2, hN0z⟩ := H.hN₀z
  obtain ⟨NZ3, hNZ3, hNz⟩ := H.hNz
  obtain ⟨NZ4, hNZ4, hNsz⟩ := H.hNsz
  have hp1 : (0 : ℝ) < Work.FTS.Regularity.pExp αG := by
    simp only [Work.FTS.Regularity.pExp]; linarith
  have hp2 : Work.FTS.Regularity.pExp αG ≤ 1 := by
    simp only [Work.FTS.Regularity.pExp]; linarith
  obtain ⟨hAKval, hAKder⟩ := HJ.AKBounds hp1 hp2
  have hmbar : |mbar0 αG G Φ| ≤ M := by
    have h := hMb 0 ⟨le_rfl, hS.le⟩
    simpa only [mbar0] using h
  have hconst : 0 ≤ NZ1 + M * 10 + NZ2 + NZ3 + NZ4 := by
    have h10 : (0 : ℝ) ≤ M * 10 := by positivity
    linarith
  refine ⟨NZ1 + M * 10 + NZ2 + NZ3 + NZ4, hconst, ?_, ?_⟩
  · intro θ hθ z hz
    have hder : ∀ x : ℝ, 0 < x → ∃ d : ℝ,
        HasDerivAt (fun z' => RHSo αG G Φ z' θ) d x ∧
          |d| ≤ NZ1 + M * 10 + NZ2 + NZ3 + NZ4 := by
      intro x hx
      obtain ⟨d1, hd1, hb1⟩ := hLz 0 ⟨le_rfl, hS.le⟩ θ hθ x hx
      obtain ⟨d2, hd2, hb2⟩ := hN0z 0 ⟨le_rfl, hS.le⟩ θ hθ x hx
      obtain ⟨d3, hd3, hb3⟩ := hNz 0 ⟨le_rfl, hS.le⟩ θ hθ x hx
      obtain ⟨d4, hd4, hb4⟩ := hNsz 0 ⟨le_rfl, hS.le⟩ θ hθ x hx
      obtain ⟨da, hda, hba⟩ := hAKder θ hθ x hx
      have hd1' : HasDerivAt (fun z' => RP1 αG G z' θ) d1 x := hd1
      have hd2' : HasDerivAt (fun z' => RP2 αG G z' θ) d2 x := hd2
      have hd3' : HasDerivAt (fun z' => RP3 αG G Φ z' θ) d3 x := hd3
      have hd4' : HasDerivAt (fun z' => RP4 αG G Φ z' θ) d4 x := hd4
      have ha : HasDerivAt (fun z' => (-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z' θ)
          ((-(mbar0 αG G Φ)) * da) x := hda.const_mul _
      have h5 : HasDerivAt
          (fun z' => RP1 αG G z' θ + ((-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z' θ
            + RP2 αG G z' θ + RP3 αG G Φ z' θ + RP4 αG G Φ z' θ))
          (d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4)) x :=
        hd1'.add (((ha.add hd2').add hd3').add hd4')
      have hR : HasDerivAt (fun z' => RHSo αG G Φ z' θ)
          (d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4)) x := by
        simpa only [RHSo_eq] using h5
      refine ⟨d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4), hR, ?_⟩
      have hprod : |(-(mbar0 αG G Φ)) * da| ≤ M * 10 := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul hmbar hba (abs_nonneg _) hM0
      calc |d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4)|
          ≤ |d1| + |(-(mbar0 αG G Φ)) * da + d2 + d3 + d4| := abs_add_le _ _
        _ ≤ |d1| + (|(-(mbar0 αG G Φ)) * da + d2 + d3| + |d4|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ |d1| + ((|(-(mbar0 αG G Φ)) * da + d2| + |d3|) + |d4|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ |d1| + (((|(-(mbar0 αG G Φ)) * da| + |d2|) + |d3|) + |d4|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ NZ1 + M * 10 + NZ2 + NZ3 + NZ4 := by linarith
    have htend : Tendsto (fun z => RHSo αG G Φ z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hl1 : Tendsto (fun z => RP1 αG G z θ) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (RP1 αG G 0 θ)) := by
        have h := HJ.jetZsliceTendsto hL hαG hθ ⟨le_rfl, hS.le⟩
        simpa only [RP1] using h
      have hl2 : Tendsto (fun z => RP2 αG G z θ) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (RP2 αG G 0 θ)) := by
        have h := HJ.jetZsliceTendsto hN0 hαG hθ ⟨le_rfl, hS.le⟩
        simpa only [RP2] using h
      have hl3 : Tendsto (fun z => RP3 αG G Φ z θ) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (RP3 αG G Φ 0 θ)) := by
        have h := HJ.jetZsliceTendsto hN hαG hθ ⟨le_rfl, hS.le⟩
        simpa only [RP3] using h
      have hl4 : Tendsto (fun z => RP4 αG G Φ z θ) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (RP4 αG G Φ 0 θ)) := by
        have h := HJ.jetZsliceTendsto hNs hαG hθ ⟨le_rfl, hS.le⟩
        simpa only [RP4] using h
      have hla : Tendsto (fun z => (-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z θ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have hb : ∀ᶠ z : ℝ in nhdsWithin 0 (Set.Ioi 0),
            |(-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z θ|
              ≤ |mbar0 αG G Φ| * (20 * z ^ 2) := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          rw [abs_mul, abs_neg]
          exact mul_le_mul_of_nonneg_left (hAKval θ hθ z hz.le) (abs_nonneg _)
        have hg : Tendsto (fun z : ℝ => |mbar0 αG G Φ| * (20 * z ^ 2))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          have hc : Continuous fun z : ℝ => |mbar0 αG G Φ| * (20 * z ^ 2) := by continuity
          simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
        exact squeeze_zero_norm' hb hg
      have hAK0 : Work.Construction.AK (Work.FTS.Regularity.pExp αG) 0 θ = 0 := by
        simp [Work.Construction.AK]
      have hlim : Tendsto (fun z => RP1 αG G z θ
            + ((-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z θ
              + RP2 αG G z θ + RP3 αG G Φ z θ + RP4 αG G Φ z θ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (RP1 αG G 0 θ + ((-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) 0 θ
            + RP2 αG G 0 θ + RP3 αG G Φ 0 θ + RP4 αG G Φ 0 θ))) := by
        rw [hAK0]
        simpa using hl1.add (((hla.add hl2).add hl3).add hl4)
      have hzero : RP1 αG G 0 θ + ((-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) 0 θ
          + RP2 αG G 0 θ + RP3 αG G Φ 0 θ + RP4 αG G Φ 0 θ) = 0 := by
        rw [← RHSo_eq 0 θ]
        exact H.hRz0 0 ⟨le_rfl, hS.le⟩ θ hθ
      have hgoal : Tendsto (fun z => RP1 αG G z θ
            + ((-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z θ
              + RP2 αG G z θ + RP3 αG G Φ z θ + RP4 αG G Φ z θ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa only [hzero] using hlim
      exact hgoal.congr' (Eventually.of_forall fun z => (RHSo_eq z θ).symm)
    exact HJ.derivBoundZero hconst hder htend z hz
  · intro θ hθ z hz
    obtain ⟨d1, hd1, hb1⟩ := hLz 0 ⟨le_rfl, hS.le⟩ θ hθ z hz
    obtain ⟨d2, hd2, hb2⟩ := hN0z 0 ⟨le_rfl, hS.le⟩ θ hθ z hz
    obtain ⟨d3, hd3, hb3⟩ := hNz 0 ⟨le_rfl, hS.le⟩ θ hθ z hz
    obtain ⟨d4, hd4, hb4⟩ := hNsz 0 ⟨le_rfl, hS.le⟩ θ hθ z hz
    obtain ⟨da, hda, hba⟩ := hAKder θ hθ z hz
    have hd1' : HasDerivAt (fun z' => RP1 αG G z' θ) d1 z := hd1
    have hd2' : HasDerivAt (fun z' => RP2 αG G z' θ) d2 z := hd2
    have hd3' : HasDerivAt (fun z' => RP3 αG G Φ z' θ) d3 z := hd3
    have hd4' : HasDerivAt (fun z' => RP4 αG G Φ z' θ) d4 z := hd4
    have ha : HasDerivAt (fun z' => (-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z' θ)
        ((-(mbar0 αG G Φ)) * da) z := hda.const_mul _
    have h5 : HasDerivAt
        (fun z' => RP1 αG G z' θ + ((-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z' θ
          + RP2 αG G z' θ + RP3 αG G Φ z' θ + RP4 αG G Φ z' θ))
        (d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4)) z :=
      hd1'.add (((ha.add hd2').add hd3').add hd4')
    refine ⟨d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4), ?_, ?_⟩
    · simpa only [RHSo_eq] using h5
    · have hprod : |(-(mbar0 αG G Φ)) * da| ≤ M * 10 := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul hmbar hba (abs_nonneg _) hM0
      calc |d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4)|
          ≤ |d1| + |(-(mbar0 αG G Φ)) * da + d2 + d3 + d4| := abs_add_le _ _
        _ ≤ |d1| + (|(-(mbar0 αG G Φ)) * da + d2 + d3| + |d4|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ |d1| + ((|(-(mbar0 αG G Φ)) * da + d2| + |d3|) + |d4|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ |d1| + (((|(-(mbar0 αG G Φ)) * da| + |d2|) + |d3|) + |d4|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ NZ1 + M * 10 + NZ2 + NZ3 + NZ4 := by linarith

end Work.FTS_RegExport.RXR1
