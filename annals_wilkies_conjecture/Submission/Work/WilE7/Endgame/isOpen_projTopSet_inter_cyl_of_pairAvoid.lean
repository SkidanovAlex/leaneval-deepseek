import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.Endgame.g2_pair_helpers
import Submission.Work.WilE7.Endgame.g2_ptwise

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt)

/-- **G2**: the `(n+1)`-projection of a vertical piece `T` is open inside the cylinder `cyl C`,
given a stratification `Wl` of the pair set `absPairSet2 R T` all of whose strata of low base rank
avoid `C`. -/
theorem isOpen_projTopSet_inter_cyl_of_pairAvoid {n m k : ℕ}
    (T R : Stratum 0 (n + (m + 1))) (hT : T.Good) (hR : R.Good) (himm : HImm T)
    (hvert : ∀ z ∈ T.X.set, projRank T z + 1 = n + (m + 1) - T.j)
    (hrankR : ∀ z ∈ R.X.set, projRank R z = n + (m + 1) - R.j)
    (hdimR : n + (m + 1) - R.j + 1 = n + (m + 1) - T.j)
    (C : Set (Fin n → ℝ)) (hk : 0 < k)
    (r : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hrcont : ∀ j, ContinuousOn (r j) C)
    (hrsub : ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
      absPtUp (n := n) (m := m) (Fin.append x (r j x)) ∈ R.X.set)
    (Wl : List (Stratum 0 (pPair n m)))
    (hWgood : ∀ W ∈ Wl, W.Good)
    (hWsub : ∀ W ∈ Wl, W.X.set ⊆ (absPairSet2 R T).set)
    (hWcov : (absPairSet2 R T).set = ⋃ W ∈ Wl, W.X.set)
    (hWlow : ∀ W ∈ Wl, ∀ w ∈ W.X.set, pairBaseRank W w < n + (m + 1) - R.j →
      Work.CoreStep.pairBase n m w ∉ C) :
    IsOpen {z : ↥(Work.WilE7.cyl C) | (z : Fin (n + 1) → ℝ) ∈ projTopSet T} := by
  classical
  -- Every point of `cyl C ∩ projTopSet T` has a neighbourhood (in the ambient space) whose trace
  -- on the cylinder is contained in `projTopSet T`.
  have hpt : ∀ z₀ ∈ Work.WilE7.cyl C, z₀ ∈ projTopSet T →
      ∃ U ∈ nhds z₀, U ∩ Work.WilE7.cyl C ⊆ projTopSet T := by
    intro z₀ hz₀cyl hz₀mem
    -- a witnessing point `t₀ ∈ T.X.set` with `projTop (absPt t₀) = z₀`
    rw [projTopSet, Set.mem_image] at hz₀mem
    obtain ⟨w, hwabs, hwproj⟩ := hz₀mem
    rw [MainDesign.absSet, Set.mem_image] at hwabs
    obtain ⟨t₀, ht₀, hwt⟩ := hwabs
    have hproj : projTop n m (absPt t₀) = z₀ := by rw [hwt]; exact hwproj
    have hb0 : basePrLin n (m + 1) t₀ = Fin.init z₀ := by
      rw [← Work.WilE7.CoreStep.projFirst_absPt t₀,
        ← Work.WilE7.CoreStep.projTop_init n m (absPt t₀), hproj]
    have hv0 : Work.WilE7.CoreStep.verT t₀ = z₀ (Fin.last n) := by
      rw [← Work.WilE7.CoreStep.projTopLin_absPtLin_last t₀,
        Work.WilE7.CoreStep.absPtLin_apply, Work.WilE7.CoreStep.projTopLin_apply, hproj]
    obtain ⟨U, hU, hUsub⟩ :=
      g2_ptwise T R hT hR himm hvert hrankR hdimR C hk r hrcont hrsub Wl
        hWgood hWsub hWcov hWlow (Fin.init z₀) (z₀ (Fin.last n)) t₀ hz₀cyl.1 ht₀ hb0 hv0
    refine ⟨U, ?_, hUsub⟩
    rwa [snoc_init_self z₀] at hU
  -- Pass to open neighbourhoods and take the union.
  let S : Set (Fin (n + 1) → ℝ) := Work.WilE7.cyl C ∩ projTopSet T
  have hS : ∀ z : ↥S, ∃ V, IsOpen V ∧ (z : Fin (n + 1) → ℝ) ∈ V ∧
      V ∩ Work.WilE7.cyl C ⊆ projTopSet T := by
    rintro ⟨z₀, hz1, hz2⟩
    obtain ⟨U, hUmem, hUsub⟩ := hpt z₀ hz1 hz2
    obtain ⟨V, hVsub, hVopen, hVmem⟩ := mem_nhds_iff.mp hUmem
    exact ⟨V, hVopen, hVmem, fun x hx => hUsub ⟨hVsub hx.1, hx.2⟩⟩
  choose V hVopen hVmem hVsub using hS
  refine isOpen_induced_iff.mpr ⟨⋃ z : ↥S, V z, isOpen_iUnion fun z => hVopen z, ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨z₀, hzV⟩ := Set.mem_iUnion.mp hz
    exact hVsub z₀ ⟨hzV, z.2⟩
  · intro hz
    refine Set.mem_iUnion.mpr ⟨⟨(z : Fin (n + 1) → ℝ), z.2, hz⟩, ?_⟩
    exact hVmem ⟨(z : Fin (n + 1) → ℝ), z.2, hz⟩

end Work.WilE7.Endgame
