import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.Dim2.levelSet_kit
import Submission.Work.Diff.Dim2.level_nbhd

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-! ## The local claim

The local slice statement is proved separately (it is the `level_nbhd` lemma of the `Dim2` area);
here we only need it as an input. -/

theorem levelSet_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    (hdim : Module.finrank ℝ E = 2)
    {N : Set M} (hN : IsOpen N)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hVnz : ∀ x ∈ N, V x ≠ 0)
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    {u : M → EuclideanSpace ℝ (Fin 2)}
    (hu : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ u N)
    (hu1 : ∀ x ∈ N, ‖u x‖ = 1)
    (huV : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x (V x) = 0)
    (huinj : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x ≠ 0)
    (hconn : ∀ c : EuclideanSpace ℝ (Fin 2), IsPreconnected {x : M | x ∈ N ∧ u x = c}) :
    ∀ x ∈ N, ∀ y ∈ N, u x = u y → ∃ s : ℝ, y = Φ 0 s x := by
  classical
  intro x hxN y hyN hxy
  -- the local claim, for every point of `N`
  have hloc : ∀ z : M, ∃ Vn : Set M, (z ∈ N → IsOpen Vn ∧ z ∈ Vn ∧
      ∀ w ∈ Vn, w ∈ N → u w = u z → ∃ s : ℝ, w = Φ 0 s z) := by
    intro z
    by_cases hz : z ∈ N
    · obtain ⟨Vn, h1, h2, h3⟩ :=
        Work.Diff.Dim2.level_nbhd (N := N) (V := V) (Φ := Φ) (u := u)
          hN hVnz hΦsm hΦself hΦderiv hu huV huinj hdim z hz
      exact ⟨Vn, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨Set.univ, fun hz' => absurd hz' hz⟩
  choose Vn hVn using hloc
  -- the level set through `x` and the flow line of `x`
  set C : Set M := {w : M | w ∈ N ∧ u w = u x} with hC
  set O : Set M := {w : M | ∃ s : ℝ, w = Φ 0 s x} with hO
  have hCconn : IsPreconnected C := by
    have h := hconn (u x)
    simpa [hC] using h
  -- the two open sets covering `C`
  set U : Set M := ⋃ z ∈ C ∩ O, Vn z with hU
  set U' : Set M := ⋃ z ∈ C \ O, Vn z with hU'
  have hUopen : IsOpen U := by
    rw [hU]
    refine isOpen_iUnion (fun z => isOpen_iUnion (fun hz => ?_))
    exact (hVn z ((hC ▸ hz.1).1)).1
  have hU'open : IsOpen U' := by
    rw [hU']
    refine isOpen_iUnion (fun z => isOpen_iUnion (fun hz => ?_))
    exact (hVn z ((hC ▸ hz.1).1)).1
  have hCsub : C ⊆ U ∪ U' := by
    intro w hwC
    by_cases hwO : w ∈ O
    · exact Or.inl (Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr
        ⟨⟨hwC, hwO⟩, (hVn w ((hC ▸ hwC).1)).2.1⟩⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr
        ⟨⟨hwC, hwO⟩, (hVn w ((hC ▸ hwC).1)).2.1⟩⟩)
  -- on `C` the two open sets are disjoint
  have hkey : ¬ (C ∩ (U ∩ U')).Nonempty := by
    rintro ⟨w, hwC, hwU, hwU'⟩
    obtain ⟨z, hwV⟩ := Set.mem_iUnion.mp hwU
    obtain ⟨hzCO, hwV⟩ := Set.mem_iUnion.mp hwV
    obtain ⟨z', hwV'⟩ := Set.mem_iUnion.mp hwU'
    obtain ⟨hz'CO, hwV'⟩ := Set.mem_iUnion.mp hwV'
    have hwN : w ∈ N := (hC ▸ hwC).1
    have hwu : u w = u x := (hC ▸ hwC).2
    have hzN : z ∈ N := (hC ▸ hzCO.1).1
    have hzu : u z = u x := (hC ▸ hzCO.1).2
    have hz'N : z' ∈ N := (hC ▸ hz'CO.1).1
    have hz'u : u z' = u x := (hC ▸ hz'CO.1).2
    -- `w` lies on the flow line of `z`, and `z` on that of `x`
    obtain ⟨a, ha⟩ := (hVn z hzN).2.2 w hwV hwN (by rw [hwu, hzu])
    obtain ⟨s, hs⟩ := hzCO.2
    have hwO : w ∈ O := ⟨a + s, by rw [ha, hs, phi_flow_add hVsm hΦself hΦderiv a s x]⟩
    -- `w` also lies on the flow line of `z'`, so `z'` lies on the flow line of `x`
    obtain ⟨b, hb⟩ := (hVn z' hz'N).2.2 w hwV' hwN (by rw [hwu, hz'u])
    have hz'w : ∃ a : ℝ, z' = Φ 0 a w := by
      refine ⟨-b, ?_⟩
      have h1 : Φ 0 (-b) w = Φ 0 (-b) (Φ 0 b z') := by rw [← hb]
      rw [h1, phi_flow_add hVsm hΦself hΦderiv (-b) b z',
        show -b + b = 0 from by ring, hΦself]
    obtain ⟨c, hc⟩ := hwO
    have hiff := phi_orbit_congr hVsm hΦself hΦderiv (x := x) (z := w) (s := c)
      (by rw [hc]) z'
    exact hz'CO.2 (hiff.mp hz'w)
  have hxU : x ∈ C ∩ U := by
    refine ⟨⟨hxN, rfl⟩, ?_⟩
    exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨⟨⟨hxN, rfl⟩, ⟨0, (hΦself 0 x).symm⟩⟩,
      (hVn x hxN).2.1⟩⟩
  have hne : ¬ (C ∩ U').Nonempty := by
    rintro ⟨w, hwC, hwU'⟩
    exact hkey (hCconn U U' hUopen hU'open hCsub ⟨x, hxU⟩ ⟨w, hwC, hwU'⟩)
  -- hence `C ⊆ U`, and `y ∈ C` lies on the flow line of `x`
  have hyC : y ∈ C := ⟨hyN, hxy.symm⟩
  have hyU : y ∈ U := by
    rcases hCsub hyC with h | h
    · exact h
    · exact absurd ⟨y, hyC, h⟩ hne
  obtain ⟨z, hy⟩ := Set.mem_iUnion.mp hyU
  obtain ⟨hzCO, hyV⟩ := Set.mem_iUnion.mp hy
  have hzN : z ∈ N := (hC ▸ hzCO.1).1
  have hzu : u z = u x := (hC ▸ hzCO.1).2
  have hyu : u y = u z := by rw [hzu]; exact hxy.symm
  obtain ⟨a, ha⟩ := (hVn z hzN).2.2 y hyV hyN hyu
  obtain ⟨s, hs⟩ := hzCO.2
  exact ⟨a + s, by rw [ha, hs, phi_flow_add hVsm hΦself hΦderiv a s x]⟩

end

end Work.Diff.Dim2
