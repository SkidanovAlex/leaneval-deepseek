import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.immediate_basins_of_petals

namespace Work.Horn.PetalImLocal

open MandelDim Filter Set Metric Topology
open scoped Topology

/-! # Component-local invariance of a parabolic basin component

This file adapts `Work.Horn.ImmBasins.image_eq_self_of_isPreconnected` (in
`Submission/Work/Horn/immediate_basins_of_petals.lean`) so that the *global* properness hypothesis
`∀ K ⊆ P, IsCompact (P ∩ f ⁻¹' K)` is replaced by properness *relative to the component* `B`, and
the hypothesis `hBcl` (`B` closed inside the basin) is dropped in favour of maximality `hmax` of `B`
among preconnected subsets of the basin.

The one step that consumes properness, `Work.Horn.ImmBasins.mem_image_of_mem_closure`, is adapted
below: the closed ball around a point `z ∈ B` lies in `B` by `hmax` (a ball is convex, hence
preconnected, and meets `B`), so it is a legitimate compact subset of `B` for the relative
properness hypothesis; and the approximating preimages are chosen *in* `B` by construction, so
`hBcl` is not needed. -/

/-- **Component-local compactness step.**  Let `B ⊆ P = ParabolicBasin f D` be maximal among
preconnected subsets of `P` (`hmax`), and suppose `f` is proper relative to `B` (`hproper`).  Then
for `z ∈ B` which is a limit point of `f '' B`, we have `z ∈ f '' B`.

Indeed, take a closed ball `L = closedBall z r` around `z` contained in the (open) basin `P`; by
`hmax` (a ball is convex, hence preconnected, and contains `z ∈ B`) we have `L ⊆ B`.  Pull the
approximating points `f (w n) ∈ L` back: the `w n` lie in the compact `B ∩ f ⁻¹' L`, so a
subsequence converges to some `a ∈ B`; then `z = f a` and `z ∈ f '' B`. -/
theorem mem_image_of_mem_closure {f : ℂ → ℂ} {D B : Set ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hBsub : B ⊆ MandelDim.ParabolicBasin f D)
    (hmax : ∀ s : Set ℂ, IsPreconnected s → s ⊆ MandelDim.ParabolicBasin f D →
      (B ∩ s).Nonempty → s ⊆ B)
    (hproper : ∀ K : Set ℂ, K ⊆ B → IsCompact K → IsCompact (B ∩ f ⁻¹' K))
    {z : ℂ} (hzB : z ∈ B) (hzcl : z ∈ closure (f '' B)) :
    z ∈ f '' B := by
  have hbasin_open : IsOpen (MandelDim.ParabolicBasin f D) :=
    Work.Horn.ImmBasins.parabolicBasin_isOpen
  have hbasin_sub : MandelDim.ParabolicBasin f D ⊆ D :=
    Work.Horn.ImmBasins.parabolicBasin_subset_D
  -- a closed ball around `z` contained in the (open) basin
  obtain ⟨ρ, hρ, hρsub⟩ :
      ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall z ρ ⊆ MandelDim.ParabolicBasin f D := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hbasin_open.mem_nhds (hBsub hzB))
    refine ⟨ε / 2, by linarith, fun y hy => hεsub ?_⟩
    have hy' : dist z y ≤ ε / 2 := by simpa [dist_comm] using hy
    have hlt : dist y z < ε := by rw [dist_comm]; linarith
    simpa [Metric.mem_ball] using hlt
  set L : Set ℂ := Metric.closedBall z ρ with hLdef
  -- by maximality, the ball lies in `B`
  have hLpre : IsPreconnected L := by
    rw [hLdef]; exact Metric.isPreconnected_closedBall
  have hLbasin : L ⊆ MandelDim.ParabolicBasin f D := by rw [hLdef]; exact hρsub
  have hLne : (B ∩ L).Nonempty :=
    ⟨z, hzB, by rw [hLdef, Metric.mem_closedBall, dist_self]; exact le_of_lt hρ⟩
  have hLsub : L ⊆ B := hmax L hLpre hLbasin hLne
  have hLc : IsCompact L := by rw [hLdef]; exact isCompact_closedBall z ρ
  have hKc : IsCompact (B ∩ f ⁻¹' L) := hproper L hLsub hLc
  -- approximating preimages, kept inside the compact set `B ∩ f ⁻¹' L`
  have hseq : ∀ n : ℕ, ∃ w ∈ B, dist (f w) z < min (1 / (n + 1 : ℝ)) ρ := by
    intro n
    obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.mp hzcl (min (1 / (n + 1 : ℝ)) ρ)
      (lt_min (by positivity) hρ)
    obtain ⟨w, hwB, rfl⟩ := hy
    exact ⟨w, hwB, by rwa [dist_comm] at hyd⟩
  choose w hwB hwd using hseq
  have hwK : ∀ n : ℕ, w n ∈ B ∩ f ⁻¹' L := by
    intro n
    refine ⟨hwB n, ?_⟩
    rw [Set.mem_preimage, hLdef, Metric.mem_closedBall]
    exact le_of_lt (lt_of_lt_of_le (hwd n) (min_le_right _ _))
  -- pass to a convergent subsequence, landing in `B` by construction
  obtain ⟨a, haK, φ, hφmono, hφlim⟩ := hKc.tendsto_subseq (fun n => hwK n)
  have haB : a ∈ B := haK.1
  have hcont : ContinuousAt f a :=
    hf.continuousOn.continuousAt (hD.mem_nhds (hbasin_sub (hBsub haB)))
  have hlim1 : Tendsto (fun n : ℕ => f (w (φ n))) atTop (𝓝 (f a)) := hcont.tendsto.comp hφlim
  have hlim2 : Tendsto (fun n : ℕ => f (w (φ n))) atTop (𝓝 z) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    have hid : n ≤ φ n := hφmono.id_le n
    have h1 : (1 : ℝ) / (φ n + 1) ≤ 1 / (n + 1 : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hid
    have h2 : dist (f (w (φ n))) z ≤ 1 / (φ n + 1 : ℝ) :=
      le_of_lt (lt_of_lt_of_le (hwd (φ n)) (min_le_left _ _))
    have h3 : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1 : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hn
    calc dist (f (w (φ n))) z ≤ 1 / (φ n + 1 : ℝ) := h2
      _ ≤ 1 / (n + 1 : ℝ) := h1
      _ ≤ 1 / (N + 1 : ℝ) := h3
      _ < ε := hN
  exact ⟨a, haB, tendsto_nhds_unique hlim1 hlim2⟩

/-- **Component-local form of the invariance step.**  Let `B` be an open preconnected subset of the
parabolic basin `P = MandelDim.ParabolicBasin f D` which is *maximal* among preconnected subsets of
`P` (`hmax`), and suppose `f` is proper *relative to `B`* (`hproper`: for compact `K ⊆ B` the set
`B ∩ f ⁻¹' K` is compact).  If `f '' B ⊆ B` and `f` is not constant on `B`, then `f '' B = B`.

This is `Work.Horn.ImmBasins.image_eq_self_of_isPreconnected` (file
`Submission/Work/Horn/immediate_basins_of_petals.lean`) with the *global* properness hypothesis
`∀ K ⊆ P, …IsCompact (P ∩ f ⁻¹' K)` weakened to properness relative to the component `B`, and with
`hBcl` (`B` closed in `P`) no longer needed.  In that file, the auxiliary step
`Work.Horn.ImmBasins.mem_image_of_mem_closure` is the one that consumes the properness; it must be
adapted likewise: a closed ball `closedBall z r ⊆ P` around `z ∈ B` lies in `B` by `hmax` (a ball is
convex, hence preconnected, and contains `z`), and the approximating points `w n ∈ B` stay in
`B ∩ f ⁻¹' (closedBall z r)` automatically because they are chosen in `B` (this is why `hBcl` is not
needed). -/
theorem image_eq_self_of_isPreconnected {f : ℂ → ℂ} {D B : Set ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hBsub : B ⊆ MandelDim.ParabolicBasin f D)
    (hmax : ∀ s : Set ℂ, IsPreconnected s → s ⊆ MandelDim.ParabolicBasin f D →
      (B ∩ s).Nonempty → s ⊆ B)
    (hproper : ∀ K : Set ℂ, K ⊆ B → IsCompact K → IsCompact (B ∩ f ⁻¹' K))
    (hBne : Set.Nonempty B) (hBopen : IsOpen B) (hBpre : IsPreconnected B)
    (hmap : Set.MapsTo f B B) (hnconst : ¬ ∃ c : ℂ, ∀ z ∈ B, f z = c) :
    Set.image f B = B := by
  have hmapsTo : f '' B ⊆ B := Set.mapsTo_iff_image_subset.mp hmap
  have hBsubD : B ⊆ D := fun z hz => Work.Horn.ImmBasins.parabolicBasin_subset_D (hBsub hz)
  -- open mapping theorem: `f '' B` is open (B open preconnected, f holomorphic and non-constant)
  have hopen : IsOpen (f '' B) := by
    rcases (hf.mono hBsubD).analyticOnNhd hBopen |>.is_constant_or_isOpen hBpre with hc | ho
    · exact absurd hc hnconst
    · exact ho B subset_rfl hBopen
  -- and closed inside `B` (the component-local compactness step)
  have hle : B ⊆ f '' B := by
    refine IsPreconnected.subset_left_of_subset_union hopen isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure) ?_ ?_ hBpre
    · intro z hz
      by_cases hzc : z ∈ closure (f '' B)
      · exact Or.inl (mem_image_of_mem_closure hD hf hBsub hmax hproper hz hzc)
      · exact Or.inr hzc
    · obtain ⟨z, hz⟩ := hBne
      exact ⟨f z, hmapsTo ⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩
  exact Set.Subset.antisymm hmapsTo hle

end Work.Horn.PetalImLocal
