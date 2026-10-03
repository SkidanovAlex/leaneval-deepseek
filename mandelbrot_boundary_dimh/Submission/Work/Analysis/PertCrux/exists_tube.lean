import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# A compact basin tube over `d.φ '' K` (`Work.Analysis.PertCrux.exists_tube`)

Given the §4.1 data `d : ParabData f₀ D₀` and a compact `K ⊆ d.DE`, we produce a compact set `T`
containing a uniform ball around every point of `d.φ '' K`, all of whose points have their whole
forward orbit inside `D₀` and converge to `0` *uniformly* on `T`.

The construction is the compactness argument behind the definition of the parabolic basin
(`MandelDim.ParabolicBasin f₀ D₀`): each point `d.φ w` (`w ∈ K`) of the basin comes with an
*open* neighbourhood `U w` on which all iterates of `f₀` stay in `D₀` and converge to `0`
uniformly.  The compact image `d.φ '' K` is covered by finitely many of these (`U` restricted to
the subtype `↥(d.φ '' K)`), so their union `Ubig` is an open neighbourhood of `d.φ '' K`; the
Lebesgue-number lemma `IsCompact.exists_cthickening_subset_open` then gives `δ > 0` with
`cthickening δ (d.φ '' K) ⊆ Ubig`.  We take `ε₀ = δ/2` and `T = cthickening δ (d.φ '' K)`:
closed and bounded, hence compact; every `ball (d.φ w) ε₀` lies in `cthickening δ (d.φ '' K)`
since `infEDist ≤ edist`; `T ⊆ Ubig` inherits the invariance `f₀^[n] '' T ⊆ D₀` pointwise, and
the uniform convergence of the finite union (via `Set.Finite.eventually_all`) restricts to `T`.
-/

namespace Work.Analysis.PertCrux

open Metric Filter Topology Set

set_option linter.unusedVariables false in
theorem exists_tube {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ T : Set ℂ, IsCompact T ∧
      (∀ w ∈ K, Metric.ball (d.φ w) ε₀ ⊆ T) ∧
      (∀ y ∈ T, ∀ n : ℕ, f₀^[n] y ∈ D₀) ∧
      (∀ ρ : ℝ, 0 < ρ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ y ∈ T, ‖f₀^[n] y‖ < ρ) := by
  classical
  have hKsub : K ⊆ d.Dφ := fun w hw => (hK hw).1
  have hbas : ∀ w ∈ K, d.φ w ∈ MandelDim.ParabolicBasin f₀ D₀ := fun w hw => (hK hw).2
  -- the image of the compact `K` is compact (this is the set the tube is built around)
  have hS : IsCompact (d.φ '' K) :=
    hKc.image_of_continuousOn (d.φ_holo.continuousOn.mono hKsub)
  -- each point of `d.φ '' K` is a basin point: it has an OPEN neighbourhood on which the iterates
  -- stay in `D₀` and converge uniformly to `0`
  have hex : ∀ z : ↥(d.φ '' K), ∃ U : Set ℂ, IsOpen U ∧ (z : ℂ) ∈ U ∧
      (∀ n : ℕ, MapsTo (f₀^[n]) U D₀) ∧
      TendstoUniformlyOn (fun n : ℕ => f₀^[n]) (fun _ => (0 : ℂ)) atTop U := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hwK, rfl⟩ := hz
    obtain ⟨V, hVne, hVmaps, hVconv⟩ := hbas w hwK
    obtain ⟨O, hOV, hOopen, hzO⟩ := _root_.mem_nhds_iff.mp hVne
    exact ⟨O, hOopen, hzO, fun n => (hVmaps n).mono hOV (Subset.rfl), hVconv.mono hOV⟩
  choose U hUopen hmemU hmapU hconvU using hex
  -- finitely many of these neighbourhoods still cover `d.φ '' K`
  have hcover : d.φ '' K ⊆ ⋃ i ∈ (Set.univ : Set ↥(d.φ '' K)), U i := by
    intro x hx
    exact Set.mem_biUnion (Set.mem_univ _) (hmemU ⟨x, hx⟩)
  obtain ⟨b', hb'sub, hb'fin, hb'cov⟩ :=
    hS.elim_finite_subcover_image (fun i _ => hUopen i) hcover
  have hUbig_open : IsOpen (⋃ i ∈ b', U i) :=
    isOpen_iUnion fun i => isOpen_iUnion fun _ => hUopen i
  -- the Lebesgue number: some full `δ`-neighbourhood of `d.φ '' K` lies in the union
  obtain ⟨δ, hδpos, hδsub⟩ := hS.exists_cthickening_subset_open hUbig_open hb'cov
  refine ⟨δ / 2, by linarith, Metric.cthickening δ (d.φ '' K), ?_, ?_, ?_, ?_⟩
  · -- the tube is closed and bounded, hence compact
    have hbdd : Bornology.IsBounded (Metric.cthickening δ (d.φ '' K)) := hS.isBounded.cthickening
    simpa [Metric.isClosed_cthickening.closure_eq] using hbdd.isCompact_closure
  · -- `ball (d.φ w) (δ/2) ⊆ cthickening δ (d.φ '' K)`
    intro w hw y hy
    rw [Metric.mem_cthickening_iff]
    have hy' : ‖y - d.φ w‖ < δ / 2 := by
      rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy
    calc Metric.infEDist y (d.φ '' K) ≤ edist y (d.φ w) :=
          Metric.infEDist_le_edist_of_mem ⟨w, hw, rfl⟩
      _ = ENNReal.ofReal (dist y (d.φ w)) := edist_dist _ _
      _ = ENNReal.ofReal ‖y - d.φ w‖ := by rw [dist_eq_norm]
      _ ≤ ENNReal.ofReal (δ / 2) := ENNReal.ofReal_le_ofReal (le_of_lt hy')
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (by linarith)
  · -- the invariance `f₀^[n] '' T ⊆ D₀`, pointwise from the covering neighbourhoods
    intro y hy n
    have hyU : y ∈ ⋃ i ∈ b', U i := hδsub hy
    rw [Set.mem_iUnion] at hyU; obtain ⟨i, hyU⟩ := hyU
    rw [Set.mem_iUnion] at hyU; obtain ⟨hib, hyU⟩ := hyU
    exact hmapU i n hyU
  · -- uniform convergence to `0` on the tube
    intro ρ hρ
    have hUnif : TendstoUniformlyOn (fun n : ℕ => f₀^[n]) (fun _ => (0 : ℂ)) atTop
        (⋃ i ∈ b', U i) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have h1 : ∀ᶠ n : ℕ in atTop, ∀ i ∈ b', ∀ x ∈ U i, dist (0 : ℂ) (f₀^[n] x) < ε := by
        rw [Set.Finite.eventually_all hb'fin]
        intro i hi
        exact (Metric.tendstoUniformlyOn_iff.mp (hconvU i)) ε hε
      refine h1.mono ?_
      intro n hn x hx
      rw [Set.mem_iUnion] at hx; obtain ⟨i, hx⟩ := hx
      rw [Set.mem_iUnion] at hx; obtain ⟨hib, hx⟩ := hx
      exact hn i hib x hx
    have hUnifT : TendstoUniformlyOn (fun n : ℕ => f₀^[n]) (fun _ => (0 : ℂ)) atTop
        (Metric.cthickening δ (d.φ '' K)) := hUnif.mono hδsub
    rw [Metric.tendstoUniformlyOn_iff] at hUnifT
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hUnifT ρ hρ)
    exact ⟨N, fun n hn y hy => by
      have h := hN n hn y hy
      rwa [dist_zero_left] at h⟩

end Work.Analysis.PertCrux
