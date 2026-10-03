import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.basinCoord.exists_basin_coordinate
import Submission.Work.Parab.petalExtras.petal_conn_sc_image
import Submission.Work.Parab.basinEnters.petal_capture
import Submission.Work.Parab.basinEnters.zero_not_mem_basin
import Submission.Work.Parab.basinGood.basin_good_exists

/-!
# Petal data for a parabolic germ

This file assembles the ingredients that HORN needs about an *unperturbed* parabolic germ
`g` on `D`:

* a Fatou/Abel coordinate `Φ` on the whole parabolic basin (`Work.Parab.basinCoord.exists_basin_coordinate`),
* a petal `V = Petal r M` that is open, connected, simply connected, avoids `0`, lies in `D`
  and in the basin, is `g`-invariant, accumulates at `0` (so meets any neighbourhood `D' ∋ 0`),
* on which `Φ` is injective and whose `Φ`-image contains the tail of every horizontal strip
  (`Work.Parab.petalExtras.petal_conn_sc_image`, which needs `1 / r < M` and identifies the
  petal with the disc of diameter `[-1/M, 0]`),
* and such that every basin orbit that never hits `0` eventually enters `V`
  (`Work.Parab.basinEnters.exists_iterate_mem_petal`).

The one point that needs care is the bookkeeping of the radius: the petal coordinate used by
`Φ` is `fatouCoord g (1 - a)` for the *same* `ParabolicBounds g h a r A A'` as the petal, so we
use the data returned by `exists_basin_coordinate` itself, raise the petal level `M` above
`1 / r` (which makes the petal a genuine disc, hence simply connected, and gives the strip
covering) and above the level of `exists_petal_level_facts` (which gives `g`-invariance).  The
petal-capture step needs a *smaller* radius; `Work.Parab.basinGood.exists_small_bounds` shrinks
`r` without changing `h, a, A, A'`, and a smaller petal is contained in the larger one.
-/

namespace Work.Horn.HB

open MandelDim Set Metric Filter Topology

/-- The petal `Petal r M = {‖z‖ < r, Re(-1/z) > M}` meets every ball around `0` (the points
`-t`, `0 < t < 1/M`, lie in it). -/
theorem exists_mem_petal_inter_ball {r M ε : ℝ} (hr : 0 < r) (hM : 0 < M) (hε : 0 < ε) :
    ∃ z ∈ Work.FatouCoord.Petal r M, ‖z‖ < ε := by
  set t : ℝ := min (min r (1 / M)) ε / 2 with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have htr : t < r := by
    rw [ht]
    have h1 : min (min r (1 / M)) ε ≤ min r (1 / M) := min_le_left _ _
    have h2 : min r (1 / M) ≤ r := min_le_left _ _
    linarith
  have htM : t < 1 / M := by
    rw [ht]
    have h1 : min (min r (1 / M)) ε ≤ min r (1 / M) := min_le_left _ _
    have h2 : min r (1 / M) ≤ 1 / M := min_le_right _ _
    linarith
  have htε : t < ε := by
    rw [ht]
    have h1 : min (min r (1 / M)) ε ≤ ε := min_le_right _ _
    linarith
  have hMt : M * t < 1 := by rw [mul_comm]; exact (lt_div_iff₀ hM).mp htM
  have hkey : M * t ^ 2 < t := by nlinarith [htpos, hMt]
  refine ⟨-((t : ℝ) : ℂ), ?_, ?_⟩
  · rw [Work.FatouCoord.mem_Petal]
    refine ⟨?_, ?_⟩
    · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htpos.le]
      exact htr
    · rw [Complex.neg_re, Complex.ofReal_re, Complex.normSq_neg, Complex.normSq_ofReal]
      nlinarith [hkey]
  · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htpos.le]
    exact htε

/-- **Petal data.**  For a parabolic germ `g` on `D` and any neighbourhood `D'` of `0` there are
a Fatou coordinate `Φ` of the parabolic basin and a petal `V ∋ x` with all the properties needed
by the HORN leaf. -/
theorem exists_petal_data {g : ℂ → ℂ} {D D' : Set ℂ} (hg : MandelDim.IsParabolicGerm g D)
    (hD'o : IsOpen D') (h0D' : (0 : ℂ) ∈ D') :
    ∃ (Φ : ℂ → ℂ) (V : Set ℂ) (x : ℂ),
      IsOpen V ∧ IsConnected V ∧ SimplyConnectedSpace ↥V ∧ (0 : ℂ) ∉ V ∧ x ∈ V ∧ V ⊆ D ∧
      (V ∩ D').Nonempty ∧ V ⊆ MandelDim.ParabolicBasin g D ∧ Set.MapsTo g V V ∧
      DifferentiableOn ℂ Φ (MandelDim.ParabolicBasin g D) ∧
      (∀ z ∈ MandelDim.ParabolicBasin g D, Φ (g z) = Φ z + 1) ∧
      Set.InjOn Φ V ∧
      (∀ b : ℝ, ∃ C : ℝ, ∀ w : ℂ, C < w.re → |w.im| ≤ b → ∃ z ∈ V, Φ z = w) ∧
      (∀ z ∈ MandelDim.ParabolicBasin g D, (∀ n : ℕ, (g^[n]) z ≠ 0) →
        ∃ n : ℕ, (g^[n]) z ∈ V) := by
  classical
  -- the basin coordinate, together with the quantitative data of its construction
  obtain ⟨Φ, h, a, r, A, A', M, hb, hball, hMpos, hPsub, _hmaps, _hconv, hdiffΦ, habelΦ, hinjΦ,
    hagree⟩ := Work.Parab.basinCoord.exists_basin_coordinate hg
  have hr : 0 < r := hb.hr
  -- a smaller radius with the petal-capture smallness, same `h, a, A, A'`
  obtain ⟨r', hr'pos, hr'le, hr'16, hsmall', hb'⟩ := Work.Parab.basinGood.exists_small_bounds hb
  -- the level above which the petal is forward invariant and carries the Fatou coordinate
  obtain ⟨M₀, _hM₀pos, hM₀⟩ := Work.Parab.basinCoord.exists_petal_level_facts hb
  -- the chosen petal level
  let M' : ℝ := max (max M (1 / r + 1)) M₀
  have hMM' : M ≤ M' := le_trans (le_max_left M (1 / r + 1)) (le_max_left _ _)
  have hM₀M' : M₀ ≤ M' := le_max_right _ _
  have hM'pos : 0 < M' := lt_of_lt_of_le hMpos hMM'
  have hM'r : 1 / r < M' := by
    have h1 : 1 / r < max M (1 / r + 1) := by
      have : (1 : ℝ) / r < 1 / r + 1 := by linarith
      exact lt_of_lt_of_le this (le_max_right _ _)
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  -- `Petal r M'` is contained in `Petal r M`: larger level, smaller petal
  have hmono : Work.FatouCoord.Petal r M' ⊆ Work.FatouCoord.Petal r M :=
    Work.FatouCoord.Petal_mono le_rfl hMM'
  have hagree' : ∀ z ∈ Work.FatouCoord.Petal r M', Φ z = Work.FatouCoord.fatouCoord g (1 - a) z :=
    fun z hz => hagree z (hmono hz)
  -- connectedness, simple connectedness, and the strip-covering property
  obtain ⟨hconn, hsc, hstrip⟩ := Work.Parab.petalExtras.petal_conn_sc_image hb hM'pos hM'r hagree'
  -- forward invariance
  have hmaps' : MapsTo g (Work.FatouCoord.Petal r M') (Work.FatouCoord.Petal r M') :=
    (hM₀ M' hM₀M').1
  -- a point of the petal inside `D'`
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hD'o.mem_nhds h0D')
  obtain ⟨x, hxV, hxε⟩ := exists_mem_petal_inter_ball (r := r) (M := M') hr hM'pos hεpos
  have hxD' : x ∈ D' := hεsub (by simpa [Metric.mem_ball, dist_eq_norm] using hxε)
  refine ⟨Φ, Work.FatouCoord.Petal r M', x, Work.FatouCoord.isOpen_Petal, hconn, hsc,
    Work.FatouCoord.not_mem_Petal_zero, hxV, ?_, ⟨x, hxV, hxD'⟩, ?_, hmaps', hdiffΦ, habelΦ,
    ?_, hstrip, ?_⟩
  · -- `Petal r M' ⊆ D`
    intro z hz
    exact hball (Work.FatouCoord.Petal_subset_ball hz)
  · -- `Petal r M' ⊆ ParabolicBasin g D`
    intro z hz
    exact hPsub (hmono hz)
  · -- injectivity of `Φ` on the petal
    intro z hz z' hz' heq
    exact hinjΦ (hmono hz) (hmono hz') heq
  · -- capture: every zero-avoiding basin orbit enters the petal
    intro z hz hne
    obtain ⟨n, hn⟩ := Work.Parab.basinEnters.exists_iterate_mem_petal hb' hr'16 hsmall' hM'pos
      (Work.Parab.basinEnters.tendsto_iterate_of_mem_basin hz) hne
    exact ⟨n, Work.FatouCoord.Petal_mono hr'le le_rfl hn⟩

end Work.Horn.HB
