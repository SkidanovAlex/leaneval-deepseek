import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.exists_distinct_criticalValues
import Submission.Work.Drive.N2.exists_disjoint_chart_neighborhoods
import Submission.Work.Drive.N2.exists_morseChart_fixed
import Submission.Work.Drive.N2.exists_modelChart_data
import Submission.Work.Drive.N2.exists_modelRadii_separated
import Submission.Work.Drive.N2.exists_modelAdapted_levelFlow_chartODE
import Submission.Work.Drive.N2.levelMonoOn_of_modelAdaptedFlow

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

/-- A finite-valued injective real function on a finite type has a positive minimal gap between the
values at distinct indices. -/
private lemma exists_pos_gap {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (hinj : Function.Injective g) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j : ι, i ≠ j → δ < |g i - g j| := by
  classical
  let S : Finset (ι × ι) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  by_cases hS : S.Nonempty
  · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image S (fun p : ι × ι => |g p.1 - g p.2|) hS
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hpos : 0 < |g p.1 - g p.2| :=
      abs_pos.mpr (fun h => hpne (hinj (sub_eq_zero.mp h)))
    refine ⟨|g p.1 - g p.2| / 2, half_pos hpos, fun i j hij => ?_⟩
    have hijS : (i, j) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
    have hle := hmin (i, j) hijS
    linarith
  · refine ⟨1, one_pos, fun i j hij => ?_⟩
    exact absurd ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩ hS

/-- The complement of an open interval gives a non-strict absolute-value bound. -/
private lemma le_abs_of_notMem_Ioo {c v η : ℝ} (h : v ∉ Set.Ioo (c - η) (c + η)) :
    η ≤ |v - c| := by
  have h' : v ≤ c - η ∨ c + η ≤ v := by
    by_contra hc
    push_neg at hc
    exact h ⟨hc.1, hc.2⟩
  rcases h' with h' | h'
  · rcases lt_or_ge η 0 with hη | hη
    · exact le_trans (le_of_lt hη) (abs_nonneg _)
    · rw [abs_of_nonpos (by linarith : v - c ≤ 0)]
      linarith
  · calc η ≤ v - c := by linarith
      _ ≤ |v - c| := le_abs_self _

/-- **Existence of the window datum.**  A Morse function with distinct critical values on a compact
surface carries the whole `n = 2` window datum at any of its critical points.

The proof is the bookkeeping announced in `Submission/Work/Drive/N2/windowDatum.lean`: enumerate the
critical points (`exists_injective_enum_critical`), separate them by disjoint chart neighbourhoods
(`exists_disjoint_chart_neighborhoods`), take the plane Morse normal form at each
(`exists_morseChart_fixed`), shrink each chart into its prescribed neighbourhood keeping a compact
region (`exists_shrunk_chart_data`), pick the model radii with the strict value separation
(`exists_modelRadii_separated`, plus the minimal gap of the finitely many distinct critical values),
build the model-adapted level flow (`exists_modelAdapted_levelFlow_chartODE`) and read off the
monotonicity (`levelMonoOn_of_modelAdaptedFlow`). -/
theorem windowDatumExists {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : Work.Drive.Morse.IsMorseDistinct f) (hmorse : Work.Drive.Morse.MorseLemma2)
    {p : M} (hp : Work.Drive.Morse.IsCritical f p) :
    Nonempty (Work.Drive.N2.WindowDatum f p) := by
  classical
  obtain ⟨hfm, hnd, hdistinct⟩ := hf
  -- enumerate the critical points
  obtain ⟨k, x, hinj, hcrit, hcover⟩ := exists_injective_enum_critical f hfm hnd
  obtain ⟨j, hj⟩ := hcover p hp
  -- disjoint chart neighbourhoods
  obtain ⟨T, hTopen, hTmem, _hTclsub, _hisoT, hTdisj⟩ :=
    exists_disjoint_chart_neighborhoods f hfm hnd x hinj hcrit hcover
  -- the plane Morse normal form at each critical point
  choose φ₀ s₁ s₂ hφ₀src hφ₀cen hsgn₁ hsgn₂ hφ₀sm hφ₀symm hφ₀val using fun i : Fin k =>
    exists_morseChart_fixed hfm (hnd (x i) (hcrit i)) hmorse
  have hsgn : ∀ i : Fin k,
      (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1) :=
    fun i => ⟨hsgn₁ i, hsgn₂ i⟩
  -- shrink each chart into its prescribed neighbourhood, keeping a compact region
  choose χ r₀ C₀ hr₀pos hχsrc hχcen hχsub hχsm hχsymm hχval hC₀sub hC₀comp hC₀clsub hC₀op using
    fun i : Fin k =>
      exists_shrunk_chart_data f (x i) (φ₀ i) (s₁ i) (s₂ i) (hφ₀src i) (hφ₀cen i) (hφ₀sm i)
        (hφ₀symm i) (hφ₀val i) (T := T i) ((hTopen i).mem_nhds (hTmem i))
  have hdisj : ∀ i j' : Fin k, i ≠ j' → Disjoint (χ i).source (χ j').source := by
    intro i j' hij
    exact Disjoint.mono (subset_trans (hχsub i) subset_closure)
      (subset_trans (hχsub j') subset_closure) (hTdisj i j' hij)
  have hvalChartQ : ∀ (i : Fin k) (y : M), y ∈ (χ i).source →
      f y = f (x i) + chartQ (χ i) (s₁ i) (s₂ i) y := by
    intro i y hy
    have h := hχval i y hy
    rw [chartQ]
    linarith
  -- the critical values are distinct, so their minimal gap is positive
  have hFinj : Function.Injective (fun i : Fin k => f (x i)) := by
    intro i j' hij
    exact hinj (hdistinct (x i) (x j') (hcrit i) (hcrit j') hij)
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_gap (fun i : Fin k => f (x i)) hFinj
  set η : ℝ := δ / 2 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  have hdist : ∀ i j' : Fin k, i ≠ j' → 2 * η < |f (x i) - f (x j')| := by
    intro i j' hij
    have h1 := hδ i j' hij
    rw [hηdef]
    linarith
  -- the model radii with the value separation
  obtain ⟨rsep, hrseppos, _hxrsep, hsepIoo⟩ :=
    exists_modelRadii_separated f x χ s₁ s₂ hχsrc hχcen hvalChartQ hηpos hdist
  -- the separation constant of the datum
  set ηd : ℝ := min (η / 4) (1 / 20) with hηddef
  have hηdpos : 0 < ηd := by
    rw [hηddef]; exact lt_min (by linarith) (by norm_num)
  have hηdlt : ηd < 1 / 10 := by
    rw [hηddef]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hηdltη : 2 * ηd < η := by
    rw [hηddef]
    have := min_le_left (η / 4) (1 / 20)
    linarith
  -- the radii of the flow balls
  set rad : Fin k → ℝ := fun i => min (r₀ i / 16) (rsep i) with hraddef
  have hradpos : ∀ i, 0 < rad i := by
    intro i
    rw [hraddef]
    exact lt_min (by have := hr₀pos i; linarith) (hrseppos i)
  have hradle_rsep : ∀ i, rad i ≤ rsep i := by
    intro i; rw [hraddef]; exact min_le_right _ _
  have hradlt_r₀ : ∀ i, rad i < r₀ i := by
    intro i
    have h1 : rad i ≤ r₀ i / 16 := by rw [hraddef]; exact min_le_left _ _
    have h2 := hr₀pos i
    linarith
  have h8rad_lt_r₀ : ∀ i, 8 * rad i < r₀ i := by
    intro i
    have h1 : rad i ≤ r₀ i / 16 := by rw [hraddef]; exact min_le_left _ _
    have h2 := hr₀pos i
    linarith
  -- the closed chart regions
  have hCsub : ∀ i : Fin k, closure (C₀ i) ⊆ (χ i).source := hC₀clsub
  have hCclsub : ∀ i : Fin k, closure (closure (C₀ i)) ⊆ (χ i).source := by
    intro i; rw [closure_closure]; exact hC₀clsub i
  have hCball : ∀ i : Fin k, modelBall (χ i) (rad i) ⊆ closure (C₀ i) := by
    intro i y hy
    exact subset_closure (hC₀op i ⟨hy.1, lt_trans hy.2 (hradlt_r₀ i)⟩)
  have hCop : ∀ i : Fin k,
      {y : M | y ∈ (χ i).source ∧ ‖χ i y‖ < 8 * rad i} ⊆ closure (C₀ i) := by
    intro i y hy
    exact subset_closure (hC₀op i ⟨hy.1, lt_trans hy.2 (h8rad_lt_r₀ i)⟩)
  -- every point outside all the regions is not critical
  have hCcrit : ∀ y : M, (∀ i : Fin k, y ∉ closure (C₀ i)) →
      ¬ Work.Drive.Morse.IsCritical f y := by
    intro y hy hyc
    obtain ⟨i, hi⟩ := hcover y hyc
    refine hy i ?_
    rw [← hi]
    exact hCball i ⟨hχsrc i, by rw [hχcen i, norm_zero]; exact hradpos i⟩
  -- the model-adapted level flow
  obtain ⟨Φ, hΦsm, hΦ0, hΦcomp, hΦlevel, hΦODE⟩ :=
    exists_modelAdapted_levelFlow_chartODE f hfm x χ s₁ s₂ rad hradpos hχsrc hχcen hsgn
      hvalChartQ hχsm hχsymm hdisj (fun i => closure (C₀ i)) hCsub
      (fun i => ⟨by rw [closure_closure]; exact hC₀comp i, hCclsub i⟩) hCball hCcrit
  -- the level law of the datum
  have hlevelDatum : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i : Fin k,
        Φ (u, y) ∉ modelBall (χ i) ((8 * rad i) / 8)) →
      f (Φ (t, y)) = f y + t := by
    intro y t hconf
    refine hΦlevel y t ?_ ?_
    · intro i
      have h0 : (0 : ℝ) ∈ Set.Icc (min 0 t) (max 0 t) :=
        ⟨min_le_left 0 t, le_max_left 0 t⟩
      have h := hconf 0 h0 i
      rw [show (8 * rad i) / 8 = rad i by ring] at h
      simpa only [hΦ0] using h
    · intro u hu i
      have h := hconf u hu i
      rwa [show (8 * rad i) / 8 = rad i by ring] at h
  -- the chart ODE of the datum
  have hODEDatum : ∀ (i : Fin k) (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ closure (C₀ i)) →
      HasDerivAt (fun σ : ℝ => χ i (Φ (σ, y)) 0)
        (chartMult ((8 * rad i) / 8) (‖χ i (Φ (t, y))‖ ^ 2) *
          (s₁ i * χ i (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => χ i (Φ (σ, y)) 1)
        (chartMult ((8 * rad i) / 8) (‖χ i (Φ (t, y))‖ ^ 2) *
          (s₂ i * χ i (Φ (t, y)) 1)) t := by
    intro i y t hconv
    have h8 : (8 * rad i) / 8 = rad i := by ring
    rw [h8]
    exact hΦODE i y t hconv
  -- monotonicity along the orbits
  have hmono : ∀ y : M, MonotoneOn (fun t : ℝ => f (Φ (t, y))) (Set.Ici 0) :=
    levelMonoOn_of_modelAdaptedFlow f hfm x χ s₁ s₂ rad hradpos hsgn hvalChartQ
      (fun i => closure (C₀ i)) hCsub hCclsub hCball Φ hΦsm hΦ0 hΦcomp hΦlevel hΦODE
  -- the separation rows
  have hsepDatum : ∀ i j' : Fin k, i ≠ j' → 2 * ηd < |f (x i) - f (x j')| := by
    intro i j' hij
    have h1 := hδ i j' hij
    have h2 : 2 * ηd ≤ η / 2 := by
      rw [hηddef]
      have := min_le_left (η / 4) (1 / 20)
      linarith
    have h3 : η / 2 < δ := by rw [hηdef]; linarith
    linarith
  have hsepKDatum : ∀ i j' : Fin k, i ≠ j' → ∀ z : M,
      z ∈ modelBall (χ i) ((8 * rad i) / 8) → 2 * ηd < |f z - f (x j')| := by
    intro i j' hij z hz
    have h8 : (8 * rad i) / 8 = rad i := by ring
    rw [h8] at hz
    have hz' : z ∈ modelBall (χ i) (rsep i) := ⟨hz.1, lt_of_lt_of_le hz.2 (hradle_rsep i)⟩
    have hle := le_abs_of_notMem_Ioo (hsepIoo i j' hij z hz')
    linarith [hηdltη]
  exact ⟨{ N := k, x := x, φ := χ, s₁ := s₁, s₂ := s₂, ρ := fun i => 8 * rad i,
            C := fun i => closure (C₀ i), j := j, hxj := hj, hinj := hinj, hcrit := hcrit,
            hcover := hcover, hρ := fun i => by have := hradpos i; linarith, hsrc := hχsrc,
            hcen := hχcen, hsgn := hsgn, hval := hvalChartQ, hφ := hχsm, hφ' := hχsymm,
            hdisj := hdisj, hCsub := hCsub, hCclosed := fun _ => isClosed_closure,
            hCcl := fun i => ⟨by rw [closure_closure]; exact hC₀comp i, hCclsub i⟩,
            hCball := fun i => by
              have h8 : (8 * rad i) / 8 = rad i := by ring
              rw [h8]; exact hCball i,
            hCop := hCop, ηd := ηd, hηd := hηdpos, hηd' := hηdlt, hsep := hsepDatum,
            hsepK := hsepKDatum, Φ := Φ, hΦsm := hΦsm, hΦ0 := hΦ0, hΦcomp := hΦcomp,
            hlevel := hlevelDatum, hODE := hODEDatum, hmono := hmono }⟩

end Work.Drive.N2
