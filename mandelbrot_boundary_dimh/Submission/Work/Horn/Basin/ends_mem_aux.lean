import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basin
import Submission.Work.Parab.basinEnters.zero_not_mem_basin

open MandelDim Filter Set Metric Topology
open scoped Topology

namespace Work.Horn.Basin

noncomputable section

/-- Along the ray `w + k` (which keeps the imaginary part) the Fatou coordinate iterates the map:
`φ (w + k) = f₀^[k] (φ w)`, whenever `|Im w| > η₀` (so `ends_sub` applies to every point of the
ray). -/
lemma ray_mem_abs (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (d : MandelDim.ParabData f₀ D₀) :
    ∀ w : ℂ, d.η₀ < |w.im| → ∀ k : ℕ, w + k ∈ d.Dφ ∧ d.φ (w + k) = (f₀^[k]) (d.φ w) := by
  intro w hw k
  have him : ∀ m : ℕ, ((w + m : ℂ)).im = w.im := by intro m; simp
  induction k with
  | zero => exact ⟨by simpa using (d.ends_sub w hw).1, by simp⟩
  | succ n ih =>
      have h1 : w + (n : ℂ) ∈ d.Dφ := ih.1
      have h3 : w + (n : ℂ) + 1 ∈ d.Dφ := by
        have hηn : d.η₀ < |((w + (n : ℂ) + 1 : ℂ)).im| := by
          rw [show ((w + (n : ℂ) + 1 : ℂ)).im = w.im by simp]; exact hw
        exact (d.ends_sub _ hηn).1
      have habel : d.φ (w + (n : ℂ) + 1) = f₀ (d.φ (w + (n : ℂ))) := d.φ_abel _ h1 h3
      have hcast : w + ((n + 1 : ℕ) : ℂ) = w + (n : ℂ) + 1 := by push_cast; ring
      constructor
      · rw [hcast]; exact h3
      · rw [hcast, habel, ih.2, Function.iterate_succ_apply']

/-- **Assembly.**  If the attracting petal `Ωp` of the §4.1 data lies in the immediate basin `B`,
then the two ends of the cylinder land in `B`: `d.φ w ∈ B` for `|Im w|` large.  (The input
`d.Ωp ⊆ B` is *not* a field of `ParabData`: it is Shishikura's "`B` is unique and contains `Ω₊`",
proved in the paper from the connectedness of the petal `Ω₊` — see `omega_subset_B`.) -/
lemma ends_mem_aux (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) (B : Set ℂ) (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hOB : d.Ωp ⊆ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ w : ℂ, η < |w.im| → d.φ w ∈ B := by
  have hg : MandelDim.IsParabolicGerm f₀ D₀ := hF0.1
  have hzero : (0 : ℂ) ∉ MandelDim.ParabolicBasin f₀ D₀ :=
    Work.Parab.basinEnters.zero_not_mem_parabolicBasin hg
  -- one half plane at a time, `s = ±1`
  have key : ∀ (s : ℝ), (s = 1 ∨ s = -1) → ∀ A : Set ℂ,
      A = {u : ℂ | max d.η₀ 1 < s * u.im} → ∀ u ∈ A, d.φ u ∈ B := by
    intro s hs A hAdef u huA
    -- the half plane is contained in the ends
    have hAends : ∀ v ∈ A, d.η₀ < |v.im| := by
      intro v hv
      rw [hAdef] at hv
      have hv1 : max d.η₀ 1 < s * v.im := hv
      have hpos : 0 < s * v.im :=
        lt_trans (lt_of_lt_of_le zero_lt_one (le_max_right d.η₀ 1)) hv1
      have hsv : s * v.im = |v.im| := by
        rcases hs with rfl | rfl
        · rw [one_mul]; exact (abs_of_pos (by simpa using hpos)).symm
        · rw [neg_one_mul]; exact (abs_of_neg (by simpa using hpos)).symm
      rw [← hsv]
      exact lt_of_le_of_lt (le_max_left d.η₀ 1) hv1
    have hADφ : A ⊆ d.Dφ := fun v hv => (d.ends_sub v (hAends v hv)).1
    have hφbasin : ∀ v ∈ A, d.φ v ∈ MandelDim.ParabolicBasin f₀ D₀ :=
      fun v hv => (d.ends_sub v (hAends v hv)).2
    -- convexity of the half plane
    have hconv : Convex ℝ A := by
      intro v hv v' hv' a b ha hb hab
      rw [hAdef] at hv hv' ⊢
      have hv1 : max d.η₀ 1 < s * v.im := hv
      have hv1' : max d.η₀ 1 < s * v'.im := hv'
      have hsm : s * (a • v + b • v').im = a * (s * v.im) + b * (s * v'.im) := by
        simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
        ring
      have hmain : max d.η₀ 1 < s * (a • v + b • v').im := by
        rw [hsm]
        rcases eq_or_lt_of_le ha with ha0 | hapos
        · have hb1 : b = 1 := by linarith [ha0, hab]
          rw [← ha0, hb1, zero_mul, zero_add, one_mul]
          exact hv1'
        · have h1 : a * (max d.η₀ 1) < a * (s * v.im) := mul_lt_mul_of_pos_left hv1 hapos
          have h2 : b * (max d.η₀ 1) ≤ b * (s * v'.im) :=
            mul_le_mul_of_nonneg_left (le_of_lt hv1') hb
          have h3 : a * (max d.η₀ 1) + b * (max d.η₀ 1) = max d.η₀ 1 := by
            rw [← add_mul, hab, one_mul]
          linarith
      exact hmain
    have hpre : IsPreconnected A := hconv.isPreconnected
    have hcont : ContinuousOn d.φ A := (d.φ_holo.mono hADφ).continuousOn
    have hpreB : IsPreconnected (d.φ '' A) := hpre.image d.φ hcont
    have hBsub : d.φ '' A ⊆ MandelDim.ParabolicBasin f₀ D₀ := by
      rintro _ ⟨v, hv, rfl⟩
      exact hφbasin v hv
    -- the ends meet `B`: some iterate of `φ u` enters the petal
    have hmemA : ∀ m : ℕ, u + m ∈ A := by
      intro m
      rw [hAdef]
      have him : ((u + m : ℂ)).im = u.im := by simp
      have : max d.η₀ 1 < s * ((u + m : ℂ)).im := by
        rw [him]; rw [hAdef] at huA; exact huA
      exact this
    have hInt : (B ∩ d.φ '' A).Nonempty := by
      have hne : ∀ n : ℕ, (f₀^[n]) (d.φ u) ≠ 0 := by
        intro n hn0
        have hray := ray_mem_abs f₀ D₀ d u (hAends u huA) n
        have hmem : (0 : ℂ) ∈ d.φ '' A :=
          ⟨u + n, hmemA n, by rw [hray.2, hn0]⟩
        exact hzero (hBsub hmem)
      obtain ⟨n, hn⟩ := d.basin_enter (d.φ u) (hφbasin u huA) hne
      exact ⟨(f₀^[n]) (d.φ u), hOB hn,
        ⟨u + n, hmemA n, (ray_mem_abs f₀ D₀ d u (hAends u huA) n).2⟩⟩
    exact hB.2.2.2.1 (d.φ '' A) hpreB hBsub hInt ⟨u, huA, rfl⟩
  refine ⟨max d.η₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right d.η₀ 1), fun w hw => ?_⟩
  rcases le_or_gt (0 : ℝ) w.im with hpos | hneg
  · refine key 1 (Or.inl rfl) {u : ℂ | max d.η₀ 1 < (1 : ℝ) * u.im} rfl w ?_
    change max d.η₀ 1 < (1 : ℝ) * w.im
    rw [one_mul]
    rwa [abs_of_nonneg hpos] at hw
  · refine key (-1) (Or.inr rfl) {u : ℂ | max d.η₀ 1 < (-1 : ℝ) * u.im} rfl w ?_
    change max d.η₀ 1 < (-1 : ℝ) * w.im
    rw [neg_one_mul]
    rw [abs_of_neg hneg] at hw
    linarith
