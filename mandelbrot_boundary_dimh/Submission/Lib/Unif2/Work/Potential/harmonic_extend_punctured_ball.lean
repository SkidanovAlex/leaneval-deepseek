import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.Dirichlet.dirichlet_ball
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le
import Submission.Lib.Unif2.Commons.Analysis.Complex.Harmonic.annulus_le_boundary
import Submission.Lib.Unif2.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
import Submission.Lib.Unif2.Work.Potential.annulus_barrier_le

/-!
# Removable singularities for bounded harmonic functions on a punctured ball

We prove that a function `w : ℂ → ℝ` which is harmonic on the punctured ball
`{z | 0 < ‖z - a‖ < ρ}` and bounded there extends to a function harmonic on the
whole ball `{z | ‖z - a‖ < ρ}`.

The heart of the argument is the classical removable–singularity theorem on the
punctured Euclidean ball at the origin: the Dirichlet solution `v` for the ball
of radius `ρ/2` with boundary data `u` is harmonic on that ball, and the
difference `u - v` is controlled on the annuli `{δ < ‖z‖ < ρ/2}` by the
logarithmic barrier `log(ρ/2 / δ)`; letting `δ → 0` gives `u = v` off the
origin.  The general case follows by translation.
-/

noncomputable section
open Set Metric Filter
open scoped Real Topology

namespace Work.Potential

/-! ## An elementary limit lemma

If a nonnegative-ish quantity `c` is bounded by `K * (log (r/δ))⁻¹ * L` for every
`0 < δ < x < r`, then `c ≤ 0` (take `δ = r/(n+2)` and let `n → ∞`). -/
private lemma le_zero_of_mul_inv_log {c K L r x : ℝ} (hr : 0 < r) (hx0 : 0 < x) (_hxr : x < r)
    (h : ∀ δ : ℝ, 0 < δ → δ < x → c ≤ K * (Real.log (r / δ))⁻¹ * L) : c ≤ 0 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (max (r / x) (Real.exp (K * L / ε)))
  have hn1 : (r / x) < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn2 : Real.exp (K * L / ε) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  set δ : ℝ := r / ((n:ℝ) + 2) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδx : δ < x := by
    rw [hδdef, div_lt_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+2)]
    have hthis : r / x < (n:ℝ) + 2 := by linarith
    have hm := mul_lt_mul_of_pos_left hthis hx0
    have hmr : x * (r / x) = r := by field_simp
    rwa [hmr] at hm
  have hrd : r / δ = (n:ℝ) + 2 := by rw [hδdef]; field_simp
  have hloggt : K * L / ε < Real.log ((n:ℝ) + 2) := by
    have h1 : Real.log (Real.exp (K * L / ε)) < Real.log ((n:ℝ) + 2) :=
      Real.log_lt_log (Real.exp_pos _) (by linarith)
    rwa [Real.log_exp] at h1
  have hKlt : K * L < ε * Real.log ((n:ℝ) + 2) := by
    have h2 : K * L < Real.log ((n:ℝ) + 2) * ε := (div_lt_iff₀ hε).mp hloggt
    simpa [mul_comm] using h2
  have hlogpos : 0 < Real.log ((n:ℝ) + 2) := by
    apply Real.log_pos; linarith
  have hmain : K * (Real.log (r / δ))⁻¹ * L < ε := by
    rw [hrd]
    rw [show K * (Real.log ((n:ℝ) + 2))⁻¹ * L = (K * L) * (Real.log ((n:ℝ) + 2))⁻¹ by ring]
    exact (mul_inv_lt_iff₀ hlogpos).mpr hKlt
  have hc := h δ hδpos hδx
  linarith

/-- **Removable singularity for a bounded harmonic function on a punctured
ball centred at the origin.**  A function harmonic on `{z | 0 < ‖z‖ < R}` and
bounded by `M` there agrees off the origin on `{z | ‖z‖ < R/2}` with a function
`U` harmonic on that ball. -/
theorem removable_singularity_ball_zero {u : ℂ → ℝ} {R M : ℝ} (hR : 0 < R)
    (hu : ∀ z : ℂ, ‖z‖ < R → z ≠ 0 → InnerProductSpace.HarmonicAt u z)
    (hb : ∀ z : ℂ, ‖z‖ < R → z ≠ 0 → |u z| ≤ M) :
    ∃ U : ℂ → ℝ, (∀ z : ℂ, ‖z‖ < R / 2 → InnerProductSpace.HarmonicAt U z) ∧
      (∀ z : ℂ, ‖z‖ < R / 2 → z ≠ 0 → U z = u z) := by
  have hr : 0 < R / 2 := by linarith
  have hMnn : 0 ≤ M := by
    have h1 : ‖(((R/2:ℝ)) : ℂ)‖ < R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]; linarith
    have h2 : ((R/2:ℝ) : ℂ) ≠ 0 := by
      simp only [Complex.ofReal_ne_zero]; exact ne_of_gt hr
    exact le_trans (abs_nonneg _) (hb _ h1 h2)
  have hFcont : ContinuousOn u (Metric.sphere 0 (R / 2)) := by
    intro z hz
    have hzn : ‖z‖ = R / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hz1 : ‖z‖ < R := by rw [hzn]; linarith
    have hz2 : z ≠ 0 := by rintro rfl; rw [norm_zero] at hzn; linarith
    exact (hu z hz1 hz2).1.continuousAt.continuousWithinAt
  obtain ⟨v, hvharm, hvcont⟩ :=
    Commons.Analysis.Complex.Dirichlet.dirichlet_ball (c := 0) (R := R / 2) hr (F := u) hFcont
  have hvharm' : ∀ z : ℂ, ‖z‖ < R / 2 → InnerProductSpace.HarmonicAt v z :=
    fun z hz => hvharm z (by simpa using hz)
  have hvcont' : ContinuousOn (fun z : ℂ => if ‖z‖ < R / 2 then v z else u z)
      (Metric.closedBall 0 (R/2)) := by
    simpa using hvcont
  -- The Dirichlet solution is bounded by `M` on the ball of radius `R/2`.
  have hvbnd : ∀ z : ℂ, ‖z‖ < R / 2 → |v z| ≤ M := by
    intro z hz
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hcont' : ContinuousOn (fun z : ℂ => if ‖z‖ < R / 2 then -v z else -u z)
          (Metric.closedBall 0 (R/2)) := by
        have heq : (fun z : ℂ => if ‖z‖ < R / 2 then -v z else -u z)
            = (fun z : ℂ => -(if ‖z‖ < R / 2 then v z else u z)) := by
          funext w; by_cases h : ‖w‖ < R / 2 <;> simp [h]
        rw [heq]; exact hvcont'.neg
      have hres := Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le (c := 0) (R := R/2) (M := M)
        (F := fun z : ℂ => -u z) hr ?_
        (fun w hw => by simpa using (hvharm' w (by simpa using hw)).neg) (by simpa using hcont')
      · have hh : -v z ≤ M := hres z (by simpa using hz); linarith
      · intro w hw
        have hwn : ‖w‖ = R / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
        have hw1 : ‖w‖ < R := by rw [hwn]; linarith
        have hw2 : w ≠ 0 := by rintro rfl; rw [norm_zero] at hwn; linarith
        have hh : -M ≤ u w := (abs_le.mp (hb w hw1 hw2)).1
        linarith
    · have hres := Commons.Analysis.Complex.Harmonic.harmonic_le_of_boundary_le (c := 0) (R := R/2) (M := M)
        (F := u) hr ?_ (fun z hz => hvharm' z (by simpa using hz)) (by simpa using hvcont')
      · have hh : v z ≤ M := hres z (by simpa using hz); linarith
      · intro w hw
        have hwn : ‖w‖ = R / 2 := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
        have hw1 : ‖w‖ < R := by rw [hwn]; linarith
        have hw2 : w ≠ 0 := by rintro rfl; rw [norm_zero] at hwn; linarith
        exact (abs_le.mp (hb w hw1 hw2)).2
  set hh : ℂ → ℝ := fun z => if ‖z‖ < R / 2 then v z else u z with hhdef
  have hhcont : ContinuousOn hh (Metric.closedBall 0 (R/2)) := by
    rw [hhdef]; exact hvcont'
  set W : ℂ → ℝ := fun z => u z - hh z with hWdef
  -- The key step: `u = v` on the punctured ball of radius `R/2`.
  have hkey : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < R / 2 → u z = v z := by
    intro z₀ hz0pos hz0lt
    have hWz0 : W z₀ = u z₀ - v z₀ := by simp [hWdef, hhdef, if_pos hz0lt]
    have hbnd : ∀ δ : ℝ, 0 < δ → δ < ‖z₀‖ →
        |W z₀| ≤ (2*M) * (Real.log ((R/2) / δ))⁻¹ * Real.log ((R/2) / ‖z₀‖) := by
      intro δ hδ hδx
      have hδr : δ < R/2 := lt_trans hδx hz0lt
      have hWharm : ∀ z : ℂ, δ < ‖z‖ → ‖z‖ < R/2 → InnerProductSpace.HarmonicAt W z := by
        intro z hz1 hz2
        have hzR : ‖z‖ < R := by linarith
        have hzne : z ≠ 0 := by rintro rfl; rw [norm_zero] at hz1; linarith
        have huu : InnerProductSpace.HarmonicAt u z := hu z hzR hzne
        have hvv : InnerProductSpace.HarmonicAt v z := hvharm' z hz2
        refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr (huu.sub hvv)
        have hS : {y : ℂ | ‖y‖ < R/2} ∈ 𝓝 z :=
          (isOpen_lt continuous_norm continuous_const).mem_nhds hz2
        filter_upwards [hS] with y hy
        have hy' : ‖y‖ < R/2 := hy
        simp [hWdef, hhdef, if_pos hy']
      have hWcont : ContinuousOn W {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ R/2} := by
        have hhcont' : ContinuousOn hh {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ R/2} :=
          hhcont.mono (fun z hz => by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2)
        have hucont : ContinuousOn u {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ R/2} := by
          intro z hz
          have hz1 : δ ≤ ‖z‖ := hz.1
          have hz2 : ‖z‖ ≤ R/2 := hz.2
          have hzne : z ≠ 0 := by rintro rfl; rw [norm_zero] at hz1; linarith
          have hzR : ‖z‖ < R := by linarith
          exact (hu z hzR hzne).1.continuousAt.continuousWithinAt
        rw [hWdef]
        exact hucont.sub hhcont'
      have hinner : ∀ z : ℂ, ‖z‖ = δ → W z ≤ 2*M := by
        intro z hz
        have hzlt : ‖z‖ < R/2 := by rw [hz]; exact hδr
        have hzR : ‖z‖ < R := by linarith
        have hzne : z ≠ 0 := by rintro rfl; rw [norm_zero] at hz; linarith
        have h1 : u z ≤ M := (abs_le.mp (hb z hzR hzne)).2
        have h2 : -M ≤ v z := (abs_le.mp (hvbnd z hzlt)).1
        have hWz : W z = u z - v z := by simp [hWdef, hhdef, if_pos hzlt]
        rw [hWz]; linarith
      have houter : ∀ z : ℂ, ‖z‖ = R/2 → W z ≤ 0 := by
        intro z hz
        have hnot : ¬ ‖z‖ < R/2 := by rw [hz]; exact lt_irrefl _
        have hWz : W z = u z - u z := by simp [hWdef, hhdef, hnot]
        rw [hWz]; simp
      have hinner' : ∀ z : ℂ, ‖z‖ = δ → (-W) z ≤ 2*M := by
        intro z hz
        have hzlt : ‖z‖ < R/2 := by rw [hz]; exact hδr
        have hzR : ‖z‖ < R := by linarith
        have hzne : z ≠ 0 := by rintro rfl; rw [norm_zero] at hz; linarith
        have h1 : -M ≤ u z := (abs_le.mp (hb z hzR hzne)).1
        have h2 : v z ≤ M := (abs_le.mp (hvbnd z hzlt)).2
        have hWz : W z = u z - v z := by simp [hWdef, hhdef, if_pos hzlt]
        show -(W z) ≤ 2*M
        rw [hWz]; linarith
      have houter' : ∀ z : ℂ, ‖z‖ = R/2 → (-W) z ≤ 0 := by
        intro z hz
        have hnot : ¬ ‖z‖ < R/2 := by rw [hz]; exact lt_irrefl _
        have hWz : W z = u z - u z := by simp [hWdef, hhdef, hnot]
        show -(W z) ≤ 0
        rw [hWz]; simp
      have hA := annulus_barrier_le (W := W) (δ := δ) (ρ := R/2) (B := 2*M) hδ hδr (by linarith)
        hWharm hWcont hinner houter
      have hA' := annulus_barrier_le (W := fun z => -W z) (δ := δ) (ρ := R/2) (B := 2*M) hδ hδr (by linarith)
        (fun z a b => (hWharm z a b).neg) hWcont.neg hinner' houter'
      have h1 := hA z₀ (le_of_lt hδx) (le_of_lt hz0lt)
      have h2 := hA' z₀ (le_of_lt hδx) (le_of_lt hz0lt)
      exact abs_le.mpr ⟨by linarith, h1⟩
    have hzero : |W z₀| ≤ 0 :=
      le_zero_of_mul_inv_log (c := |W z₀|) (K := 2*M) (L := Real.log ((R/2) / ‖z₀‖))
        (r := R/2) (x := ‖z₀‖) hr hz0pos hz0lt hbnd
    have hW0 : W z₀ = 0 := abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
    rw [hWz0] at hW0; linarith
  refine ⟨v, ?_, ?_⟩
  · intro z hz; exact hvharm' z hz
  · intro z hz hzne
    have hzpos : 0 < ‖z‖ := by rw [norm_pos_iff]; exact hzne
    exact (hkey z hzpos hz).symm

/-- **Removable singularity for bounded harmonic functions on a punctured ball.**
A function harmonic on the punctured ball `{z | 0 < ‖z - a‖ < ρ}` and bounded by
`M` there extends to a function `h` harmonic on the whole ball `{z | ‖z - a‖ < ρ}`
which agrees with `w` off the puncture. -/
theorem harmonic_extend_punctured_ball
    {a : ℂ} {ρ M : ℝ} (hρ : 0 < ρ) {w : ℂ → ℝ}
    (hw : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → InnerProductSpace.HarmonicAt w z)
    (hb : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → |w z| ≤ M) :
    ∃ h : ℂ → ℝ,
      (∀ z : ℂ, ‖z - a‖ < ρ → InnerProductSpace.HarmonicAt h z) ∧
      (∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → h z = w z) := by
  -- Translate the puncture to the origin.
  obtain ⟨U, hUharm, hUeq⟩ :=
    removable_singularity_ball_zero (u := fun y => w (a + y)) (R := ρ) (M := M) hρ
      (fun y hy hyne => by
        have hane : a + y ≠ a := fun hh => hyne (by linear_combination hh)
        have hyt : ‖(a + y) - a‖ < ρ := by simpa using hy
        exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic (u := w)
          (f := fun z : ℂ => a + z) (x := y)
          ((analyticAt_const (v := a)).add analyticAt_id) (hw (a + y) hyt hane))
      (fun y hy hyne => by
        have hane : a + y ≠ a := fun hh => hyne (by linear_combination hh)
        have hyt : ‖(a + y) - a‖ < ρ := by simpa using hy
        exact hb (a + y) hyt hane)
  refine ⟨fun y => if y = a then U 0 else w y, ?_, ?_⟩
  · intro z hz
    by_cases hza : z = a
    · rw [hza]
      have hcomp : InnerProductSpace.HarmonicAt (fun y : ℂ => U (y - a)) a :=
        Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic (u := U)
          (f := fun y : ℂ => y - a) (x := a)
          (analyticAt_id.sub (analyticAt_const (v := a)))
          (by simpa using hUharm 0 (by rw [norm_zero]; linarith))
      refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr hcomp
      have hball : Metric.ball a (ρ/2) ∈ 𝓝 a := Metric.ball_mem_nhds a (by linarith)
      filter_upwards [hball] with y hy
      have hyn : ‖y - a‖ < ρ/2 := by simpa [Metric.mem_ball, dist_eq_norm] using hy
      by_cases hya : y = a
      · rw [if_pos hya, hya]; simp
      · have hne' : y - a ≠ 0 := sub_ne_zero.mpr hya
        rw [if_neg hya, hUeq (y - a) hyn hne']
        congr 1
        ring
    · refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mpr (hw z hz hza)
      filter_upwards [isOpen_compl_singleton.mem_nhds hza] with y hy
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
      simp [if_neg hy]
  · intro z hz hza
    simp [if_neg hza]

end Work.Potential
