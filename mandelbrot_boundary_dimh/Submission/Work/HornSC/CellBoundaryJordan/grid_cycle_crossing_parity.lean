import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs
import Submission.Work.PlanarSC.not_hasArg_of_jordan_curve
import Submission.Lib.Unif2.Commons.Topology.Winding.winding_zero_of_unbounded_component
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_basic
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_range
import Submission.Work.HornSC.CellBoundaryJordan.grid_tour_injective
import Submission.Work.HornSC.CellBoundaryJordan.grid_circle_map
import Submission.Work.HornSC.CellBoundaryJordan.arg_lift_periodic
import Submission.Work.HornSC.CellBoundaryJordan.hasArg_iff_arg_lift
import Submission.Work.HornSC.CellBoundaryJordan.grid_crossing_defs
import Submission.Work.HornSC.CellBoundaryJordan.crossing_parity_of_lift
import Submission.Work.HornSC.CellBoundaryJordan.tour_crossing_strict
import Submission.Work.HornSC.CellBoundaryJordan.lvl_ncard_eq_rayMeet
import Submission.Work.HornSC.CellBoundaryJordan.winding_unimodular_of_bounded_component

/-!
# The crossing parity of a grid cycle

Let `Γ` be the closed polygonal curve traced by a simple closed grid cycle, let `a ∉ Γ` and let `R`
be the ray from `a` in the direction `1 + iε` (`ε > 0`), which by hypothesis meets `Γ` only
transversally (never at a lattice point) and only finitely often.  Then the number of crossings of
`R` with `Γ` is odd exactly when `a` lies in the bounded component of `Γᶜ`.

`a` lies in the bounded component iff the argument lift of `γ - a` is *not* periodic
(`plane_separation`, `not_hasArg_of_jordan_curve`, `winding_zero_of_unbounded_component`) and, in
that case, its drift is `±1`; the drift has the parity of the number of crossings of the ray with
`Γ` (`crossing_parity_of_lift`).
-/

namespace Work.HornSC.CellBoundaryJordan

open Set Filter

open scoped Topology

/-- **The crossing parity of a simple closed grid cycle.** -/
theorem grid_cycle_crossing_parity {k : ℕ} (hk : 3 ≤ k) (u : ℕ → ℤ × ℤ)
    (hper : ∀ i, u (i + k) = u i)
    (hinj : ∀ i j, i < k → j < k → u i = u j → i = j)
    (hstep : ∀ i, i < k → IsUnitAdj (u i) (u (i + 1)))
    {a : ℂ} {ε : ℝ} (hε : 0 < ε)
    (ha : a ∉ ⋃ i ∈ {i : ℕ | i < k}, adjSeg (u i) (u (i + 1)))
    (hgen : ∀ t : ℝ, 0 < t → ∀ m n : ℤ,
      a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ≠ (m : ℂ) + (n : ℂ) * Complex.I)
    (hfin : {t : ℝ | 0 < t ∧ a + (t : ℂ) * (⟨1, ε⟩ : ℂ) ∈
      ⋃ i ∈ {i : ℕ | i < k}, adjSeg (u i) (u (i + 1))}.Finite) :
    (Odd hfin.toFinset.card ↔
      Bornology.IsBounded (connectedComponentIn
        ((⋃ i ∈ {i : ℕ | i < k}, adjSeg (u i) (u (i + 1)))ᶜ) a)) := by
  change Odd hfin.toFinset.card ↔ Bornology.IsBounded (connectedComponentIn ((cycleSet k u)ᶜ) a)
  have ha' : a ∉ cycleSet k u := ha
  have hfin' : (rayMeet k u a ε).Finite := hfin
  -- ## The circle map and the Jordan region
  obtain ⟨γ, hγinj, hγval, hγrange⟩ := exists_circle_map_of_cycle hk u hper hinj hstep
  have hrange : Set.range γ = cycleSet k u := hγrange
  have hrange_f : Set.range (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t))) = Set.range γ := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨Circle.exp (2 * Real.pi * t), rfl⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨t₀, ht₀⟩ := Circle.exp_surjective c
      refine ⟨t₀ / (2 * Real.pi), ?_⟩
      change γ (Circle.exp (2 * Real.pi * (t₀ / (2 * Real.pi)))) = γ c
      rw [show 2 * Real.pi * (t₀ / (2 * Real.pi)) = t₀ from
            (by rw [← mul_div_assoc, mul_div_cancel_left₀ _
              (ne_of_gt (by positivity : (0:ℝ) < 2 * Real.pi))]), ht₀]
  -- ## The curve and its argument lift
  set d : ℂ := (⟨1, ε⟩ : ℂ) with hd
  have hdne : d ≠ 0 := by
    rw [hd]
    intro h
    have := congrArg Complex.re h
    simp at this
  set F : ℝ → ℂ := fun t => γ (Circle.exp (2 * Real.pi * t)) - a with hF
  have hFtour : ∀ s : ℝ, F s = tour u k s - a := by
    intro s
    simp only [hF]
    rw [hγval s]
  have hFcont : Continuous F := by
    simp only [hF]
    exact (γ.continuous.comp (Circle.exp.continuous.comp (by fun_prop))).sub continuous_const
  have hFper : Function.Periodic F 1 := by
    intro t
    rw [hFtour (t + 1), hFtour t, tour_add_one u k t]
  have hFnz : ∀ t, F t ≠ 0 := by
    intro t h
    rw [hFtour t] at h
    have h1 : tour u k t = a := sub_eq_zero.mp h
    exact ha' (h1 ▸ tour_mem_cycleSet (by omega) u t)
  obtain ⟨m, th, hthc, hthexp, hthper⟩ := arg_lift_periodic hFcont hFper hFnz
  -- the argument function of `(F ·)/d`
  set Θ : ℝ → ℝ := fun t => (th t).im - (Complex.log d).im with hΘ
  have hΘc : Continuous Θ := (Complex.continuous_im.comp hthc).sub continuous_const
  have hΘper : ∀ t, Θ (t + 1) = Θ t + (m : ℝ) * (2 * Real.pi) := by
    intro t
    have h' : (th (t + 1)).im - (th t).im = (m : ℝ) * (2 * Real.pi) := by
      have h2 : th (t + 1) - th t = (m : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hthper t]; ring
      have h3 := congrArg Complex.im h2
      simpa [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using h3
    simp only [hΘ]
    linarith
  -- the representation of `F t / d`
  have hΘrep : ∀ t, F t / d = ((‖F t / d‖ : ℝ) : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I) := by
    intro t
    have hlog : Complex.exp (Complex.log d) = d := Complex.exp_log hdne
    have h1 : F t / d = Complex.exp (th t - Complex.log d) := by
      rw [Complex.exp_sub, hthexp t, hlog]
    have h2 : (th t - Complex.log d).im = Θ t := by
      rw [hΘ]; simp [Complex.sub_im]
    have h3 : ‖F t / d‖ = Real.exp (th t - Complex.log d).re := by
      rw [h1, Complex.norm_exp]
    calc F t / d = Complex.exp (th t - Complex.log d) := h1
      _ = ((Real.exp (th t - Complex.log d).re : ℝ) : ℂ) *
            Complex.exp (((th t - Complex.log d).im : ℂ) * Complex.I) := by
            rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.re_add_im]
      _ = ((‖F t / d‖ : ℝ) : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I) := by rw [h3, h2]
  have hΘrep_tour : ∀ t : ℝ, (tour u k t - a) / d =
      ((‖(tour u k t - a) / d‖ : ℝ) : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I) := by
    intro t
    rw [← hFtour t]
    exact hΘrep t
  -- ## `HasArgPeriodic F` is the same as `HasArg F 0`
  have hHA : HasArgPeriodic F ↔ Commons.Topology.Winding.HasArg F 0 := by
    rw [hF]
    constructor
    · rintro ⟨θ, hc, hp, hrep⟩
      exact ⟨θ, hc, hp, fun t => by simpa using hrep t⟩
    · rintro ⟨θ, hc, hp, hrep⟩
      exact ⟨θ, hc, hp, fun t => by simpa using hrep t⟩
  -- ## The bounded component is exactly the non-periodic case
  have hcomp' : Bornology.IsBounded (connectedComponentIn ((cycleSet k u)ᶜ) a) ↔
      ¬ HasArgPeriodic F := by
    constructor
    · intro hbdd hh
      have hbddγ : Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a) := by
        rwa [hrange]
      have hnh := Work.PlanarSC.not_hasArg_of_jordan_curve hγinj (by rw [hrange]; exact ha') hbddγ
      exact hnh (hHA.mp hh)
    · intro hna
      by_contra hnb
      rw [← hrange] at hnb
      have hfc : Continuous (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t))) :=
        γ.continuous.comp (Circle.exp.continuous.comp (by fun_prop))
      have hper' : Function.Periodic (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t))) 1 := by
        intro t
        simp only []
        rw [hγval (t + 1), hγval t, tour_add_one u k t]
      have hp' : a ∉ Set.range (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t))) := by
        rintro ⟨t, ht⟩
        exact ha' (hrange ▸ ⟨Circle.exp (2 * Real.pi * t), ht⟩)
      have hunb' : ¬ Bornology.IsBounded (connectedComponentIn
          ((Set.range (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t))))ᶜ) a) := by
        rw [hrange_f]; exact hnb
      have h := Commons.Topology.Winding.winding_zero_of_unbounded_component hfc hper' hp' hunb'
      refine hna ?_
      refine hHA.mpr ?_
      show Commons.Topology.Winding.HasArg
        (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t)) - a) 0
      simpa only [Commons.Topology.Winding.HasArg, sub_zero] using h
  -- ## The lift is periodic exactly when the drift vanishes
  have hmzero : HasArgPeriodic F ↔ m = 0 := by
    have hiff := hasArg_iff_arg_lift hFcont hFper hFnz hthc hthexp
    constructor
    · intro hh
      have hp := hiff.mp hh
      have h1 : th (0 + 1) = th 0 := hp 0
      have h2 : ((m : ℂ) * (2 * Real.pi * Complex.I)) = 0 := by
        have h3 : th 0 + (m : ℂ) * (2 * Real.pi * Complex.I) = th 0 + 0 := by
          rw [← hthper 0, h1, add_zero]
        exact add_left_cancel h3
      have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
      have hm0 : (m : ℂ) = 0 := (mul_eq_zero.mp h2).resolve_right hne
      exact_mod_cast hm0
    · intro hm
      refine hiff.mpr ?_
      intro t
      rw [hthper t, hm]
      simp
  -- ## The parity of the crossing count
  have hstr : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) 1 →
      (∃ n : ℤ, Θ t = (n : ℝ) * (2 * Real.pi)) →
      ∃ δ : ℝ, 0 < δ ∧
        ((∀ s : ℝ, |s - t| < δ → s ≠ t → (Θ s - Θ t) * (s - t) > 0) ∨
         (∀ s : ℝ, |s - t| < δ → s ≠ t → (Θ s - Θ t) * (s - t) < 0)) := by
    intro t ht htlvl
    have hrep' : ∀ s : ℝ, 0 ≤ s → s < 1 →
        (tourOn u k s - a) / d = ((‖(tourOn u k s - a) / d‖ : ℝ) : ℂ) *
          Complex.exp ((Θ s : ℂ) * Complex.I) := by
      intro s hs0 hs1
      rw [show tourOn u k s = tour u k s from (tour_eq_tourOn u hs0 hs1).symm]
      exact hΘrep_tour s
    exact tour_crossing_strict hk u hper hinj hstep hε ha' hgen hΘc hrep' ht.1 ht.2 htlvl
  have hcount := lvl_ncard_eq_rayMeet hk u hper hinj hstep hε ha' hΘrep_tour hfin'
  have h0 : ¬ ∃ n : ℤ, Θ 0 = (n : ℝ) * (2 * Real.pi) := by
    rintro ⟨n, hn⟩
    have hreal : F 0 / d = (‖F 0 / d‖ : ℂ) := by
      have hz : (Θ 0 : ℂ) * Complex.I = (n : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hn]; push_cast; ring
      calc F 0 / d = (‖F 0 / d‖ : ℂ) * Complex.exp ((Θ 0 : ℂ) * Complex.I) := hΘrep 0
        _ = (‖F 0 / d‖ : ℂ) * Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) := by rw [hz]
        _ = (‖F 0 / d‖ : ℂ) * 1 := by rw [Complex.exp_int_mul_two_pi_mul_I]
        _ = (‖F 0 / d‖ : ℂ) := by ring
    have hpos : 0 < ‖F 0 / d‖ := norm_pos_iff.mpr (div_ne_zero (hFnz 0) hdne)
    have hpt : tour u k 0 = a + (‖F 0 / d‖ : ℂ) * d := by
      have h1 : F 0 = (‖F 0 / d‖ : ℂ) * d := by
        rw [← hreal]
        exact (div_mul_cancel₀ (F 0) hdne).symm
      have hsub : tour u k 0 - a = (‖F 0 / d‖ : ℂ) * d := (hFtour 0).symm.trans h1
      rw [← hsub]
      ring
    have hlat : tour u k 0 = (((u 0).1 : ℤ) : ℂ) + (((u 0).2 : ℤ) : ℂ) * Complex.I := by
      rw [show tour u k 0 = tourOn u k 0 from tour_eq_tourOn u le_rfl (by norm_num),
        tourOn_zero]
      apply Complex.ext <;> simp [lpt]
    exact hgen (‖F 0 / d‖) hpos ((u 0).1) ((u 0).2) (hpt.symm.trans hlat)
  have hpar := crossing_parity_of_lift hΘc hΘper h0 hstr hcount.1
  -- ## Assembly
  have hcard : hfin.toFinset.card = (lvlSetIco Θ).ncard := hcount.2.symm
  constructor
  · intro hodd
    have hm : Odd m := hpar.mp (hcard ▸ hodd)
    have hm0 : m ≠ 0 := by
      rintro rfl
      obtain ⟨c, hc⟩ := hm
      omega
    exact hcomp'.mpr (fun h => hm0 (hmzero.mp h))
  · intro hbdd
    have hbddγ : Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a) := by
      rwa [hrange]
    have hoddm : Odd m := by
      rcases winding_unimodular_of_bounded_component hγinj (by rwa [hrange]) hbddγ hthc
        (fun t => hthexp t) hthper with h' | h'
      · rw [h']; exact ⟨0, by norm_num⟩
      · rw [h']; exact ⟨-1, by norm_num⟩
    rw [hcard]
    exact hpar.mpr hoddm

end Work.HornSC.CellBoundaryJordan
