import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Main
import Submission.Work.FatouCoord.Repelling
import Submission.Work.Parab.germ
import Submission.Work.Parab.Setup
import Submission.Work.Parab.basinEnters.petal_capture
import Submission.Work.Parab.basinEnters.zero_not_mem_basin

/-!
# A Fatou coordinate on the whole parabolic basin

For a parabolic germ `f z = z + z ^ 2 h z` (`h 0 = 1`) the Leau–Fatou coordinate `φ` is
constructed on an attracting petal `Petal r M` (`Work.FatouCoord`).  This file propagates it to
the *whole* parabolic basin `MandelDim.ParabolicBasin f D`, which is what the §4.1 data of
Shishikura's paper (`MandelDim.ParabData`) needs:

* if the orbit of a basin point enters the petal, `Φ z = φ (f ^ [n] z) - n` for the first such
  `n`; this is well defined because `φ` is a Fatou coordinate on the (forward invariant) petal;
* otherwise (the degenerate case: the orbit hits the fixed point `0`) the value is `φ 0 - n`.
  This can happen because `MandelDim.ParabolicBasin` is a *locally uniform* notion on a not
  necessarily connected domain `D`; see `Parab/basinEnters/counterexample.lean`.

`Φ` is holomorphic on the basin and satisfies the Abel equation `Φ (f z) = Φ z + 1` there; it
agrees with `φ` on the petal, and the petal lies in the basin.

## Main result

* `Work.Parab.basinCoord.exists_basin_coordinate`
-/

open Complex Set Metric Filter
open scoped Topology

namespace Work.Parab.basinCoord

open Work.FatouCoord

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' M : ℝ} {z u : ℂ}

/-! ## Two coordinates of one orbit agree -/

/-- If two iterates of `z` both lie in a forward invariant domain on which `φ` is a Fatou
coordinate, the transported values `φ (f ^ [n] z) - n` agree. -/
theorem petal_coord_consistent {φ : ℂ → ℂ} {P : Set ℂ} (hφ : IsFatouCoordinateOn f φ P)
    (hP : MapsTo f P P) {n m : ℕ} (hn : f^[n] z ∈ P) (hnm : n ≤ m) (hm : f^[m] z ∈ P) :
    φ (f^[m] z) - (m : ℂ) = φ (f^[n] z) - (n : ℂ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have h1 : f^[n + d] z = f^[d] (f^[n] z) := by
    rw [Nat.add_comm n d, Function.iterate_add_apply]
  rw [h1, IsFatouCoordinateOn.iterate hφ hP hn d]
  push_cast
  ring

/-! ## The first index at which the orbit meets the petal or the fixed point -/

/-- The first index `n` with `f ^ [n] z ∈ Petal r M` or `f ^ [n] z = 0` (and `0` if there is
no such index). -/
noncomputable def firstHit (f : ℂ → ℂ) (r M : ℝ) (z : ℂ) : ℕ := by
  classical
  exact if h : ∃ n : ℕ, f^[n] z ∈ Petal r M ∨ f^[n] z = 0 then Nat.find h else 0

theorem firstHit_spec {f : ℂ → ℂ} {r M : ℝ} {z : ℂ}
    (h : ∃ n : ℕ, f^[n] z ∈ Petal r M ∨ f^[n] z = 0) :
    f^[firstHit f r M z] z ∈ Petal r M ∨ f^[firstHit f r M z] z = 0 := by
  classical
  rw [firstHit, dif_pos h]
  exact Nat.find_spec h

theorem firstHit_le {f : ℂ → ℂ} {r M : ℝ} {z : ℂ}
    (h : ∃ n : ℕ, f^[n] z ∈ Petal r M ∨ f^[n] z = 0) {n : ℕ}
    (hn : f^[n] z ∈ Petal r M ∨ f^[n] z = 0) : firstHit f r M z ≤ n := by
  classical
  by_contra hc
  push_neg at hc
  rw [firstHit, dif_pos h] at hc
  exact (Nat.find_min h hc) hn

/-- The basin coordinate built from the petal coordinate. -/
noncomputable def basinPhi (f : ℂ → ℂ) (a : ℂ) (r M : ℝ) (z : ℂ) : ℂ :=
  fatouCoord f (1 - a) (f^[firstHit f r M z] z) - (firstHit f r M z : ℂ)

/-! ## Petal facts at any sufficiently large level -/

/-- **Petal facts at any sufficiently large level.**  For every level `M` above a threshold the
petal is forward invariant, orbits in it converge to `0` (uniformly!), the explicit function
`fatouCoord f (1 - a)` is a Fatou coordinate there and is injective there. -/
theorem exists_petal_level_facts {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      MapsTo f (Petal r M) (Petal r M) ∧
      (∀ z ∈ Petal r M, Tendsto (fun n : ℕ => f^[n] z) atTop (nhds (0 : ℂ))) ∧
      IsFatouCoordinateOn f (fatouCoord f (1 - a)) (Petal r M) ∧
      Set.InjOn (fatouCoord f (1 - a)) (Petal r M) ∧
      TendstoUniformlyOn (fun n : ℕ => f^[n]) (fun _ => (0 : ℂ)) atTop (Petal r M) := by
  obtain ⟨M₁, hM₁⟩ := Petal.petal_mapsTo_tendsto_of_le hb
  obtain ⟨N₃, hN₃pos, -, hdiffW⟩ := Exist.fatouCoordW_differentiable hb
  obtain ⟨N₄, hN₄pos, -, habelW⟩ := Exist.fatouCoordW_abel hb
  obtain ⟨N₅, hN₅pos, -, hinjW⟩ := Exist.fatouCoordW_injOn hb
  obtain ⟨Ng, hNgpos, -, hgrowth⟩ := Estimate.iterate_re_growth hb
  let s : Finset ℝ := {M₁, 1, N₃, N₄, N₅, Ng}
  have hs : s.Nonempty := ⟨1, by simp [s]⟩
  refine ⟨s.max' hs, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ s.max' hs := Finset.le_max' s 1 (by simp [s])
    linarith
  · intro M hM
    have hM₁' : M₁ ≤ M := le_trans (Finset.le_max' s M₁ (by simp [s])) hM
    have h1' : (1 : ℝ) ≤ M := le_trans (Finset.le_max' s 1 (by simp [s])) hM
    have hN₃' : N₃ ≤ M := le_trans (Finset.le_max' s N₃ (by simp [s])) hM
    have hN₄' : N₄ ≤ M := le_trans (Finset.le_max' s N₄ (by simp [s])) hM
    have hN₅' : N₅ ≤ M := le_trans (Finset.le_max' s N₅ (by simp [s])) hM
    have hNg' : Ng ≤ M := le_trans (Finset.le_max' s Ng (by simp [s])) hM
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one h1'
    have hmaps : MapsTo f (Petal r M) (Petal r M) := (hM₁ M hM₁').1
    refine ⟨hmaps, (hM₁ M hM₁').2, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact hdiffW.comp differentiableOn_chart_petal
          (fun z hz => lt_of_le_of_lt hN₃' (chart_mem_of_mem_petal hz))
      · intro z hz
        have hcw : N₄ < (chart z).re := lt_of_le_of_lt hN₄' (chart_mem_of_mem_petal hz)
        have h1 : chart (f z) = wMap f (chart z) := chart_comp f (ne_zero_of_mem_Petal hz)
        simp only [fatouCoord_eq]
        rw [h1, habelW (chart z) hcw]
    · intro z hz z' hz' heq
      have hcz : N₅ < (chart z).re := lt_of_le_of_lt hN₅' (chart_mem_of_mem_petal hz)
      have hcz' : N₅ < (chart z').re := lt_of_le_of_lt hN₅' (chart_mem_of_mem_petal hz')
      have hch : chart z = chart z' := hinjW hcz hcz' heq
      calc z = chart (chart z) := (chart_chart (ne_zero_of_mem_Petal hz)).symm
        _ = chart (chart z') := by rw [hch]
        _ = z' := chart_chart (ne_zero_of_mem_Petal hz')
    · rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨n₀, hn₀pos, hn₀⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ 1 / (Ng + (n₀ : ℝ) / 2) < ε := by
        obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 / ε < (m : ℝ) := exists_nat_gt (2 / ε)
        refine ⟨m + 1, Nat.succ_pos m, ?_⟩
        have hcast0 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have hm1 : (m : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
        have hm2 : 1 / ε < (m : ℝ) / 2 := by
          have h2 : 2 / ε = 2 * (1 / ε) := by ring
          linarith
        have hx : 1 / ε < Ng + ((m + 1 : ℕ) : ℝ) / 2 := by linarith
        have hpos : (0 : ℝ) < Ng + ((m + 1 : ℕ) : ℝ) / 2 := by linarith
        rw [div_lt_iff₀ hpos]
        calc (1 : ℝ) = ε * (1 / ε) := by field_simp
          _ < ε * (Ng + ((m + 1 : ℕ) : ℝ) / 2) := mul_lt_mul_of_pos_left hx hε
      refine eventually_atTop.mpr ⟨n₀, fun n hn z hz => ?_⟩
      have hchart : Ng < (chart z).re := lt_of_le_of_lt hNg' (chart_mem_of_mem_petal hz)
      have hiter : ∀ k : ℕ, chart (f^[k] z) = (wMap f)^[k] (chart z) := by
        intro k
        induction k with
        | zero => simp
        | succ j ih =>
            have hzj : f^[j] z ≠ 0 :=
              ne_zero_of_mem_Petal (mapsTo_iterate_of_mapsTo hmaps j hz)
            rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
            rw [chart_comp f hzj, ih]
      have hne : f^[n] z ≠ 0 := ne_zero_of_mem_Petal (mapsTo_iterate_of_mapsTo hmaps n hz)
      have hnorm : ‖f^[n] z‖ = 1 / ‖(wMap f)^[n] (chart z)‖ := by
        have h1 := norm_chart hne
        rw [hiter n] at h1
        rw [h1, one_div, inv_inv]
      have hle : 1 / ‖(wMap f)^[n] (chart z)‖ ≤ 1 / (Ng + (n : ℝ) / 2) := by
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hpos : (0 : ℝ) < Ng + (n : ℝ) / 2 := by linarith
        exact one_div_le_one_div_of_le hpos
          (le_trans (hgrowth (chart z) hchart n) (Complex.re_le_norm _))
      have hlt : 1 / (Ng + (n : ℝ) / 2) ≤ 1 / (Ng + (n₀ : ℝ) / 2) := by
        have hn0 : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have h0n : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have h0n₀ : (0 : ℝ) ≤ (n₀ : ℝ) := Nat.cast_nonneg n₀
        have hpos : (0 : ℝ) < Ng + (n₀ : ℝ) / 2 := by linarith
        exact one_div_le_one_div_of_le hpos (by linarith)
      rw [dist_zero_left]
      calc ‖f^[n] z‖ = 1 / ‖(wMap f)^[n] (chart z)‖ := hnorm
        _ ≤ 1 / (Ng + (n : ℝ) / 2) := hle
        _ ≤ 1 / (Ng + (n₀ : ℝ) / 2) := hlt
        _ < ε := hn₀

/-! ## Points of the basin whose orbit hits `0` -/

/-- In the degenerate case — the orbit of a basin point hits the fixed point — the iterate
`f ^ [N]` is locally constantly `0` at that point.  Otherwise the open mapping theorem would put
`0` itself into the basin. -/
theorem locally_constant_of_hits_zero {f : ℂ → ℂ} {D : Set ℂ} {z : ℂ} {N : ℕ}
    (hD : IsOpen D) (hdiff : DifferentiableOn ℂ f D)
    (hz : z ∈ MandelDim.ParabolicBasin f D)
    (h0 : (0 : ℂ) ∉ MandelDim.ParabolicBasin f D)
    (hN : f^[N] z = 0) :
    ∃ V ∈ nhds z, ∀ u ∈ V, f^[N] u = 0 := by
  obtain ⟨U, hU, hUmap, hUunif⟩ := hz
  obtain ⟨ε, hεpos, hεU⟩ : ∃ ε > 0, ball z ε ⊆ U := Metric.mem_nhds_iff.mp hU
  have hdiffj : ∀ j : ℕ, DifferentiableOn ℂ (f^[j]) (ball z ε) := by
    intro j
    induction j with
    | zero => simpa using differentiableOn_id
    | succ k ih =>
        rw [Function.iterate_succ']
        exact hdiff.comp ih (fun w hw => hUmap k (hεU hw))
  have hanal : AnalyticAt ℂ (f^[N]) z :=
    (hdiffj N).analyticAt (isOpen_ball.mem_nhds (mem_ball_self hεpos))
  rcases hanal.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
  · refine ⟨{u : ℂ | f^[N] u = f^[N] z}, hconst, fun u hu => by rw [hu, hN]⟩
  · exfalso
    have hW : (f^[N]) '' ball z ε ∈ nhds (0 : ℂ) := by
      have h1 : (f^[N]) ⁻¹' ((f^[N]) '' ball z ε) ∈ nhds z :=
        mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hεpos))
          (fun u hu => ⟨u, hu, rfl⟩)
      have h2 : (f^[N]) '' ball z ε ∈ Filter.map (f^[N]) (nhds z) := Filter.mem_map.mpr h1
      have h3 := hopen h2
      rwa [hN] at h3
    refine h0 ⟨(f^[N]) '' ball z ε, hW, ?_, ?_⟩
    · intro k w hw
      obtain ⟨v, hv, rfl⟩ := hw
      have h1 : f^[k] (f^[N] v) = f^[k + N] v := (Function.iterate_add_apply f k N v).symm
      rw [h1]
      exact hUmap (k + N) (hεU hv)
    · rw [Metric.tendstoUniformlyOn_iff] at hUunif ⊢
      intro ε' hε'
      obtain ⟨K, hK⟩ := eventually_atTop.mp (hUunif ε' hε')
      refine eventually_atTop.mpr ⟨K, fun k hk w hw => ?_⟩
      obtain ⟨v, hv, rfl⟩ := hw
      have h1 : f^[k] (f^[N] v) = f^[k + N] v := (Function.iterate_add_apply f k N v).symm
      rw [h1]
      exact hK (k + N) (by omega) v (hεU hv)

/-! ## The main theorem -/

theorem exists_basin_coordinate {f : ℂ → ℂ} {D : Set ℂ} (hg : MandelDim.IsParabolicGerm f D) :
    ∃ (Φ : ℂ → ℂ) (h : ℂ → ℂ) (a : ℂ) (r A A' M : ℝ),
      Work.FatouCoord.ParabolicBounds f h a r A A' ∧ Metric.ball 0 r ⊆ D ∧ 0 < M ∧
      Work.FatouCoord.Petal r M ⊆ MandelDim.ParabolicBasin f D ∧
      Set.MapsTo f (Work.FatouCoord.Petal r M) (Work.FatouCoord.Petal r M) ∧
      (∀ z ∈ Work.FatouCoord.Petal r M,
        Filter.Tendsto (fun n : ℕ => f^[n] z) Filter.atTop (nhds (0 : ℂ))) ∧
      DifferentiableOn ℂ Φ (MandelDim.ParabolicBasin f D) ∧
      (∀ z ∈ MandelDim.ParabolicBasin f D, Φ (f z) = Φ z + 1) ∧
      Set.InjOn Φ (Work.FatouCoord.Petal r M) ∧
      (∀ z ∈ Work.FatouCoord.Petal r M, Φ z = Work.FatouCoord.fatouCoord f (1 - a) z) := by
  classical
  obtain ⟨h, a, r₀, A, A', hb₀, hball₀⟩ := Work.Parab.exists_parabolicBounds_of_germ hg
  -- shrink the radius so that the petal capture estimates are available
  let r : ℝ := min r₀ (min (1 / 16) (1 / (16 * (‖a‖ + A + 1))))
  have hA0 : 0 ≤ A := hb₀.hA
  have hrpos : 0 < r := by
    refine lt_min hb₀.hr (lt_min (by norm_num) ?_)
    positivity
  have hrle : r ≤ r₀ := min_le_left _ _
  have hr16 : r ≤ 1 / 16 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrbig : r ≤ 1 / (16 * (‖a‖ + A + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hb : Work.FatouCoord.ParabolicBounds f h a r A A' :=
    Work.Parab.basinEnters.parabolicBounds_mono hb₀ hrpos hrle
  have hball : ball (0 : ℂ) r ⊆ D := fun z hz => hball₀ (ball_subset_ball hrle hz)
  have hA1 : A ≤ ‖a‖ + A + 1 := by linarith [norm_nonneg a]
  have hsmall : A * r ^ 2 + ‖a‖ * r ≤ 1 / 8 := by
    have hAr : A * r ≤ 1 / 16 := by
      have h1 : A * r ≤ A * (1 / (16 * (‖a‖ + A + 1))) :=
        mul_le_mul_of_nonneg_left hrbig hA0
      have h2 : A * (1 / (16 * (‖a‖ + A + 1)))
          ≤ (‖a‖ + A + 1) * (1 / (16 * (‖a‖ + A + 1))) :=
        mul_le_mul_of_nonneg_right hA1 (by positivity)
      have h3 : (‖a‖ + A + 1) * (1 / (16 * (‖a‖ + A + 1))) = 1 / 16 := by
        field_simp
      linarith
    have hair : ‖a‖ * r ≤ 1 / 16 := by
      have h1 : ‖a‖ * r ≤ ‖a‖ * (1 / (16 * (‖a‖ + A + 1))) :=
        mul_le_mul_of_nonneg_left hrbig (norm_nonneg a)
      have h2 : ‖a‖ * (1 / (16 * (‖a‖ + A + 1)))
          ≤ (‖a‖ + A + 1) * (1 / (16 * (‖a‖ + A + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith [hA0]) (by positivity)
      have h3 : (‖a‖ + A + 1) * (1 / (16 * (‖a‖ + A + 1))) = 1 / 16 := by
        field_simp
      linarith
    have hsq : A * r ^ 2 ≤ 1 / 16 := by
      have hr2 : r ^ 2 ≤ r * (1 / 16) := by nlinarith [hrpos]
      calc A * r ^ 2 ≤ A * (r * (1 / 16)) := mul_le_mul_of_nonneg_left hr2 hA0
        _ = (A * r) * (1 / 16) := by ring
        _ ≤ (1 / 16) * (1 / 16) := mul_le_mul_of_nonneg_right hAr (by norm_num)
        _ ≤ 1 / 16 := by norm_num
    linarith
  -- the petal level
  obtain ⟨M₀, hM₀pos, hM₀⟩ := exists_petal_level_facts hb
  let M : ℝ := max M₀ 1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMge : M₀ ≤ M := le_max_left _ _
  obtain ⟨hmaps, hconvP, hfatou, hinjφ, hunifP⟩ := hM₀ M hMge
  -- basic facts about the basin
  have hzero : (0 : ℂ) ∉ MandelDim.ParabolicBasin f D :=
    Work.Parab.basinEnters.zero_not_mem_parabolicBasin hg
  have hf0 : f 0 = 0 := by
    rw [hb.f_eq 0 (by simpa using hb.hr)]
    ring
  have hiter0 : ∀ k : ℕ, f^[k] (0 : ℂ) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply', ih, hf0]
  have hgood : ∀ z ∈ MandelDim.ParabolicBasin f D,
      ∃ n : ℕ, f^[n] z ∈ Work.FatouCoord.Petal r M ∨ f^[n] z = 0 := by
    intro z hz
    by_cases hne : ∃ n : ℕ, f^[n] z = 0
    · obtain ⟨n, hn⟩ := hne
      exact ⟨n, Or.inr hn⟩
    · push_neg at hne
      obtain ⟨n, hn⟩ := Work.Parab.basinEnters.exists_iterate_mem_petal hb hr16 hsmall hMpos
        (Work.Parab.basinEnters.tendsto_iterate_of_mem_basin hz) hne
      exact ⟨n, Or.inl hn⟩
  have hmemD : ∀ z ∈ MandelDim.ParabolicBasin f D, ∀ k : ℕ, f^[k] z ∈ D := by
    intro z hz k
    obtain ⟨U, hU, hUmap, -⟩ := hz
    exact hUmap k (mem_of_mem_nhds hU)
  have hfD : ∀ w ∈ D, DifferentiableAt ℂ f w :=
    fun w hw => hg.2.2.1.differentiableAt (hg.1.mem_nhds hw)
  have hcontIter : ∀ z ∈ MandelDim.ParabolicBasin f D, ∀ k : ℕ, DifferentiableAt ℂ (f^[k]) z := by
    intro z hz k
    induction k with
    | zero => simpa using differentiableAt_id
    | succ j ih =>
        rw [Function.iterate_succ']
        exact (hfD _ (hmemD z hz j)).comp z ih
  -- the coordinate
  set Φ : ℂ → ℂ := basinPhi f a r M with hΦdef
  have hΦapply : ∀ z : ℂ, Φ z = fatouCoord f (1 - a) (f^[firstHit f r M z] z)
      - (firstHit f r M z : ℂ) := fun _ => rfl
  have hpetal_basin : Work.FatouCoord.Petal r M ⊆ MandelDim.ParabolicBasin f D := by
    intro z hz
    refine ⟨Work.FatouCoord.Petal r M, isOpen_Petal.mem_nhds hz, ?_, hunifP⟩
    intro n w hw
    exact hball (Work.FatouCoord.Petal_subset_ball
      (mapsTo_iterate_of_mapsTo hmaps n hw))
  have hhit0 : ∀ z ∈ Work.FatouCoord.Petal r M, firstHit f r M z = 0 := by
    intro z hz
    have h0 : f^[0] z ∈ Work.FatouCoord.Petal r M ∨ f^[0] z = 0 := Or.inl (by simpa using hz)
    have := firstHit_le (f := f) (r := r) (M := M) (hgood z (hpetal_basin hz)) h0
    omega
  have hΦpetal : ∀ z ∈ Work.FatouCoord.Petal r M, Φ z = fatouCoord f (1 - a) z := by
    intro z hz
    rw [hΦapply z, hhit0 z hz]
    simp
  have hinjΦ : Set.InjOn Φ (Work.FatouCoord.Petal r M) := by
    intro z hz z' hz' heq
    rw [hΦpetal z hz, hΦpetal z' hz'] at heq
    exact hinjφ hz hz' heq
  -- the index of the image
  have hIdx_abel : ∀ z ∈ MandelDim.ParabolicBasin f D, firstHit f r M z ≠ 0 →
      firstHit f r M (f z) + 1 = firstHit f r M z := by
    intro z hz hne
    have hzg := hgood z hz
    have hspec := firstHit_spec (f := f) (r := r) (M := M) hzg
    have hpos : 0 < firstHit f r M z := Nat.pos_of_ne_zero hne
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have h1 : f^[j] (f z) = f^[firstHit f r M z] z := by
      rw [hj, Function.iterate_succ_apply]
    have hgood' : f^[j] (f z) ∈ Work.FatouCoord.Petal r M ∨ f^[j] (f z) = 0 := by
      rw [h1]; exact hspec
    have hex' : ∃ k : ℕ, f^[k] (f z) ∈ Work.FatouCoord.Petal r M ∨ f^[k] (f z) = 0 :=
      ⟨j, hgood'⟩
    have hle : firstHit f r M (f z) ≤ j :=
      firstHit_le (f := f) (r := r) (M := M) (z := f z) hex' hgood'
    have hspec' := firstHit_spec (f := f) (r := r) (M := M) (z := f z) hex'
    have hgood2 : f^[firstHit f r M (f z) + 1] z ∈ Work.FatouCoord.Petal r M ∨
        f^[firstHit f r M (f z) + 1] z = 0 := by
      rw [Function.iterate_succ_apply]
      exact hspec'
    have hle2 : firstHit f r M z ≤ firstHit f r M (f z) + 1 := firstHit_le hzg hgood2
    omega
  -- the Abel equation
  have habel : ∀ z ∈ MandelDim.ParabolicBasin f D, Φ (f z) = Φ z + 1 := by
    intro z hz
    rcases Nat.eq_zero_or_pos (firstHit f r M z) with h0 | hpos
    · -- z lies in the petal
      have hspec := firstHit_spec (f := f) (r := r) (M := M) (hgood z hz)
      have hzP : z ∈ Work.FatouCoord.Petal r M := by
        rw [h0] at hspec
        rcases hspec with hp | hz0
        · exact hp
        · exact absurd (hz0 ▸ hz) hzero
      have hfP : f z ∈ Work.FatouCoord.Petal r M := hmaps hzP
      have hfP0 : f^[0] (f z) ∈ Work.FatouCoord.Petal r M := by simpa using hfP
      have hex : ∃ k : ℕ, f^[k] (f z) ∈ Work.FatouCoord.Petal r M ∨ f^[k] (f z) = 0 :=
        ⟨0, Or.inl hfP0⟩
      have hfx : firstHit f r M (f z) = 0 := by
        have := firstHit_le (f := f) (r := r) (M := M) (z := f z) hex (Or.inl hfP0)
        omega
      rw [hΦapply (f z), hΦapply z, hfx, h0]
      simp only [Function.iterate_zero, id_eq, Nat.cast_zero, sub_zero]
      rw [hfatou.2 z hzP]
    · have hh := hIdx_abel z hz (Nat.pos_iff_ne_zero.mp hpos)
      have h1 : f^[firstHit f r M (f z)] (f z) = f^[firstHit f r M z] z := by
        rw [← hh, Function.iterate_succ_apply]
      have hc : ((firstHit f r M (f z) : ℕ) : ℂ)
          = ((firstHit f r M z : ℕ) : ℂ) - 1 := by
        have h2 := congrArg (fun k : ℕ => (k : ℂ)) hh
        push_cast at h2
        linear_combination h2
      rw [hΦapply (f z), hΦapply z, h1, hc]
      ring
  -- differentiability on the basin
  have hdiffΦ : DifferentiableOn ℂ Φ (MandelDim.ParabolicBasin f D) := by
    intro z hz
    have hzg := hgood z hz
    have hspec := firstHit_spec (f := f) (r := r) (M := M) hzg
    rcases hspec with hentry | hhit
    · -- the orbit of `z` enters the petal
      have hcont : ContinuousAt (f^[firstHit f r M z]) z := (hcontIter z hz _).continuousAt
      have hV : (f^[firstHit f r M z]) ⁻¹' Work.FatouCoord.Petal r M ∈ nhds z :=
        hcont.preimage_mem_nhds (isOpen_Petal.mem_nhds hentry)
      have hφAt : DifferentiableAt ℂ (fatouCoord f (1 - a)) (f^[firstHit f r M z] z) :=
        hfatou.1.differentiableAt (isOpen_Petal.mem_nhds hentry)
      have hθdiff : DifferentiableAt ℂ (fun u : ℂ =>
          fatouCoord f (1 - a) (f^[firstHit f r M z] u) - (firstHit f r M z : ℂ)) z :=
        ((hφAt.comp z (hcontIter z hz _))).sub_const _
      refine hθdiff.differentiableWithinAt.congr_of_eventuallyEq ?_ rfl
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hV] with u huB hVu
      have hgoodU : ∃ k : ℕ, f^[k] u ∈ Work.FatouCoord.Petal r M ∨ f^[k] u = 0 := hgood u huB
      have hle : firstHit f r M u ≤ firstHit f r M z :=
        firstHit_le (f := f) (r := r) (M := M) hgoodU (Or.inl hVu)
      have hspecU := firstHit_spec (f := f) (r := r) (M := M) hgoodU
      rw [hΦapply u]
      rcases hspecU with hmem | hz0
      · exact (petal_coord_consistent (f := f) (z := u) (n := firstHit f r M u)
          (m := firstHit f r M z) hfatou hmaps hmem hle hVu).symm
      · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
        have hmemZ : f^[firstHit f r M z] u ∈ Work.FatouCoord.Petal r M := hVu
        have hzeroN : f^[firstHit f r M z] u = 0 := by
          have hdecomp : f^[firstHit f r M z] u = f^[c] (f^[firstHit f r M u] u) := by
            rw [hc, Nat.add_comm, Function.iterate_add_apply]
          rw [hdecomp, hz0]
          exact hiter0 c
        rw [hzeroN] at hmemZ
        exact (Work.FatouCoord.not_mem_Petal_zero hmemZ).elim
    · -- the orbit of `z` hits `0`
      obtain ⟨V₀, hV₀, hV₀z⟩ := locally_constant_of_hits_zero hg.1 hg.2.2.1 hz hzero hhit
      have hV₀' : ∀ᶠ u in nhds z, f^[firstHit f r M z] u = 0 :=
        Filter.mem_of_superset hV₀ hV₀z
      have hEv : ∀ᶠ u in nhds z, ∀ k : Fin (firstHit f r M z), f^[(k : ℕ)] u ≠ 0 := by
        rw [Filter.eventually_all]
        intro k
        have hk : (k : ℕ) < firstHit f r M z := k.2
        have hkne : f^[(k : ℕ)] z ≠ 0 := by
          intro hc
          have := firstHit_le (f := f) (r := r) (M := M) hzg (Or.inr hc)
          omega
        exact (hcontIter z hz (k : ℕ)).continuousAt.eventually_ne hkne
      have hconst : ∀ᶠ u in nhdsWithin z (MandelDim.ParabolicBasin f D),
          Φ u = fatouCoord f (1 - a) 0 - (firstHit f r M z : ℂ) := by
        filter_upwards [nhdsWithin_le_nhds hV₀', nhdsWithin_le_nhds hEv, self_mem_nhdsWithin]
          with u hu₁ hu₂ huB
        have hgoodU : ∃ k : ℕ, f^[k] u ∈ Work.FatouCoord.Petal r M ∨ f^[k] u = 0 := hgood u huB
        have hspecU := firstHit_spec (f := f) (r := r) (M := M) hgoodU
        have hle : firstHit f r M u ≤ firstHit f r M z :=
          firstHit_le (f := f) (r := r) (M := M) hgoodU (Or.inr hu₁)
        have hge : firstHit f r M z ≤ firstHit f r M u := by
          by_contra hc
          push_neg at hc
          rcases hspecU with hmem | hz0
          · obtain ⟨c, hc'⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hc)
            have hmemN : f^[firstHit f r M z] u ∈ Work.FatouCoord.Petal r M := by
              have hdecomp : f^[firstHit f r M z] u = f^[c] (f^[firstHit f r M u] u) := by
                rw [hc', Nat.add_comm, Function.iterate_add_apply]
              rw [hdecomp]
              exact mapsTo_iterate_of_mapsTo hmaps c hmem
            rw [hu₁] at hmemN
            exact Work.FatouCoord.not_mem_Petal_zero hmemN
          · exact (hu₂ ⟨firstHit f r M u, hc⟩) hz0
        have heq : firstHit f r M u = firstHit f r M z := le_antisymm hle hge
        rw [hΦapply u, heq, hu₁]
      have hzconst : Φ z = fatouCoord f (1 - a) 0 - (firstHit f r M z : ℂ) := by
        rw [hΦapply z, hhit]
      exact (differentiableWithinAt_const
        (c := fatouCoord f (1 - a) 0 - (firstHit f r M z : ℂ))).congr_of_eventuallyEq hconst
        hzconst
  exact ⟨Φ, h, a, r, A, A', M, hb, hball, hMpos, hpetal_basin, hmaps, hconvP, hdiffΦ, habel,
    hinjΦ, hΦpetal⟩

end

end Work.Parab.basinCoord
