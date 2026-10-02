import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.isPreconnected_rayAccum
import Submission.Work.LandLeaves.isCompact_rayAccum
import Submission.Work.LandLeaves.rayAccum_nonempty
import Submission.Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher
import Submission.Work.Landing.Angle.angDouble_iterate_succ
import Submission.Work.Landing.Land.Landing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Classical
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## Elementary angle lemmas -/

/-- `rayDirection (n * α) = rayDirection α ^ n`. -/
theorem rayDirection_nat_mul (α : ℝ) (n : ℕ) :
    Work.Landing.rayDirection ((n : ℝ) * α) = Work.Landing.rayDirection α ^ n := by
  rw [Work.Landing.rayDirection, Work.Landing.rayDirection, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Two angles with the same direction differ by an integer. -/
theorem exists_int_of_rayDirection_eq {α β : ℝ}
    (h : Work.Landing.rayDirection α = Work.Landing.rayDirection β) :
    ∃ n : ℤ, α = β + n := by
  simp only [Work.Landing.rayDirection] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have h2 : (↑(2 * Real.pi * α) : ℂ) * Complex.I =
      (↑(2 * Real.pi * β) : ℂ) * Complex.I + (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I := by
    rw [hn]; push_cast; ring
  have h3 : (↑(2 * Real.pi * α) : ℂ) * Complex.I =
      (↑(2 * Real.pi * β) + ↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I := by
    rw [h2]; ring
  have h4 := mul_right_cancel₀ Complex.I_ne_zero h3
  have h4' : (↑(2 * Real.pi * α) : ℂ) = ↑(2 * Real.pi * β + 2 * Real.pi * (n : ℝ)) := by
    rw [h4]; push_cast; ring
  have h5 : 2 * Real.pi * α = 2 * Real.pi * β + 2 * Real.pi * (n : ℝ) :=
    Complex.ofReal_inj.mp h4'
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h6 : 2 * Real.pi * α = 2 * Real.pi * (β + (n : ℝ)) := by linarith [h5]
  exact mul_left_cancel₀ hpi h6

/-- The direction of the angle `arg w / (2π)` is the unit vector `w / ‖w‖`. -/
theorem rayDirection_arg_div (w : ℂ) (hw : w ≠ 0) :
    Work.Landing.rayDirection (w.arg / (2 * Real.pi)) = w / (‖w‖ : ℂ) := by
  rw [Work.Landing.rayDirection]
  have harg : (2 * Real.pi) * (w.arg / (2 * Real.pi)) = w.arg := by field_simp
  rw [harg]
  have hnorm : (↑‖w‖ : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using norm_ne_zero_iff.mpr hw
  rw [eq_div_iff hnorm, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I w

/-- The normalised argument `arg w / 2π` lies in `(-1/2, 1/2]`. -/
theorem arg_div_two_pi_mem (w : ℂ) :
    -(1 : ℝ) / 2 < w.arg / (2 * Real.pi) ∧ w.arg / (2 * Real.pi) ≤ 1 / 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 := Complex.neg_pi_lt_arg w
  have h2 := Complex.arg_le_pi w
  constructor
  · rw [lt_div_iff₀ hpi]; linarith
  · rw [div_le_iff₀ hpi]; linarith

/-- Pigeonhole: a function `ℕ → ℤ` with bounded range takes some value infinitely often. -/
theorem exists_infinite_fiber_of_bdd {f : ℕ → ℤ} {A B : ℤ} (h : ∀ n, A ≤ f n ∧ f n ≤ B) :
    ∃ m : ℤ, Set.Infinite {n : ℕ | f n = m} := by
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber (fun n : ℕ => (⟨f n, h n⟩ : Set.Icc A B))
  refine ⟨b.1, (Set.infinite_coe_iff.mp hb).mono ?_⟩
  rintro n (hn : (⟨f n, h n⟩ : Set.Icc A B) = b)
  have : ((⟨f n, h n⟩ : Set.Icc A B)).1 = b.1 := by rw [hn]
  exact this

/-! ## The main statement -/

theorem exists_preimage_rayAccum {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ} {θ : ℝ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (h : Work.Landing.rayAccum c φ θ = {y}) :
    ∃ θ' : ℝ, Work.Landing.rayAccum c φ θ' = {y} ∧ ∃ m : ℤ, (4 : ℝ) ^ k * θ' = θ + m := by
  have hk : 0 < k := hrep.1.1
  obtain ⟨r, r', κ, g, hr, hrr', hκ0, hκ1, hgy, hcontr, hright, hleft⟩ :=
    Work.LandLeaves.exists_local_repelling_branch hrep
  have hr'pos : 0 < r' := lt_trans hr hrr'
  set N : ℕ := 4 ^ k with hNdef
  have hNpos : 0 < N := by rw [hNdef]; positivity
  have hNne : (N : ℝ) ≠ 0 := by positivity
  have hNcast : (N : ℝ) = (4 : ℝ) ^ k := by rw [hNdef]; push_cast; ring
  -- `y` is in the accumulation set of the ray at angle `θ`
  have hy : y ∈ Work.Landing.rayAccum c φ θ := by rw [h]; exact Set.mem_singleton y
  have hy' : ∀ ρ : ℝ, 1 < ρ →
      y ∈ closure {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖φ z‖ ≤ ρ} := hy
  -- the approximating ray points `z n`
  have hzn : ∀ n : ℕ, ∃ z : ℂ, z ∈ Work.Landing.dynRay c φ θ ∧
      ‖φ z‖ ≤ Work.LandLeaves.levelSeq n ∧ ‖z - y‖ < min r' (1 / ((n : ℝ) + 1)) := by
    intro n
    have hδ : 0 < min r' (1 / ((n : ℝ) + 1)) := lt_min hr'pos (by positivity)
    obtain ⟨z, hz, hzd⟩ := Metric.mem_closure_iff.mp (hy' _ (Work.LandLeaves.one_lt_levelSeq n)) _ hδ
    exact ⟨z, hz.1, hz.2, by rwa [dist_comm, dist_eq_norm] at hzd⟩
  choose z hz using hzn
  have hzn_r' : ∀ n, ‖z n - y‖ ≤ r' :=
    fun n => le_trans (le_of_lt (hz n).2.2) (min_le_left _ _)
  have hFu : ∀ n, (Tantibar c)^[2 * k] (g (z n)) = z n := fun n => hright (z n) (hzn_r' n)
  -- `g (z n)` tends to `y`
  have huy : Filter.Tendsto (fun n => g (z n)) Filter.atTop (𝓝 y) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hε
    refine ⟨N₀, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have h1 : ‖g (z n) - y‖ ≤ κ * ‖z n - y‖ := hcontr (z n) (hzn_r' n)
    have h2 : ‖z n - y‖ < 1 / ((n : ℝ) + 1) := lt_of_lt_of_le (hz n).2.2 (min_le_right _ _)
    have h3 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((N₀ : ℝ) + 1) := by
      have hn' : (N₀ : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        have : N₀ + 1 ≤ n + 1 := by omega
        exact_mod_cast this
      exact one_div_le_one_div_of_le (by positivity) hn'
    have h4 : ‖g (z n) - y‖ ≤ ‖z n - y‖ := by
      calc ‖g (z n) - y‖ ≤ κ * ‖z n - y‖ := h1
        _ ≤ 1 * ‖z n - y‖ := by nlinarith [norm_nonneg (z n - y)]
        _ = ‖z n - y‖ := one_mul _
    linarith [hN₀, h2, h3]
  -- `g (z n)` is escaping
  have huesc : ∀ n, Work.ParamRays.Escaping c (g (z n)) := by
    intro n
    rw [Work.ParamRays.escaping_iff_not_bounded]
    intro hb
    obtain ⟨M, hM⟩ := hb
    have hb' : Work.ParamRays.BoundedOrbit c (z n) := by
      refine ⟨M, fun m => ?_⟩
      have h1 : Work.ParamRays.orbit c (z n) m = Work.ParamRays.orbit c (g (z n)) (m + 2 * k) := by
        rw [Work.ParamRays.orbit, Work.ParamRays.orbit, Function.iterate_add_apply, hFu n]
      rw [h1]; exact hM (m + 2 * k)
    exact (Work.ParamRays.escaping_iff_not_bounded c (z n)).mp (hz n).1.1 hb'
  -- the Böttcher equation for the iterate
  have hphiu : ∀ n, (φ (g (z n))) ^ N = φ (z n) := by
    intro n
    have h1 := Work.ParamRays.IsDynBottcher.functional_iterate hφ (huesc n) k
    have h2 : Work.ParamRays.orbit c (g (z n)) (2 * k) = z n := hFu n
    rw [h2, ← hNdef] at h1
    exact h1.symm
  -- the ray point `φ (z n)` lies on the radial line at angle `θ`
  have hrad : ∀ n, ∃ s : ℝ, 1 < s ∧ φ (z n) = (s : ℂ) * Work.Landing.rayDirection θ :=
    fun n => (hz n).1.2
  set θn : ℕ → ℝ := fun n => (φ (g (z n))).arg / (2 * Real.pi) with hθndef
  have hwn_ne : ∀ n, φ (g (z n)) ≠ 0 := by
    intro n h0
    obtain ⟨s, hs1, hs⟩ := hrad n
    have h1 : (0 : ℂ) = φ (z n) := by
      have h2 := hphiu n
      rw [h0, zero_pow (pow_ne_zero k (by norm_num : (4:ℕ) ≠ 0))] at h2
      exact h2
    rw [hs] at h1
    have hnorm : ‖(s : ℂ) * Work.Landing.rayDirection θ‖ = s := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith),
        Work.Landing.Rays.norm_rayDirection, mul_one]
    rw [← h1, norm_zero] at hnorm
    linarith
  have hray_theta : ∀ n, Work.Landing.rayDirection (θn n) =
      φ (g (z n)) / (‖φ (g (z n))‖ : ℂ) := fun n => rayDirection_arg_div _ (hwn_ne n)
  -- the direction at `N θn n` is the direction at `θ`
  have hrayN : ∀ n, Work.Landing.rayDirection ((N : ℝ) * θn n) =
      Work.Landing.rayDirection θ := by
    intro n
    rw [rayDirection_nat_mul, hray_theta n]
    obtain ⟨s, hs1, hs⟩ := hrad n
    have hnorm : ‖φ (g (z n))‖ ^ N = s := by
      rw [← Complex.norm_pow, hphiu n, hs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith), Work.Landing.Rays.norm_rayDirection, mul_one]
    have hnum : (φ (g (z n))) ^ N = (s : ℂ) * Work.Landing.rayDirection θ := by
      rw [hphiu n]; exact hs
    have hden : ((‖φ (g (z n))‖ : ℂ)) ^ N = (s : ℂ) := by
      rw [← Complex.ofReal_pow, hnorm]
    rw [div_pow, hnum, hden]
    exact mul_div_cancel_left₀ (Work.Landing.rayDirection θ)
      (by simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt (lt_trans zero_lt_one hs1))
  choose mn hmn using fun n => exists_int_of_rayDirection_eq (hrayN n)
  have hmn_bound : ∀ n,
      ⌊-(N : ℝ) / 2 - θ⌋ + 1 ≤ mn n ∧ mn n ≤ ⌊(N : ℝ) / 2 - θ⌋ := by
    intro n
    have hb := arg_div_two_pi_mem (φ (g (z n)))
    have hNpos' : (0 : ℝ) < (N : ℝ) := by positivity
    have hm' : (mn n : ℝ) = (N : ℝ) * θn n - θ := by
      have := hmn n; linarith [this]
    constructor
    · have hlt : -(N : ℝ) / 2 - θ < (mn n : ℝ) := by nlinarith [hb.1, hm', hNpos']
      exact Int.lt_iff_add_one_le.mp (Int.floor_lt.mpr hlt)
    · have hle : (mn n : ℝ) ≤ (N : ℝ) / 2 - θ := by nlinarith [hb.2, hm', hNpos']
      exact Int.le_floor.mpr hle
  obtain ⟨m, hm_inf⟩ := exists_infinite_fiber_of_bdd (f := mn) hmn_bound
  have hmain : (4 : ℝ) ^ k * ((θ + m) / (N : ℝ)) = θ + m := by
    rw [← hNcast]
    field_simp
  refine ⟨(θ + m) / (N : ℝ), ?_, ⟨m, hmain⟩⟩
  -- `y` lies in the accumulation set of the ray at angle `θ'`
  have hmem : y ∈ Work.Landing.rayAccum c φ ((θ + m) / (N : ℝ)) := by
    intro ρ hρ
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hη : 0 < ρ ^ N - 1 := by
      have : 1 < ρ ^ N := one_lt_pow₀ hρ hNpos.ne'
      linarith
    obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt hη
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp huy ε hε
    obtain ⟨n, hn_fib, hn_gt⟩ := hm_inf.exists_gt (max N₁ N₂)
    have hn₁ : N₁ ≤ n := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn_gt)
    have hn₂ : N₂ < n := lt_of_le_of_lt (le_max_right _ _) hn_gt
    have hθn : θn n = (θ + m) / (N : ℝ) := by
      have h := hmn n
      rw [hn_fib] at h
      rw [eq_div_iff hNne]; linarith [h]
    have hlevn : Work.LandLeaves.levelSeq n = 1 + 1 / ((n : ℝ) + 1) := rfl
    have hlev : ‖φ (g (z n))‖ ^ N < ρ ^ N := by
      rw [← Complex.norm_pow, hphiu n]
      have hle : ‖φ (z n)‖ ≤ 1 + 1 / ((n : ℝ) + 1) := by rw [← hlevn]; exact (hz n).2.1
      have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N₂ : ℝ) + 1) := by
        have hn' : (N₂ : ℝ) + 1 ≤ (n : ℝ) + 1 := by
          have : N₂ + 1 ≤ n + 1 := by omega
          exact_mod_cast this
        exact one_div_le_one_div_of_le (by positivity) hn'
      linarith [hN₂, h2, hle]
    have hltρ : ‖φ (g (z n))‖ < ρ :=
      (pow_lt_pow_iff_left₀ (norm_nonneg _) (by linarith : (0 : ℝ) ≤ ρ) hNpos.ne').mp hlev
    refine ⟨g (z n), ⟨⟨huesc n, ⟨‖φ (g (z n))‖, ?_, ?_⟩⟩, ?_⟩, ?_⟩
    · have h1 : ‖φ (g (z n))‖ ^ N = ‖φ (z n)‖ := by rw [← Complex.norm_pow, hphiu n]
      obtain ⟨s, hs1, hs⟩ := hrad n
      have hnormz : ‖φ (z n)‖ = s := by
        rw [hs, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith),
          Work.Landing.Rays.norm_rayDirection, mul_one]
      have h2 : (1 : ℝ) ^ N < ‖φ (g (z n))‖ ^ N := by
        rw [h1, hnormz, one_pow]; exact hs1
      exact lt_of_pow_lt_pow_left₀ N (norm_nonneg _) h2
    · rw [← hθn, hray_theta n, ← mul_div_assoc]
      exact (mul_div_cancel_left₀ (φ (g (z n)))
        (by rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr (hwn_ne n))).symm
    · exact le_of_lt hltρ
    · rw [dist_comm]; exact hN₁ n hn₁
  -- the accumulation set is a singleton
  have hfract : Work.Landing.rayAccum c φ (Int.fract θ) = Work.Landing.rayAccum c φ θ := by
    have h1 : Int.fract θ = θ + ((-⌊θ⌋ : ℤ) : ℝ) := by
      have := Int.fract_add_floor θ; push_cast; linarith
    rw [h1, Work.FSeed.rayAccum_add_int]
  have hang : (Work.Landing.angDouble)^[2 * k] ((θ + m) / (N : ℝ)) = Int.fract θ := by
    have h2k : 2 * k = (2 * k - 1) + 1 := by omega
    rw [h2k, Work.Landing.Angle.angDouble_iterate_succ]
    have hpow : (-2 : ℝ) ^ ((2 * k - 1) + 1) = (4 : ℝ) ^ k := by
      rw [← h2k, pow_mul]; norm_num
    rw [hpow, hmain]
    exact Work.FSeed.fract_add_int θ m
  have hFimg : (Tantibar c)^[2 * k] '' Work.Landing.rayAccum c φ ((θ + m) / (N : ℝ)) =
      ({y} : Set ℂ) := by
    rw [← Work.Landing.rayAccum_iterate hφ ((θ + m) / (N : ℝ)) (2 * k), hang, hfract, h]
  have hA : ∀ x ∈ Work.Landing.rayAccum c φ ((θ + m) / (N : ℝ)), (Tantibar c)^[2 * k] x = y := by
    intro x hx
    have h1 : (Tantibar c)^[2 * k] x ∈
        (Tantibar c)^[2 * k] '' Work.Landing.rayAccum c φ ((θ + m) / (N : ℝ)) := ⟨x, hx, rfl⟩
    rw [hFimg] at h1
    simpa using h1
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨hmem, ?_⟩
  intro x hx
  by_contra hxy
  have hball : ∀ w ∈ Work.Landing.rayAccum c φ ((θ + m) / (N : ℝ)), ‖w - y‖ < r → w = y := by
    intro w hw hwr
    have h1 : ‖(Tantibar c)^[2 * k] w - y‖ ≤ r' := by
      rw [hA w hw, sub_self, norm_zero]; exact hr'pos.le
    have h2 := hleft w hwr.le h1
    rw [hA w hw, hgy] at h2
    exact h2.symm
  have hxr : r ≤ ‖x - y‖ := by
    by_contra hcon
    exact hxy (hball x hx (lt_of_not_ge hcon))
  have hpre : IsPreconnected ((fun w : ℂ => ‖w - y‖) ''
      Work.Landing.rayAccum c φ ((θ + m) / (N : ℝ))) :=
    (Work.LandLeaves.isPreconnected_rayAccum hφ _).image _ (by fun_prop)
  have h0mem : (0 : ℝ) ∈ (fun w : ℂ => ‖w - y‖) ''
      Work.Landing.rayAccum c φ ((θ + m) / (N : ℝ)) := ⟨y, hmem, by simp⟩
  have hxmem : ‖x - y‖ ∈ (fun w : ℂ => ‖w - y‖) ''
      Work.Landing.rayAccum c φ ((θ + m) / (N : ℝ)) := ⟨x, hx, rfl⟩
  have hr2mem : r / 2 ∈ Set.Icc (0 : ℝ) ‖x - y‖ := ⟨by linarith, by linarith⟩
  have hr2 : r / 2 ∈ (fun w : ℂ => ‖w - y‖) ''
      Work.Landing.rayAccum c φ ((θ + m) / (N : ℝ)) :=
    hpre.ordConnected.out' h0mem hxmem hr2mem
  obtain ⟨a, ha, har⟩ := hr2
  have har' : ‖a - y‖ = r / 2 := har
  have haz : a = y := hball a ha (by rw [har']; linarith)
  rw [haz, sub_self, norm_zero] at har'
  linarith

end

end Work.LandLeaves
