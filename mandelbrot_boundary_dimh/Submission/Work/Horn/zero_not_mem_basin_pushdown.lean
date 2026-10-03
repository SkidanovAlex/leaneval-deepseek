import Mathlib
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.basin_basic_Dg
import Submission.Work.Horn.fiber_infinite_in_basin

/-!
# `Work.Horn.zero_not_mem_basin_pushdown`

`0` is not in the parabolic basin of the pushed-down horn map `g = pushdown d.E` on
`D_g = {0} ∪ π '' (Bu ∪ Bl)`.

On the domain of the statement, `Bu ⊇ {Im > η}` contains the whole upper half plane above `η`,
so `D_g` contains a *punctured disc* around `0`, hence an honest ball `ball 0 r` around `0`
(any point `0 < |ζ| < e^{-2πη'}` has its principal lift `log ζ/(2πi)` at imaginary part `> η'`,
see `exists_ball_subset_insert_piExp_of_upper`).  So `D_g` is a neighbourhood of the fixed point
`0` at which `g` is holomorphic (`pushdown_g_holo`), fixes `0` (`pushdown` by definition) and has
`deriv g 0 = 1` (`deriv_pushdown_E`, Shishikura's normalisation (4.1.5)).

With those three inputs the claim is a purely analytic fact about *uniform* convergence to the
fixed point, proved by Cauchy's estimate: if `0` were in the basin, some iterate `g^[N]` would
satisfy `‖g^[N] z‖ < R` on the sphere of radius `R = ε/2` (`ε` the radius of a basin witness
ball), whence `‖deriv (g^[N]) 0‖ ≤ 1/2` by Cauchy's estimate — while the chain rule at the
fixed point gives `deriv (g^[N]) 0 = (deriv g 0)^N = 1`.  See `not_mem_basin_of_deriv_eq_one`.
-/

open MandelDim Set Metric Filter Topology
open scoped Topology

namespace Work.Horn

noncomputable section

/-- **`D_g = {0} ∪ π '' (Bu ∪ Bl)` contains a ball around `0`** as soon as `Bu` contains the
half plane `{Im > η}`.

Proof: the map `ζ ↦ log ζ/(2πi)` tends to the upper end as `ζ → 0`
(`MandelDim.tendsto_log_div_upperEnd`), so for `ζ ≠ 0` close enough to `0` the lift
`log ζ/(2πi)` has imaginary part `> η + 1 > η`, hence lies in `Bu`, and `π` of it is `ζ`
(`piExp_log_div`).  Being close to `0` is an open condition, so it holds on a ball. -/
theorem exists_ball_subset_insert_piExp_of_upper {Bu Bl : Set ℂ} {η : ℝ}
    (hup : {w : ℂ | η < w.im} ⊆ Bu) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := by
  have hset : {w : ℂ | η + 1 < w.im} ∈ MandelDim.upperEnd := by
    rw [MandelDim.upperEnd, Filter.mem_comap]
    exact ⟨Set.Ioi (η + 1), Ioi_mem_atTop _, fun z hz => hz⟩
  have hEv : {ζ : ℂ | η + 1 < (Complex.log ζ / (2 * Real.pi * Complex.I)).im} ∈
      𝓝[≠] (0 : ℂ) :=
    Work.Horn.MandelDim.tendsto_log_div_upperEnd.eventually hset
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhdsWithin_iff.mp hEv
  refine ⟨r, hr, fun ζ hζ => ?_⟩
  by_cases h0 : ζ = 0
  · exact Set.mem_insert_iff.mpr (Or.inl h0)
  · refine Set.mem_insert_iff.mpr (Or.inr ?_)
    have him : η + 1 < (Complex.log ζ / (2 * Real.pi * Complex.I)).im := hrsub ⟨hζ, h0⟩
    have hlt : η < (Complex.log ζ / (2 * Real.pi * Complex.I)).im := by linarith
    have hmem : Complex.log ζ / (2 * Real.pi * Complex.I) ∈ Bu := hup hlt
    exact ⟨Complex.log ζ / (2 * Real.pi * Complex.I), Set.subset_union_left hmem,
      Work.Horn.MandelDim.piExp_log_div ζ h0⟩

/-- **The analytic core.**  Let `g` be holomorphic on a set `D` containing a ball around `0`,
with `g 0 = 0` and `deriv g 0 = 1`.  Then `0` is not in the parabolic basin of `g` on `D`:
uniform convergence of the iterates on a neighbourhood forbids the multiplier `1`.

If `0` were in the basin, some iterate `g^[N]` would map the sphere of radius `R = ε/2` into the
ball of radius `R/2` (with `ball 0 ε` the basin witness), so Cauchy's estimate on `ball 0 R`
gives `‖deriv (g^[N]) 0‖ ≤ 1/2`; but `g^[N]` is holomorphic on `ball 0 ε` (composition, using
`MapsTo` of the iterates into `D`) and fixes `0`, so the chain rule gives
`deriv (g^[N]) 0 = (deriv g 0)^N = 1`. -/
theorem not_mem_basin_of_deriv_eq_one {g : ℂ → ℂ} {D : Set ℂ} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : ℂ) r ⊆ D) (hholo : DifferentiableOn ℂ g D) (hg0 : g 0 = 0)
    (hder : deriv g 0 = 1) :
    (0 : ℂ) ∉ MandelDim.ParabolicBasin g D := by
  rintro ⟨U, hU, hmap, hunif⟩
  -- a ball around `0` lying both in the basin witness `U` and in `D`
  obtain ⟨ε₀, hε₀, hε₀U⟩ := Metric.mem_nhds_iff.mp hU
  set ε : ℝ := min ε₀ r with hεdef
  have hεpos : 0 < ε := lt_min hε₀ hr
  have hεU : ball (0 : ℂ) ε ⊆ U :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hε₀U
  have hmapU : ∀ n : ℕ, MapsTo (g^[n]) (ball (0 : ℂ) ε) D := fun n z hz => hmap n (hεU hz)
  have hunifU : TendstoUniformlyOn (fun n : ℕ => g^[n]) (fun _ => (0 : ℂ)) atTop
      (ball (0 : ℂ) ε) := hunif.mono hεU
  -- all iterates are holomorphic on that ball
  have hiter_diff : ∀ n : ℕ, DifferentiableOn ℂ (g^[n]) (ball (0 : ℂ) ε) := by
    intro n
    induction n with
    | zero => simpa using differentiableOn_id
    | succ k ih =>
        rw [Function.iterate_succ']
        exact hholo.comp ih (fun z hz => hmapU k hz)
  rw [Metric.tendstoUniformlyOn_iff] at hunifU
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hunifU (ε / 2) (by linarith))
  set R : ℝ := ε / 2 with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  have hball_sub : ball (0 : ℂ) R ⊆ ball (0 : ℂ) ε := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [hR] at hz; linarith
  have hcont : ContinuousOn (g^[N]) (closedBall (0 : ℂ) R) := by
    intro z hz
    have hzε : z ∈ ball (0 : ℂ) ε := by
      rw [mem_closedBall_zero_iff] at hz
      rw [mem_ball_zero_iff]
      rw [hR] at hz; linarith
    exact ((hiter_diff N).differentiableAt (isOpen_ball.mem_nhds hzε)).continuousAt.continuousWithinAt
  -- a point of the sphere of radius `R` maximising `‖g^[N]‖`
  have hsphere_ne : (sphere (0 : ℂ) R).Nonempty :=
    ⟨(R : ℂ), by rw [mem_sphere_iff_norm]; simp [Complex.norm_real, abs_of_nonneg hRpos.le]⟩
  obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMaxOn hsphere_ne
    ((hcont.mono sphere_subset_closedBall).norm) (f := fun z => ‖g^[N] z‖)
  have hz₀ε : z₀ ∈ ball (0 : ℂ) ε := by
    have h : ‖z₀‖ = R := by simpa using (mem_sphere_iff_norm.mp hz₀)
    rw [mem_ball_zero_iff, h, hR]; linarith
  have hgN₀ : ‖g^[N] z₀‖ < R := by
    have h := hN N le_rfl z₀ hz₀ε
    rw [dist_eq_norm, zero_sub, norm_neg] at h
    rw [hR]
    exact h
  -- the iterates have derivative `1` at `0` (chain rule at the fixed point)
  have hiter0 : ∀ k : ℕ, g^[k] (0 : ℂ) = 0 := fun k => Function.iterate_fixed hg0 k
  have hgdiff : DifferentiableAt ℂ g 0 :=
    hholo.differentiableAt (Filter.mem_of_superset
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by simpa using hr))) hball)
  have hiterdiff : ∀ k : ℕ, DifferentiableAt ℂ (g^[k]) (0 : ℂ) := by
    intro k
    induction k with
    | zero => exact differentiableAt_id
    | succ j ih =>
        rw [Function.iterate_succ']
        exact DifferentiableAt.comp (0 : ℂ) (by rw [hiter0 j]; exact hgdiff) ih
  have hrec : ∀ k : ℕ, deriv (g^[k.succ]) (0 : ℂ) = deriv g (g^[k] 0) * deriv (g^[k]) 0 := by
    intro k
    rw [Function.iterate_succ']
    exact deriv_comp (0 : ℂ) (by rw [hiter0 k]; exact hgdiff) (hiterdiff k)
  have hderiv_all : ∀ n : ℕ, deriv (g^[n]) (0 : ℂ) = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [hrec k, hiter0 k, hder, ih, one_mul]
  -- Cauchy's estimate on the disc of radius `R`
  have hcauchy : ‖deriv (g^[N]) 0‖ ≤ ‖g^[N] z₀‖ / R := by
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos ⟨?_, ?_⟩ (fun z hz => hmax hz)
    · exact (hiter_diff N).mono hball_sub
    · simpa [closure_ball (0 : ℂ) (ne_of_gt hRpos)] using hcont
  rw [hderiv_all N, norm_one] at hcauchy
  have : ‖g^[N] z₀‖ / R < 1 := by
    rw [div_lt_one hRpos]
    exact hgN₀
  linarith

theorem zero_not_mem_basin_pushdown {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    (0 : ℂ) ∉ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := by
  obtain ⟨r, hr, hball⟩ := exists_ball_subset_insert_piExp_of_upper (Bu := Bu) (Bl := Bl) hup
  exact not_mem_basin_of_deriv_eq_one hr hball
    (Work.Horn.pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo)
    (Work.Horn.MandelDim.pushdown_zero d.E)
    (Work.Horn.MandelDim.deriv_pushdown_E d)

end

end Work.Horn
