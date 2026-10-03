import Mathlib
import Submission.Work.Horn.flower_defs
import Submission.Work.Horn.basin

/-!
# `BasinFacts` for the flower setup

For the parabolic germ `f z = z + a z ^ (q+1) + o (z ^ (q+1))` (`q ≥ 1`, `a ≠ 0`, `f 0 = 0`) on a
preconnected open set `D ∋ 0`, this file proves the elementary structural facts about
`MandelDim.ParabolicBasin f D` collected in `Work.Horn.Flower.BasinFacts`:

* `isOpen`, `mapsTo`, `back` — taken from `Work.Horn.basin_basic` (which needs the local openness
  of `f`; this holds because `f` is a non-constant analytic germ, `deriv f 0 = 1`);
* `zero_notMem` — `0` is not in the basin (Cauchy's estimate: if `f^N` mapped a disc around `0`
  into a strictly smaller one then `‖(f^N)'(0)‖ < 1`, but `(f^N)'(0) = 1`);
* `orbit_ne_zero` — forward invariance applied to the previous point;
* `tendsto_zero` — pointwise convergence is a special case of uniform convergence on a
  neighbourhood;
* `mem_of_iterate` — iterated backward invariance.

The only germ-theoretic input is `deriv f 0 = 1`, which is read off from the defining limit.
-/

open MandelDim Filter Topology Metric
open scoped Topology

namespace Work.Horn

noncomputable section

namespace BasinAux

/-- For a germ `f z = z + a z ^ (q+1) + o (z ^ (q+1))` (`q ≥ 1`) with `f 0 = 0`, the derivative at
`0` is `1`: indeed `(f z - f 0)/z = 1 + a z^q + z^q · ((f z - z - a z^(q+1))/z^(q+1)) → 1`. -/
lemma deriv_eq_one {f : ℂ → ℂ} {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (hfix : f 0 = 0)
    (hgerm : Tendsto (fun z : ℂ => (f z - z - a * z ^ (q + 1)) / z ^ (q + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
    deriv f 0 = 1 := by
  have hzq : Tendsto (fun z : ℂ => z ^ q) (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds 0) := by
    have h : Tendsto (fun z : ℂ => z ^ q) (nhds (0 : ℂ)) (nhds 0) := by
      have h' := Continuous.tendsto (continuous_pow q : Continuous fun z : ℂ => z ^ q) (0 : ℂ)
      rwa [zero_pow (by omega : q ≠ 0)] at h'
    exact h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto
      (fun z : ℂ => 1 + a * z ^ q + z ^ q * ((f z - z - a * z ^ (q+1)) / z ^ (q+1)))
      (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds 1) := by
    have h1 : Tendsto (fun z : ℂ => a * z ^ q) (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds (a * 0)) :=
      (tendsto_const_nhds (x := a)).mul hzq
    have h2 : Tendsto (fun z : ℂ => z ^ q * ((f z - z - a * z ^ (q+1)) / z ^ (q+1)))
        (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds (0 * 0)) := hzq.mul hgerm
    have h3 : Tendsto
        (fun z : ℂ => (1 : ℂ) + a * z ^ q + z ^ q * ((f z - z - a * z ^ (q+1)) / z ^ (q+1)))
        (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds ((1 : ℂ) + a * 0 + 0 * 0)) :=
      ((tendsto_const_nhds (x := (1 : ℂ))).add h1).add h2
    simpa using h3
  have heq : slope f 0 =ᶠ[nhdsWithin (0 : ℂ) {0}ᶜ]
      (fun z : ℂ => 1 + a * z ^ q + z ^ q * ((f z - z - a * z ^ (q+1)) / z ^ (q+1))) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    rw [slope_def_field, hfix, sub_zero, sub_zero]
    field_simp
    ring
  have hslope : Tendsto (slope f 0) (nhdsWithin (0 : ℂ) {0}ᶜ) (nhds 1) :=
    hlim.congr' heq.symm
  exact (hasDerivAt_iff_tendsto_slope.mpr hslope).deriv

/-- The iterates of a germ with `f 0 = 0`, `deriv f 0 = 1` have derivative `1` at `0`. -/
lemma deriv_iterate_zero {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (h0 : (0 : ℂ) ∈ D)
    (hf : DifferentiableOn ℂ f D) (hfix : f 0 = 0) (hdf : deriv f 0 = 1) (n : ℕ) :
    deriv (f^[n]) (0 : ℂ) = 1 := by
  have hfdiff : DifferentiableAt ℂ f 0 := hf.differentiableAt (hD.mem_nhds h0)
  have hiter0 : ∀ k : ℕ, f^[k] (0 : ℂ) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, hfix]
  have hiterdiff : ∀ k : ℕ, DifferentiableAt ℂ (f^[k]) (0 : ℂ) := by
    intro k
    induction k with
    | zero => exact differentiableAt_id
    | succ j ih =>
        rw [Function.iterate_succ']
        exact DifferentiableAt.comp (0 : ℂ) (by rw [hiter0 j]; exact hfdiff) ih
  have hrec : ∀ k : ℕ, deriv (f^[k.succ]) (0 : ℂ) = deriv f (f^[k] 0) * deriv (f^[k]) 0 := by
    intro k
    rw [Function.iterate_succ']
    exact deriv_comp (0 : ℂ) (by rw [hiter0 k]; exact hfdiff) (hiterdiff k)
  induction n with
  | zero => simp
  | succ k ih => rw [hrec k, hiter0 k, hdf, ih, one_mul]

/-- `0` is not in the parabolic basin of a germ with `f 0 = 0`, `deriv f 0 = 1`: if a neighbourhood
`U` of `0` had `f^n → 0` uniformly on `U`, then for large `N` the map `f^N` would send a disc
`ball 0 R` into `ball 0 R` with `‖f^N z₀‖ < R` on the sphere `‖z₀‖ = R`; Cauchy's estimate gives
`‖(f^N)'(0)‖ < 1`, while the chain rule gives `(f^N)'(0) = (f'(0))^N = 1`. -/
lemma zero_not_mem {f : ℂ → ℂ} {D : Set ℂ}
    (hD : IsOpen D) (h0 : (0 : ℂ) ∈ D) (hf : DifferentiableOn ℂ f D)
    (hfix : f 0 = 0) (hdf : deriv f 0 = 1) :
    (0 : ℂ) ∉ ParabolicBasin f D := by
  rintro ⟨U, hU, hmap, hunif⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hmapU : ∀ n : ℕ, Set.MapsTo (f^[n]) (ball (0 : ℂ) ε) D :=
    fun n z hz => hmap n (hεU hz)
  have hunifU : TendstoUniformlyOn (fun n : ℕ => f^[n]) (fun _ => (0 : ℂ)) atTop
      (ball (0 : ℂ) ε) := hunif.mono hεU
  have hiter_diff : ∀ n : ℕ, DifferentiableOn ℂ (f^[n]) (ball (0 : ℂ) ε) := by
    intro n
    induction n with
    | zero => simpa using differentiableOn_id
    | succ k ih =>
        rw [Function.iterate_succ']
        exact hf.comp ih (fun z hz => hmapU k hz)
  rw [Metric.tendstoUniformlyOn_iff] at hunifU
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hunifU (ε / 2) (by linarith))
  set R : ℝ := ε / 2 with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  have hball_sub : ball (0 : ℂ) R ⊆ ball (0 : ℂ) ε := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [hR] at hz; linarith
  have hcont : ContinuousOn (f^[N]) (closedBall (0 : ℂ) R) := by
    intro z hz
    have hzε : z ∈ ball (0 : ℂ) ε := by
      rw [mem_closedBall_zero_iff] at hz
      rw [mem_ball_zero_iff]
      rw [hR] at hz; linarith
    exact ((hiter_diff N).differentiableAt (isOpen_ball.mem_nhds hzε)).continuousAt.continuousWithinAt
  have hsphere_ne : (sphere (0 : ℂ) R).Nonempty :=
    ⟨(R : ℂ), by rw [mem_sphere_iff_norm]; simp [Complex.norm_real, abs_of_nonneg hRpos.le]⟩
  obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMaxOn hsphere_ne
    ((hcont.mono sphere_subset_closedBall).norm) (f := fun z => ‖f^[N] z‖)
  have hz₀ε : z₀ ∈ ball (0 : ℂ) ε := by
    have h : ‖z₀‖ = R := by simpa using (mem_sphere_iff_norm.mp hz₀)
    rw [mem_ball_zero_iff, h, hR]; linarith
  have hgN₀ : ‖f^[N] z₀‖ < R := by
    have h := hN N le_rfl z₀ hz₀ε
    rw [dist_eq_norm, zero_sub, norm_neg] at h
    rw [hR]
    exact h
  have hcauchy : ‖deriv (f^[N]) 0‖ ≤ ‖f^[N] z₀‖ / R := by
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos ⟨?_, ?_⟩ (fun z hz => hmax hz)
    · exact (hiter_diff N).mono hball_sub
    · simpa [closure_ball (0 : ℂ) (ne_of_gt hRpos)] using hcont
  rw [deriv_iterate_zero hD h0 hf hfix hdf N, norm_one] at hcauchy
  have : ‖f^[N] z₀‖ / R < 1 := by
    rw [div_lt_one hRpos]
    exact hgN₀
  linarith

/-- Pointwise convergence of the iterates at a basin point follows from the uniform convergence on
a neighbourhood. -/
lemma tendsto_zero {f : ℂ → ℂ} {D : Set ℂ} {z : ℂ} (hz : z ∈ ParabolicBasin f D) :
    Tendsto (fun n : ℕ => f^[n] z) atTop (𝓝 0) := by
  obtain ⟨U, hU, hmap, hunif⟩ := hz
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif ε hε)
  exact ⟨N, fun n hn => by
    simpa [dist_comm] using hN n hn z (mem_of_mem_nhds hU)⟩

/-- Iterated backward invariance of the basin. -/
lemma mem_of_iterate {f : ℂ → ℂ} {D : Set ℂ}
    (hback : ∀ z ∈ D, f z ∈ ParabolicBasin f D → z ∈ ParabolicBasin f D) :
    ∀ (n : ℕ) {z : ℂ}, z ∈ D → (∀ k < n, f^[k] z ∈ D) →
      f^[n] z ∈ ParabolicBasin f D → z ∈ ParabolicBasin f D := by
  intro n
  induction n with
  | zero => intro z hzD hstay hn; simpa using hn
  | succ m ih =>
      intro z hzD hstay hn
      have hmemD : f^[m] z ∈ D := hstay m (Nat.lt_succ_self m)
      rw [Function.iterate_succ_apply'] at hn
      have hb : f^[m] z ∈ ParabolicBasin f D := hback (f^[m] z) hmemD hn
      exact ih hzD (fun k hk => hstay k (Nat.lt_trans hk (Nat.lt_succ_self m))) hb

end BasinAux

theorem basin_facts {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (h : Work.Horn.Flower.Setup f D q a) : Work.Horn.Flower.BasinFacts f D := by
  have hderiv : deriv f 0 = 1 := BasinAux.deriv_eq_one h.hq h.hfix h.hgerm
  have hne : deriv f 0 ≠ 0 := by rw [hderiv]; norm_num
  have hopen := Work.Horn.MandelDim.basin_open_map h.hD h.hconn h.hf h.h0 hne
  obtain ⟨hopenB, hfwd, hback⟩ := Work.Horn.MandelDim.basin_basic h.hD h.hf hopen
  have hzero : (0 : ℂ) ∉ ParabolicBasin f D :=
    BasinAux.zero_not_mem h.hD h.h0 h.hf h.hfix hderiv
  refine ⟨hopenB, hfwd, hback, hzero, ?_, ?_, ?_⟩
  · intro z hz n hz0
    have hiter : ∀ n : ℕ, f^[n] z ∈ ParabolicBasin f D := by
      intro n
      induction n with
      | zero => simpa using hz
      | succ k ih => rw [Function.iterate_succ_apply']; exact hfwd _ ih
    have hmem : f^[n] z ∈ ParabolicBasin f D := hiter n
    rw [hz0] at hmem
    exact hzero hmem
  · intro z hz
    exact BasinAux.tendsto_zero hz
  · intro z hzD n hstay hn
    exact BasinAux.mem_of_iterate hback n hzD hstay hn

end

end Work.Horn
