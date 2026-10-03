import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.flower_q

/-!
# `Work.Horn.flower_q_component` — the Leau–Fatou flower without preconnectedness

`Work.Horn.flower_q` proves the flower theorem for a parabolic germ
`f z = z + a z^(q+1) + o(z^(q+1))` on an open **preconnected** `D ∋ 0`, which is exactly what the
parabolic layer of the Mandelbrot development needs.  The interface only supplies `IsOpen D`
(`MandelDim.IsParabolicGerm`), and one cannot simply shrink `D` to a component, because
`MandelDim.ParabolicBasin f D` depends on `D`.

This file removes `IsPreconnected D` and replaces it by the *local openness* hypothesis

  `hopen : ∀ z ∈ D, ∀ U ∈ nhds z, f '' U ∈ nhds (f z)`,

i.e. `f` is an open map at every point of `D` (for holomorphic `f` this is equivalent to `f` being
nowhere locally constant on `D`).  This is not a cosmetic change: without it the statement is
**false** (see `Submission/Work/Parab/basinEnters/counterexample.lean`: on
`D = ball 0 1 ∪ ball 5 1` with `f = (z ↦ z + z²)` on the unit disc and `f ≡ 0` on `ball 5 1`, the
point `5` lies in the parabolic basin but its orbit dies on `0` and never enters a petal).  With
`hopen`, the two places of `flower_q`'s proof that used connectedness are repaired:

* the quantitative local data `Flower.Bounds f D q a ρ` is extracted from `bounds_exists` applied
  to a *ball* around `0` inside `D` (the `Bounds` structure differs only in the field
  `ball 0 ρ ⊆ D`, so it transports along `ball 0 ε ⊆ D`);
* the basin bookkeeping `Flower.BasinFacts f D` is rebuilt from `Work.Horn.MandelDim.basin_basic`,
  whose hypothesis is literally `hopen` (this is the local form of the open mapping theorem used
  by the original proof).

Everything else (the petals `Flower.petal q a M j`, their invariance, injectivity, the capture of
the basin and the local constancy of the entered petal index) is independent of connectedness and
is reused verbatim from the `flower_q` development.
-/

namespace Work.Horn

open Filter Topology
open scoped Topology
open Work.Horn.Flower

set_option linter.unusedVariables false

/-- Quantitative local data of a parabolic germ on an open `D ∋ 0`, with no connectedness assumed:
`bounds_exists` needs only the germ, so it is applied to a ball `ball 0 ε ⊆ D` and the resulting
`Flower.Bounds f (ball 0 ε) q a ρ` is transported to `D` (the only `D`-dependent field of `Bounds`
is `hsub : ball 0 ρ ⊆ D`). -/
theorem bounds_exists_of_open {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (hD : IsOpen D) (h0 : (0 : ℂ) ∈ D)
    (hf : DifferentiableOn ℂ f D) (hq : 1 ≤ q) (ha : a ≠ 0) (hfix : f 0 = 0)
    (hgerm : Filter.Tendsto (fun z : ℂ => (f z - z - a * z ^ (q + 1)) / z ^ (q + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
    ∃ ρ : ℝ, 0 < ρ ∧ Flower.Bounds f D q a ρ := by
  obtain ⟨ε, hε, hεD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds h0)
  have hS : Flower.Setup f (Metric.ball (0 : ℂ) ε) q a :=
    ⟨Metric.isOpen_ball, (convex_ball (0 : ℂ) ε).isPreconnected, by simpa using hε,
      hf.mono hεD, hq, ha, hfix, hgerm⟩
  obtain ⟨ρ, hρ, hb⟩ := bounds_exists hS
  exact ⟨ρ, hρ, { hρ := hb.hρ
                  hsub := fun z hz => hεD (hb.hsub hz)
                  hq := hb.hq
                  ha := hb.ha
                  hfix := hb.hfix
                  hf_eq := hb.hf_eq
                  hderiv := hb.hderiv
                  hchart := hb.hchart
                  hunit_ne := hb.hunit_ne
                  hunit_re := hb.hunit_re
                  hunit_arg := hb.hunit_arg }⟩

/-- The elementary structural facts about the parabolic basin (`Flower.BasinFacts`) for an open
`D ∋ 0` on which `f` is holomorphic and open at every point — no connectedness of `D`.  This is
`basin_facts` with `MandelDim.basin_open_map` replaced by the hypothesis `hopen`. -/
theorem basin_facts_of_open {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (hD : IsOpen D) (h0 : (0 : ℂ) ∈ D) (hf : DifferentiableOn ℂ f D)
    (hopen : ∀ z ∈ D, ∀ U ∈ nhds z, f '' U ∈ nhds (f z))
    (hq : 1 ≤ q) (hfix : f 0 = 0)
    (hgerm : Filter.Tendsto (fun z : ℂ => (f z - z - a * z ^ (q + 1)) / z ^ (q + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
    Flower.BasinFacts f D := by
  have hderiv : deriv f 0 = 1 := BasinAux.deriv_eq_one hq hfix hgerm
  obtain ⟨hopenB, hfwd, hback⟩ := Work.Horn.MandelDim.basin_basic hD hf hopen
  have hzero : (0 : ℂ) ∉ MandelDim.ParabolicBasin f D :=
    BasinAux.zero_not_mem hD h0 hf hfix hderiv
  refine ⟨hopenB, hfwd, hback, hzero, ?_, ?_, ?_⟩
  · intro z hz n hz0
    have hiter : ∀ n : ℕ, f^[n] z ∈ MandelDim.ParabolicBasin f D := by
      intro n
      induction n with
      | zero => simpa using hz
      | succ k ih => rw [Function.iterate_succ_apply']; exact hfwd _ ih
    have hmem : f^[n] z ∈ MandelDim.ParabolicBasin f D := hiter n
    rw [hz0] at hmem
    exact hzero hmem
  · intro z hz
    exact BasinAux.tendsto_zero hz
  · intro z hzD n hstay hn
    exact BasinAux.mem_of_iterate hback n hzD hstay hn

theorem flower_q_component {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (hD : IsOpen D) (h0 : (0 : ℂ) ∈ D)
    (hf : DifferentiableOn ℂ f D) (hq : 1 ≤ q) (ha : a ≠ 0) (hfix : f 0 = 0)
    (hopen : ∀ z ∈ D, ∀ U ∈ nhds z, f '' U ∈ nhds (f z))
    (hgerm : Filter.Tendsto (fun z : ℂ => (f z - z - a * z ^ (q + 1)) / z ^ (q + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
    ∃ V : Fin q → Set ℂ,
      (∀ i, IsOpen (V i) ∧ IsConnected (V i) ∧ V i ⊆ D) ∧
      (∀ i, ∀ z ∈ V i, f z ∈ V i ∪ {0}) ∧
      (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
      (∀ i, (0 : ℂ) ∈ closure (V i)) ∧
      (∀ i, Set.InjOn f (V i)) ∧
      (∀ z ∈ MandelDim.ParabolicBasin f D, ∃ n : ℕ, f^[n] z ∈ ⋃ i, V i) ∧
      (∀ z ∈ D, (∃ n : ℕ, (∀ k < n, f^[k] z ∈ D) ∧ f^[n] z ∈ ⋃ i, V i) →
        z ∈ MandelDim.ParabolicBasin f D) ∧
      (∀ z ∈ MandelDim.ParabolicBasin f D, ∃ U ∈ nhds z, ∀ w ∈ U, ∀ i : Fin q,
        ((∃ n : ℕ, f^[n] z ∈ V i) ↔ (∃ n : ℕ, f^[n] w ∈ V i))) := by
  obtain ⟨ρ, hρ, hb⟩ := bounds_exists_of_open hD h0 hf hq ha hfix hgerm
  have hcc : Flower.cc q a ≠ 0 := by
    rw [Flower.cc]
    exact div_ne_zero (by norm_num) (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) ha)
  have hccpos : 0 < ‖Flower.cc q a‖ := norm_pos_iff.mpr hcc
  have hρq : 0 < ρ ^ q := pow_pos hρ q
  set M : ℝ := ‖Flower.cc q a‖ / ρ ^ q + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hRM : ‖Flower.cc q a‖ / M < ρ ^ q := by
    have h1 : ‖Flower.cc q a‖ / ρ ^ q < M := by rw [hMdef]; linarith
    have h2 : ‖Flower.cc q a‖ / M < ‖Flower.cc q a‖ / (‖Flower.cc q a‖ / ρ ^ q) :=
      div_lt_div_of_pos_left hccpos (div_pos hccpos hρq) h1
    have h3 : ‖Flower.cc q a‖ / (‖Flower.cc q a‖ / ρ ^ q) = ρ ^ q := by field_simp
    rwa [h3] at h2
  have hgeo : Flower.PetalFacts q a M := petal_facts hq ha hMpos
  have hlogpow : ∀ u : ℂ, u ≠ 0 → |u.arg| * (q : ℝ) < Real.pi →
      Complex.log (u ^ q) = (q : ℂ) * Complex.log u :=
    fun u hu hu' => log_pow_eq hq hu hu'
  have hmaps : ∀ j : Fin q, Set.MapsTo f (Flower.petal q a M j) (Flower.petal q a M j ∪ {0}) :=
    petal_mapsTo hb hMpos hRM hgeo hlogpow
  have hbasin : Flower.BasinFacts f D :=
    basin_facts_of_open hD h0 hf hopen hq hfix hgerm
  have hball : ∀ j : Fin q, Flower.petal q a M j ⊆ Metric.ball (0 : ℂ) ρ := by
    intro j z hz
    have h1 : ‖z‖ ^ q < ‖Flower.cc q a‖ / M := hgeo.petal_norm_pow_lt j z hz
    have h2 : ‖z‖ ^ q < ρ ^ q := lt_trans h1 hRM
    have h3 : ‖z‖ < ρ := by
      by_contra hcon
      push Not at hcon
      exact absurd h2 (not_lt.mpr (pow_le_pow_left₀ hρ.le hcon q))
    simpa [Metric.mem_ball, dist_zero_right] using h3
  have hinj : ∀ j : Fin q, Set.InjOn f (Flower.petal q a M j) :=
    fun j => (injOn_ball hb).mono (hball j)
  have hcap : ∀ z ∈ MandelDim.ParabolicBasin f D,
      ∃ n : ℕ, f^[n] z ∈ ⋃ j, Flower.petal q a M j := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_iterate_mem_bigPetal hb hMpos (hbasin.orbit_ne_zero z hz)
      (hbasin.tendsto_zero z hz)
    refine ⟨n, ?_⟩
    rw [hgeo.iUnion_petal_eq_bigPetal]
    exact hn
  have hsub : ∀ j : Fin q, Flower.petal q a M j ⊆ MandelDim.ParabolicBasin f D :=
    petal_subset_basin hb hMpos hRM hgeo hmaps
  have hloc := petal_index_locally_const hD hf hb hMpos hgeo hmaps hcap
  refine ⟨fun i => Flower.petal q a M i, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hgeo.isOpen_petal i, hgeo.isConnected_petal i, fun z hz => hb.hsub (hball i hz)⟩
  · intro i z hz
    exact hmaps i hz
  · intro i j hij
    exact hgeo.disjoint_petal i j hij
  · intro i
    exact hgeo.zero_mem_closure_petal i
  · intro i
    exact hinj i
  · intro z hz
    exact hcap z hz
  · intro z hzD hn
    obtain ⟨n, hstay, hmem⟩ := hn
    have hmem' : f^[n] z ∈ MandelDim.ParabolicBasin f D := by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
      exact hsub i hi
    exact hbasin.mem_of_iterate z hzD n hstay hmem'
  · intro z hz
    exact hloc z hz

end Work.Horn
