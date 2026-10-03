import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.flower_defs
import Submission.Work.Horn.log_pow_eq
import Submission.Work.Horn.bounds_exists
import Submission.Work.Horn.petal_facts
import Submission.Work.Horn.basin_facts
import Submission.Work.Horn.injOn_ball
import Submission.Work.Horn.exists_iterate_mem_bigPetal
import Submission.Work.Horn.petal_mapsTo
import Submission.Work.Horn.petal_subset_basin
import Submission.Work.Horn.petal_index_locally_const

/-!
# `Work.Horn.flower_q` — the Leau–Fatou flower of a parabolic germ of order `q+1`

For a germ `f z = z + a z^(q+1) + o(z^(q+1))` (`1 ≤ q`, `a ≠ 0`) on an open preconnected `D ∋ 0`
we construct `q` open connected petals `V j = Flower.petal q a M j` (the `j`-th branch of the
`q`-th root of the root disc `DM M` in the chart `w = cc q a / z^q`, `cc = -1/(q a)`), where
`M > ‖cc‖/ρ^q` is taken large enough that the petals lie in the disc on which the quantitative
germ bounds `Flower.Bounds` hold.  The rest is bookkeeping: the petals are the connected pieces of
`bigPetal M = {Re (cc/z^q) > M}`, they are invariant, `f` is injective on each of them (the
derivative bound `‖f' - 1‖ ≤ 1/2` on a convex ball), the chart coordinate is a translation up to
`1/4` (so orbits of petals converge to `0` uniformly and every basin orbit enters `bigPetal`), and
the entered petal index is locally constant on the basin.
-/

namespace Work.Horn

open Filter Topology
open scoped Topology
open Work.Horn.Flower

theorem flower_q {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (hD : IsOpen D) (hconn : IsPreconnected D) (h0 : (0 : ℂ) ∈ D)
    (hf : DifferentiableOn ℂ f D) (hq : 1 ≤ q) (ha : a ≠ 0) (hfix : f 0 = 0)
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
  have hS : Flower.Setup f D q a := ⟨hD, hconn, h0, hf, hq, ha, hfix, hgerm⟩
  obtain ⟨ρ, hρ, hb⟩ := bounds_exists hS
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
  have hbasin : Flower.BasinFacts f D := basin_facts hS
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
