import Mathlib
import Submission.Work.Horn.flower_q_component

/-!
# `Work.Horn.flower_q_component_nz` — the flower on an open set, with `0` in no petal

This is `Work.Horn.flower_q_component` (the Leau–Fatou flower for a parabolic germ
`f z = z + a z^(q+1) + o(z^(q+1))` on an open `D ∋ 0`, **without** preconnectedness of `D`,
replacing the latter by the local openness hypothesis
`hopen : ∀ z ∈ D, ∀ U ∈ nhds z, f '' U ∈ nhds (f z)`), with the additional conjunct
`∀ i, (0 : ℂ) ∉ V i` — the same strengthening that `Work.Horn.flower_q_nz` adds on the
preconnected route.

The point of the extra conjunct: with `0 ∉ V i` and `f (V i) ⊆ V i ∪ {0}`, the petals are
honestly forward invariant for `f` (`f (V i) ⊆ V i`), which is what the `q = 1` argument of
Lemma 5.4 needs.

As in `flower_q_nz` we re-run the (short) assembly rather than invoking the existential form of
`flower_q_component`, because from the bare existential one cannot recover the nonzero-ness.  The
construction is unchanged: the petals are `Flower.petal q a M j`, and they avoid `0` because
`Flower.rootFun` is a product of two exponentials (`Flower.PetalFacts.not_mem_petal_zero`).
The two places where `flower_q_component` replaced connectedness —
`bounds_exists_of_open` and `basin_facts_of_open` — are reused verbatim.
-/

namespace Work.Horn

open Filter Topology
open scoped Topology
open Work.Horn.Flower

set_option linter.unusedVariables false

theorem flower_q_component_nz {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ}
    (hD : IsOpen D) (h0 : (0 : ℂ) ∈ D)
    (hf : DifferentiableOn ℂ f D) (hq : 1 ≤ q) (ha : a ≠ 0) (hfix : f 0 = 0)
    (hopen : ∀ z ∈ D, ∀ U ∈ nhds z, f '' U ∈ nhds (f z))
    (hgerm : Filter.Tendsto (fun z : ℂ => (f z - z - a * z ^ (q + 1)) / z ^ (q + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
    ∃ V : Fin q → Set ℂ,
      (∀ i, IsOpen (V i) ∧ IsConnected (V i) ∧ V i ⊆ D) ∧
      (∀ i, (0 : ℂ) ∉ V i) ∧
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
  refine ⟨fun i => Flower.petal q a M i, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hgeo.isOpen_petal i, hgeo.isConnected_petal i, fun z hz => hb.hsub (hball i hz)⟩
  · intro i
    exact hgeo.not_mem_petal_zero i
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
