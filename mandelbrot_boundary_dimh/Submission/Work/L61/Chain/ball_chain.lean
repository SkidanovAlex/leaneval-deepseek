import Mathlib
import Submission.Work.L61.Basic
import Submission.Work.L61.Chain.path_chain
import Submission.Work.L61.Chain.sep_of_compact

/-!
# Lemma 6.1 (Shishikura §6) — the ball chain

`Work.L61.Chain.ball_chain` is the covering/connectivity step used to build the domain `D`
of Lemma 6.1: given a countable compact `K ⊂ ℂ` (in the application `K = Kset d hd`, the
critical orbit of the pushed-down horn map together with `0`) and three points `a, b, c`
outside `K`, there is a finite chain of balls, each disjoint from `K`, joining `a` to `c`
and passing through `b`.

The mathematics is in three steps.

* `K` is compact, hence closed, so `Kᶜ` is open; since `K` is countable and `ℂ` has real
  dimension `2 > 1`, `Kᶜ` is path connected
  (`Set.Countable.isPathConnected_compl_of_one_lt_rank`).
* Concatenating a path from `a` to `b` with one from `b` to `c` gives a path `P` from `a` to
  `c` through `b`; its image is compact and disjoint from `K`, hence at positive distance `δ`
  from `K` (`Work.L61.Chain.sep_of_compact`).
* `Work.L61.Chain.path_chain` then subdivides `[0,1]` into `N+1` points of mesh `1/N` and
  produces the chain of balls of radius `δ/2` about the sample points `P (k/N)`, with
  `P (1/2) = b` landing in the ball at the nearest sample point.
-/

namespace Work.L61.Chain

open Set Metric
open scoped unitInterval

/-- In a real vector space of dimension `> 1`, the complement of a countable set is path
connected; here specialized to `ℂ`. -/
private lemma path_connected_compl_countable {K : Set ℂ} (hKc : K.Countable) :
    IsPathConnected Kᶜ :=
  hKc.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)

/-- The concatenation of two paths takes the value `b` at the midpoint of the unit
interval. -/
private lemma trans_mid {a b c : ℂ} (P₁ : Path a b) (P₂ : Path b c) :
    (P₁.trans P₂) (⟨(1/2 : ℝ), by norm_num⟩ : I) = b := by
  rw [Path.trans_apply]
  rw [dite_eq_left (by norm_num : ((⟨(1/2 : ℝ), by norm_num⟩ : I) : ℝ) ≤ 1/2)]
  rw [show (⟨2 * ((⟨(1/2 : ℝ), by norm_num⟩ : I) : ℝ), by norm_num⟩ : I) = 1 from
    Subtype.ext (by norm_num)]
  exact P₁.target

/-- The concatenation of two paths avoiding `K` avoids `K`. -/
private lemma trans_mem_compl {K : Set ℂ} {a b c : ℂ} (P₁ : Path a b) (P₂ : Path b c)
    (h₁ : ∀ t, P₁ t ∈ Kᶜ) (h₂ : ∀ t, P₂ t ∈ Kᶜ) : ∀ t, (P₁.trans P₂) t ∈ Kᶜ := by
  intro t
  rw [Path.trans_apply]
  split_ifs with h
  · exact h₁ _
  · exact h₂ _

theorem ball_chain {K : Set ℂ} (hKc : K.Countable) (hK : IsCompact K) {a b c : ℂ}
    (ha : a ∉ K) (hb : b ∉ K) (hc : c ∉ K) :
    ∃ (N : ℕ) (cen : Fin (N + 1) → ℂ) (rad : Fin (N + 1) → ℝ) (ib : Fin (N + 1)),
      (∀ i, 0 < rad i) ∧ (∀ i, Disjoint (Metric.ball (cen i) (rad i)) K) ∧
      a ∈ Metric.ball (cen 0) (rad 0) ∧ b ∈ Metric.ball (cen ib) (rad ib) ∧
      c ∈ Metric.ball (cen (Fin.last N)) (rad (Fin.last N)) ∧
      (∀ i : Fin N, (Metric.ball (cen i.castSucc) (rad i.castSucc) ∩
        Metric.ball (cen i.succ) (rad i.succ)).Nonempty) := by
  have hpc : IsPathConnected Kᶜ := path_connected_compl_countable hKc
  obtain ⟨P₁, hP₁⟩ := hpc.joinedIn a ha b hb
  obtain ⟨P₂, hP₂⟩ := hpc.joinedIn b hb c hc
  have hmem : ∀ t : I, (P₁.trans P₂) t ∉ K := trans_mem_compl P₁ P₂ hP₁ hP₂
  have hcont : Continuous (fun t : I => (P₁.trans P₂) t) := (P₁.trans P₂).continuous
  have hsep := sep_of_compact hK (fun t : I => (P₁.trans P₂) t) hcont hmem
  obtain ⟨N, cen, rad, ib, h1, h2, h3, h4, h5, h6⟩ :=
    path_chain (fun t : I => (P₁.trans P₂) t) hcont hsep (⟨(1/2 : ℝ), by norm_num⟩ : I)
  refine ⟨N, cen, rad, ib, h1, h2, ?_, ?_, ?_, h6⟩
  · simpa using h3
  · rw [← trans_mid P₁ P₂]; exact h4
  · simpa using h5

end Work.L61.Chain
