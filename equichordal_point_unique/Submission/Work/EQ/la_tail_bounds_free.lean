import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.descendant_of_unbounded_tails

/-! # The two tail bounds of Rychlik Thm 8(3), from `descendant_of_unbounded_tails`

The statements are those of `Work.EQ.la_tail_bound_value` and `Work.EQ.la_tail_bound_seq`
(`Submission/Work/EQ/la_tail_bound_value.lean`, `.../la_tail_bound_seq.lean`), under fresh names so
that they can be proved here without touching those files.  The proofs are the ones recorded by the
project lead in `Submission/Work/EQ/la_tail_bounds_new.md`: they replace the (blocked) `ltbv_main` +
`href` route by the single new input `Work.EQ.descendant_of_unbounded_tails` — a sequence of chains
with unbounded tails yields a descendant value — which needs no analyticity of labelled `bwdP`
across branch cuts.

`_free` suffixes keep the names unique with respect to the canonical files. -/

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

open scoped Topology

/-- **Tail bound for a fixed value** (statement of `Work.EQ.la_tail_bound_value`): over an annulus
of ratio `> 1/λ` inside a small ball, the tails of the chains of every regular component of a
descendant-free value `c` are uniformly bounded. -/
theorem la_tail_bound_value_free {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r₁ r₂ : ℝ),
      0 < r₁ → r₁ < r₂ → r₂ < δ → 1 / eqLam a < r₂ / r₁ →
      ∀ c : ℂ, ∀ (S : ℕ → Set ChainData),
        (∀ n, IsRegComp a h (S n) c) →
        (∀ μ₁ ∈ CharSet a h, ∀ μ₂ ∈ CharSet a h,
          (μ₁ ≠ 1 ∨ μ₂ ≠ 1) → ∀ T : Set ChainData,
            ¬ IsRegComp a h T (c * μ₁ * μ₂)) →
        ∃ M : ℕ, ∀ n, ∀ q ∈ S n, q.2.1 ∈ Ann r₁ r₂ →
          (∀ k : ℕ, M ≤ k → q.1 (k : ℤ) =
            germC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.1)) ∧
          (∀ k : ℕ, M ≤ k → q.1 (-(k : ℤ)) =
            ugermC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.2)) := by
  obtain ⟨δ, hδ, hD⟩ := descendant_of_unbounded_tails ha0 ha1 hh
  refine ⟨δ, hδ, fun r₁ r₂ hr₁ hr₁₂ hr₂ hratio c S hS hnd => ?_⟩
  by_contra hcon
  have hbad : ∀ M : ℕ, ∃ n, ∃ q ∈ S n, q.2.1 ∈ Ann r₁ r₂ ∧
      ¬ ((∀ k : ℕ, M ≤ k → q.1 (k : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.1)) ∧
        (∀ k : ℕ, M ≤ k → q.1 (-(k : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.2))) := by
    intro M
    by_contra hno
    exact hcon ⟨M, fun n q hq hqa => by
      by_contra hx
      exact hno ⟨n, q, hq, hqa, hx⟩⟩
  choose n q hq hqann hbad' using hbad
  obtain ⟨μ₁, hμ₁, μ₂, hμ₂, hne, T, hT⟩ := hD r₁ r₂ hr₁ hr₁₂ hr₂ hratio
    (fun M => S (n M)) (fun _ => c) c q (fun M => hS (n M)) tendsto_const_nhds
    (fun M => ⟨hq M, hqann M⟩) (fun M => ⟨M, hbad' M⟩)
  exact hnd μ₁ hμ₁ μ₂ hμ₂ hne T hT

/-- **Sequential tail bound** (statement of `Work.EQ.la_tail_bound_seq`): the same conclusion for a
sequence of regular components whose values converge to a descendant-free `c₀`, along a
subsequence. -/
theorem la_tail_bound_seq_free {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r₁ r₂ : ℝ),
      0 < r₁ → r₁ < r₂ → r₂ < δ → 1 / eqLam a < r₂ / r₁ →
      ∀ (c₀ : ℂ),
        (∀ μ₁ ∈ CharSet a h, ∀ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) →
          ∀ T : Set ChainData, ¬ IsRegComp a h T (c₀ * μ₁ * μ₂)) →
      ∀ (S : ℕ → Set ChainData) (c : ℕ → ℂ),
        (∀ n, IsRegComp a h (S n) (c n)) →
        (∀ n, ‖c n‖ ≤ 2 * rhoStar a h) →
        Filter.Tendsto c Filter.atTop (nhds c₀) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ M : ℕ, ∀ k : ℕ, ∀ q ∈ S (φ k), q.2.1 ∈ Ann r₁ r₂ →
          (∀ m : ℕ, M ≤ m → q.1 (m : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ m * q.2.1)) ∧
          (∀ m : ℕ, M ≤ m → q.1 (-(m : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * q.2.2)) := by
  obtain ⟨δ, hδ, hD⟩ := descendant_of_unbounded_tails ha0 ha1 hh
  refine ⟨δ, hδ, fun r₁ r₂ hr₁ hr₁₂ hr₂ hratio c₀ hnd S c hS _ hlim => ?_⟩
  by_contra hcon
  -- for every depth `M` and every `K`, some index `n ≥ K` carries a bad chain
  have hbadAll : ∀ M K : ℕ, ∃ n, K ≤ n ∧ ∃ q ∈ S n, q.2.1 ∈ Ann r₁ r₂ ∧
      ¬ ((∀ m : ℕ, M ≤ m → q.1 (m : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ m * q.2.1)) ∧
        (∀ m : ℕ, M ≤ m → q.1 (-(m : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * q.2.2))) := by
    intro M K
    by_contra hno
    push_neg at hno
    exact hcon ⟨fun k => K + k, fun i j hij => by simpa using hij, M,
      fun k q hq hqa => hno (K + k) (by omega) q hq hqa⟩
  choose n hn q hq hqann hbad using fun M => hbadAll M M
  have hn_tend : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  obtain ⟨μ₁, hμ₁, μ₂, hμ₂, hne, T, hT⟩ := hD r₁ r₂ hr₁ hr₁₂ hr₂ hratio
    (fun M => S (n M)) (fun M => c (n M)) c₀ q (fun M => hS (n M)) (hlim.comp hn_tend)
    (fun M => ⟨hq M, hqann M⟩) (fun M => ⟨M, hbad M⟩)
  exact hnd μ₁ hμ₁ μ₂ hμ₂ hne T hT

end

end Work.EQ
