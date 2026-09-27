import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.Junc.invBranch_cluster_subseq

/-!
# The limit segment of a convergent family of chains

`Work.EQ.junction_limit_segment`: if a family `q k` of chain data has index-`0` points converging
to `S` and index-`(-N)` points converging to `T`, and every step of the `N`-step backward segment
of `q k` is a regular pair (`Work.EQ.RegPair`, i.e. the equichordal relation holds and both local
branches are nondegenerate), while at the limit point `S` no `≤ N`-step backward image lands on an
isotropic line through `O₁` (`hgood`), then `T` is the `N`-step backward image of `S` along some
sign list.

The proof reads the branch letters *at the limit*: the letter of one step is a discrete datum, so
along a subsequence it is constant; the limit of the backward step is then one of the two backward
branches of the limit point (`Work.EQ.Junc.invBranch_cluster_subseq` — the letter may flip when the
subsequence crosses the branch cut of the complex square root), and `hgood` at the intermediate
words keeps the limit segment finite and off the degenerate locus.  Iterating over the `N` levels
and passing to a nested subsequence identifies `T` with the labelled backward image of `S`.
-/

namespace Work.EQ

theorem junction_limit_segment {a : ℝ} {N : ℕ} {q : ℕ → Work.EQ.ChainData} {S T : ℂ × ℂ}
    (hstep : ∀ k, ∀ i ≤ N, Work.EQ.RegPair a ((q k).1 (-((i : ℤ) + 1))) ((q k).1 (-(i : ℤ))))
    (hgood : ∀ σ : List Bool, σ.length ≤ N →
      Work.EQ.bsq (Work.EQ.subO1 a (Work.EQ.bwdP a σ S)) ≠ 0)
    (h0 : Filter.Tendsto (fun k => (q k).1 0) Filter.atTop (nhds S))
    (hN : Filter.Tendsto (fun k => (q k).1 (-(N : ℤ))) Filter.atTop (nhds T)) :
    ∃ s : List Bool, s.length ≤ N ∧ T = Work.EQ.bwdP a s S := by
  -- For every level `i ≤ N` the `i`-th points of the chains admit a subsequence converging to the
  -- `i`-step backward image of `S` along a fixed sign list.
  have key : ∀ i, i ≤ N → ∃ (σ : List Bool) (φ : ℕ → ℕ), StrictMono φ ∧ σ.length = i ∧
      Filter.Tendsto (fun k => (q (φ k)).1 (-(i : ℤ))) Filter.atTop (nhds (Work.EQ.bwdP a σ S)) := by
    intro i
    induction i with
    | zero =>
        intro _
        exact ⟨[], (id : ℕ → ℕ), strictMono_id, rfl, by simpa using h0⟩
    | succ i ih =>
        intro hi
        have hi' : i ≤ N := by omega
        obtain ⟨σ, φ, hφm, hσlen, hφT⟩ := ih hi'
        have hSne : Work.EQ.bsq (Work.EQ.subO1 a (Work.EQ.bwdP a σ S)) ≠ 0 :=
          hgood σ (by omega)
        -- the branch letter of the `(i+1)`-st backward step of each chain, at index `φ k`
        have hbr : ∀ k, ∃ t : Bool, (q (φ k)).1 (-((i : ℤ) + 1)) =
            Work.EQ.invBranch a t ((q (φ k)).1 (-(i : ℤ))) := by
          intro k
          obtain ⟨hrel, -, hnd⟩ := hstep (φ k) i hi'
          have hnd' : Work.EQ.bsq (Work.EQ.subO1 a ((q (φ k)).1 (-(i : ℤ)))) ≠ 0 := by
            simpa [Work.EQ.bsq, Work.EQ.subO1] using hnd
          rcases Work.EQ.eqRelC_solutions hrel hnd' with h | h
          · exact ⟨true, h⟩
          · exact ⟨false, h⟩
        choose t ht using hbr
        -- the letter is constant on a subsequence, and the step limit is a branch at the limit
        obtain ⟨t', ψ, hψm, hψT⟩ := Work.EQ.Junc.invBranch_cluster_subseq
          (a := a) (S := Work.EQ.bwdP a σ S) (P := fun k => (q (φ k)).1 (-(i : ℤ)))
          (t := t) hSne hφT
        refine ⟨σ ++ [t'], φ ∘ ψ, hφm.comp hψm, ?_, ?_⟩
        · simp [hσlen]
        · rw [Work.EQ.bwdP_snoc]
          refine hψT.congr' (Filter.Eventually.of_forall (fun k => ?_))
          show Work.EQ.invBranch a (t (ψ k)) ((q (φ (ψ k))).1 (-(i : ℤ)))
              = (q ((φ ∘ ψ) k)).1 (-(((i + 1 : ℕ) : ℤ)))
          rw [show (((i + 1 : ℕ)) : ℤ) = (i : ℤ) + 1 by push_cast; ring]
          exact (ht (ψ k)).symm
  obtain ⟨σ, φ, hφm, hσlen, hφT⟩ := key N le_rfl
  exact ⟨σ, le_of_eq hσlen,
    tendsto_nhds_unique (hN.comp hφm.tendsto_atTop) hφT⟩

end Work.EQ
