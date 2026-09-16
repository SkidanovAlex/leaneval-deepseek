import Submission.ZagierHoffmanProof.StepL7

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L9: the ζ-level B* operator (paper Cor 2.7 summed over levels)

For a mixed binary relation `R` (a-terms at level `d`, b-terms at level `d+1`, every
`b`-tuple of depth ≥ 2) and `v` with `v + (t_j)₁ ≤ q` for all `b`-tuples, the paper's
`B*_v` (Cor 2.7) prepends `v` to every `a`-tuple and splits each `b`-term into the
level-`d` terms `S_d(v, t_j)` and the merged first-slot term `S_d(v + (t_j)₁, t_j⁻)`.
`bstar_pure` (StepL4) is this identity at every level `d`; `bstar_zeta` is its sum
over all levels — the ζ-level relation used in Prop 2.12's step `B*_{s_j}`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ ζ-level Cor 2.7 (B*_v on a mixed relation, pure form): for `v` with
`v + (t_j)₁ ≤ q` for every `b`-tuple, prepending `v` to the `a`-tuples and splitting
each `b`-term `S_{d+1}(t_j)` into the level-`d` terms `S_d(v, t_j)` and the merged
`S_d(v + (t_j)₁, t_j⁻)` gives a ζ-level identity (the sum over `d` of Cor 2.7). -/
theorem bstar_zeta (R : BinaryRel F) (v : ℕ+)
    (hv : ∀ j : R.ιB, (v : ℕ) + ((R.cB j) ⟨0, R.hdepB j⟩ : ℕ) ≤ Nat.card F) :
    (∑ i : R.ιA, (((R.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (consVec v (R.cA i)))) +
    (∑ j : R.ιB, (((R.aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (consVec v (R.cB j)))) +
    (∑ j : R.ιB, (((R.aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (headAdd v (R.hdepB j) (R.cB j)))) = 0 := by
  classical
  let K := RatFunc.CompletionAtInfty F
  have hlevel : ∀ d : ℕ,
      (∑ i : R.ιA, ((R.aA i : RatFunc F) : K) *
          S F (R.depA i + 1) (by omega : 0 < R.depA i + 1) (consVec v (R.cA i)) d) +
      (∑ j : R.ιB, ((R.aB j : RatFunc F) : K) *
          S F (R.depB j + 1) (by omega : 0 < R.depB j + 1) (consVec v (R.cB j)) d) +
      (∑ j : R.ιB, ((R.aB j : RatFunc F) : K) *
          S F (R.depB j) (R.hdepB j) (headAdd v (R.hdepB j) (R.cB j)) d) = 0 := by
    intro d
    simpa using (bstar_pure F (depA := R.depA) (hdepA := R.hdepA) (cA := R.cA) (aA := R.aA)
      (depB := R.depB) (hdepB := R.hdepB) (hB2 := R.hB2) (cB := R.cB) (aB := R.aB)
      v R.valid hv d)
  let g1 : ℕ → K := fun d => ∑ i : R.ιA, ((R.aA i : RatFunc F) : K) *
      S F (R.depA i + 1) (by omega : 0 < R.depA i + 1) (consVec v (R.cA i)) d
  let g2 : ℕ → K := fun d => ∑ j : R.ιB, ((R.aB j : RatFunc F) : K) *
      S F (R.depB j + 1) (by omega : 0 < R.depB j + 1) (consVec v (R.cB j)) d
  let g3 : ℕ → K := fun d => ∑ j : R.ιB, ((R.aB j : RatFunc F) : K) *
      S F (R.depB j) (R.hdepB j) (headAdd v (R.hdepB j) (R.cB j)) d
  have hsum1 : (∑ i : R.ιA, ((R.aA i : RatFunc F) : K) * ζ_A F (consVec v (R.cA i))) =
      ∑' d : ℕ, g1 d := by
    calc
      (∑ i : R.ιA, ((R.aA i : RatFunc F) : K) * ζ_A F (consVec v (R.cA i)))
          = ∑ i : R.ιA, ∑' d : ℕ, ((R.aA i : RatFunc F) : K) *
              S F (R.depA i + 1) (by omega : 0 < R.depA i + 1) (consVec v (R.cA i)) d := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [zeta_eq_tsum_block F (by omega : 0 < R.depA i + 1) (consVec v (R.cA i))]
            rw [← tsum_mul_left]
      _ = ∑' d : ℕ, g1 d := by
            dsimp [g1]
            exact Commons.Topology.InfiniteSum.fin_sum_tsum
              (fun i d => ((R.aA i : RatFunc F) : K) *
                S F (R.depA i + 1) (by omega : 0 < R.depA i + 1) (consVec v (R.cA i)) d)
              (by
                intro i
                exact (summable_S F (by omega : 0 < R.depA i + 1) (consVec v (R.cA i))).mul_left
                  ((R.aA i : RatFunc F) : K))
  have hsum2 : (∑ j : R.ιB, ((R.aB j : RatFunc F) : K) * ζ_A F (consVec v (R.cB j))) =
      ∑' d : ℕ, g2 d := by
    calc
      (∑ j : R.ιB, ((R.aB j : RatFunc F) : K) * ζ_A F (consVec v (R.cB j)))
          = ∑ j : R.ιB, ∑' d : ℕ, ((R.aB j : RatFunc F) : K) *
              S F (R.depB j + 1) (by omega : 0 < R.depB j + 1) (consVec v (R.cB j)) d := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [zeta_eq_tsum_block F (by omega : 0 < R.depB j + 1) (consVec v (R.cB j))]
            rw [← tsum_mul_left]
      _ = ∑' d : ℕ, g2 d := by
            dsimp [g2]
            exact Commons.Topology.InfiniteSum.fin_sum_tsum
              (fun j d => ((R.aB j : RatFunc F) : K) *
                S F (R.depB j + 1) (by omega : 0 < R.depB j + 1) (consVec v (R.cB j)) d)
              (by
                intro j
                exact (summable_S F (by omega : 0 < R.depB j + 1) (consVec v (R.cB j))).mul_left
                  ((R.aB j : RatFunc F) : K))
  have hsum3 : (∑ j : R.ιB, ((R.aB j : RatFunc F) : K) * ζ_A F (headAdd v (R.hdepB j) (R.cB j))) =
      ∑' d : ℕ, g3 d := by
    calc
      (∑ j : R.ιB, ((R.aB j : RatFunc F) : K) * ζ_A F (headAdd v (R.hdepB j) (R.cB j)))
          = ∑ j : R.ιB, ∑' d : ℕ, ((R.aB j : RatFunc F) : K) *
              S F (R.depB j) (R.hdepB j) (headAdd v (R.hdepB j) (R.cB j)) d := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [zeta_eq_tsum_block F (R.hdepB j) (headAdd v (R.hdepB j) (R.cB j))]
            rw [← tsum_mul_left]
      _ = ∑' d : ℕ, g3 d := by
            dsimp [g3]
            exact Commons.Topology.InfiniteSum.fin_sum_tsum
              (fun j d => ((R.aB j : RatFunc F) : K) *
                S F (R.depB j) (R.hdepB j) (headAdd v (R.hdepB j) (R.cB j)) d)
              (by
                intro j
                exact (summable_S F (R.hdepB j) (headAdd v (R.hdepB j) (R.cB j))).mul_left
                  ((R.aB j : RatFunc F) : K))
  have hper1 : ∀ i : R.ιA, Summable (fun d : ℕ => ((R.aA i : RatFunc F) : K) *
      S F (R.depA i + 1) (by omega : 0 < R.depA i + 1) (consVec v (R.cA i)) d) := by
    intro i
    exact (summable_S F (by omega : 0 < R.depA i + 1) (consVec v (R.cA i))).mul_left
      ((R.aA i : RatFunc F) : K)
  have hg1s : Summable g1 := by
    dsimp [g1]
    exact Commons.Topology.InfiniteSum.summable_fin_sum
      (fun i d => ((R.aA i : RatFunc F) : K) *
        S F (R.depA i + 1) (by omega : 0 < R.depA i + 1) (consVec v (R.cA i)) d) hper1
  have hper2 : ∀ j : R.ιB, Summable (fun d : ℕ => ((R.aB j : RatFunc F) : K) *
      S F (R.depB j + 1) (by omega : 0 < R.depB j + 1) (consVec v (R.cB j)) d) := by
    intro j
    exact (summable_S F (by omega : 0 < R.depB j + 1) (consVec v (R.cB j))).mul_left
      ((R.aB j : RatFunc F) : K)
  have hg2s : Summable g2 := by
    dsimp [g2]
    exact Commons.Topology.InfiniteSum.summable_fin_sum
      (fun j d => ((R.aB j : RatFunc F) : K) *
        S F (R.depB j + 1) (by omega : 0 < R.depB j + 1) (consVec v (R.cB j)) d) hper2
  have hper3 : ∀ j : R.ιB, Summable (fun d : ℕ => ((R.aB j : RatFunc F) : K) *
      S F (R.depB j) (R.hdepB j) (headAdd v (R.hdepB j) (R.cB j)) d) := by
    intro j
    exact (summable_S F (R.hdepB j) (headAdd v (R.hdepB j) (R.cB j))).mul_left
      ((R.aB j : RatFunc F) : K)
  have hg3s : Summable g3 := by
    dsimp [g3]
    exact Commons.Topology.InfiniteSum.summable_fin_sum
      (fun j d => ((R.aB j : RatFunc F) : K) *
        S F (R.depB j) (R.hdepB j) (headAdd v (R.hdepB j) (R.cB j)) d) hper3
  calc
    (∑ i : R.ιA, ((R.aA i : RatFunc F) : K) * ζ_A F (consVec v (R.cA i))) +
        (∑ j : R.ιB, ((R.aB j : RatFunc F) : K) * ζ_A F (consVec v (R.cB j))) +
        (∑ j : R.ιB, ((R.aB j : RatFunc F) : K) * ζ_A F (headAdd v (R.hdepB j) (R.cB j)))
        = (∑' d : ℕ, g1 d) + (∑' d : ℕ, g2 d) + (∑' d : ℕ, g3 d) := by
          rw [hsum1, hsum2, hsum3]
    _ = ∑' d : ℕ, (g1 d + g2 d + g3 d) := by
          rw [add_assoc]
          rw [← Summable.tsum_add hg2s hg3s]
          rw [← Summable.tsum_add hg1s (Summable.add hg2s hg3s)]
          apply congrArg tsum
          funext d
          rw [add_assoc]
    _ = 0 := by
          have hz : (fun d : ℕ => g1 d + g2 d + g3 d) = fun _ : ℕ => 0 := by
            funext d
            dsimp [g1, g2, g3]
            have hh := hlevel d
            -- hh : g1d + g2d + g3d-type sum = 0 but grouping (g1) + ((g2) + (g3))
            simpa [add_assoc] using hh
          rw [hz]
          simp


/-- ★ ζ-level Cor 2.6: a fixed (level-`d`) relation stays fixed after prepending an
arbitrary positive entry `x` to every tuple, at the ζ level (sum over `d` of
`StepL1.fixed_rel_prepend`).  This is the paper's `B*_{s_1} ∘ … ∘ B*_{s_{j−1}}` step
of Prop 2.12 (2.14). -/
theorem fixed_prepend_zeta {ι : Type*} [Fintype ι]
    (dep : ι → ℕ) (hdep : ∀ i, 0 < dep i) (c : ∀ i, Fin (dep i) → ℕ+)
    (a : ι → RatFunc F) (x : ℕ+)
    (h : ∀ d : ℕ, ∑ i, ((a i : RatFunc.CompletionAtInfty F) *
        S F (dep i) (hdep i) (c i) d) = 0) :
    ∑ i, ((a i : RatFunc.CompletionAtInfty F) * ζ_A F (consVec x (c i))) = 0 := by
  classical
  exact zeta_fixed_bridge F
    (dep := fun i => dep i + 1) (hdep := fun i => by omega)
    (c := fun i => consVec x (c i)) (a := a)
    (fixed_rel_prepend F dep hdep c a x h)

end ZagierHoffmanPositiveChar
