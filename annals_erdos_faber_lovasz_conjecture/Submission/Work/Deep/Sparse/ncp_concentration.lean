import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbModel
import Submission.Work.Deep.Sparse.ProbBasic
import Submission.Work.Deep.Sparse.SliceDefs
import Submission.Work.Deep.Sparse.NcpDefs
import Submission.Work.Deep.Sparse.expect_pair_sub_triple
import Submission.Work.Deep.Sparse.log_large_of_growth
import Submission.Work.Deep.Sparse.occH_eq_sum_occW
import Submission.Work.Deep.Sparse.occHtrunc_eq_sum
import Submission.Work.Deep.Sparse.occHtrunc_sub_le
import Submission.Work.Deep.Sparse.occClass_eq_sum_occW
import Submission.Work.Deep.Sparse.colourClassCount_update_abs_le
import Submission.Work.Deep.Sparse.occSlice_update_le
import Submission.Work.Deep.Sparse.occSlice_update_out_le
import Submission.Work.Deep.Sparse.fibreMean_azuma
import Submission.Work.Deep.Sparse.fibreMean_indicator
import Submission.Work.Deep.Sparse.colSpace_expect_fibreMean
import Submission.Work.Deep.Sparse.occRaw_tail
import Submission.Work.Deep.Sparse.fibreMean_occRaw_le
import Submission.Work.Deep.Sparse.expect_occRaw_le
import Submission.Work.Deep.Sparse.fibreMean_occSlice_lipschitz
import Submission.Work.Deep.Sparse.azuma_finSpace
import Submission.Work.Deep.Sparse.ncp_azuma_exponents
import Submission.Work.Deep.Sparse.ncp_tail_bound

/-!
# Concentration of `pairTerm - tripleTerm` in the naive colouring procedure

The target `Work.Deep.Sparse.ncp_concentration` is the deep input of
`Work.Deep.Sparse.ncp_lower_tail` (hence of `Work.Deep.Sparse.concentration_ncp`):
the statistic `X = pairTerm v - tripleTerm v` of the partial colouring `ofColoring G f`
is concentrated around its mean at the scale `ω/6`, where
`ω = (|nonAdjPairs G v|/2)·(1/k)·((k-1)/k)^(2D)` is the expectation lower bound of
`Work.Deep.Sparse.expect_pair_sub_triple`.

The elementary structural facts that any concentration argument for `X` uses are recorded
here:

* `occCount G f v j` — the number of colours carried by at least `j` *retained* neighbours
  of `v`; thus `occCount G f v 2` is the number of *repeated* colours (`firingCard`), and
  `X = ∑_{j ≥ 2} w j · occCount G f v j` with `w j = (j-1)(4-j)/2`.

* `occCount_update_lipschitz` — **recolouring a single vertex changes `occCount G · v j` by at
  most `2`**, because only the two colours involved in the recolouring can change their
  retained class count.  This is the "smoothness" property needed by bounded-differences
  (Azuma–Hoeffding) arguments; here it applies *conditionally on the colours of the vertices
  outside `N(v)`*, where the only free coordinates are the `deg v ≤ D` colours of `N(v)`.

## State of the proof of `ncp_concentration`

The statement is **true**: numerically (random `σ`-sparse graphs with `D` between `100` and
`400`, `k = D`) the standard deviation of `X` scales like `c·√D` while the threshold `ω/6`
scales like `c'·D`, so the threshold is `Θ(√D) ≈ 10⁷` standard deviations in the admissible
regime `D ≥ 10⁶ (log(D+2))⁸` (forced by `hbig`); the true tail is therefore far below
`exp(-(log(D+2))⁴/5000)`.

The two structural ingredients — the expansion `X = ∑_{j ≥ 2} w j · occCount G f v j`
(`w j = (j-1)(4-j)/2`) and the 2-Lipschitz property proved below — are exactly the
hypotheses of a bounded-differences argument **conditional on the colours outside `N(v)`**
(which turns the `≤ D² + 1` relevant coordinates into the `deg v ≤ D` colours of `N(v)`).

Two further analytic inputs are needed and are *not* available in this development:

1. **Azuma–Hoeffding for `colSpace`** — delegated as `Work.Deep.Sparse.azuma_finSpace`
   (the product-space McDiarmid inequality in the `FinSpace` vocabulary of
   `Submission/Work/Deep/Sparse/ProbBasic.lean`); it yields, conditionally on any outside
   colouring, `P[|occCount G · v j - E[· | η]| ≥ τ | η] ≤ 2 exp(-τ²/(8 deg v))`.

2. **Concentration of the conditional mean** `η ↦ E[X | η]` around `E X`.  This is the step
   for which no argument is known to this development: `E[X | η]` is a function of the
   *availability profiles* `A x = Fin k ∖ {f z : z ∈ N(x) ∖ N(v)}` of the *outside* colouring,
   which lives on up to `deg v · D ≤ D²` coordinates with `O(1)`-Lipschitz dependence on each
   of them, so Azuma on the outside gives only `exp(-Θ(τ²/D²))` — far too weak.  The
   Bruhn–Joos "exceptional outcomes" route cannot be used either: to beat the target
   `exp(-(log(D+2))⁴/5000)` the exceptional threshold `m` must satisfy `m log m ≳ (log D)⁴`,
   i.e. `m ≳ 200`, while the certificate constant of `P_v - T_v` at threshold `m` is
   `Θ(m³)` (a single recolouring can unretain `m` neighbours through one witness and each
   such flip destroys `Θ(m²)` triples), whereas the threshold `ω/6` allows only `c ≲ (log D)²`.
   Equivalently, `P_v - T_v` is not certifiable: forcing `P_v - T_v ≥ s` requires certifying
   the *absence* of unretained same-coloured neighbours, which cannot be done with `O(s)`
   coordinates.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **occupancy count** `occCount G f v j`: the number of colours carried by at least `j`
*retained* neighbours of `v` (with `occCount G f v 2 = firingCard G v f`). -/
noncomputable def occCount (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (f : V → Fin k)
    (v : V) (j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G f v c)).card

/-- **Recolouring one vertex does not change the class count of a colour different from both
colours involved.** -/
lemma colourClassCount_update_of_ne (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (f : V → Fin k) (u : V) (a : Fin k) (v : V) {c : Fin k}
    (hc1 : c ≠ f u) (hc2 : c ≠ a) :
    colourClassCount G (Function.update f u a) v c = colourClassCount G f v c := by
  classical
  unfold colourClassCount
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  have key : ∀ y : V, (Function.update f u a y = c) ↔ (f y = c) := by
    intro y
    rw [Function.update_apply]
    by_cases hy : y = u
    · subst hy
      simp only [if_pos rfl]
      exact ⟨fun h => absurd h.symm hc2, fun h => absurd h.symm hc1⟩
    · rw [if_neg hy]
  constructor
  · rintro ⟨hret, hcol⟩
    have hfx : f x = c := (key x).mp hcol
    refine ⟨fun z hz hzf => ?_, hfx⟩
    have hz' : f z = c := by rw [hzf, hfx]
    exact hret z hz (by rw [(key z).mpr hz', (key x).mpr hfx])
  · rintro ⟨hret, hcol⟩
    have hfx : f x = c := hcol
    have hxu : Function.update f u a x = c := (key x).mpr hfx
    refine ⟨fun z hz hzf => ?_, hxu⟩
    have hz' : f z = c := (key z).mp (by rw [hzf, hxu])
    exact hret z hz (by rw [hz', hfx])

/-- **`occCount` changes by at most `2` when a single vertex is recoloured.** -/
theorem occCount_update_lipschitz (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (f : V → Fin k) (u : V) (a : Fin k) (v : V) (j : ℕ) :
    |((occCount G (Function.update f u a) v j : ℝ) - (occCount G f v j : ℝ))| ≤ 2 := by
  classical
  have hsub : ((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G f v c))
      ⊆ ((Finset.univ : Finset (Fin k)).filter
            (fun c => j ≤ colourClassCount G (Function.update f u a) v c)) ∪ {f u, a} := by
    intro c hc
    rw [Finset.mem_filter] at hc
    by_cases hca : c = f u
    · exact Finset.mem_union_right _ (by simp [hca])
    by_cases hcb : c = a
    · exact Finset.mem_union_right _ (by simp [hcb])
    refine Finset.mem_union_left _ ?_
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ c, by
      rw [colourClassCount_update_of_ne G f u a v hca hcb]; exact hc.2⟩
  have hsub' : ((Finset.univ : Finset (Fin k)).filter
        (fun c => j ≤ colourClassCount G (Function.update f u a) v c))
      ⊆ ((Finset.univ : Finset (Fin k)).filter (fun c => j ≤ colourClassCount G f v c))
        ∪ {f u, a} := by
    intro c hc
    rw [Finset.mem_filter] at hc
    by_cases hca : c = f u
    · exact Finset.mem_union_right _ (by simp [hca])
    by_cases hcb : c = a
    · exact Finset.mem_union_right _ (by simp [hcb])
    refine Finset.mem_union_left _ ?_
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ c, by
      rw [← colourClassCount_update_of_ne G f u a v hca hcb]; exact hc.2⟩
  have hpair : ({f u, a} : Finset (Fin k)).card ≤ 2 := by
    calc ({f u, a} : Finset (Fin k)).card ≤ ({a} : Finset (Fin k)).card + 1 :=
          Finset.card_insert_le _ _
      _ = 2 := by simp
  have hcard1 : (Finset.univ.filter (fun c : Fin k => j ≤ colourClassCount G f v c)).card
      ≤ (Finset.univ.filter (fun c : Fin k =>
          j ≤ colourClassCount G (Function.update f u a) v c)).card + 2 :=
    le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) (by linarith))
  have hcard2 : (Finset.univ.filter (fun c : Fin k =>
        j ≤ colourClassCount G (Function.update f u a) v c)).card
      ≤ (Finset.univ.filter (fun c : Fin k => j ≤ colourClassCount G f v c)).card + 2 :=
    le_trans (Finset.card_le_card hsub') (le_trans (Finset.card_union_le _ _) (by linarith))
  have key1 : occCount G f v j
      = (Finset.univ.filter (fun c : Fin k => j ≤ colourClassCount G f v c)).card := rfl
  have key2 : occCount G (Function.update f u a) v j
      = (Finset.univ.filter (fun c : Fin k =>
          j ≤ colourClassCount G (Function.update f u a) v c)).card := rfl
  have h1R : ((Finset.univ.filter (fun c : Fin k => j ≤ colourClassCount G f v c)).card : ℝ)
      ≤ ((Finset.univ.filter (fun c : Fin k =>
          j ≤ colourClassCount G (Function.update f u a) v c)).card : ℝ) + 2 := by
    exact_mod_cast hcard1
  have h2R : ((Finset.univ.filter (fun c : Fin k =>
        j ≤ colourClassCount G (Function.update f u a) v c)).card : ℝ)
      ≤ ((Finset.univ.filter (fun c : Fin k => j ≤ colourClassCount G f v c)).card : ℝ) + 2 := by
    exact_mod_cast hcard2
  rw [key1, key2, abs_le]
  constructor <;> linarith


/-! ## Auxiliary lemmas for the concentration proof -/

/-- Subadditivity of `prob` for two events. -/
private lemma prob_union_le_aux {Ω : Type*} [Fintype Ω] (P : FinSpace Ω) (A B : Set Ω) :
    P.prob (A ∪ B) ≤ P.prob A + P.prob B := by
  rw [FinSpace.prob, FinSpace.prob, FinSpace.prob, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun ω _ => ?_)
  by_cases hA : ω ∈ A
  · by_cases hB : ω ∈ B
    · rw [Set.indicator_of_mem (show ω ∈ A ∪ B from Or.inl hA) P.mass,
        Set.indicator_of_mem hA P.mass, Set.indicator_of_mem hB P.mass]
      linarith [P.mass_nonneg ω]
    · rw [Set.indicator_of_mem (show ω ∈ A ∪ B from Or.inl hA) P.mass,
        Set.indicator_of_mem hA P.mass, Set.indicator_of_notMem hB P.mass]
      linarith [P.mass_nonneg ω]
  · by_cases hB : ω ∈ B
    · rw [Set.indicator_of_mem (show ω ∈ A ∪ B from Or.inr hB) P.mass,
        Set.indicator_of_notMem hA P.mass, Set.indicator_of_mem hB P.mass]
      linarith [P.mass_nonneg ω]
    · rw [Set.indicator_of_notMem (by simp [Set.mem_union, hA, hB] : ω ∉ A ∪ B) P.mass,
        Set.indicator_of_notMem hA P.mass, Set.indicator_of_notMem hB P.mass]
      norm_num

/-- The variance proxy of the *outside* Azuma step: `∑_u c_u² ≤ 7200000 D` for
`c u = occWsum ncpJ · 2 |N u ∩ N v| / k` off `N(v)` and `0` on it. -/
private lemma ncp_outside_sumsq_aux {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k D : ℕ} (hk : 0 < k) (hD : 0 < D) (hDk : D ≤ 2 * k)
    (hdeg : ∀ x : V, G.degree x ≤ D) (v : V) :
    (∑ u : V, (if u ∈ G.neighborFinset v then 0
        else occWsum ncpJ * (2 * (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ)
          / (k : ℝ))) ^ 2)
      ≤ 7200000 * (D : ℝ) := by
  classical
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hw : occWsum ncpJ = 667 := occWsum_ncpJ
  have hw0 : (0 : ℝ) ≤ occWsum ncpJ := by rw [hw]; norm_num
  -- the "count" function
  have hc0 : ∀ u : V, (0 : ℝ) ≤ (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ) :=
    fun u => by positivity
  have hcD : ∀ u : V, (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ) ≤ (D : ℝ) := by
    intro u
    have h1 : ((G.neighborFinset u) ∩ (G.neighborFinset v)).card ≤ D := by
      calc ((G.neighborFinset u) ∩ (G.neighborFinset v)).card
          ≤ (G.neighborFinset u).card := Finset.card_le_card Finset.inter_subset_left
        _ = G.degree u := SimpleGraph.card_neighborFinset_eq_degree G u
        _ ≤ D := hdeg u
    exact_mod_cast h1
  -- double counting: `∑_u |N u ∩ N v| = ∑_{y ∈ N v} deg y ≤ D²`
  have hcsum : ∑ u : V, (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ)
      ≤ (D : ℝ) ^ 2 := by
    have hpoint : ∀ u : V, (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ)
        = ∑ y ∈ G.neighborFinset v, (if y ∈ G.neighborFinset u then (1 : ℝ) else 0) := by
      intro u
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter]
      exact_mod_cast Finset.card_filter (fun y => y ∈ G.neighborFinset u) (G.neighborFinset v)
    calc ∑ u : V, (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ)
        = ∑ u : V, ∑ y ∈ G.neighborFinset v,
            (if y ∈ G.neighborFinset u then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl (fun u _ => hpoint u)
      _ = ∑ y ∈ G.neighborFinset v, ∑ u : V,
            (if y ∈ G.neighborFinset u then (1 : ℝ) else 0) := Finset.sum_comm
      _ = ∑ y ∈ G.neighborFinset v, (G.degree y : ℝ) := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          have hset : (Finset.univ.filter (fun u : V => y ∈ G.neighborFinset u))
              = G.neighborFinset y := by
            ext u
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
            exact SimpleGraph.adj_comm G u y
          rw [Finset.sum_boole, hset, SimpleGraph.card_neighborFinset_eq_degree]
      _ ≤ ∑ _y ∈ G.neighborFinset v, (D : ℝ) := by
          refine Finset.sum_le_sum (fun y _ => ?_)
          exact_mod_cast hdeg y
      _ = ((G.neighborFinset v).card : ℝ) * (D : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (D : ℝ) * (D : ℝ) := by
          have h1 : ((G.neighborFinset v).card : ℝ) ≤ (D : ℝ) := by
            rw [SimpleGraph.card_neighborFinset_eq_degree]
            exact_mod_cast hdeg v
          exact mul_le_mul_of_nonneg_right h1 (le_of_lt hDR)
      _ = (D : ℝ) ^ 2 := by ring
  -- `∑ c_u² ≤ D³`
  have hsq : ∑ u : V, (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ) ^ 2
      ≤ (D : ℝ) ^ 3 := by
    calc ∑ u : V, (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ) ^ 2
        ≤ ∑ u : V, (D : ℝ) * (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ) := by
          refine Finset.sum_le_sum (fun u _ => ?_)
          nlinarith [hc0 u, hcD u]
      _ = (D : ℝ) * ∑ u : V, (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (D : ℝ) * (D : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hcsum (le_of_lt hDR)
      _ = (D : ℝ) ^ 3 := by ring
  -- the coefficient estimate: `(2 w / k)² ≤ 16 w² / D²`
  have hcoef : (2 * occWsum ncpJ / (k : ℝ)) ^ 2 ≤ 16 * (occWsum ncpJ) ^ 2 / (D : ℝ) ^ 2 := by
    have hD2pos : (0 : ℝ) < (D : ℝ) ^ 2 := pow_pos hDR 2
    have hk2pos : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hkR 2
    have hD2q : (0 : ℝ) < (D : ℝ) ^ 2 / 4 := by positivity
    have hk2 : (D : ℝ) ^ 2 / 4 ≤ (k : ℝ) ^ 2 := by
      have h1 : (D : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hDk
      nlinarith [hDR, hkR]
    have hinv : 1 / (k : ℝ) ^ 2 ≤ 1 / ((D : ℝ) ^ 2 / 4) :=
      one_div_le_one_div_of_le hD2q hk2
    have h4 : 1 / ((D : ℝ) ^ 2 / 4) = 4 / (D : ℝ) ^ 2 := by
      rw [one_div_div]
    rw [h4] at hinv
    calc (2 * occWsum ncpJ / (k : ℝ)) ^ 2
        = (2 * occWsum ncpJ) ^ 2 * (1 / (k : ℝ) ^ 2) := by
          rw [div_pow, div_eq_mul_inv, one_div]
      _ ≤ (2 * occWsum ncpJ) ^ 2 * (4 / (D : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
      _ = 16 * (occWsum ncpJ) ^ 2 / (D : ℝ) ^ 2 := by ring
  -- full sum bound
  have hfull : ∑ u : V, (occWsum ncpJ
        * (2 * (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ) / (k : ℝ))) ^ 2
      ≤ 7200000 * (D : ℝ) := by
    have hstep : ∑ u : V, (occWsum ncpJ
          * (2 * (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ) / (k : ℝ))) ^ 2
        = (2 * occWsum ncpJ / (k : ℝ)) ^ 2
          * ∑ u : V, (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      ring
    rw [hstep]
    have hmid : (16 * (occWsum ncpJ) ^ 2 / (D : ℝ) ^ 2) * (D : ℝ) ^ 3
        = 16 * (occWsum ncpJ) ^ 2 * (D : ℝ) := by
      rw [div_mul_eq_mul_div]
      field_simp
    have hfin : 16 * (occWsum ncpJ) ^ 2 ≤ 7200000 := by rw [hw]; norm_num
    calc (2 * occWsum ncpJ / (k : ℝ)) ^ 2
          * ∑ u : V, (((G.neighborFinset u) ∩ (G.neighborFinset v)).card : ℝ) ^ 2
        ≤ (2 * occWsum ncpJ / (k : ℝ)) ^ 2 * (D : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ ≤ (16 * (occWsum ncpJ) ^ 2 / (D : ℝ) ^ 2) * (D : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = 16 * (occWsum ncpJ) ^ 2 * (D : ℝ) := hmid
      _ ≤ 7200000 * (D : ℝ) := mul_le_mul_of_nonneg_right hfin (le_of_lt hDR)
  -- drop the `if`-guard
  refine le_trans (Finset.sum_le_sum (fun u _ => ?_)) hfull
  by_cases hu : u ∈ G.neighborFinset v
  · rw [if_pos hu, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact sq_nonneg _
  · rw [if_neg hu]

/-- The number of retained neighbours of `v` of colour `c` is at most the degree of `v`. -/
lemma colourClassCount_le_degree (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (f : V → Fin k)
    (v : V) (c : Fin k) : colourClassCount G f v c ≤ G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- **`pairTerm v - tripleTerm v` is the slice sum over the full range.** -/
lemma pairTerm_sub_tripleTerm_eq_occSlice (G : SimpleGraph V) [DecidableRel G.Adj] {k D : ℕ}
    (hdeg : ∀ x : V, G.degree x ≤ D) (f : V → Fin k) (v : V) :
    (((ofColoring G f).pairTerm v : ℝ) - ((ofColoring G f).tripleTerm v : ℝ))
      = occSlice G f v D := by
  classical
  rw [pairTerm_ofColoring, tripleTerm_ofColoring, ← occClass_eq_sum_occW]
  unfold occClass
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hle : colourClassCount G f v c ≤ D :=
    le_trans (colourClassCount_le_degree G f v c) (hdeg v)
  rw [occHtrunc, occH, min_eq_left hle]

theorem ncp_concentration {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k D : ℕ} (hk : 0 < k) (hD : 0 < D) (hDk : D ≤ 2 * k) (hkD : (k : ℝ) ≤ 2 * D)
    [Nonempty (V → Fin k)] (hdeg : ∀ x : V, G.degree x ≤ D) (v : V)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsp : (δ / 2) * (D : ℝ) ^ 2 / 2 ≤ ((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2)
    (hbig : (10 : ℝ) ^ 6 * (Real.log ((D : ℝ) + 2)) ^ 8 ≤ δ ^ 2 * (D : ℝ)) :
    (Work.Deep.Sparse.colSpace (V := V) k).prob
        {f | (1 / 6) * (((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) / 2
                * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D)))
              ≤ |(((Work.Deep.Sparse.ofColoring G f).pairTerm v : ℝ)
                  - ((Work.Deep.Sparse.ofColoring G f).tripleTerm v : ℝ))
                - (Work.Deep.Sparse.colSpace (V := V) k).expect
                    (fun f => (((Work.Deep.Sparse.ofColoring G f).pairTerm v : ℝ)
                      - ((Work.Deep.Sparse.ofColoring G f).tripleTerm v : ℝ)))|}
      ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000) := by
  classical
  -- ===================== 0. Abbreviations =====================
  set A : Finset V := G.neighborFinset v with hA
  set P : (V → Fin k) → ℝ := fun f =>
    (((ofColoring G f).pairTerm v : ℝ) - ((ofColoring G f).tripleTerm v : ℝ)) with hP
  set U : (V → Fin k) → ℝ := fun f => occSlice G f v D with hU
  set X6 : (V → Fin k) → ℝ := fun f => occSlice G f v ncpJ with hX6
  set fM : (V → Fin k) → ℝ := fibreMean A X6 with hfM
  set Y : (V → Fin k) → ℝ := fun f => occSlice G f v D - occSlice G f v ncpJ with hY
  set c2 : V → ℝ := fun u => if u ∈ A then 0
    else occWsum ncpJ * (2 * (((G.neighborFinset u) ∩ A).card : ℝ) / (k : ℝ)) with hc2
  set T : ℝ := (1 / 3) * ((1 / 6) * ncpOmega G k D v) with hT
  have hom' : ncpOmega G k D v = ((nonAdjPairs G v).card : ℝ) / 2
      * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D)) := rfl
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  -- ===================== 1. basic facts =====================
  have hom_nonneg : 0 ≤ ncpOmega G k D v := by
    rw [hom']
    have h1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    exact mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (pow_nonneg (div_nonneg h1 (le_of_lt hkR)) _))
  have hTnn : 0 ≤ T := by
    rw [hT]
    exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hom_nonneg)
  have hAne : A ≠ ∅ := by
    intro hAe
    have hN : G.neighborFinset v = ∅ := by rw [← hA]; exact hAe
    have hsub : nonAdjPairs G v ⊆ (G.neighborFinset v).product (G.neighborFinset v) := by
      intro p hp
      rw [nonAdjPairs] at hp
      exact (Finset.mem_filter.mp hp).1
    have hcard : (nonAdjPairs G v).card = 0 := by
      rw [Finset.card_eq_zero]
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun p hp => ?_)
      have h1 := hsub hp
      rw [hN] at h1
      simpa using h1
    have hsp' := hsp
    rw [hcard] at hsp'
    simp only [Nat.cast_zero, zero_div] at hsp'
    have hpos : (0 : ℝ) < (δ / 2) * (D : ℝ) ^ 2 / 2 := by
      have hδD : (0 : ℝ) < δ * (D : ℝ) ^ 2 := by positivity
      linarith
    linarith
  -- ===================== 2. the decomposition identities =====================
  have hP_eq : ∀ f : V → Fin k, P f = U f := by
    intro f
    rw [hP, hU]
    exact pairTerm_sub_tripleTerm_eq_occSlice G hdeg f v
  have hEP : (colSpace (V := V) k).expect P = (colSpace (V := V) k).expect U := by
    simp only [FinSpace.expect]
    exact Finset.sum_congr rfl (fun f _ => by rw [hP_eq f])
  have hYU : ∀ f : V → Fin k, Y f = U f - X6 f := by
    intro f
    simp only [hY, hU, hX6]
  have hYeq : Y = U - X6 := by
    funext f
    rw [hYU f, Pi.sub_apply]
  have hEsplit : (colSpace (V := V) k).expect U
      = (colSpace (V := V) k).expect X6 + (colSpace (V := V) k).expect Y := by
    rw [FinSpace.expect, FinSpace.expect, FinSpace.expect, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun f _ => by rw [hYU f]; ring)
  have hEfM : (colSpace (V := V) k).expect fM = (colSpace (V := V) k).expect X6 := by
    simpa [hfM] using colSpace_expect_fibreMean A X6
  -- ===================== 3. Lipschitz constants =====================
  have hw0 : (0 : ℝ) ≤ occWsum ncpJ := by rw [occWsum_ncpJ]; norm_num
  have hc1nn : 0 ≤ 2 * occWsum ncpJ := by linarith
  have hc2nn : ∀ u : V, 0 ≤ c2 u := by
    intro u
    simp only [hc2]
    by_cases hu : u ∈ A
    · rw [if_pos hu]
    · rw [if_neg hu]
      exact mul_nonneg hw0 (div_nonneg (by positivity) (le_of_lt hkR))
  have hlip1 : ∀ u ∈ A, ∀ (f : V → Fin k) (x : Fin k),
      |X6 (Function.update f u x) - X6 f| ≤ 2 * occWsum ncpJ := by
    intro u _ f x
    simp only [hX6]
    simpa using occSlice_update_le (J := ncpJ) G f v u x
  have hlip2 : ∀ u : V, ∀ (f : V → Fin k) (x : Fin k),
      |fM (Function.update f u x) - fM f| ≤ c2 u := by
    intro u f x
    simp only [hc2]
    by_cases hu : u ∈ A
    · rw [if_pos hu]
      have heq : fM (Function.update f u x) = fM f := by
        have hgr : Function.update f u x
            = graft A (Function.update (fun a : ↥A => f a.val) ⟨u, hu⟩ x) f := by
          funext w
          by_cases hw : w = u
          · subst hw
            rw [graft_apply_of_mem _ _ hu, Function.update_self]
            simp
          · rw [Function.update_of_ne hw]
            by_cases hwA : w ∈ A
            · have hne : (⟨w, hwA⟩ : ↥A) ≠ ⟨u, hu⟩ :=
                fun h => hw (congrArg Subtype.val h)
              rw [graft_apply_of_mem _ _ hwA, Function.update_of_ne hne]
            · rw [graft_apply_of_notMem _ _ hwA]
        rw [hfM, hX6, hgr, fibreMean_graft]
      rw [heq]
      simp
    · rw [if_neg hu]
      rw [hfM, hX6]
      have h := fibreMean_occSlice_lipschitz (J := ncpJ) (z := u) G f v
        (by rw [← hA]; exact hu) x
      simpa [hA] using h
  -- ===================== 4. the two Azuma estimates =====================
  have hprob1 : (colSpace (V := V) k).prob {f : V → Fin k | T < |X6 f - fM f|}
      ≤ 2 * Real.exp (-(2 * T ^ 2) / ∑ u ∈ A, (2 * occWsum ncpJ) ^ 2) := by
    have h := fibreMean_azuma (V := V) (k := k) A X6 (fun _ => 2 * occWsum ncpJ)
      (fun _ _ => hc1nn) hlip1 T hTnn
    simpa [← hfM] using h
  have hprob2 : (colSpace (V := V) k).prob
      {f : V → Fin k | T < |fM f - (colSpace (V := V) k).expect fM|}
      ≤ 2 * Real.exp (-(2 * T ^ 2) / ∑ u : V, (c2 u) ^ 2) :=
    azuma_finSpace (V := V) (k := k) fM c2 hc2nn hlip2 T hTnn
  have htail : (colSpace (V := V) k).prob
      {f : V → Fin k | T ≤ |Y f - (colSpace (V := V) k).expect Y|}
      ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2) := by
    simpa [hT, hY] using ncp_tail_bound G hk hD hDk hkD hdeg v hδ0 hδ1 hsp hbig
  -- ===================== 5. the exponent arithmetic =====================
  have hγ := ncp_azuma_exponents G hk hD hDk hkD hdeg v hδ0 hδ1 hsp hbig
  obtain ⟨hγ1, hγ2⟩ := hγ
  have hγ1' : 2 * Real.exp (-(2 * T ^ 2) / ((D : ℝ) * (2 * occWsum ncpJ) ^ 2))
      ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2) := by
    simpa [hT] using hγ1
  have hγ2' : 2 * Real.exp (-(2 * T ^ 2) / ((7200000 : ℝ) * (D : ℝ)))
      ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2) := by
    simpa [hT] using hγ2
  have hwpos : (0 : ℝ) < 2 * occWsum ncpJ := by rw [occWsum_ncpJ]; norm_num
  have hsum1 : ∑ u ∈ A, (2 * occWsum ncpJ) ^ 2 ≤ (D : ℝ) * (2 * occWsum ncpJ) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [hA, SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast hdeg v
  have hsum2 : ∑ u : V, (c2 u) ^ 2 ≤ 7200000 * (D : ℝ) := by
    simp only [hc2]
    simpa [hA] using ncp_outside_sumsq_aux G hk hD hDk hdeg v
  have hexp1 : 2 * Real.exp (-(2 * T ^ 2) / ∑ u ∈ A, (2 * occWsum ncpJ) ^ 2)
      ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2) := by
    refine le_trans ?_ hγ1'
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    have hAcard : 0 < (A.card : ℝ) := by
      have h1 : 0 < A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAne)
      exact_mod_cast h1
    have hSpos : 0 < ∑ u ∈ A, (2 * occWsum ncpJ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_pos hAcard (pow_pos hwpos 2)
    have hDc : 0 < (D : ℝ) * (2 * occWsum ncpJ) ^ 2 := mul_pos hDR (pow_pos hwpos 2)
    have hinv : (((D : ℝ) * (2 * occWsum ncpJ) ^ 2))⁻¹
        ≤ (∑ u ∈ A, (2 * occWsum ncpJ) ^ 2)⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hSpos hsum1
    have hmain1 : (2 * T ^ 2) / ((D : ℝ) * (2 * occWsum ncpJ) ^ 2)
        ≤ (2 * T ^ 2) / (∑ u ∈ A, (2 * occWsum ncpJ) ^ 2) := by
      simp only [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    simpa only [div_eq_mul_inv, neg_mul] using neg_le_neg hmain1
  have hexp2 : 2 * Real.exp (-(2 * T ^ 2) / ∑ u : V, (c2 u) ^ 2)
      ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2) := by
    refine le_trans ?_ hγ2'
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    have hterm : (c2 v) ^ 2 ≤ ∑ u : V, (c2 u) ^ 2 := by
      refine Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ v)
    have hvA : v ∉ A := by
      rw [hA, SimpleGraph.mem_neighborFinset]
      exact G.irrefl
    have hc2v : 0 < c2 v := by
      simp only [hc2]
      rw [if_neg hvA]
      have hcard : (0 : ℝ) < (((G.neighborFinset v) ∩ A).card : ℝ) := by
        rw [hA, Finset.inter_self]
        have h1 : 0 < (G.neighborFinset v).card := by
          rw [← hA]
          exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAne)
        exact_mod_cast h1
      exact mul_pos (by rw [occWsum_ncpJ]; norm_num) (div_pos (by linarith) hkR)
    have hS2pos : 0 < ∑ u : V, (c2 u) ^ 2 := lt_of_lt_of_le (pow_pos hc2v 2) hterm
    have hden : 0 < (7200000 : ℝ) * (D : ℝ) := by positivity
    have hinv : (((7200000 : ℝ) * (D : ℝ)))⁻¹ ≤ (∑ u : V, (c2 u) ^ 2)⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hS2pos hsum2
    have hmain2 : (2 * T ^ 2) / ((7200000 : ℝ) * (D : ℝ))
        ≤ (2 * T ^ 2) / (∑ u : V, (c2 u) ^ 2) := by
      simp only [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    simpa only [div_eq_mul_inv, neg_mul] using neg_le_neg hmain2
  -- ===================== 6. the union bound =====================
  have hsub : {f : V → Fin k | (1 / 6) * ncpOmega G k D v ≤ |U f - (colSpace (V := V) k).expect U|}
      ⊆ {f : V → Fin k | T < |X6 f - fM f|}
        ∪ {f : V → Fin k | T < |fM f - (colSpace (V := V) k).expect fM|}
        ∪ {f : V → Fin k | T ≤ |Y f - (colSpace (V := V) k).expect Y|} := by
    intro f hf
    simp only [Set.mem_ofPred_eq] at hf ⊢
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    push Not at h1 h2 h3
    have hdec : U f - (colSpace (V := V) k).expect U
        = (X6 f - fM f) + (fM f - (colSpace (V := V) k).expect fM)
          + (Y f - (colSpace (V := V) k).expect Y) := by
      rw [hEsplit, hEfM]
      ring
    have htri : |U f - (colSpace (V := V) k).expect U| < 3 * T := by
      rw [hdec]
      have hA1 := abs_add_le ((X6 f - fM f) + (fM f - (colSpace (V := V) k).expect fM))
        (Y f - (colSpace (V := V) k).expect Y)
      have hA2 := abs_add_le (X6 f - fM f) (fM f - (colSpace (V := V) k).expect fM)
      calc |(X6 f - fM f) + (fM f - (colSpace (V := V) k).expect fM)
              + (Y f - (colSpace (V := V) k).expect Y)|
          ≤ |(X6 f - fM f) + (fM f - (colSpace (V := V) k).expect fM)|
              + |Y f - (colSpace (V := V) k).expect Y| := hA1
        _ ≤ |X6 f - fM f| + |fM f - (colSpace (V := V) k).expect fM|
              + |Y f - (colSpace (V := V) k).expect Y| := by linarith
        _ < (T + T) + T := by linarith
        _ = 3 * T := by ring
    have hT3 : (1 / 6) * ncpOmega G k D v = 3 * T := by
      rw [hT]; ring
    rw [hT3] at hf
    linarith
  have hunion : (colSpace (V := V) k).prob
      {f : V → Fin k | (1 / 6) * ncpOmega G k D v ≤ |U f - (colSpace (V := V) k).expect U|}
      ≤ (colSpace (V := V) k).prob {f : V → Fin k | T < |X6 f - fM f|}
        + (colSpace (V := V) k).prob
            {f : V → Fin k | T < |fM f - (colSpace (V := V) k).expect fM|}
        + (colSpace (V := V) k).prob
            {f : V → Fin k | T ≤ |Y f - (colSpace (V := V) k).expect Y|} := by
    have h1 := FinSpace.prob_mono (colSpace (V := V) k) hsub
    have h2 := prob_union_le_aux (colSpace (V := V) k)
      ({f : V → Fin k | T < |X6 f - fM f|}
        ∪ {f : V → Fin k | T < |fM f - (colSpace (V := V) k).expect fM|})
      {f : V → Fin k | T ≤ |Y f - (colSpace (V := V) k).expect Y|}
    have h3 := prob_union_le_aux (colSpace (V := V) k)
      {f : V → Fin k | T < |X6 f - fM f|}
      {f : V → Fin k | T < |fM f - (colSpace (V := V) k).expect fM|}
    linarith
  -- ===================== 7. conclusion =====================
  have hfinal : 5 * Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2)
      ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000) := by
    have h5 : (5 : ℝ) * Real.exp (-2) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos 2)]
      have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have h2 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
      rw [h1]
      nlinarith
    rw [sub_eq_add_neg, Real.exp_add]
    have hpos : 0 < Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000) := Real.exp_pos _
    nlinarith [h5, hpos]
  have hmain : (colSpace (V := V) k).prob
      {f : V → Fin k | (1 / 6) * ncpOmega G k D v ≤ |U f - (colSpace (V := V) k).expect U|}
      ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000) := by
    calc (colSpace (V := V) k).prob
          {f : V → Fin k | (1 / 6) * ncpOmega G k D v
            ≤ |U f - (colSpace (V := V) k).expect U|}
        ≤ (colSpace (V := V) k).prob {f : V → Fin k | T < |X6 f - fM f|}
            + (colSpace (V := V) k).prob
                {f : V → Fin k | T < |fM f - (colSpace (V := V) k).expect fM|}
            + (colSpace (V := V) k).prob
                {f : V → Fin k | T ≤ |Y f - (colSpace (V := V) k).expect Y|} := hunion
      _ ≤ 2 * Real.exp (-(2 * T ^ 2) / ∑ u ∈ A, (2 * occWsum ncpJ) ^ 2)
            + 2 * Real.exp (-(2 * T ^ 2) / ∑ u : V, (c2 u) ^ 2)
            + Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2) := by
          linarith [hprob1, hprob2, htail]
      _ ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2)
            + Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2)
            + Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2) := by
          linarith [hexp1, hexp2]
      _ = 3 * Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2) := by ring
      _ ≤ 5 * Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2) := by
          have := Real.exp_pos (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000 - 2)
          linarith
      _ ≤ Real.exp (-((Real.log ((D : ℝ) + 2)) ^ 4) / 5000) := hfinal
  have hset : {f : V → Fin k | (1 / 6)
        * (((nonAdjPairs G v).card : ℝ) / 2
          * ((1 : ℝ) / (k : ℝ) * (((k : ℝ) - 1) / (k : ℝ)) ^ (2 * D)))
        ≤ |P f - (colSpace (V := V) k).expect P|}
      = {f : V → Fin k | (1 / 6) * ncpOmega G k D v ≤ |U f - (colSpace (V := V) k).expect U|} := by
    ext f
    simp only [Set.mem_ofPred_eq]
    rw [hP_eq f, hEP, hom']
  rw [hset]
  exact hmain


end Work.Deep.Sparse
