/-
# Locally uniform extraction for vector-valued families on an open subset of `ℝ²`

This file proves `Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin`:
for an open `U ⊆ ℝ × ℝ`, a sequence `F : ℕ → ℝ × ℝ → (Fin k → ℝ)` that is

* locally uniformly bounded on compact subsets of `U`, and
* locally uniformly equicontinuous on compact subsets of `U`,

has a strictly monotone subsequence converging locally uniformly on `U`.

The proof is the classical Arzelà–Ascoli argument, carried out on the whole of `U` at once
(rather than on a fixed domain), so that no global compactness is needed:

1. a countable sequence `e` in `U` whose range is dense in `U` (`denseSeq_of_nonempty_aux`);
2. a Cantor diagonal extraction making the subsequence converge at every `e m`
   (`diag_extract_aux`, `diag_extract_fin_aux`);
3. equicontinuity upgrades convergence on the dense sequence to pointwise convergence at every
   point of `U` (`exists_tendsto_of_dense_equicont_fin_aux`);
4. on a compact `K ⊆ U`, a finite `δ`-net turns pointwise convergence plus uniform
   equicontinuity into uniform convergence (`tendstoUniformlyOn_of_pointwise_of_equicont_aux`).

Finally, `tendstoLocallyUniformlyOn_iff_forall_isCompact` (valid since `ℝ × ℝ` is locally
compact) identifies locally uniform convergence on the open set `U` with uniform convergence on
every compact subset of `U`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Lemmas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Filter Set Metric
open scoped Topology

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-! ## A dense sequence inside a nonempty subset of `ℝ²` -/

private theorem denseSeq_of_nonempty_aux {U : Set (ℝ × ℝ)} (hne : U.Nonempty) :
    ∃ e : ℕ → ℝ × ℝ, (∀ k : ℕ, e k ∈ U) ∧ ∀ p ∈ U, p ∈ closure (Set.range e) := by
  obtain ⟨t, htc, htsub, hUsub⟩ := TopologicalSpace.exists_countable_dense_subset U
  have htne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    obtain ⟨p, hp⟩ := hne
    have hpt : p ∈ closure t := hUsub hp
    rw [h, closure_empty] at hpt
    exact hpt
  obtain ⟨e, he⟩ := htc.exists_eq_range htne
  exact ⟨e, fun k => htsub (he.symm ▸ Set.mem_range_self k), fun p hp => he ▸ hUsub hp⟩

/-! ## Diagonal extraction with per-column bounds -/

/-- A sequence of real sequences, bounded column by column, has a subsequence converging in every
column.  Proved by normalising the columns to `[-1,1]` and using the sequential compactness of the
compact product `∏ₖ [-1,1]` (Tychonoff). -/
private theorem diag_extract_aux {u : ℕ → ℕ → ℝ}
    (h : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, |u n k| ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ, ∃ L : ℝ,
      Filter.Tendsto (fun n => u (φ n) k) Filter.atTop (nhds L) := by
  choose C hC using h
  set D : ℕ → ℝ := fun k => |C k| + 1 with hD
  have hDpos : ∀ k, 0 < D k := by
    intro k; rw [hD]; positivity
  have hb : ∀ n k : ℕ, |u n k / D k| ≤ 1 := by
    intro n k
    have h1 : |u n k| ≤ D k := by
      have h2 := hC k n
      rw [hD]
      linarith [h2, le_abs_self (C k)]
    rw [abs_div, abs_of_pos (hDpos k), div_le_one (hDpos k)]
    exact h1
  have hcomp : IsCompact (Set.univ.pi fun _ : ℕ => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hx : ∀ n : ℕ, (fun k => u n k / D k) ∈
      Set.univ.pi (fun _ : ℕ => Set.Icc (-1 : ℝ) 1) := by
    intro n
    rw [Set.mem_univ_pi]
    intro k
    exact abs_le.mp (hb n k)
  obtain ⟨a, -, φ, hφ, htend⟩ := hcomp.tendsto_subseq hx
  refine ⟨φ, hφ, fun k => ⟨a k * D k, ?_⟩⟩
  have h1 : Filter.Tendsto (fun n => u (φ n) k / D k * D k) Filter.atTop
      (nhds (a k * D k)) :=
    ((tendsto_pi_nhds.mp htend) k).mul_const (D k)
  have h2 : (fun n => u (φ n) k / D k * D k) = fun n => u (φ n) k := by
    funext n; exact div_mul_cancel₀ _ (ne_of_gt (hDpos k))
  rwa [h2] at h1

/-- Vector version of `diag_extract_aux`: the columns are indexed by `m : ℕ` but the values live
in `Fin k → ℝ`; flattening `(m, j) ↦ Nat.pair m j` and reassembling with `tendsto_pi_nhds` gives
the result. -/
private theorem diag_extract_fin_aux {k : ℕ} {e : ℕ → ℝ × ℝ} {F : ℕ → ℝ × ℝ → (Fin k → ℝ)}
    (hbdd : ∀ m : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖F n (e m)‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m : ℕ, ∃ L : Fin k → ℝ,
      Filter.Tendsto (fun n => F (φ n) (e m)) Filter.atTop (nhds L) := by
  have hcoord : ∀ t : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      |(if h : t.unpair.2 < k then F n (e t.unpair.1) ⟨t.unpair.2, h⟩ else 0)| ≤ C := by
    intro t
    obtain ⟨C, hC⟩ := hbdd t.unpair.1
    refine ⟨max C 0, fun n => ?_⟩
    by_cases h : t.unpair.2 < k
    · rw [dif_pos h]
      refine le_trans ?_ (le_trans (hC n) (le_max_left _ _))
      simpa [Real.norm_eq_abs] using
        norm_le_pi_norm (F n (e t.unpair.1)) ⟨t.unpair.2, h⟩
    · rw [dif_neg h]
      exact le_trans (le_of_eq (abs_zero)) (le_max_right _ _)
  obtain ⟨φ, hφ, hlim⟩ := diag_extract_aux (u := fun n t =>
      if h : t.unpair.2 < k then F n (e t.unpair.1) ⟨t.unpair.2, h⟩ else 0) hcoord
  refine ⟨φ, hφ, fun m => ?_⟩
  have hL : ∀ j : Fin k, ∃ L : ℝ,
      Filter.Tendsto (fun n => F (φ n) (e m) j) Filter.atTop (nhds L) := by
    intro j
    obtain ⟨L, hL⟩ := hlim (Nat.pair m j.1)
    refine ⟨L, ?_⟩
    have hfun : (fun n => (if h : (Nat.pair m j.1).unpair.2 < k then
          F (φ n) (e (Nat.pair m j.1).unpair.1) ⟨(Nat.pair m j.1).unpair.2, h⟩ else 0))
        = fun n => F (φ n) (e m) j := by
      funext n
      rw [Nat.unpair_pair, dif_pos j.2]
    rwa [hfun] at hL
  choose L hLs using hL
  exact ⟨L, tendsto_pi_nhds.mpr hLs⟩

/-! ## From a dense set to pointwise convergence -/

/-- A uniformly equicontinuous sequence that converges at every point of a set whose closure meets
the compact `K` at `p` converges at `p`.  (Cauchy criterion in the complete space `Fin k → ℝ`.) -/
private theorem exists_tendsto_of_dense_equicont_fin_aux {k : ℕ} {e : ℕ → ℝ × ℝ}
    {G : ℕ → ℝ × ℝ → (Fin k → ℝ)} {K : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hp : p ∈ closure (Set.range e ∩ K))
    (hconv : ∀ m : ℕ, ∃ L : Fin k → ℝ,
      Filter.Tendsto (fun n => G n (e m)) Filter.atTop (nhds L))
    (heq : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ q ∈ K, dist q p ≤ δ →
      ‖G n q - G n p‖ ≤ ε) :
    ∃ L : Fin k → ℝ, Filter.Tendsto (fun n => G n p) Filter.atTop (nhds L) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := heq (ε / 4) (by linarith)
  obtain ⟨d, ⟨hdmem, hdK⟩, hdp⟩ := Metric.mem_closure_iff.mp hp δ hδpos
  obtain ⟨m, rfl⟩ := hdmem
  obtain ⟨L, hL⟩ := hconv m
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hL (ε / 4) (by linarith)
  refine ⟨N, fun n hn n' hn' => ?_⟩
  have hdpm : dist (e m) p ≤ δ := le_of_lt (by rwa [dist_comm] at hdp)
  have hδ' : ∀ n : ℕ, dist (G n (e m)) (G n p) ≤ ε / 4 := fun n => by
    rw [dist_eq_norm]; exact hδ n (e m) hdK hdpm
  have h1 : dist (G n p) (G n (e m)) ≤ ε / 4 := by rw [dist_comm]; exact hδ' n
  have h2 : dist (G n (e m)) (G n' (e m)) < ε / 2 := by
    have ha := hN n hn
    have hb := hN n' hn'
    calc dist (G n (e m)) (G n' (e m))
        ≤ dist (G n (e m)) L + dist L (G n' (e m)) := dist_triangle _ _ _
      _ = dist (G n (e m)) L + dist (G n' (e m)) L := by rw [dist_comm L (G n' (e m))]
      _ < ε / 4 + ε / 4 := by linarith
      _ = ε / 2 := by ring
  have h3 : dist (G n' (e m)) (G n' p) ≤ ε / 4 := hδ' n'
  have h4 : dist (G n p) (G n' p)
      ≤ dist (G n p) (G n (e m)) + dist (G n (e m)) (G n' (e m)) + dist (G n' (e m)) (G n' p) :=
    dist_triangle4 _ _ _ _
  linarith

/-! ## Uniform convergence on a compact set -/

/-- Pointwise convergence plus uniform equicontinuity on a compact set give uniform convergence:
cover the compact set by finitely many `δ/2`-balls and use the three-term split. -/
private theorem tendstoUniformlyOn_of_pointwise_of_equicont_aux {k : ℕ} {K : Set (ℝ × ℝ)}
    {F : ℕ → ℝ × ℝ → (Fin k → ℝ)} {f : ℝ × ℝ → (Fin k → ℝ)}
    (hK : IsCompact K)
    (hpt : ∀ p ∈ K, Filter.Tendsto (fun n => F n p) Filter.atTop (nhds (f p)))
    (heqc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
      dist p q < δ → ‖F n p - F n q‖ < ε) :
    TendstoUniformlyOn F f Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := heqc (ε / 3) (by linarith)
  obtain ⟨T, hTK, hTfin, hTcov⟩ :=
    Metric.finite_approx_of_totallyBounded hK.totallyBounded (δ / 2) (by linarith)
  haveI : Fintype {t : ℝ × ℝ // t ∈ T} := hTfin.fintype
  have hev : ∀ᶠ n in Filter.atTop, ∀ t : {t : ℝ × ℝ // t ∈ T}, dist (f t.1) (F n t.1) < ε / 3 := by
    rw [Filter.eventually_all]
    intro t
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hpt t.1 (hTK t.2)) (ε / 3) (by linarith)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rwa [dist_comm] at h
  filter_upwards [hev] with n hn x hx
  obtain ⟨t, htT, hxt⟩ : ∃ t ∈ T, x ∈ ball t (δ / 2) := by
    rcases Set.mem_iUnion.mp (hTcov hx) with ⟨t, ht⟩
    rcases Set.mem_iUnion.mp ht with ⟨htT, hxt⟩
    exact ⟨t, htT, hxt⟩
  have hxtδ : dist x t < δ := by
    have h1 : dist x t < δ / 2 := mem_ball.mp hxt
    linarith
  have h1 : ‖F n x - F n t‖ < ε / 3 := hδ n x hx t (hTK htT) hxtδ
  have h2 : dist (f t) (F n t) < ε / 3 := hn ⟨t, htT⟩
  have h3 : dist (f x) (f t) ≤ ε / 3 := by
    have hxta : Filter.Tendsto (fun n' => F n' x) Filter.atTop (nhds (f x)) := hpt x hx
    have hta : Filter.Tendsto (fun n' => F n' t) Filter.atTop (nhds (f t)) := hpt t (hTK htT)
    have hnorm : Filter.Tendsto (fun n' => ‖F n' x - F n' t‖) Filter.atTop (nhds ‖f x - f t‖) :=
      (hxta.sub hta).norm
    have hle : ∀ n', ‖F n' x - F n' t‖ ≤ ε / 3 := fun n' =>
      le_of_lt (hδ n' x hx t (hTK htT) hxtδ)
    have h := le_of_tendsto_of_tendsto' hnorm tendsto_const_nhds hle
    rw [dist_eq_norm]
    exact h
  have h4 : dist (F n t) (F n x) = ‖F n x - F n t‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  have h5 : dist (f x) (F n x)
      ≤ dist (f x) (f t) + dist (f t) (F n t) + dist (F n t) (F n x) :=
    dist_triangle4 _ _ _ _
  linarith

/-! ## The main extraction -/

theorem exists_subseq_tendstoLocallyUniformlyOn_fin {k : ℕ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {F : ℕ → ℝ × ℝ → (Fin k → ℝ)}
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ U → ∃ C : ℝ, ∀ n : ℕ, ∀ p ∈ K, ‖F n p‖ ≤ C)
    (heqc : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ U → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K, dist p q < δ → ‖F n p - F n q‖ < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ × ℝ → (Fin k → ℝ),
      TendstoLocallyUniformlyOn (fun n p => F (φ n) p) f Filter.atTop U := by
  classical
  rcases U.eq_empty_or_nonempty with hUe | hUne
  · rw [hUe]
    refine ⟨id, strictMono_id, fun _ => 0, ?_⟩
    intro u hu x hx
    exact absurd hx (by simp)
  · obtain ⟨e, heU, hedense⟩ := denseSeq_of_nonempty_aux hUne
    have hcol : ∀ m : ℕ, ∃ C : ℝ, ∀ n : ℕ, ‖F n (e m)‖ ≤ C := by
      intro m
      obtain ⟨C, hC⟩ := hbdd ({e m} : Set (ℝ × ℝ)) isCompact_singleton (by
        intro p hp
        rw [Set.mem_singleton_iff] at hp
        rw [hp]
        exact heU m)
      exact ⟨C, fun n => hC n (e m) rfl⟩
    obtain ⟨φ, hφ, hlim⟩ := diag_extract_fin_aux hcol
    have hpt : ∀ p ∈ U, ∃ L : Fin k → ℝ,
        Filter.Tendsto (fun n => F (φ n) p) Filter.atTop (nhds L) := by
      intro p hp
      obtain ⟨r, hrpos, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
      have hKsub : Metric.closedBall p (r / 2) ⊆ U := by
        intro q hq
        exact hrU (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hq) (by linarith)))
      refine exists_tendsto_of_dense_equicont_fin_aux (e := e) (G := fun n q => F (φ n) q)
        (K := Metric.closedBall p (r / 2)) (p := p) ?_ ?_ ?_
      · rw [Metric.mem_closure_iff]
        intro η hη
        have hηpos : 0 < min η (r / 2) := lt_min hη (by linarith)
        obtain ⟨d, hd, hdp⟩ := Metric.mem_closure_iff.mp (hedense p hp) (min η (r / 2)) hηpos
        refine ⟨d, ⟨hd, ?_⟩, lt_of_lt_of_le hdp (min_le_left _ _)⟩
        refine Metric.mem_closedBall.mpr (le_of_lt ?_)
        rw [dist_comm]
        exact lt_of_lt_of_le hdp (min_le_right _ _)
      · intro m
        exact hlim m
      · intro ε hε
        obtain ⟨δ, hδpos, hδ⟩ :=
          heqc (Metric.closedBall p (r / 2)) (isCompact_closedBall p (r / 2)) hKsub ε hε
        refine ⟨δ / 2, by linarith, fun n q hq hqp => ?_⟩
        exact le_of_lt (hδ (φ n) q hq p (Metric.mem_closedBall_self (by linarith))
          (lt_of_le_of_lt hqp (by linarith)))
    let f : ℝ × ℝ → (Fin k → ℝ) := fun p =>
      if hp : p ∈ U then Classical.choose (hpt p hp) else 0
    have hf : ∀ p : ℝ × ℝ, p ∈ U →
        Filter.Tendsto (fun n => F (φ n) p) Filter.atTop (nhds (f p)) := by
      intro p hp
      have hfp : f p = Classical.choose (hpt p hp) := by
        show (if hp : p ∈ U then Classical.choose (hpt p hp) else 0)
            = Classical.choose (hpt p hp)
        exact dif_pos hp
      rw [hfp]
      exact Classical.choose_spec (hpt p hp)
    refine ⟨φ, hφ, f, ?_⟩
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    refine tendstoUniformlyOn_of_pointwise_of_equicont_aux (F := fun n p => F (φ n) p) (f := f)
      hK (fun p hp => hf p (hKU hp)) ?_
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := heqc K hK hKU ε hε
    exact ⟨δ, hδpos, fun n p hp q hq hpq => hδ (φ n) p hp q hq hpq⟩

end Work.FTS.StrongEps.LocUnif
