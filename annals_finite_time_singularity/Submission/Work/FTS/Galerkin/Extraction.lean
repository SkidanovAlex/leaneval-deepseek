/-
# The GALERKIN area: the compactness extraction (audit §4 N6, step 5)

This module *builds* the extraction that the compactness input of the Galerkin argument needs, from
two a-priori estimates about the sequence of Galerkin profiles `G n`:

* **uniform local bounds** (`hbdd`) — supplied by the paper's `Linf_H2` from the uniform
  `ℋ⁴`-bounds (see `Compactness.lean`);
* **uniform local Lipschitz bounds** (`hlip`) — supplied by the `ℋ⁴`-bounds on the first
  derivatives (`D_z`, `D_θ`) and by the uniform `ℋ³`-bound on `∂_τ`.

The proof is the classical one: a diagonal extraction on a countable dense subset of the slab
(`exists_strictMono_forall_tendsto_of_boundedCols`, reducing to
`Compactness/exists_strictMono_forall_tendsto_of_bounded.lean` by normalising the columns), then the
extension of the limit to the whole slab by equicontinuity
(`exists_tendsto_of_tendsto_dense`), then the uniform convergence on each compact set by the
`ε`/`3` argument with a finite `δ`-net (`isCompact` ⟹ totally bounded).

Nothing here mentions the PDE: all the analysis is in the two estimate hypotheses.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.Galerkin.Basic
import Submission.Work.FTS.Galerkin.Compactness.exists_strictMono_forall_tendsto_of_bounded

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

set_option autoImplicit false

/-! ## Diagonal extraction with per-column bounds -/

/-- **Diagonal extraction, per-column bounds.**  A sequence of real sequences that is bounded
column by column has a subsequence converging at every second index.  (The uniform-bound version is
`Work.FTS.Galerkin.Compactness.exists_strictMono_forall_tendsto_of_bounded`; normalising each column
by its bound reduces to it.) -/
theorem exists_strictMono_forall_tendsto_of_boundedCols {u : ℕ → ℕ → ℝ}
    (h : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, |u n k| ≤ C) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ k : ℕ, ∃ L : ℝ,
      Filter.Tendsto (fun n => u (ψ n) k) Filter.atTop (nhds L) := by
  choose C hC using h
  set D : ℕ → ℝ := fun k => |C k| + 1 with hDdef
  have hDpos : ∀ k, 0 < D k := by intro k; rw [hDdef]; positivity
  have hb : ∀ n k : ℕ, |u n k / D k| ≤ 1 := by
    intro n k
    have h1 : |u n k| ≤ D k := by
      have h2 := hC k n
      rw [hDdef]
      linarith [le_abs_self (C k)]
    rw [abs_div, abs_of_pos (hDpos k), div_le_one (hDpos k)]
    exact h1
  obtain ⟨ψ, hψ, hlim⟩ :=
    Compactness.exists_strictMono_forall_tendsto_of_bounded
      (u := fun n k => u n k / D k) (C := 1) hb
  refine ⟨ψ, hψ, fun k => ?_⟩
  obtain ⟨L, hL⟩ := hlim k
  refine ⟨L * D k, ?_⟩
  have h2 : Filter.Tendsto (fun n => u (ψ n) k / D k * D k) Filter.atTop (nhds (L * D k)) :=
    hL.mul_const (D k)
  have hfun : (fun n => u (ψ n) k / D k * D k) = fun n => u (ψ n) k := by
    funext n
    exact div_mul_cancel₀ _ (ne_of_gt (hDpos k))
  rwa [hfun] at h2

/-! ## Extension of the limit by equicontinuity -/

/-- **A uniformly Lipschitz sequence converging on a dense set converges everywhere.**  If `G n`
converges at every point of a dense `D`, if `p` is a point of the closure of `D ∩ U` and if the
family is Lipschitz on `U` with a constant uniform in `n`, then `G n p` converges. -/
theorem exists_tendsto_of_tendsto_dense {X : Type*} [PseudoMetricSpace X]
    {G : ℕ → X → ℝ} {D U : Set X} {p : X} (hp : p ∈ closure (D ∩ U)) {L : ℝ}
    (hconv : ∀ d ∈ D, ∃ l : ℝ, Filter.Tendsto (fun n => G n d) Filter.atTop (nhds l))
    (hlip : ∀ (n : ℕ) {q : X}, q ∈ U → |G n q - G n p| ≤ L * dist q p) :
    ∃ l : ℝ, Filter.Tendsto (fun n => G n p) Filter.atTop (nhds l) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hLpos : 0 < |L| + 1 := by positivity
  have hδpos : 0 < ε / (8 * (|L| + 1)) := by positivity
  obtain ⟨d, hd, hdp⟩ := Metric.mem_closure_iff.mp hp _ hδpos
  rcases hd with ⟨hdD, hdU⟩
  obtain ⟨l, hl⟩ := hconv d hdD
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hl (ε / 4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hdp' : dist d p < ε / (8 * (|L| + 1)) := by rwa [dist_comm] at hdp
  have hmd : |G m d - G m p| ≤ L * dist d p := hlip m hdU
  have hnd : |G n d - G n p| ≤ L * dist d p := hlip n hdU
  have hLd : L * dist d p ≤ ε / 4 := by
    have h1 : L * dist d p ≤ |L| * dist d p :=
      mul_le_mul_of_nonneg_right (le_abs_self L) dist_nonneg
    have h2 : |L| * dist d p ≤ (|L| + 1) * dist d p :=
      mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    have h3 : (|L| + 1) * dist d p < (|L| + 1) * (ε / (8 * (|L| + 1))) :=
      mul_lt_mul_of_pos_left hdp' hLpos
    have h4 : (|L| + 1) * (ε / (8 * (|L| + 1))) = ε / 8 := by
      field_simp
    linarith [h1, h2, h3, h4]
  have hmid : dist (G m d) (G n d) < ε / 2 := by
    have h1 : dist (G m d) l < ε / 4 := hN m hm
    have h2 : dist (G n d) l < ε / 4 := hN n hn
    calc dist (G m d) (G n d) ≤ dist (G m d) l + dist l (G n d) := dist_triangle _ _ _
      _ = dist (G m d) l + dist (G n d) l := by rw [dist_comm l (G n d)]
      _ < ε / 4 + ε / 4 := by linarith
      _ = ε / 2 := by ring
  calc dist (G m p) (G n p)
      ≤ dist (G m p) (G m d) + dist (G m d) (G n d) + dist (G n d) (G n p) := by
        have := dist_triangle4 (G m p) (G m d) (G n d) (G n p)
        linarith [dist_comm (G m p) (G m d)]
    _ = |G m d - G m p| + dist (G m d) (G n d) + |G n d - G n p| := by
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq]
        rw [abs_sub_comm (G m d) (G m p), abs_sub_comm (G n d) (G n p)]
    _ < ε / 4 + ε / 2 + ε / 4 := by
        have h1 : |G m d - G m p| ≤ L * dist d p := hmd
        have h2 : |G n d - G n p| ≤ L * dist d p := hnd
        linarith [hmid, hLd, h1, h2]
    _ = ε := by ring

/-! ## The extraction on the slab -/

/-- **The compactness extraction on the fake-time slab.**  Let `G n` be a sequence of real
functions on `ℝ³`, `e` a countable sequence of points of the slab whose range is dense in the slab.
If on every compact subset `K` of the slab the sequence is uniformly bounded, and is uniformly
Lipschitz *near* `K` (for pairs at distance at most `1`), then a subsequence converges locally
uniformly on the slab.

The two estimate hypotheses are what the a-priori estimates supply: uniform bounds from the paper's
`Linf_H2` and the uniform `ℋ⁴`-bounds, and the Lipschitz bounds from the `ℋ⁴`-bounds on the first
derivatives (in `z`, `θ`) and the uniform `ℋ³`-bound on `∂_τ`. -/
theorem exists_subseq_convLocUnif {G : ℕ → (ℝ × ℝ × ℝ) → ℝ} {e : ℕ → ℝ × ℝ × ℝ}
    (he : ∀ k : ℕ, e k ∈ Slab)
    (hdense : ∀ p ∈ Slab, p ∈ closure (Set.range e))
    (hbdd : ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Slab →
      ∃ C : ℝ, ∀ n : ℕ, ∀ p ∈ K, |G n p| ≤ C)
    (hlip : ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Slab →
      ∃ L : ℝ, ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ Slab, dist p q ≤ 1 →
        |G n p - G n q| ≤ L * dist p q) :
    ∃ (ψ : ℕ → ℕ) (g : (ℝ × ℝ × ℝ) → ℝ), StrictMono ψ ∧
      ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Slab →
        TendstoUniformlyOn (fun n p => G (ψ n) p) g atTop K := by
  classical
  -- per-column bounds on the dense sequence
  have hcol : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, |G n (e k)| ≤ C := by
    intro k
    have hsub : ({e k} : Set (ℝ × ℝ × ℝ)) ⊆ Slab := by
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact he k
    obtain ⟨C, hC⟩ := hbdd {e k} isCompact_singleton hsub
    exact ⟨C, fun n => hC n (e k) rfl⟩
  obtain ⟨ψ, hψ, hlim⟩ := exists_strictMono_forall_tendsto_of_boundedCols hcol
  -- pointwise limits
  have hpt : ∀ p ∈ Slab, ∃ l : ℝ, Filter.Tendsto (fun n => G (ψ n) p) Filter.atTop (nhds l) := by
    intro p hp
    obtain ⟨q, hq, hqp⟩ := Metric.mem_closure_iff.mp (hdense p hp) 1 one_pos
    obtain ⟨k, rfl⟩ := hq
    have hkp : dist p (e k) < 1 := hqp
    set Kp : Set (ℝ × ℝ × ℝ) := Metric.closedBall p 1 ∩ Slab with hKp
    have hKpcomp : IsCompact Kp := by
      rw [hKp]
      exact (isCompact_closedBall p 1).inter_right isClosed_Slab
    have hKpsub : Kp ⊆ Slab := fun q hq => hq.2
    obtain ⟨L, hL⟩ := hlip Kp hKpcomp hKpsub
    have hpKp : p ∈ Kp := by rw [hKp]; exact ⟨by simp, hp⟩
    refine exists_tendsto_of_tendsto_dense (D := Set.range e) (U := Kp) (L := L) ?_ ?_ ?_
    · rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨q, hq, hqp⟩ := Metric.mem_closure_iff.mp (hdense p hp) (min ε 1) (by positivity)
      obtain ⟨k', rfl⟩ := hq
      refine ⟨e k', ⟨⟨k', rfl⟩, ?_⟩, lt_of_lt_of_le hqp (min_le_left _ _)⟩
      rw [hKp]
      refine ⟨?_, he k'⟩
      rw [Metric.mem_closedBall, dist_comm]
      exact le_of_lt (lt_of_lt_of_le hqp (min_le_right _ _))
    · intro d hd
      obtain ⟨k', rfl⟩ := hd
      exact hlim k'
    · intro n q hq
      exact hL (ψ n) q hq p hp (Metric.mem_closedBall.mp hq.1)
  -- the limit function
  set g : (ℝ × ℝ × ℝ) → ℝ := fun p => if h : p ∈ Slab then Classical.choose (hpt p h) else 0
    with hgdef
  have hg : ∀ p ∈ Slab, Filter.Tendsto (fun n => G (ψ n) p) Filter.atTop (nhds (g p)) := by
    intro p hp
    have hgp : g p = Classical.choose (hpt p hp) := by
      rw [hgdef]
      exact dif_pos hp
    rw [hgp]
    exact Classical.choose_spec (hpt p hp)
  refine ⟨ψ, g, hψ, fun K hK hKsub => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨L, hL⟩ := hlip K hK hKsub
  have hLpos : 0 < |L| + 1 := by positivity
  set δ : ℝ := min (ε / (12 * (|L| + 1))) (1 / 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (by positivity) (by norm_num)
  have hδhalf : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_right _ _
  have hδeps : δ ≤ ε / (12 * (|L| + 1)) := by rw [hδdef]; exact min_le_left _ _
  obtain ⟨T, hTK, hTfin, hTcov⟩ :=
    Metric.finite_approx_of_totallyBounded hK.totallyBounded δ hδpos
  haveI : Fintype {t : ℝ × ℝ × ℝ // t ∈ T} := hTfin.fintype
  have hchoice : ∀ t : {t : ℝ × ℝ × ℝ // t ∈ T}, ∃ d ∈ Set.range e, dist (t : ℝ × ℝ × ℝ) d < δ := by
    intro t
    have ht : (t : ℝ × ℝ × ℝ) ∈ closure (Set.range e) := hdense t.1 (hKsub (hTK t.2))
    exact Metric.mem_closure_iff.mp ht δ hδpos
  choose d hdmem hdd using hchoice
  have hdSlab : ∀ t : {t : ℝ × ℝ × ℝ // t ∈ T}, d t ∈ Slab := by
    intro t
    obtain ⟨k', hk'⟩ := hdmem t
    rw [← hk']
    exact he k'
  -- the Lipschitz bound for the family on the relevant pairs
  have hLip : ∀ {p : ℝ × ℝ × ℝ} (hp : p ∈ K) (t : ℝ × ℝ × ℝ) (ht : t ∈ T), dist p t < δ →
      ∀ n : ℕ, |G (ψ n) p - G (ψ n) (d ⟨t, ht⟩)| ≤ L * dist p (d ⟨t, ht⟩) := by
    intro p hp t ht hpt n
    refine hL (ψ n) p hp (d ⟨t, ht⟩) (hdSlab ⟨t, ht⟩) ?_
    have h1 : dist p (d ⟨t, ht⟩) ≤ dist p t + dist t (d ⟨t, ht⟩) := dist_triangle _ _ _
    have h3 : dist t (d ⟨t, ht⟩) < δ := hdd ⟨t, ht⟩
    have h4 : 2 * δ ≤ 1 := by linarith
    linarith
  -- the Lipschitz bound for the limit function
  have hglip : ∀ {p : ℝ × ℝ × ℝ} (hp : p ∈ K) (t : ℝ × ℝ × ℝ) (ht : t ∈ T), dist p t < δ →
      |g (d ⟨t, ht⟩) - g p| ≤ L * dist (d ⟨t, ht⟩) p := by
    intro p hp t ht hpt
    have h1 : Filter.Tendsto (fun n => G (ψ n) (d ⟨t, ht⟩)) Filter.atTop
        (nhds (g (d ⟨t, ht⟩))) := hg (d ⟨t, ht⟩) (hdSlab ⟨t, ht⟩)
    have h2 : Filter.Tendsto (fun n => G (ψ n) p) Filter.atTop (nhds (g p)) := hg p (hKsub hp)
    have h3 : Filter.Tendsto (fun n => |G (ψ n) (d ⟨t, ht⟩) - G (ψ n) p|) Filter.atTop
        (nhds (|g (d ⟨t, ht⟩) - g p|)) := (h1.sub h2).abs
    refine le_of_tendsto_of_tendsto' h3 tendsto_const_nhds (fun n => ?_)
    rw [abs_sub_comm, dist_comm]
    exact hLip hp t ht hpt n
  -- the eventual closeness at the chosen points
  have hev : ∀ᶠ n in Filter.atTop,
      ∀ t : {t : ℝ × ℝ × ℝ // t ∈ T}, |G (ψ n) (d t) - g (d t)| < ε / 3 := by
    rw [Filter.eventually_all]
    intro t
    obtain ⟨k', hk'⟩ := hdmem t
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hg (e k') (he k')) (ε / 3) (by positivity)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [hk'] at h
    simpa [Real.dist_eq] using h
  filter_upwards [hev] with n hn x hx
  obtain ⟨t, htT, hxt⟩ : ∃ t ∈ T, x ∈ Metric.ball t δ := by
    rcases Set.mem_iUnion.mp (hTcov hx) with ⟨t, ht⟩
    rcases Set.mem_iUnion.mp ht with ⟨htT, hxt⟩
    exact ⟨t, htT, hxt⟩
  have hxtδ : dist x t < δ := Metric.mem_ball.mp hxt
  have hxa : |G (ψ n) x - G (ψ n) (d ⟨t, htT⟩)| ≤ L * dist x (d ⟨t, htT⟩) :=
    hLip hx t htT hxtδ n
  have hxb := hn ⟨t, htT⟩
  have hxc : |g (d ⟨t, htT⟩) - g x| ≤ L * dist x (d ⟨t, htT⟩) := by
    have h := hglip hx t htT hxtδ
    rwa [dist_comm] at h
  have hdist : dist x (d ⟨t, htT⟩) < 2 * δ := by
    have h1 : dist x (d ⟨t, htT⟩) ≤ dist x t + dist t (d ⟨t, htT⟩) := dist_triangle _ _ _
    have h3 : dist t (d ⟨t, htT⟩) < δ := hdd ⟨t, htT⟩
    linarith
  have hLd : L * dist x (d ⟨t, htT⟩) ≤ ε / 3 := by
    have h6 : L * dist x (d ⟨t, htT⟩) ≤ (|L| + 1) * dist x (d ⟨t, htT⟩) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self L]) dist_nonneg
    have h7 : (|L| + 1) * dist x (d ⟨t, htT⟩) < (|L| + 1) * (2 * δ) :=
      mul_lt_mul_of_pos_left hdist hLpos
    have h8 : (|L| + 1) * (2 * δ) ≤ ε / 3 := by
      have h9 : 2 * δ ≤ ε / (6 * (|L| + 1)) := by
        calc 2 * δ ≤ 2 * (ε / (12 * (|L| + 1))) := by linarith
          _ = ε / (6 * (|L| + 1)) := by field_simp; ring
      calc (|L| + 1) * (2 * δ) ≤ (|L| + 1) * (ε / (6 * (|L| + 1))) :=
            mul_le_mul_of_nonneg_left h9 hLpos.le
        _ = ε / 6 := by field_simp
        _ ≤ ε / 3 := by linarith
    linarith
  have htri : |G (ψ n) x - g x|
      ≤ |G (ψ n) x - G (ψ n) (d ⟨t, htT⟩)| + |G (ψ n) (d ⟨t, htT⟩) - g (d ⟨t, htT⟩)|
        + |g (d ⟨t, htT⟩) - g x| := by
    have h1 : (G (ψ n) x - g x)
        = (G (ψ n) x - G (ψ n) (d ⟨t, htT⟩)) + (G (ψ n) (d ⟨t, htT⟩) - g (d ⟨t, htT⟩))
          + (g (d ⟨t, htT⟩) - g x) := by ring
    rw [h1]
    have h2 := abs_add_le ((G (ψ n) x - G (ψ n) (d ⟨t, htT⟩))
      + (G (ψ n) (d ⟨t, htT⟩) - g (d ⟨t, htT⟩))) (g (d ⟨t, htT⟩) - g x)
    have h3 := abs_add_le (G (ψ n) x - G (ψ n) (d ⟨t, htT⟩))
      (G (ψ n) (d ⟨t, htT⟩) - g (d ⟨t, htT⟩))
    have h5 := abs_nonneg (G (ψ n) x - G (ψ n) (d ⟨t, htT⟩))
    have h6 := abs_nonneg (G (ψ n) (d ⟨t, htT⟩) - g (d ⟨t, htT⟩))
    linarith
  have hfinal : |g x - G (ψ n) x| < ε := by
    rw [abs_sub_comm]
    exact lt_of_le_of_lt htri (by linarith [hxa, hxb, hxc, hLd])
  simpa only [Real.dist_eq] using hfinal

end Work.FTS.Galerkin
