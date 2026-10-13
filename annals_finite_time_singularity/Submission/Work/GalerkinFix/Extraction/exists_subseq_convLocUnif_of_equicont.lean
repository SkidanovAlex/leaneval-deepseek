/-
# The corrected compactness extraction: equicontinuity replaces Lipschitz

`Work.FTS.Galerkin.exists_subseq_convLocUnif` (`Submission/Work/FTS/Galerkin/Extraction.lean`)
extracts a locally uniformly convergent subsequence from a family of profiles that is uniformly
bounded *and uniformly Lipschitz* on every compact subset of the fake-time slab.  The a-priori
estimates of the paper do **not** give a uniform Lipschitz modulus (an `ℋ⁴`-ball contains profiles
`θ^s` with `α/20 < s < 1`, which are only `C^β` for `β < γ - 1 = α/10`), they give a uniform
*modulus of continuity*; see `Submission/Work/FTS/GalerkinFix/Equicont.lean`.

This module re-runs the extraction with the corrected input `Work.FTS.Galerkin.ProfileEquicont`
(the bundled N4+N5 equicontinuity field), verbatim the statement consumed by the corrected Galerkin
bundle `Work.FTS.Galerkin.DynInputs`.

The proof is the classical one, and the whole difference from the Lipschitz version is that the
`ε/3`-argument is driven by a modulus `δ(ε)` of the family instead of the bound `L·dist`:

1. **diagonal extraction** on the countable dense sequence `e` of the slab, using the uniform local
   bounds `hbdd` at each point `e k` (`Work.FTS.Galerkin.exists_strictMono_forall_tendsto_of_boundedCols`);
2. **pointwise limits on the slab** by the equicontinuous version of the "convergence on a dense set"
   lemma (`exists_tendsto_of_tendsto_dense_equicont`), applied on the compact neighbourhood
   `closedBall p 1 ∩ Slab` of `p`;
3. **uniform convergence on a compact `K`**: take a finite `δ/2`-net `T` of `K` (`K` is totally
   bounded), replace each net point by a nearby point of the dense sequence, and use the modulus of
   equicontinuity of the family for the first two terms and that of the limit for the third.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.GalerkinFix.Defs
import Submission.Work.FTS.Galerkin.Extraction

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.GalerkinFix.Extraction

/-! ## Convergence on a dense set, by equicontinuity

The equicontinuous replacement for `Work.FTS.Galerkin.exists_tendsto_of_tendsto_dense`: the
Lipschitz bound `L * dist q p` is replaced by an arbitrary uniform modulus of continuity of the
family at `p`. -/

/-- **A uniformly equicontinuous sequence converging on a dense set converges everywhere.**  If the
sequence `G n` converges at every point of `D`, if `p` is a point of the closure of `D ∩ U` and the
family is equicontinuous at `p` on `U`, uniformly in `n`, then `G n p` converges.  (No completeness
of the index is needed — this is the Cauchy criterion in `ℝ`.) -/
theorem exists_tendsto_of_tendsto_dense_equicont {X : Type*} [PseudoMetricSpace X]
    {G : ℕ → X → ℝ} {D U : Set X} {p : X} (hp : p ∈ closure (D ∩ U))
    (hconv : ∀ d ∈ D, ∃ l : ℝ, Filter.Tendsto (fun n => G n d) Filter.atTop (nhds l))
    (heq : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ q ∈ U, dist q p ≤ δ →
      |G n q - G n p| ≤ ε) :
    ∃ l : ℝ, Filter.Tendsto (fun n => G n p) Filter.atTop (nhds l) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := heq (ε / 4) (by linarith)
  obtain ⟨d, hd, hdp⟩ := Metric.mem_closure_iff.mp hp δ hδpos
  obtain ⟨hdD, hdU⟩ := hd
  obtain ⟨l, hl⟩ := hconv d hdD
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hl (ε / 4) (by linarith)
  have hdp' : dist d p < δ := by rwa [dist_comm] at hdp
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmd : dist (G m p) (G m d) ≤ ε / 4 := by
    rw [Real.dist_eq, abs_sub_comm]
    exact hδ m d hdU (le_of_lt hdp')
  have hnd : dist (G n d) (G n p) ≤ ε / 4 := by
    rw [Real.dist_eq]
    exact hδ n d hdU (le_of_lt hdp')
  have hmn : dist (G m d) (G n d) < ε / 2 := by
    have h1 : dist (G m d) (G n d) ≤ dist (G m d) l + dist l (G n d) := dist_triangle _ _ _
    have h2 : dist (G m d) l < ε / 4 := hN m hm
    have h3 : dist l (G n d) < ε / 4 := by rw [dist_comm]; exact hN n hn
    linarith
  calc dist (G m p) (G n p)
      ≤ dist (G m p) (G m d) + dist (G m d) (G n d) + dist (G n d) (G n p) := by
        have h := dist_triangle4 (G m p) (G m d) (G n d) (G n p)
        linarith
    _ < ε / 4 + ε / 2 + ε / 4 := by linarith
    _ = ε := by ring

/-! ## The extraction on the slab -/

/-- **The corrected compactness extraction on the fake-time slab.**  Let `G n` be a sequence of real
functions on `ℝ³` and `e` a countable sequence of points of the slab whose range is dense in the
slab.  If on every compact subset `K` of the slab the sequence is uniformly bounded (`hbdd`) and
uniformly *equicontinuous* on `K` (as a family, `heq`), then some subsequence converges locally
uniformly on the slab.

Both estimates are what the paper's a-priori bounds supply: uniform local bounds from `Linf_H2`
together with the uniform `ℋ⁴`-bounds (`Work.FTS.GalerkinFix.linf_of_HkNorm_two` and friends), and
uniform local equicontinuity from the Hölder embedding in the space variables and the uniform `ℋ³`
bound on `∂_τ` (`Work.FTS.GalerkinFix.profileEquicont_of_box`). -/
theorem exists_subseq_convLocUnif_of_equicont {G : ℕ → (ℝ × ℝ × ℝ) → ℝ} {e : ℕ → ℝ × ℝ × ℝ}
    (he : ∀ k : ℕ, e k ∈ Work.FTS.Galerkin.Slab)
    (hdense : ∀ p ∈ Work.FTS.Galerkin.Slab, p ∈ closure (Set.range e))
    (hbdd : Work.FTS.Galerkin.ProfileBdd G)
    (heq : Work.FTS.Galerkin.ProfileEquicont G) :
    ∃ (ψ : ℕ → ℕ) (g : (ℝ × ℝ × ℝ) → ℝ), StrictMono ψ ∧
      ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.Galerkin.Slab →
        TendstoUniformlyOn (fun n p => G (ψ n) p) g atTop K := by
  classical
  -- the uniform bounds at the points of the dense sequence
  have hcol : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, |G n (e k)| ≤ C := by
    intro k
    have hsub : ({e k} : Set (ℝ × ℝ × ℝ)) ⊆ Work.FTS.Galerkin.Slab := by
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact he k
    obtain ⟨C, hC⟩ := hbdd {e k} isCompact_singleton hsub
    exact ⟨C, fun n => hC n (e k) rfl⟩
  obtain ⟨ψ, hψ, hlim⟩ :=
    Work.FTS.Galerkin.exists_strictMono_forall_tendsto_of_boundedCols hcol
  -- pointwise limits on the slab
  have hpt : ∀ p ∈ Work.FTS.Galerkin.Slab, ∃ l : ℝ,
      Filter.Tendsto (fun n => G (ψ n) p) Filter.atTop (nhds l) := by
    intro p hp
    obtain ⟨q, hq, hqp⟩ := Metric.mem_closure_iff.mp (hdense p hp) 1 one_pos
    obtain ⟨k, rfl⟩ := hq
    have hkp : dist p (e k) < 1 := hqp
    set Kp : Set (ℝ × ℝ × ℝ) := Metric.closedBall p 1 ∩ Work.FTS.Galerkin.Slab with hKp
    have hKpcomp : IsCompact Kp := by
      rw [hKp]
      exact (isCompact_closedBall p 1).inter_right Work.FTS.Galerkin.isClosed_Slab
    have hKpsub : Kp ⊆ Work.FTS.Galerkin.Slab := fun q hq => hq.2
    refine exists_tendsto_of_tendsto_dense_equicont (G := fun n p => G (ψ n) p)
      (D := Set.range e) (U := Kp) ?_ ?_ ?_
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
    · intro ε hε
      obtain ⟨δ, hδpos, hδ⟩ := heq Kp hKpcomp hKpsub ε hε
      exact ⟨δ, hδpos, fun n q hq hqp => hδ (ψ n) q hq p hp hqp⟩
  -- the limit function
  set g : (ℝ × ℝ × ℝ) → ℝ :=
    fun p => if h : p ∈ Work.FTS.Galerkin.Slab then Classical.choose (hpt p h) else 0 with hgdef
  have hg : ∀ p ∈ Work.FTS.Galerkin.Slab,
      Filter.Tendsto (fun n => G (ψ n) p) Filter.atTop (nhds (g p)) := by
    intro p hp
    have hgp : g p = Classical.choose (hpt p hp) := by
      rw [hgdef]
      exact dif_pos hp
    rw [hgp]
    exact Classical.choose_spec (hpt p hp)
  refine ⟨ψ, g, hψ, fun K hK hKsub => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- the modulus of equicontinuity of the family on `K`
  obtain ⟨δ, hδpos, hδ⟩ := heq K hK hKsub (ε / 3) (by linarith)
  set δ₂ : ℝ := δ / 2 with hδ₂def
  have hδ₂pos : 0 < δ₂ := by rw [hδ₂def]; linarith
  -- a finite `δ/2`-net of `K`, pushed back to the dense sequence
  obtain ⟨T, hTK, hTfin, hTcov⟩ :=
    Metric.finite_approx_of_totallyBounded hK.totallyBounded δ₂ hδ₂pos
  haveI : Fintype {t : ℝ × ℝ × ℝ // t ∈ T} := hTfin.fintype
  have hchoice : ∀ t : {t : ℝ × ℝ × ℝ // t ∈ T},
      ∃ d ∈ Set.range e, dist (t : ℝ × ℝ × ℝ) d < δ₂ := by
    intro t
    have ht : (t : ℝ × ℝ × ℝ) ∈ closure (Set.range e) := hdense t.1 (hKsub (hTK t.2))
    exact Metric.mem_closure_iff.mp ht δ₂ hδ₂pos
  choose d hdmem hdd using hchoice
  have hdSlab : ∀ t : {t : ℝ × ℝ × ℝ // t ∈ T}, d t ∈ Work.FTS.Galerkin.Slab := by
    intro t
    obtain ⟨k', hk'⟩ := hdmem t
    rw [← hk']
    exact he k'
  -- eventual closeness at the net points
  have hev : ∀ᶠ n in Filter.atTop,
      ∀ t : {t : ℝ × ℝ × ℝ // t ∈ T}, |G (ψ n) (d t) - g (d t)| < ε / 3 := by
    rw [Filter.eventually_all]
    intro t
    obtain ⟨k', hk'⟩ := hdmem t
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hg (e k') (he k')) (ε / 3) (by linarith)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [hk'] at h
    simpa [Real.dist_eq] using h
  filter_upwards [hev] with n hn x hx
  obtain ⟨t, htT, hxt⟩ : ∃ t ∈ T, x ∈ Metric.ball t δ₂ := by
    rcases Set.mem_iUnion.mp (hTcov hx) with ⟨t, ht⟩
    rcases Set.mem_iUnion.mp ht with ⟨htT, hxt⟩
    exact ⟨t, htT, hxt⟩
  have hxtδ : dist x t < δ₂ := Metric.mem_ball.mp hxt
  have hxd : dist x (d ⟨t, htT⟩) < δ := by
    have h1 : dist x (d ⟨t, htT⟩) ≤ dist x t + dist t (d ⟨t, htT⟩) := dist_triangle _ _ _
    have h3 : dist t (d ⟨t, htT⟩) < δ / 2 := by
      rw [hδ₂def] at hdd
      exact hdd ⟨t, htT⟩
    have h2 : dist x t < δ / 2 := by rw [hδ₂def] at hxtδ; exact hxtδ
    linarith
  have hxa : |G (ψ n) x - G (ψ n) (d ⟨t, htT⟩)| ≤ ε / 3 :=
    hδ (ψ n) x hx (d ⟨t, htT⟩) (hdSlab ⟨t, htT⟩) (le_of_lt hxd)
  have hxb := hn ⟨t, htT⟩
  -- the limit function is equicontinuous too, by passing to the limit
  have hxc : |g (d ⟨t, htT⟩) - g x| ≤ ε / 3 := by
    have h1 : Filter.Tendsto (fun n => G (ψ n) (d ⟨t, htT⟩)) Filter.atTop
        (nhds (g (d ⟨t, htT⟩))) := hg (d ⟨t, htT⟩) (hdSlab ⟨t, htT⟩)
    have h2 : Filter.Tendsto (fun n => G (ψ n) x) Filter.atTop (nhds (g x)) := hg x (hKsub hx)
    have h3 : Filter.Tendsto (fun n => |G (ψ n) (d ⟨t, htT⟩) - G (ψ n) x|) Filter.atTop
        (nhds (|g (d ⟨t, htT⟩) - g x|)) := (h1.sub h2).abs
    refine le_of_tendsto_of_tendsto' h3 tendsto_const_nhds (fun n => ?_)
    rw [abs_sub_comm]
    exact hδ (ψ n) x hx (d ⟨t, htT⟩) (hdSlab ⟨t, htT⟩) (le_of_lt hxd)
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
    exact lt_of_le_of_lt htri (by linarith [hxa, hxb, hxc])
  simpa only [Real.dist_eq] using hfinal

end Work.GalerkinFix.Extraction
