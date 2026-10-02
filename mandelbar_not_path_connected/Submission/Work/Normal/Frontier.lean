import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.escapeRadius
import Submission.Work.Normal.FilledJulia
import Submission.Work.Normal.montel_locallyBounded
import Submission.Work.Normal.exists_const_subseq_or_tendsto_atTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Julia set of a polynomial map is the boundary of the filled Julia set

For a polynomial map `f` of degree `d ≥ 2` we prove `JuliaSet f = frontier (FilledJuliaSet f)`.
This is the structural result that turns the Julia set into a geometric object: it gives `J`
closed and compact, `J ≠ ∅`, the backward invariance of `J` (via the elementary invariances of
`K`, `K°` and `Kᶜ`) and the density of iterated preimages.

The two inclusions are:

* `J ⊆ ∂K`: the Fatou set contains `K°` (the iterates are bounded by the escape radius there, so
  Montel's locally bounded principle applies) and contains `Kᶜ` (there the iterates escape locally
  uniformly); hence no Fatou point lies on `∂K`.
* `∂K ⊆ J`: if the iterates were normal on a neighbourhood `U` of a point of `∂K`, extract a
  subsequence converging locally uniformly to `g` (holomorphic) or to `∞`.  An escaping point
  `y ∈ U` (which exists because `z` lies in the closure of `Kᶜ`) rules out a holomorphic limit,
  since the orbit of `y` tends to `∞` along *every* subsequence; and a point of `U ∩ K` rules out
  the limit `∞`, since the iterates stay bounded by the escape radius on `K`.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial

/-- If the iterates escape to `∞` locally uniformly, then the iterate family is normal (with the
`∞` alternative): every sequence of iterates has a subsequence whose indices are either bounded,
giving a constant subsequence, or tend to `∞`, giving again the escape limit. -/
theorem isNormalFamily_iterateFamily_of_tendstoAtTop {f : ℂ → ℂ} {U : Set ℂ}
    (h : TendstoLocallyUniformlyAtTop (fun n : ℕ => f^[n]) U) :
    IsNormalFamily (iterateFamily f) U := by
  intro u hu
  choose k hk using fun n => hu n
  rcases exists_const_subseq_or_tendsto_atTop k with ⟨m, hm⟩ | hktop
  · choose next hnext using fun N => hm N
    let φ : ℕ → ℕ := fun n => Nat.rec (next 0) (fun _ prev => next prev) n
    have hφmono : StrictMono φ := strictMono_nat_of_lt_succ fun n => (hnext (φ n)).1
    have hφk : ∀ n, k (φ n) = m := by
      intro n
      induction n with
      | zero => exact (hnext 0).2
      | succ n _ => exact (hnext (φ n)).2
    have hconst : ∀ n, u (φ n) = fun z => f^[m] z := by
      intro n
      rw [← hk (φ n), hφk n]
    refine ⟨φ, hφmono, Or.inl ⟨fun z => f^[m] z, ?_⟩⟩
    rw [show (fun n => u (φ n)) = (fun _ : ℕ => fun z => f^[m] z) from funext hconst]
    intro e he x _
    exact ⟨univ, univ_mem, Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity he⟩
  · refine ⟨id, strictMono_id, Or.inr ?_⟩
    intro K hKU hK R
    obtain ⟨N, hN⟩ := h K hKU hK R
    obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hktop N)
    refine ⟨J, fun j hj z hz => ?_⟩
    have h2 := hN (k j) (hJ j hj) z hz
    simpa [hk j] using h2

/-- **The Julia set of a polynomial map of degree at least two is the boundary of its filled
Julia set.** -/
theorem juliaSet_eq_frontier {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : JuliaSet f = frontier (FilledJuliaSet f) := by
  obtain ⟨P, hPd, hPf⟩ := hf
  obtain ⟨R, hR2, hR, hKeq, hesc, hKcl, -, -⟩ := escapeRadius hd ⟨P, hPd, hPf⟩
  have hfdiff : Differentiable ℂ f := by
    rw [show f = fun z => P.eval z from funext fun z => hPf z]
    exact Polynomial.differentiable P
  -- (1) the interior of `K` lies in the Fatou set
  have hKint : interior (FilledJuliaSet f) ⊆ FatouSet f := by
    intro z hz
    obtain ⟨t, htK, hto, hzt⟩ := mem_interior.mp hz
    obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.mp hto z hzt
    have hBsub : Metric.ball z r ⊆ FilledJuliaSet f := hrt.trans htK
    have hbounded : IsLocallyBoundedOn (iterateFamily f) (Metric.ball z r) := by
      intro K hKB hK
      refine ⟨R, fun g hg y hy => ?_⟩
      rcases hg with ⟨n, rfl⟩
      have hyK : y ∈ FilledJuliaSet f := hBsub (hKB hy)
      rw [hKeq] at hyK
      exact hyK n
    exact fatouSet_of_mem_nhds (Metric.ball_mem_nhds z hr) Metric.isOpen_ball
      (montel_locallyBounded Metric.isOpen_ball (fun g hg => by
        rcases hg with ⟨n, rfl⟩
        exact (hfdiff.iterate n).differentiableOn) hbounded)
  -- (2) the complement of `K` lies in the Fatou set
  have hKcompl : (FilledJuliaSet f)ᶜ ⊆ FatouSet f := by
    intro z hz
    obtain ⟨U, hU, hUo, hUesc⟩ := hesc z hz
    exact fatouSet_of_mem_nhds hU hUo (isNormalFamily_iterateFamily_of_tendstoAtTop hUesc)
  -- (3) `J ⊆ ∂K`
  have hsub : JuliaSet f ⊆ frontier (FilledJuliaSet f) := by
    intro z hz
    have hzK : z ∈ FilledJuliaSet f := by
      by_contra h
      exact hz (hKcompl h)
    rw [mem_frontier_iff_notMem_interior hzK]
    exact fun h => hz (hKint h)
  -- (4) `∂K ⊆ J`
  have hsup : frontier (FilledJuliaSet f) ⊆ JuliaSet f := by
    intro z hz hzF
    have hzK : z ∈ FilledJuliaSet f := by
      rw [← hKcl.closure_eq]
      exact frontier_subset_closure hz
    have hznint : z ∉ interior (FilledJuliaSet f) := (mem_frontier_iff_notMem_interior hzK).1 hz
    obtain ⟨U, hU, hUo, hnorm⟩ := hzF
    have hzU : z ∈ U := mem_of_mem_nhds hU
    -- an escaping point in `U`
    have hexists : ∃ y ∈ U, y ∉ FilledJuliaSet f := by
      by_contra h
      push_neg at h
      exact hznint (interior_maximal h hUo hzU)
    obtain ⟨y, hyU, hyK⟩ := hexists
    obtain ⟨φ, hφ, hlim | hlim⟩ := hnorm (fun n => f^[n]) (fun n => apply_mem_iterateFamily f n)
    · -- a holomorphic limit is impossible
      obtain ⟨g, hg⟩ := hlim
      have hyesc : ∀ R' : ℝ, ∃ N : ℕ, ∀ n ≥ N, R' ≤ ‖f^[n] y‖ := by
        intro R'
        obtain ⟨V, hV, hVo, hVesc⟩ := hesc y hyK
        obtain ⟨N, hN⟩ := hVesc {y} (by simpa using mem_of_mem_nhds hV) isCompact_singleton R'
        exact ⟨N, fun n hn => hN n hn y (mem_singleton y)⟩
      have hconv : Filter.Tendsto (fun n => f^[φ n] y) Filter.atTop (nhds (g y)) :=
        hg.tendsto_at hyU
      obtain ⟨N, hN⟩ := hyesc (‖g y‖ + 1)
      have hbound : ∀ᶠ n in Filter.atTop, ‖f^[φ n] y‖ < ‖g y‖ + 1 := by
        have hcw : Filter.Tendsto (fun n => ‖f^[φ n] y‖) Filter.atTop (nhds (‖g y‖)) :=
          (continuous_norm.tendsto (g y)).comp hconv
        filter_upwards [Metric.tendsto_nhds.1 hcw 1 one_pos] with n hn
        rw [Real.dist_eq] at hn
        linarith [(abs_lt.1 hn).2]
      have hge : ∀ᶠ n in Filter.atTop, N ≤ n := Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩
      obtain ⟨n, hnlt, hnge⟩ := (hbound.and hge).exists
      have hle : N ≤ φ n := le_trans hnge (hφ.id_le n)
      linarith [hN (φ n) hle]
    · -- the limit `∞` is impossible because `z ∈ K`
      obtain ⟨N, hN⟩ := hlim {z} (by simpa using hzU) isCompact_singleton (R + 1)
      have hKbdd : ‖f^[φ (φ N)] z‖ ≤ R := by
        have hmem : z ∈ FilledJuliaSet f := hzK
        rw [hKeq] at hmem
        exact hmem (φ (φ N))
      have := hN (φ N) (hφ.id_le N) z (mem_singleton z)
      linarith
  exact Subset.antisymm hsub hsup

end Work.Normal
