import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.EndDefs
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.germC_diff_ne
import Submission.Work.EQ.germC_W_coord
import Submission.Work.EQ.rational_germ_of_eventually_eq_comp
import Submission.Work.EQ.cycle_ends_principal
import Submission.Work.EQ.cycle_trace_meromorphic
import Submission.Work.EQ.rational_of_meromorphic_trace

/-! # `rational_of_compact_cycle`: a compact regular cycle forces a rational germ

**Route (the fibre trace, `Submission/Work/EQ/DESIGN_CCM.md`).**  The old `compact_cycle_model`
(Koenigs curve of an `A₂` end) is retired: puncture orbits of `S` accumulate at *both* ends, so
no `A₂` end chart exists.  Instead, let

`Fib u = {q ∈ S : ψ₁ q = u}`,  `G u = ∑_{q ∈ Fib u} W(q)`,  `W(q) = y/(x - a/2)` of `q.1 0`.

* `cycle_ends_principal`: near `0` every `q ∈ Fib u` has `q.1 0 = germC u`, so `W(q) = h (λu)`;
  near `∞` every `q ∈ Fib u` has `q.1 0 = ugermC (c/u)`, so `W(q) = -h (c/u)` is bounded.
* `cycle_trace_meromorphic`: `Fib u` is finite, has a common size `n ≥ 1` off a discrete set and
  size `≤ n` everywhere, and `G` is meromorphic on `ℂ*`.
* Hence `G =ᶠ[𝓝[≠] u] n · h(λ·)` near `0` and `|G| ≤ n·sup|h|` near `∞`; by
  `rational_of_meromorphic_trace`, `n · h(λ·)` is a rational germ, and
  `rational_germ_of_eventually_eq_comp` descends to `h`.

The three interface lemmas are proved elsewhere in this workspace
(`Submission/Work/EQ/cycle_ends_principal.lean`, `cycle_trace_meromorphic.lean`,
`rational_of_meromorphic_trace.lean`). -/

namespace Work.EQ

open Filter _root_.Topology

/-- routine: `W = h(λu)` on the stable germ near `0` (off `0`). -/
theorem W_germC_near {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < δ →
      (germC a h u).2 / ((germC a h u).1 - ((a / 2 : ℝ) : ℂ)) = h ((eqLam a : ℂ) * u) := by
  obtain ⟨ρ, hρ, han, h0, -⟩ := germC_facts ha0 ha1 hh
  obtain ⟨δ, hδ, hdiff⟩ := germC_diff_ne ha0 ha1 hh
  have hcont : ContinuousAt (fun u => (germC a h u).1 - ((a / 2 : ℝ) : ℂ)) 0 :=
    ((han 0 (Metric.mem_ball_self hρ)).continuousAt.fst).sub continuousAt_const
  have hval : (germC a h 0).1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by
    rw [h0]; intro hc
    have : ((-1 / 2 - a / 2 : ℝ) : ℂ) = 0 := by push_cast at hc ⊢; linear_combination hc
    have : (-1 / 2 - a / 2 : ℝ) = 0 := by exact_mod_cast this
    linarith
  obtain ⟨δ', hδ', hne⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hval)
  refine ⟨min δ δ', lt_min hδ hδ', fun u hu hlt => ?_⟩
  have hden : (germC a h u).1 - ((a / 2 : ℝ) : ℂ) ≠ 0 :=
    hne (by simpa [dist_eq_norm] using lt_of_lt_of_le hlt (min_le_right _ _))
  have hsl : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 u ≠ 0 := by
    rw [dslope_of_ne _ hu, slope_def_field]
    have h00 : h ((eqLam a : ℂ) * 0) - h 0 = 0 := by simp
    rw [h00, sub_zero, sub_zero]
    exact div_ne_zero ((hdiff u (by simpa using lt_of_lt_of_le hlt (min_le_left _ _)) hu).1) hu
  rw [germC_snd_eq_h_mul hh.2.2.1 hsl, mul_div_assoc, div_self hden, mul_one]

/-- routine: `W = -h v` on the unstable germ is bounded near `0`. -/
theorem W_ugermC_bdd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ B : ℝ, 0 < δ ∧ ∀ v : ℂ, ‖v‖ < δ →
      ‖(ugermC a h v).2 / ((ugermC a h v).1 - ((a / 2 : ℝ) : ℂ))‖ ≤ B := by
  have hcont : ContinuousAt h 0 := (hh.2.1 0 (Metric.mem_ball_self hh.1)).continuousAt
  have h00 : h 0 = 0 := hh.2.2.1
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  refine ⟨δ, 1, hδ, fun v hv => ?_⟩
  have hbv : ‖h v‖ < 1 := by
    have := hb (x := v) (by simpa [dist_eq_norm] using hv)
    simpa [dist_eq_norm, h00] using this
  rw [ugermC_snd_eq_neg_mul a h00 v]
  by_cases hd : (ugermC a h v).1 - ((a / 2 : ℝ) : ℂ) = 0
  · rw [hd]; simp
  · rw [mul_div_assoc, div_self hd, mul_one, norm_neg]; exact hbv.le

/-- **A compact regular cycle forces a rational germ (replaces Chow + Rychlik Thm 12, first
half).** The fibre trace `G` of `W` over the `ψ₁`-fibres of the cycle is `n · h(λ·)` near `0`
and bounded near `∞`, hence rational; so `h` is a rational germ. -/
theorem rational_of_compact_cycle {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {p : ChainData} (hp : p ∈ H0 a h) {c : ℂ}
    (hc : ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = c) {d : ℕ} (hd : 0 < d)
    (hcyc : ∀ q ∈ connectedComponentIn (H0 a h) p,
      (hShift a)^[d] q ∈ connectedComponentIn (H0 a h) p)
    (hcpt : CompactModPunctures a h (connectedComponentIn (H0 a h) p)) :
    ∃ N D : Polynomial ℂ, D.eval 0 ≠ 0 ∧ ∀ᶠ u in 𝓝 (0 : ℂ), h u * D.eval u = N.eval u := by
  set S := connectedComponentIn (H0 a h) p with hSdef
  obtain ⟨ε, hε, hA1, hA2⟩ := cycle_ends_principal ha0 ha1 hh hp hc hd hcyc hcpt
  obtain ⟨n, hn, hfin, hcnt, hmero⟩ := cycle_trace_meromorphic ha0 ha1 hh hp hcpt
  obtain ⟨δ₁, hδ₁, hW1⟩ := W_germC_near ha0 ha1 hh
  obtain ⟨δ₂, B, hδ₂, hW2⟩ := W_ugermC_bdd ha0 ha1 hh
  set G : ℂ → ℂ := fun u => ∑ᶠ q ∈ {q | q ∈ S ∧ q.2.1 = u}, wNum 0 q / wDen a 0 q with hG
  set g : ℂ → ℂ := fun u => (n : ℂ) * h ((eqLam a : ℂ) * u) with hgdef
  have hlam0 : 0 < eqLam a := by rw [eqLam]; exact div_pos (by linarith) (by linarith)
  have hlam1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  have hnormlam : ‖(eqLam a : ℂ)‖ = eqLam a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
  -- the fibre sum when every term is the same value
  have hsum_const : ∀ u : ℂ, u ≠ 0 → ∀ w : ℂ,
      (∀ q ∈ {q | q ∈ S ∧ q.2.1 = u}, wNum 0 q / wDen a 0 q = w) →
      G u = ({q | q ∈ S ∧ q.2.1 = u}.ncard : ℂ) * w := by
    intro u hu w hw
    have hF := (hfin u hu).1
    simp only [hG]
    rw [finsum_mem_congr rfl hw, finsum_mem_eq_finite_toFinset_sum _ hF, Finset.sum_const,
      Set.ncard_eq_toFinset_card _ hF, nsmul_eq_mul]
  -- `c ≠ 0`
  have hpS : p ∈ S := mem_connectedComponentIn hp
  have hc0 : c ≠ 0 := by
    obtain ⟨ε', hε', f, -, hf0, hf⟩ := hp
    have hch := (hf p.2.1 (Metric.mem_ball_self hε')).1
    rw [hf0] at hch
    rw [← hc p hpS]; exact mul_ne_zero hch.2.1 hch.2.2.1
  -- near `0`
  have hnear : ∀ u : ℂ, u ≠ 0 → ‖u‖ < min ε δ₁ → G =ᶠ[𝓝[≠] u] g := by
    intro u hu hlt
    have hopen : ∀ᶠ w in 𝓝[≠] u, w ≠ 0 ∧ ‖w‖ < min ε δ₁ := by
      apply eventually_nhdsWithin_of_eventually_nhds
      exact (isOpen_compl_singleton.inter (isOpen_lt continuous_norm continuous_const)).mem_nhds
        ⟨hu, hlt⟩
    filter_upwards [hcnt u hu, hopen] with w hw ⟨hw0, hwlt⟩
    rw [hsum_const w hw0 (h ((eqLam a : ℂ) * w)), hw]
    rintro q ⟨hqS, hqw⟩
    have h0 : q.1 0 = germC a h w := by
      rw [← hqw]; exact hA1 q hqS (by rw [hqw]; exact lt_of_lt_of_le hwlt (min_le_left _ _))
    simp only [wNum, wDen, neg_zero, h0]
    exact hW1 w hw0 (lt_of_lt_of_le hwlt (min_le_right _ _))
  -- near `∞`
  have hfar : ∃ R B' : ℝ, ∀ u : ℂ, R < ‖u‖ → ‖G u‖ ≤ B' := by
    refine ⟨‖c‖ / min ε δ₂, n * max B 0, fun u hu => ?_⟩
    have hm : 0 < min ε δ₂ := lt_min hε hδ₂
    have hu0 : u ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hu; exact absurd hu (not_lt.mpr (by positivity))
    have hsmall : ‖c / u‖ < min ε δ₂ := by
      rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr hu0)]
      rw [div_lt_iff₀ hm] at hu; linarith
    have hterm : ∀ q ∈ {q | q ∈ S ∧ q.2.1 = u}, ‖wNum 0 q / wDen a 0 q‖ ≤ max B 0 := by
      rintro q ⟨hqS, hqu⟩
      have hq2 : q.2.2 = c / u := by
        rw [eq_div_iff hu0, ← hqu, mul_comm]; exact hc q hqS
      have h0 : q.1 0 = ugermC a h (c / u) := by
        rw [← hq2]; exact hA2 q hqS (by rw [hq2]; exact lt_of_lt_of_le hsmall (min_le_left _ _))
      simp only [wNum, wDen, neg_zero, h0]
      exact le_trans (hW2 _ (lt_of_lt_of_le hsmall (min_le_right _ _))) (le_max_left _ _)
    have hF := (hfin u hu0).1
    simp only [hG]
    rw [finsum_mem_eq_finite_toFinset_sum _ hF]
    calc ‖∑ q ∈ hF.toFinset, wNum 0 q / wDen a 0 q‖
        ≤ ∑ q ∈ hF.toFinset, ‖wNum 0 q / wDen a 0 q‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ hF.toFinset, max B 0 :=
          Finset.sum_le_sum fun q hq => hterm q ((Set.Finite.mem_toFinset hF).mp hq)
      _ = hF.toFinset.card * max B 0 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * max B 0 := by
          apply mul_le_mul_of_nonneg_right _ (le_max_right _ _)
          rw [← Set.ncard_eq_toFinset_card _ hF]; exact_mod_cast (hfin u hu0).2
  -- `g` is analytic near `0`
  have hgan : AnalyticOnNhd ℂ g (Metric.ball 0 r) := by
    intro u hu
    have hlu : (eqLam a : ℂ) * u ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, hnormlam]
      rw [Metric.mem_ball, dist_zero_right] at hu
      calc eqLam a * ‖u‖ ≤ 1 * ‖u‖ := by gcongr
        _ < r := by linarith
    exact analyticAt_const.mul ((hh.2.1 _ hlu).comp (analyticAt_const.mul analyticAt_id))
  have hε' : 0 < min (min ε δ₁) r := lt_min (lt_min hε hδ₁) hh.1
  obtain ⟨N, D, hD0, hND⟩ := rational_of_meromorphic_trace (G := G) (g := g) hε'
    (fun u hu => hgan u (Metric.ball_subset_ball (min_le_right _ _) hu)) hmero
    (fun u hu hlt => hnear u hu (lt_of_lt_of_le hlt (min_le_left _ _))) hfar
  -- descend from `g = n h(λ ·)` to `h`
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hDne : D ≠ 0 := fun h' => hD0 (by rw [h']; simp)
  have hcont : ContinuousAt h 0 := (hh.2.1 0 (Metric.mem_ball_self hh.1)).continuousAt
  have hlamC : (eqLam a : ℂ) ≠ 0 := by exact_mod_cast hlam0.ne'
  refine rational_germ_of_eventually_eq_comp (g := fun z => h ((eqLam a : ℂ) * z)) hlamC hcont
    (N := Polynomial.C (n : ℂ)⁻¹ * N) hDne ?_ (Eventually.of_forall fun z => rfl)
  apply eventually_nhdsWithin_of_eventually_nhds
  filter_upwards [hND] with z hz
  rw [Polynomial.eval_mul, Polynomial.eval_C, ← hz]
  simp only [hgdef]; field_simp

end Work.EQ
