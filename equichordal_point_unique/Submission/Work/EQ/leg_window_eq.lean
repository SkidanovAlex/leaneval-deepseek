import Mathlib
import Submission.Work.EQ.H0_path_limit_window_adm
import Submission.Work.EQ.branchPt_meromorphic
import Submission.Work.EQ.H0_path_limit_engine
import Submission.Work.EQ.meromorphicOrderAt_nonneg_of_seq_bounded

namespace Work.EQ

open Filter _root_.Topology Set Metric

open scoped Topology

noncomputable section

/-! ## Elementary analytic helpers -/

/-- A sequence of complex numbers whose `k`-th powers (`k > 0`) tend to `0` tends to `0`. -/
lemma tendsto_zero_of_pow_tendsto_zero {u : ℕ → ℂ} {k : ℕ}
    (h : Tendsto (fun n => u n ^ k) atTop (𝓝 0)) : Tendsto u atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε ^ k) (pow_pos hε k)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ‖u n‖ ^ k < ε ^ k := by
    have h2 := hN n hn
    rwa [dist_zero_right, norm_pow] at h2
  have h2 : ‖u n‖ < ε := lt_of_pow_lt_pow_left₀ k hε.le h1
  simpa [dist_zero_right] using h2

/-- A convergent sequence of complex numbers is bounded in norm. -/
lemma exists_norm_bound_of_tendsto {u : ℕ → ℂ} {a : ℂ} (h : Tendsto u atTop (𝓝 a)) :
    ∃ C : ℝ, ∀ n, ‖u n‖ ≤ C := by
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp (isBounded_range_of_tendsto u h)
  refine ⟨C + ‖u 0‖, fun n => ?_⟩
  have h1 : ‖u n - u 0‖ ≤ C := by
    have h2 := hC n 0
    rwa [dist_eq_norm] at h2
  calc ‖u n‖ = ‖(u n - u 0) + u 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖u n - u 0‖ + ‖u 0‖ := norm_add_le _ _
    _ ≤ C + ‖u 0‖ := by linarith

/-- **A meromorphic function bounded along a punctured sequence tending to `0` has the limit of
that sequence at `0`.**  `Work.EQ.meromorphicOrderAt_nonneg_of_seq_bounded` gives that the order of
`f` at `0` is nonnegative, so `f` has a limit `L` along `𝓝[≠] 0`
(Mathlib's `tendsto_nhds_of_meromorphicOrderAt_nonneg`); the sequence values converge to `L` as
well and to `a` by hypothesis, so `L = a` by uniqueness of limits. -/
lemma meromorphicAt_tendsto_nhdsNE_of_seq {f : ℂ → ℂ} {t : ℕ → ℂ} {a : ℂ} {C : ℝ}
    (hf : MeromorphicAt f 0) (ht : Tendsto t atTop (𝓝[≠] (0 : ℂ)))
    (hval : Tendsto (fun n => f (t n)) atTop (𝓝 a)) (hbd : ∀ n, ‖f (t n)‖ ≤ C) :
    Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 a) := by
  obtain ⟨L, hL⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf
    (meromorphicOrderAt_nonneg_of_seq_bounded hf ht hbd)
  have h2 : Tendsto (fun n => f (t n)) atTop (𝓝 L) := hL.comp ht
  have hLa : L = a := tendsto_nhds_unique h2 hval
  rwa [hLa] at hL

/-- The window of a continuous path of chains is the same at the two ends of a visit-free
interval.

Setting: `hfw`/`hbw` are the uniform forward/backward tails of the path from `n₁`, `m₁`, `hc` says
the end map `w ↦ germC a h (λ^n₁ w)` is analytic on `ball u R`, `x < y` are two visit times
(`ψ₁(γ x) = ψ₁(γ y) = u`), there is no visit in `(x,y)`, and `ψ₁(γ s) - u` lies inside the Puiseux
disc `rhoFin' a c u R (n₁+m₁)` on `(x,y)`.  Conclusion: the windows `j ↦ (γ ·).1 ((j:ℕ):ℤ) - m₁`
at `x` and at `y` are equal.

Route: apply `Work.EQ.H0_path_limit_window_adm` to the preconnected `I = Set.Ioo x y` to get a single
admissible sign sequence `σ` and, for each `s ∈ I`, a parameter `t` with
`t ^ (2^(n₁+m₁)) = ψ₁(γ s) - u`, `0 < ‖t‖`, `‖t‖ < rhoFin'` and the window identity against
`branchPt a c u R σ t`.  Fix `j : Fin (n₁+m₁+1)`.  For a sequence `s n ∈ I` with `s n → x` (e.g.
`s n = x + (y - x)/(n + 2)`) and the corresponding `t n`, one has `t n → 0` (because
`‖t n‖ ^ (2^(n₁+m₁)) = ‖ψ₁(γ (s n)) - u‖ → 0` by continuity of `ψ₁ ∘ γ` at `x`, using `hx`) and
`t n ≠ 0`; the values `(branchPt a c u R σ (t n) j).1 = ((γ (s n)).1 ((j:ℕ):ℤ) - m₁).1` converge,
hence are bounded.  `Work.EQ.branchPt_meromorphic` gives that
`fun t => (branchPt a c u R σ t j).1` is meromorphic at `0`, so
`Work.EQ.meromorphicAt_tendsto_nhdsNE_of_seq` produces a limit along `𝓝[≠] 0` equal to
`((γ x).1 ((j:ℕ):ℤ) - m₁).1`.  The same with a sequence approaching `y` from the left gives the same
limit (uniqueness), so the first coordinates agree; the identical argument for the second coordinate
of `branchPt` finishes. -/
theorem leg_window_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {γ : ℝ → ChainData} {S : ℝ} {n₁ m₁ : ℕ} {u : ℂ}
    (hu : u ≠ 0) {R : ℝ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w))
      (Metric.ball u R))
    (hchain : ∀ s : ℝ, S ≤ s → IsChain a h (γ s))
    (hcont : ContinuousOn γ (Set.Ici S))
    (hfw : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, n₁ ≤ n →
      (γ s).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (γ s).2.1))
    (hbw : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, m₁ ≤ n →
      (γ s).1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * (γ s).2.2))
    {x y : ℝ} (hxy : x < y) (hxS : S ≤ x) (hyS : S ≤ y)
    (hx : (γ x).2.1 = u) (hy : (γ y).2.1 = u)
    (hne : ∀ s : ℝ, x < s → s < y → (γ s).2.1 ≠ u)
    (hcl : ∀ s : ℝ, x < s → s < y →
      ‖(γ s).2.1 - u‖ < (rhoFin' a (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R
        (n₁ + m₁)) ^ (2 ^ (n₁ + m₁)))
    (j : Fin (n₁ + m₁ + 1)) :
    (γ x).1 (((j : ℕ) : ℤ) - (m₁ : ℤ)) = (γ y).1 (((j : ℕ) : ℤ) - (m₁ : ℤ)) := by
  classical
  set c : ℂ → ℂ × ℂ := fun w => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w) with hcdef
  have hc' : AnalyticOnNhd ℂ c (Metric.ball u R) := by rw [hcdef]; exact hc
  -- the visit-free interval
  have hIS : ∀ s ∈ Set.Ioo x y, S ≤ s := fun s hs => le_trans hxS (le_of_lt hs.1)
  have hneI : ∀ s ∈ Set.Ioo x y, (γ s).2.1 ≠ u := fun s hs => hne s hs.1 hs.2
  have hclI : ∀ s ∈ Set.Ioo x y,
      ‖(γ s).2.1 - u‖ < (rhoFin' a c u R (n₁ + m₁)) ^ (2 ^ (n₁ + m₁)) :=
    fun s hs => hcl s hs.1 hs.2
  obtain ⟨σ, hσAdm, hσ⟩ :=
    H0_path_limit_window_adm ha0 ha1 hh hu hR hc hchain hcont hfw hbw (Set.Ioo x y) hIS
      isPreconnected_Ioo (Set.nonempty_Ioo.2 hxy) hneI hclI
  have hmer : ∀ j' : Fin (n₁ + m₁ + 1),
      MeromorphicAt (fun t : ℂ => (branchPt a c u R σ t j').1) 0 ∧
        MeromorphicAt (fun t : ℂ => (branchPt a c u R σ t j').2) 0 :=
    fun j' => branchPt_meromorphic hR hc' hσAdm j'
  -- the abstract limit statement at one endpoint
  have step' : ∀ (p : ℂ × ℂ → ℂ), Continuous p →
      MeromorphicAt (fun t : ℂ => p (branchPt a c u R σ t j)) 0 →
      ∀ (z : ℝ), S ≤ z → (γ z).2.1 = u → ∀ s : ℕ → ℝ,
      (∀ n, s n ∈ Set.Ioo x y) → Tendsto s atTop (𝓝 z) →
      Tendsto (fun t : ℂ => p (branchPt a c u R σ t j)) (𝓝[≠] (0 : ℂ))
        (𝓝 (p ((γ z).1 (((j : ℕ) : ℤ) - (m₁ : ℤ))))) := by
    intro p hp hpm z hzS hzu s hsm hst
    choose t ht using fun n => hσ (s n) (hsm n)
    have htne : ∀ n, t n ≠ 0 := fun n => norm_pos_iff.mp (ht n).2.1
    -- the sequence lies in the tail
    have hsw : Tendsto s atTop (𝓝[Set.Ici S] z) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hst, Eventually.of_forall fun n => le_trans hxS (le_of_lt (hsm n).1)⟩
    -- the visit parameter tends to the visit value
    have hpsi : Tendsto (fun n => (γ (s n)).2.1) atTop (𝓝 u) := by
      have hcwa : ContinuousWithinAt (fun s : ℝ => (γ s).2.1) (Set.Ici S) z :=
        (continuousOn_psi1 hcont).continuousWithinAt hzS
      have h2 := hcwa.tendsto.comp hsw
      simpa [hzu, Function.comp_def] using h2
    -- the parameters tend to zero
    have hpow : Tendsto (fun n => t n ^ (2 ^ (n₁ + m₁))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => (γ (s n)).2.1 - u) atTop (𝓝 0) := by
        have h2 : Tendsto (fun n => (γ (s n)).2.1 - u) atTop (𝓝 (u - u)) :=
          hpsi.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u))
        simpa using h2
      exact Tendsto.congr' (Eventually.of_forall fun n => (ht n).1.symm) h1
    have ht0 : Tendsto t atTop (𝓝 0) :=
      tendsto_zero_of_pow_tendsto_zero hpow
    have htwith : Tendsto t atTop (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨ht0, Eventually.of_forall fun n => by simpa using htne n⟩
    -- the values converge
    have hcoord : ContinuousWithinAt
        (fun s : ℝ => p ((γ s).1 (((j : ℕ) : ℤ) - (m₁ : ℤ)))) (Set.Ici S) z :=
      (hp.comp_continuousOn (continuousOn_coord hcont _)).continuousWithinAt hzS
    have hval0 : Tendsto (fun n => p ((γ (s n)).1 (((j : ℕ) : ℤ) - (m₁ : ℤ)))) atTop
        (𝓝 (p ((γ z).1 (((j : ℕ) : ℤ) - (m₁ : ℤ))))) := hcoord.tendsto.comp hsw
    have hval : Tendsto (fun n => p (branchPt a c u R σ (t n) j)) atTop
        (𝓝 (p ((γ z).1 (((j : ℕ) : ℤ) - (m₁ : ℤ))))) :=
      Tendsto.congr' (Eventually.of_forall fun n => by rw [(ht n).2.2.2 j]) hval0
    obtain ⟨C, hC⟩ := exists_norm_bound_of_tendsto hval
    exact meromorphicAt_tendsto_nhdsNE_of_seq hpm htwith hval hC
  -- two sequences approaching the endpoints from inside
  have hdpos : ∀ n : ℕ, (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := fun n => by positivity
  have hdlt : ∀ n : ℕ, (y - x) / ((n + 2 : ℕ) : ℝ) < y - x := by
    intro n
    have h2 : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by
      have h3 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast
      linarith
    rw [div_lt_iff₀ (hdpos n)]
    have h3 := mul_lt_mul_of_pos_left h2 (sub_pos.mpr hxy)
    simpa using h3
  have hdpos' : ∀ n : ℕ, (0 : ℝ) < (y - x) / ((n + 2 : ℕ) : ℝ) :=
    fun n => div_pos (sub_pos.mpr hxy) (hdpos n)
  have hmemx : ∀ n : ℕ, x + (y - x) / ((n + 2 : ℕ) : ℝ) ∈ Set.Ioo x y :=
    fun n => ⟨by linarith [hdpos' n], by linarith [hdlt n]⟩
  have hmemy : ∀ n : ℕ, y - (y - x) / ((n + 2 : ℕ) : ℝ) ∈ Set.Ioo x y :=
    fun n => ⟨by linarith [hdlt n], by linarith [hdpos' n]⟩
  have hzero : Tendsto (fun n : ℕ => (y - x) / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  have htx : Tendsto (fun n : ℕ => x + (y - x) / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 x) := by
    have h2 : Tendsto (fun n : ℕ => x + (y - x) / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 (x + 0)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).add hzero
    simpa using h2
  have hty : Tendsto (fun n : ℕ => y - (y - x) / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 y) := by
    have h2 : Tendsto (fun n : ℕ => y - (y - x) / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 (y - 0)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)).sub hzero
    simpa using h2
  -- the two coordinates agree
  have e1 : ((γ x).1 (((j : ℕ) : ℤ) - (m₁ : ℤ))).1
      = ((γ y).1 (((j : ℕ) : ℤ) - (m₁ : ℤ))).1 :=
    tendsto_nhds_unique
      (step' Prod.fst continuous_fst (hmer j).1 x hxS hx _ hmemx htx)
      (step' Prod.fst continuous_fst (hmer j).1 y hyS hy _ hmemy hty)
  have e2 : ((γ x).1 (((j : ℕ) : ℤ) - (m₁ : ℤ))).2
      = ((γ y).1 (((j : ℕ) : ℤ) - (m₁ : ℤ))).2 :=
    tendsto_nhds_unique
      (step' Prod.snd continuous_snd (hmer j).2 x hxS hx _ hmemx htx)
      (step' Prod.snd continuous_snd (hmer j).2 y hyS hy _ hmemy hty)
  exact Prod.ext e1 e2

end

end Work.EQ
