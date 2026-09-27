/-
# A collision-free strip around the boundary line, from local injectivity

Let `g : ℝ × ℝ → F` be continuous and `2π`-periodic in its first coordinate, and suppose that

* (boundary injectivity) `g (α, 0) = g (α', 0)` forces `α ≡ α' (mod 2π)`, and
* (local injectivity) at every boundary point `(α, 0)` there is a ball on which `g` is injective.

Then `g` is injective on a whole strip `τ ∈ [-c', 0]` around the boundary line, modulo `2π`:
there is `c' > 0` such that `g (α, τ) = g (α', τ')` with `τ, τ' ∈ [-c', 0]` forces
`τ = τ'` and `α ≡ α' (mod 2π)`.

## Proof

The argument is the standard limit/cluster-point one.  Suppose the conclusion fails at every scale
`c = 1/(n+1)`; then there are points `(αₙ, τₙ), (α'ₙ, τ'ₙ)` with `τₙ, τ'ₙ ∈ [-1/(n+1), 0]`, equal
images `g (αₙ, τₙ) = g (α'ₙ, τ'ₙ)`, and not congruent modulo `2π` (or with `τₙ ≠ τ'ₙ`).

* Reduce `αₙ`, `α'ₙ` modulo `2π` into `[0, 2π]` (the periodicity of `g` preserves both the images
  and the claimed conclusion, and the congruence class).
* The reduced pairs `((αₙ, τₙ), (α'ₙ, τ'ₙ))` lie in the compact set
  `([0,2π] × [-1,0])²`, so a subsequence converges to a limit pair `(p, q)`
  (`IsCompact.tendsto_subseq`).
* Both `τ`-coordinates tend to `0`, so `p₂ = q₂ = 0`; by continuity and uniqueness of limits in the
  Hausdorff space `F` the two *boundary* points have equal images, `g p = g q`.  (This is exactly
  where `T2Space F` is needed: over a non-Hausdorff target the bad pairs can converge to two
  boundary points of different images — see the counterexample
  `Submission/Work/Drive/strip_local_false_witness.lean` for the statement without `T2Space`.)
* `hbd` then gives `p₁ - q₁ = 2πk`.  Shifting the `q`-side by the integer multiple `2πk`
  (a period of `g`) makes the two subsequences converge to the *same* boundary point `(p₁, 0)`;
  both are eventually inside one ball of `hloc p₁`, so the points must be equal: `τₙ = τ'ₙ` and
  `αₙ ≡ α'ₙ (mod 2π)` along the subsequence, contradicting the choice of the bad pairs.

Most of the formal work is bookkeeping: integer periodicity of `g (·, τ)`, reduction of a real
number modulo `2π` by `Int.fract`/`Int.floor`, and the subsequence extraction.
-/
import Mathlib

open Filter Topology

namespace Work.Drive

theorem exists_strip_injective_of_local
    {F : Type*} [TopologicalSpace F] [T2Space F]
    (g : ℝ × ℝ → F) (hg : Continuous g)
    (hper : ∀ α τ : ℝ, g (α + 2 * Real.pi, τ) = g (α, τ))
    (hbd : ∀ α α' : ℝ, g (α, 0) = g (α', 0) → ∃ k : ℤ, α - α' = 2 * Real.pi * k)
    (hloc : ∀ α : ℝ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Metric.ball (α, 0) ρ, ∀ y ∈ Metric.ball (α, 0) ρ,
      g x = g y → x = y) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ α α' τ τ' : ℝ, τ ∈ Set.Icc (-c') 0 → τ' ∈ Set.Icc (-c') 0 →
      g (α, τ) = g (α', τ') → (∃ k : ℤ, α - α' = 2 * Real.pi * k) ∧ τ = τ' := by
  -- ### integer multiples of `2π` are periods
  have hperInt : ∀ (m : ℤ) (α τ : ℝ), g (α + 2 * Real.pi * (m : ℝ), τ) = g (α, τ) := by
    intro m α τ
    have hf : Function.Periodic (fun a : ℝ => g (a, τ)) (2 * Real.pi) := fun x => hper x τ
    have h := hf.int_mul m α
    rwa [show (m : ℝ) * (2 * Real.pi) = 2 * Real.pi * (m : ℝ) by ring] at h
  -- ### every real number has a representative in `[0, 2π]`
  have hmod : ∀ α : ℝ, ∃ (m : ℤ) (r : ℝ),
      r ∈ Set.Icc 0 (2 * Real.pi) ∧ α = r + 2 * Real.pi * (m : ℝ) := by
    intro α
    refine ⟨⌊α / (2 * Real.pi)⌋, 2 * Real.pi * Int.fract (α / (2 * Real.pi)), ⟨?_, ?_⟩, ?_⟩
    · have h := Int.fract_nonneg (α / (2 * Real.pi))
      nlinarith [Real.pi_pos]
    · have h := Int.fract_lt_one (α / (2 * Real.pi))
      nlinarith [Real.pi_pos]
    · have h' : (⌊α / (2 * Real.pi)⌋ : ℝ) + Int.fract (α / (2 * Real.pi)) = α / (2 * Real.pi) :=
        Int.floor_add_fract _
      have h3 : (2 * Real.pi) *
          ((⌊α / (2 * Real.pi)⌋ : ℝ) + Int.fract (α / (2 * Real.pi))) = α := by
        rw [h']
        exact mul_div_cancel₀ α (by positivity : (2 : ℝ) * Real.pi ≠ 0)
      linarith [h3]
  by_contra hcon
  push Not at hcon
  -- ### a bad pair at every scale
  have hseq : ∀ n : ℕ, ∃ α α' τ τ' : ℝ,
      τ ∈ Set.Icc (-(1 / ((n : ℝ) + 1))) 0 ∧ τ' ∈ Set.Icc (-(1 / ((n : ℝ) + 1))) 0 ∧
      g (α, τ) = g (α', τ') ∧ ((∃ k : ℤ, α - α' = 2 * Real.pi * (k : ℝ)) → τ ≠ τ') := by
    intro n
    exact hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose α α' τ τ' hspec using hseq
  -- ### reduce the first coordinates modulo `2π`
  choose ma ra hra using fun n => hmod (α n)
  choose mb rb hrb using fun n => hmod (α' n)
  have hτmem : ∀ n, τ n ∈ Set.Icc (-1 : ℝ) 0 := by
    intro n
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    exact ⟨by linarith [(hspec n).1.1, h1], (hspec n).1.2⟩
  have hτ'mem : ∀ n, τ' n ∈ Set.Icc (-1 : ℝ) 0 := by
    intro n
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    exact ⟨by linarith [(hspec n).2.1.1, h1], (hspec n).2.1.2⟩
  have hmem : ∀ n, ((ra n, τ n), (rb n, τ' n)) ∈
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (-1 : ℝ) 0) ×ˢ
        (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (-1 : ℝ) 0) := by
    intro n
    exact ⟨⟨(hra n).1, hτmem n⟩, ⟨(hrb n).1, hτ'mem n⟩⟩
  -- the reduced points have the same image
  have hgred : ∀ n, g (ra n, τ n) = g (rb n, τ' n) := by
    intro n
    have e1 : g (ra n, τ n) = g (α n, τ n) := by
      have h := hperInt (ma n) (ra n) (τ n)
      have e : (α n, τ n) = (ra n + 2 * Real.pi * (ma n : ℝ), τ n) := by rw [(hra n).2]
      rw [e, h]
    have e2 : g (rb n, τ' n) = g (α' n, τ' n) := by
      have h := hperInt (mb n) (rb n) (τ' n)
      have e : (α' n, τ' n) = (rb n + 2 * Real.pi * (mb n : ℝ), τ' n) := by rw [(hrb n).2]
      rw [e, h]
    rw [e1, (hspec n).2.2.1, e2]
  -- the reduced points are still bad
  have hbadPQ : ∀ n, (∃ k : ℤ, ra n - rb n = 2 * Real.pi * (k : ℝ)) → τ n ≠ τ' n := by
    intro n hconj
    obtain ⟨k, hk⟩ := hconj
    refine (hspec n).2.2.2 ⟨k + (ma n - mb n), ?_⟩
    have e1 : α n = ra n + 2 * Real.pi * (ma n : ℝ) := (hra n).2
    have e2 : α' n = rb n + 2 * Real.pi * (mb n : ℝ) := (hrb n).2
    rw [e1, e2]
    push_cast
    linarith [hk]
  -- ### compactness: a cluster point of the bad pairs
  obtain ⟨⟨p, q⟩, -, φ, hφmono, hφt⟩ :=
    (isCompact_Icc.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc) |>.tendsto_subseq
      (x := fun n => ((ra n, τ n), (rb n, τ' n))) hmem
  have hφt2 : Tendsto (fun n => ((ra (φ n), τ (φ n)), (rb (φ n), τ' (φ n)))) atTop
      (𝓝 p ×ˢ 𝓝 q) := by
    have h := hφt
    rw [nhds_prod_eq] at h
    exact h
  have hpt : Tendsto (fun n => (ra (φ n), τ (φ n))) atTop (𝓝 p) := by
    simpa using hφt2.fst
  have hqt : Tendsto (fun n => (rb (φ n), τ' (φ n))) atTop (𝓝 q) := by
    simpa using hφt2.snd
  have hpt_pf : Tendsto (fun n => (ra (φ n), τ (φ n))) atTop (𝓝 p.1 ×ˢ 𝓝 p.2) := by
    have h := hpt
    rwa [nhds_prod_eq] at h
  have hqt_pf : Tendsto (fun n => (rb (φ n), τ' (φ n))) atTop (𝓝 q.1 ×ˢ 𝓝 q.2) := by
    have h := hqt
    rwa [nhds_prod_eq] at h
  -- the `τ`-coordinates of the bad pairs tend to `0`
  have hτtend : Tendsto τ atTop (𝓝 (0 : ℝ)) := by
    have hlow : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => (hspec n).1.1) (fun n => (hspec n).1.2)
  have hτ'tend : Tendsto τ' atTop (𝓝 (0 : ℝ)) := by
    have hlow : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => (hspec n).2.1.1) (fun n => (hspec n).2.1.2)
  have hp2 : p.2 = 0 := by
    refine tendsto_nhds_unique (by simpa using hpt_pf.snd) ?_
    exact hτtend.comp hφmono.tendsto_atTop
  have hq2 : q.2 = 0 := by
    refine tendsto_nhds_unique (by simpa using hqt_pf.snd) ?_
    exact hτ'tend.comp hφmono.tendsto_atTop
  have hp0 : (p.1, (0 : ℝ)) = p := by rw [← hp2, Prod.mk.eta]
  have hq0 : (q.1, (0 : ℝ)) = q := by rw [← hq2, Prod.mk.eta]
  -- ### the boundary limits have equal images (`T2Space` is used here)
  have hgpq : g p = g q := by
    have hw : Tendsto g (𝓝 p) (𝓝 (g p)) := hg.continuousAt (x := p)
    have h1 : Tendsto (fun n => g (ra (φ n), τ (φ n))) atTop (𝓝 (g p)) := hw.comp hpt
    have hw' : Tendsto g (𝓝 q) (𝓝 (g q)) := hg.continuousAt (x := q)
    have h3 : Tendsto (fun n => g (rb (φ n), τ' (φ n))) atTop (𝓝 (g q)) := hw'.comp hqt
    have h2 : Tendsto (fun n => g (ra (φ n), τ (φ n))) atTop (𝓝 (g q)) :=
      Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => (hgred (φ n)).symm) h3
    exact tendsto_nhds_unique h1 h2
  have hpqbd : g (p.1, 0) = g (q.1, 0) := by rw [hp0, hq0]; exact hgpq
  obtain ⟨k, hk⟩ := hbd p.1 q.1 hpqbd
  -- ### shift the `q`-side by `2πk` and use local injectivity at `p.1`
  obtain ⟨ρ, hρpos, hρ⟩ := hloc p.1
  have hpt0 : Tendsto (fun n => (ra (φ n), τ (φ n))) atTop (𝓝 (p.1, (0 : ℝ))) := by
    rw [hp0]
    exact hpt
  have hYtend : Tendsto (fun n => (rb (φ n) + 2 * Real.pi * (k : ℝ), τ' (φ n))) atTop
      (𝓝 (p.1, (0 : ℝ))) := by
    have h1 : Tendsto (fun n => (rb (φ n), τ' (φ n)).1 + 2 * Real.pi * (k : ℝ)) atTop
        (𝓝 (q.1 + 2 * Real.pi * (k : ℝ))) := hqt_pf.fst.add tendsto_const_nhds
    have h2 : Tendsto (fun n => (rb (φ n), τ' (φ n)).2) atTop (𝓝 (0 : ℝ)) :=
      hτ'tend.comp hφmono.tendsto_atTop
    have h3 : q.1 + 2 * Real.pi * (k : ℝ) = p.1 := by linarith [hk]
    rw [h3] at h1
    exact Filter.Tendsto.prodMk_nhds h1 h2
  have hYper : ∀ n, g (rb (φ n) + 2 * Real.pi * (k : ℝ), τ' (φ n)) = g (rb (φ n), τ' (φ n)) :=
    fun n => hperInt k (rb (φ n)) (τ' (φ n))
  have hevP : ∀ᶠ n in atTop, (ra (φ n), τ (φ n)) ∈ Metric.ball (p.1, 0) ρ :=
    hpt0.eventually (Metric.ball_mem_nhds _ hρpos)
  have hevY : ∀ᶠ n in atTop,
      (rb (φ n) + 2 * Real.pi * (k : ℝ), τ' (φ n)) ∈ Metric.ball (p.1, 0) ρ :=
    hYtend.eventually (Metric.ball_mem_nhds _ hρpos)
  obtain ⟨n, hnP, hnY⟩ := (hevP.and hevY).exists
  have heq : (ra (φ n), τ (φ n)) = (rb (φ n) + 2 * Real.pi * (k : ℝ), τ' (φ n)) :=
    hρ _ hnP _ hnY (by rw [hYper n]; exact hgred (φ n))
  exact hbadPQ (φ n) ⟨k, by linarith [congrArg Prod.fst heq]⟩ (congrArg Prod.snd heq)

end Work.Drive
