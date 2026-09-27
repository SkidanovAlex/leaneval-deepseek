import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.stable_trichotomy_of_cluster
import Submission.Work.EQ.tendsto_fan_of_uniform_limit
import Submission.Work.EQ.LaTB.not_flat_of_unNear
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.la_w0_charval_small

/-! # The stable trichotomy of a cluster, on *minimal* words, with a non-trivial value

This is `Work.EQ.stable_trichotomy_of_cluster` run on the **minimal words** of the chains and with
the **literal-word** trichotomy `Work.EQ.LaTB.la_fan_trichotomy_v2` (whose case (i) says that the
words themselves are constant, not merely their fan maps).  The two changes together buy the
extra conclusion `μ₁ ≠ 1`:

* case (i) would force all the minimal words of the subsequence to be equal, hence to have equal
  lengths, contradicting the hypothesis that their lengths are unbounded;
* in case (ii) the decomposition `ε_k = ε₀ ++ true^{s_k} ++ C_k` with `s_k → ∞` and `ε_k` ending
  in `false` gives `false ∈ C_k` for large `k`, so
  `μ₁ = charVal a h ε₁ = charVal a h (C k) < 1` by `Work.EQ.charVal_lt_one_of_false_mem`;
* case (iii) is excluded exactly as in `stable_trichotomy_of_cluster`
  (`Work.EQ.LaTB.not_flat_of_unNear` + `Work.EQ.FanSep.axis_walk`).

The uniform convergence of case (ii) is taken as an input (it is
`Work.EQ.FanTri.fan_gap_unif`, whose proof is `sorry`-free), so that the caller can instantiate both
inputs at a common radius `δ`.

`Work.EQ.exists_strictMono_length` turns "unbounded lengths" into a strictly monotone subsequence
whose lengths dominate the index. -/

namespace Work.EQ

open Filter _root_.Topology Complex Metric

noncomputable section

/-- **Unbounded lengths give a strictly monotone subsequence with the lengths dominating the
index.** -/
theorem exists_strictMono_length {ε : ℕ → List Bool}
    (h : ∀ B : ℕ, ∃ k, B ≤ (ε k).length) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ k, k ≤ (ε (ψ k)).length := by
  classical
  have hex : ∀ n : ℕ, ∃ k : ℕ, n < k ∧ n + 1 ≤ (ε k).length := by
    intro n
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ := h ((Finset.range (n + 1)).sup (fun j => (ε j).length) + n + 2)
    have hkbig : n < k := by
      by_contra hle
      push_neg at hle
      have h1 : (ε k).length ≤ (Finset.range (n + 1)).sup (fun j => (ε j).length) :=
        Finset.le_sup (f := fun j => (ε j).length)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
      omega
    have h3 := hcon k hkbig
    omega
  choose g hg using hex
  let ψ : ℕ → ℕ := fun n => Nat.rec (g 0) (fun m p => g (p + 1)) n
  have hψsucc : ∀ n, ψ (n + 1) = g (ψ n + 1) := fun n => rfl
  have hψstep : ∀ n, ψ n < ψ (n + 1) := by
    intro n
    rw [hψsucc]
    have := (hg (ψ n + 1)).1
    omega
  have hψmono : StrictMono ψ := strictMono_nat_of_lt_succ hψstep
  have hψlen : ∀ n, n + 1 ≤ (ε (ψ n)).length := by
    intro n
    cases n with
    | zero => rw [show ψ 0 = g 0 from rfl]; exact (hg 0).2
    | succ m =>
        rw [hψsucc]
        have hle : m ≤ ψ m := hψmono.id_le m
        have := (hg (ψ m + 1)).2
        omega
  exact ⟨ψ, hψmono, fun n => by have := hψlen n; omega⟩

/-- Splitting a list whose last letter is `false`: either `false` lies in the second part, or the
second part is empty and the first part ends in `false`. -/
lemma false_mem_of_getLast?_append {l m : List Bool} (h : (l ++ m).getLast? = some false) :
    false ∈ m ∨ (m = [] ∧ l.getLast? = some false) := by
  rw [List.getLast?_append] at h
  rcases hm : m.getLast? with _ | x
  · refine Or.inr ⟨List.getLast?_eq_none_iff.mp hm, ?_⟩
    rwa [hm] at h
  · refine Or.inl ?_
    have hx : x = false := by rw [hm] at h; simpa using h
    obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.mp hm
    rw [hl', hx]; simp

/-- `getLast?` of a non-empty run of principal letters. -/
lemma getLast?_replicate_true {n : ℕ} (hn : 0 < n) :
    (List.replicate n true).getLast? = some true := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.replicate_succ', List.getLast?_concat]

/-- **The stable trichotomy of a cluster, on minimal words.** If `x k` are chains of `⁰H`, read at
their level-`0` **minimal** words `ε k` (words whose last letter is `false` and whose lengths are
unbounded), with parameters `ψ₁ (x k) → W` inside the ball `B(0,δ)` and `-N`-th points `1/4`-UnNear
the axis, then along a subsequence the fan values converge to `fan a h ε₀ (μ₁ W)` with
`μ₁ ∈ CharSet a h` and `μ₁ ≠ 1`. -/
theorem stable_trichotomy_v2_of_minimal_words {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {r : ℝ} (hh : IsStableGerm a h r) :
    ∀ {δ : ℝ}, 0 < δ →
      (∀ ε : List Bool, ContinuousOn (fan a h ε) (Metric.ball (0 : ℂ) δ)) →
      (∀ ε : ℕ → List Bool, ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ((∃ ε₀, ∀ k, ε (φ k) = ε₀) ∨
         (∃ (ε₀ ε₁ : List Bool) (s : ℕ → ℕ) (C : ℕ → List Bool),
            Tendsto s atTop atTop ∧
            (∀ k, ε (φ k) = ε₀ ++ List.replicate (s k) true ++ C k) ∧
            (∀ k, fan a h (C k) 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
              charVal a h (C k) = charVal a h ε₁) ∧
            fan a h ε₁ 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧ (charVal a h ε₁).im = 0 ∧
            0 < (charVal a h ε₁).re ∧ (charVal a h ε₁).re ≤ 1) ∨
         ((∀ n : ℕ, ∀ᶠ k in atTop, n ≤ nonA1Count a h (ε (φ k))) ∧
            ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ u ∈ Metric.ball (0 : ℂ) δ,
              ‖(fan a h (ε (φ k)) u).1 - (fan a h (ε (φ k)) 0).1‖ < η ∧
              ‖(fan a h (ε (φ k)) u).2‖ < η * ‖(fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)‖))) →
      (∀ (ε₀ : List Bool) (s : ℕ → ℕ) (C : ℕ → List Bool) (μ : ℂ), Tendsto s atTop atTop →
        (∀ k, fan a h (C k) 0 = ((-1 / 2 : ℂ), (0 : ℂ))) →
        (∀ k, charVal a h (C k) = μ) →
        TendstoUniformlyOn (fun k => fan a h (ε₀ ++ List.replicate (s k) true ++ C k))
          (fun u => fan a h ε₀ (μ * u)) atTop (Metric.ball (0 : ℂ) δ)) →
      ∀ {N : ℕ} {W : ℂ} {x : ℕ → ChainData} {ε : ℕ → List Bool},
        (∀ k, IsChain a h (x k)) →
        (∀ k, (x k).1 0 = fan a h (ε k) (x k).2.1) →
        (∀ k, ‖(x k).2.1‖ < δ) →
        (∀ k, (ε k).getLast? = some false) →
        (∀ B : ℕ, ∃ k, B ≤ (ε k).length) →
        (∀ k, LaNnas.UnNear a ((x k).1 (-(N : ℤ))) (1 / 4)) →
        Tendsto (fun k => (x k).2.1) atTop (nhds W) → ‖W‖ < δ →
        ∃ ε₀, ∃ μ₁ ∈ CharSet a h, μ₁ ≠ 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
          Tendsto (fun k => fan a h (ε (φ k)) ((x (φ k)).2.1)) atTop
            (nhds (fan a h ε₀ (μ₁ * W))) := by
  intro δ hδ hcont htri hgap N W x ε hchain hread hnorm hlast hlen hnear hlim hW
  obtain ⟨ψ, hψm, hψlen⟩ := exists_strictMono_length hlen
  obtain ⟨φ₀, hφ₀m, hcase⟩ := htri (fun k => ε (ψ k))
  have hlen' : ∀ k, φ₀ k ≤ (ε (ψ (φ₀ k))).length := fun k => hψlen (φ₀ k)
  have hlast' : ∀ k, (ε (ψ (φ₀ k))).getLast? = some false := fun k => hlast (ψ (φ₀ k))
  rcases hcase with ⟨ε₀, hconst⟩ | ⟨ε₀, ε₁, s, C, hs, hword, hCret, hε₁fan, hμim, hμre0, hμre1⟩
    | ⟨hcount, hflat⟩
  · -- case (i): literal constancy contradicts unbounded lengths
    exfalso
    have h1 : φ₀ (ε₀.length + 1) ≤ ε₀.length := by
      have h2 := hlen' (ε₀.length + 1)
      rw [hconst (ε₀.length + 1)] at h2
      simpa using h2
    have h3 : ε₀.length + 1 ≤ φ₀ (ε₀.length + 1) := hφ₀m.id_le _
    omega
  · -- case (ii): the returning word contains a `false`, so `charVal ε₁ ≠ 1`
    have hs1 : ∀ᶠ k in atTop, 1 ≤ s k := (tendsto_atTop.1 hs) 1
    obtain ⟨K, hK⟩ := eventually_atTop.1 hs1
    have hfalse : ∀ k, K ≤ k → false ∈ C k := by
      intro k hk
      have hlast_k : ((ε₀ ++ List.replicate (s k) true) ++ C k).getLast? = some false := by
        have hh := hlast' k
        rw [hword k] at hh
        exact hh
      rcases false_mem_of_getLast?_append hlast_k with hmem | ⟨hne, hgl⟩
      · exact hmem
      · exfalso
        have hs1k : 0 < s k := by have := hK k hk; omega
        rw [List.getLast?_append, getLast?_replicate_true hs1k] at hgl
        simp at hgl
    have hneC : charVal a h (C K) ≠ 1 :=
      charVal_ne_one_of_false_mem ha0 ha1 hh (hCret K).1 (hfalse K le_rfl)
    have hne1 : charVal a h ε₁ ≠ 1 := fun h1 => hneC (by rw [(hCret K).2]; exact h1)
    have hre1 : (charVal a h ε₁).re < 1 := by
      rcases lt_or_eq_of_le hμre1 with h | h
      · exact h
      · exact absurd (Complex.ext h hμim) hne1
    have hunif : TendstoUniformlyOn (fun k => fan a h (ε (ψ (φ₀ k))))
        (fun u => fan a h ε₀ (charVal a h ε₁ * u)) atTop (Metric.ball (0 : ℂ) δ) := by
      have h0 := hgap ε₀ s C (charVal a h ε₁) hs (fun k => (hCret k).1) (fun k => (hCret k).2)
      simpa [hword] using h0
    refine ⟨ε₀, charVal a h ε₁, Or.inr ⟨ε₁, hε₁fan, rfl⟩, hne1, ψ ∘ φ₀, hψm.comp hφ₀m, ?_⟩
    refine tendsto_fan_of_uniform_limit (ε := fun k => ε (ψ (φ₀ k)))
      (ε₀ := ε₀) (μ := charVal a h ε₁) (x := fun k => x (ψ (φ₀ k))) hunif ?_ ?_ hW ?_ (hcont ε₀)
    · exact hlim.comp (hψm.comp hφ₀m).tendsto_atTop
    · intro k; exact hnorm (ψ (φ₀ k))
    · rw [norm_charVal_eq_re hμim hμre0]
      exact hre1
  · -- case (iii) is impossible
    exfalso
    obtain ⟨η₀, hη₀pos, hnotflat⟩ := LaTB.not_flat_of_unNear ha0 ha1 N
    obtain ⟨K, hK⟩ := eventually_atTop.mp (hflat η₀ hη₀pos)
    have hmem : ∀ k, (x (ψ (φ₀ k))).2.1 ∈ Metric.ball (0 : ℂ) δ := fun k => by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hnorm (ψ (φ₀ k))
    obtain ⟨hfl1, hfl2⟩ := hK K le_rfl ((x (ψ (φ₀ K))).2.1) (hmem K)
    obtain ⟨Y, hY⟩ := ((FanSep.axis_walk (a := a) ha0 ha1 hh).2 (ε (ψ (φ₀ K)))).2
    exact hnotflat (hchain (ψ (φ₀ K))).1 (hread (ψ (φ₀ K))) (hnear (ψ (φ₀ K))) hY hfl1 hfl2

end

end Work.EQ
