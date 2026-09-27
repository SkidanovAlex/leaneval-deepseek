import Mathlib
import Submission.Work.EQ.H0_junction_value_of_cluster
import Submission.Work.EQ.stable_trichotomy_v2_of_minimal_words
import Submission.Work.EQ.bwdP_fan_degenerate_countable
import Submission.Work.EQ.junction_limit_segment
import Submission.Work.EQ.charVal_set
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.ChainReading
import Submission.Work.EQ.chain_eq_candChain_of_tails
import Submission.Work.EQ.JNT.defs
import Submission.Work.EQ.LaTB.not_flat_of_unNear
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.H0_step5_aux
import Submission.Work.EQ.LTBV.junction_value_min
import Submission.Work.EQ.LTBV.minimal_word_last_letter_bounded

/-! # `Work.EQ.junction_nt_unbounded`

Rychlik, Invent. Math. 129 (1997), the "only one of `γ₁, γ₂` can be `1`" step (p. 45) in the
uncountability form used by this workspace: a cluster of chains of `⁰H` with `ψ₁ → z` over an
uncountable `Z` and invariant values `→ c₀ ≠ 0`, whose tails fail at arbitrarily large depths,
produces an uncountable junction set for a value `c₀μ₁μ₂` with `(μ₁,μ₂) ≠ (1,1)`, together with
words `ε, η, s` of a common length `N` (the depth) — the shape consumed by
`Work.EQ.regular_of_uncountable_junction`.

The file is organised as
* elementary helpers (`bwdP` with a prescribed length, the reading of the far end and its
  `drop` property, the shift of `TailP`/`tailIdx`, principal-letter padding of a fan word);
* `junction_forward`: the *one-sided* statement, in which the forward tails of the cluster
  chains are assumed unbounded (this is `Work.EQ.LTBV.junction_value_min` with the word lengths
  built in, via the far-end promotion described below);
* the main theorem, which splits `Z` into the forward- and backward-unbounded parts and, in the
  backward case, applies `junction_forward` to the shifted mirrors
  `w ↦ shiftZ a N₀ (mirrorChain (X z ·))` of the cluster chains.

The key point of the far end (absent from `junction_value_min`): at depth `N` the far-end words
`η k` are the words of the chains `shiftZ a N (mirrorChain (X z ·))`, and the trichotomy gives
`η k = η₀ ++ true^{s k} ++ C k` (or all `η k` literally equal).  Promoting the depth to
`N'' = N + |η₀|` drops the prefix (`far_reading_drop`), after which either the words are empty or
the uniform fan-gap estimate (`FanTri.fan_gap_unif`) identifies the limit with a pure unstable
germ `μ₂ ↦ germC (μ₂ λ^{N''} c₀ / z)`.  This is what lets the conclusion be stated with
`η = true^{N''}` of length exactly `N''`. -/

namespace Work.EQ

open Filter _root_.Topology
open Complex
open Classical

noncomputable section

/-! ## Elementary helpers -/

/-- **The limit segment, with the sign list of the prescribed length.**  Same statement as
`Work.EQ.junction_limit_segment`, but the sign list has length exactly `N` (its proof produces
one of that length). -/
theorem junction_limit_segment_len {a : ℝ} {N : ℕ} {q : ℕ → ChainData} {S T : ℂ × ℂ}
    (hstep : ∀ k, ∀ i ≤ N, RegPair a ((q k).1 (-((i : ℤ) + 1))) ((q k).1 (-(i : ℤ))))
    (hgood : ∀ σ : List Bool, σ.length ≤ N → bsq (subO1 a (bwdP a σ S)) ≠ 0)
    (h0 : Tendsto (fun k => (q k).1 0) atTop (nhds S))
    (hN : Tendsto (fun k => (q k).1 (-(N : ℤ))) atTop (nhds T)) :
    ∃ s : List Bool, s.length = N ∧ T = bwdP a s S := by
  have key : ∀ i, i ≤ N → ∃ (σ : List Bool) (φ : ℕ → ℕ), StrictMono φ ∧ σ.length = i ∧
      Tendsto (fun k => (q (φ k)).1 (-(i : ℤ))) atTop (nhds (bwdP a σ S)) := by
    intro i
    induction i with
    | zero =>
        intro _
        exact ⟨[], (id : ℕ → ℕ), strictMono_id, rfl, by simpa using h0⟩
    | succ i ih =>
        intro hi
        have hi' : i ≤ N := by omega
        obtain ⟨σ, φ, hφm, hσlen, hφT⟩ := ih hi'
        have hSne : bsq (subO1 a (bwdP a σ S)) ≠ 0 := hgood σ (by omega)
        have hbr : ∀ k, ∃ t : Bool, (q (φ k)).1 (-((i : ℤ) + 1)) =
            invBranch a t ((q (φ k)).1 (-(i : ℤ))) := by
          intro k
          obtain ⟨hrel, -, hnd⟩ := hstep (φ k) i hi'
          have hnd' : bsq (subO1 a ((q (φ k)).1 (-(i : ℤ)))) ≠ 0 := by
            simpa [bsq, subO1] using hnd
          rcases eqRelC_solutions hrel hnd' with h | h
          · exact ⟨true, h⟩
          · exact ⟨false, h⟩
        choose t ht using hbr
        obtain ⟨t', ψ, hψm, hψT⟩ := Junc.invBranch_cluster_subseq
          (a := a) (S := bwdP a σ S) (P := fun k => (q (φ k)).1 (-(i : ℤ)))
          (t := t) hSne hφT
        refine ⟨σ ++ [t'], φ ∘ ψ, hφm.comp hψm, ?_, ?_⟩
        · simp [hσlen]
        · rw [bwdP_snoc]
          refine hψT.congr' (Eventually.of_forall (fun k => ?_))
          show invBranch a (t (ψ k)) ((q (φ (ψ k))).1 (-(i : ℤ)))
              = (q ((φ ∘ ψ) k)).1 (-(((i + 1 : ℕ) : ℤ)))
          rw [show (((i + 1 : ℕ)) : ℤ) = (i : ℤ) + 1 by push_cast; ring]
          exact (ht (ψ k)).symm
  obtain ⟨σ, φ, hφm, hσlen, hφT⟩ := key N le_rfl
  exact ⟨σ, hσlen, tendsto_nhds_unique (hN.comp hφm.tendsto_atTop) hφT⟩

/-- **A fan word of principal letters is the germ.**  On the ball where the principal backward
branch inverts the germ step, `fan a h (true^N) u = germC a h u`. -/
theorem fan_replicate_true {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {δ : ℝ}
    (hinv : ∀ u : ℂ, ‖u‖ < δ →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    (N : ℕ) {u : ℂ} (hu : ‖u‖ < δ) :
    fan a h (List.replicate N true) u = germC a h u := by
  have h := fan_append_replicate_true ha0 ha1 hinv ([] : List Bool) N hu
  rw [List.nil_append] at h
  exact h

/-- The invariant parameter is preserved by the bisector reflection. -/
theorem psi_mirrorChain (q : ChainData) :
    (mirrorChain q).2.1 * (mirrorChain q).2.2 = q.2.1 * q.2.2 := by
  simp only [mirrorChain_psi1, mirrorChain_psi2, mul_comm]

/-- `TailP` is shifted by `shiftZ a j`: the forward tail of `σ^j q` from `N` is the forward tail
of `q` from `N + j`. -/
theorem TailP_shiftZ_nat {a : ℝ} {h : ℂ → ℂ} (j N : ℕ) (q : ChainData) :
    TailP a h (shiftZ a (j : ℤ) q) N ↔ TailP a h q (N + j) := by
  constructor
  · intro hq m hm
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + j := ⟨m - j, by omega⟩
    have hn : N ≤ n := by omega
    have h2 := hq n hn
    rw [shiftZ_fst, shiftZ_psi1, zpow_natCast] at h2
    have hidx : (n : ℤ) + (j : ℤ) = ((n + j : ℕ) : ℤ) := by push_cast; ring
    rw [hidx] at h2
    rw [h2]
    congr 1
    rw [pow_add]
    ring
  · intro hq n hn
    have h2 := hq (n + j) (by omega)
    rw [shiftZ_fst, shiftZ_psi1, zpow_natCast]
    have hidx : (n : ℤ) + (j : ℤ) = ((n + j : ℕ) : ℤ) := by push_cast; ring
    rw [hidx, h2]
    congr 1
    rw [pow_add]
    ring

/-- The tail index after a shift: `B ≤ tailIdx (σ^j q)` as soon as `B + j ≤ tailIdx q`. -/
theorem le_tailIdx_shiftZ_nat {a : ℝ} {h : ℂ → ℂ} {q : ChainData}
    (hex : ∃ N : ℕ, TailP a h q N) {j B : ℕ} (hle : B + j ≤ tailIdx a h q) :
    B ≤ tailIdx a h (shiftZ a (j : ℤ) q) := by
  have hjt : j ≤ tailIdx a h q := by omega
  have hshift : TailP a h (shiftZ a (j : ℤ) q) (tailIdx a h q - j) := by
    rw [TailP_shiftZ_nat, Nat.sub_add_cancel hjt]
    exact TailP_tailIdx hex
  have hex' : ∃ N : ℕ, TailP a h (shiftZ a (j : ℤ) q) N := ⟨_, hshift⟩
  have h2 : TailP a h q (tailIdx a h (shiftZ a (j : ℤ) q) + j) :=
    (TailP_shiftZ_nat j _ q).mp (TailP_tailIdx hex')
  have h3 : tailIdx a h q ≤ tailIdx a h (shiftZ a (j : ℤ) q) + j := tailIdx_le hex h2
  omega

end

end Work.EQ

namespace Work.EQ

open Filter _root_.Topology
open Complex
open Classical

noncomputable section

/-- **The far-end promotion hypothesis.** `far_reading_drop` identifies the far end of a chain at
depth `N + m` with the `m`-th suffix of the far-end word at depth `N`. -/
theorem far_reading_drop {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N : ℕ}
    {q : ChainData} (hq : IsChain a h q) :
    ∀ m : ℕ, m ≤ tailIdx a h (shiftZ a (N : ℤ) (mirrorChain q)) →
      q.1 (-(((N + m : ℕ)) : ℤ)) =
        eqMirror (fan a h
          ((fwdW a (tailIdx a h (shiftZ a (N : ℤ) (mirrorChain q)))
            (shiftZ a (N : ℤ) (mirrorChain q))).drop m)
          (((eqLam a : ℝ) : ℂ) ^ (N + m) * q.2.2)) := by
  set Q : ChainData := shiftZ a (N : ℤ) (mirrorChain q) with hQ
  set M : ℕ := tailIdx a h Q with hM
  have hQc : IsChain a h Q := isChain_shiftZ ha0 ha1 (isChain_mirrorChain hq) (N : ℤ)
  have htail : Q.1 (M : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ M * Q.2.1) :=
    TailP_of_isChain hQc M le_rfl
  intro m hm
  have hread := chain_reading_of_tail hQc htail m hm
  have hQ0 : Q.1 (m : ℤ) = eqMirror (q.1 (-(((N + m : ℕ)) : ℤ))) := by
    rw [hQ, shiftZ_fst, mirrorChain_fst]
    congr 2
    push_cast
    ring
  have hpsi : Q.2.1 = (((eqLam a : ℝ) : ℂ) ^ N) * q.2.2 := by
    rw [hQ, shiftZ_psi1, mirrorChain_psi1, zpow_natCast]
  have harg : (((eqLam a : ℝ) : ℂ) ^ m * Q.2.1)
      = (((eqLam a : ℝ) : ℂ) ^ (N + m) * q.2.2) := by
    rw [hpsi, pow_add]; ring
  calc q.1 (-(((N + m : ℕ)) : ℤ))
      = eqMirror (Q.1 (m : ℤ)) := by rw [hQ0, eqMirror_invol]
    _ = eqMirror (fan a h ((fwdW a M Q).drop m) (((eqLam a : ℝ) : ℂ) ^ m * Q.2.1)) := by
          rw [hread]
    _ = eqMirror (fan a h ((fwdW a M Q).drop m) (((eqLam a : ℝ) : ℂ) ^ (N + m) * q.2.2)) := by
          rw [harg]

theorem charValSet_subset_CharSet {a : ℝ} {h : ℂ → ℂ} : charValSet a h ⊆ CharSet a h := by
  rintro μ (rfl | ⟨ε, hε, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨ε, hε, rfl⟩

theorem CharSet_subset_charValSet {a : ℝ} {h : ℂ → ℂ} : CharSet a h ⊆ charValSet a h := by
  rintro μ (h1 | ⟨ε, hε, rfl⟩)
  · exact Or.inl h1
  · exact Or.inr ⟨ε, hε, rfl⟩

theorem CharSet_countable (a : ℝ) (h : ℂ → ℂ) : (CharSet a h).Countable :=
  (countable_charValSet a h).mono CharSet_subset_charValSet

theorem eqMirror_continuous : Continuous (eqMirror : ℂ × ℂ → ℂ × ℂ) := by
  unfold eqMirror
  fun_prop

theorem CharSet_norm_le_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {μ : ℂ} (hμ : μ ∈ CharSet a h) : ‖μ‖ ≤ 1 :=
  LTBV.ltbv_charValSet_norm_le_one ha0 ha1 hh (CharSet_subset_charValSet hμ)

theorem CharSet_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {μ : ℂ} (hμ : μ ∈ CharSet a h) : μ ≠ 0 :=
  LTBV.ltbv_charValSet_ne_zero ha0 ha1 hh (CharSet_subset_charValSet hμ)

/-- **The one-sided statement.**  If the forward tails of the cluster chains are unbounded, the
junction data of `Work.EQ.LTBV.junction_value_min` can be produced with words of a common length
`N` (the depth of the junction), and with a non-trivial characteristic value. -/
theorem junction_forward {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ δ₀ →
      ∀ {r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < δ →
      ∀ {c₀ : ℂ}, c₀ ≠ 0 →
      ∀ {Z : Set ℂ} {X : ℂ → ℕ → ChainData},
        ¬ Z.Countable → (∀ z ∈ Z, r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂) →
        (∀ z ∈ Z, ∀ k, IsChain a h (X z k)) →
        (∀ z ∈ Z, Tendsto (fun k => (X z k).2.1) atTop (nhds z)) →
        (∀ z ∈ Z, Tendsto (fun k => (X z k).2.1 * (X z k).2.2) atTop (nhds c₀)) →
        (∀ z ∈ Z, ∀ B : ℕ, ∃ k, B ≤ tailIdx a h (X z k)) →
        ∃ (N : ℕ) (ε η s : List Bool) (μ₁ μ₂ : ℂ),
          ε.length = N ∧ η.length = N ∧ s.length = N ∧
          μ₁ ∈ CharSet a h ∧ μ₂ ∈ CharSet a h ∧ (μ₁ ≠ 1 ∨ μ₂ ≠ 1) ∧ μ₁ * μ₂ ≠ 0 ∧
          ¬ {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ ∧
              ‖((eqLam a : ℝ) : ℂ) ^ N * (μ₁ * μ₂ * c₀ / w)‖ < δ ∧
              bwdP a s (fan a h ε w) =
                eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (μ₁ * μ₂ * c₀ / w)))}.Countable := by
  obtain ⟨δf, Ke, Lam, hδf, hKe, hLam, hfan⟩ := FanUniform.fan_uniform_estimates ha0 ha1 hh
  have hfan_an : ∀ ε : List Bool, AnalyticOnNhd ℂ (fan a h ε) (Metric.ball (0 : ℂ) δf) :=
    fun ε => (hfan ε).1
  have hfan_est : ∀ (ε : List Bool) (u : ℂ), u ∈ Metric.ball (0 : ℂ) δf →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ :=
    fun ε => (hfan ε).2
  have hctr : ∀ ε : List Bool, ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k :=
    fun ε => (FanSep.axis_walk ha0 ha1 hh).2 ε |>.2
  obtain ⟨δ₂, hδ₂, hdeg⟩ := bwdP_fan_degenerate_countable ha0 ha1 hh
  obtain ⟨δgap, hδgap, hgap0⟩ := FanTri.fan_gap_unif ha0 ha1 hh
  obtain ⟨δT, hδT, hTrich⟩ := JNT.exists_Trich ha0 ha1 hh
  obtain ⟨δmw, hδmw, hmw⟩ := LTBV.minimal_word_last_letter_bounded ha0 ha1 hh
  obtain ⟨δl, hδl, hleaf⟩ := LTBV.exists_leaf_radius ha0 ha1 hh
  have hlam0 : (0 : ℝ) < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  set K : ℝ := max Ke Lam with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le hKe (le_max_left _ _)
  refine ⟨min δf (min δ₂ (min δmw (min δl (min δgap (min δT (1 / (16 * K))))))),
    lt_min hδf (lt_min hδ₂ (lt_min hδmw (lt_min hδl (lt_min hδgap
      (lt_min hδT (div_pos one_pos (by linarith))))))), ?_⟩
  intro δ hδ hδδ₀ r₁ r₂ hr₁ hr₁₂ hr₂δ c₀ hc₀ Z X hZ hZann hX hX1 hX2 htails
  have hδf' : δ ≤ δf := le_trans hδδ₀ (min_le_left δf _)
  have hδ₂' : δ ≤ δ₂ := le_trans hδδ₀ (le_trans (min_le_right δf _) (min_le_left δ₂ _))
  have hδmw' : δ ≤ δmw := le_trans hδδ₀
    (le_trans (min_le_right δf _) (le_trans (min_le_right δ₂ _) (min_le_left δmw _)))
  have hδl' : δ ≤ δl := le_trans hδδ₀ (le_trans (min_le_right δf _)
    (le_trans (min_le_right δ₂ _) (le_trans (min_le_right δmw _) (min_le_left δl _))))
  have hδgap' : δ ≤ δgap := le_trans hδδ₀ (le_trans (min_le_right δf _)
    (le_trans (min_le_right δ₂ _) (le_trans (min_le_right δmw _)
      (le_trans (min_le_right δl _) (min_le_left δgap _)))))
  have hδT' : δ ≤ δT := le_trans hδδ₀ (le_trans (min_le_right δf _)
    (le_trans (min_le_right δ₂ _) (le_trans (min_le_right δmw _)
      (le_trans (min_le_right δl _) (le_trans (min_le_right δgap _) (min_le_left δT _))))))
  have hδK : δ ≤ 1 / (16 * K) := le_trans hδδ₀ (le_trans (min_le_right δf _)
    (le_trans (min_le_right δ₂ _) (le_trans (min_le_right δmw _)
      (le_trans (min_le_right δl _) (le_trans (min_le_right δgap _)
        (min_le_right δT _))))))
  have hKδ : K * δ ≤ 1 / 16 := by
    have h1 : K * δ ≤ K * (1 / (16 * K)) := mul_le_mul_of_nonneg_left hδK hKpos.le
    have h2 : K * (1 / (16 * K)) = 1 / 16 := by field_simp
    linarith
  have htri : JNT.Trich a h δ := JNT.Trich_mono hTrich hδT'
  have hcont : ∀ ε : List Bool, ContinuousOn (fan a h ε) (Metric.ball (0 : ℂ) δ) := fun ε =>
    (hfan_an ε).continuousOn.mono (Metric.ball_subset_ball hδf')
  have hest : ∀ (ε : List Bool) (u : ℂ), ‖u‖ < δf →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ :=
    fun ε u hu => hfan_est ε u (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hu)
  have hgap : ∀ (ε₀ : List Bool) (s : ℕ → ℕ) (C : ℕ → List Bool) (μ : ℂ),
      Tendsto s atTop atTop → (∀ k, fan a h (C k) 0 = ((-1 / 2 : ℂ), (0 : ℂ))) →
      (∀ k, charVal a h (C k) = μ) →
      TendstoUniformlyOn (fun k => fan a h (ε₀ ++ List.replicate (s k) true ++ C k))
        (fun u => fan a h ε₀ (μ * u)) atTop (Metric.ball (0 : ℂ) δ) :=
    fun ε₀ s C μ hs hC hμ => (hgap0 ε₀ s C μ hs hC hμ).mono (Metric.ball_subset_ball hδgap')
  -- the depth `N₀`
  set R : ℝ := ‖c₀‖ / r₁ + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  obtain ⟨N₀, hN₀δ, hN₀K⟩ : ∃ N : ℕ, (eqLam a) ^ N * R < δ ∧ K * ((eqLam a) ^ N * R) ≤ 1 / 16 := by
    have hlim : Tendsto (fun n : ℕ => (eqLam a) ^ n * R) atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const R
    have hpos : 0 < min δ (1 / (16 * K)) := lt_min hδ (div_pos one_pos (by linarith))
    obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hpos)).exists
    refine ⟨n, lt_of_lt_of_le hn (min_le_left _ _), ?_⟩
    have h2 : (eqLam a) ^ n * R < 1 / (16 * K) := lt_of_lt_of_le hn (min_le_right _ _)
    have h3 : K * ((eqLam a) ^ n * R) < 1 / 16 := by
      rw [lt_div_iff₀ (by linarith)] at h2
      linarith
    exact le_of_lt h3
  have hpow_mono_gen : ∀ {M M' : ℕ}, M' ≤ M → (eqLam a) ^ M ≤ (eqLam a) ^ M' := by
    intro M M' hM
    have h2 : M = M' + (M - M') := (Nat.add_sub_cancel' hM).symm
    rw [h2, pow_add]
    exact mul_le_of_le_one_right (pow_nonneg hlam0.le M') (pow_le_one₀ hlam0.le hlam1.le)
  have hpow_mono : ∀ {M : ℕ}, N₀ ≤ M → (eqLam a) ^ M ≤ (eqLam a) ^ N₀ :=
    fun hM => hpow_mono_gen hM
  have level_bound : ∀ {M : ℕ}, N₀ ≤ M → ∀ z : ℂ, r₁ ≤ ‖z‖ →
      (eqLam a) ^ M * ‖c₀ / z‖ ≤ (eqLam a) ^ N₀ * R := by
    intro M hM z hzr
    have hb : ‖c₀ / z‖ ≤ ‖c₀‖ / r₁ := by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hr₁ hzr
    calc (eqLam a) ^ M * ‖c₀ / z‖ ≤ (eqLam a) ^ N₀ * ‖c₀ / z‖ :=
          mul_le_mul_of_nonneg_right (hpow_mono hM) (norm_nonneg _)
      _ ≤ (eqLam a) ^ N₀ * (‖c₀‖ / r₁) := mul_le_mul_of_nonneg_left hb (pow_nonneg hlam0.le N₀)
      _ ≤ (eqLam a) ^ N₀ * R := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlam0.le N₀)
          rw [hRdef]; linarith
  have level_lt : ∀ {M : ℕ}, N₀ ≤ M → ∀ z : ℂ, r₁ ≤ ‖z‖ →
      ‖(((eqLam a : ℝ) : ℂ) ^ M * (c₀ / z))‖ < δ := by
    intro M hM z hzr
    have h1 : ‖(((eqLam a : ℝ) : ℂ) ^ M * (c₀ / z))‖ = (eqLam a) ^ M * ‖c₀ / z‖ := by
      rw [norm_mul, h0jc_norm_lamC_pow ha0 ha1 M]
    rw [h1]
    exact lt_of_le_of_lt (level_bound hM z hzr) hN₀δ
  have level_small : ∀ {M : ℕ}, N₀ ≤ M → ∀ z : ℂ, r₁ ≤ ‖z‖ →
      K * ‖(((eqLam a : ℝ) : ℂ) ^ M * (c₀ / z))‖ ≤ 1 / 8 := by
    intro M hM z hzr
    have h1 : ‖(((eqLam a : ℝ) : ℂ) ^ M * (c₀ / z))‖ = (eqLam a) ^ M * ‖c₀ / z‖ := by
      rw [norm_mul, h0jc_norm_lamC_pow ha0 ha1 M]
    rw [h1]
    calc K * ((eqLam a) ^ M * ‖c₀ / z‖) ≤ K * ((eqLam a) ^ N₀ * R) :=
          mul_le_mul_of_nonneg_left (level_bound hM z hzr) hKpos.le
      _ ≤ 1 / 16 := hN₀K
      _ ≤ 1 / 8 := by norm_num
  -- the `ψ₂`-convergence of the cluster
  have hψ₂lim : ∀ z ∈ Z, Tendsto (fun k => (X z k).2.2) atTop (nhds (c₀ / z)) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h0
      have h1 := (hZann z hz).1
      rw [h0, norm_zero] at h1
      linarith
    have hdiv : Tendsto (fun k => (X z k).2.1 * (X z k).2.2 / (X z k).2.1) atTop
        (nhds (c₀ / z)) := (hX2 z hz).div (hX1 z hz) hz0
    refine hdiv.congr' ?_
    filter_upwards with k
    exact mul_div_cancel_left₀ _ (hX z hz k).2.1
  -- the cutoff at an arbitrary depth `≥ N₀`
  have hgen : ∀ {M : ℕ}, N₀ ≤ M → ∀ z ∈ Z, ∃ K₀ : ℕ, ∀ k ≥ K₀,
      ‖(X z k).2.1‖ < δ ∧
      ‖(((eqLam a : ℝ) : ℂ) ^ M * (X z k).2.2)‖ < δ ∧
      LaNnas.UnNear a ((X z k).1 (-(M : ℤ))) (1 / 4) := by
    intro M hM z hz
    have hzann := hZann z hz
    have hzδ : ‖z‖ < δ := lt_of_le_of_lt hzann.2 hr₂δ
    have hψ₂ : Tendsto (fun k => (X z k).2.2) atTop (nhds (c₀ / z)) := hψ₂lim z hz
    have hLnorm := level_lt hM z hzann.1
    have hKnorm := level_small hM z hzann.1
    have hev1 : ∀ᶠ k in atTop, ‖(X z k).2.1‖ < δ := (hX1 z hz).norm.eventually (eventually_lt_nhds hzδ)
    have hev2 : ∀ᶠ k in atTop, ‖(((eqLam a : ℝ) : ℂ) ^ M * (X z k).2.2)‖ < δ :=
      ((hψ₂.const_mul (((eqLam a : ℝ) : ℂ) ^ M)).norm).eventually (eventually_lt_nhds hLnorm)
    have hev4 : ∀ᶠ k in atTop, ‖(((eqLam a : ℝ) : ℂ) ^ M * (X z k).2.2)‖ < δf :=
      ((hψ₂.const_mul (((eqLam a : ℝ) : ℂ) ^ M)).norm).eventually
        (eventually_lt_nhds (lt_of_lt_of_le hLnorm hδf'))
    have hev3 : ∀ᶠ k in atTop,
        K * ‖(((eqLam a : ℝ) : ℂ) ^ M * (X z k).2.2)‖ < 1 / 4 :=
      (((hψ₂.const_mul (((eqLam a : ℝ) : ℂ) ^ M)).norm).const_mul K).eventually
        (eventually_lt_nhds (lt_of_le_of_lt hKnorm (by norm_num)))
    have hev5 : ∀ᶠ k in atTop, LaNnas.UnNear a ((X z k).1 (-(M : ℤ))) (1 / 4) := by
      filter_upwards [hev3, hev4] with k hk3 hk4
      exact (LTBV.ltbv_farend_unNear ha0 ha1 hest hctr (hX z hz k) hk4).mono (le_of_lt hk3)
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (hev1.and (hev2.and hev5))
    exact ⟨K₀, fun k hk => ⟨(hK₀ k hk).1, (hK₀ k hk).2.1, (hK₀ k hk).2.2⟩⟩
  have hgenT : ∀ {M : ℕ}, N₀ ≤ M → ∀ z : ℂ, ∃ K₀ : ℕ, z ∈ Z → (∀ k ≥ K₀,
      ‖(X z k).2.1‖ < δ ∧
      ‖(((eqLam a : ℝ) : ℂ) ^ M * (X z k).2.2)‖ < δ ∧
      LaNnas.UnNear a ((X z k).1 (-(M : ℤ))) (1 / 4)) := by
    intro M hM z
    by_cases hz : z ∈ Z
    · obtain ⟨K₀, hK⟩ := hgen hM z hz
      exact ⟨K₀, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hz⟩
  have hcutT₀ : ∀ z : ℂ, ∃ K₀ : ℕ, z ∈ Z → (∀ k ≥ K₀,
      ‖(X z k).2.1‖ < δ ∧
      ‖(((eqLam a : ℝ) : ℂ) ^ N₀ * (X z k).2.2)‖ < δ ∧
      LaNnas.UnNear a ((X z k).1 (-(N₀ : ℤ))) (1 / 4)) := hgenT (M := N₀) le_rfl
  choose Kz hKz using hcutT₀
  -- the near end: the minimal words and the stable trichotomy
  have hstable : ∀ z : ℂ, ∃ (εs : ℕ → List Bool) (ε₀ : List Bool) (μ₁ : ℂ) (Φ : ℕ → ℕ),
      z ∈ Z → (μ₁ ∈ CharSet a h ∧ μ₁ ≠ 1 ∧ ‖μ₁‖ ≤ 1 ∧ StrictMono Φ ∧ (∀ k, Kz z ≤ Φ k) ∧
      (∀ k, (X z (Φ k)).1 0 = fan a h (εs k) ((X z (Φ k)).2.1)) ∧
      (∀ k, (εs k).getLast? = some false) ∧
      Tendsto (fun k => fan a h (εs k) ((X z (Φ k)).2.1)) atTop
        (nhds (fan a h ε₀ (μ₁ * z)))) := by
    intro z
    by_cases hz : z ∈ Z
    swap
    · exact ⟨fun _ => [], [], 0, id, fun h => absurd h hz⟩
    have hzδ : ‖z‖ < δ := lt_of_le_of_lt (hZann z hz).2 hr₂δ
    obtain ⟨ψ, hψmono, hψle⟩ := exists_strictMono_length
      (ε := fun k => List.replicate (tailIdx a h (X z k)) false)
      (fun B => by obtain ⟨k, hk⟩ := htails z hz B; exact ⟨k, by rw [List.length_replicate]; exact hk⟩)
    set j : ℕ → ℕ := fun k => ψ (k + Kz z + 1) with hj
    have hjmono : StrictMono j := fun p q h => hψmono (by omega)
    have hjge : ∀ k, Kz z ≤ j k := by
      intro k
      have h1 : k + Kz z + 1 ≤ j k := hψmono.id_le _
      omega
    have hjle : ∀ k, k + 1 ≤ tailIdx a h (X z (j k)) := by
      intro k
      have h1 := hψle (k + Kz z + 1)
      simp only [List.length_replicate] at h1
      have h2 : j k = ψ (k + Kz z + 1) := rfl
      rw [h2]
      omega
    have hw : ∀ k, ∃ ε : List Bool,
        (X z (j k)).1 0 = fan a h ε ((X z (j k)).2.1) ∧
        ε.length = tailIdx a h (X z (j k)) ∧ ε.getLast? = some false := by
      intro k
      have hchain : IsChain a h (X z (j k)) := hX z hz _
      have hsmall : ‖(X z (j k)).2.1‖ < δmw :=
        lt_of_lt_of_le (hKz z hz (j k) (hjge k)).1 hδmw'
      obtain ⟨ε, h1, h2, h3⟩ := hmw hchain hsmall
      exact ⟨ε, h1, h2, h3 (by have := hjle k; omega)⟩
    choose εs hεs using hw
    obtain ⟨ε₀, μ₁C, hμ₁mem, hμ₁ne, φ, hφmono, hconv⟩ :=
      stable_trichotomy_v2_of_minimal_words ha0 ha1 hh hδ hcont htri hgap
        (N := N₀) (W := z) (x := fun k => X z (j k)) (ε := εs)
        (fun k => hX z hz _)
        (fun k => (hεs k).1)
        (fun k => (hKz z hz (j k) (hjge k)).1)
        (fun k => (hεs k).2.2)
        (fun B => ⟨B, le_trans (Nat.le_succ B) (by rw [(hεs B).2.1]; exact hjle B)⟩)
        (fun k => (hKz z hz (j k) (hjge k)).2.2)
        ((hX1 z hz).comp hjmono.tendsto_atTop)
        hzδ
    exact ⟨fun k => εs (φ k), ε₀, μ₁C, fun k => j (φ k), fun _ =>
      ⟨hμ₁mem, hμ₁ne, CharSet_norm_le_one ha0 ha1 hh hμ₁mem,
        hjmono.comp hφmono, fun k => hjge (φ k), fun k => (hεs (φ k)).1,
        fun k => (hεs (φ k)).2.2, hconv⟩⟩
  choose εsz ε₀z μ₁z Φz hdata using hstable
  -- pigeonhole over `(ε₀, μ₁)`
  have hZ₁ex : ∃ (ε₀ : List Bool) (μ₁ : ℂ), μ₁ ∈ CharSet a h ∧ μ₁ ≠ 1 ∧
      ¬ {z | z ∈ Z ∧ ε₀z z = ε₀ ∧ μ₁z z = μ₁}.Countable := by
    by_contra hcon
    have hcon' : ∀ (ε₀ : List Bool) (μ₁ : ℂ), μ₁ ∈ CharSet a h → μ₁ ≠ 1 →
        {z | z ∈ Z ∧ ε₀z z = ε₀ ∧ μ₁z z = μ₁}.Countable := by
      intro ε₀ μ₁ hmem hne
      by_contra hc
      exact hcon ⟨ε₀, μ₁, hmem, hne, hc⟩
    have hsub : Z ⊆ ⋃ (p : List Bool × ℂ),
        ⋃ (_ : p ∈ Set.univ ×ˢ (CharSet a h \ {1})),
          {z | z ∈ Z ∧ ε₀z z = p.1 ∧ μ₁z z = p.2} := by
      intro z hz
      refine Set.mem_iUnion.mpr ⟨(ε₀z z, μ₁z z), ?_⟩
      exact Set.mem_iUnion.mpr ⟨⟨trivial, (hdata z hz).1, (hdata z hz).2.1⟩, hz, rfl, rfl⟩
    have hc : (⋃ (p : List Bool × ℂ),
        ⋃ (_ : p ∈ Set.univ ×ˢ (CharSet a h \ {1})),
          {z | z ∈ Z ∧ ε₀z z = p.1 ∧ μ₁z z = p.2}).Countable := by
      refine Set.Countable.biUnion
        (Set.countable_univ.prod ((CharSet_countable a h).mono ?_)) ?_
      · rintro x ⟨hx, -⟩
        exact hx
      · rintro p ⟨-, hp⟩
        exact hcon' p.1 p.2 hp.1 hp.2
    exact hZ (hc.mono hsub)
  obtain ⟨ε₀, μ₁, hμ₁mem, hμ₁ne1, hZ₁unc⟩ := hZ₁ex
  have hμ₁ne : μ₁ ≠ 0 := CharSet_ne_zero ha0 ha1 hh hμ₁mem
  have hμ₁norm : ‖μ₁‖ ≤ 1 := CharSet_norm_le_one ha0 ha1 hh hμ₁mem
  set Z₁ : Set ℂ := {z | z ∈ Z ∧ ε₀z z = ε₀ ∧ μ₁z z = μ₁} with hZ₁def
  -- the junction depth
  set N : ℕ := max N₀ ε₀.length with hNdef
  have hNN₀ : N₀ ≤ N := le_max_left _ _
  have hNlen : ε₀.length ≤ N := le_max_right _ _
  have hcutT : ∀ z : ℂ, ∃ K₀ : ℕ, z ∈ Z → (∀ k ≥ K₀,
      ‖(X z k).2.1‖ < δ ∧
      ‖(((eqLam a : ℝ) : ℂ) ^ N * (X z k).2.2)‖ < δ ∧
      LaNnas.UnNear a ((X z k).1 (-(N : ℤ))) (1 / 4)) := hgenT hNN₀
  choose Kz' hKz' using hcutT
  -- the far end: at each level the words are the forward words of the mirror chains
  have hfar : ∀ z : ℂ, ∃ (μ₂ : ℂ) (η₀ : List Bool) (χ : ℕ → List Bool) (Ψ : ℕ → ℕ),
      z ∈ Z₁ → (μ₂ ∈ charValSet a h ∧ StrictMono Ψ ∧ (∀ k, Kz' z ≤ Ψ k) ∧
      Tendsto (fun k => (X z (Ψ k)).1 0) atTop
        (nhds (fan a h ε₀ (μ₁ * z))) ∧
      (∀ k, (X z (Ψ k)).1 (-(((N + η₀.length : ℕ)) : ℤ)) =
        eqMirror (fan a h (χ k)
          ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (X z (Ψ k)).2.2))) ∧
      Tendsto (fun k => eqMirror (fan a h (χ k)
          ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (X z (Ψ k)).2.2))) atTop
        (nhds (eqMirror (germC a h
          (μ₂ * ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z))))))) := by
    intro z
    by_cases hz : z ∈ Z₁
    swap
    · exact ⟨1, [], (fun _ => []), id, fun h => absurd h hz⟩
    have hzZ : z ∈ Z := hz.1
    have hΦmono : StrictMono (Φz z) := (hdata z hzZ).2.2.2.1
    have hΦge : ∀ k, Kz z ≤ Φz z k := (hdata z hzZ).2.2.2.2.1
    have hread : ∀ k, (X z (Φz z k)).1 0 = fan a h (εsz z k) ((X z (Φz z k)).2.1) :=
      (hdata z hzZ).2.2.2.2.2.1
    have hzε : ε₀z z = ε₀ := hz.2.1
    have hzμ : μ₁z z = μ₁ := hz.2.2
    have hconv : Tendsto (fun k => fan a h (εsz z k) ((X z (Φz z k)).2.1)) atTop
        (nhds (fan a h ε₀ (μ₁ * z))) := by
      have h1 := (hdata z hzZ).2.2.2.2.2.2.2
      rw [hzε, hzμ] at h1
      exact h1
    have hzann := hZann z hzZ
    set jz : ℕ → ℕ := fun k => Φz z (k + Kz' z) with hjz
    have hjzmono : StrictMono jz := fun p q h => hΦmono (by omega)
    have hjzge : ∀ k, Kz' z ≤ jz k := by
      intro k
      have h1 : k + Kz' z ≤ jz k := hΦmono.id_le _
      omega
    have hqchain : ∀ k, IsChain a h (X z (jz k)) := fun k => hX z hzZ _
    have hqsmall : ∀ k, ‖(X z (jz k)).2.1‖ < δ :=
      fun k => (hKz' z hzZ (jz k) (hjzge k)).1
    have hQchain : ∀ k, IsChain a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz k)))) :=
      fun k => isChain_shiftZ ha0 ha1 (isChain_mirrorChain (hqchain k)) (N : ℤ)
    have hQpsi : ∀ k, (shiftZ a (N : ℤ) (mirrorChain (X z (jz k)))).2.1
        = (((eqLam a : ℝ) : ℂ) ^ N) * (X z (jz k)).2.2 := by
      intro k; rw [shiftZ_psi1, mirrorChain_psi1, zpow_natCast]
    have hQsmall : ∀ k, ‖(shiftZ a (N : ℤ) (mirrorChain (X z (jz k)))).2.1‖ < δ := by
      intro k; rw [hQpsi k]; exact (hKz' z hzZ (jz k) (hjzge k)).2.1
    have hQun : ∀ k, LaNnas.UnNear a
        ((shiftZ a (N : ℤ) (mirrorChain (X z (jz k)))).1 (-(N : ℤ))) (1 / 4) := by
      intro k
      have h1 : (shiftZ a (N : ℤ) (mirrorChain (X z (jz k)))).1 (-(N : ℤ))
          = eqMirror ((X z (jz k)).1 0) := by
        rw [shiftZ_fst, mirrorChain_fst]; simp
      rw [h1]
      refine h0jc_unNear_eqMirror ((h0jc_near_snNear hest hctr (hread (k + Kz' z)) ?_).mono ?_)
      · exact lt_of_lt_of_le (hqsmall k) hδf'
      · calc max Ke Lam * ‖(X z (jz k)).2.1‖ ≤ K * δ :=
              mul_le_mul le_rfl (hqsmall k).le (norm_nonneg _) hKpos.le
          _ ≤ 1 / 16 := hKδ
          _ ≤ 1 / 4 := by norm_num
    have hQread : ∀ k, (shiftZ a (N : ℤ) (mirrorChain (X z (jz k)))).1 0
        = fan a h (fwdW a (tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz k)))))
            (shiftZ a (N : ℤ) (mirrorChain (X z (jz k)))))
          ((shiftZ a (N : ℤ) (mirrorChain (X z (jz k)))).2.1) := by
      intro k
      simpa using chain_reading_of_tail (hQchain k)
        (TailP_of_isChain (hQchain k)
          (tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz k))))) le_rfl) 0 (Nat.zero_le _)
    have hQlim : Tendsto (fun k => (shiftZ a (N : ℤ) (mirrorChain (X z (jz k)))).2.1) atTop
        (nhds ((((eqLam a : ℝ) : ℂ) ^ N) * (c₀ / z))) := by
      have h1 : Tendsto (fun k => (X z (jz k)).2.2) atTop (nhds (c₀ / z)) :=
        (hψ₂lim z hzZ).comp hjzmono.tendsto_atTop
      exact h1.const_mul _
    have hWlt : ‖((((eqLam a : ℝ) : ℂ) ^ N) * (c₀ / z))‖ < δ := level_lt hNN₀ z hzann.1
    obtain ⟨φ, hφm, hcase⟩ := htri
      (fun k => fwdW a (tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz k)))))
        (shiftZ a (N : ℤ) (mirrorChain (X z (jz k)))))
    have hmono : StrictMono (fun k : ℕ => φ k + Kz' z) := fun p q h => by
      have h2 : φ p < φ q := hφm h
      show φ p + Kz' z < φ q + Kz' z
      omega
    have hnear0 : Tendsto (fun k => (X z (jz (φ k))).1 0) atTop
        (nhds (fan a h ε₀ (μ₁ * z))) := by
      refine (hconv.comp hmono.tendsto_atTop).congr (fun k => ?_)
      exact (hread (φ k + Kz' z)).symm
    rcases hcase with ⟨η₀, hconst⟩ | ⟨η₀, ε₁, s, C, hst, hword, hC, he₁, him, hre0, hre1⟩ |
      ⟨hvis, hflat⟩
    · -- case (i): the words are literally constant
      refine ⟨1, η₀, (fun _ => ([] : List Bool)), (fun k => jz (φ k)), fun _ =>
        ⟨Or.inl rfl, ?_, ?_, hnear0, ?_, ?_⟩⟩
      · exact hjzmono.comp hφm
      · intro k; exact hjzge (φ k)
      · intro k
        have hMlen : η₀.length
            = tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))) := by
          rw [← hconst k]
          exact fwdW_length a _ _
        have hdrop := far_reading_drop ha0 ha1 (hqchain (φ k)) (η₀.length) hMlen.le
        have hw0 : (fwdW a (tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))))
            (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k)))))).drop η₀.length = [] := by
          have h2 : fwdW a (tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))))
              (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))) = η₀ := hconst k
          rw [h2]
          exact List.drop_eq_nil_of_le (le_refl _)
        rw [hw0] at hdrop
        simpa using hdrop
      · have hparam : Tendsto
            (fun k => ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (X z (jz (φ k))).2.2)) atTop
            (nhds ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z))) :=
          ((hψ₂lim z hzZ).comp (hjzmono.comp hφm).tendsto_atTop).const_mul _
        have hWmem : ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z)) ∈ Metric.ball (0 : ℂ) δf := by
          rw [Metric.mem_ball, dist_zero_right]
          exact lt_of_lt_of_le (level_lt (M := N + η₀.length) (by omega) z hzann.1) hδf'
        have hcf : ContinuousAt (fun u : ℂ => eqMirror (germC a h u))
            ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z)) :=
          eqMirror_continuous.continuousAt.comp
            ((hfan_an []).continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hWmem))
        have hres := hcf.tendsto.comp hparam
        rw [one_mul]
        exact hres
    · -- case (ii): the words split as a prefix, a run of principal letters and a returning word
      refine ⟨charVal a h ε₁, η₀,
        (fun k => List.replicate (s k) true ++ C k), (fun k => jz (φ k)), fun _ =>
        ⟨Or.inr ⟨ε₁, he₁, rfl⟩, hjzmono.comp hφm, (fun k => hjzge (φ k)), hnear0, ?_, ?_⟩⟩
      · intro k
        have hMlen : η₀.length
            ≤ tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))) := by
          have h2 : fwdW a (tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))))
              (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k)))))
              = η₀ ++ List.replicate (s k) true ++ C k := hword k
          have h3 : η₀.length
              ≤ (η₀ ++ List.replicate (s k) true ++ C k).length := by simp
          rw [← h2] at h3
          rw [fwdW_length] at h3
          exact h3
        have hdrop := far_reading_drop ha0 ha1 (hqchain (φ k)) (η₀.length) hMlen
        have hw0 : (fwdW a (tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))))
            (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k)))))).drop η₀.length
            = List.replicate (s k) true ++ C k := by
          have h2 : fwdW a (tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))))
              (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k)))))
              = η₀ ++ List.replicate (s k) true ++ C k := hword k
          rw [h2, List.append_assoc, List.drop_left]
        rw [hw0] at hdrop
        simpa using hdrop
      · have hparam : Tendsto
            (fun k => ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (X z (jz (φ k))).2.2)) atTop
            (nhds ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z))) :=
          ((hψ₂lim z hzZ).comp (hjzmono.comp hφm).tendsto_atTop).const_mul _
        have hWmem : ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z)) ∈ Metric.ball (0 : ℂ) δf := by
          rw [Metric.mem_ball, dist_zero_right]
          exact lt_of_lt_of_le (level_lt (M := N + η₀.length) (by omega) z hzann.1) hδf'
        have hWmemδ : ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z)) ∈ Metric.ball (0 : ℂ) δ :=
          by rw [Metric.mem_ball, dist_zero_right]
             exact level_lt (M := N + η₀.length) (by omega) z hzann.1
        have hmem_par : ∀ k, ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (X z (jz (φ k))).2.2)
            ∈ Metric.ball (0 : ℂ) δ := by
          intro k
          rw [Metric.mem_ball, dist_zero_right]
          have h1 : (eqLam a) ^ (N + η₀.length) ≤ (eqLam a) ^ N := hpow_mono_gen (by omega)
          have h2 : ‖((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (X z (jz (φ k))).2.2)‖
              = (eqLam a) ^ (N + η₀.length) * ‖(X z (jz (φ k))).2.2‖ := by
            rw [norm_mul, h0jc_norm_lamC_pow ha0 ha1]
          have h3 : ‖((((eqLam a : ℝ) : ℂ) ^ N) * (X z (jz (φ k))).2.2)‖
              = (eqLam a) ^ N * ‖(X z (jz (φ k))).2.2‖ := by
            rw [norm_mul, h0jc_norm_lamC_pow ha0 ha1]
          rw [h2]
          calc (eqLam a) ^ (N + η₀.length) * ‖(X z (jz (φ k))).2.2‖
              ≤ (eqLam a) ^ N * ‖(X z (jz (φ k))).2.2‖ :=
                mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
            _ = ‖((((eqLam a : ℝ) : ℂ) ^ N) * (X z (jz (φ k))).2.2)‖ := h3.symm
            _ < δ := (hKz' z hzZ (jz (φ k)) (hjzge (φ k))).2.1
        have huni := hgap ([] : List Bool) s C (charVal a h ε₁) hst
          (fun k => (hC k).1) (fun k => (hC k).2)
        have hwithin : Tendsto
            (fun k => ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (X z (jz (φ k))).2.2)) atTop
            (nhdsWithin ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z))
              (Metric.ball (0 : ℂ) δ)) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hparam
            (Eventually.of_forall hmem_par)
        have hcw : ContinuousWithinAt
            (fun u : ℂ => fan a h [] (charVal a h ε₁ * u)) (Metric.ball (0 : ℂ) δ)
            ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z)) := by
          have h1 : ContinuousAt (fun u : ℂ => charVal a h ε₁ * u)
              ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z)) :=
            continuousAt_const.mul continuousAt_id
          have hmem2 : charVal a h ε₁
              * ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z)) ∈ Metric.ball (0 : ℂ) δf := by
            rw [Metric.mem_ball, dist_zero_right, norm_mul]
            refine lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _)
              (CharSet_norm_le_one ha0 ha1 hh (Or.inr ⟨ε₁, he₁, rfl⟩))) ?_
            rw [Metric.mem_ball, dist_zero_right] at hWmem
            exact hWmem
          have h2 : ContinuousAt (fan a h []) (charVal a h ε₁
              * ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z))) :=
            (hfan_an []).continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hmem2)
          exact (h2.comp h1).continuousWithinAt
        have hres := huni.tendsto_comp hcw hwithin
        have h1 : Tendsto (fun k => eqMirror (fan a h
            ([] ++ List.replicate (s k) true ++ C k)
            ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (X z (jz (φ k))).2.2))) atTop
            (nhds (eqMirror (fan a h [] (charVal a h ε₁
              * ((((eqLam a : ℝ) : ℂ) ^ (N + η₀.length)) * (c₀ / z)))))) :=
          (eqMirror_continuous.tendsto _).comp hres
        exact h1.congr (fun k => by simp)
    · -- case (iii): excluded by the parity separation
      exfalso
      obtain ⟨η', hη'pos, hnotflat⟩ := LaTB.not_flat_of_unNear ha0 ha1 N
      obtain ⟨k, hk⟩ := (hflat η' hη'pos).exists
      have hmem : (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))).2.1 ∈ Metric.ball (0 : ℂ) δ := by
        rw [Metric.mem_ball, dist_zero_right]; exact hQsmall (φ k)
      obtain ⟨hf1, hf2⟩ := hk _ hmem
      obtain ⟨Y, hY⟩ := hctr (fwdW a (tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))))
        (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))))
      refine hnotflat (P := fun n => (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))).1 n)
        (u := (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))).2.1)
        (ε := fwdW a (tailIdx a h (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))))
          (shiftZ a (N : ℤ) (mirrorChain (X z (jz (φ k))))))
        (Y := Y) (fun n => (hQchain (φ k)).1 n) (hQread (φ k)) (hQun (φ k)) hY hf1 hf2
  choose μ₂z η₀z χz Ψz hfardata using hfar
  -- pigeonhole over `(η₀, μ₂)`
  have hZ₂ex : ∃ (η₀ : List Bool) (μ₂ : ℂ), μ₂ ∈ charValSet a h ∧
      ¬ {z | z ∈ Z₁ ∧ η₀z z = η₀ ∧ μ₂z z = μ₂}.Countable := by
    by_contra hcon
    have hcon' : ∀ (η₀ : List Bool) (μ₂ : ℂ), μ₂ ∈ charValSet a h →
        {z | z ∈ Z₁ ∧ η₀z z = η₀ ∧ μ₂z z = μ₂}.Countable := by
      intro η₀ μ₂ hmem
      by_contra hc
      exact hcon ⟨η₀, μ₂, hmem, hc⟩
    have hsub : Z₁ ⊆ ⋃ (p : List Bool × ℂ),
        ⋃ (_ : p ∈ Set.univ ×ˢ charValSet a h),
          {z | z ∈ Z₁ ∧ η₀z z = p.1 ∧ μ₂z z = p.2} := by
      intro z hz
      refine Set.mem_iUnion.mpr ⟨(η₀z z, μ₂z z), ?_⟩
      exact Set.mem_iUnion.mpr ⟨⟨trivial, (hfardata z hz).1⟩, hz, rfl, rfl⟩
    have hc : (⋃ (p : List Bool × ℂ),
        ⋃ (_ : p ∈ Set.univ ×ˢ charValSet a h),
          {z | z ∈ Z₁ ∧ η₀z z = p.1 ∧ μ₂z z = p.2}).Countable := by
      refine Set.Countable.biUnion
        (Set.countable_univ.prod (countable_charValSet a h)) ?_
      rintro p ⟨-, hp⟩
      exact hcon' p.1 p.2 hp
    exact hZ₁unc (hc.mono hsub)
  obtain ⟨η₀, μ₂, hμ₂cv, hZ₂unc⟩ := hZ₂ex
  have hμ₂mem : μ₂ ∈ CharSet a h := charValSet_subset_CharSet hμ₂cv
  have hμ₂ne : μ₂ ≠ 0 := CharSet_ne_zero ha0 ha1 hh hμ₂mem
  have hμ₂norm : ‖μ₂‖ ≤ 1 := CharSet_norm_le_one ha0 ha1 hh hμ₂mem
  set Z₂ : Set ℂ := {z | z ∈ Z₁ ∧ η₀z z = η₀ ∧ μ₂z z = μ₂} with hZ₂def
  set N'' : ℕ := N + η₀.length with hN''def
  have hN''ge : N ≤ N'' := by rw [hN''def]; omega
  -- the countable degenerate locus
  set D : Set ℂ := {w : ℂ | ‖w‖ < δ₂ ∧ ∃ σ : List Bool, σ.length ≤ N'' ∧
    bsq (subO1 a (bwdP a σ (fan a h ε₀ w))) = 0} with hDdef
  have hDc : D.Countable := hdeg ε₀ N''
  set Bad : Set ℂ := {z : ℂ | ∃ σ : List Bool, σ.length ≤ N'' ∧
    bsq (subO1 a (bwdP a σ (fan a h ε₀ (μ₁ * z)))) = 0} with hBaddef
  have hpre : ((fun z : ℂ => μ₁ * z) ⁻¹' D).Countable := by
    have hsub : ((fun z : ℂ => μ₁ * z) ⁻¹' D) ⊆ (fun w : ℂ => w / μ₁) '' D := by
      rintro z hz
      exact ⟨μ₁ * z, hz, by show μ₁ * z / μ₁ = z; exact mul_div_cancel_left₀ _ hμ₁ne⟩
    exact (hDc.image _).mono hsub
  have hbadZ : (Bad ∩ Z₂).Countable := by
    refine hpre.mono ?_
    rintro z ⟨hb, hzZ, hzε, hzμ⟩
    have hzZ₁ : z ∈ Z₁ := hzZ
    have hzann := hZann z hzZ₁.1
    have hlt : ‖μ₁ * z‖ < δ₂ := by
      calc ‖μ₁ * z‖ = ‖μ₁‖ * ‖z‖ := norm_mul _ _
        _ ≤ 1 * r₂ := mul_le_mul hμ₁norm hzann.2 (norm_nonneg _) zero_le_one
        _ = r₂ := one_mul _
        _ < δ := hr₂δ
        _ ≤ δ₂ := hδ₂'
    exact ⟨hlt, hb⟩
  have hZ₃unc : ¬ (Z₂ ∩ Badᶜ).Countable := by
    intro h
    refine hZ₂unc ((h.union hbadZ).mono ?_)
    intro z hz
    by_cases hb : z ∈ Bad
    · exact Or.inr ⟨hb, hz⟩
    · exact Or.inl ⟨hz, hb⟩
  have hgood : ∀ z ∈ Z₂ ∩ Badᶜ, ∀ σ : List Bool, σ.length ≤ N'' →
      bsq (subO1 a (bwdP a σ (fan a h ε₀ (μ₁ * z)))) ≠ 0 := by
    intro z hz σ hσ h0
    exact hz.2 ⟨σ, hσ, h0⟩
  -- the padding of the stable word and of the unstable word
  have hpad : ∀ {u : ℂ}, ‖u‖ < δ →
      fan a h (ε₀ ++ List.replicate (N'' - ε₀.length) true) u = fan a h ε₀ u :=
    fun hu => fan_append_replicate_true ha0 ha1
      (fun v hv => hleaf v (lt_of_lt_of_le hv hδl')) _ _ hu
  have hetaFan : ∀ {u : ℂ}, ‖u‖ < δ → fan a h (List.replicate N'' true) u = germC a h u :=
    fun hu => fan_replicate_true ha0 ha1
      (fun v hv => hleaf v (lt_of_lt_of_le hv hδl')) N'' hu
  -- the junction segment for a good point
  have hjunc : ∀ z : ℂ, ∃ s : List Bool, s.length = N'' ∧
      (z ∈ Z₂ ∩ Badᶜ →
        bwdP a s (fan a h (ε₀ ++ List.replicate (N'' - ε₀.length) true) (μ₁ * z)) =
          eqMirror (germC a h (μ₂ * ((((eqLam a : ℝ) : ℂ) ^ N'') * (c₀ / z))))) := by
    intro z
    by_cases hz : z ∈ Z₂ ∩ Badᶜ
    swap
    · exact ⟨List.replicate N'' true, by simp, fun h => absurd h hz⟩
    have hzZ₁ : z ∈ Z₁ := hz.1.1
    have hzZ : z ∈ Z := hzZ₁.1
    have hzann := hZann z hzZ
    have hzη : η₀z z = η₀ := hz.1.2.1
    have hzμ₂ : μ₂z z = μ₂ := hz.1.2.2
    have hdat := hfardata z hzZ₁
    have hΨmono : StrictMono (Ψz z) := hdat.2.1
    have hΨge : ∀ k, Kz' z ≤ Ψz z k := hdat.2.2.1
    have hnearlim := hdat.2.2.2.1
    have hfareq := hdat.2.2.2.2.1
    have hfarlim := hdat.2.2.2.2.2
    have hWlt' : ‖((((eqLam a : ℝ) : ℂ) ^ N'') * (c₀ / z))‖ < δ := by
      rw [hN''def]
      exact level_lt (M := N + η₀.length) (by omega) z hzann.1
    have hconv1 : Tendsto (fun k => (X z (Ψz z k)).1 0) atTop
        (nhds (fan a h (ε₀ ++ List.replicate (N'' - ε₀.length) true) (μ₁ * z))) := by
      have hw : fan a h (ε₀ ++ List.replicate (N'' - ε₀.length) true) (μ₁ * z)
          = fan a h ε₀ (μ₁ * z) := hpad (by
        rw [norm_mul]
        calc ‖μ₁‖ * ‖z‖ ≤ 1 * r₂ := mul_le_mul hμ₁norm hzann.2 (norm_nonneg _) zero_le_one
          _ = r₂ := one_mul _
          _ < δ := hr₂δ)
      rw [hw]
      exact hnearlim
    have hconv2 : Tendsto (fun k => (X z (Ψz z k)).1 (-(N'' : ℤ))) atTop
        (nhds (eqMirror (germC a h (μ₂ * ((((eqLam a : ℝ) : ℂ) ^ N'') * (c₀ / z)))))) := by
      have h1 : (fun k => eqMirror (fan a h (χz z k)
            ((((eqLam a : ℝ) : ℂ) ^ (N + (η₀z z).length)) * (X z (Ψz z k)).2.2)))
            = fun k => (X z (Ψz z k)).1 (-(((N + (η₀z z).length : ℕ)) : ℤ)) := by
        funext k
        exact (hfareq k).symm
      rw [hN''def, ← hzη, ← h1]
      rw [show μ₂z z = μ₂ from hzμ₂] at hfarlim
      exact hfarlim
    obtain ⟨s, hslen, hs⟩ := junction_limit_segment_len
      (q := fun k => X z (Ψz z k))
      (S := fan a h (ε₀ ++ List.replicate (N'' - ε₀.length) true) (μ₁ * z))
      (T := eqMirror (germC a h (μ₂ * ((((eqLam a : ℝ) : ℂ) ^ N'') * (c₀ / z)))))
      (fun k i hi => by
        have h1 : RegPair a ((X z (Ψz z k)).1 (-(((i : ℤ) + 1))))
            ((X z (Ψz z k)).1 (-(i : ℤ))) := by
          have h2 := (hX z hzZ (Ψz z k)).1 (-((i : ℤ) + 1))
          rwa [show -((i : ℤ) + 1) + 1 = -(i : ℤ) by ring] at h2
        exact h1)
      (fun σ hσ => by
        have hw : fan a h (ε₀ ++ List.replicate (N'' - ε₀.length) true) (μ₁ * z)
            = fan a h ε₀ (μ₁ * z) := hpad (by
          rw [norm_mul]
          calc ‖μ₁‖ * ‖z‖ ≤ 1 * r₂ := mul_le_mul hμ₁norm hzann.2 (norm_nonneg _) zero_le_one
            _ = r₂ := one_mul _
            _ < δ := hr₂δ)
        rw [hw]
        exact hgood z hz σ hσ)
      hconv1 hconv2
    exact ⟨s, hslen, fun _ => hs.symm⟩
  choose sz hszlen hszj using hjunc
  -- pigeonhole over the sign list
  have hZ₄ex : ∃ s : List Bool, s.length = N'' ∧
      ¬ {z | z ∈ Z₂ ∩ Badᶜ ∧ sz z = s}.Countable := by
    by_contra hcon
    have hcon' : ∀ s : List Bool, s.length = N'' →
        {z | z ∈ Z₂ ∩ Badᶜ ∧ sz z = s}.Countable := by
      intro s hs
      by_contra hc
      exact hcon ⟨s, hs, hc⟩
    have hsub : Z₂ ∩ Badᶜ ⊆ ⋃ (p : {s : List Bool // s.length = N''}),
        ⋃ (_ : p ∈ Set.univ), {z | z ∈ Z₂ ∩ Badᶜ ∧ sz z = p.1} := by
      intro z hz
      exact Set.mem_iUnion.mpr ⟨⟨sz z, hszlen z⟩, Set.mem_iUnion.mpr ⟨trivial, hz, rfl⟩⟩
    have hc : (⋃ (p : {s : List Bool // s.length = N''}),
        ⋃ (_ : p ∈ Set.univ), {z | z ∈ Z₂ ∩ Badᶜ ∧ sz z = p.1}).Countable := by
      refine Set.Countable.biUnion Set.countable_univ ?_
      rintro p -
      exact hcon' p.1 p.2
    exact hZ₃unc (hc.mono hsub)
  obtain ⟨s, hslen, hZ₄unc⟩ := hZ₄ex
  set Z₄ : Set ℂ := {z | z ∈ Z₂ ∩ Badᶜ ∧ sz z = s} with hZ₄def
  refine ⟨N'', ε₀ ++ List.replicate (N'' - ε₀.length) true, List.replicate N'' true, s,
    μ₁, μ₂, ?_, ?_, hslen, hμ₁mem, hμ₂mem, Or.inl hμ₁ne1, mul_ne_zero hμ₁ne hμ₂ne, ?_⟩
  · rw [List.length_append, List.length_replicate]
    exact Nat.add_sub_of_le (le_trans hNlen (by rw [hN''def]; omega))
  · simp
  · intro hcount
    refine hZ₄unc ?_
    have hsub : (fun z : ℂ => μ₁ * z) '' Z₄ ⊆ {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ ∧
        ‖((eqLam a : ℝ) : ℂ) ^ N'' * (μ₁ * μ₂ * c₀ / w)‖ < δ ∧
        bwdP a s (fan a h (ε₀ ++ List.replicate (N'' - ε₀.length) true) w) =
          eqMirror (fan a h (List.replicate N'' true)
            (((eqLam a : ℝ) : ℂ) ^ N'' * (μ₁ * μ₂ * c₀ / w)))} := by
      rintro w ⟨z, hz, rfl⟩
      have hzZ₂ : z ∈ Z₂ := hz.1.1
      have hzZ₁ : z ∈ Z₁ := hzZ₂.1
      have hzZ : z ∈ Z := hzZ₁.1
      have hzann := hZann z hzZ
      have hz0 : z ≠ 0 := by
        intro h0
        have h1 := hzann.1
        rw [h0, norm_zero] at h1
        linarith
      have hszz : sz z = s := hz.2
      have hfield : μ₁ * μ₂ * c₀ / (μ₁ * z) = μ₂ * (c₀ / z) := by
        rw [show μ₁ * μ₂ * c₀ = (μ₂ * c₀) * μ₁ by ring,
          show μ₁ * z = z * μ₁ by ring, mul_div_mul_right _ _ hμ₁ne]
        rw [mul_div_assoc]
      have hwlt : ‖μ₁ * z‖ < δ := by
        calc ‖μ₁ * z‖ = ‖μ₁‖ * ‖z‖ := norm_mul _ _
          _ ≤ 1 * r₂ := mul_le_mul hμ₁norm hzann.2 (norm_nonneg _) zero_le_one
          _ = r₂ := one_mul _
          _ < δ := hr₂δ
      have hnorm₂ : ‖(((eqLam a : ℝ) : ℂ) ^ N'') * (μ₂ * (c₀ / z))‖ < δ := by
        rw [norm_mul, h0jc_norm_lamC_pow ha0 ha1]
        calc (eqLam a) ^ N'' * ‖μ₂ * (c₀ / z)‖
            ≤ (eqLam a) ^ N'' * ‖c₀ / z‖ := mul_le_mul_of_nonneg_left (by
                rw [norm_mul]
                calc ‖μ₂‖ * ‖c₀ / z‖ ≤ 1 * ‖c₀ / z‖ :=
                      mul_le_mul_of_nonneg_right hμ₂norm (norm_nonneg _)
                  _ = ‖c₀ / z‖ := one_mul _) (pow_nonneg hlam0.le N'')
          _ ≤ (eqLam a) ^ N * ‖c₀ / z‖ := by
              rw [hN''def]
              exact mul_le_mul_of_nonneg_right (hpow_mono_gen (by omega)) (norm_nonneg _)
          _ = ‖((((eqLam a : ℝ) : ℂ) ^ N)) * (c₀ / z)‖ := by
              rw [norm_mul, h0jc_norm_lamC_pow ha0 ha1]
          _ < δ := level_lt hNN₀ z hzann.1
      have hjunction : bwdP a s (fan a h (ε₀ ++ List.replicate (N'' - ε₀.length) true) (μ₁ * z))
          = eqMirror (germC a h (μ₂ * ((((eqLam a : ℝ) : ℂ) ^ N'') * (c₀ / z)))) := by
        have h := hszj z hz.1
        rw [hszz] at h
        exact h
      refine ⟨mul_ne_zero hμ₁ne hz0, hwlt, ?_, ?_⟩
      · rw [hfield]
        exact hnorm₂
      · rw [hetaFan (by rw [hfield]; exact hnorm₂), hfield]
        rw [show (((eqLam a : ℝ) : ℂ) ^ N'') * (μ₂ * (c₀ / z))
            = μ₂ * ((((eqLam a : ℝ) : ℂ) ^ N'') * (c₀ / z)) by ring]
        exact hjunction
    have h1 : ((fun z : ℂ => μ₁ * z) '' Z₄).Countable := hcount.mono hsub
    have h2 : Z₄ ⊆ (fun w : ℂ => w / μ₁) '' ((fun z : ℂ => μ₁ * z) '' Z₄) := by
      intro z hz
      exact ⟨μ₁ * z, ⟨z, hz, rfl⟩, by show μ₁ * z / μ₁ = z; exact mul_div_cancel_left₀ _ hμ₁ne⟩
    exact (h1.image _).mono h2

/-- **The uncountability form of Rychlik's "only one of `γ₁, γ₂` is `1`" step.**

`Z` splits into the points where the *forward* tails of the cluster chains are unbounded and
those where the *backward* tails are (`Work.EQ.junction_forward` supplies the conclusion in the
first case).  In the second case the conclusion — which does not mention `X` or `Z` — is obtained
by applying `Work.EQ.junction_forward` to the shifted mirrors
`w ↦ shiftZ a N₀ (mirrorChain (X z ·))`, whose `ψ₁` tends to `λ^{N₀} c₀ / z` and whose invariant
parameter is again `c₀`. -/
theorem junction_nt_unbounded {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {h : ℂ → ℂ} {r : ℝ} (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ δ₀ →
      ∀ {r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < δ →
      ∀ {c₀ : ℂ}, c₀ ≠ 0 →
      ∀ {Z : Set ℂ} {X : ℂ → ℕ → Work.EQ.ChainData},
        ¬ Z.Countable → (∀ z ∈ Z, r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂) →
        (∀ z ∈ Z, ∀ k, X z k ∈ Work.EQ.H0 a h) →
        (∀ z ∈ Z, Filter.Tendsto (fun k => (X z k).2.1) Filter.atTop (nhds z)) →
        (∀ z ∈ Z, Filter.Tendsto (fun k => (X z k).2.1 * (X z k).2.2) Filter.atTop (nhds c₀)) →
        (∀ z ∈ Z, ∀ B : ℕ, ∃ k : ℕ, ¬ (Work.EQ.TailP a h (X z k) B ∧
          ∀ j : ℕ, B ≤ j → (X z k).1 (-(j : ℤ)) =
            Work.EQ.ugermC a h (((Work.EQ.eqLam a : ℝ) : ℂ) ^ j * (X z k).2.2))) →
        ∃ (N : ℕ) (ε η s : List Bool) (μ₁ μ₂ : ℂ),
          ε.length = N ∧ η.length = N ∧ s.length = N ∧
          μ₁ ∈ Work.EQ.CharSet a h ∧ μ₂ ∈ Work.EQ.CharSet a h ∧ (μ₁ ≠ 1 ∨ μ₂ ≠ 1) ∧ μ₁ * μ₂ ≠ 0 ∧
          ¬ {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ ∧
              ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (μ₁ * μ₂ * c₀ / w)‖ < δ ∧
              Work.EQ.bwdP a s (Work.EQ.fan a h ε w) =
                Work.EQ.eqMirror (Work.EQ.fan a h η
                  (((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (μ₁ * μ₂ * c₀ / w)))}.Countable := by
  obtain ⟨δ₀, hδ₀, hmain⟩ := junction_forward ha0 ha1 hh
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδδ₀ r₁ r₂ hr₁ hr₁₂ hr₂δ c₀ hc₀ Z X hZ hZann hX hX1 hX2 htails
  have hlam0 : (0 : ℝ) < eqLam a := eqLam_pos' ha0 ha1
  have hlamC : (((eqLam a : ℝ)) : ℂ) ≠ 0 := eqLamC_ne_zero ha0 ha1
  set Zf : Set ℂ := {z : ℂ | z ∈ Z ∧ ∀ B : ℕ, ∃ k, B ≤ tailIdx a h (X z k)} with hZfdef
  set Zb : Set ℂ := {z : ℂ | z ∈ Z ∧ ∀ B : ℕ, ∃ k, B ≤ tailIdx a h (mirrorChain (X z k))}
    with hZbdef
  have hcover : Z ⊆ Zf ∪ Zb := by
    intro z hz
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h1' : ¬ (∀ B : ℕ, ∃ k, B ≤ tailIdx a h (X z k)) := fun hh => h1 ⟨hz, hh⟩
    have h2' : ¬ (∀ B : ℕ, ∃ k, B ≤ tailIdx a h (mirrorChain (X z k))) := fun hh => h2 ⟨hz, hh⟩
    push_neg at h1' h2'
    obtain ⟨B₁, hB₁⟩ := h1'
    obtain ⟨B₂, hB₂⟩ := h2'
    obtain ⟨k, hk⟩ := htails z hz (max B₁ B₂)
    refine hk ⟨?_, ?_⟩
    · have hchain : IsChain a h (X z k) := isChain_of_mem_H0 (hX z hz k)
      have hex : ∃ N : ℕ, TailP a h (X z k) N := tailP_of_isChain hchain
      have hle : tailIdx a h (X z k) ≤ max B₁ B₂ := by
        have := hB₁ k
        omega
      exact (tailIdx_le_iff hex).mp hle
    · change JNT.bwdTailP' a h (X z k) (max B₁ B₂)
      rw [JNT.bwdTailP'_iff]
      have hchain : IsChain a h (mirrorChain (X z k)) :=
        isChain_mirrorChain (isChain_of_mem_H0 (hX z hz k))
      have hex : ∃ N : ℕ, TailP a h (mirrorChain (X z k)) N := tailP_of_isChain hchain
      have hle : tailIdx a h (mirrorChain (X z k)) ≤ max B₁ B₂ := by
        have := hB₂ k
        omega
      exact (tailIdx_le_iff hex).mp hle
  have hunc : ¬ Zf.Countable ∨ ¬ Zb.Countable := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hZ ((hcon.1.union hcon.2).mono hcover)
  rcases hunc with hf | hb
  · -- the forward case
    exact hmain hδ hδδ₀ hr₁ hr₁₂ hr₂δ hc₀ hf
      (fun z hz => hZann z hz.1) (fun z hz k => isChain_of_mem_H0 (hX z hz.1 k))
      (fun z hz => hX1 z hz.1) (fun z hz => hX2 z hz.1) (fun z hz => hz.2)
  · -- the backward case: apply the one-sided statement to the shifted mirrors
    obtain ⟨N₀, hN₀⟩ : ∃ N : ℕ, (eqLam a) ^ N * (‖c₀‖ / r₁) < δ := by
      have hlim : Tendsto (fun n : ℕ => (eqLam a) ^ n * (‖c₀‖ / r₁)) atTop (nhds 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le
          (eqLam_lt_one' ha0 ha1)).mul_const (‖c₀‖ / r₁)
      obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hδ)).exists
      exact ⟨n, hn⟩
    have hch : (((eqLam a : ℝ)) : ℂ) ≠ 0 := eqLamC_ne_zero ha0 ha1
    set W : Set ℂ := (fun z : ℂ => (((eqLam a : ℝ)) : ℂ) ^ N₀ * (c₀ / z)) '' Zb with hWdef
    have hWunc : ¬ W.Countable := by
      intro hc
      refine hb ?_
      have h2 : (((fun z : ℂ => (((eqLam a : ℝ)) : ℂ) ^ N₀ * (c₀ / z)) '' Zb)).Countable := by
        rw [← hWdef]; exact hc
      have h3 : Zb ⊆ (fun w : ℂ => c₀ / (w / (((eqLam a : ℝ)) : ℂ) ^ N₀)) '' W := by
        intro z hz
        have hz0 : z ≠ 0 := by
          intro h0
          have h1 := (hZann z hz.1).1
          rw [h0, norm_zero] at h1
          linarith
        refine ⟨(((eqLam a : ℝ)) : ℂ) ^ N₀ * (c₀ / z), ⟨z, hz, rfl⟩, ?_⟩
        have hzz : z ≠ 0 := hz0
        have hlam' : (((eqLam a : ℝ)) : ℂ) ^ N₀ ≠ 0 := pow_ne_zero N₀ hch
        show c₀ / ((((eqLam a : ℝ)) : ℂ) ^ N₀ * (c₀ / z) / (((eqLam a : ℝ)) : ℂ) ^ N₀) = z
        field_simp
      exact ((h2.image _)).mono h3
    have hWann : ∀ w ∈ W, (((eqLam a) ^ N₀ * (‖c₀‖ / r₂))) ≤ ‖w‖ ∧
        ‖w‖ ≤ (eqLam a) ^ N₀ * (‖c₀‖ / r₁) := by
      rintro w ⟨z, hz, rfl⟩
      have hzann := hZann z hz.1
      have hz0 : z ≠ 0 := by
        intro h0
        have h1 := hzann.1
        rw [h0, norm_zero] at h1
        linarith
      have hnorm : ‖((((eqLam a : ℝ)) : ℂ) ^ N₀ * (c₀ / z))‖
          = (eqLam a) ^ N₀ * (‖c₀‖ / ‖z‖) := by
        rw [norm_mul, h0jc_norm_lamC_pow ha0 ha1, norm_div]
      rw [hnorm]
      have hpow : 0 < (eqLam a) ^ N₀ := pow_pos hlam0 N₀
      constructor
      · exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (norm_nonneg c₀) (lt_of_lt_of_le hr₁ hzann.1) hzann.2) hpow.le
      · exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (norm_nonneg c₀) hr₁ hzann.1) hpow.le
    have hWlt : (eqLam a) ^ N₀ * (‖c₀‖ / r₁) < δ := hN₀
    -- the family of shifted mirrors
    let zinv : ℂ → ℂ := fun w =>
      if h : ∃ z ∈ Zb, (((eqLam a : ℝ)) : ℂ) ^ N₀ * (c₀ / z) = w then h.choose else 0
    have hzinv : ∀ w ∈ W, zinv w ∈ Zb ∧ (((eqLam a : ℝ)) : ℂ) ^ N₀ * (c₀ / zinv w) = w := by
      intro w hw
      have hex : ∃ z ∈ Zb, (((eqLam a : ℝ)) : ℂ) ^ N₀ * (c₀ / z) = w := by
        obtain ⟨z, hz, hze⟩ := hw
        exact ⟨z, hz, hze⟩
      have h1 : zinv w = hex.choose := by
        simp only [zinv, dif_pos hex]
      rw [h1]
      exact hex.choose_spec
    let Y : ℂ → ℕ → ChainData := fun w k =>
      shiftZ a (N₀ : ℤ) (mirrorChain (X (zinv w) k))
    have hYchain : ∀ w ∈ W, ∀ k, IsChain a h (Y w k) := by
      intro w hw k
      exact isChain_shiftZ ha0 ha1 (isChain_mirrorChain (isChain_of_mem_H0 (hX (zinv w) (hzinv w hw).1.1 k)))
        (N₀ : ℤ)
    have hψ₂ : ∀ w ∈ W, Tendsto (fun k => (X (zinv w) k).2.2) atTop (nhds (c₀ / zinv w)) := by
      intro w hw
      have hz := (hzinv w hw).1
      have hz0 : zinv w ≠ 0 := by
        intro h0
        have h1 := (hZann (zinv w) hz.1).1
        rw [h0, norm_zero] at h1
        linarith
      have hdiv : Tendsto (fun k => (X (zinv w) k).2.1 * (X (zinv w) k).2.2 / (X (zinv w) k).2.1)
          atTop (nhds (c₀ / zinv w)) := (hX2 (zinv w) hz.1).div (hX1 (zinv w) hz.1) hz0
      refine hdiv.congr' ?_
      filter_upwards with k
      exact mul_div_cancel_left₀ _ (isChain_of_mem_H0 (hX (zinv w) hz.1 k)).2.1
    refine hmain hδ hδδ₀ (by
        have h1 : 0 < ‖c₀‖ / r₂ := div_pos (norm_pos_iff.mpr hc₀) (lt_trans hr₁ hr₁₂)
        exact mul_pos (pow_pos hlam0 N₀) h1)
      (by
        have h1 : 0 < ‖c₀‖ := norm_pos_iff.mpr hc₀
        have h2 : ‖c₀‖ / r₂ < ‖c₀‖ / r₁ := div_lt_div_of_pos_left h1 hr₁ hr₁₂
        exact mul_lt_mul_of_pos_left h2 (pow_pos hlam0 N₀))
      hWlt hc₀ hWunc hWann hYchain ?hY1 ?hY2 ?hYt
    · -- `ψ₁` converges to `w`
      intro w hw
      have h1 : Tendsto (fun k => (((eqLam a : ℝ)) : ℂ) ^ N₀ * (X (zinv w) k).2.2) atTop
          (nhds ((((eqLam a : ℝ)) : ℂ) ^ N₀ * (c₀ / zinv w))) := (hψ₂ w hw).const_mul _
      rw [(hzinv w hw).2] at h1
      refine h1.congr (fun k => ?_)
      show (((eqLam a : ℝ)) : ℂ) ^ N₀ * (X (zinv w) k).2.2
        = (shiftZ a (N₀ : ℤ) (mirrorChain (X (zinv w) k))).2.1
      rw [shiftZ_psi1, mirrorChain_psi1, zpow_natCast]
    · -- the invariant parameter is `c₀`
      intro w hw
      refine (hX2 (zinv w) (hzinv w hw).1.1).congr (fun k => ?_)
      show (X (zinv w) k).2.1 * (X (zinv w) k).2.2
        = (shiftZ a (N₀ : ℤ) (mirrorChain (X (zinv w) k))).2.1
            * (shiftZ a (N₀ : ℤ) (mirrorChain (X (zinv w) k))).2.2
      rw [shiftZ_psi1, shiftZ_psi2, mirrorChain_psi1, mirrorChain_psi2, zpow_natCast]
      field_simp
    · -- the forward tails of the shifted mirrors are unbounded
      intro w hw B
      obtain ⟨k, hk⟩ := (hzinv w hw).1.2 (B + N₀)
      refine ⟨k, le_tailIdx_shiftZ_nat ?_ ?_⟩
      · exact tailP_of_isChain (isChain_mirrorChain (isChain_of_mem_H0 (hX (zinv w) (hzinv w hw).1.1 k)))
      · exact hk

end

end Work.EQ
