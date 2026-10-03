import Mathlib
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.boxes_v3

/-!
# `Work.Repel.chainV9_cells` : the cell set of `chain_returns_v9`

Shishikura §6, Step 3: the cells `(j, k, n)` used by the return-map chase.  A cell consists of

* a chain level `j ≥ 1` and an integer translate `k` such that the fibre `V.fib j k = W j + k`
  lies inside the perturbative level-1 disc `V.Sm1 = Dsm (±η₁)`,
* a level-0 period index `n` with `|n| ≤ η/10 + 1` (so that the corresponding box lies in the
  counting disc `Dflat η`).

The count is `V.N₀ = η η₁²/(320 (C₀+1))` and comes from multiplying the level-1 count
`chain_count_copies` (fibres at level `j ≥ 1` only: a `j = 0` fibre, i.e. a ball around the base
point `cbase` of radius `ρ`, has imaginary part `≤ η₁/2` and can never lie in `Dsm (±η₁)`) by the
level-0 box window `[-M, M-1]`, `M = ⌊η/10⌋ + 1`.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-- **A single box lies in the level-0 counting disc.**  If `|n| ≤ η/10 + 1` and `η ≥ 100`, then
the full-period box `Bbox η n` (real window `(n, n+1)`, imaginary half-height
`log 2/(2π) < 1/8`) is contained in `Dflat η = closedBall (iη) (η/8)`.

The estimates: `z ∈ Bbox η n` gives `|z.re| ≤ η/10 + 2` (from `n < z.re < n+1` and
`-|n| ≤ n`) and `|z.im - η| ≤ log 2/(2π) ≤ 1/8`, and
`(η/10 + 2)² + 1/64 ≤ (η/8)²` for `η ≥ 100`. -/
lemma Bbox_subset_Dflat_of_abs_le {η : ℝ} (hη : 100 ≤ η) {n : ℤ}
    (hn : |((n : ℤ) : ℝ)| ≤ η / 10 + 1) : Bbox η n ⊆ Dflat η := by
  set c : ℝ := Real.log 2 / (2 * Real.pi) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcle : c ≤ 1 / 8 := by
    rw [hcdef]
    have h4 : 4 * Real.log 2 < Real.pi := by
      have h1 := Real.log_two_lt_d9
      have h2 := Real.pi_gt_d6
      linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    linarith
  have hc2 : c ^ 2 ≤ 1 / 64 := by nlinarith [hcpos, hcle]
  have hloghalf : Real.log (1 / 2 : ℝ) / (2 * Real.pi) = -c := by
    have h : Real.log (1 / 2 : ℝ) = -(Real.log 2) := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    rw [h, hcdef]; ring
  have hlog32 : Real.log (3 / 2 : ℝ) / (2 * Real.pi) < c := by
    rw [hcdef]
    exact div_lt_div_of_pos_right (Real.log_lt_log (by norm_num) (by norm_num)) (by positivity)
  intro z hz
  obtain ⟨hre1, hre2, him1, him2⟩ := hz
  have hnabs := abs_le.mp hn
  have hrelo : -(η / 10 + 2) ≤ z.re := by linarith [hnabs.1, hre1]
  have hrehi : z.re ≤ η / 10 + 2 := by linarith [hnabs.2, hre2]
  have hre : |z.re| ≤ η / 10 + 2 := abs_le.mpr ⟨hrelo, hrehi⟩
  have him : |z.im - η| ≤ c := by
    rw [hloghalf] at him1
    rw [abs_le]
    constructor <;> linarith [le_of_lt hlog32]
  have hkey : (η / 10 + 2) ^ 2 + 1 / 64 ≤ (η / 8) ^ 2 := by nlinarith [hη]
  rw [Dflat, Metric.mem_closedBall, dist_eq_norm,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ η)]
  have hsqi : ‖z - Complex.I * (η : ℂ)‖ ^ 2 = z.re ^ 2 + (z.im - η) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hsq : ‖z - Complex.I * (η : ℂ)‖ ^ 2 ≤ (η / 8) ^ 2 := by
    rw [hsqi]
    have h1 := abs_le.mp hre
    have h2 := abs_le.mp him
    have h1' : z.re ^ 2 ≤ (η / 10 + 2) ^ 2 := by nlinarith [h1.1, h1.2]
    have h2' : (z.im - η) ^ 2 ≤ c ^ 2 := by nlinarith [h2.1, h2.2]
    linarith [h1', h2', hc2, hkey]
  have h := sq_le_sq.mp hsq
  rw [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ η / 8)] at h
  exact h

/-- **The level-0 box window, with the index bound.**  There are at least `η/5` integer box
indices, all of absolute value `≤ η/10 + 1`, whose full-period box `Bbox η n` lies in
`Dflat η`. -/
lemma boxes_window_index (η : ℝ) (hη : 100 ≤ η) :
    ∃ T : Finset ℤ, η / 5 ≤ (T.card : ℝ) ∧
      (∀ n ∈ T, Bbox η n ⊆ Dflat η) ∧
      (∀ n ∈ T, |((n : ℤ) : ℝ)| ≤ η / 10 + 1) := by
  set M : ℤ := ⌊η / 10⌋ + 1 with hMdef
  have hMge : η / 10 ≤ (M : ℝ) := by
    rw [hMdef]; have h := Int.lt_floor_add_one (η / 10); push_cast; linarith
  have hMle : (M : ℝ) ≤ η / 10 + 1 := by
    rw [hMdef]; have h := Int.floor_le (η / 10); push_cast; linarith
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := by linarith [hMge, hη]
  have hM0 : (0 : ℤ) ≤ M := by exact_mod_cast hMnn
  refine ⟨Finset.Icc (-M) (M - 1), ?_, ?_, ?_⟩
  · have hcardZ : ((Finset.Icc (-M) (M - 1)).card : ℤ) = 2 * M := by
      have h := Int.card_Icc_of_le (-M) (M - 1) (by omega)
      calc (Finset.Icc (-M) (M - 1)).card = (M - 1) + 1 - (-M) := h
        _ = 2 * M := by ring
    have hcard : ((Finset.Icc (-M) (M - 1)).card : ℝ) = 2 * (M : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hcardZ
      push_cast at this
      exact this
    rw [hcard]; linarith
  · intro n hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
    have hnabs : |((n : ℤ) : ℝ)| ≤ (M : ℝ) := by
      rw [abs_le]
      constructor
      · have h : ((-M : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlo
        push_cast at h; linarith
      · have h : (n : ℝ) ≤ ((M - 1 : ℤ) : ℝ) := by exact_mod_cast hnhi
        push_cast at h; linarith
    exact Bbox_subset_Dflat_of_abs_le hη (by linarith [hnabs, hMle])
  · intro n hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
    rw [abs_le]
    constructor
    · have h : ((-M : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlo
      push_cast at h; linarith
    · have h : (n : ℝ) ≤ ((M - 1 : ℤ) : ℝ) := by exact_mod_cast hnhi
      push_cast at h; linarith

namespace V10

variable (V : V10)

/-- **The level-1 count, in the vocabulary of `V`.**  At least `η₁²/(64(C₀+1))` translates
`W j + k`, with `j` the chain level and `k ∈ ℤ`, lie inside the perturbative disc
`V.Sm1 = Dsm (±η₁)`. -/
lemma chain_count_Sm1 :
    ∃ S₂ : Finset (ℕ × ℤ), V.η₁ ^ 2 / (64 * (V.C₀ + 1)) ≤ (S₂.card : ℝ) ∧
      ∀ q ∈ S₂, V.fib q.1 q.2 ⊆ V.Sm1 := by
  obtain ⟨S₂, hcard, hsub⟩ := chain_count_copies V.hIsChain V.hC₀ V.hsize V.hanchor
  refine ⟨S₂, hcard, fun q hq => ?_⟩
  have h := hsub q hq
  show (fun w : ℂ => w + ((q.2 : ℤ) : ℂ)) '' V.W q.1 ⊆ V.Sm1
  have hpos : 0 < V.η₁ := V.hη₁pos
  rcases V.hIsChain.sign with hs | hs
  · rw [if_pos hs] at h
    rw [V10.Sm1, if_pos hs]
    simpa only [Dsm, abs_of_pos hpos] using h
  · rw [if_neg (by rw [hs]; norm_num)] at h
    rw [V10.Sm1, if_neg (by rw [hs]; norm_num)]
    have h2 : Dsm (-V.η₁) = Metric.closedBall (-Complex.I * (V.η₁ : ℂ)) (V.η₁ / 4) := by
      unfold Dsm
      rw [abs_neg, abs_of_pos hpos,
        show Complex.I * ((-V.η₁ : ℝ) : ℂ) = -Complex.I * (V.η₁ : ℂ) by push_cast; ring]
    rw [h2]
    exact h

/-- **The chain level of a counted cell is `≥ 1`.**  The base disc is `W 0 = ball cbase ρ`, so
any point `w ∈ W 0` satisfies `‖w‖ < ‖cbase‖ + ρ ≤ η₁/2`, and the same bound survives the
integer translate.  But every point of `Dsm (±η₁) = closedBall (±iη₁) (η₁/4)` has imaginary part
of modulus `≥ 3η₁/4`: so no translate of the base disc can be contained in `Sm1`, whence
`j ≠ 0`. -/
lemma one_le_level_of_fib_sub {j : ℕ} {k : ℤ} (h : V.fib j k ⊆ V.Sm1) : 1 ≤ j := by
  by_contra hlt
  push_neg at hlt
  have hj0 : j = 0 := by omega
  rw [hj0] at h
  obtain ⟨w₀, hw₀⟩ := (V.hIsChain.open_conn 0).2.nonempty
  have hmem : w₀ + ((k : ℤ) : ℂ) ∈ V.Sm1 := h ⟨w₀, hw₀, rfl⟩
  have hwb : w₀ ∈ Metric.ball V.cbase V.ρ := by
    rw [V.hbase] at hw₀; exact hw₀
  have hdist : ‖w₀ - V.cbase‖ < V.ρ := by
    rw [← dist_eq_norm]; exact Metric.mem_ball.mp hwb
  have hnorm : ‖w₀‖ < V.η₁ / 2 := by
    have h1 : ‖w₀‖ < ‖V.cbase‖ + V.ρ := by
      have h2 : w₀ = V.cbase + (w₀ - V.cbase) := by ring
      rw [h2]
      linarith [norm_add_le (V.cbase) (w₀ - V.cbase)]
    linarith [V.hcbase, h1]
  have him_le : w₀.im ≤ V.η₁ / 2 :=
    le_of_lt (lt_of_le_of_lt (Complex.im_le_norm _) hnorm)
  have him_ge : -(V.η₁ / 2) ≤ w₀.im := by
    have h1 : -w₀.im ≤ ‖w₀‖ := le_trans (neg_le_abs _) (Complex.abs_im_le_norm _)
    linarith
  rw [V10.Sm1] at hmem
  split at hmem
  · rw [Dsm, Metric.mem_closedBall, dist_eq_norm, abs_of_pos V.hη₁pos] at hmem
    have him : |(w₀ + ((k : ℤ) : ℂ) - Complex.I * (V.η₁ : ℂ)).im| ≤ V.η₁ / 4 :=
      le_trans (Complex.abs_im_le_norm _) hmem
    have heq : (w₀ + ((k : ℤ) : ℂ) - Complex.I * (V.η₁ : ℂ)).im = w₀.im - V.η₁ := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
    rw [heq] at him
    have h3 := (abs_le.mp him).1
    linarith [V.hη₁pos, him_le]
  · rw [Dsm, Metric.mem_closedBall, dist_eq_norm, abs_neg, abs_of_pos V.hη₁pos] at hmem
    have him : |(w₀ + ((k : ℤ) : ℂ) - Complex.I * ((-V.η₁ : ℝ) : ℂ)).im| ≤ V.η₁ / 4 :=
      le_trans (Complex.abs_im_le_norm _) hmem
    have heq : (w₀ + ((k : ℤ) : ℂ) - Complex.I * ((-V.η₁ : ℝ) : ℂ)).im = w₀.im + V.η₁ := by
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
    rw [heq] at him
    have h3 := (abs_le.mp him).2
    linarith [V.hη₁pos, him_ge]

end V10

/-- **The cells of `chain_returns_v9`.**  There are at least `N₀ = η η₁²/(320(C₀+1))` triples
`(j, k, n)` whose fibre `W j + k` lies in the perturbative disc `V.Sm1`, whose level-0 box index
satisfies `|n| ≤ η/10 + 1`, and whose chain level is `j ≥ 1`. -/
theorem chainV9_cells (V : Work.Repel.V10) :
    ∃ S : Finset (ℕ × ℤ × ℤ), V.N₀ ≤ (S.card : ℝ) ∧
      (∀ q ∈ S, V.fib q.1 q.2.1 ⊆ V.Sm1) ∧
      (∀ q ∈ S, |((q.2.2 : ℤ) : ℝ)| ≤ V.η / 10 + 1) ∧
      (∀ q ∈ S, 1 ≤ q.1) := by
  obtain ⟨S₂, hS₂card, hS₂sub⟩ := V.chain_count_Sm1
  obtain ⟨T, hTcard, _, hTidx⟩ := boxes_window_index V.η V.hη
  have hB : (0 : ℝ) ≤ V.η / 5 := by linarith [V.hηpos]
  obtain ⟨S, hScard, hSmem⟩ :=
    triple_cells (A := V.η₁ ^ 2 / (64 * (V.C₀ + 1))) (B := V.η / 5) hB hS₂card hTcard
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · have heq : V.η₁ ^ 2 / (64 * (V.C₀ + 1)) * (V.η / 5)
        = V.η * V.η₁ ^ 2 / (320 * (V.C₀ + 1)) := by
      have hC1 : (V.C₀ + 1) ≠ 0 := by have := V.hC₀; intro hc; linarith [hc]
      field_simp
      ring
    show V.η * V.η₁ ^ 2 / (320 * (V.C₀ + 1)) ≤ (S.card : ℝ)
    rw [← heq]
    exact hScard
  · intro q hq
    exact hS₂sub (q.1, q.2.1) (hSmem q hq).1
  · intro q hq
    exact hTidx q.2.2 (hSmem q hq).2
  · intro q hq
    exact V.one_le_level_of_fib_sub (hS₂sub (q.1, q.2.1) (hSmem q hq).1)

end

end Work.Repel
