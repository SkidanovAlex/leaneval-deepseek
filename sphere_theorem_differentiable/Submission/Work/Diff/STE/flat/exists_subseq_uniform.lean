import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter Metric Set
open scoped Topology

namespace Work.Diff.STE.flat

/-!
# A diagonal Arzelà–Ascoli lemma on the half-open interval `[0, τ)`

Given a countable family `i : ι` of sequences `m ↦ f m i` of functions on `[0, τ)` which are
uniformly bounded by `L i` and Lipschitz with constant `L i`, one can extract a single subsequence
`φ` along which all the sequences `m ↦ f (φ m) i` converge *uniformly* on `[0, τ)`.

The proof is the classical one, done on an explicit grid of `[0, τ)`:

* For every `ε > 0` and every `n` there are grid points `j * τ / n`, `j < n`, forming an
  `ε`-net of `[0, τ)` (`exists_grid_approx`).
* The values of all sequences at all grid points form a product of closed balls
  `∏_{ι × ℕ × ℕ} closedBall 0 (L i)`, which is compact; a diagonal subsequence converging at each
  grid point is extracted by `IsCompact.tendsto_subseq`.
* Pointwise convergence at an arbitrary `t ∈ [0, τ)` follows from the Lipschitz bound and the grid
  approximation (Cauchy criterion), and the pointwise limit `g i` is again `L i`-Lipschitz.
* Uniform convergence then follows: for a given `ε`, choose a finite grid with mesh `< δ`, where
  `L i * δ ≤ ε/4`; the finitely many grid values are eventually close, and every `t` is within `δ`
  of a grid point, so the Lipschitz bound transfers the estimate from the grid to all of `[0, τ)`.

We isolate the grid constructions as `private` helpers so that the module only exports the main
statement.
-/

/-- The `j`-th grid point of `[0, τ)` subdivided into `n` equal parts; the junk value `0` is
returned when `n ≤ j` so that the function is defined everywhere. -/
private noncomputable def gridPt (τ : ℝ) (n j : ℕ) : ℝ :=
  if j < n then (j : ℝ) * τ / (n : ℝ) else 0

private lemma grid_mem_Ico {τ : ℝ} (hτ : 0 < τ) {n j : ℕ} (hn : 0 < n) (hj : j < n) :
    (j : ℝ) * τ / (n : ℝ) ∈ Set.Ico (0 : ℝ) τ := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  constructor
  · positivity
  · rw [div_lt_iff₀ hn']
    have hj' : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj
    nlinarith [hτ]

private lemma gridPt_mem {τ : ℝ} (hτ : 0 < τ) (n j : ℕ) : gridPt τ n j ∈ Set.Ico (0 : ℝ) τ := by
  rw [gridPt]
  split_ifs with hj
  · exact grid_mem_Ico hτ (by omega) hj
  · exact ⟨le_refl 0, hτ⟩

private lemma gridPt_of_lt {τ : ℝ} {n j : ℕ} (hj : j < n) :
    gridPt τ n j = (j : ℝ) * τ / (n : ℝ) := by
  simp [gridPt, hj]

private lemma mul_div_four_le {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    L * (ε / (4 * (L + 1))) ≤ ε / 4 := by
  have h4 : (0 : ℝ) < 4 * (L + 1) := by positivity
  have h : L * (ε / (4 * (L + 1))) = L * ε / (4 * (L + 1)) := by rw [mul_div_assoc']
  rw [h, div_le_iff₀ h4]
  nlinarith [hL, hε.le]

/-- For every `ε > 0` there is a grid of `[0, τ)` with mesh `< ε`: there is `n > 0` such that every
point of `[0, τ)` is within `ε` of one of the grid points `j * τ / n`, `j < n`. -/
private lemma exists_grid_approx {τ : ℝ} (hτ : 0 < τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ,
      ∃ j : ℕ, j < n ∧ |t - (j : ℝ) * τ / (n : ℝ)| < ε := by
  obtain ⟨n, hnpos, hnε⟩ : ∃ n : ℕ, 0 < n ∧ τ / (n : ℝ) < ε := by
    refine ⟨⌊τ / ε⌋₊ + 1, Nat.succ_pos _, ?_⟩
    have hnR : (0 : ℝ) < ((⌊τ / ε⌋₊ + 1 : ℕ) : ℝ) := by positivity
    have h1 : τ / ε < ((⌊τ / ε⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one (τ / ε)
    have h1' : τ < ((⌊τ / ε⌋₊ + 1 : ℕ) : ℝ) * ε := by rwa [div_lt_iff₀ hε] at h1
    rw [div_lt_iff₀ hnR]; linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  refine ⟨n, hnpos, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := ht.1
  have hposa : (0 : ℝ) ≤ t * (n : ℝ) / τ := div_nonneg (mul_nonneg ht0 hnR.le) hτ.le
  refine ⟨⌊t * (n : ℝ) / τ⌋₊, ?_, ?_⟩
  · rw [Nat.floor_lt hposa, div_lt_iff₀ hτ]
    nlinarith [ht.2, hnR, hτ]
  · set j : ℕ := ⌊t * (n : ℝ) / τ⌋₊ with hjdef
    have hjle : (j : ℝ) ≤ t * (n : ℝ) / τ := Nat.floor_le hposa
    have hjlt : t * (n : ℝ) / τ < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hA : (j : ℝ) * τ ≤ t * (n : ℝ) := by rwa [le_div_iff₀ hτ] at hjle
    have hB : t * (n : ℝ) < ((j : ℝ) + 1) * τ := by rwa [div_lt_iff₀ hτ] at hjlt
    have h1 : (j : ℝ) * τ / (n : ℝ) ≤ t := by rw [div_le_iff₀ hnR]; exact hA
    have h2 : ((j : ℝ) + 1) * τ / (n : ℝ) = (j : ℝ) * τ / (n : ℝ) + τ / (n : ℝ) := by
      field_simp
    have h3 : t < ((j : ℝ) + 1) * τ / (n : ℝ) := by
      rw [lt_div_iff₀ hnR]; exact hB
    rw [h2] at h3
    rw [abs_of_nonneg (by linarith : 0 ≤ t - (j : ℝ) * τ / (n : ℝ))]
    linarith [h3, hnε]

theorem exists_subseq_uniform {ι : Type*} [Countable ι] {τ : ℝ} (hτ : 0 < τ) (L : ι → ℝ)
    (hL : ∀ i, 0 ≤ L i) (f : ℕ → ι → ℝ → ℂ)
    (hbdd : ∀ (i : ι) (m : ℕ), ∀ t ∈ Set.Ico (0:ℝ) τ, ‖f m i t‖ ≤ L i)
    (hlip : ∀ (i : ι) (m : ℕ), ∀ t ∈ Set.Ico (0:ℝ) τ, ∀ t' ∈ Set.Ico (0:ℝ) τ,
      ‖f m i t - f m i t'‖ ≤ L i * |t - t'|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ι → ℝ → ℂ, ∀ i,
      TendstoUniformlyOn (fun m (t : ℝ) => f (φ m) i t) (g i) Filter.atTop (Set.Ico (0:ℝ) τ) := by
  classical
  -- The values of all sequences at all grid points form a compact product of closed balls.
  have hK : IsCompact (Set.univ.pi (fun p : ι × ℕ × ℕ => Metric.closedBall (0:ℂ) (L p.1))) :=
    isCompact_univ_pi fun p => isCompact_closedBall 0 (L p.1)
  have hmem : ∀ m, (fun p : ι × ℕ × ℕ => f m p.1 (gridPt τ p.2.1 p.2.2)) ∈
      Set.univ.pi (fun p : ι × ℕ × ℕ => Metric.closedBall (0:ℂ) (L p.1)) := by
    intro m
    rw [Set.mem_univ_pi]
    intro p
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbdd p.1 m _ (gridPt_mem hτ p.2.1 p.2.2)
  -- Diagonal extraction: a subsequence converging (in the product topology) at every grid point.
  obtain ⟨a, -, φ, hφ, hφt⟩ := IsCompact.tendsto_subseq hK hmem
  have hconv : ∀ (i : ι) (n j : ℕ), ∃ z : ℂ,
      Tendsto (fun m => f (φ m) i (gridPt τ n j)) atTop (𝓝 z) := by
    intro i n j
    exact ⟨a (i, n, j), tendsto_pi_nhds.mp hφt (i, n, j)⟩
  -- Pointwise convergence at *every* point of `[0, τ)`: the grid plus the Lipschitz bound.
  have hconvI : ∀ (i : ι) (t : ℝ), ∃ z : ℂ,
      t ∈ Set.Ico (0:ℝ) τ → Tendsto (fun m => f (φ m) i t) atTop (𝓝 z) := by
    intro i t
    by_cases ht : t ∈ Set.Ico (0:ℝ) τ
    · have hcau : CauchySeq (fun m => f (φ m) i t) := by
        rw [Metric.cauchySeq_iff]
        intro ε hε
        set δ : ℝ := ε / (4 * (L i + 1)) with hδ
        have hδpos : 0 < δ := by
          rw [hδ]; exact div_pos hε (by nlinarith [hL i])
        have hLiδ : L i * δ ≤ ε / 4 := by rw [hδ]; exact mul_div_four_le (hL i) hε
        obtain ⟨n, hn, hnet⟩ := exists_grid_approx hτ hδpos
        obtain ⟨j, hj, hjt⟩ := hnet t ht
        obtain ⟨z, hz⟩ := hconv i n j
        have hdmem : gridPt τ n j ∈ Set.Ico (0:ℝ) τ := gridPt_mem hτ n j
        have hdeq : gridPt τ n j = (j:ℝ) * τ / (n:ℝ) := gridPt_of_lt hj
        rw [Metric.tendsto_nhds] at hz
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hz (ε/4) (by linarith))
        refine ⟨N, fun m hm m' hm' => ?_⟩
        have h1 : dist (f (φ m) i t) (f (φ m) i (gridPt τ n j)) ≤ L i * |t - gridPt τ n j| := by
          rw [dist_eq_norm]; exact hlip i (φ m) t ht _ hdmem
        have h2a : dist (f (φ m) i (gridPt τ n j)) z < ε/4 := hN m hm
        have h2b : dist z (f (φ m') i (gridPt τ n j)) < ε/4 := by
          rw [dist_comm]; exact hN m' hm'
        have h2 : dist (f (φ m) i (gridPt τ n j)) (f (φ m') i (gridPt τ n j)) < ε/2 := by
          have := dist_triangle (f (φ m) i (gridPt τ n j)) z (f (φ m') i (gridPt τ n j))
          linarith
        have h3 : dist (f (φ m') i (gridPt τ n j)) (f (φ m') i t) ≤
            L i * |gridPt τ n j - t| := by
          rw [dist_eq_norm]; exact hlip i (φ m') _ hdmem t ht
        have htd : |t - gridPt τ n j| < δ := by rw [hdeq]; exact hjt
        have h5 : L i * |t - gridPt τ n j| < ε/4 := by
          rcases eq_or_lt_of_le (hL i) with h0 | hpos
          · rw [← h0, zero_mul]; linarith
          · exact lt_of_lt_of_le (mul_lt_mul_of_pos_left htd hpos) hLiδ
        have h6 : L i * |gridPt τ n j - t| < ε/4 := by rw [abs_sub_comm]; exact h5
        have h4 := dist_triangle4 (f (φ m) i t) (f (φ m) i (gridPt τ n j))
          (f (φ m') i (gridPt τ n j)) (f (φ m') i t)
        linarith
      obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcau
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h ht⟩
  -- The pointwise limit.
  let g : ι → ℝ → ℂ := fun i t => Classical.choose (hconvI i t)
  have hgtend : ∀ (i : ι) (t : ℝ) (ht : t ∈ Set.Ico (0:ℝ) τ),
      Tendsto (fun m => f (φ m) i t) atTop (𝓝 (g i t)) := by
    intro i t ht
    exact (Classical.choose_spec (hconvI i t)) ht
  -- The limit inherits the Lipschitz bound.
  have hglip : ∀ (i : ι) (t : ℝ) (ht : t ∈ Set.Ico (0:ℝ) τ) (t' : ℝ)
      (ht' : t' ∈ Set.Ico (0:ℝ) τ), ‖g i t - g i t'‖ ≤ L i * |t - t'| := by
    intro i t ht t' ht'
    have h1 : Tendsto (fun m => f (φ m) i t - f (φ m) i t') atTop (𝓝 (g i t - g i t')) :=
      (hgtend i t ht).sub (hgtend i t' ht')
    have h2 : Tendsto (fun m => ‖f (φ m) i t - f (φ m) i t'‖) atTop (𝓝 ‖g i t - g i t'‖) := h1.norm
    refine le_of_tendsto h2 (Eventually.of_forall fun m => ?_)
    exact hlip i (φ m) t ht t' ht'
  refine ⟨φ, hφ, g, fun i => ?_⟩
  -- Uniform convergence via a finite grid.
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set δ : ℝ := ε / (4 * (L i + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos hε (by nlinarith [hL i])
  have hLiδ : L i * δ ≤ ε / 4 := by rw [hδdef]; exact mul_div_four_le (hL i) hε
  obtain ⟨n, hn, hnet⟩ := exists_grid_approx hτ hδpos
  have hev : ∀ᶠ m in atTop, ∀ j ∈ Finset.range n,
      dist (g i ((j:ℝ) * τ / (n:ℝ))) (f (φ m) i ((j:ℝ) * τ / (n:ℝ))) < ε / 2 := by
    rw [Finset.eventually_all]
    intro j hj
    have hjlt : j < n := Finset.mem_range.mp hj
    have hmem : (j:ℝ) * τ / (n:ℝ) ∈ Set.Ico (0:ℝ) τ := grid_mem_Ico hτ hn hjlt
    have h := (Metric.tendsto_nhds.mp (hgtend i _ hmem)) (ε/2) (by linarith)
    exact h.mono fun m hm => by rw [dist_comm]; exact hm
  filter_upwards [hev] with m hm
  intro t ht
  obtain ⟨j, hjlt, hjt⟩ := hnet t ht
  have hjmem : j ∈ Finset.range n := Finset.mem_range.mpr hjlt
  have hc : (j:ℝ) * τ / (n:ℝ) ∈ Set.Ico (0:ℝ) τ := grid_mem_Ico hτ hn hjlt
  have h1 : dist (g i t) (g i ((j:ℝ) * τ / (n:ℝ))) ≤ L i * |t - (j:ℝ) * τ / (n:ℝ)| := by
    rw [dist_eq_norm]; exact hglip i t ht _ hc
  have h2 : dist (g i ((j:ℝ)*τ/(n:ℝ))) (f (φ m) i ((j:ℝ)*τ/(n:ℝ))) < ε/2 := hm j hjmem
  have h3 : dist (f (φ m) i ((j:ℝ)*τ/(n:ℝ))) (f (φ m) i t) ≤ L i * |(j:ℝ)*τ/(n:ℝ) - t| := by
    rw [dist_eq_norm]; exact hlip i (φ m) _ hc t ht
  have h5 : L i * |t - (j:ℝ)*τ/(n:ℝ)| < ε/4 := by
    rcases eq_or_lt_of_le (hL i) with h0 | hpos
    · rw [← h0, zero_mul]; linarith
    · exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hjt hpos) hLiδ
  have h6 : L i * |(j:ℝ)*τ/(n:ℝ) - t| < ε/4 := by rw [abs_sub_comm]; exact h5
  have h4 := dist_triangle4 (g i t) (g i ((j:ℝ)*τ/(n:ℝ)))
    (f (φ m) i ((j:ℝ)*τ/(n:ℝ))) (f (φ m) i t)
  linarith

end Work.Diff.STE.flat
