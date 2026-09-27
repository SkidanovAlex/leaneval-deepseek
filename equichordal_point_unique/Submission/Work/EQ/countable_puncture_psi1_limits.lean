import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_fibre_defs
import Submission.Work.EQ.bwdP_fan_degenerate_countable
import Submission.Work.EQ.bwdP_fan_subO2_degenerate_countable
import Submission.Work.EQ.genuine_chart_window_degenerate_bn
import Submission.Work.EQ.chart_tails_unit_disc

namespace Work.EQ

open Filter _root_.Topology Set

/-! # Countably many `ψ₁`-limits of genuine punctures (Rychlik §6 step 3, first half)

The set of `u₀` for which there is a *genuine* punctured chart `e` (no limit in `⁰H` at `ζ = 0`)
with `ψ₁`-limit `u₀` and a finite `ψ₂`-limit is countable.

Route (design: `Submission/Work/EQ/DESIGN_PUNCT_CORE.md`).  Reparametrise the chart so that its
principal tails are uniform on the whole punctured unit disc (`Work.EQ.chart_tails_unit_disc`), and
pick a depth `N` large enough that `‖λ^N u₀‖ < δ` and `‖λ^N v₀‖ < δ` (possible since `λ ∈ (0,1)`).
The window dichotomy `Work.EQ.genuine_chart_window_degenerate_bn` — stated with the tail-norm
hypothesis `∀ m ≥ N, ‖λ^m u₀‖ < δ ∧ ‖λ^m v₀‖ < δ`, which is exactly what the proof uses — then
produces a short backward word `σ` from the stable germ at `λ^N u₀` along which one of the two
radicands `bsq (subO1 a ·)`, `bsq (subO2 a ·)` vanishes.  Both loci are countable
(`Work.EQ.bwdP_fan_degenerate_countable`, `Work.EQ.bwdP_fan_subO2_degenerate_countable`), so the
target is the countable union `⋃_N (λ^{-N}) • (D₁ (2N) ∪ D₂ (2N))`. -/

/-- `‖λⁿ v‖ = λⁿ ‖v‖` for `λ = eqLam a ∈ (0,1)`. -/
private theorem norm_eqLam_pow_mul' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) (v : ℂ) :
    ‖((eqLam a : ℝ) : ℂ) ^ n * v‖ = (eqLam a) ^ n * ‖v‖ := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (eqLam_pos' ha0 ha1).le]

/-- **Countably many `ψ₁`-limits of genuine punctures (Rychlik §6 step 3, first half).** -/
theorem countable_puncture_psi1_limits {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {h : ℂ → ℂ} {r : ℝ} (hh : IsStableGerm a h r) :
    Set.Countable {u₀ : ℂ | ∃ (e : ℂ → ChainData) (v₀ : ℂ) (k : ℕ),
      IsPuncturedChart a h e u₀ k ∧
      (¬ ∃ q ∈ H0 a h, Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) ∧
      Filter.Tendsto (fun ζ : ℂ => (e ζ).2.2)
        (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀)} := by
  obtain ⟨Ke, Lam, Q, δf, hKe, hLam, hQ, hδf, hF0⟩ := fan_induction ha0 ha1 hh
  obtain ⟨ρg, hρg, -, -, hreg0, -, -⟩ := germC_facts ha0 ha1 hh
  obtain ⟨δ₁, hδ₁, hD₁⟩ := bwdP_fan_degenerate_countable ha0 ha1 hh
  obtain ⟨δ₂, hδ₂, hD₂⟩ := bwdP_fan_subO2_degenerate_countable ha0 ha1 hh
  set δ : ℝ := min (min δf ρg) (min δ₁ δ₂) with hδdef
  have hδ0 : 0 < δ := lt_min (lt_min hδf hρg) (lt_min hδ₁ hδ₂)
  have hδδf : δ ≤ δf := (min_le_left _ _).trans (min_le_left _ _)
  have hδρg : δ ≤ ρg := (min_le_left _ _).trans (min_le_right _ _)
  have hδδ₁ : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδδ₂ : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hF : ∀ (ε : List Bool) (v : ℂ), ‖v‖ < δ → FanGood a h Ke Lam Q ε v :=
    fun ε v hv => hF0 ε v (by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hv hδδf)
  have hreg : ∀ u : ℂ, ‖u‖ < δ → RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)) :=
    fun u hu => (hreg0 u (by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hu hδρg)).1
  have hD1 : ∀ j : ℕ, ({w : ℂ | ‖w‖ < δ ∧ ∃ σ : List Bool, σ.length ≤ j ∧
      bsq (subO1 a (bwdP a σ (germC a h w))) = 0}).Countable := by
    intro j
    refine Set.Countable.mono ?_ (hD₁ [] j)
    intro w hw
    exact ⟨lt_of_lt_of_le hw.1 hδδ₁, hw.2⟩
  have hD2 : ∀ j : ℕ, ({w : ℂ | ‖w‖ < δ ∧ ∃ σ : List Bool, σ.length ≤ j ∧
      bsq (subO2 a (bwdP a σ (germC a h w))) = 0}).Countable := by
    intro j
    refine Set.Countable.mono ?_ (hD₂ [] j)
    intro w hw
    exact ⟨lt_of_lt_of_le hw.1 hδδ₂, hw.2⟩
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlamC : ((eqLam a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0)
  refine Set.Countable.mono ?_ (Set.countable_iUnion fun N : ℕ =>
    ((hD1 (2 * N)).union (hD2 (2 * N))).image (fun z => z / ((eqLam a : ℝ) : ℂ) ^ N))
  rintro u₀ ⟨e, v₀, k, he, hgen, hv⟩
  -- reparametrise so that the tails hold on the whole punctured unit disc
  obtain ⟨E, Ne, hEchart, hEgen, hEpsi, hEtail⟩ := chart_tails_unit_disc ha0 ha1 hh he hv hgen
  -- pick the depth `N`
  obtain ⟨N, hN1, hNNe, hNu, hNv⟩ : ∃ N : ℕ, 1 ≤ N ∧ Ne ≤ N ∧
      (eqLam a) ^ N * ‖u₀‖ < δ ∧ (eqLam a) ^ N * ‖v₀‖ < δ := by
    have hlim : Filter.Tendsto (fun n : ℕ => (eqLam a) ^ n * (‖u₀‖ + ‖v₀‖ + 1))
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const (‖u₀‖ + ‖v₀‖ + 1)
    have hpos : 0 < δ := hδ0
    obtain ⟨N₀, hN₀⟩ := (hlim.eventually (eventually_lt_nhds hpos)).exists
    refine ⟨max (max 1 Ne) N₀, le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), ?_, ?_⟩
    · have hmono : (eqLam a) ^ (max (max 1 Ne) N₀) ≤ (eqLam a) ^ N₀ :=
        pow_le_pow_of_le_one hlam0.le hlam1.le (le_max_right _ _)
      have h1 : (eqLam a) ^ N₀ * ‖u₀‖ ≤ (eqLam a) ^ N₀ * (‖u₀‖ + ‖v₀‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg v₀]) (pow_nonneg hlam0.le N₀)
      have h2 : (eqLam a) ^ (max (max 1 Ne) N₀) * ‖u₀‖
          ≤ (eqLam a) ^ N₀ * ‖u₀‖ :=
        mul_le_mul_of_nonneg_right hmono (norm_nonneg u₀)
      linarith [hN₀, h1, h2]
    · have hmono : (eqLam a) ^ (max (max 1 Ne) N₀) ≤ (eqLam a) ^ N₀ :=
        pow_le_pow_of_le_one hlam0.le hlam1.le (le_max_right _ _)
      have h1 : (eqLam a) ^ N₀ * ‖v₀‖ ≤ (eqLam a) ^ N₀ * (‖u₀‖ + ‖v₀‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg u₀]) (pow_nonneg hlam0.le N₀)
      have h2 : (eqLam a) ^ (max (max 1 Ne) N₀) * ‖v₀‖
          ≤ (eqLam a) ^ N₀ * ‖v₀‖ :=
        mul_le_mul_of_nonneg_right hmono (norm_nonneg v₀)
      linarith [hN₀, h1, h2]
  refine Set.mem_iUnion.mpr ⟨N, ?_⟩
  refine ⟨((eqLam a : ℝ) : ℂ) ^ N * u₀, ?_, ?_⟩
  · have hbn : ∀ m : ℕ, N ≤ m → ‖((eqLam a : ℝ) : ℂ) ^ m * u₀‖ < δ ∧
        ‖((eqLam a : ℝ) : ℂ) ^ m * v₀‖ < δ := by
      intro m hm
      constructor
      · rw [norm_eqLam_pow_mul' ha0 ha1 m u₀]
        calc (eqLam a) ^ m * ‖u₀‖ ≤ (eqLam a) ^ N * ‖u₀‖ :=
              mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hlam0.le hlam1.le hm)
                (norm_nonneg u₀)
          _ < δ := hNu
      · rw [norm_eqLam_pow_mul' ha0 ha1 m v₀]
        calc (eqLam a) ^ m * ‖v₀‖ ≤ (eqLam a) ^ N * ‖v₀‖ :=
              mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hlam0.le hlam1.le hm)
                (norm_nonneg v₀)
          _ < δ := hNv
    obtain ⟨σ, hσlen, hσdeg⟩ := genuine_chart_window_degenerate_bn ha0 ha1 hh hEchart hEgen hEpsi
      (fun ζ hζ0 hζ1 n hn => hEtail ζ hζ0 hζ1 n (le_trans hNNe hn)) hδ0 hN1 hF hreg hbn
    rcases hσdeg with hd | hd
    · exact Or.inl ⟨by rw [norm_eqLam_pow_mul' ha0 ha1 N u₀]; exact hNu, σ, hσlen, hd⟩
    · exact Or.inr ⟨by rw [norm_eqLam_pow_mul' ha0 ha1 N u₀]; exact hNu, σ, hσlen, hd⟩
  · show ((eqLam a : ℝ) : ℂ) ^ N * u₀ / ((eqLam a : ℝ) : ℂ) ^ N = u₀
    rw [mul_div_cancel_left₀ u₀ (pow_ne_zero _ hlamC)]

end Work.EQ
