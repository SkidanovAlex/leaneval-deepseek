import Mathlib
import Submission.Work.NN.Core.TelTwoDF.complexify_general

/-!
# The holomorphic complexification in the fibre variable (corrected statement)

This is the **corrected** version of `Work.NN.Core.TelTwoDF.exists_complexification_hol`: it adds
the hypothesis `hΩ : IsOpen Ω`, which the original statement was missing.  Without it the original
statement is *false* (see the docstring in `exists_complexification_hol.lean` and the axiom-clean
derivation of `False` in `.nnhol/counterexample_disproof.lean`): Mathlib's `AnalyticOn ℝ E Ω` is
the within-`Ω` notion, so with e.g. `Ω = {q}` it constrains nothing, while the conclusion forces
`E (z, ·)` to be real analytic on a ball around `q.2` for every `z` near `q.1`.

With `Ω` open the intended construction goes through: take an analytic germ `g` of `E` at `q`
(which exists because `Ω ∈ 𝓝 q`), complexify its power series at `q` with
`Cx.exists_analytic_complexification`, and substitute the anti-diagonal `(w, conj (w - q.2))`
for the fibre variable using `Cx.sgL`.  Since the two `ρ`-balls `ball q (2ρ)`, `ball 0 (2ρ)` of
the statement lie inside `Ω` for `ρ` small, the germ `g` agrees with `E` on all the points where
the diagonal identity is required.
-/

noncomputable section

open scoped Topology
open Set Metric

namespace Work.NN.Core.TelTwoDF

open Cx

theorem exists_complexification_hol_open {n : ℕ} {Ω : Set ((Fin n → ℂ) × ℂ)} (hΩ : IsOpen Ω)
    {E : ((Fin n → ℂ) × ℂ) → ℂ} (hE : AnalyticOn ℝ E Ω) {q : (Fin n → ℂ) × ℂ} (hq : q ∈ Ω) :
    ∃ (Φ : ((Fin n → ℂ) × ℂ) × ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧
      AnalyticOn ℝ Φ ((Ω ∩ Metric.ball q (2 * ρ)) ×ˢ Metric.ball (0 : ℂ) (2 * ρ)) ∧
      (∀ r, dist r q < 2 * ρ → Φ (r, starRingEnd ℂ (r.2 - q.2)) = E r) ∧
      (∀ r, dist r q < 2 * ρ →
        AnalyticOn ℂ (fun p : ℂ × ℂ => Φ ((r.1, p.1), p.2))
          (Metric.ball r.2 ρ ×ˢ Metric.ball (0 : ℂ) ρ)) := by
  classical
  obtain ⟨g, -, hgEq, hgan⟩ := (hE q hq).exists_analyticAt
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hΩ q hq
  obtain ⟨p, hp⟩ := hgan
  obtain ⟨r₀, hr₀⟩ := hp
  have hgOn : AnalyticOn ℝ g (Metric.eball q r₀) := hr₀.analyticOnNhd.analyticOn
  set Ωf : Set (CIdx n → ℝ) := rcSL ⁻¹' Metric.eball q r₀ with hΩfdef
  have hΩfopen : IsOpen Ωf := Metric.isOpen_eball.preimage rcSL.continuous
  have hf : AnalyticOn ℝ (fun y : CIdx n → ℝ => g (rcSL y)) Ωf :=
    AnalyticOn.comp hgOn (fun y _ => (rcSL.analyticAt y).analyticWithinAt) (fun y hy => hy)
  have hqΩf : rcL q ∈ Ωf := by
    show rcSL (rcL q) ∈ Metric.eball q r₀
    rw [rcSL_rcL, Metric.mem_eball, edist_self]
    exact hr₀.r_pos
  obtain ⟨F, ρ₀, hρ₀pos, hFℂ, hFdiag⟩ :=
    exists_analytic_complexification (ι := CIdx n) hΩfopen hf hqΩf
  have hFℝ : AnalyticOn ℝ F (Metric.ball (fun k => ((rcL q) k : ℂ)) ρ₀) := hFℂ.restrictScalars
  set ρ : ℝ := min (min (ρ₀ / 8) (ε / 2)) 1 with hρdef
  have hρpos : 0 < ρ := lt_min (lt_min (by positivity) (by positivity)) one_pos
  have h2ρ : 2 * ρ ≤ ε := by
    have h1 : ρ ≤ ε / 2 :=
      le_trans (min_le_left (min (ρ₀ / 8) (ε / 2)) 1) (min_le_right (ρ₀ / 8) (ε / 2))
    linarith
  have h4ρ : 4 * ρ < ρ₀ := by
    have h1 : ρ ≤ ρ₀ / 8 :=
      le_trans (min_le_left (min (ρ₀ / 8) (ε / 2)) 1) (min_le_left (ρ₀ / 8) (ε / 2))
    linarith
  refine ⟨fun rt => F (sgL rt + sgL (((0 : Fin n → ℂ), (0 : ℂ)), starRingEnd ℂ q.2)),
    ρ, hρpos, ?_, ?_, ?_⟩
  · have hsg : AnalyticOn ℝ (fun rt : ((Fin n → ℂ) × ℂ) × ℂ => sgL rt) Set.univ :=
      fun rt _ => (sgL.analyticAt rt).analyticWithinAt
    have hsum : AnalyticOn ℝ (fun rt : ((Fin n → ℂ) × ℂ) × ℂ =>
        sgL rt + sgL (((0 : Fin n → ℂ), (0 : ℂ)), starRingEnd ℂ q.2)) Set.univ :=
      hsg.add analyticOn_const
    have hMaps : Set.MapsTo (fun rt : ((Fin n → ℂ) × ℂ) × ℂ =>
        sgL rt + sgL (((0 : Fin n → ℂ), (0 : ℂ)), starRingEnd ℂ q.2))
        ((Ω ∩ Metric.ball q (2 * ρ)) ×ˢ Metric.ball (0 : ℂ) (2 * ρ))
        (Metric.ball (fun k => ((rcL q) k : ℂ)) ρ₀) := by
      rintro ⟨x, ζ⟩ ⟨⟨-, hx⟩, hζ⟩
      obtain ⟨z, w⟩ := x
      rw [Metric.mem_ball, dist_eq_norm] at hx hζ
      have hζ' : ‖ζ‖ < 2 * ρ := by simpa using hζ
      rw [Metric.mem_ball, dist_eq_norm]
      have hkey : sgL ((z, w), ζ) + sgL (((0 : Fin n → ℂ), (0 : ℂ)), starRingEnd ℂ q.2)
          - (fun k => ((rcL q) k : ℂ)) = sgL (((z, w) - q, ζ)) := by
        rw [← sgL_real q, ← map_add sgL, ← map_sub sgL]
        congr 1
        apply Prod.ext
        · apply Prod.ext <;> simp
        · simp
      rw [hkey]
      have hb := norm_sgL_le (((z, w) - q, ζ))
      calc ‖sgL (((z, w) - q, ζ))‖ ≤ ‖(z, w) - q‖ + ‖ζ‖ := hb
        _ < 2 * ρ + 2 * ρ := add_lt_add hx hζ'
        _ = 4 * ρ := by ring
        _ < ρ₀ := h4ρ
    exact AnalyticOn.comp hFℝ (hsum.mono (Set.subset_univ _)) hMaps
  · intro r hr
    have hrΩ : r ∈ Ω := by
      have h1 : r ∈ Metric.ball q (2 * ρ) := by rw [Metric.mem_ball]; exact hr
      exact hεsub (Metric.ball_subset_ball h2ρ h1)
    have hgr : g r = E r := (hgEq (Or.inr hrΩ)).symm
    show F (sgL (r, starRingEnd ℂ (r.2 - q.2))
        + sgL (((0 : Fin n → ℂ), (0 : ℂ)), starRingEnd ℂ q.2)) = E r
    have harg : sgL (r, starRingEnd ℂ (r.2 - q.2))
        + sgL (((0 : Fin n → ℂ), (0 : ℂ)), starRingEnd ℂ q.2)
        = fun k => ((rcL r) k : ℂ) := by
      rw [← sgL_real r, ← map_add sgL]
      congr 1
      apply Prod.ext
      · simp
      · change starRingEnd ℂ (r.2 - q.2) + starRingEnd ℂ q.2 = starRingEnd ℂ r.2
        rw [← map_add]
        congr 1
        ring
    rw [harg]
    have hdist : dist (rcL r) (rcL q) < ρ₀ := by
      have h1 : dist (rcL r) (rcL q) ≤ dist r q := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub rcL]
        exact norm_rcL_le (r - q)
      linarith
    rw [hFdiag (rcL r) hdist, rcSL_rcL]
    exact hgr
  · intro r hr
    set cr : CIdx n → ℂ := sgL (((r.1, (0 : ℂ)), starRingEnd ℂ q.2)) with hcr
    have hA : AnalyticOn ℂ (fun p : ℂ × ℂ => cr + sgC n p) Set.univ :=
      (analyticOn_const (v := cr)).add (fun p _ => (sgC n).analyticAt p |>.analyticWithinAt)
    have hMaps : Set.MapsTo (fun p : ℂ × ℂ => cr + sgC n p)
        (Metric.ball r.2 ρ ×ˢ Metric.ball (0 : ℂ) ρ)
        (Metric.ball (fun k => ((rcL q) k : ℂ)) ρ₀) := by
      rintro ⟨p1, p2⟩ ⟨hp1, hp2⟩
      rw [Metric.mem_ball, dist_eq_norm] at hp1 hp2
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : ‖r.1 - q.1‖ < 2 * ρ := by
        refine lt_of_le_of_lt (norm_fst_le (r - q)) ?_
        rw [← dist_eq_norm]; exact hr
      have h2 : ‖r.2 - q.2‖ < 2 * ρ := by
        refine lt_of_le_of_lt (norm_snd_le (r - q)) ?_
        rw [← dist_eq_norm]; exact hr
      have hp1' : ‖p1 - r.2‖ < ρ := by simpa using hp1
      have hp2' : ‖p2‖ < ρ := by simpa using hp2
      have hp1'' : ‖p1 - q.2‖ < 3 * ρ := by
        have h3 : (p1 - r.2) + (r.2 - q.2) = p1 - q.2 := by abel
        have h4 := norm_add_le (p1 - r.2) (r.2 - q.2)
        rw [h3] at h4
        linarith
      have hkey : cr + sgC n (p1, p2) - (fun k => ((rcL q) k : ℂ))
          = sgL (((r.1 - q.1, p1 - q.2), p2)) := by
        rw [hcr, sgC_eq_sgL, ← sgL_real q, ← map_add sgL, ← map_sub sgL]
        congr 1
        apply Prod.ext
        · apply Prod.ext <;> simp
        · simp
      rw [hkey]
      have hb := norm_sgL_le (((r.1 - q.1, p1 - q.2), p2))
      have h5 : ‖(r.1 - q.1, p1 - q.2)‖ < 3 * ρ := by
        rw [Prod.norm_def]
        exact max_lt (by linarith) hp1''
      calc ‖sgL (((r.1 - q.1, p1 - q.2), p2))‖ ≤ ‖(r.1 - q.1, p1 - q.2)‖ + ‖p2‖ := hb
        _ < 3 * ρ + ρ := add_lt_add h5 hp2'
        _ = 4 * ρ := by ring
        _ < ρ₀ := h4ρ
    have hcomp := AnalyticOn.comp hFℂ (hA.mono (Set.subset_univ _)) hMaps
    have hfin' : ∀ p : ℂ × ℂ, cr + sgC n p
        = sgL ((r.1, p.1), p.2) + sgL (((0 : Fin n → ℂ), (0 : ℂ)), starRingEnd ℂ q.2) := by
      intro p
      funext k
      obtain ⟨a, b⟩ := k
      rcases a with i | u <;> cases b <;> simp [hcr, smul_eq_mul] <;> ring
    refine hcomp.congr fun p _ => ?_
    rw [Function.comp_apply, hfin' p]

end Work.NN.Core.TelTwoDF
