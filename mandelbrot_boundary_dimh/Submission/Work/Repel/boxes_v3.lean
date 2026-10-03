import Mathlib
import Submission.Work.Repel.counting
import Submission.Work.Repel.boxes_full_period
import Submission.Work.Repel.triple_cells
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.chain

/-!
# The cells of §6, Step 3, at the *corrected* level-1 scale `η₁`

`Work.Repel.boxes` counts the cells with the level-1 disc `closedBall (±iη') (η'/4)`,
`η' = exp (2πη)`.  `NOTES_LEAD_repel_scale.md` shows that the level-1 PERT must be called at
scale `η₁ = exp (2πη)/‖s₀‖` (i.e. `η₁ * ‖s₀‖ = exp (2πη)`), and that the level-1 sources must lie
in `Dsm (±η₁) = closedBall (±iη₁) (η₁/4)` — *not* in `Dsm (±exp (2πη))`, which is the disc of
radius `exp (2πη)/4` and is strictly larger.  So the count must be redone with `η₁`.

Structure of the proof (the same as in `Work.Repel.boxes`): the level-1 count
`Work.Repel.chain_count_copies` — which produces cells inside `closedBall (±iη₁) (η₁/4)` — is
multiplied by the level-0 count `boxes_full_period_eta5` (full-period boxes `Bbox η n` inside
`Dflat η`) via `Work.Repel.triple_cells`.

New ingredients:

* `Bbox η n`, the **full-period** box of `Work.Repel.boxes_full_period` (real width `1`, so that
  `π` is injective on it and `π (Bbox η n)` is a full annulus), replacing the narrow box
  `box η n` of `Work.Repel.counting`;
* `boxes_full_period_eta5`, the same count as `Work.Repel.boxes_full_period` with the constant
  `η/5` instead of `η/8` (the box count in the paper's Step 3 proof, "`D(η)` contains at least
  `η` of these components"), so that the product with `η₁²/(64(C₀+1))` is exactly
  `η η₁²/(320 (C₀+1))`, the constant used by the assembly.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

/-- The full-period level-0 box of Shishikura §6, Step 3: real part in `(n, n+1)` (width `1`, so
that `π` is injective on it and `π (Bbox η n)` is the full annulus
`{e^{-2πη}/2 < ‖ζ‖ < 3 e^{-2πη}/2}`), imaginary part of height `< 1/8` at the counting height
`η`.  This is the set used in `Work.Repel.boxes_full_period`. -/
def Bbox (η : ℝ) (n : ℤ) : Set ℂ :=
  {z : ℂ | (n : ℝ) < z.re ∧ z.re < (n : ℝ) + 1 ∧
    η + Real.log (1 / 2) / (2 * Real.pi) < z.im ∧
    z.im < η + Real.log (3 / 2) / (2 * Real.pi)}

/-- `Bbox` is `Work.Repel.boxes_full_period`'s box, with the set notation factored out. -/
lemma Bbox_eq {η : ℝ} {n : ℤ} :
    Bbox η n = {z : ℂ | (n : ℝ) < z.re ∧ z.re < (n : ℝ) + 1 ∧
      η + Real.log (1 / 2) / (2 * Real.pi) < z.im ∧
      z.im < η + Real.log (3 / 2) / (2 * Real.pi)} := rfl

/-- A point of `Bbox η n` (real part `n + 1/2`, imaginary part `η`). -/
lemma Bbox_nonempty (η : ℝ) (n : ℤ) : (Bbox η n).Nonempty := by
  refine ⟨((n : ℝ) + 1 / 2 : ℂ) + (η : ℂ) * Complex.I, ?_⟩
  have hc1 : Real.log (1 / 2 : ℝ) / (2 * Real.pi) < 0 := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    exact div_neg_of_neg_of_pos (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
      (by positivity)
  have hc2 : 0 < Real.log (3 / 2 : ℝ) / (2 * Real.pi) :=
    div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hre : (((n : ℝ) + 1 / 2 : ℂ) + (η : ℂ) * Complex.I).re = (n : ℝ) + 1 / 2 := by simp
  have him : (((n : ℝ) + 1 / 2 : ℂ) + (η : ℂ) * Complex.I).im = η := by simp
  rw [Bbox, Set.mem_ofPred_eq, hre, him]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **The level-0 box count with constant `η/5`.**  The same count as
`Work.Repel.boxes_full_period`, with the integer window `[-M, M-1]`, `M = ⌊η/10⌋ + 1`, so that
the cardinality is `2M ≥ η/5`; the boxes still fit in `Dflat η = closedBall (iη) (η/8)` because
`(η/10 + 1)² + (log 2/2π)² ≤ (η/8)²` for `η ≥ 100`. -/
theorem boxes_full_period_eta5 (η : ℝ) (hη : 100 ≤ η) :
    ∃ S : Finset ℤ, η / 5 ≤ (S.card : ℝ) ∧ ∀ n ∈ S, Bbox η n ⊆ Dflat η := by
  classical
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
  set M : ℤ := ⌊η / 10⌋ + 1 with hMdef
  have hMge : η / 10 ≤ (M : ℝ) := by
    rw [hMdef]; have h := Int.lt_floor_add_one (η / 10); push_cast; linarith
  have hMle : (M : ℝ) ≤ η / 10 + 1 := by
    rw [hMdef]; have h := Int.floor_le (η / 10); push_cast; linarith
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := by linarith [hMge, hη]
  have hM0 : (0 : ℤ) ≤ M := by exact_mod_cast hMnn
  have hkey : (M : ℝ) ^ 2 + c ^ 2 ≤ (η / 8) ^ 2 := by
    have h1 : (M : ℝ) ^ 2 ≤ (η / 10 + 1) ^ 2 := by nlinarith [hMle, hMnn]
    have h2 : (η / 10 + 1) ^ 2 + 1 / 64 ≤ (η / 8) ^ 2 := by nlinarith [hη]
    linarith
  refine ⟨Finset.Icc (-M) (M - 1), ?_, ?_⟩
  · have hcardZ : ((Finset.Icc (-M) (M - 1)).card : ℤ) = 2 * M := by
      have h := Int.card_Icc_of_le (-M) (M - 1) (by omega)
      calc (Finset.Icc (-M) (M - 1)).card = (M - 1) + 1 - (-M) := h
        _ = 2 * M := by ring
    have hcard : ((Finset.Icc (-M) (M - 1)).card : ℝ) = 2 * (M : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hcardZ
      push_cast at this
      exact this
    rw [hcard]; linarith [hMge]
  · intro n hn z hz
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hre1, hre2, him1, him2⟩ := hz
    have hd : dist z (Complex.I * (η : ℂ)) = Real.sqrt (z.re ^ 2 + (z.im - η) ^ 2) := by
      rw [Complex.dist_eq_re_im]
      have h1 : (Complex.I * (η : ℂ)).re = 0 := by simp
      have h2 : (Complex.I * (η : ℂ)).im = η := by simp
      rw [h1, h2]; ring_nf
    rw [Dflat, Metric.mem_closedBall, hd, abs_of_nonneg (by linarith : (0 : ℝ) ≤ η)]
    have hn1 : |(n : ℝ)| ≤ (M : ℝ) := by
      rw [abs_le]
      constructor
      · have : ((-M : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlo
        push_cast at this; linarith
      · have : (n : ℝ) ≤ ((M - 1 : ℤ) : ℝ) := by exact_mod_cast hnhi
        push_cast at this; linarith
    have hre : |z.re| ≤ (M : ℝ) := by
      have : -(M : ℝ) ≤ z.re ∧ z.re ≤ (M : ℝ) := by
        constructor
        · have : ((-M : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnlo
          push_cast at this; linarith
        · have : (n : ℝ) ≤ ((M - 1 : ℤ) : ℝ) := by exact_mod_cast hnhi
          push_cast at this; linarith
      rw [abs_le]; exact this
    have him : |z.im - η| ≤ c := by
      rw [hloghalf] at him1
      rw [abs_le]
      constructor <;> linarith [le_of_lt hlog32]
    have hsq : z.re ^ 2 + (z.im - η) ^ 2 ≤ (η / 8) ^ 2 := by
      have h1 : z.re ^ 2 ≤ (M : ℝ) ^ 2 := by
        have := abs_le.mp hre; nlinarith [this.1, this.2]
      have h2 : (z.im - η) ^ 2 ≤ c ^ 2 := by
        have := abs_le.mp him; nlinarith [this.1, this.2]
      linarith [hkey]
    have h3 : (0 : ℝ) ≤ η / 8 := by linarith
    calc Real.sqrt (z.re ^ 2 + (z.im - η) ^ 2) ≤ Real.sqrt ((η / 8) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = η / 8 := Real.sqrt_sq h3

/-- **Shishikura §6, Step 3 (the cells), corrected level-1 scale.**  If the Lemma-6.2 chain `W`
marches to the end indicated by `sgn` at speed `< C₀ + 1` and one disc lies below the counting
region `closedBall (±iη₁) (η₁/4)`, then there are at least `η · η₁²/(320 (C₀+1))` cells
`(j, k, n)` such that the translate `W j + k` is contained in the perturbative disc
`Dsm (±η₁) = closedBall (±iη₁) (η₁/4)` of the *level-1* coordinate (the region where the fields
`φ_star_close`, `φ_inj_up` of `P₁` are available), and the full-period box `Bbox η n` lies in the
level-0 counting disc `Dflat η`.

`η₁` is the level-1 PERT scale: the assembly calls this lemma with `η₁ * ‖s₀‖ = exp (2πη)`.
The count needs `η₁ ≥ 64 (C₀+1)` (finer chain ⇒ more translates) and `η ≥ 100`. -/
theorem boxes_v3 {R : ℂ → ℂ} {DR : Set ℂ} {β : ℂ} {ζa ζb : ℂ} {ρ sgn C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W)
    {η η₁ : ℝ} (hC : 0 < C₀) (hη : 100 ≤ η) (hη₁ : 64 * (C₀ + 1) ≤ η₁)
    (hanchor : ∃ j₀ : ℕ, ∃ w ∈ W j₀, sgn * w.im < η₁ / 4) :
    ∃ S : Finset (ℕ × ℤ × ℤ),
      η * η₁ ^ 2 / (320 * (C₀ + 1)) ≤ (S.card : ℝ) ∧
      (∀ q ∈ S, (fun w : ℂ => w + ((q.2.1 : ℤ) : ℂ)) '' W q.1 ⊆
        (if sgn = 1 then Dsm η₁ else Dsm (-η₁))) ∧
      (∀ q ∈ S, Bbox η q.2.2 ⊆ Dflat η ∧ (Bbox η q.2.2).Nonempty) := by
  -- level-1 count: at least `η₁²/(64(C₀+1))` fibres `W j + k` inside `closedBall (±iη₁) (η₁/4)`
  obtain ⟨S₂, hS₂card, hS₂sub⟩ := chain_count_copies h hC hη₁ hanchor
  -- level-0 count: at least `η/5` full-period boxes `Bbox η n ⊆ Dflat η`
  obtain ⟨T, hTcard, hTbox⟩ := boxes_full_period_eta5 η hη
  obtain ⟨S, hScard, hSmem⟩ := triple_cells (B := η / 5) (by linarith) hS₂card hTcard
  refine ⟨S, ?_, ?_, ?_⟩
  · have hC1 : (0 : ℝ) < C₀ + 1 := by linarith
    have heq : η₁ ^ 2 / (64 * (C₀ + 1)) * (η / 5)
        = η * η₁ ^ 2 / (320 * (C₀ + 1)) := by
      field_simp
      ring
    calc η * η₁ ^ 2 / (320 * (C₀ + 1))
        = η₁ ^ 2 / (64 * (C₀ + 1)) * (η / 5) := heq.symm
      _ ≤ (S.card : ℝ) := hScard
  · -- containment in `Dsm (±η₁)` (`Dsm η = closedBall (iη) (|η|/4)`, and `η₁ ≥ 64 > 0`)
    have hη₁pos : 0 < η₁ := by linarith [hC, hη₁]
    intro q hq
    have h1 := hS₂sub (q.1, q.2.1) (hSmem q hq).1
    rcases h.sign with hs | hs
    · rw [if_pos hs] at h1
      rw [if_pos hs]
      simp only [Dsm, abs_of_pos hη₁pos]
      exact h1
    · rw [if_neg (by rw [hs]; norm_num)] at h1
      rw [if_neg (by rw [hs]; norm_num)]
      have h2 : Dsm (-η₁) = Metric.closedBall (-Complex.I * η₁) (η₁ / 4) := by
        unfold Dsm
        rw [abs_neg, abs_of_pos hη₁pos,
          show Complex.I * ((-η₁ : ℝ) : ℂ) = -Complex.I * (η₁ : ℂ) by push_cast; ring]
      rw [h2]
      exact h1
  · intro q hq
    exact ⟨hTbox q.2.2 (hSmem q hq).2, Bbox_nonempty η q.2.2⟩

end

end Work.Repel
