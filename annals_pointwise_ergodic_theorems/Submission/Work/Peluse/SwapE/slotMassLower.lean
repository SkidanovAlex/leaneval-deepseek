import Mathlib
import Submission.Work.Peluse.SwapE.existsSlotGood
import Submission.Work.Peluse.SwapE.lawSumEqMassBox

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-- **`SlotMassLower`** — the endgame hypotheses imply the mass lower bound.

Available as hypotheses: `hL : LinearInLaw`, `hD : SlotDensity`, `hP : PboxLeOne`
(the corresponding files import `Submission.Work.Peluse.SwapE.Defs`).

Proof sketch (`C = 1/2` works).
* `hP` gives `pbox d (q₁ ω) (q₂ ω) M (symIcc N) f ≤ 1` for every `ω`; averaging against
  `hbad : ((univ \ G).card : ℝ) ≤ δ/2 * card Ω` and `hmain : δ ≤ avg …` gives
  `(1/card Ω) * ∑_{ω ∈ G} pbox … ≥ δ/2`, hence (with `G` nonempty) some `ω ∈ G` with
  `pbox d (q₁ ω) (q₂ ω) M (symIcc N) f ≥ δ/2`.
* `hL` at `L := max (2*N) (2*H*M) ≥ 2*N` rewrites that `pboxSum` as
  `lawSum d (q₁ ω) (q₂ ω) M (symIcc N) f L
     = ∑_{n ∈ [±L]^d} (∏ k, slotLaw (q₁ ω k) (q₂ ω k) M (n k)) * boxMass d (symIcc N) f n`.
* `slotLaw q₁ q₂ M n = 0` when `|n| > 2*H*(M-1)` (the slot difference
  `pdir m - pdir m' = q₁(m₁-m₃) - q₂(m₂-m₄)` has `|·| ≤ (|q₁|+|q₂|)*(M-1) ≤ 2H(M-1) ≤ 2HM`),
  so only `n ∈ massBox d H M` contribute; and `∑ n, slotLaw q₁ q₂ M n = 1`
  (each `∑ n, slotCount = M^4`), so the slot laws are a probability vector.
* `hD` bounds each factor by `endgameK0 η H M / (4*H*M+1)`, hence the product by
  `(endgameK0 η H M)^d / (4*H*M+1)^d = (endgameK0 η H M)^d / (massBox d H M).card`
  (the last identity is `Fintype.card_piFinset` + `Int.card_Icc`).
* Hence `δ/2 ≤ (endgameK0 η H M)^d * ∑_{n ∈ massBox} ‖boxMass d (symIcc N) f n‖ / (massBoxCard H M)^d
  = (endgameK0 η H M)^d * massAvg d H M N f`, which is the conclusion with `C = 1/2`. -/
theorem slotMassLower (hL : Work.Peluse.SwapE.LinearInLaw)
    (hD : Work.Peluse.SwapE.SlotDensity) (hP : Work.Peluse.SwapE.PboxLeOne) :
    Work.Peluse.SwapE.SlotMassLower := by
  classical
  intro d _
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro Ω _ _ q₁ q₂ G H M N η δ f hH hM hη hη1 hδ hf hf1 hb hgen hbad hmain
  -- (1) a *good* slot whose `pbox` value is at least `δ/2`
  obtain ⟨ω, hωG, hω⟩ := existsSlotGood (fun ω : Ω => pbox d (q₁ ω) (q₂ ω) M (symIcc N) f) G δ hδ
    (fun ω => hP d (q₁ ω) (q₂ ω) M N f hM hf hf1) hbad hmain
  -- (2) the truncation box `[±L]^d` containing the slot box
  set L : ℕ := max (2 * N) (2 * (H * M)) with hLdef
  have h2N : 2 * N ≤ L := le_max_left _ _
  have hLm : massHalf H M ≤ (L : ℤ) := by
    have h1 : 2 * (H * M) ≤ L := le_max_right _ _
    have h2 : massHalf H M = ((2 * (H * M) : ℕ) : ℤ) := by
      unfold massHalf; push_cast; ring
    rw [h2]
    exact_mod_cast h1
  have hLlaw : pboxSum d (q₁ ω) (q₂ ω) M (symIcc N) f = lawSum d (q₁ ω) (q₂ ω) M (symIcc N) f L :=
    hL d (q₁ ω) (q₂ ω) M N L (symIcc N) f hM hf h2N
  -- (3) the slot-mass upper bound for `‖lawSum‖`
  have hbnd : ‖lawSum d (q₁ ω) (q₂ ω) M (symIcc N) f L‖
      ≤ (endgameK0 η H M) ^ d * massAvg d H M N f := by
    rw [lawSumEqMassBox d (q₁ ω) (q₂ ω) M H L (symIcc N) f
      (fun k => (hb ω k).1) (fun k => (hb ω k).2) hLm]
    have hsl_nn : ∀ (k : Fin d) (n : ℤ), 0 ≤ slotLaw (q₁ ω k) (q₂ ω k) M n := by
      intro k n; rw [slotLaw]; positivity
    calc ‖∑ n ∈ massBox d H M,
            (∏ k : Fin d, (slotLaw (q₁ ω k) (q₂ ω k) M (n k) : ℂ)) * boxMass d (symIcc N) f n‖
        ≤ ∑ n ∈ massBox d H M,
            ‖(∏ k : Fin d, (slotLaw (q₁ ω k) (q₂ ω k) M (n k) : ℂ)) * boxMass d (symIcc N) f n‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ massBox d H M,
            (∏ k : Fin d, slotLaw (q₁ ω k) (q₂ ω k) M (n k)) * ‖boxMass d (symIcc N) f n‖ := by
          apply Finset.sum_congr rfl
          intro n _
          rw [norm_mul]
          congr 1
          rw [norm_prod]
          apply Finset.prod_congr rfl
          intro k _
          simp [abs_of_nonneg (hsl_nn k (n k))]
      _ ≤ ∑ n ∈ massBox d H M,
            (endgameK0 η H M / (4 * (H : ℝ) * (M : ℝ) + 1)) ^ d
              * ‖boxMass d (symIcc N) f n‖ := by
          apply Finset.sum_le_sum
          intro n _
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          have hle := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin d)))
              (f := fun k : Fin d => slotLaw (q₁ ω k) (q₂ ω k) M (n k))
              (g := fun _ : Fin d => endgameK0 η H M / (4 * (H : ℝ) * (M : ℝ) + 1))
              (fun k _ => hsl_nn k (n k))
              (fun k _ => hD (q₁ ω k) (q₂ ω k) M H η (n k) hM hH hη hη1 (hgen ω hωG k))
          simpa [Finset.prod_const, Fintype.card_fin, div_pow] using hle
      _ = (endgameK0 η H M / (4 * (H : ℝ) * (M : ℝ) + 1)) ^ d
            * (∑ n ∈ massBox d H M, ‖boxMass d (symIcc N) f n‖) := by
          rw [Finset.mul_sum]
      _ = (endgameK0 η H M) ^ d * massAvg d H M N f := by
          simp only [massAvg]
          have hc : ((massBoxCard H M : ℝ)) = 4 * (H : ℝ) * (M : ℝ) + 1 := by
            rw [massBoxCard]; push_cast; ring
          rw [hc, div_pow]
          ring
  -- (4) combine with `δ/2 ≤ pbox ω`
  have hstep : δ / 2 ≤ ‖lawSum d (q₁ ω) (q₂ ω) M (symIcc N) f L‖ := by
    have h1 : pbox d (q₁ ω) (q₂ ω) M (symIcc N) f
        = ‖lawSum d (q₁ ω) (q₂ ω) M (symIcc N) f L‖ := by
      unfold pbox
      rw [hLlaw]
    linarith [hω, h1]
  have hhalf : δ / 2 ≤ (endgameK0 η H M) ^ d * massAvg d H M N f := le_trans hstep hbnd
  have hKpos : (0 : ℝ) < endgameK0 η H M := by unfold endgameK0; positivity
  rw [div_le_iff₀ (pow_pos hKpos d)]
  linarith [hhalf, mul_comm ((endgameK0 η H M) ^ d) (massAvg d H M N f)]

end

end Work.Peluse.SwapE
