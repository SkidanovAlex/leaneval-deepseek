import Mathlib
import Submission.Work.GM.S3.Gen.cs_defs
import Submission.Work.GM.S3.norm_Iterm_le_Rtilde_of_domain

/-!
# The per-cell bound of the cell decomposition of GM 7.2

This file proves `Work.GM.S3.Gen.cs_cell_bound`: the contribution of a single cell

`csCell N δ i j k = idx1 (Mdy N δ i) × idxM (Mdy N δ j) × idxM (Mdy N δ k)`

of the cell decomposition of GM Proposition 7.2 to `Σ ‖I_m‖` is at most

`C (N²/Bdy j) · S30g(cell, Bdy j) + C N^{-20} · #cell`,

where `Bdy N δ (δ/2) j = Mdy N δ j / (2 (M N)^{δ/2})` is the smoothing *matched* to the cell: the
second coordinate of a triple of the cell satisfies `|m₂| > Mdy N δ j`, so the hypothesis
`B (M N)^{δ/2} ≤ |m₂|/2` of the per-`m` estimate `Work.GM.S3.norm_Iterm_le_Rtilde_of_domain`
holds, and the estimate gives, for `u ∈ csCell`,

`‖Iterm N W u‖ ≤ C (N²/Bdy j) ∫_{1/2}^{2} csF(u) + C N^{-20}`,

with `csF(u)(v) = ‖R(v)‖ R̃(arg1 u₁(-u₂)u₃ v) R̃(arg2 u₁(-u₂)u₃ v)`.

The only point of care is the sign of the second coordinate: the estimate produces the arguments
`arg1 m₁ (-m₂) m₃`, `arg2 m₁ (-m₂) m₃`, whereas `S30g` uses `arg1 m₁ m₂ m₃`,
`arg2 m₁ m₂ m₃`.  The substitution `m₂ ↦ -m₂` is an involution of the cell and turns one integrand
into the other (`csF_eq_csG_neg`), so the sum of the integrals over the cell is `S30g` itself.
-/

namespace Work.GM.S3.Gen

open Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Iterm Rfun)

noncomputable section

/-! ## The two integrands -/

namespace CellBd

/-- The integrand of the per-`m` estimate `Work.GM.S3.norm_Iterm_le_Rtilde_of_domain` for the
frequency triple `u = (u₁,u₂,u₃)`, namely `‖R(v)‖ R̃(arg1 u₁(-u₂)u₃ v) R̃(arg2 u₁(-u₂)u₃ v)`;
the middle coordinate is negated, as in that estimate. -/
def csF (N : ℕ) (W : Finset ℝ) (B : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℤ × ℤ × ℤ) (v : ℝ) : ℝ :=
  ‖Rfun W v‖ * Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg1 u.1 (-u.2.1) u.2.2 v) *
    Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg2 u.1 (-u.2.1) u.2.2 v)

/-- The integrand of `S30g`, i.e. the same expression without the negation of the middle
coordinate. -/
def csG (N : ℕ) (W : Finset ℝ) (B : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℤ × ℤ × ℤ) (v : ℝ) : ℝ :=
  ‖Rfun W v‖ * Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg1 u.1 u.2.1 u.2.2 v) *
    Work.GM.S3.Rtilde W N B ψ₁ ψ₂ (Work.GM.S3.arg2 u.1 u.2.1 u.2.2 v)

/-- Negating the middle coordinate turns `csF` into `csG`. -/
theorem csF_eq_csG_neg (N : ℕ) (W : Finset ℝ) (B : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (u : ℤ × ℤ × ℤ) (v : ℝ) :
    CellBd.csF N W B ψ₁ ψ₂ u v = CellBd.csG N W B ψ₁ ψ₂ (u.1, -u.2.1, u.2.2) v := by
  simp only [CellBd.csF, CellBd.csG]

/-- `Bdy N δ η j * (M N)^η = Mdy N δ j / 2`: the smoothing `Bdy` is *matched* to the dyadic
scale `Mdy`, which is exactly the hypothesis `B (M N)^η ≤ |m₂|/2` of the per-`m` estimate for a
triple whose second coordinate lies in the window of scale `Mdy N δ j`. -/
theorem Bdy_mul_rpow {N : ℕ} (hN : 1 ≤ N) (δ η : ℝ) (j : ℕ) :
    Bdy N δ η j * (Submission.LargeValues.M N) ^ η = Mdy N δ j / 2 := by
  have hx : (Submission.LargeValues.M N) ^ η ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (Submission.LargeValues.M_ge_one hN)) η)
  rw [Bdy, div_mul_eq_mul_div, mul_div_mul_right _ _ hx]

end CellBd

open CellBd

/-! ## The per-cell bound -/

theorem cs_cell_bound :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∀ (ψ₁ ψ₂ : ℝ → ℝ), Work.GM.S3.IsBumpAtZero ψ₁ 4 → Work.GM.S3.IsBumpAtOne ψ₂ 4 →
      (∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x) → (∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x) →
    ∀ i j k : ℕ,
      (∑ u ∈ Work.GM.S3.Gen.csCell N δ i j k, ‖Submission.GM.Iterm N W u‖) ≤
        C * ((N : ℝ) ^ 2 / Work.GM.S3.Gen.Bdy N δ (δ / 2) j) *
          Work.GM.S3.Gen.S30g N W (Work.GM.S3.Gen.Bdy N δ (δ / 2) j)
            (Work.GM.S3.Gen.Mdy N δ i) (Work.GM.S3.Gen.Mdy N δ j) (Work.GM.S3.Gen.Mdy N δ k)
            ψ₁ ψ₂ +
        C * (N : ℝ) ^ (-20 : ℤ) * ((Work.GM.S3.Gen.csCell N δ i j k).card : ℝ) := by
  intro ε δ hε hδ
  obtain ⟨C₁, hC₁pos, N₀₁, hper⟩ :=
    Work.GM.S3.norm_Iterm_le_Rtilde_of_domain ε (δ / 2) hε (by linarith)
  refine ⟨C₁, hC₁pos, max N₀₁ 1, ?_⟩
  intro N hN W hW hsep ψ₁ ψ₂ hb1 hb2 hψ1ge hψ2ge i j k
  have hN1 : 1 ≤ N := le_trans (le_max_right N₀₁ 1) hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have hKpos : 0 < Klev N δ := csKlev_pos hN1 δ
  have hBpos : 0 < Bdy N δ (δ / 2) j := Bdy_pos hN1 hKpos
  have hNB : 0 < (N : ℝ) * Bdy N δ (δ / 2) j := mul_pos hN0 hBpos
  set S : Finset (ℤ × ℤ × ℤ) := csCell N δ i j k with hS
  have hmem : ∀ u ∈ S, u.2.1 ∈ idxM (Mdy N δ j) := fun u hu =>
    (mem_csCell.mp (hS ▸ hu)).2.1
  -- the per-`m` estimate, for each triple of the cell
  have hstepA : ∀ u ∈ S, ‖Iterm N W u‖ ≤
      C₁ * ((N : ℝ) ^ 2 / Bdy N δ (δ / 2) j) *
        (∫ v in (1 / 2 : ℝ)..2, CellBd.csF N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v)
      + C₁ * (N : ℝ) ^ (-20 : ℤ) := by
    intro u hu
    have hlt : Mdy N δ j < |((u.2.1 : ℤ) : ℝ)| := (Finset.mem_filter.mp (hmem u hu)).2
    have hsp : Bdy N δ (δ / 2) j * (Submission.LargeValues.M N) ^ (δ / 2)
        ≤ |((u.2.1 : ℤ) : ℝ)| / 2 := by
      rw [CellBd.Bdy_mul_rpow hN1]
      linarith
    have h := hper N (le_trans (le_max_left N₀₁ 1) hN) W hW hsep
      (Bdy N δ (δ / 2) j) ψ₁ ψ₂ hb1 hb2 hψ1ge hψ2ge hNB u.1 u.2.1 u.2.2 hsp
    simpa only [CellBd.csF, Prod.mk.eta] using h
  have hsum1 : (∑ u ∈ S, ‖Iterm N W u‖) ≤ ∑ u ∈ S,
      (C₁ * ((N : ℝ) ^ 2 / Bdy N δ (δ / 2) j) *
        (∫ v in (1 / 2 : ℝ)..2, CellBd.csF N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v)
      + C₁ * (N : ℝ) ^ (-20 : ℤ)) :=
    Finset.sum_le_sum hstepA
  have hsum2 : (∑ u ∈ S,
      (C₁ * ((N : ℝ) ^ 2 / Bdy N δ (δ / 2) j) *
        (∫ v in (1 / 2 : ℝ)..2, CellBd.csF N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v)
      + C₁ * (N : ℝ) ^ (-20 : ℤ)))
      = C₁ * ((N : ℝ) ^ 2 / Bdy N δ (δ / 2) j) *
          (∑ u ∈ S, (∫ v in (1 / 2 : ℝ)..2, CellBd.csF N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v))
        + C₁ * (N : ℝ) ^ (-20 : ℤ) * (S.card : ℝ) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.mul_sum]
    · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- the sum of the integrals is `S30g`: substitute `m₂ ↦ -m₂` (an involution of the cell)
  have hpt : ∀ u ∈ S, (∫ v in (1 / 2 : ℝ)..2, CellBd.csF N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v)
      = ∫ v in (1 / 2 : ℝ)..2,
          CellBd.csG N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ (u.1, -u.2.1, u.2.2) v := by
    intro u hu
    have hfun : (fun v : ℝ => CellBd.csF N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v)
        = fun v : ℝ => CellBd.csG N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ (u.1, -u.2.1, u.2.2) v :=
      funext fun v => CellBd.csF_eq_csG_neg N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v
    rw [hfun]
  have hA1 : (∑ u ∈ S, (∫ v in (1 / 2 : ℝ)..2, CellBd.csF N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v))
      = ∑ u ∈ S, (∫ v in (1 / 2 : ℝ)..2,
          CellBd.csG N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ (u.1, -u.2.1, u.2.2) v) :=
    Finset.sum_congr rfl hpt
  have hA2 : (∑ u ∈ S, (∫ v in (1 / 2 : ℝ)..2,
          CellBd.csG N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ (u.1, -u.2.1, u.2.2) v))
      = ∑ u ∈ S, (∫ v in (1 / 2 : ℝ)..2, CellBd.csG N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v) := by
    refine Finset.sum_nbij' (fun u : ℤ × ℤ × ℤ => (u.1, -u.2.1, u.2.2))
      (fun u : ℤ × ℤ × ℤ => (u.1, -u.2.1, u.2.2)) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      have hu' := mem_csCell.mp (hS ▸ hu)
      rw [mem_csCell]
      exact ⟨hu'.1, mem_idxM_neg_iff.mpr hu'.2.1, hu'.2.2⟩
    · intro u hu
      have hu' := mem_csCell.mp (hS ▸ hu)
      rw [mem_csCell]
      exact ⟨hu'.1, mem_idxM_neg_iff.mpr hu'.2.1, hu'.2.2⟩
    · intro u hu; exact Prod.ext rfl (Prod.ext (neg_neg _) rfl)
    · intro u hu; exact Prod.ext rfl (Prod.ext (neg_neg _) rfl)
    · intro u hu; rfl
  have hA3 : (∑ u ∈ S, (∫ v in (1 / 2 : ℝ)..2, CellBd.csG N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v))
      = S30g N W (Bdy N δ (δ / 2) j) (Mdy N δ i) (Mdy N δ j) (Mdy N δ k) ψ₁ ψ₂ := by
    have hcc : csCell N δ i j k
        = idx1 (Mdy N δ i) ×ˢ (idxM (Mdy N δ j) ×ˢ idxM (Mdy N δ k)) := rfl
    simp only [S30g, csG, hS, hcc, Finset.sum_product]
  have hmain : (∑ u ∈ S, (∫ v in (1 / 2 : ℝ)..2, CellBd.csF N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v))
      = S30g N W (Bdy N δ (δ / 2) j) (Mdy N δ i) (Mdy N δ j) (Mdy N δ k) ψ₁ ψ₂ :=
    hA1.trans (hA2.trans hA3)
  calc ∑ u ∈ S, ‖Iterm N W u‖
      ≤ ∑ u ∈ S,
          (C₁ * ((N : ℝ) ^ 2 / Bdy N δ (δ / 2) j) *
            (∫ v in (1 / 2 : ℝ)..2, CellBd.csF N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v)
          + C₁ * (N : ℝ) ^ (-20 : ℤ)) := hsum1
    _ = C₁ * ((N : ℝ) ^ 2 / Bdy N δ (δ / 2) j) *
          (∑ u ∈ S, (∫ v in (1 / 2 : ℝ)..2, CellBd.csF N W (Bdy N δ (δ / 2) j) ψ₁ ψ₂ u v))
        + C₁ * (N : ℝ) ^ (-20 : ℤ) * (S.card : ℝ) := hsum2
    _ = C₁ * ((N : ℝ) ^ 2 / Bdy N δ (δ / 2) j) *
          S30g N W (Bdy N δ (δ / 2) j) (Mdy N δ i) (Mdy N δ j) (Mdy N δ k) ψ₁ ψ₂
        + C₁ * (N : ℝ) ^ (-20 : ℤ) * (S.card : ℝ) := by rw [hmain]

end

end Work.GM.S3.Gen
