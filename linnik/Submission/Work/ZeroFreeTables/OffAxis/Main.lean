/-
# ZeroFreeTables/OffAxis/Main

**The off-axis assembly** (OA8 of `OFFAXIS_ROUTE_LEAD.md` §3.2): from the two height-`L`
certificates `RectCertC`, `RectCertS` and Jutila's family density estimate, derive
`Work.ZeroFreeTables.HBOffAxis = ZeroFreeCertOffAxis`.

The shape of the argument: `exists_stripFree_height` (OA4, from Jutila) supplies a *scale*
`L = 50·10^k`, `k ≤ M`, above which the strip `(L, 10L]` is free of zeros with `λ ≤ 2`.
`exists_isRectStrip` (OA5) produces the height-`L` rectangle minimiser `(χ', ρ')`, `RectCertS`
gives HB's Theorems 2/3 for it, and the two branches `λ₁ < 0.695` and `λ₁ ≥ 0.695` are closed by
`offAxis_identify` (OA6) + `offAxis_clauses_of_rectC` (OA3) and by `offAxis_clauses_high` (OA7).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.exists_stripFree_height
import Submission.Work.ZeroFreeTables.OffAxis.exists_isRectStrip
import Submission.Work.ZeroFreeTables.OffAxis.offAxis_identify
import Submission.Work.ZeroFreeTables.OffAxis.offAxis_clauses_high
import Submission.Work.ZeroFreeTables.OffAxis.offAxis_clauses_of_rectC

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract
open Work.ZeroFreeTables.OffAxis

/-- **`HBOffAxis` from the height-`L` certificates and an abstract "strip provider".**

The strip provider is any statement of the shape "there is a scale `50·10^k`, `k ≤ M`, above which
the strip `(50·10^k, 500·10^k]` carries no zero with `λ ≤ 2`".  Both Jutila's
`FamDensityEpsRange (4/5) 1 2` (via `exists_stripFree_height`) and the unified log-free
non-principal estimate `Work.ZeroDensity.LogFree.logFreeNP` (via
`exists_stripFree_height_of_logFreeNP`) supply one. -/
theorem hbOffAxis_of_strip (hC : RectCertC) (hS : RectCertS)
    (hstrip : ∃ M : ℕ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q], ∃ k : ℕ, k ≤ M ∧
      ∀ (χ : DirichletCharacter ℂ q) (u : ℂ),
        IsZAt (10 * ((50 : ℝ) * 10 ^ k)) χ u →
        (50 : ℝ) * 10 ^ k < |u.im| → 2 < lamOf q u) : HBOffAxis := by
  classical
  unfold HBOffAxis ZeroFreeCertOffAxis
  intro lamS _hlamS
  obtain ⟨M, qJ, hstrip_k⟩ := hstrip
  have hL1 : ∀ k : ℕ, (1 : ℝ) ≤ (50 : ℝ) * 10 ^ k := by
    intro k
    have h : (1 : ℝ) ≤ 10 ^ k := one_le_pow₀ (by norm_num)
    calc (1 : ℝ) ≤ 10 ^ k := h
      _ ≤ (50 : ℝ) * 10 ^ k := le_mul_of_one_le_left (by positivity) (by norm_num)
  choose fC hCspec using fun k => hC ((50 : ℝ) * 10 ^ k) (hL1 k)
  choose fS hSspec using fun k => hS ((50 : ℝ) * 10 ^ k) (hL1 k)
  refine ⟨max qJ (max ((Finset.range (M + 1)).sup fC) ((Finset.range (M + 1)).sup fS)), ?_⟩
  intro q hq
  refine fun χ₁ ρ₁ hm hoff => ?_
  have hqJ : qJ ≤ q := (le_max_left _ _).trans hq
  obtain ⟨k, _hkM, hstrip⟩ := hstrip_k q hqJ
  set L : ℝ := (50 : ℝ) * 10 ^ k
  have hL50 : (50 : ℝ) ≤ L := by
    show (50 : ℝ) ≤ (50 : ℝ) * 10 ^ k
    have h : (1 : ℝ) ≤ 10 ^ k := one_le_pow₀ (by norm_num)
    calc (50 : ℝ) = (50 : ℝ) * 1 := (mul_one _).symm
      _ ≤ (50 : ℝ) * 10 ^ k := mul_le_mul_of_nonneg_left h (by norm_num)
  have hstripL : ∀ (χ : DirichletCharacter ℂ q) (u : ℂ),
      IsZAt (10 * L) χ u → L < |u.im| → 2 < lamOf q u := by
    intro χ u hu him
    exact hstrip χ u hu him
  obtain ⟨χ', ρ', hR, _hle⟩ := exists_isRectStrip hL50 hstripL hm
  have hfC_le : fC k ≤ q := by
    have h1 : fC k ≤ (Finset.range (M + 1)).sup fC :=
      Finset.le_sup (Finset.mem_range.mpr (by omega))
    have h2 : (Finset.range (M + 1)).sup fC
        ≤ max ((Finset.range (M + 1)).sup fC) ((Finset.range (M + 1)).sup fS) :=
      le_max_left _ _
    exact (le_trans h1 (le_trans h2 (le_max_right _ _))).trans hq
  have hfS_le : fS k ≤ q := by
    have h1 : fS k ≤ (Finset.range (M + 1)).sup fS :=
      Finset.le_sup (Finset.mem_range.mpr (by omega))
    have h2 : (Finset.range (M + 1)).sup fS
        ≤ max ((Finset.range (M + 1)).sup fC) ((Finset.range (M + 1)).sup fS) :=
      le_max_right _ _
    exact (le_trans h1 (le_trans h2 (le_max_right _ _))).trans hq
  obtain ⟨h0, h2, h3⟩ := hSspec k q hfS_le χ' ρ' hR
  by_cases hlam : lamOf q ρ₁ < 695 / 1000
  · obtain ⟨h348, hZ2, hZ3, hZ4⟩ := hCspec k q hfC_le χ₁ ρ₁
      (offAxis_identify hL50 hm hR h0 h2 hlam) hoff
    exact offAxis_clauses_of_rectC lamS h348 hZ2 hZ3 hZ4
  · push_neg at hlam
    exact offAxis_clauses_high hL50 lamS hm h2 h3 hlam

/-- **`HBOffAxis` from the height-`L` certificates and Jutila** (`FamDensityEpsRange (4/5) 1 2`). -/
theorem hbOffAxis_of_rect (hC : RectCertC) (hS : RectCertS)
    (hJ : Work.ZeroDensity.FamDensityEpsRange (4/5) 1 2) : HBOffAxis :=
  hbOffAxis_of_strip hC hS (exists_stripFree_height hJ)

end Work.ZeroFreeTables
