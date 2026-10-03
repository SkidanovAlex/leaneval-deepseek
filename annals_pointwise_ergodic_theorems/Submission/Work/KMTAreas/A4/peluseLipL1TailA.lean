/-
# Area A4: `peluseLipL1TailA` — Proposition `lip` with a free support window `A N^d`

`A4/peluseLipL1Tail.lean` states Proposition `lip` of Krause--Mirek--Tao, §5.1, with the support
window pinned to `N₀ ≤ 2 N^d`.  The pin is too tight (`NOTES_A4_window_pin_GAP.md`): the §5.1
chain needs `N₀ ∈ [N^d/A, A N^d]` with `A` a *P-dependent* constant, and for `P = 100 X²` the
pinned statement is provably vacuous.  This module proves the free-window form

`∀ A ≥ 1, ∃ C K > 0, ∀ N N₀ δ f g h, N₀ ∈ [N^d/A, A N^d] → ...`

with `C, K` allowed to depend on `A`, splitting on the size of `N`:

* **case A** (`N ≤ C δ^{-K}`, i.e. `N` small): the dual function `Ã_N^*(h,g)` of the transposed
  average, cut to the ball of radius `⌊A N^d⌋` (and normalised by `δ^{K-1}`) is a witness; the
  spatial tail beyond `A N^d` *vanishes identically*.  Proved here as `lipL1Tail_caseA`.
* **case B** (`C δ^{-K} < N`, i.e. `N` large): the smoothing construction of §5.1, with the
  truncation radius `D = ⌊A N^d⌋`; proved in `A4/lipL1TailCaseBA.lean`
  (`Work.KMTAreas.A4.lipL1TailCaseBA`).

The two cases are combined in `peluseLipL1TailA` by taking the maximum of the two constant pairs
(monotonicity of `C δ^{-K}`, `δ^K N^d` in `(C,K)` under `C ≤`, `K ≤` and `0 < δ ≤ 1`).

## Status and recipe (for a later session)

* **Case A** is proved here (`lipL1Tail_caseA`): for *any* `C ≥ 2A + 2` and `K ≥ 1`, the hypothesis
  `N ≤ C δ^{-K}` yields the conclusion with those same constants, by truncating the transposed
  dual `Ã_N^*(h,g)` to the ball of radius `D = ⌊A N^d⌋` and scaling by `δ^{K-1}` (the tail beyond
  `A N^d` then vanishes identically).
* **Case B** (`C δ^{-K} < N`) is the §5.1 smoothing construction.  It is delegated as
  `Work.KMTAreas.A4.lipL1TailCaseBA` (`A4/lipL1TailCaseBA.lean`), whose statement is this module's
  conclusion with constants `(C_B, K_B)` and the extra hypothesis `C_B δ^{-K_B} < N`.
  **Recipe** (all of it is constants; every analytic input already exists as a lemma):
  with `u := ⌈K₀⌉ + 1` from the Peluse dichotomy `hPel A hA` (which gives `C₀, K₀`, `q ≤ C₀ δ^{-K₀}`,
  `N' ≤ N`, `δ^{K₀}N ≤ C₀N'` and `δ^{K₀}N^d ≤ C₀ ∑_x ‖lipProg N' q f x‖`), and
  `c₁ := 1 + 4 C₀ (calcConst ψ) K'`:
  - truncation radius `D := ⌊A N^d⌋` (`winA`), window `MW := D - q N'`,
    `G := sign(lipProg N' q f)` cut to `[-MW,MW]`, `w := lipWeight ψ ε N'`, `F₀ := smoothOp w G q`,
    `F := λ • F₀` with `λ := 4 C₀ δ^{Kc - u}` and `ε := min (δ^u / c₁) (C δ^{-Kc} / (2N))`;
  - the *only* two facts that depend on the window are `N₀ ≤ D` and `q N' ≤ D` (both from
    `le_winA`, as `N₀` and `q N'` are naturals) and the mass bound `2 MW + 1 ≤ K' δ^{-u} N^d`,
    which needs `K' ≥ 2A + 2`;
  - take `Kc ≥ 4u` (e.g. `5u + 6`) and `C` dominating the finitely many expressions in
    `C₀, Kw, Cm, c₁, c₂, K', calcConst ψ, A` that appear; every "`N` is large enough" step is
    `winA_master` (`α δ^{-A} ≤ N^j` from `α ≤ C^j`, `A ≤ K j`) or `winA_rpow_low` (`C/N ≤ δ^P`),
    and the two sub-cases of the `min` in `ε` reproduce the two branches of the A = 2 proof;
  - the tail clause holds *exactly* (not just up to constants): the un-scaled tail is
    `≤ q Cm/ε ≤ δ^u N^d/(8C₀)`, and `λ · δ^u N^d/(8C₀) = δ^{Kc} N^d / 2`; in particular a larger
    `Kc` is *not* an obstruction to the tail clause, only to the two bounds `λ ≤ C δ^{-Kc}` and
    `λ · ℓ¹(F₀) ≤ C δ^{-Kc} N^d`, both of which improve as `Kc` grows.
* The assembly below takes `C := max (2A+2) C_B`, `K := max 1 K_B`, uses case A when
  `N ≤ C_B δ^{-K_B}` and otherwise case B, and — because the tail clause *tightens* as `K` grows —
  rescales the case-B witness by `c := δ^{K - K_B} ≤ 1` before upgrading its constants.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.windowA
import Submission.Work.KMTAreas.A4.lipL1TailCaseBA

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Case A: `N` small -/

/-- **Case A of the free-window Proposition `lip`.**  If `C ≥ 2A + 2` and `K ≥ 1`, `A ≥ 1` and
`N ≤ C δ^{-K}`, then the transposed dual function `Ã_N^*(h,g)`, cut to the ball of radius
`⌊A N^d⌋` and scaled by `δ^{K-1}`, satisfies all the requirements of Proposition `lip` with the
constants `C, K` and the tail threshold `A N^d` (outside which it vanishes). -/
theorem lipL1Tail_caseA (P : Polynomial ℤ) (A C K : ℝ) (hA : 1 ≤ A)
    (hC : 2 * A + 2 ≤ C) (hK : 1 ≤ K) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
      (N : ℝ) ^ P.natDegree / A ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
      SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
      (N : ℝ) ≤ C * δ⁻¹ ^ K →
      ∃ (F : ℤ → ℂ) (l : ℕ) (k : ℤ),
        (∀ x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K) ∧
        Summable (fun x : ℤ => ‖F x‖) ∧
        (∑' x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
        (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖F x‖ else 0)
          ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧
        FourierSupportIn F (majorArc ρ l k) ∧
        (2 : ℝ) ^ l ≤ C * δ⁻¹ ^ K ∧
        (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ∧
        δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F‖ := by
  intro ρ hρpos hρle N N₀ δ f g h hN hδpos hδle _hN₀lo hN₀hi hfs hgs hhs hfb hgb hhb hcorr hsmall
  have hδ0 : 0 < δ⁻¹ := inv_pos.mpr hδpos
  have hδ1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδpos).mpr hδle
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
  have hA0' : (0 : ℝ) ≤ A := hA0.le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hC1 : (1 : ℝ) ≤ C := by linarith
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hNd1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ (by exact_mod_cast hN)
  have hD1K : (1 : ℝ) ≤ δ⁻¹ ^ K := Real.one_le_rpow hδ1 hK0
  have hCK : (1 : ℝ) ≤ C * δ⁻¹ ^ K := by nlinarith [hC1, hD1K]
  -- the transposed dual function
  set F₀ : ℤ → ℂ := AhalfTranspose N P h g with hF₀def
  have hF₀sup : ∀ x : ℤ, ‖F₀ x‖ ≤ 1 := fun x => lipNormAhalfTranspose hN P hhb hgb x
  -- the truncation radius
  set D : ℕ := winA A N P.natDegree with hDdef
  have hDle : (D : ℝ) ≤ A * (N : ℝ) ^ P.natDegree := by
    rw [hDdef]; exact winA_le A hA0' N P.natDegree
  have hN₀D : N₀ ≤ D := by
    rw [hDdef]; exact le_winA A hN₀hi
  -- the scaling
  set lam : ℝ := δ ^ (K - 1) with hlamdef
  have hlampos : 0 < lam := Real.rpow_pos_of_pos hδpos _
  have hlamle1 : lam ≤ 1 := Real.rpow_le_one hδpos.le hδle (by linarith)
  have hlamnorm : ‖((lam : ℝ) : ℂ)‖ = lam := by
    rw [Complex.norm_real, Real.norm_of_nonneg hlampos.le]
  have hδK_eq : lam * δ = δ ^ K := by
    have h1 : δ ^ K = δ ^ (K - 1) * δ := by
      conv_lhs => rw [show K = (K - 1) + 1 by ring]
      rw [Real.rpow_add hδpos, Real.rpow_one]
    rw [hlamdef, h1]
  -- the witness, truncated to the ball of radius `D`
  set F : ℤ → ℂ := fun x => ((lam : ℝ) : ℂ) * (if x.natAbs ≤ D then F₀ x else 0) with hFdef
  have hFvan : ∀ x : ℤ, D < x.natAbs → F x = 0 := by
    intro x hx
    have hx' : ¬ (x.natAbs ≤ D) := by omega
    change ((lam : ℝ) : ℂ) * (if x.natAbs ≤ D then F₀ x else 0) = 0
    rw [if_neg hx', mul_zero]
  have hcut : ∀ x : ℤ, ‖(if x.natAbs ≤ D then F₀ x else 0 : ℂ)‖ ≤ 1 := by
    intro x
    by_cases hx : x.natAbs ≤ D
    · rw [if_pos hx]; exact hF₀sup x
    · rw [if_neg hx]; simp
  refine ⟨F, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. the sup bound
    intro x
    rw [hFdef, norm_mul, hlamnorm]
    calc lam * ‖(if x.natAbs ≤ D then F₀ x else 0 : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul hlamle1 (hcut x) (norm_nonneg _) (by norm_num)
      _ ≤ C * δ⁻¹ ^ K := by linarith
  · -- 2. summability
    refine summable_of_ne_finset_zero (s := Finset.Icc (-(D : ℤ)) (D : ℤ)) fun x hx => ?_
    simp only [Finset.mem_Icc, not_and_or, not_le] at hx
    rw [hFvan x (by rcases hx with h' | h' <;> omega), norm_zero]
  · -- 3. the `ℓ¹` bound
    rw [hFdef]
    have hnorm_smul : (∑' x : ℤ, ‖((lam : ℝ) : ℂ) *
          (if x.natAbs ≤ D then F₀ x else 0 : ℂ)‖)
        = lam * ∑' x : ℤ, ‖(if x.natAbs ≤ D then F₀ x else 0 : ℂ)‖ := by
      rw [← tsum_mul_left]
      exact tsum_congr fun x => by rw [norm_mul, hlamnorm]
    rw [hnorm_smul]
    have h3 : (∑' x : ℤ, ‖(if x.natAbs ≤ D then F₀ x else 0 : ℂ)‖) ≤ 2 * (D : ℝ) + 1 := by
      have hsupp : SupportIn (fun x : ℤ => (if x.natAbs ≤ D then F₀ x else 0 : ℂ)) D := by
        intro x hx
        have hx' : ¬ (x.natAbs ≤ D) := by omega
        simp only [if_neg hx']
      have h1 := ellOne_le_of_supportIn (fun x : ℤ => (if x.natAbs ≤ D then F₀ x else 0 : ℂ))
        D hsupp hcut
      simpa [ellOne] using h1
    have hDle' : 2 * (D : ℝ) + 1 ≤ (2 * A + 2) * (N : ℝ) ^ P.natDegree := by
      nlinarith [hDle, hNd1]
    calc lam * (∑' x : ℤ, ‖(if x.natAbs ≤ D then F₀ x else 0 : ℂ)‖)
        ≤ lam * (2 * (D : ℝ) + 1) := mul_le_mul_of_nonneg_left h3 hlampos.le
      _ ≤ 1 * ((2 * A + 2) * (N : ℝ) ^ P.natDegree) :=
          mul_le_mul hlamle1 hDle' (by positivity) (by norm_num)
      _ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := by
          have h4 : (2 * A + 2) * (N : ℝ) ^ P.natDegree ≤ C * (N : ℝ) ^ P.natDegree :=
            mul_le_mul_of_nonneg_right hC (by positivity)
          have h5 : C * (N : ℝ) ^ P.natDegree
              ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_left (by positivity : (0:ℝ) ≤ (N:ℝ) ^ P.natDegree) hD1K)
              (by linarith)
          calc 1 * ((2 * A + 2) * (N : ℝ) ^ P.natDegree)
              = (2 * A + 2) * (N : ℝ) ^ P.natDegree := by ring
            _ ≤ C * (N : ℝ) ^ P.natDegree := h4
            _ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := h5
  · -- 4. the spatial tail vanishes beyond `A N^d`
    refine le_trans (le_of_eq ?_) (by positivity)
    rw [show (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖F x‖ else 0))
        = ∑' x : ℤ, (0 : ℝ) from tsum_congr fun x => ?_, tsum_zero]
    by_cases hx : A * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
    · have hxD : D < x.natAbs := by
        rw [hDdef]; exact winA_lt_natAbs hA0' hx
      rw [if_pos hx, hFvan x hxD, norm_zero]
    · rw [if_neg hx]
  · -- 5. Fourier support (vacuous: the arc `𝓜_{≤0,≤0}` is everything)
    rw [lipMajorArcZeroZero hρpos hρle]
    intro ξ hξ
    exact absurd (Set.mem_univ ξ) hξ
  · -- 6. the linear scale
    have h1 : (2 : ℝ) ^ (0 : ℕ) = 1 := by norm_num
    rw [h1]
    exact hCK
  · -- 7. the continuous scale
    have h1 : (2 : ℝ) ^ (0 : ℤ) = 1 := by norm_num
    rw [h1, one_le_div hNpos]
    exact hsmall
  · -- 8. the correlation
    have hpair : bilinPair f F = ((lam : ℝ) : ℂ) *
        (∑' x : ℤ, f x * (if x.natAbs ≤ D then F₀ x else 0 : ℂ)) := by
      rw [hFdef, bilinPair]
      calc ∑' x : ℤ, f x * (((lam : ℝ) : ℂ) * (if x.natAbs ≤ D then F₀ x else 0))
          = ∑' x : ℤ, ((lam : ℝ) : ℂ) * (f x * (if x.natAbs ≤ D then F₀ x else 0)) :=
            tsum_congr fun x => by ring
        _ = ((lam : ℝ) : ℂ) * ∑' x : ℤ, f x * (if x.natAbs ≤ D then F₀ x else 0) :=
            tsum_mul_left
    have htrunc : (∑' x : ℤ, f x * (if x.natAbs ≤ D then F₀ x else 0 : ℂ))
        = bilinPair f F₀ := by
      rw [bilinPair]
      refine tsum_congr fun x => ?_
      by_cases hx : f x = 0
      · rw [hx, zero_mul, zero_mul]
      · have hx' : x.natAbs ≤ N₀ := winA_supportIn_natAbs_le hfs hx
        rw [if_pos (le_trans hx' hN₀D)]
    have hdual : bilinPair f F₀ = bilinPair (AhalfZ N P f g) h := by
      rw [show bilinPair f F₀ = bilinPair F₀ f from lipBilinPairComm f F₀, hF₀def]
      exact (bilinPair_AhalfZ_eq_transpose (FinSupp.of_supportIn hfs) (FinSupp.of_supportIn hgs)
        (FinSupp.of_supportIn hhs) N P).symm
    rw [hpair, htrunc, hdual, norm_mul, hlamnorm]
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hcorr hlampos.le)
    rw [← mul_assoc lam δ ((N : ℝ) ^ P.natDegree), hδK_eq]

/-! ## Assembly of the two cases

The two branches are proved with independently chosen constants; the assembly uses
`C := max (2A + 2) C_B` and `K := max 1 K_B` (with `(C_B, K_B)` the case-B pair).  The tail
clause `∑_{|x| > A N^d} ‖F x‖ ≤ δ^K N^d / 2` *tightens* as `K` grows, so the case-B witness is
rescaled by `c := δ^{K - K_B} ≤ 1` (which multiplies its correlation with `f` by `c` and its tail
by `c`, and leaves the Fourier support unchanged). -/

theorem peluseLipL1TailA (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (hPel : Work.KMTContract.PeluseInverseKMT P) : ∀ (A : ℝ), 1 ≤ A → ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 → (N : ℝ) ^ P.natDegree / A ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree → Work.Analysis.InverseTheory.SupportIn f N₀ → Work.Analysis.InverseTheory.SupportIn g N₀ → Work.Analysis.InverseTheory.SupportIn h N₀ → (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) → δ * (N : ℝ) ^ P.natDegree ≤ ‖Work.Analysis.InverseTheory.bilinPair (Work.Analysis.InverseTheory.AhalfZ N P f g) h‖ → ∃ (F : ℤ → ℂ) (l : ℕ) (k : ℤ), (∀ x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K) ∧ Summable (fun x : ℤ => ‖F x‖) ∧ (∑' x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧ (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖F x‖ else 0) ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧ Work.Analysis.InverseTheory.FourierSupportIn F (Work.Analysis.InverseTheory.majorArc ρ l k) ∧ (2 : ℝ) ^ l ≤ C * δ⁻¹ ^ K ∧ (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ∧ δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖Work.Analysis.InverseTheory.bilinPair f F‖ := by
  intro A hA
  obtain ⟨Cb, Kb, hCbpos, hKbpos, hB⟩ := lipL1TailCaseBA P hP hPel A hA
  set K : ℝ := max 1 Kb with hKdef
  set C : ℝ := max (2 * A + 2) Cb with hCdef
  have hK1 : 1 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hKbK : Kb ≤ K := by rw [hKdef]; exact le_max_right _ _
  have h2A2 : (2 * A + 2 : ℝ) ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCbC : Cb ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hCpos : 0 < C := by linarith [h2A2, hA]
  have hKpos : 0 < K := by linarith [hK1]
  refine ⟨C, K, hCpos, hKpos, ?_⟩
  intro ρ hρpos hρle N N₀ δ f g h hN hδpos hδle hN₀lo hN₀hi hfs hgs hhs hfb hgb hhb hcorr
  have hδ1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδpos).mpr hδle
  have hδinv_mono : δ⁻¹ ^ Kb ≤ δ⁻¹ ^ K := Real.rpow_le_rpow_of_exponent_le hδ1 hKbK
  have hCb_le_C : Cb * δ⁻¹ ^ Kb ≤ C * δ⁻¹ ^ K :=
    mul_le_mul hCbC hδinv_mono (Real.rpow_nonneg (le_trans zero_le_one hδ1) Kb) hCpos.le
  by_cases hBlarge : Cb * δ⁻¹ ^ Kb < (N : ℝ)
  · -- case B (`N` large): rescale the smoothing-construction witness by `c = δ^{K - Kb}`
    obtain ⟨F, l, k, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      hB ρ hρpos hρle N N₀ δ f g h hN hδpos hδle hN₀lo hN₀hi hfs hgs hhs hfb hgb hhb hcorr
        hBlarge
    set c : ℝ := δ ^ (K - Kb) with hcdef
    have hcpos : 0 < c := Real.rpow_pos_of_pos hδpos _
    have hcle1 : c ≤ 1 := Real.rpow_le_one hδpos.le hδle (by linarith)
    have hcKb : c * δ ^ Kb = δ ^ K := by
      rw [hcdef, ← Real.rpow_add hδpos (K - Kb) Kb]
      congr 1
      ring
    have hnormc : ‖((c : ℝ) : ℂ)‖ = c := by
      rw [Complex.norm_real, Real.norm_of_nonneg hcpos.le]
    set F' : ℤ → ℂ := ((c : ℝ) : ℂ) • F with hF'def
    refine ⟨F', l, k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 1. the sup bound
      intro x
      change ‖((c : ℝ) : ℂ) • F x‖ ≤ C * δ⁻¹ ^ K
      rw [norm_smul, hnormc]
      calc c * ‖F x‖ ≤ 1 * (Cb * δ⁻¹ ^ Kb) :=
            mul_le_mul hcle1 (h1 x) (norm_nonneg _) (by norm_num)
        _ = Cb * δ⁻¹ ^ Kb := by ring
        _ ≤ C * δ⁻¹ ^ K := hCb_le_C
    · -- 2. summability
      refine (h2.mul_left c).congr fun x => ?_
      change c * ‖F x‖ = ‖((c : ℝ) : ℂ) • F x‖
      rw [norm_smul, hnormc]
    · -- 3. the `ℓ¹` bound
      have hsum : (∑' x : ℤ, ‖((c : ℝ) : ℂ) • F x‖) = c * ∑' x : ℤ, ‖F x‖ := by
        rw [← tsum_mul_left]
        exact tsum_congr fun x => by rw [norm_smul, hnormc]
      change (∑' x : ℤ, ‖((c : ℝ) : ℂ) • F x‖)
          ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree
      rw [hsum]
      calc c * (∑' x : ℤ, ‖F x‖) ≤ c * (Cb * δ⁻¹ ^ Kb * (N : ℝ) ^ P.natDegree) :=
            mul_le_mul_of_nonneg_left h3 hcpos.le
        _ ≤ 1 * (Cb * δ⁻¹ ^ Kb * (N : ℝ) ^ P.natDegree) :=
            mul_le_mul_of_nonneg_right hcle1 (by positivity)
        _ = Cb * (δ⁻¹ ^ Kb * (N : ℝ) ^ P.natDegree) := by ring
        _ ≤ Cb * (δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hδinv_mono (by positivity)) hCbpos.le
        _ = Cb * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := by ring
        _ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCbC (by positivity)) (by positivity)
    · -- 4. the spatial tail (exactly normalised by `c δ^{Kb} = δ^K`)
      have htail : (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖F' x‖ else 0))
          = c * ∑' x : ℤ,
              (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖F x‖ else 0) := by
        rw [← tsum_mul_left]
        refine tsum_congr fun x => ?_
        by_cases hx : A * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
        · rw [if_pos hx, if_pos hx]
          change ‖((c : ℝ) : ℂ) • F x‖ = c * ‖F x‖
          rw [norm_smul, hnormc]
        · rw [if_neg hx, if_neg hx, mul_zero]
      rw [htail]
      calc c * (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖F x‖ else 0))
          ≤ c * (δ ^ Kb * (N : ℝ) ^ P.natDegree / 2) :=
            mul_le_mul_of_nonneg_left h4 hcpos.le
        _ = δ ^ K * (N : ℝ) ^ P.natDegree / 2 := by
            rw [← hcKb]
            ring
    · -- 5. Fourier support
      intro ξ hξ
      change ZFourier (((c : ℝ) : ℂ) • F) ξ = 0
      rw [ZFourier_smul, h5 ξ hξ, mul_zero]
    · -- 6. the linear scale
      exact le_trans h6 hCb_le_C
    · -- 7. the continuous scale
      calc (2 : ℝ) ^ k ≤ Cb * δ⁻¹ ^ Kb / (N : ℝ) := h7
        _ ≤ C * δ⁻¹ ^ K / (N : ℝ) := div_le_div_of_nonneg_right hCb_le_C (by positivity)
    · -- 8. the correlation (scaled by `c`, normalised by `c δ^{Kb} = δ^K`)
      have hpair : bilinPair f F' = ((c : ℝ) : ℂ) * bilinPair f F := by
        have hpt : ∀ x : ℤ, f x * F' x = ((c : ℝ) : ℂ) * (f x * F x) := by
          intro x
          change f x * (((c : ℝ) : ℂ) • F x) = ((c : ℝ) : ℂ) * (f x * F x)
          ring
        rw [bilinPair, bilinPair]
        calc ∑' x : ℤ, f x * F' x = ∑' x : ℤ, ((c : ℝ) : ℂ) * (f x * F x) :=
              tsum_congr hpt
          _ = ((c : ℝ) : ℂ) * ∑' x : ℤ, f x * F x := tsum_mul_left
      rw [hpair, norm_mul, hnormc]
      have hcorr' : δ ^ K * (N : ℝ) ^ P.natDegree
          = c * (δ ^ Kb * (N : ℝ) ^ P.natDegree) := by
        rw [← hcKb]
        ring
      rw [hcorr']
      exact mul_le_mul_of_nonneg_left h8 hcpos.le
  · -- case A (`N` small)
    have hNle : (N : ℝ) ≤ C * δ⁻¹ ^ K := le_trans (not_lt.mp hBlarge) hCb_le_C
    exact lipL1Tail_caseA P A C K hA h2A2 hK1 ρ hρpos hρle N N₀ δ f g h hN hδpos hδle
      hN₀lo hN₀hi hfs hgs hhs hfb hgb hhb hcorr hNle

end Work.KMTAreas.A4
