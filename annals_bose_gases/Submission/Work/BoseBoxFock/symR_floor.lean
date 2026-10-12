import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.chiRow_bound
import Submission.Work.BoseBoxFock.sum_annOfE_normSq_le_nPlusC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.symR_floor` — the pointwise floor of the symbol discrepancy

The discrepancy identity `symR r − KzOpC (r²/ℓ³) = r²•D2F + r•D1F + D0F` (proved in
`Work.BoseBoxFock.symDiscrep`, and a hypothesis `hdisc` of the target) is turned into the
pointwise floor of the statement by bounding the three `r`-rows `D2F`, `D1F`, `D0F`
separately:

* `symR_row_D2F`: `⟪w, D2F w⟫ ≥ −4 cHCF ‖w‖²` — the `r²`-row; the only non-quantitative
  term is `(2ℓ⁻³Ŵ₁ω(0))•nOpC (f 0) ≥ 0`.
* `symR_row_D1F`: the `r¹`-row; its two `χ̂`- and `χ̂²`-rows are bounded by the
  Cauchy–Schwarz estimate `chiRowFinset_bound` against `⟪w, nPlusChi f w⟫ ≤ Kc‖w‖²` and
  (for the `χ̂²`-row, using the orthonormality `hgonb` of `g` on `excited Mode` and the
  Bessel inequality `sum_annOfE_normSq_le_nPlusC`) against `⟪w, n₊w⟫ ≤ K‖w‖²`.
* `symR_row_D0F`: the `r⁰`-row; the `(W₁+W₁ω)`-weighted number row is bounded by
  `Wsup·⟪w, nPlusChi f w⟫` and the linear `nPlusChi`-row by its `Kc`-bound.

`i3F E = ℓ⁻³ > 0` is used in every row (`hℓ`), and `Ŵ₁ω(0) ≥ 0` in the `r¹`-row (`hω0`).

## Note on `symR_floor_FALSE.md` (kept for the record; its verdict is withdrawn)

The earlier report `Submission/Work/BoseBoxFock/symR_floor_FALSE.md` argued that this lemma is
mis-stated.  Neither of its two arguments applies to the statement as it stands:

* its §1 (and `symR_floor_vacuity.lean`) analyses a **global** hypothesis
  `∀ w, ⟪w, n₊ w⟫ ≤ K‖w‖²`, which is unsatisfiable for `m ≥ 2`.  The statement's hypotheses
  `hKc`/`hK` are **per-`w`**: they sit after `∀ w : cfock (Excited m)` as arrows, so they only
  constrain the very vector `w` at which the inequality is asserted.  Nothing is vacuous, and
  `K`/`Kc` are the true per-state constants (as the proof below shows);
* its §2 counterexample (`g = c·δ_j`, `c → ∞`) is not a counterexample: it violates the
  hypothesis `hgonb`, which forces `gram (g s) (g s) = 1`, i.e. `‖g s‖ = 1` for every excited
  `s` — precisely the normalisation that makes the `χ̂²`(`g`)-row bound `2√(Σ(χ̂²)²)·√⟪w,n₊w⟫`
  (this file's `symR_row_D1F`) work.  Scaling `g` by `c` breaks `hgonb`.

The three row lemmas below are exactly the bound of `KAFZ_STATUS4.md` §1.3, and they reproduce
the statement's constant verbatim.
-/

namespace Work.BoseBoxFock

noncomputable section

open scoped BigOperators

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-! ## 0. Two elementary tools -/

/-- `i3F E = ℓ^{-3}` is positive for `ℓ > 0`. -/
lemma i3_pos {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Work.BoseB7.Q3Env Mode)
    (hℓ : 0 < E.ell) : 0 < i3F E := by
  rw [i3F, Real.rpow_neg (le_of_lt hℓ)]
  positivity

/-- The `χ̂`-row word is the sum of the superposition ladder words. -/
lemma BchiC_add_BchiA {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (s : Finset Mode) (χ : Mode → ℝ) (c : ℝ) (φ : Mode → Fin m → ℝ) :
    BchiC s χ c φ + BchiA s χ c φ
      = ∑ k ∈ s, ((c * χ k : ℝ) : ℂ) • (annOfE (φ k) + creOfE (φ k)) := by
  rw [BchiC, BchiA, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [← smul_add, add_comm]

/-- **Cauchy–Schwarz for a `Finset`-indexed `χ̂`-row**: the quadratic form of
`Σ_{k∈S} c_k (a(φ_k) + a(φ_k)†)` is bounded by
`2 √(Σ_{k∈S} c_k²) √(Σ_{k∈S} ‖a(φ_k) w‖²) ‖w‖`.

This is `Work.BoseBoxFock.chiRow_bound` with the `nPlusChi` reformulation of its second
factor replaced by the summed norms, so that the index set may be an arbitrary `Finset`
(no `AddCommGroup` on the index type). -/
lemma chiRowFinset_bound {X : Type*} [Fintype X] [DecidableEq X]
    (S : Finset X) (c : X → ℝ) (φ : X → Fin m → ℝ) (w : cfock (Excited m)) :
    |(inner ℂ w ((∑ k ∈ S, ((c k : ℝ) : ℂ) • (annOfE (φ k) + creOfE (φ k))) w)).re|
      ≤ 2 * Real.sqrt (∑ k ∈ S, c k ^ 2)
          * Real.sqrt (∑ k ∈ S, ‖annOfE (φ k) w‖ ^ 2) * ‖w‖ := by
  have hsub : (∑ k ∈ S, ((c k : ℝ) : ℂ) • (annOfE (φ k) + creOfE (φ k)))
      = (∑ k : {k : X // k ∈ S},
          ((c k.1 : ℝ) : ℂ) • (annOfE (φ k.1) + creOfE (φ k.1))) :=
    Finset.sum_subtype S (fun x => Iff.rfl) _
  have hcsq : (∑ k ∈ S, c k ^ 2) = ∑ k : {k : X // k ∈ S}, c k.1 ^ 2 :=
    Finset.sum_subtype S (fun x => Iff.rfl) _
  have hnsq : (∑ k ∈ S, ‖annOfE (φ k) w‖ ^ 2)
      = ∑ k : {k : X // k ∈ S}, ‖annOfE (φ k.1) w‖ ^ 2 :=
    Finset.sum_subtype S (fun x => Iff.rfl) _
  rw [hsub, hcsq, hnsq]
  have hre := chiRow_re_T (fun k : {k : X // k ∈ S} => c k.1)
    (fun k : {k : X // k ∈ S} => φ k.1) w
  have hnorm : |(inner ℂ w ((∑ k : {k : X // k ∈ S},
        ((c k.1 : ℝ) : ℂ) • annOfE (φ k.1)) w)).re|
      ≤ ‖w‖ * (Real.sqrt (∑ k : {k : X // k ∈ S}, c k.1 ^ 2)
          * Real.sqrt (∑ k : {k : X // k ∈ S}, ‖annOfE (φ k.1) w‖ ^ 2)) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_inner_le_norm w _).trans ?_
    exact mul_le_mul_of_nonneg_left
      (chiRow_ann_norm_le (fun k : {k : X // k ∈ S} => c k.1)
        (fun k : {k : X // k ∈ S} => φ k.1) w) (norm_nonneg w)
  calc |(inner ℂ w ((∑ k : {k : X // k ∈ S},
          ((c k.1 : ℝ) : ℂ) • (annOfE (φ k.1) + creOfE (φ k.1))) w)).re|
      = |2 * (inner ℂ w ((∑ k : {k : X // k ∈ S},
            ((c k.1 : ℝ) : ℂ) • annOfE (φ k.1)) w)).re| := by rw [hre]
    _ = 2 * |(inner ℂ w ((∑ k : {k : X // k ∈ S},
            ((c k.1 : ℝ) : ℂ) • annOfE (φ k.1)) w)).re| := by
          rw [abs_mul]; norm_num
    _ ≤ 2 * (‖w‖ * (Real.sqrt (∑ k : {k : X // k ∈ S}, c k.1 ^ 2)
          * Real.sqrt (∑ k : {k : X // k ∈ S}, ‖annOfE (φ k.1) w‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hnorm (by norm_num)
    _ = 2 * Real.sqrt (∑ k : {k : X // k ∈ S}, c k.1 ^ 2)
          * Real.sqrt (∑ k : {k : X // k ∈ S}, ‖annOfE (φ k.1) w‖ ^ 2) * ‖w‖ := by ring

/-! ## 1. The `r²`-row `D2F` -/

/-- The `r²`-row of the discrepancy is bounded below by `−4 cHCF ‖w‖²`: its only
non-quantitative part is the positive number row `(2ℓ⁻³Ŵ₁ω(0))•nOpC (f 0) ≥ 0`. -/
lemma symR_row_D2F {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (hℓ : 0 < E.ell)
    (hω0 : 0 ≤ E.W1omega0) (w : cfock (Excited m)) :
    (inner ℂ w (D2F f E gHat0 w)).re ≥ -(4 * cHCF E gHat0) * ‖w‖ ^ 2 := by
  have h1 : inner ℂ w ((1 : cfock (Excited m) →ₗ[ℂ] _) w) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [show (1 : cfock (Excited m) →ₗ[ℂ] _) w = w from rfl]
    exact kfb_inner_self_re w
  have h2 : inner ℂ w (nOpC (f 0) w) = ((‖annOfE (f 0) w‖ ^ 2 : ℝ) : ℂ) :=
    chiRow_inner_nOpC (f 0) w
  rw [D2F]
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [kfb_inner_addR, kfb_inner_smulR, kfb_inner_smulR, h1, h2]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  have hB : 0 ≤ 2 * i3F E * E.W1omega0 :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (i3_pos E hℓ))) hω0
  nlinarith [sq_nonneg ‖annOfE (f 0) w‖, mul_nonneg hB (sq_nonneg ‖annOfE (f 0) w‖)]

/-! ## 2. The `r¹`-row `D1F` -/

/-- The `r¹`-row of the discrepancy: the `χ̂`(`f`)-row is controlled by `hKc`
(`nPlusChi f ≤ Kc‖w‖²`, `Σ_k χ̂_k² ≤ 1`) and the `χ̂²`(`g`)-row by the orthonormality of
`g` on the excited modes together with `hK` (`n₊ ≤ K‖w‖²`, `Σ_{k∈exc} (χ̂²_k)² ≤ 1`). -/
lemma symR_row_D1F {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode)
    (hℓ : 0 < E.ell) (hω0 : 0 ≤ E.W1omega0)
    (hgonb : ∀ s ∈ Work.BoseB7.excited Mode, ∀ t ∈ Work.BoseB7.excited Mode,
      Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0)
    (K Kc : ℝ) (hK0 : 0 ≤ K) (hKc0 : 0 ≤ Kc)
    (hχ2 : (∑ k : Mode, E.hatChi k ^ 2) ≤ 1)
    (hχ2b : (∑ k ∈ Work.BoseB7.excited Mode, E.hatChiSq k ^ 2) ≤ 1)
    (w : cfock (Excited m))
    (hKc : (inner ℂ w (nPlusChi f w)).re ≤ Kc * ‖w‖ ^ 2)
    (hK : (inner ℂ w (nPlusC (m := m) w)).re ≤ K * ‖w‖ ^ 2) :
    (inner ℂ w (D1F f g E w)).re
      ≥ -(4 * i3F E * (|E.W1 0| * Real.sqrt Kc + E.W1omega0 * Real.sqrt K)) * ‖w‖ ^ 2 := by
  have hi3 : 0 < i3F E := i3_pos E hℓ
  set Pf : ℝ := (inner ℂ w ((BchiC (Finset.univ : Finset Mode) E.hatChi 1 f
      + BchiA (Finset.univ : Finset Mode) E.hatChi 1 f) w)).re with hPf
  set Pg : ℝ := (inner ℂ w ((BchiC (Work.BoseB7.excited Mode) E.hatChiSq 1 g
      + BchiA (Work.BoseB7.excited Mode) E.hatChiSq 1 g) w)).re with hPg
  have hsplit : (inner ℂ w (D1F f g E w)).re
      = (-(2 * i3F E * E.W1 0)) * Pf + (-(2 * i3F E * E.W1omega0)) * Pg := by
    rw [D1F, hPf, hPg]
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    simp only [kfb_inner_addR, kfb_inner_smulR, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hPf_abs : |Pf| ≤ 2 * Real.sqrt Kc * ‖w‖ ^ 2 := by
    have hb := chiRowFinset_bound (Finset.univ : Finset Mode) E.hatChi f w
    have hword : (∑ k ∈ (Finset.univ : Finset Mode), ((E.hatChi k : ℝ) : ℂ) •
          (annOfE (f k) + creOfE (f k)))
        = BchiC (Finset.univ : Finset Mode) E.hatChi 1 f
          + BchiA (Finset.univ : Finset Mode) E.hatChi 1 f := by
      rw [BchiC_add_BchiA]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_mul]
    rw [hword] at hb
    have hnsq : (∑ k ∈ (Finset.univ : Finset Mode), ‖annOfE (f k) w‖ ^ 2)
        = (inner ℂ w (nPlusChi f w)).re := by
      rw [chiRow_nPlusChi_re]
    have hs2 : Real.sqrt (∑ k ∈ (Finset.univ : Finset Mode), ‖annOfE (f k) w‖ ^ 2)
        ≤ Real.sqrt Kc * ‖w‖ := by
      rw [hnsq, ← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_mul hKc0]
      exact Real.sqrt_le_sqrt hKc
    have hs1 : Real.sqrt (∑ k ∈ (Finset.univ : Finset Mode), E.hatChi k ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      simpa using hχ2
    calc |Pf| ≤ 2 * Real.sqrt (∑ k ∈ (Finset.univ : Finset Mode), E.hatChi k ^ 2)
          * Real.sqrt (∑ k ∈ (Finset.univ : Finset Mode), ‖annOfE (f k) w‖ ^ 2) * ‖w‖ := hb
      _ ≤ 2 * 1 * (Real.sqrt Kc * ‖w‖) * ‖w‖ := by gcongr
      _ = 2 * Real.sqrt Kc * ‖w‖ ^ 2 := by ring
  have hPg_abs : |Pg| ≤ 2 * Real.sqrt K * ‖w‖ ^ 2 := by
    have hb := chiRowFinset_bound (Work.BoseB7.excited Mode) E.hatChiSq g w
    have hword : (∑ k ∈ Work.BoseB7.excited Mode, ((E.hatChiSq k : ℝ) : ℂ) •
          (annOfE (g k) + creOfE (g k)))
        = BchiC (Work.BoseB7.excited Mode) E.hatChiSq 1 g
          + BchiA (Work.BoseB7.excited Mode) E.hatChiSq 1 g := by
      rw [BchiC_add_BchiA]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_mul]
    rw [hword] at hb
    have hnsq : (∑ k ∈ Work.BoseB7.excited Mode, ‖annOfE (g k) w‖ ^ 2)
        ≤ (inner ℂ w (nPlusC (m := m) w)).re :=
      sum_annOfE_normSq_le_nPlusC (Work.BoseB7.excited Mode) g hgonb w
    have hs2 : Real.sqrt (∑ k ∈ Work.BoseB7.excited Mode, ‖annOfE (g k) w‖ ^ 2)
        ≤ Real.sqrt K * ‖w‖ := by
      rw [← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_mul hK0]
      exact Real.sqrt_le_sqrt (le_trans hnsq hK)
    have hs1 : Real.sqrt (∑ k ∈ Work.BoseB7.excited Mode, E.hatChiSq k ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact hχ2b
    calc |Pg| ≤ 2 * Real.sqrt (∑ k ∈ Work.BoseB7.excited Mode, E.hatChiSq k ^ 2)
          * Real.sqrt (∑ k ∈ Work.BoseB7.excited Mode, ‖annOfE (g k) w‖ ^ 2) * ‖w‖ := hb
      _ ≤ 2 * 1 * (Real.sqrt K * ‖w‖) * ‖w‖ := by gcongr
      _ = 2 * Real.sqrt K * ‖w‖ ^ 2 := by ring
  rw [hsplit]
  have h1 : (-(2 * i3F E * E.W1 0)) * Pf
      ≥ -(4 * i3F E * |E.W1 0| * Real.sqrt Kc) * ‖w‖ ^ 2 := by
    have hc : |(-(2 * i3F E * E.W1 0))| = 2 * i3F E * |E.W1 0| := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_pos hi3, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have hlow : (-(2 * i3F E * E.W1 0)) * Pf ≥ -|(-(2 * i3F E * E.W1 0))| * |Pf| := by
      have h := neg_abs_le ((-(2 * i3F E * E.W1 0)) * Pf)
      rw [abs_mul] at h
      linarith
    have hup : -|(-(2 * i3F E * E.W1 0))| * |Pf|
        ≥ -|(-(2 * i3F E * E.W1 0))| * (2 * Real.sqrt Kc * ‖w‖ ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hPf_abs (abs_nonneg ((-(2 * i3F E * E.W1 0))))
      nlinarith [h]
    rw [hc] at hlow hup
    nlinarith [hlow, hup]
  have h2 : (-(2 * i3F E * E.W1omega0)) * Pg
      ≥ -(4 * i3F E * E.W1omega0 * Real.sqrt K) * ‖w‖ ^ 2 := by
    have hc : |(-(2 * i3F E * E.W1omega0))| = 2 * i3F E * E.W1omega0 := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_pos hi3, abs_of_pos (by norm_num : (0:ℝ) < 2),
        abs_of_nonneg hω0]
    have hlow : (-(2 * i3F E * E.W1omega0)) * Pg ≥ -|(-(2 * i3F E * E.W1omega0))| * |Pg| := by
      have h := neg_abs_le ((-(2 * i3F E * E.W1omega0)) * Pg)
      rw [abs_mul] at h
      linarith
    have hup : -|(-(2 * i3F E * E.W1omega0))| * |Pg|
        ≥ -|(-(2 * i3F E * E.W1omega0))| * (2 * Real.sqrt K * ‖w‖ ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hPg_abs (abs_nonneg ((-(2 * i3F E * E.W1omega0))))
      nlinarith [h]
    rw [hc] at hlow hup
    nlinarith [hlow, hup]
  have haux : (-(2 * i3F E * E.W1 0)) * Pf + (-(2 * i3F E * E.W1omega0)) * Pg
      ≥ -(4 * i3F E * |E.W1 0| * Real.sqrt Kc) * ‖w‖ ^ 2
        + -(4 * i3F E * E.W1omega0 * Real.sqrt K) * ‖w‖ ^ 2 := add_le_add h1 h2
  have heq : -(4 * i3F E * (|E.W1 0| * Real.sqrt Kc + E.W1omega0 * Real.sqrt K)) * ‖w‖ ^ 2
      = -(4 * i3F E * |E.W1 0| * Real.sqrt Kc) * ‖w‖ ^ 2
        + -(4 * i3F E * E.W1omega0 * Real.sqrt K) * ‖w‖ ^ 2 := by ring
  rw [heq]
  linarith [haux]

/-! ## 3. The `r⁰`-row `D0F` -/

/-- The `r⁰`-row of the discrepancy: the `c`-number row is bounded by its absolute value,
the `(W₁+W₁ω)`-weighted number row by `Wsup·⟪w, nPlusChi f w⟫ ≤ Wsup Kc‖w‖²`, and the
linear `nPlusChi f`-row by `|Ŵ₁(0)+Ŵ₁ω(0)|·Kc‖w‖²`. -/
lemma symR_row_D0F {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 Kc Wsup : ℝ)
    (hℓ : 0 < E.ell)
    (hWsup : ∀ k : Mode, |E.W1 k + E.W1omega k| ≤ Wsup)
    (w : cfock (Excited m))
    (hKc : (inner ℂ w (nPlusChi f w)).re ≤ Kc * ‖w‖ ^ 2) :
    (inner ℂ w (D0F f E gHat0 w)).re
      ≥ -(|2 * cHCF E gHat0 + E.mu * gHat0|
            + i3F E * (Wsup + |E.W1 0 + E.W1omega0|) * Kc) * ‖w‖ ^ 2 := by
  set N : ℝ := (inner ℂ w (nPlusChi f w)).re with hNdef
  set Q : ℝ := (inner ℂ w (BW (Finset.univ : Finset Mode)
      (fun k => E.W1 k + E.W1omega k) f w)).re with hQdef
  have hN0 : 0 ≤ N := by
    rw [hNdef, chiRow_nPlusChi_re]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hW0 : 0 ≤ Wsup := le_trans (abs_nonneg _) (hWsup 0)
  have hi3 : 0 < i3F E := i3_pos E hℓ
  have hBWform : Q = ∑ k : Mode, (E.W1 k + E.W1omega k) * ‖annOfE (f k) w‖ ^ 2 := by
    rw [hQdef, BW, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [kfb_inner_sumR, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [kfb_inner_smulR, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    rw [show nmF f k w = nOpC (f k) w from rfl, chiRow_nOpC_re]
  have hBWle : Q ≤ Wsup * N := by
    rw [hBWform, hNdef, chiRow_nPlusChi_re, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc (E.W1 k + E.W1omega k) * ‖annOfE (f k) w‖ ^ 2
        ≤ |E.W1 k + E.W1omega k| * ‖annOfE (f k) w‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ ≤ Wsup * ‖annOfE (f k) w‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hWsup k) (sq_nonneg _)
  have hsplit : (inner ℂ w (D0F f E gHat0 w)).re
      = (2 * cHCF E gHat0 + E.mu * gHat0) * ‖w‖ ^ 2 + (-i3F E) * Q
        + (-(i3F E * (E.W1 0 + E.W1omega0))) * N := by
    rw [D0F, hQdef, hNdef]
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    rw [kfb_inner_addR, kfb_inner_addR, kfb_inner_smulR, kfb_inner_smulR, kfb_inner_smulR]
    rw [show (1 : cfock (Excited m) →ₗ[ℂ] _) w = w from rfl, kfb_inner_self_re]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  rw [hsplit]
  have hNle : N ≤ Kc * ‖w‖ ^ 2 := hKc
  have h1 : (-i3F E) * Q ≥ -(i3F E * Wsup * Kc) * ‖w‖ ^ 2 := by
    have hle : Q ≤ Wsup * (Kc * ‖w‖ ^ 2) := le_trans hBWle (mul_le_mul_of_nonneg_left hNle hW0)
    nlinarith [mul_le_mul_of_nonneg_left hle (le_of_lt hi3)]
  have h2 : (-(i3F E * (E.W1 0 + E.W1omega0))) * N
      ≥ -(i3F E * |E.W1 0 + E.W1omega0| * Kc) * ‖w‖ ^ 2 := by
    have hc : |(-(i3F E * (E.W1 0 + E.W1omega0)))| = i3F E * |E.W1 0 + E.W1omega0| := by
      rw [abs_neg, abs_mul, abs_of_pos hi3]
    have hlow : (-(i3F E * (E.W1 0 + E.W1omega0))) * N
        ≥ -|(-(i3F E * (E.W1 0 + E.W1omega0)))| * N := by
      nlinarith [mul_le_mul_of_nonneg_right
        (neg_abs_le (-(i3F E * (E.W1 0 + E.W1omega0)))) hN0]
    have hup : -|(-(i3F E * (E.W1 0 + E.W1omega0)))| * N
        ≥ -|(-(i3F E * (E.W1 0 + E.W1omega0)))| * (Kc * ‖w‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hNle
        (abs_nonneg (-(i3F E * (E.W1 0 + E.W1omega0))))]
    rw [hc] at hlow hup
    nlinarith [hlow, hup]
  have h3 : (2 * cHCF E gHat0 + E.mu * gHat0) * ‖w‖ ^ 2
      ≥ -|2 * cHCF E gHat0 + E.mu * gHat0| * ‖w‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right (neg_le_abs (2 * cHCF E gHat0 + E.mu * gHat0))
      (sq_nonneg ‖w‖)]
  have haux : (2 * cHCF E gHat0 + E.mu * gHat0) * ‖w‖ ^ 2 + (-i3F E) * Q
        + (-(i3F E * (E.W1 0 + E.W1omega0))) * N
      ≥ -|2 * cHCF E gHat0 + E.mu * gHat0| * ‖w‖ ^ 2 + -(i3F E * Wsup * Kc) * ‖w‖ ^ 2
        + -(i3F E * |E.W1 0 + E.W1omega0| * Kc) * ‖w‖ ^ 2 :=
    add_le_add (add_le_add h3 h1) h2
  have heq : -(|2 * cHCF E gHat0 + E.mu * gHat0|
        + i3F E * (Wsup + |E.W1 0 + E.W1omega0|) * Kc) * ‖w‖ ^ 2
      = -|2 * cHCF E gHat0 + E.mu * gHat0| * ‖w‖ ^ 2 + -(i3F E * Wsup * Kc) * ‖w‖ ^ 2
        + -(i3F E * |E.W1 0 + E.W1omega0| * Kc) * ‖w‖ ^ 2 := by ring
  rw [heq]
  linarith [haux]

/-! ## 4. The assembly -/

theorem symR_floor {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (f g : Mode → Fin m → ℝ)
    (BNH : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (PHs : Finset Mode) (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (gHat0 : ℝ) (hℓ : 0 < E.ell) (hPH : PHs = F.PHset E)
    (hcH : 0 ≤ Work.BoseBoxFock.cHCF E gHat0) (hω0 : 0 ≤ E.W1omega0)
    (hφ : ∀ k : Mode, f k 0 = 0)
    (hgonb : ∀ s ∈ Work.BoseB7.excited Mode, ∀ t ∈ Work.BoseB7.excited Mode,
      Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0)
    (hdisc : ∀ r : ℝ, 0 ≤ r →
      Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
          - Work.BoseBoxFock.KzOpC f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)
        = ((r ^ 2 : ℝ) : ℂ) • Work.BoseBoxFock.D2F f E gHat0
          + ((r : ℝ) : ℂ) • Work.BoseBoxFock.D1F f g E
          + Work.BoseBoxFock.D0F f E gHat0)
    (K Kc Wsup : ℝ) (hK0 : 0 ≤ K) (hKc0 : 0 ≤ Kc)
    (hWsup : ∀ k : Mode, |E.W1 k + E.W1omega k| ≤ Wsup)
    (hχ2 : (∑ k : Mode, E.hatChi k ^ 2) ≤ 1)
    (hχ2b : (∑ k ∈ Work.BoseB7.excited Mode, E.hatChiSq k ^ 2) ≤ 1) :
    ∀ r : ℝ, 0 ≤ r → ∀ w : Work.BoseB4.cfock (Work.BoseB4.Excited m),
      (inner ℂ w (Work.BoseBoxFock.nPlusChi f w)).re ≤ Kc * ‖w‖ ^ 2 →
      (inner ℂ w (Work.BoseBoxFock.nPlusC (m := m) w)).re ≤ K * ‖w‖ ^ 2 →
      (inner ℂ w ((Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
          - Work.BoseBoxFock.KzOpC f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)) w)).re
        ≥ -(((4 * Work.BoseBoxFock.cHCF E gHat0) * r ^ 2
              + (4 * (Work.BoseBoxFock.i3F E)
                  * (|E.W1 0| * Real.sqrt Kc + E.W1omega0 * Real.sqrt K)) * r
              + (|2 * Work.BoseBoxFock.cHCF E gHat0 + E.mu * gHat0|
                  + (Work.BoseBoxFock.i3F E) * (Wsup + |E.W1 0 + E.W1omega0|) * Kc)))
          * ‖w‖ ^ 2 := by
  intro r hr w hKc hK
  have h2 := symR_row_D2F f E gHat0 hℓ hω0 w
  have h1 := symR_row_D1F f g E hℓ hω0 hgonb K Kc hK0 hKc0 hχ2 hχ2b w hKc hK
  have h0 := symR_row_D0F f E gHat0 Kc Wsup hℓ hWsup w hKc
  have hL : (inner ℂ w ((Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
        - Work.BoseBoxFock.KzOpC f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)) w)).re
      = r ^ 2 * (inner ℂ w (Work.BoseBoxFock.D2F f E gHat0 w)).re
        + r * (inner ℂ w (Work.BoseBoxFock.D1F f g E w)).re
        + (inner ℂ w (Work.BoseBoxFock.D0F f E gHat0 w)).re := by
    rw [hdisc r hr]
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    simp only [kfb_inner_addR, kfb_inner_smulR, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hL]
  have hA : r ^ 2 * (-(4 * Work.BoseBoxFock.cHCF E gHat0) * ‖w‖ ^ 2)
      ≤ r ^ 2 * (inner ℂ w (Work.BoseBoxFock.D2F f E gHat0 w)).re :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg r)
  have hB : r * (-(4 * (Work.BoseBoxFock.i3F E)
        * (|E.W1 0| * Real.sqrt Kc + E.W1omega0 * Real.sqrt K)) * ‖w‖ ^ 2)
      ≤ r * (inner ℂ w (Work.BoseBoxFock.D1F f g E w)).re :=
    mul_le_mul_of_nonneg_left h1 hr
  have hC : -(|2 * Work.BoseBoxFock.cHCF E gHat0 + E.mu * gHat0|
        + (Work.BoseBoxFock.i3F E) * (Wsup + |E.W1 0 + E.W1omega0|) * Kc) * ‖w‖ ^ 2
      ≤ (inner ℂ w (Work.BoseBoxFock.D0F f E gHat0 w)).re := h0
  have hring : -(((4 * Work.BoseBoxFock.cHCF E gHat0) * r ^ 2
        + (4 * (Work.BoseBoxFock.i3F E)
            * (|E.W1 0| * Real.sqrt Kc + E.W1omega0 * Real.sqrt K)) * r
        + (|2 * Work.BoseBoxFock.cHCF E gHat0 + E.mu * gHat0|
            + (Work.BoseBoxFock.i3F E) * (Wsup + |E.W1 0 + E.W1omega0|) * Kc)))
        * ‖w‖ ^ 2
      = r ^ 2 * (-(4 * Work.BoseBoxFock.cHCF E gHat0) * ‖w‖ ^ 2)
        + r * (-(4 * (Work.BoseBoxFock.i3F E)
            * (|E.W1 0| * Real.sqrt Kc + E.W1omega0 * Real.sqrt K)) * ‖w‖ ^ 2)
        + (-(|2 * Work.BoseBoxFock.cHCF E gHat0 + E.mu * gHat0|
            + (Work.BoseBoxFock.i3F E) * (Wsup + |E.W1 0 + E.W1omega0|) * Kc) * ‖w‖ ^ 2) := by
    ring
  rw [hring]
  linarith [hA, hB, hC]

end

end Work.BoseBoxFock
