/-
# `Work.FTS.PhiStar.FlatWAux.AngDeriv` — the differentiation identity for the resummed
angular profiles

This file proves the `FlatW_psiSeries`-route identity

`deriv (Wt ψ j) = Linv (chia ψ (j - 1))`   on `(0, π/2)`,  `1 ≤ j ≤ J`

recalled in `FlatWAux/Defs.lean`: `Wt ψ j = Σ_m b_m λ_m^{-j} Q_m` is the resummed angular
profile, `chia ψ j = sin 2θ · Wt ψ j` its `sin 2θ`-multiple, and `Linv` the zero-moment
Dirichlet inverse of `L₀`.

The proof has four steps, for fixed `1 ≤ j` and `θ ∈ (0, π/2)`:

1. termwise differentiation of the defining series (`WtDerivTsum`), using
   `deriv Q_m = Linv (λ_m e_m)` (`FamDerivDivLinv`):
   `deriv (Wt ψ j) θ = Σ_m b_m λ_m^{-j} · Linv (λ_m e_m) θ`;
2. the per-mode rewrite `λ^{-j} · Linv (λ e_m) = λ^{-(j-1)} · Linv (e_m)` (linearity of `Linv`;
   the `m = 0` term vanishes because `b_0 = 0` by the moment hypothesis, `bmode_zero`);
3. `Linv` only sees the values on `(0, θ]`, where `chia ψ (j-1)` is the series
   `Σ_m b_m λ_m^{-(j-1)} e_m` (`chia_eq_tsum`, resp. the expansion hypothesis for `j = 1`);
4. `Linv` is linear and commutes with the `m`-summation (`LinvTsumEFam`).

Steps 1 and 4 are the two analytic inputs (a `tsum`-termwise-differentiation and an
integral/`tsum` interchange); they are proved in the sibling files `WtDerivTsum.lean` and
`LinvTsumEFam.lean`, the per-mode moment/integrability in `MomentLamEFam.lean`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.FamDerivDivLinv
import Submission.Work.FTS.PhiStar.Series.SummableModes
import Submission.Work.FTS.PhiStar.LinvFlatAux.linv_abs_le_four
import Submission.Work.FTS.PhiStar.FlatWAux.MomentLamEFam
import Submission.Work.FTS.PhiStar.FlatWAux.WtDerivTsum
import Submission.Work.FTS.PhiStar.FlatWAux.LinvTsumEFam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option maxHeartbeats 800000

/-! ## Elementary facts about the eigenvalue `lam m` -/

lemma lam_nonneg (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  positivity

lemma lam_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  positivity

/-! ## `Linv` of a constant multiple, and congruence on `(0, θ]` -/

/-- `Linv` is linear in its argument: `Linv (k · F) θ = k · Linv F θ`. -/
lemma Linv_const_mul (k : ℝ) (F : ℝ → ℝ) (θ : ℝ) :
    Work.FTS.PhiStar.Linv (fun t : ℝ => k * F t) θ = k * Work.FTS.PhiStar.Linv F θ := by
  have hpt : ∀ t : ℝ,
      Real.sin t ^ 2 * Real.cos t ^ 3 * (k * F t) / Work.Construction.s2 t
        = k * (Real.sin t ^ 2 * Real.cos t ^ 3 * F t / Work.Construction.s2 t) :=
    fun t => by ring
  simp only [Work.FTS.PhiStar.Linv]
  rw [intervalIntegral.integral_congr (fun t _ => hpt t),
    intervalIntegral.integral_const_mul]
  ring

/-- `Linv F θ` depends only on the values of `F` on `(0, θ]`. -/
lemma Linv_congr_Ioc {F G : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (h : ∀ t ∈ Set.Ioc 0 θ, F t = G t) :
    Work.FTS.PhiStar.Linv F θ = Work.FTS.PhiStar.Linv G θ := by
  simp only [Work.FTS.PhiStar.Linv, neg_inj]
  congr 1
  rw [intervalIntegral.integral_of_le hθ.le, intervalIntegral.integral_of_le hθ.le]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => by rw [h t ht])

/-! ## `chia ψ (j-1)` as a series on `(0, θ]` -/

/-- On `(0, θ] ⊂ (0, π/2)` the `sin 2θ`-multiple `chia ψ (j-1)` is the resummed series
`Σ_m b_m λ_m^{-(j-1)} e_m`.  For `j = 1` this is the expansion hypothesis; for `j ≥ 2` it is
`chia_eq_tsum` together with `s2 · Q_m = e_m`. -/
lemma chia_eq_tsum_Ioc {ψ : ℝ → ℝ}
    (hexp : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ)
    {j : ℕ} (hj : 1 ≤ j) {θ t : ℝ} (ht : t ∈ Set.Ioc 0 θ) (hθ2 : θ < Real.pi / 2) :
    chia ψ (j - 1) t
      = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1)
          * Work.FTS.PhiStar.Gegenbauer.eFam m t := by
  have htIoo : t ∈ Set.Ioo 0 (Real.pi / 2) := ⟨ht.1, lt_of_le_of_lt ht.2 hθ2⟩
  have hs2 : Work.Construction.s2 t ≠ 0 := by
    rw [Work.Construction.s2_eq, Real.sin_two_mul]
    exact mul_ne_zero
      (mul_ne_zero two_ne_zero
        (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi htIoo.1
          (by linarith [Real.pi_pos, htIoo.2]))))
      (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, htIoo.1], htIoo.2⟩))
  rcases eq_or_lt_of_le hj with hj1 | hj2
  · subst hj1
    rw [Nat.sub_self, chia_zero hs2, ← hexp t htIoo]
    exact tsum_congr (fun m => by rw [pow_zero, mul_one])
  · rw [show j - 1 = (j - 2) + 1 by omega, chia_eq_tsum ψ (j - 2) htIoo]

/-! ## The per-mode rewrite replacing `λ_m^{-j} Linv (λ_m e_m)` by `λ_m^{-(j-1)} Linv e_m` -/

/-- Termwise: `b_m λ_m^{-j} Linv (λ_m e_m) = (b_m λ_m^{-(j-1)}) Linv (e_m)`.  The `m = 0` term
vanishes on both sides: `λ_0 = 0` kills the left-hand side and `b_0 = 0` (the moment condition)
the right-hand side. -/
lemma Wt_tsum_deriv_rewrite {ψ : ℝ → ℝ}
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0) {j : ℕ} (hj : 1 ≤ j) (θ : ℝ) :
    (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j
        * Work.FTS.PhiStar.Linv
            (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ)
      = ∑' m : ℕ, (Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1))
          * Work.FTS.PhiStar.Linv
              (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ := by
  refine tsum_congr (fun m => ?_)
  by_cases hm : m = 0
  · subst hm
    rw [hb0]
    ring
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hlam : Work.FTS.PhiStar.Gegenbauer.lam m ≠ 0 := ne_of_gt (lam_pos hm1)
    rw [Linv_const_mul]
    set L : ℝ := Work.FTS.PhiStar.Linv
      (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ with hL
    have hp : (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ^ j
          * Work.FTS.PhiStar.Gegenbauer.lam m
        = (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ^ (j - 1) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
      rw [show k + 1 - 1 = k by omega, pow_succ, mul_assoc, inv_mul_cancel₀ hlam, mul_one]
    calc Work.FTS.PhiStar.Series.bmode m ψ
            * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ^ j
            * (Work.FTS.PhiStar.Gegenbauer.lam m * L)
        = Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ^ j
              * Work.FTS.PhiStar.Gegenbauer.lam m) * L := by ring
      _ = Work.FTS.PhiStar.Series.bmode m ψ
            * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ^ (j - 1) * L := by rw [hp]

/-! ## The decay of the resummed coefficients -/

/-- `1/(λ_m √(2m+1)) ≤ (m+1)^{-5/2}` for `m ≥ 1`. -/
lemma one_div_lam_sqrt_le (m : ℕ) (hm : 1 ≤ m) :
    1 / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hpow : ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))
      = 1 / (((m : ℝ) + 1) ^ 2 * Real.sqrt ((m : ℝ) + 1)) := by
    have h5 : ((m : ℝ) + 1) ^ (5 / 2 : ℝ)
        = ((m : ℝ) + 1) ^ 2 * Real.sqrt ((m : ℝ) + 1) := by
      rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_two,
        ← Real.sqrt_eq_rpow]
    rw [Real.rpow_neg (le_of_lt hx) (5 / 2), h5, ← one_div]
  rw [hpow]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have h1 : ((m : ℝ) + 1) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by nlinarith
  have h2 : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have h3 : 4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
    simp only [Work.FTS.PhiStar.Gegenbauer.lam]
    nlinarith
  calc ((m : ℝ) + 1) ^ 2 * Real.sqrt ((m : ℝ) + 1)
      ≤ (4 * (m : ℝ) ^ 2) * Real.sqrt (2 * (m : ℝ) + 1) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ ≤ Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)

/-- The resummed coefficients `b_m λ_m^{-(j-1)}` decay like `(m+1)^{-5/2}`. -/
lemma bmode_mul_pow_decay {ψ : ℝ → ℝ} {Cb : ℝ} (hCb : 0 < Cb)
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cb / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (j : ℕ) (hj : 1 ≤ j) :
    ∀ m : ℕ, |Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1)|
      ≤ Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
  intro m
  by_cases hm : m = 0
  · subst hm
    rw [hb0, zero_mul, abs_zero,
      show (((0 : ℕ) : ℝ) + 1) ^ (-(5 / 2 : ℝ)) = 1 by
        rw [show (((0 : ℕ) : ℝ) + 1) = 1 by norm_num, Real.one_rpow],
      mul_one]
    exact hCb.le
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hlam1 : 1 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      simp only [Work.FTS.PhiStar.Gegenbauer.lam]
      nlinarith
    have hinvnn : 0 ≤ (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ :=
      inv_nonneg.mpr (by linarith)
    have hinv1 : (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by linarith)]; linarith
    have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos (by linarith) (Real.sqrt_pos.mpr (by positivity))
    have habs : |((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1)| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hinvnn _)]
      calc ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1) ≤ 1 ^ (j - 1) :=
            pow_le_pow_left₀ hinvnn hinv1 _
        _ = 1 := one_pow _
    rw [abs_mul]
    calc |Work.FTS.PhiStar.Series.bmode m ψ|
            * |((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1)|
        ≤ (Cb / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) * 1 :=
          mul_le_mul (hdec m hm1) habs (abs_nonneg _) (le_of_lt (div_pos hCb hden))
      _ = Cb * (1 / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
          ring
      _ ≤ Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (one_div_lam_sqrt_le m hm1) hCb.le

/-! ## The `Linv`-bound hypothesis for the termwise differentiation -/

/-- With `|e_m| ≤ Ce (2m+1)` and the vanishing moment of `λ_m e_m` (`MomentLamEFam`), the
zero-moment inverse is bounded by `4 Ce λ_m (2m+1)` uniformly on `(0, π/2)`
(`linv_abs_le_four`). -/
lemma exists_linv_lam_eFam_bound
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.Linv
        (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ') y|
        ≤ K * (Work.FTS.PhiStar.Gegenbauer.lam m * (2 * (m : ℝ) + 1)) := by
  obtain ⟨Ce, hCe, hgr⟩ := hgr
  refine ⟨4 * Ce, by positivity, fun m y hy => ?_⟩
  obtain ⟨hmom, hint⟩ := MomentLamEFam m
  have hlam : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := lam_nonneg m
  have hK : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m * (Ce * (2 * (m : ℝ) + 1)) :=
    mul_nonneg hlam (by positivity)
  have hbdd : ∀ t : ℝ, t ∈ Set.Ioo 0 (Real.pi / 2) →
      |(fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ') t|
        ≤ Work.FTS.PhiStar.Gegenbauer.lam m * (Ce * (2 * (m : ℝ) + 1)) := by
    intro t ht
    rw [abs_mul, abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_left
      (hgr m t ⟨le_of_lt ht.1, le_of_lt ht.2⟩) hlam
  have h := Work.FTS.PhiStar.LinvFlatAux.linv_abs_le_four hK hbdd hint hmom y hy
  calc |Work.FTS.PhiStar.Linv
        (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ') y|
      ≤ 4 * (Work.FTS.PhiStar.Gegenbauer.lam m * (Ce * (2 * (m : ℝ) + 1))) := h
    _ = (4 * Ce) * (Work.FTS.PhiStar.Gegenbauer.lam m * (2 * (m : ℝ) + 1)) := by ring

/-! ## The target -/

theorem AngDeriv (ψ : ℝ → ℝ) (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hQ : ∃ C : ℕ → ℝ, (∀ l : ℕ, 0 ≤ C l) ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ (l : ℕ), l ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |iteratedDeriv l (Work.FTS.PhiStar.FlatWAux.Qm m) θ|
          ≤ C l * (2 * (m : ℝ) + 1) ^ (2 * l + 2))
    (hcont : ContinuousOn ψ (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |ψ θ| ≤ M)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    (hexp : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ) :
    ∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      deriv (Work.FTS.PhiStar.FlatWAux.Wt ψ j) θ
        = Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ (j - 1)) θ := by
  obtain ⟨Cb, hCbpos, hdec'⟩ := hdec
  obtain ⟨Ce, hCepos, hgr'⟩ := hgr
  obtain ⟨CQ, hCQnn, hQ'⟩ := hQ
  have hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0 :=
    Work.FTS.PhiStar.Series.bmode_zero ψ hmom
  have hQ0 : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ θ : ℝ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.FlatWAux.Qm m θ| ≤ C * (2 * (m : ℝ) + 1) ^ 2 := by
    refine ⟨CQ 0 + 1, by linarith [hCQnn 0], fun m hm θ hθ => ?_⟩
    have h := hQ' m hm 0 (by norm_num) θ hθ
    rw [iteratedDeriv_zero,
      show (2 * (m : ℝ) + 1) ^ (2 * 0 + 2) = (2 * (m : ℝ) + 1) ^ 2 by norm_num] at h
    calc |Work.FTS.PhiStar.FlatWAux.Qm m θ| ≤ CQ 0 * (2 * (m : ℝ) + 1) ^ 2 := h
      _ ≤ (CQ 0 + 1) * (2 * (m : ℝ) + 1) ^ 2 := by
          have h0 : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 2 := sq_nonneg _
          nlinarith
  obtain ⟨K, hKpos, hK⟩ := exists_linv_lam_eFam_bound ⟨Ce, hCepos, hgr'⟩
  intro j hj hjJ θ hθ
  have hcoef : ∀ m : ℕ, |Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1)|
      ≤ Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) :=
    bmode_mul_pow_decay hCbpos hb0 hdec' j hj
  have hstep1 : deriv (Work.FTS.PhiStar.FlatWAux.Wt ψ j) θ
      = (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j
          * Work.FTS.PhiStar.Linv
              (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ) :=
    Work.FTS.PhiStar.FlatWAux.WtDerivTsum ψ j hj ⟨Cb, hCbpos, hdec'⟩
      ⟨Ce, hCepos, hgr'⟩ hQ0 ⟨K, hKpos, hK⟩ θ hθ
  have hstep2 : (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j
          * Work.FTS.PhiStar.Linv
              (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ)
      = (∑' m : ℕ, (Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1))
          * Work.FTS.PhiStar.Linv
              (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ) :=
    Wt_tsum_deriv_rewrite hb0 hj θ
  have hstep4 : Work.FTS.PhiStar.Linv
        (fun t : ℝ => ∑' m : ℕ, (Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1))
          * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
      = (∑' m : ℕ, (Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1))
          * Work.FTS.PhiStar.Linv
              (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ) :=
    Work.FTS.PhiStar.FlatWAux.LinvTsumEFam
      (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1))
      Cb Ce hCbpos.le hCepos.le (fun m θ' hθ' => hgr' m θ' hθ') hcoef θ hθ
  have hstep3 : Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ (j - 1)) θ
      = Work.FTS.PhiStar.Linv
          (fun t : ℝ => ∑' m : ℕ, (Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1))
            * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ :=
    Linv_congr_Ioc hθ.1 (fun t ht => chia_eq_tsum_Ioc hexp hj ht hθ.2)
  exact hstep1.trans (hstep2.trans (hstep4.symm.trans hstep3.symm))

end Work.FTS.PhiStar.FlatWAux
