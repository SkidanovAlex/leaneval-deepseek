import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB2.DvApriori.dvap_numerator_bound
import Submission.Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge
import Submission.Work.BoseFixB2.DvApriori.exists_window_factor_le
import Submission.Work.BoseFixB2.DvApriori.kinFormB_secProj_offdiag
import Submission.Work.BoseFixB2.DvApriori.polPot_eq_integral
import Submission.Work.BoseFixB2.DvApriori.potBand_secProj_v4
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.dOne_dTwo_le` — FS §6 `eq:dvapriori`

`Work.BoseFixB2.DvApriori.dOne_dTwo_le`: for a *low* box state `Φ` of the box of side
`ℓ = sideAt μ (a v)` whose particle number satisfies the a priori window
`|n − μℓ³| ≤ C₁·nWindow` (`NodeB1B`'s first conjunct, carried as the hypothesis `hwin`),
the first two off-diagonals of the `n₊`-grading matrix are bounded by `K μ²ℓ³`.

The proof is FS §6's chain:

* `dOne`/`dTwo` are `2·(Σᵢ polB(1_{n₊=i}Φ, 1_{n₊=i+k}Φ))/‖Φ‖²` for `k = 1,2`;
* `polB` splits into the kinetic and potential polarisations (`polB_eq_polKin_add_polPot`);
* the kinetic part of the grading is **diagonal** (`kinFormB_secProj_offdiag`), so the whole
  off-diagonal comes from the potential (`band_one`, `band_two`):
  `Σᵢ polPot(1ᵢ,1ᵢ₊₁) = ½(q1word + q3word)` and `Σᵢ polPot(1ᵢ,1ᵢ₊₂) = ½·T₄`;
* the corpus's FS §5 potential estimates `qcross_w_d11`/`qcross_w_d13_quarter`/
  `qcross_w_d2_quarter` bound `q1word`/`q3word`/`T₄`, with the one-body kernel comparison
  `q1word_onebody_diff_bound` and the a priori `Q₄` bound `q4word_le_of_low`; the assembly is
  `dvap_numerator_bound`;
* the window gives `n ≤ 2μℓ³` (`exists_window_factor_le`), and `Adm` with `ε₀` small enough
  gives the FS potential regime `R ≤ ℓ chiR0` (`exists_adm_chiR0_ge`).
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix Work.UBB Work.UBBInputs3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-- The common step of the two band identities: the sum of `polB` over a range splits into the
sums of `polKin` and `polPot`. -/
theorem sum_polB_split {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {n m : ℕ} {d : ℕ} {Φ : Submission.BoseGases.X n → ℝ} :
    (∑ i ∈ Finset.range m, Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj (fsSide v μ) i Φ)
        (Work.BoseFixB2.secProj (fsSide v μ) (i+d) Φ))
      = (∑ i ∈ Finset.range m, polKin v h μ n (Work.BoseFixB2.secProj (fsSide v μ) i Φ)
          (Work.BoseFixB2.secProj (fsSide v μ) (i+d) Φ))
        + (∑ i ∈ Finset.range m, polPot v h μ n (Work.BoseFixB2.secProj (fsSide v μ) i Φ)
          (Work.BoseFixB2.secProj (fsSide v μ) (i+d) Φ)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact polB_eq_polKin_add_polPot (v := v) (h := h) (μ := μ) (n := n)
    (Φ := Work.BoseFixB2.secProj (fsSide v μ) i Φ)
    (Ψ := Work.BoseFixB2.secProj (fsSide v μ) (i+d) Φ)

/-- **The band-1 identity** for the box word (FS §6, the displayed `d₁`). -/
theorem band_one {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
    {R : ℝ} (hR : 0 < R) (hv1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦs : Submission.BoseGases.PermInvariant n Φ) (hvrad : _root_.BoseGases.IsRadial v)
    (hℓ : 0 < fsSide v μ) (hRℓ : R ≤ fsSide v μ * Submission.BoseGases.chiR0) :
    (∑ i ∈ Finset.range n, Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj (fsSide v μ) i Φ)
        (Work.BoseFixB2.secProj (fsSide v μ) (i+1) Φ))
      = (1/2) * (Submission.BoseGases.q1word (N := n) (fsSide v μ) μ
            (Submission.BoseGases.wPairC (fsSide v μ) (Submission.BoseGases.g0 v h))
            (Submission.BoseGases.wPairC (fsSide v μ) v) Φ
          + Submission.BoseGases.q3word (N := n) (fsSide v μ)
            (Submission.BoseGases.wPairC (fsSide v μ) v) Φ) := by
  have hsm : ∀ k : ℕ, ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.secProj (fsSide v μ) k Φ) :=
    fun k => (Work.BoseFixB2.Sector.secProj_contDiff_symm hℓ hΦ hΦs).1
  have hkin : (∑ i ∈ Finset.range n, polKin v h μ n (Work.BoseFixB2.secProj (fsSide v μ) i Φ)
      (Work.BoseFixB2.secProj (fsSide v μ) (i+1) Φ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    unfold polKin kinPart
    have hik : i ≠ i + 1 := by omega
    show (Work.BoseKinLoc.kinFormB n (fsSide v μ) (paramsAt μ (_root_.BoseGases.a v)).d
            (paramsAt μ (_root_.BoseGases.a v)).s (paramsAt μ (_root_.BoseGases.a v)).eT
            (paramsAt μ (_root_.BoseGases.a v)).b
              (Work.BoseFixB2.secProj (fsSide v μ) i Φ + Work.BoseFixB2.secProj (fsSide v μ) (i+1) Φ)
          - Work.BoseKinLoc.kinFormB n (fsSide v μ) (paramsAt μ (_root_.BoseGases.a v)).d
            (paramsAt μ (_root_.BoseGases.a v)).s (paramsAt μ (_root_.BoseGases.a v)).eT
            (paramsAt μ (_root_.BoseGases.a v)).b
              (Work.BoseFixB2.secProj (fsSide v μ) i Φ - Work.BoseFixB2.secProj (fsSide v μ) (i+1) Φ)) / 4 = 0
    exact kinFormB_secProj_offdiag (ℓ := fsSide v μ) hℓ (Φ := Φ) hΦ (i := i) (k := i+1) hik
  have hpot : (∑ i ∈ Finset.range n, polPot v h μ n (Work.BoseFixB2.secProj (fsSide v μ) i Φ)
      (Work.BoseFixB2.secProj (fsSide v μ) (i+1) Φ))
      = ∑ i ∈ Finset.range n, ∫ x in Submission.BoseGases.abox n (fsSide v μ),
          Work.BoseFixB2.secProj (fsSide v μ) i Φ x * Work.BoseFixB2.secProj (fsSide v μ) (i+1) Φ x
            * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) (fsSide v μ) μ 0 x := by
    apply Finset.sum_congr rfl
    intro i hi
    exact polPot_eq_integral (v := v) (h := h) (μ := μ) (n := n) (R := R) hR hv_supp hv1 hRℓ
      (hsm i) (hsm (i+1))
  rw [sum_polB_split (m := n) (d := 1), hkin, hpot, zero_add]
  exact (potBand_secProj_v4 (v := v) (h := h) (μ := μ) (n := n) (ℓ := fsSide v μ) hℓ hvrad hR hv_supp hv1 hRℓ hΦ).1

/-- **The band-2 identity** for the box word (FS §6, the displayed `d₂`). -/
theorem band_two {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
    {R : ℝ} (hR : 0 < R) (hv1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦs : Submission.BoseGases.PermInvariant n Φ) (hvrad : _root_.BoseGases.IsRadial v)
    (hℓ : 0 < fsSide v μ) (hRℓ : R ≤ fsSide v μ * Submission.BoseGases.chiR0) :
    (∑ i ∈ Finset.range (n-1), Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj (fsSide v μ) i Φ)
        (Work.BoseFixB2.secProj (fsSide v μ) (i+2) Φ))
      = (1/2) * (∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x in Submission.BoseGases.abox n (fsSide v μ),
          Submission.BoseGases.aP (fsSide v μ) p.1 (Submission.BoseGases.aP (fsSide v μ) p.2 Φ) x
            * Submission.BoseGases.aQ (fsSide v μ) p.2 (Submission.BoseGases.aQ (fsSide v μ) p.1 Φ) x
            * Submission.BoseGases.wPairC (fsSide v μ) v (x p.1) (x p.2)) := by
  have hsm : ∀ k : ℕ, ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.secProj (fsSide v μ) k Φ) :=
    fun k => (Work.BoseFixB2.Sector.secProj_contDiff_symm hℓ hΦ hΦs).1
  have hkin : (∑ i ∈ Finset.range (n-1), polKin v h μ n (Work.BoseFixB2.secProj (fsSide v μ) i Φ)
      (Work.BoseFixB2.secProj (fsSide v μ) (i+2) Φ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    unfold polKin kinPart
    have hik : i ≠ i + 2 := by omega
    show (Work.BoseKinLoc.kinFormB n (fsSide v μ) (paramsAt μ (_root_.BoseGases.a v)).d
            (paramsAt μ (_root_.BoseGases.a v)).s (paramsAt μ (_root_.BoseGases.a v)).eT
            (paramsAt μ (_root_.BoseGases.a v)).b
              (Work.BoseFixB2.secProj (fsSide v μ) i Φ + Work.BoseFixB2.secProj (fsSide v μ) (i+2) Φ)
          - Work.BoseKinLoc.kinFormB n (fsSide v μ) (paramsAt μ (_root_.BoseGases.a v)).d
            (paramsAt μ (_root_.BoseGases.a v)).s (paramsAt μ (_root_.BoseGases.a v)).eT
            (paramsAt μ (_root_.BoseGases.a v)).b
              (Work.BoseFixB2.secProj (fsSide v μ) i Φ - Work.BoseFixB2.secProj (fsSide v μ) (i+2) Φ)) / 4 = 0
    exact kinFormB_secProj_offdiag (ℓ := fsSide v μ) hℓ (Φ := Φ) hΦ (i := i) (k := i+2) hik
  have hpot : (∑ i ∈ Finset.range (n-1), polPot v h μ n (Work.BoseFixB2.secProj (fsSide v μ) i Φ)
      (Work.BoseFixB2.secProj (fsSide v μ) (i+2) Φ))
      = ∑ i ∈ Finset.range (n-1), ∫ x in Submission.BoseGases.abox n (fsSide v μ),
          Work.BoseFixB2.secProj (fsSide v μ) i Φ x * Work.BoseFixB2.secProj (fsSide v μ) (i+2) Φ x
            * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) (fsSide v μ) μ 0 x := by
    apply Finset.sum_congr rfl
    intro i hi
    exact polPot_eq_integral (v := v) (h := h) (μ := μ) (n := n) (R := R) hR hv_supp hv1 hRℓ
      (hsm i) (hsm (i+2))
  rw [sum_polB_split (m := n-1) (d := 2), hkin, hpot, zero_add]
  exact (potBand_secProj_v4 (v := v) (h := h) (μ := μ) (n := n) (ℓ := fsSide v μ) hℓ hvrad hR hv_supp hv1 hRℓ hΦ).2

/-- **FS §6 `eq:dvapriori`** (`thm:aprioribounds`, the `d₁,d₂` bound). -/
theorem dOne_dTwo_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J C₁ εw : ℝ} (hC₁ : 0 ≤ C₁) (hεw : 0 < εw)
    (hwin : ∀ μ : ℝ, Work.BoseBoxFix.Adm v εw μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n Φ → Work.BoseBoxFix.IsLowB v h J μ n Φ →
        |(n : ℝ) - μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3|
          ≤ C₁ * Work.BoseBox.nWindow (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
              (_root_.BoseGases.a v)) :
    ∃ K ε₀ : ℝ, 0 ≤ K ∧ 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        0 < Work.BoseBoxFix.normB v μ n Φ → Work.BoseBoxFix.IsLowB v h J μ n Φ →
        |Work.BoseFixB2.dOne v h μ n (Work.BoseFixB2.fsSide v μ) Φ|
          + |Work.BoseFixB2.dTwo v h μ n (Work.BoseFixB2.fsSide v μ) Φ|
          ≤ K * μ ^ 2 * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
  obtain ⟨ε_R, hε_R, hRge⟩ := exists_adm_chiR0_ge v hav hR
  obtain ⟨ε_w, hε_w, hwinfac⟩ := exists_window_factor_le v hav hC₁
  have hqc : 0 ≤ Submission.BoseGases.qcrossC := by
    rw [Submission.BoseGases.qcrossC]; positivity
  have hpc : 0 ≤ Submission.BoseGases.potappC := by
    rw [Submission.BoseGases.potappC]; positivity
  have hg0m : 0 ≤ Work.BoseBox.g0mass v h := by
    rw [Work.BoseBox.g0mass]
    exact MeasureTheory.integral_nonneg (fun y => abs_nonneg _)
  have hIv : 0 ≤ ∫ z : EuclideanSpace ℝ (Fin 3), v z :=
    MeasureTheory.integral_nonneg (fun z => hv z)
  have hIav : 0 ≤ ∫ y : EuclideanSpace ℝ (Fin 3), |v y| :=
    MeasureTheory.integral_nonneg (fun y => abs_nonneg _)
  refine ⟨13 * Submission.BoseGases.qcrossC * (∫ z : EuclideanSpace ℝ (Fin 3), v z)
      + 4 * Work.BoseBox.chiSup ^ 2
          * (Work.BoseBox.g0mass v h + ∫ y : EuclideanSpace ℝ (Fin 3), |v y|)
      + 5 * Submission.BoseGases.potappC * (_root_.BoseGases.a v),
    min ε_R (min ε_w (min εw 1)), ?_, ?_, ?_⟩
  · have h1 : 0 ≤ 13 * Submission.BoseGases.qcrossC * (∫ z : EuclideanSpace ℝ (Fin 3), v z) :=
      mul_nonneg (mul_nonneg (by norm_num) hqc) hIv
    have h2 : 0 ≤ 4 * Work.BoseBox.chiSup ^ 2
        * (Work.BoseBox.g0mass v h + ∫ y : EuclideanSpace ℝ (Fin 3), |v y|) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith)
    have h3 : 0 ≤ 5 * Submission.BoseGases.potappC * (_root_.BoseGases.a v) :=
      mul_nonneg (mul_nonneg (by norm_num) hpc) hav.le
    linarith
  · exact lt_min hε_R (lt_min hε_w (lt_min hεw one_pos))
  · intro μ hAdm hJKB n Φ hpos hlow
    have hμ : 0 < μ := hAdm.1
    have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
      Work.BoseBox.sideAt_pos hμ hav
    have hAdmW : Work.BoseBoxFix.Adm v εw μ :=
      Adm_mono (ε := min ε_R (min ε_w (min εw 1))) (ε' := εw)
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))) hAdm
    have hwinμ := hwin μ hAdmW hJKB n Φ hpos hlow
    have hε1 : min ε_R (min ε_w (min εw 1)) ≤ 1 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hεw2 : min ε_R (min ε_w (min εw 1)) ≤ ε_w :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 hε1
    have ht_w : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε_w := le_trans hAdm.2.1 hεw2
    have hfac := hwinfac μ hμ ht_w
    have hRℓ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 :=
      hRge μ (Adm_mono (ε := min ε_R (min ε_w (min εw 1))) (ε' := ε_R) (min_le_left _ _) hAdm)
    have hS : Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        = Work.BoseBox.boxSide (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
            (_root_.BoseGases.a v) := rfl
    have hnb : Work.BoseBox.nWindow (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)) μ
        (_root_.BoseGases.a v)
        = μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
            * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ (3 / 2 : ℝ)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 4 : ℝ)) := by
      rw [Work.BoseBox.nWindow, ← hS]
      ring
    have hW1 : |(n : ℝ) - μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3|
        ≤ (C₁ * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ (3 / 2 : ℝ)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 4 : ℝ)))
          * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) := by
      rw [hnb] at hwinμ
      nlinarith [hwinμ]
    have hℓ3 : 0 ≤ μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by positivity
    have hW2 : (C₁ * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ (3 / 2 : ℝ)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 4 : ℝ)))
          * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3)
        ≤ (1 / 2) * (μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) :=
      mul_le_mul_of_nonneg_right hfac hℓ3
    have hn2 : (n : ℝ) ≤ 2 * μ * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
      have habs := abs_le.mp (le_trans hW1 hW2)
      linarith [habs.2]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    -- the band identities
    have hb1 := band_one (v := v) (h := h) (μ := μ) (n := n) hR hv1 hv_supp Φ.contDiff Φ.symm hvrad
      (show 0 < fsSide v μ from hℓ) hRℓ
    have hb2 := band_two (v := v) (h := h) (μ := μ) (n := n) hR hv1 hv_supp Φ.contDiff Φ.symm hvrad
      (show 0 < fsSide v μ from hℓ) hRℓ
    have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
    have hdOne : Work.BoseFixB2.dOne v h μ n (Work.BoseFixB2.fsSide v μ) Φ
        = (Submission.BoseGases.q1word (N := n) (Work.BoseFixB2.fsSide v μ) μ
              (Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) (Submission.BoseGases.g0 v h))
              (Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) v) Φ
            + Submission.BoseGases.q3word (N := n) (Work.BoseFixB2.fsSide v μ)
              (Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) v) Φ)
          / Work.BoseBoxFix.normB v μ n Φ := by
      rw [Work.BoseFixB2.dOne, hb1]
      ring
    have hdTwo : Work.BoseFixB2.dTwo v h μ n (Work.BoseFixB2.fsSide v μ) Φ
        = ((∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x in Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ),
                Submission.BoseGases.aP (Work.BoseFixB2.fsSide v μ) p.1
                    (Submission.BoseGases.aP (Work.BoseFixB2.fsSide v μ) p.2 Φ) x
                  * Submission.BoseGases.aQ (Work.BoseFixB2.fsSide v μ) p.2
                    (Submission.BoseGases.aQ (Work.BoseFixB2.fsSide v μ) p.1 Φ) x
                  * Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) v (x p.1) (x p.2)))
          / Work.BoseBoxFix.normB v μ n Φ := by
      rw [Work.BoseFixB2.dTwo, hb2]
      ring
    have hnum := dvap_numerator_bound (v := v) (h := h) (μ := μ) (n := n) (R := R) (J := J)
      (show 0 < fsSide v μ from hℓ) hμ hav hR hv hvrad hv1 hv_supp hRℓ hJKB ht1 hn2
      Φ.contDiff Φ.symm Φ.nezero hlow
    rw [hdOne, hdTwo]
    have hν0 : 0 < Work.BoseBoxFix.normB v μ n Φ := hpos
    simp only [abs_div, abs_of_pos hν0]
    rw [← add_div]
    have hAB : |Submission.BoseGases.q1word (N := n) (Work.BoseFixB2.fsSide v μ) μ
          (Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) (Submission.BoseGases.g0 v h))
          (Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) v) Φ
        + Submission.BoseGases.q3word (N := n) (Work.BoseFixB2.fsSide v μ)
          (Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) v) Φ|
        ≤ |Submission.BoseGases.q1word (N := n) (Work.BoseFixB2.fsSide v μ) μ
            (Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) (Submission.BoseGases.g0 v h))
            (Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) v) Φ|
          + |Submission.BoseGases.q3word (N := n) (Work.BoseFixB2.fsSide v μ)
            (Submission.BoseGases.wPairC (Work.BoseFixB2.fsSide v μ) v) Φ| := abs_add_le _ _
    simp only [Work.BoseFixB2.fsSide] at hnum hAB ⊢
    rw [div_le_iff₀ hν0]
    linarith [hnum, hAB]

end

end Work.BoseFixB2.DvApriori
