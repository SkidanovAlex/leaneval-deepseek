import ChallengeDeps
import Submission.Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet
import Submission.Work.SmallBoxSliding.boxMassLeCube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `swhSlidingBookkeeping` — the sliding-box bookkeeping at small diluteness

The elementary "everything is large/small in the right direction" packet for the sliding box
`B(u) = dlBox (bSide v μ) (bD v μ) u` on the good set:

* the volume `bV v μ u = |B(u)|` is positive, at least `1`, and at least `μ⁻¹` (hence
  `1 ≤ μ·bV`), and at most `(ℓd)³`;
* `d = bD v μ ≤ 1` and `M = bM v μ = 48`;
* the support radius `R` of `v` is smaller than both `ℓd/16` and `ℓ·chiR0`.

The two geometric facts are the corpus lemmas
`Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet` (`|B(u)| ≥ (μ^{-1/3})³` on the good set,
via the product formula for the box volume) and
`Work.SmallBoxSliding.boxMassLeCube` (`|B(u)| ≤ (ℓd)³`).

The parameters are FS's monomials in `t = μ(a v)³`: `ℓ = a·t^{-163/323}`,
`d = t^{6/323}`, so `ℓ d = a·t^{-157/323}`; the two requirements on `R` are pure
monomial comparisons and are met by taking `ε₀` small enough (`t ≤ ε₀`), the choice being

    ε₀ = min 1 (min (a v)³ (min (a v/(16R))^{323/157} ((a v)·chiR0/R)^{323/163})) .

The threshold also forces `μ ≤ 1` (through `ε₀ ≤ (a v)³`), which is what turns `μ⁻¹ ≥ 1`
into `1 ≤ bV`.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Metric

namespace Work.BoseB1Cube

set_option linter.unusedVariables false

/-- `fsXp · c` is antitone in its *base* for `c ≤ 0` (`0 < t ≤ e`). -/
private lemma fsXp_anti {t e c : ℝ} (ht : 0 < t) (hte : t ≤ e) (hc : c ≤ 0) :
    Work.BoseBox.fsXp e c ≤ Work.BoseBox.fsXp t c := by
  rw [Work.BoseBox.fsXp, Work.BoseBox.fsXp]
  exact Real.rpow_le_rpow_of_nonpos ht hte
    (div_nonpos_of_nonpos_of_nonneg hc (by norm_num))

theorem swhSlidingBookkeeping {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hav : 0 < _root_.BoseGases.a v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3), u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) μ →
        0 < Work.BoseFixB1.bV v μ u ∧
        1 ≤ Work.BoseFixB1.bV v μ u ∧
        1 ≤ μ * Work.BoseFixB1.bV v μ u ∧
        Work.BoseFixB1.bV v μ u ≤ (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ 3 ∧
        (Work.BoseFixB1.bD v μ) ≤ 1 ∧
        Work.BoseFixB1.bM v μ = 48 ∧
        R ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ / 16 ∧
        R ≤ Work.BoseFixB1.bSide v μ * Submission.BoseGases.chiR0 := by
  have hav0 : 0 < _root_.BoseGases.a v := hav
  have hchi0 : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  have hA0 : 0 < _root_.BoseGases.a v / (16 * R) := by positivity
  have hB0 : 0 < _root_.BoseGases.a v * Submission.BoseGases.chiR0 / R := by positivity
  set e : ℝ := min 1 (min ((_root_.BoseGases.a v) ^ 3)
      (min (((_root_.BoseGases.a v) / (16 * R)) ^ (323 / 157 : ℝ))
           (((_root_.BoseGases.a v) * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ))))
    with hedef
  have hepos : 0 < e := by
    rw [hedef]
    exact lt_min (by norm_num)
      (lt_min (pow_pos hav0 3)
        (lt_min (Real.rpow_pos_of_pos hA0 _) (Real.rpow_pos_of_pos hB0 _)))
  refine ⟨e, hepos, ?_⟩
  intro μ hAdm u hu
  -- smallness facts about `e`
  have he1 : e ≤ 1 := by rw [hedef]; exact min_le_left _ _
  have hea : e ≤ (_root_.BoseGases.a v) ^ 3 := by
    rw [hedef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have heA : e ≤ ((_root_.BoseGases.a v) / (16 * R)) ^ (323 / 157 : ℝ) := by
    rw [hedef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have heB : e ≤ ((_root_.BoseGases.a v) * Submission.BoseGases.chiR0 / R) ^ (323 / 163 : ℝ) := by
    rw [hedef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  -- parameters
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav0 3)
  have htε : μ * (_root_.BoseGases.a v) ^ 3 ≤ e := Work.BoseFixB1.adm_dilute hAdm
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans htε he1
  have hμle1 : μ ≤ 1 := by
    refine le_of_mul_le_mul_right ?_ (pow_pos hav0 3)
    calc μ * (_root_.BoseGases.a v) ^ 3 ≤ e := htε
      _ ≤ (_root_.BoseGases.a v) ^ 3 := hea
      _ = 1 * (_root_.BoseGases.a v) ^ 3 := by ring
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hd1 : Work.BoseFixB1.bD v μ ≤ 1 := by
    show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1
    rw [Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_le_one ht0 ht1 (by norm_num)
  -- the closed forms `ℓd = a·fsXp t (-157)`, `ℓ = a·fsXp t (-163)`
  have hsd : Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ
      = (_root_.BoseGases.a v) * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157) := by
    show Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d = _
    rw [mul_comm, Work.BoseFixB1.d_mul_sideAt_eq hav0 hμ]
  have hbs : Work.BoseFixB1.bSide v μ
      = (_root_.BoseGases.a v) * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-163) := by
    show Work.BoseBox.sideAt μ (_root_.BoseGases.a v) = _
    exact Work.BoseFixB1.sideAt_eq_fsXp hav0 hμ
  -- the good-set regime `μ^{-1/3} ≤ ℓd`
  have hreg : μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ := by
    rw [hsd, Work.BoseFixB1.mu_inv_third_eq hav0 hμ]
    exact mul_le_mul_of_nonneg_left
      (Work.BoseBox.fsXp_le_fsXp ht0 ht1 (by norm_num : (-157 : ℝ) ≤ -(323 / 3))) hav0.le
  -- the volume bounds
  have hVge : (μ ^ (-(1 / 3 : ℝ))) ^ 3 ≤ Work.BoseFixB1.bV v μ u :=
    Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet hℓ hd hd1 hμ hreg hu
  have hcube : (μ ^ (-(1 / 3 : ℝ))) ^ 3 = μ⁻¹ := by
    have h : (-(1 / 3 : ℝ)) * (↑(3 : ℕ) : ℝ) = -1 := by norm_num
    rw [← Real.rpow_natCast (μ ^ (-(1 / 3 : ℝ))) 3, ← Real.rpow_mul hμ.le, h, Real.rpow_neg_one]
  -- the two monomial comparisons that place `R`
  have hpowA : e ^ (157 / 323 : ℝ) ≤ (_root_.BoseGases.a v) / (16 * R) := by
    have hx : 0 ≤ (_root_.BoseGases.a v) / (16 * R) := by positivity
    have h1 := Real.rpow_le_rpow hepos.le heA (by norm_num : (0 : ℝ) ≤ (157 / 323 : ℝ))
    rwa [← Real.rpow_mul hx, show (323 / 157 : ℝ) * (157 / 323) = 1 by norm_num,
      Real.rpow_one] at h1
  have hpowB : e ^ (163 / 323 : ℝ) ≤ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 / R := by
    have hx : 0 ≤ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 / R := by positivity
    have h1 := Real.rpow_le_rpow hepos.le heB (by norm_num : (0 : ℝ) ≤ (163 / 323 : ℝ))
    rwa [← Real.rpow_mul hx, show (323 / 163 : ℝ) * (163 / 323) = 1 by norm_num,
      Real.rpow_one] at h1
  have hfsA : Work.BoseBox.fsXp e (-157) = (e ^ (157 / 323 : ℝ))⁻¹ := by
    rw [Work.BoseBox.fsXp, show (-157 : ℝ) / 323 = -(157 / 323) by norm_num,
      Real.rpow_neg hepos.le]
  have hfsB : Work.BoseBox.fsXp e (-163) = (e ^ (163 / 323 : ℝ))⁻¹ := by
    rw [Work.BoseBox.fsXp, show (-163 : ℝ) / 323 = -(163 / 323) by norm_num,
      Real.rpow_neg hepos.le]
  have keyA : 16 * R / (_root_.BoseGases.a v)
      ≤ Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157) := by
    calc 16 * R / (_root_.BoseGases.a v) = ((_root_.BoseGases.a v) / (16 * R))⁻¹ := by
          rw [inv_div]
        _ ≤ (e ^ (157 / 323 : ℝ))⁻¹ :=
            inv_anti₀ (Real.rpow_pos_of_pos hepos _) hpowA
        _ = Work.BoseBox.fsXp e (-157) := hfsA.symm
        _ ≤ Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157) :=
            fsXp_anti ht0 htε (by norm_num)
  have keyB : R / ((_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
      ≤ Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-163) := by
    calc R / ((_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
          = (((_root_.BoseGases.a v) * Submission.BoseGases.chiR0) / R)⁻¹ := by rw [inv_div]
        _ ≤ (e ^ (163 / 323 : ℝ))⁻¹ :=
            inv_anti₀ (Real.rpow_pos_of_pos hepos _) hpowB
        _ = Work.BoseBox.fsXp e (-163) := hfsB.symm
        _ ≤ Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-163) :=
            fsXp_anti ht0 htε (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, hd1, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_trans ((one_le_inv₀ hμ).mpr hμle1) (hcube ▸ hVge))
  · calc (1 : ℝ) ≤ μ⁻¹ := (one_le_inv₀ hμ).mpr hμle1
      _ = (μ ^ (-(1 / 3 : ℝ))) ^ 3 := hcube.symm
      _ ≤ Work.BoseFixB1.bV v μ u := hVge
  · calc (1 : ℝ) = μ * μ⁻¹ := (mul_inv_cancel₀ (ne_of_gt hμ)).symm
      _ = μ * (μ ^ (-(1 / 3 : ℝ))) ^ 3 := by rw [hcube]
      _ ≤ μ * Work.BoseFixB1.bV v μ u := mul_le_mul_of_nonneg_left hVge hμ.le
  · exact Work.SmallBoxSliding.boxMassLeCube hℓ hd u
  · show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = 48
    rw [Work.BoseFixB1.M_eq_mValue]
    rfl
  · rw [hsd, le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    calc R * 16 = (_root_.BoseGases.a v) * (16 * R / (_root_.BoseGases.a v)) := by
          field_simp
      _ ≤ (_root_.BoseGases.a v)
            * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-157) :=
          mul_le_mul_of_nonneg_left keyA hav0.le
  · rw [hbs]
    calc R = (_root_.BoseGases.a v) * Submission.BoseGases.chiR0
              * (R / ((_root_.BoseGases.a v) * Submission.BoseGases.chiR0)) := by
          field_simp
      _ ≤ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0
            * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-163) :=
          mul_le_mul_of_nonneg_left keyB (by positivity)
      _ = (_root_.BoseGases.a v) * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-163)
            * Submission.BoseGases.chiR0 := by ring

end Work.BoseB1Cube
