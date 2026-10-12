import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.RegimeAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseFixB1S

/-- The FS-faithful excited count is a sum of integrals of squares (hence nonnegative),
for **every** real box side. -/
private lemma cnPlusBoxInd_nonnegB (a : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ)
    {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ) :
    0 ≤ Work.UBBInputs8.cnPlusBoxInd a A volA Ψ := by
  unfold Work.UBBInputs8.cnPlusBoxInd
  exact Finset.sum_nonneg fun i _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _

/-- **The closed form of the gap coefficient at FS's parameters.**  At the diluteness
`t = μa³` the small-box side is `dℓ = a·fsXp t (-157)`, so

    `tbGapCoeff (dℓ) ε_T = ½·(1+π⁻²)⁻¹·t^{1279/1292}·a⁻²`,

i.e. the coefficient is `½·tbPiFactor·fsXp t (1279/4)·a⁻²`. -/
private lemma tbGapCoeff_sideAt_eq {a μ : ℝ} (hA : 0 < a) (hμ : 0 < μ) :
    Work.SmallBoxTBWord.tbGapCoeff
        (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d)
        (Work.BoseBox.paramsAt μ a).eT
      = (1 / 2) * Work.SmallBoxTBWord.tbPiFactor * Work.BoseBox.fsXp (μ * a ^ 3) (1279 / 4)
          * (a ^ 2)⁻¹ := by
  have ht : (0 : ℝ) < μ * a ^ 3 := by positivity
  have heT : (Work.BoseBox.paramsAt μ a).eT = Work.BoseBox.fsXp (μ * a ^ 3) (23 / 4) := rfl
  -- the small-box side `dℓ = a·fsXp t (-157)`
  have hS : Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d
      = a * Work.BoseBox.fsXp (μ * a ^ 3) (-157) := by
    rw [mul_comm, Work.BoseFixB1.d_mul_sideAt_eq hA hμ]
  -- its square and the inverse
  have hsq : ((a * Work.BoseBox.fsXp (μ * a ^ 3) (-157)) ^ 2)⁻¹
      = (a ^ 2)⁻¹ * Work.BoseBox.fsXp (μ * a ^ 3) 314 := by
    rw [mul_pow, Work.BoseBox.fsXp_pow ht.le, mul_inv,
      Work.BoseBox.fsXp_inv ht]
    norm_num
  rw [Work.SmallBoxTBWord.tbGapCoeff, hS, heT, hsq]
  have hmul : Work.BoseBox.fsXp (μ * a ^ 3) (23 / 4) * Work.BoseBox.fsXp (μ * a ^ 3) 314
      = Work.BoseBox.fsXp (μ * a ^ 3) (1279 / 4) := by
    rw [Work.BoseBox.fsXp_mul ht]
    norm_num
  rw [← hmul]
  ring

/-- **The arithmetic core.**  With `t = μa³ ≤ ε₀ := (c/(2K+2c))^{1292/13}` (`c = (1+π⁻²)⁻¹`,
`K ≥ 0`), the coefficient `K·μa` is dominated by the gap coefficient
`½·c·fsXp t (1279/4)·a⁻²`: indeed `ε₀^{-13/1292} = 2K/c + 2`. -/
private lemma coef_absorb {a μ K : ℝ} (hA : 0 < a) (hμ : 0 < μ) (hK : 0 ≤ K)
    (htle : μ * a ^ 3 ≤ (Work.SmallBoxTBWord.tbPiFactor
      / (2 * K + 2 * Work.SmallBoxTBWord.tbPiFactor)) ^ ((1292 : ℝ) / 13)) :
    K * (μ * a) ≤ (1 / 2) * Work.SmallBoxTBWord.tbPiFactor
      * Work.BoseBox.fsXp (μ * a ^ 3) (1279 / 4) * (a ^ 2)⁻¹ := by
  set c : ℝ := Work.SmallBoxTBWord.tbPiFactor with hcdef
  have hc : 0 < c := Work.SmallBoxTBWord.tbPiFactor_pos
  set ε : ℝ := (c / (2 * K + 2 * c)) ^ ((1292 : ℝ) / 13) with hεdef
  set t : ℝ := μ * a ^ 3 with htdef
  have ht : 0 < t := by rw [htdef]; positivity
  have hbase0 : 0 < c / (2 * K + 2 * c) := by positivity
  have htle' : t ≤ ε := by rw [htdef, hεdef]; exact htle
  -- the closed form of `ε^{-13/1292}`
  have hεinv : ε ^ (-(13 / 1292) : ℝ) = 2 * K / c + 2 := by
    rw [hεdef]
    rw [← Real.rpow_mul hbase0.le]
    rw [show ((1292 : ℝ) / 13) * (-(13 / 1292)) = -1 by norm_num,
      Real.rpow_neg_one]
    rw [inv_div]
    field_simp
  -- `t^{-13/1292} ≥ ε^{-13/1292} = 2K/c + 2`
  have hmono : ε ^ (-(13 / 1292) : ℝ) ≤ t ^ (-(13 / 1292) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos ht htle' (by norm_num)
  have hKt : K ≤ (1 / 2) * c * t ^ (-(13 / 1292) : ℝ) := by
    have h1 : (1 / 2) * c * (2 * K / c + 2) = K + c := by
      field_simp
    have h2 : K ≤ (1 / 2) * c * (2 * K / c + 2) := by rw [h1]; linarith
    have h3 : (1 / 2) * c * (2 * K / c + 2) ≤ (1 / 2) * c * t ^ (-(13 / 1292) : ℝ) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← hεinv]
      exact hmono
    linarith
  -- multiply by `t > 0` and identify `t^{1-13/1292} = fsXp t (1279/4)`
  have hkey : K * t ≤ (1 / 2) * c * Work.BoseBox.fsXp t (1279 / 4) := by
    have h4 : K * t ≤ (1 / 2) * c * t ^ (-(13 / 1292) : ℝ) * t :=
      mul_le_mul_of_nonneg_right hKt ht.le
    have hid : t ^ (-(13 / 1292) : ℝ) * t = Work.BoseBox.fsXp t (1279 / 4) := by
      have h1 : t ^ (-(13 / 1292) : ℝ) * t = t ^ (-(13 / 1292) + 1 : ℝ) := by
        rw [Real.rpow_add ht, Real.rpow_one]
      rw [h1, Work.BoseBox.fsXp]
      congr 1
      norm_num
    calc K * t ≤ (1 / 2) * c * t ^ (-(13 / 1292) : ℝ) * t := h4
      _ = (1 / 2) * c * (t ^ (-(13 / 1292) : ℝ) * t) := by ring
      _ = (1 / 2) * c * Work.BoseBox.fsXp t (1279 / 4) := by rw [hid]
  -- transport along `t = μa³` and divide by `a²`
  have ha2 : 0 < a ^ 2 := by positivity
  have h5 : K * t * (a ^ 2)⁻¹ ≤ (1 / 2) * c * Work.BoseBox.fsXp t (1279 / 4) * (a ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr ha2.le)
  have h6 : K * (μ * a) = K * t * (a ^ 2)⁻¹ := by
    rw [htdef]
    field_simp
  rw [h6]
  exact h5

theorem gapAbsorbB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        K * (μ * (_root_.BoseGases.a v))
            * Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.SmallBoxTBWord.tbGapCoeff
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            * Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ) := by
  refine ⟨(Work.SmallBoxTBWord.tbPiFactor / (2 * K + 2 * Work.SmallBoxTBWord.tbPiFactor))
      ^ ((1292 : ℝ) / 13), ?_, ?_⟩
  · exact Real.rpow_pos_of_pos (by
      have := Work.SmallBoxTBWord.tbPiFactor_pos
      positivity) _
  · intro μ hAdm n Φ u
    obtain ⟨hμ, htle, _hPar⟩ := hAdm
    have ha : 0 < _root_.BoseGases.a v := hav
    have hcoef : K * (μ * _root_.BoseGases.a v)
        ≤ Work.SmallBoxTBWord.tbGapCoeff
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT := by
      rw [tbGapCoeff_sideAt_eq ha hμ]
      exact coef_absorb ha hμ hK htle
    exact mul_le_mul_of_nonneg_right hcoef (cnPlusBoxInd_nonnegB _ _ _ _)

end Work.BoseFixB1S
