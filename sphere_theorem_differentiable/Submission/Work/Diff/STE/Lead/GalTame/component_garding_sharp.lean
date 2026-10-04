import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory BigOperators

noncomputable section

/-- **Cauchy–Schwarz for sums of square roots of nonnegative reals.**  If `a, b ≥ 0` then
`Σᵢ √(aᵢ)·√(bᵢ) ≤ √(Σᵢ aᵢ)·√(Σᵢ bᵢ)`.  This is Cauchy–Schwarz in `ℝ^n` applied to the sequences
`√(aᵢ)`, `√(bᵢ)`, followed by the monotonicity of `√·`. -/
lemma sum_sqrt_mul_sqrt_le {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, Real.sqrt (a i) * Real.sqrt (b i)) ≤
      Real.sqrt (∑ i, a i) * Real.sqrt (∑ i, b i) := by
  have hA : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  have hsq : (∑ i, Real.sqrt (a i) * Real.sqrt (b i)) ^ 2 ≤ (∑ i, a i) * (∑ i, b i) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (b i))
    rwa [Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (ha i)),
      Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hb i))] at h
  have hnon : 0 ≤ ∑ i, Real.sqrt (a i) * Real.sqrt (b i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc (∑ i, Real.sqrt (a i) * Real.sqrt (b i))
      = Real.sqrt ((∑ i, Real.sqrt (a i) * Real.sqrt (b i)) ^ 2) := (Real.sqrt_sq hnon).symm
    _ ≤ Real.sqrt ((∑ i, a i) * (∑ i, b i)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ i, a i) * Real.sqrt (∑ i, b i) := Real.sqrt_mul hA _

/-- `√(x + y) ≤ √x + √y` for nonnegative `x, y`. -/
lemma sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y]

/-- **Young's inequality for square roots with parameter.**  For `a, b ≥ 0` and `γ > 0`,
`√(a·b) ≤ (γ·a + b/γ)/2` (the case `x = γa`, `y = b/γ` of the arithmetic–geometric mean
inequality, using `(γa)·(b/γ) = a·b`). -/
lemma sqrt_mul_le_amgm {a b γ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 < γ) :
    Real.sqrt (a * b) ≤ (γ * a + b / γ) / 2 := by
  have heq : Real.sqrt (a * b) = Real.sqrt (γ * a) * Real.sqrt (b / γ) := by
    rw [← Real.sqrt_mul (mul_nonneg hγ.le ha)]
    congr 1
    field_simp
  rw [heq]
  exact Work.Diff.STE.Lead.Gal.sqrt_mul_sqrt_le (mul_nonneg hγ.le ha) (div_nonneg hb hγ.le)

theorem component_garding_sharp {n : ℕ} (k : ℕ)
    (lamT S F Cd CT e : ℝ) (he : 0 < e) (hS : 0 ≤ S) (hCd : 0 ≤ Cd) (hCT : 0 ≤ CT)
    (hF : 0 ≤ F) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧
      ∀ (A : Fin n → Fin n → (Fin n → ℝ) → ℝ) (Th u v : (Fin n → ℝ) → ℂ)
        (hsmA : ∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d))
        (hperA : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
        (hsmT : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) Th)
        (hperT : Work.Diff.STE.Periodic1 Th)
        (hsmu : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u)
        (hperu : Work.Diff.STE.Periodic1 u)
        (hid : ∀ z, v z = (∑ c, ∑ d,
            ((A c d z : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) z) + Th z)
        (hg : (∑ l : Fin k → Fin n, Work.Diff.STE.L2re
            (fun z => ∑ c, ∑ d, ((A c d z : ℝ) : ℂ) *
              Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)
            (Work.Diff.STE.pdVec k l u))
          ≤ -(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) u + F * Work.Diff.STE.ENormSq k u)
        (KA Q1 : ℝ) (hKA : 0 ≤ KA) (hQ1 : 0 ≤ Q1)
        (hdef : ∀ l : Fin k → Fin n, Work.Diff.STE.ENormSq 0 (fun z =>
            Work.Diff.STE.pdVec k l (fun y => ∑ c, ∑ d, ((A c d y : ℝ) : ℂ) *
                Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z
              - ∑ c, ∑ d, ((A c d z : ℝ) : ℂ) *
                Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)
            ≤ Cd * (S ^ 2 * (1 + KA + Q1)))
        (hTh : ∀ l : Fin k → Fin n, Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l Th)
            ≤ CT * (1 + Q1)),
        (∑ l : Fin k → Fin n, Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v)
            (Work.Diff.STE.pdVec k l u))
          ≤ -(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) u
            + Cg * (1 + Work.Diff.STE.ENormSq k u + KA)
            + (Fintype.card (Fin k → Fin n) : ℝ) * (2 * e) * Q1 := by
  classical
  set card : ℝ := ((Fintype.card (Fin k → Fin n) : ℕ) : ℝ) with hcarddef
  have hcard_nn : 0 ≤ card := by rw [hcarddef]; positivity
  set g : ℝ := Real.sqrt (card * (Cd * S ^ 2)) + Real.sqrt (card * CT) with hgdef
  have hg_nn : 0 ≤ g := by
    rw [hgdef]; exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  set γ : ℝ := 2 * e / (g + 1) with hγdef
  have hγ_pos : 0 < γ := by
    rw [hγdef]; exact div_pos (by linarith) (by linarith)
  refine ⟨F + 3 * g + g / γ + 1, ?_, ?_⟩
  · have h0 : 0 ≤ g / γ := div_nonneg hg_nn hγ_pos.le
    linarith
  · intro A Th u v hsmA hperA hsmT hperT hsmu hperu hid hgard KA Q1 hKA hQ1 hdef hTh
    -- ### the nonlinearity and its level-`k` linearisation
    let w : (Fin n → ℝ) → ℂ :=
      fun y => ∑ c, ∑ d, ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y
    let FL : (Fin k → Fin n) → (Fin n → ℝ) → ℂ := fun l z => ∑ c, ∑ d,
      ((A c d z : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z
    have hws : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) w := by
      refine ContDiff.sum fun c _ => ContDiff.sum fun d _ => ?_
      exact (Work.Diff.STE.Lead.Gal.contDiff_ofReal_comp (hsmA c d)).mul
        (Work.Diff.STE.Lead.Gal.contDiff_pd_pd hsmu d c)
    have hv_eq : v = w + Th := by
      funext z; simpa only [Pi.add_apply] using hid z
    have hcw : ∀ l : Fin k → Fin n, Continuous (Work.Diff.STE.pdVec k l w) :=
      fun l => (Work.Diff.STE.Lead.Gal.contDiff_pdVec hws l).continuous
    have hcF : ∀ l : Fin k → Fin n, Continuous (FL l) := by
      intro l
      refine continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ => ?_
      exact ((Work.Diff.STE.Lead.Gal.contDiff_ofReal_comp (hsmA c d)).continuous).mul
        ((Work.Diff.STE.Lead.Gal.contDiff_pd_pd
          (Work.Diff.STE.Lead.Gal.contDiff_pdVec hsmu l) d c).continuous)
    have hcT : ∀ l : Fin k → Fin n, Continuous (Work.Diff.STE.pdVec k l Th) :=
      fun l => (Work.Diff.STE.Lead.Gal.contDiff_pdVec hsmT l).continuous
    have hcu : ∀ l : Fin k → Fin n, Continuous (Work.Diff.STE.pdVec k l u) :=
      fun l => (Work.Diff.STE.Lead.Gal.contDiff_pdVec hsmu l).continuous
    -- ### the per-`l` decomposition of `∂^l v`
    have hstep : ∀ l : Fin k → Fin n,
        Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v) (Work.Diff.STE.pdVec k l u)
          ≤ Work.Diff.STE.L2re (FL l) (Work.Diff.STE.pdVec k l u)
            + |Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
                (Work.Diff.STE.pdVec k l u)|
            + |Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u)| := by
      intro l
      have h1 : Work.Diff.STE.pdVec k l v = Work.Diff.STE.pdVec k l (w + Th) := by rw [hv_eq]
      have h2 : Work.Diff.STE.pdVec k l (w + Th)
          = Work.Diff.STE.pdVec k l w + Work.Diff.STE.pdVec k l Th := by
        rw [Work.Diff.STE.pdVec]
        exact Work.Diff.STE.flat.pdList_add (List.ofFn l) hws hsmT
      have h3 : Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v) (Work.Diff.STE.pdVec k l u)
          = Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l w) (Work.Diff.STE.pdVec k l u)
            + Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u) := by
        rw [h1, h2]
        exact Work.Diff.STE.cm_L2re_add _ _ _ (hcw l) (hcT l) (hcu l)
      have h4 : Work.Diff.STE.pdVec k l w
          = FL l + (Work.Diff.STE.pdVec k l w - FL l) := by
        funext z; simp only [Pi.add_apply, Pi.sub_apply]; ring
      have h5 : Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l w) (Work.Diff.STE.pdVec k l u)
          = Work.Diff.STE.L2re (FL l) (Work.Diff.STE.pdVec k l u)
            + Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
                (Work.Diff.STE.pdVec k l u) := by
        conv_lhs => rw [h4]
        exact Work.Diff.STE.cm_L2re_add _ _ _ (hcF l) ((hcw l).sub (hcF l)) (hcu l)
      rw [h3, h5]
      have a := le_abs_self (Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
        (Work.Diff.STE.pdVec k l u))
      have b := le_abs_self (Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th)
        (Work.Diff.STE.pdVec k l u))
      linarith
    -- ### notation
    let rE : ℝ := Real.sqrt (Work.Diff.STE.ENormSq k u)
    have hrE_nn : 0 ≤ rE := Real.sqrt_nonneg _
    have hrE_eq : rE = Real.sqrt (Work.Diff.STE.ENormSq k u) := rfl
    have hE_nn : 0 ≤ Work.Diff.STE.ENormSq k u := Work.Diff.STE.Lead.Gal.ENormSq_nonneg (m := k) u
    -- ### the defect and Th sums (Cauchy–Schwarz over the multi-indices)
    have hDef_l : ∀ l : Fin k → Fin n, Work.Diff.STE.ENormSq 0
        (fun z => Work.Diff.STE.pdVec k l w z - FL l z) ≤ Cd * (S ^ 2 * (1 + KA + Q1)) :=
      fun l => hdef l
    have hsumDl : (∑ l : Fin k → Fin n, Work.Diff.STE.ENormSq 0
        (fun z => Work.Diff.STE.pdVec k l w z - FL l z))
        ≤ card * (Cd * (S ^ 2 * (1 + KA + Q1))) := by
      calc (∑ l : Fin k → Fin n, Work.Diff.STE.ENormSq 0
              (fun z => Work.Diff.STE.pdVec k l w z - FL l z))
          ≤ ∑ _l : Fin k → Fin n, Cd * (S ^ 2 * (1 + KA + Q1)) :=
            Finset.sum_le_sum fun l _ => hDef_l l
        _ = card * (Cd * (S ^ 2 * (1 + KA + Q1))) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcarddef]
    have hEsum : (∑ l : Fin k → Fin n, Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l u))
        = Work.Diff.STE.ENormSq k u := by
      rw [Work.Diff.STE.ENormSq]
      exact Finset.sum_congr rfl fun l _ =>
        Work.Diff.STE.ENormSq_zero (Work.Diff.STE.pdVec k l u)
    have hCS1 : (∑ l : Fin k → Fin n,
          |Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
            (Work.Diff.STE.pdVec k l u)|)
        ≤ Real.sqrt (card * (Cd * (S ^ 2 * (1 + KA + Q1)))) * rE := by
      have hper : ∀ l : Fin k → Fin n,
          |Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
            (Work.Diff.STE.pdVec k l u)|
            ≤ Real.sqrt (Work.Diff.STE.ENormSq 0 (fun z => Work.Diff.STE.pdVec k l w z - FL l z))
              * Real.sqrt (Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l u)) := by
        intro l
        have hint1 : MeasureTheory.Integrable
            (fun z : Fin n → ℝ => ‖(fun z => Work.Diff.STE.pdVec k l w z - FL l z) z‖ ^ 2)
            (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
          Work.Diff.STE.cm_integrableOn_unitCube_of_continuous
            (((hcw l).sub (hcF l)).norm.pow 2)
        have hint2 : MeasureTheory.Integrable
            (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec k l u z‖ ^ 2)
            (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
          Work.Diff.STE.cm_integrableOn_unitCube_of_continuous ((hcu l).norm.pow 2)
        have hcs := Work.Diff.STE.L2re_abs_le_sqrt
          (fun z => Work.Diff.STE.pdVec k l w z - FL l z) (Work.Diff.STE.pdVec k l u) hint1 hint2
        rw [Work.Diff.STE.ENormSq_zero, Work.Diff.STE.ENormSq_zero]
        exact hcs
      calc (∑ l : Fin k → Fin n,
            |Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
              (Work.Diff.STE.pdVec k l u)|)
          ≤ ∑ l : Fin k → Fin n,
              Real.sqrt (Work.Diff.STE.ENormSq 0 (fun z => Work.Diff.STE.pdVec k l w z - FL l z))
              * Real.sqrt (Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l u)) :=
            Finset.sum_le_sum fun l _ => hper l
        _ ≤ Real.sqrt (∑ l : Fin k → Fin n,
              Work.Diff.STE.ENormSq 0 (fun z => Work.Diff.STE.pdVec k l w z - FL l z))
            * Real.sqrt (∑ l : Fin k → Fin n,
              Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l u)) :=
            sum_sqrt_mul_sqrt_le _ _ (fun l => Work.Diff.STE.Lead.Gal.ENormSq_nonneg _)
              (fun l => Work.Diff.STE.Lead.Gal.ENormSq_nonneg _)
        _ = Real.sqrt (∑ l : Fin k → Fin n,
              Work.Diff.STE.ENormSq 0 (fun z => Work.Diff.STE.pdVec k l w z - FL l z)) * rE := by
            rw [hEsum]
        _ ≤ Real.sqrt (card * (Cd * (S ^ 2 * (1 + KA + Q1)))) * rE :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsumDl) hrE_nn
    have hsumTl : (∑ l : Fin k → Fin n, Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l Th))
        ≤ card * (CT * (1 + Q1)) := by
      calc (∑ l : Fin k → Fin n, Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l Th))
          ≤ ∑ _l : Fin k → Fin n, CT * (1 + Q1) := Finset.sum_le_sum fun l _ => hTh l
        _ = card * (CT * (1 + Q1)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcarddef]
    have hCS2 : (∑ l : Fin k → Fin n,
          |Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u)|)
        ≤ Real.sqrt (card * (CT * (1 + Q1))) * rE := by
      have hper : ∀ l : Fin k → Fin n,
          |Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u)|
            ≤ Real.sqrt (Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l Th))
              * Real.sqrt (Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l u)) := by
        intro l
        have hint1 : MeasureTheory.Integrable
            (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec k l Th z‖ ^ 2)
            (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
          Work.Diff.STE.cm_integrableOn_unitCube_of_continuous ((hcT l).norm.pow 2)
        have hint2 : MeasureTheory.Integrable
            (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec k l u z‖ ^ 2)
            (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n))) :=
          Work.Diff.STE.cm_integrableOn_unitCube_of_continuous ((hcu l).norm.pow 2)
        have hcs := Work.Diff.STE.L2re_abs_le_sqrt
          (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u) hint1 hint2
        rw [Work.Diff.STE.ENormSq_zero, Work.Diff.STE.ENormSq_zero]
        exact hcs
      calc (∑ l : Fin k → Fin n,
            |Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u)|)
          ≤ ∑ l : Fin k → Fin n,
              Real.sqrt (Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l Th))
              * Real.sqrt (Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l u)) :=
            Finset.sum_le_sum fun l _ => hper l
        _ ≤ Real.sqrt (∑ l : Fin k → Fin n, Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l Th))
            * Real.sqrt (∑ l : Fin k → Fin n,
              Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l u)) :=
            sum_sqrt_mul_sqrt_le _ _ (fun l => Work.Diff.STE.Lead.Gal.ENormSq_nonneg _)
              (fun l => Work.Diff.STE.Lead.Gal.ENormSq_nonneg _)
        _ = Real.sqrt (∑ l : Fin k → Fin n, Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec k l Th))
              * rE := by
            rw [hEsum]
        _ ≤ Real.sqrt (card * (CT * (1 + Q1))) * rE :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsumTl) hrE_nn
    -- ### assembly of the raw bound
    have hsum : (∑ l : Fin k → Fin n,
          Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v) (Work.Diff.STE.pdVec k l u))
        ≤ (∑ l : Fin k → Fin n, Work.Diff.STE.L2re (FL l) (Work.Diff.STE.pdVec k l u))
          + (∑ l : Fin k → Fin n,
              |Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
                (Work.Diff.STE.pdVec k l u)|)
          + (∑ l : Fin k → Fin n,
              |Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th) (Work.Diff.STE.pdVec k l u)|) := by
      calc (∑ l : Fin k → Fin n,
            Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v) (Work.Diff.STE.pdVec k l u))
          ≤ ∑ l : Fin k → Fin n,
              (Work.Diff.STE.L2re (FL l) (Work.Diff.STE.pdVec k l u)
                + |Work.Diff.STE.L2re (fun z => Work.Diff.STE.pdVec k l w z - FL l z)
                    (Work.Diff.STE.pdVec k l u)|
                + |Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l Th)
                    (Work.Diff.STE.pdVec k l u)|) :=
            Finset.sum_le_sum fun l _ => hstep l
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hFLsum : (∑ l : Fin k → Fin n, Work.Diff.STE.L2re (FL l) (Work.Diff.STE.pdVec k l u))
        = (∑ l : Fin k → Fin n, Work.Diff.STE.L2re
            (fun z => ∑ c, ∑ d, ((A c d z : ℝ) : ℂ) *
              Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)
            (Work.Diff.STE.pdVec k l u)) := rfl
    have hgard' : (∑ l : Fin k → Fin n, Work.Diff.STE.L2re (FL l) (Work.Diff.STE.pdVec k l u))
        ≤ -(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) u + F * Work.Diff.STE.ENormSq k u := by
      rw [hFLsum]; exact hgard
    have hbound : (∑ l : Fin k → Fin n,
          Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v) (Work.Diff.STE.pdVec k l u))
        ≤ (-(lamT / 2) * Work.Diff.STE.ENormSq (k + 1) u + F * Work.Diff.STE.ENormSq k u)
          + (Real.sqrt (card * (Cd * (S ^ 2 * (1 + KA + Q1)))) * rE
            + Real.sqrt (card * (CT * (1 + Q1))) * rE) := by
      linarith [hsum, hgard', hCS1, hCS2]
    -- ### the arithmetic: absorb the square-root terms
    have hAa_bound : Real.sqrt (card * (Cd * (S ^ 2 * (1 + KA + Q1))))
        ≤ g * (1 + Real.sqrt KA + Real.sqrt Q1) := by
      have hfact : card * (Cd * (S ^ 2 * (1 + KA + Q1)))
          = (card * (Cd * S ^ 2)) * (1 + KA + Q1) := by ring
      have hsq : Real.sqrt (card * (Cd * (S ^ 2 * (1 + KA + Q1))))
          = Real.sqrt (card * (Cd * S ^ 2)) * Real.sqrt (1 + KA + Q1) := by
        rw [hfact, Real.sqrt_mul (mul_nonneg hcard_nn (mul_nonneg hCd (sq_nonneg S)))]
      rw [hsq]
      have hs1 : Real.sqrt (1 + KA + Q1) ≤ 1 + Real.sqrt KA + Real.sqrt Q1 := by
        have h1 : Real.sqrt ((1 + KA) + Q1) ≤ Real.sqrt (1 + KA) + Real.sqrt Q1 :=
          sqrt_add_le (by linarith) hQ1
        have h2 : Real.sqrt (1 + KA) ≤ 1 + Real.sqrt KA := by
          have h := sqrt_add_le (show (0 : ℝ) ≤ 1 by norm_num) hKA
          rw [Real.sqrt_one] at h
          linarith
        linarith
      have hgle : Real.sqrt (card * (Cd * S ^ 2)) ≤ g := by
        rw [hgdef]; exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
      calc Real.sqrt (card * (Cd * S ^ 2)) * Real.sqrt (1 + KA + Q1)
          ≤ Real.sqrt (card * (Cd * S ^ 2)) * (1 + Real.sqrt KA + Real.sqrt Q1) :=
            mul_le_mul_of_nonneg_left hs1 (Real.sqrt_nonneg _)
        _ ≤ g * (1 + Real.sqrt KA + Real.sqrt Q1) :=
            mul_le_mul_of_nonneg_right hgle (by positivity)
    have hBb_bound : Real.sqrt (card * (CT * (1 + Q1))) ≤ g * (1 + Real.sqrt Q1) := by
      have hfact : card * (CT * (1 + Q1)) = (card * CT) * (1 + Q1) := by ring
      have hsq : Real.sqrt (card * (CT * (1 + Q1)))
          = Real.sqrt (card * CT) * Real.sqrt (1 + Q1) := by
        rw [hfact, Real.sqrt_mul (mul_nonneg hcard_nn hCT)]
      rw [hsq]
      have hs2 : Real.sqrt (1 + Q1) ≤ 1 + Real.sqrt Q1 := by
        have h := sqrt_add_le (show (0 : ℝ) ≤ 1 by norm_num) hQ1
        rw [Real.sqrt_one] at h
        linarith
      have hgle : Real.sqrt (card * CT) ≤ g := by
        rw [hgdef]; exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
      calc Real.sqrt (card * CT) * Real.sqrt (1 + Q1)
          ≤ Real.sqrt (card * CT) * (1 + Real.sqrt Q1) :=
            mul_le_mul_of_nonneg_left hs2 (Real.sqrt_nonneg _)
        _ ≤ g * (1 + Real.sqrt Q1) :=
            mul_le_mul_of_nonneg_right hgle (by positivity)
    have hExtra : Real.sqrt (card * (Cd * (S ^ 2 * (1 + KA + Q1)))) * rE
        + Real.sqrt (card * (CT * (1 + Q1))) * rE
        ≤ 2 * g * (1 + Real.sqrt KA + Real.sqrt Q1) * rE := by
      have hsum2 : Real.sqrt (card * (Cd * (S ^ 2 * (1 + KA + Q1))))
          + Real.sqrt (card * (CT * (1 + Q1))) ≤ 2 * g * (1 + Real.sqrt KA + Real.sqrt Q1) := by
        have hb2 : g * (1 + Real.sqrt Q1) ≤ g * (1 + Real.sqrt KA + Real.sqrt Q1) :=
          mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg KA]) hg_nn
        linarith [hAa_bound, hBb_bound, hb2]
      calc Real.sqrt (card * (Cd * (S ^ 2 * (1 + KA + Q1)))) * rE
            + Real.sqrt (card * (CT * (1 + Q1))) * rE
          = (Real.sqrt (card * (Cd * (S ^ 2 * (1 + KA + Q1))))
              + Real.sqrt (card * (CT * (1 + Q1)))) * rE := by ring
        _ ≤ (2 * g * (1 + Real.sqrt KA + Real.sqrt Q1)) * rE :=
            mul_le_mul_of_nonneg_right hsum2 hrE_nn
    have hTotal : 2 * g * (1 + Real.sqrt KA + Real.sqrt Q1) * rE
        ≤ 2 * g * (1 + Work.Diff.STE.ENormSq k u) + g * (KA + Work.Diff.STE.ENormSq k u)
          + g * γ * Q1 + (g / γ) * Work.Diff.STE.ENormSq k u := by
      have hExp : 2 * g * (1 + Real.sqrt KA + Real.sqrt Q1) * rE
          = 2 * g * rE + 2 * g * (Real.sqrt KA * rE) + 2 * g * (Real.sqrt Q1 * rE) := by ring
      rw [hExp]
      have h1 : 2 * g * rE ≤ 2 * g * (1 + Work.Diff.STE.ENormSq k u) :=
        mul_le_mul_of_nonneg_left (Work.Diff.STE.Lead.Gal.sqrt_le_one_add hE_nn) (by positivity)
      have h2 : 2 * g * (Real.sqrt KA * rE) ≤ g * (KA + Work.Diff.STE.ENormSq k u) := by
        calc 2 * g * (Real.sqrt KA * rE)
            ≤ 2 * g * ((KA + Work.Diff.STE.ENormSq k u) / 2) :=
              mul_le_mul_of_nonneg_left
                (Work.Diff.STE.Lead.Gal.sqrt_mul_sqrt_le hKA hE_nn) (by positivity)
          _ = g * (KA + Work.Diff.STE.ENormSq k u) := by ring
      have h3 : 2 * g * (Real.sqrt Q1 * rE)
          ≤ g * γ * Q1 + (g / γ) * Work.Diff.STE.ENormSq k u := by
        have hr : Real.sqrt Q1 * rE = Real.sqrt (Q1 * Work.Diff.STE.ENormSq k u) := by
          rw [hrE_eq]; exact (Real.sqrt_mul hQ1 _).symm
        rw [hr]
        calc 2 * g * Real.sqrt (Q1 * Work.Diff.STE.ENormSq k u)
            ≤ 2 * g * ((γ * Q1 + Work.Diff.STE.ENormSq k u / γ) / 2) :=
              mul_le_mul_of_nonneg_left
                (sqrt_mul_le_amgm (a := Q1) (b := Work.Diff.STE.ENormSq k u) hQ1 hE_nn hγ_pos)
                (by positivity)
          _ = g * γ * Q1 + (g / γ) * Work.Diff.STE.ENormSq k u := by ring
      linarith [h1, h2, h3]
    -- ### the `Q1` coefficient
    have hgγ : g * γ ≤ 2 * e * card := by
      rcases Nat.eq_zero_or_pos (Fintype.card (Fin k → Fin n)) with hc0 | hcpos
      · have hcard0 : card = 0 := by rw [hcarddef]; simp [hc0]
        have hg0 : g = 0 := by rw [hgdef, hcard0]; simp
        rw [hg0, hcard0]; simp
      · have hcard1 : (1 : ℝ) ≤ card := by
          rw [hcarddef]; exact_mod_cast hcpos
        have h1 : g * γ = 2 * e * (g / (g + 1)) := by rw [hγdef]; ring
        have h2 : g / (g + 1) ≤ 1 := by
          rw [div_le_one (by linarith : (0 : ℝ) < g + 1)]
          linarith
        have h3 : 2 * e * (g / (g + 1)) ≤ 2 * e := by
          have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * e)
          simpa using this
        have h4 : 2 * e ≤ 2 * e * card := by
          have := mul_le_mul_of_nonneg_left hcard1 (by linarith : (0 : ℝ) ≤ 2 * e)
          simpa using this
        linarith [h1, h3, h4]
    have hQ1c : g * γ * Q1 ≤ card * (2 * e) * Q1 := by
      have h := mul_le_mul_of_nonneg_right hgγ hQ1
      linarith [h]
    -- ### final arithmetic
    have hkey : F * Work.Diff.STE.ENormSq k u
          + (Real.sqrt (card * (Cd * (S ^ 2 * (1 + KA + Q1)))) * rE
            + Real.sqrt (card * (CT * (1 + Q1))) * rE)
        ≤ (F + 3 * g + g / γ + 1) * (1 + Work.Diff.STE.ENormSq k u + KA)
          + card * (2 * e) * Q1 := by
      have hFE : F * Work.Diff.STE.ENormSq k u
          ≤ F * (1 + Work.Diff.STE.ENormSq k u + KA) :=
        mul_le_mul_of_nonneg_left (by linarith) hF
      have hmain : Real.sqrt (card * (Cd * (S ^ 2 * (1 + KA + Q1)))) * rE
            + Real.sqrt (card * (CT * (1 + Q1))) * rE
          ≤ (3 * g + g / γ) * (1 + Work.Diff.STE.ENormSq k u + KA) + card * (2 * e) * Q1 := by
        have h1 : 2 * g * (1 + Work.Diff.STE.ENormSq k u)
            ≤ 2 * g * (1 + Work.Diff.STE.ENormSq k u + KA) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith : (0 : ℝ) ≤ 2 * g)
        have h2 : g * (KA + Work.Diff.STE.ENormSq k u)
            ≤ g * (1 + Work.Diff.STE.ENormSq k u + KA) :=
          mul_le_mul_of_nonneg_left (by linarith) hg_nn
        have h3 : (g / γ) * Work.Diff.STE.ENormSq k u
            ≤ (g / γ) * (1 + Work.Diff.STE.ENormSq k u + KA) :=
          mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hg_nn hγ_pos.le)
        have hid1 : 2 * g * (1 + Work.Diff.STE.ENormSq k u + KA)
              + g * (1 + Work.Diff.STE.ENormSq k u + KA)
              + (g / γ) * (1 + Work.Diff.STE.ENormSq k u + KA)
            = (3 * g + g / γ) * (1 + Work.Diff.STE.ENormSq k u + KA) := by ring
        linarith [hExtra, hTotal, h1, h2, h3, hQ1c, hid1]
      have hprod : (F + 3 * g + g / γ) * (1 + Work.Diff.STE.ENormSq k u + KA)
          ≤ (F + 3 * g + g / γ + 1) * (1 + Work.Diff.STE.ENormSq k u + KA) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith [hE_nn, hKA])
      linarith [hFE, hmain, hprod]
    linarith [hbound, hkey]

end

end Work.Diff.STE.Lead.GalTame
