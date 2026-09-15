import Submission.FUP.LocalizeZplaneSum2
import Submission.Commons.Analysis.Measure.tsum_ennreal_rpow_mul_le
import Submission.Commons.Analysis.Measure.lattice_box_cover
import Submission.Commons.Analysis.Measure.tsum_lintegral_cubes_eq

open MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The single-scale localisation in the form of Han–Schlag's `prop:locddim`

Assembles `cell_zplane` (per cell) and `sup_sum_le` (sum over the lattice) with Hölder's
inequality into the global localisation estimate.
-/

namespace Submission.FUP

variable {d : ℕ}

/-- The closed unit box of the `2ℤ^d` lattice with index `n` (translate `γ`). -/
def cellTile (γ : Fin d → ℝ) (n : Fin d → ℤ) : Set (Fin d → ℝ) :=
  {x | ∀ i, |x i - (2 * (n i : ℝ) + γ i + 1)| ≤ 1}

lemma isCompact_cellTile (γ : Fin d → ℝ) (n : Fin d → ℤ) : IsCompact (cellTile γ n) := by
  have h : cellTile γ n = Set.pi Set.univ (fun i : Fin d =>
      Set.Icc ((2 * (n i : ℝ) + γ i + 1) - 1) ((2 * (n i : ℝ) + γ i + 1) + 1)) := by
    ext x
    simp only [cellTile, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    constructor
    · intro h i
      have h2 := abs_le.mp (h i)
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    · intro h i
      exact abs_le.mpr ⟨by linarith [(h i).1], by linarith [(h i).2]⟩
  rw [h]
  exact isCompact_univ_pi (fun i => isCompact_Icc)

lemma measurableSet_cellTile (γ : Fin d → ℝ) (n : Fin d → ℤ) : MeasurableSet (cellTile γ n) := by
  rw [show cellTile γ n = ⋂ i,
      {x : Fin d → ℝ | |x i - (2 * (n i : ℝ) + γ i + 1)| ≤ 1} from by
    ext x; simp [cellTile]]
  exact MeasurableSet.iInter (fun i => measurableSet_le
    ((measurable_pi_apply i).sub measurable_const).abs measurable_const)

lemma cellTile_subset_PsiR {q ε η δ : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hη0 : 0 < η) (hδ0 : 0 < δ) (hδ3 : δ < 1/3) (hητ : 1 ≤ η * phiLens q ε (1 - 3 * δ))
    {γ : Fin d → ℝ} (n : Fin d → ℤ) :
    cellTile γ n ⊆ PsiR (d := d) q ε η (cellCentre γ n) '' cbox d (1 - 3*δ) := by
  intro x hx
  rw [PsiR_image_cbox hq hε0 hε1 (by linarith) (by linarith) (by linarith) (cellCentre γ n)]
  intro j
  have h1 : |x j - cellCentre γ n j| ≤ 1 := hx j
  have h2 : (1:ℝ) ≤ η * phiLens q ε (1 - 3*δ) := hητ
  calc |x j - cellCentre γ n j| ≤ 1 := h1
    _ ≤ η * phiLens q ε (1 - 3 * δ) := h2

-- NOTE (Session 59): the theorem `localization_entire` is the next step; see
-- Submission/FUP/ROADMAP.md, Session 59 (final) §"THE next step" for its exact statement and
-- proof plan (all the analytic and measure-theoretic inputs are already proved).

/-- **The `d`-dimensional localisation estimate (Han–Schlag's `prop:locddim`).**

`F` is an entire function, `g x = F (x : ℂ^d)` its restriction to `ℝ^d`, and `a` chooses one cube
`I_n = ∏ᵢ [a n ᵢ, a n ᵢ + 2c₁]` of side `2c₁` in each cell `2n + γ + [-1,1]^d` of the lattice.
Then, with `κ = zpKappa δ H d`,

`∫ ‖g‖² ≤ C₀ · (D · ∫⁻_strip ‖F‖²)^{1-κ} · (∫⁻_{⋃ I_n} ‖g‖²)^κ`,

where `D = (η φ(1) + r + 1)^d ((πr²)^d)⁻¹` and `C₀ = cellZConst q ε δ H η c₁ d` is independent of
the band limit — which is what makes the estimate strong enough for Han–Schlag's §4. -/
theorem localization_entire {q ε δ H η c₁ r : ℝ} {γ : Fin d → ℝ}
    (hd : 1 ≤ d) (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3) (hH0 : 0 < H) (hH1 : H ≤ 1)
    (hη0 : 0 < η) (hc₁ : 0 < c₁) (hr0 : 0 < r)
    (hητ : 1 ≤ η * phiLens q ε (1 - 3 * δ))
    (hIbig : ENNReal.ofReal ((η * zpLamMax q ε) ^ d * (2 * (20 ^ d * H)))
      ≤ ENNReal.ofReal ((2 * c₁) ^ d))
    {F : (Fin d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ)
    (a : (Fin d → ℤ) → Fin d → ℝ)
    (ha : ∀ n : Fin d → ℤ, ∀ i : Fin d,
      2 * (n i : ℝ) + γ i ≤ a n i ∧ a n i + 2 * c₁ ≤ 2 * (n i : ℝ) + γ i + 2) :
    ∫⁻ x : Fin d → ℝ, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
      ≤ ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
        * (ENNReal.ofReal ((η * phiLens q ε 1 + r + 1) ^ d * ((Real.pi * r ^ 2) ^ d)⁻¹)
          * ∫⁻ z in {z : Fin d → ℂ | ∀ i, |(z i).im| ≤ η * q + r}, ENNReal.ofReal (‖F z‖ ^ 2))
          ^ (1 - zpKappa δ H d)
        * (∫⁻ x in ⋃ n : Fin d → ℤ,
              Set.pi Set.univ (fun i => Set.Icc (a n i) (a n i + 2 * c₁)),
              ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)) ^ (zpKappa δ H d) := by
  classical
  -- ### abbreviations
  set κ : ℝ := zpKappa δ H d with hκ
  set J : ℝ≥0∞ :=
    ∫⁻ z in {z : Fin d → ℂ | ∀ i, |(z i).im| ≤ η * q + r}, ENNReal.ofReal (‖F z‖ ^ 2) with hJ
  set D : ℝ := (η * phiLens q ε 1 + r + 1) ^ d * ((Real.pi * r ^ 2) ^ d)⁻¹ with hD
  set A : ℝ≥0∞ :=
    ∫⁻ x in ⋃ n : Fin d → ℤ, Set.pi Set.univ (fun i => Set.Icc (a n i) (a n i + 2 * c₁)),
      ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2) with hA
  set S : (Fin d → ℤ) → ℝ := fun n => sSup ((fun z : Fin d → ℂ =>
      ‖F (PsiCLens q ε η (cellCentre γ n) z)‖) '' Metric.closedBall 0 1) with hS
  set an : (Fin d → ℤ) → ℝ := fun n =>
    ∫ y in Set.pi Set.univ (fun i => Set.Icc (a n i) (a n i + 2 * c₁)),
      ‖F (fun i => (y i : ℂ))‖ ^ 2 with han
  -- ### basic facts
  have hε1' : ε < 1 := by linarith
  have hτ0 : 0 ≤ 1 - 3 * δ := by linarith
  have hτ1 : 1 - 3 * δ < 1 := by linarith
  have hFdiff : Differentiable ℂ F := differentiableOn_univ.mp hF.differentiableOn
  have hFcont : Continuous F := hFdiff.continuous
  have hcont : Continuous (fun y : Fin d → ℝ => ‖F (fun i => (y i : ℂ))‖ ^ 2) :=
    (hFcont.comp (continuous_pi (fun i =>
      Complex.continuous_ofReal.comp (continuous_apply i)))).norm.pow 2
  obtain ⟨hκp0, hκp1⟩ := twoConstKappa_mem hδ0 hδ3 hH0 hH1
  have hκ0 : 0 < κ := by rw [hκ, zpKappa]; exact pow_pos hκp0 d
  have hκ1 : κ ≤ 1 := by rw [hκ, zpKappa]; exact pow_le_one₀ hκp0.le hκp1
  have hκ1' : 0 ≤ 1 - κ := by linarith
  have hC0pos : 0 < cellZConst q ε δ H η c₁ d :=
    cellZConst_pos q ε δ H η c₁ d hδ0 hδ3 hq hε0 hε1 hη0 hc₁
  -- ### step 1: subadditivity over the lattice tiles
  have hstep1 : ∫⁻ x : Fin d → ℝ, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
      ≤ ∑' n : Fin d → ℤ,
          ∫⁻ x in cellTile γ n, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2) := by
    have hcov : (⋃ n : Fin d → ℤ, cellTile γ n) = Set.univ := by
      rw [← Commons.Analysis.Measure.lattice_box_cover γ]
      rfl
    calc ∫⁻ x : Fin d → ℝ, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
        = ∫⁻ x in (⋃ n : Fin d → ℤ, cellTile γ n),
            ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2) := by
          rw [hcov, Measure.restrict_univ]
      _ ≤ ∑' n : Fin d → ℤ,
            ∫⁻ x in cellTile γ n, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2) :=
          lintegral_iUnion_le _ _
  -- ### step 2: the per-cell estimate
  have hstep2 : ∀ n : Fin d → ℤ,
      ∫⁻ x in cellTile γ n, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
        ≤ ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
            * (ENNReal.ofReal ((S n) ^ 2)) ^ (1 - κ)
            * (ENNReal.ofReal (an n)) ^ κ := by
    intro n
    have hSrfl : sSup ((fun z : Fin d → ℂ =>
        ‖F (PsiCLens q ε η (cellCentre γ n) z)‖) '' Metric.closedBall 0 1) = S n := rfl
    have hanrfl : (∫ y in Set.pi Set.univ (fun i => Set.Icc (a n i) (a n i + 2 * c₁)),
        ‖F (fun i => (y i : ℂ))‖ ^ 2) = an n := rfl
    have hSnn : 0 ≤ S n := by
      rw [← hSrfl]
      exact Real.sSup_nonneg (fun x hx => by
        rcases hx with ⟨z, hz, rfl⟩; exact norm_nonneg _)
    have hannn : 0 ≤ an n := by
      rw [← hanrfl]
      exact integral_nonneg (fun y => by positivity)
    -- (a) shrink the domain of integration to the lens image
    have hsub := cellTile_subset_PsiR (d := d) (γ := γ) hq hε0 hε1' hη0 hδ0 hδ3 hητ n
    have ha1 : ∫⁻ x in cellTile γ n, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
        ≤ ∫⁻ x in PsiR (d := d) q ε η (cellCentre γ n) '' cbox d (1 - 3 * δ),
              ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2) :=
      lintegral_mono_set hsub
    -- (b) convert the `lintegral` to a Bochner integral
    have hcomp : IsCompact {y : Fin d → ℝ |
        ∀ j : Fin d, |y j - cellCentre γ n j| ≤ η * phiLens q ε (1 - 3 * δ)} := by
      have heq : {y : Fin d → ℝ |
            ∀ j : Fin d, |y j - cellCentre γ n j| ≤ η * phiLens q ε (1 - 3 * δ)}
          = Set.pi Set.univ (fun j : Fin d =>
              Set.Icc (cellCentre γ n j - η * phiLens q ε (1 - 3 * δ))
                (cellCentre γ n j + η * phiLens q ε (1 - 3 * δ))) := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
        constructor
        · intro h j
          exact (abs_le.mp (h j)).imp (fun a => by linarith) (fun b => by linarith)
        · intro h j
          exact abs_le.mpr ⟨by linarith [(h j).1], by linarith [(h j).2]⟩
      rw [heq]
      exact isCompact_univ_pi (fun j => isCompact_Icc)
    have hInt : IntegrableOn (fun y : Fin d → ℝ => ‖F (fun i => (y i : ℂ))‖ ^ 2)
        (PsiR (d := d) q ε η (cellCentre γ n) '' cbox d (1 - 3 * δ)) volume := by
      refine (hcont.continuousOn.integrableOn_compact hcomp).mono_set ?_
      rw [PsiR_image_cbox (d := d) hq hε0 hε1' hη0 hτ0 hτ1 (cellCentre γ n)]
    have ha2 : ∫⁻ x in PsiR (d := d) q ε η (cellCentre γ n) '' cbox d (1 - 3 * δ),
          ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
        = ENNReal.ofReal (∫ y in PsiR (d := d) q ε η (cellCentre γ n) '' cbox d (1 - 3 * δ),
            ‖F (fun i => (y i : ℂ))‖ ^ 2) :=
      (ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ (fun y => by positivity))).symm
    -- (c) the per-cell Cartan estimate
    have hc₁le : c₁ ≤ 1 := by
      have h := ha (fun _ => (0 : ℤ)) ⟨0, by omega⟩
      have h1 : γ ⟨0, by omega⟩ ≤ a (fun _ => (0 : ℤ)) ⟨0, by omega⟩ := by simpa using h.1
      have h2 : a (fun _ => (0 : ℤ)) ⟨0, by omega⟩ + 2 * c₁
          ≤ γ ⟨0, by omega⟩ + 2 := by simpa using h.2
      linarith
    have hl : ∀ j : Fin d, |(a n j + c₁) - cellCentre γ n j| ≤ 1 - c₁ := by
      intro j
      have h := ha n j
      simp only [cellCentre]
      rw [abs_le]
      constructor <;> linarith [h.1, h.2]
    have hbig : ENNReal.ofReal ((η * zpLamMax q ε) ^ d * (2 * (20 ^ d * H)))
        ≤ volume (Set.pi Set.univ (fun j : Fin d =>
            Set.Icc ((a n j + c₁) - c₁) ((a n j + c₁) + c₁))) := by
      rw [volume_Icube (fun j => a n j + c₁) hc₁.le]
      exact hIbig
    have hcz := cell_zplane (d := d) (F := F) hq hε0 hε1 hδ0 hδ3 hH0 hH1 hη0 hητ hd hF
      (l := fun j => a n j + c₁) hc₁ hl hbig
    have hIeq : (fun j : Fin d => Set.Icc ((a n j + c₁) - c₁) ((a n j + c₁) + c₁))
        = fun j : Fin d => Set.Icc (a n j) (a n j + 2 * c₁) := by
      funext j
      congr 1 <;> ring
    rw [hIeq] at hcz
    have ha3 : ∫ y in PsiR (d := d) q ε η (cellCentre γ n) '' cbox d (1 - 3 * δ),
          ‖F (fun i => (y i : ℂ))‖ ^ 2
        ≤ cellZConst q ε δ H η c₁ d * (S n) ^ (2 * (1 - κ)) * (an n) ^ κ := by
      rw [hSrfl, hanrfl] at hcz
      exact hcz
    -- (d) the `ENNReal` algebra
    have ha4 : ENNReal.ofReal (∫ y in PsiR (d := d) q ε η (cellCentre γ n) '' cbox d (1 - 3 * δ),
          ‖F (fun i => (y i : ℂ))‖ ^ 2)
        ≤ ENNReal.ofReal (cellZConst q ε δ H η c₁ d * (S n) ^ (2 * (1 - κ)) * (an n) ^ κ) :=
      ENNReal.ofReal_le_ofReal ha3
    have ha5 : ENNReal.ofReal (cellZConst q ε δ H η c₁ d * (S n) ^ (2 * (1 - κ))
          * (an n) ^ κ)
        = ENNReal.ofReal (cellZConst q ε δ H η c₁ d) * (ENNReal.ofReal ((S n) ^ 2)) ^ (1 - κ)
            * (ENNReal.ofReal (an n)) ^ κ := by
      have hSconv : ENNReal.ofReal ((S n) ^ (2 * (1 - κ)))
          = (ENNReal.ofReal ((S n) ^ 2)) ^ (1 - κ) := by
        have h1 : (S n) ^ (2 * (1 - κ)) = ((S n) ^ 2) ^ (1 - κ) := by
          rw [Real.rpow_mul hSnn (2 : ℝ) (1 - κ)]
          congr 1
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast (S n) 2]
        rw [h1, ← ENNReal.ofReal_rpow_of_nonneg (x := (S n) ^ 2) (p := 1 - κ)
          (by positivity) hκ1']
      have hanconv : ENNReal.ofReal ((an n) ^ κ) = (ENNReal.ofReal (an n)) ^ κ :=
        (ENNReal.ofReal_rpow_of_nonneg hannn hκ0.le).symm
      rw [ENNReal.ofReal_mul (mul_nonneg hC0pos.le (Real.rpow_nonneg hSnn _)),
          ENNReal.ofReal_mul hC0pos.le, hSconv, hanconv]
    exact (ha1.trans ha2.le).trans (ha4.trans ha5.le)
  -- ### step 3: Hölder over the lattice
  have hstep3 : ∑' n : Fin d → ℤ,
        ∫⁻ x in cellTile γ n, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
      ≤ ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
        * ((∑' n : Fin d → ℤ, ENNReal.ofReal ((S n) ^ 2)) ^ (1 - κ)
            * (∑' n : Fin d → ℤ, ENNReal.ofReal (an n)) ^ κ) := by
    have hcongr : (fun n : Fin d → ℤ => ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
          * (ENNReal.ofReal ((S n) ^ 2)) ^ (1 - κ) * (ENNReal.ofReal (an n)) ^ κ)
        = fun n : Fin d → ℤ => ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
          * ((ENNReal.ofReal ((S n) ^ 2)) ^ (1 - κ) * (ENNReal.ofReal (an n)) ^ κ) :=
      funext fun n => mul_assoc _ _ _
    calc ∑' n : Fin d → ℤ,
          ∫⁻ x in cellTile γ n, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
        ≤ ∑' n : Fin d → ℤ, (ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
            * (ENNReal.ofReal ((S n) ^ 2)) ^ (1 - κ)
            * (ENNReal.ofReal (an n)) ^ κ) := ENNReal.tsum_le_tsum hstep2
      _ = ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
            * ∑' n : Fin d → ℤ, ((ENNReal.ofReal ((S n) ^ 2)) ^ (1 - κ)
                * (ENNReal.ofReal (an n)) ^ κ) := by
          rw [hcongr, ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
            * ((∑' n : Fin d → ℤ, ENNReal.ofReal ((S n) ^ 2)) ^ (1 - κ)
                * (∑' n : Fin d → ℤ, ENNReal.ofReal (an n)) ^ κ) := by
          refine mul_le_mul_of_nonneg_left ?_ (bot_le : (0 : ℝ≥0∞) ≤ _)
          exact Commons.Analysis.Measure.tsum_ennreal_rpow_mul_le _ _ hκ0 hκ1
  -- ### step 4: the sup-sums are controlled by the strip integral
  have hstep4 : ∑' n : Fin d → ℤ, ENNReal.ofReal ((S n) ^ 2) ≤ ENNReal.ofReal D * J := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun s => ?_)
    have h := sup_sum_le (d := d) (q := q) (ε := ε) (η := η) (r := r) (γ := γ)
      hq hε0 hε1 hη0 hr0 hFdiff s
    have heq : (∑ n ∈ s, ENNReal.ofReal ((S n) ^ 2))
        = ∑ n ∈ s, ENNReal.ofReal (sSup ((fun z : Fin d → ℂ =>
            ‖F (PsiCLens q ε η (cellCentre γ n) z)‖) '' Metric.closedBall 0 1) ^ 2) :=
      Finset.sum_congr rfl (fun n _ => by
        rw [show S n = sSup ((fun z : Fin d → ℂ =>
          ‖F (PsiCLens q ε η (cellCentre γ n) z)‖) '' Metric.closedBall 0 1) from rfl])
    refine heq.trans_le ?_
    refine h.trans_eq ?_
    have hAnn : (0 : ℝ) ≤ (η * phiLens q ε 1 + r + 1) ^ d :=
      pow_nonneg (by
        have := phiLens_one_pos (q := q) (ε := ε) hq hε0 hε1'
        nlinarith [hη0, this, hr0]) d
    rw [hD, ENNReal.ofReal_mul hAnn]
    ring
  -- ### step 5: the cubes are essentially disjoint
  have hstep5 : ∑' n : Fin d → ℤ, ENNReal.ofReal (an n) = A := by
    have hper : ∀ n : Fin d → ℤ, ENNReal.ofReal (an n)
        = ∫⁻ x in Set.pi Set.univ (fun i => Set.Icc (a n i) (a n i + 2 * c₁)),
            ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2) := by
      intro n
      have hIntn : IntegrableOn (fun y : Fin d → ℝ => ‖F (fun i => (y i : ℂ))‖ ^ 2)
          (Set.pi Set.univ (fun i => Set.Icc (a n i) (a n i + 2 * c₁))) volume :=
        hcont.continuousOn.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))
      have han' : (∫ y in Set.pi Set.univ (fun i => Set.Icc (a n i) (a n i + 2 * c₁)),
          ‖F (fun i => (y i : ℂ))‖ ^ 2) = an n := rfl
      rw [← han']
      exact ofReal_integral_eq_lintegral_ofReal hIntn (ae_of_all _ (fun y => by positivity))
    rw [tsum_congr hper, Commons.Analysis.Measure.tsum_lintegral_cubes_eq hc₁.le γ a ha]
  -- ### final assembly
  calc ∫⁻ x : Fin d → ℝ, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2)
      ≤ ∑' n : Fin d → ℤ,
          ∫⁻ x in cellTile γ n, ENNReal.ofReal (‖F (fun i => (x i : ℂ))‖ ^ 2) := hstep1
    _ ≤ ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
          * ((∑' n : Fin d → ℤ, ENNReal.ofReal ((S n) ^ 2)) ^ (1 - κ)
              * (∑' n : Fin d → ℤ, ENNReal.ofReal (an n)) ^ κ) := hstep3
    _ ≤ ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
          * ((ENNReal.ofReal D * J) ^ (1 - κ) * A ^ κ) := by
        refine mul_le_mul_of_nonneg_left ?_ (bot_le : (0 : ℝ≥0∞) ≤ _)
        refine mul_le_mul' (ENNReal.rpow_le_rpow hstep4 hκ1') ?_
        rw [hstep5]
    _ = ENNReal.ofReal (cellZConst q ε δ H η c₁ d)
          * (ENNReal.ofReal (D) * J) ^ (1 - κ) * A ^ κ := by
        rw [mul_assoc]

end Submission.FUP
