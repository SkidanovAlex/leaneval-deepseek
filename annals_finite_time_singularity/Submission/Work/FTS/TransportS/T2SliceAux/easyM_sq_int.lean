import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.H2.HeasyBlocksId
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.TransportS.GoodOpenBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2SliceAux

set_option autoImplicit false

/-! ## Elementary helpers

Nothing here is specific to the problem: `esq_integrableOn_of_bound` is the standard
"dominated by an integrable function on the open interval, continuous there" criterion for
`IntegrableOn · Iθ` (the endpoints `{0, π/2}` are null), and the two closure lemmas for
`IntegrableOn` package the `const_mul` / finite-sum operations. -/

/-- `sin (2θ) > 0` on the open angular interval. -/
theorem esq_sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The endpoints of `Iθ = [0, π/2]` do not contribute: `θ` lies in the open interval a.e. -/
theorem esq_ae_mem_Ioo : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- A function continuous on the open angular interval and dominated there by an integrable
function is integrable on the slice. -/
theorem esq_integrableOn_of_bound {F H : ℝ → ℝ}
    (hH : MeasureTheory.IntegrableOn H Work.Spaces.Iθ)
    (hF : ContinuousOn F (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ‖F θ‖ ≤ H θ) :
    MeasureTheory.IntegrableOn F Work.Spaces.Iθ :=
  hH.mono' (Work.H2.T1Q.aesm_Iθ_of_continuousOn hF)
    (by filter_upwards [esq_ae_mem_Ioo] with θ hθ; exact h θ hθ)

/-- Left multiplication by a constant preserves slice integrability. -/
theorem esq_integrableOn_const_mul {c : ℝ} {F : ℝ → ℝ}
    (h : MeasureTheory.IntegrableOn F Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => c * F θ) Work.Spaces.Iθ := by
  show MeasureTheory.Integrable (fun θ => c * F θ) (volume.restrict Work.Spaces.Iθ)
  exact (show MeasureTheory.Integrable F (volume.restrict Work.Spaces.Iθ) from h).const_mul c

/-- A finite sum of slice-integrable functions is slice-integrable. -/
theorem esq_integrableOn_finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, MeasureTheory.IntegrableOn (F i) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => ∑ i ∈ s, F i θ) Work.Spaces.Iθ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (MeasureTheory.integrableOn_zero (μ := volume) (s := Work.Spaces.Iθ))
  | insert a s ha ih =>
      have h1 : MeasureTheory.IntegrableOn (F a) Work.Spaces.Iθ :=
        h a (Finset.mem_insert_self a s)
      have h2 : MeasureTheory.IntegrableOn (fun θ => ∑ i ∈ s, F i θ) Work.Spaces.Iθ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have h3 := h1.add h2
      have : (fun θ => ∑ i ∈ insert a s, F i θ) = (F a) + (fun θ => ∑ i ∈ s, F i θ) := by
        funext θ; rw [Finset.sum_insert ha]; rfl
      rw [this]
      exact h3

/-! ## The AM–GM step: one bounded factor against one weighted `L²` slot -/

/-- **One bounded factor.**  If the `sin(2θ)^{-p}`-weighted square of `B` is integrable on the
slice and `|A| ≤ K` on the open interval, then the weighted square of the product is integrable
(the dominating function is the constant multiple `K² B² sin(2θ)^{-p}`). -/
theorem esq_bdd_mul_sin_integrable {A B : ℝ → ℝ} {p K : ℝ}
    (hB : MeasureTheory.IntegrableOn (fun θ => B θ ^ 2 * (Real.sin (2 * θ)) ^ (-p))
      Work.Spaces.Iθ)
    (hAc : ContinuousOn A (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hBc : ContinuousOn B (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hA : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |A θ| ≤ K) (hK : 0 ≤ K) :
    MeasureTheory.IntegrableOn
      (fun θ => A θ ^ 2 * B θ ^ 2 * (Real.sin (2 * θ)) ^ (-p)) Work.Spaces.Iθ := by
  have hbase : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
  have hrp : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-p))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hbase.continuousOn.rpow_const (fun θ hθ => Or.inl (ne_of_gt (esq_sin_two_pos hθ)))
  refine esq_integrableOn_of_bound
    (H := fun θ => K ^ 2 * (B θ ^ 2 * (Real.sin (2 * θ)) ^ (-p)))
    (esq_integrableOn_const_mul (c := K ^ 2) hB) ?_ ?_
  · exact ((hAc.pow 2).mul (hBc.pow 2)).mul hrp
  · intro θ hθ
    have hs0 : 0 ≤ (Real.sin (2 * θ)) ^ (-p) := Real.rpow_nonneg (esq_sin_two_pos hθ).le _
    have hB2 : 0 ≤ B θ ^ 2 * (Real.sin (2 * θ)) ^ (-p) := mul_nonneg (sq_nonneg _) hs0
    have hA2 : A θ ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs (A θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hA θ hθ) 2
    have hAB : 0 ≤ A θ ^ 2 * B θ ^ 2 * (Real.sin (2 * θ)) ^ (-p) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hs0
    rw [Real.norm_of_nonneg hAB]
    calc A θ ^ 2 * B θ ^ 2 * (Real.sin (2 * θ)) ^ (-p)
        = A θ ^ 2 * (B θ ^ 2 * (Real.sin (2 * θ)) ^ (-p)) := by ring
      _ ≤ K ^ 2 * (B θ ^ 2 * (Real.sin (2 * θ)) ^ (-p)) :=
          mul_le_mul_of_nonneg_right hA2 hB2

/-- The same statement with the two factors exchanged (so that the bounded factor can be
written second). -/
theorem esq_bdd_mul_sin_integrable' {A B : ℝ → ℝ} {p K : ℝ}
    (hB : MeasureTheory.IntegrableOn (fun θ => B θ ^ 2 * (Real.sin (2 * θ)) ^ (-p))
      Work.Spaces.Iθ)
    (hAc : ContinuousOn A (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hBc : ContinuousOn B (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hA : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |A θ| ≤ K) (hK : 0 ≤ K) :
    MeasureTheory.IntegrableOn
      (fun θ => B θ ^ 2 * A θ ^ 2 * (Real.sin (2 * θ)) ^ (-p)) Work.Spaces.Iθ :=
  (esq_bdd_mul_sin_integrable hB hAc hBc hA hK).congr_fun
    (fun θ _ => by ring) measurableSet_Icc

/-! ## The expanded mixed block of `Heasy` -/

/-- A single Leibniz summand of `D_z^jD_θ^i(f·D_zg)`. -/
def EasyMZ (f g : ℝ → ℝ → ℝ) (j i a b : ℕ) (z θ : ℝ) : ℝ :=
  ((i.choose a : ℝ) * (j.choose b : ℝ))
    * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b + 1) (i - a) g z θ)

/-- The Leibniz expansion of `D_z^jD_θ^i(f·D_zg)` (`j i` are the numbers of `z`- and
`θ`-derivatives). -/
def EasyMSl (f g : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) : ℝ :=
  ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), EasyMZ f g j i a b z θ

/-- The correction term `f·D_z(D_z^jD_θ^i g)`, retained only when `i + j = 4`. -/
def EasyMCor (f g : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) : ℝ :=
  if i + j = 4 then f z θ * Work.Spaces.mixed (j + 1) i g z θ else 0

/-- The dominating function for the squared expanded block. -/
def EasyMHdom (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf : ℝ) (j i : ℕ) (z : ℝ) : ℝ → ℝ :=
  fun θ => 2 * (25 * (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (EasyMZ f g j i a b z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
    + 2 * (Kf ^ 2 * ((Work.Spaces.mixed (j + 1) i g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))

/-- **The block `EasyM` in its Leibniz-expanded form.**  On the open angular interval, -/
theorem easyM_eq_expanded (α : ℝ) (f g : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.H2.EasyM α f g j i z θ
      = (EasyMSl f g j i z θ - EasyMCor f g j i z θ) * Work.FTS.H2.Wm α z θ := by
  have hleib := Work.FTS.TransportS.mixed_mul_Dz_open j i f g hf hg z θ hz hθ.1 hθ.2
  have hsl : EasyMSl f g j i z θ
      = Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ := by
    rw [EasyMSl]
    exact hleib.symm
  have hDz : Work.Spaces.Dz (Work.Spaces.mixed j i g) z θ
      = Work.Spaces.mixed (j + 1) i g z θ := rfl
  by_cases hc : i + j ≤ 3
  · have h4 : ¬ (i + j = 4) := by omega
    have hcor : EasyMCor f g j i z θ = 0 := by
      simp only [EasyMCor, h4, ite_false]
    simp only [Work.FTS.H2.EasyM, hc, ite_true, hcor, sub_zero, hsl]
  · have h4 : i + j = 4 := by omega
    have hcor : EasyMCor f g j i z θ = f z θ * Work.Spaces.mixed (j + 1) i g z θ := by
      simp only [EasyMCor, h4, ite_true]
    have hnot : ¬ (i + j ≤ 3) := by omega
    simp only [Work.FTS.H2.EasyM, hnot, ite_false, hcor, hsl]
    rw [hDz]

/-- **The analytic heart**: the squared expanded block, weighted by `sin(2θ)^{-γ}`, is
integrable on the slice. -/
theorem easyMSl_sub_cor_sq_sin_integrable (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg : ℝ) (hα : 0 < α)
    (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z : ℝ} (hz : 0 < z)
    (hFb : ∀ b : ℕ, b ≤ 3 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter b f z θ| ≤ Kf)
    (hGb : ∀ a b : ℕ, a + b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.mixed b a g z θ| ≤ Kg)
    (hFs : ∀ a b : ℕ, 1 ≤ a → a + b ≤ 4 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ)
    (hGs : ∀ a b : ℕ, 1 ≤ a → a + b ≤ 5 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    MeasureTheory.IntegrableOn
      (fun θ => (EasyMSl f g j i z θ - EasyMCor f g j i z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  have hcf : ∀ b a : ℕ, ContinuousOn (fun θ => Work.Spaces.mixed b a f z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun b a => ((hf.mixed b a).curry_θ hz).continuousOn
  have hcg : ∀ b a : ℕ, ContinuousOn (fun θ => Work.Spaces.mixed b a g z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun b a => ((hg.mixed b a).curry_θ hz).continuousOn
  have hf_b : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f z θ| ≤ Kf := by
    intro θ hθ
    simpa only [Work.Spaces.DzIter_zero] using hFb 0 (by norm_num) θ hθ
  -- the per-summand integrability, with one bounded factor
  have hterm : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.mixed b a f z θ) ^ 2
        * (Work.Spaces.mixed (j - b + 1) (i - a) g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
    intro a ha b hb
    have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · rw [ha0, Nat.sub_zero]
      have hb3 : b ≤ 3 := by omega
      refine esq_bdd_mul_sin_integrable (p := Work.Spaces.gam α) (K := Kf)
        (hGs i (j - b + 1) hi (by omega)) (hcf b 0) (hcg (j - b + 1) i) ?_ hKf
      intro θ hθ
      simpa only [Work.Spaces.mixed_zero_right] using hFb b hb3 θ hθ
    · refine esq_bdd_mul_sin_integrable' (p := Work.Spaces.gam α) (K := Kg)
        (hFs a b hapos (by omega)) (hcg (j - b + 1) (i - a)) (hcf b a) ?_ hKg
      intro θ hθ
      exact hGb (i - a) (j - b + 1) (by omega) θ hθ
  -- the same, in the `EasyMZ` normal form
  have htermZ : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      MeasureTheory.IntegrableOn (fun θ => (EasyMZ f g j i a b z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
    intro a ha b hb
    refine (esq_integrableOn_const_mul (hterm a ha b hb)
      (c := ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2)).congr_fun ?_ measurableSet_Icc
    intro θ _
    simp only [EasyMZ]
    ring
  have hXint : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.mixed (j + 1) i g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
    hGs i (j + 1) hi (by omega)
  have hSumZ : MeasureTheory.IntegrableOn (fun θ => ∑ a ∈ Finset.range (i + 1),
      ∑ b ∈ Finset.range (j + 1), (EasyMZ f g j i a b z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
    esq_integrableOn_finset_sum _ fun a ha =>
      esq_integrableOn_finset_sum _ fun b hb => htermZ a ha b hb
  have hHdom : MeasureTheory.IntegrableOn (EasyMHdom α f g Kf j i z) Work.Spaces.Iθ := by
    have h1 : MeasureTheory.IntegrableOn (fun θ => 2 * (25 * (∑ a ∈ Finset.range (i + 1),
          ∑ b ∈ Finset.range (j + 1), (EasyMZ f g j i a b z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))) Work.Spaces.Iθ :=
      esq_integrableOn_const_mul (c := 2) (esq_integrableOn_const_mul (c := 25) hSumZ)
    have h2 : MeasureTheory.IntegrableOn (fun θ => 2 * (Kf ^ 2
          * ((Work.Spaces.mixed (j + 1) i g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))) Work.Spaces.Iθ :=
      esq_integrableOn_const_mul (c := 2) (esq_integrableOn_const_mul (c := Kf ^ 2) hXint)
    exact h1.add h2
  -- continuity of the target on the open interval
  have hs_cont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hbase : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
    exact hbase.continuousOn.rpow_const (fun θ hθ => Or.inl (ne_of_gt (esq_sin_two_pos hθ)))
  have hSl_cont : ContinuousOn (fun θ => EasyMSl f g j i z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hmain : ContinuousOn (fun θ => ∑ a ∈ Finset.range (i + 1),
        ∑ b ∈ Finset.range (j + 1), EasyMZ f g j i a b z θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      continuousOn_finset_sum _ fun a _ =>
        continuousOn_finset_sum _ fun b _ =>
          continuousOn_const.mul ((hcf b a).mul (hcg (j - b + 1) (i - a)))
    simpa only [EasyMSl] using hmain
  have hCor_cont : ContinuousOn (fun θ => EasyMCor f g j i z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    by_cases h4 : i + j = 4
    · simp only [EasyMCor, h4, ite_true]
      exact (hcf 0 0).mul (hcg (j + 1) i)
    · simp only [EasyMCor, h4, ite_false]
      exact continuousOn_const
  refine esq_integrableOn_of_bound hHdom (((hSl_cont.sub hCor_cont).pow 2).mul hs_cont) ?_
  intro θ hθ
  have hs0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    Real.rpow_nonneg (esq_sin_two_pos hθ).le _
  have hnn : 0 ≤ (EasyMSl f g j i z θ - EasyMCor f g j i z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := mul_nonneg (sq_nonneg _) hs0
  rw [Real.norm_of_nonneg hnn]
  -- the Cauchy–Schwarz bound on the Leibniz sum
  have hSl2 : (EasyMSl f g j i z θ) ^ 2 ≤ 25 * ∑ a ∈ Finset.range (i + 1),
      ∑ b ∈ Finset.range (j + 1), (EasyMZ f g j i a b z θ) ^ 2 := by
    have hinner : ∀ a : ℕ, (∑ b ∈ Finset.range (j + 1), EasyMZ f g j i a b z θ) ^ 2
        ≤ 5 * ∑ b ∈ Finset.range (j + 1), (EasyMZ f g j i a b z θ) ^ 2 := by
      intro a
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
        (f := fun b => EasyMZ f g j i a b z θ)
      calc (∑ b ∈ Finset.range (j + 1), EasyMZ f g j i a b z θ) ^ 2
          ≤ ((Finset.range (j + 1)).card : ℝ)
              * ∑ b ∈ Finset.range (j + 1), (EasyMZ f g j i a b z θ) ^ 2 := h
        _ ≤ 5 * ∑ b ∈ Finset.range (j + 1), (EasyMZ f g j i a b z θ) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun b _ => sq_nonneg _)
            rw [Finset.card_range]
            exact_mod_cast (by omega : j + 1 ≤ 5)
    have houter := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun a => ∑ b ∈ Finset.range (j + 1), EasyMZ f g j i a b z θ)
    calc (EasyMSl f g j i z θ) ^ 2
        ≤ ((Finset.range (i + 1)).card : ℝ) * ∑ a ∈ Finset.range (i + 1),
            (∑ b ∈ Finset.range (j + 1), EasyMZ f g j i a b z θ) ^ 2 := houter
      _ ≤ 5 * ∑ a ∈ Finset.range (i + 1),
            (∑ b ∈ Finset.range (j + 1), EasyMZ f g j i a b z θ) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun a _ => sq_nonneg _)
          rw [Finset.card_range]
          exact_mod_cast (by omega : i + 1 ≤ 5)
      _ ≤ 5 * ∑ a ∈ Finset.range (i + 1),
            (5 * ∑ b ∈ Finset.range (j + 1), (EasyMZ f g j i a b z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hinner a) (by norm_num)
      _ = 25 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (EasyMZ f g j i a b z θ) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
  have hSl2s : (EasyMSl f g j i z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ 25 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (EasyMZ f g j i a b z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    have hSums : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (EasyMZ f g j i a b z θ) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (EasyMZ f g j i a b z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_mul ..
    calc (EasyMSl f g j i z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ (25 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (EasyMZ f g j i a b z θ) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hSl2 hs0
      _ = 25 * ((∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (EasyMZ f g j i a b z θ) ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
          ring
      _ = 25 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (EasyMZ f g j i a b z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
          rw [hSums]
  have hCor2s : (EasyMCor f g j i z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ Kf ^ 2 * ((Work.Spaces.mixed (j + 1) i g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    have hCor2 : (EasyMCor f g j i z θ) ^ 2
        ≤ Kf ^ 2 * (Work.Spaces.mixed (j + 1) i g z θ) ^ 2 := by
      by_cases h4 : i + j = 4
      · have h1 : EasyMCor f g j i z θ = f z θ * Work.Spaces.mixed (j + 1) i g z θ := by
          simp only [EasyMCor, h4, ite_true]
        rw [h1, mul_pow]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        rw [← sq_abs (f z θ)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hf_b θ hθ) 2
      · have h1 : EasyMCor f g j i z θ = 0 := by
          simp only [EasyMCor, h4, ite_false]
        rw [h1]
        have h2 : (0 : ℝ) ≤ Kf ^ 2 * (Work.Spaces.mixed (j + 1) i g z θ) ^ 2 :=
          mul_nonneg (sq_nonneg Kf) (sq_nonneg _)
        simpa using h2
    calc (EasyMCor f g j i z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ (Kf ^ 2 * (Work.Spaces.mixed (j + 1) i g z θ) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hCor2 hs0
      _ = Kf ^ 2 * ((Work.Spaces.mixed (j + 1) i g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
  have hmain1 : (EasyMSl f g j i z θ - EasyMCor f g j i z θ) ^ 2
      ≤ 2 * (EasyMSl f g j i z θ) ^ 2 + 2 * (EasyMCor f g j i z θ) ^ 2 := by
    nlinarith [sq_nonneg (EasyMSl f g j i z θ + EasyMCor f g j i z θ)]
  calc (EasyMSl f g j i z θ - EasyMCor f g j i z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (2 * (EasyMSl f g j i z θ) ^ 2 + 2 * (EasyMCor f g j i z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right hmain1 hs0
    _ = 2 * ((EasyMSl f g j i z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        + 2 * ((EasyMCor f g j i z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        ring
    _ ≤ 2 * (25 * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          (EasyMZ f g j i a b z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        + 2 * (Kf ^ 2 * ((Work.Spaces.mixed (j + 1) i g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
        add_le_add (mul_le_mul_of_nonneg_left hSl2s (by norm_num))
          (mul_le_mul_of_nonneg_left hCor2s (by norm_num))
    _ = EasyMHdom α f g Kf j i z θ := by rw [EasyMHdom]

/-- The square of the mixed block `EasyM α f g j i` (`1 ≤ i`, `i + j ≤ 4`) of `Heasy` is
integrable on the `θ`-slice at a fixed `z > 0`.

`EasyM α f g j i z · = (D_z^j D_θ^i(f·D_z g) − [i+j = 4] f·D_z(D_z^j D_θ^i g))·Wm`.  Expand the
Leibniz rule by `Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed`,
`D_z^j D_θ^i(f·D_z g) = ∑_{a ≤ i} ∑_{b ≤ j} C(i,a) C(j,b) (D_z^bD_θ^a f)·(D_z^{j-b+1}D_θ^{i-a} g)`
(the `g`-factor is `mixed (j-b) (i-a) (D_z g) = mixed (j-b+1) (i-a) g`), and bound the square of the
sum by a constant times the sum of squares.  Each summand
`∫_θ (D_z^bD_θ^a f)² (D_z^{j-b+1}D_θ^{i-a} g)² w(z)² sin(2θ)^{-γ}` is handled by AM–GM with one
bounded factor:
* if `a = 0`: `D_z^b f` is bounded by `Kf` (note `b ≤ j ≤ 3`, since `1 ≤ i`) and
  `D_z^{j-b+1}D_θ^i g` (θ-order `i ≥ 1`) is a mixed slot of order `≤ 5` (`hGs`);
* if `a ≥ 1`: `D_z^bD_θ^a f` is a mixed `f`-slot (order `≤ 4`, `hFs`) and the `g`-factor has total
  order `i+j+1-a-b ≤ 4` resp. is pure of order `j-b+1 ≤ 4`, hence bounded by `Kg` (`hGb`).
The correction term `f·D_z(D_z^jD_θ^i g) = f·mixed (j+1) i g` has `f` bounded by `Kf` and
`mixed (j+1) i g` a mixed slot of order `i+j+1 ≤ 5` (`hGs`).  Use
`Work.H2.T1Q.integrableOn_slice_two` and `Work.H2.T1Q.aesm_Iθ_of_continuousOn` for the
measurability of the summands. -/
theorem easyM_sq_int (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg : ℝ) (hα : 0 < α)
    (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z : ℝ} (hz : 0 < z)
    (hFb : ∀ b : ℕ, b ≤ 3 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter b f z θ| ≤ Kf)
    (hGb : ∀ a b : ℕ, a + b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.mixed b a g z θ| ≤ Kg)
    (hFs : ∀ a b : ℕ, 1 ≤ a → a + b ≤ 4 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ)
    (hGs : ∀ a b : ℕ, 1 ≤ a → a + b ≤ 5 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    MeasureTheory.IntegrableOn (fun θ => (Work.FTS.H2.EasyM α f g j i z θ) ^ 2) Work.Spaces.Iθ := by
  have hslice := easyMSl_sub_cor_sq_sin_integrable α f g Kf Kg hα hKf hKg hf hg hz
    hFb hGb hFs hGs j i hi hij
  -- multiply by the (constant in `θ`) factor `w(z)²`
  have hWm : MeasureTheory.IntegrableOn (fun θ => ((EasyMSl f g j i z θ - EasyMCor f g j i z θ)
      * Work.FTS.H2.Wm α z θ) ^ 2) Work.Spaces.Iθ := by
    refine (esq_integrableOn_const_mul (c := (Work.Spaces.w z) ^ 2) hslice).congr ?_
    filter_upwards [esq_ae_mem_Ioo] with θ hθ
    rw [mul_pow, Work.FTS.H2.hbi_Wm_sq α z θ (esq_sin_two_pos hθ).le]
    ring
  exact hWm.congr (by
    filter_upwards [esq_ae_mem_Ioo] with θ hθ
    rw [easyM_eq_expanded α f g j i hi hij hf hg hz hθ])

end Work.FTS.TransportS.T2SliceAux
