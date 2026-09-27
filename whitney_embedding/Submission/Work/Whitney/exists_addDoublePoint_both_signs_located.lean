import Mathlib
import Submission.Work.Whitney.exists_addDoublePoint_both_signs_chart_like
import Submission.Work.Whitney.exists_addDoublePoint_chart_like
import Submission.Work.Whitney.exists_reflection_det_neg
import Submission.Work.Whitney.doubleDetRep_comp_clm
import Submission.Work.Whitney.EuclidModelProps

namespace Work.Whitney

theorem exists_addDoublePoint_both_signs_located {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target)
    (hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hcinv : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u)
    (U : Set M) (hUopen : IsOpen U) (h0U : c.symm 0 ∈ U) (hUsub : U ⊆ c.source)
    (H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin (2 * n)))
    (hHc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hHaxis : ∀ u, H (u, 0) = f (c.symm u))
    (ρ L : ℝ) (hρ : 0 < ρ) (hL : 0 < L)
    (hHinj : Set.InjOn H (Metric.ball 0 ρ))
    (hHimm : ∀ z ∈ Metric.ball 0 ρ, Function.Injective (fderiv ℝ H z))
    (hHLip : ∀ z ∈ Metric.ball 0 ρ, ∀ z' ∈ Metric.ball 0 ρ, ‖H z - H z'‖ ≤ L * ‖z - z'‖)
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hβc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβimm : ∀ u, Function.Injective (fderiv ℝ β u))
    (a b : Fin n → ℝ) (hab : a ≠ b) (hβab : β a = β b)
    (hβuniq : ∀ u v, u ≠ v → β u = β v → (u = a ∧ v = b) ∨ (u = b ∧ v = a))
    (R δ η : ℝ) (hR : 0 < R) (hδ : 0 < δ) (hη : 0 < η)
    (hβact : ∀ u, ‖u‖ < R → (β u).2 ≠ 0)
    (hβR : ∀ u, R ≤ ‖u‖ → β u = Work.Whitney.inclModel n u)
    (hβδ : ∀ u, ‖β u - Work.Whitney.inclModel n u‖ ≤ δ)
    (hdet : LinearMap.det (((fderiv ℝ β a).coprod (fderiv ℝ β b)).toLinearMap) ≠ 0)
    (hRa : ‖a‖ < R) (hRb : ‖b‖ < R)
    (hρR : 2 * R + δ ≤ ρ) (hδLη : L * δ < η)
    (hballU : Metric.ball 0 (3 * R) ⊆ c '' U)
    (hsrc : ∀ y : M, ‖c y‖ < 3 * R → y ∈ c.source)
    (hclean : ∀ y : M, ‖c y‖ < R → ∀ z : M, f y = f z → z = y)
    (hsep : ∀ y z : M, ‖c y‖ < R →
      2 * R ≤ ‖c z‖ → f y ≠ f z → η ≤ ‖f y - f z‖) :
    ∃ (fp fm : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) fp ∧
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) fm ∧
      (∀ z, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) fp z)) ∧
      (∀ z, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) fm z)) ∧
      (∀ y : M, R ≤ ‖c y‖ → fp y = f y) ∧
      (∀ y : M, R ≤ ‖c y‖ → fm y = f y) ∧
      ‖c p'‖ < R ∧ ‖c q'‖ < R ∧
      Work.Whitney.doubleSet fp = Work.Whitney.doubleSet f ∪ {(p', q'), (q', p')} ∧
      Work.Whitney.doubleSet fm = Work.Whitney.doubleSet f ∪ {(p', q'), (q', p')} ∧
      Work.Whitney.doubleDetC fp c p' q' ≠ 0 ∧
      Work.Whitney.doubleDetC fm c p' q' = - Work.Whitney.doubleDetC fp c p' q' := by
  classical
  have hn0 : 0 < n := by omega
  set lam : ℝ := Real.sqrt n with hlamdef
  have hlam_pos : 0 < lam := by
    rw [hlamdef]; exact Real.sqrt_pos.mpr (by exact_mod_cast hn0)
  set Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    euclidModel n lam β with hΨdef
  -- the orientation-reversing isometry fixing the axis and the model's double point image
  obtain ⟨S, hSaxis, hSz, hSnorm, hSdet⟩ :=
    exists_reflection_det_neg n hn (Ψ (scaledPt n lam a))
  have hSinj : Function.Injective S := by
    intro p q hpq
    have h : S (p - q) = 0 := by rw [map_sub, hpq, sub_self]
    have h3 : ‖p - q‖ = 0 := by
      have h4 := hSnorm (p - q)
      rw [h, norm_zero] at h4
      exact h4.symm
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  have hSball : ∀ w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ →
      S w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw ⊢
    rw [hSnorm]
    exact hw
  have hdiffH : Differentiable ℝ H := hHc.differentiable (by simp)
  have hdiffΨ : Differentiable ℝ Ψ := by
    rw [hΨdef]
    exact (contDiff_euclidModel_smooth (n := n) (lam := lam) (β := β) hβc).differentiable
      (by simp)
  -- `H ∘ S` inherits every hypothesis imposed on `H`
  have hHS_c : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => H (S w)) := hHc.comp S.contDiff
  have hHS_axis : ∀ u : EuclideanSpace ℝ (Fin n),
      (fun w => H (S w)) (u, 0) = f (c.symm u) := by
    intro u
    change H (S (u, 0)) = f (c.symm u)
    rw [hSaxis u]
    exact hHaxis u
  have hHS_inj : Set.InjOn (fun w => H (S w))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ) := by
    intro p hp q hq hpq
    exact hSinj (hHinj (hSball p hp) (hSball q hq) hpq)
  have hHS_imm : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ,
      Function.Injective (fderiv ℝ (fun w => H (S w)) z) := by
    intro z hz
    have hfd : fderiv ℝ (fun w => H (S w)) z = (fderiv ℝ H (S z)).comp S := by
      rw [fderiv_fun_comp z (hdiffH (S z)) S.differentiableAt, ContinuousLinearMap.fderiv]
    rw [hfd]
    intro p q hpq
    exact hSinj ((hHimm (S z) (hSball z hz)) hpq)
  have hHS_lip : ∀ z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ,
      ∀ z' ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ,
      ‖(fun w => H (S w)) z - (fun w => H (S w)) z'‖ ≤ L * ‖z - z'‖ := by
    intro z hz z' hz'
    have h1 : ‖S z - S z'‖ = ‖z - z'‖ := by rw [← map_sub, hSnorm]
    calc ‖H (S z) - H (S z')‖ ≤ L * ‖S z - S z'‖ :=
          hHLip (S z) (hSball z hz) (S z') (hSball z' hz')
      _ = L * ‖z - z'‖ := by rw [h1]
  -- glue the model into `H` and into `H ∘ S`
  obtain ⟨fp, p₁, q₁, hfp_sm, hfp_imm, hfp_out, hp1A, hq1B, hp1U, hq1U, hfp_form,
    hfp_ds, hfp_val, hfp_detC⟩ :=
    exists_addDoublePoint_chart_like f hf himm c h0 hcsm hcinv U hUopen h0U hUsub H hHc hHaxis
      ρ L hρ hL hHinj hHimm hHLip β hβc hβimm a b hab hβab hβuniq R δ η hR hδ hη hβact hβR
      hβδ hdet hRa hRb hρR hδLη hballU hsrc hclean hsep
  obtain ⟨fm, p₂, q₂, hfm_sm, hfm_imm, hfm_out, hp2A, hq2B, hp2U, hq2U, hfm_form,
    hfm_ds, hfm_val, hfm_detC⟩ :=
    exists_addDoublePoint_chart_like f hf himm c h0 hcsm hcinv U hUopen h0U hUsub (fun w => H (S w))
      hHS_c hHS_axis ρ L hρ hL hHS_inj hHS_imm hHS_lip β hβc hβimm a b hab hβab hβuniq
      R δ η hR hδ hη hβact hβR hβδ hdet hRa hRb hρR hδLη hballU hsrc hclean hsep
  -- the inserted double points are located inside the ball of radius `R`
  have hp1loc : ‖c p₁‖ < R := by
    rw [hp1A]
    exact norm_scaledPt_lt (n := n) (lam := lam) (R := R) (a := a) hlam_pos le_rfl hRa
  have hq1loc : ‖c q₁‖ < R := by
    rw [hq1B]
    exact norm_scaledPt_lt (n := n) (lam := lam) (R := R) (a := b) hlam_pos le_rfl hRb
  -- the two inserted double points coincide
  have hp12 : p₁ = p₂ := by
    have h1 : c p₁ = c p₂ := by rw [hp1A, hp2A]
    rw [← c.left_inv (hUsub hp1U), ← c.left_inv (hUsub hp2U), h1]
  have hq12 : q₁ = q₂ := by
    have h1 : c q₁ = c q₂ := by rw [hq1B, hq2B]
    rw [← c.left_inv (hUsub hq1U), ← c.left_inv (hUsub hq2U), h1]
  have hfm_ds' : Work.Whitney.doubleSet fm =
      Work.Whitney.doubleSet f ∪ {(p₁, q₁), (q₁, p₁)} := by
    rw [hfm_ds, ← hp12, ← hq12]
  -- the sign of the two insertions is opposite
  have hΨdbl : Ψ (scaledPt n lam a) = Ψ (scaledPt n lam b) := by
    rw [hΨdef]
    exact (euclidModel_double_point (n := n) (lam := lam) (β := β) (a := a) (b := b)
      hlam_pos hab hβab).1
  have hsign : Work.Whitney.doubleDetC fm c p₁ q₁ =
      - Work.Whitney.doubleDetC fp c p₁ q₁ := by
    have hfm_val' : Work.Whitney.doubleDetC fm c p₁ q₁ =
        Work.Whitney.doubleDetRep (fun v => H (S (Ψ v)))
          (scaledPt n lam a) (scaledPt n lam b) := by
      rw [hp12, hq12]
      exact hfm_val
    have hfp_val' : Work.Whitney.doubleDetC fp c p₁ q₁ =
        Work.Whitney.doubleDetRep (fun v => H (Ψ v))
          (scaledPt n lam a) (scaledPt n lam b) := hfp_val
    rw [hfm_val', hfp_val',
      doubleDetRep_comp_clm Ψ H S (scaledPt n lam a) (scaledPt n lam b) hΨdbl hSz
        (hdiffH (Ψ (scaledPt n lam a))) (hdiffΨ (scaledPt n lam a))
        (hdiffΨ (scaledPt n lam b)), hSdet]
    ring
  exact ⟨fp, fm, p₁, q₁, hfp_sm, hfm_sm, hfp_imm, hfm_imm, hfp_out, hfm_out, hp1loc,
    hq1loc, hfp_ds, hfm_ds', hfp_detC, hsign⟩

end Work.Whitney
