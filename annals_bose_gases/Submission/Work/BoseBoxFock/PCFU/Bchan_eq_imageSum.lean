import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PCFU.Achan_eq_imageSum
import Submission.Work.BoseBoxFock.PCFU.chanBCD_canonical
import Submission.Work.BoseBoxFock.chiRow_aP_abox_facts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

noncomputable section

/-!
# `Work.BoseBoxFock.PCFU.Bchan_eq_imageSum` — the `(B)`-channel at the image sum

The `(B)`-twin of the proved `Work.BoseBoxFock.PCFU.Achan_eq_imageSum`.  Writing
`ℓ = ellH v μ`, `κ = ((paramsAt μ (a v)).d²·sideAt μ (a v))⁻¹`, `θ = thetaFun ℓ`,
`χ = chiLam ℓ`, the theorem computes

    Bchan = ∫ Θ(x)·θ(x i)·ChBU(y, x j, u)·Θ(x[i↦y][j↦u])

as `ℓ⁶` times the `χ`-weighted `KχfrU`-integral of the fibre deviation `Q_jP_iΘ` against the
**image sum** of the low cut-off kernel — the exact structure of the `(A)`-channel with
`χ(x i)χ(x j)KfrU(x j−x i)` replaced by `χ(x j)KχfrU(x j)`.

The proof is the same three steps as in `(A)`, all of whose building blocks are already PROVED:

1. `chanB_canonical` brings `Bchan` into the canonical form
   `∫ Θ'Θ θ(y)θ(u)θ(x i)χ(x j)Ksfr(u−x j)KχfrU(x j)`, in which the two frame variables carry the
   sharp box and the slots carry the window;
2. `chan_int_y_generic` performs the `∫_y` step against `θ(y)`, producing the slot mean `P_i`
   (this is `ℓ³·aP = ∫_{acube}` together with Fubini); the parametric mean is replaced by
   `aP ℓ i Θ` through `aP_comp_update_eq` (needs `i ≠ j`);
3. `prod_theta_integral` converts the remaining `θ(u)` into the restricted integral over
   `acube ℓ`, and `int_Ksfr_aP_eq_imageSum` performs the `∫_u` step:
   `Ksfr = ℓ³·Σ'_d lowKer(· + ℓ•latVec d) − 1`, the `−1` producing the `Q_j` of `Q_jP_iΘ`
   against the tiling `Σ'_d ∫_{acube} lowKer = 1`.

What is *new* with respect to `(A)` is the weight of the channel,

    `G x = Θ x · θ(x i) · χ(x j) · KχfrU(x j)`,

(the slot-`i` factor is the sharp box instead of `χ(x i)`, and the `KfrU(x j − x i)` is replaced by
the `χ̂`-weighted `KχfrU(x j)`), whose measurability, bound and box-support are proved here, and
the final collaping of `θ(x i)`: the leftover sharp-box factor of the canonical form is the `1` of
`chiRow_aP_abox_facts` on `support Θ ⊆ abox n ℓ`.  The two `ℓ³` factors (one from step 2, one from
step 3) multiply to the `ℓ⁶` of the statement.
-/

/-! ## The `χ̂`-weighted `univ` `k`-frame: continuity and its coefficient bound

These are the `KχfrU`-twins of `G_boxFacts`'s `continuous_KfrU`/`norm_KfrU_le`; the only change is
the coefficient `W1h(k)·hatChih(k)` in place of `W1h(k)`. -/

/-- Continuity of the `χ̂`-weighted `univ` `k`-frame (a finite sum of plane waves). -/
lemma continuous_KχfrU (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) :
    Continuous fun z : E3 => KχfrU v h μ fu N z := by
  simp only [KχfrU]
  fun_prop

/-- Measurability of the `χ̂`-weighted `univ` `k`-frame. -/
lemma measurable_KχfrU (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) :
    Measurable fun z : E3 => KχfrU v h μ fu N z :=
  (continuous_KχfrU v h μ fu N).measurable

/-- **Uniform bound on the `χ̂`-weighted `univ` `k`-frame**: the triangle inequality, every summand
having modulus `|Ŵ₁(k)·χ̂(ℓκ_k)|` (the phase is purely imaginary, hence of modulus one). -/
lemma norm_KχfrU_le (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (z : E3) :
    ‖KχfrU v h μ fu N z‖
      ≤ ∑ k : Work.BoseBoxFock.Lab N,
          |Work.BoseBoxFock.W1h v h μ fu N k * Work.BoseBoxFock.hatChih v μ N k| := by
  simp only [KχfrU]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  have hexp : ‖Complex.exp (Complex.I * ((inner ℝ
      (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) z : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [hexp, mul_one]
  exact le_of_eq (RCLike.norm_ofReal _)

theorem Bchan_eq_imageSum {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ))
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * ∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)
                * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                    (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                          (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                            * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                          (u - x j + Work.BoseBoxFock.ellH v μ
                            • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                      * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                          (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                          (Function.update x j u) : ℝ) : ℂ)) := by
  obtain ⟨Cθ, hCθ⟩ := hΘb
  have hCθ0 : 0 ≤ Cθ := le_trans (abs_nonneg (Θ 0)) (hCθ 0)
  have hCθn : ∀ x, ‖Θ x‖ ≤ Cθ := fun x => by rw [Real.norm_eq_abs]; exact hCθ x
  -- the two frame bounds
  set Ks : ℝ := ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      |Work.BoseBoxFock.fLh v fc μ N s| with hKsdef
  have hKs0 : 0 ≤ Ks := by rw [hKsdef]; exact Finset.sum_nonneg fun s _ => abs_nonneg _
  set Kw : ℝ := ∑ k : Work.BoseBoxFock.Lab N,
      |Work.BoseBoxFock.W1h v h μ fu N k * Work.BoseBoxFock.hatChih v μ N k| with hKwdef
  have hKw0 : 0 ≤ Kw := by rw [hKwdef]; exact Finset.sum_nonneg fun k _ => abs_nonneg _
  -- the weight `G` of the channel and the `u`-kernel `F`
  set G : Submission.BoseGases.X n → ℂ := fun x =>
      ((Θ x : ℝ) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i)
        * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
        * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j) with hGdef
  set F : Submission.BoseGases.X n → E3 → ℂ := fun x u =>
      Work.BoseBoxFock.Ksfr v fc μ N (u - x j) with hFdef
  -- the three `G`-facts (measurability, bound, box-support)
  have hGm : Measurable G := by
    rw [hGdef]
    have h1 : Measurable fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp hΘm
    have h2 : Measurable fun x : Submission.BoseGases.X n =>
        Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i) :=
      (measurable_thetaFun hℓ).comp (measurable_pi_apply i)
    have h3 : Measurable fun x : Submission.BoseGases.X n =>
        ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp
        (((Work.BoseB4.BoxData.chiLam_cont _ _).measurable).comp (measurable_pi_apply j))
    have h4 : Measurable fun x : Submission.BoseGases.X n =>
        Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j) :=
      (measurable_KχfrU v h μ fu N).comp (measurable_pi_apply j)
    exact ((h1.mul h2).mul h3).mul h4
  have hGb : ∀ x, ‖G x‖ ≤ Cθ * 1 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * Kw := by
    intro x
    have hA : ‖((Θ x : ℝ) : ℂ)‖ ≤ Cθ := by
      rw [show ‖((Θ x : ℝ) : ℂ)‖ = |Θ x| from by simp]
      exact hCθ x
    have hC : (0 : ℝ) ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    rw [hGdef, hKwdef]
    rw [show ‖((Θ x : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i)
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
          * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)‖
        = ‖((Θ x : ℝ) : ℂ)‖
          * ‖Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i)‖
          * ‖((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)‖
          * ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)‖ from by
      rw [norm_mul, norm_mul, norm_mul]]
    exact mul_le_mul
      (mul_le_mul (mul_le_mul hA (norm_thetaFun_le_one _ _) (norm_nonneg _) hCθ0)
        (norm_chiLam_le _ _) (norm_nonneg _) (mul_nonneg hCθ0 zero_le_one))
      (norm_KχfrU_le v h μ fu N (x j)) (norm_nonneg _)
      (mul_nonneg (mul_nonneg hCθ0 zero_le_one) hC)
  have hGs : Function.support G ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ) := by
    intro x hx
    apply hΘs
    intro h0
    exact hx (by rw [hGdef]; simp [h0])
  have hFm : Measurable (fun p : Submission.BoseGases.X n × E3 => F p.1 p.2) := by
    rw [hFdef]
    exact (Work.BoseBoxFock.PCFU.continuous_Ksfr.measurable).comp
      ((continuous_snd.sub ((continuous_apply j).comp continuous_fst))).measurable
  have hFb : ∀ p : Submission.BoseGases.X n × E3, ‖F p.1 p.2‖ ≤ Ks := by
    intro p
    rw [hFdef, hKsdef]
    exact Work.BoseBoxFock.PCFU.norm_Ksfr_le _
  -- the canonical form, then the `∫_y` step
  have hcanon := chanB_canonical hij v h fc fu μ N Θ hΘ hΘm ⟨Cθ, hCθn⟩
  have hbridge : (∫ q : Submission.BoseGases.X n × (E3 × E3),
        ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.1
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.2
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (q.1 j) : ℝ) : ℂ)
          * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 - q.1 j)
          * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (q.1 j))
      = ∫ q : Submission.BoseGases.X n × (E3 × E3),
          G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.2
            * F q.1 q.2.2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with q
    rw [hGdef, hFdef]
    ring
  have hY := chan_int_y_generic (n := n) (i := i) (j := j)
      (ℓ := Work.BoseBoxFock.ellH v μ) hℓ G hGm
      (Cθ * 1 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * Kw)
      hGb hGs Θ hΘm Cθ hCθ F hFm Ks hFb
  -- the pointwise replacement of the "parametric" slot mean by `P_iΘ`
  have hP : (∫ p : Submission.BoseGases.X n × E3,
        G p.1 * F p.1 p.2
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
          * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
              (fun x' => Θ (Function.update x' j p.2)) p.1 : ℝ) : ℂ))
      = ∫ p : Submission.BoseGases.X n × E3,
          G p.1 * F p.1 p.2
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
            * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                (Function.update p.1 j p.2) : ℝ) : ℂ) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    have h := aP_comp_update_eq (ℓ := Work.BoseBoxFock.ellH v μ) hij Θ p.1 p.2
    simp only [h]
  -- the Fubini step
  have hHm : Measurable (fun p : Submission.BoseGases.X n × E3 =>
      F p.1 p.2 * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
          (Function.update p.1 j p.2) : ℝ) : ℂ)) := by
    have hAPm' : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
          (fun x' => Θ (Function.update x' j p.2)) p.1) :=
      measurable_aP_param i j hΘm
    have hAPm : Measurable (fun p : Submission.BoseGases.X n × E3 =>
        Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
          (Function.update p.1 j p.2)) := by
      rw [show (fun p : Submission.BoseGases.X n × E3 =>
            Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
              (fun x' => Θ (Function.update x' j p.2)) p.1)
          = (fun p : Submission.BoseGases.X n × E3 =>
            Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
              (Function.update p.1 j p.2)) from by
        funext p
        exact aP_comp_update_eq (ℓ := Work.BoseBoxFock.ellH v μ) hij Θ p.1 p.2] at hAPm'
      exact hAPm'
    exact hFm.mul (Complex.measurable_ofReal.comp hAPm)
  have hHb : ∀ p : Submission.BoseGases.X n × E3,
      ‖F p.1 p.2 * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
          (Function.update p.1 j p.2) : ℝ) : ℂ)‖ ≤ Ks * Cθ := by
    intro p
    have hAPb : |Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
        (Function.update p.1 j p.2)| ≤ Cθ :=
      Work.BoseBoxFock.Weak.aP_abs_le hℓ i hCθ0 (fun x => hCθ x) (Function.update p.1 j p.2)
    rw [norm_mul]
    refine mul_le_mul (hFb p) ?_ (norm_nonneg _) hKs0
    rw [Work.BoseBoxFock.PCFU.norm_ofReal_eq_abs]
    exact hAPb
  have hFub := prod_theta_integral (n := n) (ℓ := Work.BoseBoxFock.ellH v μ) hℓ
      G hGm hGs
      (Cθ * 1 * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ * Kw) hGb
      (fun x u => F x u * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
          (Function.update x j u) : ℝ) : ℂ)) hHm (Ks * Cθ) hHb
  -- the `∫_u` step (`int_Ksfr_aP_eq_imageSum`) with the image sum of the low cut-off
  have hImg : ∀ x : Submission.BoseGases.X n,
      (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
          Work.BoseBoxFock.Ksfr v fc μ N (u - x j)
            * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                (Function.update x j u) : ℝ) : ℂ))
        = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
            * ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (u - x j + Work.BoseBoxFock.ellH v μ
                        • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                  * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                      (Function.update x j u) : ℝ) : ℂ) :=
    int_Ksfr_aP_eq_imageSum (v := v) (fc := fc) (μ := μ) (N := N) hℓ hκ hN i j Θ hΘm ⟨Cθ, hCθn⟩
  -- abbreviation for the image-sum inner integral
  set J : Submission.BoseGases.X n → ℂ := fun x =>
      ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
        (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
              (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
              (u - x j + Work.BoseBoxFock.ellH v μ
                • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
              (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
              (Function.update x j u) : ℝ) : ℂ) with hJdef
  -- the sharp-box factor `θ(x i)` of the canonical form is `1` on the support of `Θ`
  have hGdrop : (∫ x : Submission.BoseGases.X n, G x * J x)
      = ∫ x : Submission.BoseGases.X n,
          (((Θ x : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
            * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)) * J x := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : Θ x = 0
    · simp only [hGdef]
      rw [hx]
      simp
    · have hxmem : x ∈ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ) :=
        hΘs (Function.mem_support.mpr hx)
      have hθ : Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i) = 1 :=
        (chiRow_aP_abox_facts (n := n) (ℓ := Work.BoseBoxFock.ellH v μ) hℓ).2.1 hxmem i
      simp only [hGdef, hθ]
      ring
  -- assembly
  calc (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = (∫ q : Submission.BoseGases.X n × (E3 × E3),
          ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * ((Θ q.1 : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.2
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
            * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (q.1 j) : ℝ) : ℂ)
            * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 - q.1 j)
            * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (q.1 j)) := hcanon
    _ = (∫ q : Submission.BoseGases.X n × (E3 × E3),
          G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.2
            * F q.1 q.2.2) := hbridge
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * ∫ p : Submission.BoseGases.X n × E3,
              G p.1 * F p.1 p.2
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
                * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
                    (fun x' => Θ (Function.update x' j p.2)) p.1 : ℝ) : ℂ) := hY
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * ∫ p : Submission.BoseGases.X n × E3,
              G p.1 * F p.1 p.2
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
                * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                    (Function.update p.1 j p.2) : ℝ) : ℂ) := by rw [hP]
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ x : Submission.BoseGases.X n, G x *
              ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                (Work.BoseBoxFock.Ksfr v fc μ N (u - x j)
                  * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                      (Function.update x j u) : ℝ) : ℂ))) := by
        congr 1
        rw [show (∫ p : Submission.BoseGases.X n × E3,
              G p.1 * F p.1 p.2
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
                * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                    (Function.update p.1 j p.2) : ℝ) : ℂ))
            = ∫ p : Submission.BoseGases.X n × E3,
                G p.1 * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
                  * (F p.1 p.2 * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                      (Function.update p.1 j p.2) : ℝ) : ℂ)) from by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with p
          ring]
        rw [hFub, hFdef]
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ x : Submission.BoseGases.X n, G x *
              (((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3 * J x)) := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        congr 1
        exact hImg x
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
              * ∫ x : Submission.BoseGases.X n, G x * J x) := by
        congr 1
        rw [← MeasureTheory.integral_const_mul]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        ring
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * ∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (x j)
                * J x := by
        rw [hGdrop]
        ring

end

end Work.BoseBoxFock.PCFU
