import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PCFU.G_boxFacts
import Submission.Work.BoseBoxFock.PCFU.aPSlotFacts
import Submission.Work.BoseBoxFock.PCFU.int_Ksfr_aP_eq_imageSum
import Submission.Work.BoseBoxFock.PCFU.prod_theta_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-!
# `Work.BoseBoxFock.PCFU.Achan_eq_imageSum` — the (A)-channel at the image sum

This module closes the `(A)`-channel of the cubic middle kernel at the **image sum** of the low
cut-off kernel.  Writing

* `ℓ = ellH v μ`, `κ = ((paramsAt μ (a v)).d²·sideAt μ (a v))⁻¹`, `χ = chiLam ℓ`, `θ = thetaFun ℓ`,
* `Achan = ∫_{X n × (E³×E³)} Θ(x)·θ(x i)·ChAU(y, x j, u)·Θ(x[i↦y][j↦u])`,

the theorem says

    Achan = ℓ⁶ ∫_x Θ(x)χ(x i)χ(x j)·KfrU(x j − x i)·
              ∫_{u∈Λ(ℓ)} (Σ'_d lowKer fc κ (u − x j + ℓ•latVec d))·Q_jP_iΘ(x[j↦u]) .

The proof is the *two explicit integrations* of §2.1 of
`FINDING_PotCubicFreeU_exists_session8.md`:

1. `chanA_canonical` brings `Achan` into canonical form
   `∫ Θ'·Θ·θ(y)θ(u)·χ(x i)χ(x j)·Ksfr(u − x j)·KfrU(x j − x i)`;
2. `chan_int_y_generic` performs the `∫_y` step against `θ(y)`, producing the slot mean `P_i`
   (this is the definitional unfolding `ℓ³·aP = ∫_{acube}`, no analysis);
3. the auxiliary Fubini lemma `prod_theta_integral` turns the remaining product integral into an
   iterated one and converts `θ(u)` into the restricted integral `∫_{u∈acube ℓ}`;
4. `int_Ksfr_aP_eq_imageSum` performs the `∫_u` step: `Ksfr = ℓ³·Σ'_d lowKer(· + ℓ•latVec d) − 1`,
   the `−1` producing the `−Π` of `Q_jP_i = P_i − Π` against the tiling
   `Σ'_d ∫_{acube} lowKer = 1`;
5. the two `ℓ³` factors multiply to the `ℓ⁶` of the statement, and
   `G x := Θ(x)χ(x i)χ(x j)KfrU(x j − x i)` is the weight of the channel (its measurability,
   boundedness, box-support and the Fubini step are the two delegated facts `G_boxFacts`
   and `prod_theta_integral`).

The module is complete and axiom-clean.
-/

theorem Achan_eq_imageSum {n : ℕ} {i j : Fin n} (hij : i ≠ j)
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
          * Work.BoseBoxFock.PCFU.ChAU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * ∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)
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
  -- the `k`-frame bound
  set Ks : ℝ := ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      |Work.BoseBoxFock.fLh v fc μ N s| with hKsdef
  have hKs0 : 0 ≤ Ks := by rw [hKsdef]; exact Finset.sum_nonneg fun s _ => abs_nonneg _
  -- the weight `G` of the channel and the `u`-kernel `F`
  set G : Submission.BoseGases.X n → ℂ := fun x =>
      ((Θ x : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
        * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i) with hGdef
  set F : Submission.BoseGases.X n → E3 → ℂ := fun x u =>
      Work.BoseBoxFock.Ksfr v fc μ N (u - x j) with hFdef
  -- the three `G`-facts (measurability, bound, box-support) come from the delegated `G_boxFacts`
  obtain ⟨hGmLit, hGbLit, hGsLit⟩ := G_boxFacts (n := n) (i := i) (j := j)
      (ℓ := Work.BoseBoxFock.ellH v μ) (v := v) (h := h) (μ := μ) (fu := fu) (N := N)
      Θ hΘm Cθ hCθ hΘs
  have hGm : Measurable G := by rw [hGdef]; exact hGmLit
  have hGb : ∀ x, ‖G x‖ ≤ Cθ * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
      * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
      * ∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k| := by
    intro x
    rw [hGdef]
    exact hGbLit x
  have hGs : Function.support G ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ) := by
    rw [hGdef]
    exact hGsLit
  have hFm : Measurable (fun p : Submission.BoseGases.X n × E3 => F p.1 p.2) := by
    rw [hFdef]
    exact (Work.BoseBoxFock.PCFU.continuous_Ksfr.measurable).comp
      ((continuous_snd.sub ((continuous_apply j).comp continuous_fst))).measurable
  have hFb : ∀ p : Submission.BoseGases.X n × E3, ‖F p.1 p.2‖ ≤ Ks := by
    intro p
    rw [hFdef, hKsdef]
    exact Work.BoseBoxFock.PCFU.norm_Ksfr_le _
  -- the canonical form, then the `∫_y` step
  have hcanon := chanA_canonical hij v h fc fu μ N Θ hΘ hΘm ⟨Cθ, hCθn⟩
  have hbridge : (∫ q : Submission.BoseGases.X n × (E3 × E3),
        ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.1
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.2
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (q.1 i) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (q.1 j) : ℝ) : ℂ)
          * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 - q.1 j)
          * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (q.1 j - q.1 i))
      = ∫ q : Submission.BoseGases.X n × (E3 × E3),
          G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.2
            * F q.1 q.2.2 := by
    apply integral_congr_ae
    filter_upwards with q
    rw [hGdef, hFdef]
    ring
  have hY := chan_int_y_generic (n := n) (i := i) (j := j)
      (ℓ := Work.BoseBoxFock.ellH v μ) hℓ G hGm
      (Cθ * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
        * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
        * ∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k|)
      hGb hGs Θ hΘm Cθ hCθ F hFm Ks hFb
  -- the pointwise replacement of the "parametric" slot mean by `P_iΘ`
  have hP : (∫ p : Submission.BoseGases.X n × E3,
        G p.1 * F p.1 p.2 * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
          * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i
              (fun x' => Θ (Function.update x' j p.2)) p.1 : ℝ) : ℂ))
      = ∫ p : Submission.BoseGases.X n × E3,
          G p.1 * F p.1 p.2 * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) p.2
            * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                (Function.update p.1 j p.2) : ℝ) : ℂ) := by
    apply integral_congr_ae
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
      (Cθ * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
        * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
        * ∑ k : Work.BoseBoxFock.Lab N, |Work.BoseBoxFock.W1h v h μ fu N k|) hGb
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
  -- assembly
  calc (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChAU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = (∫ q : Submission.BoseGases.X n × (E3 × E3),
          ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * ((Θ q.1 : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.2
            * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (q.1 i) : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (q.1 j) : ℝ) : ℂ)
            * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 - q.1 j)
            * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (q.1 j - q.1 i)) := hcanon
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
          apply integral_congr_ae
          filter_upwards with p
          ring]
        rw [hFub, hFdef]
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (∫ x : Submission.BoseGases.X n, G x *
              (((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3 * J x)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with x
        congr 1
        exact hImg x
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * (((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
              * ∫ x : Submission.BoseGases.X n, G x * J x) := by
        congr 1
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        ring
    _ = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * ∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)
                * J x := by
        have hI : (∫ x : Submission.BoseGases.X n, G x * J x)
            = ∫ x : Submission.BoseGases.X n,
                (((Θ x : ℝ) : ℂ)
                  * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x i) : ℝ) : ℂ)
                  * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) (x j) : ℝ) : ℂ)
                  * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (x j - x i)) * J x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hGdef]
        rw [hI]
        ring

end Work.BoseBoxFock.PCFU
