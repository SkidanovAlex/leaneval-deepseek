import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PCFU.aPSlotFacts
import Submission.Work.BoseBoxFock.PCFU.chanBCD_canonical
import Submission.Work.BoseBoxFock.PCFU.int_Ksfr_aP_eq_imageSum_gen
import Submission.Work.BoseBoxFock.PCFU.prod_theta_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- **The `(D)`-channel of `MiddleU` at a *fixed* frame shift `w`** (the `perW` form).

With `ℓ = ellH v μ`, `θ = thetaFun ℓ`, an arbitrary shift `w : ℝ³`, the `(D)`-channel
canonical form

    ∫_{X n × (ℝ³×ℝ³)} Θ'·Θ·θ(y)θ(x j)θ(u)θ(x i)·Ksfr(u+w)

reduces, by the two explicit integrations of the cubic dictionary
(`FINDING_PotCubicFreeU_exists_session8.md` §2.1 and §3),

1. `chan_int_y_generic` — the `∫_y` step against `θ(y)`, producing the slot mean
   `P_iΘ = aP ℓ i Θ` with the volume factor `ℓ³`;
2. `prod_theta_integral` — the Fubini step turning `θ(u)` into `∫_{u∈acube ℓ}`;
3. `int_Ksfr_aP_eq_imageSum_gen` at the shift `b = −w` — the `Ksfr = ℓ³·Σ'_d lowKer(·+ℓ•latVec d) − 1`
   evaluation of `Ksfr_eq_lowKer`, the `−1` cancelling against the tiling
   `Σ'_d ∫_{acube} lowKer = 1` and producing the fibre deviation `Q_j(P_iΘ) = aQ ℓ j (aP ℓ i Θ)`:

    = ℓ⁶ ∫_x Θ(x)θ(x j)θ(x i)·∫_{u∈acube ℓ} (Σ'_d lowKer(u+w+ℓ•latVec d))·Q_jP_iΘ(x[j↦u]) .

This is the `w`-parametrised atom out of which `Dchan_eq_imageSum` is assembled by a Fubini step
in `w` against `χ_Λ(w)·KχfrU(w)`. -/
theorem Dchan_perW {n : ℕ} {i j : Fin n} (hij : i ≠ j)
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
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ))
    (w : EuclideanSpace ℝ (Fin 3)) :
    (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.1)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 j)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.2)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
          * ∫ x : Submission.BoseGases.X n,
              (((Θ x : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j)
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i))
                * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                    (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                          (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                            * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                          (u + w + Work.BoseBoxFock.ellH v μ
                            • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                      * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                          (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                          (Function.update x j u) : ℝ) : ℂ)) := by
  obtain ⟨Cθ, hCθ⟩ := hΘb
  have hCθ0 : 0 ≤ Cθ := le_trans (abs_nonneg (Θ 0)) (hCθ 0)
  have hCθn : ∀ x, ‖Θ x‖ ≤ Cθ := fun x => by rw [Real.norm_eq_abs]; exact hCθ x
  have hCθnc : ∀ x, ‖(((Θ x : ℝ)) : ℂ)‖ ≤ Cθ :=
    fun x => by rw [norm_ofReal_eq_abs]; exact hCθ x
  -- the uniform bound of the `s`-frame
  set Ks : ℝ := ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      |Work.BoseBoxFock.fLh v fc μ N s| with hKsdef
  have hKs0 : 0 ≤ Ks := by rw [hKsdef]; exact Finset.sum_nonneg fun s _ => abs_nonneg _
  -- the channel weight `G` and the shifted frame `F`
  set G : Submission.BoseGases.X n → ℂ := fun x =>
      ((Θ x : ℝ) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j)
        * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i) with hGdef
  set F : Submission.BoseGases.X n → E3 → ℂ := fun x u =>
      Work.BoseBoxFock.Ksfr v fc μ N (u + w) with hFdef
  have hGm : Measurable G := by
    rw [hGdef]
    have h1 : Measurable fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp hΘm
    have h2 : Measurable fun x : Submission.BoseGases.X n =>
        Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j) :=
      (measurable_thetaFun hℓ).comp (measurable_pi_apply j)
    have h3 : Measurable fun x : Submission.BoseGases.X n =>
        Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i) :=
      (measurable_thetaFun hℓ).comp (measurable_pi_apply i)
    exact (h1.mul h2).mul h3
  have hGb : ∀ x, ‖G x‖ ≤ Cθ := by
    intro x
    rw [hGdef]
    calc ‖((Θ x : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i)‖
        = ‖((Θ x : ℝ) : ℂ)‖
            * ‖Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j)‖
            * ‖Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ Cθ * 1 * 1 :=
          mul_le_mul (mul_le_mul (hCθnc x) (norm_thetaFun_le_one _ _) (norm_nonneg _) hCθ0)
            (norm_thetaFun_le_one _ _) (norm_nonneg _) (by positivity)
      _ = Cθ := by ring
  have hGs : Function.support G ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ) := by
    intro x hx
    apply hΘs
    rw [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by rw [hGdef]; simp [h0])
  have hFm : Measurable (fun p : Submission.BoseGases.X n × E3 => F p.1 p.2) := by
    rw [hFdef]
    exact (continuous_Ksfr (v := v) (fc := fc) (μ := μ) (N := N)).measurable.comp
      (continuous_snd.add continuous_const).measurable
  have hFb : ∀ p : Submission.BoseGases.X n × E3, ‖F p.1 p.2‖ ≤ Ks := by
    intro p
    rw [hFdef, hKsdef]
    exact norm_Ksfr_le (p.2 + w)
  -- the target integrand, regrouped to the shape consumed by `chan_int_y_generic`
  have hbridge : (∫ q : Submission.BoseGases.X n × (E3 × E3),
        ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.1)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 j)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.2)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w))
      = ∫ q : Submission.BoseGases.X n × (E3 × E3),
          G q.1 * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) q.2.2
            * F q.1 q.2.2 := by
    apply integral_congr_ae
    filter_upwards with q
    rw [hGdef, hFdef]
    ring
  -- step 1: the `∫_y` integration against `θ(y)`, giving the slot mean `P_iΘ`
  have hY := chan_int_y_generic (n := n) (i := i) (j := j)
      (ℓ := Work.BoseBoxFock.ellH v μ) hℓ G hGm Cθ hGb hGs Θ hΘm Cθ hCθ F hFm Ks hFb
  -- the parametric slot mean is the slot mean of `Θ`
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
    apply integral_congr_ae
    filter_upwards with p
    rw [aP_comp_update_eq (ℓ := Work.BoseBoxFock.ellH v μ) hij Θ p.1 p.2]
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
    rw [norm_ofReal_eq_abs]
    exact hAPb
  -- step 1bis: Fubini, converting `θ(u)` into the restricted integral `∫_{u∈acube ℓ}`
  have hFub := prod_theta_integral (n := n) (ℓ := Work.BoseBoxFock.ellH v μ) hℓ
      G hGm hGs Cθ hGb
      (fun x u => F x u * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
          (Function.update x j u) : ℝ) : ℂ)) hHm (Ks * Cθ) hHb
  -- step 2: the `lowKer` image split of the shifted frame, at the shift `b = -w`
  have hImg : ∀ x : Submission.BoseGases.X n,
      (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
          Work.BoseBoxFock.Ksfr v fc μ N (u + w)
            * ((Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ
                (Function.update x j u) : ℝ) : ℂ))
        = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
            * ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                      (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                      (u + w + Work.BoseBoxFock.ellH v μ
                        • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                  * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                      (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                      (Function.update x j u) : ℝ) : ℂ) := by
    intro x
    simpa only [sub_neg_eq_add] using
      int_Ksfr_aP_eq_imageSum_gen (v := v) (fc := fc) (μ := μ) (N := N)
        hℓ hκ hN i j (-w) Θ hΘm ⟨Cθ, hCθn⟩ x
  -- the position-space image integral `J`
  set J : Submission.BoseGases.X n → ℂ := fun x =>
      ∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
        (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
              (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
              (u + w + Work.BoseBoxFock.ellH v μ
                • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
              (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
              (Function.update x j u) : ℝ) : ℂ) with hJdef
  calc (∫ q : Submission.BoseGases.X n
          × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
          * ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.1)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 j)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.2.2)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (q.1 i)
          * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w))
      = (∫ q : Submission.BoseGases.X n × (E3 × E3),
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
                (Work.BoseBoxFock.Ksfr v fc μ N (u + w)
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
              (((Θ x : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j)
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i))
                * J x := by
        have hI : (∫ x : Submission.BoseGases.X n, G x * J x)
            = ∫ x : Submission.BoseGases.X n,
                (((Θ x : ℝ) : ℂ)
                  * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j)
                  * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i))
                  * J x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hGdef]
        rw [hI]
        ring

end Work.BoseBoxFock.PCFU
