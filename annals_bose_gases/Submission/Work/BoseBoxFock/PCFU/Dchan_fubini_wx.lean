import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseBoxFock.PCFU.Bchan_eq_imageSum
import Submission.Work.BoseBoxFock.PCFU.int_Ksfr_aP_eq_imageSum_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.Dchan_fubini_wx` — the `w`/`x` Fubini swap of the `(D)`-channel

The target is the exchange of the two *outer* integrations of the `(D)`-channel of `MiddleU`:

    ∫_w χ_Λ(w)·KχfrU(w)·∫_x Θ(x)θ(x_j)θ(x_i)∫_u Κ(u+w)·Q_jP_iΘ
      = ∫_x Θ(x)θ(x_j)θ(x_i)∫_w χ_Λ(w)·KχfrU(w)·∫_u Κ(u+w)·Q_jP_iΘ .

Both sides are the iterated integral of the *same* jointly measurable function
`F(w, x) = A(w)·(B(x)·C(w,x))` with

* `A(w) = χ_Λ(w)·KχfrU(w)` — the `w`-weight,
* `B(x) = Θ(x)·θ(x_j)·θ(x_i)` — the `x`-weight,
* `C(w,x) = ∫_{acube} (∑'_d Κ(u + w + ℓ·latVec d))·(Q_jP_iΘ)(x[j↦u])` — the `u`-integral.

Hence the statement is `MeasureTheory.integral_integral_swap` **provided** `F` is integrable for
`volume.prod volume`.  That is the only real content:

* `χ_Λ` is continuous with compact support (`BoxData.chiLam_cont`, `BoxData.chiLam_supp`), so it is
  *bounded* on the compact box `boxL ℓ` and *supported* in it;
* `Θ` is bounded and supported in `abox n ℓ` (`hΘb`, `hΘs`);
* `KχfrU` is a finite sum of plane waves, hence bounded by `∑_k |Ŵ₁(k)χ̂(ℓκ_k)|`
  (`PCFU.norm_KχfrU_le`);
* finally, the *crucial* boundedness of the inner `u`-integral: the image sum of the low-cut kernel
  is **not** estimated by decay, but *identified* with the `s`-frame via the proved
  `PCFU.Ksfr_eq_lowKer`:

      ℓ³·∑'_d Κ(z + ℓ·latVec d) = Ksfr(z) + 1 ,

  and `Ksfr` is again a finite sum of plane waves (`PCFU.norm_Ksfr_le`).  This gives the *uniform*
  bound `|C(w,x)| ≤ 2·C_Θ·(K_s + 1)` in `w` **and** `x`, which is what makes the joint integrand
  bounded on the finite-measure set `boxL ℓ ×ˢ abox n ℓ`.

Everything here is `sorry`-free.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## 1. The image sum of the low cut-off kernel, in the `s`-frame form

`PCFU.Ksfr_eq_lowKer` evaluates the `s`-frame as `ℓ³·∑'_d Κ(· + ℓ•latVec d) − 1`; this is the
identity that turns the *decaying* image sum into the *bounded* frame. -/

/-- **The image sum in the `s`-frame form**: `∑'_d Κ(z + ℓ•latVec d) = (Ksfr z + 1)/ℓ³`. -/
private lemma imageSum_eq_Ksfr {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ)) (z : E3) :
    (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
        (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
        (z + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
      = (Work.BoseBoxFock.Ksfr v fc μ N z + 1) / ((Work.BoseBoxFock.ellH v μ : ℂ) ^ 3) := by
  have h := Ksfr_eq_lowKer (v := v) (fc := fc) (μ := μ) (N := N) hℓ hκ hN z
  have h3 : ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3 ≠ 0 := by
    rw [← Complex.ofReal_pow, ne_eq, Complex.ofReal_eq_zero]
    exact pow_ne_zero 3 (ne_of_gt hℓ)
  rw [eq_div_iff h3, h]
  ring

/-- **Uniform bound on the image sum**: `‖∑'_d Κ(z + ℓ•latVec d)‖ ≤ (C + 1)/ℓ³` whenever
`‖Ksfr‖` is bounded by `C` (e.g. `C = ∑_{s∈excited}|f_L(s)|`, by `PCFU.norm_Ksfr_le`). -/
private lemma imageSum_norm_le {v : E3 → ℝ} {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    {C : ℝ}
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ))
    (hC : ∀ z, ‖Work.BoseBoxFock.Ksfr v fc μ N z‖ ≤ C) (z : E3) :
    ‖(∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
        (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
        (z + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖
      ≤ (C + 1) / (Work.BoseBoxFock.ellH v μ) ^ 3 := by
  rw [imageSum_eq_Ksfr hℓ hκ hN z, norm_div]
  have h3 : ‖((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3‖ = (Work.BoseBoxFock.ellH v μ) ^ 3 := by
    rw [← Complex.ofReal_pow]
    rw [show ‖(((Work.BoseBoxFock.ellH v μ) ^ 3 : ℝ) : ℂ)‖
        = |(Work.BoseBoxFock.ellH v μ) ^ 3| from norm_ofReal_eq_abs _]
    exact abs_of_nonneg (by positivity)
  rw [h3]
  gcongr
  calc ‖Work.BoseBoxFock.Ksfr v fc μ N z + 1‖
        ≤ ‖Work.BoseBoxFock.Ksfr v fc μ N z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ C + 1 := by
        rw [norm_one]; exact add_le_add (hC z) le_rfl

/-! ## 2. Boundedness of `χ_Λ` -/

/-- `χ_Λ` is continuous with support in the compact box `boxL ℓ`, hence bounded. -/
private lemma chiLam_bound (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : E3,
      ‖((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)‖ ≤ C := by
  have hcont : Continuous fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont _ ℓ)
  obtain ⟨C, hC⟩ := (Work.BoseB4.BoxData.boxL_compact (B := Work.BoseK15.corpusBox) ℓ)
    |>.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun w => ?_⟩
  by_cases hw : Work.BoseK15.corpusBox.chiLam ℓ w = 0
  · rw [hw]; simp
  · have hmem : w ∈ Work.BoseK15.corpusBox.boxL ℓ :=
      Work.BoseB4.BoxData.chiLam_supp (B := Work.BoseK15.corpusBox) hℓ
        (Function.mem_support.mpr hw)
    exact le_trans (hC w hmem) (le_max_left _ _)

/-! ## 3. Measurability of the inner `u`-integral -/

/-- The slot mean `aP ℓ i Θ` is measurable when `Θ` is (it is a parametric integral of a jointly
measurable function). -/
private lemma measurable_aP_self {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘm : Measurable Θ) :
    Measurable (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ i Θ y) := by
  haveI : SFinite ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := inferInstance
  have hm : StronglyMeasurable
      (fun p : Submission.BoseGases.X n × E3 => Θ (Function.update p.1 i p.2)) :=
    (hΘm.comp (measurable_update' (a := i))).stronglyMeasurable
  have h := hm.integral_prod_right' (ν := (volume : Measure E3).restrict
    (Submission.BoseGases.acube ℓ))
  unfold Submission.BoseGases.aP
  exact (h.const_mul (1 / ℓ ^ 3)).measurable

/-- **Measurability of the `u`-integral** in the `s`-frame form, as a function of `(w, x)`. -/
private lemma measurable_chanInner {n : ℕ} (i j : Fin n) {v : E3 → ℝ}
    {fc : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Θ : Submission.BoseGases.X n → ℝ} (hΘm : Measurable Θ) :
    Measurable (fun p : E3 × Submission.BoseGases.X n =>
      ∫ u in Submission.BoseGases.acube ℓ,
        ((Work.BoseBoxFock.Ksfr v fc μ N (u + p.1) + 1) / ((ℓ : ℂ) ^ 3))
          * ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
              (Function.update p.2 j u) : ℝ) : ℂ)) := by
  haveI : SFinite ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := inferInstance
  have hK : Continuous (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
      Work.BoseBoxFock.Ksfr v fc μ N (q.2 + q.1.1)) :=
    (Work.BoseBoxFock.PCFU.continuous_Ksfr).comp (continuous_snd.add continuous_fst.fst)
  have haP : Measurable (fun y : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ i Θ y) := measurable_aP_self hℓ i hΘm
  have haPP : Measurable (fun y : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) y) := measurable_aP_self hℓ j haP
  have hupd : Measurable (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
      Function.update q.1.2 j q.2) :=
    measurable_update'.comp ((measurable_fst.snd).prodMk measurable_snd)
  have haQ : Measurable (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
      ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
        (Function.update q.1.2 j q.2) : ℝ) : ℂ)) := by
    simp only [Submission.BoseGases.aQ, Complex.ofReal_sub]
    exact (Complex.measurable_ofReal.comp (haP.comp hupd)).sub
      (Complex.measurable_ofReal.comp (haPP.comp hupd))
  have hjoint : Measurable (fun q : (E3 × Submission.BoseGases.X n) × E3 =>
      ((Work.BoseBoxFock.Ksfr v fc μ N (q.2 + q.1.1) + 1) / ((ℓ : ℂ) ^ 3))
        * ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
            (Function.update q.1.2 j q.2) : ℝ) : ℂ)) :=
    (((hK.add continuous_const).measurable).div_const _).mul haQ
  exact (hjoint.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))).measurable

/-! ## 4. The target -/

theorem Dchan_fubini_wx {n : ℕ} {i j : Fin n}
    (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (μ : ℝ) (N : ℕ)
    (hℓ : 0 < Work.BoseBoxFock.ellH v μ)
    (hκ : 0 < ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
    (hN : 2 * (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹) * Work.BoseBoxFock.ellH v μ
          / (2 * Real.pi) ≤ (N : ℝ))
    (Θ : Submission.BoseGases.X n → ℝ) (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ w : EuclideanSpace ℝ (Fin 3),
        ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
          * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w
          * (∫ x : Submission.BoseGases.X n,
              (((Θ x : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j)
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i))
                * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                    (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                          (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                            * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                          (u + w + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                      * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                          (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                          (Function.update x j u) : ℝ) : ℂ))))
      = ∫ x : Submission.BoseGases.X n,
          (((Θ x : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i))
            * (∫ w : EuclideanSpace ℝ (Fin 3),
                ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                  * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w
                  * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                      (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                            (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                              * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                            (u + w + Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                        * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                            (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                            (Function.update x j u) : ℝ) : ℂ))) := by
  obtain ⟨Cθ, hCθ⟩ := hΘb
  have hCθ0 : 0 ≤ Cθ := le_trans (abs_nonneg (Θ 0)) (hCθ 0)
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓdef
  set κs : ℝ := ((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
      * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ with hκdef
  have hℓpos : 0 < ℓ := hℓ
  have hκpos : 0 < κs := hκ
  set A : E3 → ℂ := fun w => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
      * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w with hA
  set B : Submission.BoseGases.X n → ℂ := fun x => ((Θ x : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun ℓ (x j)
      * Work.BoseK15.corpusBox.thetaFun ℓ (x i) with hB
  set C : E3 → Submission.BoseGases.X n → ℂ := fun w x =>
      ∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc κs
            (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        * ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
            (Function.update x j u) : ℝ) : ℂ) with hC
  change (∫ w : E3, A w * (∫ x : Submission.BoseGases.X n, B x * C w x))
      = ∫ x : Submission.BoseGases.X n, B x * (∫ w : E3, A w * C w x)
  obtain ⟨Cχ, hCχ0, hCχ⟩ := chiLam_bound ℓ hℓpos
  set Kw : ℝ := ∑ k : Work.BoseBoxFock.Lab N,
      |Work.BoseBoxFock.W1h v h μ fu N k * Work.BoseBoxFock.hatChih v μ N k| with hKw
  have hKw0 : 0 ≤ Kw := by rw [hKw]; exact Finset.sum_nonneg (fun k _ => abs_nonneg _)
  set Ks : ℝ := ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      |Work.BoseBoxFock.fLh v fc μ N s| with hKs
  have hKs0 : 0 ≤ Ks := by rw [hKs]; exact Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hKsb : ∀ z : E3, ‖Work.BoseBoxFock.Ksfr v fc μ N z‖ ≤ Ks := by
    intro z; rw [hKs]; exact norm_Ksfr_le z
  have hKwb : ∀ z : E3, ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z‖ ≤ Kw := by
    intro z; rw [hKw]; exact norm_KχfrU_le v h μ fu N z
  have hAb : ∀ w : E3, ‖A w‖ ≤ Cχ * Kw := by
    intro w
    change ‖((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
      * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w‖ ≤ Cχ * Kw
    rw [norm_mul]
    exact mul_le_mul (hCχ w) (hKwb w) (norm_nonneg _) hCχ0
  have hBb : ∀ x : Submission.BoseGases.X n, ‖B x‖ ≤ Cθ := by
    intro x
    change ‖((Θ x : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ (x j)
        * Work.BoseK15.corpusBox.thetaFun ℓ (x i)‖ ≤ Cθ
    have hx : ‖((Θ x : ℝ) : ℂ)‖ = |Θ x| := norm_ofReal_eq_abs _
    calc ‖((Θ x : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ (x j)
            * Work.BoseK15.corpusBox.thetaFun ℓ (x i)‖
        ≤ ‖((Θ x : ℝ) : ℂ)‖ * ‖Work.BoseK15.corpusBox.thetaFun ℓ (x j)‖
            * ‖Work.BoseK15.corpusBox.thetaFun ℓ (x i)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ Cθ * 1 * 1 := by
          rw [hx]
          gcongr
          · exact hCθ x
          · exact norm_thetaFun_le_one ℓ (x j)
          · exact norm_thetaFun_le_one ℓ (x i)
      _ = Cθ := by ring
  have hCb : ∀ w (x : Submission.BoseGases.X n), ‖C w x‖ ≤ 2 * Cθ * (Ks + 1) := by
    intro w x
    change ‖(∫ u in Submission.BoseGases.acube ℓ,
        (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc κs
            (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
        * ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
            (Function.update x j u) : ℝ) : ℂ))‖ ≤ 2 * Cθ * (Ks + 1)
    haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
      ⟨by rw [Measure.restrict_apply_univ]
          exact Submission.BoseGases.acube_lt_top ℓ hℓpos.le⟩
    have haQb : ∀ u : E3, ‖((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
        (Function.update x j u) : ℝ) : ℂ)‖ ≤ 2 * Cθ := by
      intro u
      rw [norm_ofReal_eq_abs]
      have h1 : ∀ y : Submission.BoseGases.X n, |Submission.BoseGases.aP ℓ i Θ y| ≤ Cθ :=
        fun y => Work.BoseBoxFock.Weak.aP_abs_le hℓpos i hCθ0 hCθ y
      have h2 : |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ)
          (Function.update x j u)| ≤ Cθ :=
        Work.BoseBoxFock.Weak.aP_abs_le hℓpos j hCθ0 h1 _
      simp only [Submission.BoseGases.aQ]
      calc |Submission.BoseGases.aP ℓ i Θ (Function.update x j u)
              - Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ)
                  (Function.update x j u)|
          ≤ _ + _ := abs_sub _ _
        _ ≤ Cθ + Cθ := add_le_add (h1 _) h2
        _ = 2 * Cθ := by ring
    have hbd : ∀ᵐ u ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)),
        ‖(∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc κs
            (u + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
          * ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
              (Function.update x j u) : ℝ) : ℂ)‖ ≤ (2 * Cθ * (Ks + 1)) / ℓ ^ 3 := by
      refine Filter.Eventually.of_forall (fun u => ?_)
      rw [norm_mul]
      refine le_trans (mul_le_mul
        (imageSum_norm_le (v := v) (fc := fc) (μ := μ) (N := N) (C := Ks)
          hℓpos hκpos hN hKsb (u + w))
        (haQb u) (norm_nonneg _) (div_nonneg (by linarith) (by positivity))) ?_
      rw [hℓdef]
      exact le_of_eq (by ring)
    have hmain := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) hbd
    rw [Submission.BoseGases.real_volume_acube ℓ hℓpos.le] at hmain
    exact le_trans hmain (le_of_eq (by rw [div_mul_cancel₀ _ (pow_ne_zero 3 (ne_of_gt hℓpos))]))
  have hJoint : Integrable (fun p : E3 × Submission.BoseGases.X n =>
      A p.1 * (B p.2 * C p.1 p.2)) (volume : Measure (E3 × Submission.BoseGases.X n)) := by
    refine integrable_of_bounded_support
      (s := Work.BoseK15.corpusBox.boxL ℓ ×ˢ Submission.BoseGases.abox n ℓ)
      (M := Cχ * Kw * Cθ * (2 * Cθ * (Ks + 1))) ?hs ?hm ?hb ?hsp
    · change (volume.prod volume : Measure (E3 × Submission.BoseGases.X n))
        (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Submission.BoseGases.abox n ℓ) < ⊤
      rw [Measure.prod_prod]
      exact ENNReal.mul_lt_top
        (by rw [Work.BoseB4.BoxData.volume_boxL (B := Work.BoseK15.corpusBox) hℓpos]
            exact ENNReal.ofReal_lt_top)
        (Submission.BoseGases.abox_lt_top n ℓ hℓpos.le)
    · have hAm : Measurable A := by
        rw [hA]
        exact (Complex.measurable_ofReal.comp
          (Work.BoseB4.BoxData.chiLam_cont _ ℓ).measurable).mul
          (measurable_KχfrU v h μ fu N)
      have hBm : Measurable B := by
        rw [hB]
        exact ((Complex.measurable_ofReal.comp hΘm).mul
          ((measurable_thetaFun hℓpos).comp (measurable_pi_apply j))).mul
          ((measurable_thetaFun hℓpos).comp (measurable_pi_apply i))
      have hCm : Measurable (fun p : E3 × Submission.BoseGases.X n => C p.1 p.2) := by
        change Measurable (fun p : E3 × Submission.BoseGases.X n =>
          ∫ u in Submission.BoseGases.acube ℓ,
            (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc κs
              (u + p.1 + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
              * ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
                  (Function.update p.2 j u) : ℝ) : ℂ))
        have heq : (fun p : E3 × Submission.BoseGases.X n =>
            ∫ u in Submission.BoseGases.acube ℓ,
              (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc κs
                (u + p.1 + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                * ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
                    (Function.update p.2 j u) : ℝ) : ℂ))
            = (fun p : E3 × Submission.BoseGases.X n =>
            ∫ u in Submission.BoseGases.acube ℓ,
              ((Work.BoseBoxFock.Ksfr v fc μ N (u + p.1) + 1) / ((ℓ : ℂ) ^ 3))
                * ((Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
                    (Function.update p.2 j u) : ℝ) : ℂ)) := by
          funext p
          refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
            (fun u _ => ?_)
          rw [imageSum_eq_Ksfr (v := v) (fc := fc) (μ := μ) (N := N) hℓpos hκpos hN (u + p.1)]
        rw [heq]
        exact measurable_chanInner i j hℓpos hΘm
      exact (hAm.comp measurable_fst).mul ((hBm.comp measurable_snd).mul hCm)
    · intro p
      have h1 : ‖A p.1‖ ≤ Cχ * Kw := hAb p.1
      have h2 : ‖B p.2‖ ≤ Cθ := hBb p.2
      have h3 : ‖C p.1 p.2‖ ≤ 2 * Cθ * (Ks + 1) := hCb p.1 p.2
      have h4 : 0 ≤ ‖B p.2‖ * ‖C p.1 p.2‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc ‖A p.1 * (B p.2 * C p.1 p.2)‖
          ≤ ‖A p.1‖ * ‖B p.2 * C p.1 p.2‖ := norm_mul_le _ _
        _ ≤ ‖A p.1‖ * (‖B p.2‖ * ‖C p.1 p.2‖) :=
            mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ Cχ * Kw * (Cθ * (2 * Cθ * (Ks + 1))) :=
            mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) hCθ0) h4 (mul_nonneg hCχ0 hKw0)
        _ = Cχ * Kw * Cθ * (2 * Cθ * (Ks + 1)) := by ring
    · intro p hp
      by_cases h1 : p.1 ∈ Work.BoseK15.corpusBox.boxL ℓ
      · have h2 : p.2 ∉ Submission.BoseGases.abox n ℓ :=
          fun h2 => hp (by rw [Set.mem_prod]; exact ⟨h1, h2⟩)
        have hz : B p.2 = 0 := by
          change ((Θ p.2 : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ (p.2 j)
            * Work.BoseK15.corpusBox.thetaFun ℓ (p.2 i) = 0
          have hc : Θ p.2 = 0 := by
            by_contra hne
            exact h2 (hΘs (Function.mem_support.mpr hne))
          rw [hc]; simp
        change A p.1 * (B p.2 * C p.1 p.2) = 0
        rw [hz, zero_mul, mul_zero]
      · have hz : A p.1 = 0 := by
          change ((Work.BoseK15.corpusBox.chiLam ℓ p.1 : ℝ) : ℂ)
            * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N p.1 = 0
          have hc : Work.BoseK15.corpusBox.chiLam ℓ p.1 = 0 := by
            by_contra hne
            exact h1 (Work.BoseB4.BoxData.chiLam_supp (B := Work.BoseK15.corpusBox) hℓpos
              (Function.mem_support.mpr hne))
          rw [hc]; simp
        change A p.1 * (B p.2 * C p.1 p.2) = 0
        rw [hz, zero_mul]
  have hswap := MeasureTheory.integral_integral_swap
    (μ := (volume : Measure E3)) (ν := (volume : Measure (Submission.BoseGases.X n)))
    (f := fun (w : E3) (x : Submission.BoseGases.X n) => A w * (B x * C w x)) hJoint
  have hL : (∫ w : E3, A w * (∫ x : Submission.BoseGases.X n, B x * C w x))
      = ∫ w : E3, ∫ x : Submission.BoseGases.X n, A w * (B x * C w x) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    exact (MeasureTheory.integral_const_mul (A w)
      (fun x : Submission.BoseGases.X n => B x * C w x)).symm
  have hR : (∫ x : Submission.BoseGases.X n, B x * (∫ w : E3, A w * C w x))
      = ∫ x : Submission.BoseGases.X n, ∫ w : E3, A w * (B x * C w x) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    change B x * (∫ w : E3, A w * C w x) = ∫ w : E3, A w * (B x * C w x)
    rw [show (∫ w : E3, A w * (B x * C w x)) = ∫ w : E3, B x * (A w * C w x) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => by ring))]
    exact (MeasureTheory.integral_const_mul (B x) (fun w : E3 => A w * C w x)).symm
  rw [hL, hswap, ← hR]

end

end Work.BoseBoxFock.PCFU
