import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PCFU.Dchan_fubini_qw
import Submission.Work.BoseBoxFock.PCFU.Dchan_fubini_wx
import Submission.Work.BoseBoxFock.PCFU.Dchan_perW
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.Dchan_eq_imageSum` — the `(D)`-channel at the image sum

The `(D)`-twin of the proved `Work.BoseBoxFock.PCFU.Bchan_eq_imageSum`.  Writing
`ℓ = ellH v μ`, `χ = chiLam ℓ`, `θ = thetaFun ℓ`, the theorem computes

    Dchan = ∫ Θ(x)·θ(x i)·ChDU(y, x j, u)·Θ(x[i↦y][j↦u])

as `ℓ³` times the image-sum integral of the low cut-off kernel against the fibre
deviation `Q_jP_iΘ`, with the `(D)`-weight `χ_Λ(w)KχfrU(w)` (a function of the
*third* slot) in place of the `(A)`/`(B)` `χ`-weights.

The proof is the three-step reduction of `chanD_canonical`:

1. `Dchan_fubini_qw` — Fubini over the frame variable `w`, moving the `w`-integral
   out of the `q`-integral;
2. `Dchan_perW` — for each fixed `w`, the `∫_y`/`∫_u` steps (`chan_int_y_generic`,
   `prod_theta_integral`) and the `Ksfr_eq_lowKer` identity
   `int_Ksfr_aP_eq_imageSum_gen` (with shift `b = −w`), producing
   `ℓ⁶∫_x Θ(x)θ(x j)θ(x i)·Γ_j(Q_jP_iΘ)(x)`;
3. `Dchan_fubini_wx` — the Fubini over `(w, x)`, and the removal of the two
   sharp-box factors `θ(x j)θ(x i)`, which are `1` on the support of `Θ`
   (`chiRow_aP_abox_facts`).

The two remaining `ℓ`-factors are `ℓ⁻³·ℓ⁶ = ℓ³`.
-/

namespace Work.BoseBoxFock.PCFU

theorem Dchan_eq_imageSum {n : ℕ} {i j : Fin n} (hij : i ≠ j)
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
          * Work.BoseBoxFock.PCFU.ChDU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * ∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * (∫ w : EuclideanSpace ℝ (Fin 3),
                    ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                      * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w
                      * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                          (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                                (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                                  * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                                (u + w + Work.BoseBoxFock.ellH v μ
                                  • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                            * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                                (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                                (Function.update x j u) : ℝ) : ℂ))) := by
  obtain ⟨Cθ, hCθ⟩ := hΘb
  have hθb : ∃ C : ℝ, ∀ x, |Θ x| ≤ C := ⟨Cθ, hCθ⟩
  have hCθn : ∀ x, ‖Θ x‖ ≤ Cθ := fun x => by rw [Real.norm_eq_abs]; exact hCθ x
  -- the canonical form of the `(D)`-channel
  have hcanon := chanD_canonical hij v h fc fu μ N Θ hΘ hΘm ⟨Cθ, hCθn⟩
  rw [hcanon]
  -- step 1: the Fubini over the frame variable `w`
  rw [Dchan_fubini_qw hij v h fc fu μ N hℓ Θ hΘ hΘm hθb hΘs]
  -- step 2: the per-`w` reduction (the two `∫_y`, `∫_u` steps and `Ksfr = ℓ³ΣlowKer − 1`)
  have hper : ∀ w : EuclideanSpace ℝ (Fin 3),
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
                            (Function.update x j u) : ℝ) : ℂ)) :=
    fun w => Dchan_perW hij v h fc fu μ N hℓ hκ hN Θ hΘ hΘm hθb hΘs w
  simp only [hper]
  -- abbreviations for the three surviving objects
  let Z : EuclideanSpace ℝ (Fin 3) → ℂ := fun w => ∫ x : Submission.BoseGases.X n,
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
                  (Function.update x j u) : ℝ) : ℂ))
  let f0 : EuclideanSpace ℝ (Fin 3) → ℂ := fun w =>
      ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
        * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w
  let f1 : EuclideanSpace ℝ (Fin 3) → ℂ := fun w =>
      ((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ) * f0 w
  change (∫ w : EuclideanSpace ℝ (Fin 3),
        f1 w * (((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6 * Z w))
      = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3
          * ∫ x : Submission.BoseGases.X n,
              ((Θ x : ℝ) : ℂ)
                * (∫ w : EuclideanSpace ℝ (Fin 3),
                    ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                      * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w
                      * (∫ u in Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ),
                          (∑' d : Fin 3 → ℤ, ((Work.BoseBoxFock.PCFU.lowKer fc
                                (((Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2
                                  * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹)
                                (u + w + Work.BoseBoxFock.ellH v μ
                                  • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
                            * ((Submission.BoseGases.aQ (Work.BoseBoxFock.ellH v μ) j
                                (Submission.BoseGases.aP (Work.BoseBoxFock.ellH v μ) i Θ)
                                (Function.update x j u) : ℝ) : ℂ)))
  -- the two `ℓ`-powers: `ℓ⁻³·ℓ⁶ = ℓ³`
  have hconst : ((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)
      * ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6 = ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3 := by
    have hne : ((Work.BoseBoxFock.ellH v μ : ℂ)) ≠ 0 := by
      simpa [Complex.ofReal_eq_zero] using (ne_of_gt hℓ)
    have h1 : ((Work.BoseBoxFock.ellH v μ ^ (-(3 : ℤ)) : ℝ) : ℂ)
        = (((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3)⁻¹ := by
      rw [Complex.ofReal_zpow, zpow_neg]; norm_num
    rw [h1, show ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6
        = (((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3)
          * (((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3)
        from by ring, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 hne), one_mul]
  have hfold : (∫ w : EuclideanSpace ℝ (Fin 3),
        f1 w * (((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 6 * Z w))
      = ∫ w : EuclideanSpace ℝ (Fin 3),
          ((Work.BoseBoxFock.ellH v μ : ℂ)) ^ 3 * (f0 w * Z w) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    simp only [f1]
    rw [← hconst]
    ring
  rw [hfold, MeasureTheory.integral_const_mul]
  congr 1
  -- step 3: the Fubini over `(w, x)`
  rw [Dchan_fubini_wx v h fc fu μ N hℓ hκ hN Θ hΘm hθb hΘs]
  -- the two sharp-box factors are `1` on the support of `Θ`
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  by_cases hx : Θ x = 0
  · rw [hx]; simp
  · have hxmem : x ∈ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ) :=
      hΘs (Function.mem_support.mpr hx)
    have hθj : Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x j) = 1 :=
      (Work.BoseBoxFock.chiRow_aP_abox_facts (n := n)
        (ℓ := Work.BoseBoxFock.ellH v μ) hℓ).2.1 hxmem j
    have hθi : Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) (x i) = 1 :=
      (Work.BoseBoxFock.chiRow_aP_abox_facts (n := n)
        (ℓ := Work.BoseBoxFock.ellH v μ) hℓ).2.1 hxmem i
    rw [hθj, hθi]; ring

end Work.BoseBoxFock.PCFU
