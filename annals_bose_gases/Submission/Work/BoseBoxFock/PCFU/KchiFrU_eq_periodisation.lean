import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseBoxFock.Kchifr_eq
import Submission.Work.BoseBoxFock.PCFU.UnivFrames
import Submission.Work.BoseBoxFock.uvSmear_L1_tendsto
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.KchiFrU_eq_periodisation`

The `χ̂`-weighted `univ` frame `KχfrU` (the `k`-sum over **all** labels, without the removal of
the zero mode) is the periodisation of the UV-smoothed weight against the box window:

`KχfrU v h μ fu N z = ∫_w χ_Λ(w) Σ'_d (ψ_Λ ⋆ W₁)(z − w + ℓ·latVec d) dw`,  `ℓ = ellH v μ`.

## Route

* `W1_frame_periodisation` — the Poisson sampling identity of `W1_latticeSum_eq` **without** the
  subtracted zero mode.  Since `W1_latticeSum_eq` writes the `lab N`-sum without its `k = 0` term
  and subtracts exactly that term on the right, adding the zero mode back (its value is
  `ζ_Λ(0)·Ŵ₁(0)` and `kmomLab ℓ N 0 = 0`) gives

      Σ_k Ŵ₁(k)·e^{i⟨k,y⟩} = ℓ³ Σ'_d (ψ_Λ ⋆ W₁)(y + ℓ d).

* `integral_chiLam_exp` (PROVED, `integral_chiLam_exp.lean`) evaluates the window against the
  conjugate plane wave: `∫ χ_Λ(w)e^{−i⟨p,w⟩}dw = ℓ³χ̂(ℓp)`.

* Hence, integrating the periodisation against `χ_Λ` and swapping the (finite) `Lab N`-sum with
  the integral (`integral_finsetSum` + `integral_const_mul`), every summand contributes
  `Ŵ₁(k)·χ̂(ℓk)e^{i⟨k,z⟩}`, which is exactly `KχfrU`.  The `ℓ³` of the Poisson identity cancels
  the `ℓ^{-3}` of the window transform.

Everything is `sorry`-free; the only inputs are the PROVED `W1_latticeSum_eq`,
`integral_chiLam_exp`, `hasCompactSupport_chiLam_complex` and the elementary box facts of
`Work.BoseB4.BoxData`.
-/

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary label facts -/

/-- The zero label carries momentum `0`. -/
private lemma kmomLab_zero_pcfu (ℓ : ℝ) (N : ℕ) : kmomLab ℓ N (0 : Lab N) = 0 := by
  have h0 : labVec N (0 : Lab N) = 0 := by
    funext i
    simp [labVec]
  rw [kmomLab, h0]
  ext i
  simp [Work.BoseB4.vec]

/-- A sum with the `a`-th term replaced by `0` is the full sum minus that term. -/
private lemma sum_ite_zero_pcfu {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (f : ι → ℂ) :
    (∑ x : ι, if x = a then (0 : ℂ) else f x) = (∑ x : ι, f x) - f a := by
  have h1 : (∑ x : ι, (if x = a then (0 : ℂ) else f x))
      = ∑ x : ι, (f x - (if x = a then f x else 0)) :=
    Finset.sum_congr rfl (fun x _ => by by_cases hx : x = a <;> simp [hx])
  rw [h1, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ a)]

/-! ## 2. The periodisation of `W₁` on the box lattice, without the subtracted zero mode -/

/-- **The `univ` frame of `W₁` is the periodisation of the smoothed weight**:
`Σ_{k∈Lab N} ζ_Λ(k)Ŵ₁(k)e^{i⟨k,y⟩} = ℓ³ Σ'_d (ψ_Λ ⋆ W₁)(y + ℓ·latVec d)`.

This is `Work.BoseBoxFock.W1_latticeSum_eq` with the zero mode added back on both sides. -/
private lemma W1_frame_periodisation {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 1 ≤ N)
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h ℓ))
    (hev : ∀ x, Work.BoseFixR.W1fun v h ℓ (-x) = Work.BoseFixR.W1fun v h ℓ x)
    (y : E3) :
    (∑ k : Lab N,
        ((uvCut fu (uvRad ℓ N) (kmomLab ℓ N k)
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (kmomLab ℓ N k) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)))
      = (ℓ : ℂ) ^ 3 * (∑' d : Fin 3 → ℤ,
          ((uvSmear fu (uvRad ℓ N) (Work.BoseFixR.W1fun v h ℓ) (y + ℓ • latVec d) : ℝ) : ℂ)) := by
  have hpois := W1_latticeSum_eq (v := v) (h := h) (ℓ := ℓ) hℓ (fu := fu) N hN y hI hcs hev
  have hsplit := sum_ite_zero_pcfu (0 : Lab N) (fun k : Lab N =>
      ((uvCut fu (uvRad ℓ N) (kmomLab ℓ N k)
          * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (kmomLab ℓ N k) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)))
  rw [hsplit] at hpois
  have h0 : ((uvCut fu (uvRad ℓ N) (kmomLab ℓ N (0 : Lab N))
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (kmomLab ℓ N (0 : Lab N)) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N (0 : Lab N)) y : ℂ))
      = ((uvCut fu (uvRad ℓ N) 0 * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0 : ℝ) : ℂ) := by
    simp [kmomLab_zero_pcfu]
  rw [h0] at hpois
  have h3 := congrArg (fun x : ℂ => x + ((uvCut fu (uvRad ℓ N) 0
      * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0 : ℝ) : ℂ)) hpois
  simpa [sub_add_cancel] using h3

/-! ## 3. Integrability of the window against a shifted plane wave -/

private lemma integrable_chiLam_mul_exp_neg (ℓ : ℝ) (hℓ : 0 < ℓ) (p : E3) (c : ℂ) :
    MeasureTheory.Integrable (fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * (c * Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))))) := by
  have hc : Continuous (fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont Work.BoseK15.corpusBox ℓ)
  have he : Continuous (fun w : E3 => Complex.exp (-(Complex.I * (inner ℝ p w : ℂ)))) := by
    refine Complex.continuous_exp.comp ?_
    refine Continuous.neg ?_
    exact continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))
  exact (hc.mul (continuous_const.mul he)).integrable_of_hasCompactSupport
    (HasCompactSupport.mul_right (hasCompactSupport_chiLam_complex ℓ hℓ))

/-- `e^{i⟨p,y−w⟩} = e^{i⟨p,y⟩}·e^{−i⟨p,w⟩}`. -/
private lemma exp_sub_split (p zy w : E3) :
    Complex.exp (Complex.I * (inner ℝ p (zy - w) : ℂ))
      = Complex.exp (Complex.I * (inner ℝ p zy : ℂ))
        * Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))) := by
  rw [inner_sub_right]
  push_cast
  rw [← Complex.exp_add]
  congr 1
  ring

private lemma integrable_chiLam_mul_exp_sub (ℓ : ℝ) (hℓ : 0 < ℓ) (p : E3) (t : ℂ) (zy : E3) :
    MeasureTheory.Integrable (fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * (t * Complex.exp (Complex.I * (inner ℝ p (zy - w) : ℂ)))) := by
  refine (integrable_chiLam_mul_exp_neg ℓ hℓ p
    (t * Complex.exp (Complex.I * (inner ℝ p zy : ℂ)))).congr ?_
  refine Filter.Eventually.of_forall (fun w => ?_)
  simp only [exp_sub_split p zy w, mul_assoc]

/-! ## 4. The value of one summand -/

/-- `∫_w χ_Λ(w)·t·e^{i⟨p,y−w⟩}dw = ℓ³·t·χ̂(ℓp)·e^{i⟨p,y⟩}`. -/
private lemma integral_chiLam_term (ℓ : ℝ) (hℓ : 0 < ℓ) (p : E3) (t : ℂ) (zy : E3) :
    ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * (t * Complex.exp (Complex.I * (inner ℝ p (zy - w) : ℂ)))
      = ((ℓ : ℂ) ^ 3) * (t * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ p zy : ℂ))) := by
  rw [show (fun w : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * (t * Complex.exp (Complex.I * (inner ℝ p (zy - w) : ℂ))))
      = (fun w : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * (t * Complex.exp (Complex.I * (inner ℝ p zy : ℂ))
            * Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))))) from by
      funext w; rw [exp_sub_split p zy w]; ring]
  rw [show (fun w : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * (t * Complex.exp (Complex.I * (inner ℝ p zy : ℂ))
            * Complex.exp (-(Complex.I * (inner ℝ p w : ℂ)))))
      = (fun w : E3 => (t * Complex.exp (Complex.I * (inner ℝ p zy : ℂ)))
        * (((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))))) from by
      funext w; ring]
  rw [MeasureTheory.integral_const_mul]
  rw [show (fun w : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))))
      = (fun w : E3 => Complex.exp (-(Complex.I * (inner ℝ p w : ℂ)))
        * ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ)) from by
      funext w; ring]
  rw [integral_chiLam_exp hℓ p, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-! ## 5. The target -/

theorem KchiFrU_eq_periodisation {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}
    (hℓ0 : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (hN : 1 ≤ N)
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hev : ∀ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (-x) = Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
      = ((∫ w : EuclideanSpace ℝ (Fin 3), (((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ)) : ℂ) *
            (∑' d : Fin 3 → ℤ, (((Work.BoseBoxFock.uvSmear fu
                (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
                (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                (z - w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ)) : ℂ))) : ℂ) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hside : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by rw [ellH, if_pos hℓ0]
  have h3 : ((ellH v μ : ℂ) ^ 3) ≠ 0 := by
    rw [← Complex.ofReal_pow]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact pow_ne_zero _ (ne_of_gt hℓ)
  -- the pointwise Poisson identity, with the zero mode kept
  have hT : ∀ w : E3, (∑' d : Fin 3 → ℤ,
        ((uvSmear fu (uvRad (ellH v μ) N) (Work.BoseFixR.W1fun v h (ellH v μ))
          (z - w + (ellH v μ) • latVec d) : ℝ) : ℂ))
      = ((ellH v μ : ℂ) ^ 3)⁻¹ * ∑ k : Lab N,
          ((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (z - w) : ℂ)) := by
    intro w
    have hp := W1_frame_periodisation (v := v) (h := h) (fu := fu) (ℓ := ellH v μ) hℓ
      (N := N) hN hI hcs hev (z - w)
    have hW1 : ∀ k : Lab N, W1h v h μ fu N k
        = uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
          * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ)) (kmomLab (ellH v μ) N k) := by
      intro k; simp only [W1h, ← hside]
    have hL : (∑ k : Lab N, ((uvCut fu (uvRad (ellH v μ) N) (kmomLab (ellH v μ) N k)
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (ellH v μ))
              (kmomLab (ellH v μ) N k) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (z - w) : ℂ)))
        = ∑ k : Lab N, ((W1h v h μ fu N k : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (z - w) : ℂ)) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hW1 k]
    rw [hL] at hp
    rw [hp, ← mul_assoc, inv_mul_cancel₀ h3, one_mul]
  -- integrability of each summand
  have hint : ∀ k : Lab N, MeasureTheory.Integrable (fun w : E3 =>
      ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * (((W1h v h μ fu N k : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (z - w) : ℂ)))) :=
    fun k => integrable_chiLam_mul_exp_sub (ellH v μ) hℓ (kmomLab (ellH v μ) N k)
      ((W1h v h μ fu N k : ℝ) : ℂ) z
  have step1 : (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) *
        (∑' d : Fin 3 → ℤ, ((uvSmear fu (uvRad (ellH v μ) N) (Work.BoseFixR.W1fun v h (ellH v μ))
          (z - w + (ellH v μ) • latVec d) : ℝ) : ℂ)))
      = ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) *
          (((ellH v μ : ℂ) ^ 3)⁻¹ * ∑ k : Lab N, ((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (z - w) : ℂ))) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => by simp only [hT w]))
  have hfun2 : (fun w : E3 => ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) *
        (((ellH v μ : ℂ) ^ 3)⁻¹ * ∑ k : Lab N, ((W1h v h μ fu N k : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (z - w) : ℂ))))
      = (fun w : E3 => ∑ k : Lab N, ((ellH v μ : ℂ) ^ 3)⁻¹ *
          (((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * (((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (z - w) : ℂ))))) := by
    funext w
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hsum2 : (∑ k : Lab N, ∫ w : E3, ((ellH v μ : ℂ) ^ 3)⁻¹ *
          (((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * (((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (z - w) : ℂ)))))
      = ∑ k : Lab N, ((ellH v μ : ℂ) ^ 3)⁻¹ *
          (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * (((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (z - w) : ℂ)))) :=
    Finset.sum_congr rfl (fun k _ => MeasureTheory.integral_const_mul _ _)
  have step2 : (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) *
        (((ellH v μ : ℂ) ^ 3)⁻¹ * ∑ k : Lab N, ((W1h v h μ fu N k : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (z - w) : ℂ))))
      = ((ellH v μ : ℂ) ^ 3)⁻¹ * ∑ k : Lab N, ∫ w : E3,
          ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * (((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (z - w) : ℂ))) := by
    rw [hfun2, MeasureTheory.integral_finsetSum _ (fun k _ => (hint k).const_mul _),
      hsum2, ← Finset.mul_sum]
  have step3 : (∑ k : Lab N, ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * (((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (z - w) : ℂ))))
      = ∑ k : Lab N, ((ellH v μ : ℂ) ^ 3) * (((W1h v h μ fu N k : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ellH v μ • kmomLab (ellH v μ) N k) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))) :=
    Finset.sum_congr rfl (fun k _ => integral_chiLam_term (ellH v μ) hℓ
      (kmomLab (ellH v μ) N k) ((W1h v h μ fu N k : ℝ) : ℂ) z)
  have step4 : ((ellH v μ : ℂ) ^ 3)⁻¹ * (∑ k : Lab N, ((ellH v μ : ℂ) ^ 3) *
        (((W1h v h μ fu N k : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ellH v μ • kmomLab (ellH v μ) N k) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))))
      = ∑ k : Lab N, (((W1h v h μ fu N k * hatChih v μ N k : ℝ)) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hatChih, Complex.ofReal_mul]
    rw [← mul_assoc, inv_mul_cancel₀ h3, one_mul]
  have hmain : (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ) *
        (∑' d : Fin 3 → ℤ, ((uvSmear fu (uvRad (ellH v μ) N) (Work.BoseFixR.W1fun v h (ellH v μ))
          (z - w + (ellH v μ) • latVec d) : ℝ) : ℂ)))
      = ∑ k : Lab N, (((W1h v h μ fu N k * hatChih v μ N k : ℝ)) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ)) := by
    rw [step1, step2, step3, step4]
  exact hmain.symm

end Work.BoseBoxFock.PCFU
