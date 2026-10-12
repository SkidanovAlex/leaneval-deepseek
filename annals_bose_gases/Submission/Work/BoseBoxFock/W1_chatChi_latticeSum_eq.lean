import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB7AK.W1rows.chat_neg
import Submission.Work.BoseBoxFock.latSampling_uvSmear
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open Work.BoseFixR (chat W1fun)
open Work.BoseBoxFix (LowCut)
open Work.UBB (ScatSol)
open Work.BoseK15 (corpusBox)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-! ## 0. Elementary lattice algebra

The label group `Lab N = (ZMod (2N+1))³` sits in `ℤ³` through the centred representative
`labVec`, and the momentum of a label is `(2π/ℓ)` times the lattice vector.  These are the
identifications the Poisson sampling is written in. -/

private lemma latVec_neg (m : Fin 3 → ℤ) : latVec (-m) = -latVec m := by
  ext i
  show ((-m) i : ℝ) = -(m i : ℝ)
  simp

private lemma latVec_zero : latVec (0 : Fin 3 → ℤ) = (0 : E3) := by
  ext i
  show ((0 : Fin 3 → ℤ) i : ℝ) = (0 : E3) i
  simp

private lemma vec_eq_two_pi_smul_latVec (m : Fin 3 → ℤ) :
    Work.BoseB4.vec m = (2 * Real.pi) • latVec m := by
  refine PiLp.ext fun i => ?_
  simp only [Work.BoseB4.vec, latVec, WithLp.ofLp_smul, WithLp.ofLp_toLp, Pi.smul_apply,
    smul_eq_mul]

private lemma kmomLab_eq_smul_latVec (ℓ : ℝ) (N : ℕ) (k : Lab N) :
    kmomLab ℓ N k = (2 * Real.pi / ℓ) • latVec (labVec N k) := by
  rw [kmomLab, vec_eq_two_pi_smul_latVec, smul_smul]
  congr 1
  rw [div_eq_mul_inv]
  ring

private lemma labVec_zero (N : ℕ) : labVec N (0 : Lab N) = 0 := by
  funext i
  simp [labVec]

private lemma kmomLab_zero (ℓ : ℝ) (N : ℕ) : kmomLab ℓ N (0 : Lab N) = 0 := by
  rw [kmomLab_eq_smul_latVec, labVec_zero, latVec_zero, smul_zero]

private lemma uvRad_pos_one_le {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 1 ≤ N) :
    0 < uvRad ℓ N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [uvRad]
  exact div_pos (mul_pos (div_pos (by positivity) hℓ) hNpos) (by norm_num)

private lemma uvCut_eq_zero_of_two_mul_le {fu : LowCut} {Λ : ℝ} (hΛ : 0 < Λ)
    {k : E3} (hk : 2 * Λ ≤ ‖k‖) : uvCut fu Λ k = 0 := by
  rw [uvCut, fu.zero _ ?_]
  rw [le_div_iff₀ hΛ]
  linarith

/-- The UV cut-off vanishes on the ball where the momentum label exceeds `N/2`. -/
private lemma uvCut_smul_latVec_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 1 ≤ N)
    (fu : LowCut) {m : Fin 3 → ℤ} (hm : (N : ℝ) / 2 ≤ ‖latVec m‖) :
    uvCut fu (uvRad ℓ N) ((2 * Real.pi / ℓ) • latVec m) = 0 := by
  refine uvCut_eq_zero_of_two_mul_le (uvRad_pos_one_le hℓ hN) ?_
  have hc : 0 < 2 * Real.pi / ℓ := by positivity
  have h2 : 2 * uvRad ℓ N = (2 * Real.pi / ℓ) * ((N : ℝ) / 2) := by rw [uvRad]; ring
  rw [h2, norm_smul, Real.norm_of_nonneg hc.le]
  exact mul_le_mul_of_nonneg_left hm hc.le

/-- `labVec N` hits the whole cube `[-N,N]³`: the centred representative of `m i` in
`ZMod (2N+1)` is `m i` itself as soon as `|m i| ≤ N`. -/
private lemma labVec_mk (N : ℕ) {m : Fin 3 → ℤ}
    (hm : ∀ i : Fin 3, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ)) :
    labVec N (fun i => ((m i : ℤ) : ZMod (2 * N + 1))) = m := by
  funext i
  show (((m i : ℤ) : ZMod (2 * N + 1))).valMinAbs = m i
  haveI : NeZero (2 * N + 1) := ⟨by omega⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  rw [Set.mem_Ioc]
  obtain ⟨h1, h2⟩ := hm i
  constructor <;> omega

/-- **The lattice series is the `Lab N`-sum.**  A function on `ℤ³` whose support is contained
in the open `ℓ²`-ball of radius `N/2` has the same sum over all of `ℤ³` as over the labels
`Lab N` (the ball lies in the bijective image of the centred representatives). -/
private lemma tsum_eq_labSum (N : ℕ) {F : (Fin 3 → ℤ) → ℂ}
    (hF : ∀ m : Fin 3 → ℤ, (N : ℝ) / 2 ≤ ‖latVec m‖ → F m = 0) :
    (∑' m : Fin 3 → ℤ, F m) = ∑ k : Lab N, F (labVec N k) := by
  classical
  have hinj : Set.InjOn (labVec N) (↑(Finset.univ : Finset (Lab N)) : Set (Lab N)) :=
    fun a _ b _ hab => funext fun i => ZMod.valMinAbs_inj.mp (congrFun hab i)
  rw [tsum_eq_sum (s := (Finset.univ.image (labVec N) : Finset (Fin 3 → ℤ))) ?_,
    Finset.sum_image hinj]
  intro m hm
  by_contra hne
  have hlt : ‖latVec m‖ < (N : ℝ) := by
    by_contra hcon
    push_neg at hcon
    refine hne (hF m ?_)
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hcoord : ∀ i : Fin 3, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ) := by
    intro i
    have h1 : |((m i : ℤ) : ℝ)| ≤ ‖latVec m‖ := by
      have h2 := PiLp.norm_apply_le (latVec m) i
      rwa [latVec_apply] at h2
    have h3 : |((m i : ℤ) : ℝ)| < (N : ℝ) := lt_of_le_of_lt h1 hlt
    have h4 : |((m i : ℤ) : ℝ)| ≤ (N : ℝ) := le_of_lt h3
    rw [abs_le] at h4
    exact ⟨by exact_mod_cast h4.1, by exact_mod_cast h4.2⟩
  exact hm (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, labVec_mk N hcoord⟩)

/-! ## 1. The complex exponential identities

The integrand of the target combines the two Poisson terms at `y - w` and `y + w` into a
cosine; this is the elementary identity `½(e^{-i(a-t)} + e^{-i(a+t)}) = e^{-ia}cos t` with the
constant `c = Ŵ(k)` factored out. -/

private lemma two_cos_I (x : ℂ) :
    2 * Complex.cos x = Complex.exp (Complex.I * x) + Complex.exp (-(Complex.I * x)) := by
  have h1 : Complex.exp (Complex.I * x) = Complex.exp (x * Complex.I) := by rw [mul_comm]
  have h2 : Complex.exp (-(Complex.I * x)) = Complex.exp (-x * Complex.I) := by
    congr 1
    ring
  rw [h1, h2, ← Complex.two_cos]

private lemma ofReal_cos_eq (t : ℝ) :
    ((Real.cos t : ℝ) : ℂ)
      = (1 / 2 : ℂ) *
          (Complex.exp (Complex.I * (t : ℂ)) + Complex.exp (-(Complex.I * (t : ℂ)))) := by
  rw [Complex.ofReal_cos, ← two_cos_I]
  ring

private lemma half_exp_neg_add_mul (c : ℂ) (a t : ℝ) :
    (1 / 2 : ℂ) * (c * Complex.exp (-(Complex.I * ((a - t : ℝ) : ℂ)))
        + c * Complex.exp (-(Complex.I * ((a + t : ℝ) : ℂ))))
      = c * Complex.exp (-(Complex.I * (a : ℂ))) * ((Real.cos t : ℝ) : ℂ) := by
  have h1 : Complex.exp (-(Complex.I * ((a - t : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * (a : ℂ))) * Complex.exp (Complex.I * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (-(Complex.I * ((a + t : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * (a : ℂ))) * Complex.exp (-(Complex.I * (t : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, h2, ofReal_cos_eq]
  ring

/-! ## 2. Integrability and the elementary box integrals -/

private lemma chiLam_complex_continuous (ℓ : ℝ) :
    Continuous (fun w : E3 => ((corpusBox.chiLam ℓ w : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont corpusBox ℓ)

private lemma chiLam_complex_hasCompactSupport (ℓ : ℝ) (hℓ : 0 < ℓ) :
    HasCompactSupport (fun w : E3 => ((corpusBox.chiLam ℓ w : ℝ) : ℂ)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (Work.BoseB4.BoxData.boxL_compact corpusBox ℓ) ?_
  intro w hw
  refine Work.BoseB4.BoxData.chiLam_supp corpusBox hℓ (fun h => hw ?_)
  show ((corpusBox.chiLam ℓ w : ℝ) : ℂ) = 0
  rw [show corpusBox.chiLam ℓ w = 0 from h]
  simp

private lemma integrable_chiLam_complex (ℓ : ℝ) (hℓ : 0 < ℓ) :
    Integrable (fun w : E3 => ((corpusBox.chiLam ℓ w : ℝ) : ℂ)) :=
  (chiLam_complex_continuous ℓ).integrable_of_hasCompactSupport
    (chiLam_complex_hasCompactSupport ℓ hℓ)

private lemma integrable_chiLam_mul_cos (ℓ : ℝ) (hℓ : 0 < ℓ) (p : E3) :
    Integrable (fun w : E3 =>
      ((corpusBox.chiLam ℓ w : ℝ) : ℂ) * ((Real.cos (inner ℝ p w) : ℝ) : ℂ)) := by
  have hcont : Continuous (fun w : E3 => ((Real.cos (inner ℝ p w) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_cos.comp (continuous_const.inner continuous_id))
  have hcs : HasCompactSupport (fun w : E3 =>
      ((corpusBox.chiLam ℓ w : ℝ) : ℂ) * ((Real.cos (inner ℝ p w) : ℝ) : ℂ)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (Work.BoseB4.BoxData.boxL_compact corpusBox ℓ) ?_
    intro w hw
    refine Work.BoseB4.BoxData.chiLam_supp corpusBox hℓ (fun h => hw ?_)
    show ((corpusBox.chiLam ℓ w : ℝ) : ℂ) * ((Real.cos (inner ℝ p w) : ℝ) : ℂ) = 0
    rw [show corpusBox.chiLam ℓ w = 0 from h]
    simp
  exact ((chiLam_complex_continuous ℓ).mul hcont).integrable_of_hasCompactSupport hcs

/-- `∫ χ_Λ(w) cos⟪p,w⟫ dw = ℓ³ χ̂(ℓp)`, in the complex form used by the integrand. -/
private lemma integral_chiLam_mul_cos_complex (ℓ : ℝ) (hℓ : 0 < ℓ) (p : E3) :
    (∫ w : E3,
        ((corpusBox.chiLam ℓ w : ℝ) : ℂ) * ((Real.cos (inner ℝ p w) : ℝ) : ℂ))
      = ((ℓ ^ 3 * corpusBox.hatChi (ℓ • p) : ℝ) : ℂ) := by
  have hfun : (fun w : E3 => ((corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * ((Real.cos (inner ℝ p w) : ℝ) : ℂ))
      = fun w : E3 => (((corpusBox.chiLam ℓ w) * Real.cos (inner ℝ p w) : ℝ) : ℂ) := by
    funext w
    exact (Complex.ofReal_mul _ _).symm
  rw [hfun]
  refine (integral_ofReal (μ := volume) (𝕜 := ℂ)
    (f := fun w : E3 => corpusBox.chiLam ℓ w * Real.cos (inner ℝ p w))).trans ?_
  congr 1
  exact Work.BoseB4.BoxData.integral_chiLam_mul_cos corpusBox hℓ p

/-- Removing the `a`-th term of a finite sum: `Σ_{x} (if x = a then 0 else f x) = Σ f - f a`. -/
private lemma sum_ite_zero {α : Type*} [Fintype α] [DecidableEq α] (a : α) (f : α → ℂ) :
    (∑ x : α, if x = a then (0 : ℂ) else f x) = (∑ x : α, f x) - f a := by
  have hpt : ∀ x : α, (if x = a then (0 : ℂ) else f x) = f x - (if x = a then f x else 0) := by
    intro x
    by_cases h : x = a <;> simp [h]
  calc (∑ x : α, if x = a then (0 : ℂ) else f x)
      = ∑ x : α, (f x - (if x = a then f x else 0)) := Finset.sum_congr rfl fun x _ => hpt x
    _ = (∑ x : α, f x) - ∑ x : α, (if x = a then f x else 0) :=
        Finset.sum_sub_distrib _ _
    _ = (∑ x : α, f x) - f a := by
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ a)]

end

theorem W1_chatChi_latticeSum_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {fu : Work.BoseBoxFix.LowCut} (N : ℕ) (hN : 1 ≤ N) (y : EuclideanSpace ℝ (Fin 3))
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h ℓ))
    (hev : ∀ x, Work.BoseFixR.W1fun v h ℓ (-x) = Work.BoseFixR.W1fun v h ℓ x) :
    (∑ k : Work.BoseBoxFock.Lab N, if k = 0 then 0 else
        ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N) (Work.BoseBoxFock.kmomLab ℓ N k) *
          Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (Work.BoseBoxFock.kmomLab ℓ N k) *
            Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) y : ℂ))))
      = ((ℓ ^ (-3 : ℤ) : ℝ) : ℂ) * ∫ w : EuclideanSpace ℝ (Fin 3),
          ((Work.BoseK15.corpusBox.chiLam ℓ w : ℝ) : ℂ) * (1/2 : ℂ) *
            (((ℓ : ℂ) ^ 3 * (∑' d : Fin 3 → ℤ,
                ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N) (Work.BoseFixR.W1fun v h ℓ)
                  (y - w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
              - ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N) 0 * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0 : ℝ) : ℂ))
            + ((ℓ : ℂ) ^ 3 * (∑' d : Fin 3 → ℤ,
                ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N) (Work.BoseFixR.W1fun v h ℓ)
                  (y + w + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
              - ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N) 0 * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0 : ℝ) : ℂ))) := by
  classical
  set Wv : E3 → ℝ := uvSmear fu (uvRad ℓ N) (W1fun v h ℓ) with hWv
  have hΛpos : 0 < uvRad ℓ N := uvRad_pos_one_le hℓ hN
  -- **Step 1**: Poisson sampling of the smoothed weight, in the sign convention of the target
  have hP : ∀ z : E3,
      ((ℓ : ℂ) ^ 3) * (∑' d : Fin 3 → ℤ, ((Wv (z + ℓ • latVec d) : ℝ) : ℂ))
      = ∑' m : Fin 3 → ℤ, ((chat Wv ((2 * Real.pi / ℓ) • latVec m) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ))) := by
    intro z
    rw [hWv]
    have hps := latSampling_uvSmear (fu := fu) (Λ := uvRad ℓ N) hΛpos
      (f := W1fun v h ℓ) hI hcs hev hℓ z
    rw [← hps]
    rw [← tsum_comp_neg (f := fun m : Fin 3 → ℤ =>
      ((chat (uvSmear fu (uvRad ℓ N) (W1fun v h ℓ)) ((2 * Real.pi / ℓ) • latVec m) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ)))]
    refine tsum_congr fun m => ?_
    have h1 : ((chat (uvSmear fu (uvRad ℓ N) (W1fun v h ℓ)) ((2 * Real.pi / ℓ) • latVec (-m)) : ℝ) : ℂ)
        = ((chat (uvSmear fu (uvRad ℓ N) (W1fun v h ℓ)) ((2 * Real.pi / ℓ) • latVec m) : ℝ) : ℂ) := by
      congr 1
      rw [latVec_neg, smul_neg, Work.BoseB7AK.W1rows.chat_neg]
    have h2 : Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (-m)) z : ℂ))
        = Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ))) := by
      congr 1
      rw [latVec_neg, smul_neg, inner_neg_left]
      push_cast
      ring
    rw [h1, h2]
  -- **Step 2**: the reduction to the label group `Lab N`
  have hLab : ∀ z : E3,
      (∑' m : Fin 3 → ℤ, ((chat Wv ((2 * Real.pi / ℓ) • latVec m) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ))))
      = ∑ k : Lab N, ((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) z : ℂ))) := by
    intro z
    refine tsum_eq_labSum N (F := fun m : Fin 3 → ℤ =>
      ((chat Wv ((2 * Real.pi / ℓ) • latVec m) : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ)))) ?_
    intro m hm
    have hcut : uvCut fu (uvRad ℓ N) ((2 * Real.pi / ℓ) • latVec m) = 0 :=
      uvCut_smul_latVec_eq_zero hℓ hN fu hm
    have hch : chat Wv ((2 * Real.pi / ℓ) • latVec m) = 0 := by
      rw [hWv, chat_uvSmear (fu := fu) (Λ := uvRad ℓ N) hΛpos (f := W1fun v h ℓ) hI
        ((2 * Real.pi / ℓ) • latVec m), hcut, zero_mul]
    rw [hch]
    simp
  -- **Step 3**: the zero mode
  have hC0 : ((uvCut fu (uvRad ℓ N) 0 * chat (W1fun v h ℓ) 0 : ℝ) : ℂ) = ((chat Wv 0 : ℝ) : ℂ) := by
    congr 1
    rw [hWv, ← chat_uvSmear (fu := fu) (Λ := uvRad ℓ N) hΛpos (f := W1fun v h ℓ) hI 0]
  -- **Step 4**: the pointwise integrand identity
  have hpt : ∀ w : E3,
      ((corpusBox.chiLam ℓ w : ℝ) : ℂ) * (1 / 2 : ℂ)
        * ((((ℓ : ℂ) ^ 3) * (∑' d : Fin 3 → ℤ, ((Wv (y - w + ℓ • latVec d) : ℝ) : ℂ))
              - ((uvCut fu (uvRad ℓ N) 0 * chat (W1fun v h ℓ) 0 : ℝ) : ℂ))
          + (((ℓ : ℂ) ^ 3) * (∑' d : Fin 3 → ℤ, ((Wv (y + w + ℓ • latVec d) : ℝ) : ℂ))
              - ((uvCut fu (uvRad ℓ N) 0 * chat (W1fun v h ℓ) 0 : ℝ) : ℂ)))
      = ((corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * (∑ k : Lab N, if k = 0 then 0 else
              (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ)))
                * ((Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) w) : ℝ) : ℂ))) := by
    intro w
    rw [hP (y - w), hP (y + w), hLab (y - w), hLab (y + w), hC0]
    rw [mul_assoc]
    have hGk0 : (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N (0 : Lab N))) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N (0 : Lab N))) y : ℂ)))
          * ((Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N (0 : Lab N))) w) : ℝ) : ℂ))
        = ((chat Wv 0 : ℝ) : ℂ) := by
      rw [labVec_zero, latVec_zero, smul_zero]
      simp
    have hkey : (1 / 2 : ℂ) *
        (((∑ k : Lab N, ((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
              * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) (y - w) : ℂ))))
            - ((chat Wv 0 : ℝ) : ℂ))
          + ((∑ k : Lab N, ((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
              * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) (y + w) : ℂ))))
            - ((chat Wv 0 : ℝ) : ℂ)))
        = (∑ k : Lab N, if k = 0 then 0 else
              (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ)))
                * ((Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) w) : ℝ) : ℂ))) := by
      set SA : ℂ := (∑ k : Lab N, ((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) (y - w) : ℂ)))) with hSA
      set SB : ℂ := (∑ k : Lab N, ((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) (y + w) : ℂ)))) with hSB
      rw [show (1 / 2 : ℂ) * ((SA - ((chat Wv 0 : ℝ) : ℂ)) + (SB - ((chat Wv 0 : ℝ) : ℂ)))
            = (1 / 2 : ℂ) * (SA + SB) - ((chat Wv 0 : ℝ) : ℂ) from by ring,
        hSA, hSB, ← Finset.sum_add_distrib, Finset.mul_sum]
      have hfin : (∑ k : Lab N, (1 / 2 : ℂ) *
            ((((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) (y - w) : ℂ))))
              + (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) (y + w) : ℂ))))))
          = (∑ k : Lab N, (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ)))
                * ((Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) w) : ℝ) : ℂ))) :=
        Finset.sum_congr rfl fun k _ => by
          rw [inner_sub_right, inner_add_right]
          exact half_exp_neg_add_mul _ _ _
      rw [hfin, hGk0.symm, ← sum_ite_zero (0 : Lab N)]
    rw [hkey]
  -- **Step 5**: the integral
  have hIntAll : ∀ k ∈ (Finset.univ : Finset (Lab N)),
      Integrable (fun w : E3 => ((corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * (if k = 0 then 0 else
            (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
              * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ)))
              * ((Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) w) : ℝ) : ℂ)))) := by
    intro k _
    by_cases hk : k = 0
    · simp [hk]
    · simp only [if_neg hk]
      refine ((integrable_chiLam_mul_cos ℓ hℓ ((2 * Real.pi / ℓ) • latVec (labVec N k))).const_mul
        (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ))))).congr ?_
      filter_upwards with w
      ring
  have hint : (∫ w : E3, ((corpusBox.chiLam ℓ w : ℝ) : ℂ)
        * (∑ k : Lab N, if k = 0 then 0 else
              (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ)))
                * ((Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) w) : ℝ) : ℂ))))
      = ((ℓ : ℂ) ^ 3) * (∑ k : Lab N, if k = 0 then 0 else
              (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
                * ((corpusBox.hatChi (ℓ • ((2 * Real.pi / ℓ) • latVec (labVec N k))) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ))))) := by
    rw [show (fun w : E3 => ((corpusBox.chiLam ℓ w : ℝ) : ℂ)
          * (∑ k : Lab N, if k = 0 then 0 else
              (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ)))
                * ((Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) w) : ℝ) : ℂ))))
        = fun w : E3 => ∑ k : Lab N, ((corpusBox.chiLam ℓ w : ℝ) : ℂ)
            * (if k = 0 then 0 else
              (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ)))
                * ((Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) w) : ℝ) : ℂ))) from by
      funext w
      rw [Finset.mul_sum]]
    rw [integral_finsetSum (Finset.univ) hIntAll, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k = 0
    · simp [hk]
    · rw [show (fun w : E3 => ((corpusBox.chiLam ℓ w : ℝ) : ℂ)
            * (if k = 0 then 0 else
              (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ)))
                * ((Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) w) : ℝ) : ℂ))))
          = fun w : E3 => (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
              * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ))))
            * (((corpusBox.chiLam ℓ w : ℝ) : ℂ)
              * ((Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) w) : ℝ) : ℂ)) from by
        funext w
        simp only [if_neg hk]
        ring]
      rw [if_neg hk]
      rw [integral_const_mul, integral_chiLam_mul_cos_complex ℓ hℓ]
      push_cast
      ring
  -- **Step 6**: match the two sums termwise
  have hterm : ∀ k : Lab N,
      ((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
        * ((corpusBox.hatChi (ℓ • ((2 * Real.pi / ℓ) • latVec (labVec N k))) : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ)))
      = ((uvCut fu (uvRad ℓ N) (kmomLab ℓ N k) * chat (W1fun v h ℓ) (kmomLab ℓ N k)
            * corpusBox.hatChi (ℓ • kmomLab ℓ N k) : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ))) := by
    intro k
    rw [kmomLab_eq_smul_latVec]
    rw [hWv, chat_uvSmear (fu := fu) (Λ := uvRad ℓ N) hΛpos (f := W1fun v h ℓ) hI
      ((2 * Real.pi / ℓ) • latVec (labVec N k))]
    push_cast
    ring
  have hpow3 : ((ℓ ^ (-3 : ℤ) : ℝ) : ℂ) * ((ℓ : ℂ) ^ 3) = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul,
      show ℓ ^ (-3 : ℤ) * ℓ ^ 3 = 1 from by
        rw [zpow_neg]
        exact inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ))]
    simp
  rw [show (fun w : E3 => ((corpusBox.chiLam ℓ w : ℝ) : ℂ) * (1 / 2 : ℂ)
        * ((((ℓ : ℂ) ^ 3) * (∑' d : Fin 3 → ℤ, ((Wv (y - w + ℓ • latVec d) : ℝ) : ℂ))
              - ((uvCut fu (uvRad ℓ N) 0 * chat (W1fun v h ℓ) 0 : ℝ) : ℂ))
          + (((ℓ : ℂ) ^ 3) * (∑' d : Fin 3 → ℤ, ((Wv (y + w + ℓ • latVec d) : ℝ) : ℂ))
              - ((uvCut fu (uvRad ℓ N) 0 * chat (W1fun v h ℓ) 0 : ℝ) : ℂ))))
      = fun w : E3 => ((corpusBox.chiLam ℓ w : ℝ) : ℂ)
          * (∑ k : Lab N, if k = 0 then 0 else
              (((chat Wv ((2 * Real.pi / ℓ) • latVec (labVec N k)) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) y : ℂ)))
                * ((Real.cos (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N k)) w) : ℝ) : ℂ))) from by
    funext w
    rw [hpt w]]
  rw [hint]
  conv_rhs => rw [← mul_assoc, hpow3, one_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk, if_neg hk]
    exact (hterm k).symm

end Work.BoseBoxFock
