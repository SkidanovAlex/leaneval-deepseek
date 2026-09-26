import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KfunClearSharp
import Submission.Work.Asymptotics.FunnelFar
import Submission.Work.Asymptotics.Kaxis_local_coincidence
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.KernelFacts.KMinus_T2
import Submission.Work.Asymptotics.MFix.Cusp0Flat
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero
import Submission.Work.Asymptotics.HalfFunnel.jLowerNear

/-!
# Flatness of the CKMRV kernel on the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}`

The target `Work.Asymptotics.HalfFunnel.funnelFlat` bounds the contour kernel
`t ↦ Kaxis (Kfun ℓ d) τ t` on the funnel by `C (1 + 1/t)^m e^{-c/t}`.

The proof uses the *far* case (proved in `Work.Asymptotics.FunnelFar`: away from the three
points `i/t`, `±1 + i/t` where `j` meets `j(it)`) and a *near* case which is handled by a
one-zero (Cauchy/Maximum-principle) argument on the pole-cleared kernel
`KfunClear = growthPrefactor · Kfun`, using

* the vanishing of `KfunClear` at the three coincidence points
  (`KClear_S_vanishing`, `KPlusClear_TS`/`KMinusClear_TS`, and the `T⁻¹S` translate),
* the sharp cleared bound `KfunClearSharp` on the funnel (and its `T`-translate extension to
  `Re τ ∈ (1,2]` obtained from the second-difference equation `(T-I)² = 0`),
* the quantitative lower bound `jLowerNear` for `j(τ) - j(it)`.

The three regimes are assembled at the very end: the *far* regime is bounded by
`C_f (1+1/t)^{m_f} e^{-c_f/t}`, the *near, small `t`* regime by `C_A (1+1/t)^{m_A} e^{-π/t}`,
and the *near, large `t`* regime by a pure constant `C_M`; taking
`c = min c_f π`, `m = max m_f m_A` and the appropriate maximum for `C` gives the claim.
-/

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm UpperHalfPlane Topology Manifold

namespace Work.Asymptotics.HalfFunnel

noncomputable section

set_option maxHeartbeats 4000000

open Work.Kernels Filter

/-! ## `(T-I)^2` annihilation -/

lemma T2op_const_mul (c : ℂ) (F : ℍ → ℂ) :
    T2op (fun τ => c * F τ) = fun τ => c * T2op F τ := by
  ext τ; simp only [T2op]; ring

lemma Kfun_T2 (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    T2op (fun τ : ℍ => Kfun ℓ d τ z) = 0 := by
  have hp := KernelFacts.KPlus_T2 d hd z
  have hm := KernelFacts.KMinus_T2 ℓ d hd z
  have hsplit : (fun τ : ℍ => Kfun ℓ d τ z)
      = fun τ => ((2:ℂ)⁻¹ * KPlus d τ z) + ((2:ℂ)⁻¹ * KMinus ℓ d τ z) := by
    funext τ; simp only [Kfun]; ring
  rw [hsplit, T2op_add', T2op_const_mul, T2op_const_mul, hp, hm]
  ext τ; simp

lemma growthPrefactor_vadd_one (d : ℕ) (z : ℍ) (τ : ℍ) :
    growthPrefactor d ((1:ℝ) +ᵥ τ) z = growthPrefactor d τ z := by
  simp only [growthPrefactor, KernelFacts.DeltaFun_vadd_one, KernelFacts.jInvariantFun_vadd_one]

lemma PiMatDelta_vadd_one (v : Fin 3 → ℤ) (τ : ℍ) :
    PiMatDelta v ((1 : ℝ) +ᵥ τ) = PiMatDelta v τ := by
  unfold PiMatDelta
  simp only [KernelFacts.DeltaFun_vadd_one, KernelFacts.fk_vadd_one]

lemma UpsilonPlusClear_vadd_one (d : ℕ) (z : ℍ) (i j : Fin 3) (τ : ℍ) :
    UpsilonPlusClear d ((1:ℝ) +ᵥ τ) z i j = UpsilonPlusClear d τ z i j := by
  simp only [UpsilonPlusClear]
  split_ifs with h8 h24 <;>
    simp only [PiMatDelta_vadd_one, KernelFacts.jInvariantFun_vadd_one]

lemma UpsilonMinusClear_vadd_one (d : ℕ) (z : ℍ) (i j : Fin 3) (τ : ℍ) :
    UpsilonMinusClear d ((1:ℝ) +ᵥ τ) z i j = UpsilonMinusClear d τ z i j := by
  simp only [UpsilonMinusClear]
  split_ifs with h8 h24 <;>
    simp only [PiMatDelta_vadd_one, KernelFacts.jInvariantFun_vadd_one]

lemma KPlusClear_T2' (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    T2op (fun τ : ℍ => KPlusClear d τ z) = 0 := by
  have _ := hd
  have hsum : ∀ τ : ℍ, KPlusClear d τ z
      = ∑ i : Fin 3, phiVec τ i *
          (∑ j : Fin 3, UpsilonPlusClear d τ z i j * phitVec z j) := by
    intro τ
    simp only [KPlusClear]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hcoeff : ∀ i : Fin 3, ∀ τ : ℍ,
      (∑ j : Fin 3, UpsilonPlusClear d ((1 : ℝ) +ᵥ τ) z i j * phitVec z j) =
        (∑ j : Fin 3, UpsilonPlusClear d τ z i j * phitVec z j) := by
    intro i τ
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [UpsilonPlusClear_vadd_one]
  have : (fun τ : ℍ => KPlusClear d τ z)
      = ∑ i : Fin 3, (fun τ : ℍ => phiVec τ i) *
          (fun τ : ℍ => ∑ j : Fin 3, UpsilonPlusClear d τ z i j * phitVec z j) := by
    funext τ; simpa only [Finset.sum_apply, Pi.mul_apply] using hsum τ
  rw [this]
  refine T2op_sum Finset.univ (fun i _ => ?_)
  exact T2op_mul_of (KernelFacts.phiVec_T2 i) (fun τ => hcoeff i τ)

lemma KMinusClear_T2' (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    T2op (fun τ : ℍ => KMinusClear ℓ d τ z) = 0 := by
  have _ := hd
  have hsum : ∀ τ : ℍ, KMinusClear ℓ d τ z
      = ∑ i : Fin 3, psiVec ℓ τ i *
          (∑ j : Fin 3, UpsilonMinusClear d τ z i j * psitVec ℓ z j) := by
    intro τ
    simp only [KMinusClear]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hcoeff : ∀ i : Fin 3, ∀ τ : ℍ,
      (∑ j : Fin 3, UpsilonMinusClear d ((1 : ℝ) +ᵥ τ) z i j * psitVec ℓ z j) =
        (∑ j : Fin 3, UpsilonMinusClear d τ z i j * psitVec ℓ z j) := by
    intro i τ
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [UpsilonMinusClear_vadd_one]
  have : (fun τ : ℍ => KMinusClear ℓ d τ z)
      = ∑ i : Fin 3, (fun τ : ℍ => psiVec ℓ τ i) *
          (fun τ : ℍ => ∑ j : Fin 3, UpsilonMinusClear d τ z i j * psitVec ℓ z j) := by
    funext τ; simpa only [Finset.sum_apply, Pi.mul_apply] using hsum τ
  rw [this]
  refine T2op_sum Finset.univ (fun i _ => ?_)
  exact T2op_mul_of (KernelFacts.psiVec_T2_km ℓ i) (fun τ => hcoeff i τ)

lemma KfunClear_T2 (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    T2op (fun τ : ℍ => KfunClear ℓ d τ z) = 0 := by
  have hp := KPlusClear_T2' d hd z
  have hm := KMinusClear_T2' ℓ d hd z
  have hsplit : (fun τ : ℍ => KfunClear ℓ d τ z)
      = fun τ => ((2:ℂ)⁻¹ * KPlusClear d τ z) + ((2:ℂ)⁻¹ * KMinusClear ℓ d τ z) := by
    funext τ; simp only [KfunClear]; ring
  rw [hsplit, T2op_add', T2op_const_mul, T2op_const_mul, hp, hm]
  ext τ; simp

/-! ## elementary geometry helpers -/

lemma DomainD_of_re_im (w : ℍ) (hre : |w.re| < 1) (him : 2 ≤ w.im) : w ∈ DomainD := by
  rw [DomainD]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (abs_lt.mp hre).1; linarith
  · exact (abs_lt.mp hre).2
  · have h := Complex.abs_im_le_norm ((w:ℂ) - (1/2:ℂ))
    have h2 : ((w:ℂ) - (1/2:ℂ)).im = w.im := by simp [Complex.sub_im, UpperHalfPlane.coe_im]
    rw [h2, abs_of_pos w.im_pos] at h; linarith
  · have h := Complex.abs_im_le_norm ((w:ℂ) + (1/2:ℂ))
    have h2 : ((w:ℂ) + (1/2:ℂ)).im = w.im := by simp [Complex.add_im, UpperHalfPlane.coe_im]
    rw [h2, abs_of_pos w.im_pos] at h; linarith

lemma norm_vadd_le' (x : ℝ) (z : ℍ) : ‖((x +ᵥ z : ℍ) : ℂ)‖ ≤ ‖x‖ + ‖(z:ℂ)‖ := by
  rw [UpperHalfPlane.coe_vadd]
  have h : ‖x‖ = ‖(x:ℂ)‖ := (Complex.norm_real x).symm
  rw [h]; exact norm_add_le _ _

lemma one_vadd_neg_one (x : ℍ) : (1:ℝ) +ᵥ ((-1:ℝ) +ᵥ x) = x := by
  rw [← add_vadd]; norm_num

lemma two_vadd_neg_two (x : ℍ) : (2:ℝ) +ᵥ ((-2:ℝ) +ᵥ x) = x := by
  rw [← add_vadd]; norm_num

lemma one_vadd_neg_two (x : ℍ) : (1:ℝ) +ᵥ ((-2:ℝ) +ᵥ x) = (-1:ℝ) +ᵥ x := by
  rw [← add_vadd]; norm_num

lemma jInvariantFun_vadd_neg_one (w : ℍ) :
    jInvariantFun ((-1:ℝ) +ᵥ w) = jInvariantFun w := by
  rw [← KernelFacts.jInvariantFun_vadd_one ((-1:ℝ) +ᵥ w), one_vadd_neg_one w]

lemma jInvariantFun_vadd_neg_two (w : ℍ) :
    jInvariantFun ((-2:ℝ) +ᵥ w) = jInvariantFun w := by
  have a : jInvariantFun ((-1:ℝ) +ᵥ w) = jInvariantFun w := jInvariantFun_vadd_neg_one w
  have b : jInvariantFun ((-2:ℝ) +ᵥ w) = jInvariantFun ((-1:ℝ) +ᵥ w) := by
    rw [← KernelFacts.jInvariantFun_vadd_one ((-2:ℝ) +ᵥ w), one_vadd_neg_two w]
  rw [b, a]

lemma re_vadd' (x : ℝ) (z : ℍ) : (x +ᵥ z).re = x + z.re := by
  rw [← UpperHalfPlane.coe_re, UpperHalfPlane.coe_vadd]; simp

lemma im_vadd' (x : ℝ) (z : ℍ) : (x +ᵥ z).im = z.im := by
  rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_vadd]; simp

lemma re_neg_one_vadd (w : ℍ) : ((-1:ℝ) +ᵥ w).re = w.re - 1 := by
  rw [re_vadd']; ring

lemma re_neg_two_vadd (w : ℍ) : ((-2:ℝ) +ᵥ w).re = w.re - 2 := by
  rw [re_vadd']; ring

lemma re_one_vadd (w : ℍ) : ((1:ℝ) +ᵥ w).re = w.re + 1 := by
  rw [re_vadd']; ring

lemma re_two_vadd (w : ℍ) : ((2:ℝ) +ᵥ w).re = w.re + 2 := by
  rw [re_vadd']; ring

/-! ## The wide sharp bound -/

theorem KfunClearSharpWide (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C A N : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 ≤ N ∧
      ∀ (w : ℍ) (t : ℝ) (ht : 0 < t), |w.re| ≤ 3/2 → 2 ≤ w.im → t ≤ 1 →
        jInvariantFun w ≠ jInvariantFun (imagAxis t ht) →
        ‖KfunClear ℓ d w (imagAxis t ht)‖
          ≤ C * (1 + ‖(w : ℂ)‖) ^ A * (1 + 1 / t) ^ N
              * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
              * Real.exp (-(2 * Real.pi * w.im)) := by
  obtain ⟨C0, A0, N0, hC0, hA0, hN0, hb0⟩ := KfunClearSharp ℓ d hd
  refine ⟨3 * 2 ^ A0 * C0, A0, N0, by positivity, hA0, hN0, ?_⟩
  intro w t ht hre him ht1 hne
  have hwnorm : (2:ℝ) ≤ ‖(w:ℂ)‖ := by
    have h1 : w.im ≤ ‖(w:ℂ)‖ := by
      have h := Complex.abs_im_le_norm (w:ℂ)
      rw [UpperHalfPlane.coe_im, abs_of_pos w.im_pos] at h; exact h
    linarith
  have hsharp : ∀ u : ℍ, |u.re| < 1 → 2 ≤ u.im → u.im = w.im →
      jInvariantFun u ≠ jInvariantFun (imagAxis t ht) →
      ‖KfunClear ℓ d u (imagAxis t ht)‖
        ≤ C0 * (1 + ‖(u:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
          * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im)) := by
    intro u hure huim hui hune
    have hF : Funnel u := ⟨DomainD_of_re_im u hure huim, huim⟩
    have h1 := hb0 u t ht hF ht1 hune
    rw [hui] at h1
    exact h1
  have hunif : ∀ u : ℍ, |u.re| < 1 → 2 ≤ u.im → u.im = w.im → ‖(u:ℂ)‖ ≤ ‖(w:ℂ)‖ + 2 →
      jInvariantFun u ≠ jInvariantFun (imagAxis t ht) →
      ‖KfunClear ℓ d u (imagAxis t ht)‖
        ≤ C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
          * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im)) := by
    intro u hure huim hui hnorm hune
    have h := hsharp u hure huim hui hune
    have h2 : (1 + ‖(u:ℂ)‖) ^ A0 ≤ 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 := by
      have h4 : 1 + ‖(u:ℂ)‖ ≤ 2 * (1 + ‖(w:ℂ)‖) := by linarith
      calc (1 + ‖(u:ℂ)‖) ^ A0 ≤ (2 * (1 + ‖(w:ℂ)‖)) ^ A0 :=
            Real.rpow_le_rpow (by positivity) h4 hA0
        _ = 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 := Real.mul_rpow (by norm_num) (by positivity)
    calc ‖KfunClear ℓ d u (imagAxis t ht)‖
        ≤ C0 * (1 + ‖(u:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
            * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
            * Real.exp (-(2 * Real.pi * w.im)) := h
      _ ≤ C0 * (2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0) * (1 + 1/t) ^ N0
            * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
            * Real.exp (-(2 * Real.pi * w.im)) := by gcongr
      _ = C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
            * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
            * Real.exp (-(2 * Real.pi * w.im)) := by ring
  have hthree : ‖KfunClear ℓ d w (imagAxis t ht)‖
      ≤ 3 * (C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
        * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
        * Real.exp (-(2 * Real.pi * w.im))) := by
    have htri : |w.re| < 1 ∨ |w.re| = 1 ∨ 1 < |w.re| := lt_trichotomy _ _
    rcases htri with hlt | heq | hgt
    · refine le_trans (hunif w hlt him rfl (by linarith) hne) ?_
      have hp : (0:ℝ) ≤ C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
          * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im)) := by positivity
      linarith
    · -- boundary `|Re| = 1`
      have hseq_abs : ∀ n : ℕ, |w.re * (1 - 1/((n:ℝ)+1))| < 1 := by
        intro n
        have h2 : |1 - 1/((n:ℝ)+1)| < 1 := by
          have h4 : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
          have h5 : 1/((n:ℝ)+1) ≤ 1 := by
            rw [div_le_one (by positivity : (0:ℝ) < (n:ℝ)+1)]
            have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
            linarith
          rw [abs_lt]; constructor <;> linarith
        rw [abs_mul, heq, one_mul]
        exact h2
      set s : ℕ → ℝ := fun n => w.re * (1 - 1/((n:ℝ)+1)) - w.re with hsdef
      set u : ℕ → ℍ := fun n => s n +ᵥ w with hudef
      have hu_re : ∀ n, (u n).re = w.re * (1 - 1/((n:ℝ)+1)) := by
        intro n; rw [hudef]; simp only [re_vadd']; ring
      have hu_im : ∀ n, (u n).im = w.im := by intro n; rw [hudef]; simp [im_vadd']
      have hu_norm : ∀ n, ‖((u n : ℍ) : ℂ)‖ ≤ ‖(w:ℂ)‖ + 2 := by
        intro n
        refine le_trans (norm_vadd_le' (s n) w) ?_
        have h1 : ‖(s n : ℝ)‖ ≤ 2 := by
          have h2 : s n = -(w.re * (1/((n:ℝ)+1))) := by rw [hsdef]; ring
          rw [Real.norm_eq_abs, h2, abs_neg, abs_mul, heq, one_mul,
            abs_of_pos (by positivity : (0:ℝ) < 1/((n:ℝ)+1))]
          rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+1)]
          push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
        linarith
      have hlim_s : Tendsto s atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h4 : s = fun n : ℕ => w.re * (-(1/((n:ℝ)+1))) := by
          funext n; rw [hsdef]; ring
        rw [h4]
        have := Filter.Tendsto.const_mul w.re h1.neg
        simpa using this
      have hseqC : Tendsto (fun n : ℕ => (((u n : ℍ) : ℂ))) atTop (𝓝 ((w:ℂ))) := by
        have h1 : Tendsto (fun n : ℕ => (s n : ℂ)) atTop (𝓝 0) :=
          (Complex.continuous_ofReal.tendsto 0).comp hlim_s
        have h2 := h1.add (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (w:ℂ)) atTop (𝓝 (w:ℂ)))
        have h3 : ((0:ℂ) + (w:ℂ)) = (w:ℂ) := by ring
        rw [h3] at h2
        simpa [hudef, UpperHalfPlane.coe_vadd] using h2
      have hseq : Tendsto u atTop (𝓝 w) := by
        refine (Topology.IsEmbedding.tendsto_nhds_iff (g := UpperHalfPlane.coe)
          (f := u) (l := Filter.atTop) (y := w) UpperHalfPlane.isEmbedding_coe).mpr ?_
        simpa [Function.comp_def] using hseqC
      have hev_ne : ∀ᶠ n in atTop, jInvariantFun (u n) ≠ jInvariantFun (imagAxis t ht) := by
        have hcl : IsClosed {v : ℍ | jInvariantFun v = jInvariantFun (imagAxis t ht)} :=
          isClosed_eq MiddleRange.continuous_jInvariantFun continuous_const
        have hmem : w ∈ {v : ℍ | jInvariantFun v = jInvariantFun (imagAxis t ht)}ᶜ := by
          simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using hne
        exact hseq.eventually (hcl.isOpen_compl.mem_nhds hmem)
      have hbdd : ∀ᶠ n in atTop, ‖KfunClear ℓ d (u n) (imagAxis t ht)‖
          ≤ C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
            * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
            * Real.exp (-(2 * Real.pi * w.im)) := by
        filter_upwards [hev_ne] with n hn
        refine hunif (u n) ?_ ?_ (hu_im n) (hu_norm n) hn
        · rw [hu_re]; exact hseq_abs n
        · rw [hu_im]; exact him
      have htend : Tendsto (fun n => ‖KfunClear ℓ d (u n) (imagAxis t ht)‖) atTop
          (𝓝 ‖KfunClear ℓ d w (imagAxis t ht)‖) := by
        have hc : Continuous fun v : ℍ => ‖KfunClear ℓ d v (imagAxis t ht)‖ :=
          ((KL.mdifferentiable_KfunClear_fst ℓ d hd (imagAxis t ht)).continuous).norm
        exact (hc.tendsto w).comp hseq
      refine le_trans (le_of_tendsto htend hbdd) ?_
      have hp : (0:ℝ) ≤ C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
          * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
          * Real.exp (-(2 * Real.pi * w.im)) := by positivity
      linarith
    · -- `|Re| > 1`
      by_cases hpos : 0 ≤ w.re
      · have hwr : 1 < w.re := by
          have := abs_of_nonneg hpos; rw [← this]; exact hgt
        have h1re : |((-1:ℝ) +ᵥ w).re| < 1 := by
          rw [re_neg_one_vadd, abs_lt]; constructor <;> linarith [le_abs_self (w.re), neg_abs_le (w.re), hre, hwr]
        have h2re : |((-2:ℝ) +ᵥ w).re| < 1 := by
          rw [re_neg_two_vadd, abs_lt]; constructor <;> linarith [le_abs_self (w.re), neg_abs_le (w.re), hre, hwr]
        have him1 : 2 ≤ ((-1:ℝ) +ᵥ w).im := by rw [im_vadd']; exact him
        have him2 : 2 ≤ ((-2:ℝ) +ᵥ w).im := by rw [im_vadd']; exact him
        have hn1 : ‖(((-1:ℝ) +ᵥ w : ℍ) : ℂ)‖ ≤ ‖(w:ℂ)‖ + 2 := by
          calc ‖(((-1:ℝ) +ᵥ w : ℍ) : ℂ)‖ ≤ ‖(-1:ℝ)‖ + ‖(w:ℂ)‖ := norm_vadd_le' _ _
            _ = 1 + ‖(w:ℂ)‖ := by simp
            _ ≤ ‖(w:ℂ)‖ + 2 := by linarith
        have hn2 : ‖(((-2:ℝ) +ᵥ w : ℍ) : ℂ)‖ ≤ ‖(w:ℂ)‖ + 2 := by
          calc ‖(((-2:ℝ) +ᵥ w : ℍ) : ℂ)‖ ≤ ‖(-2:ℝ)‖ + ‖(w:ℂ)‖ := norm_vadd_le' _ _
            _ = 2 + ‖(w:ℂ)‖ := by simp
            _ ≤ ‖(w:ℂ)‖ + 2 := by linarith
        have hne1 : jInvariantFun ((-1:ℝ) +ᵥ w) ≠ jInvariantFun (imagAxis t ht) := by
          rw [jInvariantFun_vadd_neg_one]; exact hne
        have hne2 : jInvariantFun ((-2:ℝ) +ᵥ w) ≠ jInvariantFun (imagAxis t ht) := by
          rw [jInvariantFun_vadd_neg_two]; exact hne
        have hT2 := congr_fun (KfunClear_T2 ℓ d hd (imagAxis t ht)) ((-2:ℝ) +ᵥ w)
        simp only [T2op, Pi.zero_apply] at hT2
        rw [two_vadd_neg_two, one_vadd_neg_two] at hT2
        have hFw : KfunClear ℓ d w (imagAxis t ht)
            = 2 * KfunClear ℓ d ((-1:ℝ) +ᵥ w) (imagAxis t ht)
              - KfunClear ℓ d ((-2:ℝ) +ᵥ w) (imagAxis t ht) := by
          have hkey : KfunClear ℓ d w (imagAxis t ht)
              - (2 * KfunClear ℓ d ((-1:ℝ) +ᵥ w) (imagAxis t ht)
                - KfunClear ℓ d ((-2:ℝ) +ᵥ w) (imagAxis t ht)) = 0 := by
            rw [show KfunClear ℓ d w (imagAxis t ht)
                - (2 * KfunClear ℓ d ((-1:ℝ) +ᵥ w) (imagAxis t ht)
                  - KfunClear ℓ d ((-2:ℝ) +ᵥ w) (imagAxis t ht))
                = KfunClear ℓ d w (imagAxis t ht)
                  - 2 * KfunClear ℓ d ((-1:ℝ) +ᵥ w) (imagAxis t ht)
                  + KfunClear ℓ d ((-2:ℝ) +ᵥ w) (imagAxis t ht) by ring]
            exact hT2
          exact sub_eq_zero.mp hkey
        have hb1 := hunif ((-1:ℝ) +ᵥ w) h1re him1 (by rw [im_vadd']) hn1 hne1
        have hb2 := hunif ((-2:ℝ) +ᵥ w) h2re him2 (by rw [im_vadd']) hn2 hne2
        have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
        rw [hFw]
        calc ‖2 * KfunClear ℓ d ((-1:ℝ) +ᵥ w) (imagAxis t ht)
              - KfunClear ℓ d ((-2:ℝ) +ᵥ w) (imagAxis t ht)‖
            ≤ ‖2 * KfunClear ℓ d ((-1:ℝ) +ᵥ w) (imagAxis t ht)‖
              + ‖KfunClear ℓ d ((-2:ℝ) +ᵥ w) (imagAxis t ht)‖ := norm_sub_le _ _
          _ = 2 * ‖KfunClear ℓ d ((-1:ℝ) +ᵥ w) (imagAxis t ht)‖
              + ‖KfunClear ℓ d ((-2:ℝ) +ᵥ w) (imagAxis t ht)‖ := by rw [norm_mul, h2]
          _ ≤ 2 * (C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
                * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
                * Real.exp (-(2 * Real.pi * w.im)))
              + (C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
                * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
                * Real.exp (-(2 * Real.pi * w.im))) :=
              add_le_add (mul_le_mul_of_nonneg_left hb1 (by norm_num)) hb2
          _ = 3 * (C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
                * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
                * Real.exp (-(2 * Real.pi * w.im))) := by ring
      · have hneg : w.re < 0 := lt_of_not_ge hpos
        have hwr : w.re < -1 := by
          have h := hgt; rw [abs_of_neg hneg] at h; linarith
        have hre1 : -(3/2) ≤ w.re := le_trans (neg_le_neg hre) (neg_abs_le _)
        have h1re : |((1:ℝ) +ᵥ w).re| < 1 := by
          rw [re_one_vadd, abs_lt]; constructor <;> linarith
        have h2re : |((2:ℝ) +ᵥ w).re| < 1 := by
          rw [re_two_vadd, abs_lt]; constructor <;> linarith
        have him1 : 2 ≤ ((1:ℝ) +ᵥ w).im := by rw [im_vadd']; exact him
        have him2 : 2 ≤ ((2:ℝ) +ᵥ w).im := by rw [im_vadd']; exact him
        have hn1 : ‖(((1:ℝ) +ᵥ w : ℍ) : ℂ)‖ ≤ ‖(w:ℂ)‖ + 2 := by
          calc ‖(((1:ℝ) +ᵥ w : ℍ) : ℂ)‖ ≤ ‖(1:ℝ)‖ + ‖(w:ℂ)‖ := norm_vadd_le' _ _
            _ = 1 + ‖(w:ℂ)‖ := by simp
            _ ≤ ‖(w:ℂ)‖ + 2 := by linarith
        have hn2 : ‖(((2:ℝ) +ᵥ w : ℍ) : ℂ)‖ ≤ ‖(w:ℂ)‖ + 2 := by
          calc ‖(((2:ℝ) +ᵥ w : ℍ) : ℂ)‖ ≤ ‖(2:ℝ)‖ + ‖(w:ℂ)‖ := norm_vadd_le' _ _
            _ = 2 + ‖(w:ℂ)‖ := by simp
            _ ≤ ‖(w:ℂ)‖ + 2 := by linarith
        have hne1 : jInvariantFun ((1:ℝ) +ᵥ w) ≠ jInvariantFun (imagAxis t ht) := by
          rw [KernelFacts.jInvariantFun_vadd_one]; exact hne
        have hne2 : jInvariantFun ((2:ℝ) +ᵥ w) ≠ jInvariantFun (imagAxis t ht) := by
          rw [Work.Kernels.vadd_one_add_one, KernelFacts.jInvariantFun_vadd_one ((1:ℝ) +ᵥ w),
            KernelFacts.jInvariantFun_vadd_one w]
          exact hne
        have hT2 := congr_fun (KfunClear_T2 ℓ d hd (imagAxis t ht)) w
        simp only [T2op, Pi.zero_apply] at hT2
        have hFw : KfunClear ℓ d w (imagAxis t ht)
            = 2 * KfunClear ℓ d ((1:ℝ) +ᵥ w) (imagAxis t ht)
              - KfunClear ℓ d ((2:ℝ) +ᵥ w) (imagAxis t ht) := by
          have hkey : KfunClear ℓ d w (imagAxis t ht)
              - (2 * KfunClear ℓ d ((1:ℝ) +ᵥ w) (imagAxis t ht)
                - KfunClear ℓ d ((2:ℝ) +ᵥ w) (imagAxis t ht)) = 0 := by
            rw [show KfunClear ℓ d w (imagAxis t ht)
                - (2 * KfunClear ℓ d ((1:ℝ) +ᵥ w) (imagAxis t ht)
                  - KfunClear ℓ d ((2:ℝ) +ᵥ w) (imagAxis t ht))
                = KfunClear ℓ d w (imagAxis t ht)
                  - 2 * KfunClear ℓ d ((1:ℝ) +ᵥ w) (imagAxis t ht)
                  + KfunClear ℓ d ((2:ℝ) +ᵥ w) (imagAxis t ht) by ring]
            rw [show KfunClear ℓ d w (imagAxis t ht)
                  - 2 * KfunClear ℓ d ((1:ℝ) +ᵥ w) (imagAxis t ht)
                  + KfunClear ℓ d ((2:ℝ) +ᵥ w) (imagAxis t ht)
                = KfunClear ℓ d ((2:ℝ) +ᵥ w) (imagAxis t ht)
                  - 2 * KfunClear ℓ d ((1:ℝ) +ᵥ w) (imagAxis t ht)
                  + KfunClear ℓ d w (imagAxis t ht) by ring]
            exact hT2
          exact sub_eq_zero.mp hkey
        have hb1 := hunif ((1:ℝ) +ᵥ w) h1re him1 (by rw [im_vadd']) hn1 hne1
        have hb2 := hunif ((2:ℝ) +ᵥ w) h2re him2 (by rw [im_vadd']) hn2 hne2
        have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
        rw [hFw]
        calc ‖2 * KfunClear ℓ d ((1:ℝ) +ᵥ w) (imagAxis t ht)
              - KfunClear ℓ d ((2:ℝ) +ᵥ w) (imagAxis t ht)‖
            ≤ ‖2 * KfunClear ℓ d ((1:ℝ) +ᵥ w) (imagAxis t ht)‖
              + ‖KfunClear ℓ d ((2:ℝ) +ᵥ w) (imagAxis t ht)‖ := norm_sub_le _ _
          _ = 2 * ‖KfunClear ℓ d ((1:ℝ) +ᵥ w) (imagAxis t ht)‖
              + ‖KfunClear ℓ d ((2:ℝ) +ᵥ w) (imagAxis t ht)‖ := by rw [norm_mul, h2]
          _ ≤ 2 * (C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
                * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
                * Real.exp (-(2 * Real.pi * w.im)))
              + (C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
                * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
                * Real.exp (-(2 * Real.pi * w.im))) :=
              add_le_add (mul_le_mul_of_nonneg_left hb1 (by norm_num)) hb2
          _ = 3 * (C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
                * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
                * Real.exp (-(2 * Real.pi * w.im))) := by ring

  calc ‖KfunClear ℓ d w (imagAxis t ht)‖
      ≤ 3 * (C0 * 2 ^ A0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
        * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
        * Real.exp (-(2 * Real.pi * w.im))) := hthree
    _ = 3 * 2 ^ A0 * C0 * (1 + ‖(w:ℂ)‖) ^ A0 * (1 + 1/t) ^ N0
        * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * t⁻¹))
        * Real.exp (-(2 * Real.pi * w.im)) := by ring


lemma imagAxis_im (t : ℝ) (ht : 0 < t) : (Work.Kernels.imagAxis t ht).im = t := by
  simp [Work.Kernels.imagAxis]

lemma imagAxis_coe (t : ℝ) (ht : 0 < t) :
    ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl

/-! ## A lower bound for `‖Δ(i t)‖` -/

theorem deltaLowerImagAxis (cΔ : ℝ) (hcΔ : 0 < cΔ)
    (hΔ : ∀ z : ℍ, 1 / 3 ≤ z.im → cΔ * ‖qParamFun z‖ ≤ ‖DeltaFun z‖)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    cΔ * ((t : ℝ) ^ 12)⁻¹ * Real.exp (-(2 * Real.pi * t⁻¹))
      ≤ ‖DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  have him : (1 : ℝ) / 3 ≤ (Work.Kernels.imagAxis t⁻¹ hs).im := by
    rw [imagAxis_im]
    have : (1:ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
    linarith
  have h1 : cΔ * ‖qParamFun (Work.Kernels.imagAxis t⁻¹ hs)‖
      ≤ ‖DeltaFun (Work.Kernels.imagAxis t⁻¹ hs)‖ := hΔ _ him
  have hqnorm : ‖qParamFun (Work.Kernels.imagAxis t⁻¹ hs)‖
      = Real.exp (-(2 * Real.pi * t⁻¹)) := by
    rw [norm_qParamFun, imagAxis_im]
  have hS := KernelFacts.kpc_smul_S_of_slash (F := DeltaFun)
    KernelFacts.kpc_Delta_slash_S (Work.Kernels.imagAxis t ht)
  rw [Work.Asymptotics.imagAxis_smul_S t ht] at hS
  have hnormτ12 : ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ) ^ (12 : ℤ)‖ = t ^ 12 := by
    rw [norm_zpow, zpow_ofNat]
    have h : ‖(((Work.Kernels.imagAxis t ht : ℍ)) : ℂ)‖ = t := by
      rw [imagAxis_coe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht]
    rw [h]
  have hnorm : ‖DeltaFun (Work.Kernels.imagAxis t⁻¹ hs)‖
      = t ^ 12 * ‖DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
    rw [hS, norm_mul, hnormτ12]
  have ht12pos : (0 : ℝ) < t ^ 12 := pow_pos ht 12
  have h2 : cΔ * Real.exp (-(2 * Real.pi * t⁻¹)) ≤ t ^ 12 * ‖DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
    rw [← hqnorm, ← hnorm]
    exact h1
  have hx : (0:ℝ) ≤ ((t:ℝ)^12)⁻¹ := by positivity
  have h4 : cΔ * ((t:ℝ)^12)⁻¹ * Real.exp (-(2 * Real.pi * t⁻¹))
      = ((t:ℝ)^12)⁻¹ * (cΔ * Real.exp (-(2 * Real.pi * t⁻¹))) := by ring
  rw [h4]
  calc ((t:ℝ)^12)⁻¹ * (cΔ * Real.exp (-(2 * Real.pi * t⁻¹)))
      ≤ ((t:ℝ)^12)⁻¹ * (t^12 * ‖DeltaFun (Work.Kernels.imagAxis t ht)‖) :=
        mul_le_mul_of_nonneg_left h2 hx
    _ = ‖DeltaFun (Work.Kernels.imagAxis t ht)‖ := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht12pos), one_mul]

/-! ## The `Kaxis` evaluation -/

lemma Kaxis_eq (ℓ : LogLambdaData) (d : ℕ) (τ : ℍ) {t : ℝ} (ht : 0 < t) :
    Kaxis (Kfun ℓ d) τ t = Kfun ℓ d τ (Work.Kernels.imagAxis t ht) := by
  rw [Kaxis, dif_pos ht]

/-! ## The cleared kernel as `growthPrefactor · Kfun` -/

lemma KfunClear_eq_growthPrefactor (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) (h : jInvariantFun τ ≠ jInvariantFun z) :
    KfunClear ℓ d τ z = growthPrefactor d τ z * Kfun ℓ d τ z := by
  rw [KfunClear, Kfun, Work.Kernels.ClearLink.KPlusClear_eq_smul d hd τ z h,
    Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ d hd τ z h]
  ring

/-! ## Vanishing of the cleared kernel at the coincidence points -/

lemma KfunClear_TS_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    KfunClear ℓ d ((1:ℝ) +ᵥ (ModularGroup.S • z)) z = 0 := by
  rw [KfunClear, Work.Residues.KPlusClear_TS d hd z, Work.Residues.KMinusClear_TS ℓ d hd z]
  ring

lemma KfunClear_TinvS_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    KfunClear ℓ d ((-1:ℝ) +ᵥ (ModularGroup.S • z)) z = 0 := by
  have hT2 := congr_fun (KfunClear_T2 ℓ d hd z) ((-1:ℝ) +ᵥ (ModularGroup.S • z))
  simp only [T2op, Pi.zero_apply] at hT2
  rw [show (2:ℝ) +ᵥ ((-1:ℝ) +ᵥ (ModularGroup.S • z)) = (1:ℝ) +ᵥ (ModularGroup.S • z)
        by rw [← add_vadd]; norm_num,
      show (1:ℝ) +ᵥ ((-1:ℝ) +ᵥ (ModularGroup.S • z)) = ModularGroup.S • z
        by rw [← add_vadd]; norm_num] at hT2
  rw [KfunClear_TS_zero ℓ d hd z, KL.KfunClear_S_self ℓ d hd z] at hT2
  simpa using hT2

/-! ## The generic one-zero step -/

lemma final_arith (M r cj δz V E1 E2 : ℝ) (e : ℕ) (hE1 : E1 ≠ 0) (hE2 : E2 ≠ 0)
    (hr : 0 < r) (hcj : 0 < cj) (hδz : 0 < δz) (hV : 0 < V) :
    (2*M/r) * V / ((1/2) * E1⁻¹ * δz ^ e * cj * E2 * V)
      = 4 * M / (r * cj * δz ^ e) * E1 * E2⁻¹ := by
  field_simp
  ring

lemma mul_le_mul_4 {a b c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ c) (h4 : 0 ≤ b) :
    a * c ≤ b * d := by
  have h5 : a * c ≤ b * c := mul_le_mul_of_nonneg_right h1 h3
  have h6 : b * c ≤ b * d := mul_le_mul_of_nonneg_left h2 h4
  linarith

lemma growthPrefactor_lower (τ z : ℍ) (t δz cj V : ℝ) (e : ℕ)
    (hδz : 0 < δz) (hcj : 0 < cj) (hV : 0 ≤ V)
    (hΔτ : (1/2 : ℝ) * Real.exp (-(2*Real.pi*τ.im)) ≤ ‖DeltaFun τ‖)
    (hΔz : δz ≤ ‖DeltaFun z‖)
    (hjlow : cj * Real.exp (2*Real.pi/t) * V ≤ ‖jInvariantFun τ - jInvariantFun z‖) :
    (1/2) * Real.exp (-(2*Real.pi*τ.im)) * δz ^ e * cj * Real.exp (2*Real.pi/t) * V
      ≤ ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e * ‖jInvariantFun τ - jInvariantFun z‖ := by
  have h1 : (1/2) * Real.exp (-(2*Real.pi*τ.im)) * δz ^ e
      ≤ ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e :=
    mul_le_mul_4 hΔτ (pow_le_pow_left₀ hδz.le hΔz e) (pow_nonneg hδz.le e) (norm_nonneg _)
  have h2 : ((1/2) * Real.exp (-(2*Real.pi*τ.im)) * δz ^ e) * (cj * Real.exp (2*Real.pi/t) * V)
      ≤ (‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e) * ‖jInvariantFun τ - jInvariantFun z‖ :=
    mul_le_mul_4 h1 hjlow
      (mul_nonneg (mul_nonneg hcj.le (Real.exp_pos _).le) hV)
      (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) e))
  calc (1/2) * Real.exp (-(2*Real.pi*τ.im)) * δz ^ e * cj * Real.exp (2*Real.pi/t) * V
      = ((1/2) * Real.exp (-(2*Real.pi*τ.im)) * δz ^ e) * (cj * Real.exp (2*Real.pi/t) * V) := by ring
    _ ≤ (‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e) * ‖jInvariantFun τ - jInvariantFun z‖ := h2
    _ = ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e * ‖jInvariantFun τ - jInvariantFun z‖ := by ring

lemma Kfun_le_one_zero (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (e : ℕ) (he : e = (if d = 8 then 1 else 2))
    {z c τ : ℍ} {t r M cj δz : ℝ} (ht : 0 < t)
    (hr : 0 < r) (hrc : r < c.im) (hcj : 0 < cj) (hδz : 0 < δz) (hMpos : 0 < M)
    (hjcz : jInvariantFun c = jInvariantFun z)
    (hM : ∀ w : ℍ, ‖(w:ℂ) - (c:ℂ)‖ ≤ r → ‖KfunClear ℓ d w z‖ ≤ M)
    (hzero : KfunClear ℓ d c z = 0)
    (hτc : ‖(τ:ℂ) - (c:ℂ)‖ < r / 2)
    (hne : jInvariantFun τ ≠ jInvariantFun z)
    (hjlow : cj * Real.exp (2 * Real.pi / t) * ‖(τ:ℂ) - (c:ℂ)‖
      ≤ ‖jInvariantFun τ - jInvariantFun z‖)
    (hΔτ : (1/2 : ℝ) * Real.exp (-(2*Real.pi*τ.im)) ≤ ‖DeltaFun τ‖)
    (hΔz : δz ≤ ‖DeltaFun z‖) :
    ‖Kfun ℓ d τ z‖
      ≤ 4 * M / (r * cj * δz ^ e) * Real.exp (2*Real.pi*τ.im) * Real.exp (-(2*Real.pi/t)) := by
  set V : ℝ := ‖(τ:ℂ) - (c:ℂ)‖ with hVdef
  have hVpos : 0 < V := by
    rw [hVdef]
    refine norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hne ?_))
    rw [UpperHalfPlane.ext h, hjcz]
  have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w : ℍ => KfunClear ℓ d w z) :=
    KL.mdifferentiable_KfunClear_fst ℓ d hd z
  have hone := KL.one_zero_apply (f := fun w : ℍ => KfunClear ℓ d w z) hf hr hrc hM
    (w₀ := c) (by rw [sub_self, norm_zero]; linarith) hzero τ hτc
  have hKC : ‖KfunClear ℓ d τ z‖ ≤ (2*M/r) * V := by
    have := hone
    rw [hVdef]; exact this
  have hGPne : growthPrefactor d τ z ≠ 0 := by
    rw [growthPrefactor]
    exact mul_ne_zero
      (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ)
        (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero z)))
      (sub_ne_zero.mpr hne)
  have hGPpos : 0 < ‖growthPrefactor d τ z‖ := norm_pos_iff.mpr hGPne
  have hKfun : ‖Kfun ℓ d τ z‖ = ‖KfunClear ℓ d τ z‖ / ‖growthPrefactor d τ z‖ := by
    have h := KfunClear_eq_growthPrefactor ℓ d hd τ z hne
    rw [h, norm_mul]
    field_simp
  have hnorm : ‖growthPrefactor d τ z‖
      = ‖DeltaFun τ‖ * ‖DeltaFun z‖ ^ e * ‖jInvariantFun τ - jInvariantFun z‖ := by
    rw [KL.norm_growthPrefactor, he]
  have hDlow : (1/2) * Real.exp (-(2*Real.pi*τ.im)) * δz ^ e * cj * Real.exp (2*Real.pi/t) * V
      ≤ ‖growthPrefactor d τ z‖ := by
    rw [hnorm]
    exact growthPrefactor_lower τ z t δz cj V e hδz hcj hVpos.le hΔτ hΔz (by rw [hVdef]; exact hjlow)
  have hDpos : 0 < (1/2) * Real.exp (-(2*Real.pi*τ.im)) * δz ^ e * cj
      * Real.exp (2*Real.pi/t) * V := by
    have ha : (0:ℝ) < (1/2) * Real.exp (-(2*Real.pi*τ.im)) :=
      mul_pos (by norm_num) (Real.exp_pos _)
    exact mul_pos (mul_pos (mul_pos (mul_pos ha (pow_pos hδz e)) hcj) (Real.exp_pos _)) hVpos
  have hnum : 0 < (2*M/r) * V := mul_pos (div_pos (mul_pos (by norm_num) hMpos) hr) hVpos
  rw [hKfun]
  have hkey : ‖KfunClear ℓ d τ z‖
      * ((1/2) * Real.exp (-(2*Real.pi*τ.im)) * δz ^ e * cj * Real.exp (2*Real.pi/t) * V)
      ≤ ((2*M/r) * V) * ‖growthPrefactor d τ z‖ :=
    mul_le_mul_4 hKC hDlow (le_of_lt hDpos) (le_of_lt hnum)
  have hstep : ‖KfunClear ℓ d τ z‖ / ‖growthPrefactor d τ z‖
      ≤ ((2*M/r) * V) / ((1/2) * Real.exp (-(2*Real.pi*τ.im)) * δz ^ e * cj
          * Real.exp (2*Real.pi/t) * V) :=
    (div_le_div_iff₀ hGPpos hDpos).mpr hkey
  refine le_trans hstep (le_of_eq ?_)
  rw [Real.exp_neg, Real.exp_neg]
  exact final_arith M r cj δz V (Real.exp (2*Real.pi*τ.im)) (Real.exp (2*Real.pi/t)) e
    (Real.exp_ne_zero _) (Real.exp_ne_zero _) hr hcj hδz hVpos

/-! ## The `j`-lower bound at the three coincidence points -/

theorem jLowerBranches :
    ∃ c : ℝ, 0 < c ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
      ∀ τ : ℍ, τ ∈ DomainD → 2 ≤ τ.im →
      (‖(τ : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ < 1 / 4 →
        c * Real.exp (2 * Real.pi / t) * ‖(τ : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ ≤
          ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖) ∧
      (‖(τ : ℂ) - ((1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ < 1 / 4 →
        c * Real.exp (2 * Real.pi / t) * ‖(τ : ℂ) - ((1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ ≤
          ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖) ∧
      (‖(τ : ℂ) - ((-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ < 1 / 4 →
        c * Real.exp (2 * Real.pi / t) * ‖(τ : ℂ) - ((-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ ≤
          ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖) := by
  obtain ⟨cJ, hcJ, hJ⟩ := Work.Asymptotics.CuspDecay.KMinusMiddle.JLowerGeSevenFourths
  refine ⟨cJ, hcJ, ?_⟩
  intro t ht ht1 τ hD h2
  have key : ∀ (u : ℍ), u ∈ DomainD → 2 ≤ u.im →
      ‖(u : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ < 1 / 4 →
      cJ * Real.exp (2 * Real.pi / t) * ‖(u : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ ≤
        ‖jInvariantFun u - jInvariantFun (imagAxis t ht)‖ := by
    intro u hD' h2' hdist
    set s : ℝ := 1 / t with hsdef
    have hspos : 0 < s := by rw [hsdef]; positivity
    have hscoe : (s : ℂ) = (t : ℂ)⁻¹ := by rw [hsdef, one_div, Complex.ofReal_inv]
    have hst : 1 / s = t := by rw [hsdef, one_div_one_div]
    set v : ℂ := (u : ℂ) - (s : ℂ) * Complex.I with hvdef
    have hv_re : v.re = u.re := by
      rw [hvdef]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, UpperHalfPlane.coe_re]
    have hv_im : v.im = u.im - s := by
      rw [hvdef]
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, UpperHalfPlane.coe_im]
    have hA : ‖(u : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ = ‖v‖ := by rw [hvdef, ← hscoe]
    have hdist_v : ‖v‖ < 1 / 4 := by rw [← hA]; exact hdist
    have hre_v : |u.re| ≤ ‖v‖ := by
      have h := Complex.abs_re_le_norm v; rwa [hv_re] at h
    have him_v : |u.im - s| ≤ ‖v‖ := by
      have h := Complex.abs_im_le_norm v; rwa [hv_im] at h
    have hre_lt : |u.re| < 1 / 4 := lt_of_le_of_lt hre_v hdist_v
    have hs74 : 7 / 4 ≤ s := by
      have h1 : u.im - s ≤ ‖v‖ := (abs_le.mp him_v).2
      linarith
    have him : |u.im - s| ≤ 1 / 4 := le_of_lt (lt_of_le_of_lt him_v hdist_v)
    have hsq : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      intro w; rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hu_le_1 : ‖v‖ ≤ ‖v - 1‖ := by
      have h1 : ‖v - 1‖ ^ 2 = (v.re - 1) ^ 2 + v.im ^ 2 := by
        rw [hsq, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]; ring
      have h3 : ‖v‖ ^ 2 ≤ ‖v - 1‖ ^ 2 := by
        rw [hsq v, h1, hv_re]
        have hle : u.re ≤ 1 / 2 := by linarith [(abs_lt.mp hre_lt).2]
        nlinarith [hle]
      nlinarith [h3, norm_nonneg v, norm_nonneg (v - 1)]
    have hu_le_m1 : ‖v‖ ≤ ‖v + 1‖ := by
      have h1 : ‖v + 1‖ ^ 2 = (v.re + 1) ^ 2 + v.im ^ 2 := by
        rw [hsq, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]; ring
      have h3 : ‖v‖ ^ 2 ≤ ‖v + 1‖ ^ 2 := by
        rw [hsq v, h1, hv_re]
        have hle : -(1 / 2 : ℝ) ≤ u.re := by linarith [(abs_lt.mp hre_lt).1]
        nlinarith [hle]
      nlinarith [h3, norm_nonneg v, norm_nonneg (v + 1)]
    have hmin : min (min ‖v‖ ‖v - 1‖) ‖v + 1‖ = ‖v‖ := by
      rw [min_eq_left (le_trans (min_le_left _ _) hu_le_m1), min_eq_left hu_le_1]
    have hres := hJ s hs74 u hD' him
    have h1eq : ‖(u : ℂ) - (((imagAxis s hspos : ℍ)) : ℂ)‖ = ‖v‖ := by
      have hveq : (u : ℂ) - (((imagAxis s hspos : ℍ)) : ℂ) = v := by
        rw [hvdef]
        rfl
      rw [hveq]
    have h2eq : ‖(u : ℂ) - ((((1 : ℝ) +ᵥ (imagAxis s hspos) : ℍ)) : ℂ)‖ = ‖v - 1‖ := by
      have hveq : (u : ℂ) - ((((1 : ℝ) +ᵥ (imagAxis s hspos) : ℍ)) : ℂ) = v - 1 := by
        rw [hvdef, UpperHalfPlane.coe_vadd]
        simp only [Work.Kernels.imagAxis, Complex.ofReal_one]
        ring
      rw [hveq]
    have h3eq : ‖(u : ℂ) - ((((-1 : ℝ) +ᵥ (imagAxis s hspos) : ℍ)) : ℂ)‖ = ‖v + 1‖ := by
      have hveq : (u : ℂ) - ((((-1 : ℝ) +ᵥ (imagAxis s hspos) : ℍ)) : ℂ) = v + 1 := by
        have h1 : ((((-1 : ℝ) +ᵥ (imagAxis s hspos) : ℍ)) : ℂ)
            = (-1 : ℂ) + ((s : ℂ) * Complex.I) := by
          rw [UpperHalfPlane.coe_vadd]
          simp [Work.Kernels.imagAxis]
        rw [h1, hvdef]
        ring
      rw [hveq]
    rw [h1eq, h2eq, h3eq, hmin] at hres
    have hpt : ∀ hh : 0 < 1 / s, imagAxis (1 / s) hh = imagAxis t ht := by
      intro hh
      apply UpperHalfPlane.ext
      have h1 : ((imagAxis (1 / s) hh : ℍ) : ℂ) = ((1 / s : ℝ) : ℂ) * Complex.I := rfl
      have h2 : ((imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
      rw [h1, h2, hst]
    rw [hpt] at hres
    have hexp : Real.exp (2 * Real.pi * s) = Real.exp (2 * Real.pi / t) := by
      rw [hsdef]; congr 1; rw [one_div, div_eq_mul_inv]
    rw [hexp] at hres
    rw [← hA] at hres
    exact hres
  refine ⟨?_, ?_, ?_⟩
  · intro hdist; exact key τ hD h2 hdist
  · intro hdist
    have hD1 : ((-1 : ℝ) +ᵥ τ) ∈ DomainD := by
      refine DomainD_of_re_im _ ?_ ?_
      · rw [re_neg_one_vadd, abs_lt]
        have h1 := Complex.abs_re_le_norm ((τ : ℂ) - ((1 : ℂ) + (t : ℂ)⁻¹ * Complex.I))
        have h2 : ((τ : ℂ) - ((1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)).re = τ.re - 1 := by
          simp [Complex.sub_re, Complex.add_re]
        rw [h2] at h1
        constructor <;> linarith [(abs_lt.mp (lt_of_le_of_lt h1 hdist)).1,
          (abs_lt.mp (lt_of_le_of_lt h1 hdist)).2]
      · rw [im_vadd']; exact h2
    have h21 : 2 ≤ ((-1 : ℝ) +ᵥ τ).im := by rw [im_vadd']; exact h2
    have hdist1 : ‖(((-1 : ℝ) +ᵥ τ : ℍ) : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ < 1 / 4 := by
      have hv : ((((-1 : ℝ) +ᵥ τ : ℍ)) : ℂ) = (-1 : ℂ) + (τ : ℂ) := by
        rw [UpperHalfPlane.coe_vadd]; norm_num
      rw [hv]
      have h2' : (-1 : ℂ) + (τ : ℂ) - (t : ℂ)⁻¹ * Complex.I
          = (τ : ℂ) - ((1 : ℂ) + (t : ℂ)⁻¹ * Complex.I) := by ring
      rw [h2']; exact hdist
    have hkey := key ((-1 : ℝ) +ᵥ τ) hD1 h21 hdist1
    rw [jInvariantFun_vadd_neg_one] at hkey
    rw [show ((((-1 : ℝ) +ᵥ τ : ℍ)) : ℂ) = (-1 : ℂ) + (τ : ℂ) by
      rw [UpperHalfPlane.coe_vadd]; norm_num] at hkey
    rw [show (-1 : ℂ) + (τ : ℂ) - (t : ℂ)⁻¹ * Complex.I
        = (τ : ℂ) - ((1 : ℂ) + (t : ℂ)⁻¹ * Complex.I) by ring] at hkey
    exact hkey
  · intro hdist
    have hD1 : ((1 : ℝ) +ᵥ τ) ∈ DomainD := by
      refine DomainD_of_re_im _ ?_ ?_
      · rw [re_one_vadd, abs_lt]
        have h1 := Complex.abs_re_le_norm ((τ : ℂ) - ((-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I))
        have h2 : ((τ : ℂ) - ((-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)).re = τ.re + 1 := by
          simp [Complex.sub_re, Complex.add_re]
        rw [h2] at h1
        constructor <;> linarith [(abs_lt.mp (lt_of_le_of_lt h1 hdist)).1,
          (abs_lt.mp (lt_of_le_of_lt h1 hdist)).2]
      · rw [im_vadd']; exact h2
    have h21 : 2 ≤ ((1 : ℝ) +ᵥ τ).im := by rw [im_vadd']; exact h2
    have hdist1 : ‖(((1 : ℝ) +ᵥ τ : ℍ) : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ < 1 / 4 := by
      have hv : ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) = (1 : ℂ) + (τ : ℂ) := by
        rw [UpperHalfPlane.coe_vadd]; norm_num
      rw [hv]
      have h2' : (1 : ℂ) + (τ : ℂ) - (t : ℂ)⁻¹ * Complex.I
          = (τ : ℂ) - ((-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I) := by ring
      rw [h2']; exact hdist
    have hkey := key ((1 : ℝ) +ᵥ τ) hD1 h21 hdist1
    rw [KernelFacts.jInvariantFun_vadd_one] at hkey
    rw [show ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) = (1 : ℂ) + (τ : ℂ) by
      rw [UpperHalfPlane.coe_vadd]; norm_num] at hkey
    rw [show (1 : ℂ) + (τ : ℂ) - (t : ℂ)⁻¹ * Complex.I
        = (τ : ℂ) - ((-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I) by ring] at hkey
    exact hkey

/-! ## Coincidence points in the small ball around the funnel points -/

lemma imagAxis_re (t : ℝ) (ht : 0 < t) : ((imagAxis t ht : ℍ) : ℂ).re = 0 := by
  rw [imagAxis_coe]; simp

lemma S_imagAxis (t : ℝ) (ht : 0 < t) :
    ModularGroup.S • (imagAxis t ht) = imagAxis t⁻¹ (inv_pos.mpr ht) :=
  Work.Asymptotics.imagAxis_smul_S t ht

lemma coe_imagAxis_inv (t : ℝ) (ht : 0 < t) :
    ((imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ) : ℂ) = (t : ℂ)⁻¹ * Complex.I := by
  show ((t⁻¹ : ℝ) : ℂ) * Complex.I = (t : ℂ)⁻¹ * Complex.I
  rw [Complex.ofReal_inv]

lemma DomainD_of_re_im' (w : ℍ) (hre : |w.re| < 1) (him : 1 ≤ w.im) : w ∈ DomainD := by
  rw [DomainD]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (abs_lt.mp hre).1; linarith
  · exact (abs_lt.mp hre).2
  · have h := Complex.abs_im_le_norm ((w:ℂ) - (1/2:ℂ))
    have h2 : ((w:ℂ) - (1/2:ℂ)).im = w.im := by simp [Complex.sub_im, UpperHalfPlane.coe_im]
    rw [h2, abs_of_pos w.im_pos] at h; linarith
  · have h := Complex.abs_im_le_norm ((w:ℂ) + (1/2:ℂ))
    have h2 : ((w:ℂ) + (1/2:ℂ)).im = w.im := by simp [Complex.add_im, UpperHalfPlane.coe_im]
    rw [h2, abs_of_pos w.im_pos] at h; linarith

lemma coincidence_axis {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (ht2 : t ≤ 2/3)
    {w : ℍ} (hw : ‖(w : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ ≤ 1 / 2)
    (hj : jInvariantFun w = jInvariantFun (imagAxis t ht)) :
    (w : ℂ) = (t : ℂ)⁻¹ * Complex.I := by
  have hinv_le : (3:ℝ)/2 ≤ t⁻¹ := by
    have h := one_div_le_one_div_of_le ht ht2
    simp only [one_div] at h
    norm_num at h
    exact h
  have him : 1 ≤ w.im := by
    have h := Complex.abs_im_le_norm ((w : ℂ) - ((t : ℂ)⁻¹ * Complex.I))
    have h2 : ((w : ℂ) - ((t : ℂ)⁻¹ * Complex.I)).im = w.im - t⁻¹ := by
      simp [Complex.sub_im, Complex.mul_im, Complex.ofReal_inv, UpperHalfPlane.coe_im]
    rw [h2] at h
    have hle : |w.im - t⁻¹| ≤ 1 / 2 := le_trans h hw
    linarith only [(abs_le.mp hle).1, hinv_le]
  have hD : w ∈ DomainD := by
    refine DomainD_of_re_im' w ?_ him
    have h := Complex.abs_re_le_norm ((w : ℂ) - ((t : ℂ)⁻¹ * Complex.I))
    have h2 : ((w : ℂ) - ((t : ℂ)⁻¹ * Complex.I)).re = w.re := by
      simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_inv, UpperHalfPlane.coe_re]
    rw [h2] at h
    exact lt_of_le_of_lt (le_trans h hw) (by norm_num)
  obtain hcases := Work.Asymptotics.eq_or_eq_S_of_re_eq_zero hD (imagAxis_re t ht) hj
  rcases hcases with hc | hc
  · -- `imagAxis t ht = w`: excluded by the distance bound
    exfalso
    rw [← hc] at hw
    have h2 : (imagAxis t ht : ℂ) - (t : ℂ)⁻¹ * Complex.I
        = ((t : ℂ) - (t : ℂ)⁻¹) * Complex.I := by
      rw [imagAxis_coe]; ring
    rw [h2, norm_mul, Complex.norm_I, mul_one] at hw
    have h3 : (1 / 2 : ℝ) < |t - t⁻¹| := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ t⁻¹ - t)]
      linarith
    have h4 : ‖(t : ℂ) - (t : ℂ)⁻¹‖ = |t - t⁻¹| := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [h4] at hw
    linarith
  · -- `imagAxis t ht = S • w`
    have hthis := congrArg (fun x : ℍ => ModularGroup.S • x) hc
    have hinv : ModularGroup.S • (ModularGroup.S • w) = w := by
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul]
      simp
    rw [hinv, S_imagAxis t ht] at hthis
    rw [← hthis, coe_imagAxis_inv]
    exact ht

lemma coincidence_p1 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (ht2 : t ≤ 2/3)
    {w : ℍ} (hw : ‖(w : ℂ) - ((1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ ≤ 1 / 2)
    (hj : jInvariantFun w = jInvariantFun (imagAxis t ht)) :
    (w : ℂ) = (1 : ℂ) + (t : ℂ)⁻¹ * Complex.I := by
  set w' : ℍ := (-1 : ℝ) +ᵥ w with hw'def
  have hcoe : (w' : ℂ) = (-1 : ℂ) + (w : ℂ) := by
    rw [hw'def]; rw [UpperHalfPlane.coe_vadd]; norm_num
  have hj' : jInvariantFun w' = jInvariantFun (imagAxis t ht) := by
    rw [hw'def, jInvariantFun_vadd_neg_one]; exact hj
  have hw' : ‖(w' : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ ≤ 1 / 2 := by
    rw [hcoe]
    rw [show (-1 : ℂ) + (w : ℂ) - (t : ℂ)⁻¹ * Complex.I
        = (w : ℂ) - ((1 : ℂ) + (t : ℂ)⁻¹ * Complex.I) by ring]
    exact hw
  have h := coincidence_axis ht ht1 ht2 hw' hj'
  rw [hcoe] at h
  linear_combination h

lemma coincidence_m1 {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (ht2 : t ≤ 2/3)
    {w : ℍ} (hw : ‖(w : ℂ) - ((-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ ≤ 1 / 2)
    (hj : jInvariantFun w = jInvariantFun (imagAxis t ht)) :
    (w : ℂ) = (-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I := by
  set w' : ℍ := (1 : ℝ) +ᵥ w with hw'def
  have hcoe : (w' : ℂ) = (1 : ℂ) + (w : ℂ) := by
    rw [hw'def]; rw [UpperHalfPlane.coe_vadd]; norm_num
  have hj' : jInvariantFun w' = jInvariantFun (imagAxis t ht) := by
    rw [hw'def, KernelFacts.jInvariantFun_vadd_one]; exact hj
  have hw' : ‖(w' : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ ≤ 1 / 2 := by
    rw [hcoe]
    rw [show (1 : ℂ) + (w : ℂ) - (t : ℂ)⁻¹ * Complex.I
        = (w : ℂ) - ((-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I) by ring]
    exact hw
  have h := coincidence_axis ht ht1 ht2 hw' hj'
  rw [hcoe] at h
  linear_combination h

/-! ## Power identities for the divisor -/

lemma delta_pow_eq (cΔ t : ℝ) (e : ℕ) (ht : 0 < t) :
    (cΔ * ((t:ℝ)^12)⁻¹ * Real.exp (-(2*Real.pi*t⁻¹))) ^ e
      = cΔ^e * (((t:ℝ)^12)^e)⁻¹ * Real.exp (-(2*Real.pi*(e:ℝ)*t⁻¹)) := by
  rw [mul_pow, mul_pow, inv_pow, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma inv_delta_pow_eq (cΔ t : ℝ) (e : ℕ) (ht : 0 < t) (hδ : 0 < cΔ) :
    (1 : ℝ) / (cΔ * ((t:ℝ)^12)⁻¹ * Real.exp (-(2*Real.pi*t⁻¹))) ^ e
      = (cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹) := by
  rw [one_div, delta_pow_eq cΔ t e ht, mul_inv, mul_inv, inv_inv, Real.exp_neg, inv_inv]

/-! ## The near-funnel bound for small `t` -/

lemma nearSharp (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (e : ℕ) (he : e = (if d = 8 then 1 else 2)) {c u : ℍ} {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (ht2 : t ≤ 2/5)
    {Cs As Ns cj cΔ : ℝ} (hCs : 0 < Cs) (hAs : 0 ≤ As) (hNs : 0 ≤ Ns)
    (hcj : 0 < cj) (hcΔ : 0 < cΔ)
    (hWide : ∀ w : ℍ, |w.re| ≤ 3/2 → 2 ≤ w.im →
        jInvariantFun w ≠ jInvariantFun (imagAxis t ht) →
        ‖KfunClear ℓ d w (imagAxis t ht)‖
          ≤ Cs * (1 + ‖(w:ℂ)‖) ^ As * (1 + t⁻¹) ^ Ns
            * Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
            * Real.exp (-(2*Real.pi*w.im)))
    (hΔ3 : ∀ v : ℍ, 1/3 ≤ v.im → cΔ * ‖qParamFun v‖ ≤ ‖DeltaFun v‖)
    (hcim : c.im = t⁻¹) (hcre : |c.re| ≤ 1)
    (hcz : jInvariantFun c = jInvariantFun (imagAxis t ht))
    (hz0 : KfunClear ℓ d c (imagAxis t ht) = 0)
    (hclas : ∀ w : ℍ, ‖(w:ℂ) - (c:ℂ)‖ ≤ 1/2 →
        jInvariantFun w = jInvariantFun (imagAxis t ht) → w = c)
    (hu : ‖(u:ℂ) - (c:ℂ)‖ < 1/4)
    (hne : jInvariantFun u ≠ jInvariantFun (imagAxis t ht))
    (hjlow : cj * Real.exp (2*Real.pi*t⁻¹) * ‖(u:ℂ) - (c:ℂ)‖
      ≤ ‖jInvariantFun u - jInvariantFun (imagAxis t ht)‖) :
    ‖Kfun ℓ d u (imagAxis t ht)‖
      ≤ 8 * Cs * 3 ^ As * Real.exp (3*Real.pi/2) / (cj * cΔ ^ e)
        * (1 + t⁻¹) ^ (As + Ns + ((12*e : ℕ) : ℝ)) * Real.exp (-(Real.pi * t⁻¹)) := by
  have hpinv : (0:ℝ) < t⁻¹ := inv_pos.mpr ht
  have hone : (5:ℝ)/2 ≤ t⁻¹ := by
    have h := one_div_le_one_div_of_le ht ht2
    simp only [one_div] at h
    norm_num at h
    exact h
  have hrate : (if d = 8 then Real.pi else 3*Real.pi) + 2*Real.pi - 2*Real.pi*(e:ℝ)
      = Real.pi := by
    rw [he]; split_ifs <;> push_cast <;> ring
  -- norm bound on `c`
  have hcnorm : ‖(c:ℂ)‖ ≤ 1 + t⁻¹ := by
    have hnormc : ‖(c:ℂ)‖ ≤ |(c:ℂ).re| + |(c:ℂ).im| := by
      have hsq : ‖(c:ℂ)‖ ^ 2 ≤ (|(c:ℂ).re| + |(c:ℂ).im|) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        nlinarith [abs_nonneg (c:ℂ).re, abs_nonneg (c:ℂ).im,
          sq_abs (c:ℂ).re, sq_abs (c:ℂ).im,
          mul_nonneg (abs_nonneg (c:ℂ).re) (abs_nonneg (c:ℂ).im)]
      have hnn : 0 ≤ |(c:ℂ).re| + |(c:ℂ).im| := by positivity
      nlinarith [norm_nonneg (c:ℂ), hsq, hnn]
    have hre : |(c:ℂ).re| ≤ 1 := by rw [UpperHalfPlane.coe_re]; exact hcre
    have him : |(c:ℂ).im| ≤ t⁻¹ := by
      rw [UpperHalfPlane.coe_im, hcim, abs_of_pos hpinv]
    linarith
  -- the ball bound
  set M : ℝ := Cs * (1 + ‖(c:ℂ)‖ + 1/2) ^ As * (1 + t⁻¹) ^ Ns
      * Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
      * Real.exp (-(2*Real.pi*(t⁻¹ - 1/2))) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hMbound : ∀ w : ℍ, ‖(w:ℂ) - (c:ℂ)‖ ≤ 1/2 →
      ‖KfunClear ℓ d w (imagAxis t ht)‖ ≤ M := by
    intro w hw
    by_cases hwj : jInvariantFun w = jInvariantFun (imagAxis t ht)
    · rw [hclas w hw hwj, hz0]
      simp only [norm_zero]
      exact le_of_lt hMpos
    · have hwtri : ‖(w:ℂ)‖ ≤ ‖(c:ℂ)‖ + ‖(w:ℂ) - (c:ℂ)‖ := by
        have h := norm_add_le (c:ℂ) ((w:ℂ) - (c:ℂ))
        rw [show (c:ℂ) + ((w:ℂ) - (c:ℂ)) = (w:ℂ) by ring] at h
        exact h
      have habsw : |w.re| ≤ 3/2 := by
        have h1 : |w.re - c.re| ≤ ‖(w:ℂ) - (c:ℂ)‖ := by
          have h := Complex.abs_re_le_norm ((w:ℂ) - (c:ℂ))
          rw [Complex.sub_re, UpperHalfPlane.coe_re, UpperHalfPlane.coe_re] at h
          exact h
        have h2 : |w.re| ≤ |c.re| + |w.re - c.re| := by
          have h := abs_add_le (c.re) (w.re - c.re)
          rw [show c.re + (w.re - c.re) = w.re by ring] at h
          exact h
        linarith [le_trans h1 hw]
      have habsim : t⁻¹ - 1/2 ≤ w.im := by
        have h1 : |w.im - c.im| ≤ ‖(w:ℂ) - (c:ℂ)‖ := by
          have h := Complex.abs_im_le_norm ((w:ℂ) - (c:ℂ))
          rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h
          exact h
        have h2 : c.im - 1/2 ≤ w.im := by
          have h3 := (abs_le.mp (le_trans h1 hw)).1
          linarith
        rw [hcim] at h2
        exact h2
      have hwim : 2 ≤ w.im := by linarith
      have h1 := hWide w habsw hwim hwj
      have hX : (1 + ‖(w:ℂ)‖) ^ As ≤ (1 + ‖(c:ℂ)‖ + 1/2) ^ As := by
        apply Real.rpow_le_rpow (by positivity) _ hAs
        linarith
      have hY : Real.exp (-(2*Real.pi*w.im))
          ≤ Real.exp (-(2*Real.pi*(t⁻¹ - 1/2))) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos]
      have s1 : Cs * (1 + ‖(w:ℂ)‖) ^ As ≤ Cs * (1 + ‖(c:ℂ)‖ + 1/2) ^ As :=
        mul_le_mul_of_nonneg_left hX hCs.le
      have s2 : Cs * (1 + ‖(w:ℂ)‖) ^ As * (1 + t⁻¹) ^ Ns
          ≤ Cs * (1 + ‖(c:ℂ)‖ + 1/2) ^ As * (1 + t⁻¹) ^ Ns :=
        mul_le_mul_of_nonneg_right s1 (by positivity)
      have s3 : Cs * (1 + ‖(w:ℂ)‖) ^ As * (1 + t⁻¹) ^ Ns
            * Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
          ≤ Cs * (1 + ‖(c:ℂ)‖ + 1/2) ^ As * (1 + t⁻¹) ^ Ns
            * Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹)) :=
        mul_le_mul_of_nonneg_right s2 (Real.exp_pos _).le
      have s4 := mul_le_mul_4 s3 hY (Real.exp_pos _).le (by positivity)
      exact le_trans h1 s4
  -- the divisor
  have hδzpos : 0 < cΔ * ((t:ℝ)^12)⁻¹ * Real.exp (-(2*Real.pi*t⁻¹)) := by positivity
  have hΔz : cΔ * ((t:ℝ)^12)⁻¹ * Real.exp (-(2*Real.pi*t⁻¹))
      ≤ ‖DeltaFun (imagAxis t ht)‖ := deltaLowerImagAxis cΔ hcΔ hΔ3 t ht ht1
  have huim2 : 2 ≤ u.im := by
    have h1 : |u.im - c.im| ≤ ‖(u:ℂ) - (c:ℂ)‖ := by
      have h := Complex.abs_im_le_norm ((u:ℂ) - (c:ℂ))
      rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h
      exact h
    have h2 : c.im - 1/4 ≤ u.im := by
      have h3 := (abs_le.mp (le_of_lt (lt_of_le_of_lt h1 hu))).1
      linarith
    rw [hcim] at h2
    linarith
  have hΔu : (1/2 : ℝ) * Real.exp (-(2*Real.pi*u.im)) ≤ ‖DeltaFun u‖ :=
    DeltaFun_funnel_lower_sharp huim2
  have hrc : (1:ℝ)/2 < c.im := by
    rw [hcim, lt_inv_comm₀ (by norm_num : (0:ℝ) < 1/2) ht]
    norm_num
    linarith [ht2]
  have hraw := Kfun_le_one_zero (ℓ := ℓ) (d := d) (hd := hd) e he (z := imagAxis t ht)
    (c := c) (τ := u) ht (by norm_num) hrc hcj hδzpos hMpos hcz hMbound hz0
    (by linarith [hu] : ‖(u:ℂ) - (c:ℂ)‖ < 1/2/2) hne hjlow hΔu hΔz
  -- final arithmetic
  have huim : u.im ≤ t⁻¹ + 1/4 := by
    have h1 : |u.im - c.im| ≤ ‖(u:ℂ) - (c:ℂ)‖ := by
      have h := Complex.abs_im_le_norm ((u:ℂ) - (c:ℂ))
      rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h
      exact h
    have h2 : u.im ≤ c.im + 1/4 := by
      have h3 := (abs_le.mp (le_of_lt (lt_of_le_of_lt h1 hu))).2
      linarith
    rw [hcim] at h2
    exact h2
  have hMle : M ≤ Cs * 3^As * (1 + t⁻¹) ^ (As + Ns)
      * Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
      * Real.exp (-(2*Real.pi*t⁻¹)) * Real.exp Real.pi := by
    rw [hMdef]
    have h1 : (1 + ‖(c:ℂ)‖ + 1/2) ^ As ≤ 3^As * (1 + t⁻¹)^As := by
      have h2 : 1 + ‖(c:ℂ)‖ + 1/2 ≤ 3 * (1 + t⁻¹) := by linarith [hcnorm]
      calc (1 + ‖(c:ℂ)‖ + 1/2) ^ As ≤ (3 * (1 + t⁻¹)) ^ As :=
            Real.rpow_le_rpow (by positivity) h2 hAs
        _ = 3^As * (1 + t⁻¹)^As := Real.mul_rpow (by norm_num) (by positivity)
    have h2 : (1 + t⁻¹) ^ Ns * (1 + t⁻¹) ^ As = (1 + t⁻¹) ^ (As + Ns) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring
    have h3 : Real.exp (-(2*Real.pi*(t⁻¹ - 1/2)))
        ≤ Real.exp (-(2*Real.pi*t⁻¹)) * Real.exp Real.pi := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    have t1 : Cs * (1 + ‖(c:ℂ)‖ + 1/2) ^ As ≤ Cs * (3^As * (1 + t⁻¹)^As) :=
      mul_le_mul_of_nonneg_left h1 hCs.le
    have t2 : Cs * (1 + ‖(c:ℂ)‖ + 1/2) ^ As * (1 + t⁻¹) ^ Ns
        ≤ Cs * (3^As * (1 + t⁻¹)^As) * (1 + t⁻¹) ^ Ns :=
      mul_le_mul_of_nonneg_right t1 (by positivity)
    have t3 : Cs * (1 + ‖(c:ℂ)‖ + 1/2) ^ As * (1 + t⁻¹) ^ Ns
          * Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
        ≤ Cs * (3^As * (1 + t⁻¹)^As) * (1 + t⁻¹) ^ Ns
          * Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹)) :=
      mul_le_mul_of_nonneg_right t2 (Real.exp_pos _).le
    have t4 := mul_le_mul_4 t3 h3 (Real.exp_pos _).le (by positivity)
    refine le_trans t4 (le_of_eq ?_)
    rw [← h2]
    ring
  have hE : Real.exp (2*Real.pi*u.im) * Real.exp (-(2*Real.pi*t⁻¹))
      ≤ Real.exp (Real.pi/2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hδinv : (1:ℝ) / (cΔ * ((t:ℝ)^12)⁻¹ * Real.exp (-(2*Real.pi*t⁻¹))) ^ e
      = (cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹) :=
    inv_delta_pow_eq cΔ t e ht hcΔ
  have hpow : ((t:ℝ)^12)^e * (1 + t⁻¹) ^ (As + Ns)
      ≤ (1 + t⁻¹) ^ (As + Ns + ((12*e : ℕ) : ℝ)) := by
    have hbase : (1:ℝ) ≤ 1 + t⁻¹ := by linarith
    have h2 : ((t:ℝ)^12)^e ≤ (1 + t⁻¹) ^ ((12*e : ℕ) : ℝ) := by
      have h1 : ((t:ℝ)^12)^e = (t : ℝ) ^ (12*e) := by rw [← pow_mul]
      rw [h1, Real.rpow_natCast]
      calc (t : ℝ) ^ (12*e) ≤ (1:ℝ) ^ (12*e) := pow_le_pow_left₀ ht.le ht1 _
        _ = 1 := one_pow _
        _ ≤ (1 + t⁻¹) ^ (12*e) := one_le_pow₀ hbase
    have h3 : (1 + t⁻¹) ^ (As + Ns + ((12*e : ℕ) : ℝ))
        = (1 + t⁻¹) ^ (As + Ns) * (1 + t⁻¹) ^ ((12*e : ℕ) : ℝ) := by
      rw [show As + Ns + ((12*e : ℕ) : ℝ) = (As + Ns) + ((12*e : ℕ) : ℝ) by ring,
        Real.rpow_add (by positivity)]
    rw [h3]
    have h4 : (0:ℝ) ≤ (1 + t⁻¹) ^ (As + Ns) := by positivity
    calc ((t:ℝ)^12)^e * (1 + t⁻¹) ^ (As + Ns)
        ≤ (1 + t⁻¹) ^ ((12*e : ℕ) : ℝ) * (1 + t⁻¹) ^ (As + Ns) :=
          mul_le_mul_of_nonneg_right h2 h4
      _ = (1 + t⁻¹) ^ (As + Ns) * (1 + t⁻¹) ^ ((12*e : ℕ) : ℝ) := by ring
  have hExp : Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
        * Real.exp (-(2*Real.pi*t⁻¹)) * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)
        * Real.exp Real.pi * Real.exp (Real.pi/2)
      = Real.exp (-(Real.pi * t⁻¹)) * Real.exp (3*Real.pi/2) := by
    have harg : -((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹) + (-(2*Real.pi*t⁻¹))
        + (2*Real.pi*(e:ℝ)*t⁻¹) + Real.pi + Real.pi/2
        = (-(Real.pi * t⁻¹)) + (3*Real.pi/2) := by
      have h2 : (if d = 8 then Real.pi else 3*Real.pi) = Real.pi + 2*Real.pi*(e:ℝ) - 2*Real.pi := by
        linarith [hrate]
      rw [h2]; ring
    calc Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
          * Real.exp (-(2*Real.pi*t⁻¹)) * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)
          * Real.exp Real.pi * Real.exp (Real.pi/2)
        = Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹) + (-(2*Real.pi*t⁻¹))
            + (2*Real.pi*(e:ℝ)*t⁻¹) + Real.pi + Real.pi/2) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ = Real.exp ((-(Real.pi * t⁻¹)) + (3*Real.pi/2)) := by rw [harg]
      _ = Real.exp (-(Real.pi * t⁻¹)) * Real.exp (3*Real.pi/2) := by rw [Real.exp_add]
  have hfinal : 4 * M / ((1/2) * cj * (cΔ * ((t:ℝ)^12)⁻¹ * Real.exp (-(2*Real.pi*t⁻¹))) ^ e)
        * Real.exp (2*Real.pi*u.im) * Real.exp (-(2*Real.pi*t⁻¹))
      ≤ 8 * Cs * 3 ^ As * Real.exp (3*Real.pi/2) / (cj * cΔ ^ e)
        * (1 + t⁻¹) ^ (As + Ns + ((12*e : ℕ) : ℝ)) * Real.exp (-(Real.pi * t⁻¹)) := by
    have hfac : 4 * M / ((1/2) * cj * (cΔ * ((t:ℝ)^12)⁻¹ * Real.exp (-(2*Real.pi*t⁻¹))) ^ e)
          * Real.exp (2*Real.pi*u.im) * Real.exp (-(2*Real.pi*t⁻¹))
        = 8 * M * ((1:ℝ) / (cΔ * ((t:ℝ)^12)⁻¹ * Real.exp (-(2*Real.pi*t⁻¹))) ^ e) / cj
          * (Real.exp (2*Real.pi*u.im) * Real.exp (-(2*Real.pi*t⁻¹))) := by
      field_simp
      ring
    rw [hfac, hδinv]
    -- abbreviations used only for the monotonicity steps
    have hYnn : (0:ℝ) ≤ 8 * ((cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)) / cj := by
      positivity
    have hBnn : (0:ℝ) ≤ 8 * (Cs * 3^As * (1 + t⁻¹) ^ (As + Ns)
              * Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
              * Real.exp (-(2*Real.pi*t⁻¹)) * Real.exp Real.pi)
            * ((cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)) / cj := by
      positivity
    have hAn : (0:ℝ) ≤ 8 * M * ((cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)) / cj := by
      positivity
    calc 8 * M * ((cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)) / cj
          * (Real.exp (2*Real.pi*u.im) * Real.exp (-(2*Real.pi*t⁻¹)))
        ≤ 8 * M * ((cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)) / cj
          * Real.exp (Real.pi/2) :=
          mul_le_mul_of_nonneg_left hE hAn
      _ ≤ 8 * (Cs * 3^As * (1 + t⁻¹) ^ (As + Ns)
              * Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
              * Real.exp (-(2*Real.pi*t⁻¹)) * Real.exp Real.pi)
            * ((cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)) / cj
            * Real.exp (Real.pi/2) := by
          have h8Y : (0:ℝ) ≤ 8
              * ((cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)) / cj
              * Real.exp (Real.pi/2) := by positivity
          have h := mul_le_mul_of_nonneg_right hMle h8Y
          calc 8 * M * ((cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)) / cj
                * Real.exp (Real.pi/2)
              = M * (8 * ((cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)) / cj
                * Real.exp (Real.pi/2)) := by ring
            _ ≤ (Cs * 3^As * (1 + t⁻¹) ^ (As + Ns)
                  * Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
                  * Real.exp (-(2*Real.pi*t⁻¹)) * Real.exp Real.pi)
                * (8 * ((cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)) / cj
                  * Real.exp (Real.pi/2)) := h
            _ = 8 * (Cs * 3^As * (1 + t⁻¹) ^ (As + Ns)
                  * Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
                  * Real.exp (-(2*Real.pi*t⁻¹)) * Real.exp Real.pi)
                * ((cΔ^e)⁻¹ * ((t:ℝ)^12)^e * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)) / cj
                * Real.exp (Real.pi/2) := by ring
      _ = 8 * Cs * 3 ^ As / cj * (cΔ ^ e)⁻¹
            * (((t:ℝ)^12)^e * (1 + t⁻¹) ^ (As + Ns))
            * (Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
              * Real.exp (-(2*Real.pi*t⁻¹)) * Real.exp (2*Real.pi*(e:ℝ)*t⁻¹)
              * Real.exp Real.pi * Real.exp (Real.pi/2)) := by ring_nf
      _ = 8 * Cs * 3 ^ As / cj * (cΔ ^ e)⁻¹
            * (((t:ℝ)^12)^e * (1 + t⁻¹) ^ (As + Ns))
            * (Real.exp (-(Real.pi * t⁻¹)) * Real.exp (3*Real.pi/2)) := by rw [hExp]
      _ ≤ 8 * Cs * 3 ^ As / cj * (cΔ ^ e)⁻¹ * (1 + t⁻¹) ^ (As + Ns + ((12*e : ℕ) : ℝ))
            * (Real.exp (-(Real.pi * t⁻¹)) * Real.exp (3*Real.pi/2)) :=
          mul_le_mul_4 (mul_le_mul_4 le_rfl hpow (by positivity) (by positivity))
            le_rfl (by positivity) (by positivity)
      _ = 8 * Cs * 3 ^ As * Real.exp (3*Real.pi/2) / (cj * cΔ ^ e)
            * (1 + t⁻¹) ^ (As + Ns + ((12*e : ℕ) : ℝ)) * Real.exp (-(Real.pi * t⁻¹)) := by
          ring_nf
  exact hraw.trans hfinal

/-! ## Regime A: the near bound for `t ≤ 2/5` -/

theorem nearA (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C m : ℝ, 0 < C ∧ 0 ≤ m ∧
      ∀ (t : ℝ) (ht : 0 < t), t ≤ 2/5 →
        ∀ τ : ℍ, τ ∈ DomainD → 2 ≤ τ.im →
          jInvariantFun τ ≠ jInvariantFun (imagAxis t ht) →
          (‖(τ : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ < 1/4 ∨
           ‖(τ : ℂ) - ((1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ < 1/4 ∨
           ‖(τ : ℂ) - ((-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ < 1/4) →
          ‖Kaxis (Kfun ℓ d) τ t‖
            ≤ C * (1 + 1/t) ^ m * Real.exp (-(Real.pi/t)) := by
  obtain ⟨Cs, As, Ns, hCs, hAs, hNs, hWide⟩ := KfunClearSharpWide ℓ d hd
  obtain ⟨cj, hcj, hJ⟩ := jLowerBranches
  obtain ⟨cΔ, hcΔ, hΔ3⟩ := delta_lower_third
  have hApos : (0:ℝ) < 8 * Cs * 3 ^ As * Real.exp (3*Real.pi/2)
      / (cj * cΔ ^ (if d = 8 then 1 else 2)) := by positivity
  refine ⟨8 * Cs * 3 ^ As * Real.exp (3*Real.pi/2) / (cj * cΔ ^ (if d = 8 then 1 else 2)),
    As + Ns + ((12 * (if d = 8 then 1 else 2) : ℕ) : ℝ), hApos, by positivity, ?_⟩
  intro t ht ht2 τ hD h2 hne hnear
  have hWide' : ∀ w : ℍ, |w.re| ≤ 3/2 → 2 ≤ w.im →
      jInvariantFun w ≠ jInvariantFun (imagAxis t ht) →
      ‖KfunClear ℓ d w (imagAxis t ht)‖
        ≤ Cs * (1 + ‖(w:ℂ)‖) ^ As * (1 + t⁻¹) ^ Ns
          * Real.exp (-((if d = 8 then Real.pi else 3*Real.pi) * t⁻¹))
          * Real.exp (-(2*Real.pi*w.im)) := by
    intro w h1 h2' h3
    have h := hWide w t ht h1 h2' (by linarith) h3
    simpa only [one_div] using h
  have hJt := hJ t ht (by linarith) τ hD h2
  rcases hnear with hmid | hrest
  · -- middle branch: `c = i/t`
    have hg : (((imagAxis t⁻¹ (inv_pos.mpr ht)) : ℍ) : ℂ) = (t:ℂ)⁻¹ * Complex.I := by
      simp only [Work.Kernels.imagAxis, Complex.ofReal_inv]
    have hcim : (imagAxis t⁻¹ (inv_pos.mpr ht)).im = t⁻¹ := by simp [Work.Kernels.imagAxis]
    have hcre : |(imagAxis t⁻¹ (inv_pos.mpr ht)).re| ≤ 1 := by simp [Work.Kernels.imagAxis]
    have hcz : jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht))
        = jInvariantFun (imagAxis t ht) := by
      rw [← S_imagAxis t ht, KernelFacts.jInvariantFun_S_smul]
    have hz0 : KfunClear ℓ d (imagAxis t⁻¹ (inv_pos.mpr ht)) (imagAxis t ht) = 0 := by
      rw [← S_imagAxis t ht]; exact KL.KfunClear_S_self ℓ d hd (imagAxis t ht)
    have hu : ‖(τ:ℂ) - (((imagAxis t⁻¹ (inv_pos.mpr ht)) : ℍ) : ℂ)‖ < 1/4 := by
      rw [hg]; exact hmid
    have hjl : cj * Real.exp (2*Real.pi*t⁻¹)
        * ‖(τ:ℂ) - (((imagAxis t⁻¹ (inv_pos.mpr ht)) : ℍ) : ℂ)‖
        ≤ ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ := by
      rw [hg]; exact hJt.1 hmid
    have hcl : ∀ w : ℍ, ‖(w:ℂ) - (((imagAxis t⁻¹ (inv_pos.mpr ht)) : ℍ) : ℂ)‖ ≤ 1/2 →
        jInvariantFun w = jInvariantFun (imagAxis t ht) → w = imagAxis t⁻¹ (inv_pos.mpr ht) := by
      intro w hw hwj
      have hw' : ‖(w:ℂ) - ((t:ℂ)⁻¹ * Complex.I)‖ ≤ 1/2 := by rw [hg] at hw; exact hw
      exact UpperHalfPlane.ext ((coincidence_axis ht (by linarith) (by linarith : t ≤ 2/3) hw' hwj).trans hg.symm)
    have h := nearSharp ℓ d hd (if d = 8 then 1 else 2) rfl (c := imagAxis t⁻¹ (inv_pos.mpr ht))
      (u := τ) ht (by linarith) ht2 hCs hAs hNs hcj hcΔ hWide' hΔ3 hcim hcre hcz hz0 hcl hu hne hjl
    simpa only [one_div, one_mul, div_eq_mul_inv, Kaxis, dif_pos ht] using h
  · rcases hrest with hp1 | hm1
    · -- branch `c = 1 + i/t`
      have hg : ((((1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) : ℂ)
          = (1:ℂ) + ((t:ℂ)⁻¹ * Complex.I) := by
        rw [UpperHalfPlane.coe_vadd]
        have h2 : (((imagAxis t⁻¹ (inv_pos.mpr ht)) : ℍ) : ℂ) = (t:ℂ)⁻¹ * Complex.I := by
          simp only [Work.Kernels.imagAxis, Complex.ofReal_inv]
        rw [h2]
        norm_num
      have hcim : ((((1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ))).im = t⁻¹ := by
        rw [im_vadd']; simp [Work.Kernels.imagAxis]
      have hcre : |((((1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ))).re| ≤ 1 := by
        rw [re_vadd']; simp [Work.Kernels.imagAxis]
      have hcz : jInvariantFun (((1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ))
          = jInvariantFun (imagAxis t ht) := by
        rw [KernelFacts.jInvariantFun_vadd_one, ← S_imagAxis t ht, KernelFacts.jInvariantFun_S_smul]
      have hz0 : KfunClear ℓ d (((1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) (imagAxis t ht) = 0 := by
        rw [← S_imagAxis t ht]; exact KfunClear_TS_zero ℓ d hd (imagAxis t ht)
      have hu : ‖(τ:ℂ) - ((((1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) : ℂ)‖ < 1/4 := by
        rw [hg]; exact hp1
      have hjl : cj * Real.exp (2*Real.pi*t⁻¹)
          * ‖(τ:ℂ) - ((((1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) : ℂ)‖
          ≤ ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ := by
        rw [hg]; exact hJt.2.1 hp1
      have hcl : ∀ w : ℍ, ‖(w:ℂ) - ((((1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) : ℂ)‖ ≤ 1/2 →
          jInvariantFun w = jInvariantFun (imagAxis t ht) →
          w = (((1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) := by
        intro w hw hwj
        have hw' : ‖(w:ℂ) - ((1:ℂ) + (t:ℂ)⁻¹ * Complex.I)‖ ≤ 1/2 := by rw [hg] at hw; exact hw
        exact UpperHalfPlane.ext ((coincidence_p1 ht (by linarith) (by linarith : t ≤ 2/3) hw' hwj).trans hg.symm)
      have h := nearSharp ℓ d hd (if d = 8 then 1 else 2) rfl
        (c := (((1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ))) (u := τ)
        ht (by linarith) ht2 hCs hAs hNs hcj hcΔ hWide' hΔ3 hcim hcre hcz hz0 hcl hu hne hjl
      simpa only [one_div, one_mul, div_eq_mul_inv, Kaxis, dif_pos ht] using h
    · -- branch `c = -1 + i/t`
      have hg : ((((-1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) : ℂ)
          = (-1:ℂ) + ((t:ℂ)⁻¹ * Complex.I) := by
        rw [UpperHalfPlane.coe_vadd]
        have h2 : (((imagAxis t⁻¹ (inv_pos.mpr ht)) : ℍ) : ℂ) = (t:ℂ)⁻¹ * Complex.I := by
          simp only [Work.Kernels.imagAxis, Complex.ofReal_inv]
        rw [h2]
        norm_num
      have hcim : ((((-1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ))).im = t⁻¹ := by
        rw [im_vadd']; simp [Work.Kernels.imagAxis]
      have hcre : |((((-1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ))).re| ≤ 1 := by
        rw [re_vadd']; simp [Work.Kernels.imagAxis]
      have hcz : jInvariantFun (((-1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ))
          = jInvariantFun (imagAxis t ht) := by
        rw [jInvariantFun_vadd_neg_one, ← S_imagAxis t ht, KernelFacts.jInvariantFun_S_smul]
      have hz0 : KfunClear ℓ d (((-1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) (imagAxis t ht) = 0 := by
        rw [← S_imagAxis t ht]; exact KfunClear_TinvS_zero ℓ d hd (imagAxis t ht)
      have hu : ‖(τ:ℂ) - ((((-1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) : ℂ)‖ < 1/4 := by
        rw [hg]; exact hm1
      have hjl : cj * Real.exp (2*Real.pi*t⁻¹)
          * ‖(τ:ℂ) - ((((-1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) : ℂ)‖
          ≤ ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ := by
        rw [hg]; exact hJt.2.2 hm1
      have hcl : ∀ w : ℍ, ‖(w:ℂ) - ((((-1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) : ℂ)‖ ≤ 1/2 →
          jInvariantFun w = jInvariantFun (imagAxis t ht) →
          w = (((-1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) := by
        intro w hw hwj
        have hw' : ‖(w:ℂ) - ((-1:ℂ) + (t:ℂ)⁻¹ * Complex.I)‖ ≤ 1/2 := by rw [hg] at hw; exact hw
        exact UpperHalfPlane.ext ((coincidence_m1 ht (by linarith) (by linarith : t ≤ 2/3) hw' hwj).trans hg.symm)
      have h := nearSharp ℓ d hd (if d = 8 then 1 else 2) rfl
        (c := (((-1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ))) (u := τ)
        ht (by linarith) ht2 hCs hAs hNs hcj hcΔ hWide' hΔ3 hcim hcre hcz hz0 hcl hu hne hjl
      simpa only [one_div, one_mul, div_eq_mul_inv, Kaxis, dif_pos ht] using h

/-! ## Regime B: the near bound for `2/5 < t ≤ 1` -/

theorem nearMid (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (t : ℝ) (ht : 0 < t), 2/5 < t → t ≤ 1 →
        ∀ τ : ℍ, τ ∈ DomainD → 2 ≤ τ.im →
          jInvariantFun τ ≠ jInvariantFun (imagAxis t ht) →
          (‖(τ : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ < 1/4 ∨
           ‖(τ : ℂ) - ((1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ < 1/4 ∨
           ‖(τ : ℂ) - ((-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ < 1/4) →
          ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨cj, hcj, hJ⟩ := jLowerBranches
  obtain ⟨cΔ, hcΔ, hΔ3⟩ := delta_lower_third
  obtain ⟨M, hMpos, hMb⟩ := KL.exists_bound_KfunClear_of_balls ℓ d hd
    (⟨((3:ℂ))*Complex.I, by simp⟩ : ℍ) (⟨(((3:ℝ)/4 : ℂ))*Complex.I, by simp⟩ : ℍ)
    (R₁ := 29/10) (R₂ := 1/2) (by norm_num) (by norm_num)
  set δz : ℝ := cΔ * Real.exp (-(5*Real.pi)) with hδzdef
  have hδzpos : 0 < δz := by rw [hδzdef]; positivity
  refine ⟨8 * M * Real.exp (Real.pi/2) / (cj * δz ^ (if d = 8 then 1 else 2)), by positivity, ?_⟩
  intro t ht ht2' ht1 τ hD h2 hne hnear
  have htinv_lo : t⁻¹ < 5/2 := by
    rw [← inv_lt_comm₀ (by norm_num : (0:ℝ) < 5/2) ht]
    norm_num
    exact ht2'
  -- bound `KfunClear` on the ball around any of the three points
  have hball : ∀ (c : ℍ), c.im = t⁻¹ → |c.re| ≤ 1 →
      ∀ w : ℍ, ‖(w:ℂ) - (c:ℂ)‖ ≤ 1/2 → ‖KfunClear ℓ d w (imagAxis t ht)‖ ≤ M := by
    intro c hcim hcre w hw
    apply hMb
    · -- `w ∈ B(5i/2, 2)`
      have h1 : ‖(w:ℂ) - (3:ℂ)*Complex.I‖
          ≤ ‖(w:ℂ) - (c:ℂ)‖ + ‖(c:ℂ) - (3:ℂ)*Complex.I‖ := by
        have h := norm_add_le ((w:ℂ) - (c:ℂ)) ((c:ℂ) - (3:ℂ)*Complex.I)
        rw [show ((w:ℂ) - (c:ℂ)) + ((c:ℂ) - (3:ℂ)*Complex.I)
            = (w:ℂ) - (3:ℂ)*Complex.I by ring] at h
        exact h
      have h2c : ‖(c:ℂ) - (3:ℂ)*Complex.I‖ ≤ 9/4 := by
        have hsq : ‖(c:ℂ) - (3:ℂ)*Complex.I‖ ^ 2 = (c.re)^2 + (t⁻¹ - 3)^2 := by
          have h5r : (((3:ℂ))*Complex.I).re = 0 := by simp [Complex.mul_re]
          have h5i : (((3:ℂ))*Complex.I).im = 3 := by simp [Complex.mul_im]
          rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
            UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hcim, h5r, h5i]
          ring
        have hnn : (0:ℝ) ≤ ‖(c:ℂ) - (3:ℂ)*Complex.I‖ := norm_nonneg _
        have hcre' : c.re ^ 2 ≤ 1 := by nlinarith [abs_le.mp hcre]
        have htinv_ge1 : (1:ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
        have him' : (t⁻¹ - 3) ^ 2 ≤ 4 := by
          have h3 : |t⁻¹ - 3| ≤ 2 := by
            rw [abs_le]; constructor <;> linarith [htinv_lo, htinv_ge1]
          nlinarith [abs_le.mp h3]
        nlinarith [hsq, hcre', him', hnn]
      linarith
    · -- `it ∈ B(3i/4, 1/2)`
      have hcoe : ((imagAxis t ht : ℍ) : ℂ) = (t:ℂ) * Complex.I := imagAxis_coe t ht
      have h2 : (t:ℂ) * Complex.I - (((3:ℝ)/4 : ℂ)) * Complex.I
          = ((t - 3/4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
      have h3 : ‖((imagAxis t ht : ℍ) : ℂ) - (((3:ℝ)/4 : ℂ)) * Complex.I‖
          = |t - 3/4| := by
        rw [hcoe, h2, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [h3, abs_le]
      constructor <;> linarith
  have hΔzt : δz ≤ ‖DeltaFun (imagAxis t ht)‖ := by
    have h := deltaLowerImagAxis cΔ hcΔ hΔ3 t ht ht1
    have h1 : cΔ * Real.exp (-(5*Real.pi))
        ≤ cΔ * ((t:ℝ)^12)⁻¹ * Real.exp (-(2*Real.pi*t⁻¹)) := by
      have hexp : Real.exp (-(5*Real.pi)) ≤ Real.exp (-(2*Real.pi*t⁻¹)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos, ht2']
      have hpw : (1:ℝ) ≤ ((t:ℝ)^12)⁻¹ := by
        have h2 : (t:ℝ)^12 ≤ 1 := pow_le_one₀ ht.le ht1
        exact (one_le_inv₀ (pow_pos ht 12)).mpr h2
      have h4 : cΔ * Real.exp (-(5*Real.pi)) = cΔ * 1 * Real.exp (-(5*Real.pi)) := by ring
      rw [h4]
      exact mul_le_mul_4 (mul_le_mul_of_nonneg_left hpw hcΔ.le) hexp
        (Real.exp_pos _).le (by positivity)
    rw [hδzdef]
    exact le_trans h1 h
  have hτim : ∀ (c : ℍ), c.im = t⁻¹ → ‖(τ:ℂ) - (c:ℂ)‖ < 1/4 → τ.im ≤ t⁻¹ + 1/4 := by
    intro c hcim hdist
    have h1 : |τ.im - c.im| ≤ ‖(τ:ℂ) - (c:ℂ)‖ := by
      have h := Complex.abs_im_le_norm ((τ:ℂ) - (c:ℂ))
      rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h
      exact h
    have h2 : τ.im ≤ c.im + 1/4 := by
      have := (abs_le.mp (le_of_lt (lt_of_le_of_lt h1 hdist))).2
      linarith
    rw [hcim] at h2
    exact h2
  have hΔτ : (1/2 : ℝ) * Real.exp (-(2*Real.pi*τ.im)) ≤ ‖DeltaFun τ‖ :=
    DeltaFun_funnel_lower_sharp h2
  have key : ∀ (c : ℍ), c.im = t⁻¹ → |c.re| ≤ 1 →
      jInvariantFun c = jInvariantFun (imagAxis t ht) →
      KfunClear ℓ d c (imagAxis t ht) = 0 →
      ‖(τ:ℂ) - (c:ℂ)‖ < 1/4 →
      cj * Real.exp (2*Real.pi*t⁻¹) * ‖(τ:ℂ) - (c:ℂ)‖
        ≤ ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ →
      ‖Kfun ℓ d τ (imagAxis t ht)‖
        ≤ 8 * M * Real.exp (Real.pi/2) / (cj * δz ^ (if d = 8 then 1 else 2)) := by
    intro c hcim hcre hcz hz0 hu hjlow
    have hrc : (1:ℝ)/2 < c.im := by
      rw [hcim]
      linarith [(one_le_inv₀ ht).mpr ht1]
    have hraw := Kfun_le_one_zero (ℓ := ℓ) (d := d) (hd := hd) _ rfl
      (z := imagAxis t ht) (c := c) (τ := τ) ht (by norm_num) hrc hcj hδzpos hMpos hcz
      (hball c hcim hcre) hz0 (by linarith [hu] : ‖(τ:ℂ) - (c:ℂ)‖ < 1/2/2) hne hjlow hΔτ hΔzt
    refine hraw.trans ?_
    have hE : Real.exp (2*Real.pi*τ.im) * Real.exp (-(2*Real.pi*t⁻¹))
        ≤ Real.exp (Real.pi/2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h3 := hτim c hcim hu
      nlinarith [Real.pi_pos]
    have hA : (0:ℝ) ≤ 4 * M / ((1/2) * cj * δz ^ (if d = 8 then 1 else 2)) := by positivity
    calc 4 * M / ((1/2) * cj * δz ^ (if d = 8 then 1 else 2))
          * Real.exp (2*Real.pi*τ.im) * Real.exp (-(2*Real.pi*t⁻¹))
        = (4 * M / ((1/2) * cj * δz ^ (if d = 8 then 1 else 2)))
          * (Real.exp (2*Real.pi*τ.im) * Real.exp (-(2*Real.pi*t⁻¹))) := by ring
      _ ≤ (4 * M / ((1/2) * cj * δz ^ (if d = 8 then 1 else 2))) * Real.exp (Real.pi/2) :=
          mul_le_mul_of_nonneg_left hE hA
      _ = 8 * M * Real.exp (Real.pi/2) / (cj * δz ^ (if d = 8 then 1 else 2)) := by
          field_simp
          ring
  rcases hnear with hmid | hrest
  · have hg : (((imagAxis t⁻¹ (inv_pos.mpr ht)) : ℍ) : ℂ) = (t:ℂ)⁻¹ * Complex.I := by
      simp only [Work.Kernels.imagAxis, Complex.ofReal_inv]
    rw [Kaxis, dif_pos ht]
    refine key (imagAxis t⁻¹ (inv_pos.mpr ht)) ?_ ?_ ?_ ?_ ?_ ?_
    · simp [Work.Kernels.imagAxis]
    · simp [Work.Kernels.imagAxis]
    · rw [← S_imagAxis t ht, KernelFacts.jInvariantFun_S_smul]
    · rw [← S_imagAxis t ht]; exact KL.KfunClear_S_self ℓ d hd (imagAxis t ht)
    · rw [hg]; exact hmid
    · rw [hg]; exact (hJ t ht ht1 τ hD h2).1 hmid
  · rcases hrest with hp1 | hm1
    · have hg : ((((1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) : ℂ)
          = (1:ℂ) + ((t:ℂ)⁻¹ * Complex.I) := by
        rw [UpperHalfPlane.coe_vadd]
        have h2' : (((imagAxis t⁻¹ (inv_pos.mpr ht)) : ℍ) : ℂ) = (t:ℂ)⁻¹ * Complex.I := by
          simp only [Work.Kernels.imagAxis, Complex.ofReal_inv]
        rw [h2']; norm_num
      rw [Kaxis, dif_pos ht]
      refine key (((1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) ?_ ?_ ?_ ?_ ?_ ?_
      · rw [im_vadd']; simp [Work.Kernels.imagAxis]
      · rw [re_vadd']; simp [Work.Kernels.imagAxis]
      · rw [KernelFacts.jInvariantFun_vadd_one, ← S_imagAxis t ht, KernelFacts.jInvariantFun_S_smul]
      · rw [← S_imagAxis t ht]; exact KfunClear_TS_zero ℓ d hd (imagAxis t ht)
      · rw [hg]; exact hp1
      · rw [hg]; exact (hJ t ht ht1 τ hD h2).2.1 hp1
    · have hg : ((((-1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) : ℂ)
          = (-1:ℂ) + ((t:ℂ)⁻¹ * Complex.I) := by
        rw [UpperHalfPlane.coe_vadd]
        have h2' : (((imagAxis t⁻¹ (inv_pos.mpr ht)) : ℍ) : ℂ) = (t:ℂ)⁻¹ * Complex.I := by
          simp only [Work.Kernels.imagAxis, Complex.ofReal_inv]
        rw [h2']; norm_num
      rw [Kaxis, dif_pos ht]
      refine key (((-1:ℝ) +ᵥ imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ)) ?_ ?_ ?_ ?_ ?_ ?_
      · rw [im_vadd']; simp [Work.Kernels.imagAxis]
      · rw [re_vadd']; simp [Work.Kernels.imagAxis]
      · rw [jInvariantFun_vadd_neg_one, ← S_imagAxis t ht, KernelFacts.jInvariantFun_S_smul]
      · rw [← S_imagAxis t ht]; exact KfunClear_TinvS_zero ℓ d hd (imagAxis t ht)
      · rw [hg]; exact hm1
      · rw [hg]; exact (hJ t ht ht1 τ hD h2).2.2 hm1

/-! ## The target theorem -/

/-! ## Combining the three regimes -/

/-- If `c ≤ c'` then `exp (-(c'/t)) ≤ exp (-(c/t))` for `t > 0`. -/
lemma exp_neg_div_le_of_le {c c' t : ℝ} (h : c ≤ c') (ht : 0 < t) :
    Real.exp (-(c' / t)) ≤ Real.exp (-(c / t)) := by
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact div_le_div_of_nonneg_right h ht.le

/-- `(1 + 1/t) ^ ·` is monotone when `t > 0`. -/
lemma one_add_one_div_rpow_le {t : ℝ} (ht : 0 < t) {m m' : ℝ} (h : m ≤ m') :
    (1 + 1 / t) ^ m ≤ (1 + 1 / t) ^ m' := by
  apply Real.rpow_le_rpow_of_exponent_le _ h
  have hh : (0:ℝ) < 1 / t := one_div_pos.mpr ht
  linarith

/-! ## The target theorem -/

theorem funnelFlat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C c m : ℝ, 0 < C ∧ 0 < c ∧ 0 ≤ m ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → t ≤ 1 →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          ≤ C * (1 + 1 / t) ^ m * Real.exp (-(c / t)) := by
  obtain ⟨Cf, cf, mf, hCf, hcf, hmf, hfar⟩ := Work.Asymptotics.FunnelFar ℓ d hd
  obtain ⟨CA, mA, hCA, hmA, hnearA⟩ := nearA ℓ d hd
  obtain ⟨CM, hCM, hnearM⟩ := nearMid ℓ d hd
  set Cc : ℝ := max (max Cf CA) (CM * Real.exp (min cf Real.pi * (5/2))) with hCc
  set cc : ℝ := min cf Real.pi with hcc
  set mm : ℝ := max mf mA with hmm
  have hCcpos : 0 < Cc := by
    rw [hCc]
    exact lt_of_lt_of_le hCf (le_trans (le_max_left Cf CA) (le_max_left _ _))
  have hccpos : 0 < cc := by rw [hcc]; exact lt_min hcf Real.pi_pos
  have hmmnn : 0 ≤ mm := by rw [hmm]; exact le_trans hmf (le_max_left mf mA)
  have hCf_le : Cf ≤ Cc := by
    rw [hCc]; exact le_trans (le_max_left Cf CA) (le_max_left _ _)
  have hCA_le : CA ≤ Cc := by
    rw [hCc]; exact le_trans (le_max_right Cf CA) (le_max_left _ _)
  have hCM_le : CM * Real.exp (cc * (5/2)) ≤ Cc := by
    rw [hCc, hcc]; exact le_max_right _ _
  have hcf_le : cc ≤ cf := by rw [hcc]; exact min_le_left cf Real.pi
  have hpi_le : cc ≤ Real.pi := by rw [hcc]; exact min_le_right cf Real.pi
  have hmf_le : mf ≤ mm := by rw [hmm]; exact le_max_left mf mA
  have hmA_le : mA ≤ mm := by rw [hmm]; exact le_max_right mf mA
  refine ⟨Cc, cc, mm, hCcpos, hccpos, hmmnn, ?_⟩
  intro τ t ht hD h2 ht1 hne
  by_cases hnear : (‖(τ : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ < 1/4 ∨
      ‖(τ : ℂ) - ((1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ < 1/4 ∨
      ‖(τ : ℂ) - ((-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ < 1/4)
  · by_cases htA : t ≤ 2/5
    · have hn := hnearA t ht htA τ hD h2 hne hnear
      refine hn.trans ?_
      have h1 : (1 + 1/t) ^ mA ≤ (1 + 1/t) ^ mm := one_add_one_div_rpow_le ht hmA_le
      have h2' : Real.exp (-(Real.pi/t)) ≤ Real.exp (-(cc/t)) := exp_neg_div_le_of_le hpi_le ht
      have h4 : (0:ℝ) ≤ (1 + 1/t) ^ mA := Real.rpow_nonneg (by positivity) mA
      have h5 : (0:ℝ) ≤ Real.exp (-(Real.pi/t)) := (Real.exp_pos _).le
      have h6 : (0:ℝ) ≤ (1 + 1/t) ^ mm := Real.rpow_nonneg (by positivity) mm
      have h7 : (0:ℝ) ≤ Real.exp (-(cc/t)) := (Real.exp_pos _).le
      calc CA * (1 + 1/t) ^ mA * Real.exp (-(Real.pi/t))
          = CA * ((1 + 1/t) ^ mA * Real.exp (-(Real.pi/t))) := by ring
        _ ≤ Cc * ((1 + 1/t) ^ mm * Real.exp (-(cc/t))) :=
            mul_le_mul hCA_le (mul_le_mul h1 h2' h5 h6) (mul_nonneg h4 h5) hCcpos.le
        _ = Cc * (1 + 1/t) ^ mm * Real.exp (-(cc/t)) := by ring
    · have htA' : 2/5 < t := not_le.mp htA
      have hn := hnearM t ht htA' ht1 τ hD h2 hne hnear
      refine hn.trans ?_
      have hstep1 : CM ≤ CM * Real.exp (cc * (5/2)) * Real.exp (-(cc/t)) := by
        have hone : (1:ℝ) ≤ Real.exp (cc * (5/2)) * Real.exp (-(cc/t)) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          have hle : cc / t ≤ cc * (5/2) := by
            rw [div_le_iff₀ ht]
            have hmul : cc * (2/5) ≤ cc * t := mul_le_mul_of_nonneg_left (le_of_lt htA') hccpos.le
            nlinarith [hmul]
          linarith
        calc CM = CM * 1 := by ring
          _ ≤ CM * (Real.exp (cc * (5/2)) * Real.exp (-(cc/t))) :=
              mul_le_mul_of_nonneg_left hone hCM.le
          _ = CM * Real.exp (cc * (5/2)) * Real.exp (-(cc/t)) := by ring
      have hstep2 : CM * Real.exp (cc * (5/2)) * Real.exp (-(cc/t))
          ≤ Cc * Real.exp (-(cc/t)) :=
        mul_le_mul_of_nonneg_right hCM_le (Real.exp_pos _).le
      have hstep3 : Cc * Real.exp (-(cc/t)) ≤ Cc * (1 + 1/t) ^ mm * Real.exp (-(cc/t)) := by
        have hone : (1:ℝ) ≤ (1 + 1/t) ^ mm := by
          apply Real.one_le_rpow
          · have hh : (0:ℝ) < 1 / t := one_div_pos.mpr ht
            linarith
          · exact hmmnn
        calc Cc * Real.exp (-(cc/t)) = Cc * (1 * Real.exp (-(cc/t))) := by ring
          _ ≤ Cc * ((1 + 1/t) ^ mm * Real.exp (-(cc/t))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hone (Real.exp_pos _).le) hCcpos.le
          _ = Cc * (1 + 1/t) ^ mm * Real.exp (-(cc/t)) := by ring
      exact le_trans hstep1 (le_trans hstep2 hstep3)
  · have h1' : 1/4 ≤ ‖(τ : ℂ) - ((t : ℂ)⁻¹ * Complex.I)‖ :=
      not_lt.mp (fun h => hnear (Or.inl h))
    have h2'' : 1/4 ≤ ‖(τ : ℂ) - ((1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ :=
      not_lt.mp (fun h => hnear (Or.inr (Or.inl h)))
    have h3'' : 1/4 ≤ ‖(τ : ℂ) - ((-1 : ℂ) + (t : ℂ)⁻¹ * Complex.I)‖ :=
      not_lt.mp (fun h => hnear (Or.inr (Or.inr h)))
    have hnf : 1/4 ≤ ‖(τ : ℂ) - ((t⁻¹ : ℝ) : ℂ) * Complex.I‖ ∧
        1/4 ≤ ‖(τ : ℂ) - ((1 : ℂ) + ((t⁻¹ : ℝ) : ℂ) * Complex.I)‖ ∧
        1/4 ≤ ‖(τ : ℂ) - ((-1 : ℂ) + ((t⁻¹ : ℝ) : ℂ) * Complex.I)‖ := by
      refine ⟨?_, ?_, ?_⟩
      · simpa only [Complex.ofReal_inv] using h1'
      · simpa only [Complex.ofReal_inv] using h2''
      · simpa only [Complex.ofReal_inv] using h3''
    have hf := hfar τ t ht hD h2 ht1 hnf hne
    refine hf.trans ?_
    have h1 : (1 + 1/t) ^ mf ≤ (1 + 1/t) ^ mm := one_add_one_div_rpow_le ht hmf_le
    have h2' : Real.exp (-(cf/t)) ≤ Real.exp (-(cc/t)) := exp_neg_div_le_of_le hcf_le ht
    have h4 : (0:ℝ) ≤ (1 + 1/t) ^ mf := Real.rpow_nonneg (by positivity) mf
    have h5 : (0:ℝ) ≤ Real.exp (-(cf/t)) := (Real.exp_pos _).le
    have h6 : (0:ℝ) ≤ (1 + 1/t) ^ mm := Real.rpow_nonneg (by positivity) mm
    have h7 : (0:ℝ) ≤ Real.exp (-(cc/t)) := (Real.exp_pos _).le
    calc Cf * (1 + 1/t) ^ mf * Real.exp (-(cf/t))
        = Cf * ((1 + 1/t) ^ mf * Real.exp (-(cf/t))) := by ring
      _ ≤ Cc * ((1 + 1/t) ^ mm * Real.exp (-(cc/t))) :=
          mul_le_mul hCf_le (mul_le_mul h1 h2' h5 h6) (mul_nonneg h4 h5) hCcpos.le
      _ = Cc * (1 + 1/t) ^ mm * Real.exp (-(cc/t)) := by ring

end
end Work.Asymptotics.HalfFunnel
