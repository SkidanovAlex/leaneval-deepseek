import Mathlib
import Submission.Work.FIArea5.S16.tsum_class_2d
import Submission.Work.FIArea4.WdyadPoisson
import Submission.Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow

namespace Work.FIArea5.S16

set_option maxHeartbeats 4000000

open scoped FourierTransform

noncomputable section

/-- The one-frequency phase `e(a k / q) = exp (2πi (a k)/q)`. -/
private def wph (q : ℕ) (a k : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (((a * k : ℤ) : ℂ) / (q : ℂ)))

/-- The two-frequency phase `e((a k + b l)/q)`. -/
private def wph2 (q : ℕ) (a b k l : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (((a * k + b * l : ℤ) : ℂ) / (q : ℂ)))

private lemma norm_wph (q : ℕ) (a k : ℤ) : ‖wph q a k‖ = 1 := by
  rw [wph]
  have h : 2 * Real.pi * Complex.I * (((a * k : ℤ) : ℂ) / (q : ℂ))
      = (((2 * Real.pi * ((a * k : ℤ) : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private lemma norm_wph2 (q : ℕ) (a b k l : ℤ) : ‖wph2 q a b k l‖ = 1 := by
  rw [wph2]
  have h : 2 * Real.pi * Complex.I * (((a * k + b * l : ℤ) : ℂ) / (q : ℂ))
      = (((2 * Real.pi * ((a * k + b * l : ℤ) : ℝ) / (q : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private lemma wph_mul (q : ℕ) (a b k l : ℤ) :
    wph q a k * wph q b l = wph2 q a b k l := by
  rw [wph, wph, wph2, ← Complex.exp_add]
  congr 1
  rw [← mul_add, ← add_div]
  congr 1
  push_cast; ring

private lemma summable_mul_prod {u v : ℤ → ℂ} (hu : Summable u) (hv : Summable v) :
    Summable (fun p : ℤ × ℤ => u p.1 * v p.2) := by
  refine Summable.of_norm ?_
  refine (Summable.mul_of_nonneg hu.norm hv.norm (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _)).congr (fun p => ?_)
  rw [norm_mul]

private lemma summable_wph2_mul (q : ℕ) (a b : ℤ) {u v : ℤ → ℂ}
    (hu : Summable u) (hv : Summable v) :
    Summable (fun ξ : ℤ × ℤ => wph2 q a b ξ.1 ξ.2 * (u ξ.1 * v ξ.2)) := by
  refine Summable.of_norm_bounded
    (Summable.mul_of_nonneg hu.norm hv.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
    (fun ξ => ?_)
  rw [norm_mul, norm_wph2, one_mul, norm_mul]

private lemma factor_sum (q : ℕ) (a b : ℤ) (f g : ℤ → ℂ)
    (hf : Summable f) (hg : Summable g) :
    (∑' ξ : ℤ × ℤ, wph2 q a b ξ.1 ξ.2 * (f ξ.1 * g ξ.2))
      = (∑' m : ℤ, wph q a m * f m) * (∑' n : ℤ, wph q b n * g n) := by
  have hf' : Summable (fun m : ℤ => wph q a m * f m) := by
    refine Summable.of_norm_bounded hf.norm (fun m => ?_)
    rw [norm_mul, norm_wph, one_mul]
  have hg' : Summable (fun n : ℤ => wph q b n * g n) := by
    refine Summable.of_norm_bounded hg.norm (fun n => ?_)
    rw [norm_mul, norm_wph, one_mul]
  have hfg : Summable (fun ξ : ℤ × ℤ => (wph q a ξ.1 * f ξ.1) * (wph q b ξ.2 * g ξ.2)) :=
    summable_mul_prod (u := fun m : ℤ => wph q a m * f m)
      (v := fun n : ℤ => wph q b n * g n) hf' hg'
  have hmain : (∑' m : ℤ, wph q a m * f m) * (∑' n : ℤ, wph q b n * g n)
      = ∑' ξ : ℤ × ℤ, (wph q a ξ.1 * f ξ.1) * (wph q b ξ.2 * g ξ.2) :=
    Summable.tsum_mul_tsum (f := fun m : ℤ => wph q a m * f m)
      (g := fun n : ℤ => wph q b n * g n) hf' hg' hfg
  rw [hmain]
  apply tsum_congr; intro ξ
  rw [← wph_mul]; ring

theorem poisson_periodic_2d (q : ℕ) (hq : 0 < q) (g : GaussianInt → ℂ)
    (hg : ∀ z w : GaussianInt, (((q : ℤ) : GaussianInt) ∣ (z - w)) → g z = g w)
    (f1 f2 : ℝ → ℂ) (hc1 : Continuous f1) (hc2 : Continuous f2) {b : ℝ} (hb : 1 < b)
    (h1 : f1 =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (h1' : (FourierTransform.fourier f1) =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (h2 : f2 =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b)))
    (h2' : (FourierTransform.fourier f2) =O[Filter.cocompact ℝ] (fun x : ℝ => |x| ^ (-b))) :
    (∑' z : ℤ × ℤ, g ⟨z.1, z.2⟩ * (f1 (z.1 : ℝ) * f2 (z.2 : ℝ)))
      = (1 / (q : ℂ) ^ 2) * ∑' ξ : ℤ × ℤ,
          (∑ α ∈ (Finset.range q).product (Finset.range q),
              g ⟨α.1, α.2⟩ * Complex.exp (2 * Real.pi * Complex.I *
                ((((α.1 * ξ.1 + α.2 * ξ.2 : ℤ)) : ℂ) / (q : ℂ))))
            * (FourierTransform.fourier f1 ((ξ.1 : ℝ) / q) *
                FourierTransform.fourier f2 ((ξ.2 : ℝ) / q)) := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqne : (q:ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hF1 : Summable (fun n : ℤ => f1 (n:ℝ)) := by
    simpa using Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow hb h1 (d := 1) one_pos
  have hF2 : Summable (fun n : ℤ => f2 (n:ℝ)) := by
    simpa using Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow hb h2 (d := 1) one_pos
  have hP1 : Summable (fun m : ℤ => 𝓕 f1 ((m:ℝ)/q)) :=
    Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow hb h1' hqpos
  have hP2 : Summable (fun n : ℤ => 𝓕 f2 ((n:ℝ)/q)) :=
    Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow hb h2' hqpos
  have hL := tsum_class_2d q hq g hg (fun n : ℤ => f1 (n:ℝ)) (fun n : ℤ => f2 (n:ℝ)) hF1 hF2
  -- one-dimensional residue Poisson (proved in `Work.FIArea4`)
  have hA : ∀ α : ℕ × ℕ,
      (∑' k : ℤ, f1 ((q:ℝ) * (k:ℝ) + (α.1:ℝ)))
        = (1/(q:ℂ)) * (∑' m : ℤ, wph q (α.1:ℤ) m * 𝓕 f1 ((m:ℝ)/q)) := by
    intro α
    have hpr := Work.FIArea4.poisson_residue f1 hc1 hb h1 h1' q hq (α.1:ℝ)
    have h1eq : (∑' k : ℤ, f1 ((q:ℝ) * (k:ℝ) + (α.1:ℝ)))
        = (∑' m : ℤ, f1 ((α.1:ℝ) + ((m * (q:ℤ) : ℤ) : ℝ))) := by
      apply tsum_congr; intro m; congr 1; push_cast; ring
    have h2eq : (∑' k : ℤ, 𝓕 f1 ((k:ℝ)/(q:ℝ))
          * Complex.exp (2 * Real.pi * Complex.I * (α.1:ℝ) * (k:ℝ) / (q:ℝ)))
        = (∑' m : ℤ, wph q (α.1:ℤ) m * 𝓕 f1 ((m:ℝ)/q)) := by
      apply tsum_congr; intro m
      have hw : wph q (α.1:ℤ) m
          = Complex.exp (2 * Real.pi * Complex.I * (α.1:ℝ) * (m:ℝ) / (q:ℝ)) := by
        rw [wph]; congr 1; push_cast; ring
      rw [hw]; ring
    rw [h1eq, hpr, h2eq, Complex.ofReal_natCast]
  have hB : ∀ α : ℕ × ℕ,
      (∑' l : ℤ, f2 ((q:ℝ) * (l:ℝ) + (α.2:ℝ)))
        = (1/(q:ℂ)) * (∑' n : ℤ, wph q (α.2:ℤ) n * 𝓕 f2 ((n:ℝ)/q)) := by
    intro α
    have hpr := Work.FIArea4.poisson_residue f2 hc2 hb h2 h2' q hq (α.2:ℝ)
    have h1eq : (∑' l : ℤ, f2 ((q:ℝ) * (l:ℝ) + (α.2:ℝ)))
        = (∑' n : ℤ, f2 ((α.2:ℝ) + ((n * (q:ℤ) : ℤ) : ℝ))) := by
      apply tsum_congr; intro n; congr 1; push_cast; ring
    have h2eq : (∑' l : ℤ, 𝓕 f2 ((l:ℝ)/(q:ℝ))
          * Complex.exp (2 * Real.pi * Complex.I * (α.2:ℝ) * (l:ℝ) / (q:ℝ)))
        = (∑' n : ℤ, wph q (α.2:ℤ) n * 𝓕 f2 ((n:ℝ)/q)) := by
      apply tsum_congr; intro n
      have hw : wph q (α.2:ℤ) n
          = Complex.exp (2 * Real.pi * Complex.I * (α.2:ℝ) * (n:ℝ) / (q:ℝ)) := by
        rw [wph]; congr 1; push_cast; ring
      rw [hw]; ring
    rw [h1eq, hpr, h2eq, Complex.ofReal_natCast]
  -- expansion of the right-hand side
  have hR_sum : (∑' ξ : ℤ × ℤ, (∑ α ∈ (Finset.range q).product (Finset.range q),
        g ⟨α.1, α.2⟩ * wph2 q (α.1:ℤ) (α.2:ℤ) ξ.1 ξ.2)
          * (𝓕 f1 ((ξ.1:ℝ)/q) * 𝓕 f2 ((ξ.2:ℝ)/q)))
      = ∑ α ∈ (Finset.range q).product (Finset.range q), g ⟨α.1, α.2⟩ *
          ((∑' m : ℤ, wph q (α.1:ℤ) m * 𝓕 f1 ((m:ℝ)/q))
            * (∑' n : ℤ, wph q (α.2:ℤ) n * 𝓕 f2 ((n:ℝ)/q))) := by
    rw [show (∑' ξ : ℤ × ℤ, (∑ α ∈ (Finset.range q).product (Finset.range q),
          g ⟨α.1, α.2⟩ * wph2 q (α.1:ℤ) (α.2:ℤ) ξ.1 ξ.2)
            * (𝓕 f1 ((ξ.1:ℝ)/q) * 𝓕 f2 ((ξ.2:ℝ)/q)))
        = (∑' ξ : ℤ × ℤ, ∑ α ∈ (Finset.range q).product (Finset.range q),
            g ⟨α.1, α.2⟩ * (wph2 q (α.1:ℤ) (α.2:ℤ) ξ.1 ξ.2
              * (𝓕 f1 ((ξ.1:ℝ)/q) * 𝓕 f2 ((ξ.2:ℝ)/q)))) from by
      apply tsum_congr; intro ξ
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro α _
      ring]
    rw [Summable.tsum_finsetSum (s := (Finset.range q).product (Finset.range q))
      (f := fun (α : ℕ × ℕ) (ξ : ℤ × ℤ) => g ⟨α.1, α.2⟩ *
        (wph2 q (α.1:ℤ) (α.2:ℤ) ξ.1 ξ.2 * (𝓕 f1 ((ξ.1:ℝ)/q) * 𝓕 f2 ((ξ.2:ℝ)/q))))
      (fun α _ => (summable_wph2_mul q (α.1:ℤ) (α.2:ℤ) hP1 hP2).mul_left (g ⟨α.1, α.2⟩))]
    apply Finset.sum_congr rfl; intro α _
    rw [tsum_mul_left]
    rw [factor_sum q (α.1:ℤ) (α.2:ℤ) (fun m : ℤ => 𝓕 f1 ((m:ℝ)/q))
      (fun n : ℤ => 𝓕 f2 ((n:ℝ)/q)) hP1 hP2]
  have hstep1 : (∑' z : ℤ × ℤ, g ⟨z.1, z.2⟩ * (f1 (z.1:ℝ) * f2 (z.2:ℝ)))
      = ∑ α ∈ (Finset.range q).product (Finset.range q), g ⟨α.1, α.2⟩ *
          ((∑' k : ℤ, f1 ((q:ℝ)*k + (α.1:ℝ))) * (∑' l : ℤ, f2 ((q:ℝ)*l + (α.2:ℝ)))) := by
    rw [hL]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    congr 1
    congr 1
    · exact tsum_congr (fun k => by congr 1; push_cast; ring)
    · exact tsum_congr (fun l => by congr 1; push_cast; ring)
  have hstepR0 : (1 / (q : ℂ) ^ 2) * ∑' ξ : ℤ × ℤ,
          (∑ α ∈ (Finset.range q).product (Finset.range q),
              g ⟨α.1, α.2⟩ * Complex.exp (2 * Real.pi * Complex.I *
                ((((α.1 * ξ.1 + α.2 * ξ.2 : ℤ)) : ℂ) / (q : ℂ))))
            * (FourierTransform.fourier f1 ((ξ.1 : ℝ) / q) *
                FourierTransform.fourier f2 ((ξ.2 : ℝ) / q))
      = (1 / (q : ℂ) ^ 2) * ∑' ξ : ℤ × ℤ,
          (∑ α ∈ (Finset.range q).product (Finset.range q),
              g ⟨α.1, α.2⟩ * wph2 q (α.1:ℤ) (α.2:ℤ) ξ.1 ξ.2)
            * (𝓕 f1 ((ξ.1 : ℝ) / q) * 𝓕 f2 ((ξ.2 : ℝ) / q)) := by
    simp only [wph2]
  have hstepR : (1 / (q : ℂ) ^ 2) * ∑' ξ : ℤ × ℤ,
          (∑ α ∈ (Finset.range q).product (Finset.range q),
              g ⟨α.1, α.2⟩ * wph2 q (α.1:ℤ) (α.2:ℤ) ξ.1 ξ.2)
            * (𝓕 f1 ((ξ.1 : ℝ) / q) * 𝓕 f2 ((ξ.2 : ℝ) / q))
      = ∑ α ∈ (Finset.range q).product (Finset.range q), g ⟨α.1, α.2⟩ *
          ((∑' k : ℤ, f1 ((q:ℝ)*k + (α.1:ℝ))) * (∑' l : ℤ, f2 ((q:ℝ)*l + (α.2:ℝ)))) := by
    rw [hR_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [hA α, hB α]
    field_simp
  rw [hstep1, hstepR0, hstepR]

end

end Work.FIArea5.S16
