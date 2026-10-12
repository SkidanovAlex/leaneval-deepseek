import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.convWindow_kinFT
import Submission.Work.BoseBoxFock.frame_sampling_L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The pointwise expansion of `qVec ℓ k w · conj (qVec ℓ k y)`

`qVec ℓ k = e^{i⟪k,·⟫}χ_Λ − χ̂(ℓk)·θ`, and `χ_Λ`, `θ` and `χ̂` are all real, so the
conjugate of the second factor is `e^{i⟪k,−·⟫}χ_Λ − χ̂(ℓk)·θ`.  Multiplying out and
using `e^{i⟪k,w⟫}e^{i⟪k,−y⟫} = e^{i⟪k,w−y⟫}` gives the four-term pointwise form. -/

/-- `θ_Λ` is real valued (`0` or `1`). -/
private lemma qve_conj_theta (ℓ : ℝ) (x : E3) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x) = Work.BoseK15.corpusBox.thetaFun ℓ x := by
  unfold Work.BoseB4.BoxData.thetaFun
  split <;> simp

/-- `conj (e^{i⟪k,x⟫}) = e^{i⟪k,−x⟫}`. -/
private lemma qve_conj_exp_I_inner (k x : E3) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * (inner ℝ k x : ℂ)))
      = Complex.exp (Complex.I * (inner ℝ k (-x) : ℂ)) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal, inner_neg_right]
  push_cast
  ring

/-- The two factors of `qVec` expanded. -/
private lemma qve_expand (ℓ : ℝ) (k x : E3) :
    Work.BoseK15.corpusBox.qVec ℓ k x
      = Complex.exp (Complex.I * (inner ℝ k x : ℂ)) * ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)
        - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ x := by
  rw [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply]
  rfl

/-- The conjugate of `qVec`, in the frequency `−x`. -/
private lemma qve_conj_expand (ℓ : ℝ) (k x : E3) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k x)
      = Complex.exp (Complex.I * (inner ℝ k (-x) : ℂ)) * ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)
        - ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ x := by
  rw [qve_expand, map_sub, map_mul, map_mul, qve_conj_exp_I_inner, qve_conj_theta,
    Complex.conj_ofReal, Complex.conj_ofReal]

/-- The four-term pointwise product `qVec ℓ k w · conj (qVec ℓ k y)`. -/
private lemma qve_prod (ℓ : ℝ) (k w y : E3) :
    Work.BoseK15.corpusBox.qVec ℓ k w * (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k y)
      = ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ k (w - y) : ℂ))
        - ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ y
            * ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ k w : ℂ))
        - Work.BoseK15.corpusBox.thetaFun ℓ w * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))
        + Work.BoseK15.corpusBox.thetaFun ℓ w * Work.BoseK15.corpusBox.thetaFun ℓ y
            * (((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)) ^ 2 := by
  rw [qve_expand, qve_conj_expand]
  have hphase : Complex.exp (Complex.I * (inner ℝ k (w - y) : ℂ))
      = Complex.exp (Complex.I * (inner ℝ k w : ℂ))
        * Complex.exp (Complex.I * (inner ℝ k (-y) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [inner_sub_right, inner_neg_right]
    push_cast
    ring
  have hneg : Complex.exp (Complex.I * (inner ℝ k (-y) : ℂ))
      = Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) := by
    congr 1
    rw [inner_neg_right]
    push_cast
    ring
  rw [hphase, hneg]
  ring

/-- `∑ (c₁F − c₂G − c₃H + c₄I) = c₁∑F − c₂∑G − c₃∑H + c₄∑I` over a finite set. -/
private lemma finset_sum_four {ι : Type*} (s : Finset ι) (c1 c2 c3 c4 : ℂ) (F G H I : ι → ℂ) :
    (∑ n ∈ s, (c1 * F n - c2 * G n - c3 * H n + c4 * I n))
      = c1 * (∑ n ∈ s, F n) - c2 * (∑ n ∈ s, G n)
        - c3 * (∑ n ∈ s, H n) + c4 * (∑ n ∈ s, I n) := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]

/-- The finite-sum expansion of the `qVec` kernel: with
`qVec ℓ k x = e^{i⟪k,x⟫}χ_Λ(x) − χ̂(ℓk)·θ(x)` (`χ_Λ = Submission.BoseGases.chiScale ℓ` and
`θ = Work.BoseK15.corpusBox.thetaFun ℓ` are both real, and so is
`χ̂ = Work.BoseK15.corpusBox.hatChi`), the sesquilinear kernel of a *finite* weighted family of
`qVec`s splits into the four lattice-type sums: the `χχ` term, the two `θ`-cross terms and the
`θθ` term. -/
theorem qVec_expansion_finset {ι : Type*} {ℓ : ℝ} (s : Finset ι) (ρ : ι → ℂ)
    (κ : ι → EuclideanSpace ℝ (Fin 3)) (w y : EuclideanSpace ℝ (Fin 3)) :
    (∑ n ∈ s, ρ n * (Work.BoseK15.corpusBox.qVec ℓ (κ n) w
        * (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ (κ n) y)))
      = ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
            * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
            * (∑ n ∈ s, ρ n * Complex.exp (Complex.I * ((inner ℝ (κ n) (w - y) : ℝ) : ℂ)))
        - ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun ℓ y
            * (∑ n ∈ s, ρ n * ((Work.BoseK15.corpusBox.hatChi (ℓ • κ n) : ℝ) : ℂ)
                * Complex.exp (Complex.I * ((inner ℝ (κ n) w : ℝ) : ℂ)))
        - Work.BoseK15.corpusBox.thetaFun ℓ w
            * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
            * (∑ n ∈ s, ρ n * ((Work.BoseK15.corpusBox.hatChi (ℓ • κ n) : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * ((inner ℝ (κ n) y : ℝ) : ℂ))))
        + Work.BoseK15.corpusBox.thetaFun ℓ w * Work.BoseK15.corpusBox.thetaFun ℓ y
            * (∑ n ∈ s, ρ n * (((Work.BoseK15.corpusBox.hatChi (ℓ • κ n) : ℝ) : ℂ)) ^ 2) := by
  have hsum : (∑ n ∈ s, ρ n * (Work.BoseK15.corpusBox.qVec ℓ (κ n) w
        * (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ (κ n) y)))
      = Finset.sum s (fun n : ι =>
          ((((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
              * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ))
              * (ρ n * Complex.exp (Complex.I * ((inner ℝ (κ n) (w - y) : ℝ) : ℂ))))
          - ((((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun ℓ y)
              * (ρ n * ((Work.BoseK15.corpusBox.hatChi (ℓ • κ n) : ℝ) : ℂ)
                  * Complex.exp (Complex.I * ((inner ℝ (κ n) w : ℝ) : ℂ))))
          - ((Work.BoseK15.corpusBox.thetaFun ℓ w
              * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ))
              * (ρ n * ((Work.BoseK15.corpusBox.hatChi (ℓ • κ n) : ℝ) : ℂ)
                  * Complex.exp (-(Complex.I * ((inner ℝ (κ n) y : ℝ) : ℂ)))))
          + ((Work.BoseK15.corpusBox.thetaFun ℓ w * Work.BoseK15.corpusBox.thetaFun ℓ y)
              * (ρ n * (((Work.BoseK15.corpusBox.hatChi (ℓ • κ n) : ℝ) : ℂ)) ^ 2))) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [qve_prod]
    ring
  rw [hsum, finset_sum_four s
    (((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
        * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ))
    (((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun ℓ y)
    (Work.BoseK15.corpusBox.thetaFun ℓ w
        * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ))
    (Work.BoseK15.corpusBox.thetaFun ℓ w * Work.BoseK15.corpusBox.thetaFun ℓ y)
    (fun n => ρ n * Complex.exp (Complex.I * ((inner ℝ (κ n) (w - y) : ℝ) : ℂ)))
    (fun n => ρ n * ((Work.BoseK15.corpusBox.hatChi (ℓ • κ n) : ℝ) : ℂ)
                  * Complex.exp (Complex.I * ((inner ℝ (κ n) w : ℝ) : ℂ)))
    (fun n => ρ n * ((Work.BoseK15.corpusBox.hatChi (ℓ • κ n) : ℝ) : ℂ)
                  * Complex.exp (-(Complex.I * ((inner ℝ (κ n) y : ℝ) : ℂ))))
    (fun n => ρ n * (((Work.BoseK15.corpusBox.hatChi (ℓ • κ n) : ℝ) : ℂ)) ^ 2)]

end Work.BoseBoxFock
