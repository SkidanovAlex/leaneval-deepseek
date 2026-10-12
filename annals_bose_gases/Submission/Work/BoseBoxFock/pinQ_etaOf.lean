import Mathlib
import Submission.Work.BoseBoxFock.PotCubicPins
import Submission.Work.BoseBoxFock.qVec_eq_etaOf_of_pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinQ_etaOf`

The identity pinned by the `f`-rows of the honest model: if the family `e : Fin m → Ω → ℂ` is
orthonormal for the pairing (the `horth` pins), its pairings against the box vector
`qVec ℓ (kmomLab ℓ N k)` reproduce the coordinates `ℓ^{3/2}·f k l` (`hpair`), then

    `η_{f k} = Σ_l (f k l) e_l =ᵐ (√ℓ³)⁻¹·qVec ℓ (kmomLab ℓ N k) = pinQ v μ N k`.

This is the `pinQ` companion of `Work.BoseBoxFock.qVec_eq_etaOf_of_pairing`, which gives the same
identity in the other direction and with the other normalisation
(`qVec =ᵐ √ℓ³ · η_{f k}`): here the scalar `(√ℓ³)⁻¹` of `pinQ` is simply cancelled.

The one point that is not a verbatim instantiation is the `L²` membership of the modes: the
requested statement only assumes `MemLp (e l) ⊤` (essential boundedness), while
`qVec_eq_etaOf_of_pairing` builds `Lp ℂ 2` classes and hence needs `MemLp (e l) 2`.  This is
recovered from the orthonormality pin itself: `∫ star (e l)·e l = 1 ≠ 0` forces
`Integrable (fun z => star (e l z)·e l z)` (a non-integrable function has Bochner integral `0`,
`MeasureTheory.Integrable.of_integral_ne_zero`), and `‖star (e l z)·e l z‖ = ‖e l z‖²`
(`norm_mul`, `norm_star`), so `z ↦ ‖e l z‖²` is integrable, which with the a.e. strong
measurability from `MemLp (e l) ⊤` is exactly `MemLp (e l) 2`.
-/

namespace Work.BoseBoxFock

open MeasureTheory

/-- A mode that is orthonormal against itself (`∫ star (e l)·e l = 1`) is square integrable:
the nonzero value of the Bochner integral forces integrability of the pointwise product, which is
the squared modulus of `e l`. -/
theorem memLp_two_of_orth_pairing {m : ℕ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hmeas : ∀ l : Fin m,
      MeasureTheory.AEStronglyMeasurable (e l)
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (l : Fin m) :
    MeasureTheory.MemLp (e l) 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  have h1 : (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l z) ≠ 0 := by
    rw [horth l l, if_pos rfl]
    exact one_ne_zero
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l z) volume :=
    Integrable.of_integral_ne_zero h1
  have hsq : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => ‖e l z‖ ^ 2) volume :=
    hint.norm.congr (Filter.Eventually.of_forall fun z => by
      simp only [norm_mul, norm_star, pow_two])
  exact (memLp_two_iff_integrable_sq_norm (hmeas l)).2 hsq

theorem pinQ_etaOf {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (HM : Work.BoseBoxFock.HonestModes v μ) {e : Fin HM.m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hpair : ∀ (k : Work.BoseBoxFock.Lab HM.N) (l : Fin HM.m),
      (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) *
          Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N k) z)
        = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * HM.f k l : ℝ) : ℂ))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤) :
    ∀ k : Work.BoseBoxFock.Lab HM.N,
      Work.BoseDict.etaOf e (HM.f k) =ᵐ[MeasureTheory.volume]
        Work.BoseBoxFock.pinQ v μ HM.N k := by
  intro k
  -- the `qVec` identity of the companion lemma, in the form `qVec =ᵐ √ℓ³ · η_{f k}`
  have hmode := qVec_eq_etaOf_of_pairing v μ HM e horth hpair
    (fun l => memLp_two_of_orth_pairing horth (fun l => (hMemLp l).aestronglyMeasurable) l)
    (fun j => (memLp_modes (ellH v μ) (ellH_pos v μ)).1 (kmomLab (ellH v μ) HM.N j)) k
  -- the normalising scalar `√ℓ³` is nonzero (indeed positive, `ℓ = ellH v μ > 0`)
  have hsqrt_ne : (((Real.sqrt ((ellH v μ) ^ 3)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos_of_pos (pow_pos (ellH_pos v μ) 3)))
  filter_upwards [hmode] with x hx
  simp only [pinQ, Complex.ofReal_inv]
  rw [hx, inv_mul_cancel_left₀ hsqrt_ne]

end Work.BoseBoxFock
