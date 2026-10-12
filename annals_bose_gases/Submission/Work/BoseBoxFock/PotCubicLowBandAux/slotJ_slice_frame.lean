import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotBesselDefs
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.slotJ_slice_frame` — the frame identity at a slice

The `j`-th slot `slotJ e T j Θ` of the first-quantised sum of a one-body operator `T` acts only on
the `j`-th coordinate of a configuration: at `x = sliceRestore j a ŷ` (the configuration with `a`
in the slot `j` and the remaining coordinates frozen to `ŷ`) it is a *one-particle* expression in
`a`.  For `T = Σ_k |f_k⟩⟨f_k|` (a finite sum of rank-one operators with real coefficient vectors
`f k : Fin m → ℝ`) the slot factorises, and the resulting integral over the slot coordinate is the
**frame identity**

    ∫ a, Re( conj(Θ (σ_j(a,ŷ))) · (slotJ e (Σ_k |f_k⟩⟨f_k|) j Θ) (σ_j(a,ŷ)) )
      = Σ_k ‖ Σ_l (f k l) · ∫ z, conj(e_l z) · Θ(σ_j(z,ŷ)) ‖² .

The point is that the right-hand side is a sum of *squares of one-body amplitudes* `B_k`, and the
left-hand side is the (real part of the) corresponding integral: writing `A_k(a) = Σ_l (f k l)e_l(a)`
and `B_k = Σ_l (f k l) C_l` with `C_l = ∫ conj(e_l z)Θ(σ_j(z,ŷ))`, the pointwise slot identity is

    (slotJ e (Σ_k |f_k⟩⟨f_k|) j Θ)(σ_j(a,ŷ)) = Σ_k A_k(a) · B_k ,

and the conjugation identity `∫ a, e_l(a) conj(Θ(σ_j(a,ŷ))) = conj(C_l)` turns the integral of the
left-hand side into `Σ_k B_k · conj(B_k) = Σ_k ‖B_k‖²`.

Everything here is `sorry`-free; the auxiliary lemmas
(`measurable_sliceRestore`, `integrable_e_mul_starTheta_slice`, `integrable_starE_mul_Theta_slice`,
`integral_e_mul_starTheta_slice`, `integral_eta_mul_starTheta_slice`) are stated for general data
and are reusable by the sibling target `slotJ_slice_excited`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.PotCubicLowBandAux

set_option autoImplicit false

/-- The slice map `a ↦ sliceRestore j a ŷ` is measurable (it is the `j`-th coordinate itself with
all the others constant). -/
theorem measurable_sliceRestore {n : ℕ} (j : Fin n)
    (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp) :
    Measurable (fun a : Work.BoseDict.Sp => sliceRestore j a ŷ) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  by_cases h : i = j
  · subst h
    simpa [sliceRestore] using measurable_id'
  · simp [sliceRestore, h]

/-- The corpus box has finite volume. -/
theorem volume_boxL_ne_top (ℓ : ℝ) :
    (volume : Measure (Work.BoseDict.Sp)) (Work.BoseK15.corpusBox.boxL ℓ) ≠ ⊤ :=
  (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top.ne

/-- A measurable function which is everywhere bounded and vanishes outside the corpus box is
integrable. -/
theorem integrable_of_bdd_of_boxL {ℓ : ℝ} {g : Work.BoseDict.Sp → ℂ}
    (hgm : AEStronglyMeasurable g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (hsupp : ∀ x, x ∉ Work.BoseK15.corpusBox.boxL ℓ → g x = 0) :
    Integrable g :=
  Work.MB.integrable_of_bdd_of_support
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)
    (volume_boxL_ne_top ℓ) hgm hC hsupp

/-- Integrability of `a ↦ e_l(a) · conj(Θ(σ_j(a,ŷ)))`. -/
theorem integrable_e_mul_starTheta_slice {m n : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (j : Fin n) {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp) (l : Fin m) :
    Integrable (fun a : Work.BoseDict.Sp => e l a * star (Θ (sliceRestore j a ŷ))) := by
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  obtain ⟨Ce, hCe⟩ := hbdd l
  refine integrable_of_bdd_of_boxL (ℓ := ℓ) (C := max Ce 0 * max CΘ 0) ?_ ?_ ?_
  · exact ((hmeas l).mul (continuous_star.measurable.comp
      (hΘm.comp (measurable_sliceRestore j ŷ)))).aestronglyMeasurable
  · intro a
    calc ‖e l a * star (Θ (sliceRestore j a ŷ))‖ = ‖e l a‖ * ‖Θ (sliceRestore j a ŷ)‖ := by
          rw [norm_mul, norm_star]
      _ ≤ max Ce 0 * max CΘ 0 := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (le_max_right _ _)
          · exact (hCe a).trans (le_max_left _ _)
          · exact (hCΘ _).trans (le_max_left _ _)
  · intro a ha
    have h0 : e l a = 0 := by
      by_contra h
      exact ha (hsupp l h)
    simp [h0]

/-- Integrability of `a ↦ conj(e_l(a)) · Θ(σ_j(a,ŷ))`. -/
theorem integrable_starE_mul_Theta_slice {m n : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (j : Fin n) {Θ : Work.BoseDict.Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp) (l : Fin m) :
    Integrable (fun a : Work.BoseDict.Sp => star (e l a) * Θ (sliceRestore j a ŷ)) := by
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  obtain ⟨Ce, hCe⟩ := hbdd l
  refine integrable_of_bdd_of_boxL (ℓ := ℓ) (C := max Ce 0 * max CΘ 0) ?_ ?_ ?_
  · exact (((continuous_star.measurable.comp (hmeas l)).mul
      (hΘm.comp (measurable_sliceRestore j ŷ)))).aestronglyMeasurable
  · intro a
    calc ‖star (e l a) * Θ (sliceRestore j a ŷ)‖ = ‖e l a‖ * ‖Θ (sliceRestore j a ŷ)‖ := by
          rw [norm_mul, norm_star]
      _ ≤ max Ce 0 * max CΘ 0 := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (le_max_right _ _)
          · exact (hCe a).trans (le_max_left _ _)
          · exact (hCΘ _).trans (le_max_left _ _)
  · intro a ha
    have h0 : e l a = 0 := by
      by_contra h
      exact ha (hsupp l h)
    simp [h0]

/-- The conjugation identity `∫ e_l · conj(Θ∘σ) = conj(∫ conj(e_l) · (Θ∘σ))`, which is what turns
the slot integral into a square of the one-body amplitude `∫ conj(e_l) · (Θ∘σ)`.  No hypotheses are
needed (the Bochner integral is total). -/
theorem integral_e_mul_starTheta_slice {m n : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (j : Fin n) {Θ : Work.BoseDict.Xn n → ℂ}
    (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp) (l : Fin m) :
    ∫ a : Work.BoseDict.Sp, e l a * star (Θ (sliceRestore j a ŷ))
      = star (∫ a : Work.BoseDict.Sp, star (e l a) * Θ (sliceRestore j a ŷ)) := by
  rw [Complex.star_def]
  rw [← integral_conj (μ := (volume : Measure (Work.BoseDict.Sp)))
      (f := fun a : Work.BoseDict.Sp => (starRingEnd ℂ) (e l a) * Θ (sliceRestore j a ŷ))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  simp only [map_mul, starRingEnd_apply, star_star]

/-- The one-mode integral: `∫ (Σ_l c_l e_l) · conj(Θ∘σ) = conj(Σ_l c_l ∫ conj(e_l) · (Θ∘σ))` for
**real** coefficients `c`. -/
theorem integral_eta_mul_starTheta_slice {m n : ℕ} (c : Fin m → ℝ) (j : Fin n)
    {e : Fin m → Work.BoseDict.Sp → ℂ} {Θ : Work.BoseDict.Xn n → ℂ}
    (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp)
    (hint : ∀ l, Integrable (fun a : Work.BoseDict.Sp =>
        e l a * star (Θ (sliceRestore j a ŷ)))) :
    ∫ a : Work.BoseDict.Sp, (∑ l : Fin m, (((c l : ℝ) : ℂ)) * e l a)
        * star (Θ (sliceRestore j a ŷ))
      = star (∑ l : Fin m, (((c l : ℝ) : ℂ))
          * ∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ)) := by
  have hsplit : (fun a : Work.BoseDict.Sp =>
        (∑ l : Fin m, (((c l : ℝ) : ℂ)) * e l a) * star (Θ (sliceRestore j a ŷ)))
      = fun a : Work.BoseDict.Sp => ∑ l : Fin m, (((c l : ℝ) : ℂ))
          * (e l a * star (Θ (sliceRestore j a ŷ))) := by
    funext a
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hsplit, integral_finsetSum _ (fun l _ => (hint l).const_mul _)]
  have hper : ∀ l : Fin m, ∫ a : Work.BoseDict.Sp, (((c l : ℝ) : ℂ))
      * (e l a * star (Θ (sliceRestore j a ŷ)))
      = (((c l : ℝ) : ℂ))
        * star (∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ)) := by
    intro l
    rw [integral_const_mul, integral_e_mul_starTheta_slice]
  rw [Finset.sum_congr rfl (fun l _ => hper l)]
  rw [star_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [star_mul]
  simp [mul_comm]

/-- **The frame identity at a slice.**  For the rank-one sum `T = Σ_k |f_k⟩⟨f_k|` and a frozen
configuration `ŷ` of the other coordinates, the real part of the slot form integrates to the sum of
the squared one-body amplitudes `Σ_l (f k l) ∫ conj(e_l) Θ(σ_j(·,ŷ))`. -/
theorem slotJ_slice_frame {m n : ℕ} {ℓ : ℝ} {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {ι : Type} [Fintype ι] (f : ι → Fin m → ℝ) (j : Fin n) {Θ : Work.BoseDict.Xn n → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (ŷ : {i : Fin n // i ≠ j} → Work.BoseDict.Sp) :
    ∫ a : Work.BoseDict.Sp, (star (Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j a ŷ))
        * (Work.BoseBoxFock.PotCubicLowBandAux.slotJ e
            (∑ k : ι, Work.BoseBoxFock.rankOnePair (f k) (f k)) j Θ
            (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j a ŷ))).re
      = ∑ k : ι, ‖∑ l : Fin m, (((f k) l : ℝ) : ℂ)
          * (∫ z : Work.BoseDict.Sp, star (e l z)
              * Θ (Work.BoseBoxFock.PotCubicLowBandAux.sliceRestore j z ŷ))‖ ^ 2 := by
  classical
  -- the two one-body quantities of the frame identity
  let A : ι → Work.BoseDict.Sp → ℂ :=
    fun k a => ∑ l : Fin m, (((f k) l : ℝ) : ℂ) * e l a
  let B : ι → ℂ := fun k => ∑ l : Fin m, (((f k) l : ℝ) : ℂ)
      * ∫ z : Work.BoseDict.Sp, star (e l z) * Θ (sliceRestore j z ŷ)
  -- (i) the pointwise slot identity: at a slice the slot of `Σ_k |f_k⟩⟨f_k|` factorises
  have hpoint : ∀ a : Work.BoseDict.Sp,
      slotJ e (∑ k : ι, rankOnePair (f k) (f k)) j Θ (sliceRestore j a ŷ)
        = ∑ k : ι, A k a * B k := by
    intro a
    dsimp only [A, B]
    rw [slotJ_finset_sum]
    simp only [Finset.sum_apply, slotJ_rankOnePair, sliceRestore_apply_self, update_sliceRestore]
  -- (ii) integrability of the one-body pieces `e_l · conj(Θ∘σ)`
  have hint : ∀ l : Fin m, Integrable (fun a : Work.BoseDict.Sp =>
      e l a * star (Θ (sliceRestore j a ŷ))) :=
    fun l => integrable_e_mul_starTheta_slice hmeas hbdd hsupp j hΘm hΘb ŷ l
  -- (iii) integrability of `a ↦ A_k(a) · conj(Θ∘σ)`
  have hIntA : ∀ k : ι, Integrable (fun a : Work.BoseDict.Sp =>
      A k a * star (Θ (sliceRestore j a ŷ))) := by
    intro k
    have hsplit : (fun a : Work.BoseDict.Sp => A k a * star (Θ (sliceRestore j a ŷ)))
        = fun a : Work.BoseDict.Sp => ∑ l : Fin m, (((f k) l : ℝ) : ℂ)
            * (e l a * star (Θ (sliceRestore j a ŷ))) := by
      funext a
      dsimp only [A]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [hsplit]
    exact integrable_finsetSum Finset.univ (fun l _ => (hint l).const_mul _)
  -- (iv) the one-body integral `∫ A_k · conj(Θ∘σ) = conj(B_k)`
  have hkey : ∀ k : ι, ∫ a : Work.BoseDict.Sp, A k a * star (Θ (sliceRestore j a ŷ))
      = star (B k) := by
    intro k
    have h := integral_eta_mul_starTheta_slice (f k) j (Θ := Θ) ŷ hint
    dsimp only [A, B] at h ⊢
    exact h
  -- (v) integrability of the whole complex integrand
  have hIntF : Integrable (fun a : Work.BoseDict.Sp =>
      star (Θ (sliceRestore j a ŷ))
        * slotJ e (∑ k : ι, rankOnePair (f k) (f k)) j Θ (sliceRestore j a ŷ)) := by
    have hsplit : (fun a : Work.BoseDict.Sp => star (Θ (sliceRestore j a ŷ))
        * slotJ e (∑ k : ι, rankOnePair (f k) (f k)) j Θ (sliceRestore j a ŷ))
        = fun a : Work.BoseDict.Sp => ∑ k : ι, B k * (A k a * star (Θ (sliceRestore j a ŷ))) := by
      funext a
      rw [hpoint a, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hsplit]
    exact integrable_finsetSum Finset.univ (fun k _ => (hIntA k).const_mul (B k))
  -- (vi) the complex identity
  have hmain : ∫ a : Work.BoseDict.Sp, star (Θ (sliceRestore j a ŷ))
      * slotJ e (∑ k : ι, rankOnePair (f k) (f k)) j Θ (sliceRestore j a ŷ)
      = ((∑ k : ι, ‖B k‖ ^ 2 : ℝ) : ℂ) := by
    have hsplit : (fun a : Work.BoseDict.Sp => star (Θ (sliceRestore j a ŷ))
        * slotJ e (∑ k : ι, rankOnePair (f k) (f k)) j Θ (sliceRestore j a ŷ))
        = fun a : Work.BoseDict.Sp => ∑ k : ι, B k * (A k a * star (Θ (sliceRestore j a ŷ))) := by
      funext a
      rw [hpoint a, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hsplit, integral_finsetSum _ (fun k _ => (hIntA k).const_mul (B k))]
    have hper : ∀ k : ι, ∫ a : Work.BoseDict.Sp, B k * (A k a * star (Θ (sliceRestore j a ŷ)))
        = B k * star (B k) := by
      intro k
      rw [integral_const_mul, hkey k]
    rw [Finset.sum_congr rfl (fun k _ => hper k)]
    have hper2 : ∀ k : ι, B k * star (B k) = ((‖B k‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [Complex.star_def, Complex.mul_conj, Complex.sq_norm]
    rw [Finset.sum_congr rfl (fun k _ => hper2 k)]
    exact (map_sum Complex.ofRealHom (fun k : ι => ‖B k‖ ^ 2) Finset.univ).symm
  -- (vii) take the real part
  simp only [← RCLike.re_to_complex]
  rw [integral_re hIntF, hmain, RCLike.re_to_complex, Complex.ofReal_re]

end Work.BoseBoxFock.PotCubicLowBandAux
