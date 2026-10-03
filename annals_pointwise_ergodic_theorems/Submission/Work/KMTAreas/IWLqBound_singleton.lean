import Mathlib
import Submission.Work.KMTAreas.iw_family
import Submission.Port.Aesm

/-!
# Translating the frequency set of an Ionescu–Wainger multiplier

`Work.Analysis.IWMultiplier.IWLqBound A Φ q C` asserts that the Ionescu–Wainger multiplier with
symbol `iwSymbolSet A Φ`, i.e. the convolution with the Fourier coefficients of
`ξ ↦ ∑_{α ∈ A} Φ (ξ - α)`, is bounded on `ℓ^q(ℤ; H)` with constant `C`, uniformly over all finite
dimensional Hilbert spaces `H`.

The frequency set `A` enters only through *translations of the symbol*: shifting `A` by `α`
replaces `Φ` by `Φ (· - α)`.  On the Fourier side that is a modulation of the sequence, which is a
pointwise multiplication by a character of modulus one, hence an isometry of every `ℓ^q`.  This
file formalises that observation for a singleton frequency set and draws the consequence that
`IWLqBound {α} Φ q C` holds as soon as `IWLqBound {0} Φ q C` does, with the *same* constant:

* `iwKernel_translate` — the Fourier coefficients of the translated symbol `Φ (· - α)` are the
  Fourier coefficients of `Φ` modulated by the character `fourier (-j) α`;
* `iwConv_singleton_shift` — the multiplier with frequency set `{α}` is the multiplier with
  frequency set `{0}` conjugated by the modulation `f m = fourier m α • f m`;
* `IWLqBound_shift_singleton` — the `ℓ^q` bound for `{0}` transfers to `{α}`;

and finally the requested `IWLqBound_singleton`.

The proof is elementary: the convolution sums are finite (the sequences tested are finitely
supported), so the only harmonic analysis needed is the translation invariance of the Haar measure
on the circle, which gives the translate rule for Fourier coefficients.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace Work.KMTAreas

open Work.Analysis.IWMultiplier (iwKernel iwConv iwConv_apply IWLqBound)
open Work.Analysis.IonescuWainger (iwSymbolSet circleMeasure)

/-- The exponential monomials are additive in the point: `e_n(x + y) = e_n(x) e_n(y)`. -/
lemma fourier_add_apply_circle (n : ℤ) (x y : Work.Analysis.IonescuWainger.Circle) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, _root_.Circle.coe_mul]

/-- Every exponential monomial has modulus one. -/
lemma norm_fourier_circle (n : ℤ) (x : Work.Analysis.IonescuWainger.Circle) :
    ‖fourier n x‖ = 1 := by
  rw [fourier_apply]
  exact _root_.Circle.norm_coe _

lemma fourier_circle_ne_zero (n : ℤ) (x : Work.Analysis.IonescuWainger.Circle) :
    fourier n x ≠ 0 := by
  intro h
  have h1 := norm_fourier_circle n x
  rw [h] at h1
  norm_num at h1

/-- The `enorm` of a point of the circle: `‖e_n(x)‖ₑ = 1`. -/
lemma enorm_fourier_circle (n : ℤ) (x : Work.Analysis.IonescuWainger.Circle) :
    ‖fourier n x‖ₑ = 1 := by
  rw [enorm_eq_nnnorm]
  exact_mod_cast (show ‖fourier n x‖₊ = 1 from
    Subtype.ext (by simpa using norm_fourier_circle n x))

/-- **Fourier coefficients of a translated symbol.**  Translating the symbol by `α` on the circle
modulates its Fourier coefficients by the character `j ↦ fourier (-j) α`. -/
lemma iwKernel_translate (Φ : Work.Analysis.IonescuWainger.Circle → ℂ)
    (α : Work.Analysis.IonescuWainger.Circle) (j : ℤ) :
    iwKernel (fun ξ : Work.Analysis.IonescuWainger.Circle => Φ (ξ - α)) j
      = fourier (-j) α * iwKernel Φ j := by
  rw [iwKernel, iwKernel, fourierCoeff, fourierCoeff]
  simp only [smul_eq_mul]
  have h1 : (∫ ξ : Work.Analysis.IonescuWainger.Circle,
        fourier (-j) ξ * Φ (ξ - α) ∂circleMeasure)
      = ∫ u : Work.Analysis.IonescuWainger.Circle,
          fourier (-j) (u + α) * Φ u ∂circleMeasure := by
    rw [← integral_add_right_eq_self
      (fun ξ : Work.Analysis.IonescuWainger.Circle => fourier (-j) ξ * Φ (ξ - α)) α]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
      simp only [add_sub_cancel_right])
  rw [h1, show (∫ u : Work.Analysis.IonescuWainger.Circle,
        fourier (-j) (u + α) * Φ u ∂circleMeasure)
      = ∫ u : Work.Analysis.IonescuWainger.Circle,
          fourier (-j) α * (fourier (-j) u * Φ u) ∂circleMeasure from
      integral_congr_ae (Filter.Eventually.of_forall fun u => by
        show fourier (-j) (u + α) * Φ u = fourier (-j) α * (fourier (-j) u * Φ u)
        rw [fourier_add_apply_circle]; ring)]
  rw [integral_const_mul]

/-- The IW symbol of a singleton frequency set is the translated symbol. -/
lemma iwSymbolSet_singleton_eq (α : Work.Analysis.IonescuWainger.Circle)
    (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) :
    iwSymbolSet {α} Φ = fun ξ => Φ (ξ - α) := by
  funext ξ
  simp [iwSymbolSet]

/-- The IW symbol of the zero frequency set is the symbol itself. -/
lemma iwSymbolSet_singleton_zero (Φ : Work.Analysis.IonescuWainger.Circle → ℂ) :
    iwSymbolSet {0} Φ = Φ := by
  funext ξ
  simp [iwSymbolSet]

/-- A convolution sum against a finitely supported sequence is a finite sum over any finite set
containing the support. -/
lemma tsum_conv_eq_finset_sum {H : Type*} [AddCommMonoid H] [TopologicalSpace H] [Module ℂ H]
    (K : ℤ → ℂ) (f : ℤ → H) (s : Finset ℤ) (hs : ∀ k, f k ≠ 0 → k ∈ s) (n : ℤ) :
    (∑' j : ℤ, K j • f (n - j)) = ∑ k ∈ s, K (n - k) • f k := by
  rw [tsum_eq_sum (L := SummationFilter.unconditional ℤ)
    (s := s.image (fun k => n - k)) ?_]
  · rw [Finset.sum_image (sub_right_injective (b := n)).injOn]
    exact Finset.sum_congr rfl fun k _ => by
      rw [show n - (n - k) = k by ring]
  · intro j hj
    have hz : f (n - j) = 0 := by
      by_contra hne
      exact hj (Finset.mem_image.mpr ⟨n - j, hs _ hne, by ring⟩)
    rw [hz, smul_zero]

/-- **The singleton IW multiplier is the zero-frequency one conjugated by a modulation.**
For a finitely supported `f`, the IW multiplier with frequency set `{α}` equals the modulation
`m ↦ fourier m α • f m`, followed by the multiplier with frequency set `{0}`, followed by the
inverse modulation. -/
lemma iwConv_singleton_shift {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Φ : Work.Analysis.IonescuWainger.Circle → ℂ)
    (α : Work.Analysis.IonescuWainger.Circle) (f : ℤ → H) (s : Finset ℤ)
    (hs : ∀ k, f k ≠ 0 → k ∈ s) (n : ℤ) :
    iwConv {α} Φ f n
      = (fourier n α)⁻¹ • iwConv {0} Φ (fun m => fourier m α • f m) n := by
  rw [iwConv_apply, iwConv_apply]
  rw [tsum_conv_eq_finset_sum (iwKernel (iwSymbolSet {α} Φ)) f s hs n,
    tsum_conv_eq_finset_sum (iwKernel (iwSymbolSet {0} Φ)) (fun m => fourier m α • f m) s
      (fun k hk => hs k (fun h => hk (by simp [h]))) n]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iwSymbolSet_singleton_eq, iwSymbolSet_singleton_zero, iwKernel_translate]
  rw [← mul_smul, ← mul_smul]
  congr 1
  have hzu : fourier n α * fourier (-(n - k)) α = fourier k α := by
    have h := fourier_add (T := 1) (m := n) (n := -(n - k)) (x := α)
    rw [show n + -(n - k) = k by ring] at h
    exact h.symm
  have hz : fourier n α ≠ 0 := fourier_circle_ne_zero n α
  rw [hzu.symm]
  field_simp

/-- **The `ℓ^q` Ionescu–Wainger bound transfers to a translated singleton frequency set**, with
the same constant: the multiplier with frequency set `{α}` is the multiplier with frequency set
`{0}` conjugated by the modulation `f ↦ (m ↦ fourier m α • f m)`, which is an isometry of every
`ℓ^q`. -/
theorem IWLqBound_shift_singleton {α : Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} {q : ENNReal} {C : NNReal}
    (h : IWLqBound {0} Φ q C) : IWLqBound {α} Φ q C := by
  intro H _ _ _ f hf
  have hfs : (Function.support (fun m : ℤ => fourier m α • f m)).Finite :=
    hf.subset fun m hm => by
      rw [Function.mem_support] at hm ⊢
      intro hf0
      exact hm (by simp [hf0])
  have hmod : eLpNorm (fun m : ℤ => fourier m α • f m) q Measure.count
      = eLpNorm f q Measure.count := by
    refine eLpNorm_congr_enorm_ae (hf := by pw_aesm) (hg := by pw_aesm) (Filter.Eventually.of_forall fun m => ?_)
    rw [enorm_smul, enorm_fourier_circle, one_mul]
  have hconj : eLpNorm (iwConv {α} Φ f) q Measure.count
      = eLpNorm (iwConv {0} Φ (fun m : ℤ => fourier m α • f m)) q Measure.count := by
    refine eLpNorm_congr_enorm_ae (hf := by pw_aesm) (hg := by pw_aesm) (Filter.Eventually.of_forall fun n => ?_)
    rw [iwConv_singleton_shift Φ α f hf.toFinset (fun k hk => hf.mem_toFinset.mpr hk) n,
      enorm_smul]
    have hone : ‖(fourier n α)⁻¹‖ₑ = 1 := by
      rw [enorm_inv (fourier_circle_ne_zero n α), enorm_fourier_circle, inv_one]
    rw [hone, one_mul]
  calc eLpNorm (iwConv {α} Φ f) q Measure.count
      = eLpNorm (iwConv {0} Φ (fun m : ℤ => fourier m α • f m)) q Measure.count := hconj
    _ ≤ ENNReal.ofReal (C : ℝ) * eLpNorm (fun m : ℤ => fourier m α • f m) q Measure.count :=
        h H (fun m : ℤ => fourier m α • f m) hfs
    _ = ENNReal.ofReal (C : ℝ) * eLpNorm f q Measure.count := by rw [hmod]

theorem IWLqBound_singleton {α : Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} {q : ENNReal}
    {C : NNReal} (h : Work.Analysis.IWMultiplier.IWLqBound {0} Φ q C) :
    ∃ C' : NNReal, 0 < C' ∧ Work.Analysis.IWMultiplier.IWLqBound {α} Φ q C' :=
  ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    (IWLqBound_shift_singleton h).mono (le_max_left _ _)⟩

end Work.KMTAreas
