import Mathlib
import Submission.Work.Drive.ppParity.Defs

/-!
# The intrinsic weighted shift of the pair map: the collar transfers

This is the first part of the lead's **S3** (`Submission/Work/Drive/NOTES_LEAD_residency.md`): the
perturbed plane chains

> `Et τ s u = Ξ (w s • unpackFst τ) (E s u)`,  `Et' τ s u = Ξ (w s • unpackSnd τ) (E' s u)`

(the *intrinsic* `ChartPert` perturbation, replacing the chart coordinate shift `E₀ s u + w s • …` of
`Work.Drive.exists_pairDiff2_good_shift`), and the two **collar transfers**: on the open collars
`{ftS x < δ}`, `{1 - δ < ftS x}` the weight vanishes identically near the point, so the perturbed pair
map agrees with the base one *as a germ* and the base regularity `PPRegAt` transfers verbatim.

The chart is never mentioned: at a meet the two chain values coincide, so both `PPRegAt` (self-centred
charts) and the collar comparison are statements about the family alone.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The intrinsically perturbed plane chain**: the chart perturbation `Ξ` applied with the vector
`w s • v` at the family parameter `s`. -/
def ppShift (Ξ : EuclideanSpace ℝ (Fin 4) → M → M) (w : ℝ → ℝ)
    (v : EuclideanSpace ℝ (Fin 4)) (E : ℝ → EuclideanSpace ℝ (Fin 2) → M) :
    ℝ → EuclideanSpace ℝ (Fin 2) → M :=
  fun s u => Ξ (w s • v) (E s u)

/-- At a vanishing weight the perturbed chain is the base chain. -/
lemma ppShift_eq_of_eq_zero {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞ0 : ∀ p : M, Ξ 0 p = p) {w : ℝ → ℝ} {v : EuclideanSpace ℝ (Fin 4)}
    {E : ℝ → EuclideanSpace ℝ (Fin 2) → M} {s : ℝ} (hs : w s = 0) (u : EuclideanSpace ℝ (Fin 2)) :
    ppShift Ξ w v E s u = E s u := by
  rw [ppShift, hs, zero_smul]
  exact hΞ0 (E s u)

/-- The two collars of the family parameter are open. -/
lemma isOpen_ppCollars (δ : ℝ) :
    IsOpen ({y : EuclideanSpace ℝ (Fin 9) | ftS y < δ} ∪
      {y : EuclideanSpace ℝ (Fin 9) | 1 - δ < ftS y}) := by
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin 9) => y 0 := by fun_prop
  refine (isOpen_lt hcont continuous_const).union ?_
  simpa only [ftS] using isOpen_lt continuous_const hcont

/-- **The perturbed chain agrees with the base one on the open collar**, as a germ. -/
theorem ppShift_eventuallyEq_collar {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞ0 : ∀ p : M, Ξ 0 p = p) {w : ℝ → ℝ} {δ : ℝ}
    (hwleft : ∀ s : ℝ, s < δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ < s → w s = 0)
    (v : EuclideanSpace ℝ (Fin 4)) (E : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    {x : EuclideanSpace ℝ (Fin 9)} (hxc : ftS x < δ ∨ 1 - δ < ftS x) :
    (fun y : EuclideanSpace ℝ (Fin 9) => ppShift Ξ w v E (ftS y) (ftU y))
      =ᶠ[𝓝 x] (fun y : EuclideanSpace ℝ (Fin 9) => E (ftS y) (ftU y)) := by
  refine Filter.eventually_of_mem ((isOpen_ppCollars δ).mem_nhds hxc) fun y hy => ?_
  rcases hy with hy | hy
  · exact ppShift_eq_of_eq_zero hΞ0 (hwleft _ hy) (ftU y)
  · exact ppShift_eq_of_eq_zero hΞ0 (hwright _ hy) (ftU y)

lemma weight_eq_zero_of_collar {w : ℝ → ℝ} {δ : ℝ}
    (hwleft : ∀ s : ℝ, s < δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ < s → w s = 0)
    {x : EuclideanSpace ℝ (Fin 9)} (hxc : ftS x < δ ∨ 1 - δ < ftS x) :
    w (ftS x) = 0 := by
  rcases hxc with h | h
  · exact hwleft _ h
  · exact hwright _ h

/-- **The pair meet at a collar point is the base pair meet.** -/
theorem ppMeet_ppShift_iff {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞ0 : ∀ p : M, Ξ 0 p = p) {w : ℝ → ℝ} {δ : ℝ}
    (hwleft : ∀ s : ℝ, s < δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ < s → w s = 0)
    (τ : EuclideanSpace ℝ (Fin 8)) (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) {x : EuclideanSpace ℝ (Fin 9)}
    (hxc : ftS x < δ ∨ 1 - δ < ftS x) :
    ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x ↔
      ppMeet E E' V W x := by
  have hw := weight_eq_zero_of_collar hwleft hwright hxc
  have h1 : ppShift Ξ w (unpackFst τ) E (ftS x) (ftU x) = E (ftS x) (ftU x) :=
    ppShift_eq_of_eq_zero hΞ0 hw (ftU x)
  have h2 : ppShift Ξ w (unpackSnd τ) E' (ftS x) (ftU x) = E' (ftS x) (ftU x) :=
    ppShift_eq_of_eq_zero hΞ0 hw (ftU x)
  constructor
  · intro h
    have h' : x ∈ Submission.Drive.unitBox 8 ∧
        ppShift Ξ w (unpackFst τ) E (ftS x) (ftU x) = V (ftY x) ∧
        ppShift Ξ w (unpackSnd τ) E' (ftS x) (ftU x) = W (ftZ x) := h
    exact ⟨h'.1, by rw [← h1]; exact h'.2.1, by rw [← h2]; exact h'.2.2⟩
  · intro h
    have h' : x ∈ Submission.Drive.unitBox 8 ∧
        E (ftS x) (ftU x) = V (ftY x) ∧ E' (ftS x) (ftU x) = W (ftZ x) := h
    exact ⟨h'.1, by rw [h1]; exact h'.2.1, by rw [h2]; exact h'.2.2⟩

/-- **The perturbed pair map agrees with the base one on the open collar**, as a germ, in the exact
shape `PPRegAt` consumes: the *perturbed* self-centred chart pair on the left, the base charts on the
right. -/
theorem ppDiff_shift_eventuallyEq_collar {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞ0 : ∀ p : M, Ξ 0 p = p) {w : ℝ → ℝ} {δ : ℝ}
    (hwleft : ∀ s : ℝ, s < δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ < s → w s = 0)
    (τ : EuclideanSpace ℝ (Fin 8)) (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) {x : EuclideanSpace ℝ (Fin 9)}
    (hxc : ftS x < δ ∨ 1 - δ < ftS x) :
    (fun y : EuclideanSpace ℝ (Fin 9) =>
        ppDiff (ppShift Ξ w (unpackFst τ) E (ftS x) (ftU x))
          (ppShift Ξ w (unpackSnd τ) E' (ftS x) (ftU x))
          (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y)
      =ᶠ[𝓝 x]
      (fun y : EuclideanSpace ℝ (Fin 9) =>
        ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W y) := by
  have hw := weight_eq_zero_of_collar hwleft hwright hxc
  have hcent : ppShift Ξ w (unpackFst τ) E (ftS x) (ftU x) = E (ftS x) (ftU x) :=
    ppShift_eq_of_eq_zero hΞ0 hw (ftU x)
  have hcent' : ppShift Ξ w (unpackSnd τ) E' (ftS x) (ftU x) = E' (ftS x) (ftU x) :=
    ppShift_eq_of_eq_zero hΞ0 hw (ftU x)
  have h1 := ppShift_eventuallyEq_collar (Ξ := Ξ) hΞ0 hwleft hwright (unpackFst τ) E hxc
  have h2 := ppShift_eventuallyEq_collar (Ξ := Ξ) hΞ0 hwleft hwright (unpackSnd τ) E' hxc
  rw [hcent, hcent']
  filter_upwards [h1, h2] with y hy1 hy2
  simp only [ppDiff, ppShift] at hy1 hy2 ⊢
  rw [hy1, hy2]

/-- **S3, collar half: the base regularity on the two collars transfers to the perturbed family.** -/
theorem PPRegAt_ppShift_of_collar {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞ0 : ∀ p : M, Ξ 0 p = p) {w : ℝ → ℝ} {δ : ℝ}
    (hwleft : ∀ s : ℝ, s < δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ < s → w s = 0)
    (τ : EuclideanSpace ℝ (Fin 8)) (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hregBase : ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      ppMeet E E' V W x → PPRegAt E E' V W x) :
    ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x →
      PPRegAt (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x := by
  intro x hx hxc hmeet
  have hm : ppMeet E E' V W x := (ppMeet_ppShift_iff hΞ0 hwleft hwright τ E E' V W hxc).mp hmeet
  have hb := hregBase x hx hxc hm
  have hev := ppDiff_shift_eventuallyEq_collar (Ξ := Ξ) hΞ0 hwleft hwright τ E E' V W hxc
  have hE1 : fderiv ℝ (ppDiff (ppShift Ξ w (unpackFst τ) E (ftS x) (ftU x))
        (ppShift Ξ w (unpackSnd τ) E' (ftS x) (ftU x))
        (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W) x
      = fderiv ℝ (ppDiff (E (ftS x) (ftU x)) (E' (ftS x) (ftU x)) E E' V W) x := by
    simpa only [] using hev.fderiv_eq
  simp only [PPRegAt] at hb ⊢
  refine ⟨?_, ?_⟩
  · rw [hE1]
    exact hb.1
  · intro hbdry
    obtain ⟨i, hi, hint, hs⟩ := hb.2 hbdry
    exact ⟨i, hi, hint, by rw [hE1]; exact hs⟩

end

end Work.Drive
