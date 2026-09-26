import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.Sard.exists_isOpen_volume_image_restrictedCritical_null
import Submission.Work.Smooth.Morse.Flow.exists_descentRate_lower_bound
import Submission.Work.Core.torusMap_eq_iff
import Submission.Work.Smooth.BoxGeneric.AeCorner.volume_image_null_of_critical_on_bisector

/-!
# Almost every box level has transverse corners, from the regularity of the bisector

For a fixed diffeomorphism `ψ`, centre `c` and coordinate permutation `σ`, and for almost every
level `s`, the following holds: at every point `y` of the surface `F = ψ(standard torus)` at which
the level set `{boxNorm c σ · = s}` meets an *edge* of the box (two signed faces
`(i, ε)`, `(j, ε')` with `i ≠ j` are tight at `y`), if

* the two face cuts `F ∩ {faceLin i ε = s}`, `F ∩ {faceLin j ε' = s}` are regular at `y`
  (the derivative of each pulled-back face function does not vanish at a parameter over `y`), and
* the *bisector* `F ∩ {faceLin i ε = faceLin j ε'}` meets `F` transversally at `y` (the derivative
  of the pulled-back difference does not vanish),

then the corner is *transverse*: the pair of derivatives of the two pulled-back face functions at a
parameter over `y` is invertible, i.e. `CornerTransverseAt ψ c σ i j ε ε' y`.

## Proof

Write `G = pullback ψ (faceLin c σ i ε)`, `H = pullback ψ (faceLin c σ j ε')` and
`h = G - H = pullback ψ (faceLin i ε - faceLin j ε')` for the functions on the parameter plane, and
let

`B = {p | the two signed faces are tight at `param ψ p` ∧ ¬ (dG p).prod (dH p) invertible ∧
          dG p ≠ 0 ∧ dH p ≠ 0 ∧ dh p ≠ 0}`

be the set of parameters at which the hypotheses hold but the conclusion fails.  On `B` we have
`h p = 0` (both faces are tight at the same level, which is the value of the box norm), `dh p ≠ 0`
(the regularity of the bisector), and — since `B` lies in the plane, so that a non-invertible pair
of functionals is a pair of *dependent* functionals, with both functionals nonzero and the
difference nonzero —

`∃ A : ℝ, dG p = A • dh p`,

i.e. `B` is contained in the set of critical points of `G` restricted to the level curve
`{h = 0}`.  By Sard's theorem on the restricted critical set
(`Work.Smooth.BoxGeneric.Sard.exists_isOpen_volume_image_restrictedCritical_null`) the image of that
critical set under `G` is *locally* Lebesgue null; a countable (Lindelöf) subcover of `B` by those
local neighbourhoods globalises this, so `volume (G '' B) = 0`.

It remains to pass from parameters to levels.  For each of the finitely many pairs `(i, j)` of
distinct faces and each choice of signs `(ε, ε') = (±1, ±1)` the levels with a corner witness are
contained in `G '' B` (the value of the box norm at a parameter of `B` is `G` there, and the
hypotheses — including the two hypothesis parameters not chosen as the base point — are invariant
under the period lattice `2πℤ²` of the parametrisation).  A finite union of null sets is null, and
the four sign choices are indexed by `Bool`.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped Topology

namespace Work.Smooth.BoxGeneric.AeCorner

noncomputable section

/-- The sign `±1` attached to a boolean. -/
def sgSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sgSign_true : sgSign true = 1 := rfl

@[simp] theorem sgSign_false : sgSign false = -1 := rfl

theorem sgSign_eq_one_or_neg_one (b : Bool) : sgSign b = 1 ∨ sgSign b = -1 := by
  cases b <;> simp

/-- The pull-back of a difference is the difference of the pull-backs. -/
theorem pullback_sub (ψ : Submission.Diffeo) (g h : R3 → ℝ) :
    Work.Smooth.Morse.pullback ψ (fun z => g z - h z) =
      (Work.Smooth.Morse.pullback ψ g) - (Work.Smooth.Morse.pullback ψ h) := rfl

/-- **The derivative of a pull-back is invariant under the period lattice.**  Two parameters over
the same point of the surface have the same derivative. -/
theorem fderiv_pullback_eq_of_param_eq {ψ : Submission.Diffeo} {g : R3 → ℝ} {p q : ℝ × ℝ}
    (h : Work.Smooth.Morse.param ψ p = Work.Smooth.Morse.param ψ q) :
    fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p =
      fderiv ℝ (Work.Smooth.Morse.pullback ψ g) q := by
  have hper : Work.Core.torusMap p.1 p.2 = Work.Core.torusMap q.1 q.2 := by
    apply ψ.injective
    simpa only [Work.Smooth.Morse.param_def] using h
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := (Work.Core.torusMap_eq_iff p.1 p.2 q.1 q.2).mp hper
  have hpq : p = (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) :=
    Prod.ext hk hl
  rw [hpq, Work.Smooth.Morse.Flow.fderiv_pullback_add_lattice ψ g q k l]

/-- The parameters of the plane at which the two signed face cuts `(i, ε)`, `(j, ε')` are tight at
the level `boxNorm` of the corresponding surface point, the pair of derivatives of the two
pulled-back face functions is *not* invertible and all three derivatives (`i`, `j` and the
difference, i.e. the bisector) are nonzero: the parameters violating the conclusion of
`ae_transverseCorner_of_regularBisector` under its hypotheses. -/
def badParams (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3)
    (ε ε' : ℝ) : Set (ℝ × ℝ) :=
  {p | IsActiveSignedFace c σ (Submission.boxNorm c σ (Work.Smooth.Morse.param ψ p)) i ε
          (Work.Smooth.Morse.param ψ p) ∧
       IsActiveSignedFace c σ (Submission.boxNorm c σ (Work.Smooth.Morse.param ψ p)) j ε'
          (Work.Smooth.Morse.param ψ p) ∧
       ¬ ((fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) p).prod
          (fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ j ε')) p)).IsInvertible ∧
       fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) p ≠ 0 ∧
       fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ j ε')) p ≠ 0 ∧
       fderiv ℝ (Work.Smooth.Morse.pullback ψ
         (fun z => faceLin c σ i ε z - faceLin c σ j ε' z)) p ≠ 0}

/-- **A pair of functionals on the plane is either invertible or proportional.**  If `L` and `M`
are functionals on `ℝ × ℝ` whose pair `L.prod M` is not invertible, and whose difference does not
vanish, then `L` is a multiple of that difference.

Indeed `¬ (L.prod M).IsInvertible` means that the pair is not injective (the domain and the
codomain both have dimension two), so there is a nonzero vector `v` with `L v = M v = 0`; writing
`w = (v.2, -v.1)`, the pair `(v, w)` is a basis of the plane, so `L` and `L - M` — two functionals
that both vanish at `v` — are proportional, and the proportionality constant is
`L w / ((L - M) w)`, which is defined because `L - M ≠ 0` forces `(L - M) w ≠ 0`. -/
theorem exists_smul_of_not_isInvertible_prod_aux {L M : (ℝ × ℝ) →L[ℝ] ℝ}
    (hLM : L - M ≠ 0) (h : ¬ (L.prod M).IsInvertible) :
    ∃ A : ℝ, L = A • (L - M) := by
  have hker : (L.prod M).ker ≠ ⊥ := by
    intro hk
    apply h
    refine ⟨ContinuousLinearEquiv.ofBijective (L.prod M) hk ?_, rfl⟩
    rw [← LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank
      (f := ((L.prod M) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))) rfl]
    exact hk
  obtain ⟨v, hvker, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have h2 : (L v, M v) = (0 : ℝ × ℝ) := by
    rw [← ContinuousLinearMap.prod_apply]
    exact hvker
  rw [Prod.mk_eq_zero] at h2
  obtain ⟨hLv, hMv⟩ := h2
  set w : ℝ × ℝ := (v.2, -v.1) with hw
  have hvsq : v.1 ^ 2 + v.2 ^ 2 ≠ 0 := by
    intro h0
    apply hv
    have h1 : v.1 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2]
    have h2 : v.2 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2]
    exact Prod.ext h1 h2
  have hkey : ∀ z : ℝ × ℝ, (v.1 ^ 2 + v.2 ^ 2) • z =
      (z.1 * v.1 + z.2 * v.2) • v + (z.1 * v.2 - z.2 * v.1) • w := by
    intro z
    ext <;> simp only [hw, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] <;> ring
  have hLz : ∀ z : ℝ × ℝ, (v.1 ^ 2 + v.2 ^ 2) * L z = (z.1 * v.2 - z.2 * v.1) * L w := by
    intro z
    have hh := congrArg L (hkey z)
    simp only [map_smul, map_add, smul_eq_mul, hLv, mul_zero, zero_add] at hh
    exact hh
  have hDz : ∀ z : ℝ × ℝ, (v.1 ^ 2 + v.2 ^ 2) * (L - M) z =
      (z.1 * v.2 - z.2 * v.1) * (L - M) w := by
    intro z
    have hh := congrArg (L - M) (hkey z)
    simp only [map_smul, map_add, smul_eq_mul, sub_apply, hLv, hMv, sub_zero, mul_zero,
      zero_add] at hh
    exact hh
  have hDw : (L - M) w ≠ 0 := by
    intro h0
    apply hLM
    refine ContinuousLinearMap.ext fun z => ?_
    have hh := hDz z
    rw [h0, mul_zero, mul_eq_zero] at hh
    rcases hh with hh | hh
    · exact absurd hh hvsq
    · exact hh
  refine ⟨L w / ((L - M) w), ?_⟩
  refine ContinuousLinearMap.ext fun z => ?_
  rw [smul_apply]
  have h1 : L z = (z.1 * v.2 - z.2 * v.1) * L w / (v.1 ^ 2 + v.2 ^ 2) := by
    rw [eq_div_iff hvsq, mul_comm]
    exact hLz z
  have h2 : (L - M) z = (z.1 * v.2 - z.2 * v.1) * (L - M) w / (v.1 ^ 2 + v.2 ^ 2) := by
    rw [eq_div_iff hvsq, mul_comm]
    exact hDz z
  rw [h1, h2, smul_eq_mul]
  field_simp

/-- On the bad parameters the two face functions agree, the bisector function is regular, and the
derivative of the `i`-face function is parallel to that of the bisector function: the exact
hypotheses of `volume_image_null_of_critical_on_bisector`. -/
theorem volume_image_badParams_null (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i j : Fin 3) (ε ε' : ℝ) :
    MeasureTheory.volume
      ((Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) '' (badParams ψ c σ i j ε ε')) = 0 := by
  have hG : ContDiff ℝ 1 (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) :=
    (pullback_faceLin_contDiff ψ c σ i ε).of_le (by simp)
  have hH : ContDiff ℝ 1 (Work.Smooth.Morse.pullback ψ (faceLin c σ j ε')) :=
    (pullback_faceLin_contDiff ψ c σ j ε').of_le (by simp)
  have hfun : (fun p : ℝ × ℝ => Work.Smooth.Morse.pullback ψ (faceLin c σ i ε) p -
        Work.Smooth.Morse.pullback ψ (faceLin c σ j ε') p) =
      Work.Smooth.Morse.pullback ψ (fun z : R3 => faceLin c σ i ε z - faceLin c σ j ε' z) := by
    funext p
    rfl
  apply volume_image_null_of_critical_on_bisector hG hH
  · -- the two faces have the same value: the box norm
    intro q hq
    obtain ⟨ha, hb, -, -, -, -⟩ := hq
    show faceLin c σ i ε (Work.Smooth.Morse.param ψ q) =
      faceLin c σ j ε' (Work.Smooth.Morse.param ψ q)
    rw [ha.1, hb.1]
  · -- the bisector is regular
    intro q hq
    obtain ⟨-, -, -, -, -, h6⟩ := hq
    rw [hfun]
    exact h6
  · -- the derivative of the first face function is parallel to the derivative of the bisector
    intro q hq
    obtain ⟨-, -, hnotinv, h1, h2, h6⟩ := hq
    have hdGi : DifferentiableAt ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) q :=
      ((pullback_faceLin_contDiff ψ c σ i ε).differentiable (by simp)).differentiableAt
    have hdHj : DifferentiableAt ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ j ε')) q :=
      ((pullback_faceLin_contDiff ψ c σ j ε').differentiable (by simp)).differentiableAt
    have hdiff : fderiv ℝ (fun p : ℝ × ℝ => Work.Smooth.Morse.pullback ψ (faceLin c σ i ε) p -
          Work.Smooth.Morse.pullback ψ (faceLin c σ j ε') p) q =
        fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) q -
          fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ j ε')) q :=
      fderiv_sub hdGi hdHj
    have h6' : fderiv ℝ (fun p : ℝ × ℝ => Work.Smooth.Morse.pullback ψ (faceLin c σ i ε) p -
          Work.Smooth.Morse.pullback ψ (faceLin c σ j ε') p) q ≠ 0 := by
      rw [hfun]
      exact h6
    have hLM : fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) q -
          fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ j ε')) q ≠ 0 := by
      intro hz
      exact h6' (by rw [hdiff, hz])
    have hdep : ∃ A : ℝ, fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) q =
        A • (fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ i ε)) q -
             fderiv ℝ (Work.Smooth.Morse.pullback ψ (faceLin c σ j ε')) q) :=
      exists_smul_of_not_isInvertible_prod_aux hLM hnotinv
    obtain ⟨A, hA⟩ := hdep
    exact ⟨A, by rw [hdiff]; exact hA⟩

theorem ae_transverseCorner_of_regularBisector {ψ : Submission.Diffeo} (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ∀ y ∈ (Work.Smooth.Morse.torus ψ).carrier, Submission.boxNorm c σ y = s → ∀ (i j : Fin 3) (ε ε' : ℝ), i ≠ j → (ε = 1 ∨ ε = -1) → (ε' = 1 ∨ ε' = -1) → Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε y → Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s j ε' y → (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧ fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p ≠ 0) → (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧ fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε')) p ≠ 0) → (∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧ fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun z : LeanEval.KnotTheory.PardonDistortion.R3 => Work.Smooth.BoxGeneric.faceLin c σ i ε z - Work.Smooth.BoxGeneric.faceLin c σ j ε' z)) p ≠ 0) → Work.Smooth.BoxGeneric.CornerTransverseAt ψ c σ i j ε ε' y := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (t := ⋃ (i : Fin 3), ⋃ (j : Fin 3), ⋃ (b : Bool), ⋃ (b' : Bool),
      (Work.Smooth.Morse.pullback ψ (faceLin c σ i (sgSign b))) ''
        (badParams ψ c σ i j (sgSign b) (sgSign b'))) ?_ ?_
  · intro s hs
    push_neg at hs
    obtain ⟨y, hycar, hsbox, i, j, ε, ε', hij, hε, hε', hacti, hactj, h1, h2, h3, hnc⟩ := hs
    obtain ⟨b, hb⟩ : ∃ b : Bool, sgSign b = ε := by
      rcases hε with h | h
      · exact ⟨true, by simp [h]⟩
      · exact ⟨false, by simp [h]⟩
    obtain ⟨b', hb'⟩ : ∃ b' : Bool, sgSign b' = ε' := by
      rcases hε' with h | h
      · exact ⟨true, by simp [h]⟩
      · exact ⟨false, by simp [h]⟩
    obtain ⟨p₁, hp₁, hd₁⟩ := h1
    obtain ⟨p₂, hp₂, hd₂⟩ := h2
    obtain ⟨p₃, hp₃, hd₃⟩ := h3
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨j, Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨b', ?_⟩⟩⟩⟩
    rw [hb, hb']
    refine ⟨p₁, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, hd₁, ?_, ?_⟩
      · show IsActiveSignedFace c σ (Submission.boxNorm c σ (Work.Smooth.Morse.param ψ p₁))
          i ε (Work.Smooth.Morse.param ψ p₁)
        rw [hp₁, hsbox]
        exact hacti
      · show IsActiveSignedFace c σ (Submission.boxNorm c σ (Work.Smooth.Morse.param ψ p₁))
          j ε' (Work.Smooth.Morse.param ψ p₁)
        rw [hp₁, hsbox]
        exact hactj
      · intro hinv
        exact hnc ⟨p₁, hp₁, hinv⟩
      · rw [fderiv_pullback_eq_of_param_eq (ψ := ψ) (g := faceLin c σ j ε')
          (p := p₁) (q := p₂) (by rw [hp₁, hp₂])]
        exact hd₂
      · rw [fderiv_pullback_eq_of_param_eq (ψ := ψ)
          (g := fun z : R3 => faceLin c σ i ε z - faceLin c σ j ε' z)
          (p := p₁) (q := p₃) (by rw [hp₁, hp₃])]
        exact hd₃
    · show faceLin c σ i ε (Work.Smooth.Morse.param ψ p₁) = s
      rw [hp₁]
      exact hacti.1
  · rw [MeasureTheory.measure_iUnion_null_iff]
    intro i
    rw [MeasureTheory.measure_iUnion_null_iff]
    intro j
    rw [MeasureTheory.measure_iUnion_null_iff]
    intro b
    rw [MeasureTheory.measure_iUnion_null_iff]
    intro b'
    exact volume_image_badParams_null ψ c σ i j (sgSign b) (sgSign b')

end

end Work.Smooth.BoxGeneric.AeCorner
