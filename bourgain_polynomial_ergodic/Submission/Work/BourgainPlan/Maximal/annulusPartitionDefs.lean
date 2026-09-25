import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusSymbolDefs

/-!
# A smooth dyadic annulus partition of unity on `ℝ ∖ {0}`

The MST §6.1 wiring (`WINDOW_WEAK_TYPE_STATUS_S13.md` §3, item 1) needs a Littlewood--Paley
decomposition of the identity, i.e. a smooth family `(θ_m : ℝ → ℝ)_{m ∈ ℤ}` with

* `θ_m` smooth, `0 ≤ θ_m ≤ 1`, supported in the dyadic annulus `{2⁻¹ < |2^m ξ| < 2}`,
* `θ_m ≡ 1` on the *inner* annulus `{3/4 ≤ |2^m ξ| ≤ 1}` (this is what makes the operators
  idempotent on functions whose frequency support sits there),
* `∑'_m θ_m (ξ) = 1` for `ξ ≠ 0`.

The construction is the classical telescoping one.  Let `s = Real.smoothTransition` (`0` on
`(-∞,0]`, `1` on `[1,∞)`), put

`annStep x = s (2x - 2) + s (-2x - 2)`,

a smooth even function which is `0` on `[-1,1]`, `1` outside `(-3/2, 3/2)` and nondecreasing in
`|x|`; then

`annAtom x = annStep (2x) - annStep x`,

so that `annAtom` is smooth, nonnegative, supported in `(1/2, 3/2)`, equals `1` on `[3/4,1]`, and
**telescopes**: `∑_{m ∈ ℤ} annAtom (2^m ξ) = 1` for `ξ ≠ 0` (the partial sums are
`annStep (2^M ξ) - annStep (2^K ξ)`, of which the first tends to `1` and the second to `0`).  This
file contains the definitions and the elementary pointwise facts; the two analytic facts used
downstream live in their own modules:

* the partition identity (`∑'_m θ_m ξ = 1`) — `annulusPartitionSum`;
* the derivative bound (`AnnulusSymbolSmooth`) — `annulusPartitionDeriv`.

`θ_m ξ = annAtomC m ξ = ((annAtom (2^m ξ) : ℝ) : ℂ)` is the complex lift used as an
`AnnulusSymbolSmooth` family (so that the forward square-function estimate `annulusSquareLp`
applies to it).
-/

open scoped BigOperators

namespace Work.BourgainPlan.Maximal

/-- The smooth even step underlying the dyadic annulus partition: `0` on `[-1,1]`, `1` outside
`(-3/2,3/2)`, nondecreasing in `|x|`. -/
noncomputable def annStep (x : ℝ) : ℝ :=
  Real.smoothTransition (2 * x - 2) + Real.smoothTransition (-2 * x - 2)

/-- The atom of the partition: `annAtom x = annStep (2x) - annStep x`.  It is smooth, nonnegative,
supported in `{1/2 < |x| < 3/2}` and equal to `1` on `{3/4 ≤ |x| ≤ 1}`. -/
noncomputable def annAtom (x : ℝ) : ℝ := annStep (2 * x) - annStep x

/-- The dyadic dilate `ξ ↦ annAtom (2^m ξ)`. -/
noncomputable def annAtomZ (m : ℤ) (ξ : ℝ) : ℝ := annAtom ((2 : ℝ) ^ m * ξ)

/-- The complex lift of the partition atom, the family used as an `AnnulusSymbolSmooth`
symbol family. -/
noncomputable def annAtomC (m : ℤ) (ξ : ℝ) : ℂ := ((annAtomZ m ξ : ℝ) : ℂ)

@[fun_prop]
lemma annStep_contDiff {n : ℕ∞} : ContDiff ℝ n annStep := by
  unfold annStep
  fun_prop

lemma annStep_eq_of_neg_one_le {x : ℝ} (h : -1 ≤ x) :
    annStep x = Real.smoothTransition (2 * x - 2) := by
  have h0 : -2 * x - 2 ≤ 0 := by linarith
  rw [annStep, Real.smoothTransition.zero_of_nonpos h0, add_zero]

lemma annStep_eq_of_le_one {x : ℝ} (h : x ≤ 1) :
    annStep x = Real.smoothTransition (-2 * x - 2) := by
  have h0 : 2 * x - 2 ≤ 0 := by linarith
  rw [annStep, Real.smoothTransition.zero_of_nonpos h0, zero_add]

lemma annStep_eq_zero_of_abs_le_one {x : ℝ} (h : |x| ≤ 1) : annStep x = 0 := by
  rw [annStep_eq_of_neg_one_le (abs_le.mp h).1]
  exact Real.smoothTransition.zero_of_nonpos (by linarith [(abs_le.mp h).2])

lemma annStep_eq_one_of_three_halves_le {x : ℝ} (h : 3 / 2 ≤ |x|) : annStep x = 1 := by
  by_cases hx : 0 ≤ x
  · rw [annStep_eq_of_neg_one_le (by linarith)]
    exact Real.smoothTransition.one_of_one_le (by rw [abs_of_nonneg hx] at h; linarith)
  · have hx' : x < 0 := not_le.mp hx
    rw [annStep_eq_of_le_one (by linarith)]
    exact Real.smoothTransition.one_of_one_le (by rw [abs_of_neg hx'] at h; linarith)

lemma annStep_nonneg (x : ℝ) : 0 ≤ annStep x := by
  rcases le_total (-1) x with hx | hx
  · rw [annStep_eq_of_neg_one_le hx]; exact Real.smoothTransition.nonneg _
  · rw [annStep_eq_of_le_one (by linarith)]; exact Real.smoothTransition.nonneg _

lemma annStep_le_one (x : ℝ) : annStep x ≤ 1 := by
  rcases le_total (-1) x with hx | hx
  · rw [annStep_eq_of_neg_one_le hx]; exact Real.smoothTransition.le_one _
  · rw [annStep_eq_of_le_one (by linarith)]; exact Real.smoothTransition.le_one _

lemma annStep_neg (x : ℝ) : annStep (-x) = annStep x := by
  unfold annStep
  rw [show 2 * -x - 2 = -2 * x - 2 by ring, show -2 * -x - 2 = 2 * x - 2 by ring]
  ring

lemma annStep_mono_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : annStep x ≤ annStep y := by
  rcases le_total x 1 with hx1 | hx1
  · rw [annStep_eq_zero_of_abs_le_one (by rw [abs_of_nonneg hx]; linarith)]
    exact annStep_nonneg y
  · rw [annStep_eq_of_neg_one_le (by linarith), annStep_eq_of_neg_one_le (by linarith)]
    exact Real.smoothTransition.monotone (by linarith)

lemma annStep_mono_abs {x y : ℝ} (h : |x| ≤ |y|) : annStep x ≤ annStep y := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx] at h
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy] at h; exact annStep_mono_nonneg hx h
    · rw [abs_of_neg (not_le.mp hy)] at h
      rw [← annStep_neg y]
      exact annStep_mono_nonneg hx (by linarith)
  · rw [abs_of_neg (not_le.mp hx)] at h
    rw [← annStep_neg x]
    have hx' : 0 ≤ -x := by linarith [not_le.mp hx]
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy] at h; exact annStep_mono_nonneg hx' h
    · rw [abs_of_neg (not_le.mp hy)] at h
      rw [← annStep_neg y]
      exact annStep_mono_nonneg hx' (by linarith)

@[fun_prop]
lemma annAtom_contDiff {n : ℕ∞} : ContDiff ℝ n annAtom := by
  unfold annAtom
  fun_prop

lemma annAtom_nonneg (x : ℝ) : 0 ≤ annAtom x := by
  have h : |x| ≤ |2 * x| := by
    rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    nlinarith [abs_nonneg x]
  have h2 := annStep_mono_abs h
  unfold annAtom
  linarith

lemma annAtom_le_one (x : ℝ) : annAtom x ≤ 1 := by
  have h1 := annStep_le_one (2 * x)
  have h2 := annStep_nonneg x
  unfold annAtom
  linarith

lemma annAtom_eq_zero_of_abs_le_half {x : ℝ} (h : |x| ≤ 1 / 2) : annAtom x = 0 := by
  have h1 : |2 * x| ≤ 1 := by
    rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    nlinarith [abs_nonneg x]
  have h2 : |x| ≤ 1 := by linarith
  rw [annAtom, annStep_eq_zero_of_abs_le_one h1, annStep_eq_zero_of_abs_le_one h2, sub_zero]

lemma annAtom_eq_zero_of_three_halves_le_abs {x : ℝ} (h : 3 / 2 ≤ |x|) : annAtom x = 0 := by
  have h1 : 3 / 2 ≤ |2 * x| := by
    rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    nlinarith [abs_nonneg x]
  rw [annAtom, annStep_eq_one_of_three_halves_le h1, annStep_eq_one_of_three_halves_le h,
    sub_self]

lemma annAtom_eq_one_of_mem {x : ℝ} (h1 : 3 / 4 ≤ |x|) (h2 : |x| ≤ 1) : annAtom x = 1 := by
  have h : 3 / 2 ≤ |2 * x| := by
    rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    nlinarith [abs_nonneg x]
  rw [annAtom, annStep_eq_one_of_three_halves_le h, annStep_eq_zero_of_abs_le_one h2, sub_zero]

lemma annAtom_support {x : ℝ} (h : annAtom x ≠ 0) : 1 / 2 < |x| ∧ |x| < 3 / 2 := by
  refine ⟨?_, ?_⟩
  · by_contra hc
    exact h (annAtom_eq_zero_of_abs_le_half (not_lt.mp hc))
  · by_contra hc
    exact h (annAtom_eq_zero_of_three_halves_le_abs (not_lt.mp hc))

lemma annAtomZ_nonneg (m : ℤ) (ξ : ℝ) : 0 ≤ annAtomZ m ξ := annAtom_nonneg _

lemma annAtomZ_le_one (m : ℤ) (ξ : ℝ) : annAtomZ m ξ ≤ 1 := annAtom_le_one _

lemma annAtomZ_support {m : ℤ} {ξ : ℝ} (h : annAtomZ m ξ ≠ 0) :
    (2 : ℝ)⁻¹ < |(2 : ℝ) ^ m * ξ| ∧ |(2 : ℝ) ^ m * ξ| < 2 := by
  obtain ⟨h1, h2⟩ := annAtom_support h
  exact ⟨by linarith, by linarith⟩

lemma annAtomZ_eq_one {m : ℤ} {ξ : ℝ} (h : 3 / 4 ≤ |(2 : ℝ) ^ m * ξ|)
    (h2 : |(2 : ℝ) ^ m * ξ| ≤ 1) : annAtomZ m ξ = 1 := annAtom_eq_one_of_mem h h2

@[simp]
lemma annAtomC_apply (m : ℤ) (ξ : ℝ) : annAtomC m ξ = ((annAtomZ m ξ : ℝ) : ℂ) := rfl

lemma annAtomC_ne_zero_iff {m : ℤ} {ξ : ℝ} : annAtomC m ξ ≠ 0 ↔ annAtomZ m ξ ≠ 0 := by
  simp [annAtomC]

/-- **The partition atoms are smooth.**  Every member of the family `annAtomC` is `C^∞` (it is the
complex lift of the dilation of `annAtom`, which is `C^∞`). -/
theorem contDiff_annAtomC (m : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (annAtomC m) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : ℝ => (2 : ℝ) ^ m * ξ) := by fun_prop
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => ((annAtom x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp annAtom_contDiff
  exact h2.comp h1

/-! ## The *squared* partition

The Littlewood--Paley recombination `G = ∑_m S_m G S_m` (MST §6.1) needs the partition normalised
with *squares*, `∑_m ψ_m (ξ)² = 1`, so that `∑_m S_m² = Id`.  Since `annAtom` is a smooth
nonnegative function vanishing on an *open* set, its square root is smooth, and

`annAtomSqZ m ξ = √(annAtom (2^m ξ))`, `annAtomSqC m ξ = ((annAtomSqZ m ξ : ℝ) : ℂ)`

is a smooth annulus-supported family whose squares telescope to one (by `hasSum_annAtomZ`). -/

/-- The square root of the partition atom: `√(annAtom (2^m ξ))`. -/
noncomputable def annAtomSqZ (m : ℤ) (ξ : ℝ) : ℝ := Real.sqrt (annAtomZ m ξ)

/-- The complex lift of the squared-partition atom. -/
noncomputable def annAtomSqC (m : ℤ) (ξ : ℝ) : ℂ := ((annAtomSqZ m ξ : ℝ) : ℂ)

lemma annAtomSqZ_nonneg (m : ℤ) (ξ : ℝ) : 0 ≤ annAtomSqZ m ξ := Real.sqrt_nonneg _

lemma annAtomSqZ_sq (m : ℤ) (ξ : ℝ) : annAtomSqZ m ξ ^ 2 = annAtomZ m ξ :=
  Real.sq_sqrt (annAtom_nonneg _)

lemma annAtomSqZ_le_one (m : ℤ) (ξ : ℝ) : annAtomSqZ m ξ ≤ 1 := by
  have h := annAtomSqZ_sq m ξ
  have h0 := annAtomSqZ_nonneg m ξ
  have h1 := annAtomZ_le_one m ξ
  nlinarith

lemma annAtomSqZ_pos_iff {m : ℤ} {ξ : ℝ} : 0 < annAtomSqZ m ξ ↔ 0 < annAtomZ m ξ :=
  Real.sqrt_pos

lemma annAtomSqZ_eq_zero_iff {m : ℤ} {ξ : ℝ} : annAtomSqZ m ξ = 0 ↔ annAtomZ m ξ = 0 := by
  constructor
  · intro h
    exact le_antisymm (Real.sqrt_eq_zero'.mp h) (annAtom_nonneg _)
  · intro h
    rw [annAtomSqZ, h, Real.sqrt_zero]

lemma annAtomSqZ_support {m : ℤ} {ξ : ℝ} (h : annAtomSqZ m ξ ≠ 0) :
    (2 : ℝ)⁻¹ < |(2 : ℝ) ^ m * ξ| ∧ |(2 : ℝ) ^ m * ξ| < 2 :=
  annAtomZ_support (fun hc => h (annAtomSqZ_eq_zero_iff.mpr hc))

@[simp]
lemma annAtomSqC_apply (m : ℤ) (ξ : ℝ) : annAtomSqC m ξ = ((annAtomSqZ m ξ : ℝ) : ℂ) := rfl

lemma annAtomSqC_ne_zero_iff {m : ℤ} {ξ : ℝ} : annAtomSqC m ξ ≠ 0 ↔ annAtomSqZ m ξ ≠ 0 := by
  simp [annAtomSqC]

end Work.BourgainPlan.Maximal
