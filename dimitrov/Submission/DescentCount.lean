import Mathlib
import Submission.Conjugates
import Submission.Phases

/-!
# Counting consequences of negation-closure (master structure / descent)

If the set `S := conjugateValues α` of conjugates of `α` is closed under
negation (`z ∈ S ⟹ -z ∈ S`), then squaring pairs up the conjugates:
`{z² : z ∈ S}` has exactly half as many elements as `S`, and the number of
*phases* of `α²` is exactly half the number of phases of `α`:

* `card_conjugateValues_sq_two_mul`: `|conjugateValues (α^2)| * 2 = |conjugateValues α|`
* `argSet_sq_card_two_mul`: `|argSet (α^2)| * 2 = |argSet α|`

These two identities make the descent `α ↦ α²` close the constants perfectly
in the induction proving the phase-refined Schinzel–Zassenhaus bound
(degree halves, phase count halves, and `house α = sqrt (house (α^2))`).

Also recorded: `conjugateValues_sq` (the squares of the conjugates of `α` are
the conjugates of `α^2`) and `house_sq` (`house (α^2) = (house α)^2`).

## How the halving lemmas are proved here

All the counting takes place at the level of an arbitrary finite set
`S : Finset ℂ` of *nonzero* numbers closed under negation (`hS0`, `hneg`):

* `phaseSq_card_two_mul S hS0 hneg`: squaring halves the number of distinct
  phases: `|(S.image (·^2)).image arg| * 2 = |S.image arg|`.
* `conjSq_card_two_mul S hS0 hneg`: squaring halves the number of distinct
  values: `|S.image (·^2)| * 2 = |S|`.

For the phase count one argues as follows.  Let `A := S.image arg`
(a finite set of principal arguments, all lying in `(-π, π]`) and let
`An := A.filter (· ≤ 0)`.  Since `S` is closed under negation and `z ≠ 0`
for `z ∈ S`, `-z ∈ S` has principal argument `arg z ± π` (plus when
`arg z ≤ 0`, minus otherwise) — this is `arg_neg_eq_if`.  Consequently `A`
is *antipodally closed*: non-positive arguments are accompanied by their
antipode `θ + π` (`hclo`), positive ones by `θ - π` (`hcup`).  The doubling
map `D(θ) := (2 • θ : Real.Angle).toReal` (= the principal argument of
`z²` when `θ = arg z`, by `Complex.arg_pow_coe_angle`) sends antipodes to
the same value (`doubleArg_add_pi`, `doubleArg_sub_pi`) and is injective on
each half-plane (`doubleArg_inj_on_nonpos`, which is
`Submission.Phases.two_smul_toReal_inj_same_half`).  Hence `A.image D`
has exactly `|An|` elements while `A` splits as `An ⊎ Ap` with
`Ap = An.image (· + π)`, so `|A| = 2·|An|`.  This is the content of the
structural lemma `doubleArg_image_card_eq_half`.

The value-counting lemma `conjSq_card_two_mul` is the same pairing argument
performed on `S` itself: split `S = Sn ⊎ Sp` by the sign of the principal
argument, notice `Sp = Sn.image (- ·)` (negation maps one half to the other
and `arg (-z) = arg z ± π` again), and that `z ↦ z²` is injective on `Sn`
(`z² = w²` forces `w = ±z`, and the minus sign would move the phase across
zero).  Squaring sends `Sp` into the image of `Sn`, so
`S.image (·^2) = Sn.image (·^2)`.

The four field-level theorems then follow by taking `S := conjugateValues α`
(whose elements are nonzero because the complex embeddings are injective)
and using the image calculus `conjugateValues_sq` and the definition
`argSet β = (conjugateValues β).image arg`.
-/

noncomputable section

open scoped Complex

namespace Submission.Descent

open Submission.Conjugates

variable {K : Type*} [Field K] [NumberField K]

/-! ## Antipodal phases and the doubling map -/

/-- The doubling map on principal arguments: the principal argument of `z²`
in terms of the principal argument of `z`. -/
def doubleArg (θ : ℝ) : ℝ := (2 • (θ : Real.Angle)).toReal

/-- The principal argument of `-z`: it is `arg z ± π`, choosing the sign that
lands back inside `(-π, π]`. -/
lemma arg_neg_eq_if (z : ℂ) (hz : z ≠ 0) :
    Complex.arg (-z) = if Complex.arg z ≤ 0 then Complex.arg z + Real.pi else Complex.arg z - Real.pi := by
  by_cases hle : Complex.arg z ≤ 0
  · have hzarg : Complex.arg (-z) = Complex.arg z + Real.pi := by
      have hang : (Complex.arg (-z) : Real.Angle) = (Complex.arg z : Real.Angle) + (Real.pi : Real.Angle) := by
        simpa using (Complex.arg_neg_coe_angle hz)
      have hang2 : (Complex.arg (-z) : Real.Angle) = (((Complex.arg z + Real.pi) : ℝ) : Real.Angle) := by
        rw [hang]
        rw [Real.Angle.coe_add]
      have hmem : Complex.arg z + Real.pi ∈ Set.Ioc (-Real.pi) Real.pi := by
        have h1 : -Real.pi < Complex.arg z := (Complex.arg_mem_Ioc z).1
        constructor
        · linarith
        · have h2 : Complex.arg z ≤ Real.pi := (Complex.arg_mem_Ioc z).2
          linarith
      have htr := congrArg Real.Angle.toReal hang2
      rw [Complex.arg_coe_angle_toReal_eq_arg] at htr
      rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hmem] at htr
      exact htr
    rw [if_pos hle]
    exact hzarg
  · have hgt : 0 < Complex.arg z := lt_of_not_ge hle
    have hzarg : Complex.arg (-z) = Complex.arg z - Real.pi := by
      have hang : (Complex.arg (-z) : Real.Angle) = (Complex.arg z : Real.Angle) + (Real.pi : Real.Angle) := by
        simpa using (Complex.arg_neg_coe_angle hz)
      have hang2 : (Complex.arg (-z) : Real.Angle) = (((Complex.arg z - Real.pi) : ℝ) : Real.Angle) := by
        rw [hang]
        rw [Real.Angle.coe_sub]
        rw [Real.Angle.sub_coe_pi_eq_add_coe_pi]
      have hmem : Complex.arg z - Real.pi ∈ Set.Ioc (-Real.pi) Real.pi := by
        have h2 : Complex.arg z ≤ Real.pi := (Complex.arg_mem_Ioc z).2
        constructor
        · linarith
        · linarith
      have htr := congrArg Real.Angle.toReal hang2
      rw [Complex.arg_coe_angle_toReal_eq_arg] at htr
      rw [Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hmem] at htr
      exact htr
    rw [if_neg hle]
    exact hzarg

/-- Doubling is invariant under the antipodal shift `θ ↦ θ + π`. -/
lemma doubleArg_add_pi (θ : ℝ) : doubleArg (θ + Real.pi) = doubleArg θ := by
  unfold doubleArg
  have hang : (2 : ℕ) • (((θ + Real.pi : ℝ) : Real.Angle)) = (2 : ℕ) • ((θ : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add]
    rw [nsmul_add]
    rw [Real.Angle.two_nsmul_coe_pi]
    rw [add_zero]
  exact congrArg Real.Angle.toReal hang

/-- Doubling is invariant under the antipodal shift `θ ↦ θ - π`. -/
lemma doubleArg_sub_pi (θ : ℝ) : doubleArg (θ - Real.pi) = doubleArg θ := by
  unfold doubleArg
  have hang : (2 : ℕ) • (((θ - Real.pi : ℝ) : Real.Angle)) = (2 : ℕ) • ((θ : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub]
    rw [Real.Angle.sub_coe_pi_eq_add_coe_pi]
    rw [nsmul_add]
    rw [Real.Angle.two_nsmul_coe_pi]
    rw [add_zero]
  exact congrArg Real.Angle.toReal hang

/-- The principal argument of `z²` is the doubling of the principal argument
of `z`. -/
lemma arg_sq_eq_doubleArg (z : ℂ) : Complex.arg (z ^ 2) = doubleArg (Complex.arg z) := by
  unfold doubleArg
  exact Submission.Phases.arg_sq_eq_toReal_two_smul z

/-- The doubling map is injective on principal arguments lying in the same
(non-positive) half-circle. -/
lemma doubleArg_inj_on_nonpos {θ₁ θ₂ : ℝ}
    (h₁ : θ₁ ∈ Set.Ioc (-Real.pi) Real.pi) (h₂ : θ₂ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hθ₁ : θ₁ ≤ 0) (hθ₂ : θ₂ ≤ 0)
    (h : doubleArg θ₁ = doubleArg θ₂) : θ₁ = θ₂ := by
  unfold doubleArg at h
  exact Submission.Phases.two_smul_toReal_inj_same_half h₁ h₂ (iff_of_true hθ₁ hθ₂) h

/-- `-z` has phase `arg z + π` when `z` has non-positive phase. -/
lemma arg_neg_eq_add_pi_of_arg_nonpos (z : ℂ) (hz : z ≠ 0) (hle : Complex.arg z ≤ 0) :
    Complex.arg (-z) = Complex.arg z + Real.pi := by
  rw [arg_neg_eq_if z hz, if_pos hle]

/-- `-z` has phase `arg z - π` when `z` has positive phase. -/
lemma arg_neg_eq_sub_pi_of_arg_pos (z : ℂ) (hz : z ≠ 0) (hgt : 0 < Complex.arg z) :
    Complex.arg (-z) = Complex.arg z - Real.pi := by
  rw [arg_neg_eq_if z hz, if_neg (not_le_of_gt hgt)]

/-- If `S` is closed under negation then a non-positive phase is accompanied
by its antipode `θ + π` among the phases of `S`. -/
lemma arg_add_pi_mem_phase {S : Finset ℂ} (hS0 : ∀ z ∈ S, z ≠ 0) (hneg : ∀ z ∈ S, -z ∈ S)
    {z : ℂ} (hz : z ∈ S) (hle : Complex.arg z ≤ 0) :
    Complex.arg z + Real.pi ∈ S.image Complex.arg := by
  have hz' : -z ∈ S := hneg z hz
  have harg : Complex.arg (-z) = Complex.arg z + Real.pi :=
    arg_neg_eq_add_pi_of_arg_nonpos z (hS0 z hz) hle
  rw [← harg]
  exact Finset.mem_image.mpr ⟨-z, hz', rfl⟩

/-- If `S` is closed under negation then a positive phase is accompanied by
its antipode `θ - π` among the phases of `S`. -/
lemma arg_sub_pi_mem_phase {S : Finset ℂ} (hS0 : ∀ z ∈ S, z ≠ 0) (hneg : ∀ z ∈ S, -z ∈ S)
    {z : ℂ} (hz : z ∈ S) (hgt : 0 < Complex.arg z) :
    Complex.arg z - Real.pi ∈ S.image Complex.arg := by
  have hz' : -z ∈ S := hneg z hz
  have harg : Complex.arg (-z) = Complex.arg z - Real.pi :=
    arg_neg_eq_sub_pi_of_arg_pos z (hS0 z hz) hgt
  rw [← harg]
  exact Finset.mem_image.mpr ⟨-z, hz', rfl⟩

/-! ## The structural halving lemma for phase sets -/

/-- For a finite set `A` of principal arguments in `(-π, π]` which is
*antipodally closed* (with every `θ ∈ A`, `θ ≤ 0` also `θ + π ∈ A`, and with
every `θ ∈ A`, `0 < θ` also `θ - π ∈ A`), the doubling map halves `A`:
the number of distinct doubled arguments is exactly half the number of
arguments in `A`. -/
lemma doubleArg_image_card_eq_half (A : Finset ℝ)
    (hmemIoc : ∀ θ ∈ A, θ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hclo : ∀ θ ∈ A, θ ≤ 0 → θ + Real.pi ∈ A)
    (hcup : ∀ θ ∈ A, 0 < θ → θ - Real.pi ∈ A) :
    let An : Finset ℝ := A.filter (fun θ : ℝ => θ ≤ 0)
    let Ap : Finset ℝ := A.filter (fun θ : ℝ => 0 < θ)
    (A.image doubleArg).card * 2 = A.card := by
  classical
  let An : Finset ℝ := A.filter (fun θ : ℝ => θ ≤ 0)
  let Ap : Finset ℝ := A.filter (fun θ : ℝ => 0 < θ)
  have hmemIoc_le_pi : ∀ θ ∈ A, θ ≤ Real.pi := fun θ hθ => (hmemIoc θ hθ).2
  have hmemIoc_gt_negpi : ∀ θ ∈ A, -Real.pi < θ := fun θ hθ => (hmemIoc θ hθ).1
  -- A = An ∪ Ap disjoint
  have hAunion : A = An ∪ Ap := by
    ext θ
    constructor
    · intro hθ
      by_cases hpos : 0 < θ
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hθ, hpos⟩))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hθ, le_of_not_gt hpos⟩))
    · intro hθ
      rcases Finset.mem_union.mp hθ with hθn | hθp
      · exact (Finset.mem_filter.mp hθn).1
      · exact (Finset.mem_filter.mp hθp).1
  have hdisj : Disjoint An Ap := by
    rw [Finset.disjoint_left]
    intro θ hθAn hθAp
    exact (not_le_of_gt (Finset.mem_filter.mp hθAp).2) (Finset.mem_filter.mp hθAn).2
  -- |Ap| = |An| via θ ↦ θ + π
  have hAp_eq_image : Ap = An.image (fun θ : ℝ => θ + Real.pi) := by
    ext θ
    constructor
    · intro hθAp
      have hθA : θ ∈ A := (Finset.mem_filter.mp hθAp).1
      have hgt : 0 < θ := (Finset.mem_filter.mp hθAp).2
      have hθ' : θ - Real.pi ∈ An := by
        refine Finset.mem_filter.mpr ⟨hcup θ hθA hgt, ?_⟩
        linarith [hmemIoc_le_pi θ hθA]
      refine Finset.mem_image.mpr ⟨θ - Real.pi, hθ', ?_⟩
      ring
    · intro hθ
      rcases Finset.mem_image.mp hθ with ⟨η, hηAn, rfl⟩
      have hηA : η ∈ A := (Finset.mem_filter.mp hηAn).1
      have hηle : η ≤ 0 := (Finset.mem_filter.mp hηAn).2
      have hshift : η + Real.pi ∈ A := hclo η hηA hηle
      refine Finset.mem_filter.mpr ⟨hshift, ?_⟩
      linarith [hmemIoc_gt_negpi η hηA]
  have hcardAp : Ap.card = An.card := by
    rw [hAp_eq_image]
    exact Finset.card_image_of_injective (s := An) (f := fun θ : ℝ => θ + Real.pi) (by
      intro θ₁ θ₂ h
      exact add_right_cancel h)
  -- |A| = 2|An|
  have hcardA : A.card = 2 * An.card := by
    rw [hAunion]
    rw [Finset.card_union_of_disjoint hdisj]
    rw [hcardAp]
    omega
  -- injectivity of doubleArg on An
  have hinjAn : Set.InjOn doubleArg ↑An := by
    intro θ₁ hθ₁An θ₂ hθ₂An h
    exact doubleArg_inj_on_nonpos (hmemIoc θ₁ (Finset.mem_filter.mp hθ₁An).1)
      (hmemIoc θ₂ (Finset.mem_filter.mp hθ₂An).1)
      (Finset.mem_filter.mp hθ₁An).2 (Finset.mem_filter.mp hθ₂An).2 h
  have hcardAnImg : (An.image doubleArg).card = An.card := by
    apply Finset.card_image_of_injOn hinjAn
  -- doubleArg(A) = doubleArg(An): extra contributions from Ap double to An values
  have hApImg : Ap.image doubleArg ⊆ An.image doubleArg := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨θ, hθAp, rfl⟩
    have hθA : θ ∈ A := (Finset.mem_filter.mp hθAp).1
    have hgt : 0 < θ := (Finset.mem_filter.mp hθAp).2
    have hθ' : θ - Real.pi ∈ An := by
      refine Finset.mem_filter.mpr ⟨hcup θ hθA hgt, ?_⟩
      linarith [hmemIoc_le_pi θ hθA]
    refine Finset.mem_image.mpr ⟨θ - Real.pi, hθ', ?_⟩
    exact doubleArg_sub_pi θ
  have hAnsubA : An ⊆ A := Finset.filter_subset _ A
  have hAimg_eq : A.image doubleArg = An.image doubleArg := by
    apply le_antisymm
    · intro v hv
      rcases Finset.mem_image.mp hv with ⟨θ, hθA, rfl⟩
      have hθAnAp : θ ∈ An ∪ Ap := by simpa [hAunion] using hθA
      rcases Finset.mem_union.mp hθAnAp with hθAn | hθAp
      · exact Finset.mem_image.mpr ⟨θ, hθAn, rfl⟩
      · exact hApImg (Finset.mem_image.mpr ⟨θ, hθAp, rfl⟩)
    · exact Finset.image_subset_image hAnsubA
  -- cardinal conclusion
  have hcardImgA : (A.image doubleArg).card = An.card := by
    rw [hAimg_eq]
    exact hcardAnImg
  calc
    (A.image doubleArg).card * 2 = An.card * 2 := by rw [hcardImgA]
    _ = A.card := by
      rw [hcardA]
      omega

/-- If `S` is a finite set of nonzero complex numbers closed under negation,
then squaring halves the number of distinct phases. -/
lemma phaseSq_card_two_mul (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    (hneg : ∀ z ∈ S, -z ∈ S) :
    ((S.image fun z : ℂ => z ^ 2).image Complex.arg).card * 2 = (S.image Complex.arg).card := by
  classical
  let A : Finset ℝ := S.image Complex.arg
  have hmemIoc : ∀ θ ∈ A, θ ∈ Set.Ioc (-Real.pi) Real.pi := by
    intro θ hθ
    rcases Finset.mem_image.mp hθ with ⟨z, hzS, rfl⟩
    exact Complex.arg_mem_Ioc z
  have hclo : ∀ θ ∈ A, θ ≤ 0 → θ + Real.pi ∈ A := by
    intro θ hθA hle
    rcases Finset.mem_image.mp hθA with ⟨z, hzS, hzθ⟩
    have hzle : Complex.arg z ≤ 0 := by simpa [hzθ] using hle
    have hmem : Complex.arg z + Real.pi ∈ A := by
      simpa [A] using (arg_add_pi_mem_phase (S := S) hS0 hneg hzS hzle)
    simpa [hzθ] using hmem
  have hcup : ∀ θ ∈ A, 0 < θ → θ - Real.pi ∈ A := by
    intro θ hθA hgt
    rcases Finset.mem_image.mp hθA with ⟨z, hzS, hzθ⟩
    have hzgt : 0 < Complex.arg z := by simpa [hzθ] using hgt
    have hmem : Complex.arg z - Real.pi ∈ A := by
      simpa [A] using (arg_sub_pi_mem_phase (S := S) hS0 hneg hzS hzgt)
    simpa [hzθ] using hmem
  have hAimg : ((S.image fun z : ℂ => z ^ 2).image Complex.arg).card * 2 =
      (S.image Complex.arg).card := by
    have hEq : (S.image (fun z : ℂ => z ^ 2)).image Complex.arg = A.image doubleArg := by
      calc
        (S.image (fun z : ℂ => z ^ 2)).image Complex.arg
            = S.image (fun z : ℂ => Complex.arg (z ^ 2)) := by
              exact Finset.image_image
        _ = S.image (fun z : ℂ => doubleArg (Complex.arg z)) := by
              apply Finset.image_congr
              intro z hz
              exact arg_sq_eq_doubleArg z
        _ = (S.image Complex.arg).image doubleArg := by
              exact (Finset.image_image (s := S) (f := Complex.arg) (g := doubleArg)).symm
        _ = A.image doubleArg := by rfl
    rw [hEq]
    change (A.image doubleArg).card * 2 = A.card
    exact doubleArg_image_card_eq_half A hmemIoc hclo hcup
  exact hAimg

/-- If `S` is a finite set of nonzero complex numbers closed under negation,
then squaring halves the number of distinct values. -/
lemma conjSq_card_two_mul (S : Finset ℂ) (hS0 : ∀ z ∈ S, z ≠ 0)
    (hneg : ∀ z ∈ S, -z ∈ S) :
    (S.image fun z : ℂ => z ^ 2).card * 2 = S.card := by
  classical
  let Sn : Finset ℂ := S.filter (fun z : ℂ => Complex.arg z ≤ 0)
  let Sp : Finset ℂ := S.filter (fun z : ℂ => ¬Complex.arg z ≤ 0)
  have hmemIoc : ∀ z ∈ S, Complex.arg z ∈ Set.Ioc (-Real.pi) Real.pi :=
    fun z hz => Complex.arg_mem_Ioc z
  -- partition
  have hSunion : S = Sn ∪ Sp := by
    ext z
    constructor
    · intro hz
      by_cases hle : Complex.arg z ≤ 0
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hz, hle⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hz, hle⟩))
    · intro hz
      rcases Finset.mem_union.mp hz with hzn | hzp
      · exact (Finset.mem_filter.mp hzn).1
      · exact (Finset.mem_filter.mp hzp).1
  have hdisj : Disjoint Sn Sp := by
    rw [Finset.disjoint_left]
    intro z hzSn hzSp
    exact (Finset.mem_filter.mp hzSp).2 (Finset.mem_filter.mp hzSn).2
  -- Sp = image of Sn under negation
  have hSp_eq_image : Sp = Sn.image (fun z : ℂ => -z) := by
    ext z
    constructor
    · intro hzSp
      have hzS : z ∈ S := (Finset.mem_filter.mp hzSp).1
      have hgt : ¬Complex.arg z ≤ 0 := (Finset.mem_filter.mp hzSp).2
      have hnegzS : -z ∈ S := hneg z hzS
      have harg : Complex.arg (-z) = Complex.arg z - Real.pi :=
        arg_neg_eq_sub_pi_of_arg_pos z (hS0 z hzS) (lt_of_not_ge hgt)
      have hnegzSn : -z ∈ Sn := by
        refine Finset.mem_filter.mpr ⟨hnegzS, ?_⟩
        rw [harg]
        have hzIoc := hmemIoc z hzS
        linarith [hzIoc.2]
      refine Finset.mem_image.mpr ⟨-z, hnegzSn, ?_⟩
      simp
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨w, hwSn, rfl⟩
      have hwS : w ∈ S := (Finset.mem_filter.mp hwSn).1
      have hwle : Complex.arg w ≤ 0 := (Finset.mem_filter.mp hwSn).2
      have hnegwS : -w ∈ S := hneg w hwS
      have harg : Complex.arg (-w) = Complex.arg w + Real.pi :=
        arg_neg_eq_add_pi_of_arg_nonpos w (hS0 w hwS) hwle
      refine Finset.mem_filter.mpr ⟨hnegwS, ?_⟩
      rw [harg]
      have hwIoc := hmemIoc w hwS
      intro hle
      have hpos : 0 < Complex.arg w + Real.pi := by linarith [hwIoc.1]
      exact (not_lt_of_ge hle) hpos
  have hcardSp : Sp.card = Sn.card := by
    rw [hSp_eq_image]
    exact Finset.card_image_of_injective (s := Sn) (f := fun z : ℂ => -z) neg_injective
  -- injectivity of squaring on Sn
  have hinjSn : Set.InjOn (fun z : ℂ => z ^ 2) ↑Sn := by
    intro z hzSn w hwSn hsq
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with hzw | hznegw
    · exact hzw
    · exfalso
      have hzle : Complex.arg z ≤ 0 := (Finset.mem_filter.mp hzSn).2
      have hwS : w ∈ S := (Finset.mem_filter.mp hwSn).1
      have hwle : Complex.arg w ≤ 0 := (Finset.mem_filter.mp hwSn).2
      have harg : Complex.arg (-w) = Complex.arg w + Real.pi :=
        arg_neg_eq_add_pi_of_arg_nonpos w (hS0 w hwS) hwle
      have hle' : Complex.arg w + Real.pi ≤ 0 := by
        have hnegwle : Complex.arg (-w) ≤ 0 := by
          rw [← hznegw]
          exact hzle
        rwa [harg] at hnegwle
      have hwIoc := hmemIoc w hwS
      exact (not_lt_of_ge hle') (by linarith [hwIoc.1])
  have hcardSnImg : (Sn.image fun z : ℂ => z ^ 2).card = Sn.card := by
    apply Finset.card_image_of_injOn hinjSn
  -- images of squaring: whole S vs Sn
  have hSpImg : Sp.image (fun z : ℂ => z ^ 2) ⊆ Sn.image (fun z : ℂ => z ^ 2) := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨z, hzSp, rfl⟩
    have hzS : z ∈ S := (Finset.mem_filter.mp hzSp).1
    have hgt : ¬Complex.arg z ≤ 0 := (Finset.mem_filter.mp hzSp).2
    have hnegzS : -z ∈ S := hneg z hzS
    have harg : Complex.arg (-z) = Complex.arg z - Real.pi :=
      arg_neg_eq_sub_pi_of_arg_pos z (hS0 z hzS) (lt_of_not_ge hgt)
    have hnegzSn : -z ∈ Sn := by
      refine Finset.mem_filter.mpr ⟨hnegzS, ?_⟩
      rw [harg]
      have hzIoc := hmemIoc z hzS
      linarith [hzIoc.2]
    refine Finset.mem_image.mpr ⟨-z, hnegzSn, ?_⟩
    ring
  have hSnsubS : Sn ⊆ S := Finset.filter_subset _ S
  have hSimg_eq : S.image (fun z : ℂ => z ^ 2) = Sn.image (fun z : ℂ => z ^ 2) := by
    apply le_antisymm
    · intro v hv
      rcases Finset.mem_image.mp hv with ⟨z, hzS, rfl⟩
      have hzSnSp : z ∈ Sn ∪ Sp := by simpa [hSunion] using hzS
      rcases Finset.mem_union.mp hzSnSp with hzSn | hzSp
      · exact Finset.mem_image.mpr ⟨z, hzSn, rfl⟩
      · exact hSpImg (Finset.mem_image.mpr ⟨z, hzSp, rfl⟩)
    · exact Finset.image_subset_image hSnsubS
  -- cardinal arithmetic
  have hcardS : S.card = 2 * Sn.card := by
    rw [hSunion]
    rw [Finset.card_union_of_disjoint hdisj]
    rw [hcardSp]
    omega
  have hcardImgS : (S.image fun z : ℂ => z ^ 2).card = Sn.card := by
    rw [hSimg_eq]
    exact hcardSnImg
  calc
    (S.image fun z : ℂ => z ^ 2).card * 2 = Sn.card * 2 := by rw [hcardImgS]
    _ = S.card := by
      rw [hcardS]
      omega

/-- The conjugates of `α` are nonzero when `α` is nonzero. -/
lemma conjugate_ne_zero_of_ne_zero (α : K) (hα0 : α ≠ 0) :
    ∀ z : ℂ, z ∈ conjugateValues α → z ≠ 0 := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨σ, hσ, rfl⟩
  exact (map_ne_zero σ).2 hα0

/-! ## The four field-level theorems -/

/-- The conjugates of `α²` are exactly the squares of the conjugates of `α`. -/
theorem conjugateValues_sq (α : K) :
    conjugateValues (α ^ 2) = (conjugateValues α).image (fun z : ℂ => z ^ 2) := by
  classical
  unfold conjugateValues
  rw [Finset.image_image]
  congr 1
  ext σ
  exact map_pow σ α 2

/-- The house of `α²` is the square of the house of `α`. -/
theorem house_sq (α : K) : NumberField.house (α ^ 2) = (NumberField.house α) ^ 2 := by
  classical
  let S : Finset ℂ := conjugateValues α
  let S₂ : Finset ℂ := conjugateValues (α ^ 2)
  let mNN : NNReal := S.sup (fun z : ℂ => ‖z‖₊)
  let m2NN : NNReal := S₂.sup (fun z : ℂ => ‖z‖₊)
  have hm : NumberField.house α = (mNN : ℝ) := by
    simpa [mNN, S] using (house_eq_sup_conj α)
  have hm2 : NumberField.house (α ^ 2) = (m2NN : ℝ) := by
    simpa [m2NN, S₂] using (house_eq_sup_conj (α ^ 2))
  have hle : m2NN ≤ mNN ^ 2 := by
    apply Finset.sup_le
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨σ, hσ, rfl⟩
    have hzS : σ α ∈ S := by
      simpa [S, conjugateValues] using (Finset.mem_image.mpr (⟨σ, Finset.mem_univ σ, rfl⟩ : (σ α) ∈ Finset.univ.image (fun τ : K →+* ℂ => τ α)))
    have hnorm : ‖σ (α ^ 2)‖₊ = ‖σ α‖₊ ^ 2 := by
      rw [map_pow]
      exact nnnorm_pow (σ α) 2
    rw [hnorm]
    exact pow_le_pow_left₀ zero_le (Finset.le_sup (f := fun z : ℂ => ‖z‖₊) hzS) 2
  have hge : mNN ^ 2 ≤ m2NN := by
    rcases exists_conj_house α with ⟨σ₀, hσ₀⟩
    have hσ₀real : (mNN : ℝ) = (‖σ₀ α‖₊ : ℝ) := by
      calc
        (mNN : ℝ) = NumberField.house α := hm.symm
        _ = ‖σ₀ α‖ := hσ₀
        _ = (‖σ₀ α‖₊ : ℝ) := by simp
    have hmNN : mNN = ‖σ₀ α‖₊ := by
      exact NNReal.coe_injective hσ₀real
    have hw : σ₀ (α ^ 2) ∈ S₂ := by
      simpa [S₂, conjugateValues] using (Finset.mem_image.mpr (⟨σ₀, Finset.mem_univ σ₀, rfl⟩ : (σ₀ (α ^ 2)) ∈ Finset.univ.image (fun τ : K →+* ℂ => τ (α ^ 2))))
    have hn : ‖σ₀ (α ^ 2)‖₊ = ‖σ₀ α‖₊ ^ 2 := by
      rw [map_pow]
      exact nnnorm_pow (σ₀ α) 2
    have hw2 : ‖σ₀ (α ^ 2)‖₊ = mNN ^ 2 := by
      rw [hn, ← hmNN]
    calc
      mNN ^ 2 = ‖σ₀ (α ^ 2)‖₊ := hw2.symm
      _ ≤ m2NN := Finset.le_sup (f := fun z : ℂ => ‖z‖₊) hw
  have hNN : m2NN = mNN ^ 2 := le_antisymm hle hge
  calc
    NumberField.house (α ^ 2) = (m2NN : ℝ) := hm2
    _ = ((mNN ^ 2 : NNReal) : ℝ) := by rw [hNN]
    _ = (mNN : ℝ) ^ 2 := by rw [NNReal.coe_pow]
    _ = (NumberField.house α) ^ 2 := by rw [← hm]

/-- If the conjugates of `α` are closed under negation, then `α²` has exactly
half as many distinct conjugates as `α`. -/
theorem card_conjugateValues_sq_two_mul (α : K) (hα0 : α ≠ 0)
    (hneg : ∀ z : ℂ, z ∈ conjugateValues α → -z ∈ conjugateValues α) :
    (conjugateValues (α ^ 2)).card * 2 = (conjugateValues α).card := by
  classical
  have hS0 := conjugate_ne_zero_of_ne_zero α hα0
  have hmain := conjSq_card_two_mul (S := conjugateValues α) hS0 hneg
  rw [conjugateValues_sq]
  exact hmain

/-- If the conjugates of `α` are closed under negation, then `α²` has exactly
half as many distinct phases as `α`. -/
theorem argSet_sq_card_two_mul (α : K) (hα0 : α ≠ 0)
    (hneg : ∀ z : ℂ, z ∈ conjugateValues α → -z ∈ conjugateValues α) :
    (argSet (α ^ 2)).card * 2 = (argSet α).card := by
  classical
  have hS0 := conjugate_ne_zero_of_ne_zero α hα0
  have hmain := phaseSq_card_two_mul (S := conjugateValues α) hS0 hneg
  unfold argSet
  rw [conjugateValues_sq]
  exact hmain

end Submission.Descent

end
