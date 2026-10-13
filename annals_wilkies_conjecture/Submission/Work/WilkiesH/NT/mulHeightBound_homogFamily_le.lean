import Mathlib
import Submission.Work.WilkiesH.NT.HomogDefs
import Submission.Work.WilkiesH.Defs

/-!
# The height bound for the homogenisation family

Let `P : MvPolynomial (Fin n) ℤ` have total degree `≤ d` and all of its coefficients bounded
by `N` in absolute value.  We bound the size of the constant `Height.mulHeightBound` attached
to the family `homogFamily P d = (homog P d, X₀^d)` of homogeneous polynomials of degree `d`:

  `max (mulHeightBound (homogFamily P d)) 1 ≤ (monoCount n d * N) ^ [K : ℚ]`.

The argument is a place-by-place estimate, using the explicit description of the coefficients
of the homogenisation: the monomial `∏ᵢ Xᵢ ^ mᵢ` of `P` contributes the monomial
`X₀ ^ (d - deg m) * ∏ᵢ Xᵢ ^ mᵢ` of `homog P d` with the same coefficient, and the map
`m ↦ cons (d - deg m) m` is injective on the support of `P`.

* At an archimedean place `v` the coefficient sum `∑_s v (coeff s)` is the sum of the values of
  the coefficients of `P`, each of which is `≤ N` because `v` restricts to the usual absolute
  value on `ℤ`; there are at most `monoCount n d` of them, since the support of `P` injects into
  the exponent vectors of total degree `≤ d` (`ExpVec`).
* At a nonarchimedean place every coefficient of `homog P d` is an integer cast, hence has value
  `≤ 1`; the second member `X₀ ^ d` of the family has the single coefficient `1`, so its
  contribution is `max (…, 1) = 1` as well.

Taking the product over the archimedean places (`totalWeight K = [K : ℚ]` of them, counted with
multiplicity) and the `finprod` over the nonarchimedean ones gives the claim.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

noncomputable section

open MvPolynomial

namespace Work.WilkiesH.NT

open Work.WilkiesH

variable {K : Type*} [Field K] {n d : ℕ}

namespace HomogHeightAux

/-! ### The coefficients of `homog` -/

/-- The exponent vectors `m ↦ Finsupp.cons (d - m.degree) m` (with respect to the extra
variable `X 0`) that describe the monomials of `homog P d` are injective on exponent vectors
of total degree `≤ d`. -/
lemma cons_degree_injective {m m' : Fin n →₀ ℕ} (hm : m.degree ≤ d) (hm' : m'.degree ≤ d)
    (h : Finsupp.cons (d - m.degree) m = Finsupp.cons (d - m'.degree) m') : m = m' := by
  have h0 : d - m.degree = d - m'.degree := by
    rw [← Finsupp.cons_zero (d - m.degree) m, h, Finsupp.cons_zero (d - m'.degree) m']
  have hd : m.degree = m'.degree := by omega
  refine Finsupp.ext fun i => ?_
  have hh := congrArg (fun f : Fin (n + 1) →₀ ℕ => f i.succ) h
  simpa [Finsupp.cons_succ] using hh

/-- Every monomial occurring in `P` has degree at most `d`. -/
lemma degree_le_of_mem_support (P : MvPolynomial (Fin n) ℤ) (hdeg : P.totalDegree ≤ d)
    {m : Fin n →₀ ℕ} (hm : m ∈ P.support) : m.degree ≤ d :=
  (MvPolynomial.le_totalDegree hm).trans hdeg

/-- The coefficient of `homog P d` at the monomial corresponding to `m` is the coefficient of
`P` at `m`. -/
lemma homog_coeff_cons (P : MvPolynomial (Fin n) ℤ) (hdeg : P.totalDegree ≤ d)
    {m : Fin n →₀ ℕ} (hm : m ∈ P.support) :
    (homog (K := K) P d).coeff (Finsupp.cons (d - m.degree) m) = ((P.coeff m : ℤ) : K) := by
  rw [homog, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single m]
  · rw [MvPolynomial.coeff_monomial, ite_eq_left rfl]
  · intro m' hm' hne
    rw [MvPolynomial.coeff_monomial, ite_eq_right]
    exact fun hcon => hne (cons_degree_injective (degree_le_of_mem_support P hdeg hm')
      (degree_le_of_mem_support P hdeg hm) hcon)
  · intro hm'; exact absurd hm hm'

/-- The coefficients of `homog P d` vanish away from the monomials coming from the support
of `P`. -/
lemma homog_coeff_eq_zero_of_notMem_image (P : MvPolynomial (Fin n) ℤ) {s : Fin (n + 1) →₀ ℕ}
    (hs : s ∉ P.support.image (fun m => Finsupp.cons (d - m.degree) m)) :
    (homog (K := K) P d).coeff s = 0 := by
  rw [homog, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_zero]
  intro m hm
  rw [MvPolynomial.coeff_monomial, ite_eq_right]
  intro hcon
  exact hs (Finset.mem_image.mpr ⟨m, hm, hcon⟩)

/-- The support of `homog P d` consists of the monomials corresponding to the support of `P`. -/
lemma homog_support_subset_image (P : MvPolynomial (Fin n) ℤ) :
    (homog (K := K) P d).support ⊆ P.support.image (fun m => Finsupp.cons (d - m.degree) m) := by
  intro s hs
  by_contra h
  exact (MvPolynomial.mem_support_iff.mp hs) (homog_coeff_eq_zero_of_notMem_image (K := K) P h)

/-! ### The support of `P` and the number of monomials -/

/-- `ExpVec n d` is the set of exponent vectors of total degree `≤ d`. -/
lemma toFinsupp_injective {n d : ℕ} :
    Function.Injective (ExpVec.toFinsupp (n := n) (d := d)) := by
  intro a b h
  have h1 : ∀ i, (a.val i : ℕ) = (b.val i : ℕ) := by
    intro i
    have := congrArg (fun f : Fin n →₀ ℕ => f i) h
    simpa [ExpVec.toFinsupp_apply, ExpVec.toFun] using this
  exact Subtype.ext (funext fun i => Fin.ext (h1 i))

/-- A polynomial of total degree `≤ d` has at most `monoCount n d` nonzero coefficients. -/
lemma support_card_le_monoCount (P : MvPolynomial (Fin n) ℤ) (hdeg : P.totalDegree ≤ d) :
    P.support.card ≤ monoCount n d := by
  classical
  have hinj : Function.Injective (ExpVec.toFinsupp (n := n) (d := d)) := toFinsupp_injective
  have hsub : P.support ⊆ (Finset.univ.image (ExpVec.toFinsupp (n := n) (d := d))) := by
    intro m hm
    have hmdeg : m.degree ≤ d := degree_le_of_mem_support P hdeg hm
    have hle : ∀ i : Fin n, m i ≤ d := fun i => (Finsupp.le_degree i m).trans hmdeg
    refine Finset.mem_image.mpr ⟨⟨fun i => ⟨m i, Nat.lt_succ_of_le (hle i)⟩, ?_⟩,
      Finset.mem_univ _, ?_⟩
    · simp only [Fin.val_mk]
      rw [← Finsupp.degree_eq_sum]
      exact hmdeg
    · refine Finsupp.ext fun i => ?_
      simp [ExpVec.toFinsupp_apply, ExpVec.toFun]
  calc P.support.card ≤ (Finset.univ.image (ExpVec.toFinsupp (n := n) (d := d))).card :=
        Finset.card_le_card hsub
    _ = (Finset.univ : Finset (ExpVec n d)).card := Finset.card_image_of_injective _ hinj
    _ = monoCount n d := by rw [Finset.card_univ]; rfl

/-- `monoCount n d` is the cardinality of a nonempty finite type. -/
lemma one_le_monoCount (n d : ℕ) : 1 ≤ monoCount n d := by
  have hne : Nonempty (ExpVec n d) := ⟨⟨fun _ => ⟨0, Nat.succ_pos d⟩, by simp⟩⟩
  have h : 0 < Fintype.card (ExpVec n d) := Fintype.card_pos_iff.mpr hne
  have h2 : 1 ≤ Fintype.card (ExpVec n d) := h
  simpa [monoCount] using h2

/-! ### Coefficients and places -/

/-- At an archimedean place, an integer coefficient of `P` of absolute value `≤ N` has value
`≤ N`. -/
lemma infinitePlace_coeff_le (P : MvPolynomial (Fin n) ℤ) {N : ℕ}
    (hcoef : ∀ m ∈ P.support, |(P.coeff m : ℤ)| ≤ (N : ℤ))
    (v : AbsoluteValue K ℝ) (hv : NumberField.IsInfinitePlace v) {m : Fin n →₀ ℕ}
    (hm : m ∈ P.support) : v (((P.coeff m : ℤ) : K)) ≤ (N : ℝ) := by
  obtain ⟨w, hw⟩ := (NumberField.isInfinitePlace_iff v).mp hv
  have h1 : v (((P.coeff m : ℤ) : K)) = ‖(P.coeff m : ℤ)‖ := by
    rw [← hw]
    exact NumberField.InfinitePlace.map_intCast w (P.coeff m)
  rw [h1, Int.norm_eq_abs, ← Int.cast_abs]
  exact_mod_cast hcoef m hm

/-- The archimedean contribution of `homog P d`: the sum of the values of its coefficients at
an infinite place `v` is bounded by `monoCount n d * N`. -/
lemma homog_arch_sum_le (P : MvPolynomial (Fin n) ℤ) (hdeg : P.totalDegree ≤ d) {N : ℕ}
    (hcoef : ∀ m ∈ P.support, |(P.coeff m : ℤ)| ≤ (N : ℤ))
    (v : AbsoluteValue K ℝ) (hv : NumberField.IsInfinitePlace v) :
    (homog (K := K) P d).coeff.sum (fun _ c => v c)
      ≤ (monoCount n d : ℝ) * (N : ℝ) := by
  rw [MvPolynomial.sum_def]
  calc ∑ s ∈ (homog (K := K) P d).support, v ((homog (K := K) P d).coeff s)
      ≤ ∑ s ∈ P.support.image (fun m => Finsupp.cons (d - m.degree) m),
          v ((homog (K := K) P d).coeff s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (homog_support_subset_image (K := K) P)
          (fun i _ _ => v.nonneg _)
    _ = ∑ m ∈ P.support, v ((homog (K := K) P d).coeff (Finsupp.cons (d - m.degree) m)) :=
        Finset.sum_image (fun x hx y hy hxy => cons_degree_injective
          (degree_le_of_mem_support P hdeg hx) (degree_le_of_mem_support P hdeg hy) hxy)
    _ = ∑ m ∈ P.support, v (((P.coeff m : ℤ) : K)) :=
        Finset.sum_congr rfl (fun m hm => by rw [homog_coeff_cons (K := K) P hdeg hm])
    _ ≤ ∑ _m ∈ P.support, (N : ℝ) :=
        Finset.sum_le_sum (fun m hm => infinitePlace_coeff_le P hcoef v hv hm)
    _ = (P.support.card : ℝ) * (N : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (monoCount n d : ℝ) * (N : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg N)
        exact_mod_cast support_card_le_monoCount P hdeg

/-- The archimedean contribution of the monomial `X₀ ^ d`: its only coefficient is `1`. -/
lemma Xpow_coeff_sum_eq (v : AbsoluteValue K ℝ) :
    (MvPolynomial.X (0 : Fin (n + 1)) ^ d : MvPolynomial (Fin (n + 1)) K).coeff.sum
        (fun _ c => v c) = 1 := by
  rw [MvPolynomial.sum_def, MvPolynomial.support_X_pow, Finset.sum_singleton,
    MvPolynomial.coeff_X_pow]
  simp

/-- At a nonarchimedean place, every coefficient of `homog P d` — being an integer cast — has
value `≤ 1`. -/
lemma nonarch_coeff_homog_le [NumberField K] (P : MvPolynomial (Fin n) ℤ)
    (hdeg : P.totalDegree ≤ d)
    (v : AbsoluteValue K ℝ) (hv : v ∈ Height.AdmissibleAbsValues.nonarchAbsVal (K := K))
    {s : Fin (n + 1) →₀ ℕ} (hs : s ∈ (homog (K := K) P d).support) :
    v ((homog (K := K) P d).coeff s) ≤ 1 := by
  obtain ⟨m, hm, hms⟩ := Finset.mem_image.mp (homog_support_subset_image (K := K) P hs)
  have hcoe : (homog (K := K) P d).coeff s = ((P.coeff m : ℤ) : K) := by
    rw [← hms]; exact homog_coeff_cons (K := K) P hdeg hm
  rw [hcoe]
  exact IsNonarchimedean.apply_intCast_le_one (f := fun x : K => v x) (by simp) (by simp)
    (fun a => v.map_neg a) (Height.AdmissibleAbsValues.isNonarchimedean v hv)

/-- `homog P d` has all coefficients of nonarchimedean value `≤ 1`. -/
lemma nonarch_iSup_coeff_homog_le [NumberField K] (P : MvPolynomial (Fin n) ℤ)
    (hdeg : P.totalDegree ≤ d)
    (v : AbsoluteValue K ℝ) (hv : v ∈ Height.AdmissibleAbsValues.nonarchAbsVal (K := K)) :
    (⨆ s : ↥((homog (K := K) P d).support), v ((homog (K := K) P d).coeff s)) ≤ 1 := by
  rcases isEmpty_or_nonempty ↥((homog (K := K) P d).support) with h | h
  · haveI := h
    rw [Real.iSup_of_isEmpty]
    norm_num
  · haveI := h
    exact ciSup_le fun s => nonarch_coeff_homog_le P hdeg v hv s.property

/-- `X₀ ^ d` has all coefficients of nonarchimedean value `≤ 1`. -/
lemma nonarch_iSup_coeff_Xpow_le [NumberField K] (v : AbsoluteValue K ℝ)
    (_hv : v ∈ Height.AdmissibleAbsValues.nonarchAbsVal (K := K)) :
    (⨆ s : ↥((MvPolynomial.X (0 : Fin (n + 1)) ^ d :
        MvPolynomial (Fin (n + 1)) K).support),
      v ((MvPolynomial.X (0 : Fin (n + 1)) ^ d : MvPolynomial (Fin (n + 1)) K).coeff s)) ≤ 1 := by
  rcases isEmpty_or_nonempty ↥((MvPolynomial.X (0 : Fin (n + 1)) ^ d :
      MvPolynomial (Fin (n + 1)) K).support) with h | h
  · haveI := h
    rw [Real.iSup_of_isEmpty]
    norm_num
  · haveI := h
    refine ciSup_le fun s => ?_
    have hs : s.val = Finsupp.single (0 : Fin (n + 1)) d := by
      simpa [MvPolynomial.support_X_pow] using s.property
    rw [hs, MvPolynomial.coeff_X_pow]
    simp

/-! ### The family `homogFamily` -/

@[simp] lemma homogFamily_apply_zero (P : MvPolynomial (Fin n) ℤ) :
    homogFamily (K := K) P d 0 = homog (K := K) P d := by
  simp [homogFamily]

@[simp] lemma homogFamily_apply_one (P : MvPolynomial (Fin n) ℤ) :
    homogFamily (K := K) P d 1 = MvPolynomial.X (0 : Fin (n + 1)) ^ d := by
  simp [homogFamily]

/-! ### Sups and products indexed by `Fin 2` -/

lemma bddAbove_range_fin_two (f : Fin 2 → ℝ) : BddAbove (Set.range f) :=
  ⟨max (f 0) (f 1), by
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _⟩

lemma iSup_fin_two_eq_max (f : Fin 2 → ℝ) : (⨆ j, f j) = max (f 0) (f 1) := by
  have hbdd := bddAbove_range_fin_two f
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun j => ?_
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_ciSup_of_le hbdd 0 le_rfl) (le_ciSup_of_le hbdd 1 le_rfl)

/-! ### Multiset products of nonnegative real numbers -/

lemma multiset_prod_le_pow_card_of_nonneg (s : Multiset ℝ) {B : ℝ} (hB : 0 ≤ B) :
    (∀ x ∈ s, 0 ≤ x) → (∀ x ∈ s, x ≤ B) → s.prod ≤ B ^ s.card :=
  Multiset.induction_on s (by simp)
    (fun a s ih h0 h1 => by
      rw [Multiset.prod_cons, Multiset.card_cons]
      have ha : a ≤ B := h1 a (Multiset.mem_cons_self a s)
      have hs0 : ∀ x ∈ s, 0 ≤ x := fun x hx => h0 x (Multiset.mem_cons_of_mem hx)
      have hs1 : ∀ x ∈ s, x ≤ B := fun x hx => h1 x (Multiset.mem_cons_of_mem hx)
      have hsp : 0 ≤ s.prod := Multiset.prod_nonneg hs0
      calc a * s.prod ≤ B * s.prod := mul_le_mul_of_nonneg_right ha hsp
        _ ≤ B * B ^ s.card := mul_le_mul_of_nonneg_left (ih hs0 hs1) hB
        _ = B ^ (s.card + 1) := by rw [pow_succ]; ring)

/-! ### The place-by-place bound for `mulHeightBound` -/

/-- If a family of polynomials has bounded archimedean coefficient sums (by `B ≥ 1`) and all
nonarchimedean coefficient sups equal to `1`, then `mulHeightBound` is bounded by
`B ^ totalWeight K`. -/
lemma mulHeightBound_le_of {K : Type*} [Field K] [Height.AdmissibleAbsValues K]
    {ι ι' : Type*} [Finite ι'] {p : ι' → MvPolynomial ι K} {B : ℝ} (hB : 1 ≤ B)
    (harchnn : ∀ v ∈ Height.AdmissibleAbsValues.archAbsVal (K := K),
      0 ≤ (⨆ j, (p j).coeff.sum (fun _ c => v c)))
    (harch : ∀ v ∈ Height.AdmissibleAbsValues.archAbsVal (K := K),
      (⨆ j, (p j).coeff.sum (fun _ c => v c)) ≤ B)
    (hnon : ∀ v ∈ Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
      (⨆ j, max (⨆ s : (p j).support, v ((p j).coeff s)) 1) = 1) :
    max (Height.mulHeightBound p) 1 ≤ B ^ Height.totalWeight K := by
  have hfin : (∏ᶠ v : ↥(Height.AdmissibleAbsValues.nonarchAbsVal (K := K)),
      (⨆ j, max (⨆ s : (p j).support, (v : AbsoluteValue K ℝ) ((p j).coeff s)) 1)) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => hnon v v.property
  refine max_le ?_ (one_le_pow₀ hB)
  rw [Height.mulHeightBound_eq, hfin, mul_one]
  refine (multiset_prod_le_pow_card_of_nonneg _ (le_trans zero_le_one hB)
    (fun x hx => by obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hx; exact harchnn v hv)
    (fun x hx => by obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hx; exact harch v hv)).trans_eq ?_
  rw [Multiset.card_map]
  rfl

end HomogHeightAux

open HomogHeightAux

theorem mulHeightBound_homogFamily_le {K : Type*} [Field K] [NumberField K] {n d N : ℕ}
    (hN : 1 ≤ N) (P : MvPolynomial (Fin n) ℤ) (hdeg : P.totalDegree ≤ d)
    (hcoef : ∀ m ∈ P.support, |(P.coeff m : ℤ)| ≤ (N : ℤ)) :
    max (Height.mulHeightBound (Work.WilkiesH.NT.homogFamily (K := K) P d)) 1
      ≤ ((Work.WilkiesH.monoCount n d : ℝ) * (N : ℝ)) ^ Module.finrank ℚ K := by
  classical
  have hB1 : (1 : ℝ) ≤ (Work.WilkiesH.monoCount n d : ℝ) * (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ (Work.WilkiesH.monoCount n d : ℝ) := by
      exact_mod_cast one_le_monoCount n d
    have h2 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  refine (mulHeightBound_le_of (K := K) (p := Work.WilkiesH.NT.homogFamily (K := K) P d)
    (B := (Work.WilkiesH.monoCount n d : ℝ) * (N : ℝ)) hB1 ?_ ?_ ?_).trans (le_of_eq ?_)
  · -- the archimedean sums are nonnegative
    intro v _
    rw [iSup_fin_two_eq_max]
    refine le_trans ?_ (le_max_left _ _)
    rw [homogFamily_apply_zero, MvPolynomial.sum_def]
    exact Finset.sum_nonneg fun m _ => v.nonneg _
  · -- the archimedean sums are bounded by `monoCount n d * N`
    intro v hv
    have hvi : NumberField.IsInfinitePlace v := NumberField.mem_multisetInfinitePlace.mp hv
    rw [iSup_fin_two_eq_max]
    exact max_le (by rw [homogFamily_apply_zero]; exact homog_arch_sum_le P hdeg hcoef v hvi)
      (by rw [homogFamily_apply_one, Xpow_coeff_sum_eq]; exact hB1)
  · -- the nonarchimedean sups are exactly `1`
    intro v hv
    have hg0 : max (⨆ s : ↥((homogFamily (K := K) P d 0).support),
        v ((homogFamily (K := K) P d 0).coeff s)) 1 ≤ 1 := by
      rw [homogFamily_apply_zero]
      exact max_le (nonarch_iSup_coeff_homog_le P hdeg v hv) le_rfl
    have hg1 : max (⨆ s : ↥((homogFamily (K := K) P d 1).support),
        v ((homogFamily (K := K) P d 1).coeff s)) 1 ≤ 1 := by
      rw [homogFamily_apply_one]
      exact max_le (nonarch_iSup_coeff_Xpow_le (n := n) (d := d) v hv) le_rfl
    refine le_antisymm ?_ ?_
    · rw [iSup_fin_two_eq_max]
      exact max_le hg0 hg1
    · refine le_trans (le_max_right _ 1)
        (le_ciSup_of_le (bddAbove_range_fin_two _) 1 le_rfl)
  · -- the number of archimedean places is the degree of `K` over `ℚ`
    rw [NumberField.totalWeight_eq_finrank]

end Work.WilkiesH.NT
