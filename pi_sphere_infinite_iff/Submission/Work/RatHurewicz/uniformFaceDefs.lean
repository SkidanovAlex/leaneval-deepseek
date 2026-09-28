import Mathlib
import Submission.Work.RatHurewicz.skelPushDefs
import Submission.Work.RatHurewicz.pushDefs
import Submission.Work.RatHurewicz.pushModel

/-!
# The uniform push of the model: face vocabulary

This module fixes the vocabulary of the *uniform* (cell-independent) push of the `k`-skeleton of
`Work.RatHurewicz.Model D` off its `k`-cells, the route to `Work.RatHurewicz.pushRawUniform`.

The push of a raw point `Sum.inl ⟨j, x⟩` of weight `k+1` (an interior point of a `k`-cell, i.e.
`(supp x).card = k + 1`) is the radial projection of the closed face spanned by `supp x` off the
centroid of that face.  To make this push *continuous at the boundary of the face* (where the
weight drops, and where the push must agree with the identity), the formula is written with the
minimum over a **fixed** finite set `S` of vertices (`faceMin S hS x`), not with the minimum over
the support: at a point of the face whose support is a *proper* subset of `S`, that minimum is `0`
and the formula reduces to the identity.

* `faceSet S` is the closed face spanned by `S`;
* `faceMin S hS x` is the smallest coordinate of `x` over `S`;
* `faceDen k S hS x = 1 - (k+1) * faceMin S hS x` is the denominator of the radial projection;
* `faceVec k S hS u x` is the pushed point, as a function `Fin m → ℝ`;
* `facePt k S hS u x hcard hx hden` is the pushed point, as a point of the simplex.

We also define the "unfolding" maps `rawUnInl`, `rawSimplex` of the raw space, which extract the
simplex coordinate of a raw point.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

namespace SkelPush

noncomputable section

variable {m : ℕ}

/-! ## The closed face spanned by a finite set of vertices -/

/-- **The closed face spanned by `S`**: the points whose support is contained in `S`. -/
def faceSet (S : Finset (Fin m)) : Set (stdSimplex ℝ (Fin m)) :=
  {x | supp x ⊆ S}

theorem mem_faceSet {S : Finset (Fin m)} {x : stdSimplex ℝ (Fin m)} :
    x ∈ faceSet S ↔ supp x ⊆ S := Iff.rfl

/-- **The closed face is closed** (the coordinates outside `S` vanish). -/
theorem isClosed_faceSet (S : Finset (Fin m)) : IsClosed (faceSet S) := by
  have h : faceSet S = ⋂ i : Fin m, (fun x : stdSimplex ℝ (Fin m) => (x : Fin m → ℝ) i) ⁻¹'
      (if i ∈ S then Set.univ else ({0} : Set ℝ)) := by
    ext x
    simp only [faceSet, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · simp [hi]
      · simp only [hi, if_false, Set.mem_singleton_iff]
        by_contra hne
        exact hi (h (mem_supp.mpr hne))
    · intro h i hi
      by_contra hne
      have := h i
      rw [if_neg hne] at this
      exact (mem_supp.mp hi) this
  rw [h]
  refine isClosed_iInter fun i => ?_
  by_cases hi : i ∈ S
  · rw [if_pos hi]; exact isClosed_univ
  · rw [if_neg hi]
    exact isClosed_singleton.preimage
      ((continuous_apply (A := fun _ : Fin m => ℝ) i).comp continuous_subtype_val)

theorem sum_of_faceSet {S : Finset (Fin m)} {x : stdSimplex ℝ (Fin m)} (hx : x ∈ faceSet S) :
    ∑ i ∈ S, (x : Fin m → ℝ) i = 1 := by
  have h : ∑ i ∈ S, (x : Fin m → ℝ) i = ∑ i, (x : Fin m → ℝ) i :=
    Finset.sum_subset (Finset.subset_univ S) fun i _ hi => by
      by_contra hne
      exact hi (hx (mem_supp.mpr hne))
  rw [h]
  exact stdSimplex.sum_eq_one x

/-! ## The minimum of the coordinates over a face -/

/-- **The smallest barycentric coordinate over `S`.** -/
def faceMin (S : Finset (Fin m)) (hS : S.Nonempty) (x : stdSimplex ℝ (Fin m)) : ℝ :=
  S.inf' hS fun i => (x : Fin m → ℝ) i

theorem faceMin_le {S : Finset (Fin m)} (hS : S.Nonempty) (x : stdSimplex ℝ (Fin m))
    {i : Fin m} (hi : i ∈ S) : faceMin S hS x ≤ (x : Fin m → ℝ) i :=
  (Finset.inf'_le_iff hS).mpr ⟨i, hi, le_refl _⟩

theorem faceMin_nonneg {S : Finset (Fin m)} (hS : S.Nonempty) (x : stdSimplex ℝ (Fin m)) :
    0 ≤ faceMin S hS x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' hS fun i => (x : Fin m → ℝ) i
  rw [faceMin, hi]
  exact x.2.1 i

theorem faceMin_eq_of_min {S : Finset (Fin m)} (hS : S.Nonempty) {x : stdSimplex ℝ (Fin m)}
    {i : Fin m} (hi : i ∈ S) (hmin : ∀ j ∈ S, (x : Fin m → ℝ) i ≤ (x : Fin m → ℝ) j) :
    faceMin S hS x = (x : Fin m → ℝ) i :=
  le_antisymm (faceMin_le hS x hi)
    ((Finset.le_inf'_iff hS (fun j => (x : Fin m → ℝ) j)).mpr hmin)

/-- The minimum over a face of cardinality `k+1` is at most `1/(k+1)`. -/
theorem faceMin_mul_card_le {S : Finset (Fin m)} (hS : S.Nonempty) {x : stdSimplex ℝ (Fin m)}
    (hx : x ∈ faceSet S) : ((S.card : ℝ)) * faceMin S hS x ≤ 1 := by
  have h : ∑ _i ∈ S, faceMin S hS x ≤ ∑ i ∈ S, (x : Fin m → ℝ) i :=
    Finset.sum_le_sum fun i hi => faceMin_le hS x hi
  rw [Finset.sum_const, nsmul_eq_mul, sum_of_faceSet hx] at h
  linarith

theorem faceMin_le_inv {S : Finset (Fin m)} (hS : S.Nonempty) {k : ℕ} (hcard : S.card = k + 1)
    {x : stdSimplex ℝ (Fin m)} (hx : x ∈ faceSet S) :
    faceMin S hS x ≤ ((k : ℝ) + 1)⁻¹ := by
  have hcard' : ((S.card : ℝ)) = (k : ℝ) + 1 := by rw [hcard]; push_cast; ring
  have h := faceMin_mul_card_le hS hx
  rw [hcard'] at h
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [inv_eq_one_div, le_div_iff₀ hpos]
  linarith

theorem one_sub_faceMin_nonneg {S : Finset (Fin m)} (hS : S.Nonempty) {k : ℕ}
    (hcard : S.card = k + 1) {x : stdSimplex ℝ (Fin m)} (hx : x ∈ faceSet S) :
    0 ≤ 1 - ((k : ℝ) + 1) * faceMin S hS x := by
  have h := faceMin_le_inv hS hcard hx
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h (le_of_lt hk), inv_mul_cancel₀ (ne_of_gt hk)]

/-- If the support of `x` is a proper subset of `S`, the minimum over `S` vanishes. -/
theorem faceMin_eq_zero_of_card_lt {S : Finset (Fin m)} (hS : S.Nonempty) {k : ℕ}
    (hcard : S.card = k + 1) {x : stdSimplex ℝ (Fin m)} (hx : x ∈ faceSet S)
    (hlt : (supp x).card ≤ k) : faceMin S hS x = 0 := by
  by_contra hne
  have hpos : 0 < faceMin S hS x := lt_of_le_of_ne (faceMin_nonneg hS x) (Ne.symm hne)
  have hsub : S ⊆ supp x := fun i hi =>
    mem_supp.mpr (ne_of_gt (lt_of_lt_of_le hpos (faceMin_le hS x hi)))
  have hle1 : S.card ≤ (supp x).card := Finset.card_le_card hsub
  have hle2 : (supp x).card ≤ S.card := Finset.card_le_card hx
  rw [hcard] at hle1
  omega

/-- If the support of `x` has the same cardinality as `S`, the two minima agree. -/
theorem faceMin_eq_suppMin {S : Finset (Fin m)} (hS : S.Nonempty) {k : ℕ}
    (hcard : S.card = k + 1) {x : stdSimplex ℝ (Fin m)} (hx : x ∈ faceSet S)
    (heq : (supp x).card = k + 1) : faceMin S hS x = suppMin x := by
  have hsupp : supp x = S := Finset.eq_of_subset_of_card_le hx (by rw [hcard, heq])
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_inf' (supp_nonempty x)
      (fun i => (x : Fin m → ℝ) i)
    exact (faceMin_le hS x (hsupp ▸ hi)).trans_eq hieq.symm
  · obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' hS (fun j => (x : Fin m → ℝ) j)
    exact (suppMin_le x (by rw [hsupp]; exact hj)).trans_eq hjeq.symm

/-- `faceMin` is continuous. -/
theorem continuous_faceMin (S : Finset (Fin m)) (hS : S.Nonempty) :
    Continuous fun x : stdSimplex ℝ (Fin m) => faceMin S hS x := by
  change Continuous fun x : stdSimplex ℝ (Fin m) => S.inf' hS fun i => (x : Fin m → ℝ) i
  exact Continuous.finset_inf'_apply hS
    (fun i _ => (continuous_apply i).comp continuous_subtype_val)

/-! ## The radial projection of a face off its centroid -/

/-- **The denominator** of the radial projection of the face `S`: it vanishes exactly at the
centroid of `S` (when `S.card = k+1`). -/
def faceDen (k : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty) (x : stdSimplex ℝ (Fin m)) : ℝ :=
  1 - ((k : ℝ) + 1) * faceMin S hS x

theorem faceDen_eq (k : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty) (x : stdSimplex ℝ (Fin m)) :
    faceDen k S hS x = 1 - ((k : ℝ) + 1) * faceMin S hS x := rfl

theorem continuous_faceDen (k : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty) :
    Continuous fun x : stdSimplex ℝ (Fin m) => faceDen k S hS x := by
  change Continuous fun x : stdSimplex ℝ (Fin m) =>
    1 - ((k : ℝ) + 1) * faceMin S hS x
  exact continuous_const.sub (continuous_const.mul (continuous_faceMin S hS))

/-- **The pushed coordinates**: the straight-line interpolation between `x` and its radial
projection off the centroid of the face `S`.  Outside `S` the coordinates are merely scaled. -/
def faceVec (k : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty) (u : unitInterval)
    (x : stdSimplex ℝ (Fin m)) : Fin m → ℝ :=
  fun i => (1 - (u : ℝ)) * ((x : Fin m → ℝ) i) +
    (u : ℝ) * (if i ∈ S then (((x : Fin m → ℝ) i) - faceMin S hS x) / faceDen k S hS x else 0)

theorem faceVec_apply (k : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty) (u : unitInterval)
    (x : stdSimplex ℝ (Fin m)) (i : Fin m) :
    faceVec k S hS u x i = (1 - (u : ℝ)) * ((x : Fin m → ℝ) i) +
      (u : ℝ) * (if i ∈ S then (((x : Fin m → ℝ) i) - faceMin S hS x) / faceDen k S hS x
        else 0) := rfl

/-- The sum of the pushed coordinates, where the denominator does not vanish. -/
theorem sum_faceVec (k : ℕ) {S : Finset (Fin m)} (hS : S.Nonempty) (hcard : S.card = k + 1)
    {x : stdSimplex ℝ (Fin m)} (hx : x ∈ faceSet S) (hden : faceDen k S hS x ≠ 0)
    (u : unitInterval) : ∑ i, faceVec k S hS u x i = 1 := by
  have hsumS : ∑ i ∈ S, (x : Fin m → ℝ) i = 1 := sum_of_faceSet hx
  have hcardR : ((S.card : ℝ)) = (k : ℝ) + 1 := by rw [hcard]; push_cast; ring
  have hif : (∑ i, (if i ∈ S then ((x : Fin m → ℝ) i - faceMin S hS x) / faceDen k S hS x
        else 0))
      = ∑ i ∈ S, ((x : Fin m → ℝ) i - faceMin S hS x) / faceDen k S hS x := by
    rw [← Finset.sum_subset (Finset.subset_univ S)
      (f := fun i => if i ∈ S then ((x : Fin m → ℝ) i - faceMin S hS x) / faceDen k S hS x
        else 0)
      (fun i _ hi => if_neg hi)]
    exact Finset.sum_congr rfl fun i hi => if_pos hi
  have hnum : (∑ i ∈ S, ((x : Fin m → ℝ) i - faceMin S hS x))
      = 1 - ((k : ℝ) + 1) * faceMin S hS x := by
    rw [Finset.sum_sub_distrib, hsumS, Finset.sum_const, nsmul_eq_mul, hcardR]
  calc ∑ i, faceVec k S hS u x i
      = ∑ i, ((1 - (u : ℝ)) * (x : Fin m → ℝ) i
          + (u : ℝ) * (if i ∈ S then ((x : Fin m → ℝ) i - faceMin S hS x) / faceDen k S hS x
            else 0)) := Finset.sum_congr rfl fun i _ => faceVec_apply k S hS u x i
    _ = (1 - (u : ℝ)) * (∑ i, (x : Fin m → ℝ) i)
          + (u : ℝ) * (∑ i, (if i ∈ S then ((x : Fin m → ℝ) i - faceMin S hS x)
            / faceDen k S hS x else 0)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = (1 - (u : ℝ)) * 1 + (u : ℝ) * (∑ i ∈ S, ((x : Fin m → ℝ) i - faceMin S hS x)
          / faceDen k S hS x) := by
        rw [hif, stdSimplex.sum_eq_one x]
    _ = (1 - (u : ℝ)) * 1 + (u : ℝ) * ((∑ i ∈ S, ((x : Fin m → ℝ) i - faceMin S hS x))
          / faceDen k S hS x) := by rw [Finset.sum_div]
    _ = (1 - (u : ℝ)) * 1 + (u : ℝ) * ((1 - ((k : ℝ) + 1) * faceMin S hS x)
          / faceDen k S hS x) := by rw [hnum]
    _ = 1 := by
        rw [show (1 - ((k : ℝ) + 1) * faceMin S hS x) = faceDen k S hS x from rfl,
          div_self hden]
        ring

/-- The pushed coordinates are nonnegative. -/
theorem faceVec_nonneg (k : ℕ) {S : Finset (Fin m)} (hS : S.Nonempty) (hcard : S.card = k + 1)
    {x : stdSimplex ℝ (Fin m)} (hx : x ∈ faceSet S) (hden : faceDen k S hS x ≠ 0)
    (u : unitInterval) (i : Fin m) : 0 ≤ faceVec k S hS u x i := by
  have hdenpos : 0 < faceDen k S hS x :=
    lt_of_le_of_ne (one_sub_faceMin_nonneg hS hcard hx) (Ne.symm hden)
  rw [faceVec_apply]
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hnum : 0 ≤ (x : Fin m → ℝ) i - faceMin S hS x :=
      sub_nonneg.mpr (faceMin_le hS x hi)
    have h1 : 0 ≤ (1 - (u : ℝ)) * (x : Fin m → ℝ) i :=
      mul_nonneg (by linarith [u.2.2]) (x.2.1 i)
    have h2 : 0 ≤ (u : ℝ) * (((x : Fin m → ℝ) i - faceMin S hS x) / faceDen k S hS x) :=
      mul_nonneg u.2.1 (div_nonneg hnum (le_of_lt hdenpos))
    linarith
  · rw [if_neg hi]
    have hxi : (x : Fin m → ℝ) i = 0 := by
      by_contra hne
      exact hi (hx (mem_supp.mpr hne))
    rw [hxi]
    simp

/-- **The pushed point of a face**, as a point of the standard simplex. -/
def facePt (k : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty) (u : unitInterval)
    (x : stdSimplex ℝ (Fin m)) (hcard : S.card = k + 1) (hx : x ∈ faceSet S)
    (hden : faceDen k S hS x ≠ 0) : stdSimplex ℝ (Fin m) :=
  ⟨faceVec k S hS u x, faceVec_nonneg k hS hcard hx hden u, sum_faceVec k hS hcard hx hden u⟩

@[simp] theorem facePt_coe (k : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty) (u : unitInterval)
    (x : stdSimplex ℝ (Fin m)) (hcard : S.card = k + 1) (hx : x ∈ faceSet S)
    (hden : faceDen k S hS x ≠ 0) :
    ((facePt k S hS u x hcard hx hden : stdSimplex ℝ (Fin m)) : Fin m → ℝ)
      = faceVec k S hS u x := rfl

/-- At time `0` the face push is the identity. -/
theorem facePt_zero (k : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty) (x : stdSimplex ℝ (Fin m))
    (hcard : S.card = k + 1) (hx : x ∈ faceSet S) (hden : faceDen k S hS x ≠ 0) :
    facePt k S hS 0 x hcard hx hden = x := by
  refine Subtype.ext (funext fun i => ?_)
  change faceVec k S hS 0 x i = (x : Fin m → ℝ) i
  rw [faceVec_apply]
  simp

/-- On the boundary of the face (where the minimum over `S` vanishes) the face push is the
identity. -/
theorem facePt_eq_self_of_faceMin_zero (k : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty)
    {x : stdSimplex ℝ (Fin m)} (hcard : S.card = k + 1) (hx : x ∈ faceSet S)
    (h0 : faceMin S hS x = 0) (hden : faceDen k S hS x ≠ 0) (u : unitInterval) :
    facePt k S hS u x hcard hx hden = x := by
  refine Subtype.ext (funext fun i => ?_)
  change faceVec k S hS u x i = (x : Fin m → ℝ) i
  rw [faceVec_apply]
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hden1 : faceDen k S hS x = 1 := by rw [faceDen_eq, h0]; ring
    rw [h0, hden1]
    ring
  · rw [if_neg hi]
    have hxi : (x : Fin m → ℝ) i = 0 := by
      by_contra hne
      exact hi (hx (mem_supp.mpr hne))
    rw [hxi]
    ring

/-! ## The unfolding map of the raw space -/

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- **The unfolding of the `Sum.inl` half of the raw space**: the identity on the simplices, and a
constant on the arcs. -/
def rawUnInl (D : MData X n x₀) : Raw D → (Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))) :=
  Sum.elim id fun p => ⟨p.1, stdSimplex.vertex (0 : Fin (n + 2))⟩

theorem rawUnInl_inl (D : MData X n x₀) (j : D.Idx) (x : stdSimplex ℝ (Fin (n + 2))) :
    rawUnInl D (Sum.inl ⟨j, x⟩) = ⟨j, x⟩ := rfl

theorem rawUnInl_inr (D : MData X n x₀) (j : D.Idx) (t : unitInterval) :
    rawUnInl D (Sum.inr ⟨j, t⟩) = ⟨j, stdSimplex.vertex (0 : Fin (n + 2))⟩ := rfl

theorem continuous_rawUnInl (D : MData X n x₀) : Continuous (rawUnInl D) := by
  refine Continuous.sumElim continuous_id ?_
  refine continuous_sigma_iff.mpr fun j => ?_
  refine (continuous_const : Continuous fun _ : unitInterval =>
    (⟨j, stdSimplex.vertex (0 : Fin (n + 2))⟩ : Σ _ : D.Idx,
      stdSimplex ℝ (Fin (n + 2)))).congr fun a => ?_
  rfl

/-- **The simplex coordinate of a raw point.** -/
def rawSimplex (D : MData X n x₀) : Raw D → stdSimplex ℝ (Fin (n + 2)) :=
  fun a => (rawUnInl D a).2

theorem rawSimplex_inl (D : MData X n x₀) (j : D.Idx) (x : stdSimplex ℝ (Fin (n + 2))) :
    rawSimplex D (Sum.inl ⟨j, x⟩) = x := rfl

theorem continuous_rawSimplex (D : MData X n x₀) : Continuous (rawSimplex D) := by
  have h : Continuous fun p : (Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))) => p.2 := by
    rw [continuous_sigma_iff]
    intro j
    exact continuous_id
  exact h.comp (continuous_rawUnInl D)

end

end SkelPush

end Work.RatHurewicz
