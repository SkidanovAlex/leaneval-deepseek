import Mathlib
import Submission.Work.RatHurewicz.pushDefs

/-!
# The push of a face of the model away from its centroid

For a point `x` of a standard simplex whose support has `k+1` elements and which is not the
centroid of its support, `collapsePt k x` is the point obtained by collapsing the smallest
barycentric coordinate of `x` to `0` and renormalising:

`collapsePt k x i = (x i - m) / (1 - (k+1) m)` for `i` in the support (`m = suppMin x`), and `0`
outside.  It lies in the closed face of the support, its support is a proper subset of the support
of `x`, and it agrees with `x` on the boundary of the face.

`pushPt k u x = (1-u) • x + u • collapsePt k x` interpolates from `x` to the collapse; the
collapse and the push are compatible with the face maps `facept p = stdSimplex.map p.succAbove`,
which is what makes them descend to the cycle model `Model D`.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## The collapse of the smallest coordinate -/

/-- The coordinate formula of the collapse (with the convention `x/0 = 0`; the denominator
vanishes exactly for the centroid of a `(k+1)`-support). -/
def collapseFun {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m)) (i : Fin m) : ℝ :=
  if i ∈ supp x then ((x : Fin m → ℝ) i - suppMin x) / (1 - ((k : ℝ) + 1) * suppMin x) else 0

/-- `collapseFun` is nonnegative when the support has `k+1` elements. -/
theorem collapseFun_nonneg {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m))
    (hcard : (supp x).card = k + 1) (i : Fin m) : 0 ≤ collapseFun k x i := by
  unfold collapseFun
  by_cases hi : i ∈ supp x
  · rw [if_pos hi]
    exact div_nonneg (by linarith [suppMin_le x hi]) (one_sub_suppMin_nonneg k x hcard)
  · rw [if_neg hi]

/-- The sum of the coordinates of `collapseFun` is `1` when the support has `k+1` elements and the
denominator does not vanish. -/
theorem sum_collapseFun {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m))
    (hcard : (supp x).card = k + 1) (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0) :
    ∑ i, collapseFun k x i = 1 := by
  have hcard' : ((supp x).card : ℝ) = (k : ℝ) + 1 := by rw [hcard]; push_cast; ring
  rw [← Finset.sum_subset (Finset.subset_univ (supp x))]
  · have hsplit : ∑ i ∈ supp x, collapseFun k x i
        = (∑ i ∈ supp x, ((x : Fin m → ℝ) i - suppMin x)) / (1 - ((k : ℝ) + 1) * suppMin x) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun i hi => by rw [collapseFun, if_pos hi])
    have hnum : (∑ i ∈ supp x, ((x : Fin m → ℝ) i - suppMin x))
        = 1 - ((k : ℝ) + 1) * suppMin x := by
      rw [Finset.sum_sub_distrib, sum_supp, Finset.sum_const]
      simp only [nsmul_eq_mul]
      rw [hcard']
    rw [hsplit, hnum, div_eq_iff hden]
    ring
  · intro i _ hi
    rw [collapseFun, if_neg hi]

/-- **The collapse of an open `(k+1)`-cell point**: the smallest coordinate on the support becomes
`0`. -/
def collapsePt {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m)) (hcard : (supp x).card = k + 1)
    (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0) : stdSimplex ℝ (Fin m) :=
  ⟨collapseFun k x, collapseFun_nonneg k x hcard,
    by rw [sum_collapseFun k x hcard hden]⟩

theorem collapsePt_coe {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m))
    (hcard : (supp x).card = k + 1) (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0) :
    ((collapsePt k x hcard hden : stdSimplex ℝ (Fin m)) : Fin m → ℝ) = collapseFun k x := rfl

/-- The support of the collapsed point is contained in the support of the point. -/
theorem supp_collapsePt_subset {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m))
    (hcard : (supp x).card = k + 1) (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0) :
    supp (collapsePt k x hcard hden) ⊆ supp x := by
  intro i hi
  by_contra hx
  have hzero : collapseFun k x i = 0 := by rw [collapseFun, if_neg hx]
  exact (mem_supp.mp hi) hzero

/-- **The collapse strictly decreases the support.** -/
theorem supp_collapsePt_ssubset {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m))
    (hcard : (supp x).card = k + 1) (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0)
    {i : Fin m} (hi : i ∈ supp x) (hmin : suppMin x = (x : Fin m → ℝ) i) :
    supp (collapsePt k x hcard hden) ⊂ supp x := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨supp_collapsePt_subset k x hcard hden, ?_⟩
  intro hc
  have : i ∈ supp (collapsePt k x hcard hden) := hc ▸ hi
  have hval : collapseFun k x i ≠ 0 := mem_supp.mp this
  rw [collapseFun, if_pos hi] at hval
  have hnum : (x : Fin m → ℝ) i - suppMin x = 0 := by rw [hmin]; ring
  rw [hnum, zero_div] at hval
  exact hval rfl

/-- At the end of the homotopy the weight drops: the collapse of an open-cell point lands on the
boundary of the cell. -/
theorem weight_collapsePt_lt {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m))
    (hcard : (supp x).card = k + 1) (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0) :
    (supp (collapsePt k x hcard hden)).card < k + 1 := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (supp_nonempty x)
    (fun i => (x : Fin m → ℝ) i)
  have hminj : suppMin x = (x : Fin m → ℝ) j := hjeq
  have hss : supp (collapsePt k x hcard hden) ⊂ supp x :=
    supp_collapsePt_ssubset k x hcard hden hj hminj
  have hlt := Finset.card_lt_card hss
  rw [hcard] at hlt
  exact hlt

/-! ## The push homotopy -/

/-- **The push of the open cell**: the straight-line interpolation between `x` and its collapse. -/
def pushPt {m : ℕ} (k : ℕ) (u : I) (x : stdSimplex ℝ (Fin m)) (hcard : (supp x).card = k + 1)
    (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0) : stdSimplex ℝ (Fin m) :=
  ⟨(1 - (u : ℝ)) • (x : Fin m → ℝ)
      + (u : ℝ) • ((collapsePt k x hcard hden : stdSimplex ℝ (Fin m)) : Fin m → ℝ),
    convex_stdSimplex ℝ (Fin m) x.2 (collapsePt k x hcard hden).2
      (by linarith [u.2.2]) u.2.1 (by ring)⟩

theorem pushPt_coe {m : ℕ} (k : ℕ) (u : I) (x : stdSimplex ℝ (Fin m))
    (hcard : (supp x).card = k + 1) (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0) :
    ((pushPt k u x hcard hden : stdSimplex ℝ (Fin m)) : Fin m → ℝ)
      = (1 - (u : ℝ)) • (x : Fin m → ℝ) + (u : ℝ) • (collapseFun k x) := rfl

@[simp] theorem pushPt_zero {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m))
    (hcard : (supp x).card = k + 1) (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0) :
    pushPt k 0 x hcard hden = x := by
  ext i
  rw [pushPt_coe]
  simp

@[simp] theorem pushPt_one {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m))
    (hcard : (supp x).card = k + 1) (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0) :
    pushPt k 1 x hcard hden = collapsePt k x hcard hden := by
  ext i
  rw [pushPt_coe, collapsePt_coe]
  simp

/-- For `u < 1` the push does not change the support. -/
theorem supp_pushPt_of_lt {m : ℕ} (k : ℕ) {u : I} (hu : (u : ℝ) < 1)
    (x : stdSimplex ℝ (Fin m)) (hcard : (supp x).card = k + 1)
    (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0) :
    supp (pushPt k u x hcard hden) = supp x := by
  ext i
  have hkey : ((pushPt k u x hcard hden : stdSimplex ℝ (Fin m)) : Fin m → ℝ) i
      = (1 - (u : ℝ)) * (x : Fin m → ℝ) i + (u : ℝ) * collapseFun k x i := rfl
  rw [mem_supp, mem_supp, hkey]
  constructor
  · intro h
    by_contra hxi
    have hx0 : (x : Fin m → ℝ) i = 0 := by simpa using hxi
    have hc0 : collapseFun k x i = 0 := by
      have hnot : ¬ (i ∈ supp x) := fun h => (mem_supp.mp h) hxi
      rw [collapseFun, if_neg hnot]
    rw [hx0, hc0] at h
    simp at h
  · intro hi
    have hxpos : 0 < (x : Fin m → ℝ) i := lt_of_le_of_ne (x.2.1 i) (Ne.symm hi)
    have hcnonneg : 0 ≤ collapseFun k x i := collapseFun_nonneg k x hcard i
    have h1 : 0 < (1 - (u : ℝ)) * (x : Fin m → ℝ) i := mul_pos (by linarith) hxpos
    have h2 : 0 ≤ (u : ℝ) * collapseFun k x i := mul_nonneg u.2.1 hcnonneg
    linarith

theorem weight_pushPt_one_lt {m : ℕ} (k : ℕ) (x : stdSimplex ℝ (Fin m))
    (hcard : (supp x).card = k + 1) (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0) :
    (supp (pushPt k 1 x hcard hden)).card < k + 1 := by
  rw [pushPt_one]
  exact weight_collapsePt_lt k x hcard hden

end
end Work.RatHurewicz

namespace Work.RatHurewicz
noncomputable section
variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## Compatibility with the face maps

The face map `facept t p = stdSimplex.map p.succAbove` sends the standard `t`-simplex onto the
`p`-th face of the standard `(t+1)`-simplex by pushing the barycentric coordinates forward.  Since
`p.succAbove` is injective and strictly monotone, the support of the image is the image of the
support, the coordinates are preserved, and hence the smallest coordinate is preserved; therefore
the collapse and the push commute with `facept`.
-/

theorem supp_facept {t : ℕ} (p : Fin (t + 1)) (z : stdSimplex ℝ (Fin t)) :
    supp (facept t p z) = (supp z).image p.succAbove :=
  supp_map_of_injective (Fin.succAbove_right_injective) z

theorem mem_supp_facept {t : ℕ} (p : Fin (t + 1)) (z : stdSimplex ℝ (Fin t))
    {i : Fin t} : p.succAbove i ∈ supp (facept t p z) ↔ i ∈ supp z := by
  rw [supp_facept, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    rw [Fin.succAbove_right_injective hji] at hj
    exact hj
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- **The coordinate formula for a face map**: the `j`-th coordinate of `facept t p w` is the sum of
the coordinates of `w` over the (at most one) preimage of `j` under `p.succAbove`. -/
theorem facept_apply_funext {t : ℕ} (p : Fin (t + 1)) (w : stdSimplex ℝ (Fin t)) :
    ((facept t p w : stdSimplex ℝ (Fin (t + 1))) : Fin (t + 1) → ℝ)
      = fun j => ∑ x ∈ Finset.univ.filter (fun x : Fin t => p.succAbove x = j),
          (w : Fin t → ℝ) x := by
  funext j
  exact ptSup_facept_apply p w j

theorem facept_apply_succAbove {t : ℕ} (p : Fin (t + 1)) (z : stdSimplex ℝ (Fin t))
    (i : Fin t) :
    ((facept t p z : stdSimplex ℝ (Fin (t + 1))) : Fin (t + 1) → ℝ) (p.succAbove i)
      = (z : Fin t → ℝ) i := by
  rw [facept_apply_funext]
  show (∑ x ∈ Finset.univ.filter (fun j : Fin t => p.succAbove j = p.succAbove i),
      (z : Fin t → ℝ) x) = (z : Fin t → ℝ) i
  have hfilter : Finset.univ.filter (fun j : Fin t => p.succAbove j = p.succAbove i) = {i} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hb => Fin.succAbove_right_injective hb, fun hb => by rw [hb]⟩
  rw [hfilter, Finset.sum_singleton]

/-- The sum over the preimages under `p.succAbove` of a vertex: at most one term. -/
theorem sum_facept_filter {t : ℕ} (p : Fin (t + 1)) (j : Fin (t + 1)) (w : Fin t → ℝ) :
    (∑ x ∈ Finset.univ.filter (fun x : Fin t => p.succAbove x = j), w x)
      = if h : ∃ i, p.succAbove i = j then w (Classical.choose h) else 0 := by
  by_cases h : ∃ i, p.succAbove i = j
  · have hf : Finset.univ.filter (fun x : Fin t => p.succAbove x = j)
        = {Classical.choose h} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hb => Fin.succAbove_right_injective (hb.trans (Classical.choose_spec h).symm),
        fun hb => hb ▸ Classical.choose_spec h⟩
    rw [hf, Finset.sum_singleton, dif_pos h]
  · have hempty : Finset.univ.filter (fun x : Fin t => p.succAbove x = j) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨x, hx⟩
      exact h ⟨x, (Finset.mem_filter.mp hx).2⟩
    rw [hempty, Finset.sum_empty, dif_neg h]

/-- The face map preserves the smallest coordinate. -/
theorem suppMin_facept {t : ℕ} (p : Fin (t + 1)) (z : stdSimplex ℝ (Fin t)) :
    suppMin (facept t p z) = suppMin z := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_inf' (supp_nonempty z) (fun i => (z : Fin t → ℝ) i)
    have hminz : suppMin z = (z : Fin t → ℝ) i := hieq
    have hle := suppMin_le (facept t p z) ((mem_supp_facept p z).mpr hi)
    rw [facept_apply_succAbove] at hle
    rwa [hminz]
  · refine Finset.le_inf' (supp_nonempty (facept t p z))
      (fun j => (facept t p z : stdSimplex ℝ (Fin (t + 1))) j) ?_
    intro j hj
    obtain ⟨i, hi, hji⟩ := Finset.mem_image.mp (supp_facept p z ▸ hj)
    rw [← hji, facept_apply_succAbove]
    exact suppMin_le z hi

theorem collapseFun_facept {t : ℕ} (k : ℕ) (p : Fin (t + 1)) (z : stdSimplex ℝ (Fin t))
    (i : Fin t) : collapseFun k (facept t p z) (p.succAbove i) = collapseFun k z i := by
  rw [collapseFun, collapseFun, suppMin_facept p z]
  by_cases hi : i ∈ supp z
  · rw [if_pos ((mem_supp_facept p z).mpr hi), if_pos hi, facept_apply_succAbove]
  · rw [if_neg (fun h => hi ((mem_supp_facept p z).mp h)), if_neg hi]

/-- Outside the image of the face map the collapse of a face point vanishes. -/
theorem collapseFun_facept_notMem {t : ℕ} (k : ℕ) (p : Fin (t + 1)) (z : stdSimplex ℝ (Fin t))
    {j : Fin (t + 1)} (h : ¬ ∃ i, p.succAbove i = j) :
    collapseFun k (facept t p z) j = 0 := by
  have hnot : ¬ (j ∈ supp (facept t p z)) := by
    intro hj
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (supp_facept p z ▸ hj)
    exact h ⟨i, hi⟩
  rw [collapseFun, if_neg hnot]

/-- Outside the image of the face map the coordinates of a face point vanish. -/
theorem facept_apply_notMem {t : ℕ} (p : Fin (t + 1)) (w : stdSimplex ℝ (Fin t))
    {j : Fin (t + 1)} (h : ¬ ∃ i, p.succAbove i = j) :
    ((facept t p w : stdSimplex ℝ (Fin (t + 1))) : Fin (t + 1) → ℝ) j = 0 := by
  rw [facept_apply_funext]
  simp only []
  rw [sum_facept_filter, dif_neg h]

/-- The collapse commutes with the face maps. -/
theorem collapsePt_facept {t : ℕ} (k : ℕ) (p : Fin (t + 1)) (z : stdSimplex ℝ (Fin t))
    (hcard : (supp (facept t p z)).card = k + 1)
    (hden : 1 - ((k : ℝ) + 1) * suppMin (facept t p z) ≠ 0)
    (hcard' : (supp z).card = k + 1) (hden' : 1 - ((k : ℝ) + 1) * suppMin z ≠ 0) :
    collapsePt k (facept t p z) hcard hden = facept t p (collapsePt k z hcard' hden') := by
  apply Subtype.ext
  funext j
  change collapseFun k (facept t p z) j = (facept t p (collapsePt k z hcard' hden')) j
  rw [facept_apply_funext]
  simp only []
  rw [sum_facept_filter]
  by_cases h : ∃ i, p.succAbove i = j
  · have hcopy := h
    obtain ⟨i, hi⟩ := hcopy
    rw [dif_pos h]
    have hchoose : Classical.choose h = i := by
      apply Fin.succAbove_right_injective
      rw [Classical.choose_spec h, hi]
    rw [hchoose, show j = p.succAbove i from hi.symm]
    exact collapseFun_facept k p z i
  · rw [dif_neg h, collapseFun_facept_notMem k p z h]

/-- The push commutes with the face maps. -/
theorem pushPt_facept {t : ℕ} (k : ℕ) (u : I) (p : Fin (t + 1)) (z : stdSimplex ℝ (Fin t))
    (hcard : (supp (facept t p z)).card = k + 1)
    (hden : 1 - ((k : ℝ) + 1) * suppMin (facept t p z) ≠ 0)
    (hcard' : (supp z).card = k + 1) (hden' : 1 - ((k : ℝ) + 1) * suppMin z ≠ 0) :
    pushPt k u (facept t p z) hcard hden = facept t p (pushPt k u z hcard' hden') := by
  apply Subtype.ext
  funext j
  change (1 - (u : ℝ)) * ((facept t p z : stdSimplex ℝ (Fin (t + 1))) : Fin (t + 1) → ℝ) j
      + (u : ℝ) * collapseFun k (facept t p z) j
    = (facept t p (pushPt k u z hcard' hden')) j
  rw [facept_apply_funext]
  simp only []
  rw [sum_facept_filter]
  by_cases h : ∃ i, p.succAbove i = j
  · have hcopy := h
    obtain ⟨i, hi⟩ := hcopy
    rw [dif_pos h]
    have hchoose : Classical.choose h = i := by
      apply Fin.succAbove_right_injective
      rw [Classical.choose_spec h, hi]
    rw [hchoose, show j = p.succAbove i from hi.symm]
    rw [facept_apply_succAbove, collapseFun_facept]
    rfl
  · rw [dif_neg h]
    have h1 : collapseFun k (facept t p z) j = 0 := collapseFun_facept_notMem k p z h
    have h2 : ((facept t p z : stdSimplex ℝ (Fin (t + 1))) : Fin (t + 1) → ℝ) j = 0 :=
      facept_apply_notMem p z h
    have h3 : (facept t p (pushPt k u z hcard' hden')) j = 0 :=
      facept_apply_notMem p _ h
    simp only [h3, h1, h2]
    ring

end
end Work.RatHurewicz
