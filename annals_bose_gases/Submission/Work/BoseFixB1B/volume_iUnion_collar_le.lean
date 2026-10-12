import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.volume_iUnion_collar_le`

The linear **collar bound** used by the sliding localisation: the `δ`-neighbourhood of the
boundary of a cube of half-side `c`, intersected with the cube itself, has volume at most
`24 c² δ`.

Concretely, for `c, δ > 0` and any centre `a`,

    volume (⋃ i : Fin 3, {x | (∀ m, |(x - a) m| ≤ c) ∧ c - |(x - a) i| < δ})
      ≤ ofReal (24 * c ^ 2 * δ) .

The set is the part of the closed cube `a + [-c,c]³` where at least one coordinate satisfies
`|(x - a) i| > c - δ`, i.e. the union of the six face slabs of thickness `δ`.  Each such slab is a
box of side lengths `2c, 2c, δ`, so it has volume `4 c² δ`; the union of the six slabs is bounded
by `6 · 4 c² δ = 24 c² δ`.

Route (all measure theory in Mathlib):

* `volume_coord_face_box_aux` — a coordinate face slab `{y | y i ∈ Icc lo hi ∧ ∀ m ≠ i,
  |y m| ≤ c}` of the cube `[-c,c]³` is a product box whose volume is `(hi - lo) · (2c)²`
  (`Real.volume_Icc`, `MeasureTheory.volume_pi_pi`, transported along the measure preserving
  `WithLp.ofLp`);
* the collar is split, for each coordinate `i`, into its two faces (positive/negative), and the
  six face volumes are summed (`MeasureTheory.measure_iUnion_fintype_le`,
  `MeasureTheory.measure_union_le`); the faces are taken *closed* (`Icc (c-δ) c` and
  `Icc (-c) (-(c-δ))`) so that the points with `|y i| = c` exactly — which do lie in the collar —
  are covered;
* finally the whole configuration is translated by `-a`
  (`MeasureTheory.measure_preimage_add_right`, using add-invariance of Lebesgue measure on
  `EuclideanSpace ℝ (Fin 3)`).

The constant `24 = 3 · 2 · 4` is the crude six-face bound; it is the constant appearing in the
collar estimate of the sliding localisation (`Work.BoseFixB1B.boxMarginDefs`, estimate (F2)).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B

set_option autoImplicit false

/-- **Volume of a coordinate face slab of the cube `[-c,c]³`.**

For `c > 0`, `lo ≤ hi` and a coordinate `i : Fin 3`, the box of points whose `i`-th coordinate lies
in `Icc lo hi` while all other coordinates satisfy `|y m| ≤ c` has volume
`(hi - lo) · (2c)²`: the `Icc` factor contributes `hi - lo` and each of the two remaining
coordinates an interval of length `2c`.

Written in the explicit `WithLp` coordinates of `EuclideanSpace ℝ (Fin 3)`: it is the preimage
under `WithLp.ofLp` of the product set `Set.univ.pi (fun m => if m = i then Icc lo hi else
Icc (-c) c)`, whose measure is computed by `MeasureTheory.volume_pi_pi`. -/
private theorem volume_coord_face_box_aux {c lo hi : ℝ} (hc : 0 < c) (hlohi : lo ≤ hi)
    (i : Fin 3) :
    MeasureTheory.volume ({y : EuclideanSpace ℝ (Fin 3) |
        y i ∈ Set.Icc lo hi ∧ ∀ m : Fin 3, m ≠ i → |y m| ≤ c})
      = ENNReal.ofReal ((hi - lo) * (2 * c) ^ 2) := by
  have hset : {y : EuclideanSpace ℝ (Fin 3) |
        y i ∈ Set.Icc lo hi ∧ ∀ m : Fin 3, m ≠ i → |y m| ≤ c}
      = WithLp.ofLp ⁻¹'
          (Set.univ.pi fun m : Fin 3 => if m = i then Set.Icc lo hi else Set.Icc (-c) c) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · rintro ⟨hi', hrest⟩ m
      by_cases hm : m = i
      · subst hm; simpa using hi'
      · simp only [hm, if_false]; exact abs_le.mp (hrest m hm)
    · intro h
      exact ⟨by simpa using h i, fun m hm => abs_le.mpr (by simpa [hm] using h m)⟩
  rw [hset]
  have hmeas : MeasurableSet (Set.univ.pi fun m : Fin 3 =>
      if m = i then Set.Icc lo hi else Set.Icc (-c) c) := by
    apply MeasurableSet.pi Set.countable_univ
    intro m _
    by_cases hm : m = i <;> simp [hm]
  rw [MeasureTheory.MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin 3))
    hmeas.nullMeasurableSet]
  rw [MeasureTheory.volume_pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ
      (fun x : Fin 3 =>
        MeasureTheory.volume (if x = i then Set.Icc lo hi else (Set.Icc (-c) c : Set ℝ)))
      (Finset.mem_univ i)]
  have hprod : ∏ x ∈ Finset.univ.erase i,
      MeasureTheory.volume (if x = i then Set.Icc lo hi else (Set.Icc (-c) c : Set ℝ))
      = MeasureTheory.volume (Set.Icc (-c) c) ^ 2 := by
    trans ∏ _x ∈ Finset.univ.erase i, MeasureTheory.volume (Set.Icc (-c) c)
    · apply Finset.prod_congr rfl
      intro x hx
      rw [if_neg (Finset.ne_of_mem_erase hx)]
    · rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
  rw [hprod, if_pos rfl]
  simp only [Real.volume_Icc]
  rw [show c - (-c) = 2 * c by ring]
  rw [← ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 2 * c)]
  rw [← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ hi - lo)]

/-- **The collar bound.**  For `c, δ > 0` and any centre `a`, the `δ`-collar of the boundary of the
cube `a + [-c,c]³` (the part of the cube where some coordinate satisfies
`|(x - a) i| > c - δ`) has volume at most `24 c² δ = 6 · (2c)² · δ`.

Proof: the collar at the origin is, for each `i : Fin 3`, contained in the union of the two closed
face slabs `{y | y i ∈ Icc (c - δ) c ∧ …}` (the positive face) and
`{y | y i ∈ Icc (-c) (-(c - δ)) ∧ …}` (the negative face), whose volumes are
`(c - (c - δ)) · (2c)² = 4 c² δ` and `((-(c - δ)) - (-c)) · (2c)² = 4 c² δ` by
`volume_coord_face_box_aux`; summing over `i` gives `3 · (2 · 4 c² δ) = 24 c² δ`.  Translation by
`-a` preserves the volume. -/
theorem volume_iUnion_collar_le {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (a : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.volume (⋃ i : Fin 3, {x : EuclideanSpace ℝ (Fin 3) |
        (∀ m : Fin 3, |(x - a) m| ≤ c) ∧ c - |(x - a) i| < δ})
      ≤ ENNReal.ofReal (24 * c ^ 2 * δ) := by
  have h4 : (0 : ℝ) ≤ 4 * c ^ 2 * δ := by positivity
  -- the collar at the origin
  set S : Set (EuclideanSpace ℝ (Fin 3)) :=
    ⋃ i : Fin 3, {y : EuclideanSpace ℝ (Fin 3) |
      (∀ m : Fin 3, |y m| ≤ c) ∧ c - |y i| < δ} with hS
  -- the set of the statement is the translate of `S` by `a`
  have hpre : (⋃ i : Fin 3, {x : EuclideanSpace ℝ (Fin 3) |
        (∀ m : Fin 3, |(x - a) m| ≤ c) ∧ c - |(x - a) i| < δ})
      = (fun x : EuclideanSpace ℝ (Fin 3) => x - a) ⁻¹' S := by
    rw [hS]
    ext x
    simp
  rw [hpre]
  have htrans : MeasureTheory.volume ((fun x : EuclideanSpace ℝ (Fin 3) => x - a) ⁻¹' S)
      = MeasureTheory.volume S := by
    have hfun : (fun x : EuclideanSpace ℝ (Fin 3) => x - a) = (fun x => x + (-a)) := by
      funext x; rw [sub_eq_add_neg]
    rw [hfun]
    exact MeasureTheory.measure_preimage_add_right MeasureTheory.volume (-a) S
  rw [htrans, hS]
  -- the three (`= 6 / 2`) face slabs all have volume `4 c² δ`
  have hsum : (∑ _i : Fin 3,
        (ENNReal.ofReal (4 * c ^ 2 * δ) + ENNReal.ofReal (4 * c ^ 2 * δ)))
      = ENNReal.ofReal (24 * c ^ 2 * δ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_add h4 h4,
      ← ENNReal.ofReal_nsmul]
    congr 1
    rw [nsmul_eq_mul]
    push_cast
    ring
  calc MeasureTheory.volume (⋃ i : Fin 3, {y : EuclideanSpace ℝ (Fin 3) |
          (∀ m : Fin 3, |y m| ≤ c) ∧ c - |y i| < δ})
      ≤ ∑ i : Fin 3, MeasureTheory.volume {y : EuclideanSpace ℝ (Fin 3) |
          (∀ m : Fin 3, |y m| ≤ c) ∧ c - |y i| < δ} :=
        MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : Fin 3, (MeasureTheory.volume {y : EuclideanSpace ℝ (Fin 3) |
            y i ∈ Set.Icc (c - δ) c ∧ ∀ m : Fin 3, m ≠ i → |y m| ≤ c}
          + MeasureTheory.volume {y : EuclideanSpace ℝ (Fin 3) |
            y i ∈ Set.Icc (-c) (-(c - δ)) ∧ ∀ m : Fin 3, m ≠ i → |y m| ≤ c}) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hsub : {y : EuclideanSpace ℝ (Fin 3) |
              (∀ m : Fin 3, |y m| ≤ c) ∧ c - |y i| < δ} ⊆
            {y : EuclideanSpace ℝ (Fin 3) |
              y i ∈ Set.Icc (c - δ) c ∧ ∀ m : Fin 3, m ≠ i → |y m| ≤ c}
            ∪ {y : EuclideanSpace ℝ (Fin 3) |
              y i ∈ Set.Icc (-c) (-(c - δ)) ∧ ∀ m : Fin 3, m ≠ i → |y m| ≤ c} := by
          intro y hy
          obtain ⟨hcube, hi⟩ := hy
          have habs : c - δ < |y i| := by linarith
          by_cases hpos : 0 ≤ y i
          · left
            have hyi : |y i| = y i := abs_of_nonneg hpos
            rw [hyi] at habs
            exact ⟨⟨habs.le, (abs_le.mp (hcube i)).2⟩, fun m _ => hcube m⟩
          · right
            have hneg : y i < 0 := not_le.mp hpos
            have hyi : |y i| = -y i := abs_of_neg hneg
            rw [hyi] at habs
            exact ⟨⟨(abs_le.mp (hcube i)).1, by linarith⟩, fun m _ => hcube m⟩
        calc MeasureTheory.volume {y : EuclideanSpace ℝ (Fin 3) |
              (∀ m : Fin 3, |y m| ≤ c) ∧ c - |y i| < δ}
            ≤ MeasureTheory.volume ({y : EuclideanSpace ℝ (Fin 3) |
                  y i ∈ Set.Icc (c - δ) c ∧ ∀ m : Fin 3, m ≠ i → |y m| ≤ c}
                ∪ {y : EuclideanSpace ℝ (Fin 3) |
                  y i ∈ Set.Icc (-c) (-(c - δ)) ∧ ∀ m : Fin 3, m ≠ i → |y m| ≤ c}) :=
              MeasureTheory.measure_mono hsub
          _ ≤ _ := MeasureTheory.measure_union_le _ _
    _ = ∑ _i : Fin 3,
          (ENNReal.ofReal (4 * c ^ 2 * δ) + ENNReal.ofReal (4 * c ^ 2 * δ)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [volume_coord_face_box_aux hc (by linarith : c - δ ≤ c) i,
          volume_coord_face_box_aux hc (by linarith : -c ≤ -(c - δ)) i,
          show c - (c - δ) = δ by ring, show (-(c - δ)) - (-c) = δ by ring,
          show δ * (2 * c) ^ 2 = 4 * c ^ 2 * δ by ring]
    _ = ENNReal.ofReal (24 * c ^ 2 * δ) := hsum

end Work.BoseFixB1B
