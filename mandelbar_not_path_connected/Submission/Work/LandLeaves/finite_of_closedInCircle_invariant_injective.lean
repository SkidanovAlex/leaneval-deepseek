import Mathlib
import Submission.Work.LandLeaves.finite_of_homeo_expanding
import Submission.Work.LandLeaves.dist_nsmul_eq_of_lt_half

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-! # Finiteness of a closed invariant set on which the angle-doubling map is injective

The proof works with the additive circle `UnitAddCircle = ℝ ⧸ ℤ`, of which `K ∪ {1}` is the
trace: the set `B = (↑) '' (K ∪ {1})` is a compact subset of the circle (the point `1` of `[0,1]`
represents the seam `0`).  The `d`-tupling map `z ↦ d • z` restricts to a continuous bijection of
`B` onto itself (`hmap`, `hsurj`, `hinj`), i.e. a self-homeomorphism `G` of the compact metric
space `B`.  Since `dist (d • z) (d • w) ≤ d * dist z w` and `dist (d • z) (d • w) = d * dist z w`
whenever `dist z w < 1/(2d)`, the abstract lemma `finite_of_homeo_expanding` gives `Finite B`,
hence `K` is finite. -/

noncomputable section

namespace Work.LandLeaves

/-- The `d`-tupling map of the circle, read off a real representative: multiplying a point
`(x : UnitAddCircle)` by `d` gives the class of `Int.fract ((d : ℝ) * x)`. -/
lemma nsmul_coe_eq_coe_fract (d : ℕ) (x : ℝ) :
    (d : ℕ) • (x : UnitAddCircle) = ((Int.fract ((d:ℝ) * x) : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_nsmul (1:ℝ) (n := d) (x := x), AddCircle.coe_fract, nsmul_eq_mul]

/-- **Finiteness of a set closed in the circle on which the angle-doubling map is injective.**

Let `d ≥ 2` and `σ x = Int.fract (d * x)` (the `d`-tupling map of the circle).  Let `K ⊆ [0,1)` be
non-empty and closed *in the circle*: `K ∪ {1}` is closed in `ℝ` (so `K` is the trace of a closed
subset of the circle, the point `1` standing for the seam `0`), and suppose `σ(K) = K` with `σ`
injective on `K` (`hmap`, `hsurj`, `hinj`).  Then `K` is finite.

This is the combinatorial heart of the finiteness of the *type* of a repelling periodic point
(Goldberg–Milnor, *Fixed points of polynomial maps II*, Lemma 2.2, but without their hypothesis
that some *rational* ray lands at the point): for `K = {ψ : rayAccum c φ ψ = {y}} ∩ Ico 0 1` the
hypotheses hold with `d = 4^k`, `σ = angDouble^[2k]` — invariance is
`Work.LandLeaves.rayAccum_angDouble_of_isRepelling`, injectivity on `K` modulo `1` is
`Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq`, surjectivity is
`Work.LandLeaves.exists_preimage_rayAccum`, and `K ∪ {1}` is closed because the type is closed
(`Work.LandLeaves.isClosed_rayAccum_singleton`) and `1`-periodic (`rayAccum_add_int`).

Proof: `hsub`+`hclosed` make `K ∪ {1} ⊆ [0,1]` compact, so `K` is compact in the circle, and
`σ|_K` is a continuous bijection of a compact space onto itself, i.e. a homeomorphism `g`.  Since
`σ` expands circle distances by the factor `d`, the map `g` is distance-decreasing by `1/d` on pairs
of circle-distance `< 1/(2d)`; a finite maximal `η/2`-separated subset of `K` then shows that `K`
cannot be infinite (an infinite `K` contains two points of circle-distance `< η/dⁿ` for every `n`,
whose images under `σⁿ` violate the separation).  Equivalently, the coding map
`Φ x = (⌊d·σⁿ x⌋)ₙ` identifies `K` with a closed shift-invariant subshift whose shift is injective;
for such a subshift the map "first symbol of the unique preimage" is continuous, hence depends on
finitely many coordinates, the resulting recurrence bounds the factor complexity, and a subshift of
bounded complexity is finite.  (In the coding formulation one must handle the `d`-adically rational
points, where `⌊d·⌋` and `Φ` are not continuous, with the compactness argument above.) -/
theorem finite_of_closedInCircle_invariant_injective {d : ℕ} (hd : 2 ≤ d) {K : Set ℝ}
    (hne : K.Nonempty) (hsub : ∀ x ∈ K, 0 ≤ x ∧ x < 1)
    (hclosed : IsClosed (K ∪ {1}))
    (hmap : ∀ x ∈ K, Int.fract ((d : ℝ) * x) ∈ K)
    (hsurj : ∀ y ∈ K, ∃ x ∈ K, Int.fract ((d : ℝ) * x) = y)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, Int.fract ((d : ℝ) * x) = Int.fract ((d : ℝ) * y) → x = y) :
    K.Finite := by
  -- The trace of `K ∪ {1}` on the circle.
  set B : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' (K ∪ {1}) with hBdef
  -- `K ∪ {1}` is a closed subset of `[0,1]`, hence compact.
  have hKcpt : IsCompact (K ∪ {1}) := by
    refine (isCompact_Icc (a := (0:ℝ)) (b := 1)).of_isClosed_subset hclosed ?_
    intro x hx
    rcases hx with hxK | hx1
    · obtain ⟨h0, h1⟩ := hsub x hxK; exact ⟨h0, le_of_lt h1⟩
    · rw [Set.mem_singleton_iff] at hx1; subst hx1; exact ⟨zero_le_one, le_rfl⟩
  have hBcpt : IsCompact B := by
    rw [hBdef]
    exact hKcpt.image (AddCircle.continuous_mk' (1:ℝ))
  haveI : CompactSpace B := isCompact_iff_compactSpace.mp hBcpt
  -- The `d`-tupling map preserves `B`.
  have hmapB : ∀ z ∈ B, (d : ℕ) • z ∈ B := by
    intro z hz
    rw [hBdef] at hz ⊢
    obtain ⟨x, hx, rfl⟩ := hz
    rcases hx with hxK | hx1
    · exact ⟨Int.fract ((d:ℝ) * x), Or.inl (hmap x hxK), (nsmul_coe_eq_coe_fract d x).symm⟩
    · rw [Set.mem_singleton_iff] at hx1; subst hx1
      refine ⟨(1:ℝ), Or.inr rfl, ?_⟩
      rw [nsmul_coe_eq_coe_fract]
      have hff : Int.fract ((d:ℝ) * 1) = 0 := by rw [mul_one]; exact Int.fract_natCast d
      rw [hff, AddCircle.coe_zero, AddCircle.coe_period]
  let g : B → B := fun z => ⟨(d : ℕ) • (z : UnitAddCircle), hmapB z z.2⟩
  have hgcont : Continuous g :=
    Continuous.subtype_mk ((continuous_nsmul d).comp continuous_subtype_val)
      (fun z => hmapB z z.2)
  have hKfract_zero : Int.fract ((d:ℝ) * 0) = 0 := by rw [mul_zero, Int.fract_zero]
  have hzero : (d:ℕ) • ((1:ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_period (1:ℝ), nsmul_zero]
  -- `g` is injective: on the circle the `d`-tupling map is injective on `B`.
  have hginj : Function.Injective g := by
    rintro ⟨z, hz⟩ ⟨w, hw⟩ hzw
    have hzw' : (d:ℕ) • z = (d:ℕ) • w := by
      simpa only [g] using congrArg Subtype.val hzw
    rw [hBdef] at hz hw
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨y, hy, rfl⟩ := hw
    apply Subtype.ext
    change ((x : ℝ) : UnitAddCircle) = ((y : ℝ) : UnitAddCircle)
    have key : ∀ a ∈ K ∪ {1}, ∀ b ∈ K ∪ {1},
        (d:ℕ) • (a : UnitAddCircle) = (d:ℕ) • (b : UnitAddCircle) →
        ((a : ℝ) : UnitAddCircle) = ((b : ℝ) : UnitAddCircle) := by
      intro a ha b hb hab
      rcases ha with haK | ha1
      · rcases hb with hbK | hb1
        · -- both in `K`: use injectivity of `σ` on `K` and of `↑` on `Ico 0 1`.
          have h1 : Int.fract ((d:ℝ) * a) = Int.fract ((d:ℝ) * b) := by
            rw [nsmul_coe_eq_coe_fract d a, nsmul_coe_eq_coe_fract d b] at hab
            exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1:ℝ)) (a := 0)
              ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one ((d:ℝ)*a)⟩
              ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one ((d:ℝ)*b)⟩).mp hab
          rw [hinj a haK b hbK h1]
        · -- `b = 1`: then `a` has `σ a = 0`, so `a = 0` and both sides are the seam.
          rw [Set.mem_singleton_iff] at hb1; subst hb1
          have h1 : Int.fract ((d:ℝ) * a) = 0 := by
            have hz2 : ((Int.fract ((d:ℝ)*a) : ℝ) : UnitAddCircle) = 0 := by
              rw [← nsmul_coe_eq_coe_fract d a, hab, hzero]
            exact (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1:ℝ))
              ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one ((d:ℝ)*a)⟩).mp hz2
          have h0K : (0:ℝ) ∈ K := by rw [← h1]; exact hmap a haK
          have ha0 : a = 0 := hinj a haK 0 h0K (by rw [h1, hKfract_zero])
          rw [ha0, AddCircle.coe_zero, AddCircle.coe_period]
      · -- `a = 1`: symmetric.
        rw [Set.mem_singleton_iff] at ha1; subst ha1
        rcases hb with hbK | hb1
        · have h1 : Int.fract ((d:ℝ) * b) = 0 := by
            have hz2 : ((Int.fract ((d:ℝ)*b) : ℝ) : UnitAddCircle) = 0 := by
              rw [← nsmul_coe_eq_coe_fract d b, ← hab, hzero]
            exact (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1:ℝ))
              ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one ((d:ℝ)*b)⟩).mp hz2
          have h0K : (0:ℝ) ∈ K := by rw [← h1]; exact hmap b hbK
          have hb0 : b = 0 := hinj b hbK 0 h0K (by rw [h1, hKfract_zero])
          rw [hb0, AddCircle.coe_zero, AddCircle.coe_period]
        · rw [Set.mem_singleton_iff] at hb1; subst hb1; rfl
    exact key x hx y hy hzw'
  -- `g` is surjective: `σ : K → K` is onto and the seam is fixed.
  have hgsurj : Function.Surjective g := by
    rintro ⟨z, hz⟩
    rw [hBdef] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rcases hx with hxK | hx1
    · obtain ⟨x', hx'K, hx'⟩ := hsurj x hxK
      refine ⟨⟨(x':ℝ), ?_⟩, ?_⟩
      · rw [hBdef]; exact ⟨x', Or.inl hx'K, rfl⟩
      · apply Subtype.ext
        show (d:ℕ) • (x' : UnitAddCircle) = ((x:ℝ) : UnitAddCircle)
        rw [nsmul_coe_eq_coe_fract, hx']
    · rw [Set.mem_singleton_iff] at hx1; subst hx1
      refine ⟨⟨0, ?_⟩, ?_⟩
      · rw [hBdef]
        exact ⟨(1:ℝ), Or.inr rfl, AddCircle.coe_period (1:ℝ)⟩
      · apply Subtype.ext
        show (d:ℕ) • (0 : UnitAddCircle) = ((1:ℝ) : UnitAddCircle)
        rw [nsmul_zero, AddCircle.coe_period]
  have hbij : Function.Bijective g := ⟨hginj, hgsurj⟩
  let e : B ≃ B := Equiv.ofBijective g hbij
  have hecont : Continuous (e : B → B) := by
    rw [Equiv.coe_ofBijective]; exact hgcont
  -- `g` is a self-homeomorphism of the compact metric space `B`.
  let G : B ≃ₜ B := Continuous.homeoOfEquivCompactToT2 (f := e) hecont
  have hdR : (1:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 1 < d)
  have hdRpos : (0:ℝ) < (d:ℝ) := lt_trans one_pos hdR
  have heta : (0:ℝ) < 1 / (2 * (d:ℝ)) := one_div_pos.mpr (by positivity)
  have hGval : ∀ a : B, (G a : UnitAddCircle) = (d:ℕ) • (a : UnitAddCircle) := fun a => rfl
  have hfinB : B.Finite := by
    rw [← Set.finite_coe_iff]
    refine finite_of_homeo_expanding (X := B) G hdR heta ?_ ?_
    · -- Lipschitz bound: the tupling map is `d`-Lipschitz.
      intro a b
      simp only [Subtype.dist_eq, hGval]
      rw [dist_eq_norm, dist_eq_norm, ← nsmul_sub]
      exact norm_nsmul_le
    · -- Expansion: on pairs at distance `< 1/(2d)` the distance is multiplied by `d`.
      intro a b hab
      rw [Subtype.dist_eq] at hab
      simp only [Subtype.dist_eq, hGval]
      refine dist_nsmul_eq_of_lt_half (n := d) ?_
      have h1 : dist ↑a ↑b < (2 * (d:ℝ))⁻¹ := by rw [one_div] at hab; exact hab
      calc (d:ℝ) * dist ↑a ↑b < (d:ℝ) * (2 * (d:ℝ))⁻¹ := mul_lt_mul_of_pos_left h1 hdRpos
        _ = 1/2 := by field_simp
  -- Transfer finiteness back to `K`.
  have hsub_img : ((↑) : ℝ → UnitAddCircle) '' K ⊆ B := by
    rw [hBdef]; exact Set.image_mono Set.subset_union_left
  have hfinImg : (((↑) : ℝ → UnitAddCircle) '' K).Finite := hfinB.subset hsub_img
  refine Set.Finite.of_finite_image hfinImg ?_
  intro x hx y hy hxy
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1:ℝ)) (a := 0)
    ⟨(hsub x hx).1, by simpa using (hsub x hx).2⟩
    ⟨(hsub y hy).1, by simpa using (hsub y hy).2⟩).mp hxy

end Work.LandLeaves
