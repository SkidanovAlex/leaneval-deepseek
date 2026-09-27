import Mathlib

/-!
# The open ball in `ℂ` with a countable set removed is preconnected

We prove that `Metric.ball (0 : ℂ) δ \ D` is preconnected whenever `0 < δ` and `D` is
countable.  The proof is a two-segment construction: for any two points `x, y` in the
punctured ball we find a point `z` on a horizontal line `{w | w.im = c}` (chosen to avoid
both `x` and `y`) such that the segments `[x, z]` and `[z, y]` avoid `D`.  The key point
is that for a fixed `d`, the set of `z` on the line whose segment to `x` (or `y`) contains
`d` is a *subsingleton*, so the whole "bad" set is countable, while the intersection of
the line with the ball is an interval, hence uncountable.
-/

namespace Work.EQ

/-- For a line `{z | z.im = c}` not passing through `x`, and a point `d ≠ x`, the set of
points `z` of the line with `d ∈ segment ℝ x z` has at most one element. -/
lemma subsingleton_segment_im {x d : ℂ} {c : ℝ} (hcx : c ≠ x.im) (hdx : d ≠ x) :
    {z : ℂ | z.im = c ∧ d ∈ segment ℝ x z}.Subsingleton := by
  intro z₁ hz₁ z₂ hz₂
  obtain ⟨hz₁im, hz₁seg⟩ := hz₁
  obtain ⟨hz₂im, hz₂seg⟩ := hz₂
  obtain ⟨θ₁, hθ₁, hθ₁eq⟩ := Set.mem_image _ _ _ |>.1 (segment_eq_image' ℝ x z₁ ▸ hz₁seg)
  obtain ⟨θ₂, hθ₂, hθ₂eq⟩ := Set.mem_image _ _ _ |>.1 (segment_eq_image' ℝ x z₂ ▸ hz₂seg)
  have him₁ : x.im + θ₁ * (c - x.im) = d.im := by
    have := congrArg Complex.im hθ₁eq
    rwa [Complex.add_im, Complex.smul_im, Complex.sub_im, hz₁im, smul_eq_mul] at this
  have him₂ : x.im + θ₂ * (c - x.im) = d.im := by
    have := congrArg Complex.im hθ₂eq
    rwa [Complex.add_im, Complex.smul_im, Complex.sub_im, hz₂im, smul_eq_mul] at this
  have hcx' : c - x.im ≠ 0 := sub_ne_zero.mpr hcx
  have hθ : θ₁ = θ₂ := by
    have hmul : θ₁ * (c - x.im) = θ₂ * (c - x.im) := by linarith
    exact mul_right_cancel₀ hcx' hmul
  have hs₁ : θ₁ • (z₁ - x) = d - x := by
    rw [eq_sub_iff_add_eq, add_comm]; exact hθ₁eq
  have hθ₁ne : θ₁ ≠ 0 := by
    intro h
    rw [h, zero_smul] at hs₁
    exact hdx (sub_eq_zero.mp hs₁.symm)
  have hs₂ : θ₂ • (z₂ - x) = d - x := by
    rw [eq_sub_iff_add_eq, add_comm]; exact hθ₂eq
  have hθ₂ne : θ₂ ≠ 0 := by rw [← hθ]; exact hθ₁ne
  have hsub : z₁ - x = z₂ - x := by
    rw [show z₁ - x = θ₁⁻¹ • (d - x) from by rw [← hs₁, smul_smul, inv_mul_cancel₀ hθ₁ne, one_smul],
        show z₂ - x = θ₂⁻¹ • (d - x) from by rw [← hs₂, smul_smul, inv_mul_cancel₀ hθ₂ne, one_smul],
        hθ]
  exact sub_left_inj.mp hsub

/-- The set of points `z` of the line `{z | z.im = c}` such that some `d ∈ D` lies on the
segment `[x, z]` is countable, as long as `x ∉ D` and the line misses `x`. -/
lemma countable_segment_im_slice {x : ℂ} {c : ℝ} {D : Set ℂ} (hD : D.Countable)
    (hcx : c ≠ x.im) (hxD : x ∉ D) :
    {z : ℂ | z.im = c ∧ ∃ d ∈ D, d ∈ segment ℝ x z}.Countable := by
  have heq : {z : ℂ | z.im = c ∧ ∃ d ∈ D, d ∈ segment ℝ x z}
      = ⋃ d, ⋃ (_ : d ∈ D), {z : ℂ | z.im = c ∧ d ∈ segment ℝ x z} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    tauto
  rw [heq]
  exact (Set.Countable.biUnion_iff hD).mpr (fun d hd =>
    (subsingleton_segment_im hcx (fun hxd => hxD (hxd ▸ hd))).countable)

/-- The intersection of the open ball of radius `δ` with a line `{z | z.im = c}` is
uncountable (it is an open interval of `ℂ`), provided `|c| < δ`. -/
lemma not_countable_im_ball_slice {c δ : ℝ} (hδ : 0 < δ) (hc : |c| < δ) :
    ¬ ({z : ℂ | z.im = c} ∩ Metric.ball (0:ℂ) δ).Countable := by
  set r := Real.sqrt (δ^2 - c^2) with hrdef
  have hc2 : c^2 < δ^2 := sq_lt_sq.mpr (by rwa [abs_of_pos hδ])
  have hrpos : 0 < r := by rw [hrdef, Real.sqrt_pos]; linarith
  have hr2 : r^2 = δ^2 - c^2 := by rw [hrdef, Real.sq_sqrt]; linarith
  have hmem : ∀ t ∈ Set.Ioo (-r) r, Complex.mk t c ∈ ({z : ℂ | z.im = c} ∩ Metric.ball (0:ℂ) δ) := by
    intro t ht
    refine ⟨rfl, ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    have htabs : |t| < r := abs_lt.mpr ⟨ht.1, ht.2⟩
    have ht2 : t^2 < r^2 := sq_lt_sq.mpr (by simpa [abs_of_pos hrpos] using htabs)
    have hnorm2 : ‖Complex.mk t c‖^2 = t^2 + c^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have : ‖Complex.mk t c‖^2 < δ^2 := by rw [hnorm2]; rw [hr2] at ht2; linarith
    have hlt : |‖Complex.mk t c‖| < |δ| := sq_lt_sq.mp this
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos hδ] at hlt
  intro hcount
  have hinj : Set.InjOn (fun t => Complex.mk t c) (Set.Ioo (-r) r) := by
    intro t₁ _ t₂ _ h
    exact congrArg Complex.re h
  have hcont' : ((fun t => Complex.mk t c) '' Set.Ioo (-r) r).Countable :=
    hcount.mono (by rintro z ⟨t, ht, rfl⟩; exact hmem t ht)
  have := Set.countable_of_injective_of_countable_image hinj hcont'
  have := Cardinal.Real.Ioo_countable_iff.mp this
  linarith

/-- Given two points `x, y` of the punctured ball, there is a point `z` of the ball such
that both segments `[x, z]` and `[z, y]` avoid `D`. -/
lemma exists_good_point {δ : ℝ} (hδ : 0 < δ) {D : Set ℂ} (hD : D.Countable)
    {x y : ℂ} (hx : x ∈ Metric.ball (0:ℂ) δ \ D) (hy : y ∈ Metric.ball (0:ℂ) δ \ D) :
    ∃ z ∈ Metric.ball (0:ℂ) δ,
      (∀ d ∈ D, d ∉ segment ℝ x z) ∧ (∀ d ∈ D, d ∉ segment ℝ z y) := by
  have hfin : ({x.im, y.im} : Set ℝ).Finite := (Set.finite_singleton y.im).insert x.im
  obtain ⟨c, hcI, hcnotin⟩ := (Set.Ioo_infinite hδ).exists_notMem_finite hfin
  have hcabs : |c| < δ := abs_lt.mpr ⟨by linarith [hcI.1], hcI.2⟩
  have hcnotx : c ≠ x.im := fun h => hcnotin (by simp [h])
  have hcnoty : c ≠ y.im := fun h => hcnotin (by simp [h])
  have hbadx : {z : ℂ | z.im = c ∧ ∃ d ∈ D, d ∈ segment ℝ x z}.Countable :=
    countable_segment_im_slice hD hcnotx hx.2
  have hbady : {z : ℂ | z.im = c ∧ ∃ d ∈ D, d ∈ segment ℝ y z}.Countable :=
    countable_segment_im_slice hD hcnoty hy.2
  have hnot : ¬ ({z : ℂ | z.im = c} ∩ Metric.ball (0:ℂ) δ).Countable :=
    not_countable_im_ball_slice hδ hcabs
  have hne : (({z : ℂ | z.im = c} ∩ Metric.ball (0:ℂ) δ) \
      ({z : ℂ | z.im = c ∧ ∃ d ∈ D, d ∈ segment ℝ x z} ∪
       {z : ℂ | z.im = c ∧ ∃ d ∈ D, d ∈ segment ℝ y z})).Nonempty := by
    by_contra h
    exact hnot ((hbadx.union hbady).mono (fun z hz => by by_contra hzb; exact h ⟨z, hz, hzb⟩))
  obtain ⟨z, hzS, hzbad⟩ := hne
  have hznotbad := not_or.mp hzbad
  refine ⟨z, hzS.2, ?_, ?_⟩
  · intro d hd hdseg
    exact hznotbad.1 ⟨hzS.1, ⟨d, hd, hdseg⟩⟩
  · intro d hd hdseg
    exact hznotbad.2 ⟨hzS.1, ⟨d, hd, segment_symm ℝ z y ▸ hdseg⟩⟩

theorem isPreconnected_ball_diff_countable {δ : ℝ} (hδ : 0 < δ) {D : Set ℂ} (hD : D.Countable) :
    IsPreconnected (Metric.ball (0 : ℂ) δ \ D) := by
  refine isPreconnected_of_forall_pair ?_
  intro x hx y hy
  obtain ⟨z, hzball, hxz, hzy⟩ := exists_good_point hδ hD hx hy
  refine ⟨segment ℝ x z ∪ segment ℝ z y, ?_, ?_, ?_, ?_⟩
  · rintro w (hw | hw)
    · exact ⟨(convex_ball (0:ℂ) δ).segment_subset hx.1 hzball hw, fun hwD => hxz w hwD hw⟩
    · exact ⟨(convex_ball (0:ℂ) δ).segment_subset hzball hy.1 hw, fun hwD => hzy w hwD hw⟩
  · exact Or.inl (left_mem_segment ℝ x z)
  · exact Or.inr (right_mem_segment ℝ z y)
  · refine IsPreconnected.union z (right_mem_segment ℝ x z) (left_mem_segment ℝ z y)
      (convex_segment (𝕜 := ℝ) x z).isPreconnected (convex_segment (𝕜 := ℝ) z y).isPreconnected

end Work.EQ
