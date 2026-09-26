import Mathlib
import Submission.Work.Drive.EpsForm.SweepGenericity

/-!
# Two planes cut the unit sphere in finitely many points

The intersection of the unit sphere of `R3` with a plane through the origin (`⟪n, ·⟫ = 0`, `n ≠ 0`)
and an affine plane (`⟪d, ·⟫ = u`) whose normal `d` is not parallel to `n` is finite: the two plane
equations cut out an affine **line** (the dimension of the orthogonal complement of `span {n, d}` is
`3 - 2 = 1` because `n` and `d` are linearly independent), and a line meets the unit sphere in at
most two points, the parameters being the roots of a genuine quadratic.

The proof below makes that quantitative: parametrising the line as `v0 + t • m` with `m ≠ 0` spanning
`(span {n, d})ᵒᵖ` and `v0` any point of the set, the sphere equation becomes the quadratic
`⟪m,m⟫ t² + 2⟪v0,m⟫ t + (⟪v0,v0⟫ - 1) = 0` in `t`, which has at most two roots.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Drive.EpsForm

noncomputable section

/-- A genuine quadratic over `ℝ` has finitely many roots.  This is stated for the concrete
polynomial `a * t ^ 2 + b * t + c` with `a ≠ 0`; the proof is the elementary factorisation
`a t² + b t + c = a (t - t₀)(t + t₀ + b/a)` around any root `t₀`. -/
lemma finite_quadratic_roots {a b c : ℝ} (ha : a ≠ 0) :
    {t : ℝ | a * t ^ 2 + b * t + c = 0}.Finite := by
  by_cases h : ∃ t₀ : ℝ, a * t₀ ^ 2 + b * t₀ + c = 0
  · obtain ⟨t₀, ht₀⟩ := h
    have hsub : {t : ℝ | a * t ^ 2 + b * t + c = 0} ⊆
        {t₀} ∪ {t : ℝ | a * t + a * t₀ + b = 0} := by
      intro t ht
      have h1 : a * t ^ 2 + b * t + c = a * t₀ ^ 2 + b * t₀ + c := by rw [ht, ht₀]
      have h2 : (t - t₀) * (a * (t + t₀) + b) = 0 := by nlinarith [h1]
      rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      rcases mul_eq_zero.mp h2 with h3 | h3
      · left; linarith
      · right; linarith
    refine Set.Finite.subset ?_ hsub
    refine (Set.finite_singleton t₀).union ?_
    exact Set.Subsingleton.finite (fun t1 ht1 t2 ht2 => by
      rw [Set.mem_ofPred_eq] at ht1 ht2
      exact mul_left_cancel₀ ha (by linarith))
  · exact Set.finite_empty.subset (fun t ht => h ⟨t, ht⟩)

/-- **The intersection of the unit sphere of `R3` with two planes through/affine is finite**, as
soon as the two normals `n` and `d` are not parallel (`n ≠ 0` and no `t` has `d = t • n`). -/
theorem twoPlanesSphere_finite {n d : LeanEval.KnotTheory.PardonDistortion.R3} (hn : n ≠ 0) (hd : ∀ t : ℝ, d ≠ t • n) (u : ℝ) :
    ({v : LeanEval.KnotTheory.PardonDistortion.R3 | inner ℝ n v = 0 ∧ inner ℝ d v = u ∧ ‖v‖ = 1} : Set LeanEval.KnotTheory.PardonDistortion.R3).Finite := by
  set S : Set R3 := {v : R3 | inner ℝ n v = 0 ∧ inner ℝ d v = u ∧ ‖v‖ = 1} with hS
  -- `n` and `d` are linearly independent
  have hind : LinearIndependent ℝ ![n, d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hn, rfl⟩
    · exfalso
      have h1 : t • d = -(s • n) := by
        rw [← add_right_inj (s • n), hst, add_neg_cancel]
      have h2 : d = t⁻¹ • (-(s • n)) := by
        have h3 : t⁻¹ • (t • d) = t⁻¹ • (-(s • n)) := by rw [h1]
        rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at h3
      exact hd (-(t⁻¹ * s)) (by rw [h2]; simp [smul_smul, smul_neg])
  -- the two plane equations define an affine line: `K` is the `span` of the two normals,
  -- and `Kᗮ` has dimension `3 - 2 = 1`
  let K : Submodule ℝ R3 := Submodule.span ℝ (Set.range ![n, d])
  have hKfin : Module.finrank ℝ K = 2 := by
    have := finrank_span_eq_card (R := ℝ) hind
    simpa [K] using this
  have hEfin : Module.finrank ℝ R3 = 3 := by
    rw [finrank_euclideanSpace]; norm_num
  have hMfin : Module.finrank ℝ (Kᗮ) = 1 :=
    Submodule.finrank_add_finrank_orthogonal' (K := K) (n := 1) (by rw [hKfin, hEfin])
  -- membership in `Kᗮ`, from the two inner products
  have hmemK : ∀ x : R3, inner ℝ n x = 0 → inner ℝ d x = 0 → x ∈ Kᗮ := by
    intro x hnx hdx
    rw [Submodule.mem_orthogonal]
    intro y hy
    refine Submodule.span_induction (p := fun y _ => inner ℝ y x = 0) ?_ ?_ ?_ ?_ hy
    · rintro z ⟨i, rfl⟩
      fin_cases i
      · simpa using hnx
      · simpa using hdx
    · simp
    · intro a b _ _ ha hb
      rw [inner_add_left, ha, hb, add_zero]
    · intro c a _ ha
      rw [inner_smul_left, ha, mul_zero]
  -- a non-zero vector spanning the one-dimensional `Kᗮ`
  have hMnb : Kᗮ ≠ ⊥ := by
    rintro h
    have h0 : Module.finrank ℝ (Kᗮ) = 0 := by rw [h]; exact finrank_bot ℝ R3
    omega
  obtain ⟨m, hmM, hm0⟩ := (Submodule.ne_bot_iff (Kᗮ)).mp hMnb
  have hMspan : Kᗮ = ℝ ∙ m := eq_span_singleton_of_mem_of_finrank_eq_one hMfin hmM hm0
  -- the affine line is `v0 + ℝ • m`; the sphere cuts it in the roots of a quadratic
  rcases S.eq_empty_or_nonempty with h0 | ⟨v0, hv0⟩
  · rw [h0]; exact Set.finite_empty
  · have hv0' : inner ℝ n v0 = 0 ∧ inner ℝ d v0 = u ∧ ‖v0‖ = 1 := by
      rw [hS] at hv0; exact hv0
    have hint : inner ℝ m m ≠ 0 := by
      have hpos : (0:ℝ) < inner ℝ m m := by
        rw [inner_self_eq_norm_sq_to_K m]
        exact pow_pos (norm_pos_iff.mpr hm0) 2
      exact ne_of_gt hpos
    have hTfin : {t : ℝ | ‖v0 + t • m‖ = 1}.Finite := by
      refine (finite_quadratic_roots (a := inner ℝ m m) (b := 2 * inner ℝ v0 m)
        (c := inner ℝ v0 v0 - 1) hint).subset ?_
      intro t ht
      have h1 : inner ℝ (v0 + t • m) (v0 + t • m) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, ht]; norm_num
      have h2 : inner ℝ (v0 + t • m) (v0 + t • m) =
          inner ℝ v0 v0 + 2 * t * inner ℝ v0 m + t^2 * inner ℝ m m := by
        simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
          real_inner_comm m v0, RCLike.conj_to_real]
        ring
      rw [h2] at h1
      show inner ℝ m m * t ^ 2 + 2 * inner ℝ v0 m * t + (inner ℝ v0 v0 - 1) = 0
      linarith
    have hSsub : S ⊆ (fun t : ℝ => v0 + t • m) '' {t : ℝ | ‖v0 + t • m‖ = 1} := by
      intro v hv
      rw [hS] at hv
      have hv' : inner ℝ n v = 0 ∧ inner ℝ d v = u ∧ ‖v‖ = 1 := hv
      have hmem : v - v0 ∈ Kᗮ := hmemK (v - v0)
        (by rw [inner_sub_right, hv'.1, hv0'.1, sub_self])
        (by rw [inner_sub_right, hv'.2.1, hv0'.2.1, sub_self])
      rw [hMspan] at hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      refine ⟨c, ?_, ?_⟩
      · show ‖v0 + c • m‖ = 1
        rw [hc, add_sub_cancel]
        exact hv'.2.2
      · show v0 + c • m = v
        rw [hc, add_sub_cancel]
    exact (hTfin.image (fun t : ℝ => v0 + t • m)).subset hSsub

end

end Work.Drive.EpsForm
