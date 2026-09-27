import Mathlib
import Submission.Work.Noncompact.exists_structured_proper_embedding_weak
import Submission.Work.Projection.exists_projection_transverse_avoiding

/-!
# A proper immersion of a second countable manifold into `ℝ^{2n}` in general position

Let `M` be a Hausdorff, second countable, nonempty smooth `n`-manifold (`1 ≤ n`, no compactness,
no boundary).  We construct a map `h : M → ℝ^{2n}` which is

* smooth,
* an immersion (`mfderiv h x` injective everywhere),
* **proper**,
* and in general position: every pair `x ≠ y` with `h x = h y` is a *transverse* double point
  (`(mfderiv h x).range ⊔ (mfderiv h y).range = ⊤`).

Since `h` is a proper immersion, its double point set is closed and discrete in `M × M ∖ Δ` and
every value has finitely many preimages; this is the input of the "push the double points to
infinity" argument which reduces the strong Whitney theorem to the compact case (see the plan in
`Submission.lean`).

## The construction

`Work.Noncompact.exists_structured_proper_embedding_weak` provides a smooth injective immersion
`g : M → ℝ^{2n+1}`, a smooth *proper* `f : M → ℝ` and `u₀ ≠ 0` with `‖g x + f x • u₀‖ ≤ 1`
(equivalently `g = b - f • u₀` with `b` bounded).  Projecting along a generic direction `u ∈ ℝ^{2n}`
(`Work.Projection.exists_projection_transverse_avoiding`, applied with the null set
`Z = {pairEquiv n (extract u₀)}`) gives an immersion with transverse double points.  The extra
condition `pairEquiv n u ∉ Z` says exactly `projVec u u₀ ≠ 0` (if `projVec u u₀ = 0` then
`u₀ = c • vVec u` with `c = (u₀ (Fin.last _))`, so `u = extract u₀`), which makes the projected map
proper:

  `‖projVec u (g x)‖ ≥ |f x| * ‖projVec u u₀‖ - ‖projVec u‖`,

and `f` is proper, so preimages of compact sets are compact.
-/

namespace Work.Noncompact

open scoped Manifold ContDiff
open Topology Set

/-- **The direction `u` with `projVec u z = 0` is determined by `z`** (for `z ≠ 0`): if
`projVec u z = 0` then `z = c • vVec u`, and `c = z (Fin.last k)` is nonzero because `z ≠ 0`; hence
`u = extract z`, where `extract z = (z_1/z_{k+1}, …, z_k/z_{k+1})`. -/
theorem eq_extract_of_projVec_eq_zero {k : ℕ}
    {u : EuclideanSpace ℝ (Fin k)} {z : EuclideanSpace ℝ (Fin (k + 1))}
    (h : Work.Projection.projVec u z = 0) (hz : z ≠ 0) :
    u = Work.Projection.extract z := by
  obtain ⟨c, hc⟩ := (Work.Projection.projVec_eq_zero_iff u z).mp h
  have hcne : c ≠ 0 := by
    intro h0
    exact hz (by rw [hc, h0, zero_smul])
  exact (Work.Projection.extract_of_eq_smul_vVec u hcne hc).symm

/-- **A proper immersion of a second countable manifold into `ℝ^{2n}` in general position.** -/
theorem exists_proper_immersion_transverse {n : ℕ} (hn : 1 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [Nonempty M] :
    ∃ h : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ h ∧ IsProperMap h ∧
      (∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) h x)) ∧
      ∀ x y, x ≠ y → h x = h y →
        (mfderiv (𝓡 n) (𝓡 (2 * n)) h x).range ⊔
        (mfderiv (𝓡 n) (𝓡 (2 * n)) h y).range = ⊤ := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨g, f, u₀, hu₀, hgsm, hfsm, hfprop, hginj, hgimm, hbnd⟩ :=
    exists_structured_proper_embedding_weak (n := n) (M := M)
  -- the unique direction whose projection kills `u₀`
  set w₀ : EuclideanSpace ℝ (Fin (2 * n)) := Work.Projection.extract u₀ with hw₀
  set Z : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    {z | z = Work.Projection.pairEquiv n w₀} with hZ
  have hZnull : MeasureTheory.volume Z = 0 := by
    haveI : MeasureTheory.NullSingletonClass
        (MeasureTheory.volume :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) :=
      MeasureTheory.Measure.prod.instNullSingletonClass_fst
    rw [hZ]
    exact MeasureTheory.measure_singleton _
  obtain ⟨u, huZ, huimm, hutr⟩ :=
    Work.Projection.exists_projection_transverse_avoiding (n := n) (M := M)
      g hgsm hginj hgimm Z hZnull
  have hpairne : Work.Projection.pairEquiv n u ≠ Work.Projection.pairEquiv n w₀ := by
    intro hcon
    exact huZ (by rw [hZ]; exact hcon)
  have hune : u ≠ w₀ := fun hcon => hpairne (by rw [hcon])
  -- the projection of `u₀` is nonzero
  have hwne : Work.Projection.projVec u u₀ ≠ 0 := by
    intro h0
    exact hune (eq_extract_of_projVec_eq_zero h0 hu₀)
  set h : M → EuclideanSpace ℝ (Fin (2 * n)) := fun x => Work.Projection.projVec u (g x) with hh
  have hsm : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ h :=
    Work.Projection.contMDiff_comp_clm (Work.Projection.projVec u) g hgsm
  -- the bounded companion of `g`
  set b : M → EuclideanSpace ℝ (Fin (2 * n + 1)) := fun x => g x + f x • u₀ with hb
  have hbbd : ∀ x, ‖b x‖ ≤ 1 := hbnd
  have hg_eq : ∀ x, g x = b x - f x • u₀ := by
    intro x
    rw [hb]
    simp
  have hlin : ∀ x, h x = Work.Projection.projVec u (b x) - f x • Work.Projection.projVec u u₀ := by
    intro x
    rw [hh]
    change Work.Projection.projVec u (g x)
      = Work.Projection.projVec u (b x) - f x • Work.Projection.projVec u u₀
    rw [hg_eq x, map_sub, map_smul]
  have hproper : IsProperMap h := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hsm.continuous, fun K hK => ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    set c₁ : ℝ := ‖Work.Projection.projVec u u₀‖ with hc₁
    set c₂ : ℝ := ‖Work.Projection.projVec u‖ with hc₂
    have hc₁pos : 0 < c₁ := by rw [hc₁]; exact norm_pos_iff.mpr hwne
    have hbdd : ∀ x, ‖Work.Projection.projVec u (b x)‖ ≤ c₂ := by
      intro x
      calc ‖Work.Projection.projVec u (b x)‖
          ≤ ‖Work.Projection.projVec u‖ * ‖b x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ c₂ * 1 := by
            rw [hc₂]
            exact mul_le_mul_of_nonneg_left (hbbd x) (norm_nonneg _)
        _ = c₂ := mul_one _
    refine IsCompact.of_isClosed_subset
      (hfprop.isCompact_preimage (isCompact_Icc (a := -((R + c₂) / c₁)) (b := (R + c₂) / c₁)))
      (hK.isClosed.preimage hsm.continuous) ?_
    intro x hx
    rw [mem_preimage] at hx
    have h1 : ‖h x‖ ≤ R := hR _ hx
    have h3 : ‖f x‖ * c₁ ≤ R + c₂ := by
      have h4 : ‖f x • Work.Projection.projVec u u₀‖
          ≤ ‖Work.Projection.projVec u (b x)‖ + ‖h x‖ := by
        have h5 : f x • Work.Projection.projVec u u₀
            = Work.Projection.projVec u (b x) - h x := by
          rw [hlin x]; abel
        rw [h5]
        exact norm_sub_le _ _
      have h6 : ‖f x • Work.Projection.projVec u u₀‖ = ‖f x‖ * c₁ := by
        rw [norm_smul, Real.norm_eq_abs, hc₁]
      rw [h6] at h4
      linarith [hbdd x]
    have h7 : ‖f x‖ ≤ (R + c₂) / c₁ := (le_div_iff₀ hc₁pos).mpr h3
    rw [mem_preimage, mem_Icc]
    have h8 : |f x| ≤ (R + c₂) / c₁ := by rwa [Real.norm_eq_abs] at h7
    exact ⟨by linarith [(abs_le.mp h8).1], by linarith [(abs_le.mp h8).2]⟩
  exact ⟨h, hsm, hproper, fun x => huimm x, fun x y hxy hhxy => hutr x y hxy hhxy⟩

end Work.Noncompact
