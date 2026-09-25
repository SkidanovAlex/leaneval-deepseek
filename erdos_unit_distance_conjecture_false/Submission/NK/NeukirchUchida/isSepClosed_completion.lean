import Mathlib
import Submission.NK.NeukirchUchida.exists_monic_separable_approx

/-!
# The completion of a separably closed valued field is separably closed

Let `K` be a field carrying a valuation with values in `Γ₀` (rank one on the completion),
and suppose `K` is separably closed.  Then the completion `K̂` of `K` with respect to the
valuation is separably closed as well.

The proof follows the strategy of Mathlib's `IsAlgClosed.of_denseRange`
(`Mathlib/Analysis/Normed/Field/Dense.lean`):  given a monic separable polynomial `f` over the
completion, approximate it coefficientwise by a monic polynomial `g` of the same degree over
`K`, choose `g` *separable* (this is the missing ingredient `exists_monic_separable_approx`,
the TODO in Mathlib's `Approximation.lean`), use continuity of roots to find a root `b` of `g`
close to a root `a` of `f`, and conclude `a ∈ L⟮b⟯ = L` by Krasner's lemma, since `b` lies in
`K ⊆ L` (as `g` splits over the separably closed field `K`).
-/

noncomputable section

set_option linter.style.haveILetI false

open Polynomial

open scoped Valued

namespace NK.NeukirchUchida

/-- If `K` is a separably closed dense subfield of a complete nonarchimedean normed field `L`,
then `L` is separably closed.  (Separable version of `IsAlgClosed.of_denseRange`.) -/
theorem isSepClosed_of_denseRange {K L : Type*} [Field K] [NontriviallyNormedField L]
    [CompleteSpace L] [IsUltrametricDist L] [Algebra K L]
    (hi : DenseRange (algebraMap K L)) [IsSepClosed K] : IsSepClosed L := by
  -- find a small nonzero element of `K`
  have hsmall : ∃ c : K, 0 < ‖algebraMap K L c‖ ∧ ‖algebraMap K L c‖ < 1 := by
    obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm L
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx
      exact absurd hx (by norm_num)
    set z : L := x⁻¹ with hzdef
    have hz0 : 0 < ‖z‖ := by
      rw [hzdef, norm_inv]
      exact inv_pos_of_pos (lt_trans zero_lt_one hx)
    have hz1 : ‖z‖ < 1 := by
      rw [hzdef, norm_inv]
      exact inv_lt_one_of_one_lt₀ hx
    have hr : 0 < min (‖z‖ / 2) ((1 - ‖z‖) / 2) := lt_min (by linarith) (by linarith)
    obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp hi z _ hr
    have hc' : ‖algebraMap K L c - z‖ < min (‖z‖ / 2) ((1 - ‖z‖) / 2) := by
      rw [← dist_eq_norm, dist_comm]
      exact hc
    have hmin1 : min (‖z‖ / 2) ((1 - ‖z‖) / 2) ≤ (1 - ‖z‖) / 2 := min_le_right _ _
    have hmin2 : min (‖z‖ / 2) ((1 - ‖z‖) / 2) ≤ ‖z‖ / 2 := min_le_left _ _
    refine ⟨c, ?_, ?_⟩
    · have h1 : ‖z‖ ≤ ‖algebraMap K L c‖ + ‖algebraMap K L c - z‖ := by
        calc ‖z‖ = ‖algebraMap K L c - (algebraMap K L c - z)‖ := by ring_nf
          _ ≤ ‖algebraMap K L c‖ + ‖algebraMap K L c - z‖ := norm_sub_le _ _
      linarith
    · have h1 : ‖algebraMap K L c‖ ≤ ‖algebraMap K L c - z‖ + ‖z‖ := by
        calc ‖algebraMap K L c‖ = ‖(algebraMap K L c - z) + z‖ := by ring_nf
          _ ≤ ‖algebraMap K L c - z‖ + ‖z‖ := norm_add_le _ _
      linarith
  -- now the main argument
  apply IsSepClosed.of_exists_root
  intro f fmon firr fsep
  have fnatdeg0 : f.natDegree ≠ 0 := (Irreducible.natDegree_pos firr).ne'
  let F := f.SplittingField
  let : NormedField F := spectralNorm.normedField L F
  let : NormedAlgebra L F := spectralNorm.normedAlgebra L F
  let a := rootOfSplits (SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  have fa0 : f.aeval a = 0 := by
    rw [← eval_map_algebraMap]
    exact eval_rootOfSplits (Polynomial.SplittingField.splits f)
      (by simpa using degree_ne_of_natDegree_ne fnatdeg0)
  -- `δ`: a positive separation radius for the conjugates of `a`
  classical
  let S : Finset F := {x ∈ (f.rootSet F).toFinset | x ≠ a}
  let δ : ℝ := if hS : S.Nonempty then Finset.min' (S.image fun x => ‖a - x‖)
      (Finset.image_nonempty.mpr hS) else 1
  have norm_sub_le : ∀ a' : F, IsConjRoot L a a' → a ≠ a' → δ ≤ ‖a - a'‖ := by
    intro a' conj ne
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · apply Finset.min'_le (S.image fun x => ‖a - x‖) (‖a - a'‖)
      apply Finset.mem_image_of_mem
      simp only [minpoly.eq_of_irreducible_of_monic firr fa0 fmon, Finset.mem_filter,
        Set.mem_toFinset, S]
      rw [← (isConjRoot_iff_mem_minpoly_rootSet ⟨f, fmon, fa0⟩)]
      exact ⟨conj, ne.symm⟩
    · simp only [ne_eq, Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff,
        Set.mem_toFinset, not_not, S] at hS
      rw [isConjRoot_iff_mem_minpoly_rootSet ⟨f, fmon, fa0⟩,
          ← minpoly.eq_of_irreducible_of_monic firr fa0 fmon] at conj
      exact (ne (hS conj).symm).elim
  have δpos : δ > 0 := by
    by_cases hS : S.Nonempty <;> simp only [hS, ↓reduceDIte, δ]
    · simp only [gt_iff_lt, Finset.lt_min'_iff, Finset.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      rintro a' ha'
      simp only [Finset.mem_filter, Set.mem_toFinset, S] at ha'
      rw [norm_pos_iff, sub_ne_zero]
      exact ha'.2.symm
    · linarith
  -- the approximation tolerance
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  -- separable approximation of `f` over `K`
  obtain ⟨g, gmon, gsep, gdeg, gcoeff⟩ :=
    exists_monic_separable_approx hi hsmall fmon fsep hε
  -- continuity of roots
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (K := L) (L := F)
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map (algebraMap K L))) gcoeff
      (by
        simpa [Polynomial.map_map] using
          (IsSepClosed.splits_of_separable g gsep).map ((algebraMap L F).comp (algebraMap K L)))
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity
  -- `b` lies in the image of `L`
  have bbot : b ∈ (⊥ : IntermediateField L F) := by
    rw [Polynomial.aroots_def,
      Splits.roots_map ((IsSepClosed.splits_of_separable g gsep).map (algebraMap K L)),
      Multiset.mem_map] at hb
    obtain ⟨bCp, _, hbCp⟩ := hb
    rw [IntermediateField.mem_bot]
    exact ⟨bCp, hbCp⟩
  have hbroot : (Polynomial.aeval b) (g.map (algebraMap K L)) = 0 :=
    (Polynomial.mem_aroots.mp hb).2
  -- Krasner's lemma
  have abot : a ∈ (⊥ : IntermediateField L F) := by
    have masp : ((minpoly L a).map (algebraMap L F)).Splits := by
      simpa [minpoly.eq_of_irreducible_of_monic firr fa0 fmon] using
        (Polynomial.SplittingField.splits f)
    have hsep : (minpoly L a).Separable := by
      rw [← minpoly.eq_of_irreducible_of_monic firr fa0 fmon]
      exact fsep
    simpa [IntermediateField.adjoin_simple_eq_bot_iff.mpr bbot] using
      IsKrasner.krasner hsep masp ⟨(g.map _), gmon.map _, hbroot⟩
        fun a' h1 h2 ↦ lt_of_lt_of_le hab (norm_sub_le a' h1 h2)
  obtain ⟨aCp, haCp⟩ := IntermediateField.mem_bot.mp abot
  use aCp
  apply_fun algebraMap L F
  · rwa [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, haCp, map_zero]
  · exact RingHom.injective _

/-- **The completion of a separably closed valued field is separably closed.**

`K` is a valued field which is separably closed, and the valuation on its completion (the
extension of `v` to the completion) has rank one.  Then the completion is separably closed. -/
theorem isSepClosed_completion {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [hv : Valued K Γ₀] [IsSepClosed K]
    (h : (Valued.extensionValuation (K := K) (Γ₀ := Γ₀)).RankOne) :
    IsSepClosed (UniformSpace.Completion K) := by
  haveI := h
  exact isSepClosed_of_denseRange (K := K) (L := UniformSpace.Completion K)
    UniformSpace.Completion.denseRange_coe

end NK.NeukirchUchida
