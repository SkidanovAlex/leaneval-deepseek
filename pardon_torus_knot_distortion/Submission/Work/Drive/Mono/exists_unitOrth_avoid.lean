import Mathlib
import Submission.Work.Drive.Mono.noGraze_unitOrthAvoid

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open scoped RealInnerProductSpace

/-- **An orthonormal direction avoiding a finite set of directions in `e^⊥`.**  Given a unit vector
`e`, a unit vector `e₂ ⊥ e`, and a finite set `W` of vectors orthogonal to `e`, there is a unit
`Ñ ⊥ e` whose inner product with every nonzero element of `W` is nonzero.  This is the finite-set
form of `Work.Drive.Mono.noGraze_unitOrthAvoid` and of the `exists_avoid_vertVel` chain, needed to
choose the kernel direction `n` of the merged no-graze witness so that it avoids both the knot's
vertical velocities and the Γ-arc directions `γ_k'(0) − e`. -/
theorem exists_unitOrth_avoid (e e₂ : LeanEval.KnotTheory.PardonDistortion.R3) (he : ‖e‖ = 1)
    (he₂ : ‖e₂‖ = 1) (horth : inner ℝ e₂ e = 0)
    (W : Finset LeanEval.KnotTheory.PardonDistortion.R3)
    (hW : ∀ w ∈ W, inner ℝ e w = 0) :
    ∃ Ñ : LeanEval.KnotTheory.PardonDistortion.R3, ‖Ñ‖ = 1 ∧ inner ℝ Ñ e = 0 ∧
      ∀ w ∈ W, w ≠ 0 → inner ℝ Ñ w ≠ 0 := by
  classical
  -- The set of *nonzero* vectors of `W`; the condition is only imposed on these.
  set G : Finset R3 := W.filter (fun w => w ≠ 0) with hG
  by_cases hne : G.Nonempty
  · -- Some nonzero element of `W` exists: the bad set is a finite union of hyperplanes.
    -- Each `w ∈ G` spans a direction in `e^⊥`; the covectors `⟪·,w⟫` cut out proper hyperplanes.
    set P : R3 → Submodule ℝ R3 := fun w => LinearMap.ker ((innerSL ℝ w : R3 →ₗ[ℝ] ℝ)) with hP
    have hPne : ∀ w : {w : R3 // w ∈ G}, P w.1 ≠ ⊤ := by
      rintro ⟨w, hw⟩ htop
      have hw0 : w ≠ 0 := (Finset.mem_filter.mp hw).2
      have hmem : w ∈ P w := by rw [htop]; trivial
      rw [hP, LinearMap.mem_ker] at hmem
      rw [show ((innerSL ℝ w : R3 →ₗ[ℝ] ℝ)) w = inner ℝ w w from rfl,
        real_inner_self_eq_norm_sq] at hmem
      exact hw0 (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hmem))
    have hsub := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt (K := ℝ) (M := R3)
      G.attach (fun w : {w : R3 // w ∈ G} => P w.1) hPne
      (by rw [ENat.card_eq_top_of_infinite (α := ℝ)]; exact ENat.natCast_lt_top _)
    obtain ⟨x, hx⟩ : ∃ x : R3, x ∉ ⋃ i ∈ G.attach, (P i.1 : Set R3) := by
      by_contra hcon
      push Not at hcon
      exact (Set.ssubset_univ_iff.mp hsub) (Set.eq_univ_of_forall hcon)
    have hxavoid : ∀ w ∈ G, inner ℝ x w ≠ 0 := by
      intro w hw hzero
      have hnotmem : x ∉ P w := fun hcon =>
        hx (Set.mem_iUnion.mpr ⟨⟨w, hw⟩, Set.mem_iUnion.mpr ⟨Finset.mem_attach _ _, hcon⟩⟩)
      apply hnotmem
      rw [hP, LinearMap.mem_ker]
      rw [show ((innerSL ℝ w : R3 →ₗ[ℝ] ℝ)) x = inner ℝ w x from rfl, real_inner_comm, hzero]
    -- Project orthogonally onto `e^⊥`: the pairing with every `w ∈ G ⊆ e^⊥` is unchanged.
    set x' : R3 := x - inner ℝ x e • e with hx'
    have hx'avoid : ∀ w ∈ G, inner ℝ x' w ≠ 0 := by
      intro w hw
      have hwperp : inner ℝ e w = 0 := hW w (Finset.mem_filter.mp hw).1
      have hval : inner ℝ x' w = inner ℝ x w := by
        rw [hx', inner_sub_left, real_inner_smul_left, hwperp, mul_zero, sub_zero]
      rw [hval]; exact hxavoid w hw
    have hx'ne : x' ≠ 0 := by
      intro h0
      obtain ⟨w, hw⟩ := hne
      exact hx'avoid w hw (by rw [h0, inner_zero_left])
    refine ⟨unitDir x', unitDir_norm x' hx'ne, ?_, ?_⟩
    · -- normalising preserves the orthogonality to `e`
      rw [inner_unitDir]
      have hxe : inner ℝ x' e = 0 := by
        rw [hx', inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he, one_pow,
          mul_one]
        ring
      rw [hxe, mul_zero]
    · -- normalising preserves the avoidance of the finitely many hyperplanes
      intro w hw hw0
      rw [inner_unitDir]
      have hwG : w ∈ G := Finset.mem_filter.mpr ⟨hw, hw0⟩
      exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hx'ne)) (hx'avoid w hwG)
  · -- `W` consists of zero vectors only: the condition is vacuous and `e₂` is a witness.
    refine ⟨e₂, he₂, horth, ?_⟩
    intro w hw hw0
    have hmem : w ∈ G := Finset.mem_filter.mpr ⟨hw, hw0⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hmem
    simp at hmem

end Work.Drive.Mono
