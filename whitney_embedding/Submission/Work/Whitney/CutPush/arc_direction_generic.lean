import Mathlib
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Whitney.CutPush.arc_straightening

/-!
# Genericity of the straightening direction for an arc

A smooth injective regular arc `c` on `[0,1]` in `ℝ^m`, `m ≥ 4`, admits a direction `v ≠ 0` such
that

* no chord `c t - c t'` (`t ≠ t'` in `[0,1]`) is a multiple of `v` (`ChordFree c v`), and
* no tangent `fderiv ℝ c t 1` is a multiple of `v`.

This is the Sard-flavoured genericity input of the arc-straightening argument.  It is proved here by
the Hausdorff-dimension substitute for Sard: the set of bad directions is the union of the images of
two explicitly parametrised `C¹` maps, from a `3`-dimensional and a `2`-dimensional domain
respectively, so its Hausdorff dimension is at most `3 < m = dim ℝ^m`; a bad direction therefore
cannot exhaust `ℝ^m`.
-/

open scoped Manifold ContDiff
open Topology MeasureTheory

namespace Work.Whitney.CutPush

/-- **Genericity of the straightening direction.** -/
theorem arc_direction_generic {m : ℕ} (hm : 4 ≤ m) (c : ℝ → EuclideanSpace ℝ (Fin m))
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c)
    (hinj : Set.InjOn c (Set.Icc (0 : ℝ) 1))
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1, fderiv ℝ c t 1 ≠ 0) :
    ∃ v : EuclideanSpace ℝ (Fin m), v ≠ 0 ∧ ChordFree c v ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ μ : ℝ, fderiv ℝ c t 1 ≠ μ • v) := by
  classical
  have hsmC : ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × ℝ => p.2⁻¹ • (c p.1.1 - c p.1.2))
      {p | p.2 ≠ 0} := by
    have hinv : ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × ℝ => p.2⁻¹) {p | p.2 ≠ 0} := by
      refine ContDiffOn.inv ?_ ?_
      · fun_prop
      · intro p hp; exact hp
    have hrest : ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × ℝ => c p.1.1 - c p.1.2) {p | p.2 ≠ 0} := by
      have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × ℝ) × ℝ => p.1.1) Set.univ := by
        fun_prop
      have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × ℝ) × ℝ => p.1.2) Set.univ := by
        fun_prop
      have hc0 : ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × ℝ => c p.1.1) Set.univ :=
        ((hc.contDiffOn (s := Set.univ)).comp h0 (fun p _ => Set.mem_univ _)).of_le (by norm_num)
      have hc1 : ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × ℝ => c p.1.2) Set.univ :=
        ((hc.contDiffOn (s := Set.univ)).comp h1 (fun p _ => Set.mem_univ _)).of_le (by norm_num)
      exact (hc0.sub hc1).mono (Set.subset_univ _)
    exact ContDiffOn.smul (𝕜' := ℝ) hinv hrest
  have hsmT : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => p.2⁻¹ • fderiv ℝ c p.1 1) {p | p.2 ≠ 0} := by
    have hfd : ContDiffOn ℝ 1 (fun t : ℝ => fderiv ℝ c t 1) Set.univ := by
      have hfd' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => fderiv ℝ c t) := by
        have h := (contDiffOn_infty_iff_fderiv_of_isOpen (𝕜 := ℝ) (f := c) (s := Set.univ)
          isOpen_univ).mp (hc.contDiffOn (s := Set.univ))
        exact contDiffOn_univ.mp h.2
      have h1 := hfd'.clm_apply
        (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (1:ℝ)))
      exact (h1.of_le (by norm_num)).contDiffOn (s := Set.univ)
    have hinv : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (p.2)⁻¹) {p | p.2 ≠ 0} := by
      refine ContDiffOn.inv ?_ ?_
      · fun_prop
      · intro p hp; exact hp
    have hcomp : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ c p.1 1) {p | p.2 ≠ 0} :=
      hfd.comp (by fun_prop) (fun p _ => Set.mem_univ _)
    exact ContDiffOn.smul (𝕜' := ℝ) hinv hcomp
  have hUopen3 : IsOpen {p : (ℝ × ℝ) × ℝ | p.2 ≠ 0} := by
    rw [show {p : (ℝ × ℝ) × ℝ | p.2 ≠ 0} = (fun p => p.2) ⁻¹' ({0}ᶜ : Set ℝ) from rfl]
    exact isOpen_compl_singleton.preimage (by fun_prop)
  have hUopen2 : IsOpen {p : ℝ × ℝ | p.2 ≠ 0} := by
    rw [show {p : ℝ × ℝ | p.2 ≠ 0} = (fun p => p.2) ⁻¹' ({0}ᶜ : Set ℝ) from rfl]
    exact isOpen_compl_singleton.preimage (by fun_prop)
  set badC : Set (EuclideanSpace ℝ (Fin m)) :=
    (fun p : (ℝ × ℝ) × ℝ => p.2⁻¹ • (c p.1.1 - c p.1.2)) ''
      {p | p.1.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.1.2 ∈ Set.Icc (0:ℝ) 1 ∧ p.2 ≠ 0} with hbadC
  set badT : Set (EuclideanSpace ℝ (Fin m)) :=
    (fun p : ℝ × ℝ => p.2⁻¹ • fderiv ℝ c p.1 1) ''
      {p | p.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2 ≠ 0} with hbadT
  have hdimC : dimH badC ≤ 3 := by
    have h := Work.Projection.dimH_image_le_of_contDiffOn (E := (ℝ × ℝ) × ℝ)
      (F := EuclideanSpace ℝ (Fin m)) (U := {p | p.2 ≠ 0}) hUopen3 hsmC
      (s := {p | p.1.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.1.2 ∈ Set.Icc (0:ℝ) 1 ∧ p.2 ≠ 0})
      (fun p hp => hp.2.2)
    rw [hbadC]
    simpa using h
  have hdimT : dimH badT ≤ 2 := by
    have h := Work.Projection.dimH_image_le_of_contDiffOn (E := ℝ × ℝ)
      (F := EuclideanSpace ℝ (Fin m)) (U := {p | p.2 ≠ 0}) hUopen2 hsmT
      (s := {p | p.1 ∈ Set.Icc (0:ℝ) 1 ∧ p.2 ≠ 0}) (fun p hp => hp.2)
    rw [hbadT]
    simpa using h
  have hbound : dimH (badC ∪ badT) ≤ 3 := by
    rw [dimH_union]
    exact max_le hdimC (le_trans hdimT (by norm_num))
  have hlt : dimH (badC ∪ badT) < dimH (Set.univ : Set (EuclideanSpace ℝ (Fin m))) := by
    rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin]
    refine lt_of_le_of_lt hbound ?_
    exact_mod_cast (by omega : 3 < m)
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin m), v ∉ badC ∪ badT := by
    by_contra h
    rw [not_exists] at h
    simp only [not_not] at h
    have hbad : badC ∪ badT = Set.univ := Set.eq_univ_iff_forall.2 h
    rw [hbad] at hlt
    exact lt_irrefl _ hlt
  rw [Set.mem_union, not_or] at hv
  obtain ⟨hvC, hvT⟩ := hv
  refine ⟨v, ?_, ?_, ?_⟩
  · intro h0
    apply hvC
    refine ⟨((0, 0), 1), ⟨by norm_num, by norm_num, by norm_num⟩, ?_⟩
    simp [h0]
  · intro t ht t' ht' hne α hcon
    have hα : α ≠ 0 := by
      intro h0
      rw [h0, zero_smul, sub_eq_zero] at hcon
      exact hne (hinj ht ht' hcon)
    refine hvC ⟨((t, t'), α), ⟨ht, ht', hα⟩, ?_⟩
    show α⁻¹ • (c t - c t') = v
    rw [hcon, inv_smul_smul₀ hα]
  · intro t ht μ hcon
    by_cases hμ : μ = 0
    · exact hreg t ht (by rw [hcon, hμ, zero_smul])
    · refine hvT ⟨(t, μ), ⟨ht, hμ⟩, ?_⟩
      show μ⁻¹ • (fderiv ℝ c t) 1 = v
      rw [hcon, inv_smul_smul₀ hμ]

end Work.Whitney.CutPush
