import Mathlib
import Submission.Work.Drive.meet32_bordism_invariance
import Submission.Work.Drive.TripleGeneral

/-!
# Transferring `Meet3Hyp` along box reparametrisations

`Work.Drive.Meet3Hyp M D` (`Submission/Work/Drive/meet32_bordism_invariance.lean`) is the packaged
hypothesis of the triple-intersection parity engine: smoothness of the three chains, transversality of
the triple at every meeting point of the box, the face condition, and the seam invariance of each
chain.

This module proves the **transfer**: if `Θ k` is a `C^∞` self-map of `𝔼³` which maps the unit box
bijectively onto itself, preserves each face (`(Θ k x) i = 0 ↔ x i = 0`, and likewise for `1`), has an
invertible derivative on the box, and has a derivative which preserves the *coordinate hyperplanes*
along the faces (`(dΘ x v) i = 0 ↔ v i = 0` for `x i ∈ {0,1}`), then `Meet3Hyp M (D k ∘ Θ k)` implies
`Meet3Hyp M D`.

This is the step that lets a Sard argument be run on a *sheared* family (where the richness of the
parametric Sard is available) while the conclusion is stated for the original encoded chains.  The
proof is the pull-back of the triple points of `D` along the inverses of the `Θ k`: transversality is
composed with the (surjective) derivatives of `Θ k`, the face condition is transported by the
face-preservation, and the common direction by the hyperplane-preservation.

This module is item **§2.4** of the project lead's `NOTES_LEAD_hodd_blockT6.md`; the statement of
`Work.Drive.meet3Hyp_of_boxReparam` is the lead's, verbatim.  It is **proved here** (sorry-free,
axiom-clean) — see `BOXREPARAM_STATUS.md` for the proof shape, the Lean traps, and a pointer to the
consumers (§2.1 `encodedGeneric.lean`, §2.5 `hasClassLinearization_of_endData.lean`).  **Do not
re-declare `meet3Hyp_of_boxReparam`, `tripleTransverse_of_comp` or `tripleCommonDir_of_comp` in
another module**: the two helpers are the linear core (transversality and the common-direction
condition survive precomposition by surjective maps).
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

/-- The order `⊤` is not zero. -/
private lemma m3r_top_ne_zero_order : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- **Transversality survives precomposition by surjective maps** (the linear core of the transfer). -/
theorem tripleTransverse_of_comp
    (f : Fin 3 → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : Fin 3 → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (h : TripleTransverse (f 0 ∘SL g 0) (f 1 ∘SL g 1) (f 2 ∘SL g 2))
    (hg : ∀ k : Fin 3, Function.Surjective (g k)) :
    TripleTransverse (f 0) (f 1) (f 2) := by
  intro w₁ w₂
  obtain ⟨v, hv₁, hv₂⟩ := h w₁ w₂
  refine ⟨fun k => g k (v k), ?_, ?_⟩
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hv₁
    exact hv₁
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hv₂
    exact hv₂

/-- **The common-direction condition survives precomposition.** -/
theorem tripleCommonDir_of_comp
    (f : Fin 3 → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : Fin 3 → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (h : TripleCommonDir (f 0 ∘SL g 0) (f 1 ∘SL g 1) (f 2 ∘SL g 2) v) :
    TripleCommonDir (f 0) (f 1) (f 2) (fun k => g k (v k)) := by
  constructor
  · simpa only [ContinuousLinearMap.comp_apply] using h.1
  · simpa only [ContinuousLinearMap.comp_apply] using h.2

/-- **The transfer of `Meet3Hyp` along a box reparametrisation.**  See the module docstring. -/
theorem meet3Hyp_of_boxReparam {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (Θ : Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hsm : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (hseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), onSeam x → D k x = D k (seamInv x))
    (hΘ : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Θ k))
    (hbij : ∀ k, Set.BijOn (Θ k) (Submission.Drive.unitBox 2) (Submission.Drive.unitBox 2))
    (hface : ∀ k, ∀ x ∈ Submission.Drive.unitBox 2, ∀ i : Fin 3,
      ((Θ k x) i = 0 ↔ x i = 0) ∧ ((Θ k x) i = 1 ↔ x i = 1))
    (hinv : ∀ k, ∀ x ∈ Submission.Drive.unitBox 2, Function.Bijective (fderiv ℝ (Θ k) x))
    (hnormal : ∀ k, ∀ x ∈ Submission.Drive.unitBox 2, ∀ i : Fin 3, (x i = 0 ∨ x i = 1) →
      ∀ v : EuclideanSpace ℝ (Fin 3), ((fderiv ℝ (Θ k) x v) i = 0 ↔ v i = 0))
    (h : Meet3Hyp M (fun k => D k ∘ Θ k)) :
    Meet3Hyp M D := by
  have hT : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 3)), MDiffAt (Θ k) y := by
    intro k y
    exact ((contMDiffAt_iff_contDiffAt).mpr ((hΘ k).contDiffAt)).mdifferentiableAt
      m3r_top_ne_zero_order
  have hD : ∀ (k : Fin 3) (z : EuclideanSpace ℝ (Fin 3)),
      MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D k) z := by
    intro k z
    exact ((hsm k).contMDiffAt).mdifferentiableAt m3r_top_ne_zero_order
  -- pull a triple point back along the `Θ`
  have hpull : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      D 0 (x 0) = D 1 (x 1) → D 0 (x 0) = D 2 (x 2) →
      ∃ y : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, y k ∈ Submission.Drive.unitBox 2) ∧ (∀ k, Θ k (y k) = x k) ∧
        ((fun k => D k ∘ Θ k) 0 (y 0) = (fun k => D k ∘ Θ k) 1 (y 1)) ∧
        ((fun k => D k ∘ Θ k) 0 (y 0) = (fun k => D k ∘ Θ k) 2 (y 2)) := by
    intro x hx h01 h02
    have hsurj : ∀ k : Fin 3, ∃ y ∈ Submission.Drive.unitBox 2, Θ k y = x k :=
      fun k => (hbij k).surjOn (hx k)
    choose y hybox hyval using hsurj
    exact ⟨y, hybox, hyval, by
        simp only [Function.comp_apply]; rw [hyval 0, hyval 1]; exact h01, by
        simp only [Function.comp_apply]; rw [hyval 0, hyval 2]; exact h02⟩
  -- the derivative of `D k ∘ Θ k` at `y k` as the composite with `d Θ k`
  have hmfd : ∀ (k : Fin 3) (y x : Fin 3 → EuclideanSpace ℝ (Fin 3)),
      (∀ k, Θ k (y k) = x k) →
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D k ∘ Θ k) (y k)
        = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D k) (x k)).comp
          (fderiv ℝ (Θ k) (y k)) := by
    intro k y x hyval
    have hcomp := mfderiv_comp (f := Θ k) (g := D k) (x := y k)
      (hD k (Θ k (y k))) (hT k (y k))
    rw [mfderiv_eq_fderiv, hyval k] at hcomp
    exact hcomp
  refine ⟨hsm, ?_, ?_, hseam⟩
  · -- transversality
    intro x hx h01 h02
    obtain ⟨y, hybox, hyval, htri01, htri02⟩ := hpull x hx h01 h02
    have h0 := h.trans y hybox htri01 htri02
    rw [hmfd 0 y x hyval, hmfd 1 y x hyval, hmfd 2 y x hyval] at h0
    refine tripleTransverse_of_comp (fun k => mfderiv (modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin 3))) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (D k) (x k)) (fun k => fderiv ℝ (Θ k) (y k)) h0 ?_
    intro k
    exact (hinv k (y k) (hybox k)).2
  · -- the face condition
    intro x hx h01 h02 hbdry
    obtain ⟨y, hybox, hyval, htri01, htri02⟩ := hpull x hx h01 h02
    -- `y` meets the boundary of the box
    have hybdry : ∃ k, y k ∈ Submission.Drive.unitBoxBdry 2 := by
      obtain ⟨k, hk⟩ := hbdry
      simp only [Submission.Drive.unitBoxBdry, Set.mem_setOf_eq] at hk
      obtain ⟨-, i, hi⟩ := hk
      refine ⟨k, hybox k, i, ?_⟩
      rcases hi with hi | hi
      · exact Or.inl (((hface k (y k) (hybox k) i).1).mp (by rw [hyval k]; exact hi))
      · exact Or.inr (((hface k (y k) (hybox k) i).2).mp (by rw [hyval k]; exact hi))
    obtain ⟨k, i, hki, hrest, hothers, v, hvdir, hvne⟩ :=
      h.face y hybox htri01 htri02 hybdry
    -- the interiors transfer
    have hinter : ∀ (k' : Fin 3) (j : Fin 3),
        x k' j ∈ Set.Ioo (0 : ℝ) 1 ↔ y k' j ∈ Set.Ioo (0 : ℝ) 1 := by
      intro k' j
      have h1 : (0 : ℝ) ≤ x k' j ∧ x k' j ≤ 1 := by
        have hh := hx k'; rw [Submission.Drive.unitBox, Set.mem_setOf_eq] at hh
        exact hh j
      have h2 : (0 : ℝ) ≤ y k' j ∧ y k' j ≤ 1 := by
        have hh := hybox k'; rw [Submission.Drive.unitBox, Set.mem_setOf_eq] at hh
        exact hh j
      have hx0 : x k' j = 0 ↔ y k' j = 0 := by
        rw [← hyval k']; exact (hface k' (y k') (hybox k') j).1
      have hx1 : x k' j = 1 ↔ y k' j = 1 := by
        rw [← hyval k']; exact (hface k' (y k') (hybox k') j).2
      constructor
      · intro hh
        exact ⟨lt_of_le_of_ne h2.1 (fun h => hh.1.ne' (hx0.mpr h.symm)),
          lt_of_le_of_ne h2.2 (fun h => hh.2.ne' (hx1.mpr h).symm)⟩
      · intro hh
        exact ⟨lt_of_le_of_ne h1.1 (fun h => hh.1.ne' (hx0.mp h.symm)),
          lt_of_le_of_ne h1.2 (fun h => hh.2.ne' (hx1.mp h).symm)⟩
    have hxki : x k i = 0 ∨ x k i = 1 := by
      rw [← hyval k]
      rcases hki with hki | hki
      · exact Or.inl (((hface k (y k) (hybox k) i).1).mpr hki)
      · exact Or.inr (((hface k (y k) (hybox k) i).2).mpr hki)
    rw [hmfd 0 y x hyval, hmfd 1 y x hyval, hmfd 2 y x hyval] at hvdir
    obtain ⟨hdir, hdir'⟩ := tripleCommonDir_of_comp
      (fun k => mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (D k) (x k))
      (fun k => fderiv ℝ (Θ k) (y k)) v hvdir
    refine ⟨k, i, hxki, fun j hj => (hinter k j).mpr (hrest j hj),
      fun k' hk' j => (hinter k' j).mpr (hothers k' hk' j), ?_⟩
    refine ⟨fun k' => fderiv ℝ (Θ k') (y k') (v k'), ⟨hdir, hdir'⟩, ?_⟩
    · intro hzero
      exact hvne ((hnormal k (y k) (hybox k) i hki (v k)).mp hzero)

end

end Work.Drive
