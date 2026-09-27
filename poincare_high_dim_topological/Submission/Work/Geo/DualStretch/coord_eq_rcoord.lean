import Mathlib
import Submission.Work.Geo.DualStretch.Local
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.carrier_spec
import Submission.Work.Geo.DualStretch.coord_spec

/-!
# `coord` and `rcoord` agree on a face

`Work.Geo.DualStretch.coord P x` is defined through the carrier face of `x`: it picks, by
`Classical.choose`, a weight function `μ` on `carrier P x` with `μ ≥ 0`, `∑ μ = 1` and
`∑ μ w • w = x`.  `Work.Geo.DualStretch.rcoord σ x` is defined in exactly the same way but with
respect to a fixed face `σ`.  Whenever `σ` is a face of `P` and `x ∈ PL.simp σ`, the carrier face is
a subface of `σ` and the two weight functions agree on `σ`: barycentric coordinates of a point with
respect to an affinely independent vertex set are unique.

The uniqueness statement is `eq_on_of_sum_eq_one_of_sum_smul_eq` below; the point of the present
lemma is that, although `coord` and `rcoord` make *different* arbitrary choices, the two chosen
functions coincide on `σ` once one of them is extended by `0` from the carrier face to `σ`.
-/

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

variable {n : ℕ}

/-- **Uniqueness of barycentric coordinates.**  If `S` is affinely independent and two weight
functions `μ`, `ν` both have total mass `1` and centre of mass `x` on `S`, then `μ` and `ν` agree on
`S`.  (Affine combinations with prescribed centre of mass are unique over an affinely independent
family.) -/
theorem eq_on_of_sum_eq_one_of_sum_smul_eq {n : ℕ} {S : Finset (PL.E n)}
    (hS : AffineIndependent ℝ ((↑) : ↥S → PL.E n)) {x : PL.E n} {μ ν : PL.E n → ℝ}
    (hμ1 : ∑ w ∈ S, μ w = 1) (hμ2 : ∑ w ∈ S, μ w • w = x)
    (hν1 : ∑ w ∈ S, ν w = 1) (hν2 : ∑ w ∈ S, ν w • w = x) :
    ∀ v ∈ S, μ v = ν v := by
  have hμ1' : ∑ w ∈ S.attach, μ (w : PL.E n) = 1 := by
    rw [Finset.sum_attach]; exact hμ1
  have hν1' : ∑ w ∈ S.attach, ν (w : PL.E n) = 1 := by
    rw [Finset.sum_attach]; exact hν1
  have hμA : (Finset.affineCombination ℝ S.attach (fun w : ↥S => (w : PL.E n)))
      (fun w => μ (w : PL.E n)) = x := by
    rw [Finset.affineCombination_eq_linear_combination S.attach _ _ hμ1']
    exact (Finset.sum_attach S (fun w => μ w • w)).trans hμ2
  have hνA : (Finset.affineCombination ℝ S.attach (fun w : ↥S => (w : PL.E n)))
      (fun w => ν (w : PL.E n)) = x := by
    rw [Finset.affineCombination_eq_linear_combination S.attach _ _ hν1']
    exact (Finset.sum_attach S (fun w => ν w • w)).trans hν2
  have heq : (Finset.affineCombination ℝ S.attach (fun w : ↥S => (w : PL.E n)))
        (fun w => μ (w : PL.E n))
      = (Finset.affineCombination ℝ S.attach (fun w : ↥S => (w : PL.E n)))
        (fun w => ν (w : PL.E n)) := by
    rw [hμA, hνA]
  intro v hv
  exact (hS.affineCombination_eq_iff_eq hμ1' hν1').mp heq ⟨v, hv⟩ (Finset.mem_attach S ⟨v, hv⟩)

theorem coord_eq_rcoord {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {σ : Finset (PL.E n)}
    (hσ : σ ∈ P.faces) {x : PL.E n} (hx : x ∈ PL.simp σ) (v : PL.E n) :
    Work.Geo.DualStretch.coord P x v = Work.Geo.DualStretch.rcoord σ x v := by
  classical
  -- `x` lies in the complex, so it has a carrier face, which is a subface of `σ`.
  have hxsp : x ∈ P.space := Geometry.SimplicialComplex.convexHull_subset_space hσ hx
  obtain ⟨hcarF, hcarx, hcarsub⟩ := carrier_spec P hP hxsp
  have hSσ : carrier P x ⊆ σ := hcarsub σ hσ hx
  have hindσ : AffineIndependent ℝ ((↑) : ↥σ → PL.E n) := P.indep hσ
  -- The witness of the carrier-face existential and the witness of the `σ`-existential.
  set hex := exists_coordOn_of_mem_simp (σ := carrier P x) hcarx with hhex
  set hr := exists_coordOn_of_mem_simp (σ := σ) hx with hhr
  obtain ⟨-, hex1, hex2⟩ := hex.choose_spec
  obtain ⟨-, hr1, hr2⟩ := hr.choose_spec
  -- Extend the carrier witness to `σ` by zero.
  have hA : ∑ w ∈ σ, (if w ∈ carrier P x then hex.choose w else 0) = 1 := by
    have h1 : ∑ w ∈ σ, (if w ∈ carrier P x then hex.choose w else 0)
        = ∑ w ∈ carrier P x, (if w ∈ carrier P x then hex.choose w else 0) :=
      (Finset.sum_subset hSσ (fun w _ hw => by simp [hw])).symm
    rw [h1]
    have h2 : ∑ w ∈ carrier P x, (if w ∈ carrier P x then hex.choose w else 0)
        = ∑ w ∈ carrier P x, hex.choose w :=
      Finset.sum_congr rfl (fun w hw => by simp [hw])
    rw [h2]; exact hex1
  have hB : ∑ w ∈ σ, (if w ∈ carrier P x then hex.choose w else 0) • w = x := by
    have h1 : ∑ w ∈ σ, (if w ∈ carrier P x then hex.choose w else 0) • w
        = ∑ w ∈ carrier P x, (if w ∈ carrier P x then hex.choose w else 0) • w :=
      (Finset.sum_subset hSσ (fun w _ hw => by simp [hw])).symm
    rw [h1]
    have h2 : ∑ w ∈ carrier P x, (if w ∈ carrier P x then hex.choose w else 0) • w
        = ∑ w ∈ carrier P x, hex.choose w • w :=
      Finset.sum_congr rfl (fun w hw => by simp [hw])
    rw [h2]; exact hex2
  -- Uniqueness on `σ`: the `σ`-witness agrees with the zero-extension of the carrier witness.
  have hkey : ∀ w ∈ σ, hr.choose w = (if w ∈ carrier P x then hex.choose w else 0) :=
    eq_on_of_sum_eq_one_of_sum_smul_eq hindσ hr1 hr2 hA hB
  -- Unfold the two definitions and compare.
  have hc : coord P x v = (if v ∈ carrier P x then hex.choose v else 0) := by
    simp only [coord]
    by_cases hv : v ∈ carrier P x
    · rw [dite_eq_left hv, dite_eq_left hex]
      simp [hv]
    · rw [dite_eq_right hv]
      simp [hv]
  have hr' : rcoord σ x v = (if v ∈ σ then hr.choose v else 0) := by
    simp only [rcoord]
    rw [dite_eq_left hx]
    by_cases hv : v ∈ σ
    · rw [dite_eq_left hv, dite_eq_left hr]
      simp [hv]
    · rw [dite_eq_right hv]
      simp [hv]
  rw [hc, hr']
  by_cases hv : v ∈ carrier P x
  · have hvσ : v ∈ σ := hSσ hv
    rw [ite_eq_left hv, ite_eq_left hvσ]
    have h := hkey v hvσ
    rw [ite_eq_left hv] at h
    exact h.symm
  · rw [ite_eq_right hv]
    by_cases hvσ : v ∈ σ
    · rw [ite_eq_left hvσ]
      have h := hkey v hvσ
      rw [ite_eq_right hv] at h
      exact h.symm
    · rw [ite_eq_right hvσ]

end Work.Geo.DualStretch
