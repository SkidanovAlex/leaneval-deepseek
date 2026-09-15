import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section

namespace Commons.Analysis.Approximation

open Finset
open scoped BigOperators

/-- **Multivariate Weierstrass approximation.**  A continuous function on the cube
`[-I, I]^K` is uniformly approximated by a polynomial in `K` variables. -/
theorem exists_mvpolynomial_near_of_continuousOn {K : ℕ} (I : ℝ) (hI : 0 ≤ I)
    (Φ : (Fin K → ℝ) → ℝ)
    (hΦ : ContinuousOn Φ (Set.pi Set.univ (fun _ : Fin K => Set.Icc (-I) I)))
    {η : ℝ} (hη : 0 < η) :
    ∃ P : MvPolynomial (Fin K) ℝ, ∀ x ∈ Set.pi Set.univ (fun _ : Fin K => Set.Icc (-I) I),
      |Φ x - MvPolynomial.eval x P| ≤ η := by
  set s : Set (Fin K → ℝ) := Set.pi Set.univ (fun _ : Fin K => Set.Icc (-I) I) with hs
  have hsc : IsCompact s := by
    rw [hs]
    exact isCompact_univ_pi (fun _ : Fin K => isCompact_Icc)
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp hsc
  let coord : Fin K → C(s, ℝ) :=
    fun i => ⟨fun x => (x : Fin K → ℝ) i, (continuous_apply i).comp continuous_subtype_val⟩
  let polyToCont : MvPolynomial (Fin K) ℝ →ₐ[ℝ] C(s, ℝ) := MvPolynomial.aeval coord
  let A : Subalgebra ℝ C(s, ℝ) := polyToCont.range
  have hsep : A.SeparatesPoints := by
    change ∀ ⦃x y : s⦄, x ≠ y →
      ∃ g : s → ℝ,
        g ∈ ((fun h : C(s, ℝ) => (h : s → ℝ)) '' (A : Set C(s, ℝ))) ∧ g x ≠ g y
    intro x y hxy
    have hxney : (x : Fin K → ℝ) ≠ (y : Fin K → ℝ) := Subtype.coe_injective.ne hxy
    have hdiff : ∃ i : Fin K, (x : Fin K → ℝ) i ≠ (y : Fin K → ℝ) i := by
      by_contra h
      push_neg at h
      exact hxney (funext h)
    rcases hdiff with ⟨i, hi⟩
    refine ⟨fun z : s => (z : Fin K → ℝ) i, ?_, hi⟩
    refine ⟨coord i, ?_, rfl⟩
    change coord i ∈ polyToCont.range
    exact (AlgHom.mem_range polyToCont).mpr ⟨MvPolynomial.X i, by simp [polyToCont, coord]⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    (A := A) hsep (fun x : s => Φ (x : Fin K → ℝ)) hΦ.domRestrict η hη
  have hmem : (g : C(s, ℝ)) ∈ polyToCont.range := by
    change (g : C(s, ℝ)) ∈ A
    exact g.2
  obtain ⟨P, hP⟩ := (AlgHom.mem_range polyToCont).mp hmem
  refine ⟨P, ?_⟩
  intro x hx
  have key : ∀ (Q : MvPolynomial (Fin K) ℝ) (z : s),
      polyToCont Q z = MvPolynomial.eval (z : Fin K → ℝ) Q := by
    intro Q z
    have h1 := MvPolynomial.comp_aeval_apply (f := coord)
      (φ := ContinuousMap.evalAlgHom ℝ ℝ z) (R := ℝ) (S₁ := C(s, ℝ)) Q
    rw [show polyToCont Q z =
          (ContinuousMap.evalAlgHom ℝ ℝ z) (MvPolynomial.aeval coord Q) from rfl, h1]
    rfl
  have hgx : (g : C(s, ℝ)) ⟨x, hx⟩ = MvPolynomial.eval x P := by
    rw [← hP, key P ⟨x, hx⟩]
  have hb : ‖(g : s → ℝ) ⟨x, hx⟩ - Φ x‖ < η := hg ⟨x, hx⟩
  have hlt : |MvPolynomial.eval x P - Φ x| < η := by
    rw [← hgx]
    simpa [Real.norm_eq_abs] using hb
  exact le_of_lt (by simpa [abs_sub_comm] using hlt)

end Commons.Analysis.Approximation
