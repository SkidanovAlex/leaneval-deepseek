import Mathlib
import Submission.Commons.Combinatorics.MvPolynomial.augmentation_of_rayleigh
import Submission.Commons.Combinatorics.MvPolynomial.top_slice_MConvex
import Submission.Commons.Combinatorics.MvPolynomial.translate_package

open Finsupp Matrix MvPolynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.Combinatorics.MvPolynomial

noncomputable section

lemma my_degN_eq_degree (n : ℕ) (m : Fin n →₀ ℕ) : degN m = Finsupp.degree m := by
  rw [degN_eq_sum]
  exact (Finsupp.degree_eq_sum m).symm

/-- weight of a support element of a homogeneous polynomial is the degree -/
lemma my_support_degN (n : ℕ) {p : MvPolynomial (Fin n) ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) {m : Fin n →₀ ℕ} (hm : m ∈ p.support) : degN m = d := by
  have hc : p.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hz := (MvPolynomial.IsHomogeneous.coeff_eq_zero hp (d := m))
  by_contra hd
  apply hc
  exact hz (by simpa [my_degN_eq_degree n m] using hd)

/-- pointwise ≤ with equal weights forces equality -/
lemma my_eq_of_le_of_degN_eq (n : ℕ) {α γ : Fin n →₀ ℕ}
    (hle : ∀ k : Fin n, α k ≤ γ k) (hdeg : degN α = degN γ) : α = γ := by
  ext k
  by_contra hk
  have hkk : α k < γ k := lt_of_le_of_ne (hle k) (by intro h; exact hk h)
  have hlt : degN α < degN γ := by
    rw [degN_eq_sum, degN_eq_sum]
    exact Finset.sum_lt_sum (fun i hi => hle i) ⟨k, Finset.mem_univ k, hkk⟩
  omega

/-- main theorem: support of a homogeneous c-Rayleigh polynomial is M-convex -/
theorem support_MConvex_of_homogeneous_Rayleigh (n d : ℕ) (c : ℝ) (hc : 0 < c)
    (p : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m)
    (hhom : p.IsHomogeneous d)
    (hr : ∀ (l : List (Fin n)) (i j : Fin n) (w : Fin n → ℝ),
      (∀ k : Fin n, 0 ≤ w k) →
        MvPolynomial.eval w (l.foldl (fun q i => MvPolynomial.pderiv i q) p) *
            MvPolynomial.eval w ((i :: j :: l).foldl (fun q i => MvPolynomial.pderiv i q) p) ≤
          c * (MvPolynomial.eval w ((i :: l).foldl (fun q i => MvPolynomial.pderiv i q) p) *
            MvPolynomial.eval w ((j :: l).foldl (fun q i => MvPolynomial.pderiv i q) p))) :
    Commons.LorentzianPolynomials.IsMConvex (p.support : Set (Fin n →₀ ℕ)) := by
  classical
  by_cases hp0 : p = 0
  · subst p
    unfold Commons.LorentzianPolynomials.IsMConvex
    intro α hα
    have hfalse : False := by simpa using hα
    exact False.elim hfalse
  · let g : MvPolynomial (Fin n) ℝ :=
      MvPolynomial.bind₁ (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C 1) p
    have hTp := translate_package n d c hc p hhom hp0 hnn hr
    rcases hTp with ⟨hRayg, hnn_g, hsupp, hweights, h0g⟩
    have h0 : g.coeff 0 ≠ 0 := MvPolynomial.mem_support_iff.mp h0g
    let T : Set (Fin n →₀ ℕ) := fun γ => γ ∈ g.support
    have haug : ∀ α ∈ T, ∀ β ∈ T, (∑ i : Fin n, α i) < (∑ i : Fin n, β i) →
        ∃ j : Fin n, α j < β j ∧ α + Finsupp.single j 1 ∈ T := by
      intro α hα β hβ hlt
      rcases (augmentation_of_rayleigh n c hc g hnn_g h0 hRayg α hα β hβ hlt) with ⟨j, hj, hmem⟩
      exact ⟨j, hj, hmem⟩
    have hdown : ∀ α ∈ T, ∀ γ : Fin n →₀ ℕ, (∀ k : Fin n, γ k ≤ α k) → γ ∈ T := by
      intro α hα γ hle
      rcases (hsupp α).mp hα with ⟨a, ha, hαle⟩
      exact (hsupp γ).mpr ⟨a, ha, fun k => le_trans (hle k) (hαle k)⟩
    have hTop := top_slice_MConvex n d T hweights hdown haug
    have hset : {m : Fin n →₀ ℕ | m ∈ T ∧ (∑ i : Fin n, m i) = d} =
        (p.support : Set (Fin n →₀ ℕ)) := by
      ext m
      constructor
      · intro h
        rcases h with ⟨hmT, hsum⟩
        rcases (hsupp m).mp hmT with ⟨a, ha, hmle⟩
        have hdegm : degN m = d := by
          rw [degN_eq_sum]
          exact hsum
        have hdega : degN a = d := my_support_degN n hhom ha
        have hEq : m = a := my_eq_of_le_of_degN_eq n hmle (by rw [hdegm, hdega])
        simpa [hEq] using ha
      · intro hm
        constructor
        · exact (hsupp m).mpr ⟨m, hm, fun k => le_rfl⟩
        · have hdeg : degN m = d := my_support_degN n hhom hm
          exact (degN_eq_sum m).symm.trans hdeg
    have hfin : Commons.LorentzianPolynomials.IsMConvex (p.support : Set (Fin n →₀ ℕ)) := by
      rw [← hset]
      exact hTop
    exact hfin

end

end Commons.Combinatorics.MvPolynomial
