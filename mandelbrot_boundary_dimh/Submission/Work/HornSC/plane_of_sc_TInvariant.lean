import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.HornSC.sc_compl_component_unbounded
import Submission.Work.HornSC.separates_strip_tinvariant

namespace Work.HornSC

open MandelDim
open Set

/-! Shishikura, Prop. 5.3 (last part).  An open connected simply connected `T`-invariant
(`T w = w + 1`) subset `X ⊆ ℂ` that contains the complement `{|Im w| > η}` of a horizontal strip
must be all of `ℂ`.

The proof is the one indicated in the paper (`$\tilde B^u = \tilde B^\ell = \C$`): writing
`A = Xᶜ ⊆ {|Im| ≤ η}`, `A` is closed and `T`-invariant.  By `sc_compl_component_unbounded`
(simply connected plane domains have no bounded complementary component) every component of `A`
is unbounded; by `separates_strip_tinvariant` an unbounded component of `A` forces the two half
planes `{Im > η}` and `{Im < -η}` to lie in *different* components of `Aᶜ = X`.  But both points
`i(η+1)` and `-i(η+1)` lie in `X` (as `|Im| = |η+1| > η`), and `X` is connected.  Contradiction. -/

theorem plane_of_sc_TInvariant (X : Set ℂ) (hXo : IsOpen X) (hXc : IsConnected X)
    (hXsc : SimplyConnectedSpace ↥X) (hXT : MandelDim.IsTInvariant X) (η : ℝ)
    (hη : {w : ℂ | η < |w.im|} ⊆ X) : X = Set.univ := by
  by_contra hne
  -- `Xᶜ` is non-empty and contained in the closed strip `{|Im| ≤ η}`
  have hAne : (Xᶜ).Nonempty := by rwa [nonempty_compl]
  obtain ⟨z, hz⟩ := hAne
  have hsub : Xᶜ ⊆ {w : ℂ | |w.im| ≤ η} := by
    intro w hw
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hw ⊢
    by_contra h
    exact hw (hη (by simpa using h))
  -- `Xᶜ` is `T`-invariant
  have hAT : MandelDim.IsTInvariant Xᶜ := by
    intro w
    simp only [Set.mem_compl_iff]
    exact not_congr (hXT w)
  -- some component of `Xᶜ` is unbounded
  have hC : ∃ z ∈ Xᶜ, ¬ Bornology.IsBounded (connectedComponentIn Xᶜ z) :=
    ⟨z, hz, sc_compl_component_unbounded X hXo hXc hXsc hz⟩
  -- hence `{Im > η}` and `{Im < -η}` lie in different components of `(Xᶜ)ᶜ = X`
  have hsep := separates_strip_tinvariant η Xᶜ hXo.isClosed_compl hAT hsub hC
  -- the two witness points
  have hyim : (Complex.I * ((η : ℂ) + 1)).im = η + 1 := by
    rw [Complex.I_mul_im, Complex.add_re, Complex.ofReal_re, Complex.one_re]
  have hzim : (-(Complex.I * ((η : ℂ) + 1))).im = -(η + 1) := by
    rw [Complex.neg_im, hyim]
  have hy : (Complex.I * ((η : ℂ) + 1)) ∈ {w : ℂ | η < w.im} := by
    simp only [Set.mem_setOf_eq, hyim]
    exact lt_add_of_pos_right η one_pos
  have hz' : (-(Complex.I * ((η : ℂ) + 1))) ∈ {w : ℂ | w.im < -η} := by
    simp only [Set.mem_setOf_eq, hzim]
    linarith
  have hyX : (Complex.I * ((η : ℂ) + 1)) ∈ X := by
    apply hη
    simp only [Set.mem_setOf_eq, hyim]
    rw [lt_abs]
    exact Or.inl (by linarith)
  have hz'X : (-(Complex.I * ((η : ℂ) + 1))) ∈ X := by
    apply hη
    simp only [Set.mem_setOf_eq, hzim]
    rw [abs_neg, lt_abs]
    exact Or.inl (by linarith)
  -- both points are in `X`, which is preconnected, so they lie in the same component of `X`
  have hcc : ∀ {y : ℂ}, y ∈ X → connectedComponentIn ((Xᶜ)ᶜ) y = X := by
    intro y hy
    rw [compl_compl]
    refine Subset.antisymm (fun a ha => connectedComponentIn_subset X y ha) ?_
    exact fun a ha => IsPreconnected.subset_connectedComponentIn hXc.isPreconnected hy
      (subset_refl X) ha
  exact hsep _ hy _ hz' ((hcc hyX).trans (hcc hz'X).symm)

end Work.HornSC
