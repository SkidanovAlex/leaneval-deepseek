/-
  WilC4/unifFinite_of_omin : uniform finiteness of `reexp`-existential families from
  o-minimality of every model of `TR`.

  `WilkiesDesign.CG.OMinModels` says that in every model `M ⊨ TR` every `LRc`-definable subset of
  the line is a finite union of order-convex sets.  Uniform finiteness — one bound for all
  parameters — is *not* a consequence of that statement taken in the standard model `ℝ` alone:
  it needs a nonstandard parameter.  The classical proof uses compactness: if the fibres of a
  family had arbitrarily many components, an ultraproduct would carry a *single* parameter whose
  fibre has arbitrarily many components, contradicting o-minimality of that model.

  Formally, the "arbitrarily many components" condition is replaced by the first-order condition
  `AltChain N` ("`N + 1` points of the fibre separated by `N` points outside it", see
  `UnifDefs.lean`), which is equivalent to "at least `N + 1` components" in any linear order.
  The ultraproduct is the hyperreal model `HR = Germ (hyperfilter ℕ) ℝ` of `HyperRealSetup.lean`;
  Łoś's theorem (`realize_hyper`) evaluates a formula at a germ of parameters on a set of indices,
  which is exactly what makes one parameter serve all `N` at once.

  The pieces used:
  * `exists_altChain_formula` : the first-order formula realising `AltChain N` in every model;
  * `realize_hyper` : Łoś's theorem for `HR`;
  * `not_altChain_of_ordConnected` : a fibre covered by `r` order-convex sets has no chain of
    length `r` (the model side);
  * `exists_cover_of_not_altChain` : conversely, no chain of length `N` over `ℝ` bounds the number
    of convex components by `N` (the real side);
  * `rexExist_fibre_formula` : `RExpExist` sets are given by a parametric `LRc`-formula.
-/
import Mathlib
import Submission.Work.WilC4.UnifDefs
import Submission.Work.WilC4.HyperRealCompat
import Submission.Work.WilC4.hsq_hyper
import Submission.Work.WilC4.realize_hyper
import Submission.Work.WilC4.TR_hyper
import Submission.Work.WilC4.exists_altChain_formula
import Submission.Work.WilC4.not_altChain_of_ordConnected
import Submission.Work.WilC4.exists_cover_of_not_altChain
import Submission.Work.WilC4.rexExist_fibre_formula
import Submission.Work.WilC2.Square

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4

/-- **The uniform bound.**  For a parametric `LRc`-family of subsets of the line, o-minimality of
every model of `TR` bounds the number of convex components of *all* the fibres at once. -/
theorem exists_alt_bound (hOM : WilkiesDesign.CG.OMinModels) {n : ℕ}
    (φ : LRc.Formula (Fin n ⊕ Fin 1)) :
    ∃ N : ℕ, ∀ p : Fin n → ℝ,
      ¬ AltChain N {t : ℝ | φ.Realize (Sum.elim p (fun _ => t))} := by
  by_contra hcon
  push_neg at hcon
  choose c hc using hcon
  choose F hF using fun N => exists_altChain_formula φ N
  let pp : Fin n → HR := fun i => ↑(fun a => c a i)
  -- Łoś: the nonstandard parameter `pp` has an alternating chain of every length
  have hreal : ∀ N : ℕ, @Formula.Realize LRc HR instLRcHR (Fin n) (F N) pp := by
    intro N
    refine (realize_hyper (F N) (fun i a => c a i)).mpr ?_
    have hmem : Set.Ici N ∈ (Filter.hyperfilter ℕ : Filter ℕ) :=
      Nat.hyperfilter_le_atTop (Filter.Ici_mem_atTop N)
    filter_upwards [hmem] with a ha
    exact (hF N ℝ Work.WilC2.real_exists_sq (c a)).mpr
      (altChain_mono (hc a) (Set.mem_Ici.mp ha))
  have hTR' : @Theory.Model LRc HR lrcSum WilkiesDesign.CG.TR := by
    rw [lrcSum_eq]
    exact TR_hyper
  -- the fibre of the family at `pp` is definable
  have hdef0 : @Set.Definable HR Set.univ LRc instLRcHR (Fin 1)
      {x : Fin 1 → HR | φ.Realize (Sum.elim pp x)} := by
    rw [Set.definable_iff_exists_formula_sum]
    refine ⟨Formula.relabel (Sum.elim (fun i : Fin n =>
      (Sum.inl ⟨pp i, Set.mem_univ _⟩ : ↥(Set.univ : Set HR) ⊕ Fin 1))
      (fun j : Fin 1 => (Sum.inr j : ↥(Set.univ : Set HR) ⊕ Fin 1))) φ, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Formula.realize_relabel]
    have hcomp : (Sum.elim (fun a : ↥(Set.univ : Set HR) => (a : HR)) x) ∘
        (Sum.elim (fun i : Fin n =>
            (Sum.inl ⟨pp i, Set.mem_univ _⟩ : ↥(Set.univ : Set HR) ⊕ Fin 1))
          (fun j : Fin 1 => (Sum.inr j : ↥(Set.univ : Set HR) ⊕ Fin 1))) = Sum.elim pp x := by
      funext i
      rcases i with i | j
      · rfl
      · rfl
    rw [hcomp]
  have hdef : @Set.Definable HR Set.univ LRc lrcSum (Fin 1)
      {x : Fin 1 → HR | @Formula.Realize LRc HR lrcSum (Fin n ⊕ Fin 1) φ (Sum.elim pp x)} := by
    rw [lrcSum_eq]
    exact hdef0
  -- o-minimality of the model: the fibre is a finite union of order-convex sets
  obtain ⟨s, hord, hX⟩ :=
    @hOM HR _ _ _ instCompatHR instRexpLHR instConstHR hTR' _ hdef
  have hS : {t : HR | @Formula.Realize LRc HR lrcSum (Fin n ⊕ Fin 1) φ
        (Sum.elim pp (fun _ => t))} = ⋃₀ (s : Set (Set HR)) := by
    ext t
    have h1 := Set.ext_iff.mp hX (fun _ : Fin 1 => t)
    simpa using h1
  have hnot := not_altChain_of_ordConnected hS hord
  have hreal' : @Formula.Realize LRc HR lrcSum (Fin n) (F s.card) pp := by
    rw [lrcSum_eq]
    exact hreal s.card
  exact hnot ((hF s.card HR hsq_hyper pp).mp hreal')

/-- **Uniform finiteness of `reexp`-existential families.**  Given o-minimality of every model of
`TR`, every `RExpExist` family `Y ⊆ ℝ^{k+1}` has a uniform bound on the number of connected
components of its fibres. -/
theorem unifFinite_of_omin (hOM : WilkiesDesign.CG.OMinModels) : WilkiesDesign.CG.UnifFiniteRExp := by
  intro k Y hY
  obtain ⟨φ, hφ⟩ := rexExist_fibre_formula Y hY
  obtain ⟨N, hN⟩ := exists_alt_bound hOM φ
  refine ⟨N, fun c => ?_⟩
  obtain ⟨s, hcard, hpre, heq⟩ := exists_cover_of_not_altChain (hN c)
  refine ⟨s, hcard, hpre, ?_⟩
  rw [← heq]
  ext t
  exact (hφ c t).symm

end Work.WilC4
