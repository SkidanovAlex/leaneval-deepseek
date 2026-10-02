import Mathlib
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.lhEven_of_pullback_bijective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The odd part of Leray–Hirsch from the bijectivity of `π^*` (rank-one case)

Let `Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι` be a complex gluing-data bundle whose
fibre is `ℂ = ℂ¹`.  Its projectivisation `P(Z) = ProjSpace Z` is the quotient of the punctured total
space by `ℂˣ`; over a rank-one bundle the projection `π = projMap Z : P(Z) → B` induces on
cohomology the whole of `H^*(P(Z))`, so `P(Z)` carries the same cohomology as `B`, and the odd part
of Leray–Hirsch is again just the statement that `π^*` is a bijection.

The theorem `lhOdd_of_pullback_bijective` records exactly that: **if `π^*` is a bijection on
`H^n(P(Z);ℤ)` for every `n`, then `LerayHirschOdd Z` holds** — i.e. for every `k` the map

`(x_i)_{i ∈ {i : Fin 1 // i ≤ k}} ↦ Σ_i π^*(x_i) ⌣ ζ^i : ⊕_i H^{2k+1-2i}(B;ℤ) → H^{2k+1}(P(Z);ℤ)`

is a bijection.  In rank one the index type `{i : Fin 1 // i ≤ k}` has the single element `i = 0`,
so the sum is the single term `π^*(x_0) ⌣ ζ^0 = π^*(x_0)` (the unit law for the *odd* pairing
`Work.Cohomology.cupH'`, `cupH'_one_right`), and the assertion is nothing but the bijectivity of
`π^*` in the odd degrees `2k+1`, with the degree bookkeeping of the Leray–Hirsch map
(`Work.Thom.cohTransport`, an isomorphism of `ModuleCat ℤ`) carried along.  This is the companion of
`lhEven_of_pullback_bijective` in `Submission/Work/LerayHirsch/lhEven_of_pullback_bijective.lean`,
whose auxiliary lemmas `cohTransport_injective` and `cohTransport_apply_symm` are reused here.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The `i = 0` summand of the odd Leray–Hirsch map** is the pullback `π^*x`: this is the unit law
`cupH'_one_right` for the odd pairing, and it is what makes `π^*` injective in odd degrees.  (The
degree cast `(2k+1-0)+0 = 2k+1` is invisible and closes by `rfl` after the unit law is applied.) -/
private theorem lhTermOdd_zero_index {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (hm : 1 ≤ m) (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (k : ℕ)
    (x : Coh ℤ (2 * k + 1 - 2 * 0) B) :
    lhTermOdd Z k (⟨⟨0, hm⟩, Nat.zero_le k⟩ : {i : Fin m // (i : ℕ) ≤ k}) x
      = cohTransport (B := ProjSpace Z) (by omega : 2 * k + 1 - 2 * 0 = 2 * k + 1)
          ((CohMap (projMap Z) ℤ (2 * k + 1 - 2 * 0)).hom x) := by
  simp only [lhTermOdd, zetaPow_zero, cohTransport_rfl, Nat.mul_zero,
    Work.Cohomology.cupH'_one_right]

/-- **The odd part of Leray–Hirsch for a bundle of rank one**, from the bijectivity of the
pullback `π^*`: if `π^* : H^n(B;ℤ) → H^n(P(Z);ℤ)` is bijective for every `n`, then the odd
Leray–Hirsch map `(x_i) ↦ Σ_i π^*(x_i) ⌣ ζ^i` is bijective in every odd degree.

The index type `{i : Fin 1 // (i : ℕ) ≤ k}` is a one-element type, so the sum defining
`lhMapOdd Z k` collapses to its `i = 0` term, which by `lhTermOdd_zero_index` is `π^*(x_0)` up to
the degree cast.  Both `π^*` (by hypothesis, in degree `2 * k + 1`) and the degree cast are
bijections, and so is the evaluation `xf ↦ xf i₀` of a dependent function on a one-element index
type. -/
theorem lhOdd_of_pullback_bijective {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (h : ∀ n : ℕ, Function.Bijective
      (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ n).hom) :
    Work.LerayHirsch.LerayHirschOdd Z := by
  intro k
  -- the unique index `i = 0 ≤ k` of the rank-one Leray–Hirsch family
  have hnat : ∀ i : {i : Fin 1 // (i : ℕ) ≤ k},
      (i : ℕ) = 0 := by
    intro i
    exact congrArg Fin.val (Subsingleton.elim i.1 (0 : Fin 1))
  -- the degree in the `i`-th summand and the degree `2k+1` are the same, for every `i`
  have hdeg : ∀ i : {i : Fin 1 // (i : ℕ) ≤ k}, 2 * k + 1 - 2 * 0 = 2 * k + 1 - 2 * (i : ℕ) := by
    intro i
    rw [hnat i]
  -- the computation of the odd Leray–Hirsch map: the sum has one term, which is `π^*` of the
  -- `i = 0` component, composed with the degree cast `2 * k + 1 - 0 = 2 * k + 1`
  have key : ∀ xf : (i : {i : Fin 1 // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B,
      lhMapOdd Z k xf = cohTransport (B := ProjSpace Z) (by omega : 2 * k + 1 - 2 * 0 = 2 * k + 1)
        ((CohMap (projMap Z) ℤ (2 * k + 1 - 2 * 0)).hom
          (xf (⟨⟨0, by omega⟩, Nat.zero_le k⟩ : {i : Fin 1 // (i : ℕ) ≤ k}))) := by
    intro xf
    rw [lhMapOdd,
      Finset.sum_eq_single (⟨⟨0, by omega⟩, Nat.zero_le k⟩ : {i : Fin 1 // (i : ℕ) ≤ k})
        (fun i _ hi => absurd (Subsingleton.elim i _) hi)
        (fun hh => absurd (Finset.mem_univ _) hh)]
    exact lhTermOdd_zero_index (le_refl 1) Z k _
  constructor
  · -- injectivity: two families with the same image have the same `i = 0` component
    intro xf xg hfg
    rw [key xf, key xg] at hfg
    have h1 := cohTransport_injective (X := ProjSpace Z) (by omega : 2 * k + 1 - 2 * 0 = 2 * k + 1)
      hfg
    have h2 := (h (2 * k + 1 - 2 * 0)).1 h1
    funext i
    have hi : i = (⟨⟨0, by omega⟩, Nat.zero_le k⟩ : {i : Fin 1 // (i : ℕ) ≤ k}) :=
      Subsingleton.elim i _
    rw [hi]
    exact h2
  · -- surjectivity: spread the preimage of the transported class over all (one) indices
    intro y
    obtain ⟨x0, hx0⟩ := (h (2 * k + 1 - 2 * 0)).2
      (cohTransport (B := ProjSpace Z) (by omega : 2 * k + 1 = 2 * k + 1 - 2 * 0) y)
    refine ⟨fun i => cohTransport (B := B) (hdeg i) x0, ?_⟩
    have hxi0 : cohTransport (B := B) (hdeg (⟨⟨0, by omega⟩, Nat.zero_le k⟩ :
        {i : Fin 1 // (i : ℕ) ≤ k})) x0 = x0 := by
      have hh : hdeg (⟨⟨0, by omega⟩, Nat.zero_le k⟩ : {i : Fin 1 // (i : ℕ) ≤ k})
          = (rfl : 2 * k + 1 - 2 * 0 = 2 * k + 1 - 2 * 0) := Subsingleton.elim _ _
      rw [hh, cohTransport_rfl]
    rw [key (fun i => cohTransport (B := B) (hdeg i) x0)]
    rw [hxi0, hx0]
    exact cohTransport_apply_symm (X := ProjSpace Z) (by omega : 2 * k + 1 - 2 * 0 = 2 * k + 1) y

end

end Work.LerayHirsch
