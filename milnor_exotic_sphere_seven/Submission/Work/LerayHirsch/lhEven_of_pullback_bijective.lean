import Mathlib
import Submission.Work.LerayHirsch.LH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The even part of Leray–Hirsch from the bijectivity of `π^*` (rank-one case)

Let `Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι` be a complex gluing-data bundle whose
fibre is `ℂ = ℂ¹`.  Its projectivisation `P(Z) = ProjSpace Z` is the quotient of the punctured total
space by `ℂˣ`; since the fibres are one-dimensional, every non-zero vector is a basis of its fibre,
so `P(Z)` carries the same cohomology as `B`, pulled back along `π = projMap Z`.

The theorem `lhEven_of_pullback_bijective` records exactly that: **if `π^*` is a bijection on
`H^n(P(Z);ℤ)` for every `n`, then Leray–Hirsch holds for `Z`** — i.e. for every `k` the map

`(x_i)_{i ∈ {i : Fin 1 // i ≤ k}} ↦ Σ_i π^*(x_i) ⌣ ζ^i`

is a bijection `⊕_{i} H^{2(k-i)}(B;ℤ) ≅ H^{2k}(P(Z);ℤ)`.  In rank one the index type
`{i : Fin 1 // i ≤ k}` has the single element `i = 0`, so the sum is the single term
`π^*(x_0) ⌣ ζ^0 = π^*(x_0)` (`LH.lean`, `cupChern_zetaPow_zero`), and the assertion is nothing but
the bijectivity of `π^*` in the even degrees `2k`, with the degree bookkeeping of the
Leray–Hirsch map (`Work.Thom.cohTransport`, an isomorphism of `ModuleCat ℤ`) carried along.

This is the `m = 1` case of `LerayHirsch`; it is what makes the splitting-principle induction of
`Submission/Work/LerayHirsch/Splitting.lean` start: the first step `SplitsOverProj` peels off the
tautological line and leaves a bundle of rank one less, and the rank-one stage is precisely the
statement here (`π^*` bijective), not a Mayer–Vietoris computation.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

/-- **Injectivity of the degree cast** `Work.Thom.cohTransport`: the transport between two equal
cohomological degrees is (the underlying map of) an isomorphism of `ModuleCat ℤ`, hence injective. -/
theorem cohTransport_injective {X : Type} [TopologicalSpace X] {n n' : ℕ} (hn : n = n') :
    Function.Injective (Work.Thom.cohTransport (B := X) hn) := by
  subst hn
  intro x y hxy
  simpa using hxy

/-- **The degree cast and its inverse**: transporting a class along `hn.symm` and back along `hn`
is the identity. -/
theorem cohTransport_apply_symm {X : Type} [TopologicalSpace X] {n n' : ℕ} (hn : n = n')
    (y : Coh ℤ n' X) :
    cohTransport (B := X) hn (cohTransport (B := X) hn.symm y) = y := by
  subst hn
  simp

/-- **The even part of Leray–Hirsch for a bundle of rank one**, from the bijectivity of the
pullback `π^*`: if `π^* : H^n(B;ℤ) → H^n(P(Z);ℤ)` is bijective for every `n`, then the
Leray–Hirsch map `(x_i) ↦ Σ_i π^*(x_i) ⌣ ζ^i` is bijective in every even degree.

The index type `{i : Fin 1 // (i : ℕ) ≤ k}` is a one-element type, so the sum defining `lhMap Z k`
collapses to its `i = 0` term, and by the unit law `cupChern_zetaPow_zero` that term is `π^*(x_0)`
up to the degree cast `2 * (k - 0) = 2 * k`.  Both `π^*` (by hypothesis, in degree `2 * (k - 0)`)
and the degree cast are bijections, and so is the evaluation `xf ↦ xf i₀` of a dependent function
on a one-element index type. -/
theorem lhEven_of_pullback_bijective {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (h : ∀ n : ℕ, Function.Bijective
      (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ n).hom) :
    Work.LerayHirsch.LerayHirsch Z := by
  intro k
  -- the unique index `i = 0 ≤ k` of the rank-one Leray–Hirsch family
  let i0 : {i : Fin 1 // (i : ℕ) ≤ k} := ⟨⟨0, by omega⟩, Nat.zero_le k⟩
  have hnat : ∀ i : {i : Fin 1 // (i : ℕ) ≤ k}, (i : ℕ) = 0 := by
    intro i
    exact congrArg Fin.val (Subsingleton.elim i.1 (0 : Fin 1))
  have hdeg : ∀ i : {i : Fin 1 // (i : ℕ) ≤ k}, 2 * (k - 0) = 2 * (k - (i : ℕ)) := by
    intro i
    rw [hnat i]
  -- the computation of the Leray–Hirsch map: the sum has one term, which is `π^*` of the `i = 0`
  -- component, composed with the degree cast `2 * (k - 0) = 2 * k`
  have key : ∀ xf : (i : {i : Fin 1 // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B,
      lhMap Z k xf = cohTransport (by omega : 2 * (k - 0) = 2 * k)
        ((CohMap (projMap Z) ℤ (2 * (k - 0))).hom (xf i0)) := by
    intro xf
    rw [lhMap_apply,
      Finset.sum_eq_single i0 (fun i _ hi => absurd (Subsingleton.elim i i0) hi)
        (fun hh => absurd (Finset.mem_univ i0) hh)]
    rw [lhTerm_def, cupChern_zetaPow_zero, Work.Whitney.cohTransport_trans]
  constructor
  · -- injectivity: two families with the same image have the same `i = 0` component
    intro xf xg hfg
    rw [key xf, key xg] at hfg
    have h1 := cohTransport_injective (by omega : 2 * (k - 0) = 2 * k) hfg
    have h2 := (h (2 * (k - 0))).1 h1
    funext i
    obtain rfl : i = i0 := Subsingleton.elim i i0
    exact h2
  · -- surjectivity: spread the preimage of the transported class over all (one) indices
    intro y
    obtain ⟨x0, hx0⟩ := (h (2 * (k - 0))).2
      (cohTransport (by omega : 2 * k = 2 * (k - 0)) y)
    refine ⟨fun i => cohTransport (hdeg i) x0, ?_⟩
    have hh : hdeg i0 = (rfl : 2 * (k - 0) = 2 * (k - (i0 : ℕ))) := Subsingleton.elim _ _
    have hxi0 : cohTransport (hdeg i0) x0 = x0 := by rw [hh, cohTransport_rfl]
    rw [key (fun i => cohTransport (hdeg i) x0)]
    rw [hxi0, hx0]
    exact cohTransport_apply_symm (by omega : 2 * (k - 0) = 2 * k) y

end

end Work.LerayHirsch
