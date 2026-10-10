import Mathlib
import Submission.Work.CY3Stab.Prod.height_map_mvPolynomial

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.exists_ltSeries_restrict_mvPolynomial`

Any chain of prime ideals of `MvPolynomial σ A` (in the `PrimeSpectrum` order, i.e. increasing by
ideal inclusion) whose last member is contained in the extension `𝔭 · MvPolynomial σ A` of an ideal
`𝔭 ≤ A` is, up to its length, already realised inside a polynomial ring `MvPolynomial s A` in
*finitely many* variables `s ⊆ σ`, with the last member again contained in the extension of `𝔭`.

## Mathematical content

Write `P_i = (L i).asIdeal`, so that `P_0 ⊊ P_1 ⊊ ⋯ ⊊ P_n` with `P_n ≤ 𝔭 · A[σ]` and `n = L.length`.
For each consecutive pair choose `f_i ∈ P_{i+1} \ P_i` (a witness of the strict inclusion) and let
`s ⊆ σ` be the union of the (finite) variable sets of the `f_i`.  Contracting the chain along the
inclusion `ρ : A[s] = MvPolynomial s A →ₐ[A] MvPolynomial σ A` gives primes

`Q_i = P_i.comap ρ = P_i ∩ A[s]`

which still form a strictly increasing chain: each `f_i` lies in the subring `A[s]` (`f_i` is a
polynomial in the variables of `s`), so its preimage under `ρ` separates `Q_i` from `Q_{i+1}`.  The
last member satisfies `Q_n ≤ (𝔭 · A[σ]).comap ρ = 𝔭 · A[s]` by monotonicity of `comap` and
`comap_rename_map_algebraMap`.

The only imported ingredient is `comap_rename_map_algebraMap` (the extension of `𝔭` is compatible
with a `rename` of variables), from `height_map_mvPolynomial`.
-/

set_option autoImplicit false

namespace Work.CY3Stab.Prod

open MvPolynomial

/-- Given a chain `L` of primes of `MvPolynomial σ A` (strictly increasing in the `PrimeSpectrum`
order, i.e. strictly increasing by ideal inclusion) whose last member is contained in the extension
of an ideal `𝔭 ≤ A`, there is a *finite* set `s ⊆ σ` of variables and a chain `L'` of primes of
`MvPolynomial s A` of the *same length* as `L` whose last member is again contained in the
extension of `𝔭`.

The chain `L'` is obtained by contracting `L` to the finitely many variables occurring in witnesses
of the strict inclusions of `L`. -/
theorem exists_ltSeries_restrict_mvPolynomial {A : Type} [CommRing A] (σ : Type) (𝔭 : Ideal A)
    (L : LTSeries (PrimeSpectrum (MvPolynomial σ A)))
    (hL : L.last.asIdeal ≤ 𝔭.map (algebraMap A (MvPolynomial σ A))) :
    ∃ (s : Set σ) (_ : s.Finite) (L' : LTSeries (PrimeSpectrum (MvPolynomial s A))),
      L'.length = L.length ∧ L'.last.asIdeal ≤ 𝔭.map (algebraMap A (MvPolynomial s A)) := by
  classical
  -- For each strict step, choose an element of `P_{i+1}` which is not in `P_i`.
  have hex : ∀ i : Fin L.length, ∃ f : MvPolynomial σ A,
      f ∈ (L i.succ).asIdeal ∧ f ∉ (L i.castSucc).asIdeal := by
    intro i
    have h : L i.castSucc < L i.succ := L.step i
    have hnle : ¬ ((L i.succ).asIdeal ≤ (L i.castSucc).asIdeal) := (lt_iff_le_not_ge.mp h).2
    obtain ⟨x, hx1, hx2⟩ := Set.not_subset.mp hnle
    exact ⟨x, hx1, hx2⟩
  choose f hfmem hfnotmem using hex
  -- The finite set of variables occurring in the chosen elements.
  let s : Set σ := ↑(Finset.univ.biUnion fun i : Fin L.length => (f i).vars)
  have hsf : s.Finite := (Finset.univ.biUnion (fun i : Fin L.length => (f i).vars)).finite_toSet
  let ρ : MvPolynomial s A →ₐ[A] MvPolynomial σ A := MvPolynomial.rename (Subtype.val : ↥s → σ)
  have hfvars : ∀ i, (↑(f i).vars : Set σ) ⊆ s := by
    intro i x hx
    show x ∈ (↑(Finset.univ.biUnion fun i : Fin L.length => (f i).vars) : Set σ)
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, hx⟩
  -- Each `f i` lies in the range of the inclusion `ρ`.
  have hfrange : ∀ i, f i ∈ ρ.range := by
    intro i
    have h1 : f i ∈ MvPolynomial.supported A s := by
      rw [MvPolynomial.mem_supported]
      exact hfvars i
    have h2 : MvPolynomial.supported A s = ρ.range := by
      rw [MvPolynomial.supported_eq_range_rename s]
    rwa [h2] at h1
  -- Preimages of the `f i` in the small polynomial ring.
  let g : Fin L.length → MvPolynomial s A := fun i => (hfrange i).choose
  have hg : ∀ i, ρ (g i) = f i := fun i => (hfrange i).choose_spec
  -- The contracted chain.
  let Q : Fin (L.length + 1) → Ideal (MvPolynomial s A) := fun j => (L j).asIdeal.comap ρ
  have hQprime : ∀ j, (Q j).IsPrime := fun j => by
    have h := (L j).isPrime
    exact Ideal.comap_isPrime ρ (L j).asIdeal
  let q : Fin (L.length + 1) → PrimeSpectrum (MvPolynomial s A) := fun j => ⟨Q j, hQprime j⟩
  refine ⟨s, hsf, ⟨L.length, q, ?_⟩, rfl, ?_⟩
  · -- Strictness is preserved by the contraction, witnessed by the `g i`.
    intro i
    show Q i.castSucc < Q i.succ
    have hle : Q i.castSucc ≤ Q i.succ :=
      Ideal.comap_mono ((lt_iff_le_not_ge.mp (L.step i : L i.castSucc < L i.succ)).1)
    refine lt_of_le_of_ne hle ?_
    intro h
    have hmem : g i ∈ Q i.succ := Ideal.mem_comap.mpr (by rw [hg i]; exact hfmem i)
    rw [← h] at hmem
    have hh : ρ (g i) ∈ (L i.castSucc).asIdeal := Ideal.mem_comap.mp hmem
    rw [hg i] at hh
    exact hfnotmem i hh
  · -- The last member is still contained in the extension of `𝔭`.
    show Q (Fin.last L.length) ≤ 𝔭.map (algebraMap A (MvPolynomial s A))
    rw [← comap_rename_map_algebraMap 𝔭 (Subtype.val : ↥s → σ) Subtype.val_injective]
    exact Ideal.comap_mono hL

end Work.CY3Stab.Prod
