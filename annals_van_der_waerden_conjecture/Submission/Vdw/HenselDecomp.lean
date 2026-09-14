import Mathlib
import Submission.Vdw.PadicLift
import Submission.Vdw.IndexFactor
import Submission.Commons.NumberTheory.Padics.hensel_lift_family

open Polynomial
open scoped BigOperators

set_option autoImplicit false

/-!
# Hensel decomposition: from a mod-`p` factorization to lifted factors (1b)

This module glues the two sides of the Hensel-half of the discindex bridge:

* **residue side** (`polyIndex` machinery over `ZMod p`): the index of a
  polynomial whose reduction factors as `∏ (hᵢ)^{eᵢ}` with distinct monic
  irreducibles `hᵢ` equals the splitting-type sum `Σ (eᵢ − 1)·deg hᵢ`
  (`splitting_type_index_of_modp_factorization`, from
  `IndexFactor.polyIndex_splitting_type`);
* **lift side** (shared commons): the *Hensel factorization lifting*
  `Commons.NumberTheory.Padics.hensel_lift_family` — a coprime monic
  factorization over `ZMod p` of the reduction of a monic polynomial lifts
  to an exact factorization over `ℤ_[p]` with the same degrees and exact
  reductions.

`hensel_lift_family_of_int` states the composite in the form the discindex
argument consumes: an *integer* monic `f` whose reduction `f mod p` factors
into pairwise-coprime monic `qᵢ` admits monic lifts `Fᵢ : ℤ_[p][X]` with
`Fᵢ mod p = qᵢ`, `deg Fᵢ = deg qᵢ`, and
`f (as an element of ℤ_[p][X]) = ∏ Fᵢ`.

What is **not** in this module (genuinely open, deep local-field content —
see Roadmap Session-20 block): the valuation bound
`v_p(Disc(K_f)) ≤ Σ (eᵢ−1)·deg hᵢ` for the number field `K_f = ℚ[x]/(f)`
of a tame prime `p > n` (Lemma 24 of Bhargava 2025).  The present Hensel
half supplies the factor decomposition that the local proof of that bound
operates on; the bound itself needs the theory of the p-adic field
`ℚ_p[x]/(f)` (ramification index × inertia degree = discriminant
valuation for tame extensions, via the different ideal) and is being built
separately.
-/

namespace Submission.Vdw

noncomputable section

/-- **Hensel lifting for an integer polynomial**: if the reduction of a monic
integer polynomial `f` factors over `ZMod p` as `∏_{i ∈ s} q i` with the
`q i` monic and pairwise coprime, then the factorization lifts to `ℤ_[p]`:
there are monic `F i` (`i ∈ s`) with `deg F i = deg (q i)`, whose reductions
are exactly the `q i`, and with `f` (viewed in `ℤ_[p][X]`) equal to
`∏_{i ∈ s} F i`. -/
theorem hensel_lift_family_of_int {p : ℕ} [Fact p.Prime] {ι : Type*} [DecidableEq ι]
    (f : ℤ[X]) (hf : f.Monic) (q : ι → (ZMod p)[X]) (s : Finset ι)
    (hqmon : ∀ i ∈ s, (q i).Monic)
    (hfac : f.map (Int.castRingHom (ZMod p)) = ∏ i ∈ s, q i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (q i) (q j)) :
    ∃ F : ι → (PadicInt p)[X],
      (∀ i ∈ s, (F i).Monic) ∧ (∀ i ∈ s, (F i).natDegree = (q i).natDegree) ∧
        f.map (Int.castRingHom (PadicInt p)) = ∏ i ∈ s, F i ∧
        (∀ i ∈ s, (F i).map (PadicInt.toZMod : PadicInt p →+* ZMod p) = q i) := by
  classical
  let g : (PadicInt p)[X] := f.map (Int.castRingHom (PadicInt p))
  have hgM : g.Monic := hf.map (Int.castRingHom (PadicInt p))
  have hfacZ : g.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = ∏ i ∈ s, q i := by
    dsimp [g]
    rw [map_intCast_toZMod, hfac]
  rcases Commons.NumberTheory.Padics.hensel_lift_family g hgM q s hqmon hfacZ hcop with
    ⟨F, hFmon, hFdeg, hFprod, hFred⟩
  exact ⟨F, hFmon, hFdeg, by simpa [g] using hFprod, hFred⟩

/-- **Splitting-type index on the residue side**: if the polynomial `g` over
`ZMod p` factors as `∏_{i ∈ s} (h i) ^ (e i)` with distinct monic
irreducibles `h i`, then `polyIndex g = Σ_{i ∈ s} (e i − 1) · deg (h i)`.
This is the mod-`p` splitting-type sum that Lemma 24 compares with the
discriminant valuation. -/
theorem splitting_type_index_of_modp_factorization {p : ℕ} [Fact p.Prime]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (h : ι → (ZMod p)[X])
    (e : ι → ℕ) (hmon : ∀ i ∈ s, (h i).Monic)
    (hirr : ∀ i ∈ s, Irreducible (h i))
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (h i) (h j))
    (he : ∀ i ∈ s, 1 ≤ e i) (g : (ZMod p)[X])
    (hg : g = ∏ i ∈ s, (h i) ^ (e i)) :
    polyIndex (F := ZMod p) g = ∑ i ∈ s, (e i - 1) * (h i).natDegree := by
  rw [hg]
  exact polyIndex_splitting_type (F := ZMod p) s h e hmon hirr hcop he

end
end Submission.Vdw
