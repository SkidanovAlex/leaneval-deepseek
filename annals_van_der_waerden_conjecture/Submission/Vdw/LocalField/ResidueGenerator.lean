import Mathlib
import Submission.Vdw.LocalField.RootsOfUnity
import Submission.Commons.GroupTheory.OrderOf.exists_pow_lt_card_eq_of_orderOf_eq_card

open Classical
open scoped NumberField WithZero

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (G3, residue side): a generator of the residue-field unit group

`κ := kap p P` is the residue field of the completion `kpInt p P`: a finite
field of characteristic `p` with `p^f` elements, `f := P.inertiaDeg ℤ`
(`kap_card`).  This module records the purely finite-field content that the
`[W : ℚ_p] = f` degree argument (G3) needs:

* `kap` carries the canonical `ZMod p`-algebra structure (`instKapZModAlgebra`,
  `ZMod.algebra` — the algebra whose scalar action is the prime-field action);
* `kap_finrank` — `[κ : 𝔽_p] = f` (`Module.finrank (ZMod p) κ = f`);
* `generator_nat_pow` — if `α` generates `κ^×` (i.e. `orderOf (mk0 α) = p^f−1`)
  then every nonzero residue is a (natural) power of `α`;
* `adjoin_eq_top_of_generator` — `𝔽_p(α) = κ` for such `α`;
* `kap_minpoly_natDegree_of_generator` — the minimal polynomial of `α` over
  `𝔽_p` has degree `f`;
* **`kap_generator_powers_linearIndependent`** — `{1, α, …, α^(f−1)}` is an
  `𝔽_p`-linearly independent family (the residue-side input to the
  mod-`𝔪` linear-independence argument of the G3 degree lower bound).

All statements carry the binder `(p) [Fact (Nat.Prime p)] (P) [P.IsMaximal]
[P.LiesOver (span {p})]` convention of the local-field chapter.  Axioms of
every statement below: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The residue field `kap p P` of the completion carries the canonical
`ZMod p`-algebra structure (the prime-field action). -/
instance instKapZModAlgebra (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Algebra (ZMod p) (kap p P) :=
  ZMod.algebra (kap p P) p

/-- The residue field has degree `f := P.inertiaDeg ℤ` over its prime field:
`Module.finrank (ZMod p) (kap p P) = f` (from `|κ| = p^f` and
`p ^ finrank = |κ|`). -/
theorem kap_finrank (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.finrank (ZMod p) (kap p P) = P.inertiaDeg ℤ := by
  classical
  have hpw : p ^ Module.finrank (ZMod p) (kap p P) = Nat.card (kap p P) :=
    FiniteField.pow_finrank_eq_natCard p (kap p P)
  have hcard := kap_card (p := p) (P := P)
  apply Nat.pow_right_injective (Fact.out : Nat.Prime p).one_lt
  simp [hpw, hcard]

/-- If `α ≠ 0` generates `κ^×` (`orderOf (mk0 α) = p^f − 1`), then every
nonzero residue is a natural power of `α`. -/
theorem generator_nat_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0) (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    {x : kap p P} (hx : x ≠ 0) : ∃ k : ℕ, α ^ k = x := by
  classical
  haveI : Fintype (kap p P) := Fintype.ofFinite (kap p P)
  let g : (kap p P)ˣ := Units.mk0 α hα
  let xu : (kap p P)ˣ := Units.mk0 x hx
  have hord : orderOf g = Fintype.card (kap p P)ˣ := by
    dsimp [g]
    rw [hgen]
    rw [Fintype.card_units (α := kap p P)]
    rw [Fintype.card_eq_nat_card]
    rw [kap_card]
  rcases Commons.GroupTheory.OrderOf.exists_pow_lt_card_eq_of_orderOf_eq_card g hord xu with
    ⟨k, hk, hpow⟩
  refine ⟨k, ?_⟩
  have hv := congrArg (fun u : (kap p P)ˣ => (u : kap p P)) hpow
  simpa [g, xu] using hv

/-- A generator of `κ^×` generates `κ` as a field over `𝔽_p`:
`𝔽_p(α) = κ`. -/
theorem adjoin_eq_top_of_generator (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    IntermediateField.adjoin (ZMod p) ({α} : Set (kap p P)) = ⊤ := by
  classical
  let I : IntermediateField (ZMod p) (kap p P) :=
    IntermediateField.adjoin (ZMod p) ({α} : Set (kap p P))
  have hmem : ∀ x : kap p P, x ∈ I := by
    intro x
    by_cases hx0 : x = 0
    · rw [hx0]
      exact I.zero_mem
    · rcases generator_nat_pow (p := p) (P := P) (α := α) hα hgen (x := x) hx0 with ⟨k, hk⟩
      rw [← hk]
      have hαmem : α ∈ I :=
        IntermediateField.mem_adjoin_simple_self (ZMod p) (E := kap p P) α
      have hz : α ^ (k : ℤ) ∈ I := zpow_mem hαmem (k : ℤ)
      simpa using hz
  exact le_antisymm le_top (by
    intro x hx
    exact hmem x)

/-- For a generator `α` of `κ^×`, the minimal polynomial of `α` over `𝔽_p`
has degree `f = P.inertiaDeg ℤ` (via `𝔽_p(α) = κ` and `[κ : 𝔽_p] = f`). -/
theorem kap_minpoly_natDegree_of_generator (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    (minpoly (ZMod p) α).natDegree = P.inertiaDeg ℤ := by
  classical
  have htop := adjoin_eq_top_of_generator (p := p) (P := P) (α := α) hα hgen
  haveI : Module.Finite (ZMod p) (kap p P) := Module.Finite.of_finite
  have hi : IsIntegral (ZMod p) α := IsIntegral.of_finite (ZMod p) α
  have hadj : Module.finrank (ZMod p)
      (IntermediateField.adjoin (ZMod p) ({α} : Set (kap p P))) =
      (minpoly (ZMod p) α).natDegree :=
    IntermediateField.adjoin.finrank hi
  have htoprank : Module.finrank (ZMod p)
      (IntermediateField.adjoin (ZMod p) ({α} : Set (kap p P))) =
      Module.finrank (ZMod p) (kap p P) := by
    rw [htop]
    simp
  rw [← hadj, htoprank]
  exact kap_finrank (p := p) (P := P)

/-- **Main**: the first `f` powers `{1, α, …, α^(f−1)}` of a generator `α` of
`κ^×` are linearly independent over `𝔽_p` (they are in fact a basis, by
`kap_finrank`). -/
theorem kap_generator_powers_linearIndependent (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    LinearIndependent (ZMod p)
      (fun i : Fin (P.inertiaDeg ℤ) => α ^ (i : ℕ)) := by
  classical
  have hdeg := kap_minpoly_natDegree_of_generator (p := p) (P := P) (α := α) hα hgen
  have hli := linearIndependent_pow (K := ZMod p) (S := kap p P) α
  exact hdeg ▸ hli

/-- **Containment among the primitive powers**: with `α` a generator of
`κ^×` (`orderOf (mk0 α) = p^f − 1`), every `(p^f−1)`-st root of unity in
the valuation ring is a power of the primitive Teichmüller lift
`teich α`. -/
theorem qthRoot_eq_teich_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    {z : kpInt p P} (hz : z ^ (p ^ P.inertiaDeg ℤ - 1) = 1) :
    ∃ k : ℕ, z = (teich p P α) ^ k := by
  classical
  have hz' : z = teich p P (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z) :=
    qthRoot_eq_teich (p := p) (P := P) hz
  have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z ≠ 0 :=
    qthRoot_mk_ne_zero (p := p) (P := P) hz
  rcases generator_nat_pow (p := p) (P := P) (α := α) hα hgen
    (x := Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z) hmk with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [hz']
  rw [← hk]
  rw [teich_pow]


end

end Submission.Vdw.LocalField
