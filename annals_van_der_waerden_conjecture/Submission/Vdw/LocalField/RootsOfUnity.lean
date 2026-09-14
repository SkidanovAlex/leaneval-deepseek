import Mathlib
import Submission.Vdw.LocalField.AdicComplete
import Submission.Vdw.LocalField.ResidueInstances
import Submission.Commons.FieldTheory.Perfection.coeff_zero_bijective_of_perfect
import Submission.Commons.GroupTheory.OrderOf.exists_pow_lt_card_eq_of_orderOf_eq_card

open scoped NumberField
open IsDedekindDomain
open IsLocalRing

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (stone 3): Teichmüller roots of unity in the valuation
ring of the completion

The unramified-subfield construction for the wild-different programme needs a
lift of the finite residue field `κ := kpInt p P ⧸ 𝔪` (a field of `p^f`
elements, `f := P.inertiaDeg ℤ`) into the valuation ring `kpInt p P` of the
completion: for every `α : κ` one wants `ζ := teich α ∈ kpInt p P` with
`ζ ≡ α (mod 𝔪)` and, when `α ≠ 0`, `ζ^(p^f−1) = 1` — a (not necessarily
primitive) `(p^f−1)`-st root of unity lifting `α`, i.e. a unit of `kpInt`.

Mathlib's `Perfection.teichmuller₀ p 𝔪 : Perfection κ p →*₀ kpInt p P`
provides the lift once the residue is given as a `Perfection`: its reduction
is the coefficient-0 map (`Perfection.mk_teichmuller₀`), so it suffices to
build the *root chain* `x ∈ Perfection κ p` of `α` — the unique element of
the perfection whose coefficient 0 is `α`.  That uniqueness/存在 is the
fleet lemma `coeff_zero_bijective_of_perfect` (the residue field `κ` is
perfect: finite, hence `PerfectField`, hence `PerfectRing`).

Module content:
* `kap` — the residue field `kpInt ⧸ 𝔪` (an `abbrev` so that the
  `ResidueInstances` Field/CharP/Finite/PerfectField instances fire);
* `kap_card` / `kap_pow_pf` — `Nat.card κ = p^f` and `α^(p^f) = α`
  (`FiniteField.pow_card` in the finite field of `p^f` elements);
* `rootChain` / `rootChain_coeff_zero` — the perfection element with
  coefficient 0 equal to `α`;
* `perfection_pow_periodic` — generic: an `x ∈ Perfection κ p` whose
  coefficient 0 is fixed by `z ↦ z^(p^f)` is itself fixed by the
  `(p^f)`-power (`Perfection.ext` is not needed: injectivity of the
  coefficient-0 map from the bijectivity lemma suffices);
* `teich α` — the Teichmüller lift `teichmuller₀ (rootChain α)`;
* `teich_mod_eq` — `mk 𝔪 (teich α) = α` (reduction property);
* `teich_ne_zero_of_ne_zero` / `teich_not_mem_maximalIdeal_of_ne_zero`;
* `teich_pow_pf` — `(teich α)^(p^f) = teich α`;
* `teich_pow_card_sub_one` — `α ≠ 0 ⟹ (teich α)^(p^f−1) = 1` (the residue
  is a domain and `teich α ≠ 0`);
* `teich_isUnit_of_ne_zero` — `α ≠ 0 ⟹ IsUnit (teich α)` (inverse
  `(teich α)^(p^f−2)`), the unit-group section of the Teichmüller map;
* `exists_rootOfUnity_lift` — the packaged statement: every nonzero residue
  has a unit root-of-unity lift of order dividing `p^f−1` with prescribed
  reduction;
* `rootChain_mul` / `teich_mul` / `teich_one` — the Teichmüller lift is a
  multiplicative section (coefficient-0 injectivity transfers the monoid law
  through the root chain; `teich` is a monoid homomorphism `κ → kpInt`),
  which the unramified-subfield `W = ℚ_p[ζ]` construction uses to identify
  the powers of the lifted generator;
* `unit_pow_eq_one_of_val_pow_eq_one` — generic bridge: a power of a nonzero
  field element is 1 iff the same power of its unit is 1;
* `teich_orderOf_eq` — EXACTNESS: if `α` generates the residue unit group
  (`orderOf (Units.mk0 α hα) = p^f − 1`) then `orderOf (teich α) = p^f − 1`
  (upper bound from `teich_pow_card_sub_one`; lower bound by reducing
  `ζ^(orderOf ζ) = 1` modulo 𝔪: `mk (ζ^m) = (mk ζ)^m` forces
  `α^(orderOf ζ) = 1`, and the generator hypothesis gives `p^f − 1 | orderOf ζ`);
* `exists_primitive_rootOfUnity` — the unit group of the finite residue field
  is cyclic, so a generator exists; its Teichmüller lift is a unit of exact
  order `p^f − 1` reducing to a nonzero generator: the primitive root of
  unity that generates `W = ℚ_p[ζ]`;
* **residue-surjectivity of the roots of unity** (`teich_power_mod_eq`,
  `teich_power_mod_ne_zero`, `teichPowerUnit`, `teichPowerUnit_val`,
  `kap_pow_ne_of_lt`, `teich_power_reduce_injective`,
  `teich_power_reduce_surjective`, and the packaged
  **`teich_power_units_bijective`**): for `α` a generator of `κ^×` the
  reductions of the first `q := p^f−1` powers of `teich α` enumerate `κ^×`
  bijectively (`Fin q → κˣ`, `k ↦ teichPowerUnit hα k`).  Ingredients:
  reduction commutes with powers (`mk (ζ^k) = α^k`), generator powers are
  distinct below `q` (field cancellation `α^i = α^j, i<j` forces `α^(j−i)=1`,
  so `q | j−i` from the exact unit order — a contradiction), and
  surjectivity via the fleet finite-group lemma
  `Commons.GroupTheory.OrderOf.exists_pow_lt_card_eq_of_orderOf_eq_card`
  (element of order = group cardinality generates, with exponent `< card`).
  This is the central residue-degree input of the `W = ℚ_p[ζ]` construction:
  the image of `μ_q ⊆ kpInt` under reduction is exactly `κ^×`, so the residue
  field of `W` contains (and, `W ⊆ K_P`, is contained in) `κ`.

This is the input the next stone (the unramified subfield `W = ℚ_p[ζ]`
inside `K_P`) consumes; the present module only needs the `IsAdicComplete`
instance of `AdicComplete` and the instance bundle of `ResidueInstances`.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The residue field `kpInt p P ⧸ 𝔪` of the completion `kpAdic p P`
(an `abbrev` so the `ResidueInstances` Field/CharP/Finite/PerfectField
instances, declared on the unfolded quotient type, fire). -/
abbrev kap (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] : Type u :=
  kpInt p P ⧸ maximalIdeal (kpInt p P)

/-- The completion residue has `p^f` elements, `f := P.inertiaDeg ℤ`
(this is `kpIntResidue_card` in `kap`-spelling). -/
theorem kap_card (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Nat.card (kap p P) = p ^ P.inertiaDeg ℤ := by
  simpa [kap] using kpIntResidue_card (K := K) p P

/-- In the finite residue field of `p^f` elements every element satisfies
`α^(p^f) = α`. -/
theorem kap_pow_pf (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    α ^ (p ^ P.inertiaDeg ℤ) = α := by
  classical
  haveI : Fintype (kap p P) := Fintype.ofFinite (kap p P)
  rw [← kap_card p P]
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card α

/-- The p-th-root chain of `α ∈ κ`: the unique element of the perfection of
the (perfect) residue field whose coefficient 0 is `α`. -/
noncomputable def rootChain (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    Perfection (kap p P) p := by
  classical
  have hsurj : Function.Surjective
      (fun x : Perfection (kap p P) p => Perfection.coeff (kap p P) p 0 x) :=
    (Commons.FieldTheory.Perfection.coeff_zero_bijective_of_perfect (R := kap p P) p).2
  exact Classical.choose (hsurj α)

/-- Coefficient 0 of the root chain of `α` is `α`. -/
theorem rootChain_coeff_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    Perfection.coeff (kap p P) p 0 (rootChain p P α) = α := by
  unfold rootChain
  have hsurj : Function.Surjective
      (fun x : Perfection (kap p P) p => Perfection.coeff (kap p P) p 0 x) :=
    (Commons.FieldTheory.Perfection.coeff_zero_bijective_of_perfect (R := kap p P) p).2
  exact Classical.choose_spec (hsurj α)

/-- Generic periodicity: if `x ∈ Perfection κ p` (κ a perfect field of
characteristic p) has coefficient 0 fixed by `z ↦ z^(p^f)`, then `x` itself
is fixed by the `(p^f)`-power.  (The coefficient-0 map on the perfection of
a perfect ring is bijective, so equality at coefficient 0 is equality.) -/
theorem perfection_pow_periodic (κ : Type u) [Field κ] (p : ℕ) [Fact (Nat.Prime p)]
    [CharP κ p] [PerfectRing κ p] (x : Perfection κ p) (f : ℕ)
    (hx : (Perfection.coeff κ p 0 x) ^ (p ^ f) = Perfection.coeff κ p 0 x) :
    x ^ (p ^ f) = x := by
  classical
  have hb : Function.Bijective (Perfection.coeff κ p 0) :=
    Commons.FieldTheory.Perfection.coeff_zero_bijective_of_perfect (R := κ) p
  apply hb.1
  calc
    Perfection.coeff κ p 0 (x ^ (p ^ f)) = (Perfection.coeff κ p 0 x) ^ (p ^ f) := map_pow _ x (p ^ f)
    _ = Perfection.coeff κ p 0 x := hx

/-- The root chain of `α` is periodic of period `p^f`: since
`α^(p^f) = α` in the finite field, `x^(p^f) = x`. -/
theorem rootChain_periodic (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    rootChain p P α ^ (p ^ P.inertiaDeg ℤ) = rootChain p P α := by
  classical
  apply perfection_pow_periodic (κ := kap p P) (p := p) (rootChain p P α) (P.inertiaDeg ℤ)
  rw [rootChain_coeff_zero]
  exact kap_pow_pf (p := p) (P := P) α

/-- The Teichmüller lift of `α : κ` into the valuation ring `kpInt p P`:
`teich α := teichmuller₀ (rootChain α)`, an element of norm ≤ 1 congruent
to `α` modulo the maximal ideal. -/
noncomputable def teich (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    kpInt p P :=
  Perfection.teichmuller₀ p (maximalIdeal (kpInt p P)) (rootChain p P α)

/-- The Teichmüller lift reduces to `α`: `mk 𝔪 (teich α) = α`. -/
theorem teich_mod_eq (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    Ideal.Quotient.mk (maximalIdeal (kpInt p P)) (teich p P α) = α := by
  unfold teich
  rw [Perfection.mk_teichmuller₀]
  exact rootChain_coeff_zero (p := p) (P := P) α

/-- A Teichmüller lift of a nonzero residue is nonzero. -/
theorem teich_ne_zero_of_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0) : teich p P α ≠ 0 := by
  intro hz
  apply hα
  rw [← teich_mod_eq (p := p) (P := P) α]
  rw [hz]
  simp

/-- A Teichmüller lift of a nonzero residue is not in the maximal ideal
(equiv. is a unit of the valuation ring). -/
theorem teich_not_mem_maximalIdeal_of_ne_zero (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) : teich p P α ∉ maximalIdeal (kpInt p P) := by
  intro hmem
  apply hα
  have hzero : Ideal.Quotient.mk (maximalIdeal (kpInt p P)) (teich p P α) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal (kpInt p P))).mpr hmem
  rw [← teich_mod_eq (p := p) (P := P) α]
  exact hzero

/-- The Teichmüller lift is fixed by the `(p^f)`-power:
`(teich α)^(p^f) = teich α`. -/
theorem teich_pow_pf (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    teich p P α ^ (p ^ P.inertiaDeg ℤ) = teich p P α := by
  unfold teich
  calc
    (Perfection.teichmuller₀ p (maximalIdeal (kpInt p P)) (rootChain p P α))
        ^ (p ^ P.inertiaDeg ℤ)
        = Perfection.teichmuller₀ p (maximalIdeal (kpInt p P))
            (rootChain p P α ^ (p ^ P.inertiaDeg ℤ)) := by
          rw [← map_pow]
    _ = Perfection.teichmuller₀ p (maximalIdeal (kpInt p P)) (rootChain p P α) := by
          rw [rootChain_periodic (p := p) (P := P) α]

/-- For a nonzero residue `α`, the Teichmüller lift is a `(p^f−1)`-st root
of unity: `(teich α)^(p^f−1) = 1`.  (From `(teich α)^(p^f) = teich α`,
`teich α ≠ 0` and the absence of zero divisors in `kpInt`.) -/
theorem teich_pow_card_sub_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0) : teich p P α ^ (p ^ P.inertiaDeg ℤ - 1) = 1 := by
  classical
  let ζ := teich p P α
  have hζpow : ζ ^ (p ^ P.inertiaDeg ℤ) = ζ := teich_pow_pf (p := p) (P := P) α
  have hp0 : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hpz1 : 1 ≤ p ^ P.inertiaDeg ℤ := Nat.succ_le_of_lt (pow_pos hp0 _)
  have hmp : (p ^ P.inertiaDeg ℤ - 1) + 1 = p ^ P.inertiaDeg ℤ := Nat.sub_add_cancel (m := 1) hpz1
  have hfac : ζ * (ζ ^ (p ^ P.inertiaDeg ℤ - 1) - 1) = 0 := by
    calc
      ζ * (ζ ^ (p ^ P.inertiaDeg ℤ - 1) - 1)
          = ζ * ζ ^ (p ^ P.inertiaDeg ℤ - 1) - ζ * 1 := by rw [mul_sub]
      _ = ζ ^ ((p ^ P.inertiaDeg ℤ - 1) + 1) - ζ := by
            rw [pow_succ', mul_one]
      _ = ζ ^ (p ^ P.inertiaDeg ℤ) - ζ := by rw [hmp]
      _ = 0 := by rw [hζpow, sub_self]
  have hζ0 : ζ ≠ 0 := teich_ne_zero_of_ne_zero (p := p) (P := P) (α := α) hα
  have hz : ζ ^ (p ^ P.inertiaDeg ℤ - 1) - 1 = 0 := (mul_eq_zero.mp hfac).resolve_left hζ0
  exact sub_eq_zero.mp hz

/-- For a nonzero residue `α`, the Teichmüller lift `teich α` is a unit of
`kpInt` (the valuation ring): from `(teich α)^(p^f−1) = 1` with the inverse
`(teich α)^(p^f−2)` (for `f ≥ 1`; the case `p^f − 1 = 1`, i.e. `p = f = 2`
degree 1 — covered since `1 ≤ m` and inverse exponent `m − 1` is allowed to
be 0). -/
theorem teich_isUnit_of_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0) : IsUnit (teich p P α) := by
  classical
  let ζ := teich p P α
  let m := p ^ P.inertiaDeg ℤ - 1
  have hfpos : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  have hp0 : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hpow2 : 2 ≤ p ^ P.inertiaDeg ℤ := by
    calc
      2 ≤ p := hp2
      _ ≤ p ^ 1 := by rw [pow_one]
      _ ≤ p ^ P.inertiaDeg ℤ := Nat.pow_le_pow_right hp0 (Nat.succ_le_of_lt hfpos)
  have hm1 : 1 ≤ m := by
    dsimp [m]
    omega
  have hζm : ζ ^ m = 1 := by
    dsimp [m]
    exact teich_pow_card_sub_one (p := p) (P := P) (α := α) hα
  refine ⟨⟨ζ, ζ ^ (m - 1), ?_, ?_⟩, rfl⟩
  · calc
      ζ * ζ ^ (m - 1) = ζ ^ ((m - 1) + 1) := by rw [← pow_succ']
      _ = ζ ^ m := by rw [Nat.sub_add_cancel hm1]
      _ = 1 := hζm
  · calc
      ζ ^ (m - 1) * ζ = ζ * ζ ^ (m - 1) := by rw [mul_comm]
      _ = 1 := by
        calc
          ζ * ζ ^ (m - 1) = ζ ^ ((m - 1) + 1) := by rw [← pow_succ']
          _ = ζ ^ m := by rw [Nat.sub_add_cancel hm1]
          _ = 1 := hζm

/-- Packaged stone-3 statement: every nonzero residue `α : κ` admits a unit
`ζ ∈ kpInt p P` whose reduction is `α` and which is a `(p^f−1)`-st root of
unity (`ζ^(p^f−1) = 1`, so `ζ^(p^f) = ζ` as well).  This is the Teichmüller
section `κ^× → 𝒪_{K_P}^×` of the unramified-subfield construction. -/
theorem exists_rootOfUnity_lift (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0) :
    ∃ ζ : kpInt p P,
      IsUnit ζ ∧
      ζ ^ (p ^ P.inertiaDeg ℤ - 1) = 1 ∧
      Ideal.Quotient.mk (maximalIdeal (kpInt p P)) ζ = α := by
  refine ⟨teich p P α, ?_, ?_, ?_⟩
  · exact teich_isUnit_of_ne_zero (p := p) (P := P) (α := α) hα
  · exact teich_pow_card_sub_one (p := p) (P := P) (α := α) hα
  · exact teich_mod_eq (p := p) (P := P) α

/-- The root chain is multiplicative: `rootChain (α·β) = rootChain α · rootChain β`
(coefficient 0 is injective on the perfection of the perfect residue field,
and both sides have coefficient 0 equal to `α·β`). -/
theorem rootChain_mul (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α β : kap p P) :
    rootChain p P (α * β) = rootChain p P α * rootChain p P β := by
  classical
  have hb : Function.Bijective (Perfection.coeff (kap p P) p 0) :=
    Commons.FieldTheory.Perfection.coeff_zero_bijective_of_perfect (R := kap p P) p
  apply hb.1
  rw [rootChain_coeff_zero, map_mul, rootChain_coeff_zero, rootChain_coeff_zero]

/-- The root chain of 1 is 1. -/
theorem rootChain_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    rootChain p P 1 = 1 := by
  classical
  have hb : Function.Bijective (Perfection.coeff (kap p P) p 0) :=
    Commons.FieldTheory.Perfection.coeff_zero_bijective_of_perfect (R := kap p P) p
  apply hb.1
  rw [rootChain_coeff_zero, map_one]

/-- The Teichmüller lift is multiplicative: `teich (α·β) = teich α · teich β`
(`teichmuller₀` is a monoid-with-zero homomorphism and the root chain is
multiplicative). -/
theorem teich_mul (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α β : kap p P) :
    teich p P (α * β) = teich p P α * teich p P β := by
  unfold teich
  rw [← map_mul, rootChain_mul]

/-- The Teichmüller lift of 1 is 1. -/
theorem teich_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    teich p P 1 = 1 := by
  unfold teich
  rw [rootChain_one, map_one]

/-- On the multiplicative submonoid of nonzero residues the Teichmüller lift
is a unit-valued monoid homomorphism (a section of the residue map): the
`teich_mul`/`teich_one` laws together with `teich_isUnit_of_ne_zero`. -/
theorem teich_mul_unit (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α β : kap p P)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    IsUnit (teich p P (α * β)) := by
  exact teich_isUnit_of_ne_zero (p := p) (P := P) (mul_ne_zero hα hβ)

/-- Generic bridge: a power of a nonzero field element equals 1 iff the
corresponding power of its unit is 1. -/
lemma unit_pow_eq_one_of_val_pow_eq_one {G₀ : Type u} [Field G₀] {a : G₀} (ha : a ≠ 0)
    {m : ℕ} (h : a ^ m = 1) : (Units.mk0 a ha) ^ m = 1 := by
  apply Units.ext
  simp [Units.val_pow_eq_pow_val, h]

/-- **Exact order of the Teichmüller lift**: if `α` is a generator of the unit
group of the residue field (i.e. `orderOf (Units.mk0 α hα) = p^f − 1`), then
`teich α` has exact order `p^f − 1` in the multiplicative monoid of `kpInt`.

The upper bound `orderOf (teich α) | p^f − 1` is `teich_pow_card_sub_one`
(monoid `orderOf_dvd_iff_pow_eq_one`); the lower bound `p^f − 1 | orderOf ζ`
comes from reducing `ζ^(orderOf ζ) = 1` modulo the maximal ideal
(`mk (ζ^m) = (mk ζ)^m`, `teich_mod_eq`), which forces `α^(orderOf ζ) = 1`,
hence (α a generator) `p^f − 1 | orderOf ζ`. -/
theorem teich_orderOf_eq (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    orderOf (teich p P α) = p ^ P.inertiaDeg ℤ - 1 := by
  classical
  let ζ := teich p P α
  let q := p ^ P.inertiaDeg ℤ - 1
  have hζq : ζ ^ q = 1 := by
    dsimp [ζ, q]
    exact teich_pow_card_sub_one (p := p) (P := P) (α := α) hα
  have hmq : orderOf ζ ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hζq
  have hζm : ζ ^ orderOf ζ = 1 := pow_orderOf_eq_one ζ
  have hred0 : (Ideal.Quotient.mk (maximalIdeal (kpInt p P))) (ζ ^ orderOf ζ) = 1 := by
    rw [hζm]
    simp
  have hmk : (Ideal.Quotient.mk (maximalIdeal (kpInt p P))) (ζ ^ orderOf ζ)
      = (Ideal.Quotient.mk (maximalIdeal (kpInt p P)) ζ) ^ orderOf ζ := by
    rw [map_pow]
  have hαm : α ^ orderOf ζ = 1 := by
    rw [hmk] at hred0
    dsimp [ζ] at hred0
    rw [teich_mod_eq (p := p) (P := P) α] at hred0
    exact hred0
  have hunit : (Units.mk0 α hα) ^ orderOf ζ = 1 :=
    unit_pow_eq_one_of_val_pow_eq_one hα hαm
  have hqm : q ∣ orderOf ζ := by
    dsimp [q]
    rw [← hgen]
    exact orderOf_dvd_iff_pow_eq_one.mpr hunit
  exact Nat.dvd_antisymm hmq hqm

/-- **Primitive `(p^f−1)`-st root of unity in `kpInt`**: the unit group of the
finite residue field `κ` is cyclic (`IsCyclic`, finite-field theory), so it
has a generator `α`; its Teichmüller lift `ζ := teich α` is a unit of exact
order `p^f − 1` reducing to the nonzero generator `α`.  This `ζ` is the
generator of the roots of unity that the unramified-subfield construction
`W = ℚ_p[ζ]` uses. -/
theorem exists_primitive_rootOfUnity (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    ∃ ζ : kpInt p P,
      orderOf ζ = p ^ P.inertiaDeg ℤ - 1 ∧ IsUnit ζ ∧
        Ideal.Quotient.mk (maximalIdeal (kpInt p P)) ζ ≠ 0 := by
  classical
  haveI : Fintype (kap p P) := Fintype.ofFinite (kap p P)
  haveI : Fintype (kap p P)ˣ := inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (kap p P)ˣ)
  have hg_order : orderOf g = p ^ P.inertiaDeg ℤ - 1 := by
    calc
      orderOf g = Nat.card (kap p P)ˣ := orderOf_eq_card_of_forall_mem_zpowers hg
      _ = Nat.card (kap p P) - 1 := Nat.card_units (kap p P)
      _ = p ^ P.inertiaDeg ℤ - 1 := by rw [kap_card p P]
  have hg0 : (g : kap p P) ≠ 0 := Units.ne_zero g
  have hgen : orderOf (Units.mk0 (g : kap p P) hg0) = p ^ P.inertiaDeg ℤ - 1 := by
    calc
      orderOf (Units.mk0 (g : kap p P) hg0) = orderOf g := by
        congr 1
        apply Units.ext
        simp
      _ = p ^ P.inertiaDeg ℤ - 1 := hg_order
  refine ⟨teich p P (g : kap p P), ?_, ?_, ?_⟩
  · exact teich_orderOf_eq (p := p) (P := P) (α := (g : kap p P)) hg0 hgen
  · exact teich_isUnit_of_ne_zero (p := p) (P := P) (α := (g : kap p P)) hg0
  · rw [teich_mod_eq (p := p) (P := P) (g : kap p P)]
    exact hg0

/-- The reduction modulo the maximal ideal commutes with powers of the
Teichmüller lift: `mk (teich α ^ k) = α^k`. -/
lemma teich_power_mod_eq (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) (k : ℕ) :
    Ideal.Quotient.mk (maximalIdeal (kpInt p P)) (teich p P α ^ k) = α ^ k := by
  rw [map_pow, teich_mod_eq]

/-- The reduction of a power of the Teichmüller lift is nonzero when `α` is. -/
lemma teich_power_mod_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0) (k : ℕ) :
    Ideal.Quotient.mk (maximalIdeal (kpInt p P)) (teich p P α ^ k) ≠ 0 := by
  rw [teich_power_mod_eq]
  exact pow_ne_zero k hα

/-- The unit of `κ` given by the reduction of `teich α ^ k`. -/
noncomputable def teichPowerUnit (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0) (k : ℕ) : (kap p P)ˣ :=
  Units.mk0 (Ideal.Quotient.mk (maximalIdeal (kpInt p P)) (teich p P α ^ k))
    (teich_power_mod_ne_zero (p := p) (P := P) (α := α) hα k)

/-- The value of `teichPowerUnit` is `α^k`. -/
lemma teichPowerUnit_val (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0) (k : ℕ) :
    (teichPowerUnit (p := p) (P := P) hα k : kap p P) = α ^ k := by
  simp [teichPowerUnit, teich_power_mod_eq]

/-- Distinctness of the first `q` powers of a generator `α` of the residue
unit group (where `q := p^f − 1 = orderOf α`): `α^i ≠ α^j` for `0 ≤ i < j < q`. -/
lemma kap_pow_ne_of_lt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0) (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    {i j : ℕ} (hij : i < j) (hj : j < p ^ P.inertiaDeg ℤ - 1) : α ^ i ≠ α ^ j := by
  classical
  intro h
  have hαi0 : α ^ i ≠ 0 := pow_ne_zero i hα
  have hαji : α ^ (j - i) = 1 := by
    have hmul : α ^ i * α ^ (j - i) = α ^ i * 1 := by
      calc
        α ^ i * α ^ (j - i) = α ^ (i + (j - i)) := by rw [← pow_add]
        _ = α ^ j := by congr 1; exact Nat.add_sub_of_le (le_of_lt hij)
        _ = α ^ i := h.symm
        _ = α ^ i * 1 := by rw [mul_one]
    exact mul_left_cancel₀ hαi0 hmul
  have hunit1 : (Units.mk0 α hα) ^ (j - i) = 1 :=
    unit_pow_eq_one_of_val_pow_eq_one hα hαji
  have hdiv : p ^ P.inertiaDeg ℤ - 1 ∣ j - i := by
    rw [← hgen]
    exact orderOf_dvd_iff_pow_eq_one.mpr hunit1
  have hpos : 0 < j - i := by omega
  have hle : p ^ P.inertiaDeg ℤ - 1 ≤ j - i := Nat.le_of_dvd hpos hdiv
  omega

/-- The reduction of the Teichmüller lift of a generator of `κ^×` maps the
first `q` powers injectively: `mk (teich α ^ i) ≠ mk (teich α ^ j)` for
distinct `i j < q`. -/
lemma teich_power_reduce_injective (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0) (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Function.Injective
      (fun k : Fin (p ^ P.inertiaDeg ℤ - 1) =>
        teichPowerUnit (p := p) (P := P) hα (k : ℕ)) := by
  intro i j hij
  apply Fin.ext
  have hval : α ^ (i : ℕ) = α ^ (j : ℕ) := by
    -- from Units.ext hij via val
    have hv := congrArg (fun u : (kap p P)ˣ => (u : kap p P)) hij
    simpa [teichPowerUnit_val] using hv
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hgt
  · exfalso
    exact kap_pow_ne_of_lt (p := p) (P := P) (α := α) hα hgen hlt (j.2) hval
  · exact heq
  · exfalso
    exact (kap_pow_ne_of_lt (p := p) (P := P) (α := α) hα hgen hgt (i.2) hval.symm)

/-- Surjectivity: every unit of the residue field is the reduction of a power
of the Teichmüller lift of a generator (`k < q`). -/
lemma teich_power_reduce_surjective (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0) (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Function.Surjective
      (fun k : Fin (p ^ P.inertiaDeg ℤ - 1) =>
        teichPowerUnit (p := p) (P := P) hα (k : ℕ)) := by
  classical
  intro x
  haveI : Fintype (kap p P) := Fintype.ofFinite (kap p P)
  haveI : DecidableEq (kap p P) := Classical.decEq _
  haveI : Fintype (kap p P)ˣ := inferInstance
  have hcardU : Nat.card (kap p P)ˣ = p ^ P.inertiaDeg ℤ - 1 := by
    calc
      Nat.card (kap p P)ˣ = Nat.card (kap p P) - 1 := Nat.card_units (kap p P)
      _ = p ^ P.inertiaDeg ℤ - 1 := by rw [kap_card p P]
  have hgen' : orderOf (Units.mk0 α hα) = Fintype.card (kap p P)ˣ := by
    calc
      orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1 := hgen
      _ = Nat.card (kap p P)ˣ := hcardU.symm
      _ = Fintype.card (kap p P)ˣ := Nat.card_eq_fintype_card
  obtain ⟨k0, hk0lt, hk0⟩ :=
    Commons.GroupTheory.OrderOf.exists_pow_lt_card_eq_of_orderOf_eq_card (Units.mk0 α hα) hgen' x
  refine ⟨⟨k0, ?_⟩, ?_⟩
  · rw [← Nat.card_eq_fintype_card, hcardU] at hk0lt
    exact hk0lt
  · apply Units.ext
    -- (teichPowerUnit hα k0 : kap) = (x : kap), i.e. α^k0 = x.val
    have hv := congrArg (fun u : (kap p P)ˣ => (u : kap p P)) hk0
    simpa [teichPowerUnit_val, Units.val_pow_eq_pow_val] using hv

/-- **Residue surjectivity of the Teichmüller roots of unity (central
residue-degree fact)**: for `α` a generator of the unit group of the residue
field (`orderOf (Units.mk0 α hα) = q := p^f − 1`), the reductions of the
first `q` powers of `teich α` enumerate exactly the units of `κ` — i.e. the
`q`-th roots of unity of `kpInt` reduce bijectively onto `κ^×`.  This is the
input of the residue-degree argument for the unramified subfield
`W = ℚ_p[ζ]` (`[W : ℚ_p] = f`), where it shows the residue field of `W`
contains (and, being a residue of a subfield of `K_P`, is contained in) `κ`. -/
theorem teich_power_units_bijective (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {α : kap p P}
    (hα : α ≠ 0) (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Function.Bijective
      (fun k : Fin (p ^ P.inertiaDeg ℤ - 1) =>
        teichPowerUnit (p := p) (P := P) hα (k : ℕ)) :=
  ⟨teich_power_reduce_injective (p := p) (P := P) (α := α) hα hgen,
   teich_power_reduce_surjective (p := p) (P := P) (α := α) hα hgen⟩



/-! ## Next stone (degree of the unramified subfield): target statement and gaps

With the residue bijection of `teich_power_units_bijective` in hand, the next
stone of the wild-different programme (Session-54 analysis) is the degree of
the unramified subfield generated by the Teichmüller root of unity:

**TARGET.**  Let `ζ := teich p P α` for `α` a generator of the unit group of
the residue field `κ = kap p P` (`orderOf (Units.mk0 α hα) = p^f − 1`,
`f := P.inertiaDeg ℤ`), and let `W` be the subfield of `K_P := kpAdic p P`
generated over the `ℚ_p`-base by `ζ`.  Prove

    Module.finrank ℚ_[p] W = P.inertiaDeg ℤ .

The missing API facts standing between the (proved) residue bijection and
this statement, in dependency order:

1. **A bundled `Algebra (QpAdic p) (kpAdic p P)` instance.**  Currently only
   `kpAdic_algebra_qp_exists : Nonempty (Algebra (QpAdic p) (kpAdic p P))`
   exists (BaseAlgebra).  One needs a concrete instance (classical
   extraction) with the compatibility laws: the algebraMap extends
   `algebraMap ℚ` (scalar tower through the dense embeddings) and is
   valuation-compatible.  Only then can `W` be named (as
   `Algebra.adjoin (QpAdic p) {ζ}` or an `IntermediateField` of `K_P`).
2. **Finiteness and degree of the completion tower.**
   `Module.Finite (QpAdic p) (kpAdic p P)` and
   `Module.finrank (QpAdic p) (kpAdic p P) = e·f` with
   `e := P.ramificationIdx ℤ` (completion preserves ramification and
   inertia).  Survey Mathlib `NumberField/Completion` / `AdicCompletion` /
   `Ideal.sum_ramification_inertia_eq_finrank`.
3. **The degree of `ℚ_p(ζ)`.**  Two chapter-scale routes:
   - (cyclotomic) `[ℚ_p(μ_q) : ℚ_p] = ord_q(p)` (`q := p^f−1`, the order of
     `p` in `(ℤ/qℤ)^×`) — a p-adic cyclotomic-degree chapter (Mathlib's
     cyclotomic theory is over number fields), plus the pure-ℕ input
     `ord_{p^f−1}(p) = f`, i.e. `(p^f − 1) ∣ (p^k − 1) ↔ f ∣ k` for `p ≥ 2`;
   - (unramified/residue) `p ∤ q` ⟹ `ℚ_p(ζ)` unramified over `ℚ_p`, so its
     degree equals its residue degree `[κ_W : 𝔽_p]`; the residue bijection
     above shows `κ ⊆ κ_W` (all of `κ^×` occurs among the reductions
     `mk (ζ^k) = α^k`) and `W ⊆ K_P` gives `κ_W ⊆ κ`, forcing both equal `f`.
     Needs an unramified-extension / μ_{p'}-unramified API (absent).

After the degree statement: `K_P/W` is totally ramified of degree `e`
(fundamental identity), then stone 4 (the local trace identity
`Tr_{K_P/ℚ_p}(w) = e · Tr_{W/ℚ_p}(w)`), feeding the S1 wild-witness gate.
-/

/-! ### The easy half of the degree bound: `μ_q(𝒪_{K_P})` is the Teichmüller
image of `κ^×` (containment among the powers of a primitive lift)

Let `q := p^f − 1` (`f := P.inertiaDeg ℤ`).  This section proves the
root-of-unity containment on which the upper-bound half of `[W : ℚ_p] = f`
rests (the "easy half" — no unramified/cyclotomic extension theory):

* `kap_pow_pf_ge_two` — `p^f ≥ 2` (`f ≥ 1` from `Ideal.inertiaDeg_pos`);
* `qthRoot_mk_ne_zero` — a `q`-th root of unity `z ∈ kpInt` reduces to a
  nonzero residue (if `mk z = 0` then `0^q = mk (z^q) = 1`, `q ≥ 1`);
* `qthRoot_geomSum_reduction_ne_zero` — for `t` with `mk t = 1`, the
  geometric sum `∑_{i<q} t^i` reduces to `q·1 = −1 ≠ 0` (hence is a unit);
* `qthRoot_eq_teich` — every `q`-th root of unity in the valuation ring is
  the Teichmüller lift of its own reduction: with `ζ₀ := teich (mk z)`,
  `t := z · ζ₀^(q−1)` satisfies `t^q = 1` and `t ≡ 1 (mod mS)`, and the
  factorisation `(t−1)·(∑_{i<q} t^i) = 0` with the sum a unit forces
  `t = 1`, i.e. `z = ζ₀`.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

/-- `p^f ≥ 2` for `f := P.inertiaDeg ℤ` (helper for `q ≥ 1`). -/
lemma kap_pow_pf_ge_two (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    2 ≤ p ^ P.inertiaDeg ℤ := by
  have hf : 1 ≤ P.inertiaDeg ℤ := Nat.succ_le_of_lt (Ideal.inertiaDeg_pos P ℤ)
  calc
    2 ≤ p := (Fact.out : Nat.Prime p).two_le
    _ = p ^ 1 := by rw [pow_one]
    _ ≤ p ^ P.inertiaDeg ℤ := Nat.pow_le_pow_right (n := p)
      (Nat.Prime.pos (Fact.out : Nat.Prime p)) (i := 1) (j := P.inertiaDeg ℤ) hf

/-- The `(p^f−1)`-st roots of unity are nontrivial mod `mS`: if
`z^(p^f−1) = 1` then the reduction `mk z` is nonzero. -/
theorem qthRoot_mk_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {z : kpInt p P}
    (hz : z ^ (p ^ P.inertiaDeg ℤ - 1) = 1) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z ≠ 0 := by
  classical
  have hq1 : 1 ≤ p ^ P.inertiaDeg ℤ - 1 := by
    have hpf := kap_pow_pf_ge_two p P
    omega
  have hred : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z) ^
      (p ^ P.inertiaDeg ℤ - 1) = 1 := by
    rw [← map_pow, hz]
    simp
  intro hmk
  have h0 : (0 : kap p P) ^ (p ^ P.inertiaDeg ℤ - 1) = 1 := by
    simpa [hmk] using hred
  have hzpow : (0 : kap p P) ^ (p ^ P.inertiaDeg ℤ - 1) = 0 :=
    zero_pow (ne_of_gt hq1)
  exact (zero_ne_one : (0 : kap p P) ≠ (1 : kap p P)) (by
    calc
      (0 : kap p P) = (0 : kap p P) ^ (p ^ P.inertiaDeg ℤ - 1) := hzpow.symm
      _ = (1 : kap p P) := h0)

/-- For `t` with reduction `1`, the geometric sum `∑_{i<q} t^i`
(`q := p^f−1`) reduces to `q·1 = −1`, hence is nonzero. -/
lemma qthRoot_geomSum_reduction_ne_zero (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {t : kpInt p P} (ht : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) t = 1) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
      (∑ i ∈ Finset.range (p ^ P.inertiaDeg ℤ - 1), t ^ i) ≠ 0 := by
  classical
  have hnat : (p ^ P.inertiaDeg ℤ - 1) + 1 = p ^ P.inertiaDeg ℤ :=
    Nat.sub_add_cancel (m := 1) (by
      have hpf := kap_pow_pf_ge_two p P
      omega)
  have hpf0 : ((p ^ P.inertiaDeg ℤ : ℕ) : kap p P) = 0 := by
    have hchar : (p : kap p P) = 0 := CharP.cast_eq_zero (kap p P) p
    calc
      ((p ^ P.inertiaDeg ℤ : ℕ) : kap p P) = (p : kap p P) ^ P.inertiaDeg ℤ := by
        exact Nat.cast_pow (α := kap p P) p (P.inertiaDeg ℤ)
      _ = 0 := by
        rw [hchar]
        exact zero_pow (ne_of_gt (Ideal.inertiaDeg_pos P ℤ))
  have hqcast : ((p ^ P.inertiaDeg ℤ - 1 : ℕ) : kap p P) = (-1 : kap p P) := by
    calc
      ((p ^ P.inertiaDeg ℤ - 1 : ℕ) : kap p P)
          = ((p ^ P.inertiaDeg ℤ : ℕ) : kap p P) - 1 := by
            rw [Nat.cast_sub (by
              have hpf := kap_pow_pf_ge_two p P
              omega)]
            simp
      _ = (0 : kap p P) - 1 := by
            rw [hpf0]
      _ = -1 := by simp
  have hmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
      (∑ i ∈ Finset.range (p ^ P.inertiaDeg ℤ - 1), t ^ i) = (-1 : kap p P) := by
    rw [map_sum]
    calc
      (∑ i ∈ Finset.range (p ^ P.inertiaDeg ℤ - 1),
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (t ^ i))
          = ∑ i ∈ Finset.range (p ^ P.inertiaDeg ℤ - 1),
              (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) t) ^ i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [map_pow]
      _ = ∑ i ∈ Finset.range (p ^ P.inertiaDeg ℤ - 1), (1 : kap p P) ^ i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [ht]
      _ = ((p ^ P.inertiaDeg ℤ - 1 : ℕ) : kap p P) := by
            simp
      _ = (-1 : kap p P) := hqcast
  rw [hmk]
  exact neg_ne_zero.mpr (one_ne_zero (α := kap p P))

/-- **Containment (easy half)**: every `(p^f−1)`-st root of unity in the
valuation ring `kpInt p P` is the Teichmüller lift of its reduction. -/
theorem qthRoot_eq_teich (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] {z : kpInt p P}
    (hz : z ^ (p ^ P.inertiaDeg ℤ - 1) = 1) :
    z = teich p P (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z) := by
  classical
  let q := p ^ P.inertiaDeg ℤ - 1
  have hq1 : 1 ≤ q := by
    have hpf := kap_pow_pf_ge_two p P
    dsimp [q]
    omega
  have hz0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z ≠ 0 :=
    qthRoot_mk_ne_zero p P hz
  let ζ₀ : kpInt p P := teich p P (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z)
  have hzq : z ^ q = 1 := by simpa [q] using hz
  have hζq : ζ₀ ^ q = 1 := by
    dsimp [ζ₀]
    simpa [q] using teich_pow_card_sub_one (p := p) (P := P)
      (α := Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z) hz0
  have hζred : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) ζ₀ =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z := by
    dsimp [ζ₀]
    exact teich_mod_eq (p := p) (P := P) _
  let t : kpInt p P := z * ζ₀ ^ (q - 1)
  have htq : t ^ q = 1 := by
    dsimp [t]
    calc
      (z * ζ₀ ^ (q - 1)) ^ q = z ^ q * (ζ₀ ^ (q - 1)) ^ q := by rw [mul_pow]
      _ = z ^ q * ζ₀ ^ ((q - 1) * q) := by rw [pow_mul]
      _ = z ^ q * ζ₀ ^ (q * (q - 1)) := by ring_nf
      _ = z ^ q * (ζ₀ ^ q) ^ (q - 1) := by rw [pow_mul]
      _ = 1 := by rw [hzq, hζq, one_pow, mul_one]
  have htmk : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) t = 1 := by
    dsimp [t]
    calc
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (z * ζ₀ ^ (q - 1))
          = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z *
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) ζ₀) ^ (q - 1) := by
            rw [map_mul, map_pow]
      _ = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z *
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z) ^ (q - 1) := by
            rw [hζred]
      _ = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z) ^ q := by
            rw [mul_comm]
            rw [← pow_succ]
            congr 1
            exact Nat.sub_add_cancel (m := 1) hq1
      _ = 1 := by
            rw [← map_pow, hzq]
            simp
  have hsum : (t - 1) * (∑ i ∈ Finset.range q, t ^ i) = 0 := by
    calc
      (t - 1) * (∑ i ∈ Finset.range q, t ^ i)
          = (∑ i ∈ Finset.range q, t ^ i) * (t - 1) := by ring
      _ = t ^ q - 1 := geom_sum_mul t q
      _ = 0 := by rw [htq]; simp
  have hsum_unit : IsUnit (∑ i ∈ Finset.range q, t ^ i) := by
    have hred_ne := qthRoot_geomSum_reduction_ne_zero p P htmk
    have hx : (∑ i ∈ Finset.range q, t ^ i) ∉ IsLocalRing.maximalIdeal (kpInt p P) := by
      intro hxmem
      exact hred_ne ((Ideal.Quotient.eq_zero_iff_mem
        (I := IsLocalRing.maximalIdeal (kpInt p P))).mpr hxmem)
    exact (not_not.mp (fun hnu => hx (by
      exact (IsLocalRing.mem_maximalIdeal (∑ i ∈ Finset.range q, t ^ i)).mpr (mem_nonunits_iff.mpr hnu))))
  have ht1 : t - 1 = 0 := by
    have hEq : (t - 1) * (∑ i ∈ Finset.range q, t ^ i)
        = 0 * (∑ i ∈ Finset.range q, t ^ i) := by
      rw [hsum, zero_mul]
    exact (IsUnit.mul_left_inj (a := (∑ i ∈ Finset.range q, t ^ i)) (b := t - 1) (c := 0)
      hsum_unit).mp hEq
  have ht : t = 1 := sub_eq_zero.mp ht1
  have ht' : z * ζ₀ ^ (q - 1) = 1 := by simpa [t] using ht
  have hzζ : z = ζ₀ := by
    have hmul : (z * ζ₀ ^ (q - 1)) * ζ₀ = ζ₀ := by
      rw [ht']
      rw [one_mul]
    calc
      z = z * ζ₀ ^ q := by
            rw [hζq]
            simp
      _ = (z * ζ₀ ^ (q - 1)) * ζ₀ := by
            have hq : q = q - 1 + 1 := (Nat.sub_add_cancel (m := 1) hq1).symm
            nth_rw 1 [hq]
            rw [pow_succ]
            rw [mul_assoc]
      _ = ζ₀ := hmul
  simpa [ζ₀] using hzζ

/-- The Teichmüller lift commutes with natural powers:
`teich (α^k) = (teich α)^k` (from `teich_mul` / `teich_one`). -/
theorem teich_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (k : ℕ) :
    teich p P (α ^ k) = (teich p P α) ^ k := by
  classical
  induction k with
  | zero =>
      simp [teich_one]
  | succ k ih =>
      calc
        teich p P (α ^ (k + 1)) = teich p P (α ^ k * α) := by
              rw [pow_succ]
        _ = teich p P (α ^ k) * teich p P α := teich_mul p P (α ^ k) α
        _ = (teich p P α) ^ k * teich p P α := by rw [ih]
        _ = (teich p P α) ^ (k + 1) := by rw [pow_succ]
