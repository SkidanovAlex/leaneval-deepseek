import Mathlib
import Submission.Vdw.LocalField.CyclotomicDegree
import Submission.Vdw.LocalField.RamificationCompat
import Submission.Vdw.LocalField.QpPadic
import Submission.Commons.NumberTheory.Padics.hensel_lift_coprime_factorization

open Classical
open scoped NumberField Polynomial WithZero

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# Local-field chapter (G3 upper bound, Hensel route): `deg (minpoly ζ) ≤ f`

Let `α` be a generator of the unit group of the residue field
`κ = kap p P` (so `orderOf (Units.mk0 α hα) = q := p^f − 1`, `f :=
P.inertiaDeg ℤ` — κ has `p^f` elements) and let
`ζ := teich p P α : kpInt p P` be its Teichmüller lift (an exact-order-`q`
root of unity in the valuation ring of `K_P := kpAdic p P`).  This module
proves the **upper bound**

    (minpoly (QpAdic p) ζ).natDegree ≤ P.inertiaDeg ℤ

via the classical Hensel route over `ℤ_p = QpInt p`:
* ζ is integral over `QpInt p` (`IsIntegral (QpInt p) x`, root of `X^q − 1`);
  hence its minimal polynomial over `QpAdic p` is the scalar extension of
  `gR := minpoly (QpInt p) x` (`minpoly.isIntegrallyClosed_eq_field_fractions'`
  — `QpInt` is integrally closed);
* `gR ∣ X^q − 1` over `QpInt`; reducing mod `p` (the reduction map
  `qpReductionHom : QpInt p →+* ZMod p`), `ḡ := (gR.map qpReductionHom)`
  divides `X^q − 1` over `ZMod p`, which is squarefree (p ∤ q);
* **Hensel** (fleet lemma at `PadicInt`, transported along
  `qpPadicIntEquiv`): a monic polynomial over `ℤ_p` that is irreducible over
  `ℚ_p` and has squarefree reduction is irreducible modulo `p` — so `ḡ` is
  irreducible over `ZMod p`;
* ζ reduces to α (`teich_mod_eq`), so `ḡ` has the root α ∈ κ (the residue
  field contains `𝔽_p`); since `ḡ` is monic irreducible over `𝔽_p`, it is the
  minimal polynomial `m_α` of α over `𝔽_p`, whose degree is at most
  `[κ : 𝔽_p] = f`.  Hence `deg g = deg gR = deg ḡ = deg m_α ≤ f`.

The lower bound `f ≤ deg g` is `teich_powers_independent_qpAdic`
(TeichLift.lean), so together `deg g = f`: the degree of the cyclotomic
subfield `W = ℚ_p(ζ)` — the residue half of the fundamental identity for
`W/ℚ_p`, and the content of the `(B)` bridge of the Session-86 roadmap.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The reduction homomorphism `QpInt p →+* ZMod p` (the canonical map onto
the residue field of the `p`-adic integers, expressed through the standard
`ℤ_[p]` via `qpPadicIntEquiv`). -/
noncomputable def qpReductionHom (p : ℕ) [Fact (Nat.Prime p)] : QpInt p →+* ZMod p :=
  PadicInt.toZMod.comp (qpPadicIntEquiv p : QpInt p →+* PadicInt p)

/-- ζ = `teich p P α` has exact order `q := p^f − 1` as a power of `1` in
`kpInt`. -/
lemma zPowCard (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    (((teich p P α : kpInt p P) : kpAdic p P) ^ (p ^ P.inertiaDeg ℤ - 1) : kpAdic p P) = 1 := by
  change (algebraMap (kpInt p P) (kpAdic p P) (teich p P α)) ^ (p ^ P.inertiaDeg ℤ - 1) =
      (algebraMap (kpInt p P) (kpAdic p P) (1 : kpInt p P))
  rw [← map_pow]
  exact congrArg (algebraMap (kpInt p P) (kpAdic p P))
    (teich_pow_card_sub_one (p := p) (P := P) (α := α) hα)

/-- ζ (as an element of `K_P`) is integral over `QpInt p`: a root of the
monic polynomial `X^q − 1 ∈ (QpInt p)[X]`. -/
theorem teich_isIntegral_qpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    IsIntegral (QpInt p) (((teich p P α : kpInt p P) : kpAdic p P)) := by
  refine ⟨Polynomial.X ^ (p ^ P.inertiaDeg ℤ - 1) - 1, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C (1 : QpInt p) (by
      have hpf := kap_pow_pf_ge_two p P
      omega)
  · have hxq' : (((teich p P α : kpInt p P) : kpAdic p P) ^ (p ^ P.inertiaDeg ℤ - 1) : kpAdic p P) = 1 :=
      zPowCard p P hα
    simp [hxq']

/-- The minimal polynomial of ζ over `QpInt p` (a monic polynomial over the
`p`-adic integers; `x := ((teich α : kpInt) : kpAdic)` is integral over
`QpInt p` by `teich_isIntegral_qpInt`). -/
noncomputable def teichMinpolyInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : (QpInt p)[X] :=
  minpoly (QpInt p) (((teich p P α : kpInt p P) : kpAdic p P))

/-- The minimal polynomial of ζ over `QpInt p` is monic and annihilates ζ. -/
theorem teichMinpolyInt_monic (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    (teichMinpolyInt p P α).Monic :=
  minpoly.monic (teich_isIntegral_qpInt p P hα)

/-- The minimal polynomial of ζ over `QpInt p` annihilates ζ (as a `QpInt`
-algebra element of `K_P`). -/
theorem teichMinpolyInt_aeval (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (_hα : α ≠ 0) :
    Polynomial.aeval (((teich p P α : kpInt p P) : kpAdic p P)) (teichMinpolyInt p P α) = 0 :=
  minpoly.aeval (QpInt p) (((teich p P α : kpInt p P) : kpAdic p P))

/-- **Field-fractions identity**: the minimal polynomial of ζ over the field
`QpAdic p` is the scalar extension of `teichMinpolyInt` (the minimal
polynomial over the integrally closed `QpInt p`). -/
theorem teich_minpoly_eq_field_map (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    minpoly (QpAdic p) (((teich p P α : kpInt p P) : kpAdic p P)) =
      (teichMinpolyInt p P α).map (algebraMap (QpInt p) (QpAdic p)) := by
  unfold teichMinpolyInt
  exact minpoly.isIntegrallyClosed_eq_field_fractions' (R := QpInt p) (K := QpAdic p)
    (S := kpAdic p P) (s := (((teich p P α : kpInt p P) : kpAdic p P)))
    (teich_isIntegral_qpInt p P hα)

/-- The scalar-extension minimal polynomial annihilates ζ over `QpAdic p`. -/
theorem teich_minpoly_aeval_field (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (_hα : α ≠ 0) :
    Polynomial.aeval (((teich p P α : kpInt p P) : kpAdic p P))
        (minpoly (QpAdic p) (((teich p P α : kpInt p P) : kpAdic p P))) = 0 :=
  minpoly.aeval (QpAdic p) (((teich p P α : kpInt p P) : kpAdic p P))


/-! ## 1. Divisibility and squarefree reduction -/

/-- **Field-level divisibility**: the minimal polynomial of ζ over `QpAdic p`
divides `X^q − 1`, `q := p^f − 1` (ζ is a `q`-th root of unity). -/
theorem teich_minpoly_dvd_X_pow_sub_one_field (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    minpoly (QpAdic p) (((teich p P α : kpInt p P) : kpAdic p P))
      ∣ (Polynomial.X ^ (p ^ P.inertiaDeg ℤ - 1) - 1 : (QpAdic p)[X]) := by
  classical
  let x : kpAdic p P := ((teich p P α : kpInt p P) : kpAdic p P)
  have hxq : (x ^ (p ^ P.inertiaDeg ℤ - 1) : kpAdic p P) = 1 := by
    simpa [x] using zPowCard p P hα
  have haev : Polynomial.aeval x (Polynomial.X ^ (p ^ P.inertiaDeg ℤ - 1) - 1 : (QpAdic p)[X]) = 0 := by
    simp [Polynomial.aeval_X_pow, hxq]
  exact minpoly.dvd (QpAdic p) x haev

/-- **Integer-level divisibility**: `gR := minpoly (QpInt p) ζ` divides
`X^q − 1` over `QpInt p` — the field-level divisibility plus
`Monic.dvd_iff_fraction_map_dvd_fraction_map` (QpInt is integrally closed in
QpAdic = its fraction field). -/
theorem teichMinpolyInt_dvd_X_pow_sub_one (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    teichMinpolyInt p P α ∣
      (Polynomial.X ^ (p ^ P.inertiaDeg ℤ - 1) - 1 : (QpInt p)[X]) := by
  classical
  have hfd : minpoly (QpAdic p) (((teich p P α : kpInt p P) : kpAdic p P))
      ∣ (Polynomial.X ^ (p ^ P.inertiaDeg ℤ - 1) - 1 : (QpAdic p)[X]) :=
    teich_minpoly_dvd_X_pow_sub_one_field p P hα
  -- over the field the statement is exactly the map of the QpInt statement
  have hmap : (minpoly (QpAdic p) (((teich p P α : kpInt p P) : kpAdic p P))) =
      (teichMinpolyInt p P α).map (algebraMap (QpInt p) (QpAdic p)) :=
    teich_minpoly_eq_field_map p P hα
  have hX : (Polynomial.X ^ (p ^ P.inertiaDeg ℤ - 1) - 1 : (QpAdic p)[X]) =
      ((Polynomial.X ^ (p ^ P.inertiaDeg ℤ - 1) - 1 : (QpInt p)[X]).map
        (algebraMap (QpInt p) (QpAdic p))) := by
    symm
    simp [Polynomial.map_X]
  have hgmon : (teichMinpolyInt p P α).Monic := teichMinpolyInt_monic p P hα
  have hXmon : (Polynomial.X ^ (p ^ P.inertiaDeg ℤ - 1) - 1 : (QpInt p)[X]).Monic :=
    Polynomial.monic_X_pow_sub_C (1 : QpInt p) (by
      have hpf := kap_pow_pf_ge_two p P
      omega)
  rw [hmap, hX] at hfd
  exact Polynomial.Monic.dvd_of_fraction_map_dvd_fraction_map hXmon hgmon hfd

/-- `X^q − 1` over `ZMod p` is separable (equivalently squarefree):
`q := p^f − 1` is not divisible by `p`. -/
theorem X_pow_sub_one_separable_zmod (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (Polynomial.X ^ (p ^ P.inertiaDeg ℤ - 1) - 1 : (ZMod p)[X]).Separable := by
  rw [Polynomial.X_pow_sub_one_separable_iff]
  intro hz
  have hdiv : p ∣ p ^ P.inertiaDeg ℤ - 1 :=
    (CharP.cast_eq_zero_iff (ZMod p) p (p ^ P.inertiaDeg ℤ - 1)).1 hz
  have hf1 : 1 ≤ P.inertiaDeg ℤ := Nat.succ_le_of_lt (Ideal.inertiaDeg_pos P ℤ)
  have hpfp : p ∣ p ^ P.inertiaDeg ℤ := by simpa using (pow_dvd_pow p hf1 : p ^ 1 ∣ p ^ P.inertiaDeg ℤ)
  have ha1 : 1 ≤ p ^ P.inertiaDeg ℤ :=
    Nat.succ_le_of_lt (pow_pos (Fact.out : Nat.Prime p).pos _)
  have hd1 : p ∣ 1 := by
    have hsub := Nat.dvd_sub hpfp hdiv
    have hsub' : p ^ P.inertiaDeg ℤ - (p ^ P.inertiaDeg ℤ - 1) = 1 := by omega
    rwa [hsub'] at hsub
  have hp1 : p = 1 := Nat.dvd_one.mp hd1
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  omega

/-- `X^q − 1` over `ZMod p` is squarefree. -/
theorem X_pow_sub_one_squarefree_zmod (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Squarefree (Polynomial.X ^ (p ^ P.inertiaDeg ℤ - 1) - 1 : (ZMod p)[X]) := by
  classical
  haveI : PerfectField (ZMod p) := PerfectField.ofFinite
  exact (PerfectField.separable_iff_squarefree (K := ZMod p)).1
    (X_pow_sub_one_separable_zmod p P)

/-- The reduction `ḡ := gR.map qpReductionHom` of the minimal polynomial is
squarefree: it divides `X^q − 1`, which is squarefree over `ZMod p`. -/
theorem teichMinpolyInt_reduction_squarefree (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    Squarefree ((teichMinpolyInt p P α).map (qpReductionHom p)) := by
  classical
  -- gR | X^q−1 over QpInt; map through qpReductionHom
  have hdvd := teichMinpolyInt_dvd_X_pow_sub_one p P hα
  rcases hdvd with ⟨h, hh⟩
  have hmap : ((teichMinpolyInt p P α).map (qpReductionHom p)) *
        h.map (qpReductionHom p) =
      (Polynomial.X ^ (p ^ P.inertiaDeg ℤ - 1) - 1 : (ZMod p)[X]) := by
    rw [← Polynomial.map_mul, ← hh]
    simp [Polynomial.map_X]
  have hdvd' : (teichMinpolyInt p P α).map (qpReductionHom p) ∣
      (Polynomial.X ^ (p ^ P.inertiaDeg ℤ - 1) - 1 : (ZMod p)[X]) :=
    ⟨h.map (qpReductionHom p), hmap.symm⟩
  exact Squarefree.squarefree_of_dvd hdvd' (X_pow_sub_one_squarefree_zmod p P)



/-! ## 2. The QpInt-level Hensel lifting (transport of the PadicInt lemma) -/

/-- **QpInt-level Hensel**: a monic polynomial `g` over `QpInt p` whose
reduction `g.map (qpReductionHom p)` factors as `a * b` with `a, b` monic and
coprime lifts to a factorization `g = A * B` over `QpInt p` with matching
degrees.  (Transport of the fleet lemma
`Commons.NumberTheory.Padics.hensel_lift_coprime_factorization` along the ring
equivalence `qpPadicIntEquiv : QpInt p ≃+* PadicInt p`.) -/
theorem hensel_lift_qpInt {p : ℕ} [Fact (Nat.Prime p)] {g : (QpInt p)[X]} (hg : g.Monic)
    {a : (ZMod p)[X]} (ha : a.Monic) {b : (ZMod p)[X]} (hb : b.Monic)
    (hfac : g.map (qpReductionHom p) = a * b) (hcop : IsCoprime a b) :
    ∃ A B : (QpInt p)[X],
      A.Monic ∧ B.Monic ∧ A.natDegree = a.natDegree ∧ B.natDegree = b.natDegree ∧
        g = A * B := by
  classical
  let e : QpInt p ≃+* PadicInt p := qpPadicIntEquiv p
  let g' : (PadicInt p)[X] := g.map (e : QpInt p →+* PadicInt p)
  have hfac' : g'.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = a * b := by
    dsimp [g']
    rw [Polynomial.map_map]
    change g.map (qpReductionHom p) = a * b
    exact hfac
  have hg'mon : g'.Monic := by
    dsimp [g']
    exact Polynomial.Monic.map _ hg
  rcases (Commons.NumberTheory.Padics.hensel_lift_coprime_factorization (f := g')
    hg'mon ha hb hfac' hcop) with ⟨A', B', hAmon, hBmon, hdegA, hdegB, hEq, hredA, hredB⟩
  refine ⟨A'.map (e.symm : PadicInt p →+* QpInt p), B'.map (e.symm : PadicInt p →+* QpInt p),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact Polynomial.Monic.map _ hAmon
  · exact Polynomial.Monic.map _ hBmon
  · calc
      (A'.map (e.symm : PadicInt p →+* QpInt p)).natDegree = A'.natDegree := by
        exact Polynomial.natDegree_map_eq_of_injective (RingEquiv.injective e.symm) A'
      _ = a.natDegree := hdegA
  · calc
      (B'.map (e.symm : PadicInt p →+* QpInt p)).natDegree = B'.natDegree := by
        exact Polynomial.natDegree_map_eq_of_injective (RingEquiv.injective e.symm) B'
      _ = b.natDegree := hdegB
  · -- g = map back of g'
    have hback : (g'.map (e.symm : PadicInt p →+* QpInt p)) = g := by
      dsimp [g']
      rw [Polynomial.map_map]
      have hid : (e.symm : PadicInt p →+* QpInt p).comp (e : QpInt p →+* PadicInt p) =
          RingHom.id (QpInt p) := by
        apply RingHom.ext
        intro r
        change e.symm (e r) = r
        exact RingEquiv.symm_apply_apply e r
      rw [hid, Polynomial.map_id]
    calc
      g = g'.map (e.symm : PadicInt p →+* QpInt p) := hback.symm
      _ = (A' * B').map (e.symm : PadicInt p →+* QpInt p) := by rw [hEq]
      _ = (A'.map (e.symm : PadicInt p →+* QpInt p)) *
            (B'.map (e.symm : PadicInt p →+* QpInt p)) := by
            rw [Polynomial.map_mul]


/-! ## 3. The reduction of the minimal polynomial is irreducible over `𝔽_p` -/

/-- The minimal polynomial of ζ over the field `QpAdic p` is irreducible
(the field-level minimal polynomial of an integral element). -/
theorem teich_minpoly_irreducible_field (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    Irreducible (minpoly (QpAdic p) (((teich p P α : kpInt p P) : kpAdic p P))) := by
  exact minpoly.irreducible (teich_isIntegral_kpAdic (p := p) (P := P) (α := α) hα)

/-- The integer minimal polynomial `gR` is not `1` (a monic polynomial of
degree `0` annihilating ζ would have to be `1`, impossible). -/
theorem teichMinpolyInt_ne_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (_hα : α ≠ 0) :
    teichMinpolyInt p P α ≠ 1 := by
  classical
  intro h1
  have hneq := minpoly.ne_one (QpInt p)
    (((teich p P α : kpInt p P) : kpAdic p P))
  unfold teichMinpolyInt at h1
  exact hneq h1

/-- Monic factors of a squarefree monic polynomial over a field are coprime
(the gcd divides both factors, so its square divides the product, and
squarefreeness makes the gcd a unit). -/
lemma isCoprime_of_squarefree_of_mul_eq {F : Type*} [Field F] {p f g : F[X]}
    (_hmonf : f.Monic) (_hmong : g.Monic) (hsq : Squarefree p) (hfac : f * g = p) :
    IsCoprime f g := by
  classical
  let d := gcd f g
  have hdvd : d * d ∣ p := by
    have hdl : d ∣ f := gcd_dvd_left f g
    have hdr : d ∣ g := gcd_dvd_right f g
    have hdvd' : d * d ∣ f * g := by
      rcases hdl with ⟨f', hf'⟩
      rcases hdr with ⟨g', hg'⟩
      refine ⟨f' * g', ?_⟩
      calc
        f * g = (d * f') * (d * g') := by rw [hf', hg']
        _ = d * d * (f' * g') := by ring
    rwa [hfac] at hdvd'
  exact (gcd_isUnit_iff f g).mp (hsq d hdvd)

/-- The reduction `ḡ := (teichMinpolyInt).map (qpReductionHom p)` of the
minimal polynomial is **irreducible over `ZMod p`**: its reduction is
squarefree (it divides `X^q − 1`), and if it factored as `f · g` with `f`,
`g` monic of positive degree, Hensel (`hensel_lift_qpInt`) would lift the
factorization to the integer polynomial, contradicting irreducibility of the
field-level minimal polynomial. -/
theorem teichMinpolyInt_reduction_irreducible (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    Irreducible ((teichMinpolyInt p P α).map (qpReductionHom p)) := by
  classical
  let gR : (QpInt p)[X] := teichMinpolyInt p P α
  let gbar : (ZMod p)[X] := gR.map (qpReductionHom p)
  have hgRmon : gR.Monic := by dsimp [gR]; exact teichMinpolyInt_monic p P hα
  have hgbarmon : gbar.Monic := by dsimp [gbar]; exact Polynomial.Monic.map _ hgRmon
  have hsq : Squarefree gbar := by
    dsimp [gbar, gR]
    exact teichMinpolyInt_reduction_squarefree p P hα
  have hgirr : Irreducible (gR.map (algebraMap (QpInt p) (QpAdic p))) := by
    dsimp [gR]
    rw [← teich_minpoly_eq_field_map p P hα]
    exact teich_minpoly_irreducible_field p P hα
  have hgRne1 : gR ≠ 1 := by dsimp [gR]; exact teichMinpolyInt_ne_one p P hα
  have hgbarn1 : gbar ≠ 1 := by
    intro h1
    apply hgRne1
    have hd0 : gbar.natDegree = 0 := by rw [h1]; simp
    have hdR0 : gR.natDegree = 0 := by
      have hdeg0 : gbar.natDegree = gR.natDegree := by
        dsimp [gbar]
        exact hgRmon.natDegree_map (qpReductionHom p)
      rwa [hdeg0] at hd0
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdR0]
    have hlc : gR.coeff 0 = 1 := by
      have hc := hgRmon.leadingCoeff
      simpa [Polynomial.leadingCoeff, hdR0] using hc
    simp [hlc]
  rw [hgbarmon.irreducible_iff_natDegree]
  refine ⟨hgbarn1, ?_⟩
  intro f g hfmon hgmon hfac
  by_contra hdeg
  have hfdeg : 0 < f.natDegree := by
    have hz : f.natDegree ≠ 0 := fun h => hdeg (Or.inl h)
    exact Nat.pos_of_ne_zero hz
  have hgdeg : 0 < g.natDegree := by
    have hz : g.natDegree ≠ 0 := fun h => hdeg (Or.inr h)
    exact Nat.pos_of_ne_zero hz
  have hfgCop : IsCoprime f g := isCoprime_of_squarefree_of_mul_eq hfmon hgmon hsq hfac
  rcases (hensel_lift_qpInt (g := gR) hgRmon hfmon hgmon hfac.symm hfgCop)
    with ⟨A, B, hAmon, hBmon, hdegA, hdegB, hEq⟩
  have hfacF : gR.map (algebraMap (QpInt p) (QpAdic p)) =
      (A.map (algebraMap (QpInt p) (QpAdic p))) *
        (B.map (algebraMap (QpInt p) (QpAdic p))) := by
    rw [← Polynomial.map_mul, ← hEq]
  have huA : ¬ IsUnit (A.map (algebraMap (QpInt p) (QpAdic p))) := by
    intro hu
    have hdA : 0 < A.natDegree := by
      rw [hdegA]
      exact hfdeg
    have hdm : (A.map (algebraMap (QpInt p) (QpAdic p))).natDegree = A.natDegree :=
      hAmon.natDegree_map (algebraMap (QpInt p) (QpAdic p))
    have hd0 : (A.map (algebraMap (QpInt p) (QpAdic p))).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  have huB : ¬ IsUnit (B.map (algebraMap (QpInt p) (QpAdic p))) := by
    intro hu
    have hdB : 0 < B.natDegree := by
      rw [hdegB]
      exact hgdeg
    have hdm : (B.map (algebraMap (QpInt p) (QpAdic p))).natDegree = B.natDegree :=
      hBmon.natDegree_map (algebraMap (QpInt p) (QpAdic p))
    have hd0 : (B.map (algebraMap (QpInt p) (QpAdic p))).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  rcases (hgirr.isUnit_or_isUnit hfacF) with hAunit | hBunit
  · exact huA hAunit
  · exact huB hBunit


/-! ## 4. The residue root `α` and the degree bound -/

/-- **Reduction to `ZMod p`**: `qpReductionHom` (the reduction through the
standard `ℤ_[p]`) agrees with the canonical quotient map onto
`ZMod p ≅ QpInt p ⧸ mR`. -/
lemma qpReductionHom_eq_residue (p : ℕ) [Fact (Nat.Prime p)] (a : QpInt p) :
    qpReductionHom p a = qpResidueEquivZMod p
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (QpInt p)) a) := by
  unfold qpReductionHom qpResidueEquivZMod
  rw [PadicInt.toZMod_eq_residueField_comp_residue]
  rfl

/-- **Coefficient triangle**: the κ-reduction of a `QpInt` coefficient
(`qpReduction`, through `kpInt`) equals the reduction to `ZMod p` followed by
the prime-field embedding `ZMod p → κ`. -/
theorem qpReduction_eq_algebraMap_qpReductionHom (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (a : QpInt p) :
    qpReduction p P a = algebraMap (ZMod p) (kap p P) (qpReductionHom p a) := by
  have h1 := qpReduction_eq_algebraMap (p := p) (P := P) a
  calc
    qpReduction p P a = algebraMap (ZMod p) (kap p P)
        (qpResidueEquivZMod p (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (QpInt p)) a)) := h1
    _ = algebraMap (ZMod p) (kap p P) (qpReductionHom p a) :=
          congrArg (algebraMap (ZMod p) (kap p P)) (qpReductionHom_eq_residue p a).symm

/-- **ζ kills `gR` over the integers**: evaluating the integer minimal
polynomial at the Teichmüller lift ζ (as an element of the valuation ring
`kpInt`, coefficients pushed by the inclusion `QpInt → kpInt`) gives `0`. -/
theorem teichMinpolyInt_eval_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (_hα : α ≠ 0) :
    Polynomial.eval₂ (algebraMap (QpInt p) (kpInt p P)) (teich p P α)
        (teichMinpolyInt p P α) = 0 := by
  classical
  let gR : (QpInt p)[X] := teichMinpolyInt p P α
  let ζz : kpInt p P := teich p P α
  let x : kpAdic p P := (ζz : kpAdic p P)
  apply kpIntToKpAdic_injective p P
  change ((Polynomial.eval₂ (algebraMap (QpInt p) (kpInt p P)) ζz gR : kpInt p P) : kpAdic p P) = 0
  have hcomp : (algebraMap (kpInt p P) (kpAdic p P)).comp
        (algebraMap (QpInt p) (kpInt p P)) = algebraMap (QpInt p) (kpAdic p P) := by
    apply RingHom.ext
    intro r
    rfl
  calc
    ((Polynomial.eval₂ (algebraMap (QpInt p) (kpInt p P)) ζz gR : kpInt p P) : kpAdic p P)
        = Polynomial.eval₂ ((algebraMap (kpInt p P) (kpAdic p P)).comp
            (algebraMap (QpInt p) (kpInt p P))) x gR := by
          -- (algebraMap kpInt kpAdic) (eval₂ ψ ζz gR) with g ζz = x
          exact Polynomial.hom_eval₂ gR (algebraMap (QpInt p) (kpInt p P))
            (algebraMap (kpInt p P) (kpAdic p P)) ζz
    _ = Polynomial.eval₂ (algebraMap (QpInt p) (kpAdic p P)) x gR := by rw [hcomp]
    _ = 0 := by
          change Polynomial.eval₂ (algebraMap (QpInt p) (kpAdic p P))
            (((teich p P α : kpInt p P) : kpAdic p P)) (teichMinpolyInt p P α) = 0
          change Polynomial.aeval (((teich p P α : kpInt p P) : kpAdic p P))
            (teichMinpolyInt p P α) = 0
          exact minpoly.aeval (QpInt p) (((teich p P α : kpInt p P) : kpAdic p P))

/-- The reduction of ζ modulo the maximal ideal of `kpInt` is `α`. -/
lemma mk_teich (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (teich p P α) = α :=
  teich_mod_eq (p := p) (P := P) α

/-- **Reduction of the root**: reducing the equation `gR(ζ) = 0` modulo the
maximal ideal of `kpInt` shows the reduction `gR.map (qpReduction p P)` has
the root `α = mk ζ` in the residue field `κ`. -/
theorem teichMinpolyInt_reduction_root (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    Polynomial.eval α (Polynomial.map (qpReduction p P) (teichMinpolyInt p P α)) = 0 := by
  classical
  let gR : (QpInt p)[X] := teichMinpolyInt p P α
  let ζz : kpInt p P := teich p P α
  let mkS : kpInt p P →+* kap p P := Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
  have hzero := teichMinpolyInt_eval_zero p P hα
  have hvia : mkS (Polynomial.eval₂ (algebraMap (QpInt p) (kpInt p P)) ζz gR) =
      Polynomial.eval₂ (mkS.comp (algebraMap (QpInt p) (kpInt p P))) (mkS ζz) gR :=
    Polynomial.hom_eval₂ gR (algebraMap (QpInt p) (kpInt p P)) mkS ζz
  have hmkz : mkS ζz = α := mk_teich p P
  have hmk0 : Polynomial.eval₂ (mkS.comp (algebraMap (QpInt p) (kpInt p P))) α gR = 0 := by
    rw [← hmkz]
    rw [← hvia]
    exact congrArg mkS hzero
  -- mkS.comp (algebraMap QpInt kpInt) = qpReduction by rfl
  change Polynomial.eval₂ (qpReduction p P) α gR = 0 at hmk0
  -- eval₂ with the same coefficient ring map = eval of the mapped polynomial
  rwa [Polynomial.eval₂_eq_eval_map] at hmk0



/-! ## 5. THE UPPER BOUND: `deg (minpoly ζ) ≤ f` -/

/-- **Integrality of `α` over `𝔽_p`**: `α` is a root of the monic polynomial
`X^q − 1` (its order is `q := p^f − 1 = |κ^×|`, `hgen`). -/
theorem residue_isIntegral_zmod (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    IsIntegral (ZMod p) α := by
  classical
  let q := p ^ P.inertiaDeg ℤ - 1
  refine ⟨Polynomial.X ^ q - 1, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C (1 : ZMod p) (by
      have hpf := kap_pow_pf_ge_two p P
      dsimp [q]
      omega)
  · have hunit : (Units.mk0 α hα) ^ q = 1 := by
      dsimp [q]
      rw [← hgen]
      exact pow_orderOf_eq_one (Units.mk0 α hα)
    have hq0 : α ^ q = 1 := by
      exact congrArg (fun u : (kap p P)ˣ => (u : kap p P)) hunit
    rw [Polynomial.eval₂_eq_eval_map]
    -- (X^q - 1).map alg = X^q - 1 in kap; eval at α = α^q - 1 = 0
    simp [hq0]

/-- The κ-reduction map of `QpInt`-coefficients equals the `ZMod p`-reduction
followed by the prime-field embedding (polynomial version of the coefficient
triangle `qpReduction_eq_algebraMap_qpReductionHom`). -/
theorem map_qpReduction_eq_map (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (g : (QpInt p)[X]) :
    g.map (qpReduction p P) =
      (g.map (qpReductionHom p)).map (algebraMap (ZMod p) (kap p P)) := by
  rw [Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro a
  exact qpReduction_eq_algebraMap_qpReductionHom p P a

/-- **`ḡ` vanishes at `α`**: the `ZMod p`-reduction of the minimal
polynomial has the residue generator `α` as a root (the reduction of the
integer-level root `gR(ζ) = 0`). -/
theorem teichMinpolyInt_reduction_root_zmod (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    ((teichMinpolyInt p P α).map (qpReductionHom p)).eval₂
      (algebraMap (ZMod p) (kap p P)) α = 0 := by
  classical
  have hroot : Polynomial.eval α (Polynomial.map (qpReduction p P) (teichMinpolyInt p P α)) = 0 :=
    teichMinpolyInt_reduction_root p P hα
  have hmap : (teichMinpolyInt p P α).map (qpReduction p P) =
      ((teichMinpolyInt p P α).map (qpReductionHom p)).map
        (algebraMap (ZMod p) (kap p P)) :=
    map_qpReduction_eq_map p P (teichMinpolyInt p P α)
  have hroot1 : Polynomial.eval α (((teichMinpolyInt p P α).map (qpReductionHom p)).map
      (algebraMap (ZMod p) (kap p P))) = 0 := by
    rwa [hmap] at hroot
  have hroot2 : ((teichMinpolyInt p P α).map (qpReductionHom p)).eval₂
      (algebraMap (ZMod p) (kap p P)) α = 0 := by
    rwa [← Polynomial.eval₂_eq_eval_map] at hroot1
  exact hroot2

/-- The `ZMod p`-minimal polynomial of `α` divides the reduction `ḡ`
(α is a root of `ḡ`). -/
theorem minpoly_dvd_reduction (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (_hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    minpoly (ZMod p) α ∣ (teichMinpolyInt p P α).map (qpReductionHom p) := by
  classical
  have hroot2 := teichMinpolyInt_reduction_root_zmod p P hα
  have hroot : Polynomial.aeval α ((teichMinpolyInt p P α).map (qpReductionHom p)) = 0 := by
    change ((teichMinpolyInt p P α).map (qpReductionHom p)).eval₂
      (algebraMap (ZMod p) (kap p P)) α = 0
    exact hroot2
  exact minpoly.dvd (ZMod p) α hroot

/-- **THE UPPER BOUND**: for `α ≠ 0` with `α` a generator of `κ^×`, the
Teichmüller lift `ζ := teich p P α` has minimal polynomial over `QpAdic p`
of degree at most `f := P.inertiaDeg ℤ`.  (With the lower bound
`teich_powers_independent_qpAdic` — `f ≤ deg` — this gives
`deg = f`, the cyclotomic-degree bridge of the G3 chapter.) -/
theorem teich_minpoly_natDegree_le_inertiaDeg (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    (minpoly (QpAdic p) (((teich p P α : kpInt p P) : kpAdic p P))).natDegree ≤
      P.inertiaDeg ℤ := by
  classical
  let x : kpAdic p P := (((teich p P α : kpInt p P) : kpAdic p P))
  let gR : (QpInt p)[X] := teichMinpolyInt p P α
  let gbar : (ZMod p)[X] := gR.map (qpReductionHom p)
  let m : (ZMod p)[X] := minpoly (ZMod p) α
  change (minpoly (QpAdic p) x).natDegree ≤ P.inertiaDeg ℤ
  -- field minpoly = gR.map (QpInt → QpAdic); degree of gR
  have hdegx : (minpoly (QpAdic p) x).natDegree = gR.natDegree := by
    calc
      (minpoly (QpAdic p) x).natDegree = (gR.map (algebraMap (QpInt p) (QpAdic p))).natDegree := by
        rw [show minpoly (QpAdic p) x = gR.map (algebraMap (QpInt p) (QpAdic p)) by
          dsimp [x, gR]
          exact teich_minpoly_eq_field_map p P hα]
      _ = gR.natDegree := by
        dsimp [gR]
        exact (teichMinpolyInt_monic p P hα).natDegree_map (algebraMap (QpInt p) (QpAdic p))
  have hdegbar : gbar.natDegree = gR.natDegree := by
    dsimp [gbar]
    exact Polynomial.Monic.natDegree_map (teichMinpolyInt_monic p P hα) (qpReductionHom p)
  -- gbar monic irreducible; m monic; m | gbar
  have hgbarmon : gbar.Monic := by
    dsimp [gbar]
    exact Polynomial.Monic.map _ (teichMinpolyInt_monic p P hα)
  have hgbirr : Irreducible gbar := by
    dsimp [gbar]
    exact teichMinpolyInt_reduction_irreducible p P hα
  have hInt := residue_isIntegral_zmod p P hα hgen
  have hmm : m.Monic := by
    dsimp [m]
    exact minpoly.monic hInt
  have hmdvd : m ∣ gbar := by
    dsimp [m, gbar]
    exact minpoly_dvd_reduction p P hα hgen
  rcases hmdvd with ⟨q, hq⟩  -- gbar = m * q
  have hmne1 : m ≠ 1 := by
    dsimp [m]
    exact minpoly.ne_one (ZMod p) α
  have hmnunit : ¬ IsUnit m := by
    intro hu
    have hd0 : m.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hdgt : 1 ≤ m.natDegree := by
      by_contra hlt
      have hd0' : m.natDegree = 0 := by omega
      have hmm1 : m = 1 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hd0']
        have hlc : m.coeff 0 = 1 := by
          have hc := hmm.leadingCoeff
          simpa [Polynomial.leadingCoeff, hd0'] using hc
        simp [hlc]
      exact hmne1 hmm1
    omega
  have hqunit : IsUnit q :=
    (hgbirr.isUnit_or_isUnit hq).resolve_left hmnunit
  have hqne0 : q ≠ 0 := by
    intro hqz
    apply hgbarmon.ne_zero
    calc
      gbar = m * q := hq
      _ = 0 := by rw [hqz]; simp
  have hqd0 : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hqunit
  have hdecomp : gbar.natDegree = m.natDegree := by
    have hmm0 : m ≠ 0 := hmm.ne_zero
    calc
      gbar.natDegree = (m * q).natDegree := by rw [hq]
      _ = m.natDegree + q.natDegree := Polynomial.natDegree_mul hmm0 hqne0
      _ = m.natDegree := by rw [hqd0]; omega
  have hmle : m.natDegree ≤ P.inertiaDeg ℤ := by
    calc
      m.natDegree ≤ Module.finrank (ZMod p) (kap p P) := by
        dsimp [m]
        exact minpoly.natDegree_le α
      _ = P.inertiaDeg ℤ := kap_finrank (p := p) (P := P)
  calc
    (minpoly (QpAdic p) x).natDegree = gbar.natDegree := by
      rw [hdegx]
      exact hdegbar.symm
    _ = m.natDegree := hdecomp
    _ ≤ P.inertiaDeg ℤ := hmle


/-- **THE cyclotomic-degree bridge**: for `α ≠ 0` a generator of `κ^×`
(`hgen`), the Teichmüller lift `ζ := teich p P α` has minimal polynomial
over `QpAdic p` of degree EXACTLY `f := P.inertiaDeg ℤ` — the upper bound
`teich_minpoly_natDegree_le_inertiaDeg` plus the lower bound from the
`f`-element linear independence `teich_powers_independent_qpAdic` (via the
`W = ℚ_p(ζ)`-adjoin degree `adjoin_finrank_eq_minpoly_natDegree`).  This is
statement (B) of the Session-86 roadmap, giving `[ℚ_p(ζ):ℚ_p] = f` — the
residue-degree half of the fundamental identity for the unramified subfield
`W/ℚ_p`. -/
theorem teich_minpoly_natDegree_eq_inertiaDeg (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    (minpoly (QpAdic p) (((teich p P α : kpInt p P) : kpAdic p P))).natDegree =
      P.inertiaDeg ℤ := by
  classical
  let x : kpAdic p P := (((teich p P α : kpInt p P) : kpAdic p P))
  change (minpoly (QpAdic p) x).natDegree = P.inertiaDeg ℤ
  have hle' : (minpoly (QpAdic p) x).natDegree ≤ P.inertiaDeg ℤ := by
    simpa [x] using (teich_minpoly_natDegree_le_inertiaDeg p P hα hgen)
  have hW : Module.finrank (QpAdic p) (Wk p P α) = (minpoly (QpAdic p) x).natDegree := by
    dsimp [x]
    exact adjoin_finrank_eq_minpoly_natDegree p P hα
  have hmem : x ∈ (Wk p P α : Set (kpAdic p P)) := by
    dsimp [x]
    exact IntermediateField.mem_adjoin_simple_self (QpAdic p)
      ((teich p P α : kpInt p P) : kpAdic p P)
  let w : Fin (P.inertiaDeg ℤ) → Wk p P α := fun i => ⟨x ^ (i : ℕ), (Wk p P α).pow_mem hmem (i : ℕ)⟩
  have hwind : LinearIndependent (QpAdic p) w := by
    let φ : Wk p P α →ₗ[QpAdic p] kpAdic p P := {
      toFun := fun z => (z : kpAdic p P)
      map_add' := by intro a b; rfl
      map_smul' := by intro s a; rfl }
    apply LinearIndependent.of_comp φ
    convert teich_powers_independent_qpAdic (p := p) (P := P) (α := α) hα hgen using 1
    ext i
    rfl
  haveI : Module.Finite (QpAdic p) (Wk p P α) :=
    IntermediateField.adjoin.finiteDimensional
      (teich_isIntegral_kpAdic (p := p) (P := P) (α := α) hα)
  have hcard : Fintype.card (Fin (P.inertiaDeg ℤ)) ≤ Module.finrank (QpAdic p) (Wk p P α) :=
    LinearIndependent.fintype_card_le_finrank hwind
  have hf : P.inertiaDeg ℤ ≤ (minpoly (QpAdic p) x).natDegree := by
    calc
      P.inertiaDeg ℤ = Fintype.card (Fin (P.inertiaDeg ℤ)) := by simp
      _ ≤ Module.finrank (QpAdic p) (Wk p P α) := hcard
      _ = (minpoly (QpAdic p) x).natDegree := hW
  exact le_antisymm hle' hf


end
end Submission.Vdw.LocalField
