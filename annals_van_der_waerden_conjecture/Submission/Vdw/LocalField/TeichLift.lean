import Mathlib
import Submission.Vdw.LocalField.RamificationCompat
import Submission.Vdw.LocalField.RankIdentity
import Submission.Vdw.LocalField.QpIntFinite
import Submission.Vdw.LocalField.ResidueGenerator

open Classical
open scoped NumberField WithZero
open Module

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (G3 lift): the DVR descent and the mod-`𝔪` engine

The two algebraic layers of the G3 lower bound (the `[W : ℚ_p] = f` degree
argument) that do not need the completion's field structure:

**Part 1 — the DVR descent (uniformizer `p`).**  The mod-`𝔪` reduction
shows that any `QpInt`-linear relation among the Teichmüller powers forces
its coefficients into the maximal ideal of `QpInt p`; part 1 supplies the
pure algebra turning such a "mod-`𝔪` triviality" into a genuine triviality
over the complete DVR `QpInt p`:

* `qpInt_p_ne_zero` — the uniformizer `p` is nonzero in `QpInt p`
  (transported from `ℤ_[p]` along `qpPadicIntEquiv`, where `CharZero` holds);
* `qpInt_divisible_all_pow_eq_zero` — **separation**: an element of
  `QpInt p` divisible by `p^k` for every `k` is zero (the `𝔪`-adic
  Hausdorff property of the local ring `QpInt p`, via
  `IsHausdorff.of_isTorsionFree`);
* `kpInt_smul_p_pow_injective` — scalar multiplication by `p^k` is injective
  on `kpInt p P` (torsion-freeness of `kpInt` over the domain `QpInt`);
* **`coeff_descent`** — given a family `v : ι → kpInt p P` with the mod-`𝔪`
  property `hmod` (every relation forces its coefficients into the maximal
  ideal), every actual relation `∑ u i • v i = 0` has `u = 0` (divide the
  relation by successive powers of `p`, re-apply `hmod`, and use separation).

**Part 2 — the mod-`𝔪` engine.**  The reduction machinery that produces
`hmod` for the Teichmüller-powers family from the residue-side independence
`kap_generator_powers_linearIndependent` (ResidueGenerator): `qpReduction`
(mk mS ∘ algebraMap), its quotient lift through `QpInt ⧸ mR`, the residue
identification `QpInt ⧸ mR ≃+* ZMod p`, the scalar compatibility
(`RingHom.ext_zmod`), the engine
`teich_qpInt_sum_zero_coeff_mem_maximal`, and the combination with
`coeff_descent` — **`teich_powers_independent_qpInt`**:
`{1, ζ, …, ζ^(f−1)}` is `QpInt`-independent in `kpInt p P` (the first half
of the G3 lower bound; the QpAdic-field step comes next).

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The uniformizer `p` is nonzero in `QpInt p` (transport of the
characteristic-zero fact from `ℤ_[p]` along `qpPadicIntEquiv`). -/
lemma qpInt_p_ne_zero (p : ℕ) [Fact (Nat.Prime p)] : (p : QpInt p) ≠ 0 := by
  intro hz
  have hmap := congrArg (qpPadicIntEquiv p) hz
  have hcast : qpPadicIntEquiv p ((p : ℕ) : QpInt p) = (p : PadicInt p) := by
    simp [qpPadicIntEquiv]
  rw [hcast, map_zero] at hmap
  have hpne : (p : PadicInt p) ≠ 0 := by
    exact_mod_cast (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
  exact hpne hmap

/-- **Separation**: an element of `QpInt p` divisible by `p^k` for every
`k` is zero (the `QpInt p` is Hausdorff for the adic topology of its maximal
ideal; the divisibility `x = p^k · s` gives `x ∈ (𝔪^k • ⊤)` for every `k`). -/
lemma qpInt_divisible_all_pow_eq_zero (p : ℕ) [Fact (Nat.Prime p)] (x : QpInt p)
    (hx : ∀ k : ℕ, ∃ s : QpInt p, x = (p : QpInt p) ^ k * s) : x = 0 := by
  classical
  let R := QpInt p
  let mR : Ideal R := IsLocalRing.maximalIdeal R
  have hpπ : mR = Ideal.span ({(p : R)} : Set R) := by
    dsimp [R, mR]
    exact qpIntMaximalIdeal_eq_span_p p
  have hsep : IsHausdorff mR R := by
    refine IsHausdorff.of_isTorsionFree mR R ?_
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  exact hsep.haus x (fun n : ℕ => by
    rw [SModEq.zero]
    rcases hx n with ⟨s, hs⟩
    have hp_mem : (p : R) ∈ mR := by
      rw [hpπ]
      exact Ideal.mem_span_singleton_self (p : R)
    have hpn_mem : (p : R) ^ n ∈ (mR ^ n : Ideal R) := Ideal.pow_mem_pow hp_mem n
    have hsmul : (p : R) ^ n • s ∈ (mR ^ n • (⊤ : Submodule R R)) :=
      Submodule.smul_mem_smul hpn_mem (Submodule.mem_top)
    have h1 : x = (p : R) ^ n • s := by
      rw [hs]
      simp
    simpa [h1] using hsmul)

/-- Scalar multiplication by `p^k` is injective on `kpInt p P`
(torsion-freeness of `kpInt` over the domain `QpInt p`). -/
lemma kpInt_smul_p_pow_injective (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (k : ℕ) {x : kpInt p P}
    (hx : (p : QpInt p) ^ k • x = 0) : x = 0 := by
  classical
  haveI : Module.IsTorsionFree (QpInt p) (kpInt p P) := kpInt_torsionFree p P
  exact (smul_eq_zero_iff_right (R := QpInt p) (M := kpInt p P)
    (pow_ne_zero k (qpInt_p_ne_zero p))).mp hx

/-- **DVR descent with uniformizer `p`**: if a mod-`𝔪` property `hmod`
forces every relation to have its coefficients in the maximal ideal, then
every actual relation `∑ u i • v i = 0` is trivial (`u = 0`).  The proof
divides the relation by successive powers of `p` (`kpInt_smul_p_pow_injective`
removes the `p^k` factor), applies `hmod` at each level, and finishes with
the separation `qpInt_divisible_all_pow_eq_zero`. -/
theorem coeff_descent (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {ι : Type*} [Fintype ι] {v : ι → kpInt p P}
    (hmod : ∀ u : ι → QpInt p,
      (∑ i, u i • v i) = 0 → ∀ i, u i ∈ IsLocalRing.maximalIdeal (QpInt p))
    (u : ι → QpInt p) (hu : (∑ i, u i • v i) = 0) : u = 0 := by
  classical
  funext i
  -- every coefficient is divisible by every power of p
  have hdiv : ∀ k : ℕ, ∀ i : ι, ∃ w : QpInt p, u i = (p : QpInt p) ^ k * w := by
    intro k
    induction k with
    | zero =>
        intro i
        refine ⟨u i, ?_⟩
        simp
    | succ k ih =>
        choose w hw using ih
        have hsum0 : (∑ i, w i • v i) = 0 := by
          apply kpInt_smul_p_pow_injective (p := p) (P := P) k
          calc
            (p : QpInt p) ^ k • (∑ i, w i • v i)
                = ∑ i, (p : QpInt p) ^ k • (w i • v i) := by
                  rw [Finset.smul_sum]
            _ = ∑ i, ((p : QpInt p) ^ k * w i) • v i := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [← smul_smul]
            _ = ∑ i, u i • v i := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [← hw i]
            _ = 0 := hu
        have hmem : ∀ i : ι, w i ∈ IsLocalRing.maximalIdeal (QpInt p) := hmod w hsum0
        intro i
        rcases (Ideal.mem_span_singleton.mp (by
          rw [← qpIntMaximalIdeal_eq_span_p p]
          exact hmem i) : (p : QpInt p) ∣ w i) with ⟨w', hwi⟩
        refine ⟨w', ?_⟩
        calc
          u i = (p : QpInt p) ^ k * w i := hw i
          _ = (p : QpInt p) ^ k * ((p : QpInt p) * w') := by rw [hwi]
          _ = (p : QpInt p) ^ (k + 1) * w' := by
                rw [pow_succ]
                ring
  exact qpInt_divisible_all_pow_eq_zero p (u i) (fun k => hdiv k i)


/-! ### The mod-`𝔪` engine (the `hmod` hypothesis for `coeff_descent`)

The reduction machinery that turns the residue-side independence
(`kap_generator_powers_linearIndependent`, ResidueGenerator) into the
mod-`𝔪` property `hmod` consumed by `coeff_descent`:

* `qpReduction` — `ρ := mk mS ∘ algebraMap (QpInt p) (kpInt p P)`: the
  κ-side reduction of a `QpInt` coefficient (an element of `kap p P`);
* `qpReduction_eq_zero_iff` — `ρ a = 0 ↔ a ∈ mR` (the image of `mR` under
  the algebra map is contained in `mS`, `mS_liesOver_mR`);
* `qpReduction_lift` — the induced ring hom `QpInt p ⧸ mR →+* kap p P`;
* `qpResidueEquivZMod` — the residue identification
  `QpInt p ⧸ mR ≃+* ZMod p` (via `ResidueField.mapEquiv (qpPadicIntEquiv p)`
  and `PadicInt.residueField`);
* `qpReduction_lift_eq_algebraMap` — the scalar compatibility: the lifted
  reduction equals `algebraMap (ZMod p) (kap p P) ∘ θ` (any two ring homs
  from `ZMod p` agree, `RingHom.ext_zmod`);
* `qpReduction_eq_algebraMap` — the element-level form `ρ a =
  algebraMap (ZMod p) (kap p P) (θ (mk mR a))`;
* **`teich_qpInt_sum_zero_coeff_mem_maximal`** — THE ENGINE: for the
  Teichmüller-powers family `v i = ζ^i` (`ζ = teich p P α`, `α` a generator
  of `κ^×`), every `QpInt`-relation `∑ u i • ζ^i = 0` forces every
  coefficient into `mR` — reduce modulo `mS` (each term becomes
  `ρ (u i) · α^i`), identify the coefficients with `ZMod p` via the scalar
  compatibility, and apply `kap_generator_powers_linearIndependent`;
* **`teich_powers_independent_qpInt`** — the combination: engine +
  `coeff_descent` give the `QpInt`-independence of `{1, ζ, …, ζ^(f−1)}` in
  `kpInt p P` (the first half of the G3 lower bound; the QpAdic-field step
  comes next).

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

/-- κ-side reduction of a `QpInt` coefficient: `ρ a := mk mS (algebraMap a)`,
an element of the residue field `kap p P`. -/
noncomputable def qpReduction (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    QpInt p →+* kap p P :=
  (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))).comp
    (algebraMap (QpInt p) (kpInt p P))

/-- The reduction vanishes exactly on the maximal ideal of `QpInt p`:
`ρ a = 0 ↔ a ∈ mR` (the algebra map sends `mR` into `mS`). -/
lemma qpReduction_eq_zero_iff (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (a : QpInt p) :
    qpReduction p P a = 0 ↔ a ∈ IsLocalRing.maximalIdeal (QpInt p) := by
  haveI : (IsLocalRing.maximalIdeal (kpInt p P)).LiesOver
      (IsLocalRing.maximalIdeal (QpInt p)) := mS_liesOver_mR p P
  unfold qpReduction
  calc
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
        (algebraMap (QpInt p) (kpInt p P) a)) = 0
        ↔ algebraMap (QpInt p) (kpInt p P) a ∈ IsLocalRing.maximalIdeal (kpInt p P) :=
          Ideal.Quotient.eq_zero_iff_mem
    _ ↔ a ∈ IsLocalRing.maximalIdeal (QpInt p) :=
          (Ideal.mem_of_liesOver (IsLocalRing.maximalIdeal (kpInt p P))
            (IsLocalRing.maximalIdeal (QpInt p)) a).symm

/-- The lifted reduction: a ring hom from the residue `QpInt p ⧸ mR` into
`kap p P` (well-defined since `ρ` vanishes on `mR`). -/
noncomputable def qpReduction_lift (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (QpInt p ⧸ IsLocalRing.maximalIdeal (QpInt p)) →+* kap p P :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal (QpInt p)) (qpReduction p P)
    (fun a ha => (qpReduction_eq_zero_iff p P a).mpr ha)

/-- The residue identification `QpInt p ⧸ mR ≃+* ZMod p`: the residue field
of `QpInt p` is `𝔽_p`. -/
noncomputable def qpResidueEquivZMod (p : ℕ) [Fact (Nat.Prime p)] :
    (QpInt p ⧸ IsLocalRing.maximalIdeal (QpInt p)) ≃+* ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv (qpPadicIntEquiv p)).trans
    (PadicInt.residueField (p := p))

/-- The scalar compatibility at the quotient level: the lifted reduction is
`algebraMap (ZMod p) (kap p P) ∘ θ` (ring homs from `ZMod p` are unique). -/
lemma qpReduction_lift_eq_algebraMap (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (x : QpInt p ⧸ IsLocalRing.maximalIdeal (QpInt p)) :
    qpReduction_lift p P x =
      algebraMap (ZMod p) (kap p P) (qpResidueEquivZMod p x) := by
  classical
  let ψ : (QpInt p ⧸ IsLocalRing.maximalIdeal (QpInt p)) →+* kap p P :=
    qpReduction_lift p P
  let θ : (QpInt p ⧸ IsLocalRing.maximalIdeal (QpInt p)) ≃+* ZMod p :=
    qpResidueEquivZMod p
  have hψ' : ψ.comp θ.symm = algebraMap (ZMod p) (kap p P) := RingHom.ext_zmod _ _
  calc
    ψ x = (ψ.comp θ.symm) (θ x) := by
      simp [θ, ψ]
    _ = algebraMap (ZMod p) (kap p P) (θ x) := by rw [hψ']

/-- The element-level scalar compatibility:
`ρ a = algebraMap (ZMod p) (kap p P) (θ (mk mR a))`. -/
lemma qpReduction_eq_algebraMap (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (a : QpInt p) :
    qpReduction p P a =
      algebraMap (ZMod p) (kap p P)
        (qpResidueEquivZMod p (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (QpInt p)) a)) := by
  classical
  calc
    qpReduction p P a
        = qpReduction_lift p P (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal (QpInt p)) a) := by
          unfold qpReduction qpReduction_lift
          rfl
    _ = algebraMap (ZMod p) (kap p P)
          (qpResidueEquivZMod p (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal (QpInt p)) a)) := by
          exact qpReduction_lift_eq_algebraMap p P _

/-- **THE mod-`𝔪` engine**: for the Teichmüller-powers family
`v i = ζ^i` (`ζ = teich p P α`, `α` a generator of `κ^×`), every
`QpInt`-relation `∑ u i • ζ^i = 0` in `kpInt p P` forces every coefficient
into the maximal ideal of `QpInt p`.  Proof: reduce modulo `mS` (each term
becomes `ρ (u i) · α^i`), identify the coefficients with `ZMod p` via the
scalar compatibility, and apply `kap_generator_powers_linearIndependent`. -/
theorem teich_qpInt_sum_zero_coeff_mem_maximal (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (u : Fin (P.inertiaDeg ℤ) → QpInt p)
    (hu : (∑ i, u i • (teich p P α : kpInt p P) ^ (i : ℕ)) = 0) :
    ∀ i, u i ∈ IsLocalRing.maximalIdeal (QpInt p) := by
  classical
  have hmk : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)))
      (∑ i, u i • (teich p P α : kpInt p P) ^ (i : ℕ)) = 0 := by
    rw [hu]
    simp
  have hstep : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)))
        (∑ i, u i • (teich p P α : kpInt p P) ^ (i : ℕ))
        = ∑ i : Fin (P.inertiaDeg ℤ), qpReduction p P (u i) * α ^ (i : ℕ) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
          (u i • (teich p P α : kpInt p P) ^ (i : ℕ))
          = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
              (algebraMap (QpInt p) (kpInt p P) (u i) *
                (teich p P α : kpInt p P) ^ (i : ℕ)) := by
            rw [Algebra.smul_def]
      _ = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
              (algebraMap (QpInt p) (kpInt p P) (u i)) *
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
              ((teich p P α : kpInt p P) ^ (i : ℕ)) := by
            rw [map_mul]
      _ = qpReduction p P (u i) * α ^ (i : ℕ) := by
            have hmkζ : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
                ((teich p P α : kpInt p P) ^ (i : ℕ)) = α ^ (i : ℕ) := by
              rw [map_pow]
              exact congrArg (fun t : kap p P => t ^ (i : ℕ))
                (teich_mod_eq (p := p) (P := P) α)
            rw [hmkζ]
            rfl
  have hred : (∑ i : Fin (P.inertiaDeg ℤ), qpReduction p P (u i) * α ^ (i : ℕ)) = 0 := by
    exact hstep.symm.trans hmk
  let θ : (QpInt p ⧸ IsLocalRing.maximalIdeal (QpInt p)) ≃+* ZMod p :=
    qpResidueEquivZMod p
  have hcoef : ∀ i : Fin (P.inertiaDeg ℤ),
      qpReduction p P (u i) * α ^ (i : ℕ)
        = θ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (QpInt p)) (u i)) • α ^ (i : ℕ) := by
    intro i
    rw [qpReduction_eq_algebraMap]
    rw [← Algebra.smul_def]
  have hred2 : (∑ i : Fin (P.inertiaDeg ℤ),
      θ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (QpInt p)) (u i)) • α ^ (i : ℕ)) = 0 := by
    calc
      (∑ i, θ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (QpInt p)) (u i)) • α ^ (i : ℕ))
          = ∑ i, qpReduction p P (u i) * α ^ (i : ℕ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (hcoef i).symm
      _ = 0 := hred
  have hli := kap_generator_powers_linearIndependent (p := p) (P := P) (α := α) hα hgen
  have hall : ∀ g : Fin (P.inertiaDeg ℤ) → ZMod p,
      (∑ i, g i • α ^ (i : ℕ)) = 0 → ∀ i, g i = 0 :=
    (Fintype.linearIndependent_iff (R := ZMod p)
      (v := fun i : Fin (P.inertiaDeg ℤ) => α ^ (i : ℕ))).mp hli
  intro i
  have hgi : θ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (QpInt p)) (u i)) = 0 :=
    hall (fun i => θ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (QpInt p)) (u i)))
      (by simpa [θ] using hred2) i
  have hmi : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (QpInt p)) (u i) = 0 := by
    have hh := congrArg (fun z : ZMod p => θ.symm z) hgi
    simpa using hh
  exact (Ideal.Quotient.eq_zero_iff_mem (I := IsLocalRing.maximalIdeal (QpInt p))).mp hmi

/-- **QpInt-independence of the Teichmüller powers**: the engine supplies the
mod-`𝔪` property, `coeff_descent` turns it into triviality of every
relation — `{1, ζ, …, ζ^(f−1)}` is linearly independent over `QpInt p` in
`kpInt p P`. -/
theorem teich_powers_independent_qpInt (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    LinearIndependent (QpInt p)
      (fun i : Fin (P.inertiaDeg ℤ) => (teich p P α : kpInt p P) ^ (i : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro u hu i
  exact congrFun (coeff_descent (p := p) (P := P)
    (ι := Fin (P.inertiaDeg ℤ))
    (v := fun i : Fin (P.inertiaDeg ℤ) => (teich p P α : kpInt p P) ^ (i : ℕ))
    (teich_qpInt_sum_zero_coeff_mem_maximal (p := p) (P := P) (α := α) hα hgen)
    u hu) i


/-! ### The QpAdic-field step (part 1): NumDen denominator clearing

The bridge from `QpInt p`-independence to full `QpAdic p`-independence
(`teich_powers_independent_qpAdic`) clears the field coefficients by a common
denominator.  The purely generic piece, stated standalone over any domain `R`
with field of fractions `F` (only used concretely at `R := QpInt p`,
`F := QpAdic p`):

* `exists_common_denominator` — for a finite family `c : ι → F` there is a
  nonzero `D : R` and `u : ι → R` with `algebraMap R F D * c i =
  algebraMap R F (u i)` for every `i` (take `D := ∏ (den c i)` and
  `u i := (num c i) · ∏_{j ≠ i} (den c j)`, via `IsFractionRing.num/den`
  + `mk'_num_den` + `mk'_spec'`);
* `common_denominator_units_iff` — with the above data, `u i ≠ 0` iff
  `num (c i) ≠ 0` (the extra denominator factors are nonzero in the domain),
  and `c i = 0` iff `num (c i) = 0` (from `mk'_num_den`).

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

/-! #### Generic NumDen clearing (no local-field content) -/

section NumDenClearing

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- Every finite family in the fraction field `F` of a UFD `R` can be cleared
by a single nonzero denominator: `D := ∏_i (den c i) ≠ 0` and each
`D · c i` is an `R`-multiple. -/
theorem exists_common_denominator {ι : Type*} [Fintype ι] (c : ι → F) :
    ∃ (D : R) (_hD : D ≠ 0) (u : ι → R),
      ∀ i, (algebraMap R F D) * c i = algebraMap R F (u i) := by
  classical
  let den : ι → ↥(nonZeroDivisors R) := fun i => IsFractionRing.den R (c i)
  refine ⟨∏ i, (den i : R), ?_, fun i =>
      IsFractionRing.num R (c i) * ∏ j ∈ Finset.univ.erase i, (den j : R), ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro i hi
    exact mem_nonZeroDivisors_iff_ne_zero.mp (den i).2
  · intro i
    have hc : c i = IsLocalization.mk' F (IsFractionRing.num R (c i)) (den i) :=
      (IsFractionRing.mk'_num_den (A := R) (c i)).symm
    have hspec := IsLocalization.mk'_spec' F (IsFractionRing.num R (c i)) (den i)
    have hden_mul : (algebraMap R F (den i : R)) * c i =
        algebraMap R F (IsFractionRing.num R (c i)) := by
      rw [← hc] at hspec
      exact hspec
    have hsplit : (∏ j, (den j : R)) = (den i : R) *
        ∏ j ∈ Finset.univ.erase i, (den j : R) := by
      exact (Finset.mul_prod_erase Finset.univ (by simp)
        (f := fun j : ι => (den j : R))).symm
    calc
      (algebraMap R F (∏ j, (den j : R))) * c i
          = (algebraMap R F ((den i : R) *
              ∏ j ∈ Finset.univ.erase i, (den j : R))) * c i := by rw [hsplit]
      _ = (algebraMap R F (den i : R)) *
            (algebraMap R F (∏ j ∈ Finset.univ.erase i, (den j : R))) * c i := by
            rw [map_mul]
      _ = (algebraMap R F (∏ j ∈ Finset.univ.erase i, (den j : R))) *
            ((algebraMap R F (den i : R)) * c i) := by ring
      _ = (algebraMap R F (∏ j ∈ Finset.univ.erase i, (den j : R))) *
            (algebraMap R F (IsFractionRing.num R (c i))) := by
            exact congrArg (fun t : F =>
              algebraMap R F (∏ j ∈ Finset.univ.erase i, (den j : R)) * t) hden_mul
      _ = algebraMap R F ((∏ j ∈ Finset.univ.erase i, (den j : R)) *
            IsFractionRing.num R (c i)) := by rw [map_mul]
      _ = algebraMap R F (IsFractionRing.num R (c i) *
            ∏ j ∈ Finset.univ.erase i, (den j : R)) := by rw [mul_comm]

/-- A cleared coefficient is zero iff the numerator is zero (the reduced
fraction property `IsFractionRing.num_eq_zero`). -/
theorem common_denominator_num_eq_zero_iff {ι : Type*} [Fintype ι] (c : ι → F)
    (i : ι) : IsFractionRing.num R (c i) = 0 ↔ c i = 0 :=
  IsFractionRing.num_eq_zero (A := R) (c i)

end NumDenClearing

/-! ### The QpAdic-field step (part 2): field independence of the powers

The concrete instantiation of the clearing at `R := QpInt p`, `F := QpAdic p`
with the module `kpAdic p P` (containing `kpInt p P`):

* `kpInt_coe_smul` — the coercion `kpInt p P → kpAdic p P` is `QpInt`-linear
  (KEY: `algebraMap (kpInt) (kpAdic) (algebraMap (QpInt) (kpInt) x) =
  algebraMap (QpInt) (kpAdic) x` holds by **rfl** for these instances);
* `kpIntToKpAdic` — the coercion as a `QpInt`-linear map, injective (its
  kernel is `⊥`, `LinearMap.ker_eq_bot`);
* `teich_powers_independent_qpInt_emb` — the embedded
  `QpInt`-independence in `kpAdic` (`LinearIndependent.map'`);
* **`teich_powers_independent_qpAdic`** — THE field statement: the
  Teichmüller powers `{1, ζ, …, ζ^(f−1)}` are linearly independent over the
  field `QpAdic p` in `kpAdic p P`.  Proof: clear denominators of a
  `QpAdic`-relation (`exists_common_denominator`), multiply the relation by
  the common denominator (a field scalar, so no torsion issue), land in the
  `kpInt`-submodule via `kpInt_coe_smul`, use the embedded
  `QpInt`-independence, and recover `c = 0` from the cleared numerators
  (`num_eq_zero`).

This closes the G3 lower bound: `[W : ℚ_p] ≥ f` (a `QpAdic`-vector-space
family of size `f` that is linearly independent has `W ⊇ span` of dimension
`f`).  Axioms of every statement: propext / Classical.choice / Quot.sound
only.
-/

/-- The coercion `kpInt p P → kpAdic p P` is `QpInt`-linear (the tower
equality `algebraMap kpInt kpAdic (algebraMap QpInt kpInt x) =
algebraMap QpInt kpAdic x` is rfl for these instances). -/
lemma kpInt_coe_smul (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (u : QpInt p) (x : kpInt p P) :
    (u • x : kpAdic p P) = u • (x : kpAdic p P) := by
  simp [Algebra.smul_def]

/-- The coercion `kpInt p P → kpAdic p P` as a `QpInt`-linear map. -/
noncomputable def kpIntToKpAdic (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    kpInt p P →ₗ[QpInt p] kpAdic p P where
  toFun := fun x => (x : kpAdic p P)
  map_add' := by intro x y; rfl
  map_smul' := by intro u x; exact (kpInt_coe_smul p P u x).symm

/-- The coercion is injective. -/
lemma kpIntToKpAdic_injective (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Function.Injective (kpIntToKpAdic p P) := by
  intro x y h
  exact Subtype.ext h

/-- The embedded (in `kpAdic`) `QpInt`-independence of the Teichmüller
powers: `LinearIndependent.map'` of `teich_powers_independent_qpInt` along
the injective coercion. -/
theorem teich_powers_independent_qpInt_emb (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    LinearIndependent (QpInt p)
      (fun i : Fin (P.inertiaDeg ℤ) =>
        (((teich p P α : kpInt p P) ^ (i : ℕ)) : kpAdic p P)) := by
  classical
  have hker : (kpIntToKpAdic p P).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (kpIntToKpAdic_injective p P)
  have hmap := LinearIndependent.map' (teich_powers_independent_qpInt (p := p) (P := P)
    (α := α) hα hgen) (kpIntToKpAdic p P) hker
  change LinearIndependent (QpInt p) (fun i : Fin (P.inertiaDeg ℤ) =>
    (kpIntToKpAdic p P) ((teich p P α : kpInt p P) ^ (i : ℕ)))
  exact hmap

/-- **THE field independence**: the Teichmüller powers are linearly
independent over the field `QpAdic p` in `kpAdic p P`.  (Clear denominators
of a relation with `exists_common_denominator`, multiply the relation by the
common denominator — a field scalar, so no torsion issue — land in the
`kpInt`-submodule via the coercion's linearity, use the embedded
`QpInt`-independence, and recover `c = 0` by cancelling the nonzero common
denominator in the field.) -/
theorem teich_powers_independent_qpAdic (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    LinearIndependent (QpAdic p)
      (fun i : Fin (P.inertiaDeg ℤ) =>
        (((teich p P α : kpInt p P) ^ (i : ℕ)) : kpAdic p P)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  rcases exists_common_denominator (R := QpInt p) (F := QpAdic p) c with ⟨D, hD, u, hu⟩
  -- multiply the relation by the common denominator (as a kpAdic element)
  let sD : kpAdic p P :=
    algebraMap (QpAdic p) (kpAdic p P) (algebraMap (QpInt p) (QpAdic p) D)
  have hc' : sD * (∑ j, c j • (((teich p P α : kpInt p P) ^ (j : ℕ)) : kpAdic p P)) = 0 := by
    rw [hc]
    simp
  -- the terms regroup into the embedded QpInt relation
  have hrel : (∑ j : Fin (P.inertiaDeg ℤ),
      ((u j • (teich p P α : kpInt p P) ^ (j : ℕ)) : kpAdic p P)) = 0 := by
    calc
      (∑ j, ((u j • (teich p P α : kpInt p P) ^ (j : ℕ)) : kpAdic p P))
          = ∑ j, ((algebraMap (QpInt p) (kpInt p P) (u j)) *
                (teich p P α : kpInt p P) ^ (j : ℕ) : kpAdic p P) := by
            apply Finset.sum_congr rfl
            intro j hj
            rfl
      _ = ∑ j, (algebraMap (QpInt p) (kpAdic p P) (u j)) *
            (((teich p P α : kpInt p P) ^ (j : ℕ)) : kpAdic p P) := by
            apply Finset.sum_congr rfl
            intro j hj
            rfl
      _ = ∑ j, (sD * (algebraMap (QpAdic p) (kpAdic p P) (c j))) *
            (((teich p P α : kpInt p P) ^ (j : ℕ)) : kpAdic p P) := by
            apply Finset.sum_congr rfl
            intro j hj
            have huj := hu j
            calc
              (algebraMap (QpInt p) (kpAdic p P) (u j)) *
                  (((teich p P α : kpInt p P) ^ (j : ℕ)) : kpAdic p P)
                  = (algebraMap (QpAdic p) (kpAdic p P) (algebraMap (QpInt p) (QpAdic p) (u j))) *
                      (((teich p P α : kpInt p P) ^ (j : ℕ)) : kpAdic p P) := by rfl
              _ = (algebraMap (QpAdic p) (kpAdic p P) (algebraMap (QpInt p) (QpAdic p) D *
                      c j)) *
                      (((teich p P α : kpInt p P) ^ (j : ℕ)) : kpAdic p P) := by
                    rw [huj]
              _ = (sD * (algebraMap (QpAdic p) (kpAdic p P) (c j))) *
                      (((teich p P α : kpInt p P) ^ (j : ℕ)) : kpAdic p P) := by
                    simp [sD, map_mul]
      _ = ∑ j, (sD * (c j • (((teich p P α : kpInt p P) ^ (j : ℕ)) : kpAdic p P))) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Algebra.smul_def]
            ring
      _ = sD * (∑ j, c j • (((teich p P α : kpInt p P) ^ (j : ℕ)) : kpAdic p P)) := by
            rw [← Finset.mul_sum]
      _ = 0 := hc'
  -- hrel is the image of an equation in kpInt: injectivity of the coercion
  have hrelInt : (∑ j, u j • (teich p P α : kpInt p P) ^ (j : ℕ)) = 0 := by
    apply kpIntToKpAdic_injective p P
    calc
      (kpIntToKpAdic p P) (∑ j, u j • (teich p P α : kpInt p P) ^ (j : ℕ))
          = ∑ j, ((u j • (teich p P α : kpInt p P) ^ (j : ℕ)) : kpAdic p P) := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rfl
      _ = 0 := hrel
  have hu0 : u = 0 := coeff_descent (p := p) (P := P)
    (ι := Fin (P.inertiaDeg ℤ))
    (v := fun j : Fin (P.inertiaDeg ℤ) => (teich p P α : kpInt p P) ^ (j : ℕ))
    (teich_qpInt_sum_zero_coeff_mem_maximal (p := p) (P := P) (α := α) hα hgen)
    u hrelInt
  -- recover c from u: u = 0 and the clearing identity give alg D * c i = 0;
  -- D ≠ 0 is nonzero in the field, so c i = 0
  have hui : u i = 0 := congrFun hu0 i
  have hdeq : (algebraMap (QpInt p) (QpAdic p) D) * c i = 0 := by
    rw [hu i]
    rw [hui]
    simp
  have hDneF : (algebraMap (QpInt p) (QpAdic p) D) ≠ 0 := by
    intro hz
    exact hD (IsFractionRing.injective (QpInt p) (QpAdic p) hz)
  exact (mul_eq_zero.mp hdeq).resolve_left hDneF

end

end Submission.Vdw.LocalField
