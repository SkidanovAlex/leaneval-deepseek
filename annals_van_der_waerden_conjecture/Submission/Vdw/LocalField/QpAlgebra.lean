import Mathlib
import Submission.Vdw.LocalField.BaseAlgebra
import Submission.Vdw.LocalField.Completion
import Submission.Vdw.LocalField.AdicComplete
import Submission.Commons.NumberTheory.Padics.integral_rationals_dense_in_integers

open scoped NumberField
open IsDedekindDomain
open UniformSpace

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (stone G1): the bundled `ℚ_p`-algebra structure on `K_P`

`BaseAlgebra.kpAdic_algebra_qp_exists` only supplies
`Nonempty (Algebra (QpAdic p) (kpAdic p P))`.  This module makes the algebra
structure **concrete**: it rebuilds the completed `ℚ ↪ K` map with explicit
content and bundles it as a global instance, so that the later degree/trace
arguments (G2/G3, Session-59 roadmap) can refer to `algebraMap (QpAdic p)
(kpAdic p P)` and reason about it.

Content:
* `qpValuation p` / `kpValuation p P` — the `(p)`-adic valuation of `ℚ` and
  the `P`-adic valuation of `K` (short names for the underlying
  `HeightOneSpectrum` valuations);
* `withVal_algebraMap_uc` — uniform continuity of the rational algebra map
  between the `WithVal`-spaces (from `BaseAlgebra.withVal_algebraMap_uc`);
* `qpCompletionMap` — the completed `ℚ`-map between the underlying uniform
  completions `(qpValuation p).Completion →+* (kpValuation p P).Completion`
  (`UniformSpace.Completion.mapRingHom` of the WithVal algebra map);
* `qpToKp` — the ring hom `QpAdic p →+* kpAdic p P` (transport through the
  `adicCompletion.equiv` equivalences);
* **`kpAdicAlgebraQp`** — the bundled instance
  `Algebra (QpAdic p) (kpAdic p P)` (`RingHom.toAlgebra qpToKp`, so
  `algebraMap = qpToKp` by rfl — lemma `algebraMap_eq_qpToKp`);
* `toCompletion_qpToKp` — `(qpToKp x).toCompletion = qpCompletionMap x.toCompletion`;
* `qpCompletionMap_algebraMap_rat`, `qpToKp_algebraMap_rat` — the map is
  `ℚ`-linear at the level of rational scalars
  (`qpToKp (algebraMap ℚ (QpAdic p) q) = algebraMap ℚ (kpAdic p P) q`);
* **`isScalarTower_QpAdic`** — `IsScalarTower ℚ (QpAdic p) (kpAdic p P)`
  (the ℚ_p-algebra extends the canonical ℚ-algebra; the scalar tower the
  degree statements over `ℚ_p` need);
* **valuation-integral preservation** (`continuous_qpToKp`,
  `rat_integral_preserved`, **`algebraMap_mem_kpInt`**): the algebraMap of
  the bundled structure sends the ring of integers of `ℚ_p` (the
  `adicCompletionIntegers` of ℚ at `(p)`) into the ring of integers of
  `K_P` (`kpInt p P`).  Proof: rationals preserve integrality
  (`v_K(q) = v_ℚ(q)^e ≤ 1` via `valuation_rat_pow_ramificationIdx` and
  `pow_le_one₀`), the integral set `{v ≤ 1}` is closed
  (`AdicComplete.isClosed_val_le_one`), `qpToKp` is continuous
  (`adicCompletion.uniformEquiv` + `Completion.continuous_map`), and
  integral rationals are dense in the integral completion of ℚ (fleet
  `Commons.NumberTheory.Padics.integral_rationals_dense_in_integers`).

Still deferred to later stones (documented in the Session-59 roadmap): the
valuation-integral preservation of `algebraMap` (`adicCompletionIntegers` of
`ℚ` at `qprime p` map into `kpInt p P`), `Module.Finite (QpAdic p)
(kpAdic p P)` with `finrank = e·f`, and the `[W : ℚ_p] = f` degree argument.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The `(p)`-adic valuation of `ℚ`. -/
abbrev qpValuation (p : ℕ) [Fact (Nat.Prime p)] := (qprime p).valuation ℚ

/-- The `P`-adic valuation of `K`. -/
abbrev kpValuation (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :=
  (kprime p P).valuation K

/-- Uniform continuity of the rational algebra map between the `WithVal`
spaces (the completed-map input). -/
lemma withVal_algebraMap_uc (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    UniformContinuous (algebraMap (WithVal (qpValuation p)) (WithVal (kpValuation p P))) := by
  have hu := withVal_algebraMap_uniformContinuous_rat (K := K) p P
  convert hu using 1
  funext x
  rw [WithVal.algebraMap_left_apply]
  rfl

/-- The completed `ℚ`-map between the underlying uniform completions. -/
noncomputable def qpCompletionMap (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    (qpValuation p).Completion →+* (kpValuation p P).Completion :=
  UniformSpace.Completion.mapRingHom
    (α := WithVal (qpValuation p)) (β := WithVal (kpValuation p P))
    (algebraMap (WithVal (qpValuation p)) (WithVal (kpValuation p P)))
    (withVal_algebraMap_uc p P).continuous

/-- The ring hom `QpAdic p →+* kpAdic p P` (the completed `ℚ ↪ K` map). -/
noncomputable def qpToKp (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    QpAdic p →+* kpAdic p P :=
  ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv (K := K) (v := kprime p P)).symm.toRingHom.comp (qpCompletionMap p P)).comp
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv (K := ℚ) (v := qprime p)).toRingHom

/-- **The bundled `ℚ_p`-algebra structure on `K_P`** (G1): the completion of
the number field `K` at `P | (p)` is a `QpAdic p`-algebra via the completed
`ℚ ↪ K` map. -/
noncomputable instance kpAdicAlgebraQp (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Algebra (QpAdic p) (kpAdic p P) :=
  RingHom.toAlgebra (qpToKp p P)

/-- The algebraMap of the bundled structure is the explicit completed map. -/
lemma algebraMap_eq_qpToKp (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    algebraMap (QpAdic p) (kpAdic p P) = qpToKp p P := by
  rfl

/-- `toCompletion` passes through `qpToKp`: the completed map on the
`adicCompletion` side is the underlying map on the completions. -/
lemma toCompletion_qpToKp (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : QpAdic p) :
    (qpToKp p P x).toCompletion = qpCompletionMap p P (x.toCompletion) := by
  unfold qpToKp
  simp [IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv_apply]
  have hsyme : ∀ y : ((kprime p P).valuation K).Completion,
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv (K := K) (v := kprime p P)).symm y =
        IsDedekindDomain.HeightOneSpectrum.adicCompletion.ofCompletion y := by
    intro y
    rfl
  rw [hsyme]

/-- The completed map is `ℚ`-linear at the level of the underlying
completions: `f (algebraMap ℚ C_ℚ q) = algebraMap ℚ C_K q`. -/
theorem qpCompletionMap_algebraMap_rat (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (q : ℚ) :
    qpCompletionMap p P (algebraMap ℚ ((qpValuation p).Completion) q) =
      algebraMap ℚ ((kpValuation p P).Completion) q := by
  calc
    qpCompletionMap p P (algebraMap ℚ ((qpValuation p).Completion) q)
        = qpCompletionMap p P ((algebraMap ℚ (WithVal (qpValuation p)) q : WithVal (qpValuation p)) : (qpValuation p).Completion) := by rfl
    _ = ((algebraMap (WithVal (qpValuation p)) (WithVal (kpValuation p P)) (algebraMap ℚ (WithVal (qpValuation p)) q)
          : WithVal (kpValuation p P)) : (kpValuation p P).Completion) := by
          unfold qpCompletionMap
          exact UniformSpace.Completion.mapRingHom_coe (withVal_algebraMap_uc p P).continuous
            (algebraMap ℚ (WithVal (qpValuation p)) q)
    _ = ((algebraMap ℚ (WithVal (kpValuation p P)) q : WithVal (kpValuation p P)) : (kpValuation p P).Completion) := by rfl
    _ = algebraMap ℚ ((kpValuation p P).Completion) q := by rfl

/-- The tower law at rational scalars: `qpToKp` extends the canonical
`ℚ`-algebra map. -/
theorem qpToKp_algebraMap_rat (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (q : ℚ) :
    qpToKp p P (algebraMap ℚ (QpAdic p) q) = algebraMap ℚ (kpAdic p P) q := by
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext (K := K) (v := kprime p P)
  calc
    (qpToKp p P (algebraMap ℚ (QpAdic p) q)).toCompletion
        = qpCompletionMap p P ((algebraMap ℚ (QpAdic p) q).toCompletion) := toCompletion_qpToKp p P _
    _ = qpCompletionMap p P (algebraMap ℚ ((qpValuation p).Completion) q) := by
          rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion_toCompletion
            (R := ℤ) (K := ℚ) (S := ℚ) (v := qprime p) (r := q)]
    _ = algebraMap ℚ ((kpValuation p P).Completion) q := qpCompletionMap_algebraMap_rat p P q
    _ = (algebraMap ℚ (kpAdic p P) q).toCompletion := by
          exact (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion_toCompletion
            (R := 𝓞 K) (K := K) (S := ℚ) (v := kprime p P) (r := q)).symm

/-- The scalar tower `ℚ → ℚ_p → K_P`: the bundled `ℚ_p`-algebra extends the
canonical `ℚ`-algebra on `K_P` (every rational scalar acts the same through
`ℚ_p` as directly). -/
instance isScalarTower_QpAdic (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    IsScalarTower ℚ (QpAdic p) (kpAdic p P) := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro q
  rw [← qpToKp_algebraMap_rat p P q]
  rfl

/-- `qpToKp` is continuous (it is built from the uniform-space equivalences
and the continuous completed map). -/
lemma continuous_qpToKp (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Continuous (qpToKp p P) := by
  unfold qpToKp
  have hc1 : Continuous
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv (K := ℚ) (v := qprime p)).toRingHom) := by
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv ℚ (qprime p)).continuous
  have hc2 : Continuous (qpCompletionMap p P) := by
    unfold qpCompletionMap
    rw [UniformSpace.Completion.coe_mapRingHom]
    exact UniformSpace.Completion.continuous_map
  have hc3 : Continuous
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv (K := K) (v := kprime p P)).symm.toRingHom) := by
    exact (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv K (kprime p P)).symm.continuous
  exact hc3.comp (hc2.comp hc1)

/-- Integral rational scalars map to integral elements: for `q : ℚ` with
`(qprime p).valuation ℚ q ≤ 1` (i.e. `q` integral at `p`), the completed map
sends `q` into the valuation ring of `K_P`.  (Rational content of the
valuation-integral preservation: `v_K(q) = v_ℚ(q)^e` with
`e := P.ramificationIdx ℤ`.) -/
lemma rat_integral_preserved (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (q : ℚ)
    (hq : (qprime p).valuation ℚ q ≤ 1) :
    Valued.v (qpToKp p P (algebraMap ℚ (QpAdic p) q)) ≤ 1 := by
  rw [qpToKp_algebraMap_rat p P q]
  have h1 : algebraMap ℚ (kpAdic p P) q = (algebraMap ℚ K q : kpAdic p P) := by
    simpa using (congrFun (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
      (R := 𝓞 K) (K := K) (S := ℚ) (v := kprime p P)) q)
  rw [h1]
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := K) (v := kprime p P)]
  rw [eq_ratCast (algebraMap ℚ K) q]
  rw [valuation_rat_pow_ramificationIdx (K := K) p P q]
  exact pow_le_one₀ (n := P.ramificationIdx ℤ) bot_le hq

/-- **Valuation-integral preservation of the bundled `ℚ_p`-algebra map**:
the `algebraMap (QpAdic p) (kpAdic p P)` sends the ring of integers of
`ℚ_p` — the `adicCompletionIntegers` of ℚ at the height-one prime `(p)` —
into the ring of integers of `K_P`.  Proof: integral rationals map to
integral elements (`rat_integral_preserved`); they are dense in the integral
completion of `ℚ` (fleet
`Commons.NumberTheory.Padics.integral_rationals_dense_in_integers`); the
map is continuous (`continuous_qpToKp`); and the integral elements form a
closed set (`AdicComplete.isClosed_val_le_one`). -/
theorem algebraMap_mem_kpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (x : (qprime p).adicCompletionIntegers ℚ) :
    (algebraMap (QpAdic p) (kpAdic p P) (x : QpAdic p) : kpAdic p P) ∈
      (kprime p P).adicCompletionIntegers K := by
  classical
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have hSclosed : IsClosed ({y : kpAdic p P | Valued.v y ≤ 1} : Set (kpAdic p P)) :=
    isClosed_val_le_one p P
  have hcont : Continuous (qpToKp p P) := continuous_qpToKp p P
  let S : Set (kpAdic p P) := {y : kpAdic p P | Valued.v y ≤ 1}
  let C : Set (QpAdic p) := qpToKp p P ⁻¹' S
  have hCclosed : IsClosed C := hSclosed.preimage hcont
  have hD : {y : QpAdic p | ∃ q : ℚ, (qprime p).valuation ℚ q ≤ 1 ∧ (q : QpAdic p) = y} ⊆ C := by
    intro y hy
    rcases hy with ⟨q, hq, rfl⟩
    have hcoe : (q : QpAdic p) = algebraMap ℚ (QpAdic p) q := by
      simp
    rw [hcoe]
    exact rat_integral_preserved p P q hq
  have hx : (x : QpAdic p) ∈ closure
      {y : QpAdic p | ∃ q : ℚ, (qprime p).valuation ℚ q ≤ 1 ∧ (q : QpAdic p) = y} := by
    simpa [QpAdic] using (Commons.NumberTheory.Padics.integral_rationals_dense_in_integers
      (v := qprime p) x)
  have hxpre : (x : QpAdic p) ∈ C := (closure_minimal hD hCclosed) hx
  exact hxpre

end
end Submission.Vdw.LocalField
