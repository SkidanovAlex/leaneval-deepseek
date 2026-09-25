/-
Copyright: the martinet_totally_real_towers team.

# The Kummer sequence for `Gal(L/K)` acting on `Lˣ`

The Kummer sequence `Work.ConCohomology.kummerSES n` instantiated at `B = Additive Lˣ` and
`G = Gal(L/K)`: `0 → μ_n → Lˣ →ⁿ n·Lˣ → 0`.  Hilbert 90 (`hilbert90_subsingleton_H1`) makes
`H¹(Gal(L/K), Lˣ)` trivial, so `δ⁰` is onto `H¹(Gal(L/K), μ_n)` (Kummer theory) and
`H²(Gal(L/K), μ_n) → H²(Gal(L/K), Lˣ)` is injective with image the classes killed by the `n`-th
power map (the `n`-torsion Brauer classes; for `n = 2` and `char K ≠ 2`, `μ₂ = {±1}` and
`H²(G,ℤ/2) ≅ H²(G,Lˣ)[2]`).

`hC : Subsingleton (H1 (Gal(L/K)) ↥(nPowers n))` is automatic when every element of `Lˣ` is an
`n`-th power (e.g. `L` separably closed and `n ≠ 0` in `L`, in particular `L = K̄` with
`char K ∤ n`), since then `nPowers n = ⊤`.
-/

import Submission.Work.ConCohomology.KummerConsequences
import Submission.Work.ConCohomology.hilbert90_subsingleton_H1
import Submission.Work.ConCohomology.nPowers_units_eq_top
import Submission.Work.ConCohomology.H1_nPowers_subsingleton

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

section UnitsGalois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- **Kummer theory** `H¹(Gal(L/K), μ_n) ≅ H⁰(Gal(L/K), n·Lˣ)/im(n·)`: `δ⁰` is onto. -/
theorem kummer_units_H1_surj (n : ℕ)
    (x : H1 (Gal(L/K)) ↥(nTorsion (G := Gal(L/K)) (B := Additive Lˣ) n)) :
    ∃ c : H0 (Gal(L/K)) ↥(nPowers (G := Gal(L/K)) (B := Additive Lˣ) n),
      connecting0 (kummerSES (G := Gal(L/K)) (B := Additive Lˣ) n) c = x :=
  kummer_H1_surjective _ hilbert90_subsingleton_H1 x

/-- **Kummer theory**, kernel part: a class in `H⁰(Gal(L/K), n·Lˣ)` is killed by `δ⁰` exactly when
it is the `n`-th power of an element of `K^× = H⁰(Gal(L/K), Lˣ)`. -/
theorem kummer_units_H1_ker (n : ℕ)
    (c : H0 (Gal(L/K)) ↥(nPowers (G := Gal(L/K)) (B := Additive Lˣ) n)) :
    connecting0 (kummerSES (G := Gal(L/K)) (B := Additive Lˣ) n) c = 0 ↔
      ∃ b : H0 (Gal(L/K)) (Additive Lˣ), H0Map (kummerG (G := Gal(L/K)) (B := Additive Lˣ) n) b = c :=
  kummer_H1_ker n c

/-- **`H²(Gal(L/K), μ_n) ↪ H²(Gal(L/K), Lˣ)`** (the `n`-torsion Brauer classes). -/
theorem kummer_units_H2_inj (n : ℕ)
    (hC : Subsingleton (H1 (Gal(L/K)) ↥(nPowers (G := Gal(L/K)) (B := Additive Lˣ) n))) :
    Function.Injective (H2Map (kummerF (G := Gal(L/K)) (B := Additive Lˣ) n)) :=
  kummer_H2_inj n hilbert90_subsingleton_H1 hC

/-- **Every `n`-torsion class in `H²(Gal(L/K), Lˣ)` comes from `H²(Gal(L/K), μ_n)`.** -/
theorem kummer_units_H2_torsion (n : ℕ)
    (hC : Subsingleton (H1 (Gal(L/K)) ↥(nPowers (G := Gal(L/K)) (B := Additive Lˣ) n)))
    (y : H2 (Gal(L/K)) (Additive Lˣ))
    (hy : H2Map (kummerG (G := Gal(L/K)) (B := Additive Lˣ) n) y = 0) :
    ∃ x : H2 (Gal(L/K)) ↥(nTorsion (G := Gal(L/K)) (B := Additive Lˣ) n),
      H2Map (kummerF (G := Gal(L/K)) (B := Additive Lˣ) n) x = y :=
  kummer_H2_torsion_range n hilbert90_subsingleton_H1 hC y hy

/-- **`hC` is free for `L` separably closed with `char K ∤ n`:** in that case every unit of `L` is
an `n`-th power, so `H¹(Gal(L/K), n·Lˣ) = H¹(Gal(L/K), Lˣ) = 0` by Hilbert 90. -/
theorem kummer_units_H2_inj_sepClosed {L : Type*} [Field L] [Algebra K L] [IsGalois K L]
    [IsSepClosed L] (n : ℕ) (hn : (n : L) ≠ 0) :
    Function.Injective (H2Map (kummerF (G := Gal(L/K)) (B := Additive Lˣ) n)) :=
  kummer_units_H2_inj n
    (H1_nPowers_subsingleton n (nPowers_units_eq_top (K := K) (L := L) n hn))

/-- **Every `n`-torsion class of `H²(Gal(L/K), Lˣ)` comes from `H²(Gal(L/K), μ_n)`**, for `L`
separably closed with `char K ∤ n` (e.g. `L = K̄`).  Together with
`kummer_units_H2_inj_sepClosed` this is `H²(Gal(L/K), μ_n) ≅ H²(Gal(L/K), Lˣ)[n]`. -/
theorem kummer_units_H2_torsion_sepClosed {L : Type*} [Field L] [Algebra K L] [IsGalois K L]
    [IsSepClosed L] (n : ℕ) (hn : (n : L) ≠ 0) (y : H2 (Gal(L/K)) (Additive Lˣ))
    (hy : H2Map (kummerG (G := Gal(L/K)) (B := Additive Lˣ) n) y = 0) :
    ∃ x : H2 (Gal(L/K)) ↥(nTorsion (G := Gal(L/K)) (B := Additive Lˣ) n),
      H2Map (kummerF (G := Gal(L/K)) (B := Additive Lˣ) n) x = y :=
  kummer_units_H2_torsion n
    (H1_nPowers_subsingleton n (nPowers_units_eq_top (K := K) (L := L) n hn)) y hy

end UnitsGalois

end Work.ConCohomology
