/-
# LinnikContract2 — Spec.lean  (the FROZEN round-2 specification)

**ROUND 2, FROZEN.**  This module spells out, as proved equivalences with explicit bodies, the
definitions that round 2 changed or introduced — the form in which they were refereed.  Each
theorem is `Iff.rfl`/`rfl`, i.e. the specification *is* the definition; writing them out is what
makes the round-2 contract readable without unfolding.

The change from round 1 is confined to the height range of `λ₁`:

* `IsZW` (`= IsZH 50`) is the round-2 wide region: a zero of a non-principal `L(s,χ)` with
  `|Im| ≤ 50` (HB's own §12 constant is `10`; the height is raised to `50` because the engines
  of §§6–10 compare against zeros up to height `40 + δ` — see `Defs.lean`).
* `IsMin1` is now `IsZW χ₁ ρ₁ ∧ ∀ χ u, IsZW χ u → λ(ρ₁) ≤ λ(u)`: `λ₁` is minimal over the wide
  region (the numbered zero need not lie in the working region).  Round 1's predicate is kept as
  `IsMin1N` and is the `H = 1` member of the family `IsMin1H`.
* `HBNumbering` (`Area 0`) is the new input: HB §6's numbered pair exists, i.e. a pair satisfying
  round-2 `IsMin1` (for large `q`, whenever the wide region is inhabited).
* `(D2)` of `DensityCert` now has its hypothesis over `IsZW` (round 1 had `IsZ`).
* `Assembly` (Area 7) keeps round 1's conclusion and carries **no** setting clause: the window
  `¬ IsZ χ₁ ρ₁` is closed by `A7/WindowCert.lean` + `A7/WindowAssembly.lean` (`area7_window`);
  round 2's earlier draft carried `NumZeroNarrow`, which is now a theorem and has been deleted.
-/
import Submission.Work.LinnikContract2.Areas
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract2.Compose

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2

variable {q : ℕ} [NeZero q]

/-- **FROZEN (round 2), region.**  `IsZW` is the round-2 wide region: a zero of a non-principal
`L(s,χ)` with `|Im ρ| ≤ 50`, the frozen round-2 height (see `Defs.lean` for why it is `50` and
not HB §12's own constant `10`). -/
theorem Round2_IsZW_spec {χ : DirichletCharacter ℂ q} {ρ : ℂ} :
    IsZW χ ρ ↔ (χ ≠ 1 ∧ zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 50) := Iff.rfl

/-- **FROZEN (round 2), the fix.**  `λ₁ = λ(ρ₁)` is the minimum of `λ` over HB's wide region
`|Im| ≤ 50`, attained at the *wide minimiser* `ρ₁` (a non-principal zero with `|Im ρ₁| ≤ 50`).

There is deliberately **no** requirement that `ρ₁` lie in the working region `|Im| ≤ 1`: the
minimality over `|Im| ≤ 50` is what the `P₃` engine of HB §§6–10 (windows up to height
`40 + δ`) and HB Lemma 12.1 (heights `γ⁽ʲ⁾ − γ⁽ᵏ⁾ ∈ [−2,2]`) need, and `IsZ → IsZW` makes the working-region
minimality a consequence (`IsMin1.le_lamOf_of_isZ`).  In the branch `λ₁ < 0.348`, `Z1` makes `ρ₁`
*real*, hence a working-region zero, and `IsMin1.toIsMin1N` then recovers round 1's predicate.
Round 1 had `IsZ` in place of `IsZW` **and** required `ρ₁ ∈ IsZ`; the first was too weak, the
second was an unprovable input. -/
theorem Round2_IsMin1_spec {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} :
    IsMin1 χ₁ ρ₁ ↔
      (IsZW χ₁ ρ₁ ∧
        ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZW χ u → lamOf q ρ₁ ≤ lamOf q u) := Iff.rfl

/-- **FROZEN (round 2), the family.**  The height-`H` minimality. -/
theorem Round2_IsMin1H_spec {H : ℝ} {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} :
    IsMin1H H χ₁ ρ₁ ↔
      (IsZH H χ₁ ρ₁ ∧
        ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZH H χ u → lamOf q ρ₁ ≤ lamOf q u) := Iff.rfl

/-- **FROZEN (round 2), round 1's predicate.**  `IsMin1N` is the `H = 1` member of the family, and
is definitionally round 1's `IsMin1`. -/
theorem Round2_IsMin1N_spec {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} :
    IsMin1N χ₁ ρ₁ ↔
      (IsZ χ₁ ρ₁ ∧
        ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZ χ u → lamOf q ρ₁ ≤ lamOf q u) := Iff.rfl

/-- **FROZEN (round 2), the fixed definition written out.**  The *round-2* `IsMin1` is the wide
*minimality*: `ρ₁` is a non-principal zero with `|Im ρ₁| ≤ 50` whose `λ` is minimal over `|Im| ≤ 50`.
There is no membership requirement in the working region `|Im| ≤ 1`; that is round 1's `IsMin1N`
(below), and it re-enters the §§14–15 argument only through `Z1` in the branch `λ₁ < 0.348`. -/
theorem Round2_IsMin1_def {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} :
    IsMin1 χ₁ ρ₁ ↔
      (IsZH 50 χ₁ ρ₁ ∧
        ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZH 50 χ u → lamOf q ρ₁ ≤ lamOf q u) := Iff.rfl

/-- **The narrow form of the minimality is free** (no hypothesis needed): the wide region of
round 2 contains the working region, so `IsMin1` is also minimality over `IsZ`. -/
theorem Round2_IsMin1_narrow {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} (h : IsMin1 χ₁ ρ₁) :
    ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZ χ u → lamOf q ρ₁ ≤ lamOf q u :=
  fun _ _ hu => h.le_lamOf_of_isZ hu

/-- **FROZEN, AREA 0.**  HB §6's numbering exists: whenever the wide region is inhabited, a pair
satisfying round-2 `IsMin1` exists.  This is a **theorem** (`Work.LinnikContract2.area0`),
deduced from the finiteness of the zeros in the critical strip with `|Im| ≤ 50`; there is no
extra input. -/
theorem Round2_Area0_spec :
    Area0 ↔ ∀ (q : ℕ) [NeZero q],
      (∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZW χ ρ) →
      ∃ (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), IsMin1 χ₁ ρ₁ := Iff.rfl

/-- **FROZEN, AREA 3.**  The zero-free certificate: for the numbered pair, the five clauses
`Z1`–`Z5` (HB Theorem 1, [X] Lemma 3.8, HB Theorem 2 with Lemma 10.3, the §15 rows, the §14 rows
with the Deuring–Heilbronn repulsion).  The clauses themselves are *unchanged* from round 1; only
the meaning of their hypothesis `IsMin1` changed. -/
theorem Round2_ZeroFreeCert_spec :
    ZeroFreeCert ↔ ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
        IsMin1 χ₁ ρ₁ →
        Z1 χ₁ ρ₁ ∧ Z2 χ₁ ρ₁ ∧ Z3 χ₁ ρ₁ ∧ Z4 χ₁ ρ₁ ∧ Z5 χ₁ ρ₁ lamS := Iff.rfl

/-- **FROZEN, AREA 4 (D1).**  HB Lemma 11.1, on the working region, up to `λ₀ = logloglog q/3`. -/
theorem Round2_D1_spec :
    D1 ↔ ∀ ε : ℝ, 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q],
      ∑ χ ∈ Finset.univ.filter
          (fun χ : DirichletCharacter ℂ q => ∃ ρ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q),
        wHB (lamChar χ) ≤ 67/6 + ε := Iff.rfl

/-- **FROZEN, AREA 4 (D2), the second fix.**  HB Table 13 (from HB Lemma 12.1), with the
hypothesis ranging over *all* non-principal zeros of height `≤ 50`, the conclusion over
the working region (`Ncount`, as in HB's `N(λ)`). -/
theorem Round2_D2_spec :
    D2 ↔ ∀ e ∈ table13, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q],
      (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZH 50 χ ρ → e.2.1 ≤ lamOf q ρ) →
      Ncount q e.1 ≤ e.2.2 := Iff.rfl

/-- **FROZEN, AREA 7.**  The assembly: given the three certificates and the §6 numbering, the
signed zero sum is bounded away from `K² = (3/10)²` by `η = η(lamS)`, uniformly in
`q ≥ q₀(R, lamS, η)` and in `a` coprime to `q`, away from the Siegel case. -/
theorem Round2_Assembly_spec :
    Area7 ↔ (ZeroFreeCert → DensityCert → PerCharCert →
      ∀ lamS : ℝ, 0 < lamS → ∃ η : ℝ, 0 < η ∧ ∀ R : ℝ, 0 < R → ∃ q₀ : ℕ,
        ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q], ¬ SiegelZero q lamS → ∀ a : ℕ, a.Coprime q →
        (∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
            ((starRingEnd ℂ) (χ a) * boxSum q (11/2) (3/10) R χ).re) <
          (3/10 : ℝ)^2 - η) := Iff.rfl

/-- **FROZEN, the composition (round 2).**  The seven areas of the contract give Linnik's theorem
with the exponent `11/2 = 5.5`; the §6 numbered zero is supplied inside `Area7` by the proved
`Area0`. -/
theorem Round2_linnik_of_areas_spec :
    (Area1 → Area2 → Area3 → Area4 → Area5 → Area6 → Area7 →
      ∃ c : ℝ, ∀ ⦃a d : ℕ⦄, 0 < a → a < d → a.Coprime d →
        LeanEval.NumberTheory.Linnik.p a d ≤ c * d ^ (5.5 : ℝ)) :=
  fun h1 h2 h3 h4 h5 h6 h7 => linnik_of_areas h1 h2 h3 h4 h5 h6 h7

/-- **FROZEN, the *discharged* setting clause.**  Round 2's earlier draft carried the clause
`NumZeroNarrow` (`IsMin1 χ₁ ρ₁ → λ₁ < 348/1000 ∨ IsZ χ₁ ρ₁`).  The clause is *false* in the window
and is no longer needed: in the window `¬ IsZ χ₁ ρ₁`, `(Z1)` forces `348/1000 ≤ λ₁`, and the §15
argument is then run at the *narrow* (working-region) minimiser (`A7/WindowCert.lean`,
`A7/WindowAssembly.lean`).  This is the only thing the window takes from `(Z1)`, recorded here as
part of the frozen specification. -/
theorem Round2_window_lam_ge {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hmin : IsMin1 χ₁ ρ₁) (hZ1 : Z1 χ₁ ρ₁) (hnZ : ¬ IsZ χ₁ ρ₁) :
    (348:ℝ)/1000 ≤ lamOf q ρ₁ := by
  by_contra hcon
  have hlt : lamOf q ρ₁ < (348:ℝ)/1000 := lt_of_not_ge hcon
  have hc348 : (0.348 : ℝ) = (348:ℝ)/1000 := by norm_num
  unfold Z1 at hZ1
  rw [hc348] at hZ1
  have h := (hZ1 hlt).2.1
  exact hnZ ⟨hmin.1.1, hmin.1.2.1, by rw [h]; norm_num⟩

end Work.LinnikContract2
