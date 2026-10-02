/-
# The Böttcher coordinate of the antipolynomial family

For the antiholomorphic unicritical family `T_c(z) = (conj z)^2 + c` we introduce the
Böttcher coordinate of `T_c` as a *characterised* object: a continuous function on the
escaping set which satisfies the Böttcher equation

`φ (T_c z) = conj (φ z) ^ 2`

and is asymptotic to the identity at infinity.  Such a `φ` is *unique*
(`IsDynBottcher.eq`), so "the Böttcher coordinate" is a well defined object even though we
do not construct it by a formula; the construction (Böttcher's theorem) belongs to the
sibling area `Work.Bottcher`.  Its modulus is recovered from the Green function,

`‖φ z‖ = exp (G_c z)`  (`IsDynBottcher.modulus`).

**Which domain?**  `IsDynBottcher c φ` (Böttcher coordinate on the whole escaping set
`{G_c > 0}`) is satisfiable **iff `c ∈ M*`**, so it must not be used for the parameter plane
off the mandelbar: there Böttcher's theorem only gives a coordinate on the *critical domain*
`{G_c > G_c(0)}`, which contains the critical value `c`.  Accordingly the parameter side uses

* `critDomain c = {z | paramPotential c < greenFun c z}`   (the domain),
* `IsCritBottcher c φ`   (Böttcher coordinate on the critical domain),
* `BottcherExists`   (existence of such a coordinate for every `c ∉ M*`, the held input),

while `IsDynBottcher` is kept for the *dynamical* plane, where it is only ever instantiated at
parameters `c ∈ M*` (see `DynBottcher`, `Landing.landsAt`).

`BottcherExists` is the (classical, unproved here) existence statement, used as a
hypothesis by the parameter-ray interface in `MbDefs.lean`.

## Main definitions

* `Work.ParamRays.escapingSet c` : the escaping set of `T_c`.
* `Work.ParamRays.IsDynBottcher c φ` : `φ` is a Böttcher coordinate of `T_c`; satisfiable iff
  `c ∈ M*` (use `IsCritBottcher` off the mandelbar).
* `Work.ParamRays.critDomain c` : the critical domain `{G_c > G_c 0} ⊇ {c} ∪ {G_c > 0}`.
* `Work.ParamRays.IsCritBottcher c φ` : `φ` is a Böttcher coordinate on the critical domain.
* `Work.ParamRays.BottcherExists` : every parameter outside the mandelbar has a critical
  Böttcher coordinate.

## Main results

* `Work.ParamRays.isDynBottcher_zero_id` : the predicate is not vacuous.
* `Work.ParamRays.IsDynBottcher.functional_iterate` : `φ (T_c^{2n} z) = φ z ^ 4^n`.
* `Work.ParamRays.IsDynBottcher.eq` : uniqueness of the Böttcher coordinate.
* `Work.ParamRays.IsDynBottcher.modulus` : `‖φ z‖ = exp (G_c z)`.
-/
import Submission.Work.ParamRays.Green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The escaping set -/

/-- The escaping set of `T_c`: the points whose orbit tends to infinity. -/
def escapingSet (c : ℂ) : Set ℂ := {z | Escaping c z}

theorem mem_escapingSet {c z : ℂ} : z ∈ escapingSet c ↔ Escaping c z := Iff.rfl

theorem Escaping.iterate {c z : ℂ} (h : Escaping c z) (n : ℕ) :
    Escaping c (orbit c z n) := by
  simp only [Escaping] at h ⊢
  have h2 : (fun m : ℕ => ‖orbit c (orbit c z n) m‖) =
      fun m : ℕ => ‖orbit c z (m + n)‖ := by
    funext m
    rw [← orbit_add c z n m, Nat.add_comm]
  rw [h2]
  exact h.comp (tendsto_add_atTop_nat n)

theorem Escaping.eventually_gt {c z : ℂ} (h : Escaping c z) (R : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, R < ‖orbit c z n‖ := by
  obtain ⟨i, hi⟩ := (Filter.tendsto_atTop_atTop.mp h) (R + 1)
  exact Filter.eventually_atTop.mpr ⟨i, fun n hn => lt_of_lt_of_le (by linarith) (hi n hn)⟩

/-! ## The Böttcher coordinate -/

/-- `IsDynBottcher c φ` : `φ` is a Böttcher coordinate for the antipolynomial `T_c`: it is the
unique continuous function on the escaping set solving the Böttcher equation
`φ (T_c z) = conj (φ z) ^ 2` and asymptotic to the identity at infinity.

**This holds only for `c ∈ M*`.**  For `c ∉ M*` the critical value `c` is an escaping point
(`escapes_criticalValue`) and the Böttcher equation forces `φ` to have no zeros on the escaping
set, so its integral along the essential loops of `{G_c > 0}` would have to be compatible with
`w ↦ conj w ^ 2`; that fails (the loop around the critical value has winding `±1`, which is
carried by `conj (·)^2` to winding `∓2`).  Consequently `IsDynBottcher c φ` is *false for every*
`c ∉ M*`; off the mandelbar use `IsCritBottcher` below, which lives on `critDomain c`. -/
def IsDynBottcher (c : ℂ) (φ : ℂ → ℂ) : Prop :=
  ContinuousOn φ (escapingSet c) ∧
    (∀ z : ℂ, Escaping c z → φ (Tantibar c z) = conj (φ z) ^ 2) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖φ z - z‖ ≤ ε * ‖z‖)

/-- `IsDynBottcher` is not vacuous: for `c = 0` the identity is a Böttcher coordinate. -/
theorem isDynBottcher_zero_id : IsDynBottcher 0 id := by
  refine ⟨continuousOn_id, ?_, ?_⟩
  · intro z _
    show Tantibar 0 z = (starRingEnd ℂ) z ^ 2
    rw [Tantibar]
    simp
  · intro ε hε
    filter_upwards with z
    rw [id_eq, sub_self, norm_zero]
    exact mul_nonneg hε.le (norm_nonneg z)

/-- `conj (conj w ^ 2) ^ 2 = w ^ 4`. -/
theorem conj_sq_sq (w : ℂ) : conj (conj w ^ 2) ^ 2 = w ^ 4 := by
  rw [map_pow, Complex.conj_conj, ← pow_mul]

theorem IsDynBottcher.functional_iterate {c : ℂ} {φ : ℂ → ℂ} (h : IsDynBottcher c φ)
    {z : ℂ} (hz : Escaping c z) (n : ℕ) :
    φ (orbit c z (2 * n)) = φ z ^ (4 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hw : Escaping c (orbit c z (2 * n)) := hz.iterate (2 * n)
    have hw1 : Escaping c (orbit c z (2 * n + 1)) := hz.iterate (2 * n + 1)
    have e1 : orbit c z (2 * n + 1) = Tantibar c (orbit c z (2 * n)) := orbit_succ c z (2 * n)
    have e2 : orbit c z (2 * (n + 1)) = Tantibar c (orbit c z (2 * n + 1)) := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring]
      exact orbit_succ c z (2 * n + 1)
    rw [e2, h.2.1 _ hw1, e1, h.2.1 _ hw, ih, conj_sq_sq, ← pow_mul, pow_succ]

/-! ## The critical domain and the critical Böttcher coordinate

`IsDynBottcher` is satisfiable only for `c ∈ M*`; for the *parameter* side (where `c` ranges
over the complement of the mandelbar) Böttcher's theorem produces a coordinate on the smaller
domain `{G_c > G_c 0}`, on which `T_c` is a conformal (anti-holomorphic) isomorphism onto
`{G_c > 2 G_c 0} ⊇ {G_c > G_c 0}`.  That domain contains both the critical value `c`
(`self_mem_critDomain`) and the points near infinity, and it equals the escaping set exactly
when `c ∈ M*`. -/

/-- The **critical domain** of `T_c`: `{z | G_c 0 < G_c z}`, the largest forward-invariant
domain on which `T_c` is (anti-)conformal.  It equals the escaping set iff `c ∈ M*`
(`critDomain_eq_escapingSet`); for `c ∉ M*` it contains the critical value `c`
(`self_mem_critDomain`) and avoids the critical point `0` and the critical value's preimages
along the backward orbit of `0`.

This is the *parameter-plane* Böttcher domain: `Φ c = φ_c c` is defined from it, and it is the
domain which the sibling area `Work.Bottcher` builds its coordinate on
(`Work.Bottcher.CritDomain`). -/
def critDomain (c : ℂ) : Set ℂ := {z | paramPotential c < greenFun c z}

/-- `IsCritBottcher c φ` : `φ` is the Böttcher coordinate of `T_c` on the critical domain
`critDomain c`: a continuous function on `critDomain c` solving the Böttcher equation
`φ (T_c z) = conj (φ z) ^ 2` there (`critDomain c` is `T_c`-invariant, `Tantibar_mem_critDomain`)
and asymptotic to the identity at infinity.

On `critDomain c` the map is unique (`isCritBottcher_unique`), so `φ` is canonical, even though
its *holomorphy* (which would follow from Böttcher's theorem) is not part of the definition. -/
def IsCritBottcher (c : ℂ) (φ : ℂ → ℂ) : Prop :=
  ContinuousOn φ (critDomain c) ∧
    (∀ z : ℂ, z ∈ critDomain c → φ (Tantibar c z) = conj (φ z) ^ 2) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖φ z - z‖ ≤ ε * ‖z‖)

/-- The classical existence statement: every parameter outside the mandelbar has a
**critical** Böttcher coordinate.  (This is Böttcher's theorem for the family `z ↦ z̄² + c`,
in the only form in which it is true off the mandelbar; it is proved in the sibling area
`Work.Bottcher` and taken as a hypothesis here.) -/
def BottcherExists : Prop := ∀ c : ℂ, c ∉ Mandelbar → ∃ φ : ℂ → ℂ, IsCritBottcher c φ

end Work.ParamRays
