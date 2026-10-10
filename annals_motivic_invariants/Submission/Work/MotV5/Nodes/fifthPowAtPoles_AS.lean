import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.asTwistFieldTrue_basic
import Submission.Work.MotV5.exists_kleinData_shiftProj
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Nodes.poleFibre_tp

set_option linter.unusedVariables false -- v435-speed

namespace Work.MotV5.Nodes

open scoped WithZero

section Bookkeeping

/-- **Valuation bookkeeping at a pole.**  For a valuation `v` with values in `ℤᵐ⁰` and `1 < v x` (a
pole of `x`), if the *value* `v x` is a fifth power of the value group then so is the value of
`x ^ 3 + x`: indeed `v (x ^ 3 + x) = (v x) ^ 3` (the term `x ^ 3` strictly dominates `x`), and
`(v x) ^ 3 = ((v s) ^ 3) ^ 5` when `v x = (v s) ^ 5`.

This isolates the *arithmetic* content of `Work.MotV5.Nodes.fifthPowAtPoles_AS` from the geometric
content: since `fAS 𝕜 = X ^ 3 + X`, the goal follows from the single statement that at every
valuation above the pole of `t` the value of `t` itself is a fifth power of the value group. -/
theorem fifthPow_pow_three_add {F : Type*} [Field F]
    (v : Valuation F (WithZero (Multiplicative ℤ))) (x : F) (hx : 1 < v x)
    (h5 : ∃ s : F, v x = v s ^ 5) : ∃ u : F, v (x ^ 3 + x) = v u ^ 5 := by
  obtain ⟨s, hs⟩ := h5
  refine ⟨s ^ 3, ?_⟩
  have hx3 : v x < v (x ^ 3) := by
    rw [Valuation.map_pow]
    exact lt_self_pow₀ hx (by norm_num : (1 : ℕ) < 3)
  rw [add_comm, Valuation.map_add_eq_of_lt_right v hx3, Valuation.map_pow, Valuation.map_pow, hs,
    ← pow_mul, ← pow_mul]

/-- The same bookkeeping for the value of `c * (x ^ 3 + x)` when `c` is a unit at `v`: the second
class of the link is `2 • fAS 𝕜`, and `2` is a unit of the (characteristic `5`) base field. -/
theorem fifthPow_const_mul_pow_three_add {F : Type*} [Field F]
    (v : Valuation F (WithZero (Multiplicative ℤ))) (c x : F) (hc : v c = 1) (hx : 1 < v x)
    (h5 : ∃ s : F, v x = v s ^ 5) : ∃ u : F, v (c * (x ^ 3 + x)) = v u ^ 5 := by
  obtain ⟨u, hu⟩ := fifthPow_pow_three_add v x hx h5
  exact ⟨u, by rw [Valuation.map_mul, hu, hc, one_mul]⟩

end Bookkeeping

/-- **The geometric input of `fifthPowAtPoles_AS`, isolated.**  At every valuation of the twist
(trivial on `𝕜`) above the pole of `t`, the value of `t` itself is a fifth power of the value group.

This is *stronger* than the conclusion of `Work.MotV5.Nodes.fifthPowAtPoles_AS` (which only asks for
the value of `g = t ^ 3 + t` to be a fifth power), and it is exactly what the fibre computation over
the pole gives: the pole divisor of `t` on the twisted surface is `5 · E'`, and every component of
the fibre has multiplicity `5` (`t ^ (-1) = s ^ 5 · unit` for a local equation `s` of `E'`), so
`v t = (v s ^ (-1)) ^ 5`.  Isolating it separates the valuation bookkeeping (proved here) from the
geometry of the twist (the local chapter of `Work.MotV5.RigAS.bridge_twist`). -/
theorem fifthPowAtPoles_of_poleFifthPower {𝕜 F : Type*} [Field 𝕜] [CharP 𝕜 5] [Field F] [Algebra 𝕜 F]
    [Algebra (RatFunc 𝕜) F] [IsScalarTower 𝕜 (RatFunc 𝕜) F]
    (hP : ∀ v : Valuation F (WithZero (Multiplicative ℤ)), Work.MotV.TrivOn 𝕜 v →
      1 < v (algebraMap (RatFunc 𝕜) F RatFunc.X) →
      ∃ s : F, v (algebraMap (RatFunc 𝕜) F RatFunc.X) = v s ^ 5)
    (g : RatFunc 𝕜) (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (v : Valuation F (WithZero (Multiplicative ℤ))) (hv : Work.MotV.TrivOn 𝕜 v)
    (hvt : 1 < v (algebraMap (RatFunc 𝕜) F RatFunc.X)) :
    ∃ u : F, v (algebraMap (RatFunc 𝕜) F g) = v u ^ 5 := by
  rcases hg with hg | hg
  · subst hg
    rw [Work.MotV.fAS, map_add, map_pow]
    exact fifthPow_pow_three_add v (algebraMap (RatFunc 𝕜) F RatFunc.X) hvt (hP v hv hvt)
  · -- `2 • fAS 𝕜 = 2 * fAS 𝕜` and `2` is a unit at `v` because `𝕜` has characteristic `5`
    have h2 : algebraMap (RatFunc 𝕜) F (2 : RatFunc 𝕜) = algebraMap 𝕜 F (2 : 𝕜) := by
      rw [show (2 : RatFunc 𝕜) = algebraMap 𝕜 (RatFunc 𝕜) (2 : 𝕜) from (map_ofNat _ 2).symm]
      exact (IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) F (2 : 𝕜)).symm
    have h20 : (2 : 𝕜) ≠ 0 := by
      intro hzero
      have h5 := (CharP.cast_eq_zero_iff 𝕜 5 2).mp hzero
      norm_num at h5
    have hv2 : v (algebraMap (RatFunc 𝕜) F (2 : RatFunc 𝕜)) = 1 := by
      rw [h2]
      exact hv 2 h20
    have hdecomp : algebraMap (RatFunc 𝕜) F (2 • Work.MotV.fAS 𝕜)
        = algebraMap (RatFunc 𝕜) F (2 : RatFunc 𝕜)
          * (algebraMap (RatFunc 𝕜) F RatFunc.X ^ 3 + algebraMap (RatFunc 𝕜) F RatFunc.X) := by
      rw [show (2 : ℕ) • Work.MotV.fAS 𝕜 = (2 : RatFunc 𝕜) * Work.MotV.fAS 𝕜 by
        rw [nsmul_eq_mul, Nat.cast_ofNat]]
      rw [Work.MotV.fAS, map_mul, map_add, map_pow]
    subst hg
    rw [hdecomp]
    exact fifthPow_const_mul_pow_three_add v _ _ hv2 hvt (hP v hv hvt)

section PoleFibre

/-- **The `PoleFibre` interface: the pole divisor of `t` comes with multiplicity `5`.**

For a field `F` with a parameter `t` (in the application `F = asTwistFieldTrue D g τ σS` and `t` the
image of `RatFunc.X`), `PoleFibre 𝕜 F t` records the *local* form of the fibre computation over the
pole: at every place `v` of `F` above the pole of `t` there is an element `s` of `F` — the equation
of the pole divisor at the centre of `v`, read in the function field — for which `t * s ^ 5` is a
**unit**.

This is precisely the "multiplicity `5`" content of `div(t) = E₀ - 5 · E' (pole divisor `5 E'`, zero divisor `E₀`)` on the quotient surface
`(C_L × E)/⟨σ'⟩`: the scheme-theoretic fibre `V(t⁻¹)` is `5 · E'`, so locally `t⁻¹ = s ^ 5 · unit`
for a local equation `s` of `E'`, i.e. `t · s ^ 5 = unit⁻¹`.  Equivalently, the pole order of `t` at
every place above the pole is divisible by `5`.

The interface deliberately allows the witness `s` to depend on the place: a *global* `s` with
`div(s) = E' - D` would require the pole fibre `E'` to be a principal divisor on the twist surface,
which is not the case (only `5 E' ∼ E₀` is principal, via `t`); the local equation exists place by
place, which is exactly what the local computation produces. -/
def PoleFibre (𝕜 F : Type*) [Field 𝕜] [Field F] [Algebra 𝕜 F] (t : F) : Prop :=
  ∀ v : Valuation F (WithZero (Multiplicative ℤ)), Work.MotV.TrivOn 𝕜 v → 1 < v t →
    ∃ s : F, v (t * s ^ 5) = 1

/-- **The `PoleFibre` datum computes the pole order as a fifth power.**  If `t * s ^ 5` is a unit at
`v` then `v t = (v s⁻¹) ^ 5`: the pole order of `t` at `v` is five times the order of `s⁻¹`.  In
particular `5 ∣ [Γ_v : ⟨v t⟩]`, i.e. the pole order of `t` at `v` is divisible by `5`. -/
theorem PoleFibre.fifthPow {𝕜 F : Type*} [Field 𝕜] [Field F] [Algebra 𝕜 F] {t : F}
    (h : PoleFibre 𝕜 F t) (v : Valuation F (WithZero (Multiplicative ℤ)))
    (hv : Work.MotV.TrivOn 𝕜 v) (hvt : 1 < v t) : ∃ u : F, v t = v u ^ 5 := by
  obtain ⟨s, hs⟩ := h v hv hvt
  refine ⟨s⁻¹, ?_⟩
  have hsplit : v (t * s ^ 5) = v t * v s ^ 5 := by
    rw [Valuation.map_mul, Valuation.map_pow]
  have hprod : v t * v s ^ 5 = 1 := by rw [← hsplit]; exact hs
  have hvt' : v t = (v s ^ 5)⁻¹ := eq_inv_of_mul_eq_one_left hprod
  rw [hvt', Valuation.map_inv, inv_pow]

/-- **The assembly: `PoleFibre` for `(F, t)` implies the conclusion of `fifthPowAtPoles_AS`.**  This
reduces the requested theorem to the geometric `PoleFibre` datum for the twist field, whose proof is
the fibre computation over the pole (model, pole divisor, multiplicity `5`). -/
theorem fifthPowAtPoles_of_poleFibre {𝕜 F : Type*} [Field 𝕜] [CharP 𝕜 5] [Field F] [Algebra 𝕜 F]
    [Algebra (RatFunc 𝕜) F] [IsScalarTower 𝕜 (RatFunc 𝕜) F]
    (h : PoleFibre 𝕜 F (algebraMap (RatFunc 𝕜) F RatFunc.X))
    (g : RatFunc 𝕜) (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (v : Valuation F (WithZero (Multiplicative ℤ))) (hv : Work.MotV.TrivOn 𝕜 v)
    (hvt : 1 < v (algebraMap (RatFunc 𝕜) F RatFunc.X)) :
    ∃ u : F, v (algebraMap (RatFunc 𝕜) F g) = v u ^ 5 :=
  fifthPowAtPoles_of_poleFifthPower
    (fun v hv hvt => PoleFibre.fifthPow h v hv hvt) g hg v hv hvt

end PoleFibre

/-- **The fibre of the Artin–Schreier twist over the pole of `t`** (the necessary condition of node
BR_AS, isolated after two provers refused the congruence version).  For `g = fAS 𝕜` or
`g = 2 • fAS 𝕜`, at every valuation `v` of the twist field `F = asTwistFieldTrue D g τ σS` which is
trivial on `𝕜` and at which `t = RatFunc.X` has a pole (`1 < v t`; values in
`WithZero (Multiplicative ℤ)`, `1 < ·` = a pole), the value of `g` is a **fifth power** of the value
group: `∃ u ∈ F, v g = v u ^ 5`.

Equivalently: for every place `P` of `F` above the pole `∞` of `t`, the pole order of `t` at `P` is
divisible by `5` — the twist is *totally ramified* over the pole of `t` (`e(P/∞) = 5`).  Since
`v g = (v t) ^ 3`, the statement is exactly `5 | ord_P(t)`.

This is the **decision point of the whole characteristic-`5` branch**: it is the necessary condition
of `Work.MotV5.Nodes.bridge_AS` (in characteristic `5`, `v (u⁵ - u)` is `1` or `v u ^ 5`, so if
`v g` is not a fifth power at `v` then no `u` makes `g - ℘u` integral there), and the constants-only
node consumes it through `Work.MotV5.asHyp_of_ASUnramified` and `Work.MotV5.hurwitz_AS_ratFunc`.

**Route.**  `F` is the function field of the quotient surface `(C_L × E)/⟨(σ', T)⟩` where `σ'` acts
on the `E`-factor by translation by the fifth-torsion point `T` (`σS` is pinned down by `ShiftOf`
plus `KleinData.Generates`: any two automorphisms agreeing on the `κ_i/κ_0` agree everywhere), and a
nonzero translation of an elliptic curve is free.  Hence the fibre over `t = ∞` is the free quotient
of `5 · (P_∞ × E)`, so every component of the fibre has multiplicity `5`: `ord_P(t) = 5 · ord_P(π)`
for the relevant uniformizers and `5 | ord_P(t)` as required.  For the canonical datum `D` of
`Work.MotV5.exists_kleinData_shiftProj` (`D11 : y² - y = x³ - x²`, `T = (0,0)`) the fibre can be
computed explicitly; the point/non-divisorial valuations are covered because the pole divisor of `t`
and its zero divisor are distinct fibres of a proper model.  If the statement fails for some
valuation `v` with `1 < v t`, report `v` (with `ord_v(t)`) — it is a counterexample to `BR_AS` as
well and the corrected mathematics for the branch.

**State of the proof (this file).**  The *arithmetic* half is proved: `fifthPow_pow_three_add`,
`fifthPow_const_mul_pow_three_add` and the assembly `fifthPowAtPoles_of_poleFifthPower` show that the
theorem follows from the single *geometric* input `hP : ∀ v, TrivOn 𝕜 v → 1 < v t →
∃ s, v t = (v s) ^ 5`.  They also show that the statement is *equivalent* (for `g = t³ + t`) to the
divisibility `5 ∣ [Γ_v : ⟨v t⟩]`, i.e. to the pole order of `t` at `v` being divisible by `5`; no
value-group argument alone can replace the geometry.

The geometric input is true and is exactly the local chapter of `Work.MotV5.RigAS.bridge_twist`: on
the model `S = (C_L × E)/⟨σ'⟩` one computes `div(t) = 5·E' - E₀` (the pole divisor of `t` is the
image of `{∞_C} × E`, with multiplicity `5` since the quotient map `C_L × E → S` is étale of degree
`5` and `π_*π^* = 5`); consequently the *scheme-theoretic* fibre `V(t⁻¹) = 5·E'`, i.e. locally
`t⁻¹ = s ^ 5 · unit` for a local equation `s` of `E'` — because `π^*(t⁻¹) = z ^ 5 (unit)` and
`π^*(s) = z (unit)`, and pullback of ideals along the flat (étale) map `π` is injective.  A place
`P` with `v_P(t) > 1` has its centre on the pole divisor `E'` (above it `t` is a unit), so passing to
the local equation at that centre gives `v_P(t) = (v_P s⁻¹) ^ 5`, which is the input `hP`.  What is
missing is therefore not a mathematical step but the *formalisation of the surface model*: the
function field of the quotient by a finite group, divisors of a surface, the centre of a valuation on
a proper model, and the pullback of ideals along an étale morphism.  Closing the gap means building
(or importing) that chapter, not weakening the statement: the statement is `true`, and its truth is
equivalent to the non-splitness of the `Artin–Schreier` twist (a split twist `F ≅ K(E)` would make
the pole order of `t` equal to `1` at the divisorial places, and the necessary condition fail). -/
theorem fifthPowAtPoles_AS (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (hg : g = Work.MotV.fAS 𝕜 ∨ g = 2 • Work.MotV.fAS 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h : Work.MotV5.ASTwistData 𝕜 D g τ σS σ)
    (v : Valuation ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (WithZero (Multiplicative ℤ)))
    (hv : Work.MotV.TrivOn 𝕜 v)
    (hvt : 1 < v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) RatFunc.X)) :
    ∃ u : ↥(Work.MotV5.asTwistFieldTrue D g τ σS),
      v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) g) = v u ^ 5 := by
  -- At every place above the pole, `v (fAS 𝕜)` is a fifth power of the value group.  This is the
  -- `tp_as` route: the twist field carries a genuine twisted Klein point (the ratios of the
  -- interpolated coordinates `asTwCoord D g i / asTwCoord D g j₀` lie in `F` and form the Klein
  -- point `asCoord W y`), so the master valuation lemma `Work.MotV5.tp_as` applies and gives
  -- `v g = (v u) ^ 5` for the class `g`; the second class of the link is `2 • fAS 𝕜`, and the
  -- constant `2` is a unit at every place because `𝕜` has characteristic `5`.
  obtain ⟨u, -, hu⟩ :=
    Work.MotV5.Nodes.fifthPow_fAS_of_tp_as D g hD hg τ σS σ h v hv hvt
  rcases hg with hg | hg
  · subst hg
    exact ⟨u, hu⟩
  · have h2 : algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (2 : RatFunc 𝕜)
        = algebraMap 𝕜 ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (2 : 𝕜) := by
      rw [show (2 : RatFunc 𝕜) = algebraMap 𝕜 (RatFunc 𝕜) (2 : 𝕜) from (map_ofNat _ 2).symm]
      exact (IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) _ (2 : 𝕜)).symm
    have h20 : (2 : 𝕜) ≠ 0 := by
      intro hzero
      have h5 := (CharP.cast_eq_zero_iff 𝕜 5 2).mp hzero
      norm_num at h5
    have hv2 : v (algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
        (2 : RatFunc 𝕜)) = 1 := by
      rw [h2]
      exact hv 2 h20
    have hdecomp : algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS)
          (2 • Work.MotV.fAS 𝕜)
        = algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (2 : RatFunc 𝕜)
          * algebraMap (RatFunc 𝕜) ↥(Work.MotV5.asTwistFieldTrue D g τ σS) (Work.MotV.fAS 𝕜) := by
      rw [show (2 : ℕ) • Work.MotV.fAS 𝕜 = (2 : RatFunc 𝕜) * Work.MotV.fAS 𝕜 by
        rw [nsmul_eq_mul, Nat.cast_ofNat]]
      rw [map_mul]
    subst hg
    rw [hdecomp, Valuation.map_mul, hv2, one_mul]
    exact ⟨u, hu⟩

end Work.MotV5.Nodes
