import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.CDT.SympDescent
import Submission.CDT.ZagierHBC
import Submission.Work.C7.seven_setup
import Submission.Work.A14D.H_cont
import Submission.Work.A14D.exists_Y9
import Submission.Work.A14D.kappa_jump_sol
import Submission.Work.A14D.kappa_jump_nnz
import Submission.Work.A14D.relation_to_LC_A
import Submission.Work.A14D.lc_implies_zero

/-! Guidance from the project lead (the requester):

# Area A14 — Lemma `14functions` (`Fourteen`, InterfacesA2), assuming `LemmaSeven` (proved: Work.C7)
Paper: REFS/L2chi.tex §"Functional Linear Independence" (7883–8268): Lemma `14functions`, its proof
and Remark `whyisthistrue`. The prior run formalized the ALGEBRAIC finish: `Submission/CDT/
RelationToSystem.lean` (`system_of_relation`, `relation_trivial`, `linearIndependent_seven`,
`no_relation_const`, all axiom-clean) and `FinalLinear.lean` (`no_solution`), abstractly over a module
with a derivation over ℂ(y), with hypothesis `hindep` (Δ, Δ', Δ'', Δ''' independent for a homogeneous
solution Δ of the order-4 ODE (explicitode), `GA_odeLHS`). What is missing is the ANALYTIC half:
producing Δ (monodromy: continue the relation around a singular point so that G ↦ G + κΔ, κ ≠ 0, with
all other functions returning to themselves up to known changes) and `hindep`.
WARNING: the Theorem-C x-side trick (compare singularities of P and P∘w at a point where only one is
singular) does NOT transfer directly: for H (radius 1 under the relation) both H and H∘w are singular at
x = 1. The lead is designing the analytic half in parallel and will message you a route; meanwhile
build the formal parts: pull a Q[y]-relation back to x, kill the integrals by ∂_y^{D+1}, reduce with the
order-2 Zagier ODE (x(1−x)(1−9x)H'' + (1−20x+27x²)H' + (9x−3)H = b + c/(1−x) — check the normalisation
in `Submission/CDT/ZagierHBC.lean` `HA_odeLHS`), and the adapter from the 14-list to the prior run's
abstract module setting. Also see Theorem C's analogous agent H50 (`Submission/Work/C17/`) for reusable
pieces (`riccati_no_rational`-style lemmas, pure-function x-side expressions, Pringsheim `Work.C17g`).
Contracts: `Submission/CDTPlan/InterfacesA2.lean` (Theorem A template), `InterfacesA.lean` (ψ_A, φ_A,
ANumerics, Zagier integrality), `InterfacesC.lean` (intY, tq, dY), `Interfaces.lean`.
The Theorem-C side has already solved the analogous pieces — REUSE, do not rebuild:
`Submission/Work/CPhi/` (lift of φ_C), `Submission/Work/CPull/` (germs.lean: `germ_of_even`,
`pullbackMero_of_germ`, `germ_intY`, `germ_tq`, pullbackMero_B2/B3/B4, deriv_phiC_zeros_finite),
`Submission/Work/CLift/` (continuation of P along Φ with OdeContinuation),
`Submission/Work/CDcl/` (symmetrised-powers route to the d/dy-closure), `Submission/Work/CDen/`.
Axiom-clean A-side facts: `Submission.Work.Purge.a_side_clean` bundles HA_ode, HB_ode, HC_ode,
GA_odeLHS_eq_zero, Cintegral/Aintegral identities, overconvergesB/C (use it instead of the
native_decide-tainted originals); `Work.ZagBI` re-proved HA_ode cleanly too. Never depend on
`native_decide` (check #print axioms).
-/


/-! ## 3. Glue for the assembly: the pure part of a relation

The assembly (see `Work.A14D`) reduces a putative relation `Σᵢ Pᵢ·fᵢ = 0` to: (i) the vanishing of
the four `G`-derivative coefficients and the three integral coefficients (the `Work.A14D` chain
`H_cont → exists_Y9 → kappa_ne_zero → relation_to_LC_A → lc_implies_zero`), and (ii) the vanishing
of the seven *pure* coefficients, which is `hS : LemmaSeven`.  Below: the index bookkeeping. -/

/-- The seven pure slots inside the fourteen-function list `B₁…B₅, G, …, B₆, B₇, ∫…`. -/
def pureIdx : Fin 7 → Fin 14 := ![0, 1, 2, 3, 4, 9, 10]

/-- The pure slots of `fourteen` are `pureB`. -/
theorem fourteen_pure (a b c : ℤ) (j : Fin 7) :
    Submission.CDTPlan.fourteen a b c (pureIdx j) = Submission.CDTPlan.pureB j := by
  fin_cases j <;> simp [pureIdx, Submission.CDTPlan.fourteen, Submission.CDTPlan.pureB]

theorem pureIdx_injective : Function.Injective pureIdx := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp [pureIdx] at h ⊢

/-- **The pure part of a relation.**  If a `ℚ[y]`-relation among the fourteen functions holds and
the coefficients of the four `G`-derivatives and of the three integrals vanish, then the remaining
relation among the seven pure functions holds (and is killed by `hS : LemmaSeven`). -/
theorem pure_part_zero (a b c : ℤ) (P : Fin 14 → Polynomial ℚ)
    (hP : ∑ i : Fin 14, (P i : PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c i = 0)
    (hG : ∀ k : Fin 4, P ⟨5 + (k : ℕ), by omega⟩ = 0)
    (hint : ∀ i : Fin 3, P ⟨11 + (i : ℕ), by omega⟩ = 0) :
    ∑ j : Fin 7, (P (pureIdx j) : PowerSeries ℚ) * Submission.CDTPlan.pureB j = 0 := by
  have hvan : ∀ i : Fin 14, (∀ j : Fin 7, pureIdx j ≠ i) →
      (P i : PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c i = 0 := by
    intro i hi
    fin_cases i
    · exact absurd rfl (hi 0)
    · exact absurd rfl (hi 1)
    · exact absurd rfl (hi 2)
    · exact absurd rfl (hi 3)
    · exact absurd rfl (hi 4)
    · exact mul_eq_zero.mpr (Or.inl (by simpa using hG 0))
    · exact mul_eq_zero.mpr (Or.inl (by simpa using hG 1))
    · exact mul_eq_zero.mpr (Or.inl (by simpa using hG 2))
    · exact mul_eq_zero.mpr (Or.inl (by simpa using hG 3))
    · exact absurd rfl (hi 5)
    · exact absurd rfl (hi 6)
    · exact mul_eq_zero.mpr (Or.inl (by simpa using hint 0))
    · exact mul_eq_zero.mpr (Or.inl (by simpa using hint 1))
    · exact mul_eq_zero.mpr (Or.inl (by simpa using hint 2))
  have h1 : (∑ i : Fin 14, (P i : PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c i)
      = ∑ i ∈ (Finset.univ.image pureIdx),
          (P i : PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c i := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    exact hvan x (fun j hj => hx (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩))
  have h2 : (∑ i ∈ (Finset.univ.image pureIdx),
        (P i : PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c i)
      = ∑ j : Fin 7, (P (pureIdx j) : PowerSeries ℚ)
          * Submission.CDTPlan.fourteen a b c (pureIdx j) := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact pureIdx_injective hxy
  rw [h1, h2] at hP
  simpa [fourteen_pure] using hP

/-!  # Route notes for `A14` (this file)

## The `x`-side set-up (formal; proved below)

* `HX a b c = ZagierH a b c` (`H = aH_A + bH_B + cH_C`) satisfies the *inhomogeneous* order-2
  equation `HA_odeLHS (HX a b c) = C b + C c·(1−X)⁻¹` (`functionsH_ode`, `HX_ode` below).
* `GX a b c = (GZ a b c) ∘ sympY`, and `sympSym_subst` gives
  `GX = HX + HX.subst sympPhi` (`GX_eq`): the symmetrisation is the *sum over the two branches*
  `H(x) + H(x/(x−1))`.
* Chain rule: `((∂_y G) ∘ y) · y' = ∂_x (G ∘ y)` (`deriv_GX`), so the `y`-derivatives of `G`
  pull back to `(ρ·∂_x)^k (H + H∘φ)` with `ρ = 1/y' = (x−1)²/(x²−2x)`.
* The *cleared* form of the order-2 equation (`HX_reduce2` below) expresses `x(1−x)(1−9x)·H''`
  through `H, H'` and the explicit inhomogeneity, i.e. reduces every higher `x`-derivative of `H`
  to the `ℚ(x)`-span of `{H, H', 1}`; the same reduction for the second branch is the
  `φ`-conjugate of this equation.

## What the analytic half has to show (status: OPEN)

Suppose `Σ_i P_i(y)·f_i(y) = 0` (`P_i ∈ ℚ[y]`, not all zero) for the fourteen functions
`f = fourteen a b c`.  Pulling back along `y ↦ y(x)` and reducing the `y`-derivatives with the two
order-2 equations gives an identity on the unit disc
  `(∗)  α·H + β·H' + γ·(H∘φ) + δ·(H∘φ)' + ε·1 + (pure part) = 0`,     `α,…,ε ∈ ℚ(x)`.
The route needs: (a) the *pure part* of `(∗)` to vanish (then `LemmaSeven` kills the pure
coefficients); (b) the *e-part* coefficients `α,β,γ,δ,ε` to vanish; (c) the *injectivity* of the
reduction (from `(∗)` back to `(P_i)`), i.e. the `A`-side analogue of `Work.C17I`'s
"ePart of ∂^{D+1}Λ = 0 ⟹ p = q = 0".

Available separations (under the absurd relation `ARel`, where `H` overconverges — radius `1`):

* at `y = 4` (`x = 2`) the pure functions have `√(y−4)`-branching while `G`, its derivatives,
  the three integrals *and* the rational coefficients are single-valued (`H` is analytic at
  `x = 2`, a regular point of the order-2 operator): the *odd part* of the relation therefore
  involves only the pure coefficients — this is the `A`-side analogue of the `C`-side's
  "acl at `x_s`" and it **kills the pure part**;
* at `x = 1` (the singularity of `H`) the pulled-back functions have expansions in powers of
  `log(1−x)`: `H` and `(H∘φ)'` have `log`-order `1`, `H` has a pole of order `≤ 3` when `c ≠ 0`
  (`A/t³ + B/t² + C/t + D log t + …` from the `c/(1−x)` inhomogeneity), `H∘φ` is bounded
  (`t·log t`), while the pure functions have `log`-orders up to `3` (`B₆∘y ∼ −log³t/6`) and pole
  order `1`; the `Λ_k`-functionals (coefficient of `log^k t`) at `x = 1` are therefore
  *local* for `k ≥ 1` and isolate first `B₆` (`Λ₃`), then `B₃, B₄, B₇` and the integrals (`Λ₂`).

The remaining difficulty (documented here so that the next session does not repeat it): the
`Λ_1`/`Λ_0` functionals at `x = 1` involve the *global* connection constants (the `log`-coefficient
`D` of `H` at `x = 1`, the analytic part of `Li₂`, `J`, and the period constants), and the paper's
own monodromy step is *vacuous* in the `ARel` case: under `ARel` the combination
`H = b(H_B − (L/2)H_A) + c(H_C − (ζ(2)/4)H_A)` is analytic at `x = 1/9`, so the monodromy of `G`
around `y = −1/72` is trivial, while around `y = 4` it is trivial because `Sym⁺` is even.
-/


namespace Work.A14

open PowerSeries
open scoped BigOperators

noncomputable section

/-- `H = a H_A + b H_B + c H_C` (the Theorem-A series, over `ℚ`). -/
abbrev HX (a b c : ℤ) : PowerSeries ℚ := Submission.CDTPlan.HZ a b c

/-- `G = Sym⁺ H`. -/
abbrev GX (a b c : ℤ) : PowerSeries ℚ := Submission.CDTPlan.GZ a b c

/-- The `x`-side pullback `G ∘ y`, `y = x²/(x−1)`. -/
noncomputable def GY (a b c : ℤ) : PowerSeries ℚ := (GX a b c).subst Submission.CDT.sympY

/-- The `x`-side pullback `H ∘ φ`, `φ = x/(x−1)`. -/
noncomputable def HP (a b c : ℤ) : PowerSeries ℚ := (HX a b c).subst Submission.CDT.sympPhi

/-- **The symmetrisation identity**: `(Sym⁺H) ∘ y = H + H ∘ φ`, i.e. `G ∘ y = H + H ∘ φ`. -/
theorem GY_eq (a b c : ℤ) : GY a b c = HX a b c + HP a b c := by
  unfold GY HP HX GX Submission.CDTPlan.GZ Submission.CDTPlan.HZ
  exact Submission.CDT.sympSym_subst _

/-- **The inhomogeneous order-2 equation** for `H`: the `x`-side normalisation of
`x(1−x)(1−9x)H'' + (1−20x+27x²)H' + (9x−3)H = b + c/(1−x)`. -/
theorem HX_ode (a b c : ℤ) :
    Submission.CDT.HA_odeLHS (HX a b c)
      = PowerSeries.C ((b : ℚ)) + PowerSeries.C ((c : ℚ)) * (1 - (PowerSeries.X : PowerSeries ℚ))⁻¹ :=
  Submission.CDT.functionsH_ode (a : ℚ) (b : ℚ) (c : ℚ)

/-- **Cleared form of the order-2 equation** (no division): the `H''`-coefficient times `H''`
is the explicit combination of `H`, `H'` and `b + c/(1−x)`.  This is the reduction step used by
every `x`-side argument: iterating it makes every higher `x`-derivative of `H` a `ℚ(x)`-linear
combination of `H`, `H'` and `1`. -/
theorem HX_reduce2 (a b c : ℤ) :
    (PowerSeries.X - PowerSeries.C 10 * PowerSeries.X ^ 2 + PowerSeries.C 9 * PowerSeries.X ^ 3)
        * (PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) (HX a b c)))
      = (PowerSeries.C ((b : ℚ)) + PowerSeries.C ((c : ℚ))
            * (1 - (PowerSeries.X : PowerSeries ℚ))⁻¹)
        - ((1 : PowerSeries ℚ) - PowerSeries.C 20 * PowerSeries.X + PowerSeries.C 27 * PowerSeries.X ^ 2)
            * PowerSeries.derivative (R := ℚ) (HX a b c)
        - (-PowerSeries.C 3 + PowerSeries.C 9 * PowerSeries.X) * HX a b c := by
  have h := HX_ode a b c
  rw [Submission.CDT.HA_odeLHS] at h
  linear_combination h

/-- **Chain rule for the pullback**: `((∂_y G) ∘ y)·y' = ∂_x (G ∘ y)`. -/
theorem deriv_GY (a b c : ℤ) :
    PowerSeries.derivative (R := ℚ) (GY a b c)
      = ((PowerSeries.derivative (R := ℚ) (GX a b c)).subst Submission.CDT.sympY)
        * (PowerSeries.derivative (R := ℚ) Submission.CDT.sympY) := by
  rw [GY]
  exact PowerSeries.derivative_subst Submission.CDT.sympY_hasSubst

/-- The pullbacks of the seven pure functions are `Work.C7.g`. -/
theorem pureB_subst (i : Fin 7) :
    (Submission.CDTPlan.pureB i).subst Submission.CDT.sympY = Work.C7.g i := rfl

end

end Work.A14

namespace Work.A14

open Submission.CDTPlan

/-- **Lemma `14functions`** (the `ℚ(y)`-linear independence of the paper's 14 functions).

`Fourteen` unfolds to: for all `a b c : ℤ` with `ARel a b c` and `b ≠ 0`,
`PolyIndependent (fourteen a b c)`.  Given a putative `ℚ[y]`-relation `Σᵢ Pᵢ·fᵢ = 0`:

* `H_cont` continues `H = HZ a b c` to the half-planes `SU`, `SL`;
* `exists_Y9` supplies the holomorphic solution `y9` of `LZ` at `1/9`;
* `kappa_jump_sol` produces the jump `D = HU - HL` on `Om1` together with its log-coefficients
  `κU`, `κL` at `1/9`, and `kappa_jump_nnz` shows `κU ≠ 0 ∨ κL ≠ 0` — this is the analytic crux
  that replaces the paper's (vacuous under `ARel`) y-side monodromy step;
* `relation_to_LC_A` transfers the relation to the `Λ`-equation `(LC)`, and cancelling the
  non-zero `κ` leaves `(LC) ≡ 0`;
* `lc_implies_zero` (the algebra of `Submission.CDT`/`Work.A14E`) then gives
  `P ⟨5+k⟩ = 0` and `P ⟨11+i⟩ = 0`;
* the remaining relation among the seven pure functions is killed by `hS : LemmaSeven`. -/
theorem fourteen_indep (hS : LemmaSeven) : Fourteen := by
  intro a b c hAR hb P hP
  obtain ⟨HU, HL, hHUd, hHLd, hHUode, hHLode, hHUag, hHLag⟩ := Work.A14D.H_cont a b c hAR
  obtain ⟨y9, δ, hY⟩ := Work.A14D.exists_Y9
  have hHU : DifferentiableOn ℂ HU Work.A14D.SU ∧
      (∀ z ∈ Work.A14D.SU, Work.A14D.LZ HU z = Work.A14D.rhsZ b c z) ∧
      ∀ z ∈ Work.A14D.SU ∩ Metric.ball 0 1, HU z = Work.A14D.Hfun a b c z :=
    ⟨hHUd, hHUode, hHUag⟩
  have hHL : DifferentiableOn ℂ HL Work.A14D.SL ∧
      (∀ z ∈ Work.A14D.SL, Work.A14D.LZ HL z = Work.A14D.rhsZ b c z) ∧
      ∀ z ∈ Work.A14D.SL ∩ Metric.ball 0 1, HL z = Work.A14D.Hfun a b c z :=
    ⟨hHLd, hHLode, hHLag⟩
  obtain ⟨D, hDd, hDode, hDj, κU, κL, hU, hL⟩ :=
    Work.A14D.kappa_jump_sol a b c hAR HU HL hHU hHL y9 δ hY
  have hκ : κU ≠ 0 ∨ κL ≠ 0 :=
    Work.A14D.kappa_jump_nnz a b c hAR hb HU HL hHU hHL y9 δ hY D hDd hDode hDj κU κL hU hL
  obtain ⟨J, hJd, hJ0, hJ', hLCκ⟩ :=
    Work.A14D.relation_to_LC_A a b c hAR P hP HU HL hHU hHL y9 δ hY D hDd hDode hDj κU κL hU hL
  have hLC : ∀ z ∈ Metric.ball Work.A14D.ninth δ,
      (∑ k : Fin 4, Work.A14D.pAtY (P ⟨5 + (k : ℕ), by omega⟩) z
          * Work.A14D.DyIter (k : ℕ) y9 z)
        + ∑ i : Fin 3, Work.A14D.pAtY (P ⟨11 + (i : ℕ), by omega⟩) z * J i z = 0 := by
    intro z hz
    rcases hκ with hk | hk
    · exact (mul_eq_zero.mp (hLCκ z hz).1).resolve_left hk
    · exact (mul_eq_zero.mp (hLCκ z hz).2).resolve_left hk
  obtain ⟨hGv, hintv⟩ := Work.A14D.lc_implies_zero hY (fun k => P ⟨5 + (k : ℕ), by omega⟩)
      (fun i => P ⟨11 + (i : ℕ), by omega⟩) J hJd hJ0 hJ' hLC
  have hG : ∀ k : Fin 4, P ⟨5 + (k : ℕ), by omega⟩ = 0 := fun k => congrFun hGv k
  have hint : ∀ i : Fin 3, P ⟨11 + (i : ℕ), by omega⟩ = 0 := fun i => congrFun hintv i
  have hpure : ∑ j : Fin 7, (P (pureIdx j) : PowerSeries ℚ) * Submission.CDTPlan.pureB j = 0 :=
    pure_part_zero a b c P hP hG hint
  have hpure0 : ∀ j : Fin 7, P (pureIdx j) = 0 := hS (fun j => P (pureIdx j)) hpure
  intro i
  fin_cases i
  · exact hpure0 0
  · exact hpure0 1
  · exact hpure0 2
  · exact hpure0 3
  · exact hpure0 4
  · exact hG 0
  · exact hG 1
  · exact hG 2
  · exact hG 3
  · exact hpure0 5
  · exact hpure0 6
  · exact hint 0
  · exact hint 1
  · exact hint 2

end Work.A14
