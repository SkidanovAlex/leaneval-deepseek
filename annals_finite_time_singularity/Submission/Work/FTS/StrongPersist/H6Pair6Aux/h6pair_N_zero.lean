/-
# `Work.FTS.StrongPersist.H6Pair6Aux.h6pair_N_zero` — audit of the delegated statement,
the route, and the state of the proof

**Owner of the note: the agent assigned `Submission/Work/FTS/StrongPersist/H6Pair6Aux/h6pair_N_zero.lean`.**
The statement is kept **byte-for-byte** below (it is the interface the requester consumes, e.g. for
`h6pair_mod`/`muDyn`).  This note records what the statement needs, what is available, and the
state of the three pieces that have been delegated.  Please read it before touching the file.

## 1. What the statement asks

For `α` in `(0,α₂]`, `f` with `H6Adm α f`, `HkMem α 7 f`, `Xn α f ≤ M`, and a split elliptic
context `Ell6Ctx α Ce Cs E Φs f Ψ` (i.e. `StarPkgo2 α Cs Φs`, `EllPkgK α 6 Ce f (E f)` and
`Ψ = Φs + E f`), it asks

  `|L₁₂(N α (F_* + f) Ψ)(0)| ≤ K α^{-9} (1+M)^4`

with a constant `K` that may depend on `Ce` but **not** on `Cs`, `α`, `M`, `f`, `Φs`, `E`.

Two structural facts drive everything.

* `N α F Φ = L_F(Ξ) + M_F`, where `Ξ := PhiTil α F Φ = Φ - Θ α F`,
  `L_F(Ξ) = 2 Rop α Ξ · F - 2 Uop α Ξ · ∂_θF - 2α Vop Ξ · D_zF` is **linear** in `Ξ`,
  `M_F = -(1/2) sin 2θ · FK F · ∂_θF - sin²θ · FK F · F` is independent of `Φ`, and `Θ α`,
  `L₁₂`, `FK`, `Rop`, `Uop`, `Vop` are all additive in the profile; hence splitting
  `F = F_* + f` and `Ψ = Φs + E f` (both provided by the context) gives
  `N α (F_*+f) (Φs+E f) = L_{F_*+f}(Ξs) + L_{F_*+f}(Ξg) + M_{F_*+f}` with
  `Ξs := PhiTs α Φs = Φs - Θ α (F_*)` (the star residual) and
  `Ξg := PhiTil α f (E f)` (the perturbation residual).
* `|L₁₂ g 0| ≤ Fa g := ∫_0^∞ r⁻¹ ∫_θ |K θ · g(r,θ)| dθ dr` (the `rl¹`-density, the route used by
  the *proved* level-four row `Work.FTS.NonlinRows.Rrl1`).  The `ℋ⁰`-route
  (`|L₁₂ g 0| ≤ C |g|_{ℋ⁰}`, `L3Rhs.L3RhsL12zero`) is **not** available here, because neither
  `Ξs` (which behaves like `z · sin 2θ` at the axis) nor `N` itself is `HkMem α 0`.

## 2. The obstruction the statement contains (and why the hypothesis matters)

The only quantitative link between `Ψ` and `f` in `Ell6Ctx` is
`HkNorm α 6 (Rop/Uop/Vop of Ξ) ≤ Ce · HkNorm α 6 f`.  In particular

* `HkNorm α 6 f` is **unbounded** on `{f | H6Adm α f ∧ HkNorm α 4 f ≤ M}`: the bump family
  `A φ((z-1)/ε) ψ(θ)` with `∫_θ K ψ = 0` (so `L₁₂ f ≡ 0` and `FK f ≡ 0`) keeps `HkNorm α 4 f ≍ M`
  (take `A = M ε^{7/2}`) while `HkNorm α 6 f ≍ M ε^{-2} → ∞`; all the `H6Adm`/`HkMem α 7 f` fields
  hold along it.  Consequently no bound in terms of `M` alone can be obtained by any argument that
  passes through the *pricing* `HkNorm α 6 (slot) ≤ Ce HkNorm α 6 f`.
* To reach the conclusion one must therefore bound `Ξ = Ξs + Ξg` at order `≤ 1` — equivalently,
  one must obtain the elliptic *pricing* at level `≤ 2` — and this is exactly the missing
  ingredient recorded in `H6Pair6Aux/NOTES_resid_pointwise.md` §2/§4 (and in
  `NOTES_H6Pair6.md` §4): the interface `Ell6Ctx`/`EllPkgK α 6` prices the residual only in `ℋ⁶`,
  and `EllPkgK α 6 ⟹ EllWeakPos` is **not** derivable (the `D_θ`-granularity of `HkIntegrand`
  always carries an extra `sin 2θ`, while `EllWeakPos` needs the *naive* `∂_θθ`-honesty).  The
  sibling statement of exactly this shape, `Work.FTS.EllSol.ellPkgK_transfer`, has been
  **machine-refuted** in this workspace (`EllSol/NOTES_ellPkgK_transfer_FALSE.md`, family
  `cex N = z^{-N} sin 2θ`).  Two independent reviews of the natural intermediate claim
  (`H6Pair6Aux/honestyTransfer_level0`) likewise returned explicit counterexamples
  (`z^{3/2}`-type boundary layers; `z^{-3/α}/cos θ`), both of the "missing hypothesis" type.

**Conclusion of the audit:** the *conclusion* is true for the constructed (honest) elliptic
solution — the paper's own estimate gives `|L₁₂(N)(0)| ≤ C(Xn₄)` with a universal constant, and the
narrow-bump, `θ`-oscillation and endpoint families all give values `→ 0` — but it is **not
derivable from the stated hypothesis**; the hypothesis needs the level-`≤2` (pointwise)
pricing of `Rop/Uop/Vop(PhiTil α f Ψ)`, i.e. the strengthening recommended in `NOTES_H6Pair6.md`
§4.  This is the same diagnosis as for `resid_pointwise`, whose statement the requester kept
"byte-for-byte (as required)".

## 3. The route implemented here (level `0`, using the *proved* `EllWeak0`)

The following chain is the one that closes, and it needs **one** non-trivial new input, the bridge
`EllPkgK α 6 Ce f Ψ (+ H6Adm α f, HkMem α 7 f) ⟹ EllWeakPos α 0 (orthSource f) (shiftSing α f Ψ)`:

1. `bslOp α (shiftSing α f Ψ) = orthSource f` and (because `H6Adm.l12 : L₁₂ f 0 = 0`)
   `shiftSing α f Ψ = Ξg + Gbar α f · sin 2θ` with `Gbar` explicit and `Gbar α f (0) = 0`;
   `HkMem α 7 f` also gives `HkMem α 0 (orthSource f)`.
2. `Work.FTS.EllipticEst.Mine.EllWeak0_exists` (**proved**): for `EllWeakPos α 0 F Ψ'`,
   `α⁴|z²∂_zzΨ'|²_{ℋ⁰} + |∂_θθΨ'|²_{ℋ⁰} ≤ C |F|²_{ℋ⁰}`.
3. `.../ellWeakPos_poincare_level0` (**delegated**): `|Ψ'|_{ℋ⁰}, |∂_θΨ'|_{ℋ⁰} ≤ C |∂_θθΨ'|_{ℋ⁰}`
   for weak-class data, so `Ξg` and its first `θ`-derivative are controlled by
   `C (1 + |f|_{ℋ⁰})`, whence (with the transform identity
   `Y(z) = -(1/α) ∫_0^1 t^{3/α-1} A(tz) dt` for `A = Uop Ξ/s2 = -3Y - α D_zY`,
   `Y := Ξ/sin 2θ`, which controls the `D_z`-slots of `Ξg` by those of `A`) the residual fields
   `Rop/Uop/Vop(Ξg)` are bounded in `ℋ⁰` by `C α^{-p} (1+M)^q`.
4. The **star** part: `Ξs = PhiTs α Φs = Ycheck α Φs · sin 2θ · z/(1+z)` with
   `Ycheck α Φs = ((z+1)/z)(PhiTs α Φs / sin 2θ)`.  `StarPkgo2` prices its fields by `Cs α` with
   `Cs` **free**, so a `Cs`-free bound is needed; it is obtained from
   `Work.FTS.PhiStar.StarCore_inhabitant` (an explicit star solution with an explicit constant
   `Cs₀`) together with `.../starPkg_solution_unique` (**delegated**: any two `StarPkgo2`-solutions
   agree for `z > 0`), giving `|Rop PhiTs| ≤ C α z/(1+z)`, `|Vop PhiTs| ≤ Cα`, `|Uop PhiTs/s2| ≤ Cα`.
5. `Fa`-assembly: `|L₁₂(N)(0)| ≤ Fa(N)`; the star pieces are bounded *pointwise* (step 4) and the
   perturbation pieces by Cauchy–Schwarz in `θ` (using step 3) and in `r` against
   `∫ r⁻¹`, each against the `f`-data `|f|_{ℋ⁴} ≤ M`; the `M_F`-pieces involve only `FK F_*`, `FK f`
   and are elementary.  Summing gives `|L₁₂(N)(0)| ≤ K(Ce) α^{-9} (1+M)⁴`.

## 4. State of the three delegated pieces (do not re-delegate)

| piece | file | verdict of the reviews |
|---|---|---|
| `ellWeakPos_shift_of_ellPkgK` (the bridge, with the source's `ℋ⁰`-honesty added as a hypothesis) | `Submission/Work/FTS/StrongPersist/H6Pair6Aux/ellWeakPos_shift_of_ellPkgK.lean` | reviews of the version *without* the source honesty: both "probably wrong (missing hypothesis)"; the version requested here adds `HkMem α 0 (bslOp α (PhiTil α f Ψ))`, which in the application is explicit, `= f - (1/4)sin2θ(αD_z(FK(F_*+f)) + 5FK(F_*+f))` |
| `ellWeakPos_poincare_level0` | `.../ellWeakPos_poincare_level0.lean` | both "looks correct as stated" (route: `H2W.sliceEtaPoincare` + the endpoint limits from the a.e. moment conditions) |
| `starPkg_solution_unique` (conclusion restricted to `z > 0` after the review) | `.../starPkg_solution_unique.lean` | the `z = 0` version was refuted by both reviewers (`SmoothOpen` is open-quadrant only); the `z > 0` version is the real content |

If the bridge comes back **proved**, steps 3–5 above finish the statement.  If it comes back
**false/mis-stated**, then the hypothesis of *this* statement (like `resid_pointwise`) is too weak
and the requester must add the level-`≤2` pricing to `Ell6Ctx` (recommended form in
`NOTES_H6Pair6.md` §4) before the lemma can exist.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.Nonlinear.Pieces.rl1Bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- **From the `rl¹`-density to the value of `L₁₂` at `0`.**  If the density bound
`Fa g ≤ C` holds (`Fa g = ∫⁻_r r⁻¹ ∫⁻_θ |K θ · g(r,θ)|`, the form in which the *proved* level-four
row `Work.FTS.NonlinRows.Rrl1` bounds `L₁₂(N)(0)`), then `|L₁₂ g 0| ≤ C`.  This is the extraction
step of the `Fa`-route used in the note above. -/
theorem le_of_Fa_le (g : Work.FTS.Galerkin.Fn) {C : ℝ} (hC : 0 ≤ C)
    (h : Work.FTS.Nonlinear.Pieces.Fa g ≤ ENNReal.ofReal C) :
    |Work.Construction.L12 g 0| ≤ C := by
  have h1 : ENNReal.ofReal |Work.Construction.L12 g 0| ≤ ENNReal.ofReal C :=
    le_trans (Work.FTS.Nonlinear.Pieces.ofReal_L12_le g) h
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp h1

theorem h6pair_N_zero (Ce : ℝ) (hCe : 0 < Ce) : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f Ψ Φs : Work.FTS.Galerkin.Fn) (M Cs : ℝ)
      (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn),
      Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs f Ψ →
      |Work.Construction.L12 (Work.Construction.N α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) 0|
        ≤ K * α ^ (-(9 : ℝ)) * (1 + M) ^ 4 := by
  sorry

end Work.FTS.StrongPersist.H6Pair6Aux
