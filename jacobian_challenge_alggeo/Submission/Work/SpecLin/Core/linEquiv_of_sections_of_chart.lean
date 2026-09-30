/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Specialisation of linear equivalence, in an affine chart (core of `specLin`)

**The theorem.**  For a valuation ring `R` over the field `K`, a curve `C/K`, an affine open
chart `W ⊆ C` containing the images of two `n`-tuples of `R`-points `s`, `t` of `C`, and a
rational function `h` on `C_F` (`F = Frac R`) with
`div h = Σ_m [s_m] - Σ_m [t_m]` on `C_F`, the point divisors
`Σ_m [s̄_m]` and `Σ_m [t̄_m]` of the special fibres are linearly equivalent on `C_κ`
(`κ = R/m`).

## The proof, in the language of the chart

Write `A = Γ(C, W)`, `B = A ⊗_K R` (the coordinate ring of the "relative chart"
`W ×_K Spec R`), `P = m_R·B` (the prime of the generic point of the special fibre) and, for
each section `s_m`, `I_m = ker(B → R)` (the prime of the generic point of the section, where
`B → R` is the `R`-algebra evaluation at the section).

1. **The dictionary.**  `K(C_F) = Frac(B)`; the closed points of `W_F ⊆ C_F` correspond to the
   primes `I ⊂ B` with `I ∩ R = 0`, and the order of vanishing of `h` there is the valuation of
   `B_I`.  Consequently the hypothesis `div h = Σ_m [s_m] - Σ_m [t_m]` becomes

   `ord_I(h) = #{m : I = I_m} - #{m : I = J_m}`   for every prime `I ⊂ B` with `I ∩ R = 0`.

   (Similarly the closed points of `W_κ` correspond to the maximal ideals `N ⊂ B` containing
   `P`, and `ord_N` of a reduction is the valuation of `B_N/P B_N`.)

2. **Content normalisation.**  By `Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map`,
   every element of `B` is `c·b'` with `c ∈ R` and `b' ∉ P`; hence, after multiplying `h` by a
   suitable element of `F^*` (which does not change its divisor), `h = a/b` with `a, b ∈ B`
   both `∉ P`, so that `h ∈ B_P^×`.  Its reduction `h̄ := (a mod P)/(b mod P)` is a well defined
   non-zero element of `Frac(B/P) = K(C_κ)`.

3. **Unit argument (the crux).**  At a closed point `N` of the special fibre, let
   `f_m, g_m ∈ B_N` be local equations of `I_m B_N` resp. `J_m B_N` (which exist and are either
   `1` or a generator, by Nakayama: `Work.SpecLin.Content.isPrincipal_of_fg_of_cyclic_map_quotient`),
   and put `u := h·Π_m g_m/Π_m f_m`.  Then `u` is a unit at the generic point `P` of the special
   fibre and at every prime `I ⊆ N` of the generic fibre, while its divisor at the generic fibre
   is trivial, so `u ∈ O_{X,N}^×` and the same for `u⁻¹`; reducing modulo `P` gives
   `h̄ = ū·Π_m f̄_m/Π_m ḡ_m` with `ū ∈ O_{C_κ,N}^×`.

4. **Divisor.**  Since `f̄_m` is a uniformizer at `N` exactly when `N` is the specialisation of
   `s_m`, the previous point computes `ord_N(h̄)`; together with the degree argument
   (`deg h̄ = 0` and regularity outside the marked points) this gives `div h̄ = Σ_m [s̄_m] - Σ_m [t̄_m]`.

## Refinement of the route (see `NOTES_chart.md` in this directory)

The unit argument of step 3 is best carried out on the *model* `X = C ×_K Spec R` (defined in
this file as `curveModel C R`), whose generic fibre is `C_F` and whose special fibre is `C_κ`.
After the content normalisation, `h` is a *unit at the generic point of the special fibre*;
consequently `div_X(h)` has **no vertical component**, so that
`div_X(h) = Σ_m [Z_{s_m}] - Σ_m [Z_{t_m}]`, where `Z_{s_m}` is the closure of the generic fibre
of the section `s_m`.  Restricting to `X_κ` — and using that a section meets the special fibre in
a single reduced point (`B ⧸ (I_m ⊔ P) ≅ κ`) — gives `div_{X_κ}(h̄) = Σ_m [s̄_m] - Σ_m [t̄_m]`.

The *pointwise* form of step 3 suggested above, namely the "weighted crux"
`ord_N(ā) = Σ_{I ⊆ N, I ∩ R = 0} [κ(I):F]·val_I(a)` for a general `a ∈ B ∖ P`, should **not** be
attempted: it is equivalent to the statement that the `F`-degree of every horizontal curve in the
model equals its intersection number with the special fibre, which requires finiteness of
normalisations and is delicate for a non-Noetherian valuation ring `R`.  The model route above
avoids it because only the *section* ideals `I_m` (which are flat over `R`, with `B ⧸ I_m ≅ R`)
occur with a nonzero multiplicity.
-/
/- The chart algebra of the relative chart (the vocabulary `chartTensor`, `evChart`,
`sectionPrime`, `chartFibrePrime`, `rPt_map_fractionRing`, `rPt_map_residueField`, the `R`-model
`curveModel`, …) now lives in the upstream module `Core/chartVocab.lean`, so that it does not
have to be imported from the present module by the modules that carry the *proof* of the
affine-chart statement.  The declarations keep their names.
-/
import Mathlib
import Submission.Work.SpecLin.Core.chartVocab
import Submission.Work.SpecLin.Up.Core.chartSpecialisation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace Work.SpecLin.Core


/-- **Assembly step (special fibre).**  The special-fibre half of the target follows from the
same statement written with `RPt.map` along `R → R ⧸ m_R` (the form used by
`Work.SpecLin.Alt.chartCore`), by rewriting `RPt.map ... p` as `closedPt R ≫ p`. -/
theorem linEquiv_of_sections_of_chart_of_chartCore {K : Type u} [Field K]
    {C : Work.CurveBasics.Curve K} {n : ℕ} (R : Type u) [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra K R] (s t : Fin n → Work.SpecLin.CurvePt C R)
    (hcore : Work.SpecLin.LinEquiv C
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.RPt.map
        (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) (s m)))
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.RPt.map
        (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) (t m)))) :
    Work.SpecLin.LinEquiv C
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.closedPt R ≫ s m))
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.closedPt R ≫ t m)) := by
  simpa only [rPt_map_residueField] using hcore


open CategoryTheory Limits AlgebraicGeometry in
theorem linEquiv_of_sections_of_chart {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {n : ℕ} (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : IsAffineOpen W)
    (s t : Fin n → Work.SpecLin.CurvePt C R)
    (hs : ∀ m, Set.range (s m).left.base ⊆ (W : Set C.left))
    (ht : ∀ m, Set.range (t m).left.base ⊆ (W : Set C.left))
    (h : (C.baseChange (FractionRing R)).functionField) (hh : h ≠ 0)
    (hdiv : (C.baseChange (FractionRing R)).div h
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.genPt R ≫ s m))
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.genPt R ≫ t m))) :
    Work.SpecLin.LinEquiv C
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.closedPt R ≫ s m))
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.closedPt R ≫ t m)) :=
  -- `Work.SpecLin.Core.Up.chartSpecialisation` is the (*) literally identical statement
  -- proved in the module `Submission.Work.SpecLin.Up.Core.chartSpecialisation`, whose proof is
  -- carried out in the "Up" copy of the affine-chart machinery (see
  -- `Submission/Work/SpecLin/Up/`); that copy imports the chart vocabulary from
  -- `Core/chartVocab.lean` and therefore does not depend on the present module, which is where
  -- the vocabulary used to live.  (*) Apart from the namespace, its statement is *literally*
  -- the statement below, so the proof is the identity.
  Work.SpecLin.Core.Up.chartSpecialisation (K := K) (C := C) (n := n) R W hW s t hs ht h hh hdiv

end Work.SpecLin.Core


/-! ## Status (complete)

The theorem `linEquiv_of_sections_of_chart` of this file is **proved**; it rests only on
`propext`, `Classical.choice` and `Quot.sound`.

### What is in this file

* `linEquiv_of_sections_of_chart` — the target statement (this file is the module that *states*
  it, as requested);
* `linEquiv_of_sections_of_chart_of_chartCore` — the assembly step: the target follows from the
  same statement written with `RPt.map` along `R → R ⧸ m_R` (the form used by
  `Work.SpecLin.Alt.chartCore`), by rewriting `RPt.map … p` as `closedPt R ≫ p`.

Everything else that used to live here — the chart algebra (`chartTensor`, `evChart`,
`sectionPrime`, `chartFibrePrime`, `chartFibreQuotEquiv`, `sectionPrimeQuotEquiv`,
`isDomain_chartTensor`, `exists_smul_notMem_chartFibrePrime`), the fibre rewrites
(`rPt_map_fractionRing`, `rPt_map_residueField`) and the `R`-model (`curveModel`, …) — has been
moved, with *unchanged names*, to the upstream module
`Submission.Work.SpecLin.Core.chartVocab.lean`.

### Why the vocabulary had to move, and how the target is proved

The mathematical content of the target (the specialisation of linear equivalence over a valuation
ring, via content normalisation, the local unit argument and the point/order dictionary) is proved
in this workspace in `Submission.Work.SpecLin.Core.chartSpecialisation`
(`Work.SpecLin.Core.chartSpecialisation`), an assembly of about thirty auxiliary modules
(`Alt/chartMap`, `Alt/chartReading`, `Alt.exists_normalized_chartTensorMap`,
`Core.cruxUnitAtMaximal`, `Core.orderDataSectionEquation`, `Setup.localOrderData`, …).

Before the vocabulary was moved, all of those modules imported it *from this file*: this file
could then not import them, and no proof carried out in them could reach this file's statement —
a module cannot import a module that imports it.  With the chart vocabulary upstream in
`Core/chartVocab.lean`, those modules (and the assembly `chartSpecialisation`) are mirrored —
verbatim, up to a `namespace Up` inserted directly inside their own namespace and to rewritten
references — in `Submission/Work/SpecLin/Up/`.  The mirror imports the vocabulary from
`Core/chartVocab.lean` and therefore does **not** import this file.  Its assembly is
`Work.SpecLin.Core.Up.chartSpecialisation`
(module `Submission.Work.SpecLin.Up.Core.chartSpecialisation`), whose *statement is literally the
statement of the target*: it mentions only `CurvePt`, `genPt`, `closedPt`, `ptDiv`, `LinEquiv`,
`div` and `functionField`, none of which lives in the mirror (they are upstream of it).  The
target is therefore the identity applied to it.

The modules that need the vocabulary keep importing it *from this module*, which obtains it from
`Core/chartVocab.lean`, so nothing downstream of this file changes.

### Mathematical warnings (unchanged)

Do **not** try to prove the "weighted crux"
`ord_N(ā) = Σ_{I ⊆ N, I ∩ R = 0} [κ(I):F]·val_I(a)` for a general `a ∈ B ∖ P`: it is equivalent
to the statement that the `F`-degree of every horizontal curve in the `R`-model equals its
intersection number with the special fibre, which needs finiteness of normalisations and can fail
for a non-Noetherian valuation ring `R`.  The successful route instead uses that `h` (after
content normalisation) is a *unit at the generic point of the special fibre*.
-/


