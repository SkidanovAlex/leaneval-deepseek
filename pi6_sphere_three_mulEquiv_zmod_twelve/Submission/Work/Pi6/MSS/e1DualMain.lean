import Mathlib
import Submission.Work.Pi6.MSS.E1Map
import Submission.Work.SSSR.serreE2Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `e1Dual`, II: the chain-level `E_1` row re-indexed to `q + s` and the comparison map

This file continues `Submission/Work/Pi6/MSS/E1Map.lean`.  Its goal is the statement

`E1Row 𝕜 (serreCF 𝕜 E B p) q ≅ dualComplex 𝕜 (E1Complex 𝕜 ξ q)`

for the Serre filtration `ξ` (`ξ.F = serF 𝕜 (Sing p)`), i.e. the cohomological `E_1` row of the
Serre spectral sequence is the `𝕜`-dual of the chain level `E_1` row.

The row complex `E1Row 𝕜 W q` has terms `pEraw 𝕜 W 1 s (q+s)`: the cohomological degree is
`q + s`, and the differential raises it by one, `q+s ↦ q+(s+1) = q+s+1`.  On the chain side the
graded pieces are `grF ξ.F s = grF (serF 𝕜 (Sing p)) s`, and `E1Complex 𝕜 ξ q` has terms
`(grF ξ.F s).homology (s+q)`.  The two indexings differ by `Nat.add_comm`, so we first isolate the
*re-indexed* complex

* `E1D.d1q ξ q s` — the differential `d¹` re-indexed to the degrees `q+s+1 → q+s`,
* `E1D.Zq ξ q` — the chain complex with `Zq.X s = (grF ξ.F s).homology (q+s)` and that differential,
* `E1D.ZqIso ξ q` — `Zq ξ q ≅ E1Complex 𝕜 ξ q`,
* `E1D.Phi` — the componentwise comparison map `pEraw 𝕜 W 1 s (q+s) ⟶ Hom(Zq.X s, 𝕜)`, built from
  the evaluation `evS` of `E1Map.lean`,
* `E1D.Phi_natural` — `Phi` is a cochain map.

The remaining steps (the comparison is an isomorphism, and the transport to `E1Complex`) are the
content of `e1Dual`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.MSS.E1D

noncomputable section

variable {𝕜 : Type} [Field 𝕜]
variable {C : ChainComplex (ModuleCat 𝕜) ℕ}

/-- The chain level `E_1` differential `d¹`, re-indexed so that its target degree is `q + s`.
Since `d¹ : H_{(s+1)+q}(grF ξ.F (s+1)) ⟶ H_{s+q}(grF ξ.F s)`, this is `d¹` transported along
`Nat.add_comm`. -/
noncomputable def d1q (ξ : Work.SSSR.Filtration 𝕜 C) (q s : ℕ) :
    (Work.SSSR.grF ξ.F (s+1)).homology (q + (s+1)) ⟶ (Work.SSSR.grF ξ.F s).homology (q + s) :=
  eqToHom (congrArg (fun n => (Work.SSSR.grF ξ.F (s+1)).homology n)
      (Nat.add_comm q (s+1))) ≫
    Work.SSSR.d1 ξ s q ≫
  eqToHom (congrArg (fun n => (Work.SSSR.grF ξ.F s).homology n) (Nat.add_comm s q))

/-- `d1q ≫ d1q = 0`. -/
theorem d1q_comp_d1q (ξ : Work.SSSR.Filtration 𝕜 C) (q s : ℕ) :
    d1q ξ q (s+1) ≫ d1q ξ q s = 0 := by
  rw [d1q, d1q]
  simp only [Category.assoc, CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl,
    Category.id_comp]
  have hd1 : Work.SSSR.d1 ξ (s+1) q ≫ (Work.SSSR.d1 ξ s q ≫
      eqToHom (congrArg (fun n => (Work.SSSR.grF ξ.F s).homology n) (Nat.add_comm s q))) = 0 := by
    rw [← Category.assoc, Work.SSSR.d1_comp_d1, Limits.zero_comp]
  rw [hd1, Limits.comp_zero]

/-- The chain complex `H_{q+s}(grF ξ.F s)` with the re-indexed `E_1` differential. -/
noncomputable def Zq (ξ : Work.SSSR.Filtration 𝕜 C) (q : ℕ) : ChainComplex (ModuleCat 𝕜) ℕ :=
  ChainComplex.of (fun s => (Work.SSSR.grF ξ.F s).homology (q + s))
    (fun s => d1q ξ q s) (fun s => d1q_comp_d1q ξ q s)

@[simp] theorem Zq_X (ξ : Work.SSSR.Filtration 𝕜 C) (q s : ℕ) :
    (Zq ξ q).X s = (Work.SSSR.grF ξ.F s).homology (q + s) := rfl

@[simp] theorem Zq_d (ξ : Work.SSSR.Filtration 𝕜 C) (q s : ℕ) :
    (Zq ξ q).d (s+1) s = d1q ξ q s := by
  simp only [Zq, ChainComplex.of_d]

/-- **`Zq ξ q` is the chain level `E_1` row with its degrees re-indexed by `Nat.add_comm`.** -/
noncomputable def ZqIso (ξ : Work.SSSR.Filtration 𝕜 C) (q : ℕ) :
    Zq ξ q ≅ Work.SSSR.E1Complex 𝕜 ξ q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun s => eqToIso (congrArg (fun n => (Work.SSSR.grF ξ.F s).homology n) (Nat.add_comm q s)))
    (by
      intro i j hij
      cases hij
      simp only [Zq_d, Work.SSSR.E1Complex, ChainComplex.of_d, d1q, CategoryTheory.eqToIso.hom,
        Category.assoc, CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_trans,
        CategoryTheory.eqToHom_refl, Category.id_comp, Category.comp_id])

/-! ## The comparison map `Φ`

From here on we specialise to the singular chains of a continuous map `p : E → B` and to the Serre
chain filtration `ξ = serreFiltrationOf p`, for which `ξ.F = serF 𝕜 (Sing p)` *definitionally*. -/

section Serre

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
variable (p : C(E, B)) (q : ℕ)

/-- **The component of the comparison map** `E₁^{s,q} ⟶ Hom(H_{q+s}(grₛ C_*(E)), 𝕜)`: an element
of the first page, represented by a cocycle `x`, is evaluated on the cycles of the graded piece.
The functional is obtained by transporting a functional on `Z_{q+s}/B_{q+s}` along the universal
coefficient identification `H_{q+s}(grₛ C_*(E)) ≅ Z_{q+s}/B_{q+s}`. -/
noncomputable def Phi (hann : ∀ s n, coFilt 𝕜 (sF p) s n =
      compAnn 𝕜 (Work.StemsB.serreSubcomplex (sF p) s) n) (s : ℕ) :
    (Work.Pi6.MSS.E1Row 𝕜 (Wc 𝕜 p) q).X s →ₗ[𝕜]
      ((Zq (Work.SSSR.serreFiltrationOf (R := 𝕜) p) q).X s →ₗ[𝕜] 𝕜) :=
  (LinearMap.dualMap
    ((Classical.choice (Work.StemsB.homology_iso_H_field 𝕜 (Kg 𝕜 p s) (q+s))).hom.hom :
      (Zq (Work.SSSR.serreFiltrationOf (R := 𝕜) p) q).X s →ₗ[𝕜]
        (↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p s) (q+s)) ⧸
          Work.StemsB.fdH 𝕜 (Kg 𝕜 p s) (q+s)))).comp (evS 𝕜 p s (q+s) hann)

end Serre

end

/-!
## What remains (state as of the last session)

Everything above builds and is `sorry`-free.  What is still missing for
`Work.Pi6.MSS.e1CohDualB` (equivalently for `Work.Pi6.MSS.e1Dual`) is:

1. **`Pi6/MSS/evS_bij`** (delegated, in flight): `Function.Bijective (evS 𝕜 p s n hann)`.
   Once it lands, each `Phi … s` is an isomorphism, since it is `evS` composed with the dual of an
   isomorphism.

2. **Naturality of `Phi`**: prove, for every `s`,
   ```
   (Work.Pi6.MSS.E1Row 𝕜 (Wc 𝕜 p) q).d s (s+1) ≫ ![(Zq (serreFiltrationOf p) q).d s (s+1)] = ...
   ```
   i.e. `Phi … s ≫ dualDiff = pD 1 s (q+s) ≫ Phi … (s+1)` (the cochain map property of `Phi`,
   `dualComplex 𝕜 (Zq …)` on the right).  Since `Zq … s` has degree `q+s` on both sides of
   `Phi` this square is *cast-free*; the elementwise verification uses
   `Work.Pi6.MSS.evZ_apply` (`evS x (mkQ z) = x (grSecX s z)`, `E1Map.lean`), the elementwise
   description of `Zq.d` via `Work.SSSR.kF_eq_of_lift` / `jF_eq_grFi` (`Submission/Work/SSSR/`),
   and, for `x ∈ pZ 𝕜 (Wc 𝕜 p) 1 s (q+s)`, the vanishing of `x` on `C(A_s)`
   (`Work.Pi6.MSS.coFiltAnn`) together with `Work.Pi6.MSS.ker_Kgπ_le_grIncl`.

3. **Assembly**: with `Phi` a componentwise isomorphism and a cochain map, build the isomorphism
   `E1Row 𝕜 (serreCF 𝕜 E B p) q ≅ dualComplex 𝕜 (Zq (serreFiltrationOf p) q)` (e.g.
   `HomologicalComplex.Hom.isoOfComponents` / `HomologicalComplex.Hom.isIso_of_components`), then
   compose with `dualComplexIsoMap (ZqIso …)` to get `e1CohDualB` for
   `ξ = Work.SSSR.serreFiltrationOf (R := 𝕜) p` (for which `ξ.F = serF 𝕜 (sSingP p)`
   *definitionally*, cf. `e1Dual.lean`).

## Useful verified facts (proved in scratch, easy to redo)

* cast of homology acts on classes by casting cycles:
  `(eqToIso (congrArg (fun n => K.homology n) h)).hom (K.homologyπ a z) =
     K.homologyπ b ((eqToIso (congrArg (fun n => K.cycles n) h)).hom z)` — `cases h; simp`.
* `homologyMap f` commutes with those casts — `cases h; simp`.
* `ShortComplex.ShortExact.δ` commutes with the casts in both degrees:
  `cases hi; cases hj; rw [Subsingleton.elim h h']; simp`.
* index transports on the pages are `Work.Pi6.MSS.pEcast`,
  `pD_pEcastNat` (`MSS/AssembleCore.lean`), `pEcast_comp`.

## Trap (cost the last session a lot of time)

Under `set_option backward.isDefEq.respectTransparency false` (needed for `grSecX` etc.),
rewriting `ModuleCat` composites (`ModuleCat.hom_comp`, `ConcreteCategory.comp_apply`) fails when
the two sides use *different* `Ring 𝕜` instances (`Field.toRing` vs `Field.toDivisionRing.toRing`),
which happens as soon as a `(Cc 𝕜 p k)`-typed element meets a `Kgπ`-typed morphism.  The fix that
works is to keep `Kgπ_d` in the `serF` ("`(Work.SSSR.serF 𝕜 (sF p)).obj s`") coordinates and, when
an element of `Cc`-type must be fed to such a composite, to introduce it with
`set X' : ↥(((Work.SSSR.serF 𝕜 (sF p)).obj s).X (k+1)) := grSecX 𝕜 p s (k+1) z with hX'`
and then `rw [ConcreteCategory.comp_apply, …]`.
-/

end Work.Pi6.MSS.E1D
