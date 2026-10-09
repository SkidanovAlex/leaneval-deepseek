/-
# `G1⁺`'s finite-half clauses, at a *fixed* level, from the proved local inputs

The finite-place half of `Work.SSGRoute.PT.canonical_localPairing_reciprocity_converse` (`G1⁺`) is

  `pair M (decomp k A) a b = χ L hKL (ι_w (levelPair f ι (βl a) [b]_L))`

at a level `L` chosen by `Classical.choose` (the choice depends on `b` only, never on `a`), and its
clauses (1)–(4) (`H1Pair.PairClauses`) are statements about `PT.finAtValue` — hence about
`PT.finAtLevel` at the chosen level.

This file proves the parts of the clause bundle that are **level-explicit**: they hold at *every*
fixed admissible level, with the given `b₀`/`hb₀` factorisation data.  Clause (1) is *already
level-free* because the level chosen by `PT.finAtValue` depends only on `b`: for
`a`, `a'`, `a + a'` the same `Classical.choose` is used, so the identity transfers verbatim.  The
other clauses additionally need level-independence (`CokerPT.finAtLevelFix_eq_of_le`; the PT lane's
`PT.finAtLevel_eq_of_le` is *false* as stated — `χ` must satisfy the inflation coherence of S1).

Proved here:

* `finAtLevel_add_left`  — clause (1): additivity in the first variable;
* `finAtLevel_add_right` — clause (2): additivity in the second variable;
* `finAtLevel_coboundary_left`  — clause (3): vanishing when the first variable is a coboundary;
* `finAtLevel_coboundary_right` — clause (3): vanishing when the second variable is a coboundary.

The `p`-torsion bookkeeping needed to apply `χ`'s additivity on `p`-torsion (S1) is discharged by
`iota_ptorsion` (`p • ι_w z = 0` for `p`-torsion `z`) together with the `nsmul`-compatibility of the
local dictionary `βl` (`local_ext_h1_bridge`): the cochain is pointwise `p`-torsion because `M` and
the coefficients `M^∨(1) = DualMod p (M ⊗ T)` are `ZMod p`-modules.
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.PT.g1plus_finHalf
import Submission.Work.SSGRoute.PT.g1plus_iota
import Submission.Work.SSGRoute.PT.levelPair_functoriality
import Submission.Work.SSGRoute.local_ext_h1_bridge
import Submission.Work.SSGRoute.CokerPT.LevelClass

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory SSGRoute SSGRoute.PTExt
open scoped TensorProduct

namespace Work.SSGRoute.PT

/-! ## `nsmul` compatibility and `p`-torsion of the pairing calculus -/

/-- In a `ZMod p`-module, `p • x = 0`. -/
theorem nsmul_eq_zero_of_zmod (p : ℕ) [Fact p.Prime] {M : Type} [AddCommGroup M]
    [Module (ZMod p) M] (x : M) : p • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self, zero_smul]

theorem isCocycleOn_nsmul {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (act : Γ →* G) (H : Subgroup Γ) (a : Γ → M) (n : ℕ)
    (ha : IsCocycleOn act H a) : IsCocycleOn act H (n • a) := by
  intro g hg h hh
  have haux : ∀ (γ : G) (k : ℕ) (x : M), γ • (k • x) = k • (γ • x) := fun γ k x =>
    AddMonoidHom.map_nsmul (AddMonoidHom.mk' (fun y => γ • y) (fun u v => smul_add γ u v)) k x
  simp only [Pi.smul_apply, ha g hg h hh]
  rw [smul_add, haux]

theorem isLocConstOn_nsmul {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M]
    (H : Subgroup Γ) (a : Γ → M) (n : ℕ) (ha : IsLocConstOn H a) :
    IsLocConstOn H (n • a) := by
  obtain ⟨U, hU, hfa⟩ := ha
  refine ⟨U, hU, fun g hg u hu hu' => ?_⟩
  show n • a (g * u) = n • a g
  rw [hfa g hg u hu hu']

/-- The localisation `extLoc` is `nsmul`-compatible. -/
theorem pt_extLoc_nsmul {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NK.GlobalCFT.Place K)
    {M : Rep.{0} Coeff Gal(K/k)} {r : ℕ} (n : ℕ)
    (x : Abelian.Ext M (idelesK k K) r) :
    extLoc w (n • x) = n • extLoc w x :=
  AddMonoidHom.map_nsmul
    { toFun := fun x => extLoc w x
      map_zero' := extLoc_zero k K w
      map_add' := fun x x' => extLoc_add k K w x x' } n x

/-- The class-group map `extToClasses` is `nsmul`-compatible. -/
theorem pt_extToClasses_nsmul {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] {M : Rep.{0} Coeff Gal(K/k)} {r : ℕ} (n : ℕ)
    (x : Abelian.Ext M (idelesK k K) r) :
    extToClasses (k := k) (K := K) (n • x) = n • extToClasses (k := k) (K := K) x :=
  AddMonoidHom.map_nsmul
    { toFun := fun x => extToClasses (k := k) (K := K) x
      map_zero' := extToClasses_zero k K
      map_add' := fun x x' => extToClasses_add k K x x' } n x

/-- The chosen orbit-supported idèle lift `iotaLift` is additive.  (Re-proved here: the `G1⁺` lane's
copy lives in a module this file does not depend on.) -/
theorem pt_iotaLift_add {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L) (z z' : extH (localUnitsK (k := k) (K := L) r) 2) :
    iotaLift (k := k) (L := L) r (z + z') =
      iotaLift (k := k) (L := L) r z + iotaLift (k := k) (L := L) r z' := by
  symm
  apply eq_iotaLift_of_spec
  · rw [extLoc_add, (iotaLift_spec (k := k) (L := L) r z).1,
      (iotaLift_spec (k := k) (L := L) r z').1]
    rfl
  · intro v hv
    rw [extLoc_add, (iotaLift_spec (k := k) (L := L) r z).2 v hv,
      (iotaLift_spec (k := k) (L := L) r z').2 v hv, add_zero]

/-- The chosen orbit-supported idèle lift `iotaLift` is `nsmul`-compatible. -/
theorem pt_iotaLift_nsmul {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L) (n : ℕ)
    (z : extH (localUnitsK (k := k) (K := L) r) 2) :
    iotaLift (k := k) (L := L) r (n • z) = n • iotaLift (k := k) (L := L) r z := by
  symm
  apply eq_iotaLift_of_spec
  · rw [pt_extLoc_nsmul, (iotaLift_spec (k := k) (L := L) r z).1]
    rfl
  · intro v hv
    rw [pt_extLoc_nsmul, (iotaLift_spec (k := k) (L := L) r z).2 v hv, smul_zero]

/-- The orbit-placement map `ι_w` is additive. -/
theorem pt_iota_add {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L) (z z' : extH (localUnitsK (k := k) (K := L) r) 2) :
    iota (k := k) (L := L) r (z + z') =
      iota (k := k) (L := L) r z + iota (k := k) (L := L) r z' := by
  show extToClasses (k := k) (K := L) (iotaLift (k := k) (L := L) r (z + z')) =
    extToClasses (k := k) (K := L) (iotaLift (k := k) (L := L) r z) +
      extToClasses (k := k) (K := L) (iotaLift (k := k) (L := L) r z')
  rw [pt_iotaLift_add, extToClasses_add]

/-- The orbit-placement map `ι_w` is `nsmul`-compatible. -/
theorem pt_iota_nsmul {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (r : NK.GlobalCFT.Place L) (n : ℕ)
    (z : extH (localUnitsK (k := k) (K := L) r) 2) :
    iota (k := k) (L := L) r (n • z) = n • iota (k := k) (L := L) r z := by
  show extToClasses (k := k) (K := L) (iotaLift (k := k) (L := L) r (n • z)) =
    n • extToClasses (k := k) (K := L) (iotaLift (k := k) (L := L) r z)
  rw [pt_iotaLift_nsmul, pt_extToClasses_nsmul]

/-- `ι_w` kills the zero class. -/
theorem pt_iota_zero {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (r : NK.GlobalCFT.Place L) :
    iota (k := k) (L := L) r (0 : extH (localUnitsK (k := k) (K := L) r) 2) = 0 := by
  have h := pt_iota_nsmul (k := k) (L := L) r 0 (0 : extH (localUnitsK (k := k) (K := L) r) 2)
  simpa using h

/-- **`p`-torsion is preserved by `ι_w`** — the input that lets `χ`'s additivity on `p`-torsion
(S1) be applied. -/
theorem pt_iota_ptorsion {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ)
    (r : NK.GlobalCFT.Place L) (z : extH (localUnitsK (k := k) (K := L) r) 2)
    (hz : p • z = 0) : p • iota (k := k) (L := L) r z = 0 := by
  rw [← pt_iota_nsmul, hz, pt_iota_zero]

/-- The level pairing is `nsmul`-compatible in its `Ext` variable. -/
theorem levelPair_nsmul_fst {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {r s : ℕ}
    (n : ℕ) (x : Abelian.Ext.{0} M A r) (h : extH (Rep.res f M) s) :
    levelPair f ι (n • x) h = n • levelPair f ι x h :=
  AddMonoidHom.map_nsmul
    { toFun := fun x => levelPair f ι x h
      map_zero' := levelPair_zero f ι h
      map_add' := fun x x' => levelPair_add f ι x x' h } n x

/-- The level pairing is `nsmul`-compatible in its `Hˢ` variable. -/
theorem levelPair_nsmul_snd {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {r s : ℕ}
    (n : ℕ) (x : Abelian.Ext.{0} M A r) (h : extH (Rep.res f M) s) :
    levelPair f ι x (n • h) = n • levelPair f ι x h :=
  AddMonoidHom.map_nsmul
    { toFun := fun h => levelPair f ι x h
      map_zero' := levelPair_zero_h f ι x
      map_add' := fun h h' => levelPair_add_h f ι x h h' } n h

/-! ## A `simp` lemma for the `obtain ⟨a, b⟩ := h` in `PT.finAtLevelFix`'s body -/

/-- `And.rec` on a conjunction, in application form.  `simp only [and_rec_apply]` turns the
`And.rec` produced by `obtain ⟨a, b⟩ := h` (left unreduced because `h` is an opaque theorem) into an
ordinary application — this is what makes the `PT.finAtLevelFix` clause proofs tractable. -/
theorem and_rec_apply {P Q : Prop} {C : Sort*} (f : P → Q → C) (h : P ∧ Q) :
    And.rec f h = f h.1 h.2 := by
  cases h with
  | intro a b => rfl

/-! ## The clauses of the finite half at a fixed level -/

section FinHalf

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- `χ` kills the zero class (S1's additivity at `u = v = 0`). -/
theorem chi_zero
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → extH (classesK k L) 2 → ZMod p)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : extH (classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) :
    χ L hKL (0 : extH (classesK k L) 2) = 0 := by
  have h := hχadd L hKL (0 : extH (classesK k L) 2) 0 (by simp) (by simp)
  have h' : χ L hKL (0 : extH (classesK k L) 2) =
      χ L hKL 0 + χ L hKL 0 := by simpa using h
  exact (add_left_cancel (show χ L hKL (0 : extH (classesK k L) 2) + (0 : ZMod p) =
      χ L hKL (0 : extH (classesK k L) 2) + χ L hKL 0 from by rw [add_zero, ← h'])).symm

end FinHalf


/-! ## The two additivity steps of `G1⁺`'s finite half, in the *generic* (definition-free) form

Clause (1) and clause (2) of the finite half are, after unfolding `PT.finAtLevel`, the two
statements below: `χ`'s additivity on `p`-torsion (S1) applied to `ι_w` of the level pairing.  They
are stated for an *arbitrary* `Rep`-level `ι`, `f` and an arbitrary `χ`-component, so they do not
depend on the internal shape of the finite-half definition — which is exactly what is needed while
that definition is being reworked by the `G1⁺` lane (see `PING_g1plus_clauses_state.md` §3.4). -/

/-- **Clause (1), generic**: `χ ∘ ι_r ∘ levelPair` is additive in the first (`Ext`) variable. -/
theorem chi_iota_levelPair_add_fst {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) [Fact p.Prime]
    (r : NK.GlobalCFT.Place L) (χL : extH (classesK k L) 2 → ZMod p)
    (hadd : ∀ u v : extH (classesK k L) 2, p • u = 0 → p • v = 0 → χL (u + v) = χL u + χL v)
    {G : Type} [Group G] (f : ↥(decompK (k := k) r) →* G)
    {A : Rep.{0} Coeff G} (ι : Rep.res f A ⟶ localUnitsK (k := k) (K := L) r)
    {M : Rep.{0} Coeff G}
    (y y' : Abelian.Ext.{0} M A 1) (h : extH (Rep.res f M) 1)
    (hy : p • y = 0) (hy' : p • y' = 0) :
    χL (iota (k := k) (L := L) r (levelPair f ι (y + y') h))
      = χL (iota (k := k) (L := L) r (levelPair f ι y h))
        + χL (iota (k := k) (L := L) r (levelPair f ι y' h)) := by
  rw [Work.SSGRoute.levelPair_add, pt_iota_add]
  refine hadd _ _ ?_ ?_
  · refine pt_iota_ptorsion p _ _ ?_
    rw [← Work.SSGRoute.PT.levelPair_nsmul_fst, hy, Work.SSGRoute.levelPair_zero]
  · refine pt_iota_ptorsion p _ _ ?_
    rw [← Work.SSGRoute.PT.levelPair_nsmul_fst, hy', Work.SSGRoute.levelPair_zero]

/-- **Clause (2), generic**: `χ ∘ ι_r ∘ levelPair` is additive in the second (`Hˢ`) variable. -/
theorem chi_iota_levelPair_add_snd {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) [Fact p.Prime]
    (r : NK.GlobalCFT.Place L) (χL : extH (classesK k L) 2 → ZMod p)
    (hadd : ∀ u v : extH (classesK k L) 2, p • u = 0 → p • v = 0 → χL (u + v) = χL u + χL v)
    {G : Type} [Group G] (f : ↥(decompK (k := k) r) →* G)
    {A : Rep.{0} Coeff G} (ι : Rep.res f A ⟶ localUnitsK (k := k) (K := L) r)
    {M : Rep.{0} Coeff G}
    (y : Abelian.Ext.{0} M A 1) (h h' : extH (Rep.res f M) 1)
    (hh : p • h = 0) (hh' : p • h' = 0) :
    χL (iota (k := k) (L := L) r (levelPair f ι y (h + h')))
      = χL (iota (k := k) (L := L) r (levelPair f ι y h))
        + χL (iota (k := k) (L := L) r (levelPair f ι y h')) := by
  rw [Work.SSGRoute.levelPair_add_h, pt_iota_add]
  refine hadd _ _ ?_ ?_
  · refine pt_iota_ptorsion p _ _ ?_
    rw [← Work.SSGRoute.PT.levelPair_nsmul_snd, hh, Work.SSGRoute.levelPair_zero_h]
  · refine pt_iota_ptorsion p _ _ ?_
    rw [← Work.SSGRoute.PT.levelPair_nsmul_snd, hh', Work.SSGRoute.levelPair_zero_h]

/-
## ARCHIVED (2026-10-03, blocked upstream): the same two clauses stated about `PT.finAtLevel`

Both proofs below are complete and were *building* against `PT/g1plus_finHalf.lean`'s `finAtLevel`
as it stood before 11:43; they broke when that file's `hval` was rewritten from the transported form
`modRep_compHom_eq_res_res … hφ ▸ hclass` to the cast-free `hval := hclass`.  With the cast gone the
*unfolded goal* is ill-typed in the sense of `PING_g1plus_clauses_state.md` §3.3 — Lean reports
"the target expression is not type-correct under the `implicit` transparency level" and
`rw [levelPair_add]` then finds no occurrence.  They should be restored (they are two lines once the
definitional form is fixed: apply `chi_iota_levelPair_add_fst`/`_snd` to the unfolded value) as soon
as `g1plus_finHalf.lean` carries a well-typed finite half again.

`finAtLevel_add_left` (clause (1) at a fixed level):
  `finAtLevel … (a + a') b hb b₀ hb₀ = finAtLevel … a b hb b₀ hb₀ + finAtLevel … a' b hb b₀ hb₀`,
  proof: `have hqc := exists_place_under_isFinPlace k Ω K A hA`;
  `have hβl := local_ext_h1_bridge … hqc.choose hAq`; `simp only [finAtLevel]`;
  `rw [hβl.choose_spec.1 a a' ha hla ha' hla']`; then `chi_iota_levelPair_add_fst` applied to the
  `ι_w (levelPair (·) hval)` under `χ L hKL`, with the `p`-torsion of `βl a` (resp. `βl a'`)
  obtained from `hβl.choose_spec`'s additivity by `nsmul`-induction plus the pointwise
  `p • a = 0` (`nsmul_eq_zero_of_zmod`).
`finAtLevel_coboundary_left` (clause (3) at a fixed level, first variable a coboundary):
  same unfolding; `rw [show hβl.choose a = 0 from (hβl.choose_spec.2.1 a ha hla).mpr hacob,
  levelPair_zero, pt_iota_zero]`; then `chi_zero`.
-/

/-- **Clause (3), generic, first variable**: `χ ∘ ι_r ∘ levelPair` vanishes on the zero `Ext` class. -/
theorem chi_iota_levelPair_zero_fst {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) [Fact p.Prime]
    (r : NK.GlobalCFT.Place L) (χL : extH (classesK k L) 2 → ZMod p) (hzero : χL 0 = 0)
    {G : Type} [Group G] (f : ↥(decompK (k := k) r) →* G)
    {A : Rep.{0} Coeff G} (ι : Rep.res f A ⟶ localUnitsK (k := k) (K := L) r)
    {M : Rep.{0} Coeff G} (h : extH (Rep.res f M) 1) :
    χL (iota (k := k) (L := L) r (levelPair f ι (0 : Abelian.Ext.{0} M A 1) h)) = 0 := by
  rw [Work.SSGRoute.levelPair_zero, pt_iota_zero, hzero]

/-- **Clause (3), generic, second variable**: the same on the zero `H¹` class. -/
theorem chi_iota_levelPair_zero_snd {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (p : ℕ) [Fact p.Prime]
    (r : NK.GlobalCFT.Place L) (χL : extH (classesK k L) 2 → ZMod p) (hzero : χL 0 = 0)
    {G : Type} [Group G] (f : ↥(decompK (k := k) r) →* G)
    {A : Rep.{0} Coeff G} (ι : Rep.res f A ⟶ localUnitsK (k := k) (K := L) r)
    {M : Rep.{0} Coeff G} (y : Abelian.Ext.{0} M A 1) :
    χL (iota (k := k) (L := L) r (levelPair f ι y (0 : extH (Rep.res f M) 1))) = 0 := by
  rw [Work.SSGRoute.levelPair_zero_h, pt_iota_zero, hzero]


/-! ## (G1) The level class is additive in the factorised crossed homomorphism

This is the piece of clause (2) that is *not* the level question: at a **fixed** level the second
factor of the finite half is the class `[b]_L ∈ H¹(D_w, M^∨(1))` of the factorisation `b₀` of `b|_H`
through `Gal(L/k)` (`PT.levelClass`), and `[b + b']_L = [b]_L + [b']_L`.

**The technical point that had blocked this** (see `PING_g1plus_clauses_state.md` §3.3): `levelClass`'s
declared type is `extH (Rep.res f (Rep.res … (modRep …))) 1` while its body is an `ExtH1.gammaZ1`
application of type `extH (modRep ↥(decompK w) …) 1`; the two are *definitionally* equal but only at
default transparency, so any `rw` into the body is rejected ("the target expression is not
type-correct under the `implicit` transparency level").  **The fix is to state the lemma at *one*
type** — ascribe all three `levelClass` applications to the `modRep` type — after which the `Z₁`
bookkeeping is proof-irrelevant, `gammaZ1` is an `AddMonoidHom`, and everything rewrites. -/

section LevelClassAdd

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K L : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k L] [IsGalois k L]
  [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]

/-- **A crossed homomorphism on `Gal(L/k)` is a `1`-cocycle on the decomposition group of `w`**:
the composite `fun g ↦ c (g : ↥L ≃ₐ[k] ↥L)` lies in `Z¹`, the coefficient carrying the `galRes`
pull-back along `φ = subtype_q ∘ f`. -/
theorem mem_Z1_comp_restrict
    (p : ℕ) [Fact p.Prime]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (f : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (hf : ∀ σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      ((f σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) : ↥K ≃ₐ[k] ↥K)
        = galRes k (↥K) (↥L) (σ : ↥L ≃ₐ[k] ↥L))
    (M T : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hcrossed : ∀ g h : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      b₀ (↑(g * h) : ↥L ≃ₐ[k] ↥L) = b₀ (g : ↥L ≃ₐ[k] ↥L) +
        (galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • b₀ (h : ↥L ≃ₐ[k] ↥L)) :
    letI : DistribMulAction ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
        (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
      DistribMulAction.compHom _
        ((decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp f)
    (fun g : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) =>
        b₀ (g : ↥L ≃ₐ[k] ↥L)) ∈
      Work.GroupCohomology.Z1 ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
        (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) := by
  rw [Work.GroupCohomology.mem_Z1_iff]
  intro g h
  show b₀ (↑(g * h)) =
    (((f g : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) : ↥K ≃ₐ[k] ↥K) • b₀ ↑h) + b₀ ↑g
  rw [hcrossed g h, hf g, add_comm]

/-- **(G1)** `PT.levelClass` is additive in the level-`L` crossed homomorphism `b₀`, *stated at one
`Ext` type* so that the whole `γ¹` bookkeeping is well-typed. -/
theorem levelClass_add
    (p : ℕ) [Fact p.Prime]
    (hKL : K ≤ L)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (f : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (hf : ∀ σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      ((f σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) : ↥K ≃ₐ[k] ↥K)
        = galRes k (↥K) (↥L) (σ : ↥L ≃ₐ[k] ↥L))
    (M T : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (b₀ b₀' : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (h1 : ∀ g h : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      b₀ (↑(g * h) : ↥L ≃ₐ[k] ↥L) = b₀ (g : ↥L ≃ₐ[k] ↥L) +
        (galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • b₀ (h : ↥L ≃ₐ[k] ↥L))
    (h2 : ∀ g h : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      b₀' (↑(g * h) : ↥L ≃ₐ[k] ↥L) = b₀' (g : ↥L ≃ₐ[k] ↥L) +
        (galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • b₀' (h : ↥L ≃ₐ[k] ↥L))
    (h3 : ∀ g h : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      (fun τ => b₀ τ + b₀' τ) (↑(g * h) : ↥L ≃ₐ[k] ↥L)
        = (fun τ => b₀ τ + b₀' τ) (g : ↥L ≃ₐ[k] ↥L) +
          (galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • (fun τ => b₀ τ + b₀' τ) (h : ↥L ≃ₐ[k] ↥L)) :
    letI : DistribMulAction ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
        (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
      DistribMulAction.compHom _
        ((decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp f)
    ((levelClass p k Ω K L hKL q w f hf M T (fun τ => b₀ τ + b₀' τ) h3 :
        extH (modRep ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))) 1) =
      (levelClass p k Ω K L hKL q w f hf M T b₀ h1 :
        extH (modRep ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))) 1) +
      (levelClass p k Ω K L hKL q w f hf M T b₀' h2 :
        extH (modRep ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))) 1)) := by
  letI : DistribMulAction ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    DistribMulAction.compHom _ ((decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp f)
  have e1 : (levelClass p k Ω K L hKL q w f hf M T b₀ h1 :
        extH (modRep ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))) 1) =
      ExtH1.gammaZ1 (↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)))
        (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
        (Work.SSGRoute.augSES_shortExact ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)))
        ⟨fun g => b₀ (g : ↥L ≃ₐ[k] ↥L), mem_Z1_comp_restrict p q w f hf M T b₀ h1⟩ := rfl
  have e2 : (levelClass p k Ω K L hKL q w f hf M T b₀' h2 :
        extH (modRep ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))) 1) =
      ExtH1.gammaZ1 (↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)))
        (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
        (Work.SSGRoute.augSES_shortExact ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)))
        ⟨fun g => b₀' (g : ↥L ≃ₐ[k] ↥L), mem_Z1_comp_restrict p q w f hf M T b₀' h2⟩ := rfl
  have e3 : (levelClass p k Ω K L hKL q w f hf M T (fun τ => b₀ τ + b₀' τ) h3 :
        extH (modRep ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))) 1) =
      ExtH1.gammaZ1 (↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)))
        (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
        (Work.SSGRoute.augSES_shortExact ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)))
        ⟨fun g => b₀ (g : ↥L ≃ₐ[k] ↥L) + b₀' (g : ↥L ≃ₐ[k] ↥L),
          mem_Z1_comp_restrict p q w f hf M T (fun τ => b₀ τ + b₀' τ) h3⟩ := rfl
  rw [e1, e2, e3]
  rw [show (⟨fun g => b₀ (g : ↥L ≃ₐ[k] ↥L) + b₀' (g : ↥L ≃ₐ[k] ↥L),
          mem_Z1_comp_restrict p q w f hf M T (fun τ => b₀ τ + b₀' τ) h3⟩ :
        Work.GroupCohomology.Z1 ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)))
      = (⟨fun g => b₀ (g : ↥L ≃ₐ[k] ↥L),
            mem_Z1_comp_restrict p q w f hf M T b₀ h1⟩ :
          Work.GroupCohomology.Z1 ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
            (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)))
        + ⟨fun g => b₀' (g : ↥L ≃ₐ[k] ↥L),
            mem_Z1_comp_restrict p q w f hf M T b₀' h2⟩
      from Subtype.ext rfl]
  rw [map_add]
  rfl

/-- **The level class depends on the crossed-homomorphism datum only through its underlying
function**: two proofs of the crossed-homomorphism property give the same class.  (Used to normalise
the proof field before applying `levelClass_add`.) -/
theorem levelClass_proof_irrel
    (p : ℕ) [Fact p.Prime]
    (hKL : K ≤ L)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (f : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (hf : ∀ σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      ((f σ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) : ↥K ≃ₐ[k] ↥K)
        = galRes k (↥K) (↥L) (σ : ↥L ≃ₐ[k] ↥L))
    (M T : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (h1 h2 : ∀ g h : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      b₀ (↑(g * h) : ↥L ≃ₐ[k] ↥L) = b₀ (g : ↥L ≃ₐ[k] ↥L) +
        (galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) • b₀ (h : ↥L ≃ₐ[k] ↥L)) :
    letI : DistribMulAction ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
        (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
      DistribMulAction.compHom _
        ((decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp f)
    ((levelClass p k Ω K L hKL q w f hf M T b₀ h1 :
        extH (modRep ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))) 1) =
      (levelClass p k Ω K L hKL q w f hf M T b₀ h2 :
        extH (modRep ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))) 1)) := by
  letI : DistribMulAction ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    DistribMulAction.compHom _ ((decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp f)
  rfl

end LevelClassAdd


/-! ## Clause (2) of the finite half at a fixed level — deferred to the `finZH`-additivity lemma

With `finAtLevel` now built from the opaque defs `finZZ`/`finZH` (see
`PT/PING_session42_finAtLevel_welltyped.md`), clause (2) at a fixed level is exactly the additivity
of `finLevelClass` in the factorised cocycle `b₀`

  `finLevelClass … (fun τ => b₀ τ + b₀' τ) … = finLevelClass … b₀ … + finLevelClass … b₀' …`

(the `finZH`-spelling of the argument that proves `levelClass_add` above: `ExtH1.gammaHom` of a sum
of `Z¹`-elements, with the `Rep`-transport of `modRep_compHom_eq_res_res` irrelevant by proof
irrelevance of the transported *type* equality), followed by `chi_iota_levelPair_add_snd`.  It is
re-stated against the `finZZ`-based `finAtLevel` as soon as that additivity lemma is available; the
*level-free* clause (2) needs `PT.finAtLevel_eq_of_le` in addition. -/

/-! ## Clauses (1) and (3) of the finite half at a fixed level

(These were previously stated against `PT.finAtLevel`'s *transported* second factor; with the
generic lemmas `chi_iota_levelPair_add_fst` / `chi_iota_levelPair_zero_fst` the proofs no longer
touch that factor, so they are stable under the reworkings of the definition.) -/

section ClauseOneThree

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- **Clause (1) of `G1⁺`'s finite half at a fixed level**: `finAtLevel` is additive in its first
variable. -/
theorem finAtLevel_add_left
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → extH (classesK k L) 2 → ZMod p)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : extH (classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L)
    (a a' : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hla : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (ha' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a')
    (hla' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a')
    (b₀ : ((↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T)))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) :
    finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L hKL (a + a') b hb b₀ hb₀
      = finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L hKL a b hb b₀ hb₀
        + finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L hKL a' b hb b₀ hb₀ := by
  classical
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h0coc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A)
      (0 : (Ω ≃ₐ[k] Ω) → M) := fun g _ h _ => by simp
  have h0lc : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (0 : (Ω ≃ₐ[k] Ω) → M) :=
    ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩
  have h0cob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
      (0 : (Ω ≃ₐ[k] Ω) → M) := ⟨0, fun g _ => by simp⟩
  have h0val : finZB p K ζ hζ hζK T hT M A hA (0 : (Ω ≃ₐ[k] Ω) → M) = 0 :=
    (finZB_eq_zero_iff p k Ω K ζ hζ hζK T hT M A hA 0 h0coc h0lc).mpr h0cob
  have hptor : ∀ c : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) c →
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) c →
      p • finZB p K ζ hζ hζK T hT M A hA c = 0 := by
    intro c hc hlc
    have hsm : ∀ n : ℕ,
        finZB p K ζ hζ hζK T hT M A hA (n • c)
          = n • finZB p K ζ hζ hζK T hT M A hA c := by
      intro n
      induction n with
      | zero =>
        rw [zero_smul, zero_smul]
        exact h0val
      | succ n ih =>
        rw [add_nsmul, one_nsmul,
          finZB_add p k Ω K ζ hζ hζK T hT M A hA (n • c) c
            (isCocycleOn_nsmul _ _ c n hc) (isLocConstOn_nsmul _ c n hlc) hc hlc,
          ih, add_nsmul, one_nsmul]
    have h1 : p • c = (0 : (Ω ≃ₐ[k] Ω) → M) := by
      funext σ
      exact nsmul_eq_zero_of_zmod p (c σ)
    rw [← hsm p, h1, h0val]
  have hZB : finZB p K ζ hζ hζK T hT M A hA (a + a')
      = finZB p K ζ hζ hζK T hT M A hA a + finZB p K ζ hζ hζK T hT M A hA a' :=
    finZB_add p k Ω K ζ hζ hζK T hT M A hA a a' ha hla ha' hla'
  have ht1 : p • finZB p K ζ hζ hζK T hT M A hA a = 0 := hptor a ha hla
  have ht2 : p • finZB p K ζ hζ hζK T hT M A hA a' = 0 := hptor a' ha' hla'
  simp only [finAtLevel, finZZ]
  rw [hZB]
  exact chi_iota_levelPair_add_fst p (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) (χ L hKL)
    (hχadd L hKL) (finZF hKL A hA) (finZI hKL A hA) _ _
    (finZH p K T M L hKL A hA b hb b₀ hb₀) ht1 ht2

/-- **Clause (3) of `G1⁺`'s finite half at a fixed level, first variable**: `finAtLevel` vanishes
when its first argument is a coboundary. -/
theorem finAtLevel_coboundary_left
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → extH (classesK k L) 2 → ZMod p)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : extH (classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hla : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hacob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (b₀ : ((↥L ≃ₐ[k] ↥L) → DualMod p (M ⊗[ZMod p] T)))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) :
    finAtLevel p k Ω K ζ hζ hζK T hT χ M A hA L hKL a b hb b₀ hb₀ = 0 := by
  classical
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hZB0 : finZB p K ζ hζ hζK T hT M A hA a = 0 :=
    (finZB_eq_zero_iff p k Ω K ζ hζ hζK T hT M A hA a ha hla).mpr hacob
  simp only [finAtLevel, finZZ]
  rw [hZB0]
  exact chi_iota_levelPair_zero_fst p (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) (χ L hKL)
    (chi_zero p k Ω K χ hχadd L hKL) (finZF hKL A hA) (finZI hKL A hA)
    (finZH p K T M L hKL A hA b hb b₀ hb₀)

end ClauseOneThree


/-! ## Clause (1) of the finite half *level-free*

`PT.finAtValue` chooses its level from `b` **alone** (never from `a`), so for `a`, `a'`, `a + a'` the
same `Classical.choose` is used and the fixed-level clause (1) transfers verbatim.  This is a
genuine `H1Pair.PairClauses` conjunct (clause (1) of `G1⁺`'s `hclauses`), with no level-independence
input. -/

section LevelFreeOne

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- **Clause (1) of `G1⁺`'s finite half, level-free**: additivity in the first variable. -/
theorem finAtValue_add_left
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → extH (classesK k L) 2 → ZMod p)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : extH (classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a a' : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (ha : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (ha' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a')
    (haa : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (a + a'))
    (hca : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hca' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a') :
    finAtValue p k Ω K ζ hζ hζK T hT χ M A hA (SSGRoute.decomp k A) (a + a') b haa hb
      = finAtValue p k Ω K ζ hζ hζK T hT χ M A hA (SSGRoute.decomp k A) a b ha hb
        + finAtValue p k Ω K ζ hζ hζK T hT χ M A hA (SSGRoute.decomp k A) a' b ha' hb := by
  classical
  simp only [finAtValue]
  rw [dif_pos trivial, dif_pos trivial, dif_pos trivial]
  by_cases hbc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b
  · rw [dif_pos hbc, dif_pos hbc, dif_pos hbc]
    have hL := exists_level_factors_locConstOn p k Ω K
      (M := DualMod p (M ⊗[ZMod p] T)) (SSGRoute.decomp k A) b hb
    let L := hL.choose
    have hLfin : FiniteDimensional k L := hL.choose_spec.choose
    have hLnorm : Normal k L := hL.choose_spec.choose_spec.choose
    letI : FiniteDimensional k L := hLfin
    letI : Normal k L := hLnorm
    letI : IsGalois k L := inferInstance
    letI : NumberField L := inferInstance
    have hKL : K ≤ L := hL.choose_spec.choose_spec.choose_spec.1
    have hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ =
        hL.choose_spec.choose_spec.choose_spec.2.choose
          (AlgEquiv.restrictNormalHom L σ) :=
      hL.choose_spec.choose_spec.choose_spec.2.choose_spec
    exact finAtLevel_add_left p k Ω K ζ hζ hζK T hT χ hχadd M A hA L hKL a a' b hbc
      hca ha hca' ha' (hL.choose_spec.choose_spec.choose_spec.2.choose) hb₀
  · rw [dif_neg hbc, dif_neg hbc, dif_neg hbc]
    simp


/-- **Clause (3) of `G1⁺`'s finite half, level-free, first variable**: `finAtValue` vanishes when its
first argument is a coboundary.  (Level-free for the same reason as clause (1).) -/
theorem finAtValue_coboundary_left
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → extH (classesK k L) 2 → ZMod p)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (hKL : K ≤ L) (u v : extH (classesK k L) 2),
        p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → DualMod p (M ⊗[ZMod p] T))
    (ha : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hca : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) a)
    (hacob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a) :
    finAtValue p k Ω K ζ hζ hζK T hT χ M A hA (SSGRoute.decomp k A) a b ha hb = 0 := by
  classical
  simp only [finAtValue]
  rw [dif_pos trivial]
  by_cases hbc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b
  · rw [dif_pos hbc]
    have hL := exists_level_factors_locConstOn p k Ω K
      (M := DualMod p (M ⊗[ZMod p] T)) (SSGRoute.decomp k A) b hb
    let L := hL.choose
    have hLfin : FiniteDimensional k L := hL.choose_spec.choose
    have hLnorm : Normal k L := hL.choose_spec.choose_spec.choose
    letI : FiniteDimensional k L := hLfin
    letI : Normal k L := hLnorm
    letI : IsGalois k L := inferInstance
    letI : NumberField L := inferInstance
    have hKL : K ≤ L := hL.choose_spec.choose_spec.choose_spec.1
    have hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ =
        hL.choose_spec.choose_spec.choose_spec.2.choose
          (AlgEquiv.restrictNormalHom L σ) :=
      hL.choose_spec.choose_spec.choose_spec.2.choose_spec
    exact finAtLevel_coboundary_left p k Ω K ζ hζ hζK T hT χ hχadd M A hA L hKL a b hbc
      hca ha hacob (hL.choose_spec.choose_spec.choose_spec.2.choose) hb₀
  · rw [dif_neg hbc]

end LevelFreeOne

end Work.SSGRoute.PT
