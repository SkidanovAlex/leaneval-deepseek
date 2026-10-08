/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# `Work.CORE4.SixConj` — report on the §4 (6) "witness"

The requested statement is

> `∃ g : G, g ∉ D.M ∧ conjSub g D.F ≤ fittingIn B.U ⊓ D.M`

i.e. *some conjugate of `F` by an element outside `M` lies in `F(U) ⊓ M`*.  This is the witness
Bender uses at the end of his §4 (6) (p. 225 of Bender, *Finite groups with dihedral Sylow
2-subgroups*, J. Algebra **70** (1981) 216–228, where `F(U) ∩ M = K₁F` is his (3)):

> "This implies `F ∩ F^g = 1` for each `g ∈ G − M`.  As we can choose `g ∈ N_G(K₁F)`, `F` is
> isomorphic to a subgroup of `K₁`, hence is cyclic."

with hypothesis list `BenderCtx G`, `Case2Data B`, `Case2Pre B D` (Bender's §4 (1)–(5)) and the
cross-area bundle `C4Inputs`.

**Verdict: the statement is under-hypothesised — it is not derivable from §4 (1)–(5) as recorded,
and the witness it asks for is precisely one of the inputs the sibling leaf `CORE4/Case2Six`
identified as *missing hypotheses*.**  The correct repair is to state the witness (together with
Bender's (3) identity and the `1.10(ii)`-layer input) as a hypothesis of a §4 (7)/(8) layer leaf.

## 1. Bender's own justification is not available from §4 (1)–(5)

Bender derives the witness from `g ∈ N_G(K₁F)`.  Read literally, that requires an element
`g ∉ M` with `g (F(U) ⊓ M) g⁻¹ = F(U) ⊓ M`, i.e. `N_G(F(U) ⊓ M) ⊄ M` — exactly the step the
referees of the design recorded as missing.  Note that this is *not* automatic from the recorded
data, and also not excluded by them: `Case2Pre` records `F ⊴ M` (as `N_G(F) = M`), and
`F ≤ F(U) ⊓ M ≤ M` by (3), so `F ⊴ F(U) ⊓ M`; but normality is not characteristicity, so
`N_G(F(U) ⊓ M) ≤ N_G(F) = M` does **not** follow, and in the case `F(U) ⊓ M ⊴ M` (which §4 (1)–(5)
do not exclude either) maximality of `M` would give `N_G(F(U) ⊓ M) = M` outright, so *no* `g ∉ M`
normalising `F(U) ⊓ M` could exist.  What the cyclicity argument needs is that some conjugate of `F`
*different from* `F` lies inside `F(U) ⊓ M`; that requires (3) plus the structure of `F(U) ⊓ M` and
of `N_G(F(U) ⊓ M)`, none of which §4 (1)–(5) record.

## 2. Machine-checked obstruction: the conclusion smuggles in Bender's (1)

Any witness forces `D.K ≠ ⊥`, as proved below (`SixConj_imp_K_ne_bot`).  Consequently any proof of
`SixConj` must first derive `K ≠ ⊥` from the recorded hypotheses.  But the recorded hypotheses are
perfectly compatible with `D.K = ⊥`; and in that case the conclusion *fails*:

* if `D.K = ⊥`, then `U ⊓ M = K ⊔ B₀ = B₀` (recorded: `Case2Pre.U_eq`), so by `Case2Data.F_def`
  and `B₀ = (U ⊓ M) ⊓ C(s)`,
  `D.F = B₀ ⊓ F(U) = (U ⊓ M) ⊓ F(U) = F(U) ⊓ M` (`F_eq_fittingIn_of_K_eq_bot`);
* then a witness `g ∉ M` with `conjSub g D.F ≤ F(U) ⊓ M = D.F` has `|F^g| = |F|`, hence
  `F^g = F`, hence `g ∈ N_G(F) = D.M` — a contradiction (`not_exists_conjSub_le_of_K_eq_bot`).

This is exactly Bender's (1) content `K = [S ∩ E, U ∩ M] = I_{U∩M}(s) ≠ 1` (equivalently: a
non-trivial cyclic subgroup of `U ∩ E/Z(E)` inverted by `s`), which in the paper is derived from the
structure of `E(M)/Z(E) ∈ {A₇, L₂(q)}`.  The formalised §4 (1)–(5) (`Case2Pre`, `Case2Data`) records
`K = I_{U∩M}(s)`, `K` cyclic, `U ⊓ M = K ⊔ B₀`, `B₀ = (U ⊓ M) ⊓ C(s)`, `F ≠ ⊥`, `F ≤ C(E)`,
`N_G(F) = M` — none of which excludes `K = ⊥` (note `⊥` is cyclic, and with `K = ⊥` both
`U ⊓ M = K ⊔ B₀` and `B₀ = (U ⊓ M) ⊓ C(s)` hold with `B₀ = U ⊓ M`, while `F = F(U) ⊓ M ≠ ⊥` is
still possible).  So a proof must derive `K ≠ ⊥` from the recorded hypotheses — in the paper this is
§4 (1) plus the structure of `E(M)` — before the witness can even be attempted.

## 3. Cross-check with the sibling report

This agrees with `Submission/Work/CORE4/Case2Six.lean` and `NOTES_CORE4.md` §6, which record that
the §4 (1)–(5) hypothesis list does not contain "the witness `g` with
`conjSub g D.F ≤ fittingIn B.U ⊓ D.M`" nor (3) nor the `1.10(ii)`-layer input, and recommend adding
them to the hypothesis list of the §4 (7)/(8) layer.

## 4. Formal status

`BenderCtx` (a non-abelian simple minimal counterexample with dihedral Sylow 2-subgroups that is
neither `A₇` nor `L₂(q)`) is the hypothesis of Bender's §§2–4 and is expected to be *unsatisfiable*
(Gorenstein–Walter); so the statement is not refutable by exhibiting a group — it is "true" only
vacuously, and a proof of it must either reproduce §4 or invoke the theorem being proved.  What is
established here is that it is not a consequence of the recorded §4 (1)–(5) data, so it cannot serve
as a hypothesis-free leaf above `Case2Pre`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G]

/-! ## 0. Elementary facts about `conjSub` -/

/-- Conjugation of a subgroup preserves its cardinality. -/
theorem conjSub_card (g : G) (K : Subgroup G) :
    Nat.card ↥(Work.GW2.conjSub g K) = Nat.card ↥K := by
  rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]

/-- `K^g = K` if and only if `g` normalises `K`. -/
theorem conjSub_eq_iff_mem_normalizer (g : G) (K : Subgroup G) :
    Work.GW2.conjSub g K = K ↔ g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Work.GW2.conjSub]
  exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := K) (g := g)).symm

/-- The Fitting subgroup of a subgroup is contained in it. -/
theorem fittingIn_le (K : Subgroup G) : Work.GW2.fittingIn K ≤ K := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

/-! ## 1. The `K = ⊥` configuration

If `D.K = ⊥` then §4 (1)–(5) force `D.F = F(U) ⊓ D.M`, and then the requested witness cannot
exist.  This is the configuration that shows the statement to be under-hypothesised: it is
compatible with every recorded hypothesis and refutes the conclusion. -/

section Case2

variable [Finite G]
variable {B : Work.GW2.BenderSetup G} (D : Work.GW2.Case2Data B)

/-- `s` inverts `K` by construction, hence normalises it. -/
theorem conjSub_s_K : Work.GW2.conjSub D.s D.K = D.K := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy' : y ∈ Work.GW2.invSet (B.U ⊓ D.M) D.s := by rw [← D.K_def]; exact hy
    show D.s * y * D.s⁻¹ ∈ D.K
    rw [hy'.2]
    exact D.K.inv_mem hy
  · intro x hx
    refine ⟨x⁻¹, D.K.inv_mem hx, ?_⟩
    have hx' : x ∈ Work.GW2.invSet (B.U ⊓ D.M) D.s := by rw [← D.K_def]; exact hx
    show D.s * x⁻¹ * D.s⁻¹ = x
    calc D.s * x⁻¹ * D.s⁻¹ = (D.s * x * D.s⁻¹)⁻¹ := by group
      _ = x := by rw [hx'.2, inv_inv]

/-- If `B.U ⊓ D.M = D.K ⊔ D.B0` and `D.K = ⊥` then `D.B0 = B.U ⊓ D.M`. -/
theorem B0_eq_UinfM_of_K_eq_bot (hU : B.U ⊓ D.M = D.K ⊔ D.B0) (hK : D.K = ⊥) :
    D.B0 = B.U ⊓ D.M := by
  rw [hU, hK, bot_sup_eq]

/-- With `D.K = ⊥`, §4 (1)–(5) give `D.F = F(U) ⊓ D.M` (Bender's (3) becomes an identity). -/
theorem F_eq_fittingIn_of_K_eq_bot (hpre : Work.GW2.Case2Pre B D) (hK : D.K = ⊥) :
    D.F = Work.GW2.fittingIn B.U ⊓ D.M := by
  have hB0 : D.B0 = B.U ⊓ D.M := B0_eq_UinfM_of_K_eq_bot D (Work.GW2.Case2Pre.U_eq B D hpre) hK
  have hWU : Work.GW2.fittingIn B.U ≤ B.U := fittingIn_le B.U
  rw [D.F_def, hB0]
  calc (B.U ⊓ D.M) ⊓ Work.GW2.fittingIn B.U
      = Work.GW2.fittingIn B.U ⊓ (B.U ⊓ D.M) := by rw [inf_comm]
    _ = (Work.GW2.fittingIn B.U ⊓ B.U) ⊓ D.M := by rw [inf_assoc]
    _ = Work.GW2.fittingIn B.U ⊓ D.M := by rw [inf_eq_left.mpr hWU]

/-- If `D.F = F(U) ⊓ D.M` then the requested witness does not exist: it would force
`F^g = F` and hence `g ∈ N_G(F) = D.M`. -/
theorem not_exists_conjSub_le_of_F_eq_fittingIn
    (hN : Subgroup.normalizer (D.F : Set G) = D.M)
    (hF : D.F = Work.GW2.fittingIn B.U ⊓ D.M) :
    ¬ ∃ g : G, g ∉ D.M ∧ Work.GW2.conjSub g D.F ≤ Work.GW2.fittingIn B.U ⊓ D.M := by
  rintro ⟨g, hgM, hle⟩
  have hle' : Work.GW2.conjSub g D.F ≤ D.F := le_trans hle (le_of_eq hF.symm)
  have heq : Work.GW2.conjSub g D.F = D.F :=
    Subgroup.eq_of_le_of_card_ge hle' (le_of_eq (conjSub_card g D.F).symm)
  have hnorm : g ∈ Subgroup.normalizer (D.F : Set G) :=
    (conjSub_eq_iff_mem_normalizer g D.F).mp heq
  exact hgM (hN ▸ hnorm)

/-- With `D.K = ⊥` (which §4 (1)–(5) do not exclude) the requested witness does not exist. -/
theorem not_exists_conjSub_le_of_K_eq_bot (hpre : Work.GW2.Case2Pre B D) (hK : D.K = ⊥) :
    ¬ ∃ g : G, g ∉ D.M ∧ Work.GW2.conjSub g D.F ≤ Work.GW2.fittingIn B.U ⊓ D.M :=
  not_exists_conjSub_le_of_F_eq_fittingIn D (Work.GW2.Case2Pre.N_F B D hpre)
    (F_eq_fittingIn_of_K_eq_bot D hpre hK)

/-- **The obstruction.**  A witness for the requested statement forces `D.K ≠ ⊥`, i.e. the
statement smuggles in the content of Bender's §4 (1) `K = [S ∩ E, U ∩ M] ≠ 1` (a non-trivial cyclic
subgroup of `U ∩ E/Z(E)` inverted by `s`), which `Case2Pre`/`Case2Data` do not record. -/
theorem SixConj_imp_K_ne_bot (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      ∀ D : Work.GW2.Case2Data B, Work.GW2.Case2Pre B D →
        (∃ g : G, g ∉ D.M ∧ Work.GW2.conjSub g D.F ≤ Work.GW2.fittingIn B.U ⊓ D.M) →
          D.K ≠ ⊥ := by
  intro G _ _ _ B D hpre hwit hK
  exact not_exists_conjSub_le_of_K_eq_bot D hpre hK hwit

end Case2

/-- Bender 1981, §4 (6), cyclicity ingredient: there is `g ∉ D.M` with
`conjSub g D.F ≤ fittingIn B.U ⊓ D.M`.

*Report (see the module docstring): the statement is the witness Bender uses in §4 (6), but
`BenderCtx`/`Case2Data`/`Case2Pre` do not supply it.  Bender's justification (`g ∈ N_G(K₁F)`)
requires `N_G(F(U) ⊓ M) ⊄ M`, which §4 (1)–(5) neither record nor exclude; and the conclusion is not
a consequence of §4 (1)–(5): by `SixConj_imp_K_ne_bot` it entails `D.K ≠ ⊥`, while `D.K = ⊥` is
compatible with all the recorded data and in that case `D.F = F(U) ⊓ D.M`, so no witness exists
(`not_exists_conjSub_le_of_K_eq_bot`).  The witness (with Bender's (3) and the `1.10(ii)`-layer
input) must be added to the hypothesis list of the §4 (7)/(8) layer. -/
theorem SixConj (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      ∀ D : Work.GW2.Case2Data B, Work.GW2.Case2Pre B D →
        ∃ g : G, g ∉ D.M ∧ Work.GW2.conjSub g D.F ≤ Work.GW2.fittingIn B.U ⊓ D.M := by sorry

end Work.CORE4
