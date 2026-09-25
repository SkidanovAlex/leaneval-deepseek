/-
Copyright: the martinet_totally_real_towers team.

# Group extensions: conjugation, the transgression, and the five term sequence

Fix a group extension `1 → N → G → Q → 1`, encoded as a structure `GroupExt G Q N` carrying
`q : G →* Q`, `i : N →* G` and `ker q = range i`.

This module sets up

* the conjugation of an element of `N` by an element of `G` (`conj`), with `i (conj g n) = g i n g⁻¹`;
* the resulting action of `G` on `1`-cochains on `N` (`conjCochain`), hence on `H¹(N,M)`;
* the raw transgression cocycle `tgFun` attached to a section of `q` and a `1`-cocycle on `N`.

The exactness statements (the five term sequence) live in the modules delegated from this one; see
`README.md` §6 for the precise status.
-/

import Submission.Work.ConCohomology.Functoriality

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

/-- A group extension `1 → N → G → Q → 1`. -/
structure GroupExt (G : Type*) (Q : Type*) (N : Type*) [Group G] [Group Q] [Group N] where
  /-- The projection `G → Q`. -/
  q : G →* Q
  /-- The inclusion `N → G`. -/
  i : N →* G
  /-- `N` is the kernel of `q`. -/
  ker_eq : ∀ g : G, q g = 1 ↔ ∃ n : N, i n = g
  /-- The inclusion is injective. -/
  injective_i : Function.Injective i

namespace GroupExt

variable {G Q N : Type*} [Group G] [Group Q] [Group N]

/-- The proof that `g i(n) g⁻¹` lies in the kernel of `q`. -/
noncomputable def conjProof (E : GroupExt G Q N) (g : G) (n : N) :
    ∃ m : N, E.i m = g * E.i n * g⁻¹ :=
  (E.ker_eq (g * E.i n * g⁻¹)).mp (by
    rw [map_mul, map_mul, map_inv, show E.q (E.i n) = 1 from (E.ker_eq (E.i n)).mpr ⟨n, rfl⟩]
    simp)

/-- The conjugation of an element of `N` by an element of `G`, as an element of `N`. -/
noncomputable def conj (E : GroupExt G Q N) (g : G) (n : N) : N :=
  Classical.choose (E.conjProof g n)

lemma i_conj (E : GroupExt G Q N) (g : G) (n : N) :
    E.i (E.conj g n) = g * E.i n * g⁻¹ :=
  Classical.choose_spec (E.conjProof g n)

/-- A lift to `N` of an element of `G` lying in the kernel of `q`. -/
noncomputable def kerLift (E : GroupExt G Q N) (x : G) (hx : E.q x = 1) : N :=
  Classical.choose ((E.ker_eq x).mp hx)

lemma i_kerLift (E : GroupExt G Q N) (x : G) (hx : E.q x = 1) :
    E.i (E.kerLift x hx) = x :=
  Classical.choose_spec ((E.ker_eq x).mp hx)

lemma conj_one (E : GroupExt G Q N) (n : N) : E.conj 1 n = n := by
  apply E.injective_i
  rw [E.i_conj]
  simp

lemma conj_split (E : GroupExt G Q N) (g : G) (n : N) :
    E.conj g n = E.kerLift (g * E.i n * g⁻¹) (by
      rw [map_mul, map_mul, map_inv,
        show E.q (E.i n) = 1 from (E.ker_eq (E.i n)).mpr ⟨n, rfl⟩]
      simp) := by
  apply E.injective_i
  rw [E.i_conj, E.i_kerLift]

end GroupExt

section Action

variable {G Q N : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group Q] [TopologicalSpace Q]
variable [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M]

/-- The conjugation action of `G` on `1`-cochains on `N`.  The hypothesis `hcont` is the
continuity of the conjugation maps on `N`; it holds whenever `i` is a topological embedding into a
group where conjugation is continuous. -/
noncomputable def conjCochain (E : GroupExt G Q N) (hcont : ∀ g : G, Continuous (E.conj g))
    (g : G) (φ : Cochain1 N M) : Cochain1 N M :=
  ⟨fun n => g • (φ (E.conj g⁻¹ n)),
    IsLocallyConstant.comp (φ.isLocallyConstant.comp_continuous (hcont g⁻¹))
      (fun m => g • m)⟩

@[simp] lemma conjCochain_apply (E : GroupExt G Q N) (hcont : ∀ g : G, Continuous (E.conj g))
    (g : G) (φ : Cochain1 N M) (n : N) :
    conjCochain E hcont g φ n = g • (φ (E.conj g⁻¹ n)) := rfl

end Action

section Transgression

variable {G Q N : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction Q M]
variable [IsDiscreteGModule Q M]

/-- The raw transgression cocycle attached to a section `s : Q → G` of `q` and a function on `N`. -/
noncomputable def tgFun (E : GroupExt G Q N) (s : Q → G) (hs : ∀ y : Q, E.q (s y) = y)
    (φ : N → M) : Q × Q → M :=
  fun p => φ (E.kerLift (s p.1 * s p.2 * (s (p.1 * p.2))⁻¹) (by
    rw [map_mul, map_mul, map_inv, hs, hs, hs]
    simp))

/-- The transgression cocycle of a locally constant `1`-cocycle on `N`, when the section is
continuous and the kernel lifting is continuous. -/
noncomputable def tgCochain (E : GroupExt G Q N) (s : Q → G) (hs : ∀ y : Q, E.q (s y) = y)
    (hscont : Continuous s)
    (hkcont : Continuous fun p : {x : G // E.q x = 1} => E.kerLift p.1 p.2)
    (φ : Cochain1 N M) : Cochain2 Q M :=
  ⟨fun p => φ (E.kerLift (s p.1 * s p.2 * (s (p.1 * p.2))⁻¹) (by
      rw [map_mul, map_mul, map_inv, hs, hs, hs]
      simp)), by
    have h1 : Continuous fun p : Q × Q => s p.1 * s p.2 * (s (p.1 * p.2))⁻¹ :=
      ((hscont.comp continuous_fst).mul (hscont.comp continuous_snd)).mul
        (hscont.comp (continuous_fst.mul continuous_snd)).inv
    exact φ.isLocallyConstant.comp_continuous
      (hkcont.comp (h1.subtype_mk (fun p => by
        rw [map_mul, map_mul, map_inv, hs, hs, hs]
        simp)))⟩

@[simp] lemma tgCochain_apply (E : GroupExt G Q N) (s : Q → G) (hs : ∀ y : Q, E.q (s y) = y)
    (hscont : Continuous s)
    (hkcont : Continuous fun p : {x : G // E.q x = 1} => E.kerLift p.1 p.2)
    (φ : Cochain1 N M) (p : Q × Q) :
    tgCochain E s hs hscont hkcont φ p =
      φ (E.kerLift (s p.1 * s p.2 * (s (p.1 * p.2))⁻¹) (by
        rw [map_mul, map_mul, map_inv, hs, hs, hs]
        simp)) := rfl

end Transgression

end Work.ConCohomology
