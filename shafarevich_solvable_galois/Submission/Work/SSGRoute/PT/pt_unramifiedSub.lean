import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.PT.vanishingInertia_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The unramified subgroup of the local `H¹`, and the cocycle-level/class-level bridge

This module supplies the local-linear-algebra layer that the relaxed Poitou–Tate assembly
(`Work.SSGRoute.PT.restrictedProduct_relaxation`, `Work.SSGRoute.pt_selmer_relaxed`) and the
reciprocity lane (`Work.SSGRoute.PT.pt_canonical_aux`) use:

* `Work.SSGRoute.inertiaTrivialCocycles` — the locally constant `1`-cocycles on the decomposition
  group `D_B` that **vanish on the inertia subgroup** `I_B`;
* `Work.SSGRoute.unramifiedSub` — their image in the local `H¹(D_B, M)`, i.e. the *unramified*
  subgroup `H¹_ur(D_B, M) ≤ H¹(D_B, M)`;
* `Work.SSGRoute.toClass_mem_unramifiedSub_iff` — **the bridge**: at a place `B` that is
  unramified in `K`, the local *class* of a locally constant cocycle `b` is unramified (it lies in
  `unramifiedSub`) **iff** the cocycle `b` itself vanishes on `I_B`.

The content of the last statement is the resolution of the "cocycle-level versus class-level"
watch-out recorded in `Submission/Work/SSGRoute/pt_selmer_relaxed.lean` and in
`SSGRoute/PT/pt_selmer_counting.lean`: the workspace phrases the Selmer conditions *on the cocycle*
(`ε σ = 0` for `σ ∈ I_B`), whereas the classical statements (Milne, *Arithmetic Duality Theorems*;
Schmidt–Wingberg) are *class-level* ("the local class is unramified").  The two agree exactly when
`I_B` acts trivially on `M` — which is guaranteed in the relevant range, because the coefficients
`M` are `Gal(K/k)`-modules and every place `B` of the Selmer range is unramified in `K` (the
`K`-ramified places are conjugates of the places in `S`, and `S` is excluded).  Indeed, if `I_B`
acts trivially on `M` then a coboundary `δm` vanishes on `I_B`, so `b = c + δm` with `c` vanishing
on `I_B` forces `b` itself to vanish on `I_B`; the converse is immediate from the definition.

The final lemma, `Work.SSGRoute.exists_finset_localClass_unramified`, records that a *global*
locally constant cocycle has unramified local class at all but finitely many finite places (up to
conjugacy): this is the class-level form of `Work.SSGRoute.PT.vanishingInertia_finite`, and it is
what makes the localisation of a global class land in the *restricted* product
`Πʳ_B [H¹(D_B, M), H¹_ur(D_B, M)]` used by the relaxation lemma.

## A design warning for the restricted-product instantiation (found by review, 2026-09-27)

The index type of that restricted product must be one place *per prime of `k`* (equivalently, one
place per `IsConjPlace`-class), **not** the type `{A : ValuationSubring Ω // IsFinPlace k A}` of all
places of `Ω`: the "unramified off a finite set" condition of `Πʳ` (the cofinite filter) would
otherwise be false.  Indeed `{A | toClass … A ∉ unramifiedSub … A}` is a union of *full*
`Gal(Ω/k)`-orbits, and the orbit of a place is infinite as soon as it is non-empty (a prime of `k`
that is not split has infinitely many places above it), so a single ramified prime gives infinitely
many bad places of `Ω` — the counterexample being a globally ramified class such as an inflated
quadratic character.  So the instantiation has to index by the conjugacy quotient `Quot` of the
finite places (or by the places of `k`), which in turn needs

* the conjugacy-invariance of the local conditions (`Work.SSGRoute.PT.inertiaVanishing_conj` for
  the inertia-vanishing, `place_basics.isCoboundaryOn_conj` for the coboundary condition), and
* the identification of the local `H¹`'s at conjugate places (`h1loc_conjLinearMap`).

With that indexing, `unramifiedSub` is well defined on the quotient and the cofinite filter is
correct.  Compare `Work.SSGRoute.exists_finset_localClass_unramified`, which is the same statement
in the "one place per class" form that needs no quotient.
-/

namespace Work.SSGRoute

set_option linter.unusedSectionVars false

noncomputable section

open scoped Pointwise
open _root_.SSGRoute

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-! ## The class of a locally constant cocycle, as a quotient map -/

/-- The class map `toClass` computed on a locally constant cocycle: it is the quotient map
`lcCocycles H → H¹(H, M)`. -/
theorem toClass_eq_mkQ (H : Subgroup (Ω ≃ₐ[k] Ω)) {f : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ lcCocycles p k Ω K M H) :
    toClass p k Ω K M H f =
      Submodule.mkQ (Submodule.comap (lcCocycles p k Ω K M H).subtype
        (coboundaries p k Ω K M H)) ⟨f, hf⟩ := by
  rw [toClass, dif_pos hf]

/-- The class map is additive, computed on locally constant cocycles.  (A local copy of
`Work.SSGRoute.PT.toClass_sub`, so that this module need not import the counting lane.) -/
theorem toClass_sub_of_mem (H : Subgroup (Ω ≃ₐ[k] Ω)) {f g : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ lcCocycles p k Ω K M H) (hg : g ∈ lcCocycles p k Ω K M H) :
    toClass p k Ω K M H (f - g) =
      toClass p k Ω K M H f - toClass p k Ω K M H g := by
  have hfg : (f - g) ∈ lcCocycles p k Ω K M H :=
    (lcCocycles p k Ω K M H).sub_mem hf hg
  have hsub : (⟨f - g, hfg⟩ : ↥(lcCocycles p k Ω K M H)) =
      ⟨f, hf⟩ - ⟨g, hg⟩ := Subtype.ext rfl
  rw [toClass_eq_mkQ p k Ω K M H hfg, toClass_eq_mkQ p k Ω K M H hf,
    toClass_eq_mkQ p k Ω K M H hg, hsub, map_sub]

/-! ## The inertia-trivial cocycles -/

/-- The locally constant `1`-cocycles on the decomposition group `D_B` of `B` that **vanish on the
inertia subgroup** `I_B`.  Their classes in `H¹(D_B, M)` are the *unramified* classes. -/
def inertiaTrivialCocycles (B : ValuationSubring Ω) :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) where
  carrier := {f | f ∈ lcCocycles p k Ω K M (decomp k B) ∧
    ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ inertiaSub k Ω B → f σ = 0}
  zero_mem' := ⟨(lcCocycles p k Ω K M (decomp k B)).zero_mem, fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf, hf0⟩ ⟨hg, hg0⟩
    refine ⟨(lcCocycles p k Ω K M (decomp k B)).add_mem hf hg, fun σ hσ => ?_⟩
    simp only [Pi.add_apply, hf0 σ hσ, hg0 σ hσ, add_zero]
  smul_mem' := by
    rintro c f ⟨hf, hf0⟩
    refine ⟨(lcCocycles p k Ω K M (decomp k B)).smul_mem c hf, fun σ hσ => ?_⟩
    simp only [Pi.smul_apply, hf0 σ hσ, smul_zero]

@[simp] theorem mem_inertiaTrivialCocycles (B : ValuationSubring Ω) {f : (Ω ≃ₐ[k] Ω) → M} :
    f ∈ inertiaTrivialCocycles p k Ω K M B ↔
      f ∈ lcCocycles p k Ω K M (decomp k B) ∧
        ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ inertiaSub k Ω B → f σ = 0 := Iff.rfl

theorem inertiaTrivialCocycles_le_lcCocycles (B : ValuationSubring Ω) :
    inertiaTrivialCocycles p k Ω K M B ≤ lcCocycles p k Ω K M (decomp k B) :=
  fun _ hf => hf.1

/-! ## The unramified subgroup of the local `H¹` -/

/-- The composite "inertia-trivial cocycle ↦ its class in the local `H¹`". -/
def inertiaTrivialToClass (B : ValuationSubring Ω) :
    ↥(inertiaTrivialCocycles p k Ω K M B) →ₗ[ZMod p] (H1loc p k Ω K M (decomp k B)) :=
  (Submodule.mkQ (Submodule.comap (lcCocycles p k Ω K M (decomp k B)).subtype
      (coboundaries p k Ω K M (decomp k B)))).comp
    (Submodule.inclusion (inertiaTrivialCocycles_le_lcCocycles p k Ω K M B))

/-- The value of that composite: the class in `H¹(D_B, M)` of the underlying cocycle. -/
@[simp] theorem inertiaTrivialToClass_apply (B : ValuationSubring Ω)
    (y : ↥(inertiaTrivialCocycles p k Ω K M B)) :
    inertiaTrivialToClass p k Ω K M B y = toClass p k Ω K M (decomp k B) y.1 := by
  rw [toClass_eq_mkQ p k Ω K M (decomp k B) y.2.1]
  exact congrArg (Submodule.mkQ (Submodule.comap (lcCocycles p k Ω K M (decomp k B)).subtype
    (coboundaries p k Ω K M (decomp k B)))) (Subtype.ext rfl)

/-- The **unramified subgroup** `H¹_ur(D_B, M) ≤ H¹(D_B, M)`: the image of the locally constant
cocycles on `D_B` that vanish on the inertia subgroup `I_B`. -/
abbrev unramifiedSub (B : ValuationSubring Ω) :
    Submodule (ZMod p) (H1loc p k Ω K M (decomp k B)) :=
  Submodule.map (inertiaTrivialToClass p k Ω K M B) ⊤

/-- **Characterisation of `unramifiedSub`.**  A class `[b]` (of a locally constant cocycle `b` on
`D_B`) is unramified iff it is also the class of a locally constant cocycle `c` that vanishes on
`I_B`. -/
theorem mem_unramifiedSub_iff (B : ValuationSubring Ω) (b : (Ω ≃ₐ[k] Ω) → M)
    (hb : b ∈ lcCocycles p k Ω K M (decomp k B)) :
    toClass p k Ω K M (decomp k B) b ∈ unramifiedSub p k Ω K M B ↔
      ∃ c : (Ω ≃ₐ[k] Ω) → M,
        c ∈ lcCocycles p k Ω K M (decomp k B) ∧
          (∀ σ : Ω ≃ₐ[k] Ω, σ ∈ inertiaSub k Ω B → c σ = 0) ∧
          toClass p k Ω K M (decomp k B) c = toClass p k Ω K M (decomp k B) b := by
  constructor
  · intro h
    obtain ⟨y, _, hy⟩ := Submodule.mem_map.mp h
    rw [inertiaTrivialToClass_apply] at hy
    exact ⟨y.1, y.2.1, y.2.2, hy⟩
  · rintro ⟨c, hc, hc0, heq⟩
    exact Submodule.mem_map.mpr ⟨⟨c, hc, hc0⟩, Submodule.mem_top, by
      rw [inertiaTrivialToClass_apply]; exact heq⟩

/-- **A representative of an unramified class that vanishes on `I_B`.**  Every element of the
unramified subgroup is the class of a locally constant cocycle on `D_B` that vanishes on `I_B`. -/
theorem exists_toClass_mem_unramifiedSub (B : ValuationSubring Ω) (x : H1loc p k Ω K M (decomp k B))
    (hx : x ∈ unramifiedSub p k Ω K M B) :
    ∃ b : (Ω ≃ₐ[k] Ω) → M, b ∈ lcCocycles p k Ω K M (decomp k B) ∧
      (∀ σ : Ω ≃ₐ[k] Ω, σ ∈ inertiaSub k Ω B → b σ = 0) ∧
      toClass p k Ω K M (decomp k B) b = x := by
  obtain ⟨b, hb, hbt⟩ := toClass_surjective p k Ω K M (decomp k B) x
  have hxb : toClass p k Ω K M (decomp k B) b ∈ unramifiedSub p k Ω K M B := by
    rw [hbt]; exact hx
  obtain ⟨c, hc, hc0, heq⟩ := (mem_unramifiedSub_iff p k Ω K M B b hb).mp hxb
  exact ⟨c, hc, hc0, by rw [heq, hbt]⟩

/-- **The easy direction of the bridge**: a cocycle vanishing on `I_B` has unramified class. -/
theorem toClass_mem_unramifiedSub_of_inertia_eq_zero (B : ValuationSubring Ω)
    {b : (Ω ≃ₐ[k] Ω) → M} (hb : b ∈ lcCocycles p k Ω K M (decomp k B))
    (h0 : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ inertiaSub k Ω B → b σ = 0) :
    toClass p k Ω K M (decomp k B) b ∈ unramifiedSub p k Ω K M B :=
  (mem_unramifiedSub_iff p k Ω K M B b hb).mpr ⟨b, hb, h0, rfl⟩

/-! ## The cocycle-level/class-level bridge -/

/-- **The bridge at a place unramified in `K`.**  If `B` is unramified in `K` (so that every
element of `I_B` acts trivially on the coefficient module `M`, a `Gal(K/k)`-module), then for a
locally constant cocycle `b` on `D_B` the following are equivalent:

* the local *class* of `b` is unramified, i.e. `[b] ∈ H¹_ur(D_B, M)`;
* the *cocycle* `b` vanishes on `I_B`.

This is the precise sense in which the workspace's cocycle-level Selmer conditions
(`b σ = 0` for `σ ∈ I_B`) agree with the classical class-level ones. -/
theorem toClass_mem_unramifiedSub_iff (B : ValuationSubring Ω) (hunr : ¬ IsRamifiedIn k K B)
    (b : (Ω ≃ₐ[k] Ω) → M) (hb : b ∈ lcCocycles p k Ω K M (decomp k B)) :
    toClass p k Ω K M (decomp k B) b ∈ unramifiedSub p k Ω K M B ↔
      ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ inertiaSub k Ω B → b σ = 0 := by
  classical
  -- every inertia element lies in the fixing subgroup of `K` when `B` is unramified in `K`
  have hfix : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ inertiaSub k Ω B → σ ∈ K.fixingSubgroup := by
    intro σ hσ
    by_contra hcon
    exact hunr ⟨σ, hσ, hcon⟩
  have hres : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ inertiaSub k Ω B → SSGRoute.res k K σ = 1 := by
    intro σ hσ
    have hker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
      IntermediateField.restrictNormalHom_ker K
    exact MonoidHom.mem_ker.mp (hker ▸ hfix σ hσ)
  constructor
  · intro h σ hσ
    obtain ⟨c, hc, hc0, heq⟩ := (mem_unramifiedSub_iff p k Ω K M B b hb).mp h
    -- `b - c` is a coboundary on `D_B`
    have hsub : (b - c) ∈ lcCocycles p k Ω K M (decomp k B) :=
      (lcCocycles p k Ω K M (decomp k B)).sub_mem hb hc
    have hcob : (b - c) ∈ coboundaries p k Ω K M (decomp k B) := by
      have h0 : toClass p k Ω K M (decomp k B) (b - c) = 0 := by
        rw [toClass_sub_of_mem p k Ω K M (decomp k B) hb hc, heq, sub_self]
      exact (toClass_eq_zero_iff p k Ω K M (decomp k B) hsub).mp h0
    obtain ⟨m, hm⟩ := hcob
    have hσD : σ ∈ decomp k B := hσ.1
    have h1 : (b - c) σ = 0 := by
      rw [hm σ hσD, hres σ hσ, one_smul, sub_self]
    have h2 : b σ - c σ = 0 := by simpa using h1
    rw [sub_eq_zero] at h2
    rw [h2, hc0 σ hσ]
  · intro h0
    exact toClass_mem_unramifiedSub_of_inertia_eq_zero p k Ω K M B hb h0

/-! ## The bridge in the Selmer range, and the local conditions of the dual Selmer group -/

/-- **The bridge in the Selmer range.**  If `S` is a finite set of places that contains, up to
conjugacy, every place ramified in `K` and every place above `p` (the hypothesis `hSram`), then at
every finite place `B` outside the conjugacy classes of `S` the local class of a cocycle `b` on
`D_B` is unramified **iff** `b` vanishes on `I_B`.  This is the form in which the bridge is applied:
the Selmer range of `Work.SSGRoute.pt_selmer_relaxed` consists exactly of the finite places outside
the classes of `S`. -/
theorem toClass_mem_unramifiedSub_iff_of_not_isConjPlace (S : Finset (ValuationSubring Ω))
    (hSram : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (IsRamifiedIn k K B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, IsConjPlace k A B)
    (B : ValuationSubring Ω) (hB : IsFinPlace k B) (hBout : ∀ A ∈ S, ¬ IsConjPlace k A B)
    (b : (Ω ≃ₐ[k] Ω) → M) (hb : b ∈ lcCocycles p k Ω K M (decomp k B)) :
    toClass p k Ω K M (decomp k B) b ∈ unramifiedSub p k Ω K M B ↔
      ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ inertiaSub k Ω B → b σ = 0 := by
  refine toClass_mem_unramifiedSub_iff p k Ω K M B ?_ b hb
  intro hram
  obtain ⟨A, hA, hconj⟩ := hSram B hB (Or.inl hram)
  exact hBout A hA hconj

/-- **The local conditions of the dual Selmer group, in class form.**  For a *global* locally
constant cocycle `b` satisfying the relaxed dual local conditions with respect to `S` and a finite
Galois extension `N` (coboundary at the finite places outside the classes of `S` that split in `N`,
inertia-vanishing at the other finite places outside the classes of `S`), the local *class* of `b`
at every finite place `B` outside the classes of `S` is trivial (if `B` splits in `N`) or
unramified (otherwise).

This is the translation of `Work.SSGRoute.PT.IsDualSelmerClass` into the class-level vocabulary in
which the local pairings and the restricted products live. -/
theorem dualSelmer_localClass (S : Finset (ValuationSubring Ω))
    (hSram : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (IsRamifiedIn k K B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, IsConjPlace k A B)
    (N : IntermediateField k Ω)
    (b : (Ω ≃ₐ[k] Ω) → M) (hb : b ∈ lcCocycles p k Ω K M ⊤)
    (hsplit : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S, ¬ IsConjPlace k A B) → IsSplitIn k N B →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (decomp k B) b)
    (hnon : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S, ¬ IsConjPlace k A B) → ¬ IsSplitIn k N B →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0)
    (B : ValuationSubring Ω) (hB : IsFinPlace k B) (hBout : ∀ A ∈ S, ¬ IsConjPlace k A B) :
    (IsSplitIn k N B → toClass p k Ω K M (decomp k B) b = 0) ∧
      (¬ IsSplitIn k N B → toClass p k Ω K M (decomp k B) b ∈ unramifiedSub p k Ω K M B) := by
  have hmem : b ∈ lcCocycles p k Ω K M (decomp k B) :=
    ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hb.1, isLocConstOn_mono le_top hb.2⟩
  refine ⟨fun hs => ?_, fun hns => ?_⟩
  · exact (toClass_eq_zero_iff p k Ω K M (decomp k B) hmem).mpr (hsplit B hB hBout hs)
  · exact (toClass_mem_unramifiedSub_iff_of_not_isConjPlace p k Ω K M S hSram B hB hBout b
      hmem).mpr (hnon B hB hBout hns)

/-! ## Unramified classes are mutually annihilating (class-level clause (6)) -/

/-- **Unramified classes annihilate each other.**  If a local pairing `pair` on the locally
constant cochains at `A` vanishes whenever both arguments vanish on the inertia subgroup `I_A` (this
is clause (6) of the canonical local Tate pairing, `PTembedding.localTatePairing_canonical`), and if
`Bh` is the induced pairing on the local `H¹`'s (with the computation rule `hB`), then `Bh` vanishes
on the unramified subgroups of both arguments.

This is the *class-level* form of clause (6), and it is what lets the relaxed Poitou–Tate
relaxation (`Work.SSGRoute.PT.restrictedProduct_relaxation`) be applied with
`U'_A := (U_A)^⊥`, where `U_A = unramifiedSub … A` is the unramified subgroup: the dual Selmer
classes are unramified at almost every place (`exists_finset_localClass_unramified`) and hence lie in
`U_A^⊥`. -/
theorem pairing_annihilates_unramifiedSub
    (M' : Type) [AddCommGroup M'] [Module (ZMod p) M'] [DistribMulAction (K ≃ₐ[k] K) M']
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M']
    (A : ValuationSubring Ω)
    (pair : ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → M') → ZMod p)
    (hr : ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → M'),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (decomp k A) a ∧
        SSGRoute.IsLocConstOn (decomp k A) a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (decomp k A) b ∧
        SSGRoute.IsLocConstOn (decomp k A) b) →
      (∀ σ : Ω ≃ₐ[k] Ω, σ ∈ inertiaSub k Ω A → a σ = 0 ∧ b σ = 0) →
      pair a b = 0)
    (Bh : H1loc p k Ω K M (decomp k A) →ₗ[ZMod p]
        H1loc p k Ω K M' (decomp k A) →ₗ[ZMod p] ZMod p)
    (hB : ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → M'),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (decomp k A) a ∧
        SSGRoute.IsLocConstOn (decomp k A) a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (decomp k A) b ∧
        SSGRoute.IsLocConstOn (decomp k A) b) →
      Bh (toClass p k Ω K M (decomp k A) a) (toClass p k Ω K M' (decomp k A) b) = pair a b)
    (x : H1loc p k Ω K M (decomp k A)) (hx : x ∈ unramifiedSub p k Ω K M A)
    (y : H1loc p k Ω K M' (decomp k A)) (hy : y ∈ unramifiedSub p k Ω K M' A) :
    Bh x y = 0 := by
  obtain ⟨a, ha, ha0, hax⟩ := exists_toClass_mem_unramifiedSub p k Ω K M A x hx
  obtain ⟨b, hb, hb0, hby⟩ := exists_toClass_mem_unramifiedSub p k Ω K M' A y hy
  rw [← hax, ← hby, hB a b ha hb]
  exact hr a b ha hb (fun σ hσ => ⟨ha0 σ hσ, hb0 σ hσ⟩)

/-! ## Unramified local class almost everywhere -/

/-- **A global locally constant cocycle has unramified local class at all but finitely many finite
places** (one place per conjugacy class).  This is the class-level form of
`Work.SSGRoute.PT.vanishingInertia_finite`, and it is the reason the localisation of a global class
lands in the *restricted* product `Πʳ_B [H¹(D_B, M), H¹_ur(D_B, M)]`. -/
theorem exists_finset_localClass_unramified (b : (Ω ≃ₐ[k] Ω) → M)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (hl : SSGRoute.IsLocConstOn ⊤ b) :
    ∃ S : Finset (ValuationSubring Ω),
      (∀ A ∈ S, SSGRoute.IsFinPlace k A) ∧
      (∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B) ∧
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        toClass p k Ω K M (decomp k B) b ∈ unramifiedSub p k Ω K M B := by
  classical
  obtain ⟨S, hSfin, hSdisj, hS0⟩ :=
    Work.SSGRoute.PT.vanishingInertia_finite k Ω K M b hb hl
  refine ⟨S, hSfin, hSdisj, fun B hB hBout => ?_⟩
  have hmem : b ∈ lcCocycles p k Ω K M (decomp k B) :=
    ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hb, isLocConstOn_mono le_top hl⟩
  exact toClass_mem_unramifiedSub_of_inertia_eq_zero p k Ω K M B hmem
    (fun σ hσ => hS0 B hB hBout σ hσ)

end

end Work.SSGRoute
