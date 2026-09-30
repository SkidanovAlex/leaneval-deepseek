import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Cohomology.exists_capH
import Submission.Work.Cohomology.kronH_bijective_field
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# AREA EMZ (`Work.Pi6.EMTableZ`) — the vocabulary of the integral-table argument

This file fixes the objects used by the EMZ argument (the lead's §7 of `REFS/NOTES_LEAD_PI6.md`):
the subgroup `p · M` of `p`-multiples and the `p`-torsion subgroup `M[p]` of an abelian group, the
statement `BocksteinLES p` of the Bockstein long exact sequence with coefficients `ℤ/p`, and the
basic cardinality bridges used to turn the rank bounds of `EMMod2`/`EMOdd` into cardinality
bounds.

The mathematics lives in the sibling modules (`Submission/Work/Pi6/EMZ/*.lean`).
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMZ

noncomputable section

/-- **The subgroup `p · M` of `p`-multiples** of an abelian group, as the range of the linear map
"multiplication by `p`". -/
def pH (p : ℕ) (M : Type) [AddCommGroup M] : AddSubgroup M :=
  ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M)).range.toAddSubgroup

/-- **Membership in `p · M`**: `x` is a `p`-multiple. -/
theorem mem_pH {p : ℕ} {M : Type} [AddCommGroup M] {x : M} :
    x ∈ pH p M ↔ ∃ y : M, (p : ℤ) • y = x :=
  LinearMap.mem_range

/-- **The `p`-torsion subgroup `M[p]`** of an abelian group, as the kernel of the linear map
"multiplication by `p`". -/
def torsP (p : ℕ) (M : Type) [AddCommGroup M] : AddSubgroup M :=
  ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M)).ker.toAddSubgroup

/-- **Membership in `M[p]`**: `x` is killed by `p`. -/
theorem mem_torsP {p : ℕ} {M : Type} [AddCommGroup M] {x : M} :
    x ∈ torsP p M ↔ (p : ℤ) • x = 0 :=
  LinearMap.mem_ker

/-- `M[p]` depends only on the `nsmul`-`p`-torsion: the membership test with `ℤ`-scalars and with
`ℕ`-scalars agree. -/
theorem mem_torsP' {p : ℕ} {M : Type} [AddCommGroup M] {x : M} :
    x ∈ torsP p M ↔ p • x = 0 := by
  rw [mem_torsP, Nat.cast_smul_eq_nsmul]

/-- `p · M` depends only on the `nsmul`: `p · M` is the range of `y ↦ p • y`. -/
theorem mem_pH' {p : ℕ} {M : Type} [AddCommGroup M] {x : M} :
    x ∈ pH p M ↔ ∃ y : M, p • y = x := by
  rw [mem_pH]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rwa [Nat.cast_smul_eq_nsmul] at hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by rwa [Nat.cast_smul_eq_nsmul]⟩

/-- **`G ⧸ p·G` is trivial iff `G` is `p`-divisible.** -/
theorem subsingleton_quot_pH_iff {p : ℕ} {G : Type} [AddCommGroup G] :
    Subsingleton (G ⧸ pH p G) ↔ ∀ x : G, ∃ y : G, p • y = x := by
  constructor
  · intro h x
    have : (QuotientAddGroup.mk x : G ⧸ pH p G) = 0 := Subsingleton.elim _ _
    rw [QuotientAddGroup.eq_zero_iff] at this
    exact mem_pH'.mp this
  · refine fun h => ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective b
    have ha : (a : G ⧸ pH p G) = 0 := by
      obtain ⟨y, hy⟩ := h a
      rw [← hy]
      exact (QuotientAddGroup.eq_zero_iff _).mpr (mem_pH'.mpr ⟨y, rfl⟩)
    have hb : (b : G ⧸ pH p G) = 0 := by
      obtain ⟨y, hy⟩ := h b
      rw [← hy]
      exact (QuotientAddGroup.eq_zero_iff _).mpr (mem_pH'.mpr ⟨y, rfl⟩)
    rw [ha, hb]

/-- **`G[p]` is trivial iff `G` has no `p`-torsion.** -/
theorem subsingleton_torsP_iff {p : ℕ} {G : Type} [AddCommGroup G] :
    Subsingleton (torsP p G) ↔ ∀ x : G, p • x = 0 → x = 0 := by
  constructor
  · intro h x hx
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, mem_torsP'.mpr hx⟩ : torsP p G) ⟨0, by simp⟩)
  · intro h
    refine ⟨fun a b => ?_⟩
    have ha : (a : G) = 0 := h a (mem_torsP'.mp a.2)
    have hb : (b : G) = 0 := h b (mem_torsP'.mp b.2)
    exact Subtype.ext (by rw [ha, hb])

end

noncomputable section

/-- **The mod-`p` Bockstein long exact sequence.**  There are additive maps

* `red n : Hₙ(X;ℤ) →+ Hₙ(X;ℤ/p)`, the reduction mod `p` (coefficient change `ℤ → ℤ/p`);
* `del n : Hₙ₊₁(X;ℤ/p) →+ Hₙ(X;ℤ)`, the Bockstein connecting map,

making the sequence
`Hₙ₊₁(X;ℤ) --·p--> Hₙ₊₁(X;ℤ) --red--> Hₙ₊₁(X;ℤ/p) --del--> Hₙ(X;ℤ) --·p--> Hₙ(X;ℤ)`
exact at all three displayed spots, for every space `X` and every `n`.

Route: the short exact sequence of coefficient modules `0 → ℤ --·p--> ℤ → ℤ/p → 0`, its image
under the coefficient extension `- ⊗ ℤ/p` (`Work.SSS.expTens`, `Work.SSS.expTensShort`,
`Work.SSS.expTensShort_shortExact`) and the long exact sequence in homology
(`HomologicalComplex.HomologySequence`); the identification of `Hₙ(C_*(X;ℤ) ⊗ ℤ/p)` with
`Hₙ(X;ℤ/p)` is `Work.SSS.chainCoeffExpIso` together with
`Work.StemsB.SphRat.homologyMapBaseChange`. -/
def BocksteinLES (p : ℕ) : Prop :=
  ∃ (red : ∀ {X : Type} [TopologicalSpace X] (n : ℕ), Work.Pi6.HR ℤ X n →+ Work.Pi6.HR (ZMod p) X n)
    (del : ∀ {X : Type} [TopologicalSpace X] (n : ℕ),
      Work.Pi6.HR (ZMod p) X (n + 1) →+ Work.Pi6.HR ℤ X n),
    (∀ (X : Type) [TopologicalSpace X] (n : ℕ),
      Function.Exact (fun x : Work.Pi6.HR ℤ X n => (p : ℤ) • x) ⇑(red (X := X) n)) ∧
    (∀ (X : Type) [TopologicalSpace X] (n : ℕ),
      Function.Exact ⇑(red (X := X) (n + 1)) ⇑(del (X := X) n)) ∧
    (∀ (X : Type) [TopologicalSpace X] (n : ℕ),
      Function.Exact ⇑(del (X := X) n) (fun x : Work.Pi6.HR ℤ X n => (p : ℤ) • x))

end

end Work.Pi6.EMZ
