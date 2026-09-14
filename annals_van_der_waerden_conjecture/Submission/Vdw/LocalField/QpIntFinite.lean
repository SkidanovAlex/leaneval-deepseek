import Mathlib
import Submission.Vdw.LocalField.ModuleFinite
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers
import Submission.Commons.NumberTheory.Padics.compactSpace_adicCompletionIntegers_rat
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers

open scoped NumberField WithZero Valued
open IsDedekindDomain

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# G2(b) integer level (a3)+(a4): `kpInt` is a finite `QpInt`-module

Continuing `ModuleFinite.lean`'s step (a) at the integer level, this module
closes the chain

* (a1) integer scalar compatibilities — done in `ModuleFinite`
  (`algebraMap_QpInt_int`, `QpInt_smul_int`);
* (a2) containment `ringOfIntegers_image_mem_QpInt_span` — done in
  `ModuleFinite` (the image of `𝓞 K` in `kpInt` lies in the `QpInt`-span of
  the images of an integral `ℤ`-basis);
* **(a3) topology**: `CompactSpace (kpInt p P)` and `CompactSpace (QpInt p)`
  (fleet L103/L104), the continuous algebra map / module topology
  `ContinuousSMul (QpInt p) (kpInt p P)` (built from the continuity of
  `qpIntToKpInt`), and — by the compact-image argument (a continuous image
  of the compact `(QpInt p)^r` is compact, hence closed in the T2 ring
  `kpInt`) — the closedness of the `QpInt`-span of the integral-basis
  images in `kpInt`;
* **(a4) span = ⊤** — the span is closed (a3) and contains the dense image
  of `𝓞 K` (a2 + fleet L102 `ringOfIntegers_dense_in_adicIntegers`), so it
  is everything.

The output is **`Module.Finite (QpInt p) (kpInt p P)`** — the integer-ring
analogue of `ModuleFinite.moduleFinite_kpAdic` — the algebraic input of the
fraction-field rank identity (next G2(b) stone: rank of the finite free
module over the complete DVR equals the fraction-field degree).
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The ring of integers `kpInt p P` of the completion is compact (fleet
L103 instantiated at `v := kprime p P`). -/
instance compactSpace_kpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    CompactSpace (kpInt p P) := by
  simpa [kpInt] using
    (Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers K (kprime p P))

/-- The `ℚ_p`-integers `QpInt p` are compact (fleet L104 instantiated at
`v := qprime p`). -/
instance compactSpace_QpInt (p : ℕ) [Fact (Nat.Prime p)] : CompactSpace (QpInt p) := by
  simpa [QpInt] using (Commons.NumberTheory.Padics.compactSpace_adicCompletionIntegers_rat (qprime p))

/-- The inclusion `QpInt → kpInt` is continuous: its composition with the
codomain inclusion into `kpAdic` is the continuous completed algebra map
`qpToKp` (the domain/codomain topologies are the induced ones, and both
coercions are continuous embeddings). -/
lemma continuous_qpIntToKpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Continuous (qpIntToKpInt p P) := by
  refine (Topology.IsInducing.subtypeVal.continuous_iff).mpr ?_
  change Continuous (fun x : QpInt p => ((qpIntToKpInt p P x : kpInt p P) : kpAdic p P))
  rw [show (fun x : QpInt p => ((qpIntToKpInt p P x : kpInt p P) : kpAdic p P))
        = fun x : QpInt p => qpToKp p P (x : QpAdic p) by
      funext x
      rfl]
  exact (continuous_qpToKp p P).comp continuous_subtype_val

/-- The algebra map `QpInt → kpInt` is continuous (definitionally the ring
hom `qpIntToKpInt` of the `kpIntAlgebraQpInt` algebra structure). -/
lemma algebraMap_QpInt_kpInt_eq (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    algebraMap (QpInt p) (kpInt p P) = qpIntToKpInt p P := by
  rw [RingHom.algebraMap_toAlgebra]

lemma continuous_algebraMap_QpInt_kpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Continuous (algebraMap (QpInt p) (kpInt p P)) := by
  rw [algebraMap_QpInt_kpInt_eq]
  exact continuous_qpIntToKpInt p P

/-- The module topology of `kpInt` over `QpInt`: the scalar action is
continuous (a continuous algebra map into a continuous-multiplication ring
makes the module a topological module — Mathlib
`continuousSMul_of_algebraMap`). -/
instance continuousSMul_QpInt_kpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    ContinuousSMul (QpInt p) (kpInt p P) := by
  refine continuousSMul_of_algebraMap (QpInt p) (kpInt p P) ?_
  rw [algebraMap_QpInt_kpInt_eq]
  exact continuous_qpIntToKpInt p P

/-- Closure inside a subtype: the closure of a set of a subtype (with the
induced topology) is the preimage of the closure of its image in the
ambient space. -/
lemma subtype_closure_preimage {α : Type*} [TopologicalSpace α] {p : α → Prop}
    (s : Set {x : α // p x}) :
    closure s = (fun y : {x : α // p x} => (y : α)) ⁻¹'
      closure ((fun y : {x : α // p x} => (y : α)) '' s) := by
  have hInd : Topology.IsInducing (fun y : {x : α // p x} => (y : α)) := ⟨rfl⟩
  exact Topology.IsInducing.closure_eq_preimage_closure_image hInd s

/-- The dense image of `𝓞 K` in `kpInt` (fleet L102 instantiated): for every
`x : kpInt`, its ambient representative lies in the closure of the image of
`𝓞 K` (the image of `ringOfIntegersToKpInt` coerced to the ambient). -/
lemma kpInt_mem_closure_ringOfIntegers (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (x : kpInt p P) :
    (x : kpAdic p P) ∈ closure
      {y : kpAdic p P | ∃ r : 𝓞 K, (algebraMap K (kpAdic p P) (r : K)) = y} := by
  simpa [kpAdic, kpInt] using
    (Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers K (kprime p P) x)

/-- **The `QpInt`-span of the images of an integral `ℤ`-basis of `𝓞 K` is all
of `kpInt`.**  (a3)+(a4): the span is closed (compact image of the compact
`(QpInt p)^r` in the T2 ring `kpInt`; the linear-combination map
`F : (Fin r → QpInt p) → kpInt`, `t ↦ ∑ tⱼ • gⱼ` is continuous and has range
exactly the span), and it contains the dense image of `𝓞 K`
(`ringOfIntegers_image_mem_QpInt_span` + fleet L102 density). -/
theorem qpIntSpan_basis_eq_top (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Submodule.span (QpInt p)
      (Set.range (fun i : Fin (Module.finrank ℤ (𝓞 K)) =>
        ringOfIntegersToKpInt p P (Module.finBasis ℤ (𝓞 K) i : 𝓞 K))) = ⊤ := by
  classical
  let r0 := Module.finrank ℤ (𝓞 K)
  let b : Module.Basis (Fin r0) ℤ (𝓞 K) := Module.finBasis ℤ (𝓞 K)
  let φ : 𝓞 K →+* kpInt p P := ringOfIntegersToKpInt p P
  let g : Fin r0 → kpInt p P := fun i => φ (b i)
  let T : Submodule (QpInt p) (kpInt p P) := Submodule.span (QpInt p) (Set.range g)
  let F : (Fin r0 → QpInt p) → kpInt p P :=
    fun t => ∑ j ∈ (Finset.univ : Finset (Fin r0)), t j • g j
  -- (a3) part 1: F is continuous (each summand is a projection times a fixed
  -- generator, the module action is continuous).
  have hcontF : Continuous F := by
    dsimp [F]
    refine continuous_finsetSum (ι := Fin r0) (M := kpInt p P) (X := Fin r0 → QpInt p)
      (f := fun j t => t j • g j) (Finset.univ) ?_
    intro j hj
    exact (continuous_apply j).smul continuous_const
  -- (a3) part 2: the range of F is exactly the span T.
  have hset : Set.range F = (T : Set (kpInt p P)) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      change (∑ j ∈ (Finset.univ : Finset (Fin r0)), t j • g j) ∈ T
      refine T.sum_mem ?_
      intro j hj
      exact Submodule.smul_mem T (t j) (Submodule.subset_span (by exact ⟨j, rfl⟩ : g j ∈ Set.range g))
    · intro hy
      change y ∈ T at hy
      have hsp : y ∈ Submodule.span (QpInt p) (Set.range g) := by
        simpa [T] using hy
      rcases (Finsupp.mem_span_range_iff_exists_finsupp (v := g) (x := y)).mp hsp with ⟨c, hc⟩
      refine ⟨fun j : Fin r0 => c j, ?_⟩
      dsimp [F]
      rw [← hc]
      rw [Finsupp.sum_fintype c (fun i a => a • g i) (by intro i; exact zero_smul _ _)]
  -- (a3) part 3: range F is compact (continuous image of the compact
  -- product of copies of the compact ring QpInt), hence closed (T2).
  have hclosedR : IsClosed (Set.range F) := by
    have himg : IsCompact (F '' (Set.univ : Set (Fin r0 → QpInt p))) :=
      isCompact_univ.image hcontF
    have hr : Set.range F = F '' (Set.univ : Set (Fin r0 → QpInt p)) := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t, trivial, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, rfl⟩
    rw [hr]
    exact himg.isClosed
  have hTclosed : IsClosed (T : Set (kpInt p P)) := by
    rw [← hset]
    exact hclosedR
  -- (a2)+(L102): the φ-image of 𝓞 K is dense in kpInt and sits in T.
  let Sφ : Set (kpInt p P) := Set.range (fun r : 𝓞 K => (ringOfIntegersToKpInt p P r : kpInt p P))
  have hSsubT : Sφ ⊆ (T : Set (kpInt p P)) := by
    rintro y ⟨r, rfl⟩
    change (ringOfIntegersToKpInt p P r : kpInt p P) ∈ T
    simpa [T, g, φ, b] using ringOfIntegers_image_mem_QpInt_span p P r
  have hScl : ∀ x : kpInt p P, x ∈ closure (Sφ : Set (kpInt p P)) := by
    intro x
    rw [subtype_closure_preimage (α := kpAdic p P)
      (p := fun y : kpAdic p P => y ∈ (kprime p P).adicCompletionIntegers K) (Sφ : Set (kpInt p P))]
    change (x : kpAdic p P) ∈ closure
      ((fun y : kpInt p P => (y : kpAdic p P)) '' (Sφ : Set (kpInt p P)))
    have himg : (fun y : kpInt p P => (y : kpAdic p P)) '' (Sφ : Set (kpInt p P)) =
        {y : kpAdic p P | ∃ r : 𝓞 K, (algebraMap K (kpAdic p P) (r : K)) = y} := by
      ext y
      constructor
      · rintro ⟨q, ⟨r, rfl⟩, rfl⟩
        refine ⟨r, ?_⟩
        rfl
      · rintro ⟨r, rfl⟩
        refine ⟨(ringOfIntegersToKpInt p P r : kpInt p P), ?_, ?_⟩
        · exact ⟨r, rfl⟩
        · rfl
    rw [himg]
    exact kpInt_mem_closure_ringOfIntegers p P x
  -- (a4): closure(Sφ) ⊆ T (T closed ⊇ Sφ) and closure(Sφ) = ⊤, so T = ⊤.
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    trivial
  · intro hx
    exact (closure_minimal hSsubT hTclosed) (hScl x)

/-- **`kpInt p P` is finitely generated as a `QpInt p`-module**: the images
of an integral `ℤ`-basis of `𝓞 K` (a finite set) generate all of `kpInt`
over `QpInt` (`qpIntSpan_basis_eq_top`). -/
noncomputable instance moduleFinite_kpInt_QpInt (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.Finite (QpInt p) (kpInt p P) := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℤ (𝓞 K))) ℤ (𝓞 K) := Module.finBasis ℤ (𝓞 K)
  let fins : Finset (kpInt p P) := Finset.univ.image
    (fun i : Fin (Module.finrank ℤ (𝓞 K)) => ringOfIntegersToKpInt p P (b i))
  exact Module.Finite.of_fg_top ⟨fins, by
    rw [← qpIntSpan_basis_eq_top (p := p) (P := P)]
    congr 1
    ext x
    simp [fins, b]⟩

end
end Submission.Vdw.LocalField
