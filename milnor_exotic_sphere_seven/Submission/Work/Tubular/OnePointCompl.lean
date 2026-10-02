import Submission.Work.Tubular.Defs
import Submission.Work.Tubular.Compact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The complement of the zero section in the one-point compactification of `ν`

This module isolates the space that the whole of item (B2) of the tubular chapter's item 3 turns on:

  `A = (ν ∖ 0) ∪ {∞} ⊆ ν⁺ = OnePoint (NormalTotal E)`,

i.e. the complement of the zero section in the one-point compactification of the normal bundle of
an embedding `E : V ↪ ℝ^{8+k}`.

* `Work.Tubular.normalNonzero` — the complement of the zero section of `ν` (a subspace of `ν`);
* `Work.Tubular.onePointNonzero` — its image in `ν⁺`, together with the point at infinity: the space
  `A`;
* `Work.Tubular.onePointZeroSection` — the zero section of `ν` inside `ν⁺`, whose complement is `A`;
* `Work.Tubular.isOpen_onePointNonzero` — **`A` is open in `ν⁺`**, which is what makes the excision
  step of (B2) applicable (the excision hypothesis `closure {∞} ⊆ interior A`).
-/

open scoped Manifold ContDiff Topology
open Function Topology Set

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {N : ℕ}

/-- **The non-zero part of the normal bundle**: the complement of the zero section of `ν`, as a
subspace of the normal total space. -/
def normalNonzero (E : EmbeddingData V N) : Set (NormalTotal E) :=
  {p : NormalTotal E | normalNorm E p ≠ 0}

@[simp] theorem mem_normalNonzero {E : EmbeddingData V N} {p : NormalTotal E} :
    p ∈ normalNonzero E ↔ normalNorm E p ≠ 0 := Iff.rfl

/-- **The complement of the zero section in the one-point compactification of the normal bundle**:
the space whose contractibility is the geometric input of (B2). -/
def onePointNonzero (E : EmbeddingData V N) : Set (OnePoint (NormalTotal E)) :=
  OnePoint.some '' normalNonzero E ∪ {OnePoint.infty}

theorem mem_onePointNonzero {E : EmbeddingData V N} {p : OnePoint (NormalTotal E)} :
    p ∈ onePointNonzero E ↔
      p = OnePoint.infty ∨ ∃ q : NormalTotal E, normalNorm E q ≠ 0 ∧ OnePoint.some q = p := by
  constructor
  · intro h
    rcases h with h | h
    · obtain ⟨q, hq, rfl⟩ := h
      exact Or.inr ⟨q, hq, rfl⟩
    · exact Or.inl h
  · rintro (rfl | ⟨q, hq, rfl⟩)
    · exact Or.inr rfl
    · exact Or.inl ⟨q, hq, rfl⟩

/-- The zero section of the normal bundle, inside the one-point compactification. -/
def onePointZeroSection (E : EmbeddingData V N) : Set (OnePoint (NormalTotal E)) :=
  OnePoint.some '' {p : NormalTotal E | normalNorm E p = 0}

/-- The set of non-zero normal vectors is open (the fibrewise norm is continuous). -/
theorem isOpen_normalNonzero (E : EmbeddingData V N) : IsOpen (normalNonzero E) :=
  isOpen_ne_fun (continuous_normalNorm E) continuous_const

/-- The set of zero normal vectors (the zero section of `ν`) is closed. -/
theorem isClosed_normalZero (E : EmbeddingData V N) :
    IsClosed {p : NormalTotal E | normalNorm E p = 0} :=
  isClosed_eq (continuous_normalNorm E) continuous_const

/-- The complement of the zero section, inside `ν⁺`, is the union of the image of the non-zero part
and the point at infinity. -/
theorem compl_onePointZeroSection (E : EmbeddingData V N) :
    (onePointZeroSection E)ᶜ = onePointNonzero E := by
  ext p
  constructor
  · intro hp
    rw [onePointNonzero, Set.mem_union]
    cases p with
    | infty => exact Or.inr rfl
    | coe q => exact Or.inl ⟨q, fun hq => hp ⟨q, hq, rfl⟩, rfl⟩
  · intro hp hz
    rw [onePointNonzero, Set.mem_union] at hp
    rcases hp with ⟨q, hq, hqp⟩ | hinf
    · rw [← hqp] at hz
      obtain ⟨q', hq', heq⟩ := hz
      rw [OnePoint.coe_eq_coe] at heq
      exact hq (heq ▸ hq')
    · rw [hinf] at hz
      obtain ⟨q, _, hqp⟩ := hz
      exact OnePoint.coe_ne_infty q hqp

/-- The zero section of the normal bundle is compact (it is a copy of the compact manifold `V`). -/
theorem isCompact_normalZero {k : ℕ} (E : EmbeddingData V (8 + k)) :
    IsCompact {p : NormalTotal E | normalNorm E p = 0} := by
  have hset : {p : NormalTotal E | normalNorm E p = 0}
      = {p : NormalTotal E | normalNorm E p ≤ 0} := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h; rw [h]
    · intro h; exact le_antisymm h (normalNorm_nonneg E p)
  rw [hset]
  exact isCompact_normalClosedDiscSet E 0

/-- **The zero section of `ν` is closed in `ν⁺`**: it is the image of a closed compact subset of
`ν`. -/
theorem isClosed_onePointZeroSection {k : ℕ} (E : EmbeddingData V (8 + k)) :
    IsClosed (onePointZeroSection E) :=
  OnePoint.isClosed_image_coe.2 ⟨isClosed_normalZero E, isCompact_normalZero E⟩

/-- **The complement of the zero section in `ν⁺` is open**: it is the complement of the closed zero
section.  This is the hypothesis under which excision applies in (B2). -/
theorem isOpen_onePointNonzero {k : ℕ} (E : EmbeddingData V (8 + k)) :
    IsOpen (onePointNonzero E) := by
  rw [← compl_onePointZeroSection E]
  exact (isClosed_onePointZeroSection E).isOpen_compl

end

end Work.Tubular
