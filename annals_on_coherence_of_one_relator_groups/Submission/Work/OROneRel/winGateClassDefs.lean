/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The gate class map of the `Z`-domain window, and the gate-injection condition

For the window decomposition of `Work.OROneRel.winAssembly` (`H = winVertex Wt c lo hi u l ≤ ⟨α | u ^ l⟩`
the image of the vertex) and a set `S` of edges of the window, this file defines

* `winGateClass Wt c lo hi u l S hS` -- the **class map of the gate** `S`: the free group on the
  gate's non-tree edges (`winBetaSub Wt c S`, `Submission/Work/OROneRel/winGateDefs.lean`) mapped into
  the *vertex subgroup* `↥(winVertex …)` by the loop class of the corresponding edge of the `ℤ`-cover;
* `WinGateInjective Wt c lo hi u l S hS` -- its injectivity, the **gate-injection condition** of
  Linton, *One-relator hierarchies*, arXiv 2202.11324, Proposition 2.2.19 (there `ι_*` for the gate
  `D ∩ t⁻¹D` and `(t ∘ ι)_*` for the gate `D ∩ tD`).

The codomain is deliberately the *subgroup* `winVertex` and not the one-relator vertex presentation
`⟨β | winRoot ^ l⟩`: the former is available without the Freiheitssatz of the window (plank (A)), so
the gate condition — and hence the splitting statement that consumes it — is independent of (A).  By
`Work.OROneRel.winGateFreiheitssatz` (which is proved) the gate's class map is injective *into the
vertex presentation*, so once (A) identifies `⟨β | winRoot ^ l⟩` with `↥winVertex` the condition here
follows from it; in particular it is a strictly weaker hypothesis than (A).
-/
import Mathlib
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.winGateDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The class map of a gate** `S`: the free group on the gate's non-tree edges, mapped to the vertex
subgroup `winVertex` by the loop class of the corresponding edge of the `ℤ`-cover. -/
noncomputable def winGateClass (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (l : ℕ) (S : Set (α × ℤ)) (hS : S ⊆ winE c lo hi) :
    FreeGroup (winBetaSub Wt c S) → ↥(winVertex Wt c lo hi u l) :=
  fun x => ⟨PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
      (winRho Wt c lo hi (winBetaSubIncl Wt c hS x)),
    by
      rw [winVertex]
      exact Subgroup.mem_map_of_mem _ ⟨winBetaSubIncl Wt c hS x, rfl⟩⟩

/-- **The gate-injection condition**: the class map of the gate is injective into the vertex
subgroup. -/
def WinGateInjective (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α) (l : ℕ)
    (S : Set (α × ℤ)) (hS : S ⊆ winE c lo hi) : Prop :=
  Function.Injective (winGateClass Wt c lo hi u l S hS)

/-- The two gates of a `Z`-domain: `D ∩ t⁻¹D` (below) and `D ∩ tD` (above), as edge sets of the
window. -/
def winGateBelow (c : α → ℤ) (lo hi : ℤ) : Set (α × ℤ) := winE c lo hi ∩ winE c (lo - 1) (hi - 1)

/-- The upper gate of a `Z`-domain. -/
def winGateAbove (c : α → ℤ) (lo hi : ℤ) : Set (α × ℤ) := winE c lo hi ∩ winE c (lo + 1) (hi + 1)

theorem winGateBelow_subset (c : α → ℤ) (lo hi : ℤ) : winGateBelow c lo hi ⊆ winE c lo hi :=
  fun _ he => he.1

theorem winGateAbove_subset (c : α → ℤ) (lo hi : ℤ) : winGateAbove c lo hi ⊆ winE c lo hi :=
  fun _ he => he.1

/-- **The class map of a gate, into the ambient group** `G = ⟨α | u ^ l⟩`: this is the form used in
the corrected gate hypotheses (the codomain `↥winVertex` of `winGateClass` is the vertex subgroup,
which is what the two-maps construction wants; `G` is what the geometric gate statement is naturally
about). -/
noncomputable def winGateClassG (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (l : ℕ) (S : Set (α × ℤ)) (hS : S ⊆ winE c lo hi) :
    FreeGroup (winBetaSub Wt c S) → PresentedGroup ({u ^ l} : Set (FreeGroup α)) :=
  fun x => PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
    (winRho Wt c lo hi (winBetaSubIncl Wt c hS x))

/-- **The gate-injection condition into the ambient group.** -/
def WinGateInjectiveG (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α) (l : ℕ)
    (S : Set (α × ℤ)) (hS : S ⊆ winE c lo hi) : Prop :=
  Function.Injective (winGateClassG Wt c lo hi u l S hS)

/-- **The gate subgroup lies in the vertex subgroup** (re-proved here so that consumers need not
import `magnusStepCase2`, which carries unproved obligations). -/
theorem winGateSub_le_winVertex' {u : FreeGroup α} {l : ℕ} {c : α → ℤ} {Wt : ℤ → FreeGroup α}
    {lo hi : ℤ} {S : Set (α × ℤ)} (hS : S ⊆ winE c lo hi) :
    winGateSub Wt c lo hi u l S hS ≤ winVertex Wt c lo hi u l := by
  rw [winGateSub, Subgroup.closure_le]
  rintro g ⟨e, rfl⟩
  refine Subgroup.mem_map_of_mem (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))) ?_
  exact MonoidHom.mem_range.mpr ⟨FreeGroup.of (winBetaSubVal Wt c hS e), rfl⟩

/-- **The elements of a gate subgroup, in terms of the gate's generators.** -/
theorem winGateSub_le_winVertex_apply {u : FreeGroup α} {l : ℕ} {c : α → ℤ} {Wt : ℤ → FreeGroup α}
    {lo hi : ℤ} {S : Set (α × ℤ)} (hS : S ⊆ winE c lo hi)
    {g : PresentedGroup ({u ^ l} : Set (FreeGroup α))} (hg : g ∈ winGateSub Wt c lo hi u l S hS) :
    g ∈ winVertex Wt c lo hi u l :=
  winGateSub_le_winVertex' hS hg

end Work.OROneRel
