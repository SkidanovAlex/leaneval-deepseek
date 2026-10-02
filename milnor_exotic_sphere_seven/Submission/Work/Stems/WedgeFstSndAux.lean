import Mathlib
import Submission.Work.Stems.WedgeHomology
-- Re-pointed (Islands subproject, 2026): the workspace contains two copies of
-- `Work.Cohomology.proj_pair_injective` — this one in `Submission/Work/Cohomology/` and the
-- identical `Submission.Work.Cohomology.CompatTrans.proj_pair_injective`.  The rest of the
-- workspace (and the whole `StemsB`/`Thom` ladder) uses the `CompatTrans` copy, so the two
-- could not be imported together.  The declaration used below (`proj_pair_injective`) has the
-- same name and statement in both; we import the copy the rest of the workspace uses.
import Submission.Work.Cohomology.CompatTrans.proj_pair_injective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The open cover of the wedge `Sⁿ ∨ Sⁿ` and its pieces

This file sets up the two open pieces of the wedge `W = Sⁿ ∨ Sⁿ` used to compute
`Hₙ(W)` by Mayer–Vietoris, and the maps between them and `Sⁿ`.

Write `b = sphBase n hn` for the base point, `q = sphOther n hn` for a second point of `Sⁿ`
(`sphOther_ne_sphBase`), and `W = wedgeSet b ⊆ Sⁿ × Sⁿ` for the "cross".  The cover is

* `wfsU n hn = {z ∈ W | z₁ ≠ q}` — the second sphere `{b} × Sⁿ` together with a punctured copy of
  the first;
* `wfsV n hn = {z ∈ W | z₂ ≠ q}` — symmetric;
* `wfsU ∪ wfsV = W`, and `wfsU ∩ wfsV` is contractible.

The first projection is a homotopy equivalence on `wfsV` (its second coordinate is never `q`), and
ditto the second projection on `wfsU`; on the other piece the corresponding projection is
nullhomotopic.  These four facts (together with the Mayer–Vietoris sequence) show that the pair of
folds `(wedgeFst, wedgeSnd)` is injective on `Hₙ(W)`.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

variable {n : ℕ}

/-! ## The two open pieces -/

/-- The wedge `Sⁿ ∨ Sⁿ` as a topological space. -/
abbrev wfsW (n : ℕ) (hn : 1 ≤ n) : TopCat := TopCat.of (wedgeSet (sphBase n hn))

/-- The open piece `U = {z ∈ Sⁿ ∨ Sⁿ | z₁ ≠ q}` of the wedge. -/
def wfsU (n : ℕ) (hn : 1 ≤ n) : Set (wfsW n hn) :=
  {z | z.1.1 ≠ sphOther n hn}

/-- The open piece `V = {z ∈ Sⁿ ∨ Sⁿ | z₂ ≠ q}` of the wedge. -/
def wfsV (n : ℕ) (hn : 1 ≤ n) : Set (wfsW n hn) :=
  {z | z.1.2 ≠ sphOther n hn}

@[simp] theorem mem_wfsU (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsW n hn)) :
    z ∈ wfsU n hn ↔ z.1.1 ≠ sphOther n hn := Iff.rfl

@[simp] theorem mem_wfsV (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsW n hn)) :
    z ∈ wfsV n hn ↔ z.1.2 ≠ sphOther n hn := Iff.rfl

theorem isOpen_wfsU (n : ℕ) (hn : 1 ≤ n) : IsOpen (wfsU n hn) :=
  isOpen_compl_singleton.preimage (continuous_subtype_val.fst)

theorem isOpen_wfsV (n : ℕ) (hn : 1 ≤ n) : IsOpen (wfsV n hn) :=
  isOpen_compl_singleton.preimage (continuous_subtype_val.snd)

theorem wfsU_union_wfsV (n : ℕ) (hn : 1 ≤ n) : wfsU n hn ∪ wfsV n hn = Set.univ := by
  ext z
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  rcases z.2 with hb | hb
  · left
    show z.1.1 ≠ sphOther n hn
    rw [hb]
    exact (sphOther_ne_sphBase n hn).symm
  · right
    show z.1.2 ≠ sphOther n hn
    rw [hb]
    exact (sphOther_ne_sphBase n hn).symm

/-! ## The structural maps -/

/-- The inclusion `U ↪ Sⁿ ∨ Sⁿ`. -/
def wfsUIncl (n : ℕ) (hn : 1 ≤ n) : C(↥(wfsU n hn), ↥(wfsW n hn)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion `V ↪ Sⁿ ∨ Sⁿ`. -/
def wfsVIncl (n : ℕ) (hn : 1 ≤ n) : C(↥(wfsV n hn), ↥(wfsW n hn)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The first fold restricted to `U`, `z ↦ z₁`. -/
def wfsUfst (n : ℕ) (hn : 1 ≤ n) : C(↥(wfsU n hn), sphere n) :=
  (wedgeFst (sphBase n hn)).comp (wfsUIncl n hn)

/-- The second fold restricted to `U`, `z ↦ z₂`. -/
def wfsUsnd (n : ℕ) (hn : 1 ≤ n) : C(↥(wfsU n hn), sphere n) :=
  (wedgeSnd (sphBase n hn)).comp (wfsUIncl n hn)

/-- The first fold restricted to `V`, `z ↦ z₁`. -/
def wfsVfst (n : ℕ) (hn : 1 ≤ n) : C(↥(wfsV n hn), sphere n) :=
  (wedgeFst (sphBase n hn)).comp (wfsVIncl n hn)

/-- The second fold restricted to `V`, `z ↦ z₂`. -/
def wfsVsnd (n : ℕ) (hn : 1 ≤ n) : C(↥(wfsV n hn), sphere n) :=
  (wedgeSnd (sphBase n hn)).comp (wfsVIncl n hn)

@[simp] theorem wfsUIncl_apply (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsU n hn)) :
    wfsUIncl n hn z = z.1 := rfl

@[simp] theorem wfsVIncl_apply (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsV n hn)) :
    wfsVIncl n hn z = z.1 := rfl

@[simp] theorem wfsUfst_apply (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsU n hn)) :
    wfsUfst n hn z = z.1.1.1 := rfl

@[simp] theorem wfsUsnd_apply (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsU n hn)) :
    wfsUsnd n hn z = z.1.1.2 := rfl

@[simp] theorem wfsVfst_apply (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsV n hn)) :
    wfsVfst n hn z = z.1.1.1 := rfl

@[simp] theorem wfsVsnd_apply (n : ℕ) (hn : 1 ≤ n) (z : ↥(wfsV n hn)) :
    wfsVsnd n hn z = z.1.1.2 := rfl

/-! ## The sections -/

/-- The section `Sⁿ → U`, `y ↦ (b, y)`. -/
def wfsUsec (n : ℕ) (hn : 1 ≤ n) : C(sphere n, ↥(wfsU n hn)) :=
  ⟨fun y => ⟨⟨(sphBase n hn, y), Or.inl rfl⟩, (sphOther_ne_sphBase n hn).symm⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_const.prodMk continuous_id⟩

/-- The section `Sⁿ → V`, `y ↦ (y, b)`. -/
def wfsVsec (n : ℕ) (hn : 1 ≤ n) : C(sphere n, ↥(wfsV n hn)) :=
  ⟨fun y => ⟨⟨(y, sphBase n hn), Or.inr rfl⟩, (sphOther_ne_sphBase n hn).symm⟩, by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_const⟩

@[simp] theorem wfsUsec_apply (n : ℕ) (hn : 1 ≤ n) (y : sphere n) :
    (wfsUsec n hn y : ↥(wedgeSet (sphBase n hn))) = ⟨(sphBase n hn, y), Or.inl rfl⟩ := rfl

@[simp] theorem wfsVsec_apply (n : ℕ) (hn : 1 ≤ n) (y : sphere n) :
    (wfsVsec n hn y : ↥(wedgeSet (sphBase n hn))) = ⟨(y, sphBase n hn), Or.inr rfl⟩ := rfl

theorem wfsUsnd_comp_wfsUsec (n : ℕ) (hn : 1 ≤ n) :
    (wfsUsnd n hn).comp (wfsUsec n hn) = ContinuousMap.id (sphere n) := by
  apply ContinuousMap.ext
  intro y
  rw [ContinuousMap.comp_apply, wfsUsnd_apply, wfsUsec_apply]
  rfl

theorem wfsVfst_comp_wfsVsec (n : ℕ) (hn : 1 ≤ n) :
    (wfsVfst n hn).comp (wfsVsec n hn) = ContinuousMap.id (sphere n) := by
  apply ContinuousMap.ext
  intro y
  rw [ContinuousMap.comp_apply, wfsVfst_apply, wfsVsec_apply]
  rfl

end

end Work.Stems
