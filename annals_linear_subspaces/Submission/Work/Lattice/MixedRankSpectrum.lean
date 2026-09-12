import Mathlib
import Submission.Work.Lattice.FullRankSpectrum

/-!
# Mixed-rank covolume-spectrum discreteness — top-level reduction and hull machinery

ROADMAP item (ii), remaining part: for a full-rank lattice `Λ ≤ ℝᵈ` (`E d =
EuclideanSpace ℝ (Fin d)`, `Λ : Submodule ℤ (E d)`, `[DiscreteTopology Λ]
[IsZLattice ℝ Λ]`), for **every rank `r ≤ d`** the covolume spectrum at rank `r` is
discrete.  The top-level statement is recorded here as a named proposition,
`mixedRankSpectrumStatement r Λ C`; the full-rank case `r = d` is PROVEN (the
`FullRankSpectrum.finite_fullRank_covol_le` transport, corollary
`statement_fullRank`).  The remaining mixed-rank case `1 ≤ r < d` is reduced to two
recorded open sub-lemmas by the **saturation (hull) route**:

For `W ≤ Λ` of rank `r`, let `V := realSpan W` (the `r`-dimensional real span) and the
**hull** of `W` in `Λ` be the full rank-`r` lattice inside `Λ` spanning `V`:

    `hull Λ W := {x : E d | x ∈ Λ ∧ x ∈ realSpan W}`    (this module: `hull`)

Then `W ≤ hull Λ W ≤ Λ`, `realSpan (hull Λ W) = realSpan W` (so `subDim (hull Λ W) =
subDim W = r`, proven here), the hull is a **direct summand** of `Λ` (saturated:
`hull = Λ ∩ V`; equivalently `Λ / hull` is torsion-free) and `[hull : W] < ∞` with
`covol(W) = covol(hull) · [hull : W] ≥ covol(hull)` (the intrinsic rank-`r`
covolume/index identity, to be built on `GraysonData.latticeCovol_span`-type wedge
facts).  The counting then splits:

**(H1)** (open, Plücker/Grassmannian) — finitely many hulls: for each `r ≤ d` and
`C : ℝ`, only finitely many saturated rank-`r` subgroups `M ≤ Λ` (i.e. `M = hull Λ M`,
equivalently direct summands / `Λ/M` torsion-free) have `latticeCovol M ≤ C`; the hulls
are in bijection with the rational `r`-subspaces `V` of `ℝᵈ` via
`M = Λ ∩ V`, and `latticeCovol M = ‖v‖` for the primitive integer Plücker vector `v`
of `V`, so only finitely many with `‖v‖ ≤ C` (integer lattice points in a ball) — or the
`O(1)`-realisation alternative.

**(H2)** (open, reduction of the per-hull fibre to the group-theory core) — for a fixed
full-rank-in-`V` lattice `M ≤ Λ` of rank `r` and bound `C`, only finitely many
`W ≤ M` with `subDim W = r` and `latticeCovol W ≤ C`: since `[M : W] =
covol(W)/covol(M) ≤ C/covol(M)`, this is the bounded-index finiteness of
`SpectrumDiscreteness.finite_index_bounded(_real)` applied to the free finite-rank
`ℤ`-module `↥M` (instances via `ZLattice.module_free/module_finite` on `M` viewed in
its real span `V`, with `subDim W = r` ⟹ `IsZLattice` in `V`).

**(H3)** (open, intrinsic index identity, rank `r`) — for `W ≤ M` full-rank in `V =
realSpan M`, `latticeCovol W = latticeCovol M · [M : W]` with `[M : W]` the index in
`V` (the rank-`r` analogue of the full-rank identity; built on the covolume-wedge
facts `SubLatticeCovol.covol_wedge_of_submodule_basis` +
`ZLattice.covolume_div_covolume_eq_relIndex'` inside `V`).

With (H1)–(H3), `mixedRankSpectrumStatement` follows by decomposing `{W}` into the
hull-fibres `⨆_M {W ≤ M : latticeCovol W ≤ C}` (finite union of finite fibres over the
finite hull set).

This module records the statement (`mixedRankSpectrumStatement`), the proven full-rank
case (`statement_fullRank`), and the hull definition with its elementary facts
(`hull`, `hull_mem_iff`, `hull_le_Λ`, `W_le_hull`, `realSpan_hull_eq`,
`subDim_hull_eq`).  All declarations are Mathlib + Submission
(FullRankSpectrum/GraysonLattice).
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.MixedRankSpectrum

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.FullRankSpectrum

/-- **Top-level mixed-rank covolume-spectrum statement** (recorded): for a full-rank
lattice `Λ ≤ ℝᵈ` and a bound `C`, only finitely many rank-`r` discrete subgroups
`W ≤ Λ` have intrinsic covolume `latticeCovol W ≤ C`.  The full-rank case `r = d` is
proven below; the mixed-rank case follows from the hull reduction (H1)–(H3) above. -/
def mixedRankSpectrumStatement {d : ℕ} (r : ℕ) (Λ : Submodule ℤ (E d)) (C : ℝ) : Prop :=
  Finite {W : Submodule ℤ (E d) // W ≤ Λ ∧ subDim W = r ∧ latticeCovol W ≤ C}

/-- **Proven case `r = d`** of the mixed-rank statement (the full-rank transport of
`FullRankSpectrum.finite_fullRank_covol_le`). -/
theorem statement_fullRank {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (C : ℝ) :
    mixedRankSpectrumStatement d Λ C := by
  dsimp [mixedRankSpectrumStatement]
  exact finite_fullRank_covol_le Λ C

/-- The **hull** of `W ≤ Λ`: the full lattice inside `Λ` spanning the real span of `W`
(`Λ ∩ realSpan W` as a `ℤ`-submodule of `ℝᵈ`). -/
def hull {d : ℕ} (Λ W : Submodule ℤ (E d)) : Submodule ℤ (E d) where
  carrier := {x : E d | x ∈ Λ ∧ x ∈ realSpan W}
  zero_mem' := ⟨Λ.zero_mem, (realSpan W).zero_mem⟩
  add_mem' := by
    rintro x y ⟨hxΛ, hxV⟩ ⟨hyΛ, hyV⟩
    exact ⟨Λ.add_mem hxΛ hyΛ, (realSpan W).add_mem hxV hyV⟩
  smul_mem' := by
    rintro a x ⟨hxΛ, hxV⟩
    refine ⟨Λ.smul_mem a hxΛ, ?_⟩
    have h := (realSpan W).smul_mem (a : ℝ) hxV
    rwa [← Int.cast_smul_eq_zsmul ℝ a x]

/-- Membership in the hull: `x ∈ hull Λ W ↔ x ∈ Λ ∧ x ∈ realSpan W`. -/
lemma hull_mem_iff {d : ℕ} (Λ W : Submodule ℤ (E d)) (x : E d) :
    x ∈ hull Λ W ↔ x ∈ Λ ∧ x ∈ realSpan W := by
  simp [hull]

/-- The hull lies inside `Λ`. -/
lemma hull_le_Λ {d : ℕ} (Λ W : Submodule ℤ (E d)) : hull Λ W ≤ Λ := by
  intro x hx
  exact (hull_mem_iff Λ W x).mp hx |>.1

/-- A submodule of `Λ` is contained in its hull. -/
lemma W_le_hull {d : ℕ} (Λ W : Submodule ℤ (E d)) (hWΛ : W ≤ Λ) : W ≤ hull Λ W := by
  intro x hx
  exact (hull_mem_iff Λ W x).mpr
    ⟨hWΛ hx, Submodule.subset_span (s := (W : Set (E d))) hx⟩

/-- The real span of the hull is the real span of `W` (both are `V` when `W ≤ Λ`). -/
lemma realSpan_hull_eq {d : ℕ} (Λ W : Submodule ℤ (E d)) (hWΛ : W ≤ Λ) :
    realSpan (hull Λ W) = realSpan W := by
  apply le_antisymm
  · -- span of the hull ⊆ realSpan W (the hull is a subset of `realSpan W`)
    apply Submodule.span_le.mpr
    intro x hx
    exact (hull_mem_iff Λ W x).mp hx |>.2
  · -- realSpan W ⊆ span of the hull (`W ≤ hull`)
    exact Submodule.span_mono (by
      intro x hx
      exact (hull_mem_iff Λ W x).mpr
        ⟨hWΛ hx, Submodule.subset_span (s := (W : Set (E d))) hx⟩)

/-- The hull has the same rank as `W` (`subDim (hull Λ W) = subDim W`). -/
lemma subDim_hull_eq {d : ℕ} (Λ W : Submodule ℤ (E d)) (hWΛ : W ≤ Λ) :
    subDim (hull Λ W) = subDim W := by
  unfold subDim
  rw [realSpan_hull_eq Λ W hWΛ]

-- The hull is an idempotent, saturated construction: `hull Λ (hull Λ W) = hull Λ W`.
lemma hull_idempotent {d : ℕ} (Λ W : Submodule ℤ (E d)) (hWΛ : W ≤ Λ) :
    hull Λ (hull Λ W) = hull Λ W := by
  classical
  ext x
  rw [hull_mem_iff Λ (hull Λ W) x, hull_mem_iff Λ W x]
  -- x ∈ realSpan (hull Λ W) ↔ x ∈ realSpan W (both are V when W ≤ Λ)
  have hsp := realSpan_hull_eq Λ W hWΛ
  constructor
  · rintro ⟨hxΛ, hxV⟩
    refine ⟨hxΛ, ?_⟩
    -- x ∈ realSpan (hull W): need x ∈ realSpan W: realSpan hull = realSpan W: use subset:
    have hleV : realSpan (hull Λ W) ≤ realSpan W := by
      -- from hsp equality
      rw [hsp]
    exact hleV hxV
  · rintro ⟨hxΛ, hxV⟩
    refine ⟨hxΛ, ?_⟩
    have hleV' : realSpan W ≤ realSpan (hull Λ W) := by
      rw [hsp]
    exact hleV' hxV

/-- The hull of `W` is the unique saturated ("direct-summand-like") rank-`r` subgroup
above `W` inside `Λ` spanning the same real subspace as `W`.  Fibre-membership: every
`W ≤ Λ` lies in its own hull (`W ≤ hull Λ W`), and the hull has the same rank
(`subDim (hull Λ W) = subDim W`). -/
lemma W_mem_fibre_of_hull {d : ℕ} (Λ : Submodule ℤ (E d)) (W : Submodule ℤ (E d))
    (hWΛ : W ≤ Λ) :
    W ≤ hull Λ W ∧ subDim (hull Λ W) = subDim W ∧ hull Λ W ≤ Λ := by
  exact ⟨W_le_hull Λ W hWΛ, subDim_hull_eq Λ W hWΛ, hull_le_Λ Λ W⟩

/-- **Fibre decomposition (hull form), first half**: if `W ≤ Λ` has rank `r` and
covolume ≤ `C`, then its hull `M := hull Λ W` is a rank-`r` subgroup of `Λ` lying in the
hull-family `H(r,C)` (with covolume ≤ `C`, to be supplied by the covolume monotonicity
`covol(hull W) ≤ covol W` once positivity/index facts are in place), and `W` lies in the
fibre `{W' ≤ M : subDim W' = r ∧ latticeCovol W' ≤ C}` over `M`.  This is the
`W ↦ (M, W)` decomposition of the spectrum set over its hulls; combined with per-hull
finiteness (intrinsic index identity + the bounded-index group core) it yields the
mixed-rank spectrum statement.  (Recorded: covol monotonicity and the per-hull
finiteness are the remaining H2 pieces; finite-many-hulls is H1.) -/
theorem fibre_decomposition {d r : ℕ} (Λ : Submodule ℤ (E d)) (W : Submodule ℤ (E d))
    (hWΛ : W ≤ Λ) (hr : subDim W = r) :
    W ≤ hull Λ W ∧ subDim (hull Λ W) = r ∧ hull Λ W ≤ Λ := by
  have h := W_mem_fibre_of_hull Λ W hWΛ
  exact ⟨h.1, by rw [h.2.1, hr], h.2.2⟩

end Submission.MixedRankSpectrum
