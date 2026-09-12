import Mathlib
import Submission.Work.Lattice.LatticePolygon
import Submission.Work.Lattice.UniformBddBelow
import Submission.Work.Lattice.DataAttainment
import Submission.Work.Polygon.GraysonEndpoints

/-!
# The nesting lemma for the P2-general HN flag: mixed-rank log-covol submodularity

The next step of P2-general (after the angular-rank data-tightness, sessions 123–124:
`polygon Λ j = rankData Λ j` and exact subgroup realisers `exists_subgroup_polygon_at_angular`
at the canonical ranks) is to **nest** the realising subgroups into a flag

    `⊥ = V₀ ≤ V_{b₁} ≤ … ≤ V_{b_{N−1}} ≤ V_{b_N} = Λ`

(`bₛ = blockStart d (polygon Λ) s`, `1 ≤ s ≤ numBlocks d (polygon Λ)`, `b_N = d`) whose
subgroups realise the polygon values up to `O(1)`.  The load-bearing lemma of that nesting
is the **mixed-rank log-covol submodularity** of the intrinsic covolume on the subgroup
lattice of a full-rank lattice:

**Statement (general form, recorded target).**  Let `Λ ≤ ℝᵈ` be a full-rank lattice
(`E d`, `[DiscreteTopology Λ] [IsZLattice ℝ Λ]`) and `V, W ≤ Λ` nonzero discrete
subgroups.  Then, with `⊓`/`⊔` the meet/join of the `ℤ`-submodules and `latticeCovol`
the covolume measured inside the subgroup's own real span,

    `latticeCovol V · latticeCovol W ≥ latticeCovol (V ⊓ W) · latticeCovol (V ⊔ W)`

equivalently (log form, for nonzero `V,W,V⊓W,V⊔W`)

    `log covol(V) + log covol(W) ≥ log covol(V ⊓ W) + log covol(V ⊔ W)`,

i.e. the join `V ⊔ W` of two realisers has covolume at most
`covol(V)·covol(W)/covol(V ⊓ W)` — so joining two realisers of adjacent angular ranks
keeps the join within the value budget, *provided* the meet has value at least the
polygon at its (smaller) rank.

**Reduction to the aligned-basis exterior-power engine (L64).**  When the two subgroups
admit **aligned `ℤ`-spanning families** — a family `u` `ℤ`-spanning `V ⊓ W` and families
`u ++ x`, `u ++ y` spanning `V`, `W` with `(u ++ x) ++ y` spanning `V ⊔ W` — the
inequality is exactly the proven Grayson-data submodularity
`Submission.GraysonData.graysonData_log_submodularity` (which reduces to the Commons
pure exterior-power inequality `exteriorPower_norm_intersection_le`, L64).  Such aligned
families exist whenever `V ⊓ W` is a **direct summand** (saturated) of both `V` and `W`;
over `ℤ` this is automatic only for saturated subgroups, and **fails in general** (e.g.
`2ℤ ≤ ℤ` is not a direct summand — the torsion obstruction recorded in session 106).

**Reduction of the flag construction to the saturated case.**  A realiser of the polygon
value at an angular rank can always be replaced by its **hull** (its saturation in `Λ`):
`proven below, `realiser_hull_eq` — `log covol(hull V) = log covol(V)` when the latter
equals the polygon value at rank `subDim V` (polygon ≤ data at the hull, and the hull's
covolume is no larger).  So the flag subgroups may be taken saturated, and the
submodularity is needed for saturated `V, W ≤ Λ` (whose meets `V ⊓ W` are again
saturated, since purity is preserved under intersections), where the remaining open
piece is the **aligned-`ℤ`-basis existence for saturated pairs** (Smith-normal-form
theory: `Module.Basis.SmithNormalForm`, diagonal entries ±1 for pure subgroups) — the
recorded next sub-lemma.

This module records the precise statements and proves the pieces currently within reach:
(1) the realiser→hull saturation `realiser_hull_eq` / `exists_saturated_realiser` (so the
nesting can work with saturated realisers); (2) the aligned-family instance of the join
inequality restated at the subgroup level (`logCovol_submodularity_aligned`), which is
what the aligned-basis existence will instantiate.  All declarations are Mathlib +
Submission (LatticePolygon/UniformBddBelow/IntrinsicIndex/MixedRankSpectrum/
GraysonEndpoints/GraysonData).
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.JoinSubmodularity

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.LatticePolygon
open Submission.UniformBddBelow
open Submission.IntrinsicIndex
open Submission.MixedRankSpectrum
open Submission.GraysonEndpoints

/-- The **log-covol submodularity of the intrinsic covolume on the subgroup lattice of a
full-rank lattice**, for subgroups presented by aligned spanning families: if `u` spans
`W₁ ⊓ W₂`, `u ++ x` spans `W₁`, `u ++ y` spans `W₂` and `(u ++ x) ++ y` spans `W₁ ⊔ W₂`
(all `ℝ`-independent), then

    `log covol(W₁) + log covol(W₂) ≥ log covol(W₁ ⊓ W₂) + log covol(W₁ ⊔ W₂)`.

This is the lattice-level statement of `GraysonData.graysonData_log_submodularity`
recorded here as the interface the aligned-basis sub-lemma must feed. -/
theorem logCovol_submodularity_aligned {d m a b : ℕ} (hm : 0 < m)
    (u : Fin m → E d) (x : Fin a → E d) (y : Fin b → E d)
    (hu : LinearIndependent ℝ u) (hux : LinearIndependent ℝ (Fin.append u x))
    (huy : LinearIndependent ℝ (Fin.append u y))
    (huxy : LinearIndependent ℝ (Fin.append (Fin.append u x) y))
    (W₁ W₂ : Submodule ℤ (E d))
    (hW₁ : W₁ = Submodule.span ℤ (Set.range (Fin.append u x)))
    (hW₂ : W₂ = Submodule.span ℤ (Set.range (Fin.append u y)))
    (hI : W₁ ⊓ W₂ = Submodule.span ℤ (Set.range u))
    (hS : W₁ ⊔ W₂ = Submodule.span ℤ (Set.range (Fin.append (Fin.append u x) y))) :
    Real.log (latticeCovol W₁) + Real.log (latticeCovol W₂) ≥
      Real.log (latticeCovol (W₁ ⊓ W₂)) + Real.log (latticeCovol (W₁ ⊔ W₂)) :=
  graysonData_log_submodularity (d := d) hm u x y hu hux huy huxy W₁ W₂ hW₁ hW₂ hI hS

/-- **Covol-positivity of a realiser's hull**: for nonzero `W ≤ Λ`, the hull is nonzero
and its covolume is positive. -/
lemma hull_pos {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (W : Submodule ℤ (E d)) (hWΛ : W ≤ Λ) (hW0 : W ≠ ⊥) :
    hull Λ W ≠ ⊥ ∧ 0 < latticeCovol (hull Λ W) := by
  have hMle : hull Λ W ≤ Λ := hull_le_Λ Λ W
  have hM0 : hull Λ W ≠ ⊥ := by
    intro hbot
    apply hW0
    have hWleBot : W ≤ (⊥ : Submodule ℤ (E d)) := by
      simpa [hbot] using (W_le_hull Λ W hWΛ)
    exact le_bot_iff.mp hWleBot
  exact ⟨hM0, latticeCovol_pos (d := d) Λ (hull Λ W) hMle hM0⟩

/-- **Realiser hull saturation**: if `W ≤ Λ` realises the polygon value at its rank
(`log covol W = polygon Λ (subDim W)`), then its hull realises the same value, has the
same rank, is saturated (`hull Λ (hull Λ W) = hull Λ W`) and lies in `Λ` — so any
realiser can be replaced by a saturated one.  Proof: the hull has the same rank
(`subDim_hull_eq`), its covolume is no larger (`covol_hull_le_covol`), and the polygon
lies below the data of every rank-`subDim W` subgroup (`polygon_le_covol`), forcing the
hull's value to equal the polygon value (hence `= log covol W`). -/
theorem realiser_hull_eq {d : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (W : Submodule ℤ (E d)) (hWΛ : W ≤ Λ) (hW0 : W ≠ ⊥)
    (hreal : Real.log (latticeCovol W) = polygon Λ (subDim W)) :
    Real.log (latticeCovol (hull Λ W)) = polygon Λ (subDim W) ∧
      subDim (hull Λ W) = subDim W ∧ hull Λ W ≤ Λ ∧
      hull Λ (hull Λ W) = hull Λ W := by
  classical
  let r : ℕ := subDim W
  have hcov : latticeCovol (hull Λ W) ≤ latticeCovol W :=
    covol_hull_le_covol (d := d) Λ W hWΛ hW0
  have hsub : subDim (hull Λ W) = r := by
    dsimp [r]
    exact subDim_hull_eq Λ W hWΛ
  have hMle : hull Λ W ≤ Λ := hull_le_Λ Λ W
  have hsat : hull Λ (hull Λ W) = hull Λ W := hull_idempotent Λ W hWΛ
  have hrW' : subDim W ≤ Module.finrank ℤ Λ := by
    rw [hΛfin]
    exact subDim_le_ambient W
  have hbd : BddBelow (rankDataSet Λ r) := by
    dsimp [r]
    exact rankData_bddBelow_of_lattice Λ hΛfin (subDim W) (by simpa [hΛfin] using subDim_le_ambient W)
  have hpoly_le : polygon Λ r ≤ Real.log (latticeCovol (hull Λ W)) := by
    dsimp [r]
    have hjd : subDim (hull Λ W) ≤ Module.finrank ℤ Λ := by
      rw [hΛfin]
      exact subDim_le_ambient (hull Λ W)
    have hbd' : BddBelow (rankDataSet Λ (subDim (hull Λ W))) := by
      rw [subDim_hull_eq Λ W hWΛ]
      exact hbd
    have hpl := polygon_le_covol Λ hMle hjd hbd'
    rw [subDim_hull_eq Λ W hWΛ] at hpl
    exact hpl
  -- polygon ≤ log covol(hull) ≤ log covol(W) = polygon: equalities
  have hlog_le : Real.log (latticeCovol (hull Λ W)) ≤ Real.log (latticeCovol W) :=
    Real.log_le_log (hull_pos Λ W hWΛ hW0).2 hcov
  have hmain : Real.log (latticeCovol (hull Λ W)) = polygon Λ r := by
    apply le_antisymm
    · calc
        Real.log (latticeCovol (hull Λ W)) ≤ Real.log (latticeCovol W) := hlog_le
        _ = polygon Λ r := by rw [hreal]
    · exact hpoly_le
  exact ⟨by simpa [r] using hmain, hsub, hMle, hsat⟩

/-- **Saturated realiser existence at the canonical ranks**: at every rank where the
polygon is realised by a subgroup (in particular at the angular ranks
`0 < blockStart d (polygon Λ) s < d` and at `d`), a **saturated** realiser exists
(a subgroup `V ≤ Λ` with `V = hull Λ V`, `subDim V = j` and
`log covol V = polygon Λ j`).  This is the form in which the flag construction consumes
the realisers (so that the meets of flag subgroups are saturated and the aligned-basis
submodularity applies). -/
theorem exists_saturated_realiser {d j : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) (hj0 : 0 < j)
    (hW : ∃ W : Submodule ℤ (E d), W ≤ Λ ∧ subDim W = j ∧
      Real.log (latticeCovol W) = polygon Λ j) :
    ∃ V : Submodule ℤ (E d), V ≤ Λ ∧ subDim V = j ∧
      Real.log (latticeCovol V) = polygon Λ j ∧ V = hull Λ V := by
  classical
  rcases hW with ⟨W, hWle, hdim, hreal⟩
  have hW0 : W ≠ ⊥ := by
    intro hz
    have hdim0 : subDim W = 0 := (subDim_eq_zero_iff_bot W).mpr hz
    omega
  have hreal' : Real.log (latticeCovol W) = polygon Λ (subDim W) := by
    rw [hdim]
    exact hreal
  have hres := realiser_hull_eq (d := d) Λ hΛfin W hWle hW0 hreal'
  -- hres : log covol(hull) = polygon Λ (subDim W) ∧ subDim(hull) = subDim W ∧ hull ≤ Λ ∧ saturated
  have hmain : Real.log (latticeCovol (hull Λ W)) = polygon Λ j := by
    rw [hres.1, hdim]
  refine ⟨hull Λ W, hres.2.2.1, by simpa [hres.2.1] using hdim, hmain, hres.2.2.2.symm⟩

/-! ## Saturated (pure) subgroups and the purity-under-meets lemma

The flag construction works with **saturated** subgroups (`V = hull Λ V`, i.e.
`V = Λ ∩ realSpan V`; equivalently the quotient is torsion-free / `V` is a direct
summand).  The aligned-`ℤ`-basis lemma for saturated pairs needs the meet of two
saturated subgroups to be saturated (so bases of the meet extend to bases of both):
that is **purity is preserved under meets**, which is immediate in the hull form: an
element of `Λ` lying in `realSpan (V ⊓ W)` lies in `realSpan V` and in `realSpan W`,
hence — by saturation of `V` and of `W` — in `V` and in `W`.  (No real-span-intersection
formula is needed.)

Note (for the record): the **join** `V ⊔ W` of two saturated subgroups need NOT be
saturated (e.g. in `ℤ³`, the two saturated planes `x+y+z = 0` and `x+y−z = 0` have
saturated-looking sum that is not pure: `2e₁ ∈ H₁+H₂` but `e₁ ∉ H₁+H₂`) — the flag
never needs to join non-nested saturated subgroups (its subgroups form a chain), and the
covol submodularity is stated for the (possibly non-saturated) join directly via its
spanning families. -/

/-- A subgroup `V` is **saturated** in `Λ` if it equals its own hull (`V = hull Λ V`,
i.e. `V = Λ ∩ realSpan V`).  Saturation implies `V ≤ Λ`. -/
def Saturated {d : ℕ} (Λ V : Submodule ℤ (E d)) : Prop := V = hull Λ V

/-- A saturated subgroup lies inside `Λ`. -/
lemma saturated_le {d : ℕ} (Λ V : Submodule ℤ (E d)) (hV : Saturated Λ V) : V ≤ Λ := by
  dsimp [Saturated] at hV
  rw [hV]
  exact hull_le_Λ Λ V

/-- Saturation is idempotent (the hull of a saturated subgroup is itself). -/
lemma saturated_hull {d : ℕ} (Λ V : Submodule ℤ (E d)) (_hVΛ : V ≤ Λ)
    (hV : Saturated Λ V) : Saturated Λ (hull Λ V) := by
  dsimp [Saturated]
  exact congrArg (hull Λ) hV

/-- **Purity is preserved under meets**: if `V, W ≤ Λ` are saturated, so is `V ⊓ W`.
An element of `Λ` in `realSpan (V⊓W)` lies in `realSpan V ∩ realSpan W`, hence (by
saturation) in `V ∩ W`; conversely `V ⊓ W` is contained in its own hull. -/
lemma saturated_inf {d : ℕ} (Λ V W : Submodule ℤ (E d)) (hV : Saturated Λ V)
    (hW : Saturated Λ W) : Saturated Λ (V ⊓ W) := by
  dsimp [Saturated]
  apply le_antisymm
  · -- V ⊓ W ≤ hull Λ (V ⊓ W) (every subgroup lies in its hull)
    intro x hx
    exact (hull_mem_iff Λ (V ⊓ W) x).mpr
      ⟨(saturated_le Λ V hV) (hx.1), Submodule.subset_span (s := ((V ⊓ W) : Set (E d))) hx⟩
  · -- hull Λ (V ⊓ W) ≤ V ⊓ W: an ambient point of realSpan(V⊓W) lies in both V and W
    intro x hx
    have hxΛ : x ∈ Λ := (hull_mem_iff Λ (V ⊓ W) x).mp hx |>.1
    have hxspan : x ∈ realSpan (V ⊓ W) := (hull_mem_iff Λ (V ⊓ W) x).mp hx |>.2
    have hxV : x ∈ V := by
      have hmono : realSpan (V ⊓ W) ≤ realSpan V := Submodule.span_mono (by intro y hy; exact hy.1)
      have hsatV : V = hull Λ V := hV
      rw [hsatV]
      exact (hull_mem_iff Λ V x).mpr ⟨hxΛ, hmono hxspan⟩
    have hxW : x ∈ W := by
      have hmono : realSpan (V ⊓ W) ≤ realSpan W := Submodule.span_mono (by intro y hy; exact hy.2)
      have hsatW : W = hull Λ W := hW
      rw [hsatW]
      exact (hull_mem_iff Λ W x).mpr ⟨hxΛ, hmono hxspan⟩
    exact ⟨hxV, hxW⟩

/-- A subgroup `N ≤ V` is **pure** in `V` (over `ℤ`, equivalently `V/N` is
torsion-free): any `x ∈ V` with a nonzero integer multiple in `N` lies in `N`. -/
def Pure {d : ℕ} (V N : Submodule ℤ (E d)) : Prop :=
  N ≤ V ∧ ∀ x : E d, x ∈ V → (∃ m : ℤ, m ≠ 0 ∧ m • x ∈ N) → x ∈ N

/-- **The meet is pure in each factor**: if `W ≤ Λ` is saturated and `V ≤ Λ`, then
`V ⊓ W` is pure in `V` — an element `x ∈ V` with a nonzero multiple `m • x ∈ V ⊓ W`
satisfies `x ∈ realSpan W` (real-span is closed under the real scalar `1/m`), hence
`x ∈ Λ ∩ realSpan W = W`, so `x ∈ V ⊓ W`.  (This is the torsion-freeness of
`V/(V ⊓ W)` needed to extend `ℤ`-bases of the meet to `V`.) -/
lemma pure_inf_left {d : ℕ} (Λ V W : Submodule ℤ (E d)) (hVΛ : V ≤ Λ)
    (hW : Saturated Λ W) : Pure V (V ⊓ W) := by
  constructor
  · exact inf_le_left
  · intro x hxV hmx
    rcases hmx with ⟨m, hm0, hm⟩
    have hxΛ : x ∈ Λ := hVΛ hxV
    have hxW : x ∈ W := by
      -- (m : ℝ) • x = (m : ℤ) • x ∈ W ⊆ realSpan W; realSpan closed under the scalar 1/m
      have hsmul : (m : ℝ) • x = m • x := Int.cast_smul_eq_zsmul ℝ m x
      have hmz : m • x ∈ W := hm.2
      have hmW0 : m • x ∈ realSpan W :=
        Submodule.subset_span (s := (W : Set (E d))) (by simpa using hmz)
      have hmW : (m : ℝ) • x ∈ realSpan W := by simpa [hsmul] using hmW0
      have hxspan : x ∈ realSpan W := by
        have hxeq : (1 / (m : ℝ)) • ((m : ℝ) • x) = x := by
          calc
            (1 / (m : ℝ)) • ((m : ℝ) • x) = ((1 / (m : ℝ)) * (m : ℝ)) • x := by rw [smul_smul]
            _ = x := by
              have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
              field_simp [hmR]
              simp
        rw [← hxeq]
        exact (realSpan W).smul_mem (1 / (m : ℝ)) hmW
      have hxHull : x ∈ hull Λ W := (hull_mem_iff Λ W x).mpr ⟨hxΛ, hxspan⟩
      rw [hW]
      exact hxHull
    exact ⟨hxV, hxW⟩

/-! ## The aligned-basis lemma (recorded target, roadmap item (i))

**Aligned-basis lemma (saturated pairs).**  Let `Λ ≤ ℝᵈ` be a full-rank lattice and
`V, W ≤ Λ` saturated (`Saturated Λ V`, `Saturated Λ W`), nonzero.  Then there are finite
`ℤ`-spanning ambient families realising the flag of the pair:

    `∃ u : Fin m → E d, ∃ x : Fin a → E d, ∃ y : Fin b → E d`,
    `span ℤ (range u) = V ⊓ W`,
    `span ℤ (range (Fin.append u x)) = V`,
    `span ℤ (range (Fin.append u y)) = W`,
    `span ℤ (range (Fin.append (Fin.append u x) y)) = V ⊔ W`,

with all four families `ℝ`-linearly independent (members of the lattice `Λ` that are
`ℤ`-independent are automatically `ℝ`-independent).

**Construction (using the delegated abstract basis-extension
`Commons.LinearAlgebra.FreeModule.basis_extend_of_quotient_free`).**
- `N := V ⊓ W` is saturated (`saturated_inf`) and pure in `V` (`pure_inf_left`), so the
  quotient `V ⧸ N` is torsion-free over `ℤ`, hence free (`Module.basisOfFiniteTypeTorsionFree'`).
- View `M := ↥V` with `N̂ := Submodule.comap (V.subtype.restrictScalars ℤ) N ≤ ↥V`
  (≅ `↥N`); apply the delegated lemma to extend a `ℤ`-basis `bN` of `N̂` (from
  `IntrinsicIndex.basis_of_family` on the certified ambient family of `N`) to a
  `ℤ`-basis `bM : Basis (Fin n) ℤ ↥V` with `bN` as its initial segment.
- Coerce `bM` to the ambient family (`v ↦ (v : E d)`); its first `|N-basis|` vectors
  (`u`) span `V ⊓ W`, its remaining vectors (`x`) complete to `V`.  Repeat with `W`
  (same `u`-part from the common basis of `N`) to get `y`; then
  `span ℤ (range (u ++ x ++ y)) = V + W` automatically (the two bases of `V` and `W`
  jointly span their sum) and the family is `ℝ`-independent.
- Degenerate case `V ⊓ W = ⊥`: `u` is the empty family (or any chosen nonempty family
  is only used when needed); the construction still works with `m = 0`.
- Instantiating the submodularity engine `logCovol_submodularity_aligned` with these
  families yields **`logCovol_submodularity_saturated`** (for saturated `V, W`) and the
  join-budget corollary. -/

end Submission.JoinSubmodularity

end
