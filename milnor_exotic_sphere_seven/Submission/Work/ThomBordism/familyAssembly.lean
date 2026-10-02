import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.PontryaginThom.Defs
import Submission.Work.ThomBordism.PontryaginThom.Additivity
import Submission.Work.ThomBordism.PontryaginThom.Hurewicz
import Submission.Work.Tubular.Interface
import Submission.Work.Drive.RationalHurewicz

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The assembly of `TransversalityCoreFamily`, choosing the codimension *per family*

`Work.ThomBordism.TransversalityCoreFamily` quantifies over finite families of closed oriented
`8`-manifolds.  The Pontryagin–Thom chapter (`Submission/Work/ThomBordism/PontryaginThom/`) proves
it from a universal Thom space `D = ThomTarget k` and the geometric data of the members of the
family; its own entry points take the data *uniformly* in the manifold (`PTExists k D`, or
`TubularThomIso k D`), which is why they appear to need a uniform embedding codimension for *all*
closed oriented `8`-manifolds (Whitney's immersion bound `ImmersionBound`).

**That uniformity is not needed.**  Thom's argument only ever handles a finite family: for a finite
family `F : ι → Man8` each member embeds into `ℝ^{8+k}` for every `k` above its own Whitney
codimension (Mathlib's embedding theorem plus padding), and a finite family therefore has a common
codimension `k ≥ 11`, chosen *after* the family.  This file is the assembly with that choice made
explicit:

* `FamilyTubeData k D ι F` — the tubular data (the collapse map and its two Hurewicz pairings, i.e.
  `Work.Tubular.TubeThomRep`) for the *members* of `F` at the codimension `k`;
* `transversalityCoreFamily_of_familyData` — `TransversalityCoreFamily` from, for every finite
  family, *some* `k ≥ 11`, *some* universal Thom space `D = ThomTarget k`, the tubular data of the
  members and both transversality statements; the Pontryagin–Thom classes of the members are then
  assembled by the (proved) additivity `ptAdditivity`, and the vanishing total numbers make a
  positive multiple of the family bound by the family transversality;
* `transversalityCoreFamily_of_uniformData` — the same with one `k` and one `D` serving every
  manifold (the form in which the chapter's own entry points are stated).

Nothing here is a hypothesis of the final theorem: the residual geometric inputs are exactly
`TubeThomRep` (the Tubular chapter: tubular neighbourhood + Thom-class naturality) and
`Transversality`/`TransversalityFamily` (the Transversality chapter), together with the rational
Hurewicz theorem `Work.Drive.RationalHurewiczStable3` in the stable range (areas STEMS/RatHurewicz)
and the universal Thom space `ThomTarget k` (area Grassmann).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom

/-! **Project-lead note (2026-09-25).**  `TransversalityFamily k D` quantifies over an *arbitrary*
loop with the family's pairings, so as an input it is as strong as `TransversalityCoreFamily`
itself; the Transversality chapter proves it only from `TransversalityRealisation`, whose `CoreTarget`
has a *global* `Φ` (so transverse preimages have trivial normal bundle and the Grassmann geometry
cannot be expressed).  The genuine geometric step "“null-homotopy of the genuine collapse ⇒
null-bordism”" is therefore not proved anywhere, and the subproject PTGEOMETRIC
(`Submission/Work/PTGeometric/`) is producing it for the genuine representative built by
`ptAdditivity` from TUBULAR's `TubeThomRep`.  When PTGEOMETRIC states its `G6`, the hypothesis
`htransF` below is to be replaced by its deliverable (equivalently, the definition of
`TransversalityCoreFamily` is consumed directly).  Do *not* build on `TransversalityRealisation`. -/

noncomputable section

/-- **The Pontryagin–Thom data of a manifold from the tubular-neighbourhood chapter's data**: the
normal-bundle data is fixed and the collapse map with its two Hurewicz pairings is exactly what
`Work.Tubular.TubeThomRep` supplies. -/
def ptRepOfTubeThomRep {k : ℕ} {D : ThomTarget k} {V : Man8} {N : NormalBundlData V}
    (r : Work.Tubular.TubeThomRep k D V N) : PTRep V k D where
  normal := N
  collapse := r.collapse
  hurewicz_p1sq := r.hurewicz_p1sq
  hurewicz_p2 := r.hurewicz_p2

/-- **The tubular Pontryagin–Thom data of the members of a family** at a codimension `k` and a
universal Thom space `D`: for each member `F i` and each of its normal-bundle data (canonically,
`NormalBundlData.nonempty`), the collapse map and its two Hurewicz pairings.  Only the members of the
family are concerned, so the codimension `k` may be chosen *after* the family. -/
def FamilyTubeData (k : ℕ) (D : ThomTarget k) (ι : Type) [Fintype ι] (F : ι → Man8) : Prop :=
  ∀ i (N : NormalBundlData (F i)), Nonempty (Work.Tubular.TubeThomRep k D (F i) N)

/-- **`TransversalityCoreFamily` from the per-family geometric data.**

For every finite family `F` of closed oriented `8`-manifolds there is a codimension `k ≥ 11`, a
universal Thom space `D = ThomTarget k` (`T = Th(γ_k)`), the tubular data of the members of `F` and
the two transversality statements.  The codimension is chosen per family: each member embeds into
`ℝ^{8+k}` for every `k` above its own Whitney codimension, so a finite family has a common one and no
uniform immersion bound is needed.

The mathematical content consumed here is `ptAdditivity` (the Pontryagin–Thom class of a disjoint
union is the sum of the classes of its pieces, so the Hurewicz pairings add), the torsion statement
`PTFamilyRep.exists_pow_eq_one_of_numbers_zero_three` (rational Hurewicz in the stable range applied
to the Thom space) and the family transversality statement. -/
theorem transversalityCoreFamily_of_familyData
    (hdata : ∀ (ι : Type) [Fintype ι] (F : ι → Man8),
      ∃ k : ℕ, 11 ≤ k ∧ ∃ D : ThomTarget k,
        FamilyTubeData k D ι F ∧ Transversality k D ∧ TransversalityFamily k D)
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily := by
  intro ι _ F h1 h2
  obtain ⟨k, hk, D, hfam, htrans, htransF⟩ := hdata ι F
  have hrep : ∀ i, Nonempty (PTRep (F i) k D) := fun i => by
    obtain ⟨N⟩ := NormalBundlData.nonempty (F i)
    obtain ⟨r⟩ := hfam i N
    exact ⟨ptRepOfTubeThomRep r⟩
  obtain ⟨r⟩ := (ptAdditivity (k := k) (D := D)) ι F hrep
  obtain ⟨N, hN, hpow⟩ := r.exists_pow_eq_one_of_numbers_zero_three hk hrat h1 h2
  exact htransF ι F r ⟨N, hN, hpow⟩

/-- **`TransversalityCoreFamily` from uniform geometric data**: one codimension `k ≥ 11`, one
universal Thom space `D`, the tubular data of *every* manifold and both transversality statements.
This is the form in which the Pontryagin–Thom chapter's entry points are stated; the per-family
assembly above shows that the uniformity is not needed. -/
theorem transversalityCoreFamily_of_uniformData {k : ℕ} (hk : 11 ≤ k) (D : ThomTarget k)
    (htub : ∀ (V : Man8) (N : NormalBundlData V), Nonempty (Work.Tubular.TubeThomRep k D V N))
    (htrans : Transversality k D) (htransF : TransversalityFamily k D)
    (hrat : Work.Drive.RationalHurewiczStable3) :
    TransversalityCoreFamily :=
  transversalityCoreFamily_of_familyData
    (fun _ _ F => ⟨k, hk, D, fun i N => htub (F i) N, htrans, htransF⟩) hrat

end

end Work.ThomBordism
