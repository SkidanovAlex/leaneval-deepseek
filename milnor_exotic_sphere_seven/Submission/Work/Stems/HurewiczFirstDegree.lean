import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.Stems.HurewiczMap
import Submission.Work.Stems.Hur2c.hurewiczMapN_injective_firstDegree
import Submission.Work.Stems.hurewiczMapN_surjective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The integral Hurewicz theorem in the first non-vanishing degree

Requested by the project lead for the subproject **SERRE**
(`Submission/Work/Drive/SERRE_BLUEPRINT.md`, blueprint step **S1**, where it is used to conclude
that `π_m(Y)` is torsion when `Y` is simply connected and `H̃_*(Y;ℚ) = 0` up to degree `m ≥ 2`).

> **`Work.Stems.hurewicz_first_degree`**: if `Y` is `(m-1)`-connected (`m ≥ 2`, i.e.
> `Subsingleton (HomotopyGroup (Fin i) Y y₀)` for all `i < m`, which includes `π₀`), then the
> Hurewicz map `Work.Stems.hurewiczMapN m _ y₀ : π_m(Y,y₀) → H_m(Y;ℤ)` is **bijective**.

This is the classical Hurewicz isomorphism theorem (Hurewicz 1935; Hutchings, *The Hurewicz
theorem*; Hatcher §2.A / §4.2).  The statement is phrased with the **fork-neutral**
`Work.Stems.hurewiczMapN` (`Submission/Work/Stems/HurewiczNeutral.lean`) so that it can be imported
next to `Work.Drive.Interfaces`; the additive packaging of the same map is
`Work.Stems.hurewiczHom` (`Submission/Work/Stems/HurewiczMapNatural.lean`), and
`Work.Stems.hurewiczMapN_mul` below records its additivity in the fork-neutral vocabulary (the form
in which the "Hurewicz image torsion ⟹ the class is torsion" corollary is applied).

## Provenance and status (AREA STEMS)

* `m = 2`: the cubical proof of Hutchings is being formalised in `Submission/Work/Stems/Hur2/` and
  `Submission/Work/Stems/Hur2b/`.  There the ingredients are `K₀`, `K₁` (`Hur2/Kfill.lean`), the
  filling `Ψ` (`Hur2/PsiCont.lean`, `Hur2b/Assembly.lean`), the properties `(Z)`
  (`PsiLin_single_based`), `(Y)` (`Hur2b/PsiLin_cubD_single`, in progress), `(i)`
  (degenerate cubes) and the comparison of the singular (simplex) chains with the cubical ones.
* `m ≥ 3`: the same proof is uniform in `m` (Hutchings' construction of the cubical homotopy
  operators `K_i : C_i → C_{i+1}` uses only `π_i(Y) = 0` for `i < m`), but the formalisation has to
  be redone in all degrees; the comparison step is blueprint **E1** of `SERRE_BLUEPRINT.md`
  (triangulate the cube into `n!` simplices, or acyclic models), **not** the "cumulative
  coordinates" homeomorphism of `Submission/Work/Stems/Hur2/PLAN.md`, which is *false* for
  `n ≥ 2` (it collapses the face `t₀ = 1`); see `Submission/Work/Stems/HUR2B_NOTES.md` §"WARNING".

## Main statements

* `Work.Stems.hurewicz_first_degree` — the interface for SERRE, **proved**: the injectivity half
  is `Work.Stems.Hur2c.hurewiczMapN_injective_firstDegree` (area STEMS' cubical development) and
  the surjectivity half is `Work.Stems.hurewiczMapN_surjective`.
* `Work.Stems.hurewiczMapN_mul` — additivity of the Hurewicz map (proved, fork-neutral); the
  `N`-th-power form `hurewiczMapN (a^N) = N • hurewiczMapN a` follows by induction using it (and
  needs `Work.Stems.hurewiczMap_one` for the base case, which lives in `Stems/HurewiczMapNatural`).
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

/-- **The integral Hurewicz theorem in the first non-vanishing degree.**  For `m ≥ 2` and an
`(m-1)`-connected space `Y` (all `πᵢ(Y,y₀)`, `i < m`, trivial — `π₀` included), the Hurewicz map
`π_m(Y,y₀) → H_m(Y;ℤ)` is bijective. -/
theorem hurewicz_first_degree {Y : Type} [TopologicalSpace Y] (m : ℕ) (hm : 2 ≤ m) (y₀ : Y)
    (hconn : ∀ i : ℕ, i < m → Subsingleton (HomotopyGroup (Fin i) Y y₀)) :
    Function.Bijective (hurewiczMapN m (by omega) y₀) :=
  ⟨Hur2c.hurewiczMapN_injective_firstDegree m hm y₀ hconn,
    hurewiczMapN_surjective m hm y₀ hconn⟩

/-- **Additivity of the Hurewicz map**, in the fork-neutral vocabulary: this is
`Work.Stems.hurewiczMap_mul` transported along the definitional identification
`hurewiczMapN = hurewiczMap`. -/
theorem hurewiczMapN_mul {Y : Type} [TopologicalSpace Y] (n : ℕ) (y₀ : Y)
    (a b : HomotopyGroup (Fin (n + 1)) Y y₀) :
    hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) y₀ (a * b) =
      hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) y₀ a +
        hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) y₀ b :=
  hurewiczMap_mul n a b

end

end Work.Stems
