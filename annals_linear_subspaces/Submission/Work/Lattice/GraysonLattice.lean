import Mathlib
import Submission.Work.Polygon.GraysonData
import Submission.Commons.Lattice.Minkowski.covolume_zeroDim_dim0
import Submission.Commons.LinearAlgebra.Submodule.realSpan_zero_iff_bot
import Submission.Commons.Lattice.SuccessiveMinima.exact_realization
import Submission.Commons.Lattice.SuccessiveMinima.positive
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent

/-!
# P1-general, first statements: lattice data, real-span dimension, realiser-span blocks

First step of the general-lattice Grayson layer (paper §3 for an arbitrary full-rank
lattice `Λ ≤ ℝᵈ` replacing the coordinate lattice): fix the formal vocabulary of the
Grayson data of a general lattice,

    `subDim W`       — the real dimension of `span_ℝ W` (the rank of the discrete subgroup W)
    `realiserSpan`   — the `ℤ`-span of the first `j` successive-minimum realisers of `Λ`
    `latticeCovol W` — the covolume of `W` inside its own real span (Submission.GraysonData)

and prove the **block-structure lemma**: with exact successive-minimum realisers `v` of
`Λ` (`Commons.Lattice.SuccessiveMinima.exact_realization`), the `ℤ`-span `Wⱼ` of the first
`j` realisers is a rank-`j` subgroup of `Λ` whose intrinsic covolume is bounded by the
product of the first `j` successive minima of `Λ`,

    `latticeCovol(Wⱼ) ≤ ∏_{i : Fin j} λ_{i.val+1}(Λ)`

(hence, by the Grayson-polygon axiom `c ≤ φ` on the data, `c_Λ(j) ≤ Σ_{i≤j} log λᵢ(Λ)` —
the one-sided, `O(1)`-free half of paper Prop 4(2) at the covolume level).  Proof:
`latticeCovol_span` identifies the covolume with the ambient wedge norm of the `j`
realisers, `exteriorPower_norm_wedge_le_prod` bounds the wedge by the product of the
norms, and the realiser property bounds each norm by the corresponding successive
minimum.

All declarations are Mathlib + Submission.GraysonData + Commons successive-minima API only.
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Submission.GraysonLattice

open Submission.GraysonData

/-- The real span of a `ℤ`-submodule `W ≤ ℝᵈ` (ambient `ℝᵈ` of `Submission.GraysonData.E`). -/
def realSpan {d : ℕ} (W : Submodule ℤ (E d)) : Submodule ℝ (E d) :=
  Submodule.span ℝ (W : Set (E d))

/-- The real dimension of `W` (the rank of the discrete subgroup `W` of `ℝᵈ`). -/
def subDim {d : ℕ} (W : Submodule ℤ (E d)) : ℕ := Module.finrank ℝ (realSpan W)

/-- The `ℤ`-span (in `ℝᵈ`) of the first `j` vectors of an ambient family `v : Fin d → ℝᵈ`
with `v i ∈ Λ` (`j ≤ d`). -/
def realiserSpan {d j : ℕ} (v : Fin d → E d) (hjd : j ≤ d) : Submodule ℤ (E d) :=
  Submodule.span ℤ (Set.range (fun k : Fin j => v (Fin.castLE hjd k)))

/-- The realiser span is contained in the lattice `Λ` whenever all the vectors lie in `Λ`. -/
lemma realiserSpan_le {d j : ℕ} (Λ : Submodule ℤ (E d)) (v : Fin d → E d) (hjd : j ≤ d)
    (hvL : ∀ i : Fin d, v i ∈ (Λ : Set (E d))) :
    realiserSpan (d := d) (j := j) v hjd ≤ Λ := by
  dsimp [realiserSpan]
  rw [Submodule.span_le]
  rintro x ⟨k, rfl⟩
  exact hvL (Fin.castLE hjd k)

/-- The real span of the realiser span equals the real span of the subfamily. -/
lemma realSpan_realiserSpan {d j : ℕ} (v : Fin d → E d) (hjd : j ≤ d) :
    realSpan (realiserSpan (d := d) (j := j) v hjd) =
      Submodule.span ℝ (Set.range (fun k : Fin j => v (Fin.castLE hjd k))) := by
  dsimp [realSpan, realiserSpan]
  rw [Submodule.span_span_of_tower (R := ℤ) (S := ℝ) (M := E d)
    (s := Set.range (fun k : Fin j => v (Fin.castLE hjd k)))]

/-- The realiser span of `j` vectors has real dimension `j`, provided they are
`ℝ`-linearly independent. -/
lemma realiserSpan_subDim {d j : ℕ} (v : Fin d → E d) (hjd : j ≤ d)
    (hvli : LinearIndependent ℝ v) :
    subDim (realiserSpan (d := d) (j := j) v hjd) = j := by
  classical
  have hvli' : LinearIndependent ℝ (fun k : Fin j => v (Fin.castLE hjd k)) :=
    hvli.comp (fun k : Fin j => Fin.castLE hjd k) (Fin.castLEEmb hjd).injective
  dsimp [subDim]
  rw [realSpan_realiserSpan v hjd]
  simpa using (finrank_span_eq_card (R := ℝ) hvli')

/-- **Block covolume bound (core)**: for exact realisers `v : Fin d → ℝᵈ` of the lattice
`Λ` (`v i ∈ Λ`, `LinearIndependent ℝ`, `‖vⱼ‖ ≤ λ_{j.val+1}(Λ)`), the `ℤ`-span of the first
`j` realisers has intrinsic covolume bounded by the product of the first `j` successive
minima of `Λ`. -/
theorem realiserSpan_covol_le_prod {d j : ℕ} (Λ : Submodule ℤ (E d)) (v : Fin d → E d)
    (hjd : j ≤ d) (hvli : LinearIndependent ℝ v)
    (hvbd : ∀ i : Fin d, ‖v i‖ ≤
      Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1))
    (hj0 : 0 < j) :
    latticeCovol (realiserSpan (d := d) (j := j) v hjd) ≤
      ∏ i : Fin j, Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1) := by
  classical
  have hvli' : LinearIndependent ℝ (fun k : Fin j => v (Fin.castLE hjd k)) :=
    hvli.comp (fun k : Fin j => Fin.castLE hjd k) (Fin.castLEEmb hjd).injective
  have hw : latticeCovol (realiserSpan (d := d) (j := j) v hjd) =
      ‖exteriorPower.ιMulti ℝ j (fun k : Fin j => v (Fin.castLE hjd k))‖ := by
    dsimp [realiserSpan]
    exact latticeCovol_span (d := d) (r := j) hj0 (fun k : Fin j => v (Fin.castLE hjd k)) hvli'
  have hwedge : ‖exteriorPower.ιMulti ℝ j (fun k : Fin j => v (Fin.castLE hjd k))‖ ≤
      ∏ i : Fin j, ‖v (Fin.castLE hjd i)‖ :=
    Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
      (fun i : Fin j => v (Fin.castLE hjd i))
  have hnorm : ∀ i : Fin j, ‖v (Fin.castLE hjd i)‖ ≤
      Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1) := by
    intro i
    have hb := hvbd (Fin.castLE hjd i)
    simpa using hb
  calc
    latticeCovol (realiserSpan (d := d) (j := j) v hjd)
        = ‖exteriorPower.ιMulti ℝ j (fun k : Fin j => v (Fin.castLE hjd k))‖ := hw
    _ ≤ ∏ i : Fin j, ‖v (Fin.castLE hjd i)‖ := hwedge
    _ ≤ ∏ i : Fin j, Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1) := by
          exact Finset.prod_le_prod (s := Finset.univ)
            (f := fun i : Fin j => ‖v (Fin.castLE hjd i)‖)
            (g := fun i : Fin j => Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1))
            (by intro i hi; exact norm_nonneg _)
            (by intro i hi; exact hnorm i)

/-- **Block-structure lemma (existential, covolume form)**: for a full-rank lattice
`Λ ≤ ℝᵈ` (`finrank ℤ Λ = d`) and `1 ≤ j ≤ d`, there is a rank-`j` subgroup `W ≤ Λ` —
the `ℤ`-span of the first `j` exact successive-minimum realisers — whose intrinsic
covolume is bounded by the product of the first `j` successive minima of `Λ`. -/
theorem exists_subgroup_covol_le_prod {d j : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛ : Module.finrank ℤ Λ = d) (hj1 : 1 ≤ j) (hjd : j ≤ d) :
    ∃ W : Submodule ℤ (E d), W ≤ Λ ∧ subDim W = j ∧
      latticeCovol W ≤
        ∏ i : Fin j, Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1) := by
  classical
  obtain ⟨v, hvli, hvbd⟩ := Commons.Lattice.SuccessiveMinima.exact_realization (E := E d)
    Λ d hΛ
  let vE : Fin d → E d := fun i => ((v i : Λ) : E d)
  have hvL : ∀ i : Fin d, vE i ∈ (Λ : Set (E d)) := by
    intro i
    exact (v i).2
  let W : Submodule ℤ (E d) := realiserSpan (d := d) (j := j) vE hjd
  refine ⟨W, ?_, ?_, ?_⟩
  · dsimp [W]
    exact realiserSpan_le Λ vE hjd hvL
  · dsimp [W]
    exact realiserSpan_subDim vE hjd hvli
  · dsimp [W, vE]
    exact realiserSpan_covol_le_prod Λ vE hjd hvli hvbd (lt_of_lt_of_le Nat.zero_lt_one hj1)

/-- **Block-structure lemma (existential, log form)**: for a full-rank lattice `Λ` and
`1 ≤ j ≤ d`, there is a rank-`j` subgroup `W ≤ Λ` with
`log covol(W) ≤ Σ_{i : Fin j} log λ_{i.val+1}(Λ)`. -/
theorem exists_subgroup_logCovol_le_sum_log {d j : ℕ} (Λ : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛ : Module.finrank ℤ Λ = d)
    (hj1 : 1 ≤ j) (hjd : j ≤ d) :
    ∃ W : Submodule ℤ (E d), W ≤ Λ ∧ subDim W = j ∧
      Real.log (latticeCovol W) ≤
        ∑ i : Fin j, Real.log (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1)) := by
  classical
  obtain ⟨v, hvli, hvbd⟩ := Commons.Lattice.SuccessiveMinima.exact_realization (E := E d)
    Λ d hΛ
  let vE : Fin d → E d := fun i => ((v i : Λ) : E d)
  have hvL : ∀ i : Fin d, vE i ∈ (Λ : Set (E d)) := by
    intro i
    exact (v i).2
  let W : Submodule ℤ (E d) := realiserSpan (d := d) (j := j) vE hjd
  have hj0 : 0 < j := lt_of_lt_of_le Nat.zero_lt_one hj1
  have hcov : latticeCovol W ≤
      ∏ i : Fin j, Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1) := by
    dsimp [W, vE]
    exact realiserSpan_covol_le_prod Λ vE hjd hvli hvbd hj0
  have hcovpos : 0 < latticeCovol W := by
    have hvliE : LinearIndependent ℝ vE := by simpa [vE] using hvli
    have hvli' : LinearIndependent ℝ (fun k : Fin j => vE (Fin.castLE hjd k)) :=
      hvliE.comp (fun k : Fin j => Fin.castLE hjd k) (Fin.castLEEmb hjd).injective
    have hne : exteriorPower.ιMulti ℝ j (fun k : Fin j => vE (Fin.castLE hjd k)) ≠ 0 :=
      Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent
        (fun k : Fin j => vE (Fin.castLE hjd k)) hvli'
    have hw : latticeCovol W =
        ‖exteriorPower.ιMulti ℝ j (fun k : Fin j => vE (Fin.castLE hjd k))‖ := by
      dsimp [W, realiserSpan]
      exact latticeCovol_span (d := d) (r := j) hj0 (fun k : Fin j => vE (Fin.castLE hjd k)) hvli'
    rw [hw]
    exact norm_pos_iff.mpr hne
  have hlampos : ∀ i : Fin j, 0 < Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1) := by
    intro i
    exact Commons.Lattice.SuccessiveMinima.positive Λ (i.val + 1) (by omega) (by rw [hΛ]; omega)
  refine ⟨W, ?_, ?_, ?_⟩
  · dsimp [W]
    exact realiserSpan_le Λ vE hjd hvL
  · dsimp [W]
    exact realiserSpan_subDim vE hjd hvli
  · calc
      Real.log (latticeCovol W) ≤
          Real.log (∏ i : Fin j, Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1)) :=
            Real.log_le_log hcovpos hcov
      _ = ∑ i : Fin j, Real.log (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1)) :=
            (Real.log_prod (s := Finset.univ) (f := fun i : Fin j =>
              Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1))
              (by intro i hi; exact ne_of_gt (hlampos i)))


/-- **One-sided Prop 4(2) lower bound (data form)**: any real function `c` lying below the
Grayson data at every subgroup of `Λ` (`c (subDim W) ≤ log covol W` for all `W ≤ Λ` — the
Grayson-polygon axiom) satisfies, for every `1 ≤ j ≤ d`,

    `c(j) ≤ ∑_{i : Fin j} log λ_{i.val+1}(Λ)`,

by evaluating `c` on the rank-`j` realiser span and chaining
`exists_subgroup_logCovol_le_sum_log`.  (In particular the Grayson polygon `c_Λ` of any
honest per-rank data — once defined — satisfies this; this is the `c(i) ≤ Σ_{t≤i} log λₜ`
half of paper Prop 4(2).) -/
theorem convex_belowData_le_sum_log {d j : ℕ} (Λ : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛ : Module.finrank ℤ Λ = d) (hj1 : 1 ≤ j) (hjd : j ≤ d)
    (c : ℕ → ℝ)
    (hbel : ∀ W : Submodule ℤ (E d), W ≤ Λ → c (subDim W) ≤ Real.log (latticeCovol W)) :
    c j ≤ ∑ i : Fin j, Real.log
      (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1)) := by
  classical
  rcases exists_subgroup_logCovol_le_sum_log (d := d) Λ hΛ hj1 hjd with ⟨W, hWle, hdim, hlog⟩
  calc
    c j = c (subDim W) := by rw [hdim]
    _ ≤ Real.log (latticeCovol W) := hbel W hWle
    _ ≤ ∑ i : Fin j, Real.log
          (Commons.Lattice.SuccessiveMinima.successiveMinimum Λ (i.val + 1)) := hlog


end Submission.GraysonLattice

end
