import Mathlib
import Submission.GeometryOfNumbers.WedgeBlocks
import Submission.GeometryOfNumbers.WedgeBlockZero
import Submission.GeometryOfNumbers.BlockCovering
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Commons.Analysis.Real.sum_log_norm_annulus

/-!
# Wedges of directions inside the contracting block: the `∧^k x₀`-decomposition

Model setting: `x₀ = modelX ℓ` is the coordinate `ℓ`-plane `Span {(B d) j | j.val < ℓ}`,
which is the real span of the contracting block (`BlockCovering.blockSpan ℓ`).  In paper
§3 Prop 5 the first Harder–Narasimhan block `V_{j₁}(ℝ)` is a coordinate subspace inside
`x₀`, and Lemma 5 supplies orthonormal unit directions `u₁..u_m ⊆ V ⊆ x₀`.  This module
proves the **orthogonal decomposition these wedges sit in**: for a family `u : Fin k → ℝᵈ`
of vectors inside `x₀`,

* the wedge `ιMulti u` is its own block-0 component: `blockElem (ιMulti u) 0 = ιMulti u`
  (`blockElem_zero_ιMulti_of_mem_modelX`) — the orthogonal projection `π₀` onto
  `∧^k x₀` (block `0`) acts as the identity;
* every higher block vanishes: `blockElem (ιMulti u) j = 0` for `1 ≤ j`
  (`blockElem_pos_ιMulti_eq_zero_of_mem_modelX`), via vanishing of all Plücker
  coordinates at subsets containing an index `≥ ℓ` (`wcoord_ιMulti_eq_zero_of_mem_modelX`,
  from `WedgeBlocks.wcoord_wedge_zero_of_block_mismatch` with the empty index set);
* if additionally `u` is orthonormal, `‖ιMulti u‖ = 1` (Commons
  `norm_iMulti_orthonormal`).

The assembled statement for the smallFlow setting (`u i ∈ blockSpan ℓ`, the real span of
the contracting block — `wedgeContract_decomposition`) is the input of the Prop-5 wedge
step: directions inside the block give a unit `k`-vector lying in `∧^k x₀`, whose
`π₀`-projection is itself.

The second half of the module makes the working projection first-class: `pi0 ℓ` is the
orthogonal projection of `⋀^k ℝᵈ` onto `∧^k x₀` along the block decomposition, defined as
the linear map `exteriorPower.map k (modelProj ℓ)` (hence `pi0 w = blockElem w 0`).  It is
bounded (`norm_pi0_le`: `‖π₀ w‖ ≤ ‖w‖`), idempotent (`pi0_idempotent`), fixes wedges of
families inside `x₀`/the contracting block (`pi0_ιMulti_of_mem_modelX`,
`pi0_ιMulti_of_mem_blockSpan`), and preserves the unit norm of wedges of orthonormal
families there (`norm_pi0_ιMulti_of_orthonormal`: `‖π₀(ιMulti u)‖ = 1`).  These are the
facts the Prop-5 `π₀`-perturbation lower bound will be built from.

All results here are Mathlib-only (besides the Submission geometry modules).
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.WedgeBlockZero
open Submission.WedgeGeneralE1

namespace Submission.WedgeContract

variable {d k : ℕ}

/-- The orthogonal projection onto `x₀` fixes the vectors of `x₀`. -/
lemma modelProj_apply_of_mem_modelX (ℓ : ℕ) {v : RD d} (hv : v ∈ modelX (d := d) ℓ) :
    modelProj (d := d) ℓ v = v := by
  unfold modelProj
  rw [projMap_apply]
  exact Submodule.starProjection_eq_self_iff.mpr hv

/-- **Block-0 of the wedge of an `x₀`-family is the wedge itself**: for `u i ∈ x₀`, the
orthogonal projection onto `∧^k x₀` (the block of subsets with no index `≥ ℓ`) acts as the
identity on `ιMulti u`. -/
lemma blockElem_zero_ιMulti_of_mem_modelX (ℓ : ℕ) (u : Fin k → RD d)
    (hu : ∀ i, u i ∈ modelX (d := d) ℓ) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0 =
      exteriorPower.ιMulti ℝ k u := by
  have h := WedgeBlockZero.blockElem_zero_ιMulti (d := d) (k := k) ℓ u
  rw [h]
  apply congrArg (exteriorPower.ιMulti ℝ k)
  funext i
  exact modelProj_apply_of_mem_modelX (d := d) ℓ (hu i)

/-- **Plücker coordinates of the wedge of an `x₀`-family vanish outside the block**: at any
`k`-subset `s` with `j ≠ 0` indices `≥ ℓ` (`s ∈ blockFinset j`), `wcoord (ιMulti u) s = 0`.
-/
lemma wcoord_ιMulti_eq_zero_of_mem_modelX (ℓ : ℕ) (u : Fin k → RD d)
    (hu : ∀ i, u i ∈ modelX (d := d) ℓ) {j : ℕ} {s : IDX d k}
    (hs : s ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) j) (hj : j ≠ 0) :
    wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k u) s = 0 := by
  classical
  have hcount : (((s : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card) = j := by
    simpa [blockFinset] using (Finset.mem_filter.mp hs).2
  have hne : (0 : ℕ) ≠ j := by omega
  simpa using (wcoord_wedge_zero_of_block_mismatch (d := d) (k := k) ℓ u (fun _ : Fin k => 0)
    hu (fun _ => Submodule.zero_mem _) (∅ : Finset (Fin k)) s (by
      rw [card_filter_enum_ge (d := d) (k := k) (ℓ := ℓ) s, hcount]
      exact hne))

/-- **Higher blocks of the wedge of an `x₀`-family vanish**: for `1 ≤ j`, the component of
`ιMulti u` in the block of subsets with `j` complement indices is `0`.  Together with
`blockElem_zero_ιMulti_of_mem_modelX` this is the orthogonal decomposition: a wedge of
directions inside `x₀` lies entirely in `∧^k x₀`. -/
lemma blockElem_pos_ιMulti_eq_zero_of_mem_modelX (ℓ : ℕ) (u : Fin k → RD d)
    (hu : ∀ i, u i ∈ modelX (d := d) ℓ) {j : ℕ} (hj : 1 ≤ j) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) j = 0 := by
  classical
  unfold blockElem
  exact Finset.sum_eq_zero (by
    intro s hs
    have hz : wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k u) s = 0 :=
      wcoord_ιMulti_eq_zero_of_mem_modelX (d := d) (k := k) ℓ u hu (s := s) hs (by omega)
    simp [hz])

/-- **Assembled decomposition inside `x₀`**: for an orthonormal family `u : Fin k → ℝᵈ`
with every `u i ∈ x₀ = modelX ℓ`, the wedge `ιMulti u` is its own block-0 component, all
higher components vanish, and its norm is `1`. -/
theorem wedgeInModelX_decomposition (ℓ : ℕ) (u : Fin k → RD d)
    (hu : ∀ i, u i ∈ modelX (d := d) ℓ) (huON : Orthonormal ℝ u) (hk : 0 < k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0 =
        exteriorPower.ιMulti ℝ k u ∧
      (∀ j : ℕ, 1 ≤ j → blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ k u) j = 0) ∧
      ‖exteriorPower.ιMulti ℝ k u‖ = 1 := by
  exact ⟨blockElem_zero_ιMulti_of_mem_modelX (d := d) (k := k) ℓ u hu, fun j hj =>
    blockElem_pos_ιMulti_eq_zero_of_mem_modelX (d := d) (k := k) ℓ u hu (j := j) hj,
    Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal (E := RD d) u huON hk⟩

/-- The real span of the contracting block (`BlockCovering.blockSpan ℓ`) is the reference
plane `x₀ = modelX ℓ` (both are the span of the standard vectors with index `< ℓ`). -/
lemma blockSpan_eq_modelX (ℓ : ℕ) :
    Submission.BlockCovering.blockSpan (d := d) ℓ = modelX (d := d) ℓ := by
  classical
  unfold Submission.BlockCovering.blockSpan
  unfold modelX
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨j.1, j.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, hi⟩, rfl⟩

/-- **Contracting-block wedge decomposition (the smallFlow setting)**: for an orthonormal
family of unit directions `u i` in the real span of the contracting block
(`u i ∈ blockSpan ℓ`, i.e. `u i ∈ x₀`), the wedge `ιMulti u` is its own block-0 component,
all higher blocks vanish, and `‖ιMulti u‖ = 1`.  This is the input of the §3 Prop-5 wedge
step: Lemma-5 directions inside the contracting block give a unit pure tensor lying in
`∧^k x₀`, fixed by the projection `π₀`. -/
theorem wedgeContract_decomposition (ℓ : ℕ) (u : Fin k → RD d)
    (hu : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k) :
    blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0 =
        exteriorPower.ιMulti ℝ k u ∧
      (∀ j : ℕ, 1 ≤ j → blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ k u) j = 0) ∧
      ‖exteriorPower.ιMulti ℝ k u‖ = 1 := by
  have hu' : ∀ i, u i ∈ modelX (d := d) ℓ := fun i => by
    simpa [blockSpan_eq_modelX (d := d) ℓ] using hu i
  exact wedgeInModelX_decomposition (d := d) (k := k) ℓ u hu' huON hk

/-! ### The projection `π₀` onto `∧^k x₀` (model of the paper's `π+`, contracting grade)

The wedge layer's working projection is `π₀ := blockElem (·) 0` — the orthogonal
projection of `⋀^k ℝᵈ` onto `∧^k x₀` along the block decomposition.  We make it
first-class as the bounded linear map `pi0 ℓ = exteriorPower.map k (modelProj ℓ)`
(`blockElem_zero_eq_map_modelProj` identifies it with the block-0 part) and record the
facts the Prop-5 `π₀`-perturbation lower bound rests on:

* `pi0_apply`: `pi0 ℓ w = blockElem w 0`;
* `norm_pi0_le`: `‖π₀ w‖ ≤ ‖w‖` (Pythagoras over the blocks: the block-0 squared norm is a
  single nonnegative summand of `Σⱼ ‖blockElem w j‖² = ‖w‖²`);
* `pi0_idempotent`: `π₀(π₀ w) = π₀ w` (since `P = modelProj ℓ` is an orthogonal projection,
  `map k (P ∘ₗ P) = map k P` by functoriality `exteriorPower.map_comp`);
* `pi0_ιMulti_of_mem_modelX` / `pi0_ιMulti_of_mem_blockSpan`: `π₀` fixes the wedge of any
  family inside `x₀` (the contracting block's real span);
* `norm_pi0_ιMulti_of_orthonormal`: for an orthonormal family inside `x₀`, `‖π₀(ιMulti u)‖
  = 1` — the norm behaviour the lower bound starts from.
-/

/-- The orthogonal projection `π₀` onto `∧^k x₀` (the block-0 component of the exterior-power
decomposition of `⋀^k ℝᵈ` along `x₀ ⊕ x₀ᗮ`), as a linear map.  It equals
`w ↦ blockElem w 0` (`pi0_apply`). -/
def pi0 (ℓ : ℕ) : WK d k →ₗ[ℝ] WK d k :=
  exteriorPower.map k (modelProj (d := d) ℓ)

/-- `π₀` acts as the block-0 component `w ↦ blockElem w 0`. -/
lemma pi0_apply (ℓ : ℕ) (w : WK d k) :
    pi0 (d := d) (k := k) ℓ w = blockElem (d := d) (k := k) (ℓ := ℓ) w 0 := by
  unfold pi0
  exact (WedgeBlockZero.blockElem_zero_eq_map_modelProj (d := d) (k := k) ℓ w).symm

/-- `π₀` is bounded with norm at most `1`: projecting onto the block-0 part cannot increase
the norm (`‖blockElem w 0‖² ≤ Σⱼ ‖blockElem w j‖² = ‖w‖²`). -/
lemma norm_pi0_le (ℓ : ℕ) (w : WK d k) : ‖pi0 (d := d) (k := k) ℓ w‖ ≤ ‖w‖ := by
  rw [pi0_apply]
  have hle0 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ ^ 2 ≤
      (Finset.range (k + 1)).sum (fun r : ℕ =>
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖ ^ 2) := by
    exact Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun r : ℕ => ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖ ^ 2)
      (by intro r hr; exact sq_nonneg _) (a := 0) (Finset.mem_range.mpr (by omega))
  have hle : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [← sum_normSq_blockElem (d := d) (k := k) (ℓ := ℓ) w]
    exact hle0
  have habs : |‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖| ≤ |‖w‖| := sq_le_sq.mp hle
  have hb : 0 ≤ ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := norm_nonneg _
  have hw : 0 ≤ ‖w‖ := norm_nonneg _
  simpa [abs_of_nonneg hb, abs_of_nonneg hw] using habs

/-- `π₀` is an idempotent projection: `π₀(π₀ w) = π₀ w` (functoriality of `⋀^k` applied to
the idempotent orthogonal projection `P = modelProj ℓ`). -/
lemma pi0_idempotent (ℓ : ℕ) (w : WK d k) :
    pi0 (d := d) (k := k) ℓ (pi0 (d := d) (k := k) ℓ w) = pi0 (d := d) (k := k) ℓ w := by
  classical
  let P : RD d →ₗ[ℝ] RD d := modelProj (d := d) ℓ
  have hPP : P ∘ₗ P = P := by
    apply LinearMap.ext
    intro v
    dsimp [P]
    exact modelProj_apply_of_mem_modelX (d := d) ℓ (by
      unfold modelProj
      exact projMap_mem (modelX (d := d) ℓ) v)
  calc
    pi0 (d := d) (k := k) ℓ (pi0 (d := d) (k := k) ℓ w)
        = exteriorPower.map k P (exteriorPower.map k P w) := by rfl
    _ = (exteriorPower.map k P ∘ₗ exteriorPower.map k P) w := by rfl
    _ = exteriorPower.map k (P ∘ₗ P) w := by rw [← exteriorPower.map_comp P P]
    _ = exteriorPower.map k P w := by rw [hPP]

/-- `π₀` is the identity on wedges of families inside `x₀`: `π₀(ιMulti u) = ιMulti u`. -/
lemma pi0_ιMulti_of_mem_modelX (ℓ : ℕ) (u : Fin k → RD d)
    (hu : ∀ i, u i ∈ modelX (d := d) ℓ) :
    pi0 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k u) = exteriorPower.ιMulti ℝ k u := by
  rw [pi0_apply]
  exact blockElem_zero_ιMulti_of_mem_modelX (d := d) (k := k) ℓ u hu

/-- `π₀` preserves the unit norm of wedges of orthonormal families inside `x₀`:
`‖π₀(ιMulti u)‖ = 1`. -/
lemma norm_pi0_ιMulti_of_orthonormal (ℓ : ℕ) (u : Fin k → RD d)
    (hu : ∀ i, u i ∈ modelX (d := d) ℓ) (huON : Orthonormal ℝ u) (hk : 0 < k) :
    ‖pi0 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k u)‖ = 1 := by
  rw [pi0_ιMulti_of_mem_modelX (d := d) (k := k) ℓ u hu]
  exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal (E := RD d) u huON hk

/-- `π₀` is the identity on wedges of families inside the real span of the contracting
block (the smallFlow setting): for `u i ∈ blockSpan ℓ`, `π₀(ιMulti u) = ιMulti u`. -/
lemma pi0_ιMulti_of_mem_blockSpan (ℓ : ℕ) (u : Fin k → RD d)
    (hu : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ) :
    pi0 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k u) = exteriorPower.ιMulti ℝ k u := by
  have hu' : ∀ i, u i ∈ modelX (d := d) ℓ := fun i => by
    simpa [blockSpan_eq_modelX (d := d) ℓ] using hu i
  exact pi0_ιMulti_of_mem_modelX (d := d) (k := k) ℓ u hu'


/-! ### One-slot perturbation of `ιMulti` (step (a) of the `π₀`-perturbation lower bound)

Generic facts (over any finite-dimensional real inner product space `E`) about changing a
single slot of a wedge family — the engine of the `m`-slot telescoping argument:

* `ιMulti_update_add`: `ιMulti` is additive in each slot
  (Mathlib `AlternatingMap.map_update_add`);
* `norm_wedge_update_sub_le`: replacing slot `i` of a family `u` by `u i + δ` changes the
  wedge by exactly `ιMulti (update u i δ)`, of norm at most
  `∏ⱼ ‖(update u i δ) j‖ = (∏_{j≠i} ‖u j‖) · ‖δ‖`
  (additivity + the Commons product bound `exteriorPower_norm_wedge_le_prod`).

In the telescoping each step is this lemma applied to the intermediate family at that step.
-/

/-- One-slot additivity of the wedge: replacing slot `i` of the family by `x + y` splits into
the sum of the replacements by `x` and by `y` (Mathlib `AlternatingMap.map_update_add`). -/
lemma ιMulti_update_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ) (u : Fin m → E) (i : Fin m) (x y : E) :
    exteriorPower.ιMulti ℝ m (Function.update u i (x + y)) =
      exteriorPower.ιMulti ℝ m (Function.update u i x) +
      exteriorPower.ιMulti ℝ m (Function.update u i y) := by
  exact AlternatingMap.map_update_add (f := exteriorPower.ιMulti ℝ m) (v := u) i x y

/-- **One-slot perturbation of the wedge**: replacing slot `i` of the family `u` by
`u i + δ` changes the wedge by `ιMulti (update u i δ)`, whose norm is bounded by
`∏ⱼ ‖(update u i δ) j‖ = (∏_{j≠i} ‖u j‖) · ‖δ‖`. -/
lemma norm_wedge_update_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ) (u : Fin m → E) (i : Fin m) (δ : E) :
    ‖exteriorPower.ιMulti ℝ m (Function.update u i (u i + δ)) -
        exteriorPower.ιMulti ℝ m u‖ ≤
      (∏ j : Fin m, ‖Function.update u i δ j‖) := by
  have hdiff : exteriorPower.ιMulti ℝ m (Function.update u i (u i + δ)) -
        exteriorPower.ιMulti ℝ m u =
      exteriorPower.ιMulti ℝ m (Function.update u i δ) := by
    rw [AlternatingMap.map_update_add (f := exteriorPower.ιMulti ℝ m) (v := u) i (u i) δ]
    rw [Function.update_eq_self]
    abel
  rw [hdiff]
  exact Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
    (Function.update u i δ)


/-! ### The interpolation `w^(r)` and the one-step recurrence (step (b) of the
`π₀`-perturbation lower bound)

Given two families `u v : Fin m → E`, the interpolation `w^(r) := wedgeInterp m u v r`
agrees with `v` on the first `r` slots (by value order: slots `j` with `j.val < r`) and with
`u` on the rest.  Hence `w^(0) = u`, `w^(m) = v`, and `w^(r+1)` is obtained from `w^(r)`
by changing the single slot `⟨r, ·⟩` from `u` to `v`:

* `wedgeInterp_succ_update`: `w^(r+1) = update w^(r) ⟨r,hr⟩ (v ⟨r,hr⟩)`;
* `ιMulti_wedgeInterp_succ`: by `ιMulti_update_add` (with `x = u`, `y = v − u`),
  `ιMulti w^(r+1) = ιMulti w^(r) + ιMulti (update w^(r) ⟨r,hr⟩ (v ⟨r,hr⟩ − u ⟨r,hr⟩))`;
* `ιMulti_wedgeInterp_succ_sub`: the difference form of the same recurrence;
* `ιMulti_sub_eq_sum_telescope`: telescoping over the `m` steps,
  `ιMulti v − ιMulti u = Σ_{i : Fin m} ιMulti (update w^(i.val) i (v i − u i))`
  (`Finset.sum_range_sub` + `Finset.sum_fin_eq_sum_range`).

Each summand is then bounded by `norm_wedge_update_sub_le`, giving the (b) estimate.
-/

/-- The interpolation family between `u` and `v`: `w^(r)` equals `v` on the first `r` slots
(`j.val < r`) and `u` on the remaining ones. -/
def wedgeInterp {E : Type*} (m : ℕ) (u v : Fin m → E) (r : ℕ) : Fin m → E :=
  fun j => if j.val < r then v j else u j

/-- The interpolation at step `0` is the original family `u`. -/
lemma wedgeInterp_zero {E : Type*} (m : ℕ) (u v : Fin m → E) :
    wedgeInterp m u v 0 = u := by
  funext j
  simp [wedgeInterp]

/-- The interpolation at step `m` is the target family `v`. -/
lemma wedgeInterp_self {E : Type*} (m : ℕ) (u v : Fin m → E) :
    wedgeInterp m u v m = v := by
  funext j
  simp [wedgeInterp, j.isLt]

/-- The one-step change of the interpolation: `w^(r+1)` differs from `w^(r)` only at the
single slot `⟨r, hr⟩`, where the value changes from `u` to `v`. -/
lemma wedgeInterp_succ_update {E : Type*} (m : ℕ) (u v : Fin m → E) (r : ℕ) (hr : r < m) :
    wedgeInterp m u v (r + 1) = Function.update (wedgeInterp m u v r) ⟨r, hr⟩ (v ⟨r, hr⟩) := by
  classical
  funext j
  by_cases h : j = ⟨r, hr⟩
  · subst j
    have hlt : (⟨r, hr⟩ : Fin m).val < r + 1 := by
      change r < r + 1
      omega
    simp [wedgeInterp, hlt]
  · rw [Function.update_of_ne h (v ⟨r, hr⟩) (wedgeInterp m u v r)]
    by_cases hlt : j.val < r
    · have hlt' : j.val < r + 1 := by omega
      simp [wedgeInterp, hlt, hlt']
    · have hrle : r ≤ j.val := le_of_not_gt hlt
      have hjne : ¬ j.val = r := by
        intro hc
        exact h (Fin.ext hc)
      have hgt : r < j.val := lt_of_le_of_ne hrle (by exact fun hc => hjne hc.symm)
      have hnot : ¬ j.val < r + 1 := by omega
      simp [wedgeInterp, hlt, hnot]

/-- **One-step recurrence of the interpolation** (sum form): for `0 ≤ r < m`,
`ιMulti w^(r+1) = ιMulti w^(r) + ιMulti (update w^(r) ⟨r,hr⟩ (v ⟨r,hr⟩ − u ⟨r,hr⟩))`,
from `ιMulti_update_add` with `x = u ⟨r,hr⟩`, `y = v ⟨r,hr⟩ − u ⟨r,hr⟩`. -/
lemma ιMulti_wedgeInterp_succ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ) (u v : Fin m → E) (r : ℕ) (hr : r < m) :
    exteriorPower.ιMulti ℝ m (wedgeInterp m u v (r + 1)) =
      exteriorPower.ιMulti ℝ m (wedgeInterp m u v r) +
      exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v r) ⟨r, hr⟩
        (v ⟨r, hr⟩ - u ⟨r, hr⟩)) := by
  have hstep : wedgeInterp m u v (r + 1) =
      Function.update (wedgeInterp m u v r) ⟨r, hr⟩ (v ⟨r, hr⟩) :=
    wedgeInterp_succ_update (m := m) (u := u) (v := v) r hr
  have hval : wedgeInterp m u v r ⟨r, hr⟩ = u ⟨r, hr⟩ := by
    simp [wedgeInterp]
  have hv : v ⟨r, hr⟩ = u ⟨r, hr⟩ + (v ⟨r, hr⟩ - u ⟨r, hr⟩) := by abel
  calc
    exteriorPower.ιMulti ℝ m (wedgeInterp m u v (r + 1))
        = exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v r) ⟨r, hr⟩
            (v ⟨r, hr⟩)) := by rw [hstep]
    _ = exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v r) ⟨r, hr⟩
          (u ⟨r, hr⟩ + (v ⟨r, hr⟩ - u ⟨r, hr⟩))) := by
          conv_lhs => rw [hv]
    _ = exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v r) ⟨r, hr⟩
          (u ⟨r, hr⟩)) +
        exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v r) ⟨r, hr⟩
          (v ⟨r, hr⟩ - u ⟨r, hr⟩)) := by
          exact ιMulti_update_add (m := m) (u := wedgeInterp m u v r) (i := ⟨r, hr⟩)
            (u ⟨r, hr⟩) (v ⟨r, hr⟩ - u ⟨r, hr⟩)
    _ = exteriorPower.ιMulti ℝ m (wedgeInterp m u v r) +
        exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v r) ⟨r, hr⟩
          (v ⟨r, hr⟩ - u ⟨r, hr⟩)) := by
          have hup : Function.update (wedgeInterp m u v r) ⟨r, hr⟩ (u ⟨r, hr⟩) =
              wedgeInterp m u v r := by
            rw [← hval]
            exact Function.update_eq_self ⟨r, hr⟩ (wedgeInterp m u v r)
          rw [hup]

/-- **One-step recurrence of the interpolation** (difference form):
`ιMulti w^(r+1) − ιMulti w^(r) = ιMulti (update w^(r) ⟨r,hr⟩ (v ⟨r,hr⟩ − u ⟨r,hr⟩))`. -/
lemma ιMulti_wedgeInterp_succ_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ) (u v : Fin m → E) (r : ℕ) (hr : r < m) :
    exteriorPower.ιMulti ℝ m (wedgeInterp m u v (r + 1)) -
        exteriorPower.ιMulti ℝ m (wedgeInterp m u v r) =
      exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v r) ⟨r, hr⟩
        (v ⟨r, hr⟩ - u ⟨r, hr⟩)) := by
  have h := ιMulti_wedgeInterp_succ (m := m) (u := u) (v := v) r hr
  rw [h]
  abel

/-- **Telescoping over the interpolation**: `ιMulti v − ιMulti u` is the sum over the `m`
one-step differences `ιMulti (update w^(i.val) i (v i − u i))`. -/
theorem ιMulti_sub_eq_sum_telescope {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ) (u v : Fin m → E) :
    exteriorPower.ιMulti ℝ m v - exteriorPower.ιMulti ℝ m u =
      (Finset.univ : Finset (Fin m)).sum (fun i : Fin m =>
        exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v i.val) i (v i - u i))) := by
  classical
  calc
    exteriorPower.ιMulti ℝ m v - exteriorPower.ιMulti ℝ m u
        = exteriorPower.ιMulti ℝ m (wedgeInterp m u v m) -
            exteriorPower.ιMulti ℝ m (wedgeInterp m u v 0) := by
            rw [wedgeInterp_self m u v, wedgeInterp_zero m u v]
    _ = (Finset.range m).sum (fun r : ℕ =>
          exteriorPower.ιMulti ℝ m (wedgeInterp m u v (r + 1)) -
          exteriorPower.ιMulti ℝ m (wedgeInterp m u v r)) := by
          exact (Finset.sum_range_sub
            (fun r : ℕ => exteriorPower.ιMulti ℝ m (wedgeInterp m u v r)) m).symm
    _ = (Finset.range m).sum (fun r : ℕ =>
          if h : r < m then
            exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v r) ⟨r, h⟩
              (v ⟨r, h⟩ - u ⟨r, h⟩))
          else 0) := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      have hr' : r < m := Finset.mem_range.mp hr
      by_cases h : r < m
      · have hstep := ιMulti_wedgeInterp_succ_sub (m := m) (u := u) (v := v) r hr'
        rw [hstep]
        simp [h]
      · exfalso
        exact h hr'
    _ = (Finset.univ : Finset (Fin m)).sum (fun i : Fin m =>
          exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v i.val) i (v i - u i))) := by
      rw [← Finset.sum_fin_eq_sum_range (fun i : Fin m =>
        exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v i.val) i (v i - u i)))]


/-! ### Normalisation estimates for the annulus family (step (i) of the `π₀` lower bound)

`v̂ = v/‖v‖` denotes the normalised annulus vector.  The estimates here are the cheap
per-direction bound used in the telescoping:

* `norm_smul_inv_sub_le_of_annulus`: if `u` is unit, `v ≠ 0` lies within `C` of `M·u` and
  `|M − ‖v‖| ≤ C`, then `‖v̂ − u‖ ≤ (2C)/‖v‖` — proof:
  `v̂ − u = ‖v‖⁻¹ • (v − ‖v‖·u)` (expand, `smul_sub`), so
  `‖v̂ − u‖ = ‖v‖⁻¹·‖v − ‖v‖·u‖ ≤ ‖v‖⁻¹·(‖v − M·u‖ + ‖M − ‖v‖‖) ≤ ‖v‖⁻¹·2C`;
* `norm_smul_inv_sub_le_one_fifth`: in the annulus of `BlockCovering` — `u` unit, `v ≠ 0`,
  `‖v − 11C·u‖ ≤ C` and `10C ≤ ‖v‖ ≤ 12C` with `C > 0` — `‖v̂ − u‖ ≤ 1/5`
  (`|11C − ‖v‖| ≤ C`, then `(2C)/‖v‖ ≤ (2C)/(10C) = 1/5`);
* `norm_ιMulti_update_wedgeInterp_le_unit`: the single update summand of the telescoping
  identity, in the unit-family context (`‖u j‖ = 1`, `‖v j‖ = 1` — e.g. `u` ON directions,
  `v = v̂` normalised annulus vectors), has norm `≤ ‖v i − u i‖`
  (Commons product bound; the product collapses to `‖v i − u i‖` since every other factor is
  the norm of a unit vector).

Combined: with `u` an ON family in the block and `v̂` the normalised annulus family
(`‖v̂ i − u i‖ ≤ 1/5` by the second lemma), each summand of
`ιMulti_sub_eq_sum_telescope` is bounded by `1/5`.
-/

/-- **Normalisation perturbation**: for a unit `u`, a nonzero `v` within `C` of `M·u` and
with `|M − ‖v‖| ≤ C` (`C ≥ 0`), the unit vector `v/‖v‖` is within `(2C)/‖v‖` of `u`. -/
lemma norm_smul_inv_sub_le_of_annulus {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E} (hu1 : ‖u‖ = 1) (hv0 : v ≠ 0) {M C : ℝ}
    (hdist : ‖v - M • u‖ ≤ C) (hann : ‖M - ‖v‖‖ ≤ C) :
    ‖(‖v‖⁻¹ • v) - u‖ ≤ (2 * C) / ‖v‖ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hu' : u = ‖v‖⁻¹ • (‖v‖ • u) := by
    rw [← mul_smul]
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
    simp
  have hrev : ‖v‖⁻¹ • (v - ‖v‖ • u) = (‖v‖⁻¹ • v) - u := by
    calc
      ‖v‖⁻¹ • (v - ‖v‖ • u) = (‖v‖⁻¹ • v) - ‖v‖⁻¹ • (‖v‖ • u) := by rw [smul_sub]
      _ = (‖v‖⁻¹ • v) - u := by rw [← hu']
  have hsplit : (‖v‖⁻¹ • v) - u = ‖v‖⁻¹ • (v - ‖v‖ • u) := hrev.symm
  have htri : ‖v - ‖v‖ • u‖ ≤ ‖v - M • u‖ + ‖M - ‖v‖‖ := by
    have hd : M • u - ‖v‖ • u = (M - ‖v‖) • u := by rw [← sub_smul]
    have hmain := norm_add_le (v - M • u) (M • u - ‖v‖ • u)
    have hsplit2 : (v - M • u) + (M • u - ‖v‖ • u) = v - ‖v‖ • u := by abel
    rw [hsplit2] at hmain
    -- second summand: ‖M•u − ‖v‖•u‖ = ‖M − ‖v‖‖·‖u‖ = ‖M − ‖v‖‖
    have hd' : ‖M • u - ‖v‖ • u‖ ≤ ‖M - ‖v‖‖ := by
      rw [hd]
      rw [norm_smul]
      simp [Real.norm_eq_abs, hu1]
    linarith
  have hb : ‖v - ‖v‖ • u‖ ≤ 2 * C := by linarith
  have hnn : 0 ≤ ‖v‖⁻¹ := inv_nonneg.mpr (norm_nonneg v)
  have hnorm1 : ‖‖v‖⁻¹ • (v - ‖v‖ • u)‖ = ‖v‖⁻¹ * ‖v - ‖v‖ • u‖ := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg hnn]
  calc
    ‖(‖v‖⁻¹ • v) - u‖ = ‖‖v‖⁻¹ • (v - ‖v‖ • u)‖ := by rw [hsplit]
    _ = ‖v‖⁻¹ * ‖v - ‖v‖ • u‖ := hnorm1
    _ ≤ ‖v‖⁻¹ * (2 * C) := mul_le_mul_of_nonneg_left hb hnn
    _ = (2 * C) / ‖v‖ := by
          rw [div_eq_mul_inv]
          rw [mul_comm]

/-- **Normalisation in the annulus**: for a unit `u` and a nonzero `v` with
`‖v − 11C·u‖ ≤ C` and `10C ≤ ‖v‖ ≤ 12C` (`C > 0`), the unit vector `v/‖v‖` is within
`1/5` of `u`. -/lemma norm_smul_inv_sub_le_one_fifth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E} (hu1 : ‖u‖ = 1) (hv0 : v ≠ 0) {C : ℝ}
    (hdist : ‖v - (11 * C) • u‖ ≤ C) (hlo : (10 * C) ≤ ‖v‖) (hhi : ‖v‖ ≤ (12 * C)) :
    ‖(‖v‖⁻¹ • v) - u‖ ≤ 1 / 5 := by
  have hann : ‖(11 * C) - ‖v‖‖ ≤ C := by
    rw [Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> nlinarith
  have hmain := norm_smul_inv_sub_le_of_annulus (u := u) (v := v) hu1 hv0
    (M := 11 * C) (C := C) hdist hann
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hfin : (2 * C) / ‖v‖ ≤ 1 / 5 := by
    rw [div_le_iff₀ hvpos]
    nlinarith
  exact le_trans hmain hfin
/-- **`k`-dependent per-direction normalisation** (general-`k` annulus): for a unit `u`,
`v ≠ 0` within `C` of `(11k)C·u` with norm in `[(11k−1)C, (11k+1)C]` (`1 ≤ k`), the
normalised vector is within `2/(11k−1)` of `u` — the relative direction error shrinks like
`1/k`, so a `k`-term wedge loses only an absolute amount `2k/(11k−1) ≤ 2/10` (independent
of `k`).  This is the per-direction input of the general-`k` annulus wedge lower bound
(which replaces the fixed `1/5`/`(1 − k/5)` slack of `norm_smul_inv_sub_le_one_fifth`). -/
lemma norm_smul_inv_sub_le_of_annulus_k {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E} (hu1 : ‖u‖ = 1) (hv0 : v ≠ 0) {C : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hdist : ‖v - (((11 : ℝ) * (k : ℝ)) * C) • u‖ ≤ C)
    (hlo : (((11 : ℝ) * (k : ℝ) - 1) * C) ≤ ‖v‖)
    (hhi : ‖v‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * C)) :
    ‖(‖v‖⁻¹ • v) - u‖ ≤ 2 / ((11 : ℝ) * (k : ℝ) - 1) := by
  have hann : ‖((11 : ℝ) * (k : ℝ)) * C - ‖v‖‖ ≤ C := by
    rw [Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> nlinarith
  have hmain := norm_smul_inv_sub_le_of_annulus (u := u) (v := v) hu1 hv0
    (M := ((11 : ℝ) * (k : ℝ)) * C) (C := C) hdist hann
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hdenpos : 0 < (11 : ℝ) * (k : ℝ) - 1 := by
    have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have hfin : (2 * C) / ‖v‖ ≤ 2 / ((11 : ℝ) * (k : ℝ) - 1) := by
    rw [div_le_div_iff₀ hvpos hdenpos]
    nlinarith
  exact le_trans hmain hfin


/-- **Single update summand of the telescoping identity, unit context**: if every `u j` and
`v j` is unit (e.g. `u` an orthonormal family of directions, `v` the family of normalised
annulus vectors), then the `i`-th summand of `ιMulti_sub_eq_sum_telescope` has norm at most
`‖v i − u i‖` (the Commons product bound collapses because all factors but the `i`-th are
unit). -/
lemma norm_ιMulti_update_wedgeInterp_le_unit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (m : ℕ) (u v : Fin m → E) (i : Fin m)
    (hu1 : ∀ j, ‖u j‖ = 1) (hv1 : ∀ j, ‖v j‖ = 1) :
    ‖exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v i.val) i (v i - u i))‖ ≤
      ‖v i - u i‖ := by
  classical
  let f : Fin m → ℝ := fun j => ‖Function.update (wedgeInterp m u v i.val) i (v i - u i) j‖
  have hp := Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
    (Function.update (wedgeInterp m u v i.val) i (v i - u i))
  have hones : ∀ j : Fin m, j ≠ i → f j = 1 := by
    intro j hj
    dsimp [f]
    rw [Function.update_of_ne hj (v i - u i) (wedgeInterp m u v i.val)]
    by_cases hlt : j.val < i.val
    · rw [wedgeInterp]
      simp [hlt, hv1 j]
    · rw [wedgeInterp]
      simp [hlt, hu1 j]
  have hprod : (∏ j : Fin m, f j) = f i := by
    exact Finset.prod_eq_single (s := Finset.univ) (f := f) i
      (by intro b hb hbne; exact hones b hbne) (by intro hi; exact (hi (Finset.mem_univ i)).elim)
  have hfi : f i = ‖v i - u i‖ := by
    simp [f, Function.update_self]
  calc
    ‖exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v i.val) i (v i - u i))‖
        ≤ (∏ j : Fin m, ‖Function.update (wedgeInterp m u v i.val) i (v i - u i) j‖) := hp
    _ = (∏ j : Fin m, f j) := by simp [f]
    _ = f i := hprod
    _ = ‖v i - u i‖ := hfi


/-! ### The telescoping norm bound (step (ii) of the `π₀` lower bound)

With the one-slot facts and the interpolation in hand, the (ii) estimate is a plain
application:

* `norm_smul_inv_eq_one`: normalising a nonzero vector gives a unit vector (`v̂ᵢ` is unit);
* `norm_ιMulti_sub_le_sum`: for two **unit** families `u v : Fin m → E`
  (`∀ j, ‖u j‖ = 1 = ‖v j‖`),
  `‖ιMulti v − ιMulti u‖ ≤ Σᵢ ‖v i − u i‖` — `norm_sum_le` on the telescoping identity
  `ιMulti_sub_eq_sum_telescope`, each summand bounded by
  `norm_ιMulti_update_wedgeInterp_le_unit`;
* `norm_ιMulti_sub_le_of_one_fifth`: if additionally `‖v i − u i‖ ≤ 1/5` for every `i`,
  then `‖ιMulti v − ιMulti u‖ ≤ m/5` (`Finset.sum_const` + `Fintype.card_fin` cleanup).

Assembled with `u` = ON block directions and `v = v̂` (normalised annulus vectors — unit by
`norm_smul_inv_eq_one`, within `1/5` of `u` by `norm_smul_inv_sub_le_one_fifth`), this is
the perturbation budget `‖ιMulti v̂ − ιMulti u‖ ≤ m/5` feeding step (iii).
-/

/-- Normalising a nonzero vector gives a unit vector: `‖(‖x‖⁻¹ • x)‖ = 1`. -/
lemma norm_smul_inv_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (hx : x ≠ 0) : ‖(‖x‖⁻¹ • x)‖ = 1 := by
  rw [norm_smul]
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- **(ii) Telescoping norm bound, generic**: for two unit families `u v : Fin m → E`,
`‖ιMulti v − ιMulti u‖` is at most the sum of the per-index differences `Σᵢ ‖v i − u i‖`. -/
lemma norm_ιMulti_sub_le_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ) (u v : Fin m → E)
    (hu1 : ∀ j, ‖u j‖ = 1) (hv1 : ∀ j, ‖v j‖ = 1) :
    ‖exteriorPower.ιMulti ℝ m v - exteriorPower.ιMulti ℝ m u‖ ≤
      (Finset.univ : Finset (Fin m)).sum (fun i : Fin m => ‖v i - u i‖) := by
  have ht := ιMulti_sub_eq_sum_telescope (m := m) (u := u) (v := v)
  calc
    ‖exteriorPower.ιMulti ℝ m v - exteriorPower.ιMulti ℝ m u‖
        = ‖(Finset.univ : Finset (Fin m)).sum (fun i : Fin m =>
            exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v i.val) i
              (v i - u i)))‖ := by rw [ht]
    _ ≤ (Finset.univ : Finset (Fin m)).sum (fun i : Fin m =>
          ‖exteriorPower.ιMulti ℝ m (Function.update (wedgeInterp m u v i.val) i
            (v i - u i))‖) := norm_sum_le _ _
    _ ≤ (Finset.univ : Finset (Fin m)).sum (fun i : Fin m => ‖v i - u i‖) := by
          apply Finset.sum_le_sum
          intro i hi
          exact norm_ιMulti_update_wedgeInterp_le_unit (m := m) (u := u) (v := v) i hu1 hv1

/-- **(ii) the `m/5` bound**: if additionally every `v i` is within `1/5` of `u i` (and both
families are unit), then `‖ιMulti v − ιMulti u‖ ≤ m/5`. -/
lemma norm_ιMulti_sub_le_of_one_fifth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ) (u v : Fin m → E)
    (hu1 : ∀ j, ‖u j‖ = 1) (hv1 : ∀ j, ‖v j‖ = 1)
    (hclose : ∀ i, ‖v i - u i‖ ≤ (1 / 5 : ℝ)) :
    ‖exteriorPower.ιMulti ℝ m v - exteriorPower.ιMulti ℝ m u‖ ≤ (m : ℝ) / 5 := by
  have hsum := norm_ιMulti_sub_le_sum (m := m) (u := u) (v := v) hu1 hv1
  have hsumle : (Finset.univ : Finset (Fin m)).sum (fun i : Fin m => ‖v i - u i‖) ≤
      (m : ℝ) / 5 := by
    calc
      (Finset.univ : Finset (Fin m)).sum (fun i : Fin m => ‖v i - u i‖)
          ≤ (Finset.univ : Finset (Fin m)).sum (fun _ : Fin m => (1 / 5 : ℝ)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hclose i
      _ = (m : ℝ) * (1 / 5) := by simp [Finset.sum_const, Fintype.card_fin]
      _ = (m : ℝ) / 5 := by ring_nf
  exact le_trans hsum hsumle


/-! ### The `π₀`-perturbation lower bound (step (iii) of the recipe)

The final block assembles the `π₀`-lower bound from the perturbation budget of (ii):

* `norm_pi0_sub_le`: `π₀` is 1-Lipschitz — `‖π₀ x − π₀ y‖ ≤ ‖x − y‖` (linearity
  `map_sub` + `norm_pi0_le` applied to `x − y`);
* `norm_pi0_ge_sub_of_unit_fixed`: reverse triangle — if `π₀` fixes a **unit** vector `w`
  and `z` is within `ε` of `w`, then `‖π₀ z‖ ≥ 1 − ε`;
* **`norm_pi0_ιMulti_ge_sub_one_fifth_of_block`** — the step-(iii) conclusion: for an
  orthonormal family `u` of unit directions in the contracting block's real span
  (`u i ∈ blockSpan ℓ`) and a unit family `v` within `1/5` of `u` pointwise
  (`v = v̂`: the normalised annulus family — unit by `norm_smul_inv_eq_one`, within `1/5`
  by `norm_smul_inv_sub_le_one_fifth`), the `π₀`-projection of the wedge satisfies
  `1 − k/5 ≤ ‖π₀(ιMulti v)‖` — combining `pi0_ιMulti_of_mem_blockSpan`,
  Commons `norm_iMulti_orthonormal` (unit `ιMulti u`), the `m/5` perturbation bound of (ii),
  and the reverse triangle.

(The scaling `‖π₀(v₁∧…∧v_m)‖ = Π‖vᵢ‖·‖π₀(ιMulti v̂)‖ ≥ Π‖vᵢ‖·(1 − k/5)` is the final
step (iv); it needs the per-slot scalar extraction from `ιMulti` and is parked with the
constant policy.)
-/

/-- `π₀` is 1-Lipschitz: `‖π₀ x − π₀ y‖ ≤ ‖x − y‖`. -/
lemma norm_pi0_sub_le (ℓ : ℕ) (x y : WK d k) :
    ‖pi0 (d := d) (k := k) ℓ x - pi0 (d := d) (k := k) ℓ y‖ ≤ ‖x - y‖ := by
  have hlin : pi0 (d := d) (k := k) ℓ (x - y) =
      pi0 (d := d) (k := k) ℓ x - pi0 (d := d) (k := k) ℓ y := by
    exact map_sub (pi0 (d := d) (k := k) ℓ) x y
  rw [← hlin]
  exact norm_pi0_le (d := d) (k := k) ℓ (x - y)

/-- **Reverse triangle for `π₀`**: if `π₀` fixes a unit vector `w` and `z` is within `ε` of
`w`, then `‖π₀ z‖ ≥ 1 − ε`. -/
lemma norm_pi0_ge_sub_of_unit_fixed (ℓ : ℕ) (w z : WK d k) (hw1 : ‖w‖ = 1)
    (hfix : pi0 (d := d) (k := k) ℓ w = w) {ε : ℝ} (hε : ‖z - w‖ ≤ ε) :
    1 - ε ≤ ‖pi0 (d := d) (k := k) ℓ z‖ := by
  have hfixnorm : ‖pi0 (d := d) (k := k) ℓ w‖ = 1 := by
    rw [hfix, hw1]
  have h₀ : ‖pi0 (d := d) (k := k) ℓ w‖ ≤ ‖pi0 (d := d) (k := k) ℓ w - pi0 (d := d) (k := k) ℓ z‖ +
      ‖pi0 (d := d) (k := k) ℓ z‖ := by
    have hveq : (pi0 (d := d) (k := k) ℓ w - pi0 (d := d) (k := k) ℓ z) +
        pi0 (d := d) (k := k) ℓ z = pi0 (d := d) (k := k) ℓ w := by abel
    have hmain := norm_add_le (pi0 (d := d) (k := k) ℓ w - pi0 (d := d) (k := k) ℓ z)
      (pi0 (d := d) (k := k) ℓ z)
    simpa [hveq] using hmain
  have hd : ‖pi0 (d := d) (k := k) ℓ w - pi0 (d := d) (k := k) ℓ z‖ ≤ ε := by
    have h1 := norm_pi0_sub_le (d := d) (k := k) ℓ w z
    have h2 : ‖w - z‖ ≤ ε := by simpa [norm_sub_rev] using hε
    exact le_trans h1 h2
  have h₁ : (1 : ℝ) ≤ ‖pi0 (d := d) (k := k) ℓ w - pi0 (d := d) (k := k) ℓ z‖ +
      ‖pi0 (d := d) (k := k) ℓ z‖ := by
    simpa [hfixnorm] using h₀
  linarith

/-- **Step-(iii) `π₀`-lower bound**: for an orthonormal family `u : Fin k → ℝᵈ` of unit
directions inside the contracting block's real span (`u i ∈ blockSpan ℓ`) and a **unit**
family `v` within `1/5` of `u` pointwise, `1 − k/5 ≤ ‖π₀(ιMulti v)‖`.  Applied with
`u` = Lemma-5 directions and `v = v̂` (normalised annulus vectors: unit by
`norm_smul_inv_eq_one`, within `1/5` by `norm_smul_inv_sub_le_one_fifth`), this is
`‖π₀(ιMulti v̂)‖ ≥ 1 − k/5`. -/
lemma norm_pi0_ιMulti_ge_sub_one_fifth_of_block (ℓ : ℕ) (u v : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (hv1 : ∀ i, ‖v i‖ = 1) (hclose : ∀ i, ‖v i - u i‖ ≤ (1 / 5 : ℝ)) :
    1 - (k : ℝ) / 5 ≤ ‖pi0 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ := by
  let w : WK d k := exteriorPower.ιMulti ℝ k u
  let z : WK d k := exteriorPower.ιMulti ℝ k v
  have hw1 : ‖w‖ = 1 := by
    dsimp [w]
    exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal (E := RD d) u huON hk
  have hfix : pi0 (d := d) (k := k) ℓ w = w := by
    dsimp [w]
    exact pi0_ιMulti_of_mem_blockSpan (d := d) (k := k) ℓ u hu_mem
  have hb : ‖z - w‖ ≤ (k : ℝ) / 5 := by
    dsimp [w, z]
    exact norm_ιMulti_sub_le_of_one_fifth (m := k) (u := u) (v := v)
      (fun j => huON.1 j) hv1 hclose
  have hgoal := norm_pi0_ge_sub_of_unit_fixed (d := d) (k := k) ℓ w z hw1 hfix
    (ε := (k : ℝ) / 5) hb
  simpa [w, z] using hgoal


/-! ### Scaling to `Π‖vᵢ‖` (step (iv) of the recipe)

The per-slot scalar-extraction fact is **already available** — Mathlib's
`AlternatingMap.map_smul_univ` gives, for any alternating map,
`f (fun i => c i • x i) = (∏ i, c i) • f x`; the RD d instance is
`DiagonalFlow.ιMulti_smul_univ` (one line).  No new generic lemma or fleet request needed.

With `v̂ i := ‖v i‖⁻¹ • v i` (the normalised family), `v i = ‖v i‖ • v̂ i` for `v i ≠ 0`, so:

* `norm_pi0_ιMulti_mul_normed`: `‖π₀(ιMulti v)‖ = (∏ᵢ ‖v i‖) · ‖π₀(ιMulti v̂)‖`
  (`ιMulti_smul_univ` with `c i = ‖v i‖`, linearity `map_smul` of `π₀`, `norm_smul`);
* **`norm_pi0_ιMulti_ge_mul_sub_one_fifth_of_block`**: the step-(iv) lower bound — for an
  orthonormal `u` of unit directions inside the contracting block (`u i ∈ blockSpan ℓ`) and
  a nonzero annulus family `v` whose normalisation `v̂` is within `1/5` of `u` pointwise,
  `(∏ᵢ ‖v i‖) · (1 − k/5) ≤ ‖π₀(ιMulti v)‖`
  (the step-(iii) bound `1 − k/5 ≤ ‖π₀(ιMulti v̂)‖` multiplied by the nonnegative
  `∏ᵢ ‖v i‖` and combined with the scaling identity).

The positivity of `(1 − k/5)` (the constant-policy decision turning this into
`‖π₀(v₁∧…∧v_k)‖ ≥ c·Πᵢ‖vᵢ‖` with a universal `c > 0`) is parked for the assembly session.
-/

/-- **`π₀`-scaling identity**: with `v̂ i := ‖v i‖⁻¹ • v i` (`v i ≠ 0`),
`‖π₀(ιMulti v)‖ = (∏ᵢ ‖v i‖) · ‖π₀(ιMulti v̂)‖`. -/
lemma norm_pi0_ιMulti_mul_normed (ℓ : ℕ) (v : Fin k → RD d) (hv0 : ∀ i, v i ≠ 0) :
    ‖pi0 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ =
      (∏ i : Fin k, ‖v i‖) *
        ‖pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (‖v i‖⁻¹) • v i))‖ := by
  have hvi : ∀ i, ‖v i‖ • ((‖v i‖⁻¹) • v i) = v i := by
    intro i
    rw [smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hv0 i))]
    simp
  have hmain : exteriorPower.ιMulti ℝ k v =
      (∏ i : Fin k, ‖v i‖) •
        exteriorPower.ιMulti ℝ k (fun i : Fin k => (‖v i‖⁻¹) • v i) := by
    calc
      exteriorPower.ιMulti ℝ k v
          = exteriorPower.ιMulti ℝ k (fun i : Fin k => ‖v i‖ • ((‖v i‖⁻¹) • v i)) := by
              apply congrArg (exteriorPower.ιMulti ℝ k)
              funext i
              exact (hvi i).symm
      _ = (∏ i : Fin k, ‖v i‖) •
            exteriorPower.ιMulti ℝ k (fun i : Fin k => (‖v i‖⁻¹) • v i) := by
            exact DiagonalFlow.ιMulti_smul_univ (fun i : Fin k => ‖v i‖)
              (fun i : Fin k => (‖v i‖⁻¹) • v i)
  have hpi : pi0 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v) =
      (∏ i : Fin k, ‖v i‖) •
        pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (‖v i‖⁻¹) • v i)) := by
    rw [hmain]
    rw [map_smul]
  have hnn : 0 ≤ (∏ i : Fin k, ‖v i‖) := Finset.prod_nonneg (fun i hi => norm_nonneg _)
  calc
    ‖pi0 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖
        = ‖(∏ i : Fin k, ‖v i‖) •
            pi0 (d := d) (k := k) ℓ
              (exteriorPower.ιMulti ℝ k (fun i : Fin k => (‖v i‖⁻¹) • v i))‖ := by rw [hpi]
    _ = (∏ i : Fin k, ‖v i‖) *
          ‖pi0 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (‖v i‖⁻¹) • v i))‖ := by
          rw [norm_smul]
          rw [Real.norm_eq_abs]
          rw [abs_of_nonneg hnn]

/-- **Step-(iv) `π₀`-lower bound with the `Π‖vᵢ‖` scaling**: for an orthonormal `u` of unit
directions inside the contracting block (`u i ∈ blockSpan ℓ`) and a nonzero annulus family
`v` whose normalisation `v̂ i = ‖v i‖⁻¹ • v i` is within `1/5` of `u` pointwise,
`(∏ᵢ ‖v i‖) · (1 − k/5) ≤ ‖π₀(ιMulti v)‖`. -/
theorem norm_pi0_ιMulti_ge_mul_sub_one_fifth_of_block (ℓ : ℕ) (u v : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k) (hv0 : ∀ i, v i ≠ 0)
    (hclose : ∀ i, ‖(‖v i‖⁻¹) • v i - u i‖ ≤ (1 / 5 : ℝ)) :
    (∏ i : Fin k, ‖v i‖) * (1 - (k : ℝ) / 5) ≤
      ‖pi0 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ := by
  classical
  let vn : Fin k → RD d := fun i => (‖v i‖⁻¹) • v i
  have hv1 : ∀ i, ‖vn i‖ = 1 := by
    intro i
    dsimp [vn]
    exact norm_smul_inv_eq_one (v i) (hv0 i)
  have hclose' : ∀ i, ‖vn i - u i‖ ≤ (1 / 5 : ℝ) := by
    intro i
    simpa [vn] using hclose i
  have hlow := norm_pi0_ιMulti_ge_sub_one_fifth_of_block (d := d) (k := k) ℓ u vn
    hu_mem huON hk hv1 hclose'
  have hprod0 : 0 ≤ (∏ i : Fin k, ‖v i‖) := Finset.prod_nonneg (fun i hi => norm_nonneg _)
  have hmul : (∏ i : Fin k, ‖v i‖) * (1 - (k : ℝ) / 5) ≤
      (∏ i : Fin k, ‖v i‖) * ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k vn)‖ := by
    exact mul_le_mul_of_nonneg_left hlow hprod0
  have heq : ‖pi0 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ =
      (∏ i : Fin k, ‖v i‖) * ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k vn)‖ := by
    simpa [vn] using (norm_pi0_ιMulti_mul_normed (d := d) (k := k) ℓ v hv0)
  exact le_trans hmul (le_of_eq heq.symm)


/-! ### The contracting-block assembly (step (a)-(b): annulus family → `π₀`-lower bound)

The first lock of the Prop-5 model construction, tying `BlockCovering`'s annulus family to
the `π₀`-lower bound machinery of this module:

* `wedgeContract_blockAnnulus_lower`: given an orthonormal family `u : Fin k → ℝᵈ` of unit
  directions in the contracting block's real span (`u i ∈ blockSpan ℓ`, `0 < ℓ ≤ d`,
  `0 < a`) and a family `v : Fin k → smallFlow a b ℓ` of annulus vectors around `11(ℓ:ℝ)a·u`
  (per-index: `‖v i − 11C·u i‖ ≤ C`, `10C ≤ ‖v i‖ ≤ 12C`, `C = (ℓ:ℝ)a`), the lower bound
  `(∏ᵢ ‖v i‖)·(1 − k/5) ≤ ‖π₀(ιMulti (ambient v))‖` holds.  Per index: `v i ≠ 0` from
  `10C ≤ ‖v i‖` and `C > 0`, and `‖v̂ i − u i‖ ≤ 1/5` by `norm_smul_inv_sub_le_one_fifth`;
  then `norm_pi0_ιMulti_ge_mul_sub_one_fifth_of_block`;
* **`exists_wedgeContract_blockAnnulus_lower`** — the instantiation with the Lemma-5
  directions: from the ON `u` alone, `BlockCovering.exists_blockFamily_annulus` produces the
  annulus family, so `∃ v : Fin k → smallFlow a b ℓ` with the `π₀`-lower bound.  (The
  wedge-upper `‖v₁∧…∧v_k‖ ≤ Π‖vᵢ‖ ≤ (12C)^k` and the `c = 1 − k/5` positivity policy are the
  next assembly items.)
-/

/-- **Annulus family → `π₀`-lower bound** (contracting block): with an ON family `u` of unit
directions in `blockSpan ℓ` and an annulus family `v : Fin k → smallFlow a b ℓ` around
`11·(ℓ:ℝ)a·u` per index, `(∏ᵢ ‖v i‖)·(1 − k/5) ≤ ‖π₀(ιMulti (ambient v))‖`. -/
theorem wedgeContract_blockAnnulus_lower (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    (hℓ0 : 0 < ℓ) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd)
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * (ℓ : ℝ) * a) • u i‖ ≤ (ℓ : ℝ) * a ∧
      (10 : ℝ) * (ℓ : ℝ) * a ≤ ‖(v i : RD d)‖ ∧
      ‖(v i : RD d)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * a) :
    (∏ i : Fin k, ‖(v i : RD d)‖) * (1 - (k : ℝ) / 5) ≤
      ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ := by
  classical
  have hv0 : ∀ i, (v i : RD d) ≠ 0 := by
    intro i
    rcases hvann i with ⟨hd, hlo, hhi⟩
    have hpos : 0 < (ℓ : ℝ) * a := mul_pos (by exact_mod_cast hℓ0) ha0
    have hnormpos : 0 < ‖(v i : RD d)‖ := lt_of_lt_of_le (by nlinarith) hlo
    exact norm_pos_iff.mp hnormpos
  have hclose : ∀ i, ‖(‖(v i : RD d)‖⁻¹) • (v i : RD d) - u i‖ ≤ (1 / 5 : ℝ) := by
    intro i
    rcases hvann i with ⟨hd, hlo, hhi⟩
    have hs : (11 * ((ℓ : ℝ) * a)) = ((11 : ℝ) * (ℓ : ℝ)) * a := by ring
    have hd' : ‖(v i : RD d) - (11 * ((ℓ : ℝ) * a)) • u i‖ ≤ (ℓ : ℝ) * a := by
      rw [hs]
      exact hd
    have hlo' : (10 * ((ℓ : ℝ) * a)) ≤ ‖(v i : RD d)‖ := by
      rw [show (10 * ((ℓ : ℝ) * a)) = ((10 : ℝ) * (ℓ : ℝ)) * a by ring]
      exact hlo
    have hhi' : ‖(v i : RD d)‖ ≤ (12 * ((ℓ : ℝ) * a)) := by
      rw [show (12 * ((ℓ : ℝ) * a)) = ((12 : ℝ) * (ℓ : ℝ)) * a by ring]
      exact hhi
    exact norm_smul_inv_sub_le_one_fifth (u := u i) (v := (v i : RD d)) (huON.1 i) (hv0 i)
      (C := (ℓ : ℝ) * a) hd' hlo' hhi'
  exact norm_pi0_ιMulti_ge_mul_sub_one_fifth_of_block (d := d) (k := k) ℓ u
    (fun i : Fin k => (v i : RD d)) hu_mem huON hk hv0 hclose

/-- **Instantiation with the Lemma-5 directions**: for an orthonormal family `u` of unit
directions in the contracting block's real span (`0 < ℓ ≤ d`, `0 < a`), the annulus family
exists (`BlockCovering.exists_blockFamily_annulus`) and satisfies the `π₀`-lower bound:
`∃ v : Fin k → smallFlow a b ℓ, (∏ᵢ ‖v i‖)·(1 − k/5) ≤ ‖π₀(ιMulti (ambient v))‖`. -/
theorem exists_wedgeContract_blockAnnulus_lower (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ}
    (ha0 : 0 < a) (hℓ0 : 0 < ℓ) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k) :
    ∃ v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd,
      (∏ i : Fin k, ‖(v i : RD d)‖) * (1 - (k : ℝ) / 5) ≤
        ‖pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ := by
  classical
  obtain ⟨v, hv⟩ := Submission.BlockCovering.exists_blockFamily_annulus (d := d) ℓ hℓd
    (a := a) (b := b) ha0 (m := k) (u := u) hu_mem (fun i => huON.1 i)
  refine ⟨v, ?_⟩
  exact wedgeContract_blockAnnulus_lower (d := d) ℓ hℓd (a := a) (b := b) ha0 hℓ0 u hu_mem huON hk v hv


/-! ### The wedge-upper and the two-sided sandwich (closing the contracting-block bound)

The upper counterpart at the same block level — no annulus hypotheses needed:

* `wedgeContract_blockAnnulus_upper`: for ANY family `v : Fin k → smallFlow a b ℓ`,
  `‖π₀(ιMulti (ambient v))‖ ≤ ∏ᵢ ‖v i‖` — `norm_pi0_le` (`‖π₀ w‖ ≤ ‖w‖`) followed by the
  Commons product bound `exteriorPower_norm_wedge_le_prod` (`‖v₁∧…∧v_k‖ ≤ ∏ᵢ‖vᵢ‖`);
* **`wedgeContract_blockAnnulus_twoSided`**: combining the lower
  (`wedgeContract_blockAnnulus_lower`: `(∏ᵢ‖v i‖)·(1 − k/5) ≤ ‖π₀(ιMulti v)‖`) and the
  upper into the two-sided sandwich at the annulus hypothesis block:
  `(∏ᵢ ‖v i‖)·(1 − k/5) ≤ ‖π₀(ιMulti v)‖ ≤ ∏ᵢ ‖v i‖`.
-/

/-- **Wedge-upper, contracting block**: for any family `v : Fin k → smallFlow a b ℓ` of block
lattice vectors, `‖π₀(ιMulti (ambient v))‖ ≤ ∏ᵢ ‖v i‖` (`norm_pi0_le` + the Commons product
bound). -/
theorem wedgeContract_blockAnnulus_upper (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ}
    (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd) :
    ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
      (∏ i : Fin k, ‖(v i : RD d)‖) := by
  have h1 := norm_pi0_le (d := d) (k := k) ℓ
    (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))
  have h2 := Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
    (fun i : Fin k => (v i : RD d))
  exact le_trans h1 h2

/-- **Two-sided sandwich, contracting block**: under the annulus hypotheses of
`wedgeContract_blockAnnulus_lower`, the `π₀`-projection of the wedge satisfies
`(∏ᵢ ‖v i‖)·(1 − k/5) ≤ ‖π₀(ιMulti v)‖ ≤ ∏ᵢ ‖v i‖`. -/
theorem wedgeContract_blockAnnulus_twoSided (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    (hℓ0 : 0 < ℓ) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd)
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * (ℓ : ℝ) * a) • u i‖ ≤ (ℓ : ℝ) * a ∧
      (10 : ℝ) * (ℓ : ℝ) * a ≤ ‖(v i : RD d)‖ ∧
      ‖(v i : RD d)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * a) :
    (∏ i : Fin k, ‖(v i : RD d)‖) * (1 - (k : ℝ) / 5) ≤
        ‖pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ∧
      ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (∏ i : Fin k, ‖(v i : RD d)‖) := by
  exact ⟨wedgeContract_blockAnnulus_lower (d := d) ℓ hℓd (a := a) (b := b) ha0 hℓ0 u
    hu_mem huON hk v hvann,
    wedgeContract_blockAnnulus_upper (d := d) ℓ hℓd (a := a) (b := b) v⟩


/-! ### Log-form of the annulus (step (b)) — the model instance

The Commons interval lemma `Commons.Analysis.Real.sum_log_norm_annulus` applied to the
contracting-block annulus family: from the per-index annulus bounds
(`10C ≤ ‖v i‖ ≤ 12C`, `C = (ℓ:ℝ)a > 0`),
`Σᵢ log‖v i‖ ∈ [k·log(10·(ℓ:ℝ)a), k·log(12·(ℓ:ℝ)a)]` (scalar associations converted with
`rw [show … by ring]`).
-/

/-- **Log-interval for the contracting-block annulus family**: from the per-index annulus
bounds (`C = (ℓ:ℝ)a > 0`), `Σᵢ log‖v i‖ ∈ [k·log(10C), k·log(12C)]`. -/
lemma wedgeContract_blockAnnulus_log_interval (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    (hℓ0 : 0 < ℓ) (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd)
    (hlo : ∀ i, (10 : ℝ) * (ℓ : ℝ) * a ≤ ‖(v i : RD d)‖)
    (hhi : ∀ i, ‖(v i : RD d)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * a) :
    (k : ℝ) * Real.log ((10 : ℝ) * (ℓ : ℝ) * a) ≤ (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ∧
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ≤ (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ) * a) := by
  have hC0 : 0 < (ℓ : ℝ) * a := mul_pos (by exact_mod_cast hℓ0) ha0
  have hlo' : ∀ i, (10 * ((ℓ : ℝ) * a)) ≤ ‖(v i : RD d)‖ := by
    intro i
    rw [show (10 * ((ℓ : ℝ) * a)) = ((10 : ℝ) * (ℓ : ℝ)) * a by ring]
    exact hlo i
  have hhi' : ∀ i, ‖(v i : RD d)‖ ≤ (12 * ((ℓ : ℝ) * a)) := by
    intro i
    rw [show (12 * ((ℓ : ℝ) * a)) = ((12 : ℝ) * (ℓ : ℝ)) * a by ring]
    exact hhi i
  have h := Commons.Analysis.Real.sum_log_norm_annulus (E := RD d) k
    (fun i : Fin k => (v i : RD d)) ((ℓ : ℝ) * a) hC0 hlo' hhi'
  have hs10 : (10 * ((ℓ : ℝ) * a)) = ((10 : ℝ) * (ℓ : ℝ)) * a := by ring
  have hs12 : (12 * ((ℓ : ℝ) * a)) = ((12 : ℝ) * (ℓ : ℝ)) * a := by ring
  rwa [hs10, hs12] at h


/-! ### The log-form sandwich (finishing the contracting-block log estimate)

Under the annulus hypotheses, `‖v i‖ ≥ 10C > 0` per index, so with `k ≤ 4` (giving
`0 < 1 − k/5`) every quantity below is positive and its logarithm is legitimate.  The
two-sided `π₀`-sandwich
`(∏ᵢ‖v i‖)·(1 − k/5) ≤ ‖π₀(ιMulti v)‖ ≤ ∏ᵢ‖v i‖` therefore exponentiates (log is
monotone) to the **log-form sandwich with explicit `O(1)` slack `log(1 − k/5)`**:

`Σᵢ log‖v i‖ + log(1 − k/5) ≤ log‖π₀(ιMulti v)‖ ≤ Σᵒ log‖v i‖`

(`Real.log_prod` turns `log(∏ᵢ‖v i‖)` into `Σᵢ log‖v i‖`; `Real.log_mul` splits the
`(1 − k/5)` factor).
-/

/-- **Log-form sandwich, contracting block**: under the annulus hypotheses and `k ≤ 4`,
`Σᵢ log‖v i‖ + log(1 − k/5) ≤ log‖π₀(ιMulti v)‖ ≤ Σᵢ log‖v i‖`. -/
lemma wedgeContract_blockAnnulus_log_twoSided (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    (hℓ0 : 0 < ℓ) (hk4 : k ≤ 4) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd)
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * (ℓ : ℝ) * a) • u i‖ ≤ (ℓ : ℝ) * a ∧
      (10 : ℝ) * (ℓ : ℝ) * a ≤ ‖(v i : RD d)‖ ∧
      ‖(v i : RD d)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * a) :
    (∑ i : Fin k, Real.log ‖(v i : RD d)‖) + Real.log (1 - (k : ℝ) / 5) ≤
        Real.log ‖pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ∧
      Real.log ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := by
  classical
  have htwo := wedgeContract_blockAnnulus_twoSided (d := d) ℓ hℓd (a := a) (b := b) ha0 hℓ0 u
    hu_mem huON hk v hvann
  have hpos : ∀ i, 0 < ‖(v i : RD d)‖ := by
    intro i
    rcases hvann i with ⟨hd, hloi, hhii⟩
    have hC : 0 < (ℓ : ℝ) * a := mul_pos (by exact_mod_cast hℓ0) ha0
    have hpos10 : 0 < (10 : ℝ) * (ℓ : ℝ) * a := by nlinarith
    exact lt_of_lt_of_le hpos10 hloi
  have hprod0 : 0 < (∏ i : Fin k, ‖(v i : RD d)‖) := Finset.prod_pos (fun i hi => hpos i)
  have hkR : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
  have h1m : 0 < 1 - (k : ℝ) / 5 := by nlinarith
  have hpi0 : 0 < ‖pi0 (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ :=
    lt_of_lt_of_le (mul_pos hprod0 h1m) htwo.1
  have hpl : Real.log (∏ i : Fin k, ‖(v i : RD d)‖) =
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := by
    exact Real.log_prod (s := Finset.univ) (f := fun i : Fin k => ‖(v i : RD d)‖)
      (by intro i hi; exact ne_of_gt (hpos i))
  constructor
  · calc
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) + Real.log (1 - (k : ℝ) / 5)
          = Real.log (∏ i : Fin k, ‖(v i : RD d)‖) + Real.log (1 - (k : ℝ) / 5) := by
              rw [← hpl]
      _ = Real.log ((∏ i : Fin k, ‖(v i : RD d)‖) * (1 - (k : ℝ) / 5)) := by
              rw [Real.log_mul (ne_of_gt hprod0) (ne_of_gt h1m)]
      _ ≤ Real.log ‖pi0 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ :=
            Real.log_le_log (mul_pos hprod0 h1m) htwo.1
  · calc
      Real.log ‖pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖
          ≤ Real.log (∏ i : Fin k, ‖(v i : RD d)‖) := Real.log_le_log hpi0 htwo.2
      _ = (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := hpl


/-! ### The exponential-length instance (step (b): `a = exp(−t/ℓ)`)

Specialising the contracting-block estimate to the exponential flow of the model
(`a = exp(−t/ℓ)`, `b = exp(t/(d−ℓ))`, so the contracting scale is `exp(−t/ℓ)`):

* `log_mul_annulus_exp`: endpoint log rewrite — `log(m·(ℓ:ℝ)·exp(−t/ℓ)) =
  log(m·(ℓ:ℝ)) − t/ℓ` (`Real.log_mul` + `Real.log_exp`);
* `wedgeContract_blockAnnulus_log_twoSided_exp`: the log-form sandwich specialised to the
  exponential flow;
* **`wedgeContract_blockAnnulus_log_exp_interval`**: the `Σᵢ log‖v i‖` identity block —
  from the per-index exp-annulus,
  `Σᵢ log‖v i‖ ∈ [k·log(10·(ℓ:ℝ)) − k·t/ℓ, k·log(12·(ℓ:ℝ)) − k·t/ℓ]`
  (log-interval with the endpoints rewritten by the helper).

Combined with the log-sandwich, this gives the first-block estimate
`log‖π₀(ιMulti v)‖ ≤ k·log(12·(ℓ:ℝ)) − t·(k/ℓ) + O(1)` of the polygon chain.
-/

/-- Endpoint log rewrite in the exponential flow: `log (m·(ℓ:ℝ)·exp(−t/ℓ)) =
log (m·(ℓ:ℝ)) − t/ℓ` for `m ≠ 0`, `0 < ℓ`. -/
lemma log_mul_annulus_exp (m : ℝ) (hm : m ≠ 0) (ℓ : ℕ) (hℓ0 : 0 < ℓ) (t : ℝ) :
    Real.log (m * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) =
      Real.log (m * (ℓ : ℝ)) - t / (ℓ : ℝ) := by
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ0)
  have hmℓ : m * (ℓ : ℝ) ≠ 0 := mul_ne_zero hm hℓR
  rw [Real.log_mul hmℓ (Real.exp_ne_zero _)]
  rw [Real.log_exp]
  rw [neg_div]
  rw [← sub_eq_add_neg]

/-- **Log-form sandwich in the exponential flow**: under the exp-annulus hypotheses and
`k ≤ 4`, `Σᵢ log‖v i‖ + log(1 − k/5) ≤ log‖π₀(ιMulti v)‖ ≤ Σᵢ log‖v i‖`. -/
lemma wedgeContract_blockAnnulus_log_twoSided_exp (ℓ : ℕ) (hℓd : ℓ < d) (hℓ0 : 0 < ℓ)
    {t : ℝ} (hk4 : k ≤ 4) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd))
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) • u i‖ ≤
          (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ∧
        (10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) :
    (∑ i : Fin k, Real.log ‖(v i : RD d)‖) + Real.log (1 - (k : ℝ) / 5) ≤
        Real.log ‖pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ∧
      Real.log ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := by
  exact wedgeContract_blockAnnulus_log_twoSided (d := d) ℓ (le_of_lt hℓd)
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) hℓ0 hk4 u hu_mem huON hk v hvann

/-- **Exponential-length interval for the contracting-block annulus family**: under the
per-index exp-annulus bounds (`0 < ℓ`),
`Σᵢ log‖v i‖ ∈ [k·log(10·(ℓ:ℝ)) − k·t/ℓ, k·log(12·(ℓ:ℝ)) − k·t/ℓ]`. -/
lemma wedgeContract_blockAnnulus_log_exp_interval (ℓ : ℕ) (hℓd : ℓ < d) (hℓ0 : 0 < ℓ)
    {t : ℝ} (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd))
    (hlo : ∀ i, (10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v i : RD d)‖)
    (hhi : ∀ i, ‖(v i : RD d)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) :
    (k : ℝ) * Real.log ((10 : ℝ) * (ℓ : ℝ)) - (k : ℝ) * (t / (ℓ : ℝ)) ≤
        (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ∧
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ≤
        (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) - (k : ℝ) * (t / (ℓ : ℝ)) := by
  -- the exp instance of the plain log-interval:
  have hint := wedgeContract_blockAnnulus_log_interval (d := d) ℓ (le_of_lt hℓd)
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) hℓ0 v hlo hhi
  -- hint.1 : (k:ℝ)·log(10·(ℓ:ℝ)·exp(−t/ℓ)) ≤ Σ ; hint.2 : Σ ≤ (k:ℝ)·log(12·(ℓ:ℝ)·exp(−t/ℓ))
  constructor
  · calc
      (k : ℝ) * Real.log ((10 : ℝ) * (ℓ : ℝ)) - (k : ℝ) * (t / (ℓ : ℝ))
          = (k : ℝ) * (Real.log ((10 : ℝ) * (ℓ : ℝ)) - t / (ℓ : ℝ)) := by
              rw [mul_sub]
      _ = (k : ℝ) * Real.log ((10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) := by
              rw [log_mul_annulus_exp (10 : ℝ) (by norm_num) ℓ hℓ0 t]
      _ ≤ (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := hint.1
  · calc
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) ≤
          (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) := hint.2
      _ = (k : ℝ) * (Real.log ((12 : ℝ) * (ℓ : ℝ)) - t / (ℓ : ℝ)) := by
              rw [log_mul_annulus_exp (12 : ℝ) (by norm_num) ℓ hℓ0 t]
      _ = (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) - (k : ℝ) * (t / (ℓ : ℝ)) := by
              rw [mul_sub]


/-! ### The full first-block estimate (upper, then lower)

Assembling the Prop-5 first-block estimate in the exponential flow: the log-sandwich upper
(`log‖π₀(ιMulti v)‖ ≤ Σᵢ log‖v i‖`) chained with the exp-interval upper
(`Σᵢ log‖v i‖ ≤ k·log(12·(ℓ:ℝ)) − k·t/ℓ`) gives the upper; the matching lower absorbs the
`log(1 − k/5)` slack (`k ≤ 4`).

* `wedgeContract_blockAnnulus_log_upper_exp`:
  `log‖π₀(ιMulti v)‖ ≤ k·log(12·(ℓ:ℝ)) − k·t/ℓ`;
* `wedgeContract_blockAnnulus_log_lower_exp`:
  `k·log(10·(ℓ:ℝ)) − k·t/ℓ + log(1 − k/5) ≤ log‖π₀(ιMulti v)‖`.
-/

/-- **First-block upper estimate** (exponential flow): under the exp-annulus hypotheses and
`k ≤ 4`, `log‖π₀(ιMulti v)‖ ≤ k·log(12·(ℓ:ℝ)) − k·t/ℓ`. -/
lemma wedgeContract_blockAnnulus_log_upper_exp (ℓ : ℕ) (hℓd : ℓ < d) (hℓ0 : 0 < ℓ)
    {t : ℝ} (hk4 : k ≤ 4) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd))
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) • u i‖ ≤
          (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ∧
        (10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) :
    Real.log ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
      (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) - (k : ℝ) * (t / (ℓ : ℝ)) := by
  have hlo : ∀ i, (10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v i : RD d)‖ := by
    intro i
    exact (hvann i).2.1
  have hhi : ∀ i, ‖(v i : RD d)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) := by
    intro i
    exact (hvann i).2.2
  have hup := (wedgeContract_blockAnnulus_log_twoSided_exp (d := d) ℓ hℓd hℓ0 (t := t) hk4 u
    hu_mem huON hk v hvann).2
  have hint := (wedgeContract_blockAnnulus_log_exp_interval (d := d) ℓ hℓd hℓ0 (t := t) v
    hlo hhi).2
  exact le_trans hup hint

/-- **First-block lower estimate** (exponential flow): under the exp-annulus hypotheses and
`k ≤ 4`, `k·log(10·(ℓ:ℝ)) − k·t/ℓ + log(1 − k/5) ≤ log‖π₀(ιMulti v)‖`. -/
lemma wedgeContract_blockAnnulus_log_lower_exp (ℓ : ℕ) (hℓd : ℓ < d) (hℓ0 : 0 < ℓ)
    {t : ℝ} (hk4 : k ≤ 4) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd))
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) • u i‖ ≤
          (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ∧
        (10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) :
    (k : ℝ) * Real.log ((10 : ℝ) * (ℓ : ℝ)) - (k : ℝ) * (t / (ℓ : ℝ)) +
        Real.log (1 - (k : ℝ) / 5) ≤
      Real.log ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ := by
  have hlo : ∀ i, (10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v i : RD d)‖ := by
    intro i
    exact (hvann i).2.1
  have hhi : ∀ i, ‖(v i : RD d)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) := by
    intro i
    exact (hvann i).2.2
  have hlow0 := (wedgeContract_blockAnnulus_log_exp_interval (d := d) ℓ hℓd hℓ0 (t := t) v
    hlo hhi).1
  have hlow1 := (wedgeContract_blockAnnulus_log_twoSided_exp (d := d) ℓ hℓd hℓ0 (t := t) hk4 u
    hu_mem huON hk v hvann).1
  have hstep : (k : ℝ) * Real.log ((10 : ℝ) * (ℓ : ℝ)) - (k : ℝ) * (t / (ℓ : ℝ)) +
        Real.log (1 - (k : ℝ) / 5) ≤
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) + Real.log (1 - (k : ℝ) / 5) :=
    add_le_add_left hlow0 (Real.log (1 - (k : ℝ) / 5))
  exact le_trans hstep hlow1


/-! ### The annulus-existence `∃ v` restatement (the §3 bridge)

Restating the first-block upper/lower estimates as existence statements: for ON
Lemma-5-style directions `u : Fin k → ℝᵈ` inside the contracting block's real span, the
exponential-flow annulus family exists (`BlockCovering.exists_blockFamily_annulus` with
`a = exp(−t/ℓ)`, `b = exp(t/(d−ℓ))`) and satisfies the first-block log estimates.

* `exists_wedgeContract_firstBlock_log_upper_exp`:
  `∃ v : Fin k → smallFlow … , log‖π₀(ιMulti (ambient v))‖ ≤ k·log(12·(ℓ:ℝ)) − k·t/ℓ`;
* `exists_wedgeContract_firstBlock_log_lower_exp`: the matching lower with the
  `log(1 − k/5)` slack.
-/

/-- **First-block upper, existence form**: for ON directions `u` in the contracting block's
real span (`k ≤ 4`), there is an annulus family `v : Fin k → smallFlow` (exp flow) whose
`π₀`-wedge satisfies `log‖π₀(ιMulti v)‖ ≤ k·log(12·(ℓ:ℝ)) − k·t/ℓ`. -/
theorem exists_wedgeContract_firstBlock_log_upper_exp (ℓ : ℕ) (hℓd : ℓ < d) (hℓ0 : 0 < ℓ)
    {t : ℝ} (hk4 : k ≤ 4) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k) :
    ∃ v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd),
      Real.log ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) - (k : ℝ) * (t / (ℓ : ℝ)) := by
  classical
  obtain ⟨v, hv⟩ := Submission.BlockCovering.exists_blockFamily_annulus (d := d) ℓ
    (le_of_lt hℓd) (a := Real.exp (-t / (ℓ : ℝ)))
    (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) (Real.exp_pos _) (m := k) (u := u)
    hu_mem (fun i => huON.1 i)
  refine ⟨v, ?_⟩
  exact wedgeContract_blockAnnulus_log_upper_exp (d := d) ℓ hℓd hℓ0 (t := t) hk4 u hu_mem
    huON hk v hv

/-- **First-block lower, existence form**: for ON directions `u` in the contracting block's
real span (`k ≤ 4`), there is an annulus family `v : Fin k → smallFlow` (exp flow) whose
`π₀`-wedge satisfies `k·log(10·(ℓ:ℝ)) − k·t/ℓ + log(1 − k/5) ≤ log‖π₀(ιMulti v)‖`. -/
theorem exists_wedgeContract_firstBlock_log_lower_exp (ℓ : ℕ) (hℓd : ℓ < d) (hℓ0 : 0 < ℓ)
    {t : ℝ} (hk4 : k ≤ 4) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k) :
    ∃ v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd),
      (k : ℝ) * Real.log ((10 : ℝ) * (ℓ : ℝ)) - (k : ℝ) * (t / (ℓ : ℝ)) +
          Real.log (1 - (k : ℝ) / 5) ≤
        Real.log ‖pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ := by
  classical
  obtain ⟨v, hv⟩ := Submission.BlockCovering.exists_blockFamily_annulus (d := d) ℓ
    (le_of_lt hℓd) (a := Real.exp (-t / (ℓ : ℝ)))
    (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) (Real.exp_pos _) (m := k) (u := u)
    hu_mem (fun i => huON.1 i)
  refine ⟨v, ?_⟩
  exact wedgeContract_blockAnnulus_log_lower_exp (d := d) ℓ hℓd hℓ0 (t := t) hk4 u hu_mem
    huON hk v hv


/-! ### The slope-visible first-block bound (the Grayson/HN link)

In the Grayson-polygon picture the contracting block consists of directions of log-scale
`−t/ℓ` each: `log(exp(−t/ℓ)) = −t/ℓ` (`Real.log_exp`), so the first `k` slopes sum to
`−t·(k/ℓ)`.  The slope-visible restatement of the first-block upper bound writes the
exponent's `t`-coefficient explicitly as `k/ℓ`:

* `wedgeContract_firstBlock_slope_sum`: `Σᵢ log(exp(−t/ℓ)) = −t·(k/ℓ)` (the first-k slope
  sum of the polygon segment);
* `wedgeContract_blockAnnulus_log_upper_exp_slope`: the upper bound in the form
  `log‖π₀(ιMulti v)‖ ≤ k·log(12·(ℓ:ℝ)) − t·(k/ℓ)` — the exponent's slope coefficient `k/ℓ`
  visible (the equality `(k:ℝ)·(t/ℓ) = t·((k:ℝ)/ℓ)` is the slope-sum identity in disguise).
-/

/-- **First-`k` slope sum of the contracting segment**: `k` contracting directions each of
log-scale `−t/ℓ` sum to `−t·(k/ℓ)` — the exponent of the first-block estimate, matching the
Grayson-polygon first-segment slope sum. -/
lemma wedgeContract_firstBlock_slope_sum (ℓ : ℕ) {t : ℝ} (k : ℕ) :
    (∑ _ : Fin k, Real.log (Real.exp (-t / (ℓ : ℝ)))) = -(t * ((k : ℝ) / (ℓ : ℝ))) := by
  calc
    (∑ _ : Fin k, Real.log (Real.exp (-t / (ℓ : ℝ))))
        = (∑ _ : Fin k, (-t / (ℓ : ℝ))) := by
            simp [Real.log_exp]
    _ = (k : ℝ) * (-t / (ℓ : ℝ)) := by simp [Finset.sum_const, Fintype.card_fin]
    _ = -(t * ((k : ℝ) / (ℓ : ℝ))) := by
            rw [div_eq_mul_inv]
            ring

/-- **First-block upper bound, slope-visible form**: under the exp-annulus hypotheses and
`k ≤ 4`, `log‖π₀(ιMulti v)‖ ≤ k·log(12·(ℓ:ℝ)) − t·(k/ℓ)` — the exponent's `t`-coefficient
is the polygon first-segment slope-sum `k/ℓ` (cf. `wedgeContract_firstBlock_slope_sum`). -/
lemma wedgeContract_blockAnnulus_log_upper_exp_slope (ℓ : ℕ) (hℓd : ℓ < d) (hℓ0 : 0 < ℓ)
    {t : ℝ} (hk4 : k ≤ 4) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd))
    (hvann : ∀ i, ‖(v i : RD d) - ((11 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) • u i‖ ≤
          (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ∧
        (10 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) :
    Real.log ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
      (k : ℝ) * Real.log ((12 : ℝ) * (ℓ : ℝ)) - t * ((k : ℝ) / (ℓ : ℝ)) := by
  have h := wedgeContract_blockAnnulus_log_upper_exp (d := d) ℓ hℓd hℓ0 (t := t) hk4 u
    hu_mem huON hk v hvann
  have hs : (k : ℝ) * (t / (ℓ : ℝ)) = t * ((k : ℝ) / (ℓ : ℝ)) := by
    rw [div_eq_mul_inv]
    ring
  rwa [hs] at h



/-! ### General-`k` `π₀`-lower bounds and the `(11k)`-anchored annulus lock

The `k ≤ 4` restriction of the fixed-constant lock above (`anchor 11C`, direction error
`1/5`, wedge loss `k/5`) is only needed to keep the slack `1 − k/5` positive.  The
`(11k)`-anchored annulus of `BlockCovering.exists_blockFamily_annulus_k` gives per-direction
error `2/(11k−1) ≤ 1/5`, so the wedge loss is the `k`-dependent quantity
`2k/(11k−1) ≤ 1/5` and the slack `1 − 2k/(11k−1) ≥ 4/5` stays positive for EVERY `k ≥ 1`:

* `norm_pi0_ιMulti_ge_sub_k_of_block` — unit-family `π₀`-lower bound with the `k`-dependent
  error `2/(11k−1)`;
* `norm_pi0_ιMulti_ge_mul_sub_k_of_block` — scaled by `∏ᵢ‖v i‖`;
* **`wedgeContract_blockAnnulus_twoSided_k`** — the general-`k` two-sided `π₀`-sandwich for
  the `(11k)`-annulus family (model Prop-5 contracting lock, no `k ≤ 4`);
* `wedgeContract_blockAnnulus_log_twoSided_k(_exp)` — its log forms.
-/

/-- The general-`k` wedge loss `2k/(11k−1)` is at most `1/5` for `k ≥ 1`, so the slack
`(1 − 2k/(11k−1))` stays at least `4/5` for every `k ≥ 1`. -/
lemma wedgeLoss_k_le_one_fifth (k : ℕ) (hk : 1 ≤ k) :
    (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) ≤ 1 / 5 := by
  have hdenpos : 0 < (11 : ℝ) * (k : ℝ) - 1 := by
    have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  rw [div_le_iff₀ hdenpos]
  have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith

/-- **`π₀`-lower bound on a unit family, general `k`** (contracting block): for an
orthonormal family `u : Fin k → ℝᵈ` of unit directions in `blockSpan ℓ` and a **unit**
family `v` whose per-direction error is `≤ 2/(11k−1)`,
`1 − 2k/(11k−1) ≤ ‖π₀(ιMulti v)‖` — valid for every `k ≥ 1`. -/
lemma norm_pi0_ιMulti_ge_sub_k_of_block (ℓ : ℕ) (u v : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (hv1 : ∀ i, ‖v i‖ = 1)
    (hclose : ∀ i, ‖v i - u i‖ ≤ 2 / ((11 : ℝ) * (k : ℝ) - 1)) :
    1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) ≤
      ‖pi0 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ := by
  let w : WK d k := exteriorPower.ιMulti ℝ k u
  let z : WK d k := exteriorPower.ιMulti ℝ k v
  have hw1 : ‖w‖ = 1 := by
    dsimp [w]
    exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal (E := RD d) u huON hk
  have hfix : pi0 (d := d) (k := k) ℓ w = w := by
    dsimp [w]
    exact pi0_ιMulti_of_mem_blockSpan (d := d) (k := k) ℓ u hu_mem
  have hsum : ‖z - w‖ ≤ (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) := by
    dsimp [w, z]
    have hsum0 : ‖exteriorPower.ιMulti ℝ k v - exteriorPower.ιMulti ℝ k u‖ ≤
        (∑ i : Fin k, ‖v i - u i‖) :=
      norm_ιMulti_sub_le_sum (m := k) (u := u) (v := v)
        (fun j => huON.1 j) hv1
    have hsumle : (∑ i : Fin k, ‖v i - u i‖) ≤
        (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) := by
      calc
        (∑ i : Fin k, ‖v i - u i‖)
            ≤ (∑ _ : Fin k, (2 / ((11 : ℝ) * (k : ℝ) - 1))) := by
              apply Finset.sum_le_sum
              intro i hi
              exact hclose i
        _ = (k : ℝ) * (2 / ((11 : ℝ) * (k : ℝ) - 1)) := by
              simp [Finset.sum_const, Fintype.card_fin]
        _ = (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) := by ring
    exact le_trans hsum0 hsumle
  have hgoal := norm_pi0_ge_sub_of_unit_fixed (d := d) (k := k) ℓ w z hw1 hfix
    (ε := (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) hsum
  simpa [w, z] using hgoal

/-- **`π₀`-lower bound with the `Π‖vᵢ‖` scaling, general `k`** (contracting block): for an
orthonormal `u` of unit directions in the contracting block and a nonzero family `v` whose
normalisation `v̂ i = ‖v i‖⁻¹ • v i` is within `2/(11k−1)` of `u` pointwise,
`(∏ᵢ ‖v i‖) · (1 − 2k/(11k−1)) ≤ ‖π₀(ιMulti v)‖`. -/
theorem norm_pi0_ιMulti_ge_mul_sub_k_of_block (ℓ : ℕ) (u v : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k) (hv0 : ∀ i, v i ≠ 0)
    (hclose : ∀ i, ‖(‖v i‖⁻¹) • v i - u i‖ ≤ 2 / ((11 : ℝ) * (k : ℝ) - 1)) :
    (∏ i : Fin k, ‖v i‖) * (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) ≤
      ‖pi0 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ := by
  classical
  let vn : Fin k → RD d := fun i => (‖v i‖⁻¹) • v i
  have hv1 : ∀ i, ‖vn i‖ = 1 := by
    intro i
    dsimp [vn]
    exact norm_smul_inv_eq_one (v i) (hv0 i)
  have hclose' : ∀ i, ‖vn i - u i‖ ≤ 2 / ((11 : ℝ) * (k : ℝ) - 1) := by
    intro i
    simpa [vn] using hclose i
  have hlow := norm_pi0_ιMulti_ge_sub_k_of_block (d := d) (k := k) ℓ u vn
    hu_mem huON hk hv1 hclose'
  have hprod0 : 0 ≤ (∏ i : Fin k, ‖v i‖) := Finset.prod_nonneg (fun i hi => norm_nonneg _)
  have hmul : (∏ i : Fin k, ‖v i‖) * (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) ≤
      (∏ i : Fin k, ‖v i‖) * ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k vn)‖ := by
    exact mul_le_mul_of_nonneg_left hlow hprod0
  have heq : ‖pi0 (d := d) (k := k) ℓ (exteriorPower.ιMulti ℝ k v)‖ =
      (∏ i : Fin k, ‖v i‖) * ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k vn)‖ := by
    simpa [vn] using (norm_pi0_ιMulti_mul_normed (d := d) (k := k) ℓ v hv0)
  exact le_trans hmul (le_of_eq heq.symm)

/-- **Two-sided `π₀`-sandwich, general `k` (contracting block, `a b` flow)**: with an ON
family `u` of unit directions in `blockSpan ℓ` and an annulus family `v : Fin k → smallFlow
a b ℓ` around `(11k)·((ℓ:ℝ))·a·u` per index (`1 ≤ k`), the two-sided estimate
`(∏ᵢ‖v i‖)·(1 − 2k/(11k−1)) ≤ ‖π₀(ιMulti v)‖ ≤ ‖ιMulti v‖` holds — no `k ≤ 4`
restriction. -/
theorem wedgeContract_blockAnnulus_twoSided_k (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    (hℓ0 : 0 < ℓ) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd)
    (hvann : ∀ i, ‖(v i : RD d) -
          (((11 : ℝ) * (k : ℝ)) * (ℓ : ℝ) * a) • u i‖ ≤ (ℓ : ℝ) * a ∧
        (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) * a ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) * a) :
    (∏ i : Fin k, ‖(v i : RD d)‖) * (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) ≤
        ‖pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ∧
      ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d))‖ := by
  classical
  have hv0 : ∀ i, (v i : RD d) ≠ 0 := by
    intro i
    rcases hvann i with ⟨hd, hlo, hhi⟩
    have hpos : 0 < (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) * a := by
      have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
      have hC : 0 < (ℓ : ℝ) * a := mul_pos (by exact_mod_cast hℓ0) ha0
      nlinarith
    have hnormpos : 0 < ‖(v i : RD d)‖ := lt_of_lt_of_le hpos hlo
    exact norm_pos_iff.mp hnormpos
  have hclose : ∀ i, ‖(‖(v i : RD d)‖⁻¹) • (v i : RD d) - u i‖ ≤
      2 / ((11 : ℝ) * (k : ℝ) - 1) := by
    intro i
    rcases hvann i with ⟨hd, hlo, hhi⟩
    let C : ℝ := (ℓ : ℝ) * a
    have hs1 : (((11 : ℝ) * (k : ℝ)) * (ℓ : ℝ) * a) = ((11 : ℝ) * (k : ℝ)) * C := by
      dsimp [C]
      ring
    have hs2 : (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) * a = ((11 : ℝ) * (k : ℝ) - 1) * C := by
      dsimp [C]
      ring
    have hs3 : (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) * a = ((11 : ℝ) * (k : ℝ) + 1) * C := by
      dsimp [C]
      ring
    have hd' : ‖(v i : RD d) - (((11 : ℝ) * (k : ℝ)) * C) • u i‖ ≤ C := by
      rw [← hs1]
      simpa [C] using hd
    have hlo' : ((11 : ℝ) * (k : ℝ) - 1) * C ≤ ‖(v i : RD d)‖ := by
      rw [← hs2]
      exact hlo
    have hhi' : ‖(v i : RD d)‖ ≤ ((11 : ℝ) * (k : ℝ) + 1) * C := by
      rw [← hs3]
      exact hhi
    have hk1 : 1 ≤ k := lt_of_lt_of_le Nat.zero_lt_one hk
    exact norm_smul_inv_sub_le_of_annulus_k (u := u i)
      (v := (v i : RD d)) (huON.1 i) (hv0 i) (C := C) hk1 hd' hlo' hhi'
  have hlow := norm_pi0_ιMulti_ge_mul_sub_k_of_block (d := d) (k := k) ℓ u
    (fun i : Fin k => (v i : RD d)) hu_mem huON hk hv0 hclose
  constructor
  · simpa using hlow
  · exact norm_pi0_le (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))

/-- **Log-form sandwich, contracting block, general `k`**: under the `(11k)`-anchored
annulus hypotheses and `1 ≤ k` (no `k ≤ 4` restriction), with the `k`-dependent wedge loss
`2k/(11k−1)`, `Σᵢ log‖v i‖ + log(1 − 2k/(11k−1)) ≤ log‖π₀(ιMulti v)‖ ≤ Σᵢ log‖v i‖`. -/
lemma wedgeContract_blockAnnulus_log_twoSided_k (ℓ : ℕ) (hℓd : ℓ ≤ d) {a b : ℝ} (ha0 : 0 < a)
    (hℓ0 : 0 < ℓ) (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d) a b ℓ hℓd)
    (hvann : ∀ i, ‖(v i : RD d) -
          (((11 : ℝ) * (k : ℝ)) * (ℓ : ℝ) * a) • u i‖ ≤ (ℓ : ℝ) * a ∧
        (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) * a ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) * a) :
    (∑ i : Fin k, Real.log ‖(v i : RD d)‖) +
        Real.log (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) ≤
        Real.log ‖pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ∧
      Real.log ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := by
  classical
  have htwo := wedgeContract_blockAnnulus_twoSided_k (d := d) ℓ hℓd (a := a) (b := b) ha0 hℓ0 u
    hu_mem huON hk v hvann
  have hpos : ∀ i, 0 < ‖(v i : RD d)‖ := by
    intro i
    rcases hvann i with ⟨hd, hloi, hhii⟩
    have hposlo : 0 < (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) * a := by
      have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
      have hC : 0 < (ℓ : ℝ) * a := by
        exact mul_pos (by exact_mod_cast hℓ0) ha0
      nlinarith
    exact lt_of_lt_of_le hposlo hloi
  have hprod0 : 0 < (∏ i : Fin k, ‖(v i : RD d)‖) := Finset.prod_pos (fun i hi => hpos i)
  have hk1 : 1 ≤ k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hloss : (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) ≤ 1 / 5 :=
    wedgeLoss_k_le_one_fifth k hk1
  have hlosslt1 : (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) < 1 := by
    exact lt_of_le_of_lt hloss (by norm_num)
  have h1m : 0 < 1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) := by
    linarith
  have hpi0 : 0 < ‖pi0 (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ :=
    lt_of_lt_of_le (mul_pos hprod0 h1m) htwo.1
  have hpl : Real.log (∏ i : Fin k, ‖(v i : RD d)‖) =
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := by
    exact Real.log_prod (s := Finset.univ) (f := fun i : Fin k => ‖(v i : RD d)‖)
      (by intro i hi; exact ne_of_gt (hpos i))
  have hprod_le : ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (∏ i : Fin k, ‖(v i : RD d)‖) := by
    have h1 := norm_pi0_le (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))
    have h2 := Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
      (fun i : Fin k => (v i : RD d))
    exact le_trans h1 h2
  constructor
  · calc
      (∑ i : Fin k, Real.log ‖(v i : RD d)‖) +
            Real.log (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1))
          = Real.log (∏ i : Fin k, ‖(v i : RD d)‖) +
            Real.log (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) := by
              rw [← hpl]
      _ = Real.log ((∏ i : Fin k, ‖(v i : RD d)‖) *
            (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1))) := by
              rw [Real.log_mul (ne_of_gt hprod0) (ne_of_gt h1m)]
      _ ≤ Real.log ‖pi0 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ :=
            Real.log_le_log (mul_pos hprod0 h1m) htwo.1
  · calc
      Real.log ‖pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖
          ≤ Real.log (∏ i : Fin k, ‖(v i : RD d)‖) := Real.log_le_log hpi0 hprod_le
      _ = (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := hpl

/-- **Log-form sandwich in the exponential flow (contracting block), general `k`**: the
exp instance of `wedgeContract_blockAnnulus_log_twoSided_k` — same sandwich
`Σᵢ log‖v i‖ + log(1 − 2k/(11k−1)) ≤ log‖π₀(ιMulti v)‖ ≤ Σᵢ log‖v i‖` for every `1 ≤ k`. -/
lemma wedgeContract_blockAnnulus_log_twoSided_k_exp (ℓ : ℕ) (hℓd : ℓ < d) (hℓ0 : 0 < ℓ)
    {t : ℝ} (u : Fin k → RD d)
    (hu_mem : ∀ i, u i ∈ Submission.BlockCovering.blockSpan (d := d) ℓ)
    (huON : Orthonormal ℝ u) (hk : 0 < k)
    (v : Fin k → Submission.FlowLatticeMinimaLower.smallFlow (d := d)
        (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd))
    (hvann : ∀ i, ‖(v i : RD d) -
          (((11 : ℝ) * (k : ℝ)) * (ℓ : ℝ) *
            Real.exp (-t / (ℓ : ℝ))) • u i‖ ≤
          (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)) ∧
        (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) *
            Real.exp (-t / (ℓ : ℝ)) ≤ ‖(v i : RD d)‖ ∧
        ‖(v i : RD d)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) *
            Real.exp (-t / (ℓ : ℝ))) :
    (∑ i : Fin k, Real.log ‖(v i : RD d)‖) +
        Real.log (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) ≤
        Real.log ‖pi0 (d := d) (k := k) ℓ
          (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ∧
      Real.log ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : RD d)))‖ ≤
        (∑ i : Fin k, Real.log ‖(v i : RD d)‖) := by
  exact wedgeContract_blockAnnulus_log_twoSided_k (d := d) ℓ (le_of_lt hℓd)
    (a := Real.exp (-t / (ℓ : ℝ))) (b := Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))
    (Real.exp_pos _) hℓ0 u hu_mem huON hk v hvann

end Submission.WedgeContract
