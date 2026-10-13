/-
# `Work.FTS.LocData.DzIter_bumpZ_bound`

The bump `bumpZ z = χ(4z - 5)` (`Work.FTS.LocData.bumpZ`) is `C^∞` with support contained in the
closed interval `[3/4, 7/4]`, so its first four iterates under `D_z = z ∂_z` are bounded on the
quadrant, uniformly in `θ`.  This is the estimate that makes the localised bump
`hLoc α = bumpZ · Γ` a legitimate `ℋ⁴`-datum of the route: its `D_z`-derivatives up to order `4`
are bounded by a universal constant (`HkIntegrand_hLoc_le` needs exactly this).

The proof does not expand `χ`: it only uses that the smooth bump has *compact support*, and the
elementary fact that the operator `T g z = z ∂_z g z` preserves both `C^∞` and the property of
vanishing off a fixed closed interval (a function vanishing on a neighbourhood of `z` has
derivative `0` there).

## The argument

* `T1 g z = z * deriv g z` is the action of `D_z` on functions of `z` alone; the (curried)
  operator of the workspace agrees with it: `DzIter_bumpZ_eq`.
* The invariant `P g := (ContDiff ℝ ∞ g ∧ ∀ z ∉ [3/4, 7/4], g z = 0)` is preserved by `T1`
  (`T1_iterate_contDiff`): `∞ g` gives `∞ (deriv g)` (`Work.FTS.LocData.contDiff_deriv`), hence
  `∞ (T1 g) = ∞ (z · deriv g)`; and `T1 g` vanishes off the interval because `deriv g` does
  (`deriv_eq_zero_of_eq_zero_off_closed`, from `Filter.EventuallyEq.deriv_eq`).
* A continuous function vanishing off `[3/4, 7/4]` is bounded
  (`Work.FTS.LocData.exists_bound_of_continuous_of_vanishes_off_Icc`, by compactness of the
  interval), so each of the five iterates `c ≤ 4` has its own bound `M c`
  (`exists_bound_T1_iterate_bumpZ`); their sum `∑_{c ≤ 4} M c` is the requested universal
  constant.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.BumpZ_contDiff
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.exists_bound_of_continuous_of_vanishes_off_Icc
import Submission.Work.FTS.LocData.contDiff_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **The action of `D_z = z ∂_z` on functions of `z` alone**: `T1 g z = z ∂_z g z`.  This is
`Work.Spaces.Dz` on a function which does not depend on `θ`; pulling the iteration down to one
variable makes the compact-support argument transparent. -/
noncomputable def T1 (g : ℝ → ℝ) : ℝ → ℝ := fun z => z * deriv g z

/-- A function vanishing off a *closed* set has zero derivative on the complement: the complement
is open, so such a point has a whole neighbourhood on which the function is `0`. -/
theorem deriv_eq_zero_of_eq_zero_off_closed {g : ℝ → ℝ} {s : Set ℝ} (hs : IsClosed s)
    (hvan : ∀ z', z' ∉ s → g z' = 0) {z : ℝ} (hz : z ∉ s) : deriv g z = 0 := by
  have hmem : sᶜ ∈ 𝓝 z := hs.isOpen_compl.mem_nhds hz
  have hev : g =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hmem] with z' hz'
    exact hvan z' hz'
  rw [Filter.EventuallyEq.deriv_eq hev]
  simp

/-- `T1` preserves `C^∞`: the derivative of a smooth function is smooth. -/
theorem T1_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (T1 g) := by
  have h := (contDiff_deriv hg).1
  rw [show T1 g = (fun z : ℝ => z * deriv g z) from rfl]
  exact ContDiff.mul contDiff_id h

/-- **The invariant of the iteration**: every iterate of `T1` applied to a smooth function
vanishing off `[3/4, 7/4]` is again smooth and vanishes off `[3/4, 7/4]`. -/
theorem T1_iterate_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hvan : ∀ z, z ∉ Set.Icc (3 / 4 : ℝ) (7 / 4) → g z = 0) (c : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) ((T1^[c]) g) ∧
      ∀ z, z ∉ Set.Icc (3 / 4 : ℝ) (7 / 4) → (T1^[c]) g z = 0 := by
  induction c with
  | zero => exact ⟨by simpa using hg, by simpa using hvan⟩
  | succ c ih =>
      obtain ⟨hc, hv⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_succ_apply']
        exact T1_contDiff hc
      · intro z hz
        rw [Function.iterate_succ_apply']
        show z * deriv ((T1^[c]) g) z = 0
        rw [deriv_eq_zero_of_eq_zero_off_closed isClosed_Icc hv hz, mul_zero]

/-- Every iterate of `T1` on `bumpZ` is bounded on the whole line. -/
theorem exists_bound_T1_iterate_bumpZ (c : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ, |(T1^[c]) bumpZ z| ≤ M := by
  obtain ⟨hc, hv⟩ := T1_iterate_contDiff BumpZ_contDiff bumpZ_eq_zero_of_notMem_Icc c
  exact exists_bound_of_continuous_of_vanishes_off_Icc (by norm_num) hc.continuous hv

/-- **`D_z^c` on `bumpZ` as a function of `z` is the `c`-th iterate of `T1`.**  The `θ`-variable is
a dummy in `fun z _ => bumpZ z`, so `Work.Spaces.pz` is the plain derivative. -/
theorem DzIter_bumpZ_eq (c : ℕ) (θ z : ℝ) :
    Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ = (T1^[c]) bumpZ z := by
  induction c generalizing z with
  | zero => rfl
  | succ c ih =>
      rw [Work.Spaces.DzIter_succ, Function.iterate_succ_apply']
      have hfun : (fun z' : ℝ => Work.Spaces.DzIter c (fun z _ => bumpZ z) z' θ)
          = (T1^[c]) bumpZ := funext fun z' => ih z'
      show z * deriv (fun z' : ℝ => Work.Spaces.DzIter c (fun z _ => bumpZ z) z' θ) z
          = T1 ((T1^[c]) bumpZ) z
      rw [hfun]
      rfl

/-- **The `D_z`-derivatives of the bump up to order `4` are uniformly bounded.** -/
theorem DzIter_bumpZ_bound :
    ∃ C : ℝ, ∀ c : ℕ, c ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      |Work.Spaces.DzIter c (fun z _ => bumpZ z) z θ| ≤ C := by
  classical
  let M : ℕ → ℝ := fun c => Classical.choose (exists_bound_T1_iterate_bumpZ c)
  have hM : ∀ c : ℕ, 0 ≤ M c ∧ ∀ z : ℝ, |(T1^[c]) bumpZ z| ≤ M c := fun c =>
    Classical.choose_spec (exists_bound_T1_iterate_bumpZ c)
  refine ⟨∑ c ∈ Finset.range 5, M c, ?_⟩
  intro c hc z _hz θ
  rw [DzIter_bumpZ_eq c θ z]
  have h1 : |(T1^[c]) bumpZ z| ≤ M c := (hM c).2 z
  have h2 : M c ≤ ∑ d ∈ Finset.range 5, M d :=
    Finset.single_le_sum (fun d _ => (hM d).1) (Finset.mem_range.mpr (by omega))
  linarith

end Work.FTS.LocData
