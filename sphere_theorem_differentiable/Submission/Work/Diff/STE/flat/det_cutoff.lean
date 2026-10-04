/-
# The determinant cut-off for the flat short-time existence theorem

Given `n ≥ 1`, `lam > 0` and `KA ≥ 0`, we construct a smooth nonnegative function `χ` on the space
`Jet n` of spatial `2`-jets which

* equals `1` on the admissible set `goodSet n lam KA` (entries bounded by `KA`, real metric matrix
  uniformly elliptic with constant `lam / 2`);
* is *supported* in the nondegenerate set `detSet n` (nonzero determinant of the real metric
  matrix).

The construction is the smooth Urysohn lemma: `goodSet n lam KA` is closed (`goodSet_isClosed`),
`detSet n` is open (`detSet_isOpen`), and the former is contained in the latter
(`goodSet_subset_detSet`, from the quadratic-form description of ellipticity).  A closed set inside
an open set is separated by a smooth function via normality (`normal_exists_closure_subset`) and
Mathlib's smooth Urysohn lemma `exists_contDiff_support_eq_eq_one_iff`.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.det_cutoff_defs
import Submission.Work.Diff.STE.flat.det_ne_zero_of_quadForm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology
open Set

namespace Work.Diff.STE.flat

noncomputable section

/-! ### The general smooth Urysohn lemma -/

/-- **Smooth Urysohn lemma.**  A closed subset `K` of a finite-dimensional real normed space which
is contained in an open set `U` is separated from the complement of `U` by a nonnegative smooth
function which is `1` on `K` and whose topological support lies in `U`. -/
theorem smooth_urysohn_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K U : Set E} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ x, 0 ≤ f x) ∧ tsupport f ⊆ U ∧
      ∀ x ∈ K, f x = 1 := by
  -- shrink `U` to an open set whose closure is still inside `U`
  obtain ⟨u, huopen, hKu, hucl⟩ := normal_exists_closure_subset hK hU hKU
  -- Mathlib's smooth Urysohn: a smooth function with support exactly `u`, equal to `1` on `K`
  obtain ⟨f, hfsm, hfr, hfsupp, hfone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) (s := u) (t := K) huopen hK hKu
  refine ⟨f, hfsm, fun x => (hfr ⟨x, rfl⟩).1, ?_, fun x hx => (hfone x).mp hx⟩
  rw [tsupport, hfsupp]
  exact hucl

/-! ### The two sets -/

/-- `goodSet n lam KA` is closed: it is an intersection of closed conditions (finitely many norm
bounds and, for each direction `v`, a closed half-space). -/
theorem goodSet_isClosed (n : ℕ) (lam KA : ℝ) : IsClosed (goodSet n lam KA) := by
  have h1 : IsClosed {w : Work.Diff.STE.Flat.Jet n | ∀ i j, ‖w.1 i j‖ ≤ KA} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun i => ?_
    rw [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  have h2 : IsClosed {w : Work.Diff.STE.Flat.Jet n | ∀ c i j, ‖w.2.1 c i j‖ ≤ KA} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun c => ?_
    rw [Set.setOf_forall]
    refine isClosed_iInter fun i => ?_
    rw [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  have h3 : IsClosed {w : Work.Diff.STE.Flat.Jet n | ∀ c d i j, ‖w.2.2 c d i j‖ ≤ KA} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun c => ?_
    rw [Set.setOf_forall]
    refine isClosed_iInter fun d => ?_
    rw [Set.setOf_forall]
    refine isClosed_iInter fun i => ?_
    rw [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  have h4 : IsClosed {w : Work.Diff.STE.Flat.Jet n | ∀ v : Fin n → ℝ,
      (lam / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat w.1 i j * v i * v j} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun v => ?_
    refine isClosed_le continuous_const ?_
    simp only [Work.Diff.STE.Flat.reMat_apply]
    fun_prop
  have h : goodSet n lam KA = {w : Work.Diff.STE.Flat.Jet n | ∀ i j, ‖w.1 i j‖ ≤ KA} ∩
      {w : Work.Diff.STE.Flat.Jet n | ∀ c i j, ‖w.2.1 c i j‖ ≤ KA} ∩
      {w : Work.Diff.STE.Flat.Jet n | ∀ c d i j, ‖w.2.2 c d i j‖ ≤ KA} ∩
      {w : Work.Diff.STE.Flat.Jet n | ∀ v : Fin n → ℝ,
        (lam / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat w.1 i j * v i * v j} := by
    ext w
    simp only [goodSet, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [h]
  exact ((h1.inter h2).inter h3).inter h4

/-- `detSet n` is open: it is the preimage of the open set `{x | x ≠ 0}` under the continuous map
`w ↦ (reMat w.1).det`. -/
theorem detSet_isOpen (n : ℕ) : IsOpen (detSet n) := by
  have hmat : Continuous (fun w : Work.Diff.STE.Flat.Jet n =>
      Work.Diff.STE.Flat.reMat w.1) := by
    apply continuous_matrix
    intro i j
    simp only [Work.Diff.STE.Flat.reMat_apply]
    fun_prop
  have hcont : Continuous (fun w : Work.Diff.STE.Flat.Jet n =>
      (Work.Diff.STE.Flat.reMat w.1).det) :=
    Continuous.matrix_det hmat
  have h := hcont.isOpen_preimage {x : ℝ | x ≠ 0} isOpen_ne
  simpa only [detSet, Set.preimage_ofPred_eq, Set.mem_ofPred_eq] using h

/-- The admissible set is contained in the nondegenerate set: uniform ellipticity of the quadratic
form forces invertibility of the real metric matrix. -/
theorem goodSet_subset_detSet (n : ℕ) (lam KA : ℝ) (hlam : 0 < lam) :
    goodSet n lam KA ⊆ detSet n := by
  rintro w ⟨-, -, -, h4⟩
  exact det_ne_zero_of_quadForm_le (Work.Diff.STE.Flat.reMat w.1) (half_pos hlam) h4

/-! ### The cut-off -/

theorem det_cutoff (n : ℕ) (hn : 1 ≤ n) (lam : ℝ) (hlam : 0 < lam) (KA : ℝ) (hKA : 0 ≤ KA) :
    ∃ χ : Work.Diff.STE.Flat.Jet n → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ w, 0 ≤ χ w) ∧
      tsupport χ ⊆ {w : Work.Diff.STE.Flat.Jet n | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0} ∧
      (∀ w : Work.Diff.STE.Flat.Jet n, (∀ i j, ‖w.1 i j‖ ≤ KA) →
        (∀ c i j, ‖w.2.1 c i j‖ ≤ KA) → (∀ c d i j, ‖w.2.2 c d i j‖ ≤ KA) →
        (∀ v : Fin n → ℝ, (lam / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat w.1 i j * v i * v j) → χ w = 1) := by
  obtain ⟨χ, hsm, hnn, hsupp, hone⟩ :=
    smooth_urysohn_closed (goodSet_isClosed n lam KA) (detSet_isOpen n)
      (goodSet_subset_detSet n lam KA hlam)
  exact ⟨χ, hsm, hnn, hsupp, fun w h1 h2 h3 h4 => hone w ⟨h1, h2, h3, h4⟩⟩

end

end Work.Diff.STE.flat
