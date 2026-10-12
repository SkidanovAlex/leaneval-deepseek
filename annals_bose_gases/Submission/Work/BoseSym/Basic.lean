import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Submission.Neumann
import Submission.Symmetry
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — the bosonic reduction (node S): core definitions

This module sets up the Banach/Hilbert framework in which the bosonic
(Perron–Frobenius) reduction of the ground-state energy of `N` particles in a
box of side `L` is carried out.

The configuration space is `Conf N = Fin N → EuclideanSpace ℝ (Fin 3)`, with
Lebesgue measure.  A function `F` on it has a gradient with `3N` components,
indexed by `GIdx N = Fin N × Fin 3` (particle `i`, coordinate `k`); the
corresponding unit direction is `kcDir N i k`.

The *ambient space* `Amb N` is the product of `L²(Conf N)` (for the function)
with `∏_{j : GIdx N} L²(Conf N)` (for the gradient components), with
`‖p‖² = ‖p.1‖² + ∑_j ‖p.2 j‖²`.

The *Dirichlet energy space* `Hsub N L` is the closure, in `Amb N`, of the set
of pairs `(F, ∇F)` for `F` ranging over the smooth functions whose support is
compact inside the open box `openBox N L`.  All the analysis of the bosonic
reduction happens on this space: the energy form, the absolute-value
inequality, the permutation action, and the minimiser construction.

## Main definitions

* `Vpot N v` : the pair interaction `x ↦ ∑_{i<j} v(x_i - x_j)`;
* `Vtrunc N v M` : its truncation `min (Vpot) M` at level `M`;
* `testSub N L` : the module of smooth functions supported in the open box;
* `graphPoint` : the pair `(F, ∇F)`, as an element of `Amb N`;
* `Hsub N L` : the Dirichlet energy space (closed submodule of `Amb N`);
* `l2Sq`, `gSq`, `hSq`, `dirForm`, `mForm` : the `L²`-norm-squared, the
  gradient-norm-squared, the graph norm, the Dirichlet form and the
  `M`-shifted inner-product form;
* `jEmbed` : the continuous linear inclusion `Hsub N L → L²(Conf N)`.
-/

namespace Work.BoseSym

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real ContDiff ENNReal

noncomputable section

set_option autoImplicit false

/-- The one-particle space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `N`-particle configuration space. -/
abbrev Conf (N : ℕ) : Type := Fin N → E3

/-- Gradient indices: particle `i`, coordinate `k`. -/
abbrev GIdx (N : ℕ) : Type := Fin N × Fin 3

/-- Lebesgue measure on configuration space. -/
abbrev volC (N : ℕ) : Measure (Conf N) := volume

/-- The `L²` space of real functions on configuration space. -/
abbrev L2 (N : ℕ) : Type := Lp ℝ 2 (volC N)

/-- The ambient Banach space: an `L²` function together with its `3N` gradient
components. -/
abbrev Amb (N : ℕ) : Type := L2 N × (GIdx N → L2 N)

/-! ## The pair interaction -/

/-- The pair interaction as a function on configuration space:
`Vpot N v x = ∑_{i < j} v (x i - x j)`. -/
def Vpot (N : ℕ) (v : E3 → ℝ) (x : Conf N) : ℝ :=
  ∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)), v (x p.1 - x p.2)

/-- The truncated pair interaction `min (Vpot N v x) M`. -/
def Vtrunc (N : ℕ) (v : E3 → ℝ) (M : ℝ) (x : Conf N) : ℝ := min (Vpot N v x) M

lemma Vpot_nonneg {N : ℕ} {v : E3 → ℝ} (hv : 0 ≤ v) (x : Conf N) : 0 ≤ Vpot N v x :=
  Finset.sum_nonneg fun p _ => hv _

lemma Vtrunc_nonneg {N : ℕ} {v : E3 → ℝ} (hv : 0 ≤ v) {M : ℝ} (hM : 0 ≤ M)
    (x : Conf N) : 0 ≤ Vtrunc N v M x :=
  le_min (Vpot_nonneg hv x) hM

lemma Vtrunc_le_Vpot (N : ℕ) (v : E3 → ℝ) (M : ℝ) (x : Conf N) :
    Vtrunc N v M x ≤ Vpot N v x := min_le_left _ _

lemma Vtrunc_le (N : ℕ) (v : E3 → ℝ) (M : ℝ) (x : Conf N) : Vtrunc N v M x ≤ M :=
  min_le_right _ _

lemma Vtrunc_mono (N : ℕ) (v : E3 → ℝ) {M M' : ℝ} (h : M ≤ M') (x : Conf N) :
    Vtrunc N v M x ≤ Vtrunc N v M' x := min_le_min le_rfl h

/-! ## Smooth test functions supported in the open box -/

/-- Smooth functions whose support is compact inside the open box. -/
def testFun (N : ℕ) (L : ℝ) : Set (Conf N → ℝ) :=
  {F | ContDiff ℝ ∞ F ∧ tsupport F ⊆ openBox N L}

lemma testFun_zero (N : ℕ) (L : ℝ) : (0 : Conf N → ℝ) ∈ testFun N L :=
  ⟨contDiff_const, by simp [tsupport]⟩

lemma testFun_add {N : ℕ} {L : ℝ} {F G : Conf N → ℝ} (hF : F ∈ testFun N L)
    (hG : G ∈ testFun N L) : F + G ∈ testFun N L := by
  refine ⟨hF.1.add hG.1, ?_⟩
  refine (tsupport_add _ _).trans (Set.union_subset hF.2 hG.2)

lemma testFun_smul {N : ℕ} {L : ℝ} {c : ℝ} {F : Conf N → ℝ} (hF : F ∈ testFun N L) :
    c • F ∈ testFun N L := by
  refine ⟨hF.1.const_smul c, ?_⟩
  by_cases hc : c = 0
  · subst hc
    simp [tsupport]
  · have hsub : Function.support (c • F) ⊆ tsupport F := fun x hx =>
      subset_tsupport F (by simpa [Function.mem_support, hc] using hx)
    exact (closure_minimal hsub (isClosed_tsupport F)).trans hF.2

/-- The module of smooth test functions supported in the open box. -/
def testSub (N : ℕ) (L : ℝ) : Submodule ℝ (Conf N → ℝ) where
  carrier := testFun N L
  add_mem' hF hG := testFun_add hF hG
  zero_mem' := testFun_zero N L
  smul_mem' c _ hF := testFun_smul (c := c) hF

/-- The open box sits inside the compact box of side `max L 1`. -/
lemma openBox_subset_box_max {N : ℕ} (L : ℝ) : openBox N L ⊆ box N (max L 1) := by
  intro x hx i k
  have h := hx i k
  exact ⟨le_of_lt h.1, le_trans (le_of_lt h.2) (le_max_left L 1)⟩

/-- The support of a test function is compact. -/
lemma hasCompactSupport_of_testFun {N : ℕ} {L : ℝ} {F : Conf N → ℝ}
    (hF : F ∈ testFun N L) : HasCompactSupport F :=
  IsCompact.of_isClosed_subset (box_compact (N := N) (L := max L 1) (lt_max_of_lt_right one_pos))
    (isClosed_tsupport F) (hF.2.trans (openBox_subset_box_max (N := N) L))

/-- A smooth function with compact support is in `L²`. -/
theorem memLp_of_contDiff_hasCompactSupport {N : ℕ} {f : Conf N → ℝ}
    (hf : ContDiff ℝ ∞ f) (hcs : HasCompactSupport f) : MemLp f 2 (volC N) :=
  hf.continuous.memLp_of_hasCompactSupport hcs

open Submission.BoseGases in
/-- The graph point of a test function: the pair `(F, ∇F)`. -/
noncomputable def graphPoint (N : ℕ) (L : ℝ) (F : testSub N L) : Amb N :=
  (MemLp.toLp (F : Conf N → ℝ)
      (memLp_of_contDiff_hasCompactSupport F.2.1 (hasCompactSupport_of_testFun F.2)),
   fun j => MemLp.toLp (fun x => fderiv ℝ (F : Conf N → ℝ) x (kcDir N j.1 j.2))
      (memLp_of_contDiff_hasCompactSupport
        (firstDir_contDiff F.2.1 (kcDir N j.1 j.2))
        (IsCompact.of_isClosed_subset (hasCompactSupport_of_testFun F.2)
          (isClosed_tsupport _) (tsupport_firstDir_subset _))))

/-- The Dirichlet energy space: the closure in `Amb N` of the graph of the
gradient over the test functions supported in the open box. -/
def Hsub (N : ℕ) (L : ℝ) : Submodule ℝ (Amb N) :=
  (Submodule.span ℝ (Set.range (graphPoint N L))).topologicalClosure

/-! ## The energy forms -/

/-- The squared `L²` norm of the function part. -/
def l2Sq {N : ℕ} (p : Amb N) : ℝ := ‖p.1‖ ^ 2

/-- The squared norm of the gradient part. -/
def gSq {N : ℕ} (p : Amb N) : ℝ := ∑ j : GIdx N, ‖p.2 j‖ ^ 2

/-- The squared graph norm `‖u‖² + ‖∇u‖²`. -/
def hSq {N : ℕ} (p : Amb N) : ℝ := l2Sq p + gSq p

/-- The potential energy `∫ W · u²` of the function part. -/
def potSq {N : ℕ} (W : Conf N → ℝ) (p : Amb N) : ℝ := ∫ x, W x * (p.1 x) ^ 2

/-- The Dirichlet form `∫ |∇u|² + ∫ W u²` of the function part. -/
def dirForm {N : ℕ} (W : Conf N → ℝ) (p : Amb N) : ℝ := gSq p + potSq W p

/-! ## The inclusion into `L²` -/

/-- The continuous linear inclusion `Hsub N L → L²(Conf N)`, taking the
function part. -/
noncomputable def jEmbed (N : ℕ) (L : ℝ) : Hsub N L →L[ℝ] L2 N :=
  LinearMap.mkContinuous
    { toFun := fun p => (p : Amb N).1
      map_add' := fun p q => rfl
      map_smul' := fun c p => rfl }
    1
    (fun p => by
      simp only [one_mul]
      calc ‖(p : Amb N).1‖ ≤ ‖(p : Amb N)‖ := norm_fst_le _
        _ = ‖p‖ := rfl)

end

end Work.BoseSym
