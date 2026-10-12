import ChallengeDeps
import Mathlib.Tactic.Have
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — the open box, and the corpus trial states inside the test module

`testSub N L` is built from functions whose support lies in the open box
`openBox N L = (0,L)^{3N}`, while the corpus trial spaces `CInfty0Box N L` and
`SymBox N L` require the support to lie in the interior of the closed box
`box N L`.  These agree (`interior_box_eq_openBox`), which lets a corpus trial
state be viewed as an element of `testSub N L` (`boxToTest`, `symBoxToTest`)
and hence its Dirichlet form be evaluated in the energy space `Hsub N L`.
-/

namespace Work.BoseSym

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real ContDiff ENNReal NNReal Convolution

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A coordinate direction of the configuration space, in coordinates. -/
lemma eDir_apply_self (N : ℕ) (i : Fin N) (k : Fin 3) : eDir N i k i k = 1 := by
  rw [eDir, kcDir]
  simp [kcStdBasis, kcE3, EuclideanSpace.single]

lemma eDir_apply_other (N : ℕ) (i : Fin N) (k : Fin 3) {j : Fin N} (hj : j ≠ i)
    (l : Fin 3) : eDir N i k j l = 0 := by
  rw [eDir, kcDir, Function.update_apply, if_neg hj]
  simp

/-- The open box is the interior of the closed box. -/
theorem interior_box_eq_openBox (N : ℕ) (L : ℝ) : interior (box N L) = openBox N L := by
  refine Set.Subset.antisymm ?_ (openBox_subset_interior_box (N := N) L)
  intro x hx
  have hnhds : box N L ∈ 𝓝 x :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset
  intro i k
  constructor
  · by_contra hlt
    push Not at hlt
    have hcont : Continuous (fun t : ℝ => x - t • eDir N i k) := by fun_prop
    have hev0 : box N L ∈ Filter.map (fun t : ℝ => x - t • eDir N i k) (𝓝 (0 : ℝ)) :=
      hcont.continuousAt (by simpa using hnhds)
    have hev : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), x - t • eDir N i k ∈ box N L :=
      (Filter.map_mono nhdsWithin_le_nhds) hev0
    have hevpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ht1, ht2⟩ := (hev.and hevpos).exists
    have hcoord : (x - t • eDir N i k) i k = x i k - t := by
      simp [Pi.sub_apply, Pi.smul_apply, eDir_apply_self, eDir_apply_other, mul_one]
    have h1 : 0 ≤ x i k - t := by
      have := (ht1 i k).1
      rwa [hcoord] at this
    linarith
  · by_contra hlt
    push Not at hlt
    have hcont : Continuous (fun t : ℝ => x + t • eDir N i k) := by fun_prop
    have hev0 : box N L ∈ Filter.map (fun t : ℝ => x + t • eDir N i k) (𝓝 (0 : ℝ)) :=
      hcont.continuousAt (by simpa using hnhds)
    have hev : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), x + t • eDir N i k ∈ box N L :=
      (Filter.map_mono nhdsWithin_le_nhds) hev0
    have hevpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ht1, ht2⟩ := (hev.and hevpos).exists
    have hcoord : (x + t • eDir N i k) i k = x i k + t := by
      simp [Pi.add_apply, Pi.smul_apply, eDir_apply_self, eDir_apply_other, mul_one]
    have h1 : x i k + t ≤ L := by
      have := (ht1 i k).2
      rwa [hcoord] at this
    linarith

/-- A `CInfty0Box` trial state, viewed as an element of the test module
`testSub N L`. -/
def boxToTest (N : ℕ) (L : ℝ) (Ψ : CInfty0Box N L) : testSub N L :=
  ⟨(Ψ : Conf N → ℝ), psi_contDiff Ψ, by
    intro y hy
    rw [← interior_box_eq_openBox N L]
    exact Ψ.support hy⟩

/-- A symmetric (`SymBox`) trial state, viewed as an element of `testSub`. -/
def symBoxToTest (N : ℕ) (L : ℝ) (Ψ : SymBox N L) : testSub N L :=
  boxToTest N L Ψ.toCInfty0Box

@[simp] lemma boxToTest_coe (N : ℕ) (L : ℝ) (Ψ : CInfty0Box N L) :
    (boxToTest N L Ψ : Conf N → ℝ) = (Ψ : Conf N → ℝ) := rfl

@[simp] lemma symBoxToTest_coe (N : ℕ) (L : ℝ) (Ψ : SymBox N L) :
    (symBoxToTest N L Ψ : Conf N → ℝ) = (Ψ : Conf N → ℝ) := rfl

end

end Work.BoseSym
