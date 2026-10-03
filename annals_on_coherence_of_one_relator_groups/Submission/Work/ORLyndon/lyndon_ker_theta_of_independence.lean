import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.LyndonIndependenceDefs
import Submission.Work.ORLyndon.mem_span_of_coset_sums
import Submission.Work.ORLyndon.lyndon_ker_theta_le
import Submission.Work.ORLyndon.cosetFinsetDefs
import Submission.Work.ORLyndon.coset_sums_eq_zero_of_cover
import Submission.Work.ORLyndon.exists_coset_decomposition

/-!
# The annihilator of the Fox derivative vector, from the Cohen--Lyndon independence

Let `X` be a type, `K` a field, `r u : F(X)` with `r = u ^ l` (`1 ≤ l`) and `G = ⟨X | r⟩` the
one-relator group.  This file proves the *hard half* of Lyndon's identity theorem for the
presentation `⟨X | r⟩`,

`LinearMap.ker (lyndonTheta K r) ≤ K[G]·(presentRho r u - 1)`,

from the Cohen--Lyndon independence of the conjugates of the relator
(`Work.ORLyndon.LyndonIndependence`, `LyndonIndependenceDefs.lean`).

## The argument

Write `w = presentRho r u ∈ G`, so that `w ^ l = 1`, and let `a ∈ K[G]` annihilate the Fox
derivative vector `v = (∂r/∂x)_x`, i.e. `a • v = 0`.

* **Transversal decomposition** (`Work.ORLyndon.exists_coset_decomposition`).  There is a finite
  list `g₀, …, g_{n-1}` of elements of `G` lying in pairwise distinct right `⟨w⟩`-cosets and
  covering the support of `a`, such that, with `cᵢ` the sum of the coefficients of `a` over the
  coset `gᵢ⟨w⟩ = cosetFinset w l (gᵢ)`, the difference `a - Σᵢ cᵢ • of (gᵢ)` lies in the left ideal
  `K[G]·(w - 1)`.

* Since `K[G]·(w-1) ≤ ker θ` (`Work.ORLyndon.lyndon_ker_theta_le`), the element
  `Σᵢ cᵢ • of (gᵢ)` also annihilates `v`, i.e. `Σᵢ cᵢ • (of (gᵢ) • v) = 0`.  The `gᵢ` lie in
  pairwise distinct `⟨w⟩`-cosets, so `Work.ORLyndon.LyndonIndependence` gives `cᵢ = 0` for all `i`.

* Hence the coefficient sum of `a` over every right `⟨w⟩`-coset vanishes
  (`Work.ORLyndon.coset_sums_eq_zero_of_cover`), and the coset-sum criterion
  `Work.ORLyndon.mem_span_of_coset_sums` yields `a ∈ K[G]·(w - 1)`.

## Main results

* `Work.ORLyndon.lyndon_ker_theta_of_independence`
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-- The coset finset of the root `presentRho r u` is the abstract coset finset of
`Work.ORLyndon.cosetFinset`. -/
theorem uCoset_eq_cosetFinset {X : Type*} [DecidableEq X] (r u : FreeGroup X) (l : ℕ)
    [DecidableEq (OneRelatorGroup r)] (g : OneRelatorGroup r) :
    uCoset r u l g = cosetFinset (presentRho r u) l g := by
  ext h
  rw [mem_uCoset, mem_cosetFinset]

theorem lyndon_ker_theta_of_independence {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l) (hpow : r = u ^ l)
    (hind : Work.ORLyndon.LyndonIndependence K r u) :
    LinearMap.ker (Work.ORLyndon.lyndonTheta K r) ≤
      Ideal.span {((MonoidAlgebra.of K (Work.ORLyndon.OneRelatorGroup r))
        (Work.ORLyndon.presentRho r u)) - 1} := by
  intro a ha
  classical
  set w : OneRelatorGroup r := presentRho r u with hw
  have hwl : w ^ l = 1 := by rw [hw, ← map_pow, hpow, presentRho_relator]
  obtain ⟨n, g, c, hdist, hcov, hc, hdec⟩ := exists_coset_decomposition w l hpos hwl a
  -- the left ideal `K[G](w-1)` is contained in `ker θ`
  have hle : Ideal.span ({MonoidAlgebra.of K (OneRelatorGroup r) w - 1} :
      Set (MonoidAlgebra K (OneRelatorGroup r))) ≤ LinearMap.ker (lyndonTheta K r) := by
    rw [hw]
    exact lyndon_ker_theta_le r u l hpow
  -- hence the coset-representative part of `a` also lies in `ker θ`
  have hb_ker : (∑ i, c i • MonoidAlgebra.of K (OneRelatorGroup r) (g i)) ∈
      LinearMap.ker (lyndonTheta K r) := by
    have h1 : a - ∑ i, c i • MonoidAlgebra.of K (OneRelatorGroup r) (g i) ∈
        LinearMap.ker (lyndonTheta K r) := hle hdec
    have h2 := Submodule.sub_mem (LinearMap.ker (lyndonTheta K r)) ha h1
    simpa using h2
  -- expanding gives the linear relation to which the independence hypothesis applies
  have hsum0 : (∑ i : Fin n, c i •
      ((MonoidAlgebra.of K (OneRelatorGroup r)) (g i) • relatorVec K r)) = 0 := by
    have h0 := LinearMap.mem_ker.mp hb_ker
    rw [lyndonTheta_apply] at h0
    rw [← h0, Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_assoc]
  have hcz : ∀ i, c i = 0 := fun i =>
    hind (Fin n) g c (fun i j hij m => hdist i j hij m) hsum0 i
  have hzero : ∀ i, (∑ h ∈ cosetFinset (presentRho r u) l (g i), a.coeff h) = 0 :=
    fun i => (hc i).symm.trans (hcz i)
  -- all coset sums of `a` vanish
  have hcs : ∀ q : OneRelatorGroup r, (uCoset r u l q).sum (fun hh => a.coeff hh) = 0 := by
    intro q
    rw [uCoset_eq_cosetFinset]
    exact coset_sums_eq_zero_of_cover w l hpos hwl a g hcov hzero q
  exact mem_span_of_coset_sums r u l hpos hpow a hcs

end Work.ORLyndon
