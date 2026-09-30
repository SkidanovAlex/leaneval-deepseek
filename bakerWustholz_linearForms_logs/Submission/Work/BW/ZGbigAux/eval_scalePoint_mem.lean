import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.bwScale
import Submission.Work.BW.eval_scale_homPiece

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.ZGbigAux

/-- If a multihomogeneous ideal `𝔓` vanishes at the cone point `x`, then it vanishes at
every torus-scaled point `(v ↦ st v.1 * x v)`.

Indeed, `𝔓` being multihomogeneous, every `G ∈ 𝔓` is the sum of its multihomogeneous
components, each of which lies in `𝔓` and hence vanishes at `x`; and each component is an
eigenvector of the scaling endomorphism, so it also vanishes at the scaled point
(`Work.BW.eval_scale_homPiece`). -/
theorem eval_scalePoint_mem {N : ℕ} (𝔓 : Ideal (Work.BW.MR N)) (hH : Work.BW.MultiHom N 𝔓)
    (st : Fin (N + 1) → ℂ) (x : Fin (N + 1) × Fin 2 → ℂ)
    (hx : ∀ G ∈ 𝔓, MvPolynomial.eval x G = 0) :
    ∀ G ∈ 𝔓,
      MvPolynomial.eval (fun v : Fin (N + 1) × Fin 2 => st v.1 * x v) G = 0 := by
  classical
  intro G hG
  have hfin : Function.HasFiniteSupport
      (fun m : Fin (N + 1) →₀ ℕ =>
        MvPolynomial.weightedHomogeneousComponent (Work.BW.mdeg N) m G) :=
    MvPolynomial.weightedHomogeneousComponent_finsupp G
  have hdecomp : G = ∑ m ∈ hfin.toFinset,
      MvPolynomial.weightedHomogeneousComponent (Work.BW.mdeg N) m G := by
    have h1 : (∑ᶠ m, MvPolynomial.weightedHomogeneousComponent (Work.BW.mdeg N) m G) = G :=
      MvPolynomial.sum_weightedHomogeneousComponent (Work.BW.mdeg N) G
    rw [finsum_eq_sum _ hfin] at h1
    exact h1.symm
  rw [hdecomp, map_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  have hc : MvPolynomial.weightedHomogeneousComponent (Work.BW.mdeg N) m G ∈ 𝔓 := hH G hG m
  have hmem : MvPolynomial.weightedHomogeneousComponent (Work.BW.mdeg N) m G ∈
      Work.BW.homPiece N m :=
    MvPolynomial.weightedHomogeneousComponent_mem (Work.BW.mdeg N) G m
  rw [Work.BW.eval_scale_homPiece m _ hmem st x, hx _ hc, mul_zero]

end Work.BW.ZGbigAux
