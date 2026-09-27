import Mathlib
import Submission.Work.KT.EG.kappa_linearise_defs
import Submission.Work.KT.EG.kappa_linearise_e
import Submission.Work.KT.EG.kappaRedDefs

namespace Work.KT.EG

open Matrix

noncomputable section

/-- **Hatcher's linearisation of polynomial clutching functions** (Prop. 2.6 of Hatcher, *Vector
Bundles and K-Theory*, §2.1). A polynomial clutching function `q` over `C(X, ℂ)` is replaced, at the
price of adding identity blocks, by a *linear* one: there is a linear unit
`D = z • pullMat a + pullMat b` (of some size `m'`) with `redK X m u = redK X m' D`, where `u` is
the unit whose values are `q.map (polyMap X)`.

Route (Hatcher). Let `N` be the degree bound and `q(z) = a_N z^N + … + a_0`. Build the
`(N+1) m × (N+1) m` block matrices `A = [[1, -z, 0, …], [0, 1, -z, …], …, [a_N, a_{N-1}, …, a_0]]`
(linear in `z`) and `B = diag (1_{Nm}, q)`. `A` is carried to `B` by the elementary column
operations `col_{i+1} ← col_{i+1} + z col_i` followed by elementary row operations making the last
row zero except for the final `q`; each operation is an explicit unipotent (hence invertible)
matrix depending continuously on a parameter `t ∈ [0,1]`, so the composite is a *unit* `W` of
matrices over `C((X × I) × S¹, ℂ)` with slices `A` and `B`; `Work.KT.Fund.kappa_homotopic` gives
`κ A = κ B`. Since `B` is block diagonal, `Work.KT.Fund.kappa_add` (with `Work.KT.Fund.kappa_one`)
gives `κ B = cls (Mat.one _ (N m)) + κ q`, and the identity
`cls (Mat.one _ (N*m)) + cls (Mat.one _ m) = cls (Mat.one _ ((N+1)*m))` (block sums,
`Work.KT.cls_sum`) converts this into `redK X m u = redK X ((N+1)*m) A`. Take `m' = (N+1)*m` and
`a`, `b` the constant coefficients of `A = z • pullMat a + pullMat b`.

Do not use any result whose file still contains a `sorry` (in particular not `Fund.kappa_mul`,
`Fund.kappa_bott`, `Fund.kappa_hopf`, `EG.kappa_lin`); all the ingredients above are sorry-free. -/
theorem kappa_linearise (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (m : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (Work.KT.EG.polyMap X)) :
    ∃ (m' : ℕ) (a b : Matrix (Fin m') (Fin m') C(X, ℂ))
      (D : (Matrix (Fin m') (Fin m') C(X × Sph ℂ, ℂ))ˣ),
      (D : Matrix (Fin m') (Fin m') C(X × Sph ℂ, ℂ))
        = (Work.KT.zUnit X : C(X × Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X a
          + Work.KT.Fund.pullMat X b ∧
      Work.KT.EG.redK X m u = Work.KT.EG.redK X m' D := by
  have hpm : polyMapA X = Work.KT.EG.polyMap X := rfl
  have hka : ∀ (n : ℕ) (w : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ),
      redKa X n w = Work.KT.EG.redK X n w := fun n w => rfl
  have hu' : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X) := by
    rw [hu, hpm]
  obtain ⟨m', a, b, D, hD, hred⟩ := kappa_linearise_aux X m q u hu'
  refine ⟨m', a, b, D, hD, ?_⟩
  rw [← hka m u, ← hka m' D]
  exact hred

end

end Work.KT.EG
