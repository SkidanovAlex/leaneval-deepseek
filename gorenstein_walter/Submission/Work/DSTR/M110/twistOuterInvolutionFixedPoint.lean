import Mathlib
import Submission.Work.DSTR.M110.Defs
import Submission.Work.DSTR.M110.Galois.decomposition
import Submission.Work.DSTR.M110.SplitCase.GaloisPart
import Submission.Work.DSTR.M110.pglInvolutionFixedPoints
import Submission.Work.DSTR.M110.semilinearFixedPoint
import Submission.Work.DSTR.M110.normSqrtOfMatrixInvolution

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110

/-- An involution of `PΓL(2,q)` (`q = p^k`, `p` odd, `q ≥ 5`) which is not in `PGL(2,q)` has a
fixed point on the projective line.  Indeed its class modulo `PGL(2,q)` is a field involution `σ`,
`t = c·σ` with `c ∈ PGL`; writing `c = pglHom (mk A)` one has `A·σ(A) = λ·1`, and the associated
`σ`-semilinear map of `F²` is a scalar twist of an involution (because `λ` is a norm `μ·σ(μ)` for
`σ`), so it has an eigenline — a fixed point of `t`. -/
theorem twistOuterInvolutionFixedPoint (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)] (t : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))
    (htG : t ∈ Work.AUTL2.pgammaL (GaloisField p k))
    (ht2 : orderOf t = 2) (htnpgl : t ∉ Work.AUTL2.pglImage (GaloisField p k)) :
    ∃ y : Work.AUTL2.P1 (GaloisField p k), t y = y := by
  classical
  let F := GaloisField p k
  let x : ↥(Work.AUTL2.pgammaL F) := ⟨t, htG⟩
  have hordx : orderOf x = 2 := by
    rw [← Subgroup.orderOf_coe x]
    exact ht2
  have hxx : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hordx, pow_two] at h
    exact h
  have ht2' : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h
    exact h
  let σ : F ≃+* F := Work.DSTR.M110.SplitAux.galPart F x
  have hσmul : σ * σ = 1 := by
    have h := Work.DSTR.M110.SplitAux.galPart_mul F x x
    rw [hxx, Work.DSTR.M110.SplitAux.galPart_one] at h
    exact h.symm
  have hσ2 : ∀ a : F, σ (σ a) = a := by
    intro a
    have h := congrFun (congrArg DFunLike.coe hσmul) a
    simpa using h
  have hσ1 : σ ≠ 1 := by
    intro h
    exact htnpgl ((Work.DSTR.M110.SplitAux.galPart_eq_one_iff F x).mp h)
  obtain ⟨c, hc, hspec⟩ := Work.DSTR.M110.SplitAux.galPart_spec F x
  have hspec_t : t = c * Work.AUTL2.galHom F σ := hspec
  obtain ⟨g0, hg0⟩ := hc
  obtain ⟨A, hA0⟩ := Matrix.ProjGenLinGroup.mk_surjective g0
  have hc'A : c = Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk A) := by
    rw [← hg0, ← hA0]
  have hconj :
      Work.AUTL2.galHom F σ * Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk A) *
          (Work.AUTL2.galHom F σ)⁻¹ =
        Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.map (σ : F →+* F) A)) :=
    Work.AUTL2.Galois.fieldAut_conj_pgl F σ A
  have hgg : Work.AUTL2.galHom F σ * Work.AUTL2.galHom F σ = 1 := by
    rw [← map_mul, hσmul, map_one]
  have hgroup :
      (Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk A) * Work.AUTL2.galHom F σ) *
          (Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk A) * Work.AUTL2.galHom F σ)
        = Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk A) *
            (Work.AUTL2.galHom F σ * Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk A) *
              (Work.AUTL2.galHom F σ)⁻¹) *
            (Work.AUTL2.galHom F σ * Work.AUTL2.galHom F σ) := by
    group
  have hkey1 : t * t = Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk
      (A * Matrix.GeneralLinearGroup.map (σ : F →+* F) A)) := by
    rw [hspec_t, hc'A, hgroup, hconj, hgg, mul_one, ← map_mul, ← map_mul]
  have hone : Work.AUTL2.pglHom F (Matrix.ProjGenLinGroup.mk
      (A * Matrix.GeneralLinearGroup.map (σ : F →+* F) A)) = 1 := by
    rw [← hkey1, ht2']
  have hmk1 : Matrix.ProjGenLinGroup.mk (A * Matrix.GeneralLinearGroup.map (σ : F →+* F) A) = 1 := by
    apply Work.AUTL2.Aut.pglHomInjective F
    rw [hone, map_one]
  have hcenter : (A * Matrix.GeneralLinearGroup.map (σ : F →+* F) A) ∈
      Subgroup.center (GL (Fin 2) F) :=
    Matrix.ProjGenLinGroup.mk_eq_one.mp hmk1
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at hcenter
  obtain ⟨u, hu⟩ := hcenter
  have hAmat : (A : Matrix (Fin 2) (Fin 2) F) *
      (Matrix.GeneralLinearGroup.map (σ : F →+* F) A : Matrix (Fin 2) (Fin 2) F) = u • 1 := by
    rw [smul_one_eq_scalar u, hu, Matrix.GeneralLinearGroup.coe_mul]
  have hμ : ∃ μ : F, μ * σ μ = u :=
    normSqrtOfMatrixInvolution p k σ hσ2 hσ1 A u hAmat
  obtain ⟨y, hy⟩ := semilinearFixedPoint σ hσ2 A u hAmat hμ
  exact ⟨y, by rw [hspec_t, hc'A]; exact hy⟩

end Work.DSTR.M110
