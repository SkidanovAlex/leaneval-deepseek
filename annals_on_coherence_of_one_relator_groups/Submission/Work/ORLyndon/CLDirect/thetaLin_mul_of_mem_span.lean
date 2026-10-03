import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.thetaLin_of
import Submission.Work.ORLyndon.CLDirect.presentSec_inv_mul_mem
import Submission.Work.ORLyndon.CLDirect.thetaFun_mul_mem

namespace Work.ORLyndon.CLDirect

/-- The key step of the Fox-kernel lemma (hardest C-unit). Sketch: prove the stronger `Ψ z := ∀ a, Θ(a * z * of g) = Θ(a * z)` by `MonoidAlgebra.induction_on` on `a` (the `add`/`smul` cases are linear, the `a = of f` case being the computation below), then obtain the `a = 1` case, then apply `Submodule.span_induction` on `hz`. (Do NOT try `span_induction` directly on the `a = 1` property: `{z | Θ (z * of g) = Θ z}` is not closed under algebra-scaling.) For the generator `z = single m 1 − 1` with `m ∈ ker (presentRho r)`, hence `m ∈ normalClosure {r}` by `Work.ORLyndon.mem_normalClosure_of_mem_ker`: `Θ(of f * (of m − 1) * of g) = thetaFun (f*m*g) − thetaFun (f*g)`; write `f*m*g = (f*g) * (g⁻¹*m*g)` and apply `thetaFun_mul_mem`; `hconj g⁻¹ m` gives `φ (g⁻¹ m g) = of (ρ g⁻¹) φ m` (rewrite `g⁻¹⁻¹ = g`), so the difference is `of (ρ f) φ m`; likewise `Θ(of f * (of m − 1)) = thetaFun (f*m) − thetaFun f = of (ρ f) φ m` by `thetaFun_mul_mem`. -/
theorem thetaLin_mul_of_mem_span {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r : FreeGroup X) (φ : FreeGroup X → MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r))
    (hmul : ∀ n n', n ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) →
      n' ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) → φ (n * n') = φ n + φ n')
    (hconj : ∀ f n, n ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) →
      φ (f * n * f⁻¹) = MonoidAlgebra.of K _ (Work.ORLyndon.presentRho r f) * φ n)
    {z : MonoidAlgebra K (FreeGroup X)}
    (hz : z ∈ Submodule.span (MonoidAlgebra K (FreeGroup X))
        (Set.range fun m : MonoidHom.ker (Work.ORLyndon.presentRho r) =>
          MonoidAlgebra.single (m : FreeGroup X) (1 : K) - 1))
    (g : FreeGroup X) :
    Work.ORLyndon.CLDirect.thetaLin (K := K) r φ (z * MonoidAlgebra.of K _ g) =
      Work.ORLyndon.CLDirect.thetaLin (K := K) r φ z := by
  classical
  -- We prove the stronger statement `Ψ w := ∀ a, Θ (a * w * of g) = Θ (a * w)` for every `w` in
  -- the span, by `Submodule.span_induction`.  The generator case is handled by
  -- `MonoidAlgebra.induction_on` on `a`.
  have key : ∀ (w : MonoidAlgebra K (FreeGroup X)),
      w ∈ Submodule.span (MonoidAlgebra K (FreeGroup X))
        (Set.range fun m : MonoidHom.ker (Work.ORLyndon.presentRho r) =>
          MonoidAlgebra.single (m : FreeGroup X) (1 : K) - 1) →
      ∀ a : MonoidAlgebra K (FreeGroup X),
        Work.ORLyndon.CLDirect.thetaLin (K := K) r φ (a * w * MonoidAlgebra.of K _ g) =
        Work.ORLyndon.CLDirect.thetaLin (K := K) r φ (a * w) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem v hv =>
        rcases hv with ⟨m, rfl⟩
        have hm : (m : FreeGroup X) ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) :=
          Work.ORLyndon.mem_normalClosure_of_mem_ker r m
        intro a
        refine MonoidAlgebra.induction_on (motive := fun u =>
            Work.ORLyndon.CLDirect.thetaLin (K := K) r φ
              (u * (MonoidAlgebra.single (m : FreeGroup X) (1 : K) - 1) * MonoidAlgebra.of K _ g) =
            Work.ORLyndon.CLDirect.thetaLin (K := K) r φ
              (u * (MonoidAlgebra.single (m : FreeGroup X) (1 : K) - 1))) a ?_ ?_ ?_
        · intro f
          have hz1 : MonoidAlgebra.of K (FreeGroup X) f *
                (MonoidAlgebra.single (m : FreeGroup X) (1:K) - 1)
              = MonoidAlgebra.of K (FreeGroup X) (f * (m : FreeGroup X)) -
                MonoidAlgebra.of K (FreeGroup X) f := by
            rw [← MonoidAlgebra.of_apply K (FreeGroup X) (m : FreeGroup X), mul_sub, mul_one,
              ← map_mul]
          have e1 : Work.ORLyndon.CLDirect.thetaLin (K := K) r φ
                (MonoidAlgebra.of K (FreeGroup X) f *
                  (MonoidAlgebra.single (m : FreeGroup X) (1:K) - 1))
              = MonoidAlgebra.of K _ (Work.ORLyndon.presentRho r f) * φ (m : FreeGroup X) := by
            rw [hz1, map_sub, Work.ORLyndon.CLDirect.thetaLin_of,
              Work.ORLyndon.CLDirect.thetaLin_of,
              Work.ORLyndon.CLDirect.thetaFun_mul_mem r φ hmul f (m : FreeGroup X) hm]
            rw [add_sub_cancel_left]
          have hmem : g⁻¹ * (m : FreeGroup X) * g ∈
              Subgroup.normalClosure ({r} : Set (FreeGroup X)) := by
            have h := Subgroup.Normal.conj_mem
              (Subgroup.normalClosure_normal (s := ({r} : Set (FreeGroup X))))
              (m : FreeGroup X) hm g⁻¹
            simpa using h
          have e2 : Work.ORLyndon.CLDirect.thetaLin (K := K) r φ
                (MonoidAlgebra.of K (FreeGroup X) f *
                  (MonoidAlgebra.single (m : FreeGroup X) (1:K) - 1) * MonoidAlgebra.of K _ g)
              = MonoidAlgebra.of K _ (Work.ORLyndon.presentRho r f) * φ (m : FreeGroup X) := by
            have hz2 : MonoidAlgebra.of K (FreeGroup X) f *
                  (MonoidAlgebra.single (m : FreeGroup X) (1:K) - 1) * MonoidAlgebra.of K _ g
                = MonoidAlgebra.of K (FreeGroup X) (f * (m : FreeGroup X) * g) -
                  MonoidAlgebra.of K (FreeGroup X) (f * g) := by
              rw [hz1, sub_mul, ← map_mul, ← map_mul]
            rw [hz2, map_sub, Work.ORLyndon.CLDirect.thetaLin_of,
              Work.ORLyndon.CLDirect.thetaLin_of]
            rw [show f * (m : FreeGroup X) * g = (f * g) * (g⁻¹ * (m : FreeGroup X) * g) from by
              group]
            rw [Work.ORLyndon.CLDirect.thetaFun_mul_mem r φ hmul (f * g)
              (g⁻¹ * (m : FreeGroup X) * g) hmem]
            have hc : φ (g⁻¹ * (m : FreeGroup X) * g)
                = MonoidAlgebra.of K _ (Work.ORLyndon.presentRho r g⁻¹) * φ (m : FreeGroup X) := by
              simpa using hconj g⁻¹ (m : FreeGroup X) hm
            rw [hc, add_sub_cancel_left]
            have hρ : Work.ORLyndon.presentRho r (f * g) * Work.ORLyndon.presentRho r g⁻¹ =
                Work.ORLyndon.presentRho r f := by
              rw [← map_mul, show f * g * g⁻¹ = f from by group]
            have hof : MonoidAlgebra.of K _ (Work.ORLyndon.presentRho r (f * g)) *
                MonoidAlgebra.of K _ (Work.ORLyndon.presentRho r g⁻¹)
                = MonoidAlgebra.of K _ (Work.ORLyndon.presentRho r f) := by
              rw [← map_mul, hρ]
            rw [← mul_assoc, hof]
          exact e2.trans e1.symm
        · intro x y ihx ihy
          rw [add_mul, add_mul, map_add, map_add, ihx, ihy]
        · intro c x ih
          rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, map_smul, map_smul, ih]
    | zero => intro a; simp
    | add x y hx hy ihx ihy => intro a; rw [mul_add, add_mul, map_add, map_add, ihx a, ihy a]
    | smul c x hx ih => intro a; simpa [smul_eq_mul, mul_assoc] using ih (a * c)
  simpa using key z hz 1

end Work.ORLyndon.CLDirect
