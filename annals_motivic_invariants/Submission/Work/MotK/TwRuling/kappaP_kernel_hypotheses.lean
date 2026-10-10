import Mathlib
import Submission.Work.MotK.TwRuling.TwSixAssemblyDefs
import Submission.Work.MotK.TGen.TwCoordGKleinTw
import Submission.Work.MotK.TGen.TwBridge
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.TwRuling.SdWNdeg

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

/-- The hypothesis bundle of `Work.MotK.TwRuling.sexticTw_notMem_kernel` for the `L(5·O)`-adapted
basis `kappaP K D h` (`κ'_i = w^{-i}·κ_i = κ_0 · twCoordG K D h i`).  ⚠ `twCoordG` itself does NOT
satisfy these hypotheses (`w^{-i}κ_i/κ_0 ∉ L(5·O)`), which is why `kappaP` is used.

* conjunct 1: `kleinCoord D L i = Σ_m coord i m • kleinBas D L m` and `kleinBas = sdBas`, so the
  `KbG K`-multiple `w^{-i}·κ_i` lies in `span (sdBas …)`;
* conjunct 2: `D.Good.spans` at `L = KbG K` gives `sdBas m = Σ_i e_{mi}·κ_i = Σ_i (e_{mi} w^i)·κ'_i`;
* conjunct 3: `TwCoordGKleinTw` gives `kleinTw a b h (twCoordG) = 0`, `kleinTwP_homog` (degree 2) and
  `κ' = κ_0 · twCoordG` give the same for `κ'` (using `D.Good.coord0_ne`). -/
theorem kappaP_kernel_hypotheses (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) (hh : h ≠ 0) :
    (∀ i : Fin 5, Work.MotK.TwRuling.kappaP K D h i ∈ Submodule.span (Work.MotK.KbG K)
        (Set.range (Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotK.KbG K)))))
      ∧ (∀ m : Fin 5, Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotK.KbG K)) m ∈
          Submodule.span (Work.MotK.KbG K) (Set.range (Work.MotK.TwRuling.kappaP K D h)))
      ∧ (∀ k : Fin 5, Work.MotK.kleinTwP (algebraMap K (Work.MotK.OmG K D) D.a)
          (algebraMap K (Work.MotK.OmG K D) D.b) (algebraMap K (Work.MotK.OmG K D) h)
          (Work.MotK.TwRuling.kappaP K D h) k = 0) := by
  -- The two bases agree: `sdBas E` is `kleinBas D (KbG K)`.
  have hsd : ∀ m : Fin 5, Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotK.KbG K)) m =
      Work.MotV.kleinBas D (Work.MotK.KbG K) m := by
    intro m; fin_cases m <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · -- conjunct 1: `kleinCoord i` is the `coord`-linear combination of the basis, hence in the span.
    intro i
    have hκmem : Work.MotV.kleinCoord D (Work.MotK.KbG K) i ∈
        Submodule.span (Work.MotK.KbG K)
          (Set.range (Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotK.KbG K)))) := by
      rw [Work.MotV.kleinCoord_eq_sum]
      refine Submodule.sum_mem _ (fun m _ => ?_)
      rw [← hsd m, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self m))
    have hkp : Work.MotK.TwRuling.kappaP K D h i =
        ((Work.MotK.root5G K h)⁻¹) ^ (i : ℕ) •
          Work.MotV.kleinCoord D (Work.MotK.KbG K) i := by
      simp only [Work.MotK.TwRuling.kappaP, Algebra.smul_def, map_pow, map_inv₀]
    rw [hkp]
    exact Submodule.smul_mem _ _ hκmem
  · -- conjunct 2: `D.Good.spans` writes the basis in the `kleinCoord` and `κ_i = w^i · κ'_i`.
    intro m
    obtain ⟨e, he⟩ := hD.spans
    rw [hsd m, he (Work.MotK.KbG K) m]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have hκ : Work.MotV.kleinCoord D (Work.MotK.KbG K) i =
        (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h)) ^ (i:ℕ) *
          Work.MotK.TwRuling.kappaP K D h i := by
      have hw : algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h) ≠ 0 :=
        Work.MotK.TGen.wG_ne_zero D hh
      simp only [Work.MotK.TwRuling.kappaP]
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hw, one_pow, one_mul]
    rw [hκ, ← mul_assoc]
    have hcomb : algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D)
          (algebraMap K (Work.MotK.KbG K) (e m i)) *
          (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h)) ^ (i:ℕ) =
        algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D)
          (algebraMap K (Work.MotK.KbG K) (e m i) * (Work.MotK.root5G K h) ^ (i:ℕ)) := by
      rw [map_mul, map_pow]
    rw [hcomb, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · -- conjunct 3: `κ' = κ_0 · twCoordG` and `kleinTwP` is homogeneous of degree two.
    have hκ0 : Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 ≠ 0 := hD.coord0_ne (Work.MotK.KbG K)
    have hsplit : Work.MotK.TwRuling.kappaP K D h =
        fun i => Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 * Work.MotK.twCoordG K D h i := by
      funext i
      simp only [Work.MotK.TwRuling.kappaP, Work.MotK.twCoordG]
      rw [← mul_div_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hκ0]
    intro k
    have hTw : Work.MotK.kleinTwP (algebraMap K (Work.MotK.OmG K D) D.a)
        (algebraMap K (Work.MotK.OmG K D) D.b) (algebraMap K (Work.MotK.OmG K D) h)
        (Work.MotK.twCoordG K D h) k = 0 := by
      rw [← Work.MotK.TGen.kleinTw_eq_kleinTwP]
      exact Work.MotK.TGen.TwCoordGKleinTw D hD h hh k
    rw [hsplit]
    rw [congrFun (Work.MotK.kleinTwP_homog (algebraMap K (Work.MotK.OmG K D) D.a)
      (algebraMap K (Work.MotK.OmG K D) D.b) (algebraMap K (Work.MotK.OmG K D) h)
      (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) (Work.MotK.twCoordG K D h)) k]
    rw [hTw, mul_zero]

end Work.MotK.TwRuling
