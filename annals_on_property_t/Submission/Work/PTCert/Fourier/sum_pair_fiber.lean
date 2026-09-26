import Mathlib

namespace Work.PTCert.Fourier

/-- **Fiber decomposition of a sum along an idempotent.**
If `f : ι → ι` is idempotent (`f (f x) = f x`), then summing over `ι` can be done by
first summing over the fixed points `xb` of `f` and then over the fiber
`{x | f x = xb.1}` of `x ↦ ⟨f x, hf x⟩` above `xb`. -/
theorem sum_fiber_decomp {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ι)
    (hf : ∀ x, f (f x) = f x) (F : ι → ℝ) :
    (∑ x : ι, F x)
      = ∑ xb : {x : ι // f x = x}, ∑ x : {x : ι // f x = xb.1}, F x.1 := by
  rw [← Finset.sum_fiberwise Finset.univ (fun x => (⟨f x, hf x⟩ : {x : ι // f x = x})) F]
  apply Finset.sum_congr rfl
  intro xb _
  have hfilt : Finset.univ.filter (fun x : ι => (⟨f x, hf x⟩ : {x // f x = x}) = xb)
      = Finset.univ.filter (fun x : ι => f x = xb.1) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hsub : (∑ x ∈ Finset.univ.filter (fun x : ι => f x = xb.1), F x)
      = ∑ x : {x : ι // f x = xb.1}, F x.1 :=
    Finset.sum_subtype (Finset.univ.filter (fun x : ι => f x = xb.1)) (fun x => by simp) F
  rw [hfilt, hsub]

theorem sum_pair_fiber {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ι)
    (hf : ∀ x, f (f x) = f x) (A B : ι → ℝ) (K : ι → ι → ℝ) :
    (∑ x : ι, ∑ y : ι, A x * B y * K (f x) (f y))
      = ∑ xb : {x : ι // f x = x}, ∑ yb : {x : ι // f x = x},
          (∑ x : {x : ι // f x = xb.1}, A x.1) * (∑ y : {x : ι // f x = yb.1}, B y.1)
            * K xb.1 yb.1 := by
  -- Step 1: decompose the inner sum over `y` along the fibers of `f`.
  have step1 : (∑ x : ι, ∑ y : ι, A x * B y * K (f x) (f y))
      = ∑ x : ι, ∑ yb : {x : ι // f x = x}, ∑ y : {x : ι // f x = yb.1},
          A x * B y.1 * K (f x) (f y.1) := by
    apply Finset.sum_congr rfl; intro x _
    exact sum_fiber_decomp f hf (fun y => A x * B y * K (f x) (f y))
  -- Step 2: on the fiber above `yb`, `f y = yb.1`.
  have step2 : (∑ x : ι, ∑ yb : {x : ι // f x = x}, ∑ y : {x : ι // f x = yb.1},
          A x * B y.1 * K (f x) (f y.1))
      = ∑ x : ι, ∑ yb : {x : ι // f x = x}, ∑ y : {x : ι // f x = yb.1},
          A x * B y.1 * K (f x) yb.1 := by
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro yb _
    apply Finset.sum_congr rfl; intro y _
    rw [y.2]
  -- Step 3: decompose the outer sum over `x` along the fibers of `f`.
  have step3 : (∑ x : ι, ∑ yb : {x : ι // f x = x}, ∑ y : {x : ι // f x = yb.1},
          A x * B y.1 * K (f x) yb.1)
      = ∑ xb : {x : ι // f x = x}, ∑ x : {x : ι // f x = xb.1},
          ∑ yb : {x : ι // f x = x}, ∑ y : {x : ι // f x = yb.1},
            A x.1 * B y.1 * K (f x.1) yb.1 := by
    exact sum_fiber_decomp f hf
      (fun x => ∑ yb : {x : ι // f x = x}, ∑ y : {x : ι // f x = yb.1},
            A x * B y.1 * K (f x) yb.1)
  -- Step 4: on the fiber above `xb`, `f x = xb.1`.
  have step4 : (∑ xb : {x : ι // f x = x}, ∑ x : {x : ι // f x = xb.1},
          ∑ yb : {x : ι // f x = x}, ∑ y : {x : ι // f x = yb.1},
            A x.1 * B y.1 * K (f x.1) yb.1)
      = ∑ xb : {x : ι // f x = x}, ∑ x : {x : ι // f x = xb.1},
          ∑ yb : {x : ι // f x = x}, ∑ y : {x : ι // f x = yb.1},
            A x.1 * B y.1 * K xb.1 yb.1 := by
    apply Finset.sum_congr rfl; intro xb _
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro yb _
    apply Finset.sum_congr rfl; intro y _
    rw [x.2]
  -- Step 5: swap the two inner sums.
  have step5 : (∑ xb : {x : ι // f x = x}, ∑ x : {x : ι // f x = xb.1},
          ∑ yb : {x : ι // f x = x}, ∑ y : {x : ι // f x = yb.1},
            A x.1 * B y.1 * K xb.1 yb.1)
      = ∑ xb : {x : ι // f x = x}, ∑ yb : {x : ι // f x = x},
          ∑ x : {x : ι // f x = xb.1}, ∑ y : {x : ι // f x = yb.1},
            A x.1 * B y.1 * K xb.1 yb.1 := by
    apply Finset.sum_congr rfl; intro xb _
    rw [Finset.sum_comm]
  -- Step 6: factor the sums.
  have step6 : (∑ xb : {x : ι // f x = x}, ∑ yb : {x : ι // f x = x},
          ∑ x : {x : ι // f x = xb.1}, ∑ y : {x : ι // f x = yb.1},
            A x.1 * B y.1 * K xb.1 yb.1)
      = ∑ xb : {x : ι // f x = x}, ∑ yb : {x : ι // f x = x},
          (∑ x : {x : ι // f x = xb.1}, A x.1) * (∑ y : {x : ι // f x = yb.1}, B y.1)
            * K xb.1 yb.1 := by
    apply Finset.sum_congr rfl; intro xb _
    apply Finset.sum_congr rfl; intro yb _
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_mul]
  rw [step1, step2, step3, step4, step5, step6]

end Work.PTCert.Fourier
