import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.FTS.EllipticEst.RPFresh.DivSinOpen.LopLeibnizPoint
import Submission.Work.FTS.EllipticEst.remov.Baux.DthIter_M_recursion

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The recursion of the iterated angular operator `Lop`

`Work.Spaces.Lop u θ = sin(2θ) · u'(θ)` is the action of `D_θ = sin(2θ) ∂_θ` on functions of
`θ` alone, and it is a derivation for the pointwise product.  If `f`, `A`, `g` solve the
inhomogeneous linear equation `Lop f = A·f - g` on `Ioo 0 (π/2)`, then the iterates of `Lop`
satisfy the binomial (Leibniz) expansion

`Lop^[i+1] f = ∑_{j ≤ i} C(i,j) · (Lop^[i-j] A) · (Lop^[j] f) - Lop^[i] g`.

The proof combines the pointwise Leibniz rule `LopLeibnizPoint` (finite-order smoothness at a
point) with the pointwise calculus of `Lop`-iterates (`Lop_iter_congr_at`, `Lop_iter_sub_at`,
in `Work.FTS.EllipticEst.remov.Baux`) and the reflection of the binomial index range
(`sum_range_choose_reflect'` below).
-/

namespace Work.FTS.PhiStar

open scoped Topology
open Filter

/-- Reflection of the binomial convolution sum over `range (k+1)`: the index map `j ↦ k - j`
permutes the range `{0, …, k}` and `k.choose (k-j) = k.choose j`, so summing
`C(k,j) · X j · Y (k-j)` is the same as summing `C(k,j) · X (k-j) · Y j`. -/
theorem sum_range_choose_reflect' (k : ℕ) (X Y : ℕ → ℝ) :
    (∑ a ∈ Finset.range (k + 1), (k.choose a : ℝ) * (X a * Y (k - a)))
      = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (X (k - j) * Y j) := by
  rw [← Finset.sum_range_reflect (fun j => (k.choose j : ℝ) * (X (k - j) * Y j)) (k + 1)]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [Nat.add_sub_cancel, Nat.sub_sub_self ha', ← Nat.choose_symm ha']

theorem LopIterRecursion {f A g : ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n f (Set.Ioo 0 (Real.pi / 2)))
    (hA : ∀ n : ℕ, ContDiffOn ℝ n A (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n g (Set.Ioo 0 (Real.pi / 2)))
    (hrec : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.Spaces.Lop f θ = A θ * f θ - g θ) :
    ∀ i : ℕ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.Lop^[i + 1]) f θ
        = (∑ j ∈ Finset.range (i + 1),
            (i.choose j : ℝ) * ((Work.Spaces.Lop^[i - j]) A θ * (Work.Spaces.Lop^[j]) f θ))
          - (Work.Spaces.Lop^[i]) g θ := by
  intro i θ hθ
  have hU : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  have hθU : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝 θ := hU.mem_nhds hθ
  -- smoothness of the data at `θ`, and of the product `A * f`
  have hAf : ContDiffAt ℝ (Work.FTS.EllipticEst.remov.Baux.DmrOrd i) (A * f) θ :=
    ((hA (i + 1)).mul (hf (i + 1))).contDiffAt hθU |>.of_le
      (Work.FTS.EllipticEst.remov.Baux.Dmr.DmrOrd_le (Nat.le_succ i))
  have hg' : ContDiffAt ℝ (Work.FTS.EllipticEst.remov.Baux.DmrOrd i) g θ :=
    (hg (i + 1)).contDiffAt hθU |>.of_le
      (Work.FTS.EllipticEst.remov.Baux.Dmr.DmrOrd_le (Nat.le_succ i))
  have hA' : ContDiffAt ℝ (Work.FTS.EllipticEst.remov.Baux.DmrOrd i) A θ :=
    (hA (i + 1)).contDiffAt hθU |>.of_le
      (Work.FTS.EllipticEst.remov.Baux.Dmr.DmrOrd_le (Nat.le_succ i))
  have hf' : ContDiffAt ℝ (Work.FTS.EllipticEst.remov.Baux.DmrOrd i) f θ :=
    (hf (i + 1)).contDiffAt hθU |>.of_le
      (Work.FTS.EllipticEst.remov.Baux.Dmr.DmrOrd_le (Nat.le_succ i))
  -- the recursion, as an eventual equality at `θ`
  have hev : Work.Spaces.Lop f =ᶠ[𝓝 θ] (A * f - g) := by
    filter_upwards [hθU] with θ' hθ'
    exact hrec θ' hθ'
  -- the three ingredients: congruence, subtractivity, Leibniz
  have hcongr := Work.FTS.EllipticEst.remov.Baux.Dmr.Lop_iter_congr_at hev i
  have hsub := Work.FTS.EllipticEst.remov.Baux.Dmr.Lop_iter_sub_at i hAf hg'
  have hleib := Work.FTS.EllipticEst.RPFresh.DivSinOpen.LopLeibnizPoint i hA' hf'
  rw [show i + 1 = i.succ from rfl, Function.iterate_succ_apply, hcongr, hsub, hleib,
    sum_range_choose_reflect' i (fun a => (Work.Spaces.Lop^[a]) A θ)
      (fun a => (Work.Spaces.Lop^[a]) f θ)]

end Work.FTS.PhiStar
