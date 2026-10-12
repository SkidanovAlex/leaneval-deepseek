import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.KzWindowGeAbsA` — the `|A|`-weighted window bound for `Σ_k n_k`

On the `n₊`-window `[0,𝓜]` (`TildeData.NWindow M g`), if the total number operator
`Σ_k n_k = Σ_k a_k†a_k` is Bessel-dominated by FS's true excited number `n₊ = T.N` with
constant `Cn`, then for *every* real weight `A` the `|A|`-weighted sum of the single-mode
diagonal number forms `⟨n_k g, g⟩ + ⟨n_{-k} g, g⟩` is bounded by the `ℓ¹` weight times the
total window bound:

  `Σ_k |A_k| (⟨n_k g,g⟩ + ⟨n_{-k} g,g⟩) ≤ 2 (Σ_k |A_k|)·Cn·𝓜·‖g‖²`.

The proof uses only three facts:
* `⟨n_k g, g⟩ = ‖a_k g‖² ≥ 0` for every mode `k` (`bp_nOp_nonneg`), so the summands are
  nonnegative and `|A_k| ≤ Σ_j |A_j|` bounds the weight pointwise;
* `Σ_k ⟨n_k g,g⟩ = ⟨(Σ_k n_k) g, g⟩` and the two halves `k`, `-k` of the sum contribute
  equally (`k ↦ -k` is a bijection of `Mode`);
* the window gives `⟨n₊ g,g⟩ ≤ 𝓜‖g‖²` (`NWindow_bp_N_le`), which `hBessel` converts into
  `Σ_k ⟨n_k g,g⟩ ≤ Cn·𝓜·‖g‖²`.
-/

namespace Work.BoseBoxFock

open BigOperators

theorem KzWindowGeAbsA {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (Cn : ℝ) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    {M : ℝ} (hM : 0 ≤ M) {g : F.H} (hg : T.NWindow M g) (A : Mode → ℝ) :
    (∑ k : Mode, |A k| * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g))
      ≤ 2 * (∑ k : Mode, |A k|) * (Cn * M * F.normSq g) := by
  -- the two halves of the sum (`k` and `-k`) are equal, `k ↦ -k` being a bijection
  have hreindex : (∑ k : Mode, F.bp (F.nOp (-k) g) g)
      = ∑ k : Mode, F.bp (F.nOp k g) g :=
    Equiv.sum_comp (Equiv.neg Mode) (fun k => F.bp (F.nOp k g) g)
  have hxsum : (∑ k : Mode, (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g))
      = 2 * ∑ k : Mode, F.bp (F.nOp k g) g := by
    rw [Finset.sum_add_distrib, hreindex]; ring
  -- the window bound for the true excited number `n₊`
  have hNle : F.bp (T.N g) g ≤ M * F.normSq g :=
    Work.BoseB7A.NWindow_bp_N_le F T hM hg
  -- Bessel + window: the total single-mode number form is `≤ Cn·𝓜·‖g‖²`
  have htotal : (∑ k : Mode, F.bp (F.nOp k g) g) ≤ Cn * M * F.normSq g := by
    have h1 : (∑ k : Mode, F.bp (F.nOp k g) g) = F.bp ((∑ k : Mode, F.nOp k) g) g := by
      simp only [LinearMap.sum_apply, map_sum]
    rw [h1]
    calc F.bp ((∑ k : Mode, F.nOp k) g) g ≤ Cn * F.bp (T.N g) g := hBessel g
      _ ≤ Cn * (M * F.normSq g) := mul_le_mul_of_nonneg_left hNle hCn0
      _ = Cn * M * F.normSq g := by ring
  -- the weight is dominated pointwise by its `ℓ¹`-norm (all summands are nonnegative)
  have hpoint : ∀ k : Mode,
      |A k| * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)
        ≤ (∑ j : Mode, |A j|) * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g) := by
    intro k
    refine mul_le_mul_of_nonneg_right ?_ ?_
    · exact Finset.single_le_sum (fun j _ => abs_nonneg (A j)) (Finset.mem_univ k)
    · exact add_nonneg (Work.BoseB7.bp_nOp_nonneg F k g) (Work.BoseB7.bp_nOp_nonneg F (-k) g)
  have hA0 : 0 ≤ ∑ j : Mode, |A j| := Finset.sum_nonneg (fun j _ => abs_nonneg (A j))
  calc (∑ k : Mode, |A k| * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g))
      ≤ ∑ k : Mode, (∑ j : Mode, |A j|) * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g) :=
        Finset.sum_le_sum (fun k _ => hpoint k)
    _ = (∑ j : Mode, |A j|) * (∑ k : Mode, (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)) := by
        rw [Finset.mul_sum]
    _ = (∑ j : Mode, |A j|) * (2 * ∑ k : Mode, F.bp (F.nOp k g) g) := by rw [hxsum]
    _ ≤ (∑ j : Mode, |A j|) * (2 * (Cn * M * F.normSq g)) :=
        mul_le_mul_of_nonneg_left (by linarith [htotal]) hA0
    _ = 2 * (∑ j : Mode, |A j|) * (Cn * M * F.normSq g) := by ring

end Work.BoseBoxFock
