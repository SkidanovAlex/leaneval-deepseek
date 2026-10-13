import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.pullback_pylipdef
import Submission.Work.WilG4c.subdiv_normle_multi_bad
import Submission.Work.WilG4c.RescalePredicates
import Submission.Work.WilG4c.ScaledLip

set_option autoImplicit false
noncomputable section
open Classical
open Work.WilkG4c WilkiesDesign WilkiesDesign.CG

namespace Work.WilkG4c

theorem pullback_pylipdef_multi_bad {k p n r : ℕ} (hr : 1 ≤ r) :
    ∀ (F : Work.WilkG4c.Family k p (n + 1))
      (s : Fin (n + 1) → Fin (3 * (Work.WilkG4c.subdivN n r - 1) + 1)),
      Work.WilkG4c.YBound F r → Work.WilkG4c.LipOnCube F 1 →
      (∀ (i : Fin k) (l : Fin p → ℝ), ∃ B : Finset ℝ,
        ∃ γ : (m : ℕ) → (Fin m → Fin (n + 1)) → ℝ → Fin n → ℝ,
          (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
            x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
            ContDiffAt ℝ m (F i l) (Work.WilkG4c.pt x y) →
            |iteratedFDeriv ℝ m (F i l) (Work.WilkG4c.pt x y) (fun t => Pi.single (v t) 1)| ≤
              2 * |iteratedFDeriv ℝ m (F i l) (Work.WilkG4c.curveFun (γ m v) x)
                    (fun t => Pi.single (v t) 1)|) ∧
          (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ), m ≤ r → x ∈ Work.WilkG4c.I →
            |iteratedFDeriv ℝ m (F i l) (Work.WilkG4c.curveFun (γ m v) x)
                (fun t => Pi.single (v t) 1)| ≤
              Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m)) →
      Work.WilkG4c.PYLipDef p n r k
        (fun i l t => F i l (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) := by
  intro F s hY hLip hγ
  set q : Fin (n + 1) → ℝ := Work.WilkG4c.subdivBase (Work.WilkG4c.subdivN n r) s with hqdef
  have hN : 1 ≤ Work.WilkG4c.subdivN n r := Work.WilkG4c.subdivN_pos hr
  have hfam : (fun (i : Fin k) (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) =>
        F i l (fun j => q j + z j / ((Work.WilkG4c.subdivN n r : ℕ) : ℝ)))
      = (fun (i : Fin k) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) =>
        F i l (Work.WilkG4c.subdivMap (Work.WilkG4c.subdivN n r) s t)) := by
    funext i l t
    congr 1
    funext j
    rw [Work.WilG4c.subdivMap_eq_div, hqdef]
  have hRP := Work.WilkG4c.RescalePredicates n p (Work.WilkG4c.subdivN n r) hN q
    (fun j => by rw [hqdef]; exact Work.WilkG4c.subdivBase_nonneg (Work.WilkG4c.subdivN n r) s j)
    (fun j => by
      rw [hqdef]
      simpa [one_div] using
        Work.WilG4c.subdivBase_add_inv_le_one (N := Work.WilkG4c.subdivN n r) hN s j)
    F r 1 le_rfl (by exact_mod_cast hN) (∅ : Set (Fin p → ℝ)) hY hLip
    (fun i l hl => absurd hl (by simp))
  refine ⟨hfam ▸ hRP.1, hfam ▸ hRP.2.1, ?_⟩
  intro i l z hz hcd m hm
  obtain ⟨B, γ, hspec⟩ := hγ i l
  exact Work.WilG4c.subdiv_normle_multi_bad (n := n) (r := r) hr (F i l)
    (Work.WilG4c.abs_le_one_of_YBound hY i l) γ B hspec.1 hspec.2 s m hm z hz hcd

end Work.WilkG4c
