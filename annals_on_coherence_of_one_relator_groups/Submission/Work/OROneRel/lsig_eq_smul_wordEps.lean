import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.MagnusRewrite

universe u

namespace Work.OROneRel

theorem lsig_eq_smul_wordEps {α : Type u} (c : α → ℤ) (x y : α) (hxy : x ≠ y) (hc : ∀ z : α, z ≠ x → z ≠ y → c z = 0) (L : List (α × Bool)) : Work.OROneRel.lsig c L = c x * Work.OROneRel.wordEps x L + c y * Work.OROneRel.wordEps y L := by
  classical
  -- Pointwise, the weight contribution of a letter `p` is `c x` times its sign if it is `x`,
  -- `c y` times its sign if it is `y`, and `0` otherwise.
  have hterm : ∀ p : α × Bool, (if p.2 then c p.1 else -c p.1)
      = c x * (if p.1 = x then (if p.2 then (1 : ℤ) else -1) else 0)
        + c y * (if p.1 = y then (if p.2 then (1 : ℤ) else -1) else 0) := by
    rintro ⟨a, b⟩
    by_cases hax : a = x
    · rw [hax]
      simp only [if_true, hxy, if_false, mul_zero, add_zero]
      cases b <;> simp
    · by_cases hay : a = y
      · rw [← hay]
        simp only [if_true, hax, if_false, mul_zero]
        cases b <;> simp
      · simp only [if_neg hax, if_neg hay, hc a hax hay]
        cases b <;> simp
  have hmap : (L.map fun p => (if p.2 then c p.1 else -c p.1))
      = L.map (fun p => c x * (if p.1 = x then (if p.2 then (1 : ℤ) else -1) else 0)
                    + c y * (if p.1 = y then (if p.2 then (1 : ℤ) else -1) else 0)) :=
    List.map_congr_left fun p _ => hterm p
  calc Work.OROneRel.lsig c L
      = (L.map fun p => (if p.2 then c p.1 else -c p.1)).sum := rfl
    _ = (L.map (fun p => c x * (if p.1 = x then (if p.2 then (1 : ℤ) else -1) else 0)
                    + c y * (if p.1 = y then (if p.2 then (1 : ℤ) else -1) else 0))).sum := by rw [hmap]
    _ = (L.map fun p => c x * (if p.1 = x then (if p.2 then (1 : ℤ) else -1) else 0)).sum
        + (L.map fun p => c y * (if p.1 = y then (if p.2 then (1 : ℤ) else -1) else 0)).sum :=
        List.sum_map_add
    _ = c x * (L.map fun p => (if p.1 = x then (if p.2 then (1 : ℤ) else -1) else 0)).sum
        + c y * (L.map fun p => (if p.1 = y then (if p.2 then (1 : ℤ) else -1) else 0)).sum := by
        rw [List.sum_map_mul_left, List.sum_map_mul_left]
    _ = c x * Work.OROneRel.wordEps x L + c y * Work.OROneRel.wordEps y L := rfl

end Work.OROneRel
