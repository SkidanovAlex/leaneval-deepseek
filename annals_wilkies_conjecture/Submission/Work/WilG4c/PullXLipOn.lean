import Mathlib
import Submission.Work.WilG4c.PullXLip
import Submission.Work.WilG4b.xDeriv_eq

namespace Work.WilG4c

/-!
  `PullXLipOn` — the same `x`-Lipschitz estimate as `Work.WilG4c.PullXLip`, but over an
  arbitrary interval `(u, v)` of `x`-values rather than the normalised interval
  `(α l, α l + β l)`.  Nothing in the argument of `PullXLip` depends on the endpoints: the
  only places the interval is used are as the domain of the `ContDiffOn` hypotheses of the
  chain rule along `s ↦ (s, γ l s)`.  We therefore run the very same chain-rule computation
  here, with `Set.Ioo u v` in place of `Set.Ioo (α l) (α l + β l)`.
-/

noncomputable section

open Classical

open WilkiesDesign

theorem PullXLipOn {p n : ℕ} (F : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (β : (Fin p → ℝ) → ℝ) (l : Fin p → ℝ)
    (u v : ℝ) (huv : u < v) (hβ : 0 < β l)
    (hγc : ∀ x ∈ Set.Ioo u v, γ l x ∈ WilkiesDesign.openCube n)
    (hC1 : ∀ x ∈ Set.Ioo u v, ∀ y ∈ WilkiesDesign.openCube n,
      ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x y))
    (hyb : ∀ x ∈ Set.Ioo u v, ∀ y ∈ WilkiesDesign.openCube n, ∀ j : Fin n,
      |fderiv ℝ (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x y)
        (Pi.single (Fin.natAdd p j.succ) 1)| ≤ 1)
    (hmax : ∀ x ∈ Set.Ioo u v, ∀ y ∈ WilkiesDesign.openCube n,
      |Work.WilkG4c.xDeriv F l x y| ≤ 2 * |Work.WilkG4c.xDeriv F l x (γ l x)|)
    (hγC1 : ∀ j : Fin n, ContDiffOn ℝ 1 (fun s : ℝ => γ l s j) (Set.Ioo u v))
    (hγb : ∀ x ∈ Set.Ioo u v, ∀ j : Fin n,
      |deriv (fun s : ℝ => γ l s j) x| * β l ≤ 1)
    (hcb : ∀ x ∈ Set.Ioo u v,
      |deriv (fun s : ℝ => F l (Fin.cons s (γ l s))) x| * β l ≤ 1)
    (hcC1 : ContDiffOn ℝ 1 (fun s : ℝ => F l (Fin.cons s (γ l s))) (Set.Ioo u v)) :
    ∀ x ∈ Set.Ioo u v, ∀ y ∈ WilkiesDesign.openCube n,
      |Work.WilkG4c.xDeriv F l x y| * β l ≤ 2 * ((n : ℝ) + 1) := by
  intro x hx y hy
  have hβnn : 0 ≤ β l := le_of_lt hβ
  have hγcx : γ l x ∈ WilkiesDesign.openCube n := hγc x hx
  have hd : DifferentiableAt ℝ (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x (γ l x)) :=
    (hC1 x hx (γ l x) hγcx).differentiableAt_one
  -- The key bound: at the near-maximiser `γ l x` the scaled `x`-derivative is `≤ n + 1`.
  have hmain : |Work.WilkG4c.xDeriv F l x (γ l x)| * β l ≤ (n : ℝ) + 1 := by
    have hxC1 : ContDiffAt ℝ 1 (F l) (Fin.cons x (γ l x)) :=
      Work.WilkG4c.contDiffAt_famFunHat_xPt F l x (γ l x) (hC1 x hx (γ l x) hγcx)
    have hγi : ∀ i : Fin n, HasDerivAt (fun s : ℝ => γ l s i)
        (deriv (fun s : ℝ => γ l s i) x) x := by
      intro i
      exact ((hγC1 i).contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt_one.hasDerivAt
    have hφ : HasDerivAt (fun s : ℝ => F l (Fin.cons s (γ l s)))
        (deriv (fun s : ℝ => F l (Fin.cons s (γ l s))) x) x :=
      (hcC1.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt_one.hasDerivAt
    -- The chain rule identity of `Work.WilG4b.xDeriv_eq`.
    have hkey := Work.WilG4b.xDeriv_eq (F l) (γ l) x
        (deriv (fun s : ℝ => F l (Fin.cons s (γ l s))) x)
        (fun i : Fin n => deriv (fun s : ℝ => γ l s i) x) hxC1 hγi hφ
    have hx0 := pullX_xDeriv_eq_fderiv F l x (γ l x) hd
    rw [hx0, hkey]
    set φ' : ℝ := deriv (fun s : ℝ => F l (Fin.cons s (γ l s))) x with hφ'def
    set S : ℝ := ∑ i : Fin n, fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)
        * deriv (fun s : ℝ => γ l s i) x with hSdef
    have hphi_b : |φ'| * β l ≤ 1 := by rw [hφ'def]; exact hcb x hx
    have hB : ∀ i : Fin n,
        |fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)| ≤ 1 := by
      intro i
      rw [← pullX_fderiv_yDir_eq F l x (γ l x) i hd]
      exact hyb x hx (γ l x) hγcx i
    have hSbound : |S| * β l ≤ (n : ℝ) := by
      have htri : |S| ≤ ∑ i : Fin n,
          |fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)|
            * |deriv (fun s : ℝ => γ l s i) x| := by
        rw [hSdef]
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul]
      calc |S| * β l
          ≤ (∑ i : Fin n, |fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)|
              * |deriv (fun s : ℝ => γ l s i) x|) * β l :=
            mul_le_mul_of_nonneg_right htri hβnn
        _ = ∑ i : Fin n, (|fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)|
              * |deriv (fun s : ℝ => γ l s i) x|) * β l := by rw [Finset.sum_mul]
        _ = ∑ i : Fin n, |fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)|
              * (|deriv (fun s : ℝ => γ l s i) x| * β l) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ ≤ ∑ _i : Fin n, (1 : ℝ) * 1 := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul (hB i) (hγb x hx i) (mul_nonneg (abs_nonneg _) hβnn) zero_le_one
        _ = (n : ℝ) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have htri2 : |φ' - S| ≤ |φ'| + |S| := by
      have := abs_add_le φ' (-S)
      simpa [sub_eq_add_neg] using this
    calc |φ' - S| * β l ≤ (|φ'| + |S|) * β l := mul_le_mul_of_nonneg_right htri2 hβnn
      _ = |φ'| * β l + |S| * β l := by ring
      _ ≤ 1 + n := add_le_add hphi_b hSbound
      _ = (n : ℝ) + 1 := by ring
  -- Finally use the near-maximality of `γ l x` on the fibre.
  have h2 : |Work.WilkG4c.xDeriv F l x y| ≤ 2 * |Work.WilkG4c.xDeriv F l x (γ l x)| :=
    hmax x hx y hy
  calc |Work.WilkG4c.xDeriv F l x y| * β l
      ≤ (2 * |Work.WilkG4c.xDeriv F l x (γ l x)|) * β l :=
        mul_le_mul_of_nonneg_right h2 hβnn
    _ = 2 * (|Work.WilkG4c.xDeriv F l x (γ l x)| * β l) := by ring
    _ ≤ 2 * ((n : ℝ) + 1) := by linarith [hmain]

end

end Work.WilG4c
