import Mathlib
import Submission.Work.WilG4c.PullXLipAt

namespace Work.WilG4c

/-!
  `PullXLipAtPw` — the pointwise form of the `x`-Lipschitz estimate of `Work.WilG4c.PullXLip`,
  with the smoothness hypotheses on the curve `s ↦ γ l s` and on `s ↦ F l (Fin.cons s (γ l s))`
  weakened from `ContDiffAt ℝ 1` to plain `DifferentiableAt` at `x`.

  This is legitimate because the chain rule identity `Work.WilG4b.xDeriv_eq` only ever consumes
  the *derivatives* of those curves at `x`: `ContDiffAt ℝ 1` was used in `PullXLipAt` solely
  through `ContDiffAt.differentiableAt_one` followed by `DifferentiableAt.hasDerivAt`, and the
  latter is available from the pointwise hypothesis directly.

  The `x`-derivative at a near-maximiser `γ l x` is `≤ n + 1` after scaling by `b`:
  the chain rule gives
    `∂₀ f (x, γ l x) = d/ds [f (cons s (γ l s))] (x) - ∑_j ∂_j f (x, γ l x) · γ_j'(x)`,
  and `|∂_j f| ≤ 1` (`hyb`), `|γ_j'| · b ≤ 1` (`hγb`), `|d/ds [...]| · b ≤ 1` (`hcb`) give
  `|∂₀ f| · b ≤ 1 + n`.  Multiplying by `2` via the near-maximality `hmax` finishes.
-/

noncomputable section

open Classical

open WilkiesDesign

theorem PullXLipAtPw {p n : ℕ} (F : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)) (l : Fin p → ℝ) (x b : ℝ) (hb : 0 ≤ b)
    (hγc : γ l x ∈ WilkiesDesign.openCube n)
    (hC1 : ∀ y ∈ WilkiesDesign.openCube n,
      ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x y))
    (hyb : ∀ y ∈ WilkiesDesign.openCube n, ∀ j : Fin n,
      |fderiv ℝ (Work.WilkG4c.famFunHat F) (Work.WilkG4c.xPt l x y)
        (Pi.single (Fin.natAdd p j.succ) 1)| ≤ 1)
    (hmax : ∀ y ∈ WilkiesDesign.openCube n,
      |Work.WilkG4c.xDeriv F l x y| ≤ 2 * |Work.WilkG4c.xDeriv F l x (γ l x)|)
    (hγd : ∀ j : Fin n, DifferentiableAt ℝ (fun s : ℝ => γ l s j) x)
    (hγb : ∀ j : Fin n, |deriv (fun s : ℝ => γ l s j) x| * b ≤ 1)
    (hcb : |deriv (fun s : ℝ => F l (Fin.cons s (γ l s))) x| * b ≤ 1)
    (hcd : DifferentiableAt ℝ (fun s : ℝ => F l (Fin.cons s (γ l s))) x) :
    ∀ y ∈ WilkiesDesign.openCube n,
      |Work.WilkG4c.xDeriv F l x y| * b ≤ 2 * ((n : ℝ) + 1) := by
  intro y hy
  have hb' : 0 ≤ b := hb
  have hγcx : γ l x ∈ WilkiesDesign.openCube n := hγc
  have hd : DifferentiableAt ℝ (Work.WilkG4c.famFunHat F)
      (Work.WilkG4c.xPt l x (γ l x)) :=
    (hC1 (γ l x) hγc).differentiableAt_one
  -- The key bound: at the near-maximiser `γ l x` the scaled `x`-derivative is `≤ n + 1`.
  have hmain : |Work.WilkG4c.xDeriv F l x (γ l x)| * b ≤ (n : ℝ) + 1 := by
    have hxC1 : ContDiffAt ℝ 1 (F l) (Fin.cons x (γ l x)) :=
      Work.WilkG4c.contDiffAt_famFunHat_xPt F l x (γ l x) (hC1 (γ l x) hγc)
    have hγi : ∀ i : Fin n, HasDerivAt (fun s : ℝ => γ l s i)
        (deriv (fun s : ℝ => γ l s i) x) x := by
      intro i
      exact (hγd i).hasDerivAt
    have hφ : HasDerivAt (fun s : ℝ => F l (Fin.cons s (γ l s)))
        (deriv (fun s : ℝ => F l (Fin.cons s (γ l s))) x) x :=
      hcd.hasDerivAt
    -- The chain rule identity of `Work.WilG4b.xDeriv_eq`.
    have hkey := Work.WilG4b.xDeriv_eq (F l) (γ l) x
        (deriv (fun s : ℝ => F l (Fin.cons s (γ l s))) x)
        (fun i : Fin n => deriv (fun s : ℝ => γ l s i) x) hxC1 hγi hφ
    have hx0 := pullX_xDeriv_eq_fderiv F l x (γ l x) hd
    rw [hx0, hkey]
    set φ' : ℝ := deriv (fun s : ℝ => F l (Fin.cons s (γ l s))) x with hφ'def
    set S : ℝ := ∑ i : Fin n, fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)
        * deriv (fun s : ℝ => γ l s i) x with hSdef
    have hphi_b : |φ'| * b ≤ 1 := by rw [hφ'def]; exact hcb
    have hB : ∀ i : Fin n,
        |fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)| ≤ 1 := by
      intro i
      rw [← pullX_fderiv_yDir_eq F l x (γ l x) i hd]
      exact hyb (γ l x) hγc i
    have hSbound : |S| * b ≤ (n : ℝ) := by
      have htri : |S| ≤ ∑ i : Fin n,
          |fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)|
            * |deriv (fun s : ℝ => γ l s i) x| := by
        rw [hSdef]
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul]
      calc |S| * b
          ≤ (∑ i : Fin n, |fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)|
              * |deriv (fun s : ℝ => γ l s i) x|) * b :=
            mul_le_mul_of_nonneg_right htri hb'
        _ = ∑ i : Fin n, (|fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)|
              * |deriv (fun s : ℝ => γ l s i) x|) * b := by rw [Finset.sum_mul]
        _ = ∑ i : Fin n, |fderiv ℝ (F l) (Fin.cons x (γ l x)) (Pi.single i.succ 1)|
              * (|deriv (fun s : ℝ => γ l s i) x| * b) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ ≤ ∑ _i : Fin n, (1 : ℝ) * 1 := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul (hB i) (hγb i) (mul_nonneg (abs_nonneg _) hb') zero_le_one
        _ = (n : ℝ) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have htri2 : |φ' - S| ≤ |φ'| + |S| := by
      have := abs_add_le φ' (-S)
      simpa [sub_eq_add_neg] using this
    calc |φ' - S| * b ≤ (|φ'| + |S|) * b := mul_le_mul_of_nonneg_right htri2 hb'
      _ = |φ'| * b + |S| * b := by ring
      _ ≤ 1 + n := add_le_add hphi_b hSbound
      _ = (n : ℝ) + 1 := by ring
  -- Finally use the near-maximality of `γ l x` on the fibre.
  have h2 : |Work.WilkG4c.xDeriv F l x y| ≤ 2 * |Work.WilkG4c.xDeriv F l x (γ l x)| :=
    hmax y hy
  calc |Work.WilkG4c.xDeriv F l x y| * b
      ≤ (2 * |Work.WilkG4c.xDeriv F l x (γ l x)|) * b :=
        mul_le_mul_of_nonneg_right h2 hb'
    _ = 2 * (|Work.WilkG4c.xDeriv F l x (γ l x)| * b) := by ring
    _ ≤ 2 * ((n : ℝ) + 1) := by linarith [hmain]

end

end Work.WilG4c
