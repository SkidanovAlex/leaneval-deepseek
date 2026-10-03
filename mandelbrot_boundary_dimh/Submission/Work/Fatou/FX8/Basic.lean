import Submission.Work.Fatou.FX8.Defs

/-!
# FX8, step 2: the deck shift in exponentiated form

`Tpow D n` is the `n`-fold deck shift `u ↦ u + n` on `XF D` (for `n : ℤ`), and `shift_Tpow` is
the induced shift of a biholomorphism `Ψ : XF D ≃ ℂ` whose deck shift is `b`.
-/

namespace Work.Fatou.FX8

open MandelDim Set Metric Complex
open scoped Topology Manifold ContDiff
open LeanEval.Geometry
open Classical

noncomputable section

open Work.Fatou

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}

/-- The `n`-fold deck shift `u ↦ u + n` on `XF D`, for `n : ℤ`. -/
def Tpow (D : Work.Fatou.FatouData) (n : ℤ) : D.XF → D.XF := fun u => D.ofℂ (D.toℂ u + (n : ℂ))

@[simp] theorem toℂ_Tpow (D : Work.Fatou.FatouData) (n : ℤ) (u : D.XF) :
    D.toℂ (Tpow D n u) = D.toℂ u + (n : ℂ) := rfl

theorem Tpow_zero (D : Work.Fatou.FatouData) (u : D.XF) : Tpow D 0 u = u := by
  show D.ofℂ (D.toℂ u + ((0 : ℤ) : ℂ)) = u
  rw [Int.cast_zero, add_zero, D.ofℂ_toℂ]

theorem Tpow_one (D : Work.Fatou.FatouData) (u : D.XF) : Tpow D 1 u = D.T u := by
  show D.ofℂ (D.toℂ u + ((1 : ℤ) : ℂ)) = D.ofℂ (D.toℂ u + 1)
  norm_num

theorem Tpow_neg_one (D : Work.Fatou.FatouData) (u : D.XF) : Tpow D (-1) u = D.Tinv u := by
  show D.ofℂ (D.toℂ u + ((-1 : ℤ) : ℂ)) = D.ofℂ (D.toℂ u - 1)
  congr 1
  norm_num
  ring

theorem Tpow_succ (D : Work.Fatou.FatouData) (n : ℤ) (u : D.XF) :
    Tpow D (n + 1) u = D.T (Tpow D n u) := by
  show D.ofℂ (D.toℂ u + ((n + 1 : ℤ) : ℂ)) = D.ofℂ (D.toℂ (Tpow D n u) + 1)
  rw [toℂ_Tpow]
  have h : ((n + 1 : ℤ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
  rw [h]
  congr 1
  ring

theorem Tpow_add (D : Work.Fatou.FatouData) (m n : ℤ) (u : D.XF) :
    Tpow D (m + n) u = Tpow D m (Tpow D n u) := by
  show D.ofℂ (D.toℂ u + ((m + n : ℤ) : ℂ)) = D.ofℂ (D.toℂ (Tpow D n u) + (m : ℂ))
  rw [toℂ_Tpow]
  have : ((m + n : ℤ) : ℂ) = (m : ℂ) + (n : ℂ) := by push_cast; ring
  rw [this]
  congr 1
  ring

/-- **The deck shift of `Ψ` in the exponentiated form.** -/
theorem shift_Tpow {D : Work.Fatou.FatouData}
    {Ψ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ} {b : ℂ}
    (hshift : ∀ u, Ψ (D.T u) = Ψ u + b) (n : ℤ) (u : D.XF) :
    Ψ (Tpow D n u) = Ψ u + (n : ℂ) * b := by
  have hnat : ∀ (k : ℕ) (u : D.XF), Ψ (Tpow D (k : ℤ) u) = Ψ u + (k : ℂ) * b := by
    intro k
    induction k with
    | zero => intro u; simp [Tpow]
    | succ k ih =>
      intro u
      have hk : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [hk, Tpow_succ D (k : ℤ) u, hshift, ih]
      push_cast
      ring
  have hT1 : ∀ u : D.XF, Ψ (Tpow D (-1) u) = Ψ u - b := by
    intro u
    have h := hshift (Tpow D (-1) u)
    rw [show D.T (Tpow D (-1) u) = u from by
      rw [Tpow_neg_one D u, D.T_Tinv]] at h
    rw [h]
    ring
  have hneg : ∀ (k : ℕ) (u : D.XF),
      Ψ (Tpow D (-(k : ℤ)) u) = Ψ u + ((-(k : ℤ) : ℤ) : ℂ) * b := by
    intro k
    induction k with
    | zero => intro u; simp [Tpow]
    | succ k ih =>
      intro u
      have hk : -(((k + 1 : ℕ)) : ℤ) = -((k : ℤ) + 1) := by push_cast; ring
      rw [hk]
      have hsplit : Tpow D (-(((k : ℤ) + 1))) u = Tpow D (-(k : ℤ)) (Tpow D (-1) u) := by
        rw [← Tpow_add]; congr 1; ring
      rw [hsplit, ih, hT1]
      have : ((-(k : ℤ) : ℤ) : ℂ) = -((k : ℂ)) := by push_cast; ring
      rw [this]
      push_cast
      ring
  by_cases hn : 0 ≤ n
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact hnat k u
  · have hlt : n < 0 := lt_of_not_ge hn
    obtain ⟨k, hk⟩ := Int.eq_negSucc_of_lt_zero hlt
    have hnk : n = -(((k : ℤ) + 1)) := by
      rw [hk]
      simp [Int.negSucc_eq]
    rw [hnk]
    exact hneg (k + 1) u

end

end Work.Fatou.FX8
