import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Pigeonhole

namespace Commons.Combinatorics

theorem grid_approx_infinite {ι : Type*} {n : ℕ} (d : ι → Fin n → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (γ : ℝ) (hγ : 0 < γ) (Y : Set ι) (hY : Y.Infinite) (hball : ∀ i ∈ Y, ∀ t, |d i t| ≤ B) :
    ∃ dbar : Fin n → ℝ, (∀ t, dbar t ≤ B + γ) ∧
      {i ∈ Y | ∀ t, d i t ≤ dbar t ∧ dbar t ≤ d i t + γ}.Infinite := by
  classical
  have h2B : 0 ≤ 2 * B := by linarith
  have hquot : 0 ≤ 2 * B / γ := div_nonneg h2B hγ.le
  set M : ℕ := Nat.floor (2 * B / γ) with hM
  have hMle : (M : ℝ) ≤ 2 * B / γ := by
    rw [hM]; exact Nat.floor_le hquot
  have hInfY : Infinite Y := Set.infinite_coe_iff.mpr hY
  -- The grid cell index of each point of `Y`, coordinatewise.
  let g : Y → (Fin n → Fin (M + 1)) := fun y t =>
    ⟨Nat.floor ((d y.1 t + B) / γ), by
      have h2 : (d y.1 t + B) / γ ≤ 2 * B / γ :=
        div_le_div_of_nonneg_right (by
          have := (abs_le.mp (hball y.1 y.2 t)).2; linarith) hγ.le
      have hfm : Nat.floor ((d y.1 t + B) / γ) ≤ M := by
        rw [hM]; exact Nat.floor_mono h2
      exact Nat.lt_succ_iff.mpr hfm⟩
  -- Infinitely many points share a cell.
  obtain ⟨a, ha⟩ := @Finite.exists_infinite_fiber Y (Fin n → Fin (M+1)) hInfY _ g
  let dbar : Fin n → ℝ := fun t => -B + (((a t : ℕ) : ℝ) + 1) * γ
  refine ⟨dbar, ?_, ?_⟩
  · intro t
    have hat : (a t : ℕ) ≤ M := by
      have := (a t).isLt
      omega
    have hcast : (((a t : ℕ) : ℝ)) + 1 ≤ (M : ℝ) + 1 := by
      have : ((a t : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hat
      linarith
    have hmul : (((a t : ℕ) : ℝ) + 1) * γ ≤ ((M : ℝ) + 1) * γ :=
      mul_le_mul_of_nonneg_right hcast hγ.le
    have hbound : ((M : ℝ) + 1) * γ ≤ 2 * B + γ := by
      have h1 : ((M : ℝ) + 1) * γ ≤ (2 * B / γ + 1) * γ :=
        mul_le_mul_of_nonneg_right (by linarith [hMle]) hγ.le
      have h2 : (2 * B / γ + 1) * γ = 2 * B + γ := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hγ), one_mul]
      rwa [h2] at h1
    simp only [dbar]
    linarith
  · have himg : (Subtype.val '' (g ⁻¹' {a})).Infinite :=
      Set.Infinite.image (fun x _ y _ h => Subtype.val_injective h)
        (Set.infinite_coe_iff.mp ha)
    refine Set.Infinite.mono ?_ himg
    rintro i ⟨y, hy, rfl⟩
    have hy' : g y = a := hy
    refine ⟨y.2, fun t => ?_⟩
    have hgt : g y t = a t := congrFun hy' t
    have hval : (Nat.floor ((d y.1 t + B) / γ) : ℝ) = ((a t : ℕ) : ℝ) := by
      have h := congrArg (fun z : Fin (M + 1) => ((z : ℕ) : ℝ)) hgt
      simpa [g] using h
    have hq : 0 ≤ (d y.1 t + B) / γ := div_nonneg (by
      have := (abs_le.mp (hball y.1 y.2 t)).1; linarith) hγ.le
    constructor
    · have h1 : (d y.1 t + B) / γ < (Nat.floor ((d y.1 t + B) / γ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h2 : d y.1 t + B < ((Nat.floor ((d y.1 t + B) / γ) : ℝ) + 1) * γ :=
        (div_lt_iff₀ hγ).mp h1
      simp only [dbar]
      rw [← hval]
      linarith
    · have h1 : (Nat.floor ((d y.1 t + B) / γ) : ℝ) ≤ (d y.1 t + B) / γ := Nat.floor_le hq
      have h2 : (Nat.floor ((d y.1 t + B) / γ) : ℝ) * γ ≤ d y.1 t + B :=
        (le_div_iff₀ hγ).mp h1
      simp only [dbar]
      rw [← hval]
      linarith

end Commons.Combinatorics