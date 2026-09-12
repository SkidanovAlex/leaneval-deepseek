import Mathlib.Analysis.InnerProductSpace.ExteriorPower

namespace Commons.Analysis.InnerProductSpace

open exteriorPower

private lemma inner_map_map_of_exteriorPower_isometry {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (f : E ≃ₗᵢ[ℝ] E) :
    ∀ x y : ⋀[ℝ]^k E,
      inner ℝ (exteriorPower.map k (f : E →ₗ[ℝ] E) x) (exteriorPower.map k (f : E →ₗ[ℝ] E) y) =
        inner ℝ x y := by
  classical
  let T : (⋀[ℝ]^k E) →ₗ[ℝ] (⋀[ℝ]^k E) := exteriorPower.map k (f : E →ₗ[ℝ] E)
  have hmap : ∀ (m : Fin k → E),
      T (exteriorPower.ιMulti ℝ k m) = exteriorPower.ιMulti ℝ k ((f : E →ₗ[ℝ] E) ∘ m) := by
    intro m
    simp [T]
  have hdec : ∀ m n : Fin k → E,
      inner ℝ (T (exteriorPower.ιMulti ℝ k m)) (T (exteriorPower.ιMulti ℝ k n)) =
        inner ℝ (exteriorPower.ιMulti ℝ k m) (exteriorPower.ιMulti ℝ k n) := by
    intro m n
    rw [hmap m, hmap n]
    rw [exteriorPower.inner_ιMulti_ιMulti, exteriorPower.inner_ιMulti_ιMulti]
    congr 1
    ext i j
    simp
  have hfirst : ∀ (n : Fin k → E) (y : ⋀[ℝ]^k E),
      inner ℝ (T (exteriorPower.ιMulti ℝ k n)) (T y) =
        inner ℝ (exteriorPower.ιMulti ℝ k n) y := by
    intro n y
    have hφψ :
        ((innerₗ (⋀[ℝ]^k E)) (T (exteriorPower.ιMulti ℝ k n))).comp T =
          (innerₗ (⋀[ℝ]^k E)) (exteriorPower.ιMulti ℝ k n) := by
      apply exteriorPower.linearMap_ext (R := ℝ) (n := k) (M := E) (N := ℝ)
      ext m
      simpa using hdec n m
    have hφψy := DFunLike.congr_fun hφψ y
    simpa using hφψy
  have hsecond : ∀ (y x : ⋀[ℝ]^k E),
      inner ℝ (T y) (T x) = inner ℝ y x := by
    intro y x
    have hφψ : ((innerₗ (⋀[ℝ]^k E)) (T y)).comp T = (innerₗ (⋀[ℝ]^k E)) y := by
      apply exteriorPower.linearMap_ext (R := ℝ) (n := k) (M := E) (N := ℝ)
      ext m
      have h := hfirst m y
      have h1 := real_inner_comm (T (exteriorPower.ιMulti ℝ k m)) (T y)
      have h2 := real_inner_comm (exteriorPower.ιMulti ℝ k m) y
      simpa using (h1.trans h).trans h2.symm
    have hφψx := DFunLike.congr_fun hφψ x
    simpa using hφψx
  intro x y
  have hc := hsecond y x
  exact (real_inner_comm (T y) (T x)).trans (hc.trans (real_inner_comm y x).symm)

lemma norm_map_exteriorPower_of_linearIsometry {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (f : E ≃ₗᵢ[ℝ] E) (w : ⋀[ℝ]^k E) :
    ‖exteriorPower.map k (f : E →ₗ[ℝ] E) w‖ = ‖w‖ := by
  have hinner := inner_map_map_of_exteriorPower_isometry (E := E) (k := k) f
  have hsq : ‖exteriorPower.map k (f : E →ₗ[ℝ] E) w‖ ^ 2 = ‖w‖ ^ 2 := by
    calc
      ‖exteriorPower.map k (f : E →ₗ[ℝ] E) w‖ ^ 2 =
          inner ℝ (exteriorPower.map k (f : E →ₗ[ℝ] E) w) (exteriorPower.map k (f : E →ₗ[ℝ] E) w) := by
        simp
      _ = inner ℝ w w := hinner w w
      _ = ‖w‖ ^ 2 := by
        simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have hpos1 : 0 ≤ ‖exteriorPower.map k (f : E →ₗ[ℝ] E) w‖ := norm_nonneg _
    have hpos2 : 0 ≤ ‖w‖ := norm_nonneg _
    nlinarith

end Commons.Analysis.InnerProductSpace
