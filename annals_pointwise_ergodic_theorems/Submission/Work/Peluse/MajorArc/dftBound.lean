import Mathlib
import Submission.Work.Peluse.MajorArc.Defs

/-!
# The discrete Fourier bound behind the major-arc estimate (`majorarc`)

This file proves `Work.Peluse.MajorArc.dftBound`, the "there is one good frequency" step in the
evaluation of the triple correlation by a windowed discrete Fourier transform.

Given three windowed sums (`X k`, `Y k` the discrete Fourier transforms of `A` resp. `B` at the
frequency `k/L`, and `Z k` that of `C`), the hypothesis `hTriple` computes the `k`-average of
`X k * Y k * Z k` as `L` times the correlation `T = ∑_{u,y} A u C y B (u+y)`, while `hPa`, `hPb`
are the Plancherel (`ℓ²`) identities for the two transforms.  The conclusion is that for some
frequency `k` one has
`‖T‖ ≤ ‖Z k‖ * √(G H)`.

The proof is Cauchy–Schwarz in `k` (plus `‖Z k‖ ≤ max_k ‖Z k‖`); the only Fourier input is the
sign symmetry `∑_k ‖(+)-transform‖² = ∑_k ‖(-)-transform‖²`, which follows from the
`k ↦ L - k` reindexing and the fact that the transform at `k = L` equals the one at `k = 0`.
-/

namespace Work.Peluse.MajorArc

open scoped BigOperators

/-- Reindexing `k ↦ L - k`: if `g` takes the same value at `L` and at `0`, the two sums agree. -/
private lemma dftBound_sum_range_comp_sub (L : ℕ) (g : ℕ → ℝ) (hg : g L = g 0) :
    ∑ k ∈ Finset.range L, g (L - k) = ∑ k ∈ Finset.range L, g k := by
  have h1 : ∀ k ∈ Finset.range L, g (L - k) = (fun i => g (i + 1)) (L - 1 - k) := by
    intro k hk
    have hk' : k < L := Finset.mem_range.mp hk
    congr 1
    omega
  rw [Finset.sum_congr rfl h1, Finset.sum_range_reflect (fun i => g (i + 1)) L]
  have h2 := Finset.sum_range_succ' g L
  have h3 := Finset.sum_range_succ g L
  linarith [h2, h3]

/-- The `ℓ²` (`Plancherel`) sum of a windowed discrete Fourier transform is invariant under
changing the sign of the frequency. -/
private lemma dftBound_pos_eq_neg (L K : ℕ) (hL : 1 ≤ L) (B : ℤ → ℂ) :
    (∑ k ∈ Finset.range L,
        ‖∑ v ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), B v * ee (((k:ℝ)*(v:ℝ))/(L:ℝ))‖^2)
  = (∑ k ∈ Finset.range L,
        ‖∑ v ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), B v * ee (-((k:ℝ)*(v:ℝ))/(L:ℝ))‖^2) := by
  have hL0 : (L:ℝ) ≠ 0 := by
    have : (0:ℝ) < (L:ℝ) := by exact_mod_cast (by omega : (0:ℕ) < L)
    exact ne_of_gt this
  let Y : ℕ → ℂ := fun k => ∑ v ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), B v * ee (((k:ℝ)*(v:ℝ))/(L:ℝ))
  let V : ℕ → ℂ := fun k => ∑ v ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), B v * ee (-((k:ℝ)*(v:ℝ))/(L:ℝ))
  -- the transform at frequency `L - k` (positive sign) is the transform at frequency `k`
  -- (negative sign), because `(L-k)v/L - (-kv/L) = v ∈ ℤ`.
  have hVY : ∀ k, k ≤ L → V k = Y (L - k) := by
    intro k hk
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
    have hLk : ((L - k : ℕ) : ℝ) = (L:ℝ) - (k:ℝ) := by rw [Nat.cast_sub hk]
    rw [hLk]
    have hx : ((L:ℝ) - (k:ℝ)) * (v:ℝ) / (L:ℝ) = (v:ℝ) + (-(((k:ℝ)*(v:ℝ)))/(L:ℝ)) := by
      rw [sub_mul, sub_div, mul_div_cancel_left₀ (v:ℝ) hL0]
      ring
    rw [hx, ee_add, ee_int, one_mul]
  -- the transform is `1`-periodic up to the identification `L ≡ 0` of the frequencies
  have hY0 : Y L = Y 0 := by
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
    have hLv : (L:ℝ)*(v:ℝ)/(L:ℝ) = (v:ℝ) := mul_div_cancel_left₀ (v:ℝ) hL0
    rw [hLv]
    simp [ee_int]
  have hg : (fun k => ‖Y k‖^2) L = (fun k => ‖Y k‖^2) 0 := by simp only [hY0]
  have key := dftBound_sum_range_comp_sub L (fun k => ‖Y k‖^2) hg
  calc ∑ k ∈ Finset.range L, ‖Y k‖^2
      = ∑ k ∈ Finset.range L, (fun k => ‖Y k‖^2) (L - k) := key.symm
    _ = ∑ k ∈ Finset.range L, ‖V k‖^2 := by
        apply Finset.sum_congr rfl
        intro k hk
        show ‖Y (L - k)‖^2 = ‖V k‖^2
        rw [← hVY k (le_of_lt (Finset.mem_range.mp hk))]

/-- **The abstract good-frequency lemma.**  If the frequencies `k ∈ range L` average to `L * T`
and the `ℓ²`-masses of `X` and `Y` are bounded by `L * G` resp. `L * H`, then some frequency `k`
satisfies `‖T‖ ≤ ‖Z k‖ * √(G H)`. -/
private lemma dftBound_exists_freq (L : ℕ) (hL : 1 ≤ L) (X Y Z : ℕ → ℂ) (G H : ℝ) (T : ℂ)
    (hT : (∑ k ∈ Finset.range L, X k * Y k * Z k) = (L : ℂ) * T)
    (hX : ∑ k ∈ Finset.range L, ‖X k‖^2 ≤ (L:ℝ)*G)
    (hY : ∑ k ∈ Finset.range L, ‖Y k‖^2 ≤ (L:ℝ)*H)
    (hG : 0 ≤ G) (_hH : 0 ≤ H) :
    ∃ k ∈ Finset.range L, ‖T‖ ≤ ‖Z k‖ * Real.sqrt (G*H) := by
  have hLpos : (0:ℝ) < (L:ℝ) := by
    have h1 : (0:ℕ) < L := by omega
    exact_mod_cast h1
  obtain ⟨k0, hk0, hmax⟩ := Finset.exists_max_image (Finset.range L) (fun k => ‖Z k‖)
      (Finset.nonempty_range_iff.mpr (by omega : L ≠ 0))
  refine ⟨k0, hk0, ?_⟩
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range L) (fun k => ‖X k‖) (fun k => ‖Y k‖)
  have hkey : (L:ℝ) * ‖T‖
      ≤ ‖Z k0‖ * (Real.sqrt (∑ k ∈ Finset.range L, ‖X k‖^2) *
                    Real.sqrt (∑ k ∈ Finset.range L, ‖Y k‖^2)) := by
    calc (L:ℝ) * ‖T‖ = ‖(L:ℂ) * T‖ := by rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ k ∈ Finset.range L, X k * Y k * Z k‖ := by rw [hT]
      _ ≤ ∑ k ∈ Finset.range L, ‖X k * Y k * Z k‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range L, ‖X k‖ * ‖Y k‖ * ‖Z k‖ := by
            apply Finset.sum_congr rfl; intro k hk; rw [norm_mul, norm_mul]
      _ ≤ ∑ k ∈ Finset.range L, ‖Z k0‖ * (‖X k‖ * ‖Y k‖) := by
            apply Finset.sum_le_sum; intro k hk
            calc ‖X k‖ * ‖Y k‖ * ‖Z k‖ ≤ ‖X k‖ * ‖Y k‖ * ‖Z k0‖ := by
                  apply mul_le_mul_of_nonneg_left (hmax k hk); positivity
              _ = ‖Z k0‖ * (‖X k‖ * ‖Y k‖) := by ring
      _ = ‖Z k0‖ * ∑ k ∈ Finset.range L, ‖X k‖ * ‖Y k‖ := by rw [Finset.mul_sum]
      _ ≤ ‖Z k0‖ * (Real.sqrt (∑ k ∈ Finset.range L, ‖X k‖^2) *
                      Real.sqrt (∑ k ∈ Finset.range L, ‖Y k‖^2)) :=
            mul_le_mul_of_nonneg_left hcs (norm_nonneg _)
  have hsqrtX : Real.sqrt (∑ k ∈ Finset.range L, ‖X k‖^2) ≤ Real.sqrt ((L:ℝ)*G) :=
    Real.sqrt_le_sqrt hX
  have hsqrtY : Real.sqrt (∑ k ∈ Finset.range L, ‖Y k‖^2) ≤ Real.sqrt ((L:ℝ)*H) :=
    Real.sqrt_le_sqrt hY
  have hLGH : Real.sqrt ((L:ℝ)*G) * Real.sqrt ((L:ℝ)*H) = (L:ℝ) * Real.sqrt (G*H) := by
    rw [← Real.sqrt_mul (mul_nonneg (le_of_lt hLpos) hG) ((L:ℝ)*H)]
    have h2 : ((L:ℝ)*G) * ((L:ℝ)*H) = (L:ℝ)^2 * (G*H) := by ring
    rw [h2, Real.sqrt_mul (by positivity) (G*H), Real.sqrt_sq (le_of_lt hLpos)]
  have hfinal : (L:ℝ) * ‖T‖ ≤ (L:ℝ) * (‖Z k0‖ * Real.sqrt (G*H)) := by
    calc (L:ℝ) * ‖T‖ ≤ ‖Z k0‖ * (Real.sqrt (∑ k ∈ Finset.range L, ‖X k‖^2) *
                      Real.sqrt (∑ k ∈ Finset.range L, ‖Y k‖^2)) := hkey
      _ ≤ ‖Z k0‖ * (Real.sqrt ((L:ℝ)*G) * Real.sqrt ((L:ℝ)*H)) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact mul_le_mul hsqrtX hsqrtY (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = ‖Z k0‖ * ((L:ℝ) * Real.sqrt (G*H)) := by rw [hLGH]
      _ = (L:ℝ) * (‖Z k0‖ * Real.sqrt (G*H)) := by ring
  exact le_of_mul_le_mul_left hfinal hLpos

theorem dftBound (L K₁ K₂ K₃ : ℕ) (hL : 1 ≤ L) (A B C : ℤ → ℂ) (G H : ℝ)
    (hTriple : (∑ k ∈ Finset.range L,
        (∑ u ∈ Finset.Icc (-(K₁ : ℤ)) (K₁ : ℤ),
            A u * Work.Peluse.ee (-((k : ℝ) * (u : ℝ)) / (L : ℝ))) *
        (∑ v ∈ Finset.Icc (-(K₂ : ℤ)) (K₂ : ℤ),
            B v * Work.Peluse.ee (((k : ℝ) * (v : ℝ)) / (L : ℝ))) *
        (∑ y ∈ Finset.Icc (-(K₃ : ℤ)) (K₃ : ℤ),
            C y * Work.Peluse.ee (-((k : ℝ) * (y : ℝ)) / (L : ℝ))))
      = (L : ℂ) * ∑ u ∈ Finset.Icc (-(K₁ : ℤ)) (K₁ : ℤ),
          ∑ y ∈ Finset.Icc (-(K₃ : ℤ)) (K₃ : ℤ), A u * C y * B (u + y))
    (hPa : (∑ k ∈ Finset.range L,
        ‖∑ n ∈ Finset.Icc (-(K₁ : ℤ)) (K₁ : ℤ),
            A n * Work.Peluse.ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))‖ ^ 2)
      = (L : ℝ) * ∑ n ∈ Finset.Icc (-(K₁ : ℤ)) (K₁ : ℤ), ‖A n‖ ^ 2)
    (hPb : (∑ k ∈ Finset.range L,
        ‖∑ n ∈ Finset.Icc (-(K₂ : ℤ)) (K₂ : ℤ),
            B n * Work.Peluse.ee (-((k : ℝ) * (n : ℝ)) / (L : ℝ))‖ ^ 2)
      = (L : ℝ) * ∑ n ∈ Finset.Icc (-(K₂ : ℤ)) (K₂ : ℤ), ‖B n‖ ^ 2)
    (hA : ∑ n ∈ Finset.Icc (-(K₁ : ℤ)) (K₁ : ℤ), ‖A n‖ ^ 2 ≤ G)
    (hB : ∑ n ∈ Finset.Icc (-(K₂ : ℤ)) (K₂ : ℤ), ‖B n‖ ^ 2 ≤ H) :
    ∃ k ∈ Finset.range L,
      ‖∑ u ∈ Finset.Icc (-(K₁ : ℤ)) (K₁ : ℤ), ∑ y ∈ Finset.Icc (-(K₃ : ℤ)) (K₃ : ℤ),
          A u * C y * B (u + y)‖
        ≤ ‖∑ y ∈ Finset.Icc (-(K₃ : ℤ)) (K₃ : ℤ),
              C y * Work.Peluse.ee (-((k : ℝ) * (y : ℝ)) / (L : ℝ))‖ * Real.sqrt (G * H) := by
  have hG : 0 ≤ G := le_trans (Finset.sum_nonneg (fun n _ => by positivity)) hA
  have hH : 0 ≤ H := le_trans (Finset.sum_nonneg (fun n _ => by positivity)) hB
  have hX : ∑ k ∈ Finset.range L,
      ‖∑ u ∈ Finset.Icc (-(K₁ : ℤ)) (K₁ : ℤ),
          A u * ee (-((k : ℝ) * (u : ℝ)) / (L : ℝ))‖ ^ 2 ≤ (L : ℝ) * G := by
    rw [hPa]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  have hY : ∑ k ∈ Finset.range L,
      ‖∑ v ∈ Finset.Icc (-(K₂ : ℤ)) (K₂ : ℤ),
          B v * ee (((k : ℝ) * (v : ℝ)) / (L : ℝ))‖ ^ 2 ≤ (L : ℝ) * H := by
    rw [dftBound_pos_eq_neg L K₂ hL B, hPb]
    exact mul_le_mul_of_nonneg_left hB (by positivity)
  obtain ⟨k, hk, hbound⟩ := dftBound_exists_freq L hL
      (fun k => ∑ u ∈ Finset.Icc (-(K₁ : ℤ)) (K₁ : ℤ),
          A u * ee (-((k : ℝ) * (u : ℝ)) / (L : ℝ)))
      (fun k => ∑ v ∈ Finset.Icc (-(K₂ : ℤ)) (K₂ : ℤ),
          B v * ee (((k : ℝ) * (v : ℝ)) / (L : ℝ)))
      (fun k => ∑ y ∈ Finset.Icc (-(K₃ : ℤ)) (K₃ : ℤ),
          C y * ee (-((k : ℝ) * (y : ℝ)) / (L : ℝ)))
      G H (∑ u ∈ Finset.Icc (-(K₁ : ℤ)) (K₁ : ℤ),
          ∑ y ∈ Finset.Icc (-(K₃ : ℤ)) (K₃ : ℤ), A u * C y * B (u + y))
      hTriple hX hY hG hH
  exact ⟨k, hk, hbound⟩

end Work.Peluse.MajorArc
