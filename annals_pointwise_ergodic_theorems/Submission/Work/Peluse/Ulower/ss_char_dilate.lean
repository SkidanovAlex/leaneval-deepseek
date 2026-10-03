import Mathlib
import Submission.Work.Peluse.Ulower.ss_coset_sum
import Submission.Work.Peluse.Ulower.ss_dft_shift

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

/-- The Fourier coefficient `∑_x F x e(ξ x)` of a function on `ℤ`. -/
def charSum (F : ℤ → ℂ) (ξ : ℝ) : ℂ := ∑' x : ℤ, F x * ee (ξ * (x : ℝ))

lemma summable_charSum {F : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖) (ξ : ℝ) :
    Summable fun x : ℤ => F x * ee (ξ * (x : ℝ)) :=
  Summable.of_norm_bounded hF (fun x => by rw [norm_mul, ee_norm, mul_one])

theorem dev_coset {c : ℤ} (hc : c ≠ 0) (r : ℕ) {g : ℤ → ℂ}
    (hg : Summable fun x : ℤ => ‖g x‖) :
    ∑' x : ℤ, (if (c.natAbs : ℤ) ∣ (x - (r : ℤ)) then g x else 0)
      = ∑' z : ℤ, g (c * (z : ℤ) + (r : ℤ)) := ss_coset_sum hc r hg

theorem dev_dft {n : ℕ} (hn : 1 ≤ n) (r : ℕ) (θ : ℝ) (x : ℤ) :
    ∑ j ∈ Finset.range n,
        ee (-(j : ℝ) * (r : ℝ) / (n : ℝ))
          * ee ((θ + (j : ℝ) / (n : ℝ)) * (x : ℝ))
      = if (n : ℤ) ∣ (x - (r : ℤ)) then (n : ℂ) * ee (θ * (x : ℝ)) else 0 :=
  ss_dft_shift hn r θ x

/-- **A Fourier coefficient of a decimated function is dominated by a Fourier coefficient of the
original.**  For `c ≠ 0`, `r < c.natAbs` and `F : ℤ → ℂ` with summable `ℓ¹`-norm, and any real
`β`, there is a real `ξ` with
`‖∑_z F (c*z + r) e(β z)‖ ≤ ‖∑_x F x e(ξ x)‖`, where `e(t) = Work.Peluse.ee t = exp(2πi t)`.

Route: the residue classes `x = c z + r'` (`r' = 0,…,|c|-1`) and the inverse DFT over `ℤ/|c|`:
placing `ξ_j := (β + j)/c` one has `∑_j e(-j r/|c|) F̂(ξ_j) = |c| · e(β r/|c|) · ∑_z F(cz+r)e(βz)`,
so the `j` maximising `|F̂(ξ_j)|` works.  (`Work.Peluse.Fourier.dftOrthogonality` has the
root-of-unity orthogonality; summing over `ℤ` splits as `∑_x F x = ∑_{r'} ∑_z F(c z + r')` for
`c ≠ 0`.) -/
theorem ss_char_dilate {c : ℤ} (hc : c ≠ 0) {F : ℤ → ℂ}
    (hF : Summable fun x : ℤ => ‖F x‖) (r : ℕ) (hr : r < c.natAbs) (β : ℝ) :
    ∃ ξ : ℝ,
      ‖∑' z : ℤ, F (c * (z : ℤ) + (r : ℤ)) * Work.Peluse.ee (β * (z : ℝ))‖ ≤
        ‖∑' x : ℤ, F x * Work.Peluse.ee (ξ * (x : ℝ))‖ := by
  set n : ℕ := c.natAbs with hn_def
  have hn : 0 < n := by rw [hn_def]; exact Int.natAbs_pos.mpr hc
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  set θ : ℝ := β / (c : ℝ) with hθ_def
  have hθ : θ * (c : ℝ) = β := by rw [hθ_def]; field_simp
  set η : ℕ → ℝ := fun j => θ + (j : ℝ) / (n : ℝ) with hη_def
  -- ## Step 1: the `HasSum` over the `n` frequencies
  have hHs : ∀ j ∈ Finset.range n,
      HasSum (fun x : ℤ => ee (-(j : ℝ) * (r : ℝ) / (n : ℝ)) *
          (F x * ee (η j * (x : ℝ))))
        (ee (-(j : ℝ) * (r : ℝ) / (n : ℝ)) * charSum F (η j)) :=
    fun j _ => (summable_charSum hF (η j)).hasSum.mul_left _
  have hmain : HasSum
      (fun x : ℤ => ∑ j ∈ Finset.range n,
        ee (-(j : ℝ) * (r : ℝ) / (n : ℝ)) * (F x * ee (η j * (x : ℝ))))
      (∑ j ∈ Finset.range n, ee (-(j : ℝ) * (r : ℝ) / (n : ℝ)) * charSum F (η j)) :=
    hasSum_sum hHs
  -- ## Step 2: the pointwise inverse DFT
  have hpt : ∀ x : ℤ,
      (∑ j ∈ Finset.range n,
        ee (-(j : ℝ) * (r : ℝ) / (n : ℝ)) * (F x * ee (η j * (x : ℝ))))
      = (if (n : ℤ) ∣ (x - (r : ℤ)) then (n : ℂ) * (F x * ee (θ * (x : ℝ))) else 0) := by
    intro x
    have h1 : (∑ j ∈ Finset.range n,
        ee (-(j : ℝ) * (r : ℝ) / (n : ℝ)) * (F x * ee (η j * (x : ℝ))))
        = F x * (∑ j ∈ Finset.range n,
            ee (-(j : ℝ) * (r : ℝ) / (n : ℝ)) * ee (η j * (x : ℝ))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [h1, hη_def]
    rw [dev_dft (show 1 ≤ n by omega) r θ x]
    by_cases hx : (n : ℤ) ∣ (x - (r : ℤ))
    · rw [if_pos hx, if_pos hx]; ring
    · rw [if_neg hx, if_neg hx, mul_zero]
  have hmain' : HasSum
      (fun x : ℤ => if (n : ℤ) ∣ (x - (r : ℤ)) then (n : ℂ) * (F x * ee (θ * (x : ℝ))) else 0)
      (∑ j ∈ Finset.range n, ee (-(j : ℝ) * (r : ℝ) / (n : ℝ)) * charSum F (η j)) :=
    hmain.congr_fun (fun x => (hpt x).symm)
  -- ## Step 3: the coset reindexing and the value of the sum
  have hval : (∑ j ∈ Finset.range n, ee (-(j : ℝ) * (r : ℝ) / (n : ℝ)) * charSum F (η j))
      = (n : ℂ) * ee (θ * (r : ℝ)) *
        (∑' z : ℤ, F (c * (z : ℤ) + (r : ℤ)) * ee (β * (z : ℝ))) := by
    rw [← hmain'.tsum_eq]
    have hg : Summable fun x : ℤ => ‖(n : ℂ) * (F x * ee (θ * (x : ℝ)))‖ :=
      (hF.mul_left (n : ℝ)).congr (fun x => by
        rw [norm_mul, norm_mul, Complex.norm_natCast, ee_norm]; ring)
    have hstep := dev_coset hc r (g := fun x : ℤ => (n : ℂ) * (F x * ee (θ * (x : ℝ)))) hg
    rw [← hn_def] at hstep
    rw [hstep]
    have hstep2 : ∀ z : ℤ, (n : ℂ) * (F (c * (z : ℤ) + (r : ℤ)) *
          ee (θ * (((c * (z : ℤ) + (r : ℤ) : ℤ)) : ℝ)))
        = (n : ℂ) * ((F (c * (z : ℤ) + (r : ℤ)) * ee (β * (z : ℝ))) * ee (θ * (r : ℝ))) := by
      intro z
      have harg : θ * (((c * (z : ℤ) + (r : ℤ) : ℤ)) : ℝ) = β * (z : ℝ) + θ * (r : ℝ) := by
        push_cast
        rw [show θ * ((c : ℝ) * (z : ℝ) + (r : ℝ))
            = (θ * (c : ℝ)) * (z : ℝ) + θ * (r : ℝ) by ring, hθ]
      rw [harg, ee_add]
      ring
    rw [tsum_congr hstep2]
    rw [tsum_mul_left]
    rw [tsum_mul_right]
    ring
  -- ## Step 4: norm bound and the maximum over `j`
  set S : ℂ := ∑' z : ℤ, F (c * (z : ℤ) + (r : ℤ)) * ee (β * (z : ℝ)) with hS_def
  have h1 : ‖(n : ℂ) * ee (θ * (r : ℝ)) * S‖ = (n : ℝ) * ‖S‖ := by
    have ha : ‖(n : ℂ) * ee (θ * (r : ℝ))‖ = (n : ℝ) := by
      rw [norm_mul, Complex.norm_natCast, ee_norm, mul_one]
    rw [norm_mul, ha]
  have h2 : ‖∑ j ∈ Finset.range n, ee (-(j : ℝ) * (r : ℝ) / (n : ℝ)) * charSum F (η j)‖
      ≤ ∑ j ∈ Finset.range n, ‖charSum F (η j)‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => ?_))
    rw [norm_mul, ee_norm, one_mul]
  obtain ⟨j₀, -, hmax⟩ := Finset.exists_max_image (Finset.range n)
    (fun j => ‖charSum F (η j)‖) (Finset.nonempty_range_iff.mpr (ne_of_gt hn))
  have h3 : ∑ j ∈ Finset.range n, ‖charSum F (η j)‖ ≤ (n : ℝ) * ‖charSum F (η j₀)‖ :=
    calc ∑ j ∈ Finset.range n, ‖charSum F (η j)‖
        ≤ ∑ j ∈ Finset.range n, ‖charSum F (η j₀)‖ := Finset.sum_le_sum hmax
      _ = (n : ℝ) * ‖charSum F (η j₀)‖ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine ⟨η j₀, ?_⟩
  have hchain : (n : ℝ) * ‖S‖ ≤ (n : ℝ) * ‖charSum F (η j₀)‖ := by
    rw [← h1, ← hval]
    exact le_trans h2 h3
  exact le_of_mul_le_mul_left hchain hnR

end

end Work.Peluse.Ulower
