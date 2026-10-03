import Mathlib
import Submission.Work.Peluse.Prop36SW.uNormPow_one_collapse

namespace Work.Peluse.Prop36SW

/-- `Npow 1 (fun _ => 1) S f K` is, definitionally, the window cardinality times `K` times the
uniformity-norm power at the single step set `arithIcc 1 K`. -/
private lemma npow_one_eq_u (M K : ℕ) (h : ℤ → ℂ) :
    Work.Peluse.TransferUp.Npow 1 (fun _ : Fin 1 => (1 : ℤ)) (Work.Peluse.symIcc M) h K
      = (((Work.Peluse.symIcc M).card : ℝ) * (K : ℝ))
        * Work.Peluse.uNormPow 1 (Work.Peluse.arithIcc (1 : ℤ) K) (Work.Peluse.symIcc M) h := by
  simp only [Work.Peluse.TransferUp.Npow, Work.Peluse.uNormPow, pow_one]

/-- Multiplication bookkeeping: the `L⁻¹` of the collapse factor cancels the extra factor `L` that
comes from the `Npow` normalisation. -/
private lemma npow_div_cancel (a c H b L : ℝ) (hL : L ≠ 0) :
    a * L * (c * (H / L) * b) = c * (a * H * b) := by
  field_simp

theorem npowOneCollapseLe :
    ∃ C : ℝ, 0 < C ∧ ∀ (L M : ℕ) (h : ℤ → ℂ), 1 ≤ M → 2 * M + 1 ≤ L →
      Work.Peluse.SupportIn h M → (∀ x : ℤ, ‖h x‖ ≤ 1) →
        Work.Peluse.TransferUp.Npow 1 (fun _ : Fin 1 => (1 : ℤ)) (Work.Peluse.symIcc M) h L
          ≤ C * Work.Peluse.TransferUp.Npow 1 (fun _ : Fin 1 => (1 : ℤ)) (Work.Peluse.symIcc M) h (2 * M + 1) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := uNormPow_one_collapse
  refine ⟨C₀, hC₀pos, ?_⟩
  intro L M h hM hLM hsup hb
  have hLpos : 0 < L := by omega
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hLpos)
  have hcoll := hC₀ L M h hM hLM hsup hb
  have hcard : (0 : ℝ) ≤ ((Work.Peluse.symIcc M).card : ℝ) := by positivity
  have hkey := mul_le_mul_of_nonneg_left hcoll (mul_nonneg hcard (by positivity : (0 : ℝ) ≤ (L : ℝ)))
  rw [npow_one_eq_u M L h, npow_one_eq_u M (2 * M + 1) h]
  calc ((Work.Peluse.symIcc M).card : ℝ) * (L : ℝ)
        * Work.Peluse.uNormPow 1 (Work.Peluse.arithIcc (1 : ℤ) L) (Work.Peluse.symIcc M) h
      ≤ ((Work.Peluse.symIcc M).card : ℝ) * (L : ℝ)
          * (C₀ * (((2 * M + 1 : ℕ) : ℝ) / (L : ℝ))
              * Work.Peluse.uNormPow 1 (Work.Peluse.arithIcc (1 : ℤ) (2 * M + 1)) (Work.Peluse.symIcc M) h) :=
        hkey
    _ = C₀ * (((Work.Peluse.symIcc M).card : ℝ) * ((2 * M + 1 : ℕ) : ℝ)
          * Work.Peluse.uNormPow 1 (Work.Peluse.arithIcc (1 : ℤ) (2 * M + 1)) (Work.Peluse.symIcc M) h) := by
        exact npow_div_cancel _ _ _ _ _ hLne

end Work.Peluse.Prop36SW
