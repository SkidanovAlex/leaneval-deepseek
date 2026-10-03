import Mathlib
import Submission.Work.Peluse.Pel51.defs

namespace Work.Peluse.Pel51

/-- **Regime I of the level transfer.**  If `η · M₁ · (B₀+1) ≤ 1` and `|b₀| ≤ B₀ · M₁`, then the
level-`2` bad set is contained in the level-`1` bad set.

Indeed, for every `a ∈ [1,M₁]` we have `|a + b₀| ≤ M₁ + B₀·M₁ = M₁(B₀+1)`, hence
`η·|a+b₀| ≤ 1`, i.e. `|a+b₀| ≤ 1/η`.  Since `Int.gcd (a+b₀) (a+b₀) = |a+b₀|`, the *gcd condition*
of the level-`2` predicate holds **automatically** on `[1,M₁]`; the level-`1` predicate has a
vacuous gcd condition.  So both bad sets are the same filter, namely the `a ∈ [1,M₁]` failing the
*size* condition `η·M₁ ≤ |a+b₀|`. -/
theorem badP_regime_one (M₁ : ℕ) (b₀ : ℤ) (η : ℝ) (B₀ : ℕ)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hreg : η * (M₁ : ℝ) * ((B₀ : ℝ) + 1) ≤ 1) (hb : |b₀| ≤ (B₀ : ℤ) * (M₁ : ℤ)) :
    (Work.Peluse.Pel51.badP 2 M₁ (fun _ : Fin 2 => b₀) η).card
      ≤ (Work.Peluse.Pel51.badP 1 M₁ (fun _ : Fin 1 => b₀) η).card := by
  -- The gcd condition `gcd (a + b₀) (a + b₀) ≤ 1/η` holds for every `a ∈ [1,M₁]`.
  have hgcd : ∀ {a : ℕ}, a ∈ Finset.Icc 1 M₁ →
      ((Int.gcd ((a : ℤ) + b₀) ((a : ℤ) + b₀) : ℕ) : ℝ) ≤ 1 / η := by
    intro a ha
    rw [Int.gcd_self, le_div_iff₀ hη0]
    have ha2 : a ≤ M₁ := (Finset.mem_Icc.mp ha).2
    -- `b₀.natAbs ≤ B₀ * M₁`
    have hb_nat : b₀.natAbs ≤ B₀ * M₁ := by
      have h2 : ((b₀.natAbs : ℤ)) ≤ ((B₀ * M₁ : ℕ) : ℤ) := by
        calc (b₀.natAbs : ℤ) = |b₀| := (Int.abs_eq_natAbs b₀).symm
          _ ≤ (B₀ : ℤ) * (M₁ : ℤ) := hb
          _ = ((B₀ * M₁ : ℕ) : ℤ) := by push_cast; ring
      exact_mod_cast h2
    -- `|a + b₀| ≤ M₁ + B₀ * M₁`
    have hn : ((a : ℤ) + b₀).natAbs ≤ M₁ + B₀ * M₁ := by
      calc ((a : ℤ) + b₀).natAbs ≤ (a : ℤ).natAbs + b₀.natAbs := Int.natAbs_add_le _ _
        _ = a + b₀.natAbs := by rw [Int.natAbs_natCast]
        _ ≤ M₁ + B₀ * M₁ := by omega
    have hR : ((((a : ℤ) + b₀).natAbs : ℕ) : ℝ)
        ≤ (M₁ : ℝ) + (B₀ : ℝ) * (M₁ : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hn
      simpa using this
    have hR' : ((((a : ℤ) + b₀).natAbs : ℕ) : ℝ) * η
        ≤ ((M₁ : ℝ) + (B₀ : ℝ) * (M₁ : ℝ)) * η :=
      mul_le_mul_of_nonneg_right hR (le_of_lt hη0)
    have hreg' : ((M₁ : ℝ) + (B₀ : ℝ) * (M₁ : ℝ)) * η ≤ 1 := by nlinarith [hreg]
    exact le_trans hR' hreg'
  -- Sufficient: the level-2 bad set is contained in the level-1 bad set.
  apply Finset.card_le_card
  intro a ha
  simp only [badP, Finset.mem_filter] at ha ⊢
  refine ⟨ha.1, ?_⟩
  intro hconj
  exact ha.2 ⟨(fun i k _ => hgcd ha.1), (fun i => hconj.2 0)⟩

end Work.Peluse.Pel51
