import Mathlib

/-!
# Finiteness of the `ℓ¹`-mass of a product kernel

If `K : ℤ → ℤ → ℂ` is `ℓ¹(ℤ²)` (i.e. `∑' p, ‖K p.1 p.2‖ < ∞`) and `κ, κ' : ℤ → ℂ` are absolutely
summable, then the `ENNReal`-valued `ℓ¹`-mass of the fourfold product family

  `w ↦ enorm (K w.1.1 w.1.2) * enorm (κ w.2.1) * enorm (κ' w.2.2)`

on `(ℤ × ℤ) × (ℤ × ℤ)` is finite (`≠ ⊤`).  This is the `ENNReal` companion of the real-valued
Young inequality `Work.KMTPlan.A6.tsum_norm_kernComp_le`, and it is what lets one use the
`ENNReal`-valued Fubini/interchange lemmas (`lintegral_tsum`, `tsum_comm`, ...) on such
product kernels without having to first produce a `Summable` statement in `ℝ`.

The proof is the elementary factorisation of the mass of a product family:

`∑' (p,q), ⟦F p⟧ * ⟦G q⟧ = (∑' p, ⟦F p⟧) * (∑' q, ⟦G q⟧)`

(`tsum_prod_mul`, the `ENNReal` form of `Summable.tsum_mul_tsum`), applied twice, together with
the fact that an absolutely summable complex sequence has finite `enorm`-mass
(`ENNReal.tsum_coe_ne_top_iff_summable`).
-/

namespace Work.KMTPlan.A6

/-- **Factorisation of a double `ENNReal`-sum with a product summand.** -/
lemma tsum_prod_mul (F G : ℤ × ℤ → ENNReal) :
    (∑' w : (ℤ × ℤ) × (ℤ × ℤ), F w.1 * G w.2) = (∑' p, F p) * (∑' q, G q) := by
  rw [ENNReal.tsum_prod (f := fun p q => F p * G q)]
  simp_rw [ENNReal.tsum_mul_left]
  exact ENNReal.tsum_mul_right

/-- **The `enorm`-mass of a product family on `ℤ × ℤ` factorises.** -/
lemma tsum_prod_enorm (κ κ' : ℤ → ℂ) :
    (∑' q : ℤ × ℤ, enorm (κ q.1) * enorm (κ' q.2))
      = (∑' i, enorm (κ i)) * (∑' j, enorm (κ' j)) := by
  rw [ENNReal.tsum_prod (f := fun (i : ℤ) (j : ℤ) => enorm (κ i) * enorm (κ' j))]
  simp_rw [ENNReal.tsum_mul_left]
  exact ENNReal.tsum_mul_right

/-- An absolutely summable complex sequence has finite `enorm`-mass. -/
lemma tsum_enorm_ne_top_of_summable {κ : ℤ → ℂ} (hκ : Summable κ) :
    (∑' i : ℤ, enorm (κ i)) ≠ ⊤ := by
  have hNN : Summable fun i : ℤ => ‖κ i‖₊ := NNReal.summable_coe.mp (by simpa using hκ.norm)
  simpa only [enorm_eq_nnnorm] using ENNReal.tsum_coe_ne_top_iff_summable.mpr hNN

/-- An `ℓ¹(ℤ²)` kernel has finite `enorm`-mass. -/
lemma tsum_enorm_prod_ne_top_of_summable {K : ℤ → ℤ → ℂ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) :
    (∑' p : ℤ × ℤ, enorm (K p.1 p.2)) ≠ ⊤ := by
  have hNN : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖₊ :=
    NNReal.summable_coe.mp (by simpa using hK)
  simpa only [enorm_eq_nnnorm] using ENNReal.tsum_coe_ne_top_iff_summable.mpr hNN

theorem enorm_prod_tsum_ne_top (K : ℤ → ℤ → ℂ) (κ κ' : ℤ → ℂ)
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hκ : Summable κ) (hκ' : Summable κ') :
    (∑' w : (ℤ × ℤ) × (ℤ × ℤ), enorm (K w.1.1 w.1.2) * enorm (κ w.2.1) * enorm (κ' w.2.2))
      ≠ ⊤ := by
  -- reassociate the summand so that it is `F w.1 * G w.2`
  have h1 : (fun w : (ℤ × ℤ) × (ℤ × ℤ) =>
        enorm (K w.1.1 w.1.2) * enorm (κ w.2.1) * enorm (κ' w.2.2))
      = fun w => enorm (K w.1.1 w.1.2) * (enorm (κ w.2.1) * enorm (κ' w.2.2)) := by
    funext w; rw [mul_assoc]
  rw [h1]
  -- factor the double sum into a product of two (finite) masses
  rw [tsum_prod_mul (F := fun p : ℤ × ℤ => enorm (K p.1 p.2))
        (G := fun q : ℤ × ℤ => enorm (κ q.1) * enorm (κ' q.2))]
  rw [tsum_prod_enorm]
  exact ENNReal.mul_ne_top (tsum_enorm_prod_ne_top_of_summable hK)
    (ENNReal.mul_ne_top (tsum_enorm_ne_top_of_summable hκ) (tsum_enorm_ne_top_of_summable hκ'))

end Work.KMTPlan.A6
