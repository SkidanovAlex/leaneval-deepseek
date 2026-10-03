import Mathlib
import Submission.Work.Peluse.SwapE.Defs

namespace Work.Peluse.SwapE

open scoped BigOperators

/-! ## Elementary helpers for `MassAvgLeOne` -/

/-- `n⁻¹ * n ≤ 1` for a natural number, real-cast (with `0⁻¹ * 0 = 0`). -/
private lemma inv_mul_self_le_one (n : ℕ) : ((n : ℝ))⁻¹ * (n : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr h.ne')]

/-- Membership in the symmetric interval is a size condition: `x ∈ symIcc N ↔ x.natAbs ≤ N`. -/
private lemma mem_symIcc_natAbs {N : ℕ} {x : ℤ} :
    x ∈ Work.Peluse.symIcc N ↔ x.natAbs ≤ N := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : ((x.natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by
      rw [Int.natCast_natAbs]; exact abs_le.mpr ⟨h1, h2⟩
    exact_mod_cast h3
  · intro h
    have h3 : (|x| : ℤ) ≤ (N : ℤ) := by
      rw [← Int.natCast_natAbs]; exact_mod_cast h
    exact abs_le.mp h3

/-- The modulus is preserved by iterated conjugation. -/
private lemma norm_star_iterate (n : ℕ) (z : ℂ) : ‖(star^[n]) z‖ = ‖z‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', norm_star, ih]

/-- A cube term is a product of `2 ^ d` terms of modulus at most `1`, hence has modulus at most
`1`. -/
private lemma norm_cubeTerm_le {d : ℕ} {f : ℤ → ℂ} (hf : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (n h' : Fin d → ℤ) (x : ℤ) :
    ‖∏ ω : Fin d → Bool,
        (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift n h' ω))‖ ≤ 1 := by
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun ω _ => norm_nonneg _) (fun ω _ => ?_)
  rw [norm_star_iterate]
  exact hf _

/-- For fixed increments the sum over the lower corner `x` of the cube term is bounded by `|S|`:
the `ω = 0` corner is `x` itself, so the integrand is supported in `S`. -/
private lemma norm_tsum_cubeTerm_le {d : ℕ} {S : Finset ℤ} {f : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsupp : ∀ x : ℤ, x ∉ S → f x = 0) (n : Fin d → ℤ) :
    ‖∑' x : ℤ, ∏ ω : Fin d → Bool,
      (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift n (0 : Fin d → ℤ) ω))‖
      ≤ (S.card : ℝ) := by
  have hvanish : ∀ x : ℤ, x ∉ S → (∏ ω : Fin d → Bool,
      (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift n (0 : Fin d → ℤ) ω))) = 0 := by
    intro x hx
    refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin d => false)) ?_
    have hw : Work.Peluse.weight (fun _ : Fin d => false) = 0 := by simp [Work.Peluse.weight]
    have hc : Work.Peluse.cornerShift n (0 : Fin d → ℤ) (fun _ : Fin d => false) = 0 := by
      simp [Work.Peluse.cornerShift]
    rw [hw, hc, Function.iterate_zero_apply]
    simpa using hsupp x hx
  rw [tsum_eq_sum (s := S) hvanish]
  calc ‖∑ x ∈ S, ∏ ω : Fin d → Bool,
        (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift n (0 : Fin d → ℤ) ω))‖
      ≤ ∑ x ∈ S, ‖∏ ω : Fin d → Bool,
          (star^[Work.Peluse.weight ω])
            (f (x + Work.Peluse.cornerShift n (0 : Fin d → ℤ) ω))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x ∈ S, (1:ℝ) :=
        Finset.sum_le_sum (fun x _ => norm_cubeTerm_le hf n 0 x)
    _ = (S.card : ℝ) := by simp

/-- The cube mass of a `1`-bounded function supported in `symIcc N` has modulus at most `1`. -/
private lemma norm_boxMass_le {d N : ℕ} {f : ℤ → ℂ}
    (hsupp : SupportIn f N) (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (n : Fin d → ℤ) :
    ‖boxMass d (Work.Peluse.symIcc N) f n‖ ≤ 1 := by
  have hsuppS : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0 := fun x hx =>
    hsupp x (by rw [← not_le]; exact fun h => hx (mem_symIcc_natAbs.mpr h))
  unfold boxMass
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_tsum_cubeTerm_le hf hsuppS n)
    (inv_nonneg.mpr (Nat.cast_nonneg _))) (inv_mul_self_le_one _)

/-- `#([−2HM, 2HM]) = 4HM+1 = massBoxCard H M`. -/
private lemma card_factor_massBox (H M : ℕ) :
    (Finset.Icc (-(massHalf H M)) (massHalf H M)).card = massBoxCard H M := by
  rw [Int.card_Icc]
  unfold massHalf massBoxCard
  have h : 2 * ((H * M : ℕ) : ℤ) + 1 - -(2 * ((H * M : ℕ) : ℤ))
      = ((4 * H * M + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [h, Int.toNat_natCast]

/-- `#(massBox d H M) = (massBoxCard H M)^d`. -/
private lemma card_massBox (d H M : ℕ) : (massBox d H M).card = (massBoxCard H M) ^ d := by
  unfold massBox
  rw [Fintype.card_piFinset]
  simp only [card_factor_massBox]
  simp

/-- **`MassAvgLeOne`** — the cube mass is bounded by one, so its average over the slot box is at
most one.

Proof sketch.  `massBox d H M = piFinset (fun _ => Finset.Icc (-(2*H*M)) (2*H*M))`, so
`(massBox d H M).card = (4*H*M+1)^d = (massBoxCard H M)^d` (`Fintype.card_piFinset`,
`Int.card_Icc`).  In `boxMass d (symIcc N) f n = (S.card)⁻¹ * ∑' x, ∏ ω, …` the `ω = 0` factor is
`f x` (`weight 0 = 0`, `cornerShift n 0 0 = 0`), so the integrand is supported in
`symIcc N`, whence `‖∑' x, …‖ ≤ (symIcc N).card` (each factor has norm `≤ 1`); dividing by
`(S.card) = 2N+1` gives `‖boxMass … n‖ ≤ 1`.  Summing over the `(massBoxCard H M)^d` slot values
and dividing by the same number gives `massAvg ≤ 1`. -/
theorem massAvgLeOne : Work.Peluse.SwapE.MassAvgLeOne := by
  intro d H M N f hsupp hf
  have hnum : ∑ n ∈ massBox d H M, ‖boxMass d (Work.Peluse.symIcc N) f n‖
      ≤ (massBoxCard H M : ℝ) ^ d := by
    calc ∑ n ∈ massBox d H M, ‖boxMass d (Work.Peluse.symIcc N) f n‖
        ≤ ∑ _n ∈ massBox d H M, (1:ℝ) :=
          Finset.sum_le_sum (fun n _ => norm_boxMass_le hsupp hf n)
      _ = ((massBox d H M).card : ℝ) := by simp
      _ = ((massBoxCard H M) ^ d : ℕ) := by rw [card_massBox]
      _ = (massBoxCard H M : ℝ) ^ d := by push_cast; ring
  have hpos : (0:ℝ) < (massBoxCard H M : ℝ) := by
    unfold massBoxCard; positivity
  unfold massAvg
  rw [div_le_one (pow_pos hpos d)]
  exact hnum

end Work.Peluse.SwapE
