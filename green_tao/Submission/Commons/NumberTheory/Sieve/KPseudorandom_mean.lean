import Mathlib

namespace Commons.NumberTheory.Sieve

/-- Interpretation of a rational coefficient in `ZMod p` (meaningful when its denominator is
less than `p`). -/
def qmod (p : ℕ) [Fact p.Prime] (q : ℚ) : ZMod p := (q.num : ZMod p) / (q.den : ZMod p)

/-- A rational number whose numerator and denominator are bounded by `L₀`. -/
def IsSmallRat (L₀ : ℕ) (q : ℚ) : Prop := q.num.natAbs ≤ L₀ ∧ q.den ≤ L₀

/-- A nonzero tuple of rationals. -/
def NonzeroTuple {t : ℕ} (L : Fin t → ℚ) : Prop := ∃ j, L j ≠ 0

/-- Two tuples of rationals are not proportional. -/
def NotProp {t : ℕ} (L L' : Fin t → ℚ) : Prop := ¬ ∃ lam : ℚ, ∀ j, L' j = lam * L j

/-- The linear form `x ↦ ∑ⱼ Lⱼ xⱼ + b` on `(ZMod p)^t`. -/
def linForm (p : ℕ) [Fact p.Prime] {t : ℕ} (L : Fin t → ℚ) (b : ZMod p)
    (x : Fin t → ZMod p) : ZMod p :=
  (∑ j, qmod p (L j) * x j) + b

/-- **Green–Tao Definition 3.1** (linear forms condition) with error `ε`. -/
def LinFormsCond (p : ℕ) [Fact p.Prime] (ν : ZMod p → ℝ) (m₀ t₀ L₀ : ℕ) (ε : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], 1 ≤ Fintype.card ι → Fintype.card ι ≤ m₀ →
  ∀ (t : ℕ), 1 ≤ t → t ≤ t₀ →
  ∀ (L : ι → Fin t → ℚ), (∀ i j, IsSmallRat L₀ (L i j)) →
    (∀ i, NonzeroTuple (L i)) → (∀ i i', i ≠ i' → NotProp (L i) (L i')) →
    ∀ b : ι → ZMod p,
      |((Fintype.card (Fin t → ZMod p) : ℝ))⁻¹ *
          ∑ x : Fin t → ZMod p, ∏ i, ν (linForm p (L i) (b i) x) - 1| ≤ ε

/-- **Green–Tao Definition 3.2** (correlation condition) with moment bounds `C`. -/
def CorrCond (p : ℕ) [Fact p.Prime] (ν : ZMod p → ℝ) (m₀ : ℕ) (C : ℕ → ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 < m → m ≤ m₀ → ∃ τ : ZMod p → ℝ,
    (∀ x, 0 ≤ τ x) ∧
    (∀ q : ℕ, 1 ≤ q → (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, (τ x) ^ q ≤ C m q) ∧
    ∀ h : Fin m → ZMod p,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, ∏ i, ν (x + h i)
        ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), τ (h i - h j)

/-- **Green–Tao Definition 3.3**: `ν` is `k`-pseudorandom. -/
def KPseudorandom (p : ℕ) [Fact p.Prime] (k : ℕ) (ν : ZMod p → ℝ) (C : ℕ → ℕ → ℝ)
    (ε : ℝ) : Prop :=
  LinFormsCond p ν (k * 2 ^ (k - 1)) (3 * k - 4) k ε ∧ CorrCond p ν (2 ^ (k - 1)) C

/-- The measure condition `𝔼 ν = 1 + O(ε)`, i.e. the `m = 1, t = 1` case of the linear forms
condition.  This is the basic sanity property of a `k`-pseudorandom measure used throughout
Green–Tao §7. -/
theorem KPseudorandom_mean {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 2 ≤ k) {ν : ZMod p → ℝ}
    {C : ℕ → ℕ → ℝ} {ε : ℝ} (h : KPseudorandom p k ν C ε) :
    |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x : ZMod p, ν x - 1| ≤ ε := by
  have hLin := h.1
  have hm : 1 ≤ k * 2 ^ (k - 1) := by
    have : 0 < k * 2 ^ (k - 1) := Nat.mul_pos (by omega) (by positivity)
    omega
  have ht : 1 ≤ 3 * k - 4 := by omega
  let L : Fin 1 → Fin 1 → ℚ := fun _ _ => 1
  let b : Fin 1 → ZMod p := fun _ => 0
  have hmain := hLin (Fin 1) (by simp) (by simpa using hm) 1 le_rfl ht L
    (by intro i j
        dsimp only [L]
        simp only [IsSmallRat, Rat.num_one, Rat.den_one, Int.natAbs_one]
        omega)
    (by intro i; exact ⟨0, by dsimp only [L]; norm_num⟩)
    (by intro i i' hne; exact absurd (Subsingleton.elim i i') hne)
    b
  have hcard : Fintype.card (Fin 1 → ZMod p) = Fintype.card (ZMod p) := by
    rw [Fintype.card_fun, Fintype.card_fin, pow_one]
  have hsum : (∑ x : Fin 1 → ZMod p,
        ∏ i : Fin 1, ν (linForm p (L i) (b i) x)) = ∑ y : ZMod p, ν y := by
    dsimp only [L, b]
    simp only [Fin.prod_univ_one, linForm, Fin.sum_univ_one, qmod, Rat.num_one,
      Rat.den_one, Int.cast_one, Nat.cast_one, div_one, one_mul, add_zero]
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod p)) _ _ (fun x => rfl)
  rw [hcard, hsum] at hmain
  exact hmain

end Commons.NumberTheory.Sieve
