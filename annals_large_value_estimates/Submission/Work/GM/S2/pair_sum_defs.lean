import Mathlib
import Submission.Work.GM.S2.Defs

/-!
# Vocabulary for the `S₂` pair-sum bound (GM §6)

The pair sum of GM's proof of Proposition 6.1 is

`Σ_{t₁,t₂ ∈ W} ‖Σ_{m ≠ 0} ĥ_{t₁-t₂}(mN)‖²`,

and the reflection (Lemma 6.2, hypothesis `hrefl`) is applied to the positive half
`Σ_{m > 0}`; the negative half is handled by the identity
`ĥ_t(-ξ) = conj (ĥ_{-t}(ξ))`.

The reflected sum is approximated by the short Dirichlet polynomial
`Σ_{1 ≤ m ≤ ⌊Y⌋} m^{iσ}` with `Y ≍ (1+|t|) T^η / N`, and the weight that survives is
`‖ĝ₁(ξ)‖ (1+|2πξ|)^{1/2}` (the factor `(1+|t|)^{-1/2}` is taken out uniformly).
-/

open Complex Finset MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false

namespace Work.GM.S2

/-- The inner sum of the pair sum: `Σ'_{m ≠ 0} ĥ_t(mN)` (the subtype form used by the
challenge statement). -/
noncomputable def Sall (N : ℕ) (t : ℝ) : ℂ :=
  ∑' (m : {m : ℤ // m ≠ 0}), Submission.GM.hhat t (((m : ℤ) : ℝ) * (N : ℝ))

/-- The positive half `Σ'_{m > 0} ĥ_t(mN)`, written as `Σ'_{k : ℕ} ĥ_t((k+1)N)` so that
its partial sums are exactly the sums appearing in the reflection hypothesis `hrefl`. -/
noncomputable def Spos (N : ℕ) (t : ℝ) : ℂ :=
  ∑' (k : ℕ), Submission.GM.hhat t ((((k + 1 : ℕ)) : ℝ) * (N : ℝ))

/-- The truncated Dirichlet polynomial `Σ_{1 ≤ m ≤ ⌊Y⌋} m^{iσ}`. -/
noncomputable def PolySum (Y σ : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (Nat.floor Y), (m : ℂ) ^ (Complex.I * (σ : ℂ))

/-- The surviving weight of the reflected integral, `‖ĝ₁(ξ)‖ (1+|2πξ|)^{1/2}`. -/
noncomputable def gwt (ξ : ℝ) : ℝ := ‖ghat1 ξ‖ * (1 + |2 * Real.pi * ξ|) ^ (1 / 2 : ℝ)

/-- The dyadic level of `|t|`, namely `⌊log₂ |t|⌋` (and `0` at `t = 0`). -/
noncomputable def lev (t : ℝ) : ℕ := Nat.log 2 (Nat.floor |t|)

/-- The truncation length attached to the dyadic level `k`. -/
noncomputable def Ylev (N : ℕ) (η : ℝ) (k : ℕ) : ℝ :=
  max 1 (((1 : ℝ) + (2 : ℝ) ^ (k + 1)) * (Submission.LargeValues.M N) ^ η / (N : ℝ))

/-! ### The hypotheses of the pair-sum bound, as named `Prop`s (definitionally equal to
the corresponding hypotheses of the challenge statement). -/

/-- The fully processed Heath–Brown input `hhb` (a `1`-separated family and a general
Dirichlet polynomial of length `X ≤ N`, with the `|W|^{7/4}`, `|W|^{29/16}` exponents of
GM (6.4) with `k = 4`). -/
def HBFull : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (T X : ℝ), 1 ≤ T → T ≤ (N : ℝ) ^ 2 → 1 ≤ X → X ≤ (N : ℝ) →
    ∀ (R : ℕ) (t : Fin R → ℝ),
      (∀ i, t i ∈ Set.Icc 0 T) → (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
      (∀ (a : ℕ → ℂ), (∀ m, ‖a m‖ ≤ 1) → (∀ m : ℕ, X < (m : ℝ) → a m = 0) →
        (∑ i : Fin R, ∑ j : Fin R,
          ‖∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor X),
              a m * (m : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
        ≤ C * (N : ℝ) ^ δ * ((R : ℝ) ^ 2 * X + (R : ℝ) ^ ((7 : ℝ) / 4) * X ^ 2
            + (R : ℝ) ^ ((29 : ℝ) / 16) * T ^ ((1 : ℝ) / 8) * X))

/-- The reflection / approximate functional equation input `hrefl`. -/
def ReflHyp : Prop :=
  ∃ Cr : ℝ, 0 < Cr ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t Y : ℝ), 1 ≤ |t| → 1 ≤ Y →
    ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y), Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖
      ≤ Cr * ∫ ξ, ‖ghat1 ξ‖ * (1 + |t + 2 * Real.pi * ξ|) ^ (-(1 / 2 : ℝ)) *
          ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y),
            (m : ℂ) ^ (Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ))‖

/-- The decay hypothesis `hdec` (in `ξ`, all orders). -/
def DecHyp : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ξ : ℝ, ξ ≠ 0 →
    ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j

/-! ## The `N` used for the Heath–Brown input at a given dyadic level -/

/-- The `N`-parameter of the Heath–Brown bound at dyadic level `kk`: large enough that the
truncation length `Ylev N η kk` and the interval length `M N` both fit. -/
noncomputable def levN (N : ℕ) (η : ℝ) (Nhb kk : ℕ) : ℕ :=
  max (max (Nat.ceil (Ylev N η kk) + 1)
        (Nat.ceil (Real.sqrt (Submission.LargeValues.M N)) + 1))
    (max (Nhb + 1) 2)

lemma le_levN_Nhb (N : ℕ) (η : ℝ) (Nhb kk : ℕ) : Nhb ≤ levN N η Nhb kk := by
  unfold levN
  exact le_trans (Nat.le_succ Nhb) (le_trans (le_max_left _ _) (le_max_right _ _))

lemma Ylev_le_levN (N : ℕ) (η : ℝ) (Nhb kk : ℕ) : Ylev N η kk ≤ (levN N η Nhb kk : ℝ) := by
  have h : Nat.ceil (Ylev N η kk) + 1 ≤ levN N η Nhb kk := by
    unfold levN
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have := Nat.ceil_le.mp (Nat.le_of_succ_le h)
  calc Ylev N η kk ≤ (Nat.ceil (Ylev N η kk) : ℝ) := Nat.le_ceil _
    _ ≤ (levN N η Nhb kk : ℝ) := by exact_mod_cast Nat.le_of_succ_le h

lemma sqrt_M_le_levN (N : ℕ) (η : ℝ) (Nhb kk : ℕ) :
    Real.sqrt (Submission.LargeValues.M N) ≤ (levN N η Nhb kk : ℝ) := by
  have h : Nat.ceil (Real.sqrt (Submission.LargeValues.M N)) + 1 ≤ levN N η Nhb kk := by
    unfold levN
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  calc Real.sqrt (Submission.LargeValues.M N)
      ≤ (Nat.ceil (Real.sqrt (Submission.LargeValues.M N)) : ℝ) := Nat.le_ceil _
    _ ≤ (levN N η Nhb kk : ℝ) := by exact_mod_cast Nat.le_of_succ_le h

lemma M_le_levN_sq (N : ℕ) (η : ℝ) (Nhb kk : ℕ) :
    Submission.LargeValues.M N ≤ (levN N η Nhb kk : ℝ) ^ 2 := by
  have h := sqrt_M_le_levN N η Nhb kk
  have h0 : (0:ℝ) ≤ (levN N η Nhb kk : ℝ) := Nat.cast_nonneg _
  calc Submission.LargeValues.M N = (Real.sqrt (Submission.LargeValues.M N)) ^ 2 :=
        (Real.sq_sqrt (by rw [Submission.LargeValues.M]; exact Real.rpow_nonneg (Nat.cast_nonneg N) _)).symm
    _ ≤ (levN N η Nhb kk : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

lemma levN_pos (N : ℕ) (η : ℝ) (Nhb kk : ℕ) : 1 ≤ levN N η Nhb kk := by
  unfold levN
  exact le_trans (by norm_num : 1 ≤ 2) (le_trans (le_max_right _ _) (le_max_right _ _))

/-! ## The Dirichlet polynomial `PolySum`, continuity and size -/

lemma card_Icc_one_le (n : ℕ) : (Finset.Icc 1 n).card ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · rw [Nat.card_Icc]; omega

lemma continuous_PolySum (Y : ℝ) : Continuous fun σ : ℝ => PolySum Y σ := by
  unfold PolySum
  refine continuous_finsetSum _ (fun m hm => ?_)
  refine Continuous.const_cpow (continuous_const.mul Complex.continuous_ofReal) (Or.inl ?_)
  exact Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hm).1; omega)

lemma norm_PolySum_le_floor (Y σ : ℝ) : ‖PolySum Y σ‖ ≤ (⌊Y⌋₊ : ℝ) := by
  unfold PolySum
  calc ‖∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, (m : ℂ) ^ (Complex.I * (σ : ℂ))‖
      ≤ ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, ‖(m : ℂ) ^ (Complex.I * (σ : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
        have hcast : (m : ℂ) = ((m : ℝ) : ℂ) := by rw [Complex.ofReal_natCast]
        rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
        simp
    _ = ((Finset.Icc 1 ⌊Y⌋₊).card : ℝ) := by simp
    _ ≤ (⌊Y⌋₊ : ℝ) := by exact_mod_cast card_Icc_one_le ⌊Y⌋₊

lemma norm_PolySum_le {Y : ℝ} (hY : 0 ≤ Y) (σ : ℝ) : ‖PolySum Y σ‖ ≤ Y :=
  le_trans (norm_PolySum_le_floor Y σ) (Nat.floor_le hY)

/-- The integrand of the reflected pair sum is integrable. -/
lemma integrable_gwt_poly (Y c sgn : ℝ) (hgwt : Integrable gwt) :
    Integrable (fun ξ : ℝ => gwt ξ * ‖PolySum Y (sgn * c + 2 * Real.pi * ξ)‖ ^ 2) := by
  have hcont : Continuous fun ξ : ℝ => ‖PolySum Y (sgn * c + 2 * Real.pi * ξ)‖ ^ 2 :=
    ((continuous_PolySum Y).comp (continuous_const.add (continuous_const.mul continuous_id))).norm.pow 2
  have hbdd : ∀ ξ : ℝ, ‖(‖PolySum Y (sgn * c + 2 * Real.pi * ξ)‖ ^ 2 : ℝ)‖ ≤ (⌊Y⌋₊ : ℝ) ^ 2 := by
    intro ξ
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_PolySum_le_floor Y _) 2
  exact (hgwt.bdd_mul (c := (⌊Y⌋₊ : ℝ) ^ 2) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall hbdd)).congr (Filter.Eventually.of_forall (fun ξ => by ring))

/-- The sum over pairs of the `ξ`-integrals is the integral of the sum of the
(truncated) Dirichlet polynomials. -/
lemma sum_integral_gwt_poly (F : Finset (ℝ × ℝ)) (Y sgn : ℝ) (hgwt : Integrable gwt) :
    (∑ p ∈ F, ∫ ξ, gwt ξ * ‖PolySum Y (sgn * (p.1 - p.2) + 2 * Real.pi * ξ)‖ ^ 2)
      = ∫ ξ, gwt ξ * ∑ p ∈ F, ‖PolySum Y (sgn * (p.1 - p.2) + 2 * Real.pi * ξ)‖ ^ 2 := by
  rw [← integral_finsetSum]
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
    change (∑ i ∈ F, gwt ξ * ‖PolySum Y (sgn * (i.1 - i.2) + 2 * Real.pi * ξ)‖ ^ 2)
      = gwt ξ * ∑ p ∈ F, ‖PolySum Y (sgn * (p.1 - p.2) + 2 * Real.pi * ξ)‖ ^ 2
    rw [Finset.mul_sum]
  · intro p hp
    exact integrable_gwt_poly Y (p.1 - p.2) sgn hgwt



end Work.GM.S2
