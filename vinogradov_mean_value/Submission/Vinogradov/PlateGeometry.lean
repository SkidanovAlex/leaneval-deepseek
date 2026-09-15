/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymBilinear

/-!
# The geometry of the plates: the Taylor expansion and the scaled containment

GLYZ's uncertainty principle (Lemma 3.3) is applied to the sum `F_J = ∑_{K ⊆ J} f_K` of the
fine pieces of a coarse interval `J`.  Its Fourier support is the union of the fine plates
`𝒰_K`, and the bump in the definition of the asymmetric constant is the one adapted to a
*constant enlargement* of the **coarse** plate `𝒰_J`.  This module supplies that geometric
input:

* `gammaVec_add_eq` — the Taylor expansion of the moment curve,
  `γ(t + Δ) = γ(t) + A_{1,t}(Δ, Δ², …, Δᵏ)`;
* `affVecDual_zero_apply` — the companion identity `A_{δ,0}(x)_l = x_l δ^{l+1}`, which is what
  makes the enlarged set a plate again;
* **`plate_add_subset`** — `𝒰_{t+Δ}(δ) ⊆ 𝒰_t(4δm)` whenever `|Δ| ≤ δm` and `δ ≤ δm`.

The last statement is the input of `IsFourierRep.uncertainty` (GLYZ Lemma 3.3) at the coarse
scale: the sum of the fine pieces of a coarse interval has Fourier support in the union of the
fine plates, which by `plate_add_subset` lies in the `4·plateHalf m`-plate of the centre of the
coarse interval.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The Taylor expansion of the moment curve -/

/-- The displacement vector `(Δ, Δ², …, Δᵏ)` of the Taylor expansion. -/
def shiftVec (k : ℕ) (Δ : ℝ) : E k :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun i => Δ ^ (i.val + 1))

/-- Defining equation of `shiftVec`. -/
lemma shiftVec_apply (k : ℕ) (Δ : ℝ) (i : Fin k) : shiftVec k Δ i = Δ ^ (i.val + 1) := rfl

/-- **The Taylor expansion of the moment curve**: `γ(t + Δ) = γ(t) + A_{1,t}(Δ, Δ², …, Δᵏ)`.
Equivalently, `(t+Δ)^{j+1} = t^{j+1} + ∑_i Δ^{i+1} (j+1 choose i+1) t^{j-i}`. -/
theorem gammaVec_add_eq (k : ℕ) (t Δ : ℝ) :
    gammaVec k (t + Δ) = gammaVec k t + affVecDual k 1 t (shiftVec k Δ) := by
  ext l
  rw [PiLp.add_apply, gammaVec_apply, gammaVec_apply, affVecDual_apply]
  simp only [shiftVec_apply, one_pow, mul_one]
  have hbin : (t + Δ) ^ (l.val + 1)
      = t ^ (l.val + 1) + ∑ r ∈ Finset.range (l.val + 1),
          Δ ^ (r + 1) * ((l.val + 1).choose (r + 1) : ℝ) * t ^ (l.val - r) := by
    have hshift : (∑ k ∈ Finset.range (l.val + 1),
          Δ ^ (k + 1) * t ^ (l.val + 1 - (k + 1)) * (((l.val + 1).choose (k + 1) : ℕ) : ℝ))
        = ∑ r ∈ Finset.range (l.val + 1),
          Δ ^ (r + 1) * ((l.val + 1).choose (r + 1) : ℝ) * t ^ (l.val - r) :=
      Finset.sum_congr rfl fun r hr => by
        rw [show l.val + 1 - (r + 1) = l.val - r from by
          simp only [Finset.mem_range] at hr
          omega]
        ring
    rw [add_comm t Δ, add_pow, Finset.sum_range_succ']
    simp only [pow_zero, tsub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul]
    rw [hshift]
    exact add_comm _ _
  have hsum1 : (∑ x : Fin k,
        Δ ^ (x.val + 1) * ((l.val + 1).choose (x.val + 1) : ℝ) * t ^ (l.val - x.val))
      = ∑ x ∈ (Finset.univ.filter fun x : Fin k => x.val ≤ l.val),
        Δ ^ (x.val + 1) * ((l.val + 1).choose (x.val + 1) : ℝ) * t ^ (l.val - x.val) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x _ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    ring
  have hsum2 : (∑ x ∈ (Finset.univ.filter fun x : Fin k => x.val ≤ l.val),
        Δ ^ (x.val + 1) * ((l.val + 1).choose (x.val + 1) : ℝ) * t ^ (l.val - x.val))
      = ∑ r ∈ Finset.range (l.val + 1),
          Δ ^ (r + 1) * ((l.val + 1).choose (r + 1) : ℝ) * t ^ (l.val - r) := by
    refine Finset.sum_bij (fun (x : Fin k) _ => x.val) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_range]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      omega
    · intro x₁ _ x₂ _ heq
      exact Fin.ext heq
    · intro r hr
      simp only [Finset.mem_range] at hr
      exact ⟨⟨r, by omega⟩, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega, rfl⟩
    · intro x _; rfl
  rw [hbin, (hsum2.symm.trans hsum1.symm)]

/-! ## 2. The action of `affVecDual` at the origin -/

/-- `A_{δ,0}(x)_l = x_l δ^{l+1}`: the affine map at the parameter `0` acts diagonally. -/
lemma affVecDual_zero_apply (k : ℕ) (δ : ℝ) (x : E k) (l : Fin k) :
    affVecDual k δ 0 x l = x l * δ ^ (l.val + 1) := by
  rw [affVecDual_apply]
  refine (Finset.sum_eq_single l (fun j _ hj => ?_) (fun hl => absurd (Finset.mem_univ l) hl)).trans ?_
  · by_cases h : j.val + 1 ≤ l.val + 1
    · rw [zero_pow (by omega : l.val - j.val ≠ 0)]
      simp
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
      simp
  · simp

/-! ## 3. The coordinate bound for `A_{δ,Δ}` -/

/-- The binomial coefficient times the factorial is bounded by the factorial: this is
`(i+1)!(l+1 choose i+1) = (l+1)!/(l-i)! ≤ (l+1)!`. -/
lemma choose_mul_factorial_le_factorial {i l : ℕ} (h : i ≤ l) :
    (i + 1).factorial * ((l + 1).choose (i + 1)) ≤ (l + 1).factorial := by
  have hmul := Nat.choose_mul_factorial_mul_factorial (show i + 1 ≤ l + 1 by omega)
  rw [show l + 1 - (i + 1) = l - i from by omega] at hmul
  have hpos : 1 ≤ (l - i).factorial := Nat.factorial_pos _
  calc (i + 1).factorial * ((l + 1).choose (i + 1))
      = (i + 1).factorial * ((l + 1).choose (i + 1)) * 1 := (mul_one _).symm
    _ ≤ (i + 1).factorial * ((l + 1).choose (i + 1)) * (l - i).factorial :=
        Nat.mul_le_mul_left _ hpos
    _ = (l + 1).choose (i + 1) * (i + 1).factorial * (l - i).factorial := by ring
    _ = (l + 1).factorial := hmul

/-- The number of `i : Fin k` with `i ≤ l` is `l + 1`. -/
lemma card_filter_fin_le (k : ℕ) (l : Fin k) :
    (Finset.univ.filter (fun i : Fin k => i.val ≤ l.val)).card = l.val + 1 := by
  rw [← Finset.card_range (l.val + 1)]
  refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    omega
  · intro i₁ _ i₂ _ heq
    exact Fin.ext heq
  · intro n hn
    simp only [Finset.mem_range] at hn
    exact ⟨⟨n, by omega⟩, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega, rfl⟩

/-- **The coordinate bound for the Taylor displacement.**  If `|Δ| ≤ δm`, `0 ≤ δ ≤ δm` and the
coefficients `y_i` satisfy `|y_i| ≤ (i+1)!`, then the `l`-th coordinate of `A_{δ,Δ}(y)` is at
most `(l+1)(l+1)!δm^{l+1}`. -/
lemma abs_affVecDual_le {k : ℕ} {δ δm Δ : ℝ} (hδ : 0 ≤ δ) (hδδ : δ ≤ δm)
    (hΔ : |Δ| ≤ δm) {y : E k} (hy : ∀ i : Fin k, |y i| ≤ ((i.val + 1).factorial : ℝ))
    (l : Fin k) :
    |affVecDual k δ Δ y l|
      ≤ ((l.val + 1).factorial : ℝ) * ((l.val : ℝ) + 1) * δm ^ (l.val + 1) := by
  have hδm : 0 ≤ δm := le_trans hδ hδδ
  rw [affVecDual_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i : Fin k, i.val ≤ l.val →
      |y i * ((l.val + 1).choose (i.val + 1) : ℝ) * δ ^ (i.val + 1) * Δ ^ (l.val - i.val)|
        ≤ ((l.val + 1).factorial : ℝ) * δm ^ (l.val + 1) := by
    intro i hi
    have habs : |y i * ((l.val + 1).choose (i.val + 1) : ℝ) * δ ^ (i.val + 1)
          * Δ ^ (l.val - i.val)|
        = |y i| * ((l.val + 1).choose (i.val + 1) : ℝ) * δ ^ (i.val + 1)
          * |Δ| ^ (l.val - i.val) := by
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ((l.val + 1).choose (i.val + 1) : ℝ)),
        abs_of_nonneg (pow_nonneg hδ (i.val + 1)), abs_pow]
    rw [habs]
    have hcf : ((i.val + 1).factorial : ℝ) * ((l.val + 1).choose (i.val + 1) : ℝ)
        ≤ ((l.val + 1).factorial : ℝ) := by
      exact_mod_cast choose_mul_factorial_le_factorial hi
    have hp : δm ^ (i.val + 1) * δm ^ (l.val - i.val) = δm ^ (l.val + 1) := by
      rw [← pow_add, show i.val + 1 + (l.val - i.val) = l.val + 1 from by omega]
    calc |y i| * ((l.val + 1).choose (i.val + 1) : ℝ) * δ ^ (i.val + 1) * |Δ| ^ (l.val - i.val)
        ≤ ((i.val + 1).factorial : ℝ) * ((l.val + 1).choose (i.val + 1) : ℝ)
            * δm ^ (i.val + 1) * δm ^ (l.val - i.val) := by
          have h1 : |y i| ≤ ((i.val + 1).factorial : ℝ) := hy i
          have h2 : δ ^ (i.val + 1) ≤ δm ^ (i.val + 1) := pow_le_pow_left₀ hδ hδδ _
          have h3 : |Δ| ^ (l.val - i.val) ≤ δm ^ (l.val - i.val) :=
            pow_le_pow_left₀ (abs_nonneg _) hΔ _
          gcongr
      _ = ((i.val + 1).factorial : ℝ) * ((l.val + 1).choose (i.val + 1) : ℝ)
            * (δm ^ (i.val + 1) * δm ^ (l.val - i.val)) := by ring
      _ = ((i.val + 1).factorial : ℝ) * ((l.val + 1).choose (i.val + 1) : ℝ)
            * δm ^ (l.val + 1) := by rw [hp]
      _ ≤ ((l.val + 1).factorial : ℝ) * δm ^ (l.val + 1) := by
          have hnn : 0 ≤ δm ^ (l.val + 1) := pow_nonneg hδm _
          have h1 : (0:ℝ) ≤ ((l.val + 1).choose (i.val + 1) : ℝ) := by positivity
          nlinarith [hcf, hnn, h1]
  have hsub : ∑ i : Fin k,
        |y i * ((l.val + 1).choose (i.val + 1) : ℝ) * δ ^ (i.val + 1) * Δ ^ (l.val - i.val)|
      = ∑ i ∈ (Finset.univ.filter fun i : Fin k => i.val ≤ l.val),
        |y i * ((l.val + 1).choose (i.val + 1) : ℝ) * δ ^ (i.val + 1) * Δ ^ (l.val - i.val)| := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    simp
  rw [hsub]
  calc ∑ i ∈ (Finset.univ.filter fun i : Fin k => i.val ≤ l.val),
        |y i * ((l.val + 1).choose (i.val + 1) : ℝ) * δ ^ (i.val + 1) * Δ ^ (l.val - i.val)|
      ≤ ∑ _i ∈ (Finset.univ.filter fun i : Fin k => i.val ≤ l.val),
          ((l.val + 1).factorial : ℝ) * δm ^ (l.val + 1) :=
        Finset.sum_le_sum fun i hi => hterm i (Finset.mem_filter.mp hi).2
    _ = (((l.val : ℝ) + 1)) * (((l.val + 1).factorial : ℝ) * δm ^ (l.val + 1)) := by
        rw [Finset.sum_const, card_filter_fin_le k l, nsmul_eq_mul]
        rw [show (((l.val + 1 : ℕ)) : ℝ) = (l.val : ℝ) + 1 from by push_cast; ring]
    _ = ((l.val + 1).factorial : ℝ) * ((l.val : ℝ) + 1) * δm ^ (l.val + 1) := by ring

/-! ## 4. The scaled containment -/

/-- **The scaled containment.**  The plate of width `δ` centred at `t + Δ` is contained in the
plate of width `4δm` centred at `t`, as soon as `|Δ| ≤ δm` and `0 ≤ δ ≤ δm`.  This is the
constant enlargement of the coarse plate that carries the union of the plates of the fine
pieces. -/
theorem plate_add_subset {k : ℕ} {δ δm Δ t : ℝ} (hδm : 0 < δm) (hδ : 0 ≤ δ) (hδδ : δ ≤ δm)
    (hΔ : |Δ| ≤ δm) : plate k δ (t + Δ) ⊆ plate k (4 * δm) t := by
  rintro ξ ⟨y, hy, rfl⟩
  rw [affMap_apply]
  set w : E k := shiftVec k Δ with hw
  set Y : E k := w + affVecDual k δ Δ y with hY
  set y' : E k := (WithLp.equiv 2 (Fin k → ℝ)).symm
    (fun l => Y l / (4 * δm) ^ (l.val + 1)) with hy'
  have hpow : ∀ l : Fin k, (0:ℝ) < (4 * δm) ^ (l.val + 1) := fun l =>
    pow_pos (by linarith) _
  have hy'box : y' ∈ plateBox k := by
    intro l
    have hYl : |Y l| ≤ ((l.val + 1).factorial : ℝ) * (4 * δm) ^ (l.val + 1) := by
      have h1 : |w l| ≤ δm ^ (l.val + 1) := by
        rw [hw, shiftVec_apply, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hΔ _
      have h2 := abs_affVecDual_le (k := k) (δ := δ) (δm := δm) (Δ := Δ) hδ hδδ hΔ hy l
      have h3 : w l + affVecDual k δ Δ y l = Y l := by rw [hY]; rfl
      have hfac : (1:ℝ) ≤ ((l.val + 1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_pos (l.val + 1)
      have hP : 0 ≤ δm ^ (l.val + 1) := pow_nonneg hδm.le _
      have hlt : (l.val : ℝ) + 2 ≤ (4:ℝ) ^ (l.val + 1) := by
        have h2 : l.val + 1 < 2 ^ (l.val + 1) := Nat.lt_two_pow_self
        have h3 : 2 ^ (l.val + 1) ≤ 4 ^ (l.val + 1) :=
          Nat.pow_le_pow_left (by norm_num : (2:ℕ) ≤ 4) _
        have hnat : l.val + 2 ≤ 4 ^ (l.val + 1) := by omega
        exact_mod_cast hnat
      calc |Y l| = |w l + affVecDual k δ Δ y l| := by rw [h3]
        _ ≤ |w l| + |affVecDual k δ Δ y l| := abs_add_le _ _
        _ ≤ δm ^ (l.val + 1)
              + ((l.val + 1).factorial : ℝ) * ((l.val : ℝ) + 1) * δm ^ (l.val + 1) :=
            add_le_add h1 h2
        _ ≤ ((l.val + 1).factorial : ℝ) * (4 * δm) ^ (l.val + 1) := by
            rw [mul_pow]
            have hstep : 1 + ((l.val + 1).factorial : ℝ) * ((l.val : ℝ) + 1)
                ≤ ((l.val + 1).factorial : ℝ) * (4:ℝ) ^ (l.val + 1) :=
              by nlinarith [hfac, hlt]
            have := mul_le_mul_of_nonneg_right hstep hP
            linarith [this]
    rw [hy']
    change |Y l / (4 * δm) ^ (l.val + 1)| ≤ ((l.val + 1).factorial : ℝ)
    rw [abs_div, abs_of_pos (hpow l), div_le_iff₀ (hpow l)]
    exact hYl
  refine ⟨y', hy'box, ?_⟩
  have hcomp : affVecDual k δ (t + Δ) y = affVecDual k 1 t (affVecDual k δ Δ y) := by
    have h : affVecDual k 1 t (affVecDual k δ Δ y) = affVecDual k δ (Δ + t) y := by
      simpa only [one_mul] using affVecDual_comp k 1 t δ Δ y
    rw [add_comm] at h
    exact h.symm
  have hz : affVecDual k (4 * δm) 0 y' = Y := by
    ext l
    rw [hy', affVecDual_zero_apply]
    change Y l / (4 * δm) ^ (l.val + 1) * (4 * δm) ^ (l.val + 1) = Y l
    exact div_mul_cancel₀ _ (hpow l).ne'
  have hkey : affVecDual k (4 * δm) t y' = affVecDual k 1 t Y := by
    have h : affVecDual k 1 t (affVecDual k (4 * δm) 0 y') = affVecDual k (4 * δm) t y' := by
      simpa only [one_mul, zero_add] using affVecDual_comp k 1 t (4 * δm) 0 y'
    rw [← h, hz]
  rw [affMap_apply, gammaVec_add_eq k t Δ, hcomp, hkey, add_assoc, ← affVecDual_add, ← hY]


/-! ## 5. The dyadic corollary -/

/-- The distance between the centre of a fine piece and the centre of the coarse block that
contains it is at most `2^{-m}`, twice the half-width of the block. -/
lemma abs_pieceCenter_sub_le {N m : ℕ} (hm : m ≤ N) (q : Fin (2 ^ m)) (j : Fin (2 ^ N))
    (hj : (j : ℕ) / 2 ^ (N - m) = (q : ℕ)) :
    |pieceCenter (2 ^ N) j - pieceCenter (2 ^ m) q| ≤ 1 / (2 : ℝ) ^ m := by
  have hM : 0 < 2 ^ (N - m) := pow_pos (by norm_num) _
  have hdec : (j : ℕ) = (q : ℕ) * 2 ^ (N - m) + (j : ℕ) % 2 ^ (N - m) := by
    have h := Nat.div_add_mod (j : ℕ) (2 ^ (N - m))
    rw [hj, Nat.mul_comm] at h
    exact h.symm
  have hmod : (j : ℕ) % 2 ^ (N - m) < 2 ^ (N - m) := Nat.mod_lt _ hM
  have hrM : (((j : ℕ) % 2 ^ (N - m) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N - m) - 1 := by
    have h1 : (j : ℕ) % 2 ^ (N - m) ≤ 2 ^ (N - m) - 1 := Nat.le_sub_one_of_lt hmod
    have h2 : ((2 ^ (N - m) - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (N - m) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow)]
      push_cast
      ring
    rw [← h2]
    exact_mod_cast h1
  have hjc : ((j : ℕ) : ℝ) = ((q : ℕ) : ℝ) * (2 : ℝ) ^ (N - m)
      + (((j : ℕ) % 2 ^ (N - m) : ℕ) : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hdec
    push_cast at h
    exact h
  have hcastN : (((2 : ℕ) ^ N : ℕ) : ℝ) = (2 : ℝ) ^ (N - m) * (2 : ℝ) ^ m := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_add, Nat.sub_add_cancel hm]
  have hcastm : (((2 : ℕ) ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  have hdiff : (((j : ℕ) : ℝ) + 1/2) / (((2 : ℕ) ^ N : ℕ) : ℝ)
        - (((q : ℕ) : ℝ) + 1/2) / (((2 : ℕ) ^ m : ℕ) : ℝ)
      = ((((j : ℕ) % 2 ^ (N - m) : ℕ) : ℝ) - ((2 : ℝ) ^ (N - m) - 1) / 2)
        / ((2 : ℝ) ^ (N - m) * (2 : ℝ) ^ m) := by
    rw [hcastN, hcastm, hjc]
    field_simp
    ring
  have hr0 : (0:ℝ) ≤ (((j : ℕ) % 2 ^ (N - m) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [pieceCenter, pieceCenter, hdiff]
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (2:ℝ) ^ (N - m) * (2:ℝ) ^ m),
    div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ) ^ (N - m) * (2:ℝ) ^ m)]
  have hmul : (1 / (2:ℝ) ^ m) * ((2:ℝ) ^ (N - m) * (2:ℝ) ^ m) = (2:ℝ) ^ (N - m) := by
    field_simp
  rw [hmul, abs_le]
  constructor <;> nlinarith [hr0, hrM]

/-- **The plates of the fine pieces inside a coarse block.**  Every fine piece of a level-`m`
dyadic block has its plate inside the `8·plateHalf m`-plate of the centre of the block.  This
is the constant enlargement of the coarse plate that carries the union of the fine plates. -/
theorem piecePlate_subset_plate_scaled {k N m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hmN : m ≤ N)
    (q : Fin (2 ^ m)) (j : Fin (2 ^ N)) (hj : (j : ℕ) / 2 ^ (N - m) = (q : ℕ)) :
    piecePlate k (2 ^ N) j ⊆ plate k (8 * plateHalf m) (pieceCenter (2 ^ m) q) := by
  have hδm : (0:ℝ) < 2 * plateHalf m := by
    rw [plateHalf]
    positivity
  have hδ : (0:ℝ) ≤ 1 / (2 * (((2 : ℕ) ^ N : ℕ) : ℝ)) := by positivity
  have h2ph : 2 * plateHalf m = 1 / (2:ℝ) ^ m := by
    rw [plateHalf, pow_succ]
    field_simp
  have hδδ : 1 / (2 * (((2 : ℕ) ^ N : ℕ) : ℝ)) ≤ 2 * plateHalf m := by
    rw [h2ph, div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    have h : (2:ℝ) ^ m ≤ (2:ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hmN
    nlinarith [h, pow_pos (by norm_num : (0:ℝ) < 2) N]
  have hΔ : |pieceCenter (2 ^ N) j - pieceCenter (2 ^ m) q| ≤ 2 * plateHalf m := by
    rw [h2ph]
    exact abs_pieceCenter_sub_le hmN q j hj
  have hkey := plate_add_subset (k := k)
    (δ := 1 / (2 * (((2 : ℕ) ^ N : ℕ) : ℝ))) (δm := 2 * plateHalf m)
    (Δ := pieceCenter (2 ^ N) j - pieceCenter (2 ^ m) q) (t := pieceCenter (2 ^ m) q)
    hδm hδ hδδ hΔ
  have ht : pieceCenter (2 ^ m) q + (pieceCenter (2 ^ N) j - pieceCenter (2 ^ m) q)
      = pieceCenter (2 ^ N) j := by ring
  rw [ht] at hkey
  have h4 : (4:ℝ) * (2 * plateHalf m) = 8 * plateHalf m := by ring
  rw [h4] at hkey
  simpa only [piecePlate] using hkey

/-! ## 6. The anisotropic diagonal scaling and the comparison of the plate bumps -/

/-- The anisotropic diagonal scaling `x ↦ (c^{i+1} x_i)` of `E k`. -/
noncomputable def diagPow (k : ℕ) (c : ℝ) : E k →ₗ[ℝ] E k :=
  (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.toLinearMap.comp
    ((LinearMap.pi fun i : Fin k =>
        (c ^ (i.val + 1) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) ∘ₗ LinearMap.proj i).comp
      (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap)

lemma diagPow_apply (k : ℕ) (c : ℝ) (x : E k) (i : Fin k) :
    diagPow k c x i = c ^ (i.val + 1) * x i := by
  rw [diagPow]
  simp only [LinearMap.comp_apply]
  rfl

/-- **The plate gauge map scales by the anisotropic diagonal.** -/
lemma plateGaugeLin_scale (k : ℕ) (c₀ δ t : ℝ) :
    plateGaugeLin k (c₀ * δ) t = (diagPow k c₀).comp (plateGaugeLin k δ t) := by
  ext x i
  rw [LinearMap.comp_apply, diagPow_apply, plateGaugeLin_apply, plateGaugeLin_apply, mul_pow]
  ring

/-- The determinant of the anisotropic diagonal scaling. -/
lemma det_diagPow (k : ℕ) (c : ℝ) : LinearMap.det (diagPow k c) = c ^ (k * (k + 1) / 2) := by
  have hsum : ∑ i : Fin k, (i.val + 1) = k * (k + 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i + 1) k]
    have h1 : ∑ i ∈ Finset.range (k + 1), i = ∑ i ∈ Finset.range k, (i + 1) := by
      rw [Finset.sum_range_succ']
      ring
    rw [← h1, Finset.sum_range_id, Nat.succ_sub_one, Nat.mul_comm]
  have hA : LinearMap.det (LinearMap.pi fun i : Fin k =>
        (c ^ (i.val + 1) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) ∘ₗ LinearMap.proj i)
      = c ^ (∑ i : Fin k, (i.val + 1)) := by
    rw [LinearMap.det_pi]
    have hcongr : (∏ i : Fin k, LinearMap.det (c ^ (i.val + 1) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)))
        = ∏ i : Fin k, c ^ (i.val + 1) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [LinearMap.det_smul, Module.finrank_self, pow_one, LinearMap.det_id, mul_one]
    rw [hcongr, Finset.prod_pow_eq_pow_sum]
  have hconj := LinearMap.det_conj
    (LinearMap.pi fun i : Fin k =>
      (c ^ (i.val + 1) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) ∘ₗ LinearMap.proj i)
    ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm)
  rw [show diagPow k c = (↑((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm) : (Fin k → ℝ) →ₗ[ℝ] E k)
      ∘ₗ (LinearMap.pi fun i : Fin k =>
        (c ^ (i.val + 1) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) ∘ₗ LinearMap.proj i)
      ∘ₗ ↑((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm).symm from rfl, hconj, hA, hsum]

/-- The gauge of the anisotropic diagonal scaling dominates the gauge. -/
lemma gauge_le_gauge_diagPow {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 1 ≤ c) (x : E k) :
    gauge k hk x ≤ gauge k hk (diagPow k c x) := by
  refine Finset.sup'_le _ _ fun i _ => ?_
  have h1 : |x i| ≤ |diagPow k c x i| := by
    rw [diagPow_apply, abs_mul, abs_of_nonneg (pow_nonneg (le_trans zero_le_one hc) _)]
    calc |x i| = 1 * |x i| := (one_mul _).symm
      _ ≤ c ^ (i.val + 1) * |x i| :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ hc) (abs_nonneg _)
  exact h1.trans (le_gauge k hk _ i)

/-- **Comparing the plate bumps at two scales.**  Enlarging the plate by the factor `c ≥ 1`
enlarges the bump by at most `c^{k(k+1)/2}`. -/
lemma phiPlate_scale_le {k : ℕ} (hk : 1 ≤ k) {c δ t A Cφ : ℝ} (hc : 1 ≤ c) (hCφ : 0 ≤ Cφ)
    (hA : 0 ≤ A) (x : E k) :
    phiPlate k hk (c * δ) t A Cφ x ≤ c ^ (k * (k + 1) / 2) * phiPlate k hk δ t A Cφ x := by
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hdet : |LinearMap.det (plateGaugeLin k (c * δ) t)|
      ≤ c ^ (k * (k + 1) / 2) * |LinearMap.det (plateGaugeLin k δ t)| := by
    rw [plateGaugeLin_scale k c δ t, LinearMap.det_comp, det_diagPow, abs_mul,
      abs_of_nonneg (pow_nonneg hc0.le _)]
  have hg : gauge k hk (plateGaugeLin k δ t x) ≤ gauge k hk (plateGaugeLin k (c * δ) t x) := by
    rw [plateGaugeLin_scale k c δ t, LinearMap.comp_apply]
    exact gauge_le_gauge_diagPow hk hc _
  have hb : (max 1 (gauge k hk (plateGaugeLin k (c * δ) t x))) ^ (-A)
      ≤ (max 1 (gauge k hk (plateGaugeLin k δ t x))) ^ (-A) := by
    refine Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) ?_ (by linarith)
    exact max_le_max le_rfl hg
  rw [phiPlate, phiPlate]
  have hstep : |LinearMap.det (plateGaugeLin k (c * δ) t)|
        * (max 1 (gauge k hk (plateGaugeLin k (c * δ) t x))) ^ (-A)
      ≤ c ^ (k * (k + 1) / 2) * |LinearMap.det (plateGaugeLin k δ t)|
        * (max 1 (gauge k hk (plateGaugeLin k δ t x))) ^ (-A) := by
    refine mul_le_mul hdet hb (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) ?_
    exact mul_nonneg (pow_nonneg hc0.le _) (abs_nonneg _)
  calc Cφ * |LinearMap.det (plateGaugeLin k (c * δ) t)|
        * (max 1 (gauge k hk (plateGaugeLin k (c * δ) t x))) ^ (-A)
      = Cφ * (|LinearMap.det (plateGaugeLin k (c * δ) t)|
        * (max 1 (gauge k hk (plateGaugeLin k (c * δ) t x))) ^ (-A)) := by ring
    _ ≤ Cφ * (c ^ (k * (k + 1) / 2) * |LinearMap.det (plateGaugeLin k δ t)|
        * (max 1 (gauge k hk (plateGaugeLin k δ t x))) ^ (-A)) :=
        mul_le_mul_of_nonneg_left hstep hCφ
    _ = c ^ (k * (k + 1) / 2) * (Cφ * |LinearMap.det (plateGaugeLin k δ t)|
        * (max 1 (gauge k hk (plateGaugeLin k δ t x))) ^ (-A)) := by ring

/-- **Comparing the `ℝ≥0∞`-valued plate bumps at two scales.** -/
lemma platePhi_scale_le {k : ℕ} (hk : 1 ≤ k) {c δ t : ℝ} (hc : 1 ≤ c) (x : E k) :
    platePhi k hk (c * δ) t x
      ≤ ENNReal.ofReal (c ^ (k * (k + 1) / 2)) * platePhi k hk δ t x := by
  have hA : (0:ℝ) ≤ gaugeExp k := by
    rw [gaugeExp]
    have h1 : (0:ℝ) ≤ pkExp k := pkExp_nonneg k
    have h2 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  rw [platePhi_apply, platePhi_apply,
    ← ENNReal.ofReal_mul (pow_nonneg (le_trans zero_le_one hc) (k * (k + 1) / 2))]
  exact ENNReal.ofReal_le_ofReal
    (phiPlate_scale_le hk hc (gaugeAmp_pos k hk).le hA x)

/-- The integral of the polar bump of a plate is the amplitude times the fixed dimensional
constant `∫ (max 1 gauge)^{-A}`; it does not depend on the plate. -/
lemma integral_phiPlate {k : ℕ} (hk : 1 ≤ k) {A : ℝ} (hA : (k : ℝ) < A) (δ c Cφ : ℝ)
    (hδ : δ ≠ 0) :
    (∫ x, phiPlate k hk δ c A Cφ x) = Cφ * ∫ z, (max 1 (gauge k hk z)) ^ (-A) := by
  have hdet := plateGaugeLin_det_ne_zero k hδ c
  have habs : |LinearMap.det (plateGaugeLin k δ c)| * |(LinearMap.det (plateGaugeLin k δ c))⁻¹|
      = 1 := by
    rw [← abs_mul, mul_inv_cancel₀ hdet, abs_one]
  have hint : Integrable (fun z : E k => (max 1 (gauge k hk z)) ^ (-A)) :=
    integrable_gauge_rpow k hk hA
  rw [show (∫ x, phiPlate k hk δ c A Cφ x)
      = ∫ x, (Cφ * |LinearMap.det (plateGaugeLin k δ c)|)
          * (max 1 (gauge k hk (plateGaugeLin k δ c x))) ^ (-A) from rfl]
  have hcomp : (∫ x, (max 1 (gauge k hk (plateGaugeLin k δ c x))) ^ (-A))
      = |(LinearMap.det (plateGaugeLin k δ c))⁻¹| * ∫ z, (max 1 (gauge k hk z)) ^ (-A) := by
    rw [integral_comp_plateGaugeLin hδ c hint, smul_eq_mul]
  rw [integral_const_mul, hcomp]
  calc (Cφ * |LinearMap.det (plateGaugeLin k δ c)|)
        * (|(LinearMap.det (plateGaugeLin k δ c))⁻¹|
          * ∫ z, (max 1 (gauge k hk z)) ^ (-A))
      = Cφ * (|LinearMap.det (plateGaugeLin k δ c)|
          * |(LinearMap.det (plateGaugeLin k δ c))⁻¹|)
        * ∫ z, (max 1 (gauge k hk z)) ^ (-A) := by ring
    _ = Cφ * ∫ z, (max 1 (gauge k hk z)) ^ (-A) := by rw [habs, mul_one]

/-- The `ℝ≥0∞`-valued integral of the canonical plate bump, in the exact form in which the
uncertainty principle produces it. -/
lemma lintegral_platePhi {k : ℕ} (hk : 1 ≤ k) (δ c : ℝ) (hδ : δ ≠ 0) :
    (∫⁻ x, platePhi k hk δ c x)
      = ENNReal.ofReal (gaugeAmp k hk)
        * ENNReal.ofReal (∫ z, (max 1 (gauge k hk z)) ^ (-(gaugeExp k))) := by
  have hA : (k : ℝ) < gaugeExp k := gaugeExp_gt hk
  have hint : Integrable (fun x : E k => phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x) :=
    platePhi_integrable k hk hδ c
  simp only [platePhi_apply]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall
    fun x => phiPlate_nonneg k hk δ c (gaugeExp k) (gaugeAmp k hk) (gaugeAmp_pos k hk).le x)]
  rw [← ENNReal.ofReal_mul (gaugeAmp_pos k hk).le,
    integral_phiPlate hk hA δ c (gaugeAmp k hk) hδ]

end Submission.Vinogradov
