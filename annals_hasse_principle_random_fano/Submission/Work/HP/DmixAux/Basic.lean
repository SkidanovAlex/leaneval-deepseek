import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MMDefs
import Submission.Work.HP.MMVec
import Submission.Work.HP.MMReindex

/-!
# Elementary facts for the `D^mix` reindexing

This file collects the small, self-contained facts used in the proof of
`Work.HP.DmixReindex` (`Submission/Work/HP/DmixReindex.lean`):

* homogeneity of `f_a = ⟨a, ν_{d,n}(·)⟩` in the variable (`formEval_neg`);
* compatibility of `toR` with `ν` and negation;
* invariances of `eNorm`, `IsPrim` and `Cgam` under `x ↦ -x`, giving that `Zx` and `Zy` are
  invariant under `x ↦ -x`;
* the inclusion `Zx a B ⊆ Zy a B` for `1 < B`;
* the identification of the lattice memberships `latOrth`, `latMod` with the evaluations
  `formEval`.
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP.DmixAux

/-! ## Generic Euclidean helpers -/

section generic
variable {ι : Type*} [Fintype ι]

/-- `rNorm` is absolutely homogeneous. -/
theorem rNorm_smul_abs (c : ℝ) (v : ι → ℝ) : rNorm (c • v) = |c| * rNorm v := by
  have h2 : ∑ i, ((c • v) i) ^ 2 = c ^ 2 * ∑ i, (v i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [rNorm, rNorm, h2, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- `Cgam v γ` only depends on `v` through the unordered line `ℝv`. -/
theorem Cgam_smul_abs_one {c : ℝ} (hc : |c| = 1) (v : ι → ℝ) (γ : ℝ) :
    Cgam (c • v) γ = Cgam v γ := by
  ext t
  simp only [Cgam, Set.mem_setOf_eq]
  have hd : dotR (c • v) t = c * dotR v t := by
    simp only [dotR, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hL : |dotR (c • v) t| = |dotR v t| := by rw [hd, abs_mul, hc, one_mul]
  have hR : rNorm (c • v) * rNorm t / (2 * γ) = rNorm v * rNorm t / (2 * γ) := by
    rw [rNorm_smul_abs, hc, one_mul]
  rw [hL, hR]

end generic

/-! ## Homogeneity of `f_a` -/

variable (d n : ℕ)

/-- `f_a(-x) = (-1)^d f_a(x)`. -/
theorem formEval_neg (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    formEval d n a (-x) = (-1) ^ d * formEval d n a x := by
  simp only [formEval]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [veronese_neg (R := ℤ) d n x m]
  ring

/-- `toR` is compatible with `ν` and negation: `toR (ν(-y)) = (-1)^d • toR (ν(y))`. -/
theorem toR_veronese_neg (y : Fin (n + 1) → ℤ) :
    toR (veronese d n (-y)) = (-1 : ℝ) ^ d • toR (veronese d n y) := by
  funext m
  simp only [toR, Pi.smul_apply, smul_eq_mul]
  rw [veronese_neg (R := ℤ) d n y m]
  push_cast
  ring

/-- `|(-1)^d| = 1`. -/
theorem abs_neg_one_pow (d : ℕ) : |(-1 : ℝ) ^ d| = 1 := by
  rw [abs_pow]
  simp

/-! ## The evaluation/lattice dictionary -/

/-- `latOrth` membership is vanishing of `f_a`. -/
theorem mem_latOrth_eq_formEval (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    a ∈ latOrth (veronese d n x) ↔ formEval d n a x = 0 := by
  rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply, formEval]
  simp only [smul_eq_mul, Int.cast_id]

/-- `latMod` membership is divisibility of `f_a`. -/
theorem mem_latMod_eq_formEval (a : Mon d n → ℤ) (y : Fin (n + 1) → ℤ) (Q : ℕ) :
    a ∈ latMod (veronese d n y) Q ↔ (Q : ℤ) ∣ formEval d n a y := by
  rw [latMod, Submodule.mem_comap, Submodule.mem_span_singleton, Fintype.linearCombination_apply,
    formEval]
  simp only [smul_eq_mul, Int.cast_id]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [← hk]; ring⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩

/-! ## Negation invariance of `Zx`, `Zy` and the inclusion `Zx ⊆ Zy` -/

section Zsets
variable [DecidableEq (Mon d n)]

/-- `Zx` is invariant under `x ↦ -x`. -/
theorem Zx_neg_mem (a : Mon d n → ℤ) (B : ℝ) (x : Fin (n + 1) → ℤ) :
    x ∈ Zx d n a B ↔ -x ∈ Zx d n a B := by
  simp only [Zx, Xi, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hp, hn⟩, hf⟩
    exact ⟨⟨by rwa [IsPrim_neg], by rwa [eNorm_neg]⟩,
      by rw [formEval_neg d n a x, hf, mul_zero]⟩
  · rintro ⟨⟨hp, hn⟩, hf⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rwa [IsPrim_neg] at hp
    · rwa [eNorm_neg] at hn
    · rw [formEval_neg d n a x] at hf
      exact (mul_eq_zero.mp hf).resolve_left (pow_ne_zero _ (by norm_num : (-1 : ℤ) ≠ 0))

/-- `Zy` is invariant under `y ↦ -y`. -/
theorem Zy_neg_mem (a : Mon d n → ℤ) (B : ℝ) (y : Fin (n + 1) → ℤ) :
    y ∈ Zy d n a B ↔ -y ∈ Zy d n a B := by
  simp only [Zy, Xi, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hp, hn⟩, hd, hc⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rwa [IsPrim_neg]
    · rwa [eNorm_neg]
    · rw [formEval_neg d n a y]
      obtain ⟨k, hk⟩ := hd
      exact ⟨(-1) ^ d * k, by rw [hk]; ring⟩
    · rw [toR_veronese_neg, Cgam_smul_abs_one (abs_neg_one_pow d) (toR (veronese d n y))
        (Real.log B)]
      exact hc
  · rintro ⟨⟨hp, hn⟩, hd, hc⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rwa [IsPrim_neg] at hp
    · rwa [eNorm_neg] at hn
    · rw [formEval_neg d n a y] at hd
      obtain ⟨k, hk⟩ := hd
      refine ⟨(-1) ^ d * k, ?_⟩
      have h1 : ((-1 : ℤ) ^ d) * ((-1 : ℤ) ^ d) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      calc formEval d n a y = ((-1 : ℤ) ^ d * (-1) ^ d) * formEval d n a y := by rw [h1, one_mul]
        _ = (-1 : ℤ) ^ d * ((-1) ^ d * formEval d n a y) := by ring
        _ = (-1 : ℤ) ^ d * (↑(bigW (wOf B)) * k) := by rw [hk]
        _ = ↑(bigW (wOf B)) * ((-1 : ℤ) ^ d * k) := by ring
    · rw [toR_veronese_neg, Cgam_smul_abs_one (abs_neg_one_pow d) (toR (veronese d n y))
        (Real.log B)] at hc
      exact hc

/-- `⟨ν(x), a⟩ = f_a(x)` for real vectors. -/
theorem dotR_toR_eq_formEval (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    dotR (toR (veronese d n x)) (toR a) = ((formEval d n a x : ℤ) : ℝ) := by
  simp only [dotR, toR, formEval]
  push_cast
  exact Finset.sum_congr rfl fun m _ => by ring

/-- Every rational zero of `f_a` of height `≤ B` is also "locally" counted, for `B > 1`. -/
theorem Zx_subset_Zy (a : Mon d n → ℤ) (B : ℝ) (hB : 1 < B) : Zx d n a B ⊆ Zy d n a B := by
  intro x hx
  rw [Zx, Xi, Set.mem_setOf_eq] at hx
  obtain ⟨⟨hp, hn⟩, hf⟩ := hx
  rw [Zy, Xi, Set.mem_setOf_eq]
  refine ⟨⟨hp, hn⟩, ?_, ?_⟩
  · rw [hf]; exact dvd_zero _
  · rw [Cgam, Set.mem_setOf_eq, dotR_toR_eq_formEval d n a x, hf]
    simp only [Int.cast_zero, abs_zero]
    apply div_nonneg
    · exact mul_nonneg (by simp only [rNorm]; exact Real.sqrt_nonneg _)
        (by simp only [rNorm]; exact Real.sqrt_nonneg _)
    · have : 0 < Real.log B := Real.log_pos hB
      linarith

end Zsets

end Work.HP.DmixAux
