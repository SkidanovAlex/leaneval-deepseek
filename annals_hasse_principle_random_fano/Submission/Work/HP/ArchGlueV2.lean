import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.dyadic_sum_tools

/-!
# Glue lemmas for the proof of `Work.HP.arch` (`Submission/Work/HP/arch.lean`).

This is a `V2` clone of `Submission/Work/HP/ArchGlue.lean` (= identical except that the
unused lemma `eNorm_nonneg` is omitted), so that the `arch` proof can be imported in the
same environment as `Submission.Work.HP.nonarch`.

* `band` : the set whose measure defines `τ(a;γ) = γ · vol(band a γ)`.
* `tauArch_mono_gamma` : monotonicity of `τ` in `γ`.
* `cover_Bset` : `IPt ∩ B(1)` is covered by the strata `Bset d n (M/2^ℓ)` and the degenerate
  set `Lset d n`.
-/

set_option autoImplicit false

noncomputable section

open Classical Finset MvPolynomial MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Work.HP

/-- The "band" whose measure defines `τ(a;γ)`. -/
def band (d n : ℕ) (a : Mon d n → ℝ) (γ : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {u | rNorm u ≤ 1 ∧ a ∈ Cgam (veronese d n u) γ}

lemma tauArch_eq (d n : ℕ) (a : Mon d n → ℝ) (γ : ℝ) :
    tauArch d n a γ = γ * (volume (band d n a γ)).toReal := rfl

lemma rNorm_toR_eq_eNorm {d n : ℕ} (v : Mon d n → ℤ) : rNorm (toR v) = eNorm v := rfl

-- NOTE (arch_v2 repackaging): the lemma `eNorm_nonneg` that stood here has been removed.
-- It is declared with a different signature in `Submission.Work.HP.MinkDefs`, and Lean refuses
-- any environment containing both.  It is not used by this file or by any module below it.

lemma one_le_eNorm_glue {d n : ℕ} {v : Mon d n → ℤ} (hv : v ≠ 0) : 1 ≤ eNorm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  have h2 : (1 : ℝ) ≤ |(v i : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
    exact_mod_cast h1
  have h3 : (1 : ℝ) ≤ (v i : ℝ) ^ 2 := by
    nlinarith [abs_nonneg (v i : ℝ), sq_abs (v i : ℝ), h2]
  calc (1 : ℝ) = Real.sqrt 1 := by simp
    _ ≤ Real.sqrt (∑ j, ((v j : ℝ)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        calc (1 : ℝ) ≤ (v i : ℝ) ^ 2 := h3
          _ ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
              Finset.single_le_sum (f := fun j => ((v j : ℝ)) ^ 2)
                (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    _ = eNorm v := rfl

/-- `band` shrinks as `γ` grows. -/
lemma band_anti {d n : ℕ} (a : Mon d n → ℝ) {γ₁ γ₂ : ℝ} (h1 : 0 < γ₁) (h2 : γ₁ ≤ γ₂) :
    band d n a γ₂ ⊆ band d n a γ₁ := by
  intro u hu
  simp only [band, Set.mem_ofPred_eq, Cgam] at hu ⊢
  obtain ⟨hru, hcu⟩ := hu
  have hγ₂ : 0 < γ₂ := lt_of_lt_of_le h1 h2
  refine ⟨hru, ?_⟩
  rw [div_eq_mul_inv] at hcu ⊢
  have hle : (2 * γ₂)⁻¹ ≤ (2 * γ₁)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  calc |dotR (veronese d n u) a| ≤ rNorm (veronese d n u) * rNorm a * (2 * γ₂)⁻¹ := hcu
    _ ≤ rNorm (veronese d n u) * rNorm a * (2 * γ₁)⁻¹ :=
        mul_le_mul_of_nonneg_left hle (mul_nonneg (rNorm_nonneg _) (rNorm_nonneg _))

lemma tauArch_mono_gamma {d n : ℕ} (a : Mon d n → ℝ) {γ₁ γ₂ : ℝ} (h1 : 0 < γ₁)
    (h2 : γ₁ ≤ γ₂) (hfin : volume (band d n a γ₁) ≠ ⊤) :
    γ₁ * tauArch d n a γ₂ ≤ γ₂ * tauArch d n a γ₁ := by
  have hγ₂ : 0 < γ₂ := lt_of_lt_of_le h1 h2
  have hvol : (volume (band d n a γ₂)).toReal ≤ (volume (band d n a γ₁)).toReal := by
    apply ENNReal.toReal_mono hfin
    exact measure_mono (band_anti a h1 h2)
  rw [tauArch_eq, tauArch_eq]
  calc γ₁ * (γ₂ * (volume (band d n a γ₂)).toReal)
      = γ₂ * (γ₁ * (volume (band d n a γ₂)).toReal) := by ring
    _ ≤ γ₂ * (γ₁ * (volume (band d n a γ₁)).toReal) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvol h1.le) hγ₂.le

/-- Every element of `IPt ∩ B(1)` lies either in a stratum `Bset d n (M/2^ℓ)` or in `Lset`. -/
lemma cover_Bset (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) {M : ℝ} (hM : 0 < M)
    (hgrad : ∀ (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ), rNorm x ≤ 1 →
      rNorm (gradVec d n a x) ≤ M * rNorm a) :
    {a : Mon d n → ℝ | IPt d n a ∧ rNorm a ≤ 1} ⊆
      (⋃ ℓ : ℕ, Bset d n (M / 2 ^ ℓ)) ∪ Lset d n := by
  rintro a ⟨haI, ha1⟩
  obtain ⟨x, hx1, hx0⟩ := haI
  by_cases hg : gradVec d n a x = 0
  · exact Or.inr ⟨ha1, x, hx1, hx0, hg⟩
  · have hμpos : 0 < rNorm (gradVec d n a x) :=
      lt_of_le_of_ne (rNorm_nonneg _) (fun h => hg (rNorm_eq_zero.mp h.symm))
    have ha0 : a ≠ 0 := by
      intro h
      apply hg
      rw [h]
      funext j
      simp [gradVec, gradF]
    have han : 0 < rNorm a :=
      lt_of_le_of_ne (rNorm_nonneg _) (fun h => ha0 (rNorm_eq_zero.mp h.symm))
    have htM : rNorm (gradVec d n a x) / rNorm a ≤ M := by
      rw [div_le_iff₀ han]
      exact hgrad a x hx1.le
    obtain ⟨ℓ, hℓ1, hℓ2⟩ :=
      (dyadic_sum_tools n hn).1 M _ hM (div_pos hμpos han) htM
    have hlt : M / 2 ^ ℓ * rNorm a < rNorm (gradVec d n a x) := by
      calc M / 2 ^ ℓ * rNorm a < rNorm (gradVec d n a x) / rNorm a * rNorm a :=
            mul_lt_mul_of_pos_right hℓ1 han
        _ = rNorm (gradVec d n a x) := div_mul_cancel₀ _ han.ne'
    have hle : rNorm (gradVec d n a x) ≤ 2 * (M / 2 ^ ℓ) * rNorm a := by
      calc rNorm (gradVec d n a x)
          = rNorm (gradVec d n a x) / rNorm a * rNorm a :=
            (div_mul_cancel₀ _ han.ne').symm
        _ ≤ (2 * (M / 2 ^ ℓ)) * rNorm a := mul_le_mul_of_nonneg_right hℓ2 han.le
    have hmem : a ∈ Bset d n (M / 2 ^ ℓ) :=
      ⟨ha1, ⟨x, hx1, hx0⟩, x, hx1, hx0, hlt, hle⟩
    rw [Set.mem_union, Set.mem_iUnion]
    exact Or.inl ⟨ℓ, hmem⟩

end Work.HP
