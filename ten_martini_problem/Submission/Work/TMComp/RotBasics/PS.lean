import Submission.Work.TMComp.RotBasics.Defs

/-!
# Basic properties of the Prüfer lift `pruferStep`

With `n = ⌊t + 1/2⌋` and `s = t - n ∈ [-1/2, 1/2)` the definition of `pruferStep` reads

* `pruferStep a t = n` if `s = -1/2`;
* `pruferStep a t = n + 1/2 + arctan (tan (π s) - a) / π` otherwise.

Consequences proved here: the value lies in `[n, n+1)`, the shift identity
`pruferStep a (t+1) = pruferStep a t + 1`, monotonicity in `t`, antitonicity in `a`, and the
positive-lift property for the companion matrix `comp a = !![a,-1;1,0]`.
-/

namespace Work.TMComp.RotBasics

open Work.TMContract

noncomputable section

variable {a t : ℝ}

theorem pruferStep_eq_of_floor {n : ℤ} (hn : ⌊t + 1 / 2⌋ = n) (h : t - (n : ℝ) ≠ -1 / 2) :
    pruferStep a t = (n : ℝ) + 1 / 2 +
      Real.arctan (Real.tan (Real.pi * (t - (n : ℝ))) - a) / Real.pi := by
  rw [pruferStep, hn]
  rw [if_neg h]

theorem pruferStep_eq_of_floor_special {n : ℤ} (hn : ⌊t + 1 / 2⌋ = n) (h : t - (n : ℝ) = -1 / 2) :
    pruferStep a t = (n : ℝ) := by
  rw [pruferStep, hn]
  rw [if_pos h]

theorem pruferStep_cell (a t : ℝ) :
    ((⌊t + 1 / 2⌋ : ℤ) : ℝ) ≤ pruferStep a t ∧
      pruferStep a t < ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 := by
  by_cases h : t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ) = -1 / 2
  · rw [pruferStep_eq_of_floor_special rfl h]
    refine ⟨le_rfl, ?_⟩
    have := Int.lt_floor_add_one (t + 1 / 2)
    push_cast
    linarith
  · rw [pruferStep_eq_of_floor rfl h]
    have h1 := Real.neg_pi_div_two_lt_arctan (Real.tan (Real.pi * (t - (⌊t + 1 / 2⌋ : ℝ))) - a)
    have h2 := Real.arctan_lt_pi_div_two (Real.tan (Real.pi * (t - (⌊t + 1 / 2⌋ : ℝ))) - a)
    have hpi := Real.pi_pos
    constructor
    · have hlt : -1 / 2 <
          Real.arctan (Real.tan (Real.pi * (t - (⌊t + 1 / 2⌋ : ℝ))) - a) / Real.pi := by
        rw [lt_div_iff₀ hpi]
        nlinarith [Real.pi_pos]
      linarith
    · have hlt : Real.arctan (Real.tan (Real.pi * (t - (⌊t + 1 / 2⌋ : ℝ))) - a) / Real.pi < 1 / 2 := by
        rw [div_lt_iff₀ hpi]
        nlinarith [Real.pi_pos]
      linarith

theorem pruferStep_floor_add_one (t : ℝ) :
    ⌊t + 1 + 1 / 2⌋ = ⌊t + 1 / 2⌋ + 1 := by
  rw [show t + 1 + 1 / 2 = (t + 1 / 2) + (1 : ℤ) by push_cast; ring, Int.floor_add_intCast]

theorem pruferStep_add_one (a t : ℝ) : pruferStep a (t + 1) = pruferStep a t + 1 := by
  have hf : ⌊t + 1 + 1 / 2⌋ = ⌊t + 1 / 2⌋ + 1 := pruferStep_floor_add_one t
  have hfr : (⌊t + 1 + 1 / 2⌋ : ℝ) = (⌊t + 1 / 2⌋ : ℝ) + 1 := by exact_mod_cast hf
  have hc : (t + 1 - ((⌊t + 1 / 2⌋ : ℝ) + 1) = -1 / 2) ↔ (t - (⌊t + 1 / 2⌋ : ℝ) = -1 / 2) := by
    constructor <;> intro h <;> linarith
  have ha : Real.pi * (t + 1 - ((⌊t + 1 / 2⌋ : ℝ) + 1)) = Real.pi * (t - (⌊t + 1 / 2⌋ : ℝ)) := by
    ring
  rw [pruferStep, pruferStep, hfr]
  by_cases h : t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ) = -1 / 2
  · rw [if_pos (hc.mpr h), if_pos h]
  · rw [if_neg (fun hc' => h (hc.mp hc')), if_neg h, ha]
    ring

theorem pruferStep_mono (a : ℝ) : Monotone (pruferStep a) := by
  intro t₁ t₂ h12
  set n₁ : ℤ := ⌊t₁ + 1 / 2⌋ with hn₁
  set n₂ : ℤ := ⌊t₂ + 1 / 2⌋ with hn₂
  have hn₁' : ⌊t₁ + 1 / 2⌋ = n₁ := hn₁.symm
  have hn₂' : ⌊t₂ + 1 / 2⌋ = n₂ := hn₂.symm
  have hfl : n₁ ≤ n₂ := by
    rw [← hn₁', ← hn₂']
    exact Int.floor_le_floor (by linarith)
  have hs1 : -1 / 2 ≤ t₁ - (n₁ : ℝ) ∧ t₁ - (n₁ : ℝ) < 1 / 2 := by
    have h1 := Int.floor_le (t₁ + 1 / 2)
    have h2 := Int.lt_floor_add_one (t₁ + 1 / 2)
    rw [hn₁'] at h1 h2
    constructor <;> linarith
  have hs2 : -1 / 2 ≤ t₂ - (n₂ : ℝ) ∧ t₂ - (n₂ : ℝ) < 1 / 2 := by
    have h1 := Int.floor_le (t₂ + 1 / 2)
    have h2 := Int.lt_floor_add_one (t₂ + 1 / 2)
    rw [hn₂'] at h1 h2
    constructor <;> linarith
  rcases lt_or_eq_of_le hfl with hlt | heq
  · have h1 := (pruferStep_cell a t₁).2
    have h2 := (pruferStep_cell a t₂).1
    rw [hn₁'] at h1
    rw [hn₂'] at h2
    have h3 : (n₁ : ℝ) + 1 ≤ (n₂ : ℝ) := by
      have h4 : n₁ + 1 ≤ n₂ := hlt
      exact_mod_cast h4
    linarith
  · by_cases h1 : t₁ - (n₁ : ℝ) = -1 / 2
    · have e1 : pruferStep a t₁ = (n₁ : ℝ) := pruferStep_eq_of_floor_special hn₁' h1
      have e2 : (n₁ : ℝ) = (n₂ : ℝ) := by rw [heq]
      have e3 := (pruferStep_cell a t₂).1
      rw [hn₂'] at e3
      linarith
    · by_cases h2 : t₂ - (n₂ : ℝ) = -1 / 2
      · exfalso
        have h1' : -1 / 2 < t₁ - (n₁ : ℝ) := lt_of_le_of_ne hs1.1 (Ne.symm h1)
        rw [heq] at h1'
        have hh : t₁ - (n₂ : ℝ) ≤ t₂ - (n₂ : ℝ) := by linarith
        linarith
      · have e1 : pruferStep a t₁ = (n₁ : ℝ) + 1 / 2 +
            Real.arctan (Real.tan (Real.pi * (t₁ - (n₁ : ℝ))) - a) / Real.pi :=
          pruferStep_eq_of_floor hn₁' h1
        have e2 : pruferStep a t₂ = (n₂ : ℝ) + 1 / 2 +
            Real.arctan (Real.tan (Real.pi * (t₂ - (n₂ : ℝ))) - a) / Real.pi :=
          pruferStep_eq_of_floor hn₂' h2
        have h1'' : -1 / 2 < t₁ - (n₁ : ℝ) := lt_of_le_of_ne hs1.1 (Ne.symm h1)
        have h2'' : -1 / 2 < t₂ - (n₂ : ℝ) := lt_of_le_of_ne hs2.1 (Ne.symm h2)
        have hss : t₁ - (n₁ : ℝ) ≤ t₂ - (n₂ : ℝ) := by
          rw [heq]; linarith
        have hx : Real.pi * (t₁ - (n₁ : ℝ)) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> nlinarith [Real.pi_pos, h1'', hs1.2]
        have hy : Real.pi * (t₂ - (n₂ : ℝ)) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
          constructor <;> nlinarith [Real.pi_pos, h2'', hs2.2]
        have hxy : Real.pi * (t₁ - (n₁ : ℝ)) ≤ Real.pi * (t₂ - (n₂ : ℝ)) := by
          nlinarith [Real.pi_pos]
        have htan : Real.tan (Real.pi * (t₁ - (n₁ : ℝ))) ≤
            Real.tan (Real.pi * (t₂ - (n₂ : ℝ))) :=
          Real.strictMonoOn_tan.monotoneOn hx hy hxy
        have harctan : Real.arctan (Real.tan (Real.pi * (t₁ - (n₁ : ℝ))) - a) ≤
            Real.arctan (Real.tan (Real.pi * (t₂ - (n₂ : ℝ))) - a) :=
          Real.arctan_mono (by linarith)
        have hcell := (pruferStep_cell a t₁).1
        rw [hn₁'] at hcell
        have hnn : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hfl
        have harctanπ : Real.arctan (Real.tan (Real.pi * (t₁ - (n₁ : ℝ))) - a) / Real.pi ≤
            Real.arctan (Real.tan (Real.pi * (t₂ - (n₂ : ℝ))) - a) / Real.pi :=
          div_le_div_of_nonneg_right harctan (le_of_lt Real.pi_pos)
        linarith

theorem pruferStep_antitone (t : ℝ) : Antitone (fun a : ℝ => pruferStep a t) := by
  intro a a' haa'
  change pruferStep a' t ≤ pruferStep a t
  have key : ∀ b : ℝ, pruferStep b t =
      (if t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ) = -1 / 2 then ((⌊t + 1 / 2⌋ : ℤ) : ℝ)
        else ((⌊t + 1 / 2⌋ : ℤ) : ℝ) + 1 / 2 +
          Real.arctan (Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - b) / Real.pi) := by
    intro b
    rw [pruferStep]
  rw [key a', key a]
  by_cases h : t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ) = -1 / 2
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    have hA : Real.arctan (Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - a') ≤
        Real.arctan (Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - a) :=
      Real.arctan_mono (by linarith)
    have hq : Real.arctan (Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - a') / Real.pi ≤
        Real.arctan (Real.tan (Real.pi * (t - ((⌊t + 1 / 2⌋ : ℤ) : ℝ))) - a) / Real.pi :=
      div_le_div_of_nonneg_right hA (le_of_lt Real.pi_pos)
    linarith


theorem vc_of_int (n : ℤ) : vc (n : ℝ) = (((-1 : ℝ) ^ n : ℝ)) • (1 : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp only [vc, Complex.smul_re, Complex.one_re]
    rw [show Real.pi * (n : ℝ) = (n : ℝ) * Real.pi by ring, Real.cos_int_mul_pi]
    rw [smul_eq_mul, mul_one]
  · simp only [vc, Complex.smul_im, Complex.one_im]
    rw [show Real.pi * (n : ℝ) = (n : ℝ) * Real.pi by ring, Real.sin_int_mul_pi]
    rw [smul_eq_mul, mul_zero]

theorem vc_add_int (n : ℤ) (r : ℝ) : vc ((n : ℝ) + r) = (((-1 : ℝ) ^ n : ℝ)) • vc r := by
  refine Complex.ext ?_ ?_
  · simp only [vc, Complex.smul_re]
    rw [show Real.pi * ((n : ℝ) + r) = (n : ℝ) * Real.pi + Real.pi * r by ring, Real.cos_add,
      Real.cos_int_mul_pi, Real.sin_int_mul_pi]
    ring
  · simp only [vc, Complex.smul_im]
    rw [show Real.pi * ((n : ℝ) + r) = (n : ℝ) * Real.pi + Real.pi * r by ring, Real.sin_add,
      Real.cos_int_mul_pi, Real.sin_int_mul_pi]
    ring

theorem smul_comp (a x : ℝ) :
    smul (comp a) (vc x) = ⟨a * Real.cos (Real.pi * x) - Real.sin (Real.pi * x),
      Real.cos (Real.pi * x)⟩ := by
  refine Complex.ext ?_ ?_ <;>
    simp [smul, comp, vc, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

theorem vc_neg_half : vc (-1 / 2) = (⟨0, -1⟩ : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp only [vc, Complex.ofReal_re]
    rw [show Real.pi * (-1 / 2) = -(Real.pi / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
  · simp only [vc, Complex.ofReal_im]
    rw [show Real.pi * (-1 / 2) = -(Real.pi / 2) by ring, Real.sin_neg, Real.sin_pi_div_two]

theorem vc_half_add (y : ℝ) : vc (1 / 2 + y) = ⟨-Real.sin (Real.pi * y), Real.cos (Real.pi * y)⟩ := by
  refine Complex.ext ?_ ?_
  · simp only [vc, Complex.ofReal_re]
    rw [show Real.pi * (1 / 2 + y) = Real.pi / 2 + Real.pi * y by ring, Real.cos_add,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  · simp only [vc, Complex.ofReal_im]
    rw [show Real.pi * (1 / 2 + y) = Real.pi / 2 + Real.pi * y by ring, Real.sin_add,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring

theorem pruferStep_smul_eq (a t : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ smul (comp a) (vc t) = ρ • vc (pruferStep a t) := by
  set n : ℤ := ⌊t + 1 / 2⌋ with hn
  have hn1 : ⌊t + 1 / 2⌋ = n := hn.symm
  set s : ℝ := t - n with hs
  have ht : t = (n : ℝ) + s := by rw [hs]; ring
  have hfl := Int.floor_le (t + 1 / 2)
  have hfu := Int.lt_floor_add_one (t + 1 / 2)
  rw [hn1] at hfl hfu
  have hslo : -1 / 2 ≤ s := by rw [hs]; linarith
  have hshi : s < 1 / 2 := by rw [hs]; linarith
  rcases eq_or_lt_of_le hslo with hsp | hsp
  · -- special case `s = -1/2`
    have hh : t - (n : ℝ) = -1 / 2 := by rw [← hs]; exact hsp.symm
    have hF : pruferStep a t = (n : ℝ) := pruferStep_eq_of_floor_special hn1 hh
    have hvct : vc t = (((-1 : ℝ) ^ n : ℝ)) • (⟨0, -1⟩ : ℂ) := by
      rw [ht, vc_add_int n s, ← hsp, vc_neg_half]
    refine ⟨1, one_pos, ?_⟩
    rw [hF, hvct, smul_smul_real, ← vc_neg_half, smul_comp, vc_of_int]
    rw [show Real.pi * (-1 / 2) = -(Real.pi / 2) by ring, Real.sin_neg, Real.sin_pi_div_two,
      Real.cos_neg, Real.cos_pi_div_two]
    refine Complex.ext ?_ ?_ <;> simp
  · -- non-special case
    set φ : ℝ := Real.arctan (Real.tan (Real.pi * s) - a) with hφ
    have hh : t - (n : ℝ) ≠ -1 / 2 := by rw [← hs]; exact ne_of_gt hsp
    have hF : pruferStep a t = (n : ℝ) + 1 / 2 + φ / Real.pi := by
      rw [pruferStep_eq_of_floor hn1 hh, ← hs, ← hφ]
    have hcs : 0 < Real.cos (Real.pi * s) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [Real.pi_pos]
    have hcφ : 0 < Real.cos φ := Real.cos_arctan_pos _
    have htanφ : Real.tan φ = Real.tan (Real.pi * s) - a := by
      rw [hφ]; exact Real.tan_arctan _
    have hsinφ : Real.sin φ = Real.cos φ * (Real.tan (Real.pi * s) - a) := by
      rw [← htanφ, Real.tan_eq_sin_div_cos]
      field_simp
    have hsinπs : Real.sin (Real.pi * s) = Real.cos (Real.pi * s) * Real.tan (Real.pi * s) := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    have hmul : Real.cos φ • smul (comp a) (vc s) =
        Real.cos (Real.pi * s) • (⟨-Real.sin φ, Real.cos φ⟩ : ℂ) := by
      rw [smul_comp]
      refine Complex.ext ?_ ?_
      · simp only [Complex.smul_re]
        rw [hsinπs, hsinφ]
        ring
      · simp only [Complex.smul_im]
        ring
    have hkey : smul (comp a) (vc s) =
        (Real.cos (Real.pi * s) / Real.cos φ) • (⟨-Real.sin φ, Real.cos φ⟩ : ℂ) := by
      have hC : Real.cos φ ≠ 0 := ne_of_gt hcφ
      calc smul (comp a) (vc s)
          = (1 / Real.cos φ) • (Real.cos φ • smul (comp a) (vc s)) := by
            rw [smul_smul, one_div, inv_mul_cancel₀ hC, one_smul]
        _ = (1 / Real.cos φ) •
              (Real.cos (Real.pi * s) • (⟨-Real.sin φ, Real.cos φ⟩ : ℂ)) := by rw [hmul]
        _ = (Real.cos (Real.pi * s) / Real.cos φ) • (⟨-Real.sin φ, Real.cos φ⟩ : ℂ) := by
            rw [smul_smul]
            congr 1
            ring
    refine ⟨Real.cos (Real.pi * s) / Real.cos φ, div_pos hcs hcφ, ?_⟩
    have hvt : vc t = (((-1 : ℝ) ^ n : ℝ)) • vc s := by
      rw [ht, vc_add_int]
    have hvF : vc (pruferStep a t) =
        (((-1 : ℝ) ^ n : ℝ)) • (⟨-Real.sin φ, Real.cos φ⟩ : ℂ) := by
      rw [hF, show (n : ℝ) + 1 / 2 + φ / Real.pi = (n : ℝ) + (1 / 2 + φ / Real.pi) by ring,
        vc_add_int, vc_half_add]
      rw [show Real.pi * (φ / Real.pi) = φ by field_simp]
    rw [hvt, hvF, smul_smul_real, hkey, smul_smul, smul_smul, mul_comm]

theorem pruferStep_isPosLift (a : ℝ) : IsPosLift (comp a) (fun t => pruferStep a t) := by
  intro t
  obtain ⟨ρ, hρ, h⟩ := pruferStep_smul_eq a t
  rw [h, norm_smul_real, vc_norm, mul_one, abs_of_pos hρ]

end

end Work.TMComp.RotBasics
