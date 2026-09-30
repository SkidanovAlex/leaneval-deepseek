import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.VKStripDefs
import Submission.Work.BMF.vk_L_lower
import Submission.Work.BMF.zeroFree_bounded_height_chi
import Submission.Work.BMF.LFunction_strip_VK
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_logDeriv_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # V3: the zero-free region of Vinogradov–Korobov type (exponent `6/7`)

This file proves `LFunction_zeroFree_VK`.  The proof has two ingredients:

* the (delegated / sibling) growth bound `VKGrowth` (node `V2`), turned into strip
  logarithmic-derivative bounds `VKStrip` by the Jensen-type argument of the sibling node
  `Work.BMF.LFunction_strip_VK`;
* the classical `3-4-1` zero-detection argument (`zeroFree_of_VKStrip`), together with the
  de la Vallée Poussin type region at bounded heights (`zeroFree_small_height`).
-/

set_option maxHeartbeats 8000000

namespace Work.BMF

open Complex

/-- **Arithmetic endgame.**  Suppose `1/(x+δ) ≤ (3/4)/x + W`, `δ ≥ 0`, `W ≥ 0` and
`xW ≤ 1/16`.  Then `δ ≥ x/8`. -/
lemma vkEndgame {x δ W : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ) (hW : 0 ≤ W) (hxW : x * W ≤ 1 / 16)
    (h1 : 1 / (x + δ) ≤ 3 / 4 / x + W) : x / 8 ≤ δ := by
  have hxδ : 0 < x + δ := by linarith
  rw [div_le_iff₀ hxδ] at h1
  have h4 : (3 / 4 / x + W) * (x + δ) = 3 / 4 + 3 * δ / (4 * x) + W * x + W * δ := by
    field_simp
    ring
  have h5 : 1 / 4 - W * x ≤ δ * (3 / (4 * x) + W) := by
    have h6 : 1 ≤ 3 / 4 + 3 * δ / (4 * x) + W * x + W * δ := by linarith [h1, h4]
    have h7 : δ * (3 / (4 * x) + W) = 3 * δ / (4 * x) + W * δ := by ring
    linarith [h6, h7]
  have h6 : 3 / (4 * x) + W ≤ 13 / (16 * x) := by
    have hW' : W ≤ 1 / (16 * x) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [hxW]
    have h7 : 3 / (4 * x) + 1 / (16 * x) = 13 / (16 * x) := by
      field_simp
      ring
    linarith [h7, hW']
  have h8 : 3 / 16 ≤ 1 / 4 - W * x := by linarith [hxW]
  have h9 : δ * (3 / (4 * x) + W) ≤ δ * (13 / (16 * x)) := mul_le_mul_of_nonneg_left h6 hδ
  have h10 : 3 / 16 ≤ δ * (13 / (16 * x)) := le_trans h8 (le_trans h5 h9)
  have h11 : δ * (13 / (16 * x)) = 13 * δ / (16 * x) := by ring
  rw [h11, le_div_iff₀ (by positivity)] at h10
  linarith [h10]

/-- **`3-4-1` combination.**  Given the three upper bounds `A ≤ p + Cζ`, `B + 1/q ≤ E Dn/η`,
`C ≤ E Dm/η`, the positivity `0 ≤ 3A + 4B + C` and the crude bounds `Dn ≤ 5Q₁`, `Dm ≤ 6Q₁`, one
has `4/q ≤ 3p + 3Cζ + 26 E Q₁/η`. -/
private lemma vkCombine {A B C p q Cζ Dn Dm η Q₁ E : ℝ}
    (hη : 0 < η) (hE : 0 < E) (h341 : 0 ≤ 3 * A + 4 * B + C)
    (hA : A ≤ p + Cζ) (hB : B ≤ -1 / q + E * Dn / η) (hC : C ≤ E * Dm / η)
    (hDn : Dn ≤ 5 * Q₁) (hDm : Dm ≤ 6 * Q₁) :
    4 * (1 / q) ≤ 3 * p + 3 * Cζ + 26 * E * Q₁ / η := by
  have h1 : η * (3 * A + 4 * B + C) ≤
      η * (3 * (p + Cζ) + 4 * (-1 / q + E * Dn / η) + E * Dm / η) :=
    mul_le_mul_of_nonneg_left (by linarith [hA, hB, hC]) hη.le
  have h2 : η * (3 * (p + Cζ) + 4 * (-1 / q + E * Dn / η) + E * Dm / η) =
      3 * η * p + 3 * η * Cζ - 4 * η * (1 / q) + 4 * E * Dn + E * Dm := by
    field_simp
    ring
  have h3 : 4 * E * Dn + E * Dm ≤ 26 * E * Q₁ := by nlinarith [hDn, hDm, hE]
  have h4 : 4 * η * (1 / q) ≤ 3 * η * p + 3 * η * Cζ + 26 * E * Q₁ := by
    rw [h2] at h1
    nlinarith [h1, h3, mul_nonneg hη.le h341]
  have h5 : (4 * η * (1 / q)) / η ≤ (3 * η * p + 3 * η * Cζ + 26 * E * Q₁) / η :=
    div_le_div_of_nonneg_right h4 hη.le
  have e1 : (4 * η * (1 / q)) / η = 4 * (1 / q) := by field_simp
  have e2 : (3 * η * p + 3 * η * Cζ + 26 * E * Q₁) / η = 3 * p + 3 * Cζ + 26 * E * Q₁ / η := by
    field_simp
  rw [e1, e2] at h5
  exact h5

/-- **Arithmetic for the shift `x = η/(K Q₁)`.**  With `x = η/(KQ₁)`, `x ≤ 1/K` and
`3Cζ + 26E ≤ K/4` one has `x (3Cζ + 26 E Q₁/η) ≤ 1/4`. -/
private lemma vk_xW_bound {x η K Q₁ Cζ E : ℝ} (hx : x = η / (K * Q₁)) (hη : 0 < η)
    (hK : 0 < K) (hQ₁ : 0 < Q₁) (hxK : x ≤ 1 / K) (hKr : 3 * Cζ + 26 * E ≤ K / 4)
    (hCζ : 0 < Cζ) : x * (3 * Cζ + 26 * E * Q₁ / η) ≤ 1 / 4 := by
  have h1 : x * (26 * E * Q₁ / η) = 26 * E / K := by
    rw [hx]
    field_simp
  have h2 : x * (3 * Cζ) ≤ 3 * Cζ / K := by
    have h : x * (3 * Cζ) ≤ (1 / K) * (3 * Cζ) := mul_le_mul_of_nonneg_right hxK (by positivity)
    have h' : (1 / K) * (3 * Cζ) = 3 * Cζ / K := by field_simp
    linarith [h, h']
  have h3 : (3 * Cζ / K + 26 * E / K : ℝ) ≤ 1 / 4 := by
    rw [← add_div, div_le_iff₀ hK]
    nlinarith [hKr, hK]
  have h4 : x * (3 * Cζ + 26 * E * Q₁ / η) = x * (3 * Cζ) + x * (26 * E * Q₁ / η) := by ring
  linarith [h1, h2, h3, h4]

/-- **Endgame of the Vinogradov–Korobov zero-free region.**  From the strip
logarithmic-derivative bounds `VKStrip c E` one gets the zero-free region of exponent `6/7` for
all heights `|t| ≥ 10`: the classical `3-4-1` argument at the point `1+x+iγ` (`x` a small
multiple of the strip width `η`), applied to `χ` at the zero's own height (pole form) and to a
primitive character `ψ` inducing `χ²` at height `2γ` (regular form). -/
theorem zeroFree_of_VKStrip (c E : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hE : 0 < E)
    (hstrip : VKStrip c E) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ σ t : ℝ, 10 ≤ |t| →
        1 - c' / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨hEpos, hreg, hpole⟩ := hstrip
  obtain ⟨Cζ, hCζpos, hCζ⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
  set Lc : ℝ := max (Real.log (1 / c)) 6 with hLcdef
  have hLc6 : 6 ≤ Lc := le_max_right _ _
  have hlogcinv : Real.log (1 / c) ≤ Lc := le_trans (le_max_left _ _) le_rfl
  have hc0 : 0 < c := hc
  set K : ℝ := 1000 * (3 * Cζ + 26 * E + 1) + 1000 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hK1 : 1 ≤ K := by rw [hKdef]; nlinarith [hCζpos, hEpos]
  have hKr : 3 * Cζ + 26 * E ≤ K / 4 := by rw [hKdef]; nlinarith [hCζpos, hEpos]
  set C₂ : ℝ := Real.log K + Lc + 2 with hC₂def
  have hC₂1 : 1 ≤ C₂ := by rw [hC₂def]; linarith [Real.log_nonneg hK1, hLc6]
  have hC₂pos : 0 < C₂ := lt_of_lt_of_le one_pos hC₂1
  set c' : ℝ := min (c / 256) (c / (256 * K * C₂)) with hc'def
  have hc'pos : 0 < c' := by rw [hc'def]; positivity
  have hc'1 : c' ≤ c / 256 := le_trans (min_le_left _ _) le_rfl
  have hc'2 : c' ≤ c / (256 * K * C₂) := le_trans (min_le_right _ _) le_rfl
  refine ⟨c', hc'pos, ?_⟩
  intro N hN χ hprim σ t ht hσ
  haveI : NeZero N := hN
  by_cases hσ1 : 1 ≤ σ
  · refine DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ)
      (s := ((σ : ℂ) + (t : ℂ) * Complex.I)) (Or.inr ?_) (by simpa using hσ1)
    intro hs
    have htz : t = 0 := by
      have h := congrArg Complex.im hs
      simpa using h
    rw [htz, abs_zero] at ht
    linarith
  push_neg at hσ1
  intro hzero
  set T : ℝ := |t| + 3 with hTdef
  set L₂ : ℝ := Real.log (|2 * t| + 3) with hL₂def
  have hTsix : 13 ≤ T := by rw [hTdef]; have := abs_nonneg t; linarith
  have hlogT1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
  have hlogTpos : 0 < Real.log T := lt_of_lt_of_le one_pos hlogT1
  have hloglogT0 : 0 ≤ Real.log (Real.log T) := Real.log_nonneg hlogT1
  have h2t : |2 * t| = 2 * |t| := by rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hL₂pos : 0 < L₂ := by
    rw [hL₂def]; exact Real.log_pos (by rw [h2t]; linarith [abs_nonneg t, ht])
  have hL₂geT : Real.log T ≤ L₂ := by
    rw [hL₂def, hTdef, h2t]
    exact Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
  have hL₂1 : 1 ≤ L₂ := le_trans hlogT1 hL₂geT
  have hL₂le : L₂ ≤ 2 * Real.log T := by
    rw [hL₂def, h2t, hTdef]
    have h1 : Real.log (2 * |t| + 3) ≤ Real.log (2 * (|t| + 3)) :=
      Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
    have h3 : Real.log (2 * (|t| + 3)) = Real.log 2 + Real.log (|t| + 3) :=
      Real.log_mul (by norm_num) (by linarith [abs_nonneg t])
    have h4 : Real.log 2 ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    linarith
  have hL₂log : Real.log L₂ ≤ 1 + Real.log (Real.log T) := by
    have h4 : Real.log L₂ ≤ Real.log (2 * Real.log T) := Real.log_le_log hL₂pos hL₂le
    rw [Real.log_mul (by norm_num) (ne_of_gt hlogTpos)] at h4
    have h5 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  set Q₀ : ℝ := Real.log ((N : ℝ) + 2) + Real.log (Real.log T) with hQ₀def
  have hlogN1 : 1 ≤ Real.log ((N : ℝ) + 2) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have h2 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    linarith [Real.exp_one_lt_three]
  have hlogs : Real.log (Real.log T) ≤ Q₀ := by rw [hQ₀def]; linarith [hlogN1]
  have hlogN : Real.log ((N : ℝ) + 2) ≤ Q₀ := by rw [hQ₀def]; linarith [hloglogT0]
  have hQ₀1 : 1 ≤ Q₀ := by rw [hQ₀def]; linarith
  have hQ₀pos : 0 < Q₀ := lt_of_lt_of_le one_pos hQ₀1
  set η : ℝ := (c / 4) * L₂ ^ (-(6 / 7 : ℝ)) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  have hηq : η ≤ 1 / 4 := by
    rw [hηdef]
    have h1 : L₂ ^ (-(6 / 7 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL₂1 (by norm_num)
    have h2 : (0:ℝ) < L₂ ^ (-(6 / 7 : ℝ)) := Real.rpow_pos_of_pos hL₂pos (-(6/7:ℝ))
    nlinarith [h1, hc, hc1, h2]
  set Q₁ : ℝ := Q₀ + Real.log K + Lc + 1 with hQ₁def
  have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hQ₁1 : 1 ≤ Q₁ := by rw [hQ₁def]; linarith
  have hQ₁pos : 0 < Q₁ := lt_of_lt_of_le one_pos hQ₁1
  have hQ₁le : Q₁ ≤ C₂ * Q₀ := by
    rw [hQ₁def, hC₂def]; nlinarith [hQ₀1, hlogK0, hLc6]
  set x : ℝ := η / (K * Q₁) with hxdef
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hηQ₁ : η ≤ Q₁ := by linarith [hηq, hQ₁1]
  have hxK : x ≤ 1 / K := by
    rw [hxdef, div_le_div_iff₀ (by positivity) hKpos]
    nlinarith [hηQ₁, hηpos, hKpos]
  have hxη8 : x ≤ η / 8 := by
    rw [hxdef, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 8)]
    have h : (8:ℝ) ≤ K * Q₁ := by nlinarith [hK1, hQ₁1]
    nlinarith [hηpos, h]
  have hx2η : x + 2 * η ≤ 1 := by nlinarith [hxη8, hηq, hηpos]
  have hηleT : η ≤ c * Real.log T ^ (-(6 / 7 : ℝ)) := by
    rw [hηdef]
    have h1 : L₂ ^ (-(6 / 7 : ℝ)) ≤ (Real.log T) ^ (-(6 / 7 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hlogTpos hL₂geT (by norm_num)
    nlinarith [h1, hc]
  have hηleL₂ : η ≤ c * Real.log (|2 * t| + 3) ^ (-(6 / 7 : ℝ)) := by
    rw [hηdef, hL₂def]
    have h1 : (0:ℝ) < Real.log (|2 * t| + 3) := by rw [← hL₂def]; exact hL₂pos
    nlinarith [hc, Real.rpow_pos_of_pos h1 (-(6/7:ℝ))]
  set Q : ℝ := Real.log (|t| + 3) ^ (6 / 7 : ℝ) * (Real.log ((N : ℝ) + 2) +
      Real.log (Real.log (|t| + 3))) with hQdef
  have hQeq : Q = Real.log T ^ (6 / 7 : ℝ) * Q₀ := by
    rw [hQdef, hQ₀def, ← hTdef]
  have hQge1 : 1 ≤ Q := by
    rw [hQeq]
    have h1 : 1 ≤ Real.log T ^ (6 / 7 : ℝ) := Real.one_le_rpow hlogT1 (by norm_num)
    nlinarith [h1, hQ₀1]
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQge1
  have hQT : Real.log T ^ (-(6 / 7 : ℝ)) = Q₀ / Q := by
    rw [hQeq, Real.rpow_neg hlogTpos.le]
    field_simp
  have hL₂inv : (1 / 2) * Real.log T ^ (-(6 / 7 : ℝ)) ≤ L₂ ^ (-(6 / 7 : ℝ)) := by
    have h1 : (2 * Real.log T) ^ (-(6 / 7 : ℝ)) ≤ L₂ ^ (-(6 / 7 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hL₂pos hL₂le (by norm_num)
    have h2 : (2 * Real.log T) ^ (-(6 / 7 : ℝ)) =
        2 ^ (-(6 / 7 : ℝ)) * Real.log T ^ (-(6 / 7 : ℝ)) :=
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hlogTpos.le
    have h3 : (1/2 : ℝ) ≤ 2 ^ (-(6 / 7 : ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 1/2) (by positivity : (0:ℝ) < 2 ^ (6/7:ℝ))]
      have h4 : (2:ℝ) ^ (6 / 7 : ℝ) ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          (by norm_num : (6/7:ℝ) ≤ 1)
      simpa using h4
    have h5 : 0 < Real.log T ^ (-(6 / 7 : ℝ)) := Real.rpow_pos_of_pos hlogTpos _
    rw [h2] at h1
    nlinarith [h1, h3, h5]
  have hδpos : 0 < 1 - σ := by linarith
  have hδle : 1 - σ ≤ c' / Q := by linarith [hσ]
  have hσpos : 0 < σ := by
    have h1 : c' / Q ≤ 1 / 256 := by
      rw [div_le_iff₀ hQpos]
      nlinarith [hc'1, hc1, hQge1]
    linarith [hσ, h1]
  set χ₂ : DirichletCharacter ℂ N := χ * χ with hχ₂def
  set M : ℕ := χ₂.conductor with hMdef
  haveI hMne : NeZero M := ⟨by rw [hMdef]; exact χ₂.conductor_ne_zero⟩
  set ψ : DirichletCharacter ℂ M := χ₂.primitiveCharacter with hψdef
  have hMle : M ≤ N := by
    rw [hMdef]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) χ₂.conductor_dvd_level
  have hval : ∀ a : ℤ, IsCoprime a (N : ℤ) → ψ (a : ZMod M) = (χ (a : ZMod N)) ^ 2 := by
    intro a ha
    have hcl := DFunLike.congr_fun (DirichletCharacter.changeLevel_primitiveCharacter χ₂) (a : ZMod N)
    have hcast := DirichletCharacter.changeLevel_eq_cast_of_dvd' (χ := χ₂.primitiveCharacter)
        χ₂.conductor_dvd_level ha
    rw [hcast] at hcl
    rw [hψdef, hcl, hχ₂def, MulChar.mul_apply]
    ring
  have hDn : VKDenom N t η x ≤ 5 * Q₁ := by
    have hunf : VKDenom N t η x = Real.log ((N : ℝ) + 2) + Real.log (Real.log T) +
        Real.log (1 / η) + Real.log (1 / x) + 1 := by
      simp only [VKDenom]
      rw [← hTdef]
    have hlogη : Real.log (1 / η) ≤ 2 * Lc + Real.log (Real.log T) := by
      have h1 : 1 / η = 4 * (1 / c) * L₂ ^ (6 / 7 : ℝ) := by
        rw [hηdef, Real.rpow_neg hL₂pos.le]
        field_simp
      have hlog4 : Real.log 4 ≤ 4 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4); linarith
      have hL₂log0 : 0 ≤ Real.log L₂ := Real.log_nonneg hL₂1
      have h67 : (6/7 : ℝ) * Real.log L₂ ≤ Real.log L₂ := by nlinarith [hL₂log0]
      rw [h1]
      rw [Real.log_mul (x := 4 * (1 / c)) (y := L₂ ^ (6 / 7 : ℝ))
          (ne_of_gt (by positivity : (0:ℝ) < 4 * (1 / c)))
          (ne_of_gt (by positivity : (0:ℝ) < L₂ ^ (6 / 7 : ℝ))),
        Real.log_mul (x := (4:ℝ)) (y := 1 / c) (by norm_num)
          (ne_of_gt (by positivity : (0:ℝ) < 1 / c)), Real.log_rpow hL₂pos]
      linarith [hlog4, hL₂log, hL₂log0, hlogcinv, hLc6, h67]
    have hlogx : Real.log (1 / x) ≤ Real.log K + Q₁ + Real.log (1 / η) := by
      have h1 : 1 / x = K * Q₁ / η := by
        rw [hxdef]; field_simp
      have h2 : Real.log Q₁ ≤ Q₁ := by
        have := Real.log_le_sub_one_of_pos hQ₁pos; linarith
      rw [h1]
      rw [Real.log_div (x := K * Q₁) (y := η) (ne_of_gt (by positivity : (0:ℝ) < K * Q₁))
          (ne_of_gt hηpos),
        Real.log_mul (x := K) (y := Q₁) (ne_of_gt hKpos) (ne_of_gt hQ₁pos), one_div, Real.log_inv]
      linarith [h2]
    rw [hunf, hQ₁def]
    linarith [hlogη, hlogx, hlogN, hlogs, hlogK0, hLc6]
  have hDm : VKDenom M (2 * t) η x ≤ 6 * Q₁ := by
    have hunf : VKDenom M (2 * t) η x = Real.log ((M : ℝ) + 2) + Real.log (Real.log (|2 * t| + 3)) +
        Real.log (1 / η) + Real.log (1 / x) + 1 := by simp only [VKDenom]
    have h7 : Real.log ((M : ℝ) + 2) ≤ Real.log ((N : ℝ) + 2) := by
      apply Real.log_le_log (by positivity)
      have h8 : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMle
      linarith
    have h8 : Real.log (Real.log (|2 * t| + 3)) ≤ 1 + Real.log (Real.log T) := by
      have hlt : 0 < Real.log (|2 * t| + 3) := by
        rw [h2t]
        exact Real.log_pos (by linarith [abs_nonneg t, ht])
      have h4 : Real.log (|2 * t| + 3) ≤ Real.log (2 * T) := by
        rw [hTdef, h2t]
        exact Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
      have h5 : Real.log (2 * T) = Real.log 2 + Real.log T :=
        Real.log_mul (by norm_num) (by linarith [hTsix])
      rw [h5] at h4
      have h6 : Real.log (Real.log (|2 * t| + 3)) ≤ Real.log (Real.log 2 + Real.log T) :=
        Real.log_le_log hlt h4
      have h7 : Real.log 2 + Real.log T ≤ 2 * Real.log T := by
        have h : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith [hTsix])
        linarith
      have hpos7 : 0 < Real.log 2 + Real.log T := by
        have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
        have h2 : 0 < Real.log T := hlogTpos
        linarith
      have h8b : Real.log (Real.log 2 + Real.log T) ≤ Real.log (2 * Real.log T) :=
        Real.log_le_log hpos7 h7
      have h9 : Real.log (2 * Real.log T) = Real.log 2 + Real.log (Real.log T) :=
        Real.log_mul (by norm_num) (ne_of_gt hlogTpos)
      have h10 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      rw [h9] at h8b
      linarith [h6, h8b, h10]
    have hunfN : VKDenom N t η x = Real.log ((N : ℝ) + 2) + Real.log (Real.log T) +
        Real.log (1 / η) + Real.log (1 / x) + 1 := by
      simp only [VKDenom]
      rw [← hTdef]
    rw [hunfN] at hDn
    rw [hunf]
    linarith [hDn, h7, h8]
  by_cases hbig : η / 16 ≤ 1 - σ
  · have hlow : c / 256 / Q < 1 - σ := by
      have h1 : c / 128 / Q ≤ η / 16 := by
        have h2 : η / 16 = (c / 64) * L₂ ^ (-(6 / 7 : ℝ)) := by rw [hηdef]; ring
        have h3 : (c / 64) * ((1 / 2) * Real.log T ^ (-(6 / 7 : ℝ))) ≤
            (c / 64) * L₂ ^ (-(6 / 7 : ℝ)) :=
          mul_le_mul_of_nonneg_left hL₂inv (by positivity)
        have h4 : c / 128 / Q ≤ (c / 64) * ((1 / 2) * Real.log T ^ (-(6 / 7 : ℝ))) := by
          rw [hQT, div_le_iff₀ hQpos]
          rw [show (c / 64) * (1 / 2 * (Q₀ / Q)) * Q = c * Q₀ / 128 by field_simp; ring]
          nlinarith [hQ₀1, hc]
        linarith [h2, h3, h4]
      have h5 : c / 256 / Q < c / 128 / Q := by
        apply div_lt_div_of_pos_right _ hQpos
        rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 256) (by norm_num : (0:ℝ) < 128)]
        linarith [hc]
      linarith [h1, h5, hbig]
    have hup : 1 - σ ≤ c / 256 / Q := by
      calc 1 - σ ≤ c' / Q := hδle
        _ ≤ (c / 256) / Q := div_le_div_of_nonneg_right hc'1 hQpos.le
    linarith [hlow, hup]
  · push_neg at hbig
    have hx1 : 1 < 1 + x := by linarith
    have hx2 : 1 + x ≤ 2 := by linarith
    set Wf : ℝ := 3 * Cζ + 26 * E * Q₁ / η with hWfdef
    have h341 := Commons.NumberTheory.DirichletCharacter.three_four_one_nonneg_uniform χ ψ hval
        (σ := 1 + x) (τ := t) hx1
    have hζb : (-deriv riemannZeta (((1 + x : ℝ) : ℂ)) / riemannZeta (((1 + x : ℝ) : ℂ))).re ≤
        1 / x + Cζ := by
      have h := hCζ (1 + x) hx1 hx2
      have hxeq : (1 + x : ℝ) - 1 = x := by ring
      rwa [hxeq] at h
    have hpoleb : (-logDeriv (DirichletCharacter.LFunction χ)
          (((1 + x : ℝ) : ℂ) + Complex.I * (t : ℂ))).re ≤
        -1 / (x + 1 - σ) + E * VKDenom N t η x / η := by
      have h := hpole N χ t x η σ ht hxpos hxη8 hx2η hηleT hσpos hσ1
        (by linarith [hbig]) hzero
      have heq : (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
          (((1 + x : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by ring
      rwa [heq] at h
    have hregb : (-logDeriv (DirichletCharacter.LFunction ψ)
          (((1 + x : ℝ) : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))).re ≤
        E * VKDenom M (2 * t) η x / η := by
      have h2t10 : 10 ≤ |2 * t| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
      have h := hreg M ψ (2 * t) x η h2t10 hxpos hxη8 hx2η hηleL₂
      have heq : (((1 + x : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) =
          (((1 + x : ℝ) : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ)) := by ring
      rwa [heq] at h
    have hq : 4 * (1 / (x + 1 - σ)) ≤ 3 * (1 / x) + 3 * Cζ + 26 * E * Q₁ / η :=
      vkCombine (p := 1 / x) (q := x + 1 - σ) hηpos hEpos h341 hζb hpoleb hregb hDn hDm
    clear hreg hpole h341 hζb hpoleb hregb hDn hDm hval
    have hW : 1 / (x + (1 - σ)) ≤ 3 / 4 / x + Wf / 4 := by
      have h := div_le_div_of_nonneg_right hq (by norm_num : (0:ℝ) ≤ 4)
      have e1 : (4 * (1 / (x + 1 - σ))) / 4 = 1 / (x + (1 - σ)) := by ring
      have e2 : (3 * (1 / x) + 3 * Cζ + 26 * E * Q₁ / η) / 4 = 3 / 4 / x + Wf / 4 := by
        rw [hWfdef]; ring
      rw [e1, e2] at h
      exact h
    have hxW : x * (Wf / 4) ≤ 1 / 16 := by
      have h := vk_xW_bound (Cζ := Cζ) (E := E) (K := K) (Q₁ := Q₁) hxdef hηpos hKpos hQ₁pos
        hxK hKr hCζpos
      rw [hWfdef]
      linarith [h]
    have hWn : (0:ℝ) ≤ Wf / 4 := by rw [hWfdef]; positivity
    have hδ8 : x / 8 ≤ 1 - σ := vkEndgame hxpos (le_of_lt hδpos) hWn hxW hW
    have hx8eq : x / 8 = c * L₂ ^ (-(6 / 7 : ℝ)) / (32 * K * Q₁) := by
      rw [hxdef, hηdef]; ring
    have hlow : c / (64 * K * C₂) / Q ≤ x / 8 := by
      rw [hx8eq]
      have hLHS : c / (64 * K * C₂) / Q = c / (64 * K * C₂ * Q) := by rw [div_div]
      rw [hLHS, div_le_div_iff₀ (by positivity) (by positivity)]
      have hm : (32 * K * Q₁ : ℝ) ≤ L₂ ^ (-(6 / 7 : ℝ)) * (64 * K * C₂ * Q) := by
        have h1 : (1 / 2) * (Q₀ / Q) ≤ L₂ ^ (-(6 / 7 : ℝ)) := by rw [← hQT]; exact hL₂inv
        have h2 : (32 * K * Q₁ : ℝ) ≤ (1 / 2) * (Q₀ / Q) * (64 * K * C₂ * Q) := by
          have h3 : (1 / 2) * (Q₀ / Q) * (64 * K * C₂ * Q) = 32 * K * C₂ * Q₀ := by
            field_simp
            ring
          rw [h3]
          have h5 : (32 * K * Q₁ : ℝ) ≤ 32 * K * (C₂ * Q₀) :=
            mul_le_mul_of_nonneg_left hQ₁le (by positivity : (0:ℝ) ≤ 32 * K)
          have h6 : (32 * K * (C₂ * Q₀) : ℝ) = 32 * K * C₂ * Q₀ := by ring
          linarith [h5, h6]
        have h4 : (0:ℝ) ≤ 64 * K * C₂ * Q := by positivity
        have h5 : (1 / 2) * (Q₀ / Q) * (64 * K * C₂ * Q) ≤ L₂ ^ (-(6 / 7 : ℝ)) * (64 * K * C₂ * Q) :=
          mul_le_mul_of_nonneg_right h1 h4
        linarith [h2, h5]
      have h6 := mul_le_mul_of_nonneg_left hm hc.le
      have h7 : c * (L₂ ^ (-(6 / 7 : ℝ)) * (64 * K * C₂ * Q)) =
          (c * L₂ ^ (-(6 / 7 : ℝ))) * (64 * K * C₂ * Q) := by ring
      linarith [h6, h7]
    have hup : 1 - σ ≤ c / (256 * K * C₂) / Q := by
      calc 1 - σ ≤ c' / Q := hδle
        _ ≤ (c / (256 * K * C₂)) / Q := div_le_div_of_nonneg_right hc'2 hQpos.le
    have hstrict : c / (256 * K * C₂) / Q < c / (64 * K * C₂) / Q := by
      apply div_lt_div_of_pos_right _ hQpos
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have h64 : (64 * K * C₂ : ℝ) < 256 * K * C₂ := by
        have h : (0:ℝ) < 192 * K * C₂ := by positivity
        linarith
      exact mul_lt_mul_of_pos_left h64 hc
    linarith [hδ8, hlow, hup, hstrict]


/-- **Assembly.**  The whole zero-free region follows from the two ingredients: the strip
logarithmic-derivative bounds `VKStrip` produced from the growth bound (for heights `|t| ≥ 10`)
and the bounded-height de la Vallée Poussin region (for `3 ≤ |t| ≤ 10`). -/
private theorem vk_final (A c₅ : ℝ) (hgr : VKGrowth A c₅)
    (hstrip : ∃ E : ℝ, 0 < E ∧ VKStrip ((min c₅ 1) / 4) E)
    (hsmall : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → ∀ σ t : ℝ, 3 ≤ |t| → |t| ≤ 10 →
        1 - c / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ σ t : ℝ, 3 ≤ |t| →
        1 - c / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨hA, hc₅, hgrV⟩ := hgr
  have hgr' : VKGrowth (max A 1) (min c₅ 1) := by
    refine ⟨lt_of_lt_of_le one_pos (le_max_right _ _), lt_min hc₅ one_pos, ?_⟩
    intro N hN χ σ t ht hσ hσ2
    have hlogpos : 0 < Real.log (|t| + 3) := Real.log_pos (by have := abs_nonneg t; linarith)
    have hlogp : 0 < Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) := Real.rpow_pos_of_pos hlogpos _
    have hle : min c₅ 1 ≤ c₅ := min_le_left _ _
    have hσ' : 1 - c₅ * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ := by
      nlinarith [hσ, hle, hlogp]
    have hbound := hgrV N χ σ t ht hσ' hσ2
    have h1 : A * (N : ℝ) ≤ max A 1 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left A 1) (by positivity)
    have h2 : A * (N : ℝ) * Real.log (|t| + 3) ^ (6 / 7 : ℝ) ≤
        max A 1 * (N : ℝ) * Real.log (|t| + 3) ^ (6 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    linarith [hbound, h2]
  have hc : (0:ℝ) < min c₅ 1 / 4 := by positivity
  have hc1 : min c₅ 1 / 4 ≤ 1 := by
    have h : min c₅ 1 ≤ 1 := min_le_right _ _
    linarith
  obtain ⟨E, hE, hstripV⟩ := hstrip
  obtain ⟨c₁, hc₁pos, h₁⟩ := zeroFree_of_VKStrip ((min c₅ 1) / 4) E hc hc1 hE hstripV
  obtain ⟨c₂, hc₂pos, h₂⟩ := hsmall
  refine ⟨min c₁ c₂, lt_min hc₁pos hc₂pos, ?_⟩
  intro N hN χ hprim σ t ht hσ
  haveI : NeZero N := hN
  have hlogTpos : 0 < Real.log (|t| + 3) := Real.log_pos (by have := abs_nonneg t; linarith)
  have hlogT1 : 1 ≤ Real.log (|t| + 3) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1)
      (by have := abs_nonneg t; linarith [Real.exp_one_lt_three])
  have hloglog0 : 0 ≤ Real.log (Real.log (|t| + 3)) := Real.log_nonneg hlogT1
  have hN2 : 1 ≤ Real.log ((N : ℝ) + 2) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have h2 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    linarith [Real.exp_one_lt_three]
  have hQpos : 0 < Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
      (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3))) := by positivity
  by_cases hle : |t| ≤ 10
  · refine h₂ N χ hprim σ t ht hle ?_
    have hm : min c₁ c₂ ≤ c₂ := min_le_right _ _
    have h3 : c₂ / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≥
        min c₁ c₂ / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) :=
      div_le_div_of_nonneg_right hm hQpos.le
    linarith [hσ, h3]
  · push_neg at hle
    refine h₁ N χ hprim σ t (le_of_lt hle) ?_
    have hm : min c₁ c₂ ≤ c₁ := min_le_left _ _
    have h3 : c₁ / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≥
        min c₁ c₂ / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
        (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) :=
      div_le_div_of_nonneg_right hm hQpos.le
    linarith [hσ, h3]

/-- **V3. Zero-free region of Vinogradov–Korobov type (exponent `6/7`)** for every *primitive*
character mod `N`, including the trivial character mod `1` (`L = ζ`), at heights `|t| ≥ 3`:
`L(σ + it, χ) ≠ 0` for `σ ≥ 1 − c / ((log(|t|+3))^{6/7} (log(N+2) + log log(|t|+3)))`. -/
theorem LFunction_zeroFree_VK_of_growth (hg : ∃ A c : ℝ, VKGrowth A c) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ σ t : ℝ, 3 ≤ |t| →
        1 - c / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨A, c₅, hgr0⟩ := hg
  have hgr : VKGrowth A c₅ := hgr0
  obtain ⟨hA, hc₅, hgrV⟩ := hgr0
  have hgr' : VKGrowth (max A 1) (min c₅ 1) := by
    refine ⟨lt_of_lt_of_le one_pos (le_max_right _ _), lt_min hc₅ one_pos, ?_⟩
    intro N hN χ σ t ht hσ hσ2
    have hlogpos : 0 < Real.log (|t| + 3) := Real.log_pos (by have := abs_nonneg t; linarith)
    have hlogp : 0 < Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) := Real.rpow_pos_of_pos hlogpos _
    have hle : min c₅ 1 ≤ c₅ := min_le_left _ _
    have hσ' : 1 - c₅ * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ := by nlinarith [hσ, hle, hlogp]
    have hbound := hgrV N χ σ t ht hσ' hσ2
    have h1 : A * (N : ℝ) ≤ max A 1 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left A 1) (by positivity)
    have h2 : A * (N : ℝ) * Real.log (|t| + 3) ^ (6 / 7 : ℝ) ≤
        max A 1 * (N : ℝ) * Real.log (|t| + 3) ^ (6 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    linarith [hbound, h2]
  exact vk_final A c₅ hgr (LFunction_strip_VK (max A 1) (min c₅ 1) hgr')
    zeroFree_bounded_height_chi

end Work.BMF


/-! # V3' (copied from `Submission/Work/BMF/LFunction_zeroFree_VK.lean`)

This is the zero-free region node V3 (`Work.BMF.LFunction_zeroFree_VK`), copied here with the
V2 input `L_growth_VK` replaced by a *hypothesis* `hg : ∃ A c, VKGrowth A c`, so that it can be
used before the sibling file `L_growth_VK.lean` builds (it imports a broken statement).  The extra
theorem at the end is `LFunction_zeroFree_VK_of_growth`.
-/
