import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.acH_lower
import Submission.Work.BW.num_kum
import Submission.Work.BW.split_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The remaining numerical inputs of BW (15) at level `J` (with `h = acH K b v`, `d = dK K`, `D = acD K σ`, `D_j = pDj r d σ j`, `D₀ = pD0 r d σ`): `d·σ_j·D_j ≤ D`; `∑_j D_j·logHeight₁(α'_j) ≤ D` (uses `logHeight₁(α'_j) ≤ dσ_j` from `BH`); `(D₀+1) ≤ 0.007·D·(57rd)/d`; and the Kummer term dominates, `2·J·h·(D₀+1)·d·log 2 ≤ kumJ K b v σ J`. Siblings `sigma_ge`, `acH_lower`, `one_le_dK`, `num_kum`, `pD0_succ_mul_log_le`, `one_le_pDj` supply the ingredients. -/
theorem num_est15_slacks {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) :
    (∀ j : Fin r, (dK K : ℝ) * σ j * (pDj r (dK K) σ j : ℝ) ≤ acD K σ) ∧
      (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) * Height.logHeight₁ (α' j) ≤ acD K σ) ∧
      (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) ≤ 0.007 * acD K σ * (57 * r * (dK K : ℝ)) / (dK K : ℝ) ∧
      (2 * J * (acH K b v) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * (dK K : ℝ) * Real.log 2
        ≤ kumJ K b v σ J) := by
  have hr : 2 ≤ r := H.hr
  have hd : 1 ≤ dK K := Module.finrank_pos
  have hdpos : (0 : ℝ) < (dK K : ℝ) := by exact_mod_cast hd
  have hrR : (0 : ℝ) < (r : ℝ) := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by linarith
  have hσ : ∀ j : Fin r, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
  obtain ⟨-, -, -, -, hσpos, hσbound, -⟩ := H.hBH
  have hlogH : ∀ j : Fin r, Height.logHeight₁ (α' j) ≤ (dK K : ℝ) * σ j := by
    intro j
    have h := hσbound j
    rw [hmod] at h
    have h1 : Height.logHeight₁ (α' j) / (dK K : ℝ) ≤ σ j :=
      le_trans (le_max_left _ _) h
    rw [div_le_iff₀ hdpos] at h1
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `d·σ_j·D_j ≤ D`
    intro j
    have hle := pDj_le hr hd σ hσ j
    have hrdσ : (0 : ℝ) < (r : ℝ) * (dK K : ℝ) * σ j :=
      mul_pos (mul_pos hrR hdpos) (hσpos j)
    have h1 : (pDj r (dK K) σ j : ℝ) * ((r : ℝ) * (dK K : ℝ) * σ j) ≤ pD r (dK K) σ := by
      rwa [le_div_iff₀ hrdσ] at hle
    have hP : (0 : ℝ) ≤ (pDj r (dK K) σ j : ℝ) := Nat.cast_nonneg _
    have hmnn : (0 : ℝ) ≤ (dK K : ℝ) * σ j * (pDj r (dK K) σ j : ℝ) :=
      mul_nonneg (mul_nonneg (le_of_lt hdpos) (le_of_lt (hσpos j))) hP
    calc (dK K : ℝ) * σ j * (pDj r (dK K) σ j : ℝ)
        = 1 * ((dK K : ℝ) * σ j * (pDj r (dK K) σ j : ℝ)) := by ring
      _ ≤ (r : ℝ) * ((dK K : ℝ) * σ j * (pDj r (dK K) σ j : ℝ)) :=
            mul_le_mul_of_nonneg_right hr1 hmnn
      _ = (pDj r (dK K) σ j : ℝ) * ((r : ℝ) * (dK K : ℝ) * σ j) := by ring
      _ ≤ pD r (dK K) σ := h1
  · -- `∑_j D_j·logHeight₁(α'_j) ≤ D`
    have hterm : ∀ j : Fin r, (pDj r (dK K) σ j : ℝ) * Height.logHeight₁ (α' j)
        ≤ pD r (dK K) σ / (r : ℝ) := by
      intro j
      have hle := pDj_le hr hd σ hσ j
      have hrdσ : (0 : ℝ) < (r : ℝ) * (dK K : ℝ) * σ j :=
        mul_pos (mul_pos hrR hdpos) (hσpos j)
      have h1 : (pDj r (dK K) σ j : ℝ) * ((r : ℝ) * (dK K : ℝ) * σ j) ≤ pD r (dK K) σ := by
        rwa [le_div_iff₀ hrdσ] at hle
      have hP : (0 : ℝ) ≤ (pDj r (dK K) σ j : ℝ) := Nat.cast_nonneg _
      calc (pDj r (dK K) σ j : ℝ) * Height.logHeight₁ (α' j)
          ≤ (pDj r (dK K) σ j : ℝ) * ((dK K : ℝ) * σ j) :=
              mul_le_mul_of_nonneg_left (hlogH j) hP
        _ ≤ pD r (dK K) σ / (r : ℝ) := by
              rw [le_div_iff₀ hrR]
              have heq : (pDj r (dK K) σ j : ℝ) * ((dK K : ℝ) * σ j) * (r : ℝ)
                  = (pDj r (dK K) σ j : ℝ) * ((r : ℝ) * (dK K : ℝ) * σ j) := by ring
              rw [heq]
              exact h1
    calc (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) * Height.logHeight₁ (α' j))
        ≤ ∑ j : Fin r, pD r (dK K) σ / (r : ℝ) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = pD r (dK K) σ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
  · -- `(D₀ + 1) ≤ 0.007·D·(57·r·d)/d`
    have hL43 : (4 : ℝ)/3 ≤ Real.log (2 * (r:ℝ) * (dK K : ℝ)) := log_2rd_ge hr hd
    have hD0 := pD0_le hr hd σ hσ
    have hDlow := pD_low hr hd σ hσ
    have hd1 : (1:ℝ) ≤ (dK K : ℝ) := by exact_mod_cast hd
    have hrr : (4:ℝ) ≤ (r:ℝ)^r := by
      have h1 : (2:ℝ)^(2:ℕ) ≤ (r:ℝ)^(2:ℕ) := pow_le_pow_left₀ (by norm_num) hr2 2
      have h2 : (r:ℝ)^(2:ℕ) ≤ (r:ℝ)^r := pow_le_pow_right₀ (by linarith) hr
      calc (4:ℝ) = (2:ℝ)^(2:ℕ) := by norm_num
        _ ≤ (r:ℝ)^(2:ℕ) := h1
        _ ≤ (r:ℝ)^r := h2
    have h32 : (32:ℝ) ≤ (32:ℝ)^(r+1) := by
      have h3 : 1 ≤ r + 1 := by omega
      have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 32) h3
      simpa using hh
    have hDge : (341:ℝ) ≤ pD r (dK K) σ := by
      have hA : (8:ℝ) ≤ 2 * (r:ℝ)^r := by linarith
      have hB : (256:ℝ) ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) := by
        have h := mul_le_mul hA h32 (by norm_num) (by positivity)
        linarith
      have hC : (256:ℝ) ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (dK K : ℝ) := by
        have h := mul_le_mul hB hd1 (by norm_num) (by positivity)
        linarith
      have hE : (341:ℝ) ≤ 2 * (r:ℝ)^r * (32:ℝ)^(r+1) * (dK K : ℝ)
          * Real.log (2 * (r:ℝ) * (dK K : ℝ)) := by
        have h := mul_le_mul hC hL43 (by norm_num) (by positivity)
        linarith
      linarith
    have hRD : (42:ℝ) ≤ (r:ℝ) * pD r (dK K) σ := by
      have h := mul_le_mul hr2 hDge (by norm_num) (by positivity)
      linarith
    have hup : (pD0 r (dK K) σ : ℝ) ≤ 0.375 * ((r:ℝ) * pD r (dK K) σ) := by
      have hAnn : (0:ℝ) ≤ (r:ℝ) * pD r (dK K) σ := by positivity
      have hstep : (r:ℝ) * pD r (dK K) σ / (2 * Real.log (2 * (r:ℝ) * (dK K : ℝ)))
          ≤ (r:ℝ) * pD r (dK K) σ / (2 * (4/3)) :=
        div_le_div_of_nonneg_left hAnn (by norm_num) (by linarith)
      calc (pD0 r (dK K) σ : ℝ)
          ≤ (r:ℝ) * pD r (dK K) σ / (2 * Real.log (2 * (r:ℝ) * (dK K : ℝ))) := hD0
        _ ≤ (r:ℝ) * pD r (dK K) σ / (2 * (4/3)) := hstep
        _ = 0.375 * ((r:ℝ) * pD r (dK K) σ) := by norm_num; ring
    have h2 : (1:ℝ) ≤ 0.024 * ((r:ℝ) * pD r (dK K) σ) := by linarith
    have hfin : ((pD0 r (dK K) σ : ℝ) + 1) ≤ 0.399 * ((r:ℝ) * pD r (dK K) σ) := by linarith
    have heq : 0.007 * pD r (dK K) σ * (57 * (r : ℝ) * (dK K : ℝ)) / (dK K : ℝ)
        = 0.399 * ((r : ℝ) * pD r (dK K) σ) := by
      field_simp
      ring
    rw [heq]
    exact hfin
  · -- the `2`-adic (Kummer) term
    have hh : 19 ≤ acH K b v := (acH_lower H).1
    have hnum := (num_kum hr hd hh σ hσ J).2.1
    have hnum' : 2 * (dK K : ℝ) * (J : ℝ) * (acH K b v : ℝ)
          * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * Real.log 2 ≤ kumJ K b v σ J := by
      rw [show kumJ K b v σ J
          = 0.044 * (J : ℝ) / Real.log (2 * (r : ℝ) * (dK K : ℝ))
              * (pS r (dK K) (acH K b v) : ℝ) * pD r (dK K) σ from rfl]
      exact hnum
    calc 2 * (J : ℝ) * (acH K b v : ℝ) * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1)
            * (dK K : ℝ) * Real.log 2
        = 2 * (dK K : ℝ) * (J : ℝ) * (acH K b v : ℝ)
            * (((pD0 r (dK K) σ : ℕ) : ℝ) + 1) * Real.log 2 := by ring
      _ ≤ kumJ K b v σ J := hnum'

end Work.BW
