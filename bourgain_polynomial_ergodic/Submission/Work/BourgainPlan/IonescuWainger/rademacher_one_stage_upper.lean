import Mathlib
import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert

set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

open Finset

private lemma card_bool_fun {κ : Type*} [Fintype κ] [DecidableEq κ] :
    Fintype.card (κ → Bool) = 2 ^ Fintype.card κ := by
  rw [Fintype.card_fun, Fintype.card_bool]

/-- One-stage Khintchine upper bound on `Fin n` with values in `ℂ`, raised to the `p`-th power. -/
private lemma khintchine_fin_real (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x : Fin n → ℂ),
      (∑ ε : Fin n → Bool, ‖∑ i : Fin n, (if ε i then (1 : ℂ) else -1) • x i‖ ^ p)
          / (2 : ℝ) ^ n
        ≤ C * (∑ i : Fin n, ‖x i‖ ^ 2) ^ (p / 2) := by
  obtain ⟨c, C₀, hc, hC₀, hK⟩ := Commons.Analysis.Walsh.exists_khintchine_hilbert p hp
  refine ⟨(C₀ * p ^ ((1 : ℝ) / 2)) ^ p, by positivity, ?_⟩
  intro n x
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hZ0 : (0 : ℝ) ≤ ∑ i : Fin n, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hA0 : (0 : ℝ) ≤ (∑ ε : Fin n → Bool,
        ‖∑ i : Fin n, (if ε i then (1 : ℂ) else -1) • x i‖ ^ p) / (2 : ℝ) ^ n :=
    div_nonneg (Finset.sum_nonneg fun ε _ => Real.rpow_nonneg (norm_nonneg _) p) (by positivity)
  have hup := (hK (H := ℂ) n x).2
  have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hA0 _) hup hp0.le
  rw [← Real.rpow_mul hA0, show (1 : ℝ) / p * p = 1 by
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hp0)], Real.rpow_one] at h1
  have hmr : (C₀ * p ^ ((1 : ℝ) / 2) * (∑ i : Fin n, ‖x i‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ p
      = (C₀ * p ^ ((1 : ℝ) / 2)) ^ p
        * ((∑ i : Fin n, ‖x i‖ ^ 2) ^ ((1 : ℝ) / 2)) ^ p :=
    Real.mul_rpow (mul_nonneg hC₀.le (Real.rpow_nonneg hp0.le _)) (Real.rpow_nonneg hZ0 _)
  rw [hmr] at h1
  rw [← Real.rpow_mul hZ0, show (1 : ℝ) / 2 * p = p / 2 by ring] at h1
  exact h1

/-- Real-valued general-index-set form of the one-stage Rademacher (Khintchine) upper bound. -/
private lemma khintchine_real (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℂ),
      (∑ η : κ → Bool, ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ ^ p)
          / (Fintype.card (κ → Bool) : ℝ)
        ≤ C * (∑ t : κ, ‖a t‖ ^ 2) ^ (p / 2) := by
  obtain ⟨C, hC, hfin⟩ := khintchine_fin_real p hp
  refine ⟨C, hC, ?_⟩
  intro κ _ _ a
  classical
  set e := Fintype.equivFin κ with he
  set x : Fin (Fintype.card κ) → ℂ := fun i => a (e.symm i) with hx
  have hbullet : (∑ η : κ → Bool, ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ ^ p)
      = (∑ η : κ → Bool, ‖∑ t : κ, (if η t then (1 : ℂ) else -1) • a t‖ ^ p) := by
    apply Finset.sum_congr rfl
    intro η _
    simp only [smul_eq_mul]
  have hsum : (∑ η : κ → Bool, ‖∑ t : κ, (if η t then (1 : ℂ) else -1) • a t‖ ^ p)
      = (∑ ε : Fin (Fintype.card κ) → Bool,
          ‖∑ i : Fin (Fintype.card κ), (if ε i then (1 : ℂ) else -1) • x i‖ ^ p) := by
    refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl Bool))
      (fun η : κ → Bool => ‖∑ t : κ, (if η t then (1 : ℂ) else -1) • a t‖ ^ p)
      (fun ε : Fin (Fintype.card κ) → Bool =>
        ‖∑ i : Fin (Fintype.card κ), (if ε i then (1 : ℂ) else -1) • x i‖ ^ p) ?_
    intro η
    congr 1
    have hpt : ∀ i : Fin (Fintype.card κ), (e.arrowCongr (Equiv.refl Bool)) η i = η (e.symm i) := by
      intro i
      rw [Equiv.arrowCongr_apply]
      rfl
    simp only [hpt, hx]
    rw [← Equiv.sum_comp e.symm (fun t : κ => (if η t then (1 : ℂ) else -1) • a t)]
  have hcardR : ((Fintype.card (κ → Bool) : ℕ) : ℝ) = (2 : ℝ) ^ Fintype.card κ := by
    rw [card_bool_fun]
    push_cast
    ring
  have hZ : (∑ i : Fin (Fintype.card κ), ‖x i‖ ^ 2) = ∑ t : κ, ‖a t‖ ^ 2 := by
    rw [hx]
    simp only []
    exact Equiv.sum_comp e.symm (fun t : κ => ‖a t‖ ^ 2)
  have hfin' := hfin (Fintype.card κ) x
  have hgoal : (∑ η : κ → Bool, ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ ^ p)
        / (Fintype.card (κ → Bool) : ℝ)
      ≤ C * (∑ i : Fin (Fintype.card κ), ‖x i‖ ^ 2) ^ (p / 2) := by
    rw [hbullet, hsum, hcardR]
    exact hfin'
  rwa [hZ] at hgoal



/-- **One-stage Rademacher (Khintchine) upper bound.** For every `p ≥ 1` there is `C > 0` such that
for every finite index type `κ` and every `a : κ → ℂ`,

`avg_{η : κ→Bool} |Σ_t η_t a_t|^p ≤ C * (Σ_t ‖a_t‖²)^{p/2}`,

where `‖z‖ₑ` is the `ENNReal`-valued norm and the average is the sum over all `2^|κ|` sign choices
divided by `card (κ → Bool)` (written as multiplication by `(card (κ→Bool))⁻¹` in `ENNReal`).  The
constant `C` is uniform in `κ` and `a`.  `ENNReal` is written out because the notation `ℝ≥0∞` is
scoped (`open scoped ENNReal`); the `DecidableEq` hypothesis is only there so that
`Fintype (κ → Bool)` is available for the sum (callers pass it via `classical`). -/
theorem rademacher_one_stage_upper (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] (a : κ → ℂ),
      (∑ η : κ → Bool, ‖∑ t, (if η t then (1 : ℂ) else -1) * a t‖ₑ ^ p)
          * (Fintype.card (κ → Bool) : ENNReal)⁻¹
        ≤ ENNReal.ofReal C * (∑ t, ‖a t‖ₑ ^ (2 : ℝ)) ^ (p / 2) := by
  obtain ⟨C, hC, hreal⟩ := khintchine_real p hp
  refine ⟨C, hC, ?_⟩
  intro κ _ _ a
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp2 : (0 : ℝ) ≤ p / 2 := div_nonneg hp0.le (by norm_num)
  have hMpos : 0 < Fintype.card (κ → Bool) := Fintype.card_pos_iff.mpr ⟨fun _ => true⟩
  have hMposR : (0 : ℝ) < (Fintype.card (κ → Bool) : ℝ) := by exact_mod_cast hMpos
  have hInvnn : (0 : ℝ) ≤ (Fintype.card (κ → Bool) : ℝ)⁻¹ := inv_nonneg.mpr hMposR.le
  have hsumN : (0 : ℝ) ≤ ∑ η : κ → Bool,
      ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ ^ p :=
    Finset.sum_nonneg fun η _ => Real.rpow_nonneg (norm_nonneg _) p
  have hZnn : (0 : ℝ) ≤ ∑ t : κ, ‖a t‖ ^ 2 := Finset.sum_nonneg fun t _ => by positivity
  have hL : (∑ η : κ → Bool, ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ₑ ^ p)
        * (Fintype.card (κ → Bool) : ENNReal)⁻¹
      = ENNReal.ofReal ((∑ η : κ → Bool,
            ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ ^ p)
          / (Fintype.card (κ → Bool) : ℝ)) := by
    have hpt : ∀ η : κ → Bool, ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ₑ ^ p
        = ENNReal.ofReal (‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ ^ p) := by
      intro η
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    have h1 : (∑ η : κ → Bool, ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ₑ ^ p)
        = ENNReal.ofReal (∑ η : κ → Bool,
            ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ ^ p) := by
      rw [Finset.sum_congr rfl (fun η (_ : η ∈ Finset.univ) => hpt η)]
      rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun η : κ → Bool => ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ ^ p)
        (fun η _ => Real.rpow_nonneg (norm_nonneg _) p)]
    have h2 : (Fintype.card (κ → Bool) : ENNReal)⁻¹
        = ENNReal.ofReal ((Fintype.card (κ → Bool) : ℝ)⁻¹) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hMposR]
    have h3 : ENNReal.ofReal (∑ η : κ → Bool,
            ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ ^ p)
          * ENNReal.ofReal ((Fintype.card (κ → Bool) : ℝ)⁻¹)
        = ENNReal.ofReal ((∑ η : κ → Bool,
            ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ ^ p)
            * (Fintype.card (κ → Bool) : ℝ)⁻¹) := by
      rw [← ENNReal.ofReal_mul (p := ∑ η : κ → Bool,
          ‖∑ t : κ, (if η t then (1 : ℂ) else -1) * a t‖ ^ p)
        (q := (Fintype.card (κ → Bool) : ℝ)⁻¹) hsumN]
    rw [h1, h2, h3, div_eq_mul_inv]
  have hR : ENNReal.ofReal C * (∑ t : κ, ‖a t‖ₑ ^ (2 : ℝ)) ^ (p / 2)
      = ENNReal.ofReal (C * (∑ t : κ, ‖a t‖ ^ 2) ^ (p / 2)) := by
    have hpt : ∀ t : κ, ‖a t‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖a t‖ ^ (2 : ℝ)) := by
      intro t
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    have hZ : (∑ t : κ, ‖a t‖ₑ ^ (2 : ℝ)) = ENNReal.ofReal (∑ t : κ, ‖a t‖ ^ 2) := by
      rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => hpt t)]
      rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun t : κ => ‖a t‖ ^ (2 : ℝ)) (fun t _ => Real.rpow_nonneg (norm_nonneg _) 2)]
      congr 1
      exact Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => Real.rpow_natCast (‖a t‖) 2)
    have h2 : (ENNReal.ofReal (∑ t : κ, ‖a t‖ ^ 2)) ^ (p / 2)
        = ENNReal.ofReal ((∑ t : κ, ‖a t‖ ^ 2) ^ (p / 2)) :=
      ENNReal.ofReal_rpow_of_nonneg hZnn hp2
    have h3 : ENNReal.ofReal C * ENNReal.ofReal ((∑ t : κ, ‖a t‖ ^ 2) ^ (p / 2))
        = ENNReal.ofReal (C * (∑ t : κ, ‖a t‖ ^ 2) ^ (p / 2)) := by
      rw [← ENNReal.ofReal_mul (p := C) (q := (∑ t : κ, ‖a t‖ ^ 2) ^ (p / 2)) hC.le]
    rw [hZ, h2, h3]
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal (hreal a)
end Work.BourgainPlan.IonescuWainger
