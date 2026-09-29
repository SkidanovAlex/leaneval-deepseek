import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.geom
import Submission.Work.TMC16Core.Core.nr_defs

/-!
# Helpers for the assembly of `Core.pd_window`
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core
open Filter

lemma fracDist_nonneg' (x : ℝ) : 0 ≤ fracDist x := abs_nonneg _

lemma fracDist_eq_zero_iff' (x : ℝ) : fracDist x = 0 ↔ ∃ z : ℤ, x = (z : ℝ) := by
  rw [fracDist, abs_eq_zero, sub_eq_zero]
  constructor
  · intro hx; exact ⟨round x, hx⟩
  · rintro ⟨z, rfl⟩; exact_mod_cast (round_intCast z).symm

lemma theta_eventual {α θ : ℝ} (h : θ ∉ Theta α) :
    (∀ᶠ k : ℤ in atTop, ((((k.natAbs : ℕ) : ℝ))⁻¹)^2 ≤ fracDist (2 * θ + (k : ℝ) * α)) ∧
    (∀ᶠ k : ℤ in atBot, ((((k.natAbs : ℕ) : ℝ))⁻¹)^2 ≤ fracDist (2 * θ + (k : ℝ) * α)) ∧
    (∀ m : ℤ, 0 < fracDist (2 * θ + (m : ℝ) * α)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [not_lt] using
      (Filter.not_frequently.mp (fun hf => h (Or.inl hf)) :
        ∀ᶠ k : ℤ in atTop,
          ¬(fracDist (2 * θ + (k : ℝ) * α) < ((((k.natAbs : ℕ) : ℝ))⁻¹)^2))
  · simpa only [not_lt] using
      (Filter.not_frequently.mp (fun hf => h (Or.inr (Or.inl hf))) :
        ∀ᶠ k : ℤ in atBot,
          ¬(fracDist (2 * θ + (k : ℝ) * α) < ((((k.natAbs : ℕ) : ℝ))⁻¹)^2))
  · intro m
    rcases lt_or_eq_of_le (fracDist_nonneg' _) with hlt | heq
    · exact hlt
    · exfalso
      obtain ⟨z, hz⟩ := (fracDist_eq_zero_iff' _).mp heq.symm
      exact h (Or.inr (Or.inr ⟨m, z, hz⟩))

/-- A threshold `K₀` and a constant `csm > 0` such that `csm` bounds `fracDist (2θ+kα)` for
`|k| < K₀`, while the quantitative bound holds for `K₀ ≤ |k|`. -/
lemma theta_setup {α θ : ℝ} (h : θ ∉ Theta α) :
    ∃ K₀ : ℤ, 1 ≤ K₀ ∧ ∃ csm : ℝ, 0 < csm ∧ csm ≤ 1 / 2 ∧
      (∀ k : ℤ, |k| < K₀ → csm ≤ fracDist (2 * θ + (k : ℝ) * α)) ∧
      (∀ k : ℤ, K₀ ≤ |k| → ((((k.natAbs : ℕ) : ℝ))⁻¹)^2 ≤ fracDist (2 * θ + (k : ℝ) * α)) := by
  obtain ⟨h1, h2, h3⟩ := theta_eventual h
  obtain ⟨Ktop, hKtop⟩ := Filter.eventually_atTop.mp h1
  obtain ⟨Kbot, hKbot⟩ := Filter.eventually_atBot.mp h2
  have hSne : (Finset.Icc (-(max (max Ktop (-Kbot)) 1)) (max (max Ktop (-Kbot)) 1)).Nonempty := by
    refine ⟨0, ?_⟩
    rw [Finset.mem_Icc]
    constructor
    · have hM : (1 : ℤ) ≤ max (max Ktop (-Kbot)) 1 := le_max_right _ _
      linarith
    · exact le_trans (by norm_num : (0:ℤ) ≤ 1) (le_max_right _ _)
  obtain ⟨k₀, hk₀mem, hk₀min⟩ := Finset.exists_min_image
    (Finset.Icc (-(max (max Ktop (-Kbot)) 1)) (max (max Ktop (-Kbot)) 1))
    (fun k : ℤ => fracDist (2 * θ + (k : ℝ) * α)) hSne
  refine ⟨max (max Ktop (-Kbot)) 1, by omega,
    fracDist (2 * θ + (k₀ : ℝ) * α), h3 k₀, ?_, ?_, ?_⟩
  · exact abs_sub_round _
  · intro k hk
    apply hk₀min k
    rw [Finset.mem_Icc]
    rw [abs_lt] at hk
    exact ⟨le_of_lt hk.1, le_of_lt hk.2⟩
  · intro k hk
    have hkabs : max Ktop (-Kbot) ≤ |k| := by omega
    rcases le_or_gt 0 k with hk0 | hk0
    · have hkabs' : |k| = k := abs_of_nonneg hk0
      have hk' : Ktop ≤ k := by
        have h1 : Ktop ≤ max Ktop (-Kbot) := le_max_left _ _
        linarith
      simpa only [Int.cast_abs, Nat.cast_natAbs] using hKtop k hk'
    · have hkabs' : |k| = -k := abs_of_neg hk0
      have hk' : k ≤ Kbot := by
        have h1 : -Kbot ≤ max Ktop (-Kbot) := le_max_right _ _
        linarith
      simpa only [Int.cast_abs, Nat.cast_natAbs] using hKbot k hk'

/-- The `θ`-bound used by the uniformity estimate. -/
lemma theta_bound_of_setup {α θ : ℝ} {K₀ : ℤ} {csm : ℝ} (hK₀1 : 1 ≤ K₀) (hcsm : 0 < csm) (hcsm1 : csm ≤ 1)
    (h1 : ∀ k : ℤ, |k| < K₀ → csm ≤ fracDist (2 * θ + (k : ℝ) * α))
    (h2 : ∀ k : ℤ, K₀ ≤ |k| → ((((k.natAbs : ℕ) : ℝ))⁻¹)^2 ≤ fracDist (2 * θ + (k : ℝ) * α))
    {Bz : ℤ} (hBz : 1 ≤ Bz) :
    ∃ c : ℝ, 0 < c ∧
      (∀ k : ℤ, |k| ≤ Bz → c ≤ fracDist (2 * θ + (k : ℝ) * α)) ∧
      Real.log (1 / c) ≤ Real.log 2 + Real.log (1 / csm) + 2 * Real.log ((Bz : ℝ) + 1) := by
  have hBzR : (1 : ℝ) ≤ (Bz : ℝ) := by exact_mod_cast hBz
  have hB1 : (0 : ℝ) < (Bz : ℝ) + 1 := by linarith
  refine ⟨min csm (1 / ((Bz : ℝ) + 1) ^ 2), lt_min hcsm (by positivity), ?_, ?_⟩
  · intro k hk
    rcases lt_or_ge (|k|) K₀ with hlt | hge
    · exact le_trans (min_le_left _ _) (h1 k hlt)
    · have h2k := h2 k hge
      have hIk1 : (1 : ℝ) ≤ |((k : ℤ) : ℝ)| := by
        have h1' : (1 : ℤ) ≤ |k| := le_trans hK₀1 hge
        rw [← Int.cast_abs]; exact_mod_cast h1'
      have hIkpos : (0 : ℝ) < |((k : ℤ) : ℝ)| := by linarith
      have hkR : |((k : ℤ) : ℝ)| ≤ (Bz : ℝ) := by
        rw [← Int.cast_abs]; exact_mod_cast hk
      have hle : (((Bz : ℝ) + 1))⁻¹ ≤ (|((k : ℤ) : ℝ)|)⁻¹ := by
        rw [inv_le_inv₀ hB1 hIkpos]; linarith
      have hsq : (((Bz : ℝ) + 1))⁻¹ ^ 2 ≤ ((|((k : ℤ) : ℝ)|)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hle 2
      have heq : 1 / ((Bz : ℝ) + 1) ^ 2 = (((Bz : ℝ) + 1))⁻¹ ^ 2 := by
        rw [one_div, inv_pow]
      rw [Nat.cast_natAbs, Int.cast_abs] at h2k
      exact le_trans (min_le_right _ _) (le_trans (le_of_eq heq) (le_trans hsq h2k))
  · have hkey : 1 / min csm (1 / ((Bz : ℝ) + 1) ^ 2)
        ≤ 1 / csm + ((Bz : ℝ) + 1) ^ 2 := by
      rcases le_total csm (1 / ((Bz : ℝ) + 1) ^ 2) with hle | hle
      · rw [min_eq_left hle]
        have : (0 : ℝ) ≤ ((Bz : ℝ) + 1) ^ 2 := by positivity
        linarith
      · rw [min_eq_right hle, one_div, one_div, inv_inv]
        have : (0 : ℝ) < 1 / csm := by positivity
        linarith
    have hlog1 : Real.log (1 / min csm (1 / ((Bz : ℝ) + 1) ^ 2))
        ≤ Real.log (1 / csm + ((Bz : ℝ) + 1) ^ 2) :=
      Real.log_le_log (by positivity) hkey
    have hac : (1 : ℝ) ≤ 1 / csm := by
      rw [le_div_iff₀ hcsm, one_mul]; exact hcsm1
    have hb : (1 : ℝ) ≤ ((Bz : ℝ) + 1) ^ 2 := by nlinarith [hBzR]
    have h2ac : 1 / csm + ((Bz : ℝ) + 1) ^ 2 ≤ 2 * ((1 / csm) * ((Bz : ℝ) + 1) ^ 2) := by
      nlinarith [hac, hb, mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / csm)
        (by positivity : (0 : ℝ) ≤ ((Bz : ℝ) + 1) ^ 2)]
    have h3 : Real.log (2 * ((1 / csm) * ((Bz : ℝ) + 1) ^ 2))
        = Real.log 2 + Real.log (1 / csm) + 2 * Real.log ((Bz : ℝ) + 1) := by
      rw [Real.log_mul (by norm_num) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow]
      ring
    linarith [hlog1, Real.log_le_log (by positivity) h2ac, h3.le, h3.ge]

/-- Existence of a block level `m ≥ 1` at which the fixed terms of the uniformity rate are
`≤ εA/4` (and `q m ≥ 8/εA`). -/
lemma block_level_exists {q : ℕ → ℕ} (hq : ∀ m, 0 < q m) (hmono : StrictMono q)
    {εA : ℝ} (hεA : 0 < εA) :
    ∃ m : ℕ, 1 ≤ m ∧
      (4 * Real.log 2 + 200 * Real.log ((q m : ℝ) + 2) + 202) / (q m : ℝ) ≤ εA / 4 ∧
      8 / εA ≤ (q m : ℝ) := by
  set D : ℝ := 800 / εA with hD
  set E : ℝ := (4 / εA) * (4 * Real.log 2 + 202) with hE
  have hD0 : 0 < D := by rw [hD]; positivity
  have hE0 : 0 ≤ E := by
    rw [hE]
    apply mul_nonneg (by positivity)
    have := Real.log_pos (by norm_num : (1:ℝ) < 2)
    linarith
  set X : ℝ := max (64 * D ^ 2) (max (2 * E + 2) (max (8 / εA) 4)) with hX
  have hXpos : 0 < X := by
    rw [hX]
    have : 0 < 8 / εA := by positivity
    positivity
  refine ⟨Nat.ceil X, ?_, ?_, ?_⟩
  · have h1 : X ≤ ((Nat.ceil X : ℕ) : ℝ) := Nat.le_ceil X
    have h2 : (1 : ℝ) ≤ X := by
      rw [hX]
      have h4 : (4 : ℝ) ≤ max (8 / εA) 4 := le_max_right _ _
      have h4' : (4 : ℝ) ≤ max (2 * E + 2) (max (8 / εA) 4) := le_trans h4 (le_max_right _ _)
      have h4'' : (4 : ℝ) ≤ max (64 * D ^ 2) (max (2 * E + 2) (max (8 / εA) 4)) :=
        le_trans h4' (le_max_right _ _)
      linarith
    have : (1 : ℝ) ≤ ((Nat.ceil X : ℕ) : ℝ) := le_trans h2 h1
    exact_mod_cast this
  · have hmX : X ≤ ((Nat.ceil X : ℕ) : ℝ) := Nat.le_ceil X
    have hXm : X ≤ ((q (Nat.ceil X) : ℕ) : ℝ) :=
      le_trans hmX (by exact_mod_cast (StrictMono.id_le hmono (Nat.ceil X)))
    have hDbig : 64 * D ^ 2 ≤ (q (Nat.ceil X) : ℝ) := by
      rw [hX] at hXm
      exact le_trans (le_max_left _ _) hXm
    have hEbig : 2 * E + 2 ≤ (q (Nat.ceil X) : ℝ) := by
      rw [hX] at hXm
      exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hXm
    have hFbig : 8 / εA ≤ (q (Nat.ceil X) : ℝ) := by
      rw [hX] at hXm
      exact le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hXm
    have h4big : (4:ℝ) ≤ (q (Nat.ceil X) : ℝ) := by
      rw [hX] at hXm
      exact le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hXm
    have h2big : (2:ℝ) ≤ (q (Nat.ceil X) : ℝ) := le_trans (by norm_num) h4big
    set Q : ℝ := ((q (Nat.ceil X) : ℕ) : ℝ) with hQ
    have hQpos : 0 < Q := by rw [hQ]; positivity
    have hQ2 : 2 ≤ Q := h2big
    have hQ64 : 64 * D ^ 2 ≤ Q := hDbig
    have hlog : D * Real.log (Q + 2) ≤ Q / 2 := by
      have hx0 : (0 : ℝ) ≤ Q + 2 := by linarith
      have hlogb : Real.log (Q + 2) ≤ 2 * Real.sqrt (Q + 2) := by
        have h := Real.log_le_rpow_div hx0 (show (0 : ℝ) < 1 / 2 by norm_num)
        have h2 : (Q + 2) ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) = 2 * (Q + 2) ^ ((1 : ℝ) / 2) := by ring
        rw [h2] at h
        rwa [← Real.sqrt_eq_rpow] at h
      have hsqrt_ge : 8 * D ≤ Real.sqrt (Q + 2) := by
        rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 8 * D)]
        apply Real.sqrt_le_sqrt
        nlinarith [hQ64]
      have hsq : (Real.sqrt (Q + 2)) ^ 2 = Q + 2 := Real.sq_sqrt hx0
      have hsnn : 0 ≤ Real.sqrt (Q + 2) := Real.sqrt_nonneg _
      calc D * Real.log (Q + 2) ≤ D * (2 * Real.sqrt (Q + 2)) :=
            mul_le_mul_of_nonneg_left hlogb (le_of_lt hD0)
        _ = 2 * D * Real.sqrt (Q + 2) := by ring
        _ ≤ (Q + 2) / 4 := by nlinarith [hsqrt_ge, hsq, hsnn, hD0]
        _ ≤ Q / 2 := by linarith
    have hkey : 4 * Real.log 2 + 200 * Real.log (Q + 2) + 202 ≤ (εA / 4) * Q := by
      have h1 : D * Real.log (Q + 2) ≤ Q / 2 := hlog
      have h2 : E ≤ Q / 2 := by linarith [hEbig]
      have hsum : (4 / εA) * (4 * Real.log 2 + 202 + 200 * Real.log (Q + 2)) ≤ Q := by
        have expand : (800 / εA) * Real.log (Q + 2) ≤ Q / 2 := by rw [← hD]; exact h1
        have expand2 : (4 / εA) * (4 * Real.log 2 + 202) ≤ Q / 2 := by rw [← hE]; exact h2
        have heq : (4 / εA) * (4 * Real.log 2 + 202 + 200 * Real.log (Q + 2))
            = (4 / εA) * (4 * Real.log 2 + 202) + (800 / εA) * Real.log (Q + 2) := by ring
        rw [heq]; linarith
      have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : (0:ℝ) ≤ εA / 4)
      have he : (εA / 4) * ((4 / εA) * (4 * Real.log 2 + 202 + 200 * Real.log (Q + 2)))
          = 4 * Real.log 2 + 202 + 200 * Real.log (Q + 2) := by field_simp
      rw [he] at hmul
      nlinarith [hmul]
    have hqmpos : (0 : ℝ) < ((q (Nat.ceil X) : ℕ) : ℝ) := by positivity
    rw [hQ] at hkey
    rw [div_le_iff₀ hqmpos]
    exact hkey
  · have hmX : X ≤ ((Nat.ceil X : ℕ) : ℝ) := Nat.le_ceil X
    have hXm : X ≤ ((q (Nat.ceil X) : ℕ) : ℝ) :=
      le_trans hmX (by exact_mod_cast (StrictMono.id_le hmono (Nat.ceil X)))
    have hFbig : 8 / εA ≤ (q (Nat.ceil X) : ℝ) := by
      rw [hX] at hXm
      exact le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hXm
    exact hFbig


end Work.TMC16Core.Core


