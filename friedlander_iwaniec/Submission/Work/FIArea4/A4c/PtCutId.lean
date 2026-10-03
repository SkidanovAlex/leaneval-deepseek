import Mathlib
import Submission.Work.FIArea4.A4c.Defs

namespace Work.FIArea4.A4c

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Telescoping of the bump `psiA` over the dyadic scales `2^j`:
`Σ_{j<J} psiA(c/2^j) = uA c − uA(c/2^J)` (`psiA s = uA s − uA(s/2)`). -/
lemma sum_range_psiA (c : ℝ) (J : ℕ) :
    ∑ j ∈ Finset.range J, psiA (c / 2 ^ j) = uA c - uA (c / 2 ^ J) := by
  have htel : ∀ N : ℕ, ∑ j ∈ Finset.range N, psiA (c / 2 ^ j) = uA (c / 2 ^ 0) - uA (c / 2 ^ N) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, psiA_apply]
      have : c / 2 ^ n / 2 = c / 2 ^ (n + 1) := by rw [div_div, ← pow_succ]
      rw [this]; ring
  simpa using htel J

/-- The two indicator halves of a strict/equality alternative on `ℕ` add up to the closed
indicator: `1{a>b} + 1{a=b} = 1{b≤a}`, inside a common constraint `R`. -/
lemma ind_pair (R : Prop) [Decidable R] (a b : ℕ) :
    (if R ∧ a > b then (1 : ℝ) else 0) + (if R ∧ a = b then (1 : ℝ) else 0)
      = if R ∧ b ≤ a then (1 : ℝ) else 0 := by
  by_cases hR : R
  · by_cases hab : a > b
    · rw [if_pos ⟨hR, hab⟩, if_neg (by rintro ⟨_, h⟩; omega), if_pos ⟨hR, by omega⟩]; norm_num
    · by_cases hab2 : a = b
      · rw [if_neg (by rintro ⟨_, h⟩; omega), if_pos ⟨hR, hab2⟩, if_pos ⟨hR, by omega⟩]; norm_num
      · rw [if_neg (by rintro ⟨_, h⟩; omega), if_neg (by rintro ⟨_, h⟩; omega),
            if_neg (by rintro ⟨_, h⟩; omega)]; norm_num
  · rw [if_neg (by rintro ⟨h, _⟩; exact hR h), if_neg (by rintro ⟨h, _⟩; exact hR h),
        if_neg (by rintro ⟨h, _⟩; exact hR h)]; norm_num

/-- `1 − 1{P} = 1{¬P}` for the real-valued indicator. -/
lemma one_sub_ind (P : Prop) [Decidable P] : (1 : ℝ) - (if P then 1 else 0) = if ¬P then 1 else 0 := by
  by_cases h : P <;> simp [h]

/-- **The per-point cut identity of the amended route (design `AREA4_ENGINES_LEAD.md` §3.2, the
pointwise core of node N6).**  For a single pair `(z₁,z₂)` and modulus `d`, this is the value at
that point of the exact splitting `Vcut = Σ_j A6cut ψ − (Wcut + Bcut) + Σ_m wA·(Wcut_m+Bcut_m−junk)`
(`Work.FIArea4.A4c.Vcut_eq_A4c`).  It is pure cut algebra, uniform in the remaining discrete data:

* if `X ≥ d` every term vanishes (the `junkCut` absorbs the middle `m`-terms: for `d ≤ X` the cut
  `1{m<d}·1{|Δ| ≤ 4dm}` *is* `Wcut_m + Bcut_m`);
* if `X < d`, the `j`-sum telescopes to `uA(|Δ|/(4Xd)) − uA(|Δ|/(4Xd·2^J))`, the `Wcut+Bcut` term is
  `1{|Δ| ≤ 4dX}` and the `m`-sum is `1 − uA(|Δ|/(4Xd))` (`one_sub_uA_div`); the hypothesis `hJd`
  makes the surviving `uA(|Δ|/(4Xd·2^J))` vanish. -/
theorem PtCutId (X : ℕ) (hX : 2 ≤ X) (z1 z2 : GaussianInt) (d : ℕ) (hd1 : 1 ≤ d)
    (hdvd : 4 * d ∣ Work.FIPlan.absDelta z1 z2) (J : ℕ)
    (hJd : 2 * ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ))) ≤ 2 ^ J) :
    (∑ j ∈ Finset.range J, (if X < d then
        Work.FIArea4.A4c.psiA ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) else 0))
      - ((if X < d ∧ 4 * d * X > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
          + (if X < d ∧ 4 * d * X = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0))
      + ∑ m ∈ Finset.Ico 1 X, Work.FIArea4.A4c.wA X m *
          (((if m < d ∧ 4 * d * m > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0)
            + (if m < d ∧ 4 * d * m = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0))
           - Work.FIArea4.A4c.junkCut X m z1 z2 d)
    = (if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) := by
  obtain ⟨n, hn⟩ := hdvd
  have hXr : (X : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < X := by omega
    exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
  have hdr : (d : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < d := by omega
    exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
  have hc4 : (0 : ℕ) < 4 * d := by omega
  have hterm : ∀ j : ℕ, ((4 * d * n : ℕ) : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))
      = ((n : ℝ) / (X : ℝ)) / 2 ^ j := by
    intro j
    have h2 : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    field_simp
  have hle : ∀ k : ℕ, (4 * d * n ≤ 4 * d * k ↔ n ≤ k) := by
    intro k
    constructor
    · intro h; exact Nat.le_of_mul_le_mul_left h hc4
    · intro h; exact Nat.mul_le_mul_left (4 * d) h
  have hltn : (4 * d * X < 4 * d * n ↔ X < n) := Nat.mul_lt_mul_left hc4
  have hc : ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ))) = (n : ℝ) / (X : ℝ) := by
    rw [hn]; push_cast; field_simp
  simp only [Work.FIArea4.A4c.junkCut]
  rw [hn]
  by_cases hlt : X < d
  · -- `X < d`: the `j`-sum survives, the `junkCut` vanishes
    have hsum1 : (∑ j ∈ Finset.range J, (if X < d then
          psiA (((4 * d * n : ℕ) : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) else 0))
        = ∑ j ∈ Finset.range J, psiA (((n : ℝ) / (X : ℝ)) / 2 ^ j) :=
      Finset.sum_congr rfl (fun j _ => by rw [if_pos hlt, hterm j])
    have hT2 : (if X < d ∧ 4 * d * X > 4 * d * n then (1 : ℝ) else 0)
          + (if X < d ∧ 4 * d * X = 4 * d * n then (1 : ℝ) else 0)
        = (if n ≤ X then (1 : ℝ) else 0) := by
      rw [ind_pair (X < d) (4 * d * X) (4 * d * n)]
      have hiff : (X < d ∧ 4 * d * n ≤ 4 * d * X) ↔ (n ≤ X) := by rw [hle X]; simp [hlt]
      rw [if_congr hiff rfl rfl]
    have hT3 : (∑ m ∈ Finset.Ico 1 X, wA X m *
        (((if m < d ∧ 4 * d * m > 4 * d * n then (1 : ℝ) else 0)
          + (if m < d ∧ 4 * d * m = 4 * d * n then (1 : ℝ) else 0))
          - (if m < d ∧ d ≤ X ∧ 4 * d * n ≤ 4 * d * m then (1 : ℝ) else 0)))
        = 1 - uA ((n : ℝ) / (X : ℝ)) := by
      have hcongr : (∑ m ∈ Finset.Ico 1 X, wA X m *
          (((if m < d ∧ 4 * d * m > 4 * d * n then (1 : ℝ) else 0)
            + (if m < d ∧ 4 * d * m = 4 * d * n then (1 : ℝ) else 0))
            - (if m < d ∧ d ≤ X ∧ 4 * d * n ≤ 4 * d * m then (1 : ℝ) else 0)))
          = ∑ m ∈ Finset.Ico 1 X, wA X m * (if n ≤ m then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mem_Ico] at hm
        have hmd : m < d := by omega
        have hj : (if m < d ∧ d ≤ X ∧ 4 * d * n ≤ 4 * d * m then (1 : ℝ) else 0) = 0 := by
          rw [if_neg]; rintro ⟨_, h, _⟩; omega
        rw [ind_pair (m < d) (4 * d * m) (4 * d * n), hj]
        have hiff : (m < d ∧ 4 * d * n ≤ 4 * d * m) ↔ (n ≤ m) := by rw [hle m]; simp [hmd]
        rw [if_congr hiff rfl rfl, sub_zero]
      rw [hcongr, ← Work.FIArea4.A4c.one_sub_uA_div X n hX]
    have hRHS : (if X < d ∧ 4 * d * X < 4 * d * n then (1 : ℝ) else 0)
        = (if X < n then (1 : ℝ) else 0) := by
      have hiff : (X < d ∧ 4 * d * X < 4 * d * n) ↔ (X < n) := by rw [hltn]; simp [hlt]
      rw [if_congr hiff rfl rfl]
    have hu : uA (((n : ℝ) / (X : ℝ)) / 2 ^ J) = 0 := by
      apply uA_zero
      have hJ : 2 * ((n : ℝ) / (X : ℝ)) ≤ 2 ^ J := by rw [← hc]; exact hJd
      have hpow : (0 : ℝ) < 2 ^ J := by positivity
      have h1 : ((n : ℝ) / (X : ℝ)) / 2 ^ J ≤ 1 / 2 := by rw [div_le_iff₀ hpow]; linarith
      linarith
    have hI : (if n ≤ X then (1 : ℝ) else 0) = 1 - (if X < n then (1 : ℝ) else 0) := by
      have h := one_sub_ind (n ≤ X)
      rw [show (if ¬(n ≤ X) then (1 : ℝ) else 0) = (if X < n then (1 : ℝ) else 0) from by
            rw [if_congr Nat.not_le rfl rfl]] at h
      linarith
    rw [hsum1, sum_range_psiA, hT2, hT3, hRHS, hu, hI]
    ring
  · -- `d ≤ X`: everything cancels
    have hge : d ≤ X := by omega
    have hsumB : (∑ j ∈ Finset.range J, (if X < d then
          psiA (((4 * d * n : ℕ) : ℝ) / (4 * (X : ℝ) * 2 ^ j * (d : ℝ))) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg hlt]
    have hT2B : (if X < d ∧ 4 * d * X > 4 * d * n then (1 : ℝ) else 0)
          + (if X < d ∧ 4 * d * X = 4 * d * n then (1 : ℝ) else 0) = 0 := by
      rw [if_neg (by rintro ⟨h, _⟩; exact hlt h), if_neg (by rintro ⟨h, _⟩; exact hlt h)]
      ring
    have hT3B : (∑ m ∈ Finset.Ico 1 X, wA X m *
        (((if m < d ∧ 4 * d * m > 4 * d * n then (1 : ℝ) else 0)
          + (if m < d ∧ 4 * d * m = 4 * d * n then (1 : ℝ) else 0))
          - (if m < d ∧ d ≤ X ∧ 4 * d * n ≤ 4 * d * m then (1 : ℝ) else 0))) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hj : (if m < d ∧ d ≤ X ∧ 4 * d * n ≤ 4 * d * m then (1 : ℝ) else 0)
          = (if m < d ∧ 4 * d * n ≤ 4 * d * m then (1 : ℝ) else 0) := by
        have hiff : (m < d ∧ d ≤ X ∧ 4 * d * n ≤ 4 * d * m) ↔ (m < d ∧ 4 * d * n ≤ 4 * d * m) := by
          constructor
          · rintro ⟨a, _, c⟩; exact ⟨a, c⟩
          · rintro ⟨a, c⟩; exact ⟨a, hge, c⟩
        rw [if_congr hiff rfl rfl]
      rw [ind_pair (m < d) (4 * d * m) (4 * d * n), hj, sub_self, mul_zero]
    rw [hsumB, hT2B, hT3B]
    rw [if_neg (by rintro ⟨h, _⟩; exact hlt h)]
    ring

end

end Work.FIArea4.A4c
