import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedDefs
import Submission.Work.KMTAreas.A7.ExceptionalSupport

namespace Work.KMTAreas.A7

open Work.Analysis.EndVar

/-!
# The off-band regime of the mixed-range §6 comparison is bounded

This module proves `Work.KMTAreas.A7.LoMixedOffBandRegimeHolds`, the structural fact behind the
crude bound on the off-band part of the KMT large-scale estimate in the mixed range `l₁ = 0`,
`l₂ ≥ 1` (see `LoMixedDefs.lean` and `LoMixedOffBand.lean`).

Write `R = Log N = Nat.log 2 (max N 2)`, `M = max k₁ k₂`,
`L = max (max 0 l₂) (max k₁ k₂)`, `us = uScale ρ L = ⌊2^{2ρL}⌋` (the arithmetic scale count) and
`u = loMixedU ρ P.natDegree l₂ k₁ k₂ = max us (d·l₂ + 3)`, `d = P.natDegree`.  The hypotheses are

* `inIndexSet C₀ (max 0 l₂) k₁ k₂ N`, i.e. `l₂, k₁, k₂ ≤ C₀ · LogLog N` (admissibility);
* `splitCut ρ L < N`, i.e. `N > 2^{2^{us}}` (the scale is large), which gives `2^{us} ≤ R` and
  hence `us ≤ log₂ R`;
* the off-band condition `¬ loBandCond ρ P l₂ k₁ k₂ N`, i.e. `R < M + 1 + 2u`.

(The main-regime hypothesis is not needed.)  Since `u ≤ us + (d·l₂+3) ≤ log₂ R + d·l₂ + 3` and
`M, l₂ ≤ C₀ · log₂(R+2)`, the off-band inequality reads

  `R + 1 ≤ (C₀(2d+1) + 2) · log₂ (R+2) + 8`,

a superlinear-in-`log` but sublinear-in-`R` bound on `R`; it forces `R ≤ c(c+9)+7` with
`c = C₀(2d+1)+2` (the numeric core `logN_param_bound_offBand`).  Then
`l₂, k₁, k₂ ≤ C₀·log₂(R+2) ≤ C₀(c+9)` and `N ≤ 2^{R+1}`, all bounded in terms of `C₀`, `d`
alone.  The explicit bound is `B = max 1 (max (c(c+9)+8) (C₀(c+9)))`.

This mirrors `Work.KMTAreas.A7.ExceptionalSupport` (the `¬ mainRegime` case), with the roles of
`mainRegime` and `loBandCond` interchanged: the argument only needs the *upper* bound
`R ≤ M + 1 + 2u` coming from `¬ loBandCond` in place of the lower bound used there.
-/

/-- The elementary inequality `L ^ 2 ≤ 2 ^ L` for `L ≥ 4`. -/
private lemma two_pow_ge_sq : ∀ L : ℕ, 4 ≤ L → L ^ 2 ≤ 2 ^ L := by
  intro L
  induction L with
  | zero => intro hL; omega
  | succ n ih =>
      intro hn4
      rcases Nat.lt_or_ge n 4 with hn | hn
      · have hn3 : n = 3 := by omega
        subst hn3
        norm_num
      · have ihn : n ^ 2 ≤ 2 ^ n := ih hn
        calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
          _ ≤ 2 * 2 ^ n := by nlinarith
          _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- If `2 ^ L ≤ k * L + 1` with `1 ≤ k` then `L ≤ k + 1`.  (The standard `log` versus linear
comparison; `L = 3`, `k = 1` is the boundary case.) -/
private lemma log_le_succ_of_two_pow_le (k L : ℕ) (hk : 1 ≤ k) (h : 2 ^ L ≤ k * L + 1) :
    L ≤ k + 1 := by
  by_contra hc
  have hc' : k + 1 < L := not_le.mp hc
  have hLk : k + 2 ≤ L := by omega
  have hprod_le : L * (L - k) ≤ 1 := by
    rcases Nat.lt_or_ge L 4 with hlt | hge
    · have hL3 : L = 3 := by omega
      have hk1 : k = 1 := by omega
      subst hL3; subst hk1
      exact absurd h (by norm_num)
    · have hsq : L ^ 2 ≤ 2 ^ L := two_pow_ge_sq L hge
      have h1 : L ^ 2 ≤ k * L + 1 := le_trans hsq h
      rw [Nat.mul_comm k L] at h1
      have hh : L * (L - k) = L ^ 2 - (L * k) := by
        rw [Nat.mul_sub_left_distrib, pow_two]
      rw [hh]
      omega
  have hsub : 2 ≤ L - k := by omega
  have hpm : (k + 2) * 2 ≤ L * (L - k) := Nat.mul_le_mul hLk hsub
  omega

/-- **The numeric core of the off-band regime.**  If `1 ≤ R` and
`R + 1 ≤ c · log₂(R+2) + 8`, then `log₂(R+2) ≤ c + 9` and `R ≤ c(c+9) + 7`.
(Proof: `2^{log₂(R+2)} ≤ R + 2 ≤ (c+8)·log₂(R+2) + 1`, so `log₂(R+2) ≤ c + 9` by
`log_le_succ_of_two_pow_le`.) -/
private lemma logN_param_bound_offBand (c R : ℕ) (hR : 1 ≤ R)
    (h : R + 1 ≤ c * Nat.log 2 (R + 2) + 8) :
    Nat.log 2 (R + 2) ≤ c + 9 ∧ R ≤ c * (c + 9) + 7 := by
  set L := Nat.log 2 (R + 2) with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
    omega
  have h2L : 2 ^ L ≤ R + 2 := by rw [hL]; exact Nat.pow_log_le_self 2 (by omega)
  have hcab : 2 ^ L ≤ (c + 8) * L + 1 := by
    have h1 : 2 ^ L ≤ c * L + 9 := by omega
    have h2 : c * L + 9 ≤ c * L + (8 * L + 1) := by
      have : 9 ≤ 8 * L + 1 := by omega
      exact Nat.add_le_add_left this (c * L)
    have h3 : c * L + (8 * L + 1) = (c + 8) * L + 1 := by ring
    omega
  have hLc : L ≤ c + 8 + 1 := log_le_succ_of_two_pow_le (c + 8) L (by omega) hcab
  have hLc' : L ≤ c + 9 := by omega
  have hR' : R + 1 ≤ c * (c + 9) + 8 := by
    have := Nat.mul_le_mul_left c hLc'
    omega
  exact ⟨hLc', by omega⟩

/-- **The arithmetic step of the off-band regime.**  With `us ≤ log₂ R` (from the largeness of the
scale) and `M, l₂ ≤ C₀ · log₂(R+2)` (from admissibility), the off-band inequality
`R < M + 1 + 2·max us (d·l₂+3)` gives `R + 1 ≤ (C₀(2d+1)+2) · log₂(R+2) + 8`. -/
private lemma offBand_key_arith (C₀ d R M l₂ us : ℕ)
    (hM : M ≤ C₀ * Nat.log 2 (R + 2)) (hl₂ : l₂ ≤ C₀ * Nat.log 2 (R + 2))
    (hus : us ≤ Nat.log 2 R)
    (hoff : R < M + 1 + 2 * max us (d * l₂ + 3)) :
    R + 1 ≤ (C₀ * (2 * d + 1) + 2) * Nat.log 2 (R + 2) + 8 := by
  have hlog : Nat.log 2 R ≤ Nat.log 2 (R + 2) := Nat.log_mono_right (by omega)
  have hu : max us (d * l₂ + 3)
      ≤ Nat.log 2 (R + 2) + (d * (C₀ * Nat.log 2 (R + 2)) + 3) := by
    refine max_le ?_ ?_
    · exact le_trans hus (le_trans hlog (Nat.le_add_right _ _))
    · have := Nat.mul_le_mul_left d hl₂
      omega
  have h2 : 2 * max us (d * l₂ + 3)
      ≤ 2 * (Nat.log 2 (R + 2) + (d * (C₀ * Nat.log 2 (R + 2)) + 3)) :=
    Nat.mul_le_mul_left 2 hu
  have h3 : M + 1 + 2 * max us (d * l₂ + 3)
      ≤ C₀ * Nat.log 2 (R + 2) + 1
          + 2 * (Nat.log 2 (R + 2) + (d * (C₀ * Nat.log 2 (R + 2)) + 3)) := by omega
  have h4 : C₀ * Nat.log 2 (R + 2) + 1
        + 2 * (Nat.log 2 (R + 2) + (d * (C₀ * Nat.log 2 (R + 2)) + 3))
      = (C₀ * (2 * d + 1) + 2) * Nat.log 2 (R + 2) + 7 := by ring
  omega

theorem LoMixedOffBandRegimeHolds (P : Polynomial ℤ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ)
    (hρ : 0 < ρ) (hρle : ρ ≤ 1 / (4 * (C₀ : ℝ))) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ (l₂ k₁ k₂ N : ℕ),
      Work.Analysis.EndVar.inIndexSet C₀ (max 0 (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N →
      Work.KMTAreas.A7.splitCut ρ (max (max 0 l₂) (max k₁ k₂)) < N →
      Work.KMTAreas.A7.mainRegime ρ k₁ k₂ N →
      ¬ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ N →
      l₂ ≤ B ∧ k₁ ≤ B ∧ k₂ ≤ B ∧ (Work.Analysis.EndVar.logN N).toNat ≤ B ∧ N ≤ 2 ^ B := by
  set c : ℕ := C₀ * (2 * P.natDegree + 1) + 2 with hc
  refine ⟨max 1 (max (c * (c + 9) + 8) (C₀ * (c + 9))), le_max_left 1 _, ?_⟩
  intro l₂ k₁ k₂ N hidx hsplit hmain hoff
  have hlogN : (Work.Analysis.EndVar.logN N).toNat = Nat.log 2 (max N 2) := by
    simp [Work.Analysis.EndVar.logN]
  have hR1 : 1 ≤ Nat.log 2 (max N 2) :=
    Nat.le_log_of_pow_le (by norm_num : 1 < 2) (le_max_right N 2)
  have hhs : Work.Analysis.EndVar.heightScale C₀ N
      = C₀ * Nat.log 2 (Nat.log 2 (max N 2) + 2) := by
    simp [Work.Analysis.EndVar.heightScale, Work.Analysis.EndVar.logLogN]
  unfold Work.Analysis.EndVar.inIndexSet at hidx
  have hM_le : max k₁ k₂ ≤ C₀ * Nat.log 2 (Nat.log 2 (max N 2) + 2) := by
    have h1 : k₁ ≤ C₀ * Nat.log 2 (Nat.log 2 (max N 2) + 2) := by
      have h : k₁ ≤ Work.Analysis.EndVar.heightScale C₀ N := by
        exact_mod_cast hidx.2.1
      rwa [hhs] at h
    have h2 : k₂ ≤ C₀ * Nat.log 2 (Nat.log 2 (max N 2) + 2) := by
      have h : k₂ ≤ Work.Analysis.EndVar.heightScale C₀ N := by
        exact_mod_cast hidx.2.2
      rwa [hhs] at h
    exact max_le h1 h2
  have hl₂_le : l₂ ≤ C₀ * Nat.log 2 (Nat.log 2 (max N 2) + 2) := by
    have h0 : (l₂ : ℤ) ≤ max 0 (l₂ : ℤ) := le_max_right _ _
    have h : (l₂ : ℤ) ≤ ((Work.Analysis.EndVar.heightScale C₀ N : ℕ) : ℤ) :=
      le_trans h0 hidx.1
    have h' : l₂ ≤ Work.Analysis.EndVar.heightScale C₀ N := by exact_mod_cast h
    rwa [hhs] at h'
  have hsplit' : 2 ^ (2 ^ Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂))) < N := by
    have h : Work.KMTAreas.A7.splitCut ρ (max (max 0 l₂) (max k₁ k₂)) < N := hsplit
    rwa [show Work.KMTAreas.A7.splitCut ρ (max (max 0 l₂) (max k₁ k₂))
          = 2 ^ (2 ^ Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂))) from rfl] at h
  have hus_le : Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂))
      ≤ Nat.log 2 (Nat.log 2 (max N 2)) := by
    have h2us : 2 ^ Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂))
        ≤ Nat.log 2 (max N 2) := by
      have h1 : 2 ^ Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂))
          ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num : 1 < 2) (le_of_lt hsplit')
      exact le_trans h1 (Nat.log_mono_right (le_max_left N 2))
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) h2us
  have hoff' : Nat.log 2 (max N 2) < max k₁ k₂ + 1
      + 2 * max (Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂)))
          (P.natDegree * l₂ + 3) := by
    have h := hoff
    unfold Work.KMTAreas.A7.loBandCond at h
    rw [hlogN] at h
    have h' := not_le.mp h
    have heq : Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂
        = max (Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂)))
            (P.natDegree * l₂ + 3) := rfl
    rwa [heq] at h'
  have hkey : Nat.log 2 (max N 2) + 1
      ≤ c * Nat.log 2 (Nat.log 2 (max N 2) + 2) + 8 := by
    rw [hc]
    exact offBand_key_arith C₀ P.natDegree (Nat.log 2 (max N 2)) (max k₁ k₂) l₂
      (Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂))) hM_le hl₂_le hus_le hoff'
  obtain ⟨hLp, hRp⟩ := logN_param_bound_offBand c (Nat.log 2 (max N 2)) hR1 hkey
  set B : ℕ := max 1 (max (c * (c + 9) + 8) (C₀ * (c + 9))) with hB
  have hB1 : C₀ * (c + 9) ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
  have hB2 : c * (c + 9) + 8 ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
  have hparam : ∀ k : ℕ, k ≤ C₀ * Nat.log 2 (Nat.log 2 (max N 2) + 2) → k ≤ B := by
    intro k hk
    exact le_trans (le_trans hk (Nat.mul_le_mul_left C₀ hLp)) hB1
  have hN : N ≤ 2 ^ (Nat.log 2 (max N 2) + 1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max N 2)
    exact le_of_lt (lt_of_le_of_lt (le_max_left N 2) h)
  have hRB : Nat.log 2 (max N 2) + 1 ≤ B := le_trans (by omega) hB2
  exact ⟨hparam l₂ hl₂_le, hparam k₁ (le_trans (le_max_left _ _) hM_le),
    hparam k₂ (le_trans (le_max_right _ _) hM_le),
    by rw [hlogN]; exact le_trans (by omega) hB2,
    le_trans hN (Nat.pow_le_pow_right (by norm_num) hRB)⟩

end Work.KMTAreas.A7
