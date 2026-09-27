import Mathlib
import Submission.Work.EQ.ucj_defs
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.HeteroAlgebra

namespace Work.EQ

open Complex

noncomputable section

/-! ## Auxiliary lemmas for `ucjChain_eqRelC` -/

/-- Unfolding of `fan` at the empty word (definitional). -/
private lemma ucj_fan_nil (a : ℝ) (h : ℂ → ℂ) (u : ℂ) : fan a h [] u = germC a h u := rfl

/-- Unfolding of `fan` at a cons (definitional). -/
private lemma ucj_fan_cons (a : ℝ) (h : ℂ → ℂ) (s : Bool) (ε : List Bool) (u : ℂ) :
    fan a h (s :: ε) u = invBranch a s (fan a h ε ((eqLam a : ℂ) * u)) := rfl

/-- The fan recursion at a drop: for `i < ε.length`,
`fan (ε.drop i) u = invBranch a ε[i] (fan (ε.drop (i+1)) (λ u))`. -/
private lemma ucj_fan_drop_getElem_cons {a : ℝ} {h : ℂ → ℂ} {ε : List Bool} {i : ℕ}
    (hi : i < ε.length) (u : ℂ) :
    fan a h (ε.drop i) u = invBranch a ε[i] (fan a h (ε.drop (i + 1)) ((eqLam a : ℂ) * u)) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

/-- The bisector reflection conjugates `EqRelC` to its inverse. -/
private theorem ucj_eqRelC_mirror {a : ℝ} {P Q : ℂ × ℂ} :
    EqRelC a (eqMirror Q) (eqMirror P) ↔ EqRelC a P Q := by
  simp only [eqMirror, EqRelC]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have hh : (-P.1 + -Q.1) ^ 2 + (P.2 + Q.2) ^ 2
          = (Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2 := by ring
      rw [hh] at h1
      exact h1
    · linear_combination (norm := ring_nf) h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have hh : (-P.1 + -Q.1) ^ 2 + (P.2 + Q.2) ^ 2
          = (Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2 := by ring
      rw [hh]
      exact h1
    · linear_combination (norm := ring_nf) h2

/-- The value of `ucjChain` at a nonnegative index in the fan window. -/
private theorem ucj_fst_nonneg {a : ℝ} {h : ℂ → ℂ} {ε η s : List Bool} {N : ℕ} {C : ℂ}
    {g : ℕ → ℂ → ℂ × ℂ} {z : ℂ} {n : ℤ} (hn : 0 ≤ n) (hk : n.toNat ≤ N) :
    (ucjChain a h ε η s N C g z).1 n
      = fan a h (ε.drop n.toNat) ((eqLam a : ℂ) ^ n * z) := by
  rw [ucjChain_fst_apply, if_pos hn, if_pos hk]

/-- The value of `ucjChain` at an index `n ≥ N`: the principal germ `germC (λ^n z)`. -/
private theorem ucj_fst_ge {a : ℝ} {h : ℂ → ℂ} {ε η s : List Bool} {N : ℕ} {C : ℂ}
    {g : ℕ → ℂ → ℂ × ℂ} {z : ℂ} (hε : ε.length = N) {n : ℤ} (hn : (N : ℤ) ≤ n) :
    (ucjChain a h ε η s N C g z).1 n = germC a h ((eqLam a : ℂ) ^ n * z) := by
  have hn0 : 0 ≤ n := by omega
  rw [ucjChain_fst_apply, if_pos hn0]
  by_cases hk : n.toNat ≤ N
  · rw [if_pos hk]
    have hdrop : ε.drop n.toNat = [] := by
      rw [List.drop_eq_nil_iff, hε]
      have h : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
      omega
    rw [hdrop, ucj_fan_nil]
  · rw [if_neg hk]

/-- The value of `ucjChain` at index `-m` for `m ≤ N`: the prescribed middle point `g m z`. -/
private theorem ucj_val_neg_le {a : ℝ} {h : ℂ → ℂ} {ε η s : List Bool} {N : ℕ} {C : ℂ}
    {g : ℕ → ℂ → ℂ × ℂ} {z : ℂ} (hg0z : g 0 z = fan a h ε z) {m : ℕ} (hm : m ≤ N) :
    (ucjChain a h ε η s N C g z).1 (-(m : ℤ)) = g m z := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have hP0 : (ucjChain a h ε η s N C g z).1 (0 : ℤ) = g 0 z := by
      rw [ucj_fst_nonneg (n := (0 : ℤ)) le_rfl (Nat.zero_le N)]
      simp [hg0z]
    simpa using hP0
  · rw [ucjChain_fst_apply, if_neg (by omega),
      if_pos (by rw [neg_neg, Int.toNat_natCast]; exact hm)]
    simp only [neg_neg, Int.toNat_natCast]

/-- The value of `ucjChain` at index `-m` for `N ≤ m`: the mirrored fan of `η` evaluated at
`λ^m (C/z)` (the boundary case `m = N` being the junction identity). -/
private theorem ucj_val_neg {a : ℝ} {h : ℂ → ℂ} {ε η s : List Bool} {N : ℕ} {C : ℂ}
    {g : ℕ → ℂ → ℂ × ℂ} {z : ℂ}
    (hg0z : g 0 z = fan a h ε z)
    (hgNz : g N z = eqMirror (fan a h η ((eqLam a : ℂ) ^ N * (C / z))))
    {m : ℕ} (hm : N ≤ m) :
    (ucjChain a h ε η s N C g z).1 (-(m : ℤ))
      = eqMirror (fan a h (η.drop (m - N)) ((eqLam a : ℂ) ^ (m : ℤ) * (C / z))) := by
  rcases eq_or_lt_of_le hm with hmN_eq | hlt
  · rw [← hmN_eq]
    have hPN : (ucjChain a h ε η s N C g z).1 (-(N : ℤ)) = g N z :=
      ucj_val_neg_le hg0z (le_refl N)
    rw [hPN, hgNz, Nat.sub_self, List.drop_zero, zpow_natCast]
  · rw [ucjChain_fst_apply, if_neg (by omega),
      if_neg (by rw [neg_neg, Int.toNat_natCast]; omega)]
    simp only [neg_neg, Int.toNat_natCast]

/-- **`ucjChain` satisfies the equichordal relation at every pair of consecutive indices.**  The
middle maps `g k` (`k ≤ N`) are nondegenerate on `U` and related by the backward recursion
(`EqRelC (g (k+1) z) (g k z)`), `g 0` is the stable fan of `ε`, and `g N` meets the mirrored
unstable fan at the junction point.  Then every consecutive pair of `ucjChain`
(`Submission.Work.EQ.ucj_defs`) is an `EqRelC`-pair. -/
theorem ucjChain_eqRelC {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {Ke Lam Q δf ρg : ℝ}
    (hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δf → FanGood a h Ke Lam Q ε' v)
    (hreg : ∀ u : ℂ, ‖u‖ < ρg → RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)))
    {N : ℕ} {ε η s : List Bool} (hε : ε.length = N) (hs : s.length = N) {C : ℂ} {U : Set ℂ}
    (hUz : ∀ z ∈ U, ‖z‖ < min δf ρg)
    (hUc : ∀ z ∈ U, ‖(((eqLam a : ℝ) : ℂ)) ^ N * (C / z)‖ < min δf ρg)
    {g : ℕ → ℂ → ℂ × ℂ}
    (hg0 : ∀ z ∈ U, g 0 z = fan a h ε z)
    (hnd : ∀ k : ℕ, k < N → ∀ z ∈ U, bsq (subO1 a (g k z)) ≠ 0)
    (hgrec : ∀ k : ℕ, k < N → ∀ z ∈ U, EqRelC a (g (k+1) z) (g k z))
    (hgjunc : ∀ z ∈ U, g N z = eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z)))) :
    ∀ z ∈ U, ∀ n : ℤ, EqRelC a ((ucjChain a h ε η s N C g z).1 n)
      ((ucjChain a h ε η s N C g z).1 (n + 1)) := by
  -- the multiplier `λ = eqLam a` lies in `(0,1]`
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlamle : eqLam a ≤ 1 := le_of_lt hlam1
  have hΛne : ((eqLam a : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0)
  have hnorm_pow_le : ∀ k : ℕ, ‖(eqLam a : ℂ) ^ k‖ ≤ 1 := by
    intro k
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
    exact pow_le_one₀ hlam0.le hlamle
  have hnorm_zpow_le : ∀ k : ℤ, 0 ≤ k → ‖(eqLam a : ℂ) ^ k‖ ≤ 1 := by
    intro k hk
    rw [show (eqLam a : ℂ) ^ k = (eqLam a : ℂ) ^ k.toNat from by
      conv_lhs => rw [← Int.toNat_of_nonneg hk]
      rw [zpow_natCast]]
    exact hnorm_pow_le k.toNat
  have hnorm_mul_le : ∀ (k : ℤ), 0 ≤ k → ∀ w : ℂ, ‖(eqLam a : ℂ) ^ k * w‖ ≤ ‖w‖ := by
    intro k hk w
    calc ‖(eqLam a : ℂ) ^ k * w‖ ≤ ‖(eqLam a : ℂ) ^ k‖ * ‖w‖ := norm_mul_le _ _
      _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right (hnorm_zpow_le k hk) (norm_nonneg w)
      _ = ‖w‖ := one_mul _
  intro z hzU n
  have hzlt : ‖z‖ < min δf ρg := hUz z hzU
  have hclt : ‖(eqLam a : ℂ) ^ N * (C / z)‖ < min δf ρg := hUc z hzU
  -- every argument of the stable fan of `ε` is small
  have hzarg : ∀ k : ℤ, 0 ≤ k → ‖(eqLam a : ℂ) ^ k * z‖ < min δf ρg := by
    intro k hk
    calc ‖(eqLam a : ℂ) ^ k * z‖ ≤ ‖z‖ := hnorm_mul_le k hk z
      _ < min δf ρg := hzlt
  -- every argument of the mirrored fan of `η` is small
  have hcarg : ∀ m : ℕ, N ≤ m → ‖(eqLam a : ℂ) ^ (m : ℤ) * (C / z)‖ < min δf ρg := by
    intro m hm
    have hexp : (((m - N : ℕ) : ℤ)) + ((N : ℤ)) = (m : ℤ) := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hm]
    have hsplit : (eqLam a : ℂ) ^ (m : ℤ)
        = (eqLam a : ℂ) ^ (((m - N : ℕ)) : ℤ) * (eqLam a : ℂ) ^ (N : ℤ) := by
      rw [← hexp, zpow_add₀ hΛne]
    calc ‖(eqLam a : ℂ) ^ (m : ℤ) * (C / z)‖
        = ‖(eqLam a : ℂ) ^ (((m - N : ℕ)) : ℤ) * ((eqLam a : ℂ) ^ N * (C / z))‖ := by
          rw [hsplit]; simp only [zpow_natCast, mul_assoc]
      _ ≤ ‖(eqLam a : ℂ) ^ (((m - N : ℕ)) : ℤ)‖ * ‖(eqLam a : ℂ) ^ N * (C / z)‖ :=
          norm_mul_le _ _
      _ ≤ 1 * ‖(eqLam a : ℂ) ^ N * (C / z)‖ :=
          mul_le_mul_of_nonneg_right (hnorm_zpow_le _ (by positivity)) (norm_nonneg _)
      _ = ‖(eqLam a : ℂ) ^ N * (C / z)‖ := one_mul _
      _ < min δf ρg := hclt
  -- the four windows of the index line
  by_cases hNle : (N : ℤ) ≤ n
  · -- window `n ≥ N`: both points are germ points
    have hn0 : 0 ≤ n := by omega
    have hPn : (ucjChain a h ε η s N C g z).1 n = germC a h ((eqLam a : ℂ) ^ n * z) :=
      ucj_fst_ge hε hNle
    have hPn1 : (ucjChain a h ε η s N C g z).1 (n + 1)
        = germC a h ((eqLam a : ℂ) ^ (n + 1) * z) := ucj_fst_ge hε (by omega)
    have harg : (eqLam a : ℂ) ^ (n + 1) * z = (eqLam a : ℂ) * ((eqLam a : ℂ) ^ n * z) := by
      rw [zpow_add₀ hΛne, zpow_one]; ring
    have hρ : ‖(eqLam a : ℂ) ^ n * z‖ < ρg :=
      lt_of_lt_of_le (hzarg n hn0) (min_le_right _ _)
    rw [hPn, hPn1, harg]
    exact (hreg ((eqLam a : ℂ) ^ n * z) hρ).1
  · have hnltN : n < (N : ℤ) := lt_of_not_ge hNle
    by_cases h0 : 0 ≤ n
    · -- window `0 ≤ n < N`: the stable fan recursion of `ε`
      have hk1 : n.toNat ≤ N := by
        have h : (n.toNat : ℤ) = n := Int.toNat_of_nonneg h0
        omega
      have hPn : (ucjChain a h ε η s N C g z).1 n
          = fan a h (ε.drop n.toNat) ((eqLam a : ℂ) ^ n * z) := ucj_fst_nonneg h0 hk1
      have hk2 : (n + 1).toNat = n.toNat + 1 := by
        have h2 : (((n + 1).toNat : ℕ) : ℤ) = n + 1 := Int.toNat_of_nonneg (by omega)
        have h3 : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg h0
        omega
      have hk2N : (n + 1).toNat ≤ N := by rw [hk2]; omega
      have hPn1 : (ucjChain a h ε η s N C g z).1 (n + 1)
          = fan a h (ε.drop (n.toNat + 1)) ((eqLam a : ℂ) ^ (n + 1) * z) := by
        rw [ucj_fst_nonneg (n := n + 1) (by omega) hk2N, hk2]
      have hk1lt : n.toNat < ε.length := by rw [hε]; omega
      have hbsq : bsq (subO1 a (fan a h (ε.drop (n.toNat + 1))
          ((eqLam a : ℂ) ^ (n + 1) * z))) ≠ 0 := by
        have hmem : ‖(eqLam a : ℂ) ^ (n + 1) * z‖ < δf :=
          lt_of_lt_of_le (hzarg (n + 1) (by omega)) (min_le_left _ _)
        have hpos := (hFG (ε.drop (n.toNat + 1))
          ((eqLam a : ℂ) ^ (n + 1) * z) hmem).2.2.2.2
        have heq : bsq (subO1 a (fan a h (ε.drop (n.toNat + 1))
              ((eqLam a : ℂ) ^ (n + 1) * z)))
            = ((fan a h (ε.drop (n.toNat + 1))
                  ((eqLam a : ℂ) ^ (n + 1) * z)).1 + (a : ℂ) / 2) ^ 2
              + (fan a h (ε.drop (n.toNat + 1))
                  ((eqLam a : ℂ) ^ (n + 1) * z)).2 ^ 2 := by
          simp only [bsq, subO1]; push_cast; ring
        intro hz0
        rw [heq] at hz0
        rw [hz0] at hpos
        simp at hpos
      rw [hPn, hPn1, ucj_fan_drop_getElem_cons hk1lt ((eqLam a : ℂ) ^ n * z)]
      have harg : (eqLam a : ℂ) * ((eqLam a : ℂ) ^ n * z) = (eqLam a : ℂ) ^ (n + 1) * z := by
        rw [zpow_add₀ hΛne, zpow_one]; ring
      rw [harg]
      exact eqRelC_invBranch ε[n.toNat] hbsq
    · have hnneg : n < 0 := lt_of_not_ge h0
      by_cases hNneg : -(N : ℤ) ≤ n
      · -- window `-N ≤ n < 0`: the prescribed middle maps `g`
        obtain ⟨m, hm_eq, hm1, hmN⟩ : ∃ m : ℕ, n = -(m : ℤ) ∧ 1 ≤ m ∧ m ≤ N := by
          refine ⟨(-n).toNat, ?_, ?_, ?_⟩
          · have hcast : ((((-n).toNat : ℕ)) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
            omega
          · have hcast : ((((-n).toNat : ℕ)) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
            omega
          · have hcast : ((((-n).toNat : ℕ)) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
            omega
        have hPn : (ucjChain a h ε η s N C g z).1 n = g m z := by
          rw [hm_eq]; exact ucj_val_neg_le (hg0 z hzU) hmN
        have hPn1 : (ucjChain a h ε η s N C g z).1 (n + 1) = g (m - 1) z := by
          have h : n + 1 = -(((m - 1 : ℕ)) : ℤ) := by omega
          rw [h]; exact ucj_val_neg_le (hg0 z hzU) (by omega)
        rw [hPn, hPn1]
        have hrec := hgrec (m - 1) (by omega) z hzU
        simpa [Nat.sub_add_cancel hm1] using hrec
      · -- window `n < -N`: the junction step and the mirrored fan recursion of `η`
        have hnlt : n < -(N : ℤ) := lt_of_not_ge hNneg
        obtain ⟨m, hm_eq, hmge⟩ : ∃ m : ℕ, n = -(m : ℤ) ∧ N + 1 ≤ m := by
          refine ⟨(-n).toNat, ?_, ?_⟩
          · have hcast : ((((-n).toNat : ℕ)) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
            omega
          · have hcast : ((((-n).toNat : ℕ)) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
            omega
        have hmN : N ≤ m := by omega
        have hm1 : 1 ≤ m := by omega
        have hmN1 : N ≤ m - 1 := by omega
        have hPn : (ucjChain a h ε η s N C g z).1 n
            = eqMirror (fan a h (η.drop (m - N)) ((eqLam a : ℂ) ^ (m : ℤ) * (C / z))) := by
          rw [hm_eq]; exact ucj_val_neg (hg0 z hzU) (hgjunc z hzU) hmN
        have hPn1 : (ucjChain a h ε η s N C g z).1 (n + 1)
            = eqMirror (fan a h (η.drop ((m - 1) - N))
                ((eqLam a : ℂ) ^ (((m - 1 : ℕ)) : ℤ) * (C / z))) := by
          have h : n + 1 = -(((m - 1 : ℕ)) : ℤ) := by omega
          rw [h]; exact ucj_val_neg (hg0 z hzU) (hgjunc z hzU) hmN1
        rw [hPn, hPn1, ucj_eqRelC_mirror]
        have hmcast : (m : ℤ) = (((m - 1 : ℕ)) : ℤ) + 1 := by
          have hsub : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := Nat.cast_sub hm1
          omega
        by_cases hlt : (m - 1) - N < η.length
        · -- still inside the word `η`: one fan recursion step
          have hidx : (m - 1) - N + 1 = m - N := by omega
          have hdrop : η.drop ((m - 1) - N) = η[(m - 1) - N] :: η.drop (m - N) := by
            rw [List.drop_eq_getElem_cons hlt, hidx]
          rw [hdrop, ucj_fan_cons]
          have harg : (eqLam a : ℂ) * ((eqLam a : ℂ) ^ (((m - 1 : ℕ)) : ℤ) * (C / z))
              = (eqLam a : ℂ) ^ (m : ℤ) * (C / z) := by
            rw [hmcast, zpow_add_one₀ hΛne]; ring
          rw [harg]
          refine eqRelC_invBranch η[(m - 1) - N] ?_
          have hmem : ‖(eqLam a : ℂ) ^ (m : ℤ) * (C / z)‖ < δf :=
            lt_of_lt_of_le (hcarg m hmN) (min_le_left _ _)
          have hpos := (hFG (η.drop (m - N)) ((eqLam a : ℂ) ^ (m : ℤ) * (C / z))
            hmem).2.2.2.2
          have heq : bsq (subO1 a (fan a h (η.drop (m - N))
                ((eqLam a : ℂ) ^ (m : ℤ) * (C / z))))
              = ((fan a h (η.drop (m - N))
                    ((eqLam a : ℂ) ^ (m : ℤ) * (C / z))).1 + (a : ℂ) / 2) ^ 2
                + (fan a h (η.drop (m - N))
                    ((eqLam a : ℂ) ^ (m : ℤ) * (C / z))).2 ^ 2 := by
            simp only [bsq, subO1]; push_cast; ring
          intro hz0
          rw [heq] at hz0
          rw [hz0] at hpos
          simp at hpos
        · -- beyond the word `η`: the germ recursion
          have hdrop1 : η.drop ((m - 1) - N) = [] := by
            rw [List.drop_eq_nil_iff]; omega
          have hdrop2 : η.drop (m - N) = [] := by
            rw [List.drop_eq_nil_iff]; omega
          rw [hdrop1, hdrop2, ucj_fan_nil, ucj_fan_nil]
          have harg : (eqLam a : ℂ) ^ (m : ℤ) * (C / z)
              = (eqLam a : ℂ) * ((eqLam a : ℂ) ^ (((m - 1 : ℕ)) : ℤ) * (C / z)) := by
            rw [hmcast, zpow_add_one₀ hΛne]; ring
          rw [harg]
          exact (hreg ((eqLam a : ℂ) ^ (((m - 1 : ℕ)) : ℤ) * (C / z))
            (lt_of_lt_of_le (hcarg (m - 1) hmN1) (min_le_right _ _))).1

end

end Work.EQ
