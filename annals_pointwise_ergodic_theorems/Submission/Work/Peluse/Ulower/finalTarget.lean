import Mathlib
import Submission.Work.Peluse.Ulower.chain
import Submission.Work.Peluse.Ulower.boxNormPow_le_one_sub
import Submission.Work.Peluse.Ulower.dSup_div_add_one_le
import Submission.Work.Peluse.Crux.boxNormPow_singleton

/-!
# The final comparison: from the single-step interface `StepLe` to `degree_lowering_v2`

This module assembles everything *except* the single step of Peluse's Lemma 3.9 (the interface
`Work.Peluse.Ulower.StepLe`): the sparse-to-dense conversion, the iteration of the step and the
final K-comparison, in exactly the form of the target statement.

The two cases of the last comparison are

* `D = 1`: the direction set is a singleton, the box-norm power is `(1/|S|) ∑_x ‖F x‖^{2^t}`
  (`Work.Peluse.Crux.boxNormPow_singleton`), which is *decreasing* in the level `t`; hence
  `δ ≤ ‖F‖_{□²}` directly and `K = 4` works.
* `D ≥ 2`: the a priori sharpness `boxNormPow_le_one_sub` gives `δ ≤ 1 - min(c δ', 2^{-s})` with
  the *uniform* constant `c` (using `dSup P Ns N + 1 ≤ ssAmax P · Ns`), whence `δ·δ' ≤ r < 1` with
  `r` uniform; then `final_compare` turns the constant-laden chain bound into the target's
  `(δ · D/Ns)^K ≤ …`.
-/

set_option maxHeartbeats 1600000
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## The uniform form of the final comparison -/

/-- `final_compare` with the exponent `K` produced *before* the data: this is what the target's
quantifier order requires. -/
lemma final_compare_uniform {C r : ℝ} (hC : 0 < C) (hr0 : 0 ≤ r) (hr1 : r < 1) (A B : ℕ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ {δ δ' : ℝ}, 0 ≤ δ → δ ≤ 1 → 0 ≤ δ' → δ' ≤ 1 → δ * δ' ≤ r →
      (δ * δ') ^ K ≤ C * δ ^ A * δ' ^ B := by
  obtain ⟨m, hm⟩ := exists_pow_le_of_lt_one hr0 hr1 hC
  refine ⟨A + B + m + 1, by omega, ?_⟩
  intro δ δ' hδ0 hδ1 hδ'0 hδ'1 hr
  have hprod : (δ * δ') ^ (A + B) ≤ δ ^ A * δ' ^ B := by
    have hfac : (δ * δ') ^ (A + B) = (δ ^ A * δ' ^ B) * (δ ^ B * δ' ^ A) := by
      rw [mul_pow, pow_add, pow_add]; ring
    rw [hfac]
    have hb : δ ^ B * δ' ^ A ≤ 1 := by
      have h1 : δ ^ B ≤ 1 := pow_le_one₀ hδ0 hδ1
      have h2 : δ' ^ A ≤ 1 := pow_le_one₀ hδ'0 hδ'1
      calc δ ^ B * δ' ^ A ≤ 1 * 1 := mul_le_mul h1 h2 (pow_nonneg hδ'0 A) (by norm_num)
        _ = 1 := by norm_num
    exact mul_le_of_le_one_right (by positivity) hb
  have hpow : (δ * δ') ^ (A + B + m + 1) = (δ * δ') ^ (A + B) * (δ * δ') ^ (m + 1) := by
    rw [show A + B + m + 1 = (A + B) + (m + 1) from by omega, pow_add]
  rw [hpow]
  have hsmall : (δ * δ') ^ (m + 1) ≤ C := by
    have h1 : (δ * δ') ^ (m + 1) ≤ r ^ (m + 1) :=
      pow_le_pow_left₀ (mul_nonneg hδ0 hδ'0) hr _
    have h2 : r ^ (m + 1) ≤ r ^ m := pow_le_pow_of_le_one hr0 hr1.le (by omega)
    linarith
  calc (δ * δ') ^ (A + B) * (δ * δ') ^ (m + 1)
      ≤ (δ ^ A * δ' ^ B) * C := mul_le_mul hprod hsmall (by positivity) (by positivity)
    _ = C * δ ^ A * δ' ^ B := by ring

/-! ## Membership in `symIcc`, in the `natAbs` form -/

lemma notMem_symIcc_of_lt {L : ℕ} {x : ℤ} (hx : L < x.natAbs) : x ∉ symIcc L := by
  intro hmem
  rw [symIcc, Finset.mem_Icc] at hmem
  have h1 : |x| ≤ (L : ℤ) := abs_le.mpr ⟨hmem.1, hmem.2⟩
  rw [← Int.natCast_natAbs] at h1
  have h2 : x.natAbs ≤ L := by exact_mod_cast h1
  omega

lemma lt_natAbs_of_notMem_symIcc {L : ℕ} {x : ℤ} (hx : x ∉ symIcc L) : L < x.natAbs := by
  by_contra h
  push_neg at h
  exact hx (by
    rw [symIcc, Finset.mem_Icc]
    have h1 : (x.natAbs : ℤ) ≤ (L : ℤ) := by exact_mod_cast h
    rw [Int.natCast_natAbs] at h1
    exact abs_le.mp h1)

/-! ## The singleton direction set -/

lemma arithIcc_one_eq_singleton (c : ℤ) : arithIcc c 1 = {c} := by
  rw [arithIcc, Finset.Icc_self, Finset.image_singleton]
  norm_num

/-- The box-norm power at a singleton direction set is `(1/|S|) ∑_x ‖F x‖^{2^t}`. -/
lemma uNormPow_singleton_symIcc {t : ℕ} (ht : 1 ≤ t) {c : ℤ} {L : ℕ} {F : ℤ → ℂ}
    (hF : ∀ x : ℤ, x ∉ symIcc L → F x = 0) :
    uNormPow t ({c} : Finset ℤ) (symIcc L) F
      = ((symIcc L).card : ℝ)⁻¹ * ∑ x ∈ symIcc L, ‖F x‖ ^ (2 ^ t) := by
  have hfin : FinSuppZ F := FinSuppZ.of_supportIn (fun x hx => hF x (notMem_symIcc_of_lt hx))
  rw [uNormPow, Work.Peluse.Crux.boxNormPow_singleton (t := t) ht c (symIcc L) F hfin]
  rw [tsum_eq_sum (s := symIcc L) (f := fun x : ℤ => ‖F x‖ ^ (2 ^ t)) (fun x hx => by
    rw [hF x hx, norm_zero, zero_pow (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))])]

/-- At a singleton direction set the box-norm power is *decreasing* in the level. -/
lemma uNormPow_singleton_le_two {s : ℕ} (hs : 2 ≤ s) {c : ℤ} {L : ℕ} {F : ℤ → ℂ}
    (hF : ∀ x : ℤ, x ∉ symIcc L → F x = 0) (hbd : ∀ x : ℤ, ‖F x‖ ≤ 1) :
    uNormPow s ({c} : Finset ℤ) (symIcc L) F ≤ uNormPow 2 ({c} : Finset ℤ) (symIcc L) F := by
  rw [uNormPow_singleton_symIcc (by omega : 1 ≤ s) hF,
    uNormPow_singleton_symIcc (by norm_num : 1 ≤ 2) hF]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum (fun x _ => ?_)
  have h4 : (4 : ℕ) ≤ 2 ^ s := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hs
    simpa using this
  exact pow_le_pow_of_le_one (norm_nonneg _) (hbd x) h4

/-! ## Real arithmetic for the sharpness step -/

lemma div_mul_div_eq' (a b d n : ℝ) (hb : b ≠ 0) (hn : n ≠ 0) :
    a / b * (d / n) = a * d / (b * n) := by
  field_simp

/-! ## The main theorem -/

/-- **The target statement, given the single-step interface.** -/
theorem degree_lowering_v2_of_step {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (hstep : StepLe P (max 1 |(((P.leadingCoeff : ℤ)) : ℝ)|)) :
    ∀ s : ℕ, 2 ≤ s → ∃ K : ℕ, 1 ≤ K ∧
      ∀ (Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ),
        2 ≤ P.natDegree → 1 ≤ N → 1 ≤ Ns → Scaled Ns N P.natDegree → N ≤ Ns →
        1 ≤ D → (D : ℝ) ≤ (Ns : ℝ) →
        SupportIn f₀ Ns → SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        0 < δ → δ ≤ 1 →
        δ ≤ uNormPow s (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N))
              (dualFn N P f₀ f₁) →
        (δ * ((D : ℝ) / (Ns : ℝ))) ^ K ≤
          uNormPow 2 (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N))
            (dualFn N P f₀ f₁) := by
  intro s hs
  have htop : 2 ≤ P.natDegree := hd
  set K₀ : ℝ := max 1 |(((P.leadingCoeff : ℤ)) : ℝ)| with hK₀def
  have hKpos : 0 < K₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hKc : |(((P.leadingCoeff : ℤ)) : ℝ)| ≤ K₀ := le_max_right _ _
  have hlc0 : P.leadingCoeff ≠ 0 := by
    intro h
    have hP : P = 0 := Polynomial.leadingCoeff_eq_zero.mp h
    rw [hP] at htop
    simp at htop
  by_cases hs2 : s = 2
  · subst hs2
    refine ⟨1, le_refl 1, ?_⟩
    intro Ns N D f₀ f₁ δ hd' hN hNs hSc hNNs hD hDNs hs0 hs1 hb0 hb1 hδ0 hδ1 hbox
    have hNspos : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs
    have hq : (D : ℝ) / (Ns : ℝ) ≤ 1 := by rw [div_le_one hNspos]; exact_mod_cast hDNs
    have h1 : (δ * ((D : ℝ) / (Ns : ℝ))) ^ 1 ≤ δ := by
      rw [pow_one]; nlinarith [hδ0, hq]
    refine le_trans h1 ?_
    simpa only [uNormPow] using hbox
  · have hs3 : 3 ≤ s := by omega
    obtain ⟨A, B, hA, hB, c, hcpos, hchain⟩ := chain_bound hKpos hKc hstep htop s hs
    -- the uniform constant of the sharpness estimate
    set C_P : ℝ := 2 * ((ssAmax P : ℕ) : ℝ) with hC_P
    have hC_Ppos : 0 < C_P := by
      rw [hC_P]; have := ssAmax_pos P; positivity
    set c₂ : ℝ := ((s : ℕ) : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| / (4 * 2 ^ s * C_P) with hc₂
    have hc₂pos : 0 < c₂ := by
      rw [hc₂]
      have h1 : (0 : ℝ) < |(((P.leadingCoeff : ℤ)) : ℝ)| :=
        abs_pos.mpr (by exact_mod_cast hlc0)
      positivity
    set r : ℝ := max (if 2 * c₂ ≤ 1 then 1 - c₂ else 1 / (4 * c₂)) (1 - 1 / 2 ^ s) with hr
    have h2spos : (0 : ℝ) < 2 ^ s := by positivity
    have hr0 : 0 ≤ r := by
      rw [hr]
      refine le_max_of_le_left ?_
      by_cases hc : 2 * c₂ ≤ 1
      · rw [if_pos hc]; linarith
      · rw [if_neg hc]; positivity
    have hr1 : r < 1 := by
      rw [hr]
      refine max_lt ?_ ?_
      · by_cases hc : 2 * c₂ ≤ 1
        · rw [if_pos hc]; linarith
        · rw [if_neg hc]
          rw [div_lt_one (by linarith : (0 : ℝ) < 4 * c₂)]
          linarith
      · have h2s : (1 : ℝ) < 2 ^ s := one_lt_pow₀ one_lt_two (by omega)
        have hpos : (0 : ℝ) < 1 / 2 ^ s := by positivity
        linarith
    obtain ⟨Kc, hKc1, hKcuniv⟩ := final_compare_uniform (C := c) (r := r) hcpos hr0 hr1 A B
    refine ⟨max 4 Kc, le_trans (by norm_num : 1 ≤ 4) (le_max_left 4 Kc), ?_⟩
    intro Ns N D f₀ f₁ δ hd' hN hNs hSc hNNs hD hDNs hs0 hs1 hb0 hb1 hδ0 hδ1 hbox
    set F : ℤ → ℂ := dualFn N P f₀ f₁ with hF
    have hbF : ∀ x : ℤ, ‖F x‖ ≤ 1 := by
      intro x; rw [hF]; exact dualFn_norm_le_one hN P f₀ f₁ hb0 hb1 x
    have hsupF : ∀ x : ℤ, x ∉ symIcc (dSup P Ns N) → F x = 0 := by
      intro x hx
      rw [hF]
      exact Tools.dualFn_supportIn (by omega) P f₀ f₁ hs0 hs1 hNNs x (lt_natAbs_of_notMem_symIcc hx)
    have hNspos : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs
    have hδ'0 : (0 : ℝ) ≤ (D : ℝ) / (Ns : ℝ) := by positivity
    have hδ'1 : (D : ℝ) / (Ns : ℝ) ≤ 1 := by rw [div_le_one hNspos]; exact_mod_cast hDNs
    by_cases hD1 : D = 1
    · -- #### the singleton case
      subst hD1
      have hbox' : δ ≤ uNormPow s ({P.leadingCoeff} : Finset ℤ) (symIcc (dSup P Ns N)) F := by
        have h := hbox
        rw [arithIcc_one_eq_singleton] at h
        rw [hF] at h
        exact h
      have hmono : uNormPow s ({P.leadingCoeff} : Finset ℤ) (symIcc (dSup P Ns N)) F ≤
          uNormPow 2 ({P.leadingCoeff} : Finset ℤ) (symIcc (dSup P Ns N)) F :=
        uNormPow_singleton_le_two hs hsupF hbF
      have hδ22 : δ ≤ uNormPow 2 ({P.leadingCoeff} : Finset ℤ) (symIcc (dSup P Ns N)) F :=
        le_trans hbox' hmono
      set d1 : ℝ := (((1 : ℕ)) : ℝ) / (Ns : ℝ) with hd1
      have hd1le : d1 ≤ 1 := by
        rw [hd1, div_le_one hNspos]; exact_mod_cast hNs
      have hd1nn : 0 ≤ d1 := by rw [hd1]; positivity
      have hfac1 : δ * d1 ≤ 1 := by
        calc δ * d1 ≤ 1 * 1 := mul_le_mul hδ1 hd1le hd1nn (by norm_num)
          _ = 1 := by ring
      have hnn : (0 : ℝ) ≤ δ * d1 := by positivity
      have hexp : 1 ≤ max 4 Kc := le_trans (by norm_num : 1 ≤ 4) (le_max_left 4 Kc)
      have hK1 : (δ * d1) ^ max 4 Kc ≤ δ * d1 := by
        simpa using pow_le_pow_of_le_one hnn hfac1 hexp
      have hδle : δ * d1 ≤ δ := by
        calc δ * d1 ≤ δ * 1 := mul_le_mul_of_nonneg_left hd1le hδ0.le
          _ = δ := by ring
      have hfin := le_trans (le_trans hK1 hδle) hδ22
      simpa [arithIcc_one_eq_singleton, hF] using hfin
    · have hD2 : 2 ≤ D := by omega
      -- #### the sharpness bound
      have hsharp := boxNormPow_le_one_sub (t := s) (by omega) (c₀ := P.leadingCoeff) hlc0
        (D := D) hD2 (L := dSup P Ns N) (F := F) hbF hsupF
      have hboxb : δ ≤ boxNormPow s (fun _ : Fin s => arithIcc P.leadingCoeff D)
          (symIcc (dSup P Ns N)) F := by
        have h := hbox
        rw [hF] at h
        simpa only [uNormPow] using h
      have hδsharp : δ ≤ 1 - min ((((s : ℕ) : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ)) /
          (4 * 2 ^ s * (((2 * dSup P Ns N + 1 : ℕ)) : ℝ))) (1 / 2 ^ s) := le_trans hboxb hsharp
      -- the uniform bound on the denominator
      have hdSupBound : (((2 * dSup P Ns N + 1 : ℕ)) : ℝ) ≤ C_P * (Ns : ℝ) := by
        have h := dSup_div_add_one_le (P := P) (c := 1) (by omega) (by norm_num) hNs hN hSc
        have h' : dSup P Ns N + 1 ≤ ssAmax P * Ns := by simpa using h
        have h'' : ((dSup P Ns N : ℕ) : ℝ) + 1 ≤ ((ssAmax P : ℕ) : ℝ) * (Ns : ℝ) := by
          exact_mod_cast h'
        rw [hC_P]
        push_cast
        linarith
      have hdenle : 4 * 2 ^ s * (((2 * dSup P Ns N + 1 : ℕ)) : ℝ) ≤
          (4 * 2 ^ s * C_P) * (Ns : ℝ) := by
        nlinarith [hdSupBound, pow_pos (by norm_num : (0 : ℝ) < 2) s]
      have hnum : (0 : ℝ) ≤ ((s : ℕ) : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ) := by
        positivity
      have hdenpos : (0 : ℝ) < 4 * 2 ^ s * (((2 * dSup P Ns N + 1 : ℕ)) : ℝ) := by
        have : (0 : ℝ) < (((2 * dSup P Ns N + 1 : ℕ)) : ℝ) := by positivity
        positivity
      -- `c₂ · δ' ≤` the min-argument
      have hc₂δ' : c₂ * ((D : ℝ) / (Ns : ℝ)) ≤
          (((s : ℕ) : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ)) /
            (4 * 2 ^ s * (((2 * dSup P Ns N + 1 : ℕ)) : ℝ)) := by
        have hNne : (Ns : ℝ) ≠ 0 := ne_of_gt hNspos
        have hCne : 4 * 2 ^ s * C_P ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 4 * 2 ^ s * C_P)
        have hleft : c₂ * ((D : ℝ) / (Ns : ℝ)) =
            (((s : ℕ) : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ)) /
              ((4 * 2 ^ s * C_P) * (Ns : ℝ)) := by
          rw [hc₂, div_mul_div_eq' _ _ _ _ hCne hNne]
        rw [hleft]
        exact div_le_div_of_nonneg_left hnum hdenpos hdenle
      have hδsharp' : δ ≤ 1 - min (c₂ * ((D : ℝ) / (Ns : ℝ))) (1 / 2 ^ s) := by
        refine le_trans hδsharp ?_
        have hmin : min (c₂ * ((D : ℝ) / (Ns : ℝ))) (1 / 2 ^ s) ≤
            min ((((s : ℕ) : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ)) /
              (4 * 2 ^ s * (((2 * dSup P Ns N + 1 : ℕ)) : ℝ))) (1 / 2 ^ s) :=
          min_le_min hc₂δ' le_rfl
        linarith
      -- the uniform `r`
      have hδδ'r : δ * ((D : ℝ) / (Ns : ℝ)) ≤ r := by
        by_cases hle : c₂ * ((D : ℝ) / (Ns : ℝ)) ≤ 1 / 2 ^ s
        · have hmin : min (c₂ * ((D : ℝ) / (Ns : ℝ))) (1 / 2 ^ s) = c₂ * ((D : ℝ) / (Ns : ℝ)) :=
            min_eq_left hle
          rw [hmin] at hδsharp'
          have := prod_le_of_le_one_sub (δ := δ) (δ' := (D : ℝ) / (Ns : ℝ)) (u := c₂)
            hδ'0 hδ'1 hc₂pos hδsharp'
          rw [hr]
          exact le_trans this (le_max_left _ _)
        · have hle' : (1 : ℝ) / 2 ^ s ≤ c₂ * ((D : ℝ) / (Ns : ℝ)) := le_of_lt (not_le.mp hle)
          have hmin : min (c₂ * ((D : ℝ) / (Ns : ℝ))) (1 / 2 ^ s) = 1 / 2 ^ s := min_eq_right hle'
          rw [hmin] at hδsharp'
          rw [hr]
          refine le_trans ?_ (le_max_right _ _)
          have hp : (0 : ℝ) ≤ 1 - 1 / 2 ^ s := by linarith
          calc δ * ((D : ℝ) / (Ns : ℝ)) ≤ (1 - 1 / 2 ^ s) * 1 := by
                exact mul_le_mul hδsharp' hδ'1 hδ'0 hp
            _ = 1 - 1 / 2 ^ s := by ring
      have hKc2 := hKcuniv (δ := δ) (δ' := (D : ℝ) / (Ns : ℝ)) hδ0.le hδ1 hδ'0 hδ'1 hδδ'r
      have hchain' := hchain Ns N D f₀ f₁ δ hd' hN hNs hSc hNNs hD hDNs hs0 hs1 hb0 hb1 hδ0 hδ1 hbox
      have hfac : δ * ((D : ℝ) / (Ns : ℝ)) ≤ 1 := by nlinarith [hδ0, hδ1, hδ'0, hδ'1]
      have hnn : (0 : ℝ) ≤ δ * ((D : ℝ) / (Ns : ℝ)) := by positivity
      exact le_trans (pow_le_pow_of_le_one hnn hfac (le_max_right 4 Kc))
        (le_trans hKc2 hchain')

end

end Work.Peluse.Ulower
