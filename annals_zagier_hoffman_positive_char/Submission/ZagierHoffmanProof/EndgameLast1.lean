import Submission.ZagierHoffmanProof.EndgameKQ

/-!
# SESSION 362 — the last case `w = 2q-2`: the level-`1`/level-`0` dictionary

`PLAN.md` §«SESSION 362».  The `q`-th root `V` of `num + N·D` (`EndgameKQ.qthRootPoly`) satisfies
`σ V = num + N·D` and `num = L^w·V`.  This module establishes the structural facts about `V` that
Dac's explicit computation needs: `V ∈ A_0[X] = F_q[θ][X]` and `deg_θ (V.coeff m) ≤ 2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial
open scoped WithZero Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma ambTheta_pow_card_eq_ambThetaNu_one : (ambThetaNu F 1) ^ Nat.card F = ambTheta F := by
  simpa using ambThetaNu_pow F 1

/-! ## §1. The dictionary between the `θ_1`- and the `θ`-coefficient -/

/-- Every `θ_μ`-coefficient of an element of `A_μ` lies in the coefficient field. -/
lemma coeffNu_mem_ambF {μ j : ℕ} {x : Ambient F} (hx : x ∈ ambA F μ) :
    coeffNu F μ j x ∈ ambF F := by
  rw [coeffNu_of_mem F hx j]
  exact ambCoeff_mem_ambF F _

/-- `degTheta` is `degNu` at level `0`. -/
lemma degTheta_eq_degNu_zero {x : Ambient F} (hx : x ∈ ambA F 0) :
    degTheta F x = degNu F 0 x := by
  rw [degTheta_of_mem F hx, degNu_of_mem F hx]

/-- ★★ **The Frobenius scaling at `ν = 1`**: for `x ∈ A_0 ⊆ A_1` the `θ_1`-degree is `q` times the
`θ`-degree. -/
lemma degNu_one_eq_card_mul_degNu_zero {x : Ambient F} (hx : x ∈ ambA F 0) :
    degNu F 1 x = Nat.card F * degNu F 0 x := by
  have hx1 : x ∈ ambA F 1 := ambA_mono F (Nat.zero_le 1) hx
  rw [degNu_eq_degTheta_pow F hx1, pow_one, degTheta_pow_card F hx, degTheta_eq_degNu_zero F hx]

/-- For `x ∈ A_0`, its `θ`-coefficient of degree `i` is its `θ_1`-coefficient of degree `q·i`. -/
lemma coeffNu_one_mul_card_eq {x : Ambient F} (hx : x ∈ ambA F 0) (i : ℕ) :
    coeffNu F 1 (Nat.card F * i) x = coeffNu F 0 i x := by
  obtain ⟨p, hp⟩ := (mem_ambA_iff F 0 x).mp hx
  rw [ambThetaNu_zero F] at hp
  have hq : 0 < Nat.card F := Nat.pos_of_ne_zero (FrobPow.ne_zero (Ambient F) (q := Nat.card F))
  have hcomp : (Polynomial.expand F (Nat.card F) p).eval₂ (algebraMap F (Ambient F)) (ambThetaNu F 1)
      = p.eval₂ (algebraMap F (Ambient F)) (ambTheta F) := by
    rw [Polynomial.expand_eq_comp_X_pow, Polynomial.eval₂_comp, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, ambTheta_pow_card_eq_ambThetaNu_one F]
  have hmem0 : p.eval₂ (algebraMap F (Ambient F)) (ambTheta F) ∈ ambA F 0 :=
    (mem_ambA_iff F 0 _).mpr ⟨p, by rw [ambThetaNu_zero F]⟩
  have hmem1 : p.eval₂ (algebraMap F (Ambient F)) (ambTheta F) ∈ ambA F 1 :=
    ambA_mono F (Nat.zero_le 1) hmem0
  have hev0 : coeffNu F 0 i (p.eval₂ (algebraMap F (Ambient F)) (ambTheta F))
      = (algebraMap F (Ambient F)) (p.coeff i) :=
    coeffNu_eq_of_eval F hmem0 (p := p) (by rw [ambThetaNu_zero F]) i
  have hev1 : coeffNu F 1 (Nat.card F * i) (p.eval₂ (algebraMap F (Ambient F)) (ambTheta F))
      = (algebraMap F (Ambient F)) ((Polynomial.expand F (Nat.card F) p).coeff (Nat.card F * i)) :=
    coeffNu_eq_of_eval F hmem1 (p := Polynomial.expand F (Nat.card F) p) hcomp (Nat.card F * i)
  rw [← hp, hev0, hev1, Polynomial.coeff_expand_mul' hq p i]

/-- ★★★★★ **`A_0` as the `qℤ`-support part of `A_1`**: if every `θ_1`-coefficient of `x ∈ A_1` of
degree outside `qℤ` vanishes, then `x ∈ A_0 = F_q[θ]`. -/
lemma mem_ambA_zero_of_coeffNu_one_eq_zero {x : Ambient F} (hx : x ∈ ambA F 1)
    (h : ∀ j, ¬ Nat.card F ∣ j → coeffNu F 1 j x = 0) : x ∈ ambA F 0 := by
  rw [← sum_coeffNu_mul_ambThetaNu F 1 hx]
  refine (ambASub F 0).sum_mem fun j _ => ?_
  by_cases hqj : Nat.card F ∣ j
  · obtain ⟨i, rfl⟩ := hqj
    have htheta : (ambThetaNu F 1) ^ (Nat.card F * i) = (ambTheta F) ^ i := by
      rw [pow_mul, ambTheta_pow_card_eq_ambThetaNu_one F]
    have hc : coeffNu F 1 (Nat.card F * i) x ∈ ambF F := coeffNu_mem_ambF F hx
    have h1 : coeffNu F 1 (Nat.card F * i) x ∈ ambA F 0 := ambF_subset_ambA_zero (F := F) hc
    have h2 : (ambTheta F) ^ i ∈ ambA F 0 :=
      ambA_pow_mem F 0 (ambTheta_mem_ambA F 0) i
    rw [htheta]
    exact ambA_mul_mem F h1 h2
  · rw [h j hqj, zero_mul]
    exact (ambASub F 0).zero_mem

/-- ★★ **The `θ`-degree bound from the `θ_1`-degree bound.** -/
lemma degNu_zero_le_of_degNu_one {x : Ambient F} (hx : x ∈ ambA F 1) {d : ℕ}
    (h : degNu F 1 x ≤ Nat.card F * d)
    (h0 : ∀ j, ¬ Nat.card F ∣ j → coeffNu F 1 j x = 0) :
    degNu F 0 x ≤ d := by
  have hx0 : x ∈ ambA F 0 := mem_ambA_zero_of_coeffNu_one_eq_zero F hx h0
  have h1 := degNu_one_eq_card_mul_degNu_zero F hx0
  have hq : 0 < Nat.card F := Nat.pos_of_ne_zero (FrobPow.ne_zero (Ambient F) (q := Nat.card F))
  rw [h1] at h
  exact Nat.le_of_mul_le_mul_left h hq


/-! ## §2. `V ∈ A_0[X]` and `deg_θ (V.coeff m) ≤ 2` -/

/-- ★★★ **The `θ_1`-degree of the coefficientwise `q`-th root**: the root of an element of `A_0` of
`θ`-degree `d` has `θ_1`-degree exactly `d`. -/
lemma qthRootPoly_degNu_one_le {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (m : ℕ) :
    degNu F 1 ((qthRootPoly F p hp).coeff m) ≤ degPolyNu F 0 p := by
  classical
  rw [qthRootPoly_coeff F hp m]
  by_cases hm : m ∈ p.support
  · rw [if_pos hm]
    have hq : 0 < Nat.card F := Nat.pos_of_ne_zero (FrobPow.ne_zero (Ambient F) (q := Nat.card F))
    have hroot : ambRootAt F 0 1 (p.coeff m) (hp m) ∈ ambA F 1 := by
      simpa using ambRootAt_mem F 0 1 (p.coeff m) (hp m)
    have h1 : (ambRootAt F 0 1 (p.coeff m) (hp m)) ^ Nat.card F = p.coeff m := by
      simpa using ambRootAt_pow F 0 1 (p.coeff m) (hp m)
    have h2 : Nat.card F * degNu F 1 (ambRootAt F 0 1 (p.coeff m) (hp m))
        = Nat.card F * degNu F 0 (p.coeff m) := by
      rw [← degNu_pow_card F hroot, h1, degNu_one_eq_card_mul_degNu_zero F (hp m)]
    rw [Nat.mul_left_cancel_iff hq] at h2
    rw [h2]
    exact degPolyNu_coeff_le F hp m
  · rw [if_neg hm, degNu_zero]
    exact Nat.zero_le _

/-- ★★★★★ **The two structural facts about the `q`-th root `V`.**  If
`num = L^w·V` with `num ∈ A_0[X]`, `V ∈ A_1[X]` and `deg_{θ_1}(V.coeff n) ≤ 2q`, then every
coefficient of `V` lies in `A_0 = F_q[θ]` and has `θ`-degree at most `2`.  (The `θ_1`-support of `V`
lies in `qℤ` by `V_theta_one_reads`/`V_theta_one_reads_add`, and the degree bound upgrades this to
`{0, q, 2q}`.) -/
theorem V_support_and_deg {w : ℕ} {V num : Polynomial (Ambient F)}
    (hV : ∀ n, V.coeff n ∈ ambA F 1)
    (hnum : ∀ n, num.coeff n ∈ ambA F 0)
    (hprod : num = (Polynomial.X - Polynomial.C (ambTheta F)) ^ w * V)
    (hbound : ∀ n, degNu F 1 (V.coeff n) ≤ 2 * Nat.card F) (hq : 3 ≤ Nat.card F) :
    (∀ m, V.coeff m ∈ ambA F 0) ∧ (∀ m, degNu F 0 (V.coeff m) ≤ 2) := by
  have hzero : ∀ m j, ¬ Nat.card F ∣ j → coeffNu F 1 j (V.coeff m) = 0 := by
    intro m j hj
    rcases lt_trichotomy j (Nat.card F) with h | h | h
    · have hj0 : j ≠ 0 := fun h0 => hj (h0 ▸ dvd_zero _)
      have hj1 : 1 ≤ j := by omega
      exact V_theta_one_reads F hV hnum hprod hj hj1 h m
    · rw [h] at hj
      exact absurd (dvd_refl (Nat.card F)) hj
    · rcases lt_trichotomy j (2 * Nat.card F) with h2 | h2 | h2
      · have ht : Nat.card F + (j - Nat.card F) = j := by omega
        have ht1 : 1 ≤ j - Nat.card F := by omega
        have htq2 : j - Nat.card F < Nat.card F := by omega
        have hsubnot : ¬ Nat.card F ∣ j - Nat.card F := by
          rintro ⟨k, hk⟩
          refine hj ⟨k + 1, ?_⟩
          calc j = (j - Nat.card F) + Nat.card F := (Nat.sub_add_cancel (le_of_lt h)).symm
            _ = Nat.card F * k + Nat.card F := by rw [hk]
            _ = Nat.card F * (k + 1) := by rw [Nat.mul_succ]
        have hfirst : ∀ j', coeffNu F 1 (j - Nat.card F) (V.coeff j') = 0 :=
          fun j' => V_theta_one_reads F hV hnum hprod hsubnot ht1 htq2 j'
        have hres := V_theta_one_reads_add F (w := w) hV hnum hprod hsubnot ht1 htq2 hfirst m
        rwa [ht] at hres
      · rw [h2] at hj
        exact absurd (dvd_mul_left (Nat.card F) 2) hj
      · exact coeffNu_degNu_lt F (hV m) (lt_of_le_of_lt (hbound m) h2)
  refine ⟨fun m => mem_ambA_zero_of_coeffNu_one_eq_zero F (hV m) (hzero m), fun m => ?_⟩
  refine degNu_zero_le_of_degNu_one F (hV m) (d := 2) ?_ (hzero m)
  rw [mul_comm (Nat.card F) 2]
  exact hbound m

end ZagierHoffmanPositiveChar
