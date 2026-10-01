import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.card_hensel_le
import Submission.Work.LinnikBurgess.critN_tripleVanish_content
import Submission.Work.LinnikBurgess.aeval_dist_eq_norm
import Submission.Work.LinnikBurgess.eq_of_dvd_sub_of_lt
import Submission.Work.LinnikBurgess.lfSmall.content_dvd_critN

open Polynomial
open scoped BigOperators
open Classical

namespace Work.LinnikBurgess.lfSmall

/-! ## The `p = 3` cap-set counting lemmas

This file proves the two cardinality bounds on `capSet 3 e a b` needed by
`Work.LinnikBurgess.lfSmall.counting_three`:

* `cap_count_noncontent_three` : `¬ 3 ∣ contAB a b` implies `card ≤ 100`;
* `cap_count_content_three`    : the sharp content count
  `card ≤ 10^3 * 3^(m - (m + T - J - 1)/2)` with `J = v_3(contAB a b)`.

Both use the fact that for `y ∈ capSet`, the transfer hypothesis gives
`3^(m + T) ∣ N(y)` where `N = critN a b`, while `3^T ∣ N'(y)`; the triple
vanishing lemma `critN_tripleVanish_content` at `k = 2` (resp. `k = J + 2`)
controls `N''(y)` and Hensel's lemma then confines the elements of `capSet`
to neighbourhoods of size `3^{-E}` of roots of suitable polynomials.
-/

/-! ### Arithmetic for `p = 3` -/

private lemma cubeLevel_three_eq (e : ℕ) : cubeLevel 3 e = (e + 2) / 3 := by
  rw [cubeLevel, if_neg (by norm_num : ¬ (3 : ℕ) = 2)]

private lemma capLevel_three_le_cubeLevel_three (e : ℕ) : capLevel 3 e ≤ cubeLevel 3 e := by
  rw [capLevel, cubeLevel_three_eq]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

private lemma cubeLevel_three_le_capLevel_three_add_two (e : ℕ) :
    cubeLevel 3 e ≤ capLevel 3 e + 2 := by
  rw [capLevel, cubeLevel_three_eq]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

private lemma three_le_capLevel_three {e : ℕ} (he : 13 ≤ e) : 3 ≤ capLevel 3 e := by
  rw [capLevel, cubeLevel_three_eq]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

private lemma padicValNat_three_six : padicValNat 3 6 = 1 := by
  have hne6 : (6 : ℕ) ≠ 0 := by norm_num
  refine le_antisymm ?_ ((padicValNat_dvd_iff_le hne6).1 (by norm_num))
  by_contra hc
  push_neg at hc
  have hd : 3 ^ 2 ∣ (6 : ℕ) :=
    dvd_trans (pow_dvd_pow 3 (by omega : 2 ≤ padicValNat 3 6)) pow_padicValNat_dvd
  norm_num at hd

/-! ### Hensel machinery at `p = 3` (transcriptions of the `p = 2` versions) -/

/-- **Hensel step.**  If `3 ^ ν` is the exact power of `3` dividing `P'(y)` and `3 ^ K ∣ P(y)`
with `2 * ν < K`, then `P` has a root `θ` in `ℤ_[3]` with `‖y - θ‖ ≤ 3 ^ (-(K - ν))`. -/
private lemma hensel_root_close_three {P : Polynomial ℤ} {y K ν : ℕ}
    (hKν : 2 * ν < K) (hK : ((3 ^ K : ℕ) : ℤ) ∣ P.eval ((y : ℤ)))
    (hne : P.derivative.eval ((y : ℤ)) ≠ 0)
    (hν : padicValNat 3 (P.derivative.eval ((y : ℤ))).natAbs = ν) :
    ∃ θ : ℤ_[3], P.aeval θ = 0 ∧
      ‖(((y : ℤ)) : ℤ_[3]) - θ‖ ≤ (3 : ℝ) ^ (-((K - ν : ℕ) : ℤ)) := by
  classical
  have hne' : (P.derivative.eval ((y : ℤ))).natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using hne
  have h1 : ((3 ^ ν : ℕ) : ℤ) ∣ P.derivative.eval ((y : ℤ)) := by
    rw [← Int.dvd_natAbs]
    exact_mod_cast (show 3 ^ ν ∣ (P.derivative.eval ((y : ℤ))).natAbs by
      rw [← hν]; exact pow_padicValNat_dvd)
  have h2 : ¬ ((3 ^ (ν + 1) : ℕ) : ℤ) ∣ P.derivative.eval ((y : ℤ)) := by
    intro hc
    have hnat : 3 ^ (ν + 1) ∣ (P.derivative.eval ((y : ℤ))).natAbs := by
      have hh := (Int.natAbs_dvd_natAbs (a := ((3 ^ (ν + 1) : ℕ) : ℤ))
        (b := P.derivative.eval ((y : ℤ)))).mpr hc
      simpa using hh
    have hle := (padicValNat_dvd_iff_le hne').1 hnat
    rw [hν] at hle
    omega
  have hnormW : ‖P.aeval (((y : ℤ)) : ℤ_[3])‖ ≤ (3 : ℝ) ^ (-(K : ℤ)) :=
    cardHensel_norm_aeval_le_of_dvd (p := 3) (P := P) (y := y) (k := K) hK
  have hnormD : ‖P.derivative.aeval (((y : ℤ)) : ℤ_[3])‖ = (3 : ℝ) ^ (-(ν : ℤ)) :=
    cardHensel_norm_aeval_deriv_eq_of_padic (p := 3) (P := P) (y := y) (ν := ν) h1 h2
  have hlt : ‖P.aeval (((y : ℤ)) : ℤ_[3])‖
      < ‖P.derivative.aeval (((y : ℤ)) : ℤ_[3])‖ ^ 2 := by
    rw [hnormD]
    have hsq : ((3 : ℝ) ^ (-(ν : ℤ))) ^ 2 = (3 : ℝ) ^ (-((2 * ν : ℕ) : ℤ)) := by
      rw [sq, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1; push_cast; ring
    rw [hsq]
    exact lt_of_le_of_lt hnormW
      ((zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).2 (by push_cast; omega))
  obtain ⟨θ, hθ0, hθlt, hθD, -⟩ := hensels_lemma hlt
  refine ⟨θ, hθ0, ?_⟩
  have hlt' : ‖(((y : ℤ)) : ℤ_[3]) - θ‖ < ‖P.derivative.aeval θ‖ := by
    rw [norm_sub_rev, hθD]
    exact hθlt
  have hprod := aeval_dist_eq_norm P hθ0 hlt'
  rw [hθD, hnormD] at hprod
  have hle : ‖(((y : ℤ)) : ℤ_[3]) - θ‖ * (3 : ℝ) ^ (-(ν : ℤ)) ≤ (3 : ℝ) ^ (-(K : ℤ)) := by
    rw [hprod]; exact hnormW
  have hmul : (3 : ℝ) ^ (-((K - ν : ℕ) : ℤ)) * (3 : ℝ) ^ (-(ν : ℤ))
      = (3 : ℝ) ^ (-(K : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    push_cast
    omega
  rw [← hmul] at hle
  exact (mul_le_mul_iff_of_pos_right (zpow_pos (by norm_num : (0 : ℝ) < 3) _)).1 hle

/-- Two naturals with the same quotient by `3 ^ E` whose difference is a multiple of `3 ^ E`
agree. -/
private lemma eq_of_div_eq_div_of_dvd_sub_three {E u v : ℕ}
    (hdvd : ((3 ^ E : ℕ) : ℤ) ∣ (u : ℤ) - (v : ℤ)) (hq : u / 3 ^ E = v / 3 ^ E) : u = v := by
  have hsym : ((3 ^ E : ℕ) : ℤ) ∣ (v : ℤ) - (u : ℤ) := by
    have he : ((v : ℤ) - (u : ℤ)) = -(((u : ℤ) - (v : ℤ))) := by ring
    rw [he]; exact dvd_neg.mpr hdvd
  have hmod : u % 3 ^ E = v % 3 ^ E := Nat.modEq_iff_dvd.mpr hsym
  have h1 := Nat.div_add_mod u (3 ^ E)
  have h2 := Nat.div_add_mod v (3 ^ E)
  rw [hq, hmod] at h1
  exact h1.symm.trans h2

/-- If every element of `S ⊆ {0, …, 3^N - 1}` lies within `3 ^ (-E)` of a root in `ℤ_[3]` of a
nonzero integral polynomial `Q`, then `card S ≤ natDegree Q * 3 ^ (N - E)`. -/
private lemma card_root_close_le_three {Q : Polynomial ℤ} (hQ : Q ≠ 0) {N E : ℕ} (S : Finset ℕ)
    (hrange : ∀ y ∈ S, y < 3 ^ N)
    (hroot : ∀ y ∈ S, ∃ θ : ℤ_[3], Q.aeval θ = 0 ∧
      ‖(((y : ℤ)) : ℤ_[3]) - θ‖ ≤ (3 : ℝ) ^ (-(E : ℤ))) :
    (S.card : ℝ) ≤ (Q.natDegree : ℝ) * (3 : ℝ) ^ (N - E) := by
  classical
  let f : ℕ → ℤ_[3] := fun y => if h : ∃ θ : ℤ_[3], Q.aeval θ = 0 ∧
      ‖(((y : ℤ)) : ℤ_[3]) - θ‖ ≤ (3 : ℝ) ^ (-(E : ℤ))
    then Classical.choose h else 0
  have hf : ∀ y (hy : y ∈ S), Q.aeval (f y) = 0 ∧
      ‖(((y : ℤ)) : ℤ_[3]) - f y‖ ≤ (3 : ℝ) ^ (-(E : ℤ)) := by
    intro y hy
    have hh := hroot y hy
    have hfy : f y = Classical.choose hh := by
      show (if h : ∃ θ : ℤ_[3], Q.aeval θ = 0 ∧
        ‖(((y : ℤ)) : ℤ_[3]) - θ‖ ≤ (3 : ℝ) ^ (-(E : ℤ))
        then Classical.choose h else 0) = Classical.choose hh
      exact dif_pos hh
    rw [hfy]
    exact Classical.choose_spec hh
  have hQmap : Q.map (algebraMap ℤ ℤ_[3]) ≠ 0 := by
    intro h
    exact hQ ((Polynomial.map_eq_zero_iff (f := algebraMap ℤ ℤ_[3])
      (fun x y hxy => (PadicInt.intCast_eq x y).1 hxy)).1 h)
  have hmaps : ∀ y ∈ S, f y ∈ (Q.map (algebraMap ℤ ℤ_[3])).roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    refine ⟨hQmap, ?_⟩
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact (hf y hy).1
  have hquot : ∀ y ∈ S, y / 3 ^ E < 3 ^ (N - E) := by
    intro y hy
    have hyN := hrange y hy
    rcases le_or_gt E N with hEN | hEN
    · rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < 3 ^ E)]
      rw [← pow_add, Nat.sub_add_cancel hEN]
      exact hyN
    · have hpow : 3 ^ N ≤ 3 ^ E := Nat.le_of_dvd (by positivity) (pow_dvd_pow 3 (by omega))
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hyN hpow)]
      exact pow_pos (by norm_num) _
  have hinj : Set.InjOn (fun y => (f y, y / 3 ^ E)) ↑S := by
    intro y₁ h₁ y₂ h₂ heq
    have hf12 : f y₁ = f y₂ := congrArg Prod.fst heq
    have hq12 : y₁ / 3 ^ E = y₂ / 3 ^ E := congrArg Prod.snd heq
    have hd1 := (hf y₁ h₁).2
    have hd2 := (hf y₂ h₂).2
    have hdist : ‖(((y₁ : ℤ)) : ℤ_[3]) - (((y₂ : ℤ)) : ℤ_[3])‖
        ≤ (3 : ℝ) ^ (-(E : ℤ)) := by
      have hz : (((y₁ : ℤ)) : ℤ_[3]) - (((y₂ : ℤ)) : ℤ_[3])
          = ((((y₁ : ℤ)) : ℤ_[3]) - f y₁) + (f y₁ - (((y₂ : ℤ)) : ℤ_[3])) := by ring
      rw [hz]
      refine (PadicInt.nonarchimedean _ _).trans (max_le hd1 ?_)
      rw [hf12, norm_sub_rev]
      exact hd2
    have hdvd : ((3 ^ E : ℕ) : ℤ) ∣ ((y₁ : ℤ) - (y₂ : ℤ)) := by
      have hcast : (((y₁ : ℤ) - (y₂ : ℤ) : ℤ) : ℤ_[3])
          = (((y₁ : ℤ)) : ℤ_[3]) - (((y₂ : ℤ)) : ℤ_[3]) := by push_cast; ring
      exact (PadicInt.norm_int_le_pow_iff_dvd).1 (by rw [hcast]; exact hdist)
    exact eq_of_div_eq_div_of_dvd_sub_three hdvd hq12
  have hsub : S.image (fun y => (f y, y / 3 ^ E))
      ⊆ (Q.map (algebraMap ℤ ℤ_[3])).roots.toFinset ×ˢ Finset.range (3 ^ (N - E)) := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨hmaps y hy, Finset.mem_range.mpr (hquot y hy)⟩
  have hrcard : ((Q.map (algebraMap ℤ ℤ_[3])).roots.toFinset.card : ℝ) ≤ Q.natDegree := by
    have h1 : (Q.map (algebraMap ℤ ℤ_[3])).roots.toFinset.card
        ≤ (Q.map (algebraMap ℤ ℤ_[3])).natDegree :=
      le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)
    have h2 : (Q.map (algebraMap ℤ ℤ_[3])).natDegree ≤ Q.natDegree :=
      Polynomial.natDegree_map_le
    exact_mod_cast le_trans h1 h2
  calc (S.card : ℝ) = ((S.image (fun y => (f y, y / 3 ^ E))).card : ℝ) := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ (((Q.map (algebraMap ℤ ℤ_[3])).roots.toFinset
          ×ˢ Finset.range (3 ^ (N - E))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ((Q.map (algebraMap ℤ ℤ_[3])).roots.toFinset.card : ℝ) * (3 : ℝ) ^ (N - E) := by
        rw [Finset.card_product, Finset.card_range, Nat.cast_mul, Nat.cast_pow]
        norm_num
    _ ≤ (Q.natDegree : ℝ) * (3 : ℝ) ^ (N - E) :=
        mul_le_mul_of_nonneg_right hrcard (by positivity)

/-! ### The noncontent count -/

/-- **`p = 3`, non-content case.**  If `3 ∤ contAB a b` then the capped part of the support has at
most `100` points. -/
theorem cap_count_noncontent_three {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hdeg2 : 2 ≤ (critN a b).natDegree) (hdeg : (critN a b).natDegree ≤ 4)
    (hmod : ¬ (3 : ℕ) ∣ contAB a b) (hbt : SuppTransfer 3 e a b) :
    (capSet 3 e a b).card ≤ 100 := by
  classical
  set m := cubeLevel 3 e with hmdef
  set T := capLevel 3 e with hTdef
  have hNne : critN a b ≠ 0 := by
    intro h; rw [h] at hdeg2; simp at hdeg2
  have hN'ne : (critN a b).derivative ≠ 0 := by
    rw [Polynomial.derivative_ne_zero]; omega
  have hN'deg : (critN a b).derivative.natDegree ≤ 3 := by
    have h := Polynomial.natDegree_derivative_le (critN a b)
    omega
  have hT3 : 3 ≤ T := by rw [hTdef]; exact three_le_capLevel_three he
  have hTm : T ≤ m := by rw [hTdef, hmdef]; exact capLevel_three_le_cubeLevel_three e
  have hmT : m ≤ T + 2 := by rw [hTdef, hmdef]; exact cubeLevel_three_le_capLevel_three_add_two e
  have hm1 : 1 ≤ m := by omega
  have hrange : ∀ y ∈ capSet 3 e a b, y < 3 ^ m := by
    intro y hy
    rw [capSet, Finset.mem_filter, suppSet, Finset.mem_filter] at hy
    have hlt := Finset.mem_range.mp hy.1.1
    simpa [hmdef] using hlt
  have hroot : ∀ y ∈ capSet 3 e a b, ∃ θ : ℤ_[3], (critN a b).derivative.aeval θ = 0 ∧
      ‖(((y : ℤ)) : ℤ_[3]) - θ‖ ≤ (3 : ℝ) ^ (-((T - 1 : ℕ) : ℤ)) := by
    intro y hy
    rw [capSet, Finset.mem_filter] at hy
    obtain ⟨hysup, hynv⟩ := hy
    rw [suppSet, Finset.mem_filter] at hysup
    obtain ⟨hyrange, hpred⟩ := hysup
    obtain ⟨hbval, hdivN⟩ := hbt y hpred
    have hbvalT : bval 3 e a b y = T := by rw [hbval]; exact min_eq_right hynv
    have hNdiv : ((3 ^ (m + T) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) := by
      have h1 : m + bval 3 e a b y = m + T := by rw [hbvalT]
      rwa [h1] at hdivN
    have h2N : ((3 ^ 2 : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) :=
      dvd_trans (by exact_mod_cast (pow_dvd_pow 3 (by omega : 2 ≤ m + T))) hNdiv
    rw [suppPred] at hpred
    by_cases hN'0 : (critN a b).derivative.eval (y : ℤ) = 0
    · refine ⟨(((y : ℤ)) : ℤ_[3]), ?_, ?_⟩
      · rw [cardHensel_aeval_natCast, hN'0, Int.cast_zero]
      · rw [sub_self, norm_zero]; exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    · have hνge : T ≤ padicValNat 3 ((critN a b).derivative.eval (y : ℤ)).natAbs := by
        have hnv : nval 3 e a b y
            = padicValNat 3 ((critN a b).derivative.eval (y : ℤ)).natAbs := by
          rw [nval, if_neg hN'0]
        rw [← hnv]; exact hynv
      have h2N' : ((3 ^ 2 : ℕ) : ℤ) ∣ (critN a b).derivative.eval (y : ℤ) := by
        rw [← Int.dvd_natAbs]
        exact_mod_cast (dvd_trans (pow_dvd_pow 3 (by omega : 2 ≤ T))
          (dvd_trans (pow_dvd_pow 3 hνge) pow_padicValNat_dvd))
      have hnotN'' : ¬ ((3 ^ 2 : ℕ) : ℤ) ∣ (critN a b).derivative.derivative.eval (y : ℤ) := by
        intro h3
        have htv := critN_tripleVanish_content (p := 3) (k := 2) a b y hpred.1 h2N h2N' h3
        rw [padicValNat_three_six] at htv
        norm_num at htv
        exact hmod htv
      have hN''0 : (critN a b).derivative.derivative.eval (y : ℤ) ≠ 0 := by
        intro h0; exact hnotN'' (by rw [h0]; exact dvd_zero _)
      set ν := padicValNat 3 ((critN a b).derivative.derivative.eval (y : ℤ)).natAbs with hνdef
      have hνle1 : ν ≤ 1 := by
        by_contra hc
        push_neg at hc
        exact hnotN'' (by
          rw [← Int.dvd_natAbs]
          exact_mod_cast (dvd_trans (pow_dvd_pow 3 (by omega : 2 ≤ ν))
            (by rw [hνdef]; exact pow_padicValNat_dvd)))
      set K := min (padicValNat 3 ((critN a b).derivative.eval (y : ℤ)).natAbs) m with hKdef
      have hK3 : 3 ≤ K := by rw [hKdef]; exact le_min (by omega) (by omega)
      have hKT : T ≤ K := by rw [hKdef]; exact le_min hνge hTm
      have hKν : 2 * ν < K := by omega
      have h3K : ((3 ^ K : ℕ) : ℤ) ∣ (critN a b).derivative.eval (y : ℤ) := by
        rw [← Int.dvd_natAbs]
        exact_mod_cast (dvd_trans (pow_dvd_pow 3 (by rw [hKdef]; exact min_le_left _ _))
          pow_padicValNat_dvd)
      obtain ⟨θ, hθ0, hθd⟩ := hensel_root_close_three (P := (critN a b).derivative) (y := y)
        (K := K) (ν := ν) hKν h3K hN''0 hνdef.symm
      refine ⟨θ, hθ0, hθd.trans ?_⟩
      exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mpr
        (neg_le_neg (by exact_mod_cast (by omega : T - 1 ≤ K - ν)))
  have hcard := card_root_close_le_three (Q := (critN a b).derivative) hN'ne
    (S := capSet 3 e a b) (N := m) (E := T - 1) hrange hroot
  have hdegR : (((critN a b).derivative.natDegree : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hN'deg
  have hp27 : (3 : ℝ) ^ (m - (T - 1)) ≤ 27 := by
    have hle : m - (T - 1) ≤ 3 := by omega
    calc (3 : ℝ) ^ (m - (T - 1)) ≤ (3 : ℝ) ^ 3 :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hle
      _ = 27 := by norm_num
  have hbound : ((capSet 3 e a b).card : ℝ) ≤ 81 := by
    calc ((capSet 3 e a b).card : ℝ)
        ≤ (((critN a b).derivative.natDegree : ℕ) : ℝ) * (3 : ℝ) ^ (m - (T - 1)) := hcard
      _ ≤ 3 * 27 := mul_le_mul hdegR hp27 (by positivity) (by norm_num)
      _ = 81 := by norm_num
  exact_mod_cast (le_trans hbound (by norm_num : (81 : ℝ) ≤ 100))

/-! ### The content count -/

/-- **`p = 3`, content case.**  With `J` the `3`-adic valuation of `contAB a b` and `h` an exact
content level of `critN a b` satisfying `1 ≤ h ≤ J + 1`, the capped part of the support is at most
`10^3 · 3^(m - ⌊(m + T - J - 1)/2⌋)`, where `m = cubeLevel 3 e` and `T = capLevel 3 e`. -/
theorem cap_count_content_three {e h J : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hdeg2 : 2 ≤ (critN a b).natDegree) (hdeg : (critN a b).natDegree ≤ 4)
    (hcontent : ∀ n, ((3 ^ h : ℕ) : ℤ) ∣ (critN a b).coeff n)
    (hprim : ∃ n, ¬ ((3 ^ (h + 1) : ℕ) : ℤ) ∣ (critN a b).coeff n)
    (hbt : SuppTransfer 3 e a b) (hJ1 : 1 ≤ h) (hhJ : h ≤ J + 1)
    (hJdiv : (3 ^ J : ℕ) ∣ contAB a b) (hJndiv : ¬ (3 ^ (J + 1) : ℕ) ∣ contAB a b) :
    (capSet 3 e a b).card
      ≤ 10 ^ 3 * 3 ^ max 0 (cubeLevel 3 e - (cubeLevel 3 e + capLevel 3 e - J - 1) / 2) := by
  classical
  set m := cubeLevel 3 e with hmdef
  set T := capLevel 3 e with hTdef
  have hNne : critN a b ≠ 0 := by
    intro h0; rw [h0] at hdeg2; simp at hdeg2
  have hcont0 : contAB a b ≠ 0 := by
    intro h0
    exact hJndiv (by rw [h0]; exact dvd_zero _)
  have hJv : padicValNat 3 (contAB a b) = J := by
    refine le_antisymm ?_ ((padicValNat_dvd_iff_le hcont0).mp hJdiv)
    by_contra hc
    push_neg at hc
    exact hJndiv (dvd_trans (pow_dvd_pow 3 (by omega : J + 1 ≤ padicValNat 3 (contAB a b)))
      pow_padicValNat_dvd)
  have hTm : T ≤ m := by rw [hTdef, hmdef]; exact capLevel_three_le_cubeLevel_three e
  have hJcoeff : ∀ n : ℕ, ((3 ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n :=
    dvd_coeff_critN_of_dvd_contAB (3 ^ J) a b hJdiv
  obtain ⟨M, hNM⟩ :=
    (Polynomial.C_dvd_iff_dvd_coeff (((3 ^ J : ℕ) : ℤ)) (critN a b)).mpr hJcoeff
  have hMne : M ≠ 0 := by intro h0; rw [h0, mul_zero] at hNM; exact hNne hNM
  have hMdeg : M.natDegree = (critN a b).natDegree := by
    rw [hNM, Polynomial.natDegree_C_mul (by positivity : (((3 ^ J : ℕ) : ℤ)) ≠ 0)]
  have hMeval : ∀ y : ℕ, (critN a b).eval (y : ℤ) = (((3 ^ J : ℕ) : ℤ)) * M.eval (y : ℤ) := by
    intro y; rw [hNM, Polynomial.eval_mul, Polynomial.eval_C]
  have hMd : (critN a b).derivative = Polynomial.C (((3 ^ J : ℕ) : ℤ)) * M.derivative := by
    rw [hNM, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
  have hMdeval : ∀ y : ℕ, (critN a b).derivative.eval (y : ℤ)
      = (((3 ^ J : ℕ) : ℤ)) * M.derivative.eval (y : ℤ) := by
    intro y; rw [hMd, Polynomial.eval_mul, Polynomial.eval_C]
  have hMd2 : (critN a b).derivative.derivative
      = Polynomial.C (((3 ^ J : ℕ) : ℤ)) * M.derivative.derivative := by
    rw [hMd, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
  have hMd2eval : ∀ y : ℕ, (critN a b).derivative.derivative.eval (y : ℤ)
      = (((3 ^ J : ℕ) : ℤ)) * M.derivative.derivative.eval (y : ℤ) := by
    intro y; rw [hMd2, Polynomial.eval_mul, Polynomial.eval_C]
  have hM'ne : M.derivative ≠ 0 := by
    rw [Polynomial.derivative_ne_zero, hMdeg]; omega
  have hrange : ∀ y ∈ capSet 3 e a b, y < 3 ^ m := by
    intro y hy
    rw [capSet, Finset.mem_filter, suppSet, Finset.mem_filter] at hy
    have hlt := Finset.mem_range.mp hy.1.1
    simpa [hmdef] using hlt
  have hunit : ∀ y ∈ capSet 3 e a b, UnitAt 3 y a b := by
    intro y hy
    rw [capSet, Finset.mem_filter] at hy
    obtain ⟨hysup, -⟩ := hy
    rw [suppSet, Finset.mem_filter] at hysup
    obtain ⟨-, hpred⟩ := hysup
    rw [suppPred] at hpred
    exact hpred.1
  have hmem : ∀ y ∈ capSet 3 e a b, ((3 ^ (m + T) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) := by
    intro y hy
    rw [capSet, Finset.mem_filter] at hy
    obtain ⟨hysup, hynv⟩ := hy
    rw [suppSet, Finset.mem_filter] at hysup
    obtain ⟨hyrange, hpred⟩ := hysup
    obtain ⟨hbval, hdivN⟩ := hbt y hpred
    have hbvalT : bval 3 e a b y = T := by rw [hbval]; exact min_eq_right hynv
    have h1 : m + bval 3 e a b y = m + T := by rw [hbvalT]
    rwa [h1] at hdivN
  by_cases hKc : 14 ≤ m + T - J - 1
  · -- the fine branch
    set K := m + T - J with hKdef
    set E := (m + T - J - 1) / 2 - 2 with hEdef
    have hK15 : 15 ≤ K := by rw [hKdef]; omega
    have hJK : J + K = m + T := by rw [hKdef]; omega
    have hmK : ∀ y ∈ capSet 3 e a b, ((3 ^ K : ℕ) : ℤ) ∣ M.eval (y : ℤ) := by
      intro y hy
      have hN := hmem y hy
      have h1 : ((3 ^ (m + T) : ℕ) : ℤ) = (((3 ^ J : ℕ) : ℤ)) * (((3 ^ K : ℕ) : ℤ)) := by
        rw [← hJK]; push_cast; rw [pow_add]
      have h2 : (((3 ^ J : ℕ) : ℤ)) * (((3 ^ K : ℕ) : ℤ))
          ∣ (((3 ^ J : ℕ) : ℤ)) * M.eval (y : ℤ) := by
        rw [← h1, ← hMeval y]; exact hN
      exact (mul_dvd_mul_iff_left (by positivity : (((3 ^ J : ℕ) : ℤ)) ≠ 0)).1 h2
    have hroot : ∀ y ∈ capSet 3 e a b, ∃ θ : ℤ_[3], (M * M.derivative).aeval θ = 0 ∧
        ‖(((y : ℤ)) : ℤ_[3]) - θ‖ ≤ (3 : ℝ) ^ (-(E : ℤ)) := by
      intro y hy
      have hMKy := hmK y hy
      by_cases hM'0 : M.derivative.eval (y : ℤ) = 0
      · refine ⟨(((y : ℤ)) : ℤ_[3]), ?_, ?_⟩
        · rw [Polynomial.aeval_mul, cardHensel_aeval_natCast M.derivative y, hM'0, Int.cast_zero,
            mul_zero]
        · rw [sub_self, norm_zero]; exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
      · set ν := padicValNat 3 (M.derivative.eval (y : ℤ)).natAbs with hνdef
        have hdvdM' : ((3 ^ ν : ℕ) : ℤ) ∣ M.derivative.eval (y : ℤ) := by
          rw [← Int.dvd_natAbs]
          exact_mod_cast (show 3 ^ ν ∣ (M.derivative.eval (y : ℤ)).natAbs by
            rw [hνdef]; exact pow_padicValNat_dvd)
        by_cases hA : 2 * ν < K
        · obtain ⟨θ, hθ0, hθd⟩ := hensel_root_close_three (P := M) (y := y) (K := K) (ν := ν)
            hA hMKy hM'0 hνdef.symm
          refine ⟨θ, ?_, ?_⟩
          · rw [Polynomial.aeval_mul, hθ0, zero_mul]
          · refine hθd.trans ?_
            have hEK : E ≤ K - ν := by omega
            exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mpr
              (neg_le_neg (by exact_mod_cast hEK))
        · have hB : K ≤ 2 * ν := by omega
          have hν8 : 8 ≤ ν := by omega
          have hcontra : ¬ ((3 ^ 2 : ℕ) : ℤ) ∣ M.derivative.derivative.eval (y : ℤ) := by
            intro h3
            have h2M : ((3 ^ 2 : ℕ) : ℤ) ∣ M.eval (y : ℤ) :=
              dvd_trans (by exact_mod_cast (pow_dvd_pow 3 (by omega : 2 ≤ K))) hMKy
            have h2M' : ((3 ^ 2 : ℕ) : ℤ) ∣ M.derivative.eval (y : ℤ) :=
              dvd_trans (by exact_mod_cast (pow_dvd_pow 3 (by omega : 2 ≤ ν))) hdvdM'
            have heq2 : (((3 ^ (J + 2) : ℕ) : ℤ))
                = (((3 ^ J : ℕ) : ℤ)) * (((3 ^ 2 : ℕ) : ℤ)) := by
              rw [pow_add]
              push_cast
              ring
            have hN2 : ((3 ^ (J + 2) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) := by
              rw [hMeval y, heq2]
              exact mul_dvd_mul_left _ h2M
            have hN2' : ((3 ^ (J + 2) : ℕ) : ℤ) ∣ (critN a b).derivative.eval (y : ℤ) := by
              rw [hMdeval y, heq2]
              exact mul_dvd_mul_left _ h2M'
            have hN2'' : ((3 ^ (J + 2) : ℕ) : ℤ)
                ∣ (critN a b).derivative.derivative.eval (y : ℤ) := by
              rw [hMd2eval y, heq2]
              exact mul_dvd_mul_left _ h3
            have htv := critN_tripleVanish_content (p := 3) (k := J + 2) a b y
              (hunit y hy) hN2 hN2' hN2''
            rw [padicValNat_three_six] at htv
            have hsub : (J + 2) - 1 = J + 1 := by omega
            rw [hsub] at htv
            have hle : J + 1 ≤ padicValNat 3 (contAB a b) := (padicValNat_dvd_iff_le hcont0).1 htv
            rw [hJv] at hle
            omega
          have hM''0 : M.derivative.derivative.eval (y : ℤ) ≠ 0 := by
            intro h0; exact hcontra (by rw [h0]; exact dvd_zero _)
          set ν' := padicValNat 3 (M.derivative.derivative.eval (y : ℤ)).natAbs with hν'def
          have hν'le1 : ν' ≤ 1 := by
            by_contra hc
            push_neg at hc
            exact hcontra (by
              rw [← Int.dvd_natAbs]
              exact_mod_cast (dvd_trans (pow_dvd_pow 3 (by omega : 2 ≤ ν'))
                (by rw [hν'def]; exact pow_padicValNat_dvd)))
          have hdvdM'ν : ((3 ^ (ν - 1) : ℕ) : ℤ) ∣ M.derivative.eval (y : ℤ) :=
            dvd_trans (by exact_mod_cast (pow_dvd_pow 3 (by omega : ν - 1 ≤ ν))) hdvdM'
          have hcond : 2 * ν' < ν - 1 := by omega
          obtain ⟨θ, hθ0, hθd⟩ := hensel_root_close_three (P := M.derivative) (y := y)
            (K := ν - 1) (ν := ν') hcond hdvdM'ν hM''0 hν'def.symm
          refine ⟨θ, ?_, ?_⟩
          · rw [Polynomial.aeval_mul, hθ0, mul_zero]
          · refine hθd.trans ?_
            have hEν : E ≤ (ν - 1) - ν' := by omega
            exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mpr
              (neg_le_neg (by exact_mod_cast hEν))
    have hcard := card_root_close_le_three (Q := M * M.derivative) (mul_ne_zero hMne hM'ne)
      (S := capSet 3 e a b) (N := m) (E := E) hrange hroot
    have hqdeg : (((M * M.derivative).natDegree : ℕ) : ℝ) ≤ 8 := by
      have h1 : (M * M.derivative).natDegree = M.natDegree + M.derivative.natDegree :=
        Polynomial.natDegree_mul hMne hM'ne
      have h2 : M.derivative.natDegree ≤ M.natDegree - 1 := Polynomial.natDegree_derivative_le M
      have h3 : M.natDegree ≤ 4 := by rw [hMdeg]; exact hdeg
      have h4 : (M * M.derivative).natDegree ≤ 8 := by omega
      exact_mod_cast h4
    have hcardR : ((capSet 3 e a b).card : ℝ) ≤ 8 * (3 : ℝ) ^ (m - E) := by
      calc ((capSet 3 e a b).card : ℝ)
          ≤ (((M * M.derivative).natDegree : ℕ) : ℝ) * (3 : ℝ) ^ (m - E) := hcard
        _ ≤ 8 * (3 : ℝ) ^ (m - E) :=
            mul_le_mul_of_nonneg_right hqdeg (by positivity)
    have hexp : m - E ≤ m - (m + T - J - 1) / 2 + 2 := by omega
    have hnum : 8 * (3 : ℝ) ^ (m - E) ≤ 1000 * (3 : ℝ) ^ (m - (m + T - J - 1) / 2) := by
      have h1 : (3 : ℝ) ^ (m - E) ≤ (3 : ℝ) ^ (m - (m + T - J - 1) / 2 + 2) :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hexp
      have h2 : (3 : ℝ) ^ (m - (m + T - J - 1) / 2 + 2)
          = (3 : ℝ) ^ (m - (m + T - J - 1) / 2) * 9 := by
        rw [pow_add]; norm_num
      have h3 : 8 * (3 : ℝ) ^ (m - E)
          ≤ 8 * ((3 : ℝ) ^ (m - (m + T - J - 1) / 2) * 9) := by
        rw [h2] at h1
        exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      calc 8 * (3 : ℝ) ^ (m - E)
          ≤ 8 * ((3 : ℝ) ^ (m - (m + T - J - 1) / 2) * 9) := h3
        _ = 72 * (3 : ℝ) ^ (m - (m + T - J - 1) / 2) := by ring
        _ ≤ 1000 * (3 : ℝ) ^ (m - (m + T - J - 1) / 2) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    have hgoalR : ((capSet 3 e a b).card : ℝ)
        ≤ ((10 ^ 3 * 3 ^ max 0 (m - (m + T - J - 1) / 2) : ℕ) : ℝ) := by
      rw [show max 0 (m - (m + T - J - 1) / 2) = m - (m + T - J - 1) / 2 from
        max_eq_right (Nat.zero_le _)]
      have hconv : (((10 ^ 3 * 3 ^ (m - (m + T - J - 1) / 2) : ℕ)) : ℝ)
          = 1000 * (3 : ℝ) ^ (m - (m + T - J - 1) / 2) := by
        push_cast
        norm_num
      rw [hconv]
      exact le_trans hcardR hnum
    exact_mod_cast hgoalR
  · -- the trivial branch
    have hK13 : m + T - J - 1 ≤ 13 := by omega
    have hK'le : (m + T - J - 1) / 2 ≤ m := by
      have hdiv := Nat.div_add_mod (m + T - J - 1) 2
      have hmod := Nat.mod_lt (m + T - J - 1) (by norm_num : 0 < 2)
      omega
    have hdec : (m + T - J - 1) / 2 + (m - (m + T - J - 1) / 2) = m := by
      rw [Nat.add_comm]
      exact Nat.sub_add_cancel hK'le
    have hcardS : (capSet 3 e a b).card ≤ 3 ^ m := by
      have hsub : capSet 3 e a b ⊆ Finset.range (3 ^ m) := fun y hy =>
        Finset.mem_range.mpr (hrange y hy)
      calc (capSet 3 e a b).card ≤ (Finset.range (3 ^ m)).card := Finset.card_le_card hsub
        _ = 3 ^ m := Finset.card_range _
    have hexp6 : (m + T - J - 1) / 2 ≤ 6 := by
      have := Nat.div_add_mod (m + T - J - 1) 2
      have hmod := Nat.mod_lt (m + T - J - 1) (by norm_num : 0 < 2)
      omega
    have hgoal : (capSet 3 e a b).card
        ≤ 10 ^ 3 * 3 ^ max 0 (m - (m + T - J - 1) / 2) := by
      rw [max_eq_right (Nat.zero_le _)]
      calc (capSet 3 e a b).card ≤ 3 ^ m := hcardS
        _ = 3 ^ ((m + T - J - 1) / 2) * 3 ^ (m - (m + T - J - 1) / 2) := by
            rw [← pow_add, hdec]
        _ ≤ 3 ^ 6 * 3 ^ (m - (m + T - J - 1) / 2) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hexp6)
        _ ≤ 10 ^ 3 * 3 ^ (m - (m + T - J - 1) / 2) :=
            Nat.mul_le_mul_right _ (by norm_num)
    exact hgoal

end Work.LinnikBurgess.lfSmall
