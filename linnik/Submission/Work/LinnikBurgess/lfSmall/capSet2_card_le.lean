import Mathlib
import Submission.Work.LinnikBurgess.lfSmall.two_defs
import Submission.Work.LinnikBurgess.natDegree_critN_le_four
import Submission.Work.LinnikBurgess.critN_tripleVanish_content
import Submission.Work.LinnikBurgess.critN_ne_zero_of_unique
import Submission.Work.LinnikBurgess.card_hensel_le

open Polynomial

namespace Work.LinnikBurgess.lfSmall

private lemma cubeLevel_two_eq (e : ℕ) : cubeLevel 2 e = (e + 3) / 3 := by simp [cubeLevel]

private lemma capLevel_two_eq (e : ℕ) : capLevel 2 e = e - 2 * ((e + 3) / 3) := by
  rw [capLevel, cubeLevel_two_eq]

private lemma capLevel_two_add_one_le_cubeLevel (e : ℕ) : capLevel 2 e + 1 ≤ cubeLevel 2 e := by
  have h := Nat.div_add_mod (e + 3) 3
  have h' : (e + 3) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  simp only [capLevel_two_eq, cubeLevel_two_eq]
  omega

private lemma aeval_natCast_two (P : Polynomial ℤ) (y : ℕ) :
    P.aeval (((y : ℤ)) : ℤ_[2]) = ((P.eval ((y : ℤ)) : ℤ) : ℤ_[2]) :=
  cardHensel_aeval_natCast P y

private lemma two_pow_dvd_two_pow {a b : ℕ} (h : a ≤ b) :
    ((2 ^ a : ℕ) : ℤ) ∣ ((2 ^ b : ℕ) : ℤ) := by
  exact_mod_cast (pow_dvd_pow 2 h : (2 : ℕ) ^ a ∣ 2 ^ b)

private lemma padicValNat_two_six : padicValNat 2 6 = 1 := by
  have hne6 : (6 : ℕ) ≠ 0 := by norm_num
  refine le_antisymm ?_ ((padicValNat_dvd_iff_le hne6).1 (by norm_num))
  by_contra hc
  push_neg at hc
  have hd : 2 ^ 2 ∣ (6 : ℕ) :=
    dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ padicValNat 2 6)) pow_padicValNat_dvd
  norm_num at hd

/-- The trivial branch of the cap-set count: if `J` is so large that `K = m + T - 1 - J ≤ 27`,
the crude bound `card ≤ 2^m` already suffices. -/
private lemma triv_numeric (m T J : ℕ) (hmT : 2 ≤ m + T) (h : ¬ (J + 28 ≤ m + T - 1)) :
    ((2 ^ m : ℕ) : ℝ) ≤ (10 : ℝ) ^ 4
      * (2 : ℝ) ^ (((m : ℝ) - (T : ℝ) + 2 + (J : ℝ)) / 2) := by
  have h1 : m + T - 2 ≤ J + 26 := by omega
  have h2 : (m : ℝ) + (T : ℝ) - 2 - (J : ℝ) ≤ 26 := by
    have h3 : ((m + T - 2 : ℕ) : ℝ) ≤ ((J + 26 : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_sub hmT] at h3
    push_cast at h3
    linarith
  have hY : (m : ℝ) ≤ ((m : ℝ) - (T : ℝ) + 2 + (J : ℝ)) / 2 + ((13 : ℕ) : ℝ) := by linarith
  have h213 : (2 : ℝ) ^ ((13 : ℕ) : ℝ) = 8192 := by
    rw [Real.rpow_natCast]; norm_num
  calc ((2 ^ m : ℕ) : ℝ)
      = (2 : ℝ) ^ ((m : ℕ) : ℝ) := by push_cast; rw [Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ (((m : ℝ) - (T : ℝ) + 2 + (J : ℝ)) / 2 + ((13 : ℕ) : ℝ)) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hY
    _ = (2 : ℝ) ^ (((m : ℝ) - (T : ℝ) + 2 + (J : ℝ)) / 2) * (2 : ℝ) ^ ((13 : ℕ) : ℝ) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = (2 : ℝ) ^ (((m : ℝ) - (T : ℝ) + 2 + (J : ℝ)) / 2) * 8192 := by rw [h213]
    _ ≤ (2 : ℝ) ^ (((m : ℝ) - (T : ℝ) + 2 + (J : ℝ)) / 2) * (10 : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_left (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    _ = (10 : ℝ) ^ 4 * (2 : ℝ) ^ (((m : ℝ) - (T : ℝ) + 2 + (J : ℝ)) / 2) := by ring

/-- The fine branch of the cap-set count: with `K = m + T - 1 - J ≥ 28` and the Hensel modulus
`E = K / 2 - 2`, a set of `8 · 2 ^ (m - E)` points is still below the target bound. -/
private lemma fine_numeric (m T J K E : ℕ) (hK : K = m + T - 1 - J) (hK28 : 28 ≤ K)
    (hTm : T ≤ m) (hE : E = K / 2 - 2) :
    8 * (2 : ℝ) ^ (m - E) ≤ (10 : ℝ) ^ 4
      * (2 : ℝ) ^ (((m : ℝ) - (T : ℝ) + 2 + (J : ℝ)) / 2) := by
  have hJle : J ≤ m + T - 1 := by omega
  have hmT1 : 1 ≤ m + T := by omega
  have hKc : (K : ℝ) = (m : ℝ) + (T : ℝ) - 1 - (J : ℝ) := by
    rw [hK, Nat.cast_sub hJle, Nat.cast_sub hmT1]
    push_cast
    ring
  have hKdec : (K : ℝ) = 2 * ((K / 2 : ℕ) : ℝ) + ((K % 2 : ℕ) : ℝ) := by
    have hA : ((2 * (K / 2) + K % 2 : ℕ) : ℝ)
        = 2 * ((K / 2 : ℕ) : ℝ) + ((K % 2 : ℕ) : ℝ) := by push_cast; ring
    have h := Nat.div_add_mod K 2
    rw [h] at hA
    exact hA
  have hKmod : ((K % 2 : ℕ) : ℝ) ≤ 1 := by
    have hlt : K % 2 ≤ 1 := by have := Nat.mod_lt K (by norm_num : 0 < 2); omega
    exact_mod_cast hlt
  have hEm : E ≤ m := by rw [hE]; omega
  have hEcast : (E : ℝ) = ((K / 2 : ℕ) : ℝ) - 2 := by
    rw [hE, Nat.cast_sub (by omega : 2 ≤ K / 2)]
    norm_num
  have hYeq : ((m : ℝ) - (T : ℝ) + 2 + (J : ℝ)) / 2 = (m : ℝ) - (K : ℝ) / 2 + 1 / 2 := by
    rw [hKc]; ring
  have hstep : ((m : ℝ) - (E : ℝ)) ≤ ((m : ℝ) - (K : ℝ) / 2 + 1 / 2) + ((10 : ℕ) : ℝ) := by
    rw [hEcast]; linarith
  have h2ten : (2 : ℝ) ^ ((10 : ℕ) : ℝ) = 1024 := by
    rw [Real.rpow_natCast]; norm_num
  calc 8 * (2 : ℝ) ^ (m - E)
      = 8 * (2 : ℝ) ^ ((m : ℝ) - (E : ℝ)) := by
          rw [← Nat.cast_sub hEm, Real.rpow_natCast]
    _ ≤ 8 * (2 : ℝ) ^ (((m : ℝ) - (K : ℝ) / 2 + 1 / 2) + ((10 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left
          ((Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hstep) (by norm_num)
    _ = 8 * ((2 : ℝ) ^ (((m : ℝ) - (K : ℝ) / 2 + 1 / 2)) * (2 : ℝ) ^ ((10 : ℕ) : ℝ)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ = 8192 * (2 : ℝ) ^ (((m : ℝ) - (K : ℝ) / 2 + 1 / 2)) := by rw [h2ten]; ring
    _ ≤ (10 : ℝ) ^ 4 * (2 : ℝ) ^ (((m : ℝ) - (K : ℝ) / 2 + 1 / 2)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    _ = (10 : ℝ) ^ 4 * (2 : ℝ) ^ (((m : ℝ) - (T : ℝ) + 2 + (J : ℝ)) / 2) := by rw [hYeq]

/-- If every coefficient of `N : ℤ[X]` is divisible by `2 ^ J`, then `N = C (2 ^ J) * M` for some
integral polynomial `M` with `natDegree M ≤ natDegree N`. -/
private lemma exists_eq_C_mul_two_pow (N : Polynomial ℤ) (J : ℕ)
    (h : ∀ n, ((2 ^ J : ℕ) : ℤ) ∣ N.coeff n) :
    ∃ M : Polynomial ℤ, N = Polynomial.C (((2 ^ J : ℕ) : ℤ)) * M ∧
      M.natDegree ≤ N.natDegree := by
  obtain ⟨M, hM⟩ := (Polynomial.C_dvd_iff_dvd_coeff (((2 ^ J : ℕ) : ℤ)) N).mpr h
  exact ⟨M, hM, by rw [hM, Polynomial.natDegree_C_mul (by positivity)]⟩

/-- **Hensel step.**  If `2 ^ ν` is the exact power of `2` dividing `P'(y)` and `2 ^ K ∣ P(y)` with
`2 * ν < K`, then `P` has a root `θ` in `ℤ_[2]` with `‖y - θ‖ ≤ 2 ^ (-(K - ν))`. -/
private lemma hensel_root_close_two {P : Polynomial ℤ} {y K ν : ℕ}
    (hKν : 2 * ν < K) (hK : ((2 ^ K : ℕ) : ℤ) ∣ P.eval ((y : ℤ)))
    (hne : P.derivative.eval ((y : ℤ)) ≠ 0)
    (hν : padicValNat 2 (P.derivative.eval ((y : ℤ))).natAbs = ν) :
    ∃ θ : ℤ_[2], P.aeval θ = 0 ∧
      ‖(((y : ℤ)) : ℤ_[2]) - θ‖ ≤ (2 : ℝ) ^ (-((K - ν : ℕ) : ℤ)) := by
  classical
  have hne' : (P.derivative.eval ((y : ℤ))).natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using hne
  have h1 : ((2 ^ ν : ℕ) : ℤ) ∣ P.derivative.eval ((y : ℤ)) := by
    rw [← Int.dvd_natAbs]
    exact_mod_cast (show 2 ^ ν ∣ (P.derivative.eval ((y : ℤ))).natAbs by
      rw [← hν]; exact pow_padicValNat_dvd)
  have h2 : ¬ ((2 ^ (ν + 1) : ℕ) : ℤ) ∣ P.derivative.eval ((y : ℤ)) := by
    intro hc
    have hnat : 2 ^ (ν + 1) ∣ (P.derivative.eval ((y : ℤ))).natAbs := by
      have hh := (Int.natAbs_dvd_natAbs (a := ((2 ^ (ν + 1) : ℕ) : ℤ))
        (b := P.derivative.eval ((y : ℤ)))).mpr hc
      simpa using hh
    have hle := (padicValNat_dvd_iff_le hne').1 hnat
    rw [hν] at hle
    omega
  have hnormW : ‖P.aeval (((y : ℤ)) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(K : ℤ)) :=
    cardHensel_norm_aeval_le_of_dvd (p := 2) (P := P) (y := y) (k := K) hK
  have hnormD : ‖P.derivative.aeval (((y : ℤ)) : ℤ_[2])‖ = (2 : ℝ) ^ (-(ν : ℤ)) :=
    cardHensel_norm_aeval_deriv_eq_of_padic (p := 2) (P := P) (y := y) (ν := ν) h1 h2
  have hlt : ‖P.aeval (((y : ℤ)) : ℤ_[2])‖
      < ‖P.derivative.aeval (((y : ℤ)) : ℤ_[2])‖ ^ 2 := by
    rw [hnormD]
    have hsq : ((2 : ℝ) ^ (-(ν : ℤ))) ^ 2 = (2 : ℝ) ^ (-((2 * ν : ℕ) : ℤ)) := by
      rw [sq, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1; push_cast; ring
    rw [hsq]
    exact lt_of_le_of_lt hnormW
      ((zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).2 (by push_cast; omega))
  obtain ⟨θ, hθ0, hθlt, hθD, -⟩ := hensels_lemma hlt
  refine ⟨θ, hθ0, ?_⟩
  have hlt' : ‖(((y : ℤ)) : ℤ_[2]) - θ‖ < ‖P.derivative.aeval θ‖ := by
    rw [norm_sub_rev, hθD]
    exact hθlt
  have hprod := aeval_dist_eq_norm P hθ0 hlt'
  rw [hθD, hnormD] at hprod
  have hle : ‖(((y : ℤ)) : ℤ_[2]) - θ‖ * (2 : ℝ) ^ (-(ν : ℤ)) ≤ (2 : ℝ) ^ (-(K : ℤ)) := by
    rw [hprod]; exact hnormW
  have hmul : (2 : ℝ) ^ (-((K - ν : ℕ) : ℤ)) * (2 : ℝ) ^ (-(ν : ℤ)) = (2 : ℝ) ^ (-(K : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    push_cast
    omega
  rw [← hmul] at hle
  exact (mul_le_mul_iff_of_pos_right (zpow_pos (by norm_num : (0 : ℝ) < 2) _)).1 hle

/-- Two naturals with the same quotient by `2 ^ E` whose difference is a multiple of `2 ^ E` agree. -/
private lemma eq_of_div_eq_div_of_dvd_sub {E u v : ℕ}
    (hdvd : ((2 ^ E : ℕ) : ℤ) ∣ (u : ℤ) - (v : ℤ)) (hq : u / 2 ^ E = v / 2 ^ E) : u = v := by
  have hsym : ((2 ^ E : ℕ) : ℤ) ∣ (v : ℤ) - (u : ℤ) := by
    have he : ((v : ℤ) - (u : ℤ)) = -(((u : ℤ) - (v : ℤ))) := by ring
    rw [he]; exact dvd_neg.mpr hdvd
  have hmod : u % 2 ^ E = v % 2 ^ E := Nat.modEq_iff_dvd.mpr hsym
  have h1 := Nat.div_add_mod u (2 ^ E)
  have h2 := Nat.div_add_mod v (2 ^ E)
  rw [hq, hmod] at h1
  exact h1.symm.trans h2

/-- If every element of `S ⊆ {0, …, 2^N - 1}` lies within `2 ^ (-E)` of a root in `ℤ_[2]` of a
nonzero integral polynomial `Q`, then `card S ≤ natDegree Q * 2 ^ (N - E)`. -/
private lemma card_root_close_le {Q : Polynomial ℤ} (hQ : Q ≠ 0) {N E : ℕ} (S : Finset ℕ)
    (hrange : ∀ y ∈ S, y < 2 ^ N)
    (hroot : ∀ y ∈ S, ∃ θ : ℤ_[2], Q.aeval θ = 0 ∧
      ‖(((y : ℤ)) : ℤ_[2]) - θ‖ ≤ (2 : ℝ) ^ (-(E : ℤ))) :
    (S.card : ℝ) ≤ (Q.natDegree : ℝ) * (2 : ℝ) ^ (N - E) := by
  classical
  let f : ℕ → ℤ_[2] := fun y => if h : ∃ θ : ℤ_[2], Q.aeval θ = 0 ∧
      ‖(((y : ℤ)) : ℤ_[2]) - θ‖ ≤ (2 : ℝ) ^ (-(E : ℤ))
    then Classical.choose h else 0
  have hf : ∀ y (hy : y ∈ S), Q.aeval (f y) = 0 ∧
      ‖(((y : ℤ)) : ℤ_[2]) - f y‖ ≤ (2 : ℝ) ^ (-(E : ℤ)) := by
    intro y hy
    have hh := hroot y hy
    have hfy : f y = Classical.choose hh := by
      show (if h : ∃ θ : ℤ_[2], Q.aeval θ = 0 ∧
        ‖(((y : ℤ)) : ℤ_[2]) - θ‖ ≤ (2 : ℝ) ^ (-(E : ℤ))
        then Classical.choose h else 0) = Classical.choose hh
      exact dif_pos hh
    rw [hfy]
    exact Classical.choose_spec hh
  have hQmap : Q.map (algebraMap ℤ ℤ_[2]) ≠ 0 := by
    intro h
    exact hQ ((Polynomial.map_eq_zero_iff (f := algebraMap ℤ ℤ_[2])
      (fun x y hxy => (PadicInt.intCast_eq x y).1 hxy)).1 h)
  have hmaps : ∀ y ∈ S, f y ∈ (Q.map (algebraMap ℤ ℤ_[2])).roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    refine ⟨hQmap, ?_⟩
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact (hf y hy).1
  have hquot : ∀ y ∈ S, y / 2 ^ E < 2 ^ (N - E) := by
    intro y hy
    have hyN := hrange y hy
    rcases le_or_gt E N with hEN | hEN
    · rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ E)]
      rw [← pow_add, Nat.sub_add_cancel hEN]
      exact hyN
    · have hpow : 2 ^ N ≤ 2 ^ E :=
        Nat.le_of_dvd (by positivity) (pow_dvd_pow 2 (by omega))
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hyN hpow)]
      exact pow_pos (by norm_num) _
  have hinj : Set.InjOn (fun y => (f y, y / 2 ^ E)) ↑S := by
    intro y₁ h₁ y₂ h₂ heq
    have hf12 : f y₁ = f y₂ := congrArg Prod.fst heq
    have hq12 : y₁ / 2 ^ E = y₂ / 2 ^ E := congrArg Prod.snd heq
    have hd1 := (hf y₁ h₁).2
    have hd2 := (hf y₂ h₂).2
    have hdist : ‖(((y₁ : ℤ)) : ℤ_[2]) - (((y₂ : ℤ)) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(E : ℤ)) := by
      have hz : (((y₁ : ℤ)) : ℤ_[2]) - (((y₂ : ℤ)) : ℤ_[2])
          = ((((y₁ : ℤ)) : ℤ_[2]) - f y₁) + (f y₁ - (((y₂ : ℤ)) : ℤ_[2])) := by ring
      rw [hz]
      refine (PadicInt.nonarchimedean _ _).trans (max_le hd1 ?_)
      rw [hf12, norm_sub_rev]
      exact hd2
    have hdvd : ((2 ^ E : ℕ) : ℤ) ∣ ((y₁ : ℤ) - (y₂ : ℤ)) := by
      have hcast : (((y₁ : ℤ) - (y₂ : ℤ) : ℤ) : ℤ_[2])
          = (((y₁ : ℤ)) : ℤ_[2]) - (((y₂ : ℤ)) : ℤ_[2]) := by push_cast; ring
      exact (PadicInt.norm_int_le_pow_iff_dvd).1 (by rw [hcast]; exact hdist)
    exact eq_of_div_eq_div_of_dvd_sub hdvd hq12
  have hsub : S.image (fun y => (f y, y / 2 ^ E))
      ⊆ (Q.map (algebraMap ℤ ℤ_[2])).roots.toFinset ×ˢ Finset.range (2 ^ (N - E)) := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨hmaps y hy, Finset.mem_range.mpr (hquot y hy)⟩
  have hrcard : ((Q.map (algebraMap ℤ ℤ_[2])).roots.toFinset.card : ℝ) ≤ Q.natDegree := by
    have h1 : (Q.map (algebraMap ℤ ℤ_[2])).roots.toFinset.card
        ≤ (Q.map (algebraMap ℤ ℤ_[2])).natDegree :=
      le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)
    have h2 : (Q.map (algebraMap ℤ ℤ_[2])).natDegree ≤ Q.natDegree :=
      Polynomial.natDegree_map_le
    exact_mod_cast le_trans h1 h2
  calc (S.card : ℝ) = ((S.image (fun y => (f y, y / 2 ^ E))).card : ℝ) := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ (((Q.map (algebraMap ℤ ℤ_[2])).roots.toFinset
          ×ˢ Finset.range (2 ^ (N - E))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ((Q.map (algebraMap ℤ ℤ_[2])).roots.toFinset.card : ℝ) * (2 : ℝ) ^ (N - E) := by
        rw [Finset.card_product, Finset.card_range, Nat.cast_mul, Nat.cast_pow]
        norm_num
    _ ≤ (Q.natDegree : ℝ) * (2 : ℝ) ^ (N - E) :=
        mul_le_mul_of_nonneg_right hrcard (by positivity)

theorem capSet2_card_le {e J : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hJc : padicValNat 2 (contAB a b) = J)
    (hJ : ∀ n, ((2 ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) :
    ((capSet2 e a b).card : ℝ) ≤ (10 : ℝ) ^ 4
      * (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) - (capLevel 2 e : ℝ) + 2 + (J : ℝ)) / 2) := by
  classical
  obtain ⟨hdeg2, hcontABne⟩ := critN_ne_zero_of_unique a b i hi
  have hdeg4 : (critN a b).natDegree ≤ 4 := natDegree_critN_le_four a b
  have hNne : critN a b ≠ 0 := by
    intro h; rw [h] at hdeg2; simp at hdeg2
  have hm5 : 5 ≤ cubeLevel 2 e := by rw [cubeLevel_two_eq]; omega
  by_cases hfine : J + 28 ≤ cubeLevel 2 e + capLevel 2 e - 1
  · -- ===== fine branch =====
    set m : ℕ := cubeLevel 2 e with hm
    set T : ℕ := capLevel 2 e with hT
    set K : ℕ := m + T - 1 - J with hK
    have hK28 : 28 ≤ K := by rw [hK]; omega
    have hJle : J ≤ m + T - 1 := by omega
    have hTm : T ≤ m := by
      rw [hT, hm]
      have := capLevel_two_add_one_le_cubeLevel e
      omega
    set E : ℕ := K / 2 - 2 with hE
    obtain ⟨M, hNM, hMdeg⟩ := exists_eq_C_mul_two_pow (critN a b) J hJ
    have hMne : M ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hNM; exact hNne hNM
    have hMnat : M.natDegree = (critN a b).natDegree := by
      rw [hNM, Polynomial.natDegree_C_mul (by positivity : (((2 ^ J : ℕ) : ℤ)) ≠ 0)]
    have hMdeg4 : M.natDegree ≤ 4 := hMnat.trans_le hdeg4
    have hM'ne : M.derivative ≠ 0 := by
      rw [Polynomial.derivative_ne_zero, hMnat]; omega
    have hMeval : ∀ y : ℕ, (critN a b).eval ((y : ℤ))
        = (((2 ^ J : ℕ) : ℤ)) * M.eval ((y : ℤ)) := by
      intro y; rw [hNM, Polynomial.eval_mul, Polynomial.eval_C]
    have hNMd : (critN a b).derivative
        = Polynomial.C (((2 ^ J : ℕ) : ℤ)) * M.derivative := by
      rw [hNM, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
    have hM'neval : ∀ y : ℕ, (critN a b).derivative.eval ((y : ℤ))
        = (((2 ^ J : ℕ) : ℤ)) * M.derivative.eval ((y : ℤ)) := by
      intro y; rw [hNMd, Polynomial.eval_mul, Polynomial.eval_C]
    have hNMdd : (critN a b).derivative.derivative
        = Polynomial.C (((2 ^ J : ℕ) : ℤ)) * M.derivative.derivative := by
      rw [hNMd, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
    have hM''neval : ∀ y : ℕ, (critN a b).derivative.derivative.eval ((y : ℤ))
        = (((2 ^ J : ℕ) : ℤ)) * M.derivative.derivative.eval ((y : ℤ)) := by
      intro y; rw [hNMdd, Polynomial.eval_mul, Polynomial.eval_C]
    have hroot : ∀ y ∈ capSet2 e a b, ∃ θ : ℤ_[2], (M * M.derivative).aeval θ = 0 ∧
        ‖(((y : ℤ)) : ℤ_[2]) - θ‖ ≤ (2 : ℝ) ^ (-(E : ℤ)) := by
      intro y hy
      rw [capSet2, Finset.mem_filter] at hy
      obtain ⟨hyr, hyunit, hyL, hyT⟩ := hy
      have hLvl : Lvl e = J + K := by
        rw [Lvl, ← hm, ← hT, hK]; omega
      have hMK : ((2 ^ K : ℕ) : ℤ) ∣ M.eval ((y : ℤ)) := by
        have h2 : (((2 ^ (J + K) : ℕ) : ℤ))
            = (((2 ^ J : ℕ) : ℤ)) * (((2 ^ K : ℕ) : ℤ)) := by
          rw [pow_add, Nat.cast_mul]
        have h3 : (((2 ^ J : ℕ) : ℤ)) * (((2 ^ K : ℕ) : ℤ))
            ∣ (((2 ^ J : ℕ) : ℤ)) * M.eval ((y : ℤ)) := by
          rw [← h2, ← hLvl, ← hMeval y]
          exact hyL
        exact (mul_dvd_mul_iff_left (by positivity : (((2 ^ J : ℕ) : ℤ)) ≠ 0)).1 h3
      by_cases hM'0 : M.derivative.eval ((y : ℤ)) = 0
      · refine ⟨(((y : ℤ)) : ℤ_[2]), ?_, ?_⟩
        · rw [Polynomial.aeval_mul, aeval_natCast_two M.derivative y, hM'0, Int.cast_zero,
            mul_zero]
        · rw [sub_self, norm_zero]
          exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
      · set ν : ℕ := padicValNat 2 (M.derivative.eval ((y : ℤ))).natAbs with hν
        have hdvdM' : (((2 ^ ν : ℕ) : ℤ)) ∣ M.derivative.eval ((y : ℤ)) := by
          rw [← Int.dvd_natAbs]
          exact_mod_cast (show 2 ^ ν ∣ (M.derivative.eval ((y : ℤ))).natAbs by
            rw [hν]; exact pow_padicValNat_dvd)
        by_cases hA : 2 * ν < K
        · obtain ⟨θ, hθ0, hθd⟩ := hensel_root_close_two (P := M) (y := y)
            (K := K) (ν := ν) hA hMK hM'0 hν.symm
          refine ⟨θ, ?_, ?_⟩
          · rw [Polynomial.aeval_mul, hθ0, zero_mul]
          · refine hθd.trans ?_
            have hEK : E ≤ K - ν := by rw [hE]; omega
            exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr
              (neg_le_neg (by exact_mod_cast hEK))
        · have hB : K ≤ 2 * ν := by omega
          have hν14 : 14 ≤ ν := by omega
          have hLvl2 : J + 2 ≤ Lvl e := by rw [hLvl]; omega
          have h2JN : (((2 ^ (J + 2) : ℕ) : ℤ)) ∣ (critN a b).eval ((y : ℤ)) :=
            dvd_trans (two_pow_dvd_two_pow hLvl2) hyL
          have h2JN' : (((2 ^ (J + 2) : ℕ) : ℤ)) ∣ (critN a b).derivative.eval ((y : ℤ)) := by
            rw [hM'neval y]
            have h1 : (((2 ^ (J + ν) : ℕ) : ℤ))
                ∣ (((2 ^ J : ℕ) : ℤ)) * M.derivative.eval ((y : ℤ)) := by
              rw [pow_add, Nat.cast_mul]
              exact mul_dvd_mul_left _ hdvdM'
            exact dvd_trans (two_pow_dvd_two_pow (by omega : J + 2 ≤ J + ν)) h1
          have hcontra : ¬ (((2 ^ (J + 2) : ℕ) : ℤ))
              ∣ (critN a b).derivative.derivative.eval ((y : ℤ)) := by
            intro h3
            have htv := critN_tripleVanish_content (p := 2) (k := J + 2) a b y hyunit
              h2JN h2JN' h3
            rw [padicValNat_two_six] at htv
            have hsub : (J + 2) - 1 = J + 1 := by omega
            rw [hsub] at htv
            have hle : J + 1 ≤ padicValNat 2 (contAB a b) :=
              (padicValNat_dvd_iff_le hcontABne).1 htv
            rw [hJc] at hle
            omega
          have hM''not : ¬ (((2 ^ 2 : ℕ) : ℤ)) ∣ M.derivative.derivative.eval ((y : ℤ)) := by
            intro hd
            apply hcontra
            rw [hM''neval y,
              show (((2 ^ (J + 2) : ℕ) : ℤ)) = (((2 ^ J : ℕ) : ℤ)) * (((2 ^ 2 : ℕ) : ℤ)) by
                rw [pow_add, Nat.cast_mul]]
            exact mul_dvd_mul_left _ hd
          have hM''0 : M.derivative.derivative.eval ((y : ℤ)) ≠ 0 := by
            intro h0; exact hM''not (by rw [h0]; exact dvd_zero _)
          set ν' : ℕ := padicValNat 2 (M.derivative.derivative.eval ((y : ℤ))).natAbs with hν'
          have hν'le1 : ν' ≤ 1 := by
            by_contra hc
            push_neg at hc
            apply hM''not
            rw [← Int.dvd_natAbs]
            exact_mod_cast (show 2 ^ 2 ∣ (M.derivative.derivative.eval ((y : ℤ))).natAbs by
              refine dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ ν')) ?_
              rw [hν']; exact pow_padicValNat_dvd)
          have hdvdM'ν : (((2 ^ (ν - 1) : ℕ) : ℤ)) ∣ M.derivative.eval ((y : ℤ)) :=
            dvd_trans (two_pow_dvd_two_pow (by omega : ν - 1 ≤ ν)) hdvdM'
          have hcond : 2 * ν' < ν - 1 := by omega
          obtain ⟨θ, hθ0, hθd⟩ := hensel_root_close_two (P := M.derivative) (y := y)
            (K := ν - 1) (ν := ν') hcond hdvdM'ν hM''0 hν'.symm
          refine ⟨θ, ?_, ?_⟩
          · rw [Polynomial.aeval_mul, hθ0, mul_zero]
          · refine hθd.trans ?_
            have hEν : E ≤ (ν - 1) - ν' := by rw [hE]; omega
            exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr
              (neg_le_neg (by exact_mod_cast hEν))
    have hQne : M * M.derivative ≠ 0 := mul_ne_zero hMne hM'ne
    have hcard := card_root_close_le (Q := M * M.derivative) hQne (S := capSet2 e a b)
      (N := m) (E := E)
      (fun y hy => by
        rw [capSet2, Finset.mem_filter, Finset.mem_range] at hy
        rw [hm]
        exact hy.1)
      hroot
    have hQdeg : (M * M.derivative).natDegree ≤ 8 := by
      rw [Polynomial.natDegree_mul hMne hM'ne]
      have hd := Polynomial.natDegree_derivative_le M
      omega
    have h8 : (((M * M.derivative).natDegree : ℕ) : ℝ) ≤ 8 := by exact_mod_cast hQdeg
    refine hcard.trans ?_
    have h2 : (((M * M.derivative).natDegree : ℕ) : ℝ) * (2 : ℝ) ^ (m - E)
        ≤ 8 * (2 : ℝ) ^ (m - E) :=
      mul_le_mul_of_nonneg_right h8 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    exact h2.trans (fine_numeric m T J K E hK hK28 hTm hE)
  · -- ===== trivial branch =====
    have hcardle : (capSet2 e a b).card ≤ 2 ^ cubeLevel 2 e := by
      rw [capSet2]
      exact le_trans (Finset.card_le_card (Finset.filter_subset _ _))
        (le_of_eq (Finset.card_range _))
    refine (Nat.cast_le.mpr hcardle).trans ?_
    refine triv_numeric (cubeLevel 2 e) (capLevel 2 e) J ?_ hfine
    have := capLevel_two_add_one_le_cubeLevel e
    omega

end Work.LinnikBurgess.lfSmall
