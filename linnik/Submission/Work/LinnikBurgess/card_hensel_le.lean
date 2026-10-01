import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.aeval_dist_eq_norm
import Submission.Work.LinnikBurgess.eq_of_dvd_sub_of_lt

open Polynomial
open scoped BigOperators

namespace Work.LinnikBurgess

lemma cardHensel_aeval_natCast {p : ℕ} [Fact p.Prime] (P : Polynomial ℤ) (y : ℕ) :
    P.aeval (((y : ℤ)) : ℤ_[p]) = ((P.eval ((y : ℤ)) : ℤ) : ℤ_[p]) := by
  rw [Polynomial.aeval_def]
  rw [show (algebraMap ℤ ℤ_[p]) = Int.castRingHom ℤ_[p] from rfl]
  rw [show (((y : ℤ) : ℤ_[p])) = (Int.castRingHom ℤ_[p]) (y : ℤ) from rfl]
  rw [Polynomial.eval₂_at_apply]
  rfl

lemma cardHensel_valuation_of_padic {p : ℕ} [Fact p.Prime] {d : ℤ} {ν : ℕ}
    (h1 : ((p ^ ν : ℕ) : ℤ) ∣ d) (h2 : ¬ ((p ^ (ν + 1) : ℕ) : ℤ) ∣ d) :
    ((d : ℤ_[p])).valuation = ν := by
  have hd0 : d ≠ 0 := fun h => h2 (h ▸ dvd_zero _)
  have hne : ((d : ℤ_[p])) ≠ 0 := fun h => hd0 ((PadicInt.intCast_eq d 0).1 h)
  have h1' : ν ≤ ((d : ℤ_[p])).valuation :=
    (PadicInt.norm_le_pow_iff_le_valuation _ hne ν).1
      ((PadicInt.norm_int_le_pow_iff_dvd).2 (by simpa [Nat.cast_pow] using h1))
  have h2' : ((d : ℤ_[p])).valuation ≤ ν := by
    by_contra h
    push Not at h
    have h3 : ‖((d : ℤ_[p]))‖ ≤ (p : ℝ) ^ (-((ν + 1 : ℕ) : ℤ)) :=
      (PadicInt.norm_le_pow_iff_le_valuation _ hne (ν + 1)).2 h
    have h4 := (PadicInt.norm_int_le_pow_iff_dvd).1 h3
    exact h2 (by simpa [Nat.cast_pow] using h4)
  exact le_antisymm h2' h1'

lemma cardHensel_norm_aeval_le_of_dvd {p : ℕ} [Fact p.Prime] {P : Polynomial ℤ} {y k : ℕ}
    (h : ((p ^ k : ℕ) : ℤ) ∣ P.eval (y : ℤ)) :
    ‖P.aeval (((y : ℤ)) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  rw [cardHensel_aeval_natCast]
  exact (PadicInt.norm_int_le_pow_iff_dvd).2 (by simpa [Nat.cast_pow] using h)

lemma cardHensel_norm_aeval_deriv_eq_of_padic {p : ℕ} [Fact p.Prime] {P : Polynomial ℤ} {y ν : ℕ}
    (h1 : ((p ^ ν : ℕ) : ℤ) ∣ P.derivative.eval (y : ℤ))
    (h2 : ¬ ((p ^ (ν + 1) : ℕ) : ℤ) ∣ P.derivative.eval (y : ℤ)) :
    ‖P.derivative.aeval (((y : ℤ)) : ℤ_[p])‖ = (p : ℝ) ^ (-(ν : ℤ)) := by
  have hval := cardHensel_valuation_of_padic h1 h2
  have hd0 : P.derivative.eval (y : ℤ) ≠ 0 := fun h => h2 (h ▸ dvd_zero _)
  have hne : ((P.derivative.eval (y : ℤ) : ℤ) : ℤ_[p]) ≠ 0 :=
    fun h => hd0 ((PadicInt.intCast_eq _ 0).1 h)
  rw [cardHensel_aeval_natCast P.derivative y, PadicInt.norm_eq_zpow_neg_valuation hne, hval]

theorem card_hensel_le {p : ℕ} [Fact p.Prime] (P : Polynomial ℤ) (hP : P ≠ 0) (M : ℕ)
    (hM : 1 ≤ M) : (henselSet p P M).card ≤ P.natDegree := by
  classical
  let F : Polynomial ℤ_[p] := P.map (algebraMap ℤ ℤ_[p])
  let u : ℕ → ℤ_[p] := fun y => ((y : ℤ) : ℤ_[p])
  let root : ℕ → ℤ_[p] := fun y =>
    if h : ‖P.aeval (u y)‖ < ‖P.derivative.aeval (u y)‖ ^ 2
    then Classical.choose (hensels_lemma h) else u y
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have key : ∀ y ∈ henselSet p P M, P.aeval (root y) = 0 ∧
      ‖u y - root y‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
    intro y hy
    obtain ⟨hyrange, ν, h1, h2, h3⟩ := Finset.mem_filter.1 hy
    have hD := cardHensel_norm_aeval_deriv_eq_of_padic h1 h2
    have hW := cardHensel_norm_aeval_le_of_dvd h3
    have hmax1 : ((M + ν : ℕ) : ℤ) ≤ ((max (2 * ν + 1) (M + ν) : ℕ) : ℤ) := by
      push_cast; exact le_max_right _ _
    have hmax2 : ((2 * ν + 1 : ℕ) : ℤ) ≤ ((max (2 * ν + 1) (M + ν) : ℕ) : ℤ) := by
      push_cast; exact le_max_left _ _
    have hW1 : ‖P.aeval (u y)‖ ≤ (p : ℝ) ^ (-((M + ν : ℕ) : ℤ)) :=
      hW.trans ((zpow_le_zpow_iff_right₀ hp1).2 (by linarith [hmax1]))
    have hW2 : ‖P.aeval (u y)‖ ≤ (p : ℝ) ^ (-((2 * ν + 1 : ℕ) : ℤ)) :=
      hW.trans ((zpow_le_zpow_iff_right₀ hp1).2 (by linarith [hmax2]))
    have hnorm : ‖P.aeval (u y)‖ < ‖P.derivative.aeval (u y)‖ ^ 2 := by
      rw [hD]
      have hsq : ((p : ℝ) ^ (-(ν : ℤ))) ^ 2 = (p : ℝ) ^ (-((2 * ν : ℕ) : ℤ)) := by
        rw [sq, ← zpow_add₀ (by positivity : (p : ℝ) ≠ 0)]
        congr 1; push_cast; ring
      rw [hsq]
      calc ‖P.aeval (u y)‖ ≤ (p : ℝ) ^ (-((2 * ν + 1 : ℕ) : ℤ)) := hW2
        _ < (p : ℝ) ^ (-((2 * ν : ℕ) : ℤ)) :=
            (zpow_lt_zpow_iff_right₀ hp1).2 (by push_cast; omega)
    have hspec := Classical.choose_spec (hensels_lemma hnorm)
    have hroot_def : root y = Classical.choose (hensels_lemma hnorm) := by
      simp only [root, dif_pos hnorm]
    have hroot0 : P.aeval (root y) = 0 := by
      rw [hroot_def]; exact hspec.1
    have hDroot : ‖P.derivative.aeval (root y)‖ = (p : ℝ) ^ (-(ν : ℤ)) := by
      rw [hroot_def, hspec.2.2.1, hD]
    refine ⟨hroot0, ?_⟩
    by_cases hW0 : P.aeval (u y) = 0
    · have huu : u y = root y := by
        rw [hroot_def]
        exact hspec.2.2.2 (u y) hW0 (by
          rw [sub_self, norm_zero, hD]
          exact zpow_pos (by positivity) _)
      rw [huu, sub_self, norm_zero]
      exact zpow_nonneg (by positivity) _
    · have hlt : ‖u y - root y‖ < ‖P.derivative.aeval (root y)‖ := by
        calc ‖u y - root y‖ = ‖u y - Classical.choose (hensels_lemma hnorm)‖ := by rw [hroot_def]
          _ = ‖Classical.choose (hensels_lemma hnorm) - u y‖ := norm_sub_rev _ _
          _ < ‖P.derivative.aeval (u y)‖ := hspec.2.1
          _ = ‖P.derivative.aeval (root y)‖ := hD.trans hDroot.symm
      have hkey2 := aeval_dist_eq_norm P hroot0 hlt
      rw [hDroot] at hkey2
      have hs : (p : ℝ) ^ (-(ν : ℤ)) ≠ 0 := zpow_ne_zero _ (by positivity)
      have hrepr : ‖u y - root y‖ = ‖P.aeval (u y)‖ / (p : ℝ) ^ (-(ν : ℤ)) := by
        rw [eq_div_iff hs]
        exact hkey2
      calc ‖u y - root y‖ = ‖P.aeval (u y)‖ / (p : ℝ) ^ (-(ν : ℤ)) := hrepr
        _ ≤ (p : ℝ) ^ (-((M + ν : ℕ) : ℤ)) / (p : ℝ) ^ (-(ν : ℤ)) :=
            div_le_div_of_nonneg_right hW1 (le_of_lt (zpow_pos (by positivity) _))
        _ = (p : ℝ) ^ (-(M : ℤ)) := by
            rw [← zpow_sub₀ (by positivity : (p : ℝ) ≠ 0)]
            congr 1; push_cast; ring
  have hinj : Set.InjOn root ↑(henselSet p P M) := by
    intro y₁ hy₁ y₂ hy₂ heq
    by_contra hne
    have d₁ := (key y₁ hy₁).2
    have d₂ := (key y₂ hy₂).2
    have hcomb : ‖u y₁ - u y₂‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
      have hz : u y₁ - u y₂ = (u y₁ - root y₁) + (root y₁ - u y₂) := by ring
      rw [hz]
      refine (PadicInt.nonarchimedean _ _).trans (max_le d₁ ?_)
      rw [heq, norm_sub_rev]
      exact d₂
    have hcast : (((y₁ : ℤ) - (y₂ : ℤ) : ℤ) : ℤ_[p]) = u y₁ - u y₂ := by
      simp only [u]; push_cast; ring
    have hdvd : (p ^ M : ℤ) ∣ ((y₁ : ℤ) - (y₂ : ℤ)) :=
      (PadicInt.norm_int_le_pow_iff_dvd).1 (by rw [hcast]; exact hcomb)
    exact hne (eq_of_dvd_sub_of_lt (Finset.mem_range.1 (Finset.mem_filter.1 hy₁).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 hy₂).1) hdvd)
  have hFne : F ≠ 0 := by
    intro h
    have hfl : F = P.map (algebraMap ℤ ℤ_[p]) := rfl
    rw [hfl] at h
    exact hP ((Polynomial.map_eq_zero_iff (f := algebraMap ℤ ℤ_[p])
      (fun a b hab => (PadicInt.intCast_eq a b).1 hab)).1 h)
  have hsub : (henselSet p P M).image root ⊆ F.roots.toFinset := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    refine ⟨hFne, ?_⟩
    rw [Polynomial.IsRoot.def]
    have hfl : F = P.map (algebraMap ℤ ℤ_[p]) := rfl
    rw [hfl, Polynomial.eval_map_algebraMap]
    exact (key y hy).1
  calc (henselSet p P M).card
      = ((henselSet p P M).image root).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ F.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ F.roots.card := Multiset.toFinset_card_le _
    _ ≤ F.natDegree := Polynomial.card_roots' F
    _ ≤ P.natDegree := by
        have hfl : F = P.map (algebraMap ℤ ℤ_[p]) := rfl
        rw [hfl]; exact Polynomial.natDegree_map_le

end Work.LinnikBurgess
