import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.sum_le_top_of_monotone
import Submission.Work.Holonomy3.card_filter_species_ge
import Submission.Work.Holonomy3.filter_div_eq_top
import Submission.Work.Holonomy3.finProdFin_symm_fst

namespace Work.Holonomy3

open scoped BigOperators

/-- (fallback copy, inlined) -/
private theorem col_sum_log_le {m d k : ℕ} (hk : 0 < k) (hmul : m * k = d) {u : ℕ} (hu : u ≤ m)
    (B c p : ℕ) (i : Fin d → Fin m) (hi : Balanced i)
    (n : Fin d → ℕ) (hn : Monotone n) :
    (∑ s : Fin d, Nat.log p ((if (i s : ℕ) < u then 0 else B) * n s + c))
      ≤ d * Nat.log p c +
        ∑ j : Fin d, Nat.log p ((if (j : ℕ) / k < u then 0 else B) * n j + c) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    have hd0 : d = 0 := by rw [← hmul, Nat.zero_mul]
    subst hd0
    simp
  · have hdm : d / m = k := by rw [← hmul]; exact Nat.mul_div_right k hm0
    have hmd : m ∣ d := ⟨k, hmul.symm⟩
    set g : Fin d → ℕ := fun s => Nat.log p (B * n s + c) with hg
    have hgmono : Monotone g := by
      rw [hg]
      intro a b hab
      exact Nat.log_mono_right (Nat.add_le_add_right (Nat.mul_le_mul_left B (hn hab)) c)
    set S : Finset (Fin d) := Finset.univ.filter (fun s => u ≤ (i s : ℕ)) with hS
    have hScard : S.card = (m - u) * k := by
      rw [hS, card_filter_species_ge hm0 hmd i hi hu, hdm]
    have ht : (m - u) * k ≤ d := by
      rw [← hmul]
      exact Nat.mul_le_mul_right k (Nat.sub_le m u)
    have hrearr : ∑ s ∈ S, g s ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin d => u ≤ (j : ℕ) / k), g j := by
      have h := sum_le_top_of_monotone ht hgmono S (le_of_eq hScard)
      rwa [← filter_div_eq_top hk hmul hu] at h
    have hR : ∑ j ∈ Finset.univ.filter (fun j : Fin d => u ≤ (j : ℕ) / k), g j
        ≤ ∑ j : Fin d, Nat.log p ((if (j : ℕ) / k < u then 0 else B) * n j + c) := by
      have hcongr : ∑ j ∈ Finset.univ.filter (fun j : Fin d => u ≤ (j : ℕ) / k), g j
          = ∑ j ∈ Finset.univ.filter (fun j : Fin d => u ≤ (j : ℕ) / k),
              Nat.log p ((if (j : ℕ) / k < u then 0 else B) * n j + c) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hlt : ¬ ((j : ℕ) / k < u) := by
          have := (Finset.mem_filter.mp hj).2
          omega
        simp [hlt, hg]
      rw [hcongr]
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => ?_)
      exact Nat.zero_le _
    have hrearr' : ∑ s ∈ S, g s
        ≤ ∑ j : Fin d, Nat.log p ((if (j : ℕ) / k < u then 0 else B) * n j + c) :=
      le_trans hrearr hR
    have hsplit : (∑ s : Fin d, Nat.log p ((if (i s : ℕ) < u then 0 else B) * n s + c))
        = (∑ s ∈ S, g s)
          + (Finset.univ.filter (fun s : Fin d => ¬ u ≤ (i s : ℕ))).card * Nat.log p c := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
            (p := fun s : Fin d => u ≤ (i s : ℕ))
            (f := fun s => Nat.log p ((if (i s : ℕ) < u then 0 else B) * n s + c))]
      congr 1
      · rw [hS]
        refine Finset.sum_congr rfl (fun s hs => ?_)
        have hle : u ≤ (i s : ℕ) := (Finset.mem_filter.mp hs).2
        have hlt : ¬ (i s : ℕ) < u := by omega
        simp [hlt, hg]
      · have hconst : ∀ s ∈ Finset.univ.filter (fun s : Fin d => ¬ u ≤ (i s : ℕ)),
            Nat.log p ((if (i s : ℕ) < u then 0 else B) * n s + c) = Nat.log p c := by
          intro s hs
          have hlt : (i s : ℕ) < u := by
            have := (Finset.mem_filter.mp hs).2
            omega
          simp [hlt]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    have hcard : (Finset.univ.filter (fun s : Fin d => ¬ u ≤ (i s : ℕ))).card * Nat.log p c
        ≤ d * Nat.log p c := by
      refine Nat.mul_le_mul_right _ ?_
      have h := Finset.card_le_card
        (Finset.filter_subset (fun s : Fin d => ¬ u ≤ (i s : ℕ)) Finset.univ)
      simpa using h
    calc ∑ s : Fin d, Nat.log p ((if (i s : ℕ) < u then 0 else B) * n s + c)
        = (∑ s ∈ S, g s)
            + (Finset.univ.filter (fun s : Fin d => ¬ u ≤ (i s : ℕ))).card * Nat.log p c :=
          hsplit
      _ ≤ (∑ j : Fin d, Nat.log p ((if (j : ℕ) / k < u then 0 else B) * n j + c))
            + d * Nat.log p c := Nat.add_le_add hrearr' hcard
      _ = d * Nat.log p c
            + ∑ j : Fin d, Nat.log p ((if (j : ℕ) / k < u then 0 else B) * n j + c) :=
          Nat.add_comm _ _

/-- (fallback copy, inlined) -/
private theorem factorization_prod_lcmUpto {ι : Type*} [Fintype ι] (f : ι → ℕ) {p : ℕ}
    (hp : p.Prime) :
    (∏ i, Submission.CDTPlan.lcmUpto (f i)).factorization p = ∑ i, Nat.log p (f i) := by
  have h := Nat.factorization_prod (S := Finset.univ) (g := fun i => Submission.CDTPlan.lcmUpto (f i))
    (fun i _ => Nat.lcmUpto_ne_zero _)
  rw [h, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl (fun i _ => Nat.factorization_lcmUpto (f i) hp)


/-- **Column-shape refinement of the lcm cap.**  For a balanced species vector `i : Fin d → Fin m`
(each species occurring `d/m` times) and a column-shaped lcm array `b` (column `h` is `0` on the
first `u_h` rows and a constant afterwards), the product of the lcms at the *permuted* positions
`i` divides `[1,…,c]^{r·d}` times the product of the lcms at the *identity* positions `j ↦ j/m`,
for a *monotone* exponent vector `n`.  Prime by prime this is the rearrangement inequality: in
column `h` the active positions of `i` carry `(m-u_h)·d/m` of the exponents, and
`N ↦ val_p [1,…,b_h N + c]` is monotone in `N`, so the sum is maximised by the top
`(m-u_h)·d/m` positions, which is the identity arrangement. -/
theorem lcm_prod_dvd_shape {m r d : ℕ} (hm : 0 < m) (b : Fin m → Fin r → ℕ)
    (hb : Submission.CDTPlan.ColumnShape b) (hmd : m ∣ d) (c : ℕ) (i : Fin d → Fin m)
    (hi : Work.Holonomy3.Balanced i) (n : Fin d → ℕ) (hn : Monotone n) :
    (∏ s : Fin d, ∏ h : Fin r, Submission.CDTPlan.lcmUpto (b (i s) h * n s + c)) ∣
      (Submission.CDTPlan.lcmUpto c) ^ (r * d) *
        ∏ i' : Fin m, ∏ s : Fin (d / m), ∏ h : Fin r,
          Submission.CDTPlan.lcmUpto (b i' h *
            n (Fin.cast (Nat.mul_div_cancel' hmd) (finProdFinEquiv (i', s))) + c) := by
  classical
  by_cases hk : 0 < d / m
  · -- main case: the position `j : Fin d` sits in the block `j / (d/m)` of the identity arrangement
    have hmul : m * (d / m) = d := Nat.mul_div_cancel' hmd
    set E : Fin m × Fin (d / m) ≃ Fin d :=
      (finProdFinEquiv (m := m) (n := d / m)).trans (finCongr hmul) with hE
    -- reindex the right hand product along `E`: position `s + (d/m)·i'` is `E (i', s)`
    have hP : (∏ i' : Fin m, ∏ s : Fin (d / m), ∏ h : Fin r,
          Submission.CDTPlan.lcmUpto
            (b i' h * n (Fin.cast (Nat.mul_div_cancel' hmd) (finProdFinEquiv (i', s))) + c))
        = ∏ j : Fin d, ∏ h : Fin r, Submission.CDTPlan.lcmUpto (b ((E.symm j).1) h * n j + c) := by
      have h1 : (∏ i' : Fin m, ∏ s : Fin (d / m), ∏ h : Fin r,
          Submission.CDTPlan.lcmUpto
            (b i' h * n (Fin.cast (Nat.mul_div_cancel' hmd) (finProdFinEquiv (i', s))) + c))
        = ∏ x : Fin m × Fin (d / m), ∏ h : Fin r,
            Submission.CDTPlan.lcmUpto
              (b x.1 h * n (Fin.cast (Nat.mul_div_cancel' hmd) (finProdFinEquiv x)) + c) :=
        (Fintype.prod_prod_type (f := fun x : Fin m × Fin (d / m) => ∏ h : Fin r,
          Submission.CDTPlan.lcmUpto
            (b x.1 h * n (Fin.cast (Nat.mul_div_cancel' hmd) (finProdFinEquiv x)) + c))).symm
      rw [h1]
      refine Fintype.prod_equiv E _ _ (fun x => ?_)
      have hEx : E x = Fin.cast (Nat.mul_div_cancel' hmd) (finProdFinEquiv x) := rfl
      rw [Equiv.symm_apply_apply E x, hEx]
    rw [hP]
    -- nonzero factors, to apply the prime-by-prime criterion for divisibility
    have hLne : (∏ s : Fin d, ∏ h : Fin r, Submission.CDTPlan.lcmUpto (b (i s) h * n s + c)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun s _ =>
        Finset.prod_ne_zero_iff.mpr (fun h _ => Nat.lcmUpto_ne_zero _))
    have hPne : (∏ j : Fin d, ∏ h : Fin r,
        Submission.CDTPlan.lcmUpto (b ((E.symm j).1) h * n j + c)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ =>
        Finset.prod_ne_zero_iff.mpr (fun h _ => Nat.lcmUpto_ne_zero _))
    have hRne : (Submission.CDTPlan.lcmUpto c) ^ (r * d) *
        (∏ j : Fin d, ∏ h : Fin r, Submission.CDTPlan.lcmUpto (b ((E.symm j).1) h * n j + c)) ≠ 0 :=
      Nat.mul_ne_zero (pow_ne_zero _ (Nat.lcmUpto_ne_zero _)) hPne
    refine (Nat.factorization_prime_le_iff_dvd hLne hRne).mp (fun p hp => ?_)
    -- evaluate both factorizations prime by prime
    have hL : (∏ s : Fin d, ∏ h : Fin r,
        Submission.CDTPlan.lcmUpto (b (i s) h * n s + c)).factorization p
        = ∑ s : Fin d, ∑ h : Fin r, Nat.log p (b (i s) h * n s + c) := by
      have h1 := Nat.factorization_prod (S := Finset.univ)
        (g := fun s : Fin d => ∏ h : Fin r, Submission.CDTPlan.lcmUpto (b (i s) h * n s + c))
        (fun s _ => Finset.prod_ne_zero_iff.mpr (fun h _ => Nat.lcmUpto_ne_zero _))
      rw [h1, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      exact factorization_prod_lcmUpto (fun h : Fin r => b (i s) h * n s + c) hp
    have hR : ((Submission.CDTPlan.lcmUpto c) ^ (r * d) *
        (∏ j : Fin d, ∏ h : Fin r,
          Submission.CDTPlan.lcmUpto (b ((E.symm j).1) h * n j + c))).factorization p
        = r * d * Nat.log p c +
          ∑ j : Fin d, ∑ h : Fin r, Nat.log p (b ((E.symm j).1) h * n j + c) := by
      have hne1 : (Submission.CDTPlan.lcmUpto c) ^ (r * d) ≠ 0 :=
        pow_ne_zero _ (Nat.lcmUpto_ne_zero _)
      rw [Nat.factorization_mul hne1 hPne, Finsupp.add_apply, Nat.factorization_pow,
        Finsupp.smul_apply, smul_eq_mul,
        show (Submission.CDTPlan.lcmUpto c).factorization p = Nat.log p c from
          Nat.factorization_lcmUpto c hp]
      have h2 := Nat.factorization_prod (S := Finset.univ)
        (g := fun j : Fin d => ∏ h : Fin r,
          Submission.CDTPlan.lcmUpto (b ((E.symm j).1) h * n j + c))
        (fun j _ => Finset.prod_ne_zero_iff.mpr (fun h _ => Nat.lcmUpto_ne_zero _))
      rw [h2, Finsupp.finsetSum_apply]
      refine congrArg (fun z => r * d * Nat.log p c + z) ?_
      exact Finset.sum_congr rfl (fun j _ =>
        factorization_prod_lcmUpto (fun h : Fin r => b ((E.symm j).1) h * n j + c) hp)
    rw [hL, hR]
    -- the columnwise rearrangement inequality, summed over the columns
    have hcol : ∀ h : Fin r,
        (∑ s : Fin d, Nat.log p (b (i s) h * n s + c))
          ≤ d * Nat.log p c + ∑ j : Fin d, Nat.log p (b ((E.symm j).1) h * n j + c) := by
      intro h
      obtain ⟨u, B, hB⟩ := hb h
      -- replace `u` by `min u m` so that the "first `u` rows" make sense inside `Fin m`
      set u' := min u m with hu'def
      have hu' : u' ≤ m := min_le_right u m
      have hB' : ∀ t : Fin m, b t h = if (t : ℕ) < u' then 0 else B := by
        intro t
        rw [hB t]
        by_cases hut : (t : ℕ) < u
        · have hlt : (t : ℕ) < u' := by
            rw [hu'def, lt_min_iff]
            exact ⟨hut, t.isLt⟩
          simp [hut, hlt]
        · have hlt : ¬ (t : ℕ) < u' := by
            intro hh
            exact hut (lt_of_lt_of_le hh (min_le_left u m))
          simp [hut, hlt]
      have hσ : ∀ j : Fin d, (((E.symm j).1 : Fin m) : ℕ) = (j : ℕ) / (d / m) :=
        fun j => finProdFin_symm_fst hmul j
      simpa only [hB', hσ] using
        col_sum_log_le (hk := hk) (hmul := hmul) (hu := hu') B c p i hi n hn
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    calc ∑ h : Fin r, ∑ s : Fin d, Nat.log p (b (i s) h * n s + c)
        ≤ ∑ h : Fin r,
            (d * Nat.log p c + ∑ j : Fin d, Nat.log p (b ((E.symm j).1) h * n j + c)) :=
          Finset.sum_le_sum (fun h _ => hcol h)
      _ = r * d * Nat.log p c +
            ∑ h : Fin r, ∑ j : Fin d, Nat.log p (b ((E.symm j).1) h * n j + c) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          congr 1
          rw [Nat.cast_id, Nat.mul_assoc]
  · -- degenerate case `d / m = 0`, hence `d = 0`: both sides are `1`
    have hk0 : d / m = 0 := Nat.eq_zero_of_not_pos hk
    have hd0 : d = 0 := by rw [← Nat.mul_div_cancel' hmd, hk0, Nat.mul_zero]
    subst hd0
    simp

end Work.Holonomy3
