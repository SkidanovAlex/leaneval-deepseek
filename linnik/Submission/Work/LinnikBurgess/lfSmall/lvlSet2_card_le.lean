import Mathlib
import Submission.Work.LinnikBurgess.lfSmall.two_defs
import Submission.Work.LinnikBurgess.card_hensel_le

/-!
# `lvlSet2_card_le`: the level set of Lemma A₂ at level `s < capLevel 2 e` has at most `8` points

`lvlSet2 e s a b` is the set of `y < 2 ^ m` (`m = cubeLevel 2 e`) that are `2`-unit points and
satisfy `2 ^ (m + s - 1) ∣ N(y)`, `N'(y) ≠ 0`, `v₂(N'(y)) = s`, where `N = critN a b`.

For `s < capLevel 2 e` and `e ≥ 13` we have `2 s + 1 ≤ m + s - 1`, so the Hensel hypothesis
`‖N(y)‖ < ‖N'(y)‖²` holds at every `y ∈ lvlSet2 e s a b`, and Hensel's lemma produces a root
`θ ∈ ℤ_[2]` of `N` with `‖y - θ‖ ≤ 2 ^ (-(m-1))`, i.e. `2 ^ (m-1) ∣ (y - θ)`.

Two distinct elements of the set that share this root are congruent mod `2 ^ (m-1)` while both
lying in `[0, 2^m)`, so a residue class mod `2 ^ (m-1)` contains at most `2` of them.  Since
`N` has at most `natDegree N ≤ 4` roots in the domain `ℤ_[2]`, we get `card ≤ 2 * 4 = 8`.
-/

open Polynomial

namespace Work.LinnikBurgess.lfSmall

/-- `cubeLevel 2 e = (e + 3) / 3`. -/
lemma cubeLevel_two_eq (e : ℕ) : cubeLevel 2 e = (e + 3) / 3 := by simp [cubeLevel]

/-- `capLevel 2 e + 1 ≤ cubeLevel 2 e`: the cap level is strictly below the cube level. -/
lemma capLevel_two_add_one_le_cubeLevel (e : ℕ) : capLevel 2 e + 1 ≤ cubeLevel 2 e := by
  have h := Nat.div_add_mod (e + 3) 3
  have h' : (e + 3) % 3 < 3 := Nat.mod_lt _ (by norm_num)
  simp only [capLevel, cubeLevel_two_eq]
  omega

/-- **Hensel's lemma with an explicit distance bound.**  If `2 ^ ν` exactly divides `P'(y)` and
`2 ^ (max (2ν+1) (M+ν))` divides `P(y)`, then `P` has a root `θ` in `ℤ_[2]` with
`‖y - θ‖ ≤ 2 ^ (-M)`.  (This is the quantitative Hensel step used for the `2`-adic counting
lemmas; it is the per-element part of the proof of `card_hensel_le` with the range condition
`y < 2 ^ M` dropped.) -/
lemma hensel_root_dist_le_two {P : Polynomial ℤ} {M ν y : ℕ}
    (h1 : ((2 ^ ν : ℕ) : ℤ) ∣ P.derivative.eval (y : ℤ))
    (h2 : ¬ ((2 ^ (ν + 1) : ℕ) : ℤ) ∣ P.derivative.eval (y : ℤ))
    (h3 : ((2 ^ max (2 * ν + 1) (M + ν) : ℕ) : ℤ) ∣ P.eval (y : ℤ)) :
    ∃ θ : ℤ_[2], P.aeval θ = 0 ∧ ‖(((y : ℤ)) : ℤ_[2]) - θ‖ ≤ (2 : ℝ) ^ (-(M : ℤ)) := by
  classical
  have hone : (1 : ℝ) < 2 := by norm_num
  have htwo : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  have hD0 := cardHensel_norm_aeval_deriv_eq_of_padic (p := 2) h1 h2
  have hD : ‖P.derivative.aeval (((y : ℤ)) : ℤ_[2])‖ = (2 : ℝ) ^ (-(ν : ℤ)) := by
    rw [hD0, htwo]
  have hW0' := cardHensel_norm_aeval_le_of_dvd (p := 2) h3
  have hW : ‖P.aeval (((y : ℤ)) : ℤ_[2])‖
      ≤ (2 : ℝ) ^ (-(((max (2 * ν + 1) (M + ν) : ℕ)) : ℤ)) := by
    refine hW0'.trans ?_
    rw [htwo]
  have hmax1 : ((M + ν : ℕ) : ℤ) ≤ ((max (2 * ν + 1) (M + ν) : ℕ) : ℤ) := by
    push_cast; exact le_max_right _ _
  have hmax2 : ((2 * ν + 1 : ℕ) : ℤ) ≤ ((max (2 * ν + 1) (M + ν) : ℕ) : ℤ) := by
    push_cast; exact le_max_left _ _
  have hW1 : ‖P.aeval (((y : ℤ)) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-((M + ν : ℕ) : ℤ)) :=
    hW.trans ((zpow_le_zpow_iff_right₀ hone).2 (by linarith [hmax1]))
  have hW2 : ‖P.aeval (((y : ℤ)) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-((2 * ν + 1 : ℕ) : ℤ)) :=
    hW.trans ((zpow_le_zpow_iff_right₀ hone).2 (by linarith [hmax2]))
  have hnorm : ‖P.aeval (((y : ℤ)) : ℤ_[2])‖
      < ‖P.derivative.aeval (((y : ℤ)) : ℤ_[2])‖ ^ 2 := by
    rw [hD]
    have hsq : ((2 : ℝ) ^ (-(ν : ℤ))) ^ 2 = (2 : ℝ) ^ (-((2 * ν : ℕ) : ℤ)) := by
      rw [sq, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1; push_cast; ring
    rw [hsq]
    calc ‖P.aeval (((y : ℤ)) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-((2 * ν + 1 : ℕ) : ℤ)) := hW2
      _ < (2 : ℝ) ^ (-((2 * ν : ℕ) : ℤ)) :=
          (zpow_lt_zpow_iff_right₀ hone).2 (by push_cast; omega)
  obtain ⟨θ, hθ0, hθlt, hθderiv, huniq⟩ := hensels_lemma (R := ℤ) hnorm
  refine ⟨θ, hθ0, ?_⟩
  by_cases hW0 : P.aeval (((y : ℤ)) : ℤ_[2]) = 0
  · have hpos : (0 : ℝ) < ‖P.derivative.aeval (((y : ℤ)) : ℤ_[2])‖ := by
      rw [hD]; exact zpow_pos (by norm_num : (0 : ℝ) < 2) _
    have huθ : (((y : ℤ)) : ℤ_[2]) = θ :=
      huniq (((y : ℤ)) : ℤ_[2]) hW0 (by rw [sub_self, norm_zero]; exact hpos)
    rw [huθ, sub_self, norm_zero]
    exact zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  · have hlt : ‖(((y : ℤ)) : ℤ_[2]) - θ‖ < ‖P.derivative.aeval θ‖ := by
      rw [hθderiv, norm_sub_rev]
      exact hθlt
    have hkey := aeval_dist_eq_norm (p := 2) P hθ0 hlt
    have hθderiv' : ‖P.derivative.aeval θ‖ = (2 : ℝ) ^ (-(ν : ℤ)) := by rw [hθderiv, hD]
    rw [hθderiv'] at hkey
    have hs : (2 : ℝ) ^ (-(ν : ℤ)) ≠ 0 := zpow_ne_zero _ (by norm_num)
    have hrepr : ‖(((y : ℤ)) : ℤ_[2]) - θ‖
        = ‖P.aeval (((y : ℤ)) : ℤ_[2])‖ / (2 : ℝ) ^ (-(ν : ℤ)) := by
      rw [eq_div_iff hs]
      exact hkey
    calc ‖(((y : ℤ)) : ℤ_[2]) - θ‖
        = ‖P.aeval (((y : ℤ)) : ℤ_[2])‖ / (2 : ℝ) ^ (-(ν : ℤ)) := hrepr
      _ ≤ (2 : ℝ) ^ (-((M + ν : ℕ) : ℤ)) / (2 : ℝ) ^ (-(ν : ℤ)) :=
          div_le_div_of_nonneg_right hW1 (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _))
      _ = (2 : ℝ) ^ (-(M : ℤ)) := by
          rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
          congr 1; push_cast; ring

/-- **Counting points clustered on `2`-adic roots.**  Let `S ⊆ [0, 2 ^ m)` be a finite set of
natural numbers, `f : ℕ → ℤ_[2]` and `R` a finite set of `2`-adic numbers containing `f`` on `S`.
If every `y ∈ S` is within `2 ^ (-(m-1))` of `f y`, then `S.card ≤ 2 * R.card`: elements of `S`
with the same `f`-value are congruent mod `2 ^ (m-1)`, and a residue class mod `2 ^ (m-1)` meets
`[0, 2 ^ m)` in exactly two integers. -/
lemma card_close_to_roots_le_two {m : ℕ} (hm : 1 ≤ m) {S : Finset ℕ} {f : ℕ → ℤ_[2]}
    {R : Finset ℤ_[2]}
    (hmaps : ∀ y ∈ S, f y ∈ R)
    (hrange : ∀ y ∈ S, y < 2 ^ m)
    (hclose : ∀ y ∈ S, ‖(((y : ℤ)) : ℤ_[2]) - f y‖
      ≤ (2 : ℝ) ^ (-((m - 1 : ℕ) : ℤ))) :
    S.card ≤ 2 * R.card := by
  classical
  have hL : 0 < 2 ^ (m - 1) := pow_pos (by norm_num) _
  have h2m : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have h : 2 ^ m = 2 ^ (m - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h]; ring
  -- every fibre of `f` over `R` has at most two elements
  have hfiber : ∀ r ∈ R, (S.filter (fun y => f y = r)).card ≤ 2 := by
    intro r _
    set T := S.filter (fun y => f y = r) with hT
    have hTsub : T ⊆ S := by
      intro y hy; rw [hT, Finset.mem_filter] at hy; exact hy.1
    have hTr : ∀ y ∈ T, f y = r := by
      intro y hy; rw [hT, Finset.mem_filter] at hy; exact hy.2
    have hcr : ∀ y ∈ T, ‖(((y : ℤ)) : ℤ_[2]) - r‖
        ≤ (2 : ℝ) ^ (-((m - 1 : ℕ) : ℤ)) := by
      intro y hy
      rw [← hTr y hy]
      exact hclose y (hTsub hy)
    -- two elements of the fibre are congruent modulo `2 ^ (m-1)`
    have hdvd : ∀ y ∈ T, ∀ y' ∈ T,
        ((2 ^ (m - 1) : ℕ) : ℤ) ∣ (y : ℤ) - (y' : ℤ) := by
      intro y hy y' hy'
      have hb : ‖(((y : ℤ)) : ℤ_[2]) - (((y' : ℤ)) : ℤ_[2])‖
          ≤ (2 : ℝ) ^ (-((m - 1 : ℕ) : ℤ)) := by
        have e1 := hcr y hy
        have e2 := hcr y' hy'
        have hsplit : (((y : ℤ)) : ℤ_[2]) - (((y' : ℤ)) : ℤ_[2])
            = ((((y : ℤ)) : ℤ_[2]) - r) + (r - (((y' : ℤ)) : ℤ_[2])) := by ring
        rw [hsplit]
        refine (PadicInt.nonarchimedean _ _).trans (max_le e1 ?_)
        rw [norm_sub_rev]
        exact e2
      have hcast : ((((y : ℤ) - (y' : ℤ) : ℤ)) : ℤ_[2])
          = (((y : ℤ)) : ℤ_[2]) - (((y' : ℤ)) : ℤ_[2]) := by push_cast; ring
      have h := (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := (y : ℤ) - (y' : ℤ))
        (n := m - 1)).1 (by rw [hcast]; exact hb)
      simpa using h
    -- the quotient map `y ↦ y / 2^(m-1)` is injective on the fibre
    have hinj : Set.InjOn (fun y : ℕ => y / 2 ^ (m - 1)) ↑T := by
      intro y hy y' hy' hq
      have hq' : y / 2 ^ (m - 1) = y' / 2 ^ (m - 1) := hq
      have hy1 : y / 2 ^ (m - 1) * 2 ^ (m - 1) ≤ y :=
        (Nat.le_div_iff_mul_le hL).1 (le_refl _)
      have hy2 : y < y / 2 ^ (m - 1) * 2 ^ (m - 1) + 2 ^ (m - 1) := by
        have h := (Nat.div_lt_iff_lt_mul hL).1 (Nat.lt_succ_self (y / 2 ^ (m - 1)))
        rw [Nat.succ_eq_add_one, Nat.add_mul, one_mul] at h
        exact h
      have hy'1 : y' / 2 ^ (m - 1) * 2 ^ (m - 1) ≤ y' :=
        (Nat.le_div_iff_mul_le hL).1 (le_refl _)
      have hy'2 : y' < y' / 2 ^ (m - 1) * 2 ^ (m - 1) + 2 ^ (m - 1) := by
        have h := (Nat.div_lt_iff_lt_mul hL).1 (Nat.lt_succ_self (y' / 2 ^ (m - 1)))
        rw [Nat.succ_eq_add_one, Nat.add_mul, one_mul] at h
        exact h
      rw [← hq'] at hy'1 hy'2
      have hbound : (((y : ℤ) - (y' : ℤ))).natAbs < 2 ^ (m - 1) := by
        rcases le_total y y' with h | h
        · have hc : (y : ℤ) - (y' : ℤ) = -(((y' - y : ℕ)) : ℤ) := by omega
          rw [hc, Int.natAbs_neg, Int.natAbs_natCast]
          omega
        · have hc : (y : ℤ) - (y' : ℤ) = (((y - y' : ℕ)) : ℤ) := by omega
          rw [hc, Int.natAbs_natCast]
          omega
      have hnat : 2 ^ (m - 1) ∣ (((y : ℤ) - (y' : ℤ))).natAbs := by
        simpa using (Int.natAbs_dvd_natAbs (a := ((2 ^ (m - 1) : ℕ) : ℤ))
          (b := (y : ℤ) - (y' : ℤ))).2 (hdvd y hy y' hy')
      have hzero := Nat.eq_zero_of_dvd_of_lt hnat hbound
      have hz : (y : ℤ) = (y' : ℤ) := by
        have := Int.natAbs_eq_zero.mp hzero
        omega
      exact Int.ofNat_inj.mp hz
    have himg : T.image (fun y : ℕ => y / 2 ^ (m - 1)) ⊆ Finset.range 2 := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨y, hy, rfl⟩ := hq
      rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hL, ← h2m]
      exact hrange y (hTsub hy)
    calc T.card = (T.image (fun y : ℕ => y / 2 ^ (m - 1))).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range 2).card := Finset.card_le_card himg
      _ = 2 := by simp
  have hsum : S.card = ∑ r ∈ R, (S.filter (fun y => f y = r)).card :=
    Finset.card_eq_sum_card_fiberwise (fun y hy => hmaps y hy)
  rw [hsum]
  calc ∑ r ∈ R, (S.filter (fun y => f y = r)).card
      ≤ ∑ _r ∈ R, 2 := Finset.sum_le_sum (fun r hr => hfiber r hr)
    _ = 2 * R.card := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm]

theorem lvlSet2_card_le {e s : ℕ} (he : 13 ≤ e) (hs : s < capLevel 2 e) (a b : Fin 3 → ℕ) :
    (lvlSet2 e s a b).card ≤ 8 := by
  classical
  have hcube1 : 1 ≤ cubeLevel 2 e := by
    have h5 : 5 ≤ cubeLevel 2 e := by rw [cubeLevel_two_eq]; omega
    omega
  have hT : capLevel 2 e + 1 ≤ cubeLevel 2 e := capLevel_two_add_one_le_cubeLevel e
  have hs2 : s + 2 ≤ cubeLevel 2 e := by omega
  have hmax : max (2 * s + 1) (cubeLevel 2 e - 1 + s) = cubeLevel 2 e + s - 1 := by omega
  by_cases hN : critN a b = 0
  · have hempty : lvlSet2 e s a b = ∅ := by
      rw [lvlSet2, Finset.filter_eq_empty_iff]
      intro y _ hp
      exact hp.2.2.1 (by rw [hN]; simp)
    rw [hempty]
    simp
  · set F : Polynomial ℤ_[2] := (critN a b).map (algebraMap ℤ ℤ_[2]) with hFdef
    have hFne : F ≠ 0 := by
      rw [hFdef]
      intro h
      exact hN ((Polynomial.map_eq_zero_iff (f := algebraMap ℤ ℤ_[2])
        (fun x y hxy => (PadicInt.intCast_eq x y).1 hxy)).1 h)
    -- every point of the level set has a nearby root of `N` in `ℤ_[2]`
    have hroot : ∀ y ∈ lvlSet2 e s a b, ∃ θ : ℤ_[2], (critN a b).aeval θ = 0 ∧
        ‖(((y : ℤ)) : ℤ_[2]) - θ‖ ≤ (2 : ℝ) ^ (-(((cubeLevel 2 e - 1 : ℕ)) : ℤ)) := by
      intro y hy
      rw [lvlSet2, Finset.mem_filter, Finset.mem_range] at hy
      obtain ⟨-, -, hdvd, hderivne, hval⟩ := hy
      have h1 : ((2 ^ s : ℕ) : ℤ) ∣ (critN a b).derivative.eval (y : ℤ) := by
        rw [← Int.dvd_natAbs]
        exact_mod_cast (show 2 ^ s ∣ ((critN a b).derivative.eval (y : ℤ)).natAbs by
          rw [← hval]; exact pow_padicValNat_dvd)
      have h2 : ¬ ((2 ^ (s + 1) : ℕ) : ℤ) ∣ (critN a b).derivative.eval (y : ℤ) := by
        intro hcon
        have hnat : 2 ^ (s + 1) ∣ ((critN a b).derivative.eval (y : ℤ)).natAbs := by
          simpa using (Int.natAbs_dvd_natAbs (a := ((2 ^ (s + 1) : ℕ) : ℤ))
            (b := (critN a b).derivative.eval (y : ℤ))).2 hcon
        have hne : ((critN a b).derivative.eval (y : ℤ)).natAbs ≠ 0 := by
          simpa [Int.natAbs_eq_zero] using hderivne
        have := (padicValNat_dvd_iff_le hne).1 hnat
        omega
      have h3 : ((2 ^ max (2 * s + 1) (cubeLevel 2 e - 1 + s) : ℕ) : ℤ) ∣
          (critN a b).eval (y : ℤ) := by
        rw [hmax]; exact hdvd
      exact hensel_root_dist_le_two (M := cubeLevel 2 e - 1) (ν := s) h1 h2 h3
    -- choose such a root for every point of the level set
    let f : ℕ → ℤ_[2] := fun y => if h : ∃ θ : ℤ_[2], (critN a b).aeval θ = 0 ∧
        ‖(((y : ℤ)) : ℤ_[2]) - θ‖ ≤ (2 : ℝ) ^ (-(((cubeLevel 2 e - 1 : ℕ)) : ℤ))
      then Classical.choose h else 0
    have hfspec : ∀ y ∈ lvlSet2 e s a b, (critN a b).aeval (f y) = 0 ∧
        ‖(((y : ℤ)) : ℤ_[2]) - f y‖ ≤ (2 : ℝ) ^ (-(((cubeLevel 2 e - 1 : ℕ)) : ℤ)) := by
      intro y hy
      have h := hroot y hy
      have hff : f y = Classical.choose h := by
        show (if h' : ∃ θ : ℤ_[2], (critN a b).aeval θ = 0 ∧
          ‖(((y : ℤ)) : ℤ_[2]) - θ‖ ≤ (2 : ℝ) ^ (-(((cubeLevel 2 e - 1 : ℕ)) : ℤ))
          then Classical.choose h' else 0) = Classical.choose h
        exact dif_pos h
      rw [hff]
      exact Classical.choose_spec h
    -- these roots are roots of the image polynomial `F`
    set R : Finset ℤ_[2] := F.roots.toFinset with hRdef
    have hmaps : ∀ y ∈ lvlSet2 e s a b, f y ∈ R := by
      intro y hy
      rw [hRdef, Multiset.mem_toFinset, Polynomial.mem_roots']
      refine ⟨hFne, ?_⟩
      rw [Polynomial.IsRoot.def, hFdef, Polynomial.eval_map]
      simpa [Polynomial.aeval_def] using (hfspec y hy).1
    have hcard : (lvlSet2 e s a b).card ≤ 2 * R.card :=
      card_close_to_roots_le_two (m := cubeLevel 2 e) hcube1 hmaps
        (fun y hy => by
          rw [lvlSet2, Finset.mem_filter, Finset.mem_range] at hy
          exact hy.1)
        (fun y hy => (hfspec y hy).2)
    have hRcard : R.card ≤ 4 := by
      rw [hRdef]
      calc F.roots.toFinset.card ≤ F.roots.card := Multiset.toFinset_card_le _
        _ ≤ F.natDegree := Polynomial.card_roots' F
        _ ≤ (critN a b).natDegree := by rw [hFdef]; exact Polynomial.natDegree_map_le
        _ ≤ 4 := natDegree_critN_le_four a b
    omega

end Work.LinnikBurgess.lfSmall
