import Mathlib
import Submission.Work.FIArea2.sol_set_lin_dioph

namespace Work.FIArea2

/-- Counting the integers of `[a,b]` lying in a single residue class mod `m` (equivalently, all
`x` with `m ∣ x - s`).  The shift `x ↦ (x-a).toNat / |m|` is strictly increasing on this set,
because two distinct members differ by a non-zero multiple of `m`, hence by at least `|m|`; its
values lie in `[0, (b-a)/|m|]`, which has `(b-a)/|m| + 1` elements. -/
lemma card_Icc_filter_dvd_sub_le (a b s m : ℤ) (hm : m ≠ 0) :
    ((Finset.Icc a b).filter (fun x => m ∣ x - s)).card ≤ (b - a).natAbs / m.natAbs + 1 := by
  have hMpos : 0 < m.natAbs := Int.natAbs_pos.mpr hm
  rcases le_or_gt a b with hab | hba
  · have hlab : (0 : ℤ) ≤ b - a := by linarith
    have hLnat : (b - a).natAbs = (b - a).toNat := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.natAbs_of_nonneg hlab, Int.toNat_of_nonneg hlab]
    rw [hLnat]
    have hstep : ∀ x x' : ℤ, x ∈ (Finset.Icc a b).filter (fun x => m ∣ x - s) →
        x' ∈ (Finset.Icc a b).filter (fun x => m ∣ x - s) → x < x' →
        (x - a).toNat / m.natAbs < (x' - a).toNat / m.natAbs := by
      intro x x' hx hx' hlt
      simp only [Finset.mem_filter, Finset.mem_Icc] at hx hx'
      have hpos : (0 : ℤ) < x' - x := by linarith
      have hdiv : m ∣ x' - x := by
        have h := dvd_sub hx'.2 hx.2
        have he : (x' - s) - (x - s) = x' - x := by ring
        rwa [he] at h
      obtain ⟨k, hk⟩ := (Int.natAbs_dvd (a := m) (b := x' - x)).mpr hdiv
      have hkpos : 0 < k := by
        have hmain : (0 : ℤ) < (m.natAbs : ℤ) * k := by rw [← hk]; exact hpos
        exact pos_of_mul_pos_right hmain (by positivity)
      have hstep_le : m.natAbs ≤ (x' - x).toNat := by
        rw [hk, Int.toNat_mul (by positivity) (le_of_lt hkpos), Int.toNat_natCast]
        have hk1 : 1 ≤ k.toNat := by
          rw [Nat.one_le_iff_ne_zero]
          intro h0
          rw [Int.toNat_eq_zero] at h0
          omega
        calc m.natAbs = m.natAbs * 1 := (mul_one _).symm
          _ ≤ m.natAbs * k.toNat := Nat.mul_le_mul_left _ hk1
      have hadd : (x' - a).toNat = (x - a).toNat + (x' - x).toNat := by
        have h1 : (0 : ℤ) ≤ x - a := by linarith [hx.1.1]
        have h2 : (0 : ℤ) ≤ x' - x := le_of_lt hpos
        have he : x' - a = (x - a) + (x' - x) := by ring
        rw [he, Int.toNat_add h1 h2]
      have key : ((x - a).toNat + m.natAbs) / m.natAbs ≤
          ((x - a).toNat + (x' - x).toNat) / m.natAbs :=
        Nat.div_le_div_right (Nat.add_le_add_left hstep_le _)
      have key2 : ((x - a).toNat + m.natAbs) / m.natAbs = (x - a).toNat / m.natAbs + 1 := by
        nth_rewrite 1 [show m.natAbs = 1 * m.natAbs from (one_mul _).symm]
        rw [Nat.add_mul_div_right _ _ hMpos]
      rw [hadd]
      omega
    have hmaps : Set.MapsTo (fun x : ℤ => (x - a).toNat / m.natAbs)
        ↑((Finset.Icc a b).filter (fun x => m ∣ x - s))
        ↑(Finset.Icc 0 ((b - a).toNat / m.natAbs)) := by
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
      exact ⟨Nat.zero_le _, Nat.div_le_div_right (Int.toNat_le_toNat (by linarith [hx.1.2]))⟩
    have hinj : Set.InjOn (fun x : ℤ => (x - a).toNat / m.natAbs)
        ↑((Finset.Icc a b).filter (fun x => m ∣ x - s)) := by
      intro x hx x' hx' heq
      rcases lt_trichotomy x x' with hlt | heq' | hgt
      · exact absurd heq (ne_of_lt (hstep x x' hx hx' hlt))
      · exact heq'
      · exact absurd heq.symm (ne_of_lt (hstep x' x hx' hx hgt))
    have hcard : (Finset.Icc 0 ((b - a).toNat / m.natAbs)).card ≤
        (b - a).toNat / m.natAbs + 1 := by
      rw [Nat.card_Icc, Nat.sub_zero]
    exact le_trans (Finset.card_le_card_of_injOn (fun x : ℤ => (x - a).toNat / m.natAbs)
      hmaps hinj) hcard
  · have hempty : Finset.Icc a b = ∅ := Finset.Icc_eq_empty_iff.mpr (not_le.mpr hba)
    rw [hempty, Finset.filter_empty]
    simp

/-- **The `s`-count of *FI* §9 (display (9.5)).**  Fix `(r₁,r₂) ≠ (0,0)` and `Δ`.  The integer
solutions of `r₁s₂ − r₂s₁ = Δ` form a single arithmetic progression with step `(r₁/ρ, r₂/ρ)`,
`ρ = (r₁,r₂)` (`Work.FIArea2.sol_set_lin_dioph`), so the number of them with `s₁ ∈ [a,b]` and
`s₂ ∈ [c,d]` is at most `1 + ρ·(b−a+1)/|r₁|`.  Stated without division: the count times `|r₁|`
is at most `|r₁| + ρ·(b−a+1)`.  This is what replaces the paper's per-`Δ` claim *"given `r₁,r₂`
and any value of `Δ` the number of ordered pairs `s₁,s₂` which give `z₁,z₂` in `B` satisfying
`r₁s₂ − r₂s₁ = Δ` is `O(ϑ^{-1}(r₁,r₂))`"*: the count is the chord of the box divided by the step
of the progression, so it needs the box's geometry (the sector) — see `NOTES.md` §22. -/
theorem card_sol_lin_dioph_le1 (r1 r2 Δ a b c d : ℤ) (hr1 : r1 ≠ 0) :
    (((Finset.Icc a b).product (Finset.Icc c d)).filter
        (fun p : ℤ × ℤ => r1 * p.2 - r2 * p.1 = Δ)).card * r1.natAbs
      ≤ r1.natAbs + (Int.gcd r1 r2) * (b - a + 1).natAbs := by
  set ρ : ℕ := r1.gcd r2 with hρ
  set G : ℤ := (ρ : ℤ) with hG
  set m : ℤ := r1 / G with hm
  have hm_eq : m = r1 / (r1.gcd r2 : ℤ) := by rw [hm, hG, hρ]
  have hGdvd : G ∣ r1 := by rw [hG, hρ]; exact Int.gcd_dvd_left r1 r2
  have hmul : m * G = r1 := by rw [hm]; exact Int.ediv_mul_cancel hGdvd
  have hmne : m ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact hr1 hmul.symm
  have hr1nat : r1.natAbs = m.natAbs * ρ := by
    rw [← hmul, Int.natAbs_mul, hG, Int.natAbs_natCast]
  have h0 : (r1, r2) ≠ (0, 0) := fun h => hr1 (by simpa using congrArg Prod.fst h)
  set S := ((Finset.Icc a b).product (Finset.Icc c d)).filter
    (fun p : ℤ × ℤ => r1 * p.2 - r2 * p.1 = Δ) with hS
  set T := (Finset.Icc a b).filter
    (fun x : ℤ => ∃ y ∈ Finset.Icc c d, r1 * y - r2 * x = Δ) with hT
  have hST : S.card ≤ T.card := by
    refine Finset.card_le_card_of_injOn (fun p : ℤ × ℤ => p.1) ?_ ?_
    · intro p hp
      rw [hS] at hp
      obtain ⟨hpI, hpeq⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpa, hpb⟩ := Finset.mem_product.mp hpI
      exact Finset.mem_filter.mpr ⟨hpa, ⟨p.2, hpb, hpeq⟩⟩
    · intro p hp q hq heq
      rw [hS] at hp hq
      obtain ⟨_, hpeq⟩ := Finset.mem_filter.mp hp
      obtain ⟨_, hqeq⟩ := Finset.mem_filter.mp hq
      have h1 : p.1 = q.1 := heq
      refine Prod.ext h1 ?_
      refine mul_left_cancel₀ hr1 ?_
      rw [h1] at hpeq
      linarith
  have hTbound : T.card * m.natAbs ≤ m.natAbs + (b - a + 1).natAbs := by
    rcases le_or_gt a b with hab | hba
    · rcases Finset.eq_empty_or_nonempty T with hTe | hTne
      · rw [hTe]; simp
      · obtain ⟨s₁, hs₁⟩ := hTne
        rw [hT] at hs₁
        obtain ⟨hs₁I, s₂, hs₂I, hs₂eq⟩ := Finset.mem_filter.mp hs₁
        have hsub : T ⊆ (Finset.Icc a b).filter (fun x => m ∣ x - s₁) := by
          intro x hx
          rw [hT] at hx
          obtain ⟨hxI, y, hyI, hyeq⟩ := Finset.mem_filter.mp hx
          refine Finset.mem_filter.mpr ⟨hxI, ?_⟩
          obtain ⟨t, ht1, _⟩ :=
            (sol_set_lin_dioph r1 r2 Δ s₁ s₂ h0 hs₂eq x y).mp hyeq
          rw [← hm_eq] at ht1
          exact ⟨t, by rw [ht1]; ring⟩
        have hcard : T.card ≤ (b - a).natAbs / m.natAbs + 1 :=
          le_trans (Finset.card_le_card hsub) (card_Icc_filter_dvd_sub_le a b s₁ m hmne)
        have hmul2 : T.card * m.natAbs ≤ (b - a).natAbs + m.natAbs := by
          calc T.card * m.natAbs
              ≤ ((b - a).natAbs / m.natAbs + 1) * m.natAbs := Nat.mul_le_mul_right _ hcard
            _ = (b - a).natAbs / m.natAbs * m.natAbs + m.natAbs := by ring
            _ ≤ (b - a).natAbs + m.natAbs := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
        have hL1 : (b - a).natAbs = (b - a).toNat := by
          apply Nat.cast_injective (R := ℤ)
          rw [Int.natAbs_of_nonneg (by linarith : (0 : ℤ) ≤ b - a),
            Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ b - a)]
        have hL2 : (b - a + 1).natAbs = (b - a).toNat + 1 := by
          have hna : (b - a + 1).natAbs = (b - a + 1).toNat := by
            apply Nat.cast_injective (R := ℤ)
            rw [Int.natAbs_of_nonneg (by linarith : (0 : ℤ) ≤ b - a + 1),
              Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ b - a + 1)]
          rw [hna, Int.toNat_add (by linarith : (0 : ℤ) ≤ b - a) (by norm_num : (0 : ℤ) ≤ 1),
            Int.toNat_one]
        refine le_trans hmul2 ?_
        rw [hL1, hL2]
        omega
    · have hTe : T = ∅ := by
        rw [hT, Finset.Icc_eq_empty_iff.mpr (not_le.mpr hba), Finset.filter_empty]
      rw [hTe]; simp
  calc S.card * r1.natAbs
      = S.card * (m.natAbs * ρ) := by rw [hr1nat]
    _ = (S.card * m.natAbs) * ρ := by ring
    _ ≤ (T.card * m.natAbs) * ρ := Nat.mul_le_mul_right ρ (Nat.mul_le_mul_right m.natAbs hST)
    _ ≤ (m.natAbs + (b - a + 1).natAbs) * ρ := Nat.mul_le_mul_right ρ hTbound
    _ = m.natAbs * ρ + (b - a + 1).natAbs * ρ := Nat.add_mul _ _ _
    _ = r1.natAbs + ρ * (b - a + 1).natAbs := by rw [← hr1nat]; ring

end Work.FIArea2
