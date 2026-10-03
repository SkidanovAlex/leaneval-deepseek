import Mathlib
import Submission.Work.Peluse.Ulower.gap_localise
import Submission.Work.Peluse.Ulower.ss_autocorr_bridge

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-!
# `Work.Peluse.Ulower.gap_transfer`

The window-localisation `gapLocalise f a Ns` (the translate `x ↦ f (x+a)` truncated to `symIcc Ns`)
changes the progression-average sum `progAvgSum N' q · = ∑_x ‖E_{m ∈ [N']} f (x + q m)‖` only by
the contribution of the progression windows that **straddle the boundary of the window**
`symIcc Ns = [-Ns, Ns]`.

For a shift `x`, the window `{x + q m : 1 ≤ m ≤ N'}` is either entirely inside `symIcc Ns`, entirely
outside it, or straddles it.  In the first case the progression average of `gapLocalise f a Ns` at
`x` equals that of `f` at `x + a`; in the second it vanishes; only straddling windows contribute,
and each contributes at most `1` while the straddling shifts `x` form at most `2 N' |q|` values
(two blocks of length `q (N'-1)`).  This is the requested bound `+ 2 (N' |q|)`.
-/

/-- The shifts at which the progression window `{x + q m : m ∈ [1,N']}` straddles the boundary of
`symIcc Ns`: two blocks, `[-Ns - q N', -Ns - q - 1]` (left boundary) and
`[Ns - q N' + 1, Ns - q]` (right boundary). -/
private def gapBad (Ns N' : ℕ) (q : ℤ) : Finset ℤ :=
  (Finset.Icc (-(Ns : ℤ) - q * (N' : ℤ)) (-(Ns : ℤ) - q - 1)) ∪
    (Finset.Icc ((Ns : ℤ) - q * (N' : ℤ) + 1) ((Ns : ℤ) - q))

/-- A counting bound for an interval of integers: `Icc a b` has at most `k` elements as soon as
`b + 1 - a ≤ k`. -/
private lemma card_Icc_int_le (a b : ℤ) (k : ℕ) (h : b + 1 - a ≤ (k : ℤ)) :
    (Finset.Icc a b).card ≤ k := by
  rw [Int.card_Icc]
  exact (Int.toNat_le_toNat h).trans_eq (Int.toNat_natCast k)

/-- The straddling shifts number at most `2 N' |q|`. -/
private lemma card_gapBad_le (Ns N' : ℕ) (q : ℤ) (hq : 1 ≤ q) :
    ((gapBad Ns N' q).card : ℝ) ≤ 2 * ((N' * q.natAbs : ℕ) : ℝ) := by
  have hq0 : (0 : ℤ) ≤ q := by omega
  have hcast : ((q.natAbs : ℕ) : ℤ) = q := by
    rw [Int.natCast_natAbs, abs_of_nonneg hq0]
  have hk : ((N' * q.natAbs : ℕ) : ℤ) = q * (N' : ℤ) := by
    rw [Nat.cast_mul, hcast]; ring
  have h1 : (Finset.Icc (-(Ns : ℤ) - q * (N' : ℤ)) (-(Ns : ℤ) - q - 1)).card
      ≤ N' * q.natAbs := by
    refine card_Icc_int_le _ _ _ ?_
    rw [hk]
    have he : (-(Ns : ℤ) - q - 1) + 1 - (-(Ns : ℤ) - q * (N' : ℤ))
        = q * (N' : ℤ) - q := by ring
    rw [he]; linarith
  have h2 : (Finset.Icc ((Ns : ℤ) - q * (N' : ℤ) + 1) ((Ns : ℤ) - q)).card
      ≤ N' * q.natAbs := by
    refine card_Icc_int_le _ _ _ ?_
    rw [hk]
    have he : ((Ns : ℤ) - q) + 1 - ((Ns : ℤ) - q * (N' : ℤ) + 1) = q * (N' : ℤ) - q := by
      ring
    rw [he]; linarith
  have hcard : (gapBad Ns N' q).card ≤ 2 * (N' * q.natAbs) := by
    rw [gapBad]
    calc _ ≤ _ + _ := Finset.card_union_le _ _
      _ ≤ N' * q.natAbs + N' * q.natAbs := add_le_add h1 h2
      _ = 2 * (N' * q.natAbs) := by ring
  calc ((gapBad Ns N' q).card : ℝ) ≤ ((2 * (N' * q.natAbs) : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = 2 * ((N' * q.natAbs : ℕ) : ℝ) := by push_cast; ring

/-- `progAvg` of a `1`-bounded function is `1`-bounded (the case `N' = 0` included). -/
private lemma norm_progAvg_le_one' {f : ℤ → ℂ} (hb : ∀ x : ℤ, ‖f x‖ ≤ 1) (N' : ℕ) (q : ℤ)
    (x : ℤ) : ‖progAvg N' q f x‖ ≤ 1 := by
  by_cases hN' : N' = 0
  · subst hN'
    simp [progAvg]
  · exact ss_progAvg_norm_le_one (Nat.one_le_iff_ne_zero.mpr hN') q hb x

/-- If the whole progression window at `x` lies in `symIcc Ns`, the progression average of the
localised function at `x` equals that of `f` at `x + a`. -/
private lemma progAvg_gapLocalise_of_all_mem {f : ℤ → ℂ} {a : ℤ} {Ns N' : ℕ} {q : ℤ} {x : ℤ}
    (h : ∀ m ∈ Finset.Icc 1 N', x + q * (m : ℤ) ∈ symIcc Ns) :
    progAvg N' q (gapLocalise f a Ns) x = progAvg N' q f (x + a) := by
  rw [progAvg, progAvg]
  congr 1
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [gapLocalise_apply_of_mem (h m hm)]
  congr 1
  ring

/-- If no point of the progression window at `x` lies in `symIcc Ns`, the progression average of
the localised function at `x` vanishes. -/
private lemma progAvg_gapLocalise_eq_zero_of_none_mem {f : ℤ → ℂ} {a : ℤ} {Ns N' : ℕ} {q : ℤ}
    {x : ℤ} (h : ∀ m ∈ Finset.Icc 1 N', x + q * (m : ℤ) ∉ symIcc Ns) :
    progAvg N' q (gapLocalise f a Ns) x = 0 := by
  rw [progAvg]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun m hm => ?_))
  rw [gapLocalise_apply_of_not_mem (h m hm)]

/-- A straddling shift is one of the two boundary blocks: the "mixed" shifts form a subset of
`gapBad Ns N' q`. -/
private lemma mem_gapBad_of_mixed (Ns N' : ℕ) (q : ℤ) (hq0 : 0 ≤ q) (x : ℤ)
    (h1 : ¬ ∀ m ∈ Finset.Icc 1 N', x + q * (m : ℤ) ∈ symIcc Ns)
    (h2 : ¬ ∀ m ∈ Finset.Icc 1 N', x + q * (m : ℤ) ∉ symIcc Ns) :
    x ∈ gapBad Ns N' q := by
  have hmem : ∀ y : ℤ, y ∈ symIcc Ns ↔ (-(Ns : ℤ) ≤ y ∧ y ≤ (Ns : ℤ)) := by
    intro y; simp [symIcc, Finset.mem_Icc]
  push_neg at h1 h2
  obtain ⟨m, hm, hmnb⟩ := h1
  obtain ⟨m', hm', hm'mem⟩ := h2
  have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hm2 : (m : ℤ) ≤ (N' : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hm).2
  have hm'1 : (1 : ℤ) ≤ (m' : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hm').1
  have hm'2 : (m' : ℤ) ≤ (N' : ℤ) := by exact_mod_cast (Finset.mem_Icc.mp hm').2
  have hqm_lo : q ≤ q * (m : ℤ) := by
    simpa using mul_le_mul_of_nonneg_left hm1 hq0
  have hqm_hi : q * (m : ℤ) ≤ q * (N' : ℤ) := mul_le_mul_of_nonneg_left hm2 hq0
  have hqm'_lo : q ≤ q * (m' : ℤ) := by
    simpa using mul_le_mul_of_nonneg_left hm'1 hq0
  have hqm'_hi : q * (m' : ℤ) ≤ q * (N' : ℤ) := mul_le_mul_of_nonneg_left hm'2 hq0
  obtain ⟨hm'lo, hm'hi⟩ := (hmem (x + q * (m' : ℤ))).mp hm'mem
  have hmnb' : x + q * (m : ℤ) < -(Ns : ℤ) ∨ (Ns : ℤ) < x + q * (m : ℤ) := by
    have h := (hmem (x + q * (m : ℤ))).not.mp hmnb
    rwa [not_and_or, not_le, not_le] at h
  have hleft : x + q < -(Ns : ℤ) ∨ (Ns : ℤ) < x + q * (N' : ℤ) := by
    rcases hmnb' with hl | hr
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hlow : -(Ns : ℤ) ≤ x + q * (N' : ℤ) := by linarith
  have hhigh : x + q ≤ (Ns : ℤ) := by linarith
  rw [gapBad, Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
  rcases hleft with hl | hr
  · exact Or.inl ⟨by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

theorem gap_transfer {f : ℤ → ℂ} {N₀ : ℕ}
    (hsupp : Work.Peluse.SupportIn f N₀) (hf : ∀ x : ℤ, ‖f x‖ ≤ 1)
    {N' : ℕ} {q : ℤ} (hq : 1 ≤ q) (a : ℤ) (Ns : ℕ) :
    Work.Peluse.progAvgSum N' q (Work.Peluse.Ulower.gapLocalise f a Ns) ≤
      Work.Peluse.progAvgSum N' q f + 2 * ((N' * q.natAbs : ℕ) : ℝ) := by
  classical
  have hq0 : (0 : ℤ) ≤ q := by omega
  have hg1 : ∀ x : ℤ, ‖gapLocalise f a Ns x‖ ≤ 1 := norm_gapLocalise_le_one hf a Ns
  -- Step 1: the pointwise bound with the indicator of the straddling set.
  have hpt : ∀ x : ℤ, ‖progAvg N' q (gapLocalise f a Ns) x‖ ≤
      ‖progAvg N' q f (x + a)‖ + (if x ∈ gapBad Ns N' q then (1 : ℝ) else 0) := by
    intro x
    by_cases hxB : x ∈ gapBad Ns N' q
    · rw [if_pos hxB]
      have h1 := norm_progAvg_le_one' hg1 N' q x
      linarith [norm_nonneg (progAvg N' q f (x + a))]
    · rw [if_neg hxB, add_zero]
      by_cases hall : ∀ m ∈ Finset.Icc 1 N', x + q * (m : ℤ) ∈ symIcc Ns
      · rw [progAvg_gapLocalise_of_all_mem hall]
      · by_cases hout : ∀ m ∈ Finset.Icc 1 N', x + q * (m : ℤ) ∉ symIcc Ns
        · rw [progAvg_gapLocalise_eq_zero_of_none_mem hout, norm_zero]
          positivity
        · exact absurd (mem_gapBad_of_mixed Ns N' q hq0 x hall hout) hxB
  -- Step 2: summability of the three families involved.
  have hsumA : Summable (fun x : ℤ => ‖progAvg N' q (gapLocalise f a Ns) x‖) := by
    refine summable_of_ne_finset_zero (s := symIcc (Ns + N' * q.natAbs)) (fun x hx => ?_)
    have hxA : Ns + N' * q.natAbs < x.natAbs :=
      not_le.mp (fun h => hx (mem_symIcc_iff.mpr h))
    rw [progAvg_supportIn' (supportIn_gapLocalise_self f a Ns) q x hxA, norm_zero]
  have hsumB : Summable (fun x : ℤ => ‖progAvg N' q f (x + a)‖) := by
    have hs := progAvg_supportIn' (N' := N') hsupp q
    refine summable_of_ne_finset_zero
      (s := (symIcc (N₀ + N' * q.natAbs)).image (fun y => y - a)) (fun x hx => ?_)
    have hxa : N₀ + N' * q.natAbs < (x + a).natAbs := by
      refine not_le.mp (fun hle => hx ?_)
      exact Finset.mem_image.mpr ⟨x + a, mem_symIcc_iff.mpr hle, by ring⟩
    rw [hs (x + a) hxa, norm_zero]
  have hsumI : Summable (fun x : ℤ => (if x ∈ gapBad Ns N' q then (1 : ℝ) else 0)) :=
    summable_of_ne_finset_zero (s := gapBad Ns N' q) (fun x hx => by simp [hx])
  -- Step 3: sum the pointwise bound.
  have hstep : progAvgSum N' q (gapLocalise f a Ns) ≤
      (∑' x : ℤ, ‖progAvg N' q f (x + a)‖) + ((gapBad Ns N' q).card : ℝ) := by
    rw [progAvgSum]
    calc (∑' x : ℤ, ‖progAvg N' q (gapLocalise f a Ns) x‖)
        ≤ ∑' x : ℤ, (‖progAvg N' q f (x + a)‖ +
            (if x ∈ gapBad Ns N' q then (1 : ℝ) else 0)) :=
          hsumA.tsum_le_tsum hpt (hsumB.add hsumI)
      _ = (∑' x : ℤ, ‖progAvg N' q f (x + a)‖) +
            ∑' x : ℤ, (if x ∈ gapBad Ns N' q then (1 : ℝ) else 0) :=
          hsumB.tsum_add hsumI
      _ = (∑' x : ℤ, ‖progAvg N' q f (x + a)‖) + ((gapBad Ns N' q).card : ℝ) := by
          congr 1
          rw [tsum_eq_sum (s := gapBad Ns N' q) (fun x hx => by simp [hx])]
          simp
  -- Step 4: the shift invariance and the counting bound.
  have hshift : (∑' x : ℤ, ‖progAvg N' q f (x + a)‖) = progAvgSum N' q f := by
    rw [progAvgSum]
    exact Equiv.tsum_eq (Equiv.addRight a) (fun y => ‖progAvg N' q f y‖)
  calc progAvgSum N' q (gapLocalise f a Ns)
      ≤ (∑' x : ℤ, ‖progAvg N' q f (x + a)‖) + ((gapBad Ns N' q).card : ℝ) := hstep
    _ = progAvgSum N' q f + ((gapBad Ns N' q).card : ℝ) := by rw [hshift]
    _ ≤ progAvgSum N' q f + 2 * ((N' * q.natAbs : ℕ) : ℝ) := by
        have hb := card_gapBad_le Ns N' q hq
        linarith

end

end Work.Peluse.Ulower
