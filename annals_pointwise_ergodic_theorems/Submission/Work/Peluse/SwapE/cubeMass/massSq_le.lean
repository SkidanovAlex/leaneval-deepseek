import Mathlib
import Submission.Work.Peluse.SwapE.cubeMass.Defs
import Submission.Work.Peluse.SwapE.cubeMassRaw_eq_zero

/-!
# `cubeMass` — the mean square of the cube mass is bounded by the window ratio

The mean square of the cube mass over the slot box,
`massSq d H M N f = (∑_{n ∈ massBox d H M} ‖boxMass d (symIcc N) f n‖²) / (4HM+1)^d`,
is at most `min (4N+1) (4HM+1) / (4HM+1)`.

Two elementary facts give this.

* Each cube mass has modulus at most `1` (`norm_boxMass_le`): in
  `boxMass d S f n = |S|⁻¹ ∑_x ∏_ω C^{|ω|} f (x + ω·n)` the `ω ≡ false` factor is `f x`, so the
  integrand is supported in `S = symIcc N`, each factor has modulus `≤ 1`, and the normalising
  constant is `|S|⁻¹`.
* The cube mass of a slot value `n` with a coordinate of modulus `> 2N` vanishes
  (`cubeMassRaw_eq_zero`), because the corners `ω ≡ false` and `ω` the singleton at the slot
  force `x ∈ symIcc N` and `x + n k ∈ symIcc N`, whence `|n k| ≤ 2N`.

Hence only the slot values whose coordinates all lie in the box `[-2N,2N]` contribute; their number
is at most `min (4N+1) (4HM+1) · (4HM+1)^(d-1)`, and dividing by `(4HM+1)^d` gives the claim.
-/

namespace Work.Peluse.SwapE.cubeMass

open scoped BigOperators

noncomputable section

open Work.Peluse

/-! ## Elementary helpers -/

private lemma inv_mul_self_le_one (n : ℕ) : ((n : ℝ))⁻¹ * (n : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr h.ne')]

/-- Membership in the symmetric interval is a size condition: `x ∈ symIcc N ↔ x.natAbs ≤ N`. -/
private lemma mem_symIcc_natAbs {N : ℕ} {x : ℤ} :
    x ∈ Work.Peluse.symIcc N ↔ x.natAbs ≤ N := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : ((x.natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by
      rw [Int.natCast_natAbs]; exact abs_le.mpr ⟨h1, h2⟩
    exact_mod_cast h3
  · intro h
    have h3 : (|x| : ℤ) ≤ (N : ℤ) := by
      rw [← Int.natCast_natAbs]; exact_mod_cast h
    exact abs_le.mp h3

private lemma norm_star_iterate (n : ℕ) (z : ℂ) : ‖(star^[n]) z‖ = ‖z‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', norm_star, ih]

/-- A cube term is a product of `2 ^ d` terms of modulus at most `1`, hence has modulus at most
`1`. -/
private lemma norm_cubeTerm_le {d : ℕ} {f : ℤ → ℂ} (hf : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (n h' : Fin d → ℤ) (x : ℤ) :
    ‖∏ ω : Fin d → Bool,
        (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift n h' ω))‖ ≤ 1 := by
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun ω _ => norm_nonneg _) (fun ω _ => ?_)
  rw [norm_star_iterate]
  exact hf _

/-- For fixed increments the sum over the lower corner `x` of the cube term is bounded by `|S|`:
the `ω = 0` corner is `x` itself, so the integrand is supported in `S`. -/
private lemma norm_tsum_cubeTerm_le {d : ℕ} {S : Finset ℤ} {f : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsupp : ∀ x : ℤ, x ∉ S → f x = 0) (n : Fin d → ℤ) :
    ‖∑' x : ℤ, ∏ ω : Fin d → Bool,
      (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift n (0 : Fin d → ℤ) ω))‖
      ≤ (S.card : ℝ) := by
  have hvanish : ∀ x : ℤ, x ∉ S → (∏ ω : Fin d → Bool,
      (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift n (0 : Fin d → ℤ) ω))) = 0 := by
    intro x hx
    refine Finset.prod_eq_zero (Finset.mem_univ (fun _ : Fin d => false)) ?_
    have hw : Work.Peluse.weight (fun _ : Fin d => false) = 0 := by simp [Work.Peluse.weight]
    have hc : Work.Peluse.cornerShift n (0 : Fin d → ℤ) (fun _ : Fin d => false) = 0 := by
      simp [Work.Peluse.cornerShift]
    rw [hw, hc, Function.iterate_zero_apply]
    simpa using hsupp x hx
  rw [tsum_eq_sum (s := S) hvanish]
  calc ‖∑ x ∈ S, ∏ ω : Fin d → Bool,
        (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift n (0 : Fin d → ℤ) ω))‖
      ≤ ∑ x ∈ S, ‖∏ ω : Fin d → Bool,
          (star^[Work.Peluse.weight ω])
            (f (x + Work.Peluse.cornerShift n (0 : Fin d → ℤ) ω))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x ∈ S, (1:ℝ) :=
        Finset.sum_le_sum (fun x _ => norm_cubeTerm_le hf n 0 x)
    _ = (S.card : ℝ) := by simp

/-- The cube mass of a `1`-bounded function supported in `symIcc N` has modulus at most `1`. -/
private lemma norm_boxMass_le {d N : ℕ} {f : ℤ → ℂ}
    (hsupp : Work.Peluse.SupportIn f N) (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (n : Fin d → ℤ) :
    ‖Work.Peluse.SwapE.boxMass d (Work.Peluse.symIcc N) f n‖ ≤ 1 := by
  have hsuppS : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0 := fun x hx =>
    hsupp x (by rw [← not_le]; exact fun h => hx (mem_symIcc_natAbs.mpr h))
  unfold Work.Peluse.SwapE.boxMass
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_tsum_cubeTerm_le hf hsuppS n)
    (inv_nonneg.mpr (Nat.cast_nonneg _))) (inv_mul_self_le_one _)

/-- The cube mass of a slot value with a coordinate of modulus `> 2N` vanishes. -/
private lemma boxMass_eq_zero_of_notMem {d N : ℕ} {f : ℤ → ℂ} (hf : Work.Peluse.SupportIn f N)
    (n : Fin d → ℤ) (i : Fin d) (h : 2 * N < (n i).natAbs) :
    Work.Peluse.SwapE.boxMass d (Work.Peluse.symIcc N) f n = 0 := by
  rw [Work.Peluse.SwapE.boxMass_eq, Work.Peluse.SwapE.cubeMassRaw_eq_zero hf n i h, mul_zero]

/-- `#(symIcc L) = 2L + 1`. -/
private lemma card_symIcc (L : ℕ) : (Work.Peluse.symIcc L).card = 2 * L + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h : ((L : ℤ) + 1 - (-(L : ℤ))) = ((2 * L + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- `#([−2HM, 2HM]) = 4HM+1 = massBoxCard H M`. -/
private lemma card_Icc_massHalf (H M : ℕ) :
    (Finset.Icc (-(Work.Peluse.SwapE.massHalf H M)) (Work.Peluse.SwapE.massHalf H M)).card
      = Work.Peluse.SwapE.massBoxCard H M := by
  rw [Int.card_Icc]
  unfold Work.Peluse.SwapE.massHalf Work.Peluse.SwapE.massBoxCard
  have h : 2 * ((H * M : ℕ) : ℤ) + 1 - -(2 * ((H * M : ℕ) : ℤ))
      = ((4 * H * M + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [h, Int.toNat_natCast]

/-- `#(I^d) = #I ^ d` for a constant finite set `I`. -/
private lemma card_piFinset_const (d : ℕ) (I : Finset ℤ) :
    (Fintype.piFinset (fun _ : Fin d => I)).card = I.card ^ d := by
  rw [Fintype.card_piFinset]
  simp [Finset.prod_const, Finset.card_univ]

/-! ## The main bound -/

theorem massSq_le (d H M N : ℕ) (hd : 1 ≤ d) (f : ℤ → ℂ) (hf : Work.Peluse.SupportIn f N)
    (hf1 : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    Work.Peluse.SwapE.massSq d H M N f
      ≤ ((min (4 * N + 1) (Work.Peluse.SwapE.massBoxCard H M) : ℕ) : ℝ)
          / ((Work.Peluse.SwapE.massBoxCard H M : ℝ)) := by
  classical
  have hCard_pos : (0 : ℝ) < (Work.Peluse.SwapE.massBoxCard H M : ℝ) := by
    unfold Work.Peluse.SwapE.massBoxCard; positivity
  have hd1 : d = (d - 1) + 1 := by omega
  -- the box `J = [-2HM, 2HM]` and the truncated box `I = J ∩ [-2N,2N]`
  set J : Finset ℤ := Finset.Icc (-(Work.Peluse.SwapE.massHalf H M))
    (Work.Peluse.SwapE.massHalf H M) with hJ
  set I : Finset ℤ := J ∩ Work.Peluse.symIcc (2 * N) with hI
  set A : Finset (Fin d → ℤ) :=
    (Work.Peluse.SwapE.massBox d H M).filter
      (fun n => ∀ i : Fin d, n i ∈ Work.Peluse.symIcc (2 * N)) with hA
  have hJcard : J.card = Work.Peluse.SwapE.massBoxCard H M := by
    rw [hJ]; exact card_Icc_massHalf H M
  -- cardinal bound for the truncated box
  have hIcard_le : I.card ≤ min (4 * N + 1) (Work.Peluse.SwapE.massBoxCard H M) := by
    refine le_min ?_ ?_
    · calc I.card ≤ (Work.Peluse.symIcc (2 * N)).card := by
            rw [hI]; exact Finset.card_le_card Finset.inter_subset_right
        _ = 4 * N + 1 := by rw [card_symIcc]; ring
    · calc I.card ≤ J.card := by
            rw [hI]; exact Finset.card_le_card Finset.inter_subset_left
        _ = Work.Peluse.SwapE.massBoxCard H M := hJcard
  -- the surviving slot values sit in the pi-box of `I`
  have hA_sub : A ⊆ Fintype.piFinset (fun _ : Fin d => I) := by
    intro n hn
    rw [hA, Finset.mem_filter] at hn
    obtain ⟨hnbox, hnI⟩ := hn
    refine Fintype.mem_piFinset.mpr (fun i => ?_)
    have hnbox' : n ∈ Fintype.piFinset (fun _ : Fin d =>
        Finset.Icc (-(Work.Peluse.SwapE.massHalf H M)) (Work.Peluse.SwapE.massHalf H M)) := hnbox
    rw [hI, Finset.mem_inter]
    exact ⟨(Fintype.mem_piFinset.mp hnbox') i, hnI i⟩
  have hAcard : A.card ≤ I.card ^ d := by
    calc A.card ≤ (Fintype.piFinset (fun _ : Fin d => I)).card := Finset.card_le_card hA_sub
      _ = I.card ^ d := card_piFinset_const d I
  have hIpow : I.card ^ d
      ≤ min (4 * N + 1) (Work.Peluse.SwapE.massBoxCard H M)
          * (Work.Peluse.SwapE.massBoxCard H M) ^ (d - 1) := by
    have hIC : I.card ≤ Work.Peluse.SwapE.massBoxCard H M := by
      calc I.card ≤ J.card := by
            rw [hI]; exact Finset.card_le_card Finset.inter_subset_left
        _ = Work.Peluse.SwapE.massBoxCard H M := hJcard
    calc I.card ^ d = I.card ^ (d - 1) * I.card := by
          conv_lhs => rw [hd1]
          exact pow_succ _ _
      _ ≤ (Work.Peluse.SwapE.massBoxCard H M) ^ (d - 1) * I.card :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hIC (d - 1))
      _ ≤ (Work.Peluse.SwapE.massBoxCard H M) ^ (d - 1)
            * min (4 * N + 1) (Work.Peluse.SwapE.massBoxCard H M) :=
            Nat.mul_le_mul_left _ hIcard_le
      _ = min (4 * N + 1) (Work.Peluse.SwapE.massBoxCard H M)
            * (Work.Peluse.SwapE.massBoxCard H M) ^ (d - 1) := Nat.mul_comm _ _
  -- the sum over the box restricts to the surviving slot values
  have hsum_split : (∑ n ∈ Work.Peluse.SwapE.massBox d H M,
        ‖Work.Peluse.SwapE.boxMass d (Work.Peluse.symIcc N) f n‖ ^ 2)
      = ∑ n ∈ A, ‖Work.Peluse.SwapE.boxMass d (Work.Peluse.symIcc N) f n‖ ^ 2 := by
    rw [hA]
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro n hnbox hnnot
    have hnp : ¬ (∀ i : Fin d, n i ∈ Work.Peluse.symIcc (2 * N)) :=
      fun h => hnnot (Finset.mem_filter.mpr ⟨hnbox, h⟩)
    rw [not_forall] at hnp
    obtain ⟨i, hi⟩ := hnp
    have hlt : 2 * N < (n i).natAbs := by
      by_contra hc
      exact hi (mem_symIcc_natAbs.mpr (not_lt.mp hc))
    rw [boxMass_eq_zero_of_notMem hf n i hlt]
    simp
  -- the numerical bound on the sum
  have hsum_le : (∑ n ∈ Work.Peluse.SwapE.massBox d H M,
        ‖Work.Peluse.SwapE.boxMass d (Work.Peluse.symIcc N) f n‖ ^ 2)
      ≤ ((min (4 * N + 1) (Work.Peluse.SwapE.massBoxCard H M) : ℕ) : ℝ)
          * (Work.Peluse.SwapE.massBoxCard H M : ℝ) ^ (d - 1) := by
    have h1 : (∑ n ∈ Work.Peluse.SwapE.massBox d H M,
          ‖Work.Peluse.SwapE.boxMass d (Work.Peluse.symIcc N) f n‖ ^ 2) ≤ (A.card : ℝ) := by
      rw [hsum_split]
      calc (∑ n ∈ A, ‖Work.Peluse.SwapE.boxMass d (Work.Peluse.symIcc N) f n‖ ^ 2)
          ≤ ∑ _n ∈ A, (1 : ℝ) := by
            refine Finset.sum_le_sum (fun n _ => ?_)
            exact pow_le_one₀ (norm_nonneg _) (norm_boxMass_le hf hf1 n)
        _ = (A.card : ℝ) := by simp
    have h2 : (A.card : ℝ) ≤ ((min (4 * N + 1) (Work.Peluse.SwapE.massBoxCard H M) : ℕ) : ℝ)
        * (Work.Peluse.SwapE.massBoxCard H M : ℝ) ^ (d - 1) := by
      have h := le_trans hAcard hIpow
      have hcast : ((A.card : ℕ) : ℝ) ≤ ((min (4 * N + 1) (Work.Peluse.SwapE.massBoxCard H M)
          * (Work.Peluse.SwapE.massBoxCard H M) ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast h
      calc (A.card : ℝ) ≤ ((min (4 * N + 1) (Work.Peluse.SwapE.massBoxCard H M)
              * (Work.Peluse.SwapE.massBoxCard H M) ^ (d - 1) : ℕ) : ℝ) := hcast
        _ = ((min (4 * N + 1) (Work.Peluse.SwapE.massBoxCard H M) : ℕ) : ℝ)
              * (Work.Peluse.SwapE.massBoxCard H M : ℝ) ^ (d - 1) := by push_cast; ring
    exact le_trans h1 h2
  -- finish
  have hpow : (Work.Peluse.SwapE.massBoxCard H M : ℝ) ^ d
      = (Work.Peluse.SwapE.massBoxCard H M : ℝ) ^ (d - 1)
          * (Work.Peluse.SwapE.massBoxCard H M : ℝ) := by
    conv_lhs => rw [hd1]
    exact pow_succ _ _
  rw [Work.Peluse.SwapE.massSq, hpow]
  have h2 : ((min (4 * N + 1) (Work.Peluse.SwapE.massBoxCard H M) : ℕ) : ℝ)
        * (Work.Peluse.SwapE.massBoxCard H M : ℝ) ^ (d - 1)
        / ((Work.Peluse.SwapE.massBoxCard H M : ℝ) ^ (d - 1)
            * (Work.Peluse.SwapE.massBoxCard H M : ℝ))
      = ((min (4 * N + 1) (Work.Peluse.SwapE.massBoxCard H M) : ℕ) : ℝ)
          / (Work.Peluse.SwapE.massBoxCard H M : ℝ) := by
    have hb : (Work.Peluse.SwapE.massBoxCard H M : ℝ) ^ (d - 1) ≠ 0 :=
      pow_ne_zero _ hCard_pos.ne'
    have hc : (Work.Peluse.SwapE.massBoxCard H M : ℝ) ≠ 0 := hCard_pos.ne'
    field_simp
  exact le_trans (div_le_div_of_nonneg_right hsum_le (by positivity)) (le_of_eq h2)

end

end Work.Peluse.SwapE.cubeMass
