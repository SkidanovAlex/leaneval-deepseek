import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseBoxFock.PCFU.latticeTailFiberLe
import Submission.Work.BoseBoxFock.PCFU.latticeTailFiberSum
import Submission.Work.BoseBoxFock.SumRangeInvSqLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.latticeTailNSqBound`

The tail of the lattice sum of `(‖m‖²)^{-N}`: for every `ρ ≥ 1` and every finite set `u` of
lattice indices `m : Fin 3 → ℤ`,

    ∑_{d ∈ u, ρ² < nSq d} ((nSq d : ℝ)^N)⁻¹ ≤ C · (ρ ^ (2N-3))⁻¹     (N ≥ 2),

where `nSq d = ∑ i, (d i).natAbs ^ 2` is the squared Euclidean norm of `d`.

The sum is split at the sup-norm `K d = max_i |d i|` (with `⌊ρ⌋` as the cut):

* the part `K d ≤ ⌊ρ⌋` lies in the box `[-⌊ρ⌋,⌊ρ⌋]³`, which has `(2⌊ρ⌋+1)³ ≤ 27 ρ³` points,
  and every surviving summand is at most `(ρ²)^{-N} = (ρ^{2N})⁻¹`, so this part is at most
  `27 (ρ^{2N-3})⁻¹`;
* the part `K d > ⌊ρ⌋` is fibre-wise dominated by the sup-norm shells: a point of the shell
  `{K d = j}` has `nSq d ≥ j²` and the shell has at most `24 j² + 2` points (`ShellCard`), so
  the tail is bounded by `∑_{j > ⌊ρ⌋} (24 j² + 2) j^{-2N} ≲ (⌊ρ⌋+1)^{3-2N} ≲ ρ^{3-2N}`.
-/

namespace Work.BoseBoxFock.PCFU

open Finset

noncomputable section

/-! ## Elementary lattice facts -/

/-- The square of the sup-norm `K` is at most the squared Euclidean norm `nSq`. -/
lemma K_sq_le_nSq (m : Fin 3 → ℤ) : (K m) ^ 2 ≤ nSq m := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3))
    ⟨0, Finset.mem_univ 0⟩ (fun i => (m i).natAbs)
  rw [K, hi, nSq]
  exact Finset.single_le_sum (f := fun j : Fin 3 => (m j).natAbs ^ 2)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

/-- `K m ≤ R` puts `m` in the box `[-R,R]³`. -/
lemma mem_box_of_K_le {m : Fin 3 → ℤ} {R : ℕ} (h : K m ≤ R) : m ∈ box R :=
  (mem_box_iff R m).mpr (fun i => le_trans (K_spec m i) h)

/-! ## The main theorem -/

theorem latticeTailNSqBound (N : ℕ) (hN : 2 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 1 ≤ ρ → ∀ u : Finset (Fin 3 → ℤ),
      ∑ d ∈ u.filter (fun d => ρ ^ 2 < (Work.BoseBoxFock.nSq d : ℝ)),
          ((Work.BoseBoxFock.nSq d : ℝ) ^ N)⁻¹
        ≤ C * ((ρ ^ (2 * N - 3))⁻¹) := by
  refine ⟨200 * (2 : ℝ) ^ (2 * N), by positivity, ?_⟩
  intro ρ hρ u
  have hρ0 : (0 : ℝ) < ρ := by linarith
  -- write `ρ` as `R + θ` with `R = ⌊ρ⌋`
  obtain ⟨R, hRle, hρlt⟩ : ∃ R : ℕ, (R : ℝ) ≤ ρ ∧ ρ < (R : ℝ) + 1 :=
    ⟨Nat.floor ρ, Nat.floor_le (le_trans zero_le_one hρ),
      by simpa using Nat.lt_floor_add_one ρ⟩
  have hR1 : 1 ≤ R := by
    rcases Nat.eq_zero_or_pos R with h | h
    · exfalso
      rw [h] at hρlt
      push_cast at hρlt
      linarith
    · exact h
  -- the filtered set and its two halves
  set v : Finset (Fin 3 → ℤ) := u.filter (fun d => ρ ^ 2 < (nSq d : ℝ)) with hvdef
  have hvsub : v ⊆ u := by
    intro d hd
    rw [hvdef, Finset.mem_filter] at hd
    exact hd.1
  have hvmem : ∀ d ∈ v, ρ ^ 2 < (nSq d : ℝ) := by
    intro d hd
    rw [hvdef, Finset.mem_filter] at hd
    exact hd.2
  set vA : Finset (Fin 3 → ℤ) := v.filter (fun d => K d ≤ R) with hAdef
  set vB : Finset (Fin 3 → ℤ) := v.filter (fun d => ¬ K d ≤ R) with hBdef
  have hvAsub : vA ⊆ v := by
    intro d hd
    rw [hAdef, Finset.mem_filter] at hd
    exact hd.1
  have hvBsub : vB ⊆ v := by
    intro d hd
    rw [hBdef, Finset.mem_filter] at hd
    exact hd.1
  have hsplit :
      ∑ d ∈ vA, ((nSq d : ℝ) ^ N)⁻¹ + ∑ d ∈ vB, ((nSq d : ℝ) ^ N)⁻¹
        = ∑ d ∈ v, ((nSq d : ℝ) ^ N)⁻¹ :=
    Finset.sum_filter_add_sum_filter_not v (fun d => K d ≤ R) _
  -- ## Part A: the bounded part `K d ≤ ⌊ρ⌋`
  have hA : ∑ d ∈ vA, ((nSq d : ℝ) ^ N)⁻¹ ≤ 27 * (ρ ^ (2 * N - 3))⁻¹ := by
    have hsub : vA ⊆ box R := by
      intro d hd
      rw [hAdef, Finset.mem_filter] at hd
      exact mem_box_of_K_le hd.2
    have hcard : (vA.card : ℝ) ≤ (2 * (R : ℝ) + 1) ^ 3 := by
      have h1 : vA.card ≤ (box R).card := Finset.card_le_card hsub
      rw [shellCard_box_card] at h1
      have h1' : ((vA.card : ℕ) : ℝ) ≤ (((2 * R + 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h1'
      exact h1'
    have hpoint : ∀ d ∈ vA, ((nSq d : ℝ) ^ N)⁻¹ ≤ (ρ ^ (2 * N))⁻¹ := by
      intro d hd
      have hgt : ρ ^ 2 < (nSq d : ℝ) := hvmem d (hvAsub hd)
      have hle : (ρ ^ 2) ≤ (nSq d : ℝ) := le_of_lt hgt
      have hpow : ρ ^ (2 * N) ≤ ((nSq d : ℝ)) ^ N := by
        rw [pow_mul]
        exact pow_le_pow_left₀ (by positivity) hle N
      exact inv_anti₀ (by positivity) hpow
    calc ∑ d ∈ vA, ((nSq d : ℝ) ^ N)⁻¹
        ≤ ∑ _d ∈ vA, (ρ ^ (2 * N))⁻¹ := Finset.sum_le_sum hpoint
      _ = (vA.card : ℝ) * (ρ ^ (2 * N))⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (R : ℝ) + 1) ^ 3 * (ρ ^ (2 * N))⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ 27 * (ρ ^ (2 * N - 3))⁻¹ := by
          have hR1' : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1
          have h3 : 2 * (R : ℝ) + 1 ≤ 3 * ρ := by linarith
          have h4 : (2 * (R : ℝ) + 1) ^ 3 ≤ 27 * ρ ^ 3 := by
            have h5 : (2 * (R : ℝ) + 1) ^ 3 ≤ (3 * ρ) ^ 3 :=
              pow_le_pow_left₀ (by positivity) h3 3
            have h6 : (3 * ρ) ^ 3 = 27 * ρ ^ 3 := by ring
            linarith [h5, h6.ge]
          have h7 : ρ ^ 3 * (ρ ^ (2 * N))⁻¹ = (ρ ^ (2 * N - 3))⁻¹ := by
            have h2 : ρ ^ (2 * N) = ρ ^ (2 * N - 3) * ρ ^ 3 := by
              rw [← pow_add]
              congr 1
              omega
            rw [h2, mul_inv, ← mul_assoc, mul_comm (ρ ^ 3) ((ρ ^ (2 * N - 3))⁻¹), mul_assoc,
              mul_inv_cancel₀ (pow_ne_zero 3 hρ0.ne'), mul_one]
          calc (2 * (R : ℝ) + 1) ^ 3 * (ρ ^ (2 * N))⁻¹
              ≤ 27 * ρ ^ 3 * (ρ ^ (2 * N))⁻¹ :=
                mul_le_mul_of_nonneg_right h4 (by positivity)
            _ = 27 * (ρ ^ (2 * N - 3))⁻¹ := by rw [mul_assoc, h7]
  -- ## Part B: the tail `K d > ⌊ρ⌋`, fibre-wise
  have hB : ∑ d ∈ vB, ((nSq d : ℝ) ^ N)⁻¹ ≤ 52 * (2 : ℝ) ^ (2 * N - 3) * (ρ ^ (2 * N - 3))⁻¹ := by
    set M : ℕ := u.sup K with hMdef
    have hKmaps : ∀ d ∈ vB, K d ∈ Finset.range (M + 1) := by
      intro d hd
      rw [Finset.mem_range]
      refine Nat.lt_succ_of_le ?_
      rw [hMdef]
      exact Finset.le_sup (hvsub (hvBsub hd))
    have hfib : ∀ j ∈ Finset.range (M + 1),
        ∑ d ∈ vB.filter (fun d => K d = j), ((nSq d : ℝ) ^ N)⁻¹
          ≤ (if R + 1 ≤ j then (24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) ^ (2 * N))⁻¹ else 0) := by
      intro j _
      by_cases hRj : R + 1 ≤ j
      · rw [if_pos hRj]
        have hj1 : 1 ≤ j := by omega
        have hsubset : vB.filter (fun d => K d = j) ⊆ (box M).filter (fun d => K d = j) := by
          intro d hd
          rw [Finset.mem_filter] at hd ⊢
          have hdu : d ∈ u := hvsub (hvBsub hd.1)
          have hKM : K d ≤ M := by rw [hMdef]; exact Finset.le_sup hdu
          exact ⟨(mem_box_iff M d).mpr (fun i => le_trans (K_spec d i) hKM), hd.2⟩
        calc ∑ d ∈ vB.filter (fun d => K d = j), ((nSq d : ℝ) ^ N)⁻¹
            ≤ ∑ d ∈ (box M).filter (fun d => K d = j), ((nSq d : ℝ) ^ N)⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ => by positivity)
          _ ≤ (24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) ^ (2 * N))⁻¹ :=
              latticeTailFiberLe N M j hN hj1
      · rw [if_neg hRj]
        have hfalse : ∀ d, d ∉ vB.filter (fun d => K d = j) := by
          intro d hd
          rw [Finset.mem_filter] at hd
          have hdvB : d ∈ vB := hd.1
          rw [hBdef, Finset.mem_filter] at hdvB
          have hlt : R < K d := not_le.mp hdvB.2
          rw [hd.2] at hlt
          omega
        exact le_of_eq (Finset.sum_eq_zero (fun d hd => absurd hd (hfalse d)))
    have hset : (Finset.range (M + 1)).filter (fun j => R + 1 ≤ j) = Finset.Ico (R + 1) (M + 1) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    calc ∑ d ∈ vB, ((nSq d : ℝ) ^ N)⁻¹
        = ∑ j ∈ Finset.range (M + 1), ∑ d ∈ vB.filter (fun d => K d = j), ((nSq d : ℝ) ^ N)⁻¹ :=
          (Finset.sum_fiberwise_of_maps_to hKmaps _).symm
      _ ≤ ∑ j ∈ Finset.range (M + 1),
            (if R + 1 ≤ j then (24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) ^ (2 * N))⁻¹ else 0) :=
          Finset.sum_le_sum hfib
      _ = ∑ j ∈ Finset.Ico (R + 1) (M + 1), (24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) ^ (2 * N))⁻¹ := by
          rw [← Finset.sum_filter, hset]
      _ ≤ 52 * (((R : ℝ) + 1) ^ (2 * N - 3))⁻¹ :=
          latticeTailFiberSum N R M hN hR1
      _ ≤ 52 * (2 : ℝ) ^ (2 * N - 3) * (ρ ^ (2 * N - 3))⁻¹ := by
          have hhalf : ρ / 2 ≤ (R : ℝ) + 1 := by linarith
          have hpow : (ρ / 2) ^ (2 * N - 3) ≤ ((R : ℝ) + 1) ^ (2 * N - 3) :=
            pow_le_pow_left₀ (by positivity) hhalf _
          have hinv : (((R : ℝ) + 1) ^ (2 * N - 3))⁻¹ ≤ ((ρ / 2) ^ (2 * N - 3))⁻¹ :=
            inv_anti₀ (by positivity) hpow
          have hdiv : ((ρ / 2) ^ (2 * N - 3))⁻¹ = (2 : ℝ) ^ (2 * N - 3) * (ρ ^ (2 * N - 3))⁻¹ := by
            rw [div_pow, inv_div, div_eq_mul_inv]
          calc 52 * (((R : ℝ) + 1) ^ (2 * N - 3))⁻¹
              ≤ 52 * ((ρ / 2) ^ (2 * N - 3))⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
            _ = 52 * (2 : ℝ) ^ (2 * N - 3) * (ρ ^ (2 * N - 3))⁻¹ := by rw [hdiv]; ring
  -- ## Combining the two parts
  have hP : (0 : ℝ) ≤ (ρ ^ (2 * N - 3))⁻¹ := by positivity
  have hconst : 27 + 52 * (2 : ℝ) ^ (2 * N - 3) ≤ 200 * (2 : ℝ) ^ (2 * N) := by
    have h2N : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * N) := one_le_pow₀ (by norm_num)
    have hle : (2 : ℝ) ^ (2 * N - 3) ≤ (2 : ℝ) ^ (2 * N) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [h2N, hle]
  have hsum := add_le_add hA hB
  have hone : 27 * (ρ ^ (2 * N - 3))⁻¹ + 52 * (2 : ℝ) ^ (2 * N - 3) * (ρ ^ (2 * N - 3))⁻¹
      ≤ 200 * (2 : ℝ) ^ (2 * N) * (ρ ^ (2 * N - 3))⁻¹ := by
    have h2 := mul_le_mul_of_nonneg_right hconst hP
    linarith [h2]
  rw [← hsplit]
  linarith [hsum, hone]

end

end Work.BoseBoxFock.PCFU
