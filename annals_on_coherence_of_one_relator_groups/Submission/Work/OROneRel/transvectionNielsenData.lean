/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# Nielsen-transvection data for the torus relator `x ^ p * y ^ q`

The lemma `Work.OROneRel.transvectionNielsenData` produces, for a two-generator torus relator
`x ^ p * y ^ q` with `p, q ≥ 2` and a Bezout relation `p * m + q = ±1` (`m < 0`), a Nielsen
transformation `ψ` and weights `(t, c)` exhibiting the "no exponent sum is zero" data consumed by the
weighted Magnus--Moldavanskii step (`Work.OROneRel.magnusStepCase2_of_weight_count`).

The witness is the transvection `ψ : x ↦ x * y ^ m`, `y ↦ y` (with inverse `x ↦ x * y ^ (-m)`).  It
sends the relator to

  `(x * y ^ m) ^ p * y ^ q`,

whose reduced word is `(x * y ^ m) ^ (p - 1) * x * y ^ (m + q)` (`Work.OROneRel.tvWord p q m`); here
`p * m + q = ±1` and `m < 0` force `0 ≤ m + q`, so no truncation occurs.  The key numerical facts are

* the exponent sum in `y` is `p * m + q = ±1`, so `ψ r` is not a proper power (a proper power has
  exponent sums divisible by its exponent) and no exponent sum vanishes;
* with `t = x` and `c = (1, -p * (p * m + q))` one has `cohom c (ψ r) = p + (p * m + q) * c y = 0`;
* the number of non-`x` letters of the reduced word is `(p - 1) * |m| + (m + q)`, exactly the bound.

`tvWord_toWord`, `tvWord_isCyclicallyReduced` and `tvWord_wvListAux_length` (siblings, importing
`transvectionNielsenDefs`) supply the word-level computations about `tvWord`.
-/
import Mathlib
import Submission.Work.OROneRel.magnusStepNielsenRoute
import Submission.Work.OROneRel.transvectionNielsenDefs
import Submission.Work.OROneRel.eps_rightPow
import Submission.Work.OROneRel.mmTrans_comp_neg
import Submission.Work.OROneRel.lsig_eq_smul_wordEps
import Submission.Work.OROneRel.tvWord_toWord
import Submission.Work.OROneRel.tvWord_isCyclicallyReduced
import Submission.Work.OROneRel.tvWord_wvListAux_length

namespace Work.OROneRel

/-! ### Bridge lemmas between the `wordOf` vocabulary and the ambient `toWord` -/

/-- `wordOf` is the reduced word with the `Classical` decidable equality, while `toWord` uses the
ambient instance; the two agree. -/
theorem tvn_wordOf_eq_toWord {α : Type*} [DecidableEq α] (u : FreeGroup α) :
    wordOf u = u.toWord := by
  have h1 : FreeGroup.IsReduced (wordOf u) := by
    unfold wordOf
    exact @FreeGroup.isReduced_toWord α (Classical.decEq α) u
  have h2 : FreeGroup.IsReduced u.toWord := FreeGroup.isReduced_toWord
  have h3 : FreeGroup.mk (wordOf u) = u := mk_wordOf u
  have h4 : FreeGroup.mk u.toWord = u := FreeGroup.mk_toWord
  have h5 : FreeGroup.reduce (wordOf u) = FreeGroup.reduce u.toWord :=
    FreeGroup.reduce.sound (by rw [h3, h4])
  rw [FreeGroup.IsReduced.reduce_eq h1, FreeGroup.IsReduced.reduce_eq h2] at h5
  exact h5

/-- The exponent sum is computed on the reduced word: `eps t r = wordEps t (wordOf r)`. -/
theorem tvn_eps_eq_wordEps_wordOf {α : Type*} (t : α) (r : FreeGroup α) :
    eps t r = wordEps t (wordOf r) := rfl

/-- Cyclic reducedness of a relator is cyclic reducedness of its reduced word. -/
theorem tvn_IsCyclicallyReducedRelator_iff_wordOf (r : FreeGroup (Fin 2)) :
    IsCyclicallyReducedRelator r ↔ FreeGroup.IsCyclicallyReduced (wordOf r) := by
  unfold IsCyclicallyReducedRelator
  rfl

/-- The relator norm is the length of the reduced word. -/
theorem tvn_relatorNorm_eq_wordOf_length (r : FreeGroup (Fin 2)) :
    relatorNorm r = (wordOf r).length := by
  rw [relatorNorm]
  rfl

/-- If the generator `x` does not occur in `r` then its exponent sum vanishes. -/
theorem tvn_eps_eq_zero_of_notMem_relatorLetters {α : Type*} {x : α} {r : FreeGroup α}
    (h : x ∉ relatorLetters r) : eps x r = 0 := by
  classical
  have hx : ∀ b : Bool, (x, b) ∉ r.toWord := by
    intro b hb
    exact h ⟨b, hb⟩
  have hmain : ∀ L : List (α × Bool), (∀ b : Bool, (x, b) ∉ L) → wordEps x L = 0 := by
    intro L
    induction L with
    | nil => intro _; simp [wordEps]
    | cons p L ih =>
      intro hL
      obtain ⟨a, bb⟩ := p
      have hp : (a, bb) ≠ (x, true) ∧ (a, bb) ≠ (x, false) :=
        ⟨fun hc => hL true (by rw [hc]; exact List.mem_cons_self ..),
         fun hc => hL false (by rw [hc]; exact List.mem_cons_self ..)⟩
      have hax : a ≠ x := by
        intro hc
        cases bb
        · exact hp.2 (by simp [hc])
        · exact hp.1 (by simp [hc])
      rw [wordEps, List.map_cons, List.sum_cons, if_neg (by simpa using hax), zero_add]
      exact ih (fun b hb => hL b (List.mem_cons_of_mem _ hb))
  rw [eps]
  exact hmain r.toWord hx

/-- **The proper-power obstruction**: a relator with an exponent sum equal to `±1` is not a proper
power, since the exponent sums of `u ^ k` are `k` times those of `u`. -/
theorem tvn_not_isProperPower_of_eps_eq_pm_one {α : Type*} (x : α) {r : FreeGroup α}
    (h : eps x r = 1 ∨ eps x r = -1) : ¬ IsProperPower r := by
  classical
  rintro ⟨u, k, hk, rfl⟩
  have hkz : eps x (u ^ k) = (k : ℤ) * eps x u := by
    rw [← zpow_natCast u k, epsc_zpow]
  rw [hkz] at h
  rcases h with h | h
  · have hk1 : (k : ℤ) = 1 ∨ (k : ℤ) = -1 := Int.eq_one_or_neg_one_of_mul_eq_one h
    have : (2 : ℤ) ≤ k := by exact_mod_cast hk
    rcases hk1 with h1 | h1 <;> omega
  · have hk1 : (k : ℤ) = 1 ∨ (k : ℤ) = -1 := by
      have h' : (k : ℤ) * eps x u = -1 := h
      have h2 : (k : ℤ) * (-(eps x u)) = 1 := by rw [mul_neg, h']; ring
      rcases Int.eq_one_or_neg_one_of_mul_eq_one h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr h3
    have : (2 : ℤ) ≤ k := by exact_mod_cast hk
    rcases hk1 with h1 | h1 <;> omega

/-- Natural powers in the exponent sum. -/
theorem tvn_epsc_pow {α : Type*} (t : α) (a : FreeGroup α) (k : ℕ) :
    eps t (a ^ k) = (k : ℤ) * eps t a := by
  rw [← zpow_natCast a k, epsc_zpow]

/-- The weight of a two-letter word is the sum of the weights of its two generators. -/
theorem tvn_lsig_wordOf_eq (c : Fin 2 → ℤ) (r : FreeGroup (Fin 2)) :
    lsig c (wordOf r) = c 0 * eps (0 : Fin 2) r + c 1 * eps (1 : Fin 2) r := by
  rw [lsig_eq_smul_wordEps c 0 1 (by decide)
    (by intro z hz0 hz1; fin_cases z <;> simp_all)]
  rw [tvn_eps_eq_wordEps_wordOf, tvn_eps_eq_wordEps_wordOf]

/-! ### The main theorem -/

theorem transvectionNielsenData (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (m : ℤ) (hm : m < 0)
    (hpm : (p : ℤ) * m + (q : ℤ) = 1 ∨ (p : ℤ) * m + (q : ℤ) = -1) :
    ∃ (ψ : FreeGroup (Fin 2) ≃* FreeGroup (Fin 2)) (t : Fin 2) (c : Fin 2 → ℤ),
      ¬ Work.OROneRel.IsProperPower
          (ψ ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q)) ∧
      Work.OROneRel.IsCyclicallyReducedRelator
          (ψ ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q)) ∧
      2 ≤ Work.OROneRel.relatorNorm
          (ψ ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q)) ∧
      (∀ x : Fin 2, x ∈ Work.OROneRel.relatorLetters
          (ψ ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q)) →
        Work.OROneRel.eps x
          (ψ ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q)) ≠ 0) ∧
      t ∈ Work.OROneRel.relatorLetters
          (ψ ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q)) ∧
      c t = 1 ∧
      Work.OROneRel.cohom c
        (ψ ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q)) = 1 ∧
      (Work.OROneRel.wvListAux c t 0
        (Work.OROneRel.wordOf
          (ψ ((FreeGroup.of 0 : FreeGroup (Fin 2)) ^ p * (FreeGroup.of 1) ^ q)))).length
        ≤ (p - 1) * m.natAbs + (m + (q : ℤ)).toNat := by
  classical
  -- The Bezout coefficient `ε = p * m + q = ±1`; note `q = ε - p * m`, so `m + q = ε + (p-1)*(-m)`.
  set ε : ℤ := (p : ℤ) * m + (q : ℤ) with hε
  have hεval : ε = 1 ∨ ε = -1 := hpm
  have hp1 : (1 : ℤ) ≤ (p : ℤ) - 1 := by
    have : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
    omega
  have hm1 : (1 : ℤ) ≤ -m := by omega
  have hprod : (1 : ℤ) ≤ ((p : ℤ) - 1) * (-m) := by nlinarith
  have hkey : m + (q : ℤ) = ((p : ℤ) * m + (q : ℤ)) + ((p : ℤ) - 1) * (-m) := by ring
  have hmq : 0 ≤ m + (q : ℤ) := by
    rw [hkey, ← hε]
    rcases hεval with hh | hh <;> rw [hh] <;> nlinarith [hprod]
  -- The transvection `x ↦ x * y ^ m`, `y ↦ y`.
  set W : Fin 2 → ℤ := fun x => if x = 0 then m else 0 with hW
  have hW0 : W 0 = m := by simp [hW]
  have hW1 : W 1 = 0 := by simp [hW]
  obtain ⟨hcomp1, hcomp2⟩ := mmTrans_comp_neg (1 : Fin 2) W hW1
  let ψ : FreeGroup (Fin 2) ≃* FreeGroup (Fin 2) :=
    MonoidHom.toMulEquiv (mmTrans 1 W) (mmTrans 1 (fun x => -(W x))) hcomp1 hcomp2
  have hψ : ∀ r : FreeGroup (Fin 2), ψ r = mmTrans 1 W r := fun r => rfl
  -- The weights: `t = x = 0` with `c x = 1`, `c y = -p * ε`.
  set c : Fin 2 → ℤ := fun x => if x = 0 then (1 : ℤ) else -((p : ℤ) * ε) with hc
  have hc0 : c 0 = 1 := by simp [hc]
  have hc1 : c 1 = -((p : ℤ) * ε) := by simp [hc]
  set R : FreeGroup (Fin 2) := (FreeGroup.of (0 : Fin 2)) ^ p * (FreeGroup.of (1 : Fin 2)) ^ q with hR
  have hψR : ψ R = (FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) ^ m) ^ p
      * (FreeGroup.of (1 : Fin 2)) ^ q := by
    have h1 : ψ (FreeGroup.of (0 : Fin 2)) = FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) ^ m := by
      rw [hψ, mmTrans_of, hW0]
    have h2 : ψ (FreeGroup.of (1 : Fin 2)) = FreeGroup.of (1 : Fin 2) := by
      rw [hψ, mmTrans_of, hW1, zpow_zero, mul_one]
    rw [hR, map_mul, map_pow, map_pow, h1, h2]
  -- Exponent sums of the image.
  have heps0 : eps (0 : Fin 2) (ψ R) = (p : ℤ) := by
    rw [hψR]
    rw [epsc_mul]
    rw [tvn_epsc_pow, tvn_epsc_pow]
    rw [epsc_mul]
    rw [epsc_zpow]
    rw [epsc_of_eq, epsc_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    ring
  have heps1 : eps (1 : Fin 2) (ψ R) = ε := by
    rw [hψR]
    rw [epsc_mul]
    rw [tvn_epsc_pow, tvn_epsc_pow]
    rw [epsc_mul]
    rw [epsc_zpow]
    rw [epsc_of_ne (by decide : (1 : Fin 2) ≠ 0), epsc_of_eq]
    rw [hε]
    ring
  have hwo : wordOf (ψ R) = tvWord p q m := by
    rw [tvn_wordOf_eq_toWord (ψ R), hψR, tvWord_toWord p q m (by omega) hm hmq]
  refine ⟨ψ, 0, c, ?_, ?_, ?_, ?_, ?_, hc0, ?_, ?_⟩
  · -- `ψ R` is not a proper power: its `y`-exponent sum is `±1`.
    refine tvn_not_isProperPower_of_eps_eq_pm_one (1 : Fin 2) ?_
    rw [heps1]; exact hεval
  · -- `ψ R` is cyclically reduced.
    rw [tvn_IsCyclicallyReducedRelator_iff_wordOf, hwo]
    exact tvWord_isCyclicallyReduced p q m (by omega) hm hmq
  · -- `ψ R` has norm at least two.
    rw [tvn_relatorNorm_eq_wordOf_length, hwo, tvWord_length]
    have hp1n : 1 ≤ p - 1 := by omega
    have hle : 1 * (m.natAbs + 1) ≤ (p - 1) * (m.natAbs + 1) :=
      Nat.mul_le_mul_right _ hp1n
    omega
  · -- no exponent sum of a letter of `ψ R` vanishes.
    intro x _
    have hx : x = 0 ∨ x = 1 := by fin_cases x <;> simp
    rcases hx with hx | hx
    · rw [hx, heps0]
      have hp0 : (0 : ℤ) < (p : ℤ) := by exact_mod_cast (by omega : 0 < p)
      omega
    · rw [hx, heps1]
      rcases hεval with h | h <;> omega
  · -- the letter `x = 0` occurs in `ψ R`.
    by_contra hmem
    have h0 := tvn_eps_eq_zero_of_notMem_relatorLetters hmem
    rw [heps0] at h0
    have : (0 : ℤ) < (p : ℤ) := by exact_mod_cast (by omega : 0 < p)
    omega
  · -- `cohom c (ψ R) = 1`, i.e. `c x * eps x (ψ R) + c y * eps y (ψ R) = 0`.
    have hcohom : cohom c (ψ R) = Multiplicative.ofAdd (lsig c (wordOf (ψ R))) := by
      conv_lhs => rw [← mk_wordOf (ψ R)]
      rw [cohom_mk]
    rw [hcohom, tvn_lsig_wordOf_eq, hc0, hc1, heps0, heps1]
    rcases hεval with h | h <;> rw [h] <;> norm_num
  · -- the weighted Magnus step needs at most `(p-1) * |m| + (m+q)` non-`x` letters.
    rw [hwo, tvWord_wvListAux_length]

end Work.OROneRel
