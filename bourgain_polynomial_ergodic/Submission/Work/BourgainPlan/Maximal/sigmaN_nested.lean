import Mathlib
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.IonescuWainger.taoSetS_coprime
import Submission.Work.BourgainPlan.IonescuWainger.farey_cover_by_taoSetS
import Submission.Work.BourgainPlan.IonescuWainger.coe_sigmaAFinset

/-!
# **(Σ1)** The Ionescu–Wainger supersets `Σ_N` are nested

`Σ_N = sigmaLeFinset (taoSetS ρ N) (iwK ρ) = ⋃_{A ⊆ S_N, |A| ≤ k} 𝕋[Q_A]`, `k = ⌊2/ρ⌋ + 1`, is
Tao's major-arc set for `S_N = taoSetS ρ N` (Tao, Lemma `iwac`), and this file proves that
`Σ_{N₁} ⊆ Σ_{N₂}` whenever `N₁ ≤ N₂` (`MST_ROUTE.md`, §1, "(Σ1) NESTED").

The mathematical content is a **matching of the moduli**: every element `q` of `S_{N₁}` divides an
element `w q` of `S_{N₂}` (`nested_exists_dvd_taoSetS`); because the elements of `S_{N₁}` are
pairwise coprime (`taoSetS_coprime`), `Q_A = ∏_{q ∈ A} q` then divides `∏_{q ∈ A} w(q)` for *any*
choice of the multiples `w(q)` (`nested_prod_dvd_of_pairwise_coprime`), and since the image of `A`
under `w` has at most `|A| ≤ k` elements we get `Q_A ∣ Q_{A'}` with `A' := A.image w ⊆ S_{N₂}`
(`nested_mem_sigmaSubAFinset_of_dvd` then converts divisibility of the moduli into containment of
the torsion subgroups `𝕋[Q_A] ⊆ 𝕋[Q_{A'}]`).

The `N`-dependence of the matching is the arithmetic content of Tao's set: for a prime power
`p^{e₁(p)} ∈ S_{N₁}` (where `e_N(p) = ⌊log N / log p⌋`) either `p^{e₂(p)} ∈ S_{N₂}` too (when `p`
is still a "large" prime at level `N₂`, i.e. `p > ⌊N₂^{ρ/2}⌋`), or `p` has become small and
`p^{e₂(p)}` divides the single element `smallPrimePowerProd ρ N₂` of `S_{N₂}`; the small element
`smallPrimePowerProd ρ N₁` of `S_{N₁}` divides `smallPrimePowerProd ρ N₂`
(`nested_smallPrimePowerProd_dvd`).  No hypothesis on `ρ` is needed: for `ρ ≤ 0` the set of "small"
primes is empty (`smallPrimePowerProd ρ N = 1`) and every element of `S_{N₁}` is a single large
prime power.

## Provenance

`Submission/Work/BourgainPlan/Maximal/iw_superset.lean` (the requester's definitions file) did not
compile when this file was written: the definition of `IWSupersetBound` referred to an undefined
identifier `sigmaN`.  The one token `(sigmaN ρ N)` has been replaced there by `(iwSigma ρ N)` (that
file's own definition of `Σ_N`) — the only change made to it.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open Work.BourgainPlan.IonescuWainger

/-- Membership characterisation of Tao's set of large prime powers: its elements are the numbers
`p ^ ⌊log N / log p⌋`, for `p` a prime with `⌊N^{ρ/2}⌋ < p ≤ N`. -/
lemma nested_mem_largePrimePowers {ρ : ℝ} {N x : ℕ} :
    x ∈ largePrimePowers ρ N ↔
      ∃ p : ℕ, Nat.Prime p ∧ ⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1 ≤ p ∧ p ≤ N ∧
        p ^ ⌊Real.log N / Real.log p⌋₊ = x := by
  rw [largePrimePowers, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpx⟩
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    exact ⟨p, hp.2, hp.1.1, hp.1.2, hpx⟩
  · rintro ⟨p, hprim, h1, h2, hpx⟩
    exact ⟨p, by rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨h1, h2⟩, hprim⟩, hpx⟩

/-- Every element of Tao's set `taoSetS ρ N` is at least `1`. -/
lemma nested_one_le_of_mem_taoSetS {ρ : ℝ} {N q : ℕ} (hq : q ∈ taoSetS ρ N) : 1 ≤ q := by
  rw [taoSetS, Finset.mem_insert] at hq
  rcases hq with rfl | hq
  · rw [smallPrimePowerProd]
    exact Finset.one_le_prod₀ (fun p hp => Nat.one_le_pow _ _ (Finset.mem_filter.mp hp).2.pos)
  · obtain ⟨p, hpp, -, -, rfl⟩ := nested_mem_largePrimePowers.mp hq
    exact Nat.one_le_pow _ _ hpp.pos

/-- **The exponent of a prime in Tao's set is at most `N`**: for a prime `p` and `1 ≤ N`,
`p ^ ⌊log N / log p⌋ ≤ N`.  This elementary bound is what makes the exponents
`e_N(p) = ⌊log N / log p⌋` at two levels `N₁ ≤ N₂` comparable. -/
lemma nested_pow_floor_log_div_log_le {N p : ℕ} (hp : Nat.Prime p) (hN : 1 ≤ N) :
    p ^ ⌊Real.log N / Real.log p⌋₊ ≤ N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hr : 0 ≤ Real.log (N : ℝ) / Real.log (p : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) (le_of_lt hlogp)
  have hmain : ((p : ℝ) ^ (⌊Real.log N / Real.log p⌋₊ : ℕ)) ≤ (N : ℝ) := by
    calc ((p : ℝ) ^ (⌊Real.log N / Real.log p⌋₊ : ℕ))
        = (p : ℝ) ^ ((⌊Real.log N / Real.log p⌋₊ : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (p : ℝ) ^ (Real.log (N : ℝ) / Real.log (p : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (Nat.floor_le hr)
      _ = (N : ℝ) := by
          have hsimp : Real.log (p : ℝ) * (Real.log (N : ℝ) / Real.log (p : ℝ))
              = Real.log (N : ℝ) := by
            rw [mul_comm (Real.log (p : ℝ)) (Real.log (N : ℝ) / Real.log (p : ℝ)),
              div_mul_cancel₀ _ (ne_of_gt hlogp)]
          rw [Real.rpow_def_of_pos hppos, hsimp, Real.exp_log hNpos]
  exact_mod_cast hmain

/-- **`smallPrimePowerProd` is monotone for divisibility**: for `N₁ ≤ N₂` the "small" element of
`taoSetS ρ N₁` divides that of `taoSetS ρ N₂`. -/
lemma nested_smallPrimePowerProd_dvd {ρ : ℝ} {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    smallPrimePowerProd ρ N₁ ∣ smallPrimePowerProd ρ N₂ := by
  by_cases hρ : 0 < ρ
  · -- for `ρ > 0` the index set grows and so do the exponents
    have hsub : (Finset.Icc 2 ⌊(N₁ : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime ⊆
        (Finset.Icc 2 ⌊(N₂ : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.1.1, le_trans hp.1.2 (Nat.floor_le_floor (Real.rpow_le_rpow
        (Nat.cast_nonneg N₁) (Nat.cast_le.mpr h) (by linarith)))⟩, hp.2⟩
    have hexp : ∀ p ∈ (Finset.Icc 2 ⌊(N₁ : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime,
        ⌊Real.log N₁ / Real.log p⌋₊ ≤ ⌊Real.log N₂ / Real.log p⌋₊ := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      have hN₁ : 1 ≤ N₁ := by
        by_contra hc
        have h0 : N₁ = 0 := by omega
        subst h0
        rw [Nat.cast_zero, Real.zero_rpow (by linarith : ρ / 2 ≠ 0)] at hp
        simp at hp
        omega
      exact le_floor_log_div_log hp.2
        (le_trans (nested_pow_floor_log_div_log_le hp.2 hN₁) h)
    have hkey := Finset.prod_sdiff
      (s₁ := (Finset.Icc 2 ⌊(N₁ : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime)
      (s₂ := (Finset.Icc 2 ⌊(N₂ : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime)
      hsub (f := fun p => p ^ ⌊Real.log N₂ / Real.log p⌋₊)
    rw [smallPrimePowerProd, smallPrimePowerProd, ← hkey]
    exact dvd_mul_of_dvd_right (Finset.prod_dvd_prod_of_dvd _ _
      (fun p hp => Nat.pow_dvd_pow p (hexp p hp))) _
  · -- for `ρ ≤ 0` there are no small primes, so `smallPrimePowerProd ρ N₁ = 1`
    have hrpow : (N₁ : ℝ) ^ (ρ / 2) ≤ 1 := by
      rcases Nat.eq_zero_or_pos N₁ with h0 | hpos
      · subst h0
        rcases eq_or_lt_of_le (le_of_not_gt hρ) with hρ0 | hρneg
        · subst hρ0
          rw [show ((0 : ℕ) : ℝ) ^ ((0 : ℝ) / 2) = 1 by norm_num [Real.rpow_zero]]
        · rw [Nat.cast_zero, Real.zero_rpow (by linarith : ρ / 2 ≠ 0)]
          norm_num
      · have h1 : (1 : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hpos
        have := Real.rpow_le_rpow_of_exponent_le h1 (show ρ / 2 ≤ (0 : ℝ) by linarith)
        rwa [Real.rpow_zero] at this
    have hfloor : ⌊(N₁ : ℝ) ^ (ρ / 2)⌋₊ ≤ 1 := by
      simpa using Nat.floor_le_floor hrpow
    have hprod : smallPrimePowerProd ρ N₁ = 1 := by
      rw [smallPrimePowerProd, Finset.prod_eq_one]
      intro p hp
      exfalso
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      omega
    rw [hprod]
    exact one_dvd _

/-- **The modulus matching (Σ1).**  Every element of Tao's set `S_{N₁} = taoSetS ρ N₁` divides an
element of `S_{N₂} = taoSetS ρ N₂` when `N₁ ≤ N₂`. -/
lemma nested_exists_dvd_taoSetS {ρ : ℝ} {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) {q : ℕ}
    (hq : q ∈ taoSetS ρ N₁) : ∃ q' ∈ taoSetS ρ N₂, q ∣ q' := by
  rw [taoSetS, Finset.mem_insert] at hq
  rcases hq with rfl | hq
  · exact ⟨smallPrimePowerProd ρ N₂, Finset.mem_insert_self _ _,
      nested_smallPrimePowerProd_dvd h⟩
  · obtain ⟨p, hpp, hlow, hhigh, hq⟩ := nested_mem_largePrimePowers.mp hq
    have hN₁ : 1 ≤ N₁ := by omega
    by_cases hcase : ⌊(N₂ : ℝ) ^ (ρ / 2)⌋₊ + 1 ≤ p
    · -- the prime `p` is still large at level `N₂`
      refine ⟨p ^ ⌊Real.log N₂ / Real.log p⌋₊, ?_, ?_⟩
      · rw [taoSetS]
        exact Finset.mem_insert_of_mem (largePrimePowers_mem hpp hcase (le_trans hhigh h))
      · rw [← hq]
        exact Nat.pow_dvd_pow p (le_floor_log_div_log hpp
          (le_trans (nested_pow_floor_log_div_log_le hpp hN₁) h))
    · -- the prime `p` has become small at level `N₂`, so it is absorbed by `smallPrimePowerProd`
      have hple : p ≤ ⌊(N₂ : ℝ) ^ (ρ / 2)⌋₊ := by omega
      refine ⟨smallPrimePowerProd ρ N₂, Finset.mem_insert_self _ _, ?_⟩
      rw [← hq]
      refine pow_dvd_smallPrimePowerProd hpp ?_ ?_
      · calc (p : ℝ) ≤ ((⌊(N₂ : ℝ) ^ (ρ / 2)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hple
          _ ≤ (N₂ : ℝ) ^ (ρ / 2) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N₂) _)
      · exact le_trans (nested_pow_floor_log_div_log_le hpp hN₁) h

/-- **A product of pairwise coprime divisors divides the modulus**: if the elements of `s` are
pairwise coprime and each divides `M`, then `∏_{a ∈ s} a ∣ M`. -/
lemma nested_prod_dvd_of_pairwise_coprime {s : Finset ℕ} {M : ℕ}
    (hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Nat.Coprime a b) (h : ∀ a ∈ s, a ∣ M) :
    ∏ a ∈ s, a ∣ M := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (h a (Finset.mem_insert_self a s)) (ih ?_ ?_)
      · refine Nat.Coprime.prod_right (fun x hx => ?_)
        exact hcop a (Finset.mem_insert_self a s) x (Finset.mem_insert_of_mem hx)
          (fun hax => ha (hax ▸ hx))
      · intro x hx y hy hxy
        exact hcop x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
      · intro x hx
        exact h x (Finset.mem_insert_of_mem hx)

/-- **The torsion subgroups increase with the modulus**: if `Q_B ∣ Q_{B'}` (both nonzero) then
`Σ_{⊆ B} = 𝕋[Q_B]` is contained in `Σ_{⊆ B'} = 𝕋[Q_{B'}]`.  Write `Q_{B'} = Q_B · (Q_{B'}/Q_B)`;
then `arcPt` with the common denominator `Q_{B'}` gives the same circle point, and reducing the
numerator modulo `Q_{B'}` lands in the `Finset` listing of `Σ_{⊆ B'}`. -/
lemma nested_mem_sigmaSubAFinset_of_dvd {B B' : Finset ℕ} (hB : 1 ≤ QA B) (hB' : 1 ≤ QA B')
    (hdvd : QA B ∣ QA B') {β : Work.BourgainPlan.IonescuWainger.Circle}
    (hβ : β ∈ sigmaSubAFinset B) : β ∈ sigmaSubAFinset B' := by
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hβ
  have hB0 : QA B ≠ 0 := by omega
  have hB'0 : QA B' ≠ 0 := by omega
  refine Finset.mem_image.mpr ⟨(((a : ℤ) * ((QA B' / QA B : ℕ) : ℤ)) % (QA B' : ℤ)).toNat, ?_, ?_⟩
  · rw [Finset.mem_range, Int.toNat_lt (Int.emod_nonneg _ (by exact_mod_cast hB'0))]
    exact Int.emod_lt_of_pos _ (by exact_mod_cast Nat.pos_of_ne_zero hB'0)
  · rw [arcPt_emod_toNat hB'0]
    exact (arcPt_commonDenom hB hB' hdvd (a : ℤ)).symm

/-- **(Σ1)** Tao's Ionescu–Wainger supersets are nested: `Σ_{N₁} ⊆ Σ_{N₂}` for `N₁ ≤ N₂`.  Every divisor of `Q_A` (`A ⊆ S_{N₁}`, `|A| ≤ k`) divides `Q_{A'}` for some `A' ⊆ S_{N₂}` with `|A'| ≤ k`: each `p^{⌊log N₁/log p⌋} ∈ S_{N₁}` divides the corresponding element of `S_{N₂}` (or the small element `smallPrimePowerProd ρ N₂` when the prime has become small), and the number of elements needed stays at most `k`. -/
theorem sigmaN_nested (ρ : ℝ) {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    Work.BourgainPlan.Maximal.iwSigma ρ N₁ ⊆ Work.BourgainPlan.Maximal.iwSigma ρ N₂ := by
  classical
  intro β hβ
  rw [iwSigma, sigmaLeFinset, Finset.mem_biUnion] at hβ
  obtain ⟨A, hA, hβA⟩ := hβ
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  obtain ⟨hAsub, hAcard⟩ := hA
  -- a choice, for each `q ∈ A ⊆ S_{N₁}`, of a multiple in `S_{N₂}`
  let W : Finset ℕ := A.attach.image
    (fun q : {x // x ∈ A} => Classical.choose (nested_exists_dvd_taoSetS h (hAsub q.2)))
  have hWmem : W ⊆ taoSetS ρ N₂ := by
    intro q' hq'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hq'
    exact (Classical.choose_spec (nested_exists_dvd_taoSetS h (hAsub q.2))).1
  have hWcard : W.card ≤ iwK ρ := by
    calc W.card ≤ A.attach.card := Finset.card_image_le
      _ = A.card := Finset.card_attach
      _ ≤ iwK ρ := hAcard
  have hWdvd : QA A ∣ QA W := by
    rw [QA, QA]
    refine nested_prod_dvd_of_pairwise_coprime
      (fun a ha b hb hab => taoSetS_coprime ρ N₁ a (hAsub ha) b (hAsub hb) hab) (fun q hq => ?_)
    refine dvd_trans (Classical.choose_spec (nested_exists_dvd_taoSetS h (hAsub hq))).2 ?_
    exact Finset.dvd_prod_of_mem _ (Finset.mem_image.mpr
      ⟨⟨q, hq⟩, Finset.mem_attach A ⟨q, hq⟩, rfl⟩)
  rw [iwSigma, sigmaLeFinset, Finset.mem_biUnion]
  refine ⟨W, ?_, ?_⟩
  · rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hWmem, hWcard⟩
  · have h1 : 1 ≤ QA A := Finset.one_le_prod₀ (fun q hq =>
      nested_one_le_of_mem_taoSetS (hAsub hq))
    have h2 : 1 ≤ QA W := Finset.one_le_prod₀ (fun q' hq' =>
      nested_one_le_of_mem_taoSetS (hWmem hq'))
    exact nested_mem_sigmaSubAFinset_of_dvd h1 h2 hWdvd hβA

end Work.BourgainPlan.Maximal
