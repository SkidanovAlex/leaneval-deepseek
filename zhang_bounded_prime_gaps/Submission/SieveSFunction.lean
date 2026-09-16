import Mathlib
import Submission.Commons.NumberTheory.CongruenceWindows.add_mod_eq_zero_iff_neg_residue
import Submission.Commons.NumberTheory.CongruenceWindows.card_window_modEq_bounds
import Submission.SieveWindows

open scoped BigOperators

/-!
# The sieve `S`-function: coprimality structure (Polymath8a §4.1)

For moduli `m i := [d i, d' i]` and a tuple `H` with `b + H i` coprime to
`W`, the window count

    S = #{ n ∈ [N,2N] : n ≡ b (W) ∧ ∀ i, m i | n + H i }

*vanishes unless* every `m i` is coprime to `W` and the `m i` are pairwise
coprime.  The coprime-to-`W` part is unconditional: any member `n` satisfies
`gcd (n + H i, W) = 1`, because `n ≡ b (W)` and `(b + H i, W) = 1`.  The
pairwise part needs the size hypothesis that a common prime of `m i`, `m j`
divides `H j - H i`, hence is bounded by the tuple diameter; in the paper
`w = log log log x` grows to infinity so this holds for every fixed tuple once
`x` is large enough.  Here that is stated with an explicit threshold `wd`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The `S`-function of Polymath8a §4.1: numbers `n ∈ [N, 2N]` with
`n ≡ b (mod W)` and `m i | n + H i` for every `i`. -/
def Sset (N W b : ℕ) {k : ℕ} (H : Fin k → ℕ) (m : Fin k → ℕ) : Finset ℕ :=
  (Finset.Icc N (2 * N)).filter fun n =>
    n % W = b % W ∧ ∀ i : Fin k, m i ∣ n + H i

/-- Adding the same offset keeps residues congruent. -/
lemma add_mod_add_mod_of_mod_eq {W b h n : ℕ} (hres : n % W = b % W) :
    (n + h) % W = (b + h) % W := by
  calc
    (n + h) % W = (n % W + h % W) % W := by rw [Nat.add_mod]
    _ = (b % W + h % W) % W := by rw [hres]
    _ = (b + h) % W := by rw [← Nat.add_mod]

/-- `gcd (x % W) W = gcd x W`. -/
lemma gcd_mod_right (x W : ℕ) : (x % W).gcd W = x.gcd W := by
  have h1 : x.gcd W = (x % W).gcd W := by
    rw [← Nat.gcd_comm]
    exact Nat.gcd_rec W x
  exact h1.symm

/-- Congruent numbers modulo `W` have equal gcd with `W`. -/
lemma gcd_add_eq_of_mod_eq {W b h n : ℕ} (hres : n % W = b % W) :
    (n + h).gcd W = (b + h).gcd W := by
  have hres' : (n + h) % W = (b + h) % W := add_mod_add_mod_of_mod_eq hres
  calc
    (n + h).gcd W = ((n + h) % W).gcd W := (gcd_mod_right (n + h) W).symm
    _ = ((b + h) % W).gcd W := by rw [hres']
    _ = (b + h).gcd W := gcd_mod_right (b + h) W

/-- In the window class of a number coprime to `W`, `n + h` is coprime to `W`. -/
lemma window_add_coprime_W {W b h n : ℕ} (hres : n % W = b % W)
    (hbW : (b + h).Coprime W) : (n + h).Coprime W := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [gcd_add_eq_of_mod_eq (W := W) hres]
  exact hbW.gcd_eq_one

/-- Any member `n` of the `S`-set forces `(m i, W) = 1` provided
`(b + H i, W) = 1`. -/
theorem Sset_mem_coprime_W {k N W b : ℕ} {H : Fin k → ℕ} {m : Fin k → ℕ} {i : Fin k}
    (hbW : (b + H i).Coprime W) {n : ℕ} (hn : n ∈ Sset N W b H m) :
    (m i).Coprime W := by
  rcases (Finset.mem_filter.mp hn) with ⟨hnIcc, hcond⟩
  rcases hcond with ⟨hnW, hmi⟩
  have hmemi : m i ∣ n + H i := hmi i
  have hncop : (n + H i).Coprime W := window_add_coprime_W (W := W) (h := H i) hnW hbW
  exact hncop.coprime_dvd_left hmemi

/-- If `i ≠ j` and the entries `H i`, `H j` are distinct with every pairwise
difference `< wd`, and every prime `≤ wd` divides `W`, then any member of the
`S`-set forces `(m i, m j) = 1`. -/
theorem Sset_mem_pairwise_coprime {k N W b wd : ℕ} {H : Fin k → ℕ} {m : Fin k → ℕ}
    (hWdiv : ∀ p : ℕ, p.Prime → p ≤ wd → p ∣ W)
    (hHinj : Function.Injective H)
    (hbW : ∀ i : Fin k, (b + H i).Coprime W)
    (hsep : ∀ i j : Fin k, i ≠ j → H j - H i < wd)
    {i j : Fin k} (hij : i ≠ j) {n : ℕ} (hn : n ∈ Sset N W b H m) :
    (m i).Coprime (m j) := by
  classical
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  -- g := gcd (m i) (m j), with a prime p | g
  rcases Nat.exists_prime_and_dvd hg with ⟨p, hp, hpg⟩
  have hpi : p ∣ m i := dvd_trans hpg (Nat.gcd_dvd_left (m i) (m j))
  have hpj : p ∣ m j := dvd_trans hpg (Nat.gcd_dvd_right (m i) (m j))
  have hmem : ∀ i : Fin k, m i ∣ n + H i := (Finset.mem_filter.mp hn).2.2
  have hpd1 : p ∣ n + H i := dvd_trans hpi (hmem i)
  have hpd2 : p ∣ n + H j := dvd_trans hpj (hmem j)
  have hdvdW : p ∣ W := by
    by_cases hlt : H i < H j
    · -- p | H j - H i, and H j - H i < wd with H i < H j
      have hd : p ∣ H j - H i := by
        have hd0 : p ∣ (n + H j) - (n + H i) := Nat.dvd_sub hpd2 hpd1
        have hred : (n + H j) - (n + H i) = H j - H i := by omega
        rwa [hred] at hd0
      have hpos : 0 < H j - H i := by omega
      have hp_le : p ≤ H j - H i := Nat.le_of_dvd hpos hd
      have hpwd : p < wd := lt_of_le_of_lt hp_le (hsep i j hij)
      exact hWdiv p hp (by omega)
    · -- H j ≤ H i; distinctness gives H j < H i
      have hle2 : H j ≤ H i := Nat.le_of_not_gt hlt
      have hne : H i ≠ H j := by
        intro h
        exact hij (hHinj h)
      have hlt2 : H j < H i := lt_of_le_of_ne hle2 (by exact fun h => hne h.symm)
      have hd : p ∣ H i - H j := by
        have hd0 : p ∣ (n + H i) - (n + H j) := Nat.dvd_sub hpd1 hpd2
        have hred : (n + H i) - (n + H j) = H i - H j := by omega
        rwa [hred] at hd0
      have hpos : 0 < H i - H j := by omega
      have hp_le : p ≤ H i - H j := Nat.le_of_dvd hpos hd
      have hpwd : p < wd := lt_of_le_of_lt hp_le (hsep j i hij.symm)
      exact hWdiv p hp (by omega)
  -- p | W and p | m i contradicts (m i, W) = 1
  have hcop : (m i).Coprime W := Sset_mem_coprime_W (hbW i) hn
  have hgW : (m i).gcd W = 1 := hcop.gcd_eq_one
  have hpd : p ∣ (m i).gcd W := Nat.dvd_gcd hpi hdvdW
  have hp1 : p = 1 := by
    rw [hgW] at hpd
    exact Nat.eq_one_of_dvd_one hpd
  exact hp.ne_one hp1


/-! ## CRT collapse of the `S`-set over `{W} ∪ {m₁,…,mₖ}`

With all moduli `m i` pairwise coprime and coprime to `W`, the `S`-set
(congruences modulo `W` and each `m i`) is a single residue class modulo
`W · ∏ᵢ m i`, so its size is `N/(W·∏ᵢ m i) + O(1)`.  This is the
Polymath8a §4.1 formula `S = x/(W·[d₁,d′₁]···[dₖ,d′ₖ]) + O(1)`. -/

/-- The combined modulus function over `Fin (k+1)` (coordinate `0 ↦ W`,
`i.succ ↦ m i`). -/
def sComb {k : ℕ} (W : ℕ) (m : Fin k → ℕ) : Fin (k + 1) → ℕ :=
  fun f => Fin.cases W m f

/-- The combined target function (residue `b` for coordinate 0, canonical
`-H i` residues for `i.succ`). -/
def aComb {k : ℕ} (b : ℕ) (H : Fin k → ℕ) (m : Fin k → ℕ) : Fin (k + 1) → ℕ :=
  fun f => Fin.cases b (fun i : Fin k => (m i - H i % m i) % m i) f

/-- `∏` over `Fin (k+1)` of the combined moduli equals `W · ∏ᵢ m i`. -/
lemma sComb_prod {k : ℕ} (W : ℕ) (m : Fin k → ℕ) :
    (∏ f : Fin (k + 1), sComb W m f) = W * (∏ i : Fin k, m i) := by
  rw [Fin.prod_univ_succ]
  simp [sComb]

/-- The `S`-set filter equals the full congruence system over `Fin (k+1)`. -/
lemma Sset_filter_eq_sComb {k N W b : ℕ} {H : Fin k → ℕ} {m : Fin k → ℕ}
    (hm0 : ∀ i : Fin k, m i ≠ 0) :
    Sset N W b H m =
      (Finset.Icc N (2 * N)).filter (fun n : ℕ =>
        ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))),
          n % sComb W m i = aComb b H m i % sComb W m i) := by
  classical
  refine Finset.filter_congr (fun n hn => ?_)
  constructor
  · intro h
    intro i hi
    refine Fin.cases ?_ ?_ i
    · simpa [sComb, aComb] using h.1
    · intro i0
      have hmemi : m i0 ∣ n + H i0 := h.2 i0
      have hmod0 : (n + H i0) % m i0 = 0 := Nat.mod_eq_zero_of_dvd hmemi
      have hmpos : 0 < m i0 := Nat.pos_of_ne_zero (hm0 i0)
      have hneg : n % m i0 = (m i0 - H i0 % m i0) % m i0 :=
        (Commons.NumberTheory.CongruenceWindows.add_mod_eq_zero_iff_neg_residue
          (m := m i0) (h := H i0) (n := n) hmpos).mp hmod0
      simpa [sComb, aComb, Nat.mod_mod] using hneg
  · intro h
    have h0 : n % W = b % W := by
      have hh := h 0 (by simp)
      simpa [sComb, aComb] using hh
    have hdiv : ∀ i : Fin k, m i ∣ n + H i := by
      intro i
      have hh := h i.succ (by simp)
      have hmpos : 0 < m i := Nat.pos_of_ne_zero (hm0 i)
      have hneg : n % m i = (m i - H i % m i) % m i := by
        simpa [sComb, aComb, Nat.mod_mod] using hh
      have hmod0 : (n + H i) % m i = 0 :=
        (Commons.NumberTheory.CongruenceWindows.add_mod_eq_zero_iff_neg_residue
          (m := m i) (h := H i) (n := n) hmpos).mpr hneg
      exact Nat.dvd_of_mod_eq_zero hmod0
    exact ⟨h0, hdiv⟩

/-- Pairwise coprimality of the combined moduli. -/
lemma sComb_pairwise_coprime {k W : ℕ} {m : Fin k → ℕ}
    (hcopW : ∀ i : Fin k, (m i).Coprime W)
    (hcopm : ∀ i j : Fin k, i ≠ j → (m i).Coprime (m j)) :
    ((Finset.univ : Finset (Fin (k + 1))) : Set (Fin (k + 1))).Pairwise
      (fun a b => Nat.Coprime (sComb W m a) (sComb W m b)) := by
  intro a ha b hb hne
  cases a using Fin.cases
  · cases b using Fin.cases
    · exact (hne rfl).elim
    · rename_i i
      simpa [sComb] using (hcopW i).symm
  · rename_i i
    cases b using Fin.cases
    · simpa [sComb] using hcopW i
    · rename_i j
      have hIn : i ≠ j := by
        intro hij
        exact hne (congrArg Fin.succ hij)
      simpa [sComb] using hcopm i j hIn

/-- The combined moduli are all nonzero. -/
lemma sComb_ne_zero {k W : ℕ} {m : Fin k → ℕ} (hW : 0 < W)
    (hm0 : ∀ i : Fin k, m i ≠ 0) : ∀ f ∈ (Finset.univ : Finset (Fin (k + 1))),
      sComb W m f ≠ 0 := by
  intro f hf
  cases f using Fin.cases
  · exact ne_of_gt hW
  · rename_i i
    exact hm0 i

/-- **`S`-function count, product form.**  For pairwise-coprime moduli
`{W} ∪ {m₁,…,mₖ}` the `S`-set count is `N/(W·∏ᵢ m i) + O(1)`:
Polymath8a §4.1 `S = x/(W·[d₁,d′₁]···[dₖ,d′ₖ]) + O(1)` (coprime case). -/
theorem Sset_card_window_bounds {k N W b : ℕ} {H : Fin k → ℕ} {m : Fin k → ℕ}
    (hW : 0 < W) (hm0 : ∀ i : Fin k, m i ≠ 0)
    (hcopW : ∀ i : Fin k, (m i).Coprime W)
    (hcopm : ∀ i j : Fin k, i ≠ j → (m i).Coprime (m j)) :
    |((Sset N W b H m).card : ℝ) -
      (N : ℝ) / ((W * (∏ i : Fin k, m i) : ℕ) : ℝ)| ≤ 2 := by
  classical
  have hcop2 : ((Finset.univ : Finset (Fin (k + 1))) : Set (Fin (k + 1))).Pairwise
      (fun u v => Nat.Coprime (sComb W m u) (sComb W m v)) :=
    sComb_pairwise_coprime (k := k) (W := W) hcopW hcopm
  have hne0 : ∀ f ∈ (Finset.univ : Finset (Fin (k + 1))), sComb W m f ≠ 0 :=
    sComb_ne_zero (k := k) hW hm0
  have hfilter : Sset N W b H m =
      (Finset.Icc N (2 * N)).filter (fun n : ℕ =>
        ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))),
          n % sComb W m i = aComb b H m i % sComb W m i) :=
    Sset_filter_eq_sComb (k := k) (H := H) (m := m) (N := N) hm0
  have hcard : (Sset N W b H m).card =
      congruenceCard N (Finset.univ : Finset (Fin (k + 1))) (sComb W m) (aComb b H m) := by
    rw [congruenceCard]
    rw [hfilter]
    apply congrArg Finset.card
    ext x
    simp
  have hbnd : |(congruenceCard N (Finset.univ : Finset (Fin (k + 1)))
        (sComb W m) (aComb b H m) : ℝ) -
      (N : ℝ) / (((Finset.univ : Finset (Fin (k + 1))).prod (sComb W m) : ℕ) : ℝ)| ≤ 2 :=
    congruenceCard_window_bounds (a := aComb b H m) (s := sComb W m)
      (t := Finset.univ) (N := N) hne0 hcop2
  have hprodU : (Finset.univ : Finset (Fin (k + 1))).prod (sComb W m) =
      W * (∏ i : Fin k, m i) := by
    change (∏ f : Fin (k + 1), sComb W m f) = W * (∏ i : Fin k, m i)
    exact sComb_prod W m
  have hbnd' : |(congruenceCard N (Finset.univ : Finset (Fin (k + 1)))
        (sComb W m) (aComb b H m) : ℝ) -
      (N : ℝ) / ((W * (∏ i : Fin k, m i) : ℕ) : ℝ)| ≤ 2 := by
    simpa [hprodU] using hbnd
  simpa [hcard] using hbnd'


/-! ## Bridging to the divisor-pair moduli `[dᵢ,d′ᵢ] = lcm (d i) (d′ i)`

The divisor-pair expansion (`Commons.NumberTheory.SieveWindows.
divisorSumProduct_window_eq`) turns window sums of products of one-dimensional
divisor sums into double sums whose `(d, d′)`-coefficient is
`# {n ∈ window : lcm d d′ | n + h}`.  Per coordinate these are exactly the
`Sset`-counts with modulus `m i := lcm (d i) (d′ i)`.  The theorems below
assemble that data into the hypotheses of `Sset_card_window_bounds`, giving
the Polymath8a §4.1 formula with the divisor-pair moduli in place. -/

/-- The `S`-set is the residue-class window filtered by the divisor
conditions. -/
theorem Sset_eq_class_filter {k N W b : ℕ} {H : Fin k → ℕ} {m : Fin k → ℕ} :
    Sset N W b H m =
      ((Finset.Icc N (2 * N)).filter (fun n => n % W = b % W)).filter
        (fun n => ∀ i : Fin k, m i ∣ n + H i) := by
  rw [Sset]
  rw [Finset.filter_filter]

/-- **Divisor-pair `S`-count.**  For moduli `m i = [d i, d′ i]` pairwise
coprime and coprime to `W`, `# S = N/(W·∏ᵢ [dᵢ,d′ᵢ]) + O(1)` — the shape the
divisor-pair expansions of Polymath8a §4.1 feed into the main term. -/
theorem Sset_lcm_card_window_bounds {k N W b : ℕ} {H d d' : Fin k → ℕ}
    (hW : 0 < W) (hd : ∀ i : Fin k, d i ≠ 0) (hd' : ∀ i : Fin k, d' i ≠ 0)
    (hcopW : ∀ i : Fin k, (Nat.lcm (d i) (d' i)).Coprime W)
    (hcopm : ∀ i j : Fin k, i ≠ j →
      (Nat.lcm (d i) (d' i)).Coprime (Nat.lcm (d j) (d' j))) :
    |((Sset N W b H (fun i => Nat.lcm (d i) (d' i))).card : ℝ) -
      (N : ℝ) / ((W * (∏ i : Fin k, Nat.lcm (d i) (d' i)) : ℕ) : ℝ)| ≤ 2 := by
  have hm0 : ∀ i : Fin k, Nat.lcm (d i) (d' i) ≠ 0 := fun i =>
    Nat.lcm_ne_zero (hd i) (hd' i)
  exact Sset_card_window_bounds (m := fun i => Nat.lcm (d i) (d' i)) hW hm0 hcopW hcopm


/-! ## Vanishing of non-coprime configurations

A tuple of moduli that is *not* coprime to `W`, or whose moduli are *not*
pairwise coprime, admits no member of the `S`-set (the count is zero).  This
is the "S vanishes unless …" half of Polymath8a §4.1, used to restrict the
`(d,e)`-sums of the expansions to coprime tuples. -/

/-- If some `m i` shares a factor with `W`, the `S`-set is empty. -/
theorem Sset_card_eq_zero_of_not_coprime_W {k N W b : ℕ} {H m : Fin k → ℕ} {i : Fin k}
    (hbW : (b + H i).Coprime W) (hbad : ¬ (m i).Coprime W) :
    Sset N W b H m = ∅ := by
  classical
  ext n
  constructor
  · intro hn
    have hc : (m i).Coprime W := Sset_mem_coprime_W (i := i) hbW hn
    exact (hbad hc).elim
  · intro h
    simp at h

/-- If two moduli share a factor (with the size hypothesis on the tuple), the
`S`-set is empty. -/
theorem Sset_card_eq_zero_of_not_pairwise_coprime {k N W b wd : ℕ} {H m : Fin k → ℕ}
    {i j : Fin k} (hWdiv : ∀ p : ℕ, p.Prime → p ≤ wd → p ∣ W)
    (hHinj : Function.Injective H) (hbW : ∀ i : Fin k, (b + H i).Coprime W)
    (hsep : ∀ i j : Fin k, i ≠ j → H j - H i < wd)
    (hij : i ≠ j) (hbad : ¬ (m i).Coprime (m j)) :
    Sset N W b H m = ∅ := by
  classical
  ext n
  constructor
  · intro hn
    have hc : (m i).Coprime (m j) := Sset_mem_pairwise_coprime (k := k) (N := N) (W := W)
      (b := b) (wd := wd) hWdiv hHinj hbW hsep (i := i) (j := j) hij hn
    exact (hbad hc).elim
  · intro h
    simp at h

end Commons.NumberTheory.MaynardSieve
