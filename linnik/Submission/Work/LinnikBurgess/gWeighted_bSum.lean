import Mathlib
import Submission.Work.LinnikBurgess.card_decompFinset_le
import Submission.Work.LinnikBurgess.sum_sqrtGcd_Icc_le
import Submission.Work.LinnikBurgess.gWeighted_expansion

/-!
# The `g`-weighted sum over triples of nonzero residues

We bound the sum of `∏_l √(gcd m (v l))` over the triples `v : Fin 3 → Fin H` that are
pointwise nonzero and satisfy `g ∣ v 0 * v 1 * v 2`.

The proof is a three-step assembly:

* `gWeighted_expansion` (reindexing / divisor expansion): the left-hand side is at most the sum
  over the decompositions `g = a 0 * a 1 * a 2` (with `a l ∣ g`) of the product over `l` of the
  single-coordinate sums `∑_{u < H, a l ∣ u, u ≠ 0} √(gcd m u)`; the pointwise input is that every
  admissible `v` admits such a decomposition (`exists_fin3_decomp`).
* each single-coordinate sum is at most `(H / a l) · τ(m)` (`factorBound_aux` below, whose
  single-sum input is the delegated `sum_sqrtGcd_Icc_le`: `∑_{t ≤ N} √(gcd m t) ≤ N · τ(m)`);
* there are at most `τ(g)^2` decompositions (`card_decompFinset_le`), and
  `∏_l (H / a l) · τ(m)^3 = H^3 / g · τ(m)^3` because `a 0 a 1 a 2 = g`.
-/

open scoped BigOperators

namespace Work.LinnikBurgess

/-- The decompositions of `g` as an ordered product of three divisors of `g`. -/
def gDecomps (g : ℕ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset (fun _ : Fin 3 => g.divisors)).filter (fun a => ∏ l : Fin 3, a l = g)

lemma mem_gDecomps {g : ℕ} (hg : 0 < g) {a : Fin 3 → ℕ} :
    a ∈ gDecomps g ↔ (∏ l : Fin 3, a l = g) ∧ ∀ l : Fin 3, a l ∣ g := by
  simp only [gDecomps, Finset.mem_filter, Fintype.mem_piFinset, Nat.mem_divisors]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, fun l => (h1 l).1⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun l => ⟨h2 l, hg.ne'⟩, h1⟩


/-- `gcd (a * t) m = gcd t m` when `a` is coprime to `m`. -/
private lemma gcd_mul_left_of_coprime {m a t : ℕ} (h : Nat.Coprime a m) :
    Nat.gcd m (a * t) = Nat.gcd m t := by
  rw [Nat.gcd_comm m (a * t), Nat.Coprime.gcd_mul_left_cancel t h, Nat.gcd_comm t m]

/-- The single-coordinate square-root-gcd sum over the nonzero multiples of `a` below `H`:
`∑_{1 ≤ u < H, a ∣ u} √(gcd m u) ≤ (H/a)·τ(m)`, for `a ∣ g` with `gcd(m,g) = 1`.

Write `u = a t` with `1 ≤ t ≤ ⌊(H-1)/a⌋`; since `a` is coprime to `m`,
`gcd(m, a t) = gcd(m, t)`, and `sum_sqrtGcd_Icc_le` bounds the resulting sum by
`⌊(H-1)/a⌋ · τ(m) ≤ (H/a) · τ(m)`. -/
private lemma factorBound_aux {m g H a : ℕ} (hm : 0 < m) (hmg : Nat.Coprime m g) (hg : 0 < g)
    (ha : a ∣ g) :
    (∑ u : Fin H, (if a ∣ (u : ℕ) then (if (u : ℕ) ≠ 0 then Real.sqrt (((Nat.gcd m (u : ℕ) : ℕ)) : ℝ) else 0) else 0))
      ≤ (H : ℝ) / (a : ℝ) * ((m.divisors.card : ℕ) : ℝ) := by
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos ha hg
  have ham : Nat.Coprime a m := Nat.Coprime.coprime_dvd_left ha hmg.symm
  set S : Finset (Fin H) := Finset.univ.filter (fun u : Fin H => a ∣ (u : ℕ) ∧ (u : ℕ) ≠ 0) with hS
  have h1 : (∑ u : Fin H, (if a ∣ (u : ℕ) then (if (u : ℕ) ≠ 0 then Real.sqrt (((Nat.gcd m (u : ℕ) : ℕ)) : ℝ) else 0) else 0))
      = ∑ u ∈ S, Real.sqrt (((Nat.gcd m (u : ℕ) : ℕ)) : ℝ) := by
    rw [hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hh1 : a ∣ (u : ℕ) <;> by_cases hh2 : (u : ℕ) ≠ 0 <;> simp [hh1, hh2]
  rw [h1]
  have h2 : (∑ u ∈ S, Real.sqrt (((Nat.gcd m (u : ℕ) : ℕ)) : ℝ))
      = ∑ t ∈ Finset.Icc 1 ((H - 1) / a), Real.sqrt (((Nat.gcd m (a * t) : ℕ)) : ℝ) := by
    refine Finset.sum_bij (fun (u : Fin H) (_ : u ∈ S) => (u : ℕ) / a) ?_ ?_ ?_ ?_
    · intro u hu
      rw [hS, Finset.mem_filter] at hu
      obtain ⟨-, hu1, hu2⟩ := hu
      rw [Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · rw [Nat.one_le_div_iff ha0]
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero hu2) hu1
      · exact Nat.div_le_div_right (Nat.le_sub_one_of_lt u.isLt)
    · intro u1 hu1 u2 hu2 heq
      rw [hS, Finset.mem_filter] at hu1 hu2
      have e1 : a * ((u1 : ℕ) / a) = (u1 : ℕ) := Nat.mul_div_cancel' hu1.2.1
      have e2 : a * ((u2 : ℕ) / a) = (u2 : ℕ) := Nat.mul_div_cancel' hu2.2.1
      apply Fin.ext
      rw [← e1, ← e2, heq]
    · intro t ht
      rw [Finset.mem_Icc] at ht
      obtain ⟨ht1, ht2⟩ := ht
      have hH : 0 < H := by
        by_contra hcon
        have h0 : H = 0 := Nat.eq_zero_of_not_pos hcon
        rw [h0] at ht2
        simp at ht2
        omega
      have hle : a * t ≤ H - 1 := by
        have := (Nat.le_div_iff_mul_le ha0).mp ht2
        rwa [Nat.mul_comm] at this
      have hlt : a * t < H := by omega
      refine ⟨⟨a * t, hlt⟩, ?_, ?_⟩
      · rw [hS, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, dvd_mul_right a t, by positivity⟩
      · show (⟨a * t, hlt⟩ : Fin H).val / a = t
        exact Nat.mul_div_right t ha0
    · intro u hu
      rw [hS, Finset.mem_filter] at hu
      have e1 : a * ((u : ℕ) / a) = (u : ℕ) := Nat.mul_div_cancel' hu.2.1
      show Real.sqrt (((Nat.gcd m ((u : ℕ)) : ℕ)) : ℝ)
        = Real.sqrt (((Nat.gcd m (a * ((u : ℕ) / a)) : ℕ)) : ℝ)
      rw [e1]
  have h3 : (∑ t ∈ Finset.Icc 1 ((H - 1) / a), Real.sqrt (((Nat.gcd m (a * t) : ℕ)) : ℝ))
      = ∑ t ∈ Finset.Icc 1 ((H - 1) / a), Real.sqrt (((Nat.gcd m t : ℕ)) : ℝ) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [gcd_mul_left_of_coprime ham]
  have h4 := sum_sqrtGcd_Icc_le m ((H - 1) / a) hm
  have h5 : ((((H - 1) / a : ℕ)) : ℝ) ≤ (H : ℝ) / (a : ℝ) := by
    calc ((((H - 1) / a : ℕ)) : ℝ) ≤ (((H - 1 : ℕ)) : ℝ) / (a : ℝ) := Nat.cast_div_le
      _ ≤ (H : ℝ) / (a : ℝ) :=
          div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le H 1) (by positivity)
  calc (∑ u ∈ S, Real.sqrt (((Nat.gcd m (u : ℕ) : ℕ)) : ℝ))
      = ∑ t ∈ Finset.Icc 1 ((H - 1) / a), Real.sqrt (((Nat.gcd m (a * t) : ℕ)) : ℝ) := h2
    _ = ∑ t ∈ Finset.Icc 1 ((H - 1) / a), Real.sqrt (((Nat.gcd m t : ℕ)) : ℝ) := h3
    _ ≤ (((H - 1) / a : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ) := h4
    _ ≤ (H : ℝ) / (a : ℝ) * ((m.divisors.card : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)

/-- The `g`-weighted sum over triples of nonzero residues.  For `0 < m`, `gcd(m,g) = 1`, the sum of `∏_l √gcd(m, v_l)` over `v : Fin 3 → Fin H` with `g ∣ ∏_l v_l` and every `v_l ≠ 0` is at most `τ(g)^2 · H^3/g · τ(m)^3`.  (One expands `g = g_0g_1g_2` with `g_l ∣ v_l` — at most `τ(g)^2` triples — and uses `∑_{1 ≤ t ≤ N} √gcd(m, g_l t) = ∑_{t ≤ N} √gcd(m,t) ≤ N τ(m)` for `gcd(m,g_l)=1`.) -/
theorem gWeighted_bSum {m g H : ℕ} (hm : 0 < m) (hmg : Nat.Coprime m g) (hg : 0 < g) :
    (∑ v : Fin 3 → Fin H, (if (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ ((g : ℤ) ∣ ∏ l : Fin 3, ((v l : ℕ) : ℤ))
        then ∏ l : Fin 3, Real.sqrt (((Nat.gcd m (v l : ℕ)) : ℕ) : ℝ) else (0:ℝ)))
      ≤ ((g.divisors.card : ℝ)) ^ 2 * ((H : ℝ) ^ 3 / (g : ℝ)) * ((m.divisors.card : ℝ)) ^ 3 := by
  -- the ℤ-divisibility condition is the ℕ-divisibility condition
  have hcond : ∀ v : Fin 3 → Fin H,
      ((∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ ((g : ℤ) ∣ ∏ l : Fin 3, ((v l : ℕ) : ℤ)))
        ↔ ((∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ (g ∣ ∏ l : Fin 3, (v l : ℕ))) := by
    intro v
    have h1 : (∏ l : Fin 3, ((v l : ℕ) : ℤ)) = ((↑(∏ l : Fin 3, (v l : ℕ))) : ℤ) := by
      rw [← Nat.cast_prod (f := fun l : Fin 3 => (v l : ℕ)) Finset.univ]
    rw [h1, Int.ofNat_dvd]
  have hLHS : (∑ v : Fin 3 → Fin H, (if (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ ((g : ℤ) ∣ ∏ l : Fin 3, ((v l : ℕ) : ℤ))
        then ∏ l : Fin 3, Real.sqrt (((Nat.gcd m (v l : ℕ)) : ℕ) : ℝ) else (0:ℝ)))
      = ∑ v : Fin 3 → Fin H, (if (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ (g ∣ ∏ l : Fin 3, (v l : ℕ))
        then ∏ l : Fin 3, Real.sqrt (((Nat.gcd m (v l : ℕ)) : ℕ) : ℝ) else (0:ℝ)) := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases h : (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ ((g : ℤ) ∣ ∏ l : Fin 3, ((v l : ℕ) : ℤ))
    · rw [if_pos h, if_pos ((hcond v).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((hcond v).mpr hh))]
  -- the divisor expansion
  have hexp := gWeighted_expansion (m := m) (g := g) (H := H) hg
  have hstep : (∑ v : Fin 3 → Fin H, (if (∀ l : Fin 3, (v l : ℕ) ≠ 0) ∧ (g ∣ ∏ l : Fin 3, (v l : ℕ))
        then ∏ l : Fin 3, Real.sqrt (((Nat.gcd m (v l : ℕ)) : ℕ) : ℝ) else (0:ℝ)))
      ≤ ∑ a ∈ gDecomps g, ∏ l : Fin 3, ∑ u : Fin H,
          (if (a l) ∣ (u : ℕ) then (if (u : ℕ) ≠ 0 then Real.sqrt (((Nat.gcd m (u : ℕ)) : ℕ) : ℝ) else 0) else 0) := by
    simpa only [gDecomps] using hexp
  -- each single-coordinate sum is `≤ H / a l · τ(m)`, and the product is `H^3/g · τ(m)^3`
  have hsum : (∑ a ∈ gDecomps g, ∏ l : Fin 3, ∑ u : Fin H,
        (if (a l) ∣ (u : ℕ) then (if (u : ℕ) ≠ 0 then Real.sqrt (((Nat.gcd m (u : ℕ)) : ℕ) : ℝ) else 0) else 0))
      ≤ ((g.divisors.card : ℝ)) ^ 2 * ((H : ℝ) ^ 3 / (g : ℝ)) * ((m.divisors.card : ℝ)) ^ 3 := by
    calc (∑ a ∈ gDecomps g, ∏ l : Fin 3, ∑ u : Fin H,
          (if (a l) ∣ (u : ℕ) then (if (u : ℕ) ≠ 0 then Real.sqrt (((Nat.gcd m (u : ℕ)) : ℕ) : ℝ) else 0) else 0))
        ≤ ∑ _a ∈ gDecomps g, ((H : ℝ) ^ 3 / (g : ℝ) * ((m.divisors.card : ℝ)) ^ 3) := by
          apply Finset.sum_le_sum
          intro a ha
          rw [mem_gDecomps hg] at ha
          obtain ⟨haprod, hadvd⟩ := ha
          calc ∏ l : Fin 3, (∑ u : Fin H,
                (if (a l) ∣ (u : ℕ) then (if (u : ℕ) ≠ 0 then Real.sqrt (((Nat.gcd m (u : ℕ)) : ℕ) : ℝ) else 0) else 0))
              ≤ ∏ l : Fin 3, ((H : ℝ) / (a l : ℝ) * ((m.divisors.card : ℕ) : ℝ)) := by
                apply Finset.prod_le_prod₀
                · intro l _
                  exact Finset.sum_nonneg (fun u _ => by
                    by_cases h1 : (a l) ∣ (u : ℕ) <;> by_cases h2 : (u : ℕ) ≠ 0 <;>
                      simp [h1, h2, Real.sqrt_nonneg])
                · intro l _
                  exact factorBound_aux (m := m) (g := g) (H := H) (a := a l) hm hmg hg (hadvd l)
            _ = (H : ℝ) ^ 3 / (g : ℝ) * ((m.divisors.card : ℝ)) ^ 3 := by
                rw [Finset.prod_mul_distrib, Finset.prod_div_distrib]
                rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                have hcast : (∏ l : Fin 3, (a l : ℝ)) = (g : ℝ) := by rw [← haprod]; simp
                rw [hcast]
      _ = ((gDecomps g).card : ℝ) * ((H : ℝ) ^ 3 / (g : ℝ) * ((m.divisors.card : ℝ)) ^ 3) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((g.divisors.card : ℝ)) ^ 2 * ((H : ℝ) ^ 3 / (g : ℝ)) * ((m.divisors.card : ℝ)) ^ 3 := by
          have hcard : (((gDecomps g).card : ℝ)) ≤ ((g.divisors.card : ℝ)) ^ 2 := by
            simpa only [gDecomps] using card_decompFinset_le (g := g) hg
          have hnn : 0 ≤ (H : ℝ) ^ 3 / (g : ℝ) * ((m.divisors.card : ℝ)) ^ 3 := by positivity
          calc ((gDecomps g).card : ℝ) * ((H : ℝ) ^ 3 / (g : ℝ) * ((m.divisors.card : ℝ)) ^ 3)
              ≤ ((g.divisors.card : ℝ)) ^ 2
                  * ((H : ℝ) ^ 3 / (g : ℝ) * ((m.divisors.card : ℝ)) ^ 3) :=
                mul_le_mul_of_nonneg_right hcard hnn
            _ = ((g.divisors.card : ℝ)) ^ 2 * ((H : ℝ) ^ 3 / (g : ℝ))
                  * ((m.divisors.card : ℝ)) ^ 3 := by ring
  rw [hLHS]
  exact le_trans hstep hsum

end Work.LinnikBurgess
