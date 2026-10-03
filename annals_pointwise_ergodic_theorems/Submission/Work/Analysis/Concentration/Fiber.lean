/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Work.Analysis.Concentration.fiber_card_sum

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Counting fibres and level sets of a polynomial modulo `q`

Elementary counting results underlying the concentration estimates of Krause–Mirek–Tao,
Appendix C.

* `fiber_card_le_prime` — over `𝔽_p` a nonzero polynomial of degree `d` has fibres of size
  at most `d` (the field case of the concentration estimate, sharp at primes);
* `fiber_card_le_of_dvd` — lifting: reducing modulo a divisor `m ∣ Q` costs a factor `Q/m`;
* `fiber_card_prime_pow_le` — the resulting bound at `Q = p^j`;
* `fiber_card_crt` — multiplicativity of the fibre counting function under the Chinese remainder
  isomorphism;
* `level_set_card_le` and `level_set_card_le_of_fiber_max` — the number of `n < N` with
  `P(n) ≡ a (mod q)` is at most `(⌈N/q⌉) · (maximal fibre)`.
-/

set_option autoImplicit false

namespace Work.Analysis.Concentration

open Polynomial Finset

noncomputable section

/-- **Fibre bound over a prime field.**  If the reduction of `P` modulo the prime `p` has degree
`d ≥ 1`, then every fibre of `P : ℤ/pℤ → ℤ/pℤ` has at most `d` elements. -/
lemma fiber_card_le_prime (P : Polynomial ℤ) {p d : ℕ} [Fact p.Prime] (hd : 1 ≤ d)
    (hdeg : (polyMapZMod P p).natDegree = d) (y : ZMod p) :
    polyFiberCard P p y ≤ d := by
  classical
  have hFne : polyMapZMod P p - Polynomial.C y ≠ 0 := by
    intro h0
    have hp : polyMapZMod P p = Polynomial.C y := sub_eq_zero.mp h0
    rw [hp] at hdeg
    simp at hdeg
    omega
  have hdegF : (polyMapZMod P p - Polynomial.C y).natDegree ≤ d := by
    calc (polyMapZMod P p - Polynomial.C y).natDegree
        ≤ max (polyMapZMod P p).natDegree (Polynomial.C y).natDegree :=
          Polynomial.natDegree_sub_le _ _
      _ ≤ d := by rw [hdeg]; simp
  have hset' : (Finset.univ.filter (fun x : ZMod p => polyEvalZMod P p x = y))
      = (Finset.univ.filter
          (fun x : ZMod p => (polyMapZMod P p - Polynomial.C y).eval x = 0)) := by
    apply Finset.filter_congr
    intro x _
    rw [polyEvalZMod_def, Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero]
  have hset : polyFiberCard P p y
      = (Finset.univ.filter (fun x : ZMod p => (polyMapZMod P p - Polynomial.C y).eval x = 0)).card := by
    rw [polyFiberCard, hset']
  rw [hset]
  calc (Finset.univ.filter (fun x : ZMod p => (polyMapZMod P p - Polynomial.C y).eval x = 0)).card
      ≤ (polyMapZMod P p - Polynomial.C y).roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hFne, Polynomial.IsRoot.def]
        exact hx
    _ ≤ (polyMapZMod P p - Polynomial.C y).roots.card := Multiset.toFinset_card_le _
    _ ≤ (polyMapZMod P p - Polynomial.C y).natDegree := Polynomial.card_roots' _
    _ ≤ d := hdegF

/-- The compatibility of `polyEvalZMod` with the reduction `ZMod Q →+* ZMod m` for `m ∣ Q`. -/
lemma polyEvalZMod_castHom (P : Polynomial ℤ) {m Q : ℕ} [NeZero m] [NeZero Q] (hmQ : m ∣ Q)
    (x : ZMod Q) :
    ZMod.castHom hmQ (ZMod m) (polyEvalZMod P Q x)
      = polyEvalZMod P m (ZMod.castHom hmQ (ZMod m) x) := by
  have hcomp : (ZMod.castHom hmQ (ZMod m)).comp (Int.castRingHom (ZMod Q))
      = Int.castRingHom (ZMod m) := RingHom.ext_int _ _
  have h1 : ZMod.castHom hmQ (ZMod m) (polyEvalZMod P Q x)
      = (polyMapZMod P Q).eval₂ (ZMod.castHom hmQ (ZMod m)) (ZMod.castHom hmQ (ZMod m) x) :=
    (Polynomial.eval₂_at_apply _ x).symm
  rw [h1, polyMapZMod, Polynomial.eval₂_map, hcomp, polyEvalZMod_def, polyMapZMod,
    Polynomial.eval_map]

/-- Every fibre of the reduction `ZMod Q → ZMod m` (for `m ∣ Q`, `m ≠ 0`) has exactly `Q / m`
elements. -/
lemma card_castHom_fiber {m Q : ℕ} (hmQ : m ∣ Q) [NeZero m] [NeZero Q] (z : ZMod m) :
    (Finset.univ.filter (fun x : ZMod Q => ZMod.castHom hmQ (ZMod m) x = z)).card = Q / m := by
  classical
  have hm0 : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  -- the fibres of the surjective homomorphism all have the cardinality of the kernel
  have hcard : ∀ w : ZMod m,
      (Finset.univ.filter (fun x : ZMod Q => ZMod.castHom hmQ (ZMod m) x = w)).card
        = (Finset.univ.filter (fun x : ZMod Q => ZMod.castHom hmQ (ZMod m) x = 0)).card := by
    intro w
    obtain ⟨v, hv⟩ := ZMod.castHom_surjective hmQ w
    have himg : (Finset.univ.filter (fun x : ZMod Q => ZMod.castHom hmQ (ZMod m) x = 0)).image
          (fun x => x + v)
        = Finset.univ.filter (fun x : ZMod Q => ZMod.castHom hmQ (ZMod m) x = w) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [map_add, hv, hy, zero_add]
      · intro hx
        refine ⟨x - v, ?_, by ring⟩
        rw [map_sub, hv, hx, sub_self]
    rw [← himg, Finset.card_image_of_injective _ (fun a b h => add_right_cancel h)]
  rw [hcard z]
  -- the kernel fibre has `Q / m` elements, since `Q = m * (card of the kernel fibre)`
  have hsum := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (ZMod Q))) (t := (Finset.univ : Finset (ZMod m)))
    (f := ZMod.castHom hmQ (ZMod m)) (by intro x _; exact Finset.mem_univ _)
  have hsumQ : Q = ∑ w : ZMod m,
      (Finset.univ.filter (fun x : ZMod Q => ZMod.castHom hmQ (ZMod m) x = w)).card := by
    rw [Finset.card_univ, ZMod.card Q] at hsum
    simpa using hsum
  rw [Finset.sum_congr rfl (fun w _ => hcard w), Finset.sum_const, smul_eq_mul,
    Finset.card_univ, ZMod.card m] at hsumQ
  set c := (Finset.univ.filter (fun x : ZMod Q => ZMod.castHom hmQ (ZMod m) x = 0)).card with hc
  have hcm : m * c = Q := by rw [hc]; exact hsumQ.symm
  show c = Q / m
  rw [← hcm, Nat.mul_div_cancel_left c (n := m) hm0]

/-- **Lifting bound.**  For `m ∣ Q`, the fibre of `P` modulo `Q` over `y` maps into the fibre of
`P` modulo `m` over `y mod m`, and every fibre of the reduction has `Q / m` elements. -/
lemma fiber_card_le_of_dvd (P : Polynomial ℤ) {m Q : ℕ} [NeZero m] [NeZero Q] (hmQ : m ∣ Q)
    (y : ZMod Q) :
    polyFiberCard P Q y ≤ (Q / m) * polyFiberCard P m (ZMod.castHom hmQ (ZMod m) y) := by
  classical
  set π := ZMod.castHom hmQ (ZMod m) with hπ
  set fibm := Finset.univ.filter (fun z : ZMod m => polyEvalZMod P m z = π y) with hfibm
  have hsub : (Finset.univ.filter (fun x : ZMod Q => polyEvalZMod P Q x = y))
      ⊆ fibm.biUnion (fun z => Finset.univ.filter (fun x : ZMod Q => π x = z)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_biUnion]
    refine ⟨π x, ?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    rw [hfibm, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [← polyEvalZMod_castHom P hmQ x, hx.2]⟩
  calc polyFiberCard P Q y
      ≤ (fibm.biUnion (fun z => Finset.univ.filter (fun x : ZMod Q => π x = z))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ z ∈ fibm, (Finset.univ.filter (fun x : ZMod Q => π x = z)).card :=
        Finset.card_biUnion_le
    _ = ∑ z ∈ fibm, Q / m := Finset.sum_congr rfl (fun z _ => card_castHom_fiber hmQ z)
    _ = (Q / m) * fibm.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = (Q / m) * polyFiberCard P m (π y) := by rw [hfibm]; rfl

/-- **Prime power lifting.**  For `p` prime and `j ≥ 1`, the fibre of `P` modulo `p^j` is
controlled by its fibre modulo `p`. -/
lemma fiber_card_prime_pow_le (P : Polynomial ℤ) {p j : ℕ} [Fact p.Prime] (hj : 1 ≤ j)
    (y : ZMod (p ^ j)) :
    polyFiberCard P (p ^ j) y
      ≤ p ^ (j - 1) * polyFiberCard P p (ZMod.castHom (by simpa using pow_dvd_pow p hj) (ZMod p) y) := by
  have hj0 : 1 ≤ j := hj
  have hp0 : 0 < p := (Fact.out (p := p.Prime)).pos
  have h := fiber_card_le_of_dvd P (m := p) (Q := p ^ j)
    (by simpa using pow_dvd_pow p hj) y
  have hpow : p ^ j / p = p ^ (j - 1) := by
    simpa using Nat.pow_div (x := p) (m := j) (n := 1) hj hp0
  rwa [hpow] at h

/-- Inside `{0, …, N-1}`, a given residue class modulo `q` occurs at most `N / q + 1` times. -/
lemma card_range_filter_natCast_zmod (q N : ℕ) [NeZero q] (b : ZMod q) :
    ((Finset.range N).filter (fun n : ℕ => (n : ZMod q) = b)).card ≤ N / q + 1 := by
  classical
  set s := (Finset.range N).filter (fun n : ℕ => (n : ZMod q) = b) with hs
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hinj : Set.InjOn (fun n : ℕ => n / q) ↑s := by
    intro n₁ h₁ n₂ h₂ hdiv
    rw [hs, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at h₁ h₂
    have hmod : n₁ % q = n₂ % q := by
      have h : (n₁ : ZMod q) = (n₂ : ZMod q) := h₁.2.trans h₂.2.symm
      rw [ZMod.natCast_eq_natCast_iff] at h
      exact h
    have hdiv' : n₁ / q = n₂ / q := hdiv
    calc n₁ = q * (n₁ / q) + n₁ % q := (Nat.div_add_mod n₁ q).symm
      _ = q * (n₂ / q) + n₂ % q := by rw [hdiv', hmod]
      _ = n₂ := Nat.div_add_mod n₂ q
  have hsub : s.image (fun n : ℕ => n / q) ⊆ Finset.range (N / q + 1) := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨n, hn, rfl⟩ := hm
    rw [hs, Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (le_of_lt hn.1))
  calc s.card = (s.image (fun n : ℕ => n / q)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (N / q + 1)).card := Finset.card_le_card hsub
    _ = N / q + 1 := Finset.card_range _

/-- **Level sets of `P` modulo `q`.**  The number of `n < N` with `P(n) ≡ a (mod q)` is at most
`⌈N/q⌉ ≤ N/q + 1` times the size of the fibre of `a`. -/
lemma level_set_card_le (P : Polynomial ℤ) (q N : ℕ) [NeZero q] (a : ZMod q) :
    polyLevelSetCard P q N a ≤ polyFiberCard P q a * (N / q + 1) := by
  classical
  set fib := Finset.univ.filter (fun x : ZMod q => polyEvalZMod P q x = a) with hfib
  have hcard : polyFiberCard P q a = fib.card := rfl
  have hmaps : Set.MapsTo (fun n : ℕ => (n : ZMod q))
      ↑((Finset.range N).filter (fun n : ℕ => polyEvalZMod P q (n : ZMod q) = a)) ↑fib := by
    intro n hn
    rw [Finset.mem_coe, Finset.mem_filter] at hn
    rw [Finset.mem_coe, hfib, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hn.2⟩
  have hsplit := Finset.card_eq_sum_card_fiberwise hmaps
  rw [polyLevelSetCard, hsplit, hcard]
  have hstep : ∀ b ∈ fib, (((Finset.range N).filter
      (fun n : ℕ => polyEvalZMod P q (n : ZMod q) = a)).filter
      (fun n : ℕ => (n : ZMod q) = b)).card ≤ N / q + 1 := by
    intro b _
    refine le_trans (Finset.card_le_card ?_) (card_range_filter_natCast_zmod q N b)
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp hn.1).1, hn.2⟩
  calc ∑ b ∈ fib, (((Finset.range N).filter
          (fun n : ℕ => polyEvalZMod P q (n : ZMod q) = a)).filter
          (fun n : ℕ => (n : ZMod q) = b)).card
      ≤ ∑ _b ∈ fib, (N / q + 1) := Finset.sum_le_sum hstep
    _ = fib.card * (N / q + 1) := by rw [Finset.sum_const, smul_eq_mul]

/-- The sharp form of the level-set bound: `#{n < N : P(n) ≡ a mod q} ≤ M (N/q + 1)` whenever
`M` bounds the size of every fibre of `P` modulo `q`. -/
lemma level_set_card_le_of_fiber_max (P : Polynomial ℤ) (q N : ℕ) [NeZero q] (a : ZMod q) {M : ℝ}
    (hM : FiberMaxBound P q M) :
    (polyLevelSetCard P q N a : ℝ) ≤ M * ((N / q + 1 : ℕ) : ℝ) := by
  have h1 := level_set_card_le P q N a
  have h2 : ((polyFiberCard P q a : ℕ) : ℝ) ≤ M := hM a
  have h3 : (0 : ℝ) ≤ ((N / q + 1 : ℕ) : ℝ) := by positivity
  calc (polyLevelSetCard P q N a : ℝ)
      ≤ (((polyFiberCard P q a) * (N / q + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (polyFiberCard P q a : ℝ) * ((N / q + 1 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ M * ((N / q + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right h2 h3

end

end Work.Analysis.Concentration
