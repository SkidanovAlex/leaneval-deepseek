import Mathlib
import Submission.Work.KMTPlan.A6.ConcAux.Defs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Counting the balls covering the fibre of a polynomial modulo `p^k`

This file develops the arithmetic used to cover `fibre p k G` by `max 1 G.natDegree` many
`p`-adic balls, along the recursion `x = r + p·t` (`r = x mod p`): the fibre above a residue
`r` is described by the rescaled polynomial `rescale p G r`, whose fibre at level `k-1` (after
removing the `p`-content) has, by induction, at most `⟨multiplicity of r⟩` balls.
-/

namespace Work.KMTPlan.A6.ConcAux

open Polynomial Finset

noncomputable section

variable {p : ℕ}

/-! ## 1. Elementary `p`-adic arithmetic -/

lemma p_two_le {p : ℕ} [Fact p.Prime] : 2 ≤ p := (Fact.out (p := p.Prime)).two_le

lemma p_pos {p : ℕ} [Fact p.Prime] : 0 < p := by have := p_two_le (p := p); omega

lemma p_int_ne_zero {p : ℕ} [Fact p.Prime] : (p : ℤ) ≠ 0 := by
  have h : (0 : ℤ) < p := by exact_mod_cast p_pos (p := p)
  omega

lemma eq_add_mul_div {p r x : ℕ} (hx : x % p = r) : x = r + p * (x / p) := by
  have h := Nat.div_add_mod' x p
  rw [hx, mul_comm] at h
  rw [add_comm]
  exact h.symm

lemma div_lt_of_lt_pow_succ {p x j : ℕ} (hp : 0 < p) (hx : x < p ^ (j + 1)) :
    x / p < p ^ j := by
  by_contra h
  have h1 : p ^ j ≤ x / p := not_lt.mp h
  have h2 := Nat.mul_le_mul_right p h1
  have h3 := Nat.div_mul_le_self x p
  have h4 : p ^ (j + 1) ≤ x := by
    rw [pow_succ]
    exact le_trans h2 h3
  omega

/-- Congruent arguments give congruent values. -/
lemma dvd_eval_sub_of_dvd_sub {p : ℕ} (Q : ℤ[X]) {n : ℕ} {x y : ℕ}
    (h : (p : ℤ) ^ n ∣ (x : ℤ) - (y : ℤ)) :
    (p : ℤ) ^ n ∣ Q.eval (x : ℤ) - Q.eval (y : ℤ) :=
  dvd_trans h (Polynomial.sub_dvd_eval_sub (x : ℤ) (y : ℤ) Q)

lemma dvd_sub_mod {p : ℕ} (n x : ℕ) :
    (p : ℤ) ^ n ∣ (x : ℤ) - ((x % p ^ n : ℕ) : ℤ) := by
  have hnat : p ^ n * (x / p ^ n) + x % p ^ n = x := by
    rw [mul_comm]; exact Nat.div_add_mod' x (p ^ n)
  have hint : (p : ℤ) ^ n * ((x / p ^ n : ℕ) : ℤ) + ((x % p ^ n : ℕ) : ℤ) = (x : ℤ) := by
    exact_mod_cast hnat
  exact ⟨((x / p ^ n : ℕ) : ℤ), by linarith⟩

/-- Reducing the argument modulo `p^n` preserves divisibility of values. -/
lemma dvd_eval_mod {p : ℕ} (Q : ℤ[X]) {n x : ℕ} (h : (p : ℤ) ^ n ∣ Q.eval (x : ℤ)) :
    (p : ℤ) ^ n ∣ Q.eval ((x % p ^ n : ℕ) : ℤ) := by
  have h1 := dvd_eval_sub_of_dvd_sub (p := p) Q (dvd_sub_mod (p := p) n x)
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h1
  exact ⟨a - b, by linarith⟩

lemma dvd_eval_of_dvd_eval_mod {p : ℕ} (Q : ℤ[X]) {n x : ℕ}
    (h : (p : ℤ) ^ n ∣ Q.eval ((x % p ^ n : ℕ) : ℤ)) :
    (p : ℤ) ^ n ∣ Q.eval (x : ℤ) := by
  have h1 := dvd_eval_sub_of_dvd_sub (p := p) Q (dvd_sub_mod (p := p) n x)
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h1
  exact ⟨a + b, by linarith⟩

lemma dvd_sub_of_dvd_mod_sub {p : ℕ} {m n x t : ℕ} (hmn : m ≤ n)
    (h : (p : ℤ) ^ m ∣ ((x % p ^ n : ℕ) : ℤ) - (t : ℤ)) :
    (p : ℤ) ^ m ∣ (x : ℤ) - (t : ℤ) := by
  have h1 : (p : ℤ) ^ m ∣ (x : ℤ) - ((x % p ^ n : ℕ) : ℤ) :=
    dvd_trans (pow_dvd_pow (p : ℤ) hmn) (dvd_sub_mod (p := p) n x)
  have heq : (x : ℤ) - (t : ℤ) =
      ((x : ℤ) - ((x % p ^ n : ℕ) : ℤ)) + (((x % p ^ n : ℕ) : ℤ) - (t : ℤ)) := by ring
  rw [heq]; exact dvd_add h1 h

lemma dvd_mod_sub_of_dvd_sub {p : ℕ} {m n x t : ℕ} (hmn : m ≤ n)
    (h : (p : ℤ) ^ m ∣ (x : ℤ) - (t : ℤ)) :
    (p : ℤ) ^ m ∣ ((x % p ^ n : ℕ) : ℤ) - (t : ℤ) := by
  have h2 : (p : ℤ) ^ m ∣ (x : ℤ) - ((x % p ^ n : ℕ) : ℤ) :=
    dvd_trans (pow_dvd_pow (p : ℤ) hmn) (dvd_sub_mod (p := p) n x)
  have h1 : (p : ℤ) ^ m ∣ ((x % p ^ n : ℕ) : ℤ) - (x : ℤ) := by
    simpa using dvd_neg.mpr h2
  have heq : ((x % p ^ n : ℕ) : ℤ) - (t : ℤ) =
      (((x % p ^ n : ℕ) : ℤ) - (x : ℤ)) + ((x : ℤ) - (t : ℤ)) := by ring
  rw [heq]; exact dvd_add h1 h

/-- If `p ∣ x - r` with `0 ≤ r < p` then `x % p = r`. -/
lemma mod_eq_of_dvd_sub {p r x : ℕ} (hr : r < p) (h : (p : ℤ) ∣ (x : ℤ) - (r : ℤ)) :
    x % p = r := by
  obtain ⟨c, hc⟩ := h
  have hx : (x : ℤ) = (r : ℤ) + (p : ℤ) * c := by linarith
  have hp1 : (1 : ℤ) ≤ (p : ℤ) := by omega
  have hc0 : (0 : ℤ) ≤ c := by
    by_contra hneg
    have hneg' : c < 0 := not_le.mp hneg
    have : (p : ℤ) * c ≤ -(p : ℤ) := by nlinarith
    have hxlt : (x : ℤ) < (r : ℤ) := by linarith [Int.natCast_nonneg x]
    have hrx : (r : ℤ) < (p : ℤ) := by exact_mod_cast hr
    have hxnn : (0 : ℤ) ≤ (x : ℤ) := Int.natCast_nonneg x
    omega
  obtain ⟨c', hc'⟩ : ∃ c' : ℕ, c = (c' : ℤ) := ⟨c.toNat, by omega⟩
  have hx' : x = r + p * c' := by
    rw [hc', ← Int.natCast_mul, ← Int.natCast_add] at hx
    exact_mod_cast hx
  rw [hx', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- The digit correspondence: a ball of level `m+1` around `r + p t` (with `x ≡ r mod p`)
corresponds to a ball of level `m` around `t` for the shifted variable `x / p`. -/
lemma dvd_sub_iff_dvd_div_sub {p : ℕ} [Fact p.Prime] {m r x t : ℕ} (hx : x % p = r) :
    (p : ℤ) ^ (m + 1) ∣ (x : ℤ) - (((r + p * t : ℕ)) : ℤ) ↔
      (p : ℤ) ^ m ∣ ((x / p : ℕ) : ℤ) - (t : ℤ) := by
  have hxeq : (x : ℤ) = (r : ℤ) + (p : ℤ) * ((x / p : ℕ) : ℤ) := by
    have h := eq_add_mul_div (p := p) hx
    exact_mod_cast h
  have h2 : (((r + p * t : ℕ)) : ℤ) = (r : ℤ) + (p : ℤ) * (t : ℤ) := by push_cast; ring
  have key : (x : ℤ) - (((r + p * t : ℕ)) : ℤ) =
      (p : ℤ) * (((x / p : ℕ) : ℤ) - (t : ℤ)) := by
    rw [hxeq, h2]; ring
  rw [key, pow_succ', mul_dvd_mul_iff_left (p_int_ne_zero (p := p))]

/-- A nonzero polynomial whose reduction mod `p` is a polynomial of degree `≤ s`. -/
lemma natDegree_map_le_of_dvd_coeff {p : ℕ} [Fact p.Prime] {Ŵ : ℤ[X]} {s : ℕ}
    (h : ∀ i, s < i → (p : ℤ) ∣ Ŵ.coeff i) :
    (Ŵ.map (Int.castRingHom (ZMod p))).natDegree ≤ s := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_map]
  have h1 : (p : ℤ) ∣ Ŵ.coeff N := h N hN
  obtain ⟨c, hc⟩ := h1
  rw [hc, map_mul]
  have hp0 : (Int.castRingHom (ZMod p)) (p : ℤ) = 0 := by
    show ((p : ℤ) : ZMod p) = 0
    rw [Int.cast_natCast, ZMod.natCast_self]
  rw [hp0, zero_mul]

/-- The reduction mod `p` of a primitive polynomial is nonzero. -/
lemma map_ne_zero_of_primitive {p : ℕ} [Fact p.Prime] {H : ℤ[X]}
    (h : ∃ i, ¬ (p : ℤ) ∣ H.coeff i) :
    H.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hzero
  obtain ⟨i, hi⟩ := h
  have hcoe : ((H.coeff i : ℤ) : ZMod p) = 0 := by
    have hc := congrArg (fun (Q : (ZMod p)[X]) => Q.coeff i) hzero
    have hc' : (Int.castRingHom (ZMod p)) (H.coeff i) = 0 := by
      simpa only [coeff_map, coeff_zero] using hc
    exact hc'
  exact hi ((ZMod.intCast_zmod_eq_zero_iff_dvd (H.coeff i) p).mp hcoe)

/-- A root of `H` mod `p` has positive multiplicity in the reduction. -/
lemma one_le_rootMultiplicity {p : ℕ} [Fact p.Prime] {H : ℤ[X]} {r : ℕ}
    (hmap : H.map (Int.castRingHom (ZMod p)) ≠ 0)
    (hr : (p : ℤ) ∣ H.eval (r : ℤ)) :
    1 ≤ (H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p) := by
  have hroot : (H.map (Int.castRingHom (ZMod p))).IsRoot (r : ZMod p) := by
    rw [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_natCast]
    obtain ⟨c, hc⟩ := hr
    rw [hc, map_mul]
    have hp0 : (Int.castRingHom (ZMod p)) (p : ℤ) = 0 := by
      show ((p : ℤ) : ZMod p) = 0
      rw [Int.cast_natCast, ZMod.natCast_self]
    rw [hp0, zero_mul]
  have := (Polynomial.rootMultiplicity_pos hmap).mpr hroot
  omega

end

end Work.KMTPlan.A6.ConcAux

namespace Work.KMTPlan.A6.ConcAux

open Polynomial Finset

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- `p^j ∣ p^a * A` implies `p^(j-a) ∣ A` (with truncated subtraction). -/
lemma dvd_of_dvd_pow_mul {p : ℕ} [Fact p.Prime] {a j : ℕ} {A : ℤ}
    (h : (p : ℤ) ^ j ∣ (p : ℤ) ^ a * A) : (p : ℤ) ^ (j - a) ∣ A := by
  by_cases ha : a ≤ j
  · have hsplit : (p : ℤ) ^ j = (p : ℤ) ^ (j - a) * (p : ℤ) ^ a := by
      rw [← pow_add, Nat.sub_add_cancel ha]
    rw [hsplit, mul_comm ((p : ℤ) ^ a) A] at h
    exact (mul_dvd_mul_iff_right (pow_ne_zero _ (p_int_ne_zero (p := p)))).mp h
  · rw [Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp ha)), pow_zero]
    exact one_dvd A

/-- The `p^m`-divisibility on the rescaled side. -/
lemma rescale_eval_mul' (H : ℤ[X]) (r : ℤ) (hp : (p : ℤ) ∣ H.eval r) (t : ℤ) :
    (p : ℤ) * (rescale p H r).eval t = H.eval (r + (p : ℤ) * t) := by
  have h := congrArg (fun q : ℤ[X] => q.eval t) (rescale_comp p H r hp)
  simpa [eval_comp, eval_add, eval_mul] using h.symm

/-- **Main induction.** Assuming the four arithmetic inputs (the rescaled–content decomposition,
the Taylor/multiplicity bridge, the multiplicity sum bound, and the content decomposition), every
fibre of a primitive polynomial is covered by at most `max 1 (deg mod p)` balls contained in it. -/
theorem exists_cover_of_inputs (p : ℕ) [Fact p.Prime]
    (hB : ∀ (H : ℤ[X]) (r : ℤ) (s : ℕ), 1 ≤ s → (p : ℤ) ∣ H.eval r →
      (∀ i, i < s → (p : ℤ) ∣ taylorCoeff H r i) → ¬ ((p : ℤ) ∣ taylorCoeff H r s) →
      ∃ a : ℕ, ∃ Ŵ : ℤ[X], rescale p H r = C ((p : ℤ) ^ a) * Ŵ ∧
        (∃ i, ¬ (p : ℤ) ∣ Ŵ.coeff i) ∧ (∀ i, s < i → (p : ℤ) ∣ Ŵ.coeff i))
    (hM : ∀ (H : ℤ[X]) (r : ℕ), H.map (Int.castRingHom (ZMod p)) ≠ 0 →
      (∀ i, i < (H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p) →
          (p : ℤ) ∣ taylorCoeff H r i) ∧
      ((p : ℤ) ∣ H.eval (r : ℤ) →
          ¬ ((p : ℤ) ∣ taylorCoeff H r
              ((H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p)))))
    (hS : ∀ (H : ℤ[X]), H.map (Int.castRingHom (ZMod p)) ≠ 0 →
      ∑ r ∈ roots p H, (H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p)
        ≤ (H.map (Int.castRingHom (ZMod p))).natDegree)
    (hD : ∀ (H : ℤ[X]), ∃ c : ℕ, ∃ Ĝ : ℤ[X], H = C ((p : ℤ) ^ c) * Ĝ ∧
      (Ĝ = 0 ∨ ∃ i, ¬ (p : ℤ) ∣ Ĝ.coeff i)) :
    ∀ (k : ℕ) (H : ℤ[X]), (∃ i, ¬ (p : ℤ) ∣ H.coeff i) →
      ∃ C : Finset (ℕ × ℕ),
        (∀ am ∈ C, am.2 ≤ k ∧ ball p k am.2 am.1 ⊆ fibre p k H) ∧
        (∀ x ∈ fibre p k H, ∃ am ∈ C, x ∈ ball p k am.2 am.1) ∧
        C.card ≤ max 1 ((H.map (Int.castRingHom (ZMod p))).natDegree) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro H hprim
    rcases k with _ | j
    · -- level 0
      refine ⟨{(0, 0)}, ?_, ?_, ?_⟩
      · intro am ham
        rw [Finset.mem_singleton] at ham
        subst ham
        refine ⟨le_refl 0, ?_⟩
        intro x
        simp only [mem_ball, mem_fibre, pow_zero, one_dvd, and_true]
        omega
      · intro x hx
        rw [mem_fibre] at hx
        exact ⟨(0, 0), Finset.mem_singleton_self 0,
          by rw [mem_ball]; exact ⟨hx.1, by simp⟩⟩
      · simp
    · -- level j + 1
      have hmap_ne : H.map (Int.castRingHom (ZMod p)) ≠ 0 := map_ne_zero_of_primitive hprim
      have hdata : ∀ r : ↥(roots p H), ∃ (a : ℕ) (Ŵ : ℤ[X]),
          rescale p H r = C ((p : ℤ) ^ a) * Ŵ ∧ (∃ i, ¬ (p : ℤ) ∣ Ŵ.coeff i) ∧
          (∀ i, (H.map (Int.castRingHom (ZMod p))).rootMultiplicity ((r : ℕ) : ZMod p) < i →
            (p : ℤ) ∣ Ŵ.coeff i) := by
        intro r
        have hrp : (p : ℤ) ∣ H.eval (((r : ℕ)) : ℤ) := (mem_roots.mp r.2).2
        have h1 := (hM H (r : ℕ) hmap_ne).1
        have h2 := (hM H (r : ℕ) hmap_ne).2 hrp
        exact hB H (((r : ℕ)) : ℤ) _ (one_le_rootMultiplicity hmap_ne hrp) hrp h1 h2
      choose A W hW using hdata
      have hchild : ∀ r : ↥(roots p H), ∃ C : Finset (ℕ × ℕ),
          (∀ am ∈ C, am.2 ≤ j - A r ∧ ball p (j - A r) am.2 am.1 ⊆ fibre p (j - A r) (W r)) ∧
          (∀ x ∈ fibre p (j - A r) (W r), ∃ am ∈ C, x ∈ ball p (j - A r) am.2 am.1) ∧
          C.card ≤ max 1 (((W r).map (Int.castRingHom (ZMod p))).natDegree) :=
        fun r => ih (j - A r) (by have := Nat.sub_le j (A r); omega) (W r) (hW r).2.1
      choose Cv hCv using hchild
      refine ⟨(roots p H).attach.biUnion
        (fun r => (Cv r).image (fun am => (((r : ℕ)) + p * am.1, am.2 + 1))), ?_, ?_, ?_⟩
      · -- containment of the lifted balls
        intro am ham
        obtain ⟨r, -, ham'⟩ := Finset.mem_biUnion.mp ham
        obtain ⟨⟨t, m⟩, htc, hcm⟩ := Finset.mem_image.mp ham'
        have key : (m + 1 ≤ j + 1 ∧
              ball p (j + 1) (m + 1) (((r : ℕ)) + p * t) ⊆ fibre p (j + 1) H) := by
          obtain ⟨hmle, hballsub⟩ := (hCv r).1 (t, m) htc
          refine ⟨by omega, ?_⟩
          intro x hx
          rw [mem_ball] at hx
          rw [mem_fibre]
          refine ⟨hx.1, ?_⟩
          have hpdiv : (p : ℤ) ∣ (x : ℤ) - ((((r : ℕ)) + p * t : ℕ) : ℤ) := by
            have hx2 := hx.2
            have hsplit : (p : ℤ) ^ (m + 1) = (p : ℤ) * (p : ℤ) ^ m := by
              rw [add_comm, pow_add, pow_one]
            rw [hsplit] at hx2
            exact dvd_trans (dvd_mul_right _ _) hx2
          have hrx : (p : ℤ) ∣ (x : ℤ) - (((r : ℕ)) : ℤ) := by
            have h1 : (p : ℤ) ∣ ((((r : ℕ)) + p * t : ℕ) : ℤ) - (((r : ℕ)) : ℤ) := by
              have heq : ((((r : ℕ)) + p * t : ℕ) : ℤ) - (((r : ℕ)) : ℤ) = (p : ℤ) * (t : ℤ) := by
                push_cast; ring
              rw [heq]
              exact dvd_mul_right _ _
            have heq : (x : ℤ) - (((r : ℕ)) : ℤ) =
                ((x : ℤ) - ((((r : ℕ)) + p * t : ℕ) : ℤ)) +
                  (((((r : ℕ)) + p * t : ℕ) : ℤ) - (((r : ℕ)) : ℤ)) := by ring
            rw [heq]; exact dvd_add hpdiv h1
          have hxmod : x % p = (r : ℕ) :=
            mod_eq_of_dvd_sub (mem_roots.mp r.2).1 hrx
          have hdiv : (p : ℤ) ^ m ∣ ((x / p : ℕ) : ℤ) - (t : ℤ) :=
            (dvd_sub_iff_dvd_div_sub (p := p) hxmod).mp hx.2
          have hy : ((x / p) % p ^ (j - A r)) ∈ ball p (j - A r) m t := by
            rw [mem_ball]
            refine ⟨Nat.mod_lt _ (pow_pos (p_pos (p := p)) _), ?_⟩
            exact dvd_mod_sub_of_dvd_sub (p := p) hmle hdiv
          have hyfib : ((x / p) % p ^ (j - A r)) ∈ fibre p (j - A r) (W r) := hballsub hy
          rw [mem_fibre] at hyfib
          have hWev : (p : ℤ) ^ (j - A r) ∣ (W r).eval (((x / p : ℕ)) : ℤ) :=
            dvd_eval_of_dvd_eval_mod (W r) hyfib.2
          have hres : (p : ℤ) ^ j ∣ (rescale p H ((r : ℕ) : ℤ)).eval (((x / p : ℕ)) : ℤ) := by
            rw [(hW r).1, eval_mul, eval_C]
            by_cases hAj : A r ≤ j
            · have hsplit : (p : ℤ) ^ j = (p : ℤ) ^ (j - A r) * (p : ℤ) ^ (A r) := by
                rw [← pow_add]; congr 1; omega
              rw [hsplit, mul_comm ((p : ℤ) ^ (A r)) ((W r).eval (((x / p : ℕ)) : ℤ))]
              exact mul_dvd_mul_right hWev _
            · have hle : j ≤ A r := le_of_lt (not_le.mp hAj)
              have hsplit : (p : ℤ) ^ (A r) = (p : ℤ) ^ j * (p : ℤ) ^ (A r - j) := by
                rw [← pow_add]; congr 1; omega
              rw [hsplit, mul_assoc]
              exact dvd_mul_right _ _
          have hxcast : ((r : ℕ) : ℤ) + (p : ℤ) * (((x / p : ℕ)) : ℤ) = (x : ℤ) := by
            have h := eq_add_mul_div (p := p) hxmod
            exact_mod_cast h.symm
          have hmuleq : H.eval (((r : ℕ) : ℤ) + (p : ℤ) * (((x / p : ℕ)) : ℤ)) =
              (p : ℤ) * (rescale p H ((r : ℕ) : ℤ)).eval (((x / p : ℕ)) : ℤ) := by
            rw [rescale_eval_mul' (p := p) H ((r : ℕ) : ℤ) (mem_roots.mp r.2).2]
          have h2 : (p : ℤ) * (p : ℤ) ^ j ∣
              (p : ℤ) * (rescale p H ((r : ℕ) : ℤ)).eval (((x / p : ℕ)) : ℤ) :=
            mul_dvd_mul_left _ hres
          rw [← hmuleq, hxcast] at h2
          rwa [show (p : ℤ) * (p : ℤ) ^ j = (p : ℤ) ^ (j + 1) by
            rw [add_comm, pow_add, pow_one]] at h2
        rw [← hcm]
        exact key
      · -- covering
        intro x hx
        rw [mem_fibre] at hx
        have hxroot : x % p ∈ roots p H := by
          rw [mem_roots]
          refine ⟨Nat.mod_lt _ (p_pos (p := p)), ?_⟩
          have h1 : (p : ℤ) ^ (1 : ℕ) ∣ H.eval ((x % p ^ (1 : ℕ) : ℕ) : ℤ) :=
            dvd_eval_mod (p := p) H (n := 1)
              (dvd_trans (pow_dvd_pow (p : ℤ) (by omega : 1 ≤ j + 1)) hx.2)
          simpa using h1
        set r : ↥(roots p H) := ⟨x % p, hxroot⟩ with hrdef
        have hxr : x % p = (r : ℕ) := rfl
        have hxdiv : x / p < p ^ j := div_lt_of_lt_pow_succ (p_pos (p := p)) hx.1
        have hres : (p : ℤ) ^ j ∣ (rescale p H ((r : ℕ) : ℤ)).eval (((x / p : ℕ)) : ℤ) := by
          have hxcast : ((r : ℕ) : ℤ) + (p : ℤ) * (((x / p : ℕ)) : ℤ) = (x : ℤ) := by
            have h := eq_add_mul_div (p := p) hxr
            exact_mod_cast h.symm
          have hmuleq : H.eval (((r : ℕ) : ℤ) + (p : ℤ) * (((x / p : ℕ)) : ℤ)) =
              (p : ℤ) * (rescale p H ((r : ℕ) : ℤ)).eval (((x / p : ℕ)) : ℤ) := by
            rw [rescale_eval_mul' (p := p) H ((r : ℕ) : ℤ) (mem_roots.mp r.2).2]
          have h2 : (p : ℤ) ^ (j + 1) ∣
              (p : ℤ) * (rescale p H ((r : ℕ) : ℤ)).eval (((x / p : ℕ)) : ℤ) := by
            rw [← hmuleq, hxcast]
            exact hx.2
          have hsplit : (p : ℤ) ^ (j + 1) = (p : ℤ) * (p : ℤ) ^ j := by
            rw [add_comm, pow_add, pow_one]
          rw [hsplit] at h2
          exact (mul_dvd_mul_iff_left (p_int_ne_zero (p := p))).mp h2
        have hWdiv : (p : ℤ) ^ (j - A r) ∣ (W r).eval (((x / p : ℕ)) : ℤ) := by
          rw [(hW r).1, eval_mul, eval_C] at hres
          exact dvd_of_dvd_pow_mul hres
        have hyfib : ((x / p) % p ^ (j - A r)) ∈ fibre p (j - A r) (W r) := by
          rw [mem_fibre]
          refine ⟨Nat.mod_lt _ (pow_pos (p_pos (p := p)) _), ?_⟩
          exact dvd_eval_mod (p := p) (W r) hWdiv
        obtain ⟨⟨t, m⟩, htc, hbm⟩ := (hCv r).2.1 _ hyfib
        refine ⟨(((r : ℕ)) + p * t, m + 1), ?_, ?_⟩
        · exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_attach _ _,
            Finset.mem_image.mpr ⟨(t, m), htc, rfl⟩⟩
        · rw [mem_ball]
          refine ⟨hx.1, ?_⟩
          rw [dvd_sub_iff_dvd_div_sub (p := p) hxr]
          rw [mem_ball] at hbm
          exact dvd_sub_of_dvd_mod_sub (p := p) (by have := (hCv r).1 (t, m) htc; omega) hbm.2
      · -- cardinality
        have h1 : ((roots p H).attach.biUnion
              (fun r => (Cv r).image (fun am => (((r : ℕ)) + p * am.1, am.2 + 1)))).card
            ≤ ∑ r ∈ (roots p H).attach,
                (((Cv r).image (fun am => (((r : ℕ)) + p * am.1, am.2 + 1))).card) :=
          Finset.card_biUnion_le
        have h2 : ∀ r ∈ (roots p H).attach,
            (((Cv r).image (fun am => (((r : ℕ)) + p * am.1, am.2 + 1))).card) ≤ (Cv r).card :=
          fun r _ => Finset.card_image_le
        have h3 : ∀ r ∈ (roots p H).attach,
            (Cv r).card ≤ max 1 (((W r).map (Int.castRingHom (ZMod p))).natDegree) :=
          fun r _ => (hCv r).2.2
        have h4 : ∀ r ∈ (roots p H).attach,
            max 1 (((W r).map (Int.castRingHom (ZMod p))).natDegree)
              ≤ (H.map (Int.castRingHom (ZMod p))).rootMultiplicity (((r : ℕ)) : ZMod p) := by
          intro r _
          refine max_le (one_le_rootMultiplicity hmap_ne (mem_roots.mp r.2).2) ?_
          exact natDegree_map_le_of_dvd_coeff (hW r).2.2
        calc ((roots p H).attach.biUnion
              (fun r => (Cv r).image (fun am => (((r : ℕ)) + p * am.1, am.2 + 1)))).card
            ≤ ∑ r ∈ (roots p H).attach,
                (((Cv r).image (fun am => (((r : ℕ)) + p * am.1, am.2 + 1))).card) := h1
          _ ≤ ∑ r ∈ (roots p H).attach, (Cv r).card := Finset.sum_le_sum h2
          _ ≤ ∑ r ∈ (roots p H).attach,
                max 1 (((W r).map (Int.castRingHom (ZMod p))).natDegree) := Finset.sum_le_sum h3
          _ ≤ ∑ r ∈ (roots p H).attach,
                (H.map (Int.castRingHom (ZMod p))).rootMultiplicity (((r : ℕ)) : ZMod p) :=
                Finset.sum_le_sum h4
          _ = ∑ r ∈ roots p H,
                (H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p) :=
                Finset.sum_attach (roots p H)
                  (fun r => (H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p))
          _ ≤ (H.map (Int.castRingHom (ZMod p))).natDegree := hS H hmap_ne
          _ ≤ max 1 ((H.map (Int.castRingHom (ZMod p))).natDegree) := le_max_right _ _

/-- Balls depend only on the centre modulo `p^k`. -/
lemma ball_mod_center {k m a : ℕ} (hm : m ≤ k) : ball p k m a = ball p k m (a % p ^ k) := by
  refine ball_eq_of_dvd_sub ?_
  exact dvd_trans (pow_dvd_pow (p : ℤ) hm) (dvd_sub_mod (p := p) k a)

/-- The fibre of `C (p^c) * Ĝ` is the preimage of the fibre of `Ĝ` at level `k - c`. -/
lemma mem_fibre_C_mul_iff {c k : ℕ} (hck : c < k) {Ĝ : ℤ[X]} {x : ℕ} (hx : x < p ^ k) :
    x ∈ fibre p k (C ((p : ℤ) ^ c) * Ĝ) ↔ x % p ^ (k - c) ∈ fibre p (k - c) Ĝ := by
  have h1 : (C ((p : ℤ) ^ c) * Ĝ).eval (x : ℤ) = (p : ℤ) ^ c * Ĝ.eval (x : ℤ) := by
    rw [eval_mul, eval_C]
  rw [mem_fibre, mem_fibre, h1]
  refine ⟨fun h => ⟨Nat.mod_lt _ (pow_pos (p_pos (p := p)) _), ?_⟩,
    fun h => ⟨hx, ?_⟩⟩
  · exact dvd_eval_mod (p := p) Ĝ (dvd_of_dvd_pow_mul (p := p) h.2)
  · have h2 : (p : ℤ) ^ (k - c) ∣ Ĝ.eval (x : ℤ) := dvd_eval_of_dvd_eval_mod (p := p) Ĝ h.2
    have h3 : (p : ℤ) ^ c * (p : ℤ) ^ (k - c) ∣ (p : ℤ) ^ c * Ĝ.eval (x : ℤ) :=
      mul_dvd_mul_left _ h2
    rwa [← pow_add, show c + (k - c) = k by omega] at h3

/-- Lifting a cover along a `p`-content factor. -/
lemma cover_lift {c k : ℕ} (hck : c < k) {Ĝ : ℤ[X]} {Cov : Finset (ℕ × ℕ)}
    (h1 : ∀ am ∈ Cov, am.2 ≤ k - c ∧ ball p (k - c) am.2 am.1 ⊆ fibre p (k - c) Ĝ)
    (h2 : ∀ x ∈ fibre p (k - c) Ĝ, ∃ am ∈ Cov, x ∈ ball p (k - c) am.2 am.1) :
    (∀ am ∈ Cov, am.2 ≤ k ∧ ball p k am.2 am.1 ⊆ fibre p k (C ((p : ℤ) ^ c) * Ĝ)) ∧
      (∀ x ∈ fibre p k (C ((p : ℤ) ^ c) * Ĝ), ∃ am ∈ Cov, x ∈ ball p k am.2 am.1) := by
  refine ⟨fun am ham => ⟨le_trans (h1 am ham).1 (by omega), ?_⟩, ?_⟩
  · intro x hx
    rw [mem_ball] at hx
    rw [mem_fibre_C_mul_iff (p := p) hck hx.1]
    exact (h1 am ham).2 (by
      rw [mem_ball]
      exact ⟨Nat.mod_lt _ (pow_pos (p_pos (p := p)) _),
        dvd_mod_sub_of_dvd_sub (p := p) (h1 am ham).1 hx.2⟩)
  · intro x hx
    have hx' : x % p ^ (k - c) ∈ fibre p (k - c) Ĝ :=
      (mem_fibre_C_mul_iff (p := p) hck (mem_fibre.mp hx).1).mp hx
    obtain ⟨am, ham, hball⟩ := h2 _ hx'
    refine ⟨am, ham, ?_⟩
    rw [mem_ball] at hball ⊢
    exact ⟨(mem_fibre.mp hx).1, dvd_sub_of_dvd_mod_sub (p := p) (h1 am ham).1 hball.2⟩

/-- The general cover statement (for an arbitrary polynomial, from the four arithmetic inputs). -/
theorem exists_cover_general (p : ℕ) [Fact p.Prime]
    (hB : ∀ (H : ℤ[X]) (r : ℤ) (s : ℕ), 1 ≤ s → (p : ℤ) ∣ H.eval r →
      (∀ i, i < s → (p : ℤ) ∣ taylorCoeff H r i) → ¬ ((p : ℤ) ∣ taylorCoeff H r s) →
      ∃ a : ℕ, ∃ Ŵ : ℤ[X], rescale p H r = C ((p : ℤ) ^ a) * Ŵ ∧
        (∃ i, ¬ (p : ℤ) ∣ Ŵ.coeff i) ∧ (∀ i, s < i → (p : ℤ) ∣ Ŵ.coeff i))
    (hM : ∀ (H : ℤ[X]) (r : ℕ), H.map (Int.castRingHom (ZMod p)) ≠ 0 →
      (∀ i, i < (H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p) →
          (p : ℤ) ∣ taylorCoeff H r i) ∧
      ((p : ℤ) ∣ H.eval (r : ℤ) →
          ¬ ((p : ℤ) ∣ taylorCoeff H r
              ((H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p)))))
    (hS : ∀ (H : ℤ[X]), H.map (Int.castRingHom (ZMod p)) ≠ 0 →
      ∑ r ∈ roots p H, (H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p)
        ≤ (H.map (Int.castRingHom (ZMod p))).natDegree)
    (hD : ∀ (H : ℤ[X]), ∃ c : ℕ, ∃ Ĝ : ℤ[X], H = C ((p : ℤ) ^ c) * Ĝ ∧
      (Ĝ = 0 ∨ ∃ i, ¬ (p : ℤ) ∣ Ĝ.coeff i))
    (k : ℕ) (hk : 1 ≤ k) (G : ℤ[X]) :
      ∃ C : Finset (ℕ × ℕ),
        (∀ am ∈ C, am.2 ≤ k ∧ ball p k am.2 am.1 ⊆ fibre p k G) ∧
        (∀ x ∈ fibre p k G, ∃ am ∈ C, x ∈ ball p k am.2 am.1) ∧
        C.card ≤ max 1 G.natDegree := by
  obtain ⟨c, Ĝ, hG, hprim⟩ := hD G
  by_cases hE : Ĝ = 0
  · subst hE
    rw [mul_zero] at hG
    subst hG
    refine ⟨{(0, 0)}, ?_, ?_, ?_⟩
    · intro am ham
      rw [Finset.mem_singleton] at ham
      subst ham
      refine ⟨by omega, ?_⟩
      intro x hx
      rw [mem_ball] at hx
      rw [mem_fibre]
      exact ⟨hx.1, by simp⟩
    · intro x hx
      rw [mem_fibre] at hx
      exact ⟨(0, 0), Finset.mem_singleton_self 0, by rw [mem_ball]; exact ⟨hx.1, by simp⟩⟩
    · simp
  · have hprim' : ∃ i, ¬ (p : ℤ) ∣ Ĝ.coeff i := by
      rcases hprim with h | h
      · exact absurd h hE
      · exact h
    by_cases hck : c < k
    · obtain ⟨C, h1, h2, h3⟩ := exists_cover_of_inputs p hB hM hS hD (k - c) Ĝ hprim'
      obtain ⟨h1', h2'⟩ := cover_lift (p := p) hck h1 h2
      refine ⟨C, ?_, ?_, ?_⟩
      · rw [hG]; exact h1'
      · rw [hG]; exact h2'
      · calc C.card ≤ max 1 ((Ĝ.map (Int.castRingHom (ZMod p))).natDegree) := h3
          _ ≤ max 1 (Ĝ.natDegree) := max_le_max le_rfl Polynomial.natDegree_map_le
          _ = max 1 (G.natDegree) := by
              rw [hG, natDegree_C_mul]
              exact pow_ne_zero _ (p_int_ne_zero (p := p))
    · refine ⟨{(0, 0)}, ?_, ?_, ?_⟩
      · intro am ham
        rw [Finset.mem_singleton] at ham
        subst ham
        refine ⟨by omega, ?_⟩
        intro x hx
        rw [mem_ball] at hx
        rw [mem_fibre]
        refine ⟨hx.1, ?_⟩
        rw [hG, eval_mul, eval_C]
        exact dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) (not_lt.mp hck)) _
      · intro x hx
        rw [mem_fibre] at hx
        exact ⟨(0, 0), Finset.mem_singleton_self 0, by rw [mem_ball]; exact ⟨hx.1, by simp⟩⟩
      · simp

end

end Work.KMTPlan.A6.ConcAux
