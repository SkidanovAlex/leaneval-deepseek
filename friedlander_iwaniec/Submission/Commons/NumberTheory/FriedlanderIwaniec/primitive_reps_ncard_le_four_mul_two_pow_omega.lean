import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.rho_le_two_pow_omega

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-! ## Auxiliary lemmas -/

/-- A finset with four explicit elements has at most four elements. -/
lemma finset_card_le_four {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 := by
  have h₁ := Finset.card_insert_le a ({b, c, d} : Finset α)
  have h₂ := Finset.card_insert_le b ({c, d} : Finset α)
  have h₃ := Finset.card_insert_le c ({d} : Finset α)
  have h₄ : ({d} : Finset α).card = 1 := Finset.card_singleton d
  omega

/-- An integer whose square is at most `m` lies in the interval `[-m, m]`. -/
lemma int_mem_Icc_of_sq_le {a : ℤ} {m : ℕ} (h : a ^ 2 ≤ (m : ℤ)) :
    a ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
  rw [Finset.mem_Icc]
  have h' : ((a.natAbs ^ 2 : ℕ) : ℤ) ≤ (m : ℤ) := by
    rw [Nat.cast_pow, Int.natAbs_sq]; exact h
  have h2 : a.natAbs ^ 2 ≤ m := by exact_mod_cast h'
  have h3 : a.natAbs ≤ m :=
    le_trans (Nat.le_self_pow (show (2 : ℕ) ≠ 0 by norm_num) a.natAbs) h2
  have h4 : |a| ≤ (m : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h3
  exact abs_le.mp h4

/-- If `a ^ 2 + b ^ 2 = m` and `gcd a b = 1`, then `IsCoprime m b`. -/
lemma isCoprime_of_sq_add_sq {a b : ℤ} {m : ℕ} (h : a ^ 2 + b ^ 2 = (m : ℤ))
    (hg : a.gcd b = 1) : IsCoprime (m : ℤ) b := by
  obtain ⟨p, q, hpq⟩ := (Int.isCoprime_iff_gcd_eq_one).mpr hg
  refine ⟨p ^ 2, (q ^ 2 - p ^ 2) * b + 2 * p * q * a, ?_⟩
  have key : p ^ 2 * (m : ℤ) + ((q ^ 2 - p ^ 2) * b + 2 * p * q * a) * b
      = (p * a + q * b) ^ 2 := by
    rw [← h]; ring
  rw [key, hpq]; norm_num

/-- If `a ^ 2 + b ^ 2 = m` and `gcd a b = 1`, then `b` is a unit modulo `m`. -/
lemma isUnit_intCast_of_sq_add_sq {a b : ℤ} {m : ℕ} (h : a ^ 2 + b ^ 2 = (m : ℤ))
    (hg : a.gcd b = 1) : IsUnit (b : ZMod m) :=
  (ZMod.coe_int_isUnit_iff_isCoprime b m).mpr (isCoprime_of_sq_add_sq h hg)

/-- For a primitive representation `a ^ 2 + b ^ 2 = m`, the residue `a * b⁻¹`
modulo `m` is a square root of `-1`. -/
lemma sq_mul_inv_eq_neg_one {a b : ℤ} {m : ℕ} (h : a ^ 2 + b ^ 2 = (m : ℤ))
    (hb : IsUnit (b : ZMod m)) :
    ((a : ZMod m) * (b : ZMod m)⁻¹) ^ 2 = -1 := by
  have hcast : (a : ZMod m) ^ 2 + (b : ZMod m) ^ 2 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod m)) h
    push_cast at this
    simpa using this
  have hb2 : ((b : ZMod m)⁻¹) ^ 2 * (b : ZMod m) ^ 2 = 1 := by
    have h1 : (b : ZMod m) * (b : ZMod m)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hb
    calc ((b : ZMod m)⁻¹) ^ 2 * (b : ZMod m) ^ 2
        = ((b : ZMod m) * (b : ZMod m)⁻¹) ^ 2 := by ring
      _ = 1 := by rw [h1]; ring
  have ha2 : (a : ZMod m) ^ 2 = -((b : ZMod m) ^ 2) := by
    rw [eq_neg_iff_add_eq_zero]; exact hcast
  calc ((a : ZMod m) * (b : ZMod m)⁻¹) ^ 2
      = (a : ZMod m) ^ 2 * ((b : ZMod m)⁻¹) ^ 2 := by ring
    _ = -(((b : ZMod m) ^ 2) * ((b : ZMod m)⁻¹) ^ 2) := by rw [ha2]; ring
    _ = -1 := by rw [mul_comm ((b : ZMod m) ^ 2), hb2]

/-- From `a * b⁻¹ = c * d⁻¹` with `b`, `d` invertible, one deduces
`a * d = c * b`. -/
lemma mul_eq_mul_of_mul_inv_eq_mul_inv {R : Type*} [CommSemiring R] [Inv R] {a b c d : R}
    (hb : b⁻¹ * b = 1) (hd : d⁻¹ * d = 1) (h : a * b⁻¹ = c * d⁻¹) : a * d = c * b := by
  have ha : a = (a * b⁻¹) * b := by rw [mul_assoc, hb, mul_one]
  have hc : c = (c * d⁻¹) * d := by rw [mul_assoc, hd, mul_one]
  rw [ha, hc, h]
  ring

/-- **Structure of the fibre of `(a, b) ↦ a * b⁻¹`.**

If `p` and `q` are primitive representations of `m` and have the same image
`a * b⁻¹` in `ZMod m`, then `q` is one of `p`, `-p`, `(-p.2, p.1)`,
`(p.2, -p.1)`.  Indeed, with `D = p.1 * q.2 - q.1 * p.2` and
`E = p.1 * q.1 + p.2 * q.2` the two-square identity
`D ^ 2 + E ^ 2 = m ^ 2` holds, and `m ∣ D`; hence `D = ε * m`, `E = δ * m`
with `δ ^ 2 + ε ^ 2 = 1`, and the linear system
`m * q.1 = p.1 * E - p.2 * D`, `m * q.2 = p.2 * E + p.1 * D` forces
`(q.1, q.2) ∈ {±(p.1, p.2), ±(-p.2, p.1)}`. -/
lemma primitive_rep_eq_of_mul_inv_eq {m : ℕ} (hm : 1 ≤ m) {p q : ℤ × ℤ}
    (hp : p.1 ^ 2 + p.2 ^ 2 = (m : ℤ)) (hpg : p.1.gcd p.2 = 1)
    (hq : q.1 ^ 2 + q.2 ^ 2 = (m : ℤ)) (hqg : q.1.gcd q.2 = 1)
    (h : (p.1 : ZMod m) * (p.2 : ZMod m)⁻¹
        = (q.1 : ZMod m) * (q.2 : ZMod m)⁻¹) :
    q = p ∨ q = -p ∨ q = (-p.2, p.1) ∨ q = (p.2, -p.1) := by
  have hm0 : (m : ℤ) ≠ 0 := by omega
  have hmpos : (0 : ℤ) < (m : ℤ) := by omega
  have hb : IsUnit (p.2 : ZMod m) := isUnit_intCast_of_sq_add_sq hp hpg
  have hbq : IsUnit (q.2 : ZMod m) := isUnit_intCast_of_sq_add_sq hq hqg
  -- `m` divides the determinant `D`
  have hdet : (m : ℤ) ∣ p.1 * q.2 - q.1 * p.2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hbd : (p.2 : ZMod m)⁻¹ * (p.2 : ZMod m) = 1 := ZMod.inv_mul_of_unit _ hb
    have hbdq : (q.2 : ZMod m)⁻¹ * (q.2 : ZMod m) = 1 := ZMod.inv_mul_of_unit _ hbq
    push_cast
    exact sub_eq_zero.mpr (mul_eq_mul_of_mul_inv_eq_mul_inv hbd hbdq h)
  obtain ⟨t, ht⟩ := hdet
  set D : ℤ := p.1 * q.2 - q.1 * p.2 with hDdef
  set E : ℤ := p.1 * q.1 + p.2 * q.2 with hEdef
  have hDt : D = (m : ℤ) * t := ht
  have hid : D ^ 2 + E ^ 2 = (m : ℤ) ^ 2 := by
    have h1 : (p.1 * q.2 - q.1 * p.2) ^ 2 + (p.1 * q.1 + p.2 * q.2) ^ 2
        = (p.1 ^ 2 + p.2 ^ 2) * (q.1 ^ 2 + q.2 ^ 2) := by ring
    rw [hDdef, hEdef, h1, hp, hq]; ring
  have hEt : E ^ 2 = (m : ℤ) ^ 2 * (1 - t ^ 2) := by
    have h2 : D ^ 2 = (m : ℤ) ^ 2 * t ^ 2 := by rw [hDt]; ring
    rw [h2] at hid
    linarith
  have ht2le : t ^ 2 ≤ 1 := by
    have hpos : (0 : ℤ) < (m : ℤ) ^ 2 := pow_pos hmpos 2
    have hnn : 0 ≤ (m : ℤ) ^ 2 * (1 - t ^ 2) := by rw [← hEt]; positivity
    have := (mul_nonneg_iff_of_pos_left hpos).mp hnn
    linarith
  have hbnd : -1 ≤ t ∧ t ≤ 1 :=
    abs_le.mp ((sq_le_one_iff_abs_le_one t).mp ht2le)
  have hq1 : (m : ℤ) * q.1 = p.1 * E - p.2 * D := by
    rw [hEdef, hDdef, ← hp]; ring
  have hq2 : (m : ℤ) * q.2 = p.2 * E + p.1 * D := by
    rw [hEdef, hDdef, ← hp]; ring
  have hcancel : ∀ x y : ℤ, (m : ℤ) * x = (m : ℤ) * y → x = y :=
    fun x y hxy => mul_left_cancel₀ hm0 hxy
  have ht_cases : t = -1 ∨ t = 0 ∨ t = 1 := by omega
  rcases ht_cases with htc | htc | htc
  · -- t = -1 : D = -m, E = 0
    have hE0 : E = 0 := by
      have : E ^ 2 = 0 := by rw [hEt, htc]; ring
      exact sq_eq_zero_iff.mp this
    have hD : D = -(m : ℤ) := by rw [hDt, htc]; ring
    have h1 : q.1 = p.2 := by
      refine hcancel _ _ ?_
      rw [hq1, hE0, hD]; ring
    have h2 : q.2 = -p.1 := by
      refine hcancel _ _ ?_
      rw [hq2, hE0, hD]; ring
    exact Or.inr (Or.inr (Or.inr (Prod.ext h1 h2)))
  · -- t = 0 : D = 0, E = ± m
    have hD : D = 0 := by rw [hDt, htc]; ring
    have hE2 : E ^ 2 = (m : ℤ) ^ 2 := by rw [hEt, htc]; ring
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hE2 with hE | hE
    · have h1 : q.1 = p.1 := by
        refine hcancel _ _ ?_; rw [hq1, hE, hD]; ring
      have h2 : q.2 = p.2 := by
        refine hcancel _ _ ?_; rw [hq2, hE, hD]; ring
      exact Or.inl (Prod.ext h1 h2)
    · have h1 : q.1 = -p.1 := by
        refine hcancel _ _ ?_; rw [hq1, hE, hD]; ring
      have h2 : q.2 = -p.2 := by
        refine hcancel _ _ ?_; rw [hq2, hE, hD]; ring
      exact Or.inr (Or.inl (Prod.ext h1 h2))
  · -- t = 1 : D = m, E = 0
    have hE0 : E = 0 := by
      have : E ^ 2 = 0 := by rw [hEt, htc]; ring
      exact sq_eq_zero_iff.mp this
    have hD : D = (m : ℤ) := by rw [hDt, htc]; ring
    have h1 : q.1 = -p.2 := by
      refine hcancel _ _ ?_
      rw [hq1, hE0, hD]; ring
    have h2 : q.2 = p.1 := by
      refine hcancel _ _ ?_
      rw [hq2, hE0, hD]; ring
    exact Or.inr (Or.inr (Or.inl (Prod.ext h1 h2)))


/-- The number of primitive representations of `m` as a sum of two squares
(i.e. `a² + b² = m` with `gcd a b = 1`) is at most `4 · 2 ^ ω(m)`.
The map `(a,b) ↦ a · b⁻¹` takes primitive representations to square roots of
`-1` modulo `m`, and each root has at most the four preimages `±(a,b)`,
`±(-b,a)`. -/
theorem primitive_reps_ncard_le_four_mul_two_pow_omega (m : ℕ) (hm : 1 ≤ m) :
    ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = (m : ℤ) ∧ Int.gcd p.1 p.2 = 1}).ncard
      ≤ 4 * 2 ^ (m.primeFactors).card := by
  classical
  have hm0 : m ≠ 0 := by omega
  haveI : NeZero m := ⟨hm0⟩
  set S : Set (ℤ × ℤ) :=
    {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = (m : ℤ) ∧ Int.gcd p.1 p.2 = 1} with hSdef
  have hmem : ∀ p : ℤ × ℤ,
      p ∈ S ↔ p.1 ^ 2 + p.2 ^ 2 = (m : ℤ) ∧ Int.gcd p.1 p.2 = 1 := fun p => Iff.rfl
  have hFin : S.Finite := by
    have hbig : (((Finset.Icc (-(m : ℤ)) (m : ℤ) : Finset ℤ) : Set ℤ)
        ×ˢ ((Finset.Icc (-(m : ℤ)) (m : ℤ) : Finset ℤ) : Set ℤ)).Finite :=
      (Finset.finite_toSet _).prod (Finset.finite_toSet _)
    refine hbig.subset ?_
    intro p hp
    obtain ⟨hp1, _⟩ := (hmem p).mp hp
    rw [Set.mem_prod]
    exact ⟨by rw [Finset.mem_coe]; exact int_mem_Icc_of_sq_le (by linarith [sq_nonneg p.2]),
           by rw [Finset.mem_coe]; exact int_mem_Icc_of_sq_le (by linarith [sq_nonneg p.1])⟩
  set sf : Finset (ℤ × ℤ) := hFin.toFinset with hsfdef
  have hmemS : ∀ p : ℤ × ℤ,
      p ∈ sf ↔ p.1 ^ 2 + p.2 ^ 2 = (m : ℤ) ∧ Int.gcd p.1 p.2 = 1 := by
    intro p
    rw [hsfdef, Set.Finite.mem_toFinset]
    exact hmem p
  let Φ : ℤ × ℤ → ZMod m := fun p => (p.1 : ZMod m) * ((p.2 : ZMod m))⁻¹
  let A : Finset (ZMod m) := Finset.univ.filter (fun α : ZMod m => α ^ 2 = -1)
  have hmaps : Set.MapsTo Φ (sf : Set (ℤ × ℤ)) (A : Set (ZMod m)) := by
    intro p hp
    rw [Finset.mem_coe] at hp
    have hpS := (hmemS p).mp hp
    rw [Finset.mem_coe]
    show Φ p ∈ A
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact sq_mul_inv_eq_neg_one hpS.1 (isUnit_intCast_of_sq_add_sq hpS.1 hpS.2)
  have hfiber : ∀ α ∈ A, (sf.filter (fun p => Φ p = α)).card ≤ 4 := by
    intro α _
    by_cases hne : (sf.filter (fun p => Φ p = α)).Nonempty
    · obtain ⟨p, hp⟩ := hne
      rw [Finset.mem_filter] at hp
      obtain ⟨hpsf, hpα⟩ := hp
      have hpS := (hmemS p).mp hpsf
      have hsub : sf.filter (fun q => Φ q = α)
          ⊆ ({p, -p, (-p.2, p.1), (p.2, -p.1)} : Finset (ℤ × ℤ)) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hqsf, hqα⟩ := hq
        have hqS := (hmemS q).mp hqsf
        have hΦ : Φ p = Φ q := by rw [hpα, hqα]
        rcases primitive_rep_eq_of_mul_inv_eq hm hpS.1 hpS.2 hqS.1 hqS.2 hΦ with h | h | h | h
        · rw [h]; exact Finset.mem_insert_self _ _
        · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        · rw [h]
          exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      exact le_trans (Finset.card_le_card hsub) (finset_card_le_four p (-p) (-p.2, p.1) (p.2, -p.1))
    · have hemp : sf.filter (fun p => Φ p = α) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hemp]
      simp
  have hcard_eq := Finset.card_eq_sum_card_fiberwise hmaps
  have hsum : sf.card ≤ 4 * A.card := by
    calc sf.card = ∑ b ∈ A, (sf.filter (fun p => Φ p = b)).card := hcard_eq
      _ ≤ ∑ _b ∈ A, 4 := Finset.sum_le_sum hfiber
      _ = 4 * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hAcard : A.card ≤ 2 ^ (m.primeFactors).card := by
    have h1 : A.card = ({α : ZMod m | α ^ 2 = -1}).ncard := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
    rw [h1]
    exact rho_le_two_pow_omega (by omega : 0 < m)
  calc S.ncard = sf.card := Set.ncard_eq_toFinset_card S hFin
    _ ≤ 4 * A.card := hsum
    _ ≤ 4 * 2 ^ (m.primeFactors).card := Nat.mul_le_mul_left 4 hAcard


end Commons.NumberTheory.FriedlanderIwaniec
