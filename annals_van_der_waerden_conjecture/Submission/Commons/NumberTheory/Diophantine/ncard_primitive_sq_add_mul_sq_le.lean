import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.primitive_reps_ncard_le_four_mul_two_pow_omega

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.Diophantine

/-!
## Counting primitive representations of `M` by the form `x² + D y²`

The number of primitive integer pairs `(x, y)` with `x² + D y² = M` is at most
four times the number of square roots of `-D` modulo `M`.  The map sending a
primitive representation to `x · y⁻¹` in `ZMod M` takes values in the roots of
`-D` (because `y` is invertible modulo `M`), and each fibre of this map contains
at most the four pairs `±(x, y)`, `±(-y, x)`.
-/

open Commons.NumberTheory.FriedlanderIwaniec

/-- If `a ^ 2 + D * b ^ 2 = m` and `gcd a b = 1`, then `b` is a unit modulo `m`.

Indeed any prime dividing both `b` and `m` divides `a ^ 2`, hence `a`, which is
incompatible with `gcd a b = 1`. -/
lemma isUnit_intCast_of_sq_add_mul_sq {D : ℕ} {a b : ℤ} {m : ℕ}
    (h : a ^ 2 + (D : ℤ) * b ^ 2 = (m : ℤ)) (hg : a.gcd b = 1) :
    IsUnit (b : ZMod m) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_gcd_eq_one, ← h]
  have hstep : (a ^ 2 + (D : ℤ) * b ^ 2).gcd b = (a ^ 2).gcd b := by
    have hD : (D : ℤ) * b ^ 2 = b * ((D : ℤ) * b) := by ring
    rw [hD, Int.gcd_add_mul_left_left]
  rw [hstep]
  exact Int.isCoprime_iff_gcd_eq_one.mp (Int.isCoprime_iff_gcd_eq_one.mpr hg).pow_left

/-- For a primitive representation `a ^ 2 + D * b ^ 2 = m`, the residue `a * b⁻¹`
modulo `m` is a square root of `-D`. -/
lemma sq_mul_inv_eq_neg_natCast {D : ℕ} {a b : ℤ} {m : ℕ}
    (h : a ^ 2 + (D : ℤ) * b ^ 2 = (m : ℤ)) (hb : IsUnit (b : ZMod m)) :
    ((a : ZMod m) * (b : ZMod m)⁻¹) ^ 2 = -((D : ℕ) : ZMod m) := by
  have hcast : (a : ZMod m) ^ 2 + ((D : ℕ) : ZMod m) * (b : ZMod m) ^ 2 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod m)) h
    push_cast at this
    simpa using this
  have hb2 : ((b : ZMod m)⁻¹) ^ 2 * (b : ZMod m) ^ 2 = 1 := by
    have h1 : (b : ZMod m) * (b : ZMod m)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hb
    calc ((b : ZMod m)⁻¹) ^ 2 * (b : ZMod m) ^ 2
        = ((b : ZMod m) * (b : ZMod m)⁻¹) ^ 2 := by ring
      _ = 1 := by rw [h1]; ring
  have ha2 : (a : ZMod m) ^ 2 = -(((D : ℕ) : ZMod m) * (b : ZMod m) ^ 2) := by
    rw [eq_neg_iff_add_eq_zero]; exact hcast
  calc ((a : ZMod m) * (b : ZMod m)⁻¹) ^ 2
      = (a : ZMod m) ^ 2 * ((b : ZMod m)⁻¹) ^ 2 := by ring
    _ = -(((D : ℕ) : ZMod m) * (b : ZMod m) ^ 2 * ((b : ZMod m)⁻¹) ^ 2) := by rw [ha2]; ring
    _ = -((D : ℕ) : ZMod m) := by
          have hsq : (b : ZMod m) ^ 2 * ((b : ZMod m)⁻¹) ^ 2 = 1 := by
            rw [mul_comm]; exact hb2
          rw [mul_assoc, hsq, mul_one]

/-- **Structure of the fibre of `(a, b) ↦ a * b⁻¹` for the form `x² + D y²`.**

If `p` and `q` are primitive representations of `m` by `x² + D y²` and have the
same image `a * b⁻¹` in `ZMod m`, then `q` is one of `p`, `-p`, `(-p.2, p.1)`,
`(p.2, -p.1)`.  With `V = p.1 * q.2 - q.1 * p.2` and
`U = p.1 * q.1 + D * p.2 * q.2` the identity `U ^ 2 + D * V ^ 2 = m ^ 2` holds
and `m ∣ V`, so `V = m * t` and `U ^ 2 = m ^ 2 * (1 - D * t ^ 2)`; hence
`D * t ^ 2 ≤ 1`.  If `t = 0` then `U = ± m`, `V = 0` and the linear system
`m * q.1 = p.1 * U - D * p.2 * V`, `m * q.2 = p.2 * U + p.1 * V` gives `q = ±p`;
if `t = ±1` then `D = 1`, `U = 0` and `V = ± m`, giving the two perpendicular
pairs. -/
lemma primitive_rep_eq_of_mul_inv_eq_D {D m : ℕ} (hD : 1 ≤ D) (hm : 1 ≤ m) {p q : ℤ × ℤ}
    (hp : p.1 ^ 2 + (D : ℤ) * p.2 ^ 2 = (m : ℤ)) (hpg : p.1.gcd p.2 = 1)
    (hq : q.1 ^ 2 + (D : ℤ) * q.2 ^ 2 = (m : ℤ)) (hqg : q.1.gcd q.2 = 1)
    (h : (p.1 : ZMod m) * (p.2 : ZMod m)⁻¹
        = (q.1 : ZMod m) * (q.2 : ZMod m)⁻¹) :
    q = p ∨ q = -p ∨ q = (-p.2, p.1) ∨ q = (p.2, -p.1) := by
  have hm0 : (m : ℤ) ≠ 0 := by omega
  have hmpos : (0 : ℤ) < (m : ℤ) := by omega
  have hb : IsUnit (p.2 : ZMod m) := isUnit_intCast_of_sq_add_mul_sq hp hpg
  have hbq : IsUnit (q.2 : ZMod m) := isUnit_intCast_of_sq_add_mul_sq hq hqg
  -- `m` divides the determinant `V`
  have hdet : (m : ℤ) ∣ p.1 * q.2 - q.1 * p.2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hbd : (p.2 : ZMod m)⁻¹ * (p.2 : ZMod m) = 1 := ZMod.inv_mul_of_unit _ hb
    have hbdq : (q.2 : ZMod m)⁻¹ * (q.2 : ZMod m) = 1 := ZMod.inv_mul_of_unit _ hbq
    push_cast
    exact sub_eq_zero.mpr (mul_eq_mul_of_mul_inv_eq_mul_inv hbd hbdq h)
  obtain ⟨t, ht⟩ := hdet
  set V : ℤ := p.1 * q.2 - q.1 * p.2 with hVdef
  set U : ℤ := p.1 * q.1 + (D : ℤ) * p.2 * q.2 with hUdef
  have hVt : V = (m : ℤ) * t := ht
  have hid : U ^ 2 + (D : ℤ) * V ^ 2 = (m : ℤ) ^ 2 := by
    have h1 : (p.1 * q.1 + (D : ℤ) * p.2 * q.2) ^ 2 + (D : ℤ) * (p.1 * q.2 - q.1 * p.2) ^ 2
        = (p.1 ^ 2 + (D : ℤ) * p.2 ^ 2) * (q.1 ^ 2 + (D : ℤ) * q.2 ^ 2) := by ring
    rw [hUdef, hVdef, h1, hp, hq]; ring
  have hUt : U ^ 2 = (m : ℤ) ^ 2 * (1 - (D : ℤ) * t ^ 2) := by
    have h2 : (D : ℤ) * V ^ 2 = (m : ℤ) ^ 2 * ((D : ℤ) * t ^ 2) := by rw [hVt]; ring
    rw [h2] at hid
    linarith
  have hDt2le : (D : ℤ) * t ^ 2 ≤ 1 := by
    have hpos : (0 : ℤ) < (m : ℤ) ^ 2 := pow_pos hmpos 2
    have hnn : 0 ≤ (m : ℤ) ^ 2 * (1 - (D : ℤ) * t ^ 2) := by rw [← hUt]; positivity
    have := (mul_nonneg_iff_of_pos_left hpos).mp hnn
    linarith
  have hDge : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
  have ht2le : t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t, hDt2le, hDge]
  have hbnd : -1 ≤ t ∧ t ≤ 1 :=
    abs_le.mp ((sq_le_one_iff_abs_le_one t).mp ht2le)
  have hq1 : (m : ℤ) * q.1 = p.1 * U - (D : ℤ) * p.2 * V := by
    rw [hUdef, hVdef, ← hp]; ring
  have hq2 : (m : ℤ) * q.2 = p.2 * U + p.1 * V := by
    rw [hUdef, hVdef, ← hp]; ring
  have hcancel : ∀ x y : ℤ, (m : ℤ) * x = (m : ℤ) * y → x = y :=
    fun x y hxy => mul_left_cancel₀ hm0 hxy
  have ht_cases : t = -1 ∨ t = 0 ∨ t = 1 := by omega
  rcases ht_cases with htc | htc | htc
  · -- t = -1 : D = 1, U = 0, V = -m
    have hD1z : (D : ℤ) = 1 := by
      have hle : (D : ℤ) ≤ 1 := by
        have := hDt2le; rw [htc] at this; simpa using this
      omega
    have hU0 : U = 0 := by
      have : U ^ 2 = 0 := by rw [hUt, htc, hD1z]; ring
      exact sq_eq_zero_iff.mp this
    have hV : V = -(m : ℤ) := by rw [hVt, htc]; ring
    have h1 : q.1 = p.2 := by
      refine hcancel _ _ ?_; rw [hq1, hU0, hV, hD1z]; ring
    have h2 : q.2 = -p.1 := by
      refine hcancel _ _ ?_; rw [hq2, hU0, hV]; ring
    exact Or.inr (Or.inr (Or.inr (Prod.ext h1 h2)))
  · -- t = 0 : V = 0, U = ± m
    have hV : V = 0 := by rw [hVt, htc]; ring
    have hU2 : U ^ 2 = (m : ℤ) ^ 2 := by rw [hUt, htc]; ring
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hU2 with hU | hU
    · have h1 : q.1 = p.1 := by
        refine hcancel _ _ ?_; rw [hq1, hU, hV]; ring
      have h2 : q.2 = p.2 := by
        refine hcancel _ _ ?_; rw [hq2, hU, hV]; ring
      exact Or.inl (Prod.ext h1 h2)
    · have h1 : q.1 = -p.1 := by
        refine hcancel _ _ ?_; rw [hq1, hU, hV]; ring
      have h2 : q.2 = -p.2 := by
        refine hcancel _ _ ?_; rw [hq2, hU, hV]; ring
      exact Or.inr (Or.inl (Prod.ext h1 h2))
  · -- t = 1 : D = 1, U = 0, V = m
    have hD1z : (D : ℤ) = 1 := by
      have hle : (D : ℤ) ≤ 1 := by
        have := hDt2le; rw [htc] at this; simpa using this
      omega
    have hU0 : U = 0 := by
      have : U ^ 2 = 0 := by rw [hUt, htc, hD1z]; ring
      exact sq_eq_zero_iff.mp this
    have hV : V = (m : ℤ) := by rw [hVt, htc]; ring
    have h1 : q.1 = -p.2 := by
      refine hcancel _ _ ?_; rw [hq1, hU0, hV, hD1z]; ring
    have h2 : q.2 = p.1 := by
      refine hcancel _ _ ?_; rw [hq2, hU0, hV]; ring
    exact Or.inr (Or.inr (Or.inl (Prod.ext h1 h2)))

/-- The number of primitive representations of `M` as `x ^ 2 + D * y ^ 2`
(i.e. `x² + D y² = M` with `gcd x y = 1`) is at most `4` times the number of
square roots of `-D` modulo `M`.  The map `(x,y) ↦ x · y⁻¹` takes primitive
representations to roots of `-D`, and each root has at most the four preimages
`±(x, y)`, `±(-y, x)`. -/
theorem ncard_primitive_sq_add_mul_sq_le (D M : ℕ) (hD : 1 ≤ D) (hM : 1 ≤ M) :
    ({p : ℤ × ℤ | p.1 ^ 2 + (D : ℤ) * p.2 ^ 2 = (M : ℤ) ∧ Int.gcd p.1 p.2 = 1}).ncard
      ≤ 4 * ({α : ZMod M | α ^ 2 = -((D : ℕ) : ZMod M)}).ncard := by
  classical
  have hm0 : M ≠ 0 := by omega
  haveI : NeZero M := ⟨hm0⟩
  have hDge : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
  set S : Set (ℤ × ℤ) :=
    {p : ℤ × ℤ | p.1 ^ 2 + (D : ℤ) * p.2 ^ 2 = (M : ℤ) ∧ Int.gcd p.1 p.2 = 1} with hSdef
  have hmem : ∀ p : ℤ × ℤ,
      p ∈ S ↔ p.1 ^ 2 + (D : ℤ) * p.2 ^ 2 = (M : ℤ) ∧ Int.gcd p.1 p.2 = 1 := fun p => Iff.rfl
  have hFin : S.Finite := by
    have hbig : (((Finset.Icc (-(M : ℤ)) (M : ℤ) : Finset ℤ) : Set ℤ)
        ×ˢ ((Finset.Icc (-(M : ℤ)) (M : ℤ) : Finset ℤ) : Set ℤ)).Finite :=
      (Finset.finite_toSet _).prod (Finset.finite_toSet _)
    refine hbig.subset ?_
    intro p hp
    obtain ⟨hp1, _⟩ := (hmem p).mp hp
    rw [Set.mem_prod]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_coe]
      exact int_mem_Icc_of_sq_le (by nlinarith [sq_nonneg p.2, hp1, hDge])
    · rw [Finset.mem_coe]
      have hp2 : p.2 ^ 2 ≤ (M : ℤ) := by nlinarith [sq_nonneg p.2, hp1, hDge]
      exact int_mem_Icc_of_sq_le hp2
  set sf : Finset (ℤ × ℤ) := hFin.toFinset with hsfdef
  have hmemS : ∀ p : ℤ × ℤ,
      p ∈ sf ↔ p.1 ^ 2 + (D : ℤ) * p.2 ^ 2 = (M : ℤ) ∧ Int.gcd p.1 p.2 = 1 := by
    intro p; rw [hsfdef, Set.Finite.mem_toFinset]; exact hmem p
  let Φ : ℤ × ℤ → ZMod M := fun p => (p.1 : ZMod M) * ((p.2 : ZMod M))⁻¹
  let A : Finset (ZMod M) := Finset.univ.filter (fun α : ZMod M => α ^ 2 = -((D : ℕ) : ZMod M))
  have hmaps : Set.MapsTo Φ (sf : Set (ℤ × ℤ)) (A : Set (ZMod M)) := by
    intro p hp
    rw [Finset.mem_coe] at hp
    have hpS := (hmemS p).mp hp
    rw [Finset.mem_coe]
    show Φ p ∈ A
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact sq_mul_inv_eq_neg_natCast hpS.1 (isUnit_intCast_of_sq_add_mul_sq hpS.1 hpS.2)
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
        rcases primitive_rep_eq_of_mul_inv_eq_D hD hM hpS.1 hpS.2 hqS.1 hqS.2 hΦ with h | h | h | h
        · rw [h]; exact Finset.mem_insert_self _ _
        · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · rw [h]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        · rw [h]
          exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      exact le_trans (Finset.card_le_card hsub) (finset_card_le_four p (-p) (-p.2, p.1) (p.2, -p.1))
    · have hemp : sf.filter (fun p => Φ p = α) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hemp]; simp
  have hcard_eq := Finset.card_eq_sum_card_fiberwise hmaps
  have hsum : sf.card ≤ 4 * A.card := by
    calc sf.card = ∑ b ∈ A, (sf.filter (fun p => Φ p = b)).card := hcard_eq
      _ ≤ ∑ _b ∈ A, 4 := Finset.sum_le_sum hfiber
      _ = 4 * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hAcard : A.card = ({α : ZMod M | α ^ 2 = -((D : ℕ) : ZMod M)}).ncard := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  calc S.ncard = sf.card := Set.ncard_eq_toFinset_card S hFin
    _ ≤ 4 * A.card := hsum
    _ = 4 * ({α : ZMod M | α ^ 2 = -((D : ℕ) : ZMod M)}).ncard := by rw [hAcard]

end Commons.NumberTheory.Diophantine
