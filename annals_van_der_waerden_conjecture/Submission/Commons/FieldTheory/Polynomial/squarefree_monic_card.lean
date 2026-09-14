import Mathlib
import Submission.Commons.Nat.squarefree_count_closed

open Polynomial
open scoped BigOperators

set_option maxHeartbeats 400000

universe u

namespace SqfreeMonicCardInternal

/-- Monic polynomials of degree `n` over `F`. -/
abbrev MonicDeg (F : Type u) [Field F] (n : ℕ) : Type u :=
  {p : F[X] // p.Monic ∧ p.natDegree = n}

/-- Squarefree monic polynomials of degree `n` over `F`. -/
abbrev SqfreeMonicDeg (F : Type u) [Field F] (n : ℕ) : Type u :=
  {p : F[X] // p.Monic ∧ p.natDegree = n ∧ Squarefree p}

/-- Build a monic polynomial of degree `n` from its coefficients below `n`. -/
noncomputable def monicOfVec (F : Type u) [Field F] (n : ℕ) (v : Fin n → F) : F[X] :=
  X ^ n + ∑ i : Fin n, C (v i) * X ^ (i : ℕ)

/-- coefficient of the lower-degree sum `∑ C (v i) X^i` at index `k ≥ n` is zero -/
lemma lowerSum_coeff_ge {F : Type u} [Field F] {n : ℕ} (v : Fin n → F) {k : ℕ} (hk : n ≤ k) :
    (∑ i : Fin n, C (v i) * X ^ (i : ℕ)).coeff k = 0 := by
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [coeff_C_mul_X_pow]
  have hik : k ≠ (i : ℕ) := by
    intro h
    have : (i : ℕ) < n := Fin.isLt i
    omega
  rw [if_neg hik]

lemma monicOfVec_coeff_X_pow {F : Type u} [Field F] {n : ℕ} (v : Fin n → F) :
    (monicOfVec F n v).coeff n = 1 := by
  rw [monicOfVec, coeff_add, coeff_X_pow, if_pos rfl]
  rw [lowerSum_coeff_ge v (le_refl n)]
  norm_num

lemma monicOfVec_natDegree {F : Type u} [Field F] (n : ℕ) (v : Fin n → F) :
    (monicOfVec F n v).natDegree = n := by
  by_cases hn : n = 0
  · subst n
    simp [monicOfVec]
  · apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [monicOfVec, coeff_add, coeff_X_pow]
      have hnN : N ≠ n := ne_of_gt hN
      rw [if_neg hnN, zero_add]
      exact lowerSum_coeff_ge v (le_of_lt hN)
    · apply le_natDegree_of_ne_zero
      rw [monicOfVec_coeff_X_pow v]
      exact one_ne_zero

lemma monicOfVec_monic {F : Type u} [Field F] (n : ℕ) (v : Fin n → F) : (monicOfVec F n v).Monic := by
  by_cases hn : n = 0
  · subst n
    simp [monicOfVec]
  · rw [Monic, leadingCoeff, monicOfVec_natDegree n v]
    exact monicOfVec_coeff_X_pow v

lemma monicOfVec_coeff {F : Type u} [Field F] {n : ℕ} (v : Fin n → F) (i : Fin n) :
    (monicOfVec F n v).coeff (i : ℕ) = v i := by
  rw [monicOfVec, coeff_add, coeff_X_pow]
  have hni : n ≠ (i : ℕ) := ne_of_gt (Fin.isLt i)
  rw [if_neg (Ne.symm hni), zero_add]
  rw [finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro b _ hb
    rw [coeff_C_mul_X_pow]
    have : (b : ℕ) ≠ (i : ℕ) := by
      intro h
      apply hb
      apply Fin.ext
      exact h
    rw [if_neg (Ne.symm this)]
  · intro hni'
    simp at hni'

/-- Equivalence between monic degree-`n` polynomials and functions `Fin n → F` (the coefficients
below the leading one). -/
noncomputable def monicDegEquivFin (F : Type u) [Field F] (n : ℕ) : MonicDeg F n ≃ (Fin n → F) where
  toFun p := fun i => p.1.coeff (i : ℕ)
  invFun v := ⟨monicOfVec F n v, monicOfVec_monic n v, monicOfVec_natDegree n v⟩
  left_inv := by
    intro p
    apply Subtype.ext
    have hp_coeff_n : p.1.coeff n = 1 := by
      calc
        p.1.coeff n = p.1.coeff (p.1.natDegree) := by rw [p.2.2]
        _ = p.1.leadingCoeff := by rfl
        _ = 1 := p.2.1
    apply Polynomial.ext
    intro k
    by_cases hk : k < n
    · calc
        (monicOfVec F n (fun i : Fin n => p.1.coeff (i : ℕ))).coeff k
            = (fun i : Fin n => p.1.coeff (i : ℕ)) ⟨k, hk⟩ := monicOfVec_coeff _ ⟨k, hk⟩
        _ = p.1.coeff k := rfl
    · have hkn : n ≤ k := le_of_not_gt hk
      rcases hkn.eq_or_lt with rfl | hlt
      · calc
          (monicOfVec F n (fun i : Fin n => p.1.coeff (i : ℕ))).coeff n = 1 := monicOfVec_coeff_X_pow _
          _ = p.1.coeff n := hp_coeff_n.symm
      · have h1 : (monicOfVec F n (fun i : Fin n => p.1.coeff (i : ℕ))).coeff k = 0 := by
          rw [monicOfVec, coeff_add, coeff_X_pow, if_neg (ne_of_gt hlt), zero_add]
          exact lowerSum_coeff_ge _ (le_of_lt hlt)
        have h2 : p.1.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by rw [p.2.2]; exact hlt)
        rw [h1, h2]
  right_inv := by
    intro v
    funext i
    exact monicOfVec_coeff v i

section Finite

variable {F : Type u} [Field F] [Fintype F]

noncomputable instance instFintypeMonicDeg (n : ℕ) : Fintype (MonicDeg F n) :=
  Fintype.ofEquiv (Fin n → F) (monicDegEquivFin F n).symm

lemma cardMonicDeg (n : ℕ) : Fintype.card (MonicDeg F n) = Fintype.card F ^ n := by
  have h := Fintype.card_congr (monicDegEquivFin F n)
  rw [Fintype.card_fun, Fintype.card_fin] at h
  exact h

/-- squarefree monic degree-`n` as a subtype of `MonicDeg n` -/
def sqfreeMonicDegEquivSubtype (n : ℕ) :
    SqfreeMonicDeg F n ≃ {p : MonicDeg F n // Squarefree (p : F[X])} where
  toFun p := ⟨⟨p.1, p.2.1, p.2.2.1⟩, p.2.2.2⟩
  invFun p := ⟨p.1.1, p.1.2.1, p.1.2.2, p.2⟩
  left_inv := by
    intro p
    cases p with
    | mk q hq =>
      rfl
  right_inv := by
    intro p
    cases p with
    | mk q hq =>
      rfl

noncomputable instance instFintypeSqfreeMonicDeg (n : ℕ) : Fintype (SqfreeMonicDeg F n) := by
  classical
  exact Fintype.ofEquiv {p : MonicDeg F n // Squarefree (p : F[X])} (sqfreeMonicDegEquivSubtype n).symm

end Finite


section Decompose

open UniqueFactorizationMonoid

variable {F : Type u} [Field F] [DecidableEq F]

/-- The squarefree (odd-part) kernel of a polynomial: product of its monic irreducible factors
each to exponent 0 or 1 according to parity of its multiplicity in `p`. -/
noncomputable def sqfreePart (p : F[X]) : F[X] :=
  ∏ m ∈ (normalizedFactors p).toFinset, m ^ ((normalizedFactors p).count m % 2)

/-- The "square part" of a polynomial: `p = sqfreePart p * (squarePart p) ^ 2`. -/
noncomputable def squarePart (p : F[X]) : F[X] :=
  ∏ m ∈ (normalizedFactors p).toFinset, m ^ ((normalizedFactors p).count m / 2)

/-- the finset of monic irreducibles dividing `p` with odd multiplicity -/
noncomputable def oddSupport (p : F[X]) : Finset F[X] :=
  (normalizedFactors p).toFinset.filter (fun m => Odd ((normalizedFactors p).count m))

lemma prod_normalizedFactors_monic {p : F[X]} (hp : p.Monic) : (normalizedFactors p).prod = p := by
  have h := Polynomial.leadingCoeff_mul_prod_normalizedFactors p
  rw [hp.leadingCoeff, map_one, one_mul] at h
  exact h

lemma monic_mem_normalizedFactors {p q : F[X]} (hq : q ≠ 0) (hp : p ∈ normalizedFactors q) :
    p.Monic := ((Polynomial.mem_normalizedFactors_iff hq).mp hp).2.1

lemma irreducible_mem_normalizedFactors {p q : F[X]} (hq : q ≠ 0) (hp : p ∈ normalizedFactors q) :
    Irreducible p := ((Polynomial.mem_normalizedFactors_iff hq).mp hp).1

lemma mul_sqfreePart_squarePart {p : F[X]} (hp : p.Monic) :
    p = sqfreePart p * (squarePart p) ^ 2 := by
  have hpne : p ≠ 0 := hp.ne_zero
  have hprod : sqfreePart p * (squarePart p) ^ 2 = (normalizedFactors p).prod := by
    simp only [sqfreePart, squarePart]
    rw [← Finset.prod_pow]
    rw [← Finset.prod_mul_distrib]
    rw [Finset.prod_multiset_count]
    apply Finset.prod_congr rfl
    intro m hm
    let c := (normalizedFactors p).count m
    change m ^ (c % 2) * (m ^ (c / 2)) ^ 2 = m ^ c
    have hpow : (m ^ (c / 2)) ^ 2 = m ^ (2 * (c / 2)) := by
      calc
        (m ^ (c / 2)) ^ 2 = m ^ ((c / 2) * 2) := (pow_mul m (c / 2) 2).symm
        _ = m ^ (2 * (c / 2)) := by rw [Nat.mul_comm]
    rw [hpow, ← pow_add, Nat.mod_add_div c 2]
  rw [hprod]
  exact (prod_normalizedFactors_monic hp).symm

lemma monic_sqfreePart {p : F[X]} (hp : p.Monic) : (sqfreePart p).Monic := by
  rw [sqfreePart]
  apply monic_prod_of_monic
  intro m hm
  exact (monic_mem_normalizedFactors hp.ne_zero (Multiset.mem_toFinset.mp hm)).pow _

lemma monic_squarePart {p : F[X]} (hp : p.Monic) : (squarePart p).Monic := by
  rw [squarePart]
  apply monic_prod_of_monic
  intro m hm
  exact (monic_mem_normalizedFactors hp.ne_zero (Multiset.mem_toFinset.mp hm)).pow _

lemma count_eq_zero_of_not_odd {n : ℕ} (hn : ¬ Odd n) : n % 2 = 0 := by
  have hne : n % 2 ≠ 1 := by
    intro h
    apply hn
    exact Nat.odd_iff.mpr h
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
  omega

lemma sqfreePart_eq_prod_oddSupport (p : F[X]) :
    sqfreePart p = ∏ m ∈ oddSupport p, m := by
  rw [sqfreePart, oddSupport]
  have hprod : (∏ m ∈ (normalizedFactors p).toFinset, m ^ ((normalizedFactors p).count m % 2)) =
      ∏ m ∈ (normalizedFactors p).toFinset.filter (fun m => Odd ((normalizedFactors p).count m)),
        m ^ ((normalizedFactors p).count m % 2) := by
    refine (Finset.prod_subset (Finset.filter_subset _ _) ?_).symm
    intro x hxS hxnotB
    have hnotodd : ¬ Odd ((normalizedFactors p).count x) := by
      intro ho
      apply hxnotB
      exact Finset.mem_filter.mpr ⟨hxS, ho⟩
    rw [count_eq_zero_of_not_odd hnotodd]
    simp
  rw [hprod]
  apply Finset.prod_congr rfl
  intro m hm
  have hodd : Odd ((normalizedFactors p).count m) := (Finset.mem_filter.mp hm).2
  rw [Nat.odd_iff.mp hodd]
  simp

lemma squarefree_sqfreePart {p : F[X]} (hp : p.Monic) : Squarefree (sqfreePart p) := by
  have hs : (sqfreePart p).Monic := monic_sqfreePart hp
  have hsne : sqfreePart p ≠ 0 := hs.ne_zero
  rw [squarefree_iff_nodup_normalizedFactors hsne]
  have hsq : sqfreePart p = (oddSupport p).val.prod := by
    rw [sqfreePart_eq_prod_oddSupport p]
    simp
  have hnf : normalizedFactors (sqfreePart p) = (oddSupport p).val.map normalize := by
    rw [hsq]
    apply normalizedFactors_prod_eq
    intro a ha
    apply irreducible_mem_normalizedFactors hp.ne_zero
    have haB : a ∈ oddSupport p := by
      simpa using (Multiset.mem_toFinset.mpr ha)
    exact Multiset.mem_toFinset.mp ((Finset.mem_filter.mp haB).1)
  rw [hnf]
  -- elements of oddSupport are monic, so normalize acts as identity
  have hnorm : (oddSupport p).val.map normalize = (oddSupport p).val := by
    have hmap : (oddSupport p).val.map normalize = (oddSupport p).val.map id := by
      apply Multiset.map_congr rfl
      intro a ha
      have haB : a ∈ oddSupport p := by
        simpa using (Multiset.mem_toFinset.mpr ha)
      exact (monic_mem_normalizedFactors hp.ne_zero
        (Multiset.mem_toFinset.mp ((Finset.mem_filter.mp haB).1))).normalize_eq_self
    rw [hmap]
    simp
  rw [hnorm]
  exact (oddSupport p).nodup


lemma count_mod_two_of_le_one {c k : ℕ} (hc : c ≤ 1) : (c + 2 * k) % 2 = c := by
  interval_cases c <;> simp

lemma count_div_two_of_le_one {c k : ℕ} (hc : c ≤ 1) : (c + 2 * k) / 2 = k := by
  interval_cases c <;> simp [Nat.add_mul_div_left _ _ (by decide : 0 < 2)]

/-- Unique squarefree-square decomposition of a monic polynomial: if `p = s * h^2` with `s`
squarefree monic and `h` monic, then `s` and `h` are the odd part and square part of `p`. -/
lemma sqfreePart_eq_of_squarefree_mul_square {p s h : F[X]} (hs : s.Monic) (hh : h.Monic)
    (hsf : Squarefree s) (hdecomp : p = s * h ^ 2) : s = sqfreePart p ∧ h = squarePart p := by
  have hpne : p ≠ 0 := by
    rw [hdecomp]
    exact mul_ne_zero hs.ne_zero (pow_ne_zero 2 hh.ne_zero)
  have hM : normalizedFactors p = normalizedFactors s + 2 • normalizedFactors h := by
    rw [hdecomp]
    rw [normalizedFactors_mul hs.ne_zero (pow_ne_zero 2 hh.ne_zero)]
    rw [normalizedFactors_pow 2]
  have hN : Multiset.Nodup (normalizedFactors s) :=
    (squarefree_iff_nodup_normalizedFactors hs.ne_zero).mp hsf
  have hcount : ∀ m : F[X], (normalizedFactors p).count m =
      (normalizedFactors s).count m + 2 * (normalizedFactors h).count m := by
    intro m
    have h1 := congrArg (fun M : Multiset F[X] => M.count m) hM
    simpa [Nat.mul_comm] using h1
  have hmod : ∀ m : F[X], (normalizedFactors p).count m % 2 = (normalizedFactors s).count m := by
    intro m
    rw [hcount m]
    exact count_mod_two_of_le_one ((Multiset.nodup_iff_count_le_one.mp hN) m)
  have hdiv : ∀ m : F[X], (normalizedFactors p).count m / 2 = (normalizedFactors h).count m := by
    intro m
    rw [hcount m]
    exact count_div_two_of_le_one ((Multiset.nodup_iff_count_le_one.mp hN) m)
  have hsubsetS : (normalizedFactors s).toFinset ⊆ (normalizedFactors p).toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset] at ha ⊢
    have hpos : 0 < (normalizedFactors s).count a := (Multiset.count_pos).mpr ha
    have hle : (normalizedFactors s).count a ≤ (normalizedFactors p).count a := by
      rw [hcount a]
      omega
    exact Multiset.count_pos.mp (lt_of_lt_of_le hpos hle)
  have hsubsetH : (normalizedFactors h).toFinset ⊆ (normalizedFactors p).toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset] at ha ⊢
    have hpos : 0 < (normalizedFactors h).count a := (Multiset.count_pos).mpr ha
    have hle : 2 * (normalizedFactors h).count a ≤ (normalizedFactors p).count a := by
      rw [hcount a]
      omega
    exact Multiset.count_pos.mp (lt_of_lt_of_le (by omega) hle)
  have hs_eq : s = sqfreePart p := by
    calc
      s = (normalizedFactors s).prod := (prod_normalizedFactors_monic hs).symm
      _ = ∏ m ∈ (normalizedFactors s).toFinset, m ^ (normalizedFactors s).count m := by
        rw [Finset.prod_multiset_count]
      _ = ∏ m ∈ (normalizedFactors p).toFinset, m ^ (normalizedFactors s).count m := by
        refine (Finset.prod_subset hsubsetS ?_)
        intro x hxM hxNs
        have h0 : (normalizedFactors s).count x = 0 := by
          refine Multiset.count_eq_zero.mpr ?_
          intro hx
          apply hxNs
          exact Multiset.mem_toFinset.mpr hx
        rw [h0]
        simp
      _ = ∏ m ∈ (normalizedFactors p).toFinset, m ^ ((normalizedFactors p).count m % 2) := by
        apply Finset.prod_congr rfl
        intro m hm
        rw [hmod m]
      _ = sqfreePart p := by rw [sqfreePart]
  have hh_eq : h = squarePart p := by
    calc
      h = (normalizedFactors h).prod := (prod_normalizedFactors_monic hh).symm
      _ = ∏ m ∈ (normalizedFactors h).toFinset, m ^ (normalizedFactors h).count m := by
        rw [Finset.prod_multiset_count]
      _ = ∏ m ∈ (normalizedFactors p).toFinset, m ^ (normalizedFactors h).count m := by
        refine (Finset.prod_subset hsubsetH ?_)
        intro x hxM hxNh
        have h0 : (normalizedFactors h).count x = 0 := by
          refine Multiset.count_eq_zero.mpr ?_
          intro hx
          apply hxNh
          exact Multiset.mem_toFinset.mpr hx
        rw [h0]
        simp
      _ = ∏ m ∈ (normalizedFactors p).toFinset, m ^ ((normalizedFactors p).count m / 2) := by
        apply Finset.prod_congr rfl
        intro m hm
        rw [hdiv m]
      _ = squarePart p := by rw [squarePart]
  exact ⟨hs_eq, hh_eq⟩

/-- Degree identity `deg p = deg s + 2 deg h` for the decomposition `p = s h²`. -/
lemma natDegree_mul_sqfreePart_squarePart {p : F[X]} (hp : p.Monic) :
    p.natDegree = (sqfreePart p).natDegree + 2 * (squarePart p).natDegree := by
  have hs : (sqfreePart p).Monic := monic_sqfreePart hp
  have hh : (squarePart p).Monic := monic_squarePart hp
  have hh2 : ((squarePart p) ^ 2).Monic := hh.pow 2
  have hprod : p.natDegree = (sqfreePart p * (squarePart p) ^ 2).natDegree :=
    congrArg Polynomial.natDegree (mul_sqfreePart_squarePart hp)
  calc
    p.natDegree = (sqfreePart p * (squarePart p) ^ 2).natDegree := hprod
    _ = (sqfreePart p).natDegree + ((squarePart p) ^ 2).natDegree := hs.natDegree_mul hh2
    _ = (sqfreePart p).natDegree + 2 * (squarePart p).natDegree := by
      rw [hh.natDegree_pow 2]

end Decompose


section Recursion

variable {F : Type u} [Field F] [Fintype F]

/-- index `deg (squarePart p)` of a monic degree-`n` polynomial `p` (an element of
`Fin (n / 2 + 1)`) -/
noncomputable def monicDegIndex (n : ℕ) (p : MonicDeg F n) : Fin (n / 2 + 1) := by
  classical
  let h : F[X] := squarePart p.1
  refine ⟨h.natDegree, ?_⟩
  have hdeg : p.1.natDegree = (sqfreePart p.1).natDegree + 2 * h.natDegree := by
    dsimp [h]
    exact natDegree_mul_sqfreePart_squarePart p.2.1
  have hle : 2 * h.natDegree ≤ n := by
    have : (sqfreePart p.1).natDegree + 2 * h.natDegree ≤ n := by rw [← hdeg, p.2.2]
    omega
  rw [Nat.lt_succ_iff]
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
  omega

/-- the fiber of `monicDegIndex` over `j` -/
abbrev FiberJ (F : Type u) [Field F] [Fintype F] (n : ℕ) (j : Fin (n / 2 + 1)) : Type u :=
  {p : MonicDeg F n // monicDegIndex n p = j}

noncomputable instance instFintypeFiberJ (n : ℕ) (j : Fin (n / 2 + 1)) : Fintype (FiberJ F n j) := by
  classical
  infer_instance


/-- equivalence between the fiber over `j` and squarefree-monic-degree-`n-2j` × monic-degree-`j` -/
noncomputable def fiberEquiv (n : ℕ) (j : Fin (n / 2 + 1)) :
    FiberJ F n j ≃ (SqfreeMonicDeg F (n - 2 * (j : ℕ)) × MonicDeg F (j : ℕ)) where
  toFun := by
    intro p
    classical
    have hdeg : (squarePart p.1.1).natDegree = (j : ℕ) := by
      have hv := congrArg Fin.val p.2
      simpa [monicDegIndex] using hv
    have hdegS : (sqfreePart p.1.1).natDegree = n - 2 * (j : ℕ) := by
      have hdegsum : p.1.1.natDegree = (sqfreePart p.1.1).natDegree +
          2 * (squarePart p.1.1).natDegree := natDegree_mul_sqfreePart_squarePart p.1.2.1
      rw [p.1.2.2] at hdegsum
      omega
    exact ⟨⟨sqfreePart p.1.1, monic_sqfreePart p.1.2.1, hdegS, squarefree_sqfreePart p.1.2.1⟩,
      ⟨squarePart p.1.1, monic_squarePart p.1.2.1, hdeg⟩⟩
  invFun := by
    intro sh
    classical
    let p : F[X] := sh.1.1 * sh.2.1 ^ 2
    have hmon : p.Monic := (sh.1.2.1).mul ((sh.2.2.1).pow 2)
    have hpdeg : p.natDegree = n := by
      have hsm : sh.1.1.Monic := sh.1.2.1
      have hhm : sh.2.1.Monic := sh.2.2.1
      have hmul : p.natDegree = sh.1.1.natDegree + (sh.2.1 ^ 2).natDegree := hsm.natDegree_mul (hhm.pow 2)
      have hpow : (sh.2.1 ^ 2).natDegree = 2 * sh.2.1.natDegree := hhm.natDegree_pow 2
      have hsdeg : sh.1.1.natDegree = n - 2 * (j : ℕ) := sh.1.2.2.1
      have hhdeg : sh.2.1.natDegree = (j : ℕ) := sh.2.2.2
      have hj : (j : ℕ) ≤ n / 2 := Nat.lt_succ_iff.mp j.isLt
      have h2j : 2 * (j : ℕ) ≤ n := by
        have h := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hj
        omega
      calc
        p.natDegree = (n - 2 * (j : ℕ)) + 2 * (j : ℕ) := by rw [hmul, hpow, hsdeg, hhdeg]
        _ = n := Nat.sub_add_cancel h2j
    refine ⟨⟨p, hmon, hpdeg⟩, ?_⟩
    -- monicDegIndex of this polynomial is j
    have hu := sqfreePart_eq_of_squarefree_mul_square sh.1.2.1 sh.2.2.1 sh.1.2.2.2
      (rfl : p = sh.1.1 * sh.2.1 ^ 2)
    apply Fin.ext
    dsimp [monicDegIndex]
    rw [← hu.2]
    exact sh.2.2.2
  left_inv := by
    intro p
    classical
    apply Subtype.ext
    apply Subtype.ext
    exact (mul_sqfreePart_squarePart p.1.2.1).symm
  right_inv := by
    intro sh
    classical
    let p : F[X] := sh.1.1 * sh.2.1 ^ 2
    have hu := sqfreePart_eq_of_squarefree_mul_square sh.1.2.1 sh.2.2.1 sh.1.2.2.2
      (rfl : p = sh.1.1 * sh.2.1 ^ 2)
    apply Prod.ext
    · apply Subtype.ext
      exact hu.1.symm
    · apply Subtype.ext
      exact hu.2.symm


/-- The recursion `q^n = SF n + Σ_{j < n/2} q^(j+1) SF (n - 2(j+1))`. -/
lemma recursion_card (n : ℕ) :
    (Fintype.card F) ^ n =
      Fintype.card (SqfreeMonicDeg F n) +
        ∑ j ∈ Finset.range (n / 2), (Fintype.card F) ^ (j + 1) *
          Fintype.card (SqfreeMonicDeg F (n - 2 * (j + 1))) := by
  classical
  have h0 : (Fintype.card F) ^ n = Fintype.card (MonicDeg F n) := (cardMonicDeg n).symm
  -- each fiber of `monicDegIndex` is finite (an explicit local instance)
  letI instFib : ∀ j : Fin (n / 2 + 1),
      Fintype {p : MonicDeg F n // monicDegIndex n p = j} :=
    fun j => by infer_instance
  have hfib : Fintype.card (MonicDeg F n) =
      ∑ j : Fin (n / 2 + 1), Fintype.card (FiberJ F n j) := by
    have h := Fintype.card_congr
      ((Equiv.sigmaFiberEquiv (α := MonicDeg F n) (β := Fin (n / 2 + 1)) (monicDegIndex n)).symm)
    rw [Fintype.card_sigma] at h
    simpa using h
  have h2 : Fintype.card (MonicDeg F n) =
      ∑ j : Fin (n / 2 + 1), Fintype.card (SqfreeMonicDeg F (n - 2 * (j : ℕ))) *
        (Fintype.card F) ^ (j : ℕ) := by
    rw [hfib]
    apply Finset.sum_congr rfl
    intro j hj
    have hfj : Fintype.card (FiberJ F n j) =
        Fintype.card (SqfreeMonicDeg F (n - 2 * (j : ℕ))) * Fintype.card (MonicDeg F (j : ℕ)) := by
      have h := @Fintype.card_congr (FiberJ F n j)
        (SqfreeMonicDeg F (n - 2 * (j : ℕ)) × MonicDeg F (j : ℕ))
        (instFintypeFiberJ n j) (inferInstance) (fiberEquiv n j)
      rw [Fintype.card_prod] at h
      simpa using h
    rw [hfj, cardMonicDeg (j : ℕ)]
  rw [h0, h2]
  let g : ℕ → ℕ := fun i => Fintype.card (SqfreeMonicDeg F (n - 2 * i)) * (Fintype.card F) ^ i
  have hfin : (∑ j : Fin (n / 2 + 1), Fintype.card (SqfreeMonicDeg F (n - 2 * (j : ℕ))) *
        (Fintype.card F) ^ (j : ℕ)) = (∑ i ∈ Finset.range (n / 2 + 1), g i) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi)]
  rw [hfin]
  rw [Finset.sum_range_succ']
  rw [add_comm]
  have hg0 : g 0 = Fintype.card (SqfreeMonicDeg F n) := by
    simp [g]
  rw [hg0]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hgi : g (i + 1) = (Fintype.card F) ^ (i + 1) *
      Fintype.card (SqfreeMonicDeg F (n - 2 * (i + 1))) := by
    simp [g, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  rw [hgi]

/-- every monic polynomial of degree one is squarefree -/
lemma monic_squarefree_of_natDegree_one {p : F[X]} (hp : p.Monic) (hdeg : p.natDegree = 1) :
    Squarefree p := by
  have hdeg' : p.degree = 1 := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, hdeg]
    norm_num
  exact (Polynomial.irreducible_of_degree_eq_one hdeg').squarefree

/-- the monic polynomial of degree zero is `1`; hence squarefree -/
lemma monic_squarefree_of_natDegree_zero {p : F[X]} (hp : p.Monic) (hdeg : p.natDegree = 0) :
    Squarefree p := by
  have hd : p.degree = 0 := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, hdeg]
    norm_num
  have hp1 : p = 1 := (hp.degree_le_zero_iff_eq_one).mp (by simp [hd])
  rw [hp1]
  exact squarefree_one

noncomputable def sqfreeMonicDegOneEquivMonicDeg : SqfreeMonicDeg F 1 ≃ MonicDeg F 1 where
  toFun p := ⟨p.1, p.2.1, p.2.2.1⟩
  invFun p := ⟨p.1, p.2.1, p.2.2, monic_squarefree_of_natDegree_one p.2.1 p.2.2⟩
  left_inv := by
    intro p
    rfl
  right_inv := by
    intro p
    rfl

noncomputable def sqfreeMonicDegZeroEquivMonicDeg : SqfreeMonicDeg F 0 ≃ MonicDeg F 0 where
  toFun p := ⟨p.1, p.2.1, p.2.2.1⟩
  invFun p := ⟨p.1, p.2.1, p.2.2, monic_squarefree_of_natDegree_zero p.2.1 p.2.2⟩
  left_inv := by
    intro p
    rfl
  right_inv := by
    intro p
    rfl

lemma cardSqfree_zero :
    @Fintype.card (SqfreeMonicDeg F 0) (instFintypeSqfreeMonicDeg 0) = 1 := by
  classical
  have h := @Fintype.card_congr (SqfreeMonicDeg F 0) (MonicDeg F 0)
    (instFintypeSqfreeMonicDeg 0) (instFintypeMonicDeg 0) sqfreeMonicDegZeroEquivMonicDeg
  have h2 : @Fintype.card (MonicDeg F 0) (instFintypeMonicDeg 0) = 1 := by
    have he := @Fintype.card_congr (MonicDeg F 0) (Fin 0 → F) (instFintypeMonicDeg 0)
      (inferInstance : Fintype (Fin 0 → F)) (monicDegEquivFin F 0)
    rw [Fintype.card_fun, Fintype.card_fin] at he
    simpa using he
  rw [h2] at h
  simpa using h

lemma cardSqfree_one :
    @Fintype.card (SqfreeMonicDeg F 1) (instFintypeSqfreeMonicDeg 1) = Fintype.card F := by
  classical
  have h := @Fintype.card_congr (SqfreeMonicDeg F 1) (MonicDeg F 1)
    (instFintypeSqfreeMonicDeg 1) (instFintypeMonicDeg 1) sqfreeMonicDegOneEquivMonicDeg
  have h2 : @Fintype.card (MonicDeg F 1) (instFintypeMonicDeg 1) = Fintype.card F := by
    have he := @Fintype.card_congr (MonicDeg F 1) (Fin 1 → F) (instFintypeMonicDeg 1)
      (inferInstance : Fintype (Fin 1 → F)) (monicDegEquivFin F 1)
    rw [Fintype.card_fun, Fintype.card_fin] at he
    simpa using he
  rw [h2] at h
  simpa using h

end Recursion

end SqfreeMonicCardInternal


namespace Commons.FieldTheory.Polynomial

open SqfreeMonicCardInternal

/-- The number of squarefree monic polynomials of degree `n ≥ 2` over a finite field `F` is
`q^n − q^(n−1)`, `q = Fintype.card F`. -/
theorem squarefree_monic_card {F : Type*} [Field F] [Fintype F] (n : ℕ) (hn : 2 ≤ n) :
    ({p : F[X] | p.Monic ∧ p.natDegree = n ∧ Squarefree p} : Set (F[X])).ncard =
      Fintype.card F ^ n - Fintype.card F ^ (n - 1) := by
  classical
  let q : ℕ := Fintype.card F
  let SF : ℕ → ℕ := fun m => Fintype.card (SqfreeMonicDeg F m)
  have hSF0 : SF 0 = 1 := by
    dsimp [SF]
    exact cardSqfree_zero
  have hSF1 : SF 1 = q := by
    dsimp [SF, q]
    exact cardSqfree_one
  have hrec : ∀ m : ℕ, 2 ≤ m →
      q ^ m = SF m + ∑ j ∈ Finset.range (m / 2), q ^ (j + 1) * SF (m - 2 * (j + 1)) := by
    intro m hm
    dsimp [q, SF]
    exact recursion_card m
  have hclosed : SF n = q ^ n - q ^ (n - 1) :=
    Commons.Nat.squarefree_count_closed (q := q) (SF := SF) hSF0 hSF1 hrec n hn
  let s : Set F[X] := {p : F[X] | p.Monic ∧ p.natDegree = n ∧ Squarefree p}
  have hcard : s.ncard = Fintype.card (SqfreeMonicDeg F n) := by
    dsimp [s]
    rw [← @Set.fintypeCard_eq_ncard F[X] {p : F[X] | p.Monic ∧ p.natDegree = n ∧ Squarefree p}
      (instFintypeSqfreeMonicDeg n)]
    rfl
  rw [hcard]
  dsimp [SF, q] at hclosed ⊢
  exact hclosed

end Commons.FieldTheory.Polynomial
