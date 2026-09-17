import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.TotallySplit

/-!
# A `q`-ary lattice with no short vector

We prove that if the number of non-zero integer vectors `x` with `0 < |x|^2 ≤ R^2` is
smaller than `2 q^m`, then some `m × d` matrix `A` over `ZMod q` has the property that
`x A ≠ 0` for every such `x`.

The proof is a double counting argument.  A matrix `A` is *bad* for `x` when `x A = 0`.
For a fixed non-zero `x` (whose reduction modulo `q` is non-zero, because `R < q`) the
set of bad matrices is the kernel of the surjective linear map `A ↦ x A`, hence has
cardinality `q ^ (m * (d-1))`.  The total number of pairs `(A, x)` with `x` short and
`A` bad for `x` is therefore `|short| * q ^ (m * (d-1))`.  On the other hand, if every
`A` had a bad `x`, then, since the set of bad `x` for a fixed `A` is invariant under the
*fixed point free* involution `x ↦ -x`, each of these sets would have at least `2`
elements, giving the lower bound `2 q ^ (m * d)`.  Comparing the two bounds yields
`|short| ≥ 2 q ^ m`, contradicting the hypothesis.
-/

open Finset

namespace Commons.Lattice.Counting

private lemma neg_norm {d : ℕ} (x : Fin d → ℤ) :
    (∑ i, (((-(x i)) : ℤ) : ℝ) ^ 2) = (∑ i, ((x i : ℝ)) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [Int.cast_neg, neg_sq]

private lemma norm_pos_of_ne_zero {d : ℕ} {x : Fin d → ℤ} (hx : x ≠ 0) :
    0 < ∑ i, ((x i : ℝ)) ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  have hpos : (0 : ℝ) < ((x i : ℝ)) ^ 2 := by
    have : (x i : ℝ) ≠ 0 := by exact_mod_cast hi
    positivity
  exact lt_of_lt_of_le hpos
    (Finset.single_le_sum (fun j _ => sq_nonneg ((x j : ℝ))) (Finset.mem_univ i))

/-- If `x` is a non-zero integer vector of squared norm at most `R^2 < q^2`, then not all
of its coordinates are divisible by the prime `q`. -/
private lemma exists_coord_zmod_ne_zero {q d : ℕ} [Fact q.Prime] {R : ℝ}
    (hR : 0 < R) (hRq : R < (q : ℝ)) {x : Fin d → ℤ}
    (hpos : 0 < ∑ i, ((x i : ℝ)) ^ 2) (hle : (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2) :
    ∃ j, (x j : ZMod q) ≠ 0 := by
  by_contra h
  push_neg at h
  have hxne : x ≠ 0 := by
    intro hx
    rw [hx] at hpos
    simp at hpos
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hxne (funext h')
  have hdvd : (q : ℤ) ∣ x j := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h j
  obtain ⟨k, hk⟩ := hdvd
  have hkne : k ≠ 0 := by
    rintro rfl
    simp at hk
    exact hj hk
  have hk1 : (1 : ℝ) ≤ ((k : ℝ)) ^ 2 := by
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have := Int.one_le_abs hkne
      exact_mod_cast this
    have := sq_le_sq.mpr (show |(1 : ℝ)| ≤ |(k : ℝ)| by simpa using h1)
    simpa using this
  have hq2 : ((q : ℝ)) ^ 2 ≤ ((x j : ℝ)) ^ 2 := by
    have hcast : ((x j : ℤ) : ℝ) = (q : ℝ) * (k : ℝ) := by
      rw [hk]; push_cast; ring
    rw [hcast]
    nlinarith [hk1, sq_nonneg ((q : ℝ) * (k : ℝ) - 0), sq_nonneg ((q : ℝ)), sq_nonneg ((k : ℝ))]
  have hbound : ((x j : ℝ)) ^ 2 ≤ ∑ i, ((x i : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg ((x i : ℝ))) (Finset.mem_univ j)
  have hRq2 : R ^ 2 < ((q : ℝ)) ^ 2 := by
    have h1 : 0 < (q : ℝ) := by
      have := (Fact.out : Nat.Prime q).two_le
      positivity
    nlinarith [hR, hRq]
  linarith

/-- The number of `m × d` matrices over `ZMod q` which annihilate a fixed non-zero vector
`x` (whose reduction mod `q` is non-zero) is `q ^ (m * (d - 1))`. -/
private lemma card_mat_ker {q m d : ℕ} [Fact q.Prime] (x : Fin d → ℤ) (j0 : Fin d)
    (hj0 : (x j0 : ZMod q) ≠ 0) :
    Nat.card {A : Matrix (Fin m) (Fin d) (ZMod q) // ∀ i, ∑ j, (x j : ZMod q) * A i j = 0}
      = q ^ (m * (d - 1)) := by
  classical
  let φ : Matrix (Fin m) (Fin d) (ZMod q) →ₗ[ZMod q] (Fin m → ZMod q) :=
    { toFun := fun A i => ∑ j, (x j : ZMod q) * A i j
      map_add' := by
        intro A B
        funext i
        simp only [Matrix.add_apply, Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      map_smul' := by
        intro c A
        funext i
        simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring }
  have hsurj : Function.Surjective φ := by
    intro w
    refine ⟨fun i j => if j = j0 then w i * ((x j0 : ZMod q))⁻¹ else 0, ?_⟩
    funext i
    show ∑ j, (x j : ZMod q) * (if j = j0 then w i * ((x j0 : ZMod q))⁻¹ else 0) = w i
    rw [Finset.sum_eq_single j0]
    · rw [if_pos rfl, mul_comm (w i) ((x j0 : ZMod q))⁻¹, ← mul_assoc,
        mul_inv_cancel₀ hj0, one_mul]
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ j0) h
  have hcard1 : Nat.card {A : Matrix (Fin m) (Fin d) (ZMod q) //
        ∀ i, ∑ j, (x j : ZMod q) * A i j = 0} = Nat.card φ.ker := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro A
    simp only [LinearMap.mem_ker, φ]
    constructor
    · intro h; funext i; exact h i
    · intro h i; exact congrFun h i
  have hfinrank : Module.finrank (ZMod q) φ.ker = m * (d - 1) := by
    have h1 := φ.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h1
    have hrange : Module.finrank (ZMod q) (Fin m → ZMod q) = m := by
      rw [Module.finrank_fintype_fun_eq_card]; simp
    have hM : Module.finrank (ZMod q) (Matrix (Fin m) (Fin d) (ZMod q)) = m * d := by
      change Module.finrank (ZMod q) (Fin m → Fin d → ZMod q) = m * d
      rw [Module.finrank_pi_fintype]
      simp [Module.finrank_fintype_fun_eq_card, Finset.sum_const, Finset.card_univ,
        smul_eq_mul]
    rw [hrange, hM] at h1
    have hd : 1 ≤ d := Nat.succ_le_of_lt j0.pos
    have key : m * (d - 1) + m = m * d := by
      have h1' : m * (d - 1) + m = m * (d - 1) + m * 1 := by rw [Nat.mul_one]
      rw [h1', ← Nat.mul_add, Nat.sub_add_cancel hd]
    rw [← key] at h1
    exact Nat.add_right_cancel (by rw [Nat.add_comm]; exact h1)
  have hcardker : Nat.card φ.ker = q ^ (m * (d - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod q) (V := φ.ker), hfinrank, Nat.card_zmod]
  rw [hcard1, hcardker]

/-- Abstract double counting: if every `A` has a bad `x`, every non-empty bad fiber has at
least two elements, and every `x` has exactly `c` bad `A`, then `2 |G| ≤ c |S|`. -/
private lemma double_counting {G S : Type*} [Fintype G] [Fintype S]
    (Bad : G → S → Prop) [DecidableRel Bad] (c : ℕ)
    (hconst : ∀ x : S, (Finset.univ.filter (fun A : G => Bad A x)).card = c)
    (hpair : ∀ A : G, (∃ x : S, Bad A x) →
      2 ≤ (Finset.univ.filter (fun x : S => Bad A x)).card)
    (hall : ∀ A : G, ∃ x : S, Bad A x) :
    2 * Fintype.card G ≤ c * Fintype.card S := by
  have hdouble : (∑ A : G, (Finset.univ.filter (fun x : S => Bad A x)).card)
      = ∑ x : S, (Finset.univ.filter (fun A : G => Bad A x)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hge : 2 * Fintype.card G
      ≤ ∑ A : G, (Finset.univ.filter (fun x : S => Bad A x)).card := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset G))
      (f := fun _ : G => 2)
      (g := fun A : G => (Finset.univ.filter (fun x : S => Bad A x)).card)
      (fun A _ => hpair A (hall A))
    rwa [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at h
  have hle : (∑ x : S, (Finset.univ.filter (fun A : G => Bad A x)).card)
      = c * Fintype.card S := by
    have h : ∀ x : S, (Finset.univ.filter (fun A : G => Bad A x)).card = c := hconst
    rw [Finset.sum_congr rfl (fun x _ => h x)]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  calc 2 * Fintype.card G
      ≤ ∑ A : G, (Finset.univ.filter (fun x : S => Bad A x)).card := hge
    _ = ∑ x : S, (Finset.univ.filter (fun A : G => Bad A x)).card := hdouble
    _ = c * Fintype.card S := hle

theorem exists_qary_lattice_no_short_vector {q m d : ℕ} [Fact q.Prime] {R : ℝ}
    (hR : 0 < R) (hRq : R < q)
    (hcard : (Nat.card {x : Fin d → ℤ // 0 < (∑ i, ((x i : ℝ)) ^ 2) ∧
        (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2} : ℝ) < 2 * (q : ℝ) ^ m) :
    ∃ A : Matrix (Fin m) (Fin d) (ZMod q),
      ∀ x : Fin d → ℤ, x ≠ 0 → (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2 →
        ¬ (∀ i, ∑ j, (x j : ZMod q) * A i j = 0) := by
  classical
  by_cases hd0 : d = 0
  · subst hd0
    refine ⟨0, ?_⟩
    intro x hx _ _
    exact hx (funext fun i => i.elim0)
  · have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    by_contra hneg
    let S : Type := {x : Fin d → ℤ // 0 < (∑ i, ((x i : ℝ)) ^ 2) ∧
        (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2}
    have hScard : (Nat.card S : ℝ) < 2 * (q : ℝ) ^ m := hcard
    let K : ℕ := ⌈R⌉₊
    have hKle : R ≤ (K : ℝ) := Nat.le_ceil R
    let Box : Finset (Fin d → ℤ) :=
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(K : ℤ)) (K : ℤ))
    have hbox : ∀ x : Fin d → ℤ, (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2 → x ∈ Box := by
      intro x hx
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      have hsq : ((x i : ℝ)) ^ 2 ≤ R ^ 2 :=
        le_trans (Finset.single_le_sum (fun j _ => sq_nonneg ((x j : ℝ)))
          (Finset.mem_univ i)) hx
      have habs : |(x i : ℝ)| ≤ R := by
        have := sq_le_sq.mp hsq
        rwa [abs_of_pos hR] at this
      have h1 : -(K : ℤ) ≤ x i := by
        have hle1 : -((K : ℝ)) ≤ (x i : ℝ) :=
          le_trans (neg_le_neg hKle) (abs_le.mp habs).1
        exact_mod_cast hle1
      have h2 : x i ≤ (K : ℤ) := by
        have hle2 : (x i : ℝ) ≤ (K : ℝ) := le_trans (abs_le.mp habs).2 hKle
        exact_mod_cast hle2
      exact ⟨h1, h2⟩
    haveI : Fintype S := Fintype.ofInjective
      (fun x : S => (⟨x.1, hbox x.1 x.2.2⟩ : {y : Fin d → ℤ // y ∈ Box}))
      (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
    let BadA : Matrix (Fin m) (Fin d) (ZMod q) → (Fin d → ℤ) → Prop :=
      fun A x => ∀ i, ∑ j, ((x j : ℤ) : ZMod q) * A i j = 0
    let Bad : Matrix (Fin m) (Fin d) (ZMod q) → S → Prop := fun A x => BadA A x.1
    let negS : S → S := fun x => ⟨fun i => -(x.1 i), by
      rw [neg_norm x.1]
      exact x.2⟩
    have hsum_neg : ∀ (A : Matrix (Fin m) (Fin d) (ZMod q)) (x : Fin d → ℤ) (i : Fin m),
        (∑ j, (((-(x j)) : ℤ) : ZMod q) * A i j)
          = -(∑ j, ((x j : ℤ) : ZMod q) * A i j) := by
      intro A x i
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [Int.cast_neg, neg_mul]
    have hbadA_neg : ∀ (A : Matrix (Fin m) (Fin d) (ZMod q)) (x : Fin d → ℤ),
        BadA A (fun j => -(x j)) ↔ BadA A x := by
      intro A x
      constructor
      · intro h i
        have := h i
        rw [hsum_neg A x i, neg_eq_zero] at this
        exact this
      · intro h i
        rw [hsum_neg A x i, h i, neg_zero]
    have hconst : ∀ x : S, (Finset.univ.filter (fun A => Bad A x)).card
        = q ^ (m * (d - 1)) := by
      intro x
      have hcard_eq : (Finset.univ.filter (fun A => Bad A x)).card
          = Nat.card {A : Matrix (Fin m) (Fin d) (ZMod q) // Bad A x} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [hcard_eq]
      obtain ⟨j0, hj0⟩ := exists_coord_zmod_ne_zero hR hRq x.2.1 x.2.2
      simpa [Bad, BadA] using card_mat_ker x.1 j0 hj0
    have hpair : ∀ A : Matrix (Fin m) (Fin d) (ZMod q),
        (∃ x : S, Bad A x) →
          2 ≤ (Finset.univ.filter (fun x : S => Bad A x)).card := by
      intro A hx
      obtain ⟨x, hxbad⟩ := hx
      have hxne : x.1 ≠ 0 := by
        intro hzero
        have h0 : (∑ i, ((x.1 i : ℝ)) ^ 2) = 0 := by rw [hzero]; simp
        linarith [x.2.1, h0]
      obtain ⟨j, hj⟩ : ∃ j, x.1 j ≠ 0 := by
        by_contra h
        push_neg at h
        exact hxne (funext h)
      have hneg : Bad A (negS x) ↔ Bad A x := by
        have := hbadA_neg A x.1
        simpa [Bad, negS] using this
      have hne : negS x ≠ x := by
        intro h
        have h1 : (negS x).1 j = x.1 j := congrFun (congrArg Subtype.val h) j
        simp only [negS] at h1
        exact hj (by omega)
      have hmem1 : x ∈ Finset.univ.filter (fun y : S => Bad A y) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hxbad
      have hmem2 : negS x ∈ Finset.univ.filter (fun y : S => Bad A y) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hneg.mpr hxbad
      have : 1 < (Finset.univ.filter (fun y : S => Bad A y)).card := by
        rw [Finset.one_lt_card]
        exact ⟨x, hmem1, negS x, hmem2, fun h => hne h.symm⟩
      exact Nat.succ_le_of_lt this
    have hall : ∀ A : Matrix (Fin m) (Fin d) (ZMod q), ∃ x : S, Bad A x := by
      intro A
      have hA : ¬ (∀ x : Fin d → ℤ, x ≠ 0 → (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2 →
          ¬ (∀ i, ∑ j, (x j : ZMod q) * A i j = 0)) := fun hP => hneg ⟨A, hP⟩
      have hA' : ¬ (∀ x : Fin d → ℤ, x ≠ 0 → (∑ i, ((x i : ℝ)) ^ 2) ≤ R ^ 2 →
          ¬ BadA A x) := fun hP => hA (fun x hx0 hle hb => hP x hx0 hle (by simpa [BadA] using hb))
      push_neg at hA'
      obtain ⟨x, hx0, hle, hbad⟩ := hA'
      exact ⟨⟨x, norm_pos_of_ne_zero hx0, hle⟩, hbad⟩
    have hmain := double_counting (G := Matrix (Fin m) (Fin d) (ZMod q)) (S := S)
      Bad (q ^ (m * (d - 1))) hconst hpair hall
    have hGcard : Fintype.card (Matrix (Fin m) (Fin d) (ZMod q)) = q ^ (m * d) := by
      change Fintype.card (Fin m → Fin d → ZMod q) = q ^ (m * d)
      rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        ZMod.card, ← pow_mul, Nat.mul_comm d m]
    have hScarde : Fintype.card S = Nat.card S := Nat.card_eq_fintype_card.symm
    rw [hGcard, hScarde] at hmain
    have key : m * (d - 1) + m = m * d := by
      have h1' : m * (d - 1) + m = m * (d - 1) + m * 1 := by rw [Nat.mul_one]
      rw [h1', ← Nat.mul_add, Nat.sub_add_cancel hdpos]
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      have := (Fact.out : Nat.Prime q).two_le
      positivity
    have hmainR : (2 : ℝ) * (q : ℝ) ^ (m * d)
        ≤ (q : ℝ) ^ (m * (d - 1)) * (Nat.card S : ℝ) := by
      have hcast := Nat.cast_le (α := ℝ) |>.mpr hmain
      push_cast at hcast
      exact hcast
    have hqmR : (q : ℝ) ^ (m * d) = (q : ℝ) ^ (m * (d - 1)) * (q : ℝ) ^ m := by
      rw [← key, pow_add]
    rw [hqmR] at hmainR
    have hapos : (0 : ℝ) < (q : ℝ) ^ (m * (d - 1)) := pow_pos hqpos _
    have hfinal : 2 * (q : ℝ) ^ m ≤ (Nat.card S : ℝ) := by
      have h1 : (2 * (q : ℝ) ^ m) * (q : ℝ) ^ (m * (d - 1))
          ≤ (Nat.card S : ℝ) * (q : ℝ) ^ (m * (d - 1)) := by
        calc (2 * (q : ℝ) ^ m) * (q : ℝ) ^ (m * (d - 1))
            = 2 * ((q : ℝ) ^ (m * (d - 1)) * (q : ℝ) ^ m) := by ring
          _ ≤ (q : ℝ) ^ (m * (d - 1)) * (Nat.card S : ℝ) := hmainR
          _ = (Nat.card S : ℝ) * (q : ℝ) ^ (m * (d - 1)) := by ring
      exact le_of_mul_le_mul_right h1 hapos
    linarith [hScard, hfinal]

end Commons.Lattice.Counting