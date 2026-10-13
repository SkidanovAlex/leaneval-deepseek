import Mathlib

namespace Work.WilkiesH.NT

open Finset

/-- If two reals have the same floor, their difference is `< 1` in absolute value. -/
private lemma abs_sub_lt_one_of_floor_eq {a b : ℝ} (h : ⌊a⌋ = ⌊b⌋) : |a - b| < 1 := by
  have h1 : ((⌊a⌋ : ℤ) : ℝ) = ((⌊b⌋ : ℤ) : ℝ) := by rw [h]
  have h2 := Int.floor_le a
  have h3 := Int.floor_le b
  have h4 := Int.lt_floor_add_one a
  have h5 := Int.lt_floor_add_one b
  rw [abs_lt]
  constructor <;> linarith

/-- If `x` ranges over the box `{0, …, Q}^N`, then every row of `A` evaluated at `x` is
bounded by `K` in absolute value, under the hypotheses of Siegel's lemma. -/
private lemma box_bound {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ i j, |A i j| ≤ B) (Q K : ℕ) (hK : (N : ℝ) * B * Q ≤ (K : ℝ))
    (x : Fin N → Fin (Q+1)) (i : Fin M) :
    |∑ j, A i j * ((x j : ℕ) : ℝ)| ≤ (K : ℝ) := by
  have h1 : |∑ j, A i j * ((x j : ℕ) : ℝ)| ≤ ∑ j, |A i j * ((x j : ℕ) : ℝ)| :=
    Finset.abs_sum_le_sum_abs (fun j => A i j * ((x j : ℕ) : ℝ)) Finset.univ
  have h2 : ∑ j, |A i j * ((x j : ℕ) : ℝ)| ≤ ∑ _j : Fin N, B * (Q : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    have hyQ : ((x j : ℕ) : ℕ) ≤ Q := by
      have := (x j).isLt
      omega
    have hyQ' : ((x j : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hyQ
    have habs : |((x j : ℕ) : ℝ)| = ((x j : ℕ) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    rw [habs]
    exact mul_le_mul (hA i j) hyQ' (Nat.cast_nonneg _) hB
  have h3 : ∑ _j : Fin N, B * (Q : ℝ) = (N : ℝ) * B * Q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
    ring
  calc |∑ j, A i j * ((x j : ℕ) : ℝ)| ≤ ∑ j, |A i j * ((x j : ℕ) : ℝ)| := h1
    _ ≤ ∑ _j : Fin N, B * (Q : ℝ) := h2
    _ = (N : ℝ) * B * Q := h3
    _ ≤ (K : ℝ) := hK

/-- **Siegel's lemma (pigeonhole form).**  For an `M × N` real matrix `A` whose entries are
bounded by `B ≥ 0`, if `N·B·Q ≤ K` and `(Q+1)^N > (2K+1)^M`, then there is a nonzero integer
vector `x` with `|x_j| ≤ Q` and `|A x| ≤ 1` in the sup norm.

Proof: map each of the `(Q+1)^N` points of `{0, …, Q}^N` to the vector of floors of `A x`.  Every
entry of `A x` lies in `[-K, K]`, so the floors range over the `(2K+1)^M` points of the box
`{-K, …, K}^M`; by pigeonhole two distinct points `x, x'` share the same floor vector.  Their
difference `x - x'` is a nonzero integer vector with entries in `[-Q, Q]`, and `A(x-x')` has all
entries of absolute value `< 1`. -/
theorem siegel_approx {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ i j, |A i j| ≤ B) (Q K : ℕ) (hK : (N : ℝ) * B * Q ≤ (K : ℝ))
    (hcard : (Q + 1) ^ N > (2 * K + 1) ^ M) :
    ∃ x : Fin N → ℤ, x ≠ 0 ∧ (∀ j, |x j| ≤ (Q : ℤ)) ∧
      ∀ i, |∑ j, A i j * ((x j : ℤ) : ℝ)| ≤ 1 := by
  -- The target box `{-K, …, K}^M` has cardinality `(2K+1)^M`.
  have hTcard :
      (Fintype.piFinset (fun _ : Fin M => Finset.Icc (-(K:ℤ)) (K:ℤ))).card = (2*K+1)^M := by
    rw [Fintype.card_piFinset]
    have hc : ∀ i : Fin M, (Finset.Icc (-(K:ℤ)) (K:ℤ)).card = 2*K+1 := fun i => by
      rw [Int.card_Icc]
      have h : (K:ℤ) + 1 - (-(K:ℤ)) = ((2*K+1 : ℕ) : ℤ) := by push_cast; ring
      rw [h, Int.toNat_natCast]
    rw [show (∏ i : Fin M, (Finset.Icc (-(K:ℤ)) (K:ℤ)).card) = (∏ _i : Fin M, (2*K+1)) from
        Finset.prod_congr rfl (fun i _ => hc i)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- The source box `{0, …, Q}^N` has cardinality `(Q+1)^N`.
  have hScard : (Finset.univ : Finset (Fin N → Fin (Q+1))).card = (Q+1)^N := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  -- The floor map sends the source box into the target box.
  have hmaps :
      Set.MapsTo (fun x : Fin N → Fin (Q+1) => fun i : Fin M => ⌊∑ j, A i j * ((x j : ℕ) : ℝ)⌋)
        ↑(Finset.univ : Finset (Fin N → Fin (Q+1)))
        ↑(Fintype.piFinset (fun _ : Fin M => Finset.Icc (-(K:ℤ)) (K:ℤ))) := by
    intro x _
    change (fun i : Fin M => ⌊∑ j, A i j * ((x j : ℕ) : ℝ)⌋)
      ∈ (Fintype.piFinset (fun _ : Fin M => Finset.Icc (-(K:ℤ)) (K:ℤ)) : Finset (Fin M → ℤ))
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hb := abs_le.mp (box_bound A hB hA Q K hK x i)
    constructor
    · rw [Int.le_floor]
      push_cast
      exact hb.1
    · have hle := box_bound A hB hA Q K hK x i
      have hfl : ⌊∑ j, A i j * ((x j : ℕ) : ℝ)⌋ ≤ (K:ℤ) := by
        have := Int.floor_le_floor (le_trans (le_abs_self _) hle)
        simpa using this
      exact hfl
  -- Pigeonhole: two distinct source points have the same floor vector.
  obtain ⟨x, _, x', _, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := (Finset.univ : Finset (Fin N → Fin (Q+1))))
      (t := Fintype.piFinset (fun _ : Fin M => Finset.Icc (-(K:ℤ)) (K:ℤ)))
      (by rw [hTcard, hScard]; exact hcard) hmaps
  have hfloor : ∀ i, ⌊∑ j, A i j * ((x j : ℕ) : ℝ)⌋ = ⌊∑ j, A i j * ((x' j : ℕ) : ℝ)⌋ :=
    fun i => congrFun heq i
  -- The candidate vector is the difference of the two colliding points.
  let d : Fin N → ℤ := fun j => ((x j : ℕ) : ℤ) - ((x' j : ℕ) : ℤ)
  refine ⟨d, ?_, ?_, ?_⟩
  · intro h
    apply hne
    funext j
    have hj : ((x j : ℕ) : ℤ) - ((x' j : ℕ) : ℤ) = 0 := congrFun h j
    have : (x j : ℕ) = (x' j : ℕ) := by omega
    exact Fin.ext this
  · intro j
    rw [abs_le]
    constructor <;> (simp only [d]; omega)
  · intro i
    have hcast : ∀ j : Fin N, ((d j : ℤ) : ℝ) = ((x j : ℕ) : ℝ) - ((x' j : ℕ) : ℝ) := by
      intro j; simp only [d]; push_cast; ring
    have hsum : ∑ j, A i j * ((d j : ℤ) : ℝ)
        = (∑ j, A i j * ((x j:ℕ):ℝ)) - (∑ j, A i j * ((x' j:ℕ):ℝ)) := by
      have hpt : ∀ j, A i j * ((d j : ℤ) : ℝ)
          = A i j * ((x j:ℕ):ℝ) - A i j * ((x' j:ℕ):ℝ) :=
        fun j => by rw [hcast j, mul_sub]
      rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_sub_distrib]
    rw [hsum]
    have := abs_sub_lt_one_of_floor_eq (hfloor i)
    linarith

end Work.WilkiesH.NT
