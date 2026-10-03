/-
# The dense/sparse comparison of Peluse's level-two box norm

For `c ≠ 0`, `D, N ≥ 1` and `f` supported in `[-N,N]`, the level-two box-norm power with the
*dense* interval direction set `[1, |c| D]` is at most four times the level-two box-norm power
with the *sparse* direction set `c[D] = {c, 2c, …, Dc}`:

`(1/4) ‖f‖^{4}_{□²_{[1,|c|D]}([-N,N])} ≤ ‖f‖^{4}_{□²_{c[D]}([-N,N])}`.

This is the comparison (P10) of `NOTES_degree_lowering_SESSION2.md`: the box-norm arguments of
`PeluseU2Inverse` / `Lemma 7.4` use interval direction sets, while `PeluseULowering` uses the
arithmetic progression `c[D]` with `c = P.leadingCoeff`, which may be negative.

## The proof

The level-two box-norm power is `|S|⁻¹ |Q|⁻⁴ P(Q,Q)` with the *pair sum*
`P(A,C) = ∑_{a,b ∈ A} ∑_x ‖∑_{k ∈ C} f (x + a + k) · conj (f (x + b + k))‖²`
(`Work.Peluse.Ulower.pairSum` and `boxNormPow_two_eq_pairSum`).  Three structural facts of the
pair sum are used:

* `pairSum_swap` — the reordering `P(A,C) = P(C,A)`, which moves the direction set between the
  inner and the outer role (a colleague's lemma, `Peluse/Ulower/pairSum_swap`);
* `pairSum_shift` — translating both direction sets by `t` changes nothing (the change of
  variables `x ↦ x + 2t` of the unconditional sum over `ℤ`);
* the Cauchy–Schwarz bound `pairSum_inner_le`: writing `m := |c|`, the interval `[1, mD]` is the
  *disjoint* union of the `m` translates `m[D] + (j + 1 - m)`, `j < m`, so for every `A`

  `pairSum f A [1, mD] ≤ m² · pairSum f A m[D]`

  (Cauchy–Schwarz `‖∑_j z_j‖² ≤ m ∑_j ‖z_j‖²` over the decomposition).

Iterating: `P(Q,Q) ≤ m² P(Q,m[D]) = m² P(m[D],Q) ≤ m⁴ P(m[D],m[D])` with `Q = [1,mD]`; dividing by
`|Q|⁴ = (mD)⁴` gives the sparse bound exactly (`m⁴` cancels `m^{-4}`).

The negative case `c < 0` is reduced to the positive one by the reflection identity
`‖f‖_{□²_{-c[D]}} = ‖f (-·)‖_{□²_{c[D]}}` (`boxNormPow_two_reflect`), together with the
invariance `‖f (-·)‖_{□²_{[1,L]}} = ‖f‖_{□²_{[1,L]}}` of the *interval* direction set — the latter
following from the translate `[1,L] - (L+1) = [-L,-1]` and the translation invariance
`boxNormPow_two_shift` of the direction set.

## Main result

* `Work.Peluse.Ulower.dense_le_apBoxNorm`
-/
import Mathlib
import Submission.Work.Peluse.Ulower.iterDefs
import Submission.Work.Peluse.BoxNormDilation.dilated_directions_ge
import Submission.Work.Peluse.Ulower.boxSumPow_neg
import Submission.Work.Peluse.Ulower.sum_arithIcc_one_eq
import Submission.Work.Peluse.Ulower.pairSum_swap

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## The inner sum of the pair sum and its square -/

/-- The inner sum `∑_{k ∈ C} f (y + a + k) · conj (f (y + b + k))` of the pair sum. -/
def innerF (f : ℤ → ℂ) (C : Finset ℤ) (a b y : ℤ) : ℂ :=
  ∑ k ∈ C, f (y + a + k) * star (f (y + b + k))

/-- The squared modulus of `innerF`, i.e. the summand of the pair sum. -/
def innerSq (f : ℤ → ℂ) (C : Finset ℤ) (a b y : ℤ) : ℝ := ‖innerF f C a b y‖ ^ 2

lemma pairSum_eq_sum (f : ℤ → ℂ) (A C : Finset ℤ) :
    pairSum f A C = ∑ a ∈ A, ∑ b ∈ A, ∑' y : ℤ, innerSq f C a b y := rfl

/-! ## Elementary facts about `symIcc`, `arithIcc` -/

lemma denseSq_mem_symIcc {x : ℤ} {L : ℕ} : x ∈ symIcc L ↔ x.natAbs ≤ L := by
  rw [symIcc, Finset.mem_Icc]
  constructor
  · intro h
    have h' : |x| ≤ (L : ℤ) := abs_le.mpr h
    have h'' : ((x.natAbs : ℕ) : ℤ) ≤ (L : ℤ) := by
      rw [← Int.natCast_natAbs] at h'
      exact h'
    exact_mod_cast h''
  · intro h
    have h'' : ((x.natAbs : ℕ) : ℤ) ≤ (L : ℤ) := by exact_mod_cast h
    have h' : |x| ≤ (L : ℤ) := by
      rw [Int.natCast_natAbs] at h''
      exact h''
    exact abs_le.mp h'

lemma denseSq_notMem_symIcc {x : ℤ} {L : ℕ} : x ∉ symIcc L ↔ L < x.natAbs := by
  rw [denseSq_mem_symIcc]
  exact not_le

lemma natAbs_le_of_mem_arithIcc_one {D : ℕ} {k : ℤ} (hk : k ∈ arithIcc 1 D) :
    k.natAbs ≤ D := by
  rw [arithIcc, Finset.mem_image] at hk
  obtain ⟨n, hn, rfl⟩ := hk
  have h2 : ((1 : ℤ) * (n : ℤ)).natAbs = n := by
    rw [one_mul, Int.natAbs_natCast]
  rw [h2]
  exact (Finset.mem_Icc.mp hn).2

lemma natAbs_le_of_mem_arithIcc_mul {m D : ℕ} {k : ℤ} (hk : k ∈ arithIcc (m : ℤ) D) :
    k.natAbs ≤ m * D := by
  rw [arithIcc, Finset.mem_image] at hk
  obtain ⟨n, hn, rfl⟩ := hk
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_left m (Finset.mem_Icc.mp hn).2

lemma card_arithIcc_one_real (L : ℕ) : ((arithIcc 1 L).card : ℝ) = (L : ℝ) := by
  rw [arithIcc, Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    simpa using hab

lemma card_arithIcc_mul_real {m : ℕ} (hm : m ≠ 0) (D : ℕ) :
    ((arithIcc (m : ℤ) D).card : ℝ) = (D : ℝ) := by
  rw [arithIcc, Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    have h : (a : ℤ) = (b : ℤ) := by
      have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm
      exact mul_left_cancel₀ hmz hab
    exact_mod_cast h

/-! ## Vanishing of the inner sums away from a window -/

lemma innerF_eq_zero_of_lt {f : ℤ → ℂ} {N : ℕ} (hsupp : SupportIn f N)
    {C : Finset ℤ} {K : ℕ} (hC : ∀ k ∈ C, k.natAbs ≤ K) {a b : ℤ} {σ : ℕ}
    (ha : a.natAbs ≤ σ) {y : ℤ} (hy : N + σ + K < y.natAbs) : innerF f C a b y = 0 := by
  rw [innerF]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hN : N < (y + a + k).natAbs := by
    have h1 : (y : ℤ).natAbs ≤ (y + a + k).natAbs + (a + k).natAbs := by
      have h := Int.natAbs_add_le (y + a + k) (-(a + k))
      rwa [show y + a + k + -(a + k) = y by ring, Int.natAbs_neg] at h
    have h2 : (a + k).natAbs ≤ a.natAbs + k.natAbs := Int.natAbs_add_le a k
    have h3 := hC k hk
    omega
  rw [hsupp _ hN, zero_mul]

lemma innerSq_eq_zero_of_lt {f : ℤ → ℂ} {N : ℕ} (hsupp : SupportIn f N)
    {C : Finset ℤ} {K : ℕ} (hC : ∀ k ∈ C, k.natAbs ≤ K) {a b : ℤ} {σ : ℕ}
    (ha : a.natAbs ≤ σ) {y : ℤ} (hy : N + σ + K < y.natAbs) : innerSq f C a b y = 0 := by
  rw [innerSq, innerF_eq_zero_of_lt hsupp hC ha hy, norm_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- If `t.natAbs ≤ M` then `|x| ≤ |x + t| + M`. -/
lemma natAbs_le_natAbs_add {x t : ℤ} {M : ℕ} (ht : t.natAbs ≤ M) :
    x.natAbs ≤ (x + t).natAbs + M := by
  have h := Int.natAbs_add_le (x + t) (-t)
  rw [show x + t + -t = x by ring, Int.natAbs_neg] at h
  omega

/-! ## Reindexing lemmas -/

/-- Change of variables for an unconditional sum over `ℤ`. -/
lemma tsum_comp_add_int (c : ℤ) (g : ℤ → ℝ) : (∑' y : ℤ, g (y + c)) = ∑' y : ℤ, g y :=
  Equiv.tsum_eq (Equiv.addRight c) g

/-- The Cauchy–Schwarz inequality for a finite sum in `ℂ`. -/
lemma norm_sum_sq_le_card_mul {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ‖∑ i, z i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖z i‖ ^ 2 := by
  have h1 : ‖∑ i, z i‖ ≤ ∑ i, ‖z i‖ := norm_sum_le _ _
  have h2 : (∑ i, ‖z i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖z i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => ‖z i‖)
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2

/-! ## The inner sum under translations -/

lemma innerF_comp_add (c : ℤ) (C : Finset ℤ) (a b y : ℤ) (f : ℤ → ℂ) :
    innerF (fun x => f (x + c)) C a b y = innerF f C a b (y + c) := by
  rw [innerF, innerF]
  refine Finset.sum_congr rfl fun k hk => ?_
  show f (y + a + k + c) * star (f (y + b + k + c)) =
    f (y + c + a + k) * star (f (y + c + b + k))
  congr 1 <;> ring

lemma innerF_shift_directions (t : ℤ) (C : Finset ℤ) (a b y : ℤ) (f : ℤ → ℂ) :
    innerF f (C.image (fun x => x + t)) a b y = innerF f C a b (y + t) := by
  rw [innerF, innerF]
  rw [Finset.sum_image (fun a _ b _ h => by simpa using add_right_cancel h)]
  refine Finset.sum_congr rfl fun k hk => ?_
  show f (y + a + (k + t)) * star (f (y + b + (k + t))) =
    f (y + t + a + k) * star (f (y + t + b + k))
  congr 1 <;> ring

lemma innerF_shift_arg (t : ℤ) (C : Finset ℤ) (a b y : ℤ) (f : ℤ → ℂ) :
    innerF f C (a + t) (b + t) (y + t) = innerF f C a b (y + (t + t)) := by
  rw [innerF, innerF]
  refine Finset.sum_congr rfl fun k hk => ?_
  show f (y + t + (a + t) + k) * star (f (y + t + (b + t) + k)) =
    f (y + (t + t) + a + k) * star (f (y + (t + t) + b + k))
  congr 1 <;> ring

/-! ## Translating the direction sets of the pair sum -/

/-- Translating the argument of `f` does not change the pair sum. -/
lemma pairSum_comp_add (c : ℤ) (A C : Finset ℤ) (f : ℤ → ℂ) :
    pairSum (fun x => f (x + c)) A C = pairSum f A C := by
  rw [pairSum_eq_sum (fun x => f (x + c)) A C, pairSum_eq_sum f A C]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  have h1 : ∀ y : ℤ, innerSq (fun x => f (x + c)) C a b y = innerSq f C a b (y + c) := by
    intro y
    rw [innerSq, innerSq, innerF_comp_add]
  simp only [h1]
  exact tsum_comp_add_int c (fun y => innerSq f C a b y)

/-- Translating both direction sets of the pair sum by `t` does not change it. -/
lemma pairSum_shift (t : ℤ) (A C : Finset ℤ) (f : ℤ → ℂ) :
    pairSum f (A.image (fun x => x + t)) (C.image (fun x => x + t)) = pairSum f A C := by
  have hinjA : Set.InjOn (fun x : ℤ => x + t) (A : Set ℤ) :=
    fun a _ b _ h => by simpa using add_right_cancel h
  calc pairSum f (A.image (fun x => x + t)) (C.image (fun x => x + t))
      = ∑ a ∈ A, ∑ b ∈ A.image (fun x => x + t),
          ∑' y : ℤ, innerSq f (C.image (fun x => x + t)) (a + t) b y := by
        rw [pairSum_eq_sum f (A.image (fun x => x + t)) (C.image (fun x => x + t))]
        exact Finset.sum_image hinjA
    _ = ∑ a ∈ A, ∑ b ∈ A,
          ∑' y : ℤ, innerSq f (C.image (fun x => x + t)) (a + t) (b + t) y := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_image hinjA
    _ = ∑ a ∈ A, ∑ b ∈ A, ∑' y : ℤ, innerSq f C a b (y + (t + t)) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          tsum_congr fun y => ?_
        rw [innerSq, innerSq, innerF_shift_directions, innerF_shift_arg]
    _ = ∑ a ∈ A, ∑ b ∈ A, ∑' y : ℤ, innerSq f C a b y := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        exact tsum_comp_add_int (t + t) (fun y => innerSq f C a b y)
    _ = pairSum f A C := by
        rw [pairSum_eq_sum f A C]

/-- Translating both direction sets of the level-two box-norm power by `t` does not change it. -/
lemma boxNormPow_two_shift (t : ℤ) (Q S : Finset ℤ) {f : ℤ → ℂ} (hf : FinSuppZ f) :
    boxNormPow 2 (fun _ : Fin 2 => Q.image (fun x => x + t)) S f
      = boxNormPow 2 (fun _ : Fin 2 => Q) S f := by
  rw [boxNormPow_two_eq_pairSum hf, boxNormPow_two_eq_pairSum hf,
    Finset.card_image_of_injOn (fun a _ b _ h => by simpa using add_right_cancel h),
    pairSum_shift t Q Q f]

/-! ## Rearranging a triple sum with a constant factor -/

lemma sum_sum_sum_mul_sum {ι : Type*} [Fintype ι] (A W : Finset ℤ) (c : ℝ)
    (F : ℤ → ℤ → ℤ → ι → ℝ) :
    (∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ W, c * ∑ j : ι, F a b y j)
      = c * ∑ j : ι, ∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ W, F a b y j := by
  calc (∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ W, c * ∑ j : ι, F a b y j)
      = ∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ W, ∑ j : ι, c * F a b y j := by
        simp only [Finset.mul_sum]
    _ = ∑ a ∈ A, ∑ b ∈ A, ∑ j : ι, ∑ y ∈ W, c * F a b y j := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a ∈ A, ∑ j : ι, ∑ b ∈ A, ∑ y ∈ W, c * F a b y j := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ j : ι, ∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ W, c * F a b y j := Finset.sum_comm
    _ = c * ∑ j : ι, ∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ W, F a b y j := by
        simp only [Finset.mul_sum]

/-! ## The Cauchy–Schwarz bound for the pair sum -/

/-- The pair sum with the *dense* inner range `[1, mD]` is at most `m²` times the pair sum with
the *sparse* inner range `m[D]`: `[1, mD]` is the disjoint union of the `m` translates
`m[D] + (j + 1 - m)`, `j < m`, and each translate is handled by Cauchy–Schwarz. -/
lemma pairSum_inner_le {m D N : ℕ} {f : ℤ → ℂ} (hsupp : SupportIn f N) (A : Finset ℤ) :
    pairSum f A (arithIcc 1 (m * D)) ≤ (m : ℝ) ^ 2 * pairSum f A (arithIcc (m : ℤ) D) := by
  classical
  set σ : ℕ := ∑ a ∈ A, a.natAbs with hσ
  set R : ℕ := N + σ + m * D + m with hR
  have hAle : ∀ a ∈ A, a.natAbs ≤ σ := by
    intro a ha
    rw [hσ]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le _) ha
  have hCQ : ∀ k ∈ arithIcc 1 (m * D), k.natAbs ≤ m * D :=
    fun k hk => natAbs_le_of_mem_arithIcc_one hk
  have hCB : ∀ k ∈ arithIcc (m : ℤ) D, k.natAbs ≤ m * D :=
    fun k hk => natAbs_le_of_mem_arithIcc_mul hk
  -- (1) the summands vanish away from the window `symIcc R`
  have hvanQ : ∀ a ∈ A, ∀ b ∈ A, ∀ y : ℤ, y ∉ symIcc R →
      innerSq f (arithIcc 1 (m * D)) a b y = 0 := by
    intro a ha b hb y hy
    refine innerSq_eq_zero_of_lt hsupp hCQ (hAle a ha) ?_
    have hy' := denseSq_notMem_symIcc.mp hy
    rw [hR] at hy'
    omega
  have hvanB : ∀ a ∈ A, ∀ b ∈ A, ∀ y : ℤ, y ∉ symIcc R →
      innerSq f (arithIcc (m : ℤ) D) a b y = 0 := by
    intro a ha b hb y hy
    refine innerSq_eq_zero_of_lt hsupp hCB (hAle a ha) ?_
    have hy' := denseSq_notMem_symIcc.mp hy
    rw [hR] at hy'
    omega
  have hvanBj : ∀ j : Fin m, ∀ a ∈ A, ∀ b ∈ A, ∀ y : ℤ, y ∉ symIcc R →
      innerSq f (arithIcc (m : ℤ) D) a b (y + ((j : ℤ) + 1 - (m : ℤ))) = 0 := by
    intro j a ha b hb y hy
    refine innerSq_eq_zero_of_lt hsupp hCB (hAle a ha) ?_
    have hy' := denseSq_notMem_symIcc.mp hy
    rw [hR] at hy'
    have htj : (((j : ℤ) + 1 - (m : ℤ))).natAbs ≤ m := by
      have hjlt : (j : ℤ) < (m : ℤ) := by exact_mod_cast j.isLt
      have hj0 : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
      have h1 : -((m : ℤ)) ≤ (j : ℤ) + 1 - (m : ℤ) := by omega
      have h2 : (j : ℤ) + 1 - (m : ℤ) ≤ (m : ℤ) := by omega
      have h3 : |(j : ℤ) + 1 - (m : ℤ)| ≤ (m : ℤ) := abs_le.mpr ⟨h1, h2⟩
      have h3' : ((((j : ℤ) + 1 - (m : ℤ)).natAbs : ℕ) : ℤ) ≤ (m : ℤ) := by
        rwa [Int.natCast_natAbs]
      exact_mod_cast h3'
    have h4 := natAbs_le_natAbs_add (x := y) (t := (j : ℤ) + 1 - (m : ℤ)) htj
    omega
  -- (2) both sides as finite sums over the window
  have hleft : pairSum f A (arithIcc 1 (m * D))
      = ∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ symIcc R, innerSq f (arithIcc 1 (m * D)) a b y := by
    rw [pairSum_eq_sum]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    exact tsum_eq_sum (s := symIcc R) fun y hy => hvanQ a ha b hb y hy
  have hright : pairSum f A (arithIcc (m : ℤ) D)
      = ∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ symIcc R, innerSq f (arithIcc (m : ℤ) D) a b y := by
    rw [pairSum_eq_sum]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    exact tsum_eq_sum (s := symIcc R) fun y hy => hvanB a ha b hb y hy
  -- (3) Cauchy–Schwarz on the decomposition of the dense inner range
  have hCS : ∀ a ∈ A, ∀ b ∈ A, ∀ x : ℤ,
      innerSq f (arithIcc 1 (m * D)) a b x
        ≤ (m : ℝ) * ∑ j : Fin m,
            innerSq f (arithIcc (m : ℤ) D) a b (x + ((j : ℤ) + 1 - (m : ℤ))) := by
    intro a ha b hb x
    have hdecomp : innerF f (arithIcc 1 (m * D)) a b x
        = ∑ j : Fin m, innerF f (arithIcc (m : ℤ) D) a b
            (x + ((j : ℤ) + 1 - (m : ℤ))) := by
      rw [innerF, sum_arithIcc_one_eq m D (g := fun y => f (x + a + y) * star (f (x + b + y)))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [innerF]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1 <;> ring
    have hcs := norm_sum_sq_le_card_mul
      (z := fun j : Fin m => innerF f (arithIcc (m : ℤ) D) a b
        (x + ((j : ℤ) + 1 - (m : ℤ))))
    rw [Fintype.card_fin] at hcs
    simp only [innerSq]
    rw [hdecomp]
    exact hcs
  -- (4) translating the window does not change the sum
  have hshift : ∀ j : Fin m, ∀ a ∈ A, ∀ b ∈ A,
      (∑ y ∈ symIcc R, innerSq f (arithIcc (m : ℤ) D) a b
          (y + ((j : ℤ) + 1 - (m : ℤ))))
        = ∑ y ∈ symIcc R, innerSq f (arithIcc (m : ℤ) D) a b y := by
    intro j a ha b hb
    calc (∑ y ∈ symIcc R, innerSq f (arithIcc (m : ℤ) D) a b
            (y + ((j : ℤ) + 1 - (m : ℤ))))
        = ∑' y : ℤ, innerSq f (arithIcc (m : ℤ) D) a b
            (y + ((j : ℤ) + 1 - (m : ℤ))) :=
          (tsum_eq_sum (s := symIcc R) fun y hy => hvanBj j a ha b hb y hy).symm
      _ = ∑' y : ℤ, innerSq f (arithIcc (m : ℤ) D) a b y :=
          tsum_comp_add_int (((j : ℤ) + 1 - (m : ℤ)))
            (fun y => innerSq f (arithIcc (m : ℤ) D) a b y)
      _ = ∑ y ∈ symIcc R, innerSq f (arithIcc (m : ℤ) D) a b y :=
          tsum_eq_sum (s := symIcc R) fun y hy => hvanB a ha b hb y hy
  -- (5) assembly
  calc pairSum f A (arithIcc 1 (m * D))
      = ∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ symIcc R, innerSq f (arithIcc 1 (m * D)) a b y := hleft
    _ ≤ ∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ symIcc R, (m : ℝ) * ∑ j : Fin m,
          innerSq f (arithIcc (m : ℤ) D) a b (y + ((j : ℤ) + 1 - (m : ℤ))) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb =>
          Finset.sum_le_sum fun y _ => hCS a ha b hb y
    _ = (m : ℝ) * ∑ j : Fin m, ∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ symIcc R,
          innerSq f (arithIcc (m : ℤ) D) a b (y + ((j : ℤ) + 1 - (m : ℤ))) :=
        sum_sum_sum_mul_sum (ι := Fin m) A (symIcc R) (m : ℝ)
          (fun a b y j => innerSq f (arithIcc (m : ℤ) D) a b
            (y + ((j : ℤ) + 1 - (m : ℤ))))
    _ = (m : ℝ) * ∑ j : Fin m, ∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ symIcc R,
          innerSq f (arithIcc (m : ℤ) D) a b y := by
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        exact Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hshift j a ha b hb
    _ = (m : ℝ) * ((m : ℝ) * ∑ a ∈ A, ∑ b ∈ A, ∑ y ∈ symIcc R,
          innerSq f (arithIcc (m : ℤ) D) a b y) := by
        congr 1
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (m : ℝ) ^ 2 * pairSum f A (arithIcc (m : ℤ) D) := by
        rw [hright]; ring

/-! ## The box-norm comparison (positive dilation) -/

lemma dense_le_sparse_pos {m D N : ℕ} (hm : 0 < m) (hD : 1 ≤ D) {f : ℤ → ℂ}
    (hsupp : SupportIn f N) :
    (1/4 : ℝ) * boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 (m * D)) (symIcc N) f ≤
      boxNormPow 2 (fun _ : Fin 2 => arithIcc (m : ℤ) D) (symIcc N) f := by
  have hfin : FinSuppZ f := FinSuppZ.of_supportIn hsupp
  have hQ := pairSum_inner_le (m := m) (D := D) (N := N) hsupp (arithIcc 1 (m * D))
  have hB := pairSum_inner_le (m := m) (D := D) (N := N) hsupp (arithIcc (m : ℤ) D)
  have hswap := pairSum_swap hfin (arithIcc 1 (m * D)) (arithIcc (m : ℤ) D)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmid : pairSum f (arithIcc 1 (m * D)) (arithIcc (m : ℤ) D)
      ≤ (m : ℝ) ^ 2 * pairSum f (arithIcc (m : ℤ) D) (arithIcc (m : ℤ) D) := by
    rw [hswap]
    exact hB
  have hPP : pairSum f (arithIcc 1 (m * D)) (arithIcc 1 (m * D))
      ≤ (m : ℝ) ^ 4 * pairSum f (arithIcc (m : ℤ) D) (arithIcc (m : ℤ) D) := by
    calc pairSum f (arithIcc 1 (m * D)) (arithIcc 1 (m * D))
        ≤ (m : ℝ) ^ 2 * pairSum f (arithIcc 1 (m * D)) (arithIcc (m : ℤ) D) := hQ
      _ ≤ (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 * pairSum f (arithIcc (m : ℤ) D) (arithIcc (m : ℤ) D)) :=
          mul_le_mul_of_nonneg_left hmid (by positivity)
      _ = (m : ℝ) ^ 4 * pairSum f (arithIcc (m : ℤ) D) (arithIcc (m : ℤ) D) := by ring
  have hcardQ : ((arithIcc 1 (m * D)).card : ℝ) = (m : ℝ) * (D : ℝ) := by
    rw [card_arithIcc_one_real]
    push_cast
    ring
  have hcardB : ((arithIcc (m : ℤ) D).card : ℝ) = (D : ℝ) := card_arithIcc_mul_real hm.ne' D
  have hkey : ((arithIcc 1 (m * D)).card : ℝ)⁻¹ ^ 4 *
        pairSum f (arithIcc 1 (m * D)) (arithIcc 1 (m * D))
      ≤ ((arithIcc (m : ℤ) D).card : ℝ)⁻¹ ^ 4 *
        pairSum f (arithIcc (m : ℤ) D) (arithIcc (m : ℤ) D) := by
    have h1 : ((arithIcc 1 (m * D)).card : ℝ)⁻¹ ^ 4 *
          pairSum f (arithIcc 1 (m * D)) (arithIcc 1 (m * D))
        ≤ ((arithIcc 1 (m * D)).card : ℝ)⁻¹ ^ 4 *
          ((m : ℝ) ^ 4 * pairSum f (arithIcc (m : ℤ) D) (arithIcc (m : ℤ) D)) :=
      mul_le_mul_of_nonneg_left hPP (by positivity)
    have h2 : ((arithIcc 1 (m * D)).card : ℝ)⁻¹ ^ 4 *
          ((m : ℝ) ^ 4 * pairSum f (arithIcc (m : ℤ) D) (arithIcc (m : ℤ) D))
        = ((arithIcc (m : ℤ) D).card : ℝ)⁻¹ ^ 4 *
          pairSum f (arithIcc (m : ℤ) D) (arithIcc (m : ℤ) D) := by
      rw [hcardQ, hcardB]
      have key : (m : ℝ) ^ 4 * ((↑m * (D : ℝ))⁻¹) ^ 4 = ((D : ℝ)⁻¹) ^ 4 := by
        rw [← mul_pow]
        congr 1
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hm0, one_mul]
      calc ((↑m * (D : ℝ))⁻¹) ^ 4 *
            ((m : ℝ) ^ 4 * pairSum f (arithIcc (m : ℤ) D) (arithIcc (m : ℤ) D))
          = (m ^ 4 * ((↑m * (D : ℝ))⁻¹) ^ 4) *
              pairSum f (arithIcc (m : ℤ) D) (arithIcc (m : ℤ) D) := by ring
        _ = ((D : ℝ)⁻¹) ^ 4 *
              pairSum f (arithIcc (m : ℤ) D) (arithIcc (m : ℤ) D) := by rw [key]
    linarith [h1, h2.le]
  have hmain : boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 (m * D)) (symIcc N) f
      ≤ boxNormPow 2 (fun _ : Fin 2 => arithIcc (m : ℤ) D) (symIcc N) f := by
    rw [boxNormPow_two_eq_pairSum hfin, boxNormPow_two_eq_pairSum hfin, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left hkey (by
      rw [inv_nonneg]
      positivity)
  calc (1/4 : ℝ) * boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 (m * D)) (symIcc N) f
      ≤ boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 (m * D)) (symIcc N) f := by
        have h0 : (0 : ℝ) ≤ boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 (m * D)) (symIcc N) f :=
          norm_nonneg _
        linarith
    _ ≤ boxNormPow 2 (fun _ : Fin 2 => arithIcc (m : ℤ) D) (symIcc N) f := hmain

/-! ## Reflecting the direction set -/

lemma boxNormPow_two_reflect (c : ℤ) (D : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) :
    boxNormPow 2 (fun _ : Fin 2 => arithIcc c D) S f
      = boxNormPow 2 (fun _ : Fin 2 => arithIcc (-c) D) S (fun x => f (-x)) := by
  have h := boxSumPow_neg 2 (-c) D S f
  simp only [neg_neg] at h
  rw [boxNormPow, boxNormPow, h]

/-- The direction set `arithIcc (-1) L` is a translate of `arithIcc 1 L`. -/
lemma arithIcc_neg_one_eq_image (L : ℕ) :
    (arithIcc 1 L).image (fun x : ℤ => x + (-((L : ℤ) + 1))) = arithIcc (-1) L := by
  ext x
  simp only [arithIcc, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨a, ⟨n, ⟨hn1, hn2⟩, hna⟩, hax⟩
    rw [one_mul] at hna
    subst hna
    have hcast : (((L + 1 - n : ℕ)) : ℤ) = (L : ℤ) + 1 - (n : ℤ) := by omega
    refine ⟨L + 1 - n, ⟨by omega, by omega⟩, ?_⟩
    rw [hcast]
    omega
  · rintro ⟨m, ⟨hm1, hm2⟩, hmx⟩
    have hcast : (((L + 1 - m : ℕ)) : ℤ) = (L : ℤ) + 1 - (m : ℤ) := by omega
    refine ⟨(1 : ℤ) * (((L + 1 - m : ℕ)) : ℤ),
      ⟨L + 1 - m, ⟨by omega, by omega⟩, by rw [one_mul]⟩, ?_⟩
    rw [hcast, ← hmx]
    omega

/-- The level-two box norm with the interval direction set is invariant under the reflection
`f ↦ f (-·)`. -/
lemma boxNormPow_two_interval_reflect {L N : ℕ} {f : ℤ → ℂ} (hsupp : SupportIn f N) :
    boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 L) (symIcc N) (fun x => f (-x))
      = boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 L) (symIcc N) f := by
  have h1 : boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 L) (symIcc N) (fun x => f (-x))
      = boxNormPow 2 (fun _ : Fin 2 => arithIcc (-1) L) (symIcc N) f := by
    have h := boxNormPow_two_reflect 1 L (symIcc N) (fun x => f (-x))
    have h2 : (fun x : ℤ => (fun x : ℤ => f (-x)) (-x)) = f := by
      funext x
      simp
    rw [h2] at h
    exact h
  rw [h1, ← arithIcc_neg_one_eq_image]
  exact boxNormPow_two_shift (-((L : ℤ) + 1)) (arithIcc 1 L) (symIcc N)
    (FinSuppZ.of_supportIn hsupp)

/-! ## The target -/

theorem dense_le_apBoxNorm {c : ℤ} {D N : ℕ} (hc : c ≠ 0) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hcDN : (D : ℝ) * |(c : ℝ)| ≤ (N : ℝ)) {f : ℤ → ℂ}
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) (hsupp : Work.Peluse.SupportIn f N) :
    (1/4 : ℝ) * Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc 1 (c.natAbs * D)) (Work.Peluse.symIcc N) f ≤
      Work.Peluse.boxNormPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc c D) (Work.Peluse.symIcc N) f := by
  have hm : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  have hsupp' : SupportIn (fun x : ℤ => f (-x)) N := by
    intro x hx
    exact hsupp (-x) (by simpa [Int.natAbs_neg] using hx)
  rcases lt_or_gt_of_ne hc with hclt | hcgt
  · -- `c < 0`
    have hnegc : (-((c.natAbs : ℕ) : ℤ)) = c := by
      have h0 : (0 : ℤ) ≤ -c := by omega
      have h1 := Int.natCast_natAbs (-c)
      rw [abs_of_nonneg h0, Int.natAbs_neg] at h1
      omega
    have hinterval : boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 (c.natAbs * D)) (symIcc N)
        (fun x => f (-x))
          = boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 (c.natAbs * D)) (symIcc N) f :=
      boxNormPow_two_interval_reflect hsupp
    have hpos := dense_le_sparse_pos (m := c.natAbs) (D := D) (N := N) hm hD hsupp'
    have hnegsym : (-c : ℤ) = ((c.natAbs : ℕ) : ℤ) := by omega
    have hsparse : boxNormPow 2 (fun _ : Fin 2 => arithIcc ((c.natAbs : ℕ) : ℤ) D) (symIcc N)
        (fun x => f (-x))
          = boxNormPow 2 (fun _ : Fin 2 => arithIcc c D) (symIcc N) f := by
      have h := (boxNormPow_two_reflect c D (symIcc N) f).symm
      rw [hnegsym] at h
      exact h
    rw [hinterval, hsparse] at hpos
    exact hpos
  · -- `0 < c`
    have hcm : ((c.natAbs : ℕ) : ℤ) = c := by
      rw [Int.natAbs_of_nonneg hcgt.le]
    have h := dense_le_sparse_pos (m := c.natAbs) (D := D) (N := N) hm hD hsupp
    rw [hcm] at h
    exact h

end

end Work.Peluse.Ulower
