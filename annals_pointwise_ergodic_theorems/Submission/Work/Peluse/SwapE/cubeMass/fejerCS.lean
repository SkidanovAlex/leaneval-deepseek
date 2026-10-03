import Mathlib
import Submission.Work.Peluse.SwapE.cubeMass.Defs

/-!
# `fejerCS` — the Cauchy–Schwarz/Fejér cube-mass bound

For a function `g : ℤ → ℂ` supported in `[-N,N]` and an integer `Card ≥ 0`, the total mass of `g`
controls its Fejér slots `h(z) = ∑_{v=1}^{Card} g(z+v)`:

`Card²·‖∑_x g x‖² ≤ (#symIcc N + Card)·∑_z ‖∑_{v=1}^{Card} g (z+v)‖²`.

## The mathematics

Write `h z = ∑_{v ∈ [1,Card]} g (z+v)`.  Two elementary observations give the bound.

* *The slots sum to `Card` times the mass.*  Exchanging the order of summation and shifting the
  (finite) sum over `ℤ`,
  `∑_z h z = ∑_{v ∈ [1,Card]} ∑_z g (z+v) = ∑_{v ∈ [1,Card]} ∑_x g x = Card · ∑_x g x`.

* *`h` is supported in the window `[-N-Card, N]`, of cardinality `#symIcc N + Card`.*  If
  `h z ≠ 0` then `g(z+v) ≠ 0` for some `v ∈ [1,Card]`, hence `z+v ∈ [-N,N]`, which gives
  `-N-Card ≤ z ≤ N`.  The interval `[-N-Card, N]` has `2N+Card+1 = #symIcc N + Card` elements.

Cauchy–Schwarz on that window closes the argument:
`‖∑_z h z‖² ≤ #window · ∑_z ‖h z‖²` (the standard `‖∑_{z∈E} h z‖² ≤ #E · ∑_{z∈E}‖h z‖²`).

The bound is exactly sharp: it is the trivial bound obtained from the cardinality of the
difference window, with no cancellation assumed on `g`.
-/

open scoped BigOperators

namespace Work.Peluse.SwapE.cubeMass

noncomputable section

open Work.Peluse

/-- `1•[Card] = {1, …, Card}` as a set of integers (the direction set of the Fejér window). -/
private lemma arithIcc_one_eq_Icc (Card : ℕ) :
    arithIcc 1 Card = Finset.Icc (1 : ℤ) (Card : ℤ) := by
  ext v
  rw [arithIcc, Finset.mem_image]
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨n, ⟨h1, h2⟩, hv⟩
    constructor
    · have : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast h1
      omega
    · have : (n : ℤ) ≤ (Card : ℤ) := by exact_mod_cast h2
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨v.toNat, ⟨?_, ?_⟩, ?_⟩
    · rw [Int.le_toNat (by omega : (0 : ℤ) ≤ v)]
      simpa using h1
    · rw [Int.toNat_le]
      simpa using h2
    · simpa using (Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ v)).symm

/-- Membership in `symIcc N` from the size of the absolute value. -/
private lemma mem_symIcc_of_natAbs_le {N : ℕ} {z : ℤ} (h : z.natAbs ≤ N) :
    z ∈ symIcc N := by
  rw [symIcc, Finset.mem_Icc]
  have h2 : (((z.natAbs : ℕ)) : ℤ) ≤ (N : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at h2
  exact ⟨neg_le_of_abs_le h2, le_of_abs_le h2⟩

/-- Refutation form of the previous lemma. -/
private lemma natAbs_lt_of_notMem_symIcc {N : ℕ} {z : ℤ} (h : z ∉ symIcc N) :
    N < z.natAbs := by
  by_contra hc
  simp only [not_lt] at hc
  exact h (mem_symIcc_of_natAbs_le hc)

/-- Cauchy–Schwarz for the modulus of a finite sum of complex numbers, in the sharp `card` form:
`‖∑_{i∈s} f i‖² ≤ #s · ∑_{i∈s} ‖f i‖²`. -/
private lemma norm_sum_sq_le_card_mul (s : Finset ℤ) (f : ℤ → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
  have h2 : (∑ i ∈ s, ‖f i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : ℤ => (1 : ℝ)) (fun i => ‖f i‖)
    simpa using this
  have hnn : 0 ≤ ∑ i ∈ s, ‖f i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  calc ‖∑ i ∈ s, f i‖ ^ 2 = ‖∑ i ∈ s, f i‖ * ‖∑ i ∈ s, f i‖ := by ring
    _ ≤ (∑ i ∈ s, ‖f i‖) * (∑ i ∈ s, ‖f i‖) :=
        mul_le_mul h1 h1 (norm_nonneg _) hnn
    _ = (∑ i ∈ s, ‖f i‖) ^ 2 := by ring
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := h2

/-- **The Fejér/Cauchy–Schwarz cube-mass bound.**  For `g` supported in `[-N,N]`,
`Card²·‖∑_x g x‖² ≤ (#symIcc N + Card)·∑_z ‖∑_{v=1}^{Card} g (z+v)‖²`. -/
theorem fejerCS (Card : ℕ) (hC : 1 ≤ Card) {N : ℕ} {g : ℤ → ℂ}
    (hg : Work.Peluse.SupportIn g N) :
    (Card : ℝ) ^ 2 * ‖∑' x : ℤ, g x‖ ^ 2
      ≤ (((Work.Peluse.symIcc N).card : ℝ) + (Card : ℝ))
          * ∑' z : ℤ, ‖∑ v ∈ Work.Peluse.arithIcc 1 Card, g (z + v)‖ ^ 2 := by
  simp only [arithIcc_one_eq_Icc]
  set I : Finset ℤ := Finset.Icc (1 : ℤ) (Card : ℤ) with hI
  set E : Finset ℤ := Finset.Icc (-(N : ℤ) - (Card : ℤ)) (N : ℤ) with hE
  -- the slots are supported in the window `E`
  have hsupp : ∀ z ∉ E, (∑ v ∈ I, g (z + v)) = 0 := by
    intro z hz
    apply Finset.sum_eq_zero
    intro v hv
    by_contra hgv
    have hvI : v ∈ Finset.Icc (1 : ℤ) (Card : ℤ) := by rwa [hI] at hv
    rw [Finset.mem_Icc] at hvI
    obtain ⟨hv1, hv2⟩ := hvI
    have hmem : z + v ∈ symIcc N := by
      by_contra hc
      exact hgv (hg (z + v) (natAbs_lt_of_notMem_symIcc hc))
    rw [symIcc, Finset.mem_Icc] at hmem
    obtain ⟨hz1, hz2⟩ := hmem
    have hzE : ¬ ((-(N : ℤ) - (Card : ℤ)) ≤ z ∧ z ≤ (N : ℤ)) := by
      rw [hE, Finset.mem_Icc] at hz
      exact hz
    simp only [not_and_or, not_le] at hzE
    rcases hzE with hgt | hlt
    · omega
    · omega
  -- the total mass, as a finite sum over the support window
  have hA : (∑' x : ℤ, g x) = ∑ x ∈ symIcc N, g x := by
    refine tsum_eq_sum (fun x hx => hg x (natAbs_lt_of_notMem_symIcc hx))
  -- the slot energy, as a finite sum over the slot window
  have hB : (∑' z : ℤ, ‖∑ v ∈ I, g (z + v)‖ ^ 2)
      = ∑ z ∈ E, ‖∑ v ∈ I, g (z + v)‖ ^ 2 := by
    refine tsum_eq_sum (fun z hz => ?_)
    rw [hsupp z hz]
    simp
  -- each shifted window sum reproduces the total mass
  have hstep : ∀ v ∈ I, ∑ z ∈ E, g (z + v) = ∑ x ∈ symIcc N, g x := by
    intro v hv
    have hvI : v ∈ Finset.Icc (1 : ℤ) (Card : ℤ) := by rwa [hI] at hv
    rw [Finset.mem_Icc] at hvI
    obtain ⟨hv1, hv2⟩ := hvI
    have hsub : symIcc N ⊆ Finset.image (fun z : ℤ => z + v) E := by
      intro x hx
      rw [Finset.mem_image]
      refine ⟨x - v, ?_, by ring⟩
      rw [hE, Finset.mem_Icc]
      rw [symIcc, Finset.mem_Icc] at hx
      obtain ⟨hx1, hx2⟩ := hx
      omega
    have hvan : ∀ x ∈ Finset.image (fun z : ℤ => z + v) E, x ∉ symIcc N → g x = 0 :=
      fun x _ hx => hg x (natAbs_lt_of_notMem_symIcc hx)
    have h1 : (∑ x ∈ Finset.image (fun z : ℤ => z + v) E, g x) = ∑ z ∈ E, g (z + v) :=
      Finset.sum_image (s := E) (g := fun z : ℤ => z + v) (f := g)
        (fun a _ b _ hab => add_right_cancel hab)
    have h2 : (∑ x ∈ symIcc N, g x)
        = ∑ x ∈ Finset.image (fun z : ℤ => z + v) E, g x := Finset.sum_subset hsub hvan
    rw [h2, h1]
  have hcardI : I.card = Card := by
    rw [hI, Int.card_Icc]
    have h : (Card : ℤ) + 1 - 1 = ((Card : ℕ) : ℤ) := by ring
    rw [h, Int.toNat_natCast]
  -- the slots sum to `Card` times the mass
  have hsum : ∑ z ∈ E, ∑ v ∈ I, g (z + v) = (Card : ℂ) * ∑ x ∈ symIcc N, g x := by
    rw [Finset.sum_comm, Finset.sum_congr rfl hstep, Finset.sum_const, hcardI, nsmul_eq_mul]
  have hcs : ‖∑ z ∈ E, ∑ v ∈ I, g (z + v)‖ ^ 2
      ≤ (E.card : ℝ) * ∑ z ∈ E, ‖∑ v ∈ I, g (z + v)‖ ^ 2 :=
    norm_sum_sq_le_card_mul E _
  have hcardE : E.card = 2 * N + Card + 1 := by
    rw [hE, Int.card_Icc]
    have h : (N : ℤ) + 1 - (-(N : ℤ) - (Card : ℤ)) = ((2 * N + Card + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [h, Int.toNat_natCast]
  have hsymCard : (symIcc N).card = 2 * N + 1 := by
    rw [symIcc, Int.card_Icc]
    have h : (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]
  have hcard : (E.card : ℝ) ≤ ((symIcc N).card : ℝ) + (Card : ℝ) := by
    rw [hcardE, hsymCard]
    have h1 : ((2 * N + Card + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + (Card : ℝ) + 1 := by push_cast; ring
    have h2 : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
    rw [h1, h2]; linarith
  calc
    (Card : ℝ) ^ 2 * ‖∑' x : ℤ, g x‖ ^ 2
        = ‖(Card : ℂ) * (∑ x ∈ symIcc N, g x)‖ ^ 2 := by
            rw [hA, norm_mul, Complex.norm_natCast]; ring
      _ = ‖∑ z ∈ E, ∑ v ∈ I, g (z + v)‖ ^ 2 := by rw [hsum]
      _ ≤ (E.card : ℝ) * ∑ z ∈ E, ‖∑ v ∈ I, g (z + v)‖ ^ 2 := hcs
      _ = (E.card : ℝ) * ∑' z : ℤ, ‖∑ v ∈ I, g (z + v)‖ ^ 2 := by rw [hB]
      _ ≤ (((symIcc N).card : ℝ) + (Card : ℝ))
            * ∑' z : ℤ, ‖∑ v ∈ I, g (z + v)‖ ^ 2 := by
            rw [hB]
            exact mul_le_mul_of_nonneg_right hcard
              (Finset.sum_nonneg (fun z _ => by positivity))

end

end Work.Peluse.SwapE.cubeMass
