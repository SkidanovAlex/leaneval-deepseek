import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.SumDefs
import Submission.Work.HP.NA.card_primMod
import Submission.Work.HP.NA.gcd_natAbs_pow_telescope
import Submission.Work.HP.NA.card_dvd_gcdMinors2_le
import Submission.Work.HP.NA.arith_bound

/-!
# The second-moment gcd sum `∑_{b₁,b₂ ∈ Bprim} gcd(𝒢(b₁,b₂), p^r)`

For a prime `p` and `r ≥ 1` we bound the double sum, over pairs of primitive vectors
`b₁, b₂ ∈ (ZMod (p^r))^{n+1}`, of `gcd(𝒢(irep b₁, irep b₂), p^r)`, where `𝒢` is the gcd of the
`2×2` minors of the two integer representatives.

The proof expands `gcd(g, p^r)` as the telescoping sum
`1 + ∑_{e=1}^{r} (p^e - p^{e-1})·[p^e ∣ g]`
(`Work.HP.NA.gcd_natAbs_pow_telescope`), counts, for each `b₁`, the number of `b₂` with
`p^e ∣ 𝒢(irep b₁, irep b₂)` by the line bound `Work.HP.NA.card_dvd_gcdMinors2_le`, and finishes
with the geometric estimate `Work.HP.NA.arith_bound`.
-/

noncomputable section
open Finset
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.HP.NA

/-- A primitive vector in `(ZMod (p^r))^{n+1}` has a coordinate whose integer representative is
not divisible by `p`. -/
private theorem irep_coord_not_dvd_of_mem_Bprim {n p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    [NeZero (p ^ r)] {b : Fin (n + 1) → ZMod (p ^ r)} (hb : b ∈ Work.HP.NA.Bprim n (p ^ r)) :
    ∃ i, ¬ (p : ℤ) ∣ Work.HP.NA.irep b i := by
  classical
  have hb' : IsPrimGen (p ^ r) b := mem_Bprim.mp hb
  obtain ⟨i, hi⟩ := (isPrimMod_iff_exists_isUnit p r (n + 1) hp hr b).mp hb'
  refine ⟨i, ?_⟩
  simp only [irep_apply]
  have hnotdvd : ¬ p ∣ (b i).val := by
    have h' : IsUnit (((b i).val : ℕ) : ZMod (p ^ r)) := by rwa [ZMod.natCast_zmod_val]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mp h'
  intro hdvd
  exact hnotdvd (by exact_mod_cast hdvd)

/-- `(s.filter q).card` is bounded by the cardinality of the subtype of elements satisfying `q`. -/
private theorem filter_card_le_natCard_gcd {α : Type*} [Fintype α] (s : Finset α) (q : α → Prop)
    [DecidablePred q] : (s.filter q).card ≤ Nat.card {x // q x} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.card_le_card (fun x hx => by
    rw [Finset.mem_filter] at hx ⊢; exact ⟨Finset.mem_univ _, hx.2⟩)

theorem sum_gcd_int_le (n p r : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hr : 1 ≤ r) [NeZero (p ^ r)] :
    (∑ b1 ∈ Work.HP.NA.Bprim n (p ^ r), ∑ b2 ∈ Work.HP.NA.Bprim n (p ^ r),
      (Nat.gcd ((Work.HP.gcdMinors2 (Work.HP.NA.irep b1) (Work.HP.NA.irep b2)).natAbs) (p ^ r) : ℝ))
      ≤ (p : ℝ) ^ (2 * (r * (n + 1))) * (1 + 4 / (p : ℝ) ^ (n - 1)) := by
  classical
  set B : Finset (Fin (n + 1) → ZMod (p ^ r)) := Bprim n (p ^ r) with hB
  set I : Finset ℕ := Finset.Ico 1 (r + 1) with hI
  set A : ℝ := (p : ℝ) ^ (r * (n + 1)) with hA
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hAPos : (0 : ℝ) < A := by rw [hA]; positivity
  have hANonneg : (0 : ℝ) ≤ A * (4 / (p : ℝ) ^ (n - 1)) := by positivity
  -- termwise telescoping identity for `gcd(·, p^r)`
  have hterm : ∀ b1 b2 : Fin (n + 1) → ZMod (p ^ r),
      (Nat.gcd (gcdMinors2 (irep b1) (irep b2)).natAbs (p ^ r) : ℝ)
        = 1 + ∑ e ∈ I, ((p ^ e - p ^ (e - 1) : ℕ) : ℝ) *
            (if (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2) then (1 : ℝ) else 0) := by
    intro b1 b2
    rw [hI, gcd_natAbs_pow_telescope p r hp]
    push_cast
    rfl
  -- `#B ≤ A`
  have hBcard : (B.card : ℝ) ≤ A := by
    have h1 : B.card ≤ (p ^ r) ^ (n + 1) := by
      calc B.card ≤ (Finset.univ : Finset (Fin (n + 1) → ZMod (p ^ r))).card :=
            Finset.card_le_card (Finset.subset_univ B)
        _ = (p ^ r) ^ (n + 1) := by
            rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_zmod,
              Nat.card_fin]
    rw [hA]
    calc (B.card : ℝ) ≤ ((p ^ r) ^ (n + 1) : ℕ) := by exact_mod_cast h1
      _ = (p : ℝ) ^ (r * (n + 1)) := by push_cast; rw [← pow_mul]
  -- per-`e` bound on the pairs with `p^e ∣ 𝒢`
  have hSe : ∀ e ∈ I,
      (∑ b1 ∈ B, ∑ b2 ∈ B, (if (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2)
          then (1 : ℝ) else 0))
        ≤ (B.card : ℝ) * ((p ^ e * p ^ ((r - e) * (n + 1)) : ℕ) : ℝ) := by
    intro e he
    have heI : e ≤ r := by rw [hI] at he; simp only [Finset.mem_Ico] at he; omega
    have hinner : ∀ b1 ∈ B,
        (∑ b2 ∈ B, (if (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2) then (1 : ℝ) else 0))
          ≤ ((p ^ e * p ^ ((r - e) * (n + 1)) : ℕ) : ℝ) := by
      intro b1 hb1
      rw [Finset.sum_boole]
      have hb1' : ∃ i, ¬ (p : ℤ) ∣ Work.HP.NA.irep b1 i :=
        irep_coord_not_dvd_of_mem_Bprim hp hr (by simpa [hB] using hb1)
      have hcnt := card_dvd_gcdMinors2_le hp heI (irep b1) hb1'
      have hle : (B.filter (fun b2 => (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2))).card
          ≤ p ^ e * p ^ ((r - e) * (n + 1)) :=
        le_trans (filter_card_le_natCard_gcd B _) hcnt
      exact_mod_cast hle
    calc (∑ b1 ∈ B, ∑ b2 ∈ B, (if (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2)
            then (1 : ℝ) else 0))
        ≤ ∑ b1 ∈ B, ((p ^ e * p ^ ((r - e) * (n + 1)) : ℕ) : ℝ) := Finset.sum_le_sum hinner
      _ = (B.card : ℝ) * ((p ^ e * p ^ ((r - e) * (n + 1)) : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- split the double sum into `#B²` plus the telescoping corrections
  have h1 : (∑ _b1 ∈ B, ∑ _b2 ∈ B, (1 : ℝ)) = (B.card : ℝ) * (B.card : ℝ) := by
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    ring
  have h2 : (∑ b1 ∈ B, ∑ b2 ∈ B, ∑ e ∈ I, ((p ^ e - p ^ (e - 1) : ℕ) : ℝ)
            * (if (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2) then (1 : ℝ) else 0))
      = ∑ e ∈ I, ((p ^ e - p ^ (e - 1) : ℕ) : ℝ)
          * (∑ b1 ∈ B, ∑ b2 ∈ B, (if (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2)
              then (1 : ℝ) else 0)) := by
    have s1 : (∑ b1 ∈ B, ∑ b2 ∈ B, ∑ e ∈ I, ((p ^ e - p ^ (e - 1) : ℕ) : ℝ)
            * (if (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2) then (1 : ℝ) else 0))
        = ∑ b1 ∈ B, ∑ e ∈ I, ∑ b2 ∈ B, ((p ^ e - p ^ (e - 1) : ℕ) : ℝ)
            * (if (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2) then (1 : ℝ) else 0) :=
      Finset.sum_congr rfl (fun b1 _ => Finset.sum_comm)
    have s2 : (∑ b1 ∈ B, ∑ e ∈ I, ∑ b2 ∈ B, ((p ^ e - p ^ (e - 1) : ℕ) : ℝ)
            * (if (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2) then (1 : ℝ) else 0))
        = ∑ e ∈ I, ∑ b1 ∈ B, ∑ b2 ∈ B, ((p ^ e - p ^ (e - 1) : ℕ) : ℝ)
            * (if (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2) then (1 : ℝ) else 0) :=
      Finset.sum_comm
    rw [s1, s2]
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b1 _
    rw [Finset.mul_sum]
  have hdecomp : (∑ b1 ∈ B, ∑ b2 ∈ B,
        (Nat.gcd (gcdMinors2 (irep b1) (irep b2)).natAbs (p ^ r) : ℝ))
      = (B.card : ℝ) * (B.card : ℝ)
        + ∑ e ∈ I, ((p ^ e - p ^ (e - 1) : ℕ) : ℝ)
            * (∑ b1 ∈ B, ∑ b2 ∈ B, (if (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2)
                then (1 : ℝ) else 0)) := by
    rw [Finset.sum_congr rfl (fun b1 _ => Finset.sum_congr rfl (fun b2 _ => hterm b1 b2))]
    simp only [Finset.sum_add_distrib]
    rw [h1, h2]
  -- bound the correction term
  have hmainBound : (∑ b1 ∈ B, ∑ b2 ∈ B,
        (Nat.gcd (gcdMinors2 (irep b1) (irep b2)).natAbs (p ^ r) : ℝ))
      ≤ (B.card : ℝ) * (B.card : ℝ)
        + (B.card : ℝ) * (A * (4 / (p : ℝ) ^ (n - 1))) := by
    rw [hdecomp]
    refine add_le_add (le_refl _) ?_
    have hSumE : (∑ e ∈ I, ((p ^ e - p ^ (e - 1) : ℕ) : ℝ)
          * ((p ^ e * p ^ ((r - e) * (n + 1)) : ℕ) : ℝ)) ≤ A * (4 / (p : ℝ) ^ (n - 1)) := by
      rw [hI, hA]; exact arith_bound p r n hp hn hr
    calc (∑ e ∈ I, ((p ^ e - p ^ (e - 1) : ℕ) : ℝ)
            * (∑ b1 ∈ B, ∑ b2 ∈ B, (if (p : ℤ) ^ e ∣ gcdMinors2 (irep b1) (irep b2)
                then (1 : ℝ) else 0)))
        ≤ ∑ e ∈ I, ((p ^ e - p ^ (e - 1) : ℕ) : ℝ)
            * ((B.card : ℝ) * ((p ^ e * p ^ ((r - e) * (n + 1)) : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum; intro e he
          exact mul_le_mul_of_nonneg_left (hSe e he) (by positivity)
      _ = (B.card : ℝ) * (∑ e ∈ I, ((p ^ e - p ^ (e - 1) : ℕ) : ℝ)
            * ((p ^ e * p ^ ((r - e) * (n + 1)) : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _; ring
      _ ≤ (B.card : ℝ) * (A * (4 / (p : ℝ) ^ (n - 1))) :=
          mul_le_mul_of_nonneg_left hSumE (by positivity)
  -- final arithmetic
  have hkey : A * A + A * (A * (4 / (p : ℝ) ^ (n - 1)))
      = (A * A) * (1 + 4 / (p : ℝ) ^ (n - 1)) := by ring
  have hA2 : A * A = (p : ℝ) ^ (2 * (r * (n + 1))) := by
    rw [hA, ← pow_add]; congr 1; ring
  calc (∑ b1 ∈ B, ∑ b2 ∈ B, (Nat.gcd (gcdMinors2 (irep b1) (irep b2)).natAbs (p ^ r) : ℝ))
      ≤ (B.card : ℝ) * (B.card : ℝ)
          + (B.card : ℝ) * (A * (4 / (p : ℝ) ^ (n - 1))) := hmainBound
    _ ≤ A * A + A * (A * (4 / (p : ℝ) ^ (n - 1))) := by
        apply add_le_add
        · exact mul_le_mul hBcard hBcard (by positivity) (le_of_lt hAPos)
        · exact mul_le_mul_of_nonneg_right hBcard hANonneg
    _ = (p : ℝ) ^ (2 * (r * (n + 1))) * (1 + 4 / (p : ℝ) ^ (n - 1)) := by
        rw [hkey, hA2]

end Work.HP.NA
