import Mathlib
import Submission.Work.Peluse.Basic

/-!
# `progAvgSum_eq_l1`

The progression average `E_{y ∈ [N']} f (x + qy) = (1/N') ∑_{m ∈ [N']} f (x + qm)` of a function
supported in `[-Ns, Ns]`, with a step `q` **larger than the diameter `2 Ns` of the support**.

The `N'` points `x + q·1, …, x + q·N'` are pairwise separated by at least `q > 2 Ns`, while two
points of the support `[-Ns, Ns]` are at distance at most `2 Ns`; hence **at most one** of them lies
in the support.  Consequently the average at every `x` is `1/N'` times a single value of `f`, and
summing over `x` counts each support point exactly `N'` times:

`∑_x ‖E_{y ∈ [N']} f (x + qy)‖ = ∑_x ‖f x‖`.

This is the "`ℓ¹`-collapse" of the progression average at a step exceeding the support range.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- Membership in the symmetric interval `symIcc L = [-L,L]` in terms of `Int.natAbs`. -/
lemma progAvgSum_mem_symIcc_iff_natAbs {L : ℕ} {x : ℤ} : x ∈ symIcc L ↔ x.natAbs ≤ L := by
  rw [symIcc, Finset.mem_Icc]
  constructor
  · intro h
    have h1 : |x| ≤ (L : ℤ) := abs_le.mpr h
    rw [← Int.natCast_natAbs] at h1
    exact_mod_cast h1
  · intro hx
    have h1 : (x.natAbs : ℤ) ≤ (L : ℤ) := by exact_mod_cast hx
    rw [Int.natCast_natAbs] at h1
    exact abs_le.mp h1

/-- If `f` is supported in `[-Ns,Ns]` and `f x ≠ 0` then `x.natAbs ≤ Ns`. -/
lemma progAvgSum_natAbs_le_of_supportIn {Ns : ℕ} {f : ℤ → ℂ} (hs : SupportIn f Ns) {x : ℤ}
    (hx : f x ≠ 0) : x.natAbs ≤ Ns := by
  by_contra h
  exact hx (hs x (not_le.mp h))

/-- `x ∉ symIcc Ns` implies `Ns < x.natAbs`. -/
lemma progAvgSum_natAbs_lt_of_not_mem {Ns : ℕ} {x : ℤ} (hx : x ∉ symIcc Ns) :
    Ns < x.natAbs := by
  by_contra h
  exact hx (progAvgSum_mem_symIcc_iff_natAbs.mpr (not_lt.mp h))

/-- **Sparsity of the progression window.**  If `f` is supported in `[-Ns,Ns]` and `q > 2 Ns`, then
for every `x` at most one `m ∈ [N']` has `f (x + q m) ≠ 0`. -/
lemma progAvgSum_card_filter_le_one {Ns N' : ℕ} {q : ℤ} (f : ℤ → ℂ) (hs : SupportIn f Ns)
    (hq : 2 * (Ns : ℤ) < q) (x : ℤ) :
    ((Finset.Icc (1:ℕ) N').filter (fun m : ℕ => f (x + q * (m : ℤ)) ≠ 0)).card ≤ 1 := by
  have hqpos : 0 < q := lt_of_le_of_lt (by positivity) hq
  have hqnat : 2 * Ns < q.natAbs := by
    have h1 : (2 * Ns : ℤ) < (q.natAbs : ℤ) := by
      rw [Int.natAbs_of_nonneg (le_of_lt hqpos)]
      exact_mod_cast hq
    exact_mod_cast h1
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  simp only [Finset.mem_filter] at ha hb
  by_contra hab
  have hna : (x + q * (a:ℤ)).natAbs ≤ Ns := progAvgSum_natAbs_le_of_supportIn hs ha.2
  have hnb : (x + q * (b:ℤ)).natAbs ≤ Ns := progAvgSum_natAbs_le_of_supportIn hs hb.2
  have hdiff : ((x + q * (a:ℤ)) - (x + q * (b:ℤ))).natAbs ≤ 2 * Ns := by
    have h := Int.natAbs_sub_le (x + q * (a:ℤ)) (x + q * (b:ℤ))
    omega
  have heq : (x + q * (a:ℤ)) - (x + q * (b:ℤ)) = q * ((a:ℤ) - (b:ℤ)) := by ring
  rw [heq, Int.natAbs_mul] at hdiff
  have hab0 : ((a:ℤ) - (b:ℤ)) ≠ 0 := by
    intro h
    exact hab (by exact_mod_cast (sub_eq_zero.mp h : (a:ℤ) = (b:ℤ)))
  have hone : 1 ≤ ((a:ℤ) - (b:ℤ)).natAbs := by
    have h : 0 < ((a:ℤ) - (b:ℤ)).natAbs := Int.natAbs_pos.mpr hab0
    omega
  have hge : 2 * Ns < q.natAbs * ((a:ℤ) - (b:ℤ)).natAbs := by
    calc 2 * Ns < q.natAbs := hqnat
      _ = q.natAbs * 1 := (mul_one _).symm
      _ ≤ q.natAbs * ((a:ℤ) - (b:ℤ)).natAbs := Nat.mul_le_mul_left _ hone
  omega

/-- The norm of a sum over a `Finset` of cardinality at most one is the sum of the norms. -/
lemma progAvgSum_norm_sum_eq_sum_norm_of_card_le_one {ι : Type*} (s : Finset ι)
    (h : s.card ≤ 1) (z : ι → ℂ) : ‖∑ i ∈ s, z i‖ = ∑ i ∈ s, ‖z i‖ := by
  classical
  rcases Finset.eq_empty_or_nonempty s with hs | ⟨a, ha⟩
  · rw [hs]; simp
  · have hsing : s = {a} := by
      ext b
      constructor
      · intro hb
        exact Finset.mem_singleton.mpr (Finset.card_le_one_iff.mp h hb ha)
      · intro hb
        exact Finset.mem_singleton.mp hb ▸ ha
    rw [hsing]; simp

/-- **The average collapses to a single term.**  If `f` is supported in `[-Ns,Ns]` and `q > 2 Ns`,
then for every `x` the modulus of the progression average equals `1/N'` times the sum of the moduli
of the `N'` (at most one nonzero) values `f (x + q m)`. -/
lemma progAvgSum_norm_progAvg_eq {Ns N' : ℕ} {q : ℤ} (f : ℤ → ℂ) (hs : SupportIn f Ns)
    (hq : 2 * (Ns : ℤ) < q) (x : ℤ) :
    ‖progAvg N' q f x‖
      = (N' : ℝ)⁻¹ * ∑ m ∈ Finset.Icc (1:ℕ) N', ‖f (x + q * (m : ℤ))‖ := by
  let A : Finset ℕ := (Finset.Icc (1:ℕ) N').filter (fun m : ℕ => f (x + q * (m : ℤ)) ≠ 0)
  have hcardA : A.card ≤ 1 := progAvgSum_card_filter_le_one f hs hq x
  have hzero : ∀ m ∈ Finset.Icc (1:ℕ) N', m ∉ A → f (x + q * (m:ℤ)) = 0 := by
    intro m hmT hmA
    by_contra hne
    exact hmA (Finset.mem_filter.mpr ⟨hmT, hne⟩)
  have hsumA : ∑ m ∈ A, f (x + q * (m:ℤ))
      = ∑ m ∈ Finset.Icc (1:ℕ) N', f (x + q * (m:ℤ)) :=
    Finset.sum_subset (Finset.filter_subset _ _) hzero
  have hnormA : ∑ m ∈ A, ‖f (x + q * (m:ℤ))‖
      = ∑ m ∈ Finset.Icc (1:ℕ) N', ‖f (x + q * (m:ℤ))‖ :=
    Finset.sum_subset (Finset.filter_subset _ _) (fun m hmT hmA => by
      rw [hzero m hmT hmA, norm_zero])
  have hsingle : ‖∑ m ∈ A, f (x + q * (m:ℤ))‖ = ∑ m ∈ A, ‖f (x + q * (m:ℤ))‖ :=
    progAvgSum_norm_sum_eq_sum_norm_of_card_le_one A hcardA _
  rw [progAvg, norm_mul, norm_inv, Complex.norm_natCast, ← hsumA, hsingle, hnormA]

theorem progAvgSum_eq_l1 {Ns N' : ℕ} {q : ℤ} (f : ℤ → ℂ) (hs : Work.Peluse.SupportIn f Ns)
    (hN' : 1 ≤ N') (hq : 2 * (Ns : ℤ) < q) :
    Work.Peluse.progAvgSum N' q f = ∑' x : ℤ, ‖f x‖ := by
  have hsumf : Summable (fun y : ℤ => ‖f y‖) := by
    refine summable_of_ne_finset_zero (s := symIcc Ns) (fun b hb => ?_)
    rw [norm_eq_zero]
    exact hs b (progAvgSum_natAbs_lt_of_not_mem hb)
  have hsumm_shift : ∀ c : ℤ, Summable (fun x : ℤ => ‖f (x + c)‖) := fun c => by
    refine summable_of_ne_finset_zero (s := symIcc (Ns + c.natAbs)) (fun b hb => ?_)
    rw [norm_eq_zero]
    by_contra hne
    have h1 : (b + c).natAbs ≤ Ns := progAvgSum_natAbs_le_of_supportIn hs hne
    have h2 : b.natAbs ≤ Ns + c.natAbs := by
      have h := Int.natAbs_sub_le (b + c) c
      rw [add_sub_cancel_right] at h
      omega
    exact absurd h2 (not_le.mpr (progAvgSum_natAbs_lt_of_not_mem hb))
  have htrans : ∀ c : ℤ, (∑' x : ℤ, ‖f (x + c)‖) = ∑' y : ℤ, ‖f y‖ := fun c =>
    by simpa [Equiv.coe_addRight] using
      Equiv.tsum_eq (Equiv.addRight c) (fun y : ℤ => ‖f y‖)
  have hcardT : (Finset.Icc (1:ℕ) N').card = N' := by
    rw [Nat.card_Icc]; omega
  have hN'ne : (N' : ℝ) ≠ 0 := by
    have : (0:ℝ) < (N' : ℝ) := by exact_mod_cast (by omega : 0 < N')
    exact ne_of_gt this
  rw [progAvgSum]
  calc ∑' x : ℤ, ‖progAvg N' q f x‖
      = ∑' x : ℤ, ((N' : ℝ)⁻¹ * ∑ m ∈ Finset.Icc (1:ℕ) N', ‖f (x + q * (m : ℤ))‖) :=
        tsum_congr (fun x => progAvgSum_norm_progAvg_eq f hs hq x)
    _ = (N' : ℝ)⁻¹ * ∑' x : ℤ, ∑ m ∈ Finset.Icc (1:ℕ) N', ‖f (x + q * (m : ℤ))‖ :=
        tsum_mul_left
    _ = (N' : ℝ)⁻¹ * ∑ m ∈ Finset.Icc (1:ℕ) N', ∑' x : ℤ, ‖f (x + q * (m : ℤ))‖ := by
        congr 1
        exact Summable.tsum_finsetSum
          (f := fun (m : ℕ) (x : ℤ) => ‖f (x + q * (m : ℤ))‖)
          (s := Finset.Icc (1:ℕ) N') (fun (m : ℕ) _ => hsumm_shift (q * (m : ℤ)))
    _ = (N' : ℝ)⁻¹ * ∑ m ∈ Finset.Icc (1:ℕ) N', (∑' y : ℤ, ‖f y‖) := by
        simp only [htrans]
    _ = (N' : ℝ)⁻¹ * ((N' : ℝ) * ∑' y : ℤ, ‖f y‖) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardT]
    _ = ∑' y : ℤ, ‖f y‖ := by
        rw [← mul_assoc, inv_mul_cancel₀ hN'ne, one_mul]

end

end Work.Peluse.Ulower
