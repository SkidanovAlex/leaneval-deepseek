import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The "swap" step in the Cauchy–Schwarz reduction of the bilinear averages

For a finitely supported `f : ℤ → ℂ` and finitely many shifts `σ k`, the `ℓ²`-mass of the
shifted sum equals the double sum of the (shifted) autocorrelation:

`∑_x ‖∑_k f (x + σ k)‖² = ∑_k ∑_k' ∑_x f (x + σ k - σ k') · conj (f x)`.

This is the elementary "expand the square and swap the order of summation" identity, made
legitimate by the finite support of `f` (every `tsum` below is really a finite sum).

The proof: expand `‖z‖² = z · conj z`, interchange the (finite) sums over `k, k'` with the
`tsum` over `x` — which is a finite sum because `f` is finitely supported — and then reindex
`x ↦ x + σ k'` (a bijection of `ℤ`, so `tsum` is unchanged).
-/

namespace Work.Peluse.SwapCS0

open scoped BigOperators

/-- A real norm-square, as a complex number, is `z * conj z`. -/
private lemma ofReal_normSq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  simp [Complex.sq_norm, Complex.mul_conj]

/-- Membership in the symmetric interval `[-L, L]`, in terms of `Int.natAbs`. -/
private lemma mem_symIcc_iff_natAbs {L : ℕ} {x : ℤ} : x ∈ symIcc L ↔ x.natAbs ≤ L := by
  rw [symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |x| ≤ (L : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · intro h
    have h' : |x| ≤ (L : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    exact abs_le.mp h'

/-- If `x` lies outside the box `symIcc L` then `L < |x|`. -/
private lemma lt_natAbs_of_notMem_symIcc {L : ℕ} {x : ℤ} (hx : x ∉ symIcc L) :
    L < x.natAbs :=
  lt_of_not_ge fun h => hx (mem_symIcc_iff_natAbs.mpr h)

/-- `|x| ≤ |x + t| + M` whenever `|t| ≤ M`. -/
private lemma natAbs_le_natAbs_add_of_natAbs_le {x t : ℤ} {M : ℕ} (ht : t.natAbs ≤ M) :
    x.natAbs ≤ (x + t).natAbs + M := by
  have h := Int.natAbs_add_le (x + t) (-t)
  rw [show x + t + -t = x by ring, Int.natAbs_neg] at h
  omega

theorem gramShift {ι : Type} [Fintype ι] (σ : ι → ℤ) (f : ℤ → ℂ)
    (hf : Work.Peluse.FinSuppZ f) :
    (∑' x : ℤ, ‖∑ k : ι, f (x + σ k)‖ ^ 2)
      = ∑ k : ι, ∑ k' : ι, ∑' x : ℤ, f (x + (σ k - σ k')) * star (f x) := by
  classical
  obtain ⟨N, hN⟩ := hf
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ k : ι, (σ k).natAbs ≤ M :=
    ⟨Finset.univ.sup (fun k : ι => (σ k).natAbs),
      fun k => Finset.le_sup (f := fun k : ι => (σ k).natAbs) (Finset.mem_univ k)⟩
  set B : ℕ := N + M with hB
  -- The summed function vanishes off the box `symIcc B`: `f (x + σ k) = 0` once `|x| > N + M`.
  have hvan : ∀ x : ℤ,
      x ∉ symIcc B → ((‖∑ k : ι, f (x + σ k)‖ ^ 2 : ℝ) : ℂ) = 0 := by
    intro x hx
    have hxB : B < x.natAbs := lt_natAbs_of_notMem_symIcc hx
    rw [hB] at hxB
    have hsum : ∑ k : ι, f (x + σ k) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      refine hN _ ?_
      have h1 := natAbs_le_natAbs_add_of_natAbs_le (x := x) (t := σ k) (hM k)
      omega
    rw [hsum, norm_zero]
    simp
  -- The shifted autocorrelation, at a single pair of shifts.
  have hpair : ∀ k k' : ι, ∑ x ∈ symIcc B, f (x + σ k) * star (f (x + σ k'))
      = ∑' y : ℤ, f (y + (σ k - σ k')) * star (f y) := by
    intro k k'
    set H : ℤ → ℂ := fun y => f (y + (σ k - σ k')) * star (f y) with hH
    have hvanH : ∀ x : ℤ, x ∉ symIcc B → H (x + σ k') = 0 := by
      intro x hx
      have hxB : B < x.natAbs := lt_natAbs_of_notMem_symIcc hx
      rw [hB] at hxB
      have h1 := natAbs_le_natAbs_add_of_natAbs_le (x := x) (t := σ k') (hM k')
      have hNlt : N < (x + σ k').natAbs := by omega
      simp only [hH]
      rw [hN _ hNlt, star_zero, mul_zero]
    calc ∑ x ∈ symIcc B, f (x + σ k) * star (f (x + σ k'))
        = ∑ x ∈ symIcc B, H (x + σ k') := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [hH]
          have harg : x + σ k = x + σ k' + (σ k - σ k') := by ring
          rw [harg]
      _ = ∑' x : ℤ, H (x + σ k') := (tsum_eq_sum (s := symIcc B) hvanH).symm
      _ = ∑' y : ℤ, H y := Equiv.tsum_eq (Equiv.addRight (σ k')) H
      _ = ∑' y : ℤ, f (y + (σ k - σ k')) * star (f y) := by rw [hH]
  -- The complex form of the desired identity.
  have hcomplex : (∑' x : ℤ, ((‖∑ k : ι, f (x + σ k)‖ ^ 2 : ℝ) : ℂ))
      = ∑ k : ι, ∑ k' : ι, ∑' x : ℤ, f (x + (σ k - σ k')) * star (f x) := by
    calc (∑' x : ℤ, ((‖∑ k : ι, f (x + σ k)‖ ^ 2 : ℝ) : ℂ))
        = ∑ x ∈ symIcc B, ((‖∑ k : ι, f (x + σ k)‖ ^ 2 : ℝ) : ℂ) :=
          tsum_eq_sum (s := symIcc B) hvan
      _ = ∑ x ∈ symIcc B, (∑ k : ι, f (x + σ k)) * star (∑ k : ι, f (x + σ k)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          exact ofReal_normSq _
      _ = ∑ x ∈ symIcc B, ∑ k : ι, ∑ k' : ι, f (x + σ k) * star (f (x + σ k')) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [star_sum, Finset.sum_mul_sum]
      _ = ∑ k : ι, ∑ k' : ι, ∑ x ∈ symIcc B, f (x + σ k) * star (f (x + σ k')) := by
          conv_lhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          exact Finset.sum_comm
      _ = ∑ k : ι, ∑ k' : ι, ∑' x : ℤ, f (x + (σ k - σ k')) * star (f x) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => hpair k k'
  rw [← Complex.ofReal_tsum] at hcomplex
  exact hcomplex

end Work.Peluse.SwapCS0
