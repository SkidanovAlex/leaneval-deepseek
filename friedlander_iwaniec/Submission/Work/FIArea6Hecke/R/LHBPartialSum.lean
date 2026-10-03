import Mathlib
import Submission.Work.FIArea6Hecke.R.DiscDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIPlan.Interface

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary pieces of the reindexing -/

/-- The Größencharacter `ψ` of spin `0` is just `χ`. -/
lemma lhb_psi_zero (chi : GaussianInt → ℂ) (z : GaussianInt) :
    Work.FIArea5.S16Hecke.psi chi 0 z = chi z := by
  rw [Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one]

/-- `heckeLam chi 0 n` written as a plain `χ`-sum over the box `gBox n`. -/
lemma lhb_heckeLam_zero (chi : GaussianInt → ℂ) (n : ℕ) :
    Work.FIArea5.S16Hecke.heckeLam chi 0 n
      = ∑ z ∈ (Work.FIPlan.gBox (n : ℤ)).filter
          (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n), chi z := by
  unfold Work.FIArea5.S16Hecke.heckeLam
  exact Finset.sum_congr rfl (fun z _ => lhb_psi_zero chi z)

/-- The box `gBox` is monotone in its radius. -/
lemma lhb_gBox_mono {a b : ℤ} (h : a ≤ b) : Work.FIPlan.gBox a ⊆ Work.FIPlan.gBox b := by
  intro z hz
  rw [Work.FIArea5.S16Hecke.mem_gBox_iff] at hz ⊢
  exact ⟨Finset.Icc_subset_Icc (by omega) (by omega) hz.1,
    Finset.Icc_subset_Icc (by omega) (by omega) hz.2⟩

/-- Filtering `gBox N` by `IsPrimary ∧ gnorm ≤ N ∧ gnorm = j` is the same as filtering `gBox j`
by `IsPrimary ∧ gnorm = j`, for `1 ≤ j ≤ N`. -/
lemma lhb_filter_gnorm_eq {j N : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N) :
    (Work.FIPlan.gBox (N : ℤ)).filter
        (fun z =>
          (Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z ≤ N) ∧ Work.FIPlan.gnorm z = j)
      = (Work.FIPlan.gBox (j : ℤ)).filter
        (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = j) := by
  apply Finset.ext
  intro z
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨-, ⟨hprim, -⟩, hgn⟩
    refine ⟨?_, hprim, hgn⟩
    exact Work.FIArea5.S16Hecke.mem_gBox_of_gnorm_le (R := (j : ℤ)) (by exact_mod_cast hj)
      (le_of_eq (congrArg (fun m : ℕ => (m : ℤ)) hgn))
  · rintro ⟨hzj, hprim, hgn⟩
    exact ⟨lhb_gBox_mono (by exact_mod_cast hjN) hzj, ⟨hprim, by rw [hgn]; exact hjN⟩, hgn⟩

/-- `discSum (N : ℝ) chi`, for a natural `N`, is the `χ`-sum over the box `gBox N` restricted to
the primary elements of norm `≤ N`. -/
lemma lhb_discSum_nat (chi : GaussianInt → ℂ) (N : ℕ) :
    Work.FIArea6Hecke.R.discSum (N : ℝ) chi
      = ∑ z ∈ (Work.FIPlan.gBox (N : ℤ)).filter
          (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z ≤ N), chi z := by
  unfold Work.FIArea6Hecke.R.discSum
  rw [Nat.ceil_natCast, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z ≤ N
  · have h1 : Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ (N : ℝ) :=
      ⟨h.1, by exact_mod_cast h.2⟩
    rw [if_pos h1, if_pos h]
  · have h1 : ¬ (Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ (N : ℝ)) := by
      intro hc
      exact h ⟨hc.1, by exact_mod_cast hc.2⟩
    rw [if_neg h1, if_neg h]

/-- The prefix sums `∑_{n ≤ N} λ(n)` of the Hecke eigenvalue sequence, with the `n = 0` term
dropped (it vanishes), as a `χ`-sum over the primary elements of norm `≤ N` in the box `gBox N`. -/
lemma lhb_range_sum_eq (chi : GaussianInt → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), Work.FIArea5.S16Hecke.heckeLam chi 0 n
      = ∑ z ∈ (Work.FIPlan.gBox (N : ℤ)).filter
          (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z ≤ N), chi z := by
  classical
  have hsplit : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hmapsto : ∀ z ∈ (Work.FIPlan.gBox (N : ℤ)).filter
        (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z ≤ N),
      Work.FIPlan.gnorm z ∈ Finset.Icc 1 N := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hprim, hle⟩ := hz
    have hpos : 0 < Work.FIPlan.gnorm z :=
      (Work.FIArea5.S16Hecke.isPrimary_odd_gnorm hprim).pos
    exact Finset.mem_Icc.mpr ⟨by omega, hle⟩
  have hzero : Work.FIArea5.S16Hecke.heckeLam chi 0 0 = 0 :=
    Work.FIArea5.S16Hecke.heckeLam_even chi 0 (by decide : Even 0)
  trans ∑ n ∈ Finset.Icc 1 N,
      ∑ z ∈ (Work.FIPlan.gBox (n : ℤ)).filter
        (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n), chi z
  · rw [hsplit, Finset.sum_insert (by rw [Finset.mem_Icc]; omega), hzero, zero_add]
    exact Finset.sum_congr rfl (fun n _ => lhb_heckeLam_zero chi n)
  · rw [← Finset.sum_fiberwise_of_maps_to (g := fun z : GaussianInt => Work.FIPlan.gnorm z)
      (t := Finset.Icc 1 N) hmapsto chi]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hset : (Work.FIPlan.gBox (n : ℤ)).filter
          (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z = n)
        = ((Work.FIPlan.gBox (N : ℤ)).filter
          (fun z => Work.FIPlan.IsPrimary z ∧ Work.FIPlan.gnorm z ≤ N)).filter
          (fun z => Work.FIPlan.gnorm z = n) := by
      rw [Finset.filter_filter]
      exact (lhb_filter_gnorm_eq hn1 hnN).symm
    rw [hset]

/-- The prefix sums of the Hecke eigenvalue sequence `λ(n) = heckeLam chi 0 n` are exactly the
primary disc sums of `DiscDefs.discSum`: for every `N`,
`∑_{n ≤ N} heckeLam chi 0 n = discSum N chi = ∑_{z ∈ gBox N, primary, |z|² ≤ N} χ(z)`.

This is a pure `Finset` reindexing: `ψ_0(z) = χ(z)`, `heckeLam chi 0 n` sums `χ` over the primary
`z` with `gnorm z = n` inside `gBox n`, and every `z` with `gnorm z = n ≥ 1` lies in `gBox n`
(and in `gBox N` for `n ≤ N`), while the `n = 0` term vanishes (`IsPrimary 0` is false). -/
theorem LHBPartialSum (chi : GaussianInt → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), Work.FIArea5.S16Hecke.heckeLam chi 0 n
      = Work.FIArea6Hecke.R.discSum (N : ℝ) chi := by
  rw [lhb_range_sum_eq chi N, lhb_discSum_nat chi N]

end

end Work.FIArea6Hecke.R
