import Mathlib
import Submission.Work.FIArea6Hecke.R2.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R2

open scoped BigOperators
open Work.FIArea6Hecke.R
open Work.FIPlan (gnorm)

noncomputable section

/-- Membership description of `crsMin M`: an element of the box whose key is minimal inside its
residue class mod `M`. -/
lemma mem_crsMin_iff (M : GaussianInt) {s : GaussianInt} :
    s ∈ crsMin M ↔ s ∈ gbox (gnorm M) ∧
      ∀ t ∈ gbox (gnorm M), M ∣ (t - s) →
        s.re + (gnorm M : ℤ) * s.im ≤ t.re + (gnorm M : ℤ) * t.im := by
  classical
  rw [crsMin, Finset.mem_filter]

/-- The key `z ↦ z.re + N · z.im` is injective on the box `[0,N)²`. -/
lemma key_inj_of_mem_gbox {N : ℕ} {u v : GaussianInt}
    (hu : u ∈ gbox N) (hv : v ∈ gbox N)
    (h : u.re + (N : ℤ) * u.im = v.re + (N : ℤ) * v.im) : u = v := by
  obtain ⟨hu0, huN, hui0, huiN⟩ := (Work.FIArea6Hecke.CGD.mem_gbox_iff N u).mp hu
  obtain ⟨hv0, hvN, hvi0, hviN⟩ := (Work.FIArea6Hecke.CGD.mem_gbox_iff N v).mp hv
  have hNpos : (0 : ℤ) < (N : ℤ) := by linarith
  have hNne : (N : ℤ) ≠ 0 := ne_of_gt hNpos
  have hdvd : (N : ℤ) ∣ u.re - v.re := by
    have hkey : u.re - v.re = (N : ℤ) * (v.im - u.im) := by linarith
    rw [hkey]; exact dvd_mul_right _ _
  have hre : u.re = v.re :=
    Work.FIArea6Hecke.CGD.int_eq_of_dvd_sub_of_mem N hu0 huN hv0 hvN hdvd
  have him : u.im = v.im := by
    have h2 : (N : ℤ) * u.im = (N : ℤ) * v.im := by linarith
    exact mul_left_cancel₀ hNne h2
  ext <;> assumption

theorem CrsMinIsCRS (M : GaussianInt) (hM : M ≠ 0) :
    Work.FIArea6Hecke.R.IsCRS M (Work.FIArea6Hecke.R2.crsMin M) := by
  classical
  intro z
  have hNne : gnorm M ≠ 0 := gnorm_ne_zero hM
  -- `gbox N` is a complete residue system mod `(N : ℤ[i])`, and `M ∣ (N : ℤ[i])`.
  have hbox : ∀ z : GaussianInt, ∃! s : GaussianInt, s ∈ gbox (gnorm M) ∧
      (((gnorm M : ℕ)) : GaussianInt) ∣ z - s :=
    (Work.FIArea6Hecke.CGD.BoxCRS (gnorm M) hNne).1
  -- The box elements congruent to `z` modulo `M`.
  set S : Finset GaussianInt := (gbox (gnorm M)).filter (fun t => M ∣ t - z) with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨s, ⟨hsbox, hsdiv⟩, _⟩ := hbox z
    refine ⟨s, Finset.mem_filter.mpr ⟨hsbox, ?_⟩⟩
    have h : M ∣ z - s := dvd_trans (dvd_gnorm M) hsdiv
    simpa only [neg_sub] using dvd_neg.mpr h
  -- Pick the box element of `S` with least key.
  obtain ⟨m, hmS, hmin⟩ := Finset.exists_min_image S (fun t => t.re + (gnorm M : ℤ) * t.im) hSne
  have hmS' := Finset.mem_filter.mp hmS
  have hmgbox : m ∈ gbox (gnorm M) := hmS'.1
  have hmz : M ∣ m - z := hmS'.2
  have hmz' : M ∣ z - m := by simpa only [neg_sub] using dvd_neg.mpr hmz
  -- `m` is minimal in its residue class, hence lies in `crsMin M`.
  have hmem : m ∈ crsMin M := by
    rw [mem_crsMin_iff]
    refine ⟨hmgbox, ?_⟩
    intro t ht htm
    have htS : t ∈ S := by
      refine Finset.mem_filter.mpr ⟨ht, ?_⟩
      have h := dvd_add htm hmz
      have heq : (t - m) + (m - z) = t - z := by ring
      rwa [heq] at h
    exact hmin t htS
  refine ⟨m, ⟨hmem, hmz'⟩, ?_⟩
  -- Uniqueness: two minimal box elements in the same residue class coincide.
  intro y ⟨hy, hyz⟩
  have hy' := (mem_crsMin_iff M).mp hy
  have hygbox : y ∈ gbox (gnorm M) := hy'.1
  have hymin := hy'.2
  have hmmin := (mem_crsMin_iff M).mp hmem |>.2
  have hd1 : M ∣ y - m := by
    have h := dvd_sub hmz' hyz
    have heq : (z - m) - (z - y) = y - m := by ring
    rwa [heq] at h
  have hd2 : M ∣ m - y := by simpa only [neg_sub] using dvd_neg.mpr hd1
  have hle1 : y.re + (gnorm M : ℤ) * y.im ≤ m.re + (gnorm M : ℤ) * m.im :=
    hymin m hmgbox hd2
  have hle2 : m.re + (gnorm M : ℤ) * m.im ≤ y.re + (gnorm M : ℤ) * y.im :=
    hmmin y hygbox hd1
  have heqk : y.re + (gnorm M : ℤ) * y.im = m.re + (gnorm M : ℤ) * m.im := le_antisymm hle1 hle2
  exact key_inj_of_mem_gbox hygbox hmgbox heqk

end

end Work.FIArea6Hecke.R2
