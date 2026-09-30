import Mathlib
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.Minkowski2.gauge_mem_interior
import Submission.Work.BW.Minkowski2.succMinBody_interior
import Submission.Work.BW.Minkowski2.succMinBody_pos
import Submission.Work.BW.Minkowski2.succMinBody_mono
import Submission.Work.BW.Minkowski2.gauge_isLatticeNorm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The gauge form of the flag of successive minima

If the standard basis vectors `eᵢ` of `ℝᵈ` are lattice vectors of `Λ` realising the successive
minima of a convex, symmetric body `K` (`eᵢ ∈ succMinBody Λ K (i+1) • K`), then every lattice
vector `z ∈ Λ` of `K`-gauge `< succMinBody Λ K (i+1)` vanishes in the coordinates `≥ i`.

In other words `Λ ∩ {gauge K < succMinBody Λ K (i+1)}` is contained in the coordinate subspace
`span {e₀, …, e_{i-1}}` — the "aligned flag" hypothesis of Minkowski's second inequality
(`Work.BW.Minkowski2.core_aligned`).

`Work.BW.Minkowski2.succMinBody_interior` gives the corresponding statement at level `i+1` (that
is, vanishing from coordinate `i+1`), which is *weaker* than what is needed here. The sharp form is
obtained by re-running its argument at the first index `j₀` with `succMinBody Λ K (i+1) ≤
succMinBody Λ K j₀`; in the remaining case, where `succMinBody Λ K i = succMinBody Λ K (i+1)`, the
weaker form applies directly. Concretely: if `z ∈ Λ` does not vanish from coordinate `i` and
`gauge K z < succMinBody Λ K (i+1)`, then `z, e₀, …, e_{i-1}` are independent lattice vectors lying
in `λ • K` for `λ = max (gauge-level) (succMinBody Λ K i)`; if `λ < succMinBody Λ K (i+1)` this
contradicts the definition of the successive minimum, and otherwise
`succMinBody Λ K i = succMinBody Λ K (i+1)` and `Work.BW.Minkowski2.succMinBody_interior` at level
`i` finishes the job.

The bridge from `interior (λ • K)` to `gauge K z < λ` is
`Work.BW.Minkowski2.mem_interior_smulSet_iff_gauge_lt`.
-/

namespace Work.BW.Minkowski2

open MeasureTheory Module
open scoped Pointwise

theorem flag_gauge {d : ℕ} (Λ : Submodule ℤ (Fin d → ℝ)) (K : Set (Fin d → ℝ))
    (hKc : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hKi : (interior K).Nonempty)
    (hstd : ∀ i : Fin d, Work.BW.stdVec i ∈ Λ)
    (hreal : ∀ i : Fin d,
      Work.BW.stdVec i ∈ Work.BW.smulSet (Work.BW.succMinBody Λ K (i.1 + 1)) K)
    (i : Fin d) (z : Fin d → ℝ) (hz : z ∈ Λ)
    (hg : gauge K z < Work.BW.succMinBody Λ K (i.1 + 1)) :
    ∀ m : Fin d, i ≤ m → z m = 0 := by
  classical
  have h0i : (0 : Fin d → ℝ) ∈ interior K := zero_mem_interior_of_convex_symm hKc hsym hKi
  have h0K : (0 : Fin d → ℝ) ∈ K := interior_subset h0i
  have hlam_pos : 0 < Work.BW.succMinBody Λ K (i.1 + 1) :=
    succMinBody_pos Λ K hreal (by omega) (by omega)
  have hint : z ∈ interior (Work.BW.smulSet (Work.BW.succMinBody Λ K (i.1 + 1)) K) :=
    (mem_interior_smulSet_iff_gauge_lt hKc h0i hlam_pos z).mpr hg
  obtain ⟨μ, hμpos, hμlt, hzμ⟩ :=
    exists_smul_lt_of_mem_interior hlam_pos (by rwa [Work.BW.smulSet_eq] at hint)
  set V : Submodule ℝ (Fin d → ℝ) :=
    Submodule.span ℝ (Set.range (fun j : Fin i.1 => Work.BW.stdVec ⟨j.1, by omega⟩)) with hV
  have hVanish : ∀ x ∈ V, ∀ m : Fin d, i.1 ≤ (m : ℕ) → x m = 0 := by
    intro x hx m hm
    refine Submodule.span_induction (p := fun x (_ : x ∈ V) => x m = 0) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩
      have hne : m ≠ (⟨j.1, by omega⟩ : Fin d) := by
        intro hcon
        have h2 : (m : ℕ) = j.1 := by simpa using congrArg Fin.val hcon
        omega
      simp [Work.BW.stdVec, hne]
    · simp
    · intro a b ha hb hpa hpb; simp [hpa, hpb]
    · intro c a ha hpa; simp [hpa]
  have hV_of_vanish : ∀ x : Fin d → ℝ, (∀ m : Fin d, i.1 ≤ (m : ℕ) → x m = 0) → x ∈ V := by
    intro x hx
    have hsum : (∑ j : Fin i.1, x ⟨j.1, by omega⟩ • Work.BW.stdVec ⟨j.1, by omega⟩) = x := by
      ext m
      by_cases hm : (m : ℕ) < i.1
      · rw [Finset.sum_apply]
        rw [Finset.sum_eq_single (⟨m.1, hm⟩ : Fin i.1)]
        · simp [Work.BW.stdVec]
        · intro b _ hb
          have hne : m ≠ (⟨b.1, by omega⟩ : Fin d) := by
            intro hcon
            exact hb (Fin.ext (by simpa using (congrArg Fin.val hcon).symm))
          simp [Work.BW.stdVec, hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [Finset.sum_apply, Finset.sum_eq_zero]
        · exact (hx m (by omega)).symm
        · intro b _
          have hne : m ≠ (⟨b.1, by omega⟩ : Fin d) := by
            intro hcon
            have h2 : (m : ℕ) = b.1 := by simpa using congrArg Fin.val hcon
            omega
          simp [Work.BW.stdVec, hne]
    rw [← hsum]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨j, rfl⟩))
  have hzV : z ∈ V := by
    by_contra hnot
    rcases Nat.eq_zero_or_pos i.1 with hk0 | hk1
    · -- i.1 = 0
      have hz0 : z ≠ 0 := by
        intro hz0
        apply hnot
        rw [hV, hz0]
        exact Submodule.zero_mem _
      have hfin : i.1 + 1 ≤ Module.finrank ℝ
          (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (μ • K))) := by
        have hmem : z ∈ Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (μ • K)) :=
          Submodule.subset_span ⟨hz, hzμ⟩
        have hpos : 0 < Module.finrank ℝ
            (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (μ • K))) :=
          Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨z, hmem⟩, by simpa using hz0⟩
        have h1 : 1 ≤ Module.finrank ℝ
            (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (μ • K))) := by omega
        rw [hk0]
        exact h1
      exact (not_le_finrank_of_lt_succMinBody Λ K hμlt) ⟨hμpos, hfin⟩
    · have hposk : 0 < Work.BW.succMinBody Λ K i.1 :=
        succMinBody_pos Λ K hreal (by omega) (by omega)
      have htailind : LinearIndependent ℝ
          (fun j : Fin i.1 => (Work.BW.stdVec ⟨j.1, by omega⟩ : Fin d → ℝ)) := by
        have h := (stdVec_linearIndependent d).comp
          (fun j : Fin i.1 => (⟨j.1, by omega⟩ : Fin d))
          (fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab))
        exact h
      rcases lt_or_ge (Work.BW.succMinBody Λ K i.1) (Work.BW.succMinBody Λ K (i.1 + 1))
        with hltk | hgek
      · -- Case A : lam_k < lam_{k+1}
        set lamstar : ℝ := max μ (Work.BW.succMinBody Λ K i.1) with hlamstar
        have hlamlt : lamstar < Work.BW.succMinBody Λ K (i.1 + 1) := by
          rw [hlamstar]; exact max_lt hμlt hltk
        have hlampos : 0 < lamstar := lt_of_lt_of_le hμpos (le_max_left _ _)
        have hzstar : z ∈ lamstar • K :=
          smul_set_subset_smul_of_le hKc h0K (le_of_lt hμpos) (le_max_left _ _) hzμ
        have hfinrank : i.1 + 1 ≤ Module.finrank ℝ
            (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lamstar • K))) := by
          have hind : LinearIndependent ℝ
              (Fin.cons z (fun j : Fin i.1 => (Work.BW.stdVec ⟨j.1, by omega⟩ : Fin d → ℝ))) :=
            LinearIndependent.finCons htailind (by
              intro hmem
              exact hnot hmem)
          have hcard : Module.finrank ℝ (Submodule.span ℝ (Set.range
              (Fin.cons z (fun j : Fin i.1 => (Work.BW.stdVec ⟨j.1, by omega⟩ : Fin d → ℝ)))))
              = i.1 + 1 := by
            rw [finrank_span_eq_card hind, Fintype.card_fin]
          rw [← hcard]
          refine Submodule.finrank_mono (Submodule.span_le.mpr ?_)
          rintro x ⟨n, rfl⟩
          refine Submodule.subset_span ⟨?_, ?_⟩
          · induction n using Fin.cases with
            | zero => simpa using hz
            | succ j => simpa using hstd ⟨j.1, by omega⟩
          · induction n using Fin.cases with
            | zero => simpa using hzstar
            | succ j =>
              have hjle : j.1 + 1 ≤ i.1 := by omega
              have hmono : Work.BW.succMinBody Λ K (j.1 + 1)
                  ≤ Work.BW.succMinBody Λ K i.1 :=
                succMinBody_mono Λ K hjle (ne_of_gt hposk)
              have h1 : Work.BW.stdVec ⟨j.1, by omega⟩
                  ∈ Work.BW.succMinBody Λ K (j.1 + 1) • K := by
                have h2 := hreal ⟨j.1, by omega⟩
                rwa [Work.BW.smulSet_eq] at h2
              exact smul_set_subset_smul_of_le hKc h0K (succMinBody_nonneg Λ K _)
                (le_trans hmono (le_max_right _ _)) h1
        exact (not_le_finrank_of_lt_succMinBody Λ K hlamlt) ⟨hlampos, hfinrank⟩
      · -- Case B : lam_k ≥ lam_{k+1}
        have hmono : Work.BW.succMinBody Λ K i.1 ≤ Work.BW.succMinBody Λ K (i.1 + 1) :=
          succMinBody_mono Λ K (by omega) (ne_of_gt hlam_pos)
        have heq : Work.BW.succMinBody Λ K i.1 = Work.BW.succMinBody Λ K (i.1 + 1) :=
          le_antisymm hmono hgek
        have hint' : z ∈ interior (Work.BW.smulSet (Work.BW.succMinBody Λ K i.1) K) := by
          rw [← heq] at hint
          exact hint
        exact hnot (hV_of_vanish z
          (succMinBody_interior Λ K hKc hsym hstd hreal i.1 (by omega) (by omega) z hz hint'))
  intro m hm
  exact hVanish z hzV m (by omega)


end Work.BW.Minkowski2
