import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.bary_inj
import Submission.Work.PL.Shell.convexHull_inter_bary
import Submission.Work.PL.Shell.flagEnum_mem
import Submission.Work.PL.Shell.flagEnum_sorted
import Submission.Work.PL.Sd1.Defs
import Submission.Work.PL.Sd1.face_inter

/-!
# `Work.PL.Sd1.Geom` — face geometry of the subdivision simplex of a flag

Auxiliary facts for the `r = 1` shelling of the barycentric subdivision:

* the flag enumeration has no repeated entries;
* the facet of the subdivision simplex of `l` opposite its `k`-th vertex is the `face` on
  the index set `flagIdx l \ {k}`;
* every point of a face has a minimal index set, which controls which faces contain it.
-/

open Set Metric Finset
open scoped BigOperators

namespace Work.PL.Sd1

noncomputable section

variable {N : ℕ}

/-- Membership in `prefixes l`. -/
theorem mem_prefixes_iff' {A : Finset (PL.E N)} {l : List (PL.E N)} :
    A ∈ Work.PL.Shell.prefixes l ↔ ∃ k < l.length, Work.PL.Shell.prefAt l k = A := by
  simp [Work.PL.Shell.prefixes, Finset.mem_image, Finset.mem_range, eq_comm]

/-- `keyLt` is irreflexive. -/
private lemma keyLt_irrefl' {α : Type*} [LinearOrder α] (a : List α) :
    ¬ Work.PL.Shell.keyLt a a := by
  rintro ⟨i, hi, ht, x, y, hx, hy, hlt⟩
  rw [hx] at hy
  exact absurd (Option.some.inj hy) (ne_of_lt hlt)

/-- The flag enumeration of a nodup list has no repeated entries. -/
theorem flagEnum_nodup {vs : List (PL.E N)} {rk : PL.E N → ℕ} (hvs : vs.Nodup)
    (hrk : (vs.map rk).Pairwise (· < ·)) : (Work.PL.Shell.flagEnum vs).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_get]
  have hs := Work.PL.Shell.flagEnum_sorted hvs hrk
  rw [List.pairwise_iff_get] at hs
  intro i j hij hcon
  have h1 := hs i j hij
  rw [hcon] at h1
  exact keyLt_irrefl' _ h1

/-- The `k`-th prefix set of a nodup list has `k + 1` elements. -/
theorem prefAt_card' {l : List (PL.E N)} (hl : l.Nodup) {k : ℕ} (hk : k < l.length) :
    (Work.PL.Shell.prefAt l k).card = k + 1 := by
  rw [Work.PL.Shell.prefAt, List.toFinset_card_of_nodup]
  · rw [List.length_take]; omega
  · exact List.Nodup.sublist (List.take_sublist (k + 1) l) hl

/-- Distinct prefix sets of a nodup list have distinct indices. -/
theorem prefAt_inj' {l : List (PL.E N)} (hl : l.Nodup) {j k : ℕ} (hj : j < l.length)
    (hk : k < l.length) (h : Work.PL.Shell.prefAt l j = Work.PL.Shell.prefAt l k) : j = k := by
  have h1 := prefAt_card' hl hj
  have h2 := prefAt_card' hl hk
  rw [h] at h1
  omega

/-- Every prefix set of a nodup list is nonempty. -/
theorem prefAt_nonempty' {l : List (PL.E N)} (hl : l.Nodup) {k : ℕ} (hk : k < l.length) :
    (Work.PL.Shell.prefAt l k).Nonempty :=
  Finset.card_pos.mp (by rw [prefAt_card' hl hk]; omega)

/-- Every prefix set consists of vertices of `Δ`. -/
theorem prefAt_subset' {Δ : Finset (PL.E N)} {l : List (PL.E N)} (hlΔ : l.toFinset = Δ)
    {k : ℕ} : Work.PL.Shell.prefAt l k ⊆ Δ := by
  intro x hx
  rw [← hlΔ, List.mem_toFinset]
  simp only [Work.PL.Shell.prefAt, List.mem_toFinset] at hx
  exact List.Sublist.subset (List.take_sublist (k + 1) l) hx

/-- The facet of the subdivision simplex of `l` opposite its `k`-th vertex, as a `face`. -/
theorem simp_erase_eq_face {N : ℕ} {Δ : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {l : List (PL.E N)} (hl : l.Nodup) (hlΔ : l.toFinset = Δ) {k : ℕ} (hk : k < l.length) :
    PL.simp (((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary).erase
        (Work.PL.Shell.bary (Work.PL.Shell.prefAt l k))) =
      face l (flagIdx l \ {k}) := by
  have hkey : (((flagIdx l).erase k).image (Work.PL.Shell.prefAt l)).image Work.PL.Shell.bary =
      ((Work.PL.Shell.prefixes l).image Work.PL.Shell.bary).erase
        (Work.PL.Shell.bary (Work.PL.Shell.prefAt l k)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨a, ha, hay⟩ := Finset.mem_image.mp hy
      obtain ⟨j, hj, hja⟩ := Finset.mem_image.mp ha
      obtain ⟨hjk, hle⟩ := Finset.mem_erase.mp hj
      have hle' : j < l.length := Finset.mem_range.mp hle
      rw [← hja] at hay
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr
        ⟨Work.PL.Shell.prefAt l j, mem_prefixes_iff'.mpr ⟨j, hle', rfl⟩, hay⟩⟩
      intro hcon
      exact hjk (prefAt_inj' hl hle' hk (Work.PL.Shell.bary_inj hΔ (prefAt_nonempty' hl hle')
        (prefAt_nonempty' hl hk) (prefAt_subset' hlΔ) (prefAt_subset' hlΔ) (hay.trans hcon)))
    · intro hy
      obtain ⟨hy2, hy1⟩ := Finset.mem_erase.mp hy
      obtain ⟨A, hA, hAy⟩ := Finset.mem_image.mp hy1
      obtain ⟨j, hj, hjA⟩ := mem_prefixes_iff'.mp hA
      refine Finset.mem_image.mpr ⟨Work.PL.Shell.prefAt l j, ?_, ?_⟩
      · refine Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨?_, ?_⟩, rfl⟩
        · intro hjk
          exact hy2 (by rw [← hAy, ← hjA, hjk])
        · exact Finset.mem_range.mpr hj
      · rw [hjA]; exact hAy
  rw [← hkey, Finset.sdiff_singleton_eq_erase]
  rfl

/-- Every point of a face has a minimal index set. -/
theorem exists_min_face {N : ℕ} {Δ : Finset (PL.E N)}
    (hΔ : AffineIndependent ℝ ((↑) : Δ → PL.E N))
    {l : List (PL.E N)} (hl : l.Nodup) (hlΔ : l.toFinset = Δ) {J : Finset ℕ}
    (hJ : J ⊆ flagIdx l) {x : PL.E N} (hx : x ∈ face l J) :
    ∃ J₀, J₀ ⊆ flagIdx l ∧ x ∈ face l J₀ ∧
      ∀ J' ⊆ flagIdx l, x ∈ face l J' → J₀ ⊆ J' := by
  classical
  set S : Finset (Finset ℕ) := (flagIdx l).powerset.filter (fun J => x ∈ face l J) with hS
  have hSne : S.Nonempty := by
    refine ⟨J, ?_⟩
    rw [hS, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hJ, hx⟩
  obtain ⟨J₀, hJ₀S, hmin⟩ := Finset.exists_min_image S Finset.card hSne
  have hJ₀ : J₀ ⊆ flagIdx l ∧ x ∈ face l J₀ := by
    rw [hS, Finset.mem_filter, Finset.mem_powerset] at hJ₀S
    exact hJ₀S
  refine ⟨J₀, hJ₀.1, hJ₀.2, ?_⟩
  intro J' hJ' hx'
  have hmem : J₀ ∩ J' ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.inter_subset_left.trans hJ₀.1, ?_⟩
    rw [face_inter (J := J₀) (J' := J') hΔ hl hlΔ hJ₀.1 hJ']
    exact ⟨hJ₀.2, hx'⟩
  have hcard : J₀.card ≤ (J₀ ∩ J').card := hmin (J₀ ∩ J') hmem
  have hsub : J₀ ∩ J' = J₀ := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard
  rw [← hsub]
  exact Finset.inter_subset_right

end

end Work.PL.Sd1
