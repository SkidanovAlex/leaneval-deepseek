import Mathlib
import Submission.Work.Geometry.Basic
import Submission.Work.Geometry.Counts

namespace Work.Geometry

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors Pointwise

/-- The `ℝ≥0∞`-valued pair count `E_a` (a sum over the lattice of indicators) equals the
cardinality of the finite set of ordered pairs realizing the differences, cast to `ℝ≥0∞`. -/
theorem pairCount_eq_coe_pairCard (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) (U : Finset K) (a : mixedEmbedding.mixedSpace K)
    (hfin : (Xset K I R a).Finite) (hU : ∀ u ∈ U, u ∈ (I : Set K)) :
    pairCount K I R U a = (pairCard K I R U a : ENNReal) := by
  classical
  -- The map `l ↦ a + l` from the lattice to the mixed space is injective.
  have hg_inj : Function.Injective
      (fun l : Lattice K I => a + (l : mixedEmbedding.mixedSpace K)) := by
    intro l l' h
    exact Subtype.ext (add_left_cancel h)
  -- For each `u`, only finitely many `l` have both `a + l` and `a + l + Φ u` in the window,
  -- because the map `l ↦ a + l` injects this set into the finite set `Xset`.
  have hPfin : ∀ u : K, Set.Finite {l : Lattice K I |
      a + (l : mixedEmbedding.mixedSpace K) ∈ Window K R ∧
      a + (l : mixedEmbedding.mixedSpace K) + mixedEmbedding K u ∈ Window K R} := by
    intro u
    refine Set.Finite.subset (Set.Finite.preimage hg_inj.injOn hfin) ?_
    intro l hl
    rw [Set.mem_preimage, mem_Xset]
    refine ⟨?_, hl.1⟩
    have h : a + (l : mixedEmbedding.mixedSpace K) - a = (l : mixedEmbedding.mixedSpace K) := by
      abel
    rw [h]
    exact l.2
  -- The finite set of qualifying lattice points for each `u`.
  let S : K → Finset (Lattice K I) := fun u => (hPfin u).toFinset
  have hS : ∀ (u : K) (l : Lattice K I),
      l ∈ S u ↔ a + (l : mixedEmbedding.mixedSpace K) ∈ Window K R ∧
        a + (l : mixedEmbedding.mixedSpace K) + mixedEmbedding K u ∈ Window K R :=
    fun u l => Set.Finite.mem_toFinset (hPfin u)
  -- Each summand of `pairCountOne` is the indicator of `S u`.
  have hterm : ∀ (u : K) (l : Lattice K I),
      (Window K R).indicator (fun _ => (1 : ENNReal)) (a + (l : mixedEmbedding.mixedSpace K)) *
        (Window K R).indicator (fun _ => (1 : ENNReal))
          (a + (l : mixedEmbedding.mixedSpace K) + mixedEmbedding K u)
        = if l ∈ S u then (1 : ENNReal) else 0 := by
    intro u l
    by_cases hl : l ∈ S u
    · have h1 := (hS u l).mp hl |>.1
      have h2 := (hS u l).mp hl |>.2
      rw [ite_eq_left hl, Set.indicator_of_mem h1, Set.indicator_of_mem h2, mul_one]
    · rw [ite_eq_right hl]
      rw [hS u l] at hl
      rw [not_and_or] at hl
      rcases hl with hl1 | hl2
      · rw [Set.indicator_of_notMem hl1, zero_mul]
      · rw [Set.indicator_of_notMem hl2, mul_zero]
  -- The map from qualifying `(u, l)` to a pair of points of `PairSet`.
  have hmap : ∀ q : ↥(U.sigma S),
      (a + (q.1.2 : mixedEmbedding.mixedSpace K),
       a + (q.1.2 : mixedEmbedding.mixedSpace K) + mixedEmbedding K q.1.1) ∈ PairSet K I R U a := by
    rintro ⟨⟨u, l⟩, hq⟩
    rw [Finset.mem_sigma] at hq
    obtain ⟨hu, hl⟩ := hq
    rw [hS u l] at hl
    obtain ⟨hl1, hl2⟩ := hl
    have hmem : mixedEmbedding K u ∈ Lattice K I := (mem_lattice I).mpr ⟨u, hU u hu, rfl⟩
    refine ⟨?_, ?_, u, hu, ?_⟩
    · rw [mem_Xset]
      refine ⟨?_, hl1⟩
      have h : a + (l : mixedEmbedding.mixedSpace K) - a = (l : mixedEmbedding.mixedSpace K) := by
        abel
      rw [h]
      exact l.2
    · rw [mem_Xset]
      refine ⟨?_, hl2⟩
      have h : a + (l : mixedEmbedding.mixedSpace K) + mixedEmbedding K u - a
          = (l : mixedEmbedding.mixedSpace K) + mixedEmbedding K u := by abel
      rw [h]
      exact add_mem l.2 hmem
    · have h : a + (l : mixedEmbedding.mixedSpace K) + mixedEmbedding K u
          - (a + (l : mixedEmbedding.mixedSpace K)) = mixedEmbedding K u := by abel
      rw [h]
  let g : ↥(U.sigma S) → mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K :=
    fun q => (a + (q.1.2 : mixedEmbedding.mixedSpace K),
              a + (q.1.2 : mixedEmbedding.mixedSpace K) + mixedEmbedding K q.1.1)
  have hg_inj' : Function.Injective g := by
    rintro ⟨⟨u₁, l₁⟩, hq₁⟩ ⟨⟨u₂, l₂⟩, hq₂⟩ h
    have h1 : a + (l₁ : mixedEmbedding.mixedSpace K) = a + (l₂ : mixedEmbedding.mixedSpace K) :=
      congrArg Prod.fst h
    have h2 : a + (l₁ : mixedEmbedding.mixedSpace K) + mixedEmbedding K u₁
        = a + (l₂ : mixedEmbedding.mixedSpace K) + mixedEmbedding K u₂ :=
      congrArg Prod.snd h
    have hl : l₁ = l₂ := Subtype.ext (add_left_cancel h1)
    have hu : u₁ = u₂ := by
      apply mixedEmbedding_injective K
      rw [h1] at h2
      exact add_left_cancel h2
    subst hu
    subst hl
    rfl
  have hf_inj : Function.Injective (fun q : ↥(U.sigma S) =>
      (⟨g q, hmap q⟩ : ↥(PairSet K I R U a))) :=
    fun q₁ q₂ h => hg_inj' (Subtype.ext_iff.mp h)
  have hf_surj : Function.Surjective (fun q : ↥(U.sigma S) =>
      (⟨g q, hmap q⟩ : ↥(PairSet K I R U a))) := by
    rintro ⟨p, hp⟩
    rw [mem_PairSet] at hp
    obtain ⟨hp1, hp2, u, hu, hdiff⟩ := hp
    let l : Lattice K I := ⟨p.1 - a, hp1.1⟩
    have hlv : (l : mixedEmbedding.mixedSpace K) = p.1 - a := rfl
    have hmem : (⟨u, l⟩ : Σ _ : K, Lattice K I) ∈ U.sigma S := by
      rw [Finset.mem_sigma]
      refine ⟨hu, ?_⟩
      rw [hS u l]
      constructor
      · show a + (p.1 - a) ∈ Window K R
        rw [add_sub_cancel]
        exact hp1.2
      · show a + (p.1 - a) + mixedEmbedding K u ∈ Window K R
        rw [show a + (p.1 - a) + mixedEmbedding K u = p.2 by rw [← hdiff]; abel]
        exact hp2.2
    refine ⟨⟨⟨u, l⟩, hmem⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show a + (l : mixedEmbedding.mixedSpace K) = p.1
      rw [hlv]
      exact add_sub_cancel a p.1
    · show a + (l : mixedEmbedding.mixedSpace K) + mixedEmbedding K u = p.2
      rw [hlv]
      rw [show a + (p.1 - a) + mixedEmbedding K u = p.2 by rw [← hdiff]; abel]
  -- The cardinality identity coming from the bijection.
  let e : ↥(U.sigma S) ≃ ↥(PairSet K I R U a) :=
    Equiv.ofBijective (fun q => (⟨g q, hmap q⟩ : ↥(PairSet K I R U a))) ⟨hf_inj, hf_surj⟩
  have hcard : (U.sigma S).card = (PairSet K I R U a).ncard := by
    have h := Nat.card_congr e
    rwa [Nat.card_eq_finsetCard, Nat.card_coe_set_eq] at h
  -- Each `pairCountOne` is the cardinality of `S u`.
  have hpco : ∀ u ∈ U, pairCountOne K I R a u = ((S u).card : ENNReal) := by
    intro u _hu
    rw [pairCountOne]
    rw [tsum_congr (fun l => hterm u l)]
    have h : (∑' l : Lattice K I, (if l ∈ S u then (1 : ENNReal) else 0))
        = ∑ l ∈ S u, (if l ∈ S u then (1 : ENNReal) else 0) :=
      tsum_eq_sum (s := S u) (fun l hl => ite_eq_right hl)
    rw [h]
    simp
  rw [show pairCount K I R U a = ∑ u ∈ U, pairCountOne K I R a u from rfl,
      show pairCard K I R U a = (PairSet K I R U a).ncard from rfl,
      ← hcard, Finset.card_sigma, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun u hu => hpco u hu)

end Work.Geometry
