/-
  WilCrux — auxiliary lemmas for node N4d (`Work.WilCrux.ParamDerivJoint`).

  Contents:

  * `Omega_inter_exists` — the class `∃ F D, X ∈ S.Ω F D a` is closed under binary intersections;
  * `thin_closure_exists` — `thin_closure` in the "some bounds" form;
  * `tendsto_punctured_iff`, `not_tendsto_punctured_iff` — the `ε`-`δ` characterisation of the
    punctured limit `𝓝[{0}ᶜ] 0`;
  * `jointLimit_of_definable` — the Baire argument of N4a/N4d: a definable pointwise limit on
    `Q0` (off a definable set `F` of empty interior) with a definable family of "modulus" sets
    `A k n` covering `Q0 ∖ F` yields an open `Q5 ⊆ Q0 ∩ J` dense in `Q0`, where `J` is any
    `Ω`-definable set containing every point at which the joint limit holds.

  Everything here is `sorry`-free.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Cell.thin_closure
import Submission.Work.WilkG4c.DSGBallMem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Binary intersections and `thin_closure` with existentially quantified bounds -/

/-- The class of `Ω`-sets with *some* bounds is closed under binary intersections. -/
theorem Omega_inter_exists {S : WilkiesDesign.SOMin} {a : ℕ} {X Y : Set (Fin a → ℝ)}
    (hX : ∃ F D : ℕ, X ∈ S.Ω F D a) (hY : ∃ F D : ℕ, Y ∈ S.Ω F D a) :
    ∃ F D : ℕ, X ∩ Y ∈ S.Ω F D a := by
  obtain ⟨F₁, D₁, h1⟩ := hX
  obtain ⟨F₂, D₂, h2⟩ := hY
  exact ⟨max F₁ F₂ + 1, D₁ + D₂, Work.WilkG4c.dsg_inter2 S h1 h2⟩

/-- `thin_closure` for `Ω`-sets given with existentially quantified bounds. -/
theorem thin_closure_exists (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {n : ℕ}
    {X : Set (Fin n → ℝ)} (hX : ∃ F D : ℕ, X ∈ S.Ω F D n) (hint : interior X = ∅) :
    interior (closure X) = ∅ := by
  obtain ⟨F, D, hX⟩ := hX
  exact Work.WilG1.Cell.thin_closure (S := S) hcd
    (show X ∈ S.Ω F (Polynomial.eval D Polynomial.X) n by simpa using hX) hint

/-! ## 2. The `ε`-`δ` characterisation of the punctured limit -/

/-- `g z → 0` along the punctured neighbourhood filter of `0` is the pointwise `ε`-`δ`
condition on the punctured balls. -/
theorem tendsto_punctured_iff {b : ℕ} (g : (Fin b → ℝ) → ℝ) :
    Filter.Tendsto g (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < δ → |g z| < ε := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    have h1 : ∀ᶠ z in nhds (0 : Fin b → ℝ),
        z ∈ ({(0 : Fin b → ℝ)}ᶜ : Set (Fin b → ℝ)) → dist (g z) 0 < ε :=
      eventually_nhdsWithin_iff.mp (h ε hε)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp h1
    refine ⟨δ, hδ, fun z hz hzδ => ?_⟩
    have h2 : dist (g z) 0 < ε :=
      hδ' (show dist z (0 : Fin b → ℝ) < δ by simpa [dist_eq_norm] using hzδ)
        (by simpa using hz)
    simpa [Real.dist_eq] using h2
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    rw [eventually_nhdsWithin_iff]
    refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun z hz hz0 => ?_⟩
    have h2 : |g z| < ε := hδ' z (by simpa using hz0) (by simpa [dist_eq_norm] using hz)
    simpa [Real.dist_eq] using h2

/-- Negation of the punctured limit, in the `ε`-`δ` form. -/
theorem not_tendsto_punctured_iff {b : ℕ} (g : (Fin b → ℝ) → ℝ) :
    ¬ Filter.Tendsto g (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0) ↔
      ∃ ε > 0, ∀ δ > 0, ∃ z : Fin b → ℝ, z ≠ 0 ∧ ‖z‖ < δ ∧ ε ≤ |g z| := by
  rw [tendsto_punctured_iff]
  constructor
  · intro h
    push_neg at h
    exact h
  · rintro ⟨ε, hε, hδ⟩ h'
    obtain ⟨δ, hδpos, hδ'⟩ := h' ε hε
    obtain ⟨z, hz0, hzδ, hzε⟩ := hδ δ hδpos
    exact absurd (hδ' z hz0 hzδ) (not_lt.mpr hzε)

/-! ## 3. The Baire argument -/

/-- **N4a/N4d (abstract).**  Let `f : ℝ^a → ℝ^b → ℝ`, `Q0 ⊆ ℝ^a` open, `t > 0`, and suppose

* `F` (the pointwise failure set) is `Ω`-definable with `interior (F ∩ Q0) = ∅`;
* `A k n` are `Ω`-definable sets on which `|f w z| < 1/(k+1)` holds for `z ≠ 0`,
  `‖z‖ < t/(n+1)`;
* every point of `Q0` where the pointwise limit holds lies in some `A k n` (for every `k`);
* `J` is `Ω`-definable and contains every point at which the joint limit holds (`hJlink`).

Then there is an open `Q5 ⊆ Q0 ∩ J` with `Q0 ⊆ closure Q5`. -/
theorem jointLimit_of_definable (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (Q0 : Set (Fin a → ℝ)) (hQ0 : IsOpen Q0) (t : ℝ) (ht : 0 < t)
    (F : Set (Fin a → ℝ)) (hFmem : ∃ Ff Df : ℕ, F ∈ S.Ω Ff Df a)
    (hFint : interior (F ∩ Q0) = ∅)
    (A : ℕ → ℕ → Set (Fin a → ℝ)) (hAmem : ∀ k n, ∃ Fn Dn : ℕ, A k n ∈ S.Ω Fn Dn a)
    (hAsub : ∀ k n, A k n ⊆ {w : Fin a → ℝ | ∀ z : Fin b → ℝ,
      z ≠ 0 → ‖z‖ < t / ((n : ℝ) + 1) → |f w z| < 1 / ((k : ℝ) + 1)})
    (hAcov : ∀ w ∈ Q0, w ∉ F → ∀ k, ∃ n, w ∈ A k n)
    (J : Set (Fin a → ℝ)) (hJmem : ∃ Ff Df : ℕ, J ∈ S.Ω Ff Df a)
    (hJlink : ∀ w : Fin a → ℝ, (∀ k : ℕ, ∃ η > 0, ∀ (w' : Fin a → ℝ) (z : Fin b → ℝ),
      dist w' w < η → z ≠ 0 → ‖z‖ < η → |f w' z| < 1 / ((k : ℝ) + 1)) → w ∈ J) :
    ∃ Q5 : Set (Fin a → ℝ), IsOpen Q5 ∧ Q5 ⊆ Q0 ∧ Q0 ⊆ closure Q5 ∧ Q5 ⊆ J := by
  classical
  have htpos : ∀ n : ℕ, 0 < t / ((n : ℝ) + 1) := fun n => div_pos ht (by positivity)
  -- the "level `k` joint bound" set
  set K : ℕ → Set (Fin a → ℝ) := fun k => ⋃ n, interior (A k n) with hKdef
  have hKopen : ∀ k, IsOpen (K k) := fun k => isOpen_iUnion fun n => isOpen_interior
  -- every ball inside `Q0` meets `K k`
  have hball : ∀ k, ∀ (c : Fin a → ℝ) (ρ : ℝ), 0 < ρ → Metric.ball c ρ ⊆ Q0 →
      (Metric.ball c ρ ∩ K k).Nonempty := by
    intro k c ρ hρ hsub
    by_cases hex : ∃ n : ℕ, (interior (Metric.ball c ρ ∩ A k n)).Nonempty
    · obtain ⟨n, x, hx⟩ := hex
      refine ⟨x, ?_⟩
      exact ⟨(interior_subset hx).1,
        Set.mem_iUnion.mpr ⟨n, interior_mono Set.inter_subset_right hx⟩⟩
    · push_neg at hex
      -- all the `A k n` are thin on the ball; the leftover lies in `F ∩ ball`
      have hintA : ∀ n : ℕ, interior (Metric.ball c ρ ∩ A k n) = ∅ := fun n => hex n
      have hBFmem : ∃ Fb Db : ℕ, Metric.ball c ρ ∩ F ∈ S.Ω Fb Db a :=
        Omega_inter_exists (S := S) (Work.WilkG4c.dsg_ball_mem S c hρ) hFmem
      have hintF : interior (Metric.ball c ρ ∩ F) = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨y, hy⟩
        have hy' : y ∈ interior (F ∩ Q0) :=
          interior_mono (s := Metric.ball c ρ ∩ F) (t := F ∩ Q0)
            (fun z hz => ⟨hz.2, hsub hz.1⟩) hy
        rw [hFint] at hy'
        exact hy'
      have hndF : interior (closure (Metric.ball c ρ ∩ F)) = ∅ :=
        thin_closure_exists S hcd hBFmem hintF
      have hndA : ∀ n : ℕ, interior (closure (Metric.ball c ρ ∩ A k n)) = ∅ := fun n =>
        thin_closure_exists S hcd
          (Omega_inter_exists (S := S) (Work.WilkG4c.dsg_ball_mem S c hρ) (hAmem k n))
          (hintA n)
      -- Baire: the complements of the closures are open dense
      set W : Option ℕ → Set (Fin a → ℝ) := fun i => match i with
        | none => (closure (Metric.ball c ρ ∩ F))ᶜ
        | some n => (closure (Metric.ball c ρ ∩ A k n))ᶜ with hWdef
      have hWopen : ∀ i : Option ℕ, IsOpen (W i) := by
        intro i
        cases i with
        | none => exact isClosed_closure.isOpen_compl
        | some n => exact isClosed_closure.isOpen_compl
      have hWdense : ∀ i : Option ℕ, Dense (W i) := by
        intro i
        cases i with
        | none =>
          rw [dense_iff_closure_eq, closure_compl]
          simp [hndF]
        | some n =>
          rw [dense_iff_closure_eq, closure_compl]
          simp [hndA n]
      have hdens := dense_iInter_of_isOpen (f := W) hWopen hWdense
      have hballne : (Metric.ball c ρ).Nonempty :=
        ⟨c, by simp only [Metric.mem_ball, dist_self]; exact hρ⟩
      obtain ⟨x, hxW, hxB⟩ := hdens.exists_mem_open Metric.isOpen_ball hballne
      -- the cover of the ball by `F` and the `A k n`
      have hcov : Metric.ball c ρ ⊆ (Metric.ball c ρ ∩ F) ∪
          ⋃ n, (Metric.ball c ρ ∩ A k n) := by
        intro w hw
        by_cases hwF : w ∈ F
        · exact Or.inl ⟨hw, hwF⟩
        · obtain ⟨n, hn⟩ := hAcov w (hsub hw) hwF k
          exact Or.inr (Set.mem_iUnion.mpr ⟨n, ⟨hw, hn⟩⟩)
      have hxWi : x ∈ ⋂ i : Option ℕ, W i := hxW
      rcases hcov hxB with h | h
      · exact absurd (subset_closure h) (Set.mem_iInter.mp hxWi none)
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
        exact absurd (subset_closure hn) (Set.mem_iInter.mp hxWi (some n))
  -- density of `K k` in `Q0`
  have hKdense : ∀ k, Q0 ⊆ closure (K k) := by
    intro k w hwQ0
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.mem_nhds_iff.mp (hQ0.mem_nhds hwQ0)
    have hmin : 0 < min ε δ₀ := lt_min hε hδ₀
    have hr : 0 < min ε δ₀ / 2 := by linarith
    have hsub : Metric.ball w (min ε δ₀ / 2) ⊆ Q0 := by
      intro y hy
      rw [Metric.mem_ball] at hy
      apply hδ₀'
      rw [Metric.mem_ball]
      have h2 : min ε δ₀ / 2 ≤ δ₀ := by
        have h3 := min_le_right ε δ₀
        linarith
      linarith
    obtain ⟨y, hyB, hyK⟩ := hball k w (min ε δ₀ / 2) hr hsub
    refine ⟨y, hyK, ?_⟩
    have hyB' : dist w y < min ε δ₀ / 2 := by
      rw [Metric.mem_ball] at hyB
      rwa [dist_comm]
    have h2 := min_le_left ε δ₀
    linarith
  -- the level-`k` bound gives membership in `J`
  have hlink : ∀ w : Fin a → ℝ, (∀ k : ℕ, w ∈ K k) → w ∈ J := by
    intro w hw
    apply hJlink w
    intro k
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hw k)
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hn)
    refine ⟨min r (t / ((n : ℝ) + 1)), lt_min hr (htpos n), ?_⟩
    intro w' z hww' hz0 hz
    have hw'ball : w' ∈ Metric.ball w r := by
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hww' (min_le_left _ _)
    have hw'A : w' ∈ A k n := hrsub hw'ball
    exact hAsub k n hw'A z hz0 (lt_of_lt_of_le hz (min_le_right _ _))
  -- `Q0 ⊆ closure J`
  have hKcat : ∀ k, Dense (K k ∪ (closure Q0)ᶜ) := by
    intro k
    rw [dense_iff_closure_eq]
    rw [Set.eq_univ_iff_forall]
    intro w
    by_cases hw : w ∈ closure Q0
    · exact closure_mono Set.subset_union_left
        (closure_minimal (hKdense k) isClosed_closure hw)
    · exact subset_closure (Or.inr hw)
  have hBigdense : Dense (⋂ k : ℕ, (K k ∪ (closure Q0)ᶜ)) :=
    dense_iInter_of_isOpen (fun k => (hKopen k).union isClosed_closure.isOpen_compl) hKcat
  have hJdense : Q0 ⊆ closure J := by
    intro w hwQ0
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.mem_nhds_iff.mp (hQ0.mem_nhds hwQ0)
    have hmin : 0 < min ε δ₀ := lt_min hε hδ₀
    have hr : 0 < min ε δ₀ / 2 := by linarith
    have hsub : Metric.ball w (min ε δ₀ / 2) ⊆ Q0 := by
      intro y hy
      rw [Metric.mem_ball] at hy
      apply hδ₀'
      rw [Metric.mem_ball]
      have h2 : min ε δ₀ / 2 ≤ δ₀ := by
        have h3 := min_le_right ε δ₀
        linarith
      linarith
    have hUne : (Metric.ball w (min ε δ₀ / 2) ∩ Q0).Nonempty := by
      refine ⟨w, ?_, hwQ0⟩
      simp only [Metric.mem_ball, dist_self]
      exact hr
    obtain ⟨x, hxBig, hxU⟩ :=
      hBigdense.exists_mem_open (Metric.isOpen_ball.inter hQ0) hUne
    have hxQ0 : x ∈ Q0 := hxU.2
    have hxcl : x ∈ interior (closure Q0) :=
      interior_maximal (subset_closure (s := Q0)) hQ0 hxQ0
    have hxK : ∀ k : ℕ, x ∈ K k := by
      intro k
      rcases Set.mem_iInter.mp hxBig k with h | h
      · exact h
      · exact absurd (interior_subset hxcl) h
    refine ⟨x, hlink x hxK, ?_⟩
    have hxdist : dist x w < min ε δ₀ / 2 := by
      have h1 : x ∈ Metric.ball w (min ε δ₀ / 2) := hxU.1
      rwa [Metric.mem_ball] at h1
    have hxdist' : dist w x < min ε δ₀ / 2 := by rw [dist_comm]; exact hxdist
    have h2 := min_le_left ε δ₀
    linarith
  -- the final open set: the interior of `J`, cut down to `Q0`
  have hInterDense : ∀ (c : Fin a → ℝ) (ρ : ℝ), 0 < ρ → Metric.ball c ρ ⊆ Q0 →
      (interior J ∩ Metric.ball c ρ).Nonempty := by
    intro c ρ hρ hsub
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hint : interior (J ∩ Metric.ball c ρ) = ∅ := by
      rw [interior_inter, Metric.isOpen_ball.interior_eq]
      exact hcon
    have hJBmem : ∃ Fj Dj : ℕ, J ∩ Metric.ball c ρ ∈ S.Ω Fj Dj a :=
      Omega_inter_exists (S := S) hJmem (Work.WilkG4c.dsg_ball_mem S c hρ)
    have hndJ : interior (closure (J ∩ Metric.ball c ρ)) = ∅ :=
      thin_closure_exists S hcd hJBmem hint
    have hsub' : Metric.ball c ρ ⊆ closure (J ∩ Metric.ball c ρ) := by
      intro x hx
      have hxc : dist x c < ρ := by rwa [Metric.mem_ball] at hx
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hr : 0 < min ε (ρ - dist x c) := lt_min hε (by linarith)
      have hxQ0 : x ∈ Q0 := by
        apply hsub
        rwa [Metric.mem_ball]
      have hxJ : x ∈ closure J := hJdense (hsub (by rwa [Metric.mem_ball] at hx))
      rw [Metric.mem_closure_iff] at hxJ
      obtain ⟨y, hyJ, hyx⟩ := hxJ (min ε (ρ - dist x c)) hr
      refine ⟨y, ?_, ?_⟩
      · refine ⟨hyJ, ?_⟩
        rw [Metric.mem_ball]
        have hyx' : dist y x < min ε (ρ - dist x c) := by rw [dist_comm]; exact hyx
        have h2 : min ε (ρ - dist x c) ≤ ρ - dist x c := min_le_right _ _
        linarith [dist_triangle y x c]
      · have h2 : min ε (ρ - dist x c) ≤ ε := min_le_left _ _
        linarith
    have hballsub : Metric.ball c ρ ⊆ interior (closure (J ∩ Metric.ball c ρ)) :=
      interior_maximal hsub' Metric.isOpen_ball
    have hmem : c ∈ interior (closure (J ∩ Metric.ball c ρ)) := by
      apply hballsub
      simp only [Metric.mem_ball, dist_self]
      exact hρ
    rw [hndJ] at hmem
    exact hmem
  refine ⟨Q0 ∩ interior J, hQ0.inter isOpen_interior, Set.inter_subset_left, ?_, ?_⟩
  · intro w hwQ0
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.mem_nhds_iff.mp (hQ0.mem_nhds hwQ0)
    have hmin : 0 < min ε δ₀ := lt_min hε hδ₀
    have hr : 0 < min ε δ₀ / 2 := by linarith
    have hsub : Metric.ball w (min ε δ₀ / 2) ⊆ Q0 := by
      intro y hy
      rw [Metric.mem_ball] at hy
      apply hδ₀'
      rw [Metric.mem_ball]
      have h2 : min ε δ₀ / 2 ≤ δ₀ := by
        have h3 := min_le_right ε δ₀
        linarith
      linarith
    obtain ⟨x, hxJ, hxB⟩ := hInterDense w (min ε δ₀ / 2) hr hsub
    have hxB' : dist x w < min ε δ₀ / 2 := by
      rw [Metric.mem_ball] at hxB
      exact hxB
    have hxB'' : dist w x < min ε δ₀ / 2 := by rw [dist_comm]; exact hxB'
    refine ⟨x, ⟨hsub (by rw [Metric.mem_ball]; exact hxB'), hxJ⟩, ?_⟩
    have h2 := min_le_left ε δ₀
    linarith
  · exact Set.inter_subset_right.trans interior_subset

end Work.WilCrux
