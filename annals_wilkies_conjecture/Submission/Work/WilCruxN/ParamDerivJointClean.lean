import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilCrux.ParamDerivAux
import Submission.Work.WilCruxN.PhiGraphMem
import Submission.Work.WilCruxN.FibreSetsMem
import Submission.Work.WilCruxN.JointSetMem
import Submission.Work.WilCruxN.ParamDerivPointwiseClean

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCruxN

open Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-- **N4d (the joint parameter-partial convergence).**  Under the hypotheses of
`ParamDerivPointwise` *plus* N4b's uniform slice-continuity clause `hz`, the parameter partials
converge *(jointly, along the punctured filter `𝓝[{p | p.2 ≠ 0}] (w,0)`)* to the parameter
partial of `a(w) = G w 0`, at every point of an open subset `Q5 ⊆ Q0` with `Q0 ⊆ closure Q5`.

Proof: the failure sets `Fail_n := {w ∈ Q0 : ∀δ>0, ∃z, 0<‖z‖<δ ∧ (w,z) ∈ E_n}` (with `E_n` the
`Ω`-set "`∂_{w_i}Ĝ ≥ 1/n` or `≤ -1/n` off the sheet") are `Ω`-definable, and
`ParamDerivPointwise` says they have empty interior, so (via `thin_closure`) they are meagre; the
two-scale Baire argument of N4a (on the pointwise-good and the uniformly-good `Ω`-sets, using the
pointwise behaviour of the partials at `z ≠ 0` and the continuity of the off-sheet derivative)
then gives an open `Q5` with the joint convergence at every point. -/
theorem ParamDerivJoint (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    {a b F D : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1))
    (Q0 : Set (Fin a → ℝ)) (hQ0 : IsOpen Q0) (r0 : ℝ) (hr0 : 0 < r0)
    (hsl : ∀ w ∈ Q0, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0))
    (hoff : ∀ w ∈ Q0, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    (hz : ∀ w₀ ∈ Q0, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      dist w w₀ < η → z ≠ 0 → ‖z‖ < η → ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε) :
    ∃ Q5 : Set (Fin a → ℝ), IsOpen Q5 ∧ Q5 ⊆ Q0 ∧ Q0 ⊆ closure Q5 ∧
      ∀ w₀ ∈ Q5, ∀ i : Fin a, Filter.Tendsto
        (fun p : (Fin a → ℝ) × (Fin b → ℝ) =>
          fderiv ℝ (Work.WilG4c.famFun G) (Fin.append p.1 p.2) (Fin.append (Pi.single i 1) 0)
            - fderiv ℝ (fun w' => G w' 0) p.1 (Pi.single i 1))
        (nhdsWithin (w₀, 0) {p : (Fin a → ℝ) × (Fin b → ℝ) | p.2 ≠ 0}) (nhds 0) := by
  classical
  set t : ℝ := min 1 r0 with htdef
  have ht : 0 < t := lt_min one_pos hr0
  have ht1 : t ≤ 1 := by rw [htdef]; exact min_le_left _ _
  -- the per-direction statement
  have key : ∀ i : Fin a, ∃ Q5 : Set (Fin a → ℝ), IsOpen Q5 ∧ Q5 ⊆ Q0 ∧ Q0 ⊆ closure Q5 ∧
      ∀ w₀ ∈ Q5, Filter.Tendsto
        (fun p : (Fin a → ℝ) × (Fin b → ℝ) =>
          fderiv ℝ (Work.WilG4c.famFun G) (Fin.append p.1 p.2)
              (Fin.append (Pi.single i 1) (0 : Fin b → ℝ))
            - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) p.1 (Pi.single i 1))
        (nhdsWithin (w₀, 0) {p : (Fin a → ℝ) × (Fin b → ℝ) | p.2 ≠ 0}) (nhds 0) := by
    intro i
    set Φ : (Fin a → ℝ) → (Fin b → ℝ) → ℝ := fun w z =>
      fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)
          (Fin.append (Pi.single i 1) (0 : Fin b → ℝ))
        - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w (Pi.single i 1) with hΦ
    -- the graph of `Φ` is `Ω`-definable (N4d-plumbing 1)
    obtain ⟨Ag, cg, hAg⟩ := PhiGraphMem S (a := a) (b := b) (F := F)
    have hΦgraph : WilkiesDesign.CG.famGraph Φ ∈ S.Ω Ag (cg.eval D) (a + b + 1) := by
      rw [hΦ]
      exact hAg D G i hG
    -- the failure set (N4d-plumbing 2, first part)
    obtain ⟨hFib1, hFib2⟩ := FibreSetsMem S (a := a) (b := b) (F := Ag) t
    obtain ⟨AF, cF, hFmem'⟩ := hFib1
    set Fset : Set (Fin a → ℝ) := {w | ¬ Filter.Tendsto (Φ w)
      (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0)} with hFset
    have hFmem : ∃ Ff Df : ℕ, Fset ∈ S.Ω Ff Df a :=
      ⟨AF, cF.eval (cg.eval D), hFmem' (cg.eval D) Φ hΦgraph⟩
    -- N4c: the failure set has empty interior
    have hFint : interior (Fset ∩ Q0) = ∅ := by
      have h := ParamDerivPointwise S hcd G hG Q0 hQ0 r0 hr0 hsl hoff hz i
      have hset : ({w : Fin a → ℝ | w ∈ Q0 ∧ ¬ Filter.Tendsto (fun z : Fin b → ℝ =>
            fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z)
                (Fin.append (Pi.single i 1) (0 : Fin b → ℝ))
              - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) w (Pi.single i 1))
          (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0)}) = Fset ∩ Q0 := by
        rw [hFset]
        ext w
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
      rw [hset] at h
      exact h
    -- the modulus sets (N4d-plumbing 2, second part)
    obtain ⟨AM, cM, hMmem'⟩ := hFib2
    set A : ℕ → ℕ → Set (Fin a → ℝ) := fun k n => {w : Fin a → ℝ | ∀ z : Fin b → ℝ, z ≠ 0 →
      ‖z‖ < t / ((n : ℝ) + 1) → |Φ w z| < 1 / ((k : ℝ) + 1)} with hA
    have hAmem : ∀ k n, ∃ Fn Dn : ℕ, A k n ∈ S.Ω Fn Dn a :=
      fun k n => ⟨AM, cM.eval (cg.eval D), hMmem' (cg.eval D) Φ hΦgraph k n⟩
    have hAsub : ∀ k n, A k n ⊆ {w : Fin a → ℝ | ∀ z : Fin b → ℝ,
        z ≠ 0 → ‖z‖ < t / ((n : ℝ) + 1) → |Φ w z| < 1 / ((k : ℝ) + 1)} :=
      fun k n w hw => hw
    -- the ε-δ characterisation of the pointwise limit gives the cover
    have hAcov : ∀ w ∈ Q0, w ∉ Fset → ∀ k, ∃ n, w ∈ A k n := by
      intro w hwQ0 hwF k
      have hT : Filter.Tendsto (Φ w)
          (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0) := by
        rw [hFset] at hwF
        exact not_not.mp hwF
      have hconv := (tendsto_punctured_iff (Φ w)).mp hT
      obtain ⟨δ, hδ, hδ'⟩ := hconv (1 / ((k : ℝ) + 1)) (by positivity)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < min δ t from lt_min hδ ht)
      refine ⟨n, ?_⟩
      show ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < t / ((n : ℝ) + 1) →
          |Φ w z| < 1 / ((k : ℝ) + 1)
      intro z hz0 hz
      have hzδ : ‖z‖ < δ := by
        have h2 : t / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
          have hx : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
          rw [div_eq_mul_inv]
          calc t * ((n : ℝ) + 1)⁻¹ ≤ 1 * ((n : ℝ) + 1)⁻¹ :=
                mul_le_mul_of_nonneg_right ht1 (le_of_lt hx)
            _ = 1 / ((n : ℝ) + 1) := by rw [one_mul, one_div]
        exact lt_of_lt_of_le hz
          (le_of_lt (lt_of_lt_of_le (lt_of_le_of_lt h2 hn) (min_le_left _ _)))
      exact hδ' z hz0 hzδ
    -- the joint-limit set (N4d-plumbing 3)
    obtain ⟨AJ, cJ, hJmem'⟩ := JointSetMem S (a := a) (b := b) (F := Ag)
    set J : Set (Fin a → ℝ) := {w | ∀ ε > 0, ∃ δ > 0,
      ∀ (w' : Fin a → ℝ) (z : Fin b → ℝ), dist w' w < δ → z ≠ 0 → ‖z‖ < δ → |Φ w' z| < ε}
      with hJ
    have hJmem : ∃ Ff Df : ℕ, J ∈ S.Ω Ff Df a :=
      ⟨AJ, cJ.eval (cg.eval D), hJmem' (cg.eval D) Φ hΦgraph⟩
    have hJlink : ∀ w : Fin a → ℝ, (∀ k : ℕ, ∃ η > 0, ∀ (w' : Fin a → ℝ) (z : Fin b → ℝ),
        dist w' w < η → z ≠ 0 → ‖z‖ < η → |Φ w' z| < 1 / ((k : ℝ) + 1)) → w ∈ J := by
      intro w hw ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      obtain ⟨η, hη, hη'⟩ := hw k
      exact ⟨η, hη, fun w' z hd hz0 hz => lt_trans (hη' w' z hd hz0 hz) hk⟩
    -- the abstract Baire argument (N4a/N4d)
    obtain ⟨Q, hQo, hQsub, hQdense, hQJ⟩ :=
      jointLimit_of_definable S hcd Φ Q0 hQ0 t ht Fset hFmem hFint A hAmem hAsub hAcov J hJmem
        hJlink
    refine ⟨Q, hQo, hQsub, hQdense, ?_⟩
    intro w₀ hw₀
    have hJw : ∀ ε > 0, ∃ δ > 0, ∀ (w' : Fin a → ℝ) (z : Fin b → ℝ),
        dist w' w₀ < δ → z ≠ 0 → ‖z‖ < δ → |Φ w' z| < ε := hQJ hw₀
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hJw ε hε
    rw [eventually_nhdsWithin_iff]
    refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun p hp hp2 => ?_⟩
    have hp1 : dist p.1 w₀ < δ := by
      rw [Prod.dist_eq] at hp
      exact lt_of_le_of_lt (le_max_left _ _) hp
    have hp2' : ‖p.2‖ < δ := by
      rw [Prod.dist_eq] at hp
      have h2 := lt_of_le_of_lt (le_max_right _ _) hp
      simpa [dist_eq_norm] using h2
    have hval : |fderiv ℝ (Work.WilG4c.famFun G) (Fin.append p.1 p.2)
          (Fin.append (Pi.single i 1) (0 : Fin b → ℝ))
        - fderiv ℝ (fun w' : Fin a → ℝ => G w' 0) p.1 (Pi.single i 1)| < ε :=
      hδ' p.1 p.2 hp1 hp2 hp2'
    simpa [Real.dist_eq] using hval
  choose Q hQo hQsub hQdense hQpoint using key
  refine ⟨Q0 ∩ ⋂ i : Fin a, Q i, hQ0.inter (isOpen_iInter_of_finite hQo),
    Set.inter_subset_left, ?_, ?_⟩
  · -- density of the intersection of the finitely many `Q i`
    intro w hwQ0
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hVopen : ∀ i : Fin a, IsOpen (Q i ∪ (closure Q0)ᶜ) := fun i =>
      (hQo i).union isClosed_closure.isOpen_compl
    have hVdense : ∀ i : Fin a, Dense (Q i ∪ (closure Q0)ᶜ) := by
      intro i
      rw [dense_iff_closure_eq]
      rw [Set.eq_univ_iff_forall]
      intro y
      by_cases hy : y ∈ closure Q0
      · exact closure_mono Set.subset_union_left
          (closure_minimal (hQdense i) isClosed_closure hy)
      · exact subset_closure (Or.inr hy)
    have hfin : (Set.range (fun i : Fin a => Q i ∪ (closure Q0)ᶜ)).Finite :=
      Set.finite_range _
    have hdens : Dense (⋂ i : Fin a, (Q i ∪ (closure Q0)ᶜ)) := by
      have h := Set.Finite.dense_sInter hfin
        (fun t ht => by
          obtain ⟨i, rfl⟩ := ht
          exact hVopen i)
        (fun t ht => by
          obtain ⟨i, rfl⟩ := ht
          exact hVdense i)
      rwa [Set.sInter_range] at h
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
    obtain ⟨x, hxD, hxU⟩ := hdens.exists_mem_open (Metric.isOpen_ball.inter hQ0) hUne
    have hxQ0 : x ∈ Q0 := hxU.2
    have hxcl : x ∈ interior (closure Q0) :=
      interior_maximal (subset_closure (s := Q0)) hQ0 hxQ0
    have hxQ : x ∈ ⋂ i : Fin a, Q i := by
      refine Set.mem_iInter.mpr fun i => ?_
      rcases Set.mem_iInter.mp hxD i with h | h
      · exact h
      · exact absurd (interior_subset hxcl) h
    have hxdist : dist x w < min ε δ₀ / 2 := by
      have h1 : x ∈ Metric.ball w (min ε δ₀ / 2) := hxU.1
      rwa [Metric.mem_ball] at h1
    have hxdist' : dist w x < min ε δ₀ / 2 := by rw [dist_comm]; exact hxdist
    exact ⟨x, ⟨hxQ0, hxQ⟩, by
      have h2 := min_le_left ε δ₀
      linarith⟩
  · -- the joint convergence at the points of the intersection
    intro w₀ hw₀ i
    exact hQpoint i w₀ (Set.mem_iInter.mp hw₀.2 i)

end Work.WilCruxN
