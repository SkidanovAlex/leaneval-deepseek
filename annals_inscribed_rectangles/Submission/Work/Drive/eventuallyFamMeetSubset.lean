import Mathlib
import Submission.Work.Drive.famMeetDefs
import Submission.Work.Drive.hVStability

/-!
# The meet condition of a smooth family is *eventually* contained in any open set

The parity engine `Work.Drive.odd_ncard_famMeet_iff` is fed a **family** `t ↦ (Lf t, N t)` of
(loop, chain) pairs on the five-box, and one of its inputs is an open condition (genericity /
`hV`-type avoidance) that is verified at the base parameter `0` *for the whole box*: every meet
point of the base pair inside `unitBox 4` lies in an open `U ⊆ ℝ⁵`.  This file proves that this
input is *stable*: it holds for all `t` in a neighbourhood of `0`.

The mathematical content is the classical tube argument, and the whole point is that it is *cheap*:
the meet relation

`Z := {(t, y) | y ∈ unitBox 4 ∧ famLoop (Lf t) y = famChain (N t) y} ⊆ ℝ^m × ℝ⁵`

is **closed** (a closed box intersected with the preimage of the diagonal under the jointly
continuous comparison map — this is where `T2Space M` is used), the parameter space is *not*
compact but the fibre `unitBox 4` *is*, so `Work.Drive.exists_prod_nhds_subset_of_isCompact_set`
(from `hVStability`, the tube lemma for a closed relation over a compact parameter set and a
compact fibre) turns the hypothesis on the slice over `{0}` into a product neighbourhood
`V ×ˢ unitBox 4` of that slice with `Z ∩ (V ×ˢ unitBox 4) ⊆ {y ∈ U}`.

Nothing about `M` beyond `T2Space` enters, and no smoothness is used: only joint continuity of the
two comparison maps.  Consequently the lemma applies verbatim to every "avoid the bad set" input of
the counting engine (genericity, `hV`, absence of boundary meets), and lets the fleet spend its
perturbations away from the base pair without re-verifying the base conditions.
-/

namespace Work.Drive

open Set Filter

theorem eventuallyFamMeetSubset {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    (Lf : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 2) → M)
    (hLf : Continuous (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
      Lf q.1 q.2))
    (N : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 4) → M)
    (hN : Continuous (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 4) =>
      N q.1 q.2))
    {U : Set (EuclideanSpace ℝ (Fin 5))} (hU : IsOpen U)
    (hbase : ∀ y : EuclideanSpace ℝ (Fin 5), y ∈ Submission.Drive.unitBox 4 →
      Work.Drive.famLoop (Lf 0) y = Work.Drive.famChain (N 0) y → y ∈ U) :
    ∀ᶠ t in nhds (0 : EuclideanSpace ℝ (Fin m)),
      ∀ y : EuclideanSpace ℝ (Fin 5), y ∈ Submission.Drive.unitBox 4 →
        Work.Drive.famLoop (Lf t) y = Work.Drive.famChain (N t) y → y ∈ U := by
  -- the comparison maps on the product, jointly continuous
  have hloopCont : Continuous (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
      Work.Drive.famLoop (Lf p.1) p.2) := by
    have hg : Continuous (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
        (p.1, Work.Drive.mk2 (p.2 0) (p.2 1))) := by
      simp only [Work.Drive.mk2]
      fun_prop
    simpa only [Function.comp_def, Work.Drive.famLoop] using hLf.comp hg
  have hchainCont : Continuous (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
      Work.Drive.famChain (N p.1) p.2) := by
    have hg : Continuous (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
        (p.1, Work.Drive.famPt (p.2 0) (Work.Drive.famT3 (p.2 2) (p.2 3) (p.2 4)))) := by
      simp only [Work.Drive.famPt, Work.Drive.famT3]
      fun_prop
    simpa only [Function.comp_def, Work.Drive.famChain] using hN.comp hg
  -- the meet relation inside the box is closed
  have hZ : IsClosed {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) |
      p.2 ∈ Submission.Drive.unitBox 4 ∧
        Work.Drive.famLoop (Lf p.1) p.2 = Work.Drive.famChain (N p.1) p.2} := by
    have h1 : IsClosed {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) |
        p.2 ∈ Submission.Drive.unitBox 4} :=
      (Work.Drive.isClosed_unitBox 4).preimage continuous_snd
    have h2 : IsClosed {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) |
        Work.Drive.famLoop (Lf p.1) p.2 = Work.Drive.famChain (N p.1) p.2} :=
      isClosed_eq hloopCont hchainCont
    exact h1.inter h2
  -- the target condition is open in the product
  have hG : IsOpen {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) | p.2 ∈ U} :=
    hU.preimage continuous_snd
  -- hypothesis: the slice over the base parameter is contained in it
  have hsub : {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) |
        p.2 ∈ Submission.Drive.unitBox 4 ∧
          Work.Drive.famLoop (Lf p.1) p.2 = Work.Drive.famChain (N p.1) p.2} ∩
        ({0} ×ˢ Submission.Drive.unitBox 4) ⊆
      {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) | p.2 ∈ U} := by
    rintro p ⟨⟨hbox, hmeet⟩, hp2⟩
    obtain ⟨h0, hybox⟩ := hp2
    have h0' : p.1 = 0 := by simpa using h0
    rw [h0'] at hmeet
    exact hbase p.2 hybox hmeet
  -- the tube lemma, with the compact parameter set `{0}` and the compact fibre `unitBox 4`
  obtain ⟨V, h0V, hVopen, hVsub⟩ :=
    Work.Drive.exists_prod_nhds_subset_of_isCompact_set hZ hG
      (isCompact_singleton (x := (0 : EuclideanSpace ℝ (Fin m))))
      (Work.Drive.isCompact_unitBox 4) hsub
  filter_upwards [hVopen.mem_nhds (h0V (Set.mem_singleton 0))] with t ht
  intro y hybox hmeet
  have hZmem : (t, y) ∈ {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) |
      p.2 ∈ Submission.Drive.unitBox 4 ∧
        Work.Drive.famLoop (Lf p.1) p.2 = Work.Drive.famChain (N p.1) p.2} :=
    ⟨hybox, hmeet⟩
  have hVmem : (t, y) ∈ V ×ˢ Submission.Drive.unitBox 4 := ⟨ht, hybox⟩
  exact hVsub ⟨hZmem, hVmem⟩

end Work.Drive
