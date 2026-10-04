import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.gramInv_jets
import Submission.Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound
import Submission.Work.Diff.EXT.chartData_contDiffOn
import Submission.Work.Diff.EXT.christoffel_bounds_of_core
import Submission.Work.Diff.EXT.ConnCov.aComp_jets_of_chartMat_jets
import Submission.Work.Diff.EXT.ConnCov.norm_iteratedFDeriv_fderiv_apply_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bounds for the chart recursion `aCovArr` from the chart jets of the metric

`Work.Diff.EXT.aCovArr G x₀ t k v i j l` is the chart recursion for the `k`-th covariant derivative
(with respect to the fixed background connection `∇^{G 0}`) of the lowered connection difference
`g_t(∇^{g_t} − ∇^{g_0})`: the `k` direction indices are `v : Fin k → Fin n`, and the three tensor
slots are `i j l`.

The main theorem `aCovArr_bound_of_jets` shows that, on a compact `K` inside the target of the chart
at `x₀` and uniformly for `t ∈ [T/2, T)`, the value of the `k`-th level of the recursion is bounded
as soon as *all* the iterated Fréchet derivatives of the chart matrix `chartMat G x₀ t` are bounded
on `K` (together with the pointwise smoothness of the chart matrix, so that the Leibniz rule
applies).

## Route

* The base level `aCovArr · 0 = aComp` is the chart array of the connection difference
  `aComp G x₀ t y i j l = ∑_p GramM(t)_{lp}(Γ(t)^p_{ij} − Γ(0)^p_{ij})`.  Its jets are controlled by
  the jets of the chart matrix: the Koszul identity `∑_p GramM(t)_{lp}Γ(t)^p_{ij} =
  koszulPair(t)_{jil}` rewrites the first half as a first derivative of `chartMat`, while the second
  half is a Leibniz product of `chartMat` with the *fixed* background Christoffel symbols
  `cGam (G 0)`, whose jets are bounded by `cGam_zero_iteratedFDeriv_bound`.  This is the delegated
  lemma `Work.Diff.EXT.ConnCov.aComp_jets_of_chartMat_jets` (the only place where the metric is
  inverted implicitly, via the Koszul form; note that `GramInv` itself is *not* needed, so the
  uniform ellipticity hypothesis `hell` of the statement is not used below).
* For the higher levels, the recursion is inverted: pointwise,
  `aCovArr · (m+1) = D(aCovArr · m)(cBasis (v 0)) − corrFun`, where `corrFun` is a sum of products
  of background Christoffel symbols with level-`m` components (`CBound.aCovArr_succ_expand`).  Hence
  bounding the jets of order `≤ k − (m+1)` at level `m+1` needs only the jets of order
  `≤ k − m` at level `m`: an induction on the level, in which the available jet order decreases by
  one at each step.  The directional derivative is bounded by
  `Work.Diff.EXT.ConnCov.norm_iteratedFDeriv_fderiv_apply_le` and the correction by the Leibniz rule
  `norm_iteratedFDeriv_mul_le_at_le`; smoothness of every level is
  `Work.Diff.EXT.CBound.aCovArr_contDiffAt`.
-/

set_option maxHeartbeats 2000000

namespace Work.Diff.EXT.ConnCov

section Aux

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- The chart array `aComp` of the lowered connection difference is smooth in the chart coordinate
at every point of the chart target. -/
theorem acbj_aComp_contDiffAt
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j l : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y := by
  have hfun : (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l)
      = fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
          Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') l p
            * (Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i j
                - Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i j) := rfl
  rw [hfun]
  refine ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) fun p _ => ?_
  refine ContDiffAt.mul ?_ ?_
  · exact Work.Diff.EXT.CBound.GramM_contDiffAt_of_target (I := I) (M := M) G x₀ t hy l p
  · exact (Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G t) x₀ hy p i j).sub
      (Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀ hy p i j)

/-- **Jet bound for the Christoffel correction function.**  If every product of a background
Christoffel entry with a component of the level-`m` chart covariant derivative of the connection
difference has `jj`-th jet bounded by `P`, then the `jj`-th jet of `corrFun` is bounded by the
number of summands times `P`. -/
theorem acbj_corrFun_jet_le
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (m : ℕ) (w : Fin m → Fin (Module.finrank ℝ E)) (a i j l : Fin (Module.finrank ℝ E))
    {jj : ℕ} {t : ℝ} {y : E} (hy : y ∈ K) {P : ℝ}
    (hprod : ∀ (p q r : Fin (Module.finrank ℝ E)) (w' : Fin m → Fin (Module.finrank ℝ E))
        (i' j' l' : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ jj (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (Work.Diff.EXT.pt (I := I) x₀ y') p q r
        * Work.Diff.EXT.aCovArr G x₀ t m w' i' j' l' y') y‖ ≤ P) :
    ‖iteratedFDeriv ℝ jj
        (fun y' : E => Work.Diff.EXT.CBound.corrFun G x₀ t m w a i j l y') y‖
      ≤ ((m : ℝ) * (Module.finrank ℝ E : ℝ) + 3 * (Module.finrank ℝ E : ℝ)) * P := by
  classical
  have hcG : ∀ (p q r : Fin (Module.finrank ℝ E)), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p q r) y :=
    fun p q r => Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀
      (hKt hy) p q r
  have hA : ∀ (w' : Fin m → Fin (Module.finrank ℝ E)) (i' j' l' : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y' : E => Work.Diff.EXT.aCovArr G x₀ t m w' i' j' l' y') y :=
    fun w' i' j' l' => Work.Diff.EXT.CBound.aCovArr_contDiffAt (I := I) (M := M) G x₀ K hKt
      m w' i' j' l' t hy
  -- a bound for a single sum over the model basis
  have hsingle : ∀ (ψ : Fin (Module.finrank ℝ E) → E → ℝ),
      (∀ p, ContDiffAt ℝ (⊤ : ℕ∞) (ψ p) y) →
      (∀ p, ‖iteratedFDeriv ℝ jj (ψ p) y‖ ≤ P) →
      ‖iteratedFDeriv ℝ jj (fun y' : E => ∑ p : Fin (Module.finrank ℝ E), ψ p y') y‖
        ≤ (Module.finrank ℝ E : ℝ) * P := by
    intro ψ hψ hψb
    refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_sum_le_at
      (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E)))) (φ := ψ) (x := y) (n := jj)
      (C := P) (fun p _ => hψ p) (fun p _ => hψb p)) ?_
    simp
  -- the four correction sums
  set F1 : E → ℝ := fun y' => ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
      Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p (w r) a
        * Work.Diff.EXT.aCovArr G x₀ t m (Function.update w r p) i j l y' with hF1def
  set F2 : E → ℝ := fun y' => ∑ p : Fin (Module.finrank ℝ E),
      Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i a
        * Work.Diff.EXT.aCovArr G x₀ t m w p j l y' with hF2def
  set F3 : E → ℝ := fun y' => ∑ p : Fin (Module.finrank ℝ E),
      Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p j a
        * Work.Diff.EXT.aCovArr G x₀ t m w i p l y' with hF3def
  set F4 : E → ℝ := fun y' => ∑ p : Fin (Module.finrank ℝ E),
      Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p l a
        * Work.Diff.EXT.aCovArr G x₀ t m w i j p y' with hF4def
  have hF1b : ‖iteratedFDeriv ℝ jj F1 y‖
      ≤ (m : ℝ) * ((Module.finrank ℝ E : ℝ) * P) := by
    rw [hF1def]
    refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_sum_le_at
      (s := (Finset.univ : Finset (Fin m)))
      (φ := fun r y' => ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p (w r) a
          * Work.Diff.EXT.aCovArr G x₀ t m (Function.update w r p) i j l y')
      (x := y) (n := jj) (C := (Module.finrank ℝ E : ℝ) * P) ?_ ?_) ?_
    · intro r _
      exact ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        fun p _ => ContDiffAt.mul (hcG p (w r) a) (hA (Function.update w r p) i j l)
    · intro r _
      exact hsingle (fun p y' => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y')
          p (w r) a * Work.Diff.EXT.aCovArr G x₀ t m (Function.update w r p) i j l y')
        (fun p => ContDiffAt.mul (hcG p (w r) a) (hA (Function.update w r p) i j l))
        (fun p => hprod p (w r) a (Function.update w r p) i j l)
    · simp
  have hF2b : ‖iteratedFDeriv ℝ jj F2 y‖ ≤ (Module.finrank ℝ E : ℝ) * P := by
    rw [hF2def]
    exact hsingle (fun p y' => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p i a
        * Work.Diff.EXT.aCovArr G x₀ t m w p j l y')
      (fun p => ContDiffAt.mul (hcG p i a) (hA w p j l)) (fun p => hprod p i a w p j l)
  have hF3b : ‖iteratedFDeriv ℝ jj F3 y‖ ≤ (Module.finrank ℝ E : ℝ) * P := by
    rw [hF3def]
    exact hsingle (fun p y' => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p j a
        * Work.Diff.EXT.aCovArr G x₀ t m w i p l y')
      (fun p => ContDiffAt.mul (hcG p j a) (hA w i p l)) (fun p => hprod p j a w i p l)
  have hF4b : ‖iteratedFDeriv ℝ jj F4 y‖ ≤ (Module.finrank ℝ E : ℝ) * P := by
    rw [hF4def]
    exact hsingle (fun p y' => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y') p l a
        * Work.Diff.EXT.aCovArr G x₀ t m w i j p y')
      (fun p => ContDiffAt.mul (hcG p l a) (hA w i j p)) (fun p => hprod p l a w i j p)
  have hF12sm : ContDiffAt ℝ (⊤ : ℕ∞) F1 y := by
    rw [hF1def]
    exact ContDiffAt.sum (s := (Finset.univ : Finset (Fin m))) fun r _ =>
      ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
        fun p _ => ContDiffAt.mul (hcG p (w r) a) (hA (Function.update w r p) i j l)
  have hF2sm : ContDiffAt ℝ (⊤ : ℕ∞) F2 y := by
    rw [hF2def]
    exact ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      fun p _ => ContDiffAt.mul (hcG p i a) (hA w p j l)
  have hF3sm : ContDiffAt ℝ (⊤ : ℕ∞) F3 y := by
    rw [hF3def]
    exact ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      fun p _ => ContDiffAt.mul (hcG p j a) (hA w i p l)
  have hF4sm : ContDiffAt ℝ (⊤ : ℕ∞) F4 y := by
    rw [hF4def]
    exact ContDiffAt.sum (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      fun p _ => ContDiffAt.mul (hcG p l a) (hA w i j p)
  have hCf : (fun y' : E => Work.Diff.EXT.CBound.corrFun G x₀ t m w a i j l y')
      = fun y' : E => F1 y' + (F2 y' + (F3 y' + F4 y')) := by
    funext y'
    simp only [Work.Diff.EXT.CBound.corrFun, hF1def, hF2def, hF3def, hF4def]
  rw [hCf]
  have h34 : ‖iteratedFDeriv ℝ jj (fun y' : E => F3 y' + F4 y') y‖
      ≤ (Module.finrank ℝ E : ℝ) * P + (Module.finrank ℝ E : ℝ) * P :=
    Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (f := F3) (g := F4)
      (C := (Module.finrank ℝ E : ℝ) * P) (D := (Module.finrank ℝ E : ℝ) * P)
      hF3sm hF4sm hF3b hF4b
  have h234 : ‖iteratedFDeriv ℝ jj (fun y' : E => F2 y' + (F3 y' + F4 y')) y‖
      ≤ (Module.finrank ℝ E : ℝ) * P
        + ((Module.finrank ℝ E : ℝ) * P + (Module.finrank ℝ E : ℝ) * P) :=
    Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (f := F2)
      (g := fun y' : E => F3 y' + F4 y')
      (C := (Module.finrank ℝ E : ℝ) * P)
      (D := (Module.finrank ℝ E : ℝ) * P + (Module.finrank ℝ E : ℝ) * P)
      hF2sm (hF3sm.add hF4sm) hF2b h34
  have hall : ‖iteratedFDeriv ℝ jj (fun y' : E => F1 y' + (F2 y' + (F3 y' + F4 y'))) y‖
      ≤ (m : ℝ) * ((Module.finrank ℝ E : ℝ) * P)
        + ((Module.finrank ℝ E : ℝ) * P
          + ((Module.finrank ℝ E : ℝ) * P + (Module.finrank ℝ E : ℝ) * P)) :=
    Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (f := F1)
      (g := fun y' : E => F2 y' + (F3 y' + F4 y'))
      (C := (m : ℝ) * ((Module.finrank ℝ E : ℝ) * P))
      (D := (Module.finrank ℝ E : ℝ) * P
        + ((Module.finrank ℝ E : ℝ) * P + (Module.finrank ℝ E : ℝ) * P))
      hF12sm (hF2sm.add (hF3sm.add hF4sm)) hF1b h234
  refine le_trans hall (le_of_eq ?_)
  ring

end Aux

theorem aCovArr_bound_of_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (x₀ : M) (K : Set E) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hjets : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y‖
        ≤ C)
    (hell : ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        δ * ∑ i, (v i) ^ 2
          ≤ ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y i j)
    (hsm : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y) :
    ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      ∀ (v : Fin k → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
        |Work.Diff.EXT.aCovArr G x₀ t k v i j l y| ≤ Ck := by
  classical
  intro k
  -- uniform jet bound for the chart array of the connection difference
  have hCAall : ∃ C : ℝ, 0 ≤ C ∧ ∀ jj ≤ k, ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ jj
          (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y‖ ≤ C :=
    Work.Diff.EXT.exists_uniform_bound_of_le
      (P := fun jj C => ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
        ∀ (i j l : Fin (Module.finrank ℝ E)),
          ‖iteratedFDeriv ℝ jj
            (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y‖ ≤ C)
      (fun jj C C' h hle t ht y hy i j l => le_trans (h t ht y hy i j l) hle) k
      (fun jj _ => aComp_jets_of_chartMat_jets (I := I) (M := M) G T x₀ K hK hKt hjets hsm jj)
  obtain ⟨CA, hCA0, hCA⟩ := hCAall
  -- uniform jet bound for the background Christoffel symbols
  have hCΓall : ∃ C : ℝ, 0 ≤ C ∧ ∀ jj ≤ k, ∀ y ∈ K,
      ∀ (p q r : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ jj (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (Work.Diff.EXT.pt (I := I) x₀ y') p q r) y‖ ≤ C :=
    Work.Diff.EXT.exists_uniform_bound_of_le
      (P := fun jj C => ∀ y ∈ K, ∀ (p q r : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ jj (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (Work.Diff.EXT.pt (I := I) x₀ y') p q r) y‖ ≤ C)
      (fun jj C C' h hle y hy p q r => le_trans (h y hy p q r) hle) k
      (fun jj _ => by
        obtain ⟨C, hC0, hC⟩ :=
          Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound (I := I) (M := M) G x₀ K hK hKt jj
        exact ⟨C, hC0, fun y hy p q r => hC y hy q r p⟩)
  obtain ⟨CΓ, hCΓ0, hCΓ⟩ := hCΓall
  -- the basis expansion constant
  set Kb : ℝ := max 1 (∑ a : Fin (Module.finrank ℝ E), ‖Module.finBasis ℝ E a‖) with hKbdef
  have hKb0 : 0 ≤ Kb := le_trans zero_le_one (le_max_left _ _)
  have hKbnorm : ∀ a : Fin (Module.finrank ℝ E), ‖Module.finBasis ℝ E a‖ ≤ Kb := fun a =>
    le_trans (Finset.single_le_sum
      (f := fun b : Fin (Module.finrank ℝ E) => ‖Module.finBasis ℝ E b‖)
      (fun b _ => norm_nonneg _) (Finset.mem_univ a)) (le_max_right _ _)
  -- the induction on the level
  have key : ∀ m : ℕ, m ≤ k → ∃ C : ℝ, 0 ≤ C ∧
      (∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K, ∀ jj : ℕ, jj ≤ k - m →
        ∀ (v : Fin m → Fin (Module.finrank ℝ E)) (a b c : Fin (Module.finrank ℝ E)),
          ‖iteratedFDeriv ℝ jj
            (fun y' : E => Work.Diff.EXT.aCovArr G x₀ t m v a b c y') y‖ ≤ C) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨CA, hCA0, ?_⟩
      intro t ht y hy jj hj v a b c
      simpa only [Work.Diff.EXT.aCovArr] using hCA jj hj t ht y hy a b c
    | succ m ih =>
      intro hmk
      obtain ⟨Cm, hCm0, hCm⟩ := ih (by omega : m ≤ k)
      set B : ℝ := max Cm CΓ with hBdef
      have hB0 : 0 ≤ B := le_trans hCm0 (le_max_left _ _)
      have hCmB : Cm ≤ B := le_max_left _ _
      have hCΓB : CΓ ≤ B := le_max_right _ _
      set P : ℝ := (2 : ℝ) ^ k * B * B with hPdef
      set Ns : ℝ := (m : ℝ) * (Module.finrank ℝ E : ℝ) + 3 * (Module.finrank ℝ E : ℝ)
        with hNsdef
      set Cb : ℝ := max (Kb * Cm) (Ns * P) with hCbdef
      have hCb0 : 0 ≤ Cb := le_trans (by positivity : (0 : ℝ) ≤ Kb * Cm) (le_max_left _ _)
      have hKbCm : Kb * Cm ≤ Cb := le_max_left _ _
      have hNsP : Ns * P ≤ Cb := le_max_right _ _
      refine ⟨2 * Cb, by positivity, ?_⟩
      intro t ht y hy jj hj v a b c
      have hjjSm : jj ≤ k - m := by omega
      have hjj1 : jj + 1 ≤ k - m := by omega
      -- the two pieces of the recursion
      set G1 : E → ℝ := fun y' => fderiv ℝ (fun y'' : E =>
          Work.Diff.EXT.aCovArr G x₀ t m (fun s : Fin m => v s.succ) a b c y'')
          y' (Work.Diff.GE.cBasis (E := E) (v 0)) with hG1def
      set G2 : E → ℝ := fun y' => Work.Diff.EXT.CBound.corrFun G x₀ t m
          (fun s : Fin m => v s.succ) (v 0) a b c y' with hG2def
      have hsplit : (fun y' : E => Work.Diff.EXT.aCovArr G x₀ t (m + 1) v a b c y')
          = fun y' : E => G1 y' + (fun z : E => -G2 z) y' := by
        funext y'
        rw [Work.Diff.EXT.CBound.aCovArr_succ_expand (I := I) (M := M) G x₀ t m v a b c y']
        simp only [hG1def, hG2def, Work.Diff.EXT.CBound.corrFun]
        ring
      have hG1sm : ContDiffAt ℝ (⊤ : ℕ∞) G1 y := by
        rw [hG1def]
        exact Work.Diff.EXT.CBound.contDiffAt_fderiv_apply'
          (Work.Diff.EXT.CBound.aCovArr_contDiffAt (I := I) (M := M) G x₀ K hKt m
            (fun s : Fin m => v s.succ) a b c t hy)
      have hG2sm : ContDiffAt ℝ (⊤ : ℕ∞) G2 y := by
        rw [hG2def]
        exact Work.Diff.EXT.CBound.corrFun_contDiffAt (I := I) (M := M) G x₀ K hKt
          (m := m) (w := fun s : Fin m => v s.succ) (a := v 0) (i := a) (j := b) (l := c)
          (fun w' i' j' l' t' => Work.Diff.EXT.CBound.aCovArr_contDiffAt (I := I) (M := M) G x₀ K
            hKt m w' i' j' l' t') t hy
      have hG1b : ‖iteratedFDeriv ℝ jj G1 y‖ ≤ Kb * Cm := by
        rw [hG1def]
        refine le_trans (norm_iteratedFDeriv_fderiv_apply_le
          (ψ := fun y'' : E => Work.Diff.EXT.aCovArr G x₀ t m
            (fun s : Fin m => v s.succ) a b c y'')
          (y := y) (ζ := Work.Diff.GE.cBasis (E := E) (v 0)) (j := jj) ?_) ?_
        · exact Work.Diff.EXT.CBound.aCovArr_contDiffAt (I := I) (M := M) G x₀ K hKt m
            (fun s : Fin m => v s.succ) a b c t hy
        · exact mul_le_mul (hKbnorm (v 0))
            (hCm t ht y hy (jj + 1) hjj1 (fun s : Fin m => v s.succ) a b c)
            (norm_nonneg _) hKb0
      have hG2b : ‖iteratedFDeriv ℝ jj G2 y‖ ≤ Ns * P := by
        rw [hG2def]
        have hprod : ∀ (p q r : Fin (Module.finrank ℝ E))
            (w' : Fin m → Fin (Module.finrank ℝ E))
            (i' j' l' : Fin (Module.finrank ℝ E)),
            ‖iteratedFDeriv ℝ jj (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
              (Work.Diff.EXT.pt (I := I) x₀ y') p q r
              * Work.Diff.EXT.aCovArr G x₀ t m w' i' j' l' y') y‖ ≤ P := by
          intro p q r w' i' j' l'
          refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_mul_le_at_le (k := jj) (m := jj)
            (B := B) le_rfl ?_ ?_ hB0 ?_ ?_) ?_
          · exact Work.Diff.EXT.CBound.cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀
              (hKt hy) p q r
          · exact Work.Diff.EXT.CBound.aCovArr_contDiffAt (I := I) (M := M) G x₀ K hKt m
              w' i' j' l' t hy
          · intro i hi
            exact le_trans (hCΓ i (by omega) y hy p q r) hCΓB
          · intro i hi
            exact le_trans (hCm t ht y hy i (by omega) w' i' j' l') hCmB
          · rw [hPdef]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) hB0)
              (by positivity)
        refine le_trans (acbj_corrFun_jet_le (I := I) (M := M) G x₀ K hKt m
          (fun s : Fin m => v s.succ) (v 0) a b c hy hprod) ?_
        rw [hNsdef]
      have hGneg : ‖iteratedFDeriv ℝ jj (fun z : E => -G2 z) y‖ ≤ Ns * P := by
        have h1 : (fun z : E => -G2 z) = -G2 := rfl
        rw [h1, iteratedFDeriv_neg]
        simpa using hG2b
      rw [hsplit]
      refine le_trans (Work.Diff.EXT.norm_iteratedFDeriv_add_le_at₂ (f := G1)
        (g := fun z : E => -G2 z) (C := Kb * Cm) (D := Ns * P) hG1sm hG2sm.neg hG1b hGneg) ?_
      linarith [hKbCm, hNsP]
  obtain ⟨Ck, hCk0, hCk⟩ := key k le_rfl
  refine ⟨Ck, hCk0, fun t ht y hy v i j l => ?_⟩
  have h := hCk t ht y hy 0 (Nat.zero_le _) v i j l
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h

end Work.Diff.EXT.ConnCov
