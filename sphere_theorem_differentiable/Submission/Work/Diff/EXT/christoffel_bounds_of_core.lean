import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.EXT.chartRic_partial_jet
import Submission.Work.Diff.EXT.norm_iteratedFDeriv_le_basisSum
import Submission.Work.Diff.EXT.chartMat_det_ne_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric


/-!
# `Work.Diff.EXT.christoffel_bounds_of_core`

The chart Christoffel symbols of a family of metrics `G`, read through the chart at `x₀`, have
uniformly bounded iterated Fréchet derivatives on `K`, uniformly on a half-open time interval,
as soon as:

* the *chart recursion* `aCovArr` of the background covariant derivatives of the connection
  difference `∇^{G(t)} - ∇^{G(0)}` is bounded on `K` (`hcore`),
* the inverse chart Gram matrices `GramInv` of the flow have bounded jets (`hGInv`),
* the chart Christoffel symbols of the *initial* metric `G 0` have bounded jets (`hcGam0`).

## Route

The key point is the *exact* algebraic identity

`Γ(G t)^l_{ij} = Γ(G 0)^l_{ij} + ∑_k γ^{lk} · a_{ijk}`,

where `a_{ijk} = ∑_m g_{km}(Γ(G t)^m_{ij} - Γ(G 0)^m_{ij})` is the *definition* of the chart
component `aComp = aCovArr ... 0` of the lowered connection difference and `γ = GramInv`,
`g = GramM`; it holds because `γ` is a left inverse of `g`.  This identity is the reason the
result does not require the chart matrices `GramM` themselves to be bounded (only `GramInv` is),
which is essential: a nearly singular `γ` has a huge inverse `g`, and the Koszul formula for
`Γ(G t)` in terms of `∂ GramM` would give nothing.

The chart recursion `aCovArr` is then used through its *definitional* unfolding

`fderiv (aCovArr G x₀ t m w i j l) y v = aCovArr G x₀ t (m+1) (cons a w) i j l y + corr`,

which expresses the *first* Fréchet derivative of the `m`-th chart covariant derivative through
the `(m+1)`-st one plus a correction that is a *product* of background Christoffel symbols with
lower order terms.  Iterating this gives a double induction:

* `JBu` (jet bounds up to order `k` plus smoothness) for `aCovArr` at order `k` and level `m`
  follows from the same statement at order `k` and levels `m` and `m+1` (the Leibniz rule for
  products and the jet decomposition lemma
  `jet_succ_le_fderiv_basis` do the bookkeeping);
* the smoothness part is a separate induction on `m`, using that `GramM`, `GramInv` and the
  Christoffel symbols are smooth functions of the chart coordinate on the chart target
  (the latter via `cGam_zero_iteratedFDeriv_bound_aux2`, the matrix inverse via Cramer's rule).

The base case `k = 0` at level `m` is exactly `hcore` at order `m`.
-/

namespace Work.Diff.EXT

/-! ### The main development -/

namespace CBound

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ### Local jet estimates (proved here so that this file is self-contained) -/

/-- Evaluation of a `CLM`-valued family at a fixed vector commutes with `iteratedFDeriv`. -/
theorem clm_apply_iteratedFDeriv {c : E → (E →L[ℝ] ℝ)} {x : E} {i : ℕ}
    (hc : ContDiffAt ℝ (⊤ : ℕ∞) c x) (u : E) (m : Fin i → E) :
    (iteratedFDeriv ℝ i (fun y => c y u) x) m = ((iteratedFDeriv ℝ i c x) m) u := by
  have key : iteratedFDeriv ℝ i (fun y => c y u) x
      = (ContinuousLinearMap.apply ℝ ℝ u).compContinuousMultilinearMap (iteratedFDeriv ℝ i c x) := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply]
      using (ContinuousLinearMap.apply ℝ ℝ u).iteratedFDeriv_comp_left (f := c) hc (i := i) (by simp)
  rw [key]
  simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearMap.apply_apply]

/-- A product of `k` nonnegative reals each `≤ S` is at most `S ^ k`. -/
private lemma prod_le_pow_card_of_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ) {S : ℝ}
    (h0 : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ S) :
    ∏ i : ι, f i ≤ S ^ Fintype.card ι := by
  classical
  have key : ∀ (t : Finset ι), (∀ i ∈ t, 0 ≤ f i) → (∀ i ∈ t, f i ≤ S) →
      ∏ i ∈ t, f i ≤ S ^ t.card := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _ _; simp
    | insert a t ha ih =>
        intro h0' h'
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
        have hfa : f a ≤ S := h' a (Finset.mem_insert_self a t)
        have ht0 : 0 ≤ ∏ i ∈ t, f i :=
          Finset.prod_nonneg (fun i hi => h0' i (Finset.mem_insert_of_mem hi))
        have hS0 : 0 ≤ S := le_trans (h0 a) hfa
        have ih' := ih (fun i hi => h0' i (Finset.mem_insert_of_mem hi))
          (fun i hi => h' i (Finset.mem_insert_of_mem hi))
        calc f a * ∏ i ∈ t, f i ≤ S * S ^ t.card := mul_le_mul hfa ih' ht0 hS0
          _ = S ^ t.card * S := by ring
  simpa only [Finset.card_univ] using key Finset.univ (fun i _ => h0 i) (fun i _ => h i)

/-- **Leibniz bound for the iterated Fréchet derivative of a product, at a point.** -/
theorem jet_mul_at_le {f g : E → ℝ} {x : E} {N : ℕ} {A B : ℕ → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (hA0 : ∀ i, 0 ≤ A i) (hB0 : ∀ i, 0 ≤ B i)
    (hA : ∀ i ≤ N, ‖iteratedFDeriv ℝ i f x‖ ≤ A i)
    (hB : ∀ i ≤ N, ‖iteratedFDeriv ℝ i g x‖ ≤ B i) :
    ‖iteratedFDeriv ℝ N (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) * A i * B (N - i) := by
  classical
  have hlev : ((N : ℕ) : ℕ∞ω) ≤ (⊤ : ℕ∞) := by simp
  obtain ⟨u₁, hu₁⟩ := ContDiffWithinAt.contDiffOn (m := (N : ℕ)) hlev (by intro h; simp at h)
    (hf : ContDiffWithinAt ℝ (⊤ : ℕ∞) f Set.univ x)
  obtain ⟨hu₁mem, hu₁sub, hu₁cd⟩ := hu₁
  obtain ⟨u₂, hu₂⟩ := ContDiffWithinAt.contDiffOn (m := (N : ℕ)) hlev (by intro h; simp at h)
    (hg : ContDiffWithinAt ℝ (⊤ : ℕ∞) g Set.univ x)
  obtain ⟨hu₂mem, hu₂sub, hu₂cd⟩ := hu₂
  have hu₁mem' : u₁ ∈ 𝓝 x := by simpa using hu₁mem
  have hu₂mem' : u₂ ∈ 𝓝 x := by simpa using hu₂mem
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.mp hu₁mem'
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.mem_nhds_iff.mp hu₂mem'
  have hso : IsOpen (Metric.ball x ε₁ ∩ Metric.ball x ε₂) := isOpen_ball.inter isOpen_ball
  have hsm : x ∈ Metric.ball x ε₁ ∩ Metric.ball x ε₂ :=
    ⟨mem_ball_self hε₁, mem_ball_self hε₂⟩
  have hcd₁ : ContDiffOn ℝ (N : ℕ) f (Metric.ball x ε₁ ∩ Metric.ball x ε₂) :=
    hu₁cd.mono (Set.inter_subset_left.trans hball₁)
  have hcd₂ : ContDiffOn ℝ (N : ℕ) g (Metric.ball x ε₁ ∩ Metric.ball x ε₂) :=
    hu₂cd.mono (Set.inter_subset_right.trans hball₂)
  have hmain := norm_iteratedFDerivWithin_mul_le hcd₁ hcd₂ hso.uniqueDiffOn hsm (n := N) le_rfl
  rw [iteratedFDerivWithin_of_isOpen N hso hsm] at hmain
  refine hmain.trans (Finset.sum_le_sum (fun i hi => ?_))
  have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hN : N - i ≤ N := Nat.sub_le N i
  rw [iteratedFDerivWithin_of_isOpen i hso hsm,
    iteratedFDerivWithin_of_isOpen (N - i) hso hsm]
  have h1 : (N.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ ≤ (N.choose i : ℝ) * A i :=
    mul_le_mul_of_nonneg_left (hA i hiN) (Nat.cast_nonneg _)
  calc (N.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (N - i) g x‖
      ≤ (N.choose i : ℝ) * A i * ‖iteratedFDeriv ℝ (N - i) g x‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (N.choose i : ℝ) * A i * B (N - i) :=
        mul_le_mul_of_nonneg_left (hB (N - i) hN) (mul_nonneg (Nat.cast_nonneg _) (hA0 i))

/-- **Smoothness of a directional derivative.** -/
theorem contDiffAt_fderiv_apply' {f : E → ℝ} {x v : E}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ f y v) x := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ f) x :=
    hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun L : E →L[ℝ] ℝ => L v) (fderiv ℝ f x) :=
    (ContinuousLinearMap.apply ℝ ℝ v).contDiff.contDiffAt
  have h := h2.comp x h1
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h

/-- **Uniform jet bound from directional `fderiv` data.** -/
theorem jet_succ_le_fderiv_basis (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {A : E → ℝ} {y : E}, ContDiffAt ℝ (⊤ : ℕ∞) A y →
      ∀ {B C : Fin (Module.finrank ℝ E) → E → ℝ},
      (∀ (a : Fin (Module.finrank ℝ E)) (y' : E),
        fderiv ℝ A y' (Module.finBasis ℝ E a) = B a y' + C a y') →
      (∀ a, ContDiffAt ℝ (⊤ : ℕ∞) (B a) y) → (∀ a, ContDiffAt ℝ (⊤ : ℕ∞) (C a) y) →
      ‖iteratedFDeriv ℝ (k + 1) A y‖ ≤
        D * ∑ a, (‖iteratedFDeriv ℝ k (B a) y‖ + ‖iteratedFDeriv ℝ k (C a) y‖) := by
  classical
  obtain ⟨Cb, hCb0, hCb⟩ := norm_iteratedFDeriv_le_basisSum (E := E) (F := ℝ) (k + 1)
  set S : ℝ := ∑ a : Fin (Module.finrank ℝ E), ‖Module.finBasis ℝ E a‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  have hSa : ∀ a : Fin (Module.finrank ℝ E), ‖Module.finBasis ℝ E a‖ ≤ S := fun a =>
    Finset.single_le_sum (f := fun b => ‖Module.finBasis ℝ E b‖)
      (fun b _ => norm_nonneg _) (Finset.mem_univ a)
  refine ⟨Cb * ((Fintype.card (Fin (k + 1) → Fin (Module.finrank ℝ E)) : ℝ) * S ^ k),
    mul_nonneg hCb0 (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hS0 _)), ?_⟩
  intro A y hA B C hid hB hC
  set T : ℝ := ∑ a, (‖iteratedFDeriv ℝ k (B a) y‖ + ‖iteratedFDeriv ℝ k (C a) y‖) with hT
  have hTa : ∀ a : Fin (Module.finrank ℝ E),
      ‖iteratedFDeriv ℝ k (B a) y‖ + ‖iteratedFDeriv ℝ k (C a) y‖ ≤ T := fun a =>
    Finset.single_le_sum (f := fun b =>
      ‖iteratedFDeriv ℝ k (B b) y‖ + ‖iteratedFDeriv ℝ k (C b) y‖)
      (fun b _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.mem_univ a)
  have hderiv : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' => fderiv ℝ A y') y :=
    hA.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have hterm : ∀ ι : Fin (k + 1) → Fin (Module.finrank ℝ E),
      ‖iteratedFDeriv ℝ (k + 1) A y (fun s => Module.finBasis ℝ E (ι s))‖
        ≤ S ^ k * (‖iteratedFDeriv ℝ k (B (ι (Fin.last k))) y‖
            + ‖iteratedFDeriv ℝ k (C (ι (Fin.last k))) y‖) := by
    intro ι
    have h1 : iteratedFDeriv ℝ (k + 1) A y (fun s => Module.finBasis ℝ E (ι s))
        = ((iteratedFDeriv ℝ k (fun y' => fderiv ℝ A y') y)
            (Fin.init (fun s => Module.finBasis ℝ E (ι s))))
          ((fun s => Module.finBasis ℝ E (ι s)) (Fin.last k)) :=
      iteratedFDeriv_succ_apply_right (𝕜 := ℝ) (f := A) (x := y) (n := k)
        (m := fun s => Module.finBasis ℝ E (ι s))
    have h2 : ((iteratedFDeriv ℝ k (fun y' => fderiv ℝ A y') y)
            (Fin.init (fun s => Module.finBasis ℝ E (ι s))))
          ((fun s => Module.finBasis ℝ E (ι s)) (Fin.last k))
        = (iteratedFDeriv ℝ k (fun y' =>
            fderiv ℝ A y' ((fun s => Module.finBasis ℝ E (ι s)) (Fin.last k))) y)
          (Fin.init (fun s => Module.finBasis ℝ E (ι s))) :=
      (clm_apply_iteratedFDeriv (E := E) (i := k) hderiv
        ((fun s => Module.finBasis ℝ E (ι s)) (Fin.last k))
        (Fin.init (fun s => Module.finBasis ℝ E (ι s)))).symm
    have h3 : iteratedFDeriv ℝ k (fun y' =>
            fderiv ℝ A y' ((fun s => Module.finBasis ℝ E (ι s)) (Fin.last k))) y
        = iteratedFDeriv ℝ k (fun y' =>
            B (ι (Fin.last k)) y' + C (ι (Fin.last k)) y') y := by
      have h := iteratedFDerivWithin_congr (𝕜 := ℝ) (s := Set.univ)
        (f := fun y' : E => B (ι (Fin.last k)) y' + C (ι (Fin.last k)) y')
        (f₁ := fun y' : E =>
          fderiv ℝ A y' ((fun s => Module.finBasis ℝ E (ι s)) (Fin.last k)))
        (fun y' _ => hid (ι (Fin.last k)) y') (Set.mem_univ y) k
      simpa only [iteratedFDerivWithin_univ] using h
    have h4 : iteratedFDeriv ℝ k (fun y' =>
            B (ι (Fin.last k)) y' + C (ι (Fin.last k)) y') y
        = iteratedFDeriv ℝ k (B (ι (Fin.last k))) y
          + iteratedFDeriv ℝ k (C (ι (Fin.last k))) y :=
      iteratedFDeriv_add_apply ((hB (ι (Fin.last k))).of_le (by simp))
        ((hC (ι (Fin.last k))).of_le (by simp))
    have hprod : ∏ s : Fin k, ‖(Fin.init (fun s => Module.finBasis ℝ E (ι s))) s‖ ≤ S ^ k := by
      have hle : ∀ s : Fin k, ‖(Fin.init (fun s' => Module.finBasis ℝ E (ι s'))) s‖ ≤ S := by
        intro s
        refine le_trans (le_of_eq ?_) (hSa (ι s.castSucc))
        simp only [Fin.init]
      simpa only [Finset.card_univ, Fintype.card_fin] using
        prod_le_pow_card_of_nonneg
          (f := fun s : Fin k => ‖(Fin.init (fun s' => Module.finBasis ℝ E (ι s'))) s‖)
          (S := S) (fun s => norm_nonneg _) hle
    rw [h1, h2, h3, h4]
    refine le_trans (norm_add_le _ _) ?_
    have hb : ‖(iteratedFDeriv ℝ k (B (ι (Fin.last k))) y)
        (Fin.init (fun s => Module.finBasis ℝ E (ι s)))‖
        ≤ ‖iteratedFDeriv ℝ k (B (ι (Fin.last k))) y‖ * S ^ k :=
      le_trans (ContinuousMultilinearMap.le_opNorm _ _)
        (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
    have hc : ‖(iteratedFDeriv ℝ k (C (ι (Fin.last k))) y)
        (Fin.init (fun s => Module.finBasis ℝ E (ι s)))‖
        ≤ ‖iteratedFDeriv ℝ k (C (ι (Fin.last k))) y‖ * S ^ k :=
      le_trans (ContinuousMultilinearMap.le_opNorm _ _)
        (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
    calc ‖(iteratedFDeriv ℝ k (B (ι (Fin.last k))) y)
            (Fin.init (fun s => Module.finBasis ℝ E (ι s)))‖
          + ‖(iteratedFDeriv ℝ k (C (ι (Fin.last k))) y)
            (Fin.init (fun s => Module.finBasis ℝ E (ι s)))‖
        ≤ ‖iteratedFDeriv ℝ k (B (ι (Fin.last k))) y‖ * S ^ k
          + ‖iteratedFDeriv ℝ k (C (ι (Fin.last k))) y‖ * S ^ k := add_le_add hb hc
      _ = S ^ k * (‖iteratedFDeriv ℝ k (B (ι (Fin.last k))) y‖
            + ‖iteratedFDeriv ℝ k (C (ι (Fin.last k))) y‖) := by ring
  refine (hCb A y).trans ?_
  have hstep : (∑ ι : Fin (k + 1) → Fin (Module.finrank ℝ E),
        ‖iteratedFDeriv ℝ (k + 1) A y (fun s => Module.finBasis ℝ E (ι s))‖)
      ≤ (Fintype.card (Fin (k + 1) → Fin (Module.finrank ℝ E)) : ℝ) * (S ^ k * T) := by
    refine le_trans (Finset.sum_le_sum (fun ι _ => hterm ι)) ?_
    refine le_trans (Finset.sum_le_sum (fun ι _ =>
      mul_le_mul_of_nonneg_left (hTa (ι (Fin.last k))) (pow_nonneg hS0 k))) ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact le_trans (mul_le_mul_of_nonneg_left hstep hCb0) (le_of_eq (by ring))

/-- `JBu σ T K k A` bundles the smoothness of the family `A` at the points of `K` with the
existence of uniform bounds for all iterated Fréchet derivatives of order `≤ k` on `K`. -/
def JBu (σ T : ℝ) (K : Set E) (k : ℕ) (A : ℝ → E → ℝ) : Prop :=
  (∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ContDiffAt ℝ (⊤ : ℕ∞) (A t) y) ∧
  ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
    ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ i ≤ k, ‖iteratedFDeriv ℝ i (A t) y‖ ≤ B i

namespace JBu

variable {σ T : ℝ} {K : Set E} {k : ℕ} {A A' : ℝ → E → ℝ}

lemma congr (h : ∀ t y, A t y = A' t y) (hA : JBu σ T K k A) : JBu σ T K k A' := by
  obtain ⟨hsm, B, hB0, hB⟩ := hA
  refine ⟨fun t ht y hy => (hsm t ht y hy).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y' => (h t y').symm)), B, hB0, ?_⟩
  intro t ht y hy i hi
  rw [show A' t = A t from funext (fun y' => (h t y').symm)]
  exact hB t ht y hy i hi

/-- Congruence of `JBu` for families that agree on the chart target. -/
lemma congrOn {x₀ : M} (hKt : K ⊆ (extChartAt I x₀).target)
    (h : ∀ t, ∀ y ∈ (extChartAt I x₀).target, A t y = A' t y) (hA : JBu σ T K k A) :
    JBu σ T K k A' := by
  obtain ⟨hsm, B, hB0, hB⟩ := hA
  have hopen := isOpen_extChartAt_target (I := I) x₀
  refine ⟨fun t ht y hy => (hsm t ht y hy).congr_of_eventuallyEq
    (Filter.eventually_of_mem (hopen.mem_nhds (hKt hy))
      (fun y' hy' => (h t y' hy').symm)), B, hB0, ?_⟩
  intro t ht y hy i hi
  have h1 : iteratedFDeriv ℝ i (A' t) y
      = iteratedFDerivWithin ℝ i (A' t) (extChartAt I x₀).target y :=
    (iteratedFDerivWithin_of_isOpen i hopen (hKt hy)).symm
  have h2 : iteratedFDerivWithin ℝ i (A' t) (extChartAt I x₀).target y
      = iteratedFDerivWithin ℝ i (A t) (extChartAt I x₀).target y :=
    iteratedFDerivWithin_congr (fun y' hy' => (h t y' hy').symm) (hKt hy) i
  have h3 : iteratedFDerivWithin ℝ i (A t) (extChartAt I x₀).target y
      = iteratedFDeriv ℝ i (A t) y := iteratedFDerivWithin_of_isOpen i hopen (hKt hy)
  rw [h1, h2, h3]
  exact hB t ht y hy i hi

lemma add (hA : JBu σ T K k A) (hA' : JBu σ T K k A') :
    JBu σ T K k (fun t y => A t y + A' t y) := by
  obtain ⟨hsm, B, hB0, hB⟩ := hA
  obtain ⟨hsm', B', hB0', hB'⟩ := hA'
  refine ⟨fun t ht y hy => (hsm t ht y hy).add (hsm' t ht y hy), fun i => B i + B' i,
    fun i => add_nonneg (hB0 i) (hB0' i), ?_⟩
  intro t ht y hy i hi
  have h1 : iteratedFDeriv ℝ i (fun y' : E => A t y' + A' t y') y
      = iteratedFDeriv ℝ i (A t) y + iteratedFDeriv ℝ i (A' t) y :=
    iteratedFDeriv_add_apply ((hsm t ht y hy).of_le (by simp)) ((hsm' t ht y hy).of_le (by simp))
  rw [h1]
  exact le_trans (norm_add_le _ _) (add_le_add (hB t ht y hy i hi) (hB' t ht y hy i hi))

lemma neg (hA : JBu σ T K k A) : JBu σ T K k (fun t y => -A t y) := by
  obtain ⟨hsm, B, hB0, hB⟩ := hA
  refine ⟨fun t ht y hy => (hsm t ht y hy).neg, B, hB0, ?_⟩
  intro t ht y hy i hi
  have h1 : iteratedFDeriv ℝ i (fun y' : E => -A t y') y = -iteratedFDeriv ℝ i (A t) y :=
    iteratedFDeriv_neg_apply
  rw [h1, norm_neg]
  exact hB t ht y hy i hi

lemma sub (hA : JBu σ T K k A) (hA' : JBu σ T K k A') :
    JBu σ T K k (fun t y => A t y - A' t y) :=
  (hA.add hA'.neg).congr (fun t y => by ring)

lemma mul (hA : JBu σ T K k A) (hA' : JBu σ T K k A') :
    JBu σ T K k (fun t y => A t y * A' t y) := by
  obtain ⟨hsm, B, hB0, hB⟩ := hA
  obtain ⟨hsm', B', hB0', hB'⟩ := hA'
  refine ⟨fun t ht y hy => (hsm t ht y hy).mul (hsm' t ht y hy),
    (fun i => ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * B j * B' (i - j)),
    (fun i => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 j)) (hB0' _))), ?_⟩
  intro t ht y hy i hi
  exact le_trans (jet_mul_at_le (hsm t ht y hy) (hsm' t ht y hy) hB0 hB0'
    (fun j hj => hB t ht y hy j (le_trans hj hi))
    (fun j hj => hB' t ht y hy j (le_trans hj hi))) le_rfl

lemma finset_sum {ι : Type*} {u : Finset ι} {F : ι → ℝ → E → ℝ}
    (hF : ∀ i ∈ u, JBu σ T K k (F i)) : JBu σ T K k (fun t y => ∑ i ∈ u, F i t y) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
      have hgoal : (fun t y => ∑ j ∈ (∅ : Finset ι), F j t y)
          = fun (_ : ℝ) (_ : E) => (0 : ℝ) := by
        funext t y
        exact Finset.sum_empty
      rw [hgoal]
      refine ⟨fun t ht y hy => contDiffAt_const, fun _ => 0, fun i => le_rfl, ?_⟩
      intro t ht y hy i hi
      have h0 : iteratedFDeriv ℝ i ((fun (_ : ℝ) (_ : E) => (0 : ℝ)) t) y = 0 := by
        rw [show (fun (_ : ℝ) (_ : E) => (0 : ℝ)) t = fun _ : E => (0 : ℝ) from rfl,
          iteratedFDeriv_fun_zero]
        rfl
      rw [h0, norm_zero]
  | insert i u hi ih =>
      have hgoal : (fun t y => ∑ j ∈ insert i u, F j t y)
          = fun t y => F i t y + ∑ j ∈ u, F j t y := by
        funext t y
        exact Finset.sum_insert hi
      rw [hgoal]
      exact (hF i (Finset.mem_insert_self i u)).add
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

lemma sum {ι : Type*} [Fintype ι] {F : ι → ℝ → E → ℝ} (hF : ∀ i, JBu σ T K k (F i)) :
    JBu σ T K k (fun t y => ∑ i, F i t y) :=
  (finset_sum (u := Finset.univ) (fun i _ => hF i)).congr (fun t y => rfl)

lemma of_static {F : E → ℝ} (hsm : ∀ y ∈ K, ContDiffAt ℝ (⊤ : ℕ∞) F y) {B : ℕ → ℝ}
    (hB0 : ∀ i, 0 ≤ B i) (hB : ∀ y ∈ K, ∀ i ≤ k, ‖iteratedFDeriv ℝ i F y‖ ≤ B i) :
    JBu σ T K k (fun _ y => F y) :=
  ⟨fun t ht y hy => hsm y hy, B, hB0, fun t ht y hy i hi => hB y hy i hi⟩

end JBu

/-! ### Structural smoothness of the chart data -/

lemma cGam_contDiffAt_of_target (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (l i j : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.cGam g x₀ (pt (I := I) x₀ y') l i j) y :=
  (contMDiffOn_iff_contDiffOn.mp
    (cGam_zero_iteratedFDeriv_bound_aux2 (I := I) (M := M) g x₀ l i j)).contDiffAt
    ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy)

lemma GramM_contDiffAt_of_target (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') i j) y := by
  have hev : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ => A i j)
      (Work.Diff.EXT.chartMatFun (I := I) (M := M) (G t) x₀ y) := by
    fun_prop
  have h := hev.comp y (contDiffAt_chartMatFun (I := I) (M := M) (G t) x₀ hy)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y' => ?_))
  rfl

lemma GramInv_contDiffAt_of_target (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y') i j) y := by
  have hM : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.EXT.chartMatFun (I := I) (M := M) (G t) x₀) y :=
    contDiffAt_chartMatFun (I := I) (M := M) (G t) x₀ hy
  have hdet : (Matrix.of
      (Work.Diff.EXT.chartMatFun (I := I) (M := M) (G t) x₀ y)).det ≠ 0 :=
    chartMat_det_ne_zero (I := I) (M := M) (G t) x₀ hy
  have hPi : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ =>
        fun i j => (Matrix.of A)⁻¹ i j)
      (Work.Diff.EXT.chartMatFun (I := I) (M := M) (G t) x₀ y) :=
    contDiffAt_matrix_inv_pi _ hdet
  have hev : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun B : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ => B i j)
      ((fun A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ =>
        fun i j => (Matrix.of A)⁻¹ i j)
        (Work.Diff.EXT.chartMatFun (I := I) (M := M) (G t) x₀ y)) := by
    fun_prop
  have hcomp := hev.comp _ hPi
  have h2 := hcomp.comp y hM
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y' => ?_))
  have hmat : Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y')
      = Matrix.of (Work.Diff.EXT.chartMatFun (I := I) (M := M) (G t) x₀ y') := by
    funext i' j'
    rfl
  simp only [Function.comp_apply]
  rw [Work.Diff.GE.GramInv, hmat]

/-! ### The two algebraic identities -/

lemma gramInv_mul_gramM (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y)
        * Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) = 1 := by
  have hdet : (Matrix.of (fun i j =>
      Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y) i j)).det ≠ 0 :=
    chartMat_det_ne_zero (I := I) (M := M) (G t) x₀ hy
  rw [Work.Diff.GE.GramInv]
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet)

lemma cGam_eq_cGam0_add (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j l : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) l i j
      = Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) l i j
        + ∑ k, Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k
            * Work.Diff.EXT.aComp G x₀ t y i j k := by
  have hmul := gramInv_mul_gramM (I := I) (M := M) G x₀ t hy
  set δ : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) k i j
      - Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) k i j with hδ
  have hmulvec : ∀ k, Work.Diff.EXT.aComp G x₀ t y i j k
      = Matrix.mulVec (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)) δ k := by
    intro k
    simp only [Work.Diff.EXT.aComp, Matrix.mulVec_apply, Matrix.row, dotProduct, hδ]
  have hfinal : (∑ k, Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k
        * Work.Diff.EXT.aComp G x₀ t y i j k) = δ l := by
    have h1 : (∑ k, Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k
          * Work.Diff.EXT.aComp G x₀ t y i j k)
        = ∑ k, Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k
            * Matrix.mulVec (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)) δ k :=
      Finset.sum_congr rfl (fun k _ => by rw [hmulvec k])
    rw [h1, show (∑ k, Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l k
            * Matrix.mulVec (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)) δ k)
        = Matrix.mulVec (Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y))
            (Matrix.mulVec (Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y)) δ) l from by
      simp only [Matrix.mulVec_apply, Matrix.row, dotProduct]]
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  rw [hfinal]
  simp only [hδ]
  ring

/-! ### The recursion identity for `aCovArr` -/

lemma aCovArr_succ_expand (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (m : ℕ)
    (v : Fin (m + 1) → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)) (y : E) :
    aCovArr G x₀ t (m + 1) v i j l y
      = fderiv ℝ (aCovArr G x₀ t m (fun s : Fin m => v s.succ) i j l) y
          (Work.Diff.GE.cBasis (E := E) (v 0))
        - ∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p (v r.succ) (v 0)
                * aCovArr G x₀ t m
                    (Function.update (fun s : Fin m => v s.succ) r p) i j l y
        - ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p i (v 0)
                * aCovArr G x₀ t m (fun s : Fin m => v s.succ) p j l y
        - ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p j (v 0)
                * aCovArr G x₀ t m (fun s : Fin m => v s.succ) i p l y
        - ∑ p : Fin (Module.finrank ℝ E),
              Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p l (v 0)
                * aCovArr G x₀ t m (fun s : Fin m => v s.succ) i j p y := rfl

noncomputable def corrFun (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (m : ℕ)
    (w : Fin m → Fin (Module.finrank ℝ E)) (a i j l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (∑ r : Fin m, ∑ p : Fin (Module.finrank ℝ E),
      Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p (w r) a
        * aCovArr G x₀ t m (Function.update w r p) i j l y)
    + (∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p i a
          * aCovArr G x₀ t m w p j l y
      + (∑ p : Fin (Module.finrank ℝ E),
          Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p j a
            * aCovArr G x₀ t m w i p l y
        + ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p l a
              * aCovArr G x₀ t m w i j p y))

lemma fderiv_aCovArr_eq (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (m : ℕ)
    (w : Fin m → Fin (Module.finrank ℝ E)) (a i j l : Fin (Module.finrank ℝ E)) (y : E) :
    fderiv ℝ (fun y' : E => aCovArr G x₀ t m w i j l y') y (Work.Diff.GE.cBasis (E := E) a)
      = aCovArr G x₀ t (m + 1) (Fin.cons a w) i j l y + corrFun G x₀ t m w a i j l y := by
  have h := aCovArr_succ_expand (I := I) (M := M) G x₀ t m (Fin.cons a w) i j l y
  simp only [Fin.cons_zero, Fin.cons_succ] at h
  rw [h]
  simp only [corrFun]
  ring

/-! ### Smoothness of the correction function and of `aCovArr` -/

lemma corrFun_contDiffAt (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target) {m : ℕ} {w : Fin m → Fin (Module.finrank ℝ E)}
    {a i j l : Fin (Module.finrank ℝ E)}
    (hA : ∀ (w' : Fin m → Fin (Module.finrank ℝ E)) (i' j' l' : Fin (Module.finrank ℝ E))
      (t : ℝ) {y : E}, y ∈ K →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => aCovArr G x₀ t m w' i' j' l' y') y)
    (t : ℝ) {y : E} (hy : y ∈ K) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => corrFun G x₀ t m w a i j l y') y := by
  have hG : ∀ (p q r : Fin (Module.finrank ℝ E)), ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p q r) y :=
    fun p q r => cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀ (hKt hy) p q r
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ r : Fin m,
      ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p (w r) a
          * aCovArr G x₀ t m (Function.update w r p) i j l y') y :=
    ContDiffAt.sum (s := Finset.univ) (fun r _ => ContDiffAt.sum (s := Finset.univ) (fun p _ =>
      (hG p (w r) a).mul (hA (Function.update w r p) i j l t hy)))
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p i a
          * aCovArr G x₀ t m w p j l y') y :=
    ContDiffAt.sum (s := Finset.univ) (fun p _ => (hG p i a).mul (hA w p j l t hy))
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p j a
          * aCovArr G x₀ t m w i p l y') y :=
    ContDiffAt.sum (s := Finset.univ) (fun p _ => (hG p j a).mul (hA w i p l t hy))
  have h4 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p l a
          * aCovArr G x₀ t m w i j p y') y :=
    ContDiffAt.sum (s := Finset.univ) (fun p _ => (hG p l a).mul (hA w i j p t hy))
  exact (h1.add (h2.add (h3.add h4))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y' => rfl))

theorem aCovArr_contDiffAt (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target) :
    ∀ (m : ℕ) (w : Fin m → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E))
      (t : ℝ) {y : E}, y ∈ K →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => aCovArr G x₀ t m w i j l y') y := by
  intro m
  induction m with
  | zero =>
    intro w i j l t y hy
    have hS : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.GramM G x₀ t (pt (I := I) x₀ y') l p
          * (Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y') p i j
              - Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') p i j)) y :=
      ContDiffAt.sum (s := Finset.univ) (fun p _ =>
        (GramM_contDiffAt_of_target (I := I) (M := M) G x₀ t (hKt hy) l p).mul
          ((cGam_contDiffAt_of_target (I := I) (M := M) (G t) x₀ (hKt hy) p i j).sub
            (cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀ (hKt hy) p i j)))
    exact hS.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y' => rfl))
  | succ m ih =>
    intro w i j l t y hy
    have hfun : (fun y' : E => aCovArr G x₀ t (m + 1) w i j l y')
        = fun y' : E => fderiv ℝ (fun y'' : E =>
              aCovArr G x₀ t m (fun s : Fin m => w s.succ) i j l y'') y'
              (Work.Diff.GE.cBasis (E := E) (w 0))
            - corrFun G x₀ t m (fun s : Fin m => w s.succ) (w 0) i j l y' := by
      funext y'
      rw [aCovArr_succ_expand (I := I) (M := M) G x₀ t m w i j l y']
      simp only [corrFun]
      ring
    rw [hfun]
    exact (contDiffAt_fderiv_apply' (ih (fun s : Fin m => w s.succ) i j l t hy)).sub
      (corrFun_contDiffAt (I := I) (M := M) G x₀ K hKt
        (fun w' i' j' l' t' => ih w' i' j' l' t') t hy)

/-! ### `JBu` families built from the chart data -/

lemma cGam0_jBu (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hcGam0 : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (pt (I := I) x₀ y') l i j) y‖ ≤ C)
    (k : ℕ) (l i j : Fin (Module.finrank ℝ E)) :
    JBu σ T K k (fun (_ : ℝ) (y : E) => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) l i j) := by
  have hsm : ∀ y ∈ K, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y') l i j) y :=
    fun y hy => cGam_contDiffAt_of_target (I := I) (M := M) (G 0) x₀ (hKt hy) l i j
  have hbd : ∀ k' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k' (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
        (pt (I := I) x₀ y') l i j) y‖ ≤ C := by
    intro k'
    obtain ⟨C, hC0, hC⟩ := hcGam0 k'
    exact ⟨C, hC0, fun y hy => hC y hy i j l⟩
  choose B hB0 hB using hbd
  exact ⟨fun t ht y hy => hsm y hy, B, hB0, fun t ht y hy i' hi' => hB i' y hy⟩

lemma gramInv_jBu (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hGInv : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.GramInv G x₀ t
          (pt (I := I) x₀ y') i j) y‖ ≤ C)
    (k : ℕ) (i j : Fin (Module.finrank ℝ E)) :
    JBu σ T K k (fun t (y : E) => Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) i j) := by
  have hsm : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y') i j) y :=
    fun t ht y hy => GramInv_contDiffAt_of_target (I := I) (M := M) G x₀ t (hKt hy) i j
  have hbd : ∀ k' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k' (fun y' : E => Work.Diff.GE.GramInv G x₀ t
        (pt (I := I) x₀ y') i j) y‖ ≤ C := by
    intro k'
    obtain ⟨C, hC0, hC⟩ := hGInv k'
    exact ⟨C, hC0, fun t ht y hy => hC t ht y hy i j⟩
  choose B hB0 hB using hbd
  exact ⟨hsm, B, hB0, fun t ht y hy i' hi' => hB i' t ht y hy⟩

lemma corrFun_jBu (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target) (k : ℕ)
    (hcGam0 : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (pt (I := I) x₀ y') l i j) y‖ ≤ C)
    (ih : ∀ (m : ℕ) (w : Fin m → Fin (Module.finrank ℝ E))
      (i j l : Fin (Module.finrank ℝ E)),
      JBu σ T K k (fun t y => aCovArr G x₀ t m w i j l y))
    (m : ℕ) (w : Fin m → Fin (Module.finrank ℝ E))
    (a i j l : Fin (Module.finrank ℝ E)) :
    JBu σ T K k (fun t y => corrFun G x₀ t m w a i j l y) := by
  have hG : ∀ (p q r : Fin (Module.finrank ℝ E)),
      JBu σ T K k (fun (_ : ℝ) (y : E) =>
        Work.Diff.GE.cGam (G 0) x₀ (pt (I := I) x₀ y) p q r) :=
    fun p q r => cGam0_jBu (I := I) (M := M) G σ T x₀ K hKt hcGam0 k p q r
  refine (JBu.sum (k := k) (σ := σ) (T := T) (K := K) (fun r : Fin m =>
      JBu.sum (fun p : Fin (Module.finrank ℝ E) =>
        (hG p (w r) a).mul (ih m (Function.update w r p) i j l)))).add
    ((JBu.sum (fun p : Fin (Module.finrank ℝ E) =>
        (hG p i a).mul (ih m w p j l))).add
      ((JBu.sum (fun p : Fin (Module.finrank ℝ E) =>
          (hG p j a).mul (ih m w i p l))).add
        (JBu.sum (fun p : Fin (Module.finrank ℝ E) =>
          (hG p l a).mul (ih m w i j p))))) |>.congr (fun t y => rfl)

/-- **The induction**: all the chart components of the background covariant derivatives of the
connection difference have uniformly bounded iterated Fréchet derivatives of every order on `K`. -/
theorem aCovArr_jBu (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hcore : ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (v : Fin k → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
        |Work.Diff.EXT.aCovArr (I := I) (M := M) G x₀ t k v i j l y| ≤ Ck)
    (hcGam0 : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (pt (I := I) x₀ y') l i j) y‖ ≤ C) :
    ∀ (k : ℕ) (m : ℕ) (w : Fin m → Fin (Module.finrank ℝ E))
      (i j l : Fin (Module.finrank ℝ E)),
      JBu σ T K k (fun t y => aCovArr G x₀ t m w i j l y) := by
  intro k
  induction k with
  | zero =>
    intro m w i j l
    obtain ⟨C, hC0, hC⟩ := hcore m
    refine ⟨fun t ht y hy => aCovArr_contDiffAt (I := I) (M := M) G x₀ K hKt m w i j l t hy,
      fun _ => C, fun _ => hC0, ?_⟩
    intro t ht y hy i' hi'
    have hi0 : i' = 0 := Nat.le_zero.mp hi'
    subst hi0
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact hC t ht y hy w i j l
  | succ k ih =>
    intro m w i j l
    obtain ⟨Dh, hDh0, hDh⟩ :=
      jet_succ_le_fderiv_basis (E := E) k
    have hBw : ∀ a : Fin (Module.finrank ℝ E),
        JBu σ T K k (fun t y => aCovArr G x₀ t (m + 1) (Fin.cons a w) i j l y) :=
      fun a => ih (m + 1) (Fin.cons a w) i j l
    have hCw : ∀ a : Fin (Module.finrank ℝ E),
        JBu σ T K k (fun t y => corrFun G x₀ t m w a i j l y) :=
      fun a => corrFun_jBu (I := I) (M := M) G σ T x₀ K hKt k hcGam0 ih m w a i j l
    choose bw hbw0 hbw using fun a => (hBw a).2
    choose cw hcw0 hcw using fun a => (hCw a).2
    obtain ⟨Bk, hBk0, hBk⟩ := (ih m w i j l).2
    have hnw : (0 : ℝ) ≤ Dh * ∑ a, (bw a k + cw a k) :=
      mul_nonneg hDh0 (Finset.sum_nonneg (fun a _ => add_nonneg (hbw0 a k) (hcw0 a k)))
    refine ⟨fun t ht y hy => aCovArr_contDiffAt (I := I) (M := M) G x₀ K hKt m w i j l t hy,
      fun i' => Bk i' + (if i' = k + 1 then Dh * ∑ a, (bw a k + cw a k) else 0),
      fun i' => add_nonneg (hBk0 i') (by split <;> [exact hnw; exact le_rfl]), ?_⟩
    intro t ht y hy i' hi'
    rcases Nat.lt_or_ge i' (k + 1) with hlt | hge
    · have hle : i' ≤ k := Nat.lt_succ_iff.mp hlt
      have h0 : (if i' = k + 1 then Dh * ∑ a, (bw a k + cw a k) else 0) = 0 := by
        simp only [if_neg (ne_of_lt hlt)]
      simp only [h0, add_zero]
      exact hBk t ht y hy i' hle
    · have heq : i' = k + 1 := le_antisymm hi' hge
      subst heq
      simp only [if_true]
      have hDh' : ‖iteratedFDeriv ℝ (k + 1) (fun y' : E => aCovArr G x₀ t m w i j l y') y‖
          ≤ Dh * ∑ a : Fin (Module.finrank ℝ E),
              (‖iteratedFDeriv ℝ k (fun y' : E =>
                  aCovArr G x₀ t (m + 1) (Fin.cons a w) i j l y') y‖
                + ‖iteratedFDeriv ℝ k (fun y' : E => corrFun G x₀ t m w a i j l y') y‖) :=
        hDh (aCovArr_contDiffAt (I := I) (M := M) G x₀ K hKt m w i j l t hy)
          (fun a y' => fderiv_aCovArr_eq (I := I) (M := M) G x₀ t m w a i j l y')
          (fun a => aCovArr_contDiffAt (I := I) (M := M) G x₀ K hKt (m + 1)
            (Fin.cons a w) i j l t hy)
          (fun a => corrFun_contDiffAt (I := I) (M := M) G x₀ K hKt
            (fun w' i' j' l' t' =>
              aCovArr_contDiffAt (I := I) (M := M) G x₀ K hKt m w' i' j' l' t') t hy)
      refine le_trans hDh' ?_
      have hsum2 : Dh * ∑ a : Fin (Module.finrank ℝ E),
            (‖iteratedFDeriv ℝ k (fun y' : E =>
                aCovArr G x₀ t (m + 1) (Fin.cons a w) i j l y') y‖
              + ‖iteratedFDeriv ℝ k (fun y' : E => corrFun G x₀ t m w a i j l y') y‖)
          ≤ Dh * ∑ a : Fin (Module.finrank ℝ E), (bw a k + cw a k) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => by
          have h1 := hbw a t ht y hy k le_rfl
          have h2 := hcw a t ht y hy k le_rfl
          linarith)) hDh0
      linarith [hBk0 (k + 1)]

end CBound

open CBound

/-! ### The final theorem -/

theorem christoffel_bounds_of_core
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target) (hU : UniqueDiffOn ℝ K)
    (hcore : ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (v : Fin k → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)),
        |Work.Diff.EXT.aCovArr (I := I) (M := M) G x₀ t k v i j l y| ≤ Ck)
    (hGInv : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.GramInv G x₀ t
          (Work.Diff.EXT.pt (I := I) x₀ y') i j) y‖ ≤ C)
    (hcGam0 : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
        (Work.Diff.EXT.pt (I := I) x₀ y') l i j) y‖ ≤ C)
    (hsmGInv : ∀ t ∈ Set.Ico σ T, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.GramInv G x₀ t
        (Work.Diff.EXT.pt (I := I) x₀ y') i j) K)
    (hsmcGam : ∀ t ∈ Set.Ico σ T, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G t) x₀
        (Work.Diff.EXT.pt (I := I) x₀ y') l i j) K) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.cGam (G t) x₀
          (Work.Diff.EXT.pt (I := I) x₀ y') l i j) y‖ ≤ C := by
  intro k
  have hmain : ∀ (i j l : Fin (Module.finrank ℝ E)),
      JBu σ T K k (fun t (y : E) => Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) l i j) := by
    intro i j l
    have h0 := cGam0_jBu (I := I) (M := M) G σ T x₀ K hKt hcGam0 k l i j
    have hsum : JBu σ T K k (fun t (y : E) => ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.GramInv G x₀ t (pt (I := I) x₀ y) l p
          * Work.Diff.EXT.aComp G x₀ t y i j p) := by
      refine (JBu.sum (k := k) (σ := σ) (T := T) (K := K)
        (fun p : Fin (Module.finrank ℝ E) =>
        (gramInv_jBu (I := I) (M := M) G σ T x₀ K hKt hGInv k l p).mul
          (aCovArr_jBu (I := I) (M := M) G σ T x₀ K hKt hcore hcGam0 k 0
            (fun s : Fin 0 => Fin.elim0 s) i j p))).congr (fun t y => rfl)
    refine (h0.add hsum).congrOn hKt (fun t y hy' => ?_)
    exact (cGam_eq_cGam0_add (I := I) (M := M) G x₀ t hy' i j l).symm
  choose B hB0 hB using fun (p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
    × Fin (Module.finrank ℝ E)) => (hmain p.1 p.2.1 p.2.2).2
  refine ⟨∑ p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
    × Fin (Module.finrank ℝ E), B p k, Finset.sum_nonneg (fun p _ => hB0 p k), ?_⟩
  intro t ht y hy i j l
  refine le_trans (hB (i, j, l) t ht y hy k le_rfl) ?_
  exact Finset.single_le_sum (fun p (_ : p ∈ Finset.univ) => hB0 p k)
    (Finset.mem_univ (i, j, l))

end Work.Diff.EXT
