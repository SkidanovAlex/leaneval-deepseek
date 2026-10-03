import Mathlib
import Submission.Lib.Unif2.Work.Drive.phaseGadget
import Submission.Lib.Unif2.Work.Drive.continuousAt_gadget
import Submission.Lib.Unif2.Work.Drive.pair_gadget_tendsto
import Submission.Lib.Unif2.Work.Drive.deriv_chart_transition_ne_zero
import Submission.Lib.Unif2.Work.Drive.tendsto_chart_transition_slope

/-!
# The degree-one phase built from a chain of pivots: setup

This file collects the definitions and the elementary "bookkeeping" facts used by the
construction of a continuous `Θ : X → ℂ` with a single simple zero at a base point `z₀` out of a
chain of pivots `a : ℕ → X` with radii `ρ : ℕ → ℝ` (see
`Submission/Work/Drive/exists_phase_of_chain.lean`).

The `i`-th transfer gadget `gadget a ρ i` differs from the constant `1` only inside the chart ball
of radius `8 ρ i` about the pivot `a i` (the set `gU a ρ i` below), and off its two pivots it is a
unit complex number.  The *locally finite* hypothesis `hlf` says that these balls are locally
finite (for every compact set only finitely many of them meet it), which makes the product
`gPhi a ρ x = ∏ᶠ i, gadget a ρ i x` a locally finite product: near every point only finitely many
factors differ from `1`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set Metric
open Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## 1. The supports of the gadgets -/

/-- The chart ball of radius `r i` about the `i`-th pivot. -/
def gB (a : ℕ → X) (r : ℕ → ℝ) (i : ℕ) : Set X :=
  {x : X | x ∈ (chartAt ℂ (a i)).source ∧
    (chartAt ℂ (a i)) x ∈ Metric.ball ((chartAt ℂ (a i)) (a i)) (r i)}

/-- The support of the `i`-th transfer gadget: the chart ball of radius `8 ρ i` about `a i`. -/
def gU (a : ℕ → X) (ρ : ℕ → ℝ) (i : ℕ) : Set X :=
  {x : X | x ∈ (chartAt ℂ (a i)).source ∧
    (chartAt ℂ (a i)) x ∈ Metric.ball ((chartAt ℂ (a i)) (a i)) (8 * ρ i)}

@[simp] lemma mem_gB {a : ℕ → X} {r : ℕ → ℝ} {i : ℕ} {x : X} :
    x ∈ gB a r i ↔ x ∈ (chartAt ℂ (a i)).source ∧
      (chartAt ℂ (a i)) x ∈ Metric.ball ((chartAt ℂ (a i)) (a i)) (r i) := Iff.rfl

@[simp] lemma mem_gU {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ} {x : X} :
    x ∈ gU a ρ i ↔ x ∈ (chartAt ℂ (a i)).source ∧
      (chartAt ℂ (a i)) x ∈ Metric.ball ((chartAt ℂ (a i)) (a i)) (8 * ρ i) := Iff.rfl

lemma mem_gU_iff {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ} {x : X} :
    x ∈ gU a ρ i ↔ x ∈ (chartAt ℂ (a i)).source ∧
      ‖(chartAt ℂ (a i)) x - gP a i‖ < 8 * ρ i := by
  rw [mem_gU, Metric.mem_ball, dist_eq_norm, gP]

lemma isOpen_gB (a : ℕ → X) (r : ℕ → ℝ) (i : ℕ) : IsOpen (gB a r i) := by
  have h : gB a r i = (chartAt ℂ (a i)).source ∩
      (chartAt ℂ (a i)) ⁻¹' Metric.ball ((chartAt ℂ (a i)) (a i)) (r i) := rfl
  rw [h]
  exact ContinuousOn.isOpen_inter_preimage (chartAt ℂ (a i)).continuousOn
    (chartAt ℂ (a i)).open_source Metric.isOpen_ball

lemma isOpen_gU (a : ℕ → X) (ρ : ℕ → ℝ) (i : ℕ) : IsOpen (gU a ρ i) :=
  isOpen_gB a (fun i => 8 * ρ i) i

/-- Every pivot lies in its own support. -/
lemma self_mem_gU {a : ℕ → X} {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i : ℕ) :
    a i ∈ gU a ρ i := by
  rw [mem_gU]
  refine ⟨mem_chart_source ℂ (a i), ?_⟩
  simp only [Metric.mem_ball, dist_self]
  linarith [hρ i]

lemma gadget_eq_one_of_notMem_gU {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ} {x : X}
    (hρ : 0 < ρ i) (hx : x ∉ gU a ρ i) : gadget a ρ i x = 1 := by
  refine gadget_eq_one_of_far hρ ?_
  rw [← mem_gU_iff]
  exact hx

lemma gadget_ne_one_mem_gU {a : ℕ → X} {ρ : ℕ → ℝ} {i : ℕ} {x : X}
    (hρ : 0 < ρ i) (h : gadget a ρ i x ≠ 1) : x ∈ gU a ρ i := by
  rw [mem_gU_iff]
  exact gadget_ne_one_mem hρ h

/-! ## 2. The step hypothesis in usable form -/

/-- The step hypothesis gives the distance estimate needed for the continuity of the gadgets. -/
lemma norm_gQ_sub_gP_lt {a : ℕ → X} {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hstep : ∀ i, a (i + 1) ∈ gB a ρ i) (i : ℕ) : ‖gQ a i - gP a i‖ < 2 * ρ i := by
  have h := hstep i
  rw [gB, Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm] at h
  rw [gQ, gP]
  linarith [h.2, hρ i]

lemma step_src {a : ℕ → X} {ρ : ℕ → ℝ} (hstep : ∀ i, a (i + 1) ∈ gB a ρ i) (i : ℕ) :
    a (i + 1) ∈ (chartAt ℂ (a i)).source := by
  have h := hstep i
  rw [gB, Set.mem_setOf_eq] at h
  exact h.1

/-! ## 3. Local finiteness -/

/-- The product of all gadgets differs from `1` at `x` only for finitely many indices. -/
lemma finite_setOf_gadget_ne_one {a : ℕ → X} {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ gU a ρ i).Nonempty}.Finite)
    (x : X) : {i : ℕ | gadget a ρ i x ≠ 1}.Finite :=
  (hlf {x} isCompact_singleton).subset (fun i hi => ⟨x, mem_singleton_iff.mpr rfl,
    gadget_ne_one_mem_gU (hρ i) hi⟩)

/-- Local finiteness in the finset-witness form: near a point there is a neighbourhood on which
every index whose support meets it belongs to a fixed finite set. -/
lemma exists_finset_forall_mem_gU_of_mem {a : ℕ → X} {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ gU a ρ i).Nonempty}.Finite) (p : X) :
    ∃ (K : Set X) (F : Finset ℕ), K ∈ 𝓝 p ∧ ∀ y ∈ K, ∀ i : ℕ, y ∈ gU a ρ i → i ∈ F := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  obtain ⟨K, hKc, hKnhds⟩ := exists_compact_mem_nhds p
  exact ⟨K, (hlf K hKc).toFinset, hKnhds, fun y hy i hi => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨y, hy, hi⟩⟩

/-- The eventually-finite form of local finiteness. -/
lemma exists_finset_eventually_gadget_ne_one {a : ℕ → X} {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ gU a ρ i).Nonempty}.Finite) (p : X) :
    ∃ F : Finset ℕ, ∀ᶠ y in 𝓝 p, ∀ i : ℕ, gadget a ρ i y ≠ 1 → i ∈ F := by
  obtain ⟨K, F, hK, hKF⟩ := exists_finset_forall_mem_gU_of_mem hρ hlf p
  exact ⟨F, Filter.eventually_of_mem hK fun y hy i hi =>
    hKF y hy i (gadget_ne_one_mem_gU (hρ i) hi)⟩

/-- The pivots form a locally finite set: every point has a neighbourhood meeting the range of `a`
only possibly at that point. -/
lemma exists_nhds_inter_range_subset_singleton {a : ℕ → X} {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ gU a ρ i).Nonempty}.Finite) (p : X) :
    ∃ W : Set X, W ∈ 𝓝 p ∧ W ∩ Set.range a ⊆ {p} := by
  obtain ⟨K, F, hK, hKF⟩ := exists_finset_forall_mem_gU_of_mem hρ hlf p
  set A : Set X := {q : X | ∃ i ∈ F, q = a i ∧ a i ≠ p} with hA
  have hAfin : A.Finite :=
    (F.finite_toSet).image a |>.subset (fun q hq => by
      obtain ⟨i, hiF, hqeq, -⟩ := hq
      exact ⟨i, hiF, hqeq.symm⟩)
  refine ⟨K ∩ Aᶜ, Filter.inter_mem hK ?_, ?_⟩
  · refine (hAfin.isClosed.isOpen_compl).mem_nhds ?_
    simp only [Set.mem_compl_iff, hA, Set.mem_setOf_eq, not_exists, not_and]
    intro i _ hp hne
    exact hne hp.symm
  · rintro z ⟨⟨hzK, hzA⟩, ⟨j, rfl⟩⟩
    have hjF : j ∈ F := hKF (a j) hzK j (self_mem_gU hρ j)
    by_contra hne
    exact hzA ⟨j, hjF, rfl, hne⟩

/-! ## 4. The two general product lemmas -/

/-- A locally finite product of functions continuous at a point is continuous at that point. -/
lemma continuousAt_finprod {ι : Type*} {g : ι → X → ℂ} {p : X}
    (hex : ∃ F : Finset ι, ∀ᶠ y in 𝓝 p, ∀ i, g i y ≠ 1 → i ∈ F)
    (hg : ∀ i, ContinuousAt (g i) p) :
    ContinuousAt (fun x : X => ∏ᶠ i, g i x) p := by
  obtain ⟨F, hF⟩ := hex
  have heq : (fun x : X => ∏ᶠ i, g i x) =ᶠ[𝓝 p] fun x : X => ∏ i ∈ F, g i x := by
    filter_upwards [hF] with y hy
    exact finprod_eq_prod_of_mulSupport_subset _
      (fun i hi => hy i (Function.mem_mulSupport.mp hi))
  have hcont : ContinuousAt (fun x : X => ∏ i ∈ F, g i x) p :=
    tendsto_finsetProd F (fun i _ => (hg i).tendsto)
  exact hcont.congr_of_eventuallyEq heq

/-- A locally finite product whose finite part has a limit along the punctured neighbourhood has
the same limit. -/
lemma tendsto_finprod_nhdsNE {ι : Type*} {g : ι → X → ℂ} {p : X} {F : Finset ι}
    (hF : ∀ᶠ y in 𝓝 p, ∀ i, g i y ≠ 1 → i ∈ F)
    {L : ℂ} (hL : Tendsto (fun y : X => ∏ i ∈ F, g i y) (𝓝[≠] p) (𝓝 L)) :
    Tendsto (fun x : X => ∏ᶠ i, g i x) (𝓝[≠] p) (𝓝 L) := by
  refine Tendsto.congr' ?_ hL
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hF] with y hy
  exact (finprod_eq_prod_of_mulSupport_subset _
    (fun i hi => hy i (Function.mem_mulSupport.mp hi))).symm

/-- Filling in a value at a point: if `f` has a limit `L` along the punctured neighbourhood of `p`,
then the function equal to `L` at `p` and to `f` elsewhere tends to `L` at `p`. -/
lemma tendsto_nhds_ite_eq {f : X → ℂ} {p : X} {L : ℂ}
    (h : Tendsto f (𝓝[≠] p) (𝓝 L)) :
    Tendsto (fun y : X => if y = p then L else f y) (𝓝 p) (𝓝 L) := by
  intro s hs
  rw [Filter.mem_map]
  have hT : f ⁻¹' s ∈ 𝓝[≠] p := Filter.mem_map.mp (h hs)
  rw [nhdsWithin, Filter.mem_inf_principal] at hT
  obtain ⟨U, hU, hUs⟩ := Filter.eventually_iff_exists_mem.mp hT
  refine Filter.mem_of_superset hU fun y hy => ?_
  by_cases hyp : y = p
  · simp only [Set.mem_preimage, if_pos hyp]
    exact mem_of_mem_nhds hs
  · simp only [Set.mem_preimage, if_neg hyp]
    exact hUs y hy hyp

/-! ## 5. The locally finite product of the gadgets -/

/-- The locally finite product of all transfer gadgets. -/
def gPhi (a : ℕ → X) (ρ : ℕ → ℝ) (x : X) : ℂ := ∏ᶠ i : ℕ, gadget a ρ i x

lemma gPhi_eq_prod_of {a : ℕ → X} {ρ : ℕ → ℝ} {F : Finset ℕ} {y : X}
    (h : ∀ i : ℕ, gadget a ρ i y ≠ 1 → i ∈ F) :
    gPhi a ρ y = ∏ i ∈ F, gadget a ρ i y :=
  finprod_eq_prod_of_mulSupport_subset _ (fun i hi => h i (Function.mem_mulSupport.mp hi))

lemma eventually_gPhi_eq_prod {a : ℕ → X} {ρ : ℕ → ℝ} {F : Finset ℕ} {p : X}
    (h : ∀ᶠ y in 𝓝 p, ∀ i : ℕ, gadget a ρ i y ≠ 1 → i ∈ F) :
    gPhi a ρ =ᶠ[𝓝 p] fun y : X => ∏ i ∈ F, gadget a ρ i y := by
  filter_upwards [h] with y hy
  exact gPhi_eq_prod_of hy

/-- Away from the pivots the product of the gadgets is continuous. -/
lemma continuousAt_gPhi_of_notMem_range {a : ℕ → X} {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hstep : ∀ i, a (i + 1) ∈ gB a ρ i)
    (hwell : ∀ i, closure (gU a ρ i) ⊆ (chartAt ℂ (a i)).source)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ gU a ρ i).Nonempty}.Finite)
    {p : X} (hp : ∀ i : ℕ, p ≠ a i) : ContinuousAt (gPhi a ρ) p := by
  refine continuousAt_finprod (g := fun i (x : X) => gadget a ρ i x)
    (exists_finset_eventually_gadget_ne_one hρ hlf p) ?_
  intro i
  exact continuousAt_gadget (hρ i) (norm_gQ_sub_gP_lt hρ hstep i) (step_src hstep i)
    (hwell i) (hp i) (hp (i + 1))

/-- Away from the pivots the product of the gadgets has modulus one. -/
lemma norm_gPhi_eq_one_of_notMem_range {a : ℕ → X} {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hstep : ∀ i, a (i + 1) ∈ gB a ρ i)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ gU a ρ i).Nonempty}.Finite)
    {x : X} (hx : ∀ i : ℕ, x ≠ a i) : ‖gPhi a ρ x‖ = 1 := by
  have hfin := finite_setOf_gadget_ne_one hρ hlf x
  rw [gPhi, finprod_eq_prod_of_mulSupport_subset_of_finite _
    (s := {i : ℕ | gadget a ρ i x ≠ 1}) (fun i hi => hi) hfin]
  rw [norm_prod]
  refine Finset.prod_eq_one fun i hi => ?_
  rw [hfin.mem_toFinset] at hi
  exact norm_gadget_eq_one (step_src hstep i) (hx i) (hx (i + 1))

lemma gPhi_ne_zero_of_notMem_range {a : ℕ → X} {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hstep : ∀ i, a (i + 1) ∈ gB a ρ i)
    (hlf : ∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ gU a ρ i).Nonempty}.Finite)
    {x : X} (hx : ∀ i : ℕ, x ≠ a i) : gPhi a ρ x ≠ 0 := by
  intro h
  have := norm_gPhi_eq_one_of_notMem_range hρ hstep hlf hx
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- Filling in a value at a point, in `ContinuousAt` form. -/
lemma continuousAt_ite_of_tendsto_nhdsNE {f : X → ℂ} {p : X} {L : ℂ}
    (h : Tendsto f (𝓝[≠] p) (𝓝 L)) :
    ContinuousAt (fun y : X => if y = p then L else f y) p := by
  rw [ContinuousAt, if_pos rfl]
  exact tendsto_nhds_ite_eq h

/-! ## 6. A scalar identity for the phase -/

/-- `z * conj (phase z) = ‖z‖`. -/
lemma mul_star_phase (z : ℂ) : z * star (phase z) = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · subst hz; simp [phase]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hstar : star ((‖z‖ : ℝ) : ℂ) = ((‖z‖ : ℝ) : ℂ) := Complex.conj_ofReal _
    have hmc : z * star z = ((Complex.normSq z : ℝ) : ℂ) := Complex.mul_conj z
    rw [phase, div_eq_mul_inv, star_mul', star_inv₀, hstar, ← mul_assoc, hmc,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_inj,
      Complex.normSq_eq_norm_sq, pow_two]
    rw [mul_assoc, mul_inv_cancel₀ hn, mul_one]

end Work.Drive
