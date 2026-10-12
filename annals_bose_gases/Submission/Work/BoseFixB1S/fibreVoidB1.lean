import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxQIndSq_prodTransfer
import Submission.Work.BoseFixB1S.fibreAeTransfer
import Submission.Work.BoseFixB1S.pairVoidAeB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-- **The pushforward of the product measure under the coordinate update.**

For a finite measure `ν` on `E3` and the map `p ↦ Function.update p.1 i p.2` on
`X n × E3`, the pushforward of `νⁿ ⊗ ν` is `ν(E3) • νⁿ`: the update forgets one of the
`n + 1` coordinates, so the resulting measure is the `n`-fold product scaled by the total
mass of the forgotten coordinate.

The proof computes the value of the pushforward on the π-system of cylinders with
measurable sides (a π-system that generates the product σ-algebra), and then applies the
extensionality `Measure.FiniteSpanningSetsIn.ext` with the constant spanning sequence
`Set.univ`. -/
theorem pushforward_update (n : ℕ) (i : Fin n) (ν : Measure E3) [IsFiniteMeasure ν] :
    Measure.map (fun p : X n × E3 => Function.update p.1 i p.2)
      ((Measure.pi (fun _ : Fin n => ν)).prod ν)
    = ν Set.univ • Measure.pi (fun _ : Fin n => ν) := by
  haveI : IsFiniteMeasure (Measure.pi (fun _ : Fin n => ν)) := inferInstance
  haveI : IsFiniteMeasure ((Measure.pi (fun _ : Fin n => ν)).prod ν) := inferInstance
  haveI : IsFiniteMeasure (Measure.map (fun p : X n × E3 => Function.update p.1 i p.2)
      ((Measure.pi (fun _ : Fin n => ν)).prod ν)) := inferInstance
  -- the value of the two measures on a cylinder
  have hcyl : ∀ s : Fin n → Set E3, (∀ k, MeasurableSet (s k)) →
      (Measure.map (fun p : X n × E3 => Function.update p.1 i p.2)
        ((Measure.pi (fun _ : Fin n => ν)).prod ν)) (Set.pi Set.univ s)
      = (ν Set.univ • Measure.pi (fun _ : Fin n => ν)) (Set.pi Set.univ s) := by
    intro s hs
    have hset : (fun p : X n × E3 => Function.update p.1 i p.2) ⁻¹' (Set.pi Set.univ s)
        = (Set.pi Set.univ (fun k => if k = i then (Set.univ : Set E3) else s k)) ×ˢ (s i) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod,
        Set.mem_ite_univ_left]
      constructor
      · intro hp
        exact ⟨fun k hk => by simpa [Function.update_apply, hk] using hp k,
          by simpa [Function.update_apply] using hp i⟩
      · intro ⟨h1, h2⟩ k
        by_cases hk : k = i
        · subst hk; simpa [Function.update_apply] using h2
        · simpa [Function.update_apply, hk] using h1 k hk
    rw [Measure.map_apply measurable_update' (MeasurableSet.pi Set.countable_univ fun k _ => hs k),
      hset, Measure.prod_prod, Measure.pi_pi, Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
    rw [← Finset.mul_prod_erase Finset.univ (fun k => ν (if k = i then Set.univ else s k))
        (a := i) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun k => ν (s k)) (a := i) (Finset.mem_univ i)]
    have hP : ∏ x ∈ Finset.univ.erase i, ν (if x = i then Set.univ else s x)
        = ∏ x ∈ Finset.univ.erase i, ν (s x) :=
      Finset.prod_congr rfl (fun x hx => by rw [if_neg (Finset.mem_erase.mp hx).1])
    rw [if_pos rfl, hP]
    ac_rfl
  set C : Set (Set (X n)) := Set.pi Set.univ '' Set.pi Set.univ
    (fun _ : Fin n => {s : Set E3 | MeasurableSet s}) with hC
  have hA : (inferInstance : MeasurableSpace (X n)) = MeasurableSpace.generateFrom C := by
    rw [hC]
    exact (generateFrom_pi (ι := Fin n) (α := fun _ : Fin n => E3)).symm
  have hpi : IsPiSystem C := by
    rw [hC]
    exact isPiSystem_pi (α := fun _ : Fin n => E3)
  have hspan : (Measure.map (fun p : X n × E3 => Function.update p.1 i p.2)
      ((Measure.pi (fun _ : Fin n => ν)).prod ν)).FiniteSpanningSetsIn C :=
    ⟨fun _ => Set.univ,
      fun _ => ⟨fun _ => Set.univ, fun _ _ => by simp, (Set.pi_univ _)⟩,
      fun _ => measure_lt_top _ _,
      by ext x; simp⟩
  refine Measure.FiniteSpanningSetsIn.ext hA hpi hspan ?_
  rintro s ⟨t, ht, rfl⟩
  exact hcyl t fun k => (Set.mem_univ_pi.mp ht) k

/-- The same pushforward identity in the box form used by the target: the product of the
restricted box measure and the restricted cube measure. -/
theorem pushforward_update_abox {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n) :
    Measure.map (fun p : X n × E3 => Function.update p.1 i p.2)
      (((volume : Measure (X n)).restrict (Submission.BoseGases.abox n ℓ)).prod
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
    = ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ •
        ((volume : Measure (X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
  haveI hfin : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact Submission.BoseGases.acube_lt_top ℓ hℓ.le
  have h := pushforward_update n i ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
  rw [restrict_abox_eq_pi n ℓ]
  exact h

theorem fibreVoidB1 {n : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hden : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
        (ℓ⁻¹ • z))
    {u : EuclideanSpace ℝ (Fin 3)} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    (hpair : Work.BoseFixB1.pairSum v M ℓ d u Φ = 0) (i j : Fin n) (hij : i ≠ j) :
    ((MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
      {p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) |
        Submission.BoseGases.chiSmallB M ℓ d u p.2 ≠ 0 ∧ v (p.2 - p.1 j) ≠ 0 ∧
        Submission.BoseGases.chiSmallB M ℓ d u (p.1 j) ≠ 0 ∧
        Φ (Function.update p.1 i p.2) ≠ 0} = 0 := by
  classical
  -- the a.e. void statement on the box
  have hae := Work.BoseFixB1S.pairVoidAeB1 (v := v) h hv hv1 hR hv_supp hM hℓ hd hR16 hRχ hden
    (u := u) (n := n) (Ψ := Φ) hΦc hpair
  -- the collapsing map (forget the coordinate `i` of the configuration)
  set F : Submission.BoseGases.X n × E3 → Submission.BoseGases.X n :=
    fun p => Function.update p.1 i p.2 with hF
  have hbad : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      ¬ (Φ x ≠ 0 ∧ Submission.BoseGases.chiSmallB M ℓ d u (x i) * v (x i - x j) *
          Submission.BoseGases.chiSmallB M ℓ d u (x j) ≠ 0) :=
    hae.mono fun x hx ⟨h1, h2⟩ => h2 (hx h1 i j hij)
  -- the pushforward of the product measure along the collapsing map
  have hmp := pushforward_update_abox (n := n) hℓ i
  have hqmp : Measure.QuasiMeasurePreserving F
      ((MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    refine ⟨?_, ?_⟩
    · exact measurable_update'
    · rw [hF, hmp]
      exact Measure.smul_absolutelyContinuous
  have hFae : ∀ᵐ p ∂((MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)).prod
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ))),
      ¬ (Φ (F p) ≠ 0 ∧ Submission.BoseGases.chiSmallB M ℓ d u (F p i) * v (F p i - F p j) *
          Submission.BoseGases.chiSmallB M ℓ d u (F p j) ≠ 0) := hqmp.ae hbad
  have hzero : ((MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)).prod
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
      {p : Submission.BoseGases.X n × E3 |
        Φ (F p) ≠ 0 ∧ Submission.BoseGases.chiSmallB M ℓ d u (F p i) * v (F p i - F p j) *
          Submission.BoseGases.chiSmallB M ℓ d u (F p j) ≠ 0} = 0 := by
    have h := (MeasureTheory.ae_iff
      (μ := ((MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ))))
      (p := fun p : Submission.BoseGases.X n × E3 =>
        ¬ (Φ (F p) ≠ 0 ∧ Submission.BoseGases.chiSmallB M ℓ d u (F p i) * v (F p i - F p j) *
            Submission.BoseGases.chiSmallB M ℓ d u (F p j) ≠ 0))).mp hFae
    simpa only [not_not] using h
  -- the target set is contained in the preimage of the null set
  refine measure_mono_null ?_ hzero
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hp
  refine ⟨h4, ?_⟩
  have hi : F p i = p.2 := by rw [hF]; exact Function.update_self i p.2 p.1
  have hj : F p j = p.1 j := by rw [hF]; exact Function.update_of_ne (Ne.symm hij) p.2 p.1
  rw [hi, hj]
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

end Work.BoseFixB1S
