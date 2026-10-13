import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open MeasureTheory Metric Filter

theorem glueAll {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {V : Set E} (hV : IsOpen V) {U : E → ℂ}
    (h0 : ∀ x ∈ V, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ V ∧
      ∃ g : E → ℂ, ContDiffOn ℝ 0 g (Metric.ball x r) ∧
        U =ᵐ[MeasureTheory.volume.restrict (Metric.ball x r)] g)
    (hn : ∀ (x : E) (n : ℕ), x ∈ V → ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ V ∧
      ∃ g : E → ℂ, ContDiffOn ℝ n g (Metric.ball x r) ∧
        U =ᵐ[MeasureTheory.volume.restrict (Metric.ball x r)] g) :
    ∃ Φ : E → ℂ, (∀ n : ℕ, ContDiffOn ℝ n Φ V) ∧
      U =ᵐ[MeasureTheory.volume.restrict V] Φ := by
  classical
  -- Local data: at every point of `V` a ball contained in `V` together with a
  -- continuous representative of `U` on that ball.
  let R : V → ℝ := fun x => (h0 (x : E) x.2).choose
  let G : V → E → ℂ := fun x => ((h0 (x : E) x.2).choose_spec).2.2.choose
  have hRpos : ∀ x : V, 0 < R x := fun x => ((h0 (x : E) x.2).choose_spec).1
  have hRsub : ∀ x : V, Metric.ball (x : E) (R x) ⊆ V :=
    fun x => ((h0 (x : E) x.2).choose_spec).2.1
  have hGcont : ∀ x : V, ContinuousOn (G x) (Metric.ball (x : E) (R x)) :=
    fun x => (((h0 (x : E) x.2).choose_spec).2.2.choose_spec).1.continuousOn
  have hGae : ∀ x : V,
      U =ᵐ[MeasureTheory.volume.restrict (Metric.ball (x : E) (R x))] G x :=
    fun x => (((h0 (x : E) x.2).choose_spec).2.2.choose_spec).2
  -- The candidate smooth function: patch at each point of `V`.
  let Φ : E → ℂ := fun y => if hy : y ∈ V then G ⟨y, hy⟩ y else 0
  have hΦval : ∀ y (hy : y ∈ V), Φ y = G ⟨y, hy⟩ y := by
    intro y hy
    dsimp only [Φ]
    exact dite_eq_left hy
  -- Two patches agree at every common point of their balls.
  have key : ∀ (x : V) (g : E → ℂ) (s : ℝ), 0 < s →
      Metric.ball (x : E) s ⊆ V → ContinuousOn g (Metric.ball (x : E) s) →
      U =ᵐ[MeasureTheory.volume.restrict (Metric.ball (x : E) s)] g →
      ∀ y ∈ Metric.ball (x : E) s, Φ y = g y := by
    intro x g s hs hsub hg hgae y hy
    have hyV : y ∈ V := hsub hy
    have hyb : y ∈ Metric.ball y (R ⟨y, hyV⟩) := Metric.mem_ball_self (hRpos ⟨y, hyV⟩)
    have hWo : IsOpen (Metric.ball y (R ⟨y, hyV⟩) ∩ Metric.ball (x : E) s) :=
      (Metric.isOpen_ball (x := y) (ε := R ⟨y, hyV⟩)).inter
        (Metric.isOpen_ball (x := (x : E)) (ε := s))
    have hyW : y ∈ Metric.ball y (R ⟨y, hyV⟩) ∩ Metric.ball (x : E) s := ⟨hyb, hy⟩
    have hc1 : ContinuousOn (G ⟨y, hyV⟩)
        (Metric.ball y (R ⟨y, hyV⟩) ∩ Metric.ball (x : E) s) :=
      (hGcont ⟨y, hyV⟩).mono Set.inter_subset_left
    have hc2 : ContinuousOn g (Metric.ball y (R ⟨y, hyV⟩) ∩ Metric.ball (x : E) s) :=
      hg.mono Set.inter_subset_right
    have ha1 : U =ᵐ[MeasureTheory.volume.restrict
        (Metric.ball y (R ⟨y, hyV⟩) ∩ Metric.ball (x : E) s)] G ⟨y, hyV⟩ :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hGae ⟨y, hyV⟩)
    have ha2 : U =ᵐ[MeasureTheory.volume.restrict
        (Metric.ball y (R ⟨y, hyV⟩) ∩ Metric.ball (x : E) s)] g :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hgae
    have heq : Set.EqOn (G ⟨y, hyV⟩) g
        (Metric.ball y (R ⟨y, hyV⟩) ∩ Metric.ball (x : E) s) :=
      MeasureTheory.Measure.eqOn_open_of_ae_eq (ha1.symm.trans ha2) hWo hc1 hc2
    rw [hΦval y hyV]
    exact heq hyW
  refine ⟨Φ, ?_, ?_⟩
  · -- smoothness of `Φ` on `V`
    intro n
    refine contDiffOn_of_locally_contDiffOn ?_
    intro y hy
    obtain ⟨s, hs, hsub, g, hg, hgae⟩ := hn y n hy
    refine ⟨Metric.ball y s, Metric.isOpen_ball (x := y) (ε := s), Metric.mem_ball_self hs, ?_⟩
    refine (hg.mono Set.inter_subset_right).congr ?_
    intro z hz
    exact key ⟨y, hy⟩ g s hs hsub hg.continuousOn hgae z hz.2
  · -- `U = Φ` almost everywhere on `V`
    have hae_ball : ∀ i : V,
        U =ᵐ[MeasureTheory.volume.restrict (Metric.ball (i : E) (R i))] Φ := by
      intro i
      have hbmeas : MeasurableSet (Metric.ball (i : E) (R i)) :=
        (Metric.isOpen_ball (x := (i : E)) (ε := R i)).measurableSet
      have h1 : (MeasureTheory.volume.restrict (Metric.ball (i : E) (R i)))
          {y : E | ¬ (U y = G i y)} = 0 :=
        (MeasureTheory.ae_iff (μ := MeasureTheory.volume.restrict (Metric.ball (i : E) (R i)))
          (p := fun y => U y = G i y)).mp (hGae i)
      have h2 : (MeasureTheory.volume.restrict (Metric.ball (i : E) (R i)))
          {y : E | ¬ (G i y = Φ y)} = 0 := by
        have hsub0 : ({y : E | ¬ (G i y = Φ y)} ∩ Metric.ball (i : E) (R i)) ⊆ (∅ : Set E) := by
          intro z hz
          exact absurd (key i (G i) (R i) (hRpos i) (hRsub i) (hGcont i) (hGae i) z hz.2)
            (fun h => hz.1 h.symm)
        have hz0 : MeasureTheory.volume (∅ : Set E) = 0 := MeasureTheory.measure_empty
        rw [MeasureTheory.Measure.restrict_apply' hbmeas,
          MeasureTheory.measure_mono_null hsub0 hz0]
      have h3 : (MeasureTheory.volume.restrict (Metric.ball (i : E) (R i)))
          {y : E | ¬ (U y = Φ y)} = 0 := by
        have hsub3 : ({y : E | ¬ (U y = Φ y)}) ⊆
            {y : E | ¬ (U y = G i y)} ∪ {y : E | ¬ (G i y = Φ y)} := by
          intro z hz
          by_cases h : U z = G i z
          · exact Or.inr (fun hg => hz (h.trans hg))
          · exact Or.inl h
        exact MeasureTheory.measure_mono_null hsub3 (MeasureTheory.measure_union_null h1 h2)
      exact (MeasureTheory.ae_iff (μ := MeasureTheory.volume.restrict (Metric.ball (i : E) (R i)))
        (p := fun y => U y = Φ y)).mpr h3
    have hcov : V ⊆ ⋃ i : V, Metric.ball (i : E) (R i) := fun y hy =>
      Set.mem_iUnion_of_mem (⟨y, hy⟩ : V) (Metric.mem_ball_self (hRpos ⟨y, hy⟩))
    obtain ⟨I, hIcount, hIcov⟩ :=
      (HereditarilyLindelofSpace.isLindelof V).elim_countable_subcover
        (fun i : V => Metric.ball (i : E) (R i))
        (fun i => Metric.isOpen_ball (x := (i : E)) (ε := R i)) hcov
    have hVeq : V = ⋃ i ∈ I, Metric.ball (i : E) (R i) :=
      le_antisymm hIcov
        (Set.iUnion₂_subset (s := fun i (_ : i ∈ I) => Metric.ball (i : E) (R i))
          (h := fun i (_ : i ∈ I) => hRsub i))
    rw [hVeq]
    exact (MeasureTheory.ae_eq_restrict_biUnion_iff (μ := MeasureTheory.volume)
      (s := fun i : V => Metric.ball (i : E) (R i)) (t := I) (ht := hIcount)
      (f := U) (g := Φ)).mpr (fun i _ => hae_ball i)

end Work.EllipticEst.InteriorRegularity.Q0
