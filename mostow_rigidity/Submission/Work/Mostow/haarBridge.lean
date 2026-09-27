import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.HaarBoost
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.VolDefs
import Submission.Work.Mostow.volH_null_linear
import Submission.Work.Mostow.fix_subset_hyperplane
import Submission.Work.Mostow.haar_action_facts
import Submission.Work.Mostow.haar_map_eq_smul_volH
import Submission.Work.Mostow.bridge_core

/-!
# Area B — the Haar-to-hyperbolic-volume bridge

`BridgeProp n` says: a discrete subgroup of `PO n 1` with a Haar fundamental domain of finite
covolume has a `volH`-fundamental domain of finite volume.

The pieces used here:
* `Work.Mostow.fix_subset_hyperplane` : a nontrivial isometry fixes only a set contained in the
  zero set of a nonzero linear functional on the hyperboloid;
* `Work.Mostow.volH_null_linear` : such a zero set is `volH`-null;
* `Work.Mostow.haar_action_facts` : `Ksub` is compact; a discrete `Γ` is countable and closed,
  acts properly discontinuously, and closest orbit points exist;
* `Work.Mostow.haar_map_eq_smul_volH` : the orbit map pushes Haar measure to a multiple of `volH`.

This file proves: the union of the fixed point sets of the elements `≠ 1` of a countable discrete
`Γ` is `volH`-null (hence there is `o` with trivial stabiliser), the Dirichlet domain at `o` is a
`volH`-fundamental domain, and the covolume of `Γ` equals the `volH`-volume of that domain up to
the proportionality constant.  The target `haarBridge` follows.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Topology

noncomputable section

variable {n : ℕ}

/-! ## `volH` is nonzero -/

theorem volH_ne_zero (n : ℕ) : volH n ≠ 0 := by
  intro hzero
  have hb : (0 : ℝ≥0∞) < (volume : Measure (E n)) (Metric.ball (0 : E n) 1) :=
    Metric.isOpen_ball.measure_pos (volume : Measure (E n)) ⟨0, Metric.mem_ball_self one_pos⟩
  have h1 : (ENNReal.ofReal ((Real.sqrt 2)⁻¹)) * (volume : Measure (E n))
        (Metric.ball (0 : E n) 1)
      ≤ ∫⁻ u in Metric.ball (0 : E n) 1, hdens u ∂(volume : Measure (E n)) := by
    rw [← setLIntegral_const (μ := (volume : Measure (E n)))
      (s := Metric.ball (0 : E n) 1) (c := ENNReal.ofReal ((Real.sqrt 2)⁻¹))]
    exact setLIntegral_mono' Metric.isOpen_ball.measurableSet fun u hu => by
      rw [Metric.mem_ball, dist_zero_right] at hu
      rw [hdens, ENNReal.ofReal_le_ofReal_iff (le_of_lt (inv_pos.mpr (tpart_pos u)))]
      rw [inv_le_inv₀ (Real.sqrt_pos.2 (by norm_num)) (tpart_pos u)]
      rw [tpart]
      apply Real.sqrt_le_sqrt
      nlinarith [norm_nonneg u]
  have hpos : (0 : ℝ≥0∞) < volH n (Metric.ball (0 : E n) 1) := by
    rw [volH_def, withDensity_apply _ Metric.isOpen_ball.measurableSet]
    exact lt_of_lt_of_le
      (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' (ne_of_gt hb)) h1
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-! ## Step 1: a point with trivial `Γ`-stabiliser -/

theorem exists_trivial_stabiliser (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) [Countable Γ] (hΓd : IsDiscrete (Γ : Set (PO n 1))) :
    ∃ o : E n, ∀ γ : Γ, γ • o = o → γ = 1 := by
  classical
  have hnull : ∀ γ : Γ, γ ≠ 1 → volH n {u : E n | γ • u = u} = 0 := by
    intro γ hγ
    obtain ⟨l, hl, hfix⟩ := fix_subset_hyperplane n hA (γ : PO n 1) (by simpa using hγ)
    set a : E n := WithLp.toLp 2 (fun i => l (Sum.inl i)) with ha
    set b : ℝ := l (Sum.inr 0) with hb
    have hsubset : {u : E n | γ • u = u} ⊆ {u : E n | inner ℝ a u + b * tpart u = 0} := by
      intro u hu
      have h0 := hfix u hu
      simp only [Set.mem_ofPred_eq]
      rw [← h0, Fintype.sum_sum_type, Fin.sum_univ_one]
      rw [inner_eq_sum, ha, hb]
      simp only [WithLp.ofLp_toLp, hlift_inl, hlift_inr]
    refine measure_mono_null hsubset (volH_null_linear n a b ?_)
    by_cases ha0 : a = 0
    · right
      intro hb0
      apply hl
      funext i
      rcases i with i | i
      · have h2 : a i = 0 := by
          have h3 := congrArg (fun w : E n => w i) ha0
          simpa using h3
        simpa [ha] using h2
      · obtain rfl : i = 0 := Subsingleton.elim i 0
        simpa [hb] using hb0
    · exact Or.inl ha0
  have hUnion : volH n (⋃ γ : {γ : Γ // γ ≠ 1}, {u : E n | (γ : Γ) • u = u}) = 0 := by
    rw [measure_iUnion_null_iff]
    intro γ
    exact hnull γ γ.2
  have hne : (⋃ γ : {γ : Γ // γ ≠ 1}, {u : E n | (γ : Γ) • u = u}) ≠ Set.univ := by
    intro h
    rw [h] at hUnion
    exact volH_ne_zero n (MeasureTheory.Measure.measure_univ_eq_zero.1 hUnion)
  obtain ⟨o, ho⟩ : ∃ o : E n, o ∉ ⋃ γ : {γ : Γ // γ ≠ 1}, {u : E n | (γ : Γ) • u = u} := by
    by_contra hmem
    refine hne (Set.eq_univ_of_forall fun x => ?_)
    by_contra hx
    exact hmem ⟨x, hx⟩
  refine ⟨o, fun γ hγ => ?_⟩
  by_contra hne1
  exact ho (Set.mem_iUnion.2 ⟨⟨γ, hne1⟩, hγ⟩)

/-! ## The bridge -/

theorem haarBridge (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    BridgeProp n := by
  intro Γ hdisc _hfund hcov
  obtain ⟨-, hact⟩ := haar_action_facts n hA hI
  obtain ⟨hcount, -, -, hmin⟩ := hact Γ hdisc
  haveI : Countable Γ := hcount
  obtain ⟨o, ho⟩ := exists_trivial_stabiliser n hA hI Γ hdisc
  obtain ⟨-, hc, hc0, hctop, hprop⟩ := haar_map_eq_smul_volH n hA hI
  obtain ⟨D, hD, hDfin⟩ :=
    bridge_core n hA hI Γ o ho (fun x => hmin o x) ⟨hc, hc0, hctop, hprop⟩ hcov
  exact ⟨hdisc, D, hD, hDfin⟩

end

end Work.Mostow
