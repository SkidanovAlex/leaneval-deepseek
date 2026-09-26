import Mathlib
import Submission.Work.Drive.meridianFibreDefs
import Submission.Work.Drive.meridianFibreAux
import Submission.Work.Drive.analyticLocalCurve
import Submission.Work.Drive.genericFullDefs
import Submission.Work.Drive.fmfDefs
import Submission.Work.Drive.finite_middles_of_chord
import Submission.Work.Drive.closure_liftedTrisecant_eq_or_tangent
import Submission.Work.Drive.tangentChordLocalCurve
import Submission.Work.Drive.shortSecantsFree_of_noInflection
import Submission.Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
import Submission.Commons.Analysis.CrossProduct.inner_cross3_self_left
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Topology

noncomputable section

theorem countable_of_forall_finite_nhds {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] {S : Set X}
    (h : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (S ∩ U).Finite) : S.Countable := by
  classical
  obtain ⟨b, hbc, _, hb⟩ := TopologicalSpace.exists_countable_basis X
  set b' : Set (Set X) := {B ∈ b | (S ∩ B).Finite} with hb'def
  have hb'c : b'.Countable := hbc.mono (fun B hB => hB.1)
  have hsub : S ⊆ ⋃ B ∈ b', (S ∩ B) := by
    intro s hs
    obtain ⟨U, hUo, hsU, hUfin⟩ := h s hs
    obtain ⟨B, hBb, hsB, hBU⟩ := hb.exists_subset_of_mem_open hsU hUo
    exact Set.mem_biUnion ⟨hBb, Set.Finite.subset hUfin (Set.inter_subset_inter_right S hBU)⟩
      ⟨hs, hsB⟩
  exact Set.Countable.mono hsub (hb'c.biUnion (fun B hB => hB.2.countable))

/-! ## 1. A two-dimensional zero with injective derivative is isolated -/

theorem exists_pos_mul_norm_le_norm_of_injective {L : (ℝ × ℝ) →L[ℝ] Space}
    (hL : Function.Injective L) : ∃ c : ℝ, 0 < c ∧ ∀ v : ℝ × ℝ, c * ‖v‖ ≤ ‖L v‖ := by
  have hcont : Continuous (fun v : ℝ × ℝ => ‖L v‖) := L.continuous.norm
  obtain ⟨c, hcpos, hcle⟩ :=
    (isCompact_sphere (0 : ℝ × ℝ) 1).exists_forall_le' hcont.continuousOn
      (f := fun v : ℝ × ℝ => ‖L v‖) (a := (0 : ℝ)) (fun b hb => by
        have hb1 : ‖b‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hb
        have hbne : b ≠ 0 := by
          intro h0
          rw [h0] at hb1
          simp at hb1
        have hLb : L b ≠ 0 := by
          intro h0
          refine hbne (hL ?_)
          simpa using h0
        exact norm_pos_iff.mpr hLb)
  refine ⟨c, hcpos, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hmem : (‖v‖)⁻¹ • v ∈ Metric.sphere (0 : ℝ × ℝ) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀ (ne_of_gt hnorm)]
    have hkey := hcle _ hmem
    have hLv : ‖L ((‖v‖)⁻¹ • v)‖ = (‖v‖)⁻¹ * ‖L v‖ := by
      rw [map_smul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    rw [hLv] at hkey
    calc c * ‖v‖ ≤ ((‖v‖)⁻¹ * ‖L v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hkey (le_of_lt hnorm)
      _ = ‖L v‖ := by
          rw [mul_assoc, mul_comm (‖L v‖) ‖v‖, ← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hnorm), one_mul]

theorem eq_of_hasFDerivAt_injective {f : ℝ × ℝ → Space} {p : ℝ × ℝ}
    {L : (ℝ × ℝ) →L[ℝ] Space} (hf : HasFDerivAt f L p) (hL : Function.Injective L)
    (hp : f p = 0) : ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℝ × ℝ, f q = 0 → dist q p < ε → q = p := by
  obtain ⟨c, hcpos, hc⟩ := exists_pos_mul_norm_le_norm_of_injective hL
  have hbdd : ∀ᶠ q in 𝓝 p, ‖f q - f p - L (q - p)‖ ≤ (c / 2) * ‖q - p‖ :=
    Asymptotics.isLittleO_iff.mp hf.isLittleO (c := c / 2) (half_pos hcpos)
  obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.mp hbdd
  refine ⟨ε, hεpos, fun q hq hdist => ?_⟩
  have h1 : ‖f q - f p - L (q - p)‖ ≤ (c / 2) * ‖q - p‖ :=
    hball (by rwa [Metric.mem_ball])
  have h2 : c * ‖q - p‖ ≤ ‖L (q - p)‖ := hc (q - p)
  have h3 : ‖L (q - p)‖ ≤ (c / 2) * ‖q - p‖ := by
    have heq : L (q - p) = -(f q - f p - L (q - p)) + (f q - f p) := by abel
    have h4 : ‖L (q - p)‖ ≤ ‖f q - f p - L (q - p)‖ + ‖f q - f p‖ := by
      have h5 : ‖L (q - p)‖ = ‖-(f q - f p - L (q - p)) + (f q - f p)‖ := congrArg norm heq
      calc ‖L (q - p)‖ = ‖-(f q - f p - L (q - p)) + (f q - f p)‖ := h5
        _ ≤ ‖-(f q - f p - L (q - p))‖ + ‖f q - f p‖ := norm_add_le _ _
        _ = ‖f q - f p - L (q - p)‖ + ‖f q - f p‖ := by rw [norm_neg]
    have h5 : ‖f q - f p‖ = 0 := by rw [hq, hp]; simp
    linarith [h4, h1, h5, norm_nonneg (f q - f p - L (q - p))]
  have h6 : c * ‖q - p‖ ≤ (c / 2) * ‖q - p‖ := le_trans h2 h3
  have hnorm : ‖q - p‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖q - p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith [h6, hpos]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-! ## 2. The two tangent-chord maps -/

def tanMapA (r : ℝ → Space) (p : ℝ × ℝ) : Space :=
  cross3 (r (p.1 + p.2) - r p.1) (velocity r p.1)

def tanMapB (r : ℝ → Space) (p : ℝ × ℝ) : Space :=
  cross3 (r (p.1 + p.2) - r p.1) (velocity r (p.1 + p.2))

def tanSetA (r : ℝ → Space) : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ p.2 < period ∧ tanMapA r p = 0}

def tanSetB (r : ℝ → Space) : Set (ℝ × ℝ) :=
  {p | 0 < p.2 ∧ p.2 < period ∧ tanMapB r p = 0}

lemma contDiff_tanMapA {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (tanMapA r) := by
  show ContDiff ℝ ⊤ (fun p : ℝ × ℝ => cross3 (r (p.1 + p.2) - r p.1) (velocity r p.1))
  have h1 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => r (p.1 + p.2)) :=
    hr.smooth.comp (contDiff_fst.add contDiff_snd)
  have h2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => r p.1) := hr.smooth.comp contDiff_fst
  have h3 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => velocity r p.1) := by
    have hv : ContDiff ℝ ⊤ (deriv r) := by
      have h1' : (⊤ : WithTop ℕ∞) + 1 = ⊤ := by simp
      exact h1' ▸ hr.smooth.deriv'
    simpa [velocity, Function.comp_def] using hv.comp contDiff_fst
  have hpair : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (r (p.1 + p.2) - r p.1, velocity r p.1)) :=
    (h1.sub h2).prodMk h3
  have hcross : ContDiff ℝ ⊤ (fun z : Space × Space => cross3 z.1 z.2) := by
    simpa [cross3] using Commons.Analysis.CrossProduct.cross3_contDiff
  exact hcross.comp hpair

lemma contDiff_tanMapB {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (tanMapB r) := by
  show ContDiff ℝ ⊤ (fun p : ℝ × ℝ => cross3 (r (p.1 + p.2) - r p.1) (velocity r (p.1 + p.2)))
  have h1 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => r (p.1 + p.2)) :=
    hr.smooth.comp (contDiff_fst.add contDiff_snd)
  have h2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => r p.1) := hr.smooth.comp contDiff_fst
  have h3 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => velocity r (p.1 + p.2)) := by
    have hv : ContDiff ℝ ⊤ (deriv r) := by
      have h1' : (⊤ : WithTop ℕ∞) + 1 = ⊤ := by simp
      exact h1' ▸ hr.smooth.deriv'
    simpa [velocity, Function.comp_def] using hv.comp (contDiff_fst.add contDiff_snd)
  have hpair : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => (r (p.1 + p.2) - r p.1, velocity r (p.1 + p.2))) :=
    (h1.sub h2).prodMk h3
  have hcross : ContDiff ℝ ⊤ (fun z : Space × Space => cross3 z.1 z.2) := by
    simpa [cross3] using Commons.Analysis.CrossProduct.cross3_contDiff
  exact hcross.comp hpair

/-! ## 3. Isolating the zeros in the two cases -/

lemma hasDerivAt_shift_curve {f : ℝ → Space} (hf : Differentiable ℝ f) (a : ℝ) :
    HasDerivAt (fun s : ℝ => f (a + s)) (deriv f a) 0 := by
  have h := ((hf (a + 0)).hasDerivAt).comp_const_add a 0
  simpa using h

lemma hasDerivAt_tanMapA_first {r : ℝ → Space} (hr : IsSmoothKnot r) (a y : ℝ) :
    HasDerivAt (fun s : ℝ => tanMapA r (a + s, y))
      (cross3 (velocity r (a + y)) (velocity r a)
        + cross3 (r (a + y) - r a) (deriv (deriv r) a)) 0 := by
  have hrd : Differentiable ℝ r := hr.smooth.differentiable (by simp)
  have hvd : Differentiable ℝ (deriv r) := by
    have hv : ContDiff ℝ ⊤ (deriv r) := by
      have h1' : (⊤ : WithTop ℕ∞) + 1 = ⊤ := by simp
      exact h1' ▸ hr.smooth.deriv'
    exact hv.differentiable (by simp)
  have hu1 : HasDerivAt (fun s : ℝ => r ((a + y) + s)) (velocity r (a + y)) 0 := by
    simpa [velocity] using hasDerivAt_shift_curve hrd (a + y)
  have hu2 : HasDerivAt (fun s : ℝ => r (a + s)) (velocity r a) 0 := by
    simpa [velocity] using hasDerivAt_shift_curve hrd a
  have hu : HasDerivAt (fun s : ℝ => r ((a + y) + s) - r (a + s))
      (velocity r (a + y) - velocity r a) 0 := hu1.sub hu2
  have hv : HasDerivAt (fun s : ℝ => velocity r (a + s)) (deriv (deriv r) a) 0 := by
    simpa [velocity] using hasDerivAt_shift_curve hvd a
  have hc := Commons.Analysis.CrossProduct.hasDerivAt_cross3
    (fun s : ℝ => r ((a + y) + s) - r (a + s)) (fun s : ℝ => velocity r (a + s)) hu hv
  have hval : cross3 (velocity r (a + y) - velocity r a) (velocity r (a + 0))
      + cross3 (r ((a + y) + 0) - r (a + 0)) (deriv (deriv r) a)
      = cross3 (velocity r (a + y)) (velocity r a)
        + cross3 (r (a + y) - r a) (deriv (deriv r) a) := by
    simp only [add_zero]
    rw [cross3_sub_left, cross3_self, sub_zero]
  refine (hc.congr_deriv hval).congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall (fun s => ?_)
  simp only [tanMapA]
  rw [show (a + s) + y = (a + y) + s by ring]
  rfl

lemma hasDerivAt_tanMapA_second {r : ℝ → Space} (hr : IsSmoothKnot r) (a y : ℝ) :
    HasDerivAt (fun s : ℝ => tanMapA r (a, y + s))
      (cross3 (velocity r (a + y)) (velocity r a)) 0 := by
  have hrd : Differentiable ℝ r := hr.smooth.differentiable (by simp)
  have hu1 : HasDerivAt (fun s : ℝ => r ((a + y) + s)) (velocity r (a + y)) 0 := by
    simpa [velocity] using hasDerivAt_shift_curve hrd (a + y)
  have hu : HasDerivAt (fun s : ℝ => r ((a + y) + s) - r a) (velocity r (a + y)) 0 :=
    hu1.sub_const (r a)
  have hv : HasDerivAt (fun _ : ℝ => velocity r a) (0 : Space) 0 := hasDerivAt_const 0 _
  have hc := Commons.Analysis.CrossProduct.hasDerivAt_cross3
    (fun s : ℝ => r ((a + y) + s) - r a) (fun _ : ℝ => velocity r a) hu hv
  have hval : cross3 (velocity r (a + y)) (velocity r a)
      + cross3 (r ((a + y) + 0) - r a) (0 : Space)
      = cross3 (velocity r (a + y)) (velocity r a) := by
    rw [cross3_zero_right, add_zero]
  refine (hc.congr_deriv hval).congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall (fun s => ?_)
  simp only [tanMapA]
  rw [show a + (y + s) = (a + y) + s by ring]
  rfl

lemma hasDerivAt_tanMapB_first {r : ℝ → Space} (hr : IsSmoothKnot r) (a y : ℝ) :
    HasDerivAt (fun s : ℝ => tanMapB r (a + s, y))
      (cross3 (r (a + y) - r a) (deriv (deriv r) (a + y))
        - cross3 (velocity r a) (velocity r (a + y))) 0 := by
  have hrd : Differentiable ℝ r := hr.smooth.differentiable (by simp)
  have hvd : Differentiable ℝ (deriv r) := by
    have hv : ContDiff ℝ ⊤ (deriv r) := by
      have h1' : (⊤ : WithTop ℕ∞) + 1 = ⊤ := by simp
      exact h1' ▸ hr.smooth.deriv'
    exact hv.differentiable (by simp)
  have hu1 : HasDerivAt (fun s : ℝ => r ((a + y) + s)) (velocity r (a + y)) 0 := by
    simpa [velocity] using hasDerivAt_shift_curve hrd (a + y)
  have hu2 : HasDerivAt (fun s : ℝ => r (a + s)) (velocity r a) 0 := by
    simpa [velocity] using hasDerivAt_shift_curve hrd a
  have hu : HasDerivAt (fun s : ℝ => r ((a + y) + s) - r (a + s))
      (velocity r (a + y) - velocity r a) 0 := hu1.sub hu2
  have hv : HasDerivAt (fun s : ℝ => velocity r ((a + y) + s))
      (deriv (deriv r) (a + y)) 0 := by
    simpa [velocity] using hasDerivAt_shift_curve hvd (a + y)
  have hc := Commons.Analysis.CrossProduct.hasDerivAt_cross3
    (fun s : ℝ => r ((a + y) + s) - r (a + s))
    (fun s : ℝ => velocity r ((a + y) + s)) hu hv
  have hval : cross3 (velocity r (a + y) - velocity r a) (velocity r ((a + y) + 0))
      + cross3 (r ((a + y) + 0) - r (a + 0)) (deriv (deriv r) (a + y))
      = cross3 (r (a + y) - r a) (deriv (deriv r) (a + y))
        - cross3 (velocity r a) (velocity r (a + y)) := by
    rw [show r ((a + y) + 0) - r (a + 0) = r (a + y) - r a by simp]
    rw [show velocity r ((a + y) + 0) = velocity r (a + y) by simp]
    have h1 : cross3 (velocity r (a + y) - velocity r a) (velocity r (a + y))
        = - cross3 (velocity r a) (velocity r (a + y)) := by
      rw [cross3_sub_left, cross3_self, zero_sub]
    rw [h1]
    abel
  refine (hc.congr_deriv hval).congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall (fun s => ?_)
  simp only [tanMapB]
  rw [show (a + s) + y = (a + y) + s by ring]
  rfl

lemma hasDerivAt_tanMapB_second {r : ℝ → Space} (hr : IsSmoothKnot r) (a y : ℝ) :
    HasDerivAt (fun s : ℝ => tanMapB r (a, y + s))
      (cross3 (r (a + y) - r a) (deriv (deriv r) (a + y))) 0 := by
  have hrd : Differentiable ℝ r := hr.smooth.differentiable (by simp)
  have hvd : Differentiable ℝ (deriv r) := by
    have hv : ContDiff ℝ ⊤ (deriv r) := by
      have h1' : (⊤ : WithTop ℕ∞) + 1 = ⊤ := by simp
      exact h1' ▸ hr.smooth.deriv'
    exact hv.differentiable (by simp)
  have hu : HasDerivAt (fun s : ℝ => r ((a + y) + s) - r a) (velocity r (a + y)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => r ((a + y) + s)) (velocity r (a + y)) 0 := by
      simpa [velocity] using hasDerivAt_shift_curve hrd (a + y)
    exact h1.sub_const (r a)
  have hv : HasDerivAt (fun s : ℝ => velocity r ((a + y) + s))
      (deriv (deriv r) (a + y)) 0 := by
    simpa [velocity] using hasDerivAt_shift_curve hvd (a + y)
  have hc := Commons.Analysis.CrossProduct.hasDerivAt_cross3
    (fun s : ℝ => r ((a + y) + s) - r a) (fun s : ℝ => velocity r ((a + y) + s)) hu hv
  have hval : cross3 (velocity r (a + y)) (velocity r ((a + y) + 0))
      + cross3 (r ((a + y) + 0) - r a) (deriv (deriv r) (a + y))
      = cross3 (r (a + y) - r a) (deriv (deriv r) (a + y)) := by
    rw [show velocity r ((a + y) + 0) = velocity r (a + y) by simp]
    rw [cross3_self, zero_add]
    rw [show r ((a + y) + 0) - r a = r (a + y) - r a by simp]
  refine (hc.congr_deriv hval).congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall (fun s => ?_)
  simp only [tanMapB]
  rw [show a + (y + s) = (a + y) + s by ring]
  rfl

/-! ## 4. The isolation theorems -/

theorem tanMapA_isolated {r : ℝ → Space} (hr : IsSmoothKnot r) (htc : TangentChordGP r)
    {p : ℝ × ℝ} (hy0 : 0 < p.2) (hy1 : p.2 < period) (hzero : tanMapA r p = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℝ × ℝ, tanMapA r q = 0 → dist q p < ε → q = p := by
  have h0 : cross3 (r (p.1 + p.2) - r p.1) (velocity r p.1) = 0 := hzero
  obtain ⟨hneB, hinner⟩ :=
    (htc p.1 (p.1 + p.2) (by linarith) (by linarith)).1 h0
  have hchord_ne : r (p.1 + p.2) - r p.1 ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro hk
    have hcls : ((p.1 : ℝ) : KnotParam) = (((p.1 + p.2 : ℝ)) : KnotParam) :=
      (knotMap_inj_iff hr).mp
        (by rw [knotMap_eq_r hr p.1, knotMap_eq_r hr (p.1 + p.2)]; exact hk.symm)
    exact coe_ne_coe_of_lt hy0 hy1 hcls
  obtain ⟨t, ht⟩ : ∃ t : ℝ, velocity r p.1 = t • (r (p.1 + p.2) - r p.1) := by
    rcases (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
      (r (p.1 + p.2) - r p.1) (velocity r p.1)).mp h0 with h | h
    · exact absurd h hchord_ne
    · exact h
  have htne : t ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ht
    exact hr.regular p.1 ht
  have hVne : cross3 (velocity r (p.1 + p.2)) (velocity r p.1) ≠ 0 := by
    rw [ht, cross3_smul_right, cross3_anticomm, smul_neg]
    exact neg_ne_zero.mpr (smul_ne_zero htne hneB)
  have hUinner : inner ℝ (cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) p.1))
      (velocity r (p.1 + p.2)) ≠ 0 := by
    have h1 : cross3 (velocity r p.1) (deriv (deriv r) p.1)
        = t • cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) p.1) := by
      rw [ht, cross3_smul_left]
    rw [h1, real_inner_smul_left] at hinner
    exact (mul_ne_zero_iff.mp hinner).2
  have hVinner : inner ℝ (cross3 (velocity r (p.1 + p.2)) (velocity r p.1))
      (velocity r (p.1 + p.2)) = 0 :=
    Commons.Analysis.CrossProduct.inner_cross3_self_left _ _
  have hdir1 : (fderiv ℝ (tanMapA r) p) ((1 : ℝ), (0 : ℝ))
      = cross3 (velocity r (p.1 + p.2)) (velocity r p.1)
        + cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) p.1) := by
    have hdiff : DifferentiableAt ℝ (tanMapA r) p :=
      ((contDiff_tanMapA hr).differentiable (by simp)).differentiableAt
    have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
      (H := tanMapA r) (p := p) (e := ((1 : ℝ), (0 : ℝ))) hdiff
    have h2 : HasDerivAt (fun s : ℝ => tanMapA r (p + s • ((1 : ℝ), (0 : ℝ))))
        (cross3 (velocity r (p.1 + p.2)) (velocity r p.1)
          + cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) p.1)) 0 := by
      refine (hasDerivAt_tanMapA_first hr p.1 p.2).congr_of_eventuallyEq ?_
      refine Filter.Eventually.of_forall (fun s => ?_)
      have hpt : p + s • ((1 : ℝ), (0 : ℝ)) = (p.1 + s, p.2) := by
        ext <;> simp [Prod.mk_add_mk, Prod.smul_mk]
      dsimp only
      rw [hpt]
    exact h1.unique h2
  have hdir2 : (fderiv ℝ (tanMapA r) p) ((0 : ℝ), (1 : ℝ))
      = cross3 (velocity r (p.1 + p.2)) (velocity r p.1) := by
    have hdiff : DifferentiableAt ℝ (tanMapA r) p :=
      ((contDiff_tanMapA hr).differentiable (by simp)).differentiableAt
    have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
      (H := tanMapA r) (p := p) (e := ((0 : ℝ), (1 : ℝ))) hdiff
    have h2 : HasDerivAt (fun s : ℝ => tanMapA r (p + s • ((0 : ℝ), (1 : ℝ))))
        (cross3 (velocity r (p.1 + p.2)) (velocity r p.1)) 0 := by
      refine (hasDerivAt_tanMapA_second hr p.1 p.2).congr_of_eventuallyEq ?_
      refine Filter.Eventually.of_forall (fun s => ?_)
      have hpt : p + s • ((0 : ℝ), (1 : ℝ)) = (p.1, p.2 + s) := by
        ext <;> simp [Prod.mk_add_mk, Prod.smul_mk]
      dsimp only
      rw [hpt]
    exact h1.unique h2
  have hker : ∀ d : ℝ × ℝ, (fderiv ℝ (tanMapA r) p) d = 0 → d = 0 := by
    intro d hd
    have hdecomp : d = d.1 • ((1 : ℝ), (0 : ℝ)) + d.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    have hform : (fderiv ℝ (tanMapA r) p) d
        = d.1 • (cross3 (velocity r (p.1 + p.2)) (velocity r p.1)
            + cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) p.1))
          + d.2 • cross3 (velocity r (p.1 + p.2)) (velocity r p.1) := by
      conv_lhs => rw [hdecomp]
      rw [map_add, map_smul, map_smul, hdir1, hdir2]
    have hzero' : d.1 • (cross3 (velocity r (p.1 + p.2)) (velocity r p.1)
            + cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) p.1))
          + d.2 • cross3 (velocity r (p.1 + p.2)) (velocity r p.1) = 0 := by
      rw [← hform]; exact hd
    have hI := congrArg (fun w : Space => inner ℝ w (velocity r (p.1 + p.2))) hzero'
    simp only [inner_add_left, real_inner_smul_left, smul_eq_mul, inner_zero_left] at hI
    simp only [hVinner, zero_add, mul_zero, add_zero] at hI
    have hd1 : d.1 = 0 := (mul_eq_zero.mp hI).resolve_right hUinner
    have hd2 : d.2 = 0 := by
      have h2 : d.2 • cross3 (velocity r (p.1 + p.2)) (velocity r p.1) = 0 := by
        simpa [hd1] using hzero'
      exact (smul_eq_zero.mp h2).resolve_right hVne
    exact Prod.ext hd1 hd2
  have hinj : Function.Injective (fderiv ℝ (tanMapA r) p) := by
    intro d₁ d₂ hd
    have hsub : (fderiv ℝ (tanMapA r) p) (d₁ - d₂) = 0 := by rw [map_sub, hd, sub_self]
    exact sub_eq_zero.mp (hker (d₁ - d₂) hsub)
  have hF : HasFDerivAt (tanMapA r) (fderiv ℝ (tanMapA r) p) p :=
    (((contDiff_tanMapA hr).differentiable (by simp)).differentiableAt).hasFDerivAt
  exact eq_of_hasFDerivAt_injective hF hinj hzero

theorem tanMapB_isolated {r : ℝ → Space} (hr : IsSmoothKnot r) (htc : TangentChordGP r)
    {p : ℝ × ℝ} (hy0 : 0 < p.2) (hy1 : p.2 < period) (hzero : tanMapB r p = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℝ × ℝ, tanMapB r q = 0 → dist q p < ε → q = p := by
  have hzeroA : cross3 (r (p.1 + p.2) - r p.1) (velocity r (p.1 + p.2)) = 0 := hzero
  obtain ⟨hneA, hinner⟩ :=
    (htc p.1 (p.1 + p.2) (by linarith) (by linarith)).2 hzeroA
  have hchord_ne : r (p.1 + p.2) - r p.1 ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro hk
    have hcls : ((p.1 : ℝ) : KnotParam) = (((p.1 + p.2 : ℝ)) : KnotParam) :=
      (knotMap_inj_iff hr).mp
        (by rw [knotMap_eq_r hr p.1, knotMap_eq_r hr (p.1 + p.2)]; exact hk.symm)
    exact coe_ne_coe_of_lt hy0 hy1 hcls
  obtain ⟨s, hs⟩ : ∃ s : ℝ, velocity r (p.1 + p.2) = s • (r (p.1 + p.2) - r p.1) := by
    rcases (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
      (r (p.1 + p.2) - r p.1) (velocity r (p.1 + p.2))).mp hzeroA with h | h
    · exact absurd h hchord_ne
    · exact h
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hs
    exact hr.regular (p.1 + p.2) hs
  have hU'ne : cross3 (velocity r p.1) (velocity r (p.1 + p.2)) ≠ 0 := by
    rw [hs, cross3_smul_right, cross3_anticomm, smul_neg]
    exact neg_ne_zero.mpr (smul_ne_zero hsne hneA)
  have hV'inner : inner ℝ (cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) (p.1 + p.2)))
      (velocity r p.1) ≠ 0 := by
    have h1 : cross3 (velocity r (p.1 + p.2)) (deriv (deriv r) (p.1 + p.2))
        = s • cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) (p.1 + p.2)) := by
      rw [hs, cross3_smul_left]
    rw [h1, real_inner_smul_left] at hinner
    exact (mul_ne_zero_iff.mp hinner).2
  have hU'inner : inner ℝ (cross3 (velocity r p.1) (velocity r (p.1 + p.2)))
      (velocity r p.1) = 0 :=
    Commons.Analysis.CrossProduct.inner_cross3_self_left _ _
  have hdir1 : (fderiv ℝ (tanMapB r) p) ((1 : ℝ), (0 : ℝ))
      = cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) (p.1 + p.2))
        - cross3 (velocity r p.1) (velocity r (p.1 + p.2)) := by
    have hdiff : DifferentiableAt ℝ (tanMapB r) p :=
      ((contDiff_tanMapB hr).differentiable (by simp)).differentiableAt
    have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
      (H := tanMapB r) (p := p) (e := ((1 : ℝ), (0 : ℝ))) hdiff
    have h2 : HasDerivAt (fun s : ℝ => tanMapB r (p + s • ((1 : ℝ), (0 : ℝ))))
        (cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) (p.1 + p.2))
          - cross3 (velocity r p.1) (velocity r (p.1 + p.2))) 0 := by
      refine (hasDerivAt_tanMapB_first hr p.1 p.2).congr_of_eventuallyEq ?_
      refine Filter.Eventually.of_forall (fun s => ?_)
      have hpt : p + s • ((1 : ℝ), (0 : ℝ)) = (p.1 + s, p.2) := by
        ext <;> simp [Prod.mk_add_mk, Prod.smul_mk]
      dsimp only
      rw [hpt]
    exact h1.unique h2
  have hdir2 : (fderiv ℝ (tanMapB r) p) ((0 : ℝ), (1 : ℝ))
      = cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) (p.1 + p.2)) := by
    have hdiff : DifferentiableAt ℝ (tanMapB r) p :=
      ((contDiff_tanMapB hr).differentiable (by simp)).differentiableAt
    have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
      (H := tanMapB r) (p := p) (e := ((0 : ℝ), (1 : ℝ))) hdiff
    have h2 : HasDerivAt (fun s : ℝ => tanMapB r (p + s • ((0 : ℝ), (1 : ℝ))))
        (cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) (p.1 + p.2))) 0 := by
      refine (hasDerivAt_tanMapB_second hr p.1 p.2).congr_of_eventuallyEq ?_
      refine Filter.Eventually.of_forall (fun s => ?_)
      have hpt : p + s • ((0 : ℝ), (1 : ℝ)) = (p.1, p.2 + s) := by
        ext <;> simp [Prod.mk_add_mk, Prod.smul_mk]
      dsimp only
      rw [hpt]
    exact h1.unique h2
  have hker : ∀ d : ℝ × ℝ, (fderiv ℝ (tanMapB r) p) d = 0 → d = 0 := by
    intro d hd
    have hdecomp : d = d.1 • ((1 : ℝ), (0 : ℝ)) + d.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    have hform : (fderiv ℝ (tanMapB r) p) d
        = d.1 • (cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) (p.1 + p.2))
            - cross3 (velocity r p.1) (velocity r (p.1 + p.2)))
          + d.2 • cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) (p.1 + p.2)) := by
      conv_lhs => rw [hdecomp]
      rw [map_add, map_smul, map_smul, hdir1, hdir2]
    have hzero' : d.1 • (cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) (p.1 + p.2))
            - cross3 (velocity r p.1) (velocity r (p.1 + p.2)))
          + d.2 • cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) (p.1 + p.2)) = 0 := by
      rw [← hform]; exact hd
    have hI := congrArg (fun w : Space => inner ℝ w (velocity r p.1)) hzero'
    simp only [inner_add_left, real_inner_smul_left, smul_eq_mul, inner_zero_left] at hI
    rw [inner_sub_left, hU'inner, sub_zero] at hI
    have hsum : d.1 + d.2 = 0 := by
      have hfac : (d.1 + d.2) * inner ℝ (cross3 (r (p.1 + p.2) - r p.1)
          (deriv (deriv r) (p.1 + p.2))) (velocity r p.1) = 0 := by
        rw [add_mul]; exact hI
      exact (mul_eq_zero.mp hfac).resolve_right hV'inner
    have hd2 : d.2 = -d.1 := by linarith
    have hd1 : d.1 = 0 := by
      have hthis := hzero'
      rw [hd2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at hthis
      have harg : (cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) (p.1 + p.2))
            - cross3 (velocity r p.1) (velocity r (p.1 + p.2)))
          - cross3 (r (p.1 + p.2) - r p.1) (deriv (deriv r) (p.1 + p.2))
          = - cross3 (velocity r p.1) (velocity r (p.1 + p.2)) := by abel
      rw [harg, smul_neg] at hthis
      have h2 : d.1 • cross3 (velocity r p.1) (velocity r (p.1 + p.2)) = 0 :=
        neg_eq_zero.mp hthis
      exact (smul_eq_zero.mp h2).resolve_right hU'ne
    exact Prod.ext hd1 (by simp [hd2, hd1])
  have hinj : Function.Injective (fderiv ℝ (tanMapB r) p) := by
    intro d₁ d₂ hd
    have hsub : (fderiv ℝ (tanMapB r) p) (d₁ - d₂) = 0 := by rw [map_sub, hd, sub_self]
    exact sub_eq_zero.mp (hker (d₁ - d₂) hsub)
  have hF : HasFDerivAt (tanMapB r) (fderiv ℝ (tanMapB r) p) p :=
    (((contDiff_tanMapB hr).differentiable (by simp)).differentiableAt).hasFDerivAt
  exact eq_of_hasFDerivAt_injective hF hinj hzero

/-! ## 5. Countability of the tangent columns -/

theorem tanSetA_countable {r : ℝ → Space} (hr : IsSmoothKnot r) (htc : TangentChordGP r) :
    (tanSetA r).Countable := by
  refine countable_of_forall_finite_nhds (fun p hp => ?_)
  obtain ⟨hy0, hy1, hzero⟩ := hp
  obtain ⟨ε, hεpos, hiso⟩ := tanMapA_isolated hr htc hy0 hy1 hzero
  refine ⟨Metric.ball p ε, Metric.isOpen_ball, Metric.mem_ball_self hεpos, ?_⟩
  refine (Set.finite_singleton p).subset (fun q hq => ?_)
  exact Set.mem_singleton_iff.mpr (hiso q hq.1.2.2 (Metric.mem_ball.mp hq.2))

theorem tanSetB_countable {r : ℝ → Space} (hr : IsSmoothKnot r) (htc : TangentChordGP r) :
    (tanSetB r).Countable := by
  refine countable_of_forall_finite_nhds (fun p hp => ?_)
  obtain ⟨hy0, hy1, hzero⟩ := hp
  obtain ⟨ε, hεpos, hiso⟩ := tanMapB_isolated hr htc hy0 hy1 hzero
  refine ⟨Metric.ball p ε, Metric.isOpen_ball, Metric.mem_ball_self hεpos, ?_⟩
  refine (Set.finite_singleton p).subset (fun q hq => ?_)
  exact Set.mem_singleton_iff.mpr (hiso q hq.1.2.2 (Metric.mem_ball.mp hq.2))

theorem tangentColumns_eq_image (r : ℝ → Space) :
    TangentColumns r = (fun p : ℝ × ℝ => p.1) '' (tanSetA r ∪ tanSetB r) := by
  ext ξ
  constructor
  · rintro ⟨y, hy0, hy1, h | h⟩
    · exact ⟨(ξ, y), Or.inl ⟨hy0, hy1, by simpa only [tanMapA] using h⟩, rfl⟩
    · exact ⟨(ξ, y), Or.inr ⟨hy0, hy1, by simpa only [tanMapB] using h⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨hy0, hy1, h⟩ | ⟨hy0, hy1, h⟩
    · exact ⟨p.2, hy0, hy1, Or.inl (by simpa only [tanMapA] using h)⟩
    · exact ⟨p.2, hy0, hy1, Or.inr (by simpa only [tanMapB] using h)⟩

theorem countable_tangentColumns_of_tangentChordGP {r : ℝ → Space} (hr : IsSmoothKnot r) (htc : TangentChordGP r) :
    (TangentColumns r).Countable := by
  rw [tangentColumns_eq_image]
  exact ((tanSetA_countable hr htc).union (tanSetB_countable hr htc)).image _

end

open LeanEval.KnotTheory.Quadrisecant in
/-- **The bad meridian columns of the lifted trisecant locus are countable.**  For a smooth knot in
transverse general position, without inflections and with non-degenerate tangent chords, the set of
columns `ξ` over which the lifted trisecant locus has an *infinite* vertical trace is countable.

Route (all inputs already exist in the workspace; the final counting is
`Work.Drive.countable_verticalColumn`, proved unconditionally by a colleague).

Let `T ξ = {y | (ξ, y) ∈ liftedTrisecant r}` be the trace and suppose it is infinite.  Every point of
the trace carries a strict middle (`exists_middle_of_mem_liftedTrisecant`), and for a fixed chord
only finitely many middles exist (`finite_middles_of_chord`), so the slice
`S ξ = {(b, m) | collinearityValue r ξ b m = 0 ∧ r m ∈ openSegment (r ξ) (r b)}` is infinite.  Reduce
the middle `m` modulo the period (the collinearity and the middle predicate are period-invariant in
`m`, see the period-shift facts about `collPartialB`/`collPartialM`), and use the short-secant bound
`shortSecantsFree_of_noInflection` (which needs `hinfl`) to place `S ξ` in the compact set
`{ξ} × [δ, period - δ] × [0, period]`.  So `S ξ` has a cluster point `q = (ξ, b, m)`; the triple is
collinear and `r m` lies on the *closed* chord.

Case A (the cluster point is off-diagonal, i.e. the classes of `ξ`, `b`, `m` are pairwise distinct):
then `r m` is *strictly* inside the chord, so `q` is a point of `TrisecantZeroSet r`, and the points
of `S ξ` form a sequence of off-diagonal collinear points converging to it: this is exactly the
hypothesis of the colleague's `Work.Drive.verticalColumn_of_sliceAccumulates` (with `hg`), which
gives `ξ ∈ VerticalColumn r`.

Case B (the cluster point is diagonal: `m` is congruent to `ξ` or to `b` modulo the period, i.e. the
middles escape to an endpoint of the chord): the endgame facts `cross_zero_of_tendsto_middle_endpoint_a`
and `cross_zero_of_tendsto_middle_endpoint_b` (both in
`Submission/Work/Drive/closure_liftedTrisecant_eq_or_tangent.lean`) then say that the limit chord
`{r ξ, r b}` is *tangent* to the knot at the endpoint the middle escaped to, i.e.
`cross3 (r b - r ξ) (velocity r ξ) = 0` or `cross3 (r b - r ξ) (velocity r b) = 0`: so
`ξ ∈ TangentColumns r` (`Submission/Work/Drive/fmfDefs.lean`) with the witness `b - ξ ∈ (0, period)`.

Hence the bad set is contained in `VerticalColumn r ∪ TangentColumns r`.  The first is countable
(`countable_verticalColumn`).  For the second: `htc` is precisely the statement that the map
`(x, y) ↦ cross3 (r (x + y) - r x) (velocity r x)` has rank two at every tangent-chord pair with
`0 < y < period`, so every such pair is *isolated*; a subset of the second-countable space `ℝ × ℝ`
all of whose points are isolated is countable
(`Work.Drive.countable_of_locallyFinite_of_secondCountable`, or a direct argument), and the columns
are the images of the pairs under the first projection.  The boundary `y → 0` and `y → period` is
excluded by the second-order expansion with `hinfl` (the chord is `(1/2) y² cross3 (r'' x) (velocity x)`
to leading order, non-zero by `hinfl`); the tangency-at-the-second-endpoint clause is the same
argument for `htc`'s second conjunct.

A countable union of countable sets is countable, so the bad columns are countable.  Since `ℝ` is
uncountable, there is then a column whose trace is finite, i.e. `FiniteMeridianFibre r`; this is the
missing input of `Work.Drive.finiteMeridianFibre_of_tangentChordGP` and of the corrected crux's
brick (d′). -/
theorem countable_badTraceColumns {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hg : TorusGeneralPositionTransverse r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (htc : TangentChordGP r) :
    {ξ : ℝ | ¬ (liftedTrisecant r ∩ {q : ℝ × ℝ | q.1 = ξ}).Finite}.Countable := by
  have hcount : (TangentColumns r ∪ VerticalColumn r).Countable :=
    (countable_tangentColumns_of_tangentChordGP hr htc).union (countable_verticalColumn r)
  refine Set.Countable.mono ?_ hcount
  intro ξ hξ
  rcases fmf_bad_imp_tangent_or_vertical hr hg hinfl ξ hξ with h | h
  · exact Or.inl h
  · exact Or.inr h

end Work.Drive
