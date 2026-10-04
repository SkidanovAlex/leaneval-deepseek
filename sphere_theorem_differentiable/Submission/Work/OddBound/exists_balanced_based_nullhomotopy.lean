import Mathlib
import Submission.Work.OddBound.minimax.exists_based_null_homotopy
import Submission.Work.UniformGridModulus.exists_uniform_modulus_of_continuous_family
import Submission.Work.PeriodicLength.curveLength_eq_mul_of_periodic_of_affine
import Submission.Work.OddBound.polygonValue.continuousOn_GExp_smul_of_minimising
import Submission.Work.OddBound.polygonValue.brokenGeodesicDefs
import Submission.Work.OddBound.polygonValue.balancing.continuous_fract_comp
import Submission.Work.OddBound.polygonValue.balancing.exists_strictMono_enum
import Submission.Work.OddBound.polygonValue.balancing.continuousRiemannianDist
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal
import Submission.Work.OddBound.liftPiecewise.exists_lift_of_piecewise_short
import Submission.BrokenLength
import Submission.UniformInj
import Submission.SegmentDomain
import Submission.EDist

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.OddBound

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec


/-- **The speed of a `1`-periodic curve is `1`-periodic.**  This is the statement of
`Work.PeriodicLength.curveSpeed_add_one`, which is `private` in the module
`Submission.Work.PeriodicLength.curveLength_eq_mul_of_periodic_of_affine`; we restate it here
because we need it for an arbitrary slice `s ↦ Hf s t` of our homotopy. -/
private lemma curveSpeed_add_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {f : ℝ → M} (hper : ∀ r : ℝ, f (r + 1) = f r) (t : ℝ) :
    Submission.Length.curveSpeed (I := I) f (t + 1) = Submission.Length.curveSpeed (I := I) f t := by
  by_cases hd : MDiffAt f t
  · -- `f` is differentiable at `t`: transport the velocity along the translation `r ↦ r - 1`.
    have hvel : Submission.Geodesic.curveVelocity (I := I) f (t + 1)
        = Submission.Geodesic.curveVelocity (I := I) f t := by
      have h1 := Submission.GeodesicGlobal2.curveVelocity_comp_sub (I := I) (σ := f) (t := t)
        (T := 1) hd
      have h2 : (fun s : ℝ => f (s - 1)) = f := by
        funext s
        simpa using (hper (s - 1)).symm
      have h3 := Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I)
        (t := t + 1) (γ := fun s : ℝ => f (s - 1)) (γ' := f) (Filter.EventuallyEq.of_eq h2)
      exact h3.symm.trans h1
    simp only [Submission.Length.curveSpeed_def]
    rw [hper t, hvel]
  · -- `f` is not differentiable at `t`: then neither at `t + 1`, and both speeds are `0`.
    have h0 : Submission.Geodesic.curveVelocity (I := I) f t = 0 := by
      show (mfderiv 𝓘(ℝ) I f t) (1 : ℝ) = 0
      rw [mfderiv_zero_of_not_mdifferentiableAt hd]
      exact zero_apply (1 : ℝ)
    have hnd : ¬ MDiffAt f (t + 1) := by
      intro hf1
      have hadd : MDiffAt (fun s : ℝ => s + 1) t := by
        rw [mdifferentiableAt_iff_differentiableAt]
        exact (differentiableAt_id (x := t)).add_const (1 : ℝ)
      have hcomp : MDiffAt (f ∘ (fun s : ℝ => s + 1)) t := hf1.comp t hadd
      have heq : f ∘ (fun s : ℝ => s + 1) = f := by
        funext s
        exact hper s
      exact hd (heq ▸ hcomp)
    have h0' : Submission.Geodesic.curveVelocity (I := I) f (t + 1) = 0 := by
      show (mfderiv 𝓘(ℝ) I f (t + 1)) (1 : ℝ) = 0
      rw [mfderiv_zero_of_not_mdifferentiableAt hnd]
      exact zero_apply (1 : ℝ)
    have hs0 : Submission.Length.curveSpeed (I := I) f t = 0 := by
      simp only [Submission.Length.curveSpeed_def]
      rw [h0, inner_zero_left, Real.sqrt_zero]
    have hs1 : Submission.Length.curveSpeed (I := I) f (t + 1) = 0 := by
      simp only [Submission.Length.curveSpeed_def]
      rw [h0', inner_zero_left, Real.sqrt_zero]
    rw [hs1, hs0]

theorem exists_balanced_based_nullhomotopy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    [SimplyConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {L : ℝ} (hL : 0 < L) {γ : ℝ → M}
    (hγsm : ContMDiff 𝓘(ℝ) I ∞ γ)
    (hγper : ∀ s : ℝ, γ (s + L) = γ s) (hγ0 : γ 0 = p)
    (hγbal : ∀ s : ℝ,
      Submission.Length.curveSpeed (I := I) (fun r : ℝ => γ (L * r)) s
        = Submission.Length.curveLength (I := I) (fun r : ℝ => γ (L * r)) 0 1) :
    ∃ (Hf : ℝ → ℝ → M) (B : ℝ), 0 < B ∧
      Continuous (fun q : ℝ × ℝ => Hf q.1 q.2) ∧
      (∀ s t : ℝ, Hf (s + 1) t = Hf s t) ∧
      (∀ t : ℝ, Hf 0 t = p) ∧
      (∀ s : ℝ, Hf s 0 = γ (L * s)) ∧
      (∀ s : ℝ, Hf s 1 = p) ∧
      (∀ t : ℝ, ∃ (k : ℕ) (a : Fin (k + 1) → ℝ),
        StrictMono a ∧ a 0 = 0 ∧ a (Fin.last k) = 1 ∧
        ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => Hf s t)
          (Set.Icc (a j.castSucc) (a j.succ))) ∧
      (∀ t : ℝ, Submission.Length.curveLength (I := I) (fun s : ℝ => Hf s t) 0 1 ≤ B) ∧
      (∀ t s : ℝ,
        Submission.Length.curveLength (I := I) (fun r : ℝ => Hf r t) 0 s
          = s * Submission.Length.curveLength (I := I) (fun r : ℝ => Hf r t) 0 1) := by
  classical
  -- ## The loop `sg : s ↦ γ (L s)`
  set sg : ℝ → M := fun s => γ (L * s) with hsg
  have hsg_sm : ContMDiff 𝓘(ℝ) I ∞ sg := by
    rw [hsg]
    exact hγsm.comp ((contMDiff_const : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun _ : ℝ => L)).mul
      (contMDiff_id : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun s : ℝ => s)))
  have hsg_cont : Continuous sg := hsg_sm.continuous
  have hsg_per : ∀ s : ℝ, sg (s + 1) = sg s := by
    intro s
    rw [hsg]
    simp only [mul_add, mul_one]
    exact hγper (L * s)
  have hsg0 : sg 0 = p := by simp [hsg, hγ0]
  have hsg1 : sg 1 = p := by simpa using (hsg_per 0).trans hsg0
  set ℓ : ℝ := Submission.Length.curveLength (I := I) sg 0 1 with hℓ
  have hspeed : ∀ s : ℝ, Submission.Length.curveSpeed (I := I) sg s = ℓ := by
    intro s
    rw [hℓ]
    exact hγbal s
  have hℓnonneg : 0 ≤ ℓ := by
    rw [hℓ]
    exact Submission.Length.curveLength_nonneg (I := I) sg (by norm_num)
  rcases lt_or_ge 0 ℓ with hℓpos | hℓnp
  · -- ===================== main case `0 < ℓ` =====================
    -- ## (1) the continuous based null homotopy of `sg`
    obtain ⟨Hm, hHmcont, hHmper, hHm0, hHm1, hHm2⟩ :=
      Work.OddBound.minimax.exists_based_null_homotopy (I := I)
        (p := p) (γ := sg) hsg_cont hsg_per hsg0
    -- ## (2) the uniform injectivity radius, uniform continuity of `Hm`, and the grid
    obtain ⟨ρ, hρpos, hρinj⟩ :=
      Submission.UniformInj.exists_pos_injAllAtLeast (I := I) (cov := cov) hmet
    haveI hcrb : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
    -- ## (2bis) the uniform modulus of continuity of `Hm` in the second variable
    obtain ⟨δ, hδpos, hδ⟩ :=
      Work.UniformGridModulus.exists_uniform_modulus_of_continuous_family (I := I)
        (F := Hm) hHmcont hρpos
    obtain ⟨Kn, hKnpos, hKδ⟩ : ∃ Kn : ℕ, 0 < Kn ∧ 1 / (Kn : ℝ) < δ := by
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
      exact ⟨n + 1, Nat.succ_pos n, by simpa [Nat.cast_add, Nat.cast_one] using hn⟩
    have hKnn : (0:ℝ) < (Kn : ℝ) := by exact_mod_cast hKnpos
    -- the grid in the homotopy parameter
    let u : ℕ → ℝ := fun j => min ((j : ℝ) / (Kn : ℝ)) 1
    have hu_mem : ∀ j : ℕ, u j ∈ Set.Icc (0:ℝ) 1 := by
      intro j
      exact ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
    have hu_self : ∀ j : ℕ, j ≤ Kn → u j = (j : ℝ) / (Kn : ℝ) := by
      intro j hj
      exact min_eq_left ((div_le_one hKnn).mpr (by exact_mod_cast hj))
    have hu_zero : u 0 = 0 := by
      rw [hu_self 0 (Nat.zero_le _)]; simp
    have hu_succ : ∀ j : ℕ, |u (j+1) - u j| ≤ 1 / (Kn : ℝ) := by
      intro j
      rcases lt_or_ge j Kn with hj | hj
      · have h1 : u j = (j:ℝ)/Kn := hu_self j hj.le
        have h2 : u (j+1) = ((j:ℝ)+1)/Kn := by
          rw [hu_self (j+1) (by omega)]; push_cast; ring_nf
        rw [h1, h2, ← sub_div, add_sub_cancel_left]
        rw [abs_of_nonneg (by positivity)]
      · have h1 : u j = 1 := by
          refine min_eq_right ?_
          rw [le_div_iff₀ hKnn, one_mul]
          exact_mod_cast hj
        have h2 : u (j+1) = 1 := by
          refine min_eq_right ?_
          rw [le_div_iff₀ hKnn, one_mul]
          exact_mod_cast (by omega : Kn ≤ j + 1)
        rw [h1, h2, sub_self, abs_zero]
        positivity
    -- the vertices of the return path: the geodesic approximation of `u ↦ Hm (1 - c) u`
    let W : ℕ → ℝ → M := fun j t => Hm (1 - polygonValue.clamp01 t) (u j)
    have hW_cont : ∀ j : ℕ, Continuous (fun t : ℝ => W j t) := by
      intro j
      change Continuous (fun t : ℝ => Hm (1 - polygonValue.clamp01 t) (u j))
      have h : Continuous (fun t : ℝ => (1 - polygonValue.clamp01 t, u j)) :=
        (continuous_const.sub polygonValue.clamp01_continuous).prodMk continuous_const
      exact hHmcont.comp h
    have hW0 : ∀ j : ℕ, W j 0 = p := by
      intro j
      have h1 : (1:ℝ) - polygonValue.clamp01 0 = 1 := by
        rw [polygonValue.clamp01_eq_zero_of_nonpos le_rfl]; ring
      have h2 : Hm 1 (u j) = Hm 0 (u j) := by simpa using hHmper 0 (u j)
      show Hm (1 - polygonValue.clamp01 0) (u j) = p
      rw [h1, h2]
      exact hHm0 (u j)
    have hW1 : ∀ j : ℕ, W j 1 = p := by
      intro j
      have h1 : (1:ℝ) - polygonValue.clamp01 1 = 0 := by
        rw [polygonValue.clamp01_eq_self zero_le_one le_rfl]; ring
      show Hm (1 - polygonValue.clamp01 1) (u j) = p
      rw [h1]
      exact hHm0 (u j)
    have hW0base : ∀ t : ℝ, W 0 t = sg (1 - polygonValue.clamp01 t) := by
      intro t
      show Hm (1 - polygonValue.clamp01 t) (u 0) = sg (1 - polygonValue.clamp01 t)
      rw [hu_zero]
      exact hHm1 _
    have hshort : ∀ (j : ℕ) (t : ℝ),
        Manifold.riemannianEDist I (W j t) (W (j+1) t) < ENNReal.ofReal ρ := by
      intro j t
      have ht : 1 - polygonValue.clamp01 t ∈ Set.Icc (0:ℝ) 1 :=
        ⟨by linarith [polygonValue.clamp01_le_one t],
         by linarith [polygonValue.clamp01_nonneg t]⟩
      have hdist : |u j - u (j+1)| < δ := by
        rw [abs_sub_comm]
        exact lt_of_le_of_lt (hu_succ j) hKδ
      exact hδ _ _ _ ht (hu_mem j) (hu_mem (j+1)) hdist
    -- ## (3) the minimising vectors of the return path
    have hvecEx : ∀ (j : ℕ) (t : ℝ), ∃ v : TangentSpace I (W j t),
        v ∈ Submission.SegmentDomain.segmentDomain hmet (W j t) ∧
          Submission.GlobalExp.GExp (cov := cov) hmet (W j t) v = W (j+1) t := by
      intro j t
      exact (Submission.SegmentDomain.exists_unique_segmentDomain_vec (I := I) (cov := cov)
        hmet htor (hinj := hρinj (W j t)) (y := W (j+1) t) (hy := hshort j t)).exists
    let vec : (j : ℕ) → (t : ℝ) → TangentSpace I (W j t) := fun j t => Classical.choose (hvecEx j t)
    have vec_GExp : ∀ (j : ℕ) (t : ℝ),
        Submission.GlobalExp.GExp (cov := cov) hmet (W j t) (vec j t) = W (j+1) t := by
      intro j t
      exact (Classical.choose_spec (hvecEx j t)).2
    have vec_norm : ∀ (j : ℕ) (t : ℝ),
        Manifold.riemannianEDist I (W j t) (W (j+1) t) = ENNReal.ofReal ‖vec j t‖ := by
      intro j t
      have h := Submission.SegmentDomain.edist_GExp_eq_norm_of_mem_segmentDomain (I := I)
        (cov := cov) hmet htor (Classical.choose_spec (hvecEx j t)).1
      rwa [vec_GExp j t] at h
    have vec_norm_lt : ∀ (j : ℕ) (t : ℝ), ‖vec j t‖ < ρ := by
      intro j t
      have h := hshort j t
      rw [vec_norm j t] at h
      exact (ENNReal.ofReal_lt_ofReal_iff hρpos).mp h
    -- ## (4) the pieces: the `σ`-arc, the geodesic return path, and the arclength scan
    let Ln : ℕ → ℝ → ℝ := fun i t =>
      if i = 0 then (1 - polygonValue.clamp01 t) * ℓ else ‖vec (i - 1) t‖
    let Pf : ℕ → ℝ → ℝ := fun i t => ∑ j ∈ Finset.range i, Ln j t
    let kap : ℕ := Kn + 1
    let Tot : ℝ → ℝ := fun t => Pf kap t
    let C : ℕ → ℝ → ℝ → M := fun i x t =>
      if i = 0 then sg (x * (1 - polygonValue.clamp01 t))
      else Submission.GlobalExp.GExp (cov := cov) hmet (W (i-1) t) (x • vec (i-1) t)
    let idx : ℝ → ℝ → ℕ := fun a t =>
      if h : ∃ j : ℕ, j < kap ∧ a ≤ Pf (j+1) t then Nat.find h else 0
    let Pt : ℝ → ℝ → M := fun a t => C (idx a t) ((a - Pf (idx a t) t) / Ln (idx a t) t) t
    let Hf : ℝ → ℝ → M := fun s t =>
      Pt (Tot (polygonValue.clamp01 t) * Int.fract s) (polygonValue.clamp01 t)
    -- ## (5) basic facts about the piece data
    have hkap : 0 < kap := by simp [kap]
    have Ln_nonneg : ∀ (i : ℕ) (t : ℝ), 0 ≤ Ln i t := by
      intro i t
      rcases i with _ | m
      · show 0 ≤ (1 - polygonValue.clamp01 t) * ℓ
        exact mul_nonneg (by linarith [polygonValue.clamp01_le_one t]) hℓnonneg
      · show 0 ≤ ‖vec m t‖
        exact norm_nonneg _
    have Pf_zero : ∀ t : ℝ, Pf 0 t = 0 := by
      intro t; simp [Pf]
    have Pf_succ : ∀ (i : ℕ) (t : ℝ), Pf (i+1) t = Pf i t + Ln i t := by
      intro i t; simp [Pf, Finset.sum_range_succ]
    have Pf_mono : ∀ {i j : ℕ} (h : i ≤ j) (t : ℝ), Pf i t ≤ Pf j t := by
      intro i j h t
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
        (fun k _ _ => Ln_nonneg k t)
    have Pf_le_Tot : ∀ (i : ℕ) (t : ℝ), i ≤ kap → Pf i t ≤ Tot t :=
      fun i t hi => Pf_mono hi t
    have Tot_nonneg : ∀ t : ℝ, 0 ≤ Tot t := by
      intro t
      have h := Pf_mono (Nat.zero_le kap) t
      rw [Pf_zero t] at h
      exact h
    -- the vertex in front of the piece `i`
    let Vx : ℕ → ℝ → M := fun i t => if i = 0 then p else W (i-1) t
    have C_zero : ∀ (i : ℕ) (t : ℝ), C i 0 t = Vx i t := by
      intro i t
      rcases i with _ | m
      · simp only [Vx, if_true]
        show sg (0 * (1 - polygonValue.clamp01 t)) = p
        simp [hsg0]
      · simp only [Vx, Nat.succ_ne_zero, if_false]
        show Submission.GlobalExp.GExp (cov := cov) hmet (W m t) ((0:ℝ) • vec m t) = W (m + 1 - 1) t
        rw [zero_smul, Submission.GlobalExp.GExp_zero]
        simp
    have C_one : ∀ (i : ℕ) (t : ℝ), C i 1 t = Vx (i+1) t := by
      intro i t
      rcases i with _ | m
      · simp only [Vx, Nat.succ_ne_zero, if_false]
        show sg (1 * (1 - polygonValue.clamp01 t)) = W (0 + 1 - 1) t
        rw [one_mul]
        rw [show (0 + 1 - 1 : ℕ) = 0 from rfl]
        exact (hW0base t).symm
      · simp only [Vx, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        show Submission.GlobalExp.GExp (cov := cov) hmet (W m t) ((1:ℝ) • vec m t) = W (m+1) t
        rw [one_smul]
        exact vec_GExp m t
    have C_junc : ∀ (i : ℕ) (t : ℝ), C i 1 t = C (i+1) 0 t := by
      intro i t
      rw [C_one i t, C_zero (i+1) t]
    have C_const : ∀ (i : ℕ) (t : ℝ), Ln i t = 0 → ∀ x y : ℝ, C i x t = C i y t := by
      intro i t hL x y
      rcases i with _ | m
      · have hc1 : (1 : ℝ) - polygonValue.clamp01 t = 0 := by
          have h := hL
          rw [show Ln 0 t = (1 - polygonValue.clamp01 t) * ℓ from rfl] at h
          rcases mul_eq_zero.mp h with h' | h'
          · exact h'
          · exact absurd h' (ne_of_gt hℓpos)
        show sg (x * (1 - polygonValue.clamp01 t)) = sg (y * (1 - polygonValue.clamp01 t))
        rw [hc1, mul_zero, mul_zero]
      · have hv : vec m t = 0 := by
          have h := hL
          rw [show Ln (m+1) t = ‖vec m t‖ from rfl] at h
          exact norm_eq_zero.mp h
        show Submission.GlobalExp.GExp (cov := cov) hmet (W m t) (x • vec m t)
          = Submission.GlobalExp.GExp (cov := cov) hmet (W m t) (y • vec m t)
        rw [hv, smul_zero, smul_zero]
    -- the vertex chain: if the intermediate pieces have zero length, the vertices agree
    have vertex_chain : ∀ (i j : ℕ) (t : ℝ), i ≤ j → Pf i t = Pf j t → Vx i t = Vx j t := by
      intro i j t hij
      induction j, hij using Nat.le_induction with
      | base => intro _; rfl
      | succ n hin ih =>
          intro hPf
          have hlen : Ln n t = 0 := by
            have h1 := Pf_succ n t
            have h2 : Pf i t ≤ Pf n t := Pf_mono hin t
            have h3 : 0 ≤ Ln n t := Ln_nonneg n t
            linarith
          have hrec : Pf i t = Pf n t := by
            have h1 := Pf_succ n t
            rw [hlen] at h1
            linarith
          have hstep : Vx n t = Vx (n+1) t := by
            rw [← C_zero n t, C_const n t hlen 0 1]
            exact C_one n t
          exact (ih hrec).trans hstep
    -- ## (7) the length and speed of a piece
    have C_mdiff : ∀ (i : ℕ) (t x : ℝ), x ∈ Set.Ioo (0:ℝ) 1 →
        MDifferentiableAt 𝓘(ℝ) I (fun y : ℝ => C i y t) x := by
      intro i t x hx
      rcases i with _ | m
      · show MDifferentiableAt 𝓘(ℝ) I
          (fun y : ℝ => sg (y * (1 - polygonValue.clamp01 t))) x
        have hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
            (fun y : ℝ => y * (1 - polygonValue.clamp01 t)) :=
          contMDiff_id.mul contMDiff_const
        exact (hsg_sm.comp hg).mdifferentiableAt (by simp)
      · by_cases hv : vec m t = 0
        · have hconst : (fun y : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (W m t)
              (y • vec m t)) = fun _ : ℝ => W m t := by
            funext y; rw [hv, smul_zero, Submission.GlobalExp.GExp_zero]
          show MDifferentiableAt 𝓘(ℝ) I (fun y : ℝ => Submission.GlobalExp.GExp (cov := cov)
            hmet (W m t) (y • vec m t)) x
          rw [hconst]
          exact mdifferentiableAt_const
        · show MDifferentiableAt 𝓘(ℝ) I (fun y : ℝ => Submission.GlobalExp.GExp (cov := cov)
            hmet (W m t) (y • vec m t)) x
          exact (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet (W m t) hv).contMDiffAt
            |>.mdifferentiableAt (by simp)
    have C_speed : ∀ (i : ℕ) (t x : ℝ), x ∈ Set.Ioo (0:ℝ) 1 →
        Submission.Length.curveSpeed (I := I) (fun y : ℝ => C i y t) x = Ln i t := by
      intro i t x hx
      rcases i with _ | m
      · show Submission.Length.curveSpeed (I := I)
          (fun y : ℝ => sg (y * (1 - polygonValue.clamp01 t))) x
            = (1 - polygonValue.clamp01 t) * ℓ
        rcases lt_or_eq_of_le (by linarith [polygonValue.clamp01_le_one t] :
          (0:ℝ) ≤ 1 - polygonValue.clamp01 t) with hpos | hzero
        · rw [show (fun y : ℝ => sg (y * (1 - polygonValue.clamp01 t)))
              = (fun y : ℝ => sg ((1 - polygonValue.clamp01 t) * y + 0)) from by
                funext y; rw [mul_comm]; ring_nf,
            Submission.Length.curveSpeed_comp_mul_add (I := I) hpos
              ((hsg_sm.contMDiffAt).mdifferentiableAt (by simp))]
          rw [hspeed]
        · have hconst : (fun y : ℝ => sg (y * (1 - polygonValue.clamp01 t)))
              = fun _ : ℝ => p := by
            funext y; rw [← hzero, mul_zero, hsg0]
          rw [hconst, Submission.Length.curveSpeed_const, ← hzero, zero_mul]
      · by_cases hv : vec m t = 0
        · have hconst : (fun y : ℝ => C (m+1) y t) = fun _ : ℝ => W m t := by
            funext y
            show Submission.GlobalExp.GExp (cov := cov) hmet (W m t) (y • vec m t) = W m t
            rw [hv, smul_zero, Submission.GlobalExp.GExp_zero]
          rw [hconst, Submission.Length.curveSpeed_const]
          rw [show Ln (m+1) t = ‖vec m t‖ from rfl, hv, norm_zero]
        · show Submission.Length.curveSpeed (I := I)
            (fun y : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (W m t) (y • vec m t)) x
              = ‖vec m t‖
          exact Submission.BrokenLength.curveSpeed_GExp_ray (cov := cov) hmet (W m t) hv x
    have C_len : ∀ (i : ℕ) (t : ℝ) (a b : ℝ), 0 ≤ a → a ≤ b → b ≤ 1 →
        Submission.Length.curveLength (I := I) (fun x : ℝ => C i x t) a b = (b - a) * Ln i t := by
      intro i t a b ha hab hb
      rcases i with _ | m
      · show Submission.Length.curveLength (I := I)
          (fun y : ℝ => sg (y * (1 - polygonValue.clamp01 t))) a b
            = (b - a) * ((1 - polygonValue.clamp01 t) * ℓ)
        rcases lt_or_eq_of_le (by linarith [polygonValue.clamp01_le_one t] :
          (0:ℝ) ≤ 1 - polygonValue.clamp01 t) with hpos | hzero
        · rw [show (fun y : ℝ => sg (y * (1 - polygonValue.clamp01 t)))
              = (fun y : ℝ => sg ((1 - polygonValue.clamp01 t) * y + 0)) from by
                funext y; rw [mul_comm]; ring_nf,
            Submission.Length.curveLength_comp_mul_add_of_le (I := I)
              (γ := sg) (c := 1 - polygonValue.clamp01 t) (d := 0) hpos hab
              (fun y _ => (hsg_sm.contMDiffAt).mdifferentiableAt (by simp)),
            add_zero, add_zero]
          rw [Submission.BrokenLength.curveLength_eq_mul_of_curveSpeed_eq (by nlinarith)
            (fun y _ => hspeed y)]
          ring
        · have hconst : (fun y : ℝ => sg (y * (1 - polygonValue.clamp01 t)))
              = fun _ : ℝ => p := by
            funext y; rw [← hzero, mul_zero, hsg0]
          rw [hconst, Submission.Length.curveLength_const]
          rw [← hzero, zero_mul, mul_zero]
      · by_cases hv : vec m t = 0
        · have hconst : (fun y : ℝ => C (m+1) y t) = fun _ : ℝ => W m t := by
            funext y
            show Submission.GlobalExp.GExp (cov := cov) hmet (W m t) (y • vec m t) = W m t
            rw [hv, smul_zero, Submission.GlobalExp.GExp_zero]
          rw [hconst, Submission.Length.curveLength_const]
          rw [show Ln (m+1) t = ‖vec m t‖ from rfl, hv, norm_zero, mul_zero]
        · show Submission.Length.curveLength (I := I)
            (fun y : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (W m t) (y • vec m t)) a b
              = (b - a) * ‖vec m t‖
          rw [Submission.BrokenLength.curveLength_GExp_ray (cov := cov) hmet (W m t) hv hab]
          ring
    -- ## (8) the Riemannian distance to the initial point of a piece
    have edist_le_curve : ∀ {γ : ℝ → M} {x y : M},
        ContMDiffOn 𝓘(ℝ) I 1 γ (Set.Icc (0:ℝ) 1) → γ 0 = x → γ 1 = y →
        Manifold.riemannianEDist I x y
          ≤ ENNReal.ofReal (Submission.Length.curveLength (I := I) γ 0 1) := by
      intro γ x y hsm h0 h1
      have h := Manifold.riemannianEDist_le_pathELength (I := I) hsm h0 h1
        (by norm_num : (0:ℝ) ≤ 1)
      rw [(Work.OddBound.longHomotopy.curveLength_toolkit (I := I) hsm).2.2 0 1
        (by norm_num) (by norm_num) (by norm_num)] at h
      exact h
    have C_cmdiff : ∀ (i : ℕ) (t : ℝ),
        ContMDiffOn 𝓘(ℝ) I ∞ (fun x : ℝ => C i x t) (Set.Icc (0:ℝ) 1) := by
      intro i t
      rcases i with _ | m
      · show ContMDiffOn 𝓘(ℝ) I ∞ (fun y : ℝ => sg (y * (1 - polygonValue.clamp01 t)))
          (Set.Icc (0:ℝ) 1)
        have hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
            (fun y : ℝ => y * (1 - polygonValue.clamp01 t)) :=
          contMDiff_id.mul contMDiff_const
        exact (hsg_sm.comp hg).contMDiffOn (s := Set.Icc (0:ℝ) 1)
      · by_cases hv : vec m t = 0
        · have hconst : (fun y : ℝ => C (m+1) y t) = fun _ : ℝ => W m t := by
            funext y
            show Submission.GlobalExp.GExp (cov := cov) hmet (W m t) (y • vec m t) = W m t
            rw [hv, smul_zero, Submission.GlobalExp.GExp_zero]
          rw [hconst]
          exact contMDiffOn_const
        · show ContMDiffOn 𝓘(ℝ) I ∞ (fun y : ℝ => Submission.GlobalExp.GExp (cov := cov)
            hmet (W m t) (y • vec m t)) (Set.Icc (0:ℝ) 1)
          exact (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet (W m t) hv).contMDiffOn
            (s := Set.Icc (0:ℝ) 1)
    have C_dist : ∀ (i : ℕ) (t x : ℝ), x ∈ Set.Icc (0:ℝ) 1 →
        Manifold.riemannianEDist I (C i x t) (C i 0 t) ≤ ENNReal.ofReal (x * Ln i t) := by
      intro i t x hx
      rcases eq_or_lt_of_le hx.1 with h0 | hpos
      · subst h0
        rw [Manifold.riemannianEDist_self, zero_mul, ENNReal.ofReal_zero]
      · have hxr : ∀ r ∈ Set.Icc (0:ℝ) 1, x * r + 0 ∈ Set.Icc (0:ℝ) 1 := by
          intro r hr
          refine ⟨add_nonneg (mul_nonneg hpos.le hr.1) le_rfl, ?_⟩
          have h2 : x * r ≤ x * 1 := mul_le_mul_of_nonneg_left hr.2 hpos.le
          rw [mul_one] at h2
          linarith [h2, hx.2]
        have haff : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : ℝ => x * r + 0) :=
          (contMDiff_const.mul contMDiff_id).add contMDiff_const
        have hsm : ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => C i (x * r + 0) t) (Set.Icc (0:ℝ) 1) := by
          have h1 : ContMDiffOn 𝓘(ℝ) I ∞ (fun r : ℝ => C i (x * r + 0) t) (Set.Icc (0:ℝ) 1) :=
            (C_cmdiff i t).comp (haff.contMDiffOn (s := Set.Icc (0:ℝ) 1)) hxr
          exact h1.of_le (by norm_num)
        have h := edist_le_curve (γ := fun r : ℝ => C i (x * r + 0) t)
          (x := C i 0 t) (y := C i x t) hsm (by simp) (by rw [mul_one, add_zero])
        have hlen : Submission.Length.curveLength (I := I) (fun r : ℝ => C i (x * r + 0) t) 0 1
            = x * Ln i t := by
          rw [Submission.Length.curveLength_comp_mul_add_of_le (I := I)
              (γ := fun y : ℝ => C i y t) (c := x) (d := 0) hpos (by norm_num)
              (fun r hr => C_mdiff i t (x * r + 0) (by
                rw [add_zero]
                refine ⟨mul_pos hpos hr.1, ?_⟩
                rcases lt_or_eq_of_le hx.2 with hx1 | hx1
                · have h2 : x * r ≤ x * 1 := mul_le_mul_of_nonneg_left hr.2.le hpos.le
                  rw [mul_one] at h2
                  linarith [h2, hx1]
                · rw [hx1, one_mul]; exact hr.2))]
          rw [mul_zero, mul_one, add_zero, add_zero,
            C_len i t 0 x le_rfl hpos.le hx.2]
          ring
        rw [hlen] at h
        rw [Manifold.riemannianEDist_comm (I := I) (x := C i 0 t) (y := C i x t)] at h
        exact h
    -- ## (9) the `GExp`-rays of the degenerate tail vanish
    have vec_eq_zero_of_le : ∀ (j : ℕ) (t : ℝ), Kn ≤ j → vec j t = 0 := by
      intro j t hj
      have h1 : u j = 1 := by
        refine min_eq_right ?_
        rw [le_div_iff₀ hKnn, one_mul]
        exact_mod_cast hj
      have h2 : u (j+1) = 1 := by
        refine min_eq_right ?_
        rw [le_div_iff₀ hKnn, one_mul]
        exact_mod_cast (by omega : Kn ≤ j + 1)
      have hv : W j t = W (j+1) t := by
        show Hm (1 - polygonValue.clamp01 t) (u j) = Hm (1 - polygonValue.clamp01 t) (u (j+1))
        rw [h1, h2]
      have h3 : ENNReal.ofReal ‖vec j t‖ = 0 := by
        rw [← vec_norm j t, hv, Manifold.riemannianEDist_self]
      exact norm_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp h3) (norm_nonneg _))
    have Ln_eq_zero_of_le : ∀ (j : ℕ) (t : ℝ), kap ≤ j → Ln j t = 0 := by
      intro j t hj
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      have hm : Kn ≤ m := by omega
      show ‖vec m t‖ = 0
      rw [vec_eq_zero_of_le m t hm, norm_zero]
    -- ## (10) the index function
    have idx_spec : ∀ (a t : ℝ), t ∈ Set.Icc (0:ℝ) 1 → 0 ≤ a → a ≤ Tot t →
        idx a t < kap ∧ a ≤ Pf (idx a t + 1) t ∧ (0 < idx a t → Pf (idx a t) t < a) := by
      intro a t ht ha0 haT
      have hex : ∃ j : ℕ, j < kap ∧ a ≤ Pf (j+1) t := by
        refine ⟨kap - 1, by omega, ?_⟩
        have h : kap - 1 + 1 = kap := Nat.succ_pred_eq_of_pos hkap
        rw [h]
        exact haT
      have hidx : idx a t = Nat.find hex := by
        simp only [idx]
        exact dif_pos hex
      refine ⟨?_, ?_, ?_⟩
      · rw [hidx]; exact (Nat.find_spec hex).1
      · rw [hidx]; exact (Nat.find_spec hex).2
      · intro hpos
        have hidlt : idx a t < kap := by rw [hidx]; exact (Nat.find_spec hex).1
        have hmin := Nat.find_min hex (m := idx a t - 1) (by omega)
        have h1 : idx a t - 1 + 1 = idx a t := Nat.succ_pred_eq_of_pos hpos
        rw [h1] at hmin
        push_neg at hmin
        exact hmin (by omega)
    have idx_le_of_le : ∀ (a t : ℝ) (i : ℕ), a ≤ Pf (i+1) t → i < kap → idx a t ≤ i := by
      intro a t i hai hi
      have hex : ∃ j : ℕ, j < kap ∧ a ≤ Pf (j+1) t := ⟨i, hi, hai⟩
      have hidx : idx a t = Nat.find hex := by
        simp only [idx]
        exact dif_pos hex
      rw [hidx]
      exact Nat.find_min' hex ⟨hi, hai⟩
    -- ## (11) the slab agreement
    have slab_agree : ∀ (i : ℕ) (a t : ℝ), t ∈ Set.Icc (0:ℝ) 1 → i < kap → 0 ≤ a →
        a ≤ Tot t → Pf i t ≤ a → a ≤ Pf (i+1) t →
        Pt a t = C i ((a - Pf i t) / Ln i t) t := by
      intro i a t ht hi ha0 haT h1 h2
      have hjle : idx a t ≤ i := idx_le_of_le a t i h2 hi
      rcases eq_or_lt_of_le hjle with heq | hlt
      · show C (idx a t) ((a - Pf (idx a t) t) / Ln (idx a t) t) t
            = C i ((a - Pf i t) / Ln i t) t
        rw [heq]
      · set j := idx a t with hj
        have hspec := idx_spec a t ht ha0 haT
        rw [← hj] at hspec
        have hfind : a ≤ Pf (j + 1) t := hspec.2.1
        have hPfji : Pf (j + 1) t = Pf i t :=
          le_antisymm (Pf_mono (by omega) t) (le_trans h1 hfind)
        have haeq : a = Pf (j + 1) t := le_antisymm hfind (by rw [hPfji]; exact h1)
        have hPt : Pt a t = C j ((a - Pf j t) / Ln j t) t := by
          simp only [Pt, ← hj]
        rw [hPt]
        have hR : C i ((a - Pf i t) / Ln i t) t = Vx i t := by
          have hz : (a - Pf i t) / Ln i t = 0 := by
            rw [← hPfji, haeq, sub_self, zero_div]
          rw [hz]
          exact C_zero i t
        rw [hR]
        rcases eq_or_ne (Ln j t) 0 with hzero | hne
        · have hPfj : Pf j t = Pf i t := by
            have h3 : Pf (j+1) t = Pf j t := by rw [Pf_succ, hzero, add_zero]
            rw [← h3]; exact hPfji
          have hzj : (a - Pf j t) / Ln j t = 0 := by
            have h4 : a = Pf j t := by rw [haeq, Pf_succ, hzero, add_zero]
            rw [h4, sub_self, zero_div]
          rw [hzj, C_zero j t]
          exact vertex_chain j i t (by omega) (by rw [hPfj])
        · have hone : (a - Pf j t) / Ln j t = 1 := by
            have h4 : a - Pf j t = Ln j t := by
              rw [haeq, Pf_succ, add_sub_cancel_left]
            rw [h4, div_self hne]
          rw [hone, C_one j t]
          exact vertex_chain (j+1) i t (by omega) hPfji
    -- ## (12) continuity in the family parameter
    have Ln_cont : ∀ i : ℕ, Continuous (fun t : ℝ => Ln i t) := by
      intro i
      rcases i with _ | m
      · show Continuous (fun t : ℝ => (1 - polygonValue.clamp01 t) * ℓ)
        exact (continuous_const.sub polygonValue.clamp01_continuous).mul continuous_const
      · show Continuous (fun t : ℝ => ‖vec m t‖)
        have hr : (fun t : ℝ => ‖vec m t‖)
            = fun t : ℝ => Submission.Distance.riemannianDist (I := I) (W m t) (W (m+1) t) := by
          funext t
          rw [Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) (W m t) (W (m+1) t),
            vec_norm m t, ENNReal.toReal_ofReal (norm_nonneg _)]
        rw [hr]
        exact (polygonValue.balancing.continuousRiemannianDist (I := I)).comp
          ((hW_cont m).prodMk (hW_cont (m+1)))
    have Pf_cont : ∀ i : ℕ, Continuous (fun t : ℝ => Pf i t) := by
      intro i
      have h : (fun t : ℝ => Pf i t) = fun t : ℝ => ∑ j ∈ Finset.range i, Ln j t := rfl
      rw [h]
      exact continuous_finsetSum _ (fun j _ => Ln_cont j)
    have C_joint : ∀ i : ℕ, ContinuousOn (fun q : ℝ × ℝ => C i q.1 q.2)
        (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) := by
      intro i
      rcases i with _ | m
      · have hg : Continuous (fun q : ℝ × ℝ => q.1 * (1 - polygonValue.clamp01 q.2)) :=
          continuous_fst.mul (continuous_const.sub
            (polygonValue.clamp01_continuous.comp continuous_snd))
        exact (hsg_cont.comp hg).continuousOn
      · exact polygonValue.continuousOn_GExp_smul_of_minimising (I := I) (cov := cov)
          hmet htor (hW_cont m) (hW_cont (m+1)) hρpos hρinj
          (fun τ _ => hshort m τ) (vec m) (fun τ _ => ⟨vec_GExp m τ, vec_norm m τ⟩)
    have Vx_cont : ∀ i : ℕ, Continuous (fun t : ℝ => Vx i t) := by
      intro i
      rcases i with _ | m
      · show Continuous (fun t : ℝ => p)
        exact continuous_const
      · show Continuous (fun t : ℝ => W (m + 1 - 1) t)
        rw [show m + 1 - 1 = m from by omega]
        exact hW_cont m
    -- ## (13) the slab functions are continuous
    have hratio_mem : ∀ (i : ℕ) (q : ℝ × ℝ), q.2 ∈ Set.Icc (0:ℝ) 1 → Pf i q.2 ≤ q.1 →
        q.1 ≤ Pf (i+1) q.2 → (q.1 - Pf i q.2)/Ln i q.2 ∈ Set.Icc (0:ℝ) 1 := by
      intro i q ht h1 h2
      rcases eq_or_lt_of_le (Ln_nonneg i q.2) with hz | hpos
      · have h3 : q.1 = Pf i q.2 := by
          have h := Pf_succ i q.2
          have h4 : Pf (i+1) q.2 = Pf i q.2 := by rw [h, hz.symm, add_zero]
          exact le_antisymm (h4 ▸ h2) h1
        rw [h3, sub_self, zero_div]
        exact ⟨le_rfl, zero_le_one⟩
      · refine ⟨div_nonneg (by linarith) hpos.le, ?_⟩
        rw [div_le_one hpos]
        have h := Pf_succ i q.2
        linarith
    have Fi_cont : ∀ i : ℕ, i < kap →
        ContinuousOn (fun q : ℝ × ℝ => C i ((q.1 - Pf i q.2)/Ln i q.2) q.2)
          {q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧ Pf i q.2 ≤ q.1 ∧ q.1 ≤ Pf (i+1) q.2} := by
      intro i hi q₀ hq₀
      obtain ⟨ht₀, h1₀, h2₀⟩ := hq₀
      by_cases hz : Ln i q₀.2 = 0
      · -- ### the degenerate case
        have hx₀ : (q₀.1 - Pf i q₀.2)/Ln i q₀.2 = 0 := by
          have h3 : q₀.1 = Pf i q₀.2 := by
            have h := Pf_succ i q₀.2
            rw [hz, add_zero] at h
            exact le_antisymm (h ▸ h2₀) h1₀
          rw [h3, sub_self, zero_div]
        change Filter.Tendsto (fun q : ℝ × ℝ => C i ((q.1 - Pf i q.2)/Ln i q.2) q.2)
          (𝓝[{q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧ Pf i q.2 ≤ q.1 ∧ q.1 ≤ Pf (i+1) q.2}] q₀)
          (𝓝 (C i ((q₀.1 - Pf i q₀.2)/Ln i q₀.2) q₀.2))
        rw [_root_.tendsto_nhds]
        intro o ho hxo
        obtain ⟨c₀, hc₀pos, hc₀sub⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds
          (I := I) (x := C i ((q₀.1 - Pf i q₀.2)/Ln i q₀.2) q₀.2) (ho.mem_nhds hxo)
        obtain ⟨ε, hεpos, hεle⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε ≤ c₀ := by
          rcases eq_or_ne c₀ ⊤ with htop | htop
          · exact ⟨1, one_pos, htop ▸ le_top⟩
          · have htoc : 0 < c₀.toReal := ENNReal.toReal_pos (ne_of_gt hc₀pos) htop
            refine ⟨c₀.toReal/2, half_pos htoc, ?_⟩
            have h2 : ENNReal.ofReal (c₀.toReal/2) ≤ ENNReal.ofReal c₀.toReal :=
              ENNReal.ofReal_le_ofReal (le_of_lt (half_lt_self htoc))
            rwa [ENNReal.ofReal_toReal htop] at h2
        have hε2 : (0:ℝ) < ε/2 := by linarith
        have hVx : ∀ᶠ t in 𝓝 q₀.2,
            Manifold.riemannianEDist I (Vx i t) (Vx i q₀.2) < ENNReal.ofReal (ε/2) := by
          filter_upwards [(Vx_cont i).continuousAt.eventually
            (Submission.EDist.eventually_riemannianEDist_lt (I := I) (Vx i q₀.2)
              (ENNReal.ofReal_pos.mpr hε2))] with t ht
          rwa [Manifold.riemannianEDist_comm] at ht
        have hLn : ∀ᶠ t in 𝓝 q₀.2, Ln i t < ε/2 := by
          have h2 : ∀ᶠ t in 𝓝 q₀.2, |Ln i t - Ln i q₀.2| < ε/2 :=
            (Metric.tendsto_nhds.mp (Ln_cont i).continuousAt.tendsto (ε/2) hε2)
          filter_upwards [h2] with t ht
          have h3 : Ln i t - Ln i q₀.2 < ε/2 := (abs_lt.mp ht).2
          rw [hz] at h3
          linarith
        have hVx' : ∀ᶠ q : ℝ × ℝ in 𝓝[{q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧
            Pf i q.2 ≤ q.1 ∧ q.1 ≤ Pf (i+1) q.2}] q₀,
            Manifold.riemannianEDist I (Vx i q.2) (Vx i q₀.2) < ENNReal.ofReal (ε/2) :=
          ((continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually hVx)
        have hLn' : ∀ᶠ q : ℝ × ℝ in 𝓝[{q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧
            Pf i q.2 ≤ q.1 ∧ q.1 ≤ Pf (i+1) q.2}] q₀, Ln i q.2 < ε/2 :=
          ((continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually hLn)
        refine Filter.mem_of_superset ?_ (fun q hq => hc₀sub (lt_of_lt_of_le hq hεle))
        filter_upwards [self_mem_nhdsWithin, hVx', hLn'] with q hq hVq hLq
        -- the two estimates
        have hmem : (q.1 - Pf i q.2)/Ln i q.2 ∈ Set.Icc (0:ℝ) 1 :=
          hratio_mem i q hq.1 hq.2.1 hq.2.2
        have hA : Manifold.riemannianEDist I (C i ((q.1 - Pf i q.2)/Ln i q.2) q.2)
            (Vx i q.2) ≤ ENNReal.ofReal (Ln i q.2) := by
          have h := C_dist i q.2 ((q.1 - Pf i q.2)/Ln i q.2) hmem
          rw [C_zero i q.2] at h
          have hle : ((q.1 - Pf i q.2)/Ln i q.2) * Ln i q.2 ≤ Ln i q.2 :=
            mul_le_of_le_one_left (Ln_nonneg i q.2) hmem.2
          exact le_trans h (ENNReal.ofReal_le_ofReal hle)
        have hB : Manifold.riemannianEDist I (Vx i q.2) (Vx i q₀.2)
            < ENNReal.ofReal (ε/2) := hVq
        have hC : ENNReal.ofReal (Ln i q.2) < ENNReal.ofReal (ε/2) :=
          (ENNReal.ofReal_lt_ofReal_iff hε2).mpr hLq
        have hval : C i ((q₀.1 - Pf i q₀.2)/Ln i q₀.2) q₀.2 = Vx i q₀.2 := by
          rw [hx₀, C_zero i q₀.2]
        rw [hval]
        have hsum := Manifold.riemannianEDist_triangle (I := I)
          (x := Vx i q₀.2) (y := Vx i q.2) (z := C i ((q.1 - Pf i q.2)/Ln i q.2) q.2)
        have hB' : Manifold.riemannianEDist I (Vx i q₀.2) (Vx i q.2) < ENNReal.ofReal (ε/2) := by
          rw [Manifold.riemannianEDist_comm]
          exact hB
        have hA' : Manifold.riemannianEDist I (Vx i q.2)
            (C i ((q.1 - Pf i q.2)/Ln i q.2) q.2) < ENNReal.ofReal (ε/2) := by
          refine lt_of_le_of_lt ?_ hC
          rw [Manifold.riemannianEDist_comm]
          exact hA
        calc Manifold.riemannianEDist I (Vx i q₀.2)
              (C i ((q.1 - Pf i q.2)/Ln i q.2) q.2)
            ≤ Manifold.riemannianEDist I (Vx i q₀.2) (Vx i q.2)
              + Manifold.riemannianEDist I (Vx i q.2)
                (C i ((q.1 - Pf i q.2)/Ln i q.2) q.2) := hsum
          _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := ENNReal.add_lt_add hB' hA'
          _ = ENNReal.ofReal ε := by
              rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
              congr 1
              ring
      · -- ### the non-degenerate case
        have hne : Ln i q₀.2 ≠ 0 := hz
        have hg : ContinuousAt (fun q : ℝ × ℝ => ((q.1 - Pf i q.2)/Ln i q.2, q.2)) q₀ := by
          refine ContinuousAt.prodMk ?_ continuousAt_snd
          exact (continuousAt_fst.sub ((Pf_cont i).continuousAt.comp continuousAt_snd)).div
            ((Ln_cont i).continuousAt.comp continuousAt_snd) hne
        refine ContinuousWithinAt.comp (g := fun q : ℝ × ℝ => C i q.1 q.2)
          (t := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) ?_ hg.continuousWithinAt ?_
        · exact (C_joint i).continuousWithinAt ⟨hratio_mem i q₀ ht₀ h1₀ h2₀, ht₀⟩
        · intro q hq
          exact ⟨hratio_mem i q hq.1 hq.2.1 hq.2.2, hq.1⟩
    -- ## (14) continuity of `Pt` on its region
    have idx_le_self : ∀ (a t : ℝ), t ∈ Set.Icc (0:ℝ) 1 → 0 ≤ a → a ≤ Tot t →
        Pf (idx a t) t ≤ a := by
      intro a t ht ha0 haT
      rcases eq_or_lt_of_le (Nat.zero_le (idx a t)) with h | h
      · rw [← h, Pf_zero]; exact ha0
      · exact le_of_lt ((idx_spec a t ht ha0 haT).2.2 h)
    have Pt_cont : ContinuousOn (fun q : ℝ × ℝ => Pt q.1 q.2)
        {q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧ 0 ≤ q.1 ∧ q.1 ≤ Tot q.2} := by
      intro q₀ hq₀
      obtain ⟨ht₀, ha₀, hT₀⟩ := hq₀
      change Filter.Tendsto (fun q : ℝ × ℝ => Pt q.1 q.2)
        (𝓝[{q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧ 0 ≤ q.1 ∧ q.1 ≤ Tot q.2}] q₀)
        (𝓝 (Pt q₀.1 q₀.2))
      rw [_root_.tendsto_nhds]
      intro o ho hxo
      obtain ⟨c, hcpos, hcsub⟩ := Submission.EDist.setOf_riemannianEDist_lt_subset_nhds
        (I := I) (x := Pt q₀.1 q₀.2) (ho.mem_nhds hxo)
      -- a ball around `q₀` (within the region) on which the distance is `< c`
      have hstep : ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℝ × ℝ, q.2 ∈ Set.Icc (0:ℝ) 1 → 0 ≤ q.1 →
          q.1 ≤ Tot q.2 → dist q q₀ < δ →
          Manifold.riemannianEDist I (Pt q₀.1 q₀.2) (Pt q.1 q.2) < c := by
        by_contra hcon
        push_neg at hcon
        choose q hq using fun n : ℕ => hcon (1/((n:ℝ)+1)) (by positivity)
        have hqreg : ∀ n, (q n).2 ∈ Set.Icc (0:ℝ) 1 ∧ 0 ≤ (q n).1 ∧ (q n).1 ≤ Tot (q n).2 :=
          fun n => ⟨(hq n).1, (hq n).2.1, (hq n).2.2.1⟩
        have hqdist : ∀ n, dist (q n) q₀ < 1/((n:ℝ)+1) := fun n => (hq n).2.2.2.1
        have hqedist : ∀ n, c ≤ Manifold.riemannianEDist I (Pt q₀.1 q₀.2)
            (Pt (q n).1 (q n).2) := fun n => (hq n).2.2.2.2
        -- the sequence converges to `q₀` within the region
        have hqlim : Filter.Tendsto q Filter.atTop
            (𝓝[{q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧ 0 ≤ q.1 ∧ q.1 ≤ Tot q.2}] q₀) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, Filter.Eventually.of_forall hqreg⟩
          rw [Metric.tendsto_nhds]
          intro ε hε
          filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
            (isOpen_Iio.mem_nhds (by simpa using hε))] with n hn
          exact lt_trans (hqdist n) hn
        -- pigeonhole: the index sequence has a constant subsequence
        have hpin : ∃ j : ℕ, j < kap ∧ ∀ N : ℕ, ∃ n > N, idx (q n).1 (q n).2 = j := by
          by_contra hcon'
          push_neg at hcon'
          choose Nf hNf using hcon'
          set Nf' : ℕ → ℕ := fun j => if h : j < kap then Nf j h else 0 with hNf'
          set M : ℕ := ∑ j ∈ Finset.range kap, Nf' j with hM
          have hMge : ∀ j, j < kap → Nf' j ≤ M := by
            intro j hj
            exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
          have hjM : idx (q (M+1)).1 (q (M+1)).2 < kap := by
            obtain ⟨h1, h2, h3⟩ := hqreg (M + 1)
            exact (idx_spec _ _ h1 h2 h3).1
          have hNf' : Nf' (idx (q (M+1)).1 (q (M+1)).2)
              = Nf (idx (q (M+1)).1 (q (M+1)).2) hjM := dif_pos hjM
          have hbound : Nf (idx (q (M+1)).1 (q (M+1)).2) hjM ≤ M := by
            rw [← hNf']; exact hMge _ hjM
          exact (hNf (idx (q (M+1)).1 (q (M+1)).2) hjM (M + 1)
            (Nat.lt_succ_of_le hbound)) rfl
        obtain ⟨j, hjlt, hjp⟩ := hpin
        obtain ⟨φ, hφmono, hφeq⟩ := Nat.exists_strictMono_subsequence hjp
        -- the subsequence converges within the region
        have hqlimφ : Filter.Tendsto (fun n => q (φ n)) Filter.atTop
            (𝓝[{q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧ 0 ≤ q.1 ∧ q.1 ≤ Tot q.2}] q₀) :=
          hqlim.comp hφmono.tendsto_atTop
        have hqlimφ' : Filter.Tendsto (fun n => q (φ n)) Filter.atTop (𝓝 q₀) :=
          hqlimφ.mono_right nhdsWithin_le_nhds
        -- the subsequence stays in the slab `j`
        have hslab : ∀ n, Pf j (q (φ n)).2 ≤ (q (φ n)).1 ∧
            (q (φ n)).1 ≤ Pf (j+1) (q (φ n)).2 := by
          intro n
          obtain ⟨h1, h2, h3⟩ := hqreg (φ n)
          have hid : idx (q (φ n)).1 (q (φ n)).2 = j := hφeq n
          exact ⟨by rw [← hid]; exact idx_le_self _ _ h1 h2 h3,
            by rw [← hid]; exact (idx_spec _ _ h1 h2 h3).2.1⟩
        have hslab_closed : IsClosed {q : ℝ × ℝ | Pf j q.2 ≤ q.1 ∧ q.1 ≤ Pf (j+1) q.2} :=
          (isClosed_le ((Pf_cont j).comp continuous_snd) continuous_fst).inter
            (isClosed_le continuous_fst ((Pf_cont (j+1)).comp continuous_snd))
        have hslab_closed' : IsClosed {q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧ Pf j q.2 ≤ q.1 ∧
            q.1 ≤ Pf (j+1) q.2} :=
          (isClosed_Icc.preimage continuous_snd).inter hslab_closed
        have hmem' : ∀ n, q (φ n) ∈ {q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧ Pf j q.2 ≤ q.1 ∧
            q.1 ≤ Pf (j+1) q.2} :=
          fun n => ⟨(hqreg (φ n)).1, (hslab n).1, (hslab n).2⟩
        have hq₀slab_all := IsClosed.mem_of_tendsto hslab_closed' hqlimφ'
          (Filter.Eventually.of_forall hmem')
        have hq₀slab : Pf j q₀.2 ≤ q₀.1 ∧ q₀.1 ≤ Pf (j+1) q₀.2 :=
          ⟨hq₀slab_all.2.1, hq₀slab_all.2.2⟩
        have hqlimφslab : Filter.Tendsto (fun n => q (φ n)) Filter.atTop
            (𝓝[{q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧ Pf j q.2 ≤ q.1 ∧ q.1 ≤ Pf (j+1) q.2}] q₀) :=
          tendsto_nhdsWithin_iff.mpr ⟨hqlimφ', Filter.Eventually.of_forall hmem'⟩
        -- `Fi j` is continuous at `q₀`
        have hFicont : ContinuousWithinAt
            (fun q : ℝ × ℝ => C j ((q.1 - Pf j q.2)/Ln j q.2) q.2)
            {q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧ Pf j q.2 ≤ q.1 ∧ q.1 ≤ Pf (j+1) q.2} q₀ :=
          Fi_cont j hjlt q₀ ⟨ht₀, hq₀slab⟩
        have hPtφ : ∀ n, Pt (q (φ n)).1 (q (φ n)).2
            = C j (((q (φ n)).1 - Pf j (q (φ n)).2)/Ln j (q (φ n)).2) (q (φ n)).2 := by
          intro n
          obtain ⟨h1, h2, h3⟩ := hqreg (φ n)
          exact slab_agree j _ _ h1 hjlt h2 h3 (hslab n).1 (hslab n).2
        have hPt₀ : C j ((q₀.1 - Pf j q₀.2)/Ln j q₀.2) q₀.2 = Pt q₀.1 q₀.2 :=
          (slab_agree j _ _ ht₀ hjlt ha₀ hT₀ hq₀slab.1 hq₀slab.2).symm
        have htend : Filter.Tendsto (fun n => Pt (q (φ n)).1 (q (φ n)).2) Filter.atTop
            (𝓝 (Pt q₀.1 q₀.2)) := by
          have hmain : Filter.Tendsto
              (fun n => C j (((q (φ n)).1 - Pf j (q (φ n)).2)/Ln j (q (φ n)).2) (q (φ n)).2)
              Filter.atTop (𝓝 (C j ((q₀.1 - Pf j q₀.2)/Ln j q₀.2) q₀.2)) :=
            hFicont.tendsto.comp hqlimφslab
          rw [hPt₀] at hmain
          exact hmain.congr' (Filter.Eventually.of_forall fun n => (hPtφ n).symm)
        have hev : ∀ᶠ n in Filter.atTop, Manifold.riemannianEDist I (Pt q₀.1 q₀.2)
            (Pt (q (φ n)).1 (q (φ n)).2) < c :=
          htend.eventually (Submission.EDist.eventually_riemannianEDist_lt (I := I)
            (Pt q₀.1 q₀.2) hcpos)
        obtain ⟨n, hn⟩ := hev.exists
        exact absurd (hqedist (φ n)) (not_le.mpr hn)
      obtain ⟨δ, hδpos, hδ⟩ := hstep
      have hmem : {q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧ 0 ≤ q.1 ∧ q.1 ≤ Tot q.2} ∩
          {q : ℝ × ℝ | dist q q₀ < δ} ∈
          𝓝[{q : ℝ × ℝ | q.2 ∈ Set.Icc (0:ℝ) 1 ∧ 0 ≤ q.1 ∧ q.1 ≤ Tot q.2}] q₀ :=
        Filter.inter_mem self_mem_nhdsWithin
          (nhdsWithin_le_nhds (Metric.ball_mem_nhds q₀ hδpos))
      exact Filter.mem_of_superset hmem (fun q hq => hcsub (hδ q hq.1.1 hq.1.2.1 hq.1.2.2 hq.2))
    -- ## (15) the endpoints of the scan
    have vertex_eq_of_Pf_eq : ∀ (i j : ℕ) (t : ℝ), Pf i t = Pf j t → Vx i t = Vx j t := by
      intro i j t h
      rcases le_total i j with hij | hji
      · exact vertex_chain i j t hij h
      · exact (vertex_chain j i t hji h.symm).symm
    have Vx_kap : ∀ t : ℝ, Vx kap t = p := by
      intro t
      have hk : kap = Kn + 1 := rfl
      rw [hk] at ⊢
      simp only [Vx, Nat.succ_ne_zero Kn, if_false]
      show W (Kn + 1 - 1) t = p
      rw [show Kn + 1 - 1 = Kn from by omega]
      show Hm (1 - polygonValue.clamp01 t) (u Kn) = p
      rw [hu_self Kn le_rfl, div_self (ne_of_gt hKnn)]
      exact hHm2 _
    have Vx_of_Pf_kap : ∀ (i : ℕ) (t : ℝ), Pf i t = Pf kap t → Vx i t = p := by
      intro i t h
      rw [vertex_eq_of_Pf_eq i kap t h, Vx_kap]
    have Pt_zero : ∀ t : ℝ, Pt 0 t = p := by
      intro t
      have hwit : (0:ℝ) ≤ Pf (0+1) t := by
        rw [Pf_succ, Pf_zero, zero_add]
        exact Ln_nonneg 0 t
      have hex : ∃ j : ℕ, j < kap ∧ (0:ℝ) ≤ Pf (j+1) t := ⟨0, hkap, hwit⟩
      have hidx0 : idx 0 t = 0 := by
        simp only [idx]
        rw [dif_pos hex]
        exact Nat.eq_zero_of_le_zero (Nat.find_min' hex ⟨hkap, hwit⟩)
      show C (idx 0 t) ((0 - Pf (idx 0 t) t)/Ln (idx 0 t) t) t = p
      rw [hidx0, Pf_zero, sub_zero, zero_div, C_zero]
      simp [Vx]
    have Pt_tot : ∀ t : ℝ, Pt (Tot t) t = p := by
      intro t
      have hex : ∃ j : ℕ, j < kap ∧ Tot t ≤ Pf (j+1) t := by
        refine ⟨kap - 1, by omega, ?_⟩
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hkap))]
      have hidx : idx (Tot t) t = Nat.find hex := by
        simp only [idx]; exact dif_pos hex
      set i : ℕ := idx (Tot t) t with hi
      have hspec := Nat.find_spec hex
      rw [← hidx] at hspec
      have hi1 : Pf (i+1) t = Tot t := by
        refine le_antisymm ?_ hspec.2
        calc Pf (i + 1) t ≤ Pf kap t := Pf_mono (by omega) t
          _ = Tot t := rfl
      have hstep : Pt (Tot t) t = C i ((Tot t - Pf i t)/Ln i t) t := by
        simp only [Pt, ← hi]
      rw [hstep]
      rcases eq_or_ne (Ln i t) 0 with hz | hne
      · have hPfi : Pf i t = Pf kap t := by
          have h2 : Pf (i+1) t = Pf i t := by rw [Pf_succ, hz, add_zero]
          rw [← h2]; exact hi1
        have hz2 : (Tot t - Pf i t)/Ln i t = 0 := by
          rw [show Tot t = Pf kap t from rfl, ← hPfi, sub_self, zero_div]
        rw [hz2, C_zero]
        exact Vx_of_Pf_kap i t hPfi
      · have hone : (Tot t - Pf i t)/Ln i t = 1 := by
          have h2 : Tot t - Pf i t = Ln i t := by
            rw [← hi1, Pf_succ, add_sub_cancel_left]
          rw [h2, div_self hne]
        rw [hone, C_one]
        exact Vx_of_Pf_kap (i+1) t hi1
    -- ## (16) the family `Hf`: continuity, periodicity, and the end slices
    have hGcont : Continuous (fun p : ℝ × ℝ =>
        Pt (Tot (polygonValue.clamp01 p.1) * polygonValue.clamp01 p.2)
          (polygonValue.clamp01 p.1)) := by
      refine Pt_cont.comp_continuous (f := fun p : ℝ × ℝ =>
        (Tot (polygonValue.clamp01 p.1) * polygonValue.clamp01 p.2,
          polygonValue.clamp01 p.1)) ?_ ?_
      · show Continuous (fun p : ℝ × ℝ => (Pf kap (polygonValue.clamp01 p.1) *
            polygonValue.clamp01 p.2, polygonValue.clamp01 p.1))
        exact ((((Pf_cont kap).comp (polygonValue.clamp01_continuous.comp continuous_fst)).mul
          (polygonValue.clamp01_continuous.comp continuous_snd))).prodMk
          (polygonValue.clamp01_continuous.comp continuous_fst)
      · intro p
        exact ⟨polygonValue.clamp01_mem p.1,
          mul_nonneg (Tot_nonneg _) (polygonValue.clamp01_nonneg p.2),
          mul_le_of_le_one_right (Tot_nonneg _) (polygonValue.clamp01_le_one p.2)⟩
    have hGper : ∀ t : ℝ, Pt (Tot (polygonValue.clamp01 t) * polygonValue.clamp01 1)
        (polygonValue.clamp01 t)
          = Pt (Tot (polygonValue.clamp01 t) * polygonValue.clamp01 0)
            (polygonValue.clamp01 t) := by
      intro t
      rw [polygonValue.clamp01_eq_one_of_one_le le_rfl,
        polygonValue.clamp01_eq_zero_of_nonpos le_rfl, mul_one, mul_zero, Pt_tot, Pt_zero]
    have Hf_cont : Continuous (fun q : ℝ × ℝ => Hf q.1 q.2) := by
      have h := polygonValue.balancing.continuous_fract_comp (X := ℝ)
        (G := fun t u => Pt (Tot (polygonValue.clamp01 t) * polygonValue.clamp01 u)
          (polygonValue.clamp01 t)) hGcont hGper
      have h2 : Continuous (fun p : ℝ × ℝ => Hf p.2 p.1) := by
        refine h.congr fun p => ?_
        show Pt (Tot (polygonValue.clamp01 p.1) * polygonValue.clamp01 (Int.fract p.2))
            (polygonValue.clamp01 p.1) = Hf p.2 p.1
        rw [polygonValue.clamp01_eq_self (Int.fract_nonneg p.2) (le_of_lt (Int.fract_lt_one p.2))]
      exact (h2.comp continuous_swap).congr fun q => rfl
    have Hf_per : ∀ s t : ℝ, Hf (s + 1) t = Hf s t := by
      intro s t
      show Pt (Tot (polygonValue.clamp01 t) * Int.fract (s + 1)) (polygonValue.clamp01 t)
        = Pt (Tot (polygonValue.clamp01 t) * Int.fract s) (polygonValue.clamp01 t)
      rw [Int.fract_add_one]
    have Hf_base : ∀ t : ℝ, Hf 0 t = p := by
      intro t
      show Pt (Tot (polygonValue.clamp01 t) * Int.fract 0) (polygonValue.clamp01 t) = p
      rw [Int.fract_zero, mul_zero, Pt_zero]
    have vec_zero_at_zero : ∀ j : ℕ, vec j 0 = 0 := by
      intro j
      have h : ENNReal.ofReal ‖vec j 0‖ = 0 := by
        rw [← vec_norm j 0, hW0 j, hW0 (j+1), Manifold.riemannianEDist_self]
      exact norm_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp h) (norm_nonneg _))
    have Tot_zero : Tot 0 = ℓ := by
      have h : Pf kap 0 = Ln 0 0 := by
        show (∑ j ∈ Finset.range kap, Ln j 0) = Ln 0 0
        refine Finset.sum_eq_single 0 ?_ ?_
        · intro j _ hj
          obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
          show ‖vec m 0‖ = 0
          rw [vec_zero_at_zero m, norm_zero]
        · intro h0
          exact absurd (Finset.mem_range.mpr hkap) h0
      show Pf kap 0 = ℓ
      rw [h]
      show (1 - polygonValue.clamp01 0) * ℓ = ℓ
      rw [polygonValue.clamp01_eq_zero_of_nonpos le_rfl]
      ring
    have Hf_zero : ∀ s : ℝ, Hf s 0 = γ (L * s) := by
      intro s
      have hT : Tot (polygonValue.clamp01 0) = ℓ := by
        rw [polygonValue.clamp01_eq_zero_of_nonpos le_rfl]; exact Tot_zero
      have h1 : Hf s 0 = Pt (ℓ * Int.fract s) 0 := by
        show Pt (Tot (polygonValue.clamp01 0) * Int.fract s) (polygonValue.clamp01 0) = _
        rw [hT, polygonValue.clamp01_eq_zero_of_nonpos le_rfl]
      rw [h1]
      have hslice : Pt (ℓ * Int.fract s) 0 = sg (Int.fract s) := by
        have ht0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
        have hu : Int.fract s ∈ Set.Icc (0:ℝ) 1 :=
          ⟨Int.fract_nonneg s, le_of_lt (Int.fract_lt_one s)⟩
        have ha0 : (0:ℝ) ≤ ℓ * Int.fract s := mul_nonneg hℓnonneg hu.1
        have haT : ℓ * Int.fract s ≤ Tot 0 := by rw [Tot_zero]; nlinarith [hu.2, hℓpos]
        have hPf1 : Pf (0+1) 0 = ℓ := by
          rw [Pf_succ]
          show Pf 0 0 + (1 - polygonValue.clamp01 0) * ℓ = ℓ
          rw [Pf_zero, polygonValue.clamp01_eq_zero_of_nonpos le_rfl, zero_add, sub_zero,
            one_mul]
        have hle2 : ℓ * Int.fract s ≤ Pf (0+1) 0 := by rw [hPf1]; nlinarith [hu.2, hℓpos]
        have h := slab_agree 0 (ℓ * Int.fract s) 0 ht0 hkap ha0 haT
          (by rw [Pf_zero]; exact ha0) hle2
        rw [h, Pf_zero, sub_zero]
        show sg ((ℓ * Int.fract s) / Ln 0 0 * (1 - polygonValue.clamp01 0)) = sg (Int.fract s)
        rw [show Ln 0 0 = (1 - polygonValue.clamp01 0) * ℓ from rfl,
          polygonValue.clamp01_eq_zero_of_nonpos le_rfl, sub_zero, one_mul, mul_one]
        have hℓne : ℓ ≠ 0 := ne_of_gt hℓpos
        rw [mul_div_cancel_left₀ (Int.fract s) hℓne]
      rw [hslice, hsg]
      have hper' : Function.Periodic γ L := hγper
      have harg : L * Int.fract s + (⌊s⌋ : ℝ) * L = L * s := by
        have h := Int.fract_add_floor s
        have h2 : (⌊s⌋ : ℝ) * L = L * ⌊s⌋ := by ring
        rw [h2, ← mul_add, h]
      rw [← harg]
      exact (hper'.int_mul ⌊s⌋ (L * Int.fract s)).symm
    have Hf_one : ∀ s : ℝ, Hf s 1 = p := by
      intro s
      have hT : Tot (polygonValue.clamp01 1) = 0 := by
        rw [polygonValue.clamp01_eq_self zero_le_one le_rfl]
        show Pf kap 1 = 0
        refine Finset.sum_eq_zero fun j _ => ?_
        rcases eq_or_ne j 0 with rfl | hj
        · show (1 - polygonValue.clamp01 1) * ℓ = 0
          rw [polygonValue.clamp01_eq_self zero_le_one le_rfl]; ring
        · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
          have hv : vec m 1 = 0 := by
            have h : ENNReal.ofReal ‖vec m 1‖ = 0 := by
              rw [← vec_norm m 1, hW1 m, hW1 (m+1), Manifold.riemannianEDist_self]
            exact norm_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp h) (norm_nonneg (vec m 1)))
          rw [show Ln (m+1) 1 = ‖vec m 1‖ from rfl, hv, norm_zero]
      show Pt (Tot (polygonValue.clamp01 1) * Int.fract s) (polygonValue.clamp01 1) = p
      rw [hT, zero_mul, polygonValue.clamp01_eq_self zero_le_one le_rfl, Pt_zero]
    -- ## (17) the arclength of a slice is affine on `[0,1]`
    have Hf_affine : ∀ t : ℝ, ∀ u ∈ Set.Icc (0:ℝ) 1,
        Submission.Length.curveLength (I := I) (fun r : ℝ => Hf r t) 0 u
          = u * Tot (polygonValue.clamp01 t) := by
      intro t u hu
      set c : ℝ := polygonValue.clamp01 t with hc_def
      have hc : c ∈ Set.Icc (0:ℝ) 1 := polygonValue.clamp01_mem t
      rcases eq_or_lt_of_le (Tot_nonneg c) with hT0 | hTpos
      · -- the totally degenerate slice is the constant loop at `p`
        have hall : (fun r : ℝ => Hf r t) = fun _ : ℝ => p := by
          funext r
          show Pt (Tot c * Int.fract r) c = p
          rw [← hT0, zero_mul, Pt_zero]
        rw [hall, Submission.Length.curveLength_const, ← hT0, mul_zero]
      · have hTotne : Tot c ≠ 0 := ne_of_gt hTpos
        -- the breakpoints of the scan, in the parameter variable
        set Q : Finset ℝ := (Finset.range (kap+1)).image (fun i => Pf i c / Tot c) with hQ
        set Bp : Finset ℝ := Q ∪ {0, 1} with hBp
        have hQ_mem : ∀ i : ℕ, i ≤ kap → Pf i c / Tot c ∈ (↑Q : Set ℝ) := by
          intro i hi
          exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)
        have hQBp : (↑Q : Set ℝ) ⊆ (↑Bp : Set ℝ) := by
          intro x hx
          exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_coe.mp hx))
        have hscaled : ∀ s : ℝ, s ∉ (↑Q : Set ℝ) → ∀ i : ℕ, i ≤ kap → Tot c * s ≠ Pf i c := by
          intro s hsQ i hi heq
          have h2 : Pf i c / Tot c = s := by rw [← heq, mul_div_cancel_left₀ s hTotne]
          exact hsQ (h2 ▸ hQ_mem i hi)
        -- away from the breakpoints the slice moves at speed `Tot c`
        have hspeed : ∀ s : ℝ, s ∈ Set.Ioo (0:ℝ) 1 → s ∉ (↑Bp : Set ℝ) →
            Submission.Length.curveSpeed (I := I) (fun r : ℝ => Hf r t) s = Tot c := by
          intro s hs hsBp
          have hsQ : s ∉ (↑Q : Set ℝ) := fun h => hsBp (hQBp h)
          have ha0 : (0:ℝ) ≤ Tot c * s := mul_nonneg hTpos.le hs.1.le
          have haT : Tot c * s ≤ Tot c := by
            have h := mul_le_mul_of_nonneg_left hs.2.le hTpos.le
            rwa [mul_one] at h
          have hspec := idx_spec (Tot c * s) c hc ha0 haT
          have hidxlt : Pf (idx (Tot c * s) c) c < Tot c * s := by
            rcases lt_or_eq_of_le (idx_le_self (Tot c * s) c hc ha0 haT) with h | h
            · exact h
            · exact absurd h.symm (hscaled s hsQ _ (le_of_lt hspec.1))
          have hidxle : Tot c * s < Pf (idx (Tot c * s) c + 1) c := by
            rcases lt_or_eq_of_le hspec.2.1 with h | h
            · exact h
            · exact absurd h (hscaled s hsQ _ (by have := hspec.1; omega))
          set i : ℕ := idx (Tot c * s) c with hi
          have hi_lt : i < kap := hspec.1
          have hLnpos : 0 < Ln i c := by
            have h := Pf_succ i c
            linarith
          have hloc : (fun r : ℝ => Hf r t)
              =ᶠ[𝓝 s] (fun r : ℝ => C i ((Tot c * r - Pf i c)/Ln i c) c) := by
            have hlt : ∀ᶠ r in 𝓝 s,
                r ∈ Set.Ioo (0:ℝ) 1 ∧ Pf i c < Tot c * r ∧ Tot c * r < Pf (i+1) c := by
              refine Filter.Eventually.and (isOpen_Ioo.mem_nhds hs) ?_
              refine Filter.Eventually.and ?_ ?_
              · exact (isOpen_lt continuous_const (continuous_const.mul continuous_id)).mem_nhds
                  (by simpa using hidxlt)
              · exact (isOpen_lt (continuous_const.mul continuous_id) continuous_const).mem_nhds
                  (by simpa using hidxle)
            filter_upwards [hlt] with r hr
            obtain ⟨hr1, hr2, hr3⟩ := hr
            have hidxr : idx (Tot c * r) c = i := by
              have hwit : i < kap ∧ Tot c * r ≤ Pf (i+1) c := ⟨hi_lt, le_of_lt hr3⟩
              have hex : ∃ j : ℕ, j < kap ∧ Tot c * r ≤ Pf (j+1) c := ⟨i, hwit⟩
              have hfind : idx (Tot c * r) c = Nat.find hex := by
                simp only [idx]; exact dif_pos hex
              rw [hfind]
              refine le_antisymm (Nat.find_min' hex hwit) ?_
              by_contra hcon
              push_neg at hcon
              have h2 : Pf (Nat.find hex + 1) c ≤ Pf i c := Pf_mono (by omega) c
              linarith [h2, hr2, (Nat.find_spec hex).2]
            show Hf r t = C i ((Tot c * r - Pf i c)/Ln i c) c
            show Pt (Tot c * Int.fract r) c = _
            rw [Int.fract_eq_self.mpr ⟨hr1.1.le, hr1.2⟩]
            show C (idx (Tot c * r) c) (((Tot c * r) - Pf (idx (Tot c * r) c) c) /
              Ln (idx (Tot c * r) c) c) c = C i ((Tot c * r - Pf i c)/Ln i c) c
            rw [hidxr]
          rw [Submission.GeodesicSpeed.curveSpeed_congr_of_eventuallyEq (I := I) hloc]
          have hx : (Tot c * s - Pf i c)/Ln i c ∈ Set.Ioo (0:ℝ) 1 :=
            ⟨div_pos (by linarith) hLnpos,
             (div_lt_one hLnpos).mpr (by linarith [Pf_succ i c])⟩
          have hxy : (Tot c / Ln i c) * s + (-(Pf i c / Ln i c)) = (Tot c * s - Pf i c)/Ln i c := by
            field_simp
            ring
          have haff : (fun r : ℝ => C i ((Tot c * r - Pf i c)/Ln i c) c)
              = (fun r : ℝ => C i ((Tot c / Ln i c) * r + (-(Pf i c / Ln i c))) c) := by
            funext r; congr 1
            field_simp
            ring
          have hmd : MDifferentiableAt 𝓘(ℝ) I (fun y : ℝ => C i y c)
              ((Tot c / Ln i c) * s + (-(Pf i c / Ln i c))) := by
            rw [hxy]
            exact C_mdiff i c _ hx
          rw [haff, Submission.Length.curveSpeed_comp_mul_add (I := I) (by positivity) hmd,
            hxy, C_speed i c _ hx, div_mul_cancel₀ (Tot c) (ne_of_gt hLnpos)]
        -- the two functions agree almost everywhere on `[0,u]`
        have hae : (fun r : ℝ => Submission.Length.curveSpeed (I := I) (fun r : ℝ => Hf r t) r)
            =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) u)] (fun _ : ℝ => Tot c) := by
          rw [Filter.EventuallyEq, MeasureTheory.ae_iff,
            MeasureTheory.Measure.restrict_apply' measurableSet_Ioc]
          refine MeasureTheory.measure_mono_null ?_ (Bp.finite_toSet.measure_zero MeasureTheory.volume)
          intro x hx
          obtain ⟨hx1, hx2⟩ := hx
          by_contra hxBp
          refine hx1 (hspeed x ⟨hx2.1, lt_of_le_of_ne (le_trans hx2.2 hu.2) ?_⟩ ?_)
          · intro hx1'
            exact hxBp (by rw [hx1']; exact Finset.mem_coe.mpr (Finset.mem_union_right _ (by simp)))
          · exact hxBp
        rw [Submission.Length.curveLength_def, intervalIntegral.integral_of_le hu.1,
          MeasureTheory.integral_congr_ae hae, MeasureTheory.setIntegral_const,
          MeasureTheory.Measure.real, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith [hu.1]), sub_zero, smul_eq_mul]
    -- ## (18) the slices are piecewise `C¹`
    have Hf_piece : ∀ t : ℝ, ∃ (k : ℕ) (a : Fin (k+1) → ℝ), StrictMono a ∧ a 0 = 0 ∧
        a (Fin.last k) = 1 ∧ ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => Hf s t)
          (Set.Icc (a j.castSucc) (a j.succ)) := by
      intro t
      set c : ℝ := polygonValue.clamp01 t with hc_def
      by_cases hT : Tot c = 0
      · refine ⟨1, fun j : Fin 2 => (((j : ℕ) : ℝ)), ?_, by simp, by simp, ?_⟩
        · intro i j hij
          show (((i : ℕ) : ℝ)) < (((j : ℕ) : ℝ))
          exact_mod_cast (Fin.lt_def.mp hij)
        · intro j
          have hconst : (fun s : ℝ => Hf s t) = fun _ : ℝ => p := by
            funext s
            show Pt (Tot c * Int.fract s) c = p
            rw [hT, zero_mul, Pt_zero]
          rw [hconst]
          exact contMDiffOn_const
      · have hTotpos : 0 < Tot c := lt_of_le_of_ne (Tot_nonneg c) (Ne.symm hT)
        have hTotne : Tot c ≠ 0 := ne_of_gt hTotpos
        set Q : Finset ℝ := ((Finset.range (kap+1)).image (fun i => Pf i c / Tot c)) ∪ {0, 1} with hQ
        have hQ0 : (0:ℝ) ∈ Q := Finset.mem_union_right _ (by simp)
        have hQ1 : (1:ℝ) ∈ Q := Finset.mem_union_right _ (by simp)
        have hQbr : ∀ i : ℕ, i ≤ kap → Pf i c / Tot c ∈ (↑Q : Set ℝ) := by
          intro i hi
          exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨i, Finset.mem_range.mpr (by omega), rfl⟩))
        have hQsub : ∀ x ∈ Q, x ∈ Set.Icc (0:ℝ) 1 := by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
            have hi' : i ≤ kap := by have := Finset.mem_range.mp hi; omega
            refine ⟨div_nonneg (Pf_mono (Nat.zero_le i) c) hTotpos.le, ?_⟩
            rw [div_le_one hTotpos]
            have := Pf_mono hi' c
            rwa [show Pf kap c = Tot c from rfl] at this
          · rcases Finset.mem_insert.mp hx with rfl | hx
            · exact ⟨le_rfl, zero_le_one⟩
            · rw [Finset.mem_singleton.mp hx]
              exact ⟨zero_le_one, le_rfl⟩
        obtain ⟨k, a, hmono, ha0, ha1, hrange⟩ :=
          polygonValue.balancing.exists_strictMono_enum hQ0 hQ1 hQsub
        have hmemIcc : ∀ i : Fin (k+1), a i ∈ Set.Icc (0:ℝ) 1 := fun i =>
          hQsub _ (Finset.mem_coe.mp (by rw [← hrange]; exact Set.mem_range_self i))
        refine ⟨k, a, hmono, ha0, ha1, ?_⟩
        intro j
        -- the midpoint of the `j`-th interval
        set m : ℝ := (a j.castSucc + a j.succ)/2 with hm
        have hjm : a j.castSucc < a j.succ :=
          hmono (Fin.castSucc_lt_succ_iff.mpr le_rfl : j.castSucc < j.succ)
        have hm_mem : m ∈ Set.Ioo (a j.castSucc) (a j.succ) := by
          constructor <;> simp only [hm] <;> linarith
        have hm01 : m ∈ Set.Icc (0:ℝ) 1 :=
          ⟨by linarith [(hmemIcc j.castSucc).1, (hmemIcc j.succ).1],
           by linarith [(hmemIcc j.castSucc).2, (hmemIcc j.succ).2]⟩
        set i : ℕ := idx (Tot c * m) c with hi
        have hm0 : (0:ℝ) ≤ Tot c * m := mul_nonneg hTotpos.le hm01.1
        have hmT : Tot c * m ≤ Tot c := by
          have h := mul_le_mul_of_nonneg_left hm01.2 hTotpos.le
          rwa [mul_one] at h
        have hspec := idx_spec (Tot c * m) c (polygonValue.clamp01_mem t) hm0 hmT
        have hi_lt : i < kap := hspec.1
        have hPfi_le : Pf i c ≤ Tot c * m := idx_le_self (Tot c * m) c
          (polygonValue.clamp01_mem t) hm0 hmT
        have hPf_le : Tot c * m ≤ Pf (i+1) c := hspec.2.1
        -- the consecutive partition points bound the slab
        have hQscale : Pf i c / Tot c ≤ a j.castSucc := by
          have hmem : Pf i c / Tot c ∈ (↑Q : Set ℝ) := hQbr i (le_of_lt hi_lt)
          obtain ⟨m', hm'⟩ := Set.mem_range.mp (by rw [hrange]; exact hmem)
          by_contra hcon
          push_neg at hcon
          have hy_le : Pf i c / Tot c ≤ m := by
            rw [div_le_iff₀ hTotpos]
            calc Pf i c ≤ Tot c * m := hPfi_le
              _ = m * Tot c := mul_comm (Tot c) m
          have hgt : a j.castSucc < a m' := by rw [hm']; exact hcon
          have hge : a j.succ ≤ a m' := by
            refine hmono.monotone ?_
            exact Fin.le_iff_val_le_val.mpr (by
              have h1 : (j.castSucc : ℕ) < (m' : ℕ) :=
                (hmono.lt_iff_lt).mp hgt
              have h2 : (j.succ : ℕ) = (j.castSucc : ℕ) + 1 := rfl
              omega)
          rw [hm'] at hge
          linarith [hge, hy_le, hm_mem.2]
        have hQscale' : a j.succ ≤ Pf (i+1) c / Tot c := by
          have hmem : Pf (i+1) c / Tot c ∈ (↑Q : Set ℝ) := hQbr (i+1) (by omega)
          obtain ⟨m', hm'⟩ := Set.mem_range.mp (by rw [hrange]; exact hmem)
          by_contra hcon
          push_neg at hcon
          have hy_ge : m ≤ Pf (i+1) c / Tot c := by
            rw [le_div_iff₀ hTotpos]
            calc m * Tot c = Tot c * m := mul_comm m (Tot c)
              _ ≤ Pf (i+1) c := hPf_le
          have hlt : a m' < a j.succ := by rw [hm']; exact hcon
          have hle : a m' ≤ a j.castSucc := by
            refine hmono.monotone ?_
            by_contra hcon2
            push_neg at hcon2
            have h1 : a j.succ ≤ a m' := by
              refine hmono.monotone ?_
              exact Fin.le_iff_val_le_val.mpr (by
                have h2 : (j.castSucc : ℕ) < (m' : ℕ) :=
                  Fin.lt_iff_val_lt_val.mpr (by omega)
                have h3 : (j.succ : ℕ) = (j.castSucc : ℕ) + 1 := rfl
                omega)
            linarith
          rw [hm'] at hle
          linarith [hle, hy_ge, hm_mem.1]
        -- the slab covers the interval
        have hcover : ∀ s ∈ Set.Icc (a j.castSucc) (a j.succ),
            Pf i c ≤ Tot c * s ∧ Tot c * s ≤ Pf (i+1) c := by
          intro s hs
          constructor
          · have h1 : Tot c * (Pf i c / Tot c) ≤ Tot c * a j.castSucc :=
              mul_le_mul_of_nonneg_left hQscale hTotpos.le
            rw [mul_div_cancel₀ _ hTotne] at h1
            have h2 : Tot c * a j.castSucc ≤ Tot c * s :=
              mul_le_mul_of_nonneg_left hs.1 hTotpos.le
            linarith
          · have h1 : Tot c * a j.succ ≤ Tot c * (Pf (i+1) c / Tot c) :=
              mul_le_mul_of_nonneg_left hQscale' hTotpos.le
            rw [mul_div_cancel₀ _ hTotne] at h1
            have h2 : Tot c * s ≤ Tot c * a j.succ :=
              mul_le_mul_of_nonneg_left hs.2 hTotpos.le
            linarith
        -- the slice agrees with the piece on the interval
        have hEq : ∀ s ∈ Set.Icc (a j.castSucc) (a j.succ), Hf s t
            = C i ((Tot c * s - Pf i c)/Ln i c) c := by
          intro s hs
          have hs01 : s ∈ Set.Icc (0:ℝ) 1 :=
            ⟨le_trans (hmemIcc j.castSucc).1 hs.1, le_trans hs.2 (hmemIcc j.succ).2⟩
          have hsT : Tot c * s ≤ Tot c := by
            have h := mul_le_mul_of_nonneg_left hs01.2 hTotpos.le
            rwa [mul_one] at h
          rcases lt_or_eq_of_le hs01.2 with hs1 | hs1
          · show Pt (Tot c * Int.fract s) c = _
            rw [Int.fract_eq_self.mpr ⟨hs01.1, hs1⟩]
            exact slab_agree i (Tot c * s) c (polygonValue.clamp01_mem t) hi_lt
              (mul_nonneg hTotpos.le hs01.1) hsT (hcover s hs).1 (hcover s hs).2
          · -- at the right endpoint `s = 1` of the last slab the two formulae still agree
            subst hs1
            have hsucc1 : a j.succ = 1 := le_antisymm (hmemIcc j.succ).2 hs.2
            have hPT : Tot c ≤ Pf (i+1) c := by
              have h1 := hQscale'
              rw [hsucc1, le_div_iff₀ hTotpos, one_mul] at h1
              exact h1
            have hL1 : Hf 1 t = p := by
              show Pt (Tot c * Int.fract 1) c = p
              rw [Int.fract_one, mul_zero]
              exact Pt_zero c
            have hR1 : C i ((Tot c * 1 - Pf i c)/Ln i c) c = p := by
              rw [mul_one, ← slab_agree i (Tot c) c (polygonValue.clamp01_mem t) hi_lt
                (Tot_nonneg c) le_rfl (Pf_le_Tot i c (by omega)) hPT]
              exact Pt_tot c
            rw [hL1, hR1]
        -- the piece is smooth
        have hLnpos : 0 < Ln i c := by
          have h2 : Tot c * m < Pf (i+1) c := by
            rcases lt_or_eq_of_le hPf_le with h | h
            · exact h
            · exfalso
              have hmem : Pf (i+1) c / Tot c ∈ (↑Q : Set ℝ) := hQbr (i+1) (by omega)
              obtain ⟨m', hm'⟩ := Set.mem_range.mp (by rw [hrange]; exact hmem)
              have hm'_eq : a m' = m := by
                rw [hm', ← h, mul_div_cancel_left₀ m hTotne]
              have hlt1 : (j.castSucc : ℕ) < (m' : ℕ) :=
                (hmono.lt_iff_lt).mp (by rw [hm'_eq]; exact hm_mem.1)
              have hlt2 : (m' : ℕ) < (j.succ : ℕ) :=
                (hmono.lt_iff_lt).mp (by rw [hm'_eq]; exact hm_mem.2)
              have hcs : (j.succ : ℕ) = (j.castSucc : ℕ) + 1 := by simp
              omega
          have h := Pf_succ i c
          linarith
        have haffine : ContMDiffOn 𝓘(ℝ) I 1
            (fun s : ℝ => C i ((Tot c * s - Pf i c)/Ln i c) c)
            (Set.Icc (a j.castSucc) (a j.succ)) := by
          have hg : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
              (fun s : ℝ => (Tot c / Ln i c) * s + (-(Pf i c / Ln i c))) :=
            (contMDiff_const.mul contMDiff_id).add contMDiff_const
          have h3 : ContMDiffOn 𝓘(ℝ) I ∞ (fun x : ℝ => C i x c) (Set.Icc (0:ℝ) 1) :=
            C_cmdiff i c
          have h4 : (fun s : ℝ => C i ((Tot c * s - Pf i c)/Ln i c) c)
              = (fun s : ℝ => C i ((Tot c / Ln i c) * s + (-(Pf i c / Ln i c))) c) := by
            funext s; congr 1
            field_simp
            ring
          rw [h4]
          refine (h3.comp (hg.contMDiffOn (s := Set.Icc (a j.castSucc) (a j.succ)))
            (fun s hs' => ?_)).of_le (by norm_num)
          show (Tot c / Ln i c) * s + (-(Pf i c / Ln i c)) ∈ Set.Icc (0:ℝ) 1
          have h5 : (Tot c / Ln i c) * s + (-(Pf i c / Ln i c))
              = (Tot c * s - Pf i c)/Ln i c := by
            field_simp
            ring
          rw [h5]
          refine ⟨div_nonneg ?_ hLnpos.le, (div_le_one hLnpos).mpr ?_⟩
          · have h6 := (hcover s hs').1
            linarith
          · have h7 := (hcover s hs').2
            have h8 := Pf_succ i c
            linarith
        exact haffine.congr (fun s hs => hEq s hs)
    -- ## (18) the speed of a slice is `1`-periodic, hence interval integrable everywhere
    have hspeed_per : ∀ t : ℝ, Function.Periodic
        (Submission.Length.curveSpeed (I := I) (fun s : ℝ => Hf s t)) 1 :=
      fun t r => curveSpeed_add_one (I := I) (fun r => Hf_per r t) r
    have Hf_hint : ∀ t a b : ℝ, IntervalIntegrable
        (Submission.Length.curveSpeed (I := I) (fun s : ℝ => Hf s t))
        MeasureTheory.volume a b := by
      intro t a b
      have hunt : IntervalIntegrable
          (Submission.Length.curveSpeed (I := I) (fun s : ℝ => Hf s t))
          MeasureTheory.volume 0 1 := by
        obtain ⟨k, a', hmono, ha0, ha1, hpiece⟩ := Hf_piece t
        exact Work.OddBound.liftPiecewise.intervalIntegrable_curveSpeed_piecewise (I := I)
          (h := fun s : ℝ => Hf s t) (S := 1) hmono ha0 ha1 hpiece 0 1
          (by norm_num) (by norm_num) (by norm_num)
      exact Function.Periodic.intervalIntegrable₀ (T := 1) (hspeed_per t) one_ne_zero hunt a b
    -- ## (19) the arclength of a slice is affine on all of `ℝ`
    have Hf_bal : ∀ t s : ℝ,
        Submission.Length.curveLength (I := I) (fun r : ℝ => Hf r t) 0 s
          = s * Submission.Length.curveLength (I := I) (fun r : ℝ => Hf r t) 0 1 := by
      intro t s
      have haff : ∀ u ∈ Set.Icc (0:ℝ) 1,
          Submission.Length.curveLength (I := I) (fun r : ℝ => Hf r t) 0 u
            = u * Submission.Length.curveLength (I := I) (fun r : ℝ => Hf r t) 0 1 := by
        intro u hu
        rw [Hf_affine t u hu]
        have h1 := Hf_affine t 1 (by norm_num)
        rw [h1, one_mul]
      exact Work.PeriodicLength.curveLength_eq_mul_of_periodic_of_affine (I := I)
        (f := fun r : ℝ => Hf r t)
        (T := Submission.Length.curveLength (I := I) (fun r : ℝ => Hf r t) 0 1)
        (fun r => Hf_per r t) (Hf_hint t) haff s
    -- ## (20) the length bound
    have hTot_le : ∀ t : ℝ, Tot t ≤ ℓ + (Kn : ℝ) * ρ := by
      intro t
      have hsplit : Tot t = Ln 0 t + ∑ j ∈ Finset.range Kn, Ln (j+1) t := by
        show (∑ j ∈ Finset.range (Kn+1), Ln j t)
            = Ln 0 t + ∑ j ∈ Finset.range Kn, Ln (j+1) t
        rw [Finset.sum_range_succ']
        ring
      rw [hsplit]
      have h1 : Ln 0 t ≤ ℓ := by
        have hcl : (0:ℝ) ≤ polygonValue.clamp01 t := (polygonValue.clamp01_mem t).1
        have hle1 : 1 - polygonValue.clamp01 t ≤ 1 := by linarith
        have hmul : (1 - polygonValue.clamp01 t) * ℓ ≤ 1 * ℓ :=
          mul_le_mul_of_nonneg_right hle1 hℓnonneg
        simpa [Ln] using hmul
      have h2 : (∑ j ∈ Finset.range Kn, Ln (j+1) t) ≤ (Kn : ℝ) * ρ := by
        have h3 : (∑ j ∈ Finset.range Kn, Ln (j+1) t) = ∑ j ∈ Finset.range Kn, ‖vec j t‖ :=
          Finset.sum_congr rfl (fun j _ => by show Ln (j+1) t = ‖vec j t‖; simp [Ln])
        rw [h3]
        calc ∑ j ∈ Finset.range Kn, ‖vec j t‖ ≤ ∑ j ∈ Finset.range Kn, ρ :=
              Finset.sum_le_sum (fun j _ => (vec_norm_lt j t).le)
          _ = (Kn : ℝ) * ρ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      linarith
    -- ## (21) the conclusion
    refine ⟨Hf, ℓ + (Kn : ℝ) * ρ + 1, ?_, Hf_cont, Hf_per, Hf_base, Hf_zero, Hf_one,
      Hf_piece, ?_, Hf_bal⟩
    · nlinarith [hℓpos, hρpos, hKnn]
    · intro t
      have h1 := Hf_affine t 1 (by norm_num)
      rw [h1, one_mul]
      have h2 := hTot_le (polygonValue.clamp01 t)
      linarith
  · -- ===================== degenerate case `\u2113 \u2264 0` =====================
    -- The loop `sg` has vanishing speed, hence it is constant.
    have hℓ0 : ℓ = 0 := le_antisymm hℓnp hℓnonneg
    have hspeed0 : ∀ s : ℝ, Submission.Length.curveSpeed (I := I) sg s = 0 := by
      intro s
      rw [hspeed s, hℓ0]
    haveI hcrb' : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
    have hsg_const : ∀ s : ℝ, sg s = p := by
      have h01 : ∀ u ∈ Set.Icc (0:ℝ) 1, sg u = p := by
        intro u hu
        have hsm : ContMDiffOn 𝓘(ℝ) I 1 sg (Set.Icc (0:ℝ) u) :=
          hsg_sm.contMDiffOn.of_le (by norm_num)
        have hle := Manifold.riemannianEDist_le_pathELength (I := I) hsm rfl rfl hu.1
        rw [(Work.OddBound.longHomotopy.curveLength_toolkit (I := I) hsm).2.2 0 u le_rfl hu.1
          le_rfl] at hle
        have hzero : Submission.Length.curveLength (I := I) sg 0 u = 0 := by
          rw [Submission.Length.curveLength_def]
          simp only [hspeed0]
          exact intervalIntegral.integral_zero
        rw [hzero, ENNReal.ofReal_zero] at hle
        have hz : Manifold.riemannianEDist I (sg 0) (sg u) = 0 := le_antisymm hle zero_le
        rw [← (Submission.EDist.riemannianEDist_eq_zero_iff (I := I)).mp hz, hsg0]
      intro s
      have hshift : sg s = sg (Int.fract s) := by
        have hper' : Function.Periodic sg 1 := hsg_per
        have h := hper'.int_mul ⌊s⌋ (Int.fract s)
        have harg : Int.fract s + (⌊s⌋ : ℝ) * 1 = s := by
          rw [mul_one]
          exact Int.fract_add_floor s
        rwa [harg] at h
      rw [hshift]
      exact h01 (Int.fract s) ⟨Int.fract_nonneg s, le_of_lt (Int.fract_lt_one s)⟩
    refine ⟨fun _ _ => p, 1, one_pos, continuous_const, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun s t => rfl
    · exact fun t => rfl
    · intro s
      show p = sg s
      exact (hsg_const s).symm
    · exact fun s => rfl
    · intro t
      refine ⟨1, fun j : Fin 2 => ((j : ℕ) : ℝ), ?_, by simp, by simp, ?_⟩
      · intro i j hij
        show (((i : ℕ) : ℝ)) < (((j : ℕ) : ℝ))
        exact_mod_cast (Fin.lt_def.mp hij)
      · intro j
        exact contMDiffOn_const
    · intro t
      rw [Submission.Length.curveLength_const]
      norm_num
    · intro t s
      rw [Submission.Length.curveLength_const, Submission.Length.curveLength_const, mul_zero]

end Work.OddBound