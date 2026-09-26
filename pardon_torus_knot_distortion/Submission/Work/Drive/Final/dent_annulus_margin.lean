import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Final.dent_annulus_defs
import Submission.Work.Drive.Final.param_add_int_mul_two_pi
import Submission.Work.Drive.Final.exists_smul_of_det2_eq_zero
import Submission.Work.Drive.Final.norm_fderiv_boxNorm_comp_param_le
import Submission.Work.Drive.Final.fderiv_add_of_periodic
import Submission.Work.Drive.Final.abs_det2_fderiv_boxNorm_comp_param

/-!
# The margin of the annulus of an event of the tilted sweep

(L4a/L4b of the design, `NOTES_LEAD_L4b.md` §1 C.)  At an event `pp` of the tilted sweep the
differentials of the sweep height, of the slab functional and of the box norm are *uniformly*
non-degenerate on the part of the surface that lies in the annulus
`r/2 ≤ ‖par q − par pp‖ ≤ r` of the closed box and the closed slab.

The annulus is compact modulo the period lattice `(2πℤ)²` of the parametrisation, the degenerate
configurations (critical points of the sweep height, tangencies to a slab face, corner points of the
box) are exactly the events of the three types, and `anyEvent_isolated` excludes every event at
distance `≤ r₁` from `pp` other than `pp` itself.  Since the annulus keeps distance `≥ r/2 > 0` from
`pp`, it carries no event at all, and a compactness argument gives the uniform constants.

The file contains the vocabulary (`fundDomain`, `AnnulusRegion`), the elementary ingredients
(closedness, continuity, the comparison of `boxNorm` with a coordinate), the two compactness
extraction lemmas `exists_pos_min_on` / `exists_bound_max_on`, and the theorem.
-/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set
open Work.Drive.EpsForm (sweepHeight)
open Work.BoxShrink.Pinch (par)

noncomputable section

/-! ## The period lattice and the fundamental domain -/

/-- The fundamental domain `[0,2π] × [0,2π]` of the period lattice of the parametrisation. -/
def fundDomain : Set (ℝ × ℝ) := Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)

theorem isCompact_fundDomain : IsCompact fundDomain := isCompact_Icc.prod isCompact_Icc

/-- Every point of the parameter plane differs from a point of the fundamental domain by an
integer multiple of the period vector. -/
theorem exists_fundDomain_add (q : ℝ × ℝ) :
    ∃ q₀ : ℝ × ℝ, q₀ ∈ fundDomain ∧
      q = q₀ + (((⌊q.1 / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi),
                ((⌊q.2 / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi)) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨(q.1 - ((⌊q.1 / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi),
           q.2 - ((⌊q.2 / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi)), ?_, ?_⟩
  · constructor
    · constructor
      · have h := Int.floor_le (q.1 / (2 * Real.pi))
        have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hpi)
        rw [div_mul_cancel₀ _ (ne_of_gt hpi)] at h2
        linarith
      · have h := Int.lt_floor_add_one (q.1 / (2 * Real.pi))
        have h2 := mul_lt_mul_of_pos_right h hpi
        rw [div_mul_cancel₀ _ (ne_of_gt hpi)] at h2
        nlinarith [h2]
    · constructor
      · have h := Int.floor_le (q.2 / (2 * Real.pi))
        have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hpi)
        rw [div_mul_cancel₀ _ (ne_of_gt hpi)] at h2
        linarith
      · have h := Int.lt_floor_add_one (q.2 / (2 * Real.pi))
        have h2 := mul_lt_mul_of_pos_right h hpi
        rw [div_mul_cancel₀ _ (ne_of_gt hpi)] at h2
        nlinarith [h2]
  · ext <;> simp

/-! ## The annulus region -/

/-- The region of the statement: the part of the parameter plane whose image lies in the annulus
`r/2 ≤ ‖· − par pp‖ ≤ r`, in the closure of the box and in the closed slab. -/
def AnnulusRegion (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) (pp : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  {q | r / 2 ≤ ‖par ψ q - par ψ pp‖ ∧
       ‖par ψ q - par ψ pp‖ ≤ r ∧
       par ψ q ∈ closure (Submission.PBox s c σ) ∧
       |slabFn c u v (par ψ q)| ≤ h}

theorem mem_AnnulusRegion {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ} {v : R3} {h : ℝ} {pp : ℝ × ℝ} {r : ℝ} {q : ℝ × ℝ} :
    q ∈ AnnulusRegion ψ s c σ u v h pp r ↔
      r / 2 ≤ ‖par ψ q - par ψ pp‖ ∧
      ‖par ψ q - par ψ pp‖ ≤ r ∧
      par ψ q ∈ closure (Submission.PBox s c σ) ∧
      |slabFn c u v (par ψ q)| ≤ h := Iff.rfl

/-! ## Elementary ingredients -/

theorem continuous_boxNorm (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous (fun y : R3 => Submission.boxNorm c σ y) := by
  unfold Submission.boxNorm
  fun_prop

theorem continuous_boxNorm_comp_par (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous (fun q : ℝ × ℝ => Submission.boxNorm c σ (par ψ q)) :=
  (continuous_boxNorm c σ).comp (Work.Smooth.Morse.param_continuous ψ)

theorem contDiff_slabFnPar (ψ : Submission.Diffeo) (c : R3) (u : ℝ) (v : R3) :
    ContDiff ℝ (⊤ : ℕ∞) (slabFnPar ψ c u v) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y : R3 => inner ℝ v y - (inner ℝ v c + u)) :=
    (ContDiff.inner ℝ contDiff_const contDiff_id).sub contDiff_const
  exact Work.Smooth.Morse.pullback_contDiff ψ hg

theorem continuous_slabFnPar (ψ : Submission.Diffeo) (c : R3) (u : ℝ) (v : R3) :
    Continuous (fun q : ℝ × ℝ => slabFn c u v (par ψ q)) :=
  (contDiff_slabFnPar ψ c u v).continuous

theorem contDiff_coordPar (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q' : ℝ × ℝ => par ψ q' (σ i)) :=
  (ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) (σ i))).comp
    (Work.Smooth.Morse.param_contDiff ψ)

/-- The `tiltedSlabClosed` of the sweep is the closed slab of the slab functional. -/
theorem tiltedSlabClosed_eq (c : R3) (u h : ℝ) (v : R3) :
    Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h =
      {y : R3 | |slabFn c u v y| ≤ h} := by
  ext y; rfl

/-- The closure of the box is contained in the sublevel set of the box norm. -/
theorem boxNorm_le_of_mem_closure (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (y : R3)
    (hy : y ∈ closure (Submission.PBox s c σ)) : Submission.boxNorm c σ y ≤ s :=
  closure_minimal (fun z hz => le_of_lt ((Submission.mem_PBox_iff s c σ z).mp hz))
    (isClosed_le (continuous_boxNorm c σ) continuous_const) hy

/-- The box norm dominates each of its three coordinates. -/
theorem div_le_boxNorm (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) (i : Fin 3) :
    |y (σ i) - c (σ i)| / Submission.boxSide i ≤ Submission.boxNorm c σ y := by
  rw [Submission.boxNorm]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

/-- A coordinate attaining the maximum of the box norm. -/
theorem exists_boxSide_mul_eq_of_boxNorm_eq (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (y : R3)
    (h : Submission.boxNorm c σ y = s) :
    ∃ i : Fin 3, |y (σ i) - c (σ i)| = Submission.boxSide i * s := by
  rw [Submission.boxNorm] at h
  rcases max_eq_iff.mp h with ⟨h', _⟩ | ⟨h2, _⟩
  · rcases max_eq_iff.mp h' with ⟨h0, _⟩ | ⟨h1, _⟩
    · exact ⟨0, by rw [div_eq_iff (Submission.boxSide_pos 0).ne'] at h0; rw [h0]; ring⟩
    · exact ⟨1, by rw [div_eq_iff (Submission.boxSide_pos 1).ne'] at h1; rw [h1]; ring⟩
  · exact ⟨2, by rw [div_eq_iff (Submission.boxSide_pos 2).ne'] at h2; rw [h2]; ring⟩

/-- The annulus region is closed. -/
theorem isClosed_AnnulusRegion (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (pp : ℝ × ℝ) (r : ℝ) :
    IsClosed (AnnulusRegion ψ s c σ u v h pp r) := by
  have hpar : Continuous (fun q : ℝ × ℝ => par ψ q) :=
    Work.Smooth.Morse.param_continuous ψ
  have h1 : Continuous (fun q : ℝ × ℝ => ‖par ψ q - par ψ pp‖) :=
    continuous_norm.comp (hpar.sub continuous_const)
  have : AnnulusRegion ψ s c σ u v h pp r =
      {q : ℝ × ℝ | r / 2 ≤ ‖par ψ q - par ψ pp‖} ∩
      ({q : ℝ × ℝ | ‖par ψ q - par ψ pp‖ ≤ r} ∩
      ({q : ℝ × ℝ | par ψ q ∈ closure (Submission.PBox s c σ)} ∩
      {q : ℝ × ℝ | |slabFn c u v (par ψ q)| ≤ h})) := by
    ext q; simp [AnnulusRegion]
  rw [this]
  refine IsClosed.inter (isClosed_le continuous_const h1) ?_
  refine IsClosed.inter (isClosed_le h1 continuous_const) ?_
  refine IsClosed.inter (isClosed_closure.preimage hpar) ?_
  exact isClosed_le (continuous_abs.comp (continuous_slabFnPar ψ c u v)) continuous_const

/-! ## Compactness extraction -/

/-- A continuous function that is positive on the region attains a positive minimum there. -/
theorem exists_pos_min_on (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h : ℝ) (pp : ℝ × ℝ) (r : ℝ) (T : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ)
    (hT : IsClosed T) (hf : Continuous f)
    (hpos : ∀ q ∈ fundDomain ∩ (AnnulusRegion ψ s c σ u v h pp r ∩ T), 0 < f q) :
    ∃ m : ℝ, 0 < m ∧ ∀ q ∈ fundDomain ∩ (AnnulusRegion ψ s c σ u v h pp r ∩ T), m ≤ f q := by
  by_cases hne : (fundDomain ∩ (AnnulusRegion ψ s c σ u v h pp r ∩ T)).Nonempty
  · obtain ⟨x, hx, hmin⟩ := (isCompact_fundDomain.inter_right
      ((isClosed_AnnulusRegion ψ s c σ u v h pp r).inter hT)).exists_isMinOn hne hf.continuousOn
    exact ⟨f x, hpos x hx, fun q hq => hmin hq⟩
  · exact ⟨1, one_pos, fun q hq => absurd ⟨q, hq⟩ hne⟩

/-- A continuous function on the region is bounded above there. -/
theorem exists_bound_max_on (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h : ℝ) (pp : ℝ × ℝ) (r : ℝ) (T : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ)
    (hT : IsClosed T) (hf : Continuous f) :
    ∃ M : ℝ, 0 < M ∧ ∀ q ∈ fundDomain ∩ (AnnulusRegion ψ s c σ u v h pp r ∩ T), f q ≤ M := by
  by_cases hne : (fundDomain ∩ (AnnulusRegion ψ s c σ u v h pp r ∩ T)).Nonempty
  · obtain ⟨x, hx, hmin⟩ := (isCompact_fundDomain.inter_right
      ((isClosed_AnnulusRegion ψ s c σ u v h pp r).inter hT)).exists_isMinOn hne hf.neg.continuousOn
    refine ⟨max (f x) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun q hq => ?_⟩
    have hle : -(f x) ≤ -(f q) := by
      simpa using hmin hq
    exact le_trans (by linarith) (le_max_left _ _)
  · exact ⟨1, one_pos, fun q hq => absurd ⟨q, hq⟩ hne⟩


/-! ## Periodicity of the quantities of the statement -/

theorem fderiv_param_eq_of_add_period {ψ : Submission.Diffeo} {q q₀ : ℝ × ℝ} (k m : ℤ)
    (h : q = q₀ + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi))) :
    fderiv ℝ (par ψ) q = fderiv ℝ (par ψ) q₀ := by
  rw [h]
  exact fderiv_add_of_periodic (fun x => param_add_int_mul_two_pi ψ x k m) q₀

theorem fderiv_sweepHeight_eq_of_add_period {ψ : Submission.Diffeo} {ℓ : R3 →L[ℝ] ℝ}
    {q q₀ : ℝ × ℝ} (k m : ℤ)
    (h : q = q₀ + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi))) :
    fderiv ℝ (sweepHeight ψ ℓ) q = fderiv ℝ (sweepHeight ψ ℓ) q₀ := by
  rw [h]
  exact fderiv_add_of_periodic (fun x => by
    show ℓ (par ψ (x.1 + (k : ℝ) * (2 * Real.pi), x.2 + (m : ℝ) * (2 * Real.pi))) = ℓ (par ψ x)
    rw [param_add_int_mul_two_pi]) q₀

theorem fderiv_slabFnPar_eq_of_add_period {ψ : Submission.Diffeo} {c : R3} {u : ℝ} {v : R3}
    {q q₀ : ℝ × ℝ} (k m : ℤ)
    (h : q = q₀ + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi))) :
    fderiv ℝ (slabFnPar ψ c u v) q = fderiv ℝ (slabFnPar ψ c u v) q₀ := by
  rw [h]
  exact fderiv_add_of_periodic (fun x => by
    show slabFn c u v (par ψ (x.1 + (k : ℝ) * (2 * Real.pi), x.2 + (m : ℝ) * (2 * Real.pi))) =
      slabFn c u v (par ψ x)
    rw [param_add_int_mul_two_pi]) q₀

theorem fderiv_boxNormPar_eq_of_add_period {ψ : Submission.Diffeo} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {q q₀ : ℝ × ℝ} (k m : ℤ)
    (h : q = q₀ + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi))) :
    fderiv ℝ (fun q' : ℝ × ℝ => Submission.boxNorm c σ (par ψ q')) q =
      fderiv ℝ (fun q' : ℝ × ℝ => Submission.boxNorm c σ (par ψ q')) q₀ := by
  rw [h]
  exact fderiv_add_of_periodic (fun x => by
    show Submission.boxNorm c σ (par ψ (x.1 + (k : ℝ) * (2 * Real.pi),
        x.2 + (m : ℝ) * (2 * Real.pi))) = Submission.boxNorm c σ (par ψ x)
    rw [param_add_int_mul_two_pi]) q₀

theorem fderiv_coordPar_eq_of_add_period {ψ : Submission.Diffeo} {σ : Equiv.Perm (Fin 3)}
    {i : Fin 3} {q q₀ : ℝ × ℝ} (k m : ℤ)
    (h : q = q₀ + ((k : ℝ) * (2 * Real.pi), (m : ℝ) * (2 * Real.pi))) :
    fderiv ℝ (fun q' : ℝ × ℝ => par ψ q' (σ i)) q =
      fderiv ℝ (fun q' : ℝ × ℝ => par ψ q' (σ i)) q₀ := by
  rw [h]
  exact fderiv_add_of_periodic (fun x => by
    show par ψ (x.1 + (k : ℝ) * (2 * Real.pi), x.2 + (m : ℝ) * (2 * Real.pi)) (σ i) =
      par ψ x (σ i)
    rw [param_add_int_mul_two_pi]) q₀

/-! ## The theorem -/

theorem dent_annulus_margin {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {pp : ℝ × ℝ} (hpp : Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp)
    {r₁ : ℝ} (hr₁ : 0 < r₁)
    (hiso : ∀ p' : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p' →
      ‖Work.BoxShrink.Pinch.par ψ p' - Work.BoxShrink.Pinch.par ψ pp‖ ≤ r₁ →
      Work.BoxShrink.Pinch.par ψ p' = Work.BoxShrink.Pinch.par ψ pp)
    {r : ℝ} (hr : 0 < r) (hrr : r ≤ r₁)
    (hslack : ∀ q' : ℝ × ℝ,
      r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - Work.BoxShrink.Pinch.par ψ pp‖ →
      ‖Work.BoxShrink.Pinch.par ψ q' - Work.BoxShrink.Pinch.par ψ pp‖ ≤ r →
      ¬ (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s ∧
        |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h)) :
    ∃ m : ℝ, 0 < m ∧ ∃ M : ℝ, 0 < M ∧ ∀ q' : ℝ × ℝ,
      r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - Work.BoxShrink.Pinch.par ψ pp‖ →
      ‖Work.BoxShrink.Pinch.par ψ q' - Work.BoxShrink.Pinch.par ψ pp‖ ≤ r →
      Work.BoxShrink.Pinch.par ψ q' ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| ≤ h →
      ‖fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q'‖ ≤ M ∧
      ‖fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q'‖ ≤ M ∧
      m ≤ ‖fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q'‖ ∧
      (|Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h →
        m ≤ |Work.Drive.Final.det2 (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q')
                 (fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q')|) ∧
      (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s →
        ‖fderiv ℝ (fun q'' : ℝ × ℝ =>
            Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q'')) q'‖ ≤ M ∧
        m ≤ |Work.Drive.Final.det2 (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) q')
                 (fderiv ℝ (fun q'' : ℝ × ℝ =>
                    Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q'')) q')|) := by
  classical
  -- the two clauses of `GoodSweepData3` that the argument uses
  obtain ⟨_, _, _, _, hGammaT, hFaceReg, _, _, _, _⟩ := hDP.2.1
  -- 1. no event of the sweep lies in the annulus
  have hnoEv : ∀ p' : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p' →
      r / 2 ≤ ‖par ψ p' - par ψ pp‖ → ‖par ψ p' - par ψ pp‖ ≤ r → False := by
    intro p' hp' hd hdr
    have h := hiso p' hp' (le_trans hdr hrr)
    rw [h] at hd
    simp only [sub_self, norm_zero] at hd
    linarith
  -- 2. pointwise non-degeneracy on the region
  have hLne : ∀ q : ℝ × ℝ, q ∈ AnnulusRegion ψ s c σ u v h pp r →
      fderiv ℝ (sweepHeight ψ ℓ) q ≠ 0 := by
    intro q hq
    obtain ⟨h1, h2, hbox, hslab⟩ := mem_AnnulusRegion.mp hq
    by_cases hbs : Submission.boxNorm c σ (par ψ q) = s
    · simpa using (hGammaT q hbs hslab).2 0
    · have hlt : Submission.boxNorm c σ (par ψ q) < s :=
        lt_of_le_of_ne (boxNorm_le_of_mem_closure c σ s _ hbox) hbs
      have hmem : par ψ q ∈ Submission.PBox s c σ := (Submission.mem_PBox_iff s c σ _).mpr hlt
      intro hcrit
      by_cases hsh : |slabFn c u v (par ψ q)| = h
      · exact hnoEv q (Or.inr (Or.inl ⟨hmem, hsh, ⟨0, by rw [hcrit]; simp⟩⟩)) h1 h2
      · refine hnoEv q (Or.inl ⟨hmem, ?_, hcrit⟩) h1 h2
        rw [tiltedSlabClosed_eq]
        exact le_of_lt (lt_of_le_of_ne hslab hsh)
  have hBoxDiff : ∀ q : ℝ × ℝ, q ∈ AnnulusRegion ψ s c σ u v h pp r →
      Submission.boxNorm c σ (par ψ q) = s →
      fderiv ℝ (fun q' : ℝ × ℝ => Submission.boxNorm c σ (par ψ q')) q ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (sweepHeight ψ ℓ) q ≠
        t • fderiv ℝ (fun q' : ℝ × ℝ => Submission.boxNorm c σ (par ψ q')) q := by
    intro q hq hbs
    exact hGammaT q hbs (mem_AnnulusRegion.mp hq).2.2.2
  have hdet2_slab : ∀ q : ℝ × ℝ, q ∈ AnnulusRegion ψ s c σ u v h pp r →
      |slabFn c u v (par ψ q)| = h →
      det2 (fderiv ℝ (sweepHeight ψ ℓ) q) (fderiv ℝ (slabFnPar ψ c u v) q) ≠ 0 := by
    intro q hq hslab
    obtain ⟨h1, h2, hbox, -⟩ := mem_AnnulusRegion.mp hq
    by_cases hbs : Submission.boxNorm c σ (par ψ q) = s
    · exact (hnoEv q (Or.inr (Or.inr ⟨hbox, hbs, hslab⟩)) h1 h2).elim
    · intro hdet
      obtain ⟨t, ht⟩ := exists_smul_of_det2_eq_zero (hFaceReg q hbox hslab) hdet
      have hlt : Submission.boxNorm c σ (par ψ q) < s :=
        lt_of_le_of_ne (boxNorm_le_of_mem_closure c σ s _ hbox) hbs
      exact hnoEv q
        (Or.inr (Or.inl ⟨(Submission.mem_PBox_iff s c σ _).mpr hlt, hslab, ⟨t, ht⟩⟩)) h1 h2
  have hdet2_box : ∀ q : ℝ × ℝ, q ∈ AnnulusRegion ψ s c σ u v h pp r →
      Submission.boxNorm c σ (par ψ q) = s →
      det2 (fderiv ℝ (sweepHeight ψ ℓ) q)
        (fderiv ℝ (fun q' : ℝ × ℝ => Submission.boxNorm c σ (par ψ q')) q) ≠ 0 := by
    intro q hq hbs hdet
    obtain ⟨t, ht⟩ := exists_smul_of_det2_eq_zero (hBoxDiff q hq hbs).1 hdet
    exact (hBoxDiff q hq hbs).2 t ht
  -- 3. continuity of the differentials
  have hcontPar : Continuous (fun q : ℝ × ℝ => fderiv ℝ (par ψ) q) :=
    (Work.Smooth.Morse.param_contDiff ψ).continuous_fderiv (by simp)
  have hcontSweep : Continuous (fun q : ℝ × ℝ => fderiv ℝ (sweepHeight ψ ℓ) q) :=
    (Work.Drive.EpsForm.sweepHeight_contDiff_two ψ ℓ).continuous_fderiv (by norm_num)
  have hcontSlab : Continuous (fun q : ℝ × ℝ => fderiv ℝ (slabFnPar ψ c u v) q) :=
    (contDiff_slabFnPar ψ c u v).continuous_fderiv (by simp)
  have hcontCoord : ∀ i : Fin 3,
      Continuous (fun q : ℝ × ℝ => fderiv ℝ (fun q' : ℝ × ℝ => par ψ q' (σ i)) q) :=
    fun i => (contDiff_coordPar ψ σ i).continuous_fderiv (by simp)
  have hcontDet2 : ∀ (A B : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ),
      Continuous A → Continuous B → Continuous (fun q : ℝ × ℝ => det2 (A q) (B q)) := by
    intro A B hA hB
    have h10 : Continuous (fun q : ℝ × ℝ => A q (1, 0)) := hA.clm_apply continuous_const
    have h01 : Continuous (fun q : ℝ × ℝ => A q (0, 1)) := hA.clm_apply continuous_const
    have hd10 : Continuous (fun q : ℝ × ℝ => B q (1, 0)) := hB.clm_apply continuous_const
    have hd01 : Continuous (fun q : ℝ × ℝ => B q (0, 1)) := hB.clm_apply continuous_const
    exact ((h10.mul hd01).sub (h01.mul hd10))
  -- 4. the constants
  obtain ⟨M1, hM1pos, hM1⟩ := exists_bound_max_on ψ s c σ u v h pp r Set.univ
    (fun q : ℝ × ℝ => ‖fderiv ℝ (par ψ) q‖) isClosed_univ (continuous_norm.comp hcontPar)
  obtain ⟨M2, hM2pos, hM2⟩ := exists_bound_max_on ψ s c σ u v h pp r Set.univ
    (fun q : ℝ × ℝ => ‖fderiv ℝ (slabFnPar ψ c u v) q‖) isClosed_univ
    (continuous_norm.comp hcontSlab)
  obtain ⟨m1, hm1pos, hm1⟩ := exists_pos_min_on ψ s c σ u v h pp r Set.univ
    (fun q : ℝ × ℝ => ‖fderiv ℝ (sweepHeight ψ ℓ) q‖) isClosed_univ
    (continuous_norm.comp hcontSweep) (fun q hq => norm_pos_iff.mpr (hLne q hq.2.1))
  obtain ⟨m2, hm2pos, hm2⟩ := exists_pos_min_on ψ s c σ u v h pp r
    {q : ℝ × ℝ | |slabFn c u v (par ψ q)| = h}
    (fun q : ℝ × ℝ => |det2 (fderiv ℝ (sweepHeight ψ ℓ) q) (fderiv ℝ (slabFnPar ψ c u v) q)|)
    (isClosed_eq (continuous_abs.comp (continuous_slabFnPar ψ c u v)) continuous_const)
    (continuous_abs.comp (hcontDet2 _ _ hcontSweep hcontSlab))
    (fun q hq => abs_pos.mpr (hdet2_slab q hq.2.1 hq.2.2))
  have hm3 : ∀ i : Fin 3, ∃ mi : ℝ, 0 < mi ∧
      ∀ q ∈ fundDomain ∩ (AnnulusRegion ψ s c σ u v h pp r ∩
        {q : ℝ × ℝ | |par ψ q (σ i) - c (σ i)| = Submission.boxSide i * s}),
      mi ≤ (1 / Submission.boxSide i) *
        |det2 (fderiv ℝ (sweepHeight ψ ℓ) q)
          (fderiv ℝ (fun q' : ℝ × ℝ => par ψ q' (σ i)) q)| := by
    intro i
    refine exists_pos_min_on ψ s c σ u v h pp r
      {q : ℝ × ℝ | |par ψ q (σ i) - c (σ i)| = Submission.boxSide i * s}
      (fun q : ℝ × ℝ => (1 / Submission.boxSide i) *
        |det2 (fderiv ℝ (sweepHeight ψ ℓ) q)
          (fderiv ℝ (fun q' : ℝ × ℝ => par ψ q' (σ i)) q)|) ?_ ?_ ?_
    · exact isClosed_eq
        (continuous_abs.comp (((contDiff_coordPar ψ σ i).continuous).sub continuous_const))
        continuous_const
    · exact (continuous_const.mul (continuous_abs.comp
        (hcontDet2 _ _ hcontSweep (hcontCoord i))))
    · intro q hq
      obtain ⟨hqA, hqc⟩ := hq.2
      have hbox := (mem_AnnulusRegion.mp hqA).2.2.1
      have hbs : Submission.boxNorm c σ (par ψ q) = s := by
        refine le_antisymm (boxNorm_le_of_mem_closure c σ s _ hbox) ?_
        have h1 := div_le_boxNorm c σ (par ψ q) i
        rw [hqc, mul_div_cancel_left₀ _ (ne_of_gt (Submission.boxSide_pos i))] at h1
        exact h1
      have hD := (hBoxDiff q hqA hbs).1
      refine mul_pos (div_pos one_pos (Submission.boxSide_pos i)) (abs_pos.mpr ?_)
      intro hz
      have hid := abs_det2_fderiv_boxNorm_comp_param
        (L := fderiv ℝ (sweepHeight ψ ℓ) q) hbs hqc hD
      rw [hz, abs_zero, mul_zero] at hid
      exact hdet2_box q hqA hbs (abs_eq_zero.mp hid)
  obtain ⟨m30, hm30pos, hm30⟩ := hm3 0
  obtain ⟨m31, hm31pos, hm31⟩ := hm3 1
  obtain ⟨m32, hm32pos, hm32⟩ := hm3 2
  refine ⟨min (min m1 m2) (min (min m30 m31) m32), ?_, max M1 M2 + 2, ?_, ?_⟩
  · exact lt_min (lt_min hm1pos hm2pos) (lt_min (lt_min hm30pos hm31pos) hm32pos)
  · have h := lt_of_lt_of_le hM1pos (le_max_left M1 M2)
    linarith
  · intro q' h1 h2 h3 h4
    have hq'S : q' ∈ AnnulusRegion ψ s c σ u v h pp r := mem_AnnulusRegion.mpr ⟨h1, h2, h3, h4⟩
    obtain ⟨q₀, hq₀fund, hq'eq⟩ := exists_fundDomain_add q'
    have hpar_eq : par ψ q' = par ψ q₀ := by
      rw [hq'eq, Prod.add_def, param_add_int_mul_two_pi]
    have hq₀S : q₀ ∈ AnnulusRegion ψ s c σ u v h pp r := by
      rw [mem_AnnulusRegion] at hq'S ⊢
      exact ⟨by rw [← hpar_eq]; exact hq'S.1, by rw [← hpar_eq]; exact hq'S.2.1,
        by rw [← hpar_eq]; exact hq'S.2.2.1, by rw [← hpar_eq]; exact hq'S.2.2.2⟩
    have hq₀K : q₀ ∈ fundDomain ∩ (AnnulusRegion ψ s c σ u v h pp r ∩ Set.univ) :=
      ⟨hq₀fund, hq₀S, trivial⟩
    have hpar_bound : ‖fderiv ℝ (par ψ) q'‖ ≤ M1 := by
      have h := hM1 q₀ hq₀K
      rwa [← fderiv_param_eq_of_add_period _ _ hq'eq] at h
    have hslab_bound : ‖fderiv ℝ (slabFnPar ψ c u v) q'‖ ≤ M2 := by
      have h := hM2 q₀ hq₀K
      rwa [← fderiv_slabFnPar_eq_of_add_period _ _ hq'eq] at h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have h := le_max_left M1 M2
      linarith
    · have h := le_max_right M1 M2
      linarith
    · have h := hm1 q₀ hq₀K
      rw [fderiv_sweepHeight_eq_of_add_period _ _ hq'eq]
      refine le_trans (le_trans (min_le_left _ _) (min_le_left m1 m2)) h
    · intro hsh
      have hq₀T : q₀ ∈ fundDomain ∩ (AnnulusRegion ψ s c σ u v h pp r ∩
          {q : ℝ × ℝ | |slabFn c u v (par ψ q)| = h}) :=
        ⟨hq₀fund, hq₀S, by show |slabFn c u v (par ψ q₀)| = h; rw [← hpar_eq]; exact hsh⟩
      have h := hm2 q₀ hq₀T
      rw [fderiv_sweepHeight_eq_of_add_period _ _ hq'eq,
        fderiv_slabFnPar_eq_of_add_period _ _ hq'eq]
      refine le_trans (le_trans (min_le_left _ _) (min_le_right m1 m2)) h
    · intro hbs
      obtain ⟨i, hi⟩ := exists_boxSide_mul_eq_of_boxNorm_eq c σ s (par ψ q') hbs
      have hD' : fderiv ℝ (fun q' : ℝ × ℝ => Submission.boxNorm c σ (par ψ q')) q' ≠ 0 :=
        (hBoxDiff q' hq'S hbs).1
      have hDbox : ‖fderiv ℝ (fun q' : ℝ × ℝ => Submission.boxNorm c σ (par ψ q')) q'‖ ≤
          ‖fderiv ℝ (par ψ) q'‖ + 1 := norm_fderiv_boxNorm_comp_param_le ψ c σ q'
      have hcoord_eq : (fun q' : ℝ × ℝ => par ψ q' (σ i)) = fun q' : ℝ × ℝ => par ψ q' (σ i) := rfl
      constructor
      · have hmax : M1 ≤ max M1 M2 := le_max_left M1 M2
        linarith
      · have hqc₀ : |par ψ q₀ (σ i) - c (σ i)| = Submission.boxSide i * s := by
          rw [← hpar_eq]; exact hi
        fin_cases i
        · have hq₀T : q₀ ∈ fundDomain ∩ (AnnulusRegion ψ s c σ u v h pp r ∩
              {q : ℝ × ℝ | |par ψ q (σ 0) - c (σ 0)| = Submission.boxSide 0 * s}) :=
            ⟨hq₀fund, hq₀S, hqc₀⟩
          have h := hm30 q₀ hq₀T
          rw [abs_det2_fderiv_boxNorm_comp_param (L := fderiv ℝ (sweepHeight ψ ℓ) q') hbs hi hD',
            fderiv_sweepHeight_eq_of_add_period _ _ hq'eq,
            fderiv_coordPar_eq_of_add_period _ _ hq'eq]
          refine le_trans (le_trans (min_le_right _ _)
            (le_trans (min_le_left _ _) (min_le_left m30 m31))) h
        · have hq₀T : q₀ ∈ fundDomain ∩ (AnnulusRegion ψ s c σ u v h pp r ∩
              {q : ℝ × ℝ | |par ψ q (σ 1) - c (σ 1)| = Submission.boxSide 1 * s}) :=
            ⟨hq₀fund, hq₀S, hqc₀⟩
          have h := hm31 q₀ hq₀T
          rw [abs_det2_fderiv_boxNorm_comp_param (L := fderiv ℝ (sweepHeight ψ ℓ) q') hbs hi hD',
            fderiv_sweepHeight_eq_of_add_period _ _ hq'eq,
            fderiv_coordPar_eq_of_add_period _ _ hq'eq]
          refine le_trans (le_trans (min_le_right _ _)
            (le_trans (min_le_left _ _) (min_le_right m30 m31))) h
        · have hq₀T : q₀ ∈ fundDomain ∩ (AnnulusRegion ψ s c σ u v h pp r ∩
              {q : ℝ × ℝ | |par ψ q (σ 2) - c (σ 2)| = Submission.boxSide 2 * s}) :=
            ⟨hq₀fund, hq₀S, hqc₀⟩
          have h := hm32 q₀ hq₀T
          rw [abs_det2_fderiv_boxNorm_comp_param (L := fderiv ℝ (sweepHeight ψ ℓ) q') hbs hi hD',
            fderiv_sweepHeight_eq_of_add_period _ _ hq'eq,
            fderiv_coordPar_eq_of_add_period _ _ hq'eq]
          refine le_trans (le_trans (min_le_right _ _)
            (min_le_right (min m30 m31) m32)) h

end

end Work.Drive.Final
