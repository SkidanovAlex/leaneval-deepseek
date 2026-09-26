import Mathlib
import Submission.Work.Drive.Final.crux_core_wd
import Submission.Work.Drive.Final.sweep_strip
import Submission.Work.Drive.EpsFormSphere.OpenTiltedRegion
import Submission.Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized

/-!
# The tilted sweep without `hreg` and `hjump`: `TiltedSweepMono` and its infimum assembly

The residual `Work.Drive.Final.TiltedSweepExists'` (`sweep_half.lean`) carries the three span
fields of Pardon's sweep (`hreg`, `hjump`, `hone`).  Two of them are **false as stated** with only
the geometric data, as the workspace's machine-checked counterexamples show:

* `hreg` (the span is constant between exceptional levels) fails when the slab swallows the box
  (`Drive/EpsForm/windingSpan_sweepRegion_eq_of_regular_REFUTED2.lean`);
* `hjump` (the `H₁`-rank jumps by at most `1` across an exceptional level) fails for the standard
  torus when the sweep height has *two* nondegenerate critical points at the same level (the
  uniqueness clause of the genericity input is missing).

This file replaces them by two fields which are the *honest* content of Pardon's dichotomy and of
his `2`-surgery count, and proves that they suffice — by an infimum argument which needs **no**
regularity of the sweep along the levels:

* **(D)** at every level outside the finite exceptional set the span is `⊥` or `⊤` (Pardon's
  dichotomy, which the count at every level supplies);
* **(L)** no level at which the span is `⊥` is reached by a drop from `⊤`: just below such a level
  the span is not `⊤`.

The assembly (`windingSpan_end_ne_bot_of_fields`) is: let `S` be the set of levels with span `⊥`
and `λ* = sInf S`; `S` is upward closed, and any essential loop of `X λ*` lies in some `X ν`
(`ν > λ*`) because the loop is compact and the family is nested, so `λ* ∈ S`; (L) at `λ*` gives a
level `μ < λ*` with span `≠ ⊤`, and (D) at a non-exceptional such `μ` makes the span `⊥`,
contradicting the infimum.  Hence the span at the end of the sweep is not `⊥`, which is exactly what
the endpoint argument (`exists_openHalf_of_essentialLoop_sdiff`) turns into Pardon's conclusion.

All the topological and order-theoretic bricks here are proved; `TiltedSweepMono` itself is the
team's residual (Pardon's pinch, in the form in which its fields are true).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.Drive.Final

noncomputable section

variable {P : Work.CoreTopology.ParamTorus} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
  {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ}

/-- The region of the tilted sweep at the level `lam` (an abbreviation for readability). -/
abbrev sweep (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam

/-- **The region at a level is the union of the regions just above it.** -/
theorem openTiltedSweepRegion_eq_iUnion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) :
    sweep P s c σ u v h ℓ lam =
      ⋃ ν ∈ Set.Ioi lam, sweep P s c σ u v h ℓ ν := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_Ioi, exists_prop, mem_openTiltedSweepRegion']
  constructor
  · rintro ⟨hyc, hyb, hrem⟩
    by_cases hslab : |inner ℝ v y - (inner ℝ v c + u)| ≤ h
    · have hlt : lam < ℓ y := by
        by_contra hcon
        exact hrem ⟨hslab, le_of_not_gt hcon⟩
      refine ⟨(lam + ℓ y) / 2, by linarith, hyc, hyb, fun hz => ?_⟩
      exact absurd hz.2 (not_le.mpr (by linarith))
    · exact ⟨lam + 1, by linarith, hyc, hyb, fun hz => hslab hz.1⟩
  · rintro ⟨ν, hν, hyc, hyb, hrem⟩
    exact ⟨hyc, hyb, fun hz => hrem ⟨hz.1, le_trans hz.2 (le_of_lt hν)⟩⟩

/-- **The regions decrease with the level.** -/
theorem sweep_anti {μ ν : ℝ} (hμν : μ ≤ ν) :
    sweep P s c σ u v h ℓ ν ⊆ sweep P s c σ u v h ℓ μ := by
  intro y hy
  rw [mem_openTiltedSweepRegion'] at hy ⊢
  exact ⟨hy.1, hy.2.1, fun hz => hy.2.2 ⟨hz.1, le_trans hz.2 hμν⟩⟩

/-- **The genericity of the tilt for the surface** — the four clauses of
`Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized` (which is *proved*), packaged so that the
span fields of the sweep can be stated at data satisfying them:

* (i) at every level `lam ∉ exc`, the sweep height `sweepHeight ψ ℓ` has non-vanishing derivative at
  every point of `PBox s c σ ∩ tiltedSlabClosed` of height `lam` (every level outside `exc` is a
  regular value of the height on the slab in the box);
* (ii) at every such level, on the slab *faces* the derivative of the height is not parallel to the
  derivative of the face functional (the wall crosses the faces transversally);
* (iii) every critical point of the height inside the box and the slab is non-degenerate in the
  parameter plane and its value lies in `exc`;
* (iv) two critical points inside the box and the slab with the same value coincide (one handle per
  level). -/
def TiltedGenericity (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) : Prop :=
  (∀ lam : ℝ, lam ∉ (exc : Set ℝ) → ∀ p : ℝ × ℝ,
      Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p ∈
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0) ∧
  (∀ lam : ℝ, lam ∉ (exc : Set ℝ) → ∀ p : ℝ × ℝ,
      Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p) ∧
  (∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p ∈
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p = 0 →
      Function.Injective (fderiv ℝ (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ)) p) ∧
        ℓ (Work.BoxShrink.Pinch.par ψ p) ∈ exc) ∧
  (∀ p p' : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p' ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p ∈
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
      Work.BoxShrink.Pinch.par ψ p' ∈
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p = 0 →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p' = 0 →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = ℓ (Work.BoxShrink.Pinch.par ψ p') →
      Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p')

/-- **The trace of a level of the tilted sweep**: the part on the surface of the frontier of the
level region `PBox s c σ \ (tiltedSlabClosed a v h ∩ {ℓ ≤ lam})`, `a = ⟪v,c⟫ + u`.  It is the set
whose lift to the parameter plane must have compact components for the *general* dichotomy
(`Work.EpsW.windingSpan_bot_or_top_of_closed_of_components_compact`) to give field (D). -/
def tiltedLevelTrace (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  P.carrier ∩ frontier (Submission.PBox s c σ \
    (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y ≤ lam}))

/-- **The data of the tilted sweep exist, with the genericity of the surface, the size condition and
the window conditions.**  Every ingredient is either the proved
`Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized` (with parameter `1`, so that
`‖v − e_{σ 2}‖ ≤ 1` and `1 · R < h`, hence `‖v − e_{σ 2}‖ · R < h`) or elementary bookkeeping
(the box is non-empty, `ℓ` is bounded on it by `|ℓ c| + ‖ℓ‖ · R`, and the finite set `exc` is bounded
by `1 + ∑_{t ∈ exc} |t|`). -/
theorem tiltedGenericity_data_exists {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (hs : 0 < s) :
    ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ),
      TiltedGenericity ψ s c σ u v h ℓ exc ∧ ‖v‖ = 1 ∧
        ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h ∧ 0 < h ∧
        (∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R) ∧
        (∃ lam0 lam1 : ℝ, (∀ y ∈ Submission.PBox s c σ, lam0 < ℓ y) ∧
          (∀ y ∈ Submission.PBox s c σ, ℓ y < lam1) ∧ lam0 < lam1 ∧
          (∀ t ∈ exc, lam0 < t ∧ t < lam1)) := by
  obtain ⟨v, h, ℓ, exc, R, hv1, hve, _hv0, _hℓ0, hRbox, hεR, c1, c2, c3, c4⟩ :=
    Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized ψ s c σ u 1 (by norm_num)
  have hc : c ∈ Submission.PBox s c σ := by
    rw [Submission.mem_PBox]
    intro i
    rw [sub_self, abs_zero]
    exact mul_pos (Submission.boxSide_pos i) hs
  have hR0 : 0 ≤ R := by simpa using hRbox c hc
  have hεR' : R < h := by simpa using hεR
  have hh : 0 < h := lt_of_le_of_lt hR0 hεR'
  have hsize : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h := by
    have h1 : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R ≤ 1 * R :=
      mul_le_mul_of_nonneg_right hve hR0
    rw [one_mul] at h1
    linarith
  -- bounds on `ℓ` over the box and on the elements of `exc`
  set q : ℝ := |ℓ c| + ‖ℓ‖ * R + 1 with hq
  have hq1 : 1 ≤ q := by rw [hq]; nlinarith [abs_nonneg (ℓ c), norm_nonneg ℓ, hR0]
  have hℓy : ∀ y ∈ Submission.PBox s c σ, |ℓ y| ≤ q - 1 := by
    intro y hy
    have h1 : ‖y - c‖ ≤ R := hRbox y hy
    have h2 : ℓ y - ℓ c = ℓ (y - c) := by rw [map_sub]
    have h3 : |ℓ (y - c)| ≤ ‖ℓ‖ * ‖y - c‖ := by
      have := ContinuousLinearMap.le_opNorm ℓ (y - c)
      rwa [Real.norm_eq_abs] at this
    have h4 : |ℓ y| ≤ |ℓ y - ℓ c| + |ℓ c| := by
      have h5 : ℓ y = (ℓ y - ℓ c) + ℓ c := by ring
      calc |ℓ y| = |(ℓ y - ℓ c) + ℓ c| := congrArg (fun t : ℝ => |t|) h5
        _ ≤ |ℓ y - ℓ c| + |ℓ c| := abs_add_le _ _
    rw [h2] at h4
    have h6 : ‖ℓ‖ * ‖y - c‖ ≤ ‖ℓ‖ * R := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    have : |ℓ y| ≤ ‖ℓ‖ * R + |ℓ c| := by linarith
    rw [hq]; linarith
  set m : ℝ := 1 + ∑ t ∈ exc, |t| with hm
  have hm1 : 1 ≤ m := by rw [hm]; linarith [Finset.sum_nonneg (fun t (_ : t ∈ exc) => abs_nonneg t)]
  have hexc : ∀ t ∈ exc, |t| ≤ m - 1 := by
    intro t ht
    have h1 : |t| ≤ ∑ t' ∈ exc, |t'| :=
      Finset.single_le_sum (fun t' (_ : t' ∈ exc) => abs_nonneg t') ht
    rw [hm]; linarith
  refine ⟨v, h, R, ℓ, exc, ⟨c1, c2, c3, c4⟩, hv1, hsize, hh, hRbox, -(q + m), q + m, ?_, ?_, ?_,
    ?_⟩
  · intro y hy
    have h1 := hℓy y hy
    have h2 : -|ℓ y| ≤ ℓ y := neg_abs_le _
    have h3 : -(q - 1) ≤ -|ℓ y| := neg_le_neg h1
    linarith
  · intro y hy
    have h1 := hℓy y hy
    have h2 : ℓ y ≤ |ℓ y| := le_abs_self _
    linarith
  · linarith
  · intro t ht
    have h1 := hexc t ht
    have h2 := neg_abs_le t
    have h3 := le_abs_self t
    constructor <;> linarith

/-- **A closed curve inside the union of a nested family of carrier-open regions lies in one
member.**  The curve's image is compact (the image of `[0, 2π]`), and the family is nested, so the
finite subcover furnished by compactness — read in the surface — collapses to a single member. -/
theorem exists_mem_of_curve_subset_iUnion {Z : ℝ → Set R3}
    (hZopen : ∀ ν : ℝ, Work.SurgeryInvariance.IsOpenInCarrier P (Z ν))
    (hZanti : ∀ ⦃μ ν : ℝ⦄, μ ≤ ν → Z ν ⊆ Z μ)
    (γ : Work.CoreTopology.ClosedCurve P) {lam : ℝ}
    (hγ : ∀ t : ℝ, γ t ∈ ⋃ ν ∈ Set.Ioi lam, Z ν) :
    ∃ ν : ℝ, lam < ν ∧ ∀ t : ℝ, γ t ∈ Z ν := by
  classical
  set g : ℝ → P.carrier := fun t => ⟨γ t, γ.mem t⟩ with hg
  have hgc : Continuous g := γ.cont.subtype_mk γ.mem
  have hgper : Function.Periodic g (2 * Real.pi) := fun t => by
    apply Subtype.ext
    simp only [hg, γ.periodic t]
  have hK : IsCompact (Set.range g) := by
    rw [← hgper.image_Icc (by positivity : (0 : ℝ) < 2 * Real.pi) 0]
    exact isCompact_Icc.image hgc
  have hcover : Set.range g ⊆
      ⋃ i : {ν : ℝ // lam < ν}, (Subtype.val ⁻¹' Z i.1 : Set P.carrier) := by
    rintro z ⟨t, rfl⟩
    obtain ⟨ν, hνmem⟩ := Set.mem_iUnion.mp (hγ t)
    obtain ⟨hν, hmem⟩ := Set.mem_iUnion.mp hνmem
    exact Set.mem_iUnion.mpr ⟨⟨ν, hν⟩, hmem⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun i : {ν : ℝ // lam < ν} => (Subtype.val ⁻¹' Z i.1 : Set P.carrier))
    (fun i => hZopen i.1) hcover
  have hne : t.Nonempty := by
    rcases t.eq_empty_or_nonempty with hem | h
    · exfalso
      have h0 := ht (Set.mem_range_self (0 : ℝ))
      rw [hem] at h0
      simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty] at h0
      exact h0
    · exact h
  refine ⟨(t.min' hne).1, (t.min' hne).2, fun t' => ?_⟩
  have hmem := ht (Set.mem_range_self t')
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨i, hi, hzi⟩ := hmem
  exact hZanti (Finset.min'_le t i hi) hzi

/-- **The span of the sweep at a level is the span of the union of the regions just above it, so a
level whose spans just above are all `⊥` is itself `⊥`.** -/
theorem windingSpan_eq_bot_of_forall_gt (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) {lam : ℝ}
    (hbot : ∀ ν : ℝ, lam < ν →
      Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ ν) = ⊥) :
    Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lam) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  intro hess
  obtain ⟨γ, hessγ, hγ⟩ := hess
  have hγ' : ∀ t : ℝ, γ t ∈
      ⋃ ν ∈ Set.Ioi lam, sweep P s c σ u v h ℓ ν := by
    intro t
    rw [← openTiltedSweepRegion_eq_iUnion P s c σ u v h ℓ lam]
    exact hγ t
  obtain ⟨ν, hν, hmem⟩ := exists_mem_of_curve_subset_iUnion
    (Z := sweep P s c σ u v h ℓ)
    (fun ν => Work.Drive.EpsFormSphere.isOpenInCarrier_openTiltedSweepRegion)
    (fun _ _ hμν => sweep_anti hμν) γ hγ'
  have hνbot := hbot ν hν
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff] at hνbot
  exact hνbot ⟨γ, hessγ, hmem⟩

/-- **The infimum assembly.**  If the span of the sweep is `⊤` at the start of the window, is `⊥`
or `⊤` at every non-exceptional level (`D`), and no level with span `⊥` is reached by a drop from
`⊤` (`L`), then the span at the end of the window is not `⊥`. -/
theorem windingSpan_end_ne_bot_of_fields (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) {lam0 lam1 : ℝ}
    {exc : Finset ℝ}
    (hstart : Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lam0) = ⊤)
    (hdich : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lam) = ⊥ ∨
        Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lam) = ⊤)
    (hnodrop : ∀ lam ∈ Set.Icc lam0 lam1,
      Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lam) = ⊥ →
        ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
          Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ mu) ≠ ⊤) :
    Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lam1) ≠ ⊥ := by
  intro hbot
  set S : Set ℝ := {lam : ℝ | Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lam)
    = ⊥} with hSdef
  have hmem_iff : ∀ lam : ℝ, lam ∈ S ↔
      Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lam) = ⊥ := by
    intro lam
    rw [hSdef]
    exact Iff.rfl
  have hSne : S.Nonempty := ⟨lam1, (hmem_iff lam1).mpr hbot⟩
  -- `lam0` is a lower bound of `S`
  have hlower : ∀ lam ∈ S, lam0 ≤ lam := by
    intro lam hlam
    by_contra hcon
    push Not at hcon
    have hle : Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lam0) ≤
        Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lam) :=
      Work.SurgeryInvariance.WindingSpan_mono P (sweep_anti (le_of_lt hcon))
    rw [hstart, (hmem_iff lam).mp hlam] at hle
    exact top_ne_bot (le_bot_iff.mp hle)
  -- `S` is upward closed
  have hup : ∀ ⦃mu nu : ℝ⦄, mu ∈ S → mu ≤ nu → nu ∈ S := by
    intro mu nu hmu hmunu
    refine (hmem_iff nu).mpr ?_
    have hle := Work.SurgeryInvariance.WindingSpan_mono (P := P)
      (X := sweep P s c σ u v h ℓ nu) (Y := sweep P s c σ u v h ℓ mu) (sweep_anti hmunu)
    rw [(hmem_iff mu).mp hmu] at hle
    exact le_bot_iff.mp hle
  set lamS : ℝ := sInf S with hlamSdef
  -- `lamS ∈ S`: an essential loop of the level region lies in one of the regions above it
  have hmemS : lamS ∈ S := by
    refine (hmem_iff lamS).mpr ?_
    rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
    intro hess
    obtain ⟨γ, hessγ, hγ⟩ := hess
    have hγ' : ∀ t : ℝ, γ t ∈ ⋃ ν ∈ Set.Ioi lamS, sweep P s c σ u v h ℓ ν := by
      intro t
      rw [← openTiltedSweepRegion_eq_iUnion P s c σ u v h ℓ lamS]
      exact hγ t
    obtain ⟨ν, hν, hmem⟩ := exists_mem_of_curve_subset_iUnion
      (Z := sweep P s c σ u v h ℓ)
      (fun ν => Work.Drive.EpsFormSphere.isOpenInCarrier_openTiltedSweepRegion)
      (fun _ _ hμν => sweep_anti hμν) γ hγ'
    have hνS : ν ∈ S := by
      have hex : ∃ lam ∈ S, lam < ν := by
        by_contra hcon
        push Not at hcon
        have hb : ∀ b ∈ S, ν ≤ b := fun b hb => hcon b hb
        have := le_csInf hSne hb
        rw [← hlamSdef] at this
        exact absurd this (not_le.mpr hν)
      obtain ⟨lam, hlam, hlt⟩ := hex
      exact hup hlam (le_of_lt hlt)
    have hνnot := (Work.SurgeryInvariance.WindingSpan_eq_bot_iff P
      (sweep P s c σ u v h ℓ ν)).mp ((hmem_iff ν).mp hνS)
    exact hνnot ⟨γ, hessγ, hmem⟩
  have hmemS' : Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lamS) = ⊥ :=
    (hmem_iff lamS).mp hmemS
  -- the window
  have hle_lam1 : lamS ≤ lam1 := csInf_le ⟨lam0, hlower⟩ ((hmem_iff lam1).mpr hbot)
  have hge_lam0 : lam0 ≤ lamS := hlower lamS hmemS
  have hgt_lam0 : lam0 < lamS := by
    rcases lt_or_eq_of_le hge_lam0 with hlt | heq
    · exact hlt
    · exfalso
      have h2 : Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lam0) = ⊥ :=
        (hmem_iff lam0).mp (heq ▸ hmemS)
      rw [hstart] at h2
      exact top_ne_bot h2
  -- (L) at `lamS`
  obtain ⟨mu0, hmu0, hno⟩ := hnodrop lamS ⟨hge_lam0, hle_lam1⟩ hmemS'
  -- a non-exceptional level in `[max mu0 lam0, lamS)`
  obtain ⟨mu, hmu_ge, hmu_lt, hmu_ne⟩ :
      ∃ mu : ℝ, max mu0 lam0 ≤ mu ∧ mu < lamS ∧ mu ∉ (exc : Set ℝ) := by
    have hmax_lt : max mu0 lam0 < lamS := max_lt hmu0 hgt_lam0
    obtain ⟨mu, hmu, hne⟩ := (Set.Ico_infinite hmax_lt).exists_notMem_finite exc.finite_toSet
    exact ⟨mu, hmu.1, hmu.2, hne⟩
  have hmu_icc : mu ∈ Set.Icc lam0 lam1 :=
    ⟨le_trans (le_max_right _ _) hmu_ge, le_of_lt (lt_of_lt_of_le hmu_lt hle_lam1)⟩
  have hmu_ico : mu ∈ Set.Ico mu0 lamS := ⟨le_trans (le_max_left _ _) hmu_ge, hmu_lt⟩
  rcases hdich mu hmu_icc hmu_ne with hbotmu | htopmu
  · -- `mu ∈ S`, contradicting the infimum
    have h2 : lamS ≤ mu := csInf_le ⟨lam0, hlower⟩ ((hmem_iff mu).mpr hbotmu)
    linarith
  · exact hno mu hmu_ico htopmu


/-- **A point of the end region of the tilted sweep lies strictly above or below the cutting
plane.**  This is the tilt estimate: a point outside the closed slab satisfies
`h < |⟪v, y - c⟫ - u|`, while the coordinate `y (σ 2)` differs from `⟪v, y - c⟫` by at most
`‖v - shiftVσ σ 1‖ · ‖y - c‖ ≤ ‖v - shiftVσ σ 1‖ · R < h`. -/
theorem mem_upperHalf_or_lowerHalf_of_mem_sdiff_tiltedSlabClosed
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h R : ℝ) (hvtilt : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h)
    (hR : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R) {y : R3}
    (hy : y ∈ Work.BoxShrink.Core.boxRegion P s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) :
    y ∈ Work.BoxShrink.Core.upperHalf c σ u ∨
      y ∈ Work.BoxShrink.Core.lowerHalf c σ u := by
  obtain ⟨⟨hyc, hyb⟩, hyslab⟩ := hy
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with he
  have hbig : h < |inner ℝ v (y - c) - u| := by
    have h1 : ¬ |inner ℝ v y - (inner ℝ v c + u)| ≤ h := hyslab
    have h2 : inner ℝ v y - (inner ℝ v c + u) = inner ℝ v (y - c) - u := by
      rw [inner_sub_right]; ring
    rw [h2] at h1
    exact not_le.mp h1
  have hcoord : inner ℝ e (y - c) = y (σ 2) - c (σ 2) := by
    rw [he, Work.BoxShrink.shiftVσ]
    simp [PiLp.inner_apply, Real.inner_apply]
  have hsplit : inner ℝ v (y - c) - u =
      (y (σ 2) - c (σ 2) - u) + inner ℝ (v - e) (y - c) := by
    rw [inner_sub_left, hcoord]; ring
  have hCS : |inner ℝ (v - e) (y - c)| ≤ ‖v - e‖ * ‖y - c‖ := abs_real_inner_le_norm _ _
  have hyR : ‖y - c‖ ≤ R := hR y hyb
  have hmono : ‖v - e‖ * ‖y - c‖ ≤ ‖v - e‖ * R :=
    mul_le_mul_of_nonneg_left hyR (norm_nonneg _)
  rcases lt_abs.mp hbig with hgt | hlt
  · refine Or.inl ?_
    show c (σ 2) + u < y (σ 2)
    have hup' : inner ℝ (v - e) (y - c) ≤ ‖v - e‖ * R := by
      have h1 : inner ℝ (v - e) (y - c) ≤ |inner ℝ (v - e) (y - c)| := le_abs_self _
      linarith
    have hkey : y (σ 2) - c (σ 2) - u =
        (inner ℝ v (y - c) - u) - inner ℝ (v - e) (y - c) := by linarith [hsplit]
    have hpos : 0 < (inner ℝ v (y - c) - u) - inner ℝ (v - e) (y - c) := by
      linarith [hvtilt]
    have : 0 < y (σ 2) - c (σ 2) - u := hkey.symm ▸ hpos
    linarith
  · refine Or.inr ?_
    show y (σ 2) < c (σ 2) + u
    have hlow' : -(‖v - e‖ * R) ≤ inner ℝ (v - e) (y - c) := by
      have h1 : -|inner ℝ (v - e) (y - c)| ≤ inner ℝ (v - e) (y - c) := neg_abs_le _
      linarith
    have hkey : y (σ 2) - c (σ 2) - u =
        (inner ℝ v (y - c) - u) - inner ℝ (v - e) (y - c) := by linarith [hsplit]
    have hneg : (inner ℝ v (y - c) - u) - inner ℝ (v - e) (y - c) < 0 := by
      linarith [hvtilt]
    have : y (σ 2) - c (σ 2) - u < 0 := hkey.symm ▸ hneg
    linarith

/-- **The endpoint of the tilted sweep.**  An essential loop of the surface in the end region
`boxRegion ∖ tiltedSlabClosed` — i.e. off the *closed* tilted slab, the region to which the sweep
shrinks — lies entirely in one of the two *open* halves of the box cut by the cutting plane.  This is
Pardon's exact half-box conclusion, with no `ε`. -/
theorem exists_openHalf_of_essentialLoop_sdiff_tiltedSlabClosed
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h R : ℝ) (hvtilt : ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h)
    (hR : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R)
    {γ : Work.CoreTopology.ClosedCurve P} (hess : Work.CoreTopology.IsEssential P γ)
    (hγ : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) :
    (∃ γ' : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ' ∧
        ∀ t : ℝ, γ' t ∈ Submission.PBox s c σ ∧ γ' t (σ 2) < c (σ 2) + u) ∨
      (∃ γ' : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ' ∧
        ∀ t : ℝ, γ' t ∈ Submission.PBox s c σ ∧ c (σ 2) + u < γ' t (σ 2)) := by
  have hU : IsOpen (Work.BoxShrink.Core.upperHalf c σ u) := by
    rw [Work.BoxShrink.Core.upperHalf]
    exact isOpen_lt continuous_const (by fun_prop)
  have hV : IsOpen (Work.BoxShrink.Core.lowerHalf c σ u) := by
    rw [Work.BoxShrink.Core.lowerHalf]
    exact isOpen_lt (by fun_prop) continuous_const
  have hdisj : Disjoint (Work.BoxShrink.Core.upperHalf c σ u)
      (Work.BoxShrink.Core.lowerHalf c σ u) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    have hy1 : c (σ 2) + u < y (σ 2) := hy
    have hy2 : y (σ 2) < c (σ 2) + u := hy'
    exact absurd (lt_trans hy1 hy2) (lt_irrefl _)
  have hcover : Set.range γ.γ ⊆ Work.BoxShrink.Core.upperHalf c σ u ∪
      Work.BoxShrink.Core.lowerHalf c σ u := by
    rintro y ⟨t, rfl⟩
    exact mem_upperHalf_or_lowerHalf_of_mem_sdiff_tiltedSlabClosed P s c σ u v h R hvtilt hR
      (hγ t)
  have hpre : IsPreconnected (Set.range γ.γ) := isPreconnected_range γ.cont
  have hmem : ∀ t : ℝ, γ t ∈ Submission.PBox s c σ := by
    intro t
    have h := hγ t
    rw [Work.BoxShrink.Core.boxRegion, Set.mem_sdiff, Set.mem_inter_iff] at h
    exact h.1.2
  rcases IsPreconnected.subset_or_subset hU hV hdisj hcover hpre with hcase | hcase
  · exact Or.inr ⟨γ, hess, fun t => ⟨hmem t, hcase ⟨t, rfl⟩⟩⟩
  · exact Or.inl ⟨γ, hess, fun t => ⟨hmem t, hcase ⟨t, rfl⟩⟩⟩

/-- **The tilted sweep in the form in which its fields are true** (`TiltedSweepMono`).

At every counted crux configuration there are a unit direction `v`, a half-width `h > 0`, a radius
`R` bounding the box, a wall functional `ℓ`, end levels `lam0 < lam1` and a finite exceptional set
`exc` such that

* the *corrected* size condition `‖v − e_{σ 2}‖ · R < h` of Pardon's tilt holds;
* `lam0` is below and `lam1` above the `ℓ`-range of the box (so the sweep starts at the box region
  and ends at `boxRegion ∖ tiltedSlabClosed`);
* **(D)** at every level outside `exc` the span of the swept region is `⊥` or `⊤` (Pardon's
  dichotomy, supplied by the count at every level);
* **(L)** no level with span `⊥` is reached by a drop from `⊤`: just below such a level the span is
  not `⊤`.

Fields (D) and (L) replace the `hreg`/`hjump`/`hone` of `TiltedSweepExists'`, which are *false* as
stated (see the module doc): (D) is Pardon's dichotomy at every level, and (L) is the part of his
`rank`-jump bound which is needed by the infimum assembly
(`windingSpan_end_ne_bot_of_fields`).  In particular (L) needs **no** hypothesis on the level being
non-exceptional, and is strictly stronger than the spelling with the extra hypothesis "some box
point lies above `λ`": that spelling leaves the assembly gap of a drop occurring at the top of the
`ℓ`-range (the region above being empty), which is exactly the case (L) has to cover. -/
def TiltedSweepMono : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
            ‖v‖ = 1 ∧ ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h ∧ 0 < h ∧
            (∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R) ∧
            (∀ y ∈ Submission.PBox s c σ, lam0 < ℓ y) ∧
            (∀ y ∈ Submission.PBox s c σ, ℓ y < lam1) ∧ lam0 < lam1 ∧
            (∀ t ∈ exc, lam0 < t ∧ t < lam1) ∧
            (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
              Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                  (sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥ ∨
                Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                  (sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊤) ∧
            (∀ lam ∈ Set.Icc lam0 lam1,
              Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                  (sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥ →
                ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
                  Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                    (sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) ≠ ⊤)

/-- **`TiltedSweepMono` gives Pardon's exact half-box conclusion** — hence, through the proved
`countingHalfEpsSphere_of_cruxCoreWd`, Pardon's `doublebubble2` in its ε-form, and then the
challenge. -/
theorem cruxCoreWd_of_tiltedSweepMono (h : TiltedSweepMono) : ∀ p q : ℕ, CruxCoreWd p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  set P := Work.Drive.EpsSphere.torusOf ψ with hP
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hvtilt, hh, hR, hlow, hhigh, hl, hexc, hdich,
    hnodrop⟩ :=
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  have hs0 : 0 < s := lt_trans hr hrs
  -- the box region has span `⊤`
  have hnoS : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.EpsW.sphereTrace_inessential_of_countsWd p q hp hq hc ψ K hd himg hsmall hs0 c σ hslice
      hcl hS
  have hne : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr
      (Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (le_of_lt hrs) hbox)
  have hstart : Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam0) = ⊤ := by
    rw [Work.Drive.EpsFormSphere.openTiltedSweepRegion_eq_boxRegion hlow]
    exact Work.Drive.EpsForm.windingSpan_boxRegion_eq_top_of_sphereTrace_inessential hs0 hslice
      hnoS hne
  have hfin : Work.SurgeryInvariance.WindingSpan P (sweep P s c σ u v h ℓ lam1) ≠ ⊥ :=
    windingSpan_end_ne_bot_of_fields P s c σ u v h ℓ hstart hdich hnodrop
  obtain ⟨γ, hess, hγ⟩ := (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hfin
  simp only [sweep] at hγ
  have hγ' : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ \
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
    intro t
    rw [Work.Drive.EpsFormSphere.openTiltedSweepRegion_eq_sdiff hhigh] at hγ
    exact hγ t
  exact exists_openHalf_of_essentialLoop_sdiff_tiltedSlabClosed P s c σ u v h R hvtilt hR hess hγ'

/-- **`TiltedSweepMono` gives Pardon's ε-form for the crux configurations.** -/
theorem countingHalfEpsSphere_of_tiltedSweepMono (h : TiltedSweepMono) :
    Work.Drive.EpsSphere.CountingHalfEpsSphere :=
  countingHalfEpsSphere_of_cruxCoreWd (cruxCoreWd_of_tiltedSweepMono h)

end

end Work.Drive.Final
