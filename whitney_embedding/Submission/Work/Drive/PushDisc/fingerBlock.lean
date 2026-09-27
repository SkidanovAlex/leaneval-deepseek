import Mathlib
import Submission.Work.Drive.PushDisc.milnorLens
import Submission.Work.Drive.PushDisc.asymChart
import Submission.Work.Drive.PushDisc.exists_chart_of_arc
import Submission.Work.Drive.PushDisc.lensThetaRows
import Submission.Work.Whitney.PushSigned

/-!
# The finger block of the second sheet

This file proves `Work.Drive.PushDisc.fingerBlock`: the parametrisation of the second sheet of the
Whitney move from the *finger row* `hfinger` (which pins `Φ ∘ f ∘ c₂.symm` on the open window
`asymReg k X'`) and the two pins.  The parametrisation is the plain one,

    σ₂ p = c₂.symm (splitE k (p.1, r • p.2)),      h p = (arch p.1, 0),

and the only non-trivial row is the last one (the frontier row): the coordinates of `Φ ∘ f` at a
frontier point of the finger's image must have `|x| = X''` or `‖v‖ = 1`.  The proof reads the
frontier point through the coordinates `g = ((Φ ∘ f)₁, (Φ ∘ f)_{2,2,2})`: `g` inverts `σ₂` on the
window, hence carries `frontier (σ₂ '' asymReg)` into `frontier (asymReg)`.  This is where
`[T2Space M]` is needed (the identity `σ₂ (g x) = x` is obtained from the closedness of the
diagonal); it is *not* implied by the locally Euclidean structure.
-/

namespace Work.Drive.PushDisc

open scoped ContDiff Manifold
open Set Metric

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

/-! ### Elementary facts about the window and the model maps -/

theorem contDiff_arch : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) arch := by
  rw [show arch = fun x : ℝ => 1 - x ^ 2 from rfl]
  fun_prop

theorem isOpen_asymReg (k : ℕ) (X : ℝ) : IsOpen (asymReg k X) := by
  have h1 : IsOpen {p : ℝ × EuclideanSpace ℝ (Fin k) | |p.1| < X} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have h2 : IsOpen {p : ℝ × EuclideanSpace ℝ (Fin k) | ‖p.2‖ < 1} :=
    isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
  exact h1.inter h2

theorem closure_asymReg_subset (k : ℕ) (X : ℝ) :
    closure (asymReg k X) ⊆ {p : ℝ × EuclideanSpace ℝ (Fin k) | |p.1| ≤ X ∧ ‖p.2‖ ≤ 1} := by
  refine closure_minimal (fun p hp => ⟨le_of_lt hp.1, le_of_lt hp.2⟩) ?_
  exact (isClosed_le (continuous_abs.comp continuous_fst) continuous_const).inter
    (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)

/-- Every point of the target of an open partial homeomorphism is the image of a point of its
source. -/
theorem symm_mem_source {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {y : Y} (hy : y ∈ e.target) : e.symm y ∈ e.source := by
  have h : e.symm y ∈ e.symm '' e.target := ⟨y, hy, rfl⟩
  rwa [e.symm_image_target_eq_source] at h

/-- The scaling of the second factor of `ℝ × E^k`, as a homeomorphism. -/
def scaleHomeo (k : ℕ) (r : ℝ) (hr : r ≠ 0) :
    (ℝ × EuclideanSpace ℝ (Fin k)) ≃ₜ (ℝ × EuclideanSpace ℝ (Fin k)) where
  toFun p := (p.1, r • p.2)
  invFun p := (p.1, r⁻¹ • p.2)
  left_inv p := by
    ext <;> simp [smul_smul, inv_mul_cancel₀ hr]
  right_inv p := by
    ext <;> simp [smul_smul, mul_inv_cancel₀ hr]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem isOpenMap_scale (k : ℕ) (r : ℝ) (hr : r ≠ 0) :
    IsOpenMap (fun p : ℝ × EuclideanSpace ℝ (Fin k) => (p.1, r • p.2)) :=
  (scaleHomeo k r hr).isOpenMap

/-- The model map `p ↦ splitE k (p.1, r • p.2)`. -/
def splitReg (k : ℕ) (r : ℝ) :
    (ℝ × EuclideanSpace ℝ (Fin k)) → EuclideanSpace ℝ (Fin (k + 1)) :=
  fun p => splitE k (p.1, r • p.2)

theorem continuous_splitReg (k : ℕ) (r : ℝ) : Continuous (splitReg k r) := by
  have h1 : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin k) => splitE k q) :=
    (Work.Drive.Whitney.splitEuclideanSpace k).choose.continuous
  have h2 : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin k) => (p.1, r • p.2)) := by
    fun_prop
  show Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin k) => splitE k (p.1, r • p.2))
  exact h1.comp h2

theorem isOpenMap_splitReg (k : ℕ) (r : ℝ) (hr : r ≠ 0) : IsOpenMap (splitReg k r) := by
  have h1 : IsOpenMap (fun q : ℝ × EuclideanSpace ℝ (Fin k) => splitE k q) :=
    (Work.Drive.Whitney.splitEuclideanSpace k).choose.isOpenMap
  show IsOpenMap (fun p : ℝ × EuclideanSpace ℝ (Fin k) => splitE k (p.1, r • p.2))
  exact h1.comp (isOpenMap_scale k r hr)

/-- The parametrisation of the second sheet. -/
def fingerParam {k : ℕ} {M : Type*} [TopologicalSpace M]
    (c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1)))) (r : ℝ)
    (p : ℝ × EuclideanSpace ℝ (Fin k)) : M :=
  c₂.symm (splitE k (p.1, r • p.2))

/-- The height of the second sheet over the window: the arch of the lens. -/
def fingerHeight (k : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin k)) :
    ℝ × EuclideanSpace ℝ (Fin k) :=
  (arch p.1, 0)

theorem contDiff_fingerHeight (k : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fingerHeight k) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin k) => arch p.1) :=
    contDiff_arch.comp contDiff_fst
  exact h1.prodMk contDiff_const

/-- The two coordinates of a point of the ambient space that the finger row pins: the `x`- and the
`v`-coordinate of `Φ ∘ f`. -/
def fingerCoords {k : ℕ} {M : Type*}
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))) (y : M) :
    ℝ × EuclideanSpace ℝ (Fin k) :=
  ((Φ (f y)).1, (Φ (f y)).2.2.2)

theorem fingerBlock {k : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * (k + 1))), Θ (Φ y) = y)
    (hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ)
    (W : Set M) (p₂ q₂ : M) (γ₂ : ℝ → M)
    (hγ₂ : Continuous γ₂) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγ₂W : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc₂ : Work.Whitney.IsSmoothChart c₂) (hc₂W : c₂.source ⊆ W)
    (hp₂c₂ : p₂ ∈ c₂.source) (hq₂c₂ : q₂ ∈ c₂.source)
    (harc₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      c₂ (γ₂ t) = Work.Drive.PushDisc.splitE k (((2 : ℝ) * t - 1), (0 : EuclideanSpace ℝ (Fin k))))
    (X' : ℝ) (hX' : 1 < X') (r : ℝ) (hr : 0 < r)
    (hwinc : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), p ∈ Work.Drive.PushDisc.asymReg k X' →
      Work.Drive.PushDisc.splitE k (p.1, r • p.2) ∈ c₂.target)
    (hp₂pin : Φ (f p₂) = ((-1 : ℝ), 0, 0, 0)) (hq₂pin : Φ (f q₂) = ((1 : ℝ), 0, 0, 0))
    (hfinger : ∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)), |x| < X' → ‖w‖ < 1 →
      Φ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, r • w))))
        = (x, Work.Drive.PushDisc.arch x, 0, w)) :
    ∃ (σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M)
      (h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k)),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Work.Drive.PushDisc.asymReg k X') ∧
      (∀ p ∈ Work.Drive.PushDisc.asymReg k X', f (σ₂ p) = Θ (p.1, (h p).1, (h p).2, p.2)) ∧
      σ₂ ((-1 : ℝ), 0) = p₂ ∧ σ₂ ((1 : ℝ), 0) = q₂ ∧
      (∀ X'' : ℝ, 1 < X'' → X'' ≤ X' → IsOpen (σ₂ '' Work.Drive.PushDisc.asymReg k X'')) ∧
      σ₂ '' Work.Drive.PushDisc.asymReg k X' ⊆ W ∧
      (∀ x : ℝ, |x| < X' → h (x, 0) = (Work.Drive.PushDisc.arch x, 0)) ∧
      (∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ Work.Drive.PushDisc.asymReg k X',
        ‖h p - (Work.Drive.PushDisc.arch p.1, 0)‖ ≤ L * ‖p.2‖) ∧
      (∀ X'' : ℝ, 1 < X'' → X'' ≤ X' → ∀ x ∈ frontier (σ₂ '' Work.Drive.PushDisc.asymReg k X''),
        |(Φ (f x)).1| = X'' ∨ ‖(Φ (f x)).2.2.2‖ = 1) := by
  refine ⟨fingerParam c₂ r, fingerHeight k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (contDiff_fingerHeight k).contDiffOn
  · intro p hp
    have hf' : Φ (f (c₂.symm (splitE k (p.1, r • p.2))))
        = (p.1, arch p.1, (0 : EuclideanSpace ℝ (Fin k)), p.2) :=
      hfinger p.1 p.2 hp.1 hp.2
    have hfp : fingerParam c₂ r p = c₂.symm (splitE k (p.1, r • p.2)) := rfl
    have hh : fingerHeight k p = (arch p.1, (0 : EuclideanSpace ℝ (Fin k))) := rfl
    rw [hfp, hh, ← hΘΦ (f (c₂.symm (splitE k (p.1, r • p.2)))), hf']
  · -- `σ₂ (-1,0) = p₂`
    have hc2p : c₂ p₂ = splitE k ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
      have h := harc₂ 0 (by norm_num)
      rw [hγ₂0] at h
      have h2 : (2 : ℝ) * 0 - 1 = -1 := by norm_num
      rwa [h2] at h
    have hp : fingerParam c₂ r ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))
        = c₂.symm (splitE k ((-1 : ℝ), r • (0 : EuclideanSpace ℝ (Fin k)))) := rfl
    rw [hp, smul_zero, ← hc2p]
    exact c₂.left_inv hp₂c₂
  · -- `σ₂ (1,0) = q₂`
    have hc2q : c₂ q₂ = splitE k ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
      have h := harc₂ 1 (by norm_num)
      rw [hγ₂1] at h
      have h2 : (2 : ℝ) * 1 - 1 = 1 := by norm_num
      rwa [h2] at h
    have hp : fingerParam c₂ r ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))
        = c₂.symm (splitE k ((1 : ℝ), r • (0 : EuclideanSpace ℝ (Fin k)))) := rfl
    rw [hp, smul_zero, ← hc2q]
    exact c₂.left_inv hq₂c₂
  · -- openness of the image of every smaller window
    intro X'' hX''1 hX''X'
    have hUsub : asymReg k X'' ⊆ asymReg k X' :=
      fun p hp => ⟨lt_of_lt_of_le hp.1 hX''X', hp.2⟩
    have hsubT : splitReg k r '' asymReg k X'' ⊆ c₂.target := by
      rintro y ⟨p, hp, rfl⟩
      exact hwinc p (hUsub hp)
    have himg : fingerParam c₂ r '' asymReg k X''
        = c₂.symm '' (splitReg k r '' asymReg k X'') :=
      Set.image_comp c₂.symm (splitReg k r) (asymReg k X'')
    rw [himg, c₂.symm_image_eq_source_inter_preimage hsubT]
    exact c₂.isOpen_inter_preimage (isOpenMap_splitReg k r hr.ne' _ (isOpen_asymReg k X''))
  · -- containment in `W`
    rintro y ⟨p, hp, rfl⟩
    refine hc₂W ?_
    have hfp : fingerParam c₂ r p = c₂.symm (splitE k (p.1, r • p.2)) := rfl
    rw [hfp]
    exact symm_mem_source c₂ (hwinc p hp)
  · -- the axis values
    intro x hx
    exact rfl
  · -- the Lipschitz row, with `L = 0`
    refine ⟨0, le_refl 0, ?_⟩
    intro p hp
    have hh : fingerHeight k p = (arch p.1, (0 : EuclideanSpace ℝ (Fin k))) := rfl
    rw [hh]
    simp
  · -- the frontier row
    intro X'' hX''1 hX''X'
    have hUsub : asymReg k X'' ⊆ asymReg k X' :=
      fun p hp => ⟨lt_of_lt_of_le hp.1 hX''X', hp.2⟩
    have hsubT : splitReg k r '' asymReg k X'' ⊆ c₂.target := by
      rintro y ⟨p, hp, rfl⟩
      exact hwinc p (hUsub hp)
    have hOpenS : IsOpen (fingerParam c₂ r '' asymReg k X'') := by
      have himg : fingerParam c₂ r '' asymReg k X''
          = c₂.symm '' (splitReg k r '' asymReg k X'') :=
        Set.image_comp c₂.symm (splitReg k r) (asymReg k X'')
      rw [himg, c₂.symm_image_eq_source_inter_preimage hsubT]
      exact c₂.isOpen_inter_preimage (isOpenMap_splitReg k r hr.ne' _ (isOpen_asymReg k X''))
    -- the coordinate map of the finger
    have hgcont : Continuous (fingerCoords Φ f) := by
      have hΦf : Continuous (fun y : M => Φ (f y)) := hΦsm.continuous.comp hf.continuous
      exact Continuous.prodMk hΦf.fst hΦf.snd.snd.snd
    -- it inverts the parametrisation on the window
    have hginv : ∀ p ∈ asymReg k X'', fingerCoords Φ f (fingerParam c₂ r p) = p := by
      intro p hp
      have hf' := hfinger p.1 p.2 (hUsub hp).1 (hUsub hp).2
      have hfp : fingerParam c₂ r p = c₂.symm (splitE k (p.1, r • p.2)) := rfl
      show ((Φ (f (fingerParam c₂ r p))).1, (Φ (f (fingerParam c₂ r p))).2.2.2) = p
      rw [hfp, hf']
    -- hence the coordinate map carries the finger onto the window
    have hgimg : fingerCoords Φ f '' (fingerParam c₂ r '' asymReg k X'') = asymReg k X'' := by
      ext q
      constructor
      · rintro ⟨y, ⟨p, hp, rfl⟩, hyq⟩
        rw [← hyq, hginv p hp]
        exact hp
      · intro hq
        exact ⟨fingerParam c₂ r q, ⟨q, hq, rfl⟩, hginv q hq⟩
    intro x hx
    have hxcl : x ∈ closure (fingerParam c₂ r '' asymReg k X'') := frontier_subset_closure hx
    have hxnot : x ∉ fingerParam c₂ r '' asymReg k X'' := by
      intro hxS
      have h2 : x ∈ closure (fingerParam c₂ r '' asymReg k X'')ᶜ := by
        have h3 := hx
        rw [frontier_eq_closure_inter_closure] at h3
        exact h3.2
      rw [IsClosed.closure_eq (isClosed_compl_iff.mpr hOpenS)] at h2
      exact h2 hxS
    have hgg : fingerCoords Φ f x ∈ closure (asymReg k X'') := by
      have h1 : fingerCoords Φ f x
          ∈ closure (fingerCoords Φ f '' (fingerParam c₂ r '' asymReg k X'')) :=
        map_mem_closure hgcont hxcl (fun y hy => ⟨y, hy, rfl⟩)
      rwa [hgimg] at h1
    have hle : |(fingerCoords Φ f x).1| ≤ X'' ∧ ‖(fingerCoords Φ f x).2‖ ≤ 1 :=
      closure_asymReg_subset k X'' hgg
    have hkey : ¬ (|(fingerCoords Φ f x).1| < X'' ∧ ‖(fingerCoords Φ f x).2‖ < 1) := by
      rintro ⟨h1, h2⟩
      have hp0 : fingerCoords Φ f x ∈ asymReg k X'' := ⟨h1, h2⟩
      have hTt : splitE k ((fingerCoords Φ f x).1, r • (fingerCoords Φ f x).2) ∈ c₂.target :=
        hwinc _ (hUsub hp0)
      have hσcont : ContinuousAt (fingerParam c₂ r) (fingerCoords Φ f x) := by
        show ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
          c₂.symm (splitE k (p.1, r • p.2))) (fingerCoords Φ f x)
        have hinner : ContinuousAt (splitReg k r) (fingerCoords Φ f x) :=
          (continuous_splitReg k r).continuousAt
        have houter : ContinuousAt c₂.symm (splitReg k r (fingerCoords Φ f x)) :=
          c₂.continuousAt_symm hTt
        exact houter.comp hinner
      have hpair : ContinuousAt
          (fun y : M => (fingerParam c₂ r (fingerCoords Φ f y), y)) x :=
        (hσcont.comp hgcont.continuousAt).prodMk continuousAt_id
      have hdiag : (fingerParam c₂ r (fingerCoords Φ f x), x) ∈ Set.diagonal M := by
        haveI : (nhdsWithin x (fingerParam c₂ r '' asymReg k X'')).NeBot :=
          mem_closure_iff_nhdsWithin_neBot.1 hxcl
        refine IsClosed.mem_of_tendsto isClosed_diagonal
          (hpair.continuousWithinAt (s := fingerParam c₂ r '' asymReg k X'')) ?_
        refine Filter.eventually_of_mem self_mem_nhdsWithin ?_
        rintro y ⟨p, hp, rfl⟩
        rw [Set.mem_diagonal_iff, hginv p hp]
      have hσgx : fingerParam c₂ r (fingerCoords Φ f x) = x := by
        have h := hdiag
        rwa [Set.mem_diagonal_iff] at h
      exact hxnot ⟨fingerCoords Φ f x, hp0, hσgx⟩
    rcases lt_or_eq_of_le hle.1 with h1 | h1
    · rcases lt_or_eq_of_le hle.2 with h2 | h2
      · exact absurd ⟨h1, h2⟩ hkey
      · exact Or.inr h2
    · exact Or.inl h1

end

end Work.Drive.PushDisc
