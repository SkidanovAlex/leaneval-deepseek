import Mathlib
import Submission.Work.Drive.PushDisc.chartObligation
import Submission.Work.Drive.PushDisc.milnorLens
import Submission.Work.Drive.PushDisc.asymChart
import Submission.Work.Drive.PushDisc.cleanRegionIsolation
import Submission.Work.Drive.PushDisc.thetaMapDefs
import Submission.Work.Drive.PushDisc.exists_chart_of_arc
import Submission.Work.Drive.PushDisc.lensThetaRows
import Submission.Work.Drive.PushDisc.lensFramesWide
import Submission.Work.Drive.PushDisc.fingerBlock
import Submission.Work.Drive.PushDisc.lensThetaGlobal

namespace Work.Drive.PushDisc

open scoped ContDiff Manifold Topology
open Set Metric

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section

/-!
# `lensAssemblySolid`: the C5 assembly of the clean-lens route

This file proves `Work.Drive.PushDisc.lensAssemblySolid`: the assembly (C5) of the compact `n ≥ 3`
case of the Whitney embedding theorem — the construction of one `ChartObligation` from the rows
produced by S5 (`Φ₀`, `Θ₀`, `U₁`, `hseg`), A2 (`Δ`), C3 (`c₂`, `hwinc`), D1 (`Θg`, `Θgi` with the
plane and disc rows) and `whitneyDiscSmooth` (`D`, `hDclean`).

The assembly is the one specified in `NOTES_S_H344_LENS_CLEAN_STATE.md` §10/§16/§17/§19:

* `Φ := Θgi ∘ Φ₀`, `Θ := Θ₀ ∘ Θg` (the global framing, inverted on the chart side),
* `c := arch`, `h := fingerHeight k = fun p => (arch p.1, 0)`,
* `σ₂ p := c₂.symm (splitE k (p.1, r • p.2)) = fingerParam c₂ r p`,
* `V := {ξ | ∃ a ∈ Δ '' lensK, dist (Θg ξ) a < δ}` with `δ` from
  `Work.Drive.PushDisc.exists_isolation_of_cleanRegion` applied to `g = Φ₀ ∘ f`, `D = Δ`,
  `K = lensK`, `Ko = lensKo` (the cleanness row `hΔclean`) and the open set `U₁ ∪ σ₂ '' asymReg`.

The rows `hσ₂`, `hW₀o`, `hW₀W`, `hcore`, `hlip`, `hfrontier` come from the finger block
(`Work.Drive.PushDisc.fingerBlock`, here in the `fingerBlockRows` form: the concrete witnesses
`fingerParam c₂ r`, `fingerHeight k`, and without the two hypotheses that proof never uses —
`IsSmoothChart c₂` and `Set.InjOn γ₂ (Icc 0 1)`; the former is *not* a consequence of the
charted-space structure, so it cannot be supplied by the assembly).

The one genuine ingredient added here is the **cover row** of the isolation: every point `z` whose
model coordinates lie in the *boundary* `lensK \ lensKo` of the lens is in `U₁ ∪ σ₂ '' asymReg`.
The bottom edge `y = 0` is covered by `hseg` (through `hclean`), the top edge `y = arch x` by `hΔ1`
(i.e. by the finger); the two disjuncts of `hclean` that would send `z` to `p₁` or `q₁` are killed
by `p₂ ∉ U₁` and `q₂ ∉ U₁`, which are proved (`not_mem_U₁_of_finger_pin`) from `hU₁row`, the
finger row and the *plane* row of `Θg`.
-/

/-! ## The finger block, with the concrete witnesses -/

/-- **`fingerBlock` with its witnesses made explicit and its unused rows removed.**  The statement
is `Work.Drive.PushDisc.fingerBlock` with the two hypotheses that its proof never uses —
`Work.Whitney.IsSmoothChart c₂` and `Set.InjOn γ₂ (Icc 0 1)` — removed and with the existential
witnesses `fingerParam c₂ r`, `fingerHeight k` written out. -/
theorem fingerBlockRows {k : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
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
    (c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc₂W : c₂.source ⊆ W)
    (hp₂c₂ : p₂ ∈ c₂.source) (hq₂c₂ : q₂ ∈ c₂.source)
    (harc₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      c₂ (γ₂ t) = Work.Drive.PushDisc.splitE k (((2 : ℝ) * t - 1), (0 : EuclideanSpace ℝ (Fin k))))
    (X' : ℝ) (hX' : 1 < X') (r : ℝ) (hr : 0 < r)
    (hwinc : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), p ∈ Work.Drive.PushDisc.asymReg k X' →
      Work.Drive.PushDisc.splitE k (p.1, r • p.2) ∈ c₂.target)
    (hfinger : ∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)), |x| < X' → ‖w‖ < 1 →
      Φ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, r • w))))
        = (x, Work.Drive.PushDisc.arch x, 0, w)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fingerHeight k) (Work.Drive.PushDisc.asymReg k X') ∧
    (∀ p ∈ Work.Drive.PushDisc.asymReg k X',
      f (fingerParam c₂ r p) = Θ (p.1, (fingerHeight k p).1, (fingerHeight k p).2, p.2)) ∧
    fingerParam c₂ r ((-1 : ℝ), 0) = p₂ ∧ fingerParam c₂ r ((1 : ℝ), 0) = q₂ ∧
    (∀ X'' : ℝ, 1 < X'' → X'' ≤ X' →
      IsOpen (fingerParam c₂ r '' Work.Drive.PushDisc.asymReg k X'')) ∧
    fingerParam c₂ r '' Work.Drive.PushDisc.asymReg k X' ⊆ W ∧
    (∀ x : ℝ, |x| < X' → fingerHeight k (x, 0) = (Work.Drive.PushDisc.arch x, 0)) ∧
    (∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ Work.Drive.PushDisc.asymReg k X',
      ‖fingerHeight k p - (Work.Drive.PushDisc.arch p.1, 0)‖ ≤ L * ‖p.2‖) ∧
    (∀ X'' : ℝ, 1 < X'' → X'' ≤ X' →
      ∀ x ∈ frontier (fingerParam c₂ r '' Work.Drive.PushDisc.asymReg k X''),
        |(Φ (f x)).1| = X'' ∨ ‖(Φ (f x)).2.2.2‖ = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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


/-! ## Two auxiliary facts used by the assembly -/

/-- **The finger parametrisation is injective on the window.**  Both factors are: `splitE k` is a
linear equivalence and `c₂.symm` is injective on `c₂.target`, which contains the image of the window
by `hwinc`. -/
theorem fingerParam_injOn {k : ℕ} {M : Type*} [TopologicalSpace M]
    (c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1)))) {r X' : ℝ} (hr : 0 < r)
    (hwinc : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), p ∈ Work.Drive.PushDisc.asymReg k X' →
      Work.Drive.PushDisc.splitE k (p.1, r • p.2) ∈ c₂.target) :
    Set.InjOn (fingerParam c₂ r) (Work.Drive.PushDisc.asymReg k X') := by
  intro p hp q hq hpq
  have hpt : Work.Drive.PushDisc.splitE k (p.1, r • p.2) ∈ c₂.target := hwinc p hp
  have hqt : Work.Drive.PushDisc.splitE k (q.1, r • q.2) ∈ c₂.target := hwinc q hq
  have h2 : c₂.symm (Work.Drive.PushDisc.splitE k (p.1, r • p.2))
      = c₂.symm (Work.Drive.PushDisc.splitE k (q.1, r • q.2)) := hpq
  have h3 := congrArg c₂ h2
  rw [c₂.right_inv hpt, c₂.right_inv hqt] at h3
  have h4 : (p.1, r • p.2) = (q.1, r • q.2) := (Work.Drive.PushDisc.splitE k).injective h3
  obtain ⟨h6, h5'⟩ := Prod.ext_iff.mp h4
  have h5 : p.2 = q.2 := by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin k) => r⁻¹ • v) h5'
    simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hr)] using this
  exact Prod.ext h6 h5

/-- **A pinned finger point is never in the flat tube `U₁`.**  The proof is a limit argument at the
two corners `x = ±1`: since `U₁` is open and the finger passes through the pin, the whole
`x`-interval around the corner consists of points of `U₁`; their `Φ₀ ∘ f`-images lie in the plane
`{y = 0, v = 0}` while their `Θg`-images are the arch curve `x ↦ Θg (x, arch x, 0, 0)`.  Since `Θg`
is the identity on the plane and `Θgi` is its inverse, the arch point `(x, arch x, 0, 0)` itself has
to lie in the plane, i.e. `arch x = 0` — impossible for `x` strictly between the corners, and at a
corner the point would be the pin itself, contradicting strict closeness. -/
theorem not_mem_U₁_of_finger_pin {k : ℕ} {M : Type*} [TopologicalSpace M]
    {f : M → EuclideanSpace ℝ (Fin (2 * (k + 1)))}
    {U₁ : Set M} (hU₁o : IsOpen U₁)
    {Φ₀ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k}
    {Θg Θgi : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k}
    (hlΘ : Function.LeftInverse Θgi Θg) (hΘgcont : Continuous Θg)
    {X' : ℝ} (hX' : 1 < X')
    (hplane0 : ∀ (x : ℝ) (u : EuclideanSpace ℝ (Fin k)), |x| ≤ X' → ‖u‖ ≤ 1 →
      Θg (x, 0, u, 0) = (x, 0, u, 0))
    (hU₁row : ∀ x : M, x ∈ U₁ →
      Φ₀ (f x) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0})
    {σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M}
    (hσ₂row : ∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)), |x| < X' → ‖w‖ < 1 →
      Θg (x, Work.Drive.PushDisc.arch x, 0, w) = Φ₀ (f (σ₂ (x, w))))
    {a : ℝ} (ha : a = -1 ∨ a = 1) (hσ₂cont : ContinuousAt σ₂ (a, 0)) :
    σ₂ (a, 0) ∉ U₁ := by
  intro hpin
  have haabs : |a| ≤ X' := by
    rcases ha with rfl | rfl <;> · simp only [abs_one, abs_neg]; linarith [hX']
  -- a radius on which `σ₂` lands in `U₁`
  obtain ⟨δ, hδpos, hδU⟩ : ∃ δ > 0, ∀ q : ℝ × EuclideanSpace ℝ (Fin k),
      dist q (a, 0) < δ → σ₂ q ∈ U₁ := by
    have hev : {q : ℝ × EuclideanSpace ℝ (Fin k) | σ₂ q ∈ U₁} ∈ 𝓝 (a, 0) :=
      hσ₂cont.eventually (hU₁o.mem_nhds hpin)
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hev
    exact ⟨δ, hδ, fun q hq => hsub (Metric.mem_ball.mpr hq)⟩
  -- the composite `q ↦ Θg (q.1, arch q.1, 0, 0)`
  set F : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k :=
    fun q => Θg (q.1, Work.Drive.PushDisc.arch q.1, 0, (0 : EuclideanSpace ℝ (Fin k))) with hFdef
  have hFcont : Continuous F := by
    have harch : Continuous
        (fun q : ℝ × EuclideanSpace ℝ (Fin k) => Work.Drive.PushDisc.arch q.1) :=
      contDiff_arch.continuous.comp continuous_fst
    have h1 : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin k) =>
        (q.1, (Work.Drive.PushDisc.arch q.1,
          ((0 : EuclideanSpace ℝ (Fin k)), (0 : EuclideanSpace ℝ (Fin k)))))) :=
      continuous_fst.prodMk (harch.prodMk (continuous_const.prodMk continuous_const))
    exact hΘgcont.comp h1
  have hFa : F (a, 0) = ((a : ℝ), 0, 0, 0) := by
    have har : Work.Drive.PushDisc.arch a = 0 := by
      rcases ha with rfl | rfl <;> norm_num [Work.Drive.PushDisc.arch]
    show Θg (a, Work.Drive.PushDisc.arch a, 0, 0) = ((a : ℝ), 0, 0, 0)
    rw [har]
    exact hplane0 a 0 haabs (by simp)
  -- the open set of good points
  set S : Set (ℝ × EuclideanSpace ℝ (Fin k)) :=
    {q | dist q (a, 0) < δ} ∩ Work.Drive.PushDisc.asymReg k X' ∩ {q | |q.1 - a| < 1} ∩
      {q | |(F q).1| < X'} ∩ {q | ‖(F q).2.2.1‖ < 1} with hSdef
  have hSopen : IsOpen S := by
    have h1 : IsOpen {q : ℝ × EuclideanSpace ℝ (Fin k) | dist q (a, 0) < δ} :=
      isOpen_lt (continuous_id.dist continuous_const) continuous_const
    have h2 : IsOpen (Work.Drive.PushDisc.asymReg k X') := isOpen_asymReg k X'
    have h3 : IsOpen {q : ℝ × EuclideanSpace ℝ (Fin k) | |q.1 - a| < 1} :=
      isOpen_lt ((continuous_fst.sub continuous_const).abs) continuous_const
    have h4 : IsOpen {q : ℝ × EuclideanSpace ℝ (Fin k) | |(F q).1| < X'} :=
      isOpen_lt ((continuous_fst.comp hFcont).abs) continuous_const
    have h5 : IsOpen {q : ℝ × EuclideanSpace ℝ (Fin k) | ‖(F q).2.2.1‖ < 1} := by
      have hc : Continuous (fun q : ℝ × EuclideanSpace ℝ (Fin k) => (F q).2.2.1) :=
        continuous_fst.comp (continuous_snd.comp (continuous_snd.comp hFcont))
      exact isOpen_lt hc.norm continuous_const
    rw [hSdef]
    exact (((h1.inter h2).inter h3).inter h4).inter h5
  have hSmem : (a, (0 : EuclideanSpace ℝ (Fin k))) ∈ S := by
    rw [hSdef]
    refine ⟨⟨⟨⟨by simp [hδpos], ⟨?_, by simp⟩⟩, by simp⟩, ?_⟩, ?_⟩
    · rcases ha with rfl | rfl <;> · simp only [abs_one, abs_neg]; linarith [hX']
    · show |(F (a, 0)).1| < X'
      rw [hFa]; rcases ha with rfl | rfl <;> norm_num <;> linarith [hX']
    · show ‖(F (a, 0)).2.2.1‖ < 1
      rw [hFa]; simp
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hSopen (a, 0) hSmem
  -- a point of `S` strictly closer to `a` than the corners
  set lam : ℝ := ε / 4 with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; linarith
  have hqmem : ((a + lam, (0 : EuclideanSpace ℝ (Fin k))) : ℝ × EuclideanSpace ℝ (Fin k))
      ∈ Metric.ball (a, 0) ε := by
    rw [Metric.mem_ball, Prod.dist_eq, dist_self, max_eq_left (by positivity)]
    show dist (a + lam) a < ε
    rw [Real.dist_eq, show a + lam - a = lam by ring, abs_of_pos hlampos]
    rw [hlamdef]; linarith
  have hq : ((a + lam, (0 : EuclideanSpace ℝ (Fin k))) : ℝ × EuclideanSpace ℝ (Fin k)) ∈ S :=
    hεsub hqmem
  rw [hSdef] at hq
  obtain ⟨⟨⟨⟨hqd, hqreg⟩, hqa⟩, hqFX⟩, hqFu⟩ := hq
  have hqU : σ₂ (a + lam, 0) ∈ U₁ := hδU _ hqd
  -- the plane membership of `F (a+lam, 0)`
  have hηP : F (a + lam, 0) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0} := by
    have h1 : Φ₀ (f (σ₂ (a + lam, 0))) ∈
        {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0} := hU₁row _ hqU
    have h2 : Θg (a + lam, Work.Drive.PushDisc.arch (a + lam), 0,
        (0 : EuclideanSpace ℝ (Fin k))) = Φ₀ (f (σ₂ (a + lam, 0))) :=
      hσ₂row (a + lam) 0 hqreg.1 hqreg.2
    rw [← h2] at h1
    exact h1
  have hηeq : F (a + lam, 0)
      = ((F (a + lam, 0)).1, (0 : ℝ), (F (a + lam, 0)).2.2.1,
          (0 : EuclideanSpace ℝ (Fin k))) := by
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
    · exact hηP.1
    · exact hηP.2
  have hΘgη : Θg (F (a + lam, 0)) = F (a + lam, 0) := by
    conv_lhs => rw [hηeq]
    rw [hplane0 _ _ (le_of_lt hqFX) (le_of_lt hqFu), hηeq]
  have hΘgiη : Θgi (F (a + lam, 0)) = F (a + lam, 0) := by
    calc Θgi (F (a + lam, 0)) = Θgi (Θg (F (a + lam, 0))) := by rw [hΘgη]
      _ = F (a + lam, 0) := hlΘ _
  have hfin : ((a + lam : ℝ), Work.Drive.PushDisc.arch (a + lam),
      (0 : EuclideanSpace ℝ (Fin k)), (0 : EuclideanSpace ℝ (Fin k))) = F (a + lam, 0) := by
    have h3 : Θgi (F (a + lam, 0))
        = ((a + lam : ℝ), Work.Drive.PushDisc.arch (a + lam),
            (0 : EuclideanSpace ℝ (Fin k)), (0 : EuclideanSpace ℝ (Fin k))) := by
      have hFF : F (a + lam, 0) = Θg ((a + lam : ℝ), Work.Drive.PushDisc.arch (a + lam),
          (0 : EuclideanSpace ℝ (Fin k)), (0 : EuclideanSpace ℝ (Fin k))) := rfl
      have := hlΘ ((a + lam : ℝ), Work.Drive.PushDisc.arch (a + lam),
          (0 : EuclideanSpace ℝ (Fin k)), (0 : EuclideanSpace ℝ (Fin k)))
      rwa [← hFF] at this
    exact h3 ▸ hΘgiη
  have harch0 : Work.Drive.PushDisc.arch (a + lam) = 0 := by
    have h1 := congrArg (fun ξ : Work.Drive.Whitney.Mdl k => ξ.2.1) hfin
    rw [hηP.1] at h1
    simpa using h1
  have hsq : (a + lam) ^ 2 = 1 := by
    have h1 := harch0
    simp [Work.Drive.PushDisc.arch] at h1
    linarith
  have hlamabs : |lam| < 1 := by simpa using hqa
  have habs' : -1 < lam ∧ lam < 1 := abs_lt.mp hlamabs
  rcases sq_eq_one_iff.mp hsq with hs | hs
  · rcases ha with h1 | h1 <;> linarith
  · rcases ha with h1 | h1 <;> linarith

/-! ## The assembly -/

theorem lensAssemblySolid {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (k : ℕ) (hk : n = k + 1) (X' : ℝ) (hX' : 1 < X') (r : ℝ) (hr : 0 < r)
    (γ₂ : ℝ → M) (hγ₂ : Continuous γ₂) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγ₂W : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (Φ₀ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k)
    (Θ₀ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n)))
    (hΦ₀sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ₀)
    (hΘ₀sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ₀)
    (hΘ₀Φ₀ : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ₀ (Φ₀ y) = y)
    (hΦ₀Θ₀ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ₀ (Θ₀ ξ) = ξ)
    (U₁ : Set M) (hU₁o : IsOpen U₁) (hU₁W : U₁ ⊆ W)
    (hU₁row : ∀ x : M, x ∈ U₁ →
      Φ₀ (f x) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0})
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hseg : ∀ x : ℝ, |x| ≤ 1 + δ₀ → ∃ z : M, z ∈ U₁ ∧ Φ₀ (f z) = (x, 0, 0, 0))
    (hp₁c : f p₁ = Θ₀ ((-1 : ℝ), 0, 0, 0)) (hq₁c : f q₁ = Θ₀ ((1 : ℝ), 0, 0, 0))
    (hpin₂ : Φ₀ (f p₂) = ((-1 : ℝ), 0, 0, 0)) (hpin₄ : Φ₀ (f q₂) = ((1 : ℝ), 0, 0, 0))
    (c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    (hc₂W : c₂.source ⊆ W)
    (hp₂c₂ : p₂ ∈ c₂.source) (hq₂c₂ : q₂ ∈ c₂.source)
    (harc₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      c₂ (γ₂ t) = Work.Drive.PushDisc.splitE k (((2 : ℝ) * t - 1), (0 : EuclideanSpace ℝ (Fin k))))
    (hwinc : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), p ∈ Work.Drive.PushDisc.asymReg k X' →
      Work.Drive.PushDisc.splitE k (p.1, r • p.2) ∈ c₂.target)
    (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (hΔsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ)
    (hΔ0 : ∀ x : ℝ, Δ (x, 0) = (x, 0, 0, 0))
    (hΔ1 : ∀ x : ℝ, Δ (x, Work.Drive.PushDisc.arch x)
      = Φ₀ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))))))
    (hΔclean : ∀ z : M, Φ₀ (f z) ∉ Δ '' Work.Drive.PushDisc.lensKo)
    (Θg Θgi : Work.Drive.Whitney.Mdl k → Work.Drive.Whitney.Mdl k)
    (hΘgsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θg)
    (hΘgism : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θgi)
    (hlΘ : Function.LeftInverse Θgi Θg) (hrΘ : Function.RightInverse Θgi Θg)
    (hplane0 : ∀ (x : ℝ) (u : EuclideanSpace ℝ (Fin k)), |x| ≤ X' → ‖u‖ ≤ 1 →
      Θg (x, 0, u, (0 : EuclideanSpace ℝ (Fin k))) = (x, 0, u, (0 : EuclideanSpace ℝ (Fin k))))
    (hdisc : ∀ (x y : ℝ), |x| ≤ X' → 0 ≤ y → y ≤ Work.Drive.PushDisc.arch x →
      Θg (x, y, 0, 0) = Δ (x, y))
    (hfinger : ∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)), |x| < X' → ‖w‖ < 1 →
      Θg (x, Work.Drive.PushDisc.arch x, 0, w)
        = Φ₀ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, r • w)))))
    (D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)))
    (hDclean : ∀ z : M, f z ∉ D '' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)) :
    Nonempty (Work.Drive.PushDisc.ChartObligation n f W p₁ p₂ q₁ q₂) := by
  subst hk
  -- ### the chart pair `(Φ, Θ) = (Θgi ∘ Φ₀, Θ₀ ∘ Θg)`
  set Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k :=
    fun y => Θgi (Φ₀ y) with hΦdef
  set Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))) :=
    fun ξ => Θ₀ (Θg ξ) with hΘdef
  have hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := hΘgism.comp hΦ₀sm
  have hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ := hΘ₀sm.comp hΘgsm
  have hΘΦ : ∀ y, Θ (Φ y) = y := by
    intro y
    change Θ₀ (Θg (Θgi (Φ₀ y))) = y
    rw [hrΘ (Φ₀ y), hΘ₀Φ₀ y]
  have hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ := by
    intro ξ
    change Θgi (Φ₀ (Θ₀ (Θg ξ))) = ξ
    rw [hΦ₀Θ₀ (Θg ξ), hlΘ ξ]
  have hΦ₀inj : Function.Injective Φ₀ := fun a b h => by
    have h2 := congrArg Θ₀ h
    rwa [hΘ₀Φ₀ a, hΘ₀Φ₀ b] at h2
  have hΘg_neg : Θg ((-1 : ℝ), (0 : ℝ), (0 : EuclideanSpace ℝ (Fin k)),
      (0 : EuclideanSpace ℝ (Fin k)))
      = ((-1 : ℝ), (0 : ℝ), (0 : EuclideanSpace ℝ (Fin k)),
          (0 : EuclideanSpace ℝ (Fin k))) :=
    hplane0 (-1) 0 (by simp only [abs_neg, abs_one]; linarith [hX']) (by simp)
  have hΘg_pos : Θg ((1 : ℝ), (0 : ℝ), (0 : EuclideanSpace ℝ (Fin k)),
      (0 : EuclideanSpace ℝ (Fin k)))
      = ((1 : ℝ), (0 : ℝ), (0 : EuclideanSpace ℝ (Fin k)),
          (0 : EuclideanSpace ℝ (Fin k))) :=
    hplane0 1 0 (by simp only [abs_one]; linarith [hX']) (by simp)
  -- ### the finger row, in `Φ`-coordinates
  have hfingerΦ : ∀ (x : ℝ) (w : EuclideanSpace ℝ (Fin k)), |x| < X' → ‖w‖ < 1 →
      Φ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, r • w))))
        = (x, Work.Drive.PushDisc.arch x, 0, w) := by
    intro x w hx hw
    change Θgi (Φ₀ (f (c₂.symm (Work.Drive.PushDisc.splitE k (x, r • w)))))
      = (x, Work.Drive.PushDisc.arch x, 0, w)
    rw [← hfinger x w hx hw]
    exact hlΘ _
  -- ### the finger block
  obtain ⟨hh, hσ₂row, hp₂f, hq₂f, hW₀o, hW₀W, hcore, hlip, hfrontier⟩ :=
    fingerBlockRows f hf Φ Θ hΦsm hΘsm hΘΦ hΦΘ W p₂ q₂ γ₂ hγ₂ hγ₂0 hγ₂1 hγ₂W c₂ hc₂W hp₂c₂
      hq₂c₂ harc₂ X' hX' r hr hwinc hfingerΦ
  have hσ₂inj : Set.InjOn (fingerParam c₂ r) (Work.Drive.PushDisc.asymReg k X') :=
    fingerParam_injOn c₂ hr hwinc
  -- ### the two pins are not in the flat tube
  have hmem_neg : ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) ∈
      Work.Drive.PushDisc.asymReg k X' := by
    refine ⟨?_, by simp⟩
    simp only [abs_neg, abs_one]; linarith [hX']
  have hmem_pos : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) ∈
      Work.Drive.PushDisc.asymReg k X' := by
    refine ⟨?_, by simp⟩
    simp only [abs_one]; linarith [hX']
  have hcont_neg : ContinuousAt (fingerParam c₂ r) ((-1 : ℝ), 0) := by
    have hinner : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
        Work.Drive.PushDisc.splitE k (p.1, r • p.2)) ((-1 : ℝ), 0) :=
      (continuous_splitReg k r).continuousAt
    have hmemT : Work.Drive.PushDisc.splitE k ((-1 : ℝ), r • (0 : EuclideanSpace ℝ (Fin k)))
        ∈ c₂.target := hwinc _ hmem_neg
    change ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
      c₂.symm (Work.Drive.PushDisc.splitE k (p.1, r • p.2))) ((-1 : ℝ), 0)
    exact ContinuousAt.comp (g := c₂.symm)
      (f := fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
        Work.Drive.PushDisc.splitE k (p.1, r • p.2)) (c₂.continuousAt_symm hmemT) hinner
  have hcont_pos : ContinuousAt (fingerParam c₂ r) ((1 : ℝ), 0) := by
    have hinner : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
        Work.Drive.PushDisc.splitE k (p.1, r • p.2)) ((1 : ℝ), 0) :=
      (continuous_splitReg k r).continuousAt
    have hmemT : Work.Drive.PushDisc.splitE k ((1 : ℝ), r • (0 : EuclideanSpace ℝ (Fin k)))
        ∈ c₂.target := hwinc _ hmem_pos
    change ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
      c₂.symm (Work.Drive.PushDisc.splitE k (p.1, r • p.2))) ((1 : ℝ), 0)
    exact ContinuousAt.comp (g := c₂.symm)
      (f := fun p : ℝ × EuclideanSpace ℝ (Fin k) =>
        Work.Drive.PushDisc.splitE k (p.1, r • p.2)) (c₂.continuousAt_symm hmemT) hinner
  have hp₂U₀ : fingerParam c₂ r ((-1 : ℝ), 0) ∉ U₁ :=
    not_mem_U₁_of_finger_pin (f := f) hU₁o hlΘ hΘgsm.continuous hX' hplane0 hU₁row
      (fun x w hx hw => hfinger x w hx hw) (Or.inl rfl) hcont_neg
  have hq₂U₀ : fingerParam c₂ r ((1 : ℝ), 0) ∉ U₁ :=
    not_mem_U₁_of_finger_pin (f := f) hU₁o hlΘ hΘgsm.continuous hX' hplane0 hU₁row
      (fun x w hx hw => hfinger x w hx hw) (Or.inr rfl) hcont_pos
  -- ### the tube is cut down to the part of the plane on which `Θg` is the identity
  have hΦ₀fc : Continuous (fun x : M => Φ₀ (f x)) := hΦ₀sm.continuous.comp hf.continuous
  set U₁' : Set M := U₁ ∩ {x : M | |(Φ₀ (f x)).1| < X'}
      ∩ {x : M | ‖(Φ₀ (f x)).2.2.1‖ < 1} with hU₁'def
  have hU₁'o : IsOpen U₁' := by
    have h1 : IsOpen {x : M | |(Φ₀ (f x)).1| < X'} :=
      isOpen_lt (continuous_abs.comp (continuous_fst.comp hΦ₀fc)) continuous_const
    have h2 : IsOpen {x : M | ‖(Φ₀ (f x)).2.2.1‖ < 1} :=
      isOpen_lt (continuous_norm.comp (continuous_fst.comp (continuous_snd.comp
        (continuous_snd.comp hΦ₀fc)))) continuous_const
    rw [hU₁'def]
    exact (hU₁o.inter h1).inter h2
  have hU₁'W : U₁' ⊆ W := fun x hx => hU₁W hx.1.1
  have hU₁'row : ∀ x : M, x ∈ U₁' →
      Φ (f x) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0} := by
    intro x hx
    obtain ⟨⟨hxU, hxA⟩, hxB⟩ := hx
    have hP : Φ₀ (f x) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0} :=
      hU₁row x hxU
    have hξeq : Φ₀ (f x) = ((Φ₀ (f x)).1, (0 : ℝ), (Φ₀ (f x)).2.2.1,
        (0 : EuclideanSpace ℝ (Fin k))) := by
      refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
      · exact hP.1
      · exact hP.2
    have hgfix : Θg (Φ₀ (f x)) = Φ₀ (f x) := by
      conv_lhs => rw [hξeq]
      rw [hplane0 _ _ (le_of_lt hxA) (le_of_lt hxB), hξeq]
    have hfix : Θgi (Φ₀ (f x)) = Φ₀ (f x) := by
      calc Θgi (Φ₀ (f x)) = Θgi (Θg (Φ₀ (f x))) := by rw [hgfix]
        _ = Φ₀ (f x) := hlΘ _
    change Θgi (Φ₀ (f x)) ∈ {ξ : Work.Drive.Whitney.Mdl k | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}
    rw [hfix]
    exact hP
  have hseg' : ∀ x : ℝ, |x| ≤ 1 → ∃ z : M, z ∈ U₁' ∧ Φ₀ (f z) = (x, 0, 0, 0) := by
    intro x hx
    obtain ⟨z, hzU, hzv⟩ := hseg x (by linarith [hx, hδ₀])
    refine ⟨z, ⟨⟨hzU, ?_⟩, ?_⟩, hzv⟩
    · show |(Φ₀ (f z)).1| < X'
      rw [hzv]
      have hlt : |x| < X' := by linarith
      simpa using hlt
    · show ‖(Φ₀ (f z)).2.2.1‖ < 1
      rw [hzv]
      simp
  have hp₂U : fingerParam c₂ r ((-1 : ℝ), 0) ∉ U₁' := fun h => hp₂U₀ h.1.1
  have hq₂U : fingerParam c₂ r ((1 : ℝ), 0) ∉ U₁' := fun h => hq₂U₀ h.1.1
  -- ### the cover row of the isolation
  have hcover : ∀ z : M, Φ₀ (f z) ∈ Δ '' (Work.Drive.PushDisc.lensK \ Work.Drive.PushDisc.lensKo)
      → z ∈ U₁' ∪ fingerParam c₂ r '' Work.Drive.PushDisc.asymReg k X' := by
    intro z hz
    obtain ⟨p, hpK, hzp⟩ := hz
    obtain ⟨hp1, hp2, hp3⟩ := hpK.1
    by_cases hy : p.2 = 0
    · -- bottom edge: covered by the tube, through `hseg'` and `hclean`
      obtain ⟨w, hwU, hwv⟩ := hseg' p.1 hp1
      have hzval : Φ₀ (f z) = ((p.1 : ℝ), (0 : ℝ), (0 : EuclideanSpace ℝ (Fin k)),
          (0 : EuclideanSpace ℝ (Fin k))) := by
        have hp_eq : p = (p.1, 0) := by rw [← hy]
        rw [← hzp, hp_eq, hΔ0]
      have hfw : f w = f z := hΦ₀inj (by rw [hwv, hzval])
      have hzW : z ∈ W := by
        by_contra hznW
        exact hsep w z (hU₁'W hwU) hznW hfw
      rcases hclean w z (hU₁'W hwU) hzW hfw with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (h ▸ hwU)
      · exact Or.inr ⟨((-1 : ℝ), 0), hmem_neg, by rw [h2]; exact hp₂f⟩
      · exact absurd (h1 ▸ hwU) (hp₂f ▸ hp₂U)
      · exact Or.inr ⟨((1 : ℝ), 0), hmem_pos, by rw [h2]; exact hq₂f⟩
      · exact absurd (h1 ▸ hwU) (hq₂f ▸ hq₂U)
    · -- top edge: the disc's top edge is the finger (`hΔ1`), and `hclean` does the rest
      have hp2pos : 0 < p.2 := lt_of_le_of_ne hp2 (Ne.symm hy)
      have habs1 : |p.1| < 1 := by
        by_contra hcon
        have h1 : |p.1| = 1 := le_antisymm hp1 (not_lt.mp hcon)
        have harch : Work.Drive.PushDisc.arch p.1 = 0 := by
          have h2 : p.1 = 1 ∨ p.1 = -1 := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h1
          rcases h2 with h2 | h2 <;> simp [Work.Drive.PushDisc.arch, h2]
        linarith [hp3]
      have harch : p.2 = Work.Drive.PushDisc.arch p.1 := by
        by_contra hne
        exact hpK.2 ⟨habs1, hp2pos, lt_of_le_of_ne hp3 hne⟩
      have hzval : Φ₀ (f z) = Φ₀ (f (fingerParam c₂ r (p.1, 0))) := by
        have h1 : Φ₀ (f z) = Δ (p.1, Work.Drive.PushDisc.arch p.1) := by
          rw [← hzp]
          show Δ (p.1, p.2) = Δ (p.1, Work.Drive.PushDisc.arch p.1)
          rw [harch]
        have h2 : Δ (p.1, Work.Drive.PushDisc.arch p.1)
            = Φ₀ (f (c₂.symm (Work.Drive.PushDisc.splitE k (p.1,
                (0 : EuclideanSpace ℝ (Fin k)))))) := hΔ1 p.1
        rw [h1, h2]
        congr 1
        rw [show fingerParam c₂ r (p.1, 0)
          = c₂.symm (Work.Drive.PushDisc.splitE k (p.1, r • (0 : EuclideanSpace ℝ (Fin k))))
          from rfl, smul_zero]
      have huin : fingerParam c₂ r (p.1, 0) ∈ W :=
        hW₀W ⟨(p.1, 0), ⟨habs1.trans hX', by simp⟩, rfl⟩
      have hfz : f (fingerParam c₂ r (p.1, 0)) = f z := (hΦ₀inj hzval).symm
      have hzW : z ∈ W := by
        by_contra hznW
        exact hsep _ z huin hznW hfz
      rcases hclean _ z huin hzW hfz with
        h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨(p.1, 0), ⟨habs1.trans hX', by simp⟩, h⟩
      · exact Or.inr ⟨((-1 : ℝ), 0), hmem_neg, by rw [h2]; exact hp₂f⟩
      · exfalso
        have hpp : fingerParam c₂ r (p.1, 0) = fingerParam c₂ r ((-1 : ℝ), 0) := by
          rw [h1, hp₂f]
        have hpair := hσ₂inj ⟨habs1.trans hX', by simp⟩ hmem_neg hpp
        have hfst : p.1 = -1 := congrArg Prod.fst hpair
        have hzero : Work.Drive.PushDisc.arch p.1 = 0 := by
          rw [hfst]; norm_num [Work.Drive.PushDisc.arch]
        linarith [hp2pos]
      · exact Or.inr ⟨((1 : ℝ), 0), hmem_pos, by rw [h2]; exact hq₂f⟩
      · exfalso
        have hpp : fingerParam c₂ r (p.1, 0) = fingerParam c₂ r ((1 : ℝ), 0) := by
          rw [h1, hq₂f]
        have hpair := hσ₂inj ⟨habs1.trans hX', by simp⟩ hmem_pos hpp
        have hfst : p.1 = 1 := congrArg Prod.fst hpair
        have hzero : Work.Drive.PushDisc.arch p.1 = 0 := by
          rw [hfst]; norm_num [Work.Drive.PushDisc.arch]
        linarith [hp2pos]
  -- ### the isolation
  have hgcont : Continuous (fun z : M => Φ₀ (f z)) := hΦ₀fc
  have hΔcont : ContinuousOn Δ Work.Drive.PushDisc.lensK := hΔsm.continuous.continuousOn
  have hDint : Δ '' Work.Drive.PushDisc.lensKo ∩ (fun z : M => Φ₀ (f z)) '' (Set.univ : Set M)
      = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro a ⟨⟨q, hq, hqa⟩, z, -, hza⟩
    exact hΔclean z ⟨q, hq, hqa.trans hza.symm⟩
  have hVopen : IsOpen (U₁' ∪ fingerParam c₂ r '' Work.Drive.PushDisc.asymReg k X') :=
    hU₁'o.union (hW₀o X' hX' le_rfl)
  obtain ⟨δ, hδpos, hδ⟩ := exists_isolation_of_cleanRegion (fun z : M => Φ₀ (f z)) hgcont Δ
    Work.Drive.PushDisc.lensK isCompact_lensK hΔcont Work.Drive.PushDisc.lensKo
    Work.Drive.PushDisc.lensKo_subset_lensK hDint
    (U₁' ∪ fingerParam c₂ r '' Work.Drive.PushDisc.asymReg k X') hVopen hcover
  -- ### the thin neighbourhood `V`
  set V : Set (Work.Drive.Whitney.Mdl k) :=
    {ξ | ∃ a ∈ Δ '' Work.Drive.PushDisc.lensK, dist (Θg ξ) a < δ} with hVdef
  have hVo : IsOpen V := by
    rw [hVdef]
    rw [show {ξ : Work.Drive.Whitney.Mdl k |
          ∃ a ∈ Δ '' Work.Drive.PushDisc.lensK, dist (Θg ξ) a < δ}
        = ⋃ a ∈ Δ '' Work.Drive.PushDisc.lensK, Θg ⁻¹' Metric.ball a δ from by
      ext ξ
      simp [Set.mem_iUnion, Set.mem_preimage, Metric.mem_ball]]
    exact isOpen_biUnion (fun a _ => Metric.isOpen_ball.preimage hΘgsm.continuous)
  have hVD : Work.Drive.PushDisc.asymDisc k Work.Drive.PushDisc.arch ⊆ V := by
    intro ξ hξ
    obtain ⟨hx1, hy0, hxy, hu0, hv0⟩ := hξ
    show ∃ a ∈ Δ '' Work.Drive.PushDisc.lensK, dist (Θg ξ) a < δ
    refine ⟨Δ (ξ.1, ξ.2.1), ⟨(ξ.1, ξ.2.1), ⟨hx1, hy0, hxy⟩, rfl⟩, ?_⟩
    have hξeq : ξ = (ξ.1, ξ.2.1, (0 : EuclideanSpace ℝ (Fin k)),
        (0 : EuclideanSpace ℝ (Fin k))) :=
      Prod.ext rfl (Prod.ext rfl (Prod.ext hu0 hv0))
    rw [hξeq, hdisc ξ.1 ξ.2.1 (by linarith [hx1, hX']) hy0 hxy, dist_self]
    exact hδpos
  have hVthin : ∀ z : M, Φ (f z) ∈ V →
      z ∈ U₁' ∨ z ∈ fingerParam c₂ r '' Work.Drive.PushDisc.asymReg k X' := by
    intro z hz
    rw [hVdef] at hz
    obtain ⟨a, ha, hdist⟩ := hz
    have hΘΦz : Θg (Φ (f z)) = Φ₀ (f z) := by
      change Θg (Θgi (Φ₀ (f z))) = Φ₀ (f z)
      exact hrΘ (Φ₀ (f z))
    rw [hΘΦz] at hdist
    rcases hδ z ⟨a, ha, hdist⟩ with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hVW : ∀ z : M, Φ (f z) ∈ V → z ∈ W := by
    intro z hz
    rcases hVthin z hz with h | h
    · exact hU₁'W h
    · exact hW₀W h
  -- ### the chart obligation
  refine ⟨hfp, hfq, hclean, k, rfl, X', hX', Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, fingerHeight k, hh,
    fingerParam c₂ r, hσ₂row, hp₂f, hq₂f, hW₀o, hW₀W, Work.Drive.PushDisc.arch, contDiff_arch,
    hcore, hlip, ?_, ?_, ?_, ?_, hfrontier, ?_, ?_, D, (fun p => Φ (D p)), (fun p => rfl),
    hDclean, U₁', hU₁'o, hU₁'row, V, hVo, hVD, hVW, hVthin⟩
  · norm_num [Work.Drive.PushDisc.arch]
  · norm_num [Work.Drive.PushDisc.arch]
  · intro x hx
    exact arch_pos hx
  · intro x h1 _
    exact arch_neg h1
  · rw [hp₁c]
    change Θ₀ ((-1 : ℝ), 0, 0, 0) = Θ₀ (Θg ((-1 : ℝ), 0, 0, 0))
    rw [hΘg_neg]
  · rw [hq₁c]
    change Θ₀ ((1 : ℝ), 0, 0, 0) = Θ₀ (Θg ((1 : ℝ), 0, 0, 0))
    rw [hΘg_pos]

end

end Work.Drive.PushDisc
