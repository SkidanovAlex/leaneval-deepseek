import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.CollarDefs
import Submission.Work.Noncompact.CompressionTube.ShrinkDefs
import Submission.Work.Noncompact.CompressionTube.radial_ball_facts
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Noncompact.CompressionTube.exists_smooth_left_inverse_infty
import Submission.Work.Isotopy.exists_localInverse_param
import Submission.Work.Noncompact.CompressionTube.exists_collar_of_local_slabs
import Submission.Work.Noncompact.CompressionTube.collar_transverse_coordinate

set_option maxHeartbeats 1600000

/-!
# The two-sided collar along a properly embedded line

For a properly embedded smooth line `γ : ℝ → M` in an `n`-manifold `M` (`n ≥ 2`) we construct a
smooth map `Ψ : ℝ^{n-1} × ℝ → M` which is a collar around the line: its core is `γ`, it is
injective and an immersion on the tube `{‖u‖ ≤ 1}`, and it escapes to infinity in both
`s`-directions.

## Structure of the argument

1. `exists_smooth_left_inverse_infty` (proved in its own file) gives a smooth `g : M → ℝ` with
   `g (γ s) = s`.
2. `collar_transverse_coordinate` (`A`) gives a smooth `P : M → ℝ^{n-1}` with `P (γ s) = 0` such
   that `x ↦ (P x, g x)` is a local diffeomorphism at every `γ s` (the `g`-compatible triviality of
   the normal bundle of the line).
3. `collar_local_section` (`B`) is the inverse function theorem at `γ s`: it produces a smooth local
   section `σ` of `(P, g)` over a slab `{‖u‖ < r} × (s-ε, s+ε)`, with `σ (0,t) = γ t`.
4. `exists_collar_of_local_slabs` (`C`) glues the local sectors along the line.  Two local sections
   of the *same* map `(P, g)` agree on the overlap of their slabs (the set where they agree is
   clopen, and contains an axis point), so the pieces glue to a single smooth section `Ψ₀` over the
   union `U` of the slabs, and `(P, g) ∘ Ψ₀ = id`.  The tube radius of `U` is a positive lower
   semicontinuous function of `s`, so (using `exists_smooth_minorant`, `D`) one can compose `Ψ₀`
   with the radial compression of the transverse coordinate to obtain a collar on the *unit* tube:
   injectivity, immersion and the `g`-level property are inherited, and the escape property follows
   from the level property because `g` is continuous and the `K` compact.
-/


namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function Metric

noncomputable section


section ShrinkParam

variable {n : ℕ}

/-- The model with corners bridge: `MCprod n` is the self model on `ℝ^{n-1} × ℝ`. -/
theorem MCprod_eq_self :
    MCprod n = modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :=
  (modelWithCornersSelf_prod (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n - 1))) (F := ℝ)).symm

/-- The radial compression of `ℝ^{n-1}` onto the open unit ball. -/
def squashC (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) : EuclideanSpace ℝ (Fin (n - 1)) :=
  (Real.sqrt (1 + ‖u‖ ^ 2))⁻¹ • u

lemma squashC_contDiff (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞)) (squashC n) :=
  (radial_ball_facts (n - 1)).1

lemma squashC_injective (n : ℕ) : Function.Injective (squashC n) :=
  (radial_ball_facts (n - 1)).2.1

lemma squashC_norm_lt_one (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) :
    ‖squashC n u‖ < 1 := (radial_ball_facts (n - 1)).2.2.1 u

lemma squashC_zero (n : ℕ) : squashC n 0 = 0 := (radial_ball_facts (n - 1)).2.2.2.1

lemma squashC_eq_univUnitBall (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) :
    squashC n u = OpenPartialHomeomorph.univUnitBall u :=
  (OpenPartialHomeomorph.univUnitBall_apply
    (E := EuclideanSpace ℝ (Fin (n - 1))) u).symm

lemma squashC_fderiv_injective (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) :
    Function.Injective (fderiv ℝ (squashC n) u) := by
  have hsurj : Function.Surjective (fderiv ℝ (squashC n) u) :=
    (radial_ball_facts (n - 1)).2.2.2.2 u
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1)))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1))) := rfl
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj

/-- The shrinking self-map `(u,s) ↦ (ρ s / 2 • (√(1+‖u‖²))⁻¹ • u, s)`. -/
def shrinkParam (n : ℕ) (ρ : ℝ → ℝ) (p : CollarParam n) : CollarParam n :=
  ((ρ p.2 / 2) • squashC n p.1, p.2)

lemma shrinkParam_snd (n : ℕ) (ρ : ℝ → ℝ) (p : CollarParam n) :
    (shrinkParam n ρ p).2 = p.2 := rfl

lemma shrinkParam_fst (n : ℕ) (ρ : ℝ → ℝ) (p : CollarParam n) :
    (shrinkParam n ρ p).1 = (ρ p.2 / 2) • squashC n p.1 := rfl

lemma shrinkParam_contDiff (n : ℕ) {ρ : ℝ → ℝ} (hρcd : ContDiff ℝ ((⊤ : ℕ∞)) ρ) :
    ContDiff ℝ ((⊤ : ℕ∞)) (shrinkParam n ρ) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞))
      (fun p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => (ρ p.2 / 2) • squashC n p.1) :=
    ((hρcd.comp contDiff_snd).div_const 2).smul ((squashC_contDiff n).comp contDiff_fst)
  exact h1.prodMk contDiff_snd

lemma shrinkParam_contMDiff (n : ℕ) {ρ : ℝ → ℝ} (hρcd : ContDiff ℝ ((⊤ : ℕ∞)) ρ) :
    ContMDiff (MCprod n) (MCprod n) smoothOrder (shrinkParam n ρ) := by
  rw [MCprod_eq_self (n := n)]
  exact (contMDiff_iff_contDiff).2 (shrinkParam_contDiff n hρcd)

lemma shrinkParam_inv_contMDiffOn (n : ℕ) {ρ : ℝ → ℝ} (hρcd : ContDiff ℝ ((⊤ : ℕ∞)) ρ)
    (hρ : ∀ s, 0 < ρ s) :
    ContMDiffOn (MCprod n) (MCprod n) smoothOrder
      (fun q : CollarParam n =>
        (OpenPartialHomeomorph.univUnitBall.symm (((ρ q.2 / 2)⁻¹) • q.1), q.2))
      {q : CollarParam n | ‖q.1‖ < ρ q.2 / 2} := by
  rw [MCprod_eq_self (n := n)]
  rw [contMDiffOn_iff_contDiffOn]
  have hinner : ContDiffOn ℝ ((⊤ : ℕ∞))
      (fun q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => ((ρ q.2 / 2)⁻¹) • q.1)
      {q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖q.1‖ < ρ q.2 / 2} := by
    intro q hq
    have hne : ρ q.2 / 2 ≠ 0 := by have := hρ q.2; linarith
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞))
        (fun q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => (ρ q.2 / 2)⁻¹) q :=
      (((hρcd.contDiffAt).comp q contDiffAt_snd).div_const 2).inv hne
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞))
        (fun q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => q.1) q := contDiffAt_fst
    exact (h1.smul h2).contDiffWithinAt
  have hmaps : MapsTo (fun q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => ((ρ q.2 / 2)⁻¹) • q.1)
      {q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖q.1‖ < ρ q.2 / 2}
      (Metric.ball (0 : EuclideanSpace ℝ (Fin (n - 1))) 1) := by
    intro q hq
    have hpos : 0 < ρ q.2 / 2 := by have := hρ q.2; linarith
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hpos))]
    rw [inv_mul_lt_one₀ hpos]
    exact hq
  have hsymm := OpenPartialHomeomorph.contDiffOn_univUnitBall_symm
    (E := EuclideanSpace ℝ (Fin (n - 1))) (n := (⊤ : ℕ∞))
  have hcomp := hsymm.comp hinner hmaps
  exact hcomp.prodMk contDiffOn_snd

theorem exists_shrink_param {n : ℕ} (ρ : ℝ → ℝ) (hρ : ∀ s, 0 < ρ s)
    (hρcd : ContDiff ℝ ((⊤ : ℕ∞)) ρ) :
    ∃ S : CollarParam n → CollarParam n, ContMDiff (MCprod n) (MCprod n) smoothOrder S ∧
      (∀ p : CollarParam n, ‖(S p).1‖ < ρ (S p).2) ∧
      (∀ p : CollarParam n, (S p).2 = p.2) ∧
      (∀ s : ℝ, S ((0 : EuclideanSpace ℝ (Fin (n - 1))), s)
        = ((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) ∧
      Set.InjOn S {p : CollarParam n | ‖p.1‖ ≤ 1} ∧
      (∀ p : CollarParam n, Function.Injective (mfderiv (MCprod n) (MCprod n) S p)) := by
  classical
  refine ⟨shrinkParam n ρ, shrinkParam_contMDiff n hρcd, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    have hpos : 0 < ρ p.2 / 2 := by have := hρ p.2; linarith
    rw [shrinkParam_fst, shrinkParam_snd, norm_smul, Real.norm_of_nonneg (le_of_lt hpos)]
    calc (ρ p.2 / 2) * ‖squashC n p.1‖ < (ρ p.2 / 2) * 1 :=
          mul_lt_mul_of_pos_left (squashC_norm_lt_one n p.1) hpos
      _ = ρ p.2 / 2 := mul_one _
      _ < ρ p.2 := by linarith [hρ p.2]
  · intro p; exact shrinkParam_snd n ρ p
  · intro s
    rw [shrinkParam, squashC_zero, smul_zero]
  · -- injectivity on the unit tube
    intro p hp q hq hpq
    have h2 : p.2 = q.2 := by
      simpa only [shrinkParam] using congrArg Prod.snd hpq
    have h1 : p.1 = q.1 := by
      refine squashC_injective n ?_
      have h3 : (ρ p.2 / 2) • squashC n p.1 = (ρ q.2 / 2) • squashC n q.1 := by
        simpa only [shrinkParam] using congrArg Prod.fst hpq
      rw [h2] at h3
      exact smul_right_injective (EuclideanSpace ℝ (Fin (n - 1)))
        (ne_of_gt (by have := hρ q.2; linarith)) h3
    exact Prod.ext h1 h2
  · -- the derivative is injective: the map is a local diffeomorphism
    intro p
    have hΦ : IsLocalDiffeomorphAt (MCprod n) (MCprod n) smoothOrder (shrinkParam n ρ) p := by
      let Φ : PartialDiffeomorph (MCprod n) (MCprod n) (CollarParam n) (CollarParam n) smoothOrder :=
        { toPartialEquiv :=
            { toFun := shrinkParam n ρ
              invFun := fun q : CollarParam n =>
                (OpenPartialHomeomorph.univUnitBall.symm (((ρ q.2 / 2)⁻¹) • q.1), q.2)
              source := univ
              target := {q : CollarParam n | ‖q.1‖ < ρ q.2 / 2}
              map_source' := by
                intro x _
                have hpos : 0 < ρ x.2 / 2 := by have := hρ x.2; linarith
                show ‖((ρ x.2 / 2) • squashC n x.1)‖ < ρ x.2 / 2
                rw [norm_smul, Real.norm_of_nonneg (le_of_lt hpos)]
                calc (ρ x.2 / 2) * ‖squashC n x.1‖ < (ρ x.2 / 2) * 1 :=
                      mul_lt_mul_of_pos_left (squashC_norm_lt_one n x.1) hpos
                  _ = ρ x.2 / 2 := mul_one _
              map_target' := fun x _ => Set.mem_univ x
              left_inv' := by
                intro x _
                have hpos : 0 < ρ x.2 / 2 := by have := hρ x.2; linarith
                have hmem : squashC n x.1 ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n - 1))) 1 :=
                  mem_ball_zero_iff.mpr (squashC_norm_lt_one n x.1)
                show (OpenPartialHomeomorph.univUnitBall.symm
                  (((ρ x.2 / 2)⁻¹) • ((ρ x.2 / 2) • squashC n x.1)), x.2) = x
                rw [inv_smul_smul₀ (ne_of_gt hpos)]
                refine Prod.ext ?_ rfl
                show OpenPartialHomeomorph.univUnitBall.symm (squashC n x.1) = x.1
                rw [squashC_eq_univUnitBall n x.1]
                exact OpenPartialHomeomorph.left_inv OpenPartialHomeomorph.univUnitBall
                  (Set.mem_univ x.1)
              right_inv' := by
                intro x hx
                have hpos : 0 < ρ x.2 / 2 := by have := hρ x.2; linarith
                have hmem : ((ρ x.2 / 2)⁻¹) • x.1
                    ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (n - 1))) 1 := by
                  rw [mem_ball_zero_iff, norm_smul,
                    Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hpos)), inv_mul_lt_one₀ hpos]
                  exact hx
                show (((ρ x.2 / 2)) • squashC n (OpenPartialHomeomorph.univUnitBall.symm
                  (((ρ x.2 / 2)⁻¹) • x.1)), x.2) = x
                refine Prod.ext ?_ rfl
                show ((ρ x.2 / 2)) • OpenPartialHomeomorph.univUnitBall
                  (OpenPartialHomeomorph.univUnitBall.symm (((ρ x.2 / 2)⁻¹) • x.1)) = x.1
                rw [OpenPartialHomeomorph.right_inv OpenPartialHomeomorph.univUnitBall hmem]
                simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
              }
          open_source := isOpen_univ
          open_target := isOpen_lt continuous_fst.norm
            ((hρcd.continuous.comp continuous_snd).div_const 2)
          contMDiffOn_toFun := (shrinkParam_contMDiff n hρcd).contMDiffOn
          contMDiffOn_invFun := shrinkParam_inv_contMDiffOn n hρcd hρ }
      exact PartialDiffeomorph.isLocalDiffeomorphAt (MCprod n) (MCprod n) smoothOrder Φ
        (Set.mem_univ p)
    have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
    rw [← IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hΦ hn]
    exact (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv hΦ hn).injective

end ShrinkParam



/-! ## The four building blocks of the collar construction -/

/-- **D.**  A positive lower semicontinuous function on `ℝ` has a smooth positive minorant. -/
theorem exists_smooth_minorant {ρ : ℝ → ℝ} (hpos : ∀ s : ℝ, 0 < ρ s)
    (hlsc : LowerSemicontinuous ρ) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r ∧ (∀ s : ℝ, 0 < r s) ∧
      ∀ s : ℝ, r s ≤ ρ s := by
  have hloc : ∀ x : ℝ, ∃ c : ℝ, ∀ᶠ y in 𝓝 x, c ∈ Set.Ioo (0 : ℝ) (ρ y) := fun x => by
    refine ⟨ρ x / 2, ?_⟩
    have h1 : ρ x / 2 < ρ x := by linarith [hpos x]
    have hpos' : 0 < ρ x / 2 := by linarith [hpos x]
    exact ((lowerSemicontinuous_iff.mp hlsc x) (ρ x / 2) h1).mono
      (fun y hy => ⟨hpos', hy⟩)
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const (I := 𝓘(ℝ, ℝ)) (M := ℝ)
    (F := ℝ) (n := (⊤ : ℕ∞)) (t := fun y => Set.Ioo (0 : ℝ) (ρ y))
    (fun y => convex_Ioo 0 (ρ y)) hloc
  exact ⟨fun s => g s, by
      have h := g.contMDiff
      rw [contMDiff_iff_contDiff] at h
      simpa using h,
    fun s => (hg s).1, fun s => (hg s).2.le⟩

/-- **B.**  Local sections of `(P, g)` over slabs: the inverse function theorem at each point of
the line. -/
theorem collar_local_section {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {g : M → ℝ} {P : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hg : ContMDiff (MC n) MCreal smoothOrder g)
    (hP : ContMDiff (MC n) (MC (n - 1)) smoothOrder P)
    (hcore : ∀ s : ℝ, P (γ s) = 0 ∧ g (γ s) = s)
    (hη : ∀ s : ℝ, ∀ v : TangentSpace (MC n) (γ s),
      mfderiv (MC n) (MC (n - 1)) P (γ s) v = 0 →
      mfderiv (MC n) MCreal g (γ s) v = 0 → v = 0)
    (s : ℝ) :
    ∃ (r ε : ℝ) (σ : CollarParam n → M), 0 < r ∧ 0 < ε ∧
      ContMDiffOn (MCprod n) (MC n) smoothOrder σ
        {p : CollarParam n | ‖p.1‖ < r ∧ |p.2 - s| < ε} ∧
      (∀ t : ℝ, |t - s| < ε → σ ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = γ t) ∧
      (∀ p : CollarParam n, ‖p.1‖ < r → |p.2 - s| < ε → (P (σ p), g (σ p)) = p) := by
  classical
  have hγcont : Continuous γ := hγ.continuous
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (γ s) with hcdef
  have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (γ s)
  have hcγ : γ s ∈ c.source := mem_chart_source _ (γ s)
  have hz0t : c (γ s) ∈ c.target := c.map_source hcγ
  have hcle : c.symm (c (γ s)) = γ s := c.left_inv hcγ
  set eta : M → CollarParam n := (fun x : M => (P x, g x)) with hetadef
  set etahat : EuclideanSpace ℝ (Fin n) → CollarParam n := eta ∘ c.symm with hetahat_def
  let w : TangentSpace (MC n) (c (γ s)) →L[ℝ] TangentSpace (MC n) (γ s) :=
    mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s))
  have hcsymm : ContMDiffOn (MC n) (MC n) smoothOrder
      (c.symm : EuclideanSpace ℝ (Fin n) → M) c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hc
  -- componentwise smoothness of the chart expression
  have hP1 : ContMDiffOn (MC n) (MC (n - 1)) smoothOrder
      (fun z : EuclideanSpace ℝ (Fin n) => P (c.symm z)) c.target :=
    hP.contMDiffOn.comp hcsymm (fun z _ => Set.mem_preimage.mpr (Set.mem_univ (c.symm z)))
  have hg1 : ContMDiffOn (MC n) MCreal smoothOrder
      (fun z : EuclideanSpace ℝ (Fin n) => g (c.symm z)) c.target :=
    hg.contMDiffOn.comp hcsymm (fun z _ => Set.mem_preimage.mpr (Set.mem_univ (c.symm z)))
  have hP1' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin n) => P (c.symm z)) c.target :=
    contMDiffOn_iff_contDiffOn.mp hP1
  have hg1' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin n) => g (c.symm z)) c.target :=
    contMDiffOn_iff_contDiffOn.mp hg1
  have hetahat_cd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) etahat c.target := hP1'.prodMk hg1'
  have hetahat_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) etahat (c (γ s)) :=
    hetahat_cd.contDiffAt (c.open_target.mem_nhds hz0t)
  -- injectivity of the chart's inverse differential
  have hcsymm_inj : Function.Injective w := by
    let Φ : PartialDiffeomorph (MC n) (MC n) (EuclideanSpace ℝ (Fin n)) M smoothOrder :=
      { toPartialEquiv := c.symm.toPartialEquiv
        open_source := c.open_target
        open_target := c.open_source
        contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas hc
        contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas hc }
    have hld : IsLocalDiffeomorphAt (MC n) (MC n) smoothOrder
        (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s)) :=
      PartialDiffeomorph.isLocalDiffeomorphAt (I := MC n) (J := MC n) (n := smoothOrder)
        (φ := Φ) (x := c (γ s)) (hx := hz0t)
    have hn : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
    have hcoe := IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hld hn
    rw [show w = mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s))
      from rfl, ← hcoe]
    exact (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv hld hn).injective
  -- componentwise chain rule
  have h1 : MDifferentiableAt (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s)) :=
    (hcsymm.contMDiffAt (c.open_target.mem_nhds hz0t)).mdifferentiableAt (by simp [smoothOrder])
  have h2 : MDifferentiableAt (MC n) (MC (n - 1)) P (c.symm (c (γ s))) := by
    rw [hcle]; exact hP.mdifferentiableAt (by simp)
  have h3 : MDifferentiableAt (MC n) MCreal g (c.symm (c (γ s))) := by
    rw [hcle]; exact hg.mdifferentiableAt (by simp)
  have hchainP : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => P (c.symm z))
      (mfderiv (MC n) (MC (n - 1)) P (c.symm (c (γ s))) ∘SL
        mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s)))
      (c (γ s)) :=
    ((h2.hasMFDerivAt.comp (c (γ s)) h1.hasMFDerivAt)).hasFDerivAt
  have hchaing : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => g (c.symm z))
      (mfderiv (MC n) MCreal g (c.symm (c (γ s))) ∘SL
        mfderiv (MC n) (MC n) (c.symm : EuclideanSpace ℝ (Fin n) → M) (c (γ s)))
      (c (γ s)) :=
    ((h3.hasMFDerivAt.comp (c (γ s)) h1.hasMFDerivAt)).hasFDerivAt
  have hderiv_inj : Function.Injective (fderiv ℝ etahat (c (γ s))) := by
    have hpair := hchainP.prodMk hchaing
    have hD : fderiv ℝ etahat (c (γ s)) =
        (mfderiv (MC n) (MC (n - 1)) P (c.symm (c (γ s))) ∘SL w).prod
          (mfderiv (MC n) MCreal g (c.symm (c (γ s))) ∘SL w) := hpair.fderiv
    rw [hcle] at hD
    have hTinj : Function.Injective
        ((mfderiv (MC n) (MC (n - 1)) P (γ s) ∘SL w).prod
          (mfderiv (MC n) MCreal g (γ s) ∘SL w)) := by
      intro y y' hyy'
      have h1 : (mfderiv (MC n) (MC (n - 1)) P (γ s) ∘SL w) y
          = (mfderiv (MC n) (MC (n - 1)) P (γ s) ∘SL w) y' := by
        rw [ContinuousLinearMap.prod_apply] at hyy'
        simpa using congrArg Prod.fst hyy'
      have h2 : (mfderiv (MC n) MCreal g (γ s) ∘SL w) y
          = (mfderiv (MC n) MCreal g (γ s) ∘SL w) y' := by
        rw [ContinuousLinearMap.prod_apply] at hyy'
        simpa using congrArg Prod.snd hyy'
      have h3 : mfderiv (MC n) (MC (n - 1)) P (γ s) (w (y - y')) = 0 := by
        have hA0 : (mfderiv (MC n) (MC (n - 1)) P (γ s) ∘SL w) (y - y') = 0 := by
          rw [map_sub, h1, sub_self]
        simpa only [ContinuousLinearMap.comp_apply] using hA0
      have h4 : mfderiv (MC n) MCreal g (γ s) (w (y - y')) = 0 := by
        have hB0 : (mfderiv (MC n) MCreal g (γ s) ∘SL w) (y - y') = 0 := by
          rw [map_sub, h2, sub_self]
        simpa only [ContinuousLinearMap.comp_apply] using hB0
      have h5 : w (y - y') = 0 := hη s (w (y - y')) h3 h4
      have h6 : y - y' = 0 := hcsymm_inj (by simpa using h5)
      exact sub_eq_zero.mp h6
    rw [hD]
    exact hTinj
  -- the derivative as a linear equivalence and the partial homeomorphism
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (CollarParam n) := by
    simp only [CollarParam, Module.finrank_prod, finrank_euclideanSpace, Module.finrank_self,
      Fintype.card_fin]
    omega
  obtain ⟨L, hL⟩ := exists_continuousLinearEquiv_of_injective hdim
    (fderiv ℝ etahat (c (γ s))) hderiv_inj
  have hL' : HasFDerivAt etahat (L : EuclideanSpace ℝ (Fin n) →L[ℝ] CollarParam n) (c (γ s)) :=
    HasFDerivAt.congr_fderiv (hetahat_at.differentiableAt (by simp)).hasFDerivAt hL.symm
  have hn0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  set φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (CollarParam n) :=
    hetahat_at.toOpenPartialHomeomorph etahat hL' hn0 with hφdef
  have hφcoe : (φ : EuclideanSpace ℝ (Fin n) → CollarParam n) = etahat :=
    ContDiffAt.toOpenPartialHomeomorph_coe hetahat_at hL' hn0
  have hz0φ : c (γ s) ∈ φ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hetahat_at hL' hn0
  have h0sφ : etahat (c (γ s)) ∈ φ.target :=
    ContDiffAt.image_mem_toOpenPartialHomeomorph_target hetahat_at hL' hn0
  have hz0s : etahat (c (γ s)) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) := by
    show eta (c.symm (c (γ s))) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), s)
    rw [c.left_inv hcγ, hetadef]
    exact Prod.ext (hcore s).1 (hcore s).2
  -- the parametric inverse function theorem
  set G : ℝ × EuclideanSpace ℝ (Fin n) → CollarParam n := fun sz => etahat sz.2 with hGdef
  have hGcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (Set.univ ×ˢ c.target) := by
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun sz : ℝ × EuclideanSpace ℝ (Fin n) => sz.2) (Set.univ ×ˢ c.target) := contDiffOn_snd
    exact hetahat_cd.comp h2 (fun sz hsz => hsz.2)
  have hGinj : Function.Injective
      (fun v : EuclideanSpace ℝ (Fin n) => fderiv ℝ G ((0 : ℝ), c (γ s)) (0, v)) := by
    have hfd2 : fderiv ℝ G ((0 : ℝ), c (γ s)) =
        (fderiv ℝ etahat (c (γ s))).comp
          (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) := by
      have h1 : HasFDerivAt (fun sz : ℝ × EuclideanSpace ℝ (Fin n) => sz.2)
          (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) ((0 : ℝ), c (γ s)) :=
        hasFDerivAt_snd
      have h2 : HasFDerivAt etahat (fderiv ℝ etahat (c (γ s)))
          ((fun sz : ℝ × EuclideanSpace ℝ (Fin n) => sz.2) ((0 : ℝ), c (γ s))) :=
        (hetahat_at.differentiableAt (by simp)).hasFDerivAt
      exact (h2.comp ((0 : ℝ), c (γ s)) h1).fderiv
    intro v v' hvv
    rw [hfd2] at hvv
    simp only [ContinuousLinearMap.comp_apply] at hvv
    exact hderiv_inj (by simpa using hvv)
  obtain ⟨O, U, W, h, hOo, h0O, hUo, hz0U, hWo, hGs0W, hV, huncurry, hGmaps, hleft⟩ :=
    Work.Isotopy.exists_localInverse_param (E := EuclideanSpace ℝ (Fin n))
      (F := CollarParam n) G (Set.univ ×ˢ c.target) (isOpen_univ.prod c.open_target)
      (0 : ℝ) (c (γ s)) ⟨trivial, hz0t⟩ hGcd c.target c.open_target hz0t hGinj
  have hhsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h 0) W := by
    have hinner : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w' : CollarParam n => ((0 : ℝ), w')) W := contDiffOn_const.prodMk contDiffOn_id
    have hres := huncurry.comp hinner (fun w' hw' => ⟨h0O, hw'⟩)
    have hfun : (Function.uncurry h ∘ fun w' : CollarParam n => ((0 : ℝ), w'))
        = fun w' => h 0 w' := by
      funext w'; rfl
    rw [hfun] at hres
    exact hres
  have hz0φsymm : φ.symm (etahat (c (γ s))) = c (γ s) := by
    have h1 : φ (c (γ s)) = etahat (c (γ s)) := by rw [hφcoe]
    rw [← h1]
    exact φ.left_inv hz0φ
  have hagree : ∀ p : CollarParam n, p ∈ φ.target → φ.symm p ∈ U → φ.symm p = h 0 p := by
    intro p hp hUp
    have h1 : G (0, φ.symm p) = p := by
      show etahat (φ.symm p) = p
      rw [← hφcoe]
      exact φ.right_inv hp
    have h3 := hleft 0 h0O (φ.symm p) hUp
    rw [h1] at h3
    exact h3.symm
  have hφsymm_cont : ContinuousAt (φ.symm) (etahat (c (γ s))) :=
    (φ.continuousOn_invFun).continuousAt (φ.open_target.mem_nhds h0sφ)
  have hUmem : φ.symm ⁻¹' U ∈ 𝓝 (etahat (c (γ s))) := by
    refine hφsymm_cont.preimage_mem_nhds (hUo.mem_nhds ?_)
    rw [hz0φsymm]
    exact hz0U
  have hS : {p : CollarParam n | p ∈ φ.target ∧ φ.symm p ∈ U} ∈ 𝓝 (etahat (c (γ s))) :=
    Filter.inter_mem (φ.open_target.mem_nhds h0sφ) hUmem
  have hbox : ({p : CollarParam n | p ∈ φ.target ∧ φ.symm p ∈ U} ∩ W) ∈ 𝓝 (etahat (c (γ s))) :=
    Filter.inter_mem hS (hWo.mem_nhds hGs0W)
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hbox
  have hcore_nhds : (fun t : ℝ => c (γ t)) ⁻¹' φ.source ∈ 𝓝 s :=
    ((c.continuousAt hcγ).comp hγcont.continuousAt) (φ.open_source.mem_nhds hz0φ)
  have hcsrc_nhds : γ ⁻¹' c.source ∈ 𝓝 s :=
    hγcont.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hcγ)
  obtain ⟨ε0, hε0pos, hε0sub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hcore_nhds hcsrc_nhds)
  refine ⟨ρ / 2, min (ρ / 2) ε0, fun p => c.symm (φ.symm p), by linarith,
    lt_min (by linarith) hε0pos, ?_, ?_, ?_⟩
  · -- smoothness on the slab
    have hslab : {p : CollarParam n | ‖p.1‖ < ρ / 2 ∧ |p.2 - s| < min (ρ / 2) ε0}
        ⊆ {p : CollarParam n | p ∈ φ.target ∧ φ.symm p ∈ U} ∩ W := by
      intro p hp
      have hdist : dist p (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) < ρ := by
        rw [Prod.dist_eq]
        refine max_lt ?_ ?_
        · rw [dist_eq_norm, sub_zero]; linarith [hp.1]
        · rw [Real.dist_eq]; linarith [hp.2, min_le_left (ρ / 2) ε0]
      exact hρsub (by rw [hz0s]; exact hdist)
    have hsm1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ.symm)
        ({p : CollarParam n | p ∈ φ.target ∧ φ.symm p ∈ U} ∩ W) := by
      refine (hhsm.mono Set.inter_subset_right).congr ?_
      intro p hp
      exact hagree p hp.1.1 hp.1.2
    have hsm2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ) (MC n) smoothOrder
        (φ.symm) ({p : CollarParam n | p ∈ φ.target ∧ φ.symm p ∈ U} ∩ W) :=
      contMDiffOn_iff_contDiffOn.mpr hsm1
    have hsm3 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ) (MC n) smoothOrder
        (φ.symm) {p : CollarParam n | ‖p.1‖ < ρ / 2 ∧ |p.2 - s| < min (ρ / 2) ε0} :=
      hsm2.mono hslab
    have hmaps : ∀ p ∈ {p : CollarParam n | ‖p.1‖ < ρ / 2 ∧ |p.2 - s| < min (ρ / 2) ε0},
        φ.symm p ∈ c.target := by
      intro p hp
      have hp' := hslab hp
      have h1 : h 0 p ∈ c.target := hV 0 h0O p hp'.2
      rw [hagree p hp'.1.1 hp'.1.2]
      exact h1
    have hcomp := hcsymm.comp hsm3 hmaps
    rw [← MCprod_eq_self (n := n)] at hcomp
    exact hcomp
  · -- the core is `γ`
    intro t ht
    have hmem : dist t s < ε0 := by
      rw [Real.dist_eq]
      exact lt_of_lt_of_le ht (min_le_right (ρ / 2) ε0)
    have hsrc : γ t ∈ c.source := (hε0sub hmem).2
    have hφsrc : c (γ t) ∈ φ.source := (hε0sub hmem).1
    have hetacγ : etahat (c (γ t)) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) := by
      show eta (c.symm (c (γ t))) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)
      rw [c.left_inv hsrc]
      rw [hetadef]
      exact Prod.ext (hcore t).1 (hcore t).2
    have hsymm_eq : φ.symm ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = c (γ t) := by
      have h1 : φ (c (γ t)) = ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) := by
        rw [hφcoe]
        exact hetacγ
      have h2 : φ.symm (φ (c (γ t))) = c (γ t) := φ.left_inv hφsrc
      rwa [h1] at h2
    show c.symm (φ.symm ((0 : EuclideanSpace ℝ (Fin (n - 1))), t)) = γ t
    rw [hsymm_eq]
    exact c.left_inv hsrc
  · -- the section property
    intro p hp1 hp2
    have hd : dist p (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) < ρ := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [dist_eq_norm, sub_zero]; linarith [hp1, hρpos]
      · rw [Real.dist_eq]; linarith [hp2, min_le_left (ρ / 2) ε0, hρpos]
    have hp' := hρsub (by rw [hz0s]; exact hd)
    have h1 : etahat (φ.symm p) = p := by
      rw [← hφcoe]
      exact φ.right_inv hp'.1.1
    simpa only [hetahat_def, hetadef, Function.comp_def] using h1

/-! ## The target theorem -/

theorem exists_collar_twosided {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M] [ConnectedSpace M] {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (hinj : Function.Injective γ) (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv MCreal (MC n) γ s)) : ∃ Ψ : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M, ContMDiff (MCprod n) (MC n) smoothOrder Ψ ∧ (∀ s : ℝ, Ψ ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) = γ s) ∧ Set.InjOn Ψ {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ ≤ 1} ∧ (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → Function.Injective (mfderiv (MCprod n) (MC n) Ψ p)) ∧ (∀ K : Set M, IsCompact K → ∃ S : ℝ, ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → S ≤ |p.2| → Ψ p ∉ K) := by
  classical
  obtain ⟨g, hgsm, hgcore⟩ := exists_smooth_left_inverse_infty hn hγ hinj hprop himm
  obtain ⟨P, hPsm, hP0, hη⟩ := collar_transverse_coordinate hn hγ hinj hprop himm hgsm hgcore
  have hcore : ∀ s : ℝ, P (γ s) = 0 ∧ g (γ s) = s := fun s => ⟨hP0 s, hgcore s⟩
  have hloc : ∀ s : ℝ, ∃ (r ε : ℝ) (σ : CollarParam n → M), 0 < r ∧ 0 < ε ∧
      ContMDiffOn (MCprod n) (MC n) smoothOrder σ
        {p : CollarParam n | ‖p.1‖ < r ∧ |p.2 - s| < ε} ∧
      (∀ t : ℝ, |t - s| < ε → σ ((0 : EuclideanSpace ℝ (Fin (n - 1))), t) = γ t) ∧
      (∀ p : CollarParam n, ‖p.1‖ < r → |p.2 - s| < ε → (P (σ p), g (σ p)) = p) :=
    fun s => collar_local_section hn hγ hgsm hPsm hcore hη s
  exact exists_collar_of_local_slabs hn hPsm hgsm hcore hloc

end

end Work.Noncompact.CompressionTube
