import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.radial_ball_facts
import Submission.Work.Noncompact.CompressionTube.smooth_minorant
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion

/-!
# Shrinking an embedded tube into a prescribed neighbourhood of its core

Let `M` be a smooth `n`-manifold (`n ≥ 2`), `γ : ℝ → M` a properly embedded line and
`Ψ : ℝ^{n-1} × ℝ → M` an embedded tube along `γ` (its core is `γ`, it is an immersion and it
escapes to infinity in both `s`-directions).  Given a closed set `C` disjoint from `γ(ℝ)` and an
open set `U ⊇ γ(ℝ)`, this file constructs a *shrunk* tube `T` with the same properties as `Ψ`
whose image lies in `U` and misses `C` on the unit tube.

The construction is `T = Ψ ∘ shrink n R`, where `R : ℝ → ℝ` is a smooth positive function which is
a minorant of `min d 1`; here `d` is the distance, in the parameter space `ℝ^{n-1} × ℝ`, from the
axis `{(0,s)}` to the complement of the open set `A = Ψ ⁻¹' (U \ C)` containing the axis.  Since
`A` is open and contains the axis, `d` is continuous and positive, so a smooth positive minorant
`R` exists (`Work.Noncompact.CompressionTube.smooth_minorant`); the map
`shrink n R (u,s) = (R s • (√(1+‖u‖²))⁻¹ • u, s)` then maps the parameter space into the tube
`{‖u‖ < R s}` of radius `R`, hence (by `R ≤ d`) into `A`, hence into `U \ C`, and its transverse
coordinate stays in the unit ball because `R ≤ 1` (which is what transfers the escaping property
of `Ψ`).

## Main results

* `shrink`, `shrinkInv`: the shrinking self-map of the parameter space and its inverse,
* `shrink_contMDiff`, `shrink_injective`, `shrink_mfderiv_injective`, `shrink_fst_norm_lt`:
  the properties of the shrinking map,
* `exists_shrunk_tube`: the requested statement.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function Metric

noncomputable section

variable {n : ℕ}

/-- The model with corners bridge: `MCprod n` is the self model on `ℝ^{n-1} × ℝ`. -/
theorem MCprod_eq_self' (n : ℕ) :
    MCprod n = modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :=
  (modelWithCornersSelf_prod (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n - 1))) (F := ℝ)).symm

/-! ### The radial compression of `ℝ^{n-1}` -/

/-- The radial compression `u ↦ (√(1+‖u‖²))⁻¹ • u` of `ℝ^{n-1}` onto the open unit ball. -/
def compress (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) : EuclideanSpace ℝ (Fin (n - 1)) :=
  (Real.sqrt (1 + ‖u‖ ^ 2))⁻¹ • u

lemma compress_eq_univUnitBall (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) :
    compress n u = OpenPartialHomeomorph.univUnitBall u :=
  (OpenPartialHomeomorph.univUnitBall_apply (E := EuclideanSpace ℝ (Fin (n - 1))) u).symm

lemma compress_contDiff (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (compress n) :=
  (radial_ball_facts (n - 1)).1

lemma compress_injective (n : ℕ) : Function.Injective (compress n) :=
  (radial_ball_facts (n - 1)).2.1

lemma compress_norm_lt_one (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) :
    ‖compress n u‖ < 1 :=
  (radial_ball_facts (n - 1)).2.2.1 u

lemma compress_zero (n : ℕ) : compress n 0 = 0 :=
  (radial_ball_facts (n - 1)).2.2.2.1

/-! ### The shrinking self-map of the parameter space -/

/-- The shrinking self-map `(u,s) ↦ (ρ s • compress u, s)` of the parameter space. -/
def shrink (n : ℕ) (ρ : ℝ → ℝ) (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    EuclideanSpace ℝ (Fin (n - 1)) × ℝ :=
  (ρ p.2 • compress n p.1, p.2)

@[simp] lemma shrink_apply (n : ℕ) (ρ : ℝ → ℝ)
    (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    shrink n ρ p = (ρ p.2 • compress n p.1, p.2) := rfl

@[simp] lemma shrink_fst (n : ℕ) (ρ : ℝ → ℝ)
    (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    (shrink n ρ p).1 = ρ p.2 • compress n p.1 := rfl

@[simp] lemma shrink_snd (n : ℕ) (ρ : ℝ → ℝ)
    (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    (shrink n ρ p).2 = p.2 := rfl

/-- The inverse of the shrinking map, built from the inverse radial compression. -/
def shrinkInv (n : ℕ) (ρ : ℝ → ℝ) (q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    EuclideanSpace ℝ (Fin (n - 1)) × ℝ :=
  (OpenPartialHomeomorph.univUnitBall.symm ((ρ q.2)⁻¹ • q.1), q.2)

lemma shrinkInv_shrink (n : ℕ) {ρ : ℝ → ℝ} (hρ : ∀ s, 0 < ρ s)
    (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    shrinkInv n ρ (shrink n ρ p) = p := by
  have hne : ρ p.2 ≠ 0 := ne_of_gt (hρ p.2)
  have hfst : (ρ (shrink n ρ p).2)⁻¹ • (shrink n ρ p).1 = compress n p.1 := by
    rw [shrink_snd, shrink_fst, inv_smul_smul₀ hne]
  refine Prod.ext ?_ rfl
  show OpenPartialHomeomorph.univUnitBall.symm
      ((ρ (shrink n ρ p).2)⁻¹ • (shrink n ρ p).1) = p.1
  rw [hfst, compress_eq_univUnitBall]
  exact OpenPartialHomeomorph.left_inv _ (Set.mem_univ (p.1))

lemma shrink_contDiff (n : ℕ) {ρ : ℝ → ℝ}
    (hρcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (shrink n ρ) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => ρ p.2 • compress n p.1) :=
    (hρcd.comp contDiff_snd).smul ((compress_contDiff n).comp contDiff_fst)
  exact h1.prodMk contDiff_snd

lemma shrink_contMDiff (n : ℕ) {ρ : ℝ → ℝ}
    (hρcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) :
    ContMDiff (MCprod n) (MCprod n) smoothOrder (shrink n ρ) := by
  rw [MCprod_eq_self' n]
  exact (contMDiff_iff_contDiff).2 (by simpa [smoothOrder] using shrink_contDiff n hρcd)

lemma shrink_fst_norm_lt (n : ℕ) {ρ : ℝ → ℝ} (hρ : ∀ s, 0 < ρ s)
    (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    ‖(shrink n ρ p).1‖ < ρ p.2 := by
  rw [shrink_fst, norm_smul, Real.norm_eq_abs, abs_of_pos (hρ p.2)]
  calc ρ p.2 * ‖compress n p.1‖ < ρ p.2 * 1 :=
        mul_lt_mul_of_pos_left (compress_norm_lt_one n p.1) (hρ p.2)
    _ = ρ p.2 := mul_one _

lemma shrink_core (n : ℕ) (ρ : ℝ → ℝ) (s : ℝ) :
    shrink n ρ ((0 : EuclideanSpace ℝ (Fin (n - 1))), s)
      = ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) := by
  refine Prod.ext ?_ rfl
  simp [shrink, compress_zero]

lemma shrink_injective (n : ℕ) {ρ : ℝ → ℝ} (hρ : ∀ s, 0 < ρ s) :
    Function.Injective (shrink n ρ) := by
  intro p q hpq
  have h2 : p.2 = q.2 := by simpa using congrArg Prod.snd hpq
  have h3 : ρ p.2 • compress n p.1 = ρ q.2 • compress n q.1 := by
    simpa using congrArg Prod.fst hpq
  have h1 : p.1 = q.1 := by
    rw [h2] at h3
    have h4 : compress n p.1 = compress n q.1 := by
      have h5 : (ρ q.2)⁻¹ • (ρ q.2 • compress n p.1)
          = (ρ q.2)⁻¹ • (ρ q.2 • compress n q.1) := by rw [h3]
      rw [smul_smul, smul_smul, inv_mul_cancel₀ (ne_of_gt (hρ q.2)), one_smul,
        one_smul] at h5
      exact h5
    exact compress_injective n h4
  exact Prod.ext h1 h2

lemma shrinkInv_contDiffAt (n : ℕ) {ρ : ℝ → ℝ}
    (hρcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hρ : ∀ s, 0 < ρ s)
    (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (shrinkInv n ρ) (shrink n ρ p) := by
  have hne : ρ (shrink n ρ p).2 ≠ 0 := ne_of_gt (hρ (shrink n ρ p).2)
  have hinner : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => (ρ q.2)⁻¹ • q.1) (shrink n ρ p) :=
    (((hρcd.contDiffAt (x := (shrink n ρ p).2)).comp (shrink n ρ p) contDiffAt_snd).inv
      hne).smul contDiffAt_fst
  have hval : (ρ (shrink n ρ p).2)⁻¹ • (shrink n ρ p).1 = compress n p.1 := by
    rw [shrink_snd, shrink_fst, inv_smul_smul₀ (ne_of_gt (hρ p.2))]
  have houter : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (OpenPartialHomeomorph.univUnitBall.symm)
      ((fun q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => (ρ q.2)⁻¹ • q.1) (shrink n ρ p)) := by
    show ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (OpenPartialHomeomorph.univUnitBall.symm) ((ρ (shrink n ρ p).2)⁻¹ • (shrink n ρ p).1)
    rw [hval]
    exact (OpenPartialHomeomorph.contDiffOn_univUnitBall_symm
        (E := EuclideanSpace ℝ (Fin (n - 1))) (n := (⊤ : ℕ∞))).contDiffAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (compress_norm_lt_one n p.1)))
  have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      ((fun q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ => (ρ q.2)⁻¹ • q.1) |> fun g =>
        OpenPartialHomeomorph.univUnitBall.symm ∘ g)
      (shrink n ρ p) :=
    houter.comp (shrink n ρ p) hinner
  exact hcomp.prodMk contDiffAt_snd

lemma shrink_mfderiv_injective (n : ℕ) {ρ : ℝ → ℝ}
    (hρcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hρ : ∀ s, 0 < ρ s)
    (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    Function.Injective (mfderiv (MCprod n) (MCprod n) (shrink n ρ) p) := by
  have hS : ContMDiffAt (MCprod n) (MCprod n) smoothOrder (shrink n ρ) p :=
    (shrink_contMDiff n hρcd).contMDiffAt
  have hSi : ContMDiffAt (MCprod n) (MCprod n) smoothOrder (shrinkInv n ρ) (shrink n ρ p) := by
    rw [MCprod_eq_self' n]
    simpa [smoothOrder] using (shrinkInv_contDiffAt n hρcd hρ p).contMDiffAt
  have hchain : mfderiv (MCprod n) (MCprod n) (shrinkInv n ρ ∘ shrink n ρ) p
      = (mfderiv (MCprod n) (MCprod n) (shrinkInv n ρ) (shrink n ρ p)).comp
        (mfderiv (MCprod n) (MCprod n) (shrink n ρ) p) :=
    mfderiv_comp (I := MCprod n) (I' := MCprod n) (I'' := MCprod n) (x := p)
      (f := shrink n ρ) (g := shrinkInv n ρ)
      (hSi.mdifferentiableAt (by simp)) (hS.mdifferentiableAt (by simp))
  rw [show shrinkInv n ρ ∘ shrink n ρ = id from funext (shrinkInv_shrink n hρ),
    mfderiv_id] at hchain
  intro v w hvw
  have hv : v = (mfderiv (MCprod n) (MCprod n) (shrinkInv n ρ) (shrink n ρ p))
      ((mfderiv (MCprod n) (MCprod n) (shrink n ρ) p) v) := by
    have h := congrArg (fun L => L v) hchain
    simp only [ContinuousLinearMap.id_apply] at h
    exact h
  have hw : w = (mfderiv (MCprod n) (MCprod n) (shrinkInv n ρ) (shrink n ρ p))
      ((mfderiv (MCprod n) (MCprod n) (shrink n ρ) p) w) := by
    have h := congrArg (fun L => L w) hchain
    simp only [ContinuousLinearMap.id_apply] at h
    exact h
  rw [hvw] at hv
  exact hv.trans hw.symm

/-! ### The main theorem -/

/-- **The shrunk tube.**  Given an embedded tube `Ψ` along `γ` escaping to infinity, a closed set
`C` disjoint from `γ(ℝ)` and an open set `U ⊇ γ(ℝ)`, there is a shrunk tube `T` with the same
properties whose image lies in `U` and misses `C` on the unit tube. -/
theorem exists_shrunk_tube {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] [ConnectedSpace M]
    {γ : ℝ → M} {Ψ : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M}
    (hΨ : ContMDiff (MCprod n) (MC n) smoothOrder Ψ)
    (hemb : Topology.IsEmbedding Ψ)
    (himm : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
      Function.Injective (mfderiv (MCprod n) (MC n) Ψ p))
    (hcore : ∀ s : ℝ, Ψ ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) = γ s)
    (hesc : ∀ K : Set M, IsCompact K → ∃ S : ℝ, ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
      ‖p.1‖ ≤ 1 → S ≤ |p.2| → Ψ p ∉ K)
    {C : Set M} (hC : IsClosed C) (hCdisj : Disjoint (Set.range γ) C)
    {U : Set M} (hUo : IsOpen U) (hU : Set.range γ ⊆ U) :
    ∃ T : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M,
      ContMDiff (MCprod n) (MC n) smoothOrder T ∧ Topology.IsEmbedding T ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
        Function.Injective (mfderiv (MCprod n) (MC n) T p)) ∧
      (∀ s : ℝ, T ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) = γ s) ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, T p ∈ U) ∧
      (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → T p ∉ C) ∧
      (∀ K : Set M, IsCompact K → ∃ S : ℝ, ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
        ‖p.1‖ ≤ 1 → S ≤ |p.2| → T p ∉ K) := by
  classical
  -- The open set of parameters whose image lies in `U` and misses `C`.
  set A : Set (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := Ψ ⁻¹' (U \ C) with hA_def
  have hAopen : IsOpen A := (hUo.sdiff hC).preimage hΨ.continuous
  have hcoreA : ∀ s : ℝ, ((0 : EuclideanSpace ℝ (Fin (n - 1))), s) ∈ A := by
    intro s
    have h1 : γ s ∈ U := hU ⟨s, rfl⟩
    have h2 : γ s ∉ C := Set.disjoint_left.mp hCdisj ⟨s, rfl⟩
    show Ψ (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) ∈ U \ C
    rw [hcore s]
    exact ⟨h1, h2⟩
  -- A continuous positive "available radius" for the transverse coordinate.
  obtain ⟨d, hdcont, hdpos, hdkey⟩ :
      ∃ d : ℝ → ℝ, Continuous d ∧ (∀ s, 0 < d s) ∧
        (∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ < d p.2 → p ∈ A) := by
    by_cases hne : (Aᶜ).Nonempty
    · refine ⟨fun s => Metric.infDist (((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) Aᶜ,
        ?_, ?_, ?_⟩
      · have hcont : Continuous (fun q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ =>
            Metric.infDist q Aᶜ) := Metric.continuous_infDist_pt Aᶜ
        have hpar : Continuous (fun s : ℝ => (((0 : EuclideanSpace ℝ (Fin (n - 1))), s))) :=
          continuous_const.prodMk continuous_id
        exact hcont.comp hpar
      · intro s
        exact (hAopen.isClosed_compl.notMem_iff_infDist_pos (x := ((0 : EuclideanSpace ℝ
          (Fin (n - 1))), s)) hne).mp (by simpa using hcoreA s)
      · intro p hp
        by_contra hnot
        have hle : Metric.infDist (((0 : EuclideanSpace ℝ (Fin (n - 1))), p.2)) Aᶜ ≤ ‖p.1‖ := by
          have hmem : p ∈ Aᶜ := hnot
          have h1 := Metric.infDist_le_dist_of_mem (x := (((0 : EuclideanSpace ℝ (Fin (n - 1))),
            p.2))) hmem
          rwa [Prod.dist_eq, dist_eq_norm, dist_self, zero_sub, norm_neg,
            max_eq_left (norm_nonneg p.1)] at h1
        exact absurd hp (not_lt.mpr hle)
    · refine ⟨fun _ => 1, continuous_const, fun s => one_pos, ?_⟩
      intro p _
      have hcomp : Aᶜ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have huniv : A = univ := by rw [← compl_compl A, hcomp, compl_empty]
      rw [huniv]
      exact trivial
  -- A smooth positive minorant of `min d 1`.
  obtain ⟨R, hRcd, hRpos, hRle⟩ :=
    smooth_minorant (φ := fun s => min (d s) 1) (hdcont.min continuous_const)
      (fun s => lt_min (hdpos s) one_pos)
  have hRd : ∀ s, R s ≤ d s := fun s => le_trans (hRle s) (min_le_left _ _)
  have hR1 : ∀ s, R s ≤ 1 := fun s => le_trans (hRle s) (min_le_right _ _)
  -- The shrinking map and its properties.
  have hScd : ContMDiff (MCprod n) (MCprod n) smoothOrder (shrink n R) :=
    shrink_contMDiff n hRcd
  have hSinj : Function.Injective (shrink n R) := shrink_injective n hRpos
  have hSimm : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
      Function.Injective (mfderiv (MCprod n) (MCprod n) (shrink n R) p) :=
    fun p => shrink_mfderiv_injective n hRcd hRpos p
  have hSA : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
      Ψ (shrink n R p) ∈ U \ C := by
    intro p
    have hmem : shrink n R p ∈ A := by
      refine hdkey (shrink n R p) ?_
      calc ‖(shrink n R p).1‖ < R (shrink n R p).2 := shrink_fst_norm_lt n hRpos p
        _ ≤ d (shrink n R p).2 := hRd _
    rwa [hA_def] at hmem
  -- The shrunk tube.
  have hTcd : ContMDiff (MCprod n) (MC n) smoothOrder (Ψ ∘ shrink n R) := hΨ.comp hScd
  have hTinj : Function.Injective (Ψ ∘ shrink n R) := hemb.injective.comp hSinj
  have hTimm : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
      Function.Injective (mfderiv (MCprod n) (MC n) (Ψ ∘ shrink n R) p) := by
    intro p
    rw [mfderiv_comp (I := MCprod n) (I' := MCprod n) (I'' := MC n) (x := p)
      (f := shrink n R) (g := Ψ)
      (hΨ.contMDiffAt.mdifferentiableAt (by simp))
      (hScd.contMDiffAt.mdifferentiableAt (by simp))]
    intro v w hvw
    simp only [Function.comp_apply] at hvw
    exact hSimm p (himm (shrink n R p) hvw)
  refine ⟨Ψ ∘ shrink n R, hTcd, ?_, hTimm, ?_, ?_, ?_, ?_⟩
  · have hld : IsLocalDiffeomorph (MCprod n) (MC n) smoothOrder (Ψ ∘ shrink n R) := by
      rw [← chartedSpaceSelf_prod] at hTcd hTimm ⊢
      exact isLocalDiffeomorph_of_immersion (n := n) (by omega) hTcd hTimm
    exact ((hld.isLocalHomeomorph).isOpenEmbedding_of_injective hTinj).toIsEmbedding
  · intro s
    show Ψ (shrink n R ((0 : EuclideanSpace ℝ (Fin (n - 1))), s)) = γ s
    rw [shrink_core n R s]
    exact hcore s
  · intro p
    exact (hSA p).1
  · intro p _
    exact (hSA p).2
  · intro K hK
    obtain ⟨S, hS⟩ := hesc K hK
    refine ⟨S, ?_⟩
    intro p hp1 hSp
    refine hS (shrink n R p) ?_ ?_
    · exact le_of_lt (lt_of_lt_of_le (shrink_fst_norm_lt n hRpos p) (hR1 p.2))
    · rw [shrink_snd]
      exact hSp

end

end Work.Noncompact.CompressionTube
