import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Submission.Work.BoseSym.Form.gSq_eq_integral
import Submission.Work.BoseSym.Form.l2Sq_eq_integral
import Submission.Work.BoseSym.Liminf.exists_inner_eq_of_ker_le_ker
import Submission.Work.BoseSym.Liminf.potSq_liminf_box
import Submission.Work.BoseSym.Rellich.rellich
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lower semicontinuity of the Dirichlet form along a bounded sequence in `Hsub`

Given a sequence `p n` in the Dirichlet energy space `Hsub N L` with
`l2Sq (p n) = 1` and uniformly bounded gradient norms, and an increasing
sequence of nonnegative weights `W n ↑ Wlim` with uniformly bounded weighted
energies `∫ W n · (p n)²`, one can extract a subsequence `φ` and find a limit
`q : Hsub N L` with `l2Sq q = 1`, `Wlim · q²` integrable on the box, and

`gSq q + ∫ Wlim · q² ≤ liminf (gSq (p ∘ φ) + ∫ (W ∘ φ) · (p ∘ φ)²)`.

The proof has three ingredients.

* **Compactness** (`Rellich.rellich`): a subsequence `φ` and `w ∈ L²` with
  `(p (φ n)).1 → w` in `L²`, whence `‖w‖ = 1`.

* **The kinetic term.**  `Amb N = L² × ∏_j L²` is Hilbertian only for the
  *graph* inner product `hSq = l2Sq + gSq`; this is the type synonym `Xsp`
  (`WithLp 2`), in which `Hsub` sits as the closed subspace `HsubX`.  The
  element `(w, h)` is produced by a Hahn–Banach/Riesz argument on the
  annihilator of `HsubX`: for `y` orthogonal to `HsubX` the orthogonality of
  `p (φ n)` gives
  `⟪(p (φ n)).1, projFirst y⟫ = -⟪toLp (p (φ n)).2, projW y⟫`, hence
  `|⟪w, projFirst y⟫| ≤ √(gSq (p (φ n))) ‖projW y‖` for every `n`, where the
  norm on the right is the `ℓ²` norm of the gradient coordinates.  Passing to
  the limit and applying Hahn–Banach followed by Riesz to the linear functional
  `y ↦ -⟪w, projFirst y⟫` (well defined on the fibres of `projW`) gives
  `h` with `‖h‖ ≤ √(liminf gSq (p ∘ φ))` and `⟪h, projW y⟫ = -⟪w, projFirst y⟫`.
  Double orthogonality in `Xsp` then places `(w, h)` in `HsubX`, i.e.
  `q := (w, WithLp.ofLp h) ∈ Hsub` with `gSq q = ‖h‖² ≤ liminf gSq (p ∘ φ)`.

* **The potential term** (`potSq_liminf_box`): monotone convergence together
  with `∫ W n · (p n)² ≤ C'` gives `∫ Wlim · w² ≤ liminf ∫ (W ∘ φ) (p ∘ φ)²`.
-/

namespace Work.BoseSym.Assemble

open MeasureTheory Filter
open scoped Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The graph-norm Hilbert space -/

/-- The gradient coordinates of the ambient space, with the `ℓ²` norm. -/
abbrev Wg (N : ℕ) := WithLp 2 (Work.BoseSym.GIdx N → Work.BoseSym.L2 N)

/-- The ambient space with the graph (`ℓ²`-product) norm. -/
abbrev Xsp (N : ℕ) := WithLp 2 (Work.BoseSym.L2 N × Wg N)

/-- The identity from the ambient space to its graph-norm version, as a linear
map. -/
noncomputable def toX (N : ℕ) : Work.BoseSym.Amb N →ₗ[ℝ] Xsp N :=
  (WithLp.linearEquiv 2 ℝ (Work.BoseSym.L2 N × Wg N)).symm.toLinearMap ∘ₗ
    LinearMap.prodMap (LinearMap.id)
      ((WithLp.linearEquiv 2 ℝ (Work.BoseSym.GIdx N → Work.BoseSym.L2 N)).symm.toLinearMap)

/-- First coordinate projection of the graph-norm ambient space. -/
noncomputable def projFirst (N : ℕ) : Xsp N →ₗ[ℝ] Work.BoseSym.L2 N :=
  (LinearMap.fst ℝ (Work.BoseSym.L2 N) (Wg N)) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (Work.BoseSym.L2 N × Wg N)).toLinearMap

/-- Projection of the graph-norm ambient space onto its gradient coordinates. -/
noncomputable def projW (N : ℕ) : Xsp N →ₗ[ℝ] Wg N :=
  (LinearMap.snd ℝ (Work.BoseSym.L2 N) (Wg N)) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (Work.BoseSym.L2 N × Wg N)).toLinearMap

lemma toX_fst (N : ℕ) (p : Work.BoseSym.Amb N) : WithLp.fst (toX N p) = p.1 := by
  rw [← WithLp.ofLp_fst]; rfl

lemma toX_snd_eq (N : ℕ) (p : Work.BoseSym.Amb N) :
    WithLp.snd (toX N p) = WithLp.toLp 2 p.2 := by
  rw [← WithLp.ofLp_snd]; rfl

lemma projFirst_toX (N : ℕ) (p : Work.BoseSym.Amb N) : projFirst N (toX N p) = p.1 := by
  simp [projFirst, toX]

lemma projW_toX (N : ℕ) (p : Work.BoseSym.Amb N) :
    projW N (toX N p) = WithLp.toLp 2 p.2 := by
  simp [projW, toX]

/-- The `Xsp` norm squared is the graph norm `hSq`. -/
lemma toX_norm_sq (N : ℕ) (p : Work.BoseSym.Amb N) : ‖toX N p‖ ^ 2 = Work.BoseSym.hSq p := by
  rw [WithLp.prod_norm_sq_eq_of_L2, toX_fst, toX_snd_eq, PiLp.norm_sq_eq_of_L2]
  simp [Work.BoseSym.hSq, Work.BoseSym.l2Sq, Work.BoseSym.gSq]

lemma toX_injective (N : ℕ) : Function.Injective (toX N) := by
  intro p q hpq
  have h1 : p.1 = q.1 := by rw [← toX_fst N p, ← toX_fst N q, hpq]
  have h2 : WithLp.toLp 2 p.2 = WithLp.toLp 2 q.2 := by
    rw [← toX_snd_eq N p, ← toX_snd_eq N q, hpq]
  exact Prod.ext h1 (WithLp.toLp_injective 2 h2)

/-- The graph norm controls the product (max) norm of `Amb N`. -/
lemma norm_toX_le (N : ℕ) (p : Work.BoseSym.Amb N) :
    ‖toX N p‖ ≤ Real.sqrt ((Fintype.card (Work.BoseSym.GIdx N) : ℝ) + 1) * ‖p‖ := by
  have hsq : ‖toX N p‖ ^ 2 = Work.BoseSym.hSq p := toX_norm_sq N p
  have hcard : (0 : ℝ) ≤ (Fintype.card (Work.BoseSym.GIdx N) : ℝ) + 1 := by positivity
  have hb : Work.BoseSym.hSq p ≤ ((Fintype.card (Work.BoseSym.GIdx N) : ℝ) + 1) * ‖p‖ ^ 2 := by
    have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
    have h2 : ∀ j, ‖p.2 j‖ ≤ ‖p‖ := fun j => (norm_le_pi_norm p.2 j).trans (norm_snd_le p)
    simp only [Work.BoseSym.hSq, Work.BoseSym.l2Sq, Work.BoseSym.gSq]
    have h3 : ∑ j : Work.BoseSym.GIdx N, ‖p.2 j‖ ^ 2 ≤ ∑ _j : Work.BoseSym.GIdx N, ‖p‖ ^ 2 :=
      Finset.sum_le_sum fun j _ => by nlinarith [h2 j, norm_nonneg (p.2 j), norm_nonneg p]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h3
    nlinarith [h1, h3, norm_nonneg p.1, norm_nonneg p]
  have hK : (Real.sqrt ((Fintype.card (Work.BoseSym.GIdx N) : ℝ) + 1) * ‖p‖) ^ 2
      = ((Fintype.card (Work.BoseSym.GIdx N) : ℝ) + 1) * ‖p‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hcard]
  have hKnn : 0 ≤ Real.sqrt ((Fintype.card (Work.BoseSym.GIdx N) : ℝ) + 1) * ‖p‖ := by positivity
  nlinarith [hsq, hb, hK, hKnn, norm_nonneg (toX N p)]

/-- `toX` is continuous. -/
noncomputable def toXclm (N : ℕ) : Work.BoseSym.Amb N →L[ℝ] Xsp N :=
  (toX N).mkContinuous _ (norm_toX_le N)

/-- The max norm of the gradient coordinates is bounded by their `ℓ²` norm; this
is why the `ℓ²` norm is the one that gives the sharp constant below. -/
lemma norm_pi_le_lp (N : ℕ) (g : Work.BoseSym.GIdx N → Work.BoseSym.L2 N) :
    ‖g‖ ≤ ‖(WithLp.toLp 2 g : Wg N)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => PiLp.norm_apply_le (WithLp.toLp 2 g) j

/-- The graph norm dominates the max norm. -/
lemma norm_le_toX_norm (N : ℕ) (p : Work.BoseSym.Amb N) : ‖p‖ ≤ ‖toX N p‖ := by
  have hsq : ‖toX N p‖ ^ 2 = Work.BoseSym.hSq p := toX_norm_sq N p
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · have h2 : ‖p.1‖ ^ 2 ≤ Work.BoseSym.hSq p := by
      have h := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (‖p.2 j‖))
      simp only [Work.BoseSym.hSq, Work.BoseSym.l2Sq, Work.BoseSym.gSq]
      linarith
    nlinarith [h2, hsq, norm_nonneg p.1, norm_nonneg (toX N p)]
  · have h1 := norm_pi_le_lp N p.2
    have h2 : ‖(WithLp.toLp 2 p.2 : Wg N)‖ ^ 2 = Work.BoseSym.gSq p := by
      rw [PiLp.norm_sq_eq_of_L2]; rfl
    have h4 : ‖p.2‖ ^ 2 ≤ Work.BoseSym.gSq p := by
      nlinarith [h1, h2, norm_nonneg p.2, norm_nonneg (WithLp.toLp 2 p.2 : Wg N)]
    have h5 : ‖p.2‖ ^ 2 ≤ Work.BoseSym.hSq p := by
      simp only [Work.BoseSym.hSq, Work.BoseSym.l2Sq]
      nlinarith [h4, sq_nonneg ‖p.1‖]
    nlinarith [h5, hsq, norm_nonneg p.2, norm_nonneg (toX N p)]

/-- The pairing of the graph point of `p` with `y`, in coordinates. -/
lemma inner_toX (N : ℕ) (p : Work.BoseSym.Amb N) (y : Xsp N) :
    inner ℝ (toX N p) y
      = inner ℝ p.1 (projFirst N y) + inner ℝ (WithLp.toLp 2 p.2) (projW N y) := by
  rw [WithLp.prod_inner_apply, PiLp.inner_apply]
  simp only [projFirst, projW, toX, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.prodMap_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    LinearMap.id_coe, id_eq]
  rfl

/-- The pairing of the pair `(w, h)`, in coordinates. -/
lemma inner_pair (N : ℕ) (w : Work.BoseSym.L2 N) (h : Wg N) (y : Xsp N) :
    inner ℝ (toX N (w, WithLp.ofLp h)) y
      = inner ℝ w (projFirst N y) + inner ℝ h (projW N y) := by
  rw [inner_toX]

/-- The projection onto the gradient coordinates is a contraction. -/
lemma norm_projW_le (N : ℕ) (y : Xsp N) : ‖projW N y‖ ≤ ‖y‖ := by
  have h : ‖y‖ ^ 2 = ‖projFirst N y‖ ^ 2 + ‖projW N y‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp [projFirst, projW]
  nlinarith [h, norm_nonneg (projW N y), norm_nonneg (projFirst N y), norm_nonneg y]

/-- The `ℓ²` norm of the gradient coordinates of `p` is `√(gSq p)`. -/
lemma norm_toLp_grad (N : ℕ) (p : Work.BoseSym.Amb N) :
    ‖(WithLp.toLp 2 p.2 : Wg N)‖ = Real.sqrt (Work.BoseSym.gSq p) := by
  have h : ‖(WithLp.toLp 2 p.2 : Wg N)‖ ^ 2 = Work.BoseSym.gSq p := by
    rw [PiLp.norm_sq_eq_of_L2]; rfl
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- The gradient-coordinate projection as a continuous linear map. -/
noncomputable def projWclm (N : ℕ) : Xsp N →L[ℝ] Wg N :=
  (projW N).mkContinuous 1 (fun y => by rw [one_mul]; exact norm_projW_le N y)

/-- The Dirichlet energy space, transported into the graph-norm Hilbert space. -/
noncomputable def HsubX (N : ℕ) (L : ℝ) : Submodule ℝ (Xsp N) :=
  (Work.BoseSym.Hsub N L).map (toX N)

lemma HsubX_of_mem {N : ℕ} {L : ℝ} {q : Work.BoseSym.Amb N}
    (hq : q ∈ Work.BoseSym.Hsub N L) : toX N q ∈ HsubX N L :=
  Submodule.mem_map_of_mem hq

/-- `HsubX` is closed, being the image of the closed subspace `Hsub` under the
norm-equivalent identification `toX`. -/
lemma HsubX_closed (N : ℕ) (L : ℝ) :
    IsClosed ((HsubX N L : Submodule ℝ (Xsp N)) : Set (Xsp N)) := by
  refine IsSeqClosed.isClosed fun u x hu hux => ?_
  choose q hq hqx using fun n => Submodule.mem_map.mp (hu n)
  have hcau : CauchySeq q := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hcu : CauchySeq u := hux.cauchySeq
    rw [Metric.cauchySeq_iff] at hcu
    obtain ⟨M, hM⟩ := hcu ε hε
    refine ⟨M, fun m hm n hn => ?_⟩
    calc dist (q m) (q n) = ‖q m - q n‖ := dist_eq_norm _ _
      _ ≤ ‖toX N (q m - q n)‖ := norm_le_toX_norm N _
      _ = ‖u m - u n‖ := by rw [map_sub, hqx m, hqx n]
      _ = dist (u m) (u n) := (dist_eq_norm _ _).symm
      _ < ε := hM m hm n hn
  obtain ⟨q₀, hq₀⟩ := cauchySeq_tendsto_of_complete hcau
  have hmem : q₀ ∈ Work.BoseSym.Hsub N L :=
    (Submodule.isClosed_topologicalClosure
      (Submodule.span ℝ (Set.range (Work.BoseSym.graphPoint N L)))).mem_of_tendsto hq₀
      (Eventually.of_forall hq)
  have hx : x = toX N q₀ := by
    have h1 : Tendsto (fun n => toX N (q n)) atTop (nhds (toX N q₀)) :=
      ((toXclm N).continuous.tendsto q₀).comp hq₀
    rw [show (fun n => toX N (q n)) = u from funext hqx] at h1
    exact (tendsto_nhds_unique h1 hux).symm
  rw [hx]
  exact HsubX_of_mem hmem

/-! ## Two elementary facts about `liminf` -/

/-- If `a n → l` and `a n ≤ b n` with `b` bounded above then `l ≤ liminf b`. -/
lemma le_liminf_of_tendsto_of_le {a b : ℕ → ℝ} {l M : ℝ} (ha : Tendsto a atTop (nhds l))
    (hba : ∀ n, a n ≤ b n) (hbM : ∀ n, b n ≤ M) : l ≤ liminf b atTop := by
  have h1 : liminf a atTop = l := ha.liminf_eq
  have h2 : liminf a atTop ≤ liminf b atTop := by
    refine liminf_le_liminf (f := (Filter.atTop : Filter ℕ)) (Eventually.of_forall hba) ?_ ?_
    · refine isBoundedUnder_of_eventually_ge (a := l - 1) ?_
      have hmem : Set.Ioi (l - 1) ∈ 𝓝 l := isOpen_Ioi.mem_nhds (by simp)
      filter_upwards [ha.eventually hmem] with n hn
      exact le_of_lt hn
    · exact IsBoundedUnder.isCoboundedUnder_flip (r := (· ≤ ·))
        (isBoundedUnder_of_eventually_le (a := M) (Eventually.of_forall hbM))
  rw [h1] at h2; exact h2

/-- `liminf √(s n) ≤ √(liminf s n)` for a bounded-above nonnegative sequence. -/
lemma liminf_sqrt_le_sqrt_liminf {s : ℕ → ℝ} {M : ℝ} (h0 : ∀ n, 0 ≤ s n)
    (hM : ∀ n, s n ≤ M) :
    liminf (fun n => Real.sqrt (s n)) atTop ≤ Real.sqrt (liminf s atTop) := by
  have hlim0 : 0 ≤ liminf s atTop := by
    refine le_liminf_of_le (f := (Filter.atTop : Filter ℕ)) (u := s) (a := (0 : ℝ)) ?_ ?_
    · exact IsBoundedUnder.isCoboundedUnder_flip (r := (· ≤ ·))
        (isBoundedUnder_of_eventually_le (a := M) (Eventually.of_forall hM))
    · exact Eventually.of_forall h0
  have hbdd : IsBoundedUnder (· ≥ ·) (Filter.atTop : Filter ℕ) (fun n : ℕ => Real.sqrt (s n)) :=
    isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
      (Eventually.of_forall (fun n : ℕ => Real.sqrt_nonneg (s n)))
  refine liminf_le_of_le (f := (Filter.atTop : Filter ℕ))
    (u := fun n : ℕ => Real.sqrt (s n)) hbdd ?_
  intro b hb
  rcases lt_or_ge b 0 with hb0 | hb0
  · linarith [Real.sqrt_nonneg (liminf s atTop)]
  · have hbsq : b ^ 2 ≤ liminf s atTop := by
      refine le_liminf_of_le (f := (Filter.atTop : Filter ℕ)) (u := s) (a := b ^ 2) ?_ ?_
      · exact IsBoundedUnder.isCoboundedUnder_flip (r := (· ≤ ·))
          (isBoundedUnder_of_eventually_le (a := M) (Eventually.of_forall hM))
      · filter_upwards [hb] with n hn
        have hs := Real.sq_sqrt (h0 n)
        have hnn := Real.sqrt_nonneg (s n)
        nlinarith [hn, hb0, hs, hnn]
    exact (Real.le_sqrt hb0 hlim0).mpr hbsq

/-! ## The main statement -/

theorem hsub_liminf_lsc {N : ℕ} {L : ℝ} {C C' : ℝ}
    (p : ℕ → Work.BoseSym.Hsub N L) (hp1 : ∀ n, Work.BoseSym.l2Sq ((p n : Work.BoseSym.Amb N)) = 1)
    (hC : ∀ n, Work.BoseSym.gSq ((p n : Work.BoseSym.Amb N)) ≤ C)
    {W : ℕ → Work.BoseSym.Conf N → ℝ} {Wlim : Work.BoseSym.Conf N → ℝ}
    (hW0 : ∀ n, 0 ≤ W n) (hWlim0 : 0 ≤ Wlim)
    (hWm : ∀ n, MeasureTheory.AEStronglyMeasurable (W n)
      (MeasureTheory.volume.restrict (BoseGases.box N L)))
    (hWlimm : MeasureTheory.AEStronglyMeasurable Wlim
      (MeasureTheory.volume.restrict (BoseGases.box N L)))
    (hWmono : ∀ n x, W n x ≤ W (n + 1) x)
    (hWtend : ∀ x, Filter.Tendsto (fun n => W n x) Filter.atTop (nhds (Wlim x)))
    (hC'i : ∀ n, MeasureTheory.IntegrableOn
      (fun x => W n x * (((p n : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
      (BoseGases.box N L) MeasureTheory.volume)
    (hC'b : ∀ n, ∫ x in BoseGases.box N L,
        W n x * (((p n : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2 ≤ C') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ q : Work.BoseSym.Hsub N L,
      Work.BoseSym.l2Sq (q : Work.BoseSym.Amb N) = 1 ∧
      MeasureTheory.IntegrableOn
        (fun x => Wlim x * (((q : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
        (BoseGases.box N L) MeasureTheory.volume ∧
      Work.BoseSym.gSq (q : Work.BoseSym.Amb N) + ∫ x in BoseGases.box N L,
          Wlim x * (((q : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2
        ≤ Filter.liminf (fun n => Work.BoseSym.gSq ((p (φ n) : Work.BoseSym.Amb N))
            + ∫ x in BoseGases.box N L,
                W (φ n) x * (((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
            Filter.atTop := by
  classical
  -- (0) the graph norm is bounded
  have hSq_le : ∀ n, Work.BoseSym.hSq ((p n : Work.BoseSym.Amb N)) ≤ C + 1 := by
    intro n
    have h1 := hp1 n
    simp only [Work.BoseSym.hSq, h1]
    linarith [hC n]
  -- (1) Rellich: strong `L²` convergence of the function parts
  obtain ⟨φ, hφ, w, hw⟩ := Rellich.rellich N L (C + 1) p hSq_le
  have hwt : Tendsto (fun n => ((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.L2 N))
      Filter.atTop (nhds w) := hw
  -- (2) the limit has norm one
  have hwnorm : ‖w‖ = 1 := by
    have h1 : Tendsto (fun n => ‖((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.L2 N)‖)
        Filter.atTop (nhds ‖w‖) := hwt.norm
    have h2 : (fun n => ‖((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.L2 N)‖)
        = fun _ => (1 : ℝ) := by
      funext n
      have h3 := hp1 (φ n)
      simp only [Work.BoseSym.l2Sq] at h3
      nlinarith [norm_nonneg (((p (φ n) : Work.BoseSym.Amb N).1) : Work.BoseSym.L2 N)]
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- (3) the kinetic part
  have hCnn : 0 ≤ C :=
    (Finset.sum_nonneg
      (fun j (_ : j ∈ Finset.univ) => sq_nonneg (‖((p 0 : Work.BoseSym.Amb N).2) j‖))).trans (hC 0)
  set Lam : ℝ :=
    Filter.liminf (fun n => Work.BoseSym.gSq ((p (φ n) : Work.BoseSym.Amb N))) Filter.atTop
    with hLamdef
  have hLamnn : 0 ≤ Lam := by
    rw [hLamdef]
    refine le_liminf_of_le (f := (Filter.atTop : Filter ℕ))
      (u := fun n : ℕ => Work.BoseSym.gSq ((p (φ n) : Work.BoseSym.Amb N))) (a := (0 : ℝ)) ?_ ?_
    · exact IsBoundedUnder.isCoboundedUnder_flip (r := (· ≤ ·))
        (isBoundedUnder_of_eventually_le (a := C) (Eventually.of_forall (fun n : ℕ => hC (φ n))))
    · exact Eventually.of_forall (fun n : ℕ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  let Y : Submodule ℝ (Xsp N) := (HsubX N L)ᗮ
  let T : Y →L[ℝ] Wg N := (projWclm N).comp (Submodule.subtypeL Y)
  let chi : Work.BoseSym.L2 N →ₗ[ℝ] ℝ :=
    { toFun := fun x => inner ℝ w x
      map_add' := fun x y => inner_add_right w x y
      map_smul' := fun c x => inner_smul_right w x c }
  let ell : Y →ₗ[ℝ] ℝ := -(chi.comp ((projFirst N).comp (Submodule.subtype Y)))
  have hell : ∀ y : Y, ell y = -inner ℝ w (projFirst N (y : Xsp N)) := fun y => rfl
  -- well-definedness of `ell` on the fibres of the gradient-coordinate projection
  have hker : T.ker ≤ ell.ker := by
    intro y hy
    have hyν : projW N (y : Xsp N) = 0 := hy
    have hδ : inner ℝ w (projFirst N (y : Xsp N)) = 0 := by
      have h1 : Tendsto (fun n => inner ℝ (((p (φ n) : Work.BoseSym.Amb N).1) : Work.BoseSym.L2 N)
          (projFirst N (y : Xsp N))) Filter.atTop
          (nhds (inner ℝ w (projFirst N (y : Xsp N)))) :=
        hwt.inner tendsto_const_nhds
      have h2 : ∀ n, inner ℝ (((p (φ n) : Work.BoseSym.Amb N).1) : Work.BoseSym.L2 N)
          (projFirst N (y : Xsp N)) = 0 := by
        intro n
        have h3 := (Submodule.mem_orthogonal (HsubX N L) (y : Xsp N)).mp y.2
          (toX N ((p (φ n)) : Work.BoseSym.Amb N)) (HsubX_of_mem (p (φ n)).2)
        rw [inner_toX] at h3
        rw [hyν, inner_zero_right, add_zero] at h3
        exact h3
      rw [funext h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    show ell y = 0
    rw [hell y, hδ, neg_zero]
  -- the quantitative bound
  have hbound : ∀ y : Y, |ell y| ≤ Real.sqrt Lam * ‖T y‖ := by
    intro y
    rcases eq_or_ne (projW N (y : Xsp N)) 0 with hν0 | hν0
    · have hyk : y ∈ T.ker := hν0
      have hz : ell y = 0 := hker hyk
      have hTy : T y = 0 := hν0
      rw [hz, hTy, norm_zero, mul_zero, abs_zero]
    · have hνpos : 0 < ‖projW N (y : Xsp N)‖ := norm_pos_iff.mpr hν0
      have hb : ∀ n, |inner ℝ (((p (φ n) : Work.BoseSym.Amb N).1) : Work.BoseSym.L2 N)
            (projFirst N (y : Xsp N))| / ‖projW N (y : Xsp N)‖
          ≤ Real.sqrt (Work.BoseSym.gSq ((p (φ n)) : Work.BoseSym.Amb N)) := by
        intro n
        have h3 := (Submodule.mem_orthogonal (HsubX N L) (y : Xsp N)).mp y.2
          (toX N ((p (φ n)) : Work.BoseSym.Amb N)) (HsubX_of_mem (p (φ n)).2)
        rw [inner_toX] at h3
        have h4 : inner ℝ (((p (φ n) : Work.BoseSym.Amb N).1) : Work.BoseSym.L2 N)
            (projFirst N (y : Xsp N))
            = - inner ℝ (WithLp.toLp 2 (((p (φ n)) : Work.BoseSym.Amb N).2))
                (projW N (y : Xsp N)) := by
          linarith [h3]
        rw [h4, abs_neg, div_le_iff₀ hνpos]
        calc |inner ℝ (WithLp.toLp 2 (((p (φ n)) : Work.BoseSym.Amb N).2))
              (projW N (y : Xsp N))|
            ≤ ‖(WithLp.toLp 2 (((p (φ n)) : Work.BoseSym.Amb N).2) : Wg N)‖
                * ‖projW N (y : Xsp N)‖ := abs_real_inner_le_norm _ _
          _ = Real.sqrt (Work.BoseSym.gSq ((p (φ n)) : Work.BoseSym.Amb N))
                * ‖projW N (y : Xsp N)‖ := by rw [norm_toLp_grad]
      have hlim : Tendsto (fun n => |inner ℝ (((p (φ n) : Work.BoseSym.Amb N).1) : Work.BoseSym.L2 N)
            (projFirst N (y : Xsp N))| / ‖projW N (y : Xsp N)‖) Filter.atTop
          (nhds (|inner ℝ w (projFirst N (y : Xsp N))| / ‖projW N (y : Xsp N)‖)) :=
        ((hwt.inner tendsto_const_nhds).abs).div_const _
      have hmain : |inner ℝ w (projFirst N (y : Xsp N))| / ‖projW N (y : Xsp N)‖
          ≤ Real.sqrt Lam := by
        refine (le_liminf_of_tendsto_of_le hlim hb (M := Real.sqrt C) ?_).trans ?_
        · intro n
          rw [Real.sqrt_le_sqrt_iff hCnn]
          exact hC (φ n)
        · rw [hLamdef]
          exact liminf_sqrt_le_sqrt_liminf
            (s := fun n => Work.BoseSym.gSq ((p (φ n)) : Work.BoseSym.Amb N))
            (fun n => Finset.sum_nonneg fun j _ => sq_nonneg _) (fun n => hC (φ n))
      rw [hell y, abs_neg]
      have hTy : ‖T y‖ = ‖projW N (y : Xsp N)‖ := rfl
      rw [hTy]
      exact (div_le_iff₀ hνpos).mp hmain
  obtain ⟨h, hhnorm, hhinner⟩ :=
    Work.BoseSym.Liminf.exists_inner_eq_of_ker_le_ker T ell hker (Real.sqrt_nonneg Lam) hbound
  -- (4) the pair `(w, h)` lies in `Hsub`
  have hQmem : (w, WithLp.ofLp h) ∈ Work.BoseSym.Hsub N L := by
    have horth : toX N (w, WithLp.ofLp h) ∈ (HsubX N L)ᗮᗮ := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      have hz : inner ℝ (toX N (w, WithLp.ofLp h)) y = 0 := by
        rw [inner_pair]
        have h1 := hhinner ⟨y, hy⟩
        have h2 : T ⟨y, hy⟩ = projW N y := rfl
        have h3 : ell ⟨y, hy⟩ = -inner ℝ w (projFirst N y) := hell ⟨y, hy⟩
        rw [h2, h3] at h1
        linarith [h1]
      rw [real_inner_comm]
      exact hz
    have hcl : (HsubX N L)ᗮᗮ = HsubX N L := by
      rw [Submodule.orthogonal_orthogonal_eq_closure,
        IsClosed.submodule_topologicalClosure_eq (HsubX_closed N L)]
    rw [hcl] at horth
    rw [HsubX, Submodule.mem_map] at horth
    obtain ⟨q, hq, hqx⟩ := horth
    have hqw : (w, WithLp.ofLp h) = q := (toX_injective N hqx).symm
    rw [hqw]
    exact hq
  -- (5) the potential part
  have hWle : ∀ {m k : ℕ}, m ≤ k → ∀ x, W m x ≤ W k x := by
    intro m k hmk
    induction hmk with
    | refl => intro x; exact le_rfl
    | step hmk ih => intro x; exact le_trans (ih x) (hWmono _ x)
  have hpot := Work.BoseSym.Liminf.potSq_liminf_box (N := N) (L := L) (C' := C')
    (W := fun n => W (φ n)) (Wlim := Wlim)
    (fun n => hW0 (φ n)) hWlim0 (fun n => hWm (φ n)) hWlimm
    (fun n x => hWle (hφ.monotone (Nat.le_succ n)) x)
    (fun x => (hWtend x).comp hφ.tendsto_atTop)
    (u := fun n => ((p (φ n)) : Work.BoseSym.Amb N).1) (v := w) hwt
    (fun n => hC'i (φ n)) (fun n => hC'b (φ n))
  -- (6) assembly
  refine ⟨φ, hφ, ⟨(w, WithLp.ofLp h), hQmem⟩, ?_, hpot.1, ?_⟩
  · show ‖w‖ ^ 2 = 1
    rw [hwnorm]; norm_num
  · have hgsq : Work.BoseSym.gSq (w, WithLp.ofLp h) ≤ Lam := by
      have h1 : Work.BoseSym.gSq (w, WithLp.ofLp h) = ‖h‖ ^ 2 := by
        simp only [Work.BoseSym.gSq]
        rw [PiLp.norm_sq_eq_of_L2]
      rw [h1]
      nlinarith [norm_nonneg h, Real.sq_sqrt hLamnn, hLamnn]
    have hsum : Lam + (Filter.liminf (fun n => ∫ x in BoseGases.box N L,
        W (φ n) x * (((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
        Filter.atTop)
        ≤ Filter.liminf (fun n => Work.BoseSym.gSq ((p (φ n) : Work.BoseSym.Amb N))
            + ∫ x in BoseGases.box N L,
                W (φ n) x * (((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
            Filter.atTop := by
      rw [hLamdef]
      exact le_liminf_add
        (isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
          (Eventually.of_forall (fun n : ℕ => Finset.sum_nonneg fun j _ => sq_nonneg _)))
        (isBoundedUnder_of_eventually_le (a := C) (Eventually.of_forall (fun n : ℕ => hC (φ n))))
        (isBoundedUnder_of_eventually_ge (a := (0 : ℝ)) (Eventually.of_forall (fun n : ℕ =>
          integral_nonneg fun x => mul_nonneg (hW0 (φ n) x) (sq_nonneg _))))
        (IsBoundedUnder.isCoboundedUnder_flip (r := (· ≤ ·))
          (isBoundedUnder_of_eventually_le (a := C') (Eventually.of_forall (fun n => hC'b (φ n)))))
    exact (add_le_add hgsq hpot.2).trans hsum

end

end Work.BoseSym.Assemble
