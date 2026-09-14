import Submission.NBody.SameBallEstimate
import Submission.NBody.HolderEstimate
import Submission.NBody.Horofunction
import Submission.Commons.Analysis.Calculus.deriv_ofLp_apply_of_differentiable
import Submission.Commons.Data.Finset.sum_fibre_pairwise
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_pi
import Submission.Commons.Topology.Metric.exists_cluster_partition
import Submission.Commons.Topology.Metric.exists_path_sub_ball_action_bound
import Mathlib

/-!
# Maderna's estimates for the action potential

Maderna's *same-ball estimate* (`curva.min` of *On weak KAM theory for N-body problems*) says that
two configurations contained in a ball of radius `R` can be joined in time `τ` by a curve whose
action is at most `α R²/τ + β τ/R`.  Combined with a *cluster partition* of the bodies (Maderna's
`clusters` lemma), it yields the fixed-time estimate

  `φ(x,y,τ) ≤ α₁ r²/τ + β₁ τ/r`  whenever `r > ‖x-y‖`,

which is the input of `thm-phih.estim` (see `HolderEstimate.lean`).

This file contains the cluster assembly.  The same-ball estimate enters as an explicit hypothesis
`SubBallEstimate`; it is proved in the commons as
`Commons.Topology.Metric.exists_path_sub_ball_action_bound`.

Everything here is fully proved.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

namespace Submission.NBody

variable [Nontrivial E]

/-- **Maderna's same-ball estimate on a sub-configuration** (hypothesis form).  For any
sub-configuration `s` and any two configurations `x`, `y` that agree outside `s` and lie in a ball
of radius `R` on `s`, there is a curve joining them in time `τ`, freezing the complement, confined
to `B(r₀, 7NR)`, collision free almost everywhere on `s`, whose kinetic energy plus *intra-`s`*
potential integral is at most `c₁ (∑_{i∈s} mᵢ) N⁴ R²/τ + c₂ (∑_{i∈s} mᵢ)² N⁴ τ/R`. -/
def SubBallEstimate (c₁ c₂ : ℝ) : Prop :=
  ∀ {N' : ℕ} (m' : Fin N' → ℝ), (∀ i, 0 < m' i) → ∀ (s : Finset (Fin N'))
    (x y : EN E N') (r₀ : E), ∀ {R τ : ℝ}, 0 < R → 0 < τ →
    (∀ i ∈ s, dist (x i) r₀ ≤ R) → (∀ i ∈ s, dist (y i) r₀ ≤ R) →
    (∀ i ∉ s, y i = x i) →
    ∃ γ : ℝ → EN E N',
      γ 0 = x ∧ γ τ = y ∧
        (∀ t, ∀ i, i ∉ s → γ t i = x i) ∧
        (∀ t, ∀ i, i ∈ s → dist (γ t i) r₀ ≤ 7 * (N' : ℝ) * R) ∧
        AbsolutelyContinuousOnInterval γ 0 τ ∧
        (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ → ∀ i ∈ s, ∀ j ∈ s, i ≠ j → γ t i ≠ γ t j) ∧
        IntegrableOn
          (fun t => (1 / 2) * (∑ i ∈ s, m' i * ‖deriv γ t i‖ ^ 2)
            + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m' i * m' j * (dist (γ t i) (γ t j))⁻¹))
          (Set.Ioc 0 τ) ∧
        (∫ t in (0 : ℝ)..τ, ((1 / 2) * (∑ i ∈ s, m' i * ‖deriv γ t i‖ ^ 2)
            + (∑ j ∈ s, ∑ i ∈ s.filter (fun i => i < j),
                m' i * m' j * (dist (γ t i) (γ t j))⁻¹)))
          ≤ c₁ * (∑ i ∈ s, m' i) * (N' : ℝ) ^ 4 * R ^ 2 / τ
              + c₂ * (∑ i ∈ s, m' i) ^ 2 * (N' : ℝ) ^ 4 * τ / R
/-! ## The fibre partition induced by a cluster map -/

section Fibres

variable {K : ℕ}

/-- The cluster (fibre) of the index `j` under the map `jj`. -/
def fibre (jj : Fin N → Fin K) (j : Fin K) : Finset (Fin N) :=
  Finset.univ.filter (fun i => jj i = j)

lemma mem_fibre {jj : Fin N → Fin K} {j : Fin K} {i : Fin N} :
    i ∈ fibre jj j ↔ jj i = j := by
  simp [fibre]

lemma fibre_disjoint {jj : Fin N → Fin K} {j l : Fin K} (h : j ≠ l) :
    Disjoint (fibre jj j) (fibre jj l) := by
  rw [Finset.disjoint_left]
  intro i hi hl
  rw [mem_fibre] at hi hl
  exact h (hi.symm.trans hl)

lemma mem_fibre_self {jj : Fin N → Fin K} (i : Fin N) : i ∈ fibre jj (jj i) := by
  rw [mem_fibre]

lemma biUnion_fibre (jj : Fin N → Fin K) :
    Finset.univ.biUnion (fun j : Fin K => fibre jj j) = Finset.univ := by
  ext i
  constructor
  · intro _; exact Finset.mem_univ i
  · intro _
    rw [Finset.mem_biUnion]
    exact ⟨jj i, Finset.mem_univ _, mem_fibre_self i⟩

/-- Summation over the fibres. -/
theorem sum_fibre {ι : Type*} [AddCommMonoid ι] (jj : Fin N → Fin K) (f : Fin N → ι) :
    (∑ j : Fin K, ∑ i ∈ fibre jj j, f i) = ∑ i, f i := by
  rw [← Finset.sum_biUnion (s := Finset.univ) (t := fun j : Fin K => fibre jj j)
    (f := fun i => f i) (fun j _ l _ hjl => fibre_disjoint hjl), biUnion_fibre]

end Fibres

/-! ## Cluster data and the glued curve -/

section Assembly

/-- The data produced by Maderna's cluster partition: centres `ctr` separated by at least
`48 N R`, each body assigned to a centre within distance `R`, where the radius `R` is comparable
to the scale `r`. -/
structure ClusterData (x : EN E N) (r : ℝ) where
  /-- number of clusters -/
  K : ℕ
  /-- the centres of the clusters -/
  ctr : Fin K → E
  /-- the cluster radius -/
  R : ℝ
  hRpos : 0 < R
  hRge : r ≤ R
  hRle : R ≤ (48 * (N : ℝ)) ^ N * r
  hsep : ∀ j k : Fin K, j ≠ k → 48 * (N : ℝ) * R ≤ dist (ctr j) (ctr k)
  /-- the assignment of bodies to clusters -/
  idx : Fin N → Fin K
  hidx : ∀ i, dist (x i) (ctr (idx i)) ≤ R

/-- **Existence of cluster data.**  Maderna's cluster partition, with `λ = 24N` and `ε = r`. -/
theorem exists_clusterData {x : EN E N} {r : ℝ} (hN : 0 < N) (hr : 0 < r) :
    Nonempty (ClusterData x r) := by
  have hN1 : (1 : ℕ) ≤ N := hN
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hlam : (1 : ℝ) < 24 * (N : ℝ) := by linarith
  obtain ⟨K, c, R, hRge, hRle, hsep, hcover⟩ :=
    Commons.Topology.Metric.exists_cluster_partition N hN (fun i => x i)
      (lam := 24 * (N : ℝ)) (eps := r) hlam hr
  have heq : (2 : ℝ) * (24 * (N : ℝ)) = 48 * (N : ℝ) := by ring
  refine ⟨⟨K, c, R, lt_of_lt_of_le hr hRge, hRge, ?_, ?_, fun i => Classical.choose (hcover i),
    fun i => Classical.choose_spec (hcover i)⟩⟩
  · rw [heq] at hRle
    exact hRle
  · intro j k hjk
    have h := hsep j k hjk
    rwa [heq] at h

namespace ClusterData

variable {x : EN E N} {r : ℝ} (D : ClusterData x r)

/-- The cluster of `j`: the set of bodies assigned to the centre `ctr j`. -/
def cl (j : Fin D.K) : Finset (Fin N) := fibre D.idx j

lemma mem_cl (j : Fin D.K) (i : Fin N) : i ∈ D.cl j ↔ D.idx i = j := mem_fibre

lemma mem_cl_self (i : Fin N) : i ∈ D.cl (D.idx i) := mem_fibre_self i

/-- The configuration obtained from `x` by replacing the coordinates of cluster `j` by those
of `y`. -/
noncomputable def patch (y : EN E N) (j : Fin D.K) : EN E N :=
  WithLp.toLp 2 (fun i => if D.idx i = j then y i else x i)

@[simp]
lemma patch_apply (y : EN E N) (j : Fin D.K) (i : Fin N) :
    (D.patch y j).ofLp i = if D.idx i = j then y i else x i := rfl

lemma patch_of_mem (y : EN E N) {i : Fin N} {j : Fin D.K} (hi : D.idx i = j) :
    (D.patch y j).ofLp i = y i := by
  simp [patch_apply, hi]

/-- The glued curve: body `i` follows the curve of its own cluster. -/
noncomputable def glue (γs : (j : Fin D.K) → ℝ → EN E N) : ℝ → EN E N :=
  fun t => WithLp.toLp 2 (fun i => (γs (D.idx i) t).ofLp i)

lemma glue_apply (γs : (j : Fin D.K) → ℝ → EN E N) (t : ℝ) (i : Fin N) :
    (D.glue γs t).ofLp i = (γs (D.idx i) t).ofLp i := rfl

/-- The distance between two bodies in different clusters is at least `20 N R`. -/
lemma dist_glue_ge_of_ne {γs : (j : Fin D.K) → ℝ → EN E N} {t : ℝ}
    {i k : Fin N} (hne : D.idx i ≠ D.idx k)
    (hconf : ∀ j : Fin D.K, ∀ l : Fin N, D.idx l = j →
      dist ((γs j t).ofLp l) (D.ctr j) ≤ 14 * (N : ℝ) * D.R) :
    20 * (N : ℝ) * D.R ≤ dist ((D.glue γs t).ofLp i) ((D.glue γs t).ofLp k) := by
  rw [glue_apply, glue_apply]
  have h1 := hconf (D.idx i) i rfl
  have h2 := hconf (D.idx k) k rfl
  have h3 : 48 * (N : ℝ) * D.R ≤ dist (D.ctr (D.idx i)) (D.ctr (D.idx k)) := D.hsep _ _ hne
  have h4 : dist (D.ctr (D.idx i)) ((γs (D.idx k) t).ofLp k)
      ≤ dist (D.ctr (D.idx i)) ((γs (D.idx i) t).ofLp i)
        + dist ((γs (D.idx i) t).ofLp i) ((γs (D.idx k) t).ofLp k) := dist_triangle _ _ _
  have h5 : dist (D.ctr (D.idx i)) (D.ctr (D.idx k))
      ≤ dist (D.ctr (D.idx i)) ((γs (D.idx k) t).ofLp k)
        + dist ((γs (D.idx k) t).ofLp k) (D.ctr (D.idx k)) := dist_triangle _ _ _
  rw [dist_comm (D.ctr (D.idx i)) ((γs (D.idx i) t).ofLp i)] at h4
  linarith

/-- **The glued curve starts at `x`.** -/
lemma glue_zero {γs : (j : Fin D.K) → ℝ → EN E N}
    (h0 : ∀ j, γs j 0 = x) : D.glue γs 0 = x := by
  refine PiLp.ext fun i => ?_
  rw [glue_apply, h0 (D.idx i)]

/-- **The glued curve ends at `y`.** -/
lemma glue_tau {y : EN E N} {τ : ℝ} {γs : (j : Fin D.K) → ℝ → EN E N}
    (hτ : ∀ j, γs j τ = D.patch y j) : D.glue γs τ = y := by
  refine PiLp.ext fun i => ?_
  rw [glue_apply, hτ (D.idx i)]
  exact D.patch_of_mem y rfl

/-- Every body stays in the ball of radius `14 N R` around the centre of its cluster. -/
def Confined (γs : (j : Fin D.K) → ℝ → EN E N) (t : ℝ) : Prop :=
  ∀ j : Fin D.K, ∀ l : Fin N, D.idx l = j →
    dist ((γs j t).ofLp l) (D.ctr j) ≤ 14 * (N : ℝ) * D.R

/-- **Confinement of the glued curve.** -/
lemma glue_confined {γs : (j : Fin D.K) → ℝ → EN E N}
    (hconf : ∀ j t, ∀ l : Fin N, D.idx l = j →
      dist ((γs j t).ofLp l) (D.ctr j) ≤ 14 * (N : ℝ) * D.R) (t : ℝ) :
    D.Confined γs t := fun j l hjl => hconf j t l hjl

/-- **The glued curve has no collisions.** -/
lemma glue_ae_noColl (hN : 0 < N) (hr : 0 < r) {τ : ℝ} {γs : (j : Fin D.K) → ℝ → EN E N}
    (hnc : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ →
      ∀ j : Fin D.K, ∀ i ∈ D.cl j, ∀ k ∈ D.cl j, i ≠ k → γs j t i ≠ γs j t k)
    (hconf : ∀ j t, ∀ l : Fin N, D.idx l = j →
      dist ((γs j t).ofLp l) (D.ctr j) ≤ 14 * (N : ℝ) * D.R) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ →
      ∀ i k : Fin N, i ≠ k → (D.glue γs t).ofLp i ≠ (D.glue γs t).ofLp k := by
  filter_upwards [hnc] with t ht
  intro hmem i k hik hcontra
  by_cases hidx : D.idx i = D.idx k
  · rw [D.glue_apply, D.glue_apply, ← hidx] at hcontra
    exact ht hmem (D.idx i) i (D.mem_cl_self i) k (by rw [D.mem_cl, hidx]) hik hcontra
  · have hge := D.dist_glue_ge_of_ne (γs := γs) hidx (fun j l hjl => hconf j t l hjl)
    rw [hcontra, dist_self] at hge
    have hN1 : (1 : ℕ) ≤ N := hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hRpos : (0 : ℝ) < D.R := lt_of_lt_of_le hr D.hRge
    have h20 : (0 : ℝ) < 20 := by norm_num
    have hpos : (0 : ℝ) < 20 * (N : ℝ) * D.R := mul_pos (mul_pos h20 hNpos) hRpos
    linarith

/-- **The glued curve is absolutely continuous.** -/
theorem glue_absolutelyContinuous {τ : ℝ} {γs : (j : Fin D.K) → ℝ → EN E N}
    (hac : ∀ j, AbsolutelyContinuousOnInterval (γs j) 0 τ) :
    AbsolutelyContinuousOnInterval (D.glue γs) 0 τ := by
  have hcoord : ∀ i : Fin N,
      AbsolutelyContinuousOnInterval (fun t => (γs (D.idx i) t).ofLp i) 0 τ := by
    intro i
    have hci := hac (D.idx i)
    rw [absolutelyContinuousOnInterval_iff] at hci ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδp⟩ := hci ε hε
    refine ⟨δ, hδ, fun E hE hEd => lt_of_le_of_lt ?_ (hδp E hE hEd)⟩
    refine Finset.sum_le_sum fun k _ => ?_
    have h := norm_apply_le_norm (γs (D.idx i) (E.2 k).1 - γs (D.idx i) (E.2 k).2) i
    rw [PiLp.sub_apply] at h
    simpa only [dist_eq_norm] using h
  refine Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_pi fun i => ?_
  have hfun : (fun t => (D.glue γs t).ofLp i) = fun t => (γs (D.idx i) t).ofLp i := by
    funext t; exact D.glue_apply γs t i
  rw [hfun]
  exact hcoord i

end ClusterData

end Assembly

/-! ## The Lagrangian of the glued curve decomposes into the cluster Lagrangians -/

section Decomposition

variable {x : EN E N} {r : ℝ} (D : ClusterData x r) (m : Fin N → ℝ)
  (γs : (j : Fin D.K) → ℝ → EN E N)

/-- The per-cluster Lagrangian integrand of the glued curve. -/
noncomputable def clusterLag (j : Fin D.K) (t : ℝ) : ℝ :=
  (1 / 2) * (∑ i ∈ D.cl j, m i * ‖(deriv (γs j) t).ofLp i‖ ^ 2)
    + (∑ k ∈ D.cl j, ∑ i ∈ (D.cl j).filter (fun i => i < k),
        m i * m k * (dist ((γs j t).ofLp i) ((γs j t).ofLp k))⁻¹)

/-- The cross-cluster potential integrand of the glued curve. -/
noncomputable def crossLag (t : ℝ) : ℝ :=
  ∑ k, ∑ i ∈ (Finset.Iio k).filter (fun i => D.idx i ≠ D.idx k),
    m i * m k * (dist ((D.glue γs t).ofLp i) ((D.glue γs t).ofLp k))⁻¹

/-- **Kinetic part of the decomposition.** -/
theorem kinetic_glue_eq (t : ℝ) (hdγ : DifferentiableAt ℝ (D.glue γs) t)
    (hdj : ∀ j : Fin D.K, DifferentiableAt ℝ (γs j) t) :
    (1 / 2) * (∑ i, m i * ‖(deriv (D.glue γs) t).ofLp i‖ ^ 2)
      = ∑ j : Fin D.K, (1 / 2) * ∑ i ∈ D.cl j, m i * ‖(deriv (γs j) t).ofLp i‖ ^ 2 := by
  have hderiv : ∀ i : Fin N,
      (deriv (D.glue γs) t).ofLp i = (deriv (γs (D.idx i)) t).ofLp i := by
    intro i
    rw [← Commons.Analysis.Calculus.deriv_ofLp_apply_of_differentiable (D.glue γs) t i hdγ,
      ← Commons.Analysis.Calculus.deriv_ofLp_apply_of_differentiable (γs (D.idx i)) t i
        (hdj (D.idx i))]
    exact congrArg (fun f : ℝ → E => deriv f t) (funext fun s => D.glue_apply γs s i)
  rw [Finset.mul_sum, ← sum_fibre (K := D.K) D.idx
    (fun i => (1 / 2) * (m i * ‖(deriv (D.glue γs) t).ofLp i‖ ^ 2))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hidx : D.idx i = j := (D.mem_cl j i).mp hi
  rw [hderiv i, hidx]

/-- **Potential part of the decomposition.** -/
theorem potential_glue_eq (t : ℝ) :
    (∑ k, ∑ i ∈ Finset.Iio k,
        m i * m k * (dist ((D.glue γs t).ofLp i) ((D.glue γs t).ofLp k))⁻¹)
      = (∑ j : Fin D.K, ∑ k ∈ D.cl j, ∑ i ∈ (D.cl j).filter (fun i => i < k),
            m i * m k * (dist ((γs j t).ofLp i) ((γs j t).ofLp k))⁻¹)
        + crossLag D m γs t := by
  set g : Fin N → Fin N → ℝ :=
    fun i k => m i * m k * (dist ((D.glue γs t).ofLp i) ((D.glue γs t).ofLp k))⁻¹ with hg
  have hsplit : (∑ k, ∑ i ∈ Finset.Iio k, g i k)
      = (∑ k, ∑ i ∈ (Finset.Iio k).filter (fun i => D.idx i = D.idx k), g i k)
        + (∑ k, ∑ i ∈ (Finset.Iio k).filter (fun i => D.idx i ≠ D.idx k), g i k) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Iio k) (fun i => D.idx i = D.idx k)
      (fun i => g i k)]
  have hcross : (∑ k, ∑ i ∈ (Finset.Iio k).filter (fun i => D.idx i ≠ D.idx k), g i k)
      = crossLag D m γs t := rfl
  have hintra : (∑ k, ∑ i ∈ (Finset.Iio k).filter (fun i => D.idx i = D.idx k), g i k)
      = ∑ j : Fin D.K, ∑ k ∈ D.cl j, ∑ i ∈ (D.cl j).filter (fun i => i < k), g i k :=
    (Commons.Data.Finset.sum_fibre_pairwise (K := D.K) D.idx g).symm
  rw [hsplit, hcross, hintra]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k hk => ?_
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : D.idx k = j := (D.mem_cl j k).mp hk
  have hii : D.idx i = j := (D.mem_cl j i).mp (Finset.mem_of_mem_filter i hi)
  rw [hg]
  beta_reduce
  rw [D.glue_apply, D.glue_apply, hik, hii]

/-- **Decomposition of the Lagrangian of the glued curve.** -/
theorem lagR_glue_eq (t : ℝ) (hdγ : DifferentiableAt ℝ (D.glue γs) t)
    (hdj : ∀ j : Fin D.K, DifferentiableAt ℝ (γs j) t) :
    lagR m 0 (D.glue γs t) (deriv (D.glue γs) t)
      = (∑ j : Fin D.K, clusterLag D m γs j t) + crossLag D m γs t := by
  have h1 := kinetic_glue_eq D m γs t hdγ hdj
  have h2 := potential_glue_eq D m γs t
  rw [lagR, U_eq_dist_sum]
  simp only [clusterLag]
  rw [h1, h2, Finset.sum_add_distrib]
  ring

end Decomposition

/-! ## The cross-cluster potential of the glued curve is small -/

section Cross

variable {x : EN E N} {r : ℝ} (D : ClusterData x r) (m : Fin N → ℝ)
  (γs : (j : Fin D.K) → ℝ → EN E N)

/-- **The cross-cluster potential is small.**  If all bodies stay in the ball of radius `14 N R`
around the centre of their cluster, then the cross-cluster potential is at most
`(∑ᵢ mᵢ)²/(20 N R)`. -/
theorem crossLag_le {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) (hN : 0 < N) {t : ℝ}
    (hc : D.Confined γs t) :
    crossLag D m γs t ≤ (∑ i, m i) ^ 2 / (20 * (N : ℝ) * D.R) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hRpos := D.hRpos
  have hden : 0 < 20 * (N : ℝ) * D.R := by positivity
  have hstep : crossLag D m γs t
      ≤ ∑ k : Fin N, ∑ _i ∈ (Finset.Iio k).filter (fun i => D.idx i ≠ D.idx k),
          m _i * m k / (20 * (N : ℝ) * D.R) := by
    unfold crossLag
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun i hi => ?_
    have hne : D.idx i ≠ D.idx k := (Finset.mem_filter.mp hi).2
    have h1 : 20 * (N : ℝ) * D.R
        ≤ dist ((D.glue γs t).ofLp i) ((D.glue γs t).ofLp k) :=
      D.dist_glue_ge_of_ne (γs := γs) hne (fun j l hjl => hc j l hjl)
    have hmik : 0 ≤ m i * m k := mul_nonneg (hm i) (hm k)
    have hinv : (dist ((D.glue γs t).ofLp i) ((D.glue γs t).ofLp k))⁻¹
        ≤ (20 * (N : ℝ) * D.R)⁻¹ := inv_anti₀ hden h1
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hmik
  refine hstep.trans ?_
  have hsplit : (∑ k : Fin N, ∑ _i ∈ (Finset.Iio k).filter (fun i => D.idx i ≠ D.idx k),
        m _i * m k / (20 * (N : ℝ) * D.R))
      = (∑ k : Fin N, ∑ _i ∈ (Finset.Iio k).filter (fun i => D.idx i ≠ D.idx k),
        m _i * m k) / (20 * (N : ℝ) * D.R) := by
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
  rw [hsplit]
  refine div_le_div_of_nonneg_right ?_ hden.le
  calc (∑ k : Fin N, ∑ _i ∈ (Finset.Iio k).filter (fun i => D.idx i ≠ D.idx k), m _i * m k)
      ≤ ∑ k : Fin N, ∑ _i ∈ Finset.Iio k, m _i * m k :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun i _ _ => mul_nonneg (hm i) (hm k))
    _ ≤ ∑ k : Fin N, ∑ _i : Fin N, m _i * m k :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) (fun i _ _ => mul_nonneg (hm i) (hm k))
    _ = (∑ i, m i) ^ 2 := by
        rw [pow_two, Finset.sum_mul_sum]
        exact Finset.sum_comm

end Cross

/-! ## Maderna's fixed-time estimate -/

section Main

/-- **Existence of the cluster curves.**  Given `r > ‖x - y‖` and the same-ball estimate `hSB`,
there is a cluster partition `D` of the bodies together with, for each cluster, a curve realising
the same-ball estimate. -/
theorem exists_cluster_curves {m : Fin N → ℝ} (hN : 0 < N) (hm : ∀ i, 0 < m i)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hSB : SubBallEstimate (E := E) c₁ c₂)
    {x y : EN E N} {r τ : ℝ} (hr : ‖x - y‖ < r) (hr0 : 0 < r) (hτ : 0 < τ) :
    ∃ D : ClusterData x r, ∃ γs : (j : Fin D.K) → ℝ → EN E N,
      (∀ j, γs j 0 = x) ∧
      (∀ j, γs j τ = D.patch y j) ∧
      (∀ j, AbsolutelyContinuousOnInterval (γs j) 0 τ) ∧
      (∀ j, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ →
        ∀ i ∈ D.cl j, ∀ k ∈ D.cl j, i ≠ k → γs j t i ≠ γs j t k) ∧
      (∀ j t, ∀ l : Fin N, D.idx l = j →
        dist ((γs j t).ofLp l) (D.ctr j) ≤ 14 * (N : ℝ) * D.R) ∧
      (∀ j, IntegrableOn (fun t => (1 / 2) * (∑ i ∈ D.cl j, m i * ‖deriv (γs j) t i‖ ^ 2)
        + (∑ k ∈ D.cl j, ∑ i ∈ (D.cl j).filter (fun i => i < k),
            m i * m k * (dist (γs j t i) (γs j t k))⁻¹)) (Set.Ioc 0 τ)) ∧
      (∀ j, (∫ t in (0 : ℝ)..τ, ((1 / 2) * (∑ i ∈ D.cl j, m i * ‖deriv (γs j) t i‖ ^ 2)
        + (∑ k ∈ D.cl j, ∑ i ∈ (D.cl j).filter (fun i => i < k),
            m i * m k * (dist (γs j t i) (γs j t k))⁻¹)))
        ≤ c₁ * (∑ i ∈ D.cl j, m i) * (N : ℝ) ^ 4 * (2 * D.R) ^ 2 / τ
            + c₂ * (∑ i ∈ D.cl j, m i) ^ 2 * (N : ℝ) ^ 4 * τ / (2 * D.R)) := by
  classical
  obtain ⟨D⟩ := exists_clusterData (E := E) (x := x) (r := r) hN hr0
  have hRpos : (0 : ℝ) < D.R := lt_of_lt_of_le hr0 D.hRge
  have hcurve : ∀ j : Fin D.K, ∃ γ : ℝ → EN E N,
      γ 0 = x ∧ γ τ = D.patch y j ∧
      (∀ t, ∀ i, i ∉ D.cl j → γ t i = x i) ∧
      (∀ t, ∀ i, i ∈ D.cl j → dist ((γ t).ofLp i) (D.ctr j) ≤ 7 * (N : ℝ) * (2 * D.R)) ∧
      AbsolutelyContinuousOnInterval γ 0 τ ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ →
        ∀ i ∈ D.cl j, ∀ k ∈ D.cl j, i ≠ k → γ t i ≠ γ t k) ∧
      IntegrableOn (fun t => (1 / 2) * (∑ i ∈ D.cl j, m i * ‖deriv γ t i‖ ^ 2)
        + (∑ k ∈ D.cl j, ∑ i ∈ (D.cl j).filter (fun i => i < k),
            m i * m k * (dist (γ t i) (γ t k))⁻¹)) (Set.Ioc 0 τ) ∧
      (∫ t in (0 : ℝ)..τ, ((1 / 2) * (∑ i ∈ D.cl j, m i * ‖deriv γ t i‖ ^ 2)
        + (∑ k ∈ D.cl j, ∑ i ∈ (D.cl j).filter (fun i => i < k),
            m i * m k * (dist (γ t i) (γ t k))⁻¹)))
        ≤ c₁ * (∑ i ∈ D.cl j, m i) * (N : ℝ) ^ 4 * (2 * D.R) ^ 2 / τ
            + c₂ * (∑ i ∈ D.cl j, m i) ^ 2 * (N : ℝ) ^ 4 * τ / (2 * D.R) := by
    intro j
    refine hSB m hm (D.cl j) x (D.patch y j) (D.ctr j) (R := 2 * D.R) (τ := τ)
      (by linarith) hτ ?_ ?_ ?_
    · intro i hi
      have h1 : D.idx i = j := (D.mem_cl j i).mp hi
      have hx := D.hidx i
      rw [h1] at hx
      linarith [hx, D.hRpos]
    · intro i hi
      have h1 : D.idx i = j := (D.mem_cl j i).mp hi
      have hy : dist ((D.patch y j) i) (x i) ≤ ‖x - y‖ := by
        rw [D.patch_of_mem y h1, dist_eq_norm, norm_sub_rev]
        exact norm_apply_le_norm (x - y) i
      have hx := D.hidx i
      rw [h1] at hx
      have htri : dist ((D.patch y j) i) (D.ctr j)
          ≤ dist ((D.patch y j) i) (x i) + dist (x i) (D.ctr j) := dist_triangle _ _ _
      linarith [hx, D.hRpos, hy, hr, htri, D.hRge]
    · intro i hi
      simp only [D.patch_apply]
      rw [if_neg]
      intro hcontra
      exact hi ((D.mem_cl j i).mpr hcontra)
  choose γs h0s hτs houts hconfs hacs hncs hInts hbnds using hcurve
  refine ⟨D, γs, h0s, hτs, hacs, hncs, ?_, ?_, ?_⟩
  · intro j t l hl
    have h := hconfs j t l ((D.mem_cl j l).mpr hl)
    rwa [show 7 * (N : ℝ) * (2 * D.R) = 14 * (N : ℝ) * D.R from by ring] at h
  · intro j
    exact hInts j
  · intro j
    exact hbnds j

end Main

/-! ## The final assembly of Maderna's fixed-time estimate -/

section Final

variable {m : Fin N → ℝ}

/-- **Maderna's fixed-time estimate.**  If `r > ‖x - y‖` then for every `τ > 0` there is a curve of
duration `τ` from `x` to `y` whose action is at most `α₁ r²/τ + β₁ τ/r`; equivalently `φ(x,y,τ)`
satisfies this bound. -/
theorem actionPotTau_le_of_lt_dist (hN : 0 < N) (hm : ∀ i, 0 < m i)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hSB : SubBallEstimate (E := E) c₁ c₂)
    {x y : EN E N} {r τ : ℝ} (hr : ‖x - y‖ < r) (hr0 : 0 < r) (hτ : 0 < τ) :
    actionPotTau m x y τ ≤ ENNReal.ofReal
      ((4 * c₁ * (N : ℝ) ^ 4 * (48 * (N : ℝ)) ^ (2 * N) * (∑ i, m i)) * r ^ 2 / τ
        + (c₂ * (N : ℝ) ^ 4 * (∑ i, m i) ^ 2 / 2
            + (∑ i, m i) ^ 2 / (20 * (N : ℝ))) * τ / r) := by
  classical
  obtain ⟨D, γs, h0s, hτs, hacs, hncs, hconfs, hInts, hbnds⟩ :=
    exists_cluster_curves (E := E) hN hm hc₁ hc₂ hSB hr hr0 hτ
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hRpos : (0 : ℝ) < D.R := lt_of_lt_of_le hr0 D.hRge
  set M : ℝ := ∑ i, m i with hM
  have hMnn : 0 ≤ M := Finset.sum_nonneg fun i _ => (hm i).le
  have hconf14 : ∀ j t, ∀ l : Fin N, D.idx l = j →
      dist ((γs j t).ofLp l) (D.ctr j) ≤ 14 * (N : ℝ) * D.R := hconfs
  -- the glued curve
  have hacγ : AbsolutelyContinuousOnInterval (D.glue γs) 0 τ := D.glue_absolutelyContinuous hacs
  have hncall : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ →
      ∀ j : Fin D.K, ∀ i ∈ D.cl j, ∀ k ∈ D.cl j, i ≠ k → γs j t i ≠ γs j t k := by
    have hall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ j : Fin D.K, t ∈ Set.Ioc 0 τ →
        ∀ i ∈ D.cl j, ∀ k ∈ D.cl j, i ≠ k → γs j t i ≠ γs j t k :=
      Filter.eventually_all.mpr hncs
    filter_upwards [hall] with t ht
    intro hmem j i hi k hk hik
    exact ht j hmem i hi k hk hik
  have hncγ : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ →
      ∀ i k : Fin N, i ≠ k → (D.glue γs t).ofLp i ≠ (D.glue γs t).ofLp k :=
    D.glue_ae_noColl hN hr0 hncall hconf14
  -- almost everywhere differentiability
  have haed : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ →
      DifferentiableAt ℝ (D.glue γs) t ∧ ∀ j : Fin D.K, DifferentiableAt ℝ (γs j) t := by
    have h1 : ∀ᵐ t ∂(volume : Measure ℝ),
        t ∈ Set.Ioc 0 τ → DifferentiableAt ℝ (D.glue γs) t := by
      have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_ae_differentiableAt_vector
        (f := D.glue γs) hacγ
      filter_upwards [h] with t ht hmem
      exact ht (by rw [Set.uIcc_of_le hτ.le]; exact ⟨le_of_lt hmem.1, hmem.2⟩)
    have h2 : ∀ᵐ t ∂(volume : Measure ℝ),
        t ∈ Set.Ioc 0 τ → ∀ j : Fin D.K, DifferentiableAt ℝ (γs j) t := by
      have hall : ∀ᵐ t ∂(volume : Measure ℝ),
          ∀ j : Fin D.K, t ∈ Set.Ioc 0 τ → DifferentiableAt ℝ (γs j) t := by
        refine Filter.eventually_all.mpr fun j => ?_
        have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_ae_differentiableAt_vector
          (f := γs j) (hacs j)
        filter_upwards [h] with t ht hmem
        exact ht (by rw [Set.uIcc_of_le hτ.le]; exact ⟨le_of_lt hmem.1, hmem.2⟩)
      filter_upwards [hall] with t ht hmem j
      exact ht j hmem
    filter_upwards [h1, h2] with t h1t h2t hmem
    exact ⟨h1t hmem, h2t hmem⟩
  -- the pointwise decomposition, almost everywhere
  have hae : (fun t => lagR m 0 (D.glue γs t) (deriv (D.glue γs) t))
      =ᵐ[volume.restrict (Set.Ioc 0 τ)]
        fun t => (∑ j : Fin D.K, clusterLag D m γs j t) + crossLag D m γs t := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [haed] with t ht hmem
    exact lagR_glue_eq D m γs t (ht hmem).1 (ht hmem).2
  -- integrability
  have hIcl : ∀ j : Fin D.K, IntervalIntegrable (fun t => clusterLag D m γs j t) volume 0 τ := by
    intro j
    rw [intervalIntegrable_iff, Set.uIoc_of_le hτ.le]
    exact hInts j
  have hIsum : IntervalIntegrable (fun t => ∑ j : Fin D.K, clusterLag D m γs j t) volume 0 τ := by
    have h := IntervalIntegrable.sum Finset.univ fun j _ => hIcl j
    have hfun : (∑ j : Fin D.K, fun t => clusterLag D m γs j t)
        = fun t => ∑ j : Fin D.K, clusterLag D m γs j t := by
      funext t
      simp only [Finset.sum_apply]
    rwa [hfun] at h
  have hcont_cross : ContinuousOn (fun t => crossLag D m γs t) (Set.uIcc 0 τ) := by
    unfold crossLag
    refine continuousOn_finset_sum Finset.univ fun k _ =>
      continuousOn_finset_sum _ fun i hi => ?_
    have hne : D.idx i ≠ D.idx k := (Finset.mem_filter.mp hi).2
    have hsub : ContinuousOn
        (fun t => (D.glue γs t).ofLp i - (D.glue γs t).ofLp k) (Set.uIcc 0 τ) :=
      (((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).comp_continuousOn hacγ.continuousOn).sub
        ((PiLp.continuous_apply 2 (fun _ : Fin N => E) k).comp_continuousOn hacγ.continuousOn))
    have hdist : ContinuousOn (fun t => dist ((D.glue γs t).ofLp i) ((D.glue γs t).ofLp k))
        (Set.uIcc 0 τ) := by
      simpa only [dist_eq_norm] using hsub.norm
    refine (ContinuousOn.inv₀ hdist fun t _ => ?_).const_mul (m i * m k)
    have hge := D.dist_glue_ge_of_ne (γs := γs) hne (fun j l hjl => hconf14 j t l hjl)
    exact ne_of_gt (lt_of_lt_of_le (by positivity) hge)
  have hIcross : IntervalIntegrable (fun t => crossLag D m γs t) volume 0 τ :=
    hcont_cross.intervalIntegrable
  have hB : IntervalIntegrable
      (fun t => (∑ j : Fin D.K, clusterLag D m γs j t) + crossLag D m γs t) volume 0 τ :=
    hIsum.add hIcross
  have hIntlag : Integrable (fun t => lagR m 0 (D.glue γs t) (deriv (D.glue γs) t))
      (volume.restrict (Set.Ioc 0 τ)) := by
    have hB' : Integrable
        (fun t => (∑ j : Fin D.K, clusterLag D m γs j t) + crossLag D m γs t)
        (volume.restrict (Set.Ioc 0 τ)) := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hτ.le] at hB
      exact hB
    exact hB'.congr hae.symm
  -- the two parts of the integral
  have hIsum' : Integrable (fun t => ∑ j : Fin D.K, clusterLag D m γs j t)
      (volume.restrict (Set.Ioc 0 τ)) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hτ.le] at hIsum
    exact hIsum
  have hIcross' : Integrable (fun t => crossLag D m γs t) (volume.restrict (Set.Ioc 0 τ)) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hτ.le] at hIcross
    exact hIcross
  have hIcl' : ∀ j : Fin D.K,
      Integrable (fun t => clusterLag D m γs j t) (volume.restrict (Set.Ioc 0 τ)) := by
    intro j
    have h := hIcl j
    rw [intervalIntegrable_iff, Set.uIoc_of_le hτ.le] at h
    exact h
  have hpoint : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ →
      lagR m 0 (D.glue γs t) (deriv (D.glue γs) t)
        = (∑ j : Fin D.K, clusterLag D m γs j t) + crossLag D m γs t := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hae
    exact hae
  have hint_eq : ∫ t in Set.Ioc (0:ℝ) τ, lagR m 0 (D.glue γs t) (deriv (D.glue γs) t)
      = (∑ j : Fin D.K, ∫ t in Set.Ioc (0:ℝ) τ, clusterLag D m γs j t)
        + ∫ t in Set.Ioc (0:ℝ) τ, crossLag D m γs t := by
    rw [MeasureTheory.integral_congr_ae hae]
    rw [MeasureTheory.integral_add hIsum' hIcross']
    congr 1
    exact MeasureTheory.integral_finset_sum Finset.univ fun j _ => hIcl' j
  -- back to interval integrals
  have hint_eq2 : ∫ t in (0:ℝ)..τ, lagR m 0 (D.glue γs t) (deriv (D.glue γs) t)
      = (∑ j : Fin D.K, ∫ t in (0:ℝ)..τ, clusterLag D m γs j t)
        + ∫ t in (0:ℝ)..τ, crossLag D m γs t := by
    rw [intervalIntegral.integral_of_le hτ.le, hint_eq]
    simp only [← intervalIntegral.integral_of_le hτ.le]
  -- the cluster part
  have hM_j : ∀ j : Fin D.K, 0 ≤ ∑ i ∈ D.cl j, m i := fun j =>
    Finset.sum_nonneg fun i _ => (hm i).le
  have hsum_M : (∑ j : Fin D.K, ∑ i ∈ D.cl j, m i) = M := by
    rw [hM]; exact sum_fibre D.idx m
  have hSum1 : (∑ j : Fin D.K, ∫ t in (0:ℝ)..τ, clusterLag D m γs j t)
      ≤ c₁ * (N : ℝ) ^ 4 * M * (2 * D.R) ^ 2 / τ
        + c₂ * (N : ℝ) ^ 4 * M ^ 2 * τ / (2 * D.R) := by
    refine (Finset.sum_le_sum fun j _ => hbnds j).trans ?_
    have hc1 : 0 ≤ c₁ * (N : ℝ) ^ 4 * (2 * D.R) ^ 2 / τ := by positivity
    have hc2 : 0 ≤ c₂ * (N : ℝ) ^ 4 * τ / (2 * D.R) := by positivity
    have hsq : (∑ j : Fin D.K, (∑ i ∈ D.cl j, m i) ^ 2) ≤ M ^ 2 := by
      rw [← hsum_M]
      exact Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => hM_j j
    have hsplit : (∑ j : Fin D.K,
          (c₁ * (∑ i ∈ D.cl j, m i) * (N : ℝ) ^ 4 * (2 * D.R) ^ 2 / τ
            + c₂ * (∑ i ∈ D.cl j, m i) ^ 2 * (N : ℝ) ^ 4 * τ / (2 * D.R)))
        = c₁ * (N : ℝ) ^ 4 * (2 * D.R) ^ 2 / τ * (∑ j : Fin D.K, ∑ i ∈ D.cl j, m i)
          + c₂ * (N : ℝ) ^ 4 * τ / (2 * D.R)
              * (∑ j : Fin D.K, (∑ i ∈ D.cl j, m i) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by ring
      · exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit, hsum_M]
    have hstep : c₂ * (N : ℝ) ^ 4 * τ / (2 * D.R) * (∑ j : Fin D.K, (∑ i ∈ D.cl j, m i) ^ 2)
        ≤ c₂ * (N : ℝ) ^ 4 * τ / (2 * D.R) * M ^ 2 := mul_le_mul_of_nonneg_left hsq hc2
    have e1 : c₁ * (N : ℝ) ^ 4 * (2 * D.R) ^ 2 / τ * M
        = c₁ * (N : ℝ) ^ 4 * M * (2 * D.R) ^ 2 / τ := by ring
    have e2 : c₂ * (N : ℝ) ^ 4 * τ / (2 * D.R) * M ^ 2
        = c₂ * (N : ℝ) ^ 4 * M ^ 2 * τ / (2 * D.R) := by ring
    rw [e2] at hstep
    rw [e1]
    exact add_le_add le_rfl hstep
  -- the cross part
  have hSum2 : ∫ t in (0:ℝ)..τ, crossLag D m γs t
      ≤ M ^ 2 / (20 * (N : ℝ) * D.R) * τ := by
    have hle : ∀ t, crossLag D m γs t ≤ M ^ 2 / (20 * (N : ℝ) * D.R) := fun t =>
      crossLag_le (D := D) (m := m) (γs := γs) (fun i => (hm i).le) hN
        (fun j l hjl => hconf14 j t l hjl)
    have hIconst : IntervalIntegrable (fun _ : ℝ => M ^ 2 / (20 * (N : ℝ) * D.R)) volume 0 τ :=
      intervalIntegrable_const
    have h := intervalIntegral.integral_mono hτ.le hIcross hIconst (fun t => hle t)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm] at h
    exact h
  -- the final bound
  have hfinal : ∫ t in (0:ℝ)..τ, lagR m 0 (D.glue γs t) (deriv (D.glue γs) t)
      ≤ 4 * c₁ * (N : ℝ) ^ 4 * (48 * (N : ℝ)) ^ (2 * N) * M * r ^ 2 / τ
        + (c₂ * (N : ℝ) ^ 4 * M ^ 2 / 2 + M ^ 2 / (20 * (N : ℝ))) * τ / r := by
    rw [hint_eq2]
    have hR2 : (2 * D.R) ^ 2 ≤ 4 * (48 * (N : ℝ)) ^ (2 * N) * r ^ 2 := by
      have h1 : D.R ^ 2 ≤ ((48 * (N : ℝ)) ^ N * r) ^ 2 := by
        exact pow_le_pow_left₀ D.hRpos.le D.hRle 2
      calc (2 * D.R) ^ 2 = 4 * D.R ^ 2 := by ring
        _ ≤ 4 * ((48 * (N : ℝ)) ^ N * r) ^ 2 := by linarith
        _ = 4 * (48 * (N : ℝ)) ^ (2 * N) * r ^ 2 := by
              rw [mul_pow, ← pow_mul]; ring
    have e1 : c₁ * (N : ℝ) ^ 4 * M * (2 * D.R) ^ 2 / τ
        ≤ 4 * c₁ * (N : ℝ) ^ 4 * (48 * (N : ℝ)) ^ (2 * N) * M * r ^ 2 / τ := by
      have hc : (0:ℝ) ≤ c₁ * (N : ℝ) ^ 4 * M := by positivity
      have hmul := mul_le_mul_of_nonneg_left hR2 hc
      have hgoal : c₁ * (N : ℝ) ^ 4 * M * (2 * D.R) ^ 2
          ≤ 4 * c₁ * (N : ℝ) ^ 4 * (48 * (N : ℝ)) ^ (2 * N) * M * r ^ 2 := by
        calc c₁ * (N : ℝ) ^ 4 * M * (2 * D.R) ^ 2
            = (c₁ * (N : ℝ) ^ 4 * M) * (2 * D.R) ^ 2 := by ring
          _ ≤ (c₁ * (N : ℝ) ^ 4 * M) * (4 * (48 * (N : ℝ)) ^ (2 * N) * r ^ 2) := hmul
          _ = 4 * c₁ * (N : ℝ) ^ 4 * (48 * (N : ℝ)) ^ (2 * N) * M * r ^ 2 := by ring
      exact div_le_div_of_nonneg_right hgoal hτ.le
    have e2 : c₂ * (N : ℝ) ^ 4 * M ^ 2 * τ / (2 * D.R)
        ≤ c₂ * (N : ℝ) ^ 4 * M ^ 2 / 2 * τ / r := by
      have hnum : (0:ℝ) ≤ c₂ * (N : ℝ) ^ 4 * M ^ 2 * τ := by positivity
      have hden : 2 * r ≤ 2 * D.R := by linarith [D.hRge]
      have h1 : c₂ * (N : ℝ) ^ 4 * M ^ 2 * τ / (2 * D.R)
          ≤ c₂ * (N : ℝ) ^ 4 * M ^ 2 * τ / (2 * r) :=
        div_le_div_of_nonneg_left hnum (by linarith) hden
      have h2 : c₂ * (N : ℝ) ^ 4 * M ^ 2 * τ / (2 * r)
          = c₂ * (N : ℝ) ^ 4 * M ^ 2 / 2 * τ / r := by ring
      rwa [h2] at h1
    have e3 : M ^ 2 / (20 * (N : ℝ) * D.R) * τ ≤ M ^ 2 / (20 * (N : ℝ)) * τ / r := by
      have hnum : (0:ℝ) ≤ M ^ 2 * τ := by positivity
      have hden : 20 * (N : ℝ) * r ≤ 20 * (N : ℝ) * D.R := by
        have := D.hRge; nlinarith [hNpos, hr0]
      have h1 : M ^ 2 * τ / (20 * (N : ℝ) * D.R) ≤ M ^ 2 * τ / (20 * (N : ℝ) * r) :=
        div_le_div_of_nonneg_left hnum (by positivity) hden
      have h2 : M ^ 2 / (20 * (N : ℝ) * D.R) * τ = M ^ 2 * τ / (20 * (N : ℝ) * D.R) := by ring
      have h3 : M ^ 2 / (20 * (N : ℝ)) * τ / r = M ^ 2 * τ / (20 * (N : ℝ) * r) := by ring
      rw [h2, h3]
      exact h1
    have e4 : (c₂ * (N : ℝ) ^ 4 * M ^ 2 / 2 + M ^ 2 / (20 * (N : ℝ))) * τ / r
        = c₂ * (N : ℝ) ^ 4 * M ^ 2 / 2 * τ / r + M ^ 2 / (20 * (N : ℝ)) * τ / r := by ring
    rw [e4]
    linarith [hSum1, hSum2, e1, e2, e3]
  -- the bridge
  have hncγ' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc 0 τ → WithoutCollisions (D.glue γs t) := by
    filter_upwards [hncγ] with t ht hmem i j hij hd
    refine ht hmem i j hij ?_
    rw [ViscositySolutions.r, dist_eq_zero] at hd
    exact hd
  exact actionPotTau_le_ofReal_of_integral_lagR hτ (fun i => (hm i).le) (D.glue_zero h0s)
    (D.glue_tau hτs) hacγ hncγ' hIntlag hfinal


end Final

/-! ## `thm-phih.estim` from the same-ball estimate -/

section Holder

/-- **The Hölder estimate for `φ_h`** (`thm-phih.estim` of Maderna–Venturelli), deduced from the
same-ball estimate via Maderna's fixed-time estimate. -/
theorem actionPot_le_holder_of_subBallEstimate {m : Fin N → ℝ} (hN : 0 < N)
    (hm : ∀ i, 0 < m i) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hSB : SubBallEstimate (E := E) c₁ c₂) {h : ℝ} (hh : 0 ≤ h) (x y : EN E N) :
    actionPot m h x y ≤ ENNReal.ofReal
      (Real.sqrt (4 * (4 * c₁ * (N : ℝ) ^ 4 * (48 * (N : ℝ)) ^ (2 * N) * (∑ i, m i))
          * (c₂ * (N : ℝ) ^ 4 * (∑ i, m i) ^ 2 / 2 + (∑ i, m i) ^ 2 / (20 * (N : ℝ)))
          * ‖x - y‖
        + 4 * (4 * c₁ * (N : ℝ) ^ 4 * (48 * (N : ℝ)) ^ (2 * N) * (∑ i, m i)) * h
          * ‖x - y‖ ^ 2)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMpos : 0 < ∑ i, m i :=
    Finset.sum_pos (fun i _ => hm i) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  refine actionPot_le_holder_of_actionPotTau_bound (fun i => (hm i).le) hh
    (α₁ := 4 * c₁ * (N : ℝ) ^ 4 * (48 * (N : ℝ)) ^ (2 * N) * (∑ i, m i))
    (β₁ := c₂ * (N : ℝ) ^ 4 * (∑ i, m i) ^ 2 / 2 + (∑ i, m i) ^ 2 / (20 * (N : ℝ)))
    ?_ ?_ ?_ x y
  · have h1 : (0:ℝ) < (48 * (N : ℝ)) ^ (2 * N) := by positivity
    positivity
  · have : (0:ℝ) < (∑ i, m i) ^ 2 := by positivity
    positivity
  · intro p q r hr τ hτ
    exact actionPotTau_le_of_lt_dist hN hm hc₁ hc₂ hSB hr
      (lt_of_le_of_lt (norm_nonneg _) hr) hτ

end Holder

/-! ## Discharging the same-ball hypothesis -/

section Discharge

/-- **The same-ball estimate holds with universal constants.** -/
theorem exists_subBallEstimate :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ SubBallEstimate (E := E) c₁ c₂ := by
  obtain ⟨c₁, c₂, h1, h2, h⟩ := Commons.Topology.Metric.exists_path_sub_ball_action_bound
  exact ⟨c₁, c₂, h1, h2, fun {N'} m' hm' s x y r₀ R τ hR hτ hx hy hout =>
    h m' hm' s x y r₀ hR hτ hx hy hout⟩

/-- **The Hölder estimate for `φ_h`** (`thm-phih.estim`), unconditionally. -/
theorem actionPot_le_holder {m : Fin N → ℝ} (hN : 0 < N) (hm : ∀ i, 0 < m i)
    {h : ℝ} (hh : 0 ≤ h) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ x y : EN E N,
      actionPot m h x y ≤ ENNReal.ofReal
        (Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2)) := by
  classical
  obtain ⟨c₁, c₂, hc₁, hc₂, hSB⟩ := exists_subBallEstimate (E := E)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMpos : 0 < ∑ i, m i :=
    Finset.sum_pos (fun i _ => hm i) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hApos : (0:ℝ) < 4 * c₁ * (N : ℝ) ^ 4 * (48 * (N : ℝ)) ^ (2 * N) * (∑ i, m i) := by
    have : (0:ℝ) < (48 * (N : ℝ)) ^ (2 * N) := by positivity
    positivity
  have hBpos : (0:ℝ) < c₂ * (N : ℝ) ^ 4 * (∑ i, m i) ^ 2 / 2
      + (∑ i, m i) ^ 2 / (20 * (N : ℝ)) := by
    have : (0:ℝ) < (∑ i, m i) ^ 2 := by positivity
    positivity
  refine ⟨4 * (4 * c₁ * (N : ℝ) ^ 4 * (48 * (N : ℝ)) ^ (2 * N) * (∑ i, m i))
      * (c₂ * (N : ℝ) ^ 4 * (∑ i, m i) ^ 2 / 2 + (∑ i, m i) ^ 2 / (20 * (N : ℝ))),
    4 * (4 * c₁ * (N : ℝ) ^ 4 * (48 * (N : ℝ)) ^ (2 * N) * (∑ i, m i)),
    by positivity, by positivity, fun x y => ?_⟩
  have hmain := actionPot_le_holder_of_subBallEstimate hN hm hc₁ hc₂ hSB hh x y
  convert hmain using 3
  ring

end Discharge

/-! ## Horofunctions exist -/

section Horo

/-- **The ideal boundary of the positive energy level is non-empty** (the first step of the proof of
Theorem 1.1 of Maderna–Venturelli): the normalised action potentials
`x ↦ φ_h(x, n·a) - φ_h(0, n·a)` have a subsequence converging uniformly on compact sets to a
function dominated by `L + h` and vanishing at `0`. -/
theorem exists_horofunction_of_masses {m : Fin N → ℝ} (hN : 0 < N) (hm : ∀ i, 0 < m i)
    {h : ℝ} (hh : 0 ≤ h) (a : EN E N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ 𝔲 : EN E N → ℝ,
      (∀ K : Set (EN E N), IsCompact K → TendstoUniformlyOn
        (fun k x => (actionPot m h x ((φ k : ℝ) • a)).toReal
          - (actionPot m h 0 ((φ k : ℝ) • a)).toReal) 𝔲 atTop K) ∧
      Dominated m h 𝔲 ∧ 𝔲 0 = 0 := by
  obtain ⟨α, β, hα, hβ, hest⟩ := actionPot_le_holder (E := E) hN hm hh
  exact exists_horofunction (m := m) (h := h) (a := a) hh hα hβ hest

end Horo

/-! ## `φ_h(x,x) = 0` for every configuration -/

section SelfZero

/-- **`φ_h(x,x) = 0` for every configuration**, with or without collisions. -/
theorem actionPot_self_eq_zero' {m : Fin N → ℝ} {h : ℝ} (hN : 0 < N) (hm : ∀ i, 0 < m i)
    (hh : 0 ≤ h) (x : EN E N) : actionPot m h x x = 0 := by
  haveI : Nontrivial (EN E N) :=
    Function.Injective.nontrivial (f := fun v : E => (PiLp.single 2 ⟨0, hN⟩ v : EN E N))
      (fun a b hab => by
        have := congrArg (fun z : EN E N => z.ofLp ⟨0, hN⟩) hab
        simpa using this)
  obtain ⟨α, β, hα, hβ, hest⟩ := actionPot_le_holder (E := E) hN hm hh
  obtain ⟨e, he⟩ := exists_ne (0 : EN E N)
  have hen : 0 < ‖e‖ := norm_pos_iff.mpr he
  set w : EN E N := ‖e‖⁻¹ • e with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hen, inv_mul_cancel₀ hen.ne']
  refine le_antisymm ?_ bot_le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεr : (0:ℝ) < (ε : ℝ) := by exact_mod_cast hε
  set δ : ℝ := min 1 ((ε:ℝ) ^ 2 / (4 * (α + h * β + 1))) with hδdef
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδle1 : δ ≤ 1 := min_le_left _ _
  have hδle : δ ≤ (ε:ℝ) ^ 2 / (4 * (α + h * β + 1)) := min_le_right _ _
  have hαβ : 0 ≤ α + h * β := by nlinarith [mul_nonneg hh hβ.le]
  have hden : 0 < 4 * (α + h * β + 1) := by positivity
  have hδe : δ * (4 * (α + h * β + 1)) ≤ (ε:ℝ) ^ 2 := by
    rw [le_div_iff₀ hden] at hδle
    linarith
  have hsqrt : 2 * Real.sqrt (α * δ + h * β * δ ^ 2) < (ε:ℝ) := by
    have h1 : α * δ + h * β * δ ^ 2 ≤ (α + h * β) * δ := by
      have hβ0 : 0 ≤ h * β := mul_nonneg hh hβ.le
      nlinarith [hδpos, hδle1, hβ0, sq_nonneg δ, hα.le, mul_nonneg hα.le hδpos.le,
        mul_nonneg hβ0 hδpos.le]
    have h2 : (α + h * β) * δ * 4 < (ε:ℝ) ^ 2 := by nlinarith [hδe]
    have h3 : Real.sqrt (α * δ + h * β * δ ^ 2) ^ 2 ≤ (α + h * β) * δ := by
      rw [Real.sq_sqrt (by positivity)]
      exact h1
    have h4 : 0 < 2 * Real.sqrt (α * δ + h * β * δ ^ 2) := by
      have : 0 < α * δ + h * β * δ ^ 2 := by positivity
      positivity
    nlinarith [h3, h4, hεr]
  set y : EN E N := x + δ • w with hydef
  have hxy : ‖x - y‖ ≤ δ := by
    have h1 : x - y = (-δ) • w := by
      rw [hydef, sub_eq_add_neg, neg_add, ← add_assoc, add_neg_cancel, zero_add, neg_smul]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hδpos, hw1, mul_one]
  have hmono : Real.sqrt (α * ‖x - y‖ + h * β * ‖x - y‖ ^ 2)
      ≤ Real.sqrt (α * δ + h * β * δ ^ 2) := by
    refine Real.sqrt_le_sqrt ?_
    have hxy0 : 0 ≤ ‖x - y‖ := norm_nonneg _
    have hβ0 : 0 ≤ h * β := mul_nonneg hh hβ.le
    nlinarith [hxy, hxy0, hδpos, hβ0, hα.le, mul_nonneg hβ0 hxy0, mul_self_le_mul_self hxy0 hxy,
      mul_nonneg hα.le hxy0, mul_nonneg hα.le hδpos.le, mul_nonneg hβ0 hδpos.le]
  have htri : actionPot m h x x ≤ actionPot m h x y + actionPot m h y x :=
    actionPot_triangle m h x y x
  have hcomm : actionPot m h y x = actionPot m h x y := actionPot_comm m h y x
  have hstep : actionPot m h x x
      ≤ ENNReal.ofReal (2 * Real.sqrt (α * δ + h * β * δ ^ 2)) := by
    have h2 : actionPot m h x y ≤ ENNReal.ofReal (Real.sqrt (α * δ + h * β * δ ^ 2)) :=
      (hest x y).trans (ENNReal.ofReal_le_ofReal hmono)
    have h3 : actionPot m h x y + actionPot m h y x ≤ 2 * ENNReal.ofReal (Real.sqrt (α * δ + h * β * δ ^ 2)) := by
      rw [hcomm, two_mul]
      exact add_le_add h2 h2
    refine htri.trans (h3.trans ?_)
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  refine hstep.trans ?_
  rw [show (0 : ℝ≥0∞) + (ε : ℝ≥0∞) = ENNReal.ofReal (ε : ℝ) from by
    rw [zero_add, ENNReal.ofReal_coe_nnreal]]
  exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff hεr).mpr hsqrt)

end SelfZero

end Submission.NBody

