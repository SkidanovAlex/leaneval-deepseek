import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Geometry.Convex.convexHull_eq_image_simplex
import Submission.Commons.Geometry.Convex.john_frame

/-
# John's ellipsoid theorem

For a compact convex set `K` with nonempty interior in a finite-dimensional real inner product
space, there are a centre `c` and an invertible linear map `T` with
`c + T '' closedBall 0 1 ⊆ K ⊆ c + n • (T '' closedBall 0 1)`, where `n` is the dimension.

This file is a self-contained development of the proof, following the classical
maximal-volume-inscribed-ellipsoid argument (F. John 1948).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set Metric Filter
open scoped Topology RealInnerProductSpace Pointwise

namespace Commons.Geometry.Convex.John

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- `E = c + M '' closedBall 0 1` (an ellipsoid) is inscribed in `K`. -/
def IsInscribed (K : Set V) (c : V) (M : V →L[ℝ] V) : Prop := ∀ y, ‖y‖ ≤ 1 → c + M y ∈ K

theorem exists_max_det (K : Set V) (hcomp : IsCompact K)
    (hint : (interior K).Nonempty) :
    ∃ (c : V) (M : V →L[ℝ] V), IsInscribed K c M ∧ M.det ≠ 0 ∧
      ∀ (c' : V) (M' : V →L[ℝ] V), IsInscribed K c' M' → |M'.det| ≤ |M.det| := by
  -- an inscribed ball
  obtain ⟨c₀, hc₀ball⟩ := hint
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hc₀ball
  obtain ⟨ε, hεpos, hεK⟩ := hc₀ball
  set r : ℝ := ε / 2 with hr
  have hrpos : 0 < r := by positivity
  have hrcK : closedBall c₀ r ⊆ K :=
    (Metric.closedBall_subset_ball (by rw [hr]; linarith)).trans hεK
  -- the feasible set
  set S : Set (V × (V →L[ℝ] V)) := {p | IsInscribed K p.1 p.2} with hS
  have hmemS : ∀ p : V × (V →L[ℝ] V), p ∈ S ↔ IsInscribed K p.1 p.2 := fun p => Iff.rfl
  -- S is closed
  have hclosed : IsClosed S := by
    have hset : S = ⋂ y ∈ closedBall (0 : V) 1,
        {p : V × (V →L[ℝ] V) | p.1 + p.2 y ∈ K} := by
      ext p
      simp only [hS, mem_ofPred_eq, mem_iInter, mem_closedBall, dist_zero_right, IsInscribed]
    rw [hset]
    refine isClosed_biInter fun y hy => hcomp.isClosed.preimage ?_
    have h1 : Continuous fun p : V × (V →L[ℝ] V) => p.1 := continuous_fst
    have h2 : Continuous fun p : V × (V →L[ℝ] V) => p.2 y :=
      ((ContinuousLinearMap.apply ℝ V y).continuous).comp continuous_snd
    exact h1.add h2
  -- S is contained in a product of compact sets
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ C := by
    have hb : Bornology.IsBounded K := hcomp.isBounded
    rwa [Metric.isBounded_iff] at hb
  set R : ℝ := max C 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRnn : 0 ≤ R := by linarith
  have hRC : C ≤ R := le_max_left _ _
  have hsub : S ⊆ K ×ˢ closedBall (0 : V →L[ℝ] V) R := by
    rintro ⟨c, M⟩ hcM
    rw [hmemS] at hcM
    refine ⟨by simpa using hcM 0 (by simp), ?_⟩
    rw [mem_closedBall, dist_zero_right]
    refine ContinuousLinearMap.opNorm_le_bound _ hRnn fun y => ?_
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have hnorm : ‖(‖y‖⁻¹ : ℝ) • y‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
      have h1 : c + M ((‖y‖⁻¹ : ℝ) • y) ∈ K := hcM _ (le_of_eq hnorm)
      have h2 : c ∈ K := by simpa using hcM 0 (by simp)
      have h3 : ‖(‖y‖⁻¹ : ℝ) • M y‖ ≤ C := by
        have h4 : dist (c + M ((‖y‖⁻¹ : ℝ) • y)) c ≤ C := hC _ h1 _ h2
        rw [dist_eq_norm, add_sub_cancel_left, map_smul] at h4
        exact h4
      have key : ‖M y‖ = ‖y‖ * ‖(‖y‖⁻¹ : ℝ) • M y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y)),
          ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_mul]
      calc ‖M y‖ = ‖y‖ * ‖(‖y‖⁻¹ : ℝ) • M y‖ := key
        _ ≤ ‖y‖ * C := mul_le_mul_of_nonneg_left h3 (norm_nonneg y)
        _ ≤ ‖y‖ * R := mul_le_mul_of_nonneg_left hRC (norm_nonneg y)
        _ = R * ‖y‖ := by ring
  -- compactness
  have hcompS : IsCompact S :=
    IsCompact.of_isClosed_subset (hcomp.prod (isCompact_closedBall (0 : V →L[ℝ] V) R))
      hclosed hsub
  -- membership of the inscribed ball
  have hball_mem : (c₀, r • (1 : V →L[ℝ] V)) ∈ S := by
    rw [hmemS]
    intro y hy
    refine hrcK ?_
    rw [mem_closedBall, dist_eq_norm]
    have h1 : ((r • (1 : V →L[ℝ] V)) y) = r • y := rfl
    have h2 : c₀ + (r • (1 : V →L[ℝ] V)) y - c₀ = r • y := by rw [h1, add_sub_cancel_left]
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
    exact mul_le_of_le_one_right hrpos.le hy
  -- extreme value theorem
  have hcont : ContinuousOn (fun p : V × (V →L[ℝ] V) => |p.2.det|) S :=
    ((ContinuousLinearMap.continuous_det.comp continuous_snd).abs).continuousOn
  obtain ⟨p, hpS, hpMax⟩ := hcompS.exists_isMaxOn ⟨_, hball_mem⟩ hcont
  have hdet0 : (r • (1 : V →L[ℝ] V)).det ≠ 0 := by
    rw [show (r • (1 : V →L[ℝ] V)).det = r ^ Module.finrank ℝ V by
      simp [ContinuousLinearMap.det, LinearMap.det_smul]]
    exact pow_ne_zero _ (ne_of_gt hrpos)
  refine ⟨p.1, p.2, (hmemS p).mp hpS, ?_, ?_⟩
  · intro hzero
    have hle : |(r • (1 : V →L[ℝ] V)).det| ≤ |p.2.det| := hpMax hball_mem
    rw [hzero, abs_zero] at hle
    have hpos : 0 < |(r • (1 : V →L[ℝ] V)).det| := abs_pos.mpr hdet0
    linarith
  · intro c' M' h'
    exact hpMax ((hmemS (c', M')).mpr h')


/-! ### The Frobenius pairing on endomorphisms

We fix an orthonormal basis `e` of `V` and use the (basis-dependent) Frobenius pairing
`frob e A B = ∑ i, ⟪A (e i), B (e i)⟫`, together with the induced pairing
`pairing (A,a) (B,b) = frob e A B + ⟪a, b⟫` on `(V →L[ℝ] V) × V`.  The usefulness of this pairing is
the identity `frob e A (rankOne u) = ⟪A u, u⟫`: it converts the rank-one operators `u ⊗ u` into
the quadratic forms `u ↦ ⟪A u, u⟫`. -/

section Frobenius

variable {ι : Type*} [Fintype ι]

/-- The rank-one operator `x ↦ ⟪x, u⟫ • u`. -/
def rankOne (u : V) : V →L[ℝ] V :=
  ContinuousLinearMap.smulRight ((InnerProductSpace.toDual ℝ V) u) u

lemma rankOne_apply [CompleteSpace V] (u x : V) : rankOne u x = inner ℝ u x • u := by
  rw [rankOne, ContinuousLinearMap.smulRight_apply]
  congr 1

lemma sum_repr_inner [CompleteSpace V] (e : OrthonormalBasis ι ℝ V) (x : V) :
    x = ∑ i, inner ℝ (e i) x • e i := by
  conv_lhs => rw [← OrthonormalBasis.sum_repr e x]
  exact Finset.sum_congr rfl fun i _ => by rw [OrthonormalBasis.repr_apply_apply]

lemma map_sum_repr [CompleteSpace V] (e : OrthonormalBasis ι ℝ V) (A : V →L[ℝ] V) (x : V) :
    A x = ∑ i, inner ℝ (e i) x • A (e i) := by
  conv_lhs => rw [sum_repr_inner e x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]

/-- The Frobenius pairing of endomorphisms, relative to a fixed orthonormal basis. -/
def frob (e : OrthonormalBasis ι ℝ V) (A B : V →L[ℝ] V) : ℝ :=
  ∑ i, inner ℝ (A (e i)) (B (e i))

lemma frob_comm (e : OrthonormalBasis ι ℝ V) (A B : V →L[ℝ] V) : frob e A B = frob e B A := by
  simp only [frob]
  exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _

lemma frob_add_left (e : OrthonormalBasis ι ℝ V) (A A' B : V →L[ℝ] V) :
    frob e (A + A') B = frob e A B + frob e A' B := by
  simp only [frob, add_apply, inner_add_left, Finset.sum_add_distrib]

lemma frob_add_right (e : OrthonormalBasis ι ℝ V) (A B B' : V →L[ℝ] V) :
    frob e A (B + B') = frob e A B + frob e A B' := by
  rw [frob_comm, frob_add_left, frob_comm e B A, frob_comm e B' A]

lemma frob_smul_left (e : OrthonormalBasis ι ℝ V) (c : ℝ) (A B : V →L[ℝ] V) :
    frob e (c • A) B = c * frob e A B := by
  simp only [frob, smul_apply, inner_smul_left, RCLike.conj_to_real, Finset.mul_sum]

lemma frob_smul_right (e : OrthonormalBasis ι ℝ V) (c : ℝ) (A B : V →L[ℝ] V) :
    frob e A (c • B) = c * frob e A B := by
  rw [frob_comm, frob_smul_left, frob_comm e B A]

lemma frob_self_nonneg (e : OrthonormalBasis ι ℝ V) (A : V →L[ℝ] V) : 0 ≤ frob e A A := by
  simp only [frob]
  exact Finset.sum_nonneg fun i _ => real_inner_self_nonneg

lemma frob_self_eq_zero (e : OrthonormalBasis ι ℝ V) {A : V →L[ℝ] V} (h : frob e A A = 0) :
    A = 0 := by
  simp only [frob] at h
  have h2 : ∀ i, A (e i) = 0 := by
    intro i
    have h1 : inner ℝ (A (e i)) (A (e i)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => real_inner_self_nonneg)).mp h i
        (Finset.mem_univ i)
    simpa using h1
  ext x
  rw [map_sum_repr e A x]
  simp [h2]

/-- The key identity: the Frobenius pairing with a rank-one operator is the corresponding
quadratic form. -/
lemma frob_rankOne [CompleteSpace V] (e : OrthonormalBasis ι ℝ V) (A : V →L[ℝ] V) (u : V) :
    frob e A (rankOne u) = inner ℝ (A u) u := by
  simp only [frob, rankOne_apply, inner_smul_right]
  rw [map_sum_repr e A u, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, RCLike.conj_to_real, real_inner_comm (e i) u]

/-- The pairing on `(V →L[ℝ] V) × V` used for the separating/closest-point argument. -/
def pairing (e : OrthonormalBasis ι ℝ V) (z z' : (V →L[ℝ] V) × V) : ℝ :=
  frob e z.1 z'.1 + inner ℝ z.2 z'.2

lemma pairing_comm (e : OrthonormalBasis ι ℝ V) (z z' : (V →L[ℝ] V) × V) :
    pairing e z z' = pairing e z' z := by
  simp only [pairing]
  rw [frob_comm e z.1 z'.1, real_inner_comm z.2 z'.2]

lemma pairing_add_left (e : OrthonormalBasis ι ℝ V) (z z' w : (V →L[ℝ] V) × V) :
    pairing e (z + z') w = pairing e z w + pairing e z' w := by
  have h1 : (z + z').1 = z.1 + z'.1 := rfl
  have h2 : (z + z').2 = z.2 + z'.2 := rfl
  simp only [pairing, h1, h2, frob_add_left, inner_add_left]
  ring

lemma pairing_smul_left (e : OrthonormalBasis ι ℝ V) (c : ℝ) (z w : (V →L[ℝ] V) × V) :
    pairing e (c • z) w = c * pairing e z w := by
  have h1 : (c • z).1 = c • z.1 := rfl
  have h2 : (c • z).2 = c • z.2 := rfl
  simp only [pairing, h1, h2, frob_smul_left, inner_smul_left, RCLike.conj_to_real]
  ring

lemma pairing_add_right (e : OrthonormalBasis ι ℝ V) (z z' w : (V →L[ℝ] V) × V) :
    pairing e z (z' + w) = pairing e z z' + pairing e z w := by
  have h1 : (z' + w).1 = z'.1 + w.1 := rfl
  have h2 : (z' + w).2 = z'.2 + w.2 := rfl
  simp only [pairing, h1, h2, frob_add_right, inner_add_right]
  ring

lemma pairing_smul_right (e : OrthonormalBasis ι ℝ V) (c : ℝ) (z w : (V →L[ℝ] V) × V) :
    pairing e z (c • w) = c * pairing e z w := by
  rw [pairing_comm e z (c • w), pairing_smul_left, pairing_comm e w z]

lemma pairing_self_nonneg (e : OrthonormalBasis ι ℝ V) (z : (V →L[ℝ] V) × V) :
    0 ≤ pairing e z z := by
  have h1 := frob_self_nonneg e z.1
  have h2 : (0:ℝ) ≤ inner ℝ z.2 z.2 := real_inner_self_nonneg
  simp only [pairing]
  linarith

lemma pairing_self_eq_zero (e : OrthonormalBasis ι ℝ V) {z : (V →L[ℝ] V) × V}
    (h : pairing e z z = 0) : z = 0 := by
  have h1 : frob e z.1 z.1 = 0 := by
    have h2 := frob_self_nonneg e z.1
    have h3 : (0:ℝ) ≤ inner ℝ z.2 z.2 := real_inner_self_nonneg
    simp only [pairing] at h
    linarith
  have h4 : inner ℝ z.2 z.2 = 0 := by
    have h2 := frob_self_nonneg e z.1
    have h3 : (0:ℝ) ≤ inner ℝ z.2 z.2 := real_inner_self_nonneg
    simp only [pairing] at h
    linarith
  have h5 : z.1 = 0 := frob_self_eq_zero e h1
  have h6 : z.2 = 0 := inner_self_eq_zero.mp h4
  exact Prod.ext h5 h6

/-- Expansion of the quadratic form along a line. -/
lemma pairing_quad (e : OrthonormalBasis ι ℝ V) (z w : (V →L[ℝ] V) × V) (s : ℝ) :
    pairing e (z + s • w) (z + s • w) =
      pairing e z z + 2 * s * pairing e z w + s ^ 2 * pairing e w w := by
  have h1 : pairing e (z + s • w) (z + s • w)
      = pairing e z (z + s • w) + s * pairing e w (z + s • w) := by
    rw [pairing_add_left, pairing_smul_left]
  have h2 : pairing e z (z + s • w) = pairing e z z + s * pairing e z w := by
    rw [pairing_add_right, pairing_smul_right]
  have h3 : pairing e w (z + s • w) = pairing e w z + s * pairing e w w := by
    rw [pairing_add_right, pairing_smul_right]
  rw [h1, h2, h3, pairing_comm e w z]
  ring

/-- The rank-one operator depends continuously on its argument. -/
lemma continuous_rankOne [CompleteSpace V] :
    Continuous fun u : V => (rankOne u : V →L[ℝ] V) := by
  have h1 : Continuous fun u : V =>
      (ContinuousLinearMap.smulRightL ℝ V V (InnerProductSpace.toDual ℝ V u)) :=
    (ContinuousLinearMap.smulRightL ℝ V V).continuous.comp (InnerProductSpace.toDual ℝ V).continuous
  have h2 : Continuous fun u : V =>
      ContinuousLinearMap.smulRightL ℝ V V (InnerProductSpace.toDual ℝ V u) u :=
    h1.clm_apply continuous_id
  simpa [rankOne, ContinuousLinearMap.smulRightL_apply_apply] using h2

lemma frob_neg_left (e : OrthonormalBasis ι ℝ V) (A B : V →L[ℝ] V) :
    frob e (-A) B = -frob e A B := by
  rw [show -A = (-1 : ℝ) • A by rw [neg_one_smul], frob_smul_left]
  ring

lemma frob_neg_right (e : OrthonormalBasis ι ℝ V) (A B : V →L[ℝ] V) :
    frob e A (-B) = -frob e A B := by
  rw [frob_comm e A (-B), frob_neg_left, frob_comm e B A]

lemma frob_sub_right (e : OrthonormalBasis ι ℝ V) (A B C : V →L[ℝ] V) :
    frob e A (B - C) = frob e A B - frob e A C := by
  rw [sub_eq_add_neg, show -C = (-1 : ℝ) • C by rw [neg_one_smul], frob_add_right, frob_smul_right]
  ring

lemma frob_sub_left (e : OrthonormalBasis ι ℝ V) (A B C : V →L[ℝ] V) :
    frob e (A - B) C = frob e A C - frob e B C := by
  rw [frob_comm, frob_sub_right, frob_comm e C A, frob_comm e C B]

/-- The quadratic form `z ↦ pairing e z z` is continuous. -/
lemma continuous_pairing_self (e : OrthonormalBasis ι ℝ V) :
    Continuous fun z : (V →L[ℝ] V) × V => pairing e z z := by
  have h : (fun z : (V →L[ℝ] V) × V => pairing e z z)
      = fun z => ∑ i, ‖z.1 (e i)‖ ^ 2 + ‖z.2‖ ^ 2 := by
    funext z
    simp only [pairing, frob]
    rw [Finset.sum_congr rfl (fun i _ => real_inner_self_eq_norm_sq (z.1 (e i))),
      real_inner_self_eq_norm_sq z.2]
  rw [h]
  refine Continuous.add (continuous_finsetSum _ fun i _ => ?_) ?_
  · exact (((ContinuousLinearMap.apply ℝ V (e i)).continuous.comp continuous_fst).norm).pow 2
  · exact (continuous_snd.norm).pow 2

end Frobenius

/-! ### Compactness of the convex hull of a compact set -/

section HullCompact

/-- The convex hull of a compact set in a finite-dimensional real normed space is compact. -/
theorem isCompact_convexHull_of_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  set n := Module.finrank ℝ E
  set m := n + 1 with hm
  have hcont : Continuous fun q : (Fin m → E) × (Fin m → ℝ) => ∑ i, q.2 i • q.1 i := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (((continuous_apply i).comp continuous_snd).smul
      ((continuous_apply i).comp continuous_fst))
  set S : Set ((Fin m → E) × (Fin m → ℝ)) :=
    {q | (∀ i, q.1 i ∈ s) ∧ (∀ i, 0 ≤ q.2 i) ∧ (∑ i, q.2 i) = 1} with hS
  have hsimplex : IsCompact {t : Fin m → ℝ | (∀ i, 0 ≤ t i) ∧ (∑ i, t i) = 1} := by
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ =>
      (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1))) ?_ ?_
    · rw [show {t : Fin m → ℝ | (∀ i, 0 ≤ t i) ∧ (∑ i, t i) = 1}
          = {t | ∀ i, 0 ≤ t i} ∩ {t | (∑ i, t i) = 1} by ext t; simp]
      refine IsClosed.inter ?_ ?_
      · rw [show {t : Fin m → ℝ | ∀ i, 0 ≤ t i} = ⋂ i, {t | (0:ℝ) ≤ t i} by ext t; simp]
        exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
      · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    · intro t ht
      simp only [Set.mem_univ_pi, Set.mem_Icc]
      intro i
      refine ⟨ht.1 i, ?_⟩
      have h := Finset.single_le_sum (f := t) (fun j _ => ht.1 j) (Finset.mem_univ i)
      linarith [h, ht.2]
  have hScompact : IsCompact S := by
    rw [hS]
    refine IsCompact.of_isClosed_subset
      ((isCompact_univ_pi fun _ => hs).prod hsimplex) ?_ ?_
    · rw [show {q : (Fin m → E) × (Fin m → ℝ) |
          (∀ i, q.1 i ∈ s) ∧ (∀ i, 0 ≤ q.2 i) ∧ (∑ i, q.2 i) = 1}
          = {q | ∀ i, q.1 i ∈ s} ∩ ({q | ∀ i, 0 ≤ q.2 i} ∩ {q | (∑ i, q.2 i) = 1}) by
        ext q; simp]
      refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
      · rw [show {q : (Fin m → E) × (Fin m → ℝ) | ∀ i, q.1 i ∈ s} = ⋂ i, {q | q.1 i ∈ s} by
          ext q; simp]
        exact isClosed_iInter fun i => hs.isClosed.preimage ((continuous_apply i).comp continuous_fst)
      · rw [show {q : (Fin m → E) × (Fin m → ℝ) | ∀ i, 0 ≤ q.2 i} = ⋂ i, {q | (0:ℝ) ≤ q.2 i} by
          ext q; simp]
        exact isClosed_iInter fun i =>
          isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)
      · exact isClosed_eq (continuous_finsetSum _ fun i _ =>
          (continuous_apply i).comp continuous_snd) continuous_const
    · intro q hq
      simp only [Set.mem_prod, Set.mem_univ_pi]
      exact ⟨hq.1, hq.2.1, hq.2.2⟩
  have hSimage : (fun q : (Fin m → E) × (Fin m → ℝ) => ∑ i, q.2 i • q.1 i) '' S
      = convexHull ℝ s := by
    rw [hS]
    refine Set.Subset.antisymm ?_ ?_
    · rintro x ⟨q, hq, rfl⟩
      exact (convex_convexHull ℝ s).sum_mem (fun i _ => hq.2.1 i) (by simpa using hq.2.2)
        (fun i _ => subset_convexHull ℝ s (hq.1 i))
    · intro x hx
      obtain ⟨ι, hι, z, w, hzs, hind, hwpos, hwsum, hwz⟩ :=
        eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) hx
      obtain ⟨p, hp⟩ := (convexHull_nonempty_iff (𝕜 := ℝ) (s := s)).mp ⟨x, hx⟩
      have hcard : Fintype.card ι ≤ m := by
        rw [hm]
        have h1 := hind.card_le_finrank_succ
        have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ Module.finrank ℝ E :=
          Submodule.finrank_le _
        exact le_trans h1 (Nat.add_le_add_right h2 1)
      obtain ⟨y, t, hy, ht0, htsum, hyt⟩ :=
        exists_fin_sum_of_card_le hcard z w (fun i => (hwpos i).le) hwsum p
      refine ⟨(y, t), ⟨?_, ht0, htsum⟩, ?_⟩
      · intro i
        rcases hy i with h | h
        · exact hzs h
        · rw [Set.mem_singleton_iff] at h
          show y i ∈ s
          rw [h]; exact hp
      · simp only [hyt, hwz]
  rw [← hSimage]
  exact hScompact.image hcont

end HullCompact

/-! ### The perturbation step -/

section Perturbation

/-- The set of contact points `∂K ∩ S^{n-1}` of a compact set is compact. -/
lemma isCompact_frontier_inter_sphere {K : Set V} (hcomp : IsCompact K) :
    IsCompact (frontier K ∩ Metric.sphere (0 : V) 1) := by
  refine IsCompact.of_isClosed_subset hcomp (isClosed_frontier.inter isClosed_sphere) ?_
  rintro u ⟨hu, -⟩
  exact hcomp.isClosed.closure_eq ▸ frontier_subset_closure hu

/-- **Perturbation step.** If `(K₀, b)` is a certificate (strictly negative on the contact points
of `K`), then for all sufficiently small `t > 0` the ellipsoid
`t • b + (1 + t • K₀) '' closedBall 0 1` is still inscribed in `K`. -/
theorem john_perturbation_membership {K : Set V} (hcomp : IsCompact K) (_hconv : Convex ℝ K)
    (hB : closedBall (0 : V) 1 ⊆ K) {K₀ : V →L[ℝ] V} {b : V}
    (hneg : ∀ u ∈ frontier K, ‖u‖ = 1 → inner ℝ (K₀ u) u + inner ℝ b u < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ∈ Set.Ioo 0 δ → ∀ y : V, ‖y‖ ≤ 1 →
      t • b + (1 + t • K₀) y ∈ K := by
  classical
  have hsphere : ∀ u : V, (u ∈ Metric.sphere (0 : V) 1 ↔ ‖u‖ = 1) := by
    intro u
    rw [mem_sphere, dist_eq_norm, sub_zero]
  have hball_int : ball (0 : V) 1 ⊆ interior K :=
    interior_maximal (ball_subset_closedBall.trans hB) isOpen_ball
  set ψ : V → ℝ := fun y => inner ℝ (K₀ y) y + inner ℝ b y with hψdef
  have hψcont : Continuous ψ := by
    rw [hψdef]
    exact (K₀.continuous.inner continuous_id).add (continuous_const.inner continuous_id)
  -- (1) a strict uniform bound for `ψ` on the contact set
  obtain ⟨c, hc, hψle⟩ : ∃ c : ℝ, c < 0 ∧
      ∀ u ∈ frontier K, ‖u‖ = 1 → ψ u ≤ c := by
    rcases Set.eq_empty_or_nonempty (frontier K ∩ Metric.sphere (0 : V) 1) with hemp | ⟨u₀, hu₀⟩
    · refine ⟨-1, by norm_num, fun u hu h1 => ?_⟩
      have hmem : u ∈ frontier K ∩ Metric.sphere (0 : V) 1 := ⟨hu, (hsphere u).mpr h1⟩
      rw [hemp] at hmem
      exact absurd hmem (by simp)
    · obtain ⟨u₁, hu₁, hmax⟩ := (isCompact_frontier_inter_sphere hcomp).exists_isMaxOn
        ⟨u₀, hu₀⟩ hψcont.continuousOn
      refine ⟨ψ u₁, hneg u₁ hu₁.1 ((hsphere u₁).mp hu₁.2), fun u hu h1 => ?_⟩
      exact hmax ⟨hu, (hsphere u).mpr h1⟩
  -- (2) a uniform bound for `b + K₀ y` on the unit ball
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V, ‖y‖ ≤ 1 → ‖b + K₀ y‖ ≤ C := by
    obtain ⟨y₀, -, hmax⟩ := (isCompact_closedBall (0 : V) 1).exists_isMaxOn
      ⟨0, by simp⟩ ((continuous_const.add K₀.continuous).norm.continuousOn)
    exact ⟨‖b + K₀ y₀‖, norm_nonneg _, fun y hy =>
      hmax (by rwa [mem_closedBall, dist_zero_right])⟩
  -- (3) the tube around the contact set
  set W : Set V := {y | ψ y < c / 2 ∧ ‖b + K₀ y‖ < C + 1} with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef]
    exact (isOpen_lt hψcont continuous_const).inter
      (isOpen_lt (continuous_const.add K₀.continuous).norm continuous_const)
  have hUsubW : frontier K ∩ Metric.sphere (0 : V) 1 ⊆ W := by
    rintro u ⟨hu, h1⟩
    have h1' : ‖u‖ = 1 := (hsphere u).mp h1
    exact ⟨lt_of_le_of_lt (hψle u hu h1') (by linarith),
      lt_of_le_of_lt (hC u (by rw [h1'])) (by linarith)⟩
  have hdiff : closedBall (0 : V) 1 \ W ⊆ interior K := by
    rintro y ⟨hy, hyW⟩
    by_contra hyint
    have hyK : y ∈ K := hB hy
    have hyfront : y ∈ frontier K := (mem_frontier_iff_notMem_interior hyK).mpr hyint
    have hnorm : ‖y‖ = 1 := by
      by_contra hne
      have hlt : ‖y‖ < 1 := lt_of_le_of_ne (by rwa [mem_closedBall, dist_zero_right] at hy) hne
      exact hyint (hball_int (by rwa [mem_ball, dist_zero_right]))
    exact hyW (hUsubW ⟨hyfront, (hsphere y).mpr hnorm⟩)
  obtain ⟨η, hη, hηK⟩ := ((isCompact_closedBall (0 : V) 1).diff hWopen).exists_cthickening_subset_open
    isOpen_interior hdiff
  -- (4) the conclusion
  have hCpos : (0 : ℝ) < C + 1 := by linarith
  have hC1 : (0 : ℝ) < (C + 1) ^ 2 := by positivity
  have hη1 : (0 : ℝ) < η / (C + 1) := div_pos hη hCpos
  have hpos1 : (0 : ℝ) < -c / (C + 1) ^ 2 := div_pos (by linarith) hC1
  refine ⟨min ((-c) / (C + 1) ^ 2) (η / (C + 1)), lt_min hpos1 hη1, ?_⟩
  rintro t ⟨ht0, htlt⟩ y hy
  have hmem_ball : ∀ x : V, ‖x‖ < 1 → x ∈ K := fun x hx =>
    hB (ball_subset_closedBall (by rwa [mem_ball, dist_zero_right]))
  have hsplit : t • b + (1 + t • K₀) y = y + t • (b + K₀ y) := by
    rw [add_apply, one_apply_eq_self, smul_apply]
    module
  by_cases hyW : y ∈ W
  · -- inside the tube: the perturbed point stays in the open unit ball
    obtain ⟨hψy, hwy⟩ := hyW
    have hlt : t * (C + 1) ^ 2 < -c :=
      (lt_div_iff₀ hC1).mp (lt_of_lt_of_le htlt (min_le_left _ _))
    refine hmem_ball _ ?_
    rw [hsplit]
    have h3 : inner ℝ y (t • (b + K₀ y)) = t * ψ y := by
      rw [inner_smul_right, inner_add_right, ← real_inner_comm y b, ← real_inner_comm y (K₀ y),
        hψdef]
      ring
    have h4 : ‖t • (b + K₀ y)‖ = t * ‖b + K₀ y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    have hy2 : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y, hy]
    have hkey : ‖y + t • (b + K₀ y)‖ ^ 2 < 1 := by
      rw [norm_add_sq_real, h3, h4]
      have hA : 2 * t * ψ y < t * c := by nlinarith [hψy, ht0]
      have hB1 : 0 ≤ t * ‖b + K₀ y‖ := mul_nonneg ht0.le (norm_nonneg _)
      have hB2 : (t * ‖b + K₀ y‖) ^ 2 < t ^ 2 * (C + 1) ^ 2 := by
        have h1 : (t * (C + 1)) ^ 2 = t ^ 2 * (C + 1) ^ 2 := by ring
        rw [← h1]
        exact pow_lt_pow_left₀ (mul_lt_mul_of_pos_left hwy ht0) hB1 (by norm_num)
      have hC2 : t ^ 2 * (C + 1) ^ 2 < -t * c := by nlinarith [hlt, ht0]
      nlinarith [hy2, hA, hB2, hC2]
    nlinarith [norm_nonneg (y + t • (b + K₀ y)), hkey]
  · -- outside the tube: within a uniform thickening of the unit ball
    have hlt : t * (C + 1) < η :=
      (lt_div_iff₀ hCpos).mp
        (lt_of_lt_of_le htlt (min_le_right _ _))
    have hmem : y ∈ closedBall (0 : V) 1 \ W :=
      ⟨by rwa [mem_closedBall, dist_zero_right], hyW⟩
    have hdist : dist (t • b + (1 + t • K₀) y) y ≤ η := by
      rw [dist_eq_norm, show t • b + (1 + t • K₀) y - y = t • (b + K₀ y) by
        rw [add_apply, one_apply_eq_self, smul_apply]
        module, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      calc t * ‖b + K₀ y‖ ≤ t * C := mul_le_mul_of_nonneg_left (hC y hy) ht0.le
        _ ≤ t * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) ht0.le
        _ ≤ η := hlt.le
    exact interior_subset (hηK (Metric.mem_cthickening_of_dist_le _ _ η _ hmem hdist))

end Perturbation

/-! ### The determinant of a small perturbation of the identity -/

section DetPerturbation

open Polynomial in
/-- For a linear map `A` of positive trace, the determinant of `1 + t • A` exceeds `1` in absolute
value for all sufficiently small positive `t`. -/
theorem det_one_add_smul_gt_one (A : V →L[ℝ] V)
    (h : 0 < LinearMap.trace ℝ V A.toLinearMap) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, t ∈ Set.Ioo 0 δ → 1 < |(1 + t • A).det| := by
  classical
  let b := (stdOrthonormalBasis ℝ V).toBasis
  let M : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
    LinearMap.toMatrix b b A.toLinearMap
  let q : Polynomial ℝ := (Matrix.det (1 + (X : ℝ[X]) • M.map Polynomial.C)).divX.divX
  have htrace : M.trace = LinearMap.trace ℝ V A.toLinearMap :=
    (LinearMap.trace_eq_matrix_trace ℝ b A.toLinearMap).symm
  have hdet : ∀ t : ℝ, (1 + t • A).det
      = 1 + (LinearMap.trace ℝ V A.toLinearMap) * t + q.eval t * t ^ 2 := by
    intro t
    have h1 : ((1 + t • A : V →L[ℝ] V) : V →ₗ[ℝ] V) = 1 + t • A.toLinearMap := by
      rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
        ContinuousLinearMap.toLinearMap_one]
    have h2 : LinearMap.toMatrix b b ((1 + t • A : V →L[ℝ] V) : V →ₗ[ℝ] V) = 1 + t • M := by
      rw [h1, LinearEquiv.map_add, LinearEquiv.map_smul, LinearMap.toMatrix_one]

    have h3 : (1 + t • A : V →L[ℝ] V).det
        = (1 + t • M).det := by
      rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, h2]
    rw [h3, Matrix.det_one_add_smul, htrace]
  obtain ⟨t₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) (q.continuous.abs.continuousOn)
  set K : ℝ := |q.eval t₀|
  have hK0 : 0 ≤ K := abs_nonneg _
  have hKq : ∀ t ∈ Set.Icc (0 : ℝ) 1, |q.eval t| ≤ K := fun t ht => hmax ht
  refine ⟨min 1 (LinearMap.trace ℝ V A.toLinearMap / (K + 1)),
    lt_min zero_lt_one (div_pos h (by linarith)), ?_⟩
  intro t ht
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have htt : t * (K + 1) < LinearMap.trace ℝ V A.toLinearMap :=
    (lt_div_iff₀ (by linarith : (0 : ℝ) < K + 1)).mp (lt_of_lt_of_le ht.2 (min_le_right _ _))
  have hqt := hKq t ⟨ht0.le, ht1.le⟩
  have hpos : 0 < LinearMap.trace ℝ V A.toLinearMap + t * q.eval t := by
    have h1 : -K ≤ q.eval t := by linarith [abs_le.mp hqt]
    nlinarith [h1, htt, ht0]
  have hgt : 1 < (1 + t • A).det := by
    rw [hdet t]
    nlinarith [hpos, ht0]
  rwa [abs_of_pos (by linarith)]

end DetPerturbation



/-! ### The contact data and the closest-point (separation) step -/

section Crux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pairing of a scalar multiple of the identity with an endomorphism. -/
lemma frob_one (e : OrthonormalBasis ι ℝ V) (A : V →L[ℝ] V) :
    frob e (1 : V →L[ℝ] V) A = ∑ i, inner ℝ (e i) (A (e i)) := by
  simp only [frob, one_apply_eq_self]

lemma frob_smul_one (e : OrthonormalBasis ι ℝ V) (c : ℝ) (A : V →L[ℝ] V) :
    frob e (c • (1 : V →L[ℝ] V)) A = c * ∑ i, inner ℝ (e i) (A (e i)) := by
  rw [frob_smul_left, frob_one]

/-- The set of "contact data": unit vectors on the boundary of `K` together with the rank-one
operator they define. -/
def contactData (K : Set V) : Set ((V →L[ℝ] V) × V) :=
  {z | ∃ u ∈ frontier K, ‖u‖ = 1 ∧ z = (rankOne u, u)}

/-- The centre point `(I/n, 0)` of the separation argument. -/
def centrePoint : (V →L[ℝ] V) × V :=
  ((Module.finrank ℝ V : ℝ)⁻¹ • (1 : V →L[ℝ] V), 0)

lemma contactData_apply (K : Set V) {u : V} (hu : u ∈ frontier K) (h : ‖u‖ = 1) :
    (rankOne u, u) ∈ contactData K := ⟨u, hu, h, rfl⟩

/-- **Separation step.** If the point `(I/n, 0)` is not in the convex hull of the contact data,
then there is a certificate `(K₀, b)`: a map of positive trace which is strictly negative on all
contact points. -/
theorem exists_certificate [CompleteSpace V] (K : Set V) (hcomp : IsCompact K)
    (e : OrthonormalBasis ι ℝ V) (hcard : Fintype.card ι = Module.finrank ℝ V)
    (hne : (contactData K).Nonempty)
    (hnot : centrePoint (V := V) ∉ convexHull ℝ (contactData K)) :
    ∃ (K₀ : V →L[ℝ] V) (b : V), 0 < (∑ i, inner ℝ (e i) (K₀ (e i))) ∧
      ∀ u ∈ frontier K, ‖u‖ = 1 → inner ℝ (K₀ u) u + inner ℝ b u < 0 := by
  classical
  have hnpos : 0 < Module.finrank ℝ V := by
    obtain ⟨z, u, hu, h1, hz⟩ := hne
    have hne0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      exact one_ne_zero h1.symm
    have : Nontrivial V := ⟨u, 0, hne0⟩
    exact Module.finrank_pos
  -- the contact set is compact
  set U : Set V := frontier K ∩ Metric.sphere (0 : V) 1 with hU
  have hUcomp : IsCompact U := by
    rw [hU]
    refine IsCompact.of_isClosed_subset hcomp (isClosed_frontier.inter isClosed_sphere) ?_
    rintro u ⟨hu, -⟩
    exact hcomp.isClosed.closure_eq ▸ frontier_subset_closure hu
  have hcontact_eq : contactData K = (fun u : V => (rankOne u, u)) '' U := by
    rw [hU]
    ext z
    simp only [contactData, Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff, mem_sphere,
      dist_eq_norm, sub_zero]
    constructor
    · rintro ⟨u, hu, h1, rfl⟩
      exact ⟨u, ⟨hu, h1⟩, rfl⟩
    · rintro ⟨u, ⟨hu, h1⟩, rfl⟩
      exact ⟨u, hu, h1, rfl⟩
  have hcont_contact : Continuous fun u : V => (rankOne u, u) :=
    (continuous_rankOne (V := V)).prodMk continuous_id
  have hcontact_comp : IsCompact (contactData K) := by
    rw [hcontact_eq]
    exact hUcomp.image hcont_contact
  have hhullcomp : IsCompact (convexHull ℝ (contactData K)) :=
    isCompact_convexHull_of_isCompact hcontact_comp
  have hhullne : (convexHull ℝ (contactData K)).Nonempty :=
    hne.mono (subset_convexHull ℝ (contactData K))
  -- the closest point
  set p : (V →L[ℝ] V) × V := centrePoint (V := V) with hp
  have hcontQ : Continuous fun z : (V →L[ℝ] V) × V => pairing e (z - p) (z - p) :=
    (continuous_pairing_self e).comp (continuous_id.sub continuous_const)
  obtain ⟨q, hqhull, hqmin⟩ := hhullcomp.exists_isMinOn hhullne hcontQ.continuousOn
  have hqp : q ≠ p := fun h => hnot (h ▸ hqhull)
  have hsq : 0 < pairing e (q - p) (q - p) := by
    rcases lt_or_eq_of_le (pairing_self_nonneg e (q - p)) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp (pairing_self_eq_zero e h.symm)) hqp
  -- the optimality inequality
  have hopt : ∀ z ∈ convexHull ℝ (contactData K), 0 ≤ pairing e (q - p) (z - q) := by
    intro z hz
    obtain ⟨A, B, hA, hB⟩ : ∃ A B : ℝ,
        A = pairing e (q - p) (z - q) ∧ B = pairing e (z - q) (z - q) := ⟨_, _, rfl, rfl⟩
    rw [← hA]
    by_contra hcon
    rw [not_le] at hcon
    have hseg : ∀ s : ℝ, s ∈ Set.Icc 0 1 →
        q + s • (z - q) ∈ convexHull ℝ (contactData K) := by
      intro s hs
      refine (convex_convexHull ℝ (contactData K)).add_smul_mem hqhull ?_ hs
      convert hz using 2
      abel
    have hB0 : 0 ≤ B := by rw [hB]; exact pairing_self_nonneg e (z - q)
    set s : ℝ := min (1/2) ((-A) / (2 * (B + 1))) with hsdef
    have hs0 : 0 < s := by
      rw [hsdef]
      exact lt_min (by norm_num) (div_pos (by linarith) (by linarith))
    have hs1 : s ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
    have hkey : 0 ≤ 2 * A + s * B := by
      have h1 : q + s • (z - q) ∈ convexHull ℝ (contactData K) := hseg s ⟨hs0.le, hs1⟩
      have h2 := hqmin h1
      change pairing e (q - p) (q - p)
          ≤ pairing e (q + s • (z - q) - p) (q + s • (z - q) - p) at h2
      have h3 : q + s • (z - q) - p = (q - p) + s • (z - q) := by abel
      rw [h3, pairing_quad] at h2
      have h4 : 0 ≤ 2 * s * A + s ^ 2 * B := by
        rw [hA, hB]
        linarith [h2]
      have h5 : 0 ≤ s * (2 * A + s * B) := by
        rw [show s * (2 * A + s * B) = 2 * s * A + s ^ 2 * B by ring]
        exact h4
      exact (mul_nonneg_iff_of_pos_left hs0).mp h5
    have hsbound : s * (2 * (B + 1)) ≤ -A := by
      rw [hsdef]
      have h2 := min_le_right (1 / 2 : ℝ) ((-A) / (2 * (B + 1)))
      have h3 : 0 < 2 * (B + 1) := by linarith
      calc min (1 / 2 : ℝ) ((-A) / (2 * (B + 1))) * (2 * (B + 1))
          ≤ ((-A) / (2 * (B + 1))) * (2 * (B + 1)) := mul_le_mul_of_nonneg_right h2 h3.le
        _ = -A := by field_simp
    have hneg : 2 * A + s * B < 0 := by nlinarith [hB0, hs0, hsbound]
    linarith [hkey, hneg]
  -- expand the inequality at a contact point
  set A₀ : V →L[ℝ] V := (q - p).1 with hA₀
  set β : V := (q - p).2 with hβ
  set m : ℝ := frob e A₀ q.1 + inner ℝ β q.2 with hm
  have hq1 : q.1 = A₀ + (Module.finrank ℝ V : ℝ)⁻¹ • (1 : V →L[ℝ] V) := by
    have h : A₀ = q.1 - (Module.finrank ℝ V : ℝ)⁻¹ • (1 : V →L[ℝ] V) := by
      rw [hA₀, hp, centrePoint]
      rfl
    rw [h]
    abel
  have hq2 : q.2 = β := by
    have h : β = q.2 - (0 : V) := by
      rw [hβ, hp, centrePoint]
      rfl
    rw [h, sub_zero]
  have hineq : ∀ u ∈ frontier K, ‖u‖ = 1 →
      m ≤ inner ℝ (A₀ u) u + inner ℝ β u := by
    intro u hu h1
    have hmem : (rankOne u, u) ∈ convexHull ℝ (contactData K) :=
      subset_convexHull ℝ _ (contactData_apply K hu h1)
    have h2 := hopt (rankOne u, u) hmem
    rw [show (rankOne u, u) - q = (rankOne u - q.1, u - q.2) from rfl] at h2
    simp only [pairing, frob_sub_right, ← hA₀, ← hβ, frob_rankOne, inner_sub_right] at h2
    rw [hm]
    linarith [h2]
  -- the algebra of the certificate
  set tA : ℝ := ∑ i, inner ℝ (e i) (A₀ (e i)) with htA
  have hm_eq : m = pairing e (q - p) (q - p) + (Module.finrank ℝ V : ℝ)⁻¹ * tA := by
    have hpair : pairing e (q - p) (q - p) = frob e A₀ A₀ + inner ℝ β β := by
      rw [pairing, ← hA₀, ← hβ]
    have hf1 : frob e A₀ (1 : V →L[ℝ] V) = tA := by
      rw [frob_comm e A₀ 1, frob_one, htA]
    rw [hm, hq1, hq2, hpair, frob_add_right, frob_smul_right, hf1]
    ring
  set μ : ℝ := ((Module.finrank ℝ V : ℝ)⁻¹ * tA + m) / 2 with hμ
  have hμ_gt : (Module.finrank ℝ V : ℝ)⁻¹ * tA < μ := by
    rw [hμ]
    linarith [hsq, hm_eq]
  have hμ_lt : μ < m := by
    rw [hμ]
    linarith [hsq, hm_eq]
  refine ⟨-A₀ + μ • (1 : V →L[ℝ] V), -β, ?_, ?_⟩
  · -- positivity of the trace
    have h11 : frob e (1 : V →L[ℝ] V) (1 : V →L[ℝ] V) = (Module.finrank ℝ V : ℝ) := by
      rw [frob_one]
      have h1 : ∀ i, inner ℝ (e i) ((1 : V →L[ℝ] V) (e i)) = 1 := by
        intro i
        rw [one_apply_eq_self, real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one e i]
        simp
      rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, hcard]
    have htr : ∑ i, inner ℝ (e i) ((-A₀ + μ • (1 : V →L[ℝ] V)) (e i))
        = -tA + μ * (Module.finrank ℝ V : ℝ) := by
      rw [← frob_one e (-A₀ + μ • (1 : V →L[ℝ] V)), frob_add_right, frob_neg_right,
        frob_smul_right, frob_one e A₀, ← htA, h11]
    rw [htr]
    have hnpos' : (0 : ℝ) < (Module.finrank ℝ V : ℝ) := by exact_mod_cast hnpos
    have h1 : tA < μ * (Module.finrank ℝ V : ℝ) := by
      have h := mul_lt_mul_of_pos_left hμ_gt hnpos'
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnpos'), one_mul, mul_comm] at h
      exact h
    linarith
  · -- strict negativity on the contact set
    intro u hu h1
    have h2 := hineq u hu h1
    have hu1 : inner ℝ u u = 1 := by
      rw [real_inner_self_eq_norm_sq, h1]
      simp
    have h3 : inner ℝ ((-A₀ + μ • (1 : V →L[ℝ] V)) u) u = μ - inner ℝ (A₀ u) u := by
      simp only [add_apply, neg_apply, smul_apply, one_apply_eq_self, inner_add_left,
        inner_neg_left, inner_smul_left, RCLike.conj_to_real]
      rw [hu1]
      ring
    have h4 : inner ℝ (-β) u = -inner ℝ β u := by simp
    rw [h3, h4]
    linarith [h2, hμ_lt, hμ_gt]


end Crux


/-! ### The normalised core of the proof

If `K` is compact and convex, contains the unit ball, and the unit ball is a maximal-volume
inscribed ellipsoid, then `K` is contained in the ball of radius `n = finrank ℝ V`. -/
theorem john_core [CompleteSpace V] (K : Set V) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (hB : closedBall (0 : V) 1 ⊆ K)
    (hmax : ∀ (c : V) (M : V →L[ℝ] V), IsInscribed K c M → |M.det| ≤ 1) :
    K ⊆ closedBall (0 : V) (Module.finrank ℝ V) := by
  classical
  have hsphere : ∀ u : V, (u ∈ Metric.sphere (0 : V) 1 ↔ ‖u‖ = 1) := by
    intro u
    rw [mem_sphere, dist_eq_norm, sub_zero]
  have hball_int : ball (0 : V) 1 ⊆ interior K :=
    interior_maximal (ball_subset_closedBall.trans hB) isOpen_ball
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ V) with hn0 | hnpos
  · have hsub_single : Subsingleton V := Module.finrank_zero_iff.mp hn0
    intro x _
    have hx : x = 0 := Subsingleton.elim x 0
    simp [hx, hn0]
  · -- (i) the support-function bound at contact points
    have hKle : ∀ u ∈ frontier K, ‖u‖ = 1 → ∀ x ∈ K, inner ℝ x u ≤ 1 := by
      intro u hu hu1 x hxK
      by_contra hcon
      rw [not_le] at hcon
      have hn1 : 0 < ‖x‖ ^ 2 + 1 := by positivity
      set lam : ℝ := min (1 / 2) ((inner ℝ x u - 1) / (‖x‖ ^ 2 + 1)) with hlamdef
      have hlam0 : 0 < lam := by
        rw [hlamdef]
        exact lt_min (by norm_num) (div_pos (by linarith) hn1)
      have hlam1 : lam < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      have hsub1 : lam * (‖x‖ ^ 2 + 1) ≤ inner ℝ x u - 1 :=
        (le_div_iff₀ hn1).mp (le_trans (min_le_right _ _) le_rfl)
      have hsub2 : lam * (‖x‖ ^ 2 - 1) ≤ lam * (‖x‖ ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam0.le
      set v : V := (1 - lam)⁻¹ • (u - lam • x) with hvdef
      have hlamne : (1 - lam) ≠ 0 := by linarith
      have huv : lam • x + (1 - lam) • v = u := by
        rw [hvdef, smul_smul, mul_inv_cancel₀ hlamne, one_smul]
        module
      have hvnorm : ‖v‖ < 1 := by
        have hkey : ‖u - lam • x‖ ^ 2 < (1 - lam) ^ 2 := by
          have h3 : inner ℝ u (lam • x) = lam * inner ℝ x u := by
            rw [inner_smul_right, real_inner_comm u x]
          have h4 : ‖lam • x‖ ^ 2 = lam ^ 2 * ‖x‖ ^ 2 := by
            rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
          rw [norm_sub_sq_real, hu1, h3, h4]
          nlinarith [hlam0, hlam1, hsub1, hsub2, hcon]
        have h1 : ‖u - lam • x‖ < 1 - lam := by
          nlinarith [norm_nonneg (u - lam • x), hkey, hlam1]
        rw [hvdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
        have h2 := mul_lt_mul_of_pos_left h1 (inv_pos.mpr (by linarith : (0:ℝ) < 1 - lam))
        rwa [inv_mul_cancel₀ (by linarith)] at h2
      have hvint : v ∈ interior K :=
        hball_int (by rwa [mem_ball, dist_zero_right])
      have hmem : x + (1 - lam) • (v - x) ∈ interior K :=
        hconv.add_smul_mem_interior hxK (by simpa using hvint) ⟨by linarith, by linarith⟩
      have heq : x + (1 - lam) • (v - x) = u := by
        rw [← huv]
        module
      rw [heq] at hmem
      have huK : u ∈ K := hcomp.isClosed.closure_eq ▸ frontier_subset_closure hu
      exact (mem_frontier_iff_notMem_interior huK).mp hu hmem
    -- (ii) the contact set is nonempty
    have hUne : (frontier K ∩ Metric.sphere (0 : V) 1).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hsub : Metric.sphere (0 : V) 1 ⊆ interior K := by
        intro u hu
        by_contra hui
        have huK : u ∈ K := hB (by
          rw [mem_closedBall, dist_zero_right]
          exact le_of_eq ((hsphere u).mp hu))
        have hmem : u ∈ frontier K ∩ Metric.sphere (0 : V) 1 :=
          ⟨(mem_frontier_iff_notMem_interior huK).mpr hui, hu⟩
        rw [hemp] at hmem
        exact absurd hmem (by simp)
      obtain ⟨δ, hδ, hδK⟩ := (isCompact_sphere (0 : V) 1).exists_cthickening_subset_open
        isOpen_interior hsub
      have hball1 : closedBall (0 : V) (1 + δ) ⊆ K := by
        intro x hx
        rw [mem_closedBall, dist_zero_right] at hx
        rcases lt_or_ge ‖x‖ 1 with h1 | h1
        · exact hB (by rw [mem_closedBall, dist_zero_right]; exact h1.le)
        · have hx0 : x ≠ 0 := by
            rintro rfl
            simp only [norm_zero] at h1
            linarith
          have hy : (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : V) 1 := by
            rw [hsphere, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
              inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
          have hd : dist x ((‖x‖⁻¹ : ℝ) • x) ≤ δ := by
            rw [dist_eq_norm, show x - (‖x‖⁻¹ : ℝ) • x = (1 - ‖x‖⁻¹) • x by
              rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs]
            have h2 : (0 : ℝ) ≤ 1 - ‖x‖⁻¹ := by
              rw [sub_nonneg]
              exact (inv_le_one₀ (norm_pos_iff.mpr hx0)).mpr h1
            rw [abs_of_nonneg h2]
            have h3 : (1 - ‖x‖⁻¹) * ‖x‖ = ‖x‖ - 1 := by
              field_simp
            rw [h3]
            linarith
          exact interior_subset (hδK (Metric.mem_cthickening_of_dist_le _ _ δ _ hy hd))
      have hins : IsInscribed K 0 ((1 + δ) • (1 : V →L[ℝ] V)) := by
        intro y hy
        rw [zero_add, smul_apply, one_apply_eq_self]
        refine hball1 (by
          rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (by linarith : (0:ℝ) < 1 + δ)]
          nlinarith [hy])
      have hle := hmax 0 ((1 + δ) • (1 : V →L[ℝ] V)) hins
      have hdet : ((1 + δ) • (1 : V →L[ℝ] V)).det = (1 + δ) ^ Module.finrank ℝ V := by
        rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
          ContinuousLinearMap.toLinearMap_one, LinearMap.det_smul]
        simp
      rw [hdet, abs_of_pos (by positivity)] at hle
      have hone : 1 < (1 + δ) ^ Module.finrank ℝ V :=
        one_lt_pow₀ (by linarith) (Nat.pos_iff_ne_zero.mp hnpos)
      linarith
    -- (iii) the centre point is in the convex hull of the contact data
    have hcenter : centrePoint (V := V) ∈ convexHull ℝ (contactData K) := by
      by_contra hnot
      let e : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V := stdOrthonormalBasis ℝ V
      have hcard : Fintype.card (Fin (Module.finrank ℝ V)) = Module.finrank ℝ V :=
        Fintype.card_fin _
      have hne : (contactData K).Nonempty := by
        obtain ⟨u, hu⟩ := hUne
        exact ⟨(rankOne u, u), contactData_apply K hu.1 ((hsphere u).mp hu.2)⟩
      obtain ⟨K₀, b, htr, hneg⟩ := exists_certificate K hcomp e hcard hne hnot
      have htr' : 0 < LinearMap.trace ℝ V K₀.toLinearMap := by
        rwa [LinearMap.trace_eq_sum_inner K₀.toLinearMap e]
      obtain ⟨δ₁, hδ₁, hmem⟩ := john_perturbation_membership hcomp hconv hB hneg
      obtain ⟨δ₂, hδ₂, hdgt⟩ := det_one_add_smul_gt_one K₀ htr'
      have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
      have ht1 : min δ₁ δ₂ / 2 ∈ Set.Ioo 0 δ₁ :=
        ⟨by linarith, by linarith [min_le_left δ₁ δ₂]⟩
      have ht2 : min δ₁ δ₂ / 2 ∈ Set.Ioo 0 δ₂ :=
        ⟨by linarith, by linarith [min_le_right δ₁ δ₂]⟩
      have hle := hmax (((min δ₁ δ₂) / 2) • b) (1 + (((min δ₁ δ₂) / 2)) • K₀)
        (fun y hy => hmem _ ht1 y hy)
      have hgt := hdgt _ ht2
      linarith
    -- (iv) extract the John frame
    obtain ⟨ι, hι, z, w, hzs, hind, hwpos, hwsum, hwz⟩ :=
      eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) hcenter
    have hz : ∀ i : ι, ∃ u : V, u ∈ frontier K ∧ ‖u‖ = 1 ∧ z i = (rankOne u, u) :=
      fun i => hzs ⟨i, rfl⟩
    choose u hu_front hu_norm hzu using hz
    have hnpos' : (0 : ℝ) < (Module.finrank ℝ V : ℝ) := by exact_mod_cast hnpos
    have hsum_op : ∑ i, w i • rankOne (u i) = (Module.finrank ℝ V : ℝ)⁻¹ • (1 : V →L[ℝ] V) := by
      have h1 : ∑ i, w i • (z i).1 = (Module.finrank ℝ V : ℝ)⁻¹ • (1 : V →L[ℝ] V) := by
        have h2 := congr_arg (LinearMap.fst ℝ (V →L[ℝ] V) V) hwz
        simpa only [map_sum, map_smul, LinearMap.fst_apply, centrePoint] using h2
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => by rw [hzu i]
    have hsum_bal : ∑ i, w i • u i = 0 := by
      have h1 : ∑ i, w i • (z i).2 = (0 : V) := by
        have h2 := congr_arg (LinearMap.snd ℝ (V →L[ℝ] V) V) hwz
        simpa only [map_sum, map_smul, LinearMap.snd_apply, centrePoint] using h2
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => by rw [hzu i]
    have hop : ∑ i, ((Module.finrank ℝ V : ℝ) * w i) • rankOne (u i) = 1 := by
      have h1 : (Module.finrank ℝ V : ℝ) • (∑ i, w i • rankOne (u i))
          = ∑ i, ((Module.finrank ℝ V : ℝ) * w i) • rankOne (u i) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
      rw [← h1, hsum_op, smul_smul, mul_inv_cancel₀ (ne_of_gt hnpos'), one_smul]
    have hbal : ∑ i, ((Module.finrank ℝ V : ℝ) * w i) • u i = 0 := by
      have h1 : (Module.finrank ℝ V : ℝ) • (∑ i, w i • u i)
          = ∑ i, ((Module.finrank ℝ V : ℝ) * w i) • u i := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
      rw [← h1, hsum_bal, smul_zero]
    have hframe : ∀ y : V,
        ∑ i, ((Module.finrank ℝ V : ℝ) * w i) * inner ℝ (u i) y ^ 2 = ‖y‖ ^ 2 := by
      intro y
      have h1 : (∑ i, ((Module.finrank ℝ V : ℝ) * w i) • rankOne (u i)) y = y := by
        rw [hop]
        simp
      rw [sum_apply] at h1
      simp only [smul_apply, rankOne_apply] at h1
      have h2 : inner ℝ (∑ i, ((Module.finrank ℝ V : ℝ) * w i) •
          (inner ℝ (u i) y • u i)) y = ‖y‖ ^ 2 := by
        rw [h1, real_inner_self_eq_norm_sq]
      rw [sum_inner] at h2
      simp only [inner_smul_left, RCLike.conj_to_real] at h2
      rw [← h2]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hbound := john_frame u (fun i => (Module.finrank ℝ V : ℝ) * w i) hu_norm
      (fun i => mul_pos hnpos' (hwpos i)) hframe hbal
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    exact hbound x fun i => by
      rw [← real_inner_comm (u i) x]
      exact hKle (u i) (hu_front i) (hu_norm i) x hx


/-- **John's ellipsoid theorem**, final assembly. -/
theorem john_ellipsoid_core [CompleteSpace V] (hpos : 0 < Module.finrank ℝ V)
    (K : Set V) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) :
    ∃ (c : V) (T : V ≃L[ℝ] V),
      (∀ y : V, ‖y‖ ≤ 1 → c + T y ∈ K) ∧
      (∀ x ∈ K, ∃ y : V, ‖y‖ ≤ 1 ∧ x = c + (Module.finrank ℝ V : ℝ) • T y) := by
  classical
  obtain ⟨c, M, hins, hMdet, hmax⟩ := exists_max_det K hcomp hint
  -- the continuous linear equivalence induced by `M`
  have hker : M.toLinearMap.ker = ⊥ := by
    by_contra h
    exact hMdet ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr h)
  have hinj : Function.Injective M := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective M := LinearMap.surjective_of_injective hinj
  let Mₑ : V ≃ₗ[ℝ] V := LinearEquiv.ofBijective M.toLinearMap ⟨hinj, hsurj⟩
  let T : V ≃L[ℝ] V := Mₑ.toContinuousLinearEquiv
  have hTM : (T : V →L[ℝ] V) = M := ContinuousLinearMap.ext fun x => rfl
  have hTapp : ∀ z : V, T z = M z := fun z => ContinuousLinearMap.ext_iff.mp hTM z
  have hdetT : (T : V →L[ℝ] V).det = M.det := by
    have hlinT : ((T : V →L[ℝ] V) : V →ₗ[ℝ] V) = (M : V →ₗ[ℝ] V) := by rw [hTM]
    rw [ContinuousLinearMap.det, ContinuousLinearMap.det, hlinT]
  set K' : Set V := {z | c + T z ∈ K} with hK'
  have hK'eq : K' = (fun y : V => T.symm (y - c)) '' K := by
    rw [hK']
    ext z
    constructor
    · intro hz
      exact ⟨c + T z, hz, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_ofPred_eq]
      rwa [show c + T (T.symm (y - c)) = y by
        rw [ContinuousLinearEquiv.apply_symm_apply]; abel]
  have hK'compact : IsCompact K' := by
    rw [hK'eq]
    exact hcomp.image (T.symm.continuous.comp (continuous_id.sub continuous_const))
  have hK'convex : Convex ℝ K' := by
    intro x hx y hy a b ha hb hab
    rw [hK'] at hx hy ⊢
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    have h1 : a • (c + T x) + b • (c + T y) = c + T (a • x + b • y) := by
      have h2 : a • (c + T x) + b • (c + T y) = (a + b) • c + T (a • x + b • y) := by
        rw [map_add, map_smul, map_smul]
        module
      rw [h2, hab, one_smul]
    rw [← h1]
    exact hconv hx hy ha hb hab
  have hB' : closedBall (0 : V) 1 ⊆ K' := by
    intro z hz
    rw [hK']
    simp only [Set.mem_ofPred_eq]
    rw [hTapp z]
    exact hins z (by rwa [mem_closedBall, dist_zero_right] at hz)
  have hmax' : ∀ (c' : V) (M' : V →L[ℝ] V), IsInscribed K' c' M' → |M'.det| ≤ 1 := by
    intro c' M' h
    have h2 : IsInscribed K (c + T c') ((T : V →L[ℝ] V).comp M') := by
      intro y hy
      have h3 := h y hy
      rw [hK'] at h3
      simp only [Set.mem_ofPred_eq] at h3
      have h4 : c + T c' + ((T : V →L[ℝ] V).comp M') y = c + T (c' + M' y) := by
        rw [ContinuousLinearMap.comp_apply, map_add]
        abel
      rw [h4]
      exact h3
    have h5 := hmax (c + T c') ((T : V →L[ℝ] V).comp M') h2
    have h6 : ((T : V →L[ℝ] V).comp M').det = M.det * M'.det := by
      rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
        ← ContinuousLinearMap.det, ← ContinuousLinearMap.det]
      rw [hdetT]
    rw [h6, abs_mul] at h5
    have hpos' : 0 < |M.det| := abs_pos.mpr hMdet
    rwa [mul_le_iff_le_one_right hpos'] at h5
  have hsub : K' ⊆ closedBall (0 : V) (Module.finrank ℝ V) :=
    john_core K' hK'compact hK'convex hB' hmax'
  -- lifting back to `K`
  have hfr : (0 : ℝ) < (Module.finrank ℝ V : ℝ) := by exact_mod_cast hpos
  refine ⟨c, T, ?_, ?_⟩
  · intro y hy
    rw [hTapp y]
    exact hins y hy
  · intro x hx
    have hxk : T.symm (x - c) ∈ K' := by
      rw [hK']
      simp only [Set.mem_ofPred_eq]
      rwa [show c + T (T.symm (x - c)) = x by
        rw [ContinuousLinearEquiv.apply_symm_apply]; abel]
    have hnorm : ‖T.symm (x - c)‖ ≤ (Module.finrank ℝ V : ℝ) := by
      have := hsub hxk
      rwa [mem_closedBall, dist_zero_right] at this
    refine ⟨((Module.finrank ℝ V : ℝ)⁻¹) • T.symm (x - c), ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hfr.le)]
      calc (Module.finrank ℝ V : ℝ)⁻¹ * ‖T.symm (x - c)‖
          ≤ (Module.finrank ℝ V : ℝ)⁻¹ * (Module.finrank ℝ V : ℝ) :=
            mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hfr.le)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hfr)
    · rw [map_smul, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
        mul_inv_cancel₀ (ne_of_gt hfr), one_smul]
      abel


end Commons.Geometry.Convex.John

open scoped RealInnerProductSpace

namespace Commons.Geometry.Convex.John

/-- **John's ellipsoid theorem.**  A compact convex set with nonempty interior in `ℝⁿ` contains an
ellipsoid `E` around some centre `c` such that `K ⊆ c + n·(E - c)`. -/
theorem john_ellipsoid {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcomp : IsCompact K) (hconv : Convex ℝ K) (hint : (interior K).Nonempty) :
    ∃ (c : EuclideanSpace ℝ (Fin n))
      (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)),
      (∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ≤ 1 → c + T y ∈ K) ∧
      (∀ x ∈ K, ∃ y : EuclideanSpace ℝ (Fin n), ‖y‖ ≤ 1 ∧ x = c + (n : ℝ) • T y) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    obtain ⟨k, hk⟩ := hint
    refine ⟨k, ContinuousLinearEquiv.refl ℝ _, ?_, ?_⟩
    · intro y hy
      have hy0 : y = 0 := Subsingleton.elim y 0
      rw [hy0, map_zero, add_zero]
      exact interior_subset hk
    · intro x hx
      refine ⟨0, by simp, ?_⟩
      have hx0 : x = k := Subsingleton.elim x k
      rw [hx0]
      simp
  · obtain ⟨c, T, h1, h2⟩ :=
      john_ellipsoid_core (V := EuclideanSpace ℝ (Fin n))
        (by rw [finrank_euclideanSpace_fin]; exact hnpos) K hcomp hconv hint
    exact ⟨c, T, h1, fun x hx => by
      obtain ⟨y, hy, hyx⟩ := h2 x hx
      exact ⟨y, hy, by rw [hyx, finrank_euclideanSpace_fin]⟩⟩


end Commons.Geometry.Convex.John