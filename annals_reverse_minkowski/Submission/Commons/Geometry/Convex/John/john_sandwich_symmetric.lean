import Mathlib
import Submission.Commons.Geometry.Convex.John.john_ellipsoid
import Submission.Commons.Geometry.Convex.john_frame

noncomputable section

open Set Metric Filter
open scoped Topology RealInnerProductSpace Pointwise

namespace Commons.Geometry.Convex.John

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Elementary Frobenius helpers in operator space -/

lemma frob_quad {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V) (A B : V →L[ℝ] V) (s : ℝ) :
    frob e (A + s • B) (A + s • B) =
      frob e A A + 2 * s * frob e A B + s ^ 2 * frob e B B := by
  calc frob e (A + s • B) (A + s • B)
      = frob e A (A + s • B) + s * frob e B (A + s • B) := by
        rw [frob_add_left, frob_smul_left]
    _ = (frob e A A + s * frob e A B) + s * (frob e B A + s * frob e B B) := by
        rw [frob_add_right, frob_smul_right, frob_add_right, frob_smul_right]
    _ = frob e A A + 2 * s * frob e A B + s ^ 2 * frob e B B := by
        rw [frob_comm e B A]; ring

lemma frob_self_norm_sq {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V) (A : V →L[ℝ] V) :
    frob e A A = ∑ i, ‖A (e i)‖ ^ 2 := by
  simp only [frob]
  exact Finset.sum_congr rfl fun i _ => real_inner_self_eq_norm_sq _

lemma continuous_frob_self {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V) :
    Continuous fun A : V →L[ℝ] V => frob e A A := by
  rw [funext (frob_self_norm_sq e)]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (((ContinuousLinearMap.apply ℝ V (e i)).continuous.comp continuous_id).norm).pow 2

/-- **Support bound at a contact point.** If the unit ball is inscribed in a convex set `K` and
`u` is a unit vector on the boundary of `K`, then `⟨x,u⟩ ≤ 1` for every `x ∈ K`. -/
lemma john_le_of_contact {K : Set V} (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (hB : closedBall (0 : V) 1 ⊆ K) {u : V} (hu : u ∈ frontier K) (hu1 : ‖u‖ = 1) :
    ∀ x ∈ K, inner ℝ x u ≤ 1 := by
  have hball_int : ball (0 : V) 1 ⊆ interior K :=
    interior_maximal (ball_subset_closedBall.trans hB) isOpen_ball
  intro x hxK
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

/-- **Nonempty contact set.** If the unit ball is a maximal centred inscribed ellipsoid of a
compact set `K` (in positive dimension), then `K` has a contact point of unit length. -/
lemma contact_nonempty_of_max {K : Set V} (hcomp : IsCompact K)
    (hB : closedBall (0 : V) 1 ⊆ K) (hn : 0 < Module.finrank ℝ V)
    (hmax : ∀ M : V →L[ℝ] V, (∀ y, ‖y‖ ≤ 1 → M y ∈ K) → |M.det| ≤ 1) :
    (frontier K ∩ Metric.sphere (0 : V) 1).Nonempty := by
  have hsphere : ∀ u : V, (u ∈ Metric.sphere (0 : V) 1 ↔ ‖u‖ = 1) := by
    intro u
    rw [mem_sphere, dist_eq_norm, sub_zero]
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
  have hins : ∀ y : V, ‖y‖ ≤ 1 → ((1 + δ) • (1 : V →L[ℝ] V)) y ∈ K := by
    intro y hy
    rw [smul_apply, one_apply_eq_self]
    refine hball1 (by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0:ℝ) < 1 + δ)]
      nlinarith [hy])
  have hle := hmax ((1 + δ) • (1 : V →L[ℝ] V)) hins
  have hdet : ((1 + δ) • (1 : V →L[ℝ] V)).det = (1 + δ) ^ Module.finrank ℝ V := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
      ContinuousLinearMap.toLinearMap_one, LinearMap.det_smul]
    simp
  rw [hdet, abs_of_pos (by positivity)] at hle
  have hone : 1 < (1 + δ) ^ Module.finrank ℝ V :=
    one_lt_pow₀ (by linarith) (Nat.pos_iff_ne_zero.mp hn)
  linarith
/-- **Separation certificate, symmetric form.** If the operator `(1/n)` is not in the convex hull
of the rank-one operators `u ⊗ u` for `u` in a compact set `S` of unit vectors, then there is an
operator `K₀` of positive trace which is strictly negative on all of `S`:
`⟨K₀ u, u⟩ < 0`. -/
theorem exists_certificate_symmetric {ι : Type*} [Fintype ι] [CompleteSpace V]
    (S : Set V) (hScomp : IsCompact S) (hSne : S.Nonempty)
    (hSunit : ∀ u ∈ S, ‖u‖ = 1)
    (e : OrthonormalBasis ι ℝ V) (hcard : Fintype.card ι = Module.finrank ℝ V)
    (hnot : (Module.finrank ℝ V : ℝ)⁻¹ • (1 : V →L[ℝ] V) ∉ convexHull ℝ (rankOne '' S)) :
    ∃ K₀ : V →L[ℝ] V, 0 < (∑ i, inner ℝ (e i) (K₀ (e i))) ∧
      ∀ u ∈ S, inner ℝ (K₀ u) u < 0 := by
  classical
  have hnpos : 0 < Module.finrank ℝ V := by
    obtain ⟨u, hu⟩ := hSne
    have hne0 : u ≠ 0 := by
      intro h
      have h1 := hSunit u hu
      rw [h, norm_zero] at h1
      exact one_ne_zero h1.symm
    haveI : Nontrivial V := ⟨u, 0, hne0⟩
    exact Module.finrank_pos
  set p : V →L[ℝ] V := (Module.finrank ℝ V : ℝ)⁻¹ • (1 : V →L[ℝ] V) with hp
  have hcompC : IsCompact (convexHull ℝ (rankOne '' S)) :=
    isCompact_convexHull_of_isCompact (hScomp.image continuous_rankOne)
  have hneC : (convexHull ℝ (rankOne '' S)).Nonempty :=
    (hSne.image rankOne).mono (subset_convexHull ℝ (rankOne '' S))
  have hcontQ : Continuous fun A : V →L[ℝ] V => frob e (A - p) (A - p) :=
    (continuous_frob_self e).comp (continuous_id.sub continuous_const)
  obtain ⟨q, hqhull, hqmin⟩ := hcompC.exists_isMinOn hneC hcontQ.continuousOn
  have hqp : q ≠ p := fun h => hnot (h ▸ hqhull)
  have hsq : 0 < frob e (q - p) (q - p) := by
    rcases lt_or_eq_of_le (frob_self_nonneg e (q - p)) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp (frob_self_eq_zero e h.symm)) hqp
  -- the optimality inequality
  have hopt : ∀ z ∈ convexHull ℝ (rankOne '' S), 0 ≤ frob e (q - p) (z - q) := by
    intro z hz
    obtain ⟨A, B, hA, hB⟩ : ∃ A B : ℝ,
        A = frob e (q - p) (z - q) ∧ B = frob e (z - q) (z - q) := ⟨_, _, rfl, rfl⟩
    rw [← hA]
    by_contra hcon
    rw [not_le] at hcon
    have hseg : ∀ s : ℝ, s ∈ Set.Icc 0 1 →
        q + s • (z - q) ∈ convexHull ℝ (rankOne '' S) := by
      intro s hs
      exact (convex_convexHull ℝ _).add_smul_sub_mem hqhull hz hs
    have hB0 : 0 ≤ B := by rw [hB]; exact frob_self_nonneg e (z - q)
    set s : ℝ := min (1/2) ((-A) / (2 * (B + 1))) with hsdef
    have hs0 : 0 < s := by
      rw [hsdef]
      exact lt_min (by norm_num) (div_pos (by linarith) (by linarith))
    have hs1 : s ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
    have hkey : 0 ≤ 2 * A + s * B := by
      have h1 : q + s • (z - q) ∈ convexHull ℝ (rankOne '' S) := hseg s ⟨hs0.le, hs1⟩
      have h2 := hqmin h1
      change frob e (q - p) (q - p) ≤
        frob e (q + s • (z - q) - p) (q + s • (z - q) - p) at h2
      have h3 : q + s • (z - q) - p = (q - p) + s • (z - q) := by abel
      rw [h3, frob_quad] at h2
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
  -- the certificate
  set A₀ : V →L[ℝ] V := q - p with hA₀
  set m : ℝ := frob e A₀ q with hm
  have hineq : ∀ u ∈ S, m ≤ inner ℝ (A₀ u) u := by
    intro u hu
    have hmem : rankOne u ∈ convexHull ℝ (rankOne '' S) :=
      subset_convexHull ℝ _ ⟨u, hu, rfl⟩
    have h2 := hopt (rankOne u) hmem
    rw [frob_sub_right] at h2
    rw [frob_rankOne] at h2
    rw [← hm] at h2
    linarith
  have hq1 : q = A₀ + (Module.finrank ℝ V : ℝ)⁻¹ • (1 : V →L[ℝ] V) := by
    rw [hA₀, hp]; abel
  set tA : ℝ := ∑ i, inner ℝ (e i) (A₀ (e i)) with htA
  have htrA : tA = frob e A₀ (1 : V →L[ℝ] V) := by
    rw [htA, frob_comm, frob_one]
  have hm_eq : m = frob e (q - p) (q - p) + (Module.finrank ℝ V : ℝ)⁻¹ * tA := by
    have hthis : frob e A₀ q = frob e A₀ A₀ + (Module.finrank ℝ V : ℝ)⁻¹ * tA := by
      rw [hq1, frob_add_right, frob_smul_right, ← htrA]
    rw [hm, hthis, show frob e A₀ A₀ = frob e (q - p) (q - p) by rw [hA₀]]
  set μ : ℝ := ((Module.finrank ℝ V : ℝ)⁻¹ * tA + m) / 2 with hμ
  have hμ_gt : (Module.finrank ℝ V : ℝ)⁻¹ * tA < μ := by rw [hμ]; linarith [hsq, hm_eq]
  have hμ_lt : μ < m := by rw [hμ]; linarith [hsq, hm_eq]
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
  refine ⟨-A₀ + μ • (1 : V →L[ℝ] V), ?_, ?_⟩
  · rw [htr]
    have hnpos' : (0 : ℝ) < (Module.finrank ℝ V : ℝ) := by exact_mod_cast hnpos
    have h1 : tA < μ * (Module.finrank ℝ V : ℝ) := by
      have h := mul_lt_mul_of_pos_left hμ_gt hnpos'
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hnpos'), one_mul, mul_comm] at h
      exact h
    linarith
  · intro u hu
    have h2 := hineq u hu
    have hu1 : inner ℝ u u = 1 := by
      rw [real_inner_self_eq_norm_sq, hSunit u hu]
      simp
    have h3 : inner ℝ ((-A₀ + μ • (1 : V →L[ℝ] V)) u) u = μ - inner ℝ (A₀ u) u := by
      simp only [add_apply, neg_apply, smul_apply, one_apply_eq_self, inner_add_left,
        inner_neg_left, inner_smul_left, RCLike.conj_to_real]
      rw [hu1]
      ring
    rw [h3]
    linarith [h2, hμ_lt]
/-- **A maximal centred inscribed ellipsoid.** For a symmetric compact convex set `K` with
nonempty interior there is an invertible `M` with `M '' B₁ ⊆ K` whose determinant is maximal
in absolute value among all centred inscribed ellipsoids. -/
theorem exists_max_det_centered (K : Set V) (hcomp : IsCompact K) (hconv : Convex ℝ K)
    (hsymm : ∀ x, x ∈ K ↔ -x ∈ K) (hint : (interior K).Nonempty) :
    ∃ M : V →L[ℝ] V, (∀ y, ‖y‖ ≤ 1 → M y ∈ K) ∧ M.det ≠ 0 ∧
      ∀ M' : V →L[ℝ] V, (∀ y, ‖y‖ ≤ 1 → M' y ∈ K) → |M'.det| ≤ |M.det| := by
  classical
  obtain ⟨z, hz⟩ := hint
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hz
  obtain ⟨ε, hεpos, hεK⟩ := hz
  set r : ℝ := ε / 2 with hr
  have hrpos : 0 < r := by positivity
  have hrball : closedBall (0 : V) r ⊆ K := by
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    have hlt : ‖w‖ < ε := by rw [hr] at hw; linarith
    have h1 : z + w ∈ K := hεK (by rw [mem_ball, dist_eq_norm]; simpa using hlt)
    have h2 : z - w ∈ K := hεK (by
      rw [mem_ball, dist_eq_norm, show z - w - z = -w by abel, norm_neg]; exact hlt)
    have h3 : -z + w ∈ K := by
      have h := (hsymm (z - w)).mp h2
      rwa [show -(z - w) = -z + w by abel] at h
    have h4 : w = (1/2 : ℝ) • (z + w) + (1/2 : ℝ) • (-z + w) := by module
    rw [h4]
    exact hconv h1 h3 (by norm_num) (by norm_num) (by norm_num)
  have h0K : (0 : V) ∈ K := hrball (by rw [mem_closedBall, dist_zero_right, norm_zero]; exact hrpos.le)
  let S : Set (V →L[ℝ] V) := {M | ∀ y, ‖y‖ ≤ 1 → M y ∈ K}
  have hmemS : ∀ M, M ∈ S ↔ (∀ y, ‖y‖ ≤ 1 → M y ∈ K) := fun M => Iff.rfl
  have hclosed : IsClosed S := by
    have hset : S = ⋂ y ∈ closedBall (0 : V) 1, {M : V →L[ℝ] V | M y ∈ K} := by
      ext M
      simp only [S, Set.mem_ofPred_eq, Set.mem_iInter, mem_closedBall, dist_zero_right]
    rw [hset]
    refine isClosed_biInter fun y hy => hcomp.isClosed.preimage ?_
    exact (ContinuousLinearMap.apply ℝ V y).continuous
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ C := by
    have hb : Bornology.IsBounded K := hcomp.isBounded
    rwa [Metric.isBounded_iff] at hb
  set R : ℝ := max C 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRnn : 0 ≤ R := by linarith
  have hRC : C ≤ R := le_max_left _ _
  have hsub : S ⊆ closedBall (0 : V →L[ℝ] V) R := by
    intro M hM
    rw [mem_closedBall, dist_zero_right]
    refine ContinuousLinearMap.opNorm_le_bound M hRnn fun y => ?_
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have hnorm : ‖(‖y‖⁻¹ : ℝ) • y‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
      have h1 : M ((‖y‖⁻¹ : ℝ) • y) ∈ K := (hmemS M).mp hM _ (le_of_eq hnorm)
      have h3 : ‖M ((‖y‖⁻¹ : ℝ) • y)‖ ≤ C := by
        have h4 := hC _ h1 0 h0K
        rwa [dist_zero_right] at h4
      have key : ‖M y‖ = ‖y‖ * ‖M ((‖y‖⁻¹ : ℝ) • y)‖ := by
        rw [map_smul, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y)), ← mul_assoc,
          mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_mul]
      calc ‖M y‖ = ‖y‖ * ‖M ((‖y‖⁻¹ : ℝ) • y)‖ := key
        _ ≤ ‖y‖ * C := mul_le_mul_of_nonneg_left h3 (norm_nonneg y)
        _ ≤ ‖y‖ * R := mul_le_mul_of_nonneg_left hRC (norm_nonneg y)
        _ = R * ‖y‖ := by ring
  have hcompS : IsCompact S :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : V →L[ℝ] V) R) hclosed hsub
  have hball_mem : (r • (1 : V →L[ℝ] V)) ∈ S := by
    rw [hmemS]
    intro y hy
    have h1 : (r • (1 : V →L[ℝ] V)) y = r • y := rfl
    rw [h1]
    refine hrball ?_
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
    exact mul_le_of_le_one_right hrpos.le hy
  have hcont : ContinuousOn (fun M : V →L[ℝ] V => |M.det|) S :=
    ((ContinuousLinearMap.continuous_det.comp continuous_id).abs).continuousOn
  obtain ⟨M, hMS, hMMax⟩ := hcompS.exists_isMaxOn ⟨_, hball_mem⟩ hcont
  have hdet0 : (r • (1 : V →L[ℝ] V)).det ≠ 0 := by
    rw [show (r • (1 : V →L[ℝ] V)).det = r ^ Module.finrank ℝ V by
      simp [ContinuousLinearMap.det, LinearMap.det_smul]]
    exact pow_ne_zero _ (ne_of_gt hrpos)
  refine ⟨M, (hmemS M).mp hMS, ?_, ?_⟩
  · intro hzero
    have hle : |(r • (1 : V →L[ℝ] V)).det| ≤ |M.det| := hMMax hball_mem
    rw [hzero, abs_zero] at hle
    have hpos : 0 < |(r • (1 : V →L[ℝ] V)).det| := abs_pos.mpr hdet0
    linarith
  · intro M' hM'
    exact hMMax ((hmemS M').mpr hM')
/-- **Symmetric John core.** If `K` is compact, convex and symmetric, contains the unit ball, and
the unit ball is maximal among the centred inscribed ellipsoids of `K`, then `K` is contained in
the ball of radius `√(dim V)`. -/
theorem john_core_symmetric [CompleteSpace V] (K : Set V) (hcomp : IsCompact K)
    (hconv : Convex ℝ K) (hsymm : ∀ x, x ∈ K ↔ -x ∈ K) (hB : closedBall (0 : V) 1 ⊆ K)
    (hmax : ∀ M : V →L[ℝ] V, (∀ y, ‖y‖ ≤ 1 → M y ∈ K) → |M.det| ≤ 1) :
    K ⊆ closedBall (0 : V) (Real.sqrt (Module.finrank ℝ V)) := by
  classical
  have hsphere : ∀ u : V, (u ∈ Metric.sphere (0 : V) 1 ↔ ‖u‖ = 1) := by
    intro u
    rw [mem_sphere, dist_eq_norm, sub_zero]
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ V) with hn0 | hnpos
  · intro x _
    haveI : Subsingleton V := Module.finrank_zero_iff.mp hn0
    rw [mem_closedBall, dist_zero_right]
    have hx : x = 0 := Subsingleton.elim x 0
    simp [hx, hn0]
  · have hnpos' : (0:ℝ) < (Module.finrank ℝ V : ℝ) := by exact_mod_cast hnpos
    have hKle : ∀ u ∈ frontier K, ‖u‖ = 1 → ∀ x ∈ K, inner ℝ u x ≤ 1 := by
      intro u hu h1 x hx
      have := john_le_of_contact hcomp hconv hB hu h1 x hx
      rwa [real_inner_comm] at this
    have hUne := contact_nonempty_of_max hcomp hB hnpos hmax
    set S : Set V := frontier K ∩ Metric.sphere (0 : V) 1 with hSdef
    have hSunit : ∀ u ∈ S, ‖u‖ = 1 := fun u hu => (hsphere u).mp hu.2
    have hScomp : IsCompact S := isCompact_frontier_inter_sphere hcomp
    have hSne : S.Nonempty := hUne
    have hcenter : (Module.finrank ℝ V : ℝ)⁻¹ • (1 : V →L[ℝ] V) ∈
        convexHull ℝ (rankOne '' S) := by
      by_contra hnot
      let e : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V := stdOrthonormalBasis ℝ V
      have hcard : Fintype.card (Fin (Module.finrank ℝ V)) = Module.finrank ℝ V :=
        Fintype.card_fin _
      obtain ⟨K₀, htr, hneg⟩ := exists_certificate_symmetric S hScomp hSne hSunit e hcard hnot
      have htr' : 0 < LinearMap.trace ℝ V K₀.toLinearMap := by
        rwa [LinearMap.trace_eq_sum_inner K₀.toLinearMap e]
      have hneg' : ∀ u ∈ frontier K, ‖u‖ = 1 →
          inner ℝ (K₀ u) u + inner ℝ (0 : V) u < 0 := by
        intro u hu h1
        have : u ∈ S := ⟨hu, (hsphere u).mpr h1⟩
        simpa using hneg u this
      obtain ⟨δ₁, hδ₁, hmem⟩ := john_perturbation_membership hcomp hconv hB hneg'
      obtain ⟨δ₂, hδ₂, hdgt⟩ := det_one_add_smul_gt_one K₀ htr'
      have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
      set t : ℝ := min δ₁ δ₂ / 2 with ht
      have ht1 : t ∈ Set.Ioo 0 δ₁ :=
        ⟨by rw [ht]; linarith, by rw [ht]; linarith [min_le_left δ₁ δ₂]⟩
      have ht2 : t ∈ Set.Ioo 0 δ₂ :=
        ⟨by rw [ht]; linarith, by rw [ht]; linarith [min_le_right δ₁ δ₂]⟩
      have hins : ∀ y : V, ‖y‖ ≤ 1 → (1 + t • K₀) y ∈ K := by
        intro y hy
        simpa using hmem t ht1 y hy
      have hle := hmax (1 + t • K₀) hins
      have hgt := hdgt t ht2
      linarith
    obtain ⟨ι, hι, z, w, hzs, hind, hwpos, hwsum, hwz⟩ :=
      eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) hcenter
    have hz : ∀ i, z i ∈ rankOne '' S := fun i => hzs (Set.mem_range_self i)
    choose u huS hzu using hz
    have hop : ∑ i, w i • rankOne (u i) = (Module.finrank ℝ V : ℝ)⁻¹ • (1 : V →L[ℝ] V) := by
      rw [← hwz]
      exact Finset.sum_congr rfl fun i _ => by rw [← hzu i]
    have hop' : ∑ i, ((Module.finrank ℝ V : ℝ) * w i) • rankOne (u i) = 1 := by
      have h1 : (Module.finrank ℝ V : ℝ) • (∑ i, w i • rankOne (u i))
          = ∑ i, ((Module.finrank ℝ V : ℝ) * w i) • rankOne (u i) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
      rw [← h1, hop, smul_smul, mul_inv_cancel₀ (ne_of_gt hnpos'), one_smul]
    have hframe : ∀ y : V,
        ∑ i, ((Module.finrank ℝ V : ℝ) * w i) * inner ℝ (u i) y ^ 2 = ‖y‖ ^ 2 := by
      intro y
      have h1 : (∑ i, ((Module.finrank ℝ V : ℝ) * w i) • rankOne (u i)) y = y := by
        rw [hop']; simp
      rw [sum_apply] at h1
      simp only [smul_apply, rankOne_apply] at h1
      have h2 : inner ℝ (∑ i, ((Module.finrank ℝ V : ℝ) * w i) •
          (inner ℝ (u i) y • u i)) y = ‖y‖ ^ 2 := by
        rw [h1, real_inner_self_eq_norm_sq]
      rw [sum_inner] at h2
      simp only [inner_smul_left, RCLike.conj_to_real] at h2
      rw [← h2]
      exact Finset.sum_congr rfl fun i _ => by ring
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    have hx2 : ‖x‖ ^ 2 ≤ (Module.finrank ℝ V : ℝ) := by
      rw [← hframe x]
      have hsum : ∑ i, ((Module.finrank ℝ V : ℝ) * w i) * inner ℝ (u i) x ^ 2
          ≤ ∑ i, ((Module.finrank ℝ V : ℝ) * w i) * 1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hc : 0 ≤ (Module.finrank ℝ V : ℝ) * w i := (mul_pos hnpos' (hwpos i)).le
        refine mul_le_mul_of_nonneg_left ?_ hc
        have h1 := hKle (u i) (huS i).1 (hSunit (u i) (huS i)) x hx
        have h2 := hKle (u i) (huS i).1 (hSunit (u i) (huS i)) (-x) ((hsymm x).mp hx)
        rw [inner_neg_right] at h2
        nlinarith [h1, h2]
      calc ∑ i, ((Module.finrank ℝ V : ℝ) * w i) * inner ℝ (u i) x ^ 2
          ≤ ∑ i, ((Module.finrank ℝ V : ℝ) * w i) * 1 := hsum
        _ = (Module.finrank ℝ V : ℝ) * ∑ i, w i := by
            simp only [mul_one]; rw [Finset.mul_sum]
        _ = (Module.finrank ℝ V : ℝ) := by rw [hwsum]; ring
    rw [← Real.sqrt_sq (norm_nonneg x)]
    exact Real.sqrt_le_sqrt hx2
/-- **Fritz John's theorem, symmetric case.** A symmetric convex body with nonempty interior
is trapped between an ellipsoid `T '' B₁` and its `√n` multiple: `T '' B₁ ⊆ K ⊆ √n • (T '' B₁)`.

This is the symmetric refinement of `Commons.Geometry.Convex.John.john_ellipsoid` (which gives
only `K ⊆ c + n • T '' B₁`): for symmetric `K` the maximal-volume inscribed ellipsoid is centered
at `0` and the John frame comes in `±` pairs, so the factor improves from `n` to `√n`.

The intended proof: use `john_ellipsoid_core`/`john_frame`-style arguments in the symmetric
setting. -/
theorem john_sandwich_symmetric {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKcomp : IsCompact K) (hKconv : Convex ℝ K)
    (hKsymm : ∀ x, x ∈ K ↔ -x ∈ K) (hKint : (interior K).Nonempty) :
    ∃ T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ≤ 1 → T y ∈ K) ∧
      (∀ x ∈ K, ∃ y : EuclideanSpace ℝ (Fin n), ‖y‖ ≤ 1 ∧ x = Real.sqrt n • T y) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    obtain ⟨k, hk⟩ := hKint
    have hkK : k ∈ K := interior_subset hk
    have h0K : (0 : EuclideanSpace ℝ (Fin 0)) ∈ K := by
      have := hKconv hkK ((hKsymm k).mp hkK) (show (0:ℝ) ≤ 1/2 by norm_num)
        (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ) + 1/2 = 1 by norm_num)
      simpa using this
    refine ⟨ContinuousLinearEquiv.refl ℝ _, ?_, ?_⟩
    · intro y hy
      have hy0 : y = 0 := Subsingleton.elim y 0
      rw [hy0, map_zero]
      exact h0K
    · intro x hx
      refine ⟨0, by simp, ?_⟩
      have hx0 : x = 0 := Subsingleton.elim x 0
      rw [hx0, Nat.cast_zero, Real.sqrt_zero, zero_smul]
  · obtain ⟨M, hMins, hMdet, hMmax⟩ := exists_max_det_centered K hKcomp hKconv hKsymm hKint
    have hker : M.toLinearMap.ker = ⊥ := by
      by_contra h
      exact hMdet ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr h)
    have hinj : Function.Injective M := LinearMap.ker_eq_bot.mp hker
    have hsurj : Function.Surjective M := LinearMap.surjective_of_injective hinj
    let Mₑ : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      LinearEquiv.ofBijective M.toLinearMap ⟨hinj, hsurj⟩
    let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) := Mₑ.toContinuousLinearEquiv
    have hTM : (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = M :=
      ContinuousLinearMap.ext fun x => rfl
    have hTapp : ∀ z : EuclideanSpace ℝ (Fin n), T z = M z :=
      fun z => ContinuousLinearMap.ext_iff.mp hTM z
    let K' : Set (EuclideanSpace ℝ (Fin n)) := {z | T z ∈ K}
    have hK'mem : ∀ z, z ∈ K' ↔ T z ∈ K := fun z => Iff.rfl
    have hK'compact : IsCompact K' := by
      have heq : K' = T.symm '' K := by
        ext z
        constructor
        · intro hz
          exact ⟨T z, (hK'mem z).mp hz, by simp⟩
        · rintro ⟨y, hy, rfl⟩
          rw [hK'mem, ContinuousLinearEquiv.apply_symm_apply]
          exact hy
      rw [heq]
      exact hKcomp.image T.symm.continuous
    have hK'convex : Convex ℝ K' := by
      intro x hx y hy a b ha hb hab
      rw [hK'mem] at hx hy ⊢
      rw [map_add, map_smul, map_smul]
      exact hKconv hx hy ha hb hab
    have hK'symm : ∀ x, x ∈ K' ↔ -x ∈ K' := by
      intro x
      rw [hK'mem, hK'mem, map_neg]
      exact hKsymm (T x)
    have hB' : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K' := by
      intro z hz
      rw [hK'mem, hTapp z]
      exact hMins z (by rwa [mem_closedBall, dist_zero_right] at hz)
    have hmax' : ∀ M' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        (∀ y, ‖y‖ ≤ 1 → M' y ∈ K') → |M'.det| ≤ 1 := by
      intro M' hM'
      have h2 : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ≤ 1 →
          (M.comp M') y ∈ K := by
        intro y hy
        have h3 := hM' y hy
        rw [hK'mem] at h3
        rw [ContinuousLinearMap.comp_apply]
        rwa [← hTapp]
      have h5 := hMmax (M.comp M') h2
      have h6 : (M.comp M').det = M.det * M'.det := by
        rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
          ← ContinuousLinearMap.det, ← ContinuousLinearMap.det]
      rw [h6, abs_mul] at h5
      have hpos' : 0 < |M.det| := abs_pos.mpr hMdet
      rwa [mul_le_iff_le_one_right hpos'] at h5
    have hsub := john_core_symmetric K' hK'compact hK'convex hK'symm hB' hmax'
    have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
    refine ⟨T, ?_, ?_⟩
    · intro y hy
      rw [hTapp y]
      exact hMins y hy
    · intro x hx
      have hxK' : T.symm x ∈ K' := by
        rw [hK'mem, ContinuousLinearEquiv.apply_symm_apply]
        exact hx
      have hnorm : ‖T.symm x‖ ≤ Real.sqrt n := by
        have h := hsub hxK'
        rw [mem_closedBall, dist_zero_right] at h
        rwa [hfin] at h
      have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
      refine ⟨(Real.sqrt n)⁻¹ • T.symm x, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
        calc (Real.sqrt n)⁻¹ * ‖T.symm x‖ ≤ (Real.sqrt n)⁻¹ * Real.sqrt n :=
              mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (Real.sqrt_nonneg _))
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hsqrtpos)
      · rw [map_smul, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
          mul_inv_cancel₀ (ne_of_gt hsqrtpos), one_smul]
end Commons.Geometry.Convex.John
