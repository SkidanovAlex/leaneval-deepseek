import Mathlib
import Submission.Work.Whitney.PathTools.RemovabilityGeneral

/-!
# A compact totally disconnected set is removable in a sphere of dimension `≥ 2`

Target: `Work.Whitney.PathTools.sphere_sdiff_isCompact_totallyDisconnected_isPreconnected`.

`E` is a finite dimensional real inner product space with `3 ≤ finrank ℝ E`, `K ⊆ E` is compact
and totally disconnected and `K ⊆ Metric.sphere c r` (`0 < r`).  Then `Metric.sphere c r \ K` is
preconnected (and, since the sphere is locally path connected, path connected).

Proof.  Pick a point `p` of the sphere outside `K` (it exists because the sphere is preconnected
with at least two points while `K` is totally disconnected) and let `v` be the unit vector with
`p = c + r • v`.  The central projection from `p` maps the hyperplane `vᗮ` onto `sphere c r \ {p}`:

  `Φ x = c + t • x + r(1 - t) • v`,   `t = 2r²/(r² + ‖x‖²)`.

`Φ` is continuous and injective on `vᗮ`, it maps into the sphere and omits `p`, and
`‖Φ x - p‖ = 2r² / √(‖x‖² + r²)`, so the preimage `K'` of `K` is compact.  It is totally
disconnected as well, hence by the flat removability theorem
(`compl_isCompact_isTotallyDisconnected_pathConnected_gen`) applied in the inner product space
`vᗮ` of dimension `n - 1 ≥ 2`, the complement of `K'` in `vᗮ` is path connected.  Its image under
`Φ` is `(sphere c r \ K) \ {p}`, which is therefore preconnected; and `p` lies in its closure
because `p ∉ K` and the sphere is not discrete.  Hence `sphere c r \ K` is preconnected.
-/

set_option maxHeartbeats 4000000

namespace Work.Whitney.PathTools

open Set Metric Topology
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Adjoining a point in the closure of a preconnected set keeps it preconnected. -/
lemma isPreconnected_insert_of_mem_closure {X : Type*} [TopologicalSpace X] {s : Set X} {x : X}
    (hs : IsPreconnected s) (hx : x ∈ closure s) : IsPreconnected (insert x s) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv huv huvdisj
  have h1 : s ⊆ u ∪ v := fun z hz => huv (Set.mem_insert_of_mem x hz)
  have h2 : s ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    exact Set.eq_empty_iff_forall_notMem.mp huvdisj z
      ⟨Set.mem_insert_of_mem x hz.1, hz.2⟩
  rcases (isPreconnected_iff_subset_of_disjoint.mp hs) u v hu hv h1 h2 with hs' | hs'
  · by_cases hxu : x ∈ u
    · refine Or.inl fun z hz => ?_
      rcases Set.mem_insert_iff.mp hz with rfl | hz'
      · exact hxu
      · exact hs' hz'
    · exfalso
      have hxv : x ∈ v := by
        rcases huv (by simp : x ∈ insert x s) with h | h
        · exact absurd h hxu
        · exact h
      obtain ⟨z, hzv, hzs⟩ := mem_closure_iff.mp hx v hv hxv
      exact Set.eq_empty_iff_forall_notMem.mp h2 z ⟨hzs, hs' hzs, hzv⟩
  · by_cases hxv : x ∈ v
    · refine Or.inr fun z hz => ?_
      rcases Set.mem_insert_iff.mp hz with rfl | hz'
      · exact hxv
      · exact hs' hz'
    · exfalso
      have hxu : x ∈ u := by
        rcases huv (by simp : x ∈ insert x s) with h | h
        · exact h
        · exact absurd h hxv
      obtain ⟨z, hzu, hzs⟩ := mem_closure_iff.mp hx u hu hxu
      exact Set.eq_empty_iff_forall_notMem.mp h2 z ⟨hzs, hzu, hs' hzs⟩

/-- The elementary algebra of the central projection: it maps the whole space into the sphere. -/
lemma central_norm {v : E} (hv : ‖v‖ = 1) {r : ℝ} (hr : 0 < r) {x : E}
    (hx : ⟪x, v⟫_ℝ = 0) :
    ‖(2 * r ^ 2 / (r ^ 2 + ‖x‖ ^ 2)) • x +
      (r * (1 - 2 * r ^ 2 / (r ^ 2 + ‖x‖ ^ 2))) • v‖ = r := by
  set a : ℝ := 2 * r ^ 2 / (r ^ 2 + ‖x‖ ^ 2) with ha
  set b : ℝ := r * (1 - 2 * r ^ 2 / (r ^ 2 + ‖x‖ ^ 2)) with hb
  have hz : ⟪a • x, b • v⟫_ℝ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hx, mul_zero, mul_zero]
  have hsq : ‖a • x + b • v‖ ^ 2 = r ^ 2 := by
    have h2 : ‖a • x + b • v‖ ^ 2 = ‖a • x‖ ^ 2 + ‖b • v‖ ^ 2 := by
      rw [norm_add_sq_real, hz]; ring
    have h3 : ‖a • x‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have h4 : ‖b • v‖ ^ 2 = b ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
    rw [h2, h3, h4, ha, hb]
    have h1 : r ^ 2 + ‖x‖ ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have hn := norm_nonneg (a • x + b • v)
    rw [ha, hb] at h
    linarith

/-- The inverse formula for the central projection: the preimage of a point of the sphere. -/
lemma central_preimage {v : E} (hv : ‖v‖ = 1) {r : ℝ} (hr : 0 < r) {y : E}
    (hy : ‖y‖ = r) (hσ : ⟪y, v⟫_ℝ < r) :
    (2 * r ^ 2 / (r ^ 2 + ‖(r / (r - ⟪y, v⟫_ℝ)) • (y - ⟪y, v⟫_ℝ • v)‖ ^ 2)) •
        ((r / (r - ⟪y, v⟫_ℝ)) • (y - ⟪y, v⟫_ℝ • v)) +
      (r * (1 - 2 * r ^ 2 / (r ^ 2 + ‖(r / (r - ⟪y, v⟫_ℝ)) • (y - ⟪y, v⟫_ℝ • v)‖ ^ 2))) • v
      = y := by
  set σ : ℝ := ⟪y, v⟫_ℝ with hσdef
  set x : E := (r / (r - σ)) • (y - σ • v) with hxdef
  have hne : r - σ ≠ 0 := ne_of_gt (by linarith)
  have hsub : ‖y - σ • v‖ ^ 2 = r ^ 2 - σ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hv, mul_one,
      sq_abs, ← hσdef, hy]
    ring
  have hxnorm : ‖x‖ ^ 2 = r ^ 2 * (r + σ) / (r - σ) := by
    rw [hxdef, norm_smul, Real.norm_of_nonneg (by positivity), mul_pow]
    rw [show ‖y - σ • v‖ ^ 2 = r ^ 2 - σ ^ 2 from hsub]
    field_simp
    ring
  have hden : r ^ 2 + ‖x‖ ^ 2 = 2 * r ^ 3 / (r - σ) := by
    rw [hxnorm]
    field_simp
    ring
  have ht : 2 * r ^ 2 / (r ^ 2 + ‖x‖ ^ 2) = (r - σ) / r := by
    rw [hden]
    field_simp
  have hmul : ((r - σ) / r) • x = y - σ • v := by
    have h1 : (r - σ) / r * (r / (r - σ)) = 1 := by field_simp
    calc ((r - σ) / r) • x = ((r - σ) / r * (r / (r - σ))) • (y - σ • v) := by
          rw [hxdef, smul_smul]
      _ = (1 : ℝ) • (y - σ • v) := by rw [h1]
      _ = y - σ • v := one_smul _ _
  rw [show (2 * r ^ 2 / (r ^ 2 + ‖x‖ ^ 2)) = (r - σ) / r from ht, hmul]
  have hcoef : r * (1 - (r - σ) / r) = σ := by field_simp; ring
  rw [hcoef]
  abel

/-- The central projection is a bijection from `vᗮ` onto `sphere c r \ {c + r • v}`. -/
theorem sphere_sdiff_isCompact_totallyDisconnected_isPreconnected [FiniteDimensional ℝ E]
    (hm : 3 ≤ Module.finrank ℝ E) {c : E} {r : ℝ} (hr : 0 < r) {K : Set E}
    (hK : IsCompact K) (hsub : K ⊆ Metric.sphere c r) (htd : IsTotallyDisconnected K) :
    IsPreconnected (Metric.sphere c r \ K) := by
  classical
  haveI hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  -- ### step 0: the sphere is not contained in `K`
  have hnotsub : ¬ (Metric.sphere c r ⊆ K) := by
    intro hsub'
    obtain ⟨w, hw⟩ : ∃ w : E, w ≠ 0 := by
      obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
      exact ⟨a - b, sub_ne_zero.mpr hab⟩
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    set u : E := ‖w‖⁻¹ • w with hudef
    have hu : ‖u‖ = 1 := by
      rw [hudef, norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hwn)]
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hu
      norm_num at hu
    have hru : r • u ≠ 0 := smul_ne_zero (ne_of_gt hr) hu0
    have hm1 : c + r • u ∈ Metric.sphere c r := by
      rw [Metric.mem_sphere, dist_eq_norm,
        show c + r • u - c = r • u by abel, norm_smul, Real.norm_of_nonneg hr.le, hu, mul_one]
    have hm2 : c - r • u ∈ Metric.sphere c r := by
      rw [Metric.mem_sphere, dist_eq_norm,
        show c - r • u - c = -(r • u) by abel, norm_neg, norm_smul,
        Real.norm_of_nonneg hr.le, hu, mul_one]
    have hne : c + r • u ≠ c - r • u := by
      intro hcon
      have h2 : r • u = -(r • u) := by
        have h3 : (c + r • u) - c = (c - r • u) - c := by rw [hcon]
        simpa using h3
      have h4 : r • u + r • u = 0 := eq_neg_iff_add_eq_zero.mp h2
      have h5 : (2 : ℝ) • (r • u) = 0 := by rw [two_smul]; exact h4
      rcases smul_eq_zero.mp h5 with h6 | h6
      · norm_num at h6
      · exact hru h6
    have hrank1 : (1 : Cardinal) < Module.rank ℝ E := by
      rw [← Module.finrank_eq_rank]
      exact_mod_cast (by omega : 1 < Module.finrank ℝ E)
    have hsingle : (Metric.sphere c r).Subsingleton :=
      htd _ hsub' (isPreconnected_sphere hrank1 c r)
    exact hne (hsingle hm1 hm2)
  obtain ⟨p, hpS, hpK⟩ := Set.not_subset.mp hnotsub
  -- ### step 1: the unit vector `v` with `p = c + r • v`, and the hyperplane `vᗮ`
  have hpc : ‖p - c‖ = r := by
    have h := Metric.mem_sphere.mp hpS
    rwa [dist_eq_norm] at h
  set v : E := r⁻¹ • (p - c) with hvdef
  have hvn : ‖v‖ = 1 := by
    rw [hvdef, norm_smul, Real.norm_of_nonneg (by positivity), hpc]
    field_simp
  have hpv : c + r • v = p := by
    rw [hvdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
    abel
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hvn
    norm_num at hvn
  set W : Submodule ℝ E := (Submodule.span ℝ {v})ᗮ with hWdef
  have hrankW : 2 ≤ Module.finrank ℝ ↥W := by
    have h1 : Module.finrank ℝ ↥(Submodule.span ℝ ({v} : Set E)) = 1 :=
      finrank_span_singleton hv0
    have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ)
      (Submodule.span ℝ ({v} : Set E))
    rw [← hWdef] at h2
    omega
  have hWmem : ∀ x : ↥W, ⟪v, (x : E)⟫_ℝ = 0 := by
    intro x
    have h1 : (x : E) ∈ (Submodule.span ℝ ({v} : Set E))ᗮ := x.2
    exact (Submodule.mem_orthogonal _ _).mp h1 v (Submodule.mem_span_singleton_self v)
  -- ### step 2: the central projection
  set Φ : E → E := fun x => c + (2 * r ^ 2 / (r ^ 2 + ‖x‖ ^ 2)) • x +
      (r * (1 - 2 * r ^ 2 / (r ^ 2 + ‖x‖ ^ 2))) • v with hΦdef
  have hΦcont : Continuous Φ := by
    rw [hΦdef]
    have hden : Continuous fun x : E => r ^ 2 + ‖x‖ ^ 2 :=
      continuous_const.add (continuous_norm.pow 2)
    have hf : Continuous fun x : E => 2 * r ^ 2 / (r ^ 2 + ‖x‖ ^ 2) :=
      continuous_const.div₀ hden (fun x => ne_of_gt (by positivity : (0:ℝ) < r ^ 2 + ‖x‖ ^ 2))
    have hg : Continuous fun x : E => r * (1 - 2 * r ^ 2 / (r ^ 2 + ‖x‖ ^ 2)) :=
      continuous_const.mul (continuous_const.sub hf)
    exact (continuous_const.add (hf.smul continuous_id)).add (hg.smul continuous_const)
  have hΦsub : ∀ x : ↥W, Φ (x : E) - c =
      (2 * r ^ 2 / (r ^ 2 + ‖(x : E)‖ ^ 2)) • (x : E) +
        (r * (1 - 2 * r ^ 2 / (r ^ 2 + ‖(x : E)‖ ^ 2))) • v := by
    intro x
    rw [hΦdef, sub_eq_iff_eq_add]
    module
  have hΦv : ∀ x : ↥W, ⟪Φ (x : E) - c, v⟫_ℝ =
      r * (1 - 2 * r ^ 2 / (r ^ 2 + ‖(x : E)‖ ^ 2)) := by
    intro x
    rw [hΦsub x, inner_add_left, real_inner_smul_left,
      show ⟪(x : E), v⟫_ℝ = 0 by rw [real_inner_comm]; exact hWmem x, mul_zero, zero_add,
      real_inner_smul_left, real_inner_self_eq_norm_sq, hvn]
    ring
  have hΦsphere : ∀ x : ↥W, Φ (x : E) ∈ Metric.sphere c r := by
    intro x
    rw [Metric.mem_sphere, dist_eq_norm, hΦsub x]
    exact central_norm hvn hr (by rw [real_inner_comm]; exact hWmem x)
  have hΦnotp : ∀ x : ↥W, Φ (x : E) ≠ p := by
    intro x hcon
    have h1 := hΦv x
    rw [hcon, ← hpv] at h1
    have h2 : ⟪c + r • v - c, v⟫_ℝ = r := by
      rw [show c + r • v - c = r • v by abel, real_inner_smul_left, real_inner_self_eq_norm_sq,
        hvn]
      ring
    rw [h2] at h1
    have h3 : (0:ℝ) < 2 * r ^ 2 / (r ^ 2 + ‖(x : E)‖ ^ 2) := by positivity
    nlinarith [h1, h3, hr]
  have hΦinj : ∀ x y : ↥W, Φ (x : E) = Φ (y : E) → x = y := by
    intro x y h
    have hb : r * (1 - 2 * r ^ 2 / (r ^ 2 + ‖(x : E)‖ ^ 2)) =
        r * (1 - 2 * r ^ 2 / (r ^ 2 + ‖(y : E)‖ ^ 2)) := by
      rw [← hΦv x, ← hΦv y, h]
    have hb' : (1 - 2 * r ^ 2 / (r ^ 2 + ‖(x : E)‖ ^ 2)) =
        (1 - 2 * r ^ 2 / (r ^ 2 + ‖(y : E)‖ ^ 2)) :=
      mul_left_cancel₀ (ne_of_gt hr) hb
    have ht : 2 * r ^ 2 / (r ^ 2 + ‖(x : E)‖ ^ 2) =
        2 * r ^ 2 / (r ^ 2 + ‖(y : E)‖ ^ 2) := by linarith
    have h2 : (2 * r ^ 2 / (r ^ 2 + ‖(x : E)‖ ^ 2)) • (x : E) =
        (2 * r ^ 2 / (r ^ 2 + ‖(y : E)‖ ^ 2)) • (y : E) := by
      have h3 : c + (2 * r ^ 2 / (r ^ 2 + ‖(x : E)‖ ^ 2)) • (x : E) +
            (r * (1 - 2 * r ^ 2 / (r ^ 2 + ‖(x : E)‖ ^ 2))) • v =
          c + (2 * r ^ 2 / (r ^ 2 + ‖(y : E)‖ ^ 2)) • (y : E) +
            (r * (1 - 2 * r ^ 2 / (r ^ 2 + ‖(y : E)‖ ^ 2))) • v := by
        rw [hΦdef] at h
        exact h
      rw [← hb'] at h3
      exact add_left_cancel (add_right_cancel h3)
    rw [← ht] at h2
    have hpos : (0:ℝ) < 2 * r ^ 2 / (r ^ 2 + ‖(x : E)‖ ^ 2) := by positivity
    have h4 : (x : E) = (y : E) := smul_right_injective E (ne_of_gt hpos) h2
    exact Subtype.ext h4
  have hΦsurj : ∀ z : E, z ∈ Metric.sphere c r → z ≠ p → ∃ x : ↥W, Φ (x : E) = z := by
    intro z hz hzp
    have hzr : ‖z - c‖ = r := by
      have h := Metric.mem_sphere.mp hz
      rwa [dist_eq_norm] at h
    set σ : ℝ := ⟪z - c, v⟫_ℝ with hσdef
    have hzσ : σ < r := by
      have h1 : 0 < ‖(z - c) - r • v‖ := by
        rw [norm_pos_iff]
        intro hzero
        refine hzp ?_
        have h2 : z - c = r • v := sub_eq_zero.mp hzero
        have h3 : z = p := by
          have h4 : z = (z - c) + c := (sub_add_cancel z c).symm
          rw [h4, h2, add_comm]
          exact hpv
        exact h3
      have h2 : ‖(z - c) - r • v‖ ^ 2 = 2 * r * (r - σ) := by
        rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hvn, mul_one,
          sq_abs, hzr, ← hσdef]
        ring
      nlinarith [h1, h2, hr]
    have hmem : ⟪(r / (r - σ)) • (z - c - σ • v), v⟫_ℝ = 0 := by
      have h1 : ⟪(z - c) - σ • v, v⟫_ℝ = 0 := by
        rw [inner_sub_left]
        rw [show ⟪z - c, v⟫_ℝ = σ from hσdef.symm]
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hvn]
        ring
      rw [real_inner_smul_left, h1, mul_zero]
    have hmem' : ⟪v, (r / (r - σ)) • (z - c - σ • v)⟫_ℝ = 0 := by
      rw [real_inner_comm]
      exact hmem
    have hxW : (r / (r - σ)) • (z - c - σ • v) ∈ W := by
      refine (Submodule.mem_orthogonal _ _).mpr ?_
      intro y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [real_inner_smul_left, hmem', mul_zero]
    refine ⟨⟨(r / (r - σ)) • (z - c - σ • v), hxW⟩, ?_⟩
    have h1 : (2 * r ^ 2 / (r ^ 2 + ‖(r / (r - ⟪z - c, v⟫_ℝ)) •
          ((z - c) - ⟪z - c, v⟫_ℝ • v)‖ ^ 2)) •
          ((r / (r - ⟪z - c, v⟫_ℝ)) • ((z - c) - ⟪z - c, v⟫_ℝ • v)) +
        (r * (1 - 2 * r ^ 2 / (r ^ 2 + ‖(r / (r - ⟪z - c, v⟫_ℝ)) •
          ((z - c) - ⟪z - c, v⟫_ℝ • v)‖ ^ 2))) • v = z - c :=
      central_preimage hvn hr hzr hzσ
    rw [← hσdef] at h1
    have h2 : Φ ((r / (r - σ)) • (z - c - σ • v)) - c = z - c := by
      rw [hΦsub ⟨(r / (r - σ)) • (z - c - σ • v), hxW⟩, h1]
    have h3 := congrArg (fun w : E => w + c) h2
    simpa using h3
  -- ### step 3: the preimage of `K` in `W`
  set K' : Set ↥W := (fun x : ↥W => Φ (x : E)) ⁻¹' K with hK'def
  have hK'mem : ∀ x : ↥W, x ∈ K' ↔ Φ (x : E) ∈ K := fun x => Set.mem_preimage
  have hproj : Continuous fun x : ↥W => Φ (x : E) := hΦcont.comp continuous_subtype_val
  have hK'closed : IsClosed K' := hK.isClosed.preimage hproj
  -- a uniform distance of `K` from `p`
  obtain ⟨η, hηpos, hη⟩ : ∃ η : ℝ, 0 < η ∧ ∀ z ∈ K, η ≤ ‖z - p‖ := by
    rcases K.eq_empty_or_nonempty with h | hne
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne
        ((continuous_id.sub continuous_const).norm).continuousOn
      have hval : 0 < ‖z₀ - p‖ := by
        rw [norm_pos_iff]
        intro h0
        have h1 : z₀ = p := sub_eq_zero.mp h0
        rw [h1] at hz₀
        exact hpK hz₀
      refine ⟨‖z₀ - p‖, hval, fun z hz => ?_⟩
      have h2 : ‖z₀ - p‖ ≤ ‖z - p‖ := hmin hz
      linarith
  -- the distance from the projection centre
  have hΦdist : ∀ x : ↥W, ‖Φ (x : E) - p‖ = 2 * r ^ 2 / Real.sqrt (‖(x : E)‖ ^ 2 + r ^ 2) := by
    intro x
    have hxv : ⟪(x : E), v⟫_ℝ = 0 := by rw [real_inner_comm]; exact hWmem x
    have h1 : Φ (x : E) - (c + r • v) =
        (2 * r ^ 2 / (r ^ 2 + ‖(x : E)‖ ^ 2)) • ((x : E) - r • v) := by
      rw [hΦdef, sub_eq_iff_eq_add]
      module
    rw [← hpv, h1, norm_smul, Real.norm_of_nonneg (by positivity)]
    have h2 : ‖(x : E) - r • v‖ = Real.sqrt (‖(x : E)‖ ^ 2 + r ^ 2) := by
      have hsq : ‖(x : E) - r • v‖ ^ 2 = ‖(x : E)‖ ^ 2 + r ^ 2 := by
        rw [norm_sub_sq_real, real_inner_smul_right, hxv, mul_zero, norm_smul, Real.norm_eq_abs,
          hvn, mul_one, sq_abs]
        ring
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    rw [h2]
    have hV : Real.sqrt (‖(x : E)‖ ^ 2 + r ^ 2) ^ 2 = r ^ 2 + ‖(x : E)‖ ^ 2 := by
      rw [Real.sq_sqrt (show (0:ℝ) ≤ ‖(x : E)‖ ^ 2 + r ^ 2 by positivity), add_comm]
    have hVpos : 0 < Real.sqrt (‖(x : E)‖ ^ 2 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
    field_simp
    exact hV
  have hK'bdd : Bornology.IsBounded K' := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : ↥W)).mpr ⟨2 * r ^ 2 / η, ?_⟩
    intro x hx
    have hxK : Φ (x : E) ∈ K := (hK'mem x).mp hx
    have h1 : η ≤ 2 * r ^ 2 / Real.sqrt (‖(x : E)‖ ^ 2 + r ^ 2) := by
      rw [← hΦdist x]; exact hη _ hxK
    rw [Metric.mem_closedBall, dist_zero_right, Submodule.coe_norm]
    have hV : Real.sqrt (‖(x : E)‖ ^ 2 + r ^ 2) ^ 2 = r ^ 2 + ‖(x : E)‖ ^ 2 := by
      rw [Real.sq_sqrt (show (0:ℝ) ≤ ‖(x : E)‖ ^ 2 + r ^ 2 by positivity), add_comm]
    have hVpos : 0 < Real.sqrt (‖(x : E)‖ ^ 2 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have h3 : Real.sqrt (‖(x : E)‖ ^ 2 + r ^ 2) ≤ 2 * r ^ 2 / η := by
      rw [le_div_iff₀ hηpos, mul_comm]
      rw [le_div_iff₀ hVpos] at h1
      linarith
    have h4 : ‖(x : E)‖ ≤ Real.sqrt (‖(x : E)‖ ^ 2 + r ^ 2) := by
      have h5 : ‖(x : E)‖ ^ 2 ≤ Real.sqrt (‖(x : E)‖ ^ 2 + r ^ 2) ^ 2 := by
        nlinarith [hV, sq_nonneg r]
      nlinarith [h5, norm_nonneg (x : E), hVpos.le]
    linarith
  have hK'cpt : IsCompact K' := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hK'closed, hK'bdd⟩
  have hK'td : IsTotallyDisconnected K' := by
    intro S hSK hSpre
    have himg : IsPreconnected ((fun x : ↥W => Φ (x : E)) '' S) :=
      hSpre.image _ hproj.continuousOn
    have hsub' : (fun x : ↥W => Φ (x : E)) '' S ⊆ K := fun z ⟨s, hs, hzs⟩ => hzs ▸ hSK hs
    have hsing : ((fun x : ↥W => Φ (x : E)) '' S).Subsingleton := htd _ hsub' himg
    intro a ha b hb
    exact hΦinj a b (hsing ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
  -- ### step 4: the flat theorem in `W`
  have hflat : IsPathConnected ((K' : Set ↥W)ᶜ) :=
    compl_isCompact_isTotallyDisconnected_pathConnected_gen (E := ↥W) hrankW hK'cpt hK'td
  -- ### step 5: the image of the complement
  set S₀ : Set E := (fun x : ↥W => Φ (x : E)) '' (K'ᶜ) with hS₀def
  have hS₀pc : IsPathConnected S₀ := hflat.image hproj
  have hS₀eq : S₀ = (Metric.sphere c r \ K) \ {p} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨hΦsphere x, ?_⟩, ?_⟩
      · intro hzK
        exact hx ((hK'mem x).mpr hzK)
      · simpa using hΦnotp x
    · rintro ⟨⟨hzS, hzK⟩, hzp⟩
      have hzp' : z ≠ p := by simpa using hzp
      obtain ⟨x, hx⟩ := hΦsurj z hzS hzp'
      exact ⟨x, fun hxK => hzK (hx ▸ ((hK'mem x).mp hxK)), hx⟩
  have hsep : Metric.sphere c r \ K = S₀ ∪ {p} := by
    rw [hS₀eq]
    ext z
    constructor
    · intro hz
      by_cases hzp : z = p
      · exact Or.inr (by simpa using hzp)
      · exact Or.inl ⟨hz, by simpa using hzp⟩
    · rintro (h | h)
      · exact h.1
      · have hzp : z = p := by simpa using h
        subst hzp
        exact ⟨hpS, hpK⟩
  -- ### step 6: `p` is a limit point of `S₀`
  have hpcl : p ∈ closure S₀ := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hδK⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball p δ, z ∉ K := by
      have h2 : IsOpen (Kᶜ) := hK.isClosed.isOpen_compl
      rcases Metric.isOpen_iff.mp h2 p hpK with ⟨δ, hδpos, hδsub⟩
      exact ⟨δ, hδpos, fun z hz => hδsub hz⟩
    haveI : Nontrivial ↥W :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (M := ↥W) (by omega)
    haveI : Nontrivial ↥W :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (M := ↥W) (by omega)
    obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ↥W, w₀ ≠ 0 := exists_ne 0
    have hw₀n : 0 < ‖(w₀ : E)‖ := norm_pos_iff.mpr (by simpa using hw₀)
    have hmpos : 0 < min ε δ := lt_min hε hδpos
    have hLpos : 0 < 2 * r ^ 2 / min ε δ := by positivity
    have hkey : ∀ N : ℕ, (2 * r ^ 2 / min ε δ) / ‖(w₀ : E)‖ < (N : ℝ) →
        2 * r ^ 2 / Real.sqrt (‖((N : ℝ) • w₀ : ↥W)‖ ^ 2 + r ^ 2) < min ε δ := by
      intro N hN
      have h2 : 2 * r ^ 2 / min ε δ < ‖((N : ℝ) • w₀ : ↥W)‖ := by
        rw [Submodule.coe_norm, Submodule.coe_smul, norm_smul,
          Real.norm_of_nonneg (by positivity)]
        rwa [div_lt_iff₀ hw₀n] at hN
      have h3 : 2 * r ^ 2 / min ε δ < Real.sqrt (‖((N : ℝ) • w₀ : ↥W)‖ ^ 2 + r ^ 2) := by
        have h4 : (2 * r ^ 2 / min ε δ) ^ 2 < ‖((N : ℝ) • w₀ : ↥W)‖ ^ 2 + r ^ 2 := by
          nlinarith [h2, sq_nonneg r, sq_pos_of_pos hLpos]
        calc 2 * r ^ 2 / min ε δ
            = Real.sqrt ((2 * r ^ 2 / min ε δ) ^ 2) := (Real.sqrt_sq hLpos.le).symm
          _ < Real.sqrt (‖((N : ℝ) • w₀ : ↥W)‖ ^ 2 + r ^ 2) :=
              Real.sqrt_lt_sqrt (by positivity) h4
      rw [div_lt_iff₀ (Real.sqrt_pos.mpr (by positivity))]
      have hmul : 2 * r ^ 2 / min ε δ * min ε δ = 2 * r ^ 2 :=
        div_mul_cancel₀ _ (ne_of_gt hmpos)
      have h5 : 2 * r ^ 2 < min ε δ *
          Real.sqrt (‖((N : ℝ) • w₀ : ↥W)‖ ^ 2 + r ^ 2) := by
        rw [← hmul]
        calc 2 * r ^ 2 / min ε δ * min ε δ = min ε δ * (2 * r ^ 2 / min ε δ) := mul_comm _ _
          _ < min ε δ * Real.sqrt (‖((N : ℝ) • w₀ : ↥W)‖ ^ 2 + r ^ 2) :=
              mul_lt_mul_of_pos_left h3 hmpos
      linarith [h5]
    obtain ⟨N, hN⟩ := exists_nat_gt ((2 * r ^ 2 / min ε δ) / ‖(w₀ : E)‖)
    refine ⟨Φ ((N : ℝ) • w₀ : ↥W), ?_, ?_⟩
    · rw [hS₀eq]
      refine ⟨⟨hΦsphere _, ?_⟩, ?_⟩
      · intro hzK
        refine hδK _ ?_ hzK
        rw [Metric.mem_ball, dist_eq_norm, hΦdist]
        exact lt_of_lt_of_le (hkey N hN) (min_le_right _ _)
      · intro hmem
        refine hΦnotp ((N : ℝ) • w₀) ?_
        simpa [Set.mem_singleton_iff] using hmem
    · rw [dist_comm, dist_eq_norm, hΦdist]
      exact lt_of_lt_of_le (hkey N hN) (min_le_left _ _)
  -- ### step 7: conclusion
  rw [hsep, Set.union_singleton]
  exact isPreconnected_insert_of_mem_closure hS₀pc.isConnected.isPreconnected hpcl

end Work.Whitney.PathTools
