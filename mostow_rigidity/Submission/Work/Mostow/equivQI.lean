import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.geoSpec
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.finite_nearStab_compact
import Submission.Work.Mostow.finite_translates_inter_compact
import Submission.Work.Mostow.paraUniqueFixed
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.horoSpec
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.flatActCocompact
import Submission.Work.Mostow.flatActProper
import Submission.Work.Mostow.thickMap
import Submission.Work.Mostow.cuspMap
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.cuspCorr
import Submission.Work.Mostow.cuspOrbitsFinite
import Submission.Work.Mostow.hrayOutsideHoroballs
import Submission.Work.Mostow.horosphereLevOneNet
import Submission.Work.Mostow.flatOrbitMap
import Submission.Work.Mostow.cuspPsiSpecShift
import Submission.Work.Mostow.reverseOfLocal
import Submission.Work.Mostow.orbitReverse
import Submission.Work.Mostow.cuspReverse

/-!
# Area C3 — `QIProp n`

Assembly of the coarsely equivariant quasi-isometry between the spaces of two lattices.

The construction (see `REFS/lead-design/equivQI.md`) is:

* on the *thick part* of `Γ` (the complement of the horoball neighbourhoods of the cusps, which is
  `Γ`-cocompact by `GeomFiniteProp`) use the orbit map `u ↦ f(γ_u) • 0`, where `γ_u` is any element
  with `γ_u⁻¹ • u` in a fixed compact fundamental set;
* on the *deep cusps* use the cusp map, built from the flat (horospherical) metrics and the flat
  orbit map `ψ_ξ` of `flatMapSpec`;
* `IsQI` then follows from the local bound (`hdist ≤ 1 ⇒ hdist (Φ u) (Φ v) ≤ C`) together with the
  subdivision of geodesics (`geoSpec`), and coarse surjectivity.

This file assembles those pieces; the individual chapters live in the modules imported above.
-/

set_option maxHeartbeats 1000000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-! ## Elementary metric facts -/

theorem hd_nonneg (hI : HypIsoData n) (u v : E n) : 0 ≤ hdist u v := hI.nonneg u v
theorem hd_symm (hI : HypIsoData n) (u v : E n) : hdist u v = hdist v u := hI.symm u v
theorem hd_eq_zero_iff (hI : HypIsoData n) (u v : E n) : hdist u v = 0 ↔ u = v := hI.eq_zero u v
theorem hd_triangle (hI : HypIsoData n) (u v w : E n) : hdist u w ≤ hdist u v + hdist v w :=
  hI.triangle u v w
theorem hd_smul (hI : HypIsoData n) (g : PO n 1) (u v : E n) : hdist (g • u) (g • v) = hdist u v :=
  hI.isom_smul g u v

/-- A chain of unit steps from `u` to `v`, when `hdist u v ≤ N`. -/
theorem exists_chain (hI : HypIsoData n) (u v : E n) {N : ℕ} (hNpos : 0 < N)
    (hN : hdist u v ≤ (N : ℝ)) :
    ∃ x : ℕ → E n, x 0 = u ∧ x N = v ∧ ∀ i < N, hdist (x i) (x (i + 1)) ≤ 1 := by
  rcases eq_or_ne u v with rfl | huv
  · refine ⟨fun _ => u, rfl, rfl, fun i _ => ?_⟩
    change hdist u u ≤ 1
    rw [(hd_eq_zero_iff hI u u).2 rfl]
    norm_num
  · have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
    refine ⟨fun i => geo u v ((i : ℝ) / (N : ℝ)), ?_, ?_, ?_⟩
    · change geo u v (((0 : ℕ) : ℝ) / (N : ℝ)) = u
      rw [Nat.cast_zero, zero_div]
      exact geo_zero_of_ne huv
    · change geo u v (((N : ℕ) : ℝ) / (N : ℝ)) = v
      rw [div_self (ne_of_gt hNposR)]
      exact geo_one_of_ne huv
    · intro i hi
      have hiN : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_lt hi
      have h1N : ((i + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
      have hs : (i : ℝ) / N ∈ Set.Icc (0:ℝ) 1 :=
        ⟨by positivity, (div_le_one hNposR).2 hiN⟩
      have ht : (((i + 1 : ℕ) : ℝ)) / N ∈ Set.Icc (0:ℝ) 1 :=
        ⟨by positivity, (div_le_one hNposR).2 h1N⟩
      rw [hdist_geo_of_ne huv hs ht]
      have hsub : (i : ℝ) / N - ((i + 1 : ℕ) : ℝ) / N = -(1 / (N : ℝ)) := by
        rw [← sub_div, show ((i : ℝ) - ((i + 1 : ℕ) : ℝ)) = -1 by push_cast; ring]
        ring
      rw [hsub, abs_neg, abs_of_pos (by positivity), one_div, inv_mul_le_iff₀ hNposR]
      simpa using hN

/-- The local bound implies the global coarse Lipschitz bound. -/
theorem hdist_map_le (hI : HypIsoData n) {Φ : E n → E n} {a : ℝ} (ha : 0 ≤ a)
    (hloc : ∀ u v : E n, hdist u v ≤ 1 → hdist (Φ u) (Φ v) ≤ a) (u v : E n) :
    hdist (Φ u) (Φ v) ≤ a * hdist u v + a := by
  by_cases huv : u = v
  · subst huv
    have h0 : hdist u u = 0 := (hd_eq_zero_iff hI u u).2 rfl
    rw [h0, mul_zero, zero_add]
    exact le_trans (le_of_eq ((hd_eq_zero_iff hI (Φ u) (Φ u)).2 rfl)) ha
  · have hne : hdist u v ≠ 0 := fun h => huv ((hd_eq_zero_iff hI u v).1 h)
    have hRpos : 0 < hdist u v := lt_of_le_of_ne (hd_nonneg hI u v) (Ne.symm hne)
    set N : ℕ := Nat.ceil (hdist u v) with hN
    have hNpos : 0 < N := by rw [hN]; exact Nat.ceil_pos.2 hRpos
    obtain ⟨x, hx0, hxN, hstep⟩ :=
      exists_chain hI u v hNpos (by rw [hN]; exact Nat.le_ceil _)
    have key : ∀ k, k ≤ N → hdist (Φ u) (Φ (x k)) ≤ (k : ℝ) * a := by
      intro k
      induction k with
      | zero => intro _; rw [hx0, (hd_eq_zero_iff hI (Φ u) (Φ u)).2 rfl]; simp
      | succ k ih =>
        intro hle
        have hkN : k ≤ N := Nat.le_of_succ_le hle
        calc hdist (Φ u) (Φ (x (k + 1)))
            ≤ hdist (Φ u) (Φ (x k)) + hdist (Φ (x k)) (Φ (x (k + 1))) := hd_triangle hI _ _ _
          _ ≤ (k : ℝ) * a + a :=
              add_le_add (ih hkN) (hloc _ _ (hstep k (Nat.lt_of_succ_le hle)))
          _ = ((k + 1 : ℕ) : ℝ) * a := by push_cast; ring
    have hsum : hdist (Φ u) (Φ v) ≤ (N : ℝ) * a := by
      have := key N le_rfl
      rwa [hxN] at this
    have hceil : (N : ℝ) ≤ hdist u v + 1 := by
      rw [hN]
      have h1 : ((Nat.ceil (hdist u v) : ℕ) : ℝ) < hdist u v + 1 := by
        exact_mod_cast Nat.ceil_lt_add_one (le_of_lt hRpos)
      linarith
    calc hdist (Φ u) (Φ v) ≤ (N : ℝ) * a := hsum
      _ ≤ (hdist u v + 1) * a := by gcongr
      _ = a * hdist u v + a := by ring


/-! ## The Busemann level along the ray, and level preservation of cusp stabilisers -/

theorem busemann_ray {ξ : E n} (hξ : ξ ∈ Sph n) (s : ℝ) :
    busemann ξ (s • ξ) = Real.log (Real.sqrt (1 + s ^ 2) - s) := by
  have h1 : ‖ξ‖ = 1 := by simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have h2 : inner ℝ (s • ξ) ξ = s := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, h1]; ring
  have h3 : ‖s • ξ‖ ^ 2 = s ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, h1, sq_abs]
    ring
  simp only [busemann, tpart, h2, h3]

theorem busemann_ray_surj {ξ : E n} (hξ : ξ ∈ Sph n) (v : ℝ) :
    ∃ s : ℝ, busemann ξ (s • ξ) = v := by
  refine ⟨-Real.sinh v, ?_⟩
  rw [busemann_ray hξ, neg_sq]
  have h1 : Real.sqrt (1 + Real.sinh v ^ 2) = Real.cosh v := by
    have : 1 + Real.sinh v ^ 2 = Real.cosh v ^ 2 := by rw [Real.cosh_sq]; ring
    rw [this, Real.sqrt_sq (Real.cosh_pos v).le]
  rw [h1, sub_neg_eq_add, Real.cosh_add_sinh, Real.log_exp]

/-- The Busemann function `β_ξ` is invariant under every element of `Γ` fixing `ξ`, as soon as the
chosen horoball family is `Γ`-invariant (the relevant clause of `GeomFiniteProp`). -/
theorem cuspStab_busemann (hI : HypIsoData n) {Γ : Subgroup (PO n 1)} {P : Set (E n)}
    {ht : E n → ℝ}
    (hinv : ∀ (γ : Γ) (ξ : E n), ξ ∈ P → ∀ u : E n,
      (γ : PO n 1) • u ∈ horoball (bd (γ : PO n 1) ξ) (ht (bd (γ : PO n 1) ξ)) ↔ u ∈ horoball ξ (ht ξ))
    {ξ : E n} (hξS : ξ ∈ Sph n) (hξP : ξ ∈ P) (γ : Γ) (hγ : bd (γ : PO n 1) ξ = ξ) :
    ∀ u : E n, busemann ξ ((γ : PO n 1) • u) = busemann ξ u := by
  set c : ℝ := busemann ξ ((γ : PO n 1) • (0 : E n)) with hc
  have hcocy : ∀ u : E n, busemann ξ ((γ : PO n 1) • u) = busemann ξ u + c := by
    intro u
    have h := hI.busemann_cocycle (γ : PO n 1) ξ u hξS
    rw [hγ] at h
    rw [h, hc]
  have hmem : ∀ u : E n, (γ : PO n 1) • u ∈ horoball ξ (ht ξ) ↔ u ∈ horoball ξ (ht ξ) := by
    intro u
    have h := hinv γ ξ hξP u
    rwa [hγ] at h
  have hc0 : c = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- c < 0 : points far above the horosphere are pulled inside it
      obtain ⟨s, hs⟩ := busemann_ray_surj hξS (ht ξ - c / 2)
      have hval : busemann ξ (s • ξ) = ht ξ - c / 2 := hs
      have hout : (s • ξ) ∉ horoball ξ (ht ξ) := by
        simp only [horoball, Set.mem_setOf_eq, not_lt]
        rw [hval]; linarith
      have hin : (γ : PO n 1) • (s • ξ) ∈ horoball ξ (ht ξ) := by
        simp only [horoball, Set.mem_setOf_eq]
        rw [hcocy (s • ξ), hval]
        linarith
      exact hout ((hmem (s • ξ)).1 hin)
    · -- c > 0 : points just below the horosphere are pushed outside it
      obtain ⟨s, hs⟩ := busemann_ray_surj hξS (ht ξ - c / 2)
      have hval : busemann ξ (s • ξ) = ht ξ - c / 2 := hs
      have hin : (s • ξ) ∈ horoball ξ (ht ξ) := by
        simp only [horoball, Set.mem_setOf_eq]
        rw [hval]; linarith
      have hout : (γ : PO n 1) • (s • ξ) ∉ horoball ξ (ht ξ) := by
        simp only [horoball, Set.mem_setOf_eq, not_lt]
        rw [hcocy (s • ξ), hval]
        linarith
      exact hout ((hmem (s • ξ)).2 hin)
  intro u
  rw [hcocy u, hc0, add_zero]

/-- Hyperbolic distance to the origin is controlled by the Euclidean norm. -/
theorem hdist_zero_le_of_norm_le (hI : HypIsoData n) {u : E n} {R : ℝ} (h : ‖u‖ ≤ R) :
    hdist (0 : E n) u ≤ Real.arcosh (Real.sqrt (1 + R ^ 2)) := by
  have hu : hdist (0 : E n) u = Real.arcosh (tpart u) := by
    rw [hdist, tpart, tpart]; simp
  rw [hu]
  rw [Real.arcosh_le_arcosh (tpart_pos u) (by positivity)]
  rw [tpart]
  exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg u])

/-- A compact set is bounded in hyperbolic distance from the origin. -/
theorem exists_hdist_le_of_isCompact_bundled (hI : HypIsoData n) {K : Set (E n)}
    (hK : IsCompact K) : ∃ M : ℝ, ∀ u ∈ K, hdist (0 : E n) u ≤ M := by
  obtain ⟨R, hR⟩ := exists_norm_le_of_isCompact hK
  exact ⟨Real.arcosh (Real.sqrt (1 + R ^ 2)), fun u hu => hdist_zero_le_of_norm_le hI (hR u hu)⟩

/-- The orbit map of a `Γ`-cocompact part: there are addresses `γ_u` with `γ_u⁻¹ • u ∈ K`, and the
ambiguity between the addresses of two points at distance `≤ 1` is a fixed finite set. -/
theorem thickOrbit (hA : POBasic n) (hI : HypIsoData n) {Γ : Subgroup (PO n 1)}
    (hdisc : IsDiscrete (SetLike.coe Γ)) {K : Set (E n)} (hK : IsCompact K)
    (hcpt : ∀ u : E n, ∃ γ : Γ, (γ : PO n 1) • u ∈ K) :
    ∃ (γof : E n → Γ) (S : Finset Γ),
      (∀ u : E n, (((γof u)⁻¹ : Γ) : PO n 1) • u ∈ K) ∧
      (∀ u v : E n, hdist u v ≤ 1 → (γof u)⁻¹ * (γof v) ∈ S) := by
  choose γ₀ hγ₀ using hcpt
  obtain ⟨M, hM⟩ := exists_hdist_le_of_isCompact_bundled hI hK
  set K₂ : Set (E n) := {x | hdist (0 : E n) x ≤ M + 1} with hK₂
  have hK₂c : IsCompact K₂ := hI.ball_compact 0 (M + 1)
  have hfin := finite_nearStab_compact hA hI hdisc hK hK₂c
  refine ⟨fun u => (γ₀ u)⁻¹, hfin.toFinset, ?_, ?_⟩
  · intro u
    simpa using hγ₀ u
  · intro u v huv
    rw [Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq, inv_inv]
    refine ⟨((γ₀ v : Γ) : PO n 1) • v, ?_, ((γ₀ u : Γ) : PO n 1) • v, ?_, ?_⟩
    · simpa using hγ₀ v
    · simp only [hK₂, Set.mem_setOf_eq]
      have h3 := hd_triangle hI (0 : E n) (((γ₀ u : Γ) : PO n 1) • u) (((γ₀ u : Γ) : PO n 1) • v)
      have h2 : hdist (((γ₀ u : Γ) : PO n 1) • u) (((γ₀ u : Γ) : PO n 1) • v) = hdist u v :=
        hI.isom_smul _ _ _
      have h1 : hdist (0 : E n) (((γ₀ u : Γ) : PO n 1) • u) ≤ M := hM _ (hγ₀ u)
      rw [h2] at h3
      linarith
    · show ((((γ₀ u) * (γ₀ v)⁻¹ : Γ)) : PO n 1) • (((γ₀ v : Γ) : PO n 1) • v)
        = ((γ₀ u : Γ) : PO n 1) • v
      have hBB : ((((γ₀ v : Γ) : PO n 1))⁻¹) • (((γ₀ v : Γ) : PO n 1) • v) = v := by
        rw [← hA.mul_smul, inv_mul_cancel, hA.one_smul]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hA.mul_smul, hBB]


/-! ## Helper identities for the `Γ`-action and for `max`/`abs` -/

section Helpers

variable {Γ Λ : Subgroup (PO n 1)}

theorem real_le_max_left (a b : ℝ) : a ≤ max a b := le_max_left a b
theorem real_le_max_right (a b : ℝ) : b ≤ max a b := le_max_right a b

theorem subgroup_mul_smul (hA : POBasic n) (a b : Γ) (u : E n) :
    ((a * b : Γ) : PO n 1) • u = (a : PO n 1) • ((b : PO n 1) • u) := by
  rw [Subgroup.coe_mul, hA.mul_smul]

theorem subgroup_inv_smul (hA : POBasic n) (a : Γ) (u : E n) :
    ((a⁻¹ : Γ) : PO n 1) • ((a : PO n 1) • u) = u := by
  rw [Subgroup.coe_inv, ← hA.mul_smul, inv_mul_cancel, hA.one_smul]

theorem subgroup_inv_smul' (hA : POBasic n) (a : Γ) (u : E n) :
    (a : PO n 1) • (((a⁻¹ : Γ)) : PO n 1) • u = u := by
  rw [Subgroup.coe_inv, ← hA.mul_smul, mul_inv_cancel, hA.one_smul]

theorem smul_inv_smul_cancel (hA : POBasic n) (a : PO n 1) (u : E n) :
    a⁻¹ • (a • u) = u := by rw [← hA.mul_smul, inv_mul_cancel, hA.one_smul]

theorem smul_smul_inv_cancel (hA : POBasic n) (a : PO n 1) (u : E n) :
    a • (a⁻¹ • u) = u := by rw [← hA.mul_smul, mul_inv_cancel, hA.one_smul]

/-- The cancellation behind the equivariance membership of `thickOrbitR`. -/
theorem subgroup_smul_conj_aux (hA : POBasic n) {Γ : Subgroup (PO n 1)}
    (γ d b : Γ) (u : E n) :
    ((((γ * d)⁻¹ * b : Γ)) : PO n 1) • ((((b⁻¹ : Γ)) : PO n 1) • ((γ : PO n 1) • u))
      = (((d⁻¹ : Γ)) : PO n 1) • u := by
  have hb : ((((γ * d)⁻¹ * b : Γ)) : PO n 1)
      = (((γ : PO n 1) * (d : PO n 1))⁻¹) * (b : PO n 1) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul]
  rw [hb, hA.mul_smul,
    show ((b : PO n 1) • ((((b⁻¹ : Γ)) : PO n 1) • ((γ : PO n 1) • u))) = ((γ : PO n 1) • u)
      from subgroup_inv_smul' hA b ((γ : PO n 1) • u),
    mul_inv_rev, hA.mul_smul,
    show (((γ : PO n 1))⁻¹ • (((γ : PO n 1)) • u)) = u
      from smul_inv_smul_cancel hA (γ : PO n 1) u,
    Subgroup.coe_inv]

theorem subgroup_coe_inv_inv (a : Γ) :
    ((((a⁻¹)⁻¹ : Γ)) : PO n 1) = ((a : Γ) : PO n 1) := by
  rw [Subgroup.coe_inv, Subgroup.coe_inv, inv_inv]

theorem subgroup_coe_mul_inv (a : Γ) :
    (a : PO n 1) * (((a⁻¹ : Γ)) : PO n 1) = 1 := by
  rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]

end Helpers

variable {Γ Λ : Subgroup (PO n 1)}

/-! ## Generalized orbit addresses and the thick orbit map -/

/-- Orbit addresses at scale `N`: as `thickOrbit`, but the ambiguity set is finite for pairs at
`hdist ≤ N` rather than `hdist ≤ 1`, and symmetric. -/
theorem thickOrbitR (hA : POBasic n) (hI : HypIsoData n) {Γ : Subgroup (PO n 1)}
    (hdisc : IsDiscrete (SetLike.coe Γ)) {K : Set (E n)} (hK : IsCompact K)
    (hcpt : ∀ u : E n, ∃ γ : Γ, (γ : PO n 1) • u ∈ K) {N : ℝ} (hN : 0 ≤ N) :
    ∃ (γof : E n → Γ) (S : Finset Γ),
      (∀ u : E n, (((γof u)⁻¹ : Γ) : PO n 1) • u ∈ K) ∧
      (∀ u v : E n, hdist u v ≤ N → (γof u)⁻¹ * (γof v) ∈ S) ∧
      (∀ u v : E n, hdist u v ≤ N → (γof v)⁻¹ * (γof u) ∈ S) := by
  choose γ₀ hγ₀ using hcpt
  obtain ⟨M, hM⟩ := exists_hdist_le_of_isCompact_bundled hI hK
  set K₂ : Set (E n) := {x | hdist (0 : E n) x ≤ M + N} with hK₂
  have hK₂c : IsCompact K₂ := hI.ball_compact 0 (M + N)
  have hKsub : K ⊆ K₂ := fun x hx => by
    simp only [hK₂, Set.mem_setOf_eq]
    have h1 := hM x hx
    linarith
  have hfin := finite_nearStab_compact hA hI hdisc hK₂c hK₂c
  refine ⟨fun u => (γ₀ u)⁻¹, hfin.toFinset, ?_, ?_, ?_⟩
  · intro u
    simpa using hγ₀ u
  · intro u v huv
    rw [Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq]
    refine ⟨((γ₀ v : Γ) : PO n 1) • v, hKsub (hγ₀ v), ((γ₀ u : Γ) : PO n 1) • v, ?_, ?_⟩
    · simp only [hK₂, Set.mem_setOf_eq]
      have h3 := hd_triangle hI (0 : E n) (((γ₀ u : Γ) : PO n 1) • u)
        (((γ₀ u : Γ) : PO n 1) • v)
      have h2 : hdist (((γ₀ u : Γ) : PO n 1) • u) (((γ₀ u : Γ) : PO n 1) • v) = hdist u v :=
        hI.isom_smul _ _ _
      have h1 : hdist (0 : E n) (((γ₀ u : Γ) : PO n 1) • u) ≤ M := hM _ (hγ₀ u)
      rw [h2] at h3
      linarith
    · rw [subgroup_mul_smul hA, subgroup_inv_smul hA (γ₀ v) v]
      congr 1
      exact subgroup_coe_inv_inv (γ₀ u)
  · intro u v huv
    rw [Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq]
    refine ⟨((γ₀ u : Γ) : PO n 1) • u, hKsub (hγ₀ u), ((γ₀ v : Γ) : PO n 1) • u, ?_, ?_⟩
    · simp only [hK₂, Set.mem_setOf_eq]
      have h3 := hd_triangle hI (0 : E n) (((γ₀ v : Γ) : PO n 1) • v)
        (((γ₀ v : Γ) : PO n 1) • u)
      have h2 : hdist (((γ₀ v : Γ) : PO n 1) • v) (((γ₀ v : Γ) : PO n 1) • u) = hdist u v := by
        rw [hI.isom_smul, hd_symm hI u v]
      have h1 : hdist (0 : E n) (((γ₀ v : Γ) : PO n 1) • v) ≤ M := hM _ (hγ₀ v)
      rw [h2] at h3
      linarith
    · rw [subgroup_mul_smul hA, subgroup_inv_smul hA (γ₀ u) u]
      congr 1
      exact subgroup_coe_inv_inv (γ₀ v)

/-- The orbit map of `Γ` (with addresses `γof`), transported to `Λ` through `f`, based at `0`. -/
noncomputable def thickPhi (f : Γ ≃* Λ) (γof : E n → Γ) : E n → E n :=
  fun u => (((f (γof u) : Λ)) : PO n 1) • (0 : E n)

/-- A comparison of `hdist` across `f`. -/
theorem hdist_f_smul (hA : POBasic n) (hI : HypIsoData n)
    (f : Γ ≃* Λ) (p q : Γ) (k : E n) :
    hdist (((f p : Λ) : PO n 1) • (0 : E n)) (((f q : Λ) : PO n 1) • k)
      = hdist (((f (q⁻¹ * p) : Λ) : PO n 1) • (0 : E n)) k := by
  have hcoe : (((f q : Λ) : PO n 1))⁻¹ * ((f p : Λ) : PO n 1)
      = ((f (q⁻¹ * p) : Λ) : PO n 1) := by
    have h2 : ((f q : Λ))⁻¹ * (f p : Λ) = f (q⁻¹ * p) := by
      rw [← map_inv, ← map_mul]
    calc (((f q : Λ) : PO n 1))⁻¹ * ((f p : Λ) : PO n 1)
        = (((((f q : Λ))⁻¹ * (f p : Λ) : Λ)) : PO n 1) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv]
      _ = ((f (q⁻¹ * p) : Λ) : PO n 1) := by rw [h2]
  have hmain : (((f q : Λ) : PO n 1))⁻¹ • (((f p : Λ) : PO n 1) • (0 : E n))
      = ((f (q⁻¹ * p) : Λ) : PO n 1) • (0 : E n) := by
    calc (((f q : Λ) : PO n 1))⁻¹ • (((f p : Λ) : PO n 1) • (0 : E n))
        = ((((f q : Λ) : PO n 1))⁻¹ * ((f p : Λ) : PO n 1)) • (0 : E n) := by
          rw [hA.mul_smul]
      _ = ((f (q⁻¹ * p) : Λ) : PO n 1) • (0 : E n) := by rw [hcoe]
  have hk : (((f q : Λ) : PO n 1))⁻¹ • (((f q : Λ) : PO n 1) • k) = k := by
    rw [← hA.mul_smul, inv_mul_cancel, hA.one_smul]
  have hiso := hI.isom_smul (((f q : Λ) : PO n 1))⁻¹
    ((((f p : Λ) : PO n 1)) • (0 : E n)) ((((f q : Λ) : PO n 1)) • k)
  rw [hmain, hk] at hiso
  exact hiso.symm

/-- The local bound for the thick orbit map, in terms of the ambiguity set. -/
theorem hdist_thickPhi_le (hA : POBasic n) (hI : HypIsoData n)
    (f : Γ ≃* Λ) (γof : E n → Γ) (S : Finset Γ) (C : ℝ)
    (hS : ∀ u v : E n, hdist u v ≤ 1 → (γof v)⁻¹ * (γof u) ∈ S)
    (hC : ∀ s : Γ, s ∈ S → hdist (0 : E n) (((f s : Λ) : PO n 1) • (0 : E n)) ≤ C)
    {u v : E n} (huv : hdist u v ≤ 1) :
    hdist (thickPhi f γof u) (thickPhi f γof v) ≤ C := by
  have he : hdist (thickPhi f γof u) (thickPhi f γof v)
      = hdist (0 : E n) (((f ((γof v)⁻¹ * (γof u)) : Λ) : PO n 1) • (0 : E n)) := by
    show hdist (((f (γof u) : Λ) : PO n 1) • (0 : E n))
          (((f (γof v) : Λ) : PO n 1) • (0 : E n)) = _
    exact hdist_f_mul hA hI f (γof u) (γof v)
  rw [he]
  exact hC _ (hS u v huv)

/-- The equivariance bound for the thick orbit map. -/
theorem hdist_thickPhi_equiv (hA : POBasic n) (hI : HypIsoData n)
    (f : Γ ≃* Λ) (γof : E n → Γ) (T : Finset Γ) (C : ℝ)
    (hT : ∀ (γ : Γ) (u : E n), ((γ * γof u)⁻¹ * γof ((γ : PO n 1) • u)) ∈ T)
    (hC : ∀ s : Γ, s ∈ T → hdist (0 : E n) (((f s : Λ) : PO n 1) • (0 : E n)) ≤ C)
    (γ : Γ) (u : E n) :
    hdist (thickPhi f γof ((γ : PO n 1) • u)) (((f γ : Λ) : PO n 1) • thickPhi f γof u)
      ≤ C := by
  have e2 : (((f γ : Λ) : PO n 1) • thickPhi f γof u)
      = ((f (γ * γof u) : Λ) : PO n 1) • (0 : E n) := by
    show ((f γ : Λ) : PO n 1) • (((f (γof u) : Λ) : PO n 1) • (0 : E n)) = _
    rw [← hA.mul_smul]
    congr 1
    rw [← Subgroup.coe_mul, ← map_mul]
  have h2 : hdist (thickPhi f γof ((γ : PO n 1) • u))
      (((f γ : Λ) : PO n 1) • thickPhi f γof u)
      = hdist (0 : E n) (((f ((γ * γof u)⁻¹ * γof ((γ : PO n 1) • u)) : Λ) : PO n 1)
          • (0 : E n)) := by
    rw [e2]
    show hdist (((f (γof ((γ : PO n 1) • u)) : Λ) : PO n 1) • (0 : E n))
          (((f (γ * γof u) : Λ) : PO n 1) • (0 : E n)) = _
    exact hdist_f_mul hA hI f (γof ((γ : PO n 1) • u)) (γ * γof u)
  rw [h2]
  exact hC _ (hT γ u)

/-- The thick orbit map: addresses, scale-`1` local bound and a **uniform** equivariance constant. -/
theorem thickPhi_spec (hA : POBasic n) (hI : HypIsoData n)
    (hdisc : IsDiscrete (SetLike.coe Γ)) (f : Γ ≃* Λ)
    {K : Set (E n)} (hK : IsCompact K) (hcpt : ∀ u : E n, ∃ γ : Γ, (γ : PO n 1) • u ∈ K) :
    ∃ (γof : E n → Γ) (C : ℝ), 0 ≤ C ∧
      (∀ u : E n, (((γof u)⁻¹ : Γ) : PO n 1) • u ∈ K) ∧
      (∀ u v : E n, hdist u v ≤ 1 → hdist (thickPhi f γof u) (thickPhi f γof v) ≤ C) ∧
      (∀ γ : Γ, ∀ u : E n, hdist (thickPhi f γof ((γ : PO n 1) • u))
        (((f γ : Λ) : PO n 1) • thickPhi f γof u) ≤ C) := by
  classical
  obtain ⟨γof, S, hKmem, hS, hS'⟩ := thickOrbitR hA hI hdisc hK hcpt (N := 1) (by norm_num)
  set T : Set Γ := {s : Γ | ∃ u ∈ K, ∃ v ∈ K, (s : PO n 1) • u = v} with hT
  have hTfin : T.Finite := finite_nearStab_compact hA hI hdisc hK hK
  set F : Finset Γ := hTfin.toFinset ∪ S with hF
  have hFmem : ∀ s : Γ, s ∈ (T ∪ (S : Set Γ)) → s ∈ F := by
    intro s hs
    rcases hs with hs | hs
    · exact Finset.mem_union.mpr (Or.inl (by rw [Set.Finite.mem_toFinset]; exact hs))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_coe.mp hs))
  set C : ℝ := F.sum (fun s : Γ =>
    max (hdist (0 : E n) (((f s : Λ) : PO n 1) • (0 : E n))) 0) with hCdef
  have hCF : ∀ s ∈ F, hdist (0 : E n) (((f s : Λ) : PO n 1) • (0 : E n)) ≤ C := by
    intro s hs
    have h1 : max (hdist (0 : E n) (((f s : Λ) : PO n 1) • (0 : E n))) 0 ≤ C := by
      rw [hCdef]
      exact Finset.single_le_sum (f := fun t : Γ =>
        max (hdist (0 : E n) (((f t : Λ) : PO n 1) • (0 : E n))) 0)
        (fun t _ => real_le_max_right _ _) hs
    exact le_trans (real_le_max_left _ _) h1
  refine ⟨γof, max C 0, real_le_max_right C 0, hKmem, ?_, ?_⟩
  · intro u v huv
    exact hdist_thickPhi_le hA hI f γof S (max C 0) (fun u v huv => hS' u v huv)
      (fun s hs => le_trans (hCF s (hFmem s (Or.inr (Finset.mem_coe.mpr hs))))
        (real_le_max_left C 0)) huv
  · intro γ u
    refine hdist_thickPhi_equiv hA hI f γof F (max C 0)
      (fun γ u => hFmem _ (Or.inl ?_))
      (fun s hs => le_trans (hCF s hs) (real_le_max_left C 0)) γ u
    refine ⟨((γof ((γ : PO n 1) • u))⁻¹ : Γ) • ((γ : PO n 1) • u), hKmem _,
      ((γof u)⁻¹ : Γ) • u, hKmem u, ?_⟩
    exact subgroup_smul_conj_aux hA γ (γof u) (γof ((γ : PO n 1) • u)) u

/-- Coarse surjectivity of the thick orbit map onto the `Λ`-side cocompact part. -/
theorem thickPhi_surj (hA : POBasic n) (hI : HypIsoData n)
    (hdisc : IsDiscrete (SetLike.coe Γ)) (f : Γ ≃* Λ)
    {K : Set (E n)} (hK : IsCompact K) (hcpt : ∀ u : E n, ∃ γ : Γ, (γ : PO n 1) • u ∈ K)
    {KΛ : Set (E n)} (hKΛ : IsCompact KΛ) (hcptΛ : ∀ w : E n, ∃ m : Λ, (m : PO n 1) • w ∈ KΛ)
    (γof : E n → Γ) (hγof : ∀ u : E n, (((γof u)⁻¹ : Γ) : PO n 1) • u ∈ K) :
    ∃ C : ℝ, ∀ w : E n, (∃ m : Λ, (m : PO n 1) • w ∈ KΛ) →
      ∃ u : E n, hdist (thickPhi f γof u) w ≤ C := by
  classical
  obtain ⟨k₀, hk₀⟩ : K.Nonempty := by
    obtain ⟨γ, hγ⟩ := hcpt (0 : E n)
    exact ⟨(γ : PO n 1) • (0 : E n), hγ⟩
  set T : Set Γ := {s : Γ | ∃ u ∈ K, ∃ v ∈ K, (s : PO n 1) • u = v} with hT
  have hTfin : T.Finite := finite_nearStab_compact hA hI hdisc hK hK
  have hTinv : ∀ s : Γ, s ∈ T → s⁻¹ ∈ T := by
    rintro s ⟨x, hx, y, hy, hxy⟩
    exact ⟨y, hy, x, hx, by
      rw [← hxy, ← hA.mul_smul, Subgroup.coe_inv, inv_mul_cancel, hA.one_smul]⟩
  have hbdd : ∀ s : Γ, s ∈ T → ∃ B : ℝ, ∀ k ∈ KΛ,
      hdist (((f s : Λ) : PO n 1) • (0 : E n)) k ≤ B := by
    intro s hs
    have hcont : ContinuousOn
        (fun k : E n => hdist (((f s : Λ) : PO n 1) • (0 : E n)) k) KΛ :=
      (hI.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    obtain ⟨B, hB⟩ := hKΛ.bddAbove_image hcont
    exact ⟨B, fun k hk => hB ⟨k, hk, rfl⟩⟩
  choose B hB using hbdd
  haveI : Fintype T := hTfin.fintype
  refine ⟨max (∑ s : T, max (B s.1 s.2) 0) 0, ?_⟩
  intro w hw
  obtain ⟨m, hm⟩ := hw
  set k : E n := (m : PO n 1) • w with hkdef
  have hmk : k ∈ KΛ := hm
  set γ : Γ := f.symm m with hγdef
  have hmf : f γ = m := by rw [hγdef]; simp
  refine ⟨(γ⁻¹ : Γ) • k₀, ?_⟩
  have hsT' : ((γof ((γ⁻¹ : Γ) • k₀))⁻¹ * γ⁻¹) ∈ T := by
    refine ⟨k₀, hk₀, ((γof ((γ⁻¹ : Γ) • k₀))⁻¹ : Γ) • ((γ⁻¹ : Γ) • k₀), hγof _, ?_⟩
    show ((((γof ((γ⁻¹ : Γ) • k₀))⁻¹ * γ⁻¹) : Γ) : PO n 1) • k₀
        = (((γof ((γ⁻¹ : Γ) • k₀))⁻¹ : Γ) : PO n 1) • ((γ⁻¹ : Γ) • k₀)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hA.mul_smul, hA.one_smul,
      smul_inv_smul_cancel hA, smul_smul_inv_cancel hA, inv_mul_cancel, mul_inv_rev]
    try rfl
  have hsT : γ * γof ((γ⁻¹ : Γ) • k₀) ∈ T := by
    have h1 := hTinv _ hsT'
    simpa [mul_inv_rev] using h1
  have hb := hB (γ * γof ((γ⁻¹ : Γ) • k₀)) hsT k hmk
  have hw' : w = ((f (γ⁻¹) : Λ) : PO n 1) • k := by
    rw [hkdef, ← hA.mul_smul]
    have h1 : (((f (γ⁻¹) : Λ) : PO n 1)) * ((m : PO n 1)) = 1 := by
      rw [← hmf, ← Subgroup.coe_mul, ← map_mul, inv_mul_cancel, map_one, Subgroup.coe_one]
    rw [h1, hA.one_smul]
  have he : hdist (thickPhi f γof ((γ⁻¹ : Γ) • k₀)) w
      = hdist (((f (γ * γof ((γ⁻¹ : Γ) • k₀)) : Λ) : PO n 1) • (0 : E n)) k := by
    show hdist (((f (γof ((γ⁻¹ : Γ) • k₀)) : Λ) : PO n 1) • (0 : E n)) w = _
    rw [hw']
    have h1 := hdist_f_smul hA hI f (γof ((γ⁻¹ : Γ) • k₀)) (γ⁻¹) k
    rwa [inv_inv] at h1
  rw [he]
  have hb2 : B (γ * γof ((γ⁻¹ : Γ) • k₀)) hsT
      ≤ max (∑ s : T, max (B s.1 s.2) 0) 0 := by
    have h1 : max (B (γ * γof ((γ⁻¹ : Γ) • k₀)) hsT) 0
        ≤ ∑ s : T, max (B s.1 s.2) 0 :=
      Finset.single_le_sum (f := fun s : T => max (B s.1 s.2) 0)
        (fun s _ => real_le_max_right (B s.1 s.2) 0)
        (Finset.mem_univ (⟨γ * γof ((γ⁻¹ : Γ) • k₀), hsT⟩ : T))
    exact le_trans (real_le_max_left _ _) (le_trans h1 (real_le_max_left _ _))
  exact le_trans hb hb2


/-- Orbit addresses relative to a `Γ`-invariant set `X` (so that the collar-thickened part can
be used as the cocompact set). -/
theorem thickOrbitX (hA : POBasic n) (hI : HypIsoData n) {Γ : Subgroup (PO n 1)}
    (hdisc : IsDiscrete (SetLike.coe Γ)) {X : Set (E n)} {K : Set (E n)} (hK : IsCompact K)
    (hcpt : ∀ u : E n, u ∈ X → ∃ γ : Γ, (γ : PO n 1) • u ∈ K)
    {N : ℝ} (hN : 0 ≤ N) :
    ∃ (γof : E n → Γ) (S : Finset Γ),
      (∀ u : E n, u ∈ X → (((γof u)⁻¹ : Γ) : PO n 1) • u ∈ K) ∧
      (∀ u : E n, u ∈ X → ∀ v : E n, v ∈ X → hdist u v ≤ N → (γof u)⁻¹ * (γof v) ∈ S) ∧
      (∀ u : E n, u ∈ X → ∀ v : E n, v ∈ X → hdist u v ≤ N → (γof v)⁻¹ * (γof u) ∈ S) := by
  classical
  choose γ₀ hγ₀ using hcpt
  obtain ⟨M, hM⟩ := exists_hdist_le_of_isCompact_bundled hI hK
  set K₂ : Set (E n) := {x | hdist (0 : E n) x ≤ M + N} with hK₂
  have hK₂c : IsCompact K₂ := hI.ball_compact 0 (M + N)
  have hKsub : K ⊆ K₂ := fun x hx => by
    simp only [hK₂, Set.mem_setOf_eq]
    have h1 := hM x hx
    linarith
  have hfin := finite_nearStab_compact hA hI hdisc hK₂c hK₂c
  let γof : E n → Γ := fun u => if hu : u ∈ X then (γ₀ u hu)⁻¹ else 1
  have hγ : ∀ (u : E n) (hu : u ∈ X), γof u = (γ₀ u hu)⁻¹ := by
    intro u hu
    show (if hu : u ∈ X then (γ₀ u hu)⁻¹ else 1) = (γ₀ u hu)⁻¹
    exact dif_pos hu
  have hγ' : ∀ (u : E n) (hu : u ∈ X), (γof u)⁻¹ = γ₀ u hu := by
    intro u hu
    rw [hγ u hu, inv_inv]
  refine ⟨γof, hfin.toFinset, ?_, ?_, ?_⟩
  · intro u hu
    rw [hγ' u hu]
    simpa using hγ₀ u hu
  · intro u hu v hv huv
    rw [hγ' u hu, hγ v hv, Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq]
    refine ⟨((γ₀ v hv : Γ) : PO n 1) • v, hKsub (hγ₀ v hv),
      ((γ₀ u hu : Γ) : PO n 1) • v, ?_, ?_⟩
    · simp only [hK₂, Set.mem_setOf_eq]
      have h3 := hd_triangle hI (0 : E n) (((γ₀ u hu : Γ) : PO n 1) • u)
        (((γ₀ u hu : Γ) : PO n 1) • v)
      have h2 : hdist (((γ₀ u hu : Γ) : PO n 1) • u) (((γ₀ u hu : Γ) : PO n 1) • v)
          = hdist u v := hI.isom_smul _ _ _
      have h1 : hdist (0 : E n) (((γ₀ u hu : Γ) : PO n 1) • u) ≤ M := hM _ (hγ₀ u hu)
      rw [h2] at h3
      linarith
    · rw [subgroup_mul_smul hA, subgroup_inv_smul hA (γ₀ v hv) v]
  · intro u hu v hv huv
    rw [hγ u hu, hγ' v hv, Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq]
    refine ⟨((γ₀ u hu : Γ) : PO n 1) • u, hKsub (hγ₀ u hu),
      ((γ₀ v hv : Γ) : PO n 1) • u, ?_, ?_⟩
    · simp only [hK₂, Set.mem_setOf_eq]
      have h3 := hd_triangle hI (0 : E n) (((γ₀ v hv : Γ) : PO n 1) • v)
        (((γ₀ v hv : Γ) : PO n 1) • u)
      have h2 : hdist (((γ₀ v hv : Γ) : PO n 1) • v) (((γ₀ v hv : Γ) : PO n 1) • u)
          = hdist u v := by rw [hI.isom_smul, hd_symm hI u v]
      have h1 : hdist (0 : E n) (((γ₀ v hv : Γ) : PO n 1) • v) ≤ M := hM _ (hγ₀ v hv)
      rw [h2] at h3
      linarith
    · rw [subgroup_mul_smul hA, subgroup_inv_smul hA (γ₀ u hu) u]

/-- The thick orbit map on a `Γ`-invariant, `Γ`-cocompact set `X`. -/
theorem thickPhiX_spec (hA : POBasic n) (hI : HypIsoData n)
    (hdisc : IsDiscrete (SetLike.coe Γ)) (f : Γ ≃* Λ)
    {X : Set (E n)} (hXinv : ∀ (γ : Γ) (u : E n), u ∈ X → (γ : PO n 1) • u ∈ X)
    {K : Set (E n)} (hK : IsCompact K) (hcpt : ∀ u : E n, u ∈ X → ∃ γ : Γ, (γ : PO n 1) • u ∈ K)
    {N : ℝ} (hN : 0 ≤ N) :
    ∃ (γof : E n → Γ) (C : ℝ), 0 ≤ C ∧
      (∀ u : E n, u ∈ X → (((γof u)⁻¹ : Γ) : PO n 1) • u ∈ K) ∧
      (∀ u : E n, u ∈ X → ∀ v : E n, v ∈ X → hdist u v ≤ N →
        hdist (thickPhi f γof u) (thickPhi f γof v) ≤ C) ∧
      (∀ γ : Γ, ∀ u : E n, u ∈ X → hdist (thickPhi f γof ((γ : PO n 1) • u))
        (((f γ : Λ) : PO n 1) • thickPhi f γof u) ≤ C) := by
  classical
  obtain ⟨γof, S, hKmem, hS, hS'⟩ := thickOrbitX hA hI hdisc hK hcpt hN
  set T : Set Γ := {s : Γ | ∃ u ∈ K, ∃ v ∈ K, (s : PO n 1) • u = v} with hT
  have hTfin : T.Finite := finite_nearStab_compact hA hI hdisc hK hK
  set F : Finset Γ := hTfin.toFinset ∪ S with hF
  have hFmem : ∀ s : Γ, s ∈ (T ∪ (S : Set Γ)) → s ∈ F := by
    intro s hs
    rcases hs with hs | hs
    · exact Finset.mem_union.mpr (Or.inl (by rw [Set.Finite.mem_toFinset]; exact hs))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_coe.mp hs))
  set C : ℝ := F.sum (fun s : Γ =>
    max (hdist (0 : E n) (((f s : Λ) : PO n 1) • (0 : E n))) 0) with hCdef
  have hCF : ∀ s ∈ F, hdist (0 : E n) (((f s : Λ) : PO n 1) • (0 : E n)) ≤ C := by
    intro s hs
    have h1 : max (hdist (0 : E n) (((f s : Λ) : PO n 1) • (0 : E n))) 0 ≤ C := by
      rw [hCdef]
      exact Finset.single_le_sum (f := fun t : Γ =>
        max (hdist (0 : E n) (((f t : Λ) : PO n 1) • (0 : E n))) 0)
        (fun t _ => real_le_max_right _ _) hs
    exact le_trans (real_le_max_left _ _) h1
  refine ⟨γof, max C 0, real_le_max_right C 0, hKmem, ?_, ?_⟩
  · intro u hu v hv huv
    have hs := hS' u hu v hv huv
    have he : hdist (thickPhi f γof u) (thickPhi f γof v)
        = hdist (0 : E n) (((f ((γof v)⁻¹ * (γof u)) : Λ) : PO n 1) • (0 : E n)) := by
      show hdist (((f (γof u) : Λ) : PO n 1) • (0 : E n))
            (((f (γof v) : Λ) : PO n 1) • (0 : E n)) = _
      exact hdist_f_mul hA hI f (γof u) (γof v)
    rw [he]
    exact le_trans (hCF _ (hFmem _ (Or.inr (Finset.mem_coe.mpr hs)))) (real_le_max_left C 0)
  · intro γ u hu
    have hT : ((γ * γof u)⁻¹ * γof ((γ : PO n 1) • u)) ∈ F :=
      hFmem _ (Or.inl ⟨((γof ((γ : PO n 1) • u))⁻¹ : Γ) • ((γ : PO n 1) • u),
        hKmem _ (hXinv γ u hu), ((γof u)⁻¹ : Γ) • u, hKmem u hu,
        subgroup_smul_conj_aux hA γ (γof u) (γof ((γ : PO n 1) • u)) u⟩)
    have h2 : hdist (thickPhi f γof ((γ : PO n 1) • u))
        (((f γ : Λ) : PO n 1) • thickPhi f γof u)
        = hdist (0 : E n) (((f ((γ * γof u)⁻¹ * γof ((γ : PO n 1) • u)) : Λ) : PO n 1)
            • (0 : E n)) := by
      have e2 : (((f γ : Λ) : PO n 1) • thickPhi f γof u)
          = ((f (γ * γof u) : Λ) : PO n 1) • (0 : E n) := by
        show ((f γ : Λ) : PO n 1) • (((f (γof u) : Λ) : PO n 1) • (0 : E n)) = _
        rw [← hA.mul_smul]
        congr 1
        rw [← Subgroup.coe_mul, ← map_mul]
      rw [e2]
      show hdist (((f (γof ((γ : PO n 1) • u)) : Λ) : PO n 1) • (0 : E n))
            (((f (γ * γof u) : Λ) : PO n 1) • (0 : E n)) = _
      exact hdist_f_mul hA hI f (γof ((γ : PO n 1) • u)) (γ * γof u)
    rw [h2]
    exact le_trans (hCF _ hT) (real_le_max_left C 0)

/-- Coarse surjectivity of the thick orbit map onto a `Λ`-side cocompact part. -/
theorem thickPhiX_surj (hA : POBasic n) (hI : HypIsoData n)
    (hdisc : IsDiscrete (SetLike.coe Γ)) (f : Γ ≃* Λ)
    {X : Set (E n)} (hXinv : ∀ (γ : Γ) (u : E n), u ∈ X → (γ : PO n 1) • u ∈ X)
    {K : Set (E n)} (hK : IsCompact K)
    (hcpt : ∀ u : E n, u ∈ X → ∃ γ : Γ, (γ : PO n 1) • u ∈ K)
    {KΛ : Set (E n)} (hKΛ : IsCompact KΛ)
    (γof : E n → Γ) (hγof : ∀ u : E n, u ∈ X → (((γof u)⁻¹ : Γ) : PO n 1) • u ∈ K)
    {XΛ : Set (E n)} (hXΛ : ∀ w : E n, w ∈ XΛ → ∃ m : Λ, (m : PO n 1) • w ∈ KΛ)
    {k₁ : E n} (hk₁K : k₁ ∈ K) (hk₁X : k₁ ∈ X) :
    ∃ C : ℝ, ∀ w : E n, w ∈ XΛ →
      ∃ u : E n, u ∈ X ∧ hdist (thickPhi f γof u) w ≤ C := by
  classical
  set T : Set Γ := {s : Γ | ∃ a ∈ K, ∃ b ∈ K, (s : PO n 1) • a = b} with hT
  have hTfin : T.Finite := finite_nearStab_compact hA hI hdisc hK hK
  have hTinv : ∀ s : Γ, s ∈ T → s⁻¹ ∈ T := by
    rintro s ⟨x, hx, y, hy, hxy⟩
    exact ⟨y, hy, x, hx, by
      rw [← hxy, ← hA.mul_smul, Subgroup.coe_inv, inv_mul_cancel, hA.one_smul]⟩
  have hbdd : ∀ s : Γ, s ∈ T → ∃ B : ℝ, ∀ k ∈ KΛ,
      hdist (((f s : Λ) : PO n 1) • (0 : E n)) k ≤ B := by
    intro s hs
    have hcont : ContinuousOn
        (fun k : E n => hdist (((f s : Λ) : PO n 1) • (0 : E n)) k) KΛ :=
      (hI.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    obtain ⟨B, hB⟩ := hKΛ.bddAbove_image hcont
    exact ⟨B, fun k hk => hB ⟨k, hk, rfl⟩⟩
  choose B hB using hbdd
  haveI : Fintype T := hTfin.fintype
  refine ⟨max (∑ s : T, max (B s.1 s.2) 0) 0, ?_⟩
  intro w hw
  obtain ⟨m, hm⟩ := hXΛ w hw
  set k : E n := (m : PO n 1) • w with hkdef
  have hmk : k ∈ KΛ := hm
  set γ : Γ := f.symm m with hγdef
  have hmf : f γ = m := by rw [hγdef]; simp
  refine ⟨(γ⁻¹ : Γ) • k₁, ?_, ?_⟩
  · exact hXinv γ⁻¹ k₁ hk₁X
  · have hsT' : ((γof ((γ⁻¹ : Γ) • k₁))⁻¹ * γ⁻¹) ∈ T := by
      refine ⟨k₁, hk₁K, ((γof ((γ⁻¹ : Γ) • k₁))⁻¹ : Γ) • ((γ⁻¹ : Γ) • k₁),
        hγof _ ?_, ?_⟩
      · exact hXinv γ⁻¹ k₁ hk₁X
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv, hA.mul_smul, hA.one_smul,
          smul_inv_smul_cancel hA, smul_smul_inv_cancel hA, inv_mul_cancel, mul_inv_rev]
        try rfl
    have hsT : γ * γof ((γ⁻¹ : Γ) • k₁) ∈ T := by
      have h1 := hTinv _ hsT'
      simpa [mul_inv_rev] using h1
    have hb := hB (γ * γof ((γ⁻¹ : Γ) • k₁)) hsT k hmk
    have hw' : w = ((f (γ⁻¹) : Λ) : PO n 1) • k := by
      rw [hkdef, ← hA.mul_smul]
      have h1 : (((f (γ⁻¹) : Λ) : PO n 1)) * ((m : PO n 1)) = 1 := by
        rw [← hmf, ← Subgroup.coe_mul, ← map_mul, inv_mul_cancel, map_one, Subgroup.coe_one]
      rw [h1, hA.one_smul]
    have he : hdist (thickPhi f γof ((γ⁻¹ : Γ) • k₁)) w
        = hdist (((f (γ * γof ((γ⁻¹ : Γ) • k₁)) : Λ) : PO n 1) • (0 : E n)) k := by
      show hdist (((f (γof ((γ⁻¹ : Γ) • k₁)) : Λ) : PO n 1) • (0 : E n)) w = _
      rw [hw']
      have h1 := hdist_f_smul hA hI f (γof ((γ⁻¹ : Γ) • k₁)) (γ⁻¹) k
      rwa [inv_inv] at h1
    rw [he]
    have hb2 : B (γ * γof ((γ⁻¹ : Γ) • k₁)) hsT
        ≤ max (∑ s : T, max (B s.1 s.2) 0) 0 := by
      have h1 : max (B (γ * γof ((γ⁻¹ : Γ) • k₁)) hsT) 0
          ≤ ∑ s : T, max (B s.1 s.2) 0 :=
        Finset.single_le_sum (f := fun s : T => max (B s.1 s.2) 0)
          (fun s _ => real_le_max_right (B s.1 s.2) 0)
          (Finset.mem_univ (⟨γ * γof ((γ⁻¹ : Γ) • k₁), hsT⟩ : T))
      exact le_trans (real_le_max_left _ _) (le_trans h1 (real_le_max_left _ _))
    exact le_trans hb hb2

/-! ## The collar around the cusps is cocompact -/

/-- The point of the horosphere of level `D` on the ray through `u` towards `ξ`. -/
theorem hdist_hptOf_foot (hI : HypIsoData n) {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) {D : ℝ}
    (hD : 0 < D) (hle : lev ξ u ≤ D) :
    hdist u (hptOf ξ (yc ξ u) D) = Real.log D - Real.log (lev ξ u) := by
  have hpos : 0 < lev ξ u := lev_pos ξ hξ u
  have hyc : inner ℝ (yc ξ u) ξ = 0 := yc_orth hξ
  have hL' : Real.cosh (hdist u (hptOf ξ (yc ξ u) D)) = Real.cosh (Real.log (lev ξ u / D)) := by
    have h := levYcFormula hξ u (hptOf ξ (yc ξ u) D)
    rw [(hptOfLevelYc ξ hξ hyc hD).1, (hptOfLevelYc ξ hξ hyc hD).2.1] at h
    simpa using h
  have harg : Real.log (lev ξ u / D) = -(Real.log D - Real.log (lev ξ u)) := by
    rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hD), neg_sub]
  rw [harg, Real.cosh_neg] at hL'
  have hnn : 0 ≤ Real.log D - Real.log (lev ξ u) := sub_nonneg.2 (Real.log_le_log hpos hle)
  calc hdist u (hptOf ξ (yc ξ u) D)
      = Real.arcosh (Real.cosh (hdist u (hptOf ξ (yc ξ u) D))) :=
        (Real.arcosh_cosh (hI.nonneg _ _)).symm
    _ = Real.arcosh (Real.cosh (Real.log D - Real.log (lev ξ u))) := by rw [hL']
    _ = Real.log D - Real.log (lev ξ u) := Real.arcosh_cosh hnn

theorem collarCocompact (hA : POBasic n) (hI : HypIsoData n)
    {Γ : Subgroup (PO n 1)} {P : Set (E n)} {ht : E n → ℝ} {D : ℝ}
    (hPsub : P ⊆ Sph n) (heq : IsEquivHeight Γ P ht)
    (hPinv : ∀ (γ : Γ) (ξ : E n), ξ ∈ P → bd (γ : PO n 1) ξ ∈ P)
    (hK : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n,
      (∀ ξ ∈ P, u ∉ horoball ξ (ht ξ)) → ∃ γ : Γ, (γ : PO n 1) • u ∈ K)
    (hcpt : ∀ ξ ∈ P, ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n,
      busemann ξ u = ht ξ → ∃ γ : Γ, bd (γ : PO n 1) ξ = ξ ∧ (γ : PO n 1) • u ∈ K)
    {m : ℕ} {ξs : Fin m → E n} (hξs : ∀ i, ξs i ∈ P)
    (hrep : ∀ ξ ∈ P, ∃ (i : Fin m) (γ : Γ), bd (γ : PO n 1) (ξs i) = ξ) :
    ∃ K' : Set (E n), IsCompact K' ∧ ∀ u : E n,
      (∀ ξ ∈ P, ht ξ - D ≤ busemann ξ u) → ∃ γ : Γ, (γ : PO n 1) • u ∈ K' := by
  classical
  obtain ⟨K, hKc, hK⟩ := hK
  obtain ⟨R₀, hR₀⟩ := exists_hdist_le_of_isCompact_bundled hI hKc
  choose Ki hKic hKicpt using fun i : Fin m => hcpt (ξs i) (hξs i)
  choose Ri hRi using fun i : Fin m => exists_hdist_le_of_isCompact_bundled hI (hKic i)
  set B : ℝ := max R₀ 0 + (∑ i : Fin m, max (Ri i) 0) + max D 0 + 1 with hBdef
  have hmaxR₀B : max R₀ 0 ≤ B := by
    rw [hBdef]
    have h1 : (0:ℝ) ≤ ∑ i : Fin m, max (Ri i) 0 :=
      Finset.sum_nonneg (fun i _ => real_le_max_right (Ri i) 0)
    have h2 : (0:ℝ) ≤ max D 0 := real_le_max_right D 0
    linarith
  have hmaxRiB : ∀ i : Fin m, max (Ri i) 0 ≤ B := by
    intro i
    rw [hBdef]
    have h1 : max (Ri i) 0 ≤ ∑ j : Fin m, max (Ri j) 0 :=
      Finset.single_le_sum (f := fun j : Fin m => max (Ri j) 0)
        (fun j _ => real_le_max_right (Ri j) 0) (Finset.mem_univ i)
    have h2 : (0:ℝ) ≤ max R₀ 0 := real_le_max_right R₀ 0
    have h3 : (0:ℝ) ≤ max D 0 := real_le_max_right D 0
    linarith
  have hR₀B : ∀ y ∈ K, hdist (0 : E n) y ≤ B := by
    intro y hy
    have h1 := hR₀ y hy
    have h2 : R₀ ≤ max R₀ 0 := real_le_max_left R₀ 0
    linarith
  have hKiB : ∀ (i : Fin m) (y : E n), y ∈ Ki i → hdist (0 : E n) y ≤ B := by
    intro i y hy
    have h1 := hRi i y hy
    have h2 : Ri i ≤ max (Ri i) 0 := real_le_max_left (Ri i) 0
    have h3 := hmaxRiB i
    linarith
  have hRiD : ∀ i : Fin m, Ri i + D ≤ B := by
    intro i
    rw [hBdef]
    have h1 : Ri i ≤ ∑ j : Fin m, max (Ri j) 0 :=
      le_trans (real_le_max_left (Ri i) 0)
        (Finset.single_le_sum (f := fun j : Fin m => max (Ri j) 0)
          (fun j _ => real_le_max_right (Ri j) 0) (Finset.mem_univ i))
    have h2 : D ≤ max D 0 := real_le_max_left D 0
    have h3 : (0:ℝ) ≤ max R₀ 0 := real_le_max_right R₀ 0
    linarith
  have hYinv : ∀ (γ : Γ) (w : E n), (∀ ξ ∈ P, ht ξ - D ≤ busemann ξ w) →
      ∀ ξ ∈ P, ht ξ - D ≤ busemann ξ ((γ : PO n 1) • w) := by
    intro γ w hw ξ hξP
    have hξ'P : bd ((γ⁻¹ : Γ) : PO n 1) ξ ∈ P := hPinv γ⁻¹ ξ hξP
    have hbdc : bd ((γ : PO n 1)) (bd ((γ⁻¹ : Γ) : PO n 1) ξ) = ξ := by
      rw [← hA.bd_mul ((γ : PO n 1)) (((γ⁻¹ : Γ) : PO n 1)) ξ (hPsub hξP)]
      rw [subgroup_coe_mul_inv γ, hA.bd_one ξ (hPsub hξP)]
    have hcoc : busemann ξ ((γ : PO n 1) • w)
        = busemann (bd ((γ⁻¹ : Γ) : PO n 1) ξ) w
          + bCocy ((γ : PO n 1)) (bd ((γ⁻¹ : Γ) : PO n 1) ξ) := by
      have h := hI.busemann_cocycle ((γ : PO n 1)) (bd ((γ⁻¹ : Γ) : PO n 1) ξ) w (hPsub hξ'P)
      rw [hbdc] at h
      rw [show bCocy ((γ : PO n 1)) (bd ((γ⁻¹ : Γ) : PO n 1) ξ)
        = busemann ξ ((γ : PO n 1) • (0 : E n)) from by unfold bCocy; rw [hbdc]]
      exact h
    have hht := heq γ (bd ((γ⁻¹ : Γ) : PO n 1) ξ) hξ'P
    rw [hbdc] at hht
    have hw' := hw (bd ((γ⁻¹ : Γ) : PO n 1) ξ) hξ'P
    rw [hcoc]
    linarith
  refine ⟨{x : E n | hdist (0 : E n) x ≤ B}, hI.ball_compact 0 B, ?_⟩
  intro u hu
  by_cases hX : ∀ ξ ∈ P, u ∉ horoball ξ (ht ξ)
  · obtain ⟨γ, hγ⟩ := hK u hX
    exact ⟨γ, hR₀B _ hγ⟩
  · push_neg at hX
    obtain ⟨ξ, hξP, hξmem⟩ := hX
    have hξlt : busemann ξ u < ht ξ := hξmem
    obtain ⟨i, γ₀, hγ₀⟩ := hrep ξ hξP
    set v : E n := ((γ₀⁻¹ : Γ) : PO n 1) • u with hvdef
    have hv : ∀ ζ ∈ P, ht ζ - D ≤ busemann ζ v := hYinv γ₀⁻¹ u hu
    have hvi : ht (ξs i) - D ≤ busemann (ξs i) v := hv (ξs i) (hξs i)
    have hvlt : busemann (ξs i) v < ht (ξs i) := by
      have hcoc : busemann ξ ((γ₀ : PO n 1) • v)
          = busemann (ξs i) v + bCocy ((γ₀ : PO n 1)) (ξs i) := by
        have h := hI.busemann_cocycle ((γ₀ : PO n 1)) (ξs i) v (hPsub (hξs i))
        rw [hγ₀] at h
        rw [show bCocy ((γ₀ : PO n 1)) (ξs i)
          = busemann ξ ((γ₀ : PO n 1) • (0 : E n)) from by unfold bCocy; rw [hγ₀]]
        exact h
      have h1 : ((γ₀ : PO n 1)) • v = u := by
        rw [hvdef, ← hA.mul_smul, subgroup_coe_mul_inv γ₀, hA.one_smul]
      have hht := heq γ₀ (ξs i) (hξs i)
      rw [hγ₀] at hht
      rw [h1] at hcoc
      linarith
    set w : E n := hptOf (ξs i) (yc (ξs i) v) (Real.exp (ht (ξs i))) with hwdef
    have hpt := hptOfLevelYc (ξs i) (hPsub (hξs i)) (y := yc (ξs i) v)
      (yc_orth (ξ := ξs i) (u := v) (hPsub (hξs i))) (Real.exp_pos (ht (ξs i)))
    have hbusw : busemann (ξs i) w = ht (ξs i) := by
      rw [hwdef]
      have h := hpt.2.2
      rw [Real.log_exp] at h
      exact h
    have hdistvw : hdist v w = ht (ξs i) - busemann (ξs i) v := by
      have h := hdist_hptOf_foot hI (hPsub (hξs i)) v (Real.exp_pos (ht (ξs i)))
        (by rw [lev_eq_exp (hPsub (hξs i)) v]; exact Real.exp_le_exp.2 (le_of_lt hvlt))
      rw [hwdef, h, Real.log_exp, lev_eq_exp (hPsub (hξs i)) v, Real.log_exp]
    have hleD : hdist v w ≤ D := by rw [hdistvw]; linarith
    obtain ⟨γ, hγfix, hγw⟩ := hKicpt i w hbusw
    refine ⟨γ * γ₀⁻¹, ?_⟩
    have h1 : ((γ * γ₀⁻¹ : Γ) : PO n 1) • u = ((γ : PO n 1)) • v := by
      rw [hvdef]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hA.mul_smul, hA.one_smul]
    show hdist (0 : E n) (((γ * γ₀⁻¹ : Γ) : PO n 1) • u) ≤ B
    rw [h1]
    have h2 : hdist (((γ : PO n 1)) • w) (((γ : PO n 1)) • v) = hdist w v := hI.isom_smul _ _ _
    have h3 : hdist (0 : E n) (((γ : PO n 1)) • w) ≤ Ri i := hRi i _ hγw
    have h4 : hdist (((γ : PO n 1)) • w) (((γ : PO n 1)) • v) ≤ D := by
      rw [h2, ← hd_symm hI v w]; exact hleD
    have h5 := hd_triangle hI (0 : E n) (((γ : PO n 1)) • w) (((γ : PO n 1)) • v)
    have h6 : Ri i + D ≤ B := hRiD i
    linarith


/-! ## Bundled cusp data and the collar-thickened part -/

/-- The data produced by `GeomFiniteProp`: a `Γ`-invariant family of pairwise disjoint horoballs
with `Γ`-cocompact complement and `Γ_ξ`-cocompact level sets. -/
structure CuspData (n : ℕ) (Γ : Subgroup (PO n 1)) where
  P : Set (E n)
  ht : E n → ℝ
  hPsub : P ⊆ Sph n
  hPinv : ∀ (γ : Γ) (ξ : E n), ξ ∈ P → bd (γ : PO n 1) ξ ∈ P
  hHeq : ∀ (γ : Γ) (ξ : E n), ξ ∈ P → ∀ u : E n,
    (γ : PO n 1) • u ∈ horoball (bd (γ : PO n 1) ξ) (ht (bd (γ : PO n 1) ξ)) ↔
      u ∈ horoball ξ (ht ξ)
  hdisj : P.Pairwise (fun ξ η => Disjoint (horoball ξ (ht ξ)) (horoball η (ht η)))
  K : Set (E n)
  hKc : IsCompact K
  hK : ∀ u : E n, (∀ ξ ∈ P, u ∉ horoball ξ (ht ξ)) → ∃ γ : Γ, (γ : PO n 1) • u ∈ K
  hcpt : ∀ ξ ∈ P, ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n,
    busemann ξ u = ht ξ → ∃ γ : Γ, bd (γ : PO n 1) ξ = ξ ∧ (γ : PO n 1) • u ∈ K

noncomputable def cuspDataOfGeomFinite {n : ℕ} (hG : GeomFiniteProp n) {Γ : Subgroup (PO n 1)}
    (hΓ : HypLattice Γ) : CuspData n Γ := by
  classical
  have h := hG Γ hΓ
  have hb := h.choose_spec.choose_spec
  exact
    { P := h.choose
      ht := h.choose_spec.choose
      hPsub := hb.1
      hPinv := hb.2.1
      hHeq := hb.2.2.1
      hdisj := hb.2.2.2.1
      K := hb.2.2.2.2.1.choose
      hKc := hb.2.2.2.2.1.choose_spec.1
      hK := hb.2.2.2.2.1.choose_spec.2
      hcpt := hb.2.2.2.2.2.1 }

/-- A Busemann level cut determines the level. -/
theorem eq_of_sub_lt_iff {A B c : ℝ} (h : ∀ t : ℝ, t + c < A ↔ t < B) : B = A - c := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : (B + (A - c)) / 2 + c < A := by linarith
    have h2 : ¬ ((B + (A - c)) / 2 < B) := by linarith
    exact h2 ((h _).mp h1)
  · have h1 : ¬ ((B + (A - c)) / 2 + c < A) := by linarith
    have h2 : (B + (A - c)) / 2 < B := by linarith
    exact h1 ((h _).mpr h2)

namespace CuspData

variable {n : ℕ} {Γ : Subgroup (PO n 1)}

/-- The horoball invariance implies that `ht` is a `Γ`-equivariant height. -/
theorem heq (cd : CuspData n Γ) (hA : POBasic n) (hI : HypIsoData n) :
    IsEquivHeight Γ cd.P cd.ht := by
  intro γ ξ hξ
  have hξS : ξ ∈ Sph n := cd.hPsub hξ
  have hb : bd (γ : PO n 1) ξ ∈ Sph n := hA.bd_mem (γ : PO n 1) ξ hξS
  have hcoc : ∀ u : E n, busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • u)
      = busemann ξ u + bCocy (γ : PO n 1) ξ :=
    fun u => hI.busemann_cocycle (γ : PO n 1) ξ u hξS
  have hiff : ∀ t : ℝ, t + bCocy (γ : PO n 1) ξ < cd.ht (bd (γ : PO n 1) ξ)
      ↔ t < cd.ht ξ := by
    intro t
    obtain ⟨s, hs⟩ := busemann_ray_surj hξS t
    rw [← hs]
    have h := cd.hHeq γ ξ hξ (s • ξ)
    simpa only [horoball, Set.mem_ofPred_eq, hcoc (s • ξ)] using h
  have := eq_of_sub_lt_iff hiff
  linarith

/-- The `Γ`-invariance of the collar-thickened part. -/
theorem collarInv (cd : CuspData n Γ) (hA : POBasic n) (hI : HypIsoData n) {D : ℝ}
    (γ : Γ) (u : E n)
    (hu : ∀ ξ ∈ cd.P, cd.ht ξ - D ≤ busemann ξ u) :
    ∀ ξ ∈ cd.P, cd.ht ξ - D ≤ busemann ξ ((γ : PO n 1) • u) := by
  intro ξ hξ
  have hξ' : bd ((γ⁻¹ : Γ) : PO n 1) ξ ∈ cd.P := cd.hPinv γ⁻¹ ξ hξ
  have hbdc : bd (γ : PO n 1) (bd ((γ⁻¹ : Γ) : PO n 1) ξ) = ξ := by
    rw [← hA.bd_mul (γ : PO n 1) ((γ⁻¹ : Γ) : PO n 1) ξ (cd.hPsub hξ)]
    rw [subgroup_coe_mul_inv γ, hA.bd_one ξ (cd.hPsub hξ)]
  have hcoc : busemann ξ ((γ : PO n 1) • u)
      = busemann (bd ((γ⁻¹ : Γ) : PO n 1) ξ) u
        + bCocy (γ : PO n 1) (bd ((γ⁻¹ : Γ) : PO n 1) ξ) := by
    have h := hI.busemann_cocycle (γ : PO n 1) (bd ((γ⁻¹ : Γ) : PO n 1) ξ) u (cd.hPsub hξ')
    rw [hbdc] at h
    rw [show bCocy (γ : PO n 1) (bd ((γ⁻¹ : Γ) : PO n 1) ξ)
      = busemann ξ ((γ : PO n 1) • (0 : E n)) from by unfold bCocy; rw [hbdc]]
    exact h
  have hht := cd.heq hA hI γ (bd ((γ⁻¹ : Γ) : PO n 1) ξ) hξ'
  rw [hbdc] at hht
  have hu' := hu (bd ((γ⁻¹ : Γ) : PO n 1) ξ) hξ'
  rw [hcoc]
  linarith

/-- The collar-thickened part is `Γ`-cocompact, with a compact set contained in it. -/
theorem collarCompact (cd : CuspData n Γ) (hA : POBasic n) (hI : HypIsoData n)
    {m : ℕ} {ξs : Fin m → E n} (hξs : ∀ i, ξs i ∈ cd.P)
    (hrep : ∀ ξ ∈ cd.P, ∃ (i : Fin m) (γ : Γ), bd (γ : PO n 1) (ξs i) = ξ) (D : ℝ) :
    ∃ K : Set (E n), IsCompact K ∧
      K ⊆ {u : E n | ∀ ξ ∈ cd.P, cd.ht ξ - D ≤ busemann ξ u} ∧
      ∀ u ∈ {u : E n | ∀ ξ ∈ cd.P, cd.ht ξ - D ≤ busemann ξ u},
        ∃ γ : Γ, (γ : PO n 1) • u ∈ K := by
  obtain ⟨K', hK'c, hK'⟩ := collarCocompact hA hI cd.hPsub (cd.heq hA hI) cd.hPinv
    ⟨cd.K, cd.hKc, cd.hK⟩ cd.hcpt hξs hrep (D := D)
  have hbus : ∀ ξ ∈ cd.P, Continuous fun u : E n => busemann ξ u := by
    intro ξ hξ
    have harg : Continuous fun u : E n => tpart u - inner ℝ u ξ := by
      unfold tpart; fun_prop
    have hpos : ∀ u : E n, 0 < tpart u - inner ℝ u ξ := by
      intro u; rw [← lev]; exact lev_pos ξ (cd.hPsub hξ) u
    exact harg.log fun u => ne_of_gt (hpos u)
  have hclosed : IsClosed {u : E n | ∀ ξ ∈ cd.P, cd.ht ξ - D ≤ busemann ξ u} := by
    have h1 : {u : E n | ∀ ξ ∈ cd.P, cd.ht ξ - D ≤ busemann ξ u}
        = ⋂ (ξ : E n), {u : E n | ξ ∈ cd.P → cd.ht ξ - D ≤ busemann ξ u} := by
      ext u; simp [Set.mem_iInter]
    rw [h1]
    refine isClosed_iInter fun ξ => ?_
    by_cases hξ : ξ ∈ cd.P
    · have h2 : {u : E n | ξ ∈ cd.P → cd.ht ξ - D ≤ busemann ξ u}
          = {u : E n | cd.ht ξ - D ≤ busemann ξ u} := by
        ext u; simp [hξ]
      rw [h2]
      exact isClosed_le continuous_const (hbus ξ hξ)
    · have h2 : {u : E n | ξ ∈ cd.P → cd.ht ξ - D ≤ busemann ξ u} = Set.univ := by
        ext u; simp [hξ]
      rw [h2]; exact isClosed_univ
  refine ⟨K' ∩ {u : E n | ∀ ξ ∈ cd.P, cd.ht ξ - D ≤ busemann ξ u}, hK'c.inter_right hclosed,
    Set.inter_subset_right, ?_⟩
  intro u hu
  obtain ⟨γ, hγ⟩ := hK' u hu
  exact ⟨γ, hγ, cd.collarInv hA hI γ u hu⟩

end CuspData

/-! ## Setup: Busemann facts and the cusp correspondence -/

/-- The Busemann function is 1-Lipschitz for `hdist`, from `HypIsoData` alone (via
`levYcFormula`). -/
theorem busemann_lipschitz' (hI : HypIsoData n) {ξ : E n} (hξ : ξ ∈ Sph n) (u v : E n) :
    |busemann ξ u - busemann ξ v| ≤ hdist u v := by
  have hu := lev_pos ξ hξ u
  have hv := lev_pos ξ hξ v
  have h1 : busemann ξ u - busemann ξ v = Real.log (lev ξ u / lev ξ v) := by
    rw [Real.log_div (ne_of_gt hu) (ne_of_gt hv), lev_eq_exp hξ u, lev_eq_exp hξ v,
      Real.log_exp, Real.log_exp]
  have h2 := levYcFormula hξ u v
  have hX : 0 ≤ (lev ξ u * lev ξ v / 2) * ‖yc ξ u - yc ξ v‖ ^ 2 :=
    mul_nonneg (div_nonneg (mul_nonneg (le_of_lt hu) (le_of_lt hv)) (by norm_num)) (sq_nonneg _)
  have h3 : Real.cosh (busemann ξ u - busemann ξ v) ≤ Real.cosh (hdist u v) := by
    rw [h1]
    linarith [h2, hX]
  have h4 : ‖busemann ξ u - busemann ξ v‖ ≤ ‖hdist u v‖ := Real.cosh_le_cosh.mp h3
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hI.nonneg u v)] at h4

namespace CuspData

variable {n : ℕ} {Γ : Subgroup (PO n 1)}

/-- The Busemann cocycle expressed through the height function: for a `Γ`-equivariant horoball
family, `β_{bd γ ξ}(γ•u) = β_ξ u + (ht (bd γ ξ) - ht ξ)`. -/
theorem busemann_shift (cd : CuspData n Γ) (hA : POBasic n) (hI : HypIsoData n)
    {ξ : E n} (hξ : ξ ∈ cd.P) (γ : Γ) (u : E n) :
    busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • u)
      = busemann ξ u + (cd.ht (bd (γ : PO n 1) ξ) - cd.ht ξ) := by
  have h1 := hI.busemann_cocycle (γ : PO n 1) ξ u (cd.hPsub hξ)
  rw [h1]
  have h := cd.heq hA hI γ ξ hξ
  show busemann ξ u + bCocy (γ : PO n 1) ξ
    = busemann ξ u + (cd.ht (bd (γ : PO n 1) ξ) - cd.ht ξ)
  rw [h]; ring

/-- The horoball family at levels `ht` is invariant under `Γ` at every level. -/
theorem horoball_smul_iff (cd : CuspData n Γ) (hA : POBasic n) (hI : HypIsoData n)
    {ξ : E n} (hξ : ξ ∈ cd.P) (γ : Γ) (u : E n) {s : ℝ} :
    (γ : PO n 1) • u ∈ horoball (bd (γ : PO n 1) ξ) (cd.ht (bd (γ : PO n 1) ξ) + s)
      ↔ u ∈ horoball ξ (cd.ht ξ + s) := by
  rw [horoball, horoball, Set.mem_setOf_eq, Set.mem_setOf_eq, cd.busemann_shift hA hI hξ γ u]
  constructor <;> intro h <;> linarith

/-- Every `Γ`-orbit of `P` meets the set of points of bounded height: `ht` is bounded on a
transversal. -/
theorem ht_transversal (cd : CuspData n Γ) (hA : POBasic n) (hI : HypIsoData n) :
    ∃ R : ℝ, ∀ ξ ∈ cd.P, ∃ γ : Γ, |cd.ht (bd (γ : PO n 1) ξ)| ≤ R := by
  obtain ⟨M, hM⟩ := exists_hdist_le_of_isCompact_bundled hI cd.hKc
  refine ⟨max M 0, fun ξ hξ => ?_⟩
  have hp : ∀ η ∈ cd.P, hray ξ (-(cd.ht ξ)) ∉ horoball η (cd.ht η) :=
    hrayOutsideHoroballs n cd.P cd.ht cd.hPsub cd.hdisj ξ hξ
  obtain ⟨γ, hγ⟩ := cd.hK _ hp
  refine ⟨γ, ?_⟩
  have hbp : busemann ξ (hray ξ (-(cd.ht ξ))) = cd.ht ξ := by
    rw [busemann_hray ξ (cd.hPsub hξ) (-(cd.ht ξ))]; ring
  have hsh := cd.busemann_shift hA hI hξ γ (hray ξ (-(cd.ht ξ)))
  rw [hbp] at hsh
  have hlip := busemann_lipschitz' hI (hA.bd_mem (γ : PO n 1) ξ (cd.hPsub hξ))
    ((γ : PO n 1) • hray ξ (-(cd.ht ξ))) (0 : E n)
  have hzero : busemann (bd (γ : PO n 1) ξ) (0 : E n) = 0 := by
    rw [busemann]; simp [tpart]
  rw [hzero, sub_zero] at hlip
  have h1 : |cd.ht (bd (γ : PO n 1) ξ)| ≤ M := by
    have h2 : busemann (bd (γ : PO n 1) ξ) ((γ : PO n 1) • hray ξ (-(cd.ht ξ)))
        = cd.ht (bd (γ : PO n 1) ξ) := by
      rw [hsh]; ring
    rw [h2] at hlip
    rw [hd_symm hI] at hlip
    exact le_trans hlip (hM _ hγ)
  exact le_trans h1 (real_le_max_left M 0)

end CuspData

/-! ## The cusp correspondence is a bijection -/

/-- `cuspCorr` applied to `f` and to `f.symm` give mutually inverse correspondences: the backward
map sends `F ξ` back to `ξ`.  This makes `F` injective. -/
theorem cuspCorr_inj (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (hG : GeomFiniteProp n) (hC : CuspRecognitionProp n)
    {Γ Λ : Subgroup (PO n 1)} (hΓ : HypLattice Γ) (hΛ : HypLattice Λ) (f : Γ ≃* Λ)
    {F G : E n → E n}
    (hFmem : ∀ ξ ∈ parFixSet Γ, F ξ ∈ parFixSet Λ)
    (hFeq : ∀ ξ ∈ parFixSet Γ, ∀ γ : Γ, F (bd γ ξ) = bd (f γ) (F ξ))
    (hGmem : ∀ η ∈ parFixSet Λ, G η ∈ parFixSet Γ)
    (hGF : ∀ η ∈ parFixSet Λ, F (G η) = η)
    (hFG : ∀ ξ ∈ parFixSet Γ, G (F ξ) = ξ) :
    Set.InjOn F (parFixSet Γ) := by
  intro ξ₁ h₁ ξ₂ h₂ hF
  have h1 : G (F ξ₁) = ξ₁ := hFG ξ₁ h₁
  have h2 : G (F ξ₂) = ξ₂ := hFG ξ₂ h₂
  rw [hF] at h1
  rw [h1] at h2
  exact h2

/-! ## Shifting a horoball family so that all heights are `≤ 0` -/

/-- Disjointness forces the heights of a horoball family to be bounded above: `0` lies in at most
one horoball, so at most one point of `P` has positive height. -/
theorem bddAbove_height {P : Set (E n)} {ht : E n → ℝ}
    (hdisj : P.Pairwise (fun ξ η => Disjoint (horoball ξ (ht ξ)) (horoball η (ht η)))) :
    BddAbove (ht '' P) := by
  have hmem0 : ∀ ξ (t : ℝ), (0 : E n) ∈ horoball ξ t ↔ 0 < t := by
    intro ξ t
    simp only [horoball, Set.mem_ofPred_eq, busemann_zero]
  by_cases hpos : ∃ ξ ∈ P, 0 < ht ξ
  · obtain ⟨ξ₀, hξ₀P, hξ₀pos⟩ := hpos
    refine ⟨max (ht ξ₀) 0, ?_⟩
    rintro y ⟨η, hηP, rfl⟩
    by_cases hη : 0 < ht η
    · have h0₁ : (0 : E n) ∈ horoball ξ₀ (ht ξ₀) := (hmem0 ξ₀ (ht ξ₀)).mpr hξ₀pos
      have h0₂ : (0 : E n) ∈ horoball η (ht η) := (hmem0 η (ht η)).mpr hη
      have hξη : ξ₀ = η := by
        by_contra hne
        exact (Set.disjoint_left.mp (hdisj hξ₀P hηP hne) h0₁) h0₂
      subst hξη
      exact le_max_left _ _
    · exact le_trans (not_lt.mp hη) (le_max_right _ _)
  · refine ⟨0, ?_⟩
    rintro y ⟨η, hηP, rfl⟩
    exact not_lt.mp fun h => hpos ⟨η, hηP, h⟩

/-- **Normalising the heights.**  A `Γ`-equivariant disjoint horoball family can be shifted down by
a (per-orbit) constant so that all heights become `≤ 0`.  This is what makes the cusp regions have
bounded level, which the cusp map estimates need. -/
theorem cuspHeightNormalize {Γ : Subgroup (PO n 1)} {P : Set (E n)} {ht : E n → ℝ}
    (heq : IsEquivHeight Γ P ht)
    (hdisj : P.Pairwise (fun ξ η => Disjoint (horoball ξ (ht ξ)) (horoball η (ht η)))) :
    ∃ ht' : E n → ℝ, (∀ ξ ∈ P, ht' ξ ≤ 0) ∧ IsEquivHeight Γ P ht' ∧ ∀ ξ ∈ P, ht' ξ ≤ ht ξ := by
  obtain ⟨C, hC⟩ := bddAbove_height hdisj
  refine ⟨fun ξ => ht ξ - max C 0, fun ξ hξ => ?_, fun γ ξ hξ => ?_, fun ξ hξ => ?_⟩
  · show ht ξ - max C 0 ≤ 0
    have h1 := hC (Set.mem_image_of_mem ht hξ)
    have h2 : C ≤ max C 0 := le_max_left _ _
    linarith
  · show ht (bd (γ : PO n 1) ξ) - max C 0 = ht ξ - max C 0 + bCocy (γ : PO n 1) ξ
    rw [heq γ ξ hξ]; ring
  · show ht ξ - max C 0 ≤ ht ξ
    have h2 : (0:ℝ) ≤ max C 0 := le_max_right _ _
    linarith

/-! ## A `Γ`-invariant choice of representative cusp -/

/-- Given finitely many representatives `ξs` covering `P` up to `Γ`-orbits, one can choose the index
`rep ξ` in a `Γ`-INVARIANT way: the set of admissible indices is constant on orbits, so its minimum
is invariant.  This is what makes the transport of the cusp map across orbits equivariant without
any cross-representative estimate. -/
theorem cuspRepInvariant {Γ : Subgroup (PO n 1)} {P : Set (E n)} (hA : POBasic n)
    (hPsub : P ⊆ Sph n)
    (hPinv : ∀ (γ : Γ) (ξ : E n), ξ ∈ P → bd (γ : PO n 1) ξ ∈ P)
    {m : ℕ} {ξs : Fin m → E n} (hξs : ∀ i, ξs i ∈ P)
    (hrep : ∀ ξ ∈ P, ∃ (i : Fin m) (γ : Γ), bd (γ : PO n 1) (ξs i) = ξ) :
    ∃ rep : (ξ : E n) → ξ ∈ P → Fin m,
      (∀ ξ (hξ : ξ ∈ P), ∃ γ : Γ, bd (γ : PO n 1) (ξs (rep ξ hξ)) = ξ) ∧
      (∀ (γ : Γ) (ξ : E n) (hξ : ξ ∈ P),
        rep (bd (γ : PO n 1) ξ) (hPinv γ ξ hξ) = rep ξ hξ) := by
  classical
  have hne : ∀ ξ (hξ : ξ ∈ P),
      ((Finset.univ.filter (fun i : Fin m => ∃ γ : Γ, bd (γ : PO n 1) (ξs i) = ξ))).Nonempty := by
    intro ξ hξ
    obtain ⟨i, γ, hγ⟩ := hrep ξ hξ
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ⟨γ, hγ⟩⟩⟩
  let rep : (ξ : E n) → ξ ∈ P → Fin m := fun ξ hξ =>
    (Finset.univ.filter (fun i : Fin m => ∃ γ : Γ, bd (γ : PO n 1) (ξs i) = ξ)).min' (hne ξ hξ)
  have hrep_mem : ∀ ξ (hξ : ξ ∈ P), ∃ γ : Γ, bd (γ : PO n 1) (ξs (rep ξ hξ)) = ξ := by
    intro ξ hξ
    have hmem : (Finset.univ.filter (fun i : Fin m => ∃ γ : Γ, bd (γ : PO n 1) (ξs i) = ξ)).min'
          (hne ξ hξ)
        ∈ (Finset.univ.filter (fun i : Fin m => ∃ γ : Γ, bd (γ : PO n 1) (ξs i) = ξ)) :=
      Finset.min'_mem _ _
    exact (Finset.mem_filter.mp hmem).2
  refine ⟨rep, hrep_mem, ?_⟩
  intro γ ξ hξ
  have hbdξ : bd (γ : PO n 1) ξ ∈ P := hPinv γ ξ hξ
  have hset : (Finset.univ.filter
        (fun i : Fin m => ∃ γ' : Γ, bd (γ' : PO n 1) (ξs i) = bd (γ : PO n 1) ξ))
      = (Finset.univ.filter (fun i : Fin m => ∃ γ' : Γ, bd (γ' : PO n 1) (ξs i) = ξ)) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · rintro ⟨γ', hγ'⟩
      refine ⟨(γ⁻¹ : Γ) * γ', ?_⟩
      have h1 : bd (((γ⁻¹ : Γ) * γ' : Γ) : PO n 1) (ξs i)
          = bd (((γ : PO n 1))⁻¹) (bd (γ' : PO n 1) (ξs i)) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hA.bd_mul ((γ : PO n 1)⁻¹) ((γ' : Γ) : PO n 1) (ξs i) (hPsub (hξs i))
      rw [h1, hγ']
      exact bd_inv_bd_cuspCorr hA (hPsub hξ)
    · rintro ⟨γ', hγ'⟩
      refine ⟨γ * γ', ?_⟩
      have h1 : bd (((γ * γ' : Γ)) : PO n 1) (ξs i)
          = bd (γ : PO n 1) (bd (γ' : PO n 1) (ξs i)) := by
        rw [Subgroup.coe_mul]
        exact hA.bd_mul (γ : PO n 1) (γ' : PO n 1) (ξs i) (hPsub (hξs i))
      rw [h1, hγ']
  show (Finset.univ.filter
        (fun i : Fin m => ∃ γ' : Γ, bd (γ' : PO n 1) (ξs i) = bd (γ : PO n 1) ξ)).min'
        (hne (bd (γ : PO n 1) ξ) hbdξ)
      = (Finset.univ.filter (fun i : Fin m => ∃ γ' : Γ, bd (γ' : PO n 1) (ξs i) = ξ)).min'
        (hne ξ hξ)
  apply le_antisymm
  · apply Finset.min'_le
    exact hset.symm ▸ Finset.min'_mem _ _
  · apply Finset.min'_le
    exact hset ▸ Finset.min'_mem _ _

/-- The point `hptOf ξ y D` of the horosphere of level `D` at `ξ` is at bounded distance
from the base point `0`, with the bound depending only on `D` and `‖y‖`. -/
theorem hdist_zero_hptOf_le (hI : HypIsoData n) {ξ y : E n} (hξ : ξ ∈ Sph n) {D : ℝ}
    (hD : 0 < D) :
    hdist (0 : E n) (hptOf ξ y D) ≤ Real.arcosh (Real.sqrt (1 +
      (((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) + D / 2 + D * ‖y‖)) ^ 2)) := by
  have hξn : ‖ξ‖ = 1 := by
    simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have hnum : 0 ≤ 1 + D ^ 2 * ‖y‖ ^ 2 := by positivity
  have hden : 0 < 2 * D := by linarith
  have hq : 0 ≤ (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) := div_nonneg hnum (le_of_lt hden)
  have hnorm : ‖hptOf ξ y D‖ ≤ (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) + D / 2 + D * ‖y‖ := by
    have h1 : hptOf ξ y D = ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2) • ξ + D • y := rfl
    rw [h1]
    calc ‖((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2) • ξ + D • y‖
        ≤ ‖((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2) • ξ‖ + ‖D • y‖ := norm_add_le _ _
      _ = |(1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2| * ‖ξ‖ + |D| * ‖y‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ = |(1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2| + D * ‖y‖ := by
            rw [hξn, mul_one, abs_of_pos hD]
      _ ≤ ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) + D / 2) + D * ‖y‖ := by
            have h2 : |(1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2|
                ≤ (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) + D / 2 := by
              rw [abs_le]
              constructor <;> linarith [hq, hD]
            linarith
  have h0 : hdist (0 : E n) (hptOf ξ y D) = Real.arcosh (tpart (hptOf ξ y D)) := by
    rw [hdist]
    have hz : tpart (0 : E n) = 1 := by rw [tpart]; norm_num
    rw [hz, one_mul, inner_zero_left, sub_zero]
  rw [h0]
  have htpart : tpart (hptOf ξ y D) = Real.sqrt (1 + ‖hptOf ξ y D‖ ^ 2) := rfl
  rw [htpart]
  refine Real.arcosh_le_arcosh (by positivity) (by positivity) |>.mpr ?_
  refine Real.sqrt_le_sqrt ?_
  nlinarith [hnorm, norm_nonneg (hptOf ξ y D), sq_nonneg ‖hptOf ξ y D‖,
    sq_nonneg ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) + D / 2 + D * ‖y‖)]

/-! ## The area C3 theorem -/

theorem equivQI (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hBb : ∀ m, BieberbachProp m) (hG : GeomFiniteProp n) (hC : CuspRecognitionProp n) :
    QIProp n := by
  intro Γ Λ hΓ hΛ f
  classical
  have hn2 : 2 ≤ n := by omega
  have hAb : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have hΓdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  have hΛdisc : IsDiscrete (SetLike.coe Λ) := hΛ.1
  -- the geometric-finiteness data, kept in explicit form (we need the parabolic clauses too)
  obtain ⟨PΓ, htΓ, hPΓsub, hPΓinv, hPΓeq, hPΓdisj, ⟨KΓc, hKΓcc, hKΓc0⟩, hcptΓ, hparΓ₁, hparΓ₂⟩ :=
    hG Γ hΓ
  obtain ⟨PΛ, htΛ, hPΛsub, hPΛinv, hPΛeq, hPΛdisj, ⟨KΛc, hKΛcc, hKΛc0⟩, hcptΛ, hparΛ₁, hparΛ₂⟩ :=
    hG Λ hΛ
  let cdΓ : CuspData n Γ :=
    { P := PΓ, ht := htΓ, hPsub := hPΓsub, hPinv := hPΓinv, hHeq := hPΓeq, hdisj := hPΓdisj,
      K := KΓc, hKc := hKΓcc, hK := hKΓc0, hcpt := hcptΓ }
  let cdΛ : CuspData n Λ :=
    { P := PΛ, ht := htΛ, hPsub := hPΛsub, hPinv := hPΛinv, hHeq := hPΛeq, hdisj := hPΛdisj,
      K := KΛc, hKc := hKΛcc, hK := hKΛc0, hcpt := hcptΛ }
  -- the cusp sets are contained in the parabolic fixed points, and vice versa
  have hPΓpar : ∀ ξ ∈ cdΓ.P, ξ ∈ parFixSet Γ :=
    fun ξ hξ => ⟨cdΓ.hPsub hξ, hparΓ₁ ξ hξ⟩
  have hPΛpar : ∀ η ∈ cdΛ.P, η ∈ parFixSet Λ :=
    fun η hη => ⟨cdΛ.hPsub hη, hparΛ₁ η hη⟩
  have hparΓP : ∀ ξ ∈ parFixSet Γ, ξ ∈ cdΓ.P := by
    rintro ξ ⟨hξS, γ, hγpar, hγbd⟩
    obtain ⟨ζ, hζP, hζbd⟩ := hparΓ₂ γ hγpar
    have hζξ : ζ = ξ := paraUniqueFixed hAb hId hγpar hξS hγbd (cdΓ.hPsub hζP) hζbd
    rw [hζξ] at hζP
    exact hζP
  have hparΛP : ∀ η ∈ parFixSet Λ, η ∈ cdΛ.P := by
    rintro η ⟨hηS, γ, hγpar, hγbd⟩
    obtain ⟨ζ, hζP, hζbd⟩ := hparΛ₂ γ hγpar
    have hζη : ζ = η := paraUniqueFixed hAb hId hγpar hηS hγbd (cdΛ.hPsub hζP) hζbd
    rw [hζη] at hζP
    exact hζP
  -- the heights are bounded above
  obtain ⟨CΓ, hCΓ⟩ := bddAbove_height cdΓ.hdisj
  obtain ⟨CΛ, hCΛ⟩ := bddAbove_height cdΛ.hdisj
  -- shrink amount: large enough that all cusp levels are ≤ 1
  set D : ℝ := max (max CΓ CΛ) 2 with hDdef
  have hDCΓ : CΓ ≤ D := le_trans (le_max_left _ _) (le_max_left _ _)
  have hDCΛ : CΛ ≤ D := le_trans (le_max_right _ _) (le_max_left _ _)
  have hD2 : (2 : ℝ) ≤ D := le_max_right _ _
  have hCΓ' : ∀ ξ ∈ cdΓ.P, cdΓ.ht ξ ≤ D := fun ξ hξ => le_trans (hCΓ (Set.mem_image_of_mem _ hξ)) hDCΓ
  have hCΛ' : ∀ η ∈ cdΛ.P, cdΛ.ht η ≤ D := fun η hη => le_trans (hCΛ (Set.mem_image_of_mem _ hη)) hDCΛ
  -- the collar-thickened parts
  set YΓ : Set (E n) := {u : E n | ∀ ξ ∈ cdΓ.P, cdΓ.ht ξ - D ≤ busemann ξ u} with hYΓdef
  set YΛ : Set (E n) := {u : E n | ∀ η ∈ cdΛ.P, cdΛ.ht η - D ≤ busemann η u} with hYΛdef
  -- the cusp correspondence
  obtain ⟨F, hFmem0, hFstab0, hFstab0', hFeq0, hFsurj0⟩ :=
    cuspCorr hn2 hA hI hBb hG hC hΓ hΛ f
  obtain ⟨G, hGmem0, hGstab0, hGstab0', hGeq0, hGsurj0⟩ :=
    cuspCorr hn2 hA hI hBb hG hC hΛ hΓ f.symm
  have hFmem : ∀ ξ ∈ cdΓ.P, F ξ ∈ cdΛ.P := fun ξ hξ => hparΛP (F ξ) (hFmem0 ξ (hPΓpar ξ hξ))
  have hGmem : ∀ η ∈ cdΛ.P, G η ∈ cdΓ.P := fun η hη => hparΓP (G η) (hGmem0 η (hPΛpar η hη))
  have hFeq : ∀ ξ ∈ cdΓ.P, ∀ γ : Γ, F (bd (γ : PO n 1) ξ) = bd ((f γ : Λ) : PO n 1) (F ξ) :=
    fun ξ hξ γ => hFeq0 ξ (hPΓpar ξ hξ) γ
  have hFstab : ∀ ξ ∈ cdΓ.P, ∀ γ : Γ,
      bd (γ : PO n 1) ξ = ξ → bd ((f γ : Λ) : PO n 1) (F ξ) = F ξ :=
    fun ξ hξ γ hγ => hFstab0 ξ (hPΓpar ξ hξ) γ hγ
  have hFstab' : ∀ ξ ∈ cdΓ.P, ∀ m : Λ,
      bd ((m : Λ) : PO n 1) (F ξ) = F ξ →
        ∃ γ : Γ, bd (γ : PO n 1) ξ = ξ ∧ f γ = m :=
    fun ξ hξ m hm => hFstab0' ξ (hPΓpar ξ hξ) m hm
  have hFsurj : ∀ η ∈ cdΛ.P, ∃ ξ ∈ cdΓ.P, F ξ = η := by
    intro η hη
    obtain ⟨ξ, hξ, hFξ⟩ := hFsurj0 η (hPΛpar η hη)
    exact ⟨ξ, hparΓP ξ hξ, hFξ⟩
  -- representatives of the cusp orbits and a Γ-invariant index
  obtain ⟨m, ξs, hξs, hrep⟩ := cuspOrbitsFinite n hAb hId Γ hΓ cdΓ.hPsub (cdΓ.heq hAb hId)
    cdΓ.hPinv cdΓ.hdisj ⟨cdΓ.K, cdΓ.hKc, cdΓ.hK⟩
  obtain ⟨irep, hirep, hirepinv⟩ := cuspRepInvariant hAb cdΓ.hPsub cdΓ.hPinv hξs hrep
  choose γr hγr using hirep
  -- the collar is Γ-cocompact with a compact subset
  obtain ⟨Kc, hKcc, hKcsub, hKc⟩ := cdΓ.collarCompact hAb hId hξs hrep D
  -- the thick orbit map on YΓ
  obtain ⟨γof, CT, hCT0, hγofK, hΦTloc, hΦTeq⟩ :=
    thickPhiX_spec hAb hId hΓdisc f (X := YΓ)
      (fun γ u hu => cdΓ.collarInv hAb hId γ u hu) hKcc hKc (N := 3) (by norm_num)
  have hPhiT_eq : ∀ u : E n, thickPhi f γof u = ((f (γof u) : Λ) : PO n 1) • (0 : E n) :=
    fun u => rfl
  set ΦT : E n → E n := thickPhi f γof with hΦTdef
  have hΦTloc' : ∀ u ∈ YΓ, ∀ v ∈ YΓ, hdist u v ≤ 3 → hdist (ΦT u) (ΦT v) ≤ CT := hΦTloc
  have hΦTeq' : ∀ γ : Γ, ∀ u : E n, u ∈ YΓ →
      hdist (ΦT ((γ : PO n 1) • u)) (((f γ : Λ) : PO n 1) • ΦT u) ≤ CT := hΦTeq
  -- the stabiliser acts with vanishing cocycle (hence preserves every level)
  have hvanΓ : ∀ (γ : Γ) (η : E n), η ∈ parFixSet Γ → bd (γ : PO n 1) η = η →
      bCocy (γ : PO n 1) η = 0 := by
    intro γ η hη hγ
    have hbus := cuspStab_busemann hId (Γ := Γ) (P := cdΓ.P) (ht := cdΓ.ht) cdΓ.hHeq
      (cdΓ.hPsub (hparΓP η hη)) (hparΓP η hη) γ hγ
    have h1 : bCocy (γ : PO n 1) η = busemann η ((γ : PO n 1) • (0 : E n)) := by
      unfold bCocy; rw [hγ]
    rw [h1, hbus 0, busemann_zero]
  have hvanΛ : ∀ (γ : Λ) (η : E n), η ∈ parFixSet Λ → bd (γ : PO n 1) η = η →
      bCocy (γ : PO n 1) η = 0 := by
    intro γ η hη hγ
    have hbus := cuspStab_busemann hId (Γ := Λ) (P := cdΛ.P) (ht := cdΛ.ht) cdΛ.hHeq
      (cdΛ.hPsub (hparΛP η hη)) (hparΛP η hη) γ hγ
    have h1 : bCocy (γ : PO n 1) η = busemann η ((γ : PO n 1) • (0 : E n)) := by
      unfold bCocy; rw [hγ]
    rw [h1, hbus 0, busemann_zero]
  -- the per-representative flat orbit maps
  have hlevξ1 : ∀ i : Fin m, ∀ γ : Γ, bd (γ : PO n 1) (ξs i) = ξs i →
      lev (ξs i) ((γ : PO n 1) • (0 : E n)) = 1 := by
    intro i γ hγ
    have hbus := cuspStab_busemann hId (Γ := Γ) (P := cdΓ.P) (ht := cdΓ.ht) cdΓ.hHeq (cdΓ.hPsub (hξs i)) (hξs i) γ hγ
    rw [lev_eq_exp (cdΓ.hPsub (hξs i)) _, hbus 0, busemann_zero, Real.exp_zero]
  have hlevη1 : ∀ i : Fin m, ∀ γ : Λ, bd (γ : PO n 1) (F (ξs i)) = F (ξs i) →
      lev (F (ξs i)) ((γ : PO n 1) • (0 : E n)) = 1 := by
    intro i γ hγ
    have hbus := cuspStab_busemann hId (Γ := Λ) (P := cdΛ.P) (ht := cdΛ.ht) cdΛ.hHeq (cdΛ.hPsub (hFmem (ξs i) (hξs i))) (hFmem (ξs i) (hξs i)) γ hγ
    rw [lev_eq_exp (cdΛ.hPsub (hFmem (ξs i) (hξs i))) _, hbus 0, busemann_zero, Real.exp_zero]
  have hcptξ1 : ∀ i : Fin m, ∃ K : Set (E n), IsCompact K ∧
      ∀ u : E n, lev (ξs i) u = 1 → ∃ γ : Γ, bd (γ : PO n 1) (ξs i) = ξs i ∧
        (γ : PO n 1) • u ∈ K := by
    intro i
    have hτ : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, busemann (ξs i) u = cdΓ.ht (ξs i) →
        ∃ γ : Γ, bd (γ : PO n 1) (ξs i) = ξs i ∧ (γ : PO n 1) • u ∈ K :=
      cdΓ.hcpt (ξs i) (hξs i)
    have hc := cuspCocompactAllLevels n hA hI Γ (ξs i) (cdΓ.hPsub (hξs i))
      (fun γ hγ => hvanΓ γ (ξs i) (hPΓpar (ξs i) (hξs i)) hγ) (cdΓ.ht (ξs i)) hτ
    obtain ⟨K, hKc, hK⟩ := hc 0
    refine ⟨K, hKc, fun u hu => hK u ?_⟩
    rw [lev_eq_exp (cdΓ.hPsub (hξs i)) u] at hu
    exact Real.exp_eq_exp.mp (hu.trans Real.exp_zero.symm)
  have hcptη1 : ∀ i : Fin m, ∃ K : Set (E n), IsCompact K ∧
      ∀ u : E n, lev (F (ξs i)) u = 1 → ∃ γ : Λ, bd (γ : PO n 1) (F (ξs i)) = F (ξs i) ∧
        (γ : PO n 1) • u ∈ K := by
    intro i
    have hτ : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, busemann (F (ξs i)) u = cdΛ.ht (F (ξs i)) →
        ∃ γ : Λ, bd (γ : PO n 1) (F (ξs i)) = F (ξs i) ∧ (γ : PO n 1) • u ∈ K :=
      cdΛ.hcpt (F (ξs i)) (hFmem (ξs i) (hξs i))
    have hc := cuspCocompactAllLevels n hA hI Λ (F (ξs i)) (cdΛ.hPsub (hFmem (ξs i) (hξs i)))
      (fun γ hγ => hvanΛ γ (F (ξs i)) (hPΛpar (F (ξs i)) (hFmem (ξs i) (hξs i))) hγ)
      (cdΛ.ht (F (ξs i))) hτ
    obtain ⟨K, hKc, hK⟩ := hc 0
    refine ⟨K, hKc, fun u hu => hK u ?_⟩
    rw [lev_eq_exp (cdΛ.hPsub (hFmem (ξs i) (hξs i))) u] at hu
    exact Real.exp_eq_exp.mp (hu.trans Real.exp_zero.symm)
  choose ψ ψδ ψy₀ ψR hψspec using fun i : Fin m =>
    flatOrbitMap n hAb hId f hΓdisc hΛdisc (cdΓ.hPsub (hξs i)) (cdΛ.hPsub (hFmem (ξs i) (hξs i)))
      (fun γ hγ => hFstab (ξs i) (hξs i) γ hγ)
      (fun mm hmm => hFstab0' (ξs i) (hPΓpar (ξs i) (hξs i)) mm hmm)
      (hlevξ1 i) (hlevη1 i) (hcptξ1 i) (hcptη1 i)
  -- the conjuncts of the flat-map specification we shall need
  have hψper : ∀ i : Fin m,
      (∀ y : E n, inner ℝ y (ξs i) = 0 → inner ℝ (ψ i y) (F (ξs i)) = 0) ∧
      (∃ L C : ℝ, 0 ≤ L ∧ 0 ≤ C ∧ ∀ x y : E n, inner ℝ x (ξs i) = 0 →
        inner ℝ y (ξs i) = 0 → ‖ψ i x - ψ i y‖ ≤ L * ‖x - y‖ + C) ∧
      (∃ C : ℝ, ∀ z : E n, inner ℝ z (F (ξs i)) = 0 →
        ∃ x : E n, inner ℝ x (ξs i) = 0 ∧ ‖ψ i x - z‖ ≤ C) ∧
      (∃ C : ℝ, ∀ γ : Γ, bd (γ : PO n 1) (ξs i) = ξs i → ∀ x : E n, inner ℝ x (ξs i) = 0 →
        ‖ψ i (flatAct (ξs i) (γ : PO n 1) x) - flatAct (F (ξs i)) ((f γ : Λ) : PO n 1) (ψ i x)‖ ≤ C) := by
    intro i
    obtain ⟨hy0, hR0, hδ, hlip, hsurj, heq⟩ := hψspec i
    refine ⟨?_, ?_, ?_, heq⟩
    · intro y hy
      exact (hδ y hy).2.2.2.1
    · obtain ⟨L, C, hL, hC, hf, _⟩ := hlip
      exact ⟨L, C, le_trans zero_le_one hL, hC, hf⟩
    · exact hsurj
  -- the per-representative cusp maps (shifted so that the cusp levels match)
  choose Ψ0 hΨ0formula hΨ0loc hΨ0eq hΨ0surj using fun i : Fin m =>
    cuspPsiSpecShift n hAb hId f (cdΓ.hPsub (hξs i)) (cdΛ.hPsub (hFmem (ξs i) (hξs i)))
      (cdΓ.ht (ξs i) - D) (cdΛ.ht (F (ξs i)) - D)
      (Real.exp (cdΛ.ht (F (ξs i)) - cdΓ.ht (ξs i))) (Real.exp_pos _)
      (ψ i) (hψper i).1 (hψper i).2.1 (hψper i).2.2.1
      (fun γ hγ => hFstab (ξs i) (hξs i) γ hγ) (hlevξ1 i) (hlevη1 i) (hψper i).2.2.2 3
  -- the shift of the i-th representative, and its inverse
  set lam : Fin m → ℝ := fun i => Real.exp (cdΛ.ht (F (ξs i)) - cdΓ.ht (ξs i)) with hlamdef
  have hlampos : ∀ i : Fin m, 0 < lam i := fun i => Real.exp_pos _
  have hlevD : ∀ i : Fin m, ∀ u : E n, u ∈ {v : E n | lev (ξs i) v ≤ Real.exp (cdΓ.ht (ξs i) - D)} ↔
      lev (ξs i) u ≤ Real.exp (cdΓ.ht (ξs i) - D) := fun i u => Iff.rfl
  -- the representative cusp regions
  let C0 : Fin m → Set (E n) := fun i => {z : E n | lev (ξs i) z < Real.exp (cdΓ.ht (ξs i) - D)}
  -- the Γ-cusp regions, DEFINED by transporting the representative's
  let Cξ : (ξ : E n) → ξ ∈ cdΓ.P → Set (E n) := fun ξ hξ =>
    (fun z => ((γr ξ hξ : Γ) : PO n 1) • z) '' (C0 (irep ξ hξ))
  -- the transported cusp map
  let Ψξ : (ξ : E n) → ξ ∈ cdΓ.P → E n → E n := fun ξ hξ u =>
    ((f (γr ξ hξ) : Λ) : PO n 1) • (Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • u))
  -- constants
  choose C0i hC0i using hΨ0loc
  have hC0i' : ∀ i : Fin m, ∀ u v : E n, lev (ξs i) u ≤ Real.exp (cdΓ.ht (ξs i) - D) →
      lev (ξs i) v ≤ Real.exp (cdΓ.ht (ξs i) - D) → hdist u v ≤ 3 →
      hdist (Ψ0 i u) (Ψ0 i v) ≤ C0i i := hC0i
  have hC0i_le : ∀ i : Fin m, max (C0i i) 0 ≤ ∑ j, max (C0i j) 0 := by
    intro i
    exact Finset.single_le_sum (f := fun j : Fin m => max (C0i j) 0)
        (fun j _ => real_le_max_right _ _) (Finset.mem_univ i)
  -- (A) the transport is coarsely Lipschitz on each cusp, uniformly
  have hΨξloc : ∀ ξ (hξ : ξ ∈ cdΓ.P) (u v : E n), u ∈ Cξ ξ hξ → v ∈ Cξ ξ hξ →
      hdist u v ≤ 3 → hdist (Ψξ ξ hξ u) (Ψξ ξ hξ v) ≤ ∑ j, max (C0i j) 0 := by
    intro ξ hξ u v hu hv huv
    obtain ⟨z, hz, hzu⟩ := hu
    obtain ⟨z', hz', hzv⟩ := hv
    have hzu' : ((γr ξ hξ : Γ) : PO n 1) • z = u := hzu
    have hzv' : ((γr ξ hξ : Γ) : PO n 1) • z' = v := hzv
    have hzz' : hdist z z' ≤ 3 := by
      rw [← hId.isom_smul ((γr ξ hξ : Γ) : PO n 1) z z', hzu', hzv']
      exact huv
    have hΨu : Ψξ ξ hξ u = ((f (γr ξ hξ) : Λ) : PO n 1) • Ψ0 (irep ξ hξ) z := by
      rw [← hzu']
      exact congrArg (fun w => ((f (γr ξ hξ) : Λ) : PO n 1) • Ψ0 (irep ξ hξ) w)
        (by rw [Subgroup.coe_inv]; exact smul_inv_smul_cancel hAb _ z)
    have hΨv : Ψξ ξ hξ v = ((f (γr ξ hξ) : Λ) : PO n 1) • Ψ0 (irep ξ hξ) z' := by
      rw [← hzv']
      exact congrArg (fun w => ((f (γr ξ hξ) : Λ) : PO n 1) • Ψ0 (irep ξ hξ) w)
        (by rw [Subgroup.coe_inv]; exact smul_inv_smul_cancel hAb _ z')
    rw [hΨu, hΨv, hId.isom_smul]
    exact le_trans (hC0i' (irep ξ hξ) z z' (le_of_lt hz) (le_of_lt hz') hzz')
      (le_trans (real_le_max_left _ _) (hC0i_le _))
  -- the Λ-cusp regions
  let CΛ : E n → Set (E n) := fun η => {w : E n | lev η w < Real.exp (cdΛ.ht η - D)}
  have hCΛsub : ∀ (m : Λ) (η : E n), η ∈ cdΛ.P → ∀ w ∈ CΛ η,
      (m : PO n 1) • w ∈ CΛ (bd (m : PO n 1) η) := by
    intro m η hη w hw
    have hsh := cdΛ.busemann_shift hAb hId hη m w
    have hw' : busemann η w < cdΛ.ht η - D := by
      have h2 : Real.exp (busemann η w) < Real.exp (cdΛ.ht η - D) := by
        rwa [← lev_eq_exp (cdΛ.hPsub hη) w]
      exact Real.exp_lt_exp.mp h2
    simp only [CΛ, Set.mem_ofPred_eq]
    rw [lev_eq_exp (cdΛ.hPsub (cdΛ.hPinv m η hη)) _]
    refine Real.exp_lt_exp.mpr ?_
    rw [hsh]
    linarith
  -- the image of the transported cusp map lies in the Λ-cusp at `F ξ`
  have hΨξimg : ∀ ξ (hξ : ξ ∈ cdΓ.P), ∀ u ∈ Cξ ξ hξ, Ψξ ξ hξ u ∈ CΛ (F ξ) := by
    intro ξ hξ u hu
    obtain ⟨z, hz, hzu⟩ := hu
    have hzu' : ((γr ξ hξ : Γ) : PO n 1) • z = u := hzu
    have hΨu : Ψξ ξ hξ u = ((f (γr ξ hξ) : Λ) : PO n 1) • Ψ0 (irep ξ hξ) z := by
      rw [← hzu']
      exact congrArg (fun w => ((f (γr ξ hξ) : Λ) : PO n 1) • Ψ0 (irep ξ hξ) w)
        (by rw [Subgroup.coe_inv]; exact smul_inv_smul_cancel hAb _ z)
    have hzC : Ψ0 (irep ξ hξ) z ∈ CΛ (F (ξs (irep ξ hξ))) := by
      have hDpos : 0 < lam (irep ξ hξ) * lev (ξs (irep ξ hξ)) z :=
        mul_pos (hlampos _) (lev_pos _ (cdΓ.hPsub (hξs _)) z)
      have hlev : lev (F (ξs (irep ξ hξ))) (hptOf (F (ξs (irep ξ hξ)))
            (ψ (irep ξ hξ) (yc (ξs (irep ξ hξ)) z))
            (lam (irep ξ hξ) * lev (ξs (irep ξ hξ)) z))
          = lam (irep ξ hξ) * lev (ξs (irep ξ hξ)) z :=
        (hptOfLevelYc (F (ξs (irep ξ hξ)))
          (cdΛ.hPsub (hFmem (ξs (irep ξ hξ)) (hξs (irep ξ hξ))))
          ((hψper (irep ξ hξ)).1 (yc (ξs (irep ξ hξ)) z)
            (yc_orth (cdΓ.hPsub (hξs (irep ξ hξ))))) hDpos).1
      change lev (F (ξs (irep ξ hξ))) (Ψ0 (irep ξ hξ) z)
        < Real.exp (cdΛ.ht (F (ξs (irep ξ hξ))) - D)
      rw [hΨ0formula (irep ξ hξ) z, hlev]
      have h1 : lev (ξs (irep ξ hξ)) z < Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D) := hz
      calc Real.exp (cdΛ.ht (F (ξs (irep ξ hξ))) - cdΓ.ht (ξs (irep ξ hξ))) *
              lev (ξs (irep ξ hξ)) z
          < Real.exp (cdΛ.ht (F (ξs (irep ξ hξ))) - cdΓ.ht (ξs (irep ξ hξ))) *
              Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D) :=
            mul_lt_mul_of_pos_left h1 (Real.exp_pos _)
        _ = Real.exp (cdΛ.ht (F (ξs (irep ξ hξ))) - D) := by
            rw [← Real.exp_add]; ring_nf
    have hmem := hCΛsub (f (γr ξ hξ)) (F (ξs (irep ξ hξ)))
      (hFmem (ξs (irep ξ hξ)) (hξs (irep ξ hξ))) _ hzC
    have h2 : bd ((f (γr ξ hξ) : Λ) : PO n 1) (F (ξs (irep ξ hξ))) = F ξ := by
      rw [← hFeq (ξs (irep ξ hξ)) (hξs (irep ξ hξ)) (γr ξ hξ), hγr ξ hξ]
    rw [hΨu]
    rwa [h2] at hmem
  -- composition of the "smul image" operations
  have hsmul_img : ∀ (g h : PO n 1) (S : Set (E n)),
      (fun z => g • z) '' ((fun z => h • z) '' S) = (fun z => (g * h) • z) '' S := by
    intro g h S
    ext w
    constructor
    · rintro ⟨y, ⟨z, hz, hyz⟩, hyw⟩
      have hyz' : h • z = y := hyz
      have hyw' : g • y = w := hyw
      exact ⟨z, hz, by show (g * h) • z = w; rw [hAb.mul_smul, hyz', hyw']⟩
    · rintro ⟨z, hz, hzw⟩
      have hzw' : (g * h) • z = w := hzw
      exact ⟨h • z, ⟨z, hz, rfl⟩, by show g • (h • z) = w; rw [← hAb.mul_smul, hzw']⟩
  -- the conjugate element and its two basic properties
  have hρ_coe : ∀ ξ (hξ : ξ ∈ cdΓ.P) (γ : Γ),
      (((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1)
        = ((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ) : Γ) : PO n 1)⁻¹
            * ((γ : PO n 1) * ((γr ξ hξ : Γ) : PO n 1)) := by
    intro ξ hξ γ
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hρfix : ∀ ξ (hξ : ξ ∈ cdΓ.P) (γ : Γ),
      bd (((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1)
          (ξs (irep ξ hξ)) = ξs (irep ξ hξ) := by
    intro ξ hξ γ
    set a : PO n 1 := ((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ) : Γ) : PO n 1) with ha
    set r : PO n 1 := ((((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ)) : PO n 1) with hr
    have hcoe : r = a⁻¹ * ((γ : PO n 1) * ((γr ξ hξ : Γ) : PO n 1)) := by
      rw [hr, ha]
      exact hρ_coe ξ hξ γ
    have h1 : bd r (ξs (irep ξ hξ))
        = bd a⁻¹ (bd (γ : PO n 1) (bd ((γr ξ hξ : Γ) : PO n 1) (ξs (irep ξ hξ)))) := by
      rw [hcoe, hAb.bd_mul a⁻¹ ((γ : PO n 1) * ((γr ξ hξ : Γ) : PO n 1)) (ξs (irep ξ hξ))
          (cdΓ.hPsub (hξs (irep ξ hξ))),
        hAb.bd_mul (γ : PO n 1) ((γr ξ hξ : Γ) : PO n 1) (ξs (irep ξ hξ))
          (cdΓ.hPsub (hξs (irep ξ hξ)))]
    rw [h1, hγr ξ hξ]
    have h2 : bd (γ : PO n 1) ξ
        = bd a (ξs (irep (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))) := by
      rw [ha, hγr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ)]
    rw [h2, hirepinv γ ξ hξ]
    exact bd_inv_bd_cuspCorr hAb (cdΓ.hPsub (hξs (irep ξ hξ)))
  have hlevρ : ∀ ξ (hξ : ξ ∈ cdΓ.P) (γ : Γ) (u : E n),
      lev (ξs (irep ξ hξ))
        ((((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1) • u)
        = lev (ξs (irep ξ hξ)) u := by
    intro ξ hξ γ u
    have hb := cuspStab_busemann hId (Γ := Γ) (P := cdΓ.P) (ht := cdΓ.ht) cdΓ.hHeq
      (cdΓ.hPsub (hξs (irep ξ hξ))) (hξs (irep ξ hξ))
      ((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ) (hρfix ξ hξ γ)
    rw [lev_eq_exp (cdΓ.hPsub (hξs (irep ξ hξ))) _,
      lev_eq_exp (cdΓ.hPsub (hξs (irep ξ hξ))) u, hb u]
  -- (2) the family of cusp regions is Γ-invariant
  have hCξinv : ∀ ξ (hξ : ξ ∈ cdΓ.P) (γ : Γ),
      (fun z => (γ : PO n 1) • z) '' (Cξ ξ hξ)
        = Cξ (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ) := by
    intro ξ hξ γ
    have hC0ρ : (fun z => (((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1) • z) ''
        (C0 (irep ξ hξ)) = C0 (irep ξ hξ) := by
      have hsub : ∀ w : E n, w ∈ C0 (irep ξ hξ) →
          (((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1) • w
            ∈ C0 (irep ξ hξ) := by
        intro w hw
        change lev (ξs (irep ξ hξ)) w < Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D) at hw
        change lev (ξs (irep ξ hξ))
          ((((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1) • w)
          < Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D)
        rwa [hlevρ ξ hξ γ w]
      have hsub' : ∀ w : E n, w ∈ C0 (irep ξ hξ) →
          (((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1)⁻¹ • w
            ∈ C0 (irep ξ hξ) := by
        intro w hw
        change lev (ξs (irep ξ hξ)) w < Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D) at hw
        change lev (ξs (irep ξ hξ))
          ((((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1)⁻¹ • w)
          < Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D)
        rw [← hlevρ ξ hξ γ ((((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1)⁻¹ • w),
          smul_smul_inv_cancel hAb]
        exact hw
      ext w
      constructor
      · rintro ⟨y, hy, hyw⟩
        have hyw' : (((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1) • y = w := hyw
        rw [← hyw']
        exact hsub y hy
      · intro hw
        refine ⟨(((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1)⁻¹ • w,
          hsub' w hw, ?_⟩
        show (((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1) •
          ((((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ) : PO n 1)⁻¹ • w) = w
        rw [smul_smul_inv_cancel hAb]
    have hprod : ((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ) : Γ) : PO n 1)
        * ((((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ)) : PO n 1)
        = (γ : PO n 1) * ((γr ξ hξ : Γ) : PO n 1) := by
      rw [hρ_coe ξ hξ γ]
      group
    change (fun z => (γ : PO n 1) • z) ''
        ((fun z => ((γr ξ hξ : Γ) : PO n 1) • z) '' C0 (irep ξ hξ)) = _
    rw [hsmul_img (γ : PO n 1) ((γr ξ hξ : Γ) : PO n 1), ← hprod,
      ← hsmul_img (((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ) : Γ) : PO n 1))
        ((((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))⁻¹ * γ * γr ξ hξ : Γ)) : PO n 1)
        (C0 (irep ξ hξ)), hC0ρ]
    change _ = (fun z => ((γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ) : Γ) : PO n 1) • z) ''
        (C0 (irep (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ)))
    rw [hirepinv γ ξ hξ]
  -- the per-representative equivariance constants
  choose Cφi hCφi using hΨ0eq
  have hCφi_le : ∀ i : Fin m, max (Cφi i) 0 ≤ ∑ j, max (Cφi j) 0 := by
    intro i
    exact Finset.single_le_sum (f := fun j : Fin m => max (Cφi j) 0)
      (fun j _ => real_le_max_right _ _) (Finset.mem_univ i)
  -- (3) the transport is coarsely f-equivariant, uniformly in ξ
  have hΨξeq : ∀ ξ (hξ : ξ ∈ cdΓ.P) (γ : Γ) (u : E n), u ∈ Cξ ξ hξ →
      hdist (Ψξ (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ) ((γ : PO n 1) • u))
        (((f γ : Λ) : PO n 1) • Ψξ ξ hξ u) ≤ ∑ j, max (Cφi j) 0 := by
    intro ξ hξ γ u hu
    obtain ⟨z, hz, hzu⟩ := hu
    have hzu' : ((γr ξ hξ : Γ) : PO n 1) • z = u := hzu
    set a : Γ := γr (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ) with ha
    set ρ : Γ := a⁻¹ * γ * γr ξ hξ with hρ
    have hρbd : bd ((ρ : Γ) : PO n 1) (ξs (irep ξ hξ)) = ξs (irep ξ hξ) := by
      simpa only [hρ, ha] using hρfix ξ hξ γ
    have h1 : Ψξ ξ hξ u = ((f (γr ξ hξ) : Λ) : PO n 1) • Ψ0 (irep ξ hξ) z := by
      have hzz : (((γr ξ hξ : Γ) : PO n 1))⁻¹ • (((γr ξ hξ : Γ) : PO n 1) • z) = z :=
        smul_inv_smul_cancel hAb _ z
      rw [← hzu']
      exact congrArg (fun w => ((f (γr ξ hξ) : Λ) : PO n 1) • Ψ0 (irep ξ hξ) w) hzz
    have hact : (((a : Γ)) : PO n 1)⁻¹ • ((γ : PO n 1) • u) = ((ρ : Γ) : PO n 1) • z := by
      rw [← hzu', hρ, ha]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hAb.mul_smul, ← hAb.mul_smul]
    have h2 : Ψξ (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ) ((γ : PO n 1) • u)
        = ((f a : Λ) : PO n 1) • Ψ0 (irep ξ hξ) (((ρ : Γ) : PO n 1) • z) := by
      show ((f a : Λ) : PO n 1) • Ψ0 (irep (bd (γ : PO n 1) ξ) (cdΓ.hPinv γ ξ hξ))
          ((((a : Γ)) : PO n 1)⁻¹ • ((γ : PO n 1) • u)) = _
      rw [hirepinv γ ξ hξ, hact]
    have hg : (((f γ : Λ)) : PO n 1) * ((f (γr ξ hξ) : Λ) : PO n 1)
        = ((f a : Λ) : PO n 1) * ((f ρ : Λ) : PO n 1) := by
      have hg' : (f γ : Λ) * f (γr ξ hξ) = f a * f ρ := by
        rw [← map_mul, ← map_mul]
        congr 1
        rw [hρ, ha]
        group
      have hcong := congrArg (fun x : Λ => (x : PO n 1)) hg'
      simpa only [Subgroup.coe_mul] using hcong
    rw [h1, h2, ← hAb.mul_smul, hg, hAb.mul_smul,
      hId.isom_smul ((f a : Λ) : PO n 1) (Ψ0 (irep ξ hξ) (((ρ : Γ) : PO n 1) • z))
        (((f ρ : Λ) : PO n 1) • Ψ0 (irep ξ hξ) z)]
    exact le_trans (le_trans (hCφi (irep ξ hξ) ρ hρbd z (le_of_lt hz)) (real_le_max_left _ _))
      (hCφi_le _)
  -- (4) the Γ-cusp regions are exactly the level-cut sub-horoballs, hence sit in the collar
  have hCξ_lt : ∀ ξ (hξ : ξ ∈ cdΓ.P) (u : E n), u ∈ Cξ ξ hξ →
      busemann ξ u < cdΓ.ht ξ - D := by
    intro ξ hξ u hu
    obtain ⟨z, hz, hzu⟩ := hu
    have hzu' : ((γr ξ hξ : Γ) : PO n 1) • z = u := hzu
    have hz' : busemann (ξs (irep ξ hξ)) z < cdΓ.ht (ξs (irep ξ hξ)) - D := by
      have h2 : lev (ξs (irep ξ hξ)) z < Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D) := hz
      rw [lev_eq_exp (cdΓ.hPsub (hξs (irep ξ hξ))) z] at h2
      exact Real.exp_lt_exp.mp h2
    have hsub : busemann ξ (((γr ξ hξ : Γ) : PO n 1) • z)
        = busemann (ξs (irep ξ hξ)) z + (cdΓ.ht ξ - cdΓ.ht (ξs (irep ξ hξ))) := by
      have h := cdΓ.busemann_shift hAb hId (hξs (irep ξ hξ)) (γr ξ hξ) z
      rw [hγr ξ hξ] at h
      exact h
    rw [← hzu', hsub]
    linarith
  have hCξ_gt : ∀ ξ (hξ : ξ ∈ cdΓ.P) (u : E n), busemann ξ u < cdΓ.ht ξ - D →
      u ∈ Cξ ξ hξ := by
    intro ξ hξ u hu
    have hbdi : bd (((γr ξ hξ)⁻¹ : Γ) : PO n 1) ξ = ξs (irep ξ hξ) := by
      have h := bd_inv_bd_cuspCorr hAb (cdΓ.hPsub (hξs (irep ξ hξ))) (g := (((γr ξ hξ : Γ)) : PO n 1))
      rw [hγr ξ hξ] at h
      rw [Subgroup.coe_inv]
      exact h
    have hsub : busemann (ξs (irep ξ hξ)) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • u)
        = busemann ξ u + (cdΓ.ht (ξs (irep ξ hξ)) - cdΓ.ht ξ) := by
      have h := cdΓ.busemann_shift hAb hId hξ (((γr ξ hξ)⁻¹ : Γ)) u
      rw [hbdi] at h
      exact h
    refine ⟨((((γr ξ hξ)⁻¹ : Γ) : PO n 1)) • u, ?_, ?_⟩
    · have h2 : lev (ξs (irep ξ hξ)) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • u)
          < Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D) := by
        rw [lev_eq_exp (cdΓ.hPsub (hξs (irep ξ hξ)))]
        refine Real.exp_lt_exp.mpr ?_
        rw [hsub]
        linarith
      exact h2
    · exact subgroup_inv_smul' hAb (γr ξ hξ) u
  have hHoro_other : ∀ ξ (hξ : ξ ∈ cdΓ.P) (v : E n), v ∈ horoball ξ (cdΓ.ht ξ) →
      ∀ ξ' (hξ' : ξ' ∈ cdΓ.P), ξ' ≠ ξ → cdΓ.ht ξ' - D ≤ busemann ξ' v := by
    intro ξ hξ v hv ξ' hξ' hne
    have hdis := cdΓ.hdisj hξ hξ' (fun h => hne h.symm)
    have hni : v ∉ horoball ξ' (cdΓ.ht ξ') := Set.disjoint_left.mp hdis hv
    have hge : cdΓ.ht ξ' ≤ busemann ξ' v := by
      by_contra hlt
      exact hni (by
        simp only [horoball, Set.mem_ofPred_eq]
        exact not_le.mp hlt)
    linarith
  have hCξ_other : ∀ ξ (hξ : ξ ∈ cdΓ.P) (u : E n), u ∈ Cξ ξ hξ →
      ∀ ξ' (hξ' : ξ' ∈ cdΓ.P), ξ' ≠ ξ → cdΓ.ht ξ' - D ≤ busemann ξ' u := by
    intro ξ hξ u hu ξ' hξ' hne
    have hmem : u ∈ horoball ξ (cdΓ.ht ξ) := by
      simp only [horoball, Set.mem_ofPred_eq]
      linarith [hCξ_lt ξ hξ u hu]
    exact hHoro_other ξ hξ u hmem ξ' hξ' hne
  have hfootY : ∀ ξ (hξ : ξ ∈ cdΓ.P) (u : E n), u ∈ Cξ ξ hξ →
      hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D)) ∈ YΓ := by
    intro ξ hξ u hu
    have hDp : 0 < Real.exp (cdΓ.ht ξ - D) := Real.exp_pos _
    have hbus : busemann ξ (hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D)))
        = cdΓ.ht ξ - D := by
      rw [(hptOfLevelYc ξ (cdΓ.hPsub hξ) (yc_orth (cdΓ.hPsub hξ)) hDp).2.2, Real.log_exp]
    have hmem : hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D)) ∈ horoball ξ (cdΓ.ht ξ) := by
      simp only [horoball, Set.mem_ofPred_eq]
      rw [hbus]
      linarith
    rw [hYΓdef]
    intro ξ' hξ'
    by_cases hEq : ξ' = ξ
    · rw [hEq, hbus]
    · exact hHoro_other ξ hξ _ hmem ξ' hξ' hEq
  have hfootDist : ∀ ξ (hξ : ξ ∈ cdΓ.P) (u : E n), u ∈ Cξ ξ hξ →
      hdist u (hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D)))
        = (cdΓ.ht ξ - D) - busemann ξ u := by
    intro ξ hξ u hu
    have hDp : 0 < Real.exp (cdΓ.ht ξ - D) := Real.exp_pos _
    have hle : lev ξ u ≤ Real.exp (cdΓ.ht ξ - D) := by
      rw [lev_eq_exp (cdΓ.hPsub hξ) u]
      exact Real.exp_le_exp.mpr (le_of_lt (hCξ_lt ξ hξ u hu))
    have hlog : Real.log (lev ξ u) = busemann ξ u := by
      rw [lev_eq_exp (cdΓ.hPsub hξ) u, Real.log_exp]
    rw [hdist_hptOf_foot hId (cdΓ.hPsub hξ) u hDp hle, Real.log_exp, hlog]
  have hCξ_unique : ∀ ξ (hξ : ξ ∈ cdΓ.P) (ζ : E n) (hζ : ζ ∈ cdΓ.P) (u : E n),
      u ∈ Cξ ξ hξ → u ∈ Cξ ζ hζ → ξ = ζ := by
    intro ξ hξ ζ hζ u hu hu'
    by_contra hne
    have hdis := cdΓ.hdisj hξ hζ hne
    have h1 : u ∈ horoball ξ (cdΓ.ht ξ) := by
      simp only [horoball, Set.mem_setOf_eq]
      linarith [hCξ_lt ξ hξ u hu]
    have h2 : u ∈ horoball ζ (cdΓ.ht ζ) := by
      simp only [horoball, Set.mem_setOf_eq]
      linarith [hCξ_lt ζ hζ u hu']
    exact (Set.disjoint_left.mp hdis h1) h2
  have hexCusp : ∀ u : E n, u ∉ YΓ →
      ∃ ξ : E n, ξ ∈ cdΓ.P ∧ busemann ξ u < cdΓ.ht ξ - D := by
    intro u hu
    have hu' : ¬ (∀ ξ ∈ cdΓ.P, cdΓ.ht ξ - D ≤ busemann ξ u) := by
      intro h
      exact hu (by rw [hYΓdef]; exact h)
    push_neg at hu'
    exact hu'
  -- (5) the closed-cusp local bound, the clamp (a `hdist`-nonexpanding retraction onto the
  -- closed cusp) and the resulting global coarse-Lipschitz bound for the cusp map
  have hlogmin : ∀ {a b : ℝ}, 0 < a → 0 < b →
      Real.log (min a b) = min (Real.log a) (Real.log b) := by
    intro a b ha hb
    rcases le_total a b with h | h
    · rw [min_eq_left h, min_eq_left (Real.log_le_log ha h)]
    · rw [min_eq_right h, min_eq_right (Real.log_le_log hb h)]
  have hclampId : ∀ ξ (hξ : ξ ∈ cdΓ.P) (w : E n), lev ξ w ≤ Real.exp (cdΓ.ht ξ - D) →
      hptOf ξ (yc ξ w) (min (lev ξ w) (Real.exp (cdΓ.ht ξ - D))) = w := by
    intro ξ hξ w hw
    refine hptOf_yc ξ (cdΓ.hPsub hξ) (min (lev ξ w) (Real.exp (cdΓ.ht ξ - D))) ?_ w ?_
    · exact lt_min (lev_pos ξ (cdΓ.hPsub hξ) w) (Real.exp_pos _)
    · exact (min_eq_left hw).symm
  have hclampLip : ∀ ξ (hξ : ξ ∈ cdΓ.P) (x y : E n),
      hdist (hptOf ξ (yc ξ x) (min (lev ξ x) (Real.exp (cdΓ.ht ξ - D))))
        (hptOf ξ (yc ξ y) (min (lev ξ y) (Real.exp (cdΓ.ht ξ - D)))) ≤ hdist x y := by
    intro ξ hξ x y
    have hξS : ξ ∈ Sph n := cdΓ.hPsub hξ
    have hTpos : 0 < Real.exp (cdΓ.ht ξ - D) := Real.exp_pos _
    have hDxpos : 0 < min (lev ξ x) (Real.exp (cdΓ.ht ξ - D)) :=
      lt_min (lev_pos ξ hξS x) hTpos
    have hDypos : 0 < min (lev ξ y) (Real.exp (cdΓ.ht ξ - D)) :=
      lt_min (lev_pos ξ hξS y) hTpos
    have h1 := levYcFormula hξS
      (hptOf ξ (yc ξ x) (min (lev ξ x) (Real.exp (cdΓ.ht ξ - D))))
      (hptOf ξ (yc ξ y) (min (lev ξ y) (Real.exp (cdΓ.ht ξ - D))))
    rw [(hptOfLevelYc ξ hξS (yc_orth hξS) hDxpos).1,
      (hptOfLevelYc ξ hξS (yc_orth hξS) hDypos).1,
      (hptOfLevelYc ξ hξS (yc_orth hξS) hDxpos).2.1,
      (hptOfLevelYc ξ hξS (yc_orth hξS) hDypos).2.1] at h1
    have h2 := levYcFormula hξS x y
    have hkey : |Real.log (min (lev ξ x) (Real.exp (cdΓ.ht ξ - D)))
        - Real.log (min (lev ξ y) (Real.exp (cdΓ.ht ξ - D)))|
        ≤ |Real.log (lev ξ x) - Real.log (lev ξ y)| := by
      rw [hlogmin (a := lev ξ x) (b := Real.exp (cdΓ.ht ξ - D)) (lev_pos ξ hξS x) hTpos,
        hlogmin (a := lev ξ y) (b := Real.exp (cdΓ.ht ξ - D)) (lev_pos ξ hξS y) hTpos]
      have h3 := abs_min_sub_min_le_max (Real.log (lev ξ x))
        (Real.log (Real.exp (cdΓ.ht ξ - D))) (Real.log (lev ξ y))
        (Real.log (Real.exp (cdΓ.ht ξ - D)))
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h3
      exact h3
    have hcosh : Real.cosh (Real.log (min (lev ξ x) (Real.exp (cdΓ.ht ξ - D))
          / min (lev ξ y) (Real.exp (cdΓ.ht ξ - D))))
        ≤ Real.cosh (Real.log (lev ξ x / lev ξ y)) := by
      rw [Real.cosh_le_cosh,
        Real.log_div (ne_of_gt hDxpos) (ne_of_gt hDypos),
        Real.log_div (ne_of_gt (lev_pos ξ hξS x)) (ne_of_gt (lev_pos ξ hξS y))]
      exact hkey
    have hterm : (min (lev ξ x) (Real.exp (cdΓ.ht ξ - D))
          * min (lev ξ y) (Real.exp (cdΓ.ht ξ - D)) / 2) * ‖yc ξ x - yc ξ y‖ ^ 2
        ≤ (lev ξ x * lev ξ y / 2) * ‖yc ξ x - yc ξ y‖ ^ 2 := by
      have hxy : min (lev ξ x) (Real.exp (cdΓ.ht ξ - D))
            * min (lev ξ y) (Real.exp (cdΓ.ht ξ - D)) ≤ lev ξ x * lev ξ y :=
        mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_of_lt hDypos)
          (le_of_lt (lev_pos ξ hξS x))
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    have hfin : Real.cosh (hdist
          (hptOf ξ (yc ξ x) (min (lev ξ x) (Real.exp (cdΓ.ht ξ - D))))
          (hptOf ξ (yc ξ y) (min (lev ξ y) (Real.exp (cdΓ.ht ξ - D)))))
        ≤ Real.cosh (hdist x y) := by
      rw [h1, h2]
      linarith
    have h4 := Real.cosh_le_cosh.mp hfin
    rwa [abs_of_nonneg (hId.nonneg _ _), abs_of_nonneg (hId.nonneg _ _)] at h4
  have hΨξlocC : ∀ ξ (hξ : ξ ∈ cdΓ.P) (u v : E n),
      lev ξ u ≤ Real.exp (cdΓ.ht ξ - D) → lev ξ v ≤ Real.exp (cdΓ.ht ξ - D) →
      hdist u v ≤ 3 → hdist (Ψξ ξ hξ u) (Ψξ ξ hξ v) ≤ ∑ j, max (C0i j) 0 := by
    intro ξ hξ u v hu hv huv
    have hbdi : bd (((γr ξ hξ)⁻¹ : Γ) : PO n 1) ξ = ξs (irep ξ hξ) := by
      have h := bd_inv_bd_cuspCorr hAb (cdΓ.hPsub (hξs (irep ξ hξ))) (g := (((γr ξ hξ : Γ)) : PO n 1))
      rw [hγr ξ hξ] at h
      rw [Subgroup.coe_inv]
      exact h
    have hlevz : ∀ w : E n, lev ξ w ≤ Real.exp (cdΓ.ht ξ - D) →
        lev (ξs (irep ξ hξ)) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)
          ≤ Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D) := by
      intro w hw
      rw [lev_eq_exp (cdΓ.hPsub (hξs (irep ξ hξ))), Real.exp_le_exp]
      have hsh := cdΓ.busemann_shift hAb hId hξ (((γr ξ hξ)⁻¹ : Γ)) w
      rw [hbdi] at hsh
      rw [hsh]
      rw [lev_eq_exp (cdΓ.hPsub hξ) w, Real.exp_le_exp] at hw
      linarith
    have hzz' : hdist ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • u) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • v) ≤ 3 := by
      calc hdist ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • u) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • v)
          = hdist u v := hId.isom_smul _ u v
        _ ≤ 3 := huv
    change hdist (((f (γr ξ hξ) : Λ) : PO n 1) • Ψ0 (irep ξ hξ)
          ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • u))
        (((f (γr ξ hξ) : Λ) : PO n 1) • Ψ0 (irep ξ hξ)
          ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • v)) ≤ _
    rw [hId.isom_smul]
    exact le_trans (hC0i' (irep ξ hξ) _ _ (hlevz u hu) (hlevz v hv) hzz')
      (le_trans (real_le_max_left _ _) (hC0i_le _))
  have hCcusp0 : 0 ≤ ∑ j : Fin m, max (C0i j) 0 :=
    Finset.sum_nonneg (fun j _ => real_le_max_right _ _)
  have hΨξglob : ∀ ξ (hξ : ξ ∈ cdΓ.P) (u v : E n),
      lev ξ u ≤ Real.exp (cdΓ.ht ξ - D) → lev ξ v ≤ Real.exp (cdΓ.ht ξ - D) →
      hdist (Ψξ ξ hξ u) (Ψξ ξ hξ v)
        ≤ (∑ j, max (C0i j) 0) * hdist u v + (∑ j, max (C0i j) 0) := by
    intro ξ hξ u v hu hv
    have hloc : ∀ x y : E n, hdist x y ≤ 1 →
        hdist (Ψξ ξ hξ (hptOf ξ (yc ξ x) (min (lev ξ x) (Real.exp (cdΓ.ht ξ - D)))))
          (Ψξ ξ hξ (hptOf ξ (yc ξ y) (min (lev ξ y) (Real.exp (cdΓ.ht ξ - D)))))
          ≤ ∑ j, max (C0i j) 0 := by
      intro x y hxy
      refine hΨξlocC ξ hξ _ _ ?_ ?_ ?_
      · rw [(hptOfLevelYc ξ (cdΓ.hPsub hξ) (yc_orth (cdΓ.hPsub hξ))
            (lt_min (lev_pos ξ (cdΓ.hPsub hξ) x) (Real.exp_pos _))).1]
        exact min_le_right _ _
      · rw [(hptOfLevelYc ξ (cdΓ.hPsub hξ) (yc_orth (cdΓ.hPsub hξ))
            (lt_min (lev_pos ξ (cdΓ.hPsub hξ) y) (Real.exp_pos _))).1]
        exact min_le_right _ _
      · exact le_trans (hclampLip ξ hξ x y) (le_trans hxy (by norm_num))
    have hres := hdist_map_le hId hCcusp0 hloc u v
    rwa [hclampId ξ hξ u hu, hclampId ξ hξ v hv] at hres
  -- (7) the level sets at the representative cusps are `Γ_ξ`-cocompact, and the two branch
  -- maps are bounded on the compact fundamental sets
  have hlevCont : ∀ i : Fin m, Continuous fun u : E n => lev (ξs i) u := by
    intro i
    change Continuous fun u : E n => tpart u - inner ℝ u (ξs i)
    unfold tpart
    fun_prop
  have hcptLev : ∀ i : Fin m, ∃ K : Set (E n), IsCompact K ∧
      (∀ z ∈ K, lev (ξs i) z = Real.exp (cdΓ.ht (ξs i) - D)) ∧
      ∀ z : E n, lev (ξs i) z = Real.exp (cdΓ.ht (ξs i) - D) →
        ∃ γ : Γ, bd (γ : PO n 1) (ξs i) = ξs i ∧ (γ : PO n 1) • z ∈ K := by
    intro i
    have hτ : ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n, busemann (ξs i) u = cdΓ.ht (ξs i) →
        ∃ γ : Γ, bd (γ : PO n 1) (ξs i) = ξs i ∧ (γ : PO n 1) • u ∈ K :=
      cdΓ.hcpt (ξs i) (hξs i)
    have hcc := cuspCocompactAllLevels n hA hI Γ (ξs i) (cdΓ.hPsub (hξs i))
      (fun γ hγ => hvanΓ γ (ξs i) (hPΓpar (ξs i) (hξs i)) hγ) (cdΓ.ht (ξs i)) hτ
    obtain ⟨K, hKc, hK⟩ := hcc (cdΓ.ht (ξs i) - D)
    refine ⟨K ∩ {z : E n | lev (ξs i) z = Real.exp (cdΓ.ht (ξs i) - D)},
      hKc.inter_right (isClosed_eq (hlevCont i) continuous_const), ?_, ?_⟩
    · intro z hz; exact hz.2
    · intro z hz
      have hb : busemann (ξs i) z = cdΓ.ht (ξs i) - D := by
        have h2 : Real.exp (busemann (ξs i) z) = Real.exp (cdΓ.ht (ξs i) - D) := by
          rw [← lev_eq_exp (cdΓ.hPsub (hξs i)) z, hz]
        exact Real.exp_injective h2
      obtain ⟨γ, hγ, hγz⟩ := hK z hb
      have hlevγ : lev (ξs i) ((γ : PO n 1) • z) = Real.exp (cdΓ.ht (ξs i) - D) := by
        have h1 : busemann (ξs i) ((γ : PO n 1) • z) = busemann (ξs i) z := by
          have hcoc := hId.busemann_cocycle (γ : PO n 1) (ξs i) z (cdΓ.hPsub (hξs i))
          rw [hγ] at hcoc
          have hb0 : busemann (ξs i) ((γ : PO n 1) • (0 : E n)) = 0 := by
            have hb1 := hvanΓ γ (ξs i) (hPΓpar (ξs i) (hξs i)) hγ
            rwa [show bCocy (γ : PO n 1) (ξs i) = busemann (ξs i) ((γ : PO n 1) • (0 : E n))
              from by unfold bCocy; rw [hγ]] at hb1
          rw [hcoc, hb0, add_zero]
        rw [lev_eq_exp (cdΓ.hPsub (hξs i)), h1, ← lev_eq_exp (cdΓ.hPsub (hξs i)) z, hz]
      exact ⟨γ, hγ, hγz, hlevγ⟩
  have hYΓ_of_lev : ∀ ξ (hξ : ξ ∈ cdΓ.P) (z : E n),
      lev ξ z = Real.exp (cdΓ.ht ξ - D) → z ∈ YΓ := by
    intro ξ hξ z hz
    have hbus : busemann ξ z = cdΓ.ht ξ - D := by
      have h2 : Real.exp (busemann ξ z) = Real.exp (cdΓ.ht ξ - D) := by
        rw [← lev_eq_exp (cdΓ.hPsub hξ) z, hz]
      exact Real.exp_injective h2
    have hmem : z ∈ horoball ξ (cdΓ.ht ξ) := by
      simp only [horoball, Set.mem_ofPred_eq]
      rw [hbus]; linarith
    rw [hYΓdef]
    intro ξ' hξ'
    by_cases hEq : ξ' = ξ
    · rw [hEq, hbus]
    · exact hHoro_other ξ hξ z hmem ξ' hξ' hEq
  have hΦTbdd : ∀ K : Set (E n), IsCompact K → K ⊆ YΓ →
      ∃ C : ℝ, ∀ z ∈ K, hdist (0 : E n) (ΦT z) ≤ C := by
    intro K hK hKY
    have hfin : ({s : Γ | ∃ u ∈ Kc, ∃ v ∈ K, ((s : Γ) : PO n 1) • u = v}).Finite :=
      finite_nearStab_compact hAb hId hΓdisc hKcc hK
    refine ⟨(hfin.toFinset).sum (fun s : Γ =>
      max (hdist (0 : E n) (((f s : Λ) : PO n 1) • (0 : E n))) 0), fun z hz => ?_⟩
    have hzKc : (((γof z)⁻¹ : Γ) : PO n 1) • z ∈ Kc := hγofK z (hKY hz)
    have hmem : (γof z) ∈ ({s : Γ | ∃ u ∈ Kc, ∃ v ∈ K, ((s : Γ) : PO n 1) • u = v}) :=
      ⟨(((γof z)⁻¹ : Γ) : PO n 1) • z, hzKc, z, hz, subgroup_inv_smul' hAb (γof z) z⟩
    have hzS : (γof z) ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact hmem
    have h1 : max (hdist (0 : E n) (((f (γof z) : Λ) : PO n 1) • (0 : E n))) 0
        ≤ (hfin.toFinset).sum (fun s : Γ =>
            max (hdist (0 : E n) (((f s : Λ) : PO n 1) • (0 : E n))) 0) :=
      Finset.single_le_sum (f := fun s : Γ =>
          max (hdist (0 : E n) (((f s : Λ) : PO n 1) • (0 : E n))) 0)
        (fun s _ => real_le_max_right _ _) hzS
    show hdist (0 : E n) (((f (γof z) : Λ) : PO n 1) • (0 : E n)) ≤ _
    exact le_trans (real_le_max_left _ _) h1
  have hΨ0glob : ∀ i : Fin m, ∀ u v : E n,
      lev (ξs i) u ≤ Real.exp (cdΓ.ht (ξs i) - D) →
      lev (ξs i) v ≤ Real.exp (cdΓ.ht (ξs i) - D) →
      hdist (Ψ0 i u) (Ψ0 i v)
        ≤ (∑ j, max (C0i j) 0) * hdist u v + (∑ j, max (C0i j) 0) := by
    intro i u v hu hv
    have hξSi : ξs i ∈ Sph n := cdΓ.hPsub (hξs i)
    have hloc : ∀ x y : E n, hdist x y ≤ 1 →
        hdist (Ψ0 i (hptOf (ξs i) (yc (ξs i) x)
            (min (lev (ξs i) x) (Real.exp (cdΓ.ht (ξs i) - D)))))
          (Ψ0 i (hptOf (ξs i) (yc (ξs i) y)
            (min (lev (ξs i) y) (Real.exp (cdΓ.ht (ξs i) - D)))))
          ≤ ∑ j, max (C0i j) 0 := by
      intro x y hxy
      refine le_trans (hC0i' i _ _ ?_ ?_ ?_)
        (le_trans (real_le_max_left _ _) (hC0i_le i))
      · rw [(hptOfLevelYc (ξs i) hξSi (yc_orth hξSi)
            (lt_min (lev_pos (ξs i) hξSi x) (Real.exp_pos _))).1]
        exact min_le_right _ _
      · rw [(hptOfLevelYc (ξs i) hξSi (yc_orth hξSi)
            (lt_min (lev_pos (ξs i) hξSi y) (Real.exp_pos _))).1]
        exact min_le_right _ _
      · exact le_trans (hclampLip (ξs i) (hξs i) x y) (le_trans hxy (by norm_num))
    have hres := hdist_map_le hId hCcusp0 hloc u v
    rwa [hclampId (ξs i) (hξs i) u hu, hclampId (ξs i) (hξs i) v hv] at hres
  -- (8) CONSISTENCY: on the seam (level `ht ξ - D`) the collar map and the cusp map agree up
  -- to a bounded error.  `∂C0 i` is `Γ_{ξs i}`-cocompact, both maps are coarsely equivariant,
  -- and on the compact fundamental set the two sides are bounded by the explicit constants
  -- `Ci` and `P0 i` (the latter via the clamp bound and the fixed reference point at flat
  -- coordinate `0`).
  set P0 : Fin m → ℝ := (fun i => Real.arcosh (Real.sqrt (1 +
      (((1 + (lam i * Real.exp (cdΓ.ht (ξs i) - D)) ^ 2 * ‖ψ i 0‖ ^ 2)
        / (2 * (lam i * Real.exp (cdΓ.ht (ξs i) - D)))
        + (lam i * Real.exp (cdΓ.ht (ξs i) - D)) / 2
        + (lam i * Real.exp (cdΓ.ht (ξs i) - D)) * ‖ψ i 0‖)) ^ 2))) with hP0def
  set B1 : Fin m → ℝ := (fun i => Real.arcosh (Real.sqrt (1 +
      (1 / (2 * Real.exp (cdΓ.ht (ξs i) - D)) + Real.exp (cdΓ.ht (ξs i) - D) / 2) ^ 2))) with hB1def
  have hP0 : ∀ i : Fin m,
      hdist (0 : E n) (Ψ0 i (hptOf (ξs i) 0 (Real.exp (cdΓ.ht (ξs i) - D)))) ≤ P0 i := by
    intro i
    rw [hP0def, hΨ0formula i,
      (hptOfLevelYc (ξs i) (cdΓ.hPsub (hξs i)) (y := 0) (by simp)
        (Real.exp_pos _)).2.1,
      (hptOfLevelYc (ξs i) (cdΓ.hPsub (hξs i)) (y := 0) (by simp)
        (Real.exp_pos _)).1]
    exact hdist_zero_hptOf_le hId (cdΛ.hPsub (hFmem (ξs i) (hξs i)))
      (mul_pos (hlampos i) (Real.exp_pos _))
  have hB1 : ∀ i : Fin m,
      hdist (0 : E n) (hptOf (ξs i) 0 (Real.exp (cdΓ.ht (ξs i) - D))) ≤ B1 i := by
    intro i
    rw [hB1def]
    have h := hdist_zero_hptOf_le hId (cdΓ.hPsub (hξs i)) (y := 0)
      (D := Real.exp (cdΓ.ht (ξs i) - D)) (Real.exp_pos _)
    simpa using h
  have hcons : ∃ C : ℝ, ∀ ξ (hξ : ξ ∈ cdΓ.P), ∀ w : E n,
      lev ξ w = Real.exp (cdΓ.ht ξ - D) → hdist (ΦT w) (Ψξ ξ hξ w) ≤ C := by
    choose Ki hKic hKilev hKicpt using hcptLev
    have hKiY : ∀ i : Fin m, Ki i ⊆ YΓ :=
      fun i z hz => hYΓ_of_lev (ξs i) (hξs i) z (hKilev i z hz)
    choose Ci hCi using fun i : Fin m => hΦTbdd (Ki i) (hKic i) (hKiY i)
    choose Ri hRi using fun i : Fin m => exists_hdist_le_of_isCompact_bundled hId (hKic i)
    have hz1lev : ∀ i : Fin m, lev (ξs i) (hptOf (ξs i) 0 (Real.exp (cdΓ.ht (ξs i) - D)))
        = Real.exp (cdΓ.ht (ξs i) - D) := fun i =>
      (hptOfLevelYc (ξs i) (cdΓ.hPsub (hξs i)) (y := 0) (by simp)
        (Real.exp_pos _)).1
    set cper : Fin m → ℝ := (fun i => CT + (CT + (∑ j, max (Cφi j) 0) + Ci i + P0 i
        + (∑ j, max (C0i j) 0) * (max (Ri i) 0 + B1 i + 1))) with hcper
    refine ⟨∑ i : Fin m, max (cper i) 0, ?_⟩
    intro ξ hξ w hw
    have hwY : w ∈ YΓ := hYΓ_of_lev ξ hξ w hw
    have hbusw : busemann ξ w = cdΓ.ht ξ - D := by
      have h2 : Real.exp (busemann ξ w) = Real.exp (cdΓ.ht ξ - D) := by
        rw [← lev_eq_exp (cdΓ.hPsub hξ) w, hw]
      exact Real.exp_injective h2
    have hbdi : bd (((γr ξ hξ)⁻¹ : Γ) : PO n 1) ξ = ξs (irep ξ hξ) := by
      have h := bd_inv_bd_cuspCorr hAb (cdΓ.hPsub (hξs (irep ξ hξ))) (g := (((γr ξ hξ : Γ)) : PO n 1))
      rw [hγr ξ hξ] at h
      rw [Subgroup.coe_inv]
      exact h
    have hzlev : lev (ξs (irep ξ hξ)) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)
        = Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D) := by
      have hsh := cdΓ.busemann_shift hAb hId hξ (((γr ξ hξ)⁻¹ : Γ)) w
      rw [hbdi] at hsh
      rw [lev_eq_exp (cdΓ.hPsub (hξs (irep ξ hξ))), hsh, hbusw, Real.exp_eq_exp]
      ring
    -- the transported collar point is close to the collar point at the representative
    have hA1 : hdist (ΦT w)
        (((f (γr ξ hξ) : Λ) : PO n 1) • ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)) ≤ CT := by
      have hzY : ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w) ∈ YΓ :=
        cdΓ.collarInv hAb hId ((γr ξ hξ)⁻¹) w hwY
      have h := hΦTeq' (γr ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w) hzY
      rwa [subgroup_inv_smul' hAb (γr ξ hξ) w] at h
    -- the bump function bound at the representative cusp
    have hGb : hdist (ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
        (Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
        ≤ CT + (∑ j, max (Cφi j) 0) + Ci (irep ξ hξ) + P0 (irep ξ hξ)
          + (∑ j, max (C0i j) 0) * (max (Ri (irep ξ hξ)) 0 + B1 (irep ξ hξ) + 1) := by
      obtain ⟨g, hgbd, hgmem⟩ := hKicpt (irep ξ hξ) _ hzlev
      have hzY : ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w) ∈ YΓ :=
        cdΓ.collarInv hAb hId ((γr ξ hξ)⁻¹) w hwY
      have hE1 : hdist (ΦT ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
          (((f g : Λ) : PO n 1) • ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)) ≤ CT :=
        hΦTeq' g _ hzY
      have hE2 : hdist (Ψ0 (irep ξ hξ) ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
          (((f g : Λ) : PO n 1) • Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
          ≤ Cφi (irep ξ hξ) :=
        hCφi (irep ξ hξ) g hgbd _ hzlev.le
      have hE1' : hdist (((f g : Λ) : PO n 1) • ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
          (ΦT ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))) ≤ CT := by
        have h := hE1
        rwa [hd_symm hId (ΦT ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
          (((f g : Λ) : PO n 1) • ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))] at h
      have hGz : hdist (ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
          (Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
          ≤ CT + (hdist (ΦT ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
              (Ψ0 (irep ξ hξ) ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
            + Cφi (irep ξ hξ)) := by
        calc hdist (ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
              (Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
            = hdist (((f g : Λ) : PO n 1) • ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
                (((f g : Λ) : PO n 1) • Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)) :=
              (by rw [hId.isom_smul])
          _ ≤ hdist (((f g : Λ) : PO n 1) • ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
                (ΦT ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
              + hdist (ΦT ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
                (((f g : Λ) : PO n 1) • Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)) :=
              hd_triangle hId _ _ _
          _ ≤ CT + (hdist (ΦT ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
                (Ψ0 (irep ξ hξ) ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
              + Cφi (irep ξ hξ)) :=
              add_le_add hE1' (le_trans (hd_triangle hId (ΦT ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
                  (Ψ0 (irep ξ hξ) ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
                  (((f g : Λ) : PO n 1) • Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
                (add_le_add le_rfl hE2))
      have hC1 : hdist (ΦT ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))) (0 : E n)
          ≤ Ci (irep ξ hξ) := by
        rw [hd_symm hId (ΦT ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))) 0]
        exact hCi _ _ hgmem
      have hC2 : hdist (0 : E n) (Ψ0 (irep ξ hξ) ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
          ≤ P0 (irep ξ hξ) + (∑ j, max (C0i j) 0)
            * (max (Ri (irep ξ hξ)) 0 + B1 (irep ξ hξ) + 1) := by
        have hgl := hΨ0glob (irep ξ hξ)
          (hptOf (ξs (irep ξ hξ)) 0 (Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D)))
          ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)) (hz1lev _).le (hKilev _ _ hgmem).le
        have hRk : hdist (0 : E n) ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
            ≤ max (Ri (irep ξ hξ)) 0 :=
          le_trans (hRi _ _ hgmem) (real_le_max_left _ _)
        have hR1 : hdist (hptOf (ξs (irep ξ hξ)) 0 (Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D))) (0 : E n)
            ≤ B1 (irep ξ hξ) := by
          rw [hd_symm hId (hptOf (ξs (irep ξ hξ)) 0 (Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D))) 0]
          exact hB1 _
        have hd1 : hdist (hptOf (ξs (irep ξ hξ)) 0 (Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D)))
            ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
            ≤ max (Ri (irep ξ hξ)) 0 + B1 (irep ξ hξ) :=
          calc hdist (hptOf (ξs (irep ξ hξ)) 0 (Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D)))
                ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
              ≤ hdist (hptOf (ξs (irep ξ hξ)) 0 (Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D))) 0
                + hdist 0 ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)) :=
                hd_triangle hId _ _ _
            _ ≤ B1 (irep ξ hξ) + max (Ri (irep ξ hξ)) 0 := add_le_add hR1 hRk
            _ = max (Ri (irep ξ hξ)) 0 + B1 (irep ξ hξ) := add_comm _ _
        have htri := hd_triangle hId (0 : E n)
          (Ψ0 (irep ξ hξ) (hptOf (ξs (irep ξ hξ)) 0 (Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D))))
          (Ψ0 (irep ξ hξ) ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
        have hgl2 : hdist (Ψ0 (irep ξ hξ) (hptOf (ξs (irep ξ hξ)) 0 (Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D))))
            (Ψ0 (irep ξ hξ) ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
            ≤ (∑ j, max (C0i j) 0) * (max (Ri (irep ξ hξ)) 0 + B1 (irep ξ hξ) + 1) :=
          calc hdist (Ψ0 (irep ξ hξ) (hptOf (ξs (irep ξ hξ)) 0 (Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D))))
                (Ψ0 (irep ξ hξ) ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
              ≤ (∑ j, max (C0i j) 0) * hdist (hptOf (ξs (irep ξ hξ)) 0 (Real.exp (cdΓ.ht (ξs (irep ξ hξ)) - D)))
                  ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
                + (∑ j, max (C0i j) 0) := hgl
            _ ≤ (∑ j, max (C0i j) 0)
                  * (max (Ri (irep ξ hξ)) 0 + B1 (irep ξ hξ)) + (∑ j, max (C0i j) 0) :=
                add_le_add (mul_le_mul_of_nonneg_left hd1 hCcusp0) le_rfl
            _ = (∑ j, max (C0i j) 0) * (max (Ri (irep ξ hξ)) 0 + B1 (irep ξ hξ) + 1) := by ring
        linarith [htri, hP0 (irep ξ hξ), hgl2]
      have hfin2 := hd_triangle hId (ΦT ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
        (0 : E n) (Ψ0 (irep ξ hξ) ((g : PO n 1) • ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)))
      have h5 : Cφi (irep ξ hξ) ≤ ∑ j, max (Cφi j) 0 :=
        le_trans (real_le_max_left _ _) (hCφi_le _)
      linarith [hGz, hC1, hC2, h5, hfin2, hCcusp0]
    -- the transported cusp point
    have hA2 : hdist (((f (γr ξ hξ) : Λ) : PO n 1) • ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
        (((f (γr ξ hξ) : Λ) : PO n 1) • Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
        = hdist (ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
          (Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)) :=
      hId.isom_smul _ _ _
    have hfinal : hdist (ΦT w) (Ψξ ξ hξ w) ≤ cper (irep ξ hξ) := by
      have hΨeq : Ψξ ξ hξ w
          = ((f (γr ξ hξ) : Λ) : PO n 1) • Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w) := rfl
      calc hdist (ΦT w) (Ψξ ξ hξ w)
          = hdist (ΦT w) (((f (γr ξ hξ) : Λ) : PO n 1)
              • Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)) := by rw [hΨeq]
        _ ≤ hdist (ΦT w) (((f (γr ξ hξ) : Λ) : PO n 1)
              • ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
            + hdist (((f (γr ξ hξ) : Λ) : PO n 1) • ΦT ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w))
              (((f (γr ξ hξ) : Λ) : PO n 1)
                • Ψ0 (irep ξ hξ) ((((γr ξ hξ)⁻¹ : Γ) : PO n 1) • w)) :=
            hd_triangle hId _ _ _
        _ ≤ CT + (CT + (∑ j, max (Cφi j) 0) + Ci (irep ξ hξ) + P0 (irep ξ hξ)
              + (∑ j, max (C0i j) 0) * (max (Ri (irep ξ hξ)) 0 + B1 (irep ξ hξ) + 1)) := by
            rw [hA2]
            exact add_le_add hA1 hGb
        _ = cper (irep ξ hξ) := rfl
    have h6 : cper (irep ξ hξ) ≤ ∑ i : Fin m, max (cper i) 0 :=
      le_trans (real_le_max_left _ _)
        (Finset.single_le_sum (f := fun i : Fin m => max (cper i) 0)
          (fun i _ => real_le_max_right _ _) (Finset.mem_univ (irep ξ hξ)))
    exact le_trans hfinal h6
  obtain ⟨Ccons0, hcons0⟩ := hcons
  set Ccons : ℝ := max Ccons0 0 with hCconsdef
  have hCcons : 0 ≤ Ccons := by rw [hCconsdef]; exact real_le_max_right _ _
  have hcons' : ∀ ξ (hξ : ξ ∈ cdΓ.P) (w : E n),
      lev ξ w = Real.exp (cdΓ.ht ξ - D) → hdist (ΦT w) (Ψξ ξ hξ w) ≤ Ccons := by
    intro ξ hξ w hw
    rw [hCconsdef]
    exact le_trans (hcons0 ξ hξ w hw) (real_le_max_left _ _)
  -- (9) the map `Φ`: the collar orbit map outside the shrunken cusps, the transported cusp map
  -- inside one of them
  have hexCuspAll : ∀ u : E n, ∃ ξ : E n,
      (ξ ∈ cdΓ.P ∧ busemann ξ u < cdΓ.ht ξ - D) ∨ u ∈ YΓ := by
    intro u
    by_cases hu : u ∈ YΓ
    · exact ⟨0, Or.inr hu⟩
    · obtain ⟨ξ, hξ⟩ := hexCusp u hu
      exact ⟨ξ, Or.inl hξ⟩
  let ξof : E n → E n := fun u => (hexCuspAll u).choose
  have hξof : ∀ u : E n,
      (ξof u ∈ cdΓ.P ∧ busemann (ξof u) u < cdΓ.ht (ξof u) - D) ∨ u ∈ YΓ :=
    fun u => (hexCuspAll u).choose_spec
  have hξofP : ∀ u (hu : u ∉ YΓ), ξof u ∈ cdΓ.P :=
    fun u hu => ((hξof u).resolve_right hu).1
  have hξofLt : ∀ u (hu : u ∉ YΓ), busemann (ξof u) u < cdΓ.ht (ξof u) - D :=
    fun u hu => ((hξof u).resolve_right hu).2
  let Φ : E n → E n :=
    fun u => if hu : u ∈ YΓ then ΦT u else Ψξ (ξof u) (hξofP u hu) u
  have hΦY : ∀ u (hu : u ∈ YΓ), Φ u = ΦT u := fun u hu => dif_pos hu
  have hΦc : ∀ u (hu : u ∉ YΓ), Φ u = Ψξ (ξof u) (hξofP u hu) u := fun u hu => dif_neg hu
  -- the two maps agree up to a congruence of the cusp parameter
  have hΨξcongr : ∀ (ξ ξ' : E n) (h : ξ = ξ') (hξ : ξ ∈ cdΓ.P) (hξ' : ξ' ∈ cdΓ.P) (w : E n),
      Ψξ ξ hξ w = Ψξ ξ' hξ' w := by
    intro ξ ξ' h hξ hξ' w
    subst h
    exact congrArg (fun hh : ξ ∈ cdΓ.P => Ψξ ξ hh w) (Subsingleton.elim hξ hξ')
  -- distinct cusps are separated
  have hCuspSep : ∀ ξ (hξ : ξ ∈ cdΓ.P) (ζ : E n) (hζ : ζ ∈ cdΓ.P) (u v : E n),
      u ∈ Cξ ξ hξ → v ∈ Cξ ζ hζ → ξ ≠ ζ → 2 ≤ hdist u v := by
    intro ξ hξ ζ hζ u v hu hv hne
    have hbu : cdΓ.ht ζ ≤ busemann ζ u := by
      have h2 : u ∈ horoball ξ (cdΓ.ht ξ) := by
        simp only [horoball, Set.mem_ofPred_eq]; linarith [hCξ_lt ξ hξ u hu]
      have h1 : u ∉ horoball ζ (cdΓ.ht ζ) := Set.disjoint_left.mp (cdΓ.hdisj hξ hζ hne) h2
      by_contra hcon
      exact h1 (by simp only [horoball, Set.mem_ofPred_eq]; exact not_le.mp hcon)
    have hbv : busemann ζ v < cdΓ.ht ζ - D := hCξ_lt ζ hζ v hv
    have hlip : busemann ζ u - busemann ζ v ≤ hdist u v :=
      le_trans (le_abs_self _) (busemann_lipschitz' hId (cdΓ.hPsub hζ) u v)
    linarith
  have hΦloc1 : ∀ u v : E n, hdist u v ≤ 1 →
      hdist (Φ u) (Φ v) ≤ CT + Ccons + (∑ j, max (C0i j) 0) + CT := by
    intro u v huv
    have huv' : hdist v u ≤ 1 := by rw [hd_symm hId v u]; exact huv
    by_cases hu : u ∈ YΓ
    · by_cases hv : v ∈ YΓ
      · -- both in the collar
        rw [hΦY u hu, hΦY v hv]
        have h1 := hΦTloc' u hu v hv (le_trans huv (by norm_num))
        linarith [hCT0]
      · -- the seam, `u` in the collar
        have hvP : ξof v ∈ cdΓ.P := hξofP v hv
        have hvLt : busemann (ξof v) v < cdΓ.ht (ξof v) - D := hξofLt v hv
        have hvC : v ∈ Cξ (ξof v) hvP := hCξ_gt _ hvP v hvLt
        have hwY : hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)) ∈ YΓ :=
          hfootY _ hvP v hvC
        have hwdist : hdist v (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))
            = (cdΓ.ht (ξof v) - D) - busemann (ξof v) v := hfootDist _ hvP v hvC
        have hdepth : (cdΓ.ht (ξof v) - D) - busemann (ξof v) v ≤ 1 := by
          have h1 : cdΓ.ht (ξof v) - D ≤ busemann (ξof v) u := by
            rw [hYΓdef] at hu
            exact hu (ξof v) hvP
          have h2 : busemann (ξof v) u - busemann (ξof v) v ≤ hdist u v :=
            le_trans (le_abs_self _) (busemann_lipschitz' hId (cdΓ.hPsub hvP) u v)
          linarith
        have hvw : hdist v (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))) ≤ 1 := by
          rw [hwdist]; exact hdepth
        have huw : hdist u (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))) ≤ 3 := by
          linarith [hd_triangle hId u v (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))),
            hvw, huv]
        have hvlev : lev (ξof v) v ≤ Real.exp (cdΓ.ht (ξof v) - D) := by
          rw [lev_eq_exp (cdΓ.hPsub hvP), Real.exp_le_exp]
          exact le_of_lt hvLt
        have hwlev : lev (ξof v) (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))
            ≤ Real.exp (cdΓ.ht (ξof v) - D) := by
          rw [(hptOfLevelYc (ξof v) (cdΓ.hPsub hvP) (yc_orth (cdΓ.hPsub hvP))
            (Real.exp_pos _)).1]
        have h1 : hdist (Ψξ (ξof v) hvP v)
            (Ψξ (ξof v) hvP (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))))
            ≤ ∑ j, max (C0i j) 0 :=
          hΨξlocC _ hvP v _ hvlev hwlev (by linarith)
        have h2 : hdist (Ψξ (ξof v) hvP (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))))
            (ΦT (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))) ≤ Ccons := by
          have h := hcons' (ξof v) hvP (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))
            ((hptOfLevelYc (ξof v) (cdΓ.hPsub hvP) (yc_orth (cdΓ.hPsub hvP)) (Real.exp_pos _)).1)
          rw [hd_symm hId] at h
          exact h
        have h3 : hdist (ΦT (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))) (ΦT u)
            ≤ CT :=
          hΦTloc' _ hwY u hu (by rw [hd_symm hId _ u]; exact huw)
        rw [hΦc v hv, hΦY u hu]
        have hsym := hd_symm hId (ΦT u) (Ψξ (ξof v) hvP v)
        linarith [hd_triangle hId (Ψξ (ξof v) hvP v)
            (Ψξ (ξof v) hvP (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))) (ΦT u),
          hd_triangle hId (Ψξ (ξof v) hvP (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))))
            (ΦT (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))) (ΦT u),
          h1, h2, h3]
    · by_cases hv : v ∈ YΓ
      · -- the seam, `v` in the collar
        have huP : ξof u ∈ cdΓ.P := hξofP u hu
        have huLt : busemann (ξof u) u < cdΓ.ht (ξof u) - D := hξofLt u hu
        have huC : u ∈ Cξ (ξof u) huP := hCξ_gt _ huP u huLt
        have hwY : hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)) ∈ YΓ :=
          hfootY _ huP u huC
        have hwdist : hdist u (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))
            = (cdΓ.ht (ξof u) - D) - busemann (ξof u) u := hfootDist _ huP u huC
        have hdepth : (cdΓ.ht (ξof u) - D) - busemann (ξof u) u ≤ 1 := by
          have h1 : cdΓ.ht (ξof u) - D ≤ busemann (ξof u) v := by
            rw [hYΓdef] at hv
            exact hv (ξof u) huP
          have h2 : busemann (ξof u) v - busemann (ξof u) u ≤ hdist v u :=
            le_trans (le_abs_self _) (busemann_lipschitz' hId (cdΓ.hPsub huP) v u)
          linarith
        have huw : hdist u (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))) ≤ 1 := by
          rw [hwdist]; exact hdepth
        have hvw : hdist v (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))) ≤ 3 := by
          linarith [hd_triangle hId v u (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))),
            huw, huv']
        have huvlev : lev (ξof u) u ≤ Real.exp (cdΓ.ht (ξof u) - D) := by
          rw [lev_eq_exp (cdΓ.hPsub huP), Real.exp_le_exp]
          exact le_of_lt huLt
        have hwlev : lev (ξof u) (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))
            ≤ Real.exp (cdΓ.ht (ξof u) - D) := by
          rw [(hptOfLevelYc (ξof u) (cdΓ.hPsub huP) (yc_orth (cdΓ.hPsub huP))
            (Real.exp_pos _)).1]
        have h1 : hdist (Ψξ (ξof u) huP u)
            (Ψξ (ξof u) huP (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))))
            ≤ ∑ j, max (C0i j) 0 :=
          hΨξlocC _ huP u _ huvlev hwlev (by linarith)
        have h2 : hdist (Ψξ (ξof u) huP (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))))
            (ΦT (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))) ≤ Ccons := by
          have h := hcons' (ξof u) huP (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))
            ((hptOfLevelYc (ξof u) (cdΓ.hPsub huP) (yc_orth (cdΓ.hPsub huP)) (Real.exp_pos _)).1)
          rw [hd_symm hId] at h
          exact h
        have h3 : hdist (ΦT (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))) (ΦT v)
            ≤ CT :=
          hΦTloc' _ hwY v hv (by rw [hd_symm hId _ v]; exact hvw)
        rw [hΦc u hu, hΦY v hv]
        linarith [hd_triangle hId (Ψξ (ξof u) huP u)
            (Ψξ (ξof u) huP (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))) (ΦT v),
          hd_triangle hId (Ψξ (ξof u) huP (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))))
            (ΦT (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))) (ΦT v),
          h1, h2, h3]
      · -- both in shrunken cusps, hence in the same one
        have huP : ξof u ∈ cdΓ.P := hξofP u hu
        have hvP : ξof v ∈ cdΓ.P := hξofP v hv
        have huC : u ∈ Cξ (ξof u) huP := hCξ_gt _ huP u (hξofLt u hu)
        have hvC : v ∈ Cξ (ξof v) hvP := hCξ_gt _ hvP v (hξofLt v hv)
        have hEq : ξof u = ξof v := by
          by_contra hne
          have hsep := hCuspSep (ξof u) huP (ξof v) hvP u v huC hvC hne
          linarith
        have hcongr := hΨξcongr (ξof u) (ξof v) hEq huP hvP v
        have hvlev : lev (ξof u) v ≤ Real.exp (cdΓ.ht (ξof u) - D) := by
          rw [lev_eq_exp (cdΓ.hPsub huP), Real.exp_le_exp]
          have h := hξofLt v hv
          rw [← hEq] at h
          exact le_of_lt h
        have huvlev : lev (ξof u) u ≤ Real.exp (cdΓ.ht (ξof u) - D) := by
          rw [lev_eq_exp (cdΓ.hPsub huP), Real.exp_le_exp]
          exact le_of_lt (hξofLt u hu)
        rw [hΦc u hu, hΦc v hv, ← hcongr]
        have h1 := hΨξlocC (ξof u) huP u v huvlev hvlev (le_trans huv (by norm_num))
        linarith [h1]
  -- (10) coarse surjectivity of `Φ`
  choose Csusp hCsusp using hΨ0surj
  have hCsusp_le : ∀ i : Fin m, Csusp i ≤ ∑ j, max (Csusp j) 0 := by
    intro i
    exact le_trans (real_le_max_left _ _)
      (Finset.single_le_sum (f := fun j : Fin m => max (Csusp j) 0)
        (fun j _ => real_le_max_right _ _) (Finset.mem_univ i))
  have h0Y : (0 : E n) ∈ YΓ := by
    rw [hYΓdef]
    intro ξ hξ
    rw [busemann_zero]
    linarith [hCΓ' ξ hξ]
  have hKcne : ∃ k₁ : E n, k₁ ∈ Kc ∧ k₁ ∈ YΓ := by
    obtain ⟨γ, hγ⟩ := hKc 0 h0Y
    exact ⟨(γ : PO n 1) • 0, hγ, cdΓ.collarInv hAb hId γ 0 h0Y⟩
  obtain ⟨k₁, hk₁K, hk₁X⟩ := hKcne
  obtain ⟨mΛ, ηs, hηs, hrepΛ⟩ := cuspOrbitsFinite n hAb hId Λ hΛ cdΛ.hPsub
    (cdΛ.heq hAb hId) cdΛ.hPinv cdΛ.hdisj ⟨cdΛ.K, cdΛ.hKc, cdΛ.hK⟩
  obtain ⟨KΛc', hKΛc'c, hKΛc'sub, hKΛc'⟩ := cdΛ.collarCompact hAb hId hηs hrepΛ D
  obtain ⟨CT1, hCT1⟩ := thickPhiX_surj hAb hId hΓdisc f (X := YΓ)
    (fun γ u hu => cdΓ.collarInv hAb hId γ u hu) hKcc hKc hKΛc'c γof hγofK
    (XΛ := YΛ) hKΛc' hk₁K hk₁X
  set Csurj : ℝ := max (max CT1 (Ccons + (∑ i : Fin m, max (Csusp i) 0)
      + 2 * (∑ j, max (C0i j) 0))) 0 with hCsurjdef
  have hCsurj0 : 0 ≤ Csurj := by rw [hCsurjdef]; exact real_le_max_right _ _
  have hCsusp_le' : ∀ i : Fin m, Csusp i ≤ Csurj := by
    intro i
    have h1 : (∑ j : Fin m, max (Csusp j) 0)
        ≤ max CT1 ((Ccons + (∑ i : Fin m, max (Csusp i) 0))
          + 2 * (∑ j : Fin m, max (C0i j) 0)) :=
      le_trans (le_trans (le_add_of_nonneg_left hCcons) (le_add_of_nonneg_right (by positivity)))
        (le_max_right _ _)
    have h2 : max CT1 ((Ccons + (∑ i : Fin m, max (Csusp i) 0))
          + 2 * (∑ j : Fin m, max (C0i j) 0)) ≤ Csurj := by
      rw [hCsurjdef]
      exact le_max_left _ _
    exact le_trans (hCsusp_le i) (le_trans h1 h2)
  have hΦsurj : ∃ C : ℝ, ∀ w : E n, ∃ u : E n, hdist (Φ u) w ≤ C := by
    refine ⟨Csurj, fun w => ?_⟩
    by_cases hw : w ∈ YΛ
    · obtain ⟨u, huX, hu⟩ := hCT1 w hw
      refine ⟨u, le_trans ?_ (le_trans (le_max_left _ _) (le_max_left _ _))⟩
      rw [hΦY u huX]
      exact hu
    · -- `w` lies deep in a Λ-cusp
      have hw'' : ∃ η : E n, η ∈ cdΛ.P ∧ busemann η w < cdΛ.ht η - D := by
        have h : ¬ (∀ η ∈ cdΛ.P, cdΛ.ht η - D ≤ busemann η w) := by
          intro hh; exact hw (by rw [hYΛdef]; exact hh)
        push_neg at h
        exact h
      obtain ⟨η, hη, hηlt⟩ := hw''
      obtain ⟨ξ, hξP, hFξ⟩ := hFsurj η hη
      have hmem : w ∈ CΛ (F ξ) := by
        simp only [CΛ, Set.mem_ofPred_eq]
        rw [lev_eq_exp (cdΛ.hPsub (hFmem ξ hξP)), Real.exp_lt_exp, hFξ]
        exact hηlt
      have hbd : bd ((((f (γr ξ hξP) : Λ)))⁻¹) (F ξ) = F (ξs (irep ξ hξP)) := by
        have h2 := bd_inv_bd_cuspCorr hAb (cdΛ.hPsub (hFmem (ξs (irep ξ hξP)) (hξs _)))
          (g := (((f (γr ξ hξP) : Λ)) : PO n 1))
        have h3 : bd (((f (γr ξ hξP) : Λ)) : PO n 1) (F (ξs (irep ξ hξP))) = F ξ := by
          rw [← hFeq (ξs (irep ξ hξP)) (hξs _) (γr ξ hξP), hγr ξ hξP]
        rw [h3] at h2
        exact h2
      have hw'lev : lev (F (ξs (irep ξ hξP)))
          ((((((f (γr ξ hξP) : Λ)) : PO n 1))⁻¹) • w)
          ≤ Real.exp (cdΛ.ht (F (ξs (irep ξ hξP))) - D) := by
        have h := hCΛsub (((f (γr ξ hξP))⁻¹ : Λ)) (F ξ) (hFmem ξ hξP) w hmem
        have hcoe : (((f (γr ξ hξP))⁻¹ : Λ) : PO n 1)
            = ((((f (γr ξ hξP) : Λ)) : PO n 1))⁻¹ := by
          rw [Subgroup.coe_inv]
        rw [hcoe, hbd] at h
        simp only [CΛ, Set.mem_ofPred_eq] at h
        exact le_of_lt h
      obtain ⟨u', hu'lev, hu'dist⟩ := hCsusp (irep ξ hξP)
        ((((((f (γr ξ hξP) : Λ)) : PO n 1))⁻¹) • w) hw'lev
      have hu'lev' : lev (ξs (irep ξ hξP)) u' ≤ Real.exp (cdΓ.ht (ξs (irep ξ hξP)) - D) := by
        have h2 : Real.exp (cdΛ.ht (F (ξs (irep ξ hξP))) - D)
            / Real.exp (cdΛ.ht (F (ξs (irep ξ hξP))) - cdΓ.ht (ξs (irep ξ hξP)))
            = Real.exp (cdΓ.ht (ξs (irep ξ hξP)) - D) := by
          rw [← Real.exp_sub]
          congr 1
          ring
        exact le_trans hu'lev (le_of_eq h2)
      have hΨeq : Ψξ ξ hξP (((γr ξ hξP : Γ) : PO n 1) • u')
          = ((((f (γr ξ hξP) : Λ)) : PO n 1)) • Ψ0 (irep ξ hξP) u' := by
        show ((((f (γr ξ hξP) : Λ)) : PO n 1)) • Ψ0 (irep ξ hξP)
            ((((((γr ξ hξP)⁻¹ : Γ)) : PO n 1)) • (((γr ξ hξP : Γ) : PO n 1) • u')) = _
        rw [Subgroup.coe_inv]
        rw [smul_inv_smul_cancel hAb (((γr ξ hξP : Γ) : PO n 1)) u']
      have hdist_rot : hdist (((((f (γr ξ hξP) : Λ)) : PO n 1)) • Ψ0 (irep ξ hξP) u') w
          = hdist (Ψ0 (irep ξ hξP) u') ((((((f (γr ξ hξP) : Λ)) : PO n 1))⁻¹) • w) := by
        calc hdist (((((f (γr ξ hξP) : Λ)) : PO n 1)) • Ψ0 (irep ξ hξP) u') w
            = hdist ((((((f (γr ξ hξP) : Λ)) : PO n 1))⁻¹)
                • (((((f (γr ξ hξP) : Λ)) : PO n 1)) • Ψ0 (irep ξ hξP) u'))
              ((((((f (γr ξ hξP) : Λ)) : PO n 1))⁻¹) • w) :=
              (hId.isom_smul _ _ _).symm
          _ = hdist (Ψ0 (irep ξ hξP) u') ((((((f (γr ξ hξP) : Λ)) : PO n 1))⁻¹) • w) := by
              rw [smul_inv_smul_cancel hAb _ _]
      by_cases hlt : lev (ξs (irep ξ hξP)) u' < Real.exp (cdΓ.ht (ξs (irep ξ hξP)) - D)
      · -- strictly inside the cusp: the cusp branch is used
        have hbu' : busemann (ξs (irep ξ hξP)) u' < cdΓ.ht (ξs (irep ξ hξP)) - D := by
          have h2 : Real.exp (busemann (ξs (irep ξ hξP)) u')
              < Real.exp (cdΓ.ht (ξs (irep ξ hξP)) - D) := by
            rw [← lev_eq_exp (cdΓ.hPsub (hξs (irep ξ hξP))) u']
            exact hlt
          exact Real.exp_lt_exp.mp h2
        have hbusu : busemann ξ (((γr ξ hξP : Γ) : PO n 1) • u')
            = busemann (ξs (irep ξ hξP)) u' + (cdΓ.ht ξ - cdΓ.ht (ξs (irep ξ hξP))) := by
          have h := cdΓ.busemann_shift hAb hId (hξs (irep ξ hξP)) (γr ξ hξP) u'
          rw [hγr ξ hξP] at h
          exact h
        have huNY : (((γr ξ hξP : Γ) : PO n 1) • u') ∉ YΓ := by
          rw [hYΓdef]
          simp only [Set.mem_ofPred_eq]
          push_neg
          exact ⟨ξ, hξP, by rw [hbusu]; linarith⟩
        have hξofu : ξof (((γr ξ hξP : Γ) : PO n 1) • u') = ξ :=
          hCξ_unique _ (hξofP _ huNY) ξ hξP _
            (hCξ_gt _ (hξofP _ huNY) _ (hξofLt _ huNY))
            (hCξ_gt ξ hξP _ (by rw [hbusu]; linarith))
        refine ⟨((γr ξ hξP : Γ) : PO n 1) • u', ?_⟩
        rw [hΦc _ huNY, hΨξcongr _ _ hξofu (hξofP _ huNY) hξP _, hΨeq, hdist_rot]
        exact le_trans hu'dist (hCsusp_le' _)
      · -- on the seam: the collar branch is used, and consistency closes the gap
        have hu'lev'' : lev (ξs (irep ξ hξP)) u'
            = Real.exp (cdΓ.ht (ξs (irep ξ hξP)) - D) :=
          le_antisymm hu'lev' (not_lt.mp hlt)
        have hbu'' : busemann (ξs (irep ξ hξP)) u' = cdΓ.ht (ξs (irep ξ hξP)) - D := by
          have h2 : Real.exp (busemann (ξs (irep ξ hξP)) u')
              = Real.exp (cdΓ.ht (ξs (irep ξ hξP)) - D) := by
            rw [← lev_eq_exp (cdΓ.hPsub (hξs (irep ξ hξP))) u']
            exact hu'lev''
          exact Real.exp_injective h2
        have hbusu : busemann ξ (((γr ξ hξP : Γ) : PO n 1) • u') = cdΓ.ht ξ - D := by
          have h := cdΓ.busemann_shift hAb hId (hξs (irep ξ hξP)) (γr ξ hξP) u'
          rw [hγr ξ hξP] at h
          rw [h, hbu'']
          ring
        have hlevu : lev ξ (((γr ξ hξP : Γ) : PO n 1) • u') = Real.exp (cdΓ.ht ξ - D) := by
          rw [lev_eq_exp (cdΓ.hPsub hξP), hbusu]
        have huY : (((γr ξ hξP : Γ) : PO n 1) • u') ∈ YΓ := by
          have hmem' : (((γr ξ hξP : Γ) : PO n 1) • u') ∈ horoball ξ (cdΓ.ht ξ) := by
            simp only [horoball, Set.mem_ofPred_eq]
            rw [hbusu]; linarith
          rw [hYΓdef]
          intro ξ' hξ'
          by_cases hEq : ξ' = ξ
          · rw [hEq, hbusu]
          · exact hHoro_other ξ hξP _ hmem' ξ' hξ' hEq
        refine ⟨((γr ξ hξP : Γ) : PO n 1) • u', ?_⟩
        rw [hΦY _ huY]
        have h1 := hcons' ξ hξP (((γr ξ hξP : Γ) : PO n 1) • u') hlevu
        have h2 : hdist (Ψξ ξ hξP (((γr ξ hξP : Γ) : PO n 1) • u')) w ≤ Csusp (irep ξ hξP) := by
          rw [hΨeq, hdist_rot]
          exact hu'dist
        have h3 : CT1 ≤ Csurj := by
          rw [hCsurjdef]
          exact le_trans (le_max_left _ _) (le_max_left _ _)
        have hS0 : 0 ≤ ∑ i : Fin m, max (Csusp i) 0 :=
          Finset.sum_nonneg (fun i _ => real_le_max_right _ _)
        have hCtop : max CT1 ((Ccons + (∑ i : Fin m, max (Csusp i) 0))
              + 2 * (∑ j : Fin m, max (C0i j) 0)) ≤ Csurj := by
          rw [hCsurjdef]
          exact le_max_left _ _
        have h4 : (∑ j : Fin m, max (C0i j) 0) ≤ Csurj := by
          have hA1 : (∑ j : Fin m, max (C0i j) 0) ≤ 2 * (∑ j : Fin m, max (C0i j) 0) := by
            linarith [hCcusp0]
          have hA2 : 2 * (∑ j : Fin m, max (C0i j) 0)
              ≤ (Ccons + (∑ i : Fin m, max (Csusp i) 0)) + 2 * (∑ j : Fin m, max (C0i j) 0) :=
            le_add_of_nonneg_left (by linarith [hCcons, hS0])
          exact le_trans (le_trans hA1 hA2) (le_trans (le_max_right _ _) hCtop)
        have h5 : Ccons + (∑ i : Fin m, max (Csusp i) 0) + 2 * (∑ j : Fin m, max (C0i j) 0)
            ≤ Csurj :=
          le_trans (le_max_right (CT1 : ℝ) ((Ccons + (∑ i : Fin m, max (Csusp i) 0))
            + 2 * (∑ j : Fin m, max (C0i j) 0))) hCtop
        linarith [hd_triangle hId (ΦT (((γr ξ hξP : Γ) : PO n 1) • u'))
          (Ψξ ξ hξP (((γr ξ hξP : Γ) : PO n 1) • u')) w, h1, h2,
          hCsusp_le (irep ξ hξP), h5, hCcons, hS0]
  obtain ⟨Cs0, hCs0⟩ := hΦsurj
  have hCs0pos : 0 ≤ Cs0 := by
    obtain ⟨u, hu⟩ := hCs0 0
    exact le_trans (hd_nonneg hId _ _) hu
  -- (11) the global coarse-Lipschitz bound for `Φ`, and its coarse equivariance
  have hΦglob : ∀ u v : E n, hdist (Φ u) (Φ v)
      ≤ (CT + Ccons + (∑ j, max (C0i j) 0) + CT) * hdist u v
        + (CT + Ccons + (∑ j, max (C0i j) 0) + CT) :=
    fun u v => hdist_map_le hId (by linarith [hCT0, hCcons, hCcusp0]) hΦloc1 u v
  have hΦeq : ∀ γ : Γ, ∃ C : ℝ, ∀ u : E n,
      hdist (Φ ((γ : PO n 1) • u)) (((f γ : Λ) : PO n 1) • Φ u) ≤ C := by
    intro γ
    refine ⟨max CT (∑ j, max (Cφi j) 0), fun u => ?_⟩
    by_cases hu : u ∈ YΓ
    · have hgu : (γ : PO n 1) • u ∈ YΓ := cdΓ.collarInv hAb hId γ u hu
      rw [hΦY _ hgu, hΦY u hu]
      exact le_trans (hΦTeq' γ u hu) (real_le_max_left _ _)
    · have huP : ξof u ∈ cdΓ.P := hξofP u hu
      have huC : u ∈ Cξ (ξof u) huP := hCξ_gt _ huP u (hξofLt u hu)
      have hgu : (γ : PO n 1) • u ∉ YΓ := by
        intro hcon
        have h := cdΓ.collarInv hAb hId γ⁻¹ ((γ : PO n 1) • u) hcon
        rw [subgroup_inv_smul hAb γ u] at h
        exact hu h
      have hguP : ξof ((γ : PO n 1) • u) ∈ cdΓ.P := hξofP _ hgu
      have hEq : ξof ((γ : PO n 1) • u) = bd (γ : PO n 1) (ξof u) :=
        hCξ_unique _ hguP _ (cdΓ.hPinv γ _ huP) _
          (hCξ_gt _ hguP _ (hξofLt _ hgu))
          (by
            have h2mem : (γ : PO n 1) • u ∈ (fun z => (γ : PO n 1) • z) '' (Cξ (ξof u) huP) :=
              ⟨u, huC, rfl⟩
            rwa [hCξinv (ξof u) huP γ] at h2mem)
      rw [hΦc _ hgu, hΦc u hu,
        hΨξcongr _ _ hEq hguP (cdΓ.hPinv γ (ξof u) huP) ((γ : PO n 1) • u)]
      exact le_trans (hΨξeq (ξof u) huP γ u huC) (real_le_max_right _ _)
  -- (12) level tracking: the levels of `Ψξ` and of the collar orbit map `ΦT`
  have hΦTlev : ∀ (η : E n) (hη : η ∈ cdΛ.P) (m : Λ),
      busemann η ((m : PO n 1) • (0 : E n))
        = cdΛ.ht η - cdΛ.ht (bd (((m⁻¹ : Λ)) : PO n 1) η) := by
    intro η hη m
    have hη' : bd (((m⁻¹ : Λ)) : PO n 1) η ∈ cdΛ.P := cdΛ.hPinv m⁻¹ η hη
    have h := cdΛ.busemann_shift hAb hId hη' m (0 : E n)
    have hbd : bd (m : PO n 1) (bd (((m⁻¹ : Λ)) : PO n 1) η) = η := by
      have h0 := bd_inv_bd_cuspCorr hAb (cdΛ.hPsub hη) (g := ((m : PO n 1))⁻¹)
      rw [Subgroup.coe_inv]
      simpa using h0
    rw [hbd, busemann_zero, zero_add] at h
    exact h
  have hFinj : ∀ ξ (hξ : ξ ∈ cdΓ.P) (ζ : E n) (hζ : ζ ∈ cdΓ.P), F ξ = F ζ → ξ = ζ := by
    intro ξ hξ ζ hζ hFF
    obtain ⟨γ, hγpar, hγbd⟩ := hparΓ₁ ξ hξ
    have hγbdF : bd ((f γ : Λ) : PO n 1) (F ξ) = F ξ := hFstab ξ hξ γ hγbd
    have hγbdF' : bd ((f γ : Λ) : PO n 1) (F ζ) = F ζ := by rw [← hFF]; exact hγbdF
    obtain ⟨γ', hγ'bd, hγ'f⟩ := hFstab' ζ hζ (f γ) hγbdF'
    have hγ'eq : γ' = γ := f.injective hγ'f
    rw [hγ'eq] at hγ'bd
    exact (paraUniqueFixed hAb hId hγpar (cdΓ.hPsub hξ) hγbd (cdΓ.hPsub hζ) hγ'bd).symm
  have hΨξlev : ∀ ξ (hξ : ξ ∈ cdΓ.P) (u : E n), u ∈ Cξ ξ hξ →
      busemann (F ξ) (Ψξ ξ hξ u) = busemann ξ u + (cdΛ.ht (F ξ) - cdΓ.ht ξ) := by
    intro ξ hξ u hu
    obtain ⟨z, hz, hzu⟩ := hu
    have hzu' : ((γr ξ hξ : Γ) : PO n 1) • z = u := hzu
    have hbdi : bd (((γr ξ hξ)⁻¹ : Γ) : PO n 1) ξ = ξs (irep ξ hξ) := by
      have h := bd_inv_bd_cuspCorr hAb (cdΓ.hPsub (hξs (irep ξ hξ))) (g := (((γr ξ hξ : Γ)) : PO n 1))
      rw [hγr ξ hξ] at h
      rw [Subgroup.coe_inv]
      exact h
    have hbus1 : busemann (ξs (irep ξ hξ)) z
        = busemann ξ (((γr ξ hξ : Γ) : PO n 1) • z)
          + (cdΓ.ht (ξs (irep ξ hξ)) - cdΓ.ht ξ) := by
      have h := cdΓ.busemann_shift hAb hId hξ (((γr ξ hξ)⁻¹ : Γ))
        (((γr ξ hξ : Γ) : PO n 1) • z)
      rw [hbdi] at h
      rw [subgroup_inv_smul hAb (γr ξ hξ) z] at h
      exact h
    have hDpos : 0 < lam (irep ξ hξ) * lev (ξs (irep ξ hξ)) z :=
      mul_pos (hlampos _) (lev_pos _ (cdΓ.hPsub (hξs _)) z)
    have hbus2 : busemann (F (ξs (irep ξ hξ))) (Ψ0 (irep ξ hξ) z)
        = Real.log (lam (irep ξ hξ) * lev (ξs (irep ξ hξ)) z) := by
      rw [hΨ0formula (irep ξ hξ) z]
      exact (hptOfLevelYc (F (ξs (irep ξ hξ)))
        (cdΛ.hPsub (hFmem (ξs (irep ξ hξ)) (hξs _)))
        ((hψper (irep ξ hξ)).1 (yc (ξs (irep ξ hξ)) z) (yc_orth (cdΓ.hPsub (hξs _))))
        hDpos).2.2
    have hFξ' : bd (((f (γr ξ hξ) : Λ)) : PO n 1) (F (ξs (irep ξ hξ))) = F ξ := by
      rw [← hFeq (ξs (irep ξ hξ)) (hξs _) (γr ξ hξ), hγr ξ hξ]
    have hmain : busemann (F ξ) (Ψξ ξ hξ u)
        = Real.log (lam (irep ξ hξ) * lev (ξs (irep ξ hξ)) z)
          + (cdΛ.ht (F ξ) - cdΛ.ht (F (ξs (irep ξ hξ)))) := by
      rw [← hzu']
      change busemann (F ξ) ((((f (γr ξ hξ) : Λ)) : PO n 1) • Ψ0 (irep ξ hξ)
        (((((γr ξ hξ)⁻¹ : Γ)) : PO n 1) • (((γr ξ hξ : Γ) : PO n 1) • z))) = _
      rw [Subgroup.coe_inv]
      rw [smul_inv_smul_cancel hAb (((γr ξ hξ : Γ) : PO n 1)) z]
      have h := cdΛ.busemann_shift hAb hId (hFmem (ξs (irep ξ hξ)) (hξs _))
        (f (γr ξ hξ)) (Ψ0 (irep ξ hξ) z)
      rw [hFξ'] at h
      rw [h, hbus2]
    rw [hmain,
      Real.log_mul (ne_of_gt (hlampos _)) (ne_of_gt (lev_pos _ (cdΓ.hPsub (hξs _)) z))]
    have hlamlog : Real.log (lam (irep ξ hξ))
        = cdΛ.ht (F (ξs (irep ξ hξ))) - cdΓ.ht (ξs (irep ξ hξ)) := by
      show Real.log (Real.exp (cdΛ.ht (F (ξs (irep ξ hξ))) - cdΓ.ht (ξs (irep ξ hξ)))) = _
      rw [Real.log_exp]
    rw [hlamlog, lev_eq_exp (cdΓ.hPsub (hξs _)) z, Real.log_exp, hbus1, hzu']
    ring
  -- (13) the level of `Φ v` at a Λ-cusp that `Φ v` does not enter, and the mixed bound
  have hΦouter : ∀ (ξ : E n) (hξ : ξ ∈ cdΓ.P),
      (∀ v : E n, v ∈ YΓ → cdΛ.ht (F ξ) - D ≤ busemann (F ξ) (Φ v)) ∧
      (∀ (ζ : E n) (hζ : ζ ∈ cdΓ.P) (v : E n), ζ ≠ ξ → v ∈ Cξ ζ hζ →
        cdΛ.ht (F ξ) - D ≤ busemann (F ξ) (Φ v)) := by
    intro ξ hξ
    have hFξP : F ξ ∈ cdΛ.P := hFmem ξ hξ
    constructor
    · intro v hvY
      rw [hΦY v hvY]
      show cdΛ.ht (F ξ) - D
        ≤ busemann (F ξ) ((((f (γof v) : Λ)) : PO n 1) • (0 : E n))
      rw [hΦTlev (F ξ) hFξP (f (γof v))]
      have h1 := hCΛ' (bd ((((f (γof v))⁻¹ : Λ)) : PO n 1) (F ξ))
        (cdΛ.hPinv _ (F ξ) hFξP)
      linarith
    · intro ζ hζ v hne hvC
      have hvNY : v ∉ YΓ := by
        intro hcon
        rw [hYΓdef] at hcon
        linarith [hcon ζ hζ, hCξ_lt ζ hζ v hvC]
      have hξofv : ξof v = ζ :=
        hCξ_unique _ (hξofP v hvNY) ζ hζ v
          (hCξ_gt _ (hξofP v hvNY) v (hξofLt v hvNY)) hvC
      have hFne : F ζ ≠ F ξ := fun hEq => hne (hFinj ζ hζ ξ hξ hEq)
      have hmem : Φ v ∈ CΛ (F ζ) := by
        rw [hΦc v hvNY, hΨξcongr _ _ hξofv (hξofP v hvNY) hζ v]
        exact hΨξimg ζ hζ v hvC
      have hmem2 : Φ v ∈ horoball (F ζ) (cdΛ.ht (F ζ)) := by
        have h' : lev (F ζ) (Φ v) < Real.exp (cdΛ.ht (F ζ) - D) := hmem
        rw [lev_eq_exp (cdΛ.hPsub (hFmem ζ hζ))] at h'
        simp only [horoball, Set.mem_ofPred_eq]
        exact lt_of_lt_of_le (Real.exp_lt_exp.mp h')
          (by linarith [hCΛ' (F ζ) (hFmem ζ hζ)])
      have hni : Φ v ∉ horoball (F ξ) (cdΛ.ht (F ξ)) :=
        Set.disjoint_left.mp (cdΛ.hdisj (hFmem ζ hζ) hFξP hFne) hmem2
      by_contra hcon
      exact hni (by simp only [horoball, Set.mem_ofPred_eq]; linarith [not_le.mp hcon])
  have hmixed : ∀ (ξ : E n) (hξ : ξ ∈ cdΓ.P) (u : E n), u ∈ Cξ ξ hξ →
      hdist (Φ u) (Φ (hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D))))
        ≤ (∑ j, max (C0i j) 0) * ((cdΓ.ht ξ - D) - busemann ξ u)
          + ((∑ j, max (C0i j) 0) + Ccons) := by
    intro ξ hξ u hu
    have hwY : hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D)) ∈ YΓ := hfootY ξ hξ u hu
    have hwdist := hfootDist ξ hξ u hu
    have huNY : u ∉ YΓ := by
      intro hcon
      rw [hYΓdef] at hcon
      linarith [hcon ξ hξ, hCξ_lt ξ hξ u hu]
    have h1 : hdist (Ψξ ξ hξ u) (Ψξ ξ hξ (hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D))))
        ≤ (∑ j, max (C0i j) 0) * ((cdΓ.ht ξ - D) - busemann ξ u) + (∑ j, max (C0i j) 0) := by
      have h := hΨξglob ξ hξ u (hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D)))
        (by rw [lev_eq_exp (cdΓ.hPsub hξ), Real.exp_le_exp]
            exact le_of_lt (hCξ_lt ξ hξ u hu))
        (le_of_eq (hptOfLevelYc ξ (cdΓ.hPsub hξ) (yc_orth (cdΓ.hPsub hξ))
          (Real.exp_pos _)).1)
      rwa [hwdist] at h
    have h2 : hdist (Ψξ ξ hξ (hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D))))
        (Φ (hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D)))) ≤ Ccons := by
      rw [hΦY _ hwY]
      have h := hcons' ξ hξ (hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D)))
        ((hptOfLevelYc ξ (cdΓ.hPsub hξ) (yc_orth (cdΓ.hPsub hξ)) (Real.exp_pos _)).1)
      rwa [hd_symm hId] at h
    have hξofu : ξof u = ξ :=
      hCξ_unique _ (hξofP u huNY) ξ hξ u
        (hCξ_gt _ (hξofP u huNY) u (hξofLt u huNY)) hu
    rw [hΦc u huNY, hΨξcongr _ _ hξofu (hξofP u huNY) hξ u]
    linarith [hd_triangle hId (Ψξ ξ hξ u)
      (Ψξ ξ hξ (hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D))))
      (Φ (hptOf ξ (yc ξ u) (Real.exp (cdΓ.ht ξ - D)))), h1, h2]
  -- (14) the reverse local bound at scale `Mrev = 2 * Cs0 + 1`
  have hψtwo : ∀ i : Fin m, ∃ L Cq : ℝ, 1 ≤ L ∧ 0 ≤ Cq ∧
      (∀ x y : E n, inner ℝ x (ξs i) = 0 → inner ℝ y (ξs i) = 0 →
        ‖ψ i x - ψ i y‖ ≤ L * ‖x - y‖ + Cq) ∧
      (∀ x y : E n, inner ℝ x (ξs i) = 0 → inner ℝ y (ξs i) = 0 →
        ‖x - y‖ ≤ L * ‖ψ i x - ψ i y‖ + Cq) := by
    intro i
    obtain ⟨hy0, hR0, hδ, hlip, hsurj, heq⟩ := hψspec i
    obtain ⟨L, Cq, hL, hCq, hfwd, hrev⟩ := hlip
    exact ⟨L, Cq, hL, hCq, hfwd, hrev⟩
  choose Li Cqi hLi hCqi hfwdi hrevdi using hψtwo
  set Mrev : ℝ := 2 * Cs0 + 1 with hMrevdef
  have hMrev0 : 0 ≤ Mrev := by rw [hMrevdef]; linarith [hCs0pos]
  set Ccs : Fin m → ℝ := (fun i => Real.arcosh (Real.cosh Mrev
      + 2 * (Li i) ^ 2 * Real.cosh Mrev / (lam i) ^ 2 + (Cqi i) ^ 2)) with hCcsdef
  have hCcs_le : ∀ i : Fin m, Ccs i ≤ ∑ j : Fin m, max (Ccs j) 0 := by
    intro i
    exact le_trans (real_le_max_left _ _)
      (Finset.single_le_sum (f := fun j : Fin m => max (Ccs j) 0)
        (fun j _ => real_le_max_right _ _) (Finset.mem_univ i))
  set Cmix : ℝ := (∑ j, max (C0i j) 0) * Mrev + ((∑ j, max (C0i j) 0) + Ccons) with hCmixdef
  have hCmix0 : 0 ≤ Cmix := by rw [hCmixdef]; positivity
  obtain ⟨CY, hCY⟩ := orbitReverse hAb hId hΓdisc hΛdisc f (X := YΓ) (K := Kc) hKcc γof hγofK
    (M := 2 * Cmix + Mrev)
  have hCY' : ∀ u v : E n, u ∈ YΓ → v ∈ YΓ → hdist (Φ u) (Φ v) ≤ 2 * Cmix + Mrev →
      hdist u v ≤ CY := by
    intro u v hu hv huv
    have hzu : Φ u = (((f (γof u) : Λ)) : PO n 1) • (0 : E n) := by
      rw [hΦY u hu]
      exact hPhiT_eq u
    have hzv : Φ v = (((f (γof v) : Λ)) : PO n 1) • (0 : E n) := by
      rw [hΦY v hv]
      exact hPhiT_eq v
    refine hCY u v hu hv ?_
    rw [← hzu, ← hzv]
    exact huv
  -- the depth bound
  have hdepthCore : ∀ u (hu : u ∉ YΓ) (v : E n), hdist (Φ u) (Φ v) ≤ Mrev →
      (cdΛ.ht (F (ξof u)) - D ≤ busemann (F (ξof u)) (Φ v)) →
      cdΓ.ht (ξof u) - D - busemann (ξof u) u ≤ Mrev := by
    intro u hu v huv h2
    have huP : ξof u ∈ cdΓ.P := hξofP u hu
    have huC : u ∈ Cξ (ξof u) huP := hCξ_gt _ huP u (hξofLt u hu)
    have h1 : busemann (F (ξof u)) (Φ u)
        = busemann (ξof u) u + (cdΛ.ht (F (ξof u)) - cdΓ.ht (ξof u)) := by
      rw [hΦc u hu]
      exact hΨξlev (ξof u) huP u huC
    have h3 : busemann (F (ξof u)) (Φ v) - busemann (F (ξof u)) (Φ u) ≤ hdist (Φ u) (Φ v) := by
      have h := busemann_lipschitz' hId (cdΛ.hPsub (hFmem (ξof u) huP)) (Φ u) (Φ v)
      rw [abs_le] at h
      linarith [h.1]
    linarith
  have hdepthY : ∀ u (hu : u ∉ YΓ) (v : E n), v ∈ YΓ → hdist (Φ u) (Φ v) ≤ Mrev →
      cdΓ.ht (ξof u) - D - busemann (ξof u) u ≤ Mrev :=
    fun u hu v hvY huv => hdepthCore u hu v huv ((hΦouter (ξof u) (hξofP u hu)).1 v hvY)
  have hdepthC : ∀ u (hu : u ∉ YΓ) (ζ : E n) (hζ : ζ ∈ cdΓ.P) (v : E n),
      ζ ≠ ξof u → v ∈ Cξ ζ hζ → hdist (Φ u) (Φ v) ≤ Mrev →
      cdΓ.ht (ξof u) - D - busemann (ξof u) u ≤ Mrev :=
    fun u hu ζ hζ v hne hvC huv =>
      hdepthCore u hu v huv ((hΦouter (ξof u) (hξofP u hu)).2 ζ hζ v hne hvC)
  have hΦrevloc : ∀ u v : E n, hdist (Φ u) (Φ v) ≤ Mrev →
      hdist u v ≤ max (max CY (CY + 2 * Mrev)) (∑ j : Fin m, max (Ccs j) 0) := by
    intro u v huv
    by_cases hu : u ∈ YΓ
    · by_cases hv : v ∈ YΓ
      · exact le_trans (hCY' u v hu hv (by linarith [huv, hCmix0]))
          (le_trans (le_max_left _ _) (le_max_left _ _))
      · -- `u` in the collar, `v` in a cusp
        have hvP : ξof v ∈ cdΓ.P := hξofP v hv
        have hvC : v ∈ Cξ (ξof v) hvP := hCξ_gt _ hvP v (hξofLt v hv)
        have hvNY := hv
        have hwY : hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)) ∈ YΓ :=
          hfootY _ hvP v hvC
        have hwdd := hfootDist _ hvP v hvC
        have hs := hdepthY v hv u hu (by
          rw [hd_symm hId (Φ v) (Φ u)]; exact huv)
        have hm : hdist (Φ v) (Φ (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))))
            ≤ Cmix := by
          refine le_trans (hmixed (ξof v) hvP v hvC) ?_
          rw [hCmixdef]
          have h1 : (∑ j, max (C0i j) 0)
              * ((cdΓ.ht (ξof v) - D) - busemann (ξof v) v) ≤ (∑ j, max (C0i j) 0) * Mrev :=
            mul_le_mul_of_nonneg_left hs hCcusp0
          linarith
        have h1 : hdist (Φ (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))) (Φ u)
            ≤ Cmix + Mrev := by
          have h2 : hdist (Φ (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))) (Φ v)
              ≤ Cmix := by
            rw [hd_symm hId (Φ (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))) (Φ v)]
            exact hm
          have huv'' : hdist (Φ v) (Φ u) ≤ Mrev := by
            rw [hd_symm hId (Φ v) (Φ u)]
            exact huv
          linarith [hd_triangle hId
            (Φ (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))) (Φ v) (Φ u), h2, huv'']
        have h3 : hdist (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))) u ≤ CY :=
          hCY' _ _ hwY hu (by linarith [h1, hCmix0])
        have h4 : hdist v (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))) ≤ Mrev := by
          rw [hwdd]; exact hs
        have h6 : hdist u v ≤ Mrev + CY := by
          rw [hd_symm hId u v]
          linarith [hd_triangle hId v
            (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))) u, h3, h4]
        exact le_trans h6
          (le_trans (le_trans (by linarith [hMrev0]) (le_max_right CY (CY + 2 * Mrev)))
            (le_max_left (max CY (CY + 2 * Mrev)) (∑ j : Fin m, max (Ccs j) 0)))
    · by_cases hv : v ∈ YΓ
      · -- `u` in a cusp, `v` in the collar
        have huP : ξof u ∈ cdΓ.P := hξofP u hu
        have huC : u ∈ Cξ (ξof u) huP := hCξ_gt _ huP u (hξofLt u hu)
        have hwY : hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)) ∈ YΓ :=
          hfootY _ huP u huC
        have hwdd := hfootDist _ huP u huC
        have hs := hdepthY u hu v hv huv
        have hm : hdist (Φ u) (Φ (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))))
            ≤ Cmix := by
          refine le_trans (hmixed (ξof u) huP u huC) ?_
          rw [hCmixdef]
          have h1 : (∑ j, max (C0i j) 0)
              * ((cdΓ.ht (ξof u) - D) - busemann (ξof u) u) ≤ (∑ j, max (C0i j) 0) * Mrev :=
            mul_le_mul_of_nonneg_left hs hCcusp0
          linarith
        have h1 : hdist (Φ (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))) (Φ v)
            ≤ Cmix + Mrev := by
          have hm' : hdist (Φ (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))) (Φ u)
              ≤ Cmix := by
            rw [hd_symm hId
              (Φ (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))) (Φ u)]
            exact hm
          linarith [hd_triangle hId
            (Φ (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))) (Φ u) (Φ v),
            hm', huv]
        have h3 : hdist (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))) v ≤ CY :=
          hCY' _ _ hwY hv (by linarith [h1, hCmix0])
        have h4 : hdist u (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))) ≤ Mrev := by
          rw [hwdd]; exact hs
        have h6 : hdist u v ≤ Mrev + CY := by
          linarith [hd_triangle hId u
            (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))) v, h3, h4]
        exact le_trans h6
          (le_trans (le_trans (by linarith [hMrev0]) (le_max_right CY (CY + 2 * Mrev)))
            (le_max_left (max CY (CY + 2 * Mrev)) (∑ j : Fin m, max (Ccs j) 0)))
      · -- both in cusps
        by_cases hEq : ξof u = ξof v
        · -- the same cusp: the cusp reverse estimate
          have huP : ξof u ∈ cdΓ.P := hξofP u hu
          have hvP : ξof v ∈ cdΓ.P := hξofP v hv
          have hcongr := hΨξcongr (ξof u) (ξof v) hEq huP hvP v
          have huv' : hdist (Ψξ (ξof u) huP u) (Ψξ (ξof u) huP v) ≤ Mrev := by
            have h := huv
            rw [hΦc u hu, hΦc v hv, ← hcongr] at h
            exact h
          have huC : u ∈ Cξ (ξof u) huP := hCξ_gt _ huP u (hξofLt u hu)
          have hvC' : v ∈ Cξ (ξof u) huP := by
            refine hCξ_gt _ huP v ?_
            rw [hEq]
            exact hξofLt v hv
          have hΨ : hdist (Ψ0 (irep (ξof u) huP)
                ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • u))
              (Ψ0 (irep (ξof u) huP) ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • v)) ≤ Mrev := by
            have h := huv'
            rw [show Ψξ (ξof u) huP u
                = (((f (γr (ξof u) huP) : Λ)) : PO n 1)
                  • Ψ0 (irep (ξof u) huP) ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • u) from rfl,
              show Ψξ (ξof u) huP v
                = (((f (γr (ξof u) huP) : Λ)) : PO n 1)
                  • Ψ0 (irep (ξof u) huP) ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • v) from rfl] at h
            rwa [hId.isom_smul] at h
          have hbdi : bd (((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) (ξof u) = ξs (irep (ξof u) huP) := by
            have h := bd_inv_bd_cuspCorr hAb (cdΓ.hPsub (hξs (irep (ξof u) huP)))
              (g := (((γr (ξof u) huP : Γ)) : PO n 1))
            rw [hγr (ξof u) huP] at h
            rw [Subgroup.coe_inv]
            exact h
          have hlevz : ∀ w : E n, w ∈ Cξ (ξof u) huP →
              lev (ξs (irep (ξof u) huP)) ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • w)
                ≤ Real.exp (cdΓ.ht (ξs (irep (ξof u) huP)) - D) := by
            intro w hw
            rw [lev_eq_exp (cdΓ.hPsub (hξs (irep (ξof u) huP))), Real.exp_le_exp]
            have hsh := cdΓ.busemann_shift hAb hId huP (((γr (ξof u) huP)⁻¹ : Γ)) w
            rw [hbdi] at hsh
            rw [hsh]
            have hw' := hCξ_lt (ξof u) huP w hw
            linarith
          have hM' : hdist (hptOf (F (ξs (irep (ξof u) huP)))
                (ψ (irep (ξof u) huP) (yc (ξs (irep (ξof u) huP))
                  ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • u)))
                (lam (irep (ξof u) huP) * lev (ξs (irep (ξof u) huP))
                  ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • u)))
              (hptOf (F (ξs (irep (ξof u) huP)))
                (ψ (irep (ξof u) huP) (yc (ξs (irep (ξof u) huP))
                  ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • v)))
                (lam (irep (ξof u) huP) * lev (ξs (irep (ξof u) huP))
                  ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • v))) ≤ Mrev := by
            have h := hΨ
            rw [hΨ0formula (irep (ξof u) huP) ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • u),
              hΨ0formula (irep (ξof u) huP) ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • v)] at h
            exact h
          have hres := cuspReverse hId (cdΓ.hPsub (hξs (irep (ξof u) huP)))
            (cdΛ.hPsub (hFmem (ξs (irep (ξof u) huP)) (hξs _)))
            (hlampos (irep (ξof u) huP))
            (by rw [Real.exp_le_one_iff]; linarith [hCΓ' (ξs (irep (ξof u) huP)) (hξs _)])
            (hLi (irep (ξof u) huP)) (hCqi (irep (ξof u) huP))
            (hψper (irep (ξof u) huP)).1 (hfwdi (irep (ξof u) huP)) (hrevdi (irep (ξof u) huP))
            (hlevz u huC) (hlevz v hvC') hM'
          have hres' : hdist ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • u)
              ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • v) ≤ Ccs (irep (ξof u) huP) := hres
          have hiso : hdist u v = hdist ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • u)
              ((((γr (ξof u) huP)⁻¹ : Γ) : PO n 1) • v) := by
            rw [hId.isom_smul]
          rw [hiso]
          exact le_trans hres'
            (le_trans (hCcs_le (irep (ξof u) huP)) (le_max_right _ _))
        · -- different cusps
          have huP : ξof u ∈ cdΓ.P := hξofP u hu
          have hvP : ξof v ∈ cdΓ.P := hξofP v hv
          have huC : u ∈ Cξ (ξof u) huP := hCξ_gt _ huP u (hξofLt u hu)
          have hvC : v ∈ Cξ (ξof v) hvP := hCξ_gt _ hvP v (hξofLt v hv)
          have hs_u := hdepthC u hu (ξof v) hvP v (fun h => hEq h.symm) hvC huv
          have huv' : hdist (Φ v) (Φ u) ≤ Mrev := by
            rw [hd_symm hId (Φ v) (Φ u)]; exact huv
          have hs_v := hdepthC v hv (ξof u) huP u hEq huC huv'
          have hwYu : hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)) ∈ YΓ :=
            hfootY _ huP u huC
          have hwYv : hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)) ∈ YΓ :=
            hfootY _ hvP v hvC
          have hwdu := hfootDist _ huP u huC
          have hwdv := hfootDist _ hvP v hvC
          have hmu : hdist (Φ u) (Φ (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))))
              ≤ Cmix := by
            refine le_trans (hmixed (ξof u) huP u huC) ?_
            rw [hCmixdef]
            have h1 : (∑ j, max (C0i j) 0)
                * ((cdΓ.ht (ξof u) - D) - busemann (ξof u) u) ≤ (∑ j, max (C0i j) 0) * Mrev :=
              mul_le_mul_of_nonneg_left hs_u hCcusp0
            linarith
          have hmv : hdist (Φ v) (Φ (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))))
              ≤ Cmix := by
            refine le_trans (hmixed (ξof v) hvP v hvC) ?_
            rw [hCmixdef]
            have h1 : (∑ j, max (C0i j) 0)
                * ((cdΓ.ht (ξof v) - D) - busemann (ξof v) v) ≤ (∑ j, max (C0i j) 0) * Mrev :=
              mul_le_mul_of_nonneg_left hs_v hCcusp0
            linarith
          have h1 : hdist (Φ (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))))
              (Φ (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))) ≤ 2 * Cmix + Mrev := by
            have h2 : hdist (Φ (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))) (Φ u)
                ≤ Cmix := by
              rw [hd_symm hId (Φ (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))) (Φ u)]
              exact hmu
            linarith [hd_triangle hId
              (Φ (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))) (Φ u)
              (Φ (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))),
              hd_triangle hId (Φ u) (Φ v)
              (Φ (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D)))),
              h2, huv, hmv]
          have h3 : hdist (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))
              (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))) ≤ CY :=
            hCY' _ _ hwYu hwYv h1
          have h4 : hdist u (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))) ≤ Mrev := by
            rw [hwdu]; exact hs_u
          have h5 : hdist v (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))) ≤ Mrev := by
            rw [hwdv]; exact hs_v
          have h4' : hdist (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))) u
              ≤ Mrev := by
            rw [hd_symm hId _ u]; exact h4
          have h5' : hdist (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))) v
              ≤ Mrev := by
            rw [hd_symm hId _ v]; exact h5
          have h6 : hdist u v ≤ 2 * Mrev + CY := by
            linarith [hd_triangle hId u
              (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D))) v,
              hd_triangle hId
                (hptOf (ξof u) (yc (ξof u) u) (Real.exp (cdΓ.ht (ξof u) - D)))
                (hptOf (ξof v) (yc (ξof v) v) (Real.exp (cdΓ.ht (ξof v) - D))) v,
              h3, h4', h5']
          exact le_trans h6
            (le_trans (by linarith [hMrev0])
              (le_trans (le_max_right _ _) (le_max_left _ _)))
  -- (15) the assembly
  set Cfg : ℝ := CT + Ccons + (∑ j, max (C0i j) 0) + CT with hCfgdef
  set Arev : ℝ := max (max CY (CY + 2 * Mrev)) (∑ j : Fin m, max (Ccs j) 0) with hArevdef
  have hArev0 : 0 ≤ Arev := by
    rw [hArevdef]
    exact le_trans (Finset.sum_nonneg (fun j _ => real_le_max_right _ _)) (le_max_right _ _)
  have hsurj' : ∀ w : E n, ∃ u : E n, hdist (Φ u) w ≤ Cs0 := hCs0
  refine ⟨Φ, ?_, hΦeq⟩
  refine ⟨max Cfg (max 1 Arev), max (max Cfg (2 * Arev)) Cs0, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (le_max_left (1 : ℝ) Arev) (le_max_right Cfg (max 1 Arev))
  · exact le_trans hCs0pos (le_max_right _ _)
  · intro u v
    have hK : Cfg ≤ max Cfg (max 1 Arev) := le_max_left _ _
    have hC : Cfg ≤ max (max Cfg (2 * Arev)) Cs0 :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hd : 0 ≤ hdist u v := hd_nonneg hId u v
    have hm := mul_le_mul_of_nonneg_right hK hd
    linarith [hΦglob u v, hm, hC]
  · intro u v
    have h := reverseOfLocal hId hArev0 hCs0pos hCs0 hΦrevloc
      (le_of_eq hMrevdef.symm) u v
    have hK1 : Arev ≤ max Cfg (max 1 Arev) :=
      le_trans (le_max_right (1 : ℝ) Arev) (le_max_right Cfg (max 1 Arev))
    have hK2 : (1 : ℝ) ≤ max Cfg (max 1 Arev) :=
      le_trans (le_max_left (1 : ℝ) Arev) (le_max_right Cfg (max 1 Arev))
    have hK : max Arev 1 ≤ max Cfg (max 1 Arev) := max_le hK1 hK2
    have hC : 2 * Arev ≤ max (max Cfg (2 * Arev)) Cs0 :=
      le_trans (le_max_right Cfg (2 * Arev)) (le_max_left _ _)
    have hd : 0 ≤ hdist (Φ u) (Φ v) := hd_nonneg hId _ _
    have hm := mul_le_mul_of_nonneg_right hK hd
    linarith [h, hm, hC]
  · intro w
    obtain ⟨u, hu⟩ := hsurj' w
    exact ⟨u, le_trans hu (le_max_right _ _)⟩

end Work.Mostow
