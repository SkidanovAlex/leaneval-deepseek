import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Grassmann-metric symmetry for subspaces of equal dimension

For two subspaces `x`, `v` of a finite-dimensional real inner product space with
`Module.finrank ℝ x = Module.finrank ℝ v`, the supremum of the orthogonal residuals
`‖z - π_v z‖` over unit vectors `z ∈ x` equals the corresponding supremum of
`‖u - π_x u‖` over unit vectors `u ∈ v`.  This is the symmetry of the largest principal
angle between two equidimensional subspaces (used for the `k = l` case of the challenge
distance `distSubspaces`).

The proof: on the space `x`, the operator `z ↦ π_x (π_v z)` is symmetric positive; let `ν`
be its smallest eigenvalue (an infimum of Rayleigh quotients, attained by the spectral
theorem for self-adjoint operators on finite-dimensional inner product spaces).  A unit
eigenvector `z₀` for `ν` minimizes `‖π_v z‖` over the unit sphere of `x`, so the residual
`‖z - π_v z‖` is maximised there with value `s₀ = ‖z₀ - π_v z₀‖`.  Dually, the unit vector
`π_v z₀ / ‖π_v z₀‖ ∈ v` (or, in the degenerate `ν = 0` case, a unit vector of `v ⊓ xᗮ`,
which is nontrivial by a dimension argument) attains the same residual `s₀` against `x`,
which gives the two inequalities between the suprema.
-/

open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The set of orthogonal residuals of unit vectors of `x` w.r.t. `v`. -/
def residSet (x v : Submodule ℝ E) : Set ℝ :=
  {r : ℝ | ∃ z : E, z ∈ x ∧ ‖z‖ = 1 ∧ ‖z - v.starProjection z‖ = r}

/-- The self-adjoint compression `z ↦ π_x(π_v z)` on the space `x`. -/
def T (x v : Submodule ℝ E) : x →ₗ[ℝ] x where
  toFun z := ⟨x.starProjection (v.starProjection (z : E)), Submodule.starProjection_apply_mem x _⟩
  map_add' := by intro a b; ext; simp [map_add]
  map_smul' := by intro a b; ext; simp [map_smul]

lemma inner_x_star_eq (x : Submodule ℝ E) (A : E) (z : x) :
    inner ℝ (x.starProjection A) (z : E) = inner ℝ A (z : E) := by
  rw [Submodule.inner_starProjection_left_eq_right]
  congr 1
  exact Submodule.starProjection_eq_self_iff.mpr z.2

lemma inner_star_x_eq (x : Submodule ℝ E) (A : E) (z : x) :
    inner ℝ (z : E) (x.starProjection A) = inner ℝ (z : E) A := by
  calc
    inner ℝ (z : E) (x.starProjection A) = inner ℝ (x.starProjection A) (z : E) := real_inner_comm _ _
    _ = inner ℝ A (z : E) := inner_x_star_eq x A z
    _ = inner ℝ (z : E) A := real_inner_comm _ _

lemma T_symm (x v : Submodule ℝ E) : (T x v).IsSymmetric := by
  intro a b
  calc
    inner ℝ (T x v a) b = inner ℝ (x.starProjection (v.starProjection (a : E))) (b : E) := rfl
    _ = inner ℝ (v.starProjection (a : E)) (b : E) := inner_x_star_eq x _ b
    _ = inner ℝ (a : E) (v.starProjection (b : E)) := by
          rw [Submodule.inner_starProjection_left_eq_right]
    _ = inner ℝ (a : E) (x.starProjection (v.starProjection (b : E))) := by
          rw [← inner_star_x_eq x (v.starProjection (b : E)) a]
    _ = inner ℝ a (T x v b) := rfl

lemma inner_v_star_eq_normSq (v : Submodule ℝ E) (a : E) :
    inner ℝ (v.starProjection a) a = ‖v.starProjection a‖ ^ 2 := by
  have h := Submodule.re_inner_starProjection_eq_normSq (K := v) (v := a)
  simpa [Submodule.coe_orthogonalProjectionOnto_apply] using h

lemma T_inner (x v : Submodule ℝ E) (z : x) :
    inner ℝ (T x v z) z = ‖v.starProjection (z : E)‖ ^ 2 := by
  calc
    inner ℝ (T x v z) z = inner ℝ (x.starProjection (v.starProjection (z : E))) (z : E) := rfl
    _ = inner ℝ (v.starProjection (z : E)) (z : E) := inner_x_star_eq x _ z
    _ = ‖v.starProjection (z : E)‖ ^ 2 := inner_v_star_eq_normSq v (z : E)

/-- The smallest eigenvalue of `T` on `x` (an infimum of Rayleigh quotients). -/
def nu (x v : Submodule ℝ E) : ℝ :=
  ⨅ w : {w : x // w ≠ 0}, (inner ℝ (T x v (w : x)) (w : x)) / ‖(w : x)‖ ^ 2

lemma range_nu_bddBelow (x v : Submodule ℝ E) :
    BddBelow (Set.range (fun w0 : {w0 : x // w0 ≠ 0} =>
      (inner ℝ (T x v (w0 : x)) (w0 : x)) / ‖(w0 : x)‖ ^ 2)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨w0, rfl⟩
  have h0 : 0 ≤ inner ℝ (T x v (w0 : x)) (w0 : x) := by
    rw [T_inner]
    exact sq_nonneg _
  have hd : 0 < ‖(w0 : x)‖ ^ 2 := by
    exact sq_pos_of_ne_zero (by simpa using (norm_ne_zero_iff.mpr w0.2))
  exact div_nonneg h0 (le_of_lt hd)

lemma hasEigenvalue_nu (x v : Submodule ℝ E) [Nontrivial x] :
    Module.End.HasEigenvalue (T x v) (nu x v) := by
  dsimp [nu]
  exact (T_symm x v).hasEigenvalue_iInf_of_finiteDimensional

lemma nu_le_of_ne_zero (x v : Submodule ℝ E) (w : x) (hw : w ≠ 0) :
    nu x v ≤ (inner ℝ (T x v w) w) / ‖(w : x)‖ ^ 2 := by
  dsimp [nu]
  exact ciInf_le (range_nu_bddBelow x v) ⟨w, hw⟩

lemma nu_le_proj_normSq_unit (x v : Submodule ℝ E) (w : x) (hw : ‖(w : x)‖ = 1) :
    nu x v ≤ ‖v.starProjection (w : E)‖ ^ 2 := by
  have hw0 : w ≠ 0 := by
    intro h
    have : ‖(w : x)‖ = 0 := by simp [h]
    linarith
  have h := nu_le_of_ne_zero x v w hw0
  have hval : (inner ℝ (T x v w) w) / ‖(w : x)‖ ^ 2 = ‖v.starProjection (w : E)‖ ^ 2 := by
    rw [T_inner, hw]
    simp
  rwa [hval] at h

noncomputable def z1 (x v : Submodule ℝ E) (w0 : x) (hw0 : w0 ≠ 0) : x :=
  (‖(w0 : x)‖⁻¹) • w0

lemma z1_norm (x v : Submodule ℝ E) (w0 : x) (hw0 : w0 ≠ 0) : ‖(z1 x v w0 hw0 : x)‖ = 1 := by
  have hne : ‖(w0 : x)‖ ≠ 0 := by simpa using (norm_ne_zero_iff.mpr hw0)
  have hpos : 0 < ‖(w0 : x)‖ := norm_pos_iff.mpr hw0
  rw [z1, norm_smul]
  rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (le_of_lt hpos)]
  field_simp [hne]

lemma z1_eig (x v : Submodule ℝ E) (w0 : x) (hw0 : w0 ≠ 0) (hT : T x v w0 = nu x v • w0) :
    T x v (z1 x v w0 hw0) = nu x v • (z1 x v w0 hw0) := by
  unfold z1
  have hlin : T x v ((‖(w0 : x)‖⁻¹) • w0) = (‖(w0 : x)‖⁻¹) • (T x v w0) := by simp
  calc
    T x v ((‖(w0 : x)‖⁻¹) • w0) = (‖(w0 : x)‖⁻¹) • (T x v w0) := hlin
    _ = (‖(w0 : x)‖⁻¹) • (nu x v • w0) := by rw [hT]
    _ = nu x v • ((‖(w0 : x)‖⁻¹) • w0) := by
          rw [smul_smul, smul_smul]
          congr 1
          ring
    _ = nu x v • z1 x v w0 hw0 := by rfl

lemma nu_eq_proj_normSq_z1 (x v : Submodule ℝ E) (w0 : x) (hw0 : w0 ≠ 0)
    (hT : T x v w0 = nu x v • w0) :
    nu x v = ‖v.starProjection ((z1 x v w0 hw0) : E)‖ ^ 2 := by
  let z := z1 x v w0 hw0
  have hz1 : ‖(z : x)‖ = 1 := z1_norm x v w0 hw0
  have hTz : T x v z = nu x v • z := z1_eig x v w0 hw0 hT
  calc
    nu x v = inner ℝ (nu x v • z) z := by
          rw [inner_smul_left]
          simp [hz1]
    _ = inner ℝ (T x v z) z := by rw [← hTz]
    _ = ‖v.starProjection (z : E)‖ ^ 2 := T_inner x v z

/-- Pythagoras: `‖z - P_v z‖² = ‖z‖² - ‖P_v z‖²`. -/
lemma resid_normSq (v : Submodule ℝ E) (z : E) :
    ‖z - v.starProjection z‖ ^ 2 = ‖z‖ ^ 2 - ‖v.starProjection z‖ ^ 2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection (x := z) (S := v)
  have hval : ‖vᗮ.starProjection z‖ ^ 2 = ‖z - v.starProjection z‖ ^ 2 := by
    congr 2
    rw [Submodule.starProjection_orthogonal_val]
  linarith

lemma norm_starProjection_le (v : Submodule ℝ E) (z : E) :
    ‖v.starProjection z‖ ≤ ‖z‖ :=
  Submodule.norm_starProjection_apply_le (K := v) z

/-- rank lemma: `(v ⊓ xᗮ) = ⊥` and equal dimensions imply `(x ⊓ vᗮ) = ⊥`. -/
lemma orth_meet_eq_bot_of_eq {x v : Submodule ℝ E}
    (hfin : Module.finrank ℝ x = Module.finrank ℝ v)
    (h : (v ⊓ xᗮ) = ⊥) : (x ⊓ vᗮ) = ⊥ := by
  let φ : v →ₗ[ℝ] x :=
    { toFun := fun u => ⟨x.starProjection (u : E), Submodule.starProjection_apply_mem x _⟩
      map_add' := by intro a b; ext; simp [map_add]
      map_smul' := by intro a b; ext; simp [map_smul] }
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff φ.ker).mpr ?_
    intro u hu
    have huφ : x.starProjection (u : E) = 0 := by
      have := congrArg (fun w : x => (w : E)) (LinearMap.mem_ker.mp hu)
      simpa [φ] using this
    have huorth : (u : E) ∈ xᗮ := by
      apply (Submodule.orthogonalProjectionOnto_eq_zero_iff).mp ?_
      ext
      rw [← Submodule.starProjection_apply]
      exact huφ
    ext
    have hmem : (u : E) ∈ (v ⊓ xᗮ) := ⟨u.2, huorth⟩
    have : (u : E) = 0 := by
      rw [h] at hmem
      simpa using hmem
    exact this
  have hφsurj : Function.Surjective φ := by
    have hker_bot : φ.ker = ⊥ := LinearMap.ker_eq_bot.mpr hφinj
    have hfrker : Module.finrank ℝ φ.ker = 0 := (Submodule.finrank_eq_zero.mpr hker_bot)
    have hfrrange : Module.finrank ℝ φ.range = Module.finrank ℝ v := by
      have := LinearMap.finrank_range_add_finrank_ker (f := φ)
      rw [hfrker, add_zero] at this
      exact this
    have htop : φ.range = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq (S := φ.range)
      rw [hfrrange, hfin]
    rw [← LinearMap.range_eq_top]
    exact htop
  refine (Submodule.eq_bot_iff (x ⊓ vᗮ)).mpr ?_
  intro z hz
  have hzx : z ∈ x := (Submodule.mem_inf.mp hz).1
  have hzv : z ∈ vᗮ := (Submodule.mem_inf.mp hz).2
  have hzφ : ∃ u : v, φ u = ⟨z, hzx⟩ := hφsurj ⟨z, hzx⟩
  rcases hzφ with ⟨u, huφ⟩
  have hφval : (x.starProjection (u : E)) = z := by
    have := congrArg (fun w : x => (w : E)) huφ
    simpa [φ] using this
  have hnorm : ‖z‖ ^ 2 = 0 := by
    calc
      ‖z‖ ^ 2 = inner ℝ z z := by
            simpa using (inner_self_eq_norm_sq z).symm
      _ = inner ℝ (x.starProjection (u : E)) z := by rw [hφval]
      _ = inner ℝ (u : E) (x.starProjection z) := by
            rw [Submodule.inner_starProjection_left_eq_right]
      _ = inner ℝ (u : E) z := by
            congr 1
            exact Submodule.starProjection_eq_self_iff.mpr hzx
      _ = 0 := by
            exact (Submodule.mem_orthogonal v z).mp hzv (u : E) u.2
  have hz0 : ‖z‖ = 0 := by
    nlinarith [sq_nonneg ‖z‖]
  simpa using hz0

lemma orth_meet_of_finrank_eq {x v : Submodule ℝ E}
    (hfin : Module.finrank ℝ x = Module.finrank ℝ v)
    (hmeet : (x ⊓ vᗮ) ≠ ⊥) : (v ⊓ xᗮ) ≠ ⊥ := by
  intro hbot
  apply hmeet
  exact orth_meet_eq_bot_of_eq hfin hbot

lemma exists_unit_orthogonal_of_finrank_eq {x v : Submodule ℝ E}
    (hfin : Module.finrank ℝ x = Module.finrank ℝ v)
    (hz0 : ∃ z : E, z ∈ x ∧ ‖z‖ = 1 ∧ v.starProjection z = 0) :
    ∃ u : E, u ∈ v ∧ ‖u‖ = 1 ∧ x.starProjection u = 0 := by
  rcases hz0 with ⟨z, hzx, hzn, hzproj⟩
  have hmeet : (x ⊓ vᗮ) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨z, ?_, ?_⟩
    · exact ⟨hzx, (Submodule.mem_orthogonal v z).2 (by
        intro u hu
        have h1 := Submodule.starProjection_inner_eq_zero (K := v) (v := z) (w := u) hu
        have hzperp : inner ℝ z u = 0 := by simpa [hzproj] using h1
        rwa [real_inner_comm])⟩
    · intro hz
      have : ‖z‖ = 0 := by simpa [hz]
      linarith
  have hmeet' : (v ⊓ xᗮ) ≠ ⊥ := orth_meet_of_finrank_eq hfin hmeet
  rw [Submodule.ne_bot_iff] at hmeet'
  rcases hmeet' with ⟨u0, hu0m, hu00⟩
  refine ⟨(‖u0‖⁻¹) • u0, ?_, ?_, ?_⟩
  · exact Submodule.smul_mem v (‖u0‖⁻¹) hu0m.1
  · rw [norm_smul]
    have hpos : 0 < ‖u0‖ := norm_pos_iff.mpr hu00
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hpos))]
    field_simp [ne_of_gt hpos]
  · have hu0orth : (‖u0‖⁻¹) • u0 ∈ xᗮ := Submodule.smul_mem xᗮ (‖u0‖⁻¹) hu0m.2
    have hz : x.orthogonalProjectionOnto ((‖u0‖⁻¹) • u0) = 0 :=
      (Submodule.orthogonalProjectionOnto_eq_zero_iff).mpr hu0orth
    rw [Submodule.starProjection_apply]
    exact congrArg (fun w : x => (w : E)) hz

/-- upper bound of a residual-sup by pointwise bounds. -/
lemma residSup_le_of_forall {x v : Submodule ℝ E} {s : ℝ}
    (hz0 : ∃ z : E, z ∈ x ∧ ‖z‖ = 1)
    (h : ∀ z : E, z ∈ x → ‖z‖ = 1 → ‖z - v.starProjection z‖ ≤ s) :
    sSup (residSet x v) ≤ s := by
  apply csSup_le
  · rcases hz0 with ⟨z, hzx, hzn⟩
    refine ⟨‖z - v.starProjection z‖, z, hzx, hzn, rfl⟩
  · intro r hr
    rcases hr with ⟨z, hzx, hzn, hzr⟩
    rw [← hzr]
    exact h z hzx hzn

/-- lower bound of a residual-sup by membership. -/
lemma le_residSup_of_mem {x v : Submodule ℝ E} {s : ℝ}
    (hmem : ∃ u : E, u ∈ v ∧ ‖u‖ = 1 ∧ ‖u - x.starProjection u‖ = s) :
    s ≤ sSup (residSet v x) := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    intro r hr
    rcases hr with ⟨u, huv, hun, hur⟩
    rw [← hur]
    have hsq := resid_normSq x u
    have hle : ‖u - x.starProjection u‖ ^ 2 ≤ 1 := by
      rw [hsq]
      rw [hun]
      nlinarith [sq_nonneg ‖x.starProjection u‖]
    have hle' : ‖u - x.starProjection u‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
      simpa using hle
    exact le_of_sq_le_sq hle' (by norm_num : (0 : ℝ) ≤ 1)
  · rcases hmem with ⟨u, huv, hun, hus⟩
    refine ⟨u, huv, hun, hus⟩

lemma residSet_eq_empty_of_bot {x v : Submodule ℝ E} (hx : x = ⊥) : residSet x v = ∅ := by
  ext r
  constructor
  · rintro ⟨z, hzx, hzn, _⟩
    have : z = 0 := by simpa [hx] using hzx
    have hz0 : ‖z‖ = 0 := by simp [this]
    linarith
  · intro hr
    exact False.elim hr

/-- One direction of the main theorem. -/
lemma residSup_le_of_finrank_eq (x v : Submodule ℝ E)
    (hfin : Module.finrank ℝ x = Module.finrank ℝ v) :
    sSup (residSet x v) ≤ sSup (residSet v x) := by
  by_cases hx : x = ⊥
  · have hv : v = ⊥ := by
      have hx0 : Module.finrank ℝ x = 0 := (Submodule.finrank_eq_zero.mpr hx)
      have hv0 : Module.finrank ℝ v = 0 := by simpa [hx0] using hfin.symm
      exact Submodule.finrank_eq_zero.mp hv0
    rw [residSet_eq_empty_of_bot hx, residSet_eq_empty_of_bot hv]
  · -- x ≠ ⊥
    haveI : Nontrivial x := (Submodule.nontrivial_iff_ne_bot.mpr hx)
    rcases (hasEigenvalue_nu x v).exists_hasEigenvector with ⟨w0, hw0⟩
    rw [Module.End.hasEigenvector_iff] at hw0
    have hw0ne : w0 ≠ 0 := hw0.2
    have hT : T x v w0 = nu x v • w0 := (Module.End.mem_eigenspace_iff.mp hw0.1)
    let z0 : x := z1 x v w0 hw0ne
    have hz0n : ‖(z0 : x)‖ = 1 := z1_norm x v w0 hw0ne
    have hz0eig : T x v z0 = nu x v • z0 := z1_eig x v w0 hw0ne hT
    have hνeq : nu x v = ‖v.starProjection (z0 : E)‖ ^ 2 := nu_eq_proj_normSq_z1 x v w0 hw0ne hT
    let z0E : E := z0
    have hz0E_mem : z0E ∈ x := z0.2
    have hz0E_norm : ‖z0E‖ = 1 := by simpa [z0E] using hz0n
    let s0 : ℝ := ‖z0E - v.starProjection z0E‖
    have hs0_nonneg : 0 ≤ s0 := norm_nonneg _

    -- s0² = 1 − ν
    have hs0_sq : s0 ^ 2 = 1 - nu x v := by
      dsimp [s0]
      rw [resid_normSq, hz0E_norm, hνeq]
      ring

    -- elementwise bound: every unit z ∈ x has residual ≤ s0
    have hbound : ∀ z : E, z ∈ x → ‖z‖ = 1 → ‖z - v.starProjection z‖ ≤ s0 := by
      intro z hzx hzn
      have hνle : nu x v ≤ ‖v.starProjection z‖ ^ 2 := by
        have := nu_le_proj_normSq_unit x v ⟨z, hzx⟩ (by simpa using hzn)
        simpa using this
      have hAz := resid_normSq v z
      have h1 : ‖z - v.starProjection z‖ ^ 2 ≤ 1 - nu x v := by
        rw [hAz, hzn]
        nlinarith [hνle]
      have hsq : ‖z - v.starProjection z‖ ^ 2 ≤ s0 ^ 2 := by
        rw [hs0_sq]
        exact h1
      exact le_of_sq_le_sq hsq hs0_nonneg

    -- upper bound
    have hup : sSup (residSet x v) ≤ s0 := by
      apply residSup_le_of_forall (s := s0)
      · exact ⟨z0E, hz0E_mem, hz0E_norm⟩
      · exact hbound

    -- lower bound: s0 ≤ sSup (residSet v x)
    have hlo : s0 ≤ sSup (residSet v x) := by
      by_cases hν0 : nu x v = 0
      · -- ν = 0
        have hP0 : v.starProjection z0E = 0 := by
          have hsq : ‖v.starProjection z0E‖ ^ 2 = 0 := by
            rw [← hνeq, hν0]
          have hnorm0 : ‖v.starProjection z0E‖ = 0 := by
            exact sq_eq_zero_iff.mp hsq
          exact norm_eq_zero.mp hnorm0
        rcases exists_unit_orthogonal_of_finrank_eq (x := x) (v := v) hfin
            ⟨z0E, hz0E_mem, hz0E_norm, hP0⟩ with ⟨uE, huE_mem, huE_norm, huE_P⟩
        have hs0 : s0 = 1 := by
          dsimp [s0]
          simp [hP0, hz0E_norm]
        have hval : ‖uE - x.starProjection uE‖ = s0 := by
          have : ‖uE - x.starProjection uE‖ = 1 := by
            rw [huE_P]
            simp [huE_norm]
          rw [hs0]
          exact this
        exact le_residSup_of_mem (x := x) (v := v) (s := s0) ⟨uE, huE_mem, huE_norm, hval⟩
      · -- ν > 0
        have hνpos : 0 < nu x v := by
          have hle : 0 ≤ nu x v := by
            rw [hνeq]
            exact sq_nonneg _
          exact lt_of_le_of_ne hle (fun h => hν0 h.symm)
        let a : E := v.starProjection z0E
        have ha_sq : ‖a‖ ^ 2 = nu x v := by
          dsimp [a, z0E]
          exact hνeq.symm
        have ha_ne : a ≠ 0 := by
          intro ha0
          have : ‖a‖ ^ 2 = 0 := by simp [ha0]
          exact hν0 (by rwa [ha_sq] at this)
        have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha_ne
        let uE : E := (‖a‖⁻¹) • a
        have huE_mem : uE ∈ v := by
          dsimp [uE]
          exact Submodule.smul_mem v (‖a‖⁻¹) (Submodule.starProjection_apply_mem v z0E)
        have huE_norm : ‖uE‖ = 1 := by
          dsimp [uE]
          rw [norm_smul]
          rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt ha_pos))]
          field_simp [ne_of_gt ha_pos]
        -- P_x (P_v z0E) = ν • z0E (eigenvector identity at E level)
        have hTa : x.starProjection a = nu x v • z0E := by
          have hco := congrArg (fun w : x => (w : E)) hz0eig
          dsimp [a, z0E, T] at hco ⊢
          simpa using hco
        -- ‖P_x uE‖² = ν
        have hPx_sq : ‖x.starProjection uE‖ ^ 2 = nu x v := by
          dsimp [uE]
          calc
            ‖x.starProjection ((‖a‖⁻¹) • a)‖ ^ 2
                = (‖a‖⁻¹) ^ 2 * ‖x.starProjection a‖ ^ 2 := by
                  rw [map_smul, norm_smul]
                  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt ha_pos))]
                  ring
            _ = (‖a‖⁻¹) ^ 2 * ‖nu x v • z0E‖ ^ 2 := by rw [hTa]
            _ = (‖a‖⁻¹) ^ 2 * (nu x v ^ 2 * ‖z0E‖ ^ 2) := by
                  rw [norm_smul]
                  rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hνpos)]
                  ring
            _ = nu x v := by
                  rw [hz0E_norm]
                  ring
                  rw [← ha_sq]
                  field_simp [ne_of_gt ha_pos]
        have hval : ‖uE - x.starProjection uE‖ = s0 := by
          have hsq := resid_normSq x uE
          -- ‖uE−P_xuE‖² = ‖uE‖² − ‖P_xuE‖² = 1 − ν = s0²
          have hle : ‖uE - x.starProjection uE‖ ^ 2 ≤ s0 ^ 2 := by
            rw [hsq, huE_norm, hPx_sq]
            rw [hs0_sq]
            norm_num
          have hge : s0 ^ 2 ≤ ‖uE - x.starProjection uE‖ ^ 2 := by
            rw [hsq, huE_norm, hPx_sq]
            rw [hs0_sq]
            norm_num
          have hnonneg : 0 ≤ ‖uE - x.starProjection uE‖ := norm_nonneg _
          exact le_antisymm (le_of_sq_le_sq hle hs0_nonneg) (le_of_sq_le_sq hge hnonneg)
        exact le_residSup_of_mem (x := x) (v := v) (s := s0) ⟨uE, huE_mem, huE_norm, hval⟩

    exact le_trans hup hlo

lemma residSup_eq_of_finrank_eq_set (x v : Submodule ℝ E)
    (hfin : Module.finrank ℝ x = Module.finrank ℝ v) :
    sSup (residSet x v) = sSup (residSet v x) := by
  apply le_antisymm
  · exact residSup_le_of_finrank_eq x v hfin
  · exact residSup_le_of_finrank_eq v x hfin.symm

/-- The requested statement: equality of residual suprema for equidimensional subspaces. -/
lemma residualSup_eq_of_finrank_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (x v : Submodule ℝ E) (h : Module.finrank ℝ x = Module.finrank ℝ v) :
    sSup {r : ℝ | ∃ z : E, z ∈ x ∧ ‖z‖ = 1 ∧ ‖z - v.starProjection z‖ = r} =
    sSup {r : ℝ | ∃ u : E, u ∈ v ∧ ‖u‖ = 1 ∧ ‖u - x.starProjection u‖ = r} := by
  change sSup (residSet x v) = sSup (residSet v x)
  exact residSup_eq_of_finrank_eq_set x v h

end Commons.Analysis.InnerProductSpace