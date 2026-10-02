import Mathlib
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher
import Submission.Work.Landing.Land.Landing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The angle of a ray landing at a repelling periodic point is pinned down modulo `1` by its return

Let `T_c z = z̄² + c` be the tricorn map, `φ` a Böttcher coordinate of `T_c`, `y` a repelling
periodic point of odd period `k` (`Work.Landing.IsRepelling c k y`), and suppose the dynamic rays
at angles `ψ` and `ψ'` both have accumulation set the singleton `{y}`.  If the two angles have the
same image under the `2k`-fold angle map `(angDouble)^[2k] θ = Int.fract (4^k θ)` — i.e.
`4^k ψ ≡ 4^k ψ' (mod 1)` — then `ψ ≡ ψ' (mod 1)`:

`∃ mm : ℤ, ψ = ψ' + mm`.

This is the **injectivity of the angle map on the type of a repelling periodic point**: the
holomorphic second return map `τ = (T_c)^[2k]` is locally biholomorphic at `y` (its multiplier
`multiplier2 c k y` has modulus `> 1`), while rays at angles `≢` modulo `1` are disjoint.
Parametrising the rays by Böttcher level, `t ↦ γ_θ(t)` with `φ (γ_θ t) = t e^{2πiθ}`, the transfer
`τ (γ_θ t) = γ_{angDouble^[2k] θ} (t^{4^k})` matches the levels; so if the two return angles agree
then the local injectivity of `τ` forces `γ_ψ t = γ_{ψ'} t`, and the two rays share a point,
whence `ψ ≡ ψ' (mod 1)`.

The Böttcher coordinate `φ` need only satisfy `IsDynBottcher`: injectivity on the escaping set and
surjectivity onto the exterior disc come from
`Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher`.
-/

namespace Work.LandLeaves

open Classical

section AngleArithmetic

/-- `Int.fract (-2 * Int.fract x) = Int.fract (-2 * x)`: the angle map `angDouble θ = fract (-2θ)`
is insensitive to integer shifts. -/
theorem fract_neg_two_fract (x : ℝ) :
    Int.fract (-2 * Int.fract x) = Int.fract (-2 * x) := by
  have hx : Int.fract x = x - (⌊x⌋ : ℤ) := by
    have h := Int.self_sub_fract (a := x)
    linarith
  rw [hx, ← Int.fract_add_intCast (-2 * x) (2 * ⌊x⌋)]
  congr 1
  push_cast
  ring

/-- `m`-fold angle doubling is multiplication of the angle by `(-2)^m`, reduced modulo `1`. -/
theorem angDouble_iterate_succ (n : ℕ) (θ : ℝ) :
    (Work.Landing.angDouble)^[n + 1] θ = Int.fract (((-2 : ℝ) ^ (n + 1)) * θ) := by
  induction n with
  | zero => simp [Work.Landing.angDouble, pow_one]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Work.Landing.angDouble, fract_neg_two_fract]
      congr 1
      rw [pow_succ]
      ring

/-- `m ≥ 1`-fold angle doubling is multiplication of the angle by `(-2)^m`, reduced modulo `1`. -/
theorem angDouble_iterate_eq (m : ℕ) (hm : 0 < m) (θ : ℝ) :
    (Work.Landing.angDouble)^[m] θ = Int.fract (((-2 : ℝ) ^ m) * θ) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact angDouble_iterate_succ n θ

/-- The `2k`-fold angle doubling is multiplication of the angle by `4^k`, reduced modulo `1`. -/
theorem angDouble_iterate_two_mul {k : ℕ} (hk : 0 < k) (θ : ℝ) :
    (Work.Landing.angDouble)^[2 * k] θ = Int.fract ((4 : ℝ) ^ k * θ) := by
  rw [angDouble_iterate_eq (2 * k) (by omega) θ]
  congr 1
  rw [show (-2 : ℝ) ^ (2 * k) = ((-2 : ℝ) ^ 2) ^ k from pow_mul (-2) 2 k]
  norm_num

end AngleArithmetic

section RayDirection

/-- The ray direction is a unit complex number. -/
theorem rayDirection_norm (θ : ℝ) : ‖Work.Landing.rayDirection θ‖ = 1 := by
  rw [Work.Landing.rayDirection]
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * θ)

/-- `‖t‖ = t` for a positive real `t`, transported to `ℂ`. -/
theorem norm_ofReal_of_pos {t : ℝ} (ht : 0 < t) : ‖(t : ℂ)‖ = t := by
  simp [abs_of_pos ht]

/-- The Böttcher level of `t e^{2πiθ}` is `t`. -/
theorem norm_mul_rayDirection {t : ℝ} (ht : 0 < t) (θ : ℝ) :
    ‖(t : ℂ) * Work.Landing.rayDirection θ‖ = t := by
  rw [norm_mul, rayDirection_norm, mul_one, norm_ofReal_of_pos ht]

/-- `(e^{2πiθ})^{4^k} = e^{2πi (4^k θ)}`. -/
theorem rayDirection_pow_four (k : ℕ) (θ : ℝ) :
    Work.Landing.rayDirection θ ^ (4 ^ k) = Work.Landing.rayDirection ((4 : ℝ) ^ k * θ) := by
  simp only [Work.Landing.rayDirection]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `(e^{2πiθ})^{4^k}` is the direction of the `2k`-fold image angle. -/
theorem rayDirection_pow_angDouble {k : ℕ} (hk : 0 < k) (θ : ℝ) :
    Work.Landing.rayDirection θ ^ (4 ^ k)
      = Work.Landing.rayDirection ((Work.Landing.angDouble)^[2 * k] θ) := by
  rw [rayDirection_pow_four k θ, angDouble_iterate_two_mul hk θ]
  refine (Work.Landing.Rays.rayDirection_eq_of_sub_int ?_).symm
  refine ⟨-⌊(4 : ℝ) ^ k * θ⌋, ?_⟩
  have h := Int.self_sub_fract (a := (4 : ℝ) ^ k * θ)
  push_cast
  linarith

end RayDirection

section RayParametrisation

variable {c : ℂ} {φ : ℂ → ℂ}

/-- The surjectivity clause of `IsDynBottcherHomeo`, phrased as an existential statement about the
point of level `t` at angle `θ`. -/
noncomputable def rayPtWitness
    (hsurj : ∀ w : ℂ, 1 < ‖w‖ → ∃ z : ℂ, Work.ParamRays.Escaping c z ∧ φ z = w)
    (θ : ℝ) (t : ℝ) (ht : 1 < t) :
    ∃ z : ℂ, Work.ParamRays.Escaping c z ∧ φ z = t * Work.Landing.rayDirection θ :=
  hsurj (t * Work.Landing.rayDirection θ) (by
    rw [norm_mul_rayDirection (zero_lt_one.trans ht)]
    exact ht)

/-- **The ray point of level `t` and angle `θ`**: the unique escaping point `z` with
`φ z = t e^{2πiθ}`.  Its existence is the surjectivity half of Böttcher's theorem, taken here as
the explicit hypothesis `hsurj`, which is available from `IsDynBottcherHomeo`. -/
noncomputable def rayPtOf
    (hsurj : ∀ w : ℂ, 1 < ‖w‖ → ∃ z : ℂ, Work.ParamRays.Escaping c z ∧ φ z = w)
    (θ : ℝ) (t : ℝ) : ℂ :=
  if ht : 1 < t then Classical.choose (rayPtWitness hsurj θ t ht) else 0

theorem rayPtOf_spec
    (hsurj : ∀ w : ℂ, 1 < ‖w‖ → ∃ z : ℂ, Work.ParamRays.Escaping c z ∧ φ z = w)
    (θ : ℝ) {t : ℝ} (ht : 1 < t) :
    Work.ParamRays.Escaping c (rayPtOf hsurj θ t) ∧
      φ (rayPtOf hsurj θ t) = t * Work.Landing.rayDirection θ := by
  have h : rayPtOf hsurj θ t = Classical.choose (rayPtWitness hsurj θ t ht) := by
    unfold rayPtOf
    rw [dif_pos ht]
  rw [h]
  exact Classical.choose_spec (rayPtWitness hsurj θ t ht)

theorem rayPtOf_norm
    (hsurj : ∀ w : ℂ, 1 < ‖w‖ → ∃ z : ℂ, Work.ParamRays.Escaping c z ∧ φ z = w)
    (θ : ℝ) {t : ℝ} (ht : 1 < t) : ‖φ (rayPtOf hsurj θ t)‖ = t := by
  rw [(rayPtOf_spec hsurj θ ht).2, norm_mul_rayDirection (zero_lt_one.trans ht)]

theorem rayPtOf_mem_dynRay
    (hsurj : ∀ w : ℂ, 1 < ‖w‖ → ∃ z : ℂ, Work.ParamRays.Escaping c z ∧ φ z = w)
    (θ : ℝ) {t : ℝ} (ht : 1 < t) :
    rayPtOf hsurj θ t ∈ Work.Landing.dynRay c φ θ := by
  refine ⟨(rayPtOf_spec hsurj θ ht).1, ?_⟩
  rw [(rayPtOf_spec hsurj θ ht).2]
  exact ⟨t, ht, rfl⟩

/-- **The level transfer**: the `2k`-th iterate of `T_c` maps the level-`t` point of the ray at
angle `θ` to the level-`t^{4^k}` point of the ray at angle `(angDouble)^[2k] θ`. -/
theorem rayPtOf_transfer {k : ℕ} (hk : 0 < k) (hφ : Work.ParamRays.IsDynBottcher c φ)
    (hinj : ∀ z w : ℂ, Work.ParamRays.Escaping c z → Work.ParamRays.Escaping c w →
      φ z = φ w → z = w)
    (hsurj : ∀ w : ℂ, 1 < ‖w‖ → ∃ z : ℂ, Work.ParamRays.Escaping c z ∧ φ z = w)
    (θ : ℝ) {t : ℝ} (ht : 1 < t) :
    (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (rayPtOf hsurj θ t)
      = rayPtOf hsurj ((Work.Landing.angDouble)^[2 * k] θ) (t ^ (4 ^ k)) := by
  have ht' : 1 < t ^ (4 ^ k) := one_lt_pow₀ ht (by positivity)
  have hesc : Work.ParamRays.Escaping c (rayPtOf hsurj θ t) := (rayPtOf_spec hsurj θ ht).1
  have hesc' : Work.ParamRays.Escaping c
      ((LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (rayPtOf hsurj θ t)) := by
    have h := hesc.iterate (2 * k)
    simpa only [Work.ParamRays.orbit] using h
  refine hinj _ _ hesc' (rayPtOf_spec hsurj _ ht').1 ?_
  have hfun : φ ((LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (rayPtOf hsurj θ t))
      = (φ (rayPtOf hsurj θ t)) ^ (4 ^ k) := by
    have h := Work.ParamRays.IsDynBottcher.functional_iterate hφ hesc k
    simpa only [Work.ParamRays.orbit] using h
  rw [hfun, (rayPtOf_spec hsurj θ ht).2, (rayPtOf_spec hsurj _ ht').2, mul_pow,
    rayDirection_pow_angDouble hk θ, Complex.ofReal_pow]

end RayParametrisation

/-- **The angle of a ray landing at a repelling periodic point is pinned down modulo `1` by the
`2k`-fold angle map.**  If the rays at angles `ψ` and `ψ'` both accumulate at the repelling
periodic point `y` of period `k`, and `4^k ψ ≡ 4^k ψ' (mod 1)`, then `ψ ≡ ψ' (mod 1)`. -/
theorem eq_mod_one_of_rayAccum_of_angDouble_eq {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ} {ψ ψ' : ℝ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    (h1 : Work.Landing.rayAccum c φ ψ = {y}) (h2 : Work.Landing.rayAccum c φ ψ' = {y})
    (h : ∃ m : ℤ, (4 : ℝ) ^ k * ψ = (4 : ℝ) ^ k * ψ' + m) : ∃ mm : ℤ, ψ = ψ' + mm := by
  have hk : 0 < k := hrep.1.1
  have hy : (LeanEval.ComplexAnalysis.Tantibar c)^[k] y = y := hrep.1.2
  obtain ⟨hφb, hinj, hsurj⟩ := isDynBottcherHomeo_of_isDynBottcher hφ
  obtain ⟨m, hm⟩ := h
  -- the two angles agree after the second return
  have ha : (Work.Landing.angDouble)^[2 * k] ψ = (Work.Landing.angDouble)^[2 * k] ψ' := by
    rw [angDouble_iterate_two_mul hk ψ, angDouble_iterate_two_mul hk ψ', hm,
      Int.fract_add_intCast]
  -- the image ray also accumulates at `y`
  have hτy : (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] y = y := by
    rw [show 2 * k = k + k from by ring, Function.iterate_add_apply, hy, hy]
  have hαacc : Work.Landing.rayAccum c φ ((Work.Landing.angDouble)^[2 * k] ψ) = {y} := by
    rw [Work.Landing.rayAccum_iterate hφ ψ (2 * k), h1, Set.image_singleton, hτy]
  -- the local branch of the return map at the repelling point
  obtain ⟨r, r', κ, g, hr, hrr', hκ0, hκ1, hgy, hcontr, hright, hleft⟩ :=
    exists_local_repelling_branch hrep
  -- quantitative landing at the three angles
  obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := rayAccum_entry hφ h1 (ε := r) hr
  obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := rayAccum_entry hφ h2 (ε := r) hr
  obtain ⟨ρα, hρα, hρα'⟩ := rayAccum_entry hφ hαacc (ε := r') (lt_trans hr hrr')
  -- a level at which all three level points lie in the right balls
  set t : ℝ := min (min ρ₁ ρ₂) (ρα ^ (1 / ((4 : ℝ) ^ k))) with htdef
  have ht1 : 1 < t := lt_min (lt_min hρ₁ hρ₂) (Real.one_lt_rpow hρα (by positivity))
  have htρ₁ : t ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have htρ₂ : t ≤ ρ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have htρα : t ^ (4 ^ k) ≤ ρα := by
    have hραpos : 0 < ρα := lt_trans zero_lt_one hρα
    have h4k : ((4 : ℝ) ^ k) ≠ 0 := by positivity
    have hstep : t ^ ((4 : ℝ) ^ k) ≤ ρα := by
      have hroot : t ≤ ρα ^ (1 / ((4 : ℝ) ^ k)) := min_le_right _ _
      calc t ^ ((4 : ℝ) ^ k) ≤ (ρα ^ (1 / ((4 : ℝ) ^ k))) ^ ((4 : ℝ) ^ k) :=
              Real.rpow_le_rpow (le_of_lt (lt_trans zero_lt_one ht1)) hroot (by positivity)
        _ = ρα ^ (1 / ((4 : ℝ) ^ k) * ((4 : ℝ) ^ k)) := (Real.rpow_mul hραpos.le _ _).symm
        _ = ρα ^ (1 : ℝ) := by rw [one_div, inv_mul_cancel₀ h4k]
        _ = ρα := Real.rpow_one ρα
    calc t ^ (4 ^ k) = t ^ (((4 : ℕ) ^ k : ℕ) : ℝ) := (Real.rpow_natCast t (4 ^ k)).symm
      _ = t ^ ((4 : ℝ) ^ k) := by congr 1; push_cast; ring
      _ ≤ ρα := hstep
  have ht' : 1 < t ^ (4 ^ k) := one_lt_pow₀ ht1 (by positivity)
  -- the two level points and their common image
  have hz₁B : ‖rayPtOf hsurj ψ t - y‖ ≤ r :=
    hρ₁' _ (rayPtOf_mem_dynRay hsurj ψ ht1) (by rw [rayPtOf_norm hsurj ψ ht1]; exact htρ₁)
  have hz₂B : ‖rayPtOf hsurj ψ' t - y‖ ≤ r :=
    hρ₂' _ (rayPtOf_mem_dynRay hsurj ψ' ht1) (by rw [rayPtOf_norm hsurj ψ' ht1]; exact htρ₂)
  have hτeq : (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (rayPtOf hsurj ψ t)
      = (LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (rayPtOf hsurj ψ' t) := by
    rw [rayPtOf_transfer hk hφ hinj hsurj ψ ht1, rayPtOf_transfer hk hφ hinj hsurj ψ' ht1, ha]
  have hz₁B' : ‖(LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (rayPtOf hsurj ψ t) - y‖ ≤ r' := by
    rw [rayPtOf_transfer hk hφ hinj hsurj ψ ht1]
    exact hρα' _ (rayPtOf_mem_dynRay hsurj _ ht') (by rw [rayPtOf_norm hsurj _ ht']; exact htρα)
  have hz₂B' : ‖(LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (rayPtOf hsurj ψ' t) - y‖ ≤ r' := by
    rw [← hτeq]; exact hz₁B'
  -- local injectivity of the return map forces the two level points to coincide
  have heq : rayPtOf hsurj ψ t = rayPtOf hsurj ψ' t := by
    calc rayPtOf hsurj ψ t
        = g ((LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (rayPtOf hsurj ψ t)) :=
          (hleft _ hz₁B hz₁B').symm
      _ = g ((LeanEval.ComplexAnalysis.Tantibar c)^[2 * k] (rayPtOf hsurj ψ' t)) := by rw [hτeq]
      _ = rayPtOf hsurj ψ' t := hleft _ hz₂B hz₂B'
  -- hence the ray directions agree, so the angles are congruent modulo `1`
  have hdir : Work.Landing.rayDirection ψ = Work.Landing.rayDirection ψ' := by
    have h : (t : ℂ) * Work.Landing.rayDirection ψ = (t : ℂ) * Work.Landing.rayDirection ψ' := by
      rw [← (rayPtOf_spec hsurj ψ ht1).2, ← (rayPtOf_spec hsurj ψ' ht1).2, heq]
    exact mul_left_cancel₀ (by simpa using ne_of_gt (lt_trans zero_lt_one ht1)) h
  rw [Work.Landing.rayDirection] at hdir
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hdir
  refine ⟨n, ?_⟩
  have h3 := congrArg Complex.im hn
  simp at h3
  nlinarith [h3, Real.pi_pos]

end Work.LandLeaves
