import Mathlib
import Submission.Work.ParamRays.isDynBottcher_unique
import Submission.Work.LandLeaves.All
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.preconnected_rayAccum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MandelFinal.Quarter

open LeanEval.ComplexAnalysis (Tantibar)

/-- `Tsq c` is the second iterate of the antiholomorphic map `T_c`: `Tsq c = (T_c)^[2]`. -/
private theorem Tsq_eq_iterate_two (c : ℂ) : (Tantibar c)^[2] = Work.Landing.Tsq c := by
  funext z
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp [Work.Landing.Tsq_apply, Tantibar]

/-- **The angle map `θ ↦ Int.fract (4 θ)` is injective on the rays landing at the cusp `1/2`.**

Port of `Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq` (the same statement for a
*repelling* periodic point) to the parabolic cusp `1/2` of `T_{1/4}`, with `k = 1` (so that the
second return map is `τ = Tsq (1/4) = (T_{1/4})^[2]` and its angle map is `θ ↦ Int.fract (4 θ)`).
The proof is the same: parametrise the two rays by the Böttcher level, use the level transfer
`Work.LandLeaves.rayPtOf_transfer` (the second return map sends the level-`t` point of the ray at
angle `ψ` to the level-`t ^ 4` point of the ray at angle `Int.fract (4 ψ)`), the quantitative
landing `Work.LandLeaves.rayAccum_entry`, the injectivity/surjectivity of the Böttcher coordinate
(`Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher`) and the *left inverse* of `τ` on a small
ball around `1/2` (`hlocal`) to force the two level points to coincide, whence the angles agree
modulo `1`.  In contrast with the repelling case only the left-inverse property of `hlocal` is
used, never a contraction.  Use `Work.ParamRays.isDynBottcher_unique` to replace the two
existential Böttcher coordinates of the `landsAt` hypotheses by a common one. -/
theorem angleInjective_quarter
    (hfix : Work.Landing.Tsq (1 / 4 : ℂ) (1 / 2) = 1 / 2)
    (hlocal : ∃ (r r' : ℝ) (g : ℂ → ℂ), 0 < r ∧ 0 < r' ∧ ∀ z : ℂ,
      ‖z - (1 / 2 : ℂ)‖ ≤ r → ‖Work.Landing.Tsq (1 / 4 : ℂ) z - (1 / 2 : ℂ)‖ ≤ r' →
      g (Work.Landing.Tsq (1 / 4 : ℂ) z) = z)
    {θ θ' : ℝ}
    (hθ : Work.Landing.landsAt (1 / 4 : ℂ) θ (1 / 2))
    (hθ' : Work.Landing.landsAt (1 / 4 : ℂ) θ' (1 / 2))
    (h : ∃ m : ℤ, (4 : ℝ) * θ = (4 : ℝ) * θ' + m) : ∃ mm : ℤ, θ = θ' + mm := by
  -- the second return map is the holomorphic `Tsq (1/4) = (T_{1/4})^[2]`, fixing the cusp
  have hτy : (Tantibar (1 / 4 : ℂ))^[2] (1 / 2 : ℂ) = 1 / 2 := by
    rw [Tsq_eq_iterate_two]
    exact hfix
  -- a Böttcher coordinate is available from each landing hypothesis
  obtain ⟨φ, hφ, h1⟩ := hθ
  obtain ⟨φ', hφ', h2₀⟩ := hθ'
  -- replace the second coordinate by the first, using uniqueness of the Böttcher coordinate
  have h2 : Work.Landing.rayAccum (1 / 4 : ℂ) φ θ' = {(1 / 2 : ℂ)} :=
    (Work.Landing.rayAccum_congr
        (fun w hw => Work.ParamRays.isDynBottcher_unique hφ' hφ hw) θ').symm.trans h2₀
  -- injectivity and surjectivity of the Böttcher coordinate
  obtain ⟨_, hinj, hsurj⟩ := Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher hφ
  -- the two angles agree after the second return
  have ha : (Work.Landing.angDouble)^[2] θ = (Work.Landing.angDouble)^[2] θ' := by
    have e1 : (Work.Landing.angDouble)^[2] θ = Int.fract (4 * θ) := by
      simpa using Work.LandLeaves.angDouble_iterate_two_mul (k := 1) (by norm_num) θ
    have e2 : (Work.Landing.angDouble)^[2] θ' = Int.fract (4 * θ') := by
      simpa using Work.LandLeaves.angDouble_iterate_two_mul (k := 1) (by norm_num) θ'
    obtain ⟨m, hm⟩ := h
    rw [e1, e2, hm, Int.fract_add_intCast]
  -- the image ray also accumulates at the cusp
  have hαacc : Work.Landing.rayAccum (1 / 4 : ℂ) φ ((Work.Landing.angDouble)^[2] θ) = {(1 / 2 : ℂ)} := by
    rw [Work.Landing.rayAccum_iterate hφ θ 2, h1, Set.image_singleton, hτy]
  -- the local left inverse of the second return map at the cusp
  obtain ⟨r, r', g, hr, hr', hgy⟩ := hlocal
  -- quantitative landing at the three angles
  obtain ⟨ρ₁, hρ₁, hρ₁'⟩ := Work.LandLeaves.rayAccum_entry hφ h1 (ε := r) hr
  obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := Work.LandLeaves.rayAccum_entry hφ h2 (ε := r) hr
  obtain ⟨ρα, hρα, hρα'⟩ := Work.LandLeaves.rayAccum_entry hφ hαacc (ε := r') hr'
  -- a level at which all three level points lie in the right balls
  set t : ℝ := min (min ρ₁ ρ₂) (ρα ^ (1 / 4 : ℝ)) with htdef
  have ht1 : 1 < t := lt_min (lt_min hρ₁ hρ₂) (Real.one_lt_rpow hρα (by norm_num : (0 : ℝ) < 1 / 4))
  have htρ₁ : t ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have htρ₂ : t ≤ ρ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have htρα : t ^ 4 ≤ ρα := by
    have hραpos : 0 < ρα := lt_trans zero_lt_one hρα
    have hstep : t ^ (4 : ℝ) ≤ ρα := by
      have hroot : t ≤ ρα ^ (1 / 4 : ℝ) := min_le_right _ _
      calc t ^ (4 : ℝ) ≤ (ρα ^ (1 / 4 : ℝ)) ^ (4 : ℝ) :=
            Real.rpow_le_rpow (le_of_lt (lt_trans zero_lt_one ht1)) hroot (by norm_num)
        _ = ρα ^ ((1 / 4 : ℝ) * 4) := (Real.rpow_mul hραpos.le _ _).symm
        _ = ρα ^ (1 : ℝ) := by norm_num
        _ = ρα := Real.rpow_one ρα
    calc t ^ 4 = t ^ ((4 : ℕ) : ℝ) := (Real.rpow_natCast t 4).symm
      _ = t ^ (4 : ℝ) := by norm_num
      _ ≤ ρα := hstep
  have ht' : 1 < t ^ 4 := one_lt_pow₀ ht1 (by norm_num)
  -- the two level points and their common image
  have hz₁B : ‖Work.LandLeaves.rayPtOf hsurj θ t - (1 / 2 : ℂ)‖ ≤ r :=
    hρ₁' _ (Work.LandLeaves.rayPtOf_mem_dynRay hsurj θ ht1)
      (by rw [Work.LandLeaves.rayPtOf_norm hsurj θ ht1]; exact htρ₁)
  have hz₂B : ‖Work.LandLeaves.rayPtOf hsurj θ' t - (1 / 2 : ℂ)‖ ≤ r :=
    hρ₂' _ (Work.LandLeaves.rayPtOf_mem_dynRay hsurj θ' ht1)
      (by rw [Work.LandLeaves.rayPtOf_norm hsurj θ' ht1]; exact htρ₂)
  have htr₁ : (Tantibar (1 / 4 : ℂ))^[2] (Work.LandLeaves.rayPtOf hsurj θ t)
      = Work.LandLeaves.rayPtOf hsurj ((Work.Landing.angDouble)^[2] θ) (t ^ 4) := by
    simpa using Work.LandLeaves.rayPtOf_transfer (k := 1) (by norm_num) hφ hinj hsurj θ ht1
  have htr₂ : (Tantibar (1 / 4 : ℂ))^[2] (Work.LandLeaves.rayPtOf hsurj θ' t)
      = Work.LandLeaves.rayPtOf hsurj ((Work.Landing.angDouble)^[2] θ') (t ^ 4) := by
    simpa using Work.LandLeaves.rayPtOf_transfer (k := 1) (by norm_num) hφ hinj hsurj θ' ht1
  have hτeq : (Tantibar (1 / 4 : ℂ))^[2] (Work.LandLeaves.rayPtOf hsurj θ t)
      = (Tantibar (1 / 4 : ℂ))^[2] (Work.LandLeaves.rayPtOf hsurj θ' t) := by
    rw [htr₁, htr₂, ha]
  have hz₁B' : ‖(Tantibar (1 / 4 : ℂ))^[2] (Work.LandLeaves.rayPtOf hsurj θ t) - (1 / 2 : ℂ)‖ ≤ r' := by
    rw [htr₁]
    exact hρα' _ (Work.LandLeaves.rayPtOf_mem_dynRay hsurj _ ht')
      (by rw [Work.LandLeaves.rayPtOf_norm hsurj _ ht']; exact htρα)
  have hz₂B' : ‖(Tantibar (1 / 4 : ℂ))^[2] (Work.LandLeaves.rayPtOf hsurj θ' t) - (1 / 2 : ℂ)‖ ≤ r' := by
    rw [← hτeq]
    exact hz₁B'
  -- the local left inverse, phrased for the iterate `(T_{1/4})^[2] = Tsq (1/4)`
  have hleft : ∀ z : ℂ, ‖z - (1 / 2 : ℂ)‖ ≤ r →
      ‖(Tantibar (1 / 4 : ℂ))^[2] z - (1 / 2 : ℂ)‖ ≤ r' →
      g ((Tantibar (1 / 4 : ℂ))^[2] z) = z := by
    intro z hz hz'
    rw [Tsq_eq_iterate_two] at hz' ⊢
    exact hgy z hz hz'
  -- the two level points coincide
  have heq : Work.LandLeaves.rayPtOf hsurj θ t = Work.LandLeaves.rayPtOf hsurj θ' t := by
    calc Work.LandLeaves.rayPtOf hsurj θ t
        = g ((Tantibar (1 / 4 : ℂ))^[2] (Work.LandLeaves.rayPtOf hsurj θ t)) :=
          (hleft _ hz₁B hz₁B').symm
      _ = g ((Tantibar (1 / 4 : ℂ))^[2] (Work.LandLeaves.rayPtOf hsurj θ' t)) := by rw [hτeq]
      _ = Work.LandLeaves.rayPtOf hsurj θ' t := hleft _ hz₂B hz₂B'
  -- hence the ray directions agree, so the angles are congruent modulo `1`
  have hdir : Work.Landing.rayDirection θ = Work.Landing.rayDirection θ' := by
    have h : (t : ℂ) * Work.Landing.rayDirection θ = (t : ℂ) * Work.Landing.rayDirection θ' := by
      rw [← (Work.LandLeaves.rayPtOf_spec hsurj θ ht1).2,
        ← (Work.LandLeaves.rayPtOf_spec hsurj θ' ht1).2, heq]
    exact mul_left_cancel₀ (by simpa using ne_of_gt (lt_trans zero_lt_one ht1)) h
  rw [Work.Landing.rayDirection] at hdir
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hdir
  refine ⟨n, ?_⟩
  have h3 := congrArg Complex.im hn
  simp at h3
  nlinarith [h3, Real.pi_pos]

end Work.MandelFinal.Quarter
