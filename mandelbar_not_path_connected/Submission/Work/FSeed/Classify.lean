/-
Copyright: subproject `Submission/Work/FSeed/` of `mandelbar_not_path_connected`.

# FSeed: the classification of the root-parabolic parameter

This file carries out **step 3** of the FSeed route
(`NOTES_LEAD_mandelbar_EL_F_contracts.md` §7.3, row `FSeed`): from the classical input bundle
`Work.FSeed.RootParabolicInput c` — the ray `R(α₁)` lands at `z₁`, `z₁` lies on a cycle of
**exact odd** period `k` with second-return multiplier `1`, together with the classical local ray
portrait of `z₁` **modulo `1`**, the simplicity of `z₁` (`simple`), the critical-orbit data, the
wake export and the parameter-ray limit condition — it derives

* `odd_period_five` — the odd period is **exactly `5`** (this is the classification: odd `k` with
  `T_c^[k] z₁ = z₁` and `T_c^[10] z₁ = z₁` gives `k ∣ 10`, so `k ∈ {1,5}`, and `k = 1` is excluded
  because then all ten angles `T^i α₁` would land at `z₁`, contra the portrait);
* `per_half`, `mult_five` — `T_c^[5] z₁ = z₁` and `multiplier2 c 5 z₁ = 1`;
* `coLands_α₂` — the **second root ray `α₂` co-lands** (ray-image lemma, since `T_c^[5] z₁ = z₁`,
  and `T^[5] α₁ = α₂`);
* `not_cusp` — `z₁` is **not a cusp**: this is now the *field* `RootParabolicInput.simple`, a
  classical per-parameter fact about the seed (`Inputs.lean`).  It is no longer derived from the
  local portrait: the ray count at `z₁` is a statement modulo `1` only, and the clause "at a cusp
  at most one ray lands" is *false* at the cusps ending the root arc, where three rays land
  (`NOTES_LEAD_mandelbar_seedsimple.md` §1, §2);
* `portrait_exact` — every ray landing at `z₁` has angle `α₁` or `α₂` **modulo `1`**;
* `rootParabolic_of_input` — the structure `Work.EL.RootParabolic` of `ELTop/Defs.lean`.

## The two inputs that are *not* assumed

* the parity/period arithmetic is done here (`Portrait/alpha_orbit`, `API/dvd_of_fixed`,
  `API/odd_dvd_ten`);
* the multiplier of the second return map at period `5` is read off at the odd period (`mult_five`),
  no separate hypothesis at period `5` is used.
-/
import Submission.Work.FSeed.Defs
import Submission.Work.FSeed.Inputs
import Submission.Work.FSeed.RootParabolic
import Submission.Work.FSeed.Portrait.alpha_orbit
import Submission.Work.FSeed.API.fixed_of_iterate_eq_five
import Submission.Work.FSeed.API.dvd_of_fixed
import Submission.Work.FSeed.API.deriv_iterate_periodic
import Submission.Work.Landing.Land.Landing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function
open scoped Topology

noncomputable section

namespace Work.FSeed

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The arithmetic of the α-orbit, in the form used below -/

/-- `T^[10]` fixes `α₁`. -/
theorem alpha_ten : (T^[10]) α₁ = α₁ := (Work.FSeed.Portrait.alpha_orbit).1

/-- `T^[5] α₁ = α₂`. -/
theorem alpha_orbit_five : (T^[5]) α₁ = α₂ := (Work.FSeed.Portrait.alpha_orbit).2.1

/-- `α₁ ≠ α₂`. -/
theorem alpha_one_ne_two : α₁ ≠ α₂ := (Work.FSeed.Portrait.alpha_orbit).2.2.2.1

/-- The ten iterates `T^[i] α₁`, `i < 10`, are pairwise distinct. -/
theorem alpha_orbit_injective {i j : ℕ} (hi : i < 10) (hj : j < 10) (hij : i ≠ j) :
    (T^[i]) α₁ ≠ (T^[j]) α₁ :=
  (Work.FSeed.Portrait.alpha_orbit).2.2.2.2.1 i j hi hj hij

/-- `Int.fract α₁ = α₁`: the first root angle is already normalised to `[0,1)`. -/
theorem fract_α₁ : Int.fract α₁ = α₁ := by
  apply Int.fract_eq_self.mpr
  norm_num [α₁]

/-- `Int.fract α₂ = α₂`: the second root angle is already normalised to `[0,1)`. -/
theorem fract_α₂ : Int.fract α₂ = α₂ := by
  apply Int.fract_eq_self.mpr
  norm_num [α₂]

/-- Every iterate `(T^[n]) α₁` of the first root angle lies in `[0,1)` — `T θ = -2θ mod 1` is
normalised by construction.  This is what converts the modulo-`1` portrait clause back into an
equality of angles along the α-orbit. -/
theorem fract_T_iterate_α₁ (n : ℕ) : Int.fract ((T^[n]) α₁) = (T^[n]) α₁ := by
  induction n with
  | zero => simpa using fract_α₁
  | succ n ih =>
    rw [Function.iterate_succ_apply', T_apply, Int.fract_fract]

/-- `α₁` is a periodic angle. -/
theorem isPeriodicAngle_α₁ : Work.Landing.IsPeriodicAngle α₁ := ⟨10, by norm_num, alpha_ten⟩

/-- `α₂` is a periodic angle. -/
theorem isPeriodicAngle_α₂ : Work.Landing.IsPeriodicAngle α₂ := by
  refine ⟨10, by norm_num, ?_⟩
  change (T^[10]) α₂ = α₂
  have h1 : (T^[5]) α₁ = α₂ := alpha_orbit_five
  have h2 : (T^[5]) α₂ = α₁ := (Work.FSeed.Portrait.alpha_orbit).2.2.1
  rw [show (10 : ℕ) = 5 + 5 from rfl, Function.iterate_add_apply, h2, h1]

/-- `Tsq c` is entire. -/
theorem differentiable_Tsq (c : ℂ) : Differentiable ℂ (Work.Landing.Tsq c) := by
  change Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
  fun_prop

/-- **The multiplier of an iterate at a periodic point is a power of the multiplier**: for `z`
fixed by `(Tsq c)^[m]`, `multiplier2 c (m*n) z = (multiplier2 c m z)^n`. -/
theorem multiplier2_iterate_periodic {c z : ℂ} {m n : ℕ} (hm : 0 < m)
    (hper : ((Work.Landing.Tsq c)^[m]) z = z) :
    Work.Landing.multiplier2 c (m * n) z = (Work.Landing.multiplier2 c m z) ^ n :=
  Work.FSeed.API.deriv_iterate_periodic (f := Work.Landing.Tsq c) (differentiable_Tsq c) hm hper n

/-! ## Step 3: the classification -/

/-- `T_c^[10]` fixes `z₁`: the ray-image lemma applied to `R(α₁)`, whose angle has period `10`. -/
theorem ten_per {c : ℂ} (h : RootParabolicInput c) : (Tantibar c)^[10] h.z₁ = h.z₁ := by
  have h1 := Work.Landing.landsAt_iterate h.ray₁ 10
  rw [alpha_ten] at h1
  exact Work.Landing.landsAt_unique h1 h.ray₁

/-- **`z₁` is not a fixed point of `T_c`**: otherwise every iterate of `α₁` would land at `z₁`,
and the three angles `α₁`, `Tα₁`, `T²α₁` have pairwise distinct fractional parts
(`fract_T_iterate_α₁` together with `alpha_orbit_injective`) — contra the modulo-`1` local
portrait. -/
theorem fixed_excluded {c : ℂ} (h : RootParabolicInput c) : Tantibar c h.z₁ ≠ h.z₁ := by
  intro hfix
  have hfixn : ∀ n : ℕ, (Tantibar c)^[n] h.z₁ = h.z₁ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, hfix]
  have hland : ∀ n : ℕ, Work.Landing.landsAt c ((T^[n]) α₁) h.z₁ := by
    intro n
    have h1 := Work.Landing.landsAt_iterate h.ray₁ n
    rwa [hfixn n] at h1
  obtain h01 | h02 | h12 := h.portrait.two_rays ((T^[0]) α₁) ((T^[1]) α₁) ((T^[2]) α₁)
    (hland 0) (hland 1) (hland 2)
  · rw [fract_T_iterate_α₁ 0, fract_T_iterate_α₁ 1] at h01
    exact alpha_orbit_injective (by norm_num) (by norm_num) (by norm_num) h01
  · rw [fract_T_iterate_α₁ 0, fract_T_iterate_α₁ 2] at h02
    exact alpha_orbit_injective (by norm_num) (by norm_num) (by norm_num) h02
  · rw [fract_T_iterate_α₁ 1, fract_T_iterate_α₁ 2] at h12
    exact alpha_orbit_injective (by norm_num) (by norm_num) (by norm_num) h12

/-- **The odd period is exactly `5`.**  An odd period `k` divides `10` (the ray-image lemma gives
`T_c^[10] z₁ = z₁` and the exact period divides every period), so `k ∈ {1, 5}`, and `k = 1` is
excluded by the portrait. -/
theorem odd_period_five {c : ℂ} (h : RootParabolicInput c) :
    ∃ k : ℕ, Odd k ∧ (Tantibar c)^[k] h.z₁ = h.z₁ ∧
      (∀ j : ℕ, 0 < j → j < k → (Tantibar c)^[j] h.z₁ ≠ h.z₁) ∧
      Work.Landing.multiplier2 c k h.z₁ = 1 ∧ k = 5 := by
  obtain ⟨k, hk, hper, hmin, hmult⟩ := h.odd_per
  have hdvd : k ∣ 10 := Work.FSeed.API.dvd_of_fixed hk.pos hmin hper (ten_per h)
  rcases Work.FSeed.API.odd_dvd_ten hk hdvd with h1 | h5
  · exact absurd (by rw [h1] at hper; exact hper) (fixed_excluded h)
  · exact ⟨k, hk, hper, hmin, hmult, h5⟩

/-- The period-`5` condition. -/
theorem per_half {c : ℂ} (h : RootParabolicInput c) : (Tantibar c)^[5] h.z₁ = h.z₁ := by
  obtain ⟨k, _, hper, _, _, hk5⟩ := odd_period_five h
  rw [hk5] at hper
  exact hper

/-- The second-return multiplier at period `5` is `1` (read off at the odd period). -/
theorem mult_five {c : ℂ} (h : RootParabolicInput c) :
    Work.Landing.multiplier2 c 5 h.z₁ = 1 := by
  obtain ⟨k, _, _, _, hmult, hk5⟩ := odd_period_five h
  rw [hk5] at hmult
  exact hmult

/-- The exactness of the period. -/
theorem exact_period {c : ℂ} (h : RootParabolicInput c) :
    ∀ j ∈ Finset.Ioo 0 5, (Tantibar c)^[j] h.z₁ ≠ h.z₁ := by
  obtain ⟨k, _, _, hmin, _, hk5⟩ := odd_period_five h
  rw [hk5] at hmin
  intro j hj
  exact hmin j (Finset.mem_Ioo.mp hj).1 (Finset.mem_Ioo.mp hj).2

/-- **The second root ray co-lands**: the ray-image lemma applied five times to `R(α₁)`, since
`T_c^[5] z₁ = z₁`, gives the landing of `R(T^5 α₁) = R(α₂)`. -/
theorem coLands_α₂ {c : ℂ} (h : RootParabolicInput c) : Work.Landing.landsAt c α₂ h.z₁ := by
  have h1 := Work.Landing.landsAt_iterate h.ray₁ 5
  rw [alpha_orbit_five, per_half h] at h1
  exact h1

/-- **`z₁` is not a cusp.**  This is the field `RootParabolicInput.simple`; `Inputs.lean` records
its classical provenance (HS Prop. 2.5, Lemma 3.1; MNS Thm 1.2, Lemma 2.9, Thm 3.2; IM16 Thm 1.1,
Cor. 5.2).  It is *not* derived here from the local portrait: the ray-theoretic statement that a
cusp forces a `T⁵`-fixed ray to land costs 35–60K
(`NOTES_LEAD_mandelbar_seedsimple.md` §2, §5). -/
theorem not_cusp {c : ℂ} (h : RootParabolicInput c) : iteratedDeriv 2 (F c) h.z₁ ≠ 0 :=
  h.simple

/-- **The portrait at `z₁` is exactly the α-pair, modulo `1`**: every ray landing at `z₁` has
angle `α₁` or `α₂` modulo `1`.  This is the mod-`1` form of the portrait clause `two_rays` along
the α-orbit, and the shape in which it is consumed downstream. -/
theorem portrait_exact {c : ℂ} (h : RootParabolicInput c) {θ : ℝ}
    (hθ : Work.Landing.landsAt c θ h.z₁) : Int.fract θ = α₁ ∨ Int.fract θ = α₂ := by
  obtain h1 | h1 | h1 := h.portrait.two_rays θ α₁ α₂ hθ h.ray₁ (coLands_α₂ h)
  · exact Or.inl (by rw [← fract_α₁]; exact h1)
  · exact Or.inr (by rw [← fract_α₂]; exact h1)
  · exact absurd (by rw [fract_α₁, fract_α₂] at h1; exact h1) alpha_one_ne_two

/-- **The classification, assembled**: the classical input bundle produces the structure
`Work.EL.RootParabolic` (`ELTop/Defs.lean`) consumed by the EL and F areas. -/
theorem rootParabolic_of_input {c : ℂ} (h : RootParabolicInput c) :
    Nonempty (Work.EL.RootParabolic c) :=
  ⟨{ φ := Work.ParamRays.dynPhiOf c
     bottcher := Work.ParamRays.isDynBottcher_dynPhiOf h.dyn.1
     hN := Work.ParamRays.dynNakane h.dyn
     z₁ := h.z₁
     per_half := per_half h
     ne_per := exact_period h
     mult := mult_five h
     simple := not_cusp h
     rays := ⟨h.ray₁, coLands_α₂ h⟩
     crit := h.crit
     wake := h.wake }⟩

end Work.FSeed

end
