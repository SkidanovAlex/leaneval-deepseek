/-
# `nest_W0`: the base arc `(α₁, α₂)` misses every `T`-preimage arc of the `z₁`-nest

The hypothesis `hcv` of the pull-back chain `Work.ELAssembly.coLand_Q` asks that `c` lie on the
*complement* of every unwrapped arc `nestArc (9 - t) (nestPair (bAng n, bAng' n) t)` that the
level-`n` pair of the `z₁`-nest feeds to `pb1Top` at step `t`.  `cv_mem_arcSide_of_W0` reduces
this to the purely angle-theoretic statement recorded here: every `θ` of the base arc
`(α₁, α₂) = (371/1023, 404/1023)` lies in the arc running from the *second* angle of
`nestArc (9 - t) (nestPair (bAng n, bAng' n) t)` back to its *first* angle (i.e. in the
complement of that arc).

Every quantity involved is affine in `Y = 1024⁻ⁿ ∈ (0, 1]`, and for each of the ten steps
`t < 10` the complementary arc is an explicit interval containing the closed base arc
`[α₁, α₂]`; the ten cases are the elementary inequalities computed below.
-/
import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELNest.Chain
import Submission.Work.ELNest.nestPair_nest

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Work.EL

set_option maxHeartbeats 2000000

/-! ## Angle arithmetic on `ℝ/ℤ` -/

/-- `InArc θ b a` holds as soon as `b < θ < a` and the arc `(b, a)` has length `< 1`. -/
private lemma InArc_of_lt {θ b a : ℝ} (hbθ : b < θ) (hθa : θ < a) (hba : a - b < 1) :
    InArc θ b a := by
  unfold InArc arcLen
  have h1 : Int.fract (θ - b) = θ - b := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have h2 : Int.fract (a - b) = a - b := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [h1, h2]
  exact ⟨by linarith, by linarith⟩

/-- `InArc` is invariant under adding integers to the two end points. -/
private lemma InArc_int_add (θ b a : ℝ) (k l : ℤ) :
    InArc θ (b + (k:ℝ)) (a + (l:ℝ)) ↔ InArc θ b a := by
  unfold InArc arcLen
  have h1 : Int.fract (θ - (b + (k:ℝ))) = Int.fract (θ - b) := by
    rw [show θ - (b + (k:ℝ)) = (θ - b) - (k:ℝ) by ring, Int.fract_sub_intCast]
  have h2 : Int.fract (a + (l:ℝ) - (b + (k:ℝ))) = Int.fract (a - b) := by
    rw [show a + (l:ℝ) - (b + (k:ℝ)) = (a - b) + ((l - k : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
  rw [h1, h2]

/-- `InArc θ b a` follows from the same statement at the representative
`α₁ + Int.fract (θ - α₁)` of `θ` in `[0, 1)`. -/
private lemma InArc_of_fract (θ b a : ℝ)
    (h : InArc (alpha1 + Int.fract (θ - alpha1)) b a) : InArc θ b a := by
  have hθb : Int.fract (θ - b)
      = Int.fract (alpha1 + Int.fract (θ - alpha1) - b) := by
    rw [show θ - b = (alpha1 + Int.fract (θ - alpha1) - b) + (((⌊θ - alpha1⌋ : ℤ)) : ℝ) by
      linarith [Int.fract_add_floor (θ - alpha1)],
      Int.fract_add_intCast]
  unfold InArc at h ⊢
  rw [hθb]
  exact h

/-- The base arc has length `33/1023`. -/
private lemma arcLen_alpha : arcLen alpha1 alpha2 = (33:ℝ)/1023 := by
  rw [arcLen, alpha1, alpha2]
  norm_num

/-- **The base arc is contained in any interval `(b, a)` of length `< 1` that brackets it.**
This is the form in which the ten cases are carried out: it suffices to exhibit integers
`m`, `l` with `b + m < α₁`, `α₂ < a + l` and `(a + l) - (b + m) < 1` (and then `InArc_int_add`
transfers the statement back to the unshifted end points `b`, `a`). -/
private lemma InArc_of_bounds {θ b a : ℝ} (hθ : InArc θ alpha1 alpha2)
    (hb : b < alpha1) (ha : alpha2 < a) (hba : a - b < 1) : InArc θ b a := by
  obtain ⟨hp, hq⟩ := hθ
  rw [arcLen_alpha] at hq
  apply InArc_of_fract
  apply InArc_of_lt
  · rw [alpha1] at hb hp ⊢; linarith
  · rw [alpha1] at hq ⊢; rw [alpha2] at ha; linarith
  · exact hba

/-! ## The two branches of `nestArc` -/

private lemma nestArc_near {j : ℕ} (p : ℝ × ℝ) (h : j % 5 = 3 ∨ j % 5 = 4) :
    Work.ELNest.nestArc j p = (p.2, p.2 + arcLen p.2 p.1) := by
  unfold Work.ELNest.nestArc
  rw [ite_eq_left h]

private lemma nestArc_far {j : ℕ} (p : ℝ × ℝ) (h : ¬ (j % 5 = 3 ∨ j % 5 = 4)) :
    Work.ELNest.nestArc j p = (p.1, p.1 + arcLen p.1 p.2) := by
  unfold Work.ELNest.nestArc
  rw [ite_eq_right h]

/-! ## The affine forms of the angles `bAng`, `bAng'` -/

private lemma bAng_eq (n : ℕ) :
    Work.ELNest.bAng n = ((371:ℝ)/1023) - ((15:ℝ)/349184) * ((1024:ℝ)^n)⁻¹ := by
  rw [Work.ELNest.bAng, Work.ELNest.alpha1, Work.ELNest.beta0, div_eq_mul_inv]; ring

private lemma bAng'_eq (n : ℕ) :
    Work.ELNest.bAng' n = ((404:ℝ)/1023) + ((139:ℝ)/349184) * ((1024:ℝ)^n)⁻¹ := by
  rw [Work.ELNest.bAng', Work.ELNest.alpha2, Work.ELNest.beta0', div_eq_mul_inv]; ring

theorem nest_W0 {c : ℂ} (n t : ℕ) (ht : t < 10) : ∀ θ : ℝ, Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ (Work.ELNest.nestArc (9 - t) (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) t)).2 (Work.ELNest.nestArc (9 - t) (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) t)).1 := by
  intro θ hθ
  set Y : ℝ := ((1024:ℝ)^n)⁻¹ with hYdef
  have hY : 0 < Y := by rw [hYdef]; positivity
  have hY1 : Y ≤ 1 := by
    rw [hYdef]; apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 1024)
  -- the explicit affine form of the level-`n` pair
  have hP10 : (Work.ELNest.bAng n, Work.ELNest.bAng' n)
      = (((371:ℝ)/1023) - ((15:ℝ)/349184)*Y, ((404:ℝ)/1023) + ((139:ℝ)/349184)*Y) := by
    rw [bAng_eq n, bAng'_eq n, ← hYdef]
  -- the chain of the ten steps, in the explicit affine forms
  have hP0 : Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 0
      = (((371:ℝ)/1023) - ((15:ℝ)/349184)*Y, ((404:ℝ)/1023) + ((139:ℝ)/349184)*Y) := by
    show (Work.ELNest.bAng n, Work.ELNest.bAng' n) = _
    exact hP10
  have hP1 : Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 1
      = (((326:ℝ)/1023) + ((15:ℝ)/698368)*Y, ((821:ℝ)/1023) - ((139:ℝ)/698368)*Y) := by
    show Work.ELNest.nestStep 9 (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 0) = _
    rw [hP0, Work.ELNest.nestStep_9 Y hY hY1]
  have hP2 : Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 2
      = (((860:ℝ)/1023) - ((15:ℝ)/1396736)*Y, ((101:ℝ)/1023) + ((139:ℝ)/1396736)*Y) := by
    show Work.ELNest.nestStep 8 (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 1) = _
    rw [hP1, Work.ELNest.nestStep_8 Y hY hY1]
  have hP3 : Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 3
      = (((461:ℝ)/1023) - ((139:ℝ)/2793472)*Y, ((593:ℝ)/1023) + ((15:ℝ)/2793472)*Y) := by
    show Work.ELNest.nestStep 7 (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 2) = _
    rw [hP2, Work.ELNest.nestStep_7 Y hY hY1]
  have hP4 : Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 4
      = (((215:ℝ)/1023) - ((15:ℝ)/5586944)*Y, ((281:ℝ)/1023) + ((139:ℝ)/5586944)*Y) := by
    show Work.ELNest.nestStep 6 (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 3) = _
    rw [hP3, Work.ELNest.nestStep_6 Y hY hY1]
  have hP5 : Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 5
      = (((371:ℝ)/1023) - ((139:ℝ)/11173888)*Y, ((404:ℝ)/1023) + ((15:ℝ)/11173888)*Y) := by
    show Work.ELNest.nestStep 5 (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 4) = _
    rw [hP4, Work.ELNest.nestStep_5 Y hY hY1]
  have hP6 : Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 6
      = (((326:ℝ)/1023) + ((139:ℝ)/22347776)*Y, ((821:ℝ)/1023) - ((15:ℝ)/22347776)*Y) := by
    show Work.ELNest.nestStep 4 (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 5) = _
    rw [hP5, Work.ELNest.nestStep_4 Y hY hY1]
  have hP7 : Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 7
      = (((860:ℝ)/1023) - ((139:ℝ)/44695552)*Y, ((101:ℝ)/1023) + ((15:ℝ)/44695552)*Y) := by
    show Work.ELNest.nestStep 3 (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 6) = _
    rw [hP6, Work.ELNest.nestStep_3 Y hY hY1]
  have hP8 : Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 8
      = (((461:ℝ)/1023) - ((15:ℝ)/89391104)*Y, ((593:ℝ)/1023) + ((139:ℝ)/89391104)*Y) := by
    show Work.ELNest.nestStep 2 (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 7) = _
    rw [hP7, Work.ELNest.nestStep_2 Y hY hY1]
  have hP9 : Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 9
      = (((215:ℝ)/1023) - ((139:ℝ)/178782208)*Y, ((281:ℝ)/1023) + ((15:ℝ)/178782208)*Y) := by
    show Work.ELNest.nestStep 1 (Work.ELNest.nestPair (Work.ELNest.bAng n, Work.ELNest.bAng' n) 8) = _
    rw [hP8, Work.ELNest.nestStep_1 Y hY hY1]
  interval_cases t
  · -- t = 0 : near arc of `p₁₀`
    rw [hP0, nestArc_near _ (by decide : (9:ℕ) % 5 = 3 ∨ (9:ℕ) % 5 = 4)]
    have harc : arcLen (((404:ℝ)/1023) + ((139:ℝ)/349184)*Y)
        (((371:ℝ)/1023) - ((15:ℝ)/349184)*Y) = ((30:ℝ)/31) - ((7:ℝ)/15872)*Y := by
      unfold arcLen
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    rw [harc, ← InArc_int_add θ _ _ (-1) 0]
    apply InArc_of_bounds hθ
    · rw [alpha1]; push_cast; linarith
    · rw [alpha2]; push_cast; linarith
    · push_cast; linarith
  · -- t = 1 : near arc of `p₉`
    rw [hP1, nestArc_near _ (by decide : (8:ℕ) % 5 = 3 ∨ (8:ℕ) % 5 = 4)]
    have harc : arcLen (((821:ℝ)/1023) - ((139:ℝ)/698368)*Y)
        (((326:ℝ)/1023) + ((15:ℝ)/698368)*Y) = ((16:ℝ)/31) + ((7:ℝ)/31744)*Y := by
      unfold arcLen
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    rw [harc, ← InArc_int_add θ _ _ (-1) 0]
    apply InArc_of_bounds hθ
    · rw [alpha1]; push_cast; linarith
    · rw [alpha2]; push_cast; linarith
    · push_cast; linarith
  · -- t = 2 : far arc of `p₈`
    rw [hP2, nestArc_far _ (by decide : ¬ ((7:ℕ) % 5 = 3 ∨ (7:ℕ) % 5 = 4))]
    have harc : arcLen (((860:ℝ)/1023) - ((15:ℝ)/1396736)*Y)
        (((101:ℝ)/1023) + ((139:ℝ)/1396736)*Y) = ((8:ℝ)/31) + ((7:ℝ)/63488)*Y := by
      unfold arcLen
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    rw [harc, ← InArc_int_add θ _ _ (-1) 0]
    apply InArc_of_bounds hθ
    · rw [alpha1]; push_cast; linarith
    · rw [alpha2]; push_cast; linarith
    · push_cast; linarith
  · -- t = 3 : far arc of `p₇`
    rw [hP3, nestArc_far _ (by decide : ¬ ((6:ℕ) % 5 = 3 ∨ (6:ℕ) % 5 = 4))]
    have harc : arcLen (((461:ℝ)/1023) - ((139:ℝ)/2793472)*Y)
        (((593:ℝ)/1023) + ((15:ℝ)/2793472)*Y) = ((4:ℝ)/31) + ((7:ℝ)/126976)*Y := by
      unfold arcLen
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩
    rw [harc, ← InArc_int_add θ _ _ (-1) 0]
    apply InArc_of_bounds hθ
    · rw [alpha1]; push_cast; linarith
    · rw [alpha2]; push_cast; linarith
    · push_cast; linarith
  · -- t = 4 : far arc of `p₆`
    rw [hP4, nestArc_far _ (by decide : ¬ ((5:ℕ) % 5 = 3 ∨ (5:ℕ) % 5 = 4))]
    have harc : arcLen (((215:ℝ)/1023) - ((15:ℝ)/5586944)*Y)
        (((281:ℝ)/1023) + ((139:ℝ)/5586944)*Y) = ((2:ℝ)/31) + ((7:ℝ)/253952)*Y := by
      unfold arcLen
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩
    rw [harc, ← InArc_int_add θ _ _ 0 1]
    apply InArc_of_bounds hθ
    · rw [alpha1]; push_cast; linarith
    · rw [alpha2]; push_cast; linarith
    · push_cast; linarith
  · -- t = 5 : near arc of `p₅`
    rw [hP5, nestArc_near _ (by decide : (4:ℕ) % 5 = 3 ∨ (4:ℕ) % 5 = 4)]
    have harc : arcLen (((404:ℝ)/1023) + ((15:ℝ)/11173888)*Y)
        (((371:ℝ)/1023) - ((139:ℝ)/11173888)*Y) = ((30:ℝ)/31) - ((7:ℝ)/507904)*Y := by
      unfold arcLen
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    rw [harc, ← InArc_int_add θ _ _ (-1) 0]
    apply InArc_of_bounds hθ
    · rw [alpha1]; push_cast; linarith
    · rw [alpha2]; push_cast; linarith
    · push_cast; linarith
  · -- t = 6 : near arc of `p₄`
    rw [hP6, nestArc_near _ (by decide : (3:ℕ) % 5 = 3 ∨ (3:ℕ) % 5 = 4)]
    have harc : arcLen (((821:ℝ)/1023) - ((15:ℝ)/22347776)*Y)
        (((326:ℝ)/1023) + ((139:ℝ)/22347776)*Y) = ((16:ℝ)/31) + ((7:ℝ)/1015808)*Y := by
      unfold arcLen
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    rw [harc, ← InArc_int_add θ _ _ (-1) 0]
    apply InArc_of_bounds hθ
    · rw [alpha1]; push_cast; linarith
    · rw [alpha2]; push_cast; linarith
    · push_cast; linarith
  · -- t = 7 : far arc of `p₃`
    rw [hP7, nestArc_far _ (by decide : ¬ ((2:ℕ) % 5 = 3 ∨ (2:ℕ) % 5 = 4))]
    have harc : arcLen (((860:ℝ)/1023) - ((139:ℝ)/44695552)*Y)
        (((101:ℝ)/1023) + ((15:ℝ)/44695552)*Y) = ((8:ℝ)/31) + ((7:ℝ)/2031616)*Y := by
      unfold arcLen
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    rw [harc, ← InArc_int_add θ _ _ (-1) 0]
    apply InArc_of_bounds hθ
    · rw [alpha1]; push_cast; linarith
    · rw [alpha2]; push_cast; linarith
    · push_cast; linarith
  · -- t = 8 : far arc of `p₂`
    rw [hP8, nestArc_far _ (by decide : ¬ ((1:ℕ) % 5 = 3 ∨ (1:ℕ) % 5 = 4))]
    have harc : arcLen (((461:ℝ)/1023) - ((15:ℝ)/89391104)*Y)
        (((593:ℝ)/1023) + ((139:ℝ)/89391104)*Y) = ((4:ℝ)/31) + ((7:ℝ)/4063232)*Y := by
      unfold arcLen
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩
    rw [harc, ← InArc_int_add θ _ _ (-1) 0]
    apply InArc_of_bounds hθ
    · rw [alpha1]; push_cast; linarith
    · rw [alpha2]; push_cast; linarith
    · push_cast; linarith
  · -- t = 9 : far arc of `p₁`
    rw [hP9, nestArc_far _ (by decide : ¬ ((0:ℕ) % 5 = 3 ∨ (0:ℕ) % 5 = 4))]
    have harc : arcLen (((215:ℝ)/1023) - ((139:ℝ)/178782208)*Y)
        (((281:ℝ)/1023) + ((15:ℝ)/178782208)*Y) = ((2:ℝ)/31) + ((7:ℝ)/8126464)*Y := by
      unfold arcLen
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, 0, by push_cast; ring⟩
    rw [harc, ← InArc_int_add θ _ _ 0 1]
    apply InArc_of_bounds hθ
    · rw [alpha1]; push_cast; linarith
    · rw [alpha2]; push_cast; linarith
    · push_cast; linarith

end Work.ELAssembly
