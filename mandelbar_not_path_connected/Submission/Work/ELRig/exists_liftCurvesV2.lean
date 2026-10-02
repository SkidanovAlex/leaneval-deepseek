/-
# ELRig — the two `1`-periodic lift curves of the ray tails (R-a2, tail form)

`Work.ELRig.exists_liftCurvesV2` closes the open item §6 of `Submission/Work/ELRig/NOTES.md` in
the *tail form*: for a root-parabolic parameter `c`, the Leau–Fatou flower of `z₁`, and the two
landing statements of the root portrait, there are `1`-periodic curves `γ₁`, `γ₂ = ι γ₁`
(`ι w = w̄ + 1/2`) in the repelling coordinate `Ψ` whose `Ψ`-images run along the two root rays,
and which cover *every* `Ψ`-preimage in the half plane `{Re < -R}` of the *tails* of the two rays
(levels below an explicitly produced `t₀ > 1`).

## The construction

`R' := max R R₀ + 1`.  The flower's `cover` at level `R'`, combined with the landing hypotheses
`LandsN` and `Pa ⊆ K c`, shows that for every level `t` in an interval `(1, t₁)` the ray point
`rayPt α₁ t` has a `Ψ`-preimage in the half plane `{Re < -R'}` (`exists_preimage_rayTail`), and
`Ψ` is injective on the larger half plane `{Re < -R₀}` by hypothesis, so this preimage
`p t := g (rayPt α₁ t)` (a choice function on the cover statement) is *unique*.  The whole
argument rests on the single identity

  `p (x ^ 1024) = p x + 1`  (for `1 < x`, `x ^ 1024 < t₁`),

which is `Ψ`-change of coordinates: `Ψ (p x + 1) = F (Ψ (p x)) = F (rayPt α₁ x) =
rayPt α₁ (x ^ 1024) = Ψ (p (x ^ 1024))`, and both points lie in the injectivity half plane.
Iterating it gives `Ψ (p x + n) = rayPt α₁ (x ^ 1024^n)` (upwards) and
`p (y ^ (1/1024)^n) = p y - n` (downwards).

With `t₀` chosen so that `1 < t₀`, `t₀ ^ 1024 < t₁` and `t₀ < t₂`, the level parametrisation
`τ s = t₀ ^ (1024 ^ s)` (`levelParam_spec`) turns the "level window" `[t₀, t₀ ^ 1024]` into a
fundamental domain, and the curve

  `γ₁ s := p (τ (s - ⌊s⌋)) + ⌊s⌋`

is the corresponding `1`-periodic lift (`γ₁ (s+1) = γ₁ s + 1`), with
`Ψ (γ₁ s) = rayPt α₁ (τ s)` for *every* `s ∈ ℝ` (the two iterated identities above handle the two
signs of `⌊s⌋`), `γ₁` continuous (the `+1` cocycle and `p (t₀ ^ 1024) = p t₀ + 1` glue the
windows), injective (its level `τ s` is strictly increasing) and, for levels below `t₀`, its range
contains exactly the `Ψ`-preimages of the `α₁`-ray in `{Re < -R}`.  Finally
`γ₂ := ι ∘ γ₁` has `ι`-image range, `1`-periodicity (`ι (w+1) = ι w - 1` sorts itself out), maps
to the `α₂` ray (`Ψ_anti` and `rayPt_g_alpha1`) and covers the `α₂`-tail because
`q (y ^ 32) = ι (p y)` (the same uniqueness argument with `Ψ_anti`), so a `Ψ`-preimage `w` of an
`α₂`-ray point of level `t < t₀` is `γ₂ s` for the index `s` with `γ₁ s = p (t ^ (1/32))`.

Everything is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.ELRig.Flower
import Submission.Work.ELRig.cert
import Submission.Work.ELRig.continuousAt_invOn
import Submission.Work.ELRig.exists_preimage_rayTail
import Submission.Work.ELRig.levelParam_spec
import Submission.Work.Top.continuousOn_rayPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Two elementary facts about the ray points -/

/-- **The degree-`1024` map `F c` on the `α₂`-ray.**  `F c = (T_c)^[10]` sends the ray point of
angle `α₂` and level `t > 1` to the ray point of the *same* angle `α₂` and level `t ^ 1024`. -/
theorem rayPt_F_alpha2 {c : ℂ} (d : Work.EL.RootParabolic c) {t : ℝ} (ht : 1 < t) :
    Work.EL.F c (Work.EL.rayPt d.hN Work.EL.alpha2 t)
      = Work.EL.rayPt d.hN Work.EL.alpha2 (t ^ (1024 : ℕ)) := by
  rw [rayPt_iterate d.hN d.bottcher ht, cert.2.2.2.1]

/-- The ray point is injective in its level (for levels `> 1`): the level is the modulus of the
Böttcher coordinate. -/
theorem rayPt_level_inj {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ t t' : ℝ}
    (ht : 1 < t) (ht' : 1 < t') (h : Work.EL.rayPt hN θ t = Work.EL.rayPt hN θ t') : t = t' := by
  have h1 := congrArg (Work.EL.dynPhi c φ) h
  rw [Work.Top.NakaneData.Phi_rayPt hN ht, Work.Top.NakaneData.Phi_rayPt hN ht'] at h1
  have h2 := congrArg norm h1
  rw [Work.Top.NakaneData.norm_rayPoint, Work.Top.NakaneData.norm_rayPoint] at h2
  rwa [abs_of_pos (by linarith : (0 : ℝ) < t), abs_of_pos (by linarith : (0 : ℝ) < t')] at h2

theorem exists_liftCurvesV2 {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (h₁ : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁)
    (h₂ : Work.EL.LandsN d.hN Work.EL.alpha2 d.z₁)
    {R R₀ : ℝ} (hRR₀ : R₀ ≤ R) (hinj : Set.InjOn fl.Ψ {w : ℂ | w.re < -R₀}) :
    ∃ (γ₁ γ₂ : ℝ → ℂ) (t₀ : ℝ), 1 < t₀ ∧
      Continuous γ₁ ∧ Continuous γ₂ ∧ Function.Injective γ₁ ∧ Function.Injective γ₂ ∧
      (∀ s : ℝ, γ₁ (s + 1) = γ₁ s + 1) ∧ (∀ s : ℝ, γ₂ (s + 1) = γ₂ s + 1) ∧
      Set.range γ₂ = (fun w : ℂ => star w + 1 / 2) '' Set.range γ₁ ∧
      (∀ s : ℝ, fl.Ψ (γ₁ s) ∈ Work.EL.paramRay d.hN Work.EL.alpha1) ∧
      (∀ s : ℝ, fl.Ψ (γ₂ s) ∈ Work.EL.paramRay d.hN Work.EL.alpha2) ∧
      (∀ w : ℂ, w.re < -R → (∃ t : ℝ, 1 < t ∧ t < t₀ ∧
          fl.Ψ w = Work.EL.rayPt d.hN Work.EL.alpha1 t) → w ∈ Set.range γ₁) ∧
      (∀ w : ℂ, w.re < -R → (∃ t : ℝ, 1 < t ∧ t < t₀ ∧
          fl.Ψ w = Work.EL.rayPt d.hN Work.EL.alpha2 t) → w ∈ Set.range γ₂) := by
  classical
  -- ===================== 1. the half plane and the two ray tails =====================
  let R' : ℝ := max R R₀ + 1
  have hRR' : R < R' := by
    simp only [R']
    linarith [le_max_left R R₀]
  have hR₀R' : R₀ < R' := by
    simp only [R']
    linarith [le_max_right R R₀]
  have hRR₀' : R ≤ R' := le_of_lt hRR'
  have hR'ge : R₀ + 1 ≤ R' := by
    simp only [R']
    linarith [le_max_right R R₀]
  have hinj' : Set.InjOn fl.Ψ {w : ℂ | w.re < -R'} :=
    hinj.mono (fun w hw => by simp only [Set.mem_setOf_eq] at hw ⊢; linarith)
  obtain ⟨t₁, ht₁, hpre₁⟩ := exists_preimage_rayTail d fl h₁ (R := R')
  obtain ⟨t₂, ht₂, hpre₂⟩ := exists_preimage_rayTail d fl h₂ (R := R')
  -- ===================== 2. the chosen inverse branch and the lift points =====================
  let g : ℂ → ℂ := fun z => if h : ∃ w : ℂ, w.re < -R' ∧ fl.Ψ w = z then h.choose else 0
  have hg_spec : ∀ z : ℂ, (h : ∃ w : ℂ, w.re < -R' ∧ fl.Ψ w = z) →
      (g z).re < -R' ∧ fl.Ψ (g z) = z := by
    intro z h
    have hspec := h.choose_spec
    simp only [g, dite_eq_left h]
    exact hspec
  have hψU : IsOpen {w : ℂ | w.re < -R'} := isOpen_lt Complex.continuous_re continuous_const
  have hg_cont : ∀ x : ℂ, x.re < -R' → ContinuousAt g (fl.Ψ x) := by
    intro x hx
    refine continuousAt_invOn hψU fl.Ψ_diff hinj' ?_ hx
    rintro z ⟨w, hw, hΨw⟩
    rw [← hΨw]
    exact ⟨(hg_spec (fl.Ψ w) ⟨w, hw, rfl⟩).2, (hg_spec (fl.Ψ w) ⟨w, hw, rfl⟩).1⟩
  let p : ℝ → ℂ := fun t => g (Work.EL.rayPt d.hN Work.EL.alpha1 t)
  let q : ℝ → ℂ := fun t => g (Work.EL.rayPt d.hN Work.EL.alpha2 t)
  have hp_mem : ∀ t : ℝ, 1 < t → t < t₁ → (p t).re < -R' := by
    intro t ht ht1
    exact (hg_spec _ (hpre₁ t ht ht1)).1
  have hp_Ψ : ∀ t : ℝ, 1 < t → t < t₁ → fl.Ψ (p t) = Work.EL.rayPt d.hN Work.EL.alpha1 t := by
    intro t ht ht1
    exact (hg_spec _ (hpre₁ t ht ht1)).2
  have hq_mem : ∀ t : ℝ, 1 < t → t < t₂ → (q t).re < -R' := by
    intro t ht ht1
    exact (hg_spec _ (hpre₂ t ht ht1)).1
  have hq_Ψ : ∀ t : ℝ, 1 < t → t < t₂ → fl.Ψ (q t) = Work.EL.rayPt d.hN Work.EL.alpha2 t := by
    intro t ht ht1
    exact (hg_spec _ (hpre₂ t ht ht1)).2
  have hp_cont : ∀ t : ℝ, 1 < t → t < t₁ → ContinuousAt p t := by
    intro t ht ht1
    have h1 : ContinuousAt (fun t : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1 t) t :=
      (Work.Top.continuousOn_rayPt d.hN Work.EL.alpha1).continuousAt (Ioi_mem_nhds ht)
    have h2 : ContinuousAt g (Work.EL.rayPt d.hN Work.EL.alpha1 t) := by
      rw [← hp_Ψ t ht ht1]
      exact hg_cont (p t) (hp_mem t ht ht1)
    exact h2.comp h1
  have huniq : ∀ w w' : ℂ, w.re < -R₀ → w'.re < -R₀ → fl.Ψ w = fl.Ψ w' → w = w' :=
    fun w w' hw hw' h => hinj hw hw' h
  -- ===================== 3. the two shift identities along the level =====================
  have hp_shift : ∀ x : ℝ, 1 < x → x < t₁ → x ^ (1024 : ℕ) < t₁ →
      p (x ^ (1024 : ℕ)) = p x + 1 := by
    intro x hx hx1 hx2
    have hx' : 1 < x ^ (1024 : ℕ) := one_lt_pow₀ hx (by norm_num)
    have h1 : fl.Ψ (p x + 1) = fl.Ψ (p (x ^ (1024 : ℕ))) := by
      rw [fl.Ψ_shift (p x), hp_Ψ x hx hx1, rayPt_F_alpha1 d hx, hp_Ψ (x ^ (1024 : ℕ)) hx' hx2]
    have h2 : (p x + 1).re < -R₀ := by
      have hmem := hp_mem x hx hx1
      simp only [Complex.add_re, Complex.one_re]
      linarith [hR'ge]
    have h3 : (p (x ^ (1024 : ℕ))).re < -R₀ := by
      have hmem := hp_mem (x ^ (1024 : ℕ)) hx' hx2
      linarith [hR₀R']
    exact (huniq (p x + 1) (p (x ^ (1024 : ℕ))) h2 h3 h1).symm
  have hpow_mul : ((1024 : ℝ)⁻¹) * 1024 = 1 := by norm_num
  have hp_down : ∀ y : ℝ, 1 < y → y < t₁ → p (y ^ ((1024 : ℝ)⁻¹)) + 1 = p y := by
    intro y hy hy1
    have hy' : 1 < y ^ ((1024 : ℝ)⁻¹) := Real.one_lt_rpow hy (by norm_num)
    have hy'1 : y ^ ((1024 : ℝ)⁻¹) < t₁ := by
      have hle : y ^ ((1024 : ℝ)⁻¹) ≤ y := by
        have := Real.rpow_le_rpow_of_exponent_le hy.le (by norm_num : ((1024 : ℝ)⁻¹) ≤ 1)
        simpa using this
      linarith
    have hpow : (y ^ ((1024 : ℝ)⁻¹)) ^ (1024 : ℕ) = y := by
      have h : (y ^ ((1024 : ℝ)⁻¹)) ^ (1024 : ℝ) = y := by
        rw [← Real.rpow_mul (le_of_lt (by linarith : (0 : ℝ) < y)), hpow_mul, Real.rpow_one]
      simpa [Real.rpow_natCast] using h
    have hsh := hp_shift (y ^ ((1024 : ℝ)⁻¹)) hy' hy'1 (by rw [hpow]; exact hy1)
    rw [hpow] at hsh
    exact hsh.symm
  -- iterated shifts
  have hp_add_nat : ∀ (x : ℝ) (n : ℕ), 1 < x → x < t₁ →
      fl.Ψ (p x + (n : ℂ)) = Work.EL.rayPt d.hN Work.EL.alpha1 (x ^ (1024 ^ n)) := by
    intro x n hx hx1
    induction n with
    | zero =>
      have h1 : x ^ (1024 ^ 0) = x := by simp
      rw [h1, Nat.cast_zero, add_zero]
      exact hp_Ψ x hx hx1
    | succ n ih =>
      have hx' : 1 < x ^ (1024 ^ n) := one_lt_pow₀ hx (pow_ne_zero n (by norm_num))
      have hcast : p x + ((n + 1 : ℕ) : ℂ) = (p x + (n : ℂ)) + 1 := by push_cast; ring
      rw [hcast, fl.Ψ_shift (p x + (n : ℂ)), ih, rayPt_F_alpha1 d hx', ← pow_mul, ← pow_succ]
  have hp_sub_nat : ∀ (y : ℝ) (n : ℕ), 1 < y → y < t₁ →
      p (y ^ (((1024 : ℝ)⁻¹) ^ n)) = p y - (n : ℂ) := by
    intro y n hy hy1
    induction n with
    | zero => simp
    | succ n ih =>
      have hy' : 1 < y ^ (((1024 : ℝ)⁻¹) ^ n) :=
        Real.one_lt_rpow hy (pow_pos (by norm_num) n)
      have hle1 : ((1024 : ℝ)⁻¹) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hle : y ^ (((1024 : ℝ)⁻¹) ^ n) ≤ y := by
        have := Real.rpow_le_rpow_of_exponent_le hy.le hle1
        simpa using this
      have hy'1 : y ^ (((1024 : ℝ)⁻¹) ^ n) < t₁ := lt_of_le_of_lt hle hy1
      have ih' : p (y ^ (((1024 : ℝ)⁻¹) ^ n)) = p y - (n : ℂ) := ih
      have hdown := hp_down (y ^ (((1024 : ℝ)⁻¹) ^ n)) hy' hy'1
      have hpow : (y ^ (((1024 : ℝ)⁻¹) ^ n)) ^ ((1024 : ℝ)⁻¹) =
          y ^ (((1024 : ℝ)⁻¹) ^ (n + 1)) := by
        rw [← Real.rpow_mul (le_of_lt (by linarith : (0 : ℝ) < y)), ← pow_succ]
      have hstep : p ((y ^ (((1024 : ℝ)⁻¹) ^ n)) ^ ((1024 : ℝ)⁻¹)) =
          p (y ^ (((1024 : ℝ)⁻¹) ^ n)) - 1 := by
        rw [eq_sub_iff_add_eq]
        exact hdown
      rw [← hpow, hstep, ih']
      push_cast
      ring
  -- ===================== 4. the level parametrisation of the ray =====================
  have hpow_neg : ∀ k : ℕ, (1024 : ℝ) ^ (-(k : ℝ)) = ((1024 : ℝ)⁻¹) ^ k := by
    intro k
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
  let t₀ : ℝ := (1 + min (t₁ ^ ((1024 : ℝ)⁻¹)) t₂) / 2
  have hmin1 : 1 < min (t₁ ^ ((1024 : ℝ)⁻¹)) t₂ :=
    lt_min (Real.one_lt_rpow ht₁ (by norm_num)) ht₂
  have ht₀1 : 1 < t₀ := by
    simp only [t₀]
    linarith
  have ht₀_lt : t₀ < min (t₁ ^ ((1024 : ℝ)⁻¹)) t₂ := by
    simp only [t₀]
    linarith
  have ht₀_t₁ : t₀ ^ (1024 : ℕ) < t₁ := by
    have hlt : t₀ < t₁ ^ ((1024 : ℝ)⁻¹) := lt_of_lt_of_le ht₀_lt (min_le_left _ _)
    calc t₀ ^ (1024 : ℕ) < (t₁ ^ ((1024 : ℝ)⁻¹)) ^ (1024 : ℕ) :=
          pow_lt_pow_left₀ hlt (le_of_lt (by linarith : (0 : ℝ) < t₀)) (by norm_num)
      _ = t₁ := by
          have h : (t₁ ^ ((1024 : ℝ)⁻¹)) ^ (1024 : ℝ) = t₁ := by
            rw [← Real.rpow_mul (le_of_lt (by linarith : (0 : ℝ) < t₁)), hpow_mul,
              Real.rpow_one]
          simpa [Real.rpow_natCast] using h
  have ht₀_t₂ : t₀ < t₂ := lt_of_lt_of_le ht₀_lt (min_le_right _ _)
  have ht₀_lt_t₁ : t₀ < t₁ := by
    have h1 : t₁ ^ ((1024 : ℝ)⁻¹) ≤ t₁ := by
      have h := Real.rpow_le_rpow_of_exponent_le ht₁.le (by norm_num : ((1024 : ℝ)⁻¹) ≤ 1)
      simpa using h
    linarith [ht₀_lt, min_le_left (t₁ ^ ((1024 : ℝ)⁻¹)) t₂]
  let τ : ℝ → ℝ := fun s => t₀ ^ ((1024 : ℝ) ^ s)
  obtain ⟨hτc, hτmono0, hτpos0, hτ00, hτ10, -, hτmul0, hτnat0, hτsurj0⟩ :=
    levelParam_spec ht₀1
  have hτcont : Continuous τ := by dsimp only [τ]; exact hτc
  have hτmono : StrictMono τ := by dsimp only [τ]; exact hτmono0
  have hτ1 : ∀ s : ℝ, 1 < τ s := by intro s; dsimp only [τ]; exact hτpos0 s
  have hτ0 : τ 0 = t₀ := by dsimp only [τ]; exact hτ00
  have hτ1' : τ 1 = t₀ ^ (1024 : ℕ) := by dsimp only [τ]; exact hτ10
  have hτmul : ∀ s u : ℝ, τ (s + u) = (τ s) ^ ((1024 : ℝ) ^ u) := by
    intro s u; dsimp only [τ]; exact hτmul0 s u
  have hτnat : ∀ s : ℝ, ∀ m : ℕ, (τ s) ^ (1024 ^ m) = τ (s + m) := by
    intro s m; dsimp only [τ]; exact hτnat0 s m
  have hτsurj : ∀ t : ℝ, 1 < t → ∃ s : ℝ, τ s = t := by
    intro t ht; dsimp only [τ]; exact hτsurj0 t ht
  -- the window bound: `τ u ∈ (1, t₁)` for `u ∈ [0, 1]`
  have huIco : ∀ s : ℝ, s - ((⌊s⌋ : ℤ) : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    intro s
    constructor
    · exact sub_nonneg.mpr (Int.floor_le s)
    · have := Int.lt_floor_add_one s
      linarith
  have hτle : ∀ u : ℝ, u ≤ 1 → τ u ≤ t₀ ^ (1024 : ℕ) := by
    intro u hu
    calc τ u ≤ τ 1 := hτmono.monotone hu
      _ = t₀ ^ (1024 : ℕ) := hτ1'
  have hτwin : ∀ u : ℝ, u ≤ 1 → τ u < t₁ :=
    fun u hu => lt_of_le_of_lt (hτle u hu) ht₀_t₁
  have hτwinIco : ∀ s : ℝ, τ (s - ((⌊s⌋ : ℤ) : ℝ)) ∈ Set.Ioo (1 : ℝ) t₁ :=
    fun s => ⟨hτ1 _, hτwin _ (le_of_lt (huIco s).2)⟩
  -- ===================== 5. the two curves =====================
  let γ₁ : ℝ → ℂ := fun s => p (τ (s - ((⌊s⌋ : ℤ) : ℝ))) + ((⌊s⌋ : ℤ) : ℂ)
  let γ₂ : ℝ → ℂ := fun s => star (γ₁ s) + 1 / 2
  -- the level of `γ₁ s` is `τ s`
  have hγ₁_Ψ : ∀ s : ℝ, fl.Ψ (γ₁ s) = Work.EL.rayPt d.hN Work.EL.alpha1 (τ s) := by
    intro s
    set m : ℤ := ⌊s⌋ with hm
    set u : ℝ := s - (m : ℝ) with hu
    have huI : u ∈ Set.Ico (0 : ℝ) 1 := by
      rw [hu, hm]
      exact huIco s
    have hus : u + (m : ℝ) = s := by rw [hu]; ring
    have hγ : γ₁ s = p (τ u) + (m : ℂ) := rfl
    have hx1 : τ u < t₁ := hτwin u (le_of_lt huI.2)
    by_cases hm0 : 0 ≤ m
    · -- `m ≥ 0`: shift up `m` times
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m := ⟨m.toNat, Int.toNat_of_nonneg hm0⟩
      have hnR : (n : ℝ) = (m : ℝ) := by exact_mod_cast hn
      have hnC : (n : ℂ) = (m : ℂ) := by exact_mod_cast hn
      have hγ' : γ₁ s = p (τ u) + (n : ℂ) := by
        rw [hγ, ← hnC]
      have hlev : (τ u) ^ (1024 ^ n) = τ s := by
        rw [hτnat, show u + (n : ℝ) = s by rw [hnR]; exact hus]
      rw [hγ', hp_add_nat (τ u) n (hτ1 u) hx1, hlev]
    · -- `m < 0`: shift down `|m|` times
      have hmneg : m < 0 := not_le.mp hm0
      have hk0 : 0 ≤ -m := by omega
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = -m := ⟨(-m).toNat, Int.toNat_of_nonneg hk0⟩
      have hkR : (k : ℝ) = -(m : ℝ) := by
        have : (k : ℤ) = -m := hk
        exact_mod_cast this
      have hkC : (k : ℂ) = -(m : ℂ) := by
        have : (k : ℤ) = -m := hk
        exact_mod_cast this
      have hγ' : γ₁ s = p (τ u) - (k : ℂ) := by
        rw [hγ, hkC]
        ring
      have hsub := hp_sub_nat (τ u) k (hτ1 u) hx1
      have hsum : u + (-(k : ℝ)) = s := by
        rw [hkR, neg_neg]
        exact hus
      have hlev : (τ u) ^ (((1024 : ℝ)⁻¹) ^ k) = τ s := by
        rw [← hpow_neg k, ← hτmul u (-(k : ℝ)), hsum]
      have hs0 : s < 0 := by
        have hm1 : (m : ℝ) ≤ -1 := by
          exact_mod_cast (show m ≤ -1 by omega)
        rw [← hus]
        linarith [huI.2]
      have hlt : (τ u) ^ (((1024 : ℝ)⁻¹) ^ k) < t₁ := by
        rw [hlev]
        have : τ s ≤ τ 0 := hτmono.monotone hs0.le
        rw [hτ0] at this
        linarith [ht₀_lt_t₁]
      rw [hγ', ← hsub, hp_Ψ _ (Real.one_lt_rpow (hτ1 u) (pow_pos (by norm_num) k)) hlt, hlev]
  -- ===================== 6. the closed-window formula and continuity =====================
  have hwin : ∀ (k : ℤ) (s : ℝ), s ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1) →
      γ₁ s = p (τ (s - (k : ℝ))) + (k : ℂ) := by
    intro k s hs
    by_cases hsk : s = (k : ℝ)
    · rw [hsk]
      simp only [γ₁, Int.floor_intCast]
    · have hks : (k : ℝ) < s := lt_of_le_of_ne hs.1 (Ne.symm hsk)
      by_cases hsk1 : s = (k : ℝ) + 1
      · rw [hsk1]
        have hfloor : ⌊((k : ℝ) + 1)⌋ = k + 1 := by
          rw [Int.floor_add_one, Int.floor_intCast]
        simp only [γ₁, hfloor]
        have hL : τ ((k : ℝ) + 1 - (((k + 1 : ℤ)) : ℝ)) = t₀ := by
          have h0 : (k : ℝ) + 1 - (((k + 1 : ℤ)) : ℝ) = 0 := by push_cast; ring
          rw [h0, hτ0]
        have hR : τ ((k : ℝ) + 1 - (k : ℝ)) = t₀ ^ (1024 : ℕ) := by
          have h1 : (k : ℝ) + 1 - (k : ℝ) = 1 := by ring
          rw [h1, hτ1']
        rw [hL, hR, hp_shift t₀ ht₀1 ht₀_lt_t₁ ht₀_t₁]
        push_cast
        ring
      · have hs' : s ∈ Set.Ico (k : ℝ) ((k : ℝ) + 1) :=
          ⟨hks.le, lt_of_le_of_ne hs.2 hsk1⟩
        simp only [γ₁, Int.floor_eq_on_Ico k s hs']
  have hGcont : ∀ (k : ℤ) (s : ℝ), τ (s - (k : ℝ)) ∈ Set.Ioo (1 : ℝ) t₁ →
      ContinuousAt (fun t : ℝ => p (τ (t - (k : ℝ))) + (k : ℂ)) s := by
    intro k s hs
    have h1 : ContinuousAt (fun t : ℝ => τ (t - (k : ℝ))) s :=
      hτcont.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    have h2 : ContinuousAt (fun t : ℝ => p (τ (t - (k : ℝ)))) s := by
      have hcomp := ContinuousAt.comp (x := s) (f := fun t : ℝ => τ (t - (k : ℝ))) (g := p)
        (hp_cont (τ (s - (k : ℝ))) hs.1 hs.2) h1
      exact hcomp
    exact h2.add continuousAt_const
  have hGcontOn : ∀ k : ℤ, ContinuousOn (fun t : ℝ => p (τ (t - (k : ℝ))) + (k : ℂ))
      (Set.Icc (k : ℝ) ((k : ℝ) + 1)) := by
    intro k
    have hmaps : Set.MapsTo (fun t : ℝ => τ (t - (k : ℝ))) (Set.Icc (k : ℝ) ((k : ℝ) + 1))
        (Set.Ioo (1 : ℝ) t₁) := by
      intro t ht
      refine ⟨hτ1 _, ?_⟩
      have hle : t - (k : ℝ) ≤ 1 := by linarith [ht.2]
      calc τ (t - (k : ℝ)) ≤ τ 1 := hτmono.monotone hle
        _ = t₀ ^ (1024 : ℕ) := hτ1'
        _ < t₁ := ht₀_t₁
    have hgc : ContinuousOn (fun t : ℝ => τ (t - (k : ℝ))) (Set.Icc (k : ℝ) ((k : ℝ) + 1)) :=
      hτcont.continuousOn.comp ((continuous_id.sub continuous_const).continuousOn)
        (fun t _ => Set.mem_univ _)
    have hpc : ContinuousOn p (Set.Ioo (1 : ℝ) t₁) :=
      fun t ht => (hp_cont t ht.1 ht.2).continuousWithinAt
    exact (hpc.comp hgc hmaps).add continuousOn_const
  have hγ₁_contOn : ∀ k : ℤ, ContinuousOn γ₁ (Set.Icc (k : ℝ) ((k : ℝ) + 1)) := by
    intro k
    exact (hGcontOn k).congr (fun s hs => hwin k s hs)
  have hγ₁_cont : Continuous γ₁ := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs : s = ((⌊s⌋ : ℤ) : ℝ)
    · have hmain : ContinuousAt γ₁ (((⌊s⌋ : ℤ)) : ℝ) := by
        set k : ℤ := ⌊s⌋ with hk
        have hb : ((k - 1 : ℤ) : ℝ) + 1 = (k : ℝ) := by push_cast; ring
        have hleft : ContinuousWithinAt γ₁ (Set.Icc (((k - 1 : ℤ) : ℝ)) (k : ℝ)) (k : ℝ) := by
          rw [← hb]
          exact (hγ₁_contOn (k - 1)).continuousWithinAt (by
            constructor <;> push_cast <;> linarith)
        have hright : ContinuousWithinAt γ₁ (Set.Icc (k : ℝ) ((k : ℝ) + 1)) (k : ℝ) :=
          (hγ₁_contOn k).continuousWithinAt (by constructor <;> linarith)
        have hunion := hleft.union hright
        have hset : Set.Icc (((k - 1 : ℤ) : ℝ)) (k : ℝ) ∪ Set.Icc (k : ℝ) ((k : ℝ) + 1)
            = Set.Icc (((k - 1 : ℤ) : ℝ)) ((k : ℝ) + 1) := by
          ext x
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact ⟨h1, le_trans h2 (by linarith)⟩
            · exact ⟨le_trans (by push_cast; linarith) h1, h2⟩
          · intro hx
            rcases le_or_gt x (k : ℝ) with h | h
            · exact Or.inl ⟨hx.1, h⟩
            · exact Or.inr ⟨h.le, hx.2⟩
        rw [hset] at hunion
        exact ContinuousWithinAt.continuousAt hunion
          (Icc_mem_nhds (by push_cast; linarith) (by linarith))
      rw [← hs] at hmain
      exact hmain
    · have hm : ((⌊s⌋ : ℤ) : ℝ) < s := lt_of_le_of_ne (Int.floor_le s) (Ne.symm hs)
      have hm' : s < ((⌊s⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one s
      have hnbhd : Set.Ioo (((⌊s⌋ : ℤ) : ℝ)) (((⌊s⌋ : ℤ) : ℝ) + 1) ∈ 𝓝 s :=
        Ioo_mem_nhds hm hm'
      have hcontG : ContinuousAt
          (fun t : ℝ => p (τ (t - ((⌊s⌋ : ℤ) : ℝ))) + ((⌊s⌋ : ℤ) : ℂ)) s :=
        hGcont ⌊s⌋ s (hτwinIco s)
      refine hcontG.congr ?_
      filter_upwards [hnbhd] with t ht
      exact (hwin ⌊s⌋ t ⟨ht.1.le, ht.2.le⟩).symm
  -- ===================== 7. periodicity, injectivity, the curve `γ₂` =====================
  have hγ₁_per : ∀ s : ℝ, γ₁ (s + 1) = γ₁ s + 1 := by
    intro s
    have hfloor : ⌊s + 1⌋ = ⌊s⌋ + 1 := Int.floor_add_one s
    simp only [γ₁, hfloor]
    have harg : s + 1 - (((⌊s⌋ + 1 : ℤ)) : ℝ) = s - ((⌊s⌋ : ℤ) : ℝ) := by push_cast; ring
    rw [harg]
    push_cast
    ring
  have hγ₁_inj : Function.Injective γ₁ := by
    intro s s' h
    have h1 : τ s = τ s' := by
      have h2 := congrArg fl.Ψ h
      rw [hγ₁_Ψ s, hγ₁_Ψ s'] at h2
      exact rayPt_level_inj d.hN (hτ1 s) (hτ1 s') h2
    exact hτmono.injective h1
  have hι2 : ∀ z : ℂ, star (star z + 1 / 2) + 1 / 2 = z + 1 := by
    intro z
    rw [star_add, star_star]
    have h : star ((1 : ℂ) / 2) = 1 / 2 := by norm_num
    rw [h]
    ring
  have hγ₂_per : ∀ s : ℝ, γ₂ (s + 1) = γ₂ s + 1 := by
    intro s
    simp only [γ₂]
    rw [hγ₁_per s, star_add, star_one]
    ring
  have hγ₂_cont : Continuous γ₂ := by
    have h1 : Continuous fun s : ℝ => star (γ₁ s) := continuous_star.comp hγ₁_cont
    exact (h1.add continuous_const :
      Continuous (fun s : ℝ => star (γ₁ s) + (1 / 2 : ℂ)))
  have hγ₂_inj : Function.Injective γ₂ := by
    intro s s' h
    have h1 : star (γ₁ s) = star (γ₁ s') := by
      have h2 := congrArg (fun z : ℂ => z - 1 / 2) h
      simpa [γ₂] using h2
    have h3 : γ₁ s = γ₁ s' := by
      have := congrArg star h1
      simpa using this
    exact hγ₁_inj h3
  have hγ₂_range : Set.range γ₂ = (fun w : ℂ => star w + 1 / 2) '' Set.range γ₁ := by
    rw [show γ₂ = (fun w : ℂ => star w + 1 / 2) ∘ γ₁ from rfl]
    exact Set.range_comp _ _
  have hγ₁_mem : ∀ s : ℝ, fl.Ψ (γ₁ s) ∈ Work.EL.paramRay d.hN Work.EL.alpha1 := by
    intro s
    rw [hγ₁_Ψ s]
    exact Work.EL.rayPt_mem_paramRay d.hN (hτ1 s)
  have hγ₂_mem : ∀ s : ℝ, fl.Ψ (γ₂ s) ∈ Work.EL.paramRay d.hN Work.EL.alpha2 := by
    intro s
    have h : fl.Ψ (γ₂ s) = Work.EL.rayPt d.hN Work.EL.alpha2 ((τ s) ^ (32 : ℕ)) := by
      simp only [γ₂]
      rw [fl.Ψ_anti (γ₁ s), hγ₁_Ψ s, rayPt_g_alpha1 d (hτ1 s)]
    rw [h]
    exact Work.EL.rayPt_mem_paramRay d.hN (one_lt_pow₀ (hτ1 s) (by norm_num))
  -- ===================== 8. the coverage of the two ray tails =====================
  have hp_memR₀ : ∀ t : ℝ, 1 < t → t < t₁ → (p t).re < -R₀ :=
    fun t ht ht1 => lt_of_lt_of_le (hp_mem t ht ht1) (by linarith [hR₀R'])
  have hq_memR₀ : ∀ t : ℝ, 1 < t → t < t₂ → (q t).re < -R₀ :=
    fun t ht ht1 => lt_of_lt_of_le (hq_mem t ht ht1) (by linarith [hR₀R'])
  have hmem_γ₁ : ∀ y : ℝ, 1 < y → y < t₀ → p y ∈ Set.range γ₁ := by
    intro y hy hy0
    have hy1 : y < t₁ := lt_trans hy0 ht₀_lt_t₁
    obtain ⟨s, hs⟩ := hτsurj y hy
    have hs0 : s < 0 := by
      by_contra h
      have h0 : 0 ≤ s := not_lt.mp h
      have hle : τ 0 ≤ τ s := hτmono.monotone h0
      rw [hτ0, hs] at hle
      linarith
    have hfloor : (((⌊s⌋ : ℤ)) : ℝ) ≤ -1 := by
      have hlt : ⌊s⌋ < 0 := (Int.floor_lt).mpr (by simpa using hs0)
      exact_mod_cast (show ⌊s⌋ ≤ -1 by omega)
    have hre : (γ₁ s).re < -R₀ := by
      simp only [γ₁, Complex.add_re]
      have hcast : ((((⌊s⌋ : ℤ)) : ℂ)).re = (((⌊s⌋ : ℤ)) : ℝ) := by simp
      rw [hcast]
      have hmem := hp_mem (τ (s - ((⌊s⌋ : ℤ) : ℝ))) (hτ1 _) (hτwin _ (le_of_lt (huIco s).2))
      linarith [hR'ge]
    refine ⟨s, ?_⟩
    exact huniq (γ₁ s) (p y) hre (hp_memR₀ y hy hy1)
      (by rw [hγ₁_Ψ, hs, hp_Ψ y hy hy1])
  have hsym : ∀ y : ℝ, 1 < y → y < t₁ → y ^ (32 : ℕ) < t₂ →
      q (y ^ (32 : ℕ)) = star (p y) + 1 / 2 := by
    intro y hy hy1 hy2
    have hy' : 1 < y ^ (32 : ℕ) := one_lt_pow₀ hy (by norm_num)
    have h1 : (q (y ^ (32 : ℕ))).re < -R₀ := hq_memR₀ _ hy' hy2
    have h2 : (star (p y) + 1 / 2).re < -R₀ := by
      have hmem := hp_mem y hy hy1
      have hre : (star (p y) + 1 / 2 : ℂ).re = (p y).re + 1 / 2 := by simp
      rw [hre]
      linarith [hR'ge]
    have h3 : fl.Ψ (q (y ^ (32 : ℕ))) = fl.Ψ (star (p y) + 1 / 2) := by
      rw [hq_Ψ _ hy' hy2, fl.Ψ_anti (p y), hp_Ψ y hy hy1, rayPt_g_alpha1 d hy]
    exact huniq _ _ h1 h2 h3
  have hcov₁ : ∀ w : ℂ, w.re < -R → (∃ t : ℝ, 1 < t ∧ t < t₀ ∧
      fl.Ψ w = Work.EL.rayPt d.hN Work.EL.alpha1 t) → w ∈ Set.range γ₁ := by
    rintro w hw ⟨t, ht1, htt, hΨ⟩
    have hwt : w = p t := by
      refine huniq w (p t) (lt_of_lt_of_le hw (by linarith [hRR₀])) (hp_memR₀ t ht1 (lt_trans htt ht₀_lt_t₁)) ?_
      rw [hΨ, hp_Ψ t ht1 (lt_trans htt ht₀_lt_t₁)]
    rw [hwt]
    exact hmem_γ₁ t ht1 htt
  have hcov₂ : ∀ w : ℂ, w.re < -R → (∃ t : ℝ, 1 < t ∧ t < t₀ ∧
      fl.Ψ w = Work.EL.rayPt d.hN Work.EL.alpha2 t) → w ∈ Set.range γ₂ := by
    rintro w hw ⟨t, ht1, htt, hΨ⟩
    have ht2 : t < t₂ := lt_of_lt_of_le htt (le_of_lt ht₀_t₂)
    have hwt : w = q t := by
      refine huniq w (q t) (lt_of_lt_of_le hw (by linarith [hRR₀])) (hq_memR₀ t ht1 ht2) ?_
      rw [hΨ, hq_Ψ t ht1 ht2]
    -- the level `t = y ^ 32` of the symmetric point
    have hy : 1 < t ^ ((32 : ℝ)⁻¹) := Real.one_lt_rpow ht1 (by norm_num)
    have hy_le_t₀ : t ^ ((32 : ℝ)⁻¹) ≤ t := by
      have := Real.rpow_le_rpow_of_exponent_le ht1.le (by norm_num : ((32 : ℝ)⁻¹) ≤ 1)
      simpa using this
    have hy1 : t ^ ((32 : ℝ)⁻¹) < t₁ :=
      lt_trans (lt_of_le_of_lt hy_le_t₀ htt) ht₀_lt_t₁
    have hy32 : (t ^ ((32 : ℝ)⁻¹)) ^ (32 : ℕ) = t := by
      have h : (t ^ ((32 : ℝ)⁻¹)) ^ (32 : ℝ) = t := by
        rw [← Real.rpow_mul (le_of_lt (by linarith : (0 : ℝ) < t)),
          show ((32 : ℝ)⁻¹) * 32 = 1 by norm_num, Real.rpow_one]
      simpa [Real.rpow_natCast] using h
    have hy2 : (t ^ ((32 : ℝ)⁻¹)) ^ (32 : ℕ) < t₂ := by
      rw [hy32]; exact ht2
    have hy0 : t ^ ((32 : ℝ)⁻¹) < t₀ := lt_of_le_of_lt hy_le_t₀ htt
    have hsym_t := hsym (t ^ ((32 : ℝ)⁻¹)) hy hy1 hy2
    rw [hy32] at hsym_t
    obtain ⟨s, hs⟩ := hmem_γ₁ (t ^ ((32 : ℝ)⁻¹)) hy hy0
    refine ⟨s, ?_⟩
    simp only [γ₂]
    rw [hs, ← hsym_t, ← hwt]
  -- ===================== 9. assembly =====================
  exact ⟨γ₁, γ₂, t₀, ht₀1, hγ₁_cont, hγ₂_cont, hγ₁_inj, hγ₂_inj, hγ₁_per, hγ₂_per,
    hγ₂_range, hγ₁_mem, hγ₂_mem, hcov₁, hcov₂⟩
