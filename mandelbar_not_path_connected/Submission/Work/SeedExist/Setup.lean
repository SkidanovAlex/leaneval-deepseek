/-
# SeedExist — the working setup: the seed data, the α-pairs, the wake arcs

This file fixes the language of the area `Submission/Work/SeedExist/` on top of
`Work.EL` (`Submission/Work/ELTop/Defs.lean`), `Work.Landing` and
`Work.ParamRays`.  Everything in the area is phrased with

* `S : Work.SeedExist.RootSeedData` — the data of the explicit certified seed of
  `NOTES_LEAD_mandelbar_noncusp.md` §2.1 (a parameter `c ∈ Mandelbar`, a simple parabolic
  fixed point `z₁` of `F c = (T_c)^[10]` of exact `T_c`-period `5`, and the landing of the
  two root rays at `z₁`);
* `hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c)` — the dynamical Böttcher data
  (`Work.ParamRays.dynNakane` of Böttcher's theorem `Work.ParamRays.DynBottcherHomeo`).

## Main definitions

* `RootSeedData`, `ExplicitRootSeed.toData`;
* `alphaPair c z₁ j` — the level-`j` α-pair of the root portrait, at its **true** landing
  point `(T_c)^[j] z₁` (this is `Work.EL.alphaPairRaw`);
* `Sfar`, `Snear` — the two sides of the level-`0` α-pair, through the wake arc `W₀` and
  through its complement;
* `wakeSide_eq` — the definitional identity exhibiting `Work.EL.wakeSide` as the side
  through the wake arc.

## Conventions

Angles are real numbers modulo `1`; `Work.EL.InArc x a b` is the open counterclockwise arc.
The wake arcs are `W_j = (wakeLo j, wakeHi j)`; for `j = 3, 4` the arc wraps around `0`
(`wakeHi j < wakeLo j` as reals), which `Int.fract` accounts for.
-/
import Submission.Work.SeedExist.Defs
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.landsN_iff_landsAt
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELPull.Defs
import Submission.Work.ELPull.tantibar_openMap
import Submission.Work.ELPull.pb1Top
import Submission.Work.FSeed.Defs
import Submission.Work.FSeed.Inputs
import Submission.Work.FSeed.Classify
import Submission.Work.FatouCoordFix.FlowerFix.ExistsFix
import Submission.Work.ELRig.Pa_subset_K
import Submission.Work.ParamRays.DynBottcher
import Submission.Work.Top.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedExist

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The seed data -/

/-- **The data of the explicit root seed** (`NOTES_LEAD_mandelbar_noncusp.md` §2.1): a
parameter `c ∈ Mandelbar` at which `F c = (T_c)^[10]` has a **simple** parabolic fixed point
`z₁` of exact `T_c`-period `5`, and at which both root rays `α₁`, `α₂` land at `z₁`.

This is the hypothesis-free replacement for `NonCuspRootLimit`: it is a `Prop` with no cited
content (the area `SeedCert` proves the `Prop`-form `ExplicitRootSeed`). -/
structure RootSeedData where
  /-- the parameter. -/
  c : ℂ
  /-- the characteristic parabolic point. -/
  z₁ : ℂ
  /-- `c` lies in the mandelbar. -/
  mem : c ∈ Mandelbar
  /-- `z₁` is fixed by the second return map `(T_c)^[5]`. -/
  g_fix : (Tantibar c)^[5] z₁ = z₁
  /-- `z₁` has exact `T_c`-period `5`. -/
  exact_period : ∀ j : ℕ, 0 < j → j < 5 → (Tantibar c)^[j] z₁ ≠ z₁
  /-- the multiplier of the second return map at `z₁` is `1`. -/
  mult_one : Work.Landing.multiplier2 c 5 z₁ = 1
  /-- `z₁` is simple: `F''(z₁) ≠ 0`. -/
  simple : iteratedDeriv 2 (Work.FSeed.F c) z₁ ≠ 0
  /-- the first root ray lands at `z₁`. -/
  lands_α₁ : Work.Landing.landsAt c Work.FSeed.α₁ z₁
  /-- the second root ray lands at `z₁`. -/
  lands_α₂ : Work.Landing.landsAt c Work.FSeed.α₂ z₁

/-- Every `ExplicitRootSeed` yields a `RootSeedData`. -/
theorem ExplicitRootSeed.toData (h : ExplicitRootSeed) : Nonempty RootSeedData := by
  obtain ⟨c, z₁, hm, hg, he, hmu, hs, hα₁, hα₂⟩ := h
  exact ⟨⟨c, z₁, hm, hg, he, hmu, hs, hα₁, hα₂⟩⟩

/-- The root angles of `Work.EL` are those of `Work.FSeed`. -/
theorem el_alpha1_eq : Work.EL.alpha1 = Work.FSeed.α₁ := rfl

theorem el_alpha2_eq : Work.EL.alpha2 = Work.FSeed.α₂ := rfl

/-- The `F` of `Work.EL` is that of `Work.FSeed`. -/
theorem el_F_eq (c : ℂ) : Work.EL.F c = Work.FSeed.F c := rfl

/-! ## The dynamical Böttcher data of the seed -/

/-- The dynamical Böttcher data of the seed, from Böttcher's theorem and `c ∈ Mandelbar`. -/
noncomputable def hNof (S : RootSeedData) (hdyn : Work.ParamRays.DynBottcherHomeo S.c) :
    Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c) :=
  Work.ParamRays.dynNakane hdyn

/-- The Böttcher condition carried by `RootSeedData` plus Böttcher's theorem. -/
theorem isDynBottcher_dynPhiOf_of_homeo {c : ℂ} (h : Work.ParamRays.DynBottcherHomeo c) :
    Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
  Work.ParamRays.isDynBottcher_dynPhiOf h.exists

/-! ## The α-pairs and the sides -/

/-- **The level-`j` α-pair of the root portrait, at its true landing point**
`(T_c)^[j] z₁`.  This is `Work.EL.alphaPairRaw`; the two angles are
`min (T^[j] α₁) (T^[j] α₂)` and `max (T^[j] α₁) (T^[j] α₂)`.

(The earlier version of `Work.EL.alphaPairRaw` stored `z₁` as the landing point for every `j`;
that defect is repaired in `Submission/Work/ELTop/Defs.lean`, so the sides below are the true
sides.) -/
abbrev alphaPair (c z₁ : ℂ) (j : ℕ) : Work.EL.RawPair := Work.EL.alphaPairRaw c z₁ j

/-- **The side `S_j` of the level-`j` α-pair through the wake arc `W_j`** — this is the side
of the `wake` field of `Work.EL.RootParabolic`. -/
abbrev wakeSide {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z₁ : ℂ) (j : ℕ) : Set ℂ :=
  Work.EL.RawPair.sideThrough hN (alphaPair c z₁ j) (Work.EL.wakeLo j) (Work.EL.wakeHi j)

/-- The definition of `Work.EL.wakeSide` exhibits it as `wakeSide`. -/
theorem wakeSide_eq {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z₁ : ℂ) (j : ℕ) :
    Work.EL.wakeSide hN z₁ j = wakeSide hN z₁ j := rfl

/-- **The far side `S` of the level-`0` α-pair**: the side through the wake arc
`W₀ = (α₁, α₂)`.  This is `Work.EL.wakeSide hN z₁ 0`. -/
abbrev Sfar {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z₁ : ℂ) : Set ℂ :=
  wakeSide hN z₁ 0

/-- **The near side `S'` of the level-`0` α-pair**: the side through the complementary
(long) arc, from `α₂` counterclockwise to `α₁`. -/
abbrev Snear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z₁ : ℂ) : Set ℂ :=
  Work.EL.RawPair.sideThrough hN (alphaPair c z₁ 0) (Work.EL.wakeHi 0) (Work.EL.wakeLo 0)

/-- **The characteristic (immediate-basin) component of the critical value**: the connected
component of `c` in the interior of the filled Julia set. -/
noncomputable def U (c : ℂ) : Set ℂ := connectedComponentIn (interior (Work.EL.K c)) c

/-- **The characteristic component of `0`**: the connected component of `0` in the interior of
the filled Julia set. -/
noncomputable def U₀ (c : ℂ) : Set ℂ := connectedComponentIn (interior (Work.EL.K c)) 0

/-! ## Angle arithmetic of the α-orbit and of the wake arcs -/

theorem T_five_α₁ : (Work.EL.T^[5]) Work.EL.alpha1 = Work.EL.alpha2 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2, Int.fract,
    Function.iterate_succ_apply', Function.iterate_zero]

theorem T_five_α₂ : (Work.EL.T^[5]) Work.EL.alpha2 = Work.EL.alpha1 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2, Int.fract,
    Function.iterate_succ_apply', Function.iterate_zero]

theorem T_ten_α₁ : (Work.EL.T^[10]) Work.EL.alpha1 = Work.EL.alpha1 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2, Int.fract,
    Function.iterate_succ_apply', Function.iterate_zero]

theorem T_ten_α₂ : (Work.EL.T^[10]) Work.EL.alpha2 = Work.EL.alpha2 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2, Int.fract,
    Function.iterate_succ_apply', Function.iterate_zero]

theorem wakeLo_zero : Work.EL.wakeLo 0 = Work.EL.alpha1 := rfl

theorem wakeHi_zero : Work.EL.wakeHi 0 = Work.EL.alpha2 := rfl

/-- The length of the wake arc `W_j`, for `j < 5`. -/
theorem arcLen_wake (j : ℕ) (hj : j < 5) :
    Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) = 33 * 2 ^ j / 1023 := by
  interval_cases j <;>
    norm_num [Work.EL.wakeLo, Work.EL.wakeHi, Work.EL.arcLen, Int.fract]

/-- The wake arcs `W_j` are short (length `< 1/2`) for `j ≤ 3`. -/
theorem arcLen_wake_lt_half (j : ℕ) (hj : j ≤ 3) :
    Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) < 1 / 2 := by
  have h := arcLen_wake j (by omega)
  rw [h]
  interval_cases j <;> norm_num

/-! ## The arc-image relation of the wake arcs -/

/-- The `Int.fract` of `T θ - c` is that of `-2θ - c`. -/
theorem fract_T_sub (θ c : ℝ) : Int.fract (Work.EL.T θ - c) = Int.fract (-2 * θ - c) := by
  rw [Work.EL.T]
  exact Work.ELPull.fract_fract_sub' (-2 * θ) c

/-- **The general forward arc-image lemma.**  If `L ∈ (0, 1/2)` and `fract (-2a - c) = 2L`,
then the image under `T` of the counterclockwise arc `(a, a+L)` lies in the counterclockwise
arc `(c, c+2L)`. -/
theorem InArc_T_of {a c L : ℝ} (hL : 0 < L) (h2L : 2 * L < 1)
    (hcf : Int.fract (-2 * a - c) = 2 * L) {θ : ℝ} (hθ : Work.EL.InArc θ a (a + L)) :
    Work.EL.InArc (Work.EL.T θ) c (c + 2 * L) := by
  have hL1 : L < 1 := by linarith
  have hx0 : 0 < Int.fract (θ - a) := hθ.1
  have hxl : Int.fract (θ - a) < L := by
    have h := hθ.2
    rw [Work.EL.arcLen, show a + L - a = L by ring,
      Int.fract_eq_self.mpr ⟨le_of_lt hL, hL1⟩] at h
    exact h
  set x : ℝ := Int.fract (θ - a) with hx
  have hdec : θ - a = x + (⌊θ - a⌋ : ℝ) := by
    rw [hx, Int.fract]; ring
  have hkey : Int.fract (Work.EL.T θ - c) = 2 * L - 2 * x := by
    rw [fract_T_sub]
    have h1 : -2 * θ - c = (-2 * a - c - 2 * x) + ((-2 * (⌊θ - a⌋ : ℤ) : ℤ) : ℝ) := by
      have := hdec
      push_cast at this ⊢
      linear_combination (-2) * this
    rw [h1, Int.fract_add_intCast]
    have h3 : -2 * a - c = Int.fract (-2 * a - c) + (⌊-2 * a - c⌋ : ℝ) := by
      rw [Int.fract]; ring
    rw [hcf] at h3
    have h2 : -2 * a - c - 2 * x = (2 * L - 2 * x) + ((⌊-2 * a - c⌋ : ℤ) : ℝ) := by
      push_cast
      linear_combination h3
    rw [h2, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have harc : Work.EL.arcLen c (c + 2 * L) = 2 * L := by
    rw [Work.EL.arcLen, show c + 2 * L - c = 2 * L by ring]
    exact Int.fract_eq_self.mpr ⟨by linarith, h2L⟩
  rw [Work.EL.InArc, hkey, harc]
  constructor <;> linarith

/-- The wake arcs `W_j` are nonempty. -/
theorem arcLen_wake_pos (j : ℕ) (hj : j < 5) :
    0 < Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) := by
  rw [arcLen_wake j hj]
  interval_cases j <;> norm_num

/-- The double of the length of `W_j` is the length of `W_{j+1}`, for `j ≤ 3`. -/
theorem arcLen_wake_succ (j : ℕ) (hj : j ≤ 3) :
    Work.EL.arcLen (Work.EL.wakeLo (j + 1)) (Work.EL.wakeHi (j + 1)) =
      2 * Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) := by
  rw [arcLen_wake (j + 1) (by omega), arcLen_wake j (by omega)]
  have : (33 : ℝ) * 2 ^ (j + 1) / 1023 = 2 * (33 * 2 ^ j / 1023) := by
    rw [pow_succ]; ring
  rw [this]

/-- The wake arcs `W_j` have length `L_j = 33·2^j/1023`, and `fract (-2·wakeLo j - wakeLo (j+1))
= 2 L_j` for `j ≤ 3` (the numerical content of the arc-image relation). -/
theorem fract_wake (j : ℕ) (hj : j ≤ 3) :
    Int.fract (-2 * Work.EL.wakeLo j - Work.EL.wakeLo (j + 1)) =
      2 * Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) := by
  interval_cases j <;>
    norm_num [Work.EL.wakeLo, Work.EL.wakeHi, Work.EL.arcLen, Int.fract,
      show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
      show (2 : ℕ) + 1 = 3 from rfl, show (3 : ℕ) + 1 = 4 from rfl]

/-- The relation `wakeHi j = wakeLo j + L_j` of the wake arcs (for `j ≤ 4`). -/
theorem wakeHi_eq (j : ℕ) (hj : j ≤ 4) :
    Work.EL.wakeHi j = Work.EL.wakeLo j + Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) := by
  interval_cases j <;>
    norm_num [Work.EL.wakeLo, Work.EL.wakeHi, Work.EL.arcLen, Int.fract,
      show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
      show (2 : ℕ) + 1 = 3 from rfl, show (3 : ℕ) + 1 = 4 from rfl,
      show (4 : ℕ) + 1 = 5 from rfl]

/-- **The angle map carries the wake arc `W_j` into `W_{j+1}`**, for `j ≤ 3`.  This is the
combinatorial fact behind the side image `T_c '' S_j = S_{j+1}`. -/
theorem InArc_T_wake (j : ℕ) (hj : j ≤ 3) {θ : ℝ}
    (hθ : Work.EL.InArc θ (Work.EL.wakeLo j) (Work.EL.wakeHi j)) :
    Work.EL.InArc (Work.EL.T θ) (Work.EL.wakeLo (j + 1)) (Work.EL.wakeHi (j + 1)) := by
  have hLpos := arcLen_wake_pos j (by omega)
  have h2L : 2 * Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j) < 1 := by
    have := arcLen_wake_lt_half j hj
    linarith
  have hθ' : Work.EL.InArc θ (Work.EL.wakeLo j)
      (Work.EL.wakeLo j + Work.EL.arcLen (Work.EL.wakeLo j) (Work.EL.wakeHi j)) := by
    rwa [← wakeHi_eq j (by omega)]
  have hmain := InArc_T_of hLpos h2L (fract_wake j hj) hθ'
  rw [wakeHi_eq (j + 1) (by omega), arcLen_wake_succ j hj]
  exact hmain

end Work.SeedExist

end
