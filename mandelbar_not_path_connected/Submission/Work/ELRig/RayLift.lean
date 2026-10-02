/-
# ELRig — the lift data of the two root rays, and its consequences

`Work.ELRig.RayLift` bundles everything that **R-a2** of the contract
(`NOTES_LEAD_mandelbar_EL_F_contracts.md` §6, clause (ii)) needs about the two root rays
`R(α₁)`, `R(α₂)` and their lifts into the repelling half plane `{Re w < -R}` of the Fatou
coordinate `fl.Ψ`:

* the two `1`-periodic curves `γ₁, γ₂` with `γ₁(s+1) = γ₁(s)+1`, `γ₂ = conj γ₁ + ½`, and their
  level parametrisation `Ψ (γ₁ s) = rayPt α₁ (τ s)` with `τ` strictly increasing onto `(1,∞)`;
* the injectivity of `Ψ` on the half plane and the flower's facts (`R₀ < R`, `hzne` = `Ψ_small`,
  `pa_ends` = `Ψ_ends`);
* **the one geometric input** `strand : RayStrand d fl R`: *on the strand of `R(αᵢ)`, the smaller
  level is the deeper point* — i.e. the ray meets the repelling half plane in a single arc,
  transversal to the level (in Hubbard–Schleicher's language, `arXiv:1209.1753`, proof of
  Theorem 6.1: the two rays project to simple closed curves in the Ecalle cylinder).  It is **not**
  derivable from `RootParabolic` + the flower's fields + the two `LandsN` hypotheses — see
  `NOTES.md` §6 — so it enters as an explicit input from the parabolic-ray side, exactly like the
  structures of the sibling areas ELTop/ELPull/ELNest.

**Everything else is proved here**, including the contract's clause (ii) itself:

* `RayLift.re_surjective₁/₂` — the real parts of the two lifts are onto `ℝ`;
* `RayLift.mem_range₁/₂` — **the full identification** `Ψ⁻¹(R(αᵢ)) ∩ H_R = range γᵢ ∩ H_R`: every
  `Ψ`-preimage in the half plane of a point of the ray lies on the lift.  This uses the residual
  input, the existence part of the construction and the fact that the curve meets the horizontal
  line through the point;
* `RayLift.coverage` / `preimage_subset` — the same for the pair curve of `α₁, α₂` at `z₁`, the
  form the R-a3 consumer uses;
* `RayLift.mono₁/₂` — the lifts are graphs over the real axis (from the residual input);
* `RayLift.hΨ₂`, `RayLift.img₁/₂` — the second lift's level `(τ s)^32` and the images on the rays;
* `RayLift.hreal_of` and `RayLift.liftSidesOf` — the sign conditions and the plane topology
  `LiftSides` of the three regions (R-a2, clause (iii)), under the contradiction hypothesis
  `E ⊆ K`.

The producer of the curve data is `Work.ELRig.exists_liftCurvesV3` (with
`Work.ELRig.exists_liftCurvesV2` for the version without the exposed level map); see `NOTES.md` §7
for the assembly recipe.
-/

import Mathlib
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.ELRig.exists_liftSidesV2
import Submission.Work.ELRig.exists_liftSides_of_anti

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- A point of the ray `R(θ)` of the dynamical plane is the ray point of some level `t > 1`. -/
theorem mem_paramRay_exists_rayPt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {θ : ℝ} {z : ℂ}
    (h : z ∈ Work.EL.paramRay hN θ) :
    ∃ t : ℝ, 1 < t ∧ z = Work.EL.rayPt hN θ t := by
  have hrange : Work.EL.paramRay hN θ
      = Set.range (fun t : {t : ℝ // 1 < t} => Work.EL.rayPt hN θ t.1) :=
    Work.Top.NakaneData.paramRay_eq_range hN θ
  rw [hrange] at h
  obtain ⟨⟨t, ht⟩, htz⟩ := h
  exact ⟨t, ht, htz.symm⟩

/-- **The residual geometric input of R-a2**, stated without any reference to the lift curves:

> the root ray `R(αᵢ)` meets the repelling half plane `{Re < -R}` in a single arc, transversal to
> the level: on that arc the *level determines the position* — of two `Ψ`-preimages in
> `{Re < -R}` of points of `R(αᵢ)`, the one of smaller level has the smaller real part.

Equivalently, in Hubbard–Schleicher's language (`arXiv:1209.1753`, proof of Theorem 6.1), the two
rays project to *simple closed curves* in the Ecalle cylinder.  This is the one statement about the
parabolic local dynamics of `Ψ` at `z₁` that the drive has to add; it is not derivable from
`RootParabolic` together with the flower's fields and the two landing hypotheses (`LandsN`) — see
`NOTES.md` §6.  Its home is the ray/topology area (ELTop) or a future "repelling coordinate at the
parabolic point" area.  Everything else of R-a2 — including the *full* identification
`Ψ⁻¹(R(αᵢ)) ∩ H_R = lifts ∩ H_R` (`RayLift.mem_range₁/₂`) — is derived from it below. -/
structure RayStrand {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁) (R : ℝ) : Prop where
  /-- on the strand of `R(α₁)`, the smaller level is the deeper point. -/
  level_mono₁ : ∀ (w w' : ℂ) (t t' : ℝ), w.re < -R → w'.re < -R → 1 < t → 1 < t' → t < t' →
      fl.Ψ w = Work.EL.rayPt d.hN Work.EL.alpha1 t →
      fl.Ψ w' = Work.EL.rayPt d.hN Work.EL.alpha1 t' → w.re < w'.re
  /-- on the strand of `R(α₂)`, the smaller level is the deeper point. -/
  level_mono₂ : ∀ (w w' : ℂ) (t t' : ℝ), w.re < -R → w'.re < -R → 1 < t → 1 < t' → t < t' →
      fl.Ψ w = Work.EL.rayPt d.hN Work.EL.alpha2 t →
      fl.Ψ w' = Work.EL.rayPt d.hN Work.EL.alpha2 t' → w.re < w'.re

/-- **R-a2: the lift data of the two root rays.**  Only `strand : RayStrand d fl R` is assumed;
every other field is either proved in this area (`exists_liftCurvesV2`/`exists_liftCurvesV3`
produce the curves with the level parametrisation `τ`, the periodicity and the anti-symmetry) or is
a flower fact (`hzne` = `Ψ_small`, `pa_ends` = `Ψ_ends`) — except `hinj`, the injectivity of `Ψ`
on the half plane, which is the flower's `Ψ_inj` (for `R` above its level). -/
structure RayLift {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁) where
  /-- the lift of the ray `R(α₁)`. -/
  γ₁ : ℝ → ℂ
  /-- the lift of the ray `R(α₂)`. -/
  γ₂ : ℝ → ℂ
  /-- the level parametrisation: `Ψ (γ₁ s)` is the point of `R(α₁)` of level `τ s`. -/
  τ : ℝ → ℝ
  /-- the level of the repelling half plane `{Re w < -R}` in which the lifts live. -/
  R : ℝ
  /-- the level of the flower's `Ψ_ends`. -/
  R₀ : ℝ
  /-- the half-plane level is above the `Ψ_ends` level. -/
  hRR₀ : R₀ < R
  /-- the level parametrisation is strictly increasing. -/
  hτmono : StrictMono τ
  /-- all levels are `> 1`. -/
  hτ1 : ∀ s : ℝ, 1 < τ s
  /-- the first lift maps onto the ray at the level `τ s`. -/
  hΨ₁ : ∀ s : ℝ, fl.Ψ (γ₁ s) = Work.EL.rayPt d.hN Work.EL.alpha1 (τ s)
  /-- the first lift is continuous. -/
  cont₁ : Continuous γ₁
  /-- the second lift is continuous. -/
  cont₂ : Continuous γ₂
  /-- the first lift is `1`-periodic up to the translation `w ↦ w + 1`. -/
  per₁ : ∀ s : ℝ, γ₁ (s + 1) = γ₁ s + 1
  /-- the second lift is `1`-periodic up to the translation `w ↦ w + 1`. -/
  per₂ : ∀ s : ℝ, γ₂ (s + 1) = γ₂ s + 1
  /-- the anti-symmetry of the pair: `γ₂` is the reflection-shift of `γ₁`. -/
  anti : ∀ s : ℝ, γ₂ s = star (γ₁ s) + 1 / 2
  /-- `Ψ` is injective on the half plane (the flower's `Ψ_inj`, for `R` above its level). -/
  hinj : Set.InjOn fl.Ψ {w : ℂ | w.re < -R}
  /-- **the residual geometric input**. -/
  strand : RayStrand d fl R
  /-- `R` lies beyond the flower's avoidance level: `Ψ` misses the parabolic point there. -/
  hzne : ∀ w : ℂ, w.re < -R → fl.Ψ w ≠ d.z₁
  /-- the flower's `Ψ_ends` at the level `R₀`. -/
  pa_ends : ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → fl.Ψ w ∈ fl.Pa

namespace RayLift

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}

/-- The second lift maps onto the ray `R(α₂)` at the level `(τ s) ^ 32` (the antiholomorphic
square root `g = (T_c)^[5]` realises `t ↦ t^32` on the rays). -/
theorem hΨ₂ (L : RayLift d fl) (s : ℝ) :
    fl.Ψ (L.γ₂ s) = Work.EL.rayPt d.hN Work.EL.alpha2 ((L.τ s) ^ (32 : ℕ)) := by
  rw [L.anti s, fl.Ψ_anti, L.hΨ₁ s]
  exact Work.ELRig.rayPt_g_alpha1 d (L.hτ1 s)

/-- The first lift maps into the ray `R(α₁)`. -/
theorem img₁ (L : RayLift d fl) (s : ℝ) :
    fl.Ψ (L.γ₁ s) ∈ Work.EL.paramRay d.hN Work.EL.alpha1 := by
  rw [L.hΨ₁ s]
  exact Work.EL.rayPt_mem_paramRay d.hN (L.hτ1 s)

/-- The second lift maps into the ray `R(α₂)`. -/
theorem img₂ (L : RayLift d fl) (s : ℝ) :
    fl.Ψ (L.γ₂ s) ∈ Work.EL.paramRay d.hN Work.EL.alpha2 := by
  rw [L.hΨ₂ s]
  exact Work.EL.rayPt_mem_paramRay d.hN (one_lt_pow₀ (L.hτ1 s) (by norm_num))

/-- **The lifts are graphs over the real axis**: their real parts are strictly increasing.  This is
derived from the curve-free strand input: two points of the same strand in the half plane are
ordered by their levels. -/
theorem mono₁ (L : RayLift d fl) : StrictMono fun s : ℝ => (L.γ₁ s).re := by
  have hadd : ∀ (n : ℕ) (σ : ℝ), L.γ₁ (σ + (n : ℝ)) = L.γ₁ σ + (n : ℂ) := by
    intro n
    induction n with
    | zero => intro σ; simp
    | succ k ih =>
      intro σ
      rw [show σ + (((k : ℕ) + 1 : ℕ) : ℝ) = (σ + ((k : ℕ) : ℝ)) + 1 by push_cast; ring,
        L.per₁, ih σ]
      push_cast; ring
  have hshift : ∀ (n : ℕ) (σ : ℝ), (L.γ₁ (σ - (n : ℝ))).re = (L.γ₁ σ).re - (n : ℝ) := by
    intro n σ
    have h := hadd n (σ - (n : ℝ))
    rw [show σ - (n : ℝ) + (n : ℝ) = σ by ring] at h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re] at this
    linarith
  intro s s' hss'
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (L.γ₁ s).re - (n : ℝ) < -L.R ∧ (L.γ₁ s').re - (n : ℝ) < -L.R := by
    obtain ⟨n, hn⟩ := exists_nat_gt (max ((L.γ₁ s).re + L.R) ((L.γ₁ s').re + L.R))
    exact ⟨n, by have := le_max_left ((L.γ₁ s).re + L.R) ((L.γ₁ s').re + L.R); linarith,
      by have := le_max_right ((L.γ₁ s).re + L.R) ((L.γ₁ s').re + L.R); linarith⟩
  have hsn : (L.γ₁ (s - n)).re = (L.γ₁ s).re - (n : ℝ) := hshift n s
  have hs'n : (L.γ₁ (s' - n)).re = (L.γ₁ s').re - (n : ℝ) := hshift n s'
  have hlt : s - (n : ℝ) < s' - (n : ℝ) := by linarith
  have hτlt : L.τ (s - n) < L.τ (s' - n) := L.hτmono hlt
  have h := L.strand.level_mono₁ (L.γ₁ (s - n)) (L.γ₁ (s' - n)) (L.τ (s - n)) (L.τ (s' - n))
    (by rw [hsn]; exact hn.1) (by rw [hs'n]; exact hn.2) (L.hτ1 _) (L.hτ1 _) hτlt
    (L.hΨ₁ _) (L.hΨ₁ _)
  rw [hsn, hs'n] at h
  linarith

/-- The second lift is a graph over the real axis. -/
theorem mono₂ (L : RayLift d fl) : StrictMono fun s : ℝ => (L.γ₂ s).re := by
  have hadd : ∀ (n : ℕ) (σ : ℝ), L.γ₂ (σ + (n : ℝ)) = L.γ₂ σ + (n : ℂ) := by
    intro n
    induction n with
    | zero => intro σ; simp
    | succ k ih =>
      intro σ
      rw [show σ + (((k : ℕ) + 1 : ℕ) : ℝ) = (σ + ((k : ℕ) : ℝ)) + 1 by push_cast; ring,
        L.per₂, ih σ]
      push_cast; ring
  have hshift : ∀ (n : ℕ) (σ : ℝ), (L.γ₂ (σ - (n : ℝ))).re = (L.γ₂ σ).re - (n : ℝ) := by
    intro n σ
    have h := hadd n (σ - (n : ℝ))
    rw [show σ - (n : ℝ) + (n : ℝ) = σ by ring] at h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re] at this
    linarith
  intro s s' hss'
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (L.γ₂ s).re - (n : ℝ) < -L.R ∧ (L.γ₂ s').re - (n : ℝ) < -L.R := by
    obtain ⟨n, hn⟩ := exists_nat_gt (max ((L.γ₂ s).re + L.R) ((L.γ₂ s').re + L.R))
    exact ⟨n, by have := le_max_left ((L.γ₂ s).re + L.R) ((L.γ₂ s').re + L.R); linarith,
      by have := le_max_right ((L.γ₂ s).re + L.R) ((L.γ₂ s').re + L.R); linarith⟩
  have hsn : (L.γ₂ (s - n)).re = (L.γ₂ s).re - (n : ℝ) := hshift n s
  have hs'n : (L.γ₂ (s' - n)).re = (L.γ₂ s').re - (n : ℝ) := hshift n s'
  have hlt : s - (n : ℝ) < s' - (n : ℝ) := by linarith
  have hτlt : L.τ (s - n) < L.τ (s' - n) := L.hτmono hlt
  have hpow : (L.τ (s - n)) ^ (32 : ℕ) < (L.τ (s' - n)) ^ (32 : ℕ) :=
    pow_lt_pow_left₀ hτlt (le_of_lt (lt_trans zero_lt_one (L.hτ1 _))) (by norm_num : (32 : ℕ) ≠ 0)
  have h := L.strand.level_mono₂ (L.γ₂ (s - n)) (L.γ₂ (s' - n))
    ((L.τ (s - n)) ^ (32 : ℕ)) ((L.τ (s' - n)) ^ (32 : ℕ))
    (by rw [hsn]; exact hn.1) (by rw [hs'n]; exact hn.2)
    (one_lt_pow₀ (L.hτ1 _) (by norm_num)) (one_lt_pow₀ (L.hτ1 _) (by norm_num)) hpow
    (L.hΨ₂ _) (L.hΨ₂ _)
  rw [hsn, hs'n] at h
  linarith

/-- **The real part of the first lift is onto.**  It is continuous and strictly monotone and, by
the `1`-periodicity, unbounded above and below. -/
theorem re_surjective₁ (L : RayLift d fl) : Function.Surjective fun s : ℝ => (L.γ₁ s).re := by
  have hcont : Continuous fun s : ℝ => (L.γ₁ s).re := Complex.continuous_re.comp L.cont₁
  have hadd : ∀ (n : ℕ) (σ : ℝ), L.γ₁ (σ + (n : ℝ)) = L.γ₁ σ + (n : ℂ) := by
    intro n
    induction n with
    | zero => intro σ; simp
    | succ k ih =>
      intro σ
      rw [show σ + (((k : ℕ) + 1 : ℕ) : ℝ) = (σ + ((k : ℕ) : ℝ)) + 1 by push_cast; ring,
        L.per₁, ih σ]
      push_cast; ring
  have hneg : ∀ (k : ℕ), (L.γ₁ (-(k : ℝ))).re = (L.γ₁ 0).re - (k : ℝ) := by
    intro k
    have h := hadd k (-(k : ℝ))
    rw [show -(k : ℝ) + (k : ℝ) = 0 by ring] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re] at h2
    linarith
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt (y - (L.γ₁ 0).re)
  obtain ⟨k, hk⟩ := exists_nat_gt ((L.γ₁ 0).re - y)
  have hn' : y < (L.γ₁ ((n : ℕ) : ℝ)).re := by
    have h := hadd n 0
    simp only [zero_add] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re] at h2
    rw [h2]; linarith
  have hk' : (L.γ₁ (-(k : ℝ))).re < y := by
    rw [hneg k]; linarith
  have hy : y ∈ Set.Icc ((fun s : ℝ => (L.γ₁ s).re) (-(k : ℝ)))
      ((fun s : ℝ => (L.γ₁ s).re) ((n : ℕ) : ℝ)) := ⟨le_of_lt hk', le_of_lt hn'⟩
  obtain ⟨c, -, hc⟩ := intermediate_value_Icc (by linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) n])
    hcont.continuousOn hy
  exact ⟨c, hc⟩

/-- The real part of the second lift is onto. -/
theorem re_surjective₂ (L : RayLift d fl) : Function.Surjective fun s : ℝ => (L.γ₂ s).re := by
  have hcont : Continuous fun s : ℝ => (L.γ₂ s).re := Complex.continuous_re.comp L.cont₂
  have hadd : ∀ (n : ℕ) (σ : ℝ), L.γ₂ (σ + (n : ℝ)) = L.γ₂ σ + (n : ℂ) := by
    intro n
    induction n with
    | zero => intro σ; simp
    | succ k ih =>
      intro σ
      rw [show σ + (((k : ℕ) + 1 : ℕ) : ℝ) = (σ + ((k : ℕ) : ℝ)) + 1 by push_cast; ring,
        L.per₂, ih σ]
      push_cast; ring
  have hneg : ∀ (k : ℕ), (L.γ₂ (-(k : ℝ))).re = (L.γ₂ 0).re - (k : ℝ) := by
    intro k
    have h := hadd k (-(k : ℝ))
    rw [show -(k : ℝ) + (k : ℝ) = 0 by ring] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re] at h2
    linarith
  intro y
  obtain ⟨n, hn⟩ := exists_nat_gt (y - (L.γ₂ 0).re)
  obtain ⟨k, hk⟩ := exists_nat_gt ((L.γ₂ 0).re - y)
  have hn' : y < (L.γ₂ ((n : ℕ) : ℝ)).re := by
    have h := hadd n 0
    simp only [zero_add] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re] at h2
    rw [h2]; linarith
  have hk' : (L.γ₂ (-(k : ℝ))).re < y := by
    rw [hneg k]; linarith
  have hy : y ∈ Set.Icc ((fun s : ℝ => (L.γ₂ s).re) (-(k : ℝ)))
      ((fun s : ℝ => (L.γ₂ s).re) ((n : ℕ) : ℝ)) := ⟨le_of_lt hk', le_of_lt hn'⟩
  obtain ⟨c, -, hc⟩ := intermediate_value_Icc (by linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) n])
    hcont.continuousOn hy
  exact ⟨c, hc⟩

/-- **R-a2 (ii), full form: every `Ψ`-preimage in the half plane of a point of `R(α₁)` lies on the
first lift.**  This is the identification `Ψ⁻¹(R(α₁)) ∩ H_R = range γ₁ ∩ H_R`; it is *derived*
from the residual strand input: the curve meets the horizontal line through `w` (its real part is
onto) and the strand input forces the two points to have the same parameter. -/
theorem mem_range₁ (L : RayLift d fl) {w : ℂ} (hw : w.re < -L.R)
    (h : fl.Ψ w ∈ Work.EL.paramRay d.hN Work.EL.alpha1) : w ∈ Set.range L.γ₁ := by
  obtain ⟨t, ht, hwt⟩ := mem_paramRay_exists_rayPt d.hN h
  obtain ⟨s, hs0⟩ := L.re_surjective₁ w.re
  have hs : (L.γ₁ s).re = w.re := hs0
  have hsR : (L.γ₁ s).re < -L.R := by rw [hs]; exact hw
  have hlev : L.τ s = t := by
    rcases lt_trichotomy (L.τ s) t with hlt | heq | hgt
    · exact absurd (L.strand.level_mono₁ (L.γ₁ s) w (L.τ s) t hsR hw (L.hτ1 s) ht hlt
        (L.hΨ₁ s) hwt) (not_lt.mpr (le_of_eq hs.symm))
    · exact heq
    · exact absurd (L.strand.level_mono₁ w (L.γ₁ s) t (L.τ s) hw hsR ht (L.hτ1 s) hgt
        hwt (L.hΨ₁ s)) (not_lt.mpr (le_of_eq hs))
  have hw' : w = L.γ₁ s := L.hinj hw hsR (by rw [hwt, L.hΨ₁ s, hlev])
  exact ⟨s, hw'.symm⟩

/-- **R-a2 (ii), full form, second ray.** -/
theorem mem_range₂ (L : RayLift d fl) {w : ℂ} (hw : w.re < -L.R)
    (h : fl.Ψ w ∈ Work.EL.paramRay d.hN Work.EL.alpha2) : w ∈ Set.range L.γ₂ := by
  obtain ⟨t, ht, hwt⟩ := mem_paramRay_exists_rayPt d.hN h
  obtain ⟨s, hs0⟩ := L.re_surjective₂ w.re
  have hs : (L.γ₂ s).re = w.re := hs0
  have hsR : (L.γ₂ s).re < -L.R := by rw [hs]; exact hw
  have hlev : (L.τ s) ^ (32 : ℕ) = t := by
    rcases lt_trichotomy ((L.τ s) ^ (32 : ℕ)) t with hlt | heq | hgt
    · exact absurd (L.strand.level_mono₂ (L.γ₂ s) w ((L.τ s) ^ (32 : ℕ)) t hsR hw
        (one_lt_pow₀ (L.hτ1 s) (by norm_num)) ht hlt (L.hΨ₂ s) hwt)
        (not_lt.mpr (le_of_eq hs.symm))
    · exact heq
    · exact absurd (L.strand.level_mono₂ w (L.γ₂ s) t ((L.τ s) ^ (32 : ℕ)) hw hsR
        ht (one_lt_pow₀ (L.hτ1 s) (by norm_num)) hgt hwt (L.hΨ₂ s))
        (not_lt.mpr (le_of_eq hs))
  have hw' : w = L.γ₂ s := L.hinj hw hsR (by rw [hwt, L.hΨ₂ s, hlev])
  exact ⟨s, hw'.symm⟩

/-- **The Ψ-preimages of the pair curve in the half plane are exactly the two lifts** (R-a2,
clause (ii), in the honest tail form). -/
theorem coverage (L : RayLift d fl) {P : Work.EL.CoPair d.hN}
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    {w : ℂ} (hw : w.re < -L.R) (hmem : fl.Ψ w ∈ Work.EL.pairCurve P) :
    w ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
  rcases (Work.EL.mem_pairCurve_iff P (fl.Ψ w)).mp hmem with h | h | h
  · exact Or.inl (L.mem_range₁ hw (hPa ▸ h))
  · exact absurd (h.trans hPy) (L.hzne w hw)
  · exact Or.inr (L.mem_range₂ hw (hPb ▸ h))

/-- Under the contradiction hypothesis `E ⊆ K c` of R-a3, the real axis below the level `-R`
avoids the two lifts: a real point of a lift would have `Ψ`-image on one of the two rays, hence
outside `K c`. -/
theorem hreal_of (L : RayLift d fl) (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) :
    ∀ x : ℝ, x < -L.R → (x : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
  rintro x _ (h | h)
  · obtain ⟨s, hs⟩ := h
    have hmem : fl.Ψ (x : ℂ) ∈ Work.EL.paramRay d.hN Work.EL.alpha1 := by
      rw [← hs]; exact L.img₁ s
    exact (Work.EL.paramRay_subset_compl d.hN Work.EL.alpha1 hmem) (hE x)
  · obtain ⟨s, hs⟩ := h
    have hmem : fl.Ψ (x : ℂ) ∈ Work.EL.paramRay d.hN Work.EL.alpha2 := by
      rw [← hs]; exact L.img₂ s
    exact (Work.EL.paramRay_subset_compl d.hN Work.EL.alpha2 hmem) (hE x)

/-- **The plane topology of the two lifts** (R-a2, clause (iii)).  Derived from the curve data
alone (`Work.ELRig.exists_liftSides_of_anti`); the two sign conditions are derived from the
anti-symmetry together with `hreal_of`. -/
noncomputable def liftSidesOf (L : RayLift d fl)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) :
    Work.EL.LiftSides d.hN d.z₁ L.γ₁ L.γ₂ L.R L.R₀ :=
  (exists_liftSides_of_anti L.hRR₀ L.cont₁ L.cont₂ L.mono₁ L.mono₂ L.per₁ L.per₂
    (by
      show Set.range L.γ₂ = (fun w : ℂ => star w + 1 / 2) '' Set.range L.γ₁
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun s => (L.anti s)))
    (L.hreal_of hE)).some

/-- The same statement in the `∀`-form used by the consumers. -/
theorem preimage_subset (L : RayLift d fl) {P : Work.EL.CoPair d.hN}
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁) :
    ∀ w : ℂ, w.re < -L.R → fl.Ψ w ∈ Work.EL.pairCurve P →
      w ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ :=
  fun w hw hmem => L.coverage hPa hPb hPy hw hmem

end RayLift
