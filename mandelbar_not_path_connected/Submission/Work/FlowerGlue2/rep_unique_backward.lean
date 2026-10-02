/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Mathlib
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.exists_back_entry
import Submission.Work.FlowerGlue2.w0_step
import Submission.Work.FlowerGlue2.rigid_of_halfPlane
import Submission.Work.ELRig.analyticOnNhd_invFunOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.rep_unique_backward` — repelling Fatou uniqueness for an arbitrary flower

Item FG-d of `Submission/Work/NOTES_LEAD_mandelbar_gaps3.md` §1: an *unconditional* repelling
Fatou uniqueness statement.  The flower's repelling coordinate `fl.Ψ` and a reference repelling
coordinate `Ψ₁` of the same germ, which agree on a Stolz sector in the sense of the hypothesis
`hsurj`, differ by a translation on a far-left half-plane.

The design is the one of §1.2 of that note, and the two hypotheses of the earlier conditional
form `Work.FlowerGlue2.rep_unique_of_image_cyl` are removed as follows.

* `himg` is *false* as stated (by `Ψ_ends`, the large-`|Im|` part of every left half-plane is sent
  by `fl.Ψ` into the attracting petal, hence never into the range of an injective `Ψ₁`).  The fix
  is to shift each point further left by its own amount: for `Re u < -N₀` the backward orbit
  `fl.Ψ (u - n)` enters the Stolz petal `Dst P R₂` for some `n` and stays there
  (`Work.FlowerGlue2.exists_back_entry`), so the comparison map
  `T u := Φ (fl.Ψ (u - n u)) + n u` (`Φ := invFunOn Ψ₁ {Re w < -R₁}`,
  `n u := Nat.find` of the entry property) is well defined on `{Re u < -N₁}`.
* `hΦ` (a holomorphic inverse of `Ψ₁`) is free: `Work.ELRig.analyticOnNhd_invFunOn`.

`T` is holomorphic (the index `n u` is locally constant, on the open set where
`fl.Ψ (u - n u) ∈ Dst P R₂`), injective (by `fl.Ψ_inj` together with `Ψ₁ (Φ z) = z` on the
petal) and `1`-equivariant, so `Work.FlowerGlue2.rigid_of_halfPlane` gives `T u = u + s`.
Unfolding `T` and pushing the shift `n u` steps forward with `fl.Ψ_shift` and `h₁.shift` yields
`fl.Ψ u = Ψ₁ (u + s)`.

Only `Ψ_diff`, `Ψ_shift`, `Ψ_small` and `Ψ_inj` of the flower are used; `Pa`, `cover` and
`Ψ_ends` play no role.
-/

namespace Work.FlowerGlue2

open Filter Set Metric
open scoped Topology

open Work.PARIMPL (ParNormal Ft gtc)

set_option maxHeartbeats 1600000

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-!
## Auxiliary iteration lemmas

Two elementary facts about iterating a shift relation `Ψ (w + 1) = F (Ψ w)`.
-/

/-- Iterates of a shift relation that holds everywhere. -/
theorem shift_iter {F Ψ : ℂ → ℂ} (hsh : ∀ w : ℂ, Ψ (w + 1) = F (Ψ w)) (w : ℂ) (k : ℕ) :
    Ψ (w + (k : ℂ)) = F^[k] (Ψ w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcast : w + ((k + 1 : ℕ) : ℂ) = (w + (k : ℂ)) + 1 := by push_cast; ring
    rw [hcast, hsh, ih, Function.iterate_succ_apply']

/-- Iterates of a shift relation that is only available on the half-plane `Re w < -R`. -/
theorem shift_iter_of_re {F Ψ : ℂ → ℂ} {R : ℝ}
    (hsh : ∀ w : ℂ, w.re < -R → Ψ (w + 1) = F (Ψ w)) {w : ℂ} (k : ℕ)
    (hw : ∀ j : ℕ, j < k → (w + (j : ℂ)).re < -R) :
    Ψ (w + (k : ℂ)) = F^[k] (Ψ w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcast : w + ((k + 1 : ℕ) : ℂ) = (w + (k : ℂ)) + 1 := by push_cast; ring
    rw [hcast, hsh _ (hw k (Nat.lt_succ_self k)),
      ih (fun j hj => hw j (Nat.lt_trans hj (Nat.lt_succ_self k))),
      Function.iterate_succ_apply']

/-- **Repelling Fatou uniqueness, unconditional in the flower.**  If the reference repelling
coordinate `Ψ₁` surjects onto a Stolz petal `Dst P R₂` from the far-left half-plane
`{Re w < -R₁ - 2}` (`hsurj`), then `fl.Ψ` and `Ψ₁` differ by a translation on a far-left
half-plane: `fl.Ψ u = Ψ₁ (u + s)` for `Re u < -N`. -/
theorem rep_unique_backward {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (hτ : P.h c₀ 0 = 1)
    (fl : Work.FatouCoord.ParabolicFlower (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    {R₁ : ℝ} {Ψ₁ : ℂ → ℂ}
    (h₁ : Work.FatouCoord.IsRepellingCoord (Work.PARIMPL.Ft c₀) d.z₁ R₁ Ψ₁)
    (hsurj : ∃ R₂ : ℝ, ∀ z ∈ Work.FlowerGlue2.Dst P R₂,
      ∃ w' : ℂ, w'.re < -R₁ - 2 ∧ Ψ₁ w' = z) :
    ∃ s : ℂ, ∃ N : ℝ, ∀ u : ℂ, u.re < -N → fl.Ψ u = Ψ₁ (u + s) := by
  classical
  obtain ⟨R₂, hR₂⟩ := hsurj
  obtain ⟨R₀, hR₀⟩ := fl.Ψ_inj
  -- ## Step 1: the inverse `Φ` of `Ψ₁` on its half-plane
  have hUopen : IsOpen {w : ℂ | w.re < -R₁} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hΦan : AnalyticOnNhd ℂ (Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁})
      (Ψ₁ '' {w : ℂ | w.re < -R₁}) :=
    Work.ELRig.analyticOnNhd_invFunOn hUopen (h₁.diff.analyticOnNhd hUopen) h₁.inj
  have hΦspec : ∀ z ∈ Dst P R₂,
      Ψ₁ (Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} z) = z ∧
        (Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} z).re < -R₁ - 2 := by
    intro z hz
    obtain ⟨w', hw're, hw'Ψ⟩ := hR₂ z hz
    have hw'U : w' ∈ {w : ℂ | w.re < -R₁} := by
      show w'.re < -R₁
      linarith
    have hex : ∃ a ∈ {w : ℂ | w.re < -R₁}, Ψ₁ a = z := ⟨w', hw'U, hw'Ψ⟩
    have hmem : Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} z ∈ {w : ℂ | w.re < -R₁} :=
      Function.invFunOn_mem hex
    have heq : Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} z = w' :=
      h₁.inj hmem hw'U (by rw [Function.invFunOn_eq hex, hw'Ψ])
    exact ⟨Function.invFunOn_eq hex, by rw [heq]; exact hw're⟩
  -- ## Step 2: compatibility of `Φ` with the shift on the Stolz petal
  have hstep : ∀ z ∈ Dst P R₂, Ft c₀ z ∈ Dst P R₂ →
      Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (Ft c₀ z)
        = Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} z + 1 := by
    intro z hz hFz
    obtain ⟨hzΨ, hzre⟩ := hΦspec z hz
    obtain ⟨hFzΨ, hFzre⟩ := hΦspec (Ft c₀ z) hFz
    have hmemA : Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (Ft c₀ z)
        ∈ {w : ℂ | w.re < -R₁} := by
      show (Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (Ft c₀ z)).re < -R₁
      linarith
    have hmemB : Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} z + 1
        ∈ {w : ℂ | w.re < -R₁} := by
      show (Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} z + 1).re < -R₁
      rw [Complex.add_re, Complex.one_re]
      linarith
    refine h₁.inj hmemA hmemB ?_
    have hshift : Ψ₁ (Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} z + 1) = Ft c₀ z := by
      rw [h₁.shift _ (by linarith), hzΨ]
    rw [hFzΨ, hshift]
  -- ## Step 3: entering the Stolz petal backwards, uniformly
  obtain ⟨N₀, hN₀⟩ := exists_back_entry P hτ fl.Ψ_shift fl.Ψ_small R₂
  let N₁ : ℝ := max N₀ R₀
  have hN₀le : N₀ ≤ N₁ := le_max_left _ _
  have hR₀le : R₀ ≤ N₁ := le_max_right _ _
  -- the predicate "Ψ(u - n) lies in the Stolz petal"
  let p : ℂ → ℕ → Prop := fun u n => fl.Ψ (u - (n : ℂ)) ∈ Dst P R₂
  have hfar : ∀ v : ℂ, v.re < -N₁ → ∀ k : ℕ, (v - (k : ℂ)) ∈ {w : ℂ | w.re < -R₀} := by
    intro v hv k
    have h1 : (v - (k : ℂ)).re = v.re - (k : ℝ) := by
      rw [Complex.sub_re, Complex.natCast_re]
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    show (v - (k : ℂ)).re < -R₀
    linarith
  have hexf : ∀ u : ℂ, u.re < -N₁ → ∃ n : ℕ, p u n :=
    fun u hu => (hN₀ u (by linarith)).1
  let nf : ℂ → ℕ := fun u => if hu : u.re < -N₁ then Nat.find (hexf u hu) else 0
  have hnf_eq : ∀ u (hu : u.re < -N₁), nf u = Nat.find (hexf u hu) := by
    intro u hu
    simp only [nf, dite_eq_left hu]
  have hnf_spec : ∀ u (hu : u.re < -N₁), p u (nf u) := by
    intro u hu
    rw [hnf_eq u hu]
    exact Nat.find_spec (hexf u hu)
  have hnf_min : ∀ u (hu : u.re < -N₁) (m : ℕ), p u m → nf u ≤ m := by
    intro u hu m hm
    rw [hnf_eq u hu]
    exact Nat.find_min' (hexf u hu) hm
  let T : ℂ → ℂ := fun u =>
    Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (fl.Ψ (u - (nf u : ℂ))) + (nf u : ℂ)
  -- upward closure of the entry property
  have hdst : ∀ u : ℂ, u.re < -N₁ → ∀ e : ℕ, p u (nf u + e) := by
    intro u hu e
    induction e with
    | zero => simpa only [Nat.add_zero] using hnf_spec u hu
    | succ e ih =>
      have hup := (hN₀ u (by linarith : u.re < -N₀)).2 (nf u + e) ih
      have hcast : (((nf u + e : ℕ)) : ℂ) + 1 = (((nf u + (e + 1) : ℕ)) : ℂ) := by
        push_cast; ring
      rwa [hcast] at hup
  have hnk : ∀ u : ℂ, u.re < -N₁ → ∀ j : ℕ, nf u ≤ j → p u j := by
    intro u hu j hj
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact hdst u hu e
  -- ## Step 4: `T u = Φ (Ψ (u - m)) + m` for every `m ≥ n u`
  have hkey : ∀ u : ℂ, u.re < -N₁ → ∀ m : ℕ, nf u ≤ m →
      T u = Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (fl.Ψ (u - (m : ℂ))) + (m : ℂ) := by
    intro u hu m hm
    change Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (fl.Ψ (u - (nf u : ℂ))) + (nf u : ℂ)
      = Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (fl.Ψ (u - (m : ℂ))) + (m : ℂ)
    obtain ⟨dd, rfl⟩ := Nat.exists_eq_add_of_le hm
    have hgoal : ∀ dd : ℕ,
        Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (fl.Ψ (u - ((nf u + dd : ℕ) : ℂ)))
            + ((nf u + dd : ℕ) : ℂ)
          = Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (fl.Ψ (u - (nf u : ℂ))) + (nf u : ℂ) := by
      intro dd
      induction dd with
      | zero => simp only [Nat.add_zero]
      | succ dd ih =>
        have hcast : (((nf u + (dd + 1) : ℕ)) : ℂ) = (((nf u + dd : ℕ)) : ℂ) + 1 := by
          push_cast; ring
        have hz₁ : p u (nf u + (dd + 1)) :=
          hnk u hu (nf u + (dd + 1)) (Nat.le_add_right _ _)
        have hz₂ : p u (nf u + dd) :=
          hnk u hu (nf u + dd) (Nat.le_add_right _ _)
        have hFt : Ft c₀ (fl.Ψ (u - (((nf u + (dd + 1) : ℕ)) : ℂ)))
            = fl.Ψ (u - (((nf u + dd : ℕ)) : ℂ)) := by
          have h := fl.Ψ_shift (u - (((nf u + (dd + 1) : ℕ)) : ℂ))
          have hc : u - (((nf u + (dd + 1) : ℕ)) : ℂ) + 1
              = u - (((nf u + dd : ℕ)) : ℂ) := by
            rw [hcast]; ring
          rw [hc] at h
          exact h.symm
        have hst := hstep (fl.Ψ (u - (((nf u + (dd + 1) : ℕ)) : ℂ))) hz₁
          (by rw [hFt]; exact hz₂)
        rw [hFt] at hst
        have heq : Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁}
              (fl.Ψ (u - (((nf u + (dd + 1) : ℕ)) : ℂ)))
            = Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁}
              (fl.Ψ (u - (((nf u + dd : ℕ)) : ℂ))) - 1 := by
          rw [hst]; ring
        rw [heq, hcast]
        linear_combination ih
    exact (hgoal dd).symm
  -- ## Step 5: `T` is holomorphic on the far-left half-plane
  have hT_at : ∀ u : ℂ, u.re < -N₁ → DifferentiableAt ℂ T u := by
    intro u hu
    have hm : p u (nf u) := hnf_spec u hu
    have hz : fl.Ψ (u - (nf u : ℂ)) ∈ Ψ₁ '' {w : ℂ | w.re < -R₁} :=
      ⟨Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (fl.Ψ (u - (nf u : ℂ))),
        by
          show (Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (fl.Ψ (u - (nf u : ℂ)))).re < -R₁
          linarith [(hΦspec _ hm).2],
        (hΦspec _ hm).1⟩
    have hinner : DifferentiableAt ℂ (fun v : ℂ => fl.Ψ (v - (nf u : ℂ))) u :=
      (fl.Ψ_diff (u - (nf u : ℂ))).comp u (differentiableAt_id.sub_const _)
    have houter : DifferentiableAt ℂ (Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁})
        (fl.Ψ (u - (nf u : ℂ))) := (hΦan _ hz).differentiableAt
    have hcomp : DifferentiableAt ℂ
        ((Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁}) ∘
          (fun v : ℂ => fl.Ψ (v - (nf u : ℂ)))) u :=
      houter.comp u hinner
    have hsum : DifferentiableAt ℂ
        (fun v : ℂ =>
          Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (fl.Ψ (v - (nf u : ℂ))) + (nf u : ℂ)) u :=
      hcomp.add_const _
    have hev : T =ᶠ[𝓝 u]
        (fun v : ℂ =>
          Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (fl.Ψ (v - (nf u : ℂ))) + (nf u : ℂ)) := by
      have hopen : IsOpen ({v : ℂ | fl.Ψ (v - (nf u : ℂ)) ∈ Dst P R₂} ∩ {v : ℂ | v.re < -N₁}) :=
        ((isOpen_Dst P R₂).preimage
          (fl.Ψ_diff.continuous.comp (continuous_id.sub continuous_const))).inter
          (isOpen_lt Complex.continuous_re continuous_const)
      have hmem : u ∈ ({v : ℂ | fl.Ψ (v - (nf u : ℂ)) ∈ Dst P R₂} ∩ {v : ℂ | v.re < -N₁}) :=
        ⟨hm, hu⟩
      filter_upwards [hopen.mem_nhds hmem] with v hv
      exact hkey v hv.2 (nf u) (hnf_min v hv.2 (nf u) hv.1)
    exact hsum.congr_of_eventuallyEq hev
  have hT_diff : DifferentiableOn ℂ T {u : ℂ | u.re < -N₁} :=
    fun u hu => (hT_at u hu).differentiableWithinAt
  -- ## Step 6: `T` is injective on the half-plane
  have hT_inj : Set.InjOn T {u : ℂ | u.re < -N₁} := by
    intro u hu u' hu' heq
    have hM1 : nf u ≤ max (nf u) (nf u') := le_max_left _ _
    have hM2 : nf u' ≤ max (nf u) (nf u') := le_max_right _ _
    have h1 := hkey u hu (max (nf u) (nf u')) hM1
    have h2 := hkey u' hu' (max (nf u) (nf u')) hM2
    rw [← heq] at h2
    have h3 : Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁}
          (fl.Ψ (u - ((max (nf u) (nf u') : ℕ) : ℂ)))
        = Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁}
          (fl.Ψ (u' - ((max (nf u) (nf u') : ℕ) : ℂ))) := by
      linear_combination h2 - h1
    have hMu : p u (max (nf u) (nf u')) := hnk u hu _ hM1
    have hMu' : p u' (max (nf u) (nf u')) := hnk u' hu' _ hM2
    have h4 : fl.Ψ (u - ((max (nf u) (nf u') : ℕ) : ℂ))
        = fl.Ψ (u' - ((max (nf u) (nf u') : ℕ) : ℂ)) := by
      rw [← (hΦspec _ hMu).1, ← (hΦspec _ hMu').1, h3]
    exact sub_left_inj.mp (hR₀ (hfar u hu _) (hfar u' hu' _) h4)
  -- ## Step 7: `T` is equivariant
  have hT_per : ∀ u : ℂ, u.re < -(N₁ + 1) → T (u + 1) = T u + 1 := by
    intro u hu
    have hu1 : (u + 1).re < -N₁ := by
      rw [Complex.add_re, Complex.one_re]
      linarith
    have hM1 : nf u ≤ max (nf u) (nf (u + 1)) := le_max_left _ _
    have hM2 : nf (u + 1) ≤ max (nf u) (nf (u + 1)) + 1 := by
      have := le_max_right (nf u) (nf (u + 1))
      omega
    have hu' : u.re < -N₁ := by linarith
    have h1 := hkey u hu' (max (nf u) (nf (u + 1))) hM1
    have h2 := hkey (u + 1) hu1 (max (nf u) (nf (u + 1)) + 1) hM2
    have harg : u + 1 - (((max (nf u) (nf (u + 1)) + 1 : ℕ)) : ℂ)
        = u - ((max (nf u) (nf (u + 1)) : ℕ) : ℂ) := by
      push_cast; ring
    rw [harg] at h2
    rw [h2, h1]
    push_cast
    ring
  -- ## Step 8: cylinder rigidity
  have hT_diff' : DifferentiableOn ℂ T {u : ℂ | u.re < -(N₁ + 1)} :=
    hT_diff.mono (fun u hu => by
      have hu' : u.re < -(N₁ + 1) := hu
      show u.re < -N₁
      linarith)
  have hT_inj' : Set.InjOn T {u : ℂ | u.re < -(N₁ + 1)} :=
    hT_inj.mono (fun u hu => by
      have hu' : u.re < -(N₁ + 1) := hu
      show u.re < -N₁
      linarith)
  obtain ⟨s, hs⟩ := rigid_of_halfPlane (R := N₁ + 1) hT_diff' hT_inj' hT_per
  refine ⟨s, max (N₁ + 1) (R₁ + |s.re| + 1), ?_⟩
  intro u hu
  have huRig : u.re < -(N₁ + 1) := by
    have h1 : N₁ + 1 ≤ max (N₁ + 1) (R₁ + |s.re| + 1) := le_max_left _ _
    linarith
  have huN₁ : u.re < -N₁ := by linarith
  have huRe : u.re + s.re < -R₁ := by
    have h1 : R₁ + |s.re| + 1 ≤ max (N₁ + 1) (R₁ + |s.re| + 1) := le_max_right _ _
    have h2 : s.re ≤ |s.re| := le_abs_self s.re
    linarith
  have hTs : T u = u + s := hs u huRig
  have hkey_u := hkey u huN₁ (nf u) le_rfl
  have hPhi_eq : Function.invFunOn Ψ₁ {w : ℂ | w.re < -R₁} (fl.Ψ (u - (nf u : ℂ)))
      = u + s - (nf u : ℂ) := by
    have h := hkey_u
    rw [hTs] at h
    linear_combination -h
  have hPsi1_eq : Ψ₁ (u + s - (nf u : ℂ)) = fl.Ψ (u - (nf u : ℂ)) := by
    rw [← hPhi_eq]
    exact (hΦspec _ (hnf_spec u huN₁)).1
  have hiter1 : fl.Ψ u = (Ft c₀)^[nf u] (fl.Ψ (u - (nf u : ℂ))) := by
    have h := shift_iter (F := Ft c₀) fl.Ψ_shift (u - (nf u : ℂ)) (nf u)
    have hc : u - (nf u : ℂ) + (nf u : ℂ) = u := by ring
    rwa [hc] at h
  have hiter2 : Ψ₁ (u + s) = (Ft c₀)^[nf u] (Ψ₁ (u + s - (nf u : ℂ))) := by
    have h := shift_iter_of_re (R := R₁) h₁.shift (k := nf u)
      (w := u + s - (nf u : ℂ)) ?_
    · have hc : u + s - (nf u : ℂ) + (nf u : ℂ) = u + s := by ring
      rwa [hc] at h
    · intro j hj
      have hre : (u + s - (nf u : ℂ) + (j : ℂ)).re
          = u.re + s.re - (nf u : ℝ) + (j : ℝ) := by
        simp only [Complex.add_re, Complex.sub_re, Complex.natCast_re]
      rw [hre]
      have hj' : (j : ℝ) ≤ (nf u : ℝ) := by exact_mod_cast le_of_lt hj
      linarith
  rw [hiter2, hPsi1_eq, ← hiter1]

end Work.FlowerGlue2
