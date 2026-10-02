/-
# ELRig — `exists_analytic_rayCylLift`: a `RayCylLift` whose first lift is real-analytic

`Submission/Work/ELRig/exists_rayCylLift.lean` produces a `RayCylLift d fl` (the two
`1`-periodic lifts of the root rays in the repelling coordinate `Ψ`, with `TailId`), but its
fields record only that `γ₁` is *continuous*: they are satisfied by every reparametrisation
`γ₁ ∘ σ` of the lift by a continuous strictly increasing `σ` with `σ (s+1) = σ s + 1`, so
analyticity of the witness of `exists_rayCylLift` is *not* provable from its fields.

The content of this file is that the lift can nevertheless be reparametrised so that it becomes
real-analytic on each period.  This is the "regularity" input of the crossing-parity route of
`Submission/Work/ELRig/NOTES.md` §6/§9, consumed by `Work.ELRig.odd_transversal_level`.

## The construction

Fix a `RayCylLift` `L` (from `exists_rayCylLift`) and let `τ₀ s = 2 ^ (1024 ^ s)` be the
analytic level map of `Work.ELRig.levelParam_spec`.  Since `range L.τ = (1, ∞)`
(`rayCylLift_range_tau`, from the fields of `RayCylLift` plus `exists_preimage_rayTail`), there
is a unique `σ : ℝ → ℝ` with `L.τ (σ s) = τ₀ s`; it is strictly increasing and surjective
(hence continuous), and `σ (s+1) = σ s + 1`.  Reparametrising,

  `L' := (L.γ₁ ∘ σ, L.γ₂ ∘ σ, τ₀, L.R)`

is again a `RayCylLift` (all fields transfer: the range of `γ₁`, and with it `TailId₁`, is
unchanged by the surjective `σ`).

For the analyticity, note that in the far-left half plane `{Re < -R}` (`R := L.R + 1`) the lift
is *pinned* to the inverse branch of `Ψ` (`rayCylLift_far_left_pin`):

  `L.γ₁ u = g (rayPt α₁ (L.τ u))` for `u ≤ sstar`,  `g := invFunOn fl.Ψ {Re < -R}`,

because `Ψ` is injective there (`RayCylLift.hinj`); and `(L.γ₁ u).re - u` is `1`-periodic and
continuous, hence bounded (`rayCylLift_re_sub_le`).  For `s ∈ (n, n+1)` choose an integer
`m ≥ max (0) ⌈σ (n+1) - sstar⌉` and use the periodicity of `L.γ₁` and of `σ`:

  `L.γ₁ (σ s) = L.γ₁ (σ s - m) + m = g (rayPt α₁ (τ₀ (s - m))) + m`  on `(n, n+1)`,

which is real-analytic on the interval: `τ₀` is analytic (`levelParam_analyticOn`, via the
complex extension `z ↦ exp (log 2 · exp (z log 1024))`), `t ↦ rayPt α₁ t` is analytic on
`(1, ∞)` (`analyticOn_rayPt_of_analytic`, from the analyticity of the Böttcher coordinate
`analyticOnNhd_dynBottcher` — the `c ∈ Mandelbar` hypothesis of the library version is unused),
and `g` is analytic on the image of the half plane (`analyticOnNhd_invFunOn`).
-/
import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.exists_liftCurvesV3
import Submission.Work.ELRig.exists_rayCylLift
import Submission.Work.ELRig.analyticOnNhd_dynBottcher
import Submission.Work.ELRig.analyticOnNhd_invFunOn
import Submission.Work.ELRig.analyticOn_rayPt_of_analytic
import Submission.Work.ELRig.rayCylLift_range_tau
import Submission.Work.ELRig.rayCylLift_far_left_pin
import Submission.Work.Bottcher.All
import Submission.Work.ParamRaysCrit.PublicAPI

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar)

/-- The complex-analytic extension of the level map `s ↦ 2 ^ (1024 ^ s)`. -/
private def lev (z : ℂ) : ℂ :=
  Complex.exp ((Real.log 2 : ℂ) * Complex.exp (z * (Real.log 1024 : ℂ)))

private theorem lev_an (z : ℂ) : AnalyticAt ℂ lev z := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => z * (Real.log 1024 : ℂ)) z :=
    analyticAt_id.mul analyticAt_const
  have h2 : AnalyticAt ℂ (fun z : ℂ => Complex.exp (z * (Real.log 1024 : ℂ))) z := h1.cexp
  have h3 : AnalyticAt ℂ
      (fun z : ℂ => (Real.log 2 : ℂ) * Complex.exp (z * (Real.log 1024 : ℂ))) z :=
    analyticAt_const.mul h2
  exact h3.cexp

private theorem lev_eq_real (s : ℝ) :
    lev (s : ℂ) = (((2 : ℝ) ^ ((1024 : ℝ) ^ s) : ℝ) : ℂ) := by
  have h1024 : (((1024 : ℝ) ^ s : ℝ) : ℂ) =
      Complex.exp ((s : ℂ) * (Real.log 1024 : ℂ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1024), Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [lev, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Complex.ofReal_exp]
  congr 1
  push_cast
  rw [h1024]

private theorem lev_re_analyticOn : AnalyticOn ℝ (fun s : ℝ => (lev (s : ℂ)).re) Set.univ := by
  intro s _
  have h : AnalyticAt ℝ (fun s : ℝ => lev (s : ℂ)) s :=
    ((lev_an (s : ℂ)).restrictScalars).comp (Complex.ofRealCLM.analyticAt s)
  have h2 : AnalyticAt ℝ (fun s : ℝ => (lev (s : ℂ)).re) s :=
    AnalyticAt.comp (g := Complex.reCLM) (f := fun s : ℝ => lev (s : ℂ))
      (Complex.reCLM.analyticAt _) h
  simpa [Function.comp_def] using h2

/-- The level map `s ↦ 2 ^ (1024 ^ s)` is real-analytic. -/
theorem levelParam_analyticOn :
    AnalyticOn ℝ (fun s : ℝ => (2 : ℝ) ^ ((1024 : ℝ) ^ s)) Set.univ :=
  lev_re_analyticOn.congr (fun s _ => by
    show (2 : ℝ) ^ ((1024 : ℝ) ^ s) = (lev (s : ℂ)).re
    rw [lev_eq_real s, Complex.ofReal_re])

/-- The real part of the first lift of a `RayCylLift` grows at most linearly. -/
theorem rayCylLift_re_sub_le {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : RayCylLift d fl) : ∃ M : ℝ, ∀ s : ℝ, (L.γ₁ s).re - s ≤ M := by
  have hper : Function.Periodic (fun s : ℝ => (L.γ₁ s).re - s) 1 := by
    intro s
    show (L.γ₁ (s + 1)).re - (s + 1) = (L.γ₁ s).re - s
    rw [L.per₁ s, Complex.add_re, Complex.one_re]
    ring
  have hcont : Continuous (fun s : ℝ => (L.γ₁ s).re - s) :=
    (Complex.continuous_re.comp L.cont₁).sub continuous_id
  have hb := hper.isBounded_of_continuous (by norm_num : (1 : ℝ) ≠ 0) hcont
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp hb
  refine ⟨C + |(L.γ₁ 0).re|, fun s => ?_⟩
  have h0 : dist ((L.γ₁ s).re - s) ((L.γ₁ 0).re - 0) ≤ C := hC s 0
  rw [Real.dist_eq, sub_zero] at h0
  have h1 : |(L.γ₁ s).re - s| ≤ C + |(L.γ₁ 0).re| := by
    calc |(L.γ₁ s).re - s| = |((L.γ₁ s).re - s - (L.γ₁ 0).re) + (L.γ₁ 0).re| := by ring_nf
      _ ≤ |(L.γ₁ s).re - s - (L.γ₁ 0).re| + |(L.γ₁ 0).re| := abs_add_le _ _
      _ ≤ C + |(L.γ₁ 0).re| := by linarith
  linarith [le_abs_self ((L.γ₁ s).re - s)]


theorem exists_analytic_rayCylLift {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (h₁ : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁) (h₂ : Work.EL.LandsN d.hN Work.EL.alpha2 d.z₁) :
    ∃ L : Work.ELRig.RayCylLift d fl,
      ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => L.γ₁ s) (Set.Ioo (n : ℝ) ((n : ℝ) + 1)) := by
  classical
  obtain ⟨L⟩ := exists_rayCylLift d fl h₁ h₂
  set R : ℝ := L.R + 1 with hRdef
  have hLR : L.R ≤ R := by rw [hRdef]; linarith
  obtain ⟨-, hτ₀mono, hτ₀1, -, -, hτ₀step, -, -, hτ₀surj⟩ :=
    levelParam_spec (t₀ := (2 : ℝ)) (by norm_num)
  have hrange : Set.range L.τ = Set.Ioi 1 := rayCylLift_range_tau d fl L h₁
  have hτstep : ∀ s : ℝ, L.τ (s + 1) = (L.τ s) ^ (1024 : ℕ) := by
    intro s
    refine rayPt_level_inj d.hN (θ := Work.EL.alpha1) (L.hτ1 (s + 1))
      (one_lt_pow₀ (L.hτ1 s) (by norm_num)) ?_
    rw [← L.hΨ₁ (s + 1), L.per₁ s, fl.Ψ_shift (L.γ₁ s), L.hΨ₁ s,
      rayPt_F_alpha1 d (L.hτ1 s)]
  let σ : ℝ → ℝ := fun s =>
    Classical.choose (Set.mem_range.mp (by rw [hrange]; exact hτ₀1 s))
  have hσspec : ∀ s : ℝ, L.τ (σ s) = (2 : ℝ) ^ ((1024 : ℝ) ^ s) := fun s =>
    Classical.choose_spec (Set.mem_range.mp (by rw [hrange]; exact hτ₀1 s))
  have hσmono : StrictMono σ := by
    intro a b hab
    have h : L.τ (σ a) < L.τ (σ b) := by
      rw [hσspec a, hσspec b]
      exact hτ₀mono hab
    exact (L.hτmono.lt_iff_lt).mp h
  have hσsurj : Function.Surjective σ := by
    intro u
    have hmem : L.τ u ∈ Set.range L.τ := ⟨u, rfl⟩
    rw [hrange] at hmem
    obtain ⟨s, hs⟩ := hτ₀surj (L.τ u) hmem
    exact ⟨s, L.hτmono.injective (by rw [hσspec s, hs])⟩
  have hσcont : Continuous σ :=
    (StrictMono.orderIsoOfSurjective σ hσmono hσsurj).continuous
  have hσs1 : ∀ s : ℝ, σ (s + 1) = σ s + 1 := by
    intro s
    have h : L.τ (σ (s + 1)) = L.τ (σ s + 1) := by
      rw [hσspec (s + 1), hτ₀step s, ← hσspec s, ← hτstep (σ s)]
    exact L.hτmono.injective h
  have hσadd : ∀ (s : ℝ) (k : ℕ), σ (s + (k : ℝ)) = σ s + (k : ℝ) := by
    intro s k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : s + ((k + 1 : ℕ) : ℝ) = (s + (k : ℝ)) + 1 := by push_cast; ring
      rw [h1, hσs1, ih]
      push_cast
      ring
  have hγadd : ∀ (u : ℝ) (k : ℕ), L.γ₁ (u + (k : ℝ)) = L.γ₁ u + (k : ℂ) := by
    intro u k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : u + ((k + 1 : ℕ) : ℝ) = (u + (k : ℝ)) + 1 := by push_cast; ring
      rw [h1, L.per₁, ih]
      push_cast
      ring
  obtain ⟨sstar₀, hpin₀⟩ := rayCylLift_far_left_pin d fl L hLR
  obtain ⟨M, hM⟩ := rayCylLift_re_sub_le L
  set sstar : ℝ := min sstar₀ (-R - M - 1) with hsstardef
  have hsstar_le : sstar ≤ sstar₀ := min_le_left _ _
  have hfar : ∀ u : ℝ, u ≤ sstar → (L.γ₁ u).re < -R := by
    intro u hu
    have h1 : u ≤ -R - M - 1 := le_trans hu (min_le_right _ _)
    have h2 := hM u
    linarith
  have hpin : ∀ u : ℝ, u ≤ sstar → L.γ₁ u =
      Function.invFunOn fl.Ψ {w : ℂ | w.re < -R}
        (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u)) :=
    fun u hu => hpin₀ u (le_trans hu hsstar_le)
  have hHopen : IsOpen {w : ℂ | w.re < -R} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hHinj : Set.InjOn fl.Ψ {w : ℂ | w.re < -R} :=
    L.hinj.mono (fun w hw => by
      simp only [Set.mem_setOf_eq] at hw ⊢
      rw [hRdef] at hw
      linarith)
  have hΨan : AnalyticOnNhd ℂ fl.Ψ {w : ℂ | w.re < -R} :=
    (fl.Ψ_diff.differentiableOn).analyticOnNhd hHopen
  have hgan : AnalyticOnNhd ℂ (Function.invFunOn fl.Ψ {w : ℂ | w.re < -R})
      (fl.Ψ '' {w : ℂ | w.re < -R}) := analyticOnNhd_invFunOn hHopen hΨan hHinj
  have hrayan : AnalyticOn ℝ (fun t : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1 t)
      (Set.Ioi 1) := analyticOn_rayPt_of_analytic d.hN (analyticOnNhd_dynBottcher d.bottcher) Work.EL.alpha1
  refine ⟨{ γ₁ := fun s => L.γ₁ (σ s)
            γ₂ := fun s => L.γ₂ (σ s)
            τ := fun s => (2 : ℝ) ^ ((1024 : ℝ) ^ s)
            R := L.R
            hτmono := hτ₀mono
            hτ1 := hτ₀1
            hΨ₁ := fun s => by rw [L.hΨ₁ (σ s), hσspec s]
            cont₁ := L.cont₁.comp hσcont
            cont₂ := L.cont₂.comp hσcont
            per₁ := fun s => by rw [hσs1 s, L.per₁ (σ s)]
            per₂ := fun s => by rw [hσs1 s, L.per₂ (σ s)]
            anti := fun s => L.anti (σ s)
            tailId₁ := fun w hw hmem => by
              obtain ⟨u, hu⟩ := L.tailId₁ w hw hmem
              obtain ⟨s, hs⟩ := hσsurj u
              exact ⟨s, by show L.γ₁ (σ s) = w; rw [hs]; exact hu⟩
            tailId₂ := fun w hw hmem => by
              obtain ⟨u, hu⟩ := L.tailId₂ w hw hmem
              obtain ⟨s, hs⟩ := hσsurj u
              exact ⟨s, by show L.γ₂ (σ s) = w; rw [hs]; exact hu⟩
            hzne := L.hzne
            hγtail := L.hγtail
            hinj := L.hinj }, ?_⟩
  intro n
  set m : ℤ := max 0 ⌈σ ((n : ℝ) + 1) - sstar⌉ with hmdef
  have hm0 : 0 ≤ m := le_max_left _ _
  have hmge : σ ((n : ℝ) + 1) - sstar ≤ (m : ℝ) := by
    have h1 : ⌈σ ((n : ℝ) + 1) - sstar⌉ ≤ m := le_max_right _ _
    have h2 : σ ((n : ℝ) + 1) - sstar ≤
        ((⌈σ ((n : ℝ) + 1) - sstar⌉ : ℤ) : ℝ) := Int.le_ceil _
    have h3 : ((⌈σ ((n : ℝ) + 1) - sstar⌉ : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    linarith
  have hmR : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    have h := Int.toNat_of_nonneg hm0
    exact_mod_cast h
  have hmZ : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by
    have h := Int.toNat_of_nonneg hm0
    exact_mod_cast h
  have hval : ∀ s ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 1),
      L.γ₁ (σ s) = Function.invFunOn fl.Ψ {w : ℂ | w.re < -R}
        (Work.EL.rayPt d.hN Work.EL.alpha1 ((2 : ℝ) ^ ((1024 : ℝ) ^ (s - (m : ℝ)))))
        + (m : ℂ) := by
    intro s hs
    have hsm : σ s - (m : ℝ) ≤ sstar := by
      have h1 : σ s ≤ σ ((n : ℝ) + 1) := hσmono.monotone (le_of_lt hs.2)
      linarith
    have hσeq : σ s - (m : ℝ) = σ (s - (m : ℝ)) := by
      have h := hσadd (s - (m : ℝ)) m.toNat
      rw [hmR, sub_add_cancel] at h
      rw [h]
      ring
    have hγ : L.γ₁ (σ s) = L.γ₁ (σ s - (m : ℝ)) + (m : ℂ) := by
      have h := hγadd (σ s - (m : ℝ)) m.toNat
      rw [hmZ, hmR, sub_add_cancel] at h
      exact h
    have hτeq : L.τ (σ s - (m : ℝ)) = (2 : ℝ) ^ ((1024 : ℝ) ^ (s - (m : ℝ))) := by
      rw [hσeq, hσspec (s - (m : ℝ))]
    rw [hγ, hpin (σ s - (m : ℝ)) hsm, hτeq]
  have hAnal : AnalyticOn ℝ (fun s : ℝ => Function.invFunOn fl.Ψ {w : ℂ | w.re < -R}
      (Work.EL.rayPt d.hN Work.EL.alpha1 ((2 : ℝ) ^ ((1024 : ℝ) ^ (s - (m : ℝ)))))
      + (m : ℂ)) (Set.Ioo (n : ℝ) ((n : ℝ) + 1)) := by
    intro s hs
    have hlev1 : 1 < (2 : ℝ) ^ ((1024 : ℝ) ^ (s - (m : ℝ))) := hτ₀1 (s - (m : ℝ))
    have hlevel : AnalyticAt ℝ (fun t : ℝ => (2 : ℝ) ^ ((1024 : ℝ) ^ t)) (s - (m : ℝ)) :=
      levelParam_analyticOn.analyticAt (z := s - (m : ℝ)) Filter.univ_mem
    have hsub : AnalyticAt ℝ (fun s : ℝ => s - (m : ℝ)) s :=
      (analyticAt_id : AnalyticAt ℝ (fun s : ℝ => s) s).sub
        (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (m : ℝ)) s)
    have hlevan : AnalyticAt ℝ (fun s : ℝ => (2 : ℝ) ^ ((1024 : ℝ) ^ (s - (m : ℝ)))) s :=
      AnalyticAt.comp (g := fun t : ℝ => (2 : ℝ) ^ ((1024 : ℝ) ^ t))
        (f := fun s : ℝ => s - (m : ℝ)) hlevel hsub
    have hray_at : AnalyticAt ℝ (fun t : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1 t)
        ((2 : ℝ) ^ ((1024 : ℝ) ^ (s - (m : ℝ)))) :=
      hrayan.analyticAt (Ioi_mem_nhds hlev1)
    have hcomp : AnalyticAt ℝ (fun s : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1
        ((2 : ℝ) ^ ((1024 : ℝ) ^ (s - (m : ℝ))))) s :=
      AnalyticAt.comp (g := fun t : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1 t)
        (f := fun s : ℝ => (2 : ℝ) ^ ((1024 : ℝ) ^ (s - (m : ℝ)))) hray_at hlevan
    have hsm : σ s - (m : ℝ) ≤ sstar := by
      have h1 : σ s ≤ σ ((n : ℝ) + 1) := hσmono.monotone (le_of_lt hs.2)
      linarith
    have hσeq : σ s - (m : ℝ) = σ (s - (m : ℝ)) := by
      have h := hσadd (s - (m : ℝ)) m.toNat
      rw [hmR, sub_add_cancel] at h
      rw [h]
      ring
    have hmemH : Work.EL.rayPt d.hN Work.EL.alpha1
        ((2 : ℝ) ^ ((1024 : ℝ) ^ (s - (m : ℝ)))) ∈ fl.Ψ '' {w : ℂ | w.re < -R} := by
      refine ⟨L.γ₁ (σ s - (m : ℝ)), hfar _ hsm, ?_⟩
      rw [L.hΨ₁, hσeq, hσspec (s - (m : ℝ))]
    have hgan_at : AnalyticAt ℝ (Function.invFunOn fl.Ψ {w : ℂ | w.re < -R})
        (Work.EL.rayPt d.hN Work.EL.alpha1
          ((2 : ℝ) ^ ((1024 : ℝ) ^ (s - (m : ℝ))))) :=
      (hgan _ hmemH).restrictScalars
    have hfinal : AnalyticAt ℝ (fun s : ℝ => Function.invFunOn fl.Ψ {w : ℂ | w.re < -R}
        (Work.EL.rayPt d.hN Work.EL.alpha1 ((2 : ℝ) ^ ((1024 : ℝ) ^ (s - (m : ℝ)))))
        + (m : ℂ)) s :=
      (AnalyticAt.comp
        (g := Function.invFunOn fl.Ψ {w : ℂ | w.re < -R})
        (f := fun s : ℝ => Work.EL.rayPt d.hN Work.EL.alpha1
          ((2 : ℝ) ^ ((1024 : ℝ) ^ (s - (m : ℝ))))) hgan_at hcomp).add
        (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (m : ℂ)) s)
    exact hfinal.analyticWithinAt
  exact hAnal.congr (fun s hs => hval s hs)

end Work.ELRig
