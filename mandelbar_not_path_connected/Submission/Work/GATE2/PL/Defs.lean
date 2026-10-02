/-
# PL — the principal Fatou parametrisation of the `c₀`-flower passes through the critical value
-/
import Mathlib
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.GATE2.ExitPath
import Submission.Work.GATE2.PL.continuousOn_invFunOn_of_injOn
import Submission.Work.GATE2.PL.starConvex_slitAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

open Set Function Filter
open Classical
open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- The antiholomorphic involution `w ↦ w̄ + 1/2` of the Écalle cylinder. -/
def sig (w : ℂ) : ℂ := star w + 1 / 2

@[simp] theorem sig_apply (w : ℂ) : sig w = star w + 1 / 2 := rfl

theorem star_half : (star (1 / 2 : ℂ)) = 1 / 2 := by
  norm_num [Complex.ext_iff]

theorem sig_sig (w : ℂ) : sig (sig w) = w + 1 := by
  rw [sig_apply, sig_apply, star_add, star_half, star_star]
  ring

theorem sig_inj : Function.Injective sig := fun a b h => by
  have h' : star a = star b := by
    have hh := congrArg (fun z : ℂ => z - 1 / 2) h
    rw [sig_apply, sig_apply] at hh
    linear_combination hh
  have h2 := congrArg star h'
  rwa [star_star, star_star] at h2

@[simp] theorem sig_re (w : ℂ) : (sig w).re = w.re + 1 / 2 := by
  simp [sig_apply, Complex.add_re]

@[simp] theorem sig_im (w : ℂ) : (sig w).im = -w.im := by
  simp [sig_apply, Complex.add_im]

theorem continuous_sig : Continuous sig := by
  rw [continuous_iff_continuousAt]
  intro w
  exact (continuous_star.continuousAt.add continuousAt_const)

/-- The `k`-th domain: the slit plane `ℂ \ (−∞, v − 1/2]`, intersected with the right half-plane
`{Re w > X − k/2}`. -/
def Dom (v X : ℝ) (k : ℕ) : Set ℂ :=
  slitAt v ∩ {w : ℂ | X - (k : ℝ) / 2 < w.re}

theorem mem_Dom {v X : ℝ} {k : ℕ} {w : ℂ} :
    w ∈ Dom v X k ↔ ¬ (w.im = 0 ∧ w.re ≤ v - 1 / 2) ∧ X - (k : ℝ) / 2 < w.re := Iff.rfl

theorem mem_Dom_slitAt {v X : ℝ} {k : ℕ} {w : ℂ} (hw : w ∈ Dom v X k) : w ∈ slitAt v :=
  (mem_Dom.mp hw).1

theorem mem_Dom_sig {v : ℝ} {w : ℂ} (hw : w ∈ slitAt v) : sig w ∈ slitAt v := by
  rw [slitAt, Set.mem_ofPred_eq] at hw ⊢
  simp only [sig_im, sig_re, neg_eq_zero]
  intro h
  exact hw ⟨h.1, by linarith [h.2]⟩

theorem slitAt_add_one {v : ℝ} {w : ℂ} (hw : w ∈ slitAt v) : w + 1 ∈ slitAt v := by
  rw [slitAt, Set.mem_ofPred_eq] at hw ⊢
  simp only [Complex.add_im, Complex.one_im, add_zero, Complex.add_re, Complex.one_re]
  intro h
  exact hw ⟨h.1, by linarith [h.2]⟩

theorem dom_sig_mem {v X : ℝ} {k : ℕ} {w : ℂ} (hw : w ∈ Dom v X k) : sig w ∈ Dom v X k := by
  obtain ⟨hw1, hw2⟩ := mem_Dom.mp hw
  refine mem_Dom.mpr ⟨mem_Dom_sig hw1, ?_⟩
  simp only [sig_re]
  linarith

theorem dom_add_one_mem {v X : ℝ} {k : ℕ} {w : ℂ} (hw : w ∈ Dom v X k) :
    w + 1 ∈ Dom v X k := by
  obtain ⟨hw1, hw2⟩ := mem_Dom.mp hw
  refine mem_Dom.mpr ⟨slitAt_add_one hw1, ?_⟩
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem dom_add_nat_mem {v X : ℝ} {k : ℕ} {w : ℂ} (hw : w ∈ Dom v X k) (n : ℕ) :
    w + (n : ℂ) ∈ Dom v X k := by
  induction n with
  | zero => simpa using hw
  | succ n ih =>
    have h1 : w + ((n + 1 : ℕ) : ℂ) = (w + (n : ℂ)) + 1 := by push_cast; ring
    rw [h1]
    exact dom_add_one_mem ih

/-- `sig` lowers the level by one: it maps `Dom v X (k+1)` into `Dom v X k`. -/
theorem dom_sig_succ {v X : ℝ} {k : ℕ} {w : ℂ} (hw : w ∈ Dom v X (k + 1)) :
    sig w ∈ Dom v X k := by
  obtain ⟨hw1, hw2⟩ := mem_Dom.mp hw
  refine mem_Dom.mpr ⟨mem_Dom_sig hw1, ?_⟩
  simp only [sig_re]
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hw2
  linarith

theorem dom_mono {v X : ℝ} {j k : ℕ} (hjk : j ≤ k) : Dom v X j ⊆ Dom v X k := by
  intro w hw
  obtain ⟨h1, h2⟩ := mem_Dom.mp hw
  refine mem_Dom.mpr ⟨h1, ?_⟩
  have : ((j : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hjk
  linarith

theorem isOpen_Dom (v X : ℝ) (k : ℕ) : IsOpen (Dom v X k) := by
  have h1 : IsOpen (slitAt v : Set ℂ) := by
    rw [slitAt]
    refine (IsClosed.inter ?_ ?_).isOpen_compl
    · exact isClosed_eq Complex.continuous_im continuous_const
    · exact isClosed_le Complex.continuous_re continuous_const
  exact h1.inter (isOpen_lt continuous_const Complex.continuous_re)

theorem dom_exhaust {v X : ℝ} {w : ℂ} (hw : w ∈ slitAt v) : ∃ k : ℕ, w ∈ Dom v X k := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (X - w.re))
  refine ⟨k, mem_Dom.mpr ⟨hw, ?_⟩⟩
  have hk' : 2 * (X - w.re) < (k : ℝ) := hk
  linarith


/-- `G c = (T_c)^[5]`, the antiholomorphic square root of `Work.EL.F c = (T_c)^[10]`. -/
abbrev G5 (c : ℂ) : ℂ → ℂ := (Tantibar c)^[5]

theorem F_eq_comp_G5 : Work.EL.F c₀ = G5 c₀ ∘ G5 c₀ := by
  rw [Work.EL.F_eq_tantibar]
  funext z
  simp only [G5, Function.comp_apply]
  rw [← Function.iterate_add_apply]

theorem F_iterate_eq (n : ℕ) :
    (Work.EL.F c₀)^[n] = (Tantibar c₀)^[10 * n] := by
  rw [Work.EL.F_eq_tantibar, ← Function.iterate_mul]

theorem T_iterate_F_eq (j n : ℕ) (z : ℂ) :
    (Tantibar c₀)^[j] ((Work.EL.F c₀)^[n] z) = (Tantibar c₀)^[j + 10 * n] z := by
  rw [F_iterate_eq, Function.iterate_add_apply]

section Base

variable (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) (G5 c₀) d.z₁)
variable (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) (G5 c₀) d.z₁ fl.Pa fl.φa)
variable {v X : ℝ}

/-- The base map `ψ₀`: the inverse of the attracting Fatou coordinate on the invariant sub-petal
`Pg`. -/
def baseψ : ℂ → ℂ := Function.invFunOn fl.φa FF.Pg

theorem baseψ_mem (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    {w : ℂ} (hw : X < w.re) :
    baseψ fl FF w ∈ FF.Pg ∧ fl.φa (baseψ fl FF w) = w :=
  Function.invFunOn_pos (hHalf w hw)

theorem baseψ_eq_of_mem (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    {w : ℂ} (hw : X < w.re) {z : ℂ} (hz : z ∈ FF.Pg) (hzφ : fl.φa z = w) :
    baseψ fl FF w = z := by
  obtain ⟨h1, h2⟩ := baseψ_mem fl FF hHalf hw
  exact fl.φa_fatou.2 (FF.Pg_sub h1) (FF.Pg_sub hz) (by rw [h2, hzφ])

theorem baseψ_anti (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    {w : ℂ} (hw : X < w.re) :
    G5 c₀ (baseψ fl FF w) = baseψ fl FF (sig w) := by
  obtain ⟨h1, h2⟩ := baseψ_mem fl FF hHalf hw
  have hsw : X < (sig w).re := by rw [sig_re]; linarith
  refine (baseψ_eq_of_mem fl FF hHalf hsw (FF.mapsTo_G_Pg _ h1) ?_).symm
  rw [fl.φa_fatou.1.2.2 _ (FF.Pg_sub h1), h2]
  rfl

theorem baseψ_shift (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    {w : ℂ} (hw : X < w.re) :
    Work.EL.F c₀ (baseψ fl FF w) = baseψ fl FF (w + 1) := by
  obtain ⟨h1, h2⟩ := baseψ_mem fl FF hHalf hw
  have hw1 : X < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  refine (baseψ_eq_of_mem fl FF hHalf hw1 (FF.mapsTo_F_Pg _ h1) ?_).symm
  rw [FF.shift _ (FF.Pg_sub h1), h2]

/-- The inductive invariant of the half-step lifting: `ψ` intertwines `G5` with `sig` on
`Dom v X k`, is the inverse of `φa` far to the right, and is continuous on `Dom v X k`. -/
structure Good (v : ℝ) (X : ℝ) (k : ℕ) (ψ : ℂ → ℂ) : Prop where
  anti : ∀ w ∈ Dom v X k, G5 c₀ (ψ w) = ψ (sig w)
  far : ∀ w : ℂ, X < w.re → ψ w ∈ FF.Pg ∧ fl.φa (ψ w) = w
  cont : ContinuousOn ψ (Dom v X k)

theorem Good.shift {k : ℕ} {ψ : ℂ → ℂ} (hψ : Good fl FF v X k ψ) :
    ∀ w ∈ Dom v X k, Work.EL.F c₀ (ψ w) = ψ (w + 1) := by
  intro w hw
  have h1 := hψ.anti w hw
  have h2 := hψ.anti (sig w) (dom_sig_mem hw)
  calc Work.EL.F c₀ (ψ w) = G5 c₀ (G5 c₀ (ψ w)) := by rw [F_eq_comp_G5]; rfl
    _ = G5 c₀ (ψ (sig w)) := by rw [h1]
    _ = ψ (sig (sig w)) := h2
    _ = ψ (w + 1) := by rw [sig_sig]

theorem Good.iterate_shift {k : ℕ} {ψ : ℂ → ℂ} (hψ : Good fl FF v X k ψ)
    {w : ℂ} (hw : w ∈ Dom v X k) :
    ∀ n : ℕ, ψ (w + (n : ℂ)) = (Work.EL.F c₀)^[n] (ψ w) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hmem : w + (n : ℂ) ∈ Dom v X k := dom_add_nat_mem hw n
    have h1 : w + ((n + 1 : ℕ) : ℂ) = (w + (n : ℂ)) + 1 := by push_cast; ring
    rw [h1, ← Good.shift fl FF hψ (w + (n : ℂ)) hmem, ih]
    rw [Function.iterate_succ_apply']

theorem baseψ_continuousOn (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w) :
    ContinuousOn (baseψ fl FF) (Dom v X 0) := by
  have hcont : ContinuousOn (baseψ fl FF) (fl.φa '' FF.Pg) :=
    continuousOn_invFunOn_of_injOn FF.isOpen_Pg
      (fl.φa_fatou.1.2.1.mono FF.Pg_sub) (fl.φa_fatou.2.mono FF.Pg_sub)
  refine hcont.mono ?_
  intro w hw
  obtain ⟨hw1, hw2⟩ := mem_Dom.mp hw
  exact ⟨baseψ fl FF w, (baseψ_mem fl FF hHalf (by simpa using hw2)).1,
    (baseψ_mem fl FF hHalf (by simpa using hw2)).2⟩

/-- The base point `X + 1` of the induction lies in every `Dom v X k`. -/
theorem mem_Dom_starP (hX : v - 1 / 2 ≤ X) (k : ℕ) :
    ((X + 1 : ℝ) : ℂ) ∈ Dom v X k := by
  refine mem_Dom.mpr ⟨?_, ?_⟩
  · rintro ⟨h1, h2⟩
    simp only [Complex.ofReal_re] at h2
    linarith
  · simp only [Complex.ofReal_re]
    have : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
    linarith

theorem starConvex_Dom (hX : v - 1 / 2 ≤ X) (k : ℕ) :
    StarConvex ℝ ((X + 1 : ℝ) : ℂ) (Dom v X k) := by
  have hp : v - 1 / 2 < X + 1 := by linarith
  have ha : X - (k : ℝ) / 2 < X + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
    linarith
  have h := starConvex_slitAt v (X + 1) (X - (k : ℝ) / 2) hp ha
  simpa only [Dom, slitAt] using h

theorem nonempty_Dom (hX : v - 1 / 2 ≤ X) (k : ℕ) : (Dom v X k).Nonempty :=
  ⟨_, mem_Dom_starP hX k⟩

theorem contractibleSpace_Dom (hX : v - 1 / 2 ≤ X) (k : ℕ) :
    ContractibleSpace ↥(Dom v X k) :=
  (starConvex_Dom hX k).contractibleSpace (nonempty_Dom hX k)

theorem good_base (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w) :
    Good fl FF v X 0 (baseψ fl FF) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    have hw' : X < w.re := by
      obtain ⟨-, h⟩ := mem_Dom.mp hw
      simpa using h
    have hsw : X < (sig w).re := by rw [sig_re]; linarith
    exact baseψ_anti fl FF hHalf hw'
  · intro w hw
    exact baseψ_mem fl FF hHalf hw
  · exact baseψ_continuousOn fl FF hHalf

end Base

end

end Work.GATE2.PL
