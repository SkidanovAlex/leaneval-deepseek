/-
# `PL/Urec` — the cut-free recursion and the global extension `PsiU`

Under the assumption `hne : Ψs v ≠ c₀` (i.e. the concrete parametrisation does *not* pass through
the critical value at the level `v`), the half-step lifts of `Work.GATE2.PL.UCore` can be iterated
over the cut-free domains `U X k = {Re w > X − k/2}`, because the only point at which the base map
could meet a critical value is `z = v − 1/2`, and there `ψ (sig z) = ψ v = Ψs v ≠ c₀` by the
uniqueness of the slit-plane lift (`Work.GATE2.PL.Good_eq`).

The result is a function `PsiU` on all of `ℂ` which intertwines `G5` with `sig` and `F` with the
unit shift, is continuous, is the inverse of the Fatou coordinate far to the right, and is bounded
(its values lie in the filled Julia set `K c₀`).  `eq_c0_of_good` then finishes by Liouville.
-/
import Mathlib
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.GATE2.ExitPath
import Submission.Work.GATE2.PL.Defs
import Submission.Work.GATE2.PL.Main
import Submission.Work.GATE2.PL.UCore
import Submission.Work.GATE2.PL.Uavoid
import Submission.Work.GATE2.PL.Good_eq
import Submission.Work.GATE2.PL.isCoveringMapOn_tantibar_five

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

variable (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) (G5 c₀) d.z₁)
variable (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) (G5 c₀) d.z₁ fl.Pa fl.φa)
variable {v X : ℝ} {Ψs : ℂ → ℂ}

/-- **The seed of the cut-free recursion**: the data of the given slit-plane parametrisation `Ψs`
together with the *negation* `hne` of the conclusion of `eq_c0_of_good`.  Under `hne` the
recursion of `PsiU` runs at every level. -/
structure Seed (v X : ℝ) (Ψs : ℂ → ℂ) : Prop where
  hX : v - 1 / 2 ≤ X
  hanti : ∀ w : ℂ, w ∈ slitAt v → G5 c₀ (Ψs w) = Ψs (sig w)
  hfar : ∀ w : ℂ, X < w.re → Ψs w ∈ FF.Pg ∧ fl.φa (Ψs w) = w
  hcont : ContinuousOn Ψs (slitAt v)
  hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
    fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ)
  hne : Ψs (v : ℂ) ≠ c₀

/-! ## From `GoodU` to `Good`, and the seed at level `0` -/

/-- `GoodU` at level `k` implies `Good` at level `k` (the slit condition is a restriction). -/
theorem Good_of_GoodU {v X : ℝ} {k : ℕ} {ψ : ℂ → ℂ} (h : GoodU fl FF v X k ψ) :
    Good fl FF v X k ψ :=
  ⟨fun w hw => h.anti w (mem_Dom.mp hw).2, h.far,
    h.cont.mono (fun w hw => (mem_Dom.mp hw).2)⟩

/-- `U X 0 = {Re > X}` is contained in the slit plane when `v − 1/2 ≤ X`. -/
theorem U_zero_subset_slitAt {v X : ℝ} (hX : v - 1 / 2 ≤ X) : U X 0 ⊆ slitAt v := by
  intro w hw
  rw [mem_U] at hw
  simp only [Nat.cast_zero, zero_div, sub_zero] at hw
  rw [slitAt, Set.mem_ofPred_eq]
  rintro ⟨him, hle⟩
  linarith

/-- `Ψs` seen as a half-step lift on `U X 0 = {Re > X}`. -/
theorem goodU_PsiS (S : Seed fl FF v X Ψs) : GoodU fl FF v X 0 Ψs where
  anti := fun w hw => S.hanti w (U_zero_subset_slitAt (v := v) (X := X) S.hX hw)
  far := S.hfar
  cont := S.hcont.mono (U_zero_subset_slitAt (v := v) (X := X) S.hX)

/-- `Ψs` seen as a `Good` function on every slit level. -/
theorem good_PsiS (S : Seed fl FF v X Ψs) (k : ℕ) : Good fl FF v X k Ψs :=
  ⟨fun w hw => S.hanti w (mem_Dom_slitAt hw), S.hfar,
    S.hcont.mono (fun w hw => mem_Dom_slitAt hw)⟩

/-- The seed of the recursion: `Ψs` avoids the critical values on `U X 0`. -/
theorem goodU2_base (S : Seed fl FF v X Ψs) : GoodU2 fl FF v X 0 Ψs :=
  ⟨goodU_PsiS fl FF S,
    notMem_critVals_U fl FF (goodU_PsiS fl FF S).anti S.hfar S.hv
      (fun _ => S.hne)⟩

/-! ## The recursive step -/

/-- **One cut-free half-step.**  From a lift on `U X k` avoiding the critical values we obtain a
lift on `U X (k+1)`, still avoiding them — the latter because the only point at which the base map
`z ↦ ψ (sig z)` can take the value `c₀` is `z = v − 1/2`, and there `ψ (sig z) = ψ v = Ψs v ≠ c₀`
by `Good_eq`. -/
theorem exists_stepU2 (S : Seed fl FF v X Ψs) {k : ℕ} {ψ : ℂ → ℂ}
    (hψ : GoodU2 fl FF v X k ψ) :
    ∃ ψ' : ℂ → ℂ, GoodU2 fl FF v X (k + 1) ψ' ∧ ∀ w ∈ U X k, ψ' w = ψ w := by
  have havoid : ∀ z : ℂ, z ∈ U X (k + 1) → ψ (sig z) ∉ critVals (c₀ := c₀) :=
    fun z hz => hψ.avoid (sig z) (sig_mem_U_succ hz)
  obtain ⟨ψ', hψ'good, hψ'agree⟩ := exists_stepU fl FF hψ.good havoid
  refine ⟨ψ', ⟨hψ'good, ?_⟩, hψ'agree⟩
  -- the base map of the *next* lift avoids the critical values on the slit part ...
  have havoidDom : ∀ z : ℂ, z ∈ Dom v X (k + 1) → ψ' (sig z) ∉ critVals (c₀ := c₀) := by
    intro z hz
    have hzU : z ∈ U X (k + 1) := (mem_Dom.mp hz).2
    have hsigU : sig z ∈ U X k := sig_mem_U_succ hzU
    rw [hψ'agree (sig z) hsigU]
    exact hψ.avoid (sig z) hsigU
  -- ... hence `ψ'` agrees with `Ψs` on the slit domain (uniqueness of the lift)
  have hdom : ∀ u ∈ Dom v X (k + 1), ψ' u = Ψs u :=
    Good_eq (fl := fl) (FF := FF) S.hX (Good_of_GoodU fl FF hψ'good)
      (good_PsiS fl FF S (k + 1)) havoidDom
  -- so `ψ' v = Ψs v ≠ c₀`, and every lift on `U X (k+1)` avoids the critical values
  refine notMem_critVals_U fl FF hψ'good.anti hψ'good.far S.hv ?_ 
  intro hvU
  have hmem : (v : ℂ) ∈ Dom v X (k + 1) := by
    refine mem_Dom.mpr ⟨?_, ?_⟩
    · rintro ⟨him, hle⟩
      simp only [Complex.ofReal_im] at him
      simp only [Complex.ofReal_re] at hle
      linarith
    · simpa [mem_U] using hvU
  rw [hdom (v : ℂ) hmem]
  exact S.hne

/-! ## The recursion, the glued function `PsiU` and its properties -/

/-- The recursively constructed sequence of cut-free lifts. -/
noncomputable def seqU2 (S : Seed fl FF v X Ψs) :
    (k : ℕ) → {ψ : ℂ → ℂ // GoodU2 fl FF v X k ψ}
  | 0 => ⟨Ψs, goodU2_base fl FF S⟩
  | k + 1 => ⟨Classical.choose (exists_stepU2 fl FF S (seqU2 S k).2),
      (Classical.choose_spec (exists_stepU2 fl FF S (seqU2 S k).2)).1⟩

theorem seqU2_agree_succ (S : Seed fl FF v X Ψs) (k : ℕ) :
    ∀ w ∈ U X k, (seqU2 fl FF S (k + 1)).1 w = (seqU2 fl FF S k).1 w :=
  (Classical.choose_spec (exists_stepU2 fl FF S (seqU2 fl FF S k).2)).2

theorem seqU2_agree (S : Seed fl FF v X Ψs) {j k : ℕ} (hjk : j ≤ k) :
    ∀ w ∈ U X j, (seqU2 fl FF S k).1 w = (seqU2 fl FF S j).1 w := by
  induction k with
  | zero =>
    obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hjk
    intro w _
    rfl
  | succ k ih =>
    intro w hw
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · have hjk' : j ≤ k := Nat.lt_succ_iff.mp h
      rw [seqU2_agree_succ fl FF S k w (U_mono hjk' hw), ih hjk' w hw]
    · have hje : j = k + 1 := le_antisymm hjk h
      subst hje
      rfl

/-- **The global extension of `Ψs`** obtained by gluing the cut-free lifts at the level of `w`. -/
noncomputable def PsiU (S : Seed fl FF v X Ψs) : ℂ → ℂ :=
  fun w => (seqU2 fl FF S (lvl X w)).1 w

theorem PsiU_eq (S : Seed fl FF v X Ψs) {k : ℕ} {w : ℂ} (hw : w ∈ U X k) :
    PsiU fl FF S w = (seqU2 fl FF S k).1 w :=
  (seqU2_agree fl FF S (lvl_le (mem_U.mp hw)) w mem_U_lvl).symm

/-- `PsiU` intertwines `G5 c₀` with `sig`. -/
theorem PsiU_anti (S : Seed fl FF v X Ψs) (w : ℂ) :
    G5 c₀ (PsiU fl FF S w) = PsiU fl FF S (sig w) := by
  have h1 : w ∈ U X (lvl X w) := mem_U_lvl
  have h2 : sig w ∈ U X (lvl X w) := sig_mem_U h1
  rw [PsiU_eq fl FF S h1, PsiU_eq fl FF S h2]
  exact (seqU2 fl FF S (lvl X w)).2.good.anti w h1

/-- `PsiU` intertwines `F c₀` with the unit shift. -/
theorem PsiU_shift (S : Seed fl FF v X Ψs) (w : ℂ) :
    Work.EL.F c₀ (PsiU fl FF S w) = PsiU fl FF S (w + 1) := by
  calc Work.EL.F c₀ (PsiU fl FF S w) = G5 c₀ (G5 c₀ (PsiU fl FF S w)) := by
        rw [F_eq_comp_G5]; rfl
    _ = G5 c₀ (PsiU fl FF S (sig w)) := by rw [PsiU_anti fl FF S w]
    _ = PsiU fl FF S (sig (sig w)) := PsiU_anti fl FF S (sig w)
    _ = PsiU fl FF S (w + 1) := by rw [sig_sig]

theorem PsiU_iterate_shift (S : Seed fl FF v X Ψs) (w : ℂ) :
    ∀ n : ℕ, PsiU fl FF S (w + (n : ℂ)) = (Work.EL.F c₀)^[n] (PsiU fl FF S w) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : w + ((n + 1 : ℕ) : ℂ) = (w + (n : ℂ)) + 1 := by push_cast; ring
    rw [h1, ← PsiU_shift fl FF S (w + (n : ℂ)), ih]
    rw [Function.iterate_succ_apply']

/-- `PsiU` is continuous on all of `ℂ`. -/
theorem PsiU_cont (S : Seed fl FF v X Ψs) : Continuous (PsiU fl FF S) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx : x ∈ U X (lvl X x) := mem_U_lvl
  have hcont : ContinuousOn (PsiU fl FF S) (U X (lvl X x)) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hres : (U X (lvl X x)).domRestrict (PsiU fl FF S) =
        (U X (lvl X x)).domRestrict (seqU2 fl FF S (lvl X x)).1 := by
      funext z
      rw [Set.domRestrict_apply, Set.domRestrict_apply]
      exact PsiU_eq fl FF S z.2
    rw [hres]
    exact continuousOn_iff_continuous_domRestrict.mp (seqU2 fl FF S (lvl X x)).2.good.cont
  exact hcont.continuousAt ((isOpen_U X (lvl X x)).mem_nhds hx)

/-- Far to the right, `PsiU` is the inverse of the Fatou coordinate on the sub-petal `Pg`. -/
theorem PsiU_far (S : Seed fl FF v X Ψs) {w : ℂ} (hw : X < w.re) :
    PsiU fl FF S w ∈ FF.Pg ∧ fl.φa (PsiU fl FF S w) = w := by
  have hwk : w ∈ U X 0 := by
    rw [mem_U]
    simpa using hw
  rw [PsiU_eq fl FF S hwk]
  exact (seqU2 fl FF S 0).2.good.far w hw

/-! ## Boundedness -/

/-- If an iterate of `z` has bounded orbit then so does `z` (the orbit of `z` is a finite prefix
followed by the orbit of its iterate). -/
theorem BoundedOrbit.of_iterate {c z : ℂ} {N : ℕ}
    (h : Work.ParamRays.BoundedOrbit c ((Tantibar c)^[N] z)) :
    Work.ParamRays.BoundedOrbit c z := by
  obtain ⟨M, hM⟩ := h
  set T : ℝ := ∑ i ∈ Finset.range N, ‖Work.ParamRays.orbit c z i‖ with hT
  have hTnn : 0 ≤ T := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  refine ⟨M + T, fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · have h1 : ‖Work.ParamRays.orbit c z n‖ ≤ T :=
      Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hn)
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = N + m := ⟨n - N, by omega⟩
    rw [Work.ParamRays.orbit_add]
    have h3 : ‖Work.ParamRays.orbit c (Work.ParamRays.orbit c z N) m‖ ≤ M := hM m
    linarith

/-- **`PsiU` is bounded**: its values lie in the filled Julia set `K c₀` of `T_{c₀}`. -/
theorem PsiU_boundedOrbit (S : Seed fl FF v X Ψs) (hK : fl.Pa ⊆ Work.EL.K c₀) (w : ℂ) :
    Work.ParamRays.BoundedOrbit c₀ (PsiU fl FF S w) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (X - w.re)
  have hXw : X < (w + (n : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hmem : PsiU fl FF S (w + (n : ℂ)) ∈ Work.EL.K c₀ :=
    hK (FF.Pg_sub (PsiU_far fl FF S hXw).1)
  rw [PsiU_iterate_shift fl FF S w n] at hmem
  rw [Work.GATE2.PL.F_iterate_eq] at hmem
  exact BoundedOrbit.of_iterate hmem

/-- The quantitative form of the boundedness: `‖PsiU w‖ ≤ max 2 ‖c₀‖`. -/
theorem PsiU_norm_le (S : Seed fl FF v X Ψs) (hK : fl.Pa ⊆ Work.EL.K c₀) (w : ℂ) :
    ‖PsiU fl FF S w‖ ≤ max 2 ‖c₀‖ :=
  Work.ParamRays.norm_le_max_of_bounded c₀ _ (PsiU_boundedOrbit fl FF S hK w)

end

end Work.GATE2.PL
