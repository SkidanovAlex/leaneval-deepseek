import Submission.Work.RatHurewicz.RelPiPathDefs
import Submission.Work.RatHurewicz.RelPiPathBasepoint
import Submission.Work.StemsB.transSymm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The comparison maps of the homotopy fibres are homotopy equivalences

For `η : Path a₀ a` in `↥A` and `ηy = setInclPath a₀ a η`, the two comparison maps
`relPathPhi a₀ a η : E_a → E_{a₀}` and `relPathPsi a₀ a η : E_{a₀} → E_a` of
`Submission/Work/RatHurewicz/RelPiPathDefs.lean` satisfy `ψ ∘ φ ~ id` and `φ ∘ ψ ~ id`.  This
file proves one of the two composites (`φ ∘ ψ ~ id`, on `E_{a₀}`) in full, and derives the other by
applying the same result to the reversed path `η.symm`.

The proof of `φ ∘ ψ ~ id` factors through the map `prependLoop a₀ (ηy ≫ ηy⁻¹)` which prepends the
*loop* `ηy ≫ ηy⁻¹` to the path component (this is `(ηy ≫ ηy⁻¹) ≫ γ` rather than
`ηy ≫ (ηy⁻¹ ≫ γ)`; the two differ by the associativity reparametrisation of `Path.trans`).  The
loop `ηy ≫ ηy⁻¹` is then null-homotopic *continuously* in the loop, by the explicit null-homotopy
`Work.StemsB.transSymmFamily`; finally `(refl) ≫ γ ~ γ` is the standard reparametrisation.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap
open Work.StemsB

set_option maxHeartbeats 1000000

namespace Work.RatHurewicz

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {A : Set Y}

/-! ## Prepending a loop to the path component -/

/-- Continuity of the concatenation `ρ ≫ γ_p` over `p`, in the clamped form. -/
theorem continuous_prependLoop_fun (a : ↥A) (ρ : Path (setIncl A a) (setIncl A a)) :
    Continuous fun q : homotopyFibre (setIncl A) a × I =>
      (ρ.trans (fibrePath q.1)) q.2 := by
  have key : (fun q : homotopyFibre (setIncl A) a × I =>
        (ρ.trans (fibrePath q.1)) q.2) =
      fun q : homotopyFibre (setIncl A) a × I =>
        if (2 : ℝ) * (q.2 : ℝ) ≤ 1 then ρ (clampI (2 * (q.2 : ℝ)))
        else fibreCM q.1 (clampI (2 * (q.2 : ℝ) - 1)) := by
    funext q
    rw [trans_apply_clampI]
    rfl
  rw [key]
  refine Continuous.if_le
    (f := fun q : homotopyFibre (setIncl A) a × I => (2 : ℝ) * (q.2 : ℝ))
    (g := fun _ : homotopyFibre (setIncl A) a × I => (1 : ℝ))
    (f' := fun q : homotopyFibre (setIncl A) a × I => ρ (clampI (2 * (q.2 : ℝ))))
    (g' := fun q : homotopyFibre (setIncl A) a × I =>
      fibreCM q.1 (clampI (2 * (q.2 : ℝ) - 1))) ?_ ?_ ?_ ?_ ?_
  · exact ρ.continuous.comp (continuous_clampI.comp (by fun_prop))
  · exact continuous_apply_comp ((fibreCMFamily a).continuous.comp continuous_fst)
      (continuous_clampI.comp (by fun_prop))
  · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
  · exact continuous_const
  · intro q hq
    have h1 : (2 : ℝ) * (q.2 : ℝ) = 1 := hq
    rw [h1, clampI_one, sub_self, clampI_zero]
    rw [show ρ (1 : I) = setIncl A a from Path.target ρ,
      show fibreCM q.1 (0 : I) = setIncl A a from fibreCM_zero q.1]

/-- Prepend the loop `ρ` (based at `i a`) to the path component of a point of the homotopy fibre:
`(a', γ) ↦ (a', ρ ≫ γ)`. -/
def prependLoop (a : ↥A) (ρ : Path (setIncl A a) (setIncl A a)) :
    C(homotopyFibre (setIncl A) a, homotopyFibre (setIncl A) a) where
  toFun p :=
    ⟨(p.1.1, (⟨(ρ.trans (fibrePath p)).toContinuousMap,
      (ρ.trans (fibrePath p)).source'⟩ : PathSpace Y (setIncl A a))),
      (ρ.trans (fibrePath p)).target'⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp continuous_subtype_val
    · refine Continuous.subtype_mk ?_ _
      exact continuous_of_continuous_uncurry _ (continuous_prependLoop_fun a ρ)

@[simp]
theorem prependLoop_fst (a : ↥A) (ρ : Path (setIncl A a) (setIncl A a))
    (p : homotopyFibre (setIncl A) a) : (prependLoop a ρ p).1.1 = p.1.1 := rfl

@[simp]
theorem prependLoop_snd (a : ↥A) (ρ : Path (setIncl A a) (setIncl A a))
    (p : homotopyFibre (setIncl A) a) :
    fibrePath (prependLoop a ρ p) = ρ.trans (fibrePath p) := rfl

/-! ## The loop `α ≫ α⁻¹` is null-homotopic, continuously -/

/-- Continuity of `z ↦ f z (g z)` for a continuous family of *paths* `f`. -/
theorem continuous_apply_comp_path {Z : Type} [TopologicalSpace Z] {x y : Y}
    {f : Z → Path x y} (hf : Continuous f) {g : Z → I} (hg : Continuous g) :
    Continuous fun z => f z (g z) :=
  ((show Continuous fun fx : Path x y × I => fx.1 fx.2 from continuous_eval).comp (hf.prodMk hg))

/-- The path in the loop space of `Y` at `i a` which is the explicit null-homotopy of the loop
`α ≫ α⁻¹` (`Work.StemsB.transSymmFamily`, continuous in `α`). -/
def loopShrinkPath (a : ↥A) {w : Y} (α : Path (setIncl A a) w) :
    Path (α.trans α.symm) (Path.refl (setIncl A a)) where
  toContinuousMap :=
    ⟨fun r => transSymmFamily (X := Y) (b := setIncl A a) (b' := w) (r, α),
      continuous_transSymmFamily.comp (continuous_id.prodMk continuous_const)⟩
  source' := Path.ext (funext fun t => transSymmFun_zero_r α t)
  target' := Path.ext (funext fun t => by
    show transSymmFun 1 α t = (Path.refl (setIncl A a)) t
    rw [transSymmFun_one_r]
    rfl)


/-! ## Convergence of a prepended loop to the constant loop -/

/-- Continuity of the uncurried formula for the shrinking homotopy of a prepended loop. -/
theorem continuous_shrinkFun (a : ↥A) {w : Y} (α : Path (setIncl A a) w) :
    Continuous fun q : (I × homotopyFibre (setIncl A) a) × I =>
      if (2 : ℝ) * (q.2 : ℝ) ≤ 1 then loopShrinkPath a α q.1.1 (clampI (2 * (q.2 : ℝ)))
      else fibreCM q.1.2 (clampI (2 * (q.2 : ℝ) - 1)) := by
  refine Continuous.if_le
    (f := fun q : (I × homotopyFibre (setIncl A) a) × I => (2 : ℝ) * (q.2 : ℝ))
    (g := fun _ : (I × homotopyFibre (setIncl A) a) × I => (1 : ℝ))
    (f' := fun q : (I × homotopyFibre (setIncl A) a) × I =>
      loopShrinkPath a α q.1.1 (clampI (2 * (q.2 : ℝ))))
    (g' := fun q : (I × homotopyFibre (setIncl A) a) × I =>
      fibreCM q.1.2 (clampI (2 * (q.2 : ℝ) - 1))) ?_ ?_ ?_ ?_ ?_
  · exact continuous_apply_comp_path
      ((loopShrinkPath a α).continuous.comp (continuous_fst.comp continuous_fst))
      (continuous_clampI.comp ((continuous_const.mul
        (continuous_subtype_val.comp continuous_snd))))
  · exact ((show Continuous fun fx : C(I, Y) × I => fx.1 fx.2 from continuous_eval).comp
      (Continuous.prodMk
        (f := fun q : (I × homotopyFibre (setIncl A) a) × I => fibreCMFamily a (q.1.2))
        (g := fun q : (I × homotopyFibre (setIncl A) a) × I => clampI (2 * (q.2 : ℝ) - 1))
        ((fibreCMFamily a).continuous.comp
          (f := fun q : (I × homotopyFibre (setIncl A) a) × I => q.1.2) (by fun_prop))
        (continuous_clampI.comp (by fun_prop))))
  · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
  · exact continuous_const
  · intro q hq
    have h1 : (2 : ℝ) * (q.2 : ℝ) = 1 := hq
    rw [h1, clampI_one, sub_self, clampI_zero]
    rw [show loopShrinkPath a α q.1.1 (1 : I) = setIncl A a from Path.target _,
      show fibreCM q.1.2 (0 : I) = setIncl A a from fibreCM_zero q.1.2]

/-- The homotopy which shrinks a prepended loop to the constant loop. -/
def shrinkHomotopy (a : ↥A) {w : Y} (α : Path (setIncl A a) w) :
    ContinuousMap.Homotopy (prependLoop a (α.trans α.symm))
      (prependLoop a (Path.refl (setIncl A a))) where
  toFun u :=
    ⟨(u.2.1.1, (⟨⟨fun s =>
        if (2 : ℝ) * (s : ℝ) ≤ 1 then loopShrinkPath a α u.1 (clampI (2 * (s : ℝ)))
        else fibreCM u.2 (clampI (2 * (s : ℝ) - 1)),
      (continuous_shrinkFun a α).comp
        (((continuous_const : Continuous fun _ : I => u.1).prodMk
          (continuous_const : Continuous fun _ : I => u.2)).prodMk continuous_id)⟩,
      by
        show (if (2 : ℝ) * (((0 : I)) : ℝ) ≤ 1 then
            loopShrinkPath a α u.1 (clampI (2 * (((0 : I)) : ℝ)))
          else fibreCM u.2 (clampI (2 * (((0 : I)) : ℝ) - 1))) = setIncl A a
        rw [if_pos (by norm_num : (2 : ℝ) * (((0 : I)) : ℝ) ≤ 1),
          show (2 : ℝ) * (((0 : I)) : ℝ) = 0 by rw [show (((0 : I)) : ℝ) = 0 from rfl]; ring,
          clampI_zero]
        exact Path.source _⟩ : PathSpace Y (setIncl A a))),
      by
        show (if (2 : ℝ) * (((1 : I)) : ℝ) ≤ 1 then
            loopShrinkPath a α u.1 (clampI (2 * (((1 : I)) : ℝ)))
          else fibreCM u.2 (clampI (2 * (((1 : I)) : ℝ) - 1))) = setIncl A u.2.1.1
        rw [show (((1 : I)) : ℝ) = 1 from rfl,
          if_neg (by norm_num : ¬ ((2 : ℝ) * 1 ≤ 1)),
          show (2 : ℝ) * 1 - 1 = 1 by norm_num, clampI_one]
        exact fibreCM_one u.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
    · refine Continuous.subtype_mk ?_ _
      exact continuous_of_continuous_uncurry _ (continuous_shrinkFun a α)
  map_zero_left := by
    intro p
    refine Subtype.ext (Prod.ext rfl ?_)
    refine Subtype.ext (ContinuousMap.ext fun s => ?_)
    show (if (2 : ℝ) * (s : ℝ) ≤ 1 then
        loopShrinkPath a α (0 : I) (clampI (2 * (s : ℝ)))
      else fibreCM p (clampI (2 * (s : ℝ) - 1))) = _
    rw [show loopShrinkPath a α (0 : I) = α.trans α.symm from Path.source _]
    show (if (2 : ℝ) * (s : ℝ) ≤ 1 then (α.trans α.symm) (clampI (2 * (s : ℝ)))
      else fibreCM p (clampI (2 * (s : ℝ) - 1)))
      = fibrePath (prependLoop a (α.trans α.symm) p) s
    rw [prependLoop_snd]
    show (if (2 : ℝ) * (s : ℝ) ≤ 1 then (α.trans α.symm) (clampI (2 * (s : ℝ)))
      else fibreCM p (clampI (2 * (s : ℝ) - 1)))
      = ((α.trans α.symm).trans (fibrePath p)) s
    rw [show ((α.trans α.symm).trans (fibrePath p)) s
          = (if (2 : ℝ) * (s : ℝ) ≤ 1 then (α.trans α.symm) (clampI (2 * (s : ℝ)))
             else (fibrePath p) (clampI (2 * (s : ℝ) - 1)))
        from trans_apply_clampI _ _ _,
      show (α.trans α.symm) (clampI (2 * (s : ℝ)))
          = (if (2 : ℝ) * ((clampI (2 * (s : ℝ))) : ℝ) ≤ 1
             then α (clampI (2 * ((clampI (2 * (s : ℝ))) : ℝ)))
             else α.symm (clampI (2 * ((clampI (2 * (s : ℝ))) : ℝ) - 1)))
        from trans_apply_clampI _ _ _]
    rfl
  map_one_left := by
    intro p
    refine Subtype.ext (Prod.ext rfl ?_)
    refine Subtype.ext (ContinuousMap.ext fun s => ?_)
    show (if (2 : ℝ) * (s : ℝ) ≤ 1 then
        loopShrinkPath a α (1 : I) (clampI (2 * (s : ℝ)))
      else fibreCM p (clampI (2 * (s : ℝ) - 1))) = _
    rw [show loopShrinkPath a α (1 : I) = Path.refl (setIncl A a) from Path.target _]
    show (if (2 : ℝ) * (s : ℝ) ≤ 1 then (Path.refl (setIncl A a)) (clampI (2 * (s : ℝ)))
      else fibreCM p (clampI (2 * (s : ℝ) - 1)))
      = fibrePath (prependLoop a (Path.refl (setIncl A a)) p) s
    rw [prependLoop_snd]
    show (if (2 : ℝ) * (s : ℝ) ≤ 1 then (Path.refl (setIncl A a)) (clampI (2 * (s : ℝ)))
      else fibreCM p (clampI (2 * (s : ℝ) - 1)))
      = ((Path.refl (setIncl A a)).trans (fibrePath p)) s
    rw [show ((Path.refl (setIncl A a)).trans (fibrePath p)) s
          = (if (2 : ℝ) * (s : ℝ) ≤ 1 then (Path.refl (setIncl A a)) (clampI (2 * (s : ℝ)))
             else (fibrePath p) (clampI (2 * (s : ℝ) - 1)))
        from trans_apply_clampI _ _ _]
    rfl

/-! ## The reparametrisation `(refl) ≫ γ ~ γ` -/

/-- Continuity of the uncurried formula of the reparametrisation homotopy. -/
theorem continuous_reflPrependFun (a : ↥A) :
    Continuous fun q : (I × homotopyFibre (setIncl A) a) × I =>
      if (2 : ℝ) * (q.2 : ℝ) ≤ 1 - (q.1.1 : ℝ) then setIncl A a
      else fibreCM q.1.2
        (clampI ((2 * (q.2 : ℝ) - 1 + (q.1.1 : ℝ)) / (1 + (q.1.1 : ℝ)))) := by
  refine Continuous.if_le
    (f := fun q : (I × homotopyFibre (setIncl A) a) × I => (2 : ℝ) * (q.2 : ℝ))
    (g := fun q : (I × homotopyFibre (setIncl A) a) × I => 1 - (q.1.1 : ℝ))
    (f' := fun q : (I × homotopyFibre (setIncl A) a) × I => setIncl A a)
    (g' := fun q : (I × homotopyFibre (setIncl A) a) × I => fibreCM q.1.2
        (clampI ((2 * (q.2 : ℝ) - 1 + (q.1.1 : ℝ)) / (1 + (q.1.1 : ℝ))))) ?_ ?_ ?_ ?_ ?_
  · exact continuous_const
  · have hfam : Continuous fun q : (I × homotopyFibre (setIncl A) a) × I =>
        fibreCM q.1.2 :=
      (fibreCMFamily a).continuous.comp
        (f := fun q : (I × homotopyFibre (setIncl A) a) × I => q.1.2) (by fun_prop)
    have harg : Continuous fun q : (I × homotopyFibre (setIncl A) a) × I =>
        clampI ((2 * (q.2 : ℝ) - 1 + (q.1.1 : ℝ)) / (1 + (q.1.1 : ℝ))) :=
      continuous_clampI.comp
        (Continuous.div (by fun_prop) (by fun_prop) (fun q => by
          have h := q.1.1.2.1
          linarith))
    exact continuous_apply_comp hfam harg
  · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
  · exact continuous_const.sub
      (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
  · intro q hq
    have h0 : 2 * (q.2 : ℝ) - 1 + (q.1.1 : ℝ) = 0 := by linarith [hq]
    rw [h0, zero_div, clampI_zero]
    exact (fibreCM_zero q.1.2).symm

/-- The standard reparametrisation homotopy `(refl) ≫ γ ~ γ`, written out explicitly. -/
def reflPrependHomotopy (a : ↥A) :
    ContinuousMap.Homotopy (prependLoop a (Path.refl (setIncl A a)))
      (ContinuousMap.id (homotopyFibre (setIncl A) a)) where
  toFun u :=
    ⟨(u.2.1.1, (⟨⟨fun s =>
        if (2 : ℝ) * (s : ℝ) ≤ 1 - (u.1 : ℝ) then setIncl A a
        else fibreCM u.2
          (clampI ((2 * (s : ℝ) - 1 + (u.1 : ℝ)) / (1 + (u.1 : ℝ)))),
      (continuous_reflPrependFun a).comp
        (((continuous_const : Continuous fun _ : I => u.1).prodMk
          (continuous_const : Continuous fun _ : I => u.2)).prodMk continuous_id)⟩,
      by
        show (if (2 : ℝ) * (((0 : I)) : ℝ) ≤ 1 - (u.1 : ℝ) then setIncl A a
          else fibreCM u.2 (clampI ((2 * (((0 : I)) : ℝ) - 1 + (u.1 : ℝ))
            / (1 + (u.1 : ℝ))))) = setIncl A a
        rw [show (((0 : I)) : ℝ) = 0 from rfl, mul_zero,
          if_pos (by linarith [u.1.2.2])]
      ⟩ : PathSpace Y (setIncl A a))),
      by
        show (if (2 : ℝ) * (((1 : I)) : ℝ) ≤ 1 - (u.1 : ℝ) then setIncl A a
          else fibreCM u.2 (clampI ((2 * (((1 : I)) : ℝ) - 1 + (u.1 : ℝ))
            / (1 + (u.1 : ℝ))))) = setIncl A u.2.1.1
        rw [show (((1 : I)) : ℝ) = 1 from rfl,
          if_neg (by linarith [u.1.2.1] :
            ¬ ((2 : ℝ) * 1 ≤ 1 - (u.1 : ℝ))),
          show (2 : ℝ) * 1 - 1 + (u.1 : ℝ) = 1 + (u.1 : ℝ) by ring,
          div_self (by linarith [u.1.2.1] : (1 + (u.1 : ℝ)) ≠ 0), clampI_one]
        exact fibreCM_one u.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
    · refine Continuous.subtype_mk ?_ _
      exact continuous_of_continuous_uncurry _ (continuous_reflPrependFun a)
  map_zero_left := by
    intro p
    refine Subtype.ext (Prod.ext rfl ?_)
    refine Subtype.ext (ContinuousMap.ext fun s => ?_)
    show (if (2 : ℝ) * (s : ℝ) ≤ 1 - (((0 : I)) : ℝ) then setIncl A a
      else fibreCM p (clampI ((2 * (s : ℝ) - 1 + (((0 : I)) : ℝ))
        / (1 + (((0 : I)) : ℝ))))) = fibrePath (prependLoop a (Path.refl (setIncl A a)) p) s
    rw [show (((0 : I)) : ℝ) = 0 from rfl, sub_zero, add_zero, add_zero]
    rw [prependLoop_snd]
    show (if (2 : ℝ) * (s : ℝ) ≤ 1 then setIncl A a
      else fibreCM p (clampI ((2 * (s : ℝ) - 1) / 1)))
      = ((Path.refl (setIncl A a)).trans (fibrePath p)) s
    rw [div_one, show ((Path.refl (setIncl A a)).trans (fibrePath p)) s
        = (if (2 : ℝ) * (s : ℝ) ≤ 1 then (Path.refl (setIncl A a)) (clampI (2 * (s : ℝ)))
           else (fibrePath p) (clampI (2 * (s : ℝ) - 1)))
      from trans_apply_clampI _ _ _]
    by_cases hs : (2 : ℝ) * (s : ℝ) ≤ 1
    · rw [if_pos hs, if_pos hs]
      rfl
    · rw [if_neg hs, if_neg hs]
      rfl
  map_one_left := by
    intro p
    refine Subtype.ext (Prod.ext rfl ?_)
    refine Subtype.ext (ContinuousMap.ext fun s => ?_)
    show (if (2 : ℝ) * (s : ℝ) ≤ 1 - (((1 : I)) : ℝ) then setIncl A a
      else fibreCM p (clampI ((2 * (s : ℝ) - 1 + (((1 : I)) : ℝ))
        / (1 + (((1 : I)) : ℝ))))) = fibreCM p s
    rw [show (((1 : I)) : ℝ) = 1 from rfl]
    by_cases hs : (2 : ℝ) * (s : ℝ) ≤ 1 - 1
    · rw [if_pos hs]
      have hs0 : s = (0 : I) := Subtype.ext (by show (s : ℝ) = 0; linarith [s.2.1])
      rw [hs0]
      exact (fibreCM_zero p).symm
    · rw [if_neg hs,
        show (2 : ℝ) * (s : ℝ) - 1 + 1 = 2 * (s : ℝ) by ring,
        show (2 * (s : ℝ)) / (1 + 1) = (s : ℝ) by ring, clampI_coe_I]


/-! ## The associativity homotopy -/

/-- Continuity of the uncurried formula of the associativity homotopy. -/
theorem continuous_assocFun (a₀ a : ↥A) (η : Path a₀ a) :
    Continuous fun q : (I × homotopyFibre (setIncl A) a₀) × I =>
      fibreCM (((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) q.1.2)
        (clampI ((1 - (q.1.1 : ℝ)) * (q.2 : ℝ)
          + (q.1.1 : ℝ) * Path.Homotopy.transAssocReparamAux q.2)) := by
  have hfam : Continuous fun q : (I × homotopyFibre (setIncl A) a₀) × I =>
      fibreCM (((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) q.1.2) :=
    (fibreCMFamily a₀).continuous.comp
      (f := fun q : (I × homotopyFibre (setIncl A) a₀) × I =>
        ((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) q.1.2)
      ((((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)).continuous.comp
        (f := fun q : (I × homotopyFibre (setIncl A) a₀) × I => q.1.2) (by fun_prop)))
  have harg : Continuous fun q : (I × homotopyFibre (setIncl A) a₀) × I =>
      clampI ((1 - (q.1.1 : ℝ)) * (q.2 : ℝ)
        + (q.1.1 : ℝ) * Path.Homotopy.transAssocReparamAux q.2) :=
    continuous_clampI.comp (by fun_prop)
  exact continuous_apply_comp hfam harg

/-- The fixed-parameter continuity of the associativity homotopy. -/
theorem continuous_assocFun_fixed (a₀ a : ↥A) (η : Path a₀ a)
    (u : I × homotopyFibre (setIncl A) a₀) :
    Continuous fun s : I =>
      fibreCM (((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) u.2)
        (clampI ((1 - (u.1 : ℝ)) * (s : ℝ)
          + (u.1 : ℝ) * Path.Homotopy.transAssocReparamAux s)) :=
  continuous_apply_comp (continuous_const : Continuous fun _ : I =>
      fibreCM (((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) u.2))
    (continuous_clampI.comp (by fun_prop))

/-- The associativity reparametrisation, applied to the composite `φ ∘ ψ`: it rewrites
`ηy ≫ (ηy⁻¹ ≫ γ)` into `(ηy ≫ ηy⁻¹) ≫ γ`. -/
def assocHomotopy (a₀ a : ↥A) (η : Path a₀ a) :
    ContinuousMap.Homotopy ((relPathPhi a₀ a η).comp (relPathPsi a₀ a η))
      (prependLoop a₀ ((setInclPath a₀ a η).trans (setInclPath a₀ a η).symm)) where
  toFun u :=
    ⟨(u.2.1.1, (⟨⟨fun s =>
        fibreCM (((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) u.2)
          (clampI ((1 - (u.1 : ℝ)) * (s : ℝ)
            + (u.1 : ℝ) * Path.Homotopy.transAssocReparamAux s)),
      continuous_assocFun_fixed a₀ a η u⟩,
      by
        show fibreCM (((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) u.2)
          (clampI ((1 - (u.1 : ℝ)) * (((0 : I)) : ℝ)
            + (u.1 : ℝ) * Path.Homotopy.transAssocReparamAux (0 : I))) = setIncl A a₀
        rw [show (((0 : I)) : ℝ) = 0 from rfl,
          show (1 - (u.1 : ℝ)) * 0 + (u.1 : ℝ) * Path.Homotopy.transAssocReparamAux (0 : I)
            = 0 by rw [Path.Homotopy.transAssocReparamAux_zero]; ring,
          clampI_zero]
        exact fibreCM_zero _⟩ : PathSpace Y (setIncl A a₀))),
      by
        show fibreCM (((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) u.2)
          (clampI ((1 - (u.1 : ℝ)) * (((1 : I)) : ℝ)
            + (u.1 : ℝ) * Path.Homotopy.transAssocReparamAux (1 : I))) = setIncl A u.2.1.1
        rw [show (((1 : I)) : ℝ) = 1 from rfl,
          show (1 - (u.1 : ℝ)) * 1 + (u.1 : ℝ) * Path.Homotopy.transAssocReparamAux (1 : I)
            = 1 by rw [Path.Homotopy.transAssocReparamAux_one]; ring,
          clampI_one]
        exact fibreCM_one _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
    · refine Continuous.subtype_mk ?_ _
      exact continuous_of_continuous_uncurry _ (continuous_assocFun a₀ a η)
  map_zero_left := by
    intro p
    refine Subtype.ext (Prod.ext rfl ?_)
    refine Subtype.ext (ContinuousMap.ext fun s => ?_)
    show fibreCM (((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) p)
      (clampI ((1 - (((0 : I)) : ℝ)) * (s : ℝ)
        + (((0 : I)) : ℝ) * Path.Homotopy.transAssocReparamAux s)) = _
    rw [show (((0 : I)) : ℝ) = 0 from rfl,
      show (1 - (0 : ℝ)) * (s : ℝ) + 0 * Path.Homotopy.transAssocReparamAux s = (s : ℝ) by ring,
      clampI_coe_I]
    rfl
  map_one_left := by
    intro p
    refine Subtype.ext (Prod.ext rfl ?_)
    refine Subtype.ext (ContinuousMap.ext fun s => ?_)
    show fibreCM (((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) p)
      (clampI ((1 - (((1 : I)) : ℝ)) * (s : ℝ)
        + (((1 : I)) : ℝ) * Path.Homotopy.transAssocReparamAux s)) = _
    rw [show (((1 : I)) : ℝ) = 1 from rfl,
      show (1 - (1 : ℝ)) * (s : ℝ) + 1 * Path.Homotopy.transAssocReparamAux s
        = Path.Homotopy.transAssocReparamAux s by ring,
      clampI_of_mem (Path.Homotopy.transAssocReparamAux_mem_I s)]
    have hF : fibreCM (((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) p)
        = (((setInclPath a₀ a η).trans
            ((setInclPath a₀ a η).symm.trans (fibrePath p)))).toContinuousMap := by
      show (fibrePath (((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) p)).toContinuousMap
        = (((setInclPath a₀ a η).trans
            ((setInclPath a₀ a η).symm.trans (fibrePath p)))).toContinuousMap
      rw [ContinuousMap.comp_apply, relPathPhi_snd, relPathPsi_snd]
      try rfl
    rw [hF]
    show (((setInclPath a₀ a η).trans
        ((setInclPath a₀ a η).symm.trans (fibrePath p)))).toContinuousMap
      ⟨Path.Homotopy.transAssocReparamAux s, Path.Homotopy.transAssocReparamAux_mem_I s⟩
      = fibrePath (prependLoop a₀ ((setInclPath a₀ a η).trans (setInclPath a₀ a η).symm) p) s
    rw [prependLoop_snd]
    have hA := Path.Homotopy.trans_assoc_reparam (setInclPath a₀ a η)
      ((setInclPath a₀ a η).symm) (fibrePath p)
    rw [hA]
    show fibreCM (((relPathPhi a₀ a η).comp (relPathPsi a₀ a η)) p)
        ⟨Path.Homotopy.transAssocReparamAux s, Path.Homotopy.transAssocReparamAux_mem_I s⟩
      = ((setInclPath a₀ a η).trans
          ((setInclPath a₀ a η).symm.trans (fibrePath p))).toContinuousMap
        ⟨Path.Homotopy.transAssocReparamAux s, Path.Homotopy.transAssocReparamAux_mem_I s⟩
    rw [hF]

/-! ## The two composites -/

theorem relPathPhi_comp_relPathPsi_homotopic (a₀ a : ↥A) (η : Path a₀ a) :
    ContinuousMap.Homotopic
      ((relPathPhi a₀ a η).comp (relPathPsi a₀ a η))
      (ContinuousMap.id (homotopyFibre (setIncl A) a₀)) :=
  ⟨(assocHomotopy a₀ a η).trans
    ((shrinkHomotopy a₀ (setInclPath a₀ a η)).trans (reflPrependHomotopy a₀))⟩

theorem relPathPsi_comp_relPathPhi_homotopic (a₀ a : ↥A) (η : Path a₀ a) :
    ContinuousMap.Homotopic
      ((relPathPsi a₀ a η).comp (relPathPhi a₀ a η))
      (ContinuousMap.id (homotopyFibre (setIncl A) a)) := by
  have h := relPathPhi_comp_relPathPsi_homotopic a a₀ η.symm
  have hcomp : (relPathPhi a a₀ η.symm).comp (relPathPsi a a₀ η.symm)
      = (relPathPsi a₀ a η).comp (relPathPhi a₀ a η) := by
    ext p
    refine Subtype.ext (Prod.ext rfl ?_)
    refine Subtype.ext (ContinuousMap.ext fun s => ?_)
    show fibrePath ((relPathPhi a a₀ η.symm) ((relPathPsi a a₀ η.symm) p)) s
      = fibrePath ((relPathPsi a₀ a η) ((relPathPhi a₀ a η) p)) s
    simp only [relPathPhi_snd, relPathPsi_snd, setInclPath_symm, Path.symm_symm]
    try rfl
  rwa [hcomp] at h

end

end Work.RatHurewicz
