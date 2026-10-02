import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.Excision
import Submission.Work.StemsB.isSerreFibration_evalOne

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Comparing the homotopy fibres of `A ↪ Y` at two points of `A` joined by a path

Let `A ⊆ Y` and `i = setIncl A : ↥A → Y`.  For `a : ↥A` the homotopy fibre
`E_a = homotopyFibre i a` (`Work.RatHurewicz`) is the space of pairs `(a', γ)` with `γ` a path in
`Y` from `i a` to `i a'`, with base point `bp_a = (a, const)`.

Given a path `η : Path a₀ a` in `↥A`, this file constructs the two comparison maps

* `relPathPhi a₀ a η : E_a → E_{a₀}`, `(a', γ) ↦ (a', η ≫ γ)`,
* `relPathPsi a₀ a η : E_{a₀} → E_a`, `(a', γ) ↦ (a', η⁻¹ ≫ γ)`,

where `η` is regarded as a path in `Y` through `setInclPath a₀ a η = η.map (setIncl A).continuous`.

These maps are the geometric input for the base point change of the relative homotopy groups along
a path in the subspace: they are mutually inverse up to homotopy (proved in the sibling file
`Submission/Work/RatHurewicz/RelPiPathHomotopy.lean`), and the base points `bp_{a₀}` and
`relPathPhi a₀ a η bp_a` are joined in `E_{a₀}` (sibling file
`Submission/Work/RatHurewicz/RelPiPathBasepoint.lean`).
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap
open Work.StemsB

namespace Work.RatHurewicz

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {A : Set Y}

/-! ## The path in `Y` underlying `η` -/

/-- The path `η` of `↥A` regarded as a path of `Y` through the inclusion. -/
def setInclPath (a₀ a : ↥A) (η : Path a₀ a) : Path (setIncl A a₀) (setIncl A a) :=
  η.map (setIncl A).continuous

@[simp]
theorem setInclPath_apply (a₀ a : ↥A) (η : Path a₀ a) (t : I) :
    setInclPath a₀ a η t = (η t : Y) := by
  rw [setInclPath, Path.map_coe]; rfl

theorem setInclPath_symm (a₀ a : ↥A) (η : Path a₀ a) :
    (setInclPath a₀ a η).symm = setInclPath a a₀ η.symm := by
  rw [setInclPath, setInclPath, Path.map_symm]

/-! ## The path attached to a point of the homotopy fibre -/

/-- The path component of a point of the homotopy fibre, as a continuous map `I → Y`. -/
def fibreCM {a : ↥A} (p : homotopyFibre (setIncl A) a) : C(I, Y) := p.1.2.1

theorem fibreCM_zero {a : ↥A} (p : homotopyFibre (setIncl A) a) :
    fibreCM p 0 = setIncl A a := p.1.2.2

theorem fibreCM_one {a : ↥A} (p : homotopyFibre (setIncl A) a) :
    fibreCM p 1 = setIncl A p.1.1 := p.2

/-- The path component of a point of the homotopy fibre, as a `Path`. -/
def fibrePath {a : ↥A} (p : homotopyFibre (setIncl A) a) :
    Path (setIncl A a) (setIncl A p.1.1) :=
  ⟨p.1.2.1, p.1.2.2, p.2⟩

@[simp]
theorem fibrePath_apply {a : ↥A} (p : homotopyFibre (setIncl A) a) (t : I) :
    fibrePath p t = fibreCM p t := rfl

theorem fibrePath_basepoint (a : ↥A) :
    fibrePath (homotopyFibreBasepoint (setIncl A) a) = Path.refl (setIncl A a) := rfl

/-- The path component, as a continuous map `E_a → C(I, Y)`. -/
def fibreCMFamily (a : ↥A) : C(homotopyFibre (setIncl A) a, C(I, Y)) where
  toFun p := fibreCM p
  continuous_toFun :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)

@[simp]
theorem fibreCMFamily_apply (a : ↥A) (p : homotopyFibre (setIncl A) a) :
    fibreCMFamily a p = fibreCM p := rfl

/-! ## The pointwise formula for concatenation, with the clamping of the argument -/

/-- The concatenation `α ≫ δ`, evaluated with the clamping map `clampI` on the arguments; this is
the form in which continuity in the two paths is manifest. -/
theorem trans_apply_clampI {X : Type} [TopologicalSpace X] {x y z : X}
    (α : Path x y) (δ : Path y z) (t : I) :
    (α.trans δ) t =
      if (2 : ℝ) * (t : ℝ) ≤ 1 then α (clampI (2 * (t : ℝ)))
      else δ (clampI (2 * (t : ℝ) - 1)) := by
  rw [Path.trans_apply]
  by_cases h : (t : ℝ) ≤ 1 / 2
  · rw [dif_pos h, if_pos (by linarith)]
    refine congrArg α ?_
    rw [clampI_of_mem ⟨by linarith [t.2.1], by linarith⟩]
  · rw [dif_neg h, if_neg (by linarith)]
    refine congrArg δ ?_
    rw [clampI_of_mem ⟨by linarith [not_le.1 h], by linarith [t.2.2]⟩]

/-! ## A continuity helper for the evaluation of a path on a clamped parameter -/

/-- Continuity of `z ↦ f z (g z)` for a continuous family of paths `f` and a continuous parameter
`g`. -/
theorem continuous_apply_comp {Z : Type} [TopologicalSpace Z] {f : Z → C(I, Y)}
    (hf : Continuous f) {g : Z → I} (hg : Continuous g) : Continuous fun z => f z (g z) :=
  ((show Continuous fun fx : C(I, Y) × I => fx.1 fx.2 from continuous_eval).comp (hf.prodMk hg))

/-! ## Continuity of the concatenated family -/

theorem continuous_trans_fibrePath_phi (a₀ a : ↥A) (η : Path a₀ a) :
    Continuous fun q : homotopyFibre (setIncl A) a × I =>
      ((setInclPath a₀ a η).trans (fibrePath q.1)) q.2 := by
  have key : (fun q : homotopyFibre (setIncl A) a × I =>
        ((setInclPath a₀ a η).trans (fibrePath q.1)) q.2) =
      fun q : homotopyFibre (setIncl A) a × I =>
        if (2 : ℝ) * (q.2 : ℝ) ≤ 1 then (setInclPath a₀ a η) (clampI (2 * (q.2 : ℝ)))
        else fibreCM q.1 (clampI (2 * (q.2 : ℝ) - 1)) := by
    funext q
    rw [trans_apply_clampI]
    rfl
  rw [key]
  refine Continuous.if_le
    (f := fun q : homotopyFibre (setIncl A) a × I => (2 : ℝ) * (q.2 : ℝ))
    (g := fun _ : homotopyFibre (setIncl A) a × I => (1 : ℝ))
    (f' := fun q : homotopyFibre (setIncl A) a × I =>
      (setInclPath a₀ a η) (clampI (2 * (q.2 : ℝ))))
    (g' := fun q : homotopyFibre (setIncl A) a × I =>
      fibreCM q.1 (clampI (2 * (q.2 : ℝ) - 1))) ?_ ?_ ?_ ?_ ?_
  · exact (setInclPath a₀ a η).continuous.comp (continuous_clampI.comp (by fun_prop))
  · exact continuous_apply_comp ((fibreCMFamily a).continuous.comp continuous_fst)
      (continuous_clampI.comp (by fun_prop))
  · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
  · exact continuous_const
  · intro q hq
    have h1 : (2 : ℝ) * (q.2 : ℝ) = 1 := hq
    rw [h1, clampI_one, sub_self, clampI_zero]
    rw [show (setInclPath a₀ a η) (1 : I) = setIncl A a from (setInclPath a₀ a η).target',
      show fibreCM q.1 (0 : I) = setIncl A a from fibreCM_zero q.1]

theorem continuous_trans_fibrePath_psi (a₀ a : ↥A) (η : Path a₀ a) :
    Continuous fun q : homotopyFibre (setIncl A) a₀ × I =>
      (((setInclPath a₀ a η).symm).trans (fibrePath q.1)) q.2 := by
  have key : (fun q : homotopyFibre (setIncl A) a₀ × I =>
        (((setInclPath a₀ a η).symm).trans (fibrePath q.1)) q.2) =
      fun q : homotopyFibre (setIncl A) a₀ × I =>
        if (2 : ℝ) * (q.2 : ℝ) ≤ 1 then ((setInclPath a₀ a η).symm) (clampI (2 * (q.2 : ℝ)))
        else fibreCM q.1 (clampI (2 * (q.2 : ℝ) - 1)) := by
    funext q
    rw [trans_apply_clampI]
    rfl
  rw [key]
  refine Continuous.if_le
    (f := fun q : homotopyFibre (setIncl A) a₀ × I => (2 : ℝ) * (q.2 : ℝ))
    (g := fun _ : homotopyFibre (setIncl A) a₀ × I => (1 : ℝ))
    (f' := fun q : homotopyFibre (setIncl A) a₀ × I =>
      ((setInclPath a₀ a η).symm) (clampI (2 * (q.2 : ℝ))))
    (g' := fun q : homotopyFibre (setIncl A) a₀ × I =>
      fibreCM q.1 (clampI (2 * (q.2 : ℝ) - 1))) ?_ ?_ ?_ ?_ ?_
  · exact ((setInclPath a₀ a η).symm).continuous.comp (continuous_clampI.comp (by fun_prop))
  · exact continuous_apply_comp ((fibreCMFamily a₀).continuous.comp continuous_fst)
      (continuous_clampI.comp (by fun_prop))
  · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
  · exact continuous_const
  · intro q hq
    have h1 : (2 : ℝ) * (q.2 : ℝ) = 1 := hq
    rw [h1, clampI_one, sub_self, clampI_zero]
    rw [show ((setInclPath a₀ a η).symm) (1 : I) = setIncl A a₀
        from ((setInclPath a₀ a η).symm).target',
      show fibreCM q.1 (0 : I) = setIncl A a₀ from fibreCM_zero q.1]

/-! ## The two comparison maps -/

/-- The comparison map `E_a → E_{a₀}`, `(a', γ) ↦ (a', η ≫ γ)`. -/
def relPathPhi (a₀ a : ↥A) (η : Path a₀ a) :
    C(homotopyFibre (setIncl A) a, homotopyFibre (setIncl A) a₀) where
  toFun p :=
    ⟨(p.1.1, (⟨((setInclPath a₀ a η).trans (fibrePath p)).toContinuousMap,
      ((setInclPath a₀ a η).trans (fibrePath p)).source'⟩ : PathSpace Y (setIncl A a₀))),
      ((setInclPath a₀ a η).trans (fibrePath p)).target'⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp continuous_subtype_val
    · refine Continuous.subtype_mk ?_ _
      exact continuous_of_continuous_uncurry _
        (continuous_trans_fibrePath_phi a₀ a η)

/-- The comparison map `E_{a₀} → E_a`, `(a', γ) ↦ (a', η⁻¹ ≫ γ)`. -/
def relPathPsi (a₀ a : ↥A) (η : Path a₀ a) :
    C(homotopyFibre (setIncl A) a₀, homotopyFibre (setIncl A) a) where
  toFun q :=
    ⟨(q.1.1, (⟨(((setInclPath a₀ a η).symm).trans (fibrePath q)).toContinuousMap,
      (((setInclPath a₀ a η).symm).trans (fibrePath q)).source'⟩ : PathSpace Y (setIncl A a))),
      (((setInclPath a₀ a η).symm).trans (fibrePath q)).target'⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact continuous_fst.comp continuous_subtype_val
    · refine Continuous.subtype_mk ?_ _
      exact continuous_of_continuous_uncurry _
        (continuous_trans_fibrePath_psi a₀ a η)

@[simp]
theorem relPathPhi_apply (a₀ a : ↥A) (η : Path a₀ a) (p : homotopyFibre (setIncl A) a) :
    relPathPhi a₀ a η p =
      ⟨(p.1.1, (⟨((setInclPath a₀ a η).trans (fibrePath p)).toContinuousMap,
        ((setInclPath a₀ a η).trans (fibrePath p)).source'⟩ : PathSpace Y (setIncl A a₀))),
        ((setInclPath a₀ a η).trans (fibrePath p)).target'⟩ := rfl

@[simp]
theorem relPathPhi_fst (a₀ a : ↥A) (η : Path a₀ a) (p : homotopyFibre (setIncl A) a) :
    (relPathPhi a₀ a η p).1.1 = p.1.1 := rfl

@[simp]
theorem relPathPhi_snd (a₀ a : ↥A) (η : Path a₀ a) (p : homotopyFibre (setIncl A) a) :
    fibrePath (relPathPhi a₀ a η p) = (setInclPath a₀ a η).trans (fibrePath p) := rfl

@[simp]
theorem relPathPsi_apply (a₀ a : ↥A) (η : Path a₀ a) (q : homotopyFibre (setIncl A) a₀) :
    relPathPsi a₀ a η q =
      ⟨(q.1.1, (⟨(((setInclPath a₀ a η).symm).trans (fibrePath q)).toContinuousMap,
        (((setInclPath a₀ a η).symm).trans (fibrePath q)).source'⟩ : PathSpace Y (setIncl A a))),
        (((setInclPath a₀ a η).symm).trans (fibrePath q)).target'⟩ := rfl

@[simp]
theorem relPathPsi_fst (a₀ a : ↥A) (η : Path a₀ a) (q : homotopyFibre (setIncl A) a₀) :
    (relPathPsi a₀ a η q).1.1 = q.1.1 := rfl

@[simp]
theorem relPathPsi_snd (a₀ a : ↥A) (η : Path a₀ a) (q : homotopyFibre (setIncl A) a₀) :
    fibrePath (relPathPsi a₀ a η q) = ((setInclPath a₀ a η).symm).trans (fibrePath q) := rfl

end

end Work.RatHurewicz

/-!
### The proof route for the sibling files

Write `i = setIncl A`, `ηy = setInclPath a₀ a η` (a path in `Y` from `i a₀` to `i a`),
`γ_p = fibrePath p`, and `bp_a = homotopyFibreBasepoint i a`.

**`relPathPhi_comp_relPathPsi_homotopic` (the homotopy `φ ∘ ψ ~ id` on `E_{a₀}`).**
Pointwise, `φ (ψ q)` is the fibre point `(q.1.1, ηy.trans (ηy.symm.trans γ_q))`: this only depends on
`q` through the path `γ_q`, and the endpoint conditions hold automatically.  The homotopy can be
assembled from two stages (`ContinuousMap.Homotopy.trans`):

1. *Associativity*: Mathlib's `Path.Homotopy.transAssoc ηy ηy.symm γ_q` is the reparametrisation
   homotopy `H (t, s) = (ηy.trans (ηy.symm.trans γ_q)) ((1 - t) * s + t * trA s)` where
   `trA = Path.Homotopy.transAssocReparamAux`; collecting it over `q` gives a homotopy on `E_{a₀}`
   (`Path.trans_assoc_reparam` identifies the `t = 1` end with
   `(ηy.trans ηy.symm).trans γ_q`), with `Continuous.if_le`/`continuous_eval` for continuity.
2. *Cancellation plus reparametrisation*: the single explicit family
   `H (t, q, s) = if 2 s ≤ 1 - t then (if 4 s ≤ 1 - t then ηy (clampI (1 - 4 s))
      else (ηy.symm) (clampI (2 * t + 4 * s - 1)))
      else γ_q (clampI ((2 * s - 1 + t) / (1 + t)))`
   interpolates between `(ηy.trans ηy.symm).trans γ_q` (at `t = 0`; compare `Path.trans_apply`) and
   `γ_q` (at `t = 1`); the denominator `1 + t` is bounded below by `1`.  The two pieces agree at the
   junctions `2 s = 1 - t` and `4 s = 1 - t` (value `i a₀` in both cases, since `ηy 0 = i a₀`).
   That the family lands in `E_{a₀}` is immediate: at `s = 0` its value is `i a₀` and at `s = 1` it is
   `γ_q 1 = i q.1.1`.

**`relPathPsi_comp_relPathPhi_homotopic` (the homotopy `ψ ∘ φ ~ id` on `E_a`).**
Same, with `ηy` replaced by `ηy.symm` (and `Path.Homotopic.symm_trans`/`trans_symm` accordingly):
`ψ (φ p) = (p.1.1, ηy.symm.trans (ηy.trans γ_p))`, the cancellation homotopy is the explicit family
`H (t, p, s) = if 2 s ≤ 1 - t then (if 4 s ≤ 1 - t then ηy.symm (clampI (1 - 4 s))
      else ηy (clampI (2 * t + 4 * s - 1)))
      else γ_p (clampI ((2 * s - 1 + t) / (1 + t)))`,
which is the identity at `t = 1` and `ηy.symm.trans (ηy.trans γ_p)` at `t = 0`; the junctions take
the value `i a` (`ηy.symm 1 = ηy 0 = i a`).

**`joined_relPathPhi_basepoint`.**  `φ bp_a` is the point `(a, ηy.trans (Path.refl (i a)))` of
`E_{a₀}`.  Chain two joinedness proofs: the path `t ↦ (η t, s ↦ ηy (clampI (s * t)))` of `E_{a₀}`
joins `bp_{a₀}` (at `t = 0`; note `η 0 = a₀` and `ηy 0 = i a₀`) to `(a, ηy)` (at `t = 1`), and the
homotopy `Path.Homotopic.trans_refl ηy` (a `ContinuousMap.Homotopy` of paths with fixed endpoints)
gives a path in `E_{a₀}` from `(a, ηy)` to `(a, ηy.trans (Path.refl (i a)))`.
-/
