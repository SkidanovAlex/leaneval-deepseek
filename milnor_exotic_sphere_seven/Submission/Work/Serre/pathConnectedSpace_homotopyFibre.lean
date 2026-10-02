import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.StemsB.PiMap
import Submission.Work.RatHurewicz.RelPiPathDefs
import Submission.Work.RatHurewicz.RelPiPathBasepoint
import Submission.Work.Serre.homotopyFibre_pathConnected

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The homotopy fibre of a general map is path connected when the map is injective on `π₀` and
surjective on `π₁`

This file generalises `Work.Serre.homotopyFibre_pathConnected` (the case `i = setIncl A : ↥A → Y`
of a subspace inclusion) to an arbitrary continuous map `i : C(A, Y)`.

The homotopy fibre `E_{a₀} = Work.RatHurewicz.homotopyFibre i a₀` is the space of pairs `(a, γ)`
with `γ` a path in `Y` from `i a₀` to `i a`, with base point `bp = (a₀, const)`.  The hypotheses
are

* `h0` — injectivity of `i` on `π₀` in the usable geometric form: a path in `Y` from `i a₀` to
  `i a` yields (for the *given* `a`) a path in `A` from `a₀` to `a`;
* `hsurj` — surjectivity of `π₁(A,a₀) → π₁(Y,i a₀)`.

The proof is the classical one: given `p = (a, γ) ∈ E_{a₀}`, the path `β⁻¹` supplied by `h0`
(where `β : Path a₀ a`) turns `γ ≫ i β⁻¹` into a loop of `Y` at `i a₀`, which by `hsurj` is the
image of a loop `λ` of `A`; then `i(λ ≫ β) ~ γ`, so `p` is joined to the point
`fibrePointOf i (i(λ ≫ β))`, and the latter is joined to the base point by the path of initial
segments of `λ ≫ β`.

Every definition and lemma of this file is the literal generalisation of the corresponding one in
`Work.Serre.homotopyFibre_pathConnected` (where `setIncl A` occurs as the map and `↥A` as the
domain), so the proofs are transcriptions.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap
open Work.StemsB

namespace Work.Serre

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {A : Type} [TopologicalSpace A]

/-! ## The path and the point attached to a point of the homotopy fibre -/

/-- The path component of a point of the homotopy fibre of `i` at `a₀`, as a `Path`. -/
def fibrePathOf (i : C(A, Y)) {a₀ : A} (p : Work.RatHurewicz.homotopyFibre i a₀) :
    Path (i a₀) (i p.1.1) :=
  ⟨p.1.2.1, p.1.2.2, p.2⟩

/-- The point `(a', γ)` of the homotopy fibre of `i` at `a₀` determined by a path
`γ : Path (i a₀) (i a')`. -/
def fibrePointOf (i : C(A, Y)) {a₀ a' : A} (γ : Path (i a₀) (i a')) :
    Work.RatHurewicz.homotopyFibre i a₀ :=
  ⟨(a', ⟨γ.toContinuousMap, γ.source'⟩), γ.target'⟩

@[simp]
theorem fibrePointOf_fst (i : C(A, Y)) {a₀ a' : A} (γ : Path (i a₀) (i a')) :
    (fibrePointOf i γ).1.1 = a' := rfl

@[simp]
theorem fibrePathOf_fibrePointOf (i : C(A, Y)) {a₀ a' : A} (γ : Path (i a₀) (i a')) :
    fibrePathOf i (fibrePointOf i γ) = γ := rfl

@[simp]
theorem fibrePointOf_fibrePathOf (i : C(A, Y)) {a₀ : A}
    (p : Work.RatHurewicz.homotopyFibre i a₀) :
    fibrePointOf i (fibrePathOf i p) = p := rfl

theorem fibrePointOf_basepoint (i : C(A, Y)) (a₀ : A) :
    fibrePointOf i (Path.refl (i a₀)) = Work.RatHurewicz.homotopyFibreBasepoint i a₀ := rfl

/-! ## Homotopies of paths give paths in the homotopy fibre -/

/-- The path in the homotopy fibre induced by a homotopy of paths with the same endpoints. -/
def homotopyFibrePathOf (i : C(A, Y)) {a₀ a' : A} {γ γ' : Path (i a₀) (i a')}
    (F : γ'.Homotopy γ) : C(I, Work.RatHurewicz.homotopyFibre i a₀) where
  toFun t :=
    ⟨(a', (⟨⟨fun s => F (t, s),
        F.continuous.comp (continuous_const.prodMk continuous_id)⟩,
      by
        show F (t, 0) = i a₀
        exact F.source t⟩ : PathSpace Y (i a₀))),
      by
        show F (t, 1) = i a'
        exact F.target t⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact continuous_const
    · refine Continuous.subtype_mk ?_ _
      refine continuous_of_continuous_uncurry _ ?_
      exact F.continuous

@[simp]
theorem homotopyFibrePathOf_apply_zero (i : C(A, Y)) {a₀ a' : A}
    {γ γ' : Path (i a₀) (i a')} (F : γ'.Homotopy γ) :
    homotopyFibrePathOf i F 0 = fibrePointOf i γ' := by
  refine Subtype.ext (Prod.ext rfl ?_)
  refine Subtype.ext (ContinuousMap.ext fun s => ?_)
  show F (0, s) = γ' s
  exact F.map_zero_left s

@[simp]
theorem homotopyFibrePathOf_apply_one (i : C(A, Y)) {a₀ a' : A}
    {γ γ' : Path (i a₀) (i a')} (F : γ'.Homotopy γ) :
    homotopyFibrePathOf i F 1 = fibrePointOf i γ := by
  refine Subtype.ext (Prod.ext rfl ?_)
  refine Subtype.ext (ContinuousMap.ext fun s => ?_)
  show F (1, s) = γ s
  exact F.map_one_left s

/-- A homotopy of paths with the same endpoints induces a path in the homotopy fibre. -/
theorem joined_fibrePointOf_of_homotopic (i : C(A, Y)) {a₀ a' : A}
    {γ γ' : Path (i a₀) (i a')} (h : γ'.Homotopic γ) :
    Joined (fibrePointOf i γ') (fibrePointOf i γ) := by
  obtain ⟨F⟩ := h
  exact ⟨{ toContinuousMap := homotopyFibrePathOf i F
           source' := homotopyFibrePathOf_apply_zero i F
           target' := homotopyFibrePathOf_apply_one i F }⟩

/-! ## The initial segments of a path of `A`, as a path in the homotopy fibre -/

/-- The initial segment of `η` up to `t`, as a path of `Y` from `i a₀` to `i (η t)`. -/
def segPathOf (i : C(A, Y)) (a₀ a : A) (η : Path a₀ a) (t : I) :
    Path (i a₀) (i (η t)) where
  toContinuousMap :=
    ⟨fun s => (η.map i.continuous) (clampI ((s : ℝ) * (t : ℝ))),
      (η.map i.continuous).continuous.comp
        (continuous_clampI.comp (continuous_subtype_val.mul continuous_const))⟩
  source' := by
    show (η.map i.continuous) (clampI ((0 : ℝ) * (t : ℝ))) = i a₀
    rw [zero_mul, clampI_zero]
    exact (η.map i.continuous).source
  target' := by
    show (η.map i.continuous) (clampI ((1 : ℝ) * (t : ℝ))) = i (η t)
    rw [one_mul, clampI_coe_I, Path.map_coe]
    rfl

/-- The initial segments of `η`, as a continuous map `I → E_{a₀}`. -/
def basepointSegMapOf (i : C(A, Y)) (a₀ a : A) (η : Path a₀ a) :
    C(I, Work.RatHurewicz.homotopyFibre i a₀) where
  toFun t := fibrePointOf i (segPathOf i a₀ a η t)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact η.continuous
    · refine Continuous.subtype_mk ?_ _
      exact continuous_of_continuous_uncurry _
        ((η.map i.continuous).continuous.comp
          (continuous_clampI.comp
            ((continuous_subtype_val.comp continuous_snd).mul
              (continuous_subtype_val.comp continuous_fst))))

@[simp]
theorem basepointSegMapOf_apply_zero (i : C(A, Y)) (a₀ a : A) (η : Path a₀ a) :
    basepointSegMapOf i a₀ a η 0 = Work.RatHurewicz.homotopyFibreBasepoint i a₀ := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact η.source'
  · refine Subtype.ext (ContinuousMap.ext fun s => ?_)
    show (η.map i.continuous) (clampI ((s : ℝ) * (((0 : I)) : ℝ))) = i a₀
    rw [show (((0 : I)) : ℝ) = 0 from rfl, mul_zero, clampI_zero]
    exact (η.map i.continuous).source

@[simp]
theorem basepointSegMapOf_apply_one (i : C(A, Y)) (a₀ a : A) (η : Path a₀ a) :
    basepointSegMapOf i a₀ a η 1 = fibrePointOf i (η.map i.continuous) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact η.target'
  · refine Subtype.ext (ContinuousMap.ext fun s => ?_)
    show (η.map i.continuous) (clampI ((s : ℝ) * (((1 : I)) : ℝ))) = (η.map i.continuous) s
    rw [show (((1 : I)) : ℝ) = 1 from rfl, mul_one, clampI_coe_I]

/-- The path of initial segments, from the base point of `E_{a₀}` to the point determined by
`η.map i`. -/
def basepointPathOf (i : C(A, Y)) (a₀ a : A) (η : Path a₀ a) :
    Path (Work.RatHurewicz.homotopyFibreBasepoint i a₀)
      (fibrePointOf i (η.map i.continuous)) where
  toContinuousMap := basepointSegMapOf i a₀ a η
  source' := basepointSegMapOf_apply_zero i a₀ a η
  target' := basepointSegMapOf_apply_one i a₀ a η

theorem joined_basepoint_fibrePointOf (i : C(A, Y)) (a₀ a : A) (η : Path a₀ a) :
    Joined (Work.RatHurewicz.homotopyFibreBasepoint i a₀)
      (fibrePointOf i (η.map i.continuous)) :=
  ⟨basepointPathOf i a₀ a η⟩

/-! ## Extracting a path of `A` homotopic to a given path of `Y` -/

/-- **If `π₁(A,a₀) → π₁(Y,i a₀)` is surjective and `β` is a path of `A` from `a` to `a₀`, then
every path of `Y` from `i a₀` to `i a` is homotopic rel endpoints to the image of a path of `A`
from `a₀` to `a`.**  (Transcription of `Work.Serre.exists_path_map_homotopic_of_surj`, with the
path `β` supplied by the caller and `setIncl A` replaced by `i`.) -/
theorem exists_path_homotopic_map_of_surj (i : C(A, Y)) (a₀ : A)
    (hsurj : Function.Surjective (πmap i 0 a₀))
    (a : A) (β : Path a a₀) (γ : Path (i a₀) (i a)) :
    ∃ lam : Path a₀ a, (lam.map i.continuous).Homotopic γ := by
  set s : Path (i a) (i a₀) := β.map i.continuous with hs
  obtain ⟨μ, hμ⟩ :=
    hsurj ⟦(genLoopEquivOfUnique (X := Y) (x := i a₀) (Fin 1)).symm (γ.trans s)⟧
  obtain ⟨lam0, rfl⟩ := Quotient.exists_rep μ
  rw [πmap_apply_mk] at hμ
  have hgen : GenLoop.Homotopic (genLoopMap i 1 lam0)
      ((genLoopEquivOfUnique (X := Y) (x := i a₀) (Fin 1)).symm (γ.trans s)) :=
    Quotient.exact hμ
  have hpath := genLoopEquivOfUnique_homotopic hgen
  rw [genLoopEquivOfUnique_genLoopMap] at hpath
  rw [Equiv.apply_symm_apply] at hpath
  refine ⟨(genLoopEquivOfUnique (X := A) (x := a₀) (Fin 1) lam0).trans β.symm, ?_⟩
  have hmap :
      ((genLoopEquivOfUnique (X := A) (x := a₀) (Fin 1) lam0).trans β.symm).map i.continuous =
        ((genLoopEquivOfUnique (X := A) (x := a₀) (Fin 1) lam0).map i.continuous).trans
          (β.symm.map i.continuous) :=
    Path.map_trans _ _ _
  rw [hmap]
  have hsymm : β.symm.map i.continuous = s.symm := by
    rw [hs, Path.map_symm]
  rw [hsymm]
  exact ((hpath.hcomp (Path.Homotopic.refl s.symm)).trans
    ((Path.Homotopic.trans_assoc γ s s.symm).trans
      (((Path.Homotopic.refl γ).hcomp (Path.Homotopic.trans_symm s)).trans
        (Path.Homotopic.trans_refl γ))))

/-! ## The target theorem -/

/-- (in `namespace Work.Serre`) The homotopy fibre of `i : C(A,Y)` at `a₀` is path connected, given
that `i` is injective on `π₀` (in the usable geometric form: a path from `i a₀` to `i a` gives one
from `a₀` to `a`) and surjective on `π₁`.  Generalisation of `Work.Serre.homotopyFibre_pathConnected`
(the `setIncl` case) to an arbitrary continuous map. -/
theorem pathConnectedSpace_homotopyFibre {Y : Type} [TopologicalSpace Y] {A : Type} [TopologicalSpace A]
    (i : C(A, Y)) (a₀ : A)
    (h0 : ∀ a : A, Nonempty (Path (i a₀) (i a)) → Nonempty (Path a₀ a))
    (hsurj : Function.Surjective (Work.StemsB.πmap i 0 a₀)) :
    PathConnectedSpace (Work.RatHurewicz.homotopyFibre i a₀) := by
  have hjoin : ∀ p : Work.RatHurewicz.homotopyFibre i a₀,
      Joined (Work.RatHurewicz.homotopyFibreBasepoint i a₀) p := by
    intro p
    obtain ⟨β'⟩ := h0 p.1.1 ⟨fibrePathOf i p⟩
    obtain ⟨lam, hlam⟩ :=
      exists_path_homotopic_map_of_surj i a₀ hsurj p.1.1 β'.symm (fibrePathOf i p)
    have h1 : Joined (fibrePointOf i (lam.map i.continuous)) p := by
      have h2 := joined_fibrePointOf_of_homotopic i hlam
      rwa [fibrePointOf_fibrePathOf] at h2
    exact (joined_basepoint_fibrePointOf i a₀ p.1.1 lam).trans h1
  exact ⟨⟨Work.RatHurewicz.homotopyFibreBasepoint i a₀⟩,
    fun p q => (hjoin p).symm.trans (hjoin q)⟩

end

end Work.Serre
