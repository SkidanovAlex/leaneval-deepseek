import Mathlib
import Submission.Work.RatHurewicz.Cofibre.ConeContract
import Submission.Work.RatHurewicz.Cofibre.Cover

/-!
# The maps of the cover of the cofibre

See `Submission/Work/RatHurewicz/Cofibre/NOTES.md`.  This file constructs the maps of the
Blakers–Massey cover `(cofibreU ι, cofibreV ι)` of `cofibre ι` (`Cofibre/Cover.lean`): the
collapse of the **half-open** cone `{h < 1/2} ≅ E ∪_F (F × [0,1/2))` onto `E` — the key fact that
makes `cofibreU ι ≃ E` (and not `≃ cofibre ι`, as the *closed* truncated cone would be).
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-! ## The canonical point of the cone -/

/-- The class of `(x,t)` in the cone on `F`. -/
def coneMk (p : F × unitInterval) : Work.Stems.Cone F := Quotient.mk'' p

/-- The relation used in the definition of `coneHeight`. -/
theorem coneHeight_rel (a b : F × unitInterval) (h : (Work.Stems.coneSetoid F).r a b) :
    a.2 = b.2 := by
  rcases h with h | ⟨h1, h2⟩
  · rw [h]
  · rw [h1, h2]

@[simp]
theorem coneHeight_coneMk (p : F × unitInterval) : coneHeight (coneMk p) = p.2 := by
  simp only [coneHeight, coneMk, Quotient.lift_mk]

/-- The half-open cone `{y : Cone F | height y < 1/2}`. -/
def coneLtHalfSet : Set (Work.Stems.Cone F) := {y | coneHeight y < cofibreHalf}

theorem isOpen_coneLtHalfSet : IsOpen (coneLtHalfSet (F := F)) :=
  isOpen_lt continuous_coneHeight continuous_const

/-- The restricted quotient map `{t < 1/2} → {h < 1/2}`, as a continuous map. -/
def coneRestrictMk :
    C(↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)), ↥(coneLtHalfSet (F := F))) where
  toFun p := ⟨coneMk (F := F) p.1, p.2⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_quotient_mk'.comp continuous_subtype_val) _

theorem isQuotientMap_coneRestrictMk :
    Topology.IsQuotientMap (coneRestrictMk (F := F)) :=
  (isQuotientMap_quotient_mk' (s := Work.Stems.coneSetoid F)).restrictPreimage_isOpen
    (isOpen_coneLtHalfSet (F := F))

/-- The projection `(x,t) ↦ x` on the preimage of the half-open cone, followed by `ι`. -/
def coneBaseFun (ι : C(F, E)) :
    C(↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)), E) where
  toFun p := ι p.1.1
  continuous_toFun := ι.continuous.comp (continuous_fst.comp continuous_subtype_val)

theorem coneBaseFun_factors (ι : C(F, E)) :
    Function.FactorsThrough (coneBaseFun ι) (coneRestrictMk (F := F)) := by
  intro a b hab
  have h : coneMk (F := F) a.1 = coneMk (F := F) b.1 := congrArg Subtype.val hab
  have hrel : (Work.Stems.coneSetoid F).r a.1 b.1 := Quotient.eq''.mp h
  show ι a.1.1 = ι b.1.1
  rcases hrel with h' | ⟨h1, h2⟩
  · rw [h']
  · exfalso
    have hlt : coneHeight (coneMk (F := F) a.1) < cofibreHalf := a.2
    rw [coneHeight_coneMk, h1] at hlt
    have hlt' : ((1 : unitInterval) : ℝ) < ((cofibreHalf : unitInterval) : ℝ) := hlt
    norm_num [cofibreHalf] at hlt'

/-- **The collapse of the half-open cone**: `[x,t] ↦ ι x` for `t < 1/2`. -/
def coneBaseLtHalf (ι : C(F, E)) : C(↥(coneLtHalfSet (F := F)), E) :=
  Topology.IsQuotientMap.lift (isQuotientMap_coneRestrictMk (F := F)) (coneBaseFun ι)
    (coneBaseFun_factors ι)

@[simp]
theorem coneBaseLtHalf_coneMk (ι : C(F, E)) (p : F × unitInterval)
    (hp : coneHeight (coneMk p) < cofibreHalf) :
    coneBaseLtHalf ι ⟨coneMk p, hp⟩ = ι p.1 := by
  have hp' : coneHeight (coneMk (F := F) p) < cofibreHalf := by rwa [coneHeight_coneMk]
  have h := Topology.IsQuotientMap.lift_comp (isQuotientMap_coneRestrictMk (F := F))
    (coneBaseFun ι) (coneBaseFun_factors ι)
  have h2 := congrFun (congrArg (fun k : C(↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)), E)
    => ⇑k) h) ⟨p, hp'⟩
  have hpt : (⟨coneMk (F := F) p, hp⟩ : ↥(coneLtHalfSet (F := F))) =
      coneRestrictMk (F := F) ⟨p, hp'⟩ := Subtype.ext rfl
  rw [hpt]
  exact h2


/-! ## The height of the cone contraction

The contraction `coneContractC` of the cone pushes the height towards `1`; this is what
keeps the contraction inside the *open* set `cofibreV ι = {0 < h}`. -/

theorem coneHeight_coneContract (s : unitInterval) (y : Work.Stems.Cone F) :
    coneHeight (coneContractC (s, y)) = pt s (coneHeight y) := by
  induction y using Quotient.inductionOn with
  | h q =>
    show coneHeight (coneContractFun (s, Quotient.mk'' q)) =
      pt s (coneHeight (Quotient.mk'' q))
    rw [coneContractFun, Quotient.liftOn_mk]
    change coneHeight (coneMk (F := F) (q.1, pt s q.2)) =
      pt s (coneHeight (coneMk (F := F) q))
    rw [coneHeight_coneMk, coneHeight_coneMk]

theorem contractPt_pos (s : unitInterval) {t : unitInterval} (ht : (0 : unitInterval) < t) :
    (0 : unitInterval) < pt s t := by
  rw [← Subtype.coe_lt_coe] at ht ⊢
  have hval : (0 : ℝ) < (1 - (s : ℝ)) * (t : ℝ) + (s : ℝ) := by
    rcases lt_or_eq_of_le (s.2.1) with h | h
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr s.2.2) ht.le) h
    · rw [← h]
      simpa using ht
  simpa [pt] using hval

theorem coneHeight_concContract_pos (s : unitInterval) (y : Work.Stems.Cone F)
    (hy : (0 : unitInterval) < coneHeight y) :
    (0 : unitInterval) < coneHeight (coneContractC (s, y)) := by
  rw [coneHeight_coneContract]
  exact contractPt_pos s hy

end

end Work.RatHurewicz
