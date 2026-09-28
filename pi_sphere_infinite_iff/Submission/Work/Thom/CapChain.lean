import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.CapGeomDefs
import Submission.Work.Thom.CapScale.lastC_scalePt_bounds
import Submission.Work.Thom.CapScale.scalePt_one
import Submission.Work.Thom.CapScale.lastC_scalePt_half_lt
import Submission.Work.Thom.CapScale.continuous_scalePt_comp
import Submission.Work.Thom.CapScale.eqProj_eq_self
import Submission.Work.Cohomology.Endgame.relComplexMapExcision
import Submission.Work.Thom.relCohHomeomorph
import Submission.Work.Thom.relCohomology_prod_contractible
import Submission.Work.Thom.CapBall.stripBig_comp_capBig
import Submission.Work.Thom.CapContract.contractibleSpace_flGt
import Submission.Work.Thom.CapGlue.isIso_CohMap_of_homotopic_inv
import Submission.Work.Thom.CapGlue.isIso_homologyMap_dualChainMap_prodMap
import Submission.Work.Thom.CapGlue.isIso_relComplexMap_homeomorph

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

/-!
# The chain of isomorphisms proving `Work.Thom.capRelCohIso`

The map of pairs of the statement,

`(b,w) ↦ (b, capMap n w) : (B × Dⁿ, B × Sⁿ⁻¹) → (B × Sⁿ, B × {last ≤ 1/2})`,

is factored as a composite of maps of pairs whose induced maps on relative cohomology are all
isomorphisms:

* `(a)` the inclusion `(B × Sⁿ, B × {last < 1/2}) → (B × Sⁿ, B × {last ≤ 1/2})`;
* `(b)` the excision iso `(B × Sⁿ, B × {last < 1/2}) → (B × {last > -1/2}, B × {-1/2 < last < 1/2})`,
  obtained by excising the closed south cap `{last ≤ -1/2}` (which lies in the interior of
  `{last < 1/2}`), followed by the canonical identification of a product-subtype with the product;
* `(c)` the cap map `(b,w) ↦ (b, capMap n w)` from `(B × Dⁿ, B × Sⁿ⁻¹)` to
  `(B × {last > -1/2}, B × {-1/2 < last < 1/2})`.
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

/-! ## Continuity of the scaling family -/

theorem continuous_scaleV_pair (n : ℕ) {α : Type} [TopologicalSpace α] (lam : α → ℝ)
    (hlam : Continuous lam) (u : α → EuclideanSpace ℝ (Fin (n + 1))) (hu : Continuous u) :
    Continuous fun a => scaleV n (lam a) (u a) := by
  have h1 : Continuous fun a => Work.Morse.strip (u a) :=
    (Work.Cohomology.continuous_strip n).comp hu
  have h2 : Continuous fun a => lam a * lastC n (u a) :=
    hlam.mul ((continuous_lastC n).comp hu)
  have h3 : Continuous fun a => Work.Morse.snocLp (Work.Morse.strip (u a)) (lam a * lastC n (u a)) :=
    Work.Morse.continuous_snocLp.comp (h1.prodMk h2)
  simpa [scaleV] using h3

theorem continuous_scalePt_const (n : ℕ) (lam : ℝ) (S : Set (MSph (n + 1)))
    (hS : ∀ v ∈ S, scaleV n lam v.1 ≠ 0) :
    Continuous fun v : ↥S => scalePt n lam v.1 (hS v.1 v.2) := by
  have hvec : Continuous fun v : ↥S => scaleV n lam v.1.1 :=
    continuous_scaleV_pair n (fun _ => lam) continuous_const
      (fun v : ↥S => v.1.1) (continuous_subtype_val.comp continuous_subtype_val)
  have hne : ∀ v : ↥S, ‖scaleV n lam v.1.1‖ ≠ 0 :=
    fun v => norm_ne_zero_iff.mpr (hS v.1 v.2)
  have hmain : Continuous fun v : ↥S => ‖scaleV n lam v.1.1‖⁻¹ • scaleV n lam v.1.1 :=
    (hvec.norm.inv₀ hne).smul hvec
  exact hmain.subtype_mk (fun v => norm_inv_smul n _ (hS v.1 v.2))

/-! ## The bands of the sphere -/

/-- The closed band `{v ∈ S^{n+1} | lastC ≤ 1/2}` of the sphere. -/
def fiberLe (n : ℕ) : Set (MSph (n + 1)) := {v | v.1 ∈ sphLe n (1 / 2)}

/-- The open band `{v ∈ S^{n+1} | lastC < 1/2}` of the sphere. -/
def fiberLt (n : ℕ) : Set (MSph (n + 1)) := {v | v.1 ∈ sphLt n (1 / 2)}

theorem mem_fiberLe (n : ℕ) (v : MSph (n + 1)) :
    v ∈ fiberLe n ↔ lastC n v.1 ≤ 1 / 2 :=
  ⟨fun h => h.2, fun h => ⟨v.2, h⟩⟩

theorem mem_fiberLt (n : ℕ) (v : MSph (n + 1)) :
    v ∈ fiberLt n ↔ lastC n v.1 < 1 / 2 :=
  ⟨fun h => h.2, fun h => ⟨v.2, h⟩⟩

/-- The scaling `Φ_λ` as a map on a fibre band where the scaling vector does not vanish. -/
def scaleCM (n : ℕ) (lam : ℝ) (S : Set (MSph (n + 1)))
    (hS : ∀ v ∈ S, scaleV n lam v.1 ≠ 0) : C(↥S, MSph (n + 1)) :=
  ⟨fun v => scalePt n lam v.1 (hS v.1 v.2), continuous_scalePt_const n lam S hS⟩

theorem scaleCM_apply (n : ℕ) (lam : ℝ) (S : Set (MSph (n + 1)))
    (hS : ∀ v ∈ S, scaleV n lam v.1 ≠ 0) (v : ↥S) :
    scaleCM n lam S hS v = scalePt n lam v.1 (hS v.1 v.2) := rfl

/-- The parametrised scaling `(t, v) ↦ Φ_{(1+t)/2}(v)`, used for the homotopies of the band. -/
def scaleParamCM (n : ℕ) (S : Set (MSph (n + 1)))
    (hS : ∀ (t : unitInterval) (v : ↥S), scaleV n ((1 + (t : ℝ)) / 2) v.1.1 ≠ 0) :
    C(unitInterval × ↥S, MSph (n + 1)) :=
  ⟨fun p => scalePt n ((1 + (p.1 : ℝ)) / 2) p.2.1 (hS p.1 p.2),
    CapScale.continuous_scalePt_comp n (α := unitInterval) (fun t : unitInterval => (1 + (t : ℝ)) / 2)
      (by fun_prop) S hS⟩

theorem scaleParamCM_apply (n : ℕ) (S : Set (MSph (n + 1)))
    (hS : ∀ (t : unitInterval) (v : ↥S), scaleV n ((1 + (t : ℝ)) / 2) v.1.1 ≠ 0)
    (p : unitInterval × ↥S) :
    scaleParamCM n S hS p = scalePt n ((1 + (p.1 : ℝ)) / 2) p.2.1 (hS p.1 p.2) := rfl

theorem scaleV_ne_zero_pos_band (n : ℕ) (t : unitInterval) (v : ↥(fiberLe n)) :
    scaleV n ((1 + (t : ℝ)) / 2) v.1.1 ≠ 0 :=
  scaleV_ne_zero_of_pos n _ (by
    have h1 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    linarith) v.1

/-- The scaling `Φ_λ` (`0 ≤ λ ≤ 1`) preserves the closed band `{last ≤ 1/2}`. -/
theorem lastC_scalePt_mem_Iic (n : ℕ) (lam : ℝ) (v : MSph (n + 1)) (h : scaleV n lam v.1 ≠ 0)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (ht : lastC n v.1 ≤ 1 / 2) :
    lastC n (scalePt n lam v h).1 ≤ 1 / 2 := by
  rcases le_total (0 : ℝ) (lastC n v.1) with hpos | hneg
  · exact le_trans ((CapScale.lastC_scalePt_bounds n lam v h h0 h1).1 hpos).2 ht
  · exact le_trans ((CapScale.lastC_scalePt_bounds n lam v h h0 h1).2 hneg).2 (by norm_num)

/-- The scaling `Φ_λ` (`0 ≤ λ ≤ 1`) preserves the open band `{last < 1/2}`. -/
theorem lastC_scalePt_mem_Iio (n : ℕ) (lam : ℝ) (v : MSph (n + 1)) (h : scaleV n lam v.1 ≠ 0)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (ht : lastC n v.1 < 1 / 2) :
    lastC n (scalePt n lam v h).1 < 1 / 2 := by
  rcases le_total (0 : ℝ) (lastC n v.1) with hpos | hneg
  · exact lt_of_le_of_lt ((CapScale.lastC_scalePt_bounds n lam v h h0 h1).1 hpos).2 ht
  · linarith [((CapScale.lastC_scalePt_bounds n lam v h h0 h1).2 hneg).2]

/-- `Φ_{1/2}` maps the closed band `{last ≤ 1/2}` into the open band `{last < 1/2}`. -/
theorem lastC_scalePt_half_mem_Iio (n : ℕ) (v : MSph (n + 1)) (h : scaleV n (1 / 2) v.1 ≠ 0)
    (ht : lastC n v.1 ≤ 1 / 2) : lastC n (scalePt n (1 / 2) v h).1 < 1 / 2 := by
  rcases le_total (0 : ℝ) (lastC n v.1) with hpos | hneg
  · exact CapScale.lastC_scalePt_half_lt n v h hpos ht
  · linarith [((CapScale.lastC_scalePt_bounds n (1 / 2) v h (by norm_num) (by norm_num)).2 hneg).2]

/-! ## The pair `(B × Sⁿ, B × band)` -/

variable (B : Type) [TopologicalSpace B] (n : ℕ)

/-- The closed lower band `{last ≤ 1/2}` of the sphere bundle; the `A` of the source pair of the
statement (`mLower n` is definitionally `sphLe n (1/2)`). -/
def ppLe : Set (B × MSph (n + 1)) := {p | p.2.1 ∈ sphLe n (1 / 2)}

/-- The open lower band `{last < 1/2}` of the sphere bundle. -/
def ppLt : Set (B × MSph (n + 1)) := {p | p.2.1 ∈ sphLt n (1 / 2)}

theorem mem_ppLe {p : B × MSph (n + 1)} : p ∈ ppLe B n ↔ lastC n p.2.1 ≤ 1 / 2 :=
  ⟨fun h => h.2, fun h => ⟨p.2.2, h⟩⟩

theorem mem_ppLt {p : B × MSph (n + 1)} : p ∈ ppLt B n ↔ lastC n p.2.1 < 1 / 2 :=
  ⟨fun h => h.2, fun h => ⟨p.2.2, h⟩⟩

/-- Projection of the closed band onto the fibre band. -/
def toFiberLe : C(↥(ppLe B n), ↥(fiberLe n)) :=
  ⟨fun p => ⟨p.1.2, p.2⟩,
    Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _⟩

/-- Projection of the open band onto the fibre band. -/
def toFiberLt : C(↥(ppLt B n), ↥(fiberLt n)) :=
  ⟨fun p => ⟨p.1.2, p.2⟩,
    Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _⟩

@[simp] theorem toFiberLe_apply (p : ↥(ppLe B n)) : ((toFiberLe B n p : ↥(fiberLe n)) : MSph (n+1)) = p.1.2 := rfl

@[simp] theorem toFiberLt_apply (p : ↥(ppLt B n)) : ((toFiberLt B n p : ↥(fiberLt n)) : MSph (n+1)) = p.1.2 := rfl

/-- The inclusion of the open band into the closed band, as a map of the subtypes. -/
def bandIncl : C(↥(ppLt B n), ↥(ppLe B n)) :=
  ⟨fun p => ⟨p.1, ⟨p.2.1, le_of_lt p.2.2⟩⟩,
    Continuous.subtype_mk continuous_subtype_val _⟩

@[simp] theorem bandIncl_apply (p : ↥(ppLt B n)) : (bandIncl B n p).1 = p.1 := rfl

/-- The scaling by `1/2` retracts the closed band into the open band. -/
def bandScale : C(↥(ppLe B n), ↥(ppLt B n)) :=
  ⟨fun p =>
    let hne : scaleV n (1 / 2) p.1.2 ≠ 0 :=
      scaleV_ne_zero_of_pos n (1 / 2) (by norm_num) p.1.2
    ⟨(p.1.1, scalePt n (1 / 2) p.1.2 hne),
      ⟨(scalePt n (1 / 2) p.1.2 hne).2,
        lastC_scalePt_half_mem_Iio n p.1.2 hne ((mem_ppLe B n).mp p.2)⟩⟩,
    Continuous.subtype_mk
      (Continuous.prodMk (continuous_fst.comp continuous_subtype_val)
        ((continuous_scalePt_const n (1 / 2) (fiberLe n)
          (fun v _ => scaleV_ne_zero_of_pos n (1 / 2) (by norm_num) v)).comp
            (toFiberLe B n).continuous)) _⟩

@[simp] theorem bandScale_fst (p : ↥(ppLe B n)) : (bandScale B n p).1.1 = p.1.1 := rfl

theorem scaleV_ne_zero_pos_fiberLt (n : ℕ) (t : unitInterval) (v : ↥(fiberLt n)) :
    scaleV n ((1 + (t : ℝ)) / 2) v.1.1 ≠ 0 :=
  scaleV_ne_zero_of_pos n _ (by
    have h1 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    linarith) v.1

/-- The parametrised scaling on the closed fibre band. -/
def fiberParamLe : C(unitInterval × ↥(fiberLe n), MSph (n + 1)) :=
  scaleParamCM n (fiberLe n) (scaleV_ne_zero_pos_band n)

/-- The parametrised scaling on the open fibre band. -/
def fiberParamLt : C(unitInterval × ↥(fiberLt n), MSph (n + 1)) :=
  scaleParamCM n (fiberLt n) (scaleV_ne_zero_pos_fiberLt n)

theorem lastC_fiberParamLe (n : ℕ) (q : unitInterval × ↥(fiberLe n))
    (hq : lastC n q.2.1.1 ≤ 1 / 2) : lastC n (fiberParamLe n q).1 ≤ 1 / 2 :=
  lastC_scalePt_mem_Iic n ((1 + (q.1 : ℝ)) / 2) q.2.1 (scaleV_ne_zero_pos_band n q.1 q.2)
    (by have h1 : (0 : ℝ) ≤ (q.1 : ℝ) := q.1.2.1; linarith)
    (by have h1 : (q.1 : ℝ) ≤ 1 := q.1.2.2; linarith) hq

theorem lastC_fiberParamLt (n : ℕ) (q : unitInterval × ↥(fiberLt n))
    (hq : lastC n q.2.1.1 < 1 / 2) : lastC n (fiberParamLt n q).1 < 1 / 2 :=
  lastC_scalePt_mem_Iio n ((1 + (q.1 : ℝ)) / 2) q.2.1 (scaleV_ne_zero_pos_fiberLt n q.1 q.2)
    (by have h1 : (0 : ℝ) ≤ (q.1 : ℝ) := q.1.2.1; linarith)
    (by have h1 : (q.1 : ℝ) ≤ 1 := q.1.2.2; linarith) hq

/-- The projection `I × {last ≤ 1/2} → I × fibre`. -/
def toFiberParamLe : C(unitInterval × ↥(ppLe B n), unitInterval × ↥(fiberLe n)) :=
  ⟨fun p => (p.1, toFiberLe B n p.2),
    Continuous.prodMk continuous_fst ((toFiberLe B n).continuous.comp continuous_snd)⟩

/-- The projection `I × {last < 1/2} → I × fibre`. -/
def toFiberParamLt : C(unitInterval × ↥(ppLt B n), unitInterval × ↥(fiberLt n)) :=
  ⟨fun p => (p.1, toFiberLt B n p.2),
    Continuous.prodMk continuous_fst ((toFiberLt B n).continuous.comp continuous_snd)⟩

/-- The underlying map of the band homotopy, on the closed band. -/
def bandMapLe : C(unitInterval × ↥(ppLe B n), B × MSph (n + 1)) :=
  ContinuousMap.prodMk
    ⟨fun p : unitInterval × ↥(ppLe B n) => p.2.1.1, by fun_prop⟩
    ((fiberParamLe n).comp (toFiberParamLe B n))

/-- The underlying map of the band homotopy, on the open band. -/
def bandMapLt : C(unitInterval × ↥(ppLt B n), B × MSph (n + 1)) :=
  ContinuousMap.prodMk
    ⟨fun p : unitInterval × ↥(ppLt B n) => p.2.1.1, by fun_prop⟩
    ((fiberParamLt n).comp (toFiberParamLt B n))

@[simp] theorem bandMapLe_apply (p : unitInterval × ↥(ppLe B n)) :
    (bandMapLe B n p).2 = fiberParamLe n (p.1, toFiberLe B n p.2) := rfl

@[simp] theorem bandMapLt_apply (p : unitInterval × ↥(ppLt B n)) :
    (bandMapLt B n p).2 = fiberParamLt n (p.1, toFiberLt B n p.2) := rfl

/-- Member of the closed band scaled by `Φ_{(1+t)/2}`. -/
def bandHomLe : C(unitInterval × ↥(ppLe B n), ↥(ppLe B n)) :=
  ⟨fun p => ⟨bandMapLe B n p,
      ⟨(bandMapLe B n p).2.2,
        lastC_fiberParamLe n (p.1, toFiberLe B n p.2) ((mem_ppLe B n).mp p.2.2)⟩⟩,
    (bandMapLe B n).continuous.subtype_mk _⟩

/-- Member of the open band scaled by `Φ_{(1+t)/2}`. -/
def bandHomLt : C(unitInterval × ↥(ppLt B n), ↥(ppLt B n)) :=
  ⟨fun p => ⟨bandMapLt B n p,
      ⟨(bandMapLt B n p).2.2,
        lastC_fiberParamLt n (p.1, toFiberLt B n p.2) ((mem_ppLt B n).mp p.2.2)⟩⟩,
    (bandMapLt B n).continuous.subtype_mk _⟩


/-! ## The endpoint computations of the band homotopies -/

theorem fiberParamLe_one (q : unitInterval × ↥(fiberLe n)) (hq : q.1 = 1) :
    fiberParamLe n q = q.2.1 := by
  apply Subtype.ext
  show ‖scaleV n ((1 + (q.1 : ℝ)) / 2) q.2.1.1‖⁻¹ • scaleV n ((1 + (q.1 : ℝ)) / 2) q.2.1.1
    = q.2.1.1
  have h1 : (1 + (q.1 : ℝ)) / 2 = 1 := by
    rw [congrArg (fun t : unitInterval => (t : ℝ)) hq]
    norm_num
  rw [h1]
  have hv : scaleV n 1 q.2.1.1 = q.2.1.1 := by
    rw [scaleV, one_mul]
    exact Work.Morse.snocLp_strip q.2.1.1
  rw [hv, show ‖q.2.1.1‖ = 1 from q.2.1.2]
  simp

theorem fiberParamLt_one (q : unitInterval × ↥(fiberLt n)) (hq : q.1 = 1) :
    fiberParamLt n q = q.2.1 := by
  apply Subtype.ext
  show ‖scaleV n ((1 + (q.1 : ℝ)) / 2) q.2.1.1‖⁻¹ • scaleV n ((1 + (q.1 : ℝ)) / 2) q.2.1.1
    = q.2.1.1
  have h1 : (1 + (q.1 : ℝ)) / 2 = 1 := by
    rw [congrArg (fun t : unitInterval => (t : ℝ)) hq]
    norm_num
  rw [h1]
  have hv : scaleV n 1 q.2.1.1 = q.2.1.1 := by
    rw [scaleV, one_mul]
    exact Work.Morse.snocLp_strip q.2.1.1
  rw [hv, show ‖q.2.1.1‖ = 1 from q.2.1.2]
  simp

theorem bandHomLe_one (p : ↥(ppLe B n)) : bandHomLe B n (1, p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    show (fiberParamLe n ((1 : unitInterval), toFiberLe B n p)).1 = p.1.2.1
    exact congrArg Subtype.val (fiberParamLe_one n _ rfl)

theorem bandHomLt_one (p : ↥(ppLt B n)) : bandHomLt B n (1, p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    show (fiberParamLt n ((1 : unitInterval), toFiberLt B n p)).1 = p.1.2.1
    exact congrArg Subtype.val (fiberParamLt_one n _ rfl)

theorem bandHomLe_zero (p : ↥(ppLe B n)) :
    bandHomLe B n (0, p) = bandIncl B n (bandScale B n p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    show ‖scaleV n ((1 + (((0 : unitInterval) : ℝ))) / 2) p.1.2.1‖⁻¹ •
        scaleV n ((1 + ((0 : unitInterval) : ℝ)) / 2) p.1.2.1
      = ‖scaleV n (1 / 2) p.1.2.1‖⁻¹ • scaleV n (1 / 2) p.1.2.1
    norm_num

theorem bandHomLt_zero (p : ↥(ppLt B n)) :
    bandHomLt B n (0, p) = bandScale B n (bandIncl B n p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    show ‖scaleV n ((1 + (((0 : unitInterval) : ℝ))) / 2) p.1.2.1‖⁻¹ •
        scaleV n ((1 + ((0 : unitInterval) : ℝ)) / 2) p.1.2.1
      = ‖scaleV n (1 / 2) p.1.2.1‖⁻¹ • scaleV n (1 / 2) p.1.2.1
    norm_num

/-- The homotopy from `bandIncl ∘ bandScale` to the identity of the closed band. -/
def bandHomotopyLe : ContinuousMap.Homotopy ((bandIncl B n).comp (bandScale B n))
    (ContinuousMap.id (↥(ppLe B n))) :=
  ⟨bandHomLe B n, bandHomLe_zero B n, bandHomLe_one B n⟩

/-- The homotopy from `bandScale ∘ bandIncl` to the identity of the open band. -/
def bandHomotopyLt : ContinuousMap.Homotopy ((bandScale B n).comp (bandIncl B n))
    (ContinuousMap.id (↥(ppLt B n))) :=
  ⟨bandHomLt B n, bandHomLt_zero B n, bandHomLt_one B n⟩

/-- The inclusion of the open band into the closed band induces an isomorphism on the cohomology of
the subtypes (the two are homotopy equivalent by the scaling). -/
theorem isIso_bandIncl (m : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℤ
      (TopCat.of ↥(ppLt B n)) (TopCat.of ↥(ppLe B n)) (TopCat.ofHom (bandIncl B n))) m) :=
  Work.Cohomology.homotopyEquiv ℤ (TopCat.of ↥(ppLt B n)) (TopCat.of ↥(ppLe B n))
    (TopCat.ofHom (bandIncl B n)) (TopCat.ofHom (bandScale B n))
    (bandHomotopyLt B n) (bandHomotopyLe B n) m

theorem isOpen_ppLt : IsOpen (ppLt B n) := by
  have h : ppLt B n = {p : B × MSph (n + 1) | lastC n p.2.1 < 1 / 2} := by
    ext p
    exact mem_ppLt B n
  rw [h]
  exact isOpen_lt (by unfold lastC; fun_prop) continuous_const

/-- The membership proof of the inclusion of pairs `(ppLt) → (ppLe)`. -/
theorem ppLt_subset_ppLe {x : B × MSph (n + 1)} (hx : x ∈ ppLt B n) : x ∈ ppLe B n :=
  ⟨hx.1, le_of_lt hx.2⟩

/-- **Step (a)**: the inclusion of pairs
`(B × Sⁿ, B × {last < 1/2}) → (B × Sⁿ, B × {last ≤ 1/2})` induces an isomorphism on relative
cohomology (the two `A`-parts are homotopy equivalent by the scaling `Φ_{1/2}`). -/
theorem isIso_relCohMap_bandIncl (m : ℕ) :
    CategoryTheory.IsIso (relCohMap (ContinuousMap.id (B × MSph (n + 1))) (ppLt B n) (ppLe B n)
      (fun x hx => ppLt_subset_ppLe B n hx) ℤ m) := by
  have hX : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℤ
      (TopCat.of (B × MSph (n + 1))) (TopCat.of (B × MSph (n + 1)))
      (𝟙 (TopCat.of (B × MSph (n + 1))))) k) := by
    intro k
    rw [Work.Cohomology.dualChainMap_id, HomologicalComplex.homologyMap_id]
    infer_instance
  have hA : ∀ k, CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℤ
      (TopCat.of ↥(ppLt B n)) (TopCat.of ↥(ppLe B n))
      (Work.Cohomology.relMapSub (ppLt B n) (ppLe B n)
        (𝟙 (TopCat.of (B × MSph (n + 1)))) (fun x hx => ppLt_subset_ppLe B n hx))) k) := by
    intro k
    have heq : Work.Cohomology.relMapSub (ppLt B n) (ppLe B n)
        (𝟙 (TopCat.of (B × MSph (n + 1)))) (fun x hx => ppLt_subset_ppLe B n hx)
        = TopCat.ofHom (bandIncl B n) := by
      apply TopCat.ext
      intro a
      rfl
    rw [heq]
    exact isIso_bandIncl B n k
  exact isIso_homologyMap_relComplexMap (X₁ := TopCat.of (B × MSph (n + 1)))
    (X₂ := TopCat.of (B × MSph (n + 1))) (ppLt B n) (ppLe B n)
    (𝟙 (TopCat.of (B × MSph (n + 1)))) (fun x hx => ppLt_subset_ppLe B n hx) ℤ hX hA m


/-! ## Step (b): excising the south cap -/

/-- The closed south cap `{last ≤ -1/2}` of the sphere bundle, the set that is excised. -/
def Zcap : Set (B × MSph (n + 1)) := {p | p.2.1 ∈ sphLe n (-(1 / 2))}

/-- The complement of the south cap is the open north cap. -/
theorem not_mem_Zcap_iff (p : B × MSph (n + 1)) :
    p ∉ Zcap B n ↔ p.2.1 ∈ sphGt n (-(1 / 2)) := by
  constructor
  · intro h
    refine ⟨p.2.2, ?_⟩
    by_contra hle
    exact h ⟨p.2.2, le_of_not_gt hle⟩
  · intro h hmem
    exact absurd hmem.2 (not_le.mpr h.2)

/-- The open band of the product with the open north cap. -/
def Qset : Set (B × ↥(flGt n (-(1 / 2)))) := {p | p.2.1.1 ∈ sphLt n (1 / 2)}

theorem mem_Qset {p : B × ↥(flGt n (-(1 / 2)))} :
    p ∈ Qset B n ↔ lastC n p.2.1.1 < 1 / 2 :=
  ⟨fun h => h.2, fun h => ⟨p.2.1.2, h⟩⟩

/-- The open north cap of a sphere point is an open north cap of the ambient point. -/
theorem isClosed_Zcap : IsClosed (Zcap B n) := by
  have h : Zcap B n = {p : B × MSph (n + 1) | lastC n p.2.1 ≤ -(1 / 2)} := by
    ext p
    constructor
    · intro hp; exact hp.2
    · intro hp; exact ⟨p.2.2, hp⟩
  rw [h]
  exact isClosed_le (by unfold lastC; fun_prop) continuous_const

theorem mem_sphGt_of_mem_flGt (v : ↥(flGt n (-(1 / 2)))) :
    v.1.1 ∈ sphGt n (-(1 / 2)) := ⟨v.1.2, v.2⟩

/-- The identification of the complement of the excised south cap with the product with the open
north cap. -/
def excHomeo : (B × ↥(flGt n (-(1 / 2)))) ≃ₜ ↥{p : B × MSph (n + 1) | p ∉ Zcap B n} where
  toFun p := ⟨(p.1, p.2.1),
    (not_mem_Zcap_iff B n (p.1, p.2.1)).mpr (mem_sphGt_of_mem_flGt n p.2)⟩
  invFun p := (p.1.1, ⟨p.1.2, ((not_mem_Zcap_iff B n p.1).mp p.2).2⟩)
  left_inv p := rfl
  right_inv p := rfl
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · fun_prop
    · fun_prop
  continuous_invFun := by
    refine Continuous.prodMk (by fun_prop) (Continuous.subtype_mk (by fun_prop) ?_)
    intro p
    exact ((not_mem_Zcap_iff B n p.1).mp p.2).2

/-- The inclusion of the complement of the excised cap, as a continuous map. -/
def subInclC : C(↥{p : B × MSph (n + 1) | p ∉ Zcap B n}, B × MSph (n + 1)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The map of pairs realizing step (b): the complement of the excised cap, projected back to
`B × Sⁿ`. -/
def excMap : C(B × ↥(flGt n (-(1 / 2))), B × MSph (n + 1)) :=
  ⟨fun p => (p.1, p.2.1), by fun_prop⟩

/-- The pair condition of the map of step (b). -/
theorem excMap_mem : ∀ q ∈ Qset B n, excMap B n q ∈ ppLt B n := by
  intro q hq
  rw [excMap]
  exact ⟨q.2.1.2, hq.2⟩

/-- **Step (b)**: the excision of the south cap, followed by the identification of the
product-subtype with the product, induces an isomorphism on relative cohomology. -/
theorem isIso_relCohMap_excision (m : ℕ) :
    CategoryTheory.IsIso (relCohMap (excMap B n) (Qset B n) (ppLt B n)
      (fun x hx => by
        rw [excMap]
        exact ⟨x.2.1.2, hx.2⟩) ℤ m) := by
  let X : TopCat := TopCat.of (B × MSph (n + 1))
  let S : Set X := {p : B × MSph (n + 1) | p ∉ Zcap B n}
  let A : Set X := ppLt B n
  have hZ : closure (Zcap B n) ⊆ interior (ppLt B n) := by
    have hsub : Zcap B n ⊆ ppLt B n := fun p hp => ⟨hp.1, lt_of_le_of_lt hp.2 (by norm_num)⟩
    calc closure (Zcap B n) = Zcap B n := (isClosed_Zcap B n).closure_eq
      _ ⊆ ppLt B n := hsub
      _ = interior (ppLt B n) := (IsOpen.interior_eq (isOpen_ppLt B n)).symm
  -- the excision isomorphism
  haveI h1 : CategoryTheory.IsIso (relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, ↑X))
      ((Subtype.val : ↥S → ↑X) ⁻¹' ppLt B n) (ppLt B n)
      (fun x hx => hx) ℤ m) :=
    Work.Cohomology.Endgame.relComplexMapExcision X A (Zcap B n) hZ m
  -- the identification of the product-subtype with the product
  haveI h2 : CategoryTheory.IsIso (relCohMap
      (excHomeo B n : C(B × ↥(flGt n (-(1 / 2))), ↥S)) (Qset B n)
      ((Subtype.val : ↥S → B × MSph (n + 1)) ⁻¹' ppLt B n)
      (fun x hx => by
        have hq : lastC n x.2.1.1 < 1 / 2 := (mem_Qset B n).mp hx
        exact ⟨x.2.1.2, hq⟩) ℤ m) :=
    CapGlue.isIso_relComplexMap_homeomorph (Qset B n)
      ((Subtype.val : ↥S → B × MSph (n + 1)) ⁻¹' ppLt B n) (excHomeo B n)
      (by
        intro x
        constructor
        · intro hx
          have hq : lastC n x.2.1.1 < 1 / 2 := (mem_Qset B n).mp hx
          exact ⟨x.2.1.2, hq⟩
        · intro hx
          exact (mem_Qset B n).mpr hx.2) ℤ m
  -- the composite is the map of pairs of step (b)
  have hcomp := relCohMap_comp' (A := Qset B n)
    (B := (Subtype.val : ↥S → B × MSph (n + 1)) ⁻¹' ppLt B n) (C := ppLt B n)
    (f := (excHomeo B n : C(B × ↥(flGt n (-(1 / 2))), ↥S)))
    (g := (⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, B × MSph (n + 1))))
    (hf := (fun x hx => by
        have hq : lastC n x.2.1.1 < 1 / 2 := (mem_Qset B n).mp hx
        exact ⟨x.2.1.2, hq⟩))
    (hg := (fun x hx => hx))
    (hgf := (fun x hx => by
        have hq : lastC n x.2.1.1 < 1 / 2 := (mem_Qset B n).mp hx
        exact ⟨x.2.1.2, hq⟩)) ℤ m
  have hmap : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, B × MSph (n + 1))).comp
      (excHomeo B n : C(B × ↥(flGt n (-(1 / 2))), ↥S)) = excMap B n := by
    apply ContinuousMap.ext
    intro p
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl
  haveI : CategoryTheory.IsIso (relCohMap
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥S, B × MSph (n + 1))).comp
        (excHomeo B n : C(B × ↥(flGt n (-(1 / 2))), ↥S)))
      (Qset B n) (ppLt B n)
      (fun x hx => by
        have hq : lastC n x.2.1.1 < 1 / 2 := (mem_Qset B n).mp hx
        exact ⟨x.2.1.2, hq⟩) ℤ m) := by
    rw [← hcomp]
    infer_instance
  rw [relCohMap_congr' (Qset B n) (ppLt B n) hmap _ _ ℤ m] at this
  exact this


/-! ## Step (c): the cap map -/

/-- The `A`-set of the source pair of the statement: the boundary sphere inside the ball. -/
def Abound : Set (B × MBall n) := {q | q.2.1 ∈ mSph n}

/-- The fibre of the target pair: the open middle band `{-1/2 < last < 1/2}`. -/
def fiberQ : Set (MSph (n + 1)) := {v | -(1 / 2) < lastC n v.1 ∧ lastC n v.1 < 1 / 2}

theorem mem_fiberQ {v : MSph (n + 1)} :
    v ∈ fiberQ n ↔ -(1 / 2) < lastC n v.1 ∧ lastC n v.1 < 1 / 2 := Iff.rfl

theorem abs_lastC_lt_one_of_mem_fiberQ {v : MSph (n + 1)} (hv : v ∈ fiberQ n) :
    |lastC n v.1| < 1 := by
  rw [abs_lt]
  exact ⟨by linarith [hv.1], by linarith [hv.2]⟩

/-- The scaling `Φ_λ` (`0 ≤ λ ≤ 1`) preserves the open middle band `{-1/2 < last < 1/2}`. -/
theorem lastC_scalePt_mem_Ioo (n : ℕ) (lam : ℝ) (v : MSph (n + 1)) (h : scaleV n lam v.1 ≠ 0)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (ht1 : -(1 / 2) < lastC n v.1) (ht2 : lastC n v.1 < 1 / 2) :
    -(1 / 2) < lastC n (scalePt n lam v h).1 ∧ lastC n (scalePt n lam v h).1 < 1 / 2 := by
  rcases le_total (0 : ℝ) (lastC n v.1) with hpos | hneg
  · have hb := (CapScale.lastC_scalePt_bounds n lam v h h0 h1).1 hpos
    exact ⟨lt_of_lt_of_le (by norm_num) hb.1, lt_of_le_of_lt hb.2 ht2⟩
  · have hb := (CapScale.lastC_scalePt_bounds n lam v h h0 h1).2 hneg
    exact ⟨lt_of_lt_of_le ht1 hb.1, lt_of_le_of_lt hb.2 (by norm_num)⟩

/-- The equator projection as a continuous map on a set of points with `strip ≠ 0`. -/
def eqProjF (n : ℕ) (S : Set (MSph (n + 1))) (hS : ∀ v ∈ S, Work.Morse.strip v.1 ≠ 0) :
    C(↥S, MSph (n + 1)) :=
  ⟨fun v => eqProj n v.1 (hS v.1 v.2), by
    have hvec : Continuous fun v : ↥S => scaleV n 0 v.1.1 :=
      continuous_scaleV_pair n (fun _ : ↥S => (0 : ℝ)) continuous_const
        (fun v : ↥S => v.1.1) (by fun_prop)
    have hne : ∀ v : ↥S, ‖scaleV n 0 v.1.1‖ ≠ 0 :=
      fun v => norm_ne_zero_iff.mpr (scaleV_zero_ne_zero n v.1 (hS v.1 v.2))
    have hmain : Continuous fun v : ↥S => ‖scaleV n 0 v.1.1‖⁻¹ • scaleV n 0 v.1.1 :=
      (hvec.norm.inv₀ hne).smul hvec
    exact hmain.subtype_mk
      (fun v => norm_inv_smul n _ (scaleV_zero_ne_zero n v.1 (hS v.1 v.2)))⟩

theorem eqProjF_val (n : ℕ) (S : Set (MSph (n + 1))) (hS : ∀ v ∈ S, Work.Morse.strip v.1 ≠ 0)
    (v : ↥S) : (eqProjF n S hS v).1 = ‖scaleV n 0 v.1.1‖⁻¹ • scaleV n 0 v.1.1 := rfl

/-- The cap map as a map into the open cap. -/
def capMapPairC : C(B × MBall n, B × ↥(flGt n (-(1 / 2)))) :=
  (ContinuousMap.id B).prodMap (capBig n)

@[simp] theorem capMapPairC_apply (q : B × MBall n) :
    capMapPairC B n q = (q.1, capBig n q.2) := rfl

/-- Projection of the target `A`-set onto its fibre. -/
def qToFiber : C(↥(Qset B n), ↥(fiberQ n)) :=
  ⟨fun p => ⟨p.1.2.1, ⟨p.1.2.2, ((mem_Qset B n).mp p.2)⟩⟩,
    Continuous.subtype_mk (by fun_prop) _⟩

@[simp] theorem qToFiber_apply (p : ↥(Qset B n)) :
    (qToFiber B n p).1 = p.1.2.1 := rfl

theorem qToFiber_mem_strip_ne (p : ↥(Qset B n)) :
    Work.Morse.strip (qToFiber B n p).1.1 ≠ 0 :=
  (strip_ne_zero_iff n (qToFiber B n p).1).mpr
    (abs_lastC_lt_one_of_mem_fiberQ n (qToFiber B n p).2)

/-- The scaling `Φ_t` on the open band. -/
def qFiberParamC : C(unitInterval × ↥(fiberQ n), MSph (n + 1)) :=
  ⟨fun q => scalePt n (q.1 : ℝ) q.2.1
      (scaleV_ne_zero_of_abs_lt n (q.1 : ℝ) q.2.1 (abs_lastC_lt_one_of_mem_fiberQ n q.2.2)),
    CapScale.continuous_scalePt_comp n (α := unitInterval) (fun t : unitInterval => (t : ℝ))
      (by fun_prop) (fiberQ n) (fun t v => scaleV_ne_zero_of_abs_lt n (t : ℝ) v.1
        (abs_lastC_lt_one_of_mem_fiberQ n v.2))⟩

@[simp] theorem qFiberParamC_apply (q : unitInterval × ↥(fiberQ n)) :
    qFiberParamC n q = scalePt n (q.1 : ℝ) q.2.1
      (scaleV_ne_zero_of_abs_lt n (q.1 : ℝ) q.2.1
        (abs_lastC_lt_one_of_mem_fiberQ n q.2.2)) := rfl

/-- The projection `I × A-set → I × fibre`. -/
def toFiberParamQ : C(unitInterval × ↥(Qset B n), unitInterval × ↥(fiberQ n)) :=
  ⟨fun p => (p.1, qToFiber B n p.2),
    Continuous.prodMk continuous_fst ((qToFiber B n).continuous.comp continuous_snd)⟩

@[simp] theorem toFiberParamQ_apply (p : unitInterval × ↥(Qset B n)) :
    toFiberParamQ B n p = (p.1, qToFiber B n p.2) := rfl

/-- The scaled point of the homotopy. -/
def qFiberParam : C(unitInterval × ↥(Qset B n), MSph (n + 1)) :=
  (qFiberParamC n).comp (toFiberParamQ B n)

theorem qFiberParam_apply (p : unitInterval × ↥(Qset B n)) :
    qFiberParam B n p = scalePt n (p.1 : ℝ) (qToFiber B n p.2).1
      (scaleV_ne_zero_of_abs_lt n (p.1 : ℝ) (qToFiber B n p.2).1
        (abs_lastC_lt_one_of_mem_fiberQ n (qToFiber B n p.2).2)) := rfl

theorem lastC_qFiberParam (p : unitInterval × ↥(Qset B n)) :
    -(1 / 2) < lastC n (qFiberParam B n p).1 ∧ lastC n (qFiberParam B n p).1 < 1 / 2 :=
  lastC_scalePt_mem_Ioo n (p.1 : ℝ) (qToFiber B n p.2).1
    (scaleV_ne_zero_of_abs_lt n (p.1 : ℝ) (qToFiber B n p.2).1
      (abs_lastC_lt_one_of_mem_fiberQ n (qToFiber B n p.2).2))
    (show (0 : ℝ) ≤ (p.1 : ℝ) from (p.1).2.1)
    (show (p.1 : ℝ) ≤ 1 from (p.1).2.2)
    (qToFiber B n p.2).2.1 (qToFiber B n p.2).2.2

/-- The scaled point as an element of the open cap. -/
def qFiberGt : C(unitInterval × ↥(Qset B n), ↥(flGt n (-(1 / 2)))) :=
  ⟨fun p => ⟨qFiberParam B n p, (lastC_qFiberParam B n p).1⟩,
    Continuous.subtype_mk (qFiberParam B n).continuous _⟩

@[simp] theorem qFiberGt_apply (p : unitInterval × ↥(Qset B n)) :
    ((qFiberGt B n p : ↥(flGt n (-(1 / 2)))) : MSph (n + 1)) = qFiberParam B n p := rfl

/-- The homotopy of the `A`-level of step (c): the scaling from the equator projection to the
identity. -/
def qHom : C(unitInterval × ↥(Qset B n), ↥(Qset B n)) :=
  ⟨fun p => ⟨(p.2.1.1, qFiberGt B n p),
      ⟨(qFiberGt B n p).1.2, (lastC_qFiberParam B n p).2⟩⟩,
    Continuous.subtype_mk
      (Continuous.prodMk (show Continuous fun p : unitInterval × ↥(Qset B n) => p.2.1.1
          from by fun_prop) (qFiberGt B n).continuous) _⟩

@[simp] theorem qHom_apply (p : unitInterval × ↥(Qset B n)) :
    qHom B n p = ⟨(p.2.1.1, qFiberGt B n p),
      ⟨(qFiberGt B n p).1.2, (lastC_qFiberParam B n p).2⟩⟩ := rfl

/-! ## Auxiliary facts about the cap map and the equator projection -/

/-- The cap map retracts `strip` on the upper hemisphere. -/
theorem capMap_strip_of_nonneg (n : ℕ) (v : MSph (n + 1)) (h : 0 ≤ lastC n v.1) :
    capMap n (Work.Morse.strip v.1) = v.1 := by
  have hnorm : ‖Work.Morse.strip v.1‖ ^ 2 = 1 - (lastC n v.1) ^ 2 := norm_strip_sq_of_unit n v
  rw [show capMap n (Work.Morse.strip v.1) = Work.Morse.snocLp (Work.Morse.strip v.1)
      (Real.sqrt (1 - ‖Work.Morse.strip v.1‖ ^ 2)) from rfl, hnorm]
  have hsq : 1 - (1 - (lastC n v.1) ^ 2) = (lastC n v.1) ^ 2 := by ring
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg h]
  exact Work.Morse.snocLp_strip v.1

/-- The `strip` of the equator projection is the normalised `strip` of the point. -/
theorem norm_strip_eqProj (n : ℕ) (v : MSph (n + 1)) (h : Work.Morse.strip v.1 ≠ 0) :
    ‖Work.Morse.strip (eqProj n v h).1‖ = 1 := by
  have h1 : ‖Work.Morse.strip (eqProj n v h).1‖ ^ 2
      = 1 - (lastC n (eqProj n v h).1) ^ 2 := norm_strip_sq_of_unit n (eqProj n v h)
  rw [lastC_eqProj n v h] at h1
  have h2 : ‖Work.Morse.strip (eqProj n v h).1‖ ^ 2 = 1 := by rw [h1]; norm_num
  nlinarith [norm_nonneg (Work.Morse.strip (eqProj n v h).1)]

/-- The points of the open band have non-zero `strip`. -/
theorem fiberQ_ne (v : MSph (n + 1)) (hv : v ∈ fiberQ n) : Work.Morse.strip v.1 ≠ 0 :=
  (strip_ne_zero_iff n v).mpr (abs_lastC_lt_one_of_mem_fiberQ n hv)

/-- The equator projection on the open band. -/
def eqProjQ : C(↥(fiberQ n), MSph (n + 1)) :=
  eqProjF n (fiberQ n) (fiberQ_ne n)

@[simp] theorem eqProjQ_apply (v : ↥(fiberQ n)) :
    eqProjQ n v = eqProj n v.1 (fiberQ_ne n v.1 v.2) := rfl

/-! ## Step (c): the restriction of the cap map to the boundary sphere -/

/-- The cap map of a point of the ball of norm one lies in the open band. -/
theorem mem_Qset_capBig (q : B × MBall n) (hq : ‖q.2.1‖ = 1) :
    (q.1, capBig n q.2) ∈ Qset B n := by
  have hlast : lastC n (capMap n q.2.1) = 0 := by
    rw [lastC, capMap_last, hq]
    norm_num
  exact ⟨(capBig n q.2).1.2, lt_of_eq_of_lt hlast (by norm_num)⟩

/-- The restriction of the cap map to the boundary sphere. -/
def capPairRestrict : C(↥(Abound B n), ↥(Qset B n)) :=
  ⟨fun q => ⟨(q.1.1, capBig n q.1.2), mem_Qset_capBig B n q.1 q.2⟩,
    Continuous.subtype_mk
      (Continuous.prodMk (show Continuous fun q : ↥(Abound B n) => q.1.1 from by fun_prop)
        ((capBig n).continuous.comp
          (show Continuous fun q : ↥(Abound B n) => q.1.2 from by fun_prop))) _⟩

/-- `strip` as a map on the sphere. -/
def stripSph (n : ℕ) : C(MSph (n + 1), EuclideanSpace ℝ (Fin n)) :=
  ⟨fun v => Work.Morse.strip v.1,
    (Work.Cohomology.continuous_strip n).comp continuous_subtype_val⟩

@[simp] theorem stripSph_apply (n : ℕ) (v : MSph (n + 1)) :
    stripSph n v = Work.Morse.strip v.1 := rfl

/-- The `EuclideanSpace`-valued inverse of the restriction of the cap map. -/
def capInvFiberC : C(↥(Qset B n), EuclideanSpace ℝ (Fin n)) :=
  (stripSph n).comp ((eqProjQ n).comp (qToFiber B n))

/-- The `MBall`-valued inverse of the restriction of the cap map. -/
def capInvFiber : C(↥(Qset B n), MBall n) :=
  ⟨fun p => ⟨capInvFiberC B n p,
      le_of_eq (norm_strip_eqProj n (qToFiber B n p).1
        (fiberQ_ne n (qToFiber B n p).1 (qToFiber B n p).2))⟩,
    Continuous.subtype_mk (capInvFiberC B n).continuous _⟩

theorem mem_Abound_mk (b : B) (w : MBall n) (hw : ‖w.1‖ = 1) : (b, w) ∈ Abound B n := hw

/-- The inverse of the restriction of the cap map, given by the equator projection. -/
def capPairRestrictInv : C(↥(Qset B n), ↥(Abound B n)) :=
  ⟨fun p => ⟨(p.1.1, capInvFiber B n p),
      mem_Abound_mk B n p.1.1 (capInvFiber B n p)
        (norm_strip_eqProj n (qToFiber B n p).1
          (fiberQ_ne n (qToFiber B n p).1 (qToFiber B n p).2))⟩,
    Continuous.subtype_mk
      (Continuous.prodMk (show Continuous fun p : ↥(Qset B n) => p.1.1 from by fun_prop)
        (capInvFiber B n).continuous) _⟩

/-! ## The endpoint computations and the homotopies of step (c) -/

/-- `strip` after the cap map is the identity. -/
theorem strip_capMap (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) :
    Work.Morse.strip (capMap n w) = w := by
  apply PiLp.ext
  intro i
  rw [Work.Morse.strip_ofLp, capMap_castSucc]

/-- `strip` of a scaled point with zero last coordinate. -/
theorem strip_smul_snocLp (n : ℕ) (c : ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    Work.Morse.strip (c • Work.Morse.snocLp w 0) = c • w := by
  apply PiLp.ext
  intro i
  simp only [Work.Morse.strip_ofLp, PiLp.smul_apply, Work.Morse.snocLp_ofLp_castSucc]

/-- `strip` after the equator projection. -/
theorem strip_eqProj (n : ℕ) (v : MSph (n + 1)) (h : Work.Morse.strip v.1 ≠ 0) :
    Work.Morse.strip (eqProj n v h).1 = ‖Work.Morse.strip v.1‖⁻¹ • Work.Morse.strip v.1 := by
  have hnorm : ‖Work.Morse.snocLp (Work.Morse.strip v.1) (0 : ℝ)‖ = ‖Work.Morse.strip v.1‖ := by
    have h1 : ‖Work.Morse.snocLp (Work.Morse.strip v.1) (0 : ℝ)‖ ^ 2
        = ‖Work.Morse.strip v.1‖ ^ 2 := by
      rw [Work.Morse.snocLp_norm_sq]
      norm_num
    nlinarith [norm_nonneg (Work.Morse.snocLp (Work.Morse.strip v.1) (0 : ℝ)),
      norm_nonneg (Work.Morse.strip v.1)]
  rw [eqProj_val]
  show Work.Morse.strip (‖scaleV n 0 v.1‖⁻¹ • scaleV n 0 v.1) = _
  rw [scaleV, MulZeroClass.zero_mul]
  rw [show ‖Work.Morse.snocLp (Work.Morse.strip v.1) (0 : ℝ)‖ = ‖Work.Morse.strip v.1‖
    from hnorm]
  exact strip_smul_snocLp n _ _

theorem qFiberParamC_one (p : ↥(fiberQ n)) :
    qFiberParamC n ((1 : unitInterval), p) = p.1 := by
  apply Subtype.ext
  show ‖scaleV n ((1 : unitInterval) : ℝ) p.1.1‖⁻¹ • scaleV n ((1 : unitInterval) : ℝ) p.1.1
    = p.1.1
  have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  rw [h1]
  have hv : scaleV n 1 p.1.1 = p.1.1 := by
    rw [scaleV, one_mul]
    exact Work.Morse.snocLp_strip p.1.1
  rw [hv, show ‖p.1.1‖ = 1 from p.1.2]
  simp

theorem qFiberParamC_zero (p : ↥(fiberQ n)) :
    qFiberParamC n ((0 : unitInterval), p) = eqProj n p.1 (fiberQ_ne n p.1 p.2) := by
  apply Subtype.ext
  show ‖scaleV n ((0 : unitInterval) : ℝ) p.1.1‖⁻¹ • scaleV n ((0 : unitInterval) : ℝ) p.1.1
    = (eqProj n p.1 (fiberQ_ne n p.1 p.2)).1
  have h1 : ((0 : unitInterval) : ℝ) = 0 := rfl
  rw [h1]
  rfl

theorem qHom_one (p : ↥(Qset B n)) : qHom B n (1, p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val (qFiberParamC_one n (qToFiber B n p))

theorem qHom_zero (p : ↥(Qset B n)) :
    qHom B n (0, p) = capPairRestrict B n (capPairRestrictInv B n p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Subtype.ext
    show (qFiberParamC n ((0 : unitInterval), qToFiber B n p)).1
      = capMap n (Work.Morse.strip (eqProj n (qToFiber B n p).1
          (fiberQ_ne n (qToFiber B n p).1 (qToFiber B n p).2)).1)
    rw [qFiberParamC_zero]
    exact (capMap_strip_of_nonneg n
      (eqProj n (qToFiber B n p).1 (fiberQ_ne n (qToFiber B n p).1 (qToFiber B n p).2))
      (le_of_eq (lastC_eqProj n _ _).symm)).symm

theorem capPairRestrictInv_comp_restrict (p : ↥(Abound B n)) :
    capPairRestrictInv B n (capPairRestrict B n p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    show Work.Morse.strip (eqProj n ((qToFiber B n (capPairRestrict B n p)).1)
        (fiberQ_ne n _ (qToFiber B n (capPairRestrict B n p)).2)).1 = p.1.2.1
    rw [strip_eqProj]
    have hstrip : Work.Morse.strip (qToFiber B n (capPairRestrict B n p)).1.1 = p.1.2.1 := by
      show Work.Morse.strip (capMap n p.1.2.1) = p.1.2.1
      exact strip_capMap n p.1.2.1
    rw [hstrip, show ‖p.1.2.1‖ = 1 from p.2]
    simp

/-- The homotopy from `capIncl ∘ capScale` to the identity of the target `A`-set. -/
def capPairHomotopy : ContinuousMap.Homotopy
    ((capPairRestrict B n).comp (capPairRestrictInv B n)) (ContinuousMap.id (↥(Qset B n))) :=
  ⟨qHom B n, qHom_zero B n, qHom_one B n⟩

/-! ## The homotopy equivalences of step (c) -/

theorem homotopic_of_contractible_codomain {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace Y] (f g : C(X, Y)) : f.Homotopic g := by
  obtain ⟨y₀, hy₀⟩ := id_nullhomotopic Y
  have h1 : f.Homotopic (ContinuousMap.const X y₀) := by
    have := hy₀.comp (ContinuousMap.Homotopic.refl f)
    simpa using this
  have h2 : g.Homotopic (ContinuousMap.const X y₀) := by
    have := hy₀.comp (ContinuousMap.Homotopic.refl g)
    simpa using this
  exact h1.trans h2.symm

theorem capPairRestrictInv_comp_restrict_cm :
    (capPairRestrictInv B n).comp (capPairRestrict B n)
      = ContinuousMap.id (↥(Abound B n)) := by
  apply ContinuousMap.ext
  intro p
  exact capPairRestrictInv_comp_restrict B n p

/-- The homotopy from `capScale ∘ capIncl` to the identity of the source `A`-set. -/
def capPairHomotopyInv : ContinuousMap.Homotopy
    ((capPairRestrictInv B n).comp (capPairRestrict B n))
      (ContinuousMap.id (↥(Abound B n))) :=
  (capPairRestrictInv_comp_restrict_cm B n).symm ▸
    ContinuousMap.Homotopy.refl (ContinuousMap.id (↥(Abound B n)))

/-- The cap map carries the boundary sphere into the open band. -/
theorem capMapPairC_mem (q : ↥(Abound B n)) : capMapPairC B n q.1 ∈ Qset B n :=
  mem_Qset_capBig B n q.1 q.2

/-- The pair condition of the cap map of step (c). -/
theorem capQ_mem : ∀ q ∈ Abound B n, capMapPairC B n q ∈ Qset B n :=
  fun q hq => mem_Qset_capBig B n q hq

/-- The ambient component of step (c): the cap map is a homotopy equivalence. -/
theorem isIso_capMapPairC_X (k : ℕ) : CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (Work.Cohomology.dualChainMap ℤ (TopCat.of (B × MBall n))
      (TopCat.of (B × ↥(flGt n (-(1 / 2))))) (TopCat.ofHom (capMapPairC B n))) k) := by
  haveI hcontr : ContractibleSpace ↥(flGt n (-(1 / 2))) := CapContract.contractibleSpace_flGt n
  have h1 : ((capBig n).comp (stripBig n)).Homotopic
      (ContinuousMap.id ↥(flGt n (-(1 / 2)))) :=
    homotopic_of_contractible_codomain _ _
  have h2 : ((stripBig n).comp (capBig n)).Homotopic (ContinuousMap.id (MBall n)) :=
    (CapBall.stripBig_comp_capBig n) ▸ ContinuousMap.Homotopic.refl (ContinuousMap.id (MBall n))
  have heq : TopCat.ofHom (capMapPairC B n)
      = TopCat.ofHom ((ContinuousMap.id B).prodMap (capBig n)) := rfl
  rw [heq]
  exact CapGlue.isIso_homologyMap_dualChainMap_prodMap (B := B) (capBig n) (stripBig n)
    h1 h2 ℤ k

/-- The `A`-level component of step (c): the restriction of the cap map to the boundary sphere is a
homotopy equivalence. -/
theorem isIso_capMapPairC_A (k : ℕ) : CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (Work.Cohomology.dualChainMap ℤ (TopCat.of ↥(Abound B n)) (TopCat.of ↥(Qset B n))
      (Work.Cohomology.relMapSub (Abound B n) (Qset B n)
        (TopCat.ofHom (capMapPairC B n)) (capQ_mem B n))) k) := by
  have heq : Work.Cohomology.relMapSub (Abound B n) (Qset B n)
      (TopCat.ofHom (capMapPairC B n)) (capQ_mem B n)
      = TopCat.ofHom (capPairRestrict B n) := by
    apply TopCat.ext
    intro x
    rfl
  rw [heq]
  exact Work.Cohomology.homotopyEquiv ℤ (TopCat.of ↥(Abound B n)) (TopCat.of ↥(Qset B n))
    (TopCat.ofHom (capPairRestrict B n)) (TopCat.ofHom (capPairRestrictInv B n))
    (capPairHomotopyInv B n) (capPairHomotopy B n) k

/-- **Step (c)**: the cap map induces an isomorphism on the relative cohomology of the pair
`(B × Dⁿ, B × Sⁿ⁻¹) → (B × {last > -1/2}, B × {-1/2 < last < 1/2})`. -/
theorem isIso_relCohMap_cap (m : ℕ) :
    CategoryTheory.IsIso (relCohMap (capMapPairC B n) (Abound B n) (Qset B n)
      (capQ_mem B n) ℤ m) :=
  Work.Thom.isIso_homologyMap_relComplexMap (X₁ := TopCat.of (B × MBall n))
    (X₂ := TopCat.of (B × ↥(flGt n (-(1 / 2))))) (Abound B n) (Qset B n)
    (TopCat.ofHom (capMapPairC B n)) (capQ_mem B n) ℤ
    (fun k => isIso_capMapPairC_X B n k) (fun k => isIso_capMapPairC_A B n k) m

end

end Work.Thom