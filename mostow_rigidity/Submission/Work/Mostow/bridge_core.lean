import Mathlib
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.HaarBoost
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.VolDefs
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.volH_null_linear
import Submission.Work.Mostow.hdistContinuous
import Submission.Work.Mostow.pullback_dirichletSet

/-!
# `bridge_core` — a finite-volume `volH`-fundamental domain from finite Haar covolume

Given
* a base point `o` whose `Γ`-stabiliser is trivial (`ho`),
* nearest orbit points exist (`hmin`),
* the orbit map `g ↦ g • 0` pushes Haar measure on `PO n 1` to a positive finite multiple
  `c` of `volH n` (`hprop`),
* `Γ` has finite Haar covolume in `PO n 1` (`hcov`),

we produce a `volH`-fundamental domain for `Γ` on `ℍⁿ = E n` of finite volume.

The construction is the *Dirichlet domain* `D` of `Γ` at `o`
(`Work.Mostow.dirichletSet`).  Its translates are pairwise a.e. disjoint because a point of
`D ∩ γ • D` is equidistant from `o` and `γ • o`, hence lies in a bisector, which is
`volH`-null (`Work.Mostow.dirichlet_bisector_null`); the stabiliser of `o` being trivial ensures
`γ • o ≠ o`.

The finiteness of `volH n D` comes from pulling `D` back along `π g = g • 0`: the preimage
`π ⁻¹' D` is a `Γ`-fundamental domain for the Haar measure on `PO n 1` whose measure is
`c * volH n D` (`hprop`), and the covolume is the measure of any fundamental domain, so
`covolume Γ (PO n 1) = c * volH n D < ⊤`.
-/

set_option maxHeartbeats 1600000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Measure
open scoped ENNReal Topology Pointwise

noncomputable section

variable {n : ℕ}

/-- The Dirichlet domain of `Γ` at the base point `o`: the set of points that are no further from
`o` than from any `Γ`-translate of `o`. -/
def dirichletSet (Γ : Subgroup (PO n 1)) (o : E n) : Set (E n) :=
  {x : E n | ∀ γ : Γ, hdist x o ≤ hdist x (γ • o)}

/-- `x ↦ hdist x o` is continuous: it is `arcosh` of the smooth function
`tpart x * tpart o - ⟪x,o⟫`, whose values are `≥ 1`. -/
lemma dirichlet_hdist_continuous_right (o : E n) : Continuous (fun x : E n => hdist x o) := by
  have hcont : Continuous (fun x : E n => tpart x * tpart o - inner ℝ x o) := by
    simp only [tpart]
    fun_prop
  have hlev : ∀ x : E n, tpart x * tpart o - inner ℝ x o ∈ Set.Ici (1 : ℝ) := by
    intro x
    simp only [Set.mem_Ici]
    have h1 : inner ℝ x o ≤ ‖x‖ * ‖o‖ := real_inner_le_norm x o
    have h2 : tpart x * tpart o = Real.sqrt ((1 + ‖x‖ ^ 2) * (1 + ‖o‖ ^ 2)) := by
      rw [tpart, tpart, Real.sqrt_mul (by positivity)]
    have h3 : (1 : ℝ) + ‖x‖ * ‖o‖ ≤ tpart x * tpart o := by
      rw [h2]
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg (‖x‖ - ‖o‖), norm_nonneg x, norm_nonneg o]
    linarith
  have h := ContinuousOn.comp_continuous (g := Real.arcosh)
    (f := fun x : E n => tpart x * tpart o - inner ℝ x o) (s := Set.Ici 1)
    Real.continuousOn_arcosh hcont hlev
  simpa [Function.comp_def, hdist] using h

/-- Each half space cutting out the Dirichlet domain is closed. -/
lemma isClosed_dirichletSet_le (Γ : Subgroup (PO n 1)) (o : E n) (γ : Γ) :
    IsClosed {x : E n | hdist x o ≤ hdist x (γ • o)} := by
  have h1 : Continuous (fun x : E n => hdist x o) := dirichlet_hdist_continuous_right o
  have h2 : Continuous (fun x : E n => hdist x (γ • o)) :=
    dirichlet_hdist_continuous_right (γ • o)
  have hsub : Continuous (fun x : E n => hdist x (γ • o) - hdist x o) := h2.sub h1
  have hpre : IsClosed ((fun x : E n => hdist x (γ • o) - hdist x o) ⁻¹' Set.Ici 0) :=
    isClosed_Ici.preimage hsub
  convert hpre using 1
  ext x
  simp [sub_nonneg]

/-- The Dirichlet domain is closed, hence measurable. -/
lemma isClosed_dirichletSet (Γ : Subgroup (PO n 1)) (o : E n) :
    IsClosed (dirichletSet Γ o) := by
  have h : dirichletSet Γ o = ⋂ γ : Γ, {x : E n | hdist x o ≤ hdist x (γ • o)} := by
    ext x
    simp [dirichletSet]
  rw [h]
  exact isClosed_iInter fun γ => isClosed_dirichletSet_le Γ o γ

/-- The equidistant set ("bisector") between two distinct points is `volH`-null.

(`Work.Mostow.bisector_null` in `haarBridge` is the same statement; it is reproved here under a
different name because `haarBridge` imports the present file.) -/
theorem dirichlet_bisector_null (n : ℕ) {o w : E n} (how : o ≠ w) :
    volH n {u : E n | hdist u o = hdist u w} = 0 := by
  have hsubset : {u : E n | hdist u o = hdist u w} ⊆
      {u : E n | inner ℝ (o - w) u + (tpart w - tpart o) * tpart u = 0} := by
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu ⊢
    have h := congrArg Real.cosh hu
    rw [cosh_hdist, cosh_hdist] at h
    have h2 : inner ℝ o u - inner ℝ w u = tpart u * tpart o - tpart u * tpart w := by
      rw [← real_inner_comm u o, ← real_inner_comm u w] at h
      linarith
    rw [inner_sub_left, h2]
    ring
  refine measure_mono_null hsubset (volH_null_linear n (o - w) (tpart w - tpart o) ?_)
  exact Or.inl (sub_ne_zero.2 how)

/-- The Haar measure on `PO n 1` is invariant under the left action of a subgroup. -/
theorem smulInvariantMeasure_subtype_PO (Γ : Subgroup (PO n 1)) :
    SMulInvariantMeasure Γ (PO n 1) (MeasureSpace.volume : Measure (PO n 1)) where
  measure_preimage_smul c s hs := by
    show (MeasureSpace.volume : Measure (PO n 1)) ((fun x : PO n 1 => c • x) ⁻¹' s) = _
    rw [show (fun x : PO n 1 => c • x) = (fun x : PO n 1 => (c : PO n 1) * x) from rfl]
    exact (measurePreserving_mul_left (Measure.haar : Measure (PO n 1))
      (c : PO n 1)).measure_preimage hs.nullMeasurableSet

/-! ## Haar measure instances on `PO n 1` -/

/-- The canonical measure on `PO n 1` is `Measure.haar`. -/
theorem po_volume_eq_haar : (MeasureSpace.volume : Measure (PO n 1)) = Measure.haar := rfl

instance instIsHaarMeasurePOVolume : IsHaarMeasure (MeasureSpace.volume : Measure (PO n 1)) :=
  po_volume_eq_haar ▸ (inferInstance : IsHaarMeasure (Measure.haar : Measure (PO n 1)))

instance instSMulInvariantMeasureSubtypePO (Γ : Subgroup (PO n 1)) :
    SMulInvariantMeasure Γ (PO n 1) (MeasureSpace.volume : Measure (PO n 1)) :=
  smulInvariantMeasure_subtype_PO Γ

/-- The left-regular action of `PO n 1` on itself preserves Haar measure. -/
instance instSMulInvariantMeasurePOself :
    SMulInvariantMeasure (PO n 1) (PO n 1) (MeasureSpace.volume : Measure (PO n 1)) where
  measure_preimage_smul c s hs := by
    exact (measurePreserving_mul_left (Measure.haar : Measure (PO n 1))
      c).measure_preimage hs.nullMeasurableSet

/-! ## The Dirichlet domain is a fundamental domain

(`Work.Mostow.dirichletSet_isFundamentalDomain`, proved by a colleague in
`Submission.Work.Mostow.dirichletSet_isFundamentalDomain`, states exactly this result but its module
imports the present one, so the argument is reproduced here under a different name.) -/

theorem bridge_dirichletSet_isFundamentalDomain (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) [Countable Γ]
    (o : Submission.Mostow.E n) (ho : ∀ γ : Γ, γ • o = o → γ = 1)
    (hmin : ∀ x : Submission.Mostow.E n, ∃ γ : Γ,
      ∀ γ' : Γ, Submission.Mostow.hdist x (γ • o) ≤ Submission.Mostow.hdist x (γ' • o)) :
    MeasureTheory.IsFundamentalDomain Γ (Work.Mostow.dirichletSet Γ o)
      (Submission.Mostow.volH n) := by
  obtain ⟨-, -, -, hone, hmul, -, -, -, -, -, -, -⟩ := hA
  obtain ⟨-, -, -, -, -, -, hiso, -, -, -, -, -, -⟩ := hI
  -- The action laws of `PO n 1`, transported to `Γ`.
  have honeΓ : ∀ y : E n, (1 : Γ) • y = y := by
    intro y
    calc (1 : Γ) • y = (1 : PO n 1) • y := rfl
      _ = y := hone y
  have hsm_mul_Γ : ∀ (g h : Γ) (y : E n), (g * h : Γ) • y = g • (h • y) := by
    intro g h y
    calc (g * h : Γ) • y = ((g : PO n 1) * (h : PO n 1)) • y := rfl
      _ = (g : PO n 1) • ((h : PO n 1) • y) := hmul (g : PO n 1) (h : PO n 1) y
      _ = g • (h • y) := rfl
  have hisoΓ : ∀ (g : Γ) (u v : E n), hdist (g • u) (g • v) = hdist u v := by
    intro g u v
    calc hdist (g • u) (g • v) = hdist ((g : PO n 1) • u) ((g : PO n 1) • v) := rfl
      _ = hdist u v := hiso (g : PO n 1) u v
  have hinv_smul : ∀ (g : Γ) (y : E n), g • ((g⁻¹ : Γ) • y) = y := by
    intro g y
    calc g • ((g⁻¹ : Γ) • y) = (g : PO n 1) • ((g : PO n 1)⁻¹ • y) := rfl
      _ = ((g : PO n 1) * (g : PO n 1)⁻¹) • y :=
          (hmul (g : PO n 1) ((g : PO n 1))⁻¹ y).symm
      _ = y := by rw [mul_inv_cancel, hone]
  have hinv_smul' : ∀ (g : Γ) (y : E n), (g⁻¹ : Γ) • (g • y) = y := by
    intro g y
    calc (g⁻¹ : Γ) • (g • y) = (g : PO n 1)⁻¹ • ((g : PO n 1) • y) := rfl
      _ = ((g : PO n 1)⁻¹ * (g : PO n 1)) • y :=
          (hmul ((g : PO n 1))⁻¹ (g : PO n 1) y).symm
      _ = y := by rw [inv_mul_cancel, hone]
  refine ⟨?_, ?_, ?_⟩
  · -- null-measurability: `D` is closed
    exact (isClosed_dirichletSet Γ o).measurableSet.nullMeasurableSet
  · -- covering: the nearest orbit point of `x` translates `x` into `D`
    refine Filter.Eventually.of_forall fun x => ?_
    obtain ⟨γ, hγ⟩ := hmin x
    refine ⟨γ⁻¹, ?_⟩
    intro δ
    have h1 : hdist ((γ⁻¹ : Γ) • x) o = hdist x (γ • o) := by
      rw [← hisoΓ γ ((γ⁻¹ : Γ) • x) o, hinv_smul γ x]
    have h2 : hdist ((γ⁻¹ : Γ) • x) (δ • o) = hdist x ((γ * δ : Γ) • o) := by
      rw [← hisoΓ γ ((γ⁻¹ : Γ) • x) (δ • o), hinv_smul γ x, ← hsm_mul_Γ γ δ o]
    rw [h1, h2]
    exact hγ (γ * δ)
  · -- pairwise a.e. disjointness: points of `a • D ∩ b • D` lie on the bisector `(a • o, b • o)`
    intro a b hab
    show volH n ((a • dirichletSet Γ o) ∩ (b • dirichletSet Γ o)) = 0
    have hne : ((a : PO n 1) • o) ≠ ((b : PO n 1) • o) := by
      intro h
      have hab_eq : a • o = b • o := by
        calc a • o = (a : PO n 1) • o := rfl
          _ = (b : PO n 1) • o := h
          _ = b • o := rfl
      have h2 : (b⁻¹ * a : Γ) • o = o := by
        rw [hsm_mul_Γ b⁻¹ a o, hab_eq, hinv_smul' b o]
      have hba : b⁻¹ * a = 1 := ho _ h2
      have hab' : a = b := by
        have hb : b * (b⁻¹ * a) = b := by rw [hba, mul_one]
        rwa [mul_inv_cancel_left] at hb
      exact hab hab'
    have hnull : volH n {u : E n | hdist u ((a : PO n 1) • o) = hdist u ((b : PO n 1) • o)} = 0 :=
      dirichlet_bisector_null n hne
    refine measure_mono_null ?_ hnull
    intro x hx
    rw [Set.mem_inter_iff, Set.mem_smul_set, Set.mem_smul_set] at hx
    obtain ⟨⟨y, hy, hyx⟩, ⟨z, hz, hzx⟩⟩ := hx
    subst hyx
    have hle1 : hdist (a • y) (a • o) ≤ hdist (a • y) (b • o) := by
      have h := hy (a⁻¹ * b : Γ)
      rw [← hisoΓ a y o, ← hisoΓ a y ((a⁻¹ * b : Γ) • o)] at h
      rw [← hsm_mul_Γ a (a⁻¹ * b) o] at h
      rw [show (a * (a⁻¹ * b) : Γ) = b from mul_inv_cancel_left a b] at h
      exact h
    have hle2 : hdist (a • y) (b • o) ≤ hdist (a • y) (a • o) := by
      have h := hz (b⁻¹ * a : Γ)
      rw [← hisoΓ b z o, ← hisoΓ b z ((b⁻¹ * a : Γ) • o)] at h
      rw [← hsm_mul_Γ b (b⁻¹ * a) o] at h
      rw [show (b * (b⁻¹ * a) : Γ) = a from mul_inv_cancel_left b a] at h
      rw [hzx] at h
      exact h
    exact le_antisymm hle1 hle2

/-! ## Assembly -/

/-- **Assembly.**  `bridge_core` follows from the two construction lemmas: the Dirichlet domain
`dirichletSet Γ o` is a `volH`-fundamental domain, and its preimage under the orbit map
`π g = g • 0` is a Haar fundamental domain of measure `c * volH n (dirichletSet Γ o)`. -/
lemma bridge_core_of_pieces (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) [Countable Γ]
    (o : Submission.Mostow.E n) (ho : ∀ γ : Γ, γ • o = o → γ = 1)
    (hmin : ∀ x : Submission.Mostow.E n, ∃ γ : Γ,
      ∀ γ' : Γ, Submission.Mostow.hdist x (γ • o) ≤ Submission.Mostow.hdist x (γ' • o))
    (c : ENNReal) (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hmap : MeasureTheory.Measure.map
        (fun g : LeanEval.Geometry.MostowRigidity.PO n 1 => g • (0 : Submission.Mostow.E n))
        (MeasureTheory.MeasureSpace.volume :
          MeasureTheory.Measure (LeanEval.Geometry.MostowRigidity.PO n 1)) =
        c • Submission.Mostow.volH n)
    (hcov : MeasureTheory.covolume Γ
      (LeanEval.Geometry.MostowRigidity.PO n 1) ≠ ⊤)
    (h1 : MeasureTheory.IsFundamentalDomain Γ (Work.Mostow.dirichletSet Γ o)
      (Submission.Mostow.volH n))
    (h2 : MeasureTheory.IsFundamentalDomain Γ
        ((fun g : LeanEval.Geometry.MostowRigidity.PO n 1 => g • (0 : Submission.Mostow.E n)) ⁻¹'
          Work.Mostow.dirichletSet Γ o)
        (MeasureTheory.MeasureSpace.volume :
          MeasureTheory.Measure (LeanEval.Geometry.MostowRigidity.PO n 1)) ∧
      (MeasureTheory.MeasureSpace.volume :
          MeasureTheory.Measure (LeanEval.Geometry.MostowRigidity.PO n 1))
        ((fun g : LeanEval.Geometry.MostowRigidity.PO n 1 => g • (0 : Submission.Mostow.E n)) ⁻¹'
          Work.Mostow.dirichletSet Γ o)
        = c * Submission.Mostow.volH n (Work.Mostow.dirichletSet Γ o)) :
    ∃ D : Set (Submission.Mostow.E n),
      MeasureTheory.IsFundamentalDomain Γ D (Submission.Mostow.volH n) ∧
      Submission.Mostow.volH n D ≠ ⊤ := by
  have hcov_eq : MeasureTheory.covolume Γ (LeanEval.Geometry.MostowRigidity.PO n 1) =
      (MeasureTheory.MeasureSpace.volume :
        MeasureTheory.Measure (LeanEval.Geometry.MostowRigidity.PO n 1))
        ((fun g : LeanEval.Geometry.MostowRigidity.PO n 1 =>
          g • (0 : Submission.Mostow.E n)) ⁻¹' Work.Mostow.dirichletSet Γ o) :=
    MeasureTheory.IsFundamentalDomain.covolume_eq_volume
      (MeasureTheory.MeasureSpace.volume :
        MeasureTheory.Measure (LeanEval.Geometry.MostowRigidity.PO n 1)) h2.1
  have h3 : c * Submission.Mostow.volH n (Work.Mostow.dirichletSet Γ o) ≠ ⊤ := by
    rw [← h2.2, ← hcov_eq]
    exact hcov
  refine ⟨Work.Mostow.dirichletSet Γ o, h1, fun htop => h3 ?_⟩
  rw [htop, ENNReal.mul_top hc0]

/-! ## The main statement -/

/-- **Bridge core.** A discrete subgroup `Γ ≤ PO n 1` with trivial stabiliser at `o`, nearest
orbit points, a positive finite orbit-map pushforward constant and finite Haar covolume admits a
`volH`-fundamental domain of finite volume. -/
theorem bridge_core (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) [Countable Γ]
    (o : Submission.Mostow.E n) (ho : ∀ γ : Γ, γ • o = o → γ = 1)
    (hmin : ∀ x : Submission.Mostow.E n, ∃ γ : Γ,
      ∀ γ' : Γ, Submission.Mostow.hdist x (γ • o) ≤ Submission.Mostow.hdist x (γ' • o))
    (hprop : ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      MeasureTheory.Measure.map (fun g : LeanEval.Geometry.MostowRigidity.PO n 1 =>
          g • (0 : Submission.Mostow.E n))
          (MeasureTheory.MeasureSpace.volume :
            MeasureTheory.Measure (LeanEval.Geometry.MostowRigidity.PO n 1)) =
        c • Submission.Mostow.volH n)
    (hcov : MeasureTheory.covolume Γ
      (LeanEval.Geometry.MostowRigidity.PO n 1) ≠ ⊤) :
    ∃ D : Set (Submission.Mostow.E n),
      MeasureTheory.IsFundamentalDomain Γ D (Submission.Mostow.volH n) ∧
      Submission.Mostow.volH n D ≠ ⊤ := by
  obtain ⟨c, hc0, hctop, hmap⟩ := hprop
  have h1 : MeasureTheory.IsFundamentalDomain Γ (Work.Mostow.dirichletSet Γ o)
      (Submission.Mostow.volH n) :=
    Work.Mostow.bridge_dirichletSet_isFundamentalDomain n hA hI Γ o ho hmin
  refine Work.Mostow.bridge_core_of_pieces n hA hI Γ o ho hmin c hc0 hctop hmap hcov h1 ?_
  exact Work.Mostow.pullback_dirichletSet n hA hI Γ hmap h1
    (Work.Mostow.isClosed_dirichletSet Γ o).measurableSet

end

end Work.Mostow
