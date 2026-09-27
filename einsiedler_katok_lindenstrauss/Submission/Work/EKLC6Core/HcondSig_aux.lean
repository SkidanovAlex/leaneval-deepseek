import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.EntSig
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLRelCross.leafwise_acovariant
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.EKLNonExc.VFacts

/-!
# `EKLC6Core.HcondSig_le_growth`

Pisa 7.34/7.35 (the "shape comparison"): for an `aDiag t`-descending plaque algebra `A` whose
atoms are `U = Uminus t`-plaques, the `σ`-algebra conditional entropy of `A` given
`comap (aDiag t ·) A` is at most the integral of the entropy contribution
`growthFun (Uminus t) ν t x = -log ν x (conjBox (Uminus t) t)`.

The proof (see the section below) bounds `H_μ(A | comap a A)` by the integral of the pointwise
"surprisal" of the `A`-atom inside its `comap a A`-atom,
`hcsg_shapeInfo x = -log (ν x (shape A U x) / ν x (shape (comap a A) U x))`, and then identifies that
integral with `∫ growthFun (Uminus t) ν t` by the pointwise covariance identity (Pisa 7.16/7.18).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Set-theoretic bookkeeping for the pull-back by `aDiag t` -/

/-- If `B` is `A`-measurable and contains `y`, then the atom `[y]_A` is contained in `B`. -/
theorem hcsg_atom_subset_of_mem {A : MeasurableSpace X3} {B : Set X3} (hB : MeasurableSet[A] B)
    {y : X3} (hy : y ∈ B) : atom A y ⊆ B :=
  Set.sInter_subset_of_mem ⟨hB, hy⟩

/-- Atoms of a smaller `σ`-algebra are bigger. -/
theorem hcsg_atom_mono {m A : MeasurableSpace X3} (h : m ≤ A) (x : X3) :
    atom A x ⊆ atom m x :=
  Set.sInter_mono (fun s hs => ⟨h s hs.1, hs.2⟩)

/-- If `y ∈ [x]_m` then the atom of `y` is contained in the atom of `x`. -/
theorem hcsg_atom_subset_atom_of_mem {m : MeasurableSpace X3} {x y : X3} (hy : y ∈ atom m x) :
    atom m y ⊆ atom m x :=
  Set.sInter_mono (fun s hs => ⟨hs.1, hcsg_atom_subset_of_mem hs.1 hs.2 hy⟩)

/-- Membership in atoms is symmetric. -/
theorem hcsg_mem_atom_comm {m : MeasurableSpace X3} {x y : X3} :
    y ∈ atom m x ↔ x ∈ atom m y := by
  have key : ∀ {a b : X3}, b ∈ atom m a → a ∈ atom m b := by
    intro a b hab
    by_contra hba
    have h : ∃ S : Set X3, MeasurableSet[m] S ∧ b ∈ S ∧ a ∉ S := by
      by_contra hc
      push_neg at hc
      exact hba (by rw [atom]; exact Set.mem_sInter.mpr (fun t ht => hc t ht.1 ht.2))
    obtain ⟨S, hSmeas, hbS, haS⟩ := h
    have hbSc : b ∈ Sᶜ := (hcsg_atom_subset_of_mem hSmeas.compl haS) hab
    exact hbSc hbS
  exact ⟨key, key⟩

/-- `y ∈ [x]_m` implies `atom m y = atom m x`. -/
theorem hcsg_atom_eq_of_mem {m : MeasurableSpace X3} {x y : X3} (hy : y ∈ atom m x) :
    atom m y = atom m x :=
  le_antisymm (hcsg_atom_subset_atom_of_mem hy) (hcsg_atom_subset_atom_of_mem (hcsg_mem_atom_comm.mp hy))

/-- The atom of a pull-back `σ`-algebra is the preimage of the atom. -/
theorem hcsg_atom_comap (T : X3 → X3) (A : MeasurableSpace X3) (x : X3) :
    atom (MeasurableSpace.comap T A) x = T ⁻¹' atom A (T x) := by
  ext z
  simp only [atom, Set.mem_preimage, Set.mem_sInter, Set.mem_ofPred_eq]
  constructor
  · intro h S' ⟨hS', hTx⟩
    exact h (T ⁻¹' S') ⟨MeasurableSpace.measurableSet_comap.mpr ⟨S', hS', rfl⟩, hTx⟩
  · intro h S ⟨hS, hx⟩
    obtain ⟨S'', hS''meas, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hS
    exact h S'' ⟨hS''meas, hx⟩

/-! ## The conjugated shapes -/

/-- `(aDiag t * g * aDiag t⁻¹) • (aDiag t • x) = aDiag t • (g • x)`. -/
theorem hcsg_smul_conj1 (t : Fin 3 → ℝ) (g : SL3) (x : X3) :
    (aDiag t * g * (aDiag t)⁻¹) • (aDiag t • x) = aDiag t • (g • x) := by
  calc (aDiag t * g * (aDiag t)⁻¹) • (aDiag t • x)
      = ((aDiag t * g * (aDiag t)⁻¹) * aDiag t) • x := by rw [← mul_smul]
    _ = (aDiag t * g) • x := by
        congr 1
        group
    _ = aDiag t • (g • x) := by rw [mul_smul]

/-- `aDiag t • ((aDiag (-t) * v * aDiag (-t)⁻¹) • x) = v • (aDiag t • x)`. -/
theorem hcsg_smul_conj2 (t : Fin 3 → ℝ) (v : SL3) (x : X3) :
    aDiag t • ((aDiag (-t) * v * (aDiag (-t))⁻¹) • x) = v • (aDiag t • x) := by
  rw [← mul_smul]
  have h : aDiag t * (aDiag (-t) * v * (aDiag (-t))⁻¹) = v * aDiag t := by
    rw [aDiag_neg_eq_inv]; group
  rw [h, mul_smul]

/-- `U` is normalised by `aDiag t` when `U` is horospherical. -/
theorem hcsg_conj_mem {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ) {u : SL3}
    (hu : u ∈ U) : aDiag t * u * (aDiag t)⁻¹ ∈ U := hU.2.1 t u hu

/-- The shape of the pull-back algebra `comap (aDiag t ·) A` at `x` is the conjugate by
`aDiag (-t)` of the shape of `A` at `aDiag t • x`. -/
theorem hcsg_shape_comap_eq {U : Subgroup SL3} (hU : IsHoro U) (A : MeasurableSpace X3)
    (t : Fin 3 → ℝ) (x : X3) :
    shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x =
      conjBy (-t) (shape A U (aDiag t • x)) := by
  rw [shape, shape, conjBy, hcsg_atom_comap]
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨hgU, hgx⟩
    refine ⟨aDiag t * g * (aDiag t)⁻¹, ⟨hcsg_conj_mem hU t hgU, ?_⟩, ?_⟩
    · rw [hcsg_smul_conj1]; exact hgx
    · rw [aDiag_neg_eq_inv]; group
  · rintro ⟨v, ⟨hvU, hvx⟩, rfl⟩
    refine ⟨hcsg_conj_mem hU (-t) hvU, ?_⟩
    rw [hcsg_smul_conj2]
    exact hvx

/-- The plaque-algebra property of `A` transports to `comap (aDiag t ·) A`. -/
theorem hcsg_comapPlaqueAlg {U : Subgroup SL3} (hU : IsHoro U) {Z : Set X3} {A : MeasurableSpace X3}
    (hA : IsPlaqueAlgebra U Z A) (t : Fin 3 → ℝ) :
    IsPlaqueAlgebra U ((fun y : X3 => aDiag t • y) ⁻¹' Z)
      (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) := by
  have h := Work.EKLRelCross.isPlaqueAlgebra_translate (S := ⟨A⟩) hU t hA
  have hZ : MeasurableSet[MeasurableSpace.comap (fun y : X3 => aDiag t • y) A]
      ((fun y : X3 => aDiag t • y) ⁻¹' Z) :=
    MeasurableSpace.measurableSet_comap.mpr ⟨Z, hA.2.2.1, rfl⟩
  have hsup : (Work.EKLRelCross.MSAlg.translate ⟨A⟩ t Z).m =
      MeasurableSpace.comap (fun y : X3 => aDiag t • y) A := by
    rw [Work.EKLRelCross.MSAlg.translate]
    exact sup_eq_left.mpr (MeasurableSpace.generateFrom_le (fun s hs => by
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact hZ))
  rw [hsup] at h
  exact h

/-! ## Basic facts about the shapes -/

/-- `1` belongs to the shape of any atom. -/
theorem hcsg_one_mem_shape (m : MeasurableSpace X3) (U : Subgroup SL3) (x : X3) :
    (1 : SL3) ∈ shape m U x :=
  ⟨U.one_mem, by rw [one_smul]; exact Set.mem_sInter.mpr (fun s hs => hs.2)⟩

/-- The shape of a plaque algebra is measurable. -/
theorem hcsg_measurableSet_shape {U : Subgroup SL3} (hU : IsHoro U) {A : MeasurableSpace X3}
    {Z : Set X3} (hA : IsPlaqueAlgebra U Z A) {x : X3} (hx : x ∈ Z) :
    MeasurableSet (shape A U x) := by
  obtain ⟨O, hOopen, hOeq⟩ := (hA.2.2.2 x hx).2.2.1
  rw [hOeq]
  exact hOopen.measurableSet.inter hU.1.measurableSet

/-- The shape of a plaque algebra contains `V δ ∩ U` for some `δ > 0`. -/
theorem hcsg_exists_V_subset_shape {U : Subgroup SL3} {A : MeasurableSpace X3} {Z : Set X3}
    (hA : IsPlaqueAlgebra U Z A) {x : X3} (hx : x ∈ Z) :
    ∃ δ : ℝ, 0 < δ ∧ V δ ∩ (U : Set SL3) ⊆ shape A U x := by
  obtain ⟨O, hOopen, hOeq⟩ := (hA.2.2.2 x hx).2.2.1
  have h1 : (1 : SL3) ∈ O := by
    have h := hcsg_one_mem_shape A U x
    rw [hOeq] at h; exact h.1
  obtain ⟨δ, hδ, hsub⟩ := Work.EKLNonExc.V_nhds_basis O (hOopen.mem_nhds h1)
  exact ⟨δ, hδ, fun g hg => by rw [hOeq]; exact ⟨hsub hg.1, hg.2⟩⟩

/-- `V δ` is open. -/
theorem hcsg_isOpen_V' (δ : ℝ) (hδ : 0 < δ) : IsOpen (V δ) :=
  (Work.EKLContract.Lemmas.V_open_one δ hδ).1

/-- The `ν x`-mass of the shape of a plaque algebra is positive and finite. -/
theorem hcsg_shape_mass_pos_and_lt_top {μ : Measure X3} [IsProbabilityMeasure μ]
    {U : Subgroup SL3} (hU : IsHoro U) {ν : X3 → Measure SL3} {X' : Set X3}
    (hL : IsLeafwise μ U ν X') {A : MeasurableSpace X3} {Z : Set X3}
    (hA : IsPlaqueAlgebra U Z A) {x : X3} (hx : x ∈ X') (hZ : x ∈ Z) :
    0 < ν x (shape A U x) ∧ ν x (shape A U x) < ⊤ := by
  obtain ⟨-, -, -, hclbound⟩ := hA.2.2.2 x hZ
  constructor
  · obtain ⟨δ, hδ, hsub⟩ := hcsg_exists_V_subset_shape hA hZ
    have h1 : ν x (V δ ∩ (U : Set SL3)) = ν x (V δ) := by
      have hdiff : ν x (V δ \ (U : Set SL3)) = 0 :=
        le_antisymm (le_trans (measure_mono (fun g hg => hg.2))
          (le_of_eq (hL.carried x hx))) bot_le
      have hadd := measure_inter_add_sdiff (V δ) hU.1.measurableSet (μ := ν x)
      rw [hdiff, add_zero] at hadd
      exact hadd
    calc 0 < ν x (V δ) := hL.pos x hx δ hδ
      _ = ν x (V δ ∩ (U : Set SL3)) := h1.symm
      _ ≤ ν x (shape A U x) := measure_mono hsub
  · obtain ⟨C, hC⟩ := hclbound
    have hbox : IsCompact {g : SL3 | ∀ p q : Fin 3, -(|C| + 1) ≤ g p q ∧ g p q ≤ |C| + 1} :=
      Work.EKLProd.sl3EntryBox_compact (fun _ _ => -(|C| + 1)) (fun _ _ => |C| + 1)
    refine lt_of_le_of_lt (measure_mono ?_) ((hL.radon x hx).lt_top_of_isCompact hbox)
    intro u hu p q
    have h1 : |u p q| ≤ |C| + 1 := le_trans (hC u hu p q) (by linarith [le_abs_self C])
    exact abs_le.mp h1

/-! ## The conditional expectation formula for the pull-back plaque algebra -/

/-- The `condexp` field of `IsLeafwise`, applied to the pulled-back plaque algebra
`comap (aDiag t ·) A`: for a bounded Borel test function, the conditional expectation w.r.t.
`comap (aDiag t ·) A` is the `ν x`-average over the shape of the pull-back atom. -/
theorem hcsg_condExp_shape_eq {μ : Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup SL3} (hU : IsHoro U) {ν : X3 → Measure SL3} {X' : Set X3}
    (hL : IsLeafwise μ U ν X') {S : Work.EKLRelCross.MSAlg} {Z : Set X3}
    (hA : IsPlaqueAlgebra U Z S.m) (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving (fun y : X3 => aDiag t • y) μ μ)
    (hZ : μ Zᶜ = 0)
    (f : X3 → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ y, |f y| ≤ C) :
    ∀ᵐ x ∂μ, MeasureTheory.condExp
        (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) μ f x =
      (∫ u in shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) U x, f (u • x) ∂(ν x))
        / (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) U x)).toReal := by
  have hAZ : MeasurableSet Z := hA.1 Z hA.2.2.1
  have hTZ : μ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl, hmp.measure_preimage hAZ.compl.nullMeasurableSet]
    exact hZ
  have hres : μ.restrict ((fun y : X3 => aDiag t • y) ⁻¹' Z) = μ :=
    MeasureTheory.Measure.restrict_eq_self_of_ae_mem (by rw [MeasureTheory.ae_iff]; exact hTZ)
  have hfield := hL.condexp ((fun y : X3 => aDiag t • y) ⁻¹' Z)
    (MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m) (hcsg_comapPlaqueAlg hU hA t) f hf hfb
  rw [← hres]
  filter_upwards [hfield] with x hx
  exact hx

/-! ## The equivariance of the shape masses along a leaf -/

/-- **Pisa 7.16, shape form**: for two points `x` and `u • x` of one leaf that lie in the same
atom of the pull-back algebra `comap (aDiag t ·) A`, the `ν`-mass of the shape of the pull-back
atom, after normalisation, is the same at both points. -/
theorem hcsg_equivariant_shape_mass {μ : Measure X3} {U : Subgroup SL3} {ν : X3 → Measure SL3}
    {X' : Set X3} (hL : IsLeafwise μ U ν X') (A : MeasurableSpace X3) {t : Fin 3 → ℝ}
    {x : X3} {u : SL3} (hx : x ∈ X') (huU : u ∈ U) (hux : u • x ∈ X')
    (hu : u • x ∈ atom (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) x)
    (hWx : MeasurableSet
      (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x))
    {B : Set X3} (hB : MeasurableSet[instMeasurableSpaceX3] B) :
    ν (u • x) (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U (u • x)
          ∩ {g : SL3 | g • (u • x) ∈ B})
        * ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)
      = ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x
          ∩ {g : SL3 | g • x ∈ B})
        * ν (u • x) (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U (u • x)) := by
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  obtain ⟨c, hc0, hctop, hceq⟩ := hL.equivariant x hx u huU hux
  have hhm : Measurable (fun g : SL3 => g * u) := (continuous_id.mul continuous_const).measurable
  have hatom : atom (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) (u • x)
      = atom (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) x := hcsg_atom_eq_of_mem hu
  have hWy : (fun g : SL3 => g * u) ⁻¹'
      (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)
      = shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U (u • x) := by
    ext g
    simp only [Set.mem_preimage, shape, Set.mem_ofPred_eq, hatom, mul_smul]
    constructor
    · rintro ⟨hgu, hgx⟩
      refine ⟨?_, hgx⟩
      have h := U.mul_mem hgu (U.inv_mem huU)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h
    · rintro ⟨hgU, hgy⟩
      exact ⟨U.mul_mem hgU huU, hgy⟩
  have hWy' : (fun g : SL3 => g * u) ⁻¹'
      (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x ∩ {g | g • x ∈ B})
      = shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U (u • x)
          ∩ {g | g • (u • x) ∈ B} := by
    rw [Set.preimage_inter, hWy]
    congr 1
    ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, mul_smul]
  have hcont : Continuous (fun g : SL3 => g • x) := continuous_id.smul continuous_const
  have hmeas1 : MeasurableSet
      (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x ∩ {g | g • x ∈ B}) :=
    hWx.inter (hB.preimage hcont.measurable)
  have h1 : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x
        ∩ {g | g • x ∈ B})
      = c * ν (u • x) (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U (u • x)
          ∩ {g | g • (u • x) ∈ B}) := by
    rw [hceq, Measure.smul_apply, smul_eq_mul, Measure.map_apply hhm hmeas1, hWy']
  have h2 : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)
      = c * ν (u • x) (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U (u • x)) := by
    rw [hceq, Measure.smul_apply, smul_eq_mul, Measure.map_apply hhm hWx, hWy]
  rw [h1, h2]
  ac_rfl

/-! ## The pointwise surprisal of an `A`-atom inside its pull-back atom -/

/-- The ratio of the `ν`-mass of the `A`-atom to that of the pull-back
`comap (aDiag t ·) A`-atom.  Its negative logarithm is the pointwise "surprisal" of the `A`-atom
in the conditional measure of `comap (aDiag t ·) A`. -/
def hcsg_shapeRatio (A : MeasurableSpace X3) (U : Subgroup SL3) (ν : X3 → Measure SL3)
    (t : Fin 3 → ℝ) (x : X3) : ℝ :=
  (ν x (shape A U x)).toReal
    / (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal

/-- The pointwise surprisal. -/
def hcsg_shapeInfo (A : MeasurableSpace X3) (U : Subgroup SL3) (ν : X3 → Measure SL3)
    (t : Fin 3 → ℝ) (x : X3) : ℝ :=
  -Real.log (hcsg_shapeRatio A U ν t x)

/-! ## `ν`-mass of the conjugated box -/

/-- The mass of `conjBox U t` is positive and finite. -/
theorem hcsg_mass_conjBox_pos_and_lt_top {μ : Measure X3} {U : Subgroup SL3} (hU : IsHoro U)
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X') (t : Fin 3 → ℝ)
    {x : X3} (hx : x ∈ X') :
    0 < ν x (conjBox U t) ∧ ν x (conjBox U t) < ⊤ := by
  obtain ⟨δ, hδ, hsub⟩ := conjBox_nhds hU t
  have h1 : ν x (V δ ∩ (U : Set SL3)) = ν x (V δ) := by
    have hdiff : ν x (V δ \ (U : Set SL3)) = 0 :=
      le_antisymm (le_trans (measure_mono (fun g hg => hg.2))
        (le_of_eq (hL.carried x hx))) bot_le
    have hadd := measure_inter_add_sdiff (V δ) hU.1.measurableSet (μ := ν x)
    rw [hdiff, add_zero] at hadd
    exact hadd
  constructor
  · calc 0 < ν x (V δ) := hL.pos x hx δ hδ
      _ = ν x (V δ ∩ (U : Set SL3)) := h1.symm
      _ ≤ ν x (conjBox U t) := measure_mono (fun g hg => hsub g hg.1 hg.2)
  · exact (hL.radon x hx).lt_top_of_isCompact (isCompact_conjBox hU t)

/-! ## The covariance identity (Pisa 7.16/7.18) in mass form -/

/-- **The pointwise identity of Pisa 7.34**: `ν x (shape (comap a A) U x) · ν (a x) (conjBox U t)
= ν (a x) (shape A U (a x))`. -/
theorem hcsg_mass_shape_mul_conjBox {μ : Measure X3} {U : Subgroup SL3} (hU : IsHoro U)
    {ν : X3 → Measure SL3} {X' X'' : Set X3} (hL : IsLeafwise μ U ν X')
    (hcov : ACovariant ν X'') {A : MeasurableSpace X3} {t : Fin 3 → ℝ} {x : X3}
    (hxX' : x ∈ X') (hxX'' : x ∈ X'')
    (hyX' : aDiag t • x ∈ X') (hyX'' : aDiag t • x ∈ X'')
    (hC : MeasurableSet
      (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)) :
    ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) * ν (aDiag t • x)
        (conjBox U t)
      = ν (aDiag t • x) (shape A U (aDiag t • x)) := by
  have hstep := covariant_step hL hcov (measurableSet_box1 hU) t
    (show aDiag t • x ∈ X' ∩ X'' from ⟨hyX', hyX''⟩)
    (show aDiag (-t) • (aDiag t • x) ∈ X' ∩ X'' from by
      rw [aDiag_smul_mul, neg_add_cancel, aDiag_zero, one_smul]; exact ⟨hxX', hxX''⟩)
    (hC := hC)
  have hneg : conjBy t (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)
      = shape A U (aDiag t • x) := by
    rw [hcsg_shape_comap_eq hU A t x, ← conjBy_add, add_neg_cancel, conjBy_zero]
  rw [hneg, show aDiag (-t) • (aDiag t • x) = x from by
      rw [aDiag_smul_mul, neg_add_cancel, aDiag_zero, one_smul]] at hstep
  exact hstep

/-! ## The pointwise identity for the surprisal -/

/-- Pushing an a.e. statement through a measure-preserving map. -/
theorem hcsg_ae_smul_of_ae {μ : Measure X3} {f : X3 → X3}
    (hmp : MeasureTheory.MeasurePreserving f μ μ) {p : X3 → Prop} (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ x ∂μ, p (f x) := by
  have h1 : ∀ᵐ x ∂μ.map f, p x := by rw [hmp.map_eq]; exact h
  exact MeasureTheory.ae_of_ae_map hmp.aemeasurable h1

/-- **Pisa 7.34/7.35** in pointwise form: the surprisal of the `A`-atom at `x` inside its
`comap (aDiag t ·) A`-atom equals `ψ (a x) - ψ x + growthFun U ν t (a x)`. -/
theorem hcsg_shapeInfo_eq {μ : Measure X3} [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup SL3}
    (hU : IsHoro U) {ν : X3 → Measure SL3} {X' X'' : Set X3} (hL : IsLeafwise μ U ν X')
    (hcov : ACovariant ν X'') (hX'' : μ X''ᶜ = 0) {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving (fun y : X3 => aDiag t • y) μ μ)
    {A : MeasurableSpace X3} {Z : Set X3} (hA : IsPlaqueAlgebra U Z A) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, hcsg_shapeInfo A U ν t x =
      Real.log ((ν (aDiag t • x) (shape A U (aDiag t • x))).toReal)
        - Real.log ((ν x (shape A U x)).toReal) + growthFun U ν t (aDiag t • x) := by
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by rw [MeasureTheory.ae_iff]; exact hL.conull
  have hX''ae : ∀ᵐ x ∂μ, x ∈ X'' := by rw [MeasureTheory.ae_iff]; exact hX''
  have hZae : ∀ᵐ x ∂μ, x ∈ Z := by rw [MeasureTheory.ae_iff]; exact hZ
  have hTX' : ∀ᵐ x ∂μ, aDiag t • x ∈ X' := hcsg_ae_smul_of_ae hmp hX'
  have hTX'' : ∀ᵐ x ∂μ, aDiag t • x ∈ X'' := hcsg_ae_smul_of_ae hmp hX''ae
  have hTZ : ∀ᵐ x ∂μ, aDiag t • x ∈ Z := hcsg_ae_smul_of_ae hmp hZae
  filter_upwards [hX', hX''ae, hZae, hTX', hTX'', hTZ] with x hxX' hxX'' hxZ hTxX' hTxX'' hTxZ
  have hW := hcsg_shape_mass_pos_and_lt_top hU hL (hcsg_comapPlaqueAlg hU hA t) hxX' hTxZ
  have hV := hcsg_shape_mass_pos_and_lt_top hU hL hA hxX' hxZ
  have hTV := hcsg_shape_mass_pos_and_lt_top hU hL hA hTxX' hTxZ
  have hCB := hcsg_mass_conjBox_pos_and_lt_top hU hL t hTxX'
  have hCmeas : MeasurableSet
      (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) :=
    hcsg_measurableSet_shape hU (hcsg_comapPlaqueAlg hU hA t) hTxZ
  have hmass := hcsg_mass_shape_mul_conjBox hU hL hcov hxX' hxX'' hTxX' hTxX'' hCmeas
  have haW : (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal
      ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt hW.1, ne_of_lt hW.2⟩
  have haV : (ν x (shape A U x)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt hV.1, ne_of_lt hV.2⟩
  have haCB : (ν (aDiag t • x) (conjBox U t)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt hCB.1, ne_of_lt hCB.2⟩
  have hlog : Real.log ((ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal)
        + Real.log ((ν (aDiag t • x) (conjBox U t)).toReal)
      = Real.log ((ν (aDiag t • x) (shape A U (aDiag t • x))).toReal) := by
    rw [← Real.log_mul haW haCB, ← ENNReal.toReal_mul, hmass]
  rw [hcsg_shapeInfo, hcsg_shapeRatio, Real.log_div haV haW, growthFun]
  linarith [hlog]

/-! ## Transfer of `μ`-null sets to the leaves -/

/-- **The local form of Pisa §8.9**: a `μ`-null measurable set is `ν x`-null along the shape of
the pull-back atom. -/
theorem hcsg_ae_shape_inter_null {μ : Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup SL3} (hU : IsHoro U) {ν : X3 → Measure SL3} {X' : Set X3}
    (hL : IsLeafwise μ U ν X') {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving (fun y : X3 => aDiag t • y) μ μ)
    {M : Set X3} (hM : MeasurableSet M) (hM0 : μ M = 0)
    {A : MeasurableSpace X3} {Z : Set X3} (hA : IsPlaqueAlgebra U Z A) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x
      ∩ {u : SL3 | u • x ∈ M}) = 0 := by
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  have hAZ : MeasurableSet Z := hA.1 Z hA.2.2.1
  have hTZ : μ ((fun y : X3 => aDiag t • y) ⁻¹' Z)ᶜ = 0 := by
    rw [← Set.preimage_compl, hmp.measure_preimage hAZ.compl.nullMeasurableSet]
    exact hZ
  have hTZae : ∀ᵐ x ∂μ, x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z := by
    rw [MeasureTheory.ae_iff]; exact hTZ
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by rw [MeasureTheory.ae_iff]; exact hL.conull
  set f : X3 → ℝ := M.indicator (fun _ : X3 => (1 : ℝ)) with hfdef
  have hf : Measurable f := measurable_const.indicator hM
  have hfnn : ∀ y, 0 ≤ f y := by
    intro y
    by_cases hy : y ∈ M
    · rw [hfdef, Set.indicator_of_mem hy]; norm_num
    · rw [hfdef, Set.indicator_of_notMem hy]
  have hfb : ∃ C, ∀ y, |f y| ≤ C := ⟨1, fun y => by
    rw [hfdef]
    by_cases hy : y ∈ M
    · rw [Set.indicator_of_mem hy, abs_one]
    · rw [Set.indicator_of_notMem hy, abs_zero]; norm_num⟩
  have hfield := hcsg_condExp_shape_eq hU hL hA t hmp hZ f hf hfb
  have hfint : ∫ x, f x ∂μ = 0 := by
    rw [hfdef, MeasureTheory.integral_indicator hM, MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def, hM0]
    simp
  have hInt : ∫ x, MeasureTheory.condExp
      (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) μ f x ∂μ = 0 := by
    rw [MeasureTheory.integral_condExp (hcsg_comapPlaqueAlg hU hA t).1, hfint]
  have hzero : MeasureTheory.condExp (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) μ f
      =ᵐ[μ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (MeasureTheory.condExp_nonneg (Filter.Eventually.of_forall hfnn))
      MeasureTheory.integrable_condExp).mp hInt
  filter_upwards [hfield, hzero, hTZae, hX'] with x hfx hzx hxTZ hxX
  have hW := hcsg_shape_mass_pos_and_lt_top hU hL (hcsg_comapPlaqueAlg hU hA t) hxX hxTZ
  have hden : (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal
      ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨ne_of_gt hW.1, ne_of_lt hW.2⟩
  have hratio : (∫ u in shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x,
      f (u • x) ∂(ν x))
      / (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal = 0 := by
    rw [← hfx, hzx]
    simp
  have hnum : (∫ u in shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x,
      f (u • x) ∂(ν x)) = 0 := by
    rcases div_eq_zero_iff.mp hratio with h | h
    · exact h
    · exact absurd h hden
  have hset : MeasurableSet {u : SL3 | u • x ∈ M} :=
    hM.preimage (continuous_id.smul continuous_const).measurable
  have hident : (∫ u in shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x,
        f (u • x) ∂(ν x))
      = (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x
          ∩ {u : SL3 | u • x ∈ M})).toReal := by
    have hfun : ∀ u : SL3, f (u • x)
        = ({u : SL3 | u • x ∈ M}).indicator (fun _ : SL3 => (1 : ℝ)) u := by
      intro u
      by_cases hu : u • x ∈ M
      · rw [hfdef, Set.indicator_of_mem hu,
          Set.indicator_of_mem (show u ∈ {u : SL3 | u • x ∈ M} from hu)]
      · rw [hfdef, Set.indicator_of_notMem hu,
          Set.indicator_of_notMem (show u ∉ {u : SL3 | u • x ∈ M} from hu)]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hfun)]
    rw [MeasureTheory.setIntegral_indicator hset, MeasureTheory.setIntegral_const, smul_eq_mul,
      mul_one, MeasureTheory.measureReal_def, Set.inter_comm]
  rw [hident] at hnum
  have htop : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x
      ∩ {u : SL3 | u • x ∈ M}) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hW.2
  rcases (ENNReal.toReal_eq_zero_iff _).mp hnum with h | h
  · exact h
  · exact absurd h (ne_of_lt htop)

/-! ## The conditional probability of an `A`-measurable set in shape form -/

/-- For an `A`-measurable set `S`, the `comap (aDiag t ·) A`-conditional probability of `S` is the
ratio of the `ν x`-masses of the shape of the pull-back atom intersected with `S` and of the whole
shape. -/
theorem hcsg_ae_condExp_eq_shape_ratio {μ : Measure X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup SL3} (hU : IsHoro U) {ν : X3 → Measure SL3} {X' : Set X3}
    (hL : IsLeafwise μ U ν X') {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving (fun y : X3 => aDiag t • y) μ μ)
    {S : Set X3} (hS : MeasurableSet S)
    {A : MeasurableSpace X3} {Z : Set X3} (hA : IsPlaqueAlgebra U Z A) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, MeasureTheory.condExp
        (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) μ
        (Set.indicator S (fun _ : X3 => (1 : ℝ))) x
      = (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x
            ∩ {u : SL3 | u • x ∈ S})).toReal
        / (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal := by
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  have hfmeas : Measurable (Set.indicator S (fun _ : X3 => (1 : ℝ))) :=
    measurable_const.indicator hS
  have hfb : ∃ C, ∀ y : X3, |Set.indicator S (fun _ : X3 => (1 : ℝ)) y| ≤ C :=
    ⟨1, fun y => by
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, abs_one]
      · rw [Set.indicator_of_notMem hy, abs_zero]; norm_num⟩
  have hfield := hcsg_condExp_shape_eq hU hL hA t hmp hZ
    (Set.indicator S (fun _ : X3 => (1 : ℝ))) hfmeas hfb
  filter_upwards [hfield] with x hx
  rw [hx]
  congr 1
  have hset : MeasurableSet {u : SL3 | u • x ∈ S} :=
    hS.preimage (continuous_id.smul continuous_const).measurable
  have hfun : ∀ u : SL3, Set.indicator S (fun _ : X3 => (1 : ℝ)) (u • x)
      = ({u : SL3 | u • x ∈ S}).indicator (fun _ : SL3 => (1 : ℝ)) u := by
    intro u
    by_cases hu : u • x ∈ S
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show u ∈ {u : SL3 | u • x ∈ S} from hu)]
    · rw [Set.indicator_of_notMem hu,
        Set.indicator_of_notMem (show u ∉ {u : SL3 | u • x ∈ S} from hu)]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hfun)]
  rw [MeasureTheory.setIntegral_indicator hset, MeasureTheory.setIntegral_const, smul_eq_mul,
    mul_one, MeasureTheory.measureReal_def, Set.inter_comm]


/-! ## The surprisal is nonnegative -/

/-- The atoms of a finite partition are measurable for its generated `σ`-algebra. -/
theorem hcsg_partSigma_mem {X : Type*} [mX : MeasurableSpace X] (P : FinPart X) (i : Fin P.n) :
    MeasurableSet[partSigma P] (P.parts i) :=
  MeasurableSpace.measurableSet_generateFrom ⟨i, rfl⟩

/-- The surprisal is nonnegative when the `A`-atoms refine the pull-back atoms
(`comap (aDiag t ·) A ≤ A`). -/
theorem hcsg_shapeInfo_nonneg {U : Subgroup SL3} {ν : X3 → Measure SL3} {t : Fin 3 → ℝ}
    {A : MeasurableSpace X3}
    (hdec : MeasurableSpace.comap (fun y : X3 => aDiag t • y) A ≤ A) (x : X3) :
    0 ≤ hcsg_shapeInfo A U ν t x := by
  have hsub : shape A U x ⊆ shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x := by
    rintro u ⟨huU, hux⟩
    exact ⟨huU, hcsg_atom_mono hdec x hux⟩
  rw [hcsg_shapeInfo, hcsg_shapeRatio, neg_nonneg]
  by_cases htop : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) = ⊤
  · rw [htop, ENNReal.toReal_top]
    simp
  · have hle : (ν x (shape A U x)).toReal
        ≤ (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal :=
      ENNReal.toReal_mono htop (measure_mono hsub)
    have hden0 : (0 : ℝ) ≤ (ν x (shape (MeasurableSpace.comap
        (fun y : X3 => aDiag t • y) A) U x)).toReal := ENNReal.toReal_nonneg
    rcases eq_or_lt_of_le hden0 with h0 | hpos
    · rw [h0.symm, div_zero, Real.log_zero]
    · exact Real.log_nonpos (div_nonneg ENNReal.toReal_nonneg hden0)
        ((div_le_one hpos).mpr hle)

end Work.EKLC6Core
