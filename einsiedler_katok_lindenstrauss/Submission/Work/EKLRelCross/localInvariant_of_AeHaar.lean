import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.plaque_identity_base
import Submission.Work.EKLRelCross.plaqueDensity
import Submission.Work.EKLRelCross.entropy_cs_interface
import Submission.Work.EKLRelCross.invariant_notes
import Submission.Work.EKLRelCross.free_orbits_of_contracting
import Submission.Work.EKLRelCross.horoUnimodular
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.EKLRelCross.exists_V_leftMul_subset
import Submission.Work.EKLUInv.local_invariance_of_ae_haar

/-!
# `Work.EKLRelCross.localInvariant_of_AeHaar` — local `U`-invariance from a.e. Haar leafwise
measures (Pisa 6.27 / EKL (6), (⟸) direction)

This file proves the *local* form of the (⟸) direction of clause (U4) of the EKL contract: if the
leafwise measures of `(μ, U)` are a.e. right-`U`-invariant (`AeHaar`), then `μ` is invariant under
every `u ∈ U` sufficiently close to `1`.

## Structure

* `PlaqueIdAt`, `AeHaarAt`, `FreeAt`, `Good`: the pointwise forms of the three a.e. properties used
  by the argument, and the conull set `Good` where all of them hold (see
  `Work.EKLRelCross.plaque_identity_base` for `PlaqueId`, `ae_free_orbit` for the freeness and the
  hypothesis `hae` for `AeHaar`).
* `goodPlaqueMassInvariant` (**Claim A**, Pisa 6.27 step 2): at a good base point `y`, every
  measurable `A` contained in a bounded plaque `C • y` has `u`-invariant `μ`-mass.  The proof is
  the two-box computation: `PlaqueId` at the boxes `V δ ∩ U ⊆ V δ' ∩ U` of the same base point
  shows that `c := μ ((V δ ∩ U) • y) / ν y (V δ ∩ U)` does not depend on the box, and
  `S_{u • A} = u • S_A` together with the left-`U`-invariance of `ν y` (`horoUnimodular`) gives
  `μ (u • A) = c * ν y (S_A) = μ A`.
* `localInvariant_of_AeHaar`: the target, obtained from Claim A by the globalization argument
  (`goodPlaqueInvariance_global`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

/-- Pointwise form of `PlaqueId`: the local product structure of `μ` along the `U`-plaque of the
base point `x₀`. -/
def PlaqueIdAt (μ : Measure X3) (U : Subgroup SL3) (ν : X3 → Measure SL3) (x₀ : X3) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ A : Set X3, MeasurableSet A →
    ν x₀ (V ε ∩ (U : Set SL3)) * μ (A ∩ Work.EKLComp.orbitPlaque U x₀ ε)
      = μ (Work.EKLComp.orbitPlaque U x₀ ε) *
        ν x₀ {u : SL3 | u ∈ V ε ∩ (U : Set SL3) ∧ u • x₀ ∈ A}

/-- Pointwise form of `AeHaar`: the leafwise measure at `x` is right-`U`-invariant. -/
def AeHaarAt (U : Subgroup SL3) (ν : X3 → Measure SL3) (x : X3) : Prop :=
  ∀ u ∈ U, (ν x).map (fun g : SL3 => g * u) = ν x

/-- The `U`-orbit of `x` is free. -/
def FreeAt (U : Subgroup SL3) (x : X3) : Prop :=
  ∀ u ∈ U, u • x = x → u = 1

/-- The conull set of base points at which every hypothesis of the local argument holds. -/
def Good (μ : Measure X3) (U : Subgroup SL3) (ν : X3 → Measure SL3) (X' : Set X3) : Set X3 :=
  {x | x ∈ X' ∧ PlaqueIdAt μ U ν x ∧ AeHaarAt U ν x ∧ FreeAt U x}

/-- Injectivity of the orbit map on `U`, from freeness at the base point. -/
theorem injOn_of_free {U : Subgroup SL3} {x : X3} (h : FreeAt U x) :
    ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ := by
  intro u₁ h₁ u₂ h₂ heq
  have hmem : u₂⁻¹ * u₁ ∈ U := U.mul_mem (U.inv_mem h₂) h₁
  have hfix : (u₂⁻¹ * u₁) • x = x := by rw [mul_smul, heq, inv_smul_smul]
  have h1 : u₂⁻¹ * u₁ = 1 := h _ hmem hfix
  calc u₁ = u₂ * (u₂⁻¹ * u₁) := (mul_inv_cancel_left u₂ u₁).symm
    _ = u₂ * 1 := by rw [h1]
    _ = u₂ := mul_one u₂

/-- **Claim A (local mass invariance on a good plaque; Pisa 6.27, step 2).**  Let `y` be a base
point at which the local product structure, the freeness of the `U`-orbit and the right-`U`-
invariance of `ν y` all hold.  Let `C ⊆ U` be a box contained in `V δ`, and let `u ∈ U` satisfy
`u • C ⊆ V δ`.  Then every measurable `A` contained in the plaque `C • y` has `u`-invariant
`μ`-mass.

Proof.  `PlaqueId` at the *single* box `V δ ∩ U` gives, for every measurable `D ⊆ P := (V δ ∩ U) • y`,
`ν y (V δ ∩ U) * μ D = μ P * ν y S_D`, where `S_D = {v ∈ U | v • y ∈ D}` (the parameter set of `D`,
which lies in `V δ ∩ U` by freeness, so that the restriction "`v ∈ V δ ∩ U`" is automatic).  The two
parameter sets of `A` and of `u • A` are linked by `S_{u • A} = u • S_A`, and `ν y` is
left-`U`-invariant (`horoUnimodular` applies to the right-invariant `ν y`, carried by the
unimodular `U`).  Hence
`ν y (V δ ∩ U) * μ (u • A) = μ P * ν y (S_{u • A}) = μ P * ν y (S_A) = ν y (V δ ∩ U) * μ A`,
and cancelling the positive finite factor `ν y (V δ ∩ U)` gives the claim. -/
theorem goodPlaqueMassInvariant {U : Subgroup SL3} (hU : IsHoro U) {μ : Measure X3}
    [IsProbabilityMeasure μ] {ν : X3 → Measure SL3} {X' : Set X3} {y : X3}
    (hy : y ∈ Good μ U ν X')
    (hradon : IsFiniteMeasureOnCompacts (ν y)) (hcar : ν y (U : Set SL3)ᶜ = 0)
    (hne : ν y ≠ 0) (hpos : ∀ δ : ℝ, 0 < δ → 0 < ν y (V δ))
    {C : Set SL3} (hCU : C ⊆ (U : Set SL3))
    {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') (hδδ' : δ ≤ δ') (hCδ : C ⊆ V δ)
    {u : SL3} (hu : u ∈ U) (huC : ∀ g ∈ C, u * g ∈ V δ')
    {A : Set X3} (hA : MeasurableSet A) (hAsub : A ⊆ (fun g : SL3 => g • y) '' C) :
    μ ((fun x : X3 => u • x) '' A) = μ A := by
  obtain ⟨-, hPId, hAe, hfree⟩ := hy
  have hinj := injOn_of_free hfree
  obtain ⟨hleft, -⟩ := Work.EKLRelCross.horoUnimodular hU (ν y) hradon hcar hne hAe
  haveI := hradon
  set B : Set SL3 := V δ' ∩ (U : Set SL3) with hB
  set P : Set X3 := Work.EKLComp.orbitPlaque U y δ' with hP
  set S : Set SL3 := {v : SL3 | v ∈ U ∧ v • y ∈ A} with hS
  -- `A ⊆ P`
  have hCδ' : C ⊆ V δ' := by
    intro g hg i j
    exact lt_of_lt_of_le (hCδ hg i j) hδδ'
  have hAP : A ⊆ P := by
    rintro z hz
    obtain ⟨g, hgC, rfl⟩ := hAsub hz
    exact ⟨g, ⟨hCδ' hgC, hCU hgC⟩, rfl⟩
  -- the parameter set of a set contained in `P` lies in `B`
  have hSsub : ∀ {D : Set X3}, D ⊆ P → {v : SL3 | v ∈ U ∧ v • y ∈ D} ⊆ B := by
    rintro D hDP v ⟨hvU, hvD⟩
    obtain ⟨w, hw, hwv⟩ := hDP hvD
    have hwv' : w = v := hinj w hw.2 v hvU (show w • y = v • y from hwv)
    rw [← hwv']; exact hw
  -- `u • A ⊆ P`
  have huAP : (fun x : X3 => u • x) '' A ⊆ P := by
    rintro z ⟨a, ha, haz⟩
    obtain ⟨g, hgC, hga⟩ := hAsub ha
    refine ⟨u * g, ⟨huC g hgC, U.mul_mem hu (hCU hgC)⟩, ?_⟩
    show (u * g) • y = z
    rw [mul_smul, show g • y = a from hga, ← haz]
  -- the `PlaqueId` identity at the box `δ`, for a set contained in `P`
  have key : ∀ {D : Set X3}, MeasurableSet D → D ⊆ P →
      ν y B * μ D = μ P * ν y {v : SL3 | v ∈ U ∧ v • y ∈ D} := by
    intro D hD hDP
    have h1 := hPId δ' hδ' D hD
    have hSDeq : {u : SL3 | u ∈ V δ' ∩ (U : Set SL3) ∧ u • y ∈ D}
        = {v : SL3 | v ∈ U ∧ v • y ∈ D} := by
      ext v; constructor
      · rintro ⟨hv, hvD⟩; exact ⟨hv.2, hvD⟩
      · rintro ⟨hvU, hvD⟩; exact ⟨hSsub hDP ⟨hvU, hvD⟩, hvD⟩
    rw [hSDeq, ← hB, ← hP, Set.inter_eq_left.mpr hDP] at h1
    exact h1
  have e1 : ν y B * μ A = μ P * ν y S := key hA hAP
  have huAmeas : MeasurableSet ((fun x : X3 => u • x) '' A) :=
    (Homeomorph.measurableEmbedding
      (Homeomorph.smul (G := SL3) (α := X3) u)).measurableSet_image' hA
  have e2 : ν y B * μ ((fun x : X3 => u • x) '' A)
      = μ P * ν y {v : SL3 | v ∈ U ∧ v • y ∈ (fun x : X3 => u • x) '' A} :=
    key huAmeas huAP
  -- the parameter set of `u • A` is the left translate of `S`
  have hSu : {v : SL3 | v ∈ U ∧ v • y ∈ (fun x : X3 => u • x) '' A}
      = (fun g : SL3 => u * g) '' S := by
    ext v; constructor
    · rintro ⟨hvU, a, ha, hav⟩
      refine ⟨u⁻¹ * v, ⟨U.mul_mem (U.inv_mem hu) hvU, ?_⟩, mul_inv_cancel_left u v⟩
      have hkey : (u⁻¹ * v) • y = a := by
        have h1 : u • ((u⁻¹ * v) • y) = u • a := by
          rw [← mul_smul, mul_inv_cancel_left]
          exact (show u • a = v • y from hav).symm
        calc (u⁻¹ * v) • y = u⁻¹ • (u • ((u⁻¹ * v) • y)) := by rw [inv_smul_smul]
          _ = u⁻¹ • (u • a) := by rw [h1]
          _ = a := by rw [inv_smul_smul]
      rw [hkey]; exact ha
    · rintro ⟨w, ⟨hwU, hwA⟩, rfl⟩
      refine ⟨U.mul_mem hu hwU, w • y, hwA, ?_⟩
      exact (mul_smul u w y).symm
  -- left-`U`-invariance of `ν y` under the map `g ↦ u * g`
  have hSmeas : MeasurableSet S :=
    hU.1.measurableSet.inter (hA.preimage (by fun_prop : Measurable fun v : SL3 => v • y))
  have hSuMeas : MeasurableSet ((fun g : SL3 => u * g) '' S) :=
    (Homeomorph.measurableEmbedding
      (Homeomorph.mulLeft u)).measurableSet_image' hSmeas
  have h5 : ν y ((fun g : SL3 => u * g) '' S) = ν y S := by
    have hmap := congrArg (fun (m : Measure SL3) => m ((fun g : SL3 => u * g) '' S)) (hleft u hu)
    rw [Measure.map_apply (by fun_prop : Measurable fun g : SL3 => u * g) hSuMeas] at hmap
    have hpre : (fun g : SL3 => u * g) ⁻¹' ((fun g : SL3 => u * g) '' S) = S := by
      ext g; constructor
      · rintro ⟨w, hw, hwg⟩
        rw [← show w = g from mul_left_cancel hwg]; exact hw
      · intro hg; exact ⟨g, hg, rfl⟩
    rw [hpre] at hmap
    exact hmap.symm
  -- positivity and finiteness of the box mass
  have hBne : ν y B ≠ 0 := by
    have hV : ν y (V δ') ≠ 0 := ne_of_gt (hpos δ' hδ')
    have hEq : ν y B = ν y (V δ') := by
      have hnull : ν y (V δ' ∩ (U : Set SL3)ᶜ) = 0 :=
        measure_mono_null Set.inter_subset_right hcar
      have hun : V δ' = (V δ' ∩ (U : Set SL3)) ∪ (V δ' ∩ (U : Set SL3)ᶜ) := by
        ext g; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]; tauto
      have hdisj : Disjoint (V δ' ∩ (U : Set SL3)) (V δ' ∩ (U : Set SL3)ᶜ) := by
        rw [Set.disjoint_left]; rintro g ⟨-, hgU⟩ ⟨-, hgU'⟩; exact hgU' hgU
      rw [hun, measure_union hdisj]
      · rw [hnull, add_zero]
      · exact (Work.EKLComp.isOpen_V δ').measurableSet.inter hU.1.measurableSet.compl
    rw [hEq]; exact hV
  have hBlt : ν y B ≠ ⊤ := by
    have hK : IsCompact {g : SL3 | ∀ i j, (1 : Matrix (Fin 3) (Fin 3) ℝ) i j - δ' ≤ g i j ∧
        g i j ≤ (1 : Matrix (Fin 3) (Fin 3) ℝ) i j + δ'} :=
      Work.EKLProd.sl3EntryBox_compact _ _
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) hK.measure_lt_top)
    intro g hg i j
    have h := hg.1 i j
    rw [abs_lt] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  -- conclude
  have : ν y B * μ ((fun x : X3 => u • x) '' A) = ν y B * μ A := by
    rw [e2, hSu, h5, ← e1]
  refine (ENNReal.mul_left_inj hBne hBlt).mp ?_
  simpa only [mul_comm] using this

/-- **Local invariance on a bounded orbit plaque.**  At a good base point `y`, for every `δ > 0`
and every `u ∈ U`, the `μ`-mass of every measurable `A ⊆ (V δ ∩ U) • y` is `u`-invariant.

This is the form of Claim A used by the globalization: the *whole* bounded plaque (not only a
small box inside it) is invariant, with no smallness restriction on `u ∈ U`.  The box transfer
`u • (V δ ∩ U) ⊆ V δ₁` is supplied by `exists_V_leftMul_subset`, and
`goodPlaqueMassInvariant` is applied with the box `V (max δ δ₁) ∩ U`. -/
theorem plaque_smul_massInvariant {U : Subgroup SL3} (hU : IsHoro U) {μ : Measure X3}
    [IsProbabilityMeasure μ] {ν : X3 → Measure SL3} {X' : Set X3} {y : X3}
    (hy : y ∈ Good μ U ν X')
    (hradon : IsFiniteMeasureOnCompacts (ν y)) (hcar : ν y (U : Set SL3)ᶜ = 0)
    (hne : ν y ≠ 0) (hpos : ∀ δ : ℝ, 0 < δ → 0 < ν y (V δ))
    {δ : ℝ} (hδ : 0 < δ) {u : SL3} (hu : u ∈ U)
    {A : Set X3} (hA : MeasurableSet A)
    (hAsub : A ⊆ (fun g : SL3 => g • y) '' (V δ ∩ (U : Set SL3))) :
    μ ((fun x : X3 => u • x) '' A) = μ A := by
  obtain ⟨δ₁, hδ₁, hbox⟩ := Work.EKLRelCross.exists_V_leftMul_subset u hδ
  set Δ : ℝ := max δ δ₁ with hΔ
  have hΔpos : 0 < Δ := lt_of_lt_of_le hδ (le_max_left _ _)
  have hδΔ : δ ≤ Δ := le_max_left _ _
  have huC : ∀ g ∈ V δ ∩ (U : Set SL3), u * g ∈ V Δ := by
    intro g hg i j
    exact lt_of_lt_of_le (hbox g hg.1 i j) (le_max_right _ _)
  exact goodPlaqueMassInvariant hU hy hradon hcar hne hpos (fun g hg => hg.2) hδ hΔpos hδΔ
    (fun _ hg => hg.1) hu huC hA hAsub

/-! ## The globalization (remaining work)

`goodPlaqueMassInvariant` + `plaque_smul_massInvariant` establish the *local* content: for `u ∈ U`
and a good base point `y`, the maps `x ↦ u • x` preserve the `μ`-mass of every measurable subset of
every bounded plaque `(V δ ∩ U) • y`.  Writing `λ := (u • ·)_* μ`, this says

* `λ ⌞ P = μ ⌞ P` for every good plaque `P = (V δ ∩ U) • y`, `y ∈ ` the conull set
  `Good μ U ν X'`.

What remains is to globalize.  Two observations made in the analysis:

1. **The `condexp` route.**  Let `h := 1_{u⁻¹A} - 1_A` (bounded).  For any plaque algebra `(Z, m)`
   whose atoms are bounded plaques based at `μ`-a.e. good points, the `condexp` field gives
   `condExp m (μ⌞Z) h x = (1/μ([x]_m)) ∫_{[x]_m} h ∂μ` for `μ`-a.e. `x` with `μ([x]_m) > 0`; the
   integral on the right vanishes by the local statement.  Hence `∫_Z h ∂μ = 0` **for every plaque
   algebra all of whose atoms have positive `μ`-mass**.  The obstruction is exactly the atoms of
   `μ`-mass zero: on those the `condexp` field is vacuous (the conditional measure is not the
   normalized atom integral), so a measure component carried on such plaques is invisible to the
   argument.  (The a.e. statement says nothing when the atoms of the chosen algebra are null.)

2. **The maximal disjoint family.**  Zorn's lemma gives a maximal pairwise disjoint family `𝒫` of
   good plaques at scale `δ`; with `W := ⋃𝒫` one has `(V s) • W ⊇ Good μ U ν X'` for `s = s(δ)`
   (every plaque meets `W` by maximality), hence `μ ((V s) • W) = 1`.  The subfamily `W₊` of plaques
   of positive `μ`-mass is **countable** (a disjoint family of positive-measure sets in a
   probability space is countable), and decomposing `(V s) • W₊ = ⋃ₙ Kₙ • W₊` with `Kₙ ⊆ Uball s`
   compact and disjointifying gives countably many pieces, each contained in a *good* plaque (the
   boxes `Kₙ · (V δ ∩ U)` are bounded).  This yields `λ ⌞ ((V s) • W₊) = μ ⌞ ((V s) • W₊)`, but
   says nothing about `(V s) • W₀`, `W₀` the union of the null plaques.  (Note: the union of an
   uncountable disjoint family has no general additivity identity — Lebesgue measure on `[0,1]` is
   the union of its points — so the countable subfamily `𝒫₊` must genuinely be used.)

3. **Why `hcontr` is needed.**  In the model `X = ℝ²/ℤ²`, `U` the vertical flow and `α` the
   horizontal flow (which does **not** contract `U`), the measure `μ = ½·Leb + ½·(Lebesgue on the
   horizontal circle {y = 0})` satisfies the analogues of `PlaqueId`, `AeHaar` and the local
   statement (all its plaques have positive mass), yet is not `U`-invariant: the horizontal circle
   is not.  So the local statement alone cannot imply the globalization; the contraction of `U`
   along `α^{t₀}` (equivalently: the `A`-covariance of the leafwise measures) must enter.  The
   intended mechanism is the **flow box**: disintegrate `μ` along the `U`-plaques of a chart whose
   transversal is a slice complementary to `Lie U`; the conditional measures are the
   `ν`-pushforwards, and the relation between the transversal measures of nested boxes carries the
   fibre ratio `ν y (V δ ∩ U) / ν y (V δ' ∩ U)`, which cancels in the two-box computation (this
   cancellation, worked out above, is what makes `μ (u • A) = μ A` for `A` inside a *box*), while
   the `U`-action fixes the transversal coordinate.  Countably many such boxes are open and cover a
   conull set.

**How the globalization is actually completed.**  The obstruction of point 2 is defeated by the
*bigness* of the atoms of the flower algebras (Pisa Cor. 6.15, `Work.EKLUInv.bigAtoms_flowers`):
there are countably many plaque algebras `(Z n, m n)` with measurable bases `G n` covering `X₃` up
to a null set such that at every `x ∈ G n` the whole `1`-plaque `V 1 ∩ U` lies in the shape of
`m n` at `x`.  For such an algebra the set `Θ n = {y ∈ Z n | u • y ∈ [y]_{m n}}` is measurable,
contains `G n` (`u ∈ V (1/4) ⊆ V 1`), and every measurable `A ⊆ Θ n` satisfies `μ (u • A) = μ A`:
the `condexp` axiom of `IsLeafwise`, applied once to `1_A` and once to `1_{u • A}`, turns the two
integrals into leafwise averages which agree by the inner-region identity (the `u`-preimage of a
shape meets the parameter set of `A` exactly as the shape itself does) and by the left-`U`
invariance of `ν`; see `Work.EKLUInv.good_of_atom`.  Since the `Θ n` are *countably* many and
cover `μ`-a.e. point, disjointifying them and using countable additivity gives the full
`MeasurePreserving (u •) μ μ` (`Work.EKLUInv.measurePreserving_of_countable_good`).  The
countability of the cover — available because the flower bases are indexed by a countable basis of
`X₃` — is what defeats the null-plaque obstruction of point 2; no openness of the `Θ n` is needed
(and is unavailable, the free locus having empty interior).

-/

/-- **Target lemma**: `AeHaar` implies local `U`-invariance of `μ` (Pisa 6.27, (⟸) direction). -/
theorem localInvariant_of_AeHaar (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3)
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hae : Work.EKLRelCross.AeHaar μ U ν) :
    ∃ ε > 0, ∀ u ∈ U, u ∈ Work.EKLContract.V ε →
      MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => u • x) μ μ := by
  refine ⟨1 / 4, by norm_num, fun u hu huV => ?_⟩
  -- geometry: countably many big-atom flowers (Pisa Cor. 6.15)
  obtain ⟨Z, G, m, hpla, hG, hcov, hshp⟩ :=
    Work.EKLUInv.bigAtoms_flowers h2 μ U hU t0 ht0 hcontr 1 (by norm_num)
  have huV1 : u ∈ V 1 ∩ (U : Set SL3) :=
    ⟨fun i j => lt_trans (huV i j) (by norm_num), hu⟩
  -- globalize: the good sets {y ∈ Z n | u • y ∈ [y]_{m n}} are countably many, cover a.e., and
  -- every measurable subset of each has u-invariant μ-mass
  refine Work.EKLUInv.measurePreserving_of_countable_good (μ := μ) (u := u)
    (fun n : ℕ => {y : X3 | y ∈ Z n ∧ u • y ∈ atom (m n) y}) ?_ ?_ ?_
  · intro n
    have h1 : MeasurableSet {y : X3 | u • y ∈ atom (m n) y} :=
      Work.EKLComp.measurableSet_smul_mem_atom ⟨m n⟩ (hpla n).1 (hpla n).2.1 u
    exact ((hpla n).1 _ (hpla n).2.2.1).inter h1
  · intro n A hA hAsub
    exact Work.EKLUInv.good_of_atom (μ := μ) hU hL hae hu (⟨m n⟩ : Work.EKLComp.SigAlg)
      (hpla n) hA (fun a ha => ⟨(hAsub ha).1, (hAsub ha).2⟩)
  · have hsub : (⋃ n, G n) ⊆ ⋃ n, {y : X3 | y ∈ Z n ∧ u • y ∈ atom (m n) y} := by
      intro x hx
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨n, (hG n).2 hxn, (hshp n x hxn huV1).2⟩
    exact MeasureTheory.measure_mono_null (Set.compl_subset_compl.mpr hsub) hcov

end Work.EKLRelCross
