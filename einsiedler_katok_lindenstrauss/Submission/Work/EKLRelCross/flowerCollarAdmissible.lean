import Mathlib
import Submission.Work.EKLRelCross.flower
import Submission.Work.EKLRelCross.atom_flower_local
import Submission.Work.EKLRelCross.flower_plaqueAlgebra_bdd
import Submission.Work.EKLRelCross.horoUnimodular
import Submission.Work.EKLRelCross.entropy_cs_interface
import Submission.Work.EKLRelCross.pushforward_relation_of_condExp
import Submission.Work.EKLUInv.local_invariance_of_ae_haar

/-!
# `Work.EKLRelCross.flowerCollarAdmissible` — the `r`-collar of a flower is admissible

Let `U ≤ SL₃(ℝ)` be horospherical, `μ` a probability measure on `X₃ = SL₃(ℝ)/SL₃(ℤ)` with a
system `ν` of leafwise measures (`IsLeafwise μ U ν X'`) that is a.e. right-`U`-invariant
(`AeHaar`), `C` a `V b`-cross section of the `U`-flow whose `U`-orbits are free, and let
`m = flowerSigma U t C W` be the flower σ-algebra of `C` at scale `t > r`.

The *collar* of `C` at scale `r` is

`Coll = {z | ∃ c ∈ C, ∃ σ ∈ V r ∩ U, u * σ ∈ V r ∩ U, z = σ • c}`,

i.e. the two-point window of the `u`-translate of a plaque point (`u ∈ U ∩ V (1/4)`).

**Claim.**  Every measurable `A ⊆ Coll` satisfies `μ (u • A) = μ A`.

The reason is that on the free points of `C` the atoms of `m` are the plaques
`(V t ∩ U) • c` (`atom_flower_local`), and both the points `σ • c` of the collar and their
`u`-translates `u σ • c` lie in the *same* atom (both `σ` and `u σ` lie in `V r ∩ U ⊆ V t ∩ U`,
and `r < t`).  Hence every point of `A` is "good" for `u` in the sense of the local admissibility
theorem `Work.EKLUInv.good_of_atom` (the measure-theoretic content of Pisa 6.27, direction
`⟸`), applied to the plaque algebra `(Z, m)` with `Z = ⋃_{c ∈ C} [c]_m`; the fact that `Z` can be
written with the *free* points of `C` (as `flower_plaqueAlgebra_bdd` produces it) is exactly the
hypothesis `hfreeC` on `C`.

This is the "admissible collar" statement used to globalize local `U`-invariance from the
flowers: on the collar the `u`-action preserves `μ`-mass of every measurable subset, and the
`AeHaar` hypothesis is consumed exactly once, in `good_of_atom`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- The displacement boxes are monotone in the radius. -/
lemma V_mono_rad {δ δ' : ℝ} (h : δ ≤ δ') : (V δ : Set SL3) ⊆ V δ' :=
  fun g hg i j => lt_of_lt_of_le (hg i j) h

theorem flowerCollarAdmissible (h2 : Work.EKLContract.P_X3)
    {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hae : Work.EKLRelCross.AeHaar μ U ν)
    {u : Work.EKLContract.SL3} (hu : u ∈ U) (huV : u ∈ Work.EKLContract.V (1/4))
    {C : Set Work.EKLContract.X3} (hC : MeasurableSet C) {W : ℕ → Set Work.EKLContract.X3}
    (hW0 : W 0 = Set.univ) (hWopen : ∀ n, IsOpen (W n))
    (hWgen : borel Work.EKLContract.X3 = MeasurableSpace.generateFrom (Set.range W))
    (hsep : ∀ z ∈ C, ∀ z' ∈ C, (∀ n, z ∈ W n ↔ z' ∈ W n) → z = z')
    (hfreeC : ∀ z ∈ C, ∀ a ∈ U, a • z = z → a = 1)
    {b t r : ℝ} (hb : 0 < b) (ht : 0 < t) (hr : 0 < r) (hrt : r < t)
    (hCS : ∀ z ∈ C, ∀ v ∈ U, v ∈ Work.EKLContract.V b → v • z ∈ C → v = 1)
    (hprod : ∀ a ∈ U, a ∈ Work.EKLContract.V t → ∀ a' ∈ U, a' ∈ Work.EKLContract.V t →
      a'⁻¹ * a ∈ Work.EKLContract.V b)
    (hcore : ∀ y ∈ (⋃ c ∈ C, Work.EKLContract.atom (Work.EKLRelCross.flowerSigma U t C W) c),
      ∀ σ ∈ U, σ ∈ Work.EKLContract.V t →
      σ • y ∈ {z : Work.EKLContract.X3 | ∃ c ∈ C, ∃ σ' : Work.EKLContract.SL3,
          σ' ∈ Work.EKLContract.V r ∩ (U : Set Work.EKLContract.SL3) ∧
          u * σ' ∈ Work.EKLContract.V r ∩ (U : Set Work.EKLContract.SL3) ∧ z = σ' • c} →
      σ • y ∈ Work.EKLContract.atom (Work.EKLRelCross.flowerSigma U t C W) y ∧
      (u * σ) • y ∈ Work.EKLContract.atom (Work.EKLRelCross.flowerSigma U t C W) y) :
    ∀ A : Set Work.EKLContract.X3, MeasurableSet A →
      A ⊆ {z : Work.EKLContract.X3 | ∃ c ∈ C, ∃ σ : Work.EKLContract.SL3,
          σ ∈ Work.EKLContract.V r ∩ (U : Set Work.EKLContract.SL3) ∧
          u * σ ∈ Work.EKLContract.V r ∩ (U : Set Work.EKLContract.SL3) ∧ z = σ • c} →
      μ ((fun x : Work.EKLContract.X3 => u • x) '' A) = μ A := by
  intro A hAmeas hAsub
  -- The product estimate in the `Vinv` form required by the flower lemmas: for `w ∈ (V t)⁻¹ ∩ U`
  -- and `v ∈ V t ∩ U` the product `w * v` is `(w⁻¹)⁻¹ * v`, to which the hypothesis `hprod`
  -- applies with `a' = w⁻¹ ∈ V t ∩ U`.
  have hprodVinv : ∀ w ∈ U, w ∈ Vinv t → ∀ v ∈ U, v ∈ V t → w * v ∈ V b := by
    intro w hwU hwVinv v hvU hvV
    have hwinv : w⁻¹ ∈ V t := mem_Vinv_iff.mp hwVinv
    have h := hprod v hvU hvV w⁻¹ (U.inv_mem hwU) hwinv
    simpa using h
  -- The base points of `C` are free, so the *free* part of `C` is all of `C`, and the plaque
  -- algebra of `flower_plaqueAlgebra_bdd` is a plaque algebra on the collar based at `C`.
  have hCint : C ∩ {x : Work.EKLContract.X3 | ∀ a ∈ U, a • x = x → a = 1} = C :=
    Set.inter_eq_left.mpr (fun z hz => hfreeC z hz)
  have hpla : Work.EKLContract.IsPlaqueAlgebra U
      (⋃ c ∈ C, atom (flowerSigma U t C W) c) (flowerSigma U t C W) := by
    have h := flower_plaqueAlgebra_bdd h2 hUcl hC hCS ht hprodVinv
      (fun a ha haV c hc hcV => hprod c hc hcV a ha haV) hW0 hWopen hWgen hsep
    rwa [hCint] at h
  -- Every point of the collar lies in its own atom: writing it as `σ • c` with `σ ∈ V r ∩ U`,
  -- the atom at `σ • c` is `(V t ∩ U) • c` (both `σ` and `u σ` lie in `V r ∩ U ⊆ V t ∩ U`).
  have hΘ : ∀ a ∈ A, a ∈ (⋃ c ∈ C, atom (flowerSigma U t C W) c) ∧
      u • a ∈ atom (flowerSigma U t C W) a := by
    intro a ha
    obtain ⟨c, hcC, σ, hσrU, huσrU, rfl⟩ := hAsub ha
    have hσVt : σ ∈ V t := V_mono_rad (le_of_lt hrt) hσrU.1
    have h1V : (1 : SL3) ∈ V t := (Work.EKLContract.Lemmas.V_open_one t ht).2
    -- the atom at the base point `c` and at its translate `σ • c` are the same plaque
    have hatom_c : atom (flowerSigma U t C W) c
        = (fun w : SL3 => w • c) '' (V t ∩ (U : Set SL3)) :=
      atom_flower_local hCS ht hprodVinv hW0 hsep (v := (1 : SL3)) h1V U.one_mem hcC
        (by rw [one_smul])
    have hatom_σc : atom (flowerSigma U t C W) (σ • c)
        = (fun w : SL3 => w • c) '' (V t ∩ (U : Set SL3)) :=
      atom_flower_local hCS ht hprodVinv hW0 hsep (v := σ) hσVt hσrU.2 hcC
        (show σ • c = σ • c from rfl)
    constructor
    · refine Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hcC, ?_⟩⟩
      rw [hatom_c]
      exact ⟨σ, ⟨hσVt, hσrU.2⟩, rfl⟩
    · rw [hatom_σc]
      exact ⟨u * σ, ⟨V_mono_rad (le_of_lt hrt) huσrU.1, huσrU.2⟩, mul_smul u σ c⟩
  exact Work.EKLUInv.good_of_atom hU hL hae hu (⟨flowerSigma U t C W⟩ : Work.EKLComp.SigAlg)
    hpla hAmeas hΘ

end Work.EKLRelCross
