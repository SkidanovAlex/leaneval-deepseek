import Mathlib
import Submission.Work.EKLRelCross.entropy_cs_interface
import Submission.Work.EKLRelCross.plaque_identity_base
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLComp.PlaqueToolkit

/-!
# `Work.EKLRelCross.plaque_ratio` — (P1′) from (P1)

`PlaqueRatio μ U ν` is the plaque-mass ratio: for `μ`-a.e. base point `x₀`, every `ε > 0` and
every `t ∈ U`,

`μ ((V ε ∩ U) • (t • x₀)) · ν x₀ (V ε ∩ U) = μ ((V ε ∩ U) • x₀) · ν x₀ ((V ε ∩ U) · t)`.

It is derived here from the *cross-multiplied* local product structure `PlaqueId` (P1) alone,
together with the cheap fields of `IsLeafwise` (`radon`, `pos`, `carried`).  The idea: `PlaqueId`
at `x₀` with a radius `δ` so large that the translated box `(V ε ∩ U)·t` is contained in
`V δ ∩ U`, applied twice — once to `A = (V ε ∩ U) • (t • x₀)` and once to `A = (V ε ∩ U) • x₀` —
gives two identities whose right hand sides involve the *same* μ-mass `μ ((V δ ∩ U) • x₀)` and
whose left hand sides carry the common factor `ν x₀ (V δ ∩ U)`, which is positive and finite
(`pos`, `radon` + compactness of an entrywise box); cancelling it yields the ratio.  The
freeness of the `U`-orbit at `x₀` (a.e., `ae_free_orbit`) is what makes the two identities match
set-theoretically.
-/

open MeasureTheory Filter Topology
open Pointwise
open scoped ENNReal

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract Work.EKLComp

/-! ## Elementary set algebra of the orbit map -/

/-- A free orbit gives injectivity of the orbit map on `U`. -/
theorem plaqueRatio_injOn_smul_of_free {U : Subgroup SL3} {x : X3}
    (hfree : ∀ u ∈ U, u • x = x → u = 1) :
    ∀ a ∈ U, ∀ b ∈ U, a • x = b • x → a = b := by
  intro a ha b hb hab
  have h : (b⁻¹ * a) • x = x := by rw [mul_smul, hab, inv_smul_smul]
  have h1 := hfree (b⁻¹ * a) (U.mul_mem (U.inv_mem hb) ha) h
  rw [inv_mul_eq_one] at h1
  exact h1.symm

/-- Membership in the orbit image of a subset of `U`. -/
theorem plaqueRatio_smul_mem_image_iff {U : Subgroup SL3} {x : X3}
    (hinj : ∀ a ∈ U, ∀ b ∈ U, a • x = b • x → a = b)
    {S : Set SL3} (hSU : S ⊆ U) {u : SL3} (huU : u ∈ U) :
    u • x ∈ (fun v : SL3 => v • x) '' S ↔ u ∈ S := by
  constructor
  · rintro ⟨v, hvS, hv⟩
    have hvu : v = u := hinj v (hSU hvS) u huU hv
    rwa [hvu] at hvS
  · exact fun hu => ⟨u, hu, rfl⟩

/-- Intersections of orbit images are orbit images of intersections. -/
theorem plaqueRatio_image_inter_image {U : Subgroup SL3} {x : X3}
    (hinj : ∀ a ∈ U, ∀ b ∈ U, a • x = b • x → a = b)
    {A B : Set SL3} (hA : A ⊆ U) (hB : B ⊆ U) :
    (fun v : SL3 => v • x) '' A ∩ (fun v : SL3 => v • x) '' B
      = (fun v : SL3 => v • x) '' (A ∩ B) := by
  ext y
  constructor
  · rintro ⟨⟨a, haA, rfl⟩, ⟨b, hbB, hba⟩⟩
    have hab : b = a := hinj b (hB hbB) a (hA haA) hba
    exact ⟨a, ⟨haA, hab ▸ hbB⟩, rfl⟩
  · rintro ⟨a, ⟨haA, haB⟩, rfl⟩
    exact ⟨⟨a, haA, rfl⟩, ⟨a, haB, rfl⟩⟩

/-- `|a - b| ≤ |a| + |b|`. -/
theorem plaqueRatio_abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  simpa [sub_eq_add_neg, abs_neg] using h

/-! ## Positivity and finiteness of the `ν`-mass of the box `V δ ∩ U` -/

/-- The `ν x`-mass of the box `V δ ∩ U` is positive: `ν x` is carried by `U` and positive on
every `V δ`. -/
theorem plaqueRatio_box_pos {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    {x : X3} (hx : x ∈ X') {δ : ℝ} (hδ : 0 < δ) :
    0 < ν x (V δ ∩ (U : Set SL3)) := by
  have hnull : ν x (V δ ∩ ((U : Set SL3))ᶜ) = 0 :=
    measure_mono_null Set.inter_subset_right (hL.carried x hx)
  have hae : (V δ : Set SL3) =ᵐ[ν x] ((V δ) ∩ (U : Set SL3) : Set SL3) := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨measure_mono_null ?_ hnull, ?_⟩
    · intro g hg
      exact ⟨hg.1, fun hgU => hg.2 ⟨hg.1, hgU⟩⟩
    · show ν x (((V δ) ∩ (U : Set SL3) : Set SL3) \ V δ) = 0
      rw [show ((V δ) ∩ (U : Set SL3) : Set SL3) \ V δ = ∅ from
        Set.sdiff_eq_empty.mpr Set.inter_subset_left, measure_empty]
  have hmeasure : ν x (V δ ∩ (U : Set SL3)) = ν x (V δ) :=
    (measure_congr hae).symm
  rw [hmeasure]
  exact hL.pos x hx δ hδ

/-- The `ν x`-mass of `V δ ∩ U` is finite: `ν x` is a Radon measure and `V δ ∩ U` sits inside
the compact entrywise box `|g i j| ≤ 1 + δ`. -/
theorem plaqueRatio_box_lt_top {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    {x : X3} (hx : x ∈ X') (δ : ℝ) :
    ν x (V δ ∩ (U : Set SL3)) < ⊤ := by
  have hsub : V δ ∩ (U : Set SL3) ⊆ {g : SL3 | ∀ i j, -(1 + δ) ≤ g i j ∧ g i j ≤ 1 + δ} := by
    rintro u ⟨huV, _⟩ i j
    exact abs_le.mp (Work.EKLProd.mem_V_entries_le huV i j)
  exact lt_of_le_of_lt (measure_mono hsub)
    ((hL.radon x hx).lt_top_of_isCompact
      (Work.EKLProd.sl3EntryBox_compact (fun _ _ => -(1 + δ)) (fun _ _ => 1 + δ)))

/-! ## The core step -/

/-- **(P1′)** at a single good base point: the plaque-mass ratio, from `PlaqueId` at `x₀`. -/
theorem plaque_ratio_point {μ : Measure X3} [IsProbabilityMeasure μ]
    (U : Subgroup SL3) (hUc : IsClosed (U : Set SL3))
    (ν : X3 → Measure SL3) (X' : Set X3) (hL : IsLeafwise μ U ν X')
    {x₀ : X3} (hx' : x₀ ∈ X') (hfree : ∀ u ∈ U, u • x₀ = x₀ → u = 1)
    (hPx : ∀ ε : ℝ, 0 < ε → ∀ A : Set X3, MeasurableSet A →
      ν x₀ (V ε ∩ (U : Set SL3)) * μ (A ∩ orbitPlaque U x₀ ε)
        = μ (orbitPlaque U x₀ ε) *
          ν x₀ {u : SL3 | u ∈ V ε ∩ (U : Set SL3) ∧ u • x₀ ∈ A})
    {ε : ℝ} (hε : 0 < ε) {t : SL3} (htU : t ∈ U) :
    μ (orbitPlaque U (t • x₀) ε) * ν x₀ (V ε ∩ (U : Set SL3))
      = μ (orbitPlaque U x₀ ε) * ν x₀ ((V ε ∩ (U : Set SL3)) * {t}) := by
  have hinj := plaqueRatio_injOn_smul_of_free (U := U) (x := x₀) hfree
  set W : Set SL3 := V ε ∩ (U : Set SL3) with hW
  have hWU : W ⊆ U := Set.inter_subset_right
  set S : Set SL3 := (fun u : SL3 => u * t) '' W with hS
  have hSU : S ⊆ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact U.mul_mem (hWU hu) htU
  -- an entrywise bound for `t`
  set Ct : ℝ := 1 + ∑ i : Fin 3, ∑ j : Fin 3, |(t : Matrix (Fin 3) (Fin 3) ℝ) i j| with hCt
  have hCt1 : 1 ≤ Ct := by
    rw [hCt]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => abs_nonneg _)))
  have hCt0 : 0 < Ct := lt_of_lt_of_le one_pos hCt1
  have ht_entry : ∀ i j : Fin 3, |(t : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ Ct := by
    intro i j
    have h1 : |(t : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ ∑ j' : Fin 3, |(t : Matrix (Fin 3) (Fin 3) ℝ) i j'| :=
      Finset.single_le_sum
        (f := fun j' : Fin 3 => |(t : Matrix (Fin 3) (Fin 3) ℝ) i j'|)
        (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : (∑ j' : Fin 3, |(t : Matrix (Fin 3) (Fin 3) ℝ) i j'|)
        ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, |(t : Matrix (Fin 3) (Fin 3) ℝ) i' j'| :=
      Finset.single_le_sum
        (f := fun i' : Fin 3 => ∑ j' : Fin 3, |(t : Matrix (Fin 3) (Fin 3) ℝ) i' j'|)
        (fun i' _ => Finset.sum_nonneg (fun j' _ => abs_nonneg _)) (Finset.mem_univ i)
    have h3 : Ct = 1 + ∑ i' : Fin 3, ∑ j' : Fin 3, |(t : Matrix (Fin 3) (Fin 3) ℝ) i' j'| := hCt
    linarith
  set δ : ℝ := 3 * (1 + ε) * Ct + 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; nlinarith [hε, hCt0]
  have hεδ : ε ≤ δ := by rw [hδ]; nlinarith [hε, hCt1]
  -- entry bound for `1`
  have h1entry : ∀ i j : Fin 3, |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    intro i j
    rw [Matrix.one_apply]
    split <;> simp
  -- `S = W·t ⊆ V δ ∩ U`
  have hSsub : S ⊆ V δ ∩ (U : Set SL3) := by
    rintro _ ⟨u, hu, rfl⟩
    have huW : u ∈ W := hu
    rw [hW] at huW
    obtain ⟨huV, huU⟩ := huW
    refine ⟨?_, U.mul_mem huU htU⟩
    intro i j
    have h1 : |((u * t : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 3 * (1 + ε) * Ct :=
      Work.EKLComp.mul_entries_le u t i j
        (fun k l => Work.EKLProd.mem_V_entries_le huV k l) ht_entry (by linarith) (le_of_lt hCt0)
    calc |((u * t : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ |((u * t : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j|
            + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := plaqueRatio_abs_sub_le_abs_add_abs _ _
      _ ≤ 3 * (1 + ε) * Ct + 1 := add_le_add h1 (by simpa using h1entry i j)
      _ < 3 * (1 + ε) * Ct + 2 := by norm_num
      _ = δ := by rw [hδ]
  -- `W ⊆ V δ ∩ U`
  have hWsubδ : W ⊆ V δ ∩ (U : Set SL3) := by
    intro u hu
    rw [hW] at hu
    refine ⟨?_, hu.2⟩
    intro i j
    have h1 : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 + ε :=
      Work.EKLProd.mem_V_entries_le hu.1 i j
    calc |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
          plaqueRatio_abs_sub_le_abs_add_abs _ _
      _ ≤ (1 + ε) + 1 := add_le_add h1 (by simpa using h1entry i j)
      _ < δ := by rw [hδ]; nlinarith [hε, hCt1]
  -- the orbit plaque at `t • x₀` is the orbit image of `S`
  have horb : orbitPlaque U (t • x₀) ε = (fun v : SL3 => v • x₀) '' S := by
    rw [hS, hW, Set.image_image]
    show (fun u : SL3 => u • (t • x₀)) '' (V ε ∩ (U : Set SL3))
        = (fun u : SL3 => (u * t) • x₀) '' (V ε ∩ (U : Set SL3))
    congr 1
    funext u
    exact (mul_smul u t x₀).symm
  -- the two set identities for the two applications of `PlaqueId`
  have hset1 : {u : SL3 | u ∈ V δ ∩ (U : Set SL3) ∧ u • x₀ ∈ orbitPlaque U (t • x₀) ε} = S := by
    ext u
    rw [horb, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hu, hmem⟩
      exact (plaqueRatio_smul_mem_image_iff (U := U) hinj hSU hu.2).mp hmem
    · intro hu
      exact ⟨hSsub hu, (plaqueRatio_smul_mem_image_iff (U := U) hinj hSU (hSU hu)).mpr hu⟩
  have hset2 : orbitPlaque U (t • x₀) ε ∩ orbitPlaque U x₀ δ = orbitPlaque U (t • x₀) ε := by
    rw [horb]
    show (fun v : SL3 => v • x₀) '' S ∩ (fun v : SL3 => v • x₀) '' (V δ ∩ (U : Set SL3))
        = (fun v : SL3 => v • x₀) '' S
    rw [plaqueRatio_image_inter_image (U := U) (x := x₀) hinj hSU Set.inter_subset_right,
      Set.inter_eq_left.mpr hSsub]
  have hset3 : orbitPlaque U x₀ ε ∩ orbitPlaque U x₀ δ = orbitPlaque U x₀ ε := by
    show (fun v : SL3 => v • x₀) '' W ∩ (fun v : SL3 => v • x₀) '' (V δ ∩ (U : Set SL3))
        = (fun v : SL3 => v • x₀) '' W
    rw [plaqueRatio_image_inter_image (U := U) (x := x₀) hinj hWU Set.inter_subset_right,
      Set.inter_eq_left.mpr hWsubδ]
  have hset4 : {u : SL3 | u ∈ V δ ∩ (U : Set SL3) ∧ u • x₀ ∈ orbitPlaque U x₀ ε} = W := by
    ext u
    rw [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hu, hmem⟩
      exact (plaqueRatio_smul_mem_image_iff (U := U) hinj hWU hu.2).mp hmem
    · intro hu
      exact ⟨hWsubδ hu, (plaqueRatio_smul_mem_image_iff (U := U) hinj hWU (hWU hu)).mpr hu⟩
  -- apply `PlaqueId` twice, at radius `δ`
  have hI1 := hPx δ hδpos (orbitPlaque U (t • x₀) ε)
    (Work.EKLProd.borelOrbitImage U hUc (t • x₀) ε)
  have hI2 := hPx δ hδpos (orbitPlaque U x₀ ε) (Work.EKLProd.borelOrbitImage U hUc x₀ ε)
  rw [hset2, hset1] at hI1
  rw [hset3, hset4] at hI2
  -- the goal, rewritten to the `PlaqueId` vocabulary
  have hbox : (V ε ∩ (U : Set SL3)) * {t} = S := by
    rw [Set.mul_singleton, ← hW]
  have hLHS : ν x₀ (V ε ∩ (U : Set SL3)) = ν x₀ W :=
    congrArg (fun s : Set SL3 => ν x₀ s) hW.symm
  have hRHS : ν x₀ ((V ε ∩ (U : Set SL3)) * {t}) = ν x₀ S :=
    congrArg (fun s : Set SL3 => ν x₀ s) hbox
  rw [hLHS, hRHS]
  -- cancel the common factor `ν x₀ (V δ ∩ U)`
  have ha0 : ν x₀ (V δ ∩ (U : Set SL3)) ≠ 0 := (plaqueRatio_box_pos hL hx' hδpos).ne'
  have haT : ν x₀ (V δ ∩ (U : Set SL3)) ≠ ⊤ := (plaqueRatio_box_lt_top hL hx' δ).ne
  refine (ENNReal.mul_right_inj ha0 haT).mp ?_
  calc ν x₀ (V δ ∩ (U : Set SL3)) * (μ (orbitPlaque U (t • x₀) ε) * ν x₀ W)
      = (ν x₀ (V δ ∩ (U : Set SL3)) * μ (orbitPlaque U (t • x₀) ε)) * ν x₀ W := by
        rw [mul_assoc]
    _ = (μ (orbitPlaque U x₀ δ) * ν x₀ S) * ν x₀ W := by rw [hI1]
    _ = μ (orbitPlaque U x₀ δ) * (ν x₀ S * ν x₀ W) := by rw [mul_assoc]
    _ = μ (orbitPlaque U x₀ δ) * (ν x₀ W * ν x₀ S) := by rw [mul_comm (ν x₀ S) (ν x₀ W)]
    _ = (μ (orbitPlaque U x₀ δ) * ν x₀ W) * ν x₀ S := by rw [mul_assoc]
    _ = (ν x₀ (V δ ∩ (U : Set SL3)) * μ (orbitPlaque U x₀ ε)) * ν x₀ S := by rw [← hI2]
    _ = ν x₀ (V δ ∩ (U : Set SL3)) * (μ (orbitPlaque U x₀ ε) * ν x₀ S) := by rw [mul_assoc]

end Work.EKLRelCross

namespace Work.EKLRelCross

/-- **(P1′) Plaque-mass ratio** is a formal consequence of the local product structure (P1). -/
theorem plaque_ratio (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3)
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hP : Work.EKLRelCross.PlaqueId μ U ν) :
    Work.EKLRelCross.PlaqueRatio μ U ν := by
  rw [PlaqueRatio]
  rw [PlaqueId] at hP
  have hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 :=
    ae_free_orbit h2 μ U hU t0 ht0 hcontr
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [MeasureTheory.ae_iff, show {a : Work.EKLContract.X3 | ¬ a ∈ X'} = X'ᶜ from rfl]
    exact hL.conull
  filter_upwards [hP, hfree, hX'] with x₀ hPx hfr hx'
  intro ε hε t htU
  exact plaque_ratio_point U hU.1 ν X' hL hx' hfr hPx hε htU

end Work.EKLRelCross
