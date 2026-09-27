/-
`Work.Geo.DualStretch.join_decomp`

`x` lies on the join segment between its low end `uOf β p P hP x` and its high end
`wOf β p P hP x`, with the barycentric parameter `SOf β p P hP x` (the total high mass):

  `x = (1 - S) • u + S • w`,   `S = SOf β p P hP x`.

The substance is the mass decomposition of `x` by the level sets of the barycentric coordinate
function `coord P x` of `x` with respect to its carrier face:

* `massG P hP x τ` is nonnegative;
* `∑_τ massG P hP x τ = 1` (the masses are a probability distribution);
* `x = ∑_τ massG P hP x τ • bary τ` (the centre of mass);
* `massG P hP x τ = 0` off the subsets of the carrier, hence off the complement of the finite
  candidate family `cands P hP`.

Splitting the last sum into its low terms (`LowFace`, i.e. `card τ ≤ p + 1`) and its high terms
gives `AOf + BOf = x`, while splitting the first gives `1 - SOf = (total low mass)`.  Since
`uOf = (1 - SOf)⁻¹ • AOf` and `wOf = SOf⁻¹ • BOf` (with the degenerate cases handled by `0`), the
join identity follows by a short case analysis on `SOf = 0` and `1 - SOf = 0`.

To keep the file independent of the (separately maintained) `massG_api` development, the four
facts above are proved here directly from the local identities `massOf_sum` and `massOf_combination`
for the carrier face; all auxiliary lemmas below are `private`.
-/
import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.carrier_spec
import Submission.Work.Geo.DualStretch.coord_spec
import Submission.Work.Geo.DualStretch.massOf_sum
import Submission.Work.Geo.DualStretch.massOf_combination

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open _root_.PL (E Cx)

variable {n : ℕ}

/-! ### The vertex set and the candidate family -/

private lemma mem_verts {P : Cx n} {hP : P.faces.Finite} {v : E n} :
    v ∈ verts P hP ↔ ∃ σ ∈ P.faces, v ∈ σ := by
  rw [verts, Finset.mem_biUnion]
  constructor
  · rintro ⟨σ, hσ, hv⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mp hσ, hv⟩
  · rintro ⟨σ, hσ, hv⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mpr hσ, hv⟩

private lemma mem_cands {P : Cx n} {hP : P.faces.Finite} {τ : Finset (E n)} :
    τ ∈ cands P hP ↔ ∃ σ ∈ P.faces, τ ⊆ σ := by
  rw [cands, Finset.mem_biUnion]
  constructor
  · rintro ⟨σ, hσ, hτ⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mp hσ, Finset.mem_powerset.mp hτ⟩
  · rintro ⟨σ, hσ, hτ⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mpr hσ, Finset.mem_powerset.mpr hτ⟩

private lemma carrier_subset_verts (P : Cx n) (hP : P.faces.Finite) (x : E n) :
    carrier P x ⊆ verts P hP := by
  classical
  unfold carrier
  split_ifs with h
  · intro v hv
    rw [mem_verts]
    exact ⟨h.choose, h.choose_spec.1, hv⟩
  · exact Finset.empty_subset _

private lemma mem_cands_of_subset_carrier (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) {τ : Finset (E n)} (h : τ ⊆ carrier P x) : τ ∈ cands P hP :=
  mem_cands.mpr ⟨carrier P x, (carrier_spec P hP hx).1, h⟩

private lemma cands_subset_powerset_verts (P : Cx n) (hP : P.faces.Finite) :
    cands P hP ⊆ (verts P hP).powerset := by
  intro τ hτ
  rw [Finset.mem_powerset]
  obtain ⟨σ, hσ, hτσ⟩ := mem_cands.mp hτ
  intro v hv
  rw [mem_verts]
  exact ⟨σ, hσ, hτσ hv⟩

/-! ### The barycentric coordinates of `x` -/

private lemma coord_nonneg (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space)
    (v : E n) : 0 ≤ coord P x v := by
  by_cases hv : v ∈ carrier P x
  · exact (coord_spec P hP hx).1 v hv
  · rw [(coord_spec P hP hx).2.2.2 v hv]

private lemma coord_nonneg_on_verts (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) : ∀ v ∈ verts P hP, 0 ≤ coord P x v := fun v _ => coord_nonneg P hP hx v

private lemma sum_coord_verts (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space) :
    ∑ v ∈ verts P hP, coord P x v = 1 := by
  have h : ∑ v ∈ carrier P x, coord P x v = ∑ v ∈ verts P hP, coord P x v :=
    Finset.sum_subset (carrier_subset_verts P hP x)
      (fun v _ hv => (coord_spec P hP hx).2.2.2 v hv)
  rw [← h, (coord_spec P hP hx).2.1]

private lemma sum_coord_smul_verts (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space) :
    ∑ v ∈ verts P hP, coord P x v • v = x := by
  have h : ∑ v ∈ carrier P x, coord P x v • v = ∑ v ∈ verts P hP, coord P x v • v :=
    Finset.sum_subset (f := fun v => coord P x v • v) (carrier_subset_verts P hP x)
      (fun v _ hv => by rw [(coord_spec P hP hx).2.2.2 v hv, zero_smul])
  rw [← h, (coord_spec P hP hx).2.2.1]

/-! ### `massG` as a local `massOf` on the vertex set -/

private lemma massG_eq_massOf_verts (P : Cx n) (hP : P.faces.Finite) (x : E n)
    (τ : Finset (E n)) : massG P hP x τ = massOf (verts P hP) (coord P x) τ := rfl

private lemma massG_nonneg (P : Cx n) (hP : P.faces.Finite) (x : E n) (τ : Finset (E n)) :
    0 ≤ massG P hP x τ := by
  rw [massG_eq_massOf_verts]
  exact le_max_left _ _

/-- `massG` vanishes off the subsets of the carrier face. -/
private lemma massG_eq_zero_of_not_subset_carrier (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) {τ : Finset (E n)} (hτ : ¬ τ ⊆ carrier P x) : massG P hP x τ = 0 := by
  obtain ⟨v, hvτ, hv⟩ := Finset.not_subset.mp hτ
  rw [massG_eq_massOf_verts, massOf]
  have hmin : minVal τ (coord P x) = 0 := by
    refine le_antisymm ?_ (minVal_nonneg fun u _ => coord_nonneg P hP hx u)
    calc minVal τ (coord P x) ≤ coord P x v := minVal_le hvτ
      _ = 0 := (coord_spec P hP hx).2.2.2 v hv
  have hmax : 0 ≤ maxVal (verts P hP \ τ) (coord P x) :=
    maxVal_nonneg fun u _ => coord_nonneg P hP hx u
  rw [hmin,
    max_eq_left (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg τ.card) (by linarith))]

private lemma massG_eq_zero_of_not_mem_cands (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) {τ : Finset (E n)} (h : τ ∉ cands P hP) : massG P hP x τ = 0 :=
  massG_eq_zero_of_not_subset_carrier P hP hx
    (fun hsub => h (mem_cands_of_subset_carrier P hP hx hsub))

/-! ### Total mass and centre of mass over the candidate family -/

private lemma sum_massG_cands_eq_one (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) : ∑ τ ∈ cands P hP, massG P hP x τ = 1 := by
  calc ∑ τ ∈ cands P hP, massG P hP x τ
      = ∑ τ ∈ (verts P hP).powerset, massG P hP x τ :=
        Finset.sum_subset (cands_subset_powerset_verts P hP)
          (fun τ _ hτ => massG_eq_zero_of_not_mem_cands P hP hx hτ)
    _ = ∑ τ ∈ (verts P hP).powerset, massOf (verts P hP) (coord P x) τ :=
        Finset.sum_congr rfl (fun τ _ => massG_eq_massOf_verts P hP x τ)
    _ = ∑ v ∈ verts P hP, coord P x v := massOf_sum (coord_nonneg_on_verts P hP hx)
    _ = 1 := sum_coord_verts P hP hx

private lemma sum_massG_cands_smul_bary (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) : ∑ τ ∈ cands P hP, massG P hP x τ • bary τ = x := by
  calc ∑ τ ∈ cands P hP, massG P hP x τ • bary τ
      = ∑ τ ∈ (verts P hP).powerset, massG P hP x τ • bary τ :=
        Finset.sum_subset (f := fun τ => massG P hP x τ • bary τ)
          (cands_subset_powerset_verts P hP)
          (fun τ _ hτ => by rw [massG_eq_zero_of_not_mem_cands P hP hx hτ, zero_smul])
    _ = ∑ τ ∈ (verts P hP).powerset, massOf (verts P hP) (coord P x) τ • bary τ :=
        Finset.sum_congr rfl (fun τ _ => by rw [massG_eq_massOf_verts])
    _ = ∑ v ∈ verts P hP, coord P x v • v := massOf_combination (coord_nonneg_on_verts P hP hx)
    _ = x := sum_coord_smul_verts P hP hx

/-! ### The join decomposition -/

theorem join_decomp {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {β : ℝ} {p : ℕ} {x : PL.E n}
    (hx : x ∈ P.space) :
    x = (1 - Work.Geo.DualStretch.SOf β p P hP x) • Work.Geo.DualStretch.uOf β p P hP x +
        Work.Geo.DualStretch.SOf β p P hP x • Work.Geo.DualStretch.wOf β p P hP x := by
  classical
  have hnn : ∀ τ ∈ cands P hP, 0 ≤ massG P hP x τ := fun τ _ => massG_nonneg P hP x τ
  have hsum : ∑ τ ∈ cands P hP, massG P hP x τ = 1 := sum_massG_cands_eq_one P hP hx
  have hcom : ∑ τ ∈ cands P hP, massG P hP x τ • bary τ = x := sum_massG_cands_smul_bary P hP hx
  -- `A + B = x`: split the centre of mass into low and high terms
  have hAB : AOf β p P hP x + BOf β p P hP x = x := by
    rw [AOf, BOf, ← Finset.sum_add_distrib]
    conv_rhs => rw [← hcom]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    by_cases hc : LowFace β p τ <;> simp [hc]
  have hSdef : SOf β p P hP x
      = ∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ) := rfl
  -- `1 - S` is the total low mass
  have hone : 1 - SOf β p P hP x
      = ∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ else 0) := by
    rw [hSdef, ← hsum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    by_cases hc : LowFace β p τ <;> simp [hc]
  have hAeq : AOf β p P hP x
      = ∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ else 0) • bary τ := by
    rw [AOf]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    by_cases hc : LowFace β p τ <;> simp [hc]
  have hBeq : BOf β p P hP x
      = ∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ) • bary τ := by
    rw [BOf]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    by_cases hc : LowFace β p τ <;> simp [hc]
  have hlo_nn : ∀ τ ∈ cands P hP,
      0 ≤ (if LowFace β p τ then massG P hP x τ else 0) := by
    intro τ hτ
    by_cases hc : LowFace β p τ <;> simp [hc, hnn τ hτ]
  have hhi_nn : ∀ τ ∈ cands P hP,
      0 ≤ (if LowFace β p τ then 0 else massG P hP x τ) := by
    intro τ hτ
    by_cases hc : LowFace β p τ <;> simp [hc, hnn τ hτ]
  by_cases hS0 : SOf β p P hP x = 0
  · -- all the mass is low: `A = x`, and `w = 0`
    have hw : wOf β p P hP x = 0 := by rw [wOf]; exact ite_eq_left hS0
    have hu : uOf β p P hP x = AOf β p P hP x := by
      rw [uOf, ite_eq_right (by rw [hS0]; norm_num), hS0, sub_zero, inv_one, one_smul]
    have hhi0 : ∀ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hhi_nn).mp (by rw [← hSdef]; exact hS0)
    have hB0 : BOf β p P hP x = 0 := by
      rw [hBeq]
      refine Finset.sum_eq_zero (fun τ hτ => ?_)
      by_cases hc : LowFace β p τ
      · simp [hc]
      · have hf0 : massG P hP x τ = 0 := by
          have := hhi0 τ hτ
          rwa [ite_eq_right hc] at this
        rw [ite_eq_right hc, hf0, zero_smul]
    have hAx : AOf β p P hP x = x := by
      have h := hAB
      rw [hB0, add_zero] at h
      exact h
    rw [hu, hw, hS0]
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact hAx.symm
  · have hw : wOf β p P hP x = (SOf β p P hP x)⁻¹ • BOf β p P hP x := by
      rw [wOf]; exact ite_eq_right hS0
    have hSw : SOf β p P hP x • wOf β p P hP x = BOf β p P hP x := by
      rw [hw, smul_smul, mul_inv_cancel₀ hS0, one_smul]
    by_cases h1S0 : 1 - SOf β p P hP x = 0
    · -- all the mass is high: `B = x`, and `u = 0`
      have hu : uOf β p P hP x = 0 := by rw [uOf]; exact ite_eq_left h1S0
      have hlo0 : ∀ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ else 0) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hlo_nn).mp (by rw [← hone]; exact h1S0)
      have hA0 : AOf β p P hP x = 0 := by
        rw [hAeq]
        refine Finset.sum_eq_zero (fun τ hτ => ?_)
        rw [hlo0 τ hτ, zero_smul]
      have hBx : BOf β p P hP x = x := by
        have h := hAB
        rw [hA0, zero_add] at h
        exact h
      rw [hu, hSw, hBx]
      simp
    · have hu : uOf β p P hP x = (1 - SOf β p P hP x)⁻¹ • AOf β p P hP x := by
        rw [uOf]; exact ite_eq_right h1S0
      have h1Su : (1 - SOf β p P hP x) • uOf β p P hP x = AOf β p P hP x := by
        rw [hu, smul_smul, mul_inv_cancel₀ h1S0, one_smul]
      rw [h1Su, hSw]
      exact hAB.symm

end Work.Geo.DualStretch
