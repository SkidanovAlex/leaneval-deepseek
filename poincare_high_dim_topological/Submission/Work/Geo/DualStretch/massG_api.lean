import Mathlib
import Submission.Work.Geo.DualStretch.Local
import Submission.Work.Geo.DualStretch.coord_spec
import Submission.Work.Geo.DualStretch.carrier_spec
import Submission.Work.Geo.DualStretch.massOf_sum
import Submission.Work.Geo.DualStretch.massOf_combination
import Submission.Work.Geo.DualStretch.massOf_chain
import Submission.Work.Geo.DualStretch.massOf_pos_iff

/-!
# The mass decomposition of a point of a complex (`massG_api`)

`massG P hP x τ` is the mass of the barycentric-subdivision simplex of `x` indexed by the level set
`τ ⊆ verts P hP` of the barycentric coordinate function `coord P x`.  This file collects the
properties that make `massG` a genuine "weight decomposition" of `x`:

* `massG` is nonnegative;
* the masses of the level sets sum to `1`;
* `x` is the centre of mass `∑_τ massG τ • bary τ`;
* off the subsets of the carrier `carrier P x` the mass vanishes;
* the level sets of positive mass are pairwise nested (they are the superlevel sets of `coord`);
* a level set of positive mass is a face of `P`.

The key observation is that `massG P hP x τ` is *definitionally* the local quantity
`massOf (verts P hP) (coord P x) τ`, and that the level sets of positive mass are automatically
inside the carrier, so that the local identities of `massOf_sum` and `massOf_combination` apply on
the full vertex set.
-/

open Set Metric
open scoped Classical

set_option linter.unusedVariables false

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

/-- The carrier of any point is contained in the vertex set of `P`. -/
private lemma carrier_subset_verts (P : Cx n) (hP : P.faces.Finite) (x : E n) :
    carrier P x ⊆ verts P hP := by
  classical
  unfold carrier
  split_ifs with h
  · intro v hv
    rw [mem_verts]
    exact ⟨h.choose, h.choose_spec.1, hv⟩
  · exact Finset.empty_subset _

/-- The carrier of a point of `P.space` is a face of `P`. -/
private lemma carrier_mem_faces (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space) :
    carrier P x ∈ P.faces := (carrier_spec P hP hx).1

/-- Every subset of the carrier belongs to `cands`. -/
private lemma mem_cands_of_subset_carrier (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space)
    {τ : Finset (E n)} (h : τ ⊆ carrier P x) : τ ∈ cands P hP :=
  mem_cands.mpr ⟨carrier P x, carrier_mem_faces P hP hx, h⟩

/-- Every candidate is a subset of the vertex set. -/
private lemma cands_subset_powerset_verts (P : Cx n) (hP : P.faces.Finite) :
    cands P hP ⊆ (verts P hP).powerset := by
  intro τ hτ
  rw [Finset.mem_powerset]
  obtain ⟨σ, hσ, hτσ⟩ := mem_cands.mp hτ
  intro v hv
  rw [mem_verts]
  exact ⟨σ, hσ, hτσ hv⟩

/-! ### The barycentric coordinate function of `x` -/

/-- `coord P x` is nonnegative everywhere. -/
private lemma coord_nonneg (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space) (v : E n) :
    0 ≤ coord P x v := by
  by_cases hv : v ∈ carrier P x
  · exact (coord_spec P hP hx).1 v hv
  · rw [(coord_spec P hP hx).2.2.2 v hv]

/-- `coord P x` is nonnegative on the vertex set. -/
private lemma coord_nonneg_on_verts (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space) :
    ∀ v ∈ verts P hP, 0 ≤ coord P x v := fun v _ => coord_nonneg P hP hx v

/-- The coordinates of `x` have total mass one on the vertex set. -/
private lemma sum_coord_verts (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space) :
    ∑ v ∈ verts P hP, coord P x v = 1 := by
  have h := Finset.sum_subset (carrier_subset_verts P hP x)
    (fun v _ hv => (coord_spec P hP hx).2.2.2 v hv)
  rw [← h, (coord_spec P hP hx).2.1]

/-- The coordinates of `x` represent `x` on the vertex set. -/
private lemma sum_coord_smul_verts (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space) :
    ∑ v ∈ verts P hP, coord P x v • v = x := by
  have h : ∑ v ∈ carrier P x, coord P x v • v = ∑ v ∈ verts P hP, coord P x v • v :=
    Finset.sum_subset (carrier_subset_verts P hP x)
      (fun v _ hv => by rw [(coord_spec P hP hx).2.2.2 v hv, zero_smul])
  rw [← h, (coord_spec P hP hx).2.2.1]

/-! ### `massG` as a global `massOf` -/

/-- `massG` is the local `massOf` computed with respect to the full vertex set. -/
private lemma massG_eq_massOf_verts (P : Cx n) (hP : P.faces.Finite) (x : E n) (τ : Finset (E n)) :
    massG P hP x τ = massOf (verts P hP) (coord P x) τ := rfl

private lemma massG_nonneg (P : Cx n) (hP : P.faces.Finite) (x : E n) (τ : Finset (E n)) :
    0 ≤ massG P hP x τ := by
  rw [massG_eq_massOf_verts]
  exact le_max_left _ _

/-! ### Vanishing off the carrier -/

/-- `massG` vanishes off the subsets of the carrier. -/
private lemma massG_eq_zero_of_not_subset_carrier (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) {τ : Finset (E n)} (hτ : ¬ τ ⊆ carrier P x) : massG P hP x τ = 0 := by
  classical
  obtain ⟨v, hvτ, hv⟩ := Finset.not_subset.mp hτ
  rw [massG_eq_massOf_verts, massOf]
  have hmin : minVal τ (coord P x) = 0 := by
    refine le_antisymm ?_ (minVal_nonneg fun u _ => coord_nonneg P hP hx u)
    calc minVal τ (coord P x) ≤ coord P x v := minVal_le hvτ
      _ = 0 := (coord_spec P hP hx).2.2.2 v hv
  have hmax : 0 ≤ maxVal (verts P hP \ τ) (coord P x) :=
    maxVal_nonneg fun u _ => coord_nonneg P hP hx u
  rw [hmin, max_eq_left (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg τ.card) (by linarith))]

/-! ### Level sets of positive mass -/

/-- A level set of positive mass is nonempty, and its level value is strictly larger than every
value outside it. -/
private lemma massG_pos_facts (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space)
    {τ : Finset (E n)} (h : 0 < massG P hP x τ) :
    τ.Nonempty ∧ maxVal (verts P hP \ τ) (coord P x) < minVal τ (coord P x) := by
  rw [massG_eq_massOf_verts, massOf] at h
  rw [lt_max_iff] at h
  rcases h with h | h
  · exact absurd h (lt_irrefl 0)
  · have hcn : (0 : ℝ) ≤ (τ.card : ℝ) := Nat.cast_nonneg _
    have hb : 0 < minVal τ (coord P x) - maxVal (verts P hP \ τ) (coord P x) := by
      by_contra hb'
      push Not at hb'
      have := mul_nonpos_of_nonneg_of_nonpos hcn hb'
      linarith
    have hc : 0 < (τ.card : ℝ) := by
      by_contra hc'
      push Not at hc'
      have := mul_nonpos_of_nonpos_of_nonneg hc' (le_of_lt hb)
      linarith
    exact ⟨Finset.card_pos.mp (by exact_mod_cast hc), sub_pos.mp hb⟩

/-- A level set of positive mass is contained in the carrier. -/
private lemma massG_pos_subset_carrier (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space)
    {τ : Finset (E n)} (h : 0 < massG P hP x τ) : τ ⊆ carrier P x := by
  obtain ⟨-, hlt⟩ := massG_pos_facts P hP hx h
  intro v hv
  by_contra hv'
  have hμv : coord P x v = 0 := (coord_spec P hP hx).2.2.2 v hv'
  have hmin0 : minVal τ (coord P x) = 0 := by
    refine le_antisymm ?_ (minVal_nonneg fun u _ => coord_nonneg P hP hx u)
    calc minVal τ (coord P x) ≤ coord P x v := minVal_le hv
      _ = 0 := hμv
  have hmax0 : 0 ≤ maxVal (verts P hP \ τ) (coord P x) :=
    maxVal_nonneg fun u _ => coord_nonneg P hP hx u
  rw [hmin0] at hlt
  linarith

/-- A level set of positive mass is a subset of the vertex set. -/
private lemma massG_pos_subset_verts (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space)
    {τ : Finset (E n)} (h : 0 < massG P hP x τ) : τ ⊆ verts P hP :=
  (massG_pos_subset_carrier P hP hx h).trans (carrier_subset_verts P hP x)

/-- Two level sets of positive mass are comparable. -/
private lemma massG_pos_chain (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space)
    {τ τ' : Finset (E n)} (h : 0 < massG P hP x τ) (h' : 0 < massG P hP x τ') :
    τ ⊆ τ' ∨ τ' ⊆ τ := by
  refine massOf_chain (s := verts P hP) (μ := coord P x)
    (massG_pos_subset_verts P hP hx h) (massG_pos_subset_verts P hP hx h') ?_ ?_
  · rw [massG_eq_massOf_verts] at h; exact h
  · rw [massG_eq_massOf_verts] at h'; exact h'

/-- A level set of positive mass is a face of `P`. -/
private lemma massG_pos_mem_faces (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space)
    {τ : Finset (E n)} (h : 0 < massG P hP x τ) : τ ∈ P.faces :=
  Geometry.SimplicialComplex.down_closed (carrier_mem_faces P hP hx)
    (massG_pos_subset_carrier P hP hx h) (massG_pos_facts P hP hx h).1

/-! ### The total mass and the centre of mass, over the candidate family -/

/-- Off `cands` the mass vanishes. -/
private lemma massG_eq_zero_of_not_mem_cands (P : Cx n) (hP : P.faces.Finite) {x : E n}
    (hx : x ∈ P.space) {τ : Finset (E n)} (h : τ ∉ cands P hP) : massG P hP x τ = 0 :=
  massG_eq_zero_of_not_subset_carrier P hP hx
    (fun hsub => h (mem_cands_of_subset_carrier P hP hx hsub))

/-- The masses of the level sets of the barycentric coordinates add up to `1`. -/
private lemma sum_massG_cands_eq_one (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space) :
    ∑ τ ∈ cands P hP, massG P hP x τ = 1 := by
  calc ∑ τ ∈ cands P hP, massG P hP x τ
      = ∑ τ ∈ (verts P hP).powerset, massG P hP x τ :=
        Finset.sum_subset (cands_subset_powerset_verts P hP)
          (fun τ _ hτ => massG_eq_zero_of_not_mem_cands P hP hx hτ)
    _ = ∑ τ ∈ (verts P hP).powerset, massOf (verts P hP) (coord P x) τ :=
        Finset.sum_congr rfl (fun τ _ => massG_eq_massOf_verts P hP x τ)
    _ = ∑ v ∈ verts P hP, coord P x v := massOf_sum (coord_nonneg_on_verts P hP hx)
    _ = 1 := sum_coord_verts P hP hx

/-- `x` is the centre of mass of the barycentres of the level sets. -/
private lemma sum_massG_cands_smul_bary (P : Cx n) (hP : P.faces.Finite) {x : E n} (hx : x ∈ P.space) :
    ∑ τ ∈ cands P hP, massG P hP x τ • bary τ = x := by
  calc ∑ τ ∈ cands P hP, massG P hP x τ • bary τ
      = ∑ τ ∈ (verts P hP).powerset, massG P hP x τ • bary τ :=
        Finset.sum_subset (cands_subset_powerset_verts P hP)
          (fun τ _ hτ => by rw [massG_eq_zero_of_not_mem_cands P hP hx hτ, zero_smul])
    _ = ∑ τ ∈ (verts P hP).powerset, massOf (verts P hP) (coord P x) τ • bary τ :=
        Finset.sum_congr rfl (fun τ _ => by rw [massG_eq_massOf_verts])
    _ = ∑ v ∈ verts P hP, coord P x v • v := massOf_combination (coord_nonneg_on_verts P hP hx)
    _ = x := sum_coord_smul_verts P hP hx

/-! ### The target -/

theorem massG_api {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {x : PL.E n} (hx : x ∈ P.space) :
    (∀ τ ∈ Work.Geo.DualStretch.cands P hP, 0 ≤ Work.Geo.DualStretch.massG P hP x τ) ∧
      (∑ τ ∈ Work.Geo.DualStretch.cands P hP, Work.Geo.DualStretch.massG P hP x τ = 1) ∧
      (∑ τ ∈ Work.Geo.DualStretch.cands P hP,
          Work.Geo.DualStretch.massG P hP x τ • Work.Geo.DualStretch.bary τ = x) ∧
      (∀ τ : Finset (PL.E n), ¬τ ⊆ Work.Geo.DualStretch.carrier P x →
          Work.Geo.DualStretch.massG P hP x τ = 0) ∧
      (∀ τ ∈ Work.Geo.DualStretch.cands P hP, ∀ τ' ∈ Work.Geo.DualStretch.cands P hP,
          0 < Work.Geo.DualStretch.massG P hP x τ → 0 < Work.Geo.DualStretch.massG P hP x τ' →
            τ ⊆ τ' ∨ τ' ⊆ τ) ∧
      (∀ τ : Finset (PL.E n), 0 < Work.Geo.DualStretch.massG P hP x τ → τ ∈ P.faces) :=
  ⟨fun τ _ => massG_nonneg P hP x τ,
   sum_massG_cands_eq_one P hP hx,
   sum_massG_cands_smul_bary P hP hx,
   fun τ hτ => massG_eq_zero_of_not_subset_carrier P hP hx hτ,
   fun τ _ τ' _ h h' => massG_pos_chain P hP hx h h',
   fun τ h => massG_pos_mem_faces P hP hx h⟩

end Work.Geo.DualStretch
