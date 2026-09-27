import Mathlib
import Submission.Work.Mostow.geodSetup
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.stab_eq_blk
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.cardKAux

/-!
# Finiteness of the pointwise stabiliser of the standard geodesic, and `1 ≤ geodPtCard`

`SetStabStd 1 m` is the setwise stabiliser of the standard geodesic `stdTG 1 m ⊆ E (1+m)`, and
`resStd 1 m c` is the induced isometry of that geodesic.  The set

`{c | c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧ resStd 1 m c = 1}`

is the **pointwise** stabiliser of the geodesic inside `Λ`: by `stab_eq_blk` such a `c` is the block
element `blk 1 m 1 R` with `R = nrmStd 1 m c`, hence (by `blk_smul_fermi`) it fixes every point of
`stdTG 1 m` pointwise — in particular the origin `0` (which lies on the geodesic, `coordEmb 1 m 0
= 0`).

So the pointwise stabiliser is contained in the stabiliser of the origin inside `Λ`, which is finite
for discrete `Λ` by `finite_nearStab` (applied with radius `0`).  The identity is in the set, so its
cardinality is at least `1`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-- The stratum point with zero normal vector is the corresponding stratum point: `fermi k m v 0 =
coordEmb k m v`. -/
lemma geod_fermi_zero (k m : ℕ) (v : Submission.Mostow.E k) :
    Submission.Mostow.fermi k m v (0 : Submission.Mostow.E m) =
      Submission.Mostow.coordEmb k m v := by
  simp [Submission.Mostow.fermi, Submission.Mostow.coordEmb, Submission.Mostow.sinhc]

/-- `coordEmb k m 0 = 0`: the origin lies on the standard stratum. -/
lemma geod_coordEmb_zero (k m : ℕ) :
    Submission.Mostow.coordEmb k m (0 : Submission.Mostow.E k) =
      (0 : Submission.Mostow.E (k + m)) := by
  have h : Fin.append (fun i : Fin k => (0 : Submission.Mostow.E k) i) (fun _ : Fin m => (0 : ℝ)) = 0 := by
    funext i
    refine Fin.addCases (fun j => by simp) (fun j => by simp) i
  simp only [Submission.Mostow.coordEmb, h, WithLp.toLp_zero]

/-- The block element `blk k m h R` acts on the standard stratum by its stratum part `h`. -/
lemma geod_blk_smul_coordEmb (k m : ℕ) (hAk : Submission.Mostow.POActionProp k)
    (hIk : Submission.Mostow.HypIsometryProp k) (hA : Submission.Mostow.POActionProp (k + m))
    (hI : Submission.Mostow.HypIsometryProp (k + m)) (h : PO k 1)
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) (v : Submission.Mostow.E k) :
    Submission.Mostow.blk k m h R • Submission.Mostow.coordEmb k m v =
      Submission.Mostow.coordEmb k m (h • v) := by
  rw [← geod_fermi_zero k m v, blk_smul_fermi k m hAk hIk hA hI h R v 0, map_zero,
    geod_fermi_zero k m (h • v)]

theorem geodPtCardFinite (m : ℕ) (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))
    (hdisc : _root_.IsDiscrete (Λ : Set (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))) :
    Finite {c : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1 // c ∈ Λ ∧ c ∈ Submission.Mostow.SetStabStd 1 m ∧ Submission.Mostow.resStd 1 m c = 1} ∧
      1 ≤ Work.Mostow.geodPtCard m Λ := by
  have hAb : POBasic (1 + m) := POBasic.ofProp hA
  have hIb : HypIsoData (1 + m) := HypIsoData.ofProp hI
  -- every element of the pointwise stabiliser of the geodesic fixes the origin
  have hfix0 : ∀ c : PO (1 + m) 1, c ∈ SetStabStd 1 m → resStd 1 m c = 1 →
      c • (0 : E (1 + m)) = 0 := by
    intro c hstab hres
    have hblk : c = blk 1 m (resStd 1 m c) (nrmStd 1 m c) := stab_eq_blk 1 m hA1 hI1 hA hI c hstab
    rw [← geod_coordEmb_zero 1 m, hblk, hres,
      geod_blk_smul_coordEmb 1 m hA1 hI1 hA hI (1 : PO 1 1) (nrmStd 1 m c) (0 : E 1),
      (POBasic.ofProp hA1).one_smul (0 : E 1), geod_coordEmb_zero 1 m]
  -- the stabiliser of the origin inside `Λ` is finite
  have hfinΛ : {γ : Λ | hdist (0 : E (1 + m)) ((γ : PO (1 + m) 1) • (0 : E (1 + m))) ≤ 0}.Finite :=
    finite_nearStab hAb hIb hdisc 0
  haveI : Finite {γ : Λ | hdist (0 : E (1 + m)) ((γ : PO (1 + m) 1) • (0 : E (1 + m))) ≤ 0} :=
    hfinΛ.to_subtype
  -- the pointwise stabiliser injects into it
  have hinj : Function.Injective
      (fun c : {c : PO (1 + m) 1 // c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧ resStd 1 m c = 1} =>
        (⟨⟨c.1, c.2.1⟩, by
          change hdist (0 : E (1 + m)) (c.1 • (0 : E (1 + m))) ≤ 0
          rw [hfix0 c.1 c.2.2.1 c.2.2.2]
          exact le_of_eq ((hIb.eq_zero 0 0).mpr rfl)⟩ :
          {γ : Λ | hdist (0 : E (1 + m)) ((γ : PO (1 + m) 1) • (0 : E (1 + m))) ≤ 0})) := by
    intro c d hcd
    have h1 : c.1 = d.1 :=
      congrArg (fun t : {γ : Λ | hdist (0 : E (1 + m))
        ((γ : PO (1 + m) 1) • (0 : E (1 + m))) ≤ 0} => ((t.1 : Λ) : PO (1 + m) 1)) hcd
    exact Subtype.ext h1
  have hSfin : Finite {c : PO (1 + m) 1 // c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧ resStd 1 m c = 1} :=
    Finite.of_injective _ hinj
  constructor
  · exact hSfin
  · -- the identity lies in the set, so its cardinality is at least one
    have h1stab : (1 : PO (1 + m) 1) ∈ SetStabStd 1 m := by
      intro u
      rw [hAb.one_smul u]
    have hne : Nonempty {c : PO (1 + m) 1 // c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧ resStd 1 m c = 1} :=
      ⟨⟨1, Subgroup.one_mem Λ, h1stab, resStd_one 1 m hA1 hI1 hA hI⟩⟩
    rw [geodPtCard]
    haveI : Fintype {c : PO (1 + m) 1 // c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧ resStd 1 m c = 1} :=
      Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    exact Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr hne)

end Work.Mostow
