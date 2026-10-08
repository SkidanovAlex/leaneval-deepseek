import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.CoreQuotientSetup
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.CoreA7OddCentralizer
import Submission.Work.CORE4.CoreL2OddCentralizer
import Submission.Work.L2F.Dihedral.dihedral_oddSubgroup
import Submission.Work.L2F.Dihedral.oddSubgroup_le_rotations

namespace Work.CORE4

open scoped MatrixGroups

/-! ## The general lifting step

Everything specific to `A₇`/`L₂(q)` happens in the central quotient `E ⧸ Z(E)`; the following
elementary lemma transports the outcome back to `E`.  (It is the same computation as
`Work.CORE4.CoreOddAction`'s private `lift_odd_action`, reproduced here because that lemma is
`private`.) -/
private lemma lift_odd_action_center {E : Type} [Group E] (Q Y : Subgroup E)
    (hcyc : IsCyclic (Y.map (QuotientGroup.mk' (Subgroup.center E))))
    (hact : ∀ q ∈ Q.map (QuotientGroup.mk' (Subgroup.center E)),
      ∀ a ∈ Y.map (QuotientGroup.mk' (Subgroup.center E)),
        q * a * q⁻¹ = a ∨ q * a * q⁻¹ = a⁻¹) :
    IsCyclic (Y.map (QuotientGroup.mk' (Subgroup.center E))) ∧
    ∀ q ∈ Q, ∀ y ∈ Y, (q * y * q⁻¹) * y⁻¹ ∈ Subgroup.center E ∨
      (q * y * q⁻¹) * y ∈ Subgroup.center E := by
  refine ⟨hcyc, ?_⟩
  intro q hq y hy
  have hq' : QuotientGroup.mk' (Subgroup.center E) q ∈
      Q.map (QuotientGroup.mk' (Subgroup.center E)) := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
  have hy' : QuotientGroup.mk' (Subgroup.center E) y ∈
      Y.map (QuotientGroup.mk' (Subgroup.center E)) := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  rcases hact _ hq' _ hy' with h | h
  · left
    have h1 : QuotientGroup.mk' (Subgroup.center E) (q * y * q⁻¹) =
        QuotientGroup.mk' (Subgroup.center E) y := by
      simpa only [map_mul, map_inv] using h
    refine (QuotientGroup.eq_one_iff ((q * y * q⁻¹) * y⁻¹)).mp ?_
    change QuotientGroup.mk' (Subgroup.center E) ((q * y * q⁻¹) * y⁻¹) = 1
    rw [map_mul, h1, map_inv, mul_inv_cancel]
  · right
    have h1 : QuotientGroup.mk' (Subgroup.center E) (q * y * q⁻¹) =
        (QuotientGroup.mk' (Subgroup.center E) y)⁻¹ := by
      simpa only [map_mul, map_inv] using h
    refine (QuotientGroup.eq_one_iff ((q * y * q⁻¹) * y)).mp ?_
    change QuotientGroup.mk' (Subgroup.center E) ((q * y * q⁻¹) * y) = 1
    rw [map_mul, h1, inv_mul_cancel]

/-- Bender 1981, §4, p. 224: the odd-order subgroup `X ≤ C_E(t)` normalised by a subgroup
`Q ≤ C_E(t)` containing the involution `t` has cyclic image in `E ⧸ Z(E)`, and every `q ∈ Q` acts
on it by `± 1` modulo `Z(E)`.

This is `Work.CORE4.CoreOddAction` without the (unused) hypotheses `IsPGroup 2 Q` and
`∀ q ∈ Q, q * t = t * q`: the reduction to the central quotient is `CoreQuotientSetup`, and the
`A₇` / `L₂(q)` structure of `E ⧸ Z(E)` is `CoreA7OddCentralizer` / `CoreL2OddCentralizer`. -/
theorem Case2Setup9S2OddAct (I : Work.GW2.C4Inputs) :
    ∀ (E : Type) [Group E] [Finite E], Odd (Nat.card (Subgroup.center E)) →
      (Nonempty ((E ⧸ Subgroup.center E) ≃* alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty ((E ⧸ Subgroup.center E) ≃*
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) →
      ∀ (t : E), orderOf t = 2 →
      ∀ (Q X : Subgroup E), t ∈ Q → Q ≤ Subgroup.centralizer ({t} : Set E) →
        X ≤ Subgroup.centralizer ({t} : Set E) → Odd (Nat.card X) →
        Q ≤ Subgroup.normalizer (X : Set E) →
        IsCyclic (X.map (QuotientGroup.mk' (Subgroup.center E))) ∧
          (∀ q ∈ Q, ∀ y ∈ X,
            (q * y * q⁻¹) * y⁻¹ ∈ Subgroup.center E ∨
              (q * y * q⁻¹) * y ∈ Subgroup.center E) := by
  intro E _ _ hZodd hshape t hto Q X htm _hQcent hXcent hXodd hQnorm
  -- Reduction to the central quotient `E ⧸ Z(E)`.
  obtain ⟨_, htqord, hAodd, hAcent, hAnorm⟩ :=
    CoreQuotientSetup hZodd Q t htm hto X hXodd hXcent
  have hAnorm' := hAnorm hQnorm
  -- The `A₇`/`L₂(q)` structure of the central quotient gives cyclicity and the `± 1` action.
  have key : IsCyclic (X.map (QuotientGroup.mk' (Subgroup.center E))) ∧
      ∀ g ∈ Subgroup.normalizer
          ((X.map (QuotientGroup.mk' (Subgroup.center E))) :
            Set (E ⧸ Subgroup.center E)),
        ∀ a ∈ X.map (QuotientGroup.mk' (Subgroup.center E)),
          g * a * g⁻¹ = a ∨ g * a * g⁻¹ = a⁻¹ := by
    rcases hshape with hA7 | hL2
    · obtain ⟨φ⟩ := hA7
      exact CoreA7OddCentralizer I.toolkit.a7 _
        φ (QuotientGroup.mk' (Subgroup.center E) t) htqord _ hAcent hAodd
    · obtain ⟨p, k, hpp, hp, hk, hφ⟩ := hL2
      obtain ⟨φ⟩ := hφ
      haveI : Fact p.Prime := hpp
      exact CoreL2OddCentralizer I.toolkit.l2cent I.l2torusNorm p k hp hk _
        φ (QuotientGroup.mk' (Subgroup.center E) t) htqord _ hAcent hAodd
  obtain ⟨hcyc, hactN⟩ := key
  exact lift_odd_action_center Q X hcyc (fun q hq a ha => hactN q (hAnorm' hq) a ha)

end Work.CORE4
