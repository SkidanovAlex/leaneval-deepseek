import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.CoreQuotientSetup
import Submission.Work.CORE4.CoreA7OddCentralizer
import Submission.Work.CORE4.CoreL2OddCentralizer

namespace Work.CORE4

open scoped MatrixGroups

/-! ## The general lifting step

Everything that is specific to `A₇`/`L₂(q)` happens in the central quotient `E ⧸ Z(E)`; the
following elementary lemma transports the outcome back to `E`. -/
private lemma lift_odd_action {E : Type} [Group E] (Q Y : Subgroup E)
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

/-- Bender 1981, §4, p. 224 (the `A₇`/`L₂(q)` structure input for `I_{U∩M}(s) = [S∩E, U∩M]`).

Let `E` be a finite group whose centre `Z := Z(E)` has odd order and whose central quotient is
`A₇` or `PSL(2,q)` (`q = p ^ k`, `p` odd, `5 ≤ q`).  Let `Q ≤ E` be a `2`-subgroup, `t ∈ Q` an
involution central in `Q`, and `Y ≤ C_E(t)` an odd-order subgroup normalised by `Q`.

Then

* the image `Y Z / Z` of `Y` in `E/Z` is **cyclic**, and
* every `q ∈ Q` acts on `Y Z / Z` by `± 1`: for all `q ∈ Q`, `y ∈ Y`, either
  `(q * y * q⁻¹) * y⁻¹ ∈ Z` or `(q * y * q⁻¹) * y ∈ Z`.

Route.  Write `Ē = E/Z`, `Ȳ = YZ/Z ≤ C_Ē(t̄)` (odd order).
* `Ē ≅ A₇`: `I.toolkit.a7` gives `|C_{A₇}(x)| = 24` for every involution `x`, so `|Ȳ|` divides
  `24` and is odd, hence `|Ȳ| ∈ {1,3}` and `Ȳ` is cyclic; and then `Aut Ȳ` has order `≤ 2`
  (`Aut Z₃ ≅ Z₂`), which gives the `± 1` statement.
* `Ē ≅ PSL(2,q)`: `I.toolkit.l2cent` gives `C_Ē(t̄) ≅ DihedralGroup n` with `2 n = q - 1` or
  `q + 1`; an odd-order subgroup of a dihedral group is cyclic and lies in the rotation subgroup
  (`Work.L2F.Dihedral.dihedral_oddSubgroup`, `oddSubgroup_le_rotations`), and the rotation subgroup
  of `C_Ē(t̄)` is a maximal torus `T` with `Ȳ ≤ T`.  For `g ∈ Q ≤ N_Ē(Ȳ)` pick a prime `r ∣ |Ȳ|`
  and the (unique) subgroup `Ȳ_r ≤ Ȳ` of order `r` (`r ≠ p`, so `I.toolkit.l2torusNorm` applies):
  it gives `|C_Ē(Ȳ_r)| ∈ {(q-1)/2, (q+1)/2} = {|T|, n'}` with `gcd(|T|, n') = 1`, so
  `C_Ē(Ȳ_r) = T`, and `N_Ē(Ȳ_r) ≅ DihedralGroup |T|`, whose elements act on the rotation
  subgroup `T` by `± 1`; since `g ∈ N_Ē(Ȳ_r)` and `Ȳ ⊆ T`, `g` acts on `Ȳ` by `± 1`.
Finally lift the conclusion from `Ē = E/Z` to `E`: `x ∈ Z ↔ xZ = 1`, so the two elements
`(q y q⁻¹) y^{∓1}` have the same image in `E/Z` in each case.

The statement is exactly what `Submission.Work.CORE4.Case2Setup9S` needs from the structure of
`A₇`/`L₂(q)`; it is the p. 224 sentence "By the structure of `A₇` and `L₂(q)`, `(U ∩ E)Z(E)/Z(E)`
is cyclic and is inverted by some involution of a Sylow 2-subgroup of `E`" (the second half,
`Q`-invariance in place of the single involution, is what makes `I_{U∩M}(s) = [S∩E, U∩M]` go
through). -/
theorem CoreOddAction (I : Work.GW2.C4Inputs) :
    ∀ (E : Type) [Group E] [Finite E], Odd (Nat.card (Subgroup.center E)) →
      (Nonempty ((E ⧸ Subgroup.center E) ≃* alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty ((E ⧸ Subgroup.center E) ≃*
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) →
      ∀ (Q : Subgroup E), IsPGroup 2 Q →
      ∀ (t : E), t ∈ Q → orderOf t = 2 → (∀ q ∈ Q, q * t = t * q) →
      ∀ (Y : Subgroup E), Odd (Nat.card Y) → Y ≤ Subgroup.centralizer ({t} : Set E) →
        Q ≤ Subgroup.normalizer (Y : Set E) →
        IsCyclic (Y.map (QuotientGroup.mk' (Subgroup.center E))) ∧
        ∀ q ∈ Q, ∀ y ∈ Y,
          (q * y * q⁻¹) * y⁻¹ ∈ Subgroup.center E ∨
            (q * y * q⁻¹) * y ∈ Subgroup.center E := by
  intro E _ _ hZodd hshape Q _ t htm hto _ Y hYodd hYcent hQnorm
  -- Reduction to the central quotient `E ⧸ Z(E)`.
  obtain ⟨_, htqord, hAodd, hAcent, hAnorm⟩ :=
    CoreQuotientSetup hZodd Q t htm hto Y hYodd hYcent
  have hAnorm' := hAnorm hQnorm
  -- The `A₇`/`L₂(q)` structure of the central quotient gives cyclicity and the `± 1` action.
  have key : IsCyclic (Y.map (QuotientGroup.mk' (Subgroup.center E))) ∧
      ∀ g ∈ Subgroup.normalizer
          ((Y.map (QuotientGroup.mk' (Subgroup.center E))) :
            Set (E ⧸ Subgroup.center E)),
        ∀ a ∈ Y.map (QuotientGroup.mk' (Subgroup.center E)),
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
  exact lift_odd_action Q Y hcyc (fun q hq a ha => hactN q (hAnorm' hq) a ha)

end Work.CORE4
