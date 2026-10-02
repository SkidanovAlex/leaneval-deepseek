import Submission.Work.ThomBordism.PontryaginThom.Hurewicz

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The assembly: `TransversalityCore` and `TransversalityCoreFamily`

The two inputs of `Work.ThomBordism.Interface` that the whole argument of `Work.ThomBordism` uses,
proved from

* **(a)** `Work.Drive.RationalHurewiczStable` (area STEMS, rationally the stable stems), applied to
  the `(k-1)`-connected Thom space `T` in the degree `8 + k ≤ 2k - 2`;
* **(b)** the universal Thom space `ThomTarget k` (the Grassmann chapter: `T = Th(γ_k)`, the classes
  `p₁²U`, `p₂U`, the connectedness of `T` and the fact that the two classes detect torsion) and the
  Pontryagin–Thom construction `PTExists` (item 1: embedding, normal bundle, tubular neighbourhood,
  Gauss map, collapse);
* **(c)** `Transversality` (item 3: turning a null-homotopy of a multiple of the collapse class into
  a null-bordism of a multiple of the family) and `PTAdditivity` (the class of a disjoint union is
  the sum of the classes of its pieces, so the Hurewicz pairings add).

The mathematics is in `Hurewicz.lean`; what is left here is the bookkeeping.  Note that the same
`k` and `T` serve the whole chapter: a single embedding codimension `k ≥ 10` works for every
`8`-manifold (Mathlib's `exists_embedding_euclidean_of_compact` embeds each compact manifold into
some `ℝ^n`, and the connectedness and spanning hypotheses on `T` are those of the *stable*
Grassmannian, so one may take a large fixed `k`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.ThomBordism.PontryaginThom

noncomputable section

variable {k : ℕ} {D : ThomTarget k}

/-- **`TransversalityCore` from the geometric inputs and rational Hurewicz.**

For a closed oriented `8`-manifold `V` whose `p₁²`- and `p₂`-numbers vanish: the Pontryagin–Thom
class `α_V` exists (item 1), its Hurewicz image is torsion (item 2, `Hurewicz.lean`), rational
Hurewicz in the stable range makes `α_V` torsion (area STEMS), and transversality (item 3) turns
the null-homotopy of a positive multiple of `α_V` into a null-bordism of a positive multiple of
`V`. -/
theorem transversalityCore_of_inputs (D : ThomTarget k) (hk : 10 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable) (hin : PTInputs k D) : TransversalityCore := by
  intro V h1 h2
  obtain ⟨r⟩ := hin.exists_rep V
  obtain ⟨N, hN, hpow⟩ :=
    r.exists_pow_eq_one_of_numbers_zero (by omega) hrat (by omega) h1 h2
  exact hin.transversality V r ⟨N, hN, hpow⟩

/-- **`TransversalityCoreFamily` from the geometric inputs and rational Hurewicz.**

For a finite family `F` of closed oriented `8`-manifolds whose *total* `p₁²`- and `p₂`-numbers
vanish: the family's Pontryagin–Thom class exists by additivity (item 3), its Hurewicz image is the
sum of the normal numbers of the pieces, i.e. the vanishing totals (item 2, `Hurewicz.lean`),
rational Hurewicz makes it torsion (area STEMS), and the family form of transversality gives a
null-bordism of a positive multiple of the family. -/
theorem transversalityCoreFamily_of_inputs (D : ThomTarget k) (hk : 10 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable) (hin : PTInputs k D) :
    TransversalityCoreFamily := by
  intro ι _ F h1 h2
  obtain ⟨r⟩ := hin.additivity ι F (fun i => hin.exists_rep (F i))
  obtain ⟨N, hN, hpow⟩ :=
    r.exists_pow_eq_one_of_numbers_zero (by omega) hrat (by omega) h1 h2
  exact hin.transversalityFamily ι F r ⟨N, hN, hpow⟩

/-- The same, from the two geometric inputs split up (`PTExists`, `PTAdditivity`,
`Transversality`) rather than bundled. -/
theorem transversalityCore_of_separateInputs (D : ThomTarget k) (hk : 10 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable) (hex : PTExists k D)
    (htrans : Transversality k D) : TransversalityCore := by
  intro V h1 h2
  obtain ⟨r⟩ := hex V
  obtain ⟨N, hN, hpow⟩ :=
    r.exists_pow_eq_one_of_numbers_zero (by omega) hrat (by omega) h1 h2
  exact htrans V r ⟨N, hN, hpow⟩

/-- The family form, from the geometric inputs split up. -/
theorem transversalityCoreFamily_of_separateInputs (D : ThomTarget k) (hk : 10 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable) (hex : PTExists k D)
    (hadd : PTAdditivity k D) (htrans : Transversality k D)
    (htransF : TransversalityFamily k D) : TransversalityCoreFamily :=
  transversalityCoreFamily_of_inputs D hk hrat ⟨hex, hadd, htrans, htransF⟩

/-- **`TransversalityCore` from the geometric inputs and `RationalHurewiczStable3`** (the weaker
contract of the project lead's message, with `k ≥ 11` so that the degree `k + 8` is in range). -/
theorem transversalityCore_of_inputs_three (D : ThomTarget k) (hk : 11 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable3) (hin : PTInputs k D) : TransversalityCore := by
  intro V h1 h2
  obtain ⟨r⟩ := hin.exists_rep V
  obtain ⟨N, hN, hpow⟩ := r.exists_pow_eq_one_of_numbers_zero_three hk hrat h1 h2
  exact hin.transversality V r ⟨N, hN, hpow⟩

/-- **`TransversalityCoreFamily` from the geometric inputs and `RationalHurewiczStable3`.** -/
theorem transversalityCoreFamily_of_inputs_three (D : ThomTarget k) (hk : 11 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable3) (hin : PTInputs k D) :
    TransversalityCoreFamily := by
  intro ι _ F h1 h2
  obtain ⟨r⟩ := hin.additivity ι F (fun i => hin.exists_rep (F i))
  obtain ⟨N, hN, hpow⟩ := r.exists_pow_eq_one_of_numbers_zero_three hk hrat h1 h2
  exact hin.transversalityFamily ι F r ⟨N, hN, hpow⟩

/-- The same, from the inputs split up. -/
theorem transversalityCore_of_separateInputs_three (D : ThomTarget k) (hk : 11 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable3) (hex : PTExists k D)
    (htrans : Transversality k D) : TransversalityCore := by
  intro V h1 h2
  obtain ⟨r⟩ := hex V
  obtain ⟨N, hN, hpow⟩ := r.exists_pow_eq_one_of_numbers_zero_three hk hrat h1 h2
  exact htrans V r ⟨N, hN, hpow⟩

/-- The family form, from the inputs split up. -/
theorem transversalityCoreFamily_of_separateInputs_three (D : ThomTarget k) (hk : 11 ≤ k)
    (hrat : Work.Drive.RationalHurewiczStable3) (hex : PTExists k D)
    (hadd : PTAdditivity k D) (htrans : Transversality k D)
    (htransF : TransversalityFamily k D) : TransversalityCoreFamily :=
  transversalityCoreFamily_of_inputs_three D hk hrat ⟨hex, hadd, htrans, htransF⟩

end

end Work.ThomBordism.PontryaginThom
