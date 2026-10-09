/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The abelianised tame quotient at a `𝔭`-adic completion

This file discharges **deliverable 4** of the area: the structure
`NK.TameData.TameAbelianisationInput p q (K_𝔭) K'`, i.e. the splitting

  `G_κ^{tr,ab} = (G_κ/V_κ)^{ab} ≅ Ẑ × μ_{q-1}`

(Shimizu, arXiv:2009.10431, Lemma 2.1, via local class field theory) for a genuine local field
`κ = K_𝔭`.

Three things happen here.

1. `q_eq`: for `κ = K_𝔭` the residue field cardinality `q = NK.LocalStructure.residueCard K 𝔭`
   is a positive power of the residue characteristic `p`
   (`NK.LocalStructure.residueCard_eq_pow_of_charP`, from `CharP` of the residue field).
2. **The reduction to `κˣ`** (`NK.TameStructure.tameAbelianisationStructure_of_unitsTameQuotient`):
   the structure of the abelianised tame quotient follows from its `κˣ`-form
   `NK.TameStructure.TameAbelianisationViaUnits` — the statement that the abelianised tame
   quotient is the quotient of the profinite completion of the unit group by the image of the wild
   inertia, together with the structure of the units.  This is the reduction the assignment asks
   for when the full class-field-theoretic route is out of reach: the class-field-theoretic
   ingredient `κˣ^{∧} ≅ G_κ^{ab}` is *available* in this workspace
   (`NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion`), what is not formalised is the
   compatibility of that isomorphism with the quotient by the wild inertia.
3. The assembly `NK.TameStructure.tameAbelianisationInput_adicCompletion`.
-/
import Submission.NK.TameStructure.Defs
import Submission.NK.LocalStructure.Tame.residueCard_eq_pow_of_charP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructure

universe u

noncomputable section

/-! ## The residue field cardinality is a `p`-power -/

variable {K : Type*} [Field K] [NumberField K]

/-- **`q = p ^ f` with `f > 0` for `κ = K_𝔭`**: the residue field of the completion is
`𝓞 K ⧸ 𝔭`, a finite field of characteristic `p`
(`NK.LocalStructure.residueCard_eq_pow_of_charP`). -/
theorem residueCard_eq_pow (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {p : ℕ} (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    ∃ f : ℕ, 0 < f ∧ NK.LocalStructure.residueCard K 𝔭 = p ^ f :=
  NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 hp hchar

/-! ## The reduction to the units -/

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K'] [IsSepClosure κ K']

/-- **The abelianised tame quotient from its `κˣ`-form** (Shimizu 2.1): if the abelianised tame
quotient is the quotient of `κˣ^{∧}` by a pro-`p` normal subgroup `U` (the image of the wild
inertia) and `κˣ^{∧} ⧸ U ≅ Ẑ × μ_{q-1}` (the structure of the units), then
`G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}`. -/
theorem tameAbelianisationStructure_of_unitsTameQuotient {p q : ℕ}
    (h : TameAbelianisationViaUnits p q κ K') :
    Nonempty (NK.LocalTame.tameAbelianization (κ := κ) (K' := K') p ≃*
      (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1)))) := by
  obtain ⟨U, -, -, h1, h2⟩ := h
  obtain ⟨e⟩ := h1
  obtain ⟨f⟩ := h2
  exact ⟨e.trans f⟩

/-- The `κˣ`-form of Shimizu's lemma implies the structure of the units: the second component of
`NK.TameStructure.TameAbelianisationViaUnits` *is* `NK.TameStructure.UnitsStructure`. -/
theorem unitsStructure_of_unitsTameQuotient {p q : ℕ} (h : TameAbelianisationViaUnits p q κ K') :
    UnitsStructure p q κ := by
  obtain ⟨U, hUn, hUp, -, h2⟩ := h
  exact ⟨U, hUn, hUp, h2⟩

/-- **The structure of the units, in the form of a surjection**: if there is a surjection
`κˣ^{∧} →* Ẑ × μ_{q-1}` with pro-`p` kernel, then `κˣ^{∧}` modulo a pro-`p` subgroup is
`Ẑ × μ_{q-1}`. -/
theorem unitsStructure_of_surjective {p q : ℕ}
    (f : NK.LocalReciprocity.completionUnits κ →*
      (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1))))
    (hf : Function.Surjective f) (hker : NK.LocalTame.IsProP p ↥(MonoidHom.ker f)) :
    UnitsStructure p q κ :=
  ⟨MonoidHom.ker f, MonoidHom.normal_ker f, hker,
    ⟨QuotientGroup.quotientKerEquivOfSurjective f hf⟩⟩

/-- **The structure of the units, equivalently a surjection with pro-`p` kernel.** -/
theorem unitsStructure_iff_exists_surjective {p q : ℕ} :
    UnitsStructure p q κ ↔
      ∃ f : NK.LocalReciprocity.completionUnits κ →*
          (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1))),
        Function.Surjective f ∧ NK.LocalTame.IsProP p ↥(MonoidHom.ker f) := by
  constructor
  · rintro ⟨U, hUn, hUp, ⟨e⟩⟩
    refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' U), ?_, ?_⟩
    · exact e.surjective.comp (QuotientGroup.mk'_surjective U)
    · have hk : (MonoidHom.ker (e.toMonoidHom.comp (QuotientGroup.mk' U))) = U := by
        ext x
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
        exact ⟨fun h => (QuotientGroup.eq_one_iff x).mp (e.injective (by simpa using h)),
          fun h => by
            rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr h, map_one]⟩
      rw [hk]
      exact hUp
  · rintro ⟨f, hf, hker⟩
    exact unitsStructure_of_surjective f hf hker

/-- **The structure of the units from an explicit splitting**: if `κˣ^{∧} ≅ (Ẑ × μ_{q-1}) × P`
with `P` pro-`p`, then `κˣ^{∧}` modulo a pro-`p` subgroup is `Ẑ × μ_{q-1}`. -/
theorem unitsStructure_of_prod {p q : ℕ} {P : Type*} [Group P] (hP : NK.LocalTame.IsProP p P)
    (e : NK.LocalReciprocity.completionUnits κ ≃*
      (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1))) × P) :
    UnitsStructure p q κ := by
  refine unitsStructure_of_surjective ((MonoidHom.fst (NK.LocalAnabelian.Zhat ×
      Multiplicative (ZMod (q - 1))) P).comp (e : NK.LocalReciprocity.completionUnits κ →*
      (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1))) × P)) ?_ ?_
  · intro y
    obtain ⟨x, hx⟩ := e.surjective (y, 1)
    exact ⟨x, by simp [hx]⟩
  · have hiso : ↥(MonoidHom.ker ((MonoidHom.fst (NK.LocalAnabelian.Zhat ×
        Multiplicative (ZMod (q - 1))) P).comp (e : NK.LocalReciprocity.completionUnits κ →*
        (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1))) × P))) ≃* P := by
      refine MulEquiv.ofBijective
        ({ toFun := fun x => (e x.1).2
           map_one' := by simp
           map_mul' := fun x y => by simp } : ↥(MonoidHom.ker _) →* P) ⟨?_, ?_⟩
      · intro x y hxy
        have hx1 : (e x.1).1 = 1 := x.2
        have hy1 : (e y.1).1 = 1 := y.2
        have hxy' : e x.1 = e y.1 := by
          rw [Prod.ext_iff]
          exact ⟨by rw [hx1, hy1], hxy⟩
        exact Subtype.ext (e.injective hxy')
      · intro y
        have hmem : e.symm (1, y) ∈ MonoidHom.ker ((MonoidHom.fst (NK.LocalAnabelian.Zhat ×
            Multiplicative (ZMod (q - 1))) P).comp (e : NK.LocalReciprocity.completionUnits κ →*
            (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1))) × P)) := by
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
          simp
        refine ⟨⟨e.symm (1, y), hmem⟩, ?_⟩
        simp
    exact (NK.LocalTame.isProP_congr hiso p).mpr hP

/-! ## The assembly -/

/-- **Deliverable 4**: `NK.TameData.TameAbelianisationInput p q (K_𝔭) K'`, i.e.
`G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` (Shimizu 2.1) and `q = p ^ f` — from the named input
`NK.TameStructure.TameAbelianisationStructure` (Shimizu 2.1) and the residue field arithmetic. -/
theorem tameAbelianisationInput_adicCompletion
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p q : ℕ} (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (hq : q = NK.LocalStructure.residueCard K 𝔭)
    (h : TameAbelianisationStructure p q K 𝔭 K') :
    NK.TameData.TameAbelianisationInput p q (𝔭.adicCompletion K) K' where
  hp := hp
  q_eq := hq.symm ▸ residueCard_eq_pow 𝔭 hp hchar
  nonempty_iso := h

/-- **Deliverable 4, in the form in which the structures of `NK.TameData` are consumed**: the
residue field order is `NK.LocalStructure.residueCard K 𝔭`. -/
theorem tameAbelianisationInput_residueCard
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {K' : Type u} [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ} (hp : p.Prime)
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (h : TameAbelianisationStructure p (NK.LocalStructure.residueCard K 𝔭) K 𝔭 K') :
    NK.TameData.TameAbelianisationInput p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K' :=
  tameAbelianisationInput_adicCompletion 𝔭 hp hchar rfl h

end

end NK.TameStructure
