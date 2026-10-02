import Submission.Work.Tubular.Gauss
import Submission.Work.Tubular.Interface
import Submission.Work.Tubular.HurewiczNatural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The Hurewicz pairing of the Pontryagin–Thom class `α_V`: the reduction to the ν-side

Item 3 of the subproject brief is the **naturality of the Thom class**: the claim that for the
Pontryagin–Thom class `α_V ∈ π_{8+k}(T)` of an embedded `8`-manifold `V ⊆ ℝ^{8+k}` the Hurewicz
pairing with the degree-`(8+k)` classes `p₁²U`, `p₂U` of the universal Thom space computes the
*normal* Pontryagin numbers of the embedding (`Work.ThomBordism.PontryaginThom.PTRep.hurewicz_p1sq`,
`…hurewicz_p2`, consumed as `Work.Tubular.TubeThomRep`).

This module carries out the **first, unconditional half** of that computation: the naturality of the
Kronecker pairing in the space (step 1 of `PairingNotes.md` §2), which *factors the pairing through
the ν-side class*:

  `⟨a, h(J ∘ c)⟩ = ⟨J^*(a), h(c)⟩`

for `c : S^{8+k} → Th(ν)` the collapse, `J : Th(ν) → T` any based map, and any `a ∈ H^{8+k}(T)`.
The main theorem is `Work.Tubular.kronH_hurewiczChain_alphaV`; the specialisation to the
Pontryagin–Thom class is `Work.Tubular.kronH_alphaV`, and the *consequence* — that the whole pairing
depends on the target only through the pulled-back class `J^*(a) ∈ H^{8+k}(Th ν)` — is
`Work.Tubular.kronH_alphaV_congr`.

Concretely, for the consumer: to prove `⟨D.p1sqU, h(α_V)⟩ = N.normalP1Sq` it is **equivalent** to
proving the single ν-side statement

  `⟨J^*(D.p1sqU), h(collapse)⟩ = N.normalP1Sq`,

where `J = gaussThomMap γ ν gauss e ∘ onePointCongr Φ` is the Gauss/classifying map
(`Work.Tubular.gaussThomMap`) and `h(collapse)` is the Hurewicz class of the Pontryagin–Thom
collapse (`Work.Tubular.tubeGenLoopOnePoint`).  That ν-side statement is `U_ν ⌢ c_*[S^{8+k}] = [V]`
in the form of `Work.Cohomology.kronH_capPair_cup`; it is *not* proved in this module — this module
removes the target from the problem and reduces item 3 to a statement about the tubular
neighbourhood of `V` alone.

Nothing here uses `Work.Stems.HurewiczMapNatural`; see `Submission/Work/Tubular/HurewiczNatural.lean`
for why (an import clash with the two `Work.Stems.wfsW` declarations).
-/

open scoped Topology Topology.Homotopy unitInterval

open Work.ThomBordism.PontryaginThom

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ} {E : EmbeddingData V (8 + k)} {ε : ℝ}

/-! ## The pairing of `α_V` factors through the ν-side class -/

/-- **The Hurewicz pairing of the Pontryagin–Thom class, reduced to the ν side.**  For a tube chart
`C` of an embedding `E : V ↪ ℝ^{8+k}`, a based map `J : Th(ν) → Y` (`J ∞ = y₀`), the metric-free
collapse `g : S^{8+k} → Th(ν)` (constant at `∞` off the open tube) and any cohomology class `a` of
degree `8+k` in `Y`:

`⟨a, h(α_V)⟩ = ⟨J^*(a), h(collapse)⟩`.

This is the naturality of the Kronecker pairing (`Work.Tubular.kronH_hurewiczChain_genLoopMap`)
applied to the definition `α_V = J ∘ collapse`. -/
theorem kronH_hurewiczChain_alphaV (C : TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    {Y : Type} [TopologicalSpace Y] (y₀ : Y)
    (J : C(OnePoint (NormalTotal E), Y)) (hJ : J OnePoint.infty = y₀)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (a : (cochainC ℤ (ssetOf Y)).homology (8 + k)) :
    kronH ℤ (ssetOf Y) (8 + k) a
        (hurewiczClassOf (8 + k) (by omega) y₀
          (Quotient.mk _ (alphaV C hR hbox y₀ J hJ g hg)))
      = kronH ℤ (ssetOf (OnePoint (NormalTotal E))) (8 + k)
          (singularCohomologyMap ℤ (TopCat.of (OnePoint (NormalTotal E))) (TopCat.of Y)
            (TopCat.ofHom J) (8 + k) a)
          (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
            (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox))) := by
  rw [hurewiczClassOf_mk, hurewiczClassOf_mk]
  exact kronH_hurewiczChain_genLoopMap J (8 + k) (by omega)
    (tubeGenLoopOnePoint C g hg hR hbox) a

/-- **The pairing depends on the target only through `J^*(a)`.**  Two targets, two based maps out of
the same Thom space `Th(ν)`, and two classes whose pullbacks to `Th(ν)` agree give the same
Hurewicz pairing with the corresponding Pontryagin–Thom classes.  This is the precise sense in
which item 3 of the brief is a statement about the tubular neighbourhood of `V` and not about the
universal Thom space: everything about the target enters through `J^*(a) ∈ H^{8+k}(Th ν)`. -/
theorem kronH_alphaV_congr (C : TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    {Y₁ : Type} [TopologicalSpace Y₁] (y₁ : Y₁)
    (J₁ : C(OnePoint (NormalTotal E), Y₁)) (hJ₁ : J₁ OnePoint.infty = y₁)
    {Y₂ : Type} [TopologicalSpace Y₂] (y₂ : Y₂)
    (J₂ : C(OnePoint (NormalTotal E), Y₂)) (hJ₂ : J₂ OnePoint.infty = y₂)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (a₁ : (cochainC ℤ (ssetOf Y₁)).homology (8 + k))
    (a₂ : (cochainC ℤ (ssetOf Y₂)).homology (8 + k))
    (h : singularCohomologyMap ℤ (TopCat.of (OnePoint (NormalTotal E))) (TopCat.of Y₁)
            (TopCat.ofHom J₁) (8 + k) a₁
          = singularCohomologyMap ℤ (TopCat.of (OnePoint (NormalTotal E))) (TopCat.of Y₂)
            (TopCat.ofHom J₂) (8 + k) a₂) :
    kronH ℤ (ssetOf Y₁) (8 + k) a₁
        (hurewiczClassOf (8 + k) (by omega) y₁
          (Quotient.mk _ (alphaV C hR hbox y₁ J₁ hJ₁ g hg)))
      = kronH ℤ (ssetOf Y₂) (8 + k) a₂
          (hurewiczClassOf (8 + k) (by omega) y₂
            (Quotient.mk _ (alphaV C hR hbox y₂ J₂ hJ₂ g hg))) := by
  rw [kronH_hurewiczChain_alphaV C hR hbox y₁ J₁ hJ₁ g hg a₁,
      kronH_hurewiczChain_alphaV C hR hbox y₂ J₂ hJ₂ g hg a₂, h]

/-- **The two `TubeThomRep` pairings, in reduced (ν-side) form.**  For a target `D`, a tube chart
`C` of `E`, a based map `J : Th(ν) → D.T` and the collapse `g`, the two Hurewicz pairings of the
Pontryagin–Thom class are the pairings of the pulled-back classes `J^*(p₁²U)`, `J^*(p₂U)` with the
Hurewicz class of the collapse.  Specialising `J` to the Gauss map `gaussThomMap γ ν gauss e`
composed with `onePointCongr Φ` (and `D.T` to `OnePoint γ.TotalSpace`) is the form in which the
Grassmann chapter's classes are consumed. -/
theorem kronH_alphaV_pairings (D : ThomTarget k) (C : TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (J : C(OnePoint (NormalTotal E), D.T)) (hJ : J OnePoint.infty = D.t₀)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty) :
    (kronH ℤ (ssetOf D.T) (8 + k) ((Nat.add_comm 8 k) ▸ D.p1sqU)
        (hurewiczClassOf (8 + k) (by omega) D.t₀
          (Quotient.mk _ (alphaV C hR hbox D.t₀ J hJ g hg)))
      = kronH ℤ (ssetOf (OnePoint (NormalTotal E))) (8 + k)
          (singularCohomologyMap ℤ (TopCat.of (OnePoint (NormalTotal E))) (TopCat.of D.T)
            (TopCat.ofHom J) (8 + k) ((Nat.add_comm 8 k) ▸ D.p1sqU))
          (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
            (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox))))
    ∧ (kronH ℤ (ssetOf D.T) (8 + k) ((Nat.add_comm 8 k) ▸ D.p2U)
        (hurewiczClassOf (8 + k) (by omega) D.t₀
          (Quotient.mk _ (alphaV C hR hbox D.t₀ J hJ g hg)))
      = kronH ℤ (ssetOf (OnePoint (NormalTotal E))) (8 + k)
          (singularCohomologyMap ℤ (TopCat.of (OnePoint (NormalTotal E))) (TopCat.of D.T)
            (TopCat.ofHom J) (8 + k) ((Nat.add_comm 8 k) ▸ D.p2U))
          (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
            (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox)))) :=
  ⟨kronH_hurewiczChain_alphaV C hR hbox D.t₀ J hJ g hg ((Nat.add_comm 8 k) ▸ D.p1sqU),
    kronH_hurewiczChain_alphaV C hR hbox D.t₀ J hJ g hg ((Nat.add_comm 8 k) ▸ D.p2U)⟩

end

end Work.Tubular
