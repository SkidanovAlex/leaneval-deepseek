import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.LinkCert_of_algEquiv
import Submission.Work.MotV.Defs
import Submission.Work.MotV.certN_of_linkCert

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Node LK_AS — restated against the junk-tolerant Crauder–Katz chart of `MotAS` (2026-10-04)

## STATUS OF THIS NODE (read this first)

* **LK_AS is not yet available.**  It is the *only* missing input of the characteristic-`5` branch
  (`STATUS.md` §12): everything else (`BR_AS`, `CO_AS`, `RIG_AS`, the existence data, the assembly
  `Work.MotV5.not_gen_charFive_all_of_linkCert`) is proved and axiom-clean.
* **The live producer is the sibling subproject `MotAS`**, node `Work.MotAS.linkCertAS`
  (`Submission/Work/MotAS/linkCertAS.lean`), whose current content reduces to the geometric
  `Work.MotAS.CensusAS` (the Crauder–Katz divisor classification in AS Galois coordinates) and is
  being built there.
* **The live consumer on this side** is `Work.MotV5.Nodes.linkCert_AS_of_CK` below (transport along
  `RatFunc 𝕜`-algebra isomorphisms, via the proved `Work.MotV5.LinkCert_of_algEquiv`) together with
  its instantiation `Work.MotV5.Nodes.linkCert_AS_of_twistFieldAS`
  (`Submission/Work/MotV5/Nodes/linkCert_AS_transport.lean`, which supplies the two isomorphisms
  from the proved node AS-EQ `Work.MotAS.twistFieldAS_eq`).  So once `Work.MotAS.linkCertAS` lands,
  `LK_AS` is one application of `linkCert_AS_of_twistFieldAS`, and then
  `Work.MotV5.not_gen_charFive_all_of_linkCert` closes characteristic `5`.
* **DEAD / DO NOT LOOK FOR Φ.**  The earlier prime-only isolation `exists_chartIso_AS` and the
  assembly `Work.MotV5.Nodes.linkCert_AS_true_of_census_and_Phi` are **superseded, unused, and
  removed from the live route** (see the paragraph below).  There is no separate "chart Φ" to
  supply: the chart is part of the CK link data behind `MotAS.linkCertAS`.

## Why the prime-only isolation was abandoned

The earlier content of this file isolated the missing input as `exists_chartIso_AS`: *prime*
polynomials `G₁`, `G₂` (the two census polynomials of `Work.MotV5.Nodes.censusTrue_AS`) together
with an isomorphism `A[1/G₂] ≃ₐ[RatFunc 𝕜] A[1/G₁]` of their chart localisations.  That is **not**
what Crauder–Katz supplies: the CK charts necessarily carry junk factors (the plane, the cone and
the chart hyperplanes — `MotK/AUDIT_LinkCertT.md` §7 proves the same for the T-twist), so the
prime-only statement is plausibly false, and the prime-only assembly
`Work.MotV5.Nodes.linkCert_AS_true_of_census_and_Phi` is **superseded and unused**.

The certificate is instead taken from the subproject `MotAS`, whose junk-tolerant node is stated
for the *explicit* twist field `twistFieldAS D g = K(y_j/y_0)` with `y = M(asRoot g)⁻¹κ`
(`M_ij = (w+i)^j`, `℘(w) = g`):

  `linkCertAS : Nonempty (LinkCert (RatFunc 𝕜) ↥(twistFieldAS D (fAS 𝕜)) ↥(twistFieldAS D (2 • fAS 𝕜)))`

and whose node **AS-EQ** (`twistFieldAS_eq`) identifies `twistFieldAS D g` with `MotV5`'s abstract
`asTwistFieldTrue D g τ σS`.  The two certificates are related by
`Work.MotV5.LinkCert_of_algEquiv` (proved): a `LinkCert` transports along `K`-algebra isomorphisms
of the two fields, legitimately because only the two residue-field clauses of the certificate mention
those fields.  The theorem `linkCert_AS_of_CK` below is exactly that transport.

The census `Work.MotV5.Nodes.censusTrue_AS` (a principal height-one prime with residue field
`RatFunc (asTwistFieldTrue D g τ σS)`, via the generator theorem `Nodes/asTwistFieldTrue_gen`) and
its two-generator input stay available, but they are no longer part of the certificate route.
Note also that the *degenerate* census trick (`F = G`, `Φ = refl`) is refuted:
`Work.MotV5.twistFieldAS_ne_two_smul` (`Submission/Work/MotV5/twistFieldAS_ne_two_smul.lean`) proves
that the two twist fields of the link do not coincide, so the hypothesis that
`Work.MotAS.linkCertAS_of_census` consumes is unsatisfiable.

## The two proved lemmas below

They are kept from the earlier version and are the reason the certificate has to be genuinely
birational: an automorphism of `K[x₀,x₁,x₂]` preserves divisor classes, so `G = ψ F` (in particular
`F = G`) would force the distinguished point `zP` — of class `RatFunc F₁` by `zP_res` — to be of class
`RatFunc F₂` or junk, by `F_all`.  Neither an automorphism-induced chart nor an elementary/monomial
Cremona transformation (whose boundary classes are all junk) can supply the CK chart.
-/

set_option autoImplicit false

namespace Work.MotV5.Nodes

/-! ## Two proved lemmas (kept from the prime-only attempt) -/

/-- **Class invariance under an automorphism of the polynomial ring.**  Applying a `K`-algebra
automorphism `ψ` of `K[x₀,…,x_{n−1}]` does not change the class of a point: for every prime `p`, the
residue fields of the point `p` and of its `ψ`-preimage are canonically isomorphic as `K`-algebras.
(The iso is `Ideal.quotientEquivAlg` followed by `IsFractionRing.algEquivOfAlgEquiv`.) -/
theorem resF_comap_algEquiv (K : Type) [Field K] {n : ℕ}
    (ψ : MvPolynomial (Fin n) K ≃ₐ[K] MvPolynomial (Fin n) K)
    (p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime] :
    Nonempty (Work.MotV.resF K ⟨Ideal.comap (ψ : MvPolynomial (Fin n) K →+*
        MvPolynomial (Fin n) K) p, Ideal.comap_isPrime ψ p⟩ ≃ₐ[K]
      Work.MotV.resF K ⟨p, ‹p.IsPrime›⟩) := by
  have hmap : p = Ideal.map (ψ : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K)
      (Ideal.comap (ψ : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K) p) :=
    (Ideal.map_comap_of_surjective _ (AlgEquiv.surjective ψ) p).symm
  refine ⟨IsFractionRing.algEquivOfAlgEquiv (Ideal.quotientEquivAlg
    (Ideal.comap (ψ : MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K) p) p ψ hmap)⟩

/-- **Barrier: `Φ` cannot be automorphism-induced.**  If a link certificate has `G = ψ F` for a
`K`-algebra automorphism `ψ` of `K[x₀,x₁,x₂]` (in particular if `F = G`), then the prime divisors
of `F` and `G` correspond bijectively with equal residue fields (previous lemma), so its
distinguished codimension-one point `zP` — which by `zP_res` has class `RatFunc F₁` — is itself a
prime above `F` and therefore, by `F_all`, must be either of class `RatFunc F₂` or junk.

Consequently a certificate between fields with `RatFunc F₁ ≇ RatFunc F₂` for which the class-`F₁`
divisor is not junk cannot be built from an automorphism of the polynomial ring: the chart map `Φ`
has to be a genuinely birational (Cremona) map, i.e. the Crauder–Katz link. -/
theorem linkCert_class_of_algEquiv_image (K : Type) [Field K] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Algebra K F₁] [Algebra K F₂] (L : Work.MotV.LinkCert K F₁ F₂)
    (ψ : MvPolynomial (Fin 3) K ≃ₐ[K] MvPolynomial (Fin 3) K) (hψ : L.G = ψ L.F) :
    Nonempty (Work.MotV.resF K L.zP ≃ₐ[K] RatFunc F₂) ∨ Work.MotV.JunkClass K L.zP := by
  classical
  have hzPprime : L.zP.asIdeal.IsPrime := L.zP.2
  set q : Work.MotA.polySpec K 3 :=
    ⟨Ideal.comap (ψ : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K) L.zP.asIdeal,
      Ideal.comap_isPrime ψ L.zP.asIdeal⟩ with hq
  -- `q` is again a codimension-one point (`RingEquiv.height_comap`)
  have hqht : Order.coheight q = 1 := by
    have h1 : q.asIdeal.height = L.zP.asIdeal.height := by
      have hq' : q.asIdeal = Ideal.comap
          (ψ.toRingEquiv : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K)
          L.zP.asIdeal := rfl
      rw [hq']
      exact RingEquiv.height_comap ψ.toRingEquiv L.zP.asIdeal
    have h3 : L.zP.asIdeal.height = 1 := by
      have h := AlgebraicGeometry.idealHeight_eq_coheight
        (CommRingCat.of (MvPolynomial (Fin 3) K)) L.zP
      exact h.trans L.zP_ht
    exact ((AlgebraicGeometry.idealHeight_eq_coheight
      (CommRingCat.of (MvPolynomial (Fin 3) K)) q).symm).trans (h1.trans h3)
  -- and it contains `F`, because `ψ F = G ∈ zP`
  have hFq : L.F ∈ q.asIdeal := by
    have hq' : q.asIdeal = Ideal.comap
        (ψ.toRingEquiv : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K)
        L.zP.asIdeal := rfl
    rw [hq', Ideal.mem_comap]
    show ψ L.F ∈ L.zP.asIdeal
    rw [← hψ]
    exact L.zP_mem
  -- the residue fields of `q` and `zP` are isomorphic
  have hcls : Nonempty (Work.MotV.resF K q ≃ₐ[K] Work.MotV.resF K L.zP) := by
    have hq' : q = (⟨Ideal.comap
        (ψ.toRingEquiv : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K)
        L.zP.asIdeal, Ideal.comap_isPrime ψ L.zP.asIdeal⟩ : Work.MotA.polySpec K 3) := rfl
    rw [hq']
    exact resF_comap_algEquiv K ψ L.zP.asIdeal
  rcases L.F_all q hqht hFq with h | h
  · left
    obtain ⟨e⟩ := h
    obtain ⟨e'⟩ := hcls
    exact ⟨e'.symm.trans e⟩
  · right
    obtain ⟨F₀, hF₀f, hF₀a, hgeo, hres⟩ := h
    obtain ⟨e⟩ := hres
    obtain ⟨e'⟩ := hcls
    exact ⟨F₀, hF₀f, hF₀a, hgeo, ⟨e'.symm.trans e⟩⟩

/-! ## Node LK_AS -/

/-- **Node LK_AS, in the form consumed from the test subproject `MotAS`.**  A link certificate for
*any* pair of `RatFunc 𝕜`-algebras which are isomorphic to the two twist fields of the link
transports to a certificate for the twist fields themselves, by
`Work.MotV5.LinkCert_of_algEquiv`.

Instantiating `F₁' := twistFieldAS D (fAS 𝕜)`, `F₂' := twistFieldAS D (2 • fAS 𝕜)`, `L` with
`MotAS`' `linkCert_AS'` and `e₁`, `e₂` with the two isomorphisms supplied by the node AS-EQ
(`twistFieldAS_eq`) turns this into the LK_AS node for `MotV5`.  The two `ASTwistData` bundles `h1`,
`h2` are carried for compatibility with the earlier statement of the node; they are not needed by the
transport. -/
theorem linkCert_AS_of_CK (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D)
    (τ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ σ₂ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (h1 : Work.MotV5.ASTwistData 𝕜 D (Work.MotV.fAS 𝕜) τ σS σ)
    (h2 : Work.MotV5.ASTwistData 𝕜 D (2 • Work.MotV.fAS 𝕜) τ₂ σS σ₂)
    (F₁' F₂' : Type) [Field F₁'] [Field F₂']
    [Algebra (RatFunc 𝕜) F₁'] [Algebra (RatFunc 𝕜) F₂']
    (L : Work.MotV.LinkCert (RatFunc 𝕜) F₁' F₂')
    (e₁ : F₁' ≃ₐ[RatFunc 𝕜] ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS))
    (e₂ : F₂' ≃ₐ[RatFunc 𝕜] ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)) :
    Nonempty (Work.MotV.LinkCert (RatFunc 𝕜)
      ↥(Work.MotV5.asTwistFieldTrue D (Work.MotV.fAS 𝕜) τ σS)
      ↥(Work.MotV5.asTwistFieldTrue D (2 • Work.MotV.fAS 𝕜) τ₂ σS)) :=
  LinkCert_of_algEquiv e₁ e₂ L

end Work.MotV5.Nodes
