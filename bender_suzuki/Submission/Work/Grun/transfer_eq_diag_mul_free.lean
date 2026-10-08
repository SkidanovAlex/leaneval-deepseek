/-
# The transfer as diagonal contribution times the free (nontrivial orbit) contribution

Mathlib's cycle formula for the transfer,
`MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot`, writes the transfer `V_{G→H}(u)` as a
product over the `⟨u⟩`-orbits of `G ⧸ H`:

  `transfer θ u = ∏ q : Quotient (orbitRel (zpowers u) (G ⧸ H)), θ ⟨x_q⁻¹ * u ^ m_q * x_q⟩`,

where `x_q` is a representative of the orbit `q` and `m_q` is its length (the minimal period of the
action of `u` on `x_q`).

Here we separate off the orbits of length one.  An orbit has length one exactly when its
representative is a coset fixed by `u`; the contribution of the length-one orbits is Hall's
*diagonal contribution* `diagProd θ u` (M. Hall, *The Theory of Groups*, §14.4, Lemma 14.4.1), and
the contribution of the remaining orbits is `freeProd θ u`.

The length-one orbits are in bijection with the fixed cosets (`fixedOrbitEquiv`), and on such an
orbit the exponent `m_q` equals `1`, so the two products agree term by term.
-/
import Mathlib
import Submission.Work.Grun.Diag

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Grun

open scoped Classical Pointwise commutatorElement
open MulAction

/-- Splitting a product according to a decidable predicate: the product over all `q` is the product
of the part supported where `p` holds with the part supported where `p` fails. -/
theorem prod_eq_prod_ite_mul_prod_ite {ι : Type*} [Fintype ι] {M : Type*} [CommMonoid M]
    (f : ι → M) (p : ι → Prop) [DecidablePred p] :
    ∏ q, f q = (∏ q, if p q then f q else 1) * (∏ q, if p q then 1 else f q) := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun q _ => by by_cases h : p q <;> simp [h]

/-- The summand of Mathlib's cycle formula for the transfer: the contribution of the `⟨u⟩`-orbit
`q` of `G ⧸ H`, namely `θ ⟨x⁻¹ * u ^ m * x⟩` for a representative `x = q.out.out` of `q` and the
orbit length `m = minimalPeriod (u • ·) q.out`. -/
noncomputable def transferTerm {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A]
    (θ : H →* A) (u : G) (q : Quotient (MulAction.orbitRel (Subgroup.zpowers u) (G ⧸ H))) : A :=
  θ ⟨(Quotient.out q.out)⁻¹ * u ^ Function.minimalPeriod (fun x => u • x) q.out * Quotient.out q.out,
     QuotientGroup.out_conj_pow_minimalPeriod_mem H u q.out⟩

/-- The length-one `⟨u⟩`-orbits of `G ⧸ H` are exactly the cosets fixed by `u`: the map sending
such an orbit to its representative `.out` is a bijection onto `fixedCosets H u`. -/
noncomputable def fixedOrbitEquiv {G : Type*} [Group G] {H : Subgroup G} (u : G) :
    {q : Quotient (MulAction.orbitRel (Subgroup.zpowers u) (G ⧸ H)) //
        Function.minimalPeriod (fun x => u • x) q.out = 1} ≃ Work.Grun.fixedCosets H u :=
  Equiv.ofBijective
    (fun q => ⟨q.1.out, by
        rw [Work.Grun.mem_fixedCosets]
        exact Function.minimalPeriod_eq_one_iff_isFixedPt.mp q.2⟩)
    ⟨fun q q' h => by
        have h1 : q.1.out = q'.1.out := by
          simpa using Subtype.ext_iff.mp h
        have h2 : q.1 = q'.1 := by
          rw [← Quotient.out_eq' q.1, ← Quotient.out_eq' q'.1, h1]
        exact Subtype.ext h2,
     fun γ => by
        have horbit : MulAction.orbit (Subgroup.zpowers u) γ.1 ⊆ {γ.1} := by
          rintro a ⟨x, rfl⟩
          simp only [Set.mem_singleton_iff, subgroup_smul_def]
          exact MulAction.mem_stabilizer_iff.mp
            ((Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr γ.2)) x.2)
        have hout : (Quotient.mk'' γ.1 :
            Quotient (MulAction.orbitRel (Subgroup.zpowers u) (G ⧸ H))).out = γ.1 :=
          horbit (orbitRel_apply.mp (Quotient.mk_out γ.1))
        refine ⟨⟨Quotient.mk'' γ.1, ?_⟩, ?_⟩
        · rw [hout]
          exact Function.minimalPeriod_eq_one_iff_isFixedPt.mpr γ.2
        · exact Subtype.ext hout⟩

/-- The underlying coset of `fixedOrbitEquiv u q` is the representative `q.out` of the orbit. -/
@[simp] theorem fixedOrbitEquiv_coe {G : Type*} [Group G] {H : Subgroup G} {u : G}
    (q : {q : Quotient (MulAction.orbitRel (Subgroup.zpowers u) (G ⧸ H)) //
        Function.minimalPeriod (fun x => u • x) q.out = 1}) :
    ((fixedOrbitEquiv u q : Work.Grun.fixedCosets H u) : G ⧸ H) = q.1.out := rfl

/-- The transfer written as the diagonal contribution times the contribution of the nontrivial
`⟨u⟩`-orbits of `G ⧸ H`.  This is Mathlib's cycle formula
`MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot`, with the cycles of length one separated
off: those are exactly the cosets of `H` fixed by `u`, and their contribution is `diagProd θ u`. -/
theorem transfer_eq_diag_mul_free {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    [Fintype (G ⧸ H)] {A : Type*} [CommGroup A] (θ : H →* A) (u : G) :
    θ.transfer u = Work.Grun.diagProd θ u * Work.Grun.freeProd θ u := by
  classical
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  rw [Work.Grun.diagProd_def]
  unfold Work.Grun.freeProd
  change ∏ q : Quotient (MulAction.orbitRel (Subgroup.zpowers u) (G ⧸ H)), transferTerm θ u q
      = (∏ γ : Work.Grun.fixedCosets H u, θ (Work.Grun.diagFactor H u γ))
        * ∏ q, if Function.minimalPeriod (fun x => u • x) q.out = 1 then 1 else transferTerm θ u q
  have hC : (∏ q : Quotient (MulAction.orbitRel (Subgroup.zpowers u) (G ⧸ H)),
        if Function.minimalPeriod (fun x => u • x) q.out = 1 then transferTerm θ u q else 1)
      = ∏ γ : Work.Grun.fixedCosets H u, θ (Work.Grun.diagFactor H u γ) := by
    rw [← Finset.prod_filter]
    have hsplit2 : (∏ q ∈ Finset.univ.filter
          (fun q => Function.minimalPeriod (fun x => u • x) q.out = 1), transferTerm θ u q)
        = ∏ q : {q : Quotient (MulAction.orbitRel (Subgroup.zpowers u) (G ⧸ H)) //
            Function.minimalPeriod (fun x => u • x) q.out = 1}, transferTerm θ u ↑q :=
      Finset.prod_subtype _ (fun q => by simp) _
    rw [hsplit2]
    refine Fintype.prod_equiv (fixedOrbitEquiv u) (fun a => transferTerm θ u ↑a)
      (fun γ => θ (Work.Grun.diagFactor H u γ)) (fun q => ?_)
    simp only [transferTerm]
    congr 1
    apply Subtype.ext
    simp only [Work.Grun.coe_diagFactor, fixedOrbitEquiv_coe]
    rw [q.2, pow_one]
  rw [← hC, prod_eq_prod_ite_mul_prod_ite (transferTerm θ u)
    (fun q => Function.minimalPeriod (fun x => u • x) q.out = 1)]

end Work.Grun
