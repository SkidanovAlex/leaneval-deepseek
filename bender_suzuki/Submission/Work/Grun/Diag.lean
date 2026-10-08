/-
# Hall's diagonal contribution (M. Hall, §14.4, p. 206)

For a subgroup `H ≤ G` and `u ∈ G`, the *diagonal contribution* to the transfer `V_{G→H}(u)` is

  `d(u) = ∏ x⁻¹ * u * x`,

the product taken over the cosets `xH` of `H` fixed by `u` (each factor lies in `H`).  This is the
contribution of the cycles of length one in Hall's Lemma 14.4.1.

Reference: M. Hall, *The Theory of Groups* (1959), §14.4, Lemmas 14.4.1–14.4.2.
-/
import Mathlib
import Submission.Work.Grun.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Classical Pointwise commutatorElement

namespace Work.Grun

variable {G : Type*} [Group G]

/-- The cosets of `H` fixed by `u`. -/
def fixedCosets (H : Subgroup G) (u : G) : Set (G ⧸ H) := {γ | u • γ = γ}

@[simp] theorem mem_fixedCosets {H : Subgroup G} {u : G} {γ : G ⧸ H} :
    γ ∈ fixedCosets H u ↔ u • γ = γ := Iff.rfl

/-- The factor `x⁻¹ * u * x` of Hall's diagonal contribution belonging to the fixed coset `γ`. -/
noncomputable def diagFactor (H : Subgroup G) (u : G) (γ : fixedCosets H u) : H :=
  ⟨γ.1.out⁻¹ * u * γ.1.out, by
    have h : u • ((γ.1.out : G) : G ⧸ H) = ((γ.1.out : G) : G ⧸ H) := by
      rw [show ((γ.1.out : G) : G ⧸ H) = γ.1 from Quotient.out_eq' γ.1]
      exact γ.2
    rw [MulAction.Quotient.smul_mk] at h
    rw [QuotientGroup.eq] at h
    simpa [mul_assoc] using H.inv_mem h⟩

@[simp] theorem coe_diagFactor (H : Subgroup G) (u : G) (γ : fixedCosets H u) :
    ((diagFactor H u γ : H) : G) = γ.1.out⁻¹ * u * γ.1.out := rfl

/-- Hall's *diagonal contribution* `d(u)`, pushed into a commutative group: the product, over the
cosets `γ` of `H` fixed by `u`, of `θ (x⁻¹ * u * x)` for a representative `x` of `γ`.  (This is
`θ ∘ d` of Hall, Lemma 14.4.1; it is independent of the choice of representatives because `θ` takes
values in a commutative group.) -/
noncomputable def diagProd {H : Subgroup G} [Fintype (G ⧸ H)] {A : Type*} [CommGroup A]
    (θ : H →* A) (u : G) : A :=
  ∏ γ : fixedCosets H u, θ (diagFactor H u γ)

/-- The contribution of the *nontrivial* `⟨u⟩`-orbits of `G ⧸ H` to the transfer: the product, over
the orbits of length `> 1`, of `θ (x⁻¹ * u ^ r * x)` for a representative `x` of the orbit and `r` its
length. -/
noncomputable def freeProd {H : Subgroup G} [Fintype (G ⧸ H)] {A : Type*} [CommGroup A]
    (θ : H →* A) (u : G) : A :=
  ∏ q : Quotient (MulAction.orbitRel (Subgroup.zpowers u) (G ⧸ H)),
    if Function.minimalPeriod (fun x => u • x) q.out = 1 then 1
    else θ ⟨(Quotient.out q.out)⁻¹ * u ^ Function.minimalPeriod (fun x => u • x) q.out *
        Quotient.out q.out, QuotientGroup.out_conj_pow_minimalPeriod_mem H u q.out⟩

@[simp] theorem diagProd_def {H : Subgroup G} [Fintype (G ⧸ H)] {A : Type*} [CommGroup A]
    (θ : H →* A) (u : G) :
    diagProd θ u = ∏ γ : fixedCosets H u, θ (diagFactor H u γ) := rfl

end Work.Grun
