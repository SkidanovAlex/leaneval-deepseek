import Mathlib
import Submission.Work.SSGRoute.PT.shapiro_defs
import Submission.Work.SSGRoute.PT.shapiro_H2_lift_defs
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro in degree `3`: the definitions

This file sets up the vocabulary for the degree-`3` Shapiro isomorphism
`H³(G, Coind_U^G M) ≅ H³(U, M)` (for `U ≤ G` an open subgroup of finite index and a `U`-module
`M`), in parallel with the degree-`2` files `shapiro_H2_coind`, `shapiro_H2_lift_defs`,
`shapiro_H2_lift` and `shapiro_H2_inj`.

* `shapiroLift3 U a` — the Shapiro lift of a `3`-cochain `a` on `U` to a `3`-cochain on `G` with
  values in the coinduced module `Coind U G M`:

    `(shapiroLift3 U a (g,h,k) : G → M) x = coord x • a (A g (xU), A h (g⁻¹ • xU), A k ((gh)⁻¹ • xU))`.

* `s2c U c` — the correction cochain of the Shapiro homotopy in degree `3`: for a `3`-cochain `c`
  on `G` with values in `Coind U G M`,

    `(s2c U c (g,h) : G → M) x = - c (secC xU, A g (xU), A h (g⁻¹ • xU)) x
                                  + c (g, secC (g⁻¹ • xU), A h (g⁻¹ • xU)) x
                                  - c (g, h, secC ((gh)⁻¹ • xU)) x`.

  (The terms carry the section representative in the first, second and third slot respectively.)

The key identity relating `s2c` to the differential (proved in
`Submission/Work/SSGRoute/PT/s2c_d2_apply.lean`, the degree-`3` analogue of `s1_d1_apply` of
`shapiro_H2_inj`) is, for every `3`-cocycle `c` of `G` with values in `Coind U G M`,

  `d² (s2c U c) (g,h,k) (x) = c (g,h,k) (x) - coord x • c (A g (xU)) (A h (g⁻¹ • xU)) (A k ((gh)⁻¹ • xU)) (1)`,

i.e. `d² (s2c U c) = c - Ψ₃ (Φ₃ c)`: `s2c` is the correction term of the Shapiro homotopy in degree
`3`.  The proof is a "cascade" of cocycle conditions (`Z3_eval` below): one inserts the section
representative in each of the four slots of the `3`-cocycle condition, at the four tuples
`(g,h,k,secC ((ghk)⁻¹ • xU))`, `(secC (xU), A g (xU), A h (g⁻¹ • xU), A k ((gh)⁻¹ • xU))`,
`(g, secC (g⁻¹ • xU), A h (g⁻¹ • xU), A k ((gh)⁻¹ • xU))` and
`(g, h, secC ((gh)⁻¹ • xU), A k ((gh)⁻¹ • xU))`, exactly as the degree-`2` proof uses `Z2_eval` at
the three section-inserted triples.

* `h3Primitive U b c` — the primitive `shapiroLift U b + s2c U c` of a `3`-cocycle `c` of `G` whose
  restriction to `U` (i.e. `Φ₃ c = (u,v,w) ↦ c (u,v,w) 1`) is the coboundary `d² b` of a locally
  constant `2`-cochain `b` of `U`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Classical

namespace Work.SSGRoute.PT

noncomputable section

variable {G : Type*} [Group G] (U : Subgroup G)
variable {M : Type*} [AddCommGroup M] [DistribMulAction U M]

/-! ## The Shapiro lift in degree `3` -/

/-- The underlying function of the degree-`3` Shapiro lift:
`x ↦ coord U x • a (A g (xU), A h (g⁻¹ • xU), A k ((gh)⁻¹ • xU))`. -/
def shapiroFun3 (a : U × U × U → M) (p : G × G × G) : G → M :=
  fun x => coord U x • a (Shapiro.A 0 G U p.1 (x : G ⧸ U),
      Shapiro.A 0 G U p.2.1 (p.1⁻¹ • (x : G ⧸ U)),
      Shapiro.A 0 G U p.2.2 ((p.1 * p.2.1)⁻¹ • (x : G ⧸ U)))

theorem shapiroFun3_mem_coind (a : U × U × U → M) (p : G × G × G) :
    shapiroFun3 U a p ∈ coindSub G U M := by
  intro x u
  simp only [shapiroFun3, coset_mul U x u, coord_mul U x u, mul_smul]

/-- **The Shapiro lift in degree `3`** of a `3`-cochain `a` on `U` to a `3`-cochain on `G` with
values in the coinduced module `Coind U G M`. -/
def shapiroLift3 (a : U × U × U → M) : G × G × G → Coind G U M :=
  fun p => ⟨shapiroFun3 U a p, shapiroFun3_mem_coind U a p⟩

@[simp] theorem shapiroLift3_apply (a : U × U × U → M) (g h k x : G) :
    (shapiroLift3 U a (g, h, k) : G → M) x
      = coord U x • a (Shapiro.A 0 G U g (x : G ⧸ U),
          Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)),
          Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U))) := rfl

/-! ## The correction cochain `s2` of the Shapiro homotopy in degree `3` -/

/-- The correction cochain of the Shapiro homotopy in degree `3`.  For a `3`-cochain `c` of `G`
with values in `Coind U G M`, `s2c U c` is the `2`-cochain

  `(g,h) ↦ (x ↦ - c (secC xU, A g (xU), A h (g⁻¹ • xU)) x
                  + c (g, secC (g⁻¹ • xU), A h (g⁻¹ • xU)) x
                  - c (g, h, secC ((gh)⁻¹ • xU)) x)`. -/
def s2c (c : G × G × G → Coind G U M) : G × G → Coind G U M :=
  fun p => ⟨fun x =>
      - (c (secC U (x : G ⧸ U), (Shapiro.A 0 G U p.1 (x : G ⧸ U) : G),
           (Shapiro.A 0 G U p.2 (p.1⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
      + (c (p.1, secC U (p.1⁻¹ • (x : G ⧸ U)),
           (Shapiro.A 0 G U p.2 (p.1⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
      - (c (p.1, p.2, secC U ((p.1 * p.2)⁻¹ • (x : G ⧸ U))) : G → M) x, by
    intro x u
    have hx : (((x * (u : G) : G)) : G ⧸ U) = (x : G ⧸ U) := coset_mul U x u
    simp only [hx]
    rw [Coind.coe_mul, Coind.coe_mul, Coind.coe_mul]
    simp only [smul_neg, smul_add, smul_sub]⟩

@[simp] theorem s2c_apply (c : G × G × G → Coind G U M) (g h x : G) :
    (s2c U c (g, h) : G → M) x
      = - (c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G),
            (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
        + (c (g, secC U (g⁻¹ • (x : G ⧸ U)),
            (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
        - (c (g, h, secC U ((g * h)⁻¹ • (x : G ⧸ U))) : G → M) x := rfl

/-! ## The `3`-cocycle condition in evaluation form -/

/-- **The `3`-cocycle condition of `c`, evaluated at a point `x`.** -/
theorem Z3_eval {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G)
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    {c : G × G × G → Coind G U M}
    (hc : c ∈ Work.SSGRoute.Z3 (M := Coind G U M) G) (g h k l x : G) :
    (c (h, k, l) : G → M) (g⁻¹ * x) - (c (g * h, k, l) : G → M) x
      + (c (g, h * k, l) : G → M) x - (c (g, h, k * l) : G → M) x
      + (c (g, h, k) : G → M) x = 0 := by
  have h1 : Work.SSGRoute.d3 (G := G) (A := Coind G U M) c = 0 :=
    ((Work.SSGRoute.mem_Z3_iff (G := G) (M := Coind G U M)).mp hc).1
  have h2 : ((Work.SSGRoute.d3 (G := G) (A := Coind G U M) c (g, h, k, l) :
      Coind G U M) : G → M) x = 0 := by
    rw [h1]; rfl
  simpa only [Work.SSGRoute.d3_apply, AddSubgroup.coe_add, AddSubgroup.coe_sub,
    Pi.add_apply, Pi.sub_apply, Coind.smul_apply, AddSubgroup.coe_zero, Pi.zero_apply] using h2

/-! ## The primitive of a `3`-cocycle whose restriction is a coboundary -/

/-- The primitive `Ψ₂ b + s₂ c` attached to a `2`-cochain `b` on `U` and a `3`-cochain `c` on `G`
with values in `Coind U G M`. -/
def h3Primitive (b : U × U → M) (c : G × G × G → Coind G U M) : G × G → Coind G U M :=
  shapiroLift U b + s2c U c

theorem h3Primitive_apply (b : U × U → M) (c : G × G × G → Coind G U M) (g h x : G) :
    (h3Primitive U b c (g, h) : G → M) x
      = (shapiroLift U b (g, h) : G → M) x + (s2c U c (g, h) : G → M) x := rfl

end

end Work.SSGRoute.PT
