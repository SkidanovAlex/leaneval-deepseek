/-
Copyright: the martinet_totally_real_towers team.

# Surjectivity of `δ⁰` when `H¹(G,B) = 0`

For a short exact sequence `0 → A --f--> B --g--> C → 0` of discrete `G`-modules `S` and a
discrete `G`-module structure on the coefficients, the connecting map

  `connecting0 S : H⁰(G,C) → H¹(G,A)`

is the degree shift in the long exact cohomology sequence.  Its image is the kernel of the
coefficient-change map `H¹Map S.f : H¹(G,A) → H¹(G,B)`; consequently, if `H¹(G,B)` is trivial
then `δ⁰` is *surjective*.

The proof is the classical diagram chase on the level of locally constant cochains.  Let
`x ∈ H¹(G,A)` be represented by the `1`-cocycle `z : G → A`.  Since `H¹(G,B) = 0`, the class of
`S.f ∘ z` in `H¹(G,B)` vanishes, i.e. `S.f (z σ) = σ • b - b` for a locally constant `b : B`.
Applying `S.g` and using `g ∘ f = 0` shows that `c := S.g b` is `G`-invariant, so `c` is a class
in `H⁰(G,C)`.  The chosen section `sect c` differs from `b` by an element of `ker g = im f`, say
`sect c = b + f a`; substituting this into the definition of `δ⁰` gives

  `S.delta0Fun c σ = z σ + (σ • a - a)`,

i.e. `δ⁰ c = z + d⁰ a` differs from `z` by the coboundary `d⁰a`.  Hence `connecting0 S c = x`.

This is the surjectivity of the *Kummer* connecting map for the coefficient sequence
`0 → μ_n → Lˣ --n--> Lˣ → 0` (there `H¹(G, Lˣ) = 0` by Hilbert 90), which is why the statement is
called `kummer_H1_surjective`.
-/

import Mathlib
import Submission.Work.ConCohomology.Connecting

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

theorem kummer_H1_surjective {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]
    (S : CoeffSES G A B C) (hB : Subsingleton (H1 G B)) (x : H1 G A) :
    ∃ c : H0 G C, connecting0 S c = x := by
  haveI : Subsingleton (H1 G B) := hB
  refine QuotientAddGroup.induction_on x ?_
  intro z
  change ∃ c : H0 G C, connecting0 S c = H1.mk z
  -- The class of `z` dies in `H¹(G,B)`, because that group is trivial.
  have hz : H1Map S.f (H1.mk z) = 0 := Subsingleton.elim _ _
  rw [H1Map_mk, H1.mk_eq_zero_iff, mem_B1'] at hz
  obtain ⟨b, hb⟩ := mem_B1.mp hz
  -- `hb` says that the `B`-valued cochain `σ ↦ σ • b - b` is the image under `S.f` of `z`.
  have hb' : ∀ σ : G, σ • b - b = S.f (((z : Z1 G A) : Cochain1 G A) σ) := by
    intro σ
    have h := DFunLike.congr_fun hb σ
    simpa only [d0Hom_apply, Z1Map_coe, cochain1Map_apply] using h
  -- `c := S.g b` is `G`-invariant.
  have hc : S.g b ∈ fixedPoints G C := by
    intro σ
    have h1 : S.g (σ • b - b) = 0 := by
      rw [hb' σ]
      exact (S.exact _).mpr ⟨_, rfl⟩
    rw [EqHom.map_sub, EqHom.map_smul] at h1
    exact sub_eq_zero.mp h1
  refine ⟨⟨S.g b, hc⟩, ?_⟩
  rw [connecting0_apply, H1.mk_eq_mk_iff, mem_B1']
  -- `S.sect c - b` has vanishing `g`-image, hence is `S.f a` for some `a : A`.
  have hsect0 : S.g (S.sect (S.g b) - b) = 0 := by
    rw [EqHom.map_sub, CoeffSES.g_sect, sub_self]
  obtain ⟨a, ha⟩ := (S.exact _).mp hsect0
  refine ⟨a, ?_⟩
  ext σ
  show σ • a - a
    = S.invFun (σ • S.sect (S.g b) - S.sect (S.g b))
      - (((z : Z1 G A) : Cochain1 G A) σ)
  have hsect : S.sect (S.g b) = b + S.f a := by
    rw [← sub_add_cancel (S.sect (S.g b)) b, ha, add_comm]
  have harg : σ • S.sect (S.g b) - S.sect (S.g b)
      = S.f (((z : Z1 G A) : Cochain1 G A) σ + (σ • a - a)) := by
    have hsplit : σ • S.sect (S.g b) - S.sect (S.g b)
        = (σ • b - b) + (σ • (S.f a) - S.f a) := by
      rw [hsect, smul_add]
      abel
    rw [hsplit, hb' σ, EqHom.map_add, EqHom.map_sub, EqHom.map_smul]
  have hinv : S.invFun (σ • S.sect (S.g b) - S.sect (S.g b))
      = ((z : Z1 G A) : Cochain1 G A) σ + (σ • a - a) :=
    invFun_eq_of_apply_eq S harg.symm
  rw [hinv]
  abel

end Work.ConCohomology
