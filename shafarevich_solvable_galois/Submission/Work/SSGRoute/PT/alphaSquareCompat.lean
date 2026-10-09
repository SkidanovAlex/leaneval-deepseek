import Mathlib
import Submission.Work.SSGRoute.PT.alphaConnectingCompat
import Submission.Work.AbsoluteKummer.SES.ConnectingH2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The third square of Milne's diagram (1.9.1) at `r = 1`, against the `SES` API

`PT/alphaConnectingCompat.lean` proves the cochain identity of the third square of Milne's diagram
(1.9.1) — `d¹(cLift ⌣ n) = ⟨d¹cLift, n⟩ − cLift ⌣ d⁰n` (`d1_cupConn10_eq_of_shortExact`), its
`B²`-form `SES_cupConn_sub_mem_B2` and its `H²`-form `SES_cupConn_H2π_eq` — for a *given* lift
`cLift` of the coefficient cocycle.  This module performs the two comparisons with the workspace's
`ShortExactSeq` API, so that the square can be stated with the API's own connecting maps
(`S.deltaH2`, `S.delta`) and their `liftCochainC` / `cocycleOf` representatives:

* `alphaSquare_deltaCocycleC_eval` — the coefficient connecting cocycle `Scoef.deltaCocycleC c`
  evaluated at the invariant `n ∈ H⁰(G,P)` equals `d¹ (Scoef.liftCochainC c)` evaluated at the
  lift `Smod.liftOf n`;
* `alphaSquare_cupConn11_lift_d0` — `cupConn11` of the same lift with `d⁰(Smod.liftOf n)` equals
  `cupConn11` of `c` with the module connecting cocycle `Smod.cocycleOf (Smod.liftOf n)`;
* `alphaSquare_cochain` — consequently the difference of those two cochains is the coboundary
  `d¹(cupConn10 (Scoef.liftCochainC c) (Smod.liftOf n))` (the cochain form of the square, in the
  API's notation).

Together with `alphaConnectingCompat`'s `d1_eval_mem_Z2` / `SES_cupConn_H2π_eq` this gives the
Leibniz square `α²(δc)(n) = α¹(c)(δn)` of `PT/alphaOneLayer.alphaOne_bijective_of_devissage`
(five-lemma descent at `r = 1` of Milne *ADT* I.1.8); see
`PT/PING_back_alphaConnectingCompat.md` §2 for the bookkeeping between the two files.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open Classical

namespace Work.SSGRoute.PT

universe u v w

section Square

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [DistribMulAction G M]
  {N : Type v} [AddCommGroup N] [DistribMulAction G N]
  {P : Type v} [AddCommGroup P] [DistribMulAction G P]
  {C : Type w} [AddCommGroup C] [DistribMulAction G C]

/-- **The coefficient connecting cocycle evaluated at an invariant.**  With

* `Smod : 0 → M → N → P → 0` the *module* short exact sequence,
* `Scoef : 0 → Hom_ℤ(P,C) → Hom_ℤ(N,C) → Hom_ℤ(M,C) → 0` the *coefficient* one, with its maps the
  transposes of `Smod`'s (`hι`, `hπ`),
* `c : Z¹(G, Hom_ℤ(M,C))` a coefficient `1`-cocycle and `n ∈ H⁰(G,P)` an invariant,

the connecting cocycle `Scoef.deltaCocycleC c`, evaluated at `n`, is the cocycle
`d¹(G, Hom_ℤ(N,C)) (Scoef.liftCochainC c)` evaluated at the chosen lift `Smod.liftOf n`. -/
theorem alphaSquare_deltaCocycleC_eval
    (Smod : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (Scoef : Work.AbsoluteKummer.ShortExactSeq G (ConjHom P C) (ConjHom N C) (ConjHom M C))
    (hι : ∀ x : ConjHom P C, (Scoef.iota x : ConjHom N C) = ConjHom.precomp Smod.pi x)
    (c : Work.AbsoluteKummer.Z1 G (ConjHom M C)) (n : ↥(Work.AbsoluteKummer.H0 G P)) :
    (fun p : G × G => (Scoef.deltaCocycleC c : G × G → ConjHom P C) p (n : P))
      = fun p : G × G =>
          (Work.GroupCohomology.d1 G (ConjHom N C)
            (Scoef.liftCochainC (c : G → ConjHom M C)) p) (Smod.liftOf n) := by
  funext p
  obtain ⟨g, h⟩ := p
  set u : ConjHom N C :=
    Work.GroupCohomology.d1 G (ConjHom N C) (Scoef.liftCochainC (c : G → ConjHom M C)) (g, h)
    with hu
  have hrange : u ∈ Scoef.iota.range :=
    Scoef.mem_range_of_mem_ker (by
      rw [AddMonoidHom.mem_ker, hu]
      exact Scoef.pi_d1_liftCochainC c g h)
  have h1 : (Scoef.iota (Scoef.iotaInv u) : ConjHom N C) = u := Scoef.iota_iotaInv hrange
  rw [hι (Scoef.iotaInv u)] at h1
  have h3 := congrArg (fun φ : ConjHom N C => φ (Smod.liftOf n)) h1
  simp only [ConjHom.precomp_apply, Smod.pi_liftOf] at h3
  rw [Scoef.deltaCocycleC_apply]
  exact h3

/-- **The cup of the coefficient lift with the module connecting cocycle.**  With `Smod`, `Scoef`,
`hι`, `hπ`, `c`, `n` as in `alphaSquare_deltaCocycleC_eval`, cupping the lifted cochain
`Scoef.liftCochainC c` with the coboundary `d⁰(Smod.liftOf n)` (an `N`-valued `1`-cochain) is the
same as cupping `c` itself with the module connecting cocycle `Smod.cocycleOf (Smod.liftOf n)`. -/
theorem alphaSquare_cupConn11_lift_d0
    (Smod : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (Scoef : Work.AbsoluteKummer.ShortExactSeq G (ConjHom P C) (ConjHom N C) (ConjHom M C))
    (hπ : ∀ y : ConjHom N C, (Scoef.pi y : ConjHom M C) = ConjHom.precomp Smod.iota y)
    (c : Work.AbsoluteKummer.Z1 G (ConjHom M C)) (n : ↥(Work.AbsoluteKummer.H0 G P)) :
    cupConn11 (Scoef.liftCochainC (c : G → ConjHom M C))
        (Work.GroupCohomology.d0 G N (Smod.liftOf n))
      = cupConn11 (c : G → ConjHom M C)
          (((Smod.cocycleOf (Smod.liftOf n) (Smod.liftOf_invariant n) :
            Work.AbsoluteKummer.Z1 G M) : G → M)) := by
  funext p
  obtain ⟨g, h⟩ := p
  set z : M := ((Smod.cocycleOf (Smod.liftOf n) (Smod.liftOf_invariant n) :
    Work.AbsoluteKummer.Z1 G M) : G → M) h with hz
  have hcoc : Smod.iota z = h • Smod.liftOf n - Smod.liftOf n :=
    Smod.iota_cocycleOf (Smod.liftOf n) (Smod.liftOf_invariant n) h
  have hA : Scoef.liftCochainC (c : G → ConjHom M C) g (Smod.iota (g • z))
      = (Scoef.pi (Scoef.liftCochainC (c : G → ConjHom M C) g)) (g • z) := by
    rw [hπ (Scoef.liftCochainC (c : G → ConjHom M C) g), ConjHom.precomp_apply]
  simp only [cupConn11_apply, Work.GroupCohomology.d0_apply]
  have hstep : g • (h • Smod.liftOf n - Smod.liftOf n) = Smod.iota (g • z) := by
    rw [Smod.iota_equivariant g z, hcoc]
  rw [hstep, hA, Scoef.pi_liftCochainC]

/-- **The third square of (1.9.1) in the API's notation, at the cochain level.**  The difference of
the two composites — the coefficient connecting cocycle evaluated at `n`, and the cup of `c` with
the module connecting cocycle — is the coboundary `d¹(cupConn10 (Scoef.liftCochainC c)
(Smod.liftOf n))`. -/
theorem alphaSquare_cochain
    (Smod : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (Scoef : Work.AbsoluteKummer.ShortExactSeq G (ConjHom P C) (ConjHom N C) (ConjHom M C))
    (hι : ∀ x : ConjHom P C, (Scoef.iota x : ConjHom N C) = ConjHom.precomp Smod.pi x)
    (hπ : ∀ y : ConjHom N C, (Scoef.pi y : ConjHom M C) = ConjHom.precomp Smod.iota y)
    (c : Work.AbsoluteKummer.Z1 G (ConjHom M C)) (n : ↥(Work.AbsoluteKummer.H0 G P)) :
    (fun p : G × G => (Scoef.deltaCocycleC c : G × G → ConjHom P C) p (n : P))
      - cupConn11 (c : G → ConjHom M C)
          (((Smod.cocycleOf (Smod.liftOf n) (Smod.liftOf_invariant n) :
            Work.AbsoluteKummer.Z1 G M) : G → M))
      = Work.GroupCohomology.d1 G C
          (cupConn10 (Scoef.liftCochainC (c : G → ConjHom M C)) (Smod.liftOf n)) := by
  have h1 := alphaSquare_deltaCocycleC_eval Smod Scoef hι c n
  have hlift : ∀ (g : G) (m : M), Scoef.liftCochainC (c : G → ConjHom M C) g (Smod.iota m)
      = (c : G → ConjHom M C) g m := by
    intro g m
    have h := congrArg (fun φ : ConjHom M C => φ m)
      (Scoef.pi_liftCochainC (c : G → ConjHom M C) g)
    rw [hπ (Scoef.liftCochainC (c : G → ConjHom M C) g)] at h
    simpa only [ConjHom.precomp_apply] using h
  have h3 := d1_cupConn10_eq_of_shortExact (S := Smod)
    (c := (c : G → ConjHom M C)) (cLift := Scoef.liftCochainC (c : G → ConjHom M C))
    hlift (fun g h => c.2.1 g h) (Smod.liftOf n) (Smod.liftOf_invariant n)
  rw [h1, ← alphaSquare_cupConn11_lift_d0 Smod Scoef hπ c n]
  exact h3.symm

end Square

end Work.SSGRoute.PT
