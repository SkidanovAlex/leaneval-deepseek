/-
Copyright (c) 2025. All rights reserved.

# Proposition 11 of Schmidt–Wingberg, on the named arithmetic hypothesis

This file states and proves the two conditional forms of **Proposition 11** of

* A. Schmidt, K. Wingberg, *Šafarevič's theorem on solvable groups as Galois groups*,
  arXiv:math/9809211, §3,

in the abstract setting `Work.Properness.Setup`, and instantiates them for an embedding problem
over `ℚ` through the dictionary `Work.Properness.closureToSetup`.

## The paper's statement

> **Proposition 11.**  Let `K|k` be a finite Galois extension of global fields with Galois group
> `G = G(K|k)` and let `A = 𝔽_p[G]^n`.  Then the embedding problem with kernel `A` over `k` is
> properly solvable.

Its proof is the template for the whole chapter.  Since `A = 𝔽_p[G]^n` is induced (hence
cohomologically trivial), the embedding problem has a solution `ψ₀ : G_k → E`.  One then chooses
primes `p_1, …, p_r` of `k` that split completely in `K` and homomorphisms
`φ_i : G_{k_{p_i}} → A` whose images generate `A`; the Grunwald–Wang theorem provides a class
`[x] ∈ H¹(k, A)` with `res_i[x] = φ_i - ψ₀|_{G_{k_{p_i}}}`, and then `ψ := x · ψ₀` is a new
solution which *agrees with* `φ_i` on `G_{k_{p_i}}`; since the images of the `φ_i` generate `A`,
`ψ(G_K) = A` and `ψ` is surjective, i.e. **proper**.

The only arithmetic ingredient is the Grunwald–Wang step (existence of the global class realizing
the prescribed local behaviour), which is isolated here as the named hypothesis
`Work.Properness.Setup.ScholzGrunwaldWangInput`.  Everything else is unconditional group theory.

## Main declarations

* `Work.Properness.prop11` — the abstract conditional Proposition 11: given the named input and a
  compatible generating family of local maps, every lift of `ρ` is proper;
* `Work.Properness.prop11_agreeing` — the sharp form: the proper solution can be chosen to agree
  with the prescribed local maps `φ i` on `T i`;
* `Work.Properness.prop11_closure` — Proposition 11 for an embedding problem over `ℚ` (with a
  closure model `M`), in the language of `Work.Properness.closureToSetup`.

## A remark on the conclusion

The conclusion `Setup.HasProperLift` is the existence of a *surjective* lift
`ψ : G_ℚ →* E.G` with `M.pi ∘ ψ = restrictHom M.L`.  The paper's "proper solution" additionally
requires the kernel of `ψ` to be *open* (a Galois-theoretic continuity condition), which is what
`Work.AbsoluteGalois.HasSurjectiveLift` and `Submission.EmbeddingProblem.IsSolvable` ask for.  In
the profinite setting in which the paper works, every homomorphism is continuous (and all the
maps constructed above are), so this poses no additional condition; the abstract `Setup` carries
no topology and hence can only assert surjectivity.  See `Submission/Work/Properness/NOTES.md`.
-/
import Mathlib
import Submission.Work.Properness.Defs
import Submission.Work.Properness.BridgeDefs
import Submission.Work.Properness.exists_properLift_of_datum
import Submission.Work.Properness.exists_properLift_agreeing_of_datum
import Submission.Work.Properness.hasProperLift_of_scholzGrunwaldWang
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Properness

open scoped Classical

noncomputable section

universe u v w x

/-- **Proposition 11 (Schmidt–Wingberg), abstract conditional form.**

Assume the arithmetic input `Setup.ScholzGrunwaldWangInput` (Grunwald–Wang: prescribed compatible
local behaviour on subgroups `T i ≤ H_K` is realized by a global `1`-cocycle).  Then for every
lift `ψ₀` of `ρ`, every finite family of subgroups `T i ≤ H_K` and every family of homomorphisms
`φ i : T i →* A` whose images generate the abelian kernel `A`, there exists a **proper** lift of
`ρ`: the embedding problem with abelian kernel `A` is properly solvable.

This is the logical content of Proposition 11 of the paper; the arithmetic input is the named
hypothesis `h`, and is *not* proved in this development. -/
theorem prop11 {S : Setup.{u, v, w}} {ι : Type x} [Fintype ι] (ψ₀ : S.Lift)
    (T : ι → Subgroup S.H) (hT : ∀ i, T i ≤ S.HK) (φ : ∀ i, T i →* S.A)
    (h : S.ScholzGrunwaldWangInput ψ₀ T hT φ) (hgen : (⨆ i, (φ i).range) = ⊤) :
    S.HasProperLift :=
  hasProperLift_of_scholzGrunwaldWang ψ₀ T hT φ h hgen

/-- **The sharp form of Proposition 11.**  From a Grunwald–Wang *datum* (a global cocycle
realizing the prescribed differences) one obtains a proper lift `ψ` of `ρ` that *agrees with the
prescribed local maps*: `ψ t = φ i t` for all `t ∈ T i`.  This is exactly the conclusion of the
paper's proof of Proposition 11 ("`ψ|_{G_{k_{p_i}}} = φ_i`"), and properness follows because the
`φ i` generate `A`. -/
theorem prop11_agreeing {S : Setup.{u, v, w}} {ι : Type x} [Fintype ι] (ψ₀ : S.Lift)
    (T : ι → Subgroup S.H) (hT : ∀ i, T i ≤ S.HK) (φ : ∀ i, T i →* S.A)
    (hdat : S.GrunwaldWangDatum ψ₀ T hT φ) (hgen : (⨆ i, (φ i).range) = ⊤) :
    ∃ ψ : S.Lift, S.IsProper ψ ∧
      ∀ (i : ι) (t : T i), (ψ : S.H → S.E) (t : S.H) = (φ i t : S.E) :=
  @exists_properLift_agreeing_of_datum.{w, v, u, x, 0} PUnit PUnit.unit PUnit.unit PUnit.unit
    S ι _ ψ₀ T hT φ hdat hgen

/-- **Proposition 11 for an embedding problem over `ℚ`.**  With the dictionary
`Work.Properness.closureToSetup` (`H = G_ℚ`, `E = E.G`, `Q = Gal(M.L/ℚ)`, `π = M.pi`,
`ρ = restrictHom M.L`), the named arithmetic input produces a proper solution of the embedding
problem with abelian kernel, as soon as the prescribed local maps on subgroups of `H_K = ker ρ`
are compatible and their images generate the kernel. -/
theorem prop11_closure {E : Submission.EmbeddingProblem ℚ} (M : E.ClosureModel)
    (hcomm : ∀ a b : M.pi.ker, a * b = b * a) {ι : Type x} [Fintype ι]
    (ψ₀ : (closureToSetup M hcomm).Lift) (T : ι → Subgroup (closureToSetup M hcomm).H)
    (hT : ∀ i, T i ≤ (closureToSetup M hcomm).HK)
    (φ : ∀ i, T i →* (closureToSetup M hcomm).A)
    (h : (closureToSetup M hcomm).ScholzGrunwaldWangInput ψ₀ T hT φ)
    (hgen : (⨆ i, (φ i).range) = ⊤) :
    (closureToSetup M hcomm).HasProperLift :=
  hasProperLift_of_scholzGrunwaldWang ψ₀ T hT φ h hgen

end

end Work.Properness
