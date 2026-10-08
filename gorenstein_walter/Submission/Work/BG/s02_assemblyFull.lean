import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02c_LamEquiv_sconj

/-!
# Area BG: assembly of the full Coherence Theorem 2.3 (A-2)

This file proves `Work.BG.s02_assemblyFull`, the design-pass-10 item **A-2** of
`NOTES_BG_s02_leaves.md`:

```
AssemblyFullProp C  =  GramProp C → BSValueTProp C → Coherence23CoreProp C → Coherence23Prop C.
```

Bender–Glauberman's Coherence Theorem 2.3 (p. 206) has six clauses.  Clauses (i), (ii),
(iii) and (vi) together with `ν̃^s = ν̃` are exactly `GoodOn C (orbitKey C ν) f`
(`Coherence23CoreProp`), which is the *input* `hcore` here; the two remaining clauses are

* **(iv)** `⟨f μ₁ - f ν₁, f μ₂ - f ν₂⟩ = 0` for `μᵢ ~ νᵢ` (`Λ`-equivalence) with
  `μ₁` not `Λ`-equivalent to `μ₂` nor to `μ₂^{s}`;
* **(v)** `(f μ - f ν)(g) = (μ - ν)(g) + (μ - ν)(s g s⁻¹)` for `g ∈ H₀ ∖ U`.

Both are proved here from the two §1 inputs `GramProp` (the Brauer–Suzuki Gram matrix,
Lemma 1.3 + Remark 1.4) and `BSValueTProp` (the value form of Lemma 1.3 on `T`), applied to
the *same* `f` supplied by the core.

* **(v)** is immediate: `GoodOn` at `ν` says `ind C (μ - ν) = f μ - f ν`, and
  `BSValueTProp` evaluates `ind C (μ - ν)` at `g`.  (`GoodOn` is applied at the key
  `orbitKey C μ`; both `μ` and `ν` lie on it, using `Λ`-reflexivity and `hL`.)

* **(iv)** `GramProp` computes the inner product as the `cH`-combination
  `cH μ₁ μ₂ - cH μ₁ ν₂ - cH ν₁ μ₂ + cH ν₁ ν₂`, where `cH α β = [β = α] + [β = α^s]`
  (Remark 1.4).  `GoodOn` at `μ₁`, resp. `μ₂`, rewrites `f μᵢ - f νᵢ = ind C (μᵢ - νᵢ)`.
  Each of the four `cH` terms then vanishes: the hypotheses
  `¬ LamEquiv C μ₁ μ₂` and `¬ LamEquiv C (sconj C μ₁) μ₂`, propagated along the
  `Λ`-equivalences `μᵢ ~ νᵢ` (via the equivalence-relation and `s`-invariance facts of
  `Submission/Work/BG/s02_assemblyCore.lean` and `s02c_LamEquiv_sconj.lean`), exclude all
  eight equalities.  This is the reason the hypothesis is stated with `sconj C μ₁`: the
  `s`-conjugate of an orbit is again an orbit, so `ν₂` may be `s`-conjugate to `μ₁` even
  when `μ₂` is not.

The remaining `Λ`-bookkeeping (`λ_β` is multiplicative, `Λ`-equivalence is an equivalence
relation, and `s` acts compatibly) is proved once in `s02_assemblyCore.lean` (items
`s02c_lamCF_mul`, `s02c_lamCF_one_mul`, `s02c_LamEquiv_{refl,symm,trans}`) and in
`s02c_LamEquiv_sconj.lean`; this file only assembles.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- `cH C a b = 0` as soon as `a` is not `Λ`-equivalent to `b` and not to `b` with `s`
inverted: `cH C a b = [b = a] + [b = a^s]` (Remark 1.4), and each hypothesis rules out the
corresponding equality through `Λ`-reflexivity. -/
lemma s02f_cH_eq_zero {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {a b : ClassFunction ↥C.P.H0 ℂ}
    (h1 : ¬ LamEquiv C a b) (h2 : ¬ LamEquiv C (sconj C a) b) : cH C a b = 0 := by
  unfold cH
  have h1' : ¬ (b = a) := fun h => h1 (h ▸ s02c_LamEquiv_refl C b)
  have h2' : ¬ (b = sconj C a) := fun h => h2 (h ▸ s02c_LamEquiv_refl C (sconj C a))
  rw [ite_eq_right h1', ite_eq_right h2', add_zero]

/-- **A-2. BG Theorem 2.3, clauses (iv) and (v) from the core.**

Given the Brauer–Suzuki Gram matrix (`GramProp`, I-2), the value form of Lemma 1.3 on `T`
(`BSValueTProp`, I-3′) and the core of Theorem 2.3 (`Coherence23CoreProp`, A-1), the
coherent map of the core also satisfies the two remaining clauses (iv) and (v), so that
`Coherence23Prop` holds. -/
theorem s02_assemblyFull {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.BG.AssemblyFullProp C := by
  intro hG hB hcore
  obtain ⟨f, hf⟩ := hcore
  refine ⟨f, hf, ?_, ?_⟩
  · -- (iv): all four `cH` terms of the Gram matrix vanish
    intro μ₁ ν₁ μ₂ ν₂ hμ₁ hν₁ hμ₂ hν₂ hL1 hL2 h12 h1s2
    -- `μ₁, ν₁ ∈ orbitKey C μ₁` and `μ₂, ν₂ ∈ orbitKey C μ₂`
    have hμ₁mem : μ₁ ∈ orbitKey C μ₁ := Or.inl (s02c_LamEquiv_refl C μ₁)
    have hν₁mem : ν₁ ∈ orbitKey C μ₁ := Or.inl hL1
    have hμ₂mem : μ₂ ∈ orbitKey C μ₂ := Or.inl (s02c_LamEquiv_refl C μ₂)
    have hν₂mem : ν₂ ∈ orbitKey C μ₂ := Or.inl hL2
    -- `GoodOn` identifies `f μᵢ - f νᵢ` with the induced difference
    have e1 : ind C (μ₁ - ν₁) = f μ₁ - f ν₁ :=
      ((hf μ₁ hμ₁) μ₁ hμ₁mem ν₁ hν₁mem hμ₁ hν₁).2.2.2.1 hL1
    have e2 : ind C (μ₂ - ν₂) = f μ₂ - f ν₂ :=
      ((hf μ₂ hμ₂) μ₂ hμ₂mem ν₂ hν₂mem hμ₂ hν₂).2.2.2.1 hL2
    -- propagate the exclusions from `(μ₁, μ₂)` to the four `cH` pairs
    have hn11 : ¬ LamEquiv C μ₁ ν₂ :=
      fun h => h12 (s02c_LamEquiv_trans C h (s02c_LamEquiv_symm C hL2))
    have hn12 : ¬ LamEquiv C (sconj C μ₁) ν₂ :=
      fun h => h1s2 (s02c_LamEquiv_trans C h (s02c_LamEquiv_symm C hL2))
    have hn31 : ¬ LamEquiv C ν₁ μ₂ :=
      fun h => h12 (s02c_LamEquiv_trans C hL1 h)
    have hn32 : ¬ LamEquiv C (sconj C ν₁) μ₂ :=
      fun h => h1s2 (s02c_LamEquiv_trans C (s02c_LamEquiv_sconj C hL1) h)
    have hn41 : ¬ LamEquiv C ν₁ ν₂ :=
      fun h => h12 (s02c_LamEquiv_trans C (s02c_LamEquiv_trans C hL1 h)
        (s02c_LamEquiv_symm C hL2))
    have hn42 : ¬ LamEquiv C (sconj C ν₁) ν₂ :=
      fun h => h1s2 (s02c_LamEquiv_trans C
        (s02c_LamEquiv_trans C (s02c_LamEquiv_sconj C hL1) h) (s02c_LamEquiv_symm C hL2))
    rw [← e1, ← e2, hG μ₁ ν₁ μ₂ ν₂ hμ₁ hν₁ hμ₂ hν₂ hL1 hL2,
      s02f_cH_eq_zero C h12 h1s2, s02f_cH_eq_zero C hn11 hn12,
      s02f_cH_eq_zero C hn31 hn32, s02f_cH_eq_zero C hn41 hn42]
    ring
  · -- (v): `BSValueTProp` on `ind C (μ - ν) = f μ - f ν`
    intro μ ν hμ hν hL g hg
    have hμmem : μ ∈ orbitKey C μ := Or.inl (s02c_LamEquiv_refl C μ)
    have hνmem : ν ∈ orbitKey C μ := Or.inl hL
    have e : ind C (μ - ν) = f μ - f ν :=
      ((hf μ hμ) μ hμmem ν hνmem hμ hν).2.2.2.1 hL
    rw [← e, hB μ ν hμ hν hL g hg]

end Work.BG
