/-
  WilC5 — the sub-specification of area C5 (a-w): the two statements that the wiring
  `Main.lean` consumes.

  The frozen hole is `WilkiesDesign.CG.C5_TE_modelComplete`

      `theorem C5_TE_modelComplete (hMCr : ModelComplete TR) (hOM : OMinModels)
          (hVI : ValIneq) : ModelComplete TE`

  i.e. "the theory `TE = Th(ℝ_exp)` is model complete", given (a) model completeness of `TR` (the
  theory of `ℝ_rexp`), (b) o-minimality of models of `TR`, and (c) Wilkie's valuation inequality
  for `TR`.

  The proof splits into two halves.

  * `reductEmbedding_of_TE` (*mechanical*, **proved**): an embedding of models of `TE` is an
    embedding of the `rexp`-reducts (`Bridge.lean`, `Reduct.lean`).  The only input beyond the
    definitions is that the definable order `leE x y := ∃z, z*z = y - x` is a linear order in every
    model of `TE`; this transfers from `ℝ` by elementarity, and gives the reflection of `|x| ≤ 1`
    needed to see that `rexpFromExp` is preserved.

  * `Ressayre_step` (**proved from the residual statement `Work.WilC5.S4SubTE`**): the `LEc`-type of
    a tuple in a model of `TE` is determined by its `LRc`-type.  This is the model-theoretic content
    of van den Dries–Macintyre–Marker, *The elementary theory of restricted analytic fields with
    exponentiation*, Ann. of Math. 140 (1994), §4 — their embedding theorem 4.1 (built from the
    extension lemmas 4.2, 4.3 and 4.4 and the saturation/compactness machinery) — together with
    Ressayre's theorem, quoted in their (4.10): the theory of `(ℝ, exp)` is axiomatized by the
    theory of `ℝ_rexp` together with the axioms E1)–E5) for an increasing surjective exponential.

    The route taken here is the embedding-theorem one: `Work.WilC5.S4SubTE` is vdDMM Theorem 4.1
    for `TE` (submodel domains), `Work.WilC5.ModelComplete_TE_of_S4SubTE` derives
    `ModelComplete TE` from it, and both `Ressayre_step` and `Ressayre_step_unif` below are then
    immediate.  See `S4_LAYER.md` §8 for the state of the §4 content.
-/
import Submission.Work.WilC5.ReductEmb
import Submission.Work.WilC5.Synthesis
import Submission.Work.WilC5.S4Residual

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **`ME1`: an embedding of models of `TE` restricts to an embedding of `rexp`-reducts.**
Mechanical: it uses that `rexpFromExp` is the definable function `|x| ≤ 1 ? exp x : 0`, and that
the definable order of a model of `TE` is a linear order (transferred from `ℝ` by elementarity),
so that the condition `|x| ≤ 1` is reflected by the embedding. -/
theorem reductEmbedding_of_TE {M N : Type} [LEc.Structure M] [LEc.Structure N]
    (hM : M ⊨ TE) (hN : N ⊨ TE) (f : M ↪[LEc] N) :
    ∃ fR : @Embedding LRc M N (reductStruct M) (reductStruct N), (fR : M → N) = f :=
  ReductEmb hM hN f

/-- **`ME2` (RESEARCH, vdDMM §4 + (4.10)): the `LEc`-type is determined by the `LRc`-type.**

If `f : M ↪[LEc] N` between models of `TE` is elementary for the `rexp`-reducts, then it is
elementary.  This is Ressayre's theorem in the form used by van den Dries–Macintyre–Marker: the
theory of `(ℝ, exp)` is axiomatized over the theory of `ℝ_rexp` by the axioms E1)–E5) for an
increasing surjective exponential, and `T_an(exp)` admits quantifier elimination in the language
with `log` and the parameter-free `𝓡`-definable functions (their Corollary 4.5). -/
theorem Ressayre_step (hMCr : ModelComplete TR) (hOM : OMinModels) (hVI : ValIneq)
    (hVP : Work.WilC5.ValProp)
    {M N : Type} [LEc.Structure M] [LEc.Structure N] (hM : M ⊨ TE) (hN : N ⊨ TE)
    (f : M ↪[LEc] N)
    (hf : ∀ {n : ℕ} (ψ : LRc.Formula (Fin n)) (x : Fin n → M),
      @Formula.Realize LRc N (reductStruct N) (Fin n) ψ ((f : M → N) ∘ x) ↔
        @Formula.Realize LRc M (reductStruct M) (Fin n) ψ x)
    {n : ℕ} (φ : LEc.Formula (Fin n)) (x : Fin n → M) :
    φ.Realize ((f : M → N) ∘ x) ↔ φ.Realize x := by
  exact @Work.WilC5.ModelComplete_TE_of_S4SubTE (Work.WilC5.S4SubTE_proved hMCr hOM hVI hVP)
    M N _ _ hM hN f n φ x

/-- **`ME2'` (same content as `Ressayre_step`, with the extra hypothesis `hUF`).**

Wilkie's proof of model completeness of `T_exp` (lecture notes, §6) has two cases.  Case 1 (`r = n`)
counts the non-singular zeros of a quasipolynomial inside a box and needs a bound that is
*uniform in the parameters* (`M*₀ ⊨ ∃^{=k} x ∈ (-N,N)^n (F(x) = 0 ∧ JF(x) ≠ 0)` with `k` depending
only on the format), which is Khovanskii's theorem; the model-level o-minimality statement `hOM`
does not obviously supply it.  `UnifFiniteRExp` is exactly that uniformity, recorded in the frozen
specification of area E (as `E0b_unif_finite`) and proposed there as an extra hypothesis for C.

This is the form of `ME2` that a prover should attack if `ME2` turns out not to be derivable from
`hMCr`, `hOM`, `hVI` alone.  It is *weaker* than `Ressayre_step` (one extra hypothesis), so
proving it gives the lead a usable `C5` at the cost of adding `hUF` to the frozen signature. -/
theorem Ressayre_step_unif (hMCr : ModelComplete TR) (hOM : OMinModels) (hVI : ValIneq)
    (hUF : UnifFiniteRExp) (hVP : Work.WilC5.ValProp)
    {M N : Type} [LEc.Structure M] [LEc.Structure N] (hM : M ⊨ TE) (hN : N ⊨ TE)
    (f : M ↪[LEc] N)
    (hf : ∀ {n : ℕ} (ψ : LRc.Formula (Fin n)) (x : Fin n → M),
      @Formula.Realize LRc N (reductStruct N) (Fin n) ψ ((f : M → N) ∘ x) ↔
        @Formula.Realize LRc M (reductStruct M) (Fin n) ψ x)
    {n : ℕ} (φ : LEc.Formula (Fin n)) (x : Fin n → M) :
    φ.Realize ((f : M → N) ∘ x) ↔ φ.Realize x := by
  exact @Work.WilC5.ModelComplete_TE_of_S4SubTE (Work.WilC5.S4SubTE_proved hMCr hOM hVI hVP)
    M N _ _ hM hN f n φ x

end Work.WilC5
