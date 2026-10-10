import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.H9.swHistKExists_proved
import Submission.Work.SSGRoute.NodeS35.swPinFamily
import Submission.Work.SSGRoute.NodeS37.defs
import Submission.Work.SSGRoute.P2Core.escapeStepNormalised
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p = 2` §4 recursion: the Ψ-vector and the prescribed datum

This file sets up the vocabulary of the `p = 2` recursion of Schmidt--Wingberg §4 (see
`ZDataTwo/NOTE_two_recursion_DESIGN.md`).

A *history* is `f : ℕ → (ValuationSubring Ω × (↥K)ˣ)` with `IsFinPlace` all along (`hf`), the
`m`-th entry being the escape prime `Q_m` together with the element `b_m ∈ Kˣ` whose Kummer cochain
is the `m`-th class.

* `sibVal` — the value of `χ_b` at a Frobenius pinned at the Kummer level of `b` above the
  σ-sibling `galLift K σ • Q` of the escape prime `Q` (the pair `(Q,b)` is passed as one argument,
  so that a rewriting `(f l) = (g l)` applies to the whole datum, see `prescDatum_congr`);
* `psiVal` — the **Ψ-vector** entry, `sibVal` at the `θ υ`-sibling;
* `valSeq` — the ℕ-indexed sequence of Ψ-vectors, i.e. the `val` of `NodeS37/defs.lean`;
* `eGam` / `eScalar` / `attScalar` — the **branch scalar** of the paper's condition (4) and its
  attachment-restricted form; `prVal_eq_eGam_smul` records that the prescribed value of the rule is
  `e • val`;
* `prescDatum` — the **prescribed local datum** `h_m A` at a block `A` of `T_m`: `0` at the
  `S`-blocks, and `-y + Σ_{l<m} Σ_ρ attScalar · χ_{b_l}` otherwise, where the sum runs over the
  finitely many candidate attachments `(l,ρ)`; at a block whose attachment is *unique* it collapses
  to `-y + e · χ_{b_l}` (`prescDatum_eq_of_attachment`), and the total datum the oracle realises
  there is `e · χ_{b_l}`, the value prescribed by (4).  The sum form is *choice-free*, which is what
  makes `prescDatum_congr` (invariance under a prefix change of the history) provable;
* `TBlock` — the place set `T_m = krep K (kleadReps K S ∪ ⋃_{j<m} kleadReps K {Q_j})`, pairwise
  non-`K`-conjugate, covering the `K`-classes above the `k`-classes of `S` and of the escape primes.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

section Defs

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-! ## The Ψ-vector -/

/-- **The value of `χ_b` at the pinned Frobenius of the σ-sibling of the escape prime `Q`**, the
pair `q = (Q, b)` being passed as a single argument so that rewriting the history at an index
rewrites the whole expression. -/
noncomputable def sibVal (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (q : ValuationSubring Ω × (↥K)ˣ) (σ : K ≃ₐ[k] K) : ZMod 2 := by
  classical
  exact
    if h : SSGRoute.IsFinPlace k q.1 then
      Work.SSGRoute.NodeS35.pinValue (K := K) (p := 2) ζ hζ hζK (fun _ => q) (fun _ => h) 0 σ
    else 0

/-- **The Ψ-vector entry of a stage**: the value of `χ_b` at the pinned Frobenius of the
`θ υ`-sibling of `Q`. -/
noncomputable def psiVal (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (q : ValuationSubring Ω × (↥K)ˣ) (υ : Work.SSGRoute.NodeS37.Gam K) : ZMod 2 :=
  sibVal (K := K) ζ hζ hζK q (Work.SSGRoute.NodeS37.theta υ).1

/-- **The sequence of Ψ-vectors of a history**: the `val` of `NodeS37/defs.lean`. -/
noncomputable def valSeq (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) : ℕ → Work.SSGRoute.NodeS37.Gam K → ZMod 2 :=
  fun m υ => psiVal (K := K) ζ hζ hζK (f m) υ

/-- **The witness predicate of the rule (4)** for the pair `(l, m)` of the history. -/
noncomputable abbrev wit (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (l m : ℕ) : Prop :=
  Work.SSGRoute.NodeS37.Witness (valSeq (K := K) ζ hζ hζK f) l m

/-- **The Ψ-vector of a history depends only on the entry at its own index.** -/
theorem valSeq_congr {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {f g : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {l m : ℕ} (hlm : l < m)
    (h : ∀ i, i < m → f i = g i) (υ : Work.SSGRoute.NodeS37.Gam K) :
    valSeq (K := K) ζ hζ hζK f l υ = valSeq (K := K) ζ hζ hζK g l υ := by
  show psiVal (K := K) ζ hζ hζK (f l) υ = psiVal (K := K) ζ hζ hζK (g l) υ
  rw [h l hlm]

/-- **The witness predicate depends only on the entries of the history below the stage index.** -/
theorem witness_congr {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {f g : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {l m : ℕ}
    (h : ∀ i, i < m → f i = g i) :
    Work.SSGRoute.NodeS37.Witness (valSeq (K := K) ζ hζ hζK f) l m ↔
      Work.SSGRoute.NodeS37.Witness (valSeq (K := K) ζ hζ hζK g) l m := by
  constructor
  · rintro ⟨t, hlt, htm, hval⟩
    refine ⟨t, hlt, htm, fun τ => ?_⟩
    rw [← valSeq_congr (K := K) (m := m) (l := t) htm h τ,
      ← valSeq_congr (K := K) (m := m) (l := l) (lt_trans hlt htm) h τ, hval τ]
  · rintro ⟨t, hlt, htm, hval⟩
    refine ⟨t, hlt, htm, fun τ => ?_⟩
    rw [valSeq_congr (K := K) (m := m) (l := t) htm h τ,
      valSeq_congr (K := K) (m := m) (l := l) (lt_trans hlt htm) h τ, hval τ]

/-- **The branch scalar of the rule (4).**  `eGam l m υ` is `1` exactly when the rule prescribes the
"own value" at the `υ`-block of the `l`-th escape prime (for the class of stage `m`), and `0` when
it prescribes `0`. -/
noncomputable def eGam (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (l m : ℕ)
    (υ : Work.SSGRoute.NodeS37.Gam K) : ZMod 2 := by
  classical
  exact if Work.SSGRoute.NodeS37.IsInv υ then 0
    else if Work.SSGRoute.NodeS37.theta υ = υ then
      (if Work.SSGRoute.NodeS37.Witness (valSeq (K := K) ζ hζ hζK f) l m then 1 else 0)
    else
      (if Work.SSGRoute.NodeS37.Witness (valSeq (K := K) ζ hζ hζK f) l m then 0 else 1)

/-- **The branch scalar depends only on the entries of the history below the stage index.** -/
theorem eGam_congr {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {f g : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {l m : ℕ}
    (h : ∀ i, i < m → f i = g i) (υ : Work.SSGRoute.NodeS37.Gam K) :
    eGam (K := K) ζ hζ hζK f l m υ = eGam (K := K) ζ hζ hζK g l m υ := by
  classical
  have hW := witness_congr (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK) (l := l) (m := m) h
  by_cases hI : Work.SSGRoute.NodeS37.IsInv υ
  · rw [eGam, eGam, if_pos hI, if_pos hI]
  · by_cases hth : Work.SSGRoute.NodeS37.theta υ = υ
    · rw [eGam, eGam, if_neg hI, if_neg hI, if_pos hth, if_pos hth]
      by_cases hW' : Work.SSGRoute.NodeS37.Witness (valSeq (K := K) ζ hζ hζK f) l m
      · rw [if_pos hW', if_pos (hW.mp hW')]
      · rw [if_neg hW', if_neg (fun hc => hW' (hW.mpr hc))]
    · rw [eGam, eGam, if_neg hI, if_neg hI, if_neg hth, if_neg hth]
      by_cases hW' : Work.SSGRoute.NodeS37.Witness (valSeq (K := K) ζ hζ hζK f) l m
      · rw [if_pos hW', if_pos (hW.mp hW')]
      · rw [if_neg hW', if_neg (fun hc => hW' (hW.mpr hc))]

/-- **The branch scalar, indexed by an element of `G(K|k)`** (`0` at `ρ = 1`, the escape prime's own
`K`-class). -/
noncomputable def eScalar (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (l m : ℕ) (ρ : K ≃ₐ[k] K) : ZMod 2 := by
  classical
  exact if h : ρ = 1 then 0 else eGam (K := K) ζ hζ hζK f l m ⟨ρ, h⟩

/-- **The branch scalar depends only on the entries of the history below the stage index.** -/
theorem eScalar_congr {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {f g : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {l m : ℕ}
    (h : ∀ i, i < m → f i = g i) (ρ : K ≃ₐ[k] K) :
    eScalar (K := K) ζ hζ hζK f l m ρ = eScalar (K := K) ζ hζ hζK g l m ρ := by
  classical
  rw [eScalar, eScalar]
  by_cases hρ : ρ = 1
  · rw [dif_pos hρ, dif_pos hρ]
  · rw [dif_neg hρ, dif_neg hρ]
    exact eGam_congr (K := K) h _

/-- **The prescribed value of the rule (4) is the branch scalar times the own value**, in the form
in which both sides mention the `Ψ`-vector of the history at the index `l`. -/
theorem prVal_eq_eGam_smul_valSeq (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (l m : ℕ)
    (υ : Work.SSGRoute.NodeS37.Gam K) :
    Work.SSGRoute.NodeS37.prVal (valSeq (K := K) ζ hζ hζK f) m l υ
      = eGam (K := K) ζ hζ hζK f l m υ • valSeq (K := K) ζ hζ hζK f l υ := by
  classical
  have hI := Work.SSGRoute.NodeS37.theta_eq_self_or_ginv υ
  by_cases hInv : Work.SSGRoute.NodeS37.IsInv υ
  · rw [Work.SSGRoute.NodeS37.prVal_of_inv hInv, eGam, if_pos hInv, zero_smul]
  · by_cases hth : Work.SSGRoute.NodeS37.theta υ = υ
    · rw [Work.SSGRoute.NodeS37.prVal_of_self hInv hth, eGam, if_neg hInv, if_pos hth]
      by_cases hW : Work.SSGRoute.NodeS37.Witness (valSeq (K := K) ζ hζ hζK f) l m
      · rw [if_pos hW, if_pos hW, one_smul]
      · rw [if_neg hW, if_neg hW, zero_smul]
    · have hgi : Work.SSGRoute.NodeS37.theta υ = Work.SSGRoute.NodeS37.ginv υ :=
        hI.resolve_left hth
      rw [Work.SSGRoute.NodeS37.prVal_of_ginv hInv hgi, eGam, if_neg hInv, if_neg hth]
      by_cases hW : Work.SSGRoute.NodeS37.Witness (valSeq (K := K) ζ hζ hζK f) l m
      · rw [if_pos hW, if_pos hW, zero_smul]
      · rw [if_neg hW, if_neg hW, one_smul]

/-- **The prescribed value of the rule (4) is the branch scalar times the own value.**  This is the
bridge between the rule formalised in `NodeS37/defs.lean` and the branch scalar used in the
recursion; the right-hand factor is the `Ψ`-entry, i.e. the pinned value at the sibling. -/
theorem prVal_eq_eGam_smul (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (l m : ℕ)
    (υ : Work.SSGRoute.NodeS37.Gam K) :
    Work.SSGRoute.NodeS37.prVal (valSeq (K := K) ζ hζ hζK f) m l υ
      = eGam (K := K) ζ hζ hζK f l m υ
        • psiVal (K := K) ζ hζ hζK (f l) υ :=
  prVal_eq_eGam_smul_valSeq (K := K) ζ hζ hζK f l m υ

/-! ## The prescribed datum -/

/-- **The attachment-restricted branch scalar**: the branch scalar of the rule (4), set to `0` unless
the block `A` really lies in the `K`-class of the `ρ`-sibling of the `l`-th escape prime.  Written
with a product instead of nested `if`s so that it is a plain term (no proof binder), which is what
makes `attScalar_congr` and `prescDatum_congr` clean. -/
noncomputable def attScalar (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (l m : ℕ) (A : ValuationSubring Ω)
    (ρ : K ≃ₐ[k] K) : ZMod 2 := by
  classical
  exact eScalar (K := K) ζ hζ hζK f l m ρ *
    (if Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ (f l).1) A
      then 1 else 0)

/-- **The attachment-restricted branch scalar depends only on the entries of the history below the
stage index.** -/
theorem attScalar_congr {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {f g : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {l m : ℕ} (hlm : l < m)
    (h : ∀ i, i < m → f i = g i) (A : ValuationSubring Ω) (ρ : K ≃ₐ[k] K) :
    attScalar (K := K) ζ hζ hζK f l m A ρ = attScalar (K := K) ζ hζ hζK g l m A ρ := by
  classical
  rw [attScalar, attScalar, eScalar_congr (K := K) h ρ, h l hlm]

/-- **The prescribed local datum `h_m` for the class of stage `m`.**  At a block `A`:

* `0`, if `A` is a `k`-conjugate of an element of `S`;
* `-y + Σ_{l<m} Σ_ρ attScalar · χ_{b_l}`, where the scalar is the branch scalar of the rule (4) at
  the `ρ`-sibling of the `l`-th escape prime, set to `0` unless `A` lies in its `K`-class; the sum
  runs over the (finitely many) pairs `(l,ρ)` with `l < m`.

At a block whose attachment is unique (`TBlock`-blocks: `prescDatum_eq_of_attachment`) the sum
collapses to the single term `-y + e · χ_{b_l}`, so that the total datum realised by the oracle
there is `e · χ_{b_l}` (the branch `e = 1` prescribes the own value, `e = 0` prescribes `0`).

The datum is a `Finset.sum` — hence *choice-free*: this is what makes `prescDatum_congr` (its
invariance under a change of the history above the stage index) provable. -/
noncomputable def prescDatum (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ))
    (m : ℕ) (A : ValuationSubring Ω) : (Ω ≃ₐ[k] Ω) → ZMod 2 := by
  classical
  exact fun σ =>
    if ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A then 0
    else - y σ + ∑ p ∈ (Finset.range m).product (Finset.univ : Finset (K ≃ₐ[k] K)),
        attScalar (K := K) ζ hζ hζK f p.1 m A p.2 •
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f p.1).2 σ

/-- **The prescribed datum vanishes at the `S`-blocks.** -/
theorem prescDatum_eq_zero_of_isConjPlace {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {S : Finset (ValuationSubring Ω)} {y : (Ω ≃ₐ[k] Ω) → ZMod 2}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)}
    {m : ℕ} {A : ValuationSubring Ω} (h : ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A) :
    prescDatum (K := K) ζ hζ hζK S y f m A = fun _ => 0 := by
  classical
  funext σ
  simp only [prescDatum, if_pos h]

/-- **The prescribed datum at a block with a unique attachment.**  If `A` is not `k`-conjugate to
any element of `S`, and `(l, ρ)` is the unique pair with `l < m`, `ρ ≠ 1` and `A` in the `K`-class of
the `ρ`-sibling of the `l`-th escape prime, then `prescDatum` collapses to its `(l, ρ)`-term. -/
theorem prescDatum_eq_of_attachment {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {S : Finset (ValuationSubring Ω)} {y : (Ω ≃ₐ[k] Ω) → ZMod 2}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)}
    {m : ℕ} {A : ValuationSubring Ω}
    (hS : ¬ ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A)
    {l : ℕ} (hl : l < m) {ρ : K ≃ₐ[k] K}
    (hAtt : Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ (f l).1) A)
    (huniq : ∀ l' : ℕ, l' < m → ∀ ρ' : K ≃ₐ[k] K,
      Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ' (f l').1) A →
      l' = l ∧ ρ' = ρ) :
    prescDatum (K := K) ζ hζ hζK S y f m A
      = fun σ => - y σ + eScalar (K := K) ζ hζ hζK f l m ρ •
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f l).2 σ := by
  classical
  funext σ
  simp only [prescDatum]
  rw [if_neg hS]
  congr 1
  rw [Finset.sum_eq_single (l, ρ) ?_ ?_]
  · rw [attScalar, if_pos hAtt, mul_one]
  · rintro ⟨l', ρ'⟩ hp hne
    obtain ⟨hl', -⟩ := Finset.mem_product.mp hp
    by_cases hρ' : ρ' = 1
    · rw [attScalar, eScalar, dif_pos hρ', zero_mul, zero_smul]
    · have hnoatt : ¬ Work.SSGRoute.gesKConj K
          (Work.SSGRoute.ZDataMup.siblingPlace K ρ' (f l').1) A := by
        intro hc
        obtain ⟨hll, hrr⟩ := huniq l' (Finset.mem_range.mp hl') ρ' hc
        exact hne (by rw [hll, hrr])
      rw [attScalar, if_neg hnoatt, mul_zero, zero_smul]
  · intro hmem
    exact absurd (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hl, Finset.mem_univ ρ⟩) hmem

/-- **The pointwise form of `prescDatum_eq_of_attachment`.** -/
theorem prescDatum_apply_eq_of_attachment {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {S : Finset (ValuationSubring Ω)} {y : (Ω ≃ₐ[k] Ω) → ZMod 2}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)}
    {m : ℕ} {A : ValuationSubring Ω}
    (hS : ¬ ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A)
    {l : ℕ} (hl : l < m) {ρ : K ≃ₐ[k] K}
    (hAtt : Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ (f l).1) A)
    (huniq : ∀ l' : ℕ, l' < m → ∀ ρ' : K ≃ₐ[k] K,
      Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K ρ' (f l').1) A →
      l' = l ∧ ρ' = ρ) (σ : Ω ≃ₐ[k] Ω) :
    prescDatum (K := K) ζ hζ hζK S y f m A σ
      = - y σ + eScalar (K := K) ζ hζ hζK f l m ρ •
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f l).2 σ :=
  congrFun (prescDatum_eq_of_attachment (K := K) (A := A) (m := m) hS hl hAtt huniq) σ

/-- **The prescribed datum is additive on every local group.** -/
theorem prescDatum_add {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {S : Finset (ValuationSubring Ω)} {y : (Ω ≃ₐ[k] Ω) → ZMod 2}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)}
    (hy : ∀ x ∈ K.fixingSubgroup, ∀ z ∈ K.fixingSubgroup, y (x * z) = y x + y z)
    (m : ℕ) (A : ValuationSubring Ω) :
    ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ z ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        prescDatum (K := K) ζ hζ hζK S y f m A (x * z)
          = prescDatum (K := K) ζ hζ hζK S y f m A x
            + prescDatum (K := K) ζ hζ hζK S y f m A z := by
  classical
  intro x hx z hz
  have hxK : x ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hx).2
  have hzK : z ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hz).2
  by_cases hS : ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A
  · rw [prescDatum_eq_zero_of_isConjPlace (K := K) hS]
    simp only [Pi.zero_apply, zero_add]
  · simp only [prescDatum, if_neg hS]
    have hsum : ∀ p ∈ (Finset.range m).product (Finset.univ : Finset (K ≃ₐ[k] K)),
        attScalar (K := K) ζ hζ hζK f p.1 m A p.2 •
            Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f p.1).2 (x * z)
        = attScalar (K := K) ζ hζ hζK f p.1 m A p.2 •
            Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f p.1).2 x
          + attScalar (K := K) ζ hζ hζK f p.1 m A p.2 •
            Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f p.1).2 z := by
      rintro ⟨l, ρ⟩ _
      rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ (f l).2 x hxK z hzK,
        smul_add]
    have hy' : y (x * z) = y x + y z := hy x hxK z hzK
    rw [hy', Finset.sum_congr rfl (fun p hp => hsum p hp), Finset.sum_add_distrib]
    ring

/-- **The prescribed datum is locally constant on every local group.** -/
theorem prescDatum_locConst {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {S : Finset (ValuationSubring Ω)} {y : (Ω ≃ₐ[k] Ω) → ZMod 2}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)}
    (hy : ∀ x ∈ K.fixingSubgroup, ∀ z ∈ K.fixingSubgroup, y (x * z) = y x + y z)
    {hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y} (m : ℕ) (A : ValuationSubring Ω) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup →
        prescDatum (K := K) ζ hζ hζK S y f m A x = 0 := by
  classical
  have hy1 : y 1 = 0 := Work.SSGRoute.H9.swAdd_one_eq_zero hy
  by_cases hS : ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A
  · refine ⟨⊤, isOpen_univ, fun x _ _ => ?_⟩
    rw [prescDatum_eq_zero_of_isConjPlace (K := K) hS]
  · obtain ⟨U₀, hU₀o, hU₀⟩ := hyc
    let g : ℕ → Subgroup (Ω ≃ₐ[k] Ω) := fun l =>
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ (f l).2).choose
    have hgo : ∀ l : ℕ, IsOpen ((g l : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
      fun l => (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ (f l).2).choose_spec.1
    have hgval : ∀ l : ℕ, ∀ x ∈ g l,
        x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f l).2 x = 0 := by
      intro l x hx hxA
      have hxK : x ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hxA).2
      have h0 := (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ
        (f l).2).choose_spec.2 1 K.fixingSubgroup.one_mem x hx hxK
      rw [one_mul] at h0
      rw [h0, Work.SSGRoute.H9.swNodeKummerCocharZMod_one K ζ hζ hζK (f l).2]
    have hinf_o : IsOpen (((Finset.range m).inf g : Subgroup (Ω ≃ₐ[k] Ω)) :
        Set (Ω ≃ₐ[k] Ω)) := by
      classical
      induction Finset.range m using Finset.induction with
      | empty => rw [Finset.inf_empty, Subgroup.coe_top]; exact isOpen_univ
      | insert a s ha ih =>
        rw [Finset.inf_insert, Subgroup.coe_inf]
        exact (hgo a).inter ih
    refine ⟨U₀ ⊓ (Finset.range m).inf g, hU₀o.inter hinf_o, fun x hx hxA => ?_⟩
    have hxU₀ : x ∈ U₀ := (Subgroup.mem_inf.mp hx).1
    have hxinf : x ∈ (Finset.range m).inf g := (Subgroup.mem_inf.mp hx).2
    have hxK : x ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hxA).2
    have hyx : y x = 0 := by
      have h0 := hU₀ 1 K.fixingSubgroup.one_mem x hxU₀ hxK
      rw [one_mul] at h0
      rw [h0, hy1]
    simp only [prescDatum, if_neg hS, hyx, neg_zero, zero_add]
    refine Finset.sum_eq_zero (fun p hp => ?_)
    obtain ⟨hl, -⟩ := Finset.mem_product.mp hp
    rw [hgval p.1 x ((Finset.inf_le (f := g) hl) hxinf) hxA, smul_zero]

/-- **The prescribed datum depends only on the entries of the history below the stage index.** -/
theorem prescDatum_congr {ζ : Ω} {hζ : IsPrimitiveRoot ζ 2} {hζK : ζ ∈ K}
    {S : Finset (ValuationSubring Ω)} {y : (Ω ≃ₐ[k] Ω) → ZMod 2}
    {f g : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {m : ℕ}
    (h : ∀ i, i < m → f i = g i) :
    prescDatum (K := K) ζ hζ hζK S y f m = prescDatum (K := K) ζ hζ hζK S y g m := by
  classical
  funext A
  funext σ
  simp only [prescDatum]
  by_cases hc : ∃ A₀ ∈ S, SSGRoute.IsConjPlace k A₀ A
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]
    have hs : (∑ p ∈ (Finset.range m).product (Finset.univ : Finset (K ≃ₐ[k] K)),
          attScalar (K := K) ζ hζ hζK f p.1 m A p.2 •
            Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f p.1).2 σ)
        = (∑ p ∈ (Finset.range m).product (Finset.univ : Finset (K ≃ₐ[k] K)),
          attScalar (K := K) ζ hζ hζK g p.1 m A p.2 •
            Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (g p.1).2 σ) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      obtain ⟨hl, -⟩ := Finset.mem_product.mp hp
      rw [attScalar_congr (K := K) (Finset.mem_range.mp hl) h A p.2,
        h p.1 (Finset.mem_range.mp hl)]
    rw [hs]

/-! ## The place set of a stage -/

/-- **The place set `T_m`**: one `K`-class representative per `K`-class above the `k`-classes of `S`
and of the first `m` escape primes `Q_j = (f j).1`. -/
noncomputable def TBlock (S : Finset (ValuationSubring Ω))
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (m : ℕ) : Finset (ValuationSubring Ω) := by
  classical
  exact Work.SSGRoute.H9.krep K
    (Work.SSGRoute.ZDataMup.kleadReps K S ∪ (Finset.range m).biUnion
      (fun j => Work.SSGRoute.ZDataMup.kleadReps K {(f j).1}))

/-- **The place set of a stage is pairwise non-`K`-conjugate.** -/
theorem TBlock_disj {S : Finset (ValuationSubring Ω)} {m : ℕ}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)} :
    ∀ A ∈ TBlock S f m, ∀ B ∈ TBlock S f m,
      Work.SSGRoute.gesKConj K A B → A = B := by
  intro A hA B hB h
  rw [TBlock] at hA hB
  exact Work.SSGRoute.H9.krep_disj K _ A hA B hB h

/-- **The place set of a stage grows with the stage.** -/
theorem TBlock_mono {S : Finset (ValuationSubring Ω)}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {m m' : ℕ} (h : m ≤ m') :
    TBlock S f m ⊆ TBlock S f m' := by
  classical
  intro A hA
  rw [TBlock] at hA ⊢
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨A', hA', hA'q⟩ := Finset.mem_image.mp hq
  refine Finset.mem_image.mpr ⟨Quotient.mk (Work.SSGRoute.H9.gesKConjSetoid K) A',
    Finset.mem_image.mpr ⟨A', ?_, rfl⟩, congrArg Quotient.out hA'q⟩
  refine Finset.mem_union.mpr ?_
  rcases Finset.mem_union.mp hA' with h1 | h2
  · exact Or.inl h1
  · refine Or.inr ?_
    obtain ⟨j, hj, hjmem⟩ := Finset.mem_biUnion.mp h2
    exact Finset.mem_biUnion.mpr ⟨j,
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) h), hjmem⟩

/-- **The place set of a stage depends only on the entries of the history below the stage.** -/
theorem TBlock_congr {S : Finset (ValuationSubring Ω)}
    {f g : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {m : ℕ} (h : ∀ i, i < m → f i = g i) :
    TBlock S f m = TBlock S g m := by
  classical
  rw [TBlock, TBlock]
  congr 1
  rw [Finset.biUnion_congr rfl (fun j hj => by rw [h j (Finset.mem_range.mp hj)])]

/-- **The membership cases of `TBlock`**: an element of `TBlock S f m` is `K`-conjugate to a
`G(K|k)`-translate of an element of `S`, or of one of the escape primes `(f l).1` with `l < m`. -/
theorem TBlock_mem_cases {S : Finset (ValuationSubring Ω)}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {m : ℕ} {A : ValuationSubring Ω}
    (hA : A ∈ TBlock S f m) :
    (∃ A₀ ∈ S, ∃ ρ : K ≃ₐ[k] K, Work.SSGRoute.gesKConj K
        (Work.SSGRoute.ZDataMup.siblingPlace K ρ A₀) A) ∨
    (∃ l : ℕ, l < m ∧ ∃ ρ : K ≃ₐ[k] K, Work.SSGRoute.gesKConj K
        (Work.SSGRoute.ZDataMup.siblingPlace K ρ (f l).1) A) := by
  classical
  rw [TBlock] at hA
  obtain ⟨A'', hA'', hA''A⟩ := Work.SSGRoute.H9.krep_mem_classes K _ A hA
  rcases Finset.mem_union.mp hA'' with h1 | h2
  · obtain ⟨⟨B, ρ⟩, hBmem, hBeq⟩ := Finset.mem_image.mp h1
    obtain ⟨hB, -⟩ := Finset.mem_product.mp hBmem
    exact Or.inl ⟨B, hB, ρ, by
      rw [← hBeq] at hA''A
      exact Work.SSGRoute.H9.swGesKConj_symm hA''A⟩
  · obtain ⟨j, hj, hjmem⟩ := Finset.mem_biUnion.mp h2
    obtain ⟨⟨B, ρ⟩, hBmem, hBeq⟩ := Finset.mem_image.mp hjmem
    obtain ⟨hB, -⟩ := Finset.mem_product.mp hBmem
    have hBsingle : B = (f j).1 := by simpa using hB
    exact Or.inr ⟨j, Finset.mem_range.mp hj, ρ, by
      rw [← hBeq, hBsingle] at hA''A
      exact Work.SSGRoute.H9.swGesKConj_symm hA''A⟩

/-- **Every element of a stage's place set is finite**, provided the places of `S` and the escape
primes are. -/
theorem TBlock_isFinPlace {S : Finset (ValuationSubring Ω)}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {m : ℕ}
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hf : ∀ j < m, SSGRoute.IsFinPlace k (f j).1) :
    ∀ A ∈ TBlock S f m, SSGRoute.IsFinPlace k A := by
  classical
  intro A hA
  rcases TBlock_mem_cases (K := K) hA with ⟨A₀, hA₀, ρ, hconj⟩ | ⟨l, hlm, ρ, hconj⟩
  · obtain ⟨τ, -, hτA⟩ := hconj
    rw [← hτA]
    exact (SSGRoute.isFinPlace_smul_iff (Work.SSGRoute.ZDataMup.siblingPlace K ρ A₀) τ).mpr
      ((SSGRoute.isFinPlace_smul_iff A₀ (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr (hSfin A₀ hA₀))
  · obtain ⟨τ, -, hτA⟩ := hconj
    rw [← hτA]
    exact (SSGRoute.isFinPlace_smul_iff (Work.SSGRoute.ZDataMup.siblingPlace K ρ (f l).1) τ).mpr
      ((SSGRoute.isFinPlace_smul_iff (f l).1 (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr (hf l hlm))

/-- **One representative per `K`-class over the `k`-classes of `S`.** -/
theorem TBlock_covers_S {S : Finset (ValuationSubring Ω)} {m : ℕ}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {A B : ValuationSubring Ω} (hA : A ∈ S)
    (hAB : SSGRoute.IsConjPlace k A B) :
    ∃ A' ∈ TBlock S f m, Work.SSGRoute.gesKConj K A' B := by
  classical
  obtain ⟨A₁, hA₁, hA₁B⟩ := Work.SSGRoute.ZDataMup.kleadReps_covers K S hA hAB
  obtain ⟨A₂, hA₂, hA₂₁⟩ := Work.SSGRoute.H9.krep_covers K _ A₁ (Finset.mem_union_left _ hA₁)
  rw [TBlock]
  exact ⟨A₂, hA₂, Work.SSGRoute.H9.swGesKConj_trans hA₂₁ hA₁B⟩

/-- **One representative per `K`-class over the `k`-classes of the escape primes.** -/
theorem TBlock_covers_Q {S : Finset (ValuationSubring Ω)} {m : ℕ}
    {f : ℕ → (ValuationSubring Ω × (↥K)ˣ)} {j : ℕ} (hj : j < m) {B : ValuationSubring Ω}
    (hB : SSGRoute.IsConjPlace k (f j).1 B) :
    ∃ A' ∈ TBlock S f m, Work.SSGRoute.gesKConj K A' B := by
  classical
  obtain ⟨A₁, hA₁, hA₁B⟩ := Work.SSGRoute.ZDataMup.kleadReps_covers K {(f j).1}
    (Finset.mem_singleton_self _) hB
  have hmem : A₁ ∈ Work.SSGRoute.ZDataMup.kleadReps K S ∪ (Finset.range m).biUnion
      (fun j => Work.SSGRoute.ZDataMup.kleadReps K {(f j).1}) :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hA₁⟩)
  obtain ⟨A₂, hA₂, hA₂₁⟩ := Work.SSGRoute.H9.krep_covers K _ A₁ hmem
  rw [TBlock]
  exact ⟨A₂, hA₂, Work.SSGRoute.H9.swGesKConj_trans hA₂₁ hA₁B⟩

end Defs

end Work.SSGRoute.ZDataTwo.TwoRec
