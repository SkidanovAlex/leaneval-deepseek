/-
  WilC5 — **value containment for a definable closure** (vdDMM (3.9), divisibility form).

  Wilkie's valuation inequality (`WilkiesDesign.CG.ValIneq`, the frozen `hVI`) says that at most
  `k` values of elements of `dcl(S ∪ {a₁,…,a_k})` can be `ℤ`-independent modulo the value group
  `Γ S = {ν c : c ∈ S, c ≠ 0}` of an elementary substructure `S`.

  The present lemma extracts the "containment" half of vdDMM (3.9) that the Ressayre/vdDMM
  Lemma 4.2–4.4 bookkeeping consumes: if `b ∈ dcl(S ∪ {a₁,…,a_k})` and the values of the
  generators `a` are `ℤ`-independent modulo `Γ S` (`hind`), then the value of `b` lies in the
  divisible hull of `Γ S` and the `ℚ`-span of the values of the generators.  Concretely there
  are `q : Fin k → ℤ`, `n ≠ 0` and `c ∈ S \ {0}` with
  `c · b ^ n · ∏ᵢ aᵢ ^ (qᵢ)` a unit — i.e. `v(b) = -v(c)/n - Σᵢ (qᵢ/n) v(aᵢ) ∈ divhull(Γ S +
  ℚ·span{v(aᵢ)})`.

  ## Proof

  * If all the generators are nonzero, apply `hVI` with the `k` generators `a` and the `k+1`
    elements `(b, a₀, …, a_{k-1})` (a `Fin (k+1) → M` family `Fin.cons b a`).  All of them are
    nonzero and definable from `S ∪ range a`, so `ValIndep S (Fin.cons b a)` would force
    `k + 1 ≤ k` — a contradiction.  Hence a nontrivial integer relation
    `c · b ^ (q 0) · ∏ᵢ aᵢ ^ (q (i+1))` is a unit.  Its coefficient `q 0` on `b` must be nonzero:
    otherwise the relation only involves the generators and then `hind` would force `q = 0`.

  * If some generator `a i₀` vanishes, that generator contributes nothing to the value span (and
    `0 ∈ S`), so delete it: the family `a' = a ∘ i₀.succAbove` has the same value span, the
    hypothesis `hind` restricts to `a'` (pad the exponent vector by `0` at `i₀`), and a relation
    for `a'` lifts back to `a` by inserting `0` at `i₀` (`Fin.insertNth`).  This induction on
    `k` terminates at `k = 0`, which is the "all nonzero" case.
-/
import Mathlib
import Submission.Work.WilC5.valIneq_span
import Submission.Work.WilC5.ValuesLemmas
import Submission.Work.WilC5.model_pow_root
import Submission.Work.WilC5.elemSub_pow_root
import Submission.Work.WilC5.Values

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC5

section Helpers

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]

/-- The singleton `{x}` is definable from a set of parameters containing `x`, in the
`Fin 1`-tuple formulation used by `DefinableElt`. -/
private theorem singleton_definable {A : Set M} {x : M} (hx : x ∈ A) :
    A.Definable LRc {fun _ : Fin 1 => x} := by
  have h1 : A.Definable₁ LRc ({x} : Set M) := Set.Definable.singleton_of_mem LRc hx
  rw [Set.Definable₁] at h1
  have hs : ({v : Fin 1 → M | v 0 ∈ ({x} : Set M)}) = {fun _ : Fin 1 => x} := by
    ext v; simp [funext_iff]
  rwa [hs] at h1

section ZeroMem

set_option backward.isDefEq.respectTransparency false

/-- `0` lies in every `LRc`-substructure: it is the interpretation of the constant symbol `0`
of the ring part of `LRc`. -/
private theorem zero_mem_substructure (S : LRc.Substructure M) : (0 : M) ∈ (S : Set M) := by
  have h := S.fun_mem (f := (Sum.inl (Sum.inl Ring.zeroFunc) : LRc.Functions 0))
      (x := fun i : Fin 0 => i.elim0) (by intro i; exact i.elim0)
  simpa using h

end ZeroMem

/-- Inserting `0` at the index `i₀` of an exponent vector leaves the monomial over `f` unchanged,
reindexed along `Fin.succAbove i₀`. -/
private theorem prod_insertNth_zero {k : ℕ} (f : Fin (k+1) → M) (i0 : Fin (k+1)) (q : Fin k → ℤ) :
    ∏ i : Fin (k+1), f i ^ (Fin.insertNth (α := fun _ : Fin (k+1) => ℤ) i0 (0:ℤ) q i)
      = ∏ j : Fin k, f (i0.succAbove j) ^ q j := by
  rw [Fin.prod_univ_succAbove
        (fun i => f i ^ (Fin.insertNth (α := fun _ : Fin (k+1) => ℤ) i0 (0:ℤ) q i)) i0,
      Fin.insertNth_apply_same, zpow_zero, one_mul]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Fin.insertNth_apply_succAbove]

/-- The "all generators nonzero" case of the value containment: apply `hVI` to the `k`
generators `a` and the `k+1` elements `(b, a₀, …, a_{k-1})`. -/
private theorem hVI_relation (S : LRc.ElementarySubstructure M) (hVI : ValIneq) {k : ℕ}
    (a : Fin k → M) (ha : ∀ i, a i ≠ 0) {b : M} (hb : b ≠ 0)
    (hbdef : ((S : Set M) ∪ Set.range a).Definable LRc {fun _ : Fin 1 => b})
    (hind : ∀ q : Fin k → ℤ, (∃ c ∈ (S : Set M), c ≠ 0 ∧
      IsUnitVal (c * ∏ i, a i ^ q i)) → q = 0) :
    ∃ (q : Fin k → ℤ) (n : ℤ), n ≠ 0 ∧ ∃ c ∈ (S : Set M), c ≠ 0 ∧
      IsUnitVal (c * b ^ n * ∏ i, a i ^ q i) := by
  set bv : Fin (k+1) → M := Fin.cons b a with hbv
  -- all the elements `(b, a₀, …, a_{k-1})` are nonzero
  have hb0 : ∀ j, bv j ≠ 0 := by
    intro j
    refine Fin.cases ?_ ?_ j
    · simp only [hbv, Fin.cons_zero]; exact hb
    · intro i
      simp only [hbv, Fin.cons_succ]; exact ha i
  -- and each of them is definable from `S ∪ range a`
  have hbdef' : ∀ j, ((S : Set M) ∪ Set.range a).Definable LRc {fun _ : Fin 1 => bv j} := by
    intro j
    refine Fin.cases ?_ ?_ j
    · simp only [hbv, Fin.cons_zero]; exact hbdef
    · intro i
      have hmem : a i ∈ (S : Set M) ∪ Set.range a := Set.mem_union_right _ (Set.mem_range_self i)
      have := singleton_definable (M := M) hmem
      simpa only [hbv, Fin.cons_succ] using this
  -- their values cannot be `ℤ`-independent modulo `Γ S`
  have hnotind : ¬ Work.WilC4.ValIndep (S : Set M) bv := by
    intro hind_bv
    have h2 := hVI M S a bv hb0 hbdef' hind_bv
    omega
  rw [Work.WilC4.ValIndep] at hnotind
  obtain ⟨q, hP⟩ := not_forall.mp hnotind
  obtain ⟨hPq, hqne⟩ := not_imp.mp hP
  obtain ⟨c, hcS, hc0, hunit⟩ := hPq
  rw [Work.WilC4.zmono] at hunit
  let q' : Fin k → ℤ := fun i => q i.succ
  -- split off the `b`-coordinate of the relation
  have hprod : ∏ j : Fin (k+1), bv j ^ q j = b ^ (q 0) * ∏ i : Fin k, a i ^ q' i := by
    rw [Fin.prod_univ_succAbove (fun j => bv j ^ q j) 0, Fin.succAbove_zero]
    simp only [hbv, Fin.cons_zero, Fin.cons_succ]
    rfl
  -- the coefficient of `b` in the relation is nonzero
  have hq0 : q 0 ≠ 0 := by
    intro h0
    rw [hprod, h0, zpow_zero, one_mul] at hunit
    have hrel : ∃ c ∈ (S : Set M), c ≠ 0 ∧ IsUnitVal (c * ∏ i, a i ^ q' i) :=
      ⟨c, hcS, hc0, hunit⟩
    have hq'0 := hind q' hrel
    apply hqne
    funext j
    refine Fin.cases h0 ?_ j
    intro i
    exact congrFun hq'0 i
  refine ⟨q', q 0, hq0, c, hcS, hc0, ?_⟩
  rw [hprod] at hunit
  rw [← mul_assoc] at hunit
  exact hunit

/-- Value containment for a definable closure, by induction on the number of generators: in the
"all nonzero" case use `hVI_relation`; otherwise delete a vanishing generator. -/
private theorem span_aux (S : LRc.ElementarySubstructure M) (hVI : ValIneq) :
    ∀ (k : ℕ) (a : Fin k → M) (b : M), b ≠ 0 →
      ((S : Set M) ∪ Set.range a).Definable LRc {fun _ : Fin 1 => b} →
      (∀ q : Fin k → ℤ, (∃ c ∈ (S : Set M), c ≠ 0 ∧ IsUnitVal (c * ∏ i, a i ^ q i)) → q = 0) →
      ∃ (q : Fin k → ℤ) (n : ℤ), n ≠ 0 ∧ ∃ c ∈ (S : Set M), c ≠ 0 ∧
        IsUnitVal (c * b ^ n * ∏ i, a i ^ q i) := by
  intro k
  induction k with
  | zero =>
    intro a b hb hbdef hind
    exact hVI_relation S hVI a (fun i => i.elim0) hb hbdef hind
  | succ k ih =>
    intro a b hb hbdef hind
    by_cases hall : ∀ i, a i ≠ 0
    · exact hVI_relation S hVI a hall hb hbdef hind
    · -- some generator vanishes: delete its index and induct
      simp only [not_forall, not_not] at hall
      obtain ⟨i0, hi0⟩ := hall
      let a' : Fin k → M := fun j => a (i0.succAbove j)
      have hzero : (0 : M) ∈ (S : Set M) := zero_mem_substructure (S : LRc.Substructure M)
      -- `range a ⊆ S ∪ range a'`
      have hrange : Set.range a ⊆ (S : Set M) ∪ Set.range a' := by
        rintro x ⟨i, rfl⟩
        rcases eq_or_ne i i0 with h | h
        · left; rw [h, hi0]; exact hzero
        · right
          obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq h
          exact ⟨j, by show a (i0.succAbove j) = a i; rw [hj]⟩
      have hbdef' : ((S : Set M) ∪ Set.range a').Definable LRc {fun _ : Fin 1 => b} :=
        Set.Definable.mono hbdef (Set.union_subset Set.subset_union_left hrange)
      -- `hind` restricts to the smaller family `a'`
      have hind' : ∀ q' : Fin k → ℤ, (∃ c ∈ (S : Set M), c ≠ 0 ∧
          IsUnitVal (c * ∏ j, a' j ^ q' j)) → q' = 0 := by
        intro q' hq'
        obtain ⟨c, hcS, hc0, hunit⟩ := hq'
        have hprod := prod_insertNth_zero (M := M) (f := a) i0 q'
        have hrel : ∃ c ∈ (S : Set M), c ≠ 0 ∧ IsUnitVal (c * ∏ i : Fin (k+1),
            a i ^ (Fin.insertNth (α := fun _ : Fin (k+1) => ℤ) i0 (0:ℤ) q' i)) :=
          ⟨c, hcS, hc0, by rw [hprod]; exact hunit⟩
        have hq0 := hind (Fin.insertNth (α := fun _ : Fin (k+1) => ℤ) i0 (0:ℤ) q') hrel
        funext j
        have hh := congrFun hq0 (i0.succAbove j)
        simpa only [Fin.insertNth_apply_succAbove, Pi.zero_apply] using hh
      obtain ⟨q', n, hn, c, hcS, hc0, hunit⟩ := ih a' b hb hbdef' hind'
      -- lift the relation for `a'` back to `a` by inserting `0` at `i₀`
      refine ⟨Fin.insertNth (α := fun _ : Fin (k+1) => ℤ) i0 (0:ℤ) q', n, hn, c, hcS, hc0, ?_⟩
      have hprod := prod_insertNth_zero (M := M) (f := a) i0 q'
      rw [hprod]; exact hunit

end Helpers

theorem SpanValueContain {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]
    (hVI : WilkiesDesign.CG.ValIneq) (S : WilkiesDesign.CG.LRc.ElementarySubstructure M)
    {k : ℕ} (a : Fin k → M) {b : M} (hb : b ≠ 0)
    (hbdef : ((S : Set M) ∪ Set.range a).Definable WilkiesDesign.CG.LRc {fun _ : Fin 1 => b})
    (hind : ∀ q : Fin k → ℤ, (∃ c ∈ (S : Set M), c ≠ 0 ∧
      WilkiesDesign.CG.IsUnitVal (c * ∏ i, a i ^ (q i))) → q = 0) :
    ∃ (q : Fin k → ℤ) (n : ℤ), n ≠ 0 ∧ ∃ c ∈ (S : Set M), c ≠ 0 ∧
      WilkiesDesign.CG.IsUnitVal (c * b ^ n * ∏ i, a i ^ (q i)) := by
  exact span_aux S hVI k a b hb hbdef hind

end Work.WilC5
