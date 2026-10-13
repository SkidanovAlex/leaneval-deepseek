/-
  WilE9 / Sharp — helpers and the core of the `DomSet2_gen` assembly.

  `DomSet2 n k S (graphOf f)` is the interior of the set on which the `Eset`-family has
  continuous (and, for `|L| < k`, differentiable) sections with the derivative attained at the
  next order.  It is built out of

  * `contPart (graphOf f)` (the continuity locus of a `Gen`-graph, `Gen.gen_contSet`),
  * `Eset n S (repL μ)` (the `Gen`-set of the Eset-family, supplied here as `hEset`),
  * `contPart (Eset n S (repL μ))` and `diffPart (Eset n S (repL μ)) i`
    (`Gen.gen_contSet` / `Gen.gen_diffSet`), and
  * `interior` (`Gen.gen_interior`),

  each of which costs a *constant* format and a *polynomial* degree.  The index `μ` runs over
  the `binom(n+k,n)` multi-indices `Ord2 n k`; the per-`μ` degree can be taken to be the *same*
  for every `μ` (the `Eset`-bound is stated with the order bound `k`), so the total degree is at
  most `(k+1)^n` times it, which is again polynomial in `k`.

  This file contains `DomSet2_gen_core`, which takes the `Eset`-bound (`hEset`, the content of
  `Eset_gen` with the order bound written as `k`) as a hypothesis; the wrapper `DomSet2_gen`
  instantiates it.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Main2
import Submission.Work.WilE9.Gen.gen_interior
import Submission.Work.WilE9.Gen.gen_contSet
import Submission.Work.WilE9.Gen.gen_diffSet
import Submission.Work.WilE9.Gen.gen_closure

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-! ## Small polynomial tools -/

/-- Substituting a multivariate polynomial into a univariate polynomial with nonnegative
integer coefficients commutes with evaluation. -/
theorem eval_eval₂_C' {σ : Type*} (v : σ → ℕ) (d : MvPolynomial σ ℕ) (p : Polynomial ℕ) :
    MvPolynomial.eval v (Polynomial.eval₂ MvPolynomial.C d p) = p.eval (MvPolynomial.eval v d) := by
  rw [Polynomial.hom_eval₂]
  have h : (MvPolynomial.eval v).comp MvPolynomial.C = RingHom.id ℕ := by
    ext n; simp
  rw [h, Polynomial.eval₂_id]

/-- Evaluation of a polynomial with nonnegative integer coefficients is monotone on `ℕ`. -/
theorem poly_eval_le'' {p : Polynomial ℕ} {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-! ## Type class instances for `Ord2`

`Ord2` is an opaque `def`, so the instances of its underlying subtype are not found by
instance search; we register them explicitly. -/

instance ord2Fintype (n k : ℕ) : Fintype (Ord2 n k) := by
  unfold Ord2; infer_instance

instance ord2DecidableEq (n k : ℕ) : DecidableEq (Ord2 n k) := by
  unfold Ord2; infer_instance

end Work.WilE9.Sharp

/-! ## `Gen` is closed under `Fintype`-indexed intersections -/

namespace Work.WilE9.Gen

/-- `Gen` is closed under finite intersections indexed by a `Fintype`; one format, degrees
adding up. -/
theorem iInter {F n : ℕ} {ι : Type*} [Fintype ι] (D : ι → ℕ) (A : ι → Set (Fin n → ℝ))
    (h : ∀ i, WilkiesDesign.E.Gen F (D i) n (A i)) :
    WilkiesDesign.E.Gen (F + 1) (∑ i, D i) n (⋂ i, A i) := by
  classical
  set e := Fintype.equivFin ι with he
  have h' : WilkiesDesign.E.Gen (F + 1) (∑ i : Fin (Fintype.card ι), D (e.symm i)) n
      (⋂ i : Fin (Fintype.card ι), A (e.symm i)) :=
    WilkiesDesign.E.Gen.inter (fun i => D (e.symm i)) (fun i => A (e.symm i)) (fun i => h _)
  have hsum : (∑ i : Fin (Fintype.card ι), D (e.symm i)) = ∑ i : ι, D i :=
    Equiv.sum_comp e.symm D
  have hset : (⋂ i : Fin (Fintype.card ι), A (e.symm i)) = ⋂ i : ι, A i := by
    ext z
    simp only [Set.mem_iInter]
    constructor
    · intro hz i; simpa using hz (e i)
    · intro hz i; exact hz (e.symm i)
  rw [hsum, hset] at h'
  exact h'

end Work.WilE9.Gen

namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-! ## The multi-index list `repL` -/

/-- The length of `repL μ` is the sum of the coordinates of `μ`. -/
theorem repL_length {n k : ℕ} (μ : Ord2 n k) : (repL μ).length = ∑ i : Fin n, (μ.1 i : ℕ) := by
  rw [repL, List.length_flatMap]
  simp only [List.length_replicate]
  rw [← List.sum_toFinset _ (List.nodup_finRange n)]
  congr 1
  ext i; simp

/-- The order represented by a multi-index is at most `k`. -/
theorem repL_length_le {n k : ℕ} (μ : Ord2 n k) : (repL μ).length ≤ k := by
  rw [repL_length]; exact μ.2

/-- There are at most `(k+1)^n` multi-indices of order at most `k`. -/
theorem ord2_card_le (n k : ℕ) : Fintype.card (Ord2 n k) ≤ (k + 1) ^ n := by
  have h1 : Fintype.card (Ord2 n k) ≤ Fintype.card (Fin n → Fin (k + 1)) :=
    Fintype.card_le_of_injective (fun μ : Ord2 n k => (μ.1 : Fin n → Fin (k + 1)))
      Subtype.coe_injective
  rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  simpa using h1

/-! ## The degree polynomial of the assembly -/

/-- **The degree budget polynomial of the `DomSet2` assembly**, in the variables
`(D₁, D, k, a₀)`:

* `PE` is the `Eset`-degree bound `bE` with its order variable read as `k`;
* `Pc` (resp. `Pd`) is the degree bound of `contPart` (resp. `diffPart`) applied to `PE`;
* `B1 = PE + Pc + n * (Pd + PE)` is the per-multi-index degree;
* `(X 2 + 1)^n * B1` accounts for the `≤ (k+1)^n` multi-indices;
* `PD1` is the degree bound of `contPart (graphOf f)`;
* `bi` is the degree budget of `interior`. -/
def DomSet2Budget (n : ℕ) (bcG bcE bD : Polynomial ℕ) (bE : MvPolynomial (Fin 3) ℕ)
    (bi : Polynomial ℕ) : MvPolynomial (Fin 4) ℕ :=
  let PE : MvPolynomial (Fin 4) ℕ := MvPolynomial.rename (Fin.succ : Fin 3 → Fin 4) bE
  let Pc : MvPolynomial (Fin 4) ℕ := Polynomial.eval₂ MvPolynomial.C PE bcE
  let Pd : MvPolynomial (Fin 4) ℕ := Polynomial.eval₂ MvPolynomial.C PE bD
  let B1 : MvPolynomial (Fin 4) ℕ := PE + Pc + MvPolynomial.C n * (Pd + PE)
  let PD1 : MvPolynomial (Fin 4) ℕ :=
    Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (0 : Fin 4)) bcG
  let Btot : MvPolynomial (Fin 4) ℕ :=
    PD1 + (MvPolynomial.X (2 : Fin 4) + MvPolynomial.C 1) ^ n * B1
  Polynomial.eval₂ MvPolynomial.C Btot bi

/-- Evaluation of `DomSet2Budget` at `(D₁, D, k, a₀)`. -/
theorem DomSet2Budget_eval (n D₁ D k a₀ : ℕ) (bcG bcE bD bi : Polynomial ℕ)
    (bE : MvPolynomial (Fin 3) ℕ) :
    MvPolynomial.eval ![D₁, D, k, a₀] (DomSet2Budget n bcG bcE bD bE bi) =
      bi.eval (bcG.eval D₁ + (k + 1) ^ n *
        (MvPolynomial.eval ![D, k, a₀] bE + bcE.eval (MvPolynomial.eval ![D, k, a₀] bE)
          + n * (bD.eval (MvPolynomial.eval ![D, k, a₀] bE)
              + MvPolynomial.eval ![D, k, a₀] bE))) := by
  have hcomp : (![D₁, D, k, a₀] ∘ Fin.succ) = (![D, k, a₀] : Fin 3 → ℕ) := by
    funext i; fin_cases i <;> rfl
  simp only [DomSet2Budget, eval_eval₂_C', MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_pow, MvPolynomial.eval_X, MvPolynomial.eval_rename,
    hcomp]
  simp

/-! ## The core assembly -/

/-- **The `Gen`-bound for `DomSet2`.**  Given the `Gen`-bound for the `Eset`-family with the
order bound written as `k` (this is the content of `Eset_gen`, whose proof consumes the degree
bound of the extended system), the domain set `DomSet2 n k S (graphOf f)` of the E9 construction
is `Gen` with a constant format and a degree polynomial in `(D₁, D, k, a₀)`. -/
theorem DomSet2_gen_core (n a₀ : ℕ) (aE : ℕ) (bE : MvPolynomial (Fin 3) ℕ)
    (hEset : ∀ (k : ℕ) (S : List (AEStratum n)) (L : List (Fin n)) (D : ℕ),
        L.length ≤ k → S.length ≤ D + 1 →
        (∀ A ∈ S, A.E.X.fmt ≤ a₀) → (∀ A ∈ S, A.E.deg ≤ D) →
        (∀ A ∈ S, A.E.X.basics.length ≤ D + 1) →
        WilkiesDesign.E.Gen aE (MvPolynomial.eval ![D, k, a₀] bE) (n + 1) (Eset n S L)) :
    ∀ F₁ : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 4) ℕ),
    ∀ (D₁ k : ℕ) (f : (Fin n → ℝ) → ℝ)
      (S : List (AEStratum n)) (D : ℕ),
      WilkiesDesign.E.Gen F₁ D₁ (n + 1) (WilkiesDesign.graphOf f) →
      S.length ≤ D + 1 →
      (∀ A ∈ S, A.E.X.fmt ≤ a₀) →
      (∀ A ∈ S, A.E.deg ≤ D) → (∀ A ∈ S, A.E.X.basics.length ≤ D + 1) →
      WilkiesDesign.E.Gen a (MvPolynomial.eval ![D₁, D, k, a₀] b) n
        (DomSet2 n k S (WilkiesDesign.graphOf f)) := by
  intro F₁
  -- the three `Gen`-tools, at the formats of `graphOf f` and of the `Eset`-family
  obtain ⟨acG, bcG, hcontG⟩ := Work.WilE9.Gen.gen_contSet F₁ n
  obtain ⟨acE, bcE, hcontE⟩ := Work.WilE9.Gen.gen_contSet aE n
  obtain ⟨aD, bD, hdiff⟩ := Work.WilE9.Gen.gen_diffSet aE n
  set F2 : ℕ := max (max (aE + 1) (acE + 1) + 1) (max aD aE + 2 + 1) + 1 with hF2
  set Finner : ℕ := max (acG + 1) (F2 + 1) + 1 with hFinner
  obtain ⟨ai, bi, hint⟩ := Work.WilE9.Gen.gen_interior Finner n
  refine ⟨ai, DomSet2Budget n bcG bcE bD bE bi, ?_⟩
  intro D₁ k f S D hgr hSlen hfmtS hdegS hlenS
  set ev : ℕ := MvPolynomial.eval ![D, k, a₀] bE with hev_def
  -- the `Eset`-bound, at the uniform order bound `k`
  have hEs : ∀ L : List (Fin n), L.length ≤ k → WilkiesDesign.E.Gen aE ev (n + 1) (Eset n S L) := by
    intro L hL
    rw [hev_def]
    exact hEset k S L D hL hSlen hfmtS hdegS hlenS
  -- the `contPart` of the graph of `f`
  have hG0 : WilkiesDesign.E.Gen (acG + 1) (bcG.eval D₁) n
      (WilkiesDesign.projLast (contPart (WilkiesDesign.graphOf f))) :=
    WilkiesDesign.E.Gen.proj (hcontG D₁ (WilkiesDesign.graphOf f) hgr)
  -- the per-multi-index part
  have hper : ∀ μ : Ord2 n k, WilkiesDesign.E.Gen F2
      (ev + bcE.eval ev + (if (repL μ).length < k then ∑ _i : Fin n, (bD.eval ev + ev) else 0)) n
      (WilkiesDesign.projLast (Eset n S (repL μ)) ∩
        WilkiesDesign.projLast (contPart (Eset n S (repL μ))) ∩
        (if (repL μ).length < k then
          ⋂ i : Fin n, WilkiesDesign.projLast
            (diffPart (Eset n S (repL μ)) i ∩ Eset n S (i :: repL μ))
         else Set.univ)) := by
    intro μ
    have hA : WilkiesDesign.E.Gen (aE + 1) ev n
        (WilkiesDesign.projLast (Eset n S (repL μ))) :=
      WilkiesDesign.E.Gen.proj (hEs (repL μ) (repL_length_le μ))
    have hB : WilkiesDesign.E.Gen (acE + 1) (bcE.eval ev) n
        (WilkiesDesign.projLast (contPart (Eset n S (repL μ)))) :=
      WilkiesDesign.E.Gen.proj (hcontE ev (Eset n S (repL μ)) (hEs (repL μ) (repL_length_le μ)))
    have hAB : WilkiesDesign.E.Gen (max (aE + 1) (acE + 1) + 1) (ev + bcE.eval ev) n
        (WilkiesDesign.projLast (Eset n S (repL μ)) ∩
          WilkiesDesign.projLast (contPart (Eset n S (repL μ)))) :=
      Work.WilE9.Gen.inter₂ hA hB
    by_cases hlen : (repL μ).length < k
    · have h3 : WilkiesDesign.E.Gen (max aD aE + 2 + 1) (∑ _i : Fin n, (bD.eval ev + ev)) n
          (⋂ i : Fin n, WilkiesDesign.projLast
            (diffPart (Eset n S (repL μ)) i ∩ Eset n S (i :: repL μ))) := by
        refine WilkiesDesign.E.Gen.inter (fun _ : Fin n => bD.eval ev + ev)
          (fun i => WilkiesDesign.projLast
            (diffPart (Eset n S (repL μ)) i ∩ Eset n S (i :: repL μ))) (fun i => ?_)
        have hDi : WilkiesDesign.E.Gen aD (bD.eval ev) (n + 1)
            (diffPart (Eset n S (repL μ)) i) :=
          hdiff ev (Eset n S (repL μ)) i (hEs (repL μ) (repL_length_le μ))
        have hlen' : (i :: repL μ).length ≤ k := by
          rw [List.length_cons]; omega
        have hEi : WilkiesDesign.E.Gen aE ev (n + 1) (Eset n S (i :: repL μ)) :=
          hEs (i :: repL μ) hlen'
        exact WilkiesDesign.E.Gen.proj
          (Work.WilE9.Gen.inter₂ hDi hEi)
      have hthis := Work.WilE9.Gen.inter₂ hAB h3
      simp only [if_pos hlen, hF2]
      exact hthis
    · have h3 : WilkiesDesign.E.Gen (max aD aE + 2 + 1) 0 n
          (Set.univ : Set (Fin n → ℝ)) := Work.WilE9.Gen.univ (max aD aE + 2) n
      have hthis := Work.WilE9.Gen.inter₂ hAB h3
      simp only [if_neg hlen, hF2]
      exact hthis
  -- the intersection over the multi-indices
  have hμ : WilkiesDesign.E.Gen (F2 + 1)
      (∑ μ : Ord2 n k,
        (ev + bcE.eval ev + (if (repL μ).length < k then ∑ _i : Fin n, (bD.eval ev + ev) else 0)))
      n (⋂ μ : Ord2 n k, WilkiesDesign.projLast (Eset n S (repL μ)) ∩
        WilkiesDesign.projLast (contPart (Eset n S (repL μ))) ∩
        (if (repL μ).length < k then
          ⋂ i : Fin n, WilkiesDesign.projLast
            (diffPart (Eset n S (repL μ)) i ∩ Eset n S (i :: repL μ))
         else Set.univ)) :=
    Work.WilE9.Gen.iInter (fun μ : Ord2 n k =>
        (ev + bcE.eval ev + (if (repL μ).length < k then ∑ _i : Fin n, (bD.eval ev + ev) else 0)))
      (fun μ : Ord2 n k => WilkiesDesign.projLast (Eset n S (repL μ)) ∩
        WilkiesDesign.projLast (contPart (Eset n S (repL μ))) ∩
        (if (repL μ).length < k then
          ⋂ i : Fin n, WilkiesDesign.projLast
            (diffPart (Eset n S (repL μ)) i ∩ Eset n S (i :: repL μ))
         else Set.univ)) hper
  have hcomb := Work.WilE9.Gen.inter₂ hG0 hμ
  have hres := hint (bcG.eval D₁ + ∑ μ : Ord2 n k,
        (ev + bcE.eval ev + (if (repL μ).length < k then ∑ _i : Fin n, (bD.eval ev + ev) else 0)))
      (WilkiesDesign.projLast (contPart (WilkiesDesign.graphOf f)) ∩
        ⋂ μ : Ord2 n k, WilkiesDesign.projLast (Eset n S (repL μ)) ∩
          WilkiesDesign.projLast (contPart (Eset n S (repL μ))) ∩
          (if (repL μ).length < k then
            ⋂ i : Fin n, WilkiesDesign.projLast
              (diffPart (Eset n S (repL μ)) i ∩ Eset n S (i :: repL μ))
           else Set.univ))
      (by rw [hFinner]; exact hcomb)
  -- the degree bookkeeping
  have hdeg_le : ∀ μ : Ord2 n k,
      ev + bcE.eval ev + (if (repL μ).length < k then ∑ _i : Fin n, (bD.eval ev + ev) else 0)
        ≤ ev + bcE.eval ev + n * (bD.eval ev + ev) := by
    intro μ
    by_cases hlen : (repL μ).length < k
    · rw [if_pos hlen]
      have hsum : (∑ _i : Fin n, (bD.eval ev + ev)) = n * (bD.eval ev + ev) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp
      rw [hsum]
    · rw [if_neg hlen]; omega
  have hsum_le : (∑ μ : Ord2 n k,
        (ev + bcE.eval ev + (if (repL μ).length < k then ∑ _i : Fin n, (bD.eval ev + ev) else 0)))
      ≤ Fintype.card (Ord2 n k) * (ev + bcE.eval ev + n * (bD.eval ev + ev)) := by
    calc (∑ μ : Ord2 n k,
          (ev + bcE.eval ev + (if (repL μ).length < k then ∑ _i : Fin n, (bD.eval ev + ev) else 0)))
        ≤ (Finset.univ : Finset (Ord2 n k)).card
            • (ev + bcE.eval ev + n * (bD.eval ev + ev)) :=
          Finset.sum_le_card_nsmul Finset.univ _ _ (fun μ _ => hdeg_le μ)
      _ = Fintype.card (Ord2 n k) * (ev + bcE.eval ev + n * (bD.eval ev + ev)) := by
          rw [Finset.card_univ, nsmul_eq_mul]
          simp
  have hfinal : bi.eval (bcG.eval D₁ + ∑ μ : Ord2 n k,
        (ev + bcE.eval ev + (if (repL μ).length < k then ∑ _i : Fin n, (bD.eval ev + ev) else 0)))
      ≤ MvPolynomial.eval ![D₁, D, k, a₀] (DomSet2Budget n bcG bcE bD bE bi) := by
    rw [DomSet2Budget_eval, hev_def]
    apply poly_eval_le''
    apply Nat.add_le_add_left
    calc (∑ μ : Ord2 n k,
          (ev + bcE.eval ev + (if (repL μ).length < k then ∑ _i : Fin n, (bD.eval ev + ev) else 0)))
        ≤ Fintype.card (Ord2 n k) * (ev + bcE.eval ev + n * (bD.eval ev + ev)) := hsum_le
      _ ≤ (k + 1) ^ n * (ev + bcE.eval ev + n * (bD.eval ev + ev)) :=
          Nat.mul_le_mul_right _ (ord2_card_le n k)
  exact Work.WilE9.Gen.monoD hfinal hres

end Work.WilE9.Sharp
