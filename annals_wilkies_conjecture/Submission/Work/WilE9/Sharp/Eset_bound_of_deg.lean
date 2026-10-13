/-
  WilE9 / Sharp — `Eset_bound_of_deg`.

  The family

      `Eset n S L = closure (psiV ⁻¹' Tset n S L)`,   `Tset n S L = ⋃ E ∈ S, exTset E.2 L`

  of `Sharp/Main.lean` is *generated* by the frozen inductive `Gen`, at a constant format and
  with a degree that is a polynomial in `(D, k, a₀)` — uniformly in the list `S` of strata, in
  the order `L`, and in an arbitrary upper bound `k` for the order `L.length`.

  This is `Sharp/Eset_gen.lean` with `L.length` replaced by `k`.  The three-step `Gen`-calculation
  (BNZ §3) is reproduced here, with two differences:

  * the degree bound for the extended system is *not* obtained from a lemma: it is the hypothesis
    `hdeg`, which is exactly the conclusion of `Sharp/exSemiPf_deg_le` — the one remaining degree
    computation of the E9 layer.  This keeps the proof independent of that computation;
  * the passage from the order `L.length` to the bound `k ≥ L.length` is monotonicity of
    `MvPolynomial.eval` on polynomials with nonnegative integer coefficients (`eval_mono`),
    combined with degree monotonicity of `Gen` (`Gen.monoD`).  Note that `Eset n S L` does not
    depend on `k` at all, so enlarging the degree budget is the only thing to do.

  Two further results are proved in this file, so that the assembly does not have to depend on
  the hole `Sharp/exSemiPf_deg_le`:

  * `EsetBndAux.exSemiPf_deg_le_of_deg` *derives* the hypothesis `hdeg` from the (proved) format
    and degree bookkeeping of `Sharp/exSemiPf_bounds` — it is `Sharp/exSemiPf_deg_le` with the
    two stratum hypotheses decoupled, which is the form the assembly uses;
  * `Eset_gen_of_deg_unconditional` is `Eset_bound_of_deg` with `hdeg` discharged by it: the
    `Eset`-family is generated at a constant format and with a degree that is a polynomial in
    `(D, k, a₀)`, with no hypothesis on the strata beyond the three bounds of the assembly.

  The three steps are:

  1. `exTset E L` is a `Star`-set, by the component bound `hE2` applied to `exSemiPf n m E L`
     (`Work.WilE8.StarOfSemipfLe.star_of_semipf_le`); the format is the constant `Next n a₀ + a₀`
     and the degree is the product of the component bound at `X.deg` with `X.deg`, which the
     degree hypothesis `hdeg` turns into a polynomial in `(D, |L|, a₀)`;
  2. `Gen.star` therefore puts `psiV ⁻¹' exTset E L` into `Gen`, and `Gen` is closed under the
     finite union over the list `S` (`Gen_list_iUnion`);
  3. `Gen` is closed under topological closure at constant format and polynomial degree
     (`Work.WilE9.Gen.gen_closure`), which is exactly `Eset n S L`.

  The hypotheses on the strata are used only in step 1: `E.2.X.fmt ≤ a₀` bounds the fibre
  dimension `m ≤ a₀`, `E.2.deg ≤ D` and `E.2.X.basics.length ≤ D + 1` are the two bounds the
  degree hypothesis consumes, and `S.length ≤ D + 1` bounds the number of summands of the union.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Main
import Submission.Work.WilE9.Sharp.exSemiPf_bounds
import Submission.Work.WilE8.StarOfSemipfLe.star_of_semipf_le
import Submission.Work.WilE8.Basic
import Submission.Work.WilE9.Sharp.AE.union_components_star
import Submission.Work.WilE9.Sharp.AE.exTsetC_star
import Submission.Work.WilE9.Gen.gen_closure
import Submission.Work.WilE9.Ift.OneShot.poly_eval_le


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

namespace EsetBndAux

/-! ## 0. Monotonicity of `MvPolynomial.eval` on `ℕ`-coefficient polynomials -/

/-- Evaluation of a multivariate polynomial with nonnegative integer coefficients is monotone in
each variable.  (Over `ℕ` this is unconditional: the coefficients are their own lower bounds.) -/
theorem eval_mono {σ : Type*} [Fintype σ] {v w : σ → ℕ} (h : ∀ i, v i ≤ w i)
    (p : MvPolynomial σ ℕ) : p.eval v ≤ p.eval w := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq']
  refine Finset.sum_le_sum fun d _ => ?_
  refine Nat.mul_le_mul_left _ ?_
  exact Finset.prod_le_prod fun i _ => Nat.pow_le_pow_left (h i) (d i)

/-! ## 1. Polynomial bookkeeping -/

/-- Substituting a multivariate polynomial into a univariate polynomial with nonnegative
integer coefficients commutes with evaluation. -/
theorem eval_eval₂_C {σ : Type*} (v : σ → ℕ) (d : MvPolynomial σ ℕ) (p : Polynomial ℕ) :
    MvPolynomial.eval v (Polynomial.eval₂ MvPolynomial.C d p) = p.eval (MvPolynomial.eval v d) := by
  rw [Polynomial.hom_eval₂]
  have h : (MvPolynomial.eval v).comp MvPolynomial.C = RingHom.id ℕ := by
    ext n; simp
  rw [h, Polynomial.eval₂_id]

/-! ## 2. Format of the extended system -/

/-- The format of the extended system is bounded by the constant `Next n a₀ + a₀` as soon as
the fibre dimension `m` and the stratum's format are bounded by `a₀`. -/
theorem exSemiPf_fmt_le (n a₀ m : ℕ) (E : EffStratum n m) (L : List (Fin n))
    (hm : m ≤ a₀) (hfmt : E.X.fmt ≤ a₀) :
    (exSemiPf n m E L).fmt ≤ Next n a₀ + a₀ := by
  have h1 : Next n m ≤ Next n a₀ := by simp only [Next]; omega
  have h2 : E.X.r ≤ a₀ := by
    have h := hfmt; simp only [SemiPf.fmt] at h; omega
  show Next n m + E.X.r ≤ Next n a₀ + a₀
  omega

/-! ## 2'. The degree bound of the extended system (an untainted replacement for
`Sharp/exSemiPf_deg_le`) -/

/-- **Degree bound for the extended system.**  This is the conclusion of `Sharp/exSemiPf_deg_le`,
i.e. exactly the hypothesis `hdeg` of `Eset_bound_of_deg`, derived from the (proved) format and
degree bookkeeping of `Sharp/exSemiPf_bounds`: the only difference is that the two bounds on the
stratum, `E.deg ≤ D` and `E.X.basics.length ≤ D + 1`, are *not* required to be related to each
other, which is what the assembly needs.  The numerical estimate is

  `deg (exSemiPf n m E L) ≤ A3 n a₀ * (D+1)^2 * (|L|+1)`

and the polynomial below is the one of `exSemiPf_bounds` evaluated at `![D, |L|, a₀]`. -/
theorem exSemiPf_deg_le_of_deg (n a₀ : ℕ) : ∃ b₀ : MvPolynomial (Fin 3) ℕ,
    ∀ (m : ℕ) (E : EffStratum n m) (L : List (Fin n)) (D : ℕ),
      m ≤ a₀ → E.X.fmt ≤ a₀ → E.deg ≤ D → E.X.basics.length ≤ D + 1 →
      (exSemiPf n m E L).deg ≤ b₀.eval ![D, L.length, a₀] := by
  refine ⟨MvPolynomial.C (A3 n a₀) * (1 + MvPolynomial.X (0 : Fin 3)) ^ 2
    * (1 + MvPolynomial.X (1 : Fin 3)), ?_⟩
  intro m E L D hm hfmt hDE hlen
  have hEval : MvPolynomial.eval ![D, L.length, a₀]
      (MvPolynomial.C (A3 n a₀) * (1 + MvPolynomial.X (0 : Fin 3)) ^ 2
        * (1 + MvPolynomial.X (1 : Fin 3)))
      = A3 n a₀ * (D + 1) ^ 2 * (L.length + 1) := by
    simp [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_add,
      MvPolynomial.eval_X] <;> ring
  rw [hEval]
  set S0 : ℕ := ∑ a : Fin (1 + m), atomDeg (E.h a) with hS0def
  set U : ℕ := atomDeg (exEq6 E.X.c E.h L) with hUdef
  have hS0_le : S0 ≤ E.deg := by rw [hS0def, EffStratum.deg]; omega
  have hXdeg_le : E.X.deg ≤ D := by have := hDE; rw [EffStratum.deg] at this; omega
  have hU_le : U ≤ A2 n a₀ * (D + 2) * (L.length + 1) := by
    rw [hUdef]
    refine (atomDeg_exEq6_le n m a₀ E L hm).trans ?_
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have hdeg_eq : (exSemiPf n m E L).deg
      = (E.X.basics.map (fun B => (exBasic E.X.c E.h L B).deg)).sum := by
    rw [SemiPf.deg, exSemiPf, List.map_map]; rfl
  have hsum : (E.X.basics.map (fun B => (exBasic E.X.c E.h L B).deg)).sum
      ≤ (E.X.basics.map (fun B => 5 * n + 10 + S0 + U + B.deg)).sum :=
    List.sum_le_sum (fun B _ => exBasic_deg_le E.X.c E.h L B S0 (le_of_eq hS0def.symm))
  have hsum2 : (E.X.basics.map (fun B => 5 * n + 10 + S0 + U + B.deg)).sum
      = E.X.basics.length * (5 * n + 10 + S0 + U) + E.X.deg := by
    rw [sum_map_add_const]
    rw [show (E.X.basics.map (fun B => B.deg)).sum = E.X.deg from rfl]
  rw [hdeg_eq]
  calc (E.X.basics.map (fun B => (exBasic E.X.c E.h L B).deg)).sum
      ≤ (E.X.basics.map (fun B => 5 * n + 10 + S0 + U + B.deg)).sum := hsum
    _ = E.X.basics.length * (5 * n + 10 + S0 + U) + E.X.deg := hsum2
    _ ≤ (D + 1) * (5 * n + 10 + D + U) + D := by
        have hc : 5 * n + 10 + S0 + U ≤ 5 * n + 10 + D + U := by omega
        have h1 : E.X.basics.length * (5 * n + 10 + S0 + U)
            ≤ (D + 1) * (5 * n + 10 + D + U) := Nat.mul_le_mul hlen hc
        omega
    _ ≤ (D + 1) * (5 * n + 10 + D + A2 n a₀ * (D + 2) * (L.length + 1)) + D := by
        have hc : 5 * n + 10 + D + U
            ≤ 5 * n + 10 + D + A2 n a₀ * (D + 2) * (L.length + 1) := by omega
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hc) _
    _ ≤ A3 n a₀ * (D + 1) ^ 2 * (L.length + 1) := arith_bound n a₀ D L.length

/-! ## 3. Step 1: `exTset E L` is a `Star`-set, with a uniform format and a polynomial degree -/

/-- **The `Star`-presentation of `exTsetC`.**  Under the three bounds supplied by the hypotheses
of `Eset_bound_of_deg` (`E.X.fmt ≤ a₀`, `E.deg ≤ D`, `E.X.basics.length ≤ D + 1`), the set
`exTsetC n m E q L` is a `Star`-set of the *constant* format `Next n a₀ + a₀` whose degree is a
polynomial in `(D, |L|, a₀)`.  The degree bound of the extended system is taken as the
hypothesis `hdeg` (the conclusion of `Sharp/exSemiPf_deg_le`) rather than proved here. -/
theorem exTsetC_star_of_deg (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ,
      ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k),
      X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (n a₀ : ℕ)
    (hdeg : ∃ b : MvPolynomial (Fin 3) ℕ,
      ∀ (m : ℕ) (E : EffStratum n m) (L : List (Fin n)) (D : ℕ),
        m ≤ a₀ → E.X.fmt ≤ a₀ → E.deg ≤ D → E.X.basics.length ≤ D + 1 →
        (exSemiPf n m E L).deg ≤ b.eval ![D, L.length, a₀]) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 3) ℕ),
    ∀ (m : ℕ) (E : EffStratum n m) (q : Fin (n + (1 + m)) → ℝ) (L : List (Fin n)) (D : ℕ),
      m ≤ a₀ → E.X.fmt ≤ a₀ → E.deg ≤ D → E.X.basics.length ≤ D + 1 →
      WilkiesDesign.E.Star a (MvPolynomial.eval ![D, L.length, a₀] b) (n + 1)
        (exTsetC n m E q L) := by
  classical
  obtain ⟨b₀, hb₀⟩ := hdeg
  refine ⟨Next n a₀ + a₀,
    Polynomial.eval₂ MvPolynomial.C b₀ ((hE2 (Next n a₀ + a₀)).choose * Polynomial.X), ?_⟩
  intro m E q L D hm hfmt hdegD hlen
  have hfmt' : (exSemiPf n m E L).fmt ≤ Next n a₀ + a₀ := exSemiPf_fmt_le n a₀ m E L hm hfmt
  have hstar := Work.WilE9.Sharp.AE.union_components_star hE2 (n + 1) (n + m + 3)
      (Next n a₀ + a₀) (exSemiPf n m E L) hfmt'
      (exComp n m E q L) (Work.WilE9.Sharp.AE.exComp_subset_set E q L)
      (Work.WilE9.Sharp.AE.exComp_componentIn_subset E q L)
  have hdeg_b := hb₀ m E L D hm hfmt hdegD hlen
  have hmono : (hE2 (Next n a₀ + a₀)).choose.eval (exSemiPf n m E L).deg * (exSemiPf n m E L).deg
      ≤ MvPolynomial.eval ![D, L.length, a₀]
          (Polynomial.eval₂ MvPolynomial.C b₀ ((hE2 (Next n a₀ + a₀)).choose * Polynomial.X)) := by
    rw [eval_eval₂_C, Polynomial.eval_mul, Polynomial.eval_X]
    exact Nat.mul_le_mul (Work.WilE9.Ift.OneShot.poly_eval_le hdeg_b) hdeg_b
  exact Work.WilE8.Star.mono hstar le_rfl hmono

/-! ## 4. Step 2: `Gen` is closed under finite unions indexed by a list -/

/-- `Gen` is closed under finite unions indexed by a list, the degrees adding up. -/
theorem Gen_list_iUnion {F n : ℕ} {α : Type*} (S : List α) (Df : α → ℕ)
    (A : α → Set (Fin n → ℝ)) (h : ∀ E ∈ S, WilkiesDesign.E.Gen F (Df E) n (A E)) :
    WilkiesDesign.E.Gen F (S.map Df).sum n (⋃ E ∈ S, A E) := by
  induction S with
  | nil =>
    have hset : (⋃ E ∈ ([] : List α), A E) = (∅ : Set (Fin n → ℝ)) := by
      ext x; simp
    rw [List.map_nil, List.sum_nil, hset]
    exact Work.WilE9.Gen.empty F n
  | cons a t ih =>
    have hset : (⋃ E ∈ (a :: t), A E) = A a ∪ (⋃ E ∈ t, A E) := by
      ext x; simp [List.mem_cons]
    rw [List.map_cons, List.sum_cons, hset]
    have h1 : WilkiesDesign.E.Gen F (Df a) n (A a) := h a (by simp)
    have h2 : WilkiesDesign.E.Gen F ((t.map Df).sum) n (⋃ E ∈ t, A E) :=
      ih (fun E hE => h E (by simp [hE]))
    have := Work.WilE9.Gen.union₂ h1 h2
    simpa [Nat.max_self] using this

/-! ## 5. Step 3: the assembly -/

/-- The `Eset`-family is generated at a constant format and with a degree that is a polynomial
in `(D, |L|, a₀)`.  This is `Sharp.Eset_gen` with the degree bound supplied as a hypothesis. -/
theorem Eset_gen_of_deg (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ,
      ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k),
      X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (n a₀ : ℕ)
    (hdeg : ∃ b : MvPolynomial (Fin 3) ℕ,
      ∀ (m : ℕ) (E : EffStratum n m) (L : List (Fin n)) (D : ℕ),
        m ≤ a₀ → E.X.fmt ≤ a₀ → E.deg ≤ D → E.X.basics.length ≤ D + 1 →
        (exSemiPf n m E L).deg ≤ b.eval ![D, L.length, a₀]) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 3) ℕ),
    ∀ (L : List (Fin n)) (S : List (AEStratum n)) (D : ℕ),
      S.length ≤ D + 1 →
      (∀ A ∈ S, A.E.X.fmt ≤ a₀) →
      (∀ A ∈ S, A.E.deg ≤ D) → (∀ A ∈ S, A.E.X.basics.length ≤ D + 1) →
      WilkiesDesign.E.Gen a (MvPolynomial.eval ![D, L.length, a₀] b) (n + 1)
        (Eset n S L) := by
  classical
  obtain ⟨a₁, b₁, hstar⟩ := exTsetC_star_of_deg hE2 n a₀ hdeg
  obtain ⟨a₂, b₂, hclos⟩ := Work.WilE9.Gen.gen_closure a₁ (n + 1)
  set d : MvPolynomial (Fin 3) ℕ := (MvPolynomial.X (0 : Fin 3) + MvPolynomial.C 1) * b₁ with hd
  set bf : MvPolynomial (Fin 3) ℕ := Polynomial.eval₂ MvPolynomial.C d b₂ with hbf
  refine ⟨a₂, bf, ?_⟩
  intro L S D hSlen hfmtS hdegS hlenS
  set v : Fin 3 → ℕ := ![D, L.length, a₀] with hv
  -- every stratum contributes a `Gen`-set
  have hstep : ∀ A ∈ S, WilkiesDesign.E.Gen a₁ (MvPolynomial.eval v b₁) (n + 1)
      (WilkiesDesign.E.psiV ⁻¹' exTsetC n A.1 A.E A.q L) := by
    intro A hA
    have hm : A.1 ≤ a₀ := by
      have h := hfmtS A hA
      simp only [SemiPf.fmt] at h
      omega
    have hs := hstar A.1 A.E A.q L D hm (hfmtS A hA) (hdegS A hA) (hlenS A hA)
    exact WilkiesDesign.E.Gen.star ⟨exTsetC n A.1 A.E A.q L, hs, rfl⟩
  have hunion := Gen_list_iUnion S (fun _ => MvPolynomial.eval v b₁)
      (fun A : AEStratum n => WilkiesDesign.E.psiV ⁻¹' exTsetC n A.1 A.E A.q L) hstep
  -- the degree of the union: `S.length` copies of the per-stratum bound, at most `D + 1`
  have hdeg_sum : (S.map (fun _ => MvPolynomial.eval v b₁)).sum =
      S.length * MvPolynomial.eval v b₁ := by
    rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
    simp
  have hd_eval : MvPolynomial.eval v d = (D + 1) * MvPolynomial.eval v b₁ := by
    rw [hd, MvPolynomial.eval_mul, MvPolynomial.eval_add, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    have hv0 : v 0 = D := rfl
    rw [hv0]
  have hle : (S.map (fun _ => MvPolynomial.eval v b₁)).sum ≤ MvPolynomial.eval v d := by
    rw [hdeg_sum, hd_eval]
    exact Nat.mul_le_mul_right _ hSlen
  have hunion' : WilkiesDesign.E.Gen a₁ (MvPolynomial.eval v d) (n + 1)
      (⋃ A ∈ S, WilkiesDesign.E.psiV ⁻¹' exTsetC n A.1 A.E A.q L) :=
    Work.WilE9.Gen.monoD hle hunion
  -- identify the union with the `psiV`-preimage of `Tset`
  have hpre : (⋃ A ∈ S, WilkiesDesign.E.psiV ⁻¹' exTsetC n A.1 A.E A.q L) =
      WilkiesDesign.E.psiV ⁻¹' Tset n S L := by
    simp only [Tset, Set.preimage_iUnion]
  have hunion'' : WilkiesDesign.E.Gen a₁ (MvPolynomial.eval v d) (n + 1)
      (WilkiesDesign.E.psiV ⁻¹' Tset n S L) := by
    rw [← hpre]
    exact hunion'
  -- closure, and the final polynomial bookkeeping
  have hclos' := hclos (MvPolynomial.eval v d)
    (WilkiesDesign.E.psiV ⁻¹' Tset n S L) hunion''
  have hfin : b₂.eval (MvPolynomial.eval v d) = MvPolynomial.eval v bf := by
    rw [hbf]
    exact (eval_eval₂_C v d b₂).symm
  rw [hfin] at hclos'
  exact hclos'

end EsetBndAux

theorem Eset_bound_of_deg (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k),
      X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (n a₀ : ℕ)
    (hdeg : ∃ b : MvPolynomial (Fin 3) ℕ,
      ∀ (m : ℕ) (E : Work.WilE9.Sharp.EffStratum n m) (L : List (Fin n)) (D : ℕ),
        m ≤ a₀ → E.X.fmt ≤ a₀ → E.deg ≤ D → E.X.basics.length ≤ D + 1 →
        (Work.WilE9.Sharp.exSemiPf n m E L).deg ≤ b.eval ![D, L.length, a₀]) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 3) ℕ),
      ∀ (k : ℕ) (S : List (Work.WilE9.Sharp.AEStratum n)) (L : List (Fin n)) (D : ℕ),
        L.length ≤ k → S.length ≤ D + 1 →
        (∀ A ∈ S, A.E.X.fmt ≤ a₀) → (∀ A ∈ S, A.E.deg ≤ D) →
        (∀ A ∈ S, A.E.X.basics.length ≤ D + 1) →
        WilkiesDesign.E.Gen a (MvPolynomial.eval ![D, k, a₀] b) (n + 1)
          (Work.WilE9.Sharp.Eset n S L) := by
  obtain ⟨a, b, hb⟩ := EsetBndAux.Eset_gen_of_deg hE2 n a₀ hdeg
  refine ⟨a, b, ?_⟩
  intro k S L D hLk hSlen hfmt hdegS hlen
  refine Work.WilE9.Gen.monoD ?_ (hb L S D hSlen hfmt hdegS hlen)
  exact EsetBndAux.eval_mono (fun i => by fin_cases i <;> simp [hLk]) b

/-- **`Eset_bound_of_deg` with the degree hypothesis discharged.**  The degree bound `hdeg` of
`Eset_bound_of_deg` is supplied by `EsetBndAux.exSemiPf_deg_le_of_deg`, which is proved from the
format/degree bookkeeping of `Sharp/exSemiPf_bounds` and therefore does not depend on the hole
`Sharp/exSemiPf_deg_le`.  Consequently the family `Eset n S L` is generated by `Gen` at a
constant format and with a degree that is a polynomial in `(D, k, a₀)`, with no hypothesis on the
strata beyond the three bounds used by the assembly. -/
theorem Eset_gen_of_deg_unconditional
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k),
      X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (n a₀ : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 3) ℕ),
      ∀ (k : ℕ) (S : List (Work.WilE9.Sharp.AEStratum n)) (L : List (Fin n)) (D : ℕ),
        L.length ≤ k → S.length ≤ D + 1 →
        (∀ A ∈ S, A.E.X.fmt ≤ a₀) → (∀ A ∈ S, A.E.deg ≤ D) →
        (∀ A ∈ S, A.E.X.basics.length ≤ D + 1) →
        WilkiesDesign.E.Gen a (MvPolynomial.eval ![D, k, a₀] b) (n + 1)
          (Work.WilE9.Sharp.Eset n S L) :=
  Eset_bound_of_deg hE2 n a₀ (EsetBndAux.exSemiPf_deg_le_of_deg n a₀)

end Work.WilE9.Sharp
