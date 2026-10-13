import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Loj.multBound_converging
import Submission.Work.WilE3.Taylor.HasLoj.Reductions
import Submission.Work.WilE3.Taylor.HasLoj.Sumsq

/-!
  annals_wilkies_conjecture, AREA E3: the assembly that reduces the target
  `Work.WilE3.Taylor.hasLoj_of_multiplicity` to the **single EA polynomial** statement.

  The target concerns the residual `∑_{f ∈ B.eqs} |eaEval c f x|` against the common zero set `Z` of
  `B.eqs`.  Writing `Φ := ∑_{f ∈ B.eqs} f²` (an EA polynomial with `{Φ = 0} = Z`, `Φ ≥ 0`), the
  elementary reductions proved in `HasLoj/Sumsq.lean` give the target as soon as one knows the
  Łojasiewicz inequality for the single EA polynomial `Φ`:

    `∀ F, ∃ K, ∀ c Φ y q, k + r ≤ F → K.eval (atomDeg Φ) < q →
       HasLoj (fun x => |eaEval c Φ x|) {x | eaEval c Φ x = 0} y q`.

  `hasLoj_of_single` below proves exactly that implication (the degree bookkeeping uses
  `eaEval_list_sum_sq`, `zero_set_list_sum_sq` and `totalDegree_list_sum_sq_le`).  So the whole
  remaining mathematical content of the target is the *single-EA-polynomial* Łojasiewicz inequality
  (Gabrielov 1995 Thm 3.4 in the single-function form) — see `NOTES_hasLoj_of_multiplicity.md`.
-/

namespace Work.WilE3.Taylor

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

variable {k r : ℕ}

/-- `eaEval` of a sum of squares is the corresponding sum of squares of the values. -/
theorem eaEval_list_sum_sq (c : EAChain k r) (L : List (EAPoly k r)) (x : Fin k → ℝ) :
    eaEval c ((L.map fun f => f ^ 2).sum) x = (L.map fun f => (eaEval c f x) ^ 2).sum := by
  have hadd : ∀ Q Q' : EAPoly k r, eaEval c (Q + Q') x = eaEval c Q x + eaEval c Q' x :=
    fun Q Q' => map_add (MvPolynomial.eval (Sum.elim x fun j => Real.exp (c.ell j x))) Q Q'
  have hmul : ∀ Q Q' : EAPoly k r, eaEval c (Q * Q') x = eaEval c Q x * eaEval c Q' x :=
    fun Q Q' => map_mul (MvPolynomial.eval (Sum.elim x fun j => Real.exp (c.ell j x))) Q Q'
  induction L with
  | nil => simp [eaEval]
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    rw [hadd, pow_two (a : EAPoly k r), hmul, ih]
    ring

/-- The total degree of a sum of squares is at most twice the sum of the total degrees. -/
theorem totalDegree_list_sum_sq_le (L : List (EAPoly k r)) :
    ((L.map fun f => f ^ 2).sum).totalDegree ≤ 2 * (L.map fun f => f.totalDegree).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    have h1 : ((a ^ 2 + (t.map fun f => f ^ 2).sum)).totalDegree ≤
        max ((a ^ 2).totalDegree) ((t.map fun f => f ^ 2).sum).totalDegree :=
      MvPolynomial.totalDegree_add _ _
    have h2 : (a ^ 2 : EAPoly k r).totalDegree ≤ 2 * a.totalDegree :=
      MvPolynomial.totalDegree_pow a 2
    have h3 : a.totalDegree ≤ atomDeg a := by simp [atomDeg]
    omega

/-- The atom degree of a sum of squares of a nonempty list is at most `3` times the sum of the
atom degrees. -/
theorem atomDeg_list_sum_sq_le {L : List (EAPoly k r)} (hL : L ≠ []) :
    atomDeg ((L.map fun f => f ^ 2).sum) ≤ 3 * (L.map fun f => atomDeg f).sum := by
  have htd := totalDegree_list_sum_sq_le L
  have hle1 : (L.map fun f => f.totalDegree).sum ≤ (L.map fun f => atomDeg f).sum :=
    List.sum_le_sum fun f _ => by simp [atomDeg]
  have hne : (L.map fun f => atomDeg f) ≠ [] := by simpa using hL
  have hpos : 1 ≤ (L.map fun f => atomDeg f).sum := by
    rcases L with _ | ⟨a, t⟩
    · exact absurd rfl hL
    · simp only [List.map_cons, List.sum_cons, atomDeg]
      omega
  have : atomDeg ((L.map fun f => f ^ 2).sum) =
      ((L.map fun f => f ^ 2).sum).totalDegree + 1 := rfl
  omega

/-- A sum of nonnegative reals vanishes only if every term does. -/
theorem list_sum_eq_zero_of_nonneg : ∀ (L : List ℝ), (∀ a ∈ L, 0 ≤ a) → L.sum = 0 →
    ∀ a ∈ L, a = 0
  | [], _, _, a, ha => by simp at ha
  | a :: t, h0, h, b, hb => by
    have ht0 : 0 ≤ t.sum := List.sum_nonneg fun z hz => h0 z (List.mem_cons_of_mem a hz)
    have h' : a + t.sum = 0 := h
    have ha : a = 0 := by linarith [h0 a (List.mem_cons_self ..)]
    have ht : t.sum = 0 := by linarith
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ha
    · exact list_sum_eq_zero_of_nonneg t (fun z hz => h0 z (List.mem_cons_of_mem a hz)) ht b hb'

/-- The zero set of a sum of squares is the common zero set. -/
theorem zero_set_list_sum_sq (c : EAChain k r) (L : List (EAPoly k r)) :
    {x : Fin k → ℝ | eaEval c ((L.map fun f => f ^ 2).sum) x = 0}
      = {x : Fin k → ℝ | ∀ f ∈ L, eaEval c f x = 0} := by
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, eaEval_list_sum_sq]
  constructor
  · intro h f hf
    have h0 : ∀ a ∈ L.map (fun f => eaEval c f x ^ 2), 0 ≤ a := by
      intro a ha
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
      positivity
    exact sq_eq_zero_iff.mp
      (list_sum_eq_zero_of_nonneg _ h0 h (eaEval c f x ^ 2) (List.mem_map_of_mem hf))
  · intro h
    refine List.sum_eq_zero (fun a ha => ?_)
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
    simp [h g hg]

/-- **The target reduces to the single-EA-polynomial Łojasiewicz inequality.**  If the inequality
holds for the zero set of every single EA polynomial, with an exponent bounded by a polynomial in
the atom degree, then it holds for the residual of an arbitrary basic EA set against its common zero
set. -/
theorem hasLoj_of_single
    (h : ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (Φ : EAPoly k r)
      (y : Fin k → ℝ) (q : ℕ), k + r ≤ F → K.eval (atomDeg Φ) < q →
      Work.WilE3.HasLoj (fun x => |eaEval c Φ x|) {x | eaEval c Φ x = 0} y q) :
    ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (B : Basic k r)
      (y : Fin k → ℝ) (q : ℕ), k + r ≤ F → K.eval B.deg < q →
      Work.WilE3.HasLoj (fun x => (B.eqs.map fun f => |eaEval c f x|).sum)
        {x | ∀ f' ∈ B.eqs, eaEval c f' x = 0} y q := by
  intro F
  obtain ⟨K1, hK1⟩ := h F
  refine ⟨K1.comp (Polynomial.C 3 * Polynomial.X) + 1, ?_⟩
  intro k r c B y q hkr hK
  have hKev : (K1.comp (Polynomial.C 3 * Polynomial.X) + 1).eval B.deg
      = K1.eval (3 * B.deg) + 1 := by
    rw [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one]
  rw [hKev] at hK
  rcases hB : B.eqs with _ | ⟨f0, rest⟩
  · exact hasLoj_of_eqs_empty c y (by omega)
  · set Φ : EAPoly k r := ((f0 :: rest).map fun f => f ^ 2).sum with hΦ
    -- the atom degree of `Φ` is at most `3 * B.deg`
    have hdeg1 : atomDeg Φ ≤ 3 * ((f0 :: rest).map fun f => atomDeg f).sum := by
      rw [hΦ]
      exact atomDeg_list_sum_sq_le (by simp)
    have hdeg2 : ((f0 :: rest).map fun f => atomDeg f).sum ≤ B.deg := by
      rw [Basic.deg, hB, List.map_append, List.sum_append]
      exact Nat.le_add_right _ _
    have hdeg : atomDeg Φ ≤ 3 * B.deg := le_trans hdeg1 (Nat.mul_le_mul_left 3 hdeg2)
    -- the exponent `2 * q` is admitted by `K1`
    have h2q : K1.eval (atomDeg Φ) < 2 * q := by
      have hmono : K1.eval (atomDeg Φ) ≤ K1.eval (3 * B.deg) :=
        Work.WilE3.Loj.polynomial_eval_le_eval hdeg
      omega
    have hLoj := hK1 k r c Φ y (2 * q) hkr h2q
    -- transport along `eaEval Φ x = ∑ (eaEval c f x)²` and the zero set identification
    have hLoj2 : Work.WilE3.HasLoj
        (fun x => ((f0 :: rest).map fun f => (eaEval c f x) ^ 2).sum)
        {x | ∀ f' ∈ (f0 :: rest), eaEval c f' x = 0} y (2 * q) := by
      have hfun : (fun x => ((f0 :: rest).map fun f => (eaEval c f x) ^ 2).sum)
          = (fun x => |eaEval c Φ x|) := by
        funext x
        have hnn : 0 ≤ ((f0 :: rest).map fun f => (eaEval c f x) ^ 2).sum :=
          List.sum_nonneg fun a ha => by
            obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
            positivity
        rw [hΦ]
        rw [eaEval_list_sum_sq c (f0 :: rest) x]
        exact (abs_of_nonneg hnn).symm
      have hset : {x | ∀ f' ∈ (f0 :: rest), eaEval c f' x = 0}
          = {x | eaEval c Φ x = 0} := by
        rw [hΦ]
        exact (zero_set_list_sum_sq c (f0 :: rest)).symm
      rw [hfun, hset]
      exact hLoj
    exact hasLoj_residual_of_sum_sq c ⟨f0 :: rest, B.pos⟩ y hLoj2

end Work.WilE3.Taylor
