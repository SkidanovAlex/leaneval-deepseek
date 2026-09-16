import Submission.ZagierHoffmanProof.Step6Tuple
import Submission.ZagierHoffmanProof.TwRows
import Submission.Commons.NumberTheory.ThetaDegObstruction.obstruction
import Submission.Commons.NumberTheory.ThetaDegObstruction.obstruction_bound
import Submission.Commons.NumberTheory.ThetaDegObstruction.dvd_of_dvd_mul_pow

/-!
# The two-term endgame (Dac §6, the `|T| = 2` case of the `𝒯'`-induction)

`Step6Tuple.tupleIndP_of_twoTerm` reduces Dac's Theorem 6.2 to the predicate `TwoTermIndP w`
(Dac's §6 Step 3(c)): a relation `a • ζ_A(w) + b • ζ_A(k, q-1) = 0` with `a, b ≠ 0` and
`w = k + (q-1)` cannot exist at the weight `w ≤ 2q-2`.

This module does the **mechanical** half of that reduction:

* `tupleListHP_inj_entries` — the exponent list determines the `Fin`-indexed tuple;
* `zeta_eq_twS1_of_tupleListHP` / `zeta_eq_twS2_of_tupleListHP` — reindexing `ζ_A 𝔰` to the two
  canonical tuples `(w)` and `(k, q-1)` from the shape of `tupleListHP F 𝔰`;
* `lseries_relation_tw` — from a two-term relation one gets the `(LD)` input of the ABP descent in
  the exact shape required by `Endgame2.tw_second_relation`: two nonzero Frobenius-fixed polynomials
  `A₁, A₂` with `evalSeriesGen (tmF … (twDatum …) (twCf … A₁ A₂) []) θ = 0`;
* `TwRowFalse w` — the **remaining mathematical content** (the subject of `Step8TwRow.lean`): the
  `(LD)` input for the two-term datum with `A₁, A₂ ≠ 0` is impossible;
* `twoTermIndP_of_rowFalse` — `TwRowFalse` at every weight `≤ 2q-2` implies `TwoTermIndP`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

universe u

variable {F : Type u} [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. Recovering a `Fin`-indexed tuple from the shape of its exponent list -/

/-- The `F`- and `H`-parts of `tupleListHP` determine the tuple. -/
lemma tupleListHP_inj_entries {n : ℕ} {𝔰 𝔰' : Fin n → ℕ+}
    (h : tupleListHP F 𝔰 = tupleListHP F 𝔰') : 𝔰 = 𝔰' := by
  have h' : List.ofFn (fun j : Fin n => ((𝔰 j : ℕ), (ambH F (𝔰 j) : Polynomial (Ambient F))))
      = List.ofFn (fun j : Fin n => ((𝔰' j : ℕ), (ambH F (𝔰' j) : Polynomial (Ambient F)))) := h
  have h2 := List.ofFn_inj.mp h'
  funext j
  exact PNat.eq (congrArg Prod.fst (congrFun h2 j))

/-- The entries of `tupleListHP` are the exponents. -/
lemma tupleListHP_entries_eq {n : ℕ} {𝔰 : Fin n → ℕ+} {w : ℕ}
    (h : tupleListHP F 𝔰 = [(w, (ambH F w : Polynomial (Ambient F)))]) :
    ∀ j : Fin n, (𝔰 j : ℕ) = w := by
  have hn : n = 1 := by
    have h2 := congrArg List.length h
    rw [tupleListHP_length, List.length_singleton] at h2
    exact h2
  subst hn
  intro j
  have hfun : (fun j : Fin 1 => (𝔰 j : ℕ)) = (fun _ : Fin 1 => w) := by
    apply List.ofFn_inj.mp
    have h1 := congrArg (List.map Prod.fst) h
    rw [show (List.map Prod.fst (tupleListHP F 𝔰))
        = List.ofFn (fun j : Fin 1 => (𝔰 j : ℕ)) from by
      rw [tupleListHP]; exact List.map_ofFn] at h1
    simpa using h1
  exact congrFun hfun j

/-- ★ **Reindexing to `(w)`**: if `tupleListHP F 𝔰 = [(w, H_w)]` then `ζ_A 𝔰 = ζ_A (w)`. -/
lemma zeta_eq_twS1_of_tupleListHP {n : ℕ} (𝔰 : Fin n → ℕ+) {w : ℕ} (hw : 0 < w)
    (h : tupleListHP F 𝔰 = [(w, (ambH F w : Polynomial (Ambient F)))]) :
    ζ_A F 𝔰 = ζ_A F (twS1 w hw) := by
  have hn : n = 1 := by
    have h2 := congrArg List.length h
    rw [tupleListHP_length, List.length_singleton] at h2
    exact h2
  subst hn
  congr 1
  funext j
  exact PNat.eq (tupleListHP_entries_eq (F := F) h j)

/-- ★ **Reindexing to `(k, q-1)`**: if `tupleListHP F 𝔰 = [(k, H_k), (q-1, H_{q-1})]` then
`ζ_A 𝔰 = ζ_A (k, q-1)`. -/
lemma zeta_eq_twS2_of_tupleListHP {n : ℕ} (𝔰 : Fin n → ℕ+) {k : ℕ} (hk : 0 < k)
    (h : tupleListHP F 𝔰 = [(k, (ambH F k : Polynomial (Ambient F))),
       (Nat.card F - 1, (ambH F (Nat.card F - 1) : Polynomial (Ambient F)))]) :
    ζ_A F 𝔰 = ζ_A F (twS2 F k hk) := by
  have hn : n = 2 := by
    have h2 := congrArg List.length h
    rw [tupleListHP_length] at h2
    simpa using h2
  subst hn
  have hfun : (fun j : Fin 2 => (𝔰 j : ℕ)) = (fun j : Fin 2 => (twS2 F k hk j : ℕ)) := by
    apply List.ofFn_inj.mp
    have h1 := congrArg (List.map Prod.fst) h
    rw [show (List.map Prod.fst (tupleListHP F 𝔰))
        = List.ofFn (fun j : Fin 2 => (𝔰 j : ℕ)) from by
      rw [tupleListHP]; exact List.map_ofFn] at h1
    rw [h1]
    simp [twS2]
  congr 1
  funext j
  exact PNat.eq (congrFun hfun j)

/-! ## §2. The `(LD)` input for the two-term datum -/

/-- The two-term datum as an explicit `Fin 2`-indexed family of exponent tuples. -/
noncomputable def twFamily (F : Type u) [Field F] [Finite F] (w k : ℕ) (hw : 0 < w) (hk : 0 < k) :
    Fin 2 → Σ r : ℕ, Fin r → ℕ+ :=
  fun i => if i = 0 then ⟨1, twS1 w hw⟩ else ⟨2, twS2 F k hk⟩

@[simp] lemma twFamily_zero (w k : ℕ) (hw : 0 < w) (hk : 0 < k) :
    twFamily F w k hw hk 0 = ⟨1, twS1 w hw⟩ := by
  simp [twFamily]

@[simp] lemma twFamily_one (w k : ℕ) (hw : 0 < w) (hk : 0 < k) :
    twFamily F w k hw hk 1 = ⟨2, twS2 F k hk⟩ := by
  simp [twFamily]

lemma twS1_list_ne_twS2_list (w k : ℕ) (hw : 0 < w) (hk : 0 < k) :
    tupleListHP F (twS1 w hw) ≠ tupleListHP F (twS2 F k hk) := by
  rw [twS1_list, twS2_list]; simp

section Frobenius

/-- `polyTwist 1` fixes polynomials whose coefficients are `ambF`-multiples of the coefficient map. -/
lemma polyTwist_map_ambCoeff (p : Polynomial F) :
    polyTwist (q := Nat.card F) 1 (p.map (ambCoeff F)) = p.map (ambCoeff F) :=
  (polyTwist_one_eq_self_iff F (p.map (ambCoeff F))).mpr (fun n => by
    rw [Polynomial.coeff_map]; exact ambCoeff_mem_ambF F _)

/-- `polyTwist 1` fixes the `Γ`-product of a tuple. -/
lemma polyTwist_gammaPolyTup_poly {n : ℕ} (𝔰 : Fin n → ℕ+) :
    polyTwist (q := Nat.card F) 1 (gammaPolyTup F 𝔰) = gammaPolyTup F 𝔰 :=
  Polynomial.coe_injective (Ambient F)
    (by rw [coe_polyTwist', frobTwist_gammaPolyTup])

/-- The power-series form of `polyTwist`-invariance. -/
lemma frobTwist_eq_self_of_polyTwist_eq_self {p : Polynomial (Ambient F)}
    (h : polyTwist (q := Nat.card F) 1 p = p) :
    frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((p : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((p : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
  rw [← coe_polyTwist', h]

end Frobenius

section Denominator

/-- ★★★ **The `(LD)` input of the ABP descent for the two-term datum.**  A two-term `K`-relation
`A • ζ_A(w) + B • ζ_A(k,q-1) = 0` with `A, B ∈ F[X] ∖ {0}` and `w = k + (q-1)` produces nonzero
Frobenius-fixed polynomials `A₁, A₂` such that `evalSeriesGen (tmF … []) θ = 0` — exactly the
hypothesis `hval` of `Endgame2.tw_second_relation`. -/
theorem lseries_relation_tw {w k : ℕ} (hw : 0 < w) (hk : 0 < k)
    (hwk : w = k + (Nat.card F - 1)) (hkq : k ≤ Nat.card F - 1)
    (hw2 : w ≤ 2 * Nat.card F - 2)
    {A B : Polynomial F} (hAne : A ≠ 0) (hBne : B ≠ 0)
    (hrel : (A : RatFunc F) • ζ_A F (twS1 w hw) + (B : RatFunc F) • ζ_A F (twS2 F k hk) = 0) :
    ∃ A₁ A₂ : Polynomial (Ambient F), A₁ ≠ 0 ∧ A₂ ≠ 0 ∧
      frobTwist (R := Ambient F) (p := Nat.card F) 1
        ((A₁ : Polynomial (Ambient F)) : PowerSeries (Ambient F))
        = ((A₁ : Polynomial (Ambient F)) : PowerSeries (Ambient F)) ∧
      frobTwist (R := Ambient F) (p := Nat.card F) 1
        ((A₂ : Polynomial (Ambient F)) : PowerSeries (Ambient F))
        = ((A₂ : Polynomial (Ambient F)) : PowerSeries (Ambient F)) ∧
      evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (twDatum F w k hw hk)
          (twCf F hw hk A₁ A₂) ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F)
        + (0 : Polynomial (Ambient F)).eval (ambTheta F) = 0 := by
  classical
  -- (3) the (LD) transport
  have hpos : ∀ i, 0 < (twFamily F w k hw hk i).1 := by
    intro i; fin_cases i
    · show 0 < (1 : ℕ); omega
    · show 0 < (2 : ℕ); omega
  have hsup : ∀ i j, ((twFamily F w k hw hk i).2 j : ℕ) ≤ 2 * Nat.card F - 2 := by
    have hq2 : 2 ≤ Nat.card F := by omega
    intro i; fin_cases i
    · intro j
      show (twS1 w hw j : ℕ) ≤ 2 * Nat.card F - 2
      simpa [twS1] using hw2
    · intro j
      fin_cases j
      · show (k : ℕ) ≤ 2 * Nat.card F - 2
        omega
      · show (Nat.card F - 1 : ℕ) ≤ 2 * Nat.card F - 2
        have h2 : 2 * Nat.card F - 2 = 2 * (Nat.card F - 1) := by omega
        rw [h2]
        exact le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)
  have hwt : ∀ i, ∑ j : Fin (twFamily F w k hw hk i).1,
      ((twFamily F w k hw hk i).2 j : ℕ) = w := by
    intro i; fin_cases i
    · show (∑ j : Fin 1, (twS1 w hw j : ℕ)) = w
      simp [twS1]
    · show (∑ j : Fin 2, (twS2 F k hk j : ℕ)) = w
      rw [Fin.sum_univ_two, twS2_zero, twS2_one]
      show (k : ℕ) + (Nat.card F - 1 : ℕ) = w
      omega
  have hrel' : (∑ i : Fin 2, (((![A, B] : Fin 2 → Polynomial F)) i : RatFunc F)
      • ζ_A F ((twFamily F w k hw hk i).2)) = 0 := by
    rw [Fin.sum_univ_two]
    rw [twFamily_zero, twFamily_one]
    simpa using hrel
  have hLD := lseries_relationP (F := F) (twFamily F w k hw hk) hpos hsup w hwt ![A, B] hrel'
  rw [Fin.sum_univ_two] at hLD
  -- (4) the two coefficient polynomials
  set A₁ : Polynomial (Ambient F) :=
    (A.map (ambCoeff F)) * gammaPolyTup F (twS2 F k hk) with hA₁
  set A₂ : Polynomial (Ambient F) :=
    (B.map (ambCoeff F)) * gammaPolyTup F (twS1 w hw) with hA₂
  have hE0 : (Finset.univ.erase (0 : Fin 2)) = ({1} : Finset (Fin 2)) := by decide
  have hE1 : (Finset.univ.erase (1 : Fin 2)) = ({0} : Finset (Fin 2)) := by decide
  have hLD' : A₁.eval (ambTheta F) * evalSeriesGen (tmL (Nat.card F) (ambOmega F)
        (tupleListHP F (twS1 w hw))) (ambTheta F)
      + A₂.eval (ambTheta F) * evalSeriesGen (tmL (Nat.card F) (ambOmega F)
        (tupleListHP F (twS2 F k hk))) (ambTheta F) = 0 := by
    have h := hLD
    rw [hE0, hE1, Finset.prod_singleton, Finset.prod_singleton, twFamily_zero,
      twFamily_one] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Polynomial.eval_mul, ← hA₁, ← hA₂] at h
    exact h
  -- (5) the evaluation of `tmF` at the empty prefix
  have hse : ∀ s ∈ twDatum F w k hw hk,
      GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F)
        (s.drop ([] : List (ℕ × Polynomial (Ambient F))).length)) := by
    intro s hs
    refine gSuperEntire_tmL_of_mem (F := F) (γ := ambGamma) (ω := ambOmega F)
      (S := twDatum F w k hw hk) ambGamma_lt_one gammaArchimedean_rat (two_le_ambCard F)
      (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F) ?_ ?_ (u := s.drop 0) ?_
    · intro s' hs' y hy
      rw [twDatum] at hs'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
      rcases hs' with rfl | rfl
      · rw [twS1_list] at hy
        simp only [List.mem_singleton] at hy
        rw [hy]; exact gIsSmall_ambOmega_pow_mul_ambH F hw
      · rw [twS2_list] at hy
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact gIsSmall_ambOmega_pow_mul_ambH F hk
        · exact gIsSmall_ambOmega_pow_mul_ambH F (by omega)
    · intro s' hs' y hy
      rw [twDatum] at hs'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
      rcases hs' with rfl | rfl
      · rw [twS1_list] at hy
        simp only [List.mem_singleton] at hy
        rw [hy]; exact gSuperEntire_ambH F _
      · rw [twS2_list] at hy
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact gSuperEntire_ambH F _
        · exact gSuperEntire_ambH F _
    · intro y hy
      exact ⟨s, hs, hy⟩
  have htmF := evalSeriesGen_tmF_shared (F := F) (w := w) (S := twDatum F w k hw hk)
    (cf := twCf F hw hk A₁ A₂) (t := ([] : List (ℕ × Polynomial (Ambient F)))) hse
  have htmF' : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (twDatum F w k hw hk)
      (twCf F hw hk A₁ A₂) ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F)
      = A₁.eval (ambTheta F) * evalSeriesGen (tmL (Nat.card F) (ambOmega F)
            (tupleListHP F (twS1 w hw))) (ambTheta F)
        + A₂.eval (ambTheta F) * evalSeriesGen (tmL (Nat.card F) (ambOmega F)
            (tupleListHP F (twS2 F k hk))) (ambTheta F) := by
    rw [htmF, twDatum, Finset.sum_pair (twS1_list_ne_twS2_list w k hw hk)]
    simp only [List.length_nil, List.take_zero, List.drop_zero, ↓reduceIte, twCf_mem₁,
      twCf_mem₂]
  refine ⟨A₁, A₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hA₁]
    exact mul_ne_zero
      ((Polynomial.map_ne_zero_iff (ambCoeff F).injective).mpr hAne)
      (fun h0 => by
        have h1 : (gammaPolyTup F (twS2 F k hk)).eval (ambTheta F) = 0 := by rw [h0]; simp
        rw [eval_gammaPolyTup] at h1
        exact (Finset.prod_ne_zero_iff.mpr (fun j _ => ambGammaF_ne_zero F _)) h1)
  · rw [hA₂]
    exact mul_ne_zero
      ((Polynomial.map_ne_zero_iff (ambCoeff F).injective).mpr hBne)
      (fun h0 => by
        have h1 : (gammaPolyTup F (twS1 w hw)).eval (ambTheta F) = 0 := by rw [h0]; simp
        rw [eval_gammaPolyTup] at h1
        exact (Finset.prod_ne_zero_iff.mpr (fun j _ => ambGammaF_ne_zero F _)) h1)
  · refine frobTwist_eq_self_of_polyTwist_eq_self (p := A₁) ?_
    rw [hA₁, polyTwist_mul, polyTwist_map_ambCoeff, polyTwist_gammaPolyTup_poly]
  · refine frobTwist_eq_self_of_polyTwist_eq_self (p := A₂) ?_
    rw [hA₂, polyTwist_mul, polyTwist_map_ambCoeff, polyTwist_gammaPolyTup_poly]
  · rw [htmF']
    simpa using hLD'

end Denominator

/-! ## §3. The remaining mathematical content: `TwRowFalse`

Everything after `lseries_relation_tw` is the deep part: from the `(LD)` input one runs the ABP
descent (`Endgame2.tw_second_relation`, hence `TwRows.tw_Y_mul_P_eq`) and obtains the two rows

  **(R)** `Q·σ(Z) = σ(Q)·W^w·(Q·A₁·H_w + Z + Y)`,   **(A)** `Y·(X^q - X) = -A₂·L^q·Q`

with `Q ≠ 0` and all coefficients of `P` in `K^{perf}`.  The claim that these are **impossible** for
`A₁, A₂ ≠ 0` is `TwRowFalse`; it is the only missing input of Dac's Theorem 6.2 in this development.
-/

/-- **The two-term ABP rows are impossible.**  For every `k ≥ 1` with `w = k + (q-1)`, `k ≤ q-1`
and every pair of nonzero Frobenius-fixed `A₁, A₂ ∈ F_q[X]`, the `(LD)` input of
`Endgame2.tw_second_relation` cannot hold.

This is stated in the `(LD)` form deliberately: `Endgame2.tw_second_relation` turns the failure of
this statement into the two rows (R)/(A), so a proof only has to analyse those two rows. -/
def TwRowFalse (F : Type u) [Field F] [Finite F] [DecidableEq (RatFunc F)] (w : ℕ) : Prop :=
  ∀ (k : ℕ) (hw : 0 < w) (hk : 0 < k) (hwk : w = k + (Nat.card F - 1))
    (hkq : k ≤ Nat.card F - 1) (A₁ A₂ : Polynomial (Ambient F)),
    frobTwist (R := Ambient F) (p := Nat.card F) 1
        ((A₁ : Polynomial (Ambient F)) : PowerSeries (Ambient F))
        = ((A₁ : Polynomial (Ambient F)) : PowerSeries (Ambient F)) →
    frobTwist (R := Ambient F) (p := Nat.card F) 1
        ((A₂ : Polynomial (Ambient F)) : PowerSeries (Ambient F))
        = ((A₂ : Polynomial (Ambient F)) : PowerSeries (Ambient F)) →
    A₁ ≠ 0 → A₂ ≠ 0 →
    evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (twDatum F w k hw hk)
        (twCf F hw hk A₁ A₂) ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F)
      + (0 : Polynomial (Ambient F)).eval (ambTheta F) ≠ 0

/-- ★★★ **The two-term endgame from the row obstruction.**  `TwRowFalse` at every weight
`q < w ≤ 2q-2` implies Dac's Step 3(c): the two-term independence `TwoTermIndP` in that range.
(The restriction to `q < w` is the honest one: for `w ≤ q` the endgame is not needed, and
`TwoTermIndP q` is false in general — cf. `PLAN.md`.) -/
theorem twoTermIndP_of_rowFalse
    (h : ∀ w : ℕ, Nat.card F < w → w ≤ 2 * Nat.card F - 2 → TwRowFalse F w) :
    ∀ w : ℕ, Nat.card F < w → w ≤ 2 * Nat.card F - 2 → TwoTermIndP (F := F) w := by
  intro w hqw hw2
  have hw1 : 1 ≤ w := by have := two_le_ambCard F; omega
  rw [TwoTermIndP]
  intro r₁ r₂ 𝔰₁ 𝔰₂ k hk hwk h1 h2 A B hAne hBne hzero
  have hw' : 0 < w := by omega
  have hk' : 0 < k := by omega
  have hkq : k ≤ Nat.card F - 1 := by omega
  have hζ1 : ζ_A F 𝔰₁ = ζ_A F (twS1 w hw') :=
    zeta_eq_twS1_of_tupleListHP (F := F) 𝔰₁ hw' h1
  have hζ2 : ζ_A F 𝔰₂ = ζ_A F (twS2 F k hk') :=
    zeta_eq_twS2_of_tupleListHP (F := F) 𝔰₂ hk' h2
  rw [hζ1, hζ2] at hzero
  obtain ⟨A₁, A₂, hA₁ne, hA₂ne, hA₁fix, hA₂fix, hval⟩ :=
    lseries_relation_tw (F := F) (w := w) (k := k) hw' hk' hwk hkq hw2 hAne hBne hzero
  exact h w hqw hw2 k hw' hk' hwk hkq A₁ A₂ hA₁fix hA₂fix hA₁ne hA₂ne hval

/-! ## §4. Case (A) of `TwRowFalse`: the `θ`-degree obstruction implies `(q-1) ∣ w`

The degree side of the argument produces, for the two-term datum, natural numbers `D := deg_θ δ₁`
and `E := deg_θ(δ₁ + G)` with `E = q·(D - w)`, `E ≤ max D q`, `w ≤ D` and the cancellation input
`E < D → D ≤ q`.  The arithmetic of those four facts is
`Commons.NumberTheory.ThetaDegObstruction.obstruction`; here we combine it with the arithmetic of the
two-term datum `w = k + (q-1)` to conclude the divisibility. -/

/-- ★★★ **Case (A) of `TwRowFalse`**: from the `θ`-degree data of the two-term rows one gets
`(q-1) ∣ w`.  For the two-term datum `w = k + (q-1)` with `1 ≤ k ≤ q-1` the alternative `w ≤ q` of
the degree obstruction forces `k = 1`. -/
theorem dvd_pred_of_deg_data {w k D E : ℕ} (hk : 2 ≤ k) (hwk : w = k + (Nat.card F - 1))
    (hkq : k ≤ Nat.card F - 1) (hq : 3 ≤ Nat.card F)
    (hE : E = Nat.card F * (D - w)) (hDe : E ≤ max D (Nat.card F))
    (hwD : w ≤ D) (hDq : E < D → D ≤ Nat.card F) :
    (Nat.card F - 1) ∣ w := by
  rcases Commons.NumberTheory.ThetaDegObstruction.obstruction hq (by omega) hE hDe hwD hDq with
    h | h
  · exact h
  · omega

/-- ★★★ **Case (A) of `TwRowFalse`, at a level `ν`.**  This is `dvd_pred_of_deg_data` in the exact
shape the level-`ν` degree computation delivers: over `A_ν = F_q[θ_ν]` the multiplier of `σ` is `q`
while the `θ_ν`-degree of `W = X - C(θ^q)` is `q^{ν+1}`, and the weight of `δ₁` is `w·q^ν`.  The
second alternative of the degree obstruction is `w·q^ν ≤ q^{ν+1}` ⟺ `w ≤ q`, which for
`w = k + (q-1)` forces `k = 1` and is excluded by `2 ≤ k`. -/
theorem dvd_pred_of_deg_data_scaled {w k ν D E : ℕ} (hk : 2 ≤ k)
    (hwk : w = k + (Nat.card F - 1)) (hkq : k ≤ Nat.card F - 1)
    (hq : 3 ≤ Nat.card F)
    (hE : E = Nat.card F * (D - w * Nat.card F ^ ν))
    (hDe : E ≤ max D (Nat.card F ^ (ν + 1)))
    (hwD : w * Nat.card F ^ ν ≤ D)
    (hDq : E < D → D ≤ Nat.card F ^ (ν + 1)) :
    (Nat.card F - 1) ∣ w := by
  have hq2 : 2 ≤ Nat.card F := by omega
  have hw0 : 0 < w * Nat.card F ^ ν :=
    Nat.mul_pos (by omega) (pow_pos (by omega) ν)
  have hQ : Nat.card F ≤ Nat.card F ^ (ν + 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < Nat.card F) (by omega : 1 ≤ ν + 1)
  rcases Commons.NumberTheory.ThetaDegObstruction.obstruction_bound (q := Nat.card F)
      (Q := Nat.card F ^ (ν + 1)) (w := w * Nat.card F ^ ν) (D := D) (E := E)
      hq hQ hw0 hE hDe hwD hDq with h | h
  · exact Commons.NumberTheory.ThetaDegObstruction.dvd_of_dvd_mul_pow (q := Nat.card F)
      (ν := ν) hq2 h
  · have hwle : w ≤ Nat.card F := by
      have h1 : Nat.card F ^ ν * w ≤ Nat.card F ^ ν * Nat.card F := by
        rw [Nat.mul_comm (Nat.card F ^ ν) w, ← pow_succ]; exact h
      exact Nat.le_of_mul_le_mul_left h1 (pow_pos (by omega) ν)
    omega

end ZagierHoffmanPositiveChar
