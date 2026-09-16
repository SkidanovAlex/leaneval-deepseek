import Submission.ZagierHoffmanProof.EndgameRow
import Submission.ZagierHoffmanProof.Endgame2

/-!
# The two explicit rows of the two-term datum

`Endgame2.tw_second_relation` produces a polynomial row vector `P` with

  `∀ t ∈ tmI S,  tmB F w S cf P (some t) = 0`,

where `S = twDatum = {(w), (k, q-1)}` and `tmI S = {[], [(k,1)]}` (`Endgame2.tmI_twDatum`).
This file expands those two equations into **the two explicit polynomial rows of Dac's §6.3
endgame** (with `Q := P none`, `Z := P (some [])`, `Y := P (some [(k,1)])`, `W := X - C(θ^q)`,
`A₁ := cf (twS1)`, `A₂ := cf (twS2)`, `H_w := ambH F w`):

* ★ **(R)** `Q·σ(Z) = σ(Q)·W^w·(Q·A₁·H_w + Z + Y)`   (Dac (6.3)),
* ★ **(A)** `Q·σ(Y) = σ(Q)·W^{q-1}·(Y + Q·A₂)`         (Dac (6.4)),

the first being `Endgame2.tmB_nil_row`, the second computed here.  The content is the two elementary
`tmA`/`tmV` evaluations at the `(k,1)`-column:

* `tmA q θ w [] [(k,1)] = 0`  and  `tmA q θ w [(k,1)] [(k,1)] = W^(w-k)`;
* `tmV q θ w (twDatum …) cf [(k,1)] = A₂·H_{q-1}·W^{w-k} = A₂·W^{w-k}`  (`H_{q-1} = 1`).

⚠ `tmI S` consists of *proper* prefixes, so the column `[(k,1)]` has no children and its only parent
is `twS2`; both facts are used above.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
open Polynomial PowerSeries Finset Matrix
open scoped WithZero Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The elementary `tmA` values -/

/-- `tmA` at the empty row and a nonempty column vanishes. -/
lemma tmA_nil_of_ne_nil (q : ℕ) (θ : Ambient F) (w : ℕ)
    {t : List (ℕ × Polynomial (Ambient F))} (ht : t ≠ []) : tmA q θ w [] t = 0 := by
  classical
  rw [tmA, if_neg, if_neg]
  · exact ht
  · simpa using ht

/-- ★ `tmA` at the `() = (x)`-column is the diagonal entry `W^(w - w(x))`. -/
lemma tmA_singleton_self (q : ℕ) (θ : Ambient F) (w : ℕ)
    (x : ℕ × Polynomial (Ambient F)) :
    tmA q θ w [x] [x] = (Polynomial.X - Polynomial.C (θ ^ q)) ^ (w - x.1) := by
  classical
  rw [tmA_diag]
  simp [tmWeight]

/-! ## §2. The `tmV` and `tmA` evaluations at the `(k,1)`-column -/

/-- ★ **`tmV` at the `(k,1)`-column.**  The only parent of `[(k,1)]` among the datum's tuples is
`twS2 = [(k,H_k), (q-1,H_{q-1})]`, whose last entry is `H_{q-1} = 1`. -/
lemma tmV_k_tw {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1)
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)) :
    tmV (Nat.card F) (ambTheta F) w (twDatum F w k hw hk) cf
        [(k, (1 : Polynomial (Ambient F)))]
      = cf (tupleListHP F (twS2 F k hk))
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (w - k) := by
  classical
  have hne : tupleListHP F (twS1 w hw) ≠ tupleListHP F (twS2 F k hk) := by
    rw [twS1_list, twS2_list]; simp
  have hk1 : ambH F k = 1 := ambH_of_le F (by have := two_le_ambCard F; omega)
  have hq1 : ambH F (Nat.card F - 1) = 1 := ambH_of_le F (by omega)
  rw [tmV, twDatum, Finset.sum_pair hne]
  rw [if_neg (by rw [twS1_list]; simp), if_pos (by rw [twS2_list]; simp [hk1])]
  rw [tmWeight_twK]
  simp only [tmQ, twS2_list, List.getLastD_cons, List.getLastD_nil]
  rw [hq1, mul_one]
  ring

/-- ★ **The `tmA`-sum at the `(k,1)`-column**: only the diagonal term survives. -/
lemma sum_tmA_k_tw {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1)
    (P : Option ↥(tmI (twDatum F w k hw hk)) → Polynomial (Ambient F)) :
    (∑ t : ↥(tmI (twDatum F w k hw hk)),
        P (some t) * tmA (Nat.card F) (ambTheta F) w t.1
          [(k, (1 : Polynomial (Ambient F)))])
      = P (some (twK F w k hw hk hkq))
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (w - k) := by
  rw [univ_twDatum F w k hw hk hkq,
    Finset.sum_pair (twNil_ne_twK F w k hw hk hkq)]
  rw [twNil_val, twK_val, tmA_nil_of_ne_nil F _ _ _ (by simp), tmA_singleton_self]
  simp

/-! ## §3. The `(k)`-row of `tmB` -/

/-- ★ **The row of `tmB` at the `(k,1)`-column of the two-term datum** — Dac's (6.4) in the form the
integrality argument consumes.  Uses `w = k + (q-1)`. -/
theorem tmB_k_row {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1)
    (hwk : w = k + (Nat.card F - 1))
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (P : Option ↥(tmI (twDatum F w k hw hk)) → Polynomial (Ambient F)) :
    tmB F w (twDatum F w k hw hk) cf P (some (twK F w k hw hk hkq))
      = P none * polyTwist (q := Nat.card F) 1 (P (some (twK F w k hw hk hkq)))
        - polyTwist (q := Nat.card F) 1 (P none)
          * ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
              * (P (some (twK F w k hw hk hkq))
                 + P none * cf (tupleListHP F (twS2 F k hk)))) := by
  classical
  have h := tmB_col_eq (F := F) (w := w) (S := twDatum F w k hw hk) (cf := cf) (P := P)
    (t' := [(k, (1 : Polynomial (Ambient F)))]) (twK F w k hw hk hkq).2
  have hs : (some (twK F w k hw hk hkq) : Option ↥(tmI (twDatum F w k hw hk)))
      = some ⟨[(k, (1 : Polynomial (Ambient F)))], (twK F w k hw hk hkq).2⟩ := rfl
  rw [hs, h, tmV_k_tw F hw hk hkq cf, sum_tmA_k_tw F hw hk hkq P]
  have hsub : w - k = Nat.card F - 1 := by omega
  rw [← hsub, hs]
  ring

/-! ## §4. The two rows, from the vanishing of `tmB` -/

/-- ★★★ **The two explicit rows of the two-term datum**, from the vanishing of `tmB` on `tmI`.
With `Q := P none`, `Z := P (some twNil)`, `Y := P (some twK)`:

* **(R)** `Q·σ(Z) = σ(Q)·W^w·(Q·A₁·H_w + Z + Y)`,
* **(A)** `Q·σ(Y) = σ(Q)·W^{q-1}·(Y + Q·A₂)`. -/
theorem tw_rows_of {w k : ℕ} (hw : 0 < w) (hk : 0 < k) (hkq : k ≤ Nat.card F - 1)
    (hwk : w = k + (Nat.card F - 1))
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    {P : Option ↥(tmI (twDatum F w k hw hk)) → Polynomial (Ambient F)}
    (hB : ∀ t : ↥(tmI (twDatum F w k hw hk)),
      tmB F w (twDatum F w k hw hk) cf P (some t) = 0) :
    (P none * polyTwist (q := Nat.card F) 1 (P (some (twNil F w k hw hk hkq)))
        = polyTwist (q := Nat.card F) 1 (P none)
          * ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
              * (P none * (cf (tupleListHP F (twS1 w hw)) * ambH F w)
                 + P (some (twNil F w k hw hk hkq))
                 + P (some (twK F w k hw hk hkq)))))
      ∧ (P none * polyTwist (q := Nat.card F) 1 (P (some (twK F w k hw hk hkq)))
        = polyTwist (q := Nat.card F) 1 (P none)
          * ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
              * (P (some (twK F w k hw hk hkq))
                 + P none * cf (tupleListHP F (twS2 F k hk))))) := by
  classical
  have hnil := hB (twNil F w k hw hk hkq)
  rw [tmB_nil_row F hw hk hkq cf P] at hnil
  have hkrow := hB (twK F w k hw hk hkq)
  rw [tmB_k_row F hw hk hkq hwk cf P] at hkrow
  exact ⟨sub_eq_zero.mp hnil, sub_eq_zero.mp hkrow⟩

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §5. The rows for the concrete datum `twCf` -/

/-- ★★★ **The two explicit rows of the two-term datum, for the coefficient function `twCf`.**  This is
`Endgame2.tw_second_relation` (the ABP second relation) with its conclusion expanded by `tmB_nil_row`
and `tmB_k_row`.  With `Q := P none`, `Z := P (some [])`, `Y := P (some [(k,1)])`, `W := X - C(θ^q)`:

* **(R)** `Q·σ(Z) = σ(Q)·W^w·(Q·A₁·H_w + Z + Y)`,
* **(A)** `Q·σ(Y) = σ(Q)·W^{q-1}·(Y + Q·A₂)`.

(`Q ≠ 0` and the `ambKperf`-membership of `P`'s coefficients are retained because the integrality
argument consumes them.) -/
theorem tw_rows {w k : ℕ} (hq : 3 ≤ Nat.card F) (hw : 0 < w) (hk : 0 < k)
    (hwk : w = k + (Nat.card F - 1)) (hkq : k ≤ Nat.card F - 1)
    (A₁ A₂ : Polynomial (Ambient F))
    (hA₁inv : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((A₁ : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((A₁ : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hA₂inv : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((A₂ : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((A₂ : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hval : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (twDatum F w k hw hk)
        (twCf F hw hk A₁ A₂) ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F)
      + (0 : Polynomial (Ambient F)).eval (ambTheta F) = 0) :
    ∃ P : Option ↥(tmI (twDatum F w k hw hk)) → Polynomial (Ambient F),
      (∀ j m, (P j).coeff m ∈ ambKperf F) ∧
      P none ≠ 0 ∧
      (P none * polyTwist (q := Nat.card F) 1 (P (some (twNil F w k hw hk hkq)))
        = polyTwist (q := Nat.card F) 1 (P none)
          * ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
              * (P none * (A₁ * ambH F w)
                 + P (some (twNil F w k hw hk hkq))
                 + P (some (twK F w k hw hk hkq))))) ∧
      (P none * polyTwist (q := Nat.card F) 1 (P (some (twK F w k hw hk hkq)))
        = polyTwist (q := Nat.card F) 1 (P none)
          * ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ (Nat.card F - 1)
              * (P (some (twK F w k hw hk hkq)) + P none * A₂))) := by
  obtain ⟨P, -, -, hPmem, hP0, hB⟩ :=
    tw_second_relation F hq hw hk hwk hkq A₁ A₂ hA₁inv hA₂inv hval
  obtain ⟨hR, hA⟩ := tw_rows_of F hw hk hkq hwk hB
  refine ⟨P, hPmem, hP0, ?_, ?_⟩
  · rw [hR, twCf_mem₁]
  · rw [hA, twCf_mem₂]

/-- The `hA₂` input of the `(k)`-row factorisation, from the Frobenius-invariance hypothesis. -/
lemma coeff_mem_ambF_of_twA₂ {A₂ : Polynomial (Ambient F)}
    (hA₂inv : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((A₂ : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((A₂ : Polynomial (Ambient F)) : PowerSeries (Ambient F))) :
    ∀ n, A₂.coeff n ∈ ambF F := fun n => by
  have h := coeff_mem_ambF_of_frobTwist_one_eq (F := F)
    (f := (A₂ : PowerSeries (Ambient F))) hA₂inv n
  simpa only [Polynomial.coeff_coe] using h

/-- ★★★ **Dac's (6.4), solved, for the two-term datum**: `Y·(X^q - X) = -A₂·(X-θ)^q·Q`, i.e.
`δ₂ := Y/Q` satisfies `δ₂·(X^q-X) = -A₂·(X-θ)^q`. -/
theorem tw_Y_mul_P_eq {w k : ℕ} (hq : 3 ≤ Nat.card F) (hw : 0 < w) (hk : 0 < k)
    (hwk : w = k + (Nat.card F - 1)) (hkq : k ≤ Nat.card F - 1)
    (A₁ A₂ : Polynomial (Ambient F))
    (hA₁inv : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((A₁ : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((A₁ : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hA₂inv : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((A₂ : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((A₂ : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hval : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (twDatum F w k hw hk)
        (twCf F hw hk A₁ A₂) ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F)
      + (0 : Polynomial (Ambient F)).eval (ambTheta F) = 0) :
    ∃ (P : Option ↥(tmI (twDatum F w k hw hk)) → Polynomial (Ambient F)) (Z : Polynomial (Ambient F)),
      (∀ j m, (P j).coeff m ∈ ambKperf F) ∧
      P none ≠ 0 ∧
      Z = P (some (twNil F w k hw hk hkq)) ∧
      P (some (twK F w k hw hk hkq)) * (Polynomial.X ^ Nat.card F - Polynomial.X)
        = A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F)
            * P none ∧
      (P none * polyTwist (q := Nat.card F) 1 Z
        = polyTwist (q := Nat.card F) 1 (P none)
          * ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
              * (P none * (A₁ * ambH F w)
                 + Z + P (some (twK F w k hw hk hkq))))) := by
  obtain ⟨P, hPmem, hP0, hR, hA⟩ := tw_rows F hq hw hk hwk hkq A₁ A₂ hA₁inv hA₂inv hval
  refine ⟨P, P (some (twNil F w k hw hk hkq)), hPmem, hP0, rfl, ?_, hR⟩
  exact tw_k_row_factor F hP0 (coeff_mem_ambF_of_twA₂ F hA₂inv) (by rw [hA]; ring)

end ZagierHoffmanPositiveChar
