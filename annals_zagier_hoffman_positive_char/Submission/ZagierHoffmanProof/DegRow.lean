import Submission.ZagierHoffmanProof.DegFrac
import Submission.ZagierHoffmanProof.TmPhi
import Submission.ZagierHoffmanProof.EndgameBound

/-!
# Reading the `(R)`-row off degreewise — the last step of obligation (A)

`PLAN.md` §«SESSION 357» §44.  `TwRows.tw_rows` produces the two rows of the two-term datum;

* **(R)** `Q·σ(Z) = σ(Q)·W^w·(Z + Y + Q·A₁·H_w)`,
* **(A)** `Y·(X^q − X) = A₂·(C(θ^q) − X^q)·Q`,

and this module extracts from **(R)** the four arithmetic facts that
`Step7Endgame.dvd_pred_of_deg_data_scaled` consumes, namely (`D := deg_ν Z − deg_ν Q`,
`E := deg_ν(Z + Y + Q·A₁·H_w) − deg_ν Q`, `q := Nat.card F`):

* `E = q · (D − w·q^ν)`, `E ≤ max D q^(ν+1)`, `w·q^ν ≤ D`, and `E < D → D ≤ q^(ν+1)`.

The sources, all read off the single identity `deg_ν` of both sides of **(R)**:

* the right side's degree is the exact value `q·deg_ν Q + w·q^(ν+1) + deg_ν(slot)`
  (`DegFrac.degPolyNu_R_side_eq`);
* the left side's degree is `deg_ν Q + q·deg_ν Z` (`degPolyNu_mul` + `degPolyNu_polyTwist_one`);
* the slot's degree is bounded by `max (deg_ν Z) (deg_ν Q + q^(ν+1))` (`degPolyNu_R_slot_le`), using
  the `(A)`-row value `deg_ν Y = deg_ν Q + q^(ν+1)` (`degPolyNu_Y_of_row`) to absorb the middle term;
* `E < D` forces `deg_ν Z <` the degree of the remaining summand, so the *cancellation* property of
  `deg_ν` (`degPolyNu_add_of_lt`) applies and gives `deg_ν(slot) = deg_ν Z`, i.e. `E = D`.

⚠ Two deviations from `PLAN.md` §44's literal statement, both necessary:

1. `Z ≠ 0` is a hypothesis.  Without it the statement is **false**: `Z = 0` forces the slot to be `0`
   (by **(R)**, since `Q·σ(Q)` and `W` are nonzero), whence `D = E = 0` and `w·q^ν ≤ D` fails.
2. `deg_ν Y = deg_ν Q + q^(ν+1)` (the `(A)`-row identity) is taken as an input rather than
   `degPolyNu_ambH_le` alone; it is what lets the middle term of the slot be absorbed, and it is
   exactly `DegFrac.degPolyNu_Y_of_row`'s conclusion.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
open Polynomial Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

/-! ## §1. Additivity and cancellation for `degPolyNu` -/

/-- `twNu ν` is additive (`twNu_mul`'s twin). -/
lemma twNu_add (ν : ℕ) (p q : Polynomial (Ambient F)) :
    twNu F ν (p + q) = twNu F ν p + twNu F ν q := by
  induction ν with
  | zero =>
      have h0 : twNu F 0 p = p := Polynomial.ext fun n => by simp [twNu_coeff]
      have h1 : twNu F 0 q = q := Polynomial.ext fun n => by simp [twNu_coeff]
      have h2 : twNu F 0 (p + q) = p + q := Polynomial.ext fun n => by simp [twNu_coeff]
      rw [h0, h1, h2]
  | succ n ih => simp only [twNu_succ, ih, polyTwist_add]

/-- ★ **The cancellation form of `degPolyNu`**: if `deg_ν q < deg_ν p` the sum has `deg_ν p`.
This is `EndgameDeg.degPoly_add_of_lt` transported along `twNu ν`. -/
theorem degPolyNu_add_of_lt {ν : ℕ} {p q : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) (hq : ∀ n, q.coeff n ∈ ambA F ν)
    (h : degPolyNu F ν q < degPolyNu F ν p) :
    degPolyNu F ν (p + q) = degPolyNu F ν p := by
  have hp0 : twNu F ν p ≠ 0 := by
    intro h0
    have hh : degPoly F (twNu F ν q) < degPoly F (twNu F ν p) := h
    rw [h0, degPoly_zero] at hh
    omega
  change degPoly F (twNu F ν (p + q)) = degPoly F (twNu F ν p)
  rw [twNu_add]
  exact degPoly_add_of_lt F (twNu F ν p) (twNu F ν q) (twNu_coeff_mem_ambA0 F hp)
    (twNu_coeff_mem_ambA0 F hq) hp0 h

/-- ★ **The `(R)`-slot's middle term**: with `deg_ν Y ≤ deg_ν Q + q^(ν+1)` and
`deg_ν H ≤ q^(ν+1)` (and `A₁` of `ambF F`-coefficients) the sum `Y + Q·A₁·H` has degree at most
`deg_ν Q + q^(ν+1)`.  This is the `hYtail` input of the cancellation case below. -/
theorem degPolyNu_add_mul_ambF_le {ν : ℕ} {Y Q A₁ H : Polynomial (Ambient F)}
    (hY : ∀ n, Y.coeff n ∈ ambA F ν) (hQ : ∀ n, Q.coeff n ∈ ambA F ν)
    (hA₁ : ∀ n, A₁.coeff n ∈ ambF F) (hH : ∀ n, H.coeff n ∈ ambA F ν)
    (hYle : degPolyNu F ν Y ≤ degPolyNu F ν Q + Nat.card F ^ (ν + 1))
    (hHle : degPolyNu F ν H ≤ Nat.card F ^ (ν + 1)) :
    degPolyNu F ν (Y + Q * A₁ * H) ≤ degPolyNu F ν Q + Nat.card F ^ (ν + 1) := by
  have hA₁ν : ∀ n, A₁.coeff n ∈ ambA F ν :=
    fun n => ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (hA₁ n))
  have hQA : ∀ n, (Q * A₁ * H).coeff n ∈ ambA F ν := fun n => coeff_mul_mem_ambA3 hQ hA₁ν hH n
  exact le_trans (degPolyNu_add_le F hY hQA)
    (max_le hYle (degPolyNu_mul_ambF_le hQ hA₁ hH hHle))

/-! ## §2. Obligation (A), final step: the four facts of `dvd_pred_of_deg_data_scaled` -/

/-- ★★★ **§41 piece 2** — reading the `(R)`-row off degreewise.  See the module docstring for the
two corrections to `PLAN.md` §44's literal statement. -/
theorem dvd_pred_of_R_row {ν w : ℕ} {Z Y Q A₁ : Polynomial (Ambient F)}
    (hZ : ∀ n, Z.coeff n ∈ ambA F ν) (hY : ∀ n, Y.coeff n ∈ ambA F ν)
    (hQ : ∀ n, Q.coeff n ∈ ambA F ν) (hA₁ : ∀ n, A₁.coeff n ∈ ambF F)
    (hQ0 : Q ≠ 0) (hσQ0 : polyTwist (q := Nat.card F) 1 Q ≠ 0) (hZ0 : Z ≠ 0)
    (hQG : degPolyNu F ν Q ≤ degPolyNu F ν (Z + Y + Q * A₁ * ambH F w))
    (hYrow : degPolyNu F ν Y = degPolyNu F ν Q + Nat.card F ^ (ν + 1))
    (hrow : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w)) :
    degPolyNu F ν (Z + Y + Q * A₁ * ambH F w) - degPolyNu F ν Q
        = Nat.card F * ((degPolyNu F ν Z - degPolyNu F ν Q) - w * Nat.card F ^ ν)
      ∧ degPolyNu F ν (Z + Y + Q * A₁ * ambH F w) - degPolyNu F ν Q
          ≤ max (degPolyNu F ν Z - degPolyNu F ν Q) (Nat.card F ^ (ν + 1))
      ∧ w * Nat.card F ^ ν ≤ degPolyNu F ν Z - degPolyNu F ν Q
      ∧ (degPolyNu F ν (Z + Y + Q * A₁ * ambH F w) - degPolyNu F ν Q
            < degPolyNu F ν Z - degPolyNu F ν Q →
          degPolyNu F ν Z - degPolyNu F ν Q ≤ Nat.card F ^ (ν + 1)) := by
  classical
  have hq2 : 2 ≤ Nat.card F := two_le_ambCard F
  set a := degPolyNu F ν Z with ha
  set b := degPolyNu F ν Q with hb
  set g := degPolyNu F ν (Z + Y + Q * A₁ * ambH F w) with hg
  -- (1) the two memberships and the nondegeneracy of the two twisted factors
  have hσZ0 : polyTwist (q := Nat.card F) 1 Z ≠ 0 := by
    refine fun h0 => hZ0 (polyTwist_one_injective F ?_)
    rw [h0, polyTwist_zero]
  have hGmem : ∀ n, (Z + Y + Q * A₁ * ambH F w).coeff n ∈ ambA F ν :=
    coeff_R_slot_mem_ambA hZ hY hQ hA₁
  have hG0 : Z + Y + Q * A₁ * ambH F w ≠ 0 := by
    intro h0
    have h1 : Q * polyTwist (q := Nat.card F) 1 Z
        = polyTwist (q := Nat.card F) 1 Q
          * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w * 0 := by
      rw [hrow, h0]
    rw [mul_zero] at h1
    exact (mul_ne_zero hQ0 hσZ0) h1
  -- (2) the degrees of the two sides of `(R)`
  have hLdeg : degPolyNu F ν (Q * polyTwist (q := Nat.card F) 1 Z) = b + Nat.card F * a := by
    rw [degPolyNu_mul (p := Q) (q := polyTwist (q := Nat.card F) 1 Z) hQ
      (polyTwist_coeff_mem_ambA F hZ 1) hQ0 hσZ0, degPolyNu_polyTwist_one hZ]
  have hRdeg : degPolyNu F ν (polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w))
      = Nat.card F * b + w * Nat.card F ^ (ν + 1) + g :=
    degPolyNu_R_side_eq hQ hGmem hσQ0 hG0
  have hdeg : b + Nat.card F * a = Nat.card F * b + w * Nat.card F ^ (ν + 1) + g := by
    rw [← hLdeg, hrow, hRdeg]
  -- (3) the slot's degree bound and the membership of its middle term
  have hA₁ν : ∀ n, A₁.coeff n ∈ ambA F ν :=
    fun n => ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (hA₁ n))
  have hQA : ∀ n, (Q * A₁ * ambH F w).coeff n ∈ ambA F ν := fun n =>
    coeff_mul_mem_ambA3 hQ hA₁ν (fun m => coeff_ambH_mem_ambA ν w m) n
  have hYtail : degPolyNu F ν (Y + Q * A₁ * ambH F w) ≤ b + Nat.card F ^ (ν + 1) :=
    degPolyNu_add_mul_ambF_le hY hQ hA₁ (coeff_ambH_mem_ambA ν w) (le_of_eq hYrow)
      (degPolyNu_ambH_le ν w)
  have hg_le : g ≤ max a (b + Nat.card F ^ (ν + 1)) := by
    have h1 := degPolyNu_R_slot_le (Z := Z) (Y := Y) (Q := Q) (A₁ := A₁) (H := ambH F w)
      hZ hY hQ hA₁ (coeff_ambH_mem_ambA ν w) (degPolyNu_ambH_le ν w)
    rw [hYrow] at h1
    refine le_trans h1 (le_of_eq ?_)
    exact max_eq_left (le_max_right a (b + Nat.card F ^ (ν + 1)))
  have hb_le_g : b ≤ g := hQG
  -- (4) the integral identity `q·(a − b) = w·q^(ν+1) + (g − b)`
  have hcast : (b : ℤ) + (Nat.card F : ℤ) * (a : ℤ)
      = (Nat.card F : ℤ) * (b : ℤ) + (w : ℤ) * ((Nat.card F : ℤ) ^ (ν + 1)) + (g : ℤ) := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hdeg
    push_cast at h
    linarith
  have hZeq : (Nat.card F : ℤ) * ((a : ℤ) - (b : ℤ))
      = (w : ℤ) * ((Nat.card F : ℤ) ^ (ν + 1)) + ((g : ℤ) - (b : ℤ)) := by
    linarith
  have hge : (0 : ℤ) ≤ (g : ℤ) - (b : ℤ) := by
    have h1 : (b : ℤ) ≤ (g : ℤ) := by exact_mod_cast hb_le_g
    linarith
  have hcZ : (0 : ℤ) < (Nat.card F : ℤ) := by
    have h1 : 0 < Nat.card F := by omega
    exact_mod_cast h1
  have hq_le : (w : ℤ) * ((Nat.card F : ℤ) ^ ν) ≤ (a : ℤ) - (b : ℤ) := by
    have hmul : (w : ℤ) * ((Nat.card F : ℤ) ^ (ν + 1))
        = (Nat.card F : ℤ) * ((w : ℤ) * ((Nat.card F : ℤ) ^ ν)) := by
      rw [pow_succ]; ring
    have h2 : (Nat.card F : ℤ) * ((w : ℤ) * ((Nat.card F : ℤ) ^ ν))
        ≤ (Nat.card F : ℤ) * ((a : ℤ) - (b : ℤ)) := by
      rw [hZeq, hmul]
      linarith
    exact le_of_mul_le_mul_left h2 hcZ
  -- (5) the ℕ bookkeeping: `b ≤ a`, `b ≤ g` and the honest subtractions
  have hb_le_a : b ≤ a := by
    have h0 : (0 : ℤ) ≤ (w : ℤ) * ((Nat.card F : ℤ) ^ ν) := by positivity
    have h1 : (0 : ℤ) ≤ (a : ℤ) - (b : ℤ) := le_trans h0 hq_le
    exact Int.ofNat_le.mp (by linarith : (b : ℤ) ≤ (a : ℤ))
  have hcast_ab : ((a - b : ℕ) : ℤ) = (a : ℤ) - (b : ℤ) := Nat.cast_sub hb_le_a
  -- (6) fact 3: `w·q^ν ≤ D`
  have hwD : w * Nat.card F ^ ν ≤ a - b := by
    have h1 : ((w * Nat.card F ^ ν : ℕ) : ℤ) ≤ ((a - b : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_pow, hcast_ab]
      exact hq_le
    exact Int.ofNat_le.mp h1
  -- (7) fact 1: `E = q·(D − w·q^ν)`
  have hEeq : g - b = Nat.card F * ((a - b) - w * Nat.card F ^ ν) := by
    have hgb : ((g - b : ℕ) : ℤ) = (g : ℤ) - (b : ℤ) := Nat.cast_sub hb_le_g
    have hsub : (((a - b) - w * Nat.card F ^ ν : ℕ) : ℤ)
        = (a : ℤ) - (b : ℤ) - (w : ℤ) * ((Nat.card F : ℤ) ^ ν) := by
      rw [Nat.cast_sub hwD, hcast_ab, Nat.cast_mul, Nat.cast_pow]
    have hkey : (g : ℤ) - (b : ℤ)
        = (Nat.card F : ℤ) * ((a : ℤ) - (b : ℤ) - (w : ℤ) * ((Nat.card F : ℤ) ^ ν)) := by
      have hmul : (w : ℤ) * ((Nat.card F : ℤ) ^ (ν + 1))
          = (Nat.card F : ℤ) * ((w : ℤ) * ((Nat.card F : ℤ) ^ ν)) := by
        rw [pow_succ]; ring
      have h := hZeq
      rw [hmul] at h
      linarith
    have h1 : ((g - b : ℕ) : ℤ)
        = ((Nat.card F * ((a - b) - w * Nat.card F ^ ν) : ℕ) : ℤ) := by
      rw [hgb, Nat.cast_mul, hsub]
      exact hkey
    exact_mod_cast h1
  -- (8) fact 2: `E ≤ max D q^(ν+1)`
  have hE_le : g - b ≤ max (a - b) (Nat.card F ^ (ν + 1)) := by
    have h1 : g - b ≤ max a (b + Nat.card F ^ (ν + 1)) - b := Nat.sub_le_sub_right hg_le b
    have h2 : max a (b + Nat.card F ^ (ν + 1)) - b ≤ max (a - b) (Nat.card F ^ (ν + 1)) := by
      rcases le_total (b + Nat.card F ^ (ν + 1)) a with h | h
      · rw [max_eq_left h]
        exact le_max_left _ _
      · rw [max_eq_right h, Nat.add_sub_cancel_left]
        exact le_max_right _ _
    exact le_trans h1 h2
  -- (9) fact 4: cancellation forces `E = D`
  have hE_lt : g - b < a - b → a - b ≤ Nat.card F ^ (ν + 1) := by
    intro hlt
    rcases lt_or_ge (b + Nat.card F ^ (ν + 1)) a with h | h
    · have h1 : degPolyNu F ν (Y + Q * A₁ * ambH F w) < degPolyNu F ν Z :=
        lt_of_le_of_lt hYtail h
      have hc := degPolyNu_add_of_lt (p := Z) (q := Y + Q * A₁ * ambH F w) hZ
        (coeff_add_mem_ambA hY hQA) h1
      rw [← add_assoc] at hc
      have hga : g = a := hc
      exact absurd hlt (by rw [hga]; exact lt_irrefl _)
    · exact le_trans (Nat.sub_le_sub_right h b) (le_of_eq (Nat.add_sub_cancel_left _ _))
  exact ⟨hEeq, hE_le, hwD, hE_lt⟩



/-! ## §3. THE MIDDLE TERM OF THE `(R)`-SLOT: `deg_ν (Y + Q·A₁·H_w) ≥ deg_ν Q`

`PLAN.md` §«SESSION 357» §44 needs `deg_ν Q ≤ deg_ν(Z + Y + Q·A₁·H_w)` (the `hQG` input of
`dvd_pred_of_R_row`).  This section proves the *half* of it that comes from the **(A)**-row, namely
`deg_ν Q ≤ deg_ν (Y + Q·A₁·H_w)` — surprisingly, with **no** hypothesis on `Z` and no hypothesis on
`w` beyond `A₁, A₂` and `Q` being nonzero:

from **(A)** and the algebraic identity

  `(Y + Q·A₁·H_w)·(X^q − X) = Q·(A₁·H_w·(X^q − X) − A₂·(X^q − C(θ^q)))`

(`tw_Y_mul_P_eq` is the input), the right-hand factor is **nonzero**: evaluating at `X = θ` kills the
`A₂`-term and leaves `A₁(θ)·H_w(θ)·(θ^q − θ) = 0`, impossible since the three factors are nonzero
(`A₁ ≠ 0` has `F_q`-coefficients and `θ` is transcendental, `H_w(θ) ∈ {1, θ^q − θ}`, and
`θ^q ≠ θ`).  Since `deg_ν(X^q − X) = 0`, multiplicativity of `deg_ν` finishes the argument. -/

/-- `H_w − (k−1)·(X − C θ)^q = X^q − X` for `w = k + (q−1)`, `2 ≤ k ≤ q−1`.  This is the identity
behind the `k = q−1` case (`PLAN.md` §4(B)) and the middle-term estimate below. -/
theorem ambH_sub_mul_pow_card {w k : ℕ} (hwk : w = k + (Nat.card F - 1))
    (hk : 2 ≤ k) (hkq : k ≤ Nat.card F - 1) :
    ambH F w - Polynomial.C ((k - 1 : ℕ) : Ambient F)
        * (Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F
      = Polynomial.X ^ Nat.card F - Polynomial.X := by
  have hq2 : 2 ≤ Nat.card F := two_le_ambCard F
  have hw : Nat.card F < w := by omega
  rw [ambH_factor_of_lt hw, X_sub_C_pow_card F (ambTheta F)]
  have hsub : w - Nat.card F = k - 1 := by omega
  rw [hsub]
  ring

/-- `(H_w)(θ) ≠ 0`: it is `1` for `w ≤ q` and `θ^q − θ` for `w > q`. -/
lemma ambH_eval_theta_ne_zero (w : ℕ) : (ambH F w).eval (ambTheta F) ≠ 0 := by
  by_cases h : w ≤ Nat.card F
  · rw [ambH_of_le F h]; simp
  · rw [ambH_of_lt (not_le.mp h)]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [sub_self, mul_zero, add_zero]
    exact sub_ne_zero.mpr (ambTheta_pow_ne_ambTheta F)

/-- ★★ **The numerator of the middle term is nonzero.**  Evaluating at `X = θ` kills the `A₂`-term
and leaves `A₁(θ)·H_w(θ)·(θ^q − θ) = 0`, impossible since all three factors are nonzero. -/
theorem num_two_ne_zero {w : ℕ} {A₁ A₂ : Polynomial (Ambient F)}
    (hA₁ : ∀ n, A₁.coeff n ∈ ambF F) (hA₁0 : A₁ ≠ 0) :
    A₁ * ambH F w * (Polynomial.X ^ Nat.card F - Polynomial.X)
      - A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) ≠ 0 := by
  intro h
  have hθ := congrArg (fun p : Polynomial (Ambient F) => p.eval (ambTheta F)) h
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_zero] at hθ
  rw [sub_self, mul_zero, sub_zero] at hθ
  rcases mul_eq_zero.mp hθ with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact eval_theta_ne_zero_of_coeff_mem_ambF F hA₁ hA₁0 h2
    · exact ambH_eval_theta_ne_zero w h2
  · exact (sub_ne_zero.mpr (ambTheta_pow_ne_ambTheta F)) h1

/-- ★★★ **The middle term of the `(R)`-slot dominates the denominator**: from the `(A)`-row alone,
`deg_ν Q ≤ deg_ν (Y + Q·A₁·H_w)`.  This is the `DG ≥ 0` half of `PLAN.md` §«SESSION 357»
§«continued 44», and it is what turns `deg_ν(δ₁ + G) ≥ 0` (the missing ordering hypothesis of
`dvd_pred_of_R_row`) into a theorem. -/
theorem degPolyNu_le_add_mul_ambH {ν w : ℕ} {Y Q A₁ A₂ : Polynomial (Ambient F)}
    (hY : ∀ n, Y.coeff n ∈ ambA F ν) (hQ : ∀ n, Q.coeff n ∈ ambA F ν)
    (hA₁ : ∀ n, A₁.coeff n ∈ ambF F) (hA₂ : ∀ n, A₂.coeff n ∈ ambF F)
    (hQ0 : Q ≠ 0) (hA₁0 : A₁ ≠ 0)
    (hrowA : Y * (Polynomial.X ^ Nat.card F - Polynomial.X)
      = A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F) * Q) :
    degPolyNu F ν Q ≤ degPolyNu F ν (Y + Q * A₁ * ambH F w) := by
  have hA₁ν : ∀ n, A₁.coeff n ∈ ambA F ν :=
    fun n => ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (hA₁ n))
  have hA₂ν : ∀ n, A₂.coeff n ∈ ambA F ν :=
    fun n => ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (hA₂ n))
  have hPmem : ∀ n,
      (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)).coeff n ∈ ambA F ν :=
    fun n => ambA_mono F (Nat.zero_le ν) (ambF_subset_ambA_zero (coeff_X_pow_sub_X_mem_ambF n))
  have hLqmem : ∀ n, (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F) :
      Polynomial (Ambient F)).coeff n ∈ ambA F ν := by
    intro n
    rw [← X_sub_C_pow_card F (ambTheta F)]
    exact coeff_pow_mem_ambA (fun m => ambA_mono F (Nat.zero_le ν)
      (coeff_X_sub_C_mem_ambA_zero ambTheta_mem_ambA_zero m)) (Nat.card F) n
  have hHmem : ∀ n, (ambH F w).coeff n ∈ ambA F ν := fun n => coeff_ambH_mem_ambA ν w n
  set N := A₁ * ambH F w * (Polynomial.X ^ Nat.card F - Polynomial.X)
    - A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) with hN
  have hNmem : ∀ n, N.coeff n ∈ ambA F ν := by
    intro n
    rw [hN, Polynomial.coeff_sub]
    exact (ambASub F ν).sub_mem (coeff_mul_mem_ambA (coeff_mul_mem_ambA hA₁ν hHmem) hPmem n)
      (coeff_mul_mem_ambA hA₂ν hLqmem n)
  have hN0 : N ≠ 0 := by
    rw [hN]; exact num_two_ne_zero hA₁ hA₁0
  have hP0 : (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)) ≠ 0 := by
    intro h
    have h1 := congrArg (fun p : Polynomial (Ambient F) => p.coeff 1) h
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_zero] at h1
    have hq1 : 1 ≠ Nat.card F := by have := two_le_ambCard F; omega
    simp [hq1] at h1
  have hYWmem : ∀ n, (Y + Q * A₁ * ambH F w).coeff n ∈ ambA F ν :=
    fun n => coeff_add_mem_ambA hY (coeff_mul_mem_ambA (coeff_mul_mem_ambA hQ hA₁ν) hHmem) n
  have hfac : (Y + Q * A₁ * ambH F w) * (Polynomial.X ^ Nat.card F - Polynomial.X)
      = Q * N := by
    rw [hN, add_mul, hrowA]; ring
  have hYW0 : Y + Q * A₁ * ambH F w ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hfac
    exact hN0 ((mul_eq_zero.mp hfac.symm).resolve_left hQ0)
  have hdeg : degPolyNu F ν (Y + Q * A₁ * ambH F w)
      + degPolyNu F ν (Polynomial.X ^ Nat.card F - Polynomial.X)
      = degPolyNu F ν Q + degPolyNu F ν N := by
    rw [← degPolyNu_mul hYWmem hPmem hYW0 hP0, ← degPolyNu_mul hQ hNmem hQ0 hN0, hfac]
  rw [degPolyNu_X_pow_sub_X, add_zero] at hdeg
  rw [hdeg]
  exact Nat.le_add_right _ _

/-! ## §4. The degenerate case `Z = 0`: the two rows are **impossible**

`PLAN.md` §«SESSION 357» §44's `dvd_pred_of_R_row` needs `Z ≠ 0` (see the module docstring): when
`Z = 0` the `(R)`-row forces the slot `Z + Y + Q·A₁·H_w` to vanish, `D = E = 0`, and the conclusion's
third conjunct fails.  The degenerate case is nevertheless impossible, by the **same**
evaluation-at-`θ` argument that proves `num_two_ne_zero`:

`Z = 0` ⟹ `Y = −Q·A₁·H_w` (from `(R)`, since `σQ ≠ 0` and `W ≠ 0`); substituting in `(A)` and
cancelling `Q` gives `A₁·H_w·(X^q − X) = A₂·(X^q − C(θ^q))`, against `num_two_ne_zero`. -/

/-- ★★ **`Z = 0` is impossible.**  This is the complement of `dvd_pred_of_R_row`'s `Z ≠ 0`
hypothesis, and it is what makes the pair of rows of the two-term datum usable without knowing
`P(some twNil) ≠ 0` in advance. -/
theorem row_false_of_Z_eq_zero {w : ℕ} {Z Y Q A₁ A₂ : Polynomial (Ambient F)}
    (hA₁ : ∀ n, A₁.coeff n ∈ ambF F) (hA₁0 : A₁ ≠ 0) (hQ0 : Q ≠ 0)
    (hrowA : Y * (Polynomial.X ^ Nat.card F - Polynomial.X)
      = A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F) * Q)
    (hrowR : Q * polyTwist (q := Nat.card F) 1 Z
      = polyTwist (q := Nat.card F) 1 Q
        * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ w
        * (Z + Y + Q * A₁ * ambH F w))
    (hZ0 : Z = 0) : False := by
  have hσQ0 : polyTwist (q := Nat.card F) 1 Q ≠ 0 := by
    refine fun h0 => hQ0 (polyTwist_one_injective F ?_)
    rw [h0, polyTwist_zero]
  -- the slot vanishes
  have hG0 : Y + Q * A₁ * ambH F w = 0 := by
    have h1 := hrowR
    rw [hZ0] at h1
    rw [polyTwist_zero, mul_zero, zero_add] at h1
    rcases mul_eq_zero.mp h1.symm with h2 | h2
    · exact absurd h2 (mul_ne_zero hσQ0 (pow_ne_zero w X_sub_C_theta_pow_ne_zero))
    · exact h2
  have hY : Y = -(Q * A₁ * ambH F w) := eq_neg_of_add_eq_zero_left hG0
  -- cancel `Q` from the (A)-row
  have hkey : A₁ * ambH F w * (Polynomial.X ^ Nat.card F - Polynomial.X)
      = A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) := by
    have h1 : (Q * A₁ * ambH F w) * (Polynomial.X ^ Nat.card F - Polynomial.X)
        = A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) * Q := by
      have h := congrArg Neg.neg hrowA
      rw [hY] at h
      rw [← neg_mul, neg_neg] at h
      rw [show -(A₂ * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F) * Q)
          = A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) * Q
          from by ring] at h
      exact h
    refine mul_left_cancel₀ hQ0 ?_
    calc Q * (A₁ * ambH F w * (Polynomial.X ^ Nat.card F - Polynomial.X))
        = (Q * A₁ * ambH F w) * (Polynomial.X ^ Nat.card F - Polynomial.X) := by ring
      _ = A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) * Q := h1
      _ = Q * (A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))) := by
          ring
  exact num_two_ne_zero hA₁ hA₁0 (sub_eq_zero.mpr hkey)

/-- ★★★ **The decomposition of the middle-term numerator**: with `w = k + (q−1)`, `2 ≤ k ≤ q−1`,

  `A₁·H_w·(X^q − X) − A₂·(X^q − C(θ^q))
     = A₁·(X^q − X)^2 + ((k−1)·A₁·(X^q − X) − A₂)·(X^q − C(θ^q))`,

i.e. `N = A₁·P² + M·L^q` with `M := C(k−1)·A₁·P − A₂`.  Since `deg_ν P = 0` and `deg_ν L^q = q^(ν+1)`,
this makes `deg_ν N` either `0` (iff `M = 0`) or `≥ q^(ν+1)`, and combined with the `(A)`-row bound
`deg_ν N = deg_ν(Y + Q·A₁·H_w) − deg_ν Q ≤ q^(ν+1)` it is **exactly two values**: `0` or `q^(ν+1)`.
This is the dichotomy that narrows `PLAN.md` §«SESSION 358» §5's residual case. -/
theorem num_two_decomp {w k : ℕ} (hwk : w = k + (Nat.card F - 1)) (hk : 2 ≤ k)
    (hkq : k ≤ Nat.card F - 1) {A₁ A₂ : Polynomial (Ambient F)} :
    A₁ * ambH F w * (Polynomial.X ^ Nat.card F - Polynomial.X)
        - A₂ * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))
      = A₁ * (Polynomial.X ^ Nat.card F - Polynomial.X) ^ 2
        + (Polynomial.C ((k - 1 : ℕ) : Ambient F) * A₁
            * (Polynomial.X ^ Nat.card F - Polynomial.X) - A₂)
          * (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) := by
  have hH : ambH F w = (Polynomial.X ^ Nat.card F - Polynomial.X)
      + Polynomial.C ((k - 1 : ℕ) : Ambient F)
        * (Polynomial.X - Polynomial.C (ambTheta F)) ^ Nat.card F := by
    have := ambH_sub_mul_pow_card (F := F) hwk hk hkq
    rw [← this]; ring
  rw [hH, X_sub_C_pow_card F (ambTheta F)]
  ring

end ZagierHoffmanPositiveChar
