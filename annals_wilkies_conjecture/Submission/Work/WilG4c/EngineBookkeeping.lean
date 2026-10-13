/-
  WilG4c / EngineBookkeeping — the polynomial bookkeeping of the cell engine.

  The engine produces a chart family whose data are polynomials in the parameters `(D, r)`, and
  the `Ω`-machine has to be fed with a *format* `a`, a *degree* `b` and a *coefficient* `c` that
  dominate the pieces the engine multiplies together.  Concretely we are given

  * `b_cp`, `b_fe` — the degree polynomials of the two families that are combined (the "cover
    piece" read at `(D, 1)` and the "fibre piece" read at `(D, r)`);
  * `b_ih` — the degree polynomial of the induction hypothesis, applied at `(Df, r)` where `Df`
    is the format we are about to build;
  * `C_mw`, `C_eng`, `C_sub` — the multiplicative/additive constants of the two combination steps;
  * `c_ih` — the coefficient polynomial of the induction hypothesis.

  The lemma asserts that one can choose *once and for all* polynomials `Df`, `b` (with natural
  coefficients) and `c` (with real coefficients) so that for **every** `D, r` the three
  inequalities hold:

  * `Df` dominates `max (b_cp(D,1)) (b_fe(D,r))` and `C_mw * that + C_mw`;
  * `b` dominates `C_eng * max (Df(D,r)) (b_ih(Df(D,r), r)) + C_eng + C_sub`;
  * `c` dominates `|c_ih(Df(D,r), r, n+2, -log(ε/4))| * ((2c₀+3)(r+1)+3)^{n+1}`.

  The construction is explicit:
  * `Df = (C_mw+1)·(b_cp(·,1) + b_fe) + (C_mw+1)` (with `b_cp(·,1)` obtained by substituting the
    second variable by `1`);
  * `b  = (C_eng+1)·(Df + b_ih(Df,·)) + (C_eng+C_sub+1)`;
  * `c  = W² + 1` where `W` is `c_ih` composed with the substitution
    `(x₀,x₁,x₂,x₃) ↦ (Df, x₁, n+2, x₃ + log 4)` and multiplied by the polynomial
    `K(x₁) = ((2c₀+3)(x₁+1)+3)^{n+1}`.

  The point of `W² + 1` is that `t² + 1 ≥ |t|` for every real `t`, so a *single* polynomial `c`
  with no positivity bookkeeping dominates the absolute value; the shift by `log 4` in the fourth
  slot converts `-log ε` into `-log (ε/4)`.
-/
import Mathlib

noncomputable section
open Classical

namespace Work.WilG4c

/-- Evaluating `eval₂ C g p` at `v` is the same as evaluating `p` at the image of `v` under `g`. -/
private lemma eval_eval₂_C {R : Type*} [CommSemiring R] {σ τ : Type*}
    (g : σ → MvPolynomial τ R) (p : MvPolynomial σ R) (v : τ → R) :
    MvPolynomial.eval v (MvPolynomial.eval₂ MvPolynomial.C g p)
      = MvPolynomial.eval (fun i => MvPolynomial.eval v (g i)) p := by
  rw [MvPolynomial.eval_eval₂]
  have h : (MvPolynomial.eval v).comp (MvPolynomial.C) = RingHom.id R := by
    ext a; simp
  rw [h, MvPolynomial.eval₂_id]

/-- Embed the two-variable polynomial `Df` into four variables, reading the first two
coordinates. -/
private noncomputable def embed24 (Df : MvPolynomial (Fin 2) ℕ) : MvPolynomial (Fin 4) ℝ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun i : Fin 2 => if i = 0 then MvPolynomial.X 0 else MvPolynomial.X 1)
    (MvPolynomial.map (Nat.castRingHom ℝ) Df)

/-- Evaluation of the embedding `embed24`. -/
private lemma eval_embed24 (Df : MvPolynomial (Fin 2) ℕ) (D r : ℕ) (u w : ℝ) :
    MvPolynomial.eval ![(D:ℝ),(r:ℝ),u,w] (embed24 Df) = ((Df.eval ![D,r] : ℕ) : ℝ) := by
  unfold embed24
  rw [eval_eval₂_C]
  rw [MvPolynomial.eval_map]
  have hg : (fun i : Fin 2 => MvPolynomial.eval ![(D:ℝ),(r:ℝ),u,w]
        (if i = 0 then MvPolynomial.X 0 else MvPolynomial.X 1))
      = (fun i : Fin 2 => ((![D,r] i : ℕ) : ℝ)) := by
    funext i; fin_cases i <;> simp
  rw [hg]
  change MvPolynomial.eval₂ (Nat.castRingHom ℝ) ((Nat.castRingHom ℝ) ∘ ![D,r]) Df
    = ((MvPolynomial.eval ![D,r] Df : ℕ) : ℝ)
  rw [← MvPolynomial.eval₂_comp]
  rfl

/-- The substitution `(x₀,x₁,x₂,x₃) ↦ (Df, x₁, n+2, x₃ + log 4)` applied to `c_ih`, evaluated at
`(D, r, 1, -log ε)`.  The fourth slot witnesses the identity
`-log ε + log 4 = -log (ε/4)`. -/
private lemma eval_subst4 (n : ℕ) (Df : MvPolynomial (Fin 2) ℕ) (c_ih : MvPolynomial (Fin 4) ℝ)
    (D r : ℕ) (eps : ℝ) (heps : eps ≠ 0) :
    MvPolynomial.eval ![(D:ℝ),(r:ℝ),(1:ℝ),-Real.log eps]
      (MvPolynomial.eval₂ MvPolynomial.C
        ![embed24 Df, MvPolynomial.X 1, MvPolynomial.C ((n+2:ℕ):ℝ),
          MvPolynomial.X 3 + MvPolynomial.C (Real.log 4)] c_ih)
    = c_ih.eval ![((Df.eval ![D,r] : ℕ) : ℝ), (r:ℝ), ((n+2:ℕ):ℝ), -Real.log (eps/4)] := by
  rw [eval_eval₂_C]
  have hfun : (fun i : Fin 4 => MvPolynomial.eval ![(D:ℝ),(r:ℝ),(1:ℝ),-Real.log eps]
        (![embed24 Df, MvPolynomial.X 1, MvPolynomial.C ((n+2:ℕ):ℝ),
          MvPolynomial.X 3 + MvPolynomial.C (Real.log 4)] i))
      = ![((Df.eval ![D,r] : ℕ) : ℝ), (r:ℝ), ((n+2:ℕ):ℝ), -Real.log (eps/4)] := by
    funext i
    fin_cases i <;> simp [eval_embed24 Df D r]
    rw [Real.log_div heps (by norm_num : (4:ℝ) ≠ 0)]; ring
  rw [hfun]

/-- `t² + 1 ≥ |t|` for every real `t`. -/
private lemma sq_add_one_ge_abs (t : ℝ) : |t| ≤ t^2 + 1 := by
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (t - 1/2), sq_nonneg (t + 1/2)]

/-- The elementary `ℕ`-inequality behind the first conjunct: `(C+1)(A+B)+(C+1)` dominates both
`max A B` and `C · max A B + C`. -/
private lemma key1 (C_mw A B : ℕ) :
    max (max A B) (C_mw * max A B + C_mw) ≤ (C_mw + 1) * (A + B) + (C_mw + 1) := by
  have hmS : max A B ≤ A + B := max_le (Nat.le_add_right A B) (Nat.le_add_left B A)
  have hdecomp : (C_mw + 1) * (A + B) + (C_mw + 1)
      = C_mw * (A + B) + (A + B) + (C_mw + 1) := by ring
  have h1 : C_mw * max A B + C_mw ≤ (C_mw + 1) * (A + B) + (C_mw + 1) := by
    rw [hdecomp]
    have := Nat.mul_le_mul_left C_mw hmS
    omega
  have h2 : max A B ≤ (C_mw + 1) * (A + B) + (C_mw + 1) := by
    rw [hdecomp]; omega
  exact max_le h2 h1

/-- The elementary `ℕ`-inequality behind the second conjunct. -/
private lemma key2 (C_eng C_sub DfE bihE : ℕ) :
    C_eng * max DfE bihE + C_eng + C_sub
      ≤ (C_eng + 1) * (DfE + bihE) + (C_eng + C_sub + 1) := by
  have hmS : max DfE bihE ≤ DfE + bihE :=
    max_le (Nat.le_add_right DfE bihE) (Nat.le_add_left bihE DfE)
  have hdecomp : (C_eng + 1) * (DfE + bihE) + (C_eng + C_sub + 1)
      = C_eng * (DfE + bihE) + (DfE + bihE) + (C_eng + C_sub + 1) := by ring
  rw [hdecomp]
  have := Nat.mul_le_mul_left C_eng hmS
  omega

theorem EngineBookkeeping (n : ℕ) (c₀ : ℝ) (hc₀ : 0 ≤ c₀)
    (b_cp b_fe b_ih : MvPolynomial (Fin 2) ℕ) (C_mw C_eng C_sub : ℕ)
    (c_ih : MvPolynomial (Fin 4) ℝ) :
    ∃ (Df : MvPolynomial (Fin 2) ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r : ℕ),
        max (max (MvPolynomial.eval ![D, 1] b_cp) (MvPolynomial.eval ![D, r] b_fe))
            (C_mw * max (MvPolynomial.eval ![D, 1] b_cp) (MvPolynomial.eval ![D, r] b_fe) + C_mw)
          ≤ MvPolynomial.eval ![D, r] Df ∧
        C_eng * max (MvPolynomial.eval ![D, r] Df)
            (MvPolynomial.eval ![(MvPolynomial.eval ![D, r] Df), r] b_ih) + C_eng + C_sub
          ≤ MvPolynomial.eval ![D, r] b ∧
        ∀ (ε : ℝ), 0 < ε → ε < 1 →
          |c_ih.eval ![((MvPolynomial.eval ![D, r] Df : ℕ) : ℝ), (r : ℝ), ((n + 2 : ℕ) : ℝ),
              -Real.log (ε / 4)]| * (((2 * c₀ + 3) * (r + 1) + 3) ^ (n + 1) : ℝ)
            ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (1 : ℝ), -Real.log ε] c := by
  -- the substitution sending the second variable of `b_cp` to `1`
  let gcp : Fin 2 → MvPolynomial (Fin 2) ℕ :=
    fun i => if i = 0 then MvPolynomial.X 0 else MvPolynomial.C 1
  let bcp1 : MvPolynomial (Fin 2) ℕ := MvPolynomial.eval₂ MvPolynomial.C gcp b_cp
  -- the format dominating `b_cp(·,1)` and `b_fe`
  let Df : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.C (C_mw + 1) * (bcp1 + b_fe) + MvPolynomial.C (C_mw + 1)
  -- the substitution sending the first variable of `b_ih` to `Df`
  let gih : Fin 2 → MvPolynomial (Fin 2) ℕ :=
    fun i => if i = 0 then Df else MvPolynomial.X 1
  let bih : MvPolynomial (Fin 2) ℕ := MvPolynomial.eval₂ MvPolynomial.C gih b_ih
  -- the degree dominating `Df` and the induction hypothesis
  let b : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.C (C_eng + 1) * (Df + bih) + MvPolynomial.C (C_eng + C_sub + 1)
  refine ⟨Df, b,
    ((MvPolynomial.C (2 * c₀ + 3) * (MvPolynomial.X 1 + MvPolynomial.C 1) + MvPolynomial.C 3)
        ^ (n + 1)
      * MvPolynomial.eval₂ MvPolynomial.C
          ![embed24 Df, MvPolynomial.X 1, MvPolynomial.C ((n + 2 : ℕ) : ℝ),
            MvPolynomial.X 3 + MvPolynomial.C (Real.log 4)] c_ih) ^ 2 + MvPolynomial.C 1, ?_⟩
  intro D r
  refine ⟨?_, ?_, ?_⟩
  · -- first conjunct: `Df` dominates the two format contributions
    have hbcp1 : MvPolynomial.eval ![D, r] bcp1 = MvPolynomial.eval ![D, 1] b_cp := by
      simp only [bcp1, eval_eval₂_C]
      rw [show (fun i : Fin 2 => MvPolynomial.eval ![D, r] (gcp i)) = ![D, 1] from by
        funext i; fin_cases i <;> simp [gcp]]
    have hDf : MvPolynomial.eval ![D, r] Df
        = (C_mw + 1) * (MvPolynomial.eval ![D, 1] b_cp + MvPolynomial.eval ![D, r] b_fe)
          + (C_mw + 1) := by
      simp only [Df, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C, hbcp1]
    rw [hDf]
    exact key1 C_mw _ _
  · -- second conjunct: `b` dominates the degree of the induction hypothesis
    have hbih : MvPolynomial.eval ![D, r] bih
        = MvPolynomial.eval ![(MvPolynomial.eval ![D, r] Df), r] b_ih := by
      simp only [bih, eval_eval₂_C]
      rw [show (fun i : Fin 2 => MvPolynomial.eval ![D, r] (gih i))
            = ![(MvPolynomial.eval ![D, r] Df), r] from by
        funext i; fin_cases i <;> simp [gih]]
    have hb : MvPolynomial.eval ![D, r] b
        = (C_eng + 1) * (MvPolynomial.eval ![D, r] Df + MvPolynomial.eval ![D, r] bih)
          + (C_eng + C_sub + 1) := by
      simp only [b, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
    rw [hb, hbih]
    exact key2 C_eng C_sub _ _
  · -- third conjunct: `c = W² + 1` dominates `|c_ih ∘ substitution| · K`
    intro eps heps0 heps1
    have hCmp : MvPolynomial.eval ![(D:ℝ),(r:ℝ),(1:ℝ),-Real.log eps]
        (MvPolynomial.eval₂ MvPolynomial.C
          ![embed24 Df, MvPolynomial.X 1, MvPolynomial.C ((n+2:ℕ):ℝ),
            MvPolynomial.X 3 + MvPolynomial.C (Real.log 4)] c_ih)
        = c_ih.eval ![((MvPolynomial.eval ![D,r] Df : ℕ):ℝ), (r:ℝ), ((n+2:ℕ):ℝ),
            -Real.log (eps/4)] :=
      eval_subst4 n Df c_ih D r eps heps0.ne'
    have hK : MvPolynomial.eval ![(D:ℝ),(r:ℝ),(1:ℝ),-Real.log eps]
        ((MvPolynomial.C (2*c₀+3)*(MvPolynomial.X 1 + MvPolynomial.C 1) + MvPolynomial.C 3)
          ^(n+1))
        = (((2*c₀+3)*(r+1)+3)^(n+1) : ℝ) := by
      simp only [MvPolynomial.eval_pow, MvPolynomial.eval_add, MvPolynomial.eval_mul,
        MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.cons_val_one, Matrix.cons_val_zero]
    -- unfold the right-hand side (only there, so that the substitution `Df` on the left is
    -- left untouched, which keeps it syntactically equal to the statement of `hCmp`).
    conv_rhs => rw [MvPolynomial.eval_add, MvPolynomial.eval_pow, MvPolynomial.eval_mul,
      MvPolynomial.eval_C]
    rw [hK, hCmp]
    have hKnn : (0:ℝ) ≤ (((2*c₀+3)*(r+1)+3)^(n+1) : ℝ) := by
      apply pow_nonneg; nlinarith [hc₀, (Nat.cast_nonneg r : (0:ℝ) ≤ (r:ℝ))]
    have h1 : |c_ih.eval ![((MvPolynomial.eval ![D,r] Df : ℕ):ℝ), (r:ℝ), ((n+2:ℕ):ℝ),
          -Real.log (eps/4)]| * (((2*c₀+3)*(r+1)+3)^(n+1) : ℝ)
        = |(((2*c₀+3)*(r+1)+3)^(n+1) : ℝ)
            * c_ih.eval ![((MvPolynomial.eval ![D,r] Df : ℕ):ℝ), (r:ℝ), ((n+2:ℕ):ℝ),
              -Real.log (eps/4)]| := by
      rw [abs_mul, abs_of_nonneg hKnn, mul_comm]
    rw [h1]
    exact sq_add_one_ge_abs _

end Work.WilG4c
