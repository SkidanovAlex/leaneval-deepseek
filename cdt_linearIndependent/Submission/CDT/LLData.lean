import Mathlib

/-!
# The C-side pushforward data of Calegari--Dimitrov--Tang

(arXiv:2408.15403, section "Products of two logarithms")

The paper's order-two operator `M = P2 ∂² + P1 ∂ + P0` (eq. `ODE`) annihilates
`P_A(x) = A(a,x) ⋆ A(b,x)`.  Under the degree-two map `π : x ↦ y = x²/(x-1)`
(so `y = x + x/(x-1)`, with the involution `w(x) = x/(x-1)`, `π∘w = π`), the
*pushforward* `LL` of `M` is the order-four operator

  `LL = Σ_{i=0}^4 c_i(y) dⁱ/dyⁱ`   with
  `c₀ = R₁₂`, `c₁ = R₁₆,ᴬ`, `c₂ = y R₁₆,ᴮ`, `c₃ = y²(y-4) R₁₅`,
  `c₄ = (y-4)² y³ R₄(y) R₁₀(y)`                                    (coefficientsofL)

and `LL` satisfies `LL(G_A) = 0` for `G_A(y) = P_A(x) + P_A(x/(x-1))`.

The polynomials below are the paper-normalised ones: `R₄`, `R₁₀` are the
paper's explicit displays, and `c₀, c₁, c₂` were computed by two independent
routes (a power-series kernel computation and the pushforward D-module
`K[∂_x]/(M)`), interpolated in `(a,b)` with all `(a,b)`-coefficients of total
degree ≤ 12; see `Scratch/lemma14/cside/README.md`.  The tables live in
`Submission/CDT/LLOperator.lean` (not imported here, to keep the build light).

Variables: `X 0 = a`, `X 1 = b`, `X 2 = y`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

open MvPolynomial

namespace Submission.CDT.LL

/-- Polynomials in `a, b, y` (`X 0 = a`, `X 1 = b`, `X 2 = y`). -/
abbrev MP : Type := MvPolynomial (Fin 3) ℚ

/-- The monomial `c · a^da · b^db · y^dy`. -/
noncomputable def mono (da db dy : ℕ) (c : MP) : MP := c * X 0 ^ da * X 1 ^ db * X 2 ^ dy

/-- Sum of a table of monomials. -/
noncomputable def ms (l : List (ℕ × ℕ × ℕ × MP)) : MP :=
  (l.map (fun t => mono t.1 t.2.1 t.2.2.1 t.2.2.2)).sum

theorem ms_cons (t : ℕ × ℕ × ℕ × MP) (l : List (ℕ × ℕ × ℕ × MP)) :
    ms (t :: l) = mono t.1 t.2.1 t.2.2.1 t.2.2.2 + ms l := rfl

theorem ms_nil : ms ([] : List (ℕ × ℕ × ℕ × MP)) = 0 := rfl

noncomputable def R4L : List (ℕ × ℕ × ℕ × MP) :=
  [
    (0, 0, 0, (1 : MP)), (0, 0, 1, (4 : MP)), (0, 2, 1, (-8 : MP)), (1, 1, 1, (-4 : MP)),
    (2, 0, 1, (-8 : MP)), (2, 2, 1, (16 : MP)), (0, 0, 2, (4 : MP)), (0, 2, 2, (-12 : MP)),
    (0, 4, 2, (16 : MP)), (1, 1, 2, (20 : MP)), (1, 3, 2, (-16 : MP)), (2, 0, 2, (-12 : MP)),
    (3, 1, 2, (-16 : MP)), (4, 0, 2, (16 : MP)), (0, 2, 3, (-8 : MP)), (1, 1, 3, (16 : MP)),
    (1, 3, 3, (-16 : MP)), (2, 0, 3, (-8 : MP)), (2, 2, 3, (32 : MP)), (3, 1, 3, (-16 : MP)),
    (0, 2, 4, (4 : MP)), (1, 1, 4, (-8 : MP)), (2, 0, 4, (4 : MP)),
  ]

noncomputable def R10L : List (ℕ × ℕ × ℕ × MP) :=
  [
    (2, 2, 0, (4 : MP)), (0, 0, 1, (9 : MP)), (0, 2, 1, (-27 : MP)), (1, 1, 1, (-102 : MP)),
    (1, 3, 1, (144 : MP)), (2, 0, 1, (-27 : MP)), (2, 2, 1, (207 : MP)), (2, 4, 1, (-128 : MP)),
    (3, 1, 1, (144 : MP)), (3, 3, 1, (-160 : MP)), (4, 2, 1, (-128 : MP)), (0, 0, 2, (64 : MP)),
    (0, 2, 2, (-93 : MP)), (0, 4, 2, (228 : MP)), (1, 1, 2, (-284 : MP)), (1, 3, 2, (740 : MP)),
    (1, 5, 2, (-992 : MP)), (2, 0, 2, (-93 : MP)), (2, 2, 2, (-818 : MP)), (2, 4, 2, (-16 : MP)),
    (3, 1, 2, (740 : MP)), (3, 3, 2, (1208 : MP)), (4, 0, 2, (228 : MP)), (4, 2, 2, (-16 : MP)),
    (4, 4, 2, (64 : MP)), (5, 1, 2, (-992 : MP)), (0, 0, 3, (164 : MP)), (0, 2, 3, (-132 : MP)),
    (0, 4, 3, (-804 : MP)), (0, 6, 3, (432 : MP)), (1, 1, 3, (-100 : MP)), (1, 3, 3, (1218 : MP)),
    (1, 5, 3, (2360 : MP)), (1, 7, 3, (-1536 : MP)), (2, 0, 3, (-132 : MP)), (2, 2, 3, (-1108 : MP)),
    (2, 4, 3, (-856 : MP)), (2, 6, 3, (1856 : MP)), (3, 1, 3, (1218 : MP)), (3, 3, 3, (-3120 : MP)),
    (3, 5, 3, (-448 : MP)), (4, 0, 3, (-804 : MP)), (4, 2, 3, (-856 : MP)), (4, 4, 3, (-16 : MP)),
    (5, 1, 3, (2360 : MP)), (5, 3, 3, (-448 : MP)), (6, 0, 3, (432 : MP)), (6, 2, 3, (1856 : MP)),
    (7, 1, 3, (-1536 : MP)), (0, 0, 4, (168 : MP)), (0, 2, 4, (-18 : MP)), (0, 4, 4, (-1476 : MP)),
    (0, 6, 4, (432 : MP)), (1, 1, 4, (-108 : MP)), (1, 3, 4, (-840 : MP)), (1, 5, 4, (688 : MP)),
    (1, 7, 4, (384 : MP)), (2, 0, 4, (-18 : MP)), (2, 2, 4, (4384 : MP)), (2, 4, 4, (-8864 : MP)),
    (2, 6, 4, (4384 : MP)), (3, 1, 4, (-840 : MP)), (3, 3, 4, (15744 : MP)), (3, 5, 4, (-11744 : MP)),
    (4, 0, 4, (-1476 : MP)), (4, 2, 4, (-8864 : MP)), (4, 4, 4, (13920 : MP)), (5, 1, 4, (688 : MP)),
    (5, 3, 4, (-11744 : MP)), (6, 0, 4, (432 : MP)), (6, 2, 4, (4384 : MP)), (7, 1, 4, (384 : MP)),
    (0, 0, 5, (32 : MP)), (0, 2, 5, (180 : MP)), (0, 4, 5, (2467 : MP)), (0, 6, 5, (792 : MP)),
    (0, 8, 5, (-720 : MP)), (1, 1, 5, (-424 : MP)), (1, 3, 5, (-4228 : MP)), (1, 5, 5, (440 : MP)),
    (1, 7, 5, (1824 : MP)), (2, 0, 5, (180 : MP)), (2, 2, 5, (3554 : MP)), (2, 4, 5, (-15928 : MP)),
    (2, 6, 5, (5104 : MP)), (3, 1, 5, (-4228 : MP)), (3, 3, 5, (29392 : MP)), (3, 5, 5, (-25088 : MP)),
    (4, 0, 5, (2467 : MP)), (4, 2, 5, (-15928 : MP)), (4, 4, 5, (37760 : MP)), (5, 1, 5, (440 : MP)),
    (5, 3, 5, (-25088 : MP)), (6, 0, 5, (792 : MP)), (6, 2, 5, (5104 : MP)), (7, 1, 5, (1824 : MP)),
    (8, 0, 5, (-720 : MP)), (0, 0, 6, (-32 : MP)), (0, 2, 6, (-336 : MP)), (0, 4, 6, (258 : MP)),
    (0, 6, 6, (-3840 : MP)), (0, 8, 6, (480 : MP)), (1, 1, 6, (736 : MP)), (1, 3, 6, (1064 : MP)),
    (1, 5, 6, (6680 : MP)), (1, 7, 6, (-4320 : MP)), (2, 0, 6, (-336 : MP)), (2, 2, 6, (-2676 : MP)),
    (2, 4, 6, (6976 : MP)), (2, 6, 6, (10688 : MP)), (3, 1, 6, (1064 : MP)), (3, 3, 6, (-19632 : MP)),
    (3, 5, 6, (-12256 : MP)), (4, 0, 6, (258 : MP)), (4, 2, 6, (6976 : MP)), (4, 4, 6, (10816 : MP)),
    (5, 1, 6, (6680 : MP)), (5, 3, 6, (-12256 : MP)), (6, 0, 6, (-3840 : MP)), (6, 2, 6, (10688 : MP)),
    (7, 1, 6, (-4320 : MP)), (8, 0, 6, (480 : MP)), (0, 2, 7, (-576 : MP)), (0, 4, 7, (-1392 : MP)),
    (0, 6, 7, (4368 : MP)), (1, 1, 7, (1152 : MP)), (1, 3, 7, (5312 : MP)), (1, 5, 7, (-12848 : MP)),
    (1, 7, 7, (576 : MP)), (2, 0, 7, (-576 : MP)), (2, 2, 7, (-7840 : MP)), (2, 4, 7, (12912 : MP)),
    (2, 6, 7, (-1104 : MP)), (3, 1, 7, (5312 : MP)), (3, 3, 7, (-8864 : MP)), (3, 5, 7, (-768 : MP)),
    (4, 0, 7, (-1392 : MP)), (4, 2, 7, (12912 : MP)), (4, 4, 7, (2592 : MP)), (5, 1, 7, (-12848 : MP)),
    (5, 3, 7, (-768 : MP)), (6, 0, 7, (4368 : MP)), (6, 2, 7, (-1104 : MP)), (7, 1, 7, (576 : MP)),
    (0, 2, 8, (192 : MP)), (0, 4, 8, (168 : MP)), (0, 6, 8, (-960 : MP)), (1, 1, 8, (-384 : MP)),
    (1, 3, 8, (-864 : MP)), (1, 5, 8, (1568 : MP)), (2, 0, 8, (192 : MP)), (2, 2, 8, (1392 : MP)),
    (2, 4, 8, (2368 : MP)), (2, 6, 8, (-288 : MP)), (3, 1, 8, (-864 : MP)), (3, 3, 8, (-5952 : MP)),
    (3, 5, 8, (1152 : MP)), (4, 0, 8, (168 : MP)), (4, 2, 8, (2368 : MP)), (4, 4, 8, (-1728 : MP)),
    (5, 1, 8, (1568 : MP)), (5, 3, 8, (1152 : MP)), (6, 0, 8, (-960 : MP)), (6, 2, 8, (-288 : MP)),
    (0, 4, 9, (160 : MP)), (1, 3, 9, (-640 : MP)), (1, 5, 9, (448 : MP)), (2, 2, 9, (960 : MP)),
    (2, 4, 9, (-1792 : MP)), (3, 1, 9, (-640 : MP)), (3, 3, 9, (2688 : MP)), (4, 0, 9, (160 : MP)),
    (4, 2, 9, (-1792 : MP)), (5, 1, 9, (448 : MP)), (0, 4, 10, (-32 : MP)), (1, 3, 10, (128 : MP)),
    (2, 2, 10, (-192 : MP)), (3, 1, 10, (128 : MP)), (4, 0, 10, (-32 : MP)),
  ]


noncomputable def R4 : MP := ms R4L
noncomputable def R10 : MP := ms R10L

/-- `(X-1)⁴ · P(X²/(X-1))` for `P` a polynomial of degree `≤ 4` in `y`. -/
noncomputable def subm (l : List (ℕ × ℕ × ℕ × MP)) : MP :=
  (l.map (fun t => mono t.1 t.2.1 (2 * t.2.2.1) t.2.2.2 * (X 2 - 1) ^ (4 - t.2.2.1))).sum

/-- `(X-1)⁴ · P(X/(X-1))` for `P` a polynomial of degree `≤ 4` in `X`. -/
noncomputable def mob (l : List (ℕ × ℕ × ℕ × MP)) : MP :=
  (l.map (fun t => mono t.1 t.2.1 t.2.2.1 t.2.2.2 * (X 2 - 1) ^ (4 - t.2.2.1))).sum

/-- The quartic `Q₄ = 1 - 4abX + (4a²+4b²-2)X² - 4abX³ + X⁴` of (ODE). -/
noncomputable def Q4L : List (ℕ × ℕ × ℕ × MP) :=
  [(0,0,0,(1:MP)), (1,1,1,(-4:MP)), (2,0,2,(4:MP)), (0,2,2,(4:MP)), (0,0,2,(-2:MP)),
   (1,1,3,(-4:MP)), (0,0,4,(1:MP))]

noncomputable def Q4 : MP := ms Q4L

/-- `(X-1)⁴ R₄(X²/(X-1))`, cleared of denominators. -/
noncomputable def R4pull : MP := subm R4L

/-- `(X-1)⁴ Q₄(X/(X-1))`, cleared of denominators. -/
noncomputable def Q4sig : MP := mob Q4L

/-- The paper's remark after (coefficientsofL): `(1-x)⁴ R₄(x + x/(x-1))` has
`(a ± √(a²-1))(b ± √(b²-1))` as four of its eight roots, together with their
images under `w(x) = x/(x-1)`; equivalently
`(X-1)⁴ R₄(y(X)) = Q₄(X) · Q₄^w(X)`, since the four roots of `Q₄` are exactly
`(a ± √(a²-1))(b ± √(b²-1))`.  In particular the roots of `R₄(y)` are the
singularities `y_{a^{±},b^{±}}` of `LL`. -/
theorem R4_symmetrisation : R4pull = Q4 * Q4sig := by
  unfold R4pull Q4sig Q4 ms subm mob mono R4L Q4L
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- The numerator of `c₃/c₄ = 3/(y-4) + 5/y + 3R₄'/R₄ - R₁₀'/R₁₀`. -/
noncomputable def LambdaNum : MP :=
  3 * X 2 * R4 * R10 + 5 * (X 2 - 4) * R4 * R10
    + 3 * X 2 * (X 2 - 4) * (MvPolynomial.pderiv 2 R4) * R10
    - X 2 * (X 2 - 4) * R4 * (MvPolynomial.pderiv 2 R10)

/-- The paper's `c₃ = y²(y-4) R₁₅`. -/
noncomputable def c3 : MP := (X 2 - 4) * X 2 ^ 2 * LambdaNum

/-- The paper's `c₄ = (y-4)² y³ R₄ R₁₀`. -/
noncomputable def c4 : MP := (X 2 - 4) ^ 2 * X 2 ^ 3 * R4 * R10

theorem c3_eq : c3 = (X 2 - 4) * X 2 ^ 2 * LambdaNum := rfl

theorem c4_eq : c4 = (X 2 - 4) ^ 2 * X 2 ^ 3 * R4 * R10 := rfl

/-- The paper's log-derivative identity
`c₃/c₄ = 3/(y-4) + 5/y + 3R₄'/R₄ - R₁₀'/R₁₀`, cleared of denominators. -/
theorem c3_mul_eq_c4_mul : c3 * (X 2 * (X 2 - 4) * R4 * R10) = c4 * LambdaNum := by
  rw [c3_eq, c4_eq]; ring

/-- `y²` divides `c₃` (the paper's `c₃ = y²(y-4) R₁₅`). -/
theorem X2_sq_dvd_c3 : X 2 ^ 2 ∣ c3 :=
  ⟨(X 2 - 4) * LambdaNum, by rw [c3_eq]; ring⟩

/-- `(y-4)²` divides `c₄` (the paper's `c₄ = (y-4)² y³ R₄ R₁₀`). -/
theorem X2_sub4_sq_dvd_c4 : (X 2 - 4) ^ 2 ∣ c4 :=
  ⟨X 2 ^ 3 * R4 * R10, by rw [c4_eq]; ring⟩

/-- `y³ ∣ c₄`. -/
theorem X2_pow3_dvd_c4 : X 2 ^ 3 ∣ c4 :=
  ⟨(X 2 - 4) ^ 2 * R4 * R10, by rw [c4_eq]; ring⟩

/-! ### The residues of `Λ = c₃/c₄` at the two ramification points -/

/-- The residue of `Λ = c₃/c₄` at `y = 0` is `5`, i.e.
`c₃/c₄ - 5/y` is regular at `y = 0` (the paper's
`c₃/c₄ = 3/(y-4) + 5/y + 3R₄'/R₄ - R₁₀'/R₁₀`).  Here
`c₃/c₄ = Λnum/((y-4)·y·R₄·R₁₀)`, so clearing the denominators this is
`y ∣ Λnum - 5(y-4)R₄R₁₀`. -/
theorem X2_dvd_LambdaNum_sub_five :
    X 2 ∣ LambdaNum - 5 * (X 2 - 4) * R4 * R10 :=
  ⟨3 * R4 * R10 + 3 * (X 2 - 4) * MvPolynomial.pderiv 2 R4 * R10
      - (X 2 - 4) * R4 * MvPolynomial.pderiv 2 R10,
   by unfold LambdaNum; ring⟩

/-- The residue of `Λ = c₃/c₄` at `y = 4` is `3`, i.e. `y - 4 ∣ Λnum - 3yR₄R₁₀`. -/
theorem X2_sub4_dvd_LambdaNum_sub_three :
    (X 2 - 4) ∣ LambdaNum - 3 * X 2 * R4 * R10 :=
  ⟨5 * R4 * R10 + 3 * X 2 * MvPolynomial.pderiv 2 R4 * R10
      - X 2 * R4 * MvPolynomial.pderiv 2 R10,
   by unfold LambdaNum; ring⟩

/-- Modulo `R₄`, `Λnum ≡ 3y(y-4)R₄'R₁₀`; hence at a simple root `β` of `R₄` the
*residue* of `Λ = c₃/c₄ = Λnum/((y-4)yR₄R₁₀)` is
`3β(β-4)R₄'(β)R₁₀(β) / ((β-4)βR₄'(β)R₁₀(β)) = 3`. -/
theorem R4_dvd_LambdaNum_sub :
    R4 ∣ LambdaNum - 3 * X 2 * (X 2 - 4) * MvPolynomial.pderiv 2 R4 * R10 :=
  ⟨3 * X 2 * R10 + 5 * (X 2 - 4) * R10 - X 2 * (X 2 - 4) * MvPolynomial.pderiv 2 R10,
   by unfold LambdaNum; ring⟩

/-- Modulo `R₁₀`, `Λnum ≡ -y(y-4)R₄R₁₀'`; hence at a simple root `γ` of `R₁₀` the
residue of `Λ` is `-γ(γ-4)R₄(γ)R₁₀'(γ)/((γ-4)γR₄(γ)R₁₀'(γ)) = -1`. -/
theorem R10_dvd_LambdaNum_add :
    R10 ∣ LambdaNum + X 2 * (X 2 - 4) * R4 * MvPolynomial.pderiv 2 R10 :=
  ⟨3 * X 2 * R4 + 5 * (X 2 - 4) * R4 + 3 * X 2 * (X 2 - 4) * MvPolynomial.pderiv 2 R4,
   by unfold LambdaNum; ring⟩

/-! ### The local data at the branch point `y = 0` -/

/-- Substitution `y ↦ 0` in `ℚ[a,b,y]`: the evaluation at the branch point `y = 0` of `π`. -/
noncomputable def evalY0 : MP →ₐ[ℚ] MP := MvPolynomial.aeval ![X 0, X 1, 0]

/-- The constant term of `R₄`: `R₄(0) = 1`. -/
theorem evalY0_R4 : evalY0 R4 = 1 := by
  unfold evalY0 R4 ms mono R4L
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp [map_mul, map_pow] <;> rw [map_ofNat]

/-- The constant term of `R₁₀`: `R₁₀(0) = 4a²b²`. -/
theorem evalY0_R10 : evalY0 R10 = 4 * (X 0) ^ 2 * (X 1) ^ 2 := by
  unfold evalY0 R10 ms mono R10L
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp [map_mul, map_pow] <;> rw [map_ofNat]

/-- `R₄(0)·R₁₀(0) = 4a²b²`.  With `Λnum(0) = -20R₄(0)R₁₀(0)` (all the other terms of `Λnum`
carry a factor `y`) this is the local data at `y = 0`: the orders of vanishing of `c₄, c₃` are
`3, 2`, so `c₃/c₄` has residue `5` at `0` (see `X2_dvd_LambdaNum_sub_five`), and the
indicial polynomial of the eliminated fourth-order equation at `0` is
`¼(N-3)²(2N-5)²` (SESSION 41, `Scratch/lemma14/cside/README.md` §11). -/
theorem evalY0_R4_mul_R10 : evalY0 (R4 * R10) = 4 * (X 0) ^ 2 * (X 1) ^ 2 := by
  rw [map_mul, evalY0_R4, evalY0_R10]; ring

end Submission.CDT.LL
