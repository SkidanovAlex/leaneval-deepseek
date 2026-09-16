import Submission.ZagierHoffmanProof.TmMotive

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial Matrix Finset
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

/-!
# The criterion input `Φ = A^{(-1)}` of the merged `t`-motive

Given the merged dual `t`-motive `A = tmAOpt q θ w S cf` with `A_0`-coefficients, the matrix
required by the Anderson–Brownawell–Papanikolas criterion is its coefficientwise `(-1)`-twist
`Φ = A^{(-1)}`, realised in `TmRoot.lean` as the coefficientwise `q`-th root.
-/

variable (F : Type*) [Field F] [Finite F]

/-- The criterion input `Φ = A^{(-1)}` of the merged `t`-motive, with `A` the polynomial matrix
(`tmAOpt`) whose entries have `A_0 = F_q[θ]`-coefficients. -/
noncomputable def tmPhi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial (Ambient F))) (hA : ∀ i j m, (A i j).coeff m ∈ ambA F 0) :
    Matrix ι ι (Polynomial (Ambient F)) :=
  fun i j => polyQRoot F (A i j) (hA i j)

lemma tmPhi_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial (Ambient F))) (hA : ∀ i j m, (A i j).coeff m ∈ ambA F 0)
    (i j : ι) : tmPhi F A hA i j = polyQRoot F (A i j) (hA i j) := rfl

/-- The `(1)`-twist of `Φ` is `A`. -/
lemma polyTwist_tmPhi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial (Ambient F))) (hA : ∀ i j m, (A i j).coeff m ∈ ambA F 0)
    (i j : ι) :
    polyTwist (q := Nat.card F) 1 (tmPhi F A hA i j) = A i j :=
  polyTwist_one_polyQRoot F (A i j) (hA i j)

/-- The coefficients of `Φ` lie in `A_1 = F_q[θ^{q^{-1}}]`. -/
lemma tmPhi_coeff_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial (Ambient F))) (hA : ∀ i j m, (A i j).coeff m ∈ ambA F 0) :
    ∀ i j m, (tmPhi F A hA i j).coeff m ∈ ambA F 1 :=
  fun i j m => polyQRoot_mem F (A i j) (hA i j) m

/-- **The functional equation in the criterion's form**: the first column `ψ` of `Ψ` satisfies
`ψ = Φ^{(1)}·ψ^{(1)}` with `Φ` the coefficientwise `q`-th root of `A`. -/
theorem tmPhi_twist_mat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial (Ambient F))) (hA : ∀ i j m, (A i j).coeff m ∈ ambA F 0) :
    frobTwistMat (K := Ambient F) (q := Nat.card F) 1
        ((coeHom (K := Ambient F)).mapMatrix (tmPhi F A hA))
      = (coeHom (K := Ambient F)).mapMatrix A := by
  funext i j
  rw [frobTwistMat_apply, RingHom.mapMatrix_apply, Matrix.map_apply, ← coe_polyTwist,
    polyTwist_tmPhi, RingHom.mapMatrix_apply, Matrix.map_apply]



/-! ## Appendix: the `q`-th root of `(X - C θ^q)^n`

The determinant of `Φ` needs the fact that the coefficientwise `q`-th root of
`(X - C (θ^q))^n` is `(X - C θ)^n` (the binomial coefficients are `F_q`-rational). -/

lemma polyTwist_one_injective :
    Function.Injective (polyTwist (K := Ambient F) (q := Nat.card F) 1) := by
  intro p r hpr
  ext m
  have h := congrArg (fun s : Polynomial (Ambient F) => s.coeff m) hpr
  simp only [polyTwist, polyTwistHom_apply, Polynomial.coeff_map, frobPowHom_apply,
    pow_one] at h
  exact ambPow_injective F 1 (by simpa using h)

lemma polyTwist_one_X_sub_C_pow (n : ℕ) :
    polyTwist (K := Ambient F) (q := Nat.card F) 1 ((X - C (ambTheta F)) ^ n)
      = (X - C ((ambTheta F) ^ Nat.card F)) ^ n := by
  simp only [polyTwist, polyTwistHom_apply, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, frobPowHom_apply, pow_one]

/-- ★ The coefficientwise `q`-th root of `(X - C θ^q)^n` is `(X - C θ)^n`. -/
lemma polyQRoot_X_sub_C_pow (n : ℕ)
    (h0 : ∀ m, ((X - C ((ambTheta F) ^ Nat.card F)) ^ n : Polynomial (Ambient F)).coeff m
      ∈ ambA F 0) :
    polyQRoot F ((X - C ((ambTheta F) ^ Nat.card F)) ^ n) h0 = (X - C (ambTheta F)) ^ n := by
  apply polyTwist_one_injective F
  rw [polyTwist_one_polyQRoot, polyTwist_one_X_sub_C_pow]



/-! ## §3. The determinant of the dual `t`-motive

The merged `t`-motive is "triangular with respect to the tuple length": its only possible
off-diagonal nonzero entries are at `(t, t.dropLast)`, which strictly decreases the length.  We
transport this to a `LinearOrder` on the index set (decreasing in `tmLen`, with the
`Fintype.equivFin` enumeration as tie-breaker) and use `Matrix.det_of_isUpperTriangular`.  This
avoids the `Matrix.det_apply`-permutation route entirely (see `PLAN.md` for why that route does
not re-elaborate). -/

section Det

variable {K : Type*} [Field K] [DecidableEq K]

open scoped Classical
set_option warn.classDefReducibility false

lemma tmA_ne_zero_imp {θ : K} (q : ℕ) (w : ℕ) {t t' : List (ℕ × Polynomial K)}
    (h : tmA q θ w t t' ≠ 0) : t' = t ∨ t' = t.dropLast := by
  by_contra hc
  exact h (tmA_eq_zero_of_ne θ w (fun h1 => hc (Or.inl h1)) (fun h2 => hc (Or.inr h2)))

lemma length_dropLast_le (t : List (ℕ × Polynomial K)) : t.dropLast.length ≤ t.length := by
  rw [List.length_dropLast]; omega

/-- The length function used for the triangularity argument: `none` gets a value larger than
every tuple length, and `some t` gets `t.1.length`. -/
noncomputable def tmLen (S : Finset (List (ℕ × Polynomial K))) :
    Option ↥(tmI S) → ℕ :=
  fun i => match i with
    | none => (∑ s ∈ S, s.length) + 1
    | some t => t.1.length

@[simp] lemma tmLen_some (S : Finset (List (ℕ × Polynomial K))) (t : ↥(tmI S)) :
    tmLen S (some t) = t.1.length := rfl

@[simp] lemma tmLen_none (S : Finset (List (ℕ × Polynomial K))) :
    tmLen S none = (∑ s ∈ S, s.length) + 1 := rfl

lemma length_tmI_lt (S : Finset (List (ℕ × Polynomial K))) (t : ↥(tmI S)) :
    t.1.length < (∑ s ∈ S, s.length) + 1 := by
  obtain ⟨s, hs, k, hk, hkt⟩ := mem_tmI.mp t.2
  have h1 : t.1.length = k := by rw [← hkt, List.length_take, min_eq_left (by omega)]
  have h2 : s.length ≤ ∑ s ∈ S, s.length := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hs
  omega

/-- A linear order on the index set of the merged `t`-motive, *decreasing* in the tuple length:
if a `t`-motive entry `M i j` is nonzero off the diagonal then `j = i.dropLast`, so `j` is
strictly *smaller* in this order (Mathlib's `IsUpperTriangular` asks for `M i j = 0` when
`j < i`). -/
noncomputable def tmOrd (S : Finset (List (ℕ × Polynomial K))) :
    LinearOrder (Option ↥(tmI S)) :=
  LinearOrder.lift'
    (fun i => toLex ((∑ s ∈ S, s.length) + 1 - tmLen S i,
      ((Fintype.equivFin (Option ↥(tmI S))) i : ℕ)))
    (fun i j h => by
      have h1 : ((∑ s ∈ S, s.length) + 1 - tmLen S i,
            ((Fintype.equivFin (Option ↥(tmI S))) i : ℕ))
          = ((∑ s ∈ S, s.length) + 1 - tmLen S j,
            ((Fintype.equivFin (Option ↥(tmI S))) j : ℕ)) := h
      exact (Fintype.equivFin (Option ↥(tmI S))).injective
        (Fin.ext (congrArg Prod.snd h1)))

attribute [local instance] tmOrd

lemma tmLen_le_of_lt (S : Finset (List (ℕ × Polynomial K))) {i j : Option ↥(tmI S)}
    (h : j < i) : tmLen S i ≤ tmLen S j := by
  have h1 : toLex ((∑ s ∈ S, s.length) + 1 - tmLen S j,
        ((Fintype.equivFin (Option ↥(tmI S))) j : ℕ))
      < toLex ((∑ s ∈ S, s.length) + 1 - tmLen S i,
        ((Fintype.equivFin (Option ↥(tmI S))) i : ℕ)) := h
  have h2 := (Prod.Lex.toLex_lt_toLex.mp h1)
  have h3 : (∑ s ∈ S, s.length) + 1 - tmLen S j
      ≤ (∑ s ∈ S, s.length) + 1 - tmLen S i := by
    rcases h2 with h2 | ⟨h2, -⟩
    · exact le_of_lt h2
    · exact le_of_eq h2
  have h4 : tmLen S i ≤ (∑ s ∈ S, s.length) + 1 := by
    cases i with
    | none => rw [tmLen_none]
    | some t => exact le_of_lt (length_tmI_lt S t)
  have h5 : tmLen S j ≤ (∑ s ∈ S, s.length) + 1 := by
    cases j with
    | none => rw [tmLen_none]
    | some t => exact le_of_lt (length_tmI_lt S t)
  omega

/-- The merged `t`-motive is upper triangular for the length-decreasing order. -/
lemma tmAOpt_isUpperTriangular {θ : K} (q : ℕ) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial K))) (cf : List (ℕ × Polynomial K) → Polynomial K) :
    (tmAOpt q θ w S cf).IsUpperTriangular := by
  intro i j hij
  have hle := tmLen_le_of_lt S hij
  simp only [id_eq] at hle hij
  cases i with
  | none =>
    cases j with
    | none => exact absurd hij (lt_irrefl _)
    | some t =>
      rw [tmLen_none, tmLen_some] at hle
      exact absurd hle (not_le.mpr (length_tmI_lt S t))
  | some t =>
    cases j with
    | none => rw [tmAOpt_some_none]
    | some t' =>
      by_contra h0
      rw [tmAOpt_some_some] at h0
      rcases tmA_ne_zero_imp q w h0 with h2 | h2
      · have hji : (some t' : Option ↥(tmI S)) = some t := congrArg some (Subtype.ext h2)
        rw [hji] at hij
        exact absurd hij (lt_irrefl (some t))
      · by_cases hnil : t.1 = []
        · have h3 : t'.1 = t.1 := by rw [h2, hnil]; rfl
          have hji : (some t' : Option ↥(tmI S)) = some t := congrArg some (Subtype.ext h3)
          rw [hji] at hij
          exact absurd hij (lt_irrefl (some t))
        · rw [tmLen_some, tmLen_some, h2, List.length_dropLast] at hle
          have hpos : 0 < t.1.length := List.length_pos_iff.mpr hnil
          omega

/-- **The determinant of the merged dual `t`-motive** is the product of its diagonal:
`∏_{t} (t - θ^q)^{w - w(t)}`. -/
theorem det_tmAOpt {θ : K} (q : ℕ) (w : ℕ) (S : Finset (List (ℕ × Polynomial K)))
    (cf : List (ℕ × Polynomial K) → Polynomial K) :
    (tmAOpt q θ w S cf).det
      = ∏ t : ↥(tmI S), (X - C (θ ^ q)) ^ (w - tmWeight t.1) := by
  rw [Matrix.det_of_isUpperTriangular (tmAOpt_isUpperTriangular q w S cf),
    Fintype.prod_option, tmAOpt_none_none, one_mul]
  exact Finset.prod_congr rfl fun t _ => by rw [tmAOpt_some_some, tmA_diag]

end Det

section DetPhi

variable (F : Type*) [Field F] [Finite F]

open scoped Classical
set_option warn.classDefReducibility false

attribute [local instance] tmOrd

lemma polyQRoot_eq_zero_of_eq_zero {p : Polynomial (Ambient F)}
    (hp : ∀ m, p.coeff m ∈ ambA F 0) (hz : p = 0) : polyQRoot F p hp = 0 := by
  subst hz
  simp only [polyQRoot, Polynomial.support_zero, Finset.sum_empty]

lemma polyQRoot_one_eq (hp : ∀ m, (1 : Polynomial (Ambient F)).coeff m ∈ ambA F 0) :
    polyQRoot F 1 hp = 1 := by
  apply polyTwist_one_injective F
  rw [polyTwist_one_polyQRoot]
  simp [polyTwist, polyTwistHom_apply]

/-- **The determinant of the criterion input `Φ`**: the coefficientwise `q`-th root replaces
`(X - C θ^q)` by `(X - C θ)`. -/
theorem det_tmPhi (w : ℕ) (S : Finset (List (ℕ × Polynomial (Ambient F))))
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (hA : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m ∈ ambA F 0) :
    (tmPhi F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA).det
      = (X - C (ambTheta F)) ^ (∑ t : ↥(tmI S), (w - tmWeight t.1)) := by
  have htri :
      (tmPhi F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA).IsUpperTriangular := by
    intro i j hij
    by_contra h0
    have h1 : tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j ≠ 0 := fun hz =>
      h0 (polyQRoot_eq_zero_of_eq_zero F (hA i j) hz)
    exact absurd (tmAOpt_isUpperTriangular (K := Ambient F) (Nat.card F) w S cf hij) h1
  have h1 : tmPhi F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA none none = 1 := by
    show polyQRoot F
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf none none) (hA none none) = 1
    exact polyQRoot_one_eq F _
  have h2 : ∀ t : ↥(tmI S),
      tmPhi F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA (some t) (some t)
        = (X - C (ambTheta F)) ^ (w - tmWeight t.1) := by
    intro t
    show polyQRoot F
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf (some t) (some t))
      (hA (some t) (some t)) = (X - C (ambTheta F)) ^ (w - tmWeight t.1)
    simp only [tmAOpt_some_some, tmA_diag]
    exact polyQRoot_X_sub_C_pow F (w - tmWeight t.1) _
  rw [Matrix.det_of_isUpperTriangular htri, Fintype.prod_option, h1, one_mul,
    Finset.prod_congr rfl (fun t (_ : t ∈ Finset.univ) => h2 t),
    Finset.prod_pow_eq_pow_sum]

end DetPhi

end ZagierHoffmanPositiveChar
