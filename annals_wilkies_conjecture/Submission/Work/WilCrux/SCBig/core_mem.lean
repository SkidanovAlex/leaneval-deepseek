/-
  WilCrux / SCBig — `core_mem`: the `Ω`-membership of the core set `coreSet T ε`.

  `coreSet (a := a) (b := b) T ε ⊆ ℝ^{((a+1)+(b+b))+2}` is, by definition, the set of points `u`
  whose `(w, z, y)`-block `u ∘ e1` and whose `(w, z', y')`-block `u ∘ e2` both lie in `T`, and
  whose two value coordinates `u yIx`, `u yIx'` differ by less than `ε`:

      `coreSet T ε = coordPre e1 T ∩ (coordPre e2 T ∩ {u | |u yIx - u yIx'| < ε})`.

  Each of the three conjuncts is an `Ω`-set with bounds independent of `ε`:

  * `Work.WilG5.coordPre_mem` gives `coordPre ι T ∈ Ω (F + 64*(N+m) + 64) (D + 32*(N+m) + 32) N`
    for `T ∈ Ω F D m`, `ι : Fin m → Fin N`;
  * `|u i - u j| < ε` is the intersection of the two strict half-spaces
    `u i - u j < ε` and `u j - u i < ε`, each a positivity set of a *degree one* polynomial
    (the constant `ε` only enters the coefficients, not the total degree), so
    `pos_mem` gives format `N + 2` and degree `3` for each, hence `N + 3` and `6` after the
    intersection.

  Two binary intersections then cost one format step each and add the degrees: with
  `cD = 32*(N+m) + 32` the resulting degree is `(D + cD) + ((D + cD) + 6) = 2*D + 2*cD + 6`,
  which is `q.eval D` for `q = C (2*cD + 6) + C 2 * X`; the format is `Ft + A` with
  `A = (64*(N+m) + 64) + (N + 3) + 2`.
-/
import Mathlib
import Submission.Work.WilCrux.SliceCauchyBig
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Calc.pos_mem

set_option autoImplicit false

namespace Work.WilCrux.SCBig

/-! ## Two auxiliary `Ω`-sets with bounds independent of the parameters -/

/-- The strict half-space `{u | u i - u j < c}` is an `Ω`-set, with format and degree
uniform in `c`: it is the positivity set `{0 < ε - (X i - X j)}` of a polynomial of total
degree at most one. -/
private theorem subLt_mem (S : WilkiesDesign.SOMin) {N : ℕ} (i j : Fin N) (c : ℝ) :
    {u : Fin N → ℝ | u i - u j < c} ∈ S.Ω (N + 2) 3 N := by
  have htd : (MvPolynomial.C c - (MvPolynomial.X i - MvPolynomial.X j) :
      MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
    refine le_trans (Work.WilG5.td_sub_le _ _) ?_
    refine max_le ?_ ?_
    · exact le_trans (Work.WilG5.td_C_le c) (Nat.zero_le 1)
    · exact le_trans (Work.WilG5.td_sub_le _ _)
        (max_le (Work.WilG5.td_X_le i) (Work.WilG5.td_X_le j))
  have h := Work.WilG1.Calc.pos_mem (S := S) 0
    (MvPolynomial.C c - (MvPolynomial.X i - MvPolynomial.X j) : MvPolynomial (Fin N) ℝ)
  have hset : {u : Fin N → ℝ | 0 < MvPolynomial.eval u
      (MvPolynomial.C c - (MvPolynomial.X i - MvPolynomial.X j) : MvPolynomial (Fin N) ℝ)}
      = {u : Fin N → ℝ | u i - u j < c} := by
    ext u
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_C,
      MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  rw [hset] at h
  refine Work.WilG5.mem_mono h (N + 2) 3 le_rfl ?_
  simp only [Polynomial.eval_C]
  omega

/-- Binary intersection of two `Ω`-sets at a common format. -/
private theorem inter2_mem {S : WilkiesDesign.SOMin} {n F D₁ D₂ : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F D₁ n) (hB : B ∈ S.Ω F D₂ n) :
    A ∩ B ∈ S.Ω (F + 1) (D₁ + D₂) n := by
  have h := S.inter (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then A else B)
    (by intro i; fin_cases i
        · simpa using hA
        · simpa using hB)
  have hsum : (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ := by
    rw [Fin.sum_univ_two]; simp
  rw [hsum, Work.WilG1.Omega.iInter_fin_two] at h
  exact h

/-- The two-sided inequality `{u | |u i - u j| < c}` is an `Ω`-set, with format and degree
uniform in `c`. -/
private theorem absSubLt_mem (S : WilkiesDesign.SOMin) {N : ℕ} (i j : Fin N) (c : ℝ) :
    {u : Fin N → ℝ | |u i - u j| < c} ∈ S.Ω (N + 3) 6 N := by
  have h := inter2_mem (S := S) (subLt_mem S i j c) (subLt_mem S j i c)
  have hset : {u : Fin N → ℝ | u i - u j < c} ∩ {u : Fin N → ℝ | u j - u i < c}
      = {u : Fin N → ℝ | |u i - u j| < c} := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [abs_lt]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  rw [hset] at h
  refine Work.WilG5.mem_mono h (N + 3) 6 ?_ le_rfl
  omega

/-! ## The general shape of the argument -/

/-- The core set of two coordinate pullbacks and a two-sided value inequality is an `Ω`-set
with a format that is `F` plus a constant and a degree that is a polynomial in `D`. -/
private theorem coreSet_mem_aux (S : WilkiesDesign.SOMin) (m N : ℕ)
    (ι₁ ι₂ : Fin m → Fin N) (i j : Fin N) :
    ∃ (A : ℕ) (q : Polynomial ℕ),
      ∀ (F D : ℕ) (T : Set (Fin m → ℝ)) (ε : ℝ),
        T ∈ S.Ω F D m →
          Work.WilG5.coordPre ι₁ T ∩ (Work.WilG5.coordPre ι₂ T ∩
            {u : Fin N → ℝ | |u i - u j| < ε}) ∈ S.Ω (F + A) (q.eval D) N := by
  set cF : ℕ := 64 * (N + m) + 64 with hcF
  set cD : ℕ := 32 * (N + m) + 32 with hcD
  set A0 : ℕ := cF + (N + 3) with hA0
  refine ⟨A0 + 2, Polynomial.C (cD + cD + 6) + Polynomial.C 2 * Polynomial.X, ?_⟩
  intro F D T ε hT
  -- the two pullbacks of `T`
  have hA : Work.WilG5.coordPre ι₁ T ∈ S.Ω (F + cF) (D + cD) N := by
    refine Work.WilG5.mem_mono
      (Work.WilG5.coordPre_mem (S := S) (m := m) (N := N) (ι := ι₁) hT)
      (F + cF) (D + cD) ?_ ?_
    · simp only [hcF]; omega
    · simp only [hcD]; omega
  have hB : Work.WilG5.coordPre ι₂ T ∈ S.Ω (F + cF) (D + cD) N := by
    refine Work.WilG5.mem_mono
      (Work.WilG5.coordPre_mem (S := S) (m := m) (N := N) (ι := ι₂) hT)
      (F + cF) (D + cD) ?_ ?_
    · simp only [hcF]; omega
    · simp only [hcD]; omega
  -- the value inequality
  have hC : {u : Fin N → ℝ | |u i - u j| < ε} ∈ S.Ω (F + cF) 6 N := by
    refine Work.WilG5.mem_mono (absSubLt_mem S i j ε) (F + cF) 6 ?_ le_rfl
    simp only [hcF]; omega
  -- the two intersections
  have hBC := inter2_mem (S := S) hB hC
  have hA' : Work.WilG5.coordPre ι₁ T ∈ S.Ω ((F + cF) + 1) (D + cD) N :=
    Work.WilG5.mem_mono hA ((F + cF) + 1) (D + cD) (by omega) le_rfl
  have hABC := inter2_mem (S := S) hA' hBC
  refine Work.WilG5.mem_mono hABC (F + (A0 + 2))
    ((Polynomial.C (cD + cD + 6) + Polynomial.C 2 * Polynomial.X : Polynomial ℕ).eval D) ?_ ?_
  · simp only [hA0, hcF]; omega
  · have hev : (Polynomial.C (cD + cD + 6) + Polynomial.C 2 * Polynomial.X :
        Polynomial ℕ).eval D = (cD + cD + 6) + 2 * D := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    rw [hev]
    omega

/-! ## The requested lemma -/

theorem core_mem (S : WilkiesDesign.SOMin) (a b : ℕ) :
    ∃ (A : ℕ) (q : Polynomial ℕ),
      ∀ (Ft Dt : ℕ) (T : Set (Fin ((a + b) + 1) → ℝ)) (ε : ℝ),
        T ∈ S.Ω Ft Dt ((a + b) + 1) →
          coreSet (a := a) (b := b) T ε ∈ S.Ω (Ft + A) (q.eval Dt) (((a + 1) + (b + b)) + 2) := by
  obtain ⟨A, q, h⟩ := coreSet_mem_aux (S := S) ((a + b) + 1) (((a + 1) + (b + b)) + 2)
    (e1 (a := a) (b := b)) (e2 (a := a) (b := b))
    (yIx (a := a) (b := b)) (yIx' (a := a) (b := b))
  refine ⟨A, q, ?_⟩
  intro Ft Dt T ε hT
  have hset : coreSet (a := a) (b := b) T ε =
      Work.WilG5.coordPre (e1 (a := a) (b := b)) T ∩
        (Work.WilG5.coordPre (e2 (a := a) (b := b)) T ∩
          {u : Fin (((a + 1) + (b + b)) + 2) → ℝ | |u yIx - u yIx'| < ε}) := by
    ext u
    simp [coreSet, Work.WilG5.coordPre]
  rw [hset]
  exact h Ft Dt T ε hT

end Work.WilCrux.SCBig
