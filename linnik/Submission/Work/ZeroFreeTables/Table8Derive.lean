/-
# ZeroFreeTables — Table8Derive.lean

The `P₃` engine of AREA 3 at work: **HB Lemma 9.1 + the rational certificate of
Table 8 give the `λ₀`-bounds of HB's Table 8** for the thirteen entries used by
`rows15` (i.e. for `λ₁ ∈ [0.348, 0.60]`), with the `0.001` safety margin of the
frozen statement.

The mathematical content is the monotonicity of the engine inequality (9.13) in
both `λ₁` and `λ₀`, and the choice `ε = -p913(hi,v,a,K) / (2(a+hi))`.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## Monotonicity of the engine inequality -/

/-- `P₃(x) - P₃(y) = (x - y)(1 + x + y + (2/3)(x² + xy + y²))`, identically. -/
theorem P3R_sub_eq (x y : ℝ) :
    P3R x - P3R y = (x - y) * (1 + x + y + (2/3) * (x^2 + x*y + y^2)) := by
  simp only [P3R]; ring

/-- `P₃` is strictly increasing on `ℝ` (`P₃'(x) = 1 + 2x + 2x² > 0`). -/
theorem P3R_strictMono : StrictMono P3R := by
  intro x y hxy
  have hdiff : P3R y - P3R x
      = (y - x) * (1 + y + x + (2/3) * (y^2 + y*x + x^2)) := P3R_sub_eq y x
  have hpos : 0 < y - x := sub_pos.mpr hxy
  have hfac : (2/3) * ((x + 1/2)^2 + (x + 1/2) * (y + 1/2) + (y + 1/2)^2) + 1/2
      = 1 + y + x + (2/3) * (y^2 + y*x + x^2) := by ring
  have h2 : 0 < 1 + y + x + (2/3) * (y^2 + y*x + x^2) := by
    rw [← hfac]
    nlinarith [sq_nonneg (x + 1/2), sq_nonneg (y + 1/2),
      sq_nonneg ((x + 1/2) + (y + 1/2))]
  have : 0 < P3R y - P3R x := by rw [hdiff]; exact mul_pos hpos h2
  linarith

theorem P3R_mono : Monotone P3R := P3R_strictMono.monotone

theorem P3R_lt_iff {x y : ℝ} : P3R x < P3R y ↔ x < y := P3R_strictMono.lt_iff_lt

theorem P3R_le_iff {x y : ℝ} : P3R x ≤ P3R y ↔ x ≤ y := P3R_strictMono.le_iff_le

/-- The bracket of (9.13), `P₃((a+λ)/a) - P₃((a+λ)/(a+λ₀))`, is non-decreasing in `λ`
for `0 ≤ λ ≤ λ₀` and `a > 0`.  Both factors in
`P₃(u) - P₃(v) = (u - v)(1 + u + v + u² + uv + v²)` increase with `λ`. -/
theorem p3_bracket_mono {lam lam' lam₀ a : ℝ} (h0 : 0 ≤ lam) (h : lam ≤ lam')
    (h2 : lam' ≤ lam₀) (ha : 0 < a) :
    P3R ((a+lam)/a) - P3R ((a+lam)/(a+lam₀))
      ≤ P3R ((a+lam')/a) - P3R ((a+lam')/(a+lam₀)) := by
  have hlam₀nn : 0 ≤ lam₀ := le_trans h0 (le_trans h h2)
  have hden : 0 < a + lam₀ := by linarith
  have key : ∀ l : ℝ, P3R ((a+l)/a) - P3R ((a+l)/(a+lam₀))
      = ((a + l) * lam₀ / (a * (a+lam₀))) *
        (1 + ((a+l)/a) + ((a+l)/(a+lam₀)) + (2/3) * (((a+l)/a)^2
          + ((a+l)/a) * ((a+l)/(a+lam₀)) + ((a+l)/(a+lam₀))^2)) := by
    intro l
    have h2' : (a + l)/a - (a + l)/(a + lam₀) = (a + l) * lam₀ / (a * (a + lam₀)) := by
      field_simp
      ring
    rw [P3R_sub_eq, h2']
  rw [key lam, key lam']
  have hf1 : (a + lam) * lam₀ / (a * (a + lam₀)) ≤ (a + lam') * lam₀ / (a * (a + lam₀)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hf1nn : 0 ≤ (a + lam) * lam₀ / (a * (a + lam₀)) :=
    div_nonneg (mul_nonneg (by linarith) hlam₀nn) (by positivity)
  have hu1 : 0 ≤ (a+lam)/a := div_nonneg (by linarith) ha.le
  have hv1 : 0 ≤ (a+lam)/(a+lam₀) := div_nonneg (by linarith) hden.le
  have hQnn : 0 ≤ 1 + ((a+lam)/a) + ((a+lam)/(a+lam₀)) + (2/3) * (((a+lam)/a)^2
      + ((a+lam)/a) * ((a+lam)/(a+lam₀)) + ((a+lam)/(a+lam₀))^2) := by
    have h1 : 0 ≤ ((a+lam)/a)^2 := sq_nonneg _
    have h2 : 0 ≤ ((a+lam)/(a+lam₀))^2 := sq_nonneg _
    have h3 : 0 ≤ ((a+lam)/a) * ((a+lam)/(a+lam₀)) := mul_nonneg hu1 hv1
    linarith
  have hQmono : 1 + ((a+lam)/a) + ((a+lam)/(a+lam₀)) + (2/3) * (((a+lam)/a)^2
      + ((a+lam)/a) * ((a+lam)/(a+lam₀)) + ((a+lam)/(a+lam₀))^2)
      ≤ 1 + ((a+lam')/a) + ((a+lam')/(a+lam₀)) + (2/3) * (((a+lam')/a)^2
      + ((a+lam')/a) * ((a+lam')/(a+lam₀)) + ((a+lam')/(a+lam₀))^2) := by
    have hu : (a+lam)/a ≤ (a+lam')/a :=
      div_le_div_of_nonneg_right (by linarith) ha.le
    have hv : (a+lam)/(a+lam₀) ≤ (a+lam')/(a+lam₀) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    have hu0 : 0 ≤ (a+lam)/a := div_nonneg (by linarith) ha.le
    have hv0 : 0 ≤ (a+lam)/(a+lam₀) := div_nonneg (by linarith) hden.le
    have hu'0 : 0 ≤ (a+lam')/a := div_nonneg (by linarith) ha.le
    have h2u : ((a+lam)/a)^2 ≤ ((a+lam')/a)^2 := pow_le_pow_left₀ hu0 hu 2
    have h2v : ((a+lam)/(a+lam₀))^2 ≤ ((a+lam')/(a+lam₀))^2 := pow_le_pow_left₀ hv0 hv 2
    have huv : ((a+lam)/a) * ((a+lam)/(a+lam₀)) ≤ ((a+lam')/a) * ((a+lam')/(a+lam₀)) :=
      mul_le_mul hu hv hv0 hu'0
    linarith
  have hlast : 0 ≤ (a+lam') * lam₀ / (a * (a+lam₀)) :=
    div_nonneg (mul_nonneg (by linarith [h0, h]) hlam₀nn) (by positivity)
  exact mul_le_mul hf1 hQmono hQnn hlast

/-- (9.13)'s left hand side is *non-decreasing* in `λ₀`.  Hence the inequality is
easiest for large `λ₀`, and the certificate at the tabulated value `v` (together
with `λ₀ ≤ v`) gives the lower bound `v ≤ λ₀`. -/
theorem p913_mono_lam₀ {lam₁ lam₀ lam₀' a K : ℝ} (ha : 0 < a) (hlam₁ : -a < lam₁)
    (hlam₀ : -a < lam₀) (hlam₀' : -a < lam₀') (h : lam₀ ≤ lam₀') :
    p913 lam₁ lam₀ a K ≤ p913 lam₁ lam₀' a K := by
  have h1 : 0 < a + lam₁ := by linarith
  have h2 : 0 < a + lam₀ := by linarith
  have hden : (a + lam₁) / (a + lam₀') ≤ (a + lam₁) / (a + lam₀) :=
    div_le_div_of_nonneg_left h1.le h2 (by linarith)
  have hmono : P3R ((a + lam₁) / (a + lam₀')) ≤ P3R ((a + lam₁) / (a + lam₀)) :=
    P3R_mono hden
  have hK2 : 0 ≤ K ^ 2 + 1/2 := by positivity
  have h3 : (K^2+1/2) * (P3R ((a+lam₁)/(a+lam₀')) - P3R ((a+lam₁)/(a+lam₀)))
      ≤ 0 := by
    have : P3R ((a + lam₁) / (a + lam₀')) - P3R ((a + lam₁) / (a + lam₀)) ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos hK2 this
  unfold p913
  linarith [h3]

/-- (9.13)'s left hand side is non-decreasing in `λ₁` for `0 ≤ λ₁ ≤ λ₁' ≤ λ₀` and
`a > 0`, `K > 0`.  This is what lets the certificate at the *right* end of each
interval cover the whole interval. -/
theorem p913_mono_lam₁ {lam₁ lam₁' lam₀ a K : ℝ} (h0 : 0 ≤ lam₁) (h : lam₁ ≤ lam₁')
    (h2 : lam₁' ≤ lam₀) (ha : 0 < a) (hK : 0 < K) :
    p913 lam₁ lam₀ a K ≤ p913 lam₁' lam₀ a K := by
  have hbr := p3_bracket_mono (lam := lam₁) (lam' := lam₁') (lam₀ := lam₀) h0 h h2 ha
  have hpsi : 0 ≤ psi13 K := by
    unfold psi13
    nlinarith [sq_nonneg K, sq_nonneg (K + 3/2)]
  have hK2 : 0 ≤ K ^ 2 + 1/2 := by positivity
  have h3 : (K^2+1/2) * (P3R ((a+lam₁)/a) - P3R ((a+lam₁)/(a+lam₀)))
      ≤ (K^2+1/2) * (P3R ((a+lam₁')/a) - P3R ((a+lam₁')/(a+lam₀))) :=
    mul_le_mul_of_nonneg_left hbr hK2
  have h2' : (a + lam₁) * psi13 K ≤ (a + lam₁') * psi13 K :=
    mul_le_mul_of_nonneg_right (by linarith) hpsi
  unfold p913
  linarith [h2', h3]

/-- The side condition of Lemma 9.1 becomes easier as `λ₁` decreases. -/
theorem cond913_mono_lam₁ {lam₁ lam₁' lam₀ a K : ℝ} (h : lam₁ ≤ lam₁') (hK : 0 < K)
    (ha : 0 < a) (ha₁ : 0 < a + lam₁) (hcond : cond913 lam₁' lam₀ a K) :
    cond913 lam₁ lam₀ a K := by
  have hKnn : 0 ≤ Kond K := le_of_lt (lt_min (by positivity) (by positivity))
  have hle : (a + lam₁) ^ 3 ≤ (a + lam₁') ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have h1 : 0 < (a + lam₁) ^ 3 := pow_pos ha₁ 3
  have h4 : Kond K / (a + lam₁') ^ 3 ≤ Kond K / (a + lam₁) ^ 3 :=
    div_le_div_of_nonneg_left hKnn h1 hle
  unfold cond913 at hcond ⊢
  linarith


/-! ## The engine at work: HB Lemma 9.1 + the certificate give the `λ₀` bound -/

/-- A non-principal Dirichlet character has modulus at least `2`
(`ZMod 1` carries only the trivial character). -/
theorem two_le_modulus_of_char_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : 2 ≤ q := by
  by_contra h
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : q = 1 := by omega
  subst hq1
  exact hχ (Subsingleton.elim χ 1)

/-- Elementary facts about the certificate rows: the witness `a`, the right end
`hi` and the constant `K = Kaff hi` are positive, and `hi ≤ v`. -/
theorem t8certRows_facts : ∀ r ∈ t8certRows,
    0 < r.2.2.2 ∧ 0 < Kaff r.2.1 ∧ r.2.1 ≤ r.2.2.1 ∧ 0 < r.2.1 := by
  intro r hr
  simp only [t8certRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    · subst h
      refine ⟨by norm_num, by norm_num [Kaff], by norm_num, by norm_num⟩

/-- **HB Lemma 9.1 at work.**  For a certified row of Table 8, with `K = Kaff hi`
and the tabulated value `v`, the inequality (9.13) forces `λ₀ ≥ v` for every
second zero `ρ ≠ ρ₁` of `χ₁` in the complex case.  This is the second conjunct of
`Lam0Bound χ₁ ρ₁ v`. -/
theorem lam0_row_of_lemma9_1 (h9 : HBLemma9_1)
    (hcert : ∀ r ∈ t8certRows,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (r0 : ℝ × ℝ × ℝ × ℝ) (hr0 : r0 ∈ t8certRows) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) → lamOf q ρ₁ ≤ r0.2.1 →
      Lam0BoundOther χ₁ ρ₁ r0.2.2.1 := by
  obtain ⟨ha, hK, hhiv, hhipos⟩ := t8certRows_facts r0 hr0
  obtain ⟨hcond, hp⟩ := hcert r0 hr0
  set ε : ℝ := -p913 r0.2.1 r0.2.2.1 r0.2.2.2 (Kaff r0.2.1) / (2 * (r0.2.2.2 + r0.2.1))
    with hεdef
  have hεden : 0 < 2 * (r0.2.2.2 + r0.2.1) := by linarith
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (by linarith) hεden
  obtain ⟨q₀, hq₀⟩ := h9 r0.2.2.2 (Kaff r0.2.1) ε ha hK hε
  refine ⟨q₀, fun q hq _ χ₁ ρ₁ hm hcx hlam ρ hZ hne hconj => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hmem : IsZ χ₁ ρ₁ := isMin1_isZ hm.1
  have hq2 : 2 ≤ q := two_le_modulus_of_char_ne_one (isZ_ne_one hmem)
  have hlam1nn : 0 ≤ lamOf q ρ₁ :=
    Work.LinnikContract.API.isZ_lambda_nonneg hq2 hmem
  have hlam0nn : 0 ≤ lamOf q ρ :=
    Work.LinnikContract.API.isZ_lambda_nonneg hq2 hZ
  -- the side condition, transported from `(hi, v)` to `(λ₁, λ₀)`
  have hcond' : cond913 (lamOf q ρ₁) (lamOf q ρ) r0.2.2.2 (Kaff r0.2.1) := by
    have ha1 : 0 < r0.2.2.2 + lamOf q ρ₁ := by linarith
    have ha4 : 0 < r0.2.2.2 + lamOf q ρ := by linarith
    have hKnn : 0 ≤ Kond (Kaff r0.2.1) :=
      le_of_lt (lt_min (by positivity) (by positivity))
    have h3 : Kond (Kaff r0.2.1) / (r0.2.2.2 + r0.2.1) ^ 3
        ≤ Kond (Kaff r0.2.1) / (r0.2.2.2 + lamOf q ρ₁) ^ 3 :=
      div_le_div_of_nonneg_left hKnn (pow_pos ha1 3)
        (pow_le_pow_left₀ (by linarith) (by linarith : r0.2.2.2 + lamOf q ρ₁ ≤ r0.2.2.2 + r0.2.1) 3)
    have h4 : 1 / (r0.2.2.2 + r0.2.2.1) ^ 3 ≤ 1 / (r0.2.2.2 + lamOf q ρ) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos ha4 3)
        (pow_le_pow_left₀ (by linarith) (by linarith : r0.2.2.2 + lamOf q ρ ≤ r0.2.2.2 + r0.2.2.1) 3)
    unfold cond913 at hcond ⊢
    linarith
  have hineq := hq₀ q hq χ₁ ρ₁ ρ hm hcx hmem hZ hne.symm hconj hcond'
  have hineq' : 0 ≤ p913 (lamOf q ρ₁) (lamOf q ρ) r0.2.2.2 (Kaff r0.2.1)
      + (r0.2.2.2 + lamOf q ρ₁) * ε := hineq
  -- monotonicity in `λ₀`, then in `λ₁`, and the value of `ε`
  have h1 : p913 (lamOf q ρ₁) (lamOf q ρ) r0.2.2.2 (Kaff r0.2.1)
      ≤ p913 (lamOf q ρ₁) r0.2.2.1 r0.2.2.2 (Kaff r0.2.1) :=
    p913_mono_lam₀ ha (by linarith) (by linarith) (by linarith) (le_of_lt hlt)
  have h2 : p913 (lamOf q ρ₁) r0.2.2.1 r0.2.2.2 (Kaff r0.2.1)
      ≤ p913 r0.2.1 r0.2.2.1 r0.2.2.2 (Kaff r0.2.1) :=
    p913_mono_lam₁ hlam1nn hlam hhiv ha hK
  have hεval : (r0.2.2.2 + r0.2.1) * ε
      = -(p913 r0.2.1 r0.2.2.1 r0.2.2.2 (Kaff r0.2.1)) / 2 := by
    rw [hεdef]
    field_simp
  have h5 : (r0.2.2.2 + lamOf q ρ₁) * ε ≤ (r0.2.2.2 + r0.2.1) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  linarith [hineq', h1, h2, h5, hεval, hp]


/-! ## The finite max over the certified rows -/

/-- A finite family of `∃ N, P a N` with `P` monotone in its threshold (a larger `N`
is a weaker statement) has a common threshold. -/
theorem exists_threshold_of_forall_mem {α : Type*} (l : List α) (P : α → ℕ → Prop)
    (h : ∀ a ∈ l, ∃ n : ℕ, P a n)
    (hmono : ∀ a ∈ l, ∀ n n' : ℕ, n ≤ n' → P a n → P a n') :
    ∃ N : ℕ, ∀ a ∈ l, P a N := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a t ih =>
      have ha : a ∈ a :: t := List.mem_cons_self
      have hmem : ∀ b ∈ t, b ∈ a :: t := fun b hb => List.mem_cons_of_mem a hb
      obtain ⟨n, hn⟩ := h a ha
      obtain ⟨N, hN⟩ := ih (fun b hb => h b (hmem b hb)) (fun b hb => hmono b (hmem b hb))
      refine ⟨max n N, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with hba | hbt
      · rw [hba]
        exact hmono a ha n (max n N) (le_max_left _ _) hn
      · exact hmono b (hmem b hbt) N (max n N) (le_max_right _ _) (hN b hbt)

/-- **The certified part of HB Table 8**: modulo HB Lemma 9.1 and the rational
certificate, the thirteen entries of Table 8 used by `rows15` give `λ₀`-bounds for
every `q` above a single threshold. -/
theorem HBTable8_certified_other (h9 : HBLemma9_1)
    (hcert : ∀ r ∈ t8certRows,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      ∀ r ∈ t8certRows, lamOf q ρ₁ ≤ r.2.1 → Lam0BoundOther χ₁ ρ₁ r.2.2.1 := by
  obtain ⟨N, hN⟩ := exists_threshold_of_forall_mem t8certRows
    (fun r N => ∀ q : ℕ, N ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) → lamOf q ρ₁ ≤ r.2.1 →
      Lam0BoundOther χ₁ ρ₁ r.2.2.1)
    (fun r hr => lam0_row_of_lemma9_1 h9 hcert r hr)
    (fun r hr n n' hn hn' q hq => hn' q (le_trans hn hq))
  exact ⟨N, fun q hq _ χ₁ ρ₁ hm hcx r hr hlam => hN r hr q hq χ₁ ρ₁ hm hcx hlam⟩


/-! ## The extension of the certificate to all 21 printed entries -/

theorem t8certRowsExt_facts : ∀ r ∈ t8certRowsExt,
    0 < r.2.2.2 ∧ 0 < Kaff r.2.1 ∧ r.2.1 ≤ r.2.2.1 ∧ 0 < r.2.1 := by
  intro r hr
  simp only [t8certRowsExt, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;>
    · subst h
      refine ⟨by norm_num, by norm_num [Kaff], by norm_num, by norm_num⟩

/-- The row lemma with the elementary facts supplied by the caller. -/
theorem lam0_row_of_lemma9_1_of_facts (h9 : HBLemma9_1) {r0 : ℝ × ℝ × ℝ × ℝ}
    (hcert : cond913 r0.2.1 r0.2.2.1 r0.2.2.2 (Kaff r0.2.1) ∧
      p913 r0.2.1 r0.2.2.1 r0.2.2.2 (Kaff r0.2.1) < 0)
    (ha : 0 < r0.2.2.2) (hK : 0 < Kaff r0.2.1) (hhiv : r0.2.1 ≤ r0.2.2.1)
    (hhipos : 0 < r0.2.1) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) → lamOf q ρ₁ ≤ r0.2.1 →
      Lam0BoundOther χ₁ ρ₁ r0.2.2.1 := by
  obtain ⟨hcond, hp⟩ := hcert
  set ε : ℝ := -p913 r0.2.1 r0.2.2.1 r0.2.2.2 (Kaff r0.2.1) / (2 * (r0.2.2.2 + r0.2.1))
    with hεdef
  have hεden : 0 < 2 * (r0.2.2.2 + r0.2.1) := by linarith
  have hε : 0 < ε := by
    rw [hεdef]
    exact div_pos (by linarith) hεden
  obtain ⟨q₀, hq₀⟩ := h9 r0.2.2.2 (Kaff r0.2.1) ε ha hK hε
  refine ⟨q₀, fun q hq _ χ₁ ρ₁ hm hcx hlam ρ hZ hne hconj => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hmem : IsZ χ₁ ρ₁ := isMin1_isZ hm.1
  have hq2 : 2 ≤ q := two_le_modulus_of_char_ne_one (isZ_ne_one hmem)
  have hlam1nn : 0 ≤ lamOf q ρ₁ :=
    Work.LinnikContract.API.isZ_lambda_nonneg hq2 hmem
  have hlam0nn : 0 ≤ lamOf q ρ :=
    Work.LinnikContract.API.isZ_lambda_nonneg hq2 hZ
  have hcond' : cond913 (lamOf q ρ₁) (lamOf q ρ) r0.2.2.2 (Kaff r0.2.1) := by
    have ha1 : 0 < r0.2.2.2 + lamOf q ρ₁ := by linarith
    have ha4 : 0 < r0.2.2.2 + lamOf q ρ := by linarith
    have hKnn : 0 ≤ Kond (Kaff r0.2.1) :=
      le_of_lt (lt_min (by positivity) (by positivity))
    have h3 : Kond (Kaff r0.2.1) / (r0.2.2.2 + r0.2.1) ^ 3
        ≤ Kond (Kaff r0.2.1) / (r0.2.2.2 + lamOf q ρ₁) ^ 3 :=
      div_le_div_of_nonneg_left hKnn (pow_pos ha1 3)
        (pow_le_pow_left₀ (by linarith) (by linarith : r0.2.2.2 + lamOf q ρ₁ ≤ r0.2.2.2 + r0.2.1) 3)
    have h4 : 1 / (r0.2.2.2 + r0.2.2.1) ^ 3 ≤ 1 / (r0.2.2.2 + lamOf q ρ) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos ha4 3)
        (pow_le_pow_left₀ (by linarith) (by linarith : r0.2.2.2 + lamOf q ρ ≤ r0.2.2.2 + r0.2.2.1) 3)
    unfold cond913 at hcond ⊢
    linarith
  have hineq := hq₀ q hq χ₁ ρ₁ ρ hm hcx hmem hZ hne.symm hconj hcond'
  have hineq' : 0 ≤ p913 (lamOf q ρ₁) (lamOf q ρ) r0.2.2.2 (Kaff r0.2.1)
      + (r0.2.2.2 + lamOf q ρ₁) * ε := hineq
  have h1 : p913 (lamOf q ρ₁) (lamOf q ρ) r0.2.2.2 (Kaff r0.2.1)
      ≤ p913 (lamOf q ρ₁) r0.2.2.1 r0.2.2.2 (Kaff r0.2.1) :=
    p913_mono_lam₀ ha (by linarith) (by linarith) (by linarith) (le_of_lt hlt)
  have h2 : p913 (lamOf q ρ₁) r0.2.2.1 r0.2.2.2 (Kaff r0.2.1)
      ≤ p913 r0.2.1 r0.2.2.1 r0.2.2.2 (Kaff r0.2.1) :=
    p913_mono_lam₁ hlam1nn hlam hhiv ha hK
  have hεval : (r0.2.2.2 + r0.2.1) * ε
      = -(p913 r0.2.1 r0.2.2.1 r0.2.2.2 (Kaff r0.2.1)) / 2 := by
    rw [hεdef]
    field_simp
  have h5 : (r0.2.2.2 + lamOf q ρ₁) * ε ≤ (r0.2.2.2 + r0.2.1) * ε :=
    mul_le_mul_of_nonneg_right (by linarith) hε.le
  linarith [hineq', h1, h2, h5, hεval, hp]

/-- The certified λ₀-bounds for **all 21 printed entries** of Table 8
(`t8certRows ++ t8certRowsExt`). -/
theorem HBTable8_certified_all (h9 : HBLemma9_1)
    (hcert : ∀ r ∈ t8certRows,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0)
    (hcertExt : ∀ r ∈ t8certRowsExt,
      cond913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) ∧
      p913 r.2.1 r.2.2.1 r.2.2.2 (Kaff r.2.1) < 0) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      ∀ r ∈ t8certRows ++ t8certRowsExt, lamOf q ρ₁ ≤ r.2.1 → Lam0BoundOther χ₁ ρ₁ r.2.2.1 := by
  obtain ⟨N, hN⟩ := exists_threshold_of_forall_mem (t8certRows ++ t8certRowsExt)
    (fun r N => ∀ q : ℕ, N ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) → lamOf q ρ₁ ≤ r.2.1 →
      Lam0BoundOther χ₁ ρ₁ r.2.2.1)
    (fun r hr => by
      rcases List.mem_append.mp hr with hr' | hr'
      · obtain ⟨ha, hK, hhiv, hhipos⟩ := t8certRows_facts r hr'
        exact lam0_row_of_lemma9_1_of_facts h9 (hcert r hr') ha hK hhiv hhipos
      · obtain ⟨ha, hK, hhiv, hhipos⟩ := t8certRowsExt_facts r hr'
        exact lam0_row_of_lemma9_1_of_facts h9 (hcertExt r hr') ha hK hhiv hhipos)
    (fun r hr n n' hn hn' q hq => hn' q (le_trans hn hq))
  exact ⟨N, fun q hq _ χ₁ ρ₁ hm hcx r hr hlam => hN r hr q hq χ₁ ρ₁ hm hcx hlam⟩

end Work.ZeroFreeTables
