import Mathlib
import Submission.Work.Q44Geom.defs

set_option autoImplicit false
set_option linter.unusedVariables false

open MvPolynomial

noncomputable section

namespace Work.Q44Geom

/-! ## Auxiliary material for `gcdOne` -/

section Basic

/-- The polynomial `Σ_k (L e_k) X_k` attached to a linear functional on `ℚ^5`. -/
def linOf (L : (Fin 5 → ℚ) →ₗ[ℚ] ℚ) : MvPolynomial (Fin 5) ℚ :=
  ∑ k : Fin 5, C (L (Pi.single k 1)) * X k

lemma pi_eq_sum_single (y : Fin 5 → ℚ) :
    (∑ k : Fin 5, y k • Pi.single k (1 : ℚ)) = y := by
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one]
  · intro k _ hk
    have h0 : (Pi.single k (1 : ℚ) : Fin 5 → ℚ) i = 0 := by
      rw [Pi.single_eq_of_ne' hk]
    rw [h0, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma eval_linOf (L : (Fin 5 → ℚ) →ₗ[ℚ] ℚ) (y : Fin 5 → ℚ) : eval y (linOf L) = L y := by
  have h1 : eval y (linOf L) = ∑ k : Fin 5, L (Pi.single k 1) * y k := by
    simp only [linOf, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have h2 : L y = ∑ k : Fin 5, L (Pi.single k 1) * y k := by
    conv_lhs => rw [← pi_eq_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, smul_eq_mul]
    ring
  rw [h1, h2]

lemma algebraMap_rat_mvpoly (σ : Type*) (r : ℚ) :
    (algebraMap ℚ (MvPolynomial σ ℚ)) r = (C r : MvPolynomial σ ℚ) := by
  rw [← MvPolynomial.C_eq_algebraMap ℚ σ]

lemma algebraMap_rat_twoBlock (r : ℚ) :
    (algebraMap ℚ (MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ))) r
      = C (C r : MvPolynomial (Fin 3) ℚ) := by
  rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin 3) ℚ)
        (MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ)),
      ← MvPolynomial.C_eq_algebraMap (MvPolynomial (Fin 3) ℚ) (Fin 2),
      ← MvPolynomial.C_eq_algebraMap ℚ (Fin 3)]

lemma eval_aeval_eval {σ : Type*} (g : σ → MvPolynomial (Fin 5) ℚ) (q : MvPolynomial σ ℚ)
    (y : Fin 5 → ℚ) :
    eval y (MvPolynomial.aeval g q) = eval (fun a => eval y (g a)) q := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.aeval_C, algebraMap_rat_mvpoly (Fin 5) a, MvPolynomial.eval_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
      simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

end Basic

/-! ## `Pref` -/

section Pref

/-- `Pref n G`: every nonzero `u`-coefficient of `G` sits at `u`-degree `≤ n` and is a form of
degree `n - |s|` in the `p`-variables. -/
def Pref (n : ℕ) (G : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ)) : Prop :=
  ∀ s : Fin 2 →₀ ℕ, G.coeff s ≠ 0 →
    Finsupp.degree s ≤ n ∧ (G.coeff s).IsHomogeneous (n - Finsupp.degree s)

lemma pref_zero (n : ℕ) : Pref n (0 : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ)) := by
  intro s hs
  exact absurd rfl hs

lemma pref_C_aux (n : ℕ) (g : MvPolynomial (Fin 3) ℚ) (hg : g.IsHomogeneous n) :
    Pref n (C g : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ)) := by
  intro s hs
  rw [MvPolynomial.coeff_C] at hs
  have hs0 : (0 : Fin 2 →₀ ℕ) = s := by
    by_contra h
    rw [if_neg h] at hs
    exact hs rfl
  rw [← hs0] at *
  constructor
  · simp
  · simpa using hg

lemma pref_one : Pref 0 (1 : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ)) := by
  have h : (1 : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ))
      = C (1 : MvPolynomial (Fin 3) ℚ) := (map_one (C : MvPolynomial (Fin 3) ℚ →+* _)).symm
  rw [h]
  exact pref_C_aux 0 (1 : MvPolynomial (Fin 3) ℚ) (isHomogeneous_one (Fin 3) ℚ)

lemma pref_X (j : Fin 2) :
    Pref 1 (X j : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ)) := by
  intro s hs
  rw [MvPolynomial.coeff_X] at hs
  have hs0 : (Finsupp.single j 1 : Fin 2 →₀ ℕ) = s := by
    by_contra h
    rw [if_neg h] at hs
    exact hs rfl
  rw [← hs0] at *
  constructor
  · rw [Finsupp.degree_single]
  · rw [Finsupp.degree_single, MvPolynomial.coeff_X]
    simpa using (isHomogeneous_one (Fin 3) ℚ)

lemma pref_add {n : ℕ} {G H : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ)}
    (hG : Pref n G) (hH : Pref n H) : Pref n (G + H) := by
  intro s hs
  rw [MvPolynomial.coeff_add] at hs ⊢
  by_cases hG0 : G.coeff s = 0
  · rw [hG0, zero_add] at hs ⊢
    exact hH s hs
  · by_cases hH0 : H.coeff s = 0
    · rw [hH0, add_zero] at hs ⊢
      exact hG s hG0
    · obtain ⟨hd1, hh1⟩ := hG s hG0
      obtain ⟨hd2, hh2⟩ := hH s hH0
      exact ⟨hd1, IsHomogeneous.add hh1 hh2⟩

lemma pref_mul {m n : ℕ} {G H : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ)}
    (hG : Pref m G) (hH : Pref n H) : Pref (m + n) (G * H) := by
  intro s hs
  rw [MvPolynomial.coeff_mul] at hs
  obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  have hxs : x.1 + x.2 = s := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have h1 : G.coeff x.1 ≠ 0 := by
    intro h; exact hxne (by rw [h, zero_mul])
  have h2 : H.coeff x.2 ≠ 0 := by
    intro h; exact hxne (by rw [h, mul_zero])
  obtain ⟨hd1, hh1⟩ := hG x.1 h1
  obtain ⟨hd2, hh2⟩ := hH x.2 h2
  have hdeg : Finsupp.degree s = Finsupp.degree x.1 + Finsupp.degree x.2 := by
    rw [← hxs, map_add]
  constructor
  · rw [hdeg]; omega
  · rw [MvPolynomial.coeff_mul]
    refine IsHomogeneous.sum _ _ _ (fun y hy => ?_)
    by_cases hy1 : G.coeff y.1 = 0
    · rw [hy1, zero_mul]
      exact isHomogeneous_zero (Fin 3) ℚ _
    · by_cases hy2 : H.coeff y.2 = 0
      · rw [hy2, mul_zero]
        exact isHomogeneous_zero (Fin 3) ℚ _
      · obtain ⟨hd1', hh1'⟩ := hG y.1 hy1
        obtain ⟨hd2', hh2'⟩ := hH y.2 hy2
        have hys : y.1 + y.2 = s := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
        have hdegy : Finsupp.degree s = Finsupp.degree y.1 + Finsupp.degree y.2 := by
          rw [← hys, map_add]
        have hmul := IsHomogeneous.mul hh1' hh2'
        rw [show (m - Finsupp.degree y.1) + (n - Finsupp.degree y.2)
              = m + n - Finsupp.degree s from by omega] at hmul
        exact hmul

lemma pref_sum {ι : Type*} (S : Finset ι)
    (F : ι → MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ))
    (n : ℕ) (h : ∀ i ∈ S, Pref n (F i)) : Pref n (∑ i ∈ S, F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact pref_zero n
  | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      exact pref_add (h a (Finset.mem_insert_self a S))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma pref_pow {m : ℕ} {G : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ)} (hG : Pref m G) :
    ∀ k : ℕ, Pref (m * k) (G ^ k) := by
  intro k
  induction k with
  | zero => simpa using pref_one
  | succ k ih =>
      rw [pow_succ, Nat.mul_succ]
      exact pref_mul ih hG

end Pref

/-! ## `sigma` of a homogeneous polynomial -/

section Sigma

lemma pref_sigma_X (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ) (i : Fin 5) :
    Pref 1 (sigma w b₁ b₂ (X i)) := by
  have h : sigma w b₁ b₂ (X i) = C (linForm w i) + X (0 : Fin 2) * C (C (b₁ i))
      + X (1 : Fin 2) * C (C (b₂ i)) := by
    rw [sigma, MvPolynomial.aeval_X]
  rw [h]
  refine pref_add (pref_add ?_ ?_) ?_
  · refine pref_C_aux 1 (linForm w i) ?_
    rw [linForm]
    refine IsHomogeneous.sum _ _ _ (fun a _ => ?_)
    have h1 : (C (w a i) : MvPolynomial (Fin 3) ℚ).IsHomogeneous 0 :=
      isHomogeneous_C (Fin 3) (w a i)
    have h2 : (X a : MvPolynomial (Fin 3) ℚ).IsHomogeneous 1 := isHomogeneous_X ℚ a
    simpa using IsHomogeneous.mul h1 h2
  · exact pref_mul (pref_X (0 : Fin 2))
      (pref_C_aux 0 (C (b₁ i) : MvPolynomial (Fin 3) ℚ) (isHomogeneous_C (Fin 3) (b₁ i)))
  · exact pref_mul (pref_X (1 : Fin 2))
      (pref_C_aux 0 (C (b₂ i) : MvPolynomial (Fin 3) ℚ) (isHomogeneous_C (Fin 3) (b₂ i)))

lemma pref_sigma_monomial (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (d : Fin 5 →₀ ℕ) (c : ℚ) :
    Pref (Finsupp.degree d) (sigma w b₁ b₂ (MvPolynomial.monomial d c)) := by
  have hprod : Pref (∑ i ∈ d.support, d i)
      (∏ i ∈ d.support, (sigma w b₁ b₂ (X i)) ^ (d i)) := by
    induction d.support using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact pref_one
    | insert a S ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha]
        have hpowa : Pref (d a) (sigma w b₁ b₂ (X a) ^ (d a)) := by
          simpa using pref_pow (pref_sigma_X w b₁ b₂ a) (d a)
        exact pref_mul hpowa ih
  have hmain := pref_mul (pref_C_aux 0 (C c : MvPolynomial (Fin 3) ℚ)
    (isHomogeneous_C (Fin 3) c)) hprod
  rw [sigma, MvPolynomial.aeval_monomial, algebraMap_rat_twoBlock c]
  rw [show Finsupp.degree d = ∑ i ∈ d.support, d i from Finsupp.degree_apply d]
  simp only [sigma, MvPolynomial.aeval_X, Finsupp.prod, zero_add] at hmain ⊢
  exact hmain

lemma pref_sigma (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (f : MvPolynomial (Fin 5) ℚ) (hf : f.IsHomogeneous 4) :
    Pref 4 (sigma w b₁ b₂ f) := by
  rw [MvPolynomial.as_sum f, map_sum]
  refine pref_sum _ _ 4 (fun d hd => ?_)
  have hdeg : Finsupp.degree d = 4 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hd) (MvPolynomial.IsHomogeneous.coeff_eq_zero hf h)
  have h' := pref_sigma_monomial w b₁ b₂ d (f.coeff d)
  rwa [hdeg] at h'

end Sigma

/-! ## Evaluation lemmas for `sigma` -/

section EvalSigma

lemma eval_sigma_X (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ) (i : Fin 5)
    (p : Fin 3 → ℚ) (u : Fin 2 → ℚ) :
    eval p (eval (fun j : Fin 2 => C (u j)) (sigma w b₁ b₂ (X i)))
      = substPoint w b₁ b₂ p u i := by
  rw [sigma, MvPolynomial.aeval_X]
  simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, eval_linForm,
    substPoint]

lemma eval_sigma (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ) (f : MvPolynomial (Fin 5) ℚ)
    (p : Fin 3 → ℚ) (u : Fin 2 → ℚ) :
    eval p (eval (fun j : Fin 2 => C (u j)) (sigma w b₁ b₂ f))
      = eval (substPoint w b₁ b₂ p u) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      simp only [sigma, MvPolynomial.aeval_C, algebraMap_rat_twoBlock a, MvPolynomial.eval_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
      rw [show sigma w b₁ b₂ (f * X i) = sigma w b₁ b₂ f * sigma w b₁ b₂ (X i) from by
            rw [map_mul],
        map_mul, map_mul, map_mul, hf, MvPolynomial.eval_X,
        eval_sigma_X w b₁ b₂ i p u]

lemma eval_sigma_eq_sum (G : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ)) (p : Fin 3 → ℚ)
    (u : Fin 2 → ℚ) :
    eval p (eval (fun j : Fin 2 => C (u j)) G)
      = ∑ s ∈ G.support, eval p (G.coeff s) * ∏ j ∈ s.support, (u j) ^ (s j) := by
  rw [MvPolynomial.eval_eq (X := fun j : Fin 2 => C (u j)) G, map_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [map_mul, map_prod]
  congr 1
  exact Finset.prod_congr rfl (fun j _ => by rw [map_pow, MvPolynomial.eval_C])

lemma eval_map_eval_eq (G : MvPolynomial (Fin 2) (MvPolynomial (Fin 3) ℚ)) (u : Fin 2 → ℚ) :
    eval u (MvPolynomial.map (MvPolynomial.eval (0 : Fin 3 → ℚ)) G)
      = eval (0 : Fin 3 → ℚ) (eval (fun j : Fin 2 => C (u j)) G) := by
  induction G using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.map_C, MvPolynomial.eval_C]
  | add G H hG hH => simp only [map_add, hG, hH]
  | mul_X G j hG =>
      simp only [map_mul, hG, MvPolynomial.map_X, MvPolynomial.eval_X, MvPolynomial.eval_C]

lemma eq_C_eval_zero_of_isHomogeneous_zero (g : MvPolynomial (Fin 3) ℚ)
    (hg : g.IsHomogeneous 0) :
    g = C (eval (0 : Fin 3 → ℚ) g) := by
  have hcoeff : ∀ d : Fin 3 →₀ ℕ, d ≠ 0 → g.coeff d = 0 := by
    intro d hd
    refine MvPolynomial.IsHomogeneous.coeff_eq_zero hg (fun h => hd ?_)
    exact (Finsupp.degree_eq_zero_iff d).mp h
  have h1 : g = C (g.coeff 0) := by
    ext d
    rw [MvPolynomial.coeff_C]
    by_cases hd : d = 0
    · subst hd; simp
    · rw [if_neg (fun h => hd h.symm), hcoeff d hd]
  rw [h1, MvPolynomial.eval_C]

end EvalSigma

/-! ## The coefficient of `sigma` as a level form -/

lemma coeff_sigma_eq_levelForm (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (f : MvPolynomial (Fin 5) ℚ) (s : Fin 2 →₀ ℕ) :
    (sigma w b₁ b₂ f).coeff s = levelForm w b₁ b₂ f (fun j => s j) := by
  rw [levelForm]
  congr 1
  exact (Equiv.symm_apply_apply Finsupp.equivFunOnFinite s).symm

/-! ## Vanishing of the `u`-coefficients of degree `≥ 4` -/

section Vanish

lemma coeff_sigma_eq_zero_of_four_le (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (f : MvPolynomial (Fin 5) ℚ) (hf : f.IsHomogeneous 4)
    (hℓ : ∀ u : Fin 2 → ℚ, eval (u 0 • b₁ + u 1 • b₂) f = 0)
    (s : Fin 2 →₀ ℕ) (hs : 4 ≤ Finsupp.degree s) :
    (sigma w b₁ b₂ f).coeff s = 0 := by
  have hpref := pref_sigma w b₁ b₂ f hf
  by_cases hne : (sigma w b₁ b₂ f).coeff s = 0
  · exact hne
  · obtain ⟨hd, hhom⟩ := hpref s hne
    have hzero : eval (0 : Fin 3 → ℚ) ((sigma w b₁ b₂ f).coeff s) = 0 := by
      have hmap : MvPolynomial.map (MvPolynomial.eval (0 : Fin 3 → ℚ)) (sigma w b₁ b₂ f) = 0 := by
        refine MvPolynomial.funext (fun u => ?_)
        rw [eval_map_eval_eq, eval_sigma]
        have hsub : substPoint w b₁ b₂ (0 : Fin 3 → ℚ) u = u 0 • b₁ + u 1 • b₂ := by
          funext i
          simp [substPoint]
        rw [hsub, hℓ u]
        simp
      have hthis := congrArg (fun (g : MvPolynomial (Fin 2) ℚ) => g.coeff s) hmap
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at hthis
      exact hthis
    have heq : 4 - Finsupp.degree s = 0 := by omega
    have hconst := eq_C_eval_zero_of_isHomogeneous_zero _ (by simpa [heq] using hhom)
    rw [hconst, hzero]
    simp

end Vanish

/-! ## The assembly -/

section Assembly

lemma substPoint_eq_of_recon (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (P : Fin 3 → (Fin 5 → ℚ) →ₗ[ℚ] ℚ) (Q : Fin 2 → (Fin 5 → ℚ) →ₗ[ℚ] ℚ)
    (hrecon : ∀ y : Fin 5 → ℚ,
      (∑ a : Fin 3, (P a y) • w a) + (∑ j : Fin 2, (Q j y) • ![b₁, b₂] j) = y)
    (y : Fin 5 → ℚ) :
    substPoint w b₁ b₂ (fun a => P a y) (fun j => Q j y) = y := by
  conv_rhs => rw [← hrecon y]
  funext i
  simp only [substPoint, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma eval_aeval_linOf (P : Fin 3 → (Fin 5 → ℚ) →ₗ[ℚ] ℚ) (q : MvPolynomial (Fin 3) ℚ)
    (y : Fin 5 → ℚ) :
    eval y (MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) q) = eval (fun a => P a y) q := by
  rw [eval_aeval_eval]
  rw [show (fun a : Fin 3 => eval y (linOf (P a))) = (fun a : Fin 3 => P a y) from
    funext (fun a => eval_linOf (P a) y)]

lemma aeval_linOf_invariant (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (P : Fin 3 → (Fin 5 → ℚ) →ₗ[ℚ] ℚ)
    (hPb : ∀ (a : Fin 3) (j : Fin 2), P a (![b₁, b₂] j) = 0)
    (q : MvPolynomial (Fin 3) ℚ) (a b : ℚ) (x : Fin 5 → ℚ) :
    eval (x + a • b₁ + b • b₂) (MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) q)
      = eval x (MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) q) := by
  rw [eval_aeval_linOf, eval_aeval_linOf]
  rw [show (fun a' : Fin 3 => P a' (x + a • b₁ + b • b₂)) = (fun a' : Fin 3 => P a' x) from by
    funext a'
    have hb1 : P a' b₁ = 0 := by simpa using hPb a' 0
    have hb2 : P a' b₂ = 0 := by simpa using hPb a' 1
    rw [map_add, map_add, map_smul, map_smul, hb1, hb2, smul_zero, smul_zero, add_zero,
      add_zero]]

lemma not_isUnit_aeval_linOf (w : Fin 3 → Fin 5 → ℚ)
    (P : Fin 3 → (Fin 5 → ℚ) →ₗ[ℚ] ℚ)
    (hPw : ∀ (a a' : Fin 3), P a (w a') = if a = a' then 1 else 0)
    (h : MvPolynomial (Fin 3) ℚ)
    (hh : ¬ IsUnit h) :
    ¬ IsUnit (MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) h) := by
  intro hunit
  obtain ⟨c, hcunit, hc⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced (R := ℚ)).mp hunit
  refine hh ((MvPolynomial.isUnit_iff_eq_C_of_isReduced (R := ℚ)).mpr ⟨c, hcunit, ?_⟩)
  refine MvPolynomial.funext (fun pvec => ?_)
  have hval : ∀ a : Fin 3, P a (∑ a' : Fin 3, (pvec a') • w a') = pvec a := by
    intro a
    rw [map_sum, Finset.sum_eq_single a]
    · rw [map_smul, hPw a a, if_pos rfl, smul_eq_mul, mul_one]
    · intro a' _ ha'
      rw [map_smul, hPw a a', if_neg (Ne.symm ha'), smul_eq_mul, mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ a) hmem
  have h1 : eval (∑ a' : Fin 3, (pvec a') • w a')
      (MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) h) = eval pvec h := by
    rw [eval_aeval_linOf,
      show (fun a : Fin 3 => P a (∑ a' : Fin 3, (pvec a') • w a')) = pvec from funext hval]
  rw [← h1, hc, MvPolynomial.eval_C, MvPolynomial.eval_C]

theorem gcdOne_aux (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (P : Fin 3 → (Fin 5 → ℚ) →ₗ[ℚ] ℚ) (Q : Fin 2 → (Fin 5 → ℚ) →ₗ[ℚ] ℚ)
    (hPw : ∀ (a a' : Fin 3), P a (w a') = if a = a' then 1 else 0)
    (hPb : ∀ (a : Fin 3) (j : Fin 2), P a (![b₁, b₂] j) = 0)
    (hrecon : ∀ y : Fin 5 → ℚ,
      (∑ a : Fin 3, (P a y) • w a) + (∑ j : Fin 2, (Q j y) • ![b₁, b₂] j) = y)
    (f : MvPolynomial (Fin 5) ℚ) (hf : f.IsHomogeneous 4)
    (hirr : Irreducible f)
    (hnd : ¬ ∀ a b : ℚ, ∀ x : Fin 5 → ℚ,
      MvPolynomial.eval (x + a • b₁ + b • b₂) f = MvPolynomial.eval x f)
    (hℓ : ∀ u : Fin 2 → ℚ, MvPolynomial.eval (u 0 • b₁ + u 1 • b₂) f = 0)
    (h : MvPolynomial (Fin 3) ℚ)
    (hdiv : ∀ i ∈ Finset.range 4, ∀ j ∈ Finset.range 4, i + j ≤ 3 →
      h ∣ levelForm w b₁ b₂ f ![i, j]) :
    IsUnit h := by
  have hcof : ∀ s : Fin 2 →₀ ℕ, Finsupp.degree s ≤ 3 → h ∣ (sigma w b₁ b₂ f).coeff s := by
    intro s hs
    have h0 : s 0 ≤ 3 := by have := Finsupp.le_degree 0 s; omega
    have h1 : s 1 ≤ 3 := by have := Finsupp.le_degree 1 s; omega
    have hmem0 : s 0 ∈ Finset.range 4 := by rw [Finset.mem_range]; omega
    have hmem1 : s 1 ∈ Finset.range 4 := by rw [Finset.mem_range]; omega
    have hsum : Finsupp.degree s = s 0 + s 1 := by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    have hfun : (fun j : Fin 2 => s j) = ![s 0, s 1] := by
      funext j; fin_cases j <;> simp
    rw [coeff_sigma_eq_levelForm, hfun]
    exact hdiv (s 0) hmem0 (s 1) hmem1 (by omega)
  let Mf : (Fin 2 →₀ ℕ) → MvPolynomial (Fin 3) ℚ := fun s =>
    if hs : Finsupp.degree s ≤ 3 then (hcof s hs).choose else 0
  have hMf : ∀ s : Fin 2 →₀ ℕ, (hs : Finsupp.degree s ≤ 3) →
      (sigma w b₁ b₂ f).coeff s = h * Mf s := by
    intro s hs
    have hspec := (hcof s hs).choose_spec
    simpa [Mf, dif_pos hs] using hspec
  let A : MvPolynomial (Fin 5) ℚ := MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) h
  let B : MvPolynomial (Fin 5) ℚ :=
    ∑ s ∈ (sigma w b₁ b₂ f).support.filter (fun s => Finsupp.degree s ≤ 3),
      MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) (Mf s) *
        ∏ j ∈ s.support, (linOf (Q j)) ^ (s j)
  have hfAB : f = A * B := by
    refine MvPolynomial.funext (fun y => ?_)
    have hy := substPoint_eq_of_recon w b₁ b₂ P Q hrecon y
    have hev1 : eval y f = ∑ s ∈ (sigma w b₁ b₂ f).support,
        eval (fun a => P a y) ((sigma w b₁ b₂ f).coeff s) *
          ∏ j ∈ s.support, (Q j y) ^ (s j) := by
      conv_lhs => rw [← hy]
      rw [← eval_sigma w b₁ b₂ f (fun a => P a y) (fun j => Q j y)]
      exact eval_sigma_eq_sum _ _ _
    have hev2 : (∑ s ∈ (sigma w b₁ b₂ f).support,
        eval (fun a => P a y) ((sigma w b₁ b₂ f).coeff s) *
          ∏ j ∈ s.support, (Q j y) ^ (s j))
        = ∑ s ∈ (sigma w b₁ b₂ f).support.filter (fun s => Finsupp.degree s ≤ 3),
        eval (fun a => P a y) ((sigma w b₁ b₂ f).coeff s) *
          ∏ j ∈ s.support, (Q j y) ^ (s j) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro s hs hsnot
      have h4 : 4 ≤ Finsupp.degree s := by
        by_contra hcon
        exact hsnot (Finset.mem_filter.mpr ⟨hs, by omega⟩)
      rw [coeff_sigma_eq_zero_of_four_le w b₁ b₂ f hf hℓ s h4, map_zero, zero_mul]
    have hev3 : (∑ s ∈ (sigma w b₁ b₂ f).support.filter (fun s => Finsupp.degree s ≤ 3),
        eval (fun a => P a y) ((sigma w b₁ b₂ f).coeff s) *
          ∏ j ∈ s.support, (Q j y) ^ (s j))
        = ∑ s ∈ (sigma w b₁ b₂ f).support.filter (fun s => Finsupp.degree s ≤ 3),
        (eval (fun a => P a y) h * eval (fun a => P a y) (Mf s)) *
          ∏ j ∈ s.support, (Q j y) ^ (s j) := by
      refine Finset.sum_congr rfl (fun s hs => ?_)
      have hs3 : Finsupp.degree s ≤ 3 := (Finset.mem_filter.mp hs).2
      rw [hMf s hs3, map_mul]
    have hev4 : (∑ s ∈ (sigma w b₁ b₂ f).support.filter (fun s => Finsupp.degree s ≤ 3),
        (eval (fun a => P a y) h * eval (fun a => P a y) (Mf s)) *
          ∏ j ∈ s.support, (Q j y) ^ (s j))
        = eval (fun a => P a y) h *
        ∑ s ∈ (sigma w b₁ b₂ f).support.filter (fun s => Finsupp.degree s ≤ 3),
          eval (fun a => P a y) (Mf s) * ∏ j ∈ s.support, (Q j y) ^ (s j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by ring)
    have hA : eval y A = eval (fun a => P a y) h := by
      rw [show A = MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) h from rfl,
        eval_aeval_linOf]
    have hB : eval y B = ∑ s ∈ (sigma w b₁ b₂ f).support.filter (fun s => Finsupp.degree s ≤ 3),
        eval (fun a => P a y) (Mf s) * ∏ j ∈ s.support, (Q j y) ^ (s j) := by
      rw [show B = ∑ s ∈ (sigma w b₁ b₂ f).support.filter (fun s => Finsupp.degree s ≤ 3),
          MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) (Mf s) *
            ∏ j ∈ s.support, (linOf (Q j)) ^ (s j) from rfl]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [map_mul, eval_aeval_linOf, map_prod]
      congr 1
      exact Finset.prod_congr rfl (fun j _ => by rw [map_pow, eval_linOf])
    rw [map_mul, hA, hB, hev1, hev2, hev3, hev4]
  by_cases hunit : IsUnit h
  · exact hunit
  · exfalso
    have hAne : ¬ IsUnit A := not_isUnit_aeval_linOf w P hPw h hunit
    rcases hirr.isUnit_or_isUnit hfAB with hAu | hBu
    · exact hAne hAu
    · obtain ⟨c, hcunit, hBc⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced (R := ℚ)).mp hBu
      have hAex : A = MvPolynomial.aeval (fun a : Fin 3 => linOf (P a)) h := rfl
      have hfA : f = c • A := by
        rw [hfAB, hBc, mul_comm, MvPolynomial.C_mul']
      refine hnd ?_
      intro a b x
      have hinv := aeval_linOf_invariant w b₁ b₂ P hPb h a b x
      have h1 : eval (x + a • b₁ + b • b₂) A = eval x A := by rw [hAex, hinv]
      have h2 : ∀ z : Fin 5 → ℚ, eval z (c • A) = c * eval z A := by
        intro z
        rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
      rw [hfA, h2 (x + a • b₁ + b • b₂), h2 x, h1]

end Assembly



/-! ## Dual coordinates for the basis `(w, b₁, b₂)` -/

lemma gcdCoordRecon_local (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (hb : LinearIndependent ℚ (Fin.append w ![b₁, b₂])) :
    ∃ (P : Fin 3 → (Fin 5 → ℚ) →ₗ[ℚ] ℚ) (Q : Fin 2 → (Fin 5 → ℚ) →ₗ[ℚ] ℚ),
      (∀ (a a' : Fin 3), P a (w a') = if a = a' then 1 else 0) ∧
      (∀ (a : Fin 3) (j : Fin 2), P a (![b₁, b₂] j) = 0) ∧
      (∀ y : Fin 5 → ℚ,
        (∑ a : Fin 3, (P a y) • w a) + (∑ j : Fin 2, (Q j y) • ![b₁, b₂] j) = y) := by
  classical
  have hcard : Fintype.card (Fin 5) = Module.finrank ℚ (Fin 5 → ℚ) := by
    rw [Module.finrank_fintype_fun_eq_card]
  let bs : Module.Basis (Fin 5) ℚ (Fin 5 → ℚ) :=
    basisOfLinearIndependentOfCardEqFinrank hb hcard
  have hbw : ∀ a : Fin 3, bs (Fin.castAdd 2 a) = w a := by
    intro a
    show basisOfLinearIndependentOfCardEqFinrank hb hcard (Fin.castAdd 2 a) = w a
    rw [coe_basisOfLinearIndependentOfCardEqFinrank hb hcard, Fin.append_left]
  have hbb : ∀ j : Fin 2, bs (Fin.natAdd 3 j) = ![b₁, b₂] j := by
    intro j
    show basisOfLinearIndependentOfCardEqFinrank hb hcard (Fin.natAdd 3 j) = ![b₁, b₂] j
    rw [coe_basisOfLinearIndependentOfCardEqFinrank hb hcard, Fin.append_right]
  refine ⟨fun a => bs.coord (Fin.castAdd 2 a), fun j => bs.coord (Fin.natAdd 3 j), ?_, ?_, ?_⟩
  · intro a a'
    show bs.coord (Fin.castAdd 2 a) (w a') = _
    rw [Module.Basis.coord_apply, ← hbw a', Module.Basis.repr_self_apply]
    by_cases h : a = a'
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc => h (Fin.castAdd_inj.mp hc).symm)]
  · intro a j
    show bs.coord (Fin.castAdd 2 a) (![b₁, b₂] j) = 0
    rw [Module.Basis.coord_apply, ← hbb j, Module.Basis.repr_self_apply]
    rw [if_neg]
    intro hc
    have hv := congrArg Fin.val hc
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  · intro y
    have h5 : (∑ i : Fin (3 + 2), (bs.repr y i) • bs i) = y := Module.Basis.sum_repr bs y
    rw [Fin.sum_univ_add] at h5
    rw [show (∑ i : Fin 3, (bs.repr y (Fin.castAdd 2 i)) • bs (Fin.castAdd 2 i))
          = ∑ i : Fin 3, (bs.coord (Fin.castAdd 2 i) y) • w i from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hbw i, ← Module.Basis.coord_apply]] at h5
    rw [show (∑ i : Fin 2, (bs.repr y (Fin.natAdd 3 i)) • bs (Fin.natAdd 3 i))
          = ∑ i : Fin 2, (bs.coord (Fin.natAdd 3 i) y) • ![b₁, b₂] i from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hbb i, ← Module.Basis.coord_apply]] at h5
    exact h5

/-- The statement requested: the gcd of the level forms of degree `≤ 3` is a unit. -/
theorem gcdOne (b₁ b₂ : Fin 5 → ℚ) (w : Fin 3 → Fin 5 → ℚ)
    (hb : LinearIndependent ℚ (Fin.append w ![b₁, b₂]))
    (hsp : Submodule.span ℚ (Set.range (Fin.append w ![b₁, b₂])) = ⊤)
    (f : MvPolynomial (Fin 5) ℚ) (hf : f.IsHomogeneous 4)
    (hirr : Irreducible f)
    (hnd : ¬ ∀ a b : ℚ, ∀ x : Fin 5 → ℚ,
      MvPolynomial.eval (x + a • b₁ + b • b₂) f = MvPolynomial.eval x f)
    (hℓ : ∀ u : Fin 2 → ℚ, MvPolynomial.eval (u 0 • b₁ + u 1 • b₂) f = 0)
    (h : MvPolynomial (Fin 3) ℚ)
    (hdiv : ∀ i ∈ Finset.range 4, ∀ j ∈ Finset.range 4, i + j ≤ 3 →
      h ∣ Work.Q44Geom.levelForm w b₁ b₂ f ![i, j]) :
    IsUnit h := by
  obtain ⟨P, Q, hPw, hPb, hrecon⟩ := gcdCoordRecon_local w b₁ b₂ hb
  exact gcdOne_aux w b₁ b₂ P Q hPw hPb hrecon f hf hirr hnd hℓ h hdiv

end Work.Q44Geom
