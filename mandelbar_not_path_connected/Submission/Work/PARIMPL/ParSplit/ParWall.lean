/-
The "wall" vocabulary for the assembly of `ParNormal` from `SplitData`.

Given `S : SplitData d` we have the midpoint `S.m` and the half-difference
`Δ c = S.E c / 2` of the two split fixed points of `F c = (Tsq c)^[5]`.  Write
`G c = Δ c ^ 2`.  This module produces the functions

* `parRho S c` — the continuous nonvanishing function with `m - F(m) = G * ρ`
  (the quotient `Q_c(z) = ((z-m)^2-G) R_c(z)` evaluated at `z = m`, extended to the
  collision locus),
* `Rfun S c w` — `R_c (m + w)`,
* `parH S c` — the continuous unit function `\overline{dir G}`, from the symmetric
  difference quotient of the holomorphic partner `G_c = conj ∘ (T_c)^[5]` of the
  antiholomorphic square root at `m`,
* `parLam S c` — `\overline{parH S c}`, which is `σ · dir G` (`σ` the wall branch sign).

Everything is a finite sum of continuous functions, so no polynomial-division API is used.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.Split
import Submission.Work.PARIMPL.ParSplit.Sqrt
import Submission.Work.PARIMPL.ParSplit.exists_uniform_bounds

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 4000
set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

open Polynomial

/-! ## Polynomials whose coefficients are continuous on a set -/

/-- A family of polynomials whose coefficients are all continuous on `s`. -/
def ContCoeffOn (p : ℂ → Polynomial ℂ) (s : Set ℂ) : Prop := ∀ k, ContinuousOn (fun c => (p c).coeff k) s

theorem coeff_finsetSum_poly (s : Finset ℕ) (g : ℕ → Polynomial ℂ) (k : ℕ) :
    (∑ i ∈ s, g i).coeff k = ∑ i ∈ s, (g i).coeff k := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

theorem contCoeffOn_const (p : Polynomial ℂ) (s : Set ℂ) : ContCoeffOn (fun _ => p) s :=
  fun _ => continuousOn_const

theorem contCoeffOn_C {f : ℂ → ℂ} {s : Set ℂ} (hf : ContinuousOn f s) :
    ContCoeffOn (fun c => Polynomial.C (f c)) s := by
  intro k
  by_cases h : k = 0
  · subst h; simpa using hf
  · simpa [Polynomial.coeff_C, h] using (continuousOn_const : ContinuousOn (fun _ : ℂ => (0:ℂ)) s)

theorem contCoeffOn_X {s : Set ℂ} : ContCoeffOn (fun _ => (Polynomial.X : Polynomial ℂ)) s := by
  intro k
  by_cases h : 1 = k
  · subst h; simpa using (continuousOn_const : ContinuousOn (fun _ : ℂ => (1:ℂ)) s)
  · simpa [Polynomial.coeff_X, h] using (continuousOn_const : ContinuousOn (fun _ : ℂ => (0:ℂ)) s)

theorem contCoeffOn_add {p q : ℂ → Polynomial ℂ} {s : Set ℂ}
    (hp : ContCoeffOn p s) (hq : ContCoeffOn q s) : ContCoeffOn (fun c => p c + q c) s := by
  intro k
  rw [show (fun c => (p c + q c).coeff k)
        = (fun c => (p c).coeff k) + (fun c => (q c).coeff k) from by
      funext c; exact Polynomial.coeff_add _ _ k]
  exact (hp k).add (hq k)

theorem contCoeffOn_sub {p q : ℂ → Polynomial ℂ} {s : Set ℂ}
    (hp : ContCoeffOn p s) (hq : ContCoeffOn q s) : ContCoeffOn (fun c => p c - q c) s := by
  intro k
  rw [show (fun c => (p c - q c).coeff k)
        = (fun c => (p c).coeff k) - (fun c => (q c).coeff k) from by
      funext c; exact Polynomial.coeff_sub _ _ k]
  exact (hp k).sub (hq k)

theorem contCoeffOn_mul {p q : ℂ → Polynomial ℂ} {s : Set ℂ}
    (hp : ContCoeffOn p s) (hq : ContCoeffOn q s) : ContCoeffOn (fun c => p c * q c) s := by
  intro k
  have hfun : (fun c => (p c * q c).coeff k)
      = fun c => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal k,
          (p c).coeff x.1 * (q c).coeff x.2 := by
    funext c; rw [Polynomial.coeff_mul]
  rw [hfun]
  exact continuousOn_finsetSum _ (fun x _ => (hp x.1).mul (hq x.2))

theorem contCoeffOn_pow {p : ℂ → Polynomial ℂ} {s : Set ℂ} (hp : ContCoeffOn p s) (n : ℕ) :
    ContCoeffOn (fun c => (p c) ^ n) s := by
  induction n with
  | zero => simpa using (contCoeffOn_const (1 : Polynomial ℂ) s)
  | succ n ih => simpa [pow_succ] using contCoeffOn_mul ih hp

theorem contCoeffOn_comp {p q : ℂ → Polynomial ℂ} {s : Set ℂ} (hp : ContCoeffOn p s) {N : ℕ}
    (hN : ∀ c, (p c).natDegree ≤ N) (hq : ContCoeffOn q s) :
    ContCoeffOn (fun c => (p c).comp (q c)) s := by
  intro k
  have hsub : ∀ c, (p c).support ⊆ Finset.range (N+1) := by
    intro c n hn
    rw [Finset.mem_range]
    by_contra h
    push Not at h
    exact (Polynomial.mem_support_iff.mp hn)
      (Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hN c; omega))
  have key : ∀ c, (p c).comp (q c)
      = ∑ n ∈ Finset.range (N+1), Polynomial.C ((p c).coeff n) * (q c)^n := by
    intro c
    rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def,
      Finset.sum_subset (hsub c) (fun x _ hxs => by
        have : (p c).coeff x = 0 := by
          by_contra hc
          exact hxs (Polynomial.mem_support_iff.mpr hc)
        simp [this])]
  have hfun : (fun c => ((p c).comp (q c)).coeff k)
      = fun c => ∑ n ∈ Finset.range (N+1), (p c).coeff n * (((q c)^n).coeff k) := by
    funext c
    rw [key c, coeff_finsetSum_poly]
    apply Finset.sum_congr rfl
    intro n _
    rw [Polynomial.coeff_C_mul]
  rw [hfun]
  exact continuousOn_finsetSum _ (fun n _ => (hp n).mul ((contCoeffOn_pow hq n) k))

/-! ## The polynomials of the return map -/

/-- `Tsq c` as a polynomial. -/
noncomputable def TsqPoly (c : ℂ) : Polynomial ℂ :=
  (X ^ 2 + Polynomial.C (star c)) ^ 2 + Polynomial.C c

theorem TsqPoly_eval (c z : ℂ) : (TsqPoly c).eval z = Work.Landing.Tsq c z := by
  simp [TsqPoly, Work.Landing.Tsq, eval_add, eval_pow]

theorem natDegree_TsqPoly (c : ℂ) : (TsqPoly c).natDegree ≤ 4 := by
  rw [TsqPoly]
  have h1 : (X ^ 2 + Polynomial.C (star c) : Polynomial ℂ).natDegree ≤ 2 := by
    calc (X ^ 2 + Polynomial.C (star c) : Polynomial ℂ).natDegree
        ≤ max (X ^ 2 : Polynomial ℂ).natDegree (Polynomial.C (star c) : Polynomial ℂ).natDegree :=
          natDegree_add_le _ _
      _ ≤ 2 := by rw [natDegree_X_pow, natDegree_C]; simp
  calc ((X ^ 2 + Polynomial.C (star c)) ^ 2 + Polynomial.C c : Polynomial ℂ).natDegree
      ≤ max ((X ^ 2 + Polynomial.C (star c)) ^ 2 : Polynomial ℂ).natDegree (Polynomial.C c : Polynomial ℂ).natDegree :=
        natDegree_add_le _ _
    _ ≤ 4 := by
        rw [natDegree_C]
        refine max_le ?_ (by simp)
        calc ((X ^ 2 + Polynomial.C (star c)) ^ 2 : Polynomial ℂ).natDegree
            ≤ 2 * (X ^ 2 + Polynomial.C (star c) : Polynomial ℂ).natDegree := natDegree_pow_le
          _ ≤ 4 := by linarith

/-- `(Tsq c)^[n]` as a polynomial. -/
noncomputable def iterPoly (c : ℂ) : ℕ → Polynomial ℂ
  | 0 => X
  | (n+1) => (iterPoly c n).comp (TsqPoly c)

theorem iterPoly_eval (c : ℂ) (n : ℕ) (z : ℂ) :
    (iterPoly c n).eval z = (Work.Landing.Tsq c)^[n] z := by
  induction n generalizing z with
  | zero => simp [iterPoly]
  | succ n ih =>
    rw [iterPoly, eval_comp, TsqPoly_eval,
      show (iterPoly c n).eval (Work.Landing.Tsq c z)
          = (Work.Landing.Tsq c)^[n] (Work.Landing.Tsq c z) from ih _,
      Function.iterate_succ_apply]

theorem iterPoly_natDegree_le (c : ℂ) (n : ℕ) : (iterPoly c n).natDegree ≤ 4 ^ n := by
  induction n with
  | zero => simp [iterPoly]
  | succ n ih =>
    rw [iterPoly]
    calc ((iterPoly c n).comp (TsqPoly c)).natDegree
        ≤ (iterPoly c n).natDegree * (TsqPoly c).natDegree := natDegree_comp_le
      _ ≤ 4 ^ n * 4 := Nat.mul_le_mul ih (natDegree_TsqPoly c)
      _ = 4 ^ (n+1) := by ring

theorem contCoeffOn_TsqPoly (s : Set ℂ) : ContCoeffOn TsqPoly s := by
  rw [show TsqPoly = fun c : ℂ => (X ^ 2 + Polynomial.C (star c)) ^ 2 + Polynomial.C c from rfl]
  exact contCoeffOn_add (contCoeffOn_pow (contCoeffOn_add (contCoeffOn_pow contCoeffOn_X 2)
    (contCoeffOn_C continuous_star.continuousOn)) 2) (contCoeffOn_C continuous_id.continuousOn)

theorem contCoeffOn_iterPoly (n : ℕ) (s : Set ℂ) : ContCoeffOn (fun c => iterPoly c n) s := by
  induction n with
  | zero => simpa [iterPoly] using contCoeffOn_X (s := s)
  | succ n ih =>
    rw [show (fun c : ℂ => iterPoly c (n+1)) = fun c => (iterPoly c n).comp (TsqPoly c) from rfl]
    exact contCoeffOn_comp ih (fun c => iterPoly_natDegree_le c n) (contCoeffOn_TsqPoly s)

/-- The polynomial of the second return map `F c = (Tsq c)^[5]`. -/
noncomputable def Fpoly (c : ℂ) : Polynomial ℂ := iterPoly c 5

theorem Fpoly_eval (c z : ℂ) : (Fpoly c).eval z = Work.EL.F c z := iterPoly_eval c 5 z

/-- The polynomial of `F c - id`. -/
noncomputable def Qpoly (c : ℂ) : Polynomial ℂ := Fpoly c - X

theorem Qpoly_eval (c z : ℂ) : (Qpoly c).eval z = Work.EL.F c z - z := by
  simp [Qpoly, Fpoly_eval, eval_sub, eval_X]

theorem contCoeffOn_Qpoly (s : Set ℂ) : ContCoeffOn Qpoly s :=
  contCoeffOn_sub (contCoeffOn_iterPoly 5 s) contCoeffOn_X

theorem natDegree_Qpoly (c : ℂ) : (Qpoly c).natDegree ≤ 1024 := by
  rw [Qpoly]
  calc (Fpoly c - X : Polynomial ℂ).natDegree
      ≤ max (Fpoly c).natDegree (X : Polynomial ℂ).natDegree := natDegree_sub_le _ _
    _ ≤ 1024 := by
        refine max_le ?_ (by simp)
        have := iterPoly_natDegree_le c 5
        simpa [Fpoly] using this

/-- The holomorphic partner `G_c = conj ∘ (T_c)^[5]` of the antiholomorphic square root. -/
noncomputable def Gpoly (c : ℂ) : Polynomial ℂ := (iterPoly c 2) ^ 2 + Polynomial.C (star c)

theorem Gpoly_eval (c u : ℂ) :
    (Gpoly c).eval u = ((Work.Landing.Tsq c)^[2] u) ^ 2 + star c := by
  simp [Gpoly, iterPoly_eval, eval_add, eval_pow]

theorem natDegree_Gpoly (c : ℂ) : (Gpoly c).natDegree ≤ 32 := by
  rw [Gpoly]
  calc ((iterPoly c 2) ^ 2 + Polynomial.C (star c) : Polynomial ℂ).natDegree
      ≤ max ((iterPoly c 2) ^ 2 : Polynomial ℂ).natDegree (Polynomial.C (star c) : Polynomial ℂ).natDegree :=
        natDegree_add_le _ _
    _ ≤ 32 := by
        rw [natDegree_C]
        refine max_le ?_ (by simp)
        calc ((iterPoly c 2) ^ 2 : Polynomial ℂ).natDegree
            ≤ 2 * (iterPoly c 2).natDegree := natDegree_pow_le
          _ ≤ 32 := by
              have := iterPoly_natDegree_le c 2
              norm_num at this ⊢
              omega

theorem contCoeffOn_Gpoly (s : Set ℂ) : ContCoeffOn Gpoly s :=
  contCoeffOn_add (contCoeffOn_pow (contCoeffOn_iterPoly 2 s) 2)
    (contCoeffOn_C continuous_star.continuousOn)

theorem natDegree_Gpoly_le (c : ℂ) : (Gpoly c).natDegree ≤ 1024 :=
  le_trans (natDegree_Gpoly c) (by norm_num)

/-! ## The wall data -/

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- Degree bound for `Q_c` and its shifts. -/
abbrev wallN : ℕ := 4 ^ 5

/-- `G c`, the square of the half-difference of the two split fixed points. -/
noncomputable def Gc (S : SplitData d) (c : ℂ) : ℂ := (S.E c / 2) ^ 2

theorem continuousOn_Gc (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ) :
    ContinuousOn (Gc S) (ball c₀ ρ) := by
  unfold Gc
  exact ((S.cont_E.mono (ball_subset_ball hρ)).div_const 2).pow 2

/-- `Q_c` shifted to `S.m c`. -/
noncomputable def Phi (S : SplitData d) (c : ℂ) : Polynomial ℂ :=
  (Qpoly c).comp (X + Polynomial.C (S.m c))

/-- The coefficients of `Q_c (S.m c + ·)`. -/
noncomputable def phi (S : SplitData d) (c : ℂ) (l : ℕ) : ℂ := (Phi S c).coeff l

/-- The coefficients of `R_c (S.m c + ·)`, `R_c` the quotient of `Q_c` by `(X - m)^2 - G`. -/
noncomputable def psi (S : SplitData d) (c : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (wallN + 1), (Gc S c) ^ j * phi S c (k + 2 * j + 2)

/-- `R_c (S.m c + w)`. -/
noncomputable def Rfun (S : SplitData d) (c : ℂ) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (wallN + 1), psi S c k * w ^ k

/-- `R_c (S.m c + ·)` as a polynomial. -/
noncomputable def Rpoly (S : SplitData d) (c : ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (wallN + 1), Polynomial.C (psi S c k) * X ^ k

/-- The continuous nonvanishing function `ρ` with `S.m c - F c (S.m c) = G c * ρ c`. -/
noncomputable def parRho (S : SplitData d) (c : ℂ) : ℂ := psi S c 0

/-- `G_c` shifted to `S.m c`. -/
noncomputable def Gam (S : SplitData d) (c : ℂ) : Polynomial ℂ :=
  (Gpoly c).comp (X + Polynomial.C (S.m c))

/-- The coefficients of `G_c (S.m c + ·)`. -/
noncomputable def gam (S : SplitData d) (c : ℂ) (l : ℕ) : ℂ := (Gam S c).coeff l

/-- The symmetric difference quotient `(G_c(m+Δ) - G_c(m-Δ))/(2Δ)`. -/
noncomputable def parH (S : SplitData d) (c : ℂ) : ℂ :=
  ∑ l ∈ Finset.range (wallN + 1),
    (if l % 2 = 1 then gam S c l * (S.E c / 2) ^ (l - 1) else 0)

/-- `σ · dir G`, the branch-corrected direction of `G`. -/
noncomputable def parLam (S : SplitData d) (c : ℂ) : ℂ := star (parH S c)

/-- The branch sign of the collision locus: `-1` where the antiholomorphic square root swaps
the two split fixed points, `+1` where it fixes them. -/
noncomputable def parSigma (S : SplitData d) (c : ℂ) : ℝ :=
  if gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2 then -1 else 1

theorem contCoeffOn_Phi (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ) : ContCoeffOn (Phi S) (ball c₀ ρ) := by
  have h1 : ContCoeffOn (fun c : ℂ => X + Polynomial.C (S.m c)) (ball c₀ ρ) :=
    contCoeffOn_add contCoeffOn_X
      (contCoeffOn_C (S.cont_m.mono (ball_subset_ball hρ)))
  exact contCoeffOn_comp (N := 1024) (contCoeffOn_Qpoly _)
    (fun c => le_trans (natDegree_Qpoly c) (by norm_num [wallN])) h1

theorem continuousOn_phi (S : SplitData d) (l : ℕ) {ρ : ℝ} (hρ : ρ ≤ S.ρ) :
    ContinuousOn (fun c => phi S c l) (ball c₀ ρ) :=
  (contCoeffOn_Phi S hρ) l

theorem continuousOn_psi (S : SplitData d) (k : ℕ) {ρ : ℝ} (hρ : ρ ≤ S.ρ) :
    ContinuousOn (fun c => psi S c k) (ball c₀ ρ) := by
  unfold psi
  exact continuousOn_finsetSum _ (fun j _ => ((continuousOn_Gc S hρ).pow j).mul
    (continuousOn_phi S _ hρ))

theorem continuousOn_Rfun (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ) :
    ContinuousOn (fun p : ℂ × ℂ => Rfun S p.1 p.2) (ball c₀ ρ ×ˢ Set.univ) := by
  unfold Rfun
  refine continuousOn_finsetSum _ (fun k _ => ?_)
  exact ((continuousOn_psi S k hρ).comp continuousOn_fst (fun x hx => hx.1)).mul
    (continuousOn_snd.pow k)

theorem continuousOn_parRho (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ) :
    ContinuousOn (parRho S) (ball c₀ ρ) := continuousOn_psi S 0 hρ

theorem contCoeffOn_Gam (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ) : ContCoeffOn (Gam S) (ball c₀ ρ) := by
  have h1 : ContCoeffOn (fun c : ℂ => X + Polynomial.C (S.m c)) (ball c₀ ρ) :=
    contCoeffOn_add contCoeffOn_X (contCoeffOn_C (S.cont_m.mono (ball_subset_ball hρ)))
  exact contCoeffOn_comp (N := 1024) (contCoeffOn_Gpoly _)
    (fun c => le_trans (natDegree_Gpoly_le c) (by norm_num [wallN])) h1

theorem continuousOn_gam (S : SplitData d) (l : ℕ) {ρ : ℝ} (hρ : ρ ≤ S.ρ) :
    ContinuousOn (fun c => gam S c l) (ball c₀ ρ) :=
  (contCoeffOn_Gam S hρ) l

theorem continuousOn_parH (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ) :
    ContinuousOn (parH S) (ball c₀ ρ) := by
  unfold parH
  refine continuousOn_finsetSum _ (fun l _ => ?_)
  by_cases h : l % 2 = 1
  · simp only [h, if_true]
    exact (continuousOn_gam S l hρ).mul ((S.cont_E.mono (ball_subset_ball hρ)).div_const 2 |>.pow (l-1))
  · simp only [h, if_false]
    exact continuousOn_const

theorem continuousOn_parLam (S : SplitData d) {ρ : ℝ} (hρ : ρ ≤ S.ρ) :
    ContinuousOn (parLam S) (ball c₀ ρ) :=
  (continuousOn_parH S hρ).star


/-! ## The chart of the parameter normal form, built from the wall data -/

/-- The continuous unit function `u₀` with `u₀ ^ 2 = σ · dir G · dir(ρ)^2`; it is the value
`h c 0` of the normalized germ. -/
noncomputable def parU0 (S : SplitData d) (c : ℂ) : ℂ :=
  Complex.sqrt (parLam S c * (parRho S c) ^ 2 / ‖parRho S c‖ ^ 2)

/-- The chart scale `s c = u₀ c / ρ c`. -/
noncomputable def parS (S : SplitData d) (c : ℂ) : ℂ := parU0 S c / parRho S c

/-- `a c ^ 2`, the (continuous, real) discriminant: `σ · |G| · |ρ|^2`. -/
noncomputable def parA2 (S : SplitData d) (c : ℂ) : ℝ :=
  parSigma S c * ‖Gc S c‖ * ‖parRho S c‖ ^ 2

/-- The chosen square root of `parA2`. -/
noncomputable def parA (S : SplitData d) (c : ℂ) : ℂ := realSqrt (parA2 S c)

/-- The positive scale `λ` on `Nm`. -/
noncomputable def parLamReal (S : SplitData d) (c : ℂ) : ℝ := Real.sqrt ‖parA2 S c‖

/-- The germ of the normal form: `h c ζ = s c · R_c (m c + s c ζ)`. -/
noncomputable def parHgerm (S : SplitData d) (c ζ : ℂ) : ℂ := parS S c * Rfun S c (parS S c * ζ)

/-- The linear coefficient of the germ. -/
noncomputable def parH1 (S : SplitData d) (c : ℂ) : ℂ := (parS S c) ^ 2 * psi S c 1

/-- The correction constant of the approximate Écalle coordinate. -/
noncomputable def parKappa (S : SplitData d) (c : ℂ) : ℂ :=
  parHgerm S c 0 - parH1 S c / parHgerm S c 0


end Work.PARIMPL.ParSplit
