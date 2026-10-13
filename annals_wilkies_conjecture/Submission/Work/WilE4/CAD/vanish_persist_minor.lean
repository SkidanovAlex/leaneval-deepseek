import Mathlib
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.signConst_data
import Submission.Work.WilE4.CAD.Minors
import Submission.Work.WilE4.Poly.spec_pderiv
import Submission.Work.WilE4.CAD.exists_minimal_rootMultiplicity_member
import Submission.Work.WilE4.CAD.rootMultiplicity_gcd
import Submission.Work.WilE4.CAD.disk_roots_card_eventually_const
import Submission.Work.WilE4.CAD.exists_seq_of_not_eventually_nhdsWithin
import Submission.Work.WilE4.CAD.exists_disk_roots_eq_singleton
import Submission.Work.WilE4.CAD.map_ofReal_ne_zero
import Submission.Work.WilE4.CAD.gcd_spec_natDegree_const_on_C
import Submission.Work.WilE4.CAD.gcd_root_along_sequence

/-!
# `Work.WilE4.CAD.vanish_persist_minor` — proof strategy (session notes)

Goal: for a family `P : Fin k → MvPolynomial (Fin (m+1)) ℝ` closed under `∂_m`, with all
coefficient signs and all Sylvester-minor signs constant on `C`, and `x₀ ∈ C`, `t₀ : ℝ`: for
`x ∈ C` close to `x₀` there is `t` close to `t₀` at which *all* members vanishing at `(x₀,t₀)`
vanish.

## The argument

Let `V := {i | (spec (P i) x₀).eval t₀ = 0}` (the "vanishing pattern") and `μ i :=
rootMultiplicity t₀ (spec (P i) x₀)`.

1. **Trivial case.** If every `i ∈ V` has `spec (P i) x₀ = 0`, then by `hcoeff` all its
   coefficients vanish on `C`, so it is the zero polynomial on `C` and any `t` works.

2. **Minimal member.** Otherwise use `exists_minimal_rootMultiplicity_member` to get `i₀ ∈ V`
   with `spec (P i₀) x₀ ≠ 0` and `μ i₀ = 1`, i.e. a *simple* root at `t₀`.

3. **The simple root persists (IVT).** `eventually_exists_root_near_of_simple_root` (below, proved)
   gives a real root `α(x) ∈ (t₀-δ, t₀+δ)` of `spec (P i₀) x` for `x` near `x₀`: the root at
   `x₀` is simple, hence the signs of `spec (P i₀) x₀` at `t₀ ± δ` are opposite, and the signs
   of the fibre at the two fixed points are stable in the parameter (`sign_stable_Icc`).

4. **Uniqueness in the disk.** `disk_roots_card_eventually_const` (proved, module
   `Submission.Work.WilE4.CAD.disk_roots_card_eventually_const`) says that the number of complex
   roots in a disk is locally constant for a family of bounded degree with continuous
   coefficients whose boundary circle avoids the roots at the base point.  Applied to the member
   `i₀` this shows: for `x` near `x₀`, `spec (P i₀) x` has *exactly one* root in the disk, so
   this root is `α(x)` (the real one found in step 3).

5. **Simultaneity.** For `j ∈ V` one must show `α(x)` is also a root of `spec (P j) x`.  The
   natural route is via `gcd (spec (P i₀) x) (spec (P j) x)`, whose `natDegree` is constant on
   `C` (`gcd_spec_natDegree_const_on_C`, from `hmin` + the Sylvester rank formula
   `rank = deg f + deg g - deg gcd`, module `Submission.Work.WilE4.CAD.rank_sylvester_exact`)
   and whose multiplicity at `t₀` is `min 1 (μ j) = 1` (`rootMultiplicity_gcd`).  The missing
   ingredient is that this gcd's root does **not escape to infinity**: `gcd_coeff_continuous`
   is FALSE in general (a common root can escape to infinity while `natDegree (gcd)` stays
   constant — see the counterexample recorded in
   `Submission/Work/WilE4/CAD/gcd_coeff_continuous.lean`).  Under the present hypotheses
   (`hcoeff` + `hmin`) the escaping configuration is excluded, but turning that into a lemma is
   the remaining gap.  A correct statement needs the *subresultant / principal-subresultant*
   data, which is exactly what `hmin` supplies.
-/

namespace Work.WilE4.CAD

open Classical Filter
open scoped Topology

/-- The evaluation map `(x, t) ↦ (spec Q x).eval t` is continuous. -/
theorem continuous_spec_eval_pt {m : ℕ} (Q : MvPolynomial (Fin (m + 1)) ℝ) :
    Continuous fun p : (Fin m → ℝ) × ℝ => (Work.WilE4.spec Q p.1).eval p.2 := by
  have h1 : Continuous fun p : (Fin m → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (m + 1) → ℝ) := by
    rw [continuous_pi_iff]
    intro j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨l, rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc]
      exact (continuous_apply l).comp continuous_fst
    · simp only [Fin.snoc_last]
      exact continuous_snd
  have h2 : Continuous fun p : (Fin m → ℝ) × ℝ =>
      MvPolynomial.eval (Fin.snoc p.1 p.2) Q :=
    (MvPolynomial.continuous_eval (p := Q)).comp h1
  convert h2 using 1
  funext p
  exact Work.WilE4.spec_eval_snoc Q p.1 p.2

/-- If `spec Q x₀` has a simple root at `t₀` and no other root in `[t₀ - δ, t₀ + δ]`, then for
every `x` near `x₀` the fibre `spec Q x` has a root in `(t₀ - δ, t₀ + δ)`. -/
theorem eventually_exists_root_near_of_simple_root {m : ℕ} (Q : MvPolynomial (Fin (m + 1)) ℝ)
    {x₀ : Fin m → ℝ} {t₀ δ : ℝ} (hδ : 0 < δ)
    (hsimple : (Work.WilE4.spec Q x₀).rootMultiplicity t₀ = 1)
    (hnone : ∀ t ∈ Set.Icc (t₀ - δ) (t₀ + δ), t ≠ t₀ → ¬ (Work.WilE4.spec Q x₀).IsRoot t) :
    ∀ᶠ x in nhds x₀, ∃ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), (Work.WilE4.spec Q x).IsRoot t := by
  set f : Polynomial ℝ := Work.WilE4.spec Q x₀ with hf
  have hf0 : f ≠ 0 := by
    rintro h
    rw [h, Polynomial.rootMultiplicity_zero] at hsimple
    exact one_ne_zero hsimple.symm
  -- factor `f = (X - C t₀) * u` with `u` not vanishing on the interval
  obtain ⟨u, hu, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 t₀
  rw [hsimple, pow_one] at hu
  have hu0 : u.eval t₀ ≠ 0 := fun h0 => hndvd ((Polynomial.dvd_iff_isRoot).mpr h0)
  have hun : ∀ z ∈ Set.Icc (t₀ - δ) (t₀ + δ), z ≠ t₀ → u.eval z ≠ 0 := by
    intro z hz hz0 huz
    have hfz : f.eval z = 0 := by
      rw [hu, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, huz,
        mul_zero]
    exact hnone z hz hz0 (Polynomial.IsRoot.def.mpr hfz)
  have hfne : ∀ y ∈ Set.Icc (t₀ - δ) (t₀ + δ), y ≠ t₀ → f.eval y ≠ 0 := by
    intro y hy hy0 h
    exact hnone y hy hy0 (Polynomial.IsRoot.def.mpr h)
  have hne1 : u.eval (t₀ - δ) ≠ 0 := hun _ ⟨by linarith, by linarith⟩ (by linarith)
  have hne2 : u.eval (t₀ + δ) ≠ 0 := hun _ ⟨by linarith, by linarith⟩ (by linarith)
  -- the signs of `u` at the two endpoints agree (otherwise `u` would have a root in between)
  have hpos : 0 < u.eval (t₀ - δ) * u.eval (t₀ + δ) := by
    rcases lt_trichotomy (u.eval (t₀ - δ)) 0 with h | h | h
    · rcases lt_trichotomy (u.eval (t₀ + δ)) 0 with h2 | h2 | h2
      · nlinarith
      · exact absurd h2 hne2
      · obtain ⟨z, hz, hzr⟩ :=
          exists_root_of_eval_mul_neg (show t₀ - δ ≤ t₀ + δ by linarith) (by nlinarith)
        have hz0 : z ≠ t₀ := by
          intro h'; rw [h', Polynomial.IsRoot.def] at hzr; exact hu0 hzr
        exact absurd (Polynomial.IsRoot.def.mp hzr) (hun z hz hz0)
    · exact absurd h hne1
    · rcases lt_trichotomy (u.eval (t₀ + δ)) 0 with h2 | h2 | h2
      · obtain ⟨z, hz, hzr⟩ :=
          exists_root_of_eval_mul_neg (show t₀ - δ ≤ t₀ + δ by linarith) (by nlinarith)
        have hz0 : z ≠ t₀ := by
          intro h'; rw [h', Polynomial.IsRoot.def] at hzr; exact hu0 hzr
        exact absurd (Polynomial.IsRoot.def.mp hzr) (hun z hz hz0)
      · exact absurd h2 hne2
      · nlinarith
  -- the endpoint values of `f` have opposite signs
  have hfprod : f.eval (t₀ - δ) * f.eval (t₀ + δ) < 0 := by
    have e1 : f.eval (t₀ - δ) = -(δ * u.eval (t₀ - δ)) := by
      rw [hu, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      ring
    have e2 : f.eval (t₀ + δ) = δ * u.eval (t₀ + δ) := by
      rw [hu, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      ring
    rw [e1, e2]
    have h : 0 < (δ * u.eval (t₀ - δ)) * (δ * u.eval (t₀ + δ)) := by
      rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact mul_pos (mul_pos hδ h1) (mul_pos hδ h2)
      · exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hδ h1) (mul_neg_of_pos_of_neg hδ h2)
    linarith [h]
  -- stability of the endpoint signs under a small change of the parameter
  have hstabL : ∀ᶠ x in nhds x₀, ∀ y ∈ Set.Icc (t₀ - δ) (t₀ - (2:ℝ)⁻¹ * δ),
      SignType.sign ((Work.WilE4.spec Q x).eval y)
        = SignType.sign ((Work.WilE4.spec Q x₀).eval y) := by
    refine sign_stable_Icc (continuous_spec_eval_pt Q) (x₀ := x₀)
      (a := t₀ - δ) (b := t₀ - (2:ℝ)⁻¹ * δ) (fun y hy => ?_)
    exact hfne y ⟨hy.1, by linarith [hy.2]⟩ (by intro h; rw [h] at hy; linarith [hy.2])
  have hstabR : ∀ᶠ x in nhds x₀, ∀ y ∈ Set.Icc (t₀ + (2:ℝ)⁻¹ * δ) (t₀ + δ),
      SignType.sign ((Work.WilE4.spec Q x).eval y)
        = SignType.sign ((Work.WilE4.spec Q x₀).eval y) := by
    refine sign_stable_Icc (continuous_spec_eval_pt Q) (x₀ := x₀)
      (a := t₀ + (2:ℝ)⁻¹ * δ) (b := t₀ + δ) (fun y hy => ?_)
    exact hfne y ⟨by linarith [hy.1], hy.2⟩ (by intro h; rw [h] at hy; linarith [hy.1])
  filter_upwards [hstabL, hstabR] with x hxL hxR
  have h1 : SignType.sign ((Work.WilE4.spec Q x).eval (t₀ - δ))
      = SignType.sign (f.eval (t₀ - δ)) := by
    simpa [hf] using hxL (t₀ - δ) ⟨le_rfl, by linarith⟩
  have h2 : SignType.sign ((Work.WilE4.spec Q x).eval (t₀ + δ))
      = SignType.sign (f.eval (t₀ + δ)) := by
    simpa [hf] using hxR (t₀ + δ) ⟨by linarith, le_rfl⟩
  have hneg : (Work.WilE4.spec Q x).eval (t₀ - δ) * (Work.WilE4.spec Q x).eval (t₀ + δ) < 0 := by
    rcases lt_trichotomy (f.eval (t₀ - δ)) 0 with hlt | heq | hgt
    · have hlt2 : 0 < f.eval (t₀ + δ) := by nlinarith [hfprod]
      rw [sign_neg hlt] at h1
      rw [sign_pos hlt2] at h2
      exact mul_neg_of_neg_of_pos (sign_eq_neg_one_iff.mp h1) (sign_eq_one_iff.mp h2)
    · exact absurd heq (hfne (t₀ - δ) ⟨le_rfl, by linarith⟩ (by linarith))
    · have hlt2 : f.eval (t₀ + δ) < 0 := by nlinarith [hfprod]
      rw [sign_pos hgt] at h1
      rw [sign_neg hlt2] at h2
      exact mul_neg_of_pos_of_neg (sign_eq_one_iff.mp h1) (sign_eq_neg_one_iff.mp h2)
  obtain ⟨t, ht, htr⟩ :=
    exists_root_of_eval_mul_neg (show t₀ - δ ≤ t₀ + δ by linarith) hneg
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, htr⟩
  · intro h'
    rw [← h', Polynomial.IsRoot.def] at htr
    rw [htr, zero_mul] at hneg
    exact absurd hneg (lt_irrefl 0)
  · intro h'
    rw [h', Polynomial.IsRoot.def] at htr
    rw [htr, mul_zero] at hneg
    exact absurd hneg (lt_irrefl 0)

/-! ## Auxiliary lemmas -/

/-- On `C`, a coefficient of index `≤ D` of a fibre vanishes at one point of `C` iff it vanishes at
every point of `C`. -/
theorem coeff_spec_eq_zero_iff_of_hcoeff {m k : ℕ} {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ}
    {D : ℕ} {C : Set (Fin m → ℝ)}
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((Work.WilE4.spec (P i) x).coeff j)
        = SignType.sign ((Work.WilE4.spec (P i) x').coeff j))
    {i : Fin k} {j : ℕ} (hj : j ≤ D) {x x' : Fin m → ℝ} (hx : x ∈ C) (hx' : x' ∈ C) :
    (Work.WilE4.spec (P i) x).coeff j = 0 ↔ (Work.WilE4.spec (P i) x').coeff j = 0 := by
  have h := hcoeff i j hj x hx x' hx'
  rw [← sign_eq_zero_iff, h, sign_eq_zero_iff]

/-- `hcoeff` packaged as `CoeffConst`. -/
theorem coeffConst_of_hcoeff {m k : ℕ} {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ} {D : ℕ}
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D) {C : Set (Fin m → ℝ)}
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((Work.WilE4.spec (P i) x).coeff j)
        = SignType.sign ((Work.WilE4.spec (P i) x').coeff j)) : CoeffConst P C :=
  fun i j hj x hx x' hx' => hcoeff i j (le_trans hj (hD i)) x hx x' hx'

/-- The `natDegree` of a fibre is bounded by the degree of the member in the last variable. -/
theorem spec_natDegree_le_degreeOf {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℝ)
    (x : Fin m → ℝ) : (Work.WilE4.spec P x).natDegree ≤ P.degreeOf (Fin.last m) := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  exact coeff_spec_eq_zero_of_degreeOf_lt P x hj

/-- On `C` the `natDegree` of a fibre is constant. -/
theorem spec_natDegree_eq_of_hcoeff {m k : ℕ} {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ} {D : ℕ}
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D) {C : Set (Fin m → ℝ)}
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((Work.WilE4.spec (P i) x).coeff j)
        = SignType.sign ((Work.WilE4.spec (P i) x').coeff j))
    {i : Fin k} {x x' : Fin m → ℝ} (hx : x ∈ C) (hx' : x' ∈ C) :
    (Work.WilE4.spec (P i) x).natDegree = (Work.WilE4.spec (P i) x').natDegree :=
  natDegree_spec_const (coeffConst_of_hcoeff hD hcoeff) hx hx'

/-- If a fibre vanishes at some point of `C` then it vanishes on all of `C`. -/
theorem spec_eq_zero_on_C_of_eq_zero {m k : ℕ} {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ}
    {D : ℕ} (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D) {C : Set (Fin m → ℝ)}
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((Work.WilE4.spec (P i) x).coeff j)
        = SignType.sign ((Work.WilE4.spec (P i) x').coeff j))
    {i : Fin k} {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ C) (h0 : Work.WilE4.spec (P i) x₀ = 0)
    {x : Fin m → ℝ} (hx : x ∈ C) : Work.WilE4.spec (P i) x = 0 := by
  ext j
  show (Work.WilE4.spec (P i) x).coeff j = 0
  by_cases hj : j ≤ D
  · rw [(coeff_spec_eq_zero_iff_of_hcoeff hcoeff hj hx hx₀)]
    rw [h0]
    exact Polynomial.coeff_zero j
  · exact coeff_spec_eq_zero_of_degreeOf_lt (P i) x (lt_of_le_of_lt (hD i) (Nat.lt_of_not_le hj))

/-- Conversely a fibre that is non-zero at a point of `C` is non-zero on all of `C`. -/
theorem spec_ne_zero_of_ne_zero_of_hcoeff {m k : ℕ} {P : Fin k → MvPolynomial (Fin (m + 1)) ℝ}
    {D : ℕ} (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D) {C : Set (Fin m → ℝ)}
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((Work.WilE4.spec (P i) x).coeff j)
        = SignType.sign ((Work.WilE4.spec (P i) x').coeff j))
    {i : Fin k} {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ C) (h0 : Work.WilE4.spec (P i) x₀ ≠ 0)
    {x : Fin m → ℝ} (hx : x ∈ C) : Work.WilE4.spec (P i) x ≠ 0 :=
  fun h => h0 (spec_eq_zero_on_C_of_eq_zero (x₀ := x) (x := x₀) hD hcoeff hx h hx₀)

/-- A polynomial with a root of multiplicity exactly one has non-vanishing derivative. -/
theorem not_derivative_isRoot_of_rootMultiplicity_eq_one {q : Polynomial ℝ} {t : ℝ}
    (hq : q ≠ 0) (hmult : q.rootMultiplicity t = 1) : ¬ q.derivative.IsRoot t := by
  intro hd
  have hr : q.IsRoot t := (Polynomial.rootMultiplicity_pos hq).mp (by rw [hmult]; norm_num)
  have hlt := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hq).mpr ⟨hr, hd⟩
  rw [hmult] at hlt
  exact absurd hlt (by norm_num)

/-- A root of a divisor is a root of the multiple. -/
theorem isRoot_of_dvd {p q : Polynomial ℝ} (h : q ∣ p) {t : ℝ} (ht : q.IsRoot t) :
    p.IsRoot t := by
  obtain ⟨w, rfl⟩ := h
  rw [Polynomial.IsRoot.def] at ht ⊢
  rw [Polynomial.eval_mul, ht, zero_mul]

/-- The distance between two real complex numbers is the absolute value of their difference. -/
theorem dist_ofReal_ofReal (a b : ℝ) : dist (a : ℂ) (b : ℂ) = |a - b| := by
  rw [dist_eq_norm, ← Complex.ofReal_sub]
  exact RCLike.norm_ofReal (K := ℂ) _

theorem vanish_persist_minor {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ) (D : ℕ)
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D)
    (hclosed : ∀ i : Fin k, ∃ j : Fin k, P j = MvPolynomial.pderiv (Fin.last m) (P i))
    (C : Set (Fin m → ℝ))
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((Work.WilE4.spec (P i) x).coeff j) = SignType.sign ((Work.WilE4.spec (P i) x').coeff j))
    (hmin : PscSignConst P C)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ C) (t₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ nhds x₀, ∀ x ∈ U ∩ C, ∃ t : ℝ, |t - t₀| < ε ∧
      ∀ i : Fin k, (Work.WilE4.spec (P i) x₀).eval t₀ = 0 → (Work.WilE4.spec (P i) x).eval t = 0 := by
  classical
  -- It suffices to prove the statement eventually near `x₀` in the ambient space.
  suffices key : ∀ᶠ x in nhds x₀, x ∈ C → ∃ t : ℝ, |t - t₀| < ε ∧
      ∀ i : Fin k, (Work.WilE4.spec (P i) x₀).eval t₀ = 0 → (Work.WilE4.spec (P i) x).eval t = 0 by
    have hmem : {x : Fin m → ℝ | ∃ t : ℝ, |t - t₀| < ε ∧ ∀ i : Fin k,
        (Work.WilE4.spec (P i) x₀).eval t₀ = 0 → (Work.WilE4.spec (P i) x).eval t = 0}
        ∈ nhdsWithin x₀ C := by
      rw [mem_nhdsWithin_iff_eventually]
      exact key
    obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hmem
    exact ⟨U, hU, fun x hx => hUs hx⟩
  by_cases htriv : ∀ i : Fin k, (Work.WilE4.spec (P i) x₀).eval t₀ = 0 →
      Work.WilE4.spec (P i) x₀ = 0
  · -- Case A: every fibre vanishing at `(x₀,t₀)` vanishes identically on `C`.
    filter_upwards with x hxC
    refine ⟨t₀, ?_, fun i hi => ?_⟩
    · simpa using hε
    · rw [spec_eq_zero_on_C_of_eq_zero hD hcoeff hx₀ (htriv i hi) hxC]
      simp
  · -- Case B: some fibre has a non-zero specialisation vanishing at `t₀`.
    push_neg at htriv
    obtain ⟨i₁, hi₁eval, hi₁ne⟩ := htriv
    obtain ⟨i₀, hi₀eval, hi₀ne, hi₀mult, _hi₀min⟩ :=
      exists_minimal_rootMultiplicity_member P hclosed x₀ ⟨i₁, hi₁eval, hi₁ne⟩
    have hi₀simple : ¬ (Work.WilE4.spec (P i₀) x₀).derivative.IsRoot t₀ :=
      not_derivative_isRoot_of_rootMultiplicity_eq_one hi₀ne hi₀mult
    obtain ⟨ρ, hρpos, hρltε, hρroots, hρcircle⟩ :=
      exists_disk_roots_eq_singleton hi₀ne (Polynomial.IsRoot.def.mpr hi₀eval) hi₀simple hε
    -- No root of the `i₀`-fibre other than `t₀` in the closed interval of radius `ρ`.
    have hnone : ∀ t ∈ Set.Icc (t₀ - ρ) (t₀ + ρ), t ≠ t₀ →
        ¬ (Work.WilE4.spec (P i₀) x₀).IsRoot t := by
      intro t ht hne hroot
      have hmap : ((Work.WilE4.spec (P i₀) x₀).map (algebraMap ℝ ℂ)).IsRoot (t : ℂ) := by
        simpa using Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hroot
      have hle : dist (t : ℂ) (t₀ : ℂ) ≤ ρ := by
        rw [dist_ofReal_ofReal, abs_le]
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rcases lt_or_eq_of_le hle with hlt | heq
      · have hmem : (t : ℂ) ∈ ((Work.WilE4.spec (P i₀) x₀).map (algebraMap ℝ ℂ)).roots.filter
            (fun z : ℂ => dist z (t₀ : ℂ) < ρ) :=
          Multiset.mem_filter.mpr
            ⟨(Polynomial.mem_roots (map_ofReal_ne_zero hi₀ne)).mpr hmap, hlt⟩
        rw [hρroots] at hmem
        exact hne (Complex.ofReal_injective (by simpa using hmem))
      · exact hρcircle (t : ℂ) heq (Polynomial.IsRoot.def.mp hmap)
    -- The only root of the `i₀`-fibre within distance `ρ` of `t₀` is `t₀` itself.
    have huniq₀ : ∀ t : ℝ, |t - t₀| ≤ ρ → (Work.WilE4.spec (P i₀) x₀).IsRoot t → t = t₀ := by
      intro t ht hroot
      have hIcc : t ∈ Set.Icc (t₀ - ρ) (t₀ + ρ) := by
        rw [abs_le] at ht
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      by_contra hne
      exact hnone t hIcc hne hroot
    -- The `i₀`-fibre has a root in the interval, for `x` near `x₀`.
    have hIVT : ∀ᶠ x in nhds x₀, ∃ t ∈ Set.Ioo (t₀ - ρ) (t₀ + ρ),
        (Work.WilE4.spec (P i₀) x).IsRoot t :=
      eventually_exists_root_near_of_simple_root (P i₀) hρpos hi₀mult hnone
    -- and exactly one root in the disk.
    have hcount : ∀ᶠ x in nhds x₀,
        (((Work.WilE4.spec (P i₀) x).map (algebraMap ℝ ℂ)).roots.filter
          (fun z : ℂ => dist z (t₀ : ℂ) < ρ)).card = 1 := by
      have hdc : ∀ᶠ x in nhds x₀,
          ((Multiset.filter (fun z : ℂ => dist z (t₀ : ℂ) < ρ)
            (((Work.WilE4.spec (P i₀) x).map (algebraMap ℝ ℂ)).roots)).card
            = (Multiset.filter (fun z : ℂ => dist z (t₀ : ℂ) < ρ)
            (((Work.WilE4.spec (P i₀) x₀).map (algebraMap ℝ ℂ)).roots)).card) :=
        disk_roots_card_eventually_const
          (fun x : Fin m → ℝ => (Work.WilE4.spec (P i₀) x).map (algebraMap ℝ ℂ)) D
          (fun k => by
            simp only [Polynomial.coeff_map]
            exact Complex.continuous_ofReal.comp (continuous_spec_coeff (P i₀) k))
          x₀
          (by
            filter_upwards with x
            exact le_trans (le_trans Polynomial.natDegree_map_le
              (spec_natDegree_le_degreeOf (P i₀) x)) (hD i₀))
          hρpos (fun z hz => hρcircle z hz)
      filter_upwards [hdc] with x hx
      rw [hx, hρroots]
      simp [hρpos]
    -- Suppose the conclusion fails; extract a sequence in `C` converging to `x₀`.
    by_contra hcon
    obtain ⟨u, huC, hulim, huφ⟩ := exists_seq_of_not_eventually_nhdsWithin
      (fun h => hcon (eventually_nhdsWithin_iff.mp h))
    have hIVTseq : ∀ᶠ n in Filter.atTop, ∃ t ∈ Set.Ioo (t₀ - ρ) (t₀ + ρ),
        (Work.WilE4.spec (P i₀) (u n)).IsRoot t := hulim.eventually hIVT
    have hcountseq : ∀ᶠ n in Filter.atTop,
        (((Work.WilE4.spec (P i₀) (u n)).map (algebraMap ℝ ℂ)).roots.filter
          (fun z : ℂ => dist z (t₀ : ℂ) < ρ)).card = 1 := hulim.eventually hcount
    -- Each member vanishing at `(x₀,t₀)` shares a root with the `i₀`-fibre in the interval.
    have hgcdseq : ∀ᶠ n in Filter.atTop, ∀ j : Fin k, Work.WilE4.spec (P j) x₀ ≠ 0 →
        (Work.WilE4.spec (P j) x₀).eval t₀ = 0 → ∃ t ∈ Set.Ioo (t₀ - ρ) (t₀ + ρ),
          (gcd (Work.WilE4.spec (P i₀) (u n)) (Work.WilE4.spec (P j) (u n))).IsRoot t := by
      rw [Filter.eventually_all]
      intro j
      by_cases hjn : Work.WilE4.spec (P j) x₀ = 0
      · exact Filter.Eventually.of_forall fun n hne _ => absurd hjn hne
      · by_cases hje : (Work.WilE4.spec (P j) x₀).eval t₀ = 0
        · exact (gcd_root_along_sequence P D hD C hcoeff hmin hx₀ u huC hulim hρpos hi₀ne hjn
            hi₀eval hje hi₀mult huniq₀).mono fun n hn _ _ => hn
        · exact Filter.Eventually.of_forall fun n _ he => absurd he hje
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hIVTseq
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp hcountseq
    obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp hgcdseq
    set n : ℕ := max N₁ (max N₂ N₃) with hn
    have hαn : ∃ t ∈ Set.Ioo (t₀ - ρ) (t₀ + ρ), (Work.WilE4.spec (P i₀) (u n)).IsRoot t :=
      hN₁ n (le_max_left _ _)
    have hcn : (((Work.WilE4.spec (P i₀) (u n)).map (algebraMap ℝ ℂ)).roots.filter
        (fun z : ℂ => dist z (t₀ : ℂ) < ρ)).card = 1 :=
      hN₂ n (le_trans (le_max_left N₂ N₃) (le_max_right N₁ _))
    have hgn : ∀ j : Fin k, Work.WilE4.spec (P j) x₀ ≠ 0 →
        (Work.WilE4.spec (P j) x₀).eval t₀ = 0 → ∃ t ∈ Set.Ioo (t₀ - ρ) (t₀ + ρ),
          (gcd (Work.WilE4.spec (P i₀) (u n)) (Work.WilE4.spec (P j) (u n))).IsRoot t :=
      hN₃ n (le_trans (le_max_right N₂ N₃) (le_max_right N₁ _))
    obtain ⟨α, hαIoo, hαroot⟩ := hαn
    refine (huφ n) ⟨α, ?_, ?_⟩
    · have hlt : |α - t₀| < ρ := by
        rw [abs_lt]
        exact ⟨by linarith [hαIoo.1], by linarith [hαIoo.2]⟩
      linarith
    · intro i hi
      by_cases hiz : Work.WilE4.spec (P i) x₀ = 0
      · rw [spec_eq_zero_on_C_of_eq_zero hD hcoeff hx₀ hiz (huC n)]
        simp
      · obtain ⟨t, htIoo, htroot⟩ := hgn i hiz hi
        have hne : ((Work.WilE4.spec (P i₀) (u n)).map (algebraMap ℝ ℂ)) ≠ 0 :=
          map_ofReal_ne_zero (spec_ne_zero_of_ne_zero_of_hcoeff hD hcoeff hx₀ hi₀ne (huC n))
        have hdiv : (gcd (Work.WilE4.spec (P i₀) (u n)) (Work.WilE4.spec (P i) (u n))) ∣
            (Work.WilE4.spec (P i₀) (u n)) := gcd_dvd_left _ _
        have hdistα : dist (α : ℂ) (t₀ : ℂ) < ρ := by
          rw [dist_ofReal_ofReal, abs_lt]
          exact ⟨by linarith [hαIoo.1], by linarith [hαIoo.2]⟩
        have hdistt : dist (t : ℂ) (t₀ : ℂ) < ρ := by
          rw [dist_ofReal_ofReal, abs_lt]
          exact ⟨by linarith [htIoo.1], by linarith [htIoo.2]⟩
        have hrootα' : ((Work.WilE4.spec (P i₀) (u n)).map (algebraMap ℝ ℂ)).IsRoot (α : ℂ) := by simpa using Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hαroot
        have hroott' : ((Work.WilE4.spec (P i₀) (u n)).map (algebraMap ℝ ℂ)).IsRoot (t : ℂ) := by simpa using Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) (isRoot_of_dvd hdiv htroot)
        have hmemα : (α : ℂ) ∈ ((Work.WilE4.spec (P i₀) (u n)).map (algebraMap ℝ ℂ)).roots.filter
            (fun z : ℂ => dist z (t₀ : ℂ) < ρ) :=
          Multiset.mem_filter.mpr
            ⟨(Polynomial.mem_roots hne).mpr hrootα', hdistα⟩
        have hmemt : (t : ℂ) ∈ ((Work.WilE4.spec (P i₀) (u n)).map (algebraMap ℝ ℂ)).roots.filter
            (fun z : ℂ => dist z (t₀ : ℂ) < ρ) :=
          Multiset.mem_filter.mpr
            ⟨(Polynomial.mem_roots hne).mpr hroott', hdistt⟩
        obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcn
        have h1 : (α : ℂ) = a := by rw [ha] at hmemα; simpa using hmemα
        have h2 : (t : ℂ) = a := by rw [ha] at hmemt; simpa using hmemt
        have htα : t = α := Complex.ofReal_injective (h2.trans h1.symm)
        have hdiv2 : (gcd (Work.WilE4.spec (P i₀) (u n)) (Work.WilE4.spec (P i) (u n))) ∣
            (Work.WilE4.spec (P i) (u n)) := gcd_dvd_right _ _
        rw [← htα]
        exact isRoot_of_dvd hdiv2 htroot

end Work.WilE4.CAD
