import Mathlib
import Submission.Commons.LorentzianPolynomials.deform_mem_L
import Submission.Commons.LorentzianPolynomials.cubic_deform_mem_S2
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

noncomputable section

/-! Notation: `Y := Fin.last n` (the extra variable), `e := Fin.castSucc` (embedding). -/

abbrev cds3Y (n : ℕ) : Fin (n + 1) := Fin.last n
abbrev cds3e (n : ℕ) : Fin n → Fin (n + 1) := Fin.castSucc

lemma cds3e_injective (n : ℕ) : Function.Injective (cds3e n) := Fin.castSucc_injective n

lemma cds3e_ne_Y (n : ℕ) (j : Fin n) : cds3e n j ≠ cds3Y n := by
  intro h
  have hval : (cds3e n j).val = (cds3Y n).val := congrArg Fin.val h
  have h1 : (cds3e n j).val = j.val := by simp [cds3e, Fin.castSucc]
  have h2 : (cds3Y n).val = n := by simp [cds3Y, Fin.last]
  rw [h1, h2] at hval
  omega

/-- every element of `Fin (n+1)` is `e j` or `Y` -/
lemma cds3e_or_Y (n : ℕ) (k : Fin (n + 1)) : (∃ j : Fin n, k = cds3e n j) ∨ k = cds3Y n := by
  by_cases hk : k.val < n
  · left
    refine ⟨⟨k.val, hk⟩, ?_⟩
    apply Fin.ext
    simp [cds3e, Fin.castSucc]
  · right
    apply Fin.ext
    simp [cds3Y, Fin.last]
    omega

/-- stability is preserved by renaming along any map -/
lemma cds3_IsStable_rename {n m : ℕ} (f : Fin n → Fin m) (p : MvPolynomial (Fin n) ℝ)
    (hp : IsStable p) : IsStable (MvPolynomial.rename f p) := by
  rcases hp with hz | hz'
  · left
    rw [hz]
    simp
  · right
    intro z
    rw [MvPolynomial.aeval_rename]
    exact hz' (fun i : Fin n => z (f i))

/-- stability of the embedded polynomial implies stability of the original (castSucc) -/
lemma cds3_IsStable_rename_castSucc {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsStable (MvPolynomial.rename (cds3e n) p)) : IsStable p := by
  classical
  let I : UpperHalfPlane := ⟨Complex.I, by simp⟩
  rcases hp with hz | hz'
  · left
    exact MvPolynomial.rename_injective (cds3e n) (cds3e_injective n) hz
  · right
    intro z
    let g : Fin (n + 1) → UpperHalfPlane := fun j =>
      if hj : j.val < n then z ⟨j.val, hj⟩ else I
    have hfun : ((fun j : Fin (n + 1) => ((g j : UpperHalfPlane) : ℂ)) ∘ cds3e n)
        = (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) := by
      funext i
      simp [g, cds3e, Fin.castSucc]
    have heq : MvPolynomial.aeval (fun i : Fin n => (z i : ℂ)) p =
        MvPolynomial.aeval (fun j : Fin (n + 1) => ((g j : UpperHalfPlane) : ℂ))
          (MvPolynomial.rename (cds3e n) p) := by
      rw [MvPolynomial.aeval_rename]
      rw [hfun]
    change MvPolynomial.aeval (fun i : Fin n => ((z i : ℍ) : ℂ)) p ≠ 0
    rw [heq]
    exact hz' g

/-- coefficients of an injective rename are nonnegative iff the originals are -/
lemma cds3_coeff_rename_nonneg {n m : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f)
    (p : MvPolynomial (Fin n) ℝ) :
    (∀ m' : Fin m →₀ ℕ, 0 ≤ (MvPolynomial.rename f p).coeff m') ↔
      ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m := by
  classical
  constructor
  · intro h m
    have hmm := h (m.mapDomain f)
    rwa [MvPolynomial.coeff_rename_mapDomain f hf p m] at hmm
  · intro h m'
    by_cases himg : ∃ m : Fin n →₀ ℕ, m.mapDomain f = m'
    · rcases himg with ⟨m, rfl⟩
      rw [MvPolynomial.coeff_rename_mapDomain f hf p m]
      exact h m
    · have h0 : (MvPolynomial.rename f p).coeff m' = 0 :=
        MvPolynomial.coeff_rename_eq_zero f p m' (fun u hu => by
          exact False.elim (himg ⟨u, hu⟩))
      rw [h0]

/-- `rename e` sends a degree-`d` homogeneous polynomial to a degree-`d` one -/
lemma cds3_rename_isHomogeneous (n : ℕ) {d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous d) : (MvPolynomial.rename (cds3e n) p).IsHomogeneous d := by
  exact MvPolynomial.IsHomogeneous.rename_isHomogeneous (f := cds3e n) hp

/-- partial derivative commutes with injective renaming -/
lemma cds3_pderiv_rename (n : ℕ) (j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv (cds3e n j) (MvPolynomial.rename (cds3e n) p) =
      MvPolynomial.rename (cds3e n) (MvPolynomial.pderiv j p) := by
  exact MvPolynomial.pderiv_rename (f := cds3e n) (cds3e_injective n) j p

/-! ## zeroLastY and dilY: setting / dilating the last variable -/

/-- substitute the last variable by `0` (staying in the `(n+1)`-variable ring) -/
def cds3_zeroLastY (n : ℕ) (p : MvPolynomial (Fin (n + 1)) ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  MvPolynomial.aeval (fun k : Fin (n + 1) => if k = cds3Y n then 0 else MvPolynomial.X k) p

/-- dilate the last variable by `θ` -/
def cds3_dilY (n : ℕ) (θ : ℝ) (p : MvPolynomial (Fin (n + 1)) ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  MvPolynomial.aeval (fun k : Fin (n + 1) =>
    if k = cds3Y n then MvPolynomial.C θ * MvPolynomial.X k else MvPolynomial.X k) p

/-- coefficients of `zeroLastY` -/
lemma cds3_zeroLastY_coeff (n : ℕ) (p : MvPolynomial (Fin (n + 1)) ℝ)
    (m : Fin (n + 1) →₀ ℕ) :
    (cds3_zeroLastY n p).coeff m = if m (cds3Y n) = 0 then p.coeff m else 0 := by
  classical
  let amap : Fin (n + 1) → ℝ := fun k => if k = cds3Y n then 0 else 1
  have hdilmap : (fun k : Fin (n + 1) => MvPolynomial.C (amap k) * MvPolynomial.X k) =
      (fun k : Fin (n + 1) =>
        if k = cds3Y n then (0 : MvPolynomial (Fin (n + 1)) ℝ) else MvPolynomial.X k) := by
    funext k
    by_cases hk : k = cds3Y n
    · subst k
      simp [amap]
    · simp [amap, hk]
  have hdil : MvPolynomial.aeval (fun k : Fin (n + 1) => MvPolynomial.C (amap k) * MvPolynomial.X k) p =
      cds3_zeroLastY n p := by
    unfold cds3_zeroLastY
    rw [hdilmap]
  rw [← hdil]
  rw [cdmN_cdn_dil_aeval_coeff (n := n + 1) amap p m]
  by_cases hm : m (cds3Y n) = 0
  · have hprod : (∏ j ∈ m.support, amap j ^ m j) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      have hjy : j ≠ cds3Y n := by
        intro hjy
        have hmj : m j ≠ 0 := Finsupp.mem_support_iff.mp hj
        rw [hjy] at hmj
        exact hmj hm
      have haj : amap j = 1 := by simp [amap, hjy]
      rw [haj]
      simp
    rw [hprod]
    simp [hm]
  · have hm0 : m (cds3Y n) ≠ 0 := hm
    have hmemY : cds3Y n ∈ m.support := Finsupp.mem_support_iff.mpr hm0
    have hprod : (∏ j ∈ m.support, amap j ^ m j) = 0 := by
      rw [← Finset.mul_prod_erase (s := m.support) (f := fun j => amap j ^ m j)
          (a := cds3Y n) hmemY]
      have haY : amap (cds3Y n) ^ m (cds3Y n) = 0 := by
        dsimp [amap]
        simp [hm0]
      rw [haY]
      simp
    rw [hprod]
    simp [hm]
lemma cds3_dilY_coeff (n : ℕ) (θ : ℝ) (p : MvPolynomial (Fin (n + 1)) ℝ)
    (m : Fin (n + 1) →₀ ℕ) :
    (cds3_dilY n θ p).coeff m = θ ^ (m (cds3Y n)) * p.coeff m := by
  classical
  let amap : Fin (n + 1) → ℝ := fun k => if k = cds3Y n then θ else 1
  have hdilmap : (fun k : Fin (n + 1) => MvPolynomial.C (amap k) * MvPolynomial.X k) =
      (fun k : Fin (n + 1) =>
        if k = cds3Y n then MvPolynomial.C θ * MvPolynomial.X k else MvPolynomial.X k) := by
    funext k
    by_cases hk : k = cds3Y n
    · subst k
      simp [amap]
    · simp [amap, hk]
  have hdil : MvPolynomial.aeval (fun k : Fin (n + 1) => MvPolynomial.C (amap k) * MvPolynomial.X k) p =
      cds3_dilY n θ p := by
    unfold cds3_dilY
    rw [hdilmap]
  rw [← hdil]
  rw [cdmN_cdn_dil_aeval_coeff (n := n + 1) amap p m]
  by_cases hm : cds3Y n ∈ m.support
  · have herase : (∏ x ∈ m.support.erase (cds3Y n), amap x ^ m x) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      have hjy : j ≠ cds3Y n := by
        intro hjy
        have hmem : j ∈ m.support.erase (cds3Y n) := hj
        have hnot : j ∉ m.support.erase (cds3Y n) := by
          rw [hjy]
          simp
        exact hnot hmem
      have haj : amap j = 1 := by simp [amap, hjy]
      rw [haj]
      simp
    rw [← Finset.mul_prod_erase (s := m.support) (f := fun j => amap j ^ m j)
        (a := cds3Y n) hm]
    rw [herase, mul_one]
    dsimp [amap]
    rw [if_pos rfl]
    ring
  · have hmY : m (cds3Y n) = 0 := by
      by_contra h
      exact hm (Finsupp.mem_support_iff.mpr h)
    have hprod : (∏ j ∈ m.support, amap j ^ m j) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      have hjy : j ≠ cds3Y n := by
        intro hjy
        have hmj : m j ≠ 0 := Finsupp.mem_support_iff.mp hj
        rw [hjy] at hmj
        exact hmj hmY
      have haj : amap j = 1 := by simp [amap, hjy]
      rw [haj]
      simp
    rw [hprod]
    rw [hmY]
    simp

/-- `zeroLastY` keeps homogeneity -/
lemma cds3_zeroLastY_isHomogeneous (n : ℕ) {d : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ)
    (hp : p.IsHomogeneous d) : (cds3_zeroLastY n p).IsHomogeneous d := by
  classical
  have hg : ∀ k : Fin (n + 1),
      (if k = cds3Y n then (0 : MvPolynomial (Fin (n + 1)) ℝ) else MvPolynomial.X k).IsHomogeneous 1 := by
    intro k
    by_cases hk : k = cds3Y n
    · subst k
      rw [if_pos rfl]
      exact MvPolynomial.isHomogeneous_zero (σ := Fin (n + 1)) (R := ℝ) 1
    · rw [if_neg hk]
      exact MvPolynomial.isHomogeneous_X (σ := Fin (n + 1)) (R := ℝ) k
  have h := MvPolynomial.IsHomogeneous.aeval (hφ := hp)
    (g := fun k : Fin (n + 1) =>
      if k = cds3Y n then (0 : MvPolynomial (Fin (n + 1)) ℝ) else MvPolynomial.X k) hg
  simpa [cds3_zeroLastY, Nat.one_mul] using h

/-- `zeroLastY` of a stable polynomial is stable (dilation by a nonnegative vector) -/
lemma cds3_zeroLastY_IsStable (n : ℕ) (p : MvPolynomial (Fin (n + 1)) ℝ)
    (hp : IsStable p) : IsStable (cds3_zeroLastY n p) := by
  classical
  let a : Fin (n + 1) → ℝ := fun k => if k = cds3Y n then 0 else 1
  have ha : ∀ k : Fin (n + 1), 0 ≤ a k := by
    intro k
    by_cases hk : k = cds3Y n
    · subst k; simp [a]
    · simp [a, hk]
  have hdilmap : (fun k : Fin (n + 1) => MvPolynomial.C (a k) * MvPolynomial.X k) =
      (fun k : Fin (n + 1) =>
        if k = cds3Y n then (0 : MvPolynomial (Fin (n + 1)) ℝ) else MvPolynomial.X k) := by
    funext k
    by_cases hk : k = cds3Y n
    · subst k
      simp [a]
    · simp [a, hk]
  have hdil : (MvPolynomial.aeval (fun k : Fin (n + 1) => MvPolynomial.C (a k) * MvPolynomial.X k) p)
      = cds3_zeroLastY n p := by
    unfold cds3_zeroLastY
    rw [hdilmap]
  rw [← hdil]
  exact cdmN_closure_dilate_nonneg a ha p hp

/-- `zeroLastY` is additive -/
lemma cds3_zeroLastY_add (n : ℕ) (p q : MvPolynomial (Fin (n + 1)) ℝ) :
    cds3_zeroLastY n (p + q) = cds3_zeroLastY n p + cds3_zeroLastY n q := by
  unfold cds3_zeroLastY
  rw [map_add]

/-- `zeroLastY` commutes with constant multiples -/
lemma cds3_zeroLastY_C_mul (n : ℕ) (c : ℝ) (p : MvPolynomial (Fin (n + 1)) ℝ) :
    cds3_zeroLastY n (MvPolynomial.C c * p) = MvPolynomial.C c * cds3_zeroLastY n p := by
  unfold cds3_zeroLastY
  rw [map_mul]
  simp

/-- `zeroLastY (X_Y · s) = 0` -/
lemma cds3_zeroLastY_X_Y_mul (n : ℕ) (s : MvPolynomial (Fin (n + 1)) ℝ) :
    cds3_zeroLastY n (MvPolynomial.X (cds3Y n) * s) = 0 := by
  classical
  unfold cds3_zeroLastY
  rw [map_mul]
  have hx : MvPolynomial.aeval (R := ℝ) (fun k : Fin (n + 1) =>
      if k = cds3Y n then (0 : MvPolynomial (Fin (n + 1)) ℝ) else MvPolynomial.X k)
      (MvPolynomial.X (cds3Y n)) = 0 := by
    rw [MvPolynomial.aeval_X]
    simp
  rw [hx]
  simp

/-- `∂_{e j}` commutes with `zeroLastY` -/
lemma cds3_pderiv_castSucc_zeroLastY (n : ℕ) (j : Fin n) (p : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial.pderiv (cds3e n j) (cds3_zeroLastY n p) =
      cds3_zeroLastY n (MvPolynomial.pderiv (cds3e n j) p) := by
  classical
  apply MvPolynomial.ext
  intro m
  have hej_neY : cds3e n j ≠ cds3Y n := cds3e_ne_Y n j
  have hshift : (m + (Finsupp.single (cds3e n j) (1 : ℕ) : Fin (n + 1) →₀ ℕ)) (cds3Y n) = m (cds3Y n) := by
    simp [Finsupp.add_apply, Finsupp.single_apply, hej_neY]
  by_cases hm : m (cds3Y n) = 0
  · simp [MvPolynomial.coeff_pderiv, cds3_zeroLastY_coeff, hm, hshift]
  · have hmne : m (cds3Y n) ≠ 0 := hm
    simp [MvPolynomial.coeff_pderiv, cds3_zeroLastY_coeff, hm, hshift]
/-- The deformed cubic raw polynomial -/
def cds3_defPolyY (n : ℕ) (θ : ℝ) (j : Fin n) (h : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial (Fin (n + 1)) ℝ :=
  h + MvPolynomial.C θ * MvPolynomial.X (cds3Y n) * MvPolynomial.pderiv (cds3e n j) h

/-- `∂_Y` of the deform, then `zeroLastY`: only the linear terms survive -/
lemma cds3_zeroLastY_pderivY_defPolyY (n : ℕ) (θ : ℝ) (j : Fin n)
    (h : MvPolynomial (Fin (n + 1)) ℝ) :
    cds3_zeroLastY n (MvPolynomial.pderiv (cds3Y n) (cds3_defPolyY n θ j h)) =
      cds3_zeroLastY n (MvPolynomial.pderiv (cds3Y n) h) +
        MvPolynomial.C θ * cds3_zeroLastY n (MvPolynomial.pderiv (cds3e n j) h) := by
  classical
  let s : MvPolynomial (Fin (n + 1)) ℝ := MvPolynomial.pderiv (cds3e n j) h
  have hlb : MvPolynomial.pderiv (cds3Y n) (MvPolynomial.X (cds3Y n) * s) =
      s + MvPolynomial.X (cds3Y n) * MvPolynomial.pderiv (cds3Y n) s := by
    rw [MvPolynomial.pderiv_mul]
    rw [MvPolynomial.pderiv_X_self]
    ring
  have hprod : MvPolynomial.pderiv (cds3Y n)
        (MvPolynomial.C θ * MvPolynomial.X (cds3Y n) * MvPolynomial.pderiv (cds3e n j) h) =
      MvPolynomial.C θ * s +
        MvPolynomial.C θ * MvPolynomial.X (cds3Y n) * MvPolynomial.pderiv (cds3Y n) s := by
    rw [mul_assoc]
    rw [MvPolynomial.pderiv_C_mul]
    rw [hlb]
    ring
  calc
    cds3_zeroLastY n (MvPolynomial.pderiv (cds3Y n) (cds3_defPolyY n θ j h))
        = cds3_zeroLastY n (MvPolynomial.pderiv (cds3Y n) h +
            (MvPolynomial.C θ * s +
              MvPolynomial.C θ * MvPolynomial.X (cds3Y n) * MvPolynomial.pderiv (cds3Y n) s)) := by
          unfold cds3_defPolyY
          rw [map_add, hprod]
    _ = cds3_zeroLastY n (MvPolynomial.pderiv (cds3Y n) h) +
          cds3_zeroLastY n (MvPolynomial.C θ * s) +
          cds3_zeroLastY n (MvPolynomial.C θ * MvPolynomial.X (cds3Y n) * MvPolynomial.pderiv (cds3Y n) s) := by
          rw [cds3_zeroLastY_add, cds3_zeroLastY_add]
          rw [add_assoc]
    _ = cds3_zeroLastY n (MvPolynomial.pderiv (cds3Y n) h) +
          MvPolynomial.C θ * cds3_zeroLastY n s + 0 := by
          rw [cds3_zeroLastY_C_mul]
          rw [mul_assoc]
          rw [cds3_zeroLastY_C_mul]
          rw [cds3_zeroLastY_X_Y_mul]
          simp
    _ = cds3_zeroLastY n (MvPolynomial.pderiv (cds3Y n) h) +
          MvPolynomial.C θ * cds3_zeroLastY n s := by
          simp
    _ = cds3_zeroLastY n (MvPolynomial.pderiv (cds3Y n) h) +
          MvPolynomial.C θ * cds3_zeroLastY n (MvPolynomial.pderiv (cds3e n j) h) := by
          dsimp [s]

/-- `zeroLastY` of a polynomial with no `Y`-monomials is itself -/
lemma cds3_zeroLastY_of_noY {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ)
    (hp : ∀ m : Fin (n + 1) →₀ ℕ, 0 < m (cds3Y n) → p.coeff m = 0) :
    cds3_zeroLastY n p = p := by
  classical
  apply MvPolynomial.ext
  intro m
  by_cases hm : m (cds3Y n) = 0
  · rw [cds3_zeroLastY_coeff, if_pos hm]
  · rw [cds3_zeroLastY_coeff, if_neg hm]
    have hmpos : 0 < m (cds3Y n) := Nat.pos_of_ne_zero hm
    exact (hp m hmpos).symm

/-! ## Embedding into `L (n+1) 3` -/

/-- the embedded element -/
def cds3_embed3 (n : ℕ) (f : H n 3) : H (n + 1) 3 :=
  ⟨MvPolynomial.rename (cds3e n) f.1, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact cds3_rename_isHomogeneous n f.1 (by simpa [MvPolynomial.mem_homogeneousSubmodule] using f.2)⟩

/-- `mapDomain e` of a difference by a single coordinate (injective `e`) -/
lemma cds3_mapDomain_sub_single {n : ℕ} (e : Fin n → Fin (n + 1)) (he : Function.Injective e)
    (a : Fin n →₀ ℕ) (i0 : Fin n) :
    (a - (Finsupp.single i0 (1 : ℕ) : Fin n →₀ ℕ)).mapDomain e =
      a.mapDomain e - (Finsupp.single (e i0) (1 : ℕ) : Fin (n + 1) →₀ ℕ) := by
  classical
  ext t
  by_cases ht : ∃ u : Fin n, e u = t
  · rcases ht with ⟨u, rfl⟩
    simp [Finsupp.mapDomain_apply he, Finsupp.sub_apply, Finsupp.single_apply, he.eq_iff]
  · have hnot : t ∉ Set.range e := by
      rintro ⟨u, rfl⟩
      exact ht ⟨u, rfl⟩
    rw [Finsupp.mapDomain_of_notMem_range (a - Finsupp.single i0 1) t hnot]
    have hte : t ≠ e i0 := by
      intro hh
      exact ht ⟨i0, hh.symm⟩
    simp [Finsupp.sub_apply, Finsupp.mapDomain_of_notMem_range a t hnot,
      Finsupp.single_apply, hte]

/-- `mapDomain e` commutes with an exchange move `α - e_i + e_j` (injective `e`) -/
lemma cds3_mapDomain_exchange {n : ℕ} (e : Fin n → Fin (n + 1)) (he : Function.Injective e)
    (a : Fin n →₀ ℕ) (i0 j0 : Fin n) :
    (a - (Finsupp.single i0 (1 : ℕ) : Fin n →₀ ℕ) +
        (Finsupp.single j0 (1 : ℕ) : Fin n →₀ ℕ)).mapDomain e =
      a.mapDomain e - (Finsupp.single (e i0) (1 : ℕ) : Fin (n + 1) →₀ ℕ) +
        (Finsupp.single (e j0) (1 : ℕ) : Fin (n + 1) →₀ ℕ) := by
  classical
  rw [Finsupp.mapDomain_add]
  rw [cds3_mapDomain_sub_single e he a i0]
  rw [Finsupp.mapDomain_single]
/-- M-convexity is preserved by the coordinate embedding -/
lemma cds3_MConvex_image_embed {n : ℕ} (A : Set (Fin n →₀ ℕ))
    (hA : IsMConvex A) : IsMConvex {γ | ∃ α ∈ A, γ = α.mapDomain (cds3e n)} := by
  classical
  let S : Set (Fin (n + 1) →₀ ℕ) := {γ | ∃ α ∈ A, γ = α.mapDomain (cds3e n)}
  change IsMConvex S
  intro γ hγ δ hδ i hgt
  rcases hγ with ⟨α, hα, rfl⟩
  rcases hδ with ⟨β, hβ, rfl⟩
  have hγ0 (t : Fin (n + 1)) (ht : t ∉ Set.range (cds3e n)) :
      (α.mapDomain (cds3e n)) t = 0 := Finsupp.mapDomain_of_notMem_range α t ht
  have hδ0 (t : Fin (n + 1)) (ht : t ∉ Set.range (cds3e n)) :
      (β.mapDomain (cds3e n)) t = 0 := Finsupp.mapDomain_of_notMem_range β t ht
  rcases cds3e_or_Y n i with hi | hiY
  · rcases hi with ⟨i0, rfl⟩
    -- i = e i0: compare coefficients at i0
    have hgt' : α i0 > β i0 := by
      rw [Finsupp.mapDomain_apply (cds3e_injective n) α i0,
        Finsupp.mapDomain_apply (cds3e_injective n) β i0] at hgt
      exact hgt
    rcases hA α hα β hβ i0 hgt' with ⟨j0, hlt, hmem⟩
    refine ⟨cds3e n j0, ?_, ?_⟩
    · -- γ j0 < δ j0
      rw [Finsupp.mapDomain_apply (cds3e_injective n) α j0,
        Finsupp.mapDomain_apply (cds3e_injective n) β j0]
      exact hlt
    · -- γ − e_{e i0} + e_{e j0} ∈ S
      refine ⟨α - Finsupp.single i0 1 + Finsupp.single j0 1, hmem, ?_⟩
      rw [cds3_mapDomain_exchange (cds3e n) (cds3e_injective n)]
  · -- i = Y: impossible since both sides are 0 at Y
    subst i
    have hgt0 : (α.mapDomain (cds3e n)) (cds3Y n) > (β.mapDomain (cds3e n)) (cds3Y n) := hgt
    have hnotY : cds3Y n ∉ Set.range (cds3e n) := by
      rintro ⟨u, hu⟩
      have hval : (cds3e n u).val = (cds3Y n).val := congrArg Fin.val hu
      have h1 : (cds3e n u).val = u.val := by simp [cds3e, Fin.castSucc]
      have h2 : (cds3Y n).val = n := by simp [cds3Y, Fin.last]
      rw [h1, h2] at hval
      omega
    have hγY : (α.mapDomain (cds3e n)) (cds3Y n) = 0 := hγ0 (cds3Y n) hnotY
    have hδY : (β.mapDomain (cds3e n)) (cds3Y n) = 0 := hδ0 (cds3Y n) hnotY
    omega

/-- support of the embedded polynomial is the image -/
lemma cds3_embed3_support (n : ℕ) (f : H n 3) :
    (cds3_embed3 n f).1.support = Finset.image (Finsupp.mapDomain (cds3e n)) f.1.support := by
  classical
  exact MvPolynomial.support_rename_of_injective (p := f.1) (f := cds3e n) (cds3e_injective n)

/-- `∂_Y` of an embedded polynomial is zero -/
lemma cds3_pderivY_rename (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv (cds3Y n) (MvPolynomial.rename (cds3e n) p) = 0 := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_pderiv]
  have hc : (MvPolynomial.rename (cds3e n) p).coeff (m + Finsupp.single (cds3Y n) 1) = 0 := by
    apply MvPolynomial.coeff_rename_eq_zero (f := cds3e n) p
    intro u hu
    have huY : (u.mapDomain (cds3e n)) (cds3Y n) = 0 := by
      exact Finsupp.mapDomain_of_notMem_range u (cds3Y n) (by
        rintro ⟨t, ht⟩
        have hval : (cds3e n t).val = (cds3Y n).val := congrArg Fin.val ht
        have h1 : (cds3e n t).val = t.val := by simp [cds3e, Fin.castSucc]
        have h2 : (cds3Y n).val = n := by simp [cds3Y, Fin.last]
        rw [h1, h2] at hval
        omega)
    have hqY : (m + (Finsupp.single (cds3Y n) (1 : ℕ) : Fin (n + 1) →₀ ℕ)) (cds3Y n) ≠ 0 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    have hq : (u.mapDomain (cds3e n)) (cds3Y n) =
        (m + (Finsupp.single (cds3Y n) (1 : ℕ) : Fin (n + 1) →₀ ℕ)) (cds3Y n) := by
      rw [hu]
    omega
  rw [hc]
  simp

/-- embedding preserves L-membership -/
lemma cds3_embed3_mem_L (n : ℕ) (f : H n 3) (hf : f ∈ L n 3) : cds3_embed3 n f ∈ L (n + 1) 3 := by
  classical
  have hfM : f ∈ M n 3 := by
    have h' : f ∈ {x : H n 3 | x ∈ M n 3 ∧ ∀ i : Fin n, ⟨x.1.pderiv i, x.2.pderiv⟩ ∈ L n 2} := by
      simpa [L] using hf
    exact h'.1
  have hfderiv : ∀ i : Fin n, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ L n 2 := by
    have h' : f ∈ {x : H n 3 | x ∈ M n 3 ∧ ∀ i : Fin n, ⟨x.1.pderiv i, x.2.pderiv⟩ ∈ L n 2} := by
      simpa [L] using hf
    exact h'.2
  change cds3_embed3 n f ∈ {x : H (n + 1) 3 |
    x ∈ M (n + 1) 3 ∧ ∀ i : Fin (n + 1), ⟨x.1.pderiv i, x.2.pderiv⟩ ∈ L (n + 1) 2}
  constructor
  · -- M-membership
    change IsMConvex ((cds3_embed3 n f).1.support : Set (Fin (n + 1) →₀ ℕ)) ∧
      ∀ m : Fin (n + 1) →₀ ℕ, 0 ≤ (cds3_embed3 n f).1.coeff m
    constructor
    · rw [cds3_embed3_support]
      change IsMConvex ((Finset.image (Finsupp.mapDomain (cds3e n)) f.1.support
        : Finset (Fin (n + 1) →₀ ℕ)) : Set (Fin (n + 1) →₀ ℕ))
      have heq : ((Finset.image (Finsupp.mapDomain (cds3e n)) f.1.support
          : Finset (Fin (n + 1) →₀ ℕ)) : Set (Fin (n + 1) →₀ ℕ)) =
          {γ | ∃ α ∈ (f.1.support : Set (Fin n →₀ ℕ)), γ = α.mapDomain (cds3e n)} := by
        ext γ
        constructor
        · intro hγ
          rcases (Finset.mem_image.mp hγ) with ⟨α, hα, hγeq⟩
          exact ⟨α, hα, hγeq.symm⟩
        · rintro ⟨α, hα, rfl⟩
          exact Finset.mem_image.mpr ⟨α, hα, rfl⟩
      rw [heq]
      exact cds3_MConvex_image_embed (A := (f.1.support : Set (Fin n →₀ ℕ))) hfM.1
    · intro m
      exact (cds3_coeff_rename_nonneg (cds3e n) (cds3e_injective n) f.1).2 hfM.2 m
  · -- partials
    intro k
    have hkS : IsStable ((cds3_embed3 n f).1.pderiv k) ∧
      ∀ m : Fin (n + 1) →₀ ℕ, 0 ≤ ((cds3_embed3 n f).1.pderiv k).coeff m := by
      rcases cds3e_or_Y n k with hk | hkY
      · rcases hk with ⟨j, rfl⟩
        have hqS : (⟨f.1.pderiv j, f.2.pderiv⟩ : H n 2) ∈ S n 2 := hfderiv j
        rcases hqS with ⟨hqstab, hqnn⟩
        have hpder : MvPolynomial.pderiv (cds3e n j) (cds3_embed3 n f).1 =
            MvPolynomial.rename (cds3e n) (MvPolynomial.pderiv j f.1) := by
          dsimp [cds3_embed3]
          exact cds3_pderiv_rename n j f.1
        constructor
        · rw [hpder]
          exact cds3_IsStable_rename (cds3e n) (MvPolynomial.pderiv j f.1) hqstab
        · intro m
          rw [hpder]
          exact (cds3_coeff_rename_nonneg (cds3e n) (cds3e_injective n)
            (MvPolynomial.pderiv j f.1)).2 hqnn m
      · subst k
        have hzero : MvPolynomial.pderiv (cds3Y n) (cds3_embed3 n f).1 = 0 := by
          dsimp [cds3_embed3]
          exact cds3_pderivY_rename n f.1
        constructor
        · rw [hzero]
          left
          rfl
        · intro m
          rw [hzero]
          simp
    change (⟨(cds3_embed3 n f).1.pderiv k, (cds3_embed3 n f).2.pderiv⟩ : H (n + 1) 2) ∈ S (n + 1) 2
    change IsStable ((cds3_embed3 n f).1.pderiv k) ∧
      ∀ m : Fin (n + 1) →₀ ℕ, 0 ≤ ((cds3_embed3 n f).1.pderiv k).coeff m
    exact hkS

/-! ## Fold and extraction -/

/-- one deform step as an `H (n+1) 3` element -/
abbrev cds3_deformStep (n : ℕ) (θ : ℝ) (j : Fin n) (g : H (n + 1) 3) : H (n + 1) 3 :=
  DML.defElem (n + 1) 3 θ (cds3Y n) (cds3e n j) g

/-- the value of the deform step -/
lemma cds3_deformStep_val (n : ℕ) (θ : ℝ) (j : Fin n) (g : H (n + 1) 3) :
    (cds3_deformStep n θ j g).1 = cds3_defPolyY n θ j g.1 := by
  rfl

/-- iterated deform over a list of indices (`D_j` applied after the tail) -/
def cds3_fold (n : ℕ) (u : Fin n → ℝ) : List (Fin n) → H (n + 1) 3 → H (n + 1) 3
  | [], g => g
  | j :: l, g => cds3_deformStep n (u j) j (cds3_fold n u l g)

/-- each deform step preserves L-membership -/
lemma cds3_deformStep_mem_L (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (j : Fin n)
    (g : H (n + 1) 3) (hg : g ∈ L (n + 1) 3) : cds3_deformStep n θ j g ∈ L (n + 1) 3 := by
  classical
  rcases deform_mem_L (n + 1) 3 (by omega) θ hθ (cds3Y n) (cds3e n j) g hg with ⟨w, hw, hwval⟩
  have heq : cds3_deformStep n θ j g = w := by
    apply Subtype.ext
    change (DML.defElem (n + 1) 3 θ (cds3Y n) (cds3e n j) g).1 = w.1
    rw [DML.defElem_apply, hwval]
  rwa [heq]

/-- the fold preserves L-membership -/
lemma cds3_fold_mem_L (n : ℕ) (u : Fin n → ℝ) (l : List (Fin n))
    (g : H (n + 1) 3) (hg : g ∈ L (n + 1) 3) (hu : ∀ j : Fin n, 0 ≤ u j) :
    cds3_fold n u l g ∈ L (n + 1) 3 := by
  induction l with
  | nil => simpa [cds3_fold] using hg
  | cons j l ih =>
      simpa [cds3_fold] using (cds3_deformStep_mem_L n (u j) (hu j) j (cds3_fold n u l g) ih)

/-- occurrence-sum over a list -/
def cds3_occSum (n : ℕ) (u : Fin n → ℝ) (l : List (Fin n))
    (f : MvPolynomial (Fin (n + 1)) ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  (l.map (fun j => MvPolynomial.C (u j) * MvPolynomial.pderiv (cds3e n j) f)).sum

/-- restricting the fold to `Y = 0` gives the base (if the base has no `Y`) -/
lemma cds3_fold_zeroLastY (n : ℕ) (u : Fin n → ℝ) (l : List (Fin n))
    (g : H (n + 1) 3) (hg : ∀ m : Fin (n + 1) →₀ ℕ, 0 < m (cds3Y n) → g.1.coeff m = 0) :
    cds3_zeroLastY n (cds3_fold n u l g).1 = g.1 := by
  classical
  induction l with
  | nil =>
      rw [cds3_fold]
      exact cds3_zeroLastY_of_noY g.1 hg
  | cons j l ih =>
      rw [cds3_fold, cds3_deformStep_val]
      unfold cds3_defPolyY
      rw [cds3_zeroLastY_add]
      rw [mul_assoc]
      rw [cds3_zeroLastY_C_mul]
      rw [cds3_zeroLastY_X_Y_mul]
      simp
      exact ih

/-- `∂_Y` of a polynomial with no `Y`-monomials is zero -/
lemma cds3_pderivY_of_noY (n : ℕ) (p : MvPolynomial (Fin (n + 1)) ℝ)
    (hp : ∀ m : Fin (n + 1) →₀ ℕ, 0 < m (cds3Y n) → p.coeff m = 0) :
    MvPolynomial.pderiv (cds3Y n) p = 0 := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_pderiv]
  have hc : p.coeff (m + (Finsupp.single (cds3Y n) (1 : ℕ) : Fin (n + 1) →₀ ℕ)) = 0 := by
    apply hp
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  rw [hc]
  simp

/-- restriction-to-0 of the `Y`-derivative of the fold equals the occurrence sum -/
lemma cds3_extract (n : ℕ) (u : Fin n → ℝ) (l : List (Fin n))
    (g : H (n + 1) 3) (hg : ∀ m : Fin (n + 1) →₀ ℕ, 0 < m (cds3Y n) → g.1.coeff m = 0) :
    cds3_zeroLastY n (MvPolynomial.pderiv (cds3Y n) (cds3_fold n u l g).1) =
      cds3_occSum n u l g.1 := by
  classical
  induction l with
  | nil =>
      have hp : MvPolynomial.pderiv (cds3Y n) g.1 = 0 := cds3_pderivY_of_noY n g.1 hg
      simp [cds3_fold, cds3_occSum, hp, cds3_zeroLastY]
  | cons j l ih =>
      have hmain :
          cds3_zeroLastY n (MvPolynomial.pderiv (cds3Y n) (cds3_fold n u (j :: l) g).1)
            = cds3_occSum n u l g.1 +
                MvPolynomial.C (u j) * MvPolynomial.pderiv (cds3e n j) g.1 := by
        rw [cds3_fold, cds3_deformStep_val]
        rw [cds3_zeroLastY_pderivY_defPolyY]
        rw [ih]
        rw [← cds3_pderiv_castSucc_zeroLastY n j (cds3_fold n u l g).1]
        rw [cds3_fold_zeroLastY n u l g hg]
      rw [hmain]
      unfold cds3_occSum
      rw [List.map_cons, List.sum_cons]
      ring


/-- occurrence-sum over `finRange n` equals the full Finset sum -/
lemma cds3_occSum_finRange (n : ℕ) (u : Fin n → ℝ) (f : MvPolynomial (Fin (n + 1)) ℝ) :
    cds3_occSum n u (List.finRange n) f =
      ∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv (cds3e n j) f := by
  classical
  unfold cds3_occSum
  rw [← List.ofFn_id]
  rw [List.map_ofFn]
  simp [List.sum_ofFn]

/-- a degree-2 homogeneous polynomial not involving `Y`, stable after embedding, is
stable -/
lemma cds3_mem_S_of_embedY_mem_S (n : ℕ) (q : H n 2)
    (he : (⟨MvPolynomial.rename (cds3e n) q.1, by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact cds3_rename_isHomogeneous n q.1 (by simpa [MvPolynomial.mem_homogeneousSubmodule] using q.2)⟩ : H (n + 1) 2) ∈ S (n + 1) 2) :
    q ∈ S n 2 := by
  classical
  rcases he with ⟨hestab, henn⟩
  change IsStable q.1 ∧ ∀ m : Fin n →₀ ℕ, 0 ≤ q.1.coeff m
  constructor
  · exact cds3_IsStable_rename_castSucc q.1 hestab
  · intro m
    have hc : q.1.coeff m =
        (MvPolynomial.rename (cds3e n) q.1).coeff (m.mapDomain (cds3e n)) := by
      exact (MvPolynomial.coeff_rename_mapDomain (cds3e n) (cds3e_injective n) q.1 m).symm
    rw [hc]
    exact henn (m.mapDomain (cds3e n))

/-- `zeroLastY` keeps an `S (n+1) 2` element in `S (n+1) 2` -/
lemma cds3_zeroLastY_mem_S (n : ℕ) (P : H (n + 1) 2) (hP : P ∈ S (n + 1) 2) :
    (⟨cds3_zeroLastY n P.1, cds3_zeroLastY_isHomogeneous n P.1 P.2⟩ : H (n + 1) 2) ∈ S (n + 1) 2 := by
  rcases hP with ⟨hstab, hnn⟩
  change IsStable (cds3_zeroLastY n P.1) ∧ ∀ m : Fin (n + 1) →₀ ℕ, 0 ≤ (cds3_zeroLastY n P.1).coeff m
  constructor
  · exact cds3_zeroLastY_IsStable n P.1 hstab
  · intro m
    rw [cds3_zeroLastY_coeff]
    by_cases hm : m (cds3Y n) = 0
    · simp [hm, hnn m]
    · simp [hm]

/-- the directional-derivative polynomial is homogeneous of degree 2 -/
lemma cds3_sum_pderiv_isHomogeneous (n : ℕ) (f : H n 3) (u : Fin n → ℝ) :
    (∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv j f.1).IsHomogeneous 2 := by
  classical
  refine MvPolynomial.IsHomogeneous.sum (s := Finset.univ)
    (fun j : Fin n => MvPolynomial.C (u j) * MvPolynomial.pderiv j f.1) 2 ?_
  intro j hj
  have hp : (MvPolynomial.pderiv j f.1).IsHomogeneous 2 := by
    simpa using f.2.pderiv
  exact (MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) (u j)).mul hp

/-! ## Main theorem -/

/-- directional derivative at degree 3 stays in `S n 2` -/
theorem cds3_directional_deriv_three_mem_S (n : ℕ) (f : H n 3) (hf : f ∈ L n 3)
    (u : Fin n → ℝ) (hu : ∀ j : Fin n, 0 ≤ u j) :
    ∃ q : H n 2, q ∈ S n 2 ∧
      q.1 = ∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv j f.1 := by
  classical
  let fe : H (n + 1) 3 := cds3_embed3 n f
  have hfe : fe ∈ L (n + 1) 3 := by
    dsimp [fe]
    exact cds3_embed3_mem_L n f hf
  have hfenoY : ∀ m : Fin (n + 1) →₀ ℕ, 0 < m (cds3Y n) → fe.1.coeff m = 0 := by
    intro m hm
    dsimp [fe, cds3_embed3]
    apply MvPolynomial.coeff_rename_eq_zero (f := cds3e n) f.1
    intro u hu
    have huY : (u.mapDomain (cds3e n)) (cds3Y n) = 0 := by
      exact Finsupp.mapDomain_of_notMem_range u (cds3Y n) (by
        rintro ⟨t, ht⟩
        have hval : (cds3e n t).val = (cds3Y n).val := congrArg Fin.val ht
        have h1 : (cds3e n t).val = t.val := by simp [cds3e, Fin.castSucc]
        have h2 : (cds3Y n).val = n := by simp [cds3Y, Fin.last]
        rw [h1, h2] at hval
        omega)
    have hmc : m (cds3Y n) ≠ 0 := by omega
    have hmapY : (u.mapDomain (cds3e n)) (cds3Y n) = m (cds3Y n) := by
      rw [hu]
    omega
  let W : H (n + 1) 3 := cds3_fold n u (List.finRange n) fe
  have hW : W ∈ L (n + 1) 3 := by
    dsimp [W]
    exact cds3_fold_mem_L n u (List.finRange n) fe hfe hu
  have hY : (⟨W.1.pderiv (cds3Y n), W.2.pderiv⟩ : H (n + 1) 2) ∈ S (n + 1) 2 := by
    have hW' : W ∈ {x : H (n + 1) 3 |
        x ∈ M (n + 1) 3 ∧ ∀ i : Fin (n + 1), ⟨x.1.pderiv i, x.2.pderiv⟩ ∈ L (n + 1) 2} := by
      simpa [L] using hW
    exact hW'.2 (cds3Y n)
  have hR0 : (⟨cds3_zeroLastY n (W.1.pderiv (cds3Y n)),
      cds3_zeroLastY_isHomogeneous n (W.1.pderiv (cds3Y n)) W.2.pderiv⟩ : H (n + 1) 2) ∈ S (n + 1) 2 :=
    cds3_zeroLastY_mem_S n (⟨W.1.pderiv (cds3Y n), W.2.pderiv⟩ : H (n + 1) 2) hY
  have hextract : cds3_zeroLastY n (W.1.pderiv (cds3Y n)) =
      ∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv (cds3e n j) fe.1 := by
    calc
      cds3_zeroLastY n (W.1.pderiv (cds3Y n))
          = cds3_occSum n u (List.finRange n) fe.1 := by
            dsimp [W]
            exact cds3_extract n u (List.finRange n) fe hfenoY
      _ = ∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv (cds3e n j) fe.1 := by
            exact cds3_occSum_finRange n u fe.1
  let q : H n 2 := ⟨∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv j f.1,
    by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact cds3_sum_pderiv_isHomogeneous n f u⟩
  have hrename : MvPolynomial.rename (cds3e n) q.1 = cds3_zeroLastY n (W.1.pderiv (cds3Y n)) := by
    rw [hextract]
    dsimp [q]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hpder : MvPolynomial.pderiv (cds3e n j) fe.1 =
        MvPolynomial.rename (cds3e n) (MvPolynomial.pderiv j f.1) := by
      dsimp [fe, cds3_embed3]
      exact cds3_pderiv_rename n j f.1
    rw [map_mul]
    rw [MvPolynomial.rename_C]
    rw [hpder]
  have hqS : q ∈ S n 2 := by
    have hS' : (⟨MvPolynomial.rename (cds3e n) q.1, by
        rw [MvPolynomial.mem_homogeneousSubmodule]
        exact cds3_rename_isHomogeneous n q.1 q.2⟩ : H (n + 1) 2) ∈ S (n + 1) 2 := by
      rcases hR0 with ⟨hstab0, hnn0⟩
      change IsStable (MvPolynomial.rename (cds3e n) q.1) ∧
        ∀ m : Fin (n + 1) →₀ ℕ, 0 ≤ (MvPolynomial.rename (cds3e n) q.1).coeff m
      constructor
      · rw [hrename]
        exact hstab0
      · intro m
        rw [hrename]
        exact hnn0 m
    exact cds3_mem_S_of_embedY_mem_S n q hS'
  refine ⟨q, hqS, ?_⟩
  dsimp [q]



/-- The exact requested theorem: for a Lorentzian cubic `f` and `u ≥ 0`, the
directional derivative `Σⱼ uⱼ·∂ⱼf` is a Lorentzian quadratic. -/
theorem cubic_directional_deriv_stable (n : ℕ) (hn : 0 < n)
    (f : Commons.LorentzianPolynomials.H n 3) (hf : f ∈ Commons.LorentzianPolynomials.L n 3)
    (u : Fin n → ℝ) (hu : ∀ j : Fin n, 0 ≤ u j) :
    ∃ g : Commons.LorentzianPolynomials.H n 2,
      g ∈ Commons.LorentzianPolynomials.L n 2 ∧
        g.1 = ∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv j f.1 := by
  classical
  rcases cds3_directional_deriv_three_mem_S n f hf u hu with ⟨q, hqS, hq⟩
  refine ⟨q, ?_, hq⟩
  simpa [L] using hqS

end
end Commons.LorentzianPolynomials
