import Mathlib
import Submission.Nocommon
import Submission.CubeLemma

/-!
# Core of `lem:squarefree_nocommon`: squarefree small integer combination

This file implements the proof described in the header comment of the original
skeleton.  See `Submission.NocommonCore.nocommon_core`.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace Submission.NocommonCore

open Submission.Nocommon

/-- The family `s i = (S i).map (algebraMap ℤ ℂ)` of complex polynomials. -/
private def sOf (K : ℕ) (S : Fin (K + 1) → Polynomial ℤ) (i : Fin (K + 1)) : Polynomial ℂ :=
  (S i).map (algebraMap ℤ ℂ)

/-- The coefficient ring `ℂ[X_1,…,X_K]`. -/
private abbrev XR (K : ℕ) := MvPolynomial (Fin K) ℂ

/-- Embedding of `ℂ[Y]` into `XR K[Y]` (coefficients constant in `X`). -/
private def cEmb (K : ℕ) : Polynomial ℂ →+* Polynomial (XR K) :=
  Polynomial.mapRingHom (MvPolynomial.C (R := ℂ) (σ := Fin K))

/-- The generic linear combination polynomial `F(Y) = s₀(Y) + Σ X_i·sᵢ(Y)`. -/
private def mkF (K : ℕ) (t : Fin (K + 1) → Polynomial ℂ) : Polynomial (XR K) :=
  cEmb K (t 0) + ∑ i : Fin K, Polynomial.C (MvPolynomial.X i) * cEmb K (t (Fin.succ i))

section BasicFacts

variable {K : ℕ}

/-- The `j`-th `Y`-coefficient of `mkF` is affine-linear in the `X`-variables. -/
lemma mkF_coeff (t : Fin (K + 1) → Polynomial ℂ) (j : ℕ) :
    (mkF K t).coeff j =
      (MvPolynomial.C ((t 0).coeff j) : XR K) +
        ∑ i : Fin K, MvPolynomial.X i * (MvPolynomial.C ((t (Fin.succ i)).coeff j) : XR K) := by
  rw [mkF]
  rw [Polynomial.coeff_add]
  -- coefficient of the sum over i
  rw [Polynomial.finsetSum_coeff]
  simp [cEmb, Polynomial.coeff_map, Polynomial.coeff_C_mul, mul_comm]

/-- Each `Y`-coefficient of `mkF` has `X`-total-degree `≤ 1`. -/
lemma mkF_coeff_totalDegree_le_one (t : Fin (K + 1) → Polynomial ℂ) (j : ℕ) :
    ((mkF K t).coeff j).totalDegree ≤ 1 := by
  rw [mkF_coeff]
  refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
  refine max_le ?_ ?_
  · simp [MvPolynomial.totalDegree_C]
  · refine le_trans (MvPolynomial.totalDegree_finsetSum_le (s := Finset.univ)
      (d := 1) ?_) (by simp)
    intro i hi
    have h1x : (MvPolynomial.X i : XR K).totalDegree = 1 := by
      exact MvPolynomial.totalDegree_X i
    have hC : (MvPolynomial.C ((t (Fin.succ i)).coeff j) : XR K).totalDegree = 0 :=
      MvPolynomial.totalDegree_C _
    calc
      (MvPolynomial.X i * MvPolynomial.C ((t (Fin.succ i)).coeff j)).totalDegree
          ≤ (MvPolynomial.X i).totalDegree + (MvPolynomial.C ((t (Fin.succ i)).coeff j)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 := by simp [h1x, hC]

/-- Vanishing of the coefficients above `m`. -/
lemma mkF_coeff_eq_zero_of_lt {m : ℕ} (t : Fin (K + 1) → Polynomial ℂ)
    (hdeg : ∀ i, (t i).natDegree ≤ m) {j : ℕ} (hj : m < j) :
    (mkF K t).coeff j = 0 := by
  rw [mkF_coeff]
  have ht0 : (t 0).coeff j = 0 := by
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (by have h0 := hdeg (0 : Fin (K + 1)); omega)
  have hti : ∀ i : Fin K, (t (Fin.succ i)).coeff j = 0 := fun i =>
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (by have h0 := hdeg (Fin.succ i); omega)
  rw [ht0]
  simp [hti]

/-- Nonzero-ness of the degree-`m` leading coefficient (requires `m ≠ 0` so that
`(t 0).natDegree = m` forces `t 0 ≠ 0`). -/
lemma mkF_coeff_ne_zero_of_lead {m : ℕ} (t : Fin (K + 1) → Polynomial ℂ)
    (hlead : (t 0).natDegree = m) (hm : m ≠ 0) : (mkF K t).coeff m ≠ 0 := by
  have ht0nz : t 0 ≠ 0 := by
    intro hz
    rw [hz] at hlead
    simp at hlead
    exact hm hlead.symm
  -- evaluate all X-variables at 0
  let ev0 : XR K →+* ℂ := MvPolynomial.eval (fun _ : Fin K => (0 : ℂ))
  have hcoeff0 : (t 0).coeff m ≠ 0 := by
    rw [← hlead, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr ht0nz
  intro hz
  have hmk : ev0 ((mkF K t).coeff m) = (t 0).coeff m := by
    rw [mkF_coeff]
    simp [ev0]
  exact hcoeff0 (by simpa [hmk] using congrArg ev0 hz)

/-- The degree of `mkF` is exactly `m` when `deg(t 0) = m` and `m ≠ 0`. -/
lemma mkF_natDegree {m : ℕ} (t : Fin (K + 1) → Polynomial ℂ)
    (hdeg : ∀ i, (t i).natDegree ≤ m) (hlead : (t 0).natDegree = m) (hm : m ≠ 0) :
    (mkF K t).natDegree = m := by
  apply le_antisymm
  · exact (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => mkF_coeff_eq_zero_of_lt t hdeg hN)
  · by_contra hlt
    have hcoeff0 : (mkF K t).coeff m ≠ 0 := mkF_coeff_ne_zero_of_lead t hlead hm
    have hzero : (mkF K t).coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    exact hcoeff0 hzero

end BasicFacts

section HomComp

variable {σ : Type*}

lemma range_sum_eq {M : Type*} [AddCommMonoid M] {a : ℕ} {f : ℕ → M}
    (hf : ∀ r, a < r → f r = 0) {b : ℕ} (hab : a ≤ b) :
    (∑ r ∈ Finset.range (a + 1), f r) = (∑ r ∈ Finset.range (b + 1), f r) := by
  refine Finset.sum_subset ?hs ?hz
  · intro r hr
    exact Finset.mem_range.mpr (by have : r < a + 1 := Finset.mem_range.mp hr; omega)
  · intro r hr hr'
    have : a < r := by
      rw [Finset.mem_range] at hr'
      omega
    exact hf r this

/-- Decompose `x` into its homogeneous components of degree `≤ e`. -/
lemma hc_sum_range (x : MvPolynomial σ ℂ) (e : ℕ) (hxe : x.totalDegree ≤ e) :
    x = ∑ r ∈ Finset.range (e + 1), MvPolynomial.homogeneousComponent r x := by
  calc
    x = ∑ r ∈ Finset.range (x.totalDegree + 1), MvPolynomial.homogeneousComponent r x := by
        simp [MvPolynomial.sum_homogeneousComponent x]
    _ = ∑ r ∈ Finset.range (e + 1), MvPolynomial.homogeneousComponent r x := by
        refine (range_sum_eq (f := fun r => MvPolynomial.homogeneousComponent r x) ?_ hxe)
        intro r hr
        exact MvPolynomial.homogeneousComponent_eq_zero r x (by omega)

lemma hcomp_eq_self {p : MvPolynomial σ ℂ} {n : ℕ} (hp : p.IsHomogeneous n) :
    MvPolynomial.homogeneousComponent n p = p := by
  classical
  have hp' : p ∈ MvPolynomial.homogeneousSubmodule σ ℂ n := hp
  rw [MvPolynomial.homogeneousComponent_of_mem (m := n) hp']
  simp

lemma hcomp_of_ne {p : MvPolynomial σ ℂ} {m n : ℕ} (hp : p.IsHomogeneous n) (hmn : m ≠ n) :
    MvPolynomial.homogeneousComponent m p = 0 := by
  classical
  have hp' : p ∈ MvPolynomial.homogeneousSubmodule σ ℂ n := hp
  rw [MvPolynomial.homogeneousComponent_of_mem (m := m) hp']
  simp [hmn]

lemma hc_homogeneous_mul {x : MvPolynomial σ ℂ} {r : ℕ} (hx : x.IsHomogeneous r)
    {y : MvPolynomial σ ℂ} {s : ℕ} (hy : y.IsHomogeneous s) (e : ℕ) :
    MvPolynomial.homogeneousComponent e (x * y) = if r + s = e then x * y else 0 := by
  by_cases he : r + s = e
  · rw [if_pos he]
    have hmul : (x * y).IsHomogeneous (r + s) := MvPolynomial.IsHomogeneous.mul hx hy
    simpa [he] using hcomp_eq_self hmul
  · rw [if_neg he]
    have hmul : (x * y).IsHomogeneous (r + s) := MvPolynomial.IsHomogeneous.mul hx hy
    exact hcomp_of_ne hmul (by intro h; apply he; exact h.symm)

/-- Top-degree component of a product (when degree bounds are `a` and `b`). -/
lemma hc_top_mul (x y : MvPolynomial σ ℂ) (a b : ℕ)
    (hxa : x.totalDegree ≤ a) (hyb : y.totalDegree ≤ b) :
    MvPolynomial.homogeneousComponent (a + b) (x * y) =
      MvPolynomial.homogeneousComponent a x * MvPolynomial.homogeneousComponent b y := by
  classical
  have hxeq : x = ∑ r ∈ Finset.range (a + 1), MvPolynomial.homogeneousComponent r x :=
    hc_sum_range x a hxa
  have hyeq : y = ∑ s ∈ Finset.range (b + 1), MvPolynomial.homogeneousComponent s y :=
    hc_sum_range y b hyb
  calc
    MvPolynomial.homogeneousComponent (a + b) (x * y)
        = MvPolynomial.homogeneousComponent (a + b)
            ((∑ r ∈ Finset.range (a + 1), MvPolynomial.homogeneousComponent r x) *
              (∑ s ∈ Finset.range (b + 1), MvPolynomial.homogeneousComponent s y)) := by
          rw [← hxeq, ← hyeq]
    _ = ∑ r ∈ Finset.range (a + 1), ∑ s ∈ Finset.range (b + 1),
          MvPolynomial.homogeneousComponent (a + b)
            (MvPolynomial.homogeneousComponent r x * MvPolynomial.homogeneousComponent s y) := by
          rw [Finset.sum_mul]
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          rw [map_sum]
    _ = ∑ r ∈ Finset.range (a + 1), ∑ s ∈ Finset.range (b + 1),
          if r + s = a + b
            then MvPolynomial.homogeneousComponent r x * MvPolynomial.homogeneousComponent s y
            else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro s hs
          rw [hc_homogeneous_mul (MvPolynomial.homogeneousComponent_isHomogeneous r x)
            (MvPolynomial.homogeneousComponent_isHomogeneous s y) (a + b)]
    _ = MvPolynomial.homogeneousComponent a x * MvPolynomial.homogeneousComponent b y := by
          rw [Finset.sum_eq_single a]
          · rw [Finset.sum_eq_single b]
            · simp
            · intro s hs hsb
              rw [if_neg]
              intro h
              apply hsb
              have hs' := Finset.mem_range.mp hs
              omega
            · intro hnb
              exfalso
              exact hnb (Finset.mem_range.mpr (by omega))
          · intro r hr hra
            have hrle : r < a := by
              have hr' := Finset.mem_range.mp hr
              omega
            rw [Finset.sum_eq_zero]
            intro s hs
            rw [if_neg]
            intro h
            have hs' := Finset.mem_range.mp hs
            omega
          · intro hna
            exfalso
            exact hna (Finset.mem_range.mpr (by omega))

end HomComp

section GradedPoly

variable {K : ℕ}

/-- The degree in the `X`-variables of a polynomial over `ℂ[X_1,…,X_K]`: the maximal
`X`-total-degree of its `Y`-coefficients. -/
noncomputable def xdeg {K : ℕ} (P : Polynomial (XR K)) : ℕ :=
  (Finset.range (P.natDegree + 1)).sup (fun j => (P.coeff j).totalDegree)

/-- The part of `P` whose `Y`-coefficients are homogeneous of `X`-degree `e`. -/
noncomputable def xp {K : ℕ} (e : ℕ) (P : Polynomial (XR K)) : Polynomial (XR K) :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    Polynomial.monomial j (MvPolynomial.homogeneousComponent e (P.coeff j))

/-- The `Y`-coefficients of `P` have `X`-degree bounded by `xdeg P`. -/
lemma coeff_totalDegree_le_xdeg {K : ℕ} (P : Polynomial (XR K)) (j : ℕ) :
    (P.coeff j).totalDegree ≤ xdeg P := by
  by_cases hj : j ∈ P.support
  · have hjn : j ≤ P.natDegree := by
      by_contra h
      have hc : P.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      exact (Polynomial.mem_support_iff.mp hj) hc
    exact Finset.le_sup (f := fun j => (P.coeff j).totalDegree)
      (Finset.mem_range.mpr (by omega))
  · have hc : P.coeff j = 0 := by
      by_contra h
      exact hj (Polynomial.mem_support_iff.mpr h)
    simp [hc]


/-- Coefficientwise description of `xp`. -/
lemma xp_coeff {K : ℕ} (e : ℕ) (P : Polynomial (XR K)) (j : ℕ) :
    (xp e P).coeff j = MvPolynomial.homogeneousComponent e (P.coeff j) := by
  classical
  by_cases hjn : j ≤ P.natDegree
  · -- j in range
    rw [xp]
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      rw [Polynomial.coeff_monomial, if_neg hkj]
    · intro hnj
      exfalso
      exact hnj (Finset.mem_range.mpr (by omega))
  · have hcoeff : P.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [xp]
    rw [Polynomial.finsetSum_coeff]
    rw [hcoeff]
    simp
    rw [Finset.sum_eq_zero]
    intro k hk
    have hkj : j ≠ k := by
      have hk' := Finset.mem_range.mp hk
      omega
    rw [Polynomial.coeff_monomial, if_neg (by exact fun h : k = j => hkj h.symm)]

/-- Top-`X`-degree piece of a product is the product of the top pieces. -/
lemma xp_mul_top {K : ℕ} (P Q : Polynomial (XR K)) :
    xp (xdeg P + xdeg Q) (P * Q) = xp (xdeg P) P * xp (xdeg Q) Q := by
  classical
  apply Polynomial.ext
  intro j
  rw [xp_coeff]
  rw [Polynomial.coeff_mul]
  rw [map_sum]
  rw [Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [xp_coeff, xp_coeff]
  exact hc_top_mul (P.coeff x.1) (Q.coeff x.2) (xdeg P) (xdeg Q)
    (coeff_totalDegree_le_xdeg P x.1) (coeff_totalDegree_le_xdeg Q x.2)



/-- `mkF` has `xdeg ≤ 1`: its coefficients are affine in `X`. -/
lemma mkF_xdeg_le_one (t : Fin (K + 1) → Polynomial ℂ) : xdeg (mkF K t) ≤ 1 := by
  unfold xdeg
  exact Finset.sup_le (fun j hj => mkF_coeff_totalDegree_le_one t j)

/-- If every coefficient has small total degree, the top part vanishes. -/
lemma xp_eq_zero_of_coeff_totalDegree_lt {K : ℕ} (e : ℕ) (P : Polynomial (XR K))
    (h : ∀ j : ℕ, (P.coeff j).totalDegree < e) : xp e P = 0 := by
  apply Polynomial.ext
  intro j
  rw [xp_coeff]
  exact MvPolynomial.homogeneousComponent_eq_zero e (P.coeff j) (h j)

/-- A nonzero homogeneous-degree part implies the total degree is at least it. -/
lemma xdeg_ge_of_xp_ne_zero {K : ℕ} (e : ℕ) (P : Polynomial (XR K))
    (h : xp e P ≠ 0) : e ≤ xdeg P := by
  by_contra hc
  have hlt : xdeg P < e := by omega
  have hzero : ∀ j : ℕ, (P.coeff j).totalDegree < e := fun j =>
    lt_of_le_of_lt (coeff_totalDegree_le_xdeg P j) hlt
  exact h (xp_eq_zero_of_coeff_totalDegree_lt e P hzero)

/-- If `c ≠ 0`, the `totalDegree c`-homogeneous component of `c` is nonzero. -/
lemma hc_totalDegree_ne_zero {K : ℕ} (c : XR K) (hc0 : c ≠ 0) :
    MvPolynomial.homogeneousComponent (c.totalDegree) c ≠ 0 := by
  classical
  have hsup : c.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, MvPolynomial.support_eq_empty]
    exact hc0
  let f : (Fin K →₀ ℕ) → ℕ := fun s => s.sum (fun _ e => e)
  obtain ⟨μ, hμsup, hmax⟩ := Finset.exists_max_image c.support f hsup
  have hdeg_eq : f μ = c.totalDegree := by
    apply le_antisymm
    · exact MvPolynomial.le_totalDegree hμsup
    · unfold MvPolynomial.totalDegree
      exact Finset.sup_le (fun x hx => hmax x hx)
  have hcμ : c.coeff μ ≠ 0 := MvPolynomial.mem_support_iff.mp hμsup
  have hc' : (MvPolynomial.homogeneousComponent (c.totalDegree) c).coeff μ ≠ 0 := by
    rw [MvPolynomial.coeff_homogeneousComponent]
    rw [if_pos]
    · exact hcμ
    · have : Finsupp.degree μ = f μ := by
        rw [Finsupp.degree_apply]
        rfl
      rw [this, hdeg_eq]
  intro hzero
  exact hc' (by rw [hzero]; simp)



/-- The top-`X`-degree part of a nonzero polynomial is nonzero. -/
lemma xp_xdeg_ne_zero {K : ℕ} (P : Polynomial (XR K)) (hP : P ≠ 0) :
    xp (xdeg P) P ≠ 0 := by
  classical
  by_contra hz
  by_cases ha0 : xdeg P = 0
  · apply hP
    apply Polynomial.ext
    intro j
    have hle : (P.coeff j).totalDegree ≤ 0 := by
      have h := coeff_totalDegree_le_xdeg P j
      rw [ha0] at h
      exact h
    have hde := hc_sum_range (P.coeff j) 0 hle
    calc
      P.coeff j = MvPolynomial.homogeneousComponent 0 (P.coeff j) := by simpa using hde
      _ = (xp 0 P).coeff j := by rw [xp_coeff]
      _ = 0 := by
        have hz0 : xp 0 P = 0 := by simpa [ha0] using hz
        rw [hz0]
        simp
  · have hpos : 0 < xdeg P := Nat.pos_of_ne_zero ha0
    have hdecomp : ∀ j : ℕ, P.coeff j =
        ∑ e ∈ Finset.range (xdeg P), MvPolynomial.homogeneousComponent e (P.coeff j) := by
      intro j
      have hfull := hc_sum_range (P.coeff j) (xdeg P) (coeff_totalDegree_le_xdeg P j)
      have htail : MvPolynomial.homogeneousComponent (xdeg P) (P.coeff j) = 0 := by
        have hc : (xp (xdeg P) P).coeff j = 0 := by rw [hz]; simp
        simpa [xp_coeff] using hc
      calc
        P.coeff j = ∑ e ∈ Finset.range (xdeg P + 1),
            MvPolynomial.homogeneousComponent e (P.coeff j) := hfull
        _ = (∑ e ∈ Finset.range (xdeg P),
            MvPolynomial.homogeneousComponent e (P.coeff j)) +
            MvPolynomial.homogeneousComponent (xdeg P) (P.coeff j) := by
              rw [Finset.sum_range_succ]
        _ = ∑ e ∈ Finset.range (xdeg P),
            MvPolynomial.homogeneousComponent e (P.coeff j) := by rw [htail]; simp
    have hle_all : ∀ j : ℕ, (P.coeff j).totalDegree ≤ xdeg P - 1 := by
      intro j
      rw [hdecomp j]
      refine MvPolynomial.totalDegree_finsetSum_le (s := Finset.range (xdeg P))
        (d := xdeg P - 1) ?_
      intro e he
      have he' : e < xdeg P := Finset.mem_range.mp he
      have hhom := MvPolynomial.homogeneousComponent_isHomogeneous e (P.coeff j)
      exact le_trans (MvPolynomial.IsHomogeneous.totalDegree_le hhom) (by omega)
    have hle : xdeg P ≤ xdeg P - 1 := by
      unfold xdeg
      exact Finset.sup_le (fun j hj => hle_all j)
    omega


/-- A polynomial of `X`-total-degree zero is the image of a `ℂ[Y]` polynomial under `cEmb`. -/
lemma cEmb_eq_of_xdeg_zero {K : ℕ} (G : Polynomial (XR K)) (hG : xdeg G = 0) :
    ∃ G0 : Polynomial ℂ, G = cEmb K G0 := by
  classical
  -- coefficients of G are constants in X
  have hconst : ∀ j : ℕ, G.coeff j = MvPolynomial.C
      (MvPolynomial.coeff (0 : Fin K →₀ ℕ) (G.coeff j)) := by
    intro j
    have hle : (G.coeff j).totalDegree ≤ 0 := by
      have h := coeff_totalDegree_le_xdeg G j
      rw [hG] at h
      exact h
    have ht : (G.coeff j).totalDegree = 0 := le_antisymm hle (Nat.zero_le _)
    apply MvPolynomial.ext
    intro μ
    by_cases hμ : μ = 0
    · subst μ
      simp [MvPolynomial.coeff_C]
    · have hμc : (G.coeff j).coeff μ = 0 := by
        by_contra hc
        have hmem : μ ∈ (G.coeff j).support := MvPolynomial.mem_support_iff.mpr hc
        have hle0 := MvPolynomial.le_totalDegree hmem
        rw [ht] at hle0
        have hz : (μ.sum (fun _ e => e)) = 0 := le_antisymm hle0 (Nat.zero_le _)
        have hμ' : μ = 0 := by
          apply Finsupp.ext
          intro i
          by_cases hi : i ∈ μ.support
          · have hle_i : μ i ≤ μ.sum (fun _ e => e) := by
              calc
                μ i = ((Finsupp.single i (μ i)).sum (fun _ e => e)) := by
                  simp [Finsupp.sum_single_index]
                _ ≤ μ.sum (fun _ e => e) := by
                  exact Finsupp.single_le_sum (f := μ) (g := fun _ e => e)
                    (h := fun _ _ => Nat.zero_le _) i
            have hle0' : μ i ≤ 0 := by
              calc
                μ i ≤ μ.sum (fun _ e => e) := hle_i
                _ = 0 := hz
            exact le_antisymm hle0' (Nat.zero_le _)
          · simpa [Finsupp.notMem_support_iff] using hi
        exact hμ hμ'
      rw [hμc, MvPolynomial.coeff_C, if_neg (by exact fun h : 0 = μ => hμ h.symm)]
  let G0 : Polynomial ℂ := G.support.sum (fun j => Polynomial.monomial j
    (MvPolynomial.coeff (0 : Fin K →₀ ℕ) (G.coeff j)))
  refine ⟨G0, ?_⟩
  apply Polynomial.ext
  intro j
  by_cases hj : j ∈ G.support
  · have hc0 : G0.coeff j = MvPolynomial.coeff (0 : Fin K →₀ ℕ) (G.coeff j) := by
      simp [G0, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k hk hkj
        rw [Polynomial.coeff_monomial, if_neg hkj]
      · intro hnj
        exact False.elim (hnj hj)
    calc
      G.coeff j = MvPolynomial.C (MvPolynomial.coeff (0 : Fin K →₀ ℕ) (G.coeff j)) := by
        exact hconst j
      _ = MvPolynomial.C (G0.coeff j) := by rw [hc0]
      _ = (cEmb K G0).coeff j := by
        simp [cEmb, Polynomial.coeff_map]
  · have hc : G.coeff j = 0 := by
      by_contra h
      exact hj (Polynomial.mem_support_iff.mpr h)
    have hc0 : G0.coeff j = 0 := by
      simp [G0, Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro k hk
      rw [Polynomial.coeff_monomial, if_neg (by intro h; exact hj (by rw [← h]; exact hk))]
    calc
      G.coeff j = 0 := hc
      _ = MvPolynomial.C (G0.coeff j) := by rw [hc0]; simp
      _ = (cEmb K G0).coeff j := by
        simp [cEmb, Polynomial.coeff_map]

lemma mkF_xp_eq_zero_of_two_le {K : ℕ} (t : Fin (K + 1) → Polynomial ℂ) {e : ℕ}
    (he : 2 ≤ e) : xp e (mkF K t) = 0 := by
  apply xp_eq_zero_of_coeff_totalDegree_lt e (mkF K t)
  intro j
  exact lt_of_le_of_lt (mkF_coeff_totalDegree_le_one t j) (by omega)

/-- The affine polynomial `mkF K t` can only factor into polynomials one of which is
constant in the `X`-variables. -/
lemma affine_factor {K : ℕ} (t : Fin (K + 1) → Polynomial ℂ) (G H : Polynomial (XR K))
    (hF : mkF K t = G * H) (hF0 : mkF K t ≠ 0) :
    (∃ G0 : Polynomial ℂ, G = cEmb K G0) ∨ (∃ H0 : Polynomial ℂ, H = cEmb K H0) := by
  classical
  by_cases hG0 : xdeg G = 0
  · left
    exact cEmb_eq_of_xdeg_zero G hG0
  · by_cases hH0 : xdeg H = 0
    · right
      exact cEmb_eq_of_xdeg_zero H hH0
    · exfalso
      have hG1 : 1 ≤ xdeg G := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hG0)
      have hH1 : 1 ≤ xdeg H := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hH0)
      have hGnz : G ≠ 0 := by
        intro h
        apply hF0
        rw [hF, h]
        simp
      have hHnz : H ≠ 0 := by
        intro h
        apply hF0
        rw [hF, h]
        simp
      have htopG : xp (xdeg G) G ≠ 0 := xp_xdeg_ne_zero G hGnz
      have htopH : xp (xdeg H) H ≠ 0 := xp_xdeg_ne_zero H hHnz
      have hprod : xp (xdeg G + xdeg H) (G * H) ≠ 0 := by
        rw [xp_mul_top]
        exact mul_ne_zero htopG htopH
      have hF' : xp (xdeg G + xdeg H) (mkF K t) ≠ 0 := by
        simpa [hF] using hprod
      have he2 : 2 ≤ xdeg G + xdeg H := by omega
      exact hF' (mkF_xp_eq_zero_of_two_le t he2)


/-- Nonconstant complex polynomials have a complex root. -/
lemma exists_root_of_one_le_natDegree (p : Polynomial ℂ) (hp : 1 ≤ p.natDegree) :
    ∃ z : ℂ, p.eval z = 0 := by
  have hne : p ≠ 0 := by
    intro h
    rw [h] at hp
    simp at hp
  have hdeg : 0 < p.degree := by
    rw [Polynomial.degree_eq_natDegree hne]
    exact_mod_cast hp
  rcases Complex.exists_root hdeg with ⟨z, hz⟩
  exact ⟨z, hz⟩

/-- If a `ℂ[Y]`-polynomial divides all members of the family, all members share a root. -/
lemma common_root_of_dvd_family {K : ℕ} (t : Fin (K + 1) → Polynomial ℂ) (G0 : Polynomial ℂ)
    (hdeg : 1 ≤ G0.natDegree)
    (hdiv0 : G0 ∣ t 0) (hdiv : ∀ i : Fin K, G0 ∣ t (Fin.succ i)) :
    ∃ z : ℂ, ∀ i : Fin (K + 1), (t i).eval z = 0 := by
  rcases exists_root_of_one_le_natDegree G0 hdeg with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  intro i
  refine Fin.cases (motive := fun j => (t j).eval z = 0) ?_ ?_ i
  · -- i = 0
    rcases hdiv0 with ⟨q, hq⟩
    rw [hq]
    simp [hz]
  · intro i
    rcases hdiv i with ⟨q, hq⟩
    rw [hq]
    simp [hz]

/-- Evaluating the `X`-variables at `0` turns `mkF` into the constant member `t 0`. -/
lemma mkF_map_eval (t : Fin (K + 1) → Polynomial ℂ) (w : Fin K → ℂ) :
    (mkF K t).map (MvPolynomial.eval w) =
      t 0 + ∑ i : Fin K, Polynomial.C (w i) * t (Fin.succ i) := by
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_map, mkF_coeff]
  rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff]
  rw [map_add, map_sum]
  simp [MvPolynomial.eval, Polynomial.coeff_C_mul]






/-- Evaluation of a mapped integer polynomial agrees with `aeval`. -/
lemma map_eval_eq_aeval (S : Polynomial ℤ) (z : ℂ) :
    (S.map (algebraMap ℤ ℂ)).eval z = Polynomial.aeval z S := by
  rw [Polynomial.aeval_def]
  change eval₂ (RingHom.id ℂ) z (S.map (algebraMap ℤ ℂ)) = eval₂ (algebraMap ℤ ℂ) z S
  exact (Polynomial.eval₂_map (p := S) (f := algebraMap ℤ ℂ) (g := RingHom.id ℂ)
    (x := z)).trans (by simp)

/-- Evaluating the `X`-variables at `0` turns `mkF` into the constant member `t 0`. -/
lemma mkF_map_eval_zero (t : Fin (K + 1) → Polynomial ℂ) :
    (mkF K t).map (MvPolynomial.eval (fun _ : Fin K => (0 : ℂ))) = t 0 := by
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_map]
  rw [mkF_coeff]
  rw [map_add, map_sum]
  simp [MvPolynomial.eval]

/-- Applying the same evaluation to an embedded `ℂ[Y]` polynomial gives it back. -/
lemma cEmb_map_eval_zero (p : Polynomial ℂ) :
    (cEmb K p).map (MvPolynomial.eval (fun _ : Fin K => (0 : ℂ))) = p := by
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_map]
  simp [cEmb, Polynomial.coeff_map]

/-- A `ℂ[Y]`-factor of `mkF` divides the constant member `t 0`. -/
lemma cEmb_dvd_zero (t : Fin (K + 1) → Polynomial ℂ) (G0 : Polynomial ℂ)
    (H : Polynomial (XR K)) (hF : mkF K t = cEmb K G0 * H) :
    G0 ∣ t 0 := by
  let ev0 : XR K →+* ℂ := MvPolynomial.eval (fun _ : Fin K => (0 : ℂ))
  have h1 : (mkF K t).map ev0 = t 0 := mkF_map_eval_zero t
  refine ⟨H.map ev0, ?_⟩
  calc
    t 0 = (mkF K t).map ev0 := by rw [h1]
    _ = (cEmb K G0).map ev0 * H.map ev0 := by rw [hF]; simp
    _ = G0 * H.map ev0 := by rw [cEmb_map_eval_zero]
    _ = G0 * H.map ev0 := rfl

/-- A `ℂ[Y]`-factor of `mkF` divides every `X_i`-member `t (i+1)`. -/
lemma cEmb_dvd_succ (t : Fin (K + 1) → Polynomial ℂ) (i : Fin K)
    (G0 : Polynomial ℂ) (H : Polynomial (XR K)) (hF : mkF K t = cEmb K G0 * H) :
    G0 ∣ t (Fin.succ i) := by
  classical
  let hL : Polynomial ℂ := ∑ k ∈ Finset.range (H.natDegree + 1), Polynomial.monomial k
    (MvPolynomial.coeff (Finsupp.single i 1) (H.coeff k))
  have hcoeffL : ∀ k : ℕ, (hL.coeff k) =
      MvPolynomial.coeff (Finsupp.single i 1) (H.coeff k) := by
    intro k
    by_cases hk : k ≤ H.natDegree
    · simp [hL, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single k]
      · simp
      · intro k' hk' hkk'
        rw [Polynomial.coeff_monomial, if_neg hkk']
      · intro hnk
        exact False.elim (hnk (Finset.mem_range.mpr (by omega)))
    · have hc : H.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [hL, hc, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_zero]
      intro k' hk'
      have hk'lt : k' < H.natDegree + 1 := Finset.mem_range.mp hk'
      rw [Polynomial.coeff_monomial, if_neg (by omega)]
  have coeff_X_C : ∀ (i' : Fin K) (m : Fin K →₀ ℕ) (c : ℂ),
      MvPolynomial.coeff m (MvPolynomial.X i' * MvPolynomial.C c) =
        if m = Finsupp.single i' 1 then c else 0 := by
    intro i' m c
    by_cases hm : m = Finsupp.single i' 1
    · rw [if_pos hm]
      rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_pos hm.symm]
      simp
    · rw [if_neg hm]
      rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X,
        if_neg (by intro h; exact hm h.symm)]
      simp
  have hmain : ∀ i' : Fin K, ∀ c : ℂ,
      MvPolynomial.coeff (Finsupp.single i 1) (MvPolynomial.X i' * MvPolynomial.C c) =
        if i' = i then c else 0 := by
    intro i' c
    rw [coeff_X_C i' (Finsupp.single i 1) c]
    by_cases h : Finsupp.single i 1 = Finsupp.single i' 1
    · have hii : i = i' := (Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)).mp h
      rw [if_pos h, if_pos hii.symm]
    · rw [if_neg h]
      have hni : i' ≠ i := by
        intro hii'
        apply h
        rw [hii']
      rw [if_neg hni]
  refine ⟨hL, ?_⟩
  apply Polynomial.ext
  intro j
  have hstep : MvPolynomial.coeff (Finsupp.single i 1) ((mkF K t).coeff j) = (t (Fin.succ i)).coeff j := by
    rw [mkF_coeff]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_sum]
    have hfirst : MvPolynomial.coeff (Finsupp.single i 1) (MvPolynomial.C ((t 0).coeff j)) = 0 := by
      rw [MvPolynomial.coeff_C, if_neg]
      intro hz
      have h1 : (1 : ℕ) = (0 : ℕ) := by
        have hh := congrArg (fun d : Fin K →₀ ℕ => d i) hz
        simpa using hh
      norm_num at h1
    simp [hfirst]
    rw [Finset.sum_eq_single i]
    · rw [hmain i ((t (Fin.succ i)).coeff j)]
      simp
    · intro i' hi' hne
      rw [hmain i' ((t (Fin.succ i')).coeff j), if_neg (by exact fun h => hne h)]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ i))
  calc
    (t (Fin.succ i)).coeff j
        = MvPolynomial.coeff (Finsupp.single i 1) ((mkF K t).coeff j) := hstep.symm
    _ = MvPolynomial.coeff (Finsupp.single i 1) ((cEmb K G0 * H).coeff j) := by rw [← hF]
    _ = (G0 * hL).coeff j := by
          rw [Polynomial.coeff_mul]
          rw [Polynomial.coeff_mul]
          rw [MvPolynomial.coeff_sum]
          apply Finset.sum_congr rfl
          intro x hx
          calc
            MvPolynomial.coeff (Finsupp.single i 1) ((cEmb K G0).coeff x.1 * H.coeff x.2)
                = MvPolynomial.coeff (Finsupp.single i 1) (MvPolynomial.C (G0.coeff x.1) * H.coeff x.2) := by
                    simp [cEmb, Polynomial.coeff_map]
            _ = G0.coeff x.1 * MvPolynomial.coeff (Finsupp.single i 1) (H.coeff x.2) := by
                    rw [MvPolynomial.coeff_C_mul]
            _ = G0.coeff x.1 * hL.coeff x.2 := by rw [hcoeffL x.2]

/-- Under the no-common-root hypothesis, `mkF K t` is irreducible in
`(ℂ[X_1,…,X_K])[Y]`. -/
lemma affine_irreducible (t : Fin (K + 1) → Polynomial ℂ)
    (hnc : ∀ z : ℂ, ¬ (∀ i : Fin (K + 1), (t i).eval z = 0))
    (hm : 1 ≤ (t 0).natDegree) (hdeg : ∀ i, (t i).natDegree ≤ (t 0).natDegree) :
    Irreducible (mkF K t) := by
  classical
  have hFnat : (mkF K t).natDegree = (t 0).natDegree :=
    mkF_natDegree t hdeg rfl (by omega)
  have hF0 : mkF K t ≠ 0 := by
    intro h
    rw [h] at hFnat
    simp at hFnat
    omega
  have hFnunit : ¬ IsUnit (mkF K t) := by
    intro hu
    rcases (Polynomial.isUnit_iff.mp hu) with ⟨r, hr, hrp⟩
    rw [← hrp] at hFnat
    simp at hFnat
    omega
  refine ⟨hFnunit, ?_⟩
  intro a b hab
  rcases affine_factor t a b hab hF0 with hGa | hHb
  · rcases hGa with ⟨G0, ha⟩
    have hdiv : mkF K t = cEmb K G0 * b := by rw [← ha]; exact hab
    have h0 : G0 ∣ t 0 := cEmb_dvd_zero t G0 b hdiv
    have hsucc : ∀ i : Fin K, G0 ∣ t (Fin.succ i) := fun i => cEmb_dvd_succ t i G0 b hdiv
    by_cases hG0 : 1 ≤ G0.natDegree
    · rcases common_root_of_dvd_family t G0 hG0 h0 hsucc with ⟨z, hz⟩
      exact False.elim (hnc z hz)
    · have hnat0 : G0.natDegree = 0 := by omega
      have hG0nz : G0 ≠ 0 := by
        intro hz
        apply hF0
        rw [hab, ha, hz]
        simp
      have hG0c : G0 = Polynomial.C (G0.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hnat0
      have hc0 : G0.coeff 0 ≠ 0 := by
        intro hc
        apply hG0nz
        rw [hG0c, hc, Polynomial.C_0]
      have huM : IsUnit (MvPolynomial.C (G0.coeff 0) : XR K) := by
        exact (Units.map (MvPolynomial.C (R := ℂ) (σ := Fin K) : ℂ →* XR K)
          (Units.mk0 (G0.coeff 0) hc0)).isUnit
      have hu1 : IsUnit (cEmb K (Polynomial.C (G0.coeff 0))) := by
        rw [show cEmb K (Polynomial.C (G0.coeff 0)) = Polynomial.C (MvPolynomial.C (G0.coeff 0)) by
          simp [cEmb]]
        exact Polynomial.isUnit_C.mpr huM
      left
      rw [ha, hG0c]
      exact hu1
  · rcases hHb with ⟨H0, hb⟩
    have hdiv : mkF K t = cEmb K H0 * a := by rw [← hb, mul_comm]; exact hab
    have h0 : H0 ∣ t 0 := cEmb_dvd_zero t H0 a hdiv
    have hsucc : ∀ i : Fin K, H0 ∣ t (Fin.succ i) := fun i => cEmb_dvd_succ t i H0 a hdiv
    by_cases hH0 : 1 ≤ H0.natDegree
    · rcases common_root_of_dvd_family t H0 hH0 h0 hsucc with ⟨z, hz⟩
      exact False.elim (hnc z hz)
    · have hnat0 : H0.natDegree = 0 := by omega
      have hH0nz : H0 ≠ 0 := by
        intro hz
        apply hF0
        rw [hab, hb, hz]
        simp
      have hH0c : H0 = Polynomial.C (H0.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hnat0
      have hc0 : H0.coeff 0 ≠ 0 := by
        intro hc
        apply hH0nz
        rw [hH0c, hc, Polynomial.C_0]
      have huM : IsUnit (MvPolynomial.C (H0.coeff 0) : XR K) := by
        exact (Units.map (MvPolynomial.C (R := ℂ) (σ := Fin K) : ℂ →* XR K)
          (Units.mk0 (H0.coeff 0) hc0)).isUnit
      have hu1 : IsUnit (cEmb K (Polynomial.C (H0.coeff 0))) := by
        rw [show cEmb K (Polynomial.C (H0.coeff 0)) = Polynomial.C (MvPolynomial.C (H0.coeff 0)) by
          simp [cEmb]]
        exact Polynomial.isUnit_C.mpr huM
      right
      rw [hb, hH0c]
      exact hu1

/-- An irreducible polynomial of positive degree is primitive. -/
lemma primitive_of_irreducible (F : Polynomial (XR K)) (hF : Irreducible F)
    (hdeg : 1 ≤ F.natDegree) : F.IsPrimitive := by
  exact hF.isPrimitive (by omega)

/-- Irreducible and primitive lifts to the fraction field. -/
lemma irreducible_map_fractionRing (F : Polynomial (XR K)) (hF : Irreducible F)
    (hp : F.IsPrimitive) :
    Irreducible (F.map (algebraMap (XR K) (FractionRing (XR K)))) := by
  classical
  let L := FractionRing (XR K)
  letI : Field L := IsFractionRing.toField (A := XR K) (K := L)
  exact (hp.irreducible_iff_irreducible_map_fraction_map (K := L)).mp hF

/-- If `F` is irreducible, primitive, and `derivative F` has smaller degree, then
the resultant of `F` and `derivative F` is nonzero. -/
lemma resultant_ne_zero_of_irreducible (F : Polynomial (XR K))
    (hF : Irreducible F) (hp : F.IsPrimitive) (hF0 : F ≠ 0)
    (hF'0 : derivative F ≠ 0) (hlt : (derivative F).natDegree < F.natDegree) :
    F.resultant (derivative F) ≠ 0 := by
  classical
  let L := FractionRing (XR K)
  letI : Field L := IsFractionRing.toField (A := XR K) (K := L)
  let φ : (XR K) →+* L := algebraMap (XR K) L
  let FL : Polynomial L := F.map φ
  let FL' : Polynomial L := (derivative F).map φ
  have hFLirr : Irreducible FL := by
    exact irreducible_map_fractionRing F hF hp
  have hFL0 : FL ≠ 0 := by
    dsimp [FL]
    intro h
    apply hF0
    exact (Polynomial.map_eq_zero_iff (IsFractionRing.injective (XR K) L)).mp h
  have hFL'd0 : FL' ≠ 0 := by
    dsimp [FL']
    intro h
    apply hF'0
    exact (Polynomial.map_eq_zero_iff (IsFractionRing.injective (XR K) L)).mp h
  have hndFL : FL.natDegree = F.natDegree := by
    dsimp [FL]
    exact Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective (XR K) L) F
  have hndFL' : FL'.natDegree = (derivative F).natDegree := by
    dsimp [FL']
    exact Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective (XR K) L) (derivative F)
  have hndvd : ¬ FL ∣ FL' := by
    intro h
    rcases h with ⟨W, hW⟩
    have hW0 : W ≠ 0 := by
      intro hw
      apply hFL'd0
      rw [hW, hw]
      simp
    have hndW : FL.natDegree + W.natDegree = FL'.natDegree := by
      rw [hW]
      exact (Polynomial.natDegree_mul hFL0 hW0).symm
    rw [hndFL, hndFL'] at hndW
    omega
  have hcop : IsCoprime FL FL' := by
    exact (hFLirr.coprime_iff_not_dvd).mpr hndvd
  have hres : FL.resultant FL' ≠ 0 := by
    exact Polynomial.resultant_ne_zero FL FL' hcop
  have hφD : φ (F.resultant (derivative F)) ≠ 0 := by
    change φ (Polynomial.resultant F (derivative F) F.natDegree (derivative F).natDegree) ≠ 0
    rw [← Polynomial.resultant_map_map (f := F) (g := derivative F) (m := F.natDegree)
      (n := (derivative F).natDegree) φ]
    have h1 : (F.map φ).natDegree = F.natDegree :=
      Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective (XR K) L) F
    have h2 : ((derivative F).map φ).natDegree = (derivative F).natDegree :=
      Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective (XR K) L) (derivative F)
    have hconv : (F.map φ).resultant ((derivative F).map φ) F.natDegree (derivative F).natDegree
        = FL.resultant FL' := by
      rw [h1, h2]
    rw [hconv]
    exact hres
  intro hD
  exact hφD (by rw [hD]; simp)

/-- The determinant of a matrix with entries of total degree `≤ 1` has total degree `≤ n`. -/
lemma det_totalDegree_le {K n : ℕ} (A : Matrix (Fin n) (Fin n) (XR K))
    (hA : ∀ i j, (A i j).totalDegree ≤ 1) : A.det.totalDegree ≤ n := by
  classical
  rw [Matrix.det_apply]
  refine MvPolynomial.totalDegree_finsetSum_le (s := Finset.univ) (d := n) ?_
  intro σ hσ
  have h : (Equiv.Perm.sign σ) • (∏ i, A (σ i) i) = ((Equiv.Perm.sign σ : ℤ) • (∏ i, A (σ i) i)) := rfl
  calc
    ((Equiv.Perm.sign σ) • (∏ i, A (σ i) i)).totalDegree
        ≤ (∏ i, A (σ i) i).totalDegree := by
          rw [h]
          rw [zsmul_eq_mul]
          refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
          have hz : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin K) ℂ) =
              MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : ℂ)) := by norm_num
          rw [hz, MvPolynomial.totalDegree_C]
          simp
    _ ≤ ∑ i : Fin n, (A (σ i) i).totalDegree := by
          exact MvPolynomial.totalDegree_finsetProd (s := Finset.univ) (f := fun i => A (σ i) i)
    _ ≤ n := by
          calc
            (∑ i : Fin n, (A (σ i) i).totalDegree) ≤ ∑ i : Fin n, (1 : ℕ) := by
              exact Finset.sum_le_sum (fun i hi => hA (σ i) i)
            _ = n := by simp

/-- Entries of the Sylvester matrix have total degree `≤ 1` when the coefficients do. -/
lemma sylvester_totalDegree_le_one (f g : Polynomial (XR K)) (m n : ℕ)
    (hf : ∀ j : ℕ, (f.coeff j).totalDegree ≤ 1)
    (hg : ∀ j : ℕ, (g.coeff j).totalDegree ≤ 1)
    (i j : Fin (m + n)) :
    (Polynomial.sylvester f g m n i j).totalDegree ≤ 1 := by
  classical
  induction j using Fin.addCases with
  | left j1 =>
    simp [Polynomial.sylvester, Matrix.of_apply]
    by_cases hij : (i : ℕ) ∈ Set.Icc (j1 : ℕ) (j1 + n)
    · have hc : (j1 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j1 : ℕ) + n := by simpa [Set.mem_Icc] using hij
      rw [if_pos hc]
      exact hg (↑i - ↑j1)
    · have hc : ¬ ((j1 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j1 : ℕ) + n) := by simpa [Set.mem_Icc] using hij
      rw [if_neg hc]
      simp
  | right j1 =>
    simp [Polynomial.sylvester, Matrix.of_apply]
    by_cases hij : (i : ℕ) ∈ Set.Icc (j1 : ℕ) (j1 + m)
    · have hc : (j1 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j1 : ℕ) + m := by simpa [Set.mem_Icc] using hij
      rw [if_pos hc]
      exact hf (↑i - ↑j1)
    · have hc : ¬ ((j1 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j1 : ℕ) + m) := by simpa [Set.mem_Icc] using hij
      rw [if_neg hc]
      simp

/-- Derivative coefficients have total degree `≤ 1` when the coefficients do. -/
lemma derivative_coeff_totalDegree_le_one (P : Polynomial (XR K))
    (hP : ∀ j : ℕ, (P.coeff j).totalDegree ≤ 1) (j : ℕ) :
    ((derivative P).coeff j).totalDegree ≤ 1 := by
  rw [Polynomial.coeff_derivative]
  calc
    ((P.coeff (j + 1)) * (j + 1 : XR K)).totalDegree
        ≤ (P.coeff (j + 1)).totalDegree + ((j + 1 : XR K)).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 := by
      have hz : (j + 1 : XR K) = MvPolynomial.C (j + 1 : ℂ) := by norm_num
      rw [hz, MvPolynomial.totalDegree_C]
      simp [hP (j + 1)]

/-- The resultant of two polynomials with affine-in-`X` coefficients has
`X`-total-degree bounded by the sum of the degrees. -/
lemma resultant_totalDegree_le (f g : Polynomial (XR K))
    (hf : ∀ j : ℕ, (f.coeff j).totalDegree ≤ 1)
    (hg : ∀ j : ℕ, (g.coeff j).totalDegree ≤ 1) :
    (f.resultant g).totalDegree ≤ f.natDegree + g.natDegree := by
  have hd : (Polynomial.sylvester f g f.natDegree g.natDegree).det.totalDegree
      ≤ f.natDegree + g.natDegree := by
    exact det_totalDegree_le (Polynomial.sylvester f g f.natDegree g.natDegree)
      (by intro i j; exact sylvester_totalDegree_le_one f g f.natDegree g.natDegree hf hg i j)
  simpa [Polynomial.resultant] using hd


end GradedPoly

/-- Core of `lem:squarefree_nocommon`, lead at index 0. -/
theorem nocommon_core {m K : ℕ} (hK : 1 ≤ K) (S : Fin (K + 1) → Polynomial ℤ)
    (hnz0 : S 0 ≠ 0) (hdeg : ∀ i, (S i).natDegree ≤ m) (hlead : (S 0).natDegree = m)
    (hnc : ∀ z : ℂ, ¬ (∀ i : Fin (K + 1), Polynomial.aeval z (S i) = 0)) :
    ∃ b : Fin K → ℕ, (∀ i, b i ≤ 2 * m) ∧
      DistinctRootData
        (S 0 + ∑ i : Fin K, Polynomial.C (((b i : ℕ) : ℤ)) * S (Fin.succ i)) m := by
  by_cases hm : m = 0
  · -- the constant case: choose all coefficients zero
    refine ⟨(fun _ : Fin K => 0), ?_, ?_⟩
    · intro i
      rw [hm]
    · dsimp [DistinctRootData]
      rw [hm]
      have hA : S 0 + ∑ i : Fin K, Polynomial.C (0 : ℤ) * S (Fin.succ i) = S 0 := by
        simp
      rw [hA]
      constructor
      · exact hlead.trans hm
      · have hnat : (S 0).natDegree = 0 := hlead.trans hm
        have hS0c : S 0 = Polynomial.C ((S 0).coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hnat
        have hc0 : (S 0).coeff 0 ≠ 0 := by
          intro hc
          apply hnz0
          rw [hS0c, hc, Polynomial.C_0]
        rw [hS0c, Polynomial.map_C]
        rw [Polynomial.separable_C]
        exact isUnit_iff_ne_zero.mpr (by
          change ((S 0).coeff 0 : ℂ) ≠ 0
          exact_mod_cast hc0)


  · -- m ≥ 1: use the generic resultant machinery and the cube lemma
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let s : Fin (K + 1) → Polynomial ℂ := fun i => (S i).map (algebraMap ℤ ℂ)
    have hsdeg : ∀ i, (s i).natDegree ≤ m := by
      intro i
      dsimp [s]
      rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective (S i)]
      exact hdeg i
    have hslead : (s 0).natDegree = m := by
      dsimp [s]
      rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective (S 0)]
      exact hlead
    have hnc_s : ∀ z : ℂ, ¬ (∀ i : Fin (K + 1), (s i).eval z = 0) := by
      intro z hz
      exact hnc z (fun i => by
        have h := hz i
        rw [← map_eval_eq_aeval (S i) z]
        exact h)
    have hm' : 1 ≤ (s 0).natDegree := by
      rw [hslead]
      omega
    have hsdeg' : ∀ i, (s i).natDegree ≤ (s 0).natDegree := fun i =>
      le_trans (hsdeg i) (le_of_eq hslead.symm)
    let F : Polynomial (XR K) := mkF K s
    let Fd : Polynomial (XR K) := derivative F
    have hFnat : F.natDegree = m := by
      dsimp [F]
      exact mkF_natDegree s hsdeg hslead hm
    have hFnat_ne0 : F.natDegree ≠ 0 := by
      rw [hFnat]
      exact hm
    have hF0 : F ≠ 0 := by
      intro h
      rw [h] at hFnat
      simp at hFnat
      omega
    have hlc0 : F.coeff m ≠ 0 := by
      dsimp [F]
      exact mkF_coeff_ne_zero_of_lead s hslead hm
    have hFcoeff_gt : ∀ j : ℕ, m < j → F.coeff j = 0 := by
      intro j hj
      dsimp [F]
      exact mkF_coeff_eq_zero_of_lt s hsdeg hj
    have hFd0 : Fd ≠ 0 := by
      intro h
      exact hFnat_ne0 (Polynomial.derivative_eq_zero.mp h)
    have hFd_deg : Fd.natDegree = m - 1 := by
      dsimp [Fd]
      rw [Polynomial.natDegree_derivative F, hFnat]
    have hFirr : Irreducible F := by
      dsimp [F]
      exact affine_irreducible s hnc_s hm' hsdeg'
    have hFprim : F.IsPrimitive := primitive_of_irreducible F hFirr (by rw [hFnat]; omega)
    let D : XR K := Polynomial.resultant F Fd m (m - 1)
    have hD0default : F.resultant Fd ≠ 0 :=
      resultant_ne_zero_of_irreducible F hFirr hFprim hF0 hFd0 (by
        rw [hFnat, hFd_deg]
        omega)
    have hD0 : D ≠ 0 := by
      dsimp [D]
      simpa [hFnat, hFd_deg] using hD0default
    let lc : XR K := F.coeff m
    have hlc1 : lc.totalDegree ≤ 1 := by
      dsimp [lc, F]
      exact mkF_coeff_totalDegree_le_one s m
    have hDdefeq : D = F.resultant Fd := by
      dsimp [D]
      rw [hFnat, hFd_deg]
    have hDdeg : D.totalDegree ≤ 2 * m - 1 := by
      rw [hDdefeq]
      have hb' : (F.resultant Fd).totalDegree ≤ F.natDegree + Fd.natDegree :=
        resultant_totalDegree_le F Fd (fun j => by
          dsimp [F]
          exact mkF_coeff_totalDegree_le_one s j)
          (fun j => derivative_coeff_totalDegree_le_one F (fun j => by
            dsimp [F]
            exact mkF_coeff_totalDegree_le_one s j) j)
      calc
        (F.resultant Fd).totalDegree ≤ F.natDegree + Fd.natDegree := hb'
        _ = m + (m - 1) := by rw [hFnat, hFd_deg]
        _ = 2 * m - 1 := by omega
    let E : XR K := lc * D
    have hE0 : E ≠ 0 := by
      dsimp [E]
      exact mul_ne_zero (by dsimp [lc]; exact hlc0) hD0
    have hEdeg : E.totalDegree ≤ 2 * m := by
      dsimp [E]
      calc
        (lc * D).totalDegree ≤ lc.totalDegree + D.totalDegree := MvPolynomial.totalDegree_mul _ _
        _ ≤ 1 + (2 * m - 1) := by
          exact add_le_add hlc1 hDdeg
        _ ≤ 2 * m := by omega
    rcases Submission.CubeLemma.cube_value (r := K) (d := 2 * m) E hE0 hEdeg with ⟨v, hvle, hEv⟩
    let ψ : XR K →+* ℂ := MvPolynomial.eval (fun i : Fin K => (v i : ℂ))
    have hψlc : ψ lc ≠ 0 := by
      intro hz
      apply hEv
      dsimp [E, ψ]
      rw [map_mul, hz]
      simp
    have hψD : ψ D ≠ 0 := by
      intro hz
      apply hEv
      dsimp [E, ψ]
      rw [map_mul, hz]
      simp
    let A : Polynomial ℤ := S 0 + ∑ i : Fin K,
        Polynomial.C (((v i : ℕ) : ℤ)) * S (Fin.succ i)
    let A0 : Polynomial ℂ := A.map (algebraMap ℤ ℂ)
    have hA0map : A0 = F.map ψ := by
      dsimp [A0, A, F, ψ, s]
      rw [mkF_map_eval]
      rw [Polynomial.map_add, Polynomial.map_sum]
      simp [Polynomial.map_mul, Polynomial.map_C]
    have hderF : derivative (F.map ψ) = Fd.map ψ := by
      dsimp [Fd]
      rw [Polynomial.derivative_map]
    have hderA0 : derivative A0 = Fd.map ψ := by
      rw [hA0map]
      exact hderF
    have hA0nat : A0.natDegree = m := by
      apply le_antisymm
      · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rw [hA0map, Polynomial.coeff_map]
        have : F.coeff N = 0 := hFcoeff_gt N (by omega)
        simp [this]
      · by_contra hlt
        have hlt' : A0.natDegree < m := by omega
        have hz : A0.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt'
        have hc : A0.coeff m ≠ 0 := by
          rw [hA0map, Polynomial.coeff_map]
          dsimp [lc] at hψlc
          exact hψlc
        exact hc hz
    have hA0nz : A0 ≠ 0 := by
      intro h
      rw [h] at hA0nat
      simp at hA0nat
      omega
    have hA0d_nat : (derivative A0).natDegree = m - 1 := by
      rw [Polynomial.natDegree_derivative A0, hA0nat]
    have hA0d0 : derivative A0 ≠ 0 := by
      intro h
      have : A0.natDegree = 0 := Polynomial.derivative_eq_zero.mp h
      rw [hA0nat] at this
      omega
    have hψres : A0.resultant (derivative A0) = ψ D := by
      have hmap : (F.map ψ).resultant (Fd.map ψ) m (m - 1) = ψ D := by
        dsimp [D]
        exact (Polynomial.resultant_map_map (f := F) (g := Fd) (m := m) (n := m - 1) ψ)
      calc
        A0.resultant (derivative A0) = (F.map ψ).resultant (Fd.map ψ) m (m - 1) := by
          rw [hA0map, hderF]
          have h1 : (F.map ψ).natDegree = m := by rw [← hA0map]; exact hA0nat
          have h2 : (Fd.map ψ).natDegree = m - 1 := by rw [← hderA0]; exact hA0d_nat
          simp [h1, h2]
        _ = ψ D := hmap
    have hresA0 : A0.resultant (derivative A0) ≠ 0 := by
      rw [hψres]
      exact hψD
    have hA0sep : A0.Separable := by
      rw [Polynomial.separable_def]
      by_contra hncop
      exact hresA0 (Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hA0nz, hncop⟩)
    have hAnat : A.natDegree = m := by
      have hmap : A.natDegree = A0.natDegree := by
        dsimp [A0]
        exact (Polynomial.natDegree_map_eq_of_injective Int.cast_injective A).symm
      rw [hmap]
      exact hA0nat
    refine ⟨v, ?_, ?_⟩
    · intro i
      exact hvle i
    · change DistinctRootData A m
      exact ⟨hAnat, hA0sep⟩
end Submission.NocommonCore
