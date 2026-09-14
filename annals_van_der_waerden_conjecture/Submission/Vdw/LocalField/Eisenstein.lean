import Mathlib
import Submission.Vdw.LocalField.OWEmbed
import Submission.Vdw.LocalField.WildDifferent
import Submission.Vdw.LocalField.KpVal

open Classical
open IsLocalRing
open scoped NumberField WithZero Valued

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# WildDifferent sub-stone (d) COMPLETE: f_ϖ is Eisenstein over 𝒪_W

Setup as in OWEmbed/WildDifferent: `W = Wk p P α = ℚ_p(ζ)` the
Teichmüller subfield of `K_P = kpAdic p P`, `ϖ := uniformizer p P` a
uniformizer of `kpInt p P`, `e := P.ramificationIdx ℤ`,
`f_ϖ := minpoly (Wk p P α) ϖval` (monic, degree `e` — (c)(iii) closed in
OWEmbed — coefficients in `𝒪_W = OW_subring` — (c)(ii)),
`𝔪_W = OW_ker` the maximal ideal of `𝒪_W` (`e(W) = 1`: `𝔪_W = (p)`).

THEOREMS — the Eisenstein property of `f_ϖ` over `𝒪_W` (sub-stone (d)):

**(d) part 1 (Eisenstein coefficient congruence)**:
`fϖWk_coeff_mem_ker` — for every `i < e`, the coefficient
`(fϖWk p P α).coeff i` lies in `𝔪_W = OW_ker p P α`.  (The reduction of
`f_ϖ` modulo `𝔪_W` is `X^e`.)

**(d) part 2 (constant term is a uniformizer of 𝒪_W)**:
`fϖWk_constTerm_witness_exact` — the `kpInt` witness of the constant
coefficient has EXACT filtration degree `e` (`z₀ ∈ 𝔪^e \ 𝔪^{e+1}`), and
`fϖWk_constTerm_not_mem_ker_sq` — `c₀ ∉ 𝔪_W²`.  (Proof: the annihilating
identity `z₀ + ϖ^e + Σ_{1≤j<e} z_j·ϖ^j = 0` with every tail term in
`𝔪^{e+1}` forces `ϖ^e = -z₀ - (tail)`, so `z₀ ∈ 𝔪^{e+1}` would put `ϖ^e`
in `𝔪^{e+1}`, contradicting `ϖ^e ∉ 𝔪^{e+1}`; the `𝔪_W²`-form follows by
pushing `𝔪_W²` through `owToKpInt` into `𝔪^{2e} ⊆ 𝔪^{e+1}` via the
principal-ideal chain `𝔪_W = (pOW)`, `(p)·kpInt = 𝔪^e`.)

PROOF (no-cancellation at the uniformizer filtration).  Let
`z_i := owToKpInt c_i ∈ kpInt` be the integral witness of `c_i` (the
`kpInt` representative of the value of the coefficient).  Since
`f_ϖ(ϖval) = 0` in `K_P` and `(c_i : K_P) = (z_i : K_P)`, the kpInt-level
identity `∑_{i ≤ e} z_i·ϖ^i = 0` holds (`z_e = 1`).  Suppose some
`i₀ < e` has `z_{i₀} ∉ 𝔪` (a unit of the local ring `kpInt`).  Take the
least such `i₀`; then:

* the `i₀`-term `z_{i₀}·ϖ^{i₀}` has exact filtration degree `i₀`
  (unit coefficient, `unit_mul_uniformizer_pow_not_mem_succ`);
* for `i < i₀`: `z_i ∈ 𝔪` (minimality) ⟹ `c_i ∈ 𝔪_W` (the kernel
  description `resOW_hom c_i = mk (owToKpInt c_i)`) ⟹ `z_i ∈ 𝔪^e`
  (`𝔪_W·kpInt = 𝔪^e`, `OW_ker_map_eq_mS_pow_ramIdx`), so the term lies in
  `𝔪^{e+i} ⊆ 𝔪^{i₀+1}` (`mem_mul_pow_pow_kpInt`);
* for `i₀ < i ≤ e`: `ϖ^i ∈ 𝔪^i ⊆ 𝔪^{i₀+1}`, so the term lies in
  `𝔪^{i₀+1}`.

`sum_not_mem_pow_of_others_small` then forces
`∑_{i ≤ e} z_i·ϖ^i ∉ 𝔪^{i₀+1}`, contradicting the identity (= 0).  Hence
no such `i₀` exists and every `i < e` has `z_i ∈ 𝔪`, i.e. `c_i ∈ 𝔪_W`.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- Product of ideal-power members of the principal uniformizer filtration:
for `a ∈ 𝔪^m`, `b ∈ 𝔪^n` (𝔪 := maximal ideal of `kpInt`, 𝔪^k = (ϖ^k)),
`a·b ∈ 𝔪^{m+n}`. -/
lemma mem_mul_pow_pow_kpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (a b : kpInt p P) (m n : ℕ)
    (ha : a ∈ (maximalIdeal (kpInt p P)) ^ m)
    (hb : b ∈ (maximalIdeal (kpInt p P)) ^ n) :
    a * b ∈ (maximalIdeal (kpInt p P)) ^ (m + n) := by
  classical
  rw [maximalIdeal_pow_eq_span p P m] at ha
  rw [Ideal.mem_span_singleton] at ha
  rcases ha with ⟨d, hd⟩
  rw [maximalIdeal_pow_eq_span p P n] at hb
  rw [Ideal.mem_span_singleton] at hb
  rcases hb with ⟨e, he⟩
  rw [maximalIdeal_pow_eq_span p P (m + n)]
  rw [Ideal.mem_span_singleton]
  refine ⟨d * e, ?_⟩
  rw [hd, he]
  rw [pow_add]
  ring

/-- **(d) part 1**: the non-leading coefficients of
`f_ϖ = minpoly (Wk p P α) ϖval` lie in the maximal ideal `𝔪_W = OW_ker`
of `𝒪_W` (the Eisenstein congruence: `f_ϖ ≡ X^e (mod 𝔪_W)`). -/
theorem fϖWk_coeff_mem_ker (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    ∀ i : ℕ, i < P.ramificationIdx ℤ →
      (⟨(fϖWk p P α).coeff i, fϖWk_coeff_mem_OW p P α i⟩ : OW_subring p P α) ∈ OW_ker p P α := by
  classical
  intro i hi
  let e : ℕ := P.ramificationIdx ℤ
  let g : Polynomial (Wk p P α) := fϖWk p P α
  let mS : Ideal (kpInt p P) := maximalIdeal (kpInt p P)
  let ϖ : kpInt p P := uniformizer p P
  let z : ℕ → kpInt p P := fun j => owToKpInt p P α ⟨g.coeff j, fϖWk_coeff_mem_OW p P α j⟩
  have hnat : g.natDegree = e := by
    simpa [g, e] using (fϖWk_natDegree_eq_ramIdx p P hα hgen)
  -- the kpInt-level annihilating sum over i ≤ e (from f_ϖ(ϖval) = 0):
  have hzero : (∑ j ∈ Finset.range (e + 1), z j * ϖ ^ j) = 0 := by
    have hae0 : (Polynomial.aeval (ϖ : kpAdic p P)) g = 0 := by
      simpa [g, ϖ] using (fϖWk_aeval p P α)
    have h1 := Polynomial.aeval_eq_sum_range (p := g) (x := (ϖ : kpAdic p P))
    have hg0 : (∑ j ∈ Finset.range (g.natDegree + 1),
        g.coeff j • ((ϖ : kpAdic p P) ^ j)) = 0 := by
      simpa [h1] using hae0
    rw [hnat] at hg0
    -- convert the kpAdic-level sum (smul form) to the kpInt-level sum z·ϖ^j
    have hval : ((∑ j ∈ Finset.range (e + 1), (z j * ϖ ^ j : kpInt p P)) : kpAdic p P) = 0 := by
      calc
        ((∑ j ∈ Finset.range (e + 1), (z j * ϖ ^ j : kpInt p P)) : kpAdic p P)
            = ∑ j ∈ Finset.range (e + 1), ((z j * ϖ ^ j : kpInt p P) : kpAdic p P) := by simp
        _ = ∑ j ∈ Finset.range (e + 1),
              (g.coeff j : kpAdic p P) * ((ϖ : kpAdic p P) ^ j) := by
              apply Finset.sum_congr rfl
              intro j hj
              calc
                ((z j * ϖ ^ j : kpInt p P) : kpAdic p P)
                    = ((z j : kpInt p P) : kpAdic p P) * ((ϖ ^ j : kpInt p P) : kpAdic p P) := rfl
                _ = (g.coeff j : kpAdic p P) * ((ϖ ^ j : kpInt p P) : kpAdic p P) := by
                      dsimp [z]
                      rw [owToKpInt_value p P α ⟨g.coeff j, fϖWk_coeff_mem_OW p P α j⟩]
                _ = (g.coeff j : kpAdic p P) * ((ϖ : kpAdic p P) ^ j) := rfl
        _ = 0 := by
              convert hg0 using 1
              apply Finset.sum_congr rfl
              intro j hj
              rw [Algebra.smul_def]
              rfl
    -- injectivity of kpInt → kpAdic:
    have hinj : Function.Injective (fun x : kpInt p P => (x : kpAdic p P)) := by
      intro a b hab
      exact Subtype.ext hab
    exact hinj (by simpa using hval)
  -- membership z ∈ 𝔪 ⟺ c ∈ 𝔪_W:
  have hzker : ∀ j : ℕ, z j ∈ mS ↔
      (⟨g.coeff j, fϖWk_coeff_mem_OW p P α j⟩ : OW_subring p P α) ∈ OW_ker p P α := by
    intro j
    rw [RingHom.mem_ker]
    rw [show (resOW_hom p P α) ⟨g.coeff j, fϖWk_coeff_mem_OW p P α j⟩ =
        Ideal.Quotient.mk (maximalIdeal (kpInt p P)) (z j) by
          dsimp [z]
          exact resOW_hom_eq_mk_owToKpInt p P α ⟨g.coeff j, fϖWk_coeff_mem_OW p P α j⟩]
    exact (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal (kpInt p P)) (a := z j)).symm
  -- membership c ∈ 𝔪_W ⟹ z ∈ 𝔪^e (via the ideal map 𝔪_W·kpInt = 𝔪^e):
  have hz_e : ∀ j : ℕ, z j ∈ mS → z j ∈ mS ^ e := by
    intro j hzj
    have hcj : (⟨g.coeff j, fϖWk_coeff_mem_OW p P α j⟩ : OW_subring p P α) ∈ OW_ker p P α :=
      (hzker j).1 hzj
    have hm : z j ∈ (OW_ker p P α).map (owToKpInt p P α) := by
      change z j ∈ Ideal.span ((fun w : OW_subring p P α => owToKpInt p P α w) ''
        (OW_ker p P α : Set (OW_subring p P α)))
      exact Ideal.subset_span ⟨(⟨g.coeff j, fϖWk_coeff_mem_OW p P α j⟩ : OW_subring p P α), hcj, rfl⟩
    rwa [OW_ker_map_eq_mS_pow_ramIdx p P hα hgen] at hm
  -- aux: no-cancellation at the least index
  have haux : ∀ j₀ : ℕ, j₀ < e → (∀ t < j₀, z t ∈ mS) → z j₀ ∈ mS := by
    intro j₀ hj₀ hsmall0
    by_contra hbad
    have hzunit : IsUnit (z j₀) := by
      rw [IsLocalRing.mem_maximalIdeal] at hbad
      change z j₀ ∈ {x : kpInt p P | ¬ IsUnit x} → False at hbad
      exact not_not.mp (by simpa using hbad)
    rcases hzunit with ⟨u, hu⟩
    have hbig : z j₀ * ϖ ^ j₀ ∉ mS ^ (j₀ + 1) := by
      have hnm := unit_mul_uniformizer_pow_not_mem_succ p P u j₀
      simpa [hu, mS, ϖ] using hnm
    have hsmall : ∀ j ∈ Finset.range (e + 1), j ≠ j₀ → z j * ϖ ^ j ∈ mS ^ (j₀ + 1) := by
      intro j hj hne
      have hjr : j < e + 1 := Finset.mem_range.mp hj
      by_cases hjl : j < j₀
      · -- j < j₀: z j ∈ 𝔪^e and ϖ^j ∈ 𝔪^j ⟹ product ∈ 𝔪^{e+j} ⊆ 𝔪^{j₀+1}
        have hzj : z j ∈ mS := hsmall0 j hjl
        have hzje : z j ∈ mS ^ e := hz_e j hzj
        have hpow : ϖ ^ j ∈ mS ^ j := by
          simpa [mS, ϖ] using (uniformizer_pow_mem_maximalIdeal_pow p P j)
        have hprod : z j * ϖ ^ j ∈ mS ^ (e + j) := by
          simpa [mS] using (mem_mul_pow_pow_kpInt p P (z j) (ϖ ^ j) e j (by simpa [mS] using hzje) (by simpa [mS] using hpow))
        have hle : j₀ + 1 ≤ e + j := by omega
        exact (Ideal.pow_le_pow_right hle) hprod
      · -- j₀ < j ≤ e: ϖ^j ∈ 𝔪^j ⊆ 𝔪^{j₀+1}
        have hjg : j₀ < j := lt_of_le_of_ne (Nat.le_of_not_gt hjl) (Ne.symm hne)
        have hjj : j₀ + 1 ≤ j := Nat.succ_le_of_lt hjg
        have hpow : ϖ ^ j ∈ mS ^ j := by
          simpa [mS, ϖ] using (uniformizer_pow_mem_maximalIdeal_pow p P j)
        have hprod : z j * ϖ ^ j ∈ mS ^ j := by
          have hz0 : z j ∈ mS ^ 0 := by simp [mS]
          simpa [mS] using (mem_mul_pow_pow_kpInt p P (z j) (ϖ ^ j) 0 j (by simp) (by simpa [mS] using hpow))
        exact (Ideal.pow_le_pow_right hjj) hprod
    have hsum_ne : (∑ j ∈ Finset.range (e + 1), z j * ϖ ^ j) ∉ mS ^ (j₀ + 1) :=
      sum_not_mem_pow_of_others_small mS (Finset.range (e + 1)) (fun j => z j * ϖ ^ j)
        (by exact Finset.mem_range.mpr (Nat.lt_succ_of_lt hj₀)) j₀ hbig hsmall
    have hzmem : (0 : kpInt p P) ∈ mS ^ (j₀ + 1) := by simp [mS]
    exact hsum_ne (by simp [hzero])
  -- strong induction: all i < e have z i ∈ 𝔪
  have hz_all : ∀ j : ℕ, j < e → z j ∈ mS := by
    intro j
    refine Nat.strong_induction_on j ?_
    intro j ih hj
    exact haux j hj (fun t ht => (ih t ht) (Nat.lt_trans ht hj))
  have hzi : z i ∈ mS := hz_all i (by simpa [e] using hi)
  -- conclude: c_i ∈ 𝔪_W
  simpa [g] using (hzker i).1 hzi

/-! ## (d) part 2: the constant term of f_ϖ is a uniformizer of 𝒪_W

With (d) part 1 (`fϖWk_coeff_mem_ker`: every coefficient of degree `< e`
lies in `𝔪_W = OW_ker`, i.e. its `kpInt` witness lies in `𝔪^e`), the
annihilating identity `∑_{j ≤ e} z_j·ϖ^j = 0` (`fϖWk_z_sum_annihilate`,
from `fϖWk_aeval`), the kernel description
`z ∈ 𝔪 ↔ c ∈ 𝔪_W` (`fϖWk_z_mem_ker_iff`) and the push-forward
`c ∈ 𝔪_W ⟹ z ∈ 𝔪^e` (`fϖWk_z_mem_pow_of_mem_ker`) are factored as
reusable top-level lemmas (the (c)-chapter's structural facts at the
`kpInt` level).

THEOREM **(d) part 2** `fϖWk_constTerm_witness_exact` — for (hα)(hgen),
the witness `z₀` of the constant coefficient `c₀ := (fϖWk p P α).coeff 0`
has EXACT filtration degree `e := P.ramificationIdx ℤ`:
`z₀ ∈ 𝔪^e` (part 1) and `z₀ ∉ 𝔪^{e+1}`.  Proof of the second conjunct:
the identity `z₀ + ϖ^e + Σ_{1 ≤ j < e} z_j·ϖ^j = 0` (split the range of
`fϖWk_z_sum_annihilate` at `j = 0` and `j = e`, using `z_e = 1`, i.e.
`g` monic of degree `e`); the tail `Σ_{1 ≤ j < e} z_j·ϖ^j` lies in
`𝔪^{e+1}` (each `z_j ∈ 𝔪^e` by part 1, `ϖ^j ∈ 𝔪^j`, so the term is in
`𝔪^{e+j} ⊆ 𝔪^{e+1}` via `mem_mul_pow_pow_kpInt` and
`sum_mem_pow_of_all`).  If `z₀ ∈ 𝔪^{e+1}`, then `ϖ^e = −z₀ − (tail) ∈
𝔪^{e+1}`, contradicting the exactness `ϖ^e ∉ 𝔪^{e+1}`
(`uniformizer_pow_not_mem_maximalIdeal_succ`).  This is the Eisenstein
"constant term is a uniformizer of 𝒪_W" claim at the level of the
`kpInt` witnesses (sub-stone (d) COMPLETE with part 1).
-/

/-- The `kpInt` witness of the coefficient `(fϖWk p P α).coeff j` (the
integral representative in `kpInt` of the value of the `𝒪_W`-coefficient). -/
noncomputable def fϖWk_z (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (j : ℕ) : kpInt p P :=
  owToKpInt p P α ⟨(fϖWk p P α).coeff j, fϖWk_coeff_mem_OW p P α j⟩

/-- The kpInt-level annihilating identity for `f_ϖ`:
`∑_{j ≤ e} z_j·ϖ^j = 0` in `kpInt` (from `f_ϖ(ϖval) = 0` in `K_P` and the
injectivity of `kpInt → kpAdic`). -/
lemma fϖWk_z_sum_annihilate (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    (∑ j ∈ Finset.range (P.ramificationIdx ℤ + 1), fϖWk_z p P α j * uniformizer p P ^ j) = 0 := by
  classical
  let e : ℕ := P.ramificationIdx ℤ
  let g : Polynomial (Wk p P α) := fϖWk p P α
  let ϖ : kpInt p P := uniformizer p P
  have hnat : g.natDegree = e := by
    simpa [g, e] using (fϖWk_natDegree_eq_ramIdx p P hα hgen)
  have hae0 : (Polynomial.aeval (ϖ : kpAdic p P)) g = 0 := by
    simpa [g, ϖ] using (fϖWk_aeval p P α)
  have h1 := Polynomial.aeval_eq_sum_range (p := g) (x := (ϖ : kpAdic p P))
  have hg0 : (∑ j ∈ Finset.range (g.natDegree + 1),
      g.coeff j • ((ϖ : kpAdic p P) ^ j)) = 0 := by
    simpa [h1] using hae0
  rw [hnat] at hg0
  have hval : ((∑ j ∈ Finset.range (e + 1),
      (fϖWk_z p P α j * ϖ ^ j : kpInt p P)) : kpAdic p P) = 0 := by
    calc
      ((∑ j ∈ Finset.range (e + 1), (fϖWk_z p P α j * ϖ ^ j : kpInt p P)) : kpAdic p P)
          = ∑ j ∈ Finset.range (e + 1), ((fϖWk_z p P α j * ϖ ^ j : kpInt p P) : kpAdic p P) := by simp
      _ = ∑ j ∈ Finset.range (e + 1),
            (g.coeff j : kpAdic p P) * ((ϖ : kpAdic p P) ^ j) := by
            apply Finset.sum_congr rfl
            intro j hj
            calc
              ((fϖWk_z p P α j * ϖ ^ j : kpInt p P) : kpAdic p P)
                  = ((fϖWk_z p P α j : kpInt p P) : kpAdic p P) * ((ϖ ^ j : kpInt p P) : kpAdic p P) := rfl
              _ = (g.coeff j : kpAdic p P) * ((ϖ ^ j : kpInt p P) : kpAdic p P) := by
                    dsimp [fϖWk_z, g]
                    rw [owToKpInt_value p P α ⟨(fϖWk p P α).coeff j, fϖWk_coeff_mem_OW p P α j⟩]
              _ = (g.coeff j : kpAdic p P) * ((ϖ : kpAdic p P) ^ j) := rfl
      _ = 0 := by
            convert hg0 using 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [Algebra.smul_def]
            rfl
  have hinj : Function.Injective (fun x : kpInt p P => (x : kpAdic p P)) := by
    intro a b hab
    exact Subtype.ext hab
  -- goal is the kpInt sum = 0 (e is a let; defeq to the ramIdx statement)
  exact hinj (by simpa [fϖWk_z, e, ϖ] using hval)

/-- Kernel description at the witness level: for every `j`,
`z_j ∈ 𝔪 ↔ c_j ∈ 𝔪_W` (`resOW_hom c_j = mk (owToKpInt c_j)`, kernel of the
reduction). -/
lemma fϖWk_z_mem_ker_iff (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (j : ℕ) :
    fϖWk_z p P α j ∈ maximalIdeal (kpInt p P) ↔
      (⟨(fϖWk p P α).coeff j, fϖWk_coeff_mem_OW p P α j⟩ : OW_subring p P α) ∈ OW_ker p P α := by
  classical
  rw [RingHom.mem_ker]
  rw [show (resOW_hom p P α) ⟨(fϖWk p P α).coeff j, fϖWk_coeff_mem_OW p P α j⟩ =
      Ideal.Quotient.mk (maximalIdeal (kpInt p P)) (fϖWk_z p P α j) by
        dsimp [fϖWk_z]
        exact resOW_hom_eq_mk_owToKpInt p P α ⟨(fϖWk p P α).coeff j, fϖWk_coeff_mem_OW p P α j⟩]
  exact (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal (kpInt p P)) (a := fϖWk_z p P α j)).symm

/-- The maximal ideal of 𝒪_W pushes forward into `𝔪^e`:
`c_j ∈ 𝔪_W ⟹ z_j ∈ 𝔪^e` (𝔪_W·kpInt = 𝔪^e,
`OW_ker_map_eq_mS_pow_ramIdx`). -/
lemma fϖWk_z_mem_pow_of_mem_ker (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (j : ℕ) :
    (⟨(fϖWk p P α).coeff j, fϖWk_coeff_mem_OW p P α j⟩ : OW_subring p P α) ∈ OW_ker p P α →
      fϖWk_z p P α j ∈ (maximalIdeal (kpInt p P)) ^ P.ramificationIdx ℤ := by
  classical
  intro hcj
  have hm : fϖWk_z p P α j ∈ (OW_ker p P α).map (owToKpInt p P α) := by
    change fϖWk_z p P α j ∈ Ideal.span ((fun w : OW_subring p P α => owToKpInt p P α w) ''
      (OW_ker p P α : Set (OW_subring p P α)))
    exact Ideal.subset_span
      ⟨(⟨(fϖWk p P α).coeff j, fϖWk_coeff_mem_OW p P α j⟩ : OW_subring p P α), hcj, rfl⟩
  rwa [OW_ker_map_eq_mS_pow_ramIdx p P hα hgen] at hm

/-- **(d) part 2**: the constant coefficient of `f_ϖ` is a uniformizer of
`𝒪_W` — its `kpInt` witness has EXACT filtration degree
`e := P.ramificationIdx ℤ`: `z₀ ∈ 𝔪^e` and `z₀ ∉ 𝔪^{e+1}`. -/
theorem fϖWk_constTerm_witness_exact (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    fϖWk_z p P α 0 ∈ (maximalIdeal (kpInt p P)) ^ P.ramificationIdx ℤ ∧
    fϖWk_z p P α 0 ∉ (maximalIdeal (kpInt p P)) ^ (P.ramificationIdx ℤ + 1) := by
  classical
  constructor
  · -- z₀ ∈ 𝔪^e from (d) part 1 at i = 0 (0 < e):
    have hc0 : (⟨(fϖWk p P α).coeff 0, fϖWk_coeff_mem_OW p P α 0⟩ : OW_subring p P α)
        ∈ OW_ker p P α := fϖWk_coeff_mem_ker p P hα hgen 0 (Ideal.ramificationIdx_pos P ℤ)
    exact fϖWk_z_mem_pow_of_mem_ker p P hα hgen 0 hc0
  · -- z₀ ∉ 𝔪^{e+1}:
    intro hz0mem
    have hann := fϖWk_z_sum_annihilate p P hα hgen
    have hnat : (fϖWk p P α).natDegree = P.ramificationIdx ℤ :=
      fϖWk_natDegree_eq_ramIdx p P hα hgen
    -- z_e = 1 (g monic of degree e):
    have hze : fϖWk_z p P α (P.ramificationIdx ℤ) = 1 := by
      dsimp [fϖWk_z]
      have hce : (fϖWk p P α).coeff (P.ramificationIdx ℤ) = 1 := by
        rw [← hnat]
        exact (fϖWk_monic p P α).coeff_natDegree
      have : (⟨(fϖWk p P α).coeff (P.ramificationIdx ℤ), fϖWk_coeff_mem_OW p P α (P.ramificationIdx ℤ)⟩
          : OW_subring p P α) = 1 := by
        apply Subtype.ext
        simp [hce]
      rw [this]
      exact (owToKpInt p P α).map_one'
    -- the tail Σ_{1 ≤ j < e} z_j·ϖ^j ∈ 𝔪^{e+1} (each z_j ∈ 𝔪^e by part 1):
    have htail : (∑ j ∈ (Finset.range (P.ramificationIdx ℤ)).erase 0,
        fϖWk_z p P α j * uniformizer p P ^ j)
        ∈ (maximalIdeal (kpInt p P)) ^ (P.ramificationIdx ℤ + 1) := by
      apply sum_mem_pow_of_all (maximalIdeal (kpInt p P))
        ((Finset.range (P.ramificationIdx ℤ)).erase 0)
        (fun j => fϖWk_z p P α j * uniformizer p P ^ j)
        (fun j => P.ramificationIdx ℤ + 1) (P.ramificationIdx ℤ + 1)
      · intro j hj
        rfl
      · intro j hj
        have hmem' : j ∈ Finset.range (P.ramificationIdx ℤ) := (Finset.mem_erase.mp hj).2
        have hjnz : j ≠ 0 := (Finset.mem_erase.mp hj).1
        have hjm : j < P.ramificationIdx ℤ := Finset.mem_range.mp hmem'
        have hc0j : (⟨(fϖWk p P α).coeff j, fϖWk_coeff_mem_OW p P α j⟩ : OW_subring p P α)
            ∈ OW_ker p P α := fϖWk_coeff_mem_ker p P hα hgen j hjm
        have hzj : fϖWk_z p P α j ∈ (maximalIdeal (kpInt p P)) ^ P.ramificationIdx ℤ :=
          fϖWk_z_mem_pow_of_mem_ker p P hα hgen j hc0j
        have hpow : uniformizer p P ^ j ∈ (maximalIdeal (kpInt p P)) ^ j :=
          uniformizer_pow_mem_maximalIdeal_pow p P j
        have hprod : fϖWk_z p P α j * uniformizer p P ^ j
            ∈ (maximalIdeal (kpInt p P)) ^ (P.ramificationIdx ℤ + j) :=
          mem_mul_pow_pow_kpInt p P (fϖWk_z p P α j) (uniformizer p P ^ j)
            (P.ramificationIdx ℤ) j hzj hpow
        have hle : P.ramificationIdx ℤ + 1 ≤ P.ramificationIdx ℤ + j := by omega
        exact (Ideal.pow_le_pow_right hle) hprod
    -- the split identity: z₀ + ϖ^e + tail = 0
    have hmain : fϖWk_z p P α 0 + uniformizer p P ^ P.ramificationIdx ℤ
        + (∑ j ∈ (Finset.range (P.ramificationIdx ℤ)).erase 0, fϖWk_z p P α j * uniformizer p P ^ j) = 0 := by
      have hsplit : (∑ j ∈ Finset.range (P.ramificationIdx ℤ + 1), fϖWk_z p P α j * uniformizer p P ^ j)
          = fϖWk_z p P α 0 + uniformizer p P ^ P.ramificationIdx ℤ
              + (∑ j ∈ (Finset.range (P.ramificationIdx ℤ)).erase 0, fϖWk_z p P α j * uniformizer p P ^ j) := by
        have hsucc := Finset.sum_range_succ
          (f := fun j => fϖWk_z p P α j * uniformizer p P ^ j) (P.ramificationIdx ℤ)
        have herase := Finset.sum_erase_add
          (s := Finset.range (P.ramificationIdx ℤ))
          (f := fun j => fϖWk_z p P α j * uniformizer p P ^ j) (a := 0)
          (by exact Finset.mem_range.mpr (Ideal.ramificationIdx_pos P ℤ))
        calc
          (∑ j ∈ Finset.range (P.ramificationIdx ℤ + 1), fϖWk_z p P α j * uniformizer p P ^ j)
              = (∑ j ∈ Finset.range (P.ramificationIdx ℤ), fϖWk_z p P α j * uniformizer p P ^ j)
                  + fϖWk_z p P α (P.ramificationIdx ℤ) * uniformizer p P ^ P.ramificationIdx ℤ := hsucc
          _ = ((∑ j ∈ (Finset.range (P.ramificationIdx ℤ)).erase 0, fϖWk_z p P α j * uniformizer p P ^ j)
                  + fϖWk_z p P α 0 * uniformizer p P ^ 0)
                  + fϖWk_z p P α (P.ramificationIdx ℤ) * uniformizer p P ^ P.ramificationIdx ℤ := by
                  rw [← herase]
          _ = fϖWk_z p P α 0 + uniformizer p P ^ P.ramificationIdx ℤ
                  + (∑ j ∈ (Finset.range (P.ramificationIdx ℤ)).erase 0, fϖWk_z p P α j * uniformizer p P ^ j) := by
                  have hz0pow : fϖWk_z p P α 0 * uniformizer p P ^ 0 = fϖWk_z p P α 0 := by simp
                  have hzepow : fϖWk_z p P α (P.ramificationIdx ℤ) * uniformizer p P ^ P.ramificationIdx ℤ
                      = uniformizer p P ^ P.ramificationIdx ℤ := by simp [hze]
                  rw [hz0pow, hzepow]
                  abel
      rwa [hsplit] at hann
    -- ϖ^e = -z₀ - tail, and the RHS lies in 𝔪^{e+1}:
    have hneg : -(fϖWk_z p P α 0) ∈ (maximalIdeal (kpInt p P)) ^ (P.ramificationIdx ℤ + 1) :=
      neg_mem hz0mem
    have htailneg : -(∑ j ∈ (Finset.range (P.ramificationIdx ℤ)).erase 0,
        fϖWk_z p P α j * uniformizer p P ^ j)
        ∈ (maximalIdeal (kpInt p P)) ^ (P.ramificationIdx ℤ + 1) := neg_mem htail
    have hϖmem : uniformizer p P ^ P.ramificationIdx ℤ
        ∈ (maximalIdeal (kpInt p P)) ^ (P.ramificationIdx ℤ + 1) := by
      have hmain' : uniformizer p P ^ P.ramificationIdx ℤ
          = -(fϖWk_z p P α 0)
              - (∑ j ∈ (Finset.range (P.ramificationIdx ℤ)).erase 0, fϖWk_z p P α j * uniformizer p P ^ j) := by
        calc
          uniformizer p P ^ P.ramificationIdx ℤ
              = (fϖWk_z p P α 0 + uniformizer p P ^ P.ramificationIdx ℤ
                  + (∑ j ∈ (Finset.range (P.ramificationIdx ℤ)).erase 0, fϖWk_z p P α j * uniformizer p P ^ j))
                - fϖWk_z p P α 0
                - (∑ j ∈ (Finset.range (P.ramificationIdx ℤ)).erase 0, fϖWk_z p P α j * uniformizer p P ^ j) := by ring
          _ = -(fϖWk_z p P α 0)
              - (∑ j ∈ (Finset.range (P.ramificationIdx ℤ)).erase 0, fϖWk_z p P α j * uniformizer p P ^ j) := by
                rw [hmain]
                ring
      rw [hmain']
      rw [sub_eq_add_neg]
      exact add_mem hneg htailneg
    have hnot : uniformizer p P ^ P.ramificationIdx ℤ
        ∉ (maximalIdeal (kpInt p P)) ^ (P.ramificationIdx ℤ + 1) :=
      uniformizer_pow_not_mem_maximalIdeal_succ p P (P.ramificationIdx ℤ)
    exact hnot hϖmem


/-- **(d) part 2, subring form**: the constant coefficient `c₀` of `f_ϖ` is
NOT in `𝔪_W² = (OW_ker)²` — `c₀` is a uniformizer of `𝒪_W` (with part 1:
`c₀ ∈ 𝔪_W`).  Proof: `c₀ ∈ 𝔪_W²` would push its witness into
`𝔪^{2e} ⊆ 𝔪^{e+1}` (`Ideal.map_pow` + `OW_ker_map_eq_mS_pow_ramIdx` +
the principal-power equality `(𝔪^e)² = 𝔪^{2e}`), contradicting the exact
filtration `z₀ ∉ 𝔪^{e+1}` of `fϖWk_constTerm_witness_exact`. -/
theorem fϖWk_constTerm_not_mem_ker_sq (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    (⟨(fϖWk p P α).coeff 0, fϖWk_coeff_mem_OW p P α 0⟩ : OW_subring p P α)
      ∉ (OW_ker p P α) ^ 2 := by
  classical
  intro hc0
  let c₀ : OW_subring p P α :=
    ⟨(fϖWk p P α).coeff 0, fϖWk_coeff_mem_OW p P α 0⟩
  -- OW_ker = (pOW), so OW_ker² = (pOW²); c₀ ∈ OW_ker² gives a factor:
  have hker2 : (OW_ker p P α) ^ 2 = Ideal.span ({pOW p P α * pOW p P α} : Set (OW_subring p P α)) := by
    rw [OW_ker_eq_span_pOW p P hα hgen]
    rw [Ideal.span_singleton_pow (pOW p P α) 2]
    congr 1
    rw [pow_two]
  have hc0fac : ∃ d : OW_subring p P α,
      c₀ = d * (pOW p P α * pOW p P α) := by
    rw [hker2] at hc0
    rw [Ideal.mem_span_singleton] at hc0
    rcases hc0 with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    -- hd : (pOW * pOW) ∣ c₀ : c₀ = (pOW*pOW) * d (comm: = d * (pOW*pOW))
    simpa [c₀, mul_comm, mul_left_comm, mul_assoc] using hd
  rcases hc0fac with ⟨d, hd⟩
  -- push through owToKpInt: z₀ = φ(d)·(p : kpInt)² :
  have hz0eq : fϖWk_z p P α 0 = (owToKpInt p P α d : kpInt p P) * (p : kpInt p P) ^ 2 := by
    dsimp [fϖWk_z]
    change (owToKpInt p P α c₀) = (owToKpInt p P α d) * (p : kpInt p P) ^ 2
    -- φ c₀ = φ (d · pOW · pOW) = φ d · φ pOW · φ pOW = φ d · p · p
    have hc : c₀ = d * pOW p P α * pOW p P α := by
      simpa [mul_assoc] using hd
    rw [hc]
    rw [map_mul, map_mul]
    simp [owToKpInt_pOW p P α, pow_two, mul_comm, mul_assoc]
  -- z₀ ∈ (p : kpInt)²-span:
  have hzspan : fϖWk_z p P α 0 ∈ Ideal.span ({(p : kpInt p P) ^ 2} : Set (kpInt p P)) := by
    rw [Ideal.mem_span_singleton]
    refine ⟨owToKpInt p P α d, ?_⟩
    simpa [mul_comm] using hz0eq
  -- span{(p:kpInt)} = 𝔪^e (sub-stone (a)):
  have hspan_p : Ideal.span ({(p : kpInt p P)} : Set (kpInt p P))
      = (maximalIdeal (kpInt p P)) ^ P.ramificationIdx ℤ := by
    exact (mR_map_eq_span_p p P).symm.trans (mR_map_eq_mS_pow_ramIdx p P)
  -- (span{p})² = 𝔪^{2e}:
  have hsq : (Ideal.span ({(p : kpInt p P)} : Set (kpInt p P))) ^ 2
      = (maximalIdeal (kpInt p P)) ^ (2 * P.ramificationIdx ℤ) := by
    have hpow' : (uniformizer p P ^ P.ramificationIdx ℤ) ^ 2
        = uniformizer p P ^ (2 * P.ramificationIdx ℤ) := by
      rw [← pow_mul]
      exact congrArg (fun n : ℕ => uniformizer p P ^ n)
        (by omega : P.ramificationIdx ℤ * 2 = 2 * P.ramificationIdx ℤ)
    calc
      (Ideal.span ({(p : kpInt p P)} : Set (kpInt p P))) ^ 2
          = ((maximalIdeal (kpInt p P)) ^ P.ramificationIdx ℤ) ^ 2 := by rw [hspan_p]
      _ = Ideal.span {(uniformizer p P ^ P.ramificationIdx ℤ) ^ 2} := by
            rw [maximalIdeal_pow_eq_span p P (P.ramificationIdx ℤ)]
            exact (Ideal.span_singleton_pow (uniformizer p P ^ P.ramificationIdx ℤ) 2)
      _ = (maximalIdeal (kpInt p P)) ^ (2 * P.ramificationIdx ℤ) := by
            rw [hpow']
            rw [← maximalIdeal_pow_eq_span p P (2 * P.ramificationIdx ℤ)]
  -- span{(p:kpInt)²} = (span{p})² = 𝔪^{2e}:
  have hz2e : fϖWk_z p P α 0 ∈ (maximalIdeal (kpInt p P)) ^ (2 * P.ramificationIdx ℤ) := by
    have hs2 : Ideal.span ({(p : kpInt p P) ^ 2} : Set (kpInt p P))
        = (maximalIdeal (kpInt p P)) ^ (2 * P.ramificationIdx ℤ) := by
      calc
        Ideal.span ({(p : kpInt p P) ^ 2} : Set (kpInt p P))
            = (Ideal.span ({(p : kpInt p P)} : Set (kpInt p P))) ^ 2 := by
              exact (Ideal.span_singleton_pow ((p : kpInt p P)) 2).symm
        _ = (maximalIdeal (kpInt p P)) ^ (2 * P.ramificationIdx ℤ) := hsq
    rw [hs2] at hzspan
    exact hzspan
  -- 𝔪^{2e} ⊆ 𝔪^{e+1}:
  have hle : P.ramificationIdx ℤ + 1 ≤ 2 * P.ramificationIdx ℤ := by
    have he1 : 1 ≤ P.ramificationIdx ℤ := Ideal.ramificationIdx_pos P ℤ
    omega
  have hz0 : fϖWk_z p P α 0 ∈ (maximalIdeal (kpInt p P)) ^ (P.ramificationIdx ℤ + 1) :=
    (Ideal.pow_le_pow_right hle) hz2e
  have hnot := (fϖWk_constTerm_witness_exact p P hα hgen).2
  exact hnot hz0


/-! ## (U): the valuation of an 𝒪_W element is an `e`-multiple

THEOREM **`OW_witness_kpVal_dvd`** — the restriction of the `𝔪`-adic
valuation of `kpInt` to the Teichmüller subfield `W`: for every `c ∈ 𝒪_W`
(`c ≠ 0`) with `kpInt`-witness `z := owToKpInt c`, the filtration degree
`kpVal z` is a multiple of `e := P.ramificationIdx ℤ`.  Proof (induction on
`kpVal z`): if `z ∉ 𝔪` then `z` is a unit so `kpVal z = 0`; if `z ∈ 𝔪`
then `c ∈ 𝔪_W` (kernel description `owToKpInt_mem_maximalIdeal_iff_mem_ker`,
`resOW_hom c = mk z`), and `𝔪_W = (pOW)` (`OW_ker_eq_span_pOW`) gives
`c = pOW·u`, so `z = p·z_u` and
`kpVal z = kpVal p + kpVal z_u = e + kpVal z_u`
(`kpVal_mul` + `kpVal_natCast_p`); `kpVal z_u < kpVal z` (e ≥ 1), and the
induction hypothesis applied to `u` gives `e ∣ kpVal z_u`, hence
`e ∣ kpVal z`.  This is the restriction-of-valuation input of the
WildDifferent (e) sub-stone (the term-valuation congruence
`v(i·c_i·ϖ^{i−1}) ≡ (i−1) mod e` needs `kpVal z_i ≡ 0 mod e` for the
coefficient witnesses `z_i`).
-/

/-- Kernel description for an arbitrary 𝒪_W element: the `kpInt` witness
lies in 𝔪 exactly when the element lies in `𝔪_W = OW_ker`. -/
lemma owToKpInt_mem_maximalIdeal_iff_mem_ker (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (c : OW_subring p P α) :
    owToKpInt p P α c ∈ maximalIdeal (kpInt p P) ↔ c ∈ OW_ker p P α := by
  classical
  rw [RingHom.mem_ker]
  rw [show (resOW_hom p P α) c = Ideal.Quotient.mk (maximalIdeal (kpInt p P))
      (owToKpInt p P α c) by
        exact resOW_hom_eq_mk_owToKpInt p P α c]
  exact (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal (kpInt p P))
    (a := owToKpInt p P α c)).symm

/-- **(U)**: the `𝔪`-adic valuation of an 𝒪_W element's `kpInt` witness is
an `e := P.ramificationIdx ℤ`-multiple (the restriction of the valuation
to the unramified Teichmüller subfield `W`). -/
theorem OW_witness_kpVal_dvd (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (c : OW_subring p P α) (hc : c ≠ 0) :
    P.ramificationIdx ℤ ∣ kpVal p P (owToKpInt p P α c) := by
  classical
  have hw0 : ∀ c' : OW_subring p P α, c' ≠ 0 → owToKpInt p P α c' ≠ 0 := by
    intro c' hc' hz
    exact hc' (owToKpInt_injective p P α (by simpa using hz))
  have he1 : 1 ≤ P.ramificationIdx ℤ := Ideal.ramificationIdx_pos P ℤ
  -- strong induction on the witness value:
  have hmain : ∀ n : ℕ, (∀ t < n, ∀ (c' : OW_subring p P α), c' ≠ 0 →
      kpVal p P (owToKpInt p P α c') = t → P.ramificationIdx ℤ ∣ t) →
      ∀ (c' : OW_subring p P α), c' ≠ 0 →
      kpVal p P (owToKpInt p P α c') = n → P.ramificationIdx ℤ ∣ n := by
    intro n ih c' hc' hn
    by_cases hwin : owToKpInt p P α c' ∈ maximalIdeal (kpInt p P)
    · -- witness ∈ 𝔪: c' ∈ 𝔪_W = (pOW), c' = pOW·u
      have hck : c' ∈ OW_ker p P α := (owToKpInt_mem_maximalIdeal_iff_mem_ker p P α c').1 hwin
      have hspan : c' ∈ Ideal.span ({pOW p P α} : Set (OW_subring p P α)) := by
        rw [OW_ker_eq_span_pOW p P hα hgen] at hck
        exact hck
      rw [Ideal.mem_span_singleton] at hspan
      rcases hspan with ⟨u, hu⟩
      -- hu : c' = (pOW p P α) * u (divisibility orientation)
      have huz : u ≠ 0 := by
        intro hu0
        apply hc'
        rw [hu, hu0]
        simp
      have huz0 : owToKpInt p P α u ≠ 0 := hw0 u huz
      -- witness(c') = p·witness(u):
      have hwceq : owToKpInt p P α c' = (p : kpInt p P) * owToKpInt p P α u := by
        rw [hu]
        rw [map_mul]
        rw [owToKpInt_pOW p P α]
      -- kpVal(wc') = e + kpVal(wu):
      have hkp : kpVal p P (owToKpInt p P α c') = P.ramificationIdx ℤ + kpVal p P (owToKpInt p P α u) := by
        rw [hwceq]
        rw [kpVal_mul p P (p : kpInt p P) (owToKpInt p P α u) (int_p_ne_zero p P) huz0]
        rw [kpVal_natCast_p p P]
      have htlt : kpVal p P (owToKpInt p P α u) < n := by
        rw [← hn]
        rw [hkp]
        omega
      have hdvu : P.ramificationIdx ℤ ∣ kpVal p P (owToKpInt p P α u) :=
        ih (kpVal p P (owToKpInt p P α u)) htlt u huz rfl
      rw [← hn]
      rw [hkp]
      exact dvd_add (dvd_refl (P.ramificationIdx ℤ)) hdvu
    · -- witness ∉ 𝔪: z is a unit, kpVal z = 0
      have hkp0 : kpVal p P (owToKpInt p P α c') = 0 := by
        rw [mem_maximalIdeal_iff_one_le_kpVal p P (owToKpInt p P α c') (hw0 c' hc')] at hwin
        omega
      rw [← hn]
      rw [hkp0]
      exact dvd_zero (P.ramificationIdx ℤ)
  have hfinal : ∀ (c' : OW_subring p P α), c' ≠ 0 →
      kpVal p P (owToKpInt p P α c') = kpVal p P (owToKpInt p P α c) →
      P.ramificationIdx ℤ ∣ kpVal p P (owToKpInt p P α c) := by
    exact Nat.strong_induction_on (kpVal p P (owToKpInt p P α c)) hmain
  exact hfinal c hc rfl

/-- The top coefficient witness is 1: `z_e = 1` (the leading coefficient of
the monic `f_ϖ` of degree `e`). -/
lemma fϖWk_z_top_eq_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    fϖWk_z p P α (P.ramificationIdx ℤ) = 1 := by
  classical
  dsimp [fϖWk_z]
  have hnat : (fϖWk p P α).natDegree = P.ramificationIdx ℤ :=
    fϖWk_natDegree_eq_ramIdx p P hα hgen
  have hce : (fϖWk p P α).coeff (P.ramificationIdx ℤ) = 1 := by
    rw [← hnat]
    exact (fϖWk_monic p P α).coeff_natDegree
  have hc : (⟨(fϖWk p P α).coeff (P.ramificationIdx ℤ), fϖWk_coeff_mem_OW p P α (P.ramificationIdx ℤ)⟩
      : OW_subring p P α) = 1 := by
    apply Subtype.ext
    simp [hce]
  rw [hc]
  exact (owToKpInt p P α).map_one'


end
end Submission.Vdw.LocalField
