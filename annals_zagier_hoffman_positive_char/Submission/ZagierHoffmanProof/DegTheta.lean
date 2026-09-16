import Submission.ZagierHoffmanProof.KuanLin
import Submission.ZagierHoffmanProof.ACMplDatum

/-!
# The `θ`-degree on `ambA F 0 = F_q[θ]`, and the degree estimate of IMKDP Lemma 3.3

`ambA F 0` is the image of `F_q[X]` under `X ↦ θ` (`mem_ambA_iff`), and by the transcendence of `θ`
over `F_q` (`ambTheta_transcendental`) the witnessing polynomial is unique.  `degTheta x` is its
degree.  This is the `θ`-degree of the degree estimate in Lemma 3.3 of

* B.-H. Im, H. Kim, K. N. Le, T. N. Dac, L. H. Pham, *Zagier–Hoffman's conjectures in positive
  characteristic*, arXiv:2205.07165 (2022),

the replacement of the Kuan–Lin citation of ND21 §6 (see `Submission/PLAN.md` §«SESSION 351»).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial
open scoped WithZero

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The `θ`-degree of an element of `ambA F 0 = F_q[θ]` (and `0` on elements outside). -/
noncomputable def degTheta (x : Ambient F) : ℕ := by
  classical
  exact if h : x ∈ ambA F 0 then (Classical.choose ((mem_ambA_iff F 0 x).mp h)).natDegree else 0

lemma degTheta_of_mem {x : Ambient F} (hx : x ∈ ambA F 0) :
    degTheta F x = (Classical.choose ((mem_ambA_iff F 0 x).mp hx)).natDegree :=
  dif_pos hx

/-- The witnessing polynomial evaluates to `x`. -/
lemma degTheta_witness {x : Ambient F} (hx : x ∈ ambA F 0) :
    (Classical.choose ((mem_ambA_iff F 0 x).mp hx)).eval₂ (algebraMap F (Ambient F)) (ambTheta F)
      = x := by
  simpa only [ambThetaNu_zero] using Classical.choose_spec ((mem_ambA_iff F 0 x).mp hx)

/-- `degTheta` computed from any witnessing polynomial. -/
lemma degTheta_eq_of_eval {x : Ambient F} (hx : x ∈ ambA F 0) {p : Polynomial F}
    (hp : p.eval₂ (algebraMap F (Ambient F)) (ambTheta F) = x) : degTheta F x = p.natDegree := by
  rw [degTheta_of_mem F hx]
  congr 1
  refine sub_eq_zero.mp (ambTheta_transcendental F _ ?_)
  rw [Polynomial.eval₂_sub, hp, degTheta_witness F hx, sub_self]

-- IN PROGRESS (SESSION 351/352): the following lemmas are the remaining content of the
-- `θ`-degree estimate of IMKDP Lemma 3.3 (the statements are fixed; see `PLAN.md` §«SESSION 351»
-- §3 for the proofs to be written/ported).  They are commented out so that this module compiles.
--
/-- Conventions: `degTheta 0 = 0` (`deg_θ 0 = -∞` mathematically) and `degTheta 1 = 0`. -/
@[simp] lemma degTheta_zero : degTheta F (0 : Ambient F) = 0 := by
  rw [degTheta_eq_of_eval F ((ambASub F 0).zero_mem) (p := 0) (by simp)]
  simp

@[simp] lemma degTheta_one : degTheta F (1 : Ambient F) = 0 := by
  rw [degTheta_eq_of_eval F (ambA_one_mem F 0) (p := 1) (by simp)]
  simp

/-- `deg_θ θ = 1`. -/
lemma degTheta_theta : degTheta F (ambTheta F) = 1 := by
  rw [degTheta_eq_of_eval F (ambTheta_mem_ambA_zero) (p := Polynomial.X) (by simp)]
  simp

/-- `deg_θ (θ^e) = e`. -/
lemma degTheta_pow_theta (e : ℕ) : degTheta F ((ambTheta F) ^ e) = e := by
  rw [degTheta_eq_of_eval F (ambA_pow_mem F 0 (ambTheta_mem_ambA_zero) e)
      (p := Polynomial.X ^ e) (by simp)]
  simp
/-- The `θ`-degree is subadditive. -/
lemma degTheta_add_le {x y : Ambient F} (hx : x ∈ ambA F 0) (hy : y ∈ ambA F 0) :
    degTheta F (x + y) ≤ max (degTheta F x) (degTheta F y) := by
  set px := Classical.choose ((mem_ambA_iff F 0 x).mp hx) with hpx
  set py := Classical.choose ((mem_ambA_iff F 0 y).mp hy) with hpy
  have ex : px.eval₂ (algebraMap F (Ambient F)) (ambTheta F) = x := degTheta_witness F hx
  have ey : py.eval₂ (algebraMap F (Ambient F)) (ambTheta F) = y := degTheta_witness F hy
  have hxy : (px + py).eval₂ (algebraMap F (Ambient F)) (ambTheta F) = x + y := by
    rw [Polynomial.eval₂_add, ex, ey]
  have h1 : degTheta F (x + y) = (px + py).natDegree :=
    degTheta_eq_of_eval F (ambA_add_mem F hx hy) hxy
  have h2 : degTheta F x = px.natDegree := degTheta_eq_of_eval F hx ex
  have h3 : degTheta F y = py.natDegree := degTheta_eq_of_eval F hy ey
  rw [h1, h2, h3]
  exact Polynomial.natDegree_add_le px py
/-- The `θ`-degree is additive on products (for nonzero factors: `degTheta 0 = 0` is a convention,
`deg_θ 0 = -∞` mathematically). -/
lemma degTheta_mul {x y : Ambient F} (hx : x ∈ ambA F 0) (hy : y ∈ ambA F 0)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    degTheta F (x * y) = degTheta F x + degTheta F y := by
  set px := Classical.choose ((mem_ambA_iff F 0 x).mp hx) with hpx
  set py := Classical.choose ((mem_ambA_iff F 0 y).mp hy) with hpy
  have ex : px.eval₂ (algebraMap F (Ambient F)) (ambTheta F) = x := degTheta_witness F hx
  have ey : py.eval₂ (algebraMap F (Ambient F)) (ambTheta F) = y := degTheta_witness F hy
  have hpx0 : px ≠ 0 := fun h => hx0 (by rw [← ex, h, Polynomial.eval₂_zero])
  have hpy0 : py ≠ 0 := fun h => hy0 (by rw [← ey, h, Polynomial.eval₂_zero])
  have hxy : (px * py).eval₂ (algebraMap F (Ambient F)) (ambTheta F) = x * y := by
    rw [Polynomial.eval₂_mul, ex, ey]
  have h1 : degTheta F (x * y) = (px * py).natDegree :=
    degTheta_eq_of_eval F (ambA_mul_mem F hx hy) hxy
  have h2 : degTheta F x = px.natDegree := degTheta_eq_of_eval F hx ex
  have h3 : degTheta F y = py.natDegree := degTheta_eq_of_eval F hy ey
  rw [h1, h2, h3, Polynomial.natDegree_mul hpx0 hpy0]
/-- `(Σ_i c_i θ^i)^q = Σ_i c_i (θ^q)^i` for coefficients `c_i ∈ F_q`. -/
lemma eval₂_theta_pow_card (p : Polynomial F) :
    p.eval₂ (algebraMap F (Ambient F)) ((ambTheta F) ^ Nat.card F)
      = (p.eval₂ (algebraMap F (Ambient F)) (ambTheta F)) ^ Nat.card F := by
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range,
    FrobPow.sum_pow_finset]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hq : (ambCoeff F (p.coeff i)) ^ Nat.card F = ambCoeff F (p.coeff i) :=
    (mem_ambF_iff F _).mp (ambCoeff_mem_ambF F _)
  simp only [algebraMap_ambient_eq]
  rw [mul_pow, ← pow_mul, ← pow_mul, hq, Nat.mul_comm i (Nat.card F)]

/-- Substituting `X ↦ X^q` and evaluating at `θ` is the `q`-th power. -/
lemma comp_X_pow_eval₂ (p : Polynomial F) :
    (p.comp (Polynomial.X ^ Nat.card F)).eval₂ (algebraMap F (Ambient F)) (ambTheta F)
      = p.eval₂ (algebraMap F (Ambient F)) ((ambTheta F) ^ Nat.card F) := by
  rw [Polynomial.eval₂_comp]
  congr 1
  rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]

/-- ★★ The Frobenius behaviour of the `θ`-degree. -/
lemma degTheta_pow_card {x : Ambient F} (hx : x ∈ ambA F 0) :
    degTheta F (x ^ Nat.card F) = Nat.card F * degTheta F x := by
  set p := Classical.choose ((mem_ambA_iff F 0 x).mp hx) with hp
  have ex : p.eval₂ (algebraMap F (Ambient F)) (ambTheta F) = x := degTheta_witness F hx
  have hcomp : (p.comp (Polynomial.X ^ Nat.card F)).eval₂ (algebraMap F (Ambient F)) (ambTheta F)
      = x ^ Nat.card F := by
    rw [comp_X_pow_eval₂, eval₂_theta_pow_card, ex]
  rw [degTheta_eq_of_eval F (ambA_pow_mem F 0 hx (Nat.card F))
      (p := p.comp (Polynomial.X ^ Nat.card F)) hcomp,
    degTheta_eq_of_eval F hx ex, Polynomial.natDegree_comp, Polynomial.natDegree_X_pow]
  exact Nat.mul_comm _ _
/-! ## §2. Auxiliary `θ`-degree bounds for sums -/

/-- A finite sum of elements of `ambA F 0` whose `θ`-degrees are bounded by `B` has `θ`-degree
bounded by `B`. -/
lemma degTheta_sum_le {ι : Type*} (s : Finset ι) (f : ι → Ambient F)
    (hf : ∀ i ∈ s, f i ∈ ambA F 0) {B : ℕ} (hB : ∀ i ∈ s, degTheta F (f i) ≤ B) :
    degTheta F (∑ i ∈ s, f i) ≤ B := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (degTheta_add_le F (hf a (Finset.mem_insert_self a s))
        ((ambASub F 0).sum_mem fun i hi => hf i (Finset.mem_insert_of_mem hi))) ?_
      exact max_le (hB a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hB i (Finset.mem_insert_of_mem hi)))

/-! ## §3. The coefficient of `X^n` on the left-hand side -/

/-- An element of `ambF F = F_q` has `θ`-degree `0`. -/
lemma degTheta_of_mem_ambF {ε : Ambient F} (hε : ε ∈ ambF F) (hε0 : ε ≠ 0) :
    degTheta F ε = 0 := by
  obtain ⟨c, rfl⟩ := eq_range_ambCoeff_of_mem_ambF F hε
  have hp : (Polynomial.C c).eval₂ (algebraMap F (Ambient F)) (ambTheta F) = ambCoeff F c := by
    rw [Polynomial.eval₂_C, algebraMap_ambient_eq]
  rw [degTheta_eq_of_eval F (ambF_subset_ambA_zero (ambCoeff_mem_ambF F c))
      (p := Polynomial.C c) hp]
  exact Polynomial.natDegree_C c

/-- The coefficient of `X^n` in `C ε * polyTwist 1 δ` is `ε * (δ.coeff n)^q`. -/
lemma coeff_C_mul_polyTwist (ε : Ambient F) (δ : Polynomial (Ambient F)) (n : ℕ) :
    (Polynomial.C ε * polyTwist (q := Nat.card F) 1 δ).coeff n = ε * (δ.coeff n) ^ Nat.card F := by
  rw [Polynomial.coeff_C_mul, coeff_polyTwist_one]

/-- ★ **The left-hand side of the comparison**: the coefficient of `X^n` in `C ε * polyTwist 1 δ`
has `θ`-degree `q * degTheta (δ.coeff n)` (for `ε ∈ F_q^×` and `δ.coeff n ≠ 0`). -/
lemma degTheta_LHS_coeff {ε : Ambient F} (hε : ε ∈ ambF F) (hε0 : ε ≠ 0)
    {δ : Polynomial (Ambient F)} (hδ : ∀ n, δ.coeff n ∈ ambA F 0) (n : ℕ)
    (hδn : δ.coeff n ≠ 0) :
    degTheta F ((Polynomial.C ε * polyTwist (q := Nat.card F) 1 δ).coeff n)
      = Nat.card F * degTheta F (δ.coeff n) := by
  rw [coeff_C_mul_polyTwist]
  rw [degTheta_mul F (ambF_subset_ambA_zero hε) (ambA_pow_mem F 0 (hδ n) (Nat.card F))
    hε0 (pow_ne_zero _ hδn)]
  rw [degTheta_pow_card F (hδ n), degTheta_of_mem_ambF F hε hε0, zero_add]


/-! ## §4. Powers, signs, and constants; the coefficient of `X^j` in `(X - C a)^m` -/

/-- `deg_θ (x^k) = k · deg_θ x` for `x ≠ 0`. -/
lemma degTheta_pow {x : Ambient F} (hx : x ∈ ambA F 0) (hx0 : x ≠ 0) (k : ℕ) :
    degTheta F (x ^ k) = k * degTheta F x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, degTheta_mul F (ambA_pow_mem F 0 hx k) hx (pow_ne_zero k hx0) hx0, ih]
      ring

/-- Negation does not change the `θ`-degree. -/
lemma degTheta_neg {x : Ambient F} (hx : x ∈ ambA F 0) : degTheta F (-x) = degTheta F x := by
  rw [degTheta_eq_of_eval F ((ambASub F 0).neg_mem hx)
        (p := -Classical.choose ((mem_ambA_iff F 0 x).mp hx))
        (by rw [Polynomial.eval₂_neg, degTheta_witness F hx]),
      degTheta_eq_of_eval F hx (p := Classical.choose ((mem_ambA_iff F 0 x).mp hx))
        (degTheta_witness F hx),
      Polynomial.natDegree_neg]

/-- Natural-number constants lie in `ambA F 0`. -/
lemma natCast_mem_ambA (n : ℕ) : ((n : Ambient F)) ∈ ambA F 0 := by
  rw [← map_natCast (algebraMap F (Ambient F)) n, algebraMap_ambient_eq]
  exact ambF_subset_ambA_zero (ambCoeff_mem_ambF F _)

/-- Natural-number constants have `θ`-degree `0`. -/
lemma degTheta_natCast (n : ℕ) : degTheta F ((n : Ambient F)) = 0 := by
  rcases eq_or_ne ((n : Ambient F)) 0 with h | hn
  · rw [h, degTheta_zero]
  rw [← map_natCast (algebraMap F (Ambient F)) n]
  exact degTheta_of_mem_ambF F
    (by rw [algebraMap_ambient_eq]; exact ambCoeff_mem_ambF F _) (by rwa [map_natCast])

/-- ★ **The coefficient of `X^j` in `(X - C a)^m`**: its `θ`-degree is at most `m · deg_θ a`
(via Mathlib's `Polynomial.coeff_X_add_C_pow`). -/
lemma degTheta_coeff_X_sub_C_pow {a : Ambient F} (ha : a ∈ ambA F 0) (m j : ℕ) :
    degTheta F (((Polynomial.X - Polynomial.C a) ^ m).coeff j) ≤ m * degTheta F a := by
  have hX : Polynomial.X - Polynomial.C a = Polynomial.X + Polynomial.C (-a) := by
    rw [map_neg, sub_eq_add_neg]
  rw [hX, Polynomial.coeff_X_add_C_pow]
  rcases eq_or_ne (m.choose j : Ambient F) 0 with hc | hc
  · rw [hc, mul_zero, degTheta_zero]
    exact Nat.zero_le _
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [neg_zero, degTheta_zero, mul_zero]
    rcases eq_or_ne (m - j) 0 with h0 | h0
    · rw [h0, pow_zero, one_mul]
      exact le_of_eq (degTheta_natCast F (m.choose j))
    · rw [zero_pow h0, zero_mul, degTheta_zero]
  have hna : (-a) ∈ ambA F 0 := (ambASub F 0).neg_mem ha
  have hna0 : -a ≠ 0 := neg_ne_zero.mpr ha0
  refine le_trans (le_of_eq (degTheta_mul F (ambA_pow_mem F 0 hna (m - j))
    (natCast_mem_ambA F (m.choose j)) (pow_ne_zero _ hna0) hc)) ?_
  rw [degTheta_pow F hna hna0, degTheta_neg F ha, degTheta_natCast, add_zero]
  exact Nat.mul_le_mul_right _ (Nat.sub_le m j)

/-- ★ **The `θ`-degree of a coefficient of a product**: bounded by the sum of the bounds on the
factors' coefficients. -/
lemma degTheta_coeff_mul_le {p q : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (hq : ∀ n, q.coeff n ∈ ambA F 0)
    {D E : ℕ} (hD : ∀ n, degTheta F (p.coeff n) ≤ D) (hE : ∀ n, degTheta F (q.coeff n) ≤ E)
    (n : ℕ) : degTheta F ((p * q).coeff n) ≤ D + E := by
  rw [Polynomial.coeff_mul]
  exact degTheta_sum_le F (Finset.HasAntidiagonal.antidiagonal n)
    (fun x => p.coeff x.1 * q.coeff x.2) (fun x _ => ambA_mul_mem F (hp x.1) (hq x.2))
    (fun x _ => by
      rcases eq_or_ne (p.coeff x.1) 0 with h0 | h0
      · rw [h0, zero_mul, degTheta_zero]
        exact Nat.zero_le _
      rcases eq_or_ne (q.coeff x.2) 0 with h0' | h0'
      · rw [h0', mul_zero, degTheta_zero]
        exact Nat.zero_le _
      · rw [degTheta_mul F (hp x.1) (hq x.2) h0 h0']
        exact add_le_add (hD x.1) (hE x.2))

/-! ## §5. The `θ`-degree estimate of IMKDP Lemma 3.3 -/

/-- ★★★ **The `θ`-degree estimate** (`deg_θ δ ≤ max (q·m/(q-1), deg_θ F / q)`, division-free), in
the form used by the two-term endgame of the Zagier–Hoffman problem. -/
theorem kuanLin_degree {m : ℕ} (hm : 1 ≤ m) {ε : Ambient F} (hε : ε ∈ ambF F) (hε0 : ε ≠ 0)
    {δ Fp : Polynomial (Ambient F)} (hδ : ∀ n, δ.coeff n ∈ ambA F 0)
    (hFp : ∀ n, Fp.coeff n ∈ ambA F 0)
    (h : Polynomial.C ε * polyTwist (q := Nat.card F) 1 δ
      = δ * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ m + Fp)
    {n₀ : ℕ} (hn₀ : ∀ n, degTheta F (δ.coeff n) ≤ degTheta F (δ.coeff n₀))
    {E : ℕ} (hE : ∀ n, degTheta F (Fp.coeff n) ≤ E) :
    (Nat.card F - 1) * degTheta F (δ.coeff n₀) ≤ Nat.card F * m ∨
      Nat.card F * degTheta F (δ.coeff n₀) ≤ E := by
  have hq2 : 2 ≤ Nat.card F := two_le_ambCard F
  rcases eq_or_ne (δ.coeff n₀) 0 with h0 | h0
  · left
    rw [h0, degTheta_zero]
    exact Nat.zero_le _
  have hW : ((ambTheta F) ^ Nat.card F) ∈ ambA F 0 := ambA_pow_mem F 0 ambTheta_mem_ambA_zero _
  have hWdeg : degTheta F ((ambTheta F) ^ Nat.card F) = Nat.card F := by
    rw [degTheta_pow_card F ambTheta_mem_ambA_zero, degTheta_theta, mul_one]
  have hL : degTheta F ((Polynomial.C ε * polyTwist (q := Nat.card F) 1 δ).coeff n₀)
      = Nat.card F * degTheta F (δ.coeff n₀) := degTheta_LHS_coeff F hε hε0 hδ n₀ h0
  have hR : degTheta F ((δ * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ m
        + Fp).coeff n₀) ≤ max (degTheta F (δ.coeff n₀) + (m * Nat.card F)) E := by
    rw [Polynomial.coeff_add]
    refine le_trans (degTheta_add_le F
      (coeff_mul_mem_ambA0 hδ (coeff_X_sub_C_pow_mem hW m) n₀) (hFp n₀)) (max_le ?_ ?_)
    · refine le_trans (degTheta_coeff_mul_le F hδ (coeff_X_sub_C_pow_mem hW m) hn₀ ?_ n₀)
        (le_max_left _ _)
      intro j
      simpa only [hWdeg] using degTheta_coeff_X_sub_C_pow F hW m j
    · exact le_trans (hE n₀) (le_max_right _ _)
  have hkey : Nat.card F * degTheta F (δ.coeff n₀)
      ≤ max (degTheta F (δ.coeff n₀) + (m * Nat.card F)) E := by
    have heq : (Polynomial.C ε * polyTwist (q := Nat.card F) 1 δ).coeff n₀
        = (δ * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ m + Fp).coeff n₀ :=
      congrArg (fun p : Polynomial (Ambient F) => p.coeff n₀) h
    calc Nat.card F * degTheta F (δ.coeff n₀)
        = degTheta F ((Polynomial.C ε * polyTwist (q := Nat.card F) 1 δ).coeff n₀) := hL.symm
      _ = degTheta F ((δ * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ m
            + Fp).coeff n₀) := by rw [heq]
      _ ≤ max (degTheta F (δ.coeff n₀) + (m * Nat.card F)) E := hR
  have hD : Nat.card F * degTheta F (δ.coeff n₀)
      = (Nat.card F - 1) * degTheta F (δ.coeff n₀) + degTheta F (δ.coeff n₀) := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ Nat.card F by omega)]
    rw [add_mul, one_mul]
  by_cases hc : Nat.card F * degTheta F (δ.coeff n₀) ≤ E
  · exact Or.inr hc
  · left
    rw [max_def] at hkey
    split_ifs at hkey
    · exact absurd hkey hc
    · have h2 : (Nat.card F - 1) * degTheta F (δ.coeff n₀) + degTheta F (δ.coeff n₀)
          ≤ Nat.card F * m + degTheta F (δ.coeff n₀) := by
        rw [← hD]
        calc Nat.card F * degTheta F (δ.coeff n₀)
            ≤ degTheta F (δ.coeff n₀) + m * Nat.card F := hkey
          _ = Nat.card F * m + degTheta F (δ.coeff n₀) := by ring
      omega

-- ★★★ NEXT: the `∅`-row closure (SESSION 350 §2.5 + SESSION 351 §2)
-- ★★★ NEXT: the assembly of IMKDP Lemma 3.3's degree estimate (see PLAN.md §«SESSION 351» §2-3).
-- The statement to prove (all hypotheses are the ones the ABP rows provide, cf. `tmB_nil_row`):
--
-- theorem kuanLin_degree {m : ℕ} (hm : 1 ≤ m) {ε : Ambient F} (hε : ε ∈ ambF F) (hε0 : ε ≠ 0)
--     {δ Fp : Polynomial (Ambient F)} (hδ : ∀ n, δ.coeff n ∈ ambA F 0)
--     (hFp : ∀ n, Fp.coeff n ∈ ambA F 0)
--     (h : Polynomial.C ε * polyTwist (q := Nat.card F) 1 δ
--       = δ * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ m + Fp)
--     {n₀ : ℕ} (hn₀ : ∀ n, degTheta F (δ.coeff n) ≤ degTheta F (δ.coeff n₀))
--     {E : ℕ} (hE : ∀ n, degTheta F (Fp.coeff n) ≤ E) :
--     (Nat.card F - 1) * degTheta F (δ.coeff n₀) ≤ Nat.card F * m ∨
--       Nat.card F * degTheta F (δ.coeff n₀) ≤ E
--
-- PROOF OUTLINE (3 lines in the paper, `coeff`-level here):
-- * take the coefficients of `X^{n₀}` of both sides (`Polynomial.coeff_mul`,
--   `HasAntidiagonal.antidiagonal`); the LHS coefficient is `ε * (δ.coeff n₀)^q`
--   (`coeff_polyTwist_one`) with θ-degree `q * degTheta (δ.coeff n₀)` by `degTheta_mul`
--   (`degTheta ε = 0` for `ε ∈ ambF F`) and `degTheta_pow_card`;
-- * the RHS coefficient is `Σ_{i+j=n₀} δ.coeff i * ((X - C (θ^q))^m).coeff j + Fp.coeff n₀`;
--   the θ-degree of `((X - C (θ^q))^m).coeff j = binom(m,j) * (-θ^q)^(m-j)` is `q*(m-j) ≤ q*m`
--   (`degTheta_pow_theta`, `degTheta_mul`), and `degTheta (δ.coeff i) ≤ degTheta (δ.coeff n₀)`
--   by `hn₀`; so the whole RHS coefficient has θ-degree `≤ max (degTheta (δ.coeff n₀) + q*m) E`
--   (`degTheta_add_le` + `Finset`-induction over the antidiagonal);
-- * if `q * D > degTheta (δ.coeff n₀) + q*m` (i.e. `(q-1)*D > q*m`) and `q * D > E`, the two sides'
--   θ-degrees differ, contradicting the equality `h` — exactly the paper's argument.
--
-- When `Commons.NumberTheory.FunctionField.theta_degree_bound` lands, the same statement can be
-- obtained by instantiating it (it is the abstract version of this comparison).

end ZagierHoffmanPositiveChar
