import Submission.ZagierHoffmanProof.DegNu

/-!
# The `θ_μ`-coefficient extraction on `A_μ = F_q[θ_μ]`

`ambA F μ = F_q[θ_μ]` is the image of `F_q[T]` under `T ↦ θ_μ`, and `θ_μ` is transcendental over
`F_q` (`ambThetaNu_transcendental`), so the witnessing polynomial of `x ∈ A_μ` is unique and the
`θ_μ`-expansion of `x` is finite and well defined.  This file makes that expansion a first-class
object:

* `coeffNu F μ j x` — the coefficient of `θ_μ^j` in `x ∈ A_μ` (junk `0` outside);
* `coeffNu_of_mem`, `coeffNu_eq_of_eval` (well-definedness);
* `coeffNu_add`, `coeffNu_self`;
* ★★ `coeffNu_pow_card`: `coeffNu μ (q·j) (x^q) = coeffNu μ j x` — the Frobenius **permutes** the
  `θ_μ`-coefficients (there is NO `q`-th power on the right, because `x`'s coefficients already lie in
  `F_q`).  This is the `σ(θ_μ) = θ_μ^q` engine of the level descent.

⚠ The fraction-field version (`coeffRat` on `ratLevelF F μ`) is the follow-up; the sign/shape
conventions fixed here are the ones the descent uses.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial
open scoped WithZero

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The coefficient of `θ_μ^j` -/

/-- The coefficient of `θ_μ^j` in an element of `A_μ = F_q[θ_μ]` (and `0` outside). -/
noncomputable def coeffNu (μ : ℕ) (j : ℕ) (x : Ambient F) : Ambient F := by
  classical
  exact if h : x ∈ ambA F μ then
    (algebraMap F (Ambient F)) ((Classical.choose ((mem_ambA_iff F μ x).mp h)).coeff j) else 0

lemma coeffNu_of_mem {μ : ℕ} {x : Ambient F} (hx : x ∈ ambA F μ) (j : ℕ) :
    coeffNu F μ j x = (algebraMap F (Ambient F))
      ((Classical.choose ((mem_ambA_iff F μ x).mp hx)).coeff j) :=
  dif_pos hx

/-- **Well-definedness**: `coeffNu` computed from any witnessing polynomial. -/
lemma coeffNu_eq_of_eval {μ : ℕ} {x : Ambient F} (hx : x ∈ ambA F μ) {p : Polynomial F}
    (hp : p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F μ) = x) (j : ℕ) :
    coeffNu F μ j x = (algebraMap F (Ambient F)) (p.coeff j) := by
  rw [coeffNu_of_mem F hx j]
  congr 1
  have h : Classical.choose ((mem_ambA_iff F μ x).mp hx) - p = 0 := by
    refine ambThetaNu_transcendental F μ _ ?_
    rw [Polynomial.eval₂_sub, degNu_witness F hx, hp, sub_self]
  exact congrArg (fun r : Polynomial F => r.coeff j) (sub_eq_zero.mp h)

@[simp] lemma coeffNu_zero (μ : ℕ) (j : ℕ) : coeffNu F μ j (0 : Ambient F) = 0 := by
  rw [coeffNu_eq_of_eval F ((ambASub F μ).zero_mem) (p := 0) (by simp)]
  simp

/-- `θ_μ` itself. -/
lemma coeffNu_self (μ : ℕ) : coeffNu F μ 1 (ambThetaNu F μ) = 1 := by
  rw [coeffNu_eq_of_eval F ((mem_ambA_iff F μ _).mpr ⟨Polynomial.X, by simp⟩)
    (p := Polynomial.X) (by simp)]
  simp

/-! ## §2. Additivity -/

lemma coeffNu_add {μ : ℕ} {x y : Ambient F} (hx : x ∈ ambA F μ) (hy : y ∈ ambA F μ) (j : ℕ) :
    coeffNu F μ j (x + y) = coeffNu F μ j x + coeffNu F μ j y := by
  rw [coeffNu_eq_of_eval F (ambA_add_mem F hx hy)
      (p := Classical.choose ((mem_ambA_iff F μ x).mp hx)
        + Classical.choose ((mem_ambA_iff F μ y).mp hy)) (by
        rw [Polynomial.eval₂_add, degNu_witness F hx, degNu_witness F hy]),
    coeffNu_eq_of_eval F hx (degNu_witness F hx),
    coeffNu_eq_of_eval F hy (degNu_witness F hy)]
  rw [Polynomial.coeff_add, map_add]

/-! ## §3. Multiplicativity (convolution) -/

lemma coeffNu_mul {μ : ℕ} {x y : Ambient F} (hx : x ∈ ambA F μ) (hy : y ∈ ambA F μ) (j : ℕ) :
    coeffNu F μ j (x * y)
      = ∑ i ∈ Finset.HasAntidiagonal.antidiagonal j, coeffNu F μ i.1 x * coeffNu F μ i.2 y := by
  rw [coeffNu_eq_of_eval F (ambA_mul_mem F hx hy)
      (p := Classical.choose ((mem_ambA_iff F μ x).mp hx)
        * Classical.choose ((mem_ambA_iff F μ y).mp hy)) (by
        rw [Polynomial.eval₂_mul, degNu_witness F hx, degNu_witness F hy]),
    Polynomial.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, coeffNu_eq_of_eval F hx (degNu_witness F hx) i.1,
    coeffNu_eq_of_eval F hy (degNu_witness F hy) i.2]

/-! ## §4. ★★ The Frobenius permutation of the coefficients -/

/-- `(p.comp (X^q)).coeff (q*j) = (p.coeff j)^q` on `F` (via `Polynomial.expand`). -/
lemma comp_X_pow_card_coeff (p : Polynomial F) (j : ℕ) :
    (p.comp (Polynomial.X ^ Nat.card F)).coeff (Nat.card F * j) = (p.coeff j) ^ Nat.card F := by
  have hq : 0 < Nat.card F := Nat.pos_of_ne_zero (FrobPow.ne_zero (Ambient F) (q := Nat.card F))
  rw [← Polynomial.expand_eq_comp_X_pow,
    Polynomial.coeff_expand hq p (Nat.card F * j), if_pos ⟨j, rfl⟩,
    Nat.mul_div_cancel_left j hq, pow_card_eq (F := F) (p.coeff j)]

/-- ★★ **Frobenius permutes the `θ_μ`-coefficients**: `coeffNu μ (q·j) (x^q) = coeffNu μ j x`.
(There is no `q`-th power on the right: the coefficients of `x` already lie in `F_q`.) -/
lemma coeffNu_pow_card {μ : ℕ} {x : Ambient F} (hx : x ∈ ambA F μ) (j : ℕ) :
    coeffNu F μ (Nat.card F * j) (x ^ Nat.card F) = coeffNu F μ j x := by
  set p := Classical.choose ((mem_ambA_iff F μ x).mp hx) with hp
  have ex : p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F μ) = x := degNu_witness F hx
  calc coeffNu F μ (Nat.card F * j) (x ^ Nat.card F)
      = coeffNu F μ (Nat.card F * j)
          ((p.comp (Polynomial.X ^ Nat.card F)).eval₂ (algebraMap F (Ambient F))
            (ambThetaNu F μ)) := by
        rw [Polynomial.eval₂_comp, Polynomial.eval₂_pow, Polynomial.eval₂_X,
          eval₂_ambThetaNu_pow_card F μ p, ex]
    _ = (algebraMap F (Ambient F))
          ((p.comp (Polynomial.X ^ Nat.card F)).coeff (Nat.card F * j)) :=
        coeffNu_eq_of_eval F
          ((mem_ambA_iff F μ _).mpr ⟨p.comp (Polynomial.X ^ Nat.card F), rfl⟩) rfl
          (Nat.card F * j)
    _ = (algebraMap F (Ambient F)) ((p.coeff j) ^ Nat.card F) := by
        rw [comp_X_pow_card_coeff]
    _ = (algebraMap F (Ambient F)) (p.coeff j) := by
        rw [map_pow, algebraMap_ambient_eq, ambCoeff_pow_card F]
    _ = coeffNu F μ j x := (coeffNu_eq_of_eval F hx ex j).symm

/-! ## §5. Finiteness of the `θ_μ`-expansion -/

/-- The `θ_μ`-expansion of `x ∈ A_μ` is finite: it stops at `degNu μ x`. -/
lemma coeffNu_degNu_lt {μ : ℕ} {x : Ambient F} (hx : x ∈ ambA F μ) {j : ℕ}
    (hj : degNu F μ x < j) : coeffNu F μ j x = 0 := by
  rw [coeffNu_eq_of_eval F hx (degNu_witness F hx),
    show (Classical.choose ((mem_ambA_iff F μ x).mp hx)).coeff j = 0 from
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [← degNu_of_mem F hx]; exact hj)]
  simp

/-- ★ `x` is the sum of its `θ_μ`-coefficients times `θ_μ^j`. -/
lemma sum_coeffNu_mul_ambThetaNu (μ : ℕ) {x : Ambient F} (hx : x ∈ ambA F μ) :
    (∑ j ∈ Finset.range (degNu F μ x + 1), coeffNu F μ j x * (ambThetaNu F μ) ^ j) = x := by
  conv_rhs => rw [← degNu_witness F hx]
  rw [Polynomial.eval₂_eq_sum_range, degNu_of_mem F hx]
  exact Finset.sum_congr rfl fun j _ => by
    rw [coeffNu_eq_of_eval F hx (degNu_witness F hx) j]

/-! ## §6. The monomial shift (the atomic ingredient of any `θ_μ^N`-based definition) -/

/-- `θ_μ ∈ A_μ`. -/
lemma ambThetaNu_mem_ambA (μ : ℕ) : ambThetaNu F μ ∈ ambA F μ :=
  (mem_ambA_iff F μ _).mpr ⟨Polynomial.X, by simp⟩

/-- ★★ **The monomial shift**: multiplying by `θ_μ^N` shifts the `θ_μ`-coefficients, so
`coeffNu μ (j+N) (θ_μ^N · x) = coeffNu μ j x` for `x ∈ A_μ`.

This is the well-definedness input for defining the `θ_μ`-Laurent coefficient of `y ∈ F_q(θ_μ)` by
`coeffNu μ (j+N) (y · θ_μ^N)` (the two choices of `N` agreeing by this lemma). -/
lemma coeffNu_ambThetaNu_pow_mul {μ : ℕ} {x : Ambient F} (hx : x ∈ ambA F μ) (N j : ℕ) :
    coeffNu F μ (j + N) ((ambThetaNu F μ) ^ N * x) = coeffNu F μ j x := by
  set p := Classical.choose ((mem_ambA_iff F μ x).mp hx) with hp
  have ex : p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F μ) = x := degNu_witness F hx
  have hmem : (ambThetaNu F μ) ^ N * x ∈ ambA F μ :=
    ambA_mul_mem F (ambA_pow_mem F μ (ambThetaNu_mem_ambA F μ) N) hx
  rw [coeffNu_eq_of_eval F hmem (p := Polynomial.X ^ N * p) (by
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, ex]),
      coeffNu_eq_of_eval F hx ex j]
  congr 1
  rw [Polynomial.coeff_X_pow_mul]

/-! ## §7. ★★★ Step (1) of the level-`0` endgame: the three-term collapse -/

/-- ★★★ **The three-term collapse.**  If `x ∈ A_0 = F_q[θ]` has its `θ`-support inside `qℤ`
(`hsupp`) and `degNu 0 x = 2q` (`hdeg`), then

  `x = x_0 + x_1 · θ^q + x_2 · θ^(2q)`

with `x_j := coeffNu 0 (j*q) x`.  This is step (1) of the level-`0` endgame: it is what turns
`δ₁ ∈ F_q[θ^q][X]` with `deg_θ δ₁ = 2q` into a *three-unknown* problem. -/
lemma eq_three_terms_of_support {x : Ambient F} (hx : x ∈ ambA F 0)
    (hsupp : ∀ m, ¬ Nat.card F ∣ m → coeffNu F 0 m x = 0)
    (hdeg : degNu F 0 x = 2 * Nat.card F) :
    x = ∑ j ∈ ({0, Nat.card F, 2 * Nat.card F} : Finset ℕ),
        coeffNu F 0 j x * (ambTheta F) ^ j := by
  have hqpos : 0 < Nat.card F := Nat.pos_of_ne_zero (FrobPow.ne_zero (Ambient F) (q := Nat.card F))
  have hsum : (∑ j ∈ Finset.range (2 * Nat.card F + 1),
      coeffNu F 0 j x * (ambTheta F) ^ j) = x := by
    have h := sum_coeffNu_mul_ambThetaNu F 0 hx
    rw [hdeg, ambThetaNu_zero F] at h
    exact h
  refine hsum.symm.trans ?_
  refine (Finset.sum_subset (f := fun j => coeffNu F 0 j x * (ambTheta F) ^ j) ?_ ?_).symm
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (by omega)
  · intro j hjS hjT
    simp only [Finset.mem_range] at hjS
    by_cases hq : Nat.card F ∣ j
    · obtain ⟨k, rfl⟩ := hq
      have hk : k ≤ 2 := by nlinarith
      have hk2 : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk2 with rfl | rfl | rfl
      · exact absurd (by simp) hjT
      · exact absurd (by simp) hjT
      · exact absurd (by rw [Nat.mul_comm]; simp) hjT
    · rw [hsupp j hq, zero_mul]

/-! ## §8. The degree-`0` read (the atom of the `θ^0`-coefficient identification) -/

/-- ★ **A `θ_μ`-constant pulls out of `coeffNu` at degree `0`**: for `c` with no `θ_μ`-component
above degree `0`, `coeffNu μ j (c * y) = coeffNu μ 0 c * coeffNu μ j y`.  Specialised here to `j = 0`,
which is the step used to read the `θ^0`-coefficient of `P · (†)` in the two-term endgame
(`P, A₁, A₂` are `θ`-constants). -/
lemma coeffNu_zero_mul {μ : ℕ} {x y : Ambient F} (hx : x ∈ ambA F μ) (hy : y ∈ ambA F μ) :
    coeffNu F μ 0 (x * y) = coeffNu F μ 0 x * coeffNu F μ 0 y := by
  rw [coeffNu_mul F hx hy 0, Finset.HasAntidiagonal.antidiagonal_zero, Finset.sum_singleton]

/-- ★★ **A `θ_μ`-constant pulls out of `coeffNu`.**  If `c ∈ A_μ` has no `θ_μ`-component above
degree `0` (`hconst`), then `coeffNu μ j (c * y) = coeffNu μ 0 c * coeffNu μ j y`.  This is what the
degree-`0` and degree-`q` reads of `P · (†)` need, since `P`, `A₁`, `A₂` are `θ`-constants. -/
lemma coeffNu_mul_of_constant {μ : ℕ} {c y : Ambient F} (hc : c ∈ ambA F μ)
    (hy : y ∈ ambA F μ) (hconst : ∀ i, i ≠ 0 → coeffNu F μ i c = 0) (j : ℕ) :
    coeffNu F μ j (c * y) = coeffNu F μ 0 c * coeffNu F μ j y := by
  rw [coeffNu_mul F hc hy j]
  refine (Finset.sum_eq_single_of_mem (0, j)
    (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) fun b hb hbne => ?_).trans ?_
  · by_cases h0 : b.1 = 0
    · exfalso
      refine hbne (Prod.ext h0 ?_)
      have h1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      omega
    · rw [hconst b.1 h0, zero_mul]
  · rfl

/-- ★ **The `hconst` input**: an element of `A_μ` of `θ_μ`-degree `0` (a "`θ_μ`-constant") has no
`θ_μ`-component above degree `0`.  This is what `coeffNu_mul_of_constant` consumes for the factors
`P`, `A₁`, `A₂` of the cleared identity `P · (†)`, which are `θ`-constants. -/
lemma coeffNu_eq_zero_of_degNu_eq_zero {μ : ℕ} {c : Ambient F} (hc : c ∈ ambA F μ)
    (h0 : degNu F μ c = 0) {i : ℕ} (hi : i ≠ 0) : coeffNu F μ i c = 0 :=
  coeffNu_degNu_lt F hc (by omega)

/-- The `hconst` input for the `θ`-constants of the endgame: a coefficient-field element (e.g. any
element of `F_q[X]`, such as `P`, `A₁`, `A₂`) has no positive `θ_μ`-component. -/
lemma coeffNu_eq_zero_of_mem_ambF {μ : ℕ} {x : Ambient F} (hx : x ∈ ambF F) {i : ℕ}
    (hi : i ≠ 0) : coeffNu F μ i x = 0 :=
  coeffNu_eq_zero_of_degNu_eq_zero F
    (ambA_mono (F := F) (Nat.zero_le μ) (mem_ambA_zero_of_mem_ambF hx)) (degNu_ambF F hx) hi

/-- The coefficientwise `hconst` for the `θ`-constant *polynomials* of the endgame: if `P` has
coefficients in the coefficient field (`P = X^q - X`, `A₁`, `A₂` all do), then each of its
coefficients has no positive `θ`-component.  Applied to the `X`-coefficients of `P · (†)` this is the
`hconst` slot of `coeffNu_mul_of_constant` at the factors `P`, `A₁`, `A₂`. -/
lemma coeffNu_coeff_eq_zero_of_mem_ambF {P : Polynomial (Ambient F)}
    (hP : ∀ n, P.coeff n ∈ ambF F) {n i : ℕ} (hi : i ≠ 0) : coeffNu F 0 i (P.coeff n) = 0 :=
  coeffNu_eq_zero_of_mem_ambF F (hP n) hi

/-! ## §9. `coeffNu` over finite sums (route (i), first row) -/

/-- ★ **`coeffNu` is additive over finite sums.**  With route (i) fixed (read `coeffNu 0` on the
`X`-coefficients of `Polynomial (Ambient F)`, no fraction field), the level-`0` rows are sums over
`Finset.HasAntidiagonal.antidiagonal`, so this is the lemma that turns `coeffNu 0` of a product into a
sum of products. -/
lemma coeffNu_sum {μ : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Ambient F}
    (hf : ∀ i ∈ s, f i ∈ ambA F μ) (j : ℕ) :
    coeffNu F μ j (∑ i ∈ s, f i) = ∑ i ∈ s, coeffNu F μ j (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have ha' : f a ∈ ambA F μ := hf a (Finset.mem_insert_self a s)
      have hs' : ∀ i ∈ s, f i ∈ ambA F μ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        coeffNu_add F ha' ((ambASub F μ).sum_mem fun i hi => hs' i hi) j, ih hs']

/-- ★★ **The first level-`0` row, in atomic form**: the `θ^0`-coefficient (read coefficientwise in
`X`) of a product of two `A_0`-polynomials.  This is the pattern every row of the endgame follows —
`P · u^q`, `A₂ · L^q`, `A₁(w-q) · P · L^q` are all instances (`P`, `A₁`, `A₂` are `θ`-constants, so
their `θ^0`-coefficient is themselves). -/
lemma coeffNu_zero_coeff_mul {p y : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (hy : ∀ n, y.coeff n ∈ ambA F 0) (n : ℕ) :
    coeffNu F 0 0 ((p * y).coeff n)
      = ∑ b ∈ Finset.HasAntidiagonal.antidiagonal n,
          coeffNu F 0 0 (p.coeff b.1) * coeffNu F 0 0 (y.coeff b.2) := by
  rw [Polynomial.coeff_mul,
    coeffNu_sum F _ (fun b _ => ambA_mul_mem F (hp b.1) (hy b.2)) 0]
  exact Finset.sum_congr rfl fun b _ => coeffNu_zero_mul F (hp b.1) (hy b.2)

/-- A coefficient-field element is its own `θ_μ`-constant part. -/
lemma coeffNu_zero_of_mem_ambF {μ : ℕ} {x : Ambient F} (hx : x ∈ ambF F) :
    coeffNu F μ 0 x = x := by
  obtain ⟨a, rfl⟩ := eq_range_ambCoeff_of_mem_ambF F hx
  rw [coeffNu_eq_of_eval F
      (ambA_mono (F := F) (Nat.zero_le μ) (mem_ambA_zero_of_mem_ambF (ambCoeff_mem_ambF F a)))
      (p := Polynomial.C a) (by rw [Polynomial.eval₂_C, algebraMap_ambient_eq]) 0,
    Polynomial.coeff_C, if_pos rfl, algebraMap_ambient_eq]

/-- ★★ **The `θ`-constant factor version of the first row**: a polynomial `p` with coefficients in the
coefficient field (`P = X^q - X`, `A₁`, `A₂`) pulls out of the `θ^0`-coefficient, coefficientwise in
`X`.  This is item 1 of §«continued 24». -/
lemma coeffNu_zero_coeff_mul_of_ambF {p y : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambF F) (hy : ∀ n, y.coeff n ∈ ambA F 0) (n : ℕ) :
    coeffNu F 0 0 ((p * y).coeff n)
      = ∑ b ∈ Finset.HasAntidiagonal.antidiagonal n,
          p.coeff b.1 * coeffNu F 0 0 (y.coeff b.2) := by
  rw [coeffNu_zero_coeff_mul F (fun m => mem_ambA_zero_of_mem_ambF (hp m)) hy n]
  exact Finset.sum_congr rfl fun b _ => by rw [coeffNu_zero_of_mem_ambF F (hp b.1)]

/-- ★★★ **The `θ`-constant pull-out at every `θ`-degree `j`, coefficientwise in `X`** — i.e.
§«continued 24»'s items 1 **and** 2 in one statement.  For `P·u^q` this gives the `θ^0`-read (`j = 0`)
and the `θ^q`-read (`j = q`) with a single lemma. -/
lemma coeffNu_coeff_mul_of_ambF {p y : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambF F) (hy : ∀ n, y.coeff n ∈ ambA F 0) (j n : ℕ) :
    coeffNu F 0 j ((p * y).coeff n)
      = ∑ b ∈ Finset.HasAntidiagonal.antidiagonal n,
          p.coeff b.1 * coeffNu F 0 j (y.coeff b.2) := by
  rw [Polynomial.coeff_mul,
    coeffNu_sum F _ (fun b _ => ambA_mul_mem F (mem_ambA_zero_of_mem_ambF (hp b.1)) (hy b.2)) j]
  exact Finset.sum_congr rfl fun b _ =>
    (coeffNu_mul_of_constant F (mem_ambA_zero_of_mem_ambF (hp b.1)) (hy b.2)
      (fun i hi => coeffNu_eq_zero_of_mem_ambF F (hp b.1) hi) j).trans
      (by rw [coeffNu_zero_of_mem_ambF F (hp b.1)])

/-! ## §10. The `σ`-twin (corrected identity of §«continued 28») -/

/-- ★★★ **The `σ`-twin of the coefficient rule.**  For a polynomial `p` with `A_μ`-coefficients, the
`θ_μ`-coefficients of its coefficientwise Frobenius twist `polyTwist 1 p` are the `q`-th powers, hence
sit at `θ`-degrees scaled by `q` — with the *same* value:

  `coeffNu μ (q·j) ((polyTwist 1 p).coeff n) = coeffNu μ j (p.coeff n)`.

This is the coefficient rewrite the corrected identity `σ(δ₁) = W^w·(δ₁ + δ₂ + A₁H_w)` of
§«continued 28» needs: `σ(δ₁) = polyTwist 1 δ₁` coefficientwise, and its coefficients are recovered
from those of `δ₁` by this lemma.  Two lines: `polyTwist_one_coeff` then `coeffNu_pow_card`. -/
lemma coeffNu_polyTwist_coeff {μ : ℕ} {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F μ) (j n : ℕ) :
    coeffNu F μ (Nat.card F * j)
        ((polyTwist (q := Nat.card F) 1 p).coeff n) = coeffNu F μ j (p.coeff n) := by
  rw [polyTwist_one_coeff]
  exact coeffNu_pow_card F (hp n) j

/-- The `θ`-coefficients of a power of `θ`: `coeffNu 0 m (θ^k) = if m = k then 1 else 0`.  The atom of
the reads: every factor of `P·σ(δ₁) = P·W^w·δ₁ + W^w·(-A₂L^q + A₁P² + A₁(w-q)·P·L^q)` is a sum of
such monomials in `θ` (`W = X - C(θ^q)` and `L^q = X^q - C(θ^q)` are two-term in `θ^q`). -/
lemma coeffNu_ambTheta_pow (k m : ℕ) :
    coeffNu F 0 m ((ambTheta F) ^ k) = if m = k then 1 else 0 := by
  have hmem : (ambTheta F) ^ k ∈ ambA F 0 :=
    (mem_ambA_iff F 0 _).mpr ⟨Polynomial.X ^ k, by simp [ambThetaNu_zero F]⟩
  rw [coeffNu_eq_of_eval F hmem (p := Polynomial.X ^ k)
      (by simp [ambThetaNu_zero F]) m, Polynomial.coeff_X_pow]
  split_ifs <;> simp

end ZagierHoffmanPositiveChar
