import Submission.ZagierHoffmanProof.EndgameDeg
import Submission.ZagierHoffmanProof.AmbRootLevel

/-!
# The `θ_ν`-degree on `A_ν = F_q[θ_ν]`

`K^{perf} = ⋃_ν F_q(θ_ν)` (`AbpDescentRestrict.ratLevelF`).  The `q`-th power map sends `θ_ν` to
`θ_{ν-1}`, so at a *finite* level `ν` it *scales* `θ_ν`-degrees by `q`: that is `degNu_pow_card`
below, the engine of the "Mahler" degree analysis of the two-term endgame (Dac §6.3).

This file provides `degNu F ν` and its algebraic API.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial
open scoped WithZero

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The `θ_ν`-degree -/

/-- The `θ_ν`-degree of an element of `A_ν = F_q[θ_ν]` (and `0` outside). -/
noncomputable def degNu (ν : ℕ) (x : Ambient F) : ℕ := by
  classical
  exact if h : x ∈ ambA F ν then (Classical.choose ((mem_ambA_iff F ν x).mp h)).natDegree else 0

lemma degNu_of_mem {ν : ℕ} {x : Ambient F} (hx : x ∈ ambA F ν) :
    degNu F ν x = (Classical.choose ((mem_ambA_iff F ν x).mp hx)).natDegree :=
  dif_pos hx

/-- The witnessing polynomial evaluates to `x`. -/
lemma degNu_witness {ν : ℕ} {x : Ambient F} (hx : x ∈ ambA F ν) :
    (Classical.choose ((mem_ambA_iff F ν x).mp hx)).eval₂ (algebraMap F (Ambient F))
      (ambThetaNu F ν) = x :=
  Classical.choose_spec ((mem_ambA_iff F ν x).mp hx)

/-- `degNu` computed from any witnessing polynomial. -/
lemma degNu_eq_of_eval {ν : ℕ} {x : Ambient F} (hx : x ∈ ambA F ν) {p : Polynomial F}
    (hp : p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = x) :
    degNu F ν x = p.natDegree := by
  rw [degNu_of_mem F hx]
  congr 1
  refine sub_eq_zero.mp (ambThetaNu_transcendental F ν _ ?_)
  rw [Polynomial.eval₂_sub, hp, degNu_witness F hx, sub_self]

@[simp] lemma degNu_zero (ν : ℕ) : degNu F ν (0 : Ambient F) = 0 := by
  rw [degNu_eq_of_eval F (ν := ν) ((ambASub F ν).zero_mem) (p := 0) (by simp)]
  simp

@[simp] lemma degNu_one (ν : ℕ) : degNu F ν (1 : Ambient F) = 0 := by
  rw [degNu_eq_of_eval F (ν := ν) ((ambASub F ν).one_mem) (p := 1) (by simp)]
  simp

lemma degNu_ambThetaNu (ν : ℕ) : degNu F ν (ambThetaNu F ν) = 1 := by
  rw [degNu_eq_of_eval F (ν := ν)
      ((mem_ambA_iff F ν _).mpr ⟨Polynomial.X, by simp⟩) (p := Polynomial.X) (by simp)]
  simp

/-- `deg_ν θ = q ^ ν` (`θ = θ_ν ^ (q^ν)`). -/
lemma degNu_ambTheta (ν : ℕ) : degNu F ν (ambTheta F) = Nat.card F ^ ν := by
  rw [← ambThetaNu_pow F ν]
  rw [degNu_eq_of_eval F (ν := ν)
      ((mem_ambA_iff F ν _).mpr ⟨Polynomial.X ^ (Nat.card F ^ ν), by simp⟩)
      (p := Polynomial.X ^ (Nat.card F ^ ν)) (by simp)]
  simp

/-- Elements of the coefficient field have `θ_ν`-degree `0`. -/
lemma degNu_ambF {ν : ℕ} {c : Ambient F} (hc : c ∈ ambF F) : degNu F ν c = 0 := by
  obtain ⟨a, rfl⟩ := eq_range_ambCoeff_of_mem_ambF F hc
  rw [degNu_eq_of_eval F (ν := ν)
      ((mem_ambA_iff F ν _).mpr ⟨Polynomial.C a,
        by rw [Polynomial.eval₂_C, algebraMap_ambient_eq]⟩)
      (p := Polynomial.C a) (by rw [Polynomial.eval₂_C, algebraMap_ambient_eq])]
  simp

/-! ## §2. Additivity/subadditivity and multiplicativity -/

lemma degNu_add_le {ν : ℕ} {x y : Ambient F} (hx : x ∈ ambA F ν) (hy : y ∈ ambA F ν) :
    degNu F ν (x + y) ≤ max (degNu F ν x) (degNu F ν y) := by
  set px := Classical.choose ((mem_ambA_iff F ν x).mp hx) with hpx
  set py := Classical.choose ((mem_ambA_iff F ν y).mp hy) with hpy
  have ex : px.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = x := degNu_witness F hx
  have ey : py.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = y := degNu_witness F hy
  have hxy : (px + py).eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = x + y := by
    rw [Polynomial.eval₂_add, ex, ey]
  have h1 : degNu F ν (x + y) = (px + py).natDegree := degNu_eq_of_eval F (ambA_add_mem F hx hy) hxy
  have h2 : degNu F ν x = px.natDegree := degNu_eq_of_eval F hx ex
  have h3 : degNu F ν y = py.natDegree := degNu_eq_of_eval F hy ey
  rw [h1, h2, h3]
  exact Polynomial.natDegree_add_le px py

lemma degNu_mul {ν : ℕ} {x y : Ambient F} (hx : x ∈ ambA F ν) (hy : y ∈ ambA F ν)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    degNu F ν (x * y) = degNu F ν x + degNu F ν y := by
  set px := Classical.choose ((mem_ambA_iff F ν x).mp hx) with hpx
  set py := Classical.choose ((mem_ambA_iff F ν y).mp hy) with hpy
  have ex : px.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = x := degNu_witness F hx
  have ey : py.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = y := degNu_witness F hy
  have hpx0 : px ≠ 0 := fun h => hx0 (by rw [← ex, h, Polynomial.eval₂_zero])
  have hpy0 : py ≠ 0 := fun h => hy0 (by rw [← ey, h, Polynomial.eval₂_zero])
  have hxy : (px * py).eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = x * y := by
    rw [Polynomial.eval₂_mul, ex, ey]
  have h1 : degNu F ν (x * y) = (px * py).natDegree := degNu_eq_of_eval F (ambA_mul_mem F hx hy) hxy
  have h2 : degNu F ν x = px.natDegree := degNu_eq_of_eval F hx ex
  have h3 : degNu F ν y = py.natDegree := degNu_eq_of_eval F hy ey
  rw [h1, h2, h3, Polynomial.natDegree_mul hpx0 hpy0]

/-! ## §2b. The level-`ν` to level-`0` transport -/

/-- `(p(θ_ν)) ^ (q^ν) = p(θ)` (Freshman's dream plus `θ_ν ^ (q^ν) = θ`). -/
lemma eval₂_ambThetaNu_pow_pow_card (ν : ℕ) (p : Polynomial F) :
    (p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν)) ^ (Nat.card F ^ ν)
      = p.eval₂ (algebraMap F (Ambient F)) (ambTheta F) := by
  have h1 : ∀ i : ℕ, ((ambThetaNu F ν) ^ i) ^ (Nat.card F ^ ν) = (ambTheta F) ^ i := by
    intro i
    calc ((ambThetaNu F ν) ^ i) ^ (Nat.card F ^ ν)
        = ((ambThetaNu F ν) ^ (Nat.card F ^ ν)) ^ i := by
          rw [← pow_mul, ← pow_mul]; exact congrArg _ (Nat.mul_comm i (Nat.card F ^ ν))
      _ = (ambTheta F) ^ i := by rw [ambThetaNu_pow F ν]
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range,
    FrobPow.sum_pow (R := Ambient F) (Finset.range (p.natDegree + 1)) _ ν]
  exact Finset.sum_congr rfl fun i _ => by
    rw [mul_pow, h1 i, algebraMap_ambient_eq, ambCoeff_pow_pow F ν (p.coeff i)]

/-- ★★ The `q^ν`-power map sends `A_ν = F_q[θ_ν]` *into* `A_0 = F_q[θ]`: if `x = p(θ_ν)` then
`x ^ (q^ν) = p(θ)`. -/
lemma ambA_pow_pow_card_mem {ν : ℕ} {x : Ambient F} (hx : x ∈ ambA F ν) :
    x ^ (Nat.card F ^ ν) ∈ ambA F 0 := by
  obtain ⟨p, rfl⟩ := (mem_ambA_iff F ν x).mp hx
  rw [eval₂_ambThetaNu_pow_pow_card F ν p]
  exact (mem_ambA_iff F 0 _).mpr ⟨p, rfl⟩

/-- **The level comparison**: the `θ`-degree of the `q^ν`-th power of an element of `A_ν` is its
`θ_ν`-degree. -/
lemma degNu_eq_degTheta_pow {ν : ℕ} {x : Ambient F} (hx : x ∈ ambA F ν) :
    degNu F ν x = degTheta F (x ^ (Nat.card F ^ ν)) := by
  obtain ⟨p, rfl⟩ := (mem_ambA_iff F ν x).mp hx
  have hmemν : p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) ∈ ambA F ν :=
    (mem_ambA_iff F ν _).mpr ⟨p, rfl⟩
  have hmem0 : p.eval₂ (algebraMap F (Ambient F)) (ambTheta F) ∈ ambA F 0 :=
    (mem_ambA_iff F 0 _).mpr ⟨p, rfl⟩
  rw [degNu_eq_of_eval F hmemν rfl, eval₂_ambThetaNu_pow_pow_card F ν p,
    degTheta_eq_of_eval F hmem0 rfl]

/-! ## §3. The Frobenius scaling -/

/-- `(p(θ_ν))^q = (p.comp (X^q))(θ_ν)`, i.e. substituting `X ↦ X^q` and evaluating at `θ_ν`. -/
lemma eval₂_ambThetaNu_pow_card (ν : ℕ) (p : Polynomial F) :
    p.eval₂ (algebraMap F (Ambient F)) ((ambThetaNu F ν) ^ Nat.card F)
      = (p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν)) ^ Nat.card F := by
  have hFrob : FrobPow (Ambient F) (Nat.card F) := frobPow_ambient F
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range,
    FrobPow.sum_pow_finset (R := Ambient F)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hq : (ambCoeff F (p.coeff i)) ^ Nat.card F = ambCoeff F (p.coeff i) := ambCoeff_pow_card F _
  simp only [algebraMap_ambient_eq]
  rw [mul_pow, ← pow_mul, ← pow_mul, hq, Nat.mul_comm i (Nat.card F)]

/-- ★★ **The Frobenius scaling of the `θ_ν`-degree**: `deg_ν (x^q) = q · deg_ν x`. -/
lemma degNu_pow_card {ν : ℕ} {x : Ambient F} (hx : x ∈ ambA F ν) :
    degNu F ν (x ^ Nat.card F) = Nat.card F * degNu F ν x := by
  set p := Classical.choose ((mem_ambA_iff F ν x).mp hx) with hp
  have ex : p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) = x := degNu_witness F hx
  have hmem : x ^ Nat.card F ∈ ambA F ν :=
    (mem_ambA_iff F ν _).mpr ⟨p.comp (Polynomial.X ^ Nat.card F), by
      rw [Polynomial.eval₂_comp, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        eval₂_ambThetaNu_pow_card F ν p, ex]⟩
  have hcomp : (p.comp (Polynomial.X ^ Nat.card F)).eval₂ (algebraMap F (Ambient F))
      (ambThetaNu F ν) = x ^ Nat.card F := by
    rw [Polynomial.eval₂_comp, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      eval₂_ambThetaNu_pow_card F ν p, ex]
  rw [degNu_eq_of_eval F hmem hcomp, degNu_eq_of_eval F hx ex,
    Polynomial.natDegree_comp, Polynomial.natDegree_X_pow]
  exact Nat.mul_comm _ _

/-! ## §4. The `ν`-fold twist and the level-`ν` polynomial degree -/

/-- The `ν`-fold Frobenius twist of a polynomial (coefficientwise `q^ν`-th power). -/
noncomputable def twNu (ν : ℕ) (p : Polynomial (Ambient F)) : Polynomial (Ambient F) :=
  (polyTwist (q := Nat.card F) 1)^[ν] p

lemma twNu_succ (ν : ℕ) (p : Polynomial (Ambient F)) :
    twNu F (ν + 1) p = polyTwist (q := Nat.card F) 1 (twNu F ν p) := by
  rw [twNu, Function.iterate_succ_apply', twNu]

@[simp] lemma twNu_coeff (ν : ℕ) (p : Polynomial (Ambient F)) (n : ℕ) :
    (twNu F ν p).coeff n = (p.coeff n) ^ (Nat.card F ^ ν) := by
  induction ν with
  | zero => simp [twNu]
  | succ ν ih =>
      rw [show ν + 1 = ν.succ from rfl, twNu_succ, polyTwist_one_coeff, ih, ← pow_mul,
        pow_succ]


lemma twNu_coeff_mem_ambA0 {ν : ℕ} {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) : ∀ n, (twNu F ν p).coeff n ∈ ambA F 0 := by
  intro n
  rw [twNu_coeff]
  exact ambA_pow_pow_card_mem F (hp n)

/-- The level-`ν` `θ`-degree of a polynomial: the maximum of the `θ_ν`-degrees of its
coefficients (equal to the level-`0` degree of its `ν`-fold twist). -/
noncomputable def degPolyNu (ν : ℕ) (p : Polynomial (Ambient F)) : ℕ := degPoly F (twNu F ν p)

lemma degPolyNu_le_iff {ν : ℕ} {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) {m : ℕ} :
    degPolyNu F ν p ≤ m ↔ ∀ n, degNu F ν (p.coeff n) ≤ m := by
  rw [degPolyNu, degPoly_le_iff' F]
  refine forall_congr' fun n => ?_
  rw [twNu_coeff, degNu_eq_degTheta_pow F (hp n)]

lemma degPolyNu_le_of_coeff_le {ν : ℕ} {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) {m : ℕ} (h : ∀ n, degNu F ν (p.coeff n) ≤ m) :
    degPolyNu F ν p ≤ m := (degPolyNu_le_iff F hp).mpr h

lemma degPolyNu_coeff_le {ν : ℕ} {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) (n : ℕ) :
    degNu F ν (p.coeff n) ≤ degPolyNu F ν p :=
  (degPolyNu_le_iff F hp).mp le_rfl n

@[simp] lemma twNu_zero (ν : ℕ) :
    twNu F ν (0 : Polynomial (Ambient F)) = 0 := by
  induction ν with
  | zero => simp [twNu]
  | succ ν ih => rw [twNu_succ, ih]; exact map_zero _

@[simp] lemma degPolyNu_zero (ν : ℕ) : degPolyNu F ν (0 : Polynomial (Ambient F)) = 0 := by
  rw [degPolyNu, twNu_zero, degPoly_zero]

lemma degPolyNu_add_le {ν : ℕ} {p q : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F ν) (hq : ∀ n, q.coeff n ∈ ambA F ν) :
    degPolyNu F ν (p + q) ≤ max (degPolyNu F ν p) (degPolyNu F ν q) := by
  refine degPolyNu_le_of_coeff_le F (fun n => ?_) fun n => ?_
  · rw [Polynomial.coeff_add]; exact ambA_add_mem F (hp n) (hq n)
  · rw [Polynomial.coeff_add]
    exact le_trans (degNu_add_le F (hp n) (hq n))
      (max_le_max (degPolyNu_coeff_le F hp n) (degPolyNu_coeff_le F hq n))


/-! ## §5. Elementary `degNu` facts used by the endgame -/

lemma degNu_neg {ν : ℕ} {x : Ambient F} (hx : x ∈ ambA F ν) :
    degNu F ν (-x) = degNu F ν x := by
  rw [degNu_eq_of_eval F ((ambASub F ν).neg_mem hx)
      (p := -Classical.choose ((mem_ambA_iff F ν x).mp hx)) (by
        rw [Polynomial.eval₂_neg, degNu_witness F hx]),
    degNu_eq_of_eval F hx (degNu_witness F hx)]
  simp

/-- `θ ∈ A_ν` (`θ = θ_ν ^ (q^ν)`). -/
lemma ambTheta_mem_ambA (ν : ℕ) : ambTheta F ∈ ambA F ν :=
  (mem_ambA_iff F ν _).mpr ⟨Polynomial.X ^ (Nat.card F ^ ν), by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X, ambThetaNu_pow F ν]⟩

/-- `θ_ν ^ (q^(ν+1)) = θ ^ q`. -/
lemma ambThetaNu_pow_succ (ν : ℕ) :
    (ambThetaNu F ν) ^ (Nat.card F ^ (ν + 1)) = (ambTheta F) ^ Nat.card F := by
  rw [pow_succ, pow_mul, ambThetaNu_pow]

lemma degNu_theta_pow_card (ν : ℕ) :
    degNu F ν ((ambTheta F) ^ Nat.card F) = Nat.card F ^ (ν + 1) := by
  rw [← ambThetaNu_pow_succ F ν]
  rw [degNu_eq_of_eval F (ν := ν)
      ((mem_ambA_iff F ν _).mpr ⟨Polynomial.X ^ (Nat.card F ^ (ν + 1)), by simp⟩)
      (p := Polynomial.X ^ (Nat.card F ^ (ν + 1))) (by simp)]
  simp

lemma degPolyNu_C {ν : ℕ} {a : Ambient F} (ha : a ∈ ambA F ν) :
    degPolyNu F ν (Polynomial.C a) = degNu F ν a := by
  have hmem : ∀ n, (Polynomial.C a : Polynomial (Ambient F)).coeff n ∈ ambA F ν := by
    intro n
    rw [Polynomial.coeff_C]
    split_ifs with h
    · simpa [h] using ha
    · exact ambA_zero_mem ν
  have hbound : ∀ n, degNu F ν ((Polynomial.C a : Polynomial (Ambient F)).coeff n)
      ≤ degNu F ν a := by
    intro n
    rw [Polynomial.coeff_C]
    split_ifs with h
    · simpa [h] using le_rfl
    · rw [degNu_zero]; exact Nat.zero_le _
  have h0 : (Polynomial.C a : Polynomial (Ambient F)).coeff 0 = a := by
    rw [Polynomial.coeff_C, if_pos rfl]
  refine le_antisymm (degPolyNu_le_of_coeff_le F hmem hbound) ?_
  calc degNu F ν a = degNu F ν ((Polynomial.C a : Polynomial (Ambient F)).coeff 0) := by rw [h0]
    _ ≤ degPolyNu F ν (Polynomial.C a) := degPolyNu_coeff_le F hmem 0

/-- The coefficient family of `X - C(θ^q)` lies in `A_ν`. -/
lemma coeff_mem_ambA_X_sub_C_theta_pow (ν : ℕ) :
    ∀ n, (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)).coeff n ∈ ambA F ν := by
  intro n
  rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  refine (ambASub F ν).sub_mem ?_ ?_
  · split_ifs with h; exacts [ambA_one_mem F ν, ambA_zero_mem ν]
  · split_ifs with h
    · exact ambA_pow_mem F ν (ambTheta_mem_ambA F ν) (Nat.card F)
    · exact ambA_zero_mem ν

/-- ★ `deg_ν (X - C(θ^q)) = q^(ν+1)` — the level-`ν` degree of `W`. -/
lemma degPolyNu_X_sub_C_theta_pow (ν : ℕ) :
    degPolyNu F ν (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F))
      = Nat.card F ^ (ν + 1) := by
  have hmem := coeff_mem_ambA_X_sub_C_theta_pow F ν
  have hpow : (ambTheta F) ^ Nat.card F ∈ ambA F ν :=
    ambA_pow_mem F ν (ambTheta_mem_ambA F ν) (Nat.card F)
  have hq : degNu F ν ((ambTheta F) ^ Nat.card F) = Nat.card F ^ (ν + 1) :=
    degNu_theta_pow_card F ν
  refine le_antisymm (degPolyNu_le_of_coeff_le F hmem fun n => ?_) ?_
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    by_cases h1 : (1 : ℕ) = n
    · rw [if_pos h1]
      by_cases h0 : n = 0
      · rw [if_pos h0, sub_eq_add_neg]
        refine le_trans (degNu_add_le F ((ambASub F ν).one_mem) ((ambASub F ν).neg_mem hpow)) ?_
        rw [degNu_neg F hpow, hq, degNu_one]
        exact max_le (Nat.zero_le _) le_rfl
      · rw [if_neg h0, sub_zero, degNu_one]; exact Nat.zero_le _
    · rw [if_neg h1, zero_sub]
      by_cases h0 : n = 0
      · rw [if_pos h0, degNu_neg F hpow, hq]
      · rw [if_neg h0, neg_zero, degNu_zero]; exact Nat.zero_le _
  · have h0 : (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) :
        Polynomial (Ambient F)).coeff 0 = -((ambTheta F) ^ Nat.card F) := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C,
        if_neg (by norm_num : ¬ (1 : ℕ) = 0), if_pos rfl, zero_sub]
    calc Nat.card F ^ (ν + 1)
        = degNu F ν (-((ambTheta F) ^ Nat.card F)) := by rw [degNu_neg F hpow, hq]
      _ = degNu F ν ((Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)).coeff 0) := by
          rw [h0]
      _ ≤ degPolyNu F ν (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) :=
          degPolyNu_coeff_le F hmem 0

end ZagierHoffmanPositiveChar