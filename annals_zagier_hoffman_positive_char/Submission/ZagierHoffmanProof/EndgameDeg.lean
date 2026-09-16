import Submission.ZagierHoffmanProof.Endgame2
import Submission.ZagierHoffmanProof.DegTheta
import Submission.ZagierHoffmanProof.Solve64
import Submission.ZagierHoffmanProof.HDatum

/-!
# The `θ`-degree of a polynomial over `F_q[θ]`, and the degree estimate of the two-term endgame

`degTheta F x` is the `θ`-degree of an element `x ∈ ambA F 0 = F_q[θ]` (`DegTheta.lean`).
Here we extend it to `degPoly F p`, the maximum of the `θ`-degrees of the coefficients of a
polynomial `p ∈ Ambient F[X]` whose coefficients all lie in `ambA F 0`.  This is the "degree in
`θ`" of the bivariate object `p`, and it satisfies the two structural rules

* `degPoly (p * q) = degPoly p + degPoly q`,
* `degPoly (polyTwist 1 p) = Nat.card F * degPoly p`,

which are what the θ-degree comparison of the two-term endgame (ND21 §6, IMKDP §3.3) needs.

`degQ F u Q = degPoly F u - degPoly F Q` is the corresponding degree of the rational function
`u / Q`, which is what makes the comparison of an equation `σ(y) = (X - θ)^w y + …` with
denominators meaningful.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial
open scoped WithZero

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The `θ`-degree of a polynomial with `F_q[θ]`-coefficients -/

/-- The `θ`-degree of a polynomial: the maximum of the `θ`-degrees of its coefficients. -/
noncomputable def degPoly (p : Polynomial (Ambient F)) : ℕ :=
  p.support.sup (fun n => degTheta F (p.coeff n))

lemma degPoly_le_iff {p : Polynomial (Ambient F)} {m : ℕ} :
    degPoly F p ≤ m ↔ ∀ n ∈ p.support, degTheta F (p.coeff n) ≤ m :=
  Finset.sup_le_iff

lemma degPoly_le_of_coeff_le {p : Polynomial (Ambient F)} {m : ℕ}
    (h : ∀ n, degTheta F (p.coeff n) ≤ m) : degPoly F p ≤ m := by
  rw [degPoly_le_iff]
  intro n _
  exact h n

lemma degPoly_coeff_le (p : Polynomial (Ambient F)) (n : ℕ) :
    degTheta F (p.coeff n) ≤ degPoly F p := by
  rcases eq_or_ne (p.coeff n) 0 with h | h
  · rw [h, degTheta_zero]; exact Nat.zero_le _
  · exact Finset.le_sup (f := fun n => degTheta F (p.coeff n))
      (Polynomial.mem_support_iff.mpr h)

@[simp] lemma degPoly_zero : degPoly F (0 : Polynomial (Ambient F)) = 0 := by
  simp [degPoly]

lemma degPoly_le_iff' {p : Polynomial (Ambient F)} {m : ℕ} :
    degPoly F p ≤ m ↔ ∀ n, degTheta F (p.coeff n) ≤ m := by
  constructor
  · intro h n
    rcases eq_or_ne (p.coeff n) 0 with h0 | h0
    · rw [h0, degTheta_zero]; exact Nat.zero_le _
    · exact (degPoly_le_iff F).mp h n (Polynomial.mem_support_iff.mpr h0)
  · intro h; exact degPoly_le_of_coeff_le F h

/-! ### §1a. An index attaining the maximum, chosen as large as possible -/

lemma exists_degPoly_eq (p : Polynomial (Ambient F)) (h0 : p ≠ 0) :
    ∃ n ∈ p.support, degTheta F (p.coeff n) = degPoly F p := by
  have hne : p.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact h0 (Polynomial.support_eq_empty.mp h)
  obtain ⟨n, hn, hmax⟩ :=
    Finset.exists_max_image p.support (fun n => degTheta F (p.coeff n)) hne
  refine ⟨n, hn, le_antisymm (Finset.le_sup (f := fun n => degTheta F (p.coeff n)) hn) ?_⟩
  rw [degPoly, Finset.sup_le_iff]
  intro m hm
  exact hmax m hm

/-- An index attaining `degPoly`, chosen to be the largest such index. -/
lemma exists_degPoly_max_idx (p : Polynomial (Ambient F)) (h0 : p ≠ 0) :
    ∃ n ∈ p.support, degTheta F (p.coeff n) = degPoly F p ∧
      ∀ m ∈ p.support, degTheta F (p.coeff m) = degPoly F p → m ≤ n := by
  classical
  set T := p.support.filter (fun m => degTheta F (p.coeff m) = degPoly F p) with hT
  have hne : T.Nonempty := by
    obtain ⟨n, hn, he⟩ := exists_degPoly_eq F p h0
    exact ⟨n, Finset.mem_filter.mpr ⟨hn, he⟩⟩
  refine ⟨T.max' hne, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (T.max'_mem hne)).1
  · exact (Finset.mem_filter.mp (T.max'_mem hne)).2
  · intro m hm hme
    exact Finset.le_max' T m (Finset.mem_filter.mpr ⟨hm, hme⟩)

/-- Strict decay of `degTheta` past the largest maximising index. -/
lemma degTheta_lt_degPoly_of_lt_max {p : Polynomial (Ambient F)} {h0 : p ≠ 0}
    {n : ℕ} (hn : ∀ m ∈ p.support, degTheta F (p.coeff m) = degPoly F p → m ≤ n)
    {m : ℕ} (hm : m ∈ p.support) (hmn : n < m) :
    degTheta F (p.coeff m) < degPoly F p := by
  rcases lt_or_eq_of_le (degPoly_coeff_le F p m) with h | h
  · exact h
  · exact absurd (hn m hm h) (by omega)

/-! ### §1b. Additivity -/

/-- A sum whose second summand has strictly smaller `θ`-degree has the `θ`-degree of the first. -/
lemma degTheta_add_of_lt {x y : Ambient F} (hx : x ∈ ambA F 0) (hy : y ∈ ambA F 0)
    (h : degTheta F y < degTheta F x) : degTheta F (x + y) = degTheta F x := by
  set px := Classical.choose ((mem_ambA_iff F 0 x).mp hx) with hpx
  set py := Classical.choose ((mem_ambA_iff F 0 y).mp hy) with hpy
  have ex : px.eval₂ (algebraMap F (Ambient F)) (ambTheta F) = x := degTheta_witness F hx
  have ey : py.eval₂ (algebraMap F (Ambient F)) (ambTheta F) = y := degTheta_witness F hy
  have hxy : (px + py).eval₂ (algebraMap F (Ambient F)) (ambTheta F) = x + y := by
    rw [Polynomial.eval₂_add, ex, ey]
  have hlt : py.natDegree < px.natDegree := by
    rw [← degTheta_eq_of_eval F hy ey, ← degTheta_eq_of_eval F hx ex]
    exact h
  rw [degTheta_eq_of_eval F (ambA_add_mem F hx hy) hxy,
    degTheta_eq_of_eval F hx ex, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt]

lemma degPoly_add_le (p q : Polynomial (Ambient F))
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (hq : ∀ n, q.coeff n ∈ ambA F 0) :
    degPoly F (p + q) ≤ max (degPoly F p) (degPoly F q) := by
  refine degPoly_le_of_coeff_le F fun n => ?_
  rw [Polynomial.coeff_add]
  rcases eq_or_ne (p.coeff n) 0 with h | h
  · rw [h, zero_add]; exact le_trans (degPoly_coeff_le F q n) (le_max_right _ _)
  rcases eq_or_ne (q.coeff n) 0 with h' | h'
  · rw [h', add_zero]; exact le_trans (degPoly_coeff_le F p n) (le_max_left _ _)
  · exact le_trans (degTheta_add_le F (hp n) (hq n))
      (max_le_max (degPoly_coeff_le F p n) (degPoly_coeff_le F q n))

lemma degPoly_add_of_lt (p q : Polynomial (Ambient F))
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (hq : ∀ n, q.coeff n ∈ ambA F 0)
    (hp0 : p ≠ 0) (h : degPoly F q < degPoly F p) :
    degPoly F (p + q) = degPoly F p := by
  refine le_antisymm ?_ ?_
  · refine le_trans (degPoly_add_le F p q hp hq) ?_
    rw [max_eq_left (le_of_lt h)]
  · obtain ⟨n, hn, hne, -⟩ := exists_degPoly_max_idx F p hp0
    have hpn : p.coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
    have hqn : degTheta F (q.coeff n) < degTheta F (p.coeff n) := by
      rw [hne]; exact lt_of_le_of_lt (degPoly_coeff_le F q n) h
    have hcoe : (p + q).coeff n = p.coeff n + q.coeff n := Polynomial.coeff_add p q n
    have heq : degTheta F ((p + q).coeff n) = degPoly F p := by
      rw [hcoe, degTheta_add_of_lt F (hp n) (hq n) hqn, hne]
    rw [← heq]
    exact degPoly_coeff_le F (p + q) n

/-! ### §1c. Multiplicativity -/

lemma degPoly_mul_le (p q : Polynomial (Ambient F))
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (hq : ∀ n, q.coeff n ∈ ambA F 0) :
    degPoly F (p * q) ≤ degPoly F p + degPoly F q :=
  degPoly_le_of_coeff_le F fun n =>
    degTheta_coeff_mul_le F hp hq (D := degPoly F p) (E := degPoly F q)
      (fun _ => degPoly_coeff_le F p _) (fun _ => degPoly_coeff_le F q _) n


/-! ### §1d. The Frobenius twist -/

lemma polyTwist_one_coeff (p : Polynomial (Ambient F)) (n : ℕ) :
    (polyTwist (q := Nat.card F) 1 p).coeff n = (p.coeff n) ^ Nat.card F := by
  rw [polyTwist, polyTwistHom_apply, Polynomial.coeff_map, frobPowHom_apply, pow_one]

lemma polyTwist_one_fixed (p : Polynomial (Ambient F)) (hp : ∀ n, p.coeff n ∈ ambF F) :
    polyTwist (q := Nat.card F) 1 p = p := (polyTwist_one_eq_self_iff F p).mpr hp

lemma degPoly_polyTwist (p : Polynomial (Ambient F)) (hp : ∀ n, p.coeff n ∈ ambA F 0) :
    degPoly F (polyTwist (q := Nat.card F) 1 p) = Nat.card F * degPoly F p := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [show polyTwist (q := Nat.card F) 1 (0 : Polynomial (Ambient F)) = 0 from map_zero _]
    simp
  refine le_antisymm ?_ ?_
  · refine degPoly_le_of_coeff_le F fun n => ?_
    rw [polyTwist_one_coeff]
    calc degTheta F ((p.coeff n) ^ Nat.card F)
        = Nat.card F * degTheta F (p.coeff n) := degTheta_pow_card F (hp n)
      _ ≤ Nat.card F * degPoly F p := Nat.mul_le_mul_left _ (degPoly_coeff_le F p n)
  · obtain ⟨n, hn, hne, -⟩ := exists_degPoly_max_idx F p hp0
    have h := degPoly_coeff_le F (polyTwist (q := Nat.card F) 1 p) n
    rw [polyTwist_one_coeff, degTheta_pow_card F (hp n), hne] at h
    exact h

/-! ### §1e. Values at explicit polynomials -/

lemma degPoly_C {x : Ambient F} (hx : x ∈ ambA F 0) :
    degPoly F (Polynomial.C x) = degTheta F x := by
  refine le_antisymm ?_ ?_
  · rw [degPoly_le_iff']
    intro n
    rw [Polynomial.coeff_C]
    split_ifs with h
    · subst h; exact le_rfl
    · rw [degTheta_zero]; exact Nat.zero_le _
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · have hmem : (0 : ℕ) ∈ (Polynomial.C x : Polynomial (Ambient F)).support := by
        rw [Polynomial.mem_support_iff, Polynomial.coeff_C_zero]; exact hx0
      calc degTheta F x = degTheta F ((Polynomial.C x : Polynomial (Ambient F)).coeff 0) := by
              rw [Polynomial.coeff_C_zero]
        _ ≤ degPoly F (Polynomial.C x) := degPoly_coeff_le F _ 0

lemma coeff_X_sub_C (a : Ambient F) (n : ℕ) :
    (Polynomial.X - Polynomial.C a : Polynomial (Ambient F)).coeff n
      = (if (1 : ℕ) = n then 1 else 0) - (if n = 0 then a else 0) := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]

lemma degPoly_X_sub_C {a : Ambient F} (ha : a ∈ ambA F 0) :
    degPoly F (Polynomial.X - Polynomial.C a) = degTheta F a := by
  refine le_antisymm ?_ ?_
  · refine degPoly_le_of_coeff_le F fun n => ?_
    rw [coeff_X_sub_C]
    rcases eq_or_ne (1 : ℕ) n with h1 | h1
    · subst h1
      rw [if_pos rfl, if_neg (by omega : ¬ (1 : ℕ) = 0), sub_zero, degTheta_one] <;>
        exact Nat.zero_le _
    · rw [if_neg h1]
      rcases eq_or_ne n 0 with h0 | h0
      · subst h0
        rw [if_pos rfl, zero_sub, degTheta_neg F ha] <;> exact le_rfl
      · rw [if_neg h0, sub_zero, degTheta_zero] <;> exact Nat.zero_le _
  · have h0 : (Polynomial.X - Polynomial.C a : Polynomial (Ambient F)).coeff 0 = -a := by
      rw [coeff_X_sub_C, if_neg (by omega : ¬ (1 : ℕ) = 0), if_pos rfl, zero_sub]
    calc degTheta F a = degTheta F (-a) := (degTheta_neg F ha).symm
      _ = degTheta F ((Polynomial.X - Polynomial.C a : Polynomial (Ambient F)).coeff 0) := by
            rw [h0]
      _ ≤ degPoly F _ := degPoly_coeff_le F _ 0

lemma degPoly_X_pow_sub_X (hq : 2 ≤ Nat.card F) :
    degPoly F (Polynomial.X ^ Nat.card F - Polynomial.X) = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  refine degPoly_le_of_coeff_le F fun n => ?_
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  rcases eq_or_ne n (Nat.card F) with h | h
  · subst h
    rw [if_pos rfl, if_neg (by omega : ¬ (1 : ℕ) = Nat.card F), sub_zero, degTheta_one] <;>
      exact Nat.zero_le _
  · rw [if_neg h]
    rcases eq_or_ne (1 : ℕ) n with h1 | h1
    · subst h1
      rw [if_pos rfl, zero_sub, degTheta_neg F (ambA_one_mem F 0), degTheta_one] <;>
        exact Nat.zero_le _
    · rw [if_neg h1, sub_zero, degTheta_zero] <;> exact Nat.zero_le _

/-! ### §1f. Coefficient memberships -/

lemma coeff_mem_ambA_zero_C {x : Ambient F} (hx : x ∈ ambA F 0) (n : ℕ) :
    (Polynomial.C x : Polynomial (Ambient F)).coeff n ∈ ambA F 0 := by
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hx
  · exact (ambASub F 0).zero_mem

lemma coeff_mem_ambA_zero_add {p q : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (hq : ∀ n, q.coeff n ∈ ambA F 0) (n : ℕ) :
    (p + q).coeff n ∈ ambA F 0 := by
  rw [Polynomial.coeff_add]; exact (ambASub F 0).add_mem (hp n) (hq n)

lemma coeff_mem_ambA_zero_sub {p q : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (hq : ∀ n, q.coeff n ∈ ambA F 0) (n : ℕ) :
    (p - q).coeff n ∈ ambA F 0 := by
  rw [Polynomial.coeff_sub]; exact (ambASub F 0).sub_mem (hp n) (hq n)

lemma coeff_mem_ambA_zero_mul {p q : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (hq : ∀ n, q.coeff n ∈ ambA F 0) (n : ℕ) :
    (p * q).coeff n ∈ ambA F 0 := by
  rw [Polynomial.coeff_mul]
  exact (ambASub F 0).sum_mem fun x _ => ambA_mul_mem F (hp x.1) (hq x.2)

lemma coeff_mem_ambA_zero_C_mul {c : Ambient F} (hc : c ∈ ambA F 0)
    {p : Polynomial (Ambient F)} (hp : ∀ n, p.coeff n ∈ ambA F 0) (n : ℕ) :
    (Polynomial.C c * p).coeff n ∈ ambA F 0 := by
  rw [Polynomial.coeff_C_mul]; exact ambA_mul_mem F hc (hp n)

lemma coeff_mem_ambA_zero_X_pow_sub_X (hq : 2 ≤ Nat.card F) (n : ℕ) :
    (Polynomial.X ^ Nat.card F - Polynomial.X : Polynomial (Ambient F)).coeff n
      ∈ ambA F 0 := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  rcases eq_or_ne n (Nat.card F) with h1 | h1
  · subst h1
    rw [if_pos rfl, if_neg (by omega : ¬ (1 : ℕ) = Nat.card F), sub_zero]
    exact (ambASub F 0).one_mem
  · rw [if_neg h1]
    rcases eq_or_ne (1 : ℕ) n with h2 | h2
    · subst h2
      rw [if_pos rfl, zero_sub]
      exact (ambASub F 0).neg_mem (ambASub F 0).one_mem
    · rw [if_neg h2, sub_zero]
      exact (ambASub F 0).zero_mem

/-! ### §1g. Multiplicativity -/

lemma degPoly_mul (p q : Polynomial (Ambient F))
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (hq : ∀ n, q.coeff n ∈ ambA F 0)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    degPoly F (p * q) = degPoly F p + degPoly F q := by
  classical
  refine le_antisymm (degPoly_mul_le F p q hp hq) ?_
  rcases eq_or_ne (degPoly F p + degPoly F q) 0 with hdegen | hdegen
  · rw [hdegen]; exact Nat.zero_le _
  obtain ⟨n₀, hn₀, hne, hnmax⟩ := exists_degPoly_max_idx F p hp0
  obtain ⟨m₀, hm₀, hme, hmmax⟩ := exists_degPoly_max_idx F q hq0
  have hpn : p.coeff n₀ ≠ 0 := Polynomial.mem_support_iff.mp hn₀
  have hqm : q.coeff m₀ ≠ 0 := Polynomial.mem_support_iff.mp hm₀
  set s := Finset.HasAntidiagonal.antidiagonal (n₀ + m₀) with hs
  set a : ℕ × ℕ := (n₀, m₀) with ha
  have has : a ∈ s := by
    rw [hs, ha, Finset.HasAntidiagonal.mem_antidiagonal]
  have hmain : degTheta F (p.coeff n₀ * q.coeff m₀) = degPoly F p + degPoly F q := by
    rw [degTheta_mul F (hp n₀) (hq m₀) hpn hqm, hne, hme]
  have hrest : degTheta F (∑ x ∈ s.erase a, p.coeff x.1 * q.coeff x.2)
      < degPoly F p + degPoly F q := by
    have hle := degTheta_sum_le F (s.erase a)
      (fun x => p.coeff x.1 * q.coeff x.2)
      (fun x _ => ambA_mul_mem F (hp x.1) (hq x.2))
      (B := degPoly F p + degPoly F q - 1) (fun x hx => ?_)
    · omega
    · obtain ⟨hxa, hxs⟩ := Finset.mem_erase.mp hx
      have hsum : x.1 + x.2 = n₀ + m₀ := Finset.HasAntidiagonal.mem_antidiagonal.mp hxs
      rcases eq_or_ne (p.coeff x.1) 0 with h1 | h1
      · rw [h1, zero_mul, degTheta_zero]; exact Nat.zero_le _
      rcases eq_or_ne (q.coeff x.2) 0 with h2 | h2
      · rw [h2, mul_zero, degTheta_zero]; exact Nat.zero_le _
      rw [degTheta_mul F (hp x.1) (hq x.2) h1 h2]
      have h1s : x.1 ∈ p.support := Polynomial.mem_support_iff.mpr h1
      have h2s : x.2 ∈ q.support := Polynomial.mem_support_iff.mpr h2
      have hle1 := degPoly_coeff_le F p x.1
      have hle2 := degPoly_coeff_le F q x.2
      rcases lt_trichotomy x.1 n₀ with hlt | heq | hgt
      · have hgt2 : m₀ < x.2 := by omega
        have hstrict := degTheta_lt_degPoly_of_lt_max F (h0 := hq0) hmmax h2s hgt2
        omega
      · exfalso
        have hx2 : x.2 = m₀ := by omega
        exact hxa (by rw [ha]; exact Prod.ext heq hx2)
      · have hstrict := degTheta_lt_degPoly_of_lt_max F (h0 := hp0) hnmax h1s hgt
        omega
  have hcoeff : (p * q).coeff (n₀ + m₀)
      = (∑ x ∈ s.erase a, p.coeff x.1 * q.coeff x.2) + p.coeff n₀ * q.coeff m₀ := by
    rw [Polynomial.coeff_mul, ← hs]
    exact (Finset.sum_erase_add s (fun x => p.coeff x.1 * q.coeff x.2) has).symm
  have hrest' : degTheta F (∑ x ∈ s.erase a, p.coeff x.1 * q.coeff x.2)
      < degTheta F (p.coeff n₀ * q.coeff m₀) := by
    rw [hmain]; exact hrest
  have hkey : degTheta F ((p * q).coeff (n₀ + m₀)) = degPoly F p + degPoly F q := by
    rw [hcoeff, add_comm, degTheta_add_of_lt F (ambA_mul_mem F (hp n₀) (hq m₀))
      ((ambASub F 0).sum_mem fun x _ => ambA_mul_mem F (hp x.1) (hq x.2)) hrest', hmain]
  calc degPoly F p + degPoly F q = degTheta F ((p * q).coeff (n₀ + m₀)) := hkey.symm
    _ ≤ degPoly F (p * q) := degPoly_coeff_le F _ _

lemma coeff_mem_ambA_zero_pow {p : Polynomial (Ambient F)}
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (k : ℕ) : ∀ n, (p ^ k).coeff n ∈ ambA F 0 := by
  induction k with
  | zero => intro n; rw [pow_zero]; exact coeff_mem_ambA_zero_C F (ambA_one_mem F 0) n
  | succ k ih => intro n; rw [pow_succ]; exact coeff_mem_ambA_zero_mul F ih hp n

@[simp] lemma degPoly_one : degPoly F (1 : Polynomial (Ambient F)) = 0 := by
  rw [← Polynomial.C_1, degPoly_C F (ambA_one_mem F 0), degTheta_one]

lemma degPoly_pow (p : Polynomial (Ambient F))
    (hp : ∀ n, p.coeff n ∈ ambA F 0) (hp0 : p ≠ 0) (k : ℕ) :
    degPoly F (p ^ k) = k * degPoly F p := by
  induction k with
  | zero => rw [pow_zero, Nat.zero_mul, degPoly_one]
  | succ k ih =>
      rw [pow_succ, degPoly_mul F (p ^ k) p (fun n => coeff_mem_ambA_zero_pow F hp k n) hp
        (pow_ne_zero k hp0) hp0, ih]
      ring

/-! ### §1h. The values at `X^q - C(θ^q)`, `C(θ^q) - X^q` and `H_n`

The key device is the Frobenius identity `(X - C θ)^q = X^q - C (θ^q)` (`X_sub_C_pow_card`), which
reduces every `θ`-degree computation for `X^q - C(θ^q)` to `deg_θ (X - C θ) = 1` and
`degPoly_pow`. -/

/-- `degPoly` is invariant under negation. -/
lemma degPoly_neg (p : Polynomial (Ambient F)) (hp : ∀ n, p.coeff n ∈ ambA F 0) :
    degPoly F (-p) = degPoly F p := by
  refine le_antisymm ?_ ?_
  · refine degPoly_le_of_coeff_le F fun n => ?_
    rw [Polynomial.coeff_neg, degTheta_neg F (x := p.coeff n) (hp n)]
    exact degPoly_coeff_le F p n
  · refine degPoly_le_of_coeff_le F fun n => ?_
    have h := degPoly_coeff_le F (-p) n
    rw [Polynomial.coeff_neg, degTheta_neg F (x := p.coeff n) (hp n)] at h
    exact h

lemma coeff_mem_ambA_zero_X (n : ℕ) :
    (Polynomial.X : Polynomial (Ambient F)).coeff n ∈ ambA F 0 := by
  rw [Polynomial.coeff_X]
  split_ifs with h
  · exact (ambASub F 0).one_mem
  · exact (ambASub F 0).zero_mem

lemma coeff_mem_ambA_zero_X_sub_C {a : Ambient F} (ha : a ∈ ambA F 0) (n : ℕ) :
    (Polynomial.X - Polynomial.C a : Polynomial (Ambient F)).coeff n ∈ ambA F 0 := by
  rw [sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.coeff_add]
  exact (ambASub F 0).add_mem (coeff_mem_ambA_zero_X F n)
    (coeff_mem_ambA_zero_C F ((ambASub F 0).neg_mem ha) n)

lemma coeff_mem_ambA_zero_X_pow_sub_theta_pow (hq : 2 ≤ Nat.card F) (n : ℕ) :
    (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F) :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := by
  rw [← X_sub_C_pow_card F (ambTheta F)]
  exact coeff_mem_ambA_zero_pow F
    (coeff_mem_ambA_zero_X_sub_C F (ambTheta_mem_ambA_zero (F := F))) (Nat.card F) n

lemma coeff_mem_ambA_zero_theta_pow_sub_X_pow (hq : 2 ≤ Nat.card F) (n : ℕ) :
    (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 := by
  rw [show (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F :
      Polynomial (Ambient F))
      = -(Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) from
        (neg_sub _ _).symm,
    Polynomial.coeff_neg]
  exact (ambASub F 0).neg_mem (coeff_mem_ambA_zero_X_pow_sub_theta_pow F hq n)

/-- `deg_θ (X^q - θ^q) = q`, i.e. the `θ`-degree of the linear factor `(X - θ)^q`. -/
lemma degPoly_X_pow_sub_theta_pow (hq : 2 ≤ Nat.card F) :
    degPoly F (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F))
      = Nat.card F := by
  have hmem : ∀ n, (Polynomial.X - Polynomial.C (ambTheta F) :
      Polynomial (Ambient F)).coeff n ∈ ambA F 0 :=
    coeff_mem_ambA_zero_X_sub_C F (ambTheta_mem_ambA_zero (F := F))
  have hne : (Polynomial.X - Polynomial.C (ambTheta F) : Polynomial (Ambient F)) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero _
  rw [← X_sub_C_pow_card F (ambTheta F), degPoly_pow F _ hmem hne (Nat.card F),
    degPoly_X_sub_C F (ambTheta_mem_ambA_zero (F := F)), degTheta_theta, Nat.mul_one]

/-- `deg_θ (θ^q - X^q) = q` (the orientation used by the two rows of the endgame). -/
lemma degPoly_theta_pow_sub_X_pow (hq : 2 ≤ Nat.card F) :
    degPoly F (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F)
      = Nat.card F := by
  rw [show (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F :
        Polynomial (Ambient F))
      = -(Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) from
        (neg_sub _ _).symm,
    degPoly_neg F _ (coeff_mem_ambA_zero_X_pow_sub_theta_pow F hq),
    degPoly_X_pow_sub_theta_pow F hq]

/-- `deg_θ H_n ≤ q` for every `n`: the `θ`-degree of `ambH` is at most that of `θ^q`. -/
lemma degPoly_ambH_le (hq : 2 ≤ Nat.card F) (n : ℕ) :
    degPoly F (ambH F n) ≤ Nat.card F := by
  have hmemP : ∀ m, (Polynomial.X ^ Nat.card F - Polynomial.X :
      Polynomial (Ambient F)).coeff m ∈ ambA F 0 :=
    coeff_mem_ambA_zero_X_pow_sub_X F hq
  have hmemC : ∀ m, (Polynomial.C ((n - Nat.card F : ℕ) : Ambient F) :
      Polynomial (Ambient F)).coeff m ∈ ambA F 0 :=
    fun m => coeff_mem_ambA_zero_C F (natCast_mem_ambA F (n - Nat.card F)) m
  have hmemD : ∀ m, (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F) :
      Polynomial (Ambient F)).coeff m ∈ ambA F 0 :=
    coeff_mem_ambA_zero_X_pow_sub_theta_pow F hq
  by_cases h : n ≤ Nat.card F
  · rw [ambH_of_le F h, degPoly_one]
    exact Nat.zero_le _
  · rw [ambH_of_gt F (lt_of_not_ge h)]
    refine le_trans (degPoly_add_le F _ _ hmemP
      (fun m => coeff_mem_ambA_zero_C_mul F (natCast_mem_ambA F (n - Nat.card F)) hmemD m))
      (max_le ?_ ?_)
    · rw [degPoly_X_pow_sub_X F hq]
      exact Nat.zero_le _
    · refine le_trans (degPoly_mul_le F _ _
        (coeff_mem_ambA_zero_C F (natCast_mem_ambA F (n - Nat.card F))) hmemD) ?_
      have hc : degPoly F (Polynomial.C ((n - Nat.card F : ℕ) : Ambient F)) = 0 := by
        rw [degPoly_C F (natCast_mem_ambA F (n - Nat.card F)), degTheta_natCast F]
      rw [hc, degPoly_X_pow_sub_theta_pow F hq]
      simp

end ZagierHoffmanPositiveChar
