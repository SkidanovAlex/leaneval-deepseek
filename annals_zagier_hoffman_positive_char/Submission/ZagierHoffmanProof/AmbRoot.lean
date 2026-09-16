import Submission.ZagierHoffmanProof.AmbientRing

/-!
# Roots of elements of `A_0` inside the levels `A_ν`

The ring `A_ν = F_q[θ_ν]` (the range of `T ↦ θ_ν`) contains the `q^ν`-th root of every element of
`A_0 = F_q[θ]`:

* `ambRootPoly ν p = p(θ_ν)`, with `(ambRootPoly ν p) ^ (q^ν) = p(θ)`;
* `ambRoot ν x hx` — the same, for `x ∈ A_0`, using the (unique) `p` with `p(θ) = x`.

These are the elements in which the auxiliary-function system of the ABP criterion is expressed.
-/

set_option autoImplicit false
open Polynomial
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- `p ↦ p(θ_ν)`: the `q^ν`-th root of `p(θ)`. -/
noncomputable def ambRootPoly (ν : ℕ) (p : Polynomial F) : Ambient F :=
  p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν)

@[simp] lemma ambRootPoly_apply (ν : ℕ) (p : Polynomial F) :
    ambRootPoly F ν p = p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν) := rfl

lemma ambRootPoly_pow (ν : ℕ) (p : Polynomial F) :
    (ambRootPoly F ν p) ^ (Nat.card F ^ ν)
      = p.eval₂ (algebraMap F (Ambient F)) (ambTheta F) :=
  ambThetaNu_eval_pow F ν p

lemma ambRootPoly_mem (ν : ℕ) (p : Polynomial F) : ambRootPoly F ν p ∈ ambA F ν :=
  (mem_ambA_iff F ν _).mpr ⟨p, rfl⟩

lemma v_ambRootPoly (ν : ℕ) (p : Polynomial F) (hp : p ≠ 0) :
    Valued.v (ambRootPoly F ν p) = (ambKappa F ν) ^ p.natDegree :=
  v_eval₂_ambThetaNu F ν p hp

/-- A chosen `θ`-preimage in `F[T]` of an element of `A_0`. -/
noncomputable def ambPreimage (x : Ambient F) (hx : x ∈ ambA F 0) : Polynomial F :=
  Classical.choose ((mem_ambA_iff F 0 x).mp hx)

lemma ambPreimage_spec (x : Ambient F) (hx : x ∈ ambA F 0) :
    (ambPreimage F x hx).eval₂ (algebraMap F (Ambient F)) (ambTheta F) = x :=
  Classical.choose_spec ((mem_ambA_iff F 0 x).mp hx)

/-- The `q^ν`-th root of an element of `A_0`, realised in `A_ν`. -/
noncomputable def ambRoot (ν : ℕ) (x : Ambient F) (hx : x ∈ ambA F 0) : Ambient F :=
  ambRootPoly F ν (ambPreimage F x hx)

lemma ambRoot_pow (ν : ℕ) (x : Ambient F) (hx : x ∈ ambA F 0) :
    (ambRoot F ν x hx) ^ (Nat.card F ^ ν) = x := by
  rw [ambRoot, ambRootPoly_pow, ambPreimage_spec]

lemma ambRoot_mem (ν : ℕ) (x : Ambient F) (hx : x ∈ ambA F 0) : ambRoot F ν x hx ∈ ambA F ν :=
  ambRootPoly_mem F ν _

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- `exp` turns multiplication of rational exponents into powers. -/
lemma expmul_rat (k : ℚ) (m : ℕ) : (WithZero.exp k) ^ m = (WithZero.exp (k * m) : ℚᵐ⁰) := by
  induction m with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, ih, ← WithZero.exp_add]
      congr 1
      push_cast
      ring

/-- The `q^ν`-th power of the root is the original element. -/
lemma v_ambRoot_pow (F : Type*) [Field F] [Finite F] (ν : ℕ) (x : Ambient F)
    (hx : x ∈ ambA F 0) :
    (Valued.v (ambRoot F ν x hx)) ^ (Nat.card F ^ ν) = Valued.v x := by
  rw [← map_pow, ambRoot_pow]

lemma ambKappa_zero (F : Type*) [Field F] [Finite F] (d : ℕ) :
    (ambKappa F 0) ^ d = WithZero.exp (((Nat.card F : ℚ) - 1) * d) := by
  rw [ambKappa]
  rw [show (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ 0) = ((Nat.card F : ℚ) - 1) by simp]
  rw [expmul_rat]

lemma ambKappa_pow_self (F : Type*) [Field F] [Finite F] (ν d : ℕ) :
    ((ambKappa F ν) ^ d) ^ (Nat.card F ^ ν) = (ambKappa F 0) ^ d := by
  rw [ambKappa_zero, ambKappa]
  simp only [expmul_rat]
  rw [WithZero.exp_inj]
  have hq : ((Nat.card F : ℚ)) ^ ν ≠ 0 := by
    have h2 : (0 : ℚ) < (Nat.card F : ℚ) := by
      have h3 := two_le_card_field F
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) h3)
    exact pow_ne_zero _ (ne_of_gt h2)
  field_simp
  push_cast
  ring

/-- **The size of the root.**  If `x ∈ A_0` has `v x ≤ κ_0^d` then its `q^ν`-th root has
`v ≤ κ_ν^d`. -/
lemma v_ambRoot_le (F : Type*) [Field F] [Finite F] (ν : ℕ) (x : Ambient F)
    (hx : x ∈ ambA F 0) {d : ℕ} (hd : Valued.v x ≤ (ambKappa F 0) ^ d) :
    Valued.v (ambRoot F ν x hx) ≤ (ambKappa F ν) ^ d := by
  have hq := FrobPow.ne_zero (Ambient F) (q := Nat.card F)
  refine (pow_le_pow_iff_left₀ (zero_le : (0 : ℚᵐ⁰) ≤ _) (zero_le : (0 : ℚᵐ⁰) ≤ _)
    (pow_ne_zero ν hq)).mp ?_
  rw [v_ambRoot_pow, ambKappa_pow_self]
  exact hd
