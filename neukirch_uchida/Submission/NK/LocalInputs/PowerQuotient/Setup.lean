import Mathlib
import Submission.NK.LocalInputs.Inputs
import Submission.NK.LocalInputs.Defs
import Submission.NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg
import Submission.NK.LocalInputs.PowerQuotient.pow_mem_maximalIdeal_pow
import Submission.NK.LocalInputs.PowerQuotient.val_prime_adicCompletion
import Submission.NK.LocalInputs.PowerQuotient.relIndex_maximalIdeal_pow
import Submission.NK.LocalInputs.ResidueChar.primesEquiv_primeBelow
import Submission.Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq
import Submission.Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero
open IsDedekindDomain

namespace NK.LocalInputs.PowerQuotient

variable {K : Type*} [Field K] [NumberField K]

noncomputable section

abbrev Zstar := WithZero (Multiplicative ℤ)

/-- The valuation of the completion, as a `Valuation`. -/
abbrev vv (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Valuation (𝔭.adicCompletion K) Zstar := Valued.v

lemma delta_le_one {M : ℕ} (hM : 1 ≤ M) :
    (WithZero.exp (-(M : ℤ)) : Zstar) ≤ 1 := by
  rw [show (1 : Zstar) = WithZero.exp (0 : ℤ) from WithZero.exp_zero.symm]
  exact WithZero.exp_le_exp.mpr (by omega)

lemma delta_lt_one {M : ℕ} (hM : 1 ≤ M) :
    (WithZero.exp (-(M : ℤ)) : Zstar) < 1 := by
  rw [show (1 : Zstar) = WithZero.exp (0 : ℤ) from WithZero.exp_zero.symm]
  exact WithZero.exp_lt_exp.mpr (by omega)

/-- The log domain: `y` with `y - 1 ∈ 𝔪 ^ M`. -/
def Disk (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) (M : ℕ)
    (y : 𝔭.adicCompletion K) : Prop :=
  vv 𝔭 (y - 1) ≤ (WithZero.exp (-(M : ℤ)) : Zstar)

/-- The exp domain: `x` with `x ∈ 𝔪 ^ M`. -/
def EDisk (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) (M : ℕ)
    (x : 𝔭.adicCompletion K) : Prop :=
  vv 𝔭 x ≤ (WithZero.exp (-(M : ℤ)) : Zstar)

variable {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)}

lemma disk_val_eq_one {M : ℕ} (hM : 1 ≤ M) {y : 𝔭.adicCompletion K}
    (hy : Disk 𝔭 M y) : vv 𝔭 y = 1 := by
  have hlt : vv 𝔭 (y - 1) < 1 := lt_of_le_of_lt hy (delta_lt_one hM)
  have h := Valuation.map_add_eq_of_lt_left (v := vv 𝔭) (x := (1 : 𝔭.adicCompletion K))
    (y := y - 1) (by rw [Valuation.map_one]; exact hlt)
  have h2 : (1 : 𝔭.adicCompletion K) + (y - 1) = y := by ring
  rw [h2] at h
  simpa using h

lemma disk_mul {M : ℕ} (hM : 1 ≤ M) {y z : 𝔭.adicCompletion K}
    (hy : Disk 𝔭 M y) (hz : Disk 𝔭 M z) : Disk 𝔭 M (y * z) := by
  have hsplit : y * z - 1 = (y - 1) + ((z - 1) + (y - 1) * (z - 1)) := by ring
  rw [Disk] at hy hz ⊢
  rw [hsplit]
  refine Valuation.map_add_le (v := vv 𝔭) hy ?_
  refine Valuation.map_add_le (v := vv 𝔭) hz ?_
  rw [Valuation.map_mul]
  calc vv 𝔭 (y - 1) * vv 𝔭 (z - 1)
      ≤ vv 𝔭 (y - 1) * 1 := mul_le_mul' (le_refl _) (le_trans hz (delta_le_one hM))
    _ = vv 𝔭 (y - 1) := mul_one _
    _ ≤ (WithZero.exp (-(M : ℤ)) : Zstar) := hy

lemma disk_pow {M : ℕ} (hM : 1 ≤ M) {y : 𝔭.adicCompletion K} (hy : Disk 𝔭 M y) (n : ℕ) :
    Disk 𝔭 M (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    show vv 𝔭 ((1 : 𝔭.adicCompletion K) - 1) ≤ _
    rw [sub_self, map_zero]; exact zero_le
  | succ k ih => rw [pow_succ]; exact disk_mul hM ih hy

/-- The maximal ideal of the ring of integers of the local field `K_𝔭`. -/
noncomputable def maxId (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Ideal (𝔭.adicCompletionIntegers K) := IsLocalRing.maximalIdeal _

/-- `U_n = 1 + 𝔪^n`, the `n`-th principal unit group. -/
noncomputable def pu (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ) :
    Subgroup ((𝔭.adicCompletionIntegers K)ˣ) where
  carrier := {u | ((u : 𝔭.adicCompletionIntegers K) - 1) ∈ (maxId 𝔭) ^ n}
  one_mem' := by
    show ((1 : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) - 1 ∈ (maxId 𝔭) ^ n
    rw [Units.val_one, sub_self]
    exact Submodule.zero_mem _
  mul_mem' := by
    intro u w hu hw
    show ((u * w : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) - 1 ∈ (maxId 𝔭) ^ n
    have h : ((u * w : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) - 1 =
        (((u : 𝔭.adicCompletionIntegers K) - 1) * ((w : 𝔭.adicCompletionIntegers K) - 1)
          + ((u : 𝔭.adicCompletionIntegers K) - 1) + ((w : 𝔭.adicCompletionIntegers K) - 1)) := by
      rw [Units.val_mul]; ring
    rw [h]
    exact add_mem (add_mem (Ideal.mul_mem_left _ _ hw) hu) hw
  inv_mem' := by
    intro u hu
    have hu' : ((u : 𝔭.adicCompletionIntegers K) - 1) ∈ (maxId 𝔭) ^ n := hu
    show ((u⁻¹ : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) - 1 ∈ (maxId 𝔭) ^ n
    have hcoe : ((u⁻¹ : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K)
        * (u : 𝔭.adicCompletionIntegers K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h : ((u⁻¹ : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) - 1 =
        -(((u⁻¹ : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K)
          * ((u : 𝔭.adicCompletionIntegers K) - 1)) := by
      rw [mul_sub, hcoe, mul_one]; ring
    rw [h]
    exact neg_mem (Ideal.mul_mem_left _ _ hu')

lemma mem_pu_iff (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ)
    (u : (𝔭.adicCompletionIntegers K)ˣ) :
    u ∈ pu 𝔭 n ↔ ((u : 𝔭.adicCompletionIntegers K) - 1) ∈ (maxId 𝔭) ^ n := Iff.rfl

lemma pu_one (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    pu 𝔭 1 = NK.LocalInputs.principalUnits K 𝔭 := by
  ext u
  rw [mem_pu_iff, NK.LocalInputs.mem_principalUnits_iff]
  show ((u : 𝔭.adicCompletionIntegers K) - 1) ∈ (maxId 𝔭) ^ 1 ↔ _
  rw [pow_one]; rfl

lemma pu_antitone (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Antitone (pu (K := K) 𝔭) := by
  intro m n hmn u hu
  rw [mem_pu_iff] at hu ⊢
  exact Ideal.pow_le_pow_right hmn hu

/-- Membership in `pu` in terms of the valuation of the completion. -/
lemma mem_pu_iff_val (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ)
    (u : (𝔭.adicCompletionIntegers K)ˣ) :
    u ∈ pu 𝔭 n ↔
      (Valued.v : Valuation (𝔭.adicCompletion K) Zstar)
        (((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) - 1) ≤
        (WithZero.exp (-(n : ℤ)) : Zstar) := by
  rw [mem_pu_iff]
  show ((u : 𝔭.adicCompletionIntegers K) - 1) ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ n ↔ _
  have h := Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
    (K := K) 𝔭 ((u : 𝔭.adicCompletionIntegers K) - 1) n
  have hcoe : (Valued.v : Valuation (𝔭.adicCompletion K) Zstar)
        ((((u : 𝔭.adicCompletionIntegers K) - 1 : 𝔭.adicCompletionIntegers K) :
          𝔭.adicCompletion K))
      = (Valued.v : Valuation (𝔭.adicCompletion K) Zstar)
        (((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) - 1) := rfl
  rw [← hcoe, h]


section LogData

/-- The exponential and logarithm of the completion on the disk `{x : v x ≤ exp (-M)}`,
with the properties supplied by the analysis of the commons. -/
structure LogData (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) (M : ℕ) where
  hM : 1 ≤ M
  exp : 𝔭.adicCompletion K → 𝔭.adicCompletion K
  log : 𝔭.adicCompletion K → 𝔭.adicCompletion K
  exp_add : ∀ x y, EDisk 𝔭 M x → EDisk 𝔭 M y → exp (x + y) = exp x * exp y
  exp_zero : exp 0 = 1
  val_exp_sub_one : ∀ x, EDisk 𝔭 M x → vv 𝔭 (exp x - 1) = vv 𝔭 x
  exp_log : ∀ y, Disk 𝔭 M y → exp (log y) = y
  val_log : ∀ y, Disk 𝔭 M y → vv 𝔭 (log y) = vv 𝔭 (y - 1)
  val_log_le : ∀ y, Disk 𝔭 M y → EDisk 𝔭 M (log y)
  log_exp : ∀ x, EDisk 𝔭 M x → log (exp x) = x

theorem exists_logData (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ M : ℕ, 1 ≤ M ∧ Nonempty (LogData 𝔭 M) := by
  obtain ⟨M, hM, exp, log, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq (K := K) 𝔭
  exact ⟨M, hM, ⟨
    { hM := hM
      exp := exp
      log := log
      exp_add := fun x y hx hy => h₄ x y hx hy
      exp_zero := h₃
      val_exp_sub_one := fun x hx => h₂ x hx
      exp_log := fun y hy => (h₅ y hy).2.2
      val_log := fun y hy => (h₅ y hy).2.1
      val_log_le := fun y hy => (h₅ y hy).1
      log_exp := fun x hx => h₆ x hx }⟩⟩

variable {M : ℕ}

/-- On the disk the logarithm is multiplicative. -/
lemma log_mul (D : LogData 𝔭 M) {y z : 𝔭.adicCompletion K}
    (hy : Disk 𝔭 M y) (hz : Disk 𝔭 M z) :
    D.log (y * z) = D.log y + D.log z := by
  have hlogy : EDisk 𝔭 M (D.log y) := D.val_log_le y hy
  have hlogz : EDisk 𝔭 M (D.log z) := D.val_log_le z hz
  have hsum : vv 𝔭 (D.log y + D.log z) ≤ (WithZero.exp (-(M : ℤ)) : Zstar) :=
    Valuation.map_add_le (v := vv 𝔭) hlogy hlogz
  have hexp : D.exp (D.log y + D.log z) = y * z := by
    rw [D.exp_add _ _ hlogy hlogz, D.exp_log y hy, D.exp_log z hz]
  rw [← hexp, D.log_exp _ hsum]

lemma log_one (D : LogData 𝔭 M) : D.log 1 = 0 := by
  have h : vv 𝔭 (0 : 𝔭.adicCompletion K) ≤ (WithZero.exp (-(M : ℤ)) : Zstar) := by
    rw [map_zero]; exact zero_le
  rw [← D.exp_zero, D.log_exp 0 h]

lemma log_pow (D : LogData 𝔭 M) {y : 𝔭.adicCompletion K} (hy : Disk 𝔭 M y) (n : ℕ) :
    D.log (y ^ n) = n • D.log y := by
  induction n with
  | zero => rw [pow_zero, log_one]; simp
  | succ k ih =>
    rw [pow_succ, log_mul D (disk_pow D.hM hy k) hy, ih, succ_nsmul]

/-- The exponential is injective on its domain. -/
lemma exp_inj (D : LogData 𝔭 M) {x y : 𝔭.adicCompletion K}
    (hx : EDisk 𝔭 M x) (hy : EDisk 𝔭 M y) (h : D.exp x = D.exp y) : x = y := by
  rw [← D.log_exp x hx, ← D.log_exp y hy, h]

lemma log_eq_zero_iff (D : LogData 𝔭 M) {y : 𝔭.adicCompletion K} (hy : Disk 𝔭 M y) :
    D.log y = 0 ↔ y = 1 := by
  constructor
  · intro h
    rw [← D.exp_log y hy, h, D.exp_zero]
  · intro h
    rw [h, log_one]

end LogData


section Torsion

variable {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)} {p : ℕ}

/-- If `x ^ p ^ m = 1` then `x ^ p ^ k = 1` for all `k ≥ m`. -/
lemma pow_pow_eq_one_of_le {G : Type*} [Group G] {x : G} {m k : ℕ} (h : x ^ p ^ m = 1)
    (hmk : m ≤ k) : x ^ p ^ k = 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmk
  rw [pow_add, pow_mul, h]
  simp

/-- The units of the ring of integers of the completion, as units of the completion. -/
noncomputable def coeUnit (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ((𝔭.adicCompletionIntegers K)ˣ) →* (𝔭.adicCompletion K)ˣ :=
  Units.map (algebraMap (𝔭.adicCompletionIntegers K) (𝔭.adicCompletion K))

/-- **The subgroup of `p`-power roots of unity** in the units of the ring of integers of the
completion `K_𝔭`. -/
noncomputable def torsionSubgroup (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (p : ℕ) : Subgroup ((𝔭.adicCompletionIntegers K)ˣ) where
  carrier := {u | ∃ m : ℕ, (coeUnit 𝔭 u) ^ p ^ m = 1}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro u v ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨max m n, ?_⟩
    rw [show (coeUnit 𝔭) (u * v) = (coeUnit 𝔭) u * (coeUnit 𝔭) v from map_mul _ _ _]
    rw [mul_pow, pow_pow_eq_one_of_le hm (le_max_left m n),
      pow_pow_eq_one_of_le hn (le_max_right m n), one_mul]
  inv_mem' := by
    rintro u ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [show (coeUnit 𝔭) u⁻¹ = ((coeUnit 𝔭) u)⁻¹ from map_inv _ _]
    rw [inv_pow, hm, inv_one]

lemma mem_torsionSubgroup_iff {u : (𝔭.adicCompletionIntegers K)ˣ} :
    u ∈ torsionSubgroup 𝔭 p ↔ ∃ m : ℕ, (coeUnit 𝔭 u) ^ p ^ m = 1 := Iff.rfl

end Torsion

section Levels

variable {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)} {p : ℕ}

/-- The ramification index `e = v(p)` of the local field. -/
def ram (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) : ℕ :=
  𝔭.asIdeal.ramificationIdx ℤ

/-- The additive subgroup `𝔪 ^ n` of the completion `K_𝔭`. -/
noncomputable def levelSub (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ) :
    AddSubgroup (𝔭.adicCompletion K) :=
  AddSubgroup.map
    (RingHom.toAddMonoidHom (algebraMap (𝔭.adicCompletionIntegers K) (𝔭.adicCompletion K)))
    ((maxId 𝔭 ^ n).toAddSubgroup)

lemma levelSub_eq_of_val (n : ℕ) (x : 𝔭.adicCompletion K) :
    x ∈ levelSub 𝔭 n ↔ vv 𝔭 x ≤ (WithZero.exp (-(n : ℤ)) : Zstar) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ (maxId 𝔭) ^ n := hy
    rw [maxId] at hy'
    exact (Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
      (K := K) 𝔭 y n).mpr hy'
  · intro hx
    have hmem : x ∈ (Valued.v : Valuation (𝔭.adicCompletion K) Zstar).valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff]
      refine le_trans hx ?_
      rw [show (1 : Zstar) = WithZero.exp (0 : ℤ) from WithZero.exp_zero.symm, WithZero.exp_le_exp]
      omega
    let y : 𝔭.adicCompletionIntegers K := ⟨x, hmem⟩
    have hyκ : ((y : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) = x := rfl
    refine ⟨y, ?_, hyκ⟩
    have h1 : y ∈ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ n :=
      (Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
        (K := K) 𝔭 y n).mp (by rw [hyκ]; exact hx)
    rw [maxId]
    exact h1

/-- Auxiliary: `exp (-(a+b)) = exp (-a) * exp (-b)`. -/
lemma exp_neg_add (a b : ℕ) :
    (WithZero.exp (-(((a + b : ℕ) : ℤ))) : Zstar) =
      (WithZero.exp (-(a : ℤ)) : Zstar) * (WithZero.exp (-(b : ℤ)) : Zstar) := by
  rw [← WithZero.exp_add]
  congr 1
  push_cast
  ring

/-- Multiplication by `p` shifts the filtration by `e`: `p · 𝔪 ^ M = 𝔪 ^ (M + e)`. -/
lemma levelSub_map_mul_p (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) (M : ℕ) :
    (levelSub 𝔭 M).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K)) =
      levelSub 𝔭 (M + ram 𝔭) := by
  have hval := val_prime_adicCompletion (K := K) 𝔭 hp hres
  have hval' : vv 𝔭 ((p : ℕ) : 𝔭.adicCompletion K) =
      (WithZero.exp (-(ram 𝔭 : ℤ)) : Zstar) := by
    rw [hval, ← WithZero.exp_nsmul]
    congr 1
    simp [ram]
  have hp0 : ((p : ℕ) : 𝔭.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hval'
    exact WithZero.exp_ne_zero hval'.symm
  ext y
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hx' := (levelSub_eq_of_val (𝔭 := 𝔭) M x).mp hx
    change ((p : ℕ) : 𝔭.adicCompletion K) * x = y at hxy
    refine (levelSub_eq_of_val (𝔭 := 𝔭) (M + ram 𝔭) _).mpr ?_
    rw [← hxy, Valuation.map_mul, hval']
    calc (WithZero.exp (-(ram 𝔭 : ℤ)) : Zstar) * vv 𝔭 x
        ≤ (WithZero.exp (-(ram 𝔭 : ℤ)) : Zstar) * (WithZero.exp (-(M : ℤ)) : Zstar) :=
          mul_le_mul' (le_refl _) hx'
      _ = (WithZero.exp (-(M : ℤ)) : Zstar) * (WithZero.exp (-(ram 𝔭 : ℤ)) : Zstar) := mul_comm _ _
      _ = (WithZero.exp (-(((M + ram 𝔭 : ℕ) : ℤ)))) := (exp_neg_add M (ram 𝔭)).symm
  · intro hy
    refine ⟨y / ((p : ℕ) : 𝔭.adicCompletion K), ?_, ?_⟩
    · refine (levelSub_eq_of_val (𝔭 := 𝔭) M _).mpr ?_
      have hy' : vv 𝔭 y ≤ (WithZero.exp (-(((M + ram 𝔭 : ℕ) : ℤ)))) :=
        (levelSub_eq_of_val (𝔭 := 𝔭) (M + ram 𝔭) y).mp hy
      rw [exp_neg_add M (ram 𝔭)] at hy'
      rw [Valuation.map_div, hval']
      exact (div_le_iff₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)).mpr hy'
    · change ((p : ℕ) : 𝔭.adicCompletion K) * (y / ((p : ℕ) : 𝔭.adicCompletion K)) = y
      rw [mul_div_cancel₀ _ hp0]

end Levels

section PowerShift

variable {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)} {p : ℕ}

lemma pu_le_one (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    1 ≤ ram 𝔭 := by
  have hpR : ((p : ℕ) : 𝔭.adicCompletionIntegers K) ∈ maxId 𝔭 := by
    rw [maxId]
    refine (IsLocalRing.residue_eq_zero_iff _).mp ?_
    have h := (CharP.charP_iff_prime_eq_zero hp).mp hres
    rw [← h]
    simp
  have hval := val_prime_adicCompletion (K := K) 𝔭 hp hres
  have hval' : vv 𝔭 ((p : ℕ) : 𝔭.adicCompletion K) =
      (WithZero.exp (-(ram 𝔭 : ℤ)) : Zstar) := by
    rw [hval, ← WithZero.exp_nsmul]
    congr 1
    simp [ram]
  have hm : ((p : ℕ) : 𝔭.adicCompletionIntegers K) ∈
      IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ 1 := by
    rw [pow_one, ← maxId]; exact hpR
  have hle : vv 𝔭 ((p : ℕ) : 𝔭.adicCompletion K) ≤ (WithZero.exp (-(1 : ℤ)) : Zstar) :=
    (Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
      (K := K) 𝔭 ((p : ℕ) : 𝔭.adicCompletionIntegers K) 1).mpr hm
  rw [hval'] at hle
  have h2 : -(ram 𝔭 : ℤ) ≤ -(1 : ℤ) := WithZero.exp_le_exp.mp hle
  omega

lemma p_mem_maxId_pow (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    ((p : ℕ) : 𝔭.adicCompletionIntegers K) ∈ (maxId 𝔭) ^ (ram 𝔭) := by
  have hval := val_prime_adicCompletion (K := K) 𝔭 hp hres
  have hval' : vv 𝔭 ((p : ℕ) : 𝔭.adicCompletion K) =
      (WithZero.exp (-(ram 𝔭 : ℤ)) : Zstar) := by
    rw [hval, ← WithZero.exp_nsmul]
    congr 1
    simp [ram]
  rw [maxId]
  refine (Commons.NumberTheory.NumberField.Completion.val_le_exp_neg_iff_mem_maximalIdeal_pow
    (K := K) 𝔭 ((p : ℕ) : 𝔭.adicCompletionIntegers K) (ram 𝔭)).mp ?_
  change vv 𝔭 ((p : ℕ) : 𝔭.adicCompletion K) ≤ (WithZero.exp (-(ram 𝔭 : ℤ)) : Zstar)
  exact le_of_eq hval'

/-- The `p`-th power map shifts the filtration by `e` once the level is at least `e`. -/
lemma pow_mem_pu_of_le (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) {n : ℕ}
    (hn : ram 𝔭 ≤ n) (hn1 : 1 ≤ n) {u : (𝔭.adicCompletionIntegers K)ˣ} (hu : u ∈ pu 𝔭 n) :
    u ^ p ∈ pu 𝔭 (n + ram 𝔭) := by
  have h := pow_mem_maximalIdeal_pow (K := K) 𝔭 hp (p_mem_maxId_pow (K := K) (𝔭 := 𝔭) hp hres) hn1 hu
  have hle : n + ram 𝔭 ≤ 2 * n := by omega
  change (((u ^ p : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) - 1) ∈
    IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ min (n + ram 𝔭) (2 * n) at h
  rw [min_eq_left hle] at h
  change (((u ^ p : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) - 1) ∈
    (maxId 𝔭) ^ (n + ram 𝔭)
  rw [maxId]
  exact h

lemma le_two_pow (e : ℕ) : e ≤ 2 ^ e := by
  induction e with
  | zero => simp
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]
    omega

lemma min_two_mul_le (a e : ℕ) :
    min (2 * a) e ≤ min (min a e + e) (2 * min a e) := by
  rcases le_total a e with h | h
  · rw [min_eq_left h]
    refine le_min ?_ ?_
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_left _ _) (by omega)
  · rw [min_eq_right h]
    refine le_min ?_ ?_
    · exact le_trans (min_le_right _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)

/-- The `p ^ k`-th power of a principal unit lies at least at the level `min (2 ^ k) e`. -/
lemma pow_pow_mem_pu_min (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) (k : ℕ)
    {u : (𝔭.adicCompletionIntegers K)ˣ} (hu : u ∈ pu 𝔭 1) :
    u ^ p ^ k ∈ pu 𝔭 (min (2 ^ k) (ram 𝔭)) := by
  induction k with
  | zero =>
    have he1 : 1 ≤ ram 𝔭 := pu_le_one (K := K) (𝔭 := 𝔭) hp hres
    simpa [min_eq_left he1] using hu
  | succ k ih =>
    have he1 : 1 ≤ ram 𝔭 := pu_le_one (K := K) (𝔭 := 𝔭) hp hres
    have hn1 : 1 ≤ min (2 ^ k) (ram 𝔭) := le_min Nat.one_le_two_pow he1
    have h := pow_mem_maximalIdeal_pow (K := K) 𝔭 hp (p_mem_maxId_pow (K := K) (𝔭 := 𝔭) hp hres)
      hn1 ih
    have hpow : u ^ p ^ (k + 1) = (u ^ p ^ k) ^ p := by
      rw [pow_succ, pow_mul]
    rw [hpow]
    have hmin : min (2 ^ (k + 1)) (ram 𝔭) ≤
        min (min (2 ^ k) (ram 𝔭) + ram 𝔭) (2 * min (2 ^ k) (ram 𝔭)) := by
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      rw [h2]
      exact min_two_mul_le (2 ^ k) (ram 𝔭)
    exact pu_antitone (K := K) 𝔭 hmin h

/-- Once at level `n ≥ e`, the `p ^ j`-th powers lie at level `n + j * e`. -/
lemma pow_pow_mem_pu_add (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) {n : ℕ}
    (hn : ram 𝔭 ≤ n) (hn1 : 1 ≤ n) {u : (𝔭.adicCompletionIntegers K)ˣ} (hu : u ∈ pu 𝔭 n)
    (j : ℕ) : u ^ p ^ j ∈ pu 𝔭 (n + j * ram 𝔭) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
    have hn1' : 1 ≤ n + j * ram 𝔭 := le_trans hn1 (Nat.le_add_right n (j * ram 𝔭))
    have hle : ram 𝔭 ≤ n + j * ram 𝔭 := le_trans hn (Nat.le_add_right n (j * ram 𝔭))
    have h := pow_mem_pu_of_le (K := K) (𝔭 := 𝔭) hp hres hle hn1' ih
    have hpow : u ^ p ^ (j + 1) = (u ^ p ^ j) ^ p := by rw [pow_succ, pow_mul]
    rw [hpow]
    have : n + (j + 1) * ram 𝔭 = (n + j * ram 𝔭) + ram 𝔭 := by ring
    rw [this]
    exact h

/-- The deep power: for `u ∈ U_1`, `u ^ p ^ (e + M) ∈ U_M`. -/
lemma deep_pow_mem (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) (M : ℕ)
    {u : (𝔭.adicCompletionIntegers K)ˣ} (hu : u ∈ pu 𝔭 1) :
    u ^ p ^ (ram 𝔭 + M) ∈ pu 𝔭 M := by
  have he1 : 1 ≤ ram 𝔭 := pu_le_one (K := K) (𝔭 := 𝔭) hp hres
  have h1 : u ^ p ^ (ram 𝔭) ∈ pu 𝔭 (min (2 ^ (ram 𝔭)) (ram 𝔭)) :=
    pow_pow_mem_pu_min (K := K) (𝔭 := 𝔭) hp hres (ram 𝔭) hu
  rw [min_eq_right (le_two_pow (ram 𝔭))] at h1
  have h2 := pow_pow_mem_pu_add (K := K) (𝔭 := 𝔭) hp hres (le_refl (ram 𝔭)) he1 h1 M
  have hpow : u ^ p ^ (ram 𝔭 + M) = (u ^ p ^ (ram 𝔭)) ^ p ^ M := by
    rw [pow_add, pow_mul]
  rw [hpow]
  refine pu_antitone (K := K) 𝔭 ?_ h2
  have : ram 𝔭 + M * ram 𝔭 = (M + 1) * ram 𝔭 := by ring
  rw [this]
  nlinarith [he1]

end PowerShift

end

end NK.LocalInputs.PowerQuotient
