import Submission.ZagierHoffmanProof.ABPPoly
import Submission.ZagierHoffmanProof.AmbRoot

/-!
# A level-free Siegel lemma over `O = ⋃_ν A_ν`

The auxiliary-function step of the ABP criterion solves a linear system whose entries lie in the
ring `O = ⋃_ν A_ν` with **level-0** size bounded by a constant, and whose solution has level-0
size `O(1)`.  The exact counting `card_ambA` is available at each level `ν`, and every element of
`A_ν` of size `≤ C` has level-`ν` degree `≤ q^ν · log_κ C`; hence one can run the pigeonhole at a
level `ν ≫ 0`.
-/

set_option autoImplicit false
open Polynomial
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The power map `x ↦ x^(q^ν)` is injective on the ambient field. -/
lemma ambPow_injective (ν : ℕ) :
    Function.Injective (fun x : Ambient F => x ^ (Nat.card F ^ ν)) := by
  haveI : ExpChar (Ambient F) (ringChar F) := ExpChar.prime (ringChar_prime_field F)
  have hp : ringChar F ≠ 0 := (ringChar_prime_field F).ne_zero
  intro x y hxy
  have hq : Nat.card F ^ ν = (ringChar F) ^ (ambFrobIdx F * ν) := by
    rw [ambCard_eq_pow F, pow_mul]
  rw [hq] at hxy
  change x ^ ((ringChar F) ^ (ambFrobIdx F * ν)) = y ^ ((ringChar F) ^ (ambFrobIdx F * ν)) at hxy
  have h : (x - y) ^ ((ringChar F) ^ (ambFrobIdx F * ν)) = 0 := by
    rw [sub_pow_expChar_pow, hxy, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ hp) |>.mp h)

/-- `θ_ν₀` is a `q^(ν-ν₀)`-th power of `θ_ν` for `ν₀ ≤ ν`. -/
lemma ambThetaNu_eq_pow {ν₀ ν : ℕ} (h : ν₀ ≤ ν) :
    ambThetaNu F ν₀ = (ambThetaNu F ν) ^ (Nat.card F ^ (ν - ν₀)) := by
  refine ambPow_injective F ν₀ ?_
  change (ambThetaNu F ν₀) ^ (Nat.card F ^ ν₀)
    = ((ambThetaNu F ν) ^ (Nat.card F ^ (ν - ν₀))) ^ (Nat.card F ^ ν₀)
  rw [ambThetaNu_pow, ← pow_mul, ← Nat.pow_add, Nat.sub_add_cancel h, ambThetaNu_pow]

/-- The levels `A_ν` are increasing in `ν`. -/
lemma ambA_mono {ν₀ ν : ℕ} (h : ν₀ ≤ ν) : ambA F ν₀ ⊆ ambA F ν := by
  intro x hx
  obtain ⟨p, rfl⟩ := (mem_ambA_iff F ν₀ x).mp hx
  refine (mem_ambA_iff F ν _).mpr
    ⟨p.comp (Polynomial.X ^ (Nat.card F ^ (ν - ν₀))), ?_⟩
  simp only [Polynomial.eval₂_comp, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  rw [← ambThetaNu_eq_pow F h]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- The valuation of `p(θ_ν)` in exponential form. -/
lemma v_ambRootPoly_eq (ν : ℕ) (p : Polynomial F) (hp : p ≠ 0) :
    Valued.v (ambRootPoly F ν p)
      = WithZero.exp ((p.natDegree : ℚ)
          * (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ ν)) := by
  rw [v_ambRootPoly F ν p hp, ambKappa, expmul_rat, mul_comm]

/-- **The level-`ν` degree bound.**  If an element of `A_ν` (written `p(θ_ν)`) has size `≤ C`,
then its defining polynomial has degree `≤ q^ν · log_κ C`. -/
lemma natDegree_le_of_v_le {ν : ℕ} {p : Polynomial F} (hp : p ≠ 0) {C : ℚᵐ⁰} (hCpos : 0 < C)
    (hC : Valued.v (ambRootPoly F ν p) ≤ C) :
    (p.natDegree : ℚ) * (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ ν) ≤ C.log := by
  rw [v_ambRootPoly_eq F ν p hp] at hC
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have h1 : WithZero.exp ((p.natDegree : ℚ)
      * (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ ν)) ≤ WithZero.exp (C.log) := by
    rwa [WithZero.exp_log hCne]
  exact WithZero.exp_le_exp.mp h1

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-- ★★★ **The level-free Siegel lemma over `O = ⋃_ν A_ν`.**  If a matrix with entries in `O` has
all entries of size `≤ exp c`, then there is a nonzero kernel vector with entries in `O` of size
`≤ exp d`, provided `card R · c < (card S - card R) · d`. -/
theorem siegel_union {R S : Type*} [Fintype R] [Fintype S]
    (hcard : Fintype.card R < Fintype.card S) {c d : ℚ} (hc : 0 < c)
    (hcd : (Fintype.card R : ℚ) * c < ((Fintype.card S : ℚ) - Fintype.card R) * d)
    (M : Matrix R S (Ambient F))
    (hMmem : ∀ i j, ∃ ν, M i j ∈ ambA F ν)
    (hMsize : ∀ i j, Valued.v (M i j) ≤ WithZero.exp c) :
    ∃ z : S → Ambient F, (∀ j, ∃ ν, z j ∈ ambA F ν) ∧ (∀ j, Valued.v (z j) ≤ WithZero.exp d)
      ∧ z ≠ 0 ∧ M.mulVec z = 0 := by
  classical
  have hq2 : (2 : ℚ) ≤ Nat.card F := by
    have := two_le_card_field F; exact_mod_cast this
  set k : ℚ := (Nat.card F : ℚ) - 1 with hkdef
  have hkpos : 0 < k := by rw [hkdef]; linarith
  set χ : R → S → ℕ := fun i j => Classical.choose (hMmem i j) with hχdef
  have hχspec : ∀ i j, M i j ∈ ambA F (χ i j) := fun i j => Classical.choose_spec (hMmem i j)
  set ν₀ : ℕ := Finset.univ.sup (fun i => Finset.univ.sup (fun j => χ i j)) with hν₀def
  have hχν₀ : ∀ i j, χ i j ≤ ν₀ := by
    intro i j
    rw [hν₀def]
    exact le_trans (Finset.le_sup (f := fun j => χ i j) (Finset.mem_univ j))
      (Finset.le_sup (f := fun i => Finset.univ.sup (fun j => χ i j)) (Finset.mem_univ i))
  set dC : ℚ := c / k with hdCdef
  set dD : ℚ := d / k with hdDdef
  have hΔpos : 0 < ((Fintype.card S : ℚ) - Fintype.card R) * dD - (Fintype.card R : ℚ) * dC := by
    have hsr : (Fintype.card R : ℚ) < (Fintype.card S : ℚ) := by exact_mod_cast hcard
    have h1 : (Fintype.card R : ℚ) * dC = (Fintype.card R : ℚ) * c / k := by
      rw [hdCdef]; ring
    have h2 : ((Fintype.card S : ℚ) - Fintype.card R) * dD
        = ((Fintype.card S : ℚ) - Fintype.card R) * d / k := by rw [hdDdef]; ring
    rw [h1, h2, sub_pos, div_lt_div_iff_of_pos_right hkpos]
    exact hcd
  obtain ⟨N, hN⟩ := exists_nat_gt ((Fintype.card R : ℚ)
    / (((Fintype.card S : ℚ) - Fintype.card R) * dD - (Fintype.card R : ℚ) * dC))
  set ν : ℕ := max ν₀ (max N 1) with hνdef
  have hν₀le : ν₀ ≤ ν := le_max_left ν₀ (max N 1)
  have hNle : N ≤ ν := le_trans (le_max_left N 1) (le_max_right ν₀ (max N 1))
  set μ : ℕ := Nat.ceil (((Nat.card F : ℚ) ^ ν) * dC) with hμdef
  set mm : ℕ := Nat.floor (((Nat.card F : ℚ) ^ ν) * dD) with hmmdef
  have hμge : ((Nat.card F : ℚ) ^ ν) * dC ≤ (μ : ℚ) := by
    rw [hμdef]; exact Nat.le_ceil _
  have hsrq : (0 : ℚ) < (Fintype.card S : ℚ) - Fintype.card R := by
    have : (Fintype.card R : ℚ) < (Fintype.card S : ℚ) := by exact_mod_cast hcard
    linarith
  have hdpos : 0 < d := by nlinarith [hcd, hc, hsrq]
  have hmmle : (mm : ℚ) ≤ ((Nat.card F : ℚ) ^ ν) * dD := by
    rw [hmmdef]
    exact Nat.floor_le (by rw [hdDdef]; positivity)
  have hmmgt : ((Nat.card F : ℚ) ^ ν) * dD - 1 < (mm : ℚ) := by
    have h := Nat.lt_floor_add_one (((Nat.card F : ℚ) ^ ν) * dD)
    rw [hmmdef]
    push_cast
    linarith
  have hqpowN : (N : ℚ) ≤ (Nat.card F : ℚ) ^ ν := by
    have h1 : (N : ℚ) ≤ (ν : ℚ) := by exact_mod_cast hNle
    have h2 : (ν : ℚ) < (2 : ℚ) ^ ν := by
      have h : ν < 2 ^ ν := Nat.lt_two_pow_self
      exact_mod_cast h
    have h3 : (2 : ℚ) ^ ν ≤ (Nat.card F : ℚ) ^ ν :=
      pow_le_pow_left₀ (by norm_num) hq2 ν
    linarith
  have hkey : (Fintype.card R : ℚ)
      < ((Nat.card F : ℚ) ^ ν) * (((Fintype.card S : ℚ) - Fintype.card R) * dD
          - (Fintype.card R : ℚ) * dC) := by
    have hN' : (Fintype.card R : ℚ)
        < (N : ℚ) * (((Fintype.card S : ℚ) - Fintype.card R) * dD
            - (Fintype.card R : ℚ) * dC) := by
      have h := mul_lt_mul_of_pos_right hN hΔpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hΔpos)] at h
    have hNnn : (0 : ℚ) ≤ (N : ℚ) := Nat.cast_nonneg N
    nlinarith [hN', hqpowN, hΔpos]
  have hμlt : (μ : ℚ) < ((Nat.card F : ℚ) ^ ν) * dC + 1 := by
    have h := Nat.ceil_lt_add_one (a := ((Nat.card F : ℚ) ^ ν) * dC) (by positivity)
    simpa [hμdef] using h
  have hm : (mm + μ + 1) * Fintype.card R < (mm + 1) * Fintype.card S := by
    have hcast : ((mm : ℚ) + μ + 1) * (Fintype.card R : ℚ)
        < ((mm : ℚ) + 1) * (Fintype.card S : ℚ) := by
      nlinarith [hμlt, hmmgt, hkey, hsrq]
    exact_mod_cast hcast
  have hMν : ∀ i j, M i j ∈ ambA F ν ∧ Valued.v (M i j) ≤ (ambKappa F ν) ^ μ := by
    intro i j
    refine ⟨ambA_mono F (le_trans (hχν₀ i j) hν₀le) (hχspec i j), ?_⟩
    rw [ambKappa, expmul_rat, mul_comm]
    have h2 : (((Nat.card F : ℚ) ^ ν) * dC) * (k / (Nat.card F : ℚ) ^ ν) = c := by
      rw [hdCdef]; field_simp
    calc Valued.v (M i j) ≤ WithZero.exp c := hMsize i j
      _ = WithZero.exp ((((Nat.card F : ℚ) ^ ν) * dC) * (k / (Nat.card F : ℚ) ^ ν)) := by
          rw [h2]
      _ ≤ WithZero.exp ((μ : ℚ) * (k / (Nat.card F : ℚ) ^ ν)) := by
          refine WithZero.exp_le_exp.mpr ?_
          exact mul_le_mul_of_nonneg_right hμge
            (show (0 : ℚ) ≤ k / (Nat.card F : ℚ) ^ ν by positivity)
  obtain ⟨z, hz, hz0, hzM⟩ := siegel_one (F := F) (ν := ν) (μ := μ) (m := mm) hcard hm M hMν
  refine ⟨z, fun j => ⟨ν, (hz j).1⟩, fun j => ?_, hz0, hzM⟩
  have h2 : (((Nat.card F : ℚ) ^ ν) * dD) * (k / (Nat.card F : ℚ) ^ ν) = d := by
    rw [hdDdef]; field_simp
  have hz2 : Valued.v (z j) ≤ WithZero.exp ((mm : ℚ) * (k / (Nat.card F : ℚ) ^ ν)) := by
    have h := (hz j).2
    rw [ambKappa, expmul_rat, mul_comm] at h
    exact h
  refine le_trans hz2 (WithZero.exp_le_exp.mpr ?_)
  rw [← h2]
  exact mul_le_mul_of_nonneg_right hmmle (by positivity)
