import Mathlib

/-!
# The torsion-free rank of an ℓ-adic tower product is infinite

**The engine of this chapter's refutation of `NK.ShimizuRank.GammaTFRankFinite`.**

For a prime `ℓ` consider the profinite group

  `T_ℓ := ∏_{n ∈ ℕ} ℤ/ℓ^n`,

the product of the cyclic `ℓ`-groups of *unbounded* exponent, as a `ℤ_ℓ`-module (each factor
`ZMod (ℓ^n)` carrying the `ℤ_ℓ`-structure induced by the reduction `PadicInt.toZModPow`).

The classical fact recorded here is that

  **`rank_{ℤ_ℓ} (T_ℓ ⧸ T_ℓ[tors]) = ℵ₀`**,

i.e. `T_ℓ` has *infinite* torsion-free rank, even though every factor of the product is a finite
group (of rank `0`).  This is the reason why an inverse limit of finite `ℓ`-groups with surjective
transition maps can have infinite `ℤ_ℓ`-rank: the `ℤ_ℓ`-rank of a product of finite modules is *not*
the supremum of the ranks of the factors — the *diagonal*, i.e. the coherent family `(1, 1, 1, …)`,
already has infinite order as soon as the exponents are unbounded.

Concretely we exhibit, for every `i`, the element

  `x_i ∈ T_ℓ`,   `(x_i)_n = 1`  if `ℓ^i ∣ n` but `ℓ^{i+1} ∤ n`,   `(x_i)_n = 0` otherwise,

and prove that the images of the `x_i`, `i ∈ ℕ`, in `T_ℓ ⧸ T_ℓ[tors]` form a `ℤ_ℓ`-linearly
independent family.  Since the index set `ℕ` is infinite, `LinearIndependent.aleph0_le_rank` gives
`ℵ₀ ≤ rank_{ℤ_ℓ} (T_ℓ ⧸ T_ℓ[tors])`.

The family is modelled on the observation that the "digits" of an element of `∏_n ℤ/ℓ^n` at the
places of `ℓ`-adic valuation exactly `i` are independent of those at the places of valuation
`j ≠ i`: the `n` involved range over an unbounded set, on which a nontrivial `ℤ_ℓ`-scalar cannot
annihilate an element of order `ℓ^n` for every `n`.

## Main results

* `NK.RankTheoryDeep.towerElem_independent_on_torsion` — the `towerElem i` are `ℤ_ℓ`-linearly
  independent modulo torsion;
* `NK.RankTheoryDeep.aleph0_le_rank_of_surjective_tower` — **the engine**: a `ℤ_ℓ`-module `M`
  admitting a surjective `ℤ_ℓ`-linear map onto `T_ℓ` has torsion-free rank `≥ ℵ₀` (in particular
  `ℵ₀ ≤ rank_{ℤ_ℓ} (T_ℓ ⧸ T_ℓ[tors])`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Cardinal

namespace NK.RankTheoryDeep

universe u v

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **The canonical `ℤ_ℓ`-module structure on `ℤ/ℓ^n`**: the scalar action of `a : ℤ_ℓ` is
multiplication by the reduction `PadicInt.toZModPow n a` of `a` modulo `ℓ^n`. -/
noncomputable instance instModulePadicIntZModPow (n : ℕ) : Module (PadicInt ℓ) (ZMod (ℓ ^ n)) :=
  Module.compHom (ZMod (ℓ ^ n)) (PadicInt.toZModPow (p := ℓ) n)

/-- The scalar action of `ℤ_ℓ` on `ZMod (ℓ^n)` is multiplication by the reduction of the scalar. -/
theorem smul_zmodPow_eq_mul (n : ℕ) (a : PadicInt ℓ) (x : ZMod (ℓ ^ n)) :
    a • x = PadicInt.toZModPow (p := ℓ) n a * x := rfl

/-- **The ℓ-adic tower product `T_ℓ = ∏_{n} ℤ/ℓ^n`**, as a `ℤ_ℓ`-module. -/
abbrev EllTower (ℓ : ℕ) : Type := ∀ n : ℕ, ZMod (ℓ ^ n)

/-- The `n`-th coordinate of the element `x_i` of the tower: `1` if the `ℓ`-adic valuation of `n`
is exactly `i`, and `0` otherwise. -/
noncomputable def towerGen (i n : ℕ) : ZMod (ℓ ^ n) :=
  if ℓ ^ i ∣ n ∧ ¬ ℓ ^ (i + 1) ∣ n then 1 else 0

/-- **The `i`-th "independent" element of the tower**: `1` in the coordinates of `ℓ`-adic valuation
exactly `i`, `0` elsewhere. -/
noncomputable def towerElem (i : ℕ) : EllTower ℓ := fun n => towerGen (ℓ := ℓ) i n

@[simp] theorem towerElem_apply (i n : ℕ) : towerElem (ℓ := ℓ) i n = towerGen (ℓ := ℓ) i n := rfl

/-- **There are arbitrarily large natural numbers of `ℓ`-adic valuation exactly `i`.** -/
theorem exists_vpow_eq (i N : ℕ) : ∃ n ≥ N, ℓ ^ i ∣ n ∧ ¬ ℓ ^ (i + 1) ∣ n := by
  have hℓ : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have hℓ1 : 1 ≤ ℓ := hℓ
  refine ⟨ℓ ^ i * (1 + ℓ * N), ?_, ⟨1 + ℓ * N, rfl⟩, ?_⟩
  · have h1 : 1 * (1 + ℓ * N) ≤ ℓ ^ i * (1 + ℓ * N) :=
      Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ hℓ1)
    have h2 : N ≤ 1 + ℓ * N := by nlinarith
    omega
  · rintro ⟨c, hc⟩
    have hpos : 0 < ℓ ^ i := pow_pos hℓ i
    have hEq : ℓ ^ i * (1 + ℓ * N) = ℓ ^ i * (ℓ * c) := by
      rw [hc]; ring
    have hcancel : 1 + ℓ * N = ℓ * c := Nat.mul_left_cancel hpos hEq
    have hdvd : ℓ ∣ 1 + ℓ * N := ⟨c, hcancel⟩
    have hdvd1 : ℓ ∣ 1 := by
      have := Nat.dvd_sub hdvd (dvd_mul_right ℓ N)
      simpa using this
    have hle := Nat.le_of_dvd (by norm_num) hdvd1
    have := (Fact.out : ℓ.Prime).two_le
    omega

/-- A coordinate of valuation different from `i` receives the value `0` from `x_j`. -/
theorem towerGen_eq_zero_of_ne {i j n : ℕ} (hi : ℓ ^ i ∣ n) (hi' : ¬ ℓ ^ (i + 1) ∣ n)
    (hj : j ≠ i) : towerGen (ℓ := ℓ) j n = 0 := by
  rw [towerGen]
  by_cases h : ℓ ^ j ∣ n ∧ ¬ ℓ ^ (j + 1) ∣ n
  · obtain ⟨h1, h2⟩ := h
    rcases lt_trichotomy j i with hji | hji | hji
    · exact absurd (dvd_trans (pow_dvd_pow ℓ (Nat.succ_le_of_lt hji)) hi) h2
    · exact absurd hji hj
    · exact absurd (dvd_trans (pow_dvd_pow ℓ (Nat.succ_le_of_lt hji)) h1) hi'
  · simp [h]

/-- At a coordinate of valuation exactly `i`, the element `x_i` takes the value `1`. -/
theorem towerGen_self {i n : ℕ} (hi : ℓ ^ i ∣ n) (hi' : ¬ ℓ ^ (i + 1) ∣ n) :
    towerGen (ℓ := ℓ) i n = 1 := by
  rw [towerGen]; simp [hi, hi']

/-- **The coordinate computation of the main argument.**  At a coordinate `n` of `ℓ`-adic valuation
exactly `i`, the scalar multiple `a • ∑_{j ∈ s} g_j • x_j` takes the value `toZModPow n (a * g_i)`. -/
theorem smul_sum_apply (a : PadicInt ℓ) (s : Finset ℕ) (g : ℕ → PadicInt ℓ) {i n : ℕ}
    (his : i ∈ s) (hi : ℓ ^ i ∣ n) (hi' : ¬ ℓ ^ (i + 1) ∣ n) :
    (a • (∑ j ∈ s, g j • towerElem (ℓ := ℓ) j)) n
      = PadicInt.toZModPow (p := ℓ) n (a * g i) := by
  have h1 : (∑ j ∈ s, g j • towerElem (ℓ := ℓ) j) n = g i • towerElem (ℓ := ℓ) i n := by
    rw [Finset.sum_apply]
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _ hj
      rw [Pi.smul_apply, towerElem_apply, towerGen_eq_zero_of_ne (ℓ := ℓ) hi hi' hj, smul_zero]
    · intro hi'
      exact absurd his hi'
  rw [Pi.smul_apply, h1, towerElem_apply, towerGen_self (ℓ := ℓ) hi hi']
  rw [smul_smul, smul_zmodPow_eq_mul, mul_one]

/-- **The tower elements are independent modulo torsion**: a `ℤ_ℓ`-linear relation between the
`x_i` that holds modulo the torsion submodule of `T_ℓ` is trivial. -/
theorem towerElem_independent_on_torsion (s : Finset ℕ) (g : ℕ → PadicInt ℓ)
    (h : (∑ i ∈ s, g i • towerElem (ℓ := ℓ) i) ∈
        Submodule.torsion (PadicInt ℓ) (EllTower ℓ)) :
    ∀ i ∈ s, g i = 0 := by
  classical
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_torsion_iff (∑ i ∈ s, g i • towerElem (ℓ := ℓ) i)).mp h
  have ha0 : (a : PadicInt ℓ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp a.2
  intro i hi
  have hz0 : (a : PadicInt ℓ) * g i = 0 := by
    by_contra hzne
    obtain ⟨n, hnN, hni, hni'⟩ :=
      exists_vpow_eq (ℓ := ℓ) i (((a : PadicInt ℓ) * g i).valuation + 1)
    have hcoord := smul_sum_apply (ℓ := ℓ) (a : PadicInt ℓ) s g hi hni hni'
    have hz : PadicInt.toZModPow (p := ℓ) n ((a : PadicInt ℓ) * g i) = 0 := by
      have hzero := congrArg (fun f : EllTower ℓ => f n) ha
      simp only [Pi.zero_apply] at hzero
      rw [← hcoord]
      exact hzero
    have hmem : (a : PadicInt ℓ) * g i ∈ Ideal.span {((ℓ : PadicInt ℓ)) ^ n} := by
      rw [← PadicInt.ker_toZModPow n, RingHom.mem_ker]
      exact hz
    have hle : n ≤ ((a : PadicInt ℓ) * g i).valuation :=
      (PadicInt.mem_span_pow_iff_le_valuation _ hzne n).mp hmem
    omega
  rcases mul_eq_zero.mp hz0 with h' | h'
  · exact absurd h' ha0
  · exact h'

/-- **The engine**: if a `ℤ_ℓ`-module `M` admits a surjective `ℤ_ℓ`-linear map onto the ℓ-adic
tower product `T_ℓ = ∏_n ℤ/ℓ^n`, then its torsion-free quotient has infinite `ℤ_ℓ`-rank. -/
theorem aleph0_le_rank_of_surjective_tower {M : Type u} [AddCommGroup M]
    [Module (PadicInt ℓ) M] (f : M →ₗ[PadicInt ℓ] EllTower ℓ)
    (hf : Function.Surjective f) :
    ℵ₀ ≤ Module.rank (PadicInt ℓ) (M ⧸ Submodule.torsion (PadicInt ℓ) M) := by
  classical
  choose m hm using fun i : ℕ => hf (towerElem (ℓ := ℓ) i)
  set t := Submodule.torsion (PadicInt ℓ) M with ht
  refine LinearIndependent.aleph0_le_rank (v := fun i : ℕ => t.mkQ (m i)) ?_
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hsum : ∑ j ∈ s, g j • m j ∈ t := by
    have h1 : t.mkQ (∑ j ∈ s, g j • m j) = 0 := by
      rw [map_sum]
      simp only [map_smul]
      exact hg
    rw [Submodule.mkQ_apply] at h1
    exact (Submodule.Quotient.mk_eq_zero t).mp h1
  -- push forward along `f`
  have h4 : f (∑ j ∈ s, g j • m j) = ∑ j ∈ s, g j • towerElem (ℓ := ℓ) j := by
    rw [map_sum]
    simp only [map_smul, hm]
  have h2 : (∑ j ∈ s, g j • towerElem (ℓ := ℓ) j) ∈
      Submodule.torsion (PadicInt ℓ) (EllTower ℓ) := by
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff (∑ j ∈ s, g j • m j)).mp hsum
    have htor : f (∑ j ∈ s, g j • m j) ∈ Submodule.torsion (PadicInt ℓ) (EllTower ℓ) :=
      (Submodule.mem_torsion_iff _).mpr ⟨r, by simpa using congrArg f hr⟩
    rwa [h4] at htor
  exact towerElem_independent_on_torsion (ℓ := ℓ) s g h2 i hi

end NK.RankTheoryDeep
