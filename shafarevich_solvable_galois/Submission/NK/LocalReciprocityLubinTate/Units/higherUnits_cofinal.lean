import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Cofinality of the higher unit filtration `U^n = 1 + 𝔪^n`

The main result of this file is `NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal`: for a
nonarchimedean local field `F` of characteristic zero, every finite-index subgroup `M ≤ Fˣ`
contains some higher unit group `U^n = higherUnits F n`.  Equivalently, the filtration `U^n` is
cofinal among the finite-index subgroups of `Fˣ`.

## The argument

The two ingredients are

* **`𝒪[F]` is `𝔪`-adically complete**, so that a Newton/approximation sequence in `𝒪[F]` has a
  limit; and
* **Newton's method for the `D`-th power map**, which shows that every element of `1 + 𝔪^n` is a
  `D`-th power for `n` large enough.

Concretely, `exists_pow_eq_of_mem_maximalIdeal_pow` states: for every `D ≥ 1` there is `n` such
that every `y ∈ 𝔪^n` has a `D`-th root `1 + x` with `x ∈ 𝔪`.  The proof follows the classical
Newton iteration for the polynomial `X^D - (1 + y)` at the approximate root `1`; the derivative at
`1` is `D`, which is not a unit, and the iteration is therefore controlled by the additive
valuation `addVal 𝒪[F]` of the discrete valuation ring `𝒪[F]`: if the current error lies in
`𝔪^{2e+2^j}` (where `e = addVal D`), the next error lies in `𝔪^{2e+2^{j+1}}`, while the
increment of the approximating sequence lies in `𝔪^{j+1}` — enough for the sequence to be Cauchy
for the `𝔪`-adic topology.  The limit is a root by `IsHausdorff`, and lies in `1 + 𝔪` because the
first Newton increment does.

For the cofinality statement, take `D = M.index` (finite by hypothesis); then `x^D ∈ M` for every
`x ∈ Fˣ` (`Subgroup.pow_index_mem`), and the Newton lemma exhibits every element of `U^n` as a
`D`-th power, whence `U^n ≤ M`.

## Main results

* `NK.LocalReciprocityLubinTate.Units.mem_maximalIdeal_pow_iff_addVal`;
* `NK.LocalReciprocityLubinTate.Units.exists_pow_eq_of_mem_maximalIdeal_pow`;
* `NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal`.
-/

open scoped ValuativeRel

set_option linter.style.haveILetI false

universe u

namespace NK.LocalReciprocityLubinTate.Units

noncomputable section

/-! ## Membership in the powers of the maximal ideal via the additive valuation

On the discrete valuation ring `𝒪[F]`, the `n`-th power of the maximal ideal is exactly the set
where the additive valuation `IsDiscreteValuationRing.addVal` is at least `n`.  This converts
ideal membership (as needed for the `IsPrecomplete`/`IsHausdorff` API) into arithmetic in `ℕ∞`. -/

theorem mem_maximalIdeal_pow_iff_addVal (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (x : ↥𝒪[F]) :
    x ∈ 𝓂[F] ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal ↥𝒪[F] x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥𝒪[F]
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hϖ.addVal_pow]

/-! ## Newton's method for the `D`-th power map on `1 + 𝔪` -/

/-- **Newton's method for `X^D - (1 + y)` near the root `1`.**

For a nonarchimedean local field `F` of characteristic zero and every `D ≥ 1` there is `n` such
that every `y ∈ 𝔪[F]^n` admits a `D`-th root `1 + x` with `x ∈ 𝔪[F]`:
`(1 + x)^D = 1 + y`.

The derivative `D` of `X^D - (1 + y)` at `1` is not a unit of `𝒪[F]`; writing `e = addVal D`, the
Newton iteration `x_{j+1} = x_j - (X^D - (1+y))(x_j)/D · x_j^{-(D-1)}` is controlled as follows:
if `1 + y - x_j^D ∈ 𝔪^{2e+2^j}` then `x_{j+1} - x_j ∈ 𝔪^{e+2^j}` and
`1 + y - x_{j+1}^D ∈ 𝔪^{2e+2^{j+1}}`.  The increments therefore lie in `𝔪^{j+1}`, the sequence is
Cauchy for the `𝔪`-adic topology on the complete ring `𝒪[F]`, and the limit `L` satisfies
`L^D = 1 + y` by Hausdorffness; moreover `L = 1 + x` with `x ∈ 𝔪` because the first increment
does. -/
theorem exists_pow_eq_of_mem_maximalIdeal_pow (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
    (D : ℕ) (hD : 1 ≤ D) :
    ∃ n : ℕ, ∀ y : ↥𝒪[F], y ∈ 𝓂[F] ^ n →
      ∃ x : ↥𝒪[F], x ∈ 𝓂[F] ∧ (1 + x) ^ D = 1 + y := by
  classical
  haveI hAC : IsAdicComplete 𝓂[F] ↥𝒪[F] := by
    let U : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
    haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
    exact inferInstance
  haveI hpre : IsPrecomplete 𝓂[F] ↥𝒪[F] := inferInstance
  haveI hhau : IsHausdorff 𝓂[F] ↥𝒪[F] := inferInstance
  have hD0 : (D : ↥𝒪[F]) ≠ 0 := by
    intro h
    have hF : (D : F) = 0 := by
      have := congrArg (fun z : ↥𝒪[F] => (z : F)) h
      simpa using this
    exact (Nat.cast_ne_zero.mpr (by omega : D ≠ 0)) hF
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℕ∞) = IsDiscreteValuationRing.addVal ↥𝒪[F] (D : ↥𝒪[F]) := by
    refine WithTop.ne_top_iff_exists.mp ?_
    exact fun h => hD0 ((IsDiscreteValuationRing.addVal_eq_top_iff (R := ↥𝒪[F])).mp h)
  refine ⟨2 * e + 1, fun y hy => ?_⟩
  -- the Newton step
  have step : ∀ (x : ↥𝒪[F]) (j : ℕ), x - 1 ∈ 𝓂[F] →
      (1 + y - x ^ D) ∈ 𝓂[F] ^ (2 * e + 2 ^ j) →
      ∃ h : ↥𝒪[F], h ∈ 𝓂[F] ^ (e + 2 ^ j) ∧ (x + h) - 1 ∈ 𝓂[F] ∧
        (1 + y - (x + h) ^ D) ∈ 𝓂[F] ^ (2 * e + 2 ^ (j + 1)) := by
    intro x j hx hε
    have hxunit : IsUnit x := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem
      have h1 : (1 : ↥𝒪[F]) ∈ 𝓂[F] := by
        have hsub : x - (x - 1) = 1 := by ring
        rw [← hsub]
        exact sub_mem hmem hx
      exact (IsLocalRing.maximalIdeal.isMaximal ↥𝒪[F]).ne_top (Ideal.eq_top_iff_one _ |>.mpr h1)
    have hux : IsUnit (x ^ (D - 1)) := hxunit.pow (D - 1)
    have hval : IsDiscreteValuationRing.addVal ↥𝒪[F] ((D : ↥𝒪[F]) * x ^ (D - 1))
        = (e : ℕ∞) := by
      have hux' : IsDiscreteValuationRing.addVal ↥𝒪[F] (x ^ (D - 1)) = 0 := by
        have h1 : x ^ (D - 1) = ((hux.unit : (↥𝒪[F])ˣ) : ↥𝒪[F]) := (IsUnit.unit_spec hux).symm
        rw [h1, IsDiscreteValuationRing.addVal_eq_zero_of_unit]
      rw [IsDiscreteValuationRing.addVal_mul, he, hux']
      exact add_zero _
    have hle : IsDiscreteValuationRing.addVal ↥𝒪[F] ((D : ↥𝒪[F]) * x ^ (D - 1))
        ≤ IsDiscreteValuationRing.addVal ↥𝒪[F] (1 + y - x ^ D) := by
      rw [hval]
      refine le_trans ?_ ((mem_maximalIdeal_pow_iff_addVal F (2 * e + 2 ^ j)
        (1 + y - x ^ D)).mp hε)
      have hle' : e ≤ 2 * e + 2 ^ j := by
        have hj : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        omega
      exact_mod_cast hle'
    obtain ⟨h, hh⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.mp hle
    have hhval : ((e + 2 ^ j : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal ↥𝒪[F] h := by
      have h1 : IsDiscreteValuationRing.addVal ↥𝒪[F] (1 + y - x ^ D)
          = (e : ℕ∞) + IsDiscreteValuationRing.addVal ↥𝒪[F] h := by
        rw [hh, IsDiscreteValuationRing.addVal_mul, hval]
      have h2 : ((2 * e + 2 ^ j : ℕ) : ℕ∞)
          ≤ IsDiscreteValuationRing.addVal ↥𝒪[F] (1 + y - x ^ D) :=
        (mem_maximalIdeal_pow_iff_addVal F (2 * e + 2 ^ j) (1 + y - x ^ D)).mp hε
      rw [h1] at h2
      have h3 : (e : ℕ∞) + ((e + 2 ^ j : ℕ) : ℕ∞)
          ≤ (e : ℕ∞) + IsDiscreteValuationRing.addVal ↥𝒪[F] h := by
        refine le_trans (le_of_eq ?_) h2
        rw [ENat.natCast_add]
        push_cast
        ring
      exact (ENat.add_le_add_iff_left (ENat.natCast_ne_top e)).mp h3
    have hhmem : h ∈ 𝓂[F] ^ (e + 2 ^ j) :=
      (mem_maximalIdeal_pow_iff_addVal F (e + 2 ^ j) h).mpr hhval
    -- Taylor expansion of `X^D` at `x`
    obtain ⟨q, hq⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add
      (Polynomial.X ^ D : Polynomial ↥𝒪[F]) x h
    have hderiv : Polynomial.eval x ((Polynomial.X ^ D : Polynomial ↥𝒪[F]).derivative)
        = (D : ↥𝒪[F]) * x ^ (D - 1) := by
      rw [Polynomial.derivative_X_pow]
      simp
    have heval : Polynomial.eval (x + h) (Polynomial.X ^ D : Polynomial ↥𝒪[F]) = (x + h) ^ D := by
      simp
    have hq' : q * h ^ 2 + ((D : ↥𝒪[F]) * x ^ (D - 1)) * h + x ^ D = (x + h) ^ D := by
      rw [← hderiv, ← heval]
      simpa using hq
    have hroot : (x + h) ^ D = 1 + y + q * h ^ 2 := by
      rw [← hq', ← hh]
      ring
    have hnew : (1 + y - (x + h) ^ D) ∈ 𝓂[F] ^ (2 * e + 2 ^ (j + 1)) := by
      have heq : 1 + y - (x + h) ^ D = -(q * h ^ 2) := by rw [hroot]; ring
      rw [heq, mem_maximalIdeal_pow_iff_addVal F, AddValuation.map_neg]
      have h1 : IsDiscreteValuationRing.addVal ↥𝒪[F] (q * h ^ 2)
          = IsDiscreteValuationRing.addVal ↥𝒪[F] q
            + (2 : ℕ∞) * IsDiscreteValuationRing.addVal ↥𝒪[F] h := by
        rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
          nsmul_eq_mul]
        norm_num
      have h2 : ((2 * e + 2 ^ (j + 1) : ℕ) : ℕ∞)
          ≤ (2 : ℕ∞) * IsDiscreteValuationRing.addVal ↥𝒪[F] h := by
        have h3 : (2 : ℕ∞) * ((e + 2 ^ j : ℕ) : ℕ∞)
            ≤ (2 : ℕ∞) * IsDiscreteValuationRing.addVal ↥𝒪[F] h :=
          mul_le_mul' le_rfl hhval
        refine le_trans (le_of_eq ?_) h3
        push_cast
        ring
      rw [h1]
      exact le_trans h2
        (le_add_of_nonneg_left (b := IsDiscreteValuationRing.addVal ↥𝒪[F] q) zero_le)
    refine ⟨h, hhmem, ?_, hnew⟩
    have : (x + h) - 1 = (x - 1) + h := by ring
    rw [this]
    exact add_mem hx (Ideal.pow_le_self (n := e + 2 ^ j) (by
      have hj : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      omega) hhmem)
  -- the Newton sequence: `aux j = (x j, x (j+1))`, with the increment lying in `𝔪^{j+1}`
  let P : ℕ → (↥𝒪[F] × ↥𝒪[F]) → Prop := fun j p =>
    (p.1 - 1 ∈ 𝓂[F]) ∧ (p.2 - 1 ∈ 𝓂[F]) ∧ (p.2 - p.1 ∈ 𝓂[F] ^ (j + 1)) ∧
      (1 + y - p.2 ^ D ∈ 𝓂[F] ^ (2 * e + 2 ^ (j + 1)))
  let aux : (j : ℕ) → { p : ↥𝒪[F] × ↥𝒪[F] // P j p } :=
    Nat.rec (motive := fun j => { p : ↥𝒪[F] × ↥𝒪[F] // P j p })
      (by
        let h := Classical.choose (step 1 0 (by simp) (by simpa using hy))
        have hspec := Classical.choose_spec (step 1 0 (by simp) (by simpa using hy))
        refine ⟨(1, 1 + h), by simp, ?_, ?_, ?_⟩
        · exact hspec.2.1
        · show (1 + h) - 1 ∈ 𝓂[F] ^ (0 + 1)
          rw [add_sub_cancel_left]
          exact Ideal.pow_le_pow_right (by omega) hspec.1
        · exact hspec.2.2)
      (fun j ih => by
        let h := Classical.choose (step ih.1.2 (j + 1) ih.2.2.1 ih.2.2.2.2)
        have hspec := Classical.choose_spec (step ih.1.2 (j + 1) ih.2.2.1 ih.2.2.2.2)
        refine ⟨(ih.1.2, ih.1.2 + h), ih.2.2.1, ?_, ?_, ?_⟩
        · exact hspec.2.1
        · show (ih.1.2 + h) - ih.1.2 ∈ 𝓂[F] ^ (j + 1 + 1)
          rw [add_sub_cancel_left]
          exact Ideal.pow_le_pow_right (by
            have := Nat.lt_two_pow_self (n := j + 1)
            omega) hspec.1
        · exact hspec.2.2)
  have hnext : ∀ j, (aux (j+1)).1.1 = (aux j).1.2 := fun j => rfl
  have hmem_incr : ∀ j, (aux (j+1)).1.1 - (aux j).1.1 ∈ 𝓂[F] ^ (j + 1) := by
    intro j
    rw [hnext j]
    exact (aux j).2.2.2.1
  have hε_all : ∀ n, 1 + y - (aux n).1.1 ^ D ∈ 𝓂[F] ^ n := by
    intro n
    rcases n with _ | n
    · simp
    · rw [hnext n]
      refine Ideal.pow_le_pow_right (by
        have := Nat.lt_two_pow_self (n := n + 1)
        omega) (aux n).2.2.2.2
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      (aux m).1.1 ≡ (aux n).1.1 [SMOD (𝓂[F] ^ m • ⊤ : Submodule ↥𝒪[F] ↥𝒪[F])] := by
    intro m n hmn
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    induction n with
    | zero =>
      have hm0 : m = 0 := by omega
      subst hm0
      simp
    | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hmn' : m ≤ n := by omega
        have h1 : (aux m).1.1 - (aux (n + 1)).1.1
            = ((aux m).1.1 - (aux n).1.1) - ((aux (n + 1)).1.1 - (aux n).1.1) := by ring
        rw [h1]
        exact sub_mem (ih hmn') (Ideal.pow_le_pow_right (by omega) (hmem_incr n))
      · have : m = n + 1 := by omega
        subst this
        simp
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := 𝓂[F]) (M := ↥𝒪[F])
    (fun j => (aux j).1.1) hcauchy
  have hLmem : ∀ n : ℕ, L - (aux n).1.1 ∈ 𝓂[F] ^ n := by
    intro n
    have h := hL n
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h
    rw [show L - (aux n).1.1 = -((aux n).1.1 - L) by ring]
    exact neg_mem h
  refine ⟨L - 1, ?_, ?_⟩
  · have h1 : L - (aux 1).1.1 ∈ 𝓂[F] := by simpa using hLmem 1
    have h2 : (aux 1).1.1 - 1 ∈ 𝓂[F] := (aux 1).2.1
    rw [show L - 1 = (L - (aux 1).1.1) + ((aux 1).1.1 - 1) by ring]
    exact add_mem h1 h2
  · have hroot : L ^ D = 1 + y := by
      rw [← sub_eq_zero]
      refine IsHausdorff.haus' (I := 𝓂[F]) (L ^ D - (1 + y)) (fun n => ?_)
      rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
      have h1 : L ^ D - (aux n).1.1 ^ D ∈ 𝓂[F] ^ n := by
        obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow L (aux n).1.1 D
        rw [hc]
        exact Ideal.mul_mem_right _ _ (hLmem n)
      have h2 : (aux n).1.1 ^ D - (1 + y) ∈ 𝓂[F] ^ n := by
        rw [show (aux n).1.1 ^ D - (1 + y) = -(1 + y - (aux n).1.1 ^ D) by ring]
        exact neg_mem (hε_all n)
      rw [show L ^ D - (1 + y)
        = (L ^ D - (aux n).1.1 ^ D) + ((aux n).1.1 ^ D - (1 + y)) by ring]
      exact add_mem h1 h2
    rw [show 1 + (L - 1) = L by ring, hroot]

/-! ## Cofinality of the higher unit filtration -/

/-- **Cofinality of the higher unit filtration.**

Every finite-index subgroup `M` of `Fˣ` contains some higher unit group `U^n = 1 + 𝔪^n`.

Since `Fˣ` is abelian and `[Fˣ : M] = D` is finite, `x^D ∈ M` for every `x : Fˣ`
(`Subgroup.pow_index_mem`).  By `exists_pow_eq_of_mem_maximalIdeal_pow` with `D = M.index`, every
element of `U^n` for suitable `n` is a `D`-th power in `𝒪[F]ˣ ≤ Fˣ`, hence lies in `M`. -/
theorem higherUnits_cofinal (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] (M : Subgroup Fˣ)
    (hM : M.FiniteIndex) : ∃ n : ℕ, NK.LocalReciprocityLubinTate.higherUnits F n ≤ M := by
  classical
  have hD : M.index ≠ 0 := Subgroup.finiteIndex_iff.mp hM
  have hD1 : 1 ≤ M.index := Nat.one_le_iff_ne_zero.mpr hD
  obtain ⟨n, hn⟩ := exists_pow_eq_of_mem_maximalIdeal_pow F M.index hD1
  refine ⟨n, fun u hu => ?_⟩
  rw [NK.LocalReciprocityLubinTate.higherUnits, Subgroup.mem_map] at hu
  obtain ⟨v, hv, hvu⟩ := hu
  rw [NK.LocalReciprocityLubinTate.mem_principalUnits_iff] at hv
  obtain ⟨x, hx, hxpow⟩ := hn ((v : ↥𝒪[F]) - 1) hv
  have hxunit : IsUnit (1 + x : ↥𝒪[F]) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have h1 : (1 : ↥𝒪[F]) ∈ 𝓂[F] := by
      have hsub : (1 + x) - x = 1 := by ring
      rw [← hsub]
      exact sub_mem hmem hx
    exact (IsLocalRing.maximalIdeal.isMaximal ↥𝒪[F]).ne_top (Ideal.eq_top_iff_one _ |>.mpr h1)
  let w : (↥𝒪[F])ˣ := hxunit.unit
  have hw : w ^ M.index = v := by
    apply Units.ext
    show ((w ^ M.index : (↥𝒪[F])ˣ) : ↥𝒪[F]) = (v : ↥𝒪[F])
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec hxunit]
    convert hxpow using 2
    ring
  have hpow : (Units.map (Subring.subtype 𝒪[F]).toMonoidHom w) ^ M.index = u := by
    rw [← map_pow, hw, hvu]
  rw [← hpow]
  exact Subgroup.pow_index_mem M (Units.map (Subring.subtype 𝒪[F]).toMonoidHom w)

end

end NK.LocalReciprocityLubinTate.Units
