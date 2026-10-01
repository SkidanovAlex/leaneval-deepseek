import Mathlib
import Submission.Work.LinnikBurgess.gaussTwoLocal_defs
import Submission.Work.LinnikBurgess.peel_gauss
import Submission.Work.LinnikBurgess.primePow_kernel_char_sum
import Submission.Work.LinnikBurgess.vcap_kernel_eq
import Submission.Work.LinnikBurgess.vcap_two_gamma
import Submission.Work.LinnikBurgess.dvd_natCast_val_iff

/-!
# Bounding the peeled quadratic Gauss sum

This file is the next link after `Work.LinnikBurgess.peel_gauss`: it turns the peel

`∑_{w : ZMod (p^e)} corr6-summand = C(y) · ∑_{z : ZMod (p^(e-m))} θ ^ ((α z + γ z²).val)`

into a numeric bound on the peeled sum over the modulus range `p^(e-m)`.

The engine is the **second moment** of the quadratic Gauss sum: for a primitive `p^K`-th root of
unity `θ` one has `G * conj G = p^K · ∑_{h : 2γh = 0} θ ^ ((α h).val)`, because after the
substitution `z = h + z'` the inner sum is a complete additive-character sum.  This makes

`‖G‖² = p^K · (p^g if p^g ∣ α.val else 0)`, `g = vcap p K (2γ).val`,

hence `‖G‖ ≤ p^((K+g)/2)`; applied to `θ = psiFun p e m χ 1` (primitive of order `p^(e-m)` when
`χ` is primitive) and `γ = -(1/2)p^m·defect2`, `α = defect1` (so `g = m + vcap p (e-2m) defect2`),
this bounds the peeled sum by `p^(e/2) · p^(b_y/2)`.

The two Gauss-sum lemmas below have exactly the statements of
`Work.LinnikBurgess.gaussQuad_mul_star` and `Work.LinnikBurgess.gaussQuad_bound` (which currently
carry a `sorry`); they are proved here from scratch and are axiom-clean, so a caller may import
this module instead and keep its proofs `sorryAx`-free.  The names differ, so both modules can be
imported side by side without a name clash.
-/

open scoped BigOperators

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.LinnikBurgess

variable {p K : ℕ} [Fact p.Prime]

/-! ## Elementary lemmas on powers of a root of unity and on `ZMod`-character sums -/

/-- `vcap p K x ≤ K`. -/
lemma vcap_le_K (p K x : ℕ) : vcap p K x ≤ K := by
  rw [vcap]; split
  · exact le_rfl
  · exact min_le_right _ _

/-- `θ ^ a.val * θ ^ b.val = θ ^ (a + b).val` when `θ ^ N = 1`. -/
lemma theta_pow_val_add {N : ℕ} [NeZero N] {θ : ℂ} (hθ : θ ^ N = 1) (a b : ZMod N) :
    θ ^ a.val * θ ^ b.val = θ ^ (a + b).val := by
  rw [← pow_add, ZMod.val_add, pow_eq_pow_mod (a.val + b.val) hθ]

/-- `(θ ^ a.val)⁻¹ = θ ^ (-a).val` when `θ ^ N = 1`. -/
lemma theta_pow_val_neg {N : ℕ} [NeZero N] {θ : ℂ} (hθ : θ ^ N = 1) (a : ZMod N) :
    (θ ^ a.val)⁻¹ = θ ^ (-a).val := by
  have h := theta_pow_val_add hθ a (-a)
  rw [add_neg_cancel, ZMod.val_zero, pow_zero] at h
  exact inv_eq_of_mul_eq_one_right h

/-- The complete additive-character sum `∑_{w : ZMod N} θ ^ ((c w).val)` is `N` when `c = 0`
and `0` otherwise, for `θ` a *primitive* `N`-th root of unity. -/
lemma zmod_mul_char_sum {N : ℕ} [NeZero N] {θ : ℂ} (hθ : IsPrimitiveRoot θ N) (c : ZMod N) :
    (∑ w : ZMod N, θ ^ ((c * w).val)) = if c = 0 then (N : ℂ) else 0 := by
  have hθN : θ ^ N = 1 := hθ.pow_eq_one
  have hterm : ∀ w : ZMod N, θ ^ ((c * w).val) = (θ ^ c.val) ^ w.val := by
    intro w
    rw [ZMod.val_mul, ← pow_mul]
    exact (pow_eq_pow_mod (c.val * w.val) hθN).symm
  rw [Finset.sum_congr rfl (fun w _ => hterm w)]
  have hζ : (θ ^ c.val) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hθN, one_pow]
  rw [Commons.NumberTheory.DirichletCharacter.sum_zmod_pow_eq N hζ]
  by_cases hc : c = 0
  · rw [if_pos hc, if_pos (by rw [hc, ZMod.val_zero, pow_zero])]
  · rw [if_neg hc, if_neg]
    intro h
    exact hc ((ZMod.val_eq_zero c).mp
      (Nat.eq_zero_of_dvd_of_lt ((hθ.pow_eq_one_iff_dvd c.val).mp h) (ZMod.val_lt c)))

/-! ## The second moment of the quadratic Gauss sum -/

/-- **Second moment of the quadratic Gauss sum.**  For an odd prime `p`, a primitive `p^K`-th root
of unity `θ` and `α γ : ZMod (p^K)`,
`G · conj G = p^K · ∑_{h : (2γ)h = 0} θ ^ ((α h).val)`, `G = ∑_{w} θ ^ ((α w + γ w²).val)`.
On the kernel of `2γ` the quadratic term drops out (`2γh = 0` forces `γh = 0`). -/
theorem gaussQuad_mul_conj (hp2 : p ≠ 2) (hK : 1 ≤ K)
    {θ : ℂ} (hθ : IsPrimitiveRoot θ (p ^ K)) (α γ : ZMod (p ^ K)) :
    gaussQuad p K θ α γ * star (gaussQuad p K θ α γ)
      = ((p ^ K : ℕ) : ℂ)
        * (∑ h : ZMod (p ^ K), if (2 * γ) * h = 0 then θ ^ ((α * h).val) else 0) := by
  haveI : NeZero (p ^ K) := ⟨pow_ne_zero K (Fact.out : p.Prime).ne_zero⟩
  have hθN : θ ^ (p ^ K) = 1 := hθ.pow_eq_one
  have hθnorm : ‖θ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hθN (pow_ne_zero K (Fact.out : p.Prime).ne_zero)
  have hnormpow : ∀ n : ℕ, ‖θ ^ n‖ = 1 := fun n => by rw [norm_pow, hθnorm, one_pow]
  -- the conjugate of the Gauss sum, as a sum of inverse phases
  have hstar : star (gaussQuad p K θ α γ)
      = ∑ w : ZMod (p ^ K), θ ^ (-(α * w + γ * w ^ 2)).val := by
    change (starRingEnd ℂ) (gaussQuad p K θ α γ) = _
    rw [gaussQuad, map_sum (starRingEnd ℂ)
      (fun w : ZMod (p ^ K) => θ ^ ((α * w + γ * w ^ 2).val)) Finset.univ]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [← Complex.inv_eq_conj (hnormpow _), theta_pow_val_neg (N := p ^ K) hθN]
  calc gaussQuad p K θ α γ * star (gaussQuad p K θ α γ)
      = (∑ w : ZMod (p ^ K), θ ^ ((α * w + γ * w ^ 2).val))
        * (∑ w : ZMod (p ^ K), θ ^ (-(α * w + γ * w ^ 2)).val) := by
        rw [hstar, gaussQuad]
    _ = ∑ w : ZMod (p ^ K), ∑ w' : ZMod (p ^ K),
          θ ^ ((α * w + γ * w ^ 2).val) * θ ^ (-(α * w' + γ * w' ^ 2)).val :=
        Finset.sum_mul_sum _ _ _ _
    _ = ∑ w : ZMod (p ^ K), ∑ w' : ZMod (p ^ K),
          θ ^ ((α * w + γ * w ^ 2) - (α * w' + γ * w' ^ 2)).val := by
        refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun w' _ => ?_))
        rw [theta_pow_val_add (N := p ^ K) hθN, sub_eq_add_neg]
    _ = ∑ w : ZMod (p ^ K), ∑ h : ZMod (p ^ K),
          θ ^ ((α * w + γ * w ^ 2) - (α * (w - h) + γ * (w - h) ^ 2)).val := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [← Equiv.sum_comp (Equiv.subLeft w)
          (fun w' : ZMod (p ^ K) => θ ^ ((α * w + γ * w ^ 2) - (α * w' + γ * w' ^ 2)).val)]
        exact Finset.sum_congr rfl (fun h _ => by rw [Equiv.subLeft_apply])
    _ = ∑ w : ZMod (p ^ K), ∑ h : ZMod (p ^ K),
          θ ^ ((α * h - γ * h ^ 2) + (2 * γ * h) * w).val := by
        refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun h _ => ?_))
        congr 1
        ring
    _ = ∑ w : ZMod (p ^ K), ∑ h : ZMod (p ^ K),
          θ ^ (α * h - γ * h ^ 2).val * θ ^ ((2 * γ * h) * w).val := by
        refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun h _ => ?_))
        rw [← theta_pow_val_add (N := p ^ K) hθN]
    _ = ∑ h : ZMod (p ^ K), θ ^ (α * h - γ * h ^ 2).val
          * (∑ w : ZMod (p ^ K), θ ^ ((2 * γ * h) * w).val) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ h : ZMod (p ^ K), θ ^ (α * h - γ * h ^ 2).val
          * (if (2 * γ) * h = 0 then ((p ^ K : ℕ) : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [zmod_mul_char_sum (N := p ^ K) hθ (2 * γ * h)]
    _ = ∑ h : ZMod (p ^ K), ((p ^ K : ℕ) : ℂ)
          * (if (2 * γ) * h = 0 then θ ^ (α * h - γ * h ^ 2).val else 0) := by
        refine Finset.sum_congr rfl (fun h _ => ?_)
        split_ifs <;> ring
    _ = ((p ^ K : ℕ) : ℂ) * (∑ h : ZMod (p ^ K),
          if (2 * γ) * h = 0 then θ ^ (α * h - γ * h ^ 2).val else 0) :=
        (Finset.mul_sum Finset.univ _ _).symm
    _ = ((p ^ K : ℕ) : ℂ) * (∑ h : ZMod (p ^ K),
          if (2 * γ) * h = 0 then θ ^ ((α * h).val) else 0) := by
        congr 1
        refine Finset.sum_congr rfl (fun h _ => ?_)
        by_cases hc : (2 * γ) * h = 0
        · rw [if_pos hc, if_pos hc]
          congr 1
          have hγ : γ * h = 0 := by
            have h2 : (2 : ZMod (p ^ K)) * (γ * h) = 0 := by rw [← mul_assoc]; exact hc
            exact (IsUnit.mul_right_eq_zero
              (isUnit_two_zmod (p := p) (e := K) hp2)).mp h2
          rw [show γ * h ^ 2 = 0 by
            rw [show γ * h ^ 2 = (γ * h) * h by ring, hγ, zero_mul], sub_zero]
        · rw [if_neg hc, if_neg hc]

/-! ## The norm bound for the peeled Gauss sum -/

/-- **Quadratic Gauss-sum bound over `ZMod (p^K)`.**  For `p` odd, `K ≥ 1`, `θ` a primitive
`p^K`-th root of unity and `α γ : ZMod (p^K)`:
`‖∑_{w} θ ^ ((α w + γ w²).val)‖ ≤ p^((K+g)/2)` if `p^g ∣ α.val` and `= 0` otherwise, where
`g = vcap p K (2γ).val`. -/
theorem gaussQuad_norm_bound (hp2 : p ≠ 2) (hK : 1 ≤ K)
    (θ : ℂ) (hθ : IsPrimitiveRoot θ (p ^ K)) (α γ : ZMod (p ^ K)) :
    ‖gaussQuad p K θ α γ‖
      ≤ (if (p ^ vcap p K (2 * γ).val) ∣ α.val
          then (p : ℝ) ^ (((K : ℝ) + (vcap p K (2 * γ).val : ℝ)) / 2) else 0) := by
  haveI : NeZero (p ^ K) := ⟨pow_ne_zero K (Fact.out : p.Prime).ne_zero⟩
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  set G : ℂ := gaussQuad p K θ α γ with hGdef
  -- the kernel of multiplication by `2γ` is the kernel of multiplication by `p^(vcap …)`
  have hbridge : ∀ h : ZMod (p ^ K),
      ((2 * γ) * h = 0) ↔ (((p ^ vcap p K (2 * γ).val : ℕ) : ZMod (p ^ K)) * h = 0) :=
    fun h => vcap_kernel_eq hK (2 * γ) h
  -- evaluation of the kernel sum
  have hKsum : (∑ h : ZMod (p ^ K), if (2 * γ) * h = 0 then θ ^ ((α * h).val) else 0)
      = if p ^ vcap p K (2 * γ).val ∣ α.val
          then ((p ^ vcap p K (2 * γ).val : ℕ) : ℂ) else 0 := by
    have e1 : (∑ h : ZMod (p ^ K), if (2 * γ) * h = 0 then θ ^ ((α * h).val) else 0)
        = ∑ h ∈ Finset.univ.filter (fun h : ZMod (p ^ K) => (2 * γ) * h = 0),
            θ ^ ((α * h).val) := by
      rw [Finset.sum_filter]
    have e2 : (∑ h ∈ Finset.univ.filter (fun h : ZMod (p ^ K) => (2 * γ) * h = 0),
            θ ^ ((α * h).val))
        = ∑ h ∈ Finset.univ.filter
            (fun h : ZMod (p ^ K) =>
              ((p ^ vcap p K (2 * γ).val : ℕ) : ZMod (p ^ K)) * h = 0),
            θ ^ ((α * h).val) := by
      refine Finset.sum_congr ?_ (fun h _ => rfl)
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hbridge h
    rw [e1, e2]
    exact primePow_kernel_char_sum (vcap_le_K p K (2 * γ).val) hθ α
  -- norm-squared identity
  have hnorm : ‖G‖ ^ 2 = (p : ℝ) ^ K * (if p ^ vcap p K (2 * γ).val ∣ α.val
      then (p : ℝ) ^ (vcap p K (2 * γ).val) else 0) := by
    have h1 : ‖G * star G‖ = ‖G‖ ^ 2 := by rw [norm_mul, norm_star, pow_two]
    have hcoll := gaussQuad_mul_conj (p := p) (K := K) hp2 hK hθ α γ
    rw [← hGdef] at hcoll
    rw [← h1, hcoll, hKsum]
    rw [norm_mul, Complex.norm_natCast, Nat.cast_pow]
    congr 1
    by_cases hc : p ^ vcap p K (2 * γ).val ∣ α.val
    · rw [if_pos hc, if_pos hc, Complex.norm_natCast, Nat.cast_pow]
    · rw [if_neg hc, if_neg hc, norm_zero]
  set e : ℝ := ((K : ℝ) + (vcap p K (2 * γ).val : ℝ)) / 2 with hedef
  by_cases hc : p ^ vcap p K (2 * γ).val ∣ α.val
  · rw [if_pos hc]
    have hsq : ‖G‖ ^ 2 = ((p : ℝ) ^ e) ^ 2 := by
      rw [hnorm, if_pos hc]
      have hpK : (p : ℝ) ^ K = (p : ℝ) ^ ((K : ℕ) : ℝ) := (Real.rpow_natCast (p : ℝ) K).symm
      have hpg : (p : ℝ) ^ (vcap p K (2 * γ).val)
          = (p : ℝ) ^ ((vcap p K (2 * γ).val : ℕ) : ℝ) :=
        (Real.rpow_natCast (p : ℝ) (vcap p K (2 * γ).val)).symm
      rw [hpK, hpg, ← Real.rpow_add hpR, pow_two, ← Real.rpow_add hpR]
      congr 1
      rw [hedef]; ring
    exact le_of_eq ((pow_left_inj₀ (norm_nonneg G) (Real.rpow_nonneg hpR.le e)
      (by norm_num : (2 : ℕ) ≠ 0)).mp hsq)
  · rw [if_neg hc]
    have hz : ‖G‖ ^ 2 = 0 := by rw [hnorm, if_neg hc, mul_zero]
    have hzero : ‖G‖ = 0 := by nlinarith [norm_nonneg G]
    rw [hzero]

/-! ## The peeled sum over the next modulus range -/

/-- **The peeled cubic correlation, bounded over `ZMod (p^(e-m))`.**  Let `p` be an odd prime,
`m ≥ 1`, `e ≤ 3m`, `2m ≤ e`, `χ` a primitive Dirichlet character mod `p^e`, `a b : Fin 3 → ℕ`
and `y : ℕ` a unit at `p`.  Then the inner sum over the `p^(e-m)` lifts `x = y + p^m w` of the
cubic correlation is bounded by `p^(e/2) · p^(b_y/2)`, where `b_y = vcap p (e-2m) (defect2(y))`,
the factor `p^(b_y/2)` being present exactly when `p^(m+b_y) ∣ defect1(y)`.

Proof: `peel_gauss` rewrites the sum as the constant `C` times the quadratic Gauss sum with
`θ = psiFun p e m χ 1` (primitive of order `p^(e-m)` by `psiFun_one_isPrimitiveRoot`), `α = defect1`
and `γ = -(1/2)p^m·defect2`; `gaussQuad_norm_bound` bounds it by `p^(((e-m)+g)/2)` with
`g = vcap p (e-m) (2γ).val = m + vcap p (e-2m) (defect2).val` (`vcap_two_gamma`), and
`dvd_natCast_val_iff` converts the divisibility condition on `α.val` into one on `defect1`; `‖C‖ ≤ 1`. -/
theorem peel_gauss_bound {e m : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) (h3 : e ≤ 3 * m)
    (h2m : 2 * m ≤ e) (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (a b : Fin 3 → ℕ) (y : ℕ) (hy : UnitAt p y a b) :
    ‖∑ w : ZMod (p ^ (e - m)),
        χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
              * ((w.val : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
              + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
              + ((b l : ℕ) : ZMod (p ^ e)))))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2)
        * (if p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val) ∣ (defect1 p e a b y).val
            then (p : ℝ) ^ (((vcap p (e - 2 * m) (defect2 p e a b y).val : ℕ) : ℝ) / 2)
            else 0) := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).ne_zero⟩
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hK1 : 1 ≤ e - m := by omega
  set γ : ZMod (p ^ (e - m)) :=
    -(2 : ZMod (p ^ (e - m)))⁻¹ * ((p ^ m : ℕ) : ZMod (p ^ (e - m)))
      * (((defect2 p e a b y).val : ℕ) : ZMod (p ^ (e - m))) with hγdef
  set α : ZMod (p ^ (e - m)) := (((defect1 p e a b y).val : ℕ) : ZMod (p ^ (e - m))) with hαdef
  -- the peel
  have hpeel := peel_gauss (p := p) (e := e) (m := m) hp2 hm h3 h2m χ a b y hy
  rw [hpeel, norm_mul]
  -- the constant has norm at most one
  have hC : ‖χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3,
            (((y : ℕ) : ZMod (p ^ e)) + ((b l : ℕ) : ZMod (p ^ e)))))‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
      (DirichletCharacter.norm_le_one χ _)
  refine le_trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _)) ?_
  rw [one_mul]
  -- the Gauss-sum bound, with the parameters identified
  have hprim : IsPrimitiveRoot (psiFun p e m χ 1) (p ^ (e - m)) :=
    psiFun_one_isPrimitiveRoot (p := p) (e := e) (m := m) hp2 hm h3 h2m χ hχ
  have hgq := gaussQuad_norm_bound (p := p) (K := e - m) hp2 hK1 (psiFun p e m χ 1) hprim α γ
  have hvcapg : vcap p (e - m) (2 * γ).val
      = m + vcap p (e - 2 * m) (defect2 p e a b y).val := by
    rw [hγdef]
    exact vcap_two_gamma (p := p) (e := e) (m := m) hp2 hm h2m (defect2 p e a b y).val
      (ZMod.val_lt _)
  have hgle : m + vcap p (e - 2 * m) (defect2 p e a b y).val ≤ e - m := by
    have hv := vcap_le_K p (e - 2 * m) (defect2 p e a b y).val
    omega
  have hcond : (p ^ vcap p (e - m) (2 * γ).val ∣ α.val)
      ↔ (p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val)
          ∣ (defect1 p e a b y).val) := by
    rw [hvcapg, hαdef]
    exact dvd_natCast_val_iff (p := p) (K := e - m)
      (g := m + vcap p (e - 2 * m) (defect2 p e a b y).val)
      (d := (defect1 p e a b y).val) hgle
  have hexp : (((e - m : ℕ) : ℝ) + ((m + vcap p (e - 2 * m) (defect2 p e a b y).val : ℕ) : ℝ))
      / 2 = (e : ℝ) / 2 + ((vcap p (e - 2 * m) (defect2 p e a b y).val : ℕ) : ℝ) / 2 := by
    have h1 : (e - m) + (m + vcap p (e - 2 * m) (defect2 p e a b y).val)
        = e + vcap p (e - 2 * m) (defect2 p e a b y).val := by omega
    have h2 : ((e - m : ℕ) : ℝ) + ((m + vcap p (e - 2 * m) (defect2 p e a b y).val : ℕ) : ℝ)
        = ((e : ℕ) : ℝ) + ((vcap p (e - 2 * m) (defect2 p e a b y).val : ℕ) : ℝ) := by
      rw [← Nat.cast_add, ← Nat.cast_add, h1]
    rw [h2]; ring
  refine hgq.trans ?_
  by_cases hc : p ^ vcap p (e - m) (2 * γ).val ∣ α.val
  · rw [if_pos hc]
    have hc2 : p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val)
        ∣ (defect1 p e a b y).val := hcond.mp hc
    rw [if_pos hc2]
    have h2 : (p : ℝ) ^ ((((e - m : ℕ) : ℝ)
          + ((vcap p (e - m) (2 * γ).val : ℕ) : ℝ)) / 2)
        = (p : ℝ) ^ ((e : ℝ) / 2
            + ((vcap p (e - 2 * m) (defect2 p e a b y).val : ℕ) : ℝ) / 2) := by
      rw [hvcapg, hexp]
    rw [h2, Real.rpow_add hpR]
  · rw [if_neg hc]
    have hc2 : ¬ (p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val)
        ∣ (defect1 p e a b y).val) := fun h => hc (hcond.mpr h)
    rw [if_neg hc2, mul_zero]

end Work.LinnikBurgess
