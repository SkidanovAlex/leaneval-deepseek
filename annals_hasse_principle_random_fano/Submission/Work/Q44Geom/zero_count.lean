import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.HP.Q44Child.quartic_zero_bound
import Submission.Work.Q44Geom.ball_box_count

/-!
# `Work.Q44Geom.zero_count`

There is a constant `C > 0` such that every nonzero rational polynomial `f` in `5` variables
of total degree at most `4` has at most `C T^4` integral zeros of Euclidean norm at most `T`.

The proof is a reduction to the integer case:

* `int_model_self` clears denominators: `f` is `C (N : ℚ) * g` for the reduction of an integer
  polynomial `g` with `g.totalDegree ≤ f.totalDegree`;
* `Work.HP.Q44Child.count_all` bounds the number of zeros of a nonzero integer polynomial of
  total degree `≤ 4` in the coordinate box `[-M, M]^5` by `C * (M + 1)^4`;
* `Work.Q44Geom.ball_box_count` replaces the Euclidean ball of radius `T` by the box with
  `M = ⌈T⌉₊`, and `(⌈T⌉₊ + 1)^4 ≤ 81 T^4` for `T ≥ 1`.
-/

namespace Work.Q44Geom

/-- Arithmetic: if the denominator of `q` divides `N`, then `(N / q.den) * q.num` is the
integer `N * q`. -/
lemma den_dvd_cast (q : ℚ) (N : ℕ) (h : q.den ∣ N) :
    ((((N / q.den : ℕ) * q.num : ℤ)) : ℚ) = (N : ℚ) * q := by
  have hmul : ((q.den : ℚ)) * q = ((q.num : ℚ)) := by
    rw [mul_comm, Rat.mul_den_eq_num]
  have hDi : ((N / q.den : ℕ) : ℚ) * ((q.den : ℚ)) = (N : ℚ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel h]
  calc ((((N / q.den : ℕ) * q.num : ℤ)) : ℚ)
      = ((N / q.den : ℕ) : ℚ) * ((q.num : ℤ) : ℚ) := by rw [Int.cast_mul, Int.cast_natCast]
    _ = ((N / q.den : ℕ) : ℚ) * ((q.den : ℚ) * q) := by rw [hmul]
    _ = (N : ℚ) * q := by rw [← mul_assoc, hDi]

/-- Clearing denominators: every nonzero rational polynomial is a nonzero rational multiple of
the reduction of an integer polynomial of no larger total degree. -/
lemma int_model_self {σ : Type*} (f : MvPolynomial σ ℚ) (hf : f ≠ 0) :
    ∃ (N : ℕ) (g : MvPolynomial σ ℤ), 0 < N ∧ g ≠ 0 ∧
      MvPolynomial.map (Int.castRingHom ℚ) g = MvPolynomial.C (N : ℚ) * f ∧
      g.totalDegree ≤ f.totalDegree := by
  classical
  set N : ℕ := ∏ m ∈ f.support, (f.coeff m).den with hN
  have hNne : N ≠ 0 := by
    rw [hN]
    exact Finset.prod_ne_zero_iff.mpr fun m _ => Rat.den_nz (f.coeff m)
  have hNpos : 0 < N := Nat.pos_of_ne_zero hNne
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hNne
  set z : ℚ → ℤ := fun q => if q = 0 then 0 else (N / q.den : ℕ) * q.num with hz
  have hz0 : z 0 = 0 := by simp [hz]
  set g : MvPolynomial σ ℤ := AddMonoidAlgebra.ofCoeff (Finsupp.mapRange z hz0 f.coeff) with hg
  have hgc : ∀ m : σ →₀ ℕ, g.coeff m = z (f.coeff m) := by
    intro m
    rw [hg]
    rfl
  have hzq : ∀ m : σ →₀ ℕ, ((z (f.coeff m) : ℤ) : ℚ) = (N : ℚ) * f.coeff m := by
    intro m
    by_cases hm : m ∈ f.support
    · have hne : f.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
      have hzval : z (f.coeff m) = (N / (f.coeff m).den : ℕ) * (f.coeff m).num := by
        simp [hz, hne]
      rw [hzval]
      exact den_dvd_cast (f.coeff m) N (by rw [hN]; exact Finset.dvd_prod_of_mem _ hm)
    · have h0 : f.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
      rw [h0, hz0]
      simp
  have hmap : MvPolynomial.map (Int.castRingHom ℚ) g = MvPolynomial.C (N : ℚ) * f := by
    refine MvPolynomial.ext _ _ fun m => ?_
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, hgc m]
    exact hzq m
  have hgne : g ≠ 0 := by
    intro h0
    have h1 : MvPolynomial.map (Int.castRingHom ℚ) g = 0 := by rw [h0, map_zero]
    rw [hmap] at h1
    have hcN : MvPolynomial.C (N : ℚ) ≠ (0 : MvPolynomial σ ℚ) := by
      intro hc
      exact hNq (MvPolynomial.C_eq_zero.mp hc)
    exact (mul_ne_zero hcN hf) h1
  have hsupp : g.support ⊆ f.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    exact hm (by rw [hgc m, h0, hz0])
  have hdeg : g.totalDegree ≤ f.totalDegree := by
    rw [MvPolynomial.totalDegree_eq g, MvPolynomial.totalDegree_eq f]
    exact Finset.sup_mono hsupp
  exact ⟨N, g, hNpos, hgne, hmap, hdeg⟩

/-- Evaluating the reduction of an integer polynomial at a rational point agrees with the
integer evaluation. -/
lemma eval_map_intCast (g : MvPolynomial (Fin 5) ℤ) (x : Fin 5 → ℤ) :
    MvPolynomial.eval (Work.Q44Geom.toRatLM x) (MvPolynomial.map (Int.castRingHom ℚ) g)
      = ((MvPolynomial.eval x g : ℤ) : ℚ) := by
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp (Int.castRingHom ℚ) x g).symm

theorem zero_count : ∃ C : ℝ, 0 < C ∧ ∀ (f : MvPolynomial (Fin 5) ℚ), f ≠ 0 →
    f.totalDegree ≤ 4 → ∀ T : ℝ, 1 ≤ T →
    (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ T ∧ MvPolynomial.eval (Work.Q44Geom.toRatLM x) f = 0} :
      Set (Fin 5 → ℤ)).ncard : ℝ) ≤ C * T ^ 4 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.HP.Q44Child.count_all 4
  refine ⟨81 * C₀, by positivity, ?_⟩
  intro f hf hdeg T hT
  obtain ⟨N, g, hNpos, hgne, hgm, hgdeg⟩ := int_model_self f hf
  have hNq : (N : ℚ) ≠ 0 := by
    have h : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hNpos
    exact ne_of_gt h
  -- the two zero sets agree, because `eval x g` differs from `eval (toRatLM x) f` by `N ≠ 0`
  have hkey : ∀ x : Fin 5 → ℤ,
      MvPolynomial.eval (Work.Q44Geom.toRatLM x) f = 0 ↔ MvPolynomial.eval x g = 0 := by
    intro x
    have h1 : ((MvPolynomial.eval x g : ℤ) : ℚ)
        = (N : ℚ) * MvPolynomial.eval (Work.Q44Geom.toRatLM x) f := by
      rw [← eval_map_intCast g x, hgm, MvPolynomial.eval_mul, MvPolynomial.eval_C]
    constructor
    · intro h0
      have h2 : ((MvPolynomial.eval x g : ℤ) : ℚ) = 0 := by rw [h1, h0, mul_zero]
      exact_mod_cast h2
    · intro h0
      have h2 : (N : ℚ) * MvPolynomial.eval (Work.Q44Geom.toRatLM x) f = 0 := by
        rw [← h1, h0]
        norm_num
      exact (mul_eq_zero.mp h2).resolve_left hNq
  have hset : ({x : Fin 5 → ℤ |
        Work.HP.eNorm x ≤ T ∧ MvPolynomial.eval (Work.Q44Geom.toRatLM x) f = 0} :
        Set (Fin 5 → ℤ))
      = {x : Fin 5 → ℤ | Work.HP.eNorm x ≤ T ∧ MvPolynomial.eval x g = 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [hkey x]
  rw [hset]
  have harith : ((⌈T⌉₊ : ℝ) + 1) ^ 4 ≤ 81 * T ^ 4 := by
    have h1 : (⌈T⌉₊ : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
    have h2 : (⌈T⌉₊ : ℝ) + 1 ≤ 3 * T := by linarith
    have h3 : (0 : ℝ) ≤ (⌈T⌉₊ : ℝ) + 1 := by positivity
    calc ((⌈T⌉₊ : ℝ) + 1) ^ 4 ≤ (3 * T) ^ 4 := pow_le_pow_left₀ h3 h2 4
      _ = 81 * T ^ 4 := by ring
  calc (({x : Fin 5 → ℤ | Work.HP.eNorm x ≤ T ∧ MvPolynomial.eval x g = 0} :
        Set (Fin 5 → ℤ)).ncard : ℝ)
      ≤ (((Work.HP.Q44Child.cbox 5 ⌈T⌉₊).filter
          (fun x => MvPolynomial.eval x g = 0)).card : ℝ) :=
        Work.Q44Geom.ball_box_count g T
    _ = ((Work.HP.Q44Child.Cnt 5 g ⌈T⌉₊ : ℕ) : ℝ) := rfl
    _ ≤ C₀ * ((⌈T⌉₊ : ℝ) + 1) ^ 4 := hC₀ g hgne (hgdeg.trans hdeg) ⌈T⌉₊
    _ ≤ C₀ * (81 * T ^ 4) := mul_le_mul_of_nonneg_left harith hC₀pos.le
    _ = (81 * C₀) * T ^ 4 := by ring

end Work.Q44Geom
