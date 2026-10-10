import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Irreducibility of the Artin–Schreier polynomial `X ^ p - X - a`

Over a field `F` of prime characteristic `p`, the polynomial `X ^ p - X - a ∈ F[X]` is irreducible
as soon as `a` is not of the form `b ^ p - b` (`b ∈ F`).

The proof is the classical one: we work in an algebraic closure `K` of `F` and let `α ∈ K` be a
root of `X ^ p - X - a`.  All roots of `X ^ p - X - a` in `K` are of the shape `α + c` with
`c ^ p = c`.  If `m := minpoly F α` has degree `d < p`, then `m` is monic of degree `d` and splits
in `K`, so `m.nextCoeff = -(m.roots.sum)`; writing every root `β` of `m` as `α + (β - α)` exhibits
`-(m.nextCoeff) - d • α` as an element of the prime subfield of `K`, whence `d • α ∈ F`; as
`1 ≤ d < p` the scalar `d` is invertible, so `α ∈ F` and `a = α ^ p - α`, a contradiction.
-/

set_option linter.style.haveILetI false

namespace Work.ClassBCD.RatFunc

open Polynomial

/-- A multiset-sum identity: for a multiset `s` in a ring and an element `a`,
`s.sum = (s.map (· - a)).sum + s.card • a`. -/
theorem multiset_sum_eq_sum_sub_add_card_nsmul {R : Type*} [Ring R] (s : Multiset R) (a : R) :
    s.sum = (s.map (fun b => b - a)).sum + s.card • a := by
  have hfun : (fun b : R => (b - a) + a) = id := by funext b; simp
  have key : s = s.map (fun b => (b - a) + a) := by rw [hfun, Multiset.map_id]
  rw [key, Multiset.sum_map_add, show (fun b : R => a) = Function.const R a from rfl,
    Multiset.map_const, Multiset.sum_replicate]
  simp

open Polynomial in
theorem irreducible_X_pow_sub_X_sub_C (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (a : F) (h : ∀ b : F, b ^ p - b ≠ a) :
    Irreducible (X ^ p - X - C a : F[X]) := by
  have hpp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hpp.two_le
  have hp_pos : 0 < p := hpp.pos
  set f : F[X] := X ^ p - X - C a with hf
  have hfnat : f.natDegree = p := by
    rw [hf]
    rw [show (X ^ p - X - C a : F[X]) = (X ^ p - X) - C a from rfl]
    rw [natDegree_sub_C,
      natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X, natDegree_X_pow]; omega),
      natDegree_X_pow]
  have hfmonic : f.Monic := by
    rw [hf]
    have hdegX : (X : F[X]).degree < (X ^ p : F[X]).degree := by
      rw [degree_X, degree_X_pow]
      exact_mod_cast (by omega : 1 < p)
    have h1 : (X ^ p - X : F[X]).Monic := (monic_X_pow p).sub_of_left hdegX
    refine h1.sub_of_left ?_
    have h3 : (X ^ p - X : F[X]).degree = (X ^ p : F[X]).degree :=
      degree_sub_eq_left_of_degree_lt hdegX
    rw [h3, degree_X_pow]
    exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hp_pos)
  -- the algebraic closure and a root `α` of `f`
  let K := AlgebraicClosure F
  haveI : IsAlgClosed K := AlgebraicClosure.isAlgClosed F
  have hdeg : (f.map (algebraMap F K)).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (hfmonic.map (algebraMap F K)).ne_zero,
      natDegree_map_eq_of_injective (algebraMap F K).injective f, hfnat]
    exact fun hh => hp_pos.ne' (WithBot.coe_eq_zero.mp hh)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (f.map (algebraMap F K)) hdeg
  have hαeval : aeval α f = 0 := by
    rw [aeval_def, ← eval_map]
    exact hα
  -- the minimal polynomial
  have hαint : IsIntegral F α := ⟨f, hfmonic, hαeval⟩
  set m : F[X] := minpoly F α with hm
  have hm_monic : m.Monic := by rw [hm]; exact minpoly.monic hαint
  have hm_irr : Irreducible m := by rw [hm]; exact minpoly.irreducible hαint
  have hm_dvd : m ∣ f := by rw [hm]; exact minpoly.dvd F α hαeval
  have hαeq : α ^ p - α = algebraMap F K a := by
    have hh := hαeval
    rw [hf] at hh
    simp only [aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at hh
    linear_combination (norm := first | refl_ring1 | ring1) hh
  suffices hm_nat : m.natDegree = p by
    have hfm : f = m :=
      eq_of_monic_of_dvd_of_natDegree_le hm_monic hfmonic hm_dvd (by rw [hfnat, hm_nat])
    change Irreducible f
    rw [hfm]
    exact hm_irr
  by_contra hne
  have hle : m.natDegree ≤ p := by
    rw [← hfnat]; exact natDegree_le_of_dvd hm_dvd hfmonic.ne_zero
  have hlt : m.natDegree < p := lt_of_le_of_ne hle hne
  have hm1 : m.natDegree ≠ 0 := by
    have : m ≠ 1 := fun h1 => hm_irr.not_isUnit (h1 ▸ isUnit_one)
    exact (hm_monic.natDegree_pos.mpr this).ne'
  -- `M := m` viewed in `K[X]`
  set M : K[X] := m.map (algebraMap F K) with hM
  have hMsplits : M.Splits := IsAlgClosed.splits M
  have hMmonic : M.Monic := by rw [hM]; exact hm_monic.map _
  have hMne : M ≠ 0 := hMmonic.ne_zero
  have hMnat : M.natDegree = m.natDegree := by
    rw [hM]; exact natDegree_map_eq_of_injective (algebraMap F K).injective m
  have hMnext : M.nextCoeff = algebraMap F K m.nextCoeff := by
    rw [hM]; exact nextCoeff_map (algebraMap F K).injective m
  have hMnextsum : M.nextCoeff = - M.roots.sum :=
    hMsplits.nextCoeff_eq_neg_sum_roots_of_monic hMmonic
  -- every root of `M` is `α` plus an element with `x ^ p = x`
  have hβroot : ∀ β ∈ M.roots, β ^ p - β = algebraMap F K a := by
    intro β hβ
    have hMβ : eval β M = 0 := by
      rw [mem_roots hMne] at hβ; exact hβ
    have hdiv : M ∣ f.map (algebraMap F K) := by
      rw [hM]; exact Polynomial.map_dvd _ hm_dvd
    have hq : eval β (f.map (algebraMap F K)) = 0 :=
      Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdiv hMβ
    have hfm : f.map (algebraMap F K) = X ^ p - X - C (algebraMap F K a) := by
      rw [hf, show (X ^ p - X - C a : F[X]) = (X ^ p - X) - C a from rfl]
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [hfm] at hq
    simp only [eval_sub, eval_pow, eval_X, eval_C] at hq
    linear_combination (norm := first | refl_ring1 | ring1) hq
  have hsub : ∀ β ∈ M.roots, β - α ∈ (⊥ : Subfield K) := by
    intro β hβ
    rw [Subfield.mem_bot_iff_pow_eq_self K p]
    rw [sub_pow_char]
    linear_combination (norm := first | refl_ring1 | ring1) (hβroot β hβ) - hαeq
  set S : K := (M.roots.map (fun b => b - α)).sum with hSdef
  have hSmem : S ∈ (⊥ : Subfield K) := by
    rw [hSdef]
    refine (⊥ : Subfield K).multiset_sum_mem _ ?_
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact hsub b hb
  have hcard : M.roots.card = m.natDegree := by
    rw [← hMsplits.natDegree_eq_card_roots, hMnat]
  have hsum2 : M.roots.sum = S + M.roots.card • α := by
    rw [hSdef]; exact multiset_sum_eq_sum_sub_add_card_nsmul M.roots α
  have hsum3 : M.roots.sum = - algebraMap F K m.nextCoeff := by
    have h1 : M.roots.sum = - M.nextCoeff := by rw [hMnextsum, neg_neg]
    rw [h1, hMnext]
  have hkey : (M.roots.card : K) * α = - algebraMap F K m.nextCoeff - S := by
    have h2 : M.roots.sum = S + (M.roots.card : K) * α := by rw [hsum2, nsmul_eq_mul]
    rw [hsum3] at h2
    rw [h2]
    first | refl_ring1 | ring
  -- the scalar `m.natDegree` is nonzero in `F`
  have hdneF : (m.natDegree : F) ≠ 0 := by
    intro hzero
    rw [CharP.cast_eq_zero_iff F p] at hzero
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm1) hzero
    omega
  -- `S` is a cast of an element of `F`
  obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p K).mp hSmem
  have hSmap : S = algebraMap F K (n : F) := by
    rw [← hn]; exact (map_intCast (algebraMap F K) n).symm
  have hkey' : (M.roots.card : K) * α = algebraMap F K (-m.nextCoeff - (n : F)) := by
    rw [hkey, hSmap, map_sub, map_neg]
  -- hence `α` itself is the image of an element of `F`
  have hcardF : (M.roots.card : K) = algebraMap F K (m.natDegree : F) := by
    rw [hcard, ← map_natCast (algebraMap F K) m.natDegree]
  have hcastK : algebraMap F K (m.natDegree : F) ≠ 0 := by
    simpa using (algebraMap F K).injective.ne hdneF
  let x : F := (-m.nextCoeff - (n : F)) * (m.natDegree : F)⁻¹
  have hαmap : algebraMap F K x = α := by
    dsimp only [x]
    have hmul : algebraMap F K (m.natDegree : F)
          * algebraMap F K ((-m.nextCoeff - (n : F)) * (m.natDegree : F)⁻¹)
        = algebraMap F K (m.natDegree : F) * α := by
      rw [← map_mul, ← hcardF, hkey']
      congr 1
      field_simp
    exact mul_left_cancel₀ hcastK hmul
  have hx : α ^ p - α = algebraMap F K (x ^ p - x) := by
    rw [← hαmap, map_sub, map_pow]
  exact h x ((algebraMap F K).injective (by rw [← hx, hαeq]))

end Work.ClassBCD.RatFunc
