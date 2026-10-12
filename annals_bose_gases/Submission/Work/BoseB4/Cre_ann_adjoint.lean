import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB4.RealFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Cre_ann_adjoint` — `a_l† = (a_l)*` for the Bombieri form

On the real bosonic Fock space `RealFock m = (Fin m →₀ ℕ) →₀ ℝ` (monomial
coefficients, `bomb` the Bombieri form `⟪p,q⟫ = Σ_α p_α q_α α!`) the creation
operator `cre m l` (multiplication by `x_l`) is the `bomb`-adjoint of the
annihilation operator `ann m l` (`∂/∂x_l`):

    bomb m (cre m l p) q = bomb m p (ann m l q).

The proof is by linearity in `p` (`Finsupp.induction_linear`), reducing to the
basis elements `Finsupp.single α c`, for which all four quantities are computed
explicitly:

* `bomb m (Finsupp.single α c) q = c * mfac α * q α` (`bomb_single`);
* `cre m l (Finsupp.single α c) = Finsupp.single (α + e m l) c` (`cre_single`);
* `ann m l q α = (α l + 1) * q (α + e m l)` (`ann_apply`);
* `mfac (α + e m l) = (α l + 1) * mfac α` (`mfac_add_e`, the weight `α!` gains
  the factor `α l + 1` when the `l`-th occupation is raised).

The only non-trivial bookkeeping is the truncated subtraction on multi-indices
(`Finsupp.tsub`): `ann` shifts `d` down from `α + e_l` to `α`, and the extra
contribution coming from the truncation has vanishing weight (`tsub_e_eq`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-! ## 1. The Bombieri form on basis vectors -/

/-- `bomb` against a basis vector in the first argument. -/
lemma bomb_single {m : ℕ} (α : Fin m →₀ ℕ) (c : ℝ) (q : RealFock m) :
    bomb m (Finsupp.single α c) q = c * mfac α * q α := by
  simp only [bomb, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul]
  ring

/-- `bomb` against a basis vector in the second argument. -/
lemma bomb_single_right {m : ℕ} (β : Fin m →₀ ℕ) (d : ℝ) (r : RealFock m) :
    bomb m r (Finsupp.single β d) = d * mfac β * r β := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [map_add, LinearMap.add_apply, Finsupp.add_apply]
      rw [hf, hg]
      ring
  | single γ e =>
      rw [bomb_single]
      by_cases h : γ = β
      · subst h
        simp [mul_comm, mul_left_comm]
      · rw [Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne (Ne.symm h)]
        ring

/-! ## 2. Creation on a basis vector -/

/-- `cre m l` raises the `l`-th occupation by one; on a basis vector it is the
basis vector at the shifted multi-index. -/
lemma cre_single {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) (c : ℝ) :
    cre m l (Finsupp.single α c) = Finsupp.single (α + e m l) c := by
  rw [cre, Finsupp.lsum_single]
  rfl

/-! ## 3. The weight `mfac` under the shift `α ↦ α + e_l` -/

/-- `mfac` as a product over all coordinates (`0! = 1` kills the complement of
the support). -/
lemma mfac_eq_prod {m : ℕ} (α : Fin m →₀ ℕ) :
    mfac α = ∏ x : Fin m, ((α x).factorial : ℝ) := by
  rw [mfac, Finsupp.prod_fintype α (fun _ k => (k.factorial : ℝ)) (by intro i; simp)]

/-- Raising the `l`-th occupation multiplies the weight `α!` by `α l + 1`. -/
lemma mfac_add_e {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) :
    mfac (α + e m l) = ((α l : ℝ) + 1) * mfac α := by
  rw [mfac_eq_prod, mfac_eq_prod]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin m))
        (fun x => (((α + e m l) x).factorial : ℝ)) (Finset.mem_univ l),
      ← Finset.mul_prod_erase (Finset.univ : Finset (Fin m))
        (fun x => ((α x).factorial : ℝ)) (Finset.mem_univ l)]
  have hl : (α + e m l) l = α l + 1 := by
    rw [Finsupp.add_apply, e, Finsupp.single_eq_same]
  have hP : (∏ x ∈ Finset.univ.erase l, (((α + e m l) x).factorial : ℝ))
      = ∏ x ∈ Finset.univ.erase l, ((α x).factorial : ℝ) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finset.mem_erase] at hx
    obtain ⟨hxl, -⟩ := hx
    rw [Finsupp.add_apply, e, Finsupp.single_eq_of_ne hxl, add_zero]
  have hfac : ((α l + 1).factorial : ℝ) = ((α l : ℝ) + 1) * ((α l).factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hl, hfac, hP]
  ring

/-! ## 4. Annihilation on a basis vector -/

/-- The truncated subtraction undoes the addition of `e m l`. -/
lemma add_e_tsub_e {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) :
    (α + e m l) - e m l = α := by
  ext x
  by_cases hx : x = l <;> simp [e, hx]

/-- `β - e m l = α` forces `β` to be either `α + e m l` or `α` itself; in the
latter case the `l`-th coordinate of `β` vanishes, which is why the truncated
branch carries weight zero in `ann_apply`. -/
lemma tsub_e_eq {m : ℕ} {l : Fin m} {β α : Fin m →₀ ℕ} (h : β - e m l = α) :
    β = α + e m l ∨ (β = α ∧ β l = 0) := by
  have hl : β l - 1 = α l := by
    have := congrArg (fun f : Fin m →₀ ℕ => f l) h
    simpa [Finsupp.tsub_apply, e, Finsupp.single_eq_same] using this
  have hx : ∀ x, x ≠ l → β x = α x := by
    intro x hxl
    have := congrArg (fun f : Fin m →₀ ℕ => f x) h
    simpa [Finsupp.tsub_apply, e, Finsupp.single_eq_of_ne hxl] using this
  rcases eq_or_ne (β l) 0 with h0 | hne
  · right
    refine ⟨Finsupp.ext fun x => ?_, h0⟩
    by_cases hxl : x = l
    · subst hxl; omega
    · exact hx x hxl
  · left
    refine Finsupp.ext fun x => ?_
    by_cases hxl : x = l
    · subst hxl
      simp only [Finsupp.add_apply, e, Finsupp.single_eq_same]
      omega
    · rw [Finsupp.add_apply, e, Finsupp.single_eq_of_ne hxl, add_zero]
      exact hx x hxl

/-- `ann m l` as an explicit weighted shift of the coefficients. -/
lemma ann_eq_sum {m : ℕ} (l : Fin m) (q : RealFock m) :
    ann m l q = q.sum (fun γ c => (c * (γ l : ℝ)) • Finsupp.single (γ - e m l) (1:ℝ)) := by
  rw [ann, Finsupp.lsum_apply]
  refine Finsupp.sum_congr fun γ _ => ?_
  rw [LinearMap.toSpanSingleton_apply, smul_smul]

/-- The explicit coefficient of `ann m l q`: the `l`-th occupation is lowered by
one and the coefficient is multiplied by the *old* occupation `α l + 1`. -/
lemma ann_apply {m : ℕ} (l : Fin m) (q : RealFock m) (α : Fin m →₀ ℕ) :
    ann m l q α = ((α l : ℝ) + 1) * q (α + e m l) := by
  rw [ann_eq_sum, Finsupp.sum_apply]
  rw [Finsupp.sum_eq_single (α + e m l)]
  · rw [Finsupp.smul_apply, add_e_tsub_e, Finsupp.single_eq_same, Finsupp.add_apply, e,
      Finsupp.single_eq_same]
    push_cast
    ring
  · intro b hb hne
    by_cases h : b - e m l = α
    · rcases tsub_e_eq h with hb' | ⟨hb', hbl⟩
      · exact absurd hb' hne
      · subst hb'
        rw [hbl]
        simp
    · rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (Ne.symm h), smul_zero]
  · intro _
    simp

/-! ## 5. The adjointness -/

theorem Cre_ann_adjoint {m : ℕ} (l : Fin m) (p q : Work.BoseB4.RealFock m) :
    Work.BoseB4.bomb m (Work.BoseB4.cre m l p) q
      = Work.BoseB4.bomb m p (Work.BoseB4.ann m l q) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [map_add, LinearMap.add_apply]
      rw [hf, hg]
  | single α c =>
      rw [cre_single, bomb_single, bomb_single, ann_apply, mfac_add_e]
      ring

end Work.BoseB4
