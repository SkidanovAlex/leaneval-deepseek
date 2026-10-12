import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseB4.Split_ann_excited
import Submission.Work.BoseB4.Split_cre_excited
import Submission.Work.BoseB4.Split_inner
import Submission.Work.BoseB4.annC_creC_ccr
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.inner_annC_creC` — creation is the adjoint of annihilation on `cfock X`

`Work.BoseB4.CFock` presents the complex Fock core `(X →₀ ℕ) →₀ ℂ` as a submodule
`cfock X` of `ℓ²(X →₀ ℕ)` (so that it inherits `InnerProductSpace ℂ`) and defines the
two ladder operators of a mode `i` on it, `annC X i` (annihilation) and `creC X i`
(creation).  This file proves that the latter is the **Hilbert adjoint** of the former,

    `⟪a_i u, v⟫ = ⟪u, a_i† v⟫`   for all `u v : cfock X`,

i.e. `inner ℂ (annC X i u) v = inner ℂ u (creC X i v)` — the ℓ² formulation of the
`Finsupp`-level commutation computation of `Work.BoseB4.annC_creC_ccr`, and the
companion of the condensate statement `Work.BoseB4.adjoint_a0`.

## Proof

`toCFock X : ((X →₀ ℕ) →₀ ℂ) ≃ₗ[ℂ] cfock X` is a linear equivalence, so it suffices to
prove the identity on its image: `u = toCFock X f`, `v = toCFock X g`.  Under it the two
operators become the explicit `Finsupp` maps `annF`, `creF` (`annC_toCFock`,
`creC_toCFock`), and the pairing on `cfock X` is the ℓ² pairing of the corresponding
`toLp`-images (`Submodule.coe_inner`, `toCFock_coe`).

Both sides are additive in `f` and in `g`, so the two `Finsupp.induction_linear`
principles (`key` below) reduce the identity to its value on pairs of basis vectors
(`pair` below).  There, `toLp_single` and

  `annF i (single γ c) = (c √(γ_i)) • single (γ - e_i)`,
  `creF i (single δ d) = (d √(δ_i + 1)) • single (δ + e_i)`

turn the two sides into the two complex numbers

  `d · √(γ_i)`   (non-zero only when `δ = γ - e_i`)   and
  `d · √(δ_i + 1)`   (non-zero only when `γ = δ + e_i`),

which agree: `δ = γ - e_i` forces `δ_i + 1 = γ_i` as soon as `γ_i ≠ 0`, and the remaining
degenerate case `γ_i = 0` has the weight `√0 = 0` on the left (so the left side vanishes)
and mismatched index shifts on the right (`γ ≠ γ + e_i`).  In the `i ≠ j`-free setting
here there is no index confusion; all weights are real, so complex conjugation (which
`inner` applies to its *first* argument) does not change them.

## Layout

* `sqc`/`sqc1` — the two Fock weights as complex numbers, with their basic facts
  (`sqc_zero`, `star_sqc`, `sqc_succ_eq`);
* `annF_single`/`creF_single`, `toLp_annF_single`/`toLp_creF_single` — the ladder
  operators and `toLp` on basis vectors;
* index-shift lemmas for `γ ± e_i` (`tsub_add_single`, `tsub_eq_self`,
  `tsub_eq_of_add_single`, `add_single_ne_self`);
* `pair` — the basis-vector case of the adjointness identity;
* `key` — the identity on `toLp`-images for arbitrary `f g`;
* `inner_annC_creC` — the statement, transported back to `cfock X`.
-/

noncomputable section

open scoped lp

namespace Work.BoseBoxFock.Adj

open Work.BoseB4

/-! ## 1. The Fock weights -/

/-- The annihilation weight `√n` of `Work.BoseB4.annF`, as a complex number. -/
def sqc (n : ℕ) : ℂ := (Real.sqrt (n : ℝ) : ℂ)

/-- The creation weight `√(n+1)` of `Work.BoseB4.creF`, as a complex number. -/
def sqc1 (n : ℕ) : ℂ := (Real.sqrt ((n : ℝ) + 1) : ℂ)

lemma sqc_zero : sqc 0 = 0 := by simp [sqc]

/-- The weights are real, so `inner`'s complex conjugation fixes them. -/
lemma star_sqc (n : ℕ) : (starRingEnd ℂ) (sqc n) = sqc n := by simp [sqc]

/-- `sqc (n+1) = sqc1 n`: raising the occupation by one turns the annihilation weight
into the creation weight.  This is where the `√(γ_i) = √((γ - e_i)_i + 1)` of the proof
below comes from. -/
lemma sqc_succ_eq (n : ℕ) : sqc (n + 1) = sqc1 n := by
  have h : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  simp only [sqc, sqc1, h]

variable {X : Type*} [DecidableEq X]

/-! ## 2. The ladder operators on basis vectors -/

/-- `annF i` on a basis vector: it lowers the `i`-occupation, gaining the weight
`√(γ_i)`. -/
lemma annF_single' (i : X) (γ : X →₀ ℕ) (c : ℂ) :
    annF X i (Finsupp.single γ c)
      = (c * sqc (γ i)) • Finsupp.single (γ - Finsupp.single i 1) (1 : ℂ) := by
  simp only [annF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul, sqc]

/-- `creF i` on a basis vector: it raises the `i`-occupation, gaining the weight
`√(γ_i + 1)`. -/
lemma creF_single' (i : X) (γ : X →₀ ℕ) (c : ℂ) :
    creF X i (Finsupp.single γ c)
      = (c * sqc1 (γ i)) • Finsupp.single (γ + Finsupp.single i 1) (1 : ℂ) := by
  simp only [creF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, smul_smul, sqc1]

/-- The same for the image in `ℓ²`: `annF` of a basis vector is the corresponding
`lp.single`. -/
lemma toLp_annF_single (i : X) (γ : X →₀ ℕ) (c : ℂ) :
    toLp X (annF X i (Finsupp.single γ c))
      = lp.single 2 (γ - Finsupp.single i 1) (c * sqc (γ i)) := by
  rw [annF_single', Finsupp.smul_single, smul_eq_mul, mul_one, toLp_single]

/-- The same for `creF`. -/
lemma toLp_creF_single (i : X) (δ : X →₀ ℕ) (d : ℂ) :
    toLp X (creF X i (Finsupp.single δ d))
      = lp.single 2 (δ + Finsupp.single i 1) (d * sqc1 (δ i)) := by
  rw [creF_single', Finsupp.smul_single, smul_eq_mul, mul_one, toLp_single]

/-! ## 3. Index shifts of a multi-index by `± e_i` -/

/-- Raising the `i`-th occupation of `γ - e_i` recovers `γ`, provided `γ_i ≠ 0`. -/
lemma tsub_add_single (i : X) (γ : X →₀ ℕ) (h : γ i ≠ 0) :
    (γ - Finsupp.single i 1) + Finsupp.single i 1 = γ := by
  ext k
  simp only [Finsupp.add_apply, Finsupp.tsub_apply]
  by_cases hk : k = i
  · subst hk
    rw [Finsupp.single_eq_same]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h)
  · rw [Finsupp.single_eq_of_ne hk]; simp

/-- If the `i`-th occupation vanishes, lowering it is a no-op. -/
lemma tsub_eq_self (i : X) (γ : X →₀ ℕ) (h : γ i = 0) :
    γ - Finsupp.single i 1 = γ := by
  ext k
  by_cases hk : k = i
  · subst hk; simp [Finsupp.tsub_apply, Finsupp.single_eq_same, h]
  · rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hk, tsub_zero]

/-- Conversely, if `γ = δ + e_i`, then `γ` has a quantum in the mode `i` to lower:
`γ - e_i = δ`. -/
lemma tsub_eq_of_add_single_adj (i : X) {γ δ : X →₀ ℕ} (h : γ = δ + Finsupp.single i 1) :
    γ - Finsupp.single i 1 = δ := by
  ext k
  by_cases hk : k = i
  · subst hk
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same, h, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  · rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hk, tsub_zero, h, Finsupp.add_apply,
      Finsupp.single_eq_of_ne hk, add_zero]

omit [DecidableEq X] in
/-- Raising an occupation always changes the multi-index. -/
lemma add_single_ne_self (i : X) (γ : X →₀ ℕ) : γ ≠ γ + Finsupp.single i 1 := by
  intro h
  have hc := congrArg (fun f : X →₀ ℕ => f i) h
  rw [Finsupp.add_apply, Finsupp.single_eq_same] at hc
  exact Nat.succ_ne_self (γ i) hc.symm

/-! ## 4. The basis-vector case -/

/-- **The adjointness identity on a pair of basis vectors.**  `annF i` moves the
occupation of the mode `i` down (weight `√(γ_i)`), `creF i` moves it up (weight
`√(δ_i + 1)`); the two pairings are computed by the orthonormality of the ℓ² basis
vectors and agree by `sqc_succ_eq`, the degenerate case `γ_i = 0` being annihilated by
the vanishing weight `√0 = 0`. -/
lemma pair (i : X) (γ δ : X →₀ ℕ) (c d : ℂ) :
    inner ℂ (toLp X (annF X i (Finsupp.single γ c))) (toLp X (Finsupp.single δ d))
      = inner ℂ (toLp X (Finsupp.single γ c)) (toLp X (creF X i (Finsupp.single δ d))) := by
  rw [toLp_annF_single, toLp_creF_single, toLp_single, toLp_single,
      lp.inner_single_left, lp.inner_single_left, lp.coeFn_single, lp.coeFn_single,
      Pi.single_apply, Pi.single_apply, RCLike.inner_apply, RCLike.inner_apply,
      map_mul, star_sqc]
  -- goal: `(if γ - e_i = δ then d else 0) * (star c * √(γ_i))
  --        = (if γ = δ + e_i then d * √(δ_i + 1) else 0) * star c`
  by_cases h : γ - Finsupp.single i 1 = δ
  · rw [if_pos h]
    by_cases hγ : γ i = 0
    · -- `γ` has no quantum in the mode `i`: the lowering weight vanishes.
      have hδ : δ = γ := by rw [← h]; exact tsub_eq_self i γ hγ
      have hne : ¬ (γ = δ + Finsupp.single i 1) := by rw [hδ]; exact add_single_ne_self i γ
      rw [if_neg hne]
      simp [hγ, sqc_zero]
    · -- the generic case: `γ = δ + e_i` and `δ_i + 1 = γ_i`.
      have hγ' : γ = δ + Finsupp.single i 1 := by rw [← h, tsub_add_single i γ hγ]
      rw [if_pos hγ']
      have hs : sqc1 (δ i) = sqc (γ i) := by
        rw [← h, Finsupp.tsub_apply, Finsupp.single_eq_same, ← sqc_succ_eq (γ i - 1),
            Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hγ)]
      rw [hs]
      ring
  · -- neither side can shift into the other basis vector.
    have hne : ¬ (γ = δ + Finsupp.single i 1) :=
      fun hh => h (tsub_eq_of_add_single_adj i hh)
    rw [if_neg h, if_neg hne]
    simp

/-! ## 5. Assembly: additivity in both arguments -/

/-- `creC` is the image of `creF` under `toCFock`. -/
lemma creC_toCFock' (i : X) (g : (X →₀ ℕ) →₀ ℂ) :
    creC X i (toCFock X g) = toCFock X (creF X i g) := by simp [creC]

/-- **The adjointness identity on the `toLp`-images**, for arbitrary `f g`.  Induction on
`f` (the argument the left-hand side annihilates) using additivity of the pairing, then
on `g`, reduces everything to `pair`. -/
lemma key (i : X) (f g : (X →₀ ℕ) →₀ ℂ) :
    inner ℂ (toLp X (annF X i f)) (toLp X g)
      = inner ℂ (toLp X f) (toLp X (creF X i g)) := by
  revert g
  induction f using Finsupp.induction_linear with
  | zero => intro g; simp
  | add f₁ f₂ h₁ h₂ =>
      intro g
      simp only [map_add, inner_add_left]
      rw [h₁ g, h₂ g]
  | single γ c =>
      intro g
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add g₁ g₂ k₁ k₂ =>
          simp only [map_add, inner_add_right]
          rw [k₁, k₂]
      | single δ d => exact pair i γ δ c d

end Work.BoseBoxFock.Adj

namespace Work.BoseBoxFock

open Work.BoseB4

theorem inner_annC_creC {X : Type*} [DecidableEq X] (i : X)
    (u v : Work.BoseB4.cfock X) :
    inner ℂ (Work.BoseB4.annC X i u) v = inner ℂ u (Work.BoseB4.creC X i v) := by
  obtain ⟨f, rfl⟩ := (toCFock X).surjective u
  obtain ⟨g, rfl⟩ := (toCFock X).surjective v
  rw [annC_toCFock, Adj.creC_toCFock', Submodule.coe_inner, Submodule.coe_inner,
    toCFock_coe, toCFock_coe, toCFock_coe, toCFock_coe]
  exact Adj.key i f g

end Work.BoseBoxFock
