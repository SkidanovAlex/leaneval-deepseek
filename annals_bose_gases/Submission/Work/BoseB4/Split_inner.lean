import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseB4.Split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Split_inner` — `split` is an isometry onto the Bombieri-normalised core

The mode-lattice Fock space `Work.BoseB4.RealFock m` carries the Bombieri form
`bomb m p q = Σ_α p_α q_α α!`, in which the *normalised* monomials `x^α/√(α!)`
are orthonormal; the abstract §8 carrier `FockCore (cfock (Excited m))` carries
its ℓ² inner product `coreInner`.  The mode-lattice split
`Work.BoseB4.split` — with its weight `√((α 0)! (α|₀)!)` — intertwines the two:

    `coreInner (split p) (split q) = bomb m p q`.

This is the `ℓ²`-form of the statement that `Work.BoseB4.split` identifies the
mode lattice with the abstract second-quantisation carrier `FockCore (cfock _)`,
and it is the identity that lets FS's `thm:Kafz` (proved abstractly in
`Submission/Work/BoseB4/Kafz_sum.lean`) be read on the mode lattice
(`Submission/Work/BoseB4/KafzLattice.lean`).

The proof is a two-variable `Finsupp.induction_linear`: `split` is the
`Finsupp.lsum` of the basis vectors `x^α ↦ √(α 0)! (α|₀)! · e_{α 0} ⊗ |α|₀⟩`,
whose mutual inner products are `δ_{αβ} α!` by the factorisation
`α! = (α 0)! · (α|₀)!` of the multi-index factorial.
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

variable {m : ℕ} [NeZero m]

/-! ## 1. The image of a basis vector -/

/-- The excited-mode factor `√(α 0)! (α|₀)! · |α|₀⟩` of the image of `x^α`. -/
noncomputable def splitInnerC (α : Fin m →₀ ℕ) : cfock (Excited m) :=
  toCFock (Excited m)
    (Finsupp.single (restOf α) (((fockW (α 0) (restOf α)) : ℝ) : ℂ))

/-- The image of the mode-lattice basis vector `x^α` under `split`. -/
noncomputable def splitInnerB (α : Fin m →₀ ℕ) : FockCore (cfock (Excited m)) :=
  Finsupp.single (α 0) (splitInnerC α)

lemma splitInnerB_eq (α : Fin m →₀ ℕ) :
    splitInnerB α = Finsupp.single (α 0) (splitInnerC α) := rfl

/-- `split` is the `Finsupp.lsum` of the basis vectors `splitInnerB`. -/
lemma split_single (α : Fin m →₀ ℕ) (a : ℝ) :
    split (Finsupp.single α a) = a • splitInnerB α := by
  simp [split, splitInnerB, splitInnerC, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-! ## 2. The multi-index factorial factorises -/

/-- `α! = (α 0)! · (α|₀)!`: the factorial of a multi-index splits off the
condensate mode. -/
lemma mfac_factor (α : Fin m →₀ ℕ) : mfac α = ((α 0).factorial : ℝ) * mfacG (restOf α) := by
  have h1 : α.filter (fun l : Fin m => l = 0) = Finsupp.single 0 (α 0) := by
    ext x
    by_cases h : x = 0 <;> simp [h]
  have h2 : (α.filter (fun l : Fin m => ¬ l = 0)).subtypeDomain (fun j : Fin m => j ≠ 0)
      = restOf α := by
    ext j
    simp only [restOf, Finsupp.subtypeDomain_apply]
    exact Finsupp.filter_apply_pos (f := α) (p := fun l : Fin m => ¬ l = 0) j.2
  have h3 : mfacG (restOf α)
      = (α.filter (fun l : Fin m => ¬ l = 0)).prod (fun _ k => (k.factorial : ℝ)) := by
    rw [mfacG, ← h2]
    exact Finsupp.prod_subtypeDomain_index (h := fun _ k => (k.factorial : ℝ))
      (p := fun j : Fin m => j ≠ 0) (v := α.filter (fun l : Fin m => ¬ l = 0)) (by
        intro x hx hx0
        refine (Finsupp.mem_support_iff.mp hx) ?_
        rw [hx0]
        exact Finsupp.filter_apply_neg (f := α) (p := fun l : Fin m => ¬ l = 0) (by simp))
  have h4 := Finsupp.prod_filter_mul_prod_filter_not (p := fun l : Fin m => l = 0)
    α (fun _ k => (k.factorial : ℝ))
  rw [mfac, ← h4, h1, ← h3]
  rw [Finsupp.prod_single_index (by simp)]

lemma mfacG_nonneg (β : Excited m →₀ ℕ) : 0 ≤ mfacG β := by
  rw [mfacG]
  exact Finset.prod_nonneg fun _ _ => by positivity

/-- The weight `fockW` squares to the factorial weight. -/
lemma fockW_mul_self (n : ℕ) (β : Excited m →₀ ℕ) :
    fockW n β * fockW n β = (n.factorial : ℝ) * mfacG β := by
  rw [fockW, Real.mul_self_sqrt]
  exact mul_nonneg (by positivity) (mfacG_nonneg β)

/-! ## 3. Inner products on the abstract carrier -/

/-- Distinct condensate levels are orthogonal; on a level the inner product is
the spectators' one. -/
lemma inner_level_of (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n m : ℕ) (v w : E) :
    inner ℂ (level E n v) (level E m w) = if n = m then inner ℂ v w else 0 := by
  rw [show level E n v = lp.single 2 n v from by simp [level],
      show level E m w = lp.single 2 m w from by simp [level],
      lp.inner_single_left, lp.single_apply, Pi.single_apply]
  by_cases h : n = m <;> simp [h]

/-- The canonical inclusion of the complex Fock core into `ℓ²`. -/
lemma toCFock_coe {X : Type*} [DecidableEq X] (f : (X →₀ ℕ) →₀ ℂ) :
    (↑(toCFock X f) : lp (fun _ : X →₀ ℕ => ℂ) 2) = toLp X f := rfl

/-- `toLp` sends a basis vector to the corresponding `ℓ²` basis vector. -/
lemma toLp_single {X : Type*} [DecidableEq X] (β : X →₀ ℕ) (c : ℂ) :
    toLp X (Finsupp.single β c) = lp.single 2 β c := by
  simp only [toLp]
  rw [Finsupp.lsum_single]
  exact lp.singleContinuousLinearMap_apply (E := fun _ : X →₀ ℕ => ℂ) β c

/-- The basis vectors of `cfock X` are orthonormal for the ℓ² inner product. -/
lemma inner_toCFock_single {X : Type*} [DecidableEq X] (β β' : X →₀ ℕ) (c c' : ℂ) :
    inner ℂ (toCFock X (Finsupp.single β c)) (toCFock X (Finsupp.single β' c'))
      = if β = β' then (starRingEnd ℂ) c * c' else 0 := by
  rw [Submodule.coe_inner, toCFock_coe, toCFock_coe, toLp_single, toLp_single,
    lp.inner_single_left, lp.single_apply, Pi.single_apply]
  by_cases h : β = β'
  · rw [if_pos h, if_pos h, RCLike.inner_apply, mul_comm]
  · rw [if_neg h, if_neg h, inner_zero_right]

/-! ## 4. Bilinearity of `coreInner` over `ℝ` -/

lemma coreInner_add_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ψ Ψ' Ψ'' : FockCore E) :
    coreInner (Ψ + Ψ') Ψ'' = coreInner Ψ Ψ'' + coreInner Ψ' Ψ'' := by
  simp only [coreInner, map_add, inner_add_left]

lemma coreInner_add_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ψ Ψ' Ψ'' : FockCore E) :
    coreInner Ψ (Ψ' + Ψ'') = coreInner Ψ Ψ' + coreInner Ψ Ψ'' := by
  simp only [coreInner, map_add, inner_add_right]

lemma coreInner_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b : ℝ) (Ψ Ψ' : FockCore E) :
    coreInner (a • Ψ) (b • Ψ') = ((a : ℝ) : ℂ) * (((b : ℝ) : ℂ) * coreInner Ψ Ψ') := by
  simp only [coreInner]
  rw [← Complex.coe_smul a Ψ, ← Complex.coe_smul b Ψ', map_smul, map_smul,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]

/-! ## 5. `bomb` on a basis vector -/

omit [NeZero m] in
/-- The Bombieri form on a basis vector of the mode lattice. -/
lemma bomb_single_split (α : Fin m →₀ ℕ) (a : ℝ) (q : RealFock m) :
    bomb m (Finsupp.single α a) q = a * (mfac α * q α) := by
  simp [bomb, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.lapply_apply]

/-! ## 6. The basis vectors are orthonormal -/

lemma eq_of_restOf_eq {α β : Fin m →₀ ℕ} (h0 : α 0 = β 0) (h : restOf α = restOf β) :
    α = β := by
  ext l
  by_cases hl : l = 0
  · subst hl; exact h0
  · have hh := congrArg (fun f : Excited m →₀ ℕ => f ⟨l, hl⟩) h
    simpa [restOf, Finsupp.subtypeDomain_apply] using hh

lemma inner_splitInnerC (α β : Fin m →₀ ℕ) :
    inner ℂ (splitInnerC α) (splitInnerC β)
      = if restOf α = restOf β
          then (((fockW (α 0) (restOf α)) * (fockW (β 0) (restOf β)) : ℝ) : ℂ) else 0 := by
  rw [splitInnerC, splitInnerC, inner_toCFock_single]
  by_cases h : restOf α = restOf β
  · rw [if_pos h, if_pos h, Complex.conj_ofReal, ← Complex.ofReal_mul]
  · rw [if_neg h, if_neg h]

/-- The images of distinct basis vectors are orthogonal, and the image of `x^α`
has squared norm `α!`. -/
lemma coreInner_splitInnerB (α β : Fin m →₀ ℕ) :
    coreInner (splitInnerB α) (splitInnerB β) = if α = β then ((mfac α : ℝ) : ℂ) else 0 := by
  have hA : Embed (cfock (Excited m)) (splitInnerB α)
      = level (cfock (Excited m)) (α 0) (splitInnerC α) := by
    rw [splitInnerB_eq]
    exact Embed_single (E := cfock (Excited m)) (α 0) (splitInnerC α)
  have hB : Embed (cfock (Excited m)) (splitInnerB β)
      = level (cfock (Excited m)) (β 0) (splitInnerC β) := by
    rw [splitInnerB_eq]
    exact Embed_single (E := cfock (Excited m)) (β 0) (splitInnerC β)
  rw [coreInner, hA, hB, inner_level_of]
  by_cases h : α = β
  · subst h
    rw [if_pos rfl, if_pos rfl, inner_splitInnerC, if_pos rfl, fockW_mul_self,
      ← mfac_factor]
  · rw [if_neg h]
    by_cases h0 : α 0 = β 0
    · have hr : restOf α ≠ restOf β := fun hr => h (eq_of_restOf_eq h0 hr)
      rw [if_pos h0, inner_splitInnerC, if_neg hr]
    · rw [if_neg h0]

/-! ## 7. The assembly -/

/-- Both sides as functions of `(p, q)` are `ℝ`-bilinear and agree on the basis
vectors `Finsupp.single α 1`; hence they agree everywhere. -/
lemma splitInner_key : ∀ p : RealFock m, ∀ q : RealFock m,
    coreInner (split p) (split q) = ((bomb m p q : ℝ) : ℂ) := by
  intro p
  induction p using Finsupp.induction_linear with
  | zero => intro q; simp [coreInner]
  | add f g hf hg =>
      intro q
      rw [map_add, map_add, coreInner_add_left, LinearMap.add_apply, hf q, hg q,
        ← Complex.ofReal_add]
  | single α a =>
      intro q
      induction q using Finsupp.induction_linear with
      | zero => simp [coreInner]
      | add u v hu hv =>
          rw [map_add, map_add, coreInner_add_right, hu, hv, ← Complex.ofReal_add]
      | single β b =>
          rw [split_single, split_single, bomb_single_split]
          trans ((a : ℝ) : ℂ) * (((b : ℝ) : ℂ) * coreInner (splitInnerB α) (splitInnerB β))
          · exact coreInner_smul (E := cfock (Excited m)) a b _ _
          · rw [coreInner_splitInnerB]
            by_cases h : α = β
            · subst h
              rw [if_pos rfl, Finsupp.single_eq_same]
              push_cast
              ring
            · rw [if_neg h, Finsupp.single_eq_of_ne h]
              simp

theorem Split_inner {m : ℕ} [NeZero m] (p q : Work.BoseB4.RealFock m) :
    Work.BoseB4.coreInner (Work.BoseB4.split p) (Work.BoseB4.split q) = Work.BoseB4.bomb m p q := by
  exact splitInner_key p q

end Work.BoseB4
