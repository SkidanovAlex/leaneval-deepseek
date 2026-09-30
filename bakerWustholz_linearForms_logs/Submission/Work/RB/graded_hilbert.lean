import Mathlib
import Submission.Work.RB.Defs
import Submission.Work.RB.eventuallyPoly_of_diffs
import Submission.Work.RB.hilb_add_X
import Submission.Work.RB.hilb_reduce
import Submission.Work.RB.weightedHomogeneousComponent_monomial
import Submission.Work.RB.isWHomog_colon
import Submission.Work.RB.isWHomog_sup_span_X

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RB

open MvPolynomial

noncomputable section

variable {n : ℕ}

/-! ## Elementary helpers -/

/-- Evaluation after substitution: `(aeval f P).eval x = P.eval (fun j => (f j).eval x)`. -/
theorem eval_aeval_apply (f : Fin n → MvPolynomial (Fin n) ℚ) (x : Fin n → ℚ)
    (P : MvPolynomial (Fin n) ℚ) :
    (MvPolynomial.aeval f P).eval x = P.eval (fun j => (f j).eval x) := by
  have h2 : (MvPolynomial.aeval x).comp (MvPolynomial.aeval f)
      = MvPolynomial.aeval (fun j => (f j).eval x) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rfl
  calc (MvPolynomial.aeval f P).eval x
      = MvPolynomial.aeval x (MvPolynomial.aeval f P) := rfl
    _ = ((MvPolynomial.aeval x).comp (MvPolynomial.aeval f)) P := rfl
    _ = MvPolynomial.aeval (fun j => (f j).eval x) P := by rw [h2]
    _ = P.eval (fun j => (f j).eval x) := rfl

/-- Substitution decreasing the `i`-th variable by one. -/
def shiftP (i : Fin n) (P : MvPolynomial (Fin n) ℚ) : MvPolynomial (Fin n) ℚ :=
  MvPolynomial.aeval (fun j => if j = i then MvPolynomial.X j - 1 else MvPolynomial.X j) P

theorem shiftP_eval {i : Fin n} (P : MvPolynomial (Fin n) ℚ) {d : Fin n →₀ ℕ} (hd : 1 ≤ d i) :
    (shiftP i P).eval (fun j => (d j : ℚ)) =
      P.eval (fun j => (((d - (Finsupp.single i 1 : Fin n →₀ ℕ)) j : ℕ) : ℚ)) := by
  have hassgn : (fun j => (MvPolynomial.eval (fun j => (d j : ℚ)))
        (if j = i then MvPolynomial.X j - 1 else MvPolynomial.X j))
      = (fun j => (((d - (Finsupp.single i 1 : Fin n →₀ ℕ)) j : ℕ) : ℚ)) := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl]
      simp only [MvPolynomial.eval_sub, MvPolynomial.eval_X, map_one]
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.cast_sub hd]
      norm_num
    · rw [if_neg hj]
      simp only [MvPolynomial.eval_X]
      rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hj, tsub_zero]
  rw [shiftP,
    eval_aeval_apply (f := fun j => if j = i then MvPolynomial.X j - 1 else MvPolynomial.X j)
      (x := fun j => (d j : ℚ)), hassgn]

/-- Substitution increasing the `i`-th variable by one. -/
def upP (i : Fin n) (P : MvPolynomial (Fin n) ℚ) : MvPolynomial (Fin n) ℚ :=
  MvPolynomial.aeval (fun j => if j = i then MvPolynomial.X j + 1 else MvPolynomial.X j) P

theorem upP_eval {i : Fin n} (P : MvPolynomial (Fin n) ℚ) (d : Fin n →₀ ℕ) :
    (upP i P).eval (fun j => (d j : ℚ)) =
      P.eval (fun j => (((d + (Finsupp.single i 1 : Fin n →₀ ℕ)) j : ℕ) : ℚ)) := by
  have hassgn : (fun j => (MvPolynomial.eval (fun j => (d j : ℚ)))
        (if j = i then MvPolynomial.X j + 1 else MvPolynomial.X j))
      = (fun j => (((d + (Finsupp.single i 1 : Fin n →₀ ℕ)) j : ℕ) : ℚ)) := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl]
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_X, map_one]
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
    · rw [if_neg hj]
      simp only [MvPolynomial.eval_X]
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hj, add_zero]
  rw [upP,
    eval_aeval_apply (f := fun j => if j = i then MvPolynomial.X j + 1 else MvPolynomial.X j)
      (x := fun j => (d j : ℚ)), hassgn]

theorem tsub_single_add (q : Fin n →₀ ℕ) (i : Fin n) (h : 1 ≤ q i) :
    (q - (Finsupp.single i 1 : Fin n →₀ ℕ)) + Finsupp.single i 1 = q := by
  ext j
  rw [Finsupp.add_apply, Finsupp.tsub_apply]
  by_cases hj : j = i
  · subst hj; simp only [Finsupp.single_eq_same]; omega
  · simp only [Finsupp.single_eq_of_ne hj, tsub_zero, add_zero]

/-! ## Renaming along an injection is graded

We give a self-contained proof (the standalone module `weight_mapDomain`/`isWHomog_comap_rename`
is not imported here because of a name clash between agent-authored files). -/

theorem rb_weight_mapDomain {α β M : Type*} [AddCommMonoid M] (w : β → M) (f : α → β)
    (x : α →₀ ℕ) : Finsupp.weight w (Finsupp.mapDomain f x) = Finsupp.weight (w ∘ f) x := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply]
  exact Finsupp.sum_mapDomain_index (fun b => by simp) (fun b m₁ m₂ => by simp [add_smul])

theorem rb_rename_whc {σ τ M R : Type*} [CommSemiring R] [AddCommMonoid M] [DecidableEq M]
    (f : σ → τ) (w : τ → M) (n : M) (p : MvPolynomial σ R) :
    MvPolynomial.rename f (MvPolynomial.weightedHomogeneousComponent (fun a => w (f a)) n p) =
      MvPolynomial.weightedHomogeneousComponent w n (MvPolynomial.rename f p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
      by_cases h : Finsupp.weight (fun a => w (f a)) d = n
      · have e1 : MvPolynomial.weightedHomogeneousComponent (fun a => w (f a)) n
            (MvPolynomial.monomial d a) = MvPolynomial.monomial d a := by
          rw [weightedHomogeneousComponent_monomial, ite_eq_left h]
        have h' : Finsupp.weight w (Finsupp.mapDomain f d) = n := by
          rw [rb_weight_mapDomain w f d]; exact h
        have e2 : MvPolynomial.weightedHomogeneousComponent w n
            (MvPolynomial.monomial (Finsupp.mapDomain f d) a)
              = MvPolynomial.monomial (Finsupp.mapDomain f d) a := by
          rw [weightedHomogeneousComponent_monomial, ite_eq_left h']
        simp only [e1, MvPolynomial.rename_monomial, e2]
      · have e1 : MvPolynomial.weightedHomogeneousComponent (fun a => w (f a)) n
            (MvPolynomial.monomial d a) = 0 := by
          rw [weightedHomogeneousComponent_monomial, ite_eq_right h]
        have h' : ¬ (Finsupp.weight w (Finsupp.mapDomain f d) = n) := by
          rw [rb_weight_mapDomain w f d]; exact h
        have e2 : MvPolynomial.weightedHomogeneousComponent w n
            (MvPolynomial.monomial (Finsupp.mapDomain f d) a) = 0 := by
          rw [weightedHomogeneousComponent_monomial, ite_eq_right h']
        simp only [e1, MvPolynomial.rename_zero, MvPolynomial.rename_monomial, e2]
  | add p q hp hq =>
      simp only [map_add, hp, hq]

theorem rb_isWHomog_comap_rename {n : ℕ} {σ : Type*} [Fintype σ] (w : σ → Fin n →₀ ℕ) {v : σ}
    (J : Ideal (MvPolynomial σ ℂ)) (hJ : IsWHomog w J) :
    IsWHomog (fun x : {x : σ // x ≠ v} => w x.1)
      (Ideal.comap (MvPolynomial.rename (Subtype.val)) J) := by
  intro p hp d
  rw [Ideal.mem_comap] at hp ⊢
  rw [rb_rename_whc (Subtype.val) w d p]
  exact hJ _ hp d

/-! ## Degenerate graded pieces -/

theorem homPiece_eq_bot_of_weight_zero {σ : Type*} [Fintype σ] {w : σ → Fin n →₀ ℕ} {i : Fin n}
    (h : ∀ v : σ, (w v) i = 0) {d : Fin n →₀ ℕ} (hd : d i ≠ 0) : homPiece w d = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro p hp
  rw [mem_homPiece] at hp
  refine MvPolynomial.IsWeightedHomogeneous.eq_zero_of_no_monomials hp (fun m hm => ?_)
  have hzero : (Finsupp.weight w m) i = 0 := by
    rw [Finsupp.weight_apply, Finsupp.sum_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun v _ => ?_
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [h v, mul_zero]
  rw [hm] at hzero
  exact hd hzero

theorem hilb_eq_zero_of_no_var {σ : Type*} [Fintype σ] {w : σ → Fin n →₀ ℕ} {i : Fin n}
    (h : ∀ v : σ, (w v) i = 0) (I : Ideal (MvPolynomial σ ℂ)) {d : Fin n →₀ ℕ}
    (hd : d i ≠ 0) : hilb w I d = 0 := by
  rw [hilb, homPiece_eq_bot_of_weight_zero h hd]
  have key := Submodule.finrank_quotient_add_finrank
    (N := Submodule.comap (⊥ : Submodule ℂ (MvPolynomial σ ℂ)).subtype (I.restrictScalars ℂ))
  rw [finrank_bot] at key
  omega

/-! ## The main theorem -/

/-- **Multigraded Hilbert–Samuel** (fixed: the weights must be basis vectors, else the Hilbert
function is only a *quasi*-polynomial; see the counterexamples in review).

For a `w`-homogeneous ideal `I` of `R = MvPolynomial σ ℂ`, where every variable has weight a basis
vector `eᵢ`, the dimension over `ℂ` of the multigraded piece of `R/I` of multidegree `d` is, for all
`d` whose coordinates are all large enough, given by a polynomial in `d`.

Proof route: induction on the (finite) variable set `σ`.  Pick a variable `x = X v` of multidegree
`e`, and use the exact sequence of graded `R`-modules
`0 → (I : x)/I → R/I → R/I → R/(I + (x)) → 0`
(the middle map is multiplication by `x`).  Both outer modules are killed by `x`, hence are graded
modules over `MvPolynomial (σ \ {v}) ℂ` (e.g. via `MvPolynomial.optionEquivLeft` /
`MvPolynomial.finSuccEquiv` after removing the variable), and they are finitely generated; the
induction hypothesis (or a generalisation of it to finitely generated graded modules over the
subring) applies to them.  It then gives eventual polynomiality of the difference
`d ↦ dim (R/I)_d` in the `v`-coordinate, and partial sums of an eventually polynomial function are
eventually polynomial (express a polynomial as a combination of the binomial functions
`n ↦ n.choose k`, whose partial sums are `n ↦ (n+1).choose (k+1)`). -/
theorem graded_hilbert {n : ℕ} {σ : Type} [Fintype σ] (w : σ → Fin n →₀ ℕ)
    (hw : ∀ v : σ, ∃ i : Fin n, w v = Finsupp.single i 1)
    (I : Ideal (MvPolynomial σ ℂ))
    (hI : ∀ p ∈ I, ∀ d, MvPolynomial.weightedHomogeneousComponent w d p ∈ I) :
    ∃ (P : MvPolynomial (Fin n) ℚ) (N : ℕ), ∀ d : Fin n →₀ ℕ, (∀ i, N ≤ d i) →
      ((Module.finrank ℂ (MvPolynomial.weightedHomogeneousSubmodule ℂ w d ⧸
        Submodule.comap (MvPolynomial.weightedHomogeneousSubmodule ℂ w d).subtype
          (I.restrictScalars ℂ)) : ℕ) : ℚ) = P.eval (fun i => (d i : ℚ)) := by
  classical
  suffices H : ∀ m, ∀ (τ : Type) [Fintype τ], Fintype.card τ = m →
      ∀ (w : τ → Fin n →₀ ℕ), (∀ v, ∃ i, w v = Finsupp.single i 1) →
      ∀ (J : Ideal (MvPolynomial τ ℂ)), IsWHomog w J →
        ∃ (P : MvPolynomial (Fin n) ℚ) (N : ℕ), ∀ d : Fin n →₀ ℕ, (∀ i, N ≤ d i) →
          ((hilb w J d : ℕ) : ℚ) = P.eval (fun i => (d i : ℚ)) by
    obtain ⟨P, N, hPN⟩ := H (Fintype.card σ) σ rfl w hw I hI
    exact ⟨P, N, hPN⟩
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro τ _ hcard w hw J hJ
    have hw_ne : ∀ v : τ, w v ≠ 0 := fun v => by
      obtain ⟨i, hi⟩ := hw v
      rw [hi]
      exact Finsupp.single_ne_zero.mpr one_ne_zero
    have key : ∀ J : Ideal (MvPolynomial τ ℂ), IsWHomog w J →
        ∃ (P : MvPolynomial (Fin n) ℚ) (N : ℕ), ∀ d : Fin n →₀ ℕ, (∀ i, N ≤ d i) →
          ((hilb w J d : ℕ) : ℚ) = P.eval (fun i => (d i : ℚ)) := by
      intro J
      let C : Ideal (MvPolynomial τ ℂ) → Prop := fun K => IsWHomog w K →
          ∃ (P : MvPolynomial (Fin n) ℚ) (N : ℕ), ∀ d : Fin n →₀ ℕ, (∀ i, N ≤ d i) →
            ((hilb w K d : ℕ) : ℚ) = P.eval (fun i => (d i : ℚ))
      change C J
      refine WellFounded.induction (C := C) (r := (· > ·))
        (IsNoetherian.wellFoundedGT (R := MvPolynomial τ ℂ)) J ?_
      intro J ihJ hJ
      -- eventual polynomiality of `J + (X v)` via the outer induction
      have hspan : ∀ v : τ, ∃ (P : MvPolynomial (Fin n) ℚ) (N : ℕ),
          ∀ d : Fin n →₀ ℕ, (∀ i, N ≤ d i) →
          ((hilb w (J ⊔ Ideal.span {MvPolynomial.X v}) d : ℕ) : ℚ)
            = P.eval (fun i => (d i : ℚ)) := by
        intro v
        have hX : MvPolynomial.X v ∈ J ⊔ Ideal.span {MvPolynomial.X v} :=
          Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
        have hJ' : IsWHomog w (J ⊔ Ideal.span {MvPolynomial.X v}) :=
          isWHomog_sup_span_X w hJ
        have hcard' : Fintype.card {x : τ // x ≠ v} < m := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (p := fun a => a ≠ v) (x := v) (by simp)
        obtain ⟨P₁, N₁, hP₁raw⟩ := ih (Fintype.card {x : τ // x ≠ v}) hcard'
          {x : τ // x ≠ v} rfl (fun x => w x.1) (fun x => hw x.1)
          (Ideal.comap (MvPolynomial.rename (Subtype.val)) (J ⊔ Ideal.span {MvPolynomial.X v}))
          (rb_isWHomog_comap_rename w (J ⊔ Ideal.span {MvPolynomial.X v}) hJ')
        refine ⟨P₁, N₁, fun d hd => ?_⟩
        rw [hilb_reduce w (J ⊔ Ideal.span {MvPolynomial.X v}) hX hJ' d]
        exact hP₁raw d hd
      by_cases hA : ∃ v : τ, ¬ (Submodule.colon (J : Submodule (MvPolynomial τ ℂ)
          (MvPolynomial τ ℂ)) ({MvPolynomial.X v} : Set (MvPolynomial τ ℂ))) ≤ J
      · -- Case A: some colon ideal strictly contains `J`
        obtain ⟨v, hv⟩ := hA
        obtain ⟨i, hi⟩ := hw v
        obtain ⟨P₁, N₁, hP₁⟩ := hspan v
        have hJ'' : IsWHomog w (Submodule.colon (J : Submodule (MvPolynomial τ ℂ)
            (MvPolynomial τ ℂ)) ({MvPolynomial.X v} : Set (MvPolynomial τ ℂ))) :=
          isWHomog_colon (v := v) (I := J) w hJ
        have hle : J ≤ Submodule.colon (J : Submodule (MvPolynomial τ ℂ)
            (MvPolynomial τ ℂ)) ({MvPolynomial.X v} : Set (MvPolynomial τ ℂ)) := by
          intro p hp
          rw [Submodule.mem_colon_singleton]
          exact Ideal.mul_mem_right (MvPolynomial.X v) J hp
        have hlt : J < Submodule.colon (J : Submodule (MvPolynomial τ ℂ)
            (MvPolynomial τ ℂ)) ({MvPolynomial.X v} : Set (MvPolynomial τ ℂ)) :=
          lt_of_le_of_ne hle (fun h => hv (le_of_eq h.symm))
        obtain ⟨P₂, N₂, hP₂⟩ := ihJ _ hlt hJ''
        refine ⟨P₁ + shiftP i P₂, max N₁ (N₂ + 1), fun q hq => ?_⟩
        have hqN₁ : ∀ j, N₁ ≤ q j := fun j => le_trans (le_max_left _ _) (hq j)
        have hqN₂ : ∀ j, N₂ + 1 ≤ q j := fun j => le_trans (le_max_right _ _) (hq j)
        have hqi : 1 ≤ q i := by have := hqN₂ i; omega
        have hrel := hilb_add_X w hw_ne (v := v) J hJ
          (q - (Finsupp.single i 1 : Fin n →₀ ℕ))
        rw [hi, tsub_single_add q i hqi] at hrel
        have hE : ∀ j, N₂ ≤ (q - (Finsupp.single i 1 : Fin n →₀ ℕ)) j := by
          intro j
          rw [Finsupp.tsub_apply]
          by_cases hj : j = i
          · subst hj; rw [Finsupp.single_eq_same]; have := hqN₂ j; omega
          · rw [Finsupp.single_eq_of_ne hj, tsub_zero]; have := hqN₂ j; omega
        rw [MvPolynomial.eval_add]
        rw [show ((hilb w J q : ℕ) : ℚ)
              = ((hilb w (J ⊔ Ideal.span {MvPolynomial.X v}) q : ℕ) : ℚ)
                + ((hilb w (Submodule.colon (J : Submodule (MvPolynomial τ ℂ)
                    (MvPolynomial τ ℂ)) ({MvPolynomial.X v} : Set (MvPolynomial τ ℂ)))
                    (q - (Finsupp.single i 1 : Fin n →₀ ℕ)) : ℕ) : ℚ) from by
            rw [hrel]; push_cast; ring]
        rw [hP₁ q hqN₁, hP₂ _ hE, ← shiftP_eval (i := i) P₂ hqi]
      · -- Case B: all colon ideals equal `J`; use the difference criterion
        have hcol : ∀ v : τ, Submodule.colon (J : Submodule (MvPolynomial τ ℂ)
            (MvPolynomial τ ℂ)) ({MvPolynomial.X v} : Set (MvPolynomial τ ℂ)) = J := by
          intro v
          exact le_antisymm (by by_contra h; exact hA ⟨v, h⟩) (by
            intro p hp
            rw [Submodule.mem_colon_singleton]
            exact Ideal.mul_mem_right (MvPolynomial.X v) J hp)
        have hdata : ∀ i : Fin n, ∃ M : ℕ, ∃ Q : MvPolynomial (Fin n) ℚ,
            ∀ d : Fin n →₀ ℕ, (∀ j, M ≤ d j) →
              (fun d => (hilb w J d : ℚ)) (d + Finsupp.single i 1)
                - (fun d => (hilb w J d : ℚ)) d = Q.eval (fun j => (d j : ℚ)) := by
          intro i
          by_cases hc : ∃ v : τ, w v = Finsupp.single i 1
          · obtain ⟨v, hv⟩ := hc
            obtain ⟨P₁, N₁, hP₁⟩ := hspan v
            refine ⟨N₁, upP i P₁, fun d hd => ?_⟩
            change ((hilb w J (d + (Finsupp.single i 1 : Fin n →₀ ℕ)) : ℕ) : ℚ) - ((hilb w J d : ℕ) : ℚ)
              = (upP i P₁).eval (fun j => (d j : ℚ))
            have hrel := hilb_add_X w hw_ne (v := v) J hJ d
            rw [hv, hcol v] at hrel
            have hcast : ((hilb w J (d + (Finsupp.single i 1 : Fin n →₀ ℕ)) : ℕ) : ℚ)
                - ((hilb w J d : ℕ) : ℚ)
                = ((hilb w (J ⊔ Ideal.span {MvPolynomial.X v})
                    (d + Finsupp.single i 1) : ℕ) : ℚ) := by
              rw [hrel]; push_cast; ring
            have hdN₁ : ∀ j, N₁ ≤ (d + (Finsupp.single i 1 : Fin n →₀ ℕ)) j := by
              intro j; rw [Finsupp.add_apply]
              exact le_trans (hd j) (Nat.le_add_right _ _)
            rw [hcast, hP₁ _ hdN₁, upP_eval]
          · have hvzero : ∀ v : τ, (w v) i = 0 := by
              intro v
              obtain ⟨j, hj⟩ := hw v
              rw [hj]
              by_cases hji : j = i
              · exact absurd ⟨v, by rw [hj, hji]⟩ hc
              · rw [Finsupp.single_eq_of_ne (Ne.symm hji)]
            refine ⟨1, 0, fun d hd => ?_⟩
            change ((hilb w J (d + (Finsupp.single i 1 : Fin n →₀ ℕ)) : ℕ) : ℚ) - ((hilb w J d : ℕ) : ℚ)
              = (0 : MvPolynomial (Fin n) ℚ).eval (fun j => (d j : ℚ))
            have h1 : hilb w J (d + (Finsupp.single i 1 : Fin n →₀ ℕ)) = 0 := by
              refine hilb_eq_zero_of_no_var hvzero J ?_
              rw [Finsupp.add_apply, Finsupp.single_eq_same]; omega
            have h2 : hilb w J d = 0 :=
              hilb_eq_zero_of_no_var hvzero J (by have := hd i; omega)
            rw [h1, h2]; simp
        have hstep : ∃ M : ℕ, ∀ i : Fin n, ∃ Q : MvPolynomial (Fin n) ℚ,
            ∀ d : Fin n →₀ ℕ, (∀ j, M ≤ d j) →
              (fun d => (hilb w J d : ℚ)) (d + Finsupp.single i 1)
                - (fun d => (hilb w J d : ℚ)) d = Q.eval (fun j => (d j : ℚ)) := by
          choose Mf Qf hQf using hdata
          exact ⟨Finset.univ.sup Mf, fun i => ⟨Qf i, fun d hd =>
            hQf i d (fun j => le_trans (Finset.le_sup (Finset.mem_univ i)) (hd j))⟩⟩
        exact eventuallyPoly_of_diffs hstep
    exact key J hJ

end

end Work.RB
