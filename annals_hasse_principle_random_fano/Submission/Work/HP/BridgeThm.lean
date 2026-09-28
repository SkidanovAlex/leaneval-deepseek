import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.BridgeEval
import Submission.Work.HP.BridgeSol
import Submission.Work.HP.BridgePrim

/-!
# The counting bridge between projective hypersurfaces and primitive coefficient vectors

`toV` sends a primitive integer coefficient vector to the projective point of the corresponding
form; the height of the representative of that point is the norm of the vector, and the fibres
of `toV` are the pairs `±a`.  This file turns those facts into the count identities used in
`Work.HP.bridge`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Filter
open scoped LinearAlgebra.Projectivization

namespace Work.HP

open HassePrincipleRandomFano (HasSolutionsIn)

variable {d n : ℕ}

/-! ## Elementary complements -/

lemma hasSolutionsIn_neg (d n : ℕ) (a : Mon d n → ℤ) (S : Type*) [CommSemiring S]
    [Algebra ℚ S] :
    HasSolutionsIn (formOf d n (-a)) S ↔ HasSolutionsIn (formOf d n a) S := by
  rw [formOf_neg]
  simpa [neg_one_smul] using hasSolutionsIn_smul (formOf d n a) S (-1) (by norm_num)

lemma hasRatZero_neg (d n : ℕ) (a : Mon d n → ℤ) : HasRatZero d n (-a) ↔ HasRatZero d n a := by
  rw [← hasSolutionsIn_rat d n (-a), ← hasSolutionsIn_rat d n a]
  exact hasSolutionsIn_neg d n a ℚ

lemma adelicSol_neg (d n : ℕ) (a : Mon d n → ℤ) : AdelicSol d n (-a) ↔ AdelicSol d n a :=
  hasSolutionsIn_neg d n a HassePrincipleRandomFano.𝔸

/-- Solubility only depends on the projective point, hence agrees for a primitive coefficient
vector of that point. -/
lemma hasSolutionsIn_rep_toV (d n : ℕ) (a : Mon d n → ℤ) (ha : IsPrim a) (S : Type*)
    [CommSemiring S] [Algebra ℚ S] :
    HasSolutionsIn (toV a).rep.1 S ↔ HasSolutionsIn (formOf d n a) S := by
  have hne : toHom a ≠ 0 := toV_ne_zero_of_ne_zero a ha.ne_zero
  have hmk : Projectivization.mk ℚ (toHom a) hne
      = Projectivization.mk ℚ (toV a).rep (toV a).rep_nonzero :=
    (toV_of_ne_zero a hne).symm.trans (Projectivization.mk_rep (toV a)).symm
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' ℚ (toHom a) (toV a).rep hne (toV a).rep_nonzero).1 hmk
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact hne hc.symm
  have hcoe : (toV a).rep.1 = c⁻¹ • formOf d n a := by
    have h := congrArg (fun x : homogeneousSubmodule (Fin (n + 1)) ℚ d =>
      (x : MvPolynomial (Fin (n + 1)) ℚ)) hc
    have h2 : c • (toV a).rep.1 = formOf d n a := by simpa using h
    rw [← h2, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [hcoe]
  exact hasSolutionsIn_smul (formOf d n a) S c⁻¹ (inv_ne_zero hc0)

/-! ## The two-to-one counting lemma -/

/-- If `f : S → T` is two-to-one with fibres `{a, σ a}`, then `S` has twice as many elements
as `T`. -/
lemma ncard_eq_two_mul_ncard {α β : Type*} (f : α → β) (σ : α → α) (S : Set α) (T : Set β)
    (hSfin : S.Finite) (hSσ : ∀ a ∈ S, σ a ∈ S) (hne : ∀ a ∈ S, σ a ≠ a)
    (hST : ∀ a ∈ S, f a ∈ T) (hsurj : ∀ b ∈ T, ∃ a ∈ S, f a = b)
    (hfib : ∀ a ∈ S, ∀ b ∈ S, f b = f a ↔ b = a ∨ b = σ a) :
    S.ncard = 2 * T.ncard := by
  classical
  have hTfin : T.Finite := by
    refine (hSfin.image f).subset ?_
    rintro b hb
    obtain ⟨a, ha, hfa⟩ := hsurj b hb
    exact ⟨a, ha, hfa⟩
  have hH : (hSfin.toFinset : Set α).MapsTo f hTfin.toFinset := by
    intro a ha
    exact hTfin.mem_toFinset.2 (hST a (hSfin.mem_toFinset.1 ha))
  have hcard2 : ∀ b ∈ hTfin.toFinset,
      (hSfin.toFinset.filter fun a => f a = b).card = 2 := by
    intro b hb
    obtain ⟨a, ha, hfa⟩ := hsurj b (hTfin.mem_toFinset.1 hb)
    have hfil : (hSfin.toFinset.filter fun x => f x = b)
        = (hSfin.toFinset.filter fun x => f x = f a) := by
      congr 1
      ext x
      rw [hfa]
    rw [hfil]
    have hset : (hSfin.toFinset.filter fun x => f x = f a) = ({a, σ a} : Finset α) := by
      ext x
      simp only [Finset.mem_filter, hSfin.mem_toFinset, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hfx⟩
        exact (hfib a ha x hx).1 hfx
      · rintro (rfl | rfl)
        · exact ⟨ha, rfl⟩
        · exact ⟨hSσ a ha, (hfib a ha (σ a) (hSσ a ha)).2 (Or.inr rfl)⟩
    rw [hset, Finset.card_pair (hne a ha).symm]
  have h1 : hSfin.toFinset.card
      = ∑ b ∈ hTfin.toFinset, (hSfin.toFinset.filter fun a => f a = b).card :=
    Finset.card_eq_sum_card_fiberwise hH
  have h2 : (∑ b ∈ hTfin.toFinset, (hSfin.toFinset.filter fun a => f a = b).card)
      = hTfin.toFinset.card * 2 := Finset.sum_const_nat hcard2
  rw [Set.ncard_eq_toFinset_card S hSfin, Set.ncard_eq_toFinset_card T hTfin, h1, h2]
  exact Nat.mul_comm _ _

/-! ## The count identities -/

/-- Counting transport for `HasRatZero`. -/
theorem ncard_primSet_hasRatZero (d n : ℕ) (A : ℝ) :
    (primSet d n A (HasRatZero d n)).ncard
      = 2 * ({V ∈ HassePrincipleRandomFano.heightLE d n A |
          HasSolutionsIn V.rep.1 ℚ}).ncard := by
  refine ncard_eq_two_mul_ncard (toV (d := d) (n := n)) Neg.neg (primSet d n A (HasRatZero d n))
    {V | V ∈ HassePrincipleRandomFano.heightLE d n A ∧ HasSolutionsIn V.rep.1 ℚ}
    (finite_primSet (d := d) (n := n) A _) ?_ ?_ ?_ ?_ ?_
  · rintro a ⟨hprim, hnorm, hP⟩
    exact ⟨hprim.neg, by rw [eNorm_neg]; exact hnorm, (hasRatZero_neg d n a).2 hP⟩
  · rintro a ⟨hprim, -, -⟩ h
    refine hprim.ne_zero (funext fun m => ?_)
    have h2 := congrFun h m
    simp only [Pi.neg_apply, Pi.zero_apply] at h2 ⊢
    linarith
  · rintro a ⟨hprim, hnorm, hP⟩
    refine ⟨?_, (hasSolutionsIn_rep_toV d n a hprim ℚ).2 ((hasSolutionsIn_rat d n a).2 hP)⟩
    show HassePrincipleRandomFano.height (toV a).rep.1 ≤ A
    rw [height_rep d n a hprim (toV a) rfl]
    exact hnorm
  · rintro V ⟨hV, hQ⟩
    obtain ⟨a, hprim, haV⟩ := toV_surjective d n V
    have hQ' : HasSolutionsIn (toV a).rep.1 ℚ := by rwa [haV]
    exact ⟨a, ⟨hprim, by rw [← height_rep d n a hprim V haV]; exact hV,
      (hasSolutionsIn_rat d n a).1 ((hasSolutionsIn_rep_toV d n a hprim ℚ).1 hQ')⟩, haV⟩
  · rintro a ⟨hprim, -, -⟩ b ⟨hbprim, -, -⟩
    exact toV_eq_toV d n b a hbprim hprim

/-- Counting transport for `AdelicSol`. -/
theorem ncard_primSet_adelic (d n : ℕ) (A : ℝ) :
    (primSet d n A (AdelicSol d n)).ncard
      = 2 * ({V ∈ HassePrincipleRandomFano.heightLE d n A |
          HasSolutionsIn V.rep.1 HassePrincipleRandomFano.𝔸}).ncard := by
  refine ncard_eq_two_mul_ncard (toV (d := d) (n := n)) Neg.neg (primSet d n A (AdelicSol d n))
    {V | V ∈ HassePrincipleRandomFano.heightLE d n A ∧
      HasSolutionsIn V.rep.1 HassePrincipleRandomFano.𝔸}
    (finite_primSet (d := d) (n := n) A _) ?_ ?_ ?_ ?_ ?_
  · rintro a ⟨hprim, hnorm, hP⟩
    exact ⟨hprim.neg, by rw [eNorm_neg]; exact hnorm, (adelicSol_neg d n a).2 hP⟩
  · rintro a ⟨hprim, -, -⟩ h
    refine hprim.ne_zero (funext fun m => ?_)
    have h2 := congrFun h m
    simp only [Pi.neg_apply, Pi.zero_apply] at h2 ⊢
    linarith
  · rintro a ⟨hprim, hnorm, hP⟩
    refine ⟨?_, (hasSolutionsIn_rep_toV d n a hprim HassePrincipleRandomFano.𝔸).2 hP⟩
    show HassePrincipleRandomFano.height (toV a).rep.1 ≤ A
    rw [height_rep d n a hprim (toV a) rfl]
    exact hnorm
  · rintro V ⟨hV, hQ⟩
    obtain ⟨a, hprim, haV⟩ := toV_surjective d n V
    have hQ' : HasSolutionsIn (toV a).rep.1 HassePrincipleRandomFano.𝔸 := by rwa [haV]
    exact ⟨a, ⟨hprim, by rw [← height_rep d n a hprim V haV]; exact hV,
      (hasSolutionsIn_rep_toV d n a hprim HassePrincipleRandomFano.𝔸).1 hQ'⟩, haV⟩
  · rintro a ⟨hprim, -, -⟩ b ⟨hbprim, -, -⟩
    exact toV_eq_toV d n b a hbprim hprim

/-- Counting transport for the full height ball. -/
theorem ncard_primSet_true (d n : ℕ) (A : ℝ) :
    (primSet d n A (fun _ => True)).ncard
      = 2 * (HassePrincipleRandomFano.heightLE d n A).ncard := by
  refine ncard_eq_two_mul_ncard (toV (d := d) (n := n)) Neg.neg (primSet d n A (fun _ => True))
    (HassePrincipleRandomFano.heightLE d n A) (finite_primSet (d := d) (n := n) A _) ?_ ?_ ?_ ?_ ?_
  · rintro a ⟨hprim, hnorm, -⟩
    exact ⟨hprim.neg, by rw [eNorm_neg]; exact hnorm, trivial⟩
  · rintro a ⟨hprim, -, -⟩ h
    refine hprim.ne_zero (funext fun m => ?_)
    have h2 := congrFun h m
    simp only [Pi.neg_apply, Pi.zero_apply] at h2 ⊢
    linarith
  · rintro a ⟨hprim, hnorm, -⟩
    show HassePrincipleRandomFano.height (toV a).rep.1 ≤ A
    rw [height_rep d n a hprim (toV a) rfl]
    exact hnorm
  · rintro V hV
    obtain ⟨a, hprim, haV⟩ := toV_surjective d n V
    exact ⟨a, ⟨hprim, by rw [← height_rep d n a hprim V haV]; exact hV, trivial⟩, haV⟩
  · rintro a ⟨hprim, -, -⟩ b ⟨hbprim, -, -⟩
    exact toV_eq_toV d n b a hbprim hprim

end Work.HP
