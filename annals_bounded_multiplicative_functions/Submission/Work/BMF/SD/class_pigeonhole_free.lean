import Mathlib
import Submission.Work.BMF.SD.large_sieve_cover_free
import Submission.Work.BMF.polyrel_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The class pigeonhole, clash-free

`Work.BMF.SD.class_pigeonhole` (`SD/class_pigeonhole.lean`) extracts, from a family of correlating
`k`-degree phases in a window `~ C₀H`, a subfamily of relative size `>= 1/K` (`K = O(1)`) all of
whose members are `PolyRel k C 1`-related to one common member.  It rests on
`Work.BMF.SD.large_sieve_cover`, whose import closure contains `SD/weyl_inverse` and therefore
cannot be loaded together with `Submission.Work.BMF.SD.tk_short`.  This file repeats the same proof
on top of the clash-free cover `Submission.Work.BMF.SD.large_sieve_cover_free`, so that the
phase-class structure is available inside the scaling-down development
(`Work.BMF.SD.good_prime_incidence` and its chain).  The proof is verbatim `class_pigeonhole`'s;
only the name of the cover changed.
-/

namespace Work.BMF.SD

open Classical Polynomial Finset Real Complex
open Work.BMF

/-- Reflexivity of `PolyRel` at constant `C ≥ 1`: `(I, P) ~_δ (I, P)`. -/
lemma PolyRel.refl {k : ℕ} {C : ℝ} (P : ℝ[X]) {x L : ℝ} (hC : 1 ≤ C) (hL : 0 ≤ L) :
    PolyRel k C 1 x L P x L P := by
  refine ⟨?_, ?_, ?_, 0, 0, Submodule.zero_mem _, Submodule.zero_mem _, ?_, ?_,
    IntegralOn.zero 1⟩
  · simpa using mul_le_mul_of_nonneg_right hC hL
  · simpa using mul_le_mul_of_nonneg_right hC hL
  · rw [sub_self, abs_zero]; exact mul_nonneg (by linarith) hL
  · show P = 0 + P + 0; ring
  · intro t ht; rw [Polynomial.eval_zero, abs_zero]; linarith

/-- Pigeonhole: given a map `g` from a nonempty finite type into a finite set `A`, some value
`j ∈ A` has a fibre of size at least `#ι / #A`, in the multiplicative form `#ι ≤ #fibre * #A`. -/
lemma exists_fiber_card_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (g : ι → ι) (hg : ∀ t, g t ∈ A) (t₀ : ι) :
    ∃ j ∈ A, (Fintype.card ι : ℝ) ≤
      ((Finset.univ.filter (fun t => g t = j)).card : ℝ) * (A.card : ℝ) := by
  classical
  have hAne : A.Nonempty := ⟨g t₀, hg t₀⟩
  obtain ⟨j₀, hj₀A, hj₀max⟩ := Finset.exists_max_image A
    (fun j => (Finset.univ.filter (fun t => g t = j)).card) hAne
  refine ⟨j₀, hj₀A, ?_⟩
  have hsum : (Finset.univ : Finset ι).card =
      ∑ j ∈ A, (Finset.univ.filter (fun t => g t = j)).card :=
    Finset.card_eq_sum_card_fiberwise (f := g) (s := Finset.univ) (t := A)
      (fun x _ => hg x)
  have hle : ∑ j ∈ A, (Finset.univ.filter (fun t => g t = j)).card ≤
      ∑ _j ∈ A, (Finset.univ.filter (fun t => g t = j₀)).card :=
    Finset.sum_le_sum (fun j hj => hj₀max j hj)
  rw [Finset.sum_const, nsmul_eq_mul] at hle
  have hle' : (Finset.univ : Finset ι).card ≤
      (Finset.univ.filter (fun t => g t = j₀)).card * A.card := by
    rw [hsum]
    exact le_trans hle (le_of_eq (mul_comm _ _))
  have hcard : (Fintype.card ι : ℝ) = ((Finset.univ : Finset ι).card : ℝ) := by
    rw [Finset.card_univ]
  rw [hcard]
  exact_mod_cast hle'

/-- **The phase-class pigeonhole of the scaling-down step (MRT Prop. 3.1 / MRTTZ Prop. 3.4, phase
half).**

Let `f` be `1`-bounded, let `(xᵢ, Lᵢ, Pᵢ)_{i ∈ S}` be a *nonempty* finite family of intervals with
`degree ≤ k` phases, all lying in the window `[x₀ - C₀H, x₀ + C₀H]` with lengths `≍ H`, and all
*correlating* with `f` at level `η'`: `η' Lᵢ ≤ ‖corr f Pᵢ xᵢ Lᵢ‖`.  Then one can find a subfamily
`A ⊆ S` of size `≥ #S / K` (with `K = K(k,η',C₀) = O(1)`) all of whose members are
`PolyRel k C 1`-related to one *common* member `i₀ ∈ A`, with `C = C(k,η',C₀)`.

This is the pigeonhole that the paper's proof of Prop. "Scaling down" performs after the large
sieve: the correlating rescaled phases attached to a single cluster position fall into `K = O(1)`
`PolyRel`-classes, so some class carries `≫ π₀(P')/K` of the `≫ π₀(P')` pairs of the cluster; the
chosen phase `φ'_{I'}` is the representative of that class.  (This is the step which the
fixed-phase form of the target cannot reproduce: it identifies *a* large class, not the class of
the target's own dilated phase.)

Proof: apply `Work.BMF.SD.large_sieve_cover` to the family (index type `Fin N`, enumerating `S`);
it returns `C` and `K` and a covering set `A₀` of size `≤ K` with every `i` `PolyRel k C 1`-related
to some `j ∈ A₀`.  Assigning each `i` to such a `j` and taking the largest fibre gives `A` with
`#A · K ≥ #S`, and all its members are related to the *same* representative `i₀` with the same
constant `C` (no transitivity of `PolyRel` is needed). -/
theorem class_pigeonhole_free (k : ℕ) (η' C₀ : ℝ) (hη' : 0 < η') (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, C₀ ≤ C ∧ ∃ K : ℕ, 0 < K ∧
      ∀ (N : ℕ) (f : ℕ → ℂ) (x₀ H : ℝ) (xs Ls : Fin N → ℝ) (Ps : Fin N → ℝ[X])
        (S : Finset (Fin N)),
        S.Nonempty →
        (∀ n, ‖f n‖ ≤ 1) → 1 ≤ H → (∀ i ∈ S, 1 ≤ xs i) →
        (∀ i ∈ S, Ls i ≤ C₀ * H ∧ H ≤ C₀ * Ls i ∧ |xs i - x₀| ≤ C₀ * H) →
        (∀ i ∈ S, Ps i ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ)) →
        (∀ i ∈ S, η' * Ls i ≤ ‖corr f (Ps i) (xs i) (Ls i)‖) →
        ∃ A : Finset (Fin N), A ⊆ S ∧ (S.card : ℝ) ≤ (A.card : ℝ) * K ∧
          ∃ i₀ ∈ A, ∀ i ∈ A,
            PolyRel k C 1 (xs i) (Ls i) (Ps i) (xs i₀) (Ls i₀) (Ps i₀) := by
  classical
  obtain ⟨C, hCge, K₀, hcov⟩ := large_sieve_cover_free k η' C₀ hη' hC₀
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hC1 : 1 ≤ C := le_trans hC₀ hCge
  refine ⟨C, hCge, K₀ + 1, Nat.succ_pos _, ?_⟩
  intro N f x₀ H xs Ls Ps S hSne hf hH hxs hgeo hdeg hcorr
  have hSpos : 0 < S.card := Finset.card_pos.mpr hSne
  let e : Fin S.card ≃ ↥S := (S.equivFin).symm
  let ee : Fin S.card → Fin N := fun t => (e t).1
  have hee_mem : ∀ t, ee t ∈ S := fun t => (e t).2
  have hee_inj : Function.Injective ee := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  have hLpos : ∀ t : Fin S.card, 0 ≤ Ls (ee t) := by
    intro t
    have h := (hgeo (ee t) (hee_mem t)).2.1
    nlinarith [h, hH, hC₀pos]
  obtain ⟨A₀, hA₀card, hA₀cov⟩ :=
    hcov (S.card) f x₀ H (fun t => xs (ee t)) (fun t => Ls (ee t)) (fun t => Ps (ee t))
      hf hH (fun t => hxs (ee t) (hee_mem t))
      (fun t => hgeo (ee t) (hee_mem t)) (fun t => hdeg (ee t) (hee_mem t))
      (fun t => hcorr (ee t) (hee_mem t))
  -- the representative map into `A₀`
  let g : Fin S.card → Fin S.card := fun t => Classical.choose (hA₀cov t)
  have hg_mem : ∀ t, g t ∈ A₀ := fun t => (Classical.choose_spec (hA₀cov t)).1
  have hg_rel : ∀ t, PolyRel k C 1 (xs (ee t)) (Ls (ee t)) (Ps (ee t))
      (xs (ee (g t))) (Ls (ee (g t))) (Ps (ee (g t))) :=
    fun t => (Classical.choose_spec (hA₀cov t)).2
  obtain ⟨j₀, hj₀A, hfib⟩ := exists_fiber_card_ge A₀ g hg_mem ⟨0, hSpos⟩
  -- the fibre over `j₀`, plus the representative `j₀` itself
  let F : Finset (Fin S.card) := Finset.univ.filter (fun t => g t = j₀)
  have hFrel : ∀ t ∈ F, PolyRel k C 1 (xs (ee t)) (Ls (ee t)) (Ps (ee t))
      (xs (ee j₀)) (Ls (ee j₀)) (Ps (ee j₀)) := by
    intro t ht
    have hgt : g t = j₀ := (Finset.mem_filter.mp ht).2
    have h := hg_rel t
    rw [hgt] at h
    exact h
  have hFsub : F ⊆ F ∪ {j₀} := Finset.subset_union_left
  refine ⟨(F ∪ {j₀}).image ee, ?hsub, ?hcard, ee j₀, ?hmem, ?hrel⟩
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨t, -, rfl⟩
    exact hee_mem t
  · have himg : ((F ∪ {j₀}).image ee).card = (F ∪ {j₀}).card :=
      Finset.card_image_of_injective _ hee_inj
    rw [himg]
    have hFle : (F.card : ℝ) ≤ ((F ∪ {j₀}).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hFsub
    have hA₀le : (A₀.card : ℝ) ≤ ((K₀ + 1 : ℕ) : ℝ) := by
      have : A₀.card ≤ K₀ + 1 := by omega
      exact_mod_cast this
    have hU0 : (0 : ℝ) ≤ ((F ∪ {j₀}).card : ℝ) := by positivity
    calc (S.card : ℝ) = (Fintype.card (Fin S.card) : ℝ) := by simp
      _ ≤ (F.card : ℝ) * (A₀.card : ℝ) := hfib
      _ ≤ ((F ∪ {j₀}).card : ℝ) * (A₀.card : ℝ) :=
          mul_le_mul_of_nonneg_right hFle (by positivity)
      _ ≤ ((F ∪ {j₀}).card : ℝ) * ((K₀ + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hA₀le hU0
  · exact Finset.mem_image.mpr
      ⟨j₀, Finset.mem_union_right _ (Finset.mem_singleton_self j₀), rfl⟩
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨t, htU, rfl⟩
    rcases Finset.mem_union.mp htU with htF | ht1
    · exact hFrel t htF
    · have htj : t = j₀ := Finset.mem_singleton.mp ht1
      subst t
      exact PolyRel.refl (Ps (ee j₀)) hC1 (hLpos j₀)

end Work.BMF.SD
