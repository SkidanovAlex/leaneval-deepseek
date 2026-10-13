import Mathlib
import Submission.Work.DSM5b.HCF.Surj
import Submission.Work.DSM5b.HCF.SurjSign
import Submission.Work.DSM5b.HCF.collision_structure
import Submission.Work.DSM5b.HCF.sign_tupDel_collision

namespace Work.DSM5b.HCF

universe u

open Work.DSM5b

/-- Parity identity used in the sign cancellation: with `i₁ < i₂`, the exponent `i₂ + (i₂ - i₁ - 1)`
is congruent to `i₁ + 1` modulo `2`. -/
lemma neg_one_pow_collision {R : Type u} [CommRing R] {i₁ i₂ : ℕ} (h : i₁ < i₂) :
    (-1 : R) ^ (i₂ + (i₂ - i₁ - 1)) = - (-1 : R) ^ i₁ := by
  have hm : i₂ + (i₂ - i₁ - 1) = i₁ + 1 + 2 * (i₂ - i₁ - 1) := by omega
  rw [hm, pow_add, pow_add, pow_one, pow_mul, neg_one_sq, one_pow, mul_one]
  ring

theorem surjD_secFun {R : Type u} [CommRing R] {n : ℕ} (S₀ : Finset (Fin n)) (N : Type u)
    [AddCommGroup N] [Module R N] (p : ℕ) (hp : p + 2 = S₀.card) (y : N) :
    Work.DSM5b.surjD (R := R) S₀ N (p + 1)
      (fun τ => Work.DSM5b.HCF.signOfR (R := R) τ hp • y) = 0 := by
  classical
  funext σ
  change (∑ i : Fin (p + 3), (if h : tupRng (tupDel i σ.1) = S₀ then
      ((-1 : R) ^ (i : ℕ)) •
        (signOfR (R := R) (⟨tupDel i σ.1, h⟩ : SurjIdx S₀ (p + 1)) hp • y) else 0)) = 0
  -- ### The reference equivalence and the lifted surjection.
  let e : Fin (p + 2) ≃ ↥S₀ := refEquiv S₀ (p + 1) hp
  let v : Fin (p + 3) → Fin (p + 2) := fun k => e.symm ⟨σ.1 k, mem_of_range σ k⟩
  have hv : Function.Surjective v := by
    intro s
    have hs : (e s : Fin n) ∈ tupRng σ.1 := by rw [σ.2]; exact (e s).2
    rw [tupRng, Finset.mem_image] at hs
    obtain ⟨k, -, hk⟩ := hs
    refine ⟨k, ?_⟩
    show e.symm ⟨σ.1 k, mem_of_range σ k⟩ = s
    rw [show (⟨σ.1 k, mem_of_range σ k⟩ : ↥S₀) = e s from Subtype.ext hk]
    exact e.symm_apply_apply s
  obtain ⟨i₁, i₂, hlt, heq, hchar⟩ := collision_structure v hv
  -- ### `e` of a deleted lifted tuple.
  have hkey : ∀ (i : Fin (p + 3)) (k : Fin (p + 2)),
      (e (tupDel i v k) : Fin n) = (tupDel i σ.1) k := by
    intro i k
    simp only [tupDel_apply, v]
    rw [e.apply_symm_apply]
  -- ### Injectivity is preserved by the lift.
  have hinj_iff : ∀ i : Fin (p + 3),
      Function.Injective (tupDel i σ.1) ↔ Function.Injective (tupDel i v) := by
    intro i
    constructor
    · intro hinj k l hkl
      apply hinj
      have h2 := congrArg (fun x : Fin (p + 2) => (e x : Fin n)) hkl
      simpa only [hkey i k, hkey i l] using h2
    · intro hinj k l hkl
      refine hinj ?_
      apply e.injective
      apply Subtype.ext
      rw [hkey i k, hkey i l, hkl]
  -- ### `tupRng (tupDel i σ.1) = S₀ ↔ Injective (tupDel i σ.1)`.
  have hcard_iff : ∀ i : Fin (p + 3),
      (tupRng (tupDel i σ.1) = S₀) ↔ Function.Injective (tupDel i σ.1) := by
    intro i
    set g : Fin (p + 2) → Fin n := tupDel i σ.1 with hg
    have hsub : tupRng g ⊆ S₀ := (tupRng_del_subset i σ.1).trans (le_of_eq σ.2)
    constructor
    · intro h
      have hc : (tupRng g).card = (Finset.univ : Finset (Fin (p + 2))).card := by
        rw [h, Finset.card_univ, Fintype.card_fin]
        exact hp.symm
      rw [tupRng, Finset.card_image_iff] at hc
      intro a b hab
      exact hc (Finset.mem_univ a) (Finset.mem_univ b) hab
    · intro hinj
      have hc1 : (tupRng g).card = (Finset.univ : Finset (Fin (p + 2))).card := by
        rw [tupRng]
        exact Finset.card_image_of_injective _ hinj
      have hc2 : (tupRng g).card = S₀.card := by
        rw [hc1, Finset.card_univ, Fintype.card_fin]
        exact hp
      exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hc2.symm)
  have hcond : ∀ i : Fin (p + 3), (tupRng (tupDel i σ.1) = S₀) ↔ (i = i₁ ∨ i = i₂) :=
    fun i => (hcard_iff i).trans (hinj_iff i) |>.trans (hchar i)
  -- ### The two surviving summands.
  let τ₁ : SurjIdx S₀ (p + 1) := ⟨tupDel i₁ σ.1, (hcond i₁).mpr (Or.inl rfl)⟩
  let τ₂ : SurjIdx S₀ (p + 1) := ⟨tupDel i₂ σ.1, (hcond i₂).mpr (Or.inr rfl)⟩
  set F : Fin (p + 3) → N := fun i => dite (tupRng (tupDel i σ.1) = S₀)
      (fun h => ((-1 : R) ^ (i : ℕ)) •
        (signOfR (R := R) (⟨tupDel i σ.1, h⟩ : SurjIdx S₀ (p + 1)) hp • y))
      (fun _ => 0) with hF
  change (∑ i : Fin (p + 3), F i) = 0
  have hout : ∀ i, i ∉ ({i₁, i₂} : Finset (Fin (p + 3))) → F i = 0 := by
    intro i hi
    have hni₁ : i ≠ i₁ := fun h => hi (h ▸ Finset.mem_insert_self _ _)
    have hni₂ : i ≠ i₂ := fun h =>
      hi (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hc : ¬ (tupRng (tupDel i σ.1) = S₀) := fun hc =>
      ((hcond i).mp hc).elim hni₁ hni₂
    simp only [hF]
    exact dif_neg hc
  have hpair0 : ({i₁, i₂} : Finset (Fin (p + 3))).sum F = Finset.univ.sum F :=
    Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => hout x hx)
  have hpair : (∑ i : Fin (p + 3), F i) = F i₁ + F i₂ := by
    rw [hpair0.symm, Finset.sum_pair (ne_of_lt hlt)]
  rw [hpair]
  have hFi₁ : F i₁ = ((-1 : R) ^ (i₁ : ℕ)) • (signOfR (R := R) τ₁ hp • y) := by
    simp only [hF, τ₁]
    rw [dif_pos ((hcond i₁).mpr (Or.inl rfl))]
  have hFi₂ : F i₂ = ((-1 : R) ^ (i₂ : ℕ)) • (signOfR (R := R) τ₂ hp • y) := by
    simp only [hF, τ₂]
    rw [dif_pos ((hcond i₂).mpr (Or.inr rfl))]
  rw [hFi₁, hFi₂]
  -- ### The signs of the two deletions differ by `(-1)^(i₂ - i₁ - 1)`.
  let u₁ : Equiv.Perm (Fin (p + 2)) := permOf τ₁ hp
  let u₂ : Equiv.Perm (Fin (p + 2)) := permOf τ₂ hp
  have hperm : ∀ (i : Fin (p + 3)) (h : tupRng (tupDel i σ.1) = S₀) (k : Fin (p + 2)),
      permOf (⟨tupDel i σ.1, h⟩ : SurjIdx S₀ (p + 1)) hp k = tupDel i v k := by
    intro i h k
    have hsub : (⟨(tupDel i σ.1) k,
          mem_of_range (⟨tupDel i σ.1, h⟩ : SurjIdx S₀ (p + 1)) k⟩ : ↥S₀)
        = ⟨σ.1 (Fin.succAbove i k), mem_of_range σ (Fin.succAbove i k)⟩ := Subtype.ext rfl
    show (posEquiv (⟨tupDel i σ.1, h⟩ : SurjIdx S₀ (p + 1)) hp).trans
        (refEquiv S₀ (p + 1) hp).symm k = tupDel i v k
    rw [Equiv.trans_apply, tupDel_apply]
    simp only [posEquiv, Equiv.ofBijective_apply, e, v]
    rw [hsub]
  have hu₁ : ∀ k : Fin (p + 2), u₁ k = tupDel i₁ v k :=
    fun k => hperm i₁ ((hcond i₁).mpr (Or.inl rfl)) k
  have hu₂ : ∀ k : Fin (p + 2), u₂ k = tupDel i₂ v k :=
    fun k => hperm i₂ ((hcond i₂).mpr (Or.inr rfl)) k
  have hsign := sign_tupDel_collision (n := p + 1) hlt heq u₁ u₂ hu₁ hu₂
  have hsignR : signOfR (R := R) τ₂ hp
      = signOfR (R := R) τ₁ hp * (-1 : R) ^ ((i₂ : ℕ) - (i₁ : ℕ) - 1) := by
    have hzv := congrArg (fun z : ℤˣ => (((z : ℤ) : R))) hsign
    have e₂ : signOfR (R := R) τ₂ hp = (((Equiv.Perm.sign u₂ : ℤˣ) : ℤ) : R) := rfl
    have e₁ : signOfR (R := R) τ₁ hp = (((Equiv.Perm.sign u₁ : ℤˣ) : ℤ) : R) := rfl
    rw [e₂, e₁, hzv]
    push_cast
    ring
  -- ### Cancellation of the two surviving summands.
  rw [smul_smul, smul_smul, ← add_smul]
  rw [hsignR]
  rw [show ((-1 : R) ^ (i₁ : ℕ)) * signOfR (R := R) τ₁ hp
        + ((-1 : R) ^ (i₂ : ℕ))
          * (signOfR (R := R) τ₁ hp * (-1 : R) ^ ((i₂ : ℕ) - (i₁ : ℕ) - 1)) = 0
      from ?_]
  · rw [zero_smul]
  · rw [← mul_assoc, mul_comm ((-1 : R) ^ (i₂ : ℕ)), mul_assoc, ← pow_add,
      neg_one_pow_collision (R := R) (show (i₁ : ℕ) < (i₂ : ℕ) from hlt)]
    ring

end Work.DSM5b.HCF
