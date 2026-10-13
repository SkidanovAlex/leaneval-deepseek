import Mathlib
import Submission.Work.DSM5b.HCF.GSurjSign
import Submission.Work.DSM5b.HCF.surjD_secFun

namespace Work.DSM5b.HCF

universe u

theorem gsurjD_signSection {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    {S₀ : Finset ι} {N : Type u} [AddCommGroup N] [Module R N]
    (q : ℕ) (hq : q + 1 = S₀.card) (Y : N) :
    Work.DSM5b.HCF.gsurjD (R := R) S₀ N q
      (fun σ : Work.DSM5b.HCF.GSurjIdx S₀ q =>
        Work.DSM5b.HCF.gSignOfR (R := R) σ hq • Y) = 0 := by
  classical
  funext τ
  change (∑ i : Fin (q + 2), (if h : tupRng (tupDel i τ.1) = S₀ then
      ((-1 : R) ^ (i : ℕ)) •
        (gSignOfR (R := R) (⟨tupDel i τ.1, h⟩ : GSurjIdx S₀ q) hq • Y) else 0)) = 0
  -- ### The reference equivalence and the lifted surjection.
  let e : Fin (q + 1) ≃ ↥S₀ := gRefEquiv S₀ q hq
  let v : Fin (q + 2) → Fin (q + 1) := fun k => e.symm ⟨τ.1 k, gMem τ k⟩
  have hv : Function.Surjective v := by
    intro s
    have hs : (e s : ι) ∈ tupRng τ.1 := by rw [τ.2]; exact (e s).2
    rw [tupRng, Finset.mem_image] at hs
    obtain ⟨k, -, hk⟩ := hs
    refine ⟨k, ?_⟩
    show e.symm ⟨τ.1 k, gMem τ k⟩ = s
    rw [show (⟨τ.1 k, gMem τ k⟩ : ↥S₀) = e s from Subtype.ext hk]
    exact e.symm_apply_apply s
  obtain ⟨i₁, i₂, hlt, heq, hchar⟩ := collision_structure v hv
  -- ### `e` of a deleted lifted tuple.
  have hkey : ∀ (i : Fin (q + 2)) (k : Fin (q + 1)),
      (e (tupDel i v k) : ι) = (tupDel i τ.1) k := by
    intro i k
    simp only [tupDel_apply, v]
    rw [e.apply_symm_apply]
  -- ### Injectivity is preserved by the lift.
  have hinj_iff : ∀ i : Fin (q + 2),
      Function.Injective (tupDel i τ.1) ↔ Function.Injective (tupDel i v) := by
    intro i
    constructor
    · intro hinj k l hkl
      apply hinj
      have h2 := congrArg (fun x : Fin (q + 1) => (e x : ι)) hkl
      simpa only [hkey i k, hkey i l] using h2
    · intro hinj k l hkl
      refine hinj ?_
      apply e.injective
      apply Subtype.ext
      rw [hkey i k, hkey i l, hkl]
  -- ### `tupRng (tupDel i τ.1) = S₀ ↔ Injective (tupDel i τ.1)`.
  have hcard_iff : ∀ i : Fin (q + 2),
      (tupRng (tupDel i τ.1) = S₀) ↔ Function.Injective (tupDel i τ.1) := by
    intro i
    set g : Fin (q + 1) → ι := tupDel i τ.1 with hg
    have hsub : tupRng g ⊆ S₀ := (tupRng_del_subset i τ.1).trans (le_of_eq τ.2)
    constructor
    · intro h
      have hc : (tupRng g).card = (Finset.univ : Finset (Fin (q + 1))).card := by
        rw [h, Finset.card_univ, Fintype.card_fin]
        exact hq.symm
      rw [tupRng, Finset.card_image_iff] at hc
      intro a b hab
      exact hc (Finset.mem_univ a) (Finset.mem_univ b) hab
    · intro hinj
      have hc1 : (tupRng g).card = (Finset.univ : Finset (Fin (q + 1))).card := by
        rw [tupRng]
        exact Finset.card_image_of_injective _ hinj
      have hc2 : (tupRng g).card = S₀.card := by
        rw [hc1, Finset.card_univ, Fintype.card_fin]
        exact hq
      exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hc2.symm)
  have hcond : ∀ i : Fin (q + 2), (tupRng (tupDel i τ.1) = S₀) ↔ (i = i₁ ∨ i = i₂) :=
    fun i => (hcard_iff i).trans (hinj_iff i) |>.trans (hchar i)
  -- ### The two surviving summands.
  let τ₁ : GSurjIdx S₀ q := ⟨tupDel i₁ τ.1, (hcond i₁).mpr (Or.inl rfl)⟩
  let τ₂ : GSurjIdx S₀ q := ⟨tupDel i₂ τ.1, (hcond i₂).mpr (Or.inr rfl)⟩
  set F : Fin (q + 2) → N := fun i => dite (tupRng (tupDel i τ.1) = S₀)
      (fun h => ((-1 : R) ^ (i : ℕ)) •
        (gSignOfR (R := R) (⟨tupDel i τ.1, h⟩ : GSurjIdx S₀ q) hq • Y))
      (fun _ => 0) with hF
  change (∑ i : Fin (q + 2), F i) = 0
  have hout : ∀ i, i ∉ ({i₁, i₂} : Finset (Fin (q + 2))) → F i = 0 := by
    intro i hi
    have hni₁ : i ≠ i₁ := fun h => hi (h ▸ Finset.mem_insert_self _ _)
    have hni₂ : i ≠ i₂ := fun h =>
      hi (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hc : ¬ (tupRng (tupDel i τ.1) = S₀) := fun hc =>
      ((hcond i).mp hc).elim hni₁ hni₂
    simp only [hF]
    exact dif_neg hc
  have hpair0 : ({i₁, i₂} : Finset (Fin (q + 2))).sum F = Finset.univ.sum F :=
    Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => hout x hx)
  have hpair : (∑ i : Fin (q + 2), F i) = F i₁ + F i₂ := by
    rw [hpair0.symm, Finset.sum_pair (ne_of_lt hlt)]
  rw [hpair]
  have hFi₁ : F i₁ = ((-1 : R) ^ (i₁ : ℕ)) • (gSignOfR (R := R) τ₁ hq • Y) := by
    simp only [hF, τ₁]
    rw [dif_pos ((hcond i₁).mpr (Or.inl rfl))]
  have hFi₂ : F i₂ = ((-1 : R) ^ (i₂ : ℕ)) • (gSignOfR (R := R) τ₂ hq • Y) := by
    simp only [hF, τ₂]
    rw [dif_pos ((hcond i₂).mpr (Or.inr rfl))]
  rw [hFi₁, hFi₂]
  -- ### The signs of the two deletions differ by `(-1)^(i₂ - i₁ - 1)`.
  let u₁ : Equiv.Perm (Fin (q + 1)) := gPermOf τ₁ hq
  let u₂ : Equiv.Perm (Fin (q + 1)) := gPermOf τ₂ hq
  have hperm : ∀ (i : Fin (q + 2)) (h : tupRng (tupDel i τ.1) = S₀) (k : Fin (q + 1)),
      gPermOf (⟨tupDel i τ.1, h⟩ : GSurjIdx S₀ q) hq k = tupDel i v k := by
    intro i h k
    have hsub : (⟨(tupDel i τ.1) k,
          gMem (⟨tupDel i τ.1, h⟩ : GSurjIdx S₀ q) k⟩ : ↥S₀)
        = ⟨τ.1 (Fin.succAbove i k), gMem τ (Fin.succAbove i k)⟩ := Subtype.ext rfl
    show (gPosEquiv (⟨tupDel i τ.1, h⟩ : GSurjIdx S₀ q) hq).trans
        (gRefEquiv S₀ q hq).symm k = tupDel i v k
    rw [Equiv.trans_apply, tupDel_apply]
    simp only [gPosEquiv, Equiv.ofBijective_apply, e, v]
    rw [hsub]
  have hu₁ : ∀ k : Fin (q + 1), u₁ k = tupDel i₁ v k :=
    fun k => hperm i₁ ((hcond i₁).mpr (Or.inl rfl)) k
  have hu₂ : ∀ k : Fin (q + 1), u₂ k = tupDel i₂ v k :=
    fun k => hperm i₂ ((hcond i₂).mpr (Or.inr rfl)) k
  have hsign := sign_tupDel_collision (n := q) hlt heq u₁ u₂ hu₁ hu₂
  have hsignR : gSignOfR (R := R) τ₂ hq
      = gSignOfR (R := R) τ₁ hq * (-1 : R) ^ ((i₂ : ℕ) - (i₁ : ℕ) - 1) := by
    have hzv := congrArg (fun z : ℤˣ => (((z : ℤ) : R))) hsign
    have e₂ : gSignOfR (R := R) τ₂ hq = (((Equiv.Perm.sign u₂ : ℤˣ) : ℤ) : R) := rfl
    have e₁ : gSignOfR (R := R) τ₁ hq = (((Equiv.Perm.sign u₁ : ℤˣ) : ℤ) : R) := rfl
    rw [e₂, e₁, hzv]
    push_cast
    ring
  -- ### Cancellation of the two surviving summands.
  rw [smul_smul, smul_smul, ← add_smul]
  rw [hsignR]
  rw [show ((-1 : R) ^ (i₁ : ℕ)) * gSignOfR (R := R) τ₁ hq
        + ((-1 : R) ^ (i₂ : ℕ))
          * (gSignOfR (R := R) τ₁ hq * (-1 : R) ^ ((i₂ : ℕ) - (i₁ : ℕ) - 1)) = 0
      from ?_]
  · rw [zero_smul]
  · rw [← mul_assoc, mul_comm ((-1 : R) ^ (i₂ : ℕ)), mul_assoc, ← pow_add,
      neg_one_pow_collision (R := R) (show (i₁ : ℕ) < (i₂ : ℕ) from hlt)]
    ring

end Work.DSM5b.HCF
