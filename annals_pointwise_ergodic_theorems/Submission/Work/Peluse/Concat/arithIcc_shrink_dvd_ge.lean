import Mathlib
import Submission.Work.Peluse.BoxNorm.prodCubeSum_norm_le
import Submission.Work.Peluse.BoxNorm.boxNormPow_shift

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

/-! ## Elementary auxiliary lemmas -/

/-- The cardinality of the arithmetic progression `c[L]` for `c ≠ 0`. -/
lemma card_arithIcc_shrink {c : ℤ} (hc : c ≠ 0) (L : ℕ) :
    (Work.Peluse.arithIcc c L).card = L := by
  rw [Work.Peluse.arithIcc, Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    have h : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hc hab
    exact_mod_cast h

/-- The scalar identity for the normalising constants of the two cube sums. -/
lemma scalar_key_shrink (m L' t : ℕ) :
    ((((m * L' : ℕ) : ℂ))⁻¹) ^ t * ((((m * L' : ℕ) : ℂ))⁻¹) ^ t
      = ((m : ℂ) ^ (2 * t))⁻¹ *
        ((((L' : ℕ) : ℂ))⁻¹ ^ t * (((L' : ℕ) : ℂ))⁻¹ ^ t) := by
  have hA : ((((m * L' : ℕ) : ℂ))⁻¹) ^ t * ((((m * L' : ℕ) : ℂ))⁻¹) ^ t
      = ((((m * L' : ℕ) : ℂ))⁻¹) ^ (2 * t) := by
    rw [← pow_add, show t + t = 2 * t by omega]
  have hB : ((((L' : ℕ) : ℂ))⁻¹) ^ t * ((((L' : ℕ) : ℂ))⁻¹) ^ t
      = ((((L' : ℕ) : ℂ))⁻¹) ^ (2 * t) := by
    rw [← pow_add, show t + t = 2 * t by omega]
  have hC : ((((m * L' : ℕ) : ℂ))⁻¹) ^ (2 * t)
      = ((m : ℂ) ^ (2 * t))⁻¹ * ((((L' : ℕ) : ℂ))⁻¹) ^ (2 * t) := by
    rw [Nat.cast_mul, mul_inv, mul_pow, ← inv_pow]
  rw [hA, hB, hC]

/-- The elementary step extracting the two normalising factors. -/
lemma scalar_step_shrink {K : Type*} [Field K] (k X Y m2 : K) (t : ℕ)
    (h : X ^ t * X ^ t = m2 * (Y ^ t * Y ^ t)) :
    k * X ^ t * X ^ t = m2 * (k * Y ^ t * Y ^ t) := by
  rw [mul_assoc, mul_assoc, h]
  ring

/-- Pulling a constant out of a finite sum of the shape occurring below. -/
lemma sum_mul_const_shrink {ι : Type*} [Fintype ι] (g : ι → ℂ) (a : ℂ) :
    (∑ i, a * g i) = a * ∑ i, g i := (Finset.mul_sum Finset.univ g a).symm

/-- `cornerShift` is additive in both arguments. -/
lemma cornerShift_add_shrink {t : ℕ} (h h' k k' : Fin t → ℤ) (ω : Fin t → Bool) :
    Work.Peluse.cornerShift (h + h') (k + k') ω
      = Work.Peluse.cornerShift h k ω + Work.Peluse.cornerShift h' k' ω := by
  simp only [Work.Peluse.cornerShift, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by by_cases hω : ω i <;> simp [hω])

/-- The version with the second corner tuple equal to `0`. -/
lemma cornerShift_zero_add_shrink {t : ℕ} (u v : Fin t → ℤ) (ω : Fin t → Bool) :
    Work.Peluse.cornerShift (u + v) (0 : Fin t → ℤ) ω
      = Work.Peluse.cornerShift u 0 ω + Work.Peluse.cornerShift v 0 ω := by
  simpa using cornerShift_add_shrink u v (0 : Fin t → ℤ) (0 : Fin t → ℤ) ω

/-- The cube term of `F`, summed over `x`, with one corner at the origin. -/
abbrev Wf (t : ℕ) (F : (Fin t → Bool) → ℤ → ℂ) (u : Fin t → ℤ) : ℂ :=
  ∑' x : ℤ, ∏ ω : Fin t → Bool,
    (star^[Work.Peluse.weight ω]) (F ω (x + Work.Peluse.cornerShift u 0 ω))

/-- Shifting a finitely supported function keeps it finitely supported. -/
lemma finsupp_shift_shrink {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) (s : ℤ) :
    Work.Peluse.FinSuppZ (Work.Peluse.shift s f) := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨N + s.natAbs, fun x hx => ?_⟩
  refine hN (x + s) ?_
  have htri : (x.natAbs : ℤ) ≤ ((x + s).natAbs : ℤ) + (s.natAbs : ℤ) := by
    have h := Int.natAbs_add_le (x + s) (-s)
    rw [show (x + s) + -s = x from by ring, Int.natAbs_neg] at h
    exact_mod_cast h
  have hx' : ((N + s.natAbs : ℕ) : ℤ) < (x.natAbs : ℤ) := by exact_mod_cast hx
  push_cast at hx'
  omega

/-! ## Folding `prodCubeSum` of a constant family -/

/-- `prodCubeSum` of a *constant* direction family, with the corner differences made explicit. -/
lemma prodCubeSum_const_shrink {t : ℕ} (A S : Finset ℤ) (F : (Fin t → Bool) → ℤ → ℂ)
    (hc : ∀ (h h' : Fin t → ℤ),
      (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (F ω (x + Work.Peluse.cornerShift h h' ω)))
        = ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (F ω (x + Work.Peluse.cornerShift (h - h') (0 : Fin t → ℤ) ω))) :
    Work.Peluse.prodCubeSum t (fun _ : Fin t => A) S F
      = ((S.card : ℂ))⁻¹ * (∏ _ : Fin t, ((A.card : ℂ))⁻¹)
          * (∏ _ : Fin t, ((A.card : ℂ))⁻¹)
          * ∑ h : Fin t → ↥A, ∑ h' : Fin t → ↥A,
              Wf t F (fun i => (h i : ℤ) - (h' i : ℤ)) := by
  rw [Work.Peluse.prodCubeSum_eq]
  have hp : (∏ i : Fin t, (((fun _ : Fin t => A) i).card : ℂ)⁻¹)
      = (∏ _ : Fin t, ((A.card : ℂ))⁻¹) :=
    Finset.prod_congr rfl (fun i _ => rfl)
  rw [hp, hp]
  refine congrArg (fun z => ((S.card : ℂ))⁻¹ * (∏ _ : Fin t, ((A.card : ℂ))⁻¹)
      * (∏ _ : Fin t, ((A.card : ℂ))⁻¹) * z) ?_
  refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
  exact hc (fun i => (h i : ℤ)) (fun i => (h' i : ℤ))

/-- The same fold for a family obtained from `F` by shifting each member `F ω` by the corner
`cornerShift e 0 ω`; the extra shift is then absorbed into the argument of `F`. -/
lemma prodCubeSum_shiftFam_shrink {t : ℕ} (A S : Finset ℤ) (F : (Fin t → Bool) → ℤ → ℂ)
    (e : Fin t → ℤ)
    (hc : ∀ (G : (Fin t → Bool) → ℤ → ℂ) (h h' : Fin t → ℤ),
      (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (G ω (x + Work.Peluse.cornerShift h h' ω)))
        = ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (G ω (x + Work.Peluse.cornerShift (h - h') (0 : Fin t → ℤ) ω))) :
    Work.Peluse.prodCubeSum t (fun _ : Fin t => A) S
        (fun ω : Fin t → Bool => Work.Peluse.shift (Work.Peluse.cornerShift e 0 ω) (F ω))
      = ((S.card : ℂ))⁻¹ * (∏ _ : Fin t, ((A.card : ℂ))⁻¹)
          * (∏ _ : Fin t, ((A.card : ℂ))⁻¹)
          * ∑ r : Fin t → ↥A, ∑ r' : Fin t → ↥A,
              Wf t F ((fun i => (r i : ℤ) - (r' i : ℤ)) + e) := by
  rw [prodCubeSum_const_shrink A S
    (fun ω : Fin t → Bool => Work.Peluse.shift (Work.Peluse.cornerShift e 0 ω) (F ω))
    (hc (fun ω : Fin t → Bool => Work.Peluse.shift (Work.Peluse.cornerShift e 0 ω) (F ω)))]
  refine congrArg (fun z => ((S.card : ℂ))⁻¹ * (∏ _ : Fin t, ((A.card : ℂ))⁻¹)
      * (∏ _ : Fin t, ((A.card : ℂ))⁻¹) * z) ?_
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun r' _ => ?_))
  refine tsum_congr (fun x => ?_)
  refine Finset.prod_congr rfl (fun ω _ => ?_)
  rw [cornerShift_zero_add_shrink]
  have hshift : Work.Peluse.shift (Work.Peluse.cornerShift e 0 ω) (F ω)
        (x + Work.Peluse.cornerShift (fun i => (r i : ℤ) - (r' i : ℤ)) 0 ω)
      = F ω ((x + Work.Peluse.cornerShift (fun i => (r i : ℤ) - (r' i : ℤ)) 0 ω)
          + Work.Peluse.cornerShift e 0 ω) := rfl
  change star^[Work.Peluse.weight ω]
      (Work.Peluse.shift (Work.Peluse.cornerShift e 0 ω) (F ω)
        (x + Work.Peluse.cornerShift (fun i => (r i : ℤ) - (r' i : ℤ)) 0 ω))
    = star^[Work.Peluse.weight ω]
        (F ω (x + (Work.Peluse.cornerShift (fun i => (r i : ℤ) - (r' i : ℤ)) 0 ω
          + Work.Peluse.cornerShift e 0 ω)))
  rw [hshift]
  congr 1
  ring

/-! ## The block decomposition of a sum over the function space `Fin t → ↥(c[L])` -/

/-- Splitting a sum over tuples in `c[m·L']` according to the block decomposition
`↥(c[m·L']) ≃ ↥(c[L']) × Fin m`. -/
lemma block_sum_shrink {t : ℕ} (c : ℤ) {L' m : ℕ} (hL' : 1 ≤ L') (hm : 1 ≤ m)
    (e : ↥(Work.Peluse.arithIcc c (m * L')) ≃ (↥(Work.Peluse.arithIcc c L') × Fin m))
    (he : ∀ (r : ↥(Work.Peluse.arithIcc c L')) (j : Fin m),
        ((e.symm (r, j) : ↥(Work.Peluse.arithIcc c (m * L'))) : ℤ) = (r : ℤ) + c * L' * (j : ℤ))
    (Φ : (Fin t → ℤ) → ℂ) :
    (∑ h : Fin t → ↥(Work.Peluse.arithIcc c (m * L')),
        ∑ h' : Fin t → ↥(Work.Peluse.arithIcc c (m * L')),
          Φ (fun i => (h i : ℤ) - (h' i : ℤ)))
      = ∑ jj : (Fin t → Fin m) × (Fin t → Fin m),
          ∑ r : Fin t → ↥(Work.Peluse.arithIcc c L'),
            ∑ r' : Fin t → ↥(Work.Peluse.arithIcc c L'),
              Φ ((fun i => (r i : ℤ) - (r' i : ℤ))
                  + (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) := by
  classical
  let A : Finset ℤ := Work.Peluse.arithIcc c (m * L')
  let B : Finset ℤ := Work.Peluse.arithIcc c L'
  let eT : (Fin t → ↥A) ≃ ((Fin t → Fin m) × (Fin t → ↥B)) :=
    { toFun := fun h => (fun i => (e (h i)).2, fun i => (e (h i)).1)
      invFun := fun p => fun i => e.symm (p.2 i, p.1 i)
      left_inv := fun h => by funext i; simp
      right_inv := fun p => by
        refine Prod.ext ?_ ?_
        · funext i; simp
        · funext i; simp }
  have hsymm : ∀ (j : Fin t → Fin m) (b : Fin t → ↥B) (i : Fin t),
      ((eT.symm (j, b)) i : ℤ) = (b i : ℤ) + c * L' * (j i : ℤ) := by
    intro j b i
    exact he (b i) (j i)
  have h1 : (∑ h : Fin t → ↥A, ∑ h' : Fin t → ↥A, Φ (fun i => (h i : ℤ) - (h' i : ℤ)))
      = ∑ p : (Fin t → ↥A) × (Fin t → ↥A), Φ (fun i => (p.1 i : ℤ) - (p.2 i : ℤ)) := by
    rw [← Fintype.sum_prod_type']
  have h2 : (∑ p : (Fin t → ↥A) × (Fin t → ↥A), Φ (fun i => (p.1 i : ℤ) - (p.2 i : ℤ)))
      = ∑ q : ((Fin t → Fin m) × (Fin t → ↥B)) × ((Fin t → Fin m) × (Fin t → ↥B)),
          Φ (fun i => ((eT.symm q.1) i : ℤ) - ((eT.symm q.2) i : ℤ)) :=
    Fintype.sum_equiv (Equiv.prodCongr eT eT) _ _ (fun p => by simp [Equiv.prodCongr])
  have h3a :
      (∑ q : ((Fin t → Fin m) × (Fin t → ↥B)) × ((Fin t → Fin m) × (Fin t → ↥B)),
          Φ (fun i => ((eT.symm q.1) i : ℤ) - ((eT.symm q.2) i : ℤ)))
      = ∑ x : ((Fin t → Fin m) × (Fin t → Fin m)) × ((Fin t → ↥B) × (Fin t → ↥B)),
          Φ (fun i => ((eT.symm (x.1.1, x.2.1)) i : ℤ) - ((eT.symm (x.1.2, x.2.2)) i : ℤ)) :=
    Fintype.sum_equiv
      (Equiv.prodProdProdComm (Fin t → Fin m) (Fin t → ↥B) (Fin t → Fin m) (Fin t → ↥B))
      _ _ (fun q => by simp [Equiv.prodProdProdComm])
  have h3b :
      (∑ x : ((Fin t → Fin m) × (Fin t → Fin m)) × ((Fin t → ↥B) × (Fin t → ↥B)),
          Φ (fun i => ((eT.symm (x.1.1, x.2.1)) i : ℤ) - ((eT.symm (x.1.2, x.2.2)) i : ℤ)))
      = ∑ jj : (Fin t → Fin m) × (Fin t → Fin m),
          ∑ rr : (Fin t → ↥B) × (Fin t → ↥B),
            Φ (fun i => ((eT.symm (jj.1, rr.1)) i : ℤ) - ((eT.symm (jj.2, rr.2)) i : ℤ)) := by
    rw [Fintype.sum_prod_type]
  have h4 : (∑ jj : (Fin t → Fin m) × (Fin t → Fin m),
          ∑ rr : (Fin t → ↥B) × (Fin t → ↥B),
            Φ (fun i => ((eT.symm (jj.1, rr.1)) i : ℤ) - ((eT.symm (jj.2, rr.2)) i : ℤ)))
      = ∑ jj : (Fin t → Fin m) × (Fin t → Fin m),
          ∑ r : Fin t → ↥B, ∑ r' : Fin t → ↥B,
            Φ ((fun i => (r i : ℤ) - (r' i : ℤ))
                + (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) := by
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun r' _ => ?_))
    refine congrArg Φ (funext (fun i => ?_))
    show ((eT.symm (jj.1, r)) i : ℤ) - ((eT.symm (jj.2, r')) i : ℤ)
        = ((r i : ℤ) - (r' i : ℤ)) + c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))
    rw [hsymm jj.1 r i, hsymm jj.2 r' i]
    ring
  exact h1.trans (h2.trans (h3a.trans (h3b.trans h4)))

/-! ## The corner reindexing and the block decomposition -/

/-- The cube term summed over `x` depends on the two shift tuples `h, h'` only through `h - h'`. -/
lemma tsum_cube_corner_eq_shrink {t : ℕ} (F : (Fin t → Bool) → ℤ → ℂ) (h h' : Fin t → ℤ) :
    (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
        (F ω (x + Work.Peluse.cornerShift h h' ω)))
      = ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (F ω (x + Work.Peluse.cornerShift (h - h') (0 : Fin t → ℤ) ω)) := by
  have hkey : ∀ x : ℤ,
      (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (F ω (x + Work.Peluse.cornerShift h h' ω)))
        = (fun y : ℤ => ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (F ω (y + Work.Peluse.cornerShift (h - h') (0 : Fin t → ℤ) ω)))
          (x + ∑ i, h' i) := by
    intro x
    refine Finset.prod_congr rfl (fun ω _ => ?_)
    have hcs : Work.Peluse.cornerShift h h' ω
        = (∑ i, h' i) + Work.Peluse.cornerShift (h - h') (0 : Fin t → ℤ) ω := by
      rw [Work.Peluse.cornerShift, Work.Peluse.cornerShift, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Pi.sub_apply, Pi.zero_apply]
      by_cases hω : ω i <;> simp [hω]
    rw [hcs]
    ring
  rw [tsum_congr hkey]
  simpa [Equiv.coe_addRight] using Equiv.tsum_eq (Equiv.addRight (∑ i, h' i))
    (fun y : ℤ => ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
      (F ω (y + Work.Peluse.cornerShift (h - h') (0 : Fin t → ℤ) ω)))

/-- Membership of the block index `(r,j)`: `r + c·L'·j ∈ c[m·L']`. -/
lemma blockMap_mem_shrink {c : ℤ} {L' m L : ℕ} (hL : L = m * L') (hL' : 1 ≤ L')
    (r : ↥(Work.Peluse.arithIcc c L')) (j : Fin m) :
    (r : ℤ) + c * L' * (j : ℤ) ∈ Work.Peluse.arithIcc c L := by
  obtain ⟨a, ha, har⟩ := Finset.mem_image.mp r.2
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have ha2 : a ≤ L' := (Finset.mem_Icc.mp ha).2
  have hj : (j : ℕ) < m := j.2
  refine Finset.mem_image.mpr ⟨a + L' * (j : ℕ), ?_, ?_⟩
  · refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
    rw [hL]
    calc a + L' * (j : ℕ) ≤ L' + L' * (j : ℕ) := by omega
      _ = L' * ((j : ℕ) + 1) := by ring
      _ ≤ L' * m := Nat.mul_le_mul_left _ (by omega)
      _ = m * L' := by ring
  · rw [← har]
    push_cast
    ring

/-- Injectivity of the block map. -/
lemma blockMap_injective_shrink {c : ℤ} (hc : c ≠ 0) {L' m L : ℕ} (hL : L = m * L')
    (hL' : 1 ≤ L') :
    Function.Injective (fun p : ↥(Work.Peluse.arithIcc c L') × Fin m =>
      (⟨(p.1 : ℤ) + c * L' * (p.2 : ℤ), blockMap_mem_shrink hL hL' p.1 p.2⟩ :
        ↥(Work.Peluse.arithIcc c L))) := by
  rintro ⟨r, j⟩ ⟨r', j'⟩ h
  obtain ⟨a, ha, har⟩ := Finset.mem_image.mp r.2
  obtain ⟨a', ha', har'⟩ := Finset.mem_image.mp r'.2
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have ha2 : a ≤ L' := (Finset.mem_Icc.mp ha).2
  have ha'1 : 1 ≤ a' := (Finset.mem_Icc.mp ha').1
  have ha'2 : a' ≤ L' := (Finset.mem_Icc.mp ha').2
  have harZ : (r : ℤ) = c * (a : ℤ) := har.symm
  have har'Z : (r' : ℤ) = c * (a' : ℤ) := har'.symm
  have hval : (r : ℤ) + c * L' * (j : ℤ) = (r' : ℤ) + c * L' * (j' : ℤ) :=
    congrArg Subtype.val h
  have heq : (a : ℤ) + L' * ((j : ℕ) : ℤ) = (a' : ℤ) + L' * ((j' : ℕ) : ℤ) := by
    have h2 : c * ((a : ℤ) + L' * ((j : ℕ) : ℤ))
        = c * ((a' : ℤ) + L' * ((j' : ℕ) : ℤ)) := by
      calc c * ((a : ℤ) + L' * ((j : ℕ) : ℤ))
          = (r : ℤ) + c * L' * ((j : ℕ) : ℤ) := by rw [harZ]; ring
        _ = (r' : ℤ) + c * L' * ((j' : ℕ) : ℤ) := hval
        _ = c * ((a' : ℤ) + L' * ((j' : ℕ) : ℤ)) := by rw [har'Z]; ring
    exact mul_left_cancel₀ hc h2
  have heqN : a + L' * (j : ℕ) = a' + L' * (j' : ℕ) := by exact_mod_cast heq
  have hj : (j : ℕ) = (j' : ℕ) := by
    have h1 : ((a - 1) + L' * (j : ℕ)) / L' = (j : ℕ) := by
      rw [Nat.add_mul_div_left (a - 1) (j : ℕ) (by omega), Nat.div_eq_of_lt (by omega)]
      omega
    have h2 : ((a' - 1) + L' * (j' : ℕ)) / L' = (j' : ℕ) := by
      rw [Nat.add_mul_div_left (a' - 1) (j' : ℕ) (by omega), Nat.div_eq_of_lt (by omega)]
      omega
    have h3 : (a - 1) + L' * (j : ℕ) = (a' - 1) + L' * (j' : ℕ) := by
      rw [← Nat.sub_add_comm ha1, ← Nat.sub_add_comm ha'1, heqN]
    rw [← h1, h3, h2]
  have haeq : a = a' := by
    rw [hj] at heqN
    exact Nat.add_right_cancel heqN
  refine Prod.ext ?_ ?_
  · exact Subtype.ext (by rw [harZ, har'Z, haeq])
  · exact Fin.ext hj

/-- The block decomposition `↥(c[m·L']) ≃ ↥(c[L']) × Fin m`, realised by the map
`(r,j) ↦ r + c·L'·j`. -/
theorem arithIcc_blockEquiv_shrink {c : ℤ} (hc : c ≠ 0) {L' m L : ℕ} (hL : L = m * L')
    (hL' : 1 ≤ L') (hm : 1 ≤ m) :
    ∃ e : ↥(Work.Peluse.arithIcc c L) ≃ (↥(Work.Peluse.arithIcc c L') × Fin m),
      ∀ (r : ↥(Work.Peluse.arithIcc c L')) (j : Fin m),
        ((e.symm (r, j) : ↥(Work.Peluse.arithIcc c L)) : ℤ) = (r : ℤ) + c * L' * (j : ℤ) := by
  have hcard : Fintype.card (↥(Work.Peluse.arithIcc c L') × Fin m)
      = Fintype.card ↥(Work.Peluse.arithIcc c L) := by
    rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin,
      card_arithIcc_shrink hc L', card_arithIcc_shrink hc L, hL, Nat.mul_comm]
  have hbij : Function.Bijective (fun p : ↥(Work.Peluse.arithIcc c L') × Fin m =>
      (⟨(p.1 : ℤ) + c * L' * (p.2 : ℤ), blockMap_mem_shrink hL hL' p.1 p.2⟩ :
        ↥(Work.Peluse.arithIcc c L))) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨blockMap_injective_shrink hc hL hL', hcard⟩
  refine ⟨(Equiv.ofBijective _ hbij).symm, ?_⟩
  intro r j
  rfl

/-- The degenerate case `L = 0`: the direction set `c[0]` is empty. -/
lemma boxNormPow_arithIcc_zero_shrink {t : ℕ} (ht : 1 ≤ t) (c : ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) :
    Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c 0) S f = 0 := by
  have hempty : Work.Peluse.arithIcc c 0 = (∅ : Finset ℤ) := by
    rw [Work.Peluse.arithIcc]
    simp
  rw [Work.Peluse.boxNormPow, Work.Peluse.boxSumPow, hempty, Work.Peluse.prodCubeSum_eq]
  have hp : (∏ i : Fin t, (((fun _ : Fin t => (∅ : Finset ℤ)) i).card : ℂ)⁻¹) = 0 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.card_empty, Nat.cast_zero,
      inv_zero, zero_pow (by omega)]
  simp only [hp]
  simp

/-! ## The main inequality -/

/-- The shrink inequality for `c[m·L']` versus `c[L']`, with the two inputs (the corner reindexing
of the cube term and the block decomposition of `↥(c[m·L'])`) supplied as hypotheses. -/
theorem shrink_of_data {t : ℕ} (ht : 1 ≤ t) {c : ℤ} (hc0 : c ≠ 0) {L' m : ℕ} (hL' : 1 ≤ L')
    (hm : 1 ≤ m) {N : ℕ} {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f)
    (hcorner : ∀ (G : (Fin t → Bool) → ℤ → ℂ) (h h' : Fin t → ℤ),
      (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
          (G ω (x + Work.Peluse.cornerShift h h' ω)))
        = ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (G ω (x + Work.Peluse.cornerShift (h - h') (0 : Fin t → ℤ) ω)))
    (e : ↥(Work.Peluse.arithIcc c (m * L')) ≃ (↥(Work.Peluse.arithIcc c L') × Fin m))
    (he : ∀ (r : ↥(Work.Peluse.arithIcc c L')) (j : Fin m),
        ((e.symm (r, j) : ↥(Work.Peluse.arithIcc c (m * L'))) : ℤ) = (r : ℤ) + c * L' * (j : ℤ)) :
    Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c (m * L'))
        (Work.Peluse.symIcc N) f
      ≤ Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c L')
        (Work.Peluse.symIcc N) f := by
  classical
  have hPa : (∏ _ : Fin t, (((Work.Peluse.arithIcc c (m * L')).card : ℂ))⁻¹)
      = ((((m * L' : ℕ) : ℂ))⁻¹) ^ t := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, card_arithIcc_shrink hc0]
  have hPq : (∏ _ : Fin t, (((Work.Peluse.arithIcc c L').card : ℂ))⁻¹)
      = ((((L' : ℕ) : ℂ))⁻¹) ^ t := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, card_arithIcc_shrink hc0]
  have hblock : ∀ jj : (Fin t → Fin m) × (Fin t → Fin m),
      Work.Peluse.prodCubeSum t (fun _ : Fin t => Work.Peluse.arithIcc c L')
          (Work.Peluse.symIcc N)
          (fun ω : Fin t → Bool => Work.Peluse.shift
            (Work.Peluse.cornerShift (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)
        = ((Work.Peluse.symIcc N).card : ℂ)⁻¹
            * (∏ _ : Fin t, (((Work.Peluse.arithIcc c L').card : ℂ))⁻¹)
            * (∏ _ : Fin t, (((Work.Peluse.arithIcc c L').card : ℂ))⁻¹)
            * ∑ r : Fin t → ↥(Work.Peluse.arithIcc c L'),
                ∑ r' : Fin t → ↥(Work.Peluse.arithIcc c L'),
                  Wf t (fun _ : Fin t → Bool => f)
                    ((fun i => (r i : ℤ) - (r' i : ℤ))
                      + (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))) := by
    intro jj
    exact prodCubeSum_shiftFam_shrink (Work.Peluse.arithIcc c L') (Work.Peluse.symIcc N)
      (fun _ : Fin t → Bool => f)
      (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) hcorner
  have hsc2 : ((↑(Work.Peluse.symIcc N).card : ℂ))⁻¹
          * ((((m * L' : ℕ) : ℂ))⁻¹) ^ t * ((((m * L' : ℕ) : ℂ))⁻¹) ^ t
        = ((m : ℂ) ^ (2 * t))⁻¹ *
          (((↑(Work.Peluse.symIcc N).card : ℂ))⁻¹
            * ((((L' : ℕ) : ℂ))⁻¹) ^ t * ((((L' : ℕ) : ℂ))⁻¹) ^ t) :=
    scalar_step_shrink ((↑(Work.Peluse.symIcc N).card : ℂ))⁻¹ ((((m * L' : ℕ) : ℂ))⁻¹)
      ((((L' : ℕ) : ℂ))⁻¹) (((m : ℂ) ^ (2 * t))⁻¹) t (scalar_key_shrink m L' t)
  let Sig : ℂ := ∑ jj : (Fin t → Fin m) × (Fin t → Fin m),
          ∑ r : Fin t → ↥(Work.Peluse.arithIcc c L'),
            ∑ r' : Fin t → ↥(Work.Peluse.arithIcc c L'),
              Wf t (fun _ : Fin t → Bool => f)
                ((fun i => (r i : ℤ) - (r' i : ℤ))
                  + (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))))
  have hL : Work.Peluse.prodCubeSum t (fun _ : Fin t => Work.Peluse.arithIcc c (m * L'))
        (Work.Peluse.symIcc N) (fun _ : Fin t → Bool => f)
      = ((↑(Work.Peluse.symIcc N).card : ℂ))⁻¹
          * ((((m * L' : ℕ) : ℂ))⁻¹) ^ t * ((((m * L' : ℕ) : ℂ))⁻¹) ^ t * Sig := by
    rw [prodCubeSum_const_shrink (Work.Peluse.arithIcc c (m * L')) (Work.Peluse.symIcc N)
      (fun _ : Fin t → Bool => f) (hcorner _)]
    rw [block_sum_shrink c hL' hm e he (Wf t (fun _ : Fin t → Bool => f))]
    simp only [hPa]
    rfl
  have hR : (∑ jj : (Fin t → Fin m) × (Fin t → Fin m),
        Work.Peluse.prodCubeSum t (fun _ : Fin t => Work.Peluse.arithIcc c L')
          (Work.Peluse.symIcc N)
          (fun ω : Fin t → Bool => Work.Peluse.shift
            (Work.Peluse.cornerShift (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f))
      = ((↑(Work.Peluse.symIcc N).card : ℂ))⁻¹
          * ((((L' : ℕ) : ℂ))⁻¹) ^ t * ((((L' : ℕ) : ℂ))⁻¹) ^ t * Sig := by
    rw [Finset.sum_congr rfl (fun jj _ => hblock jj)]
    simp only [hPq]
    rw [sum_mul_const_shrink (fun jj : (Fin t → Fin m) × (Fin t → Fin m) =>
      ∑ r : Fin t → ↥(Work.Peluse.arithIcc c L'),
        ∑ r' : Fin t → ↥(Work.Peluse.arithIcc c L'),
          Wf t (fun _ : Fin t → Bool => f)
            ((fun i => (r i : ℤ) - (r' i : ℤ))
              + (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ)))))]
  have hmain : Work.Peluse.prodCubeSum t (fun _ : Fin t => Work.Peluse.arithIcc c (m * L'))
        (Work.Peluse.symIcc N) (fun _ : Fin t → Bool => f)
      = ((m : ℂ) ^ (2 * t))⁻¹ *
        ∑ jj : (Fin t → Fin m) × (Fin t → Fin m),
          Work.Peluse.prodCubeSum t (fun _ : Fin t => Work.Peluse.arithIcc c L')
            (Work.Peluse.symIcc N)
            (fun ω : Fin t → Bool => Work.Peluse.shift
              (Work.Peluse.cornerShift (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f) := by
    rw [hL, hR, hsc2]
    ring
  have hterm : ∀ jj : (Fin t → Fin m) × (Fin t → Fin m),
      ‖Work.Peluse.prodCubeSum t (fun _ : Fin t => Work.Peluse.arithIcc c L')
          (Work.Peluse.symIcc N)
          (fun ω : Fin t → Bool => Work.Peluse.shift
            (Work.Peluse.cornerShift (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖
        ≤ Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c L')
            (Work.Peluse.symIcc N) f := by
    intro jj
    have hfin : ∀ ω : Fin t → Bool, Work.Peluse.FinSuppZ (Work.Peluse.shift
        (Work.Peluse.cornerShift (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f) :=
      fun ω => finsupp_shift_shrink hf _
    have hgcs := Work.Peluse.BoxNorm.prodCubeSum_norm_le ht
      (fun _ : Fin t => Work.Peluse.arithIcc c L') (Work.Peluse.symIcc N)
      (fun ω : Fin t → Bool => Work.Peluse.shift
        (Work.Peluse.cornerShift (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f) hfin
    have hprod : (∏ ω : Fin t → Bool, Work.Peluse.boxNorm t
          (fun _ : Fin t => Work.Peluse.arithIcc c L') (Work.Peluse.symIcc N)
          (Work.Peluse.shift
            (Work.Peluse.cornerShift (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f))
        = Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c L')
            (Work.Peluse.symIcc N) f := by
      have hpt : ∀ ω : Fin t → Bool, Work.Peluse.boxNorm t
            (fun _ : Fin t => Work.Peluse.arithIcc c L') (Work.Peluse.symIcc N)
            (Work.Peluse.shift
              (Work.Peluse.cornerShift (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)
          = (Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c L')
              (Work.Peluse.symIcc N) f) ^ (1 / (2 : ℝ) ^ t) := by
        intro ω
        rw [Work.Peluse.boxNorm,
          Work.Peluse.BoxNorm.boxNormPow_shift t (fun _ : Fin t => Work.Peluse.arithIcc c L')
            (Work.Peluse.symIcc N) f _ hf]
      rw [Finset.prod_congr rfl (fun ω _ => hpt ω), Finset.prod_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact Work.Peluse.BoxNorm.rpow_root_pow
        (norm_nonneg (Work.Peluse.boxSumPow t (fun _ : Fin t => Work.Peluse.arithIcc c L')
          (Work.Peluse.symIcc N) f)) t
    rw [← hprod]
    exact hgcs
  have hcard : ((Fintype.card ((Fin t → Fin m) × (Fin t → Fin m))) : ℝ)
      = ((m : ℝ)) ^ (2 * t) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
    rw [← pow_add, show t + t = 2 * t by omega]
  have hmne : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmn : ‖((m : ℂ) ^ (2 * t))⁻¹‖ = (((m : ℝ)) ^ (2 * t))⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  rw [Work.Peluse.boxNormPow, Work.Peluse.boxSumPow, hmain]
  calc ‖((m : ℂ) ^ (2 * t))⁻¹ *
        ∑ jj : (Fin t → Fin m) × (Fin t → Fin m),
          Work.Peluse.prodCubeSum t (fun _ : Fin t => Work.Peluse.arithIcc c L')
            (Work.Peluse.symIcc N)
            (fun ω : Fin t → Bool => Work.Peluse.shift
              (Work.Peluse.cornerShift (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖
      ≤ ‖((m : ℂ) ^ (2 * t))⁻¹‖ *
          ‖∑ jj : (Fin t → Fin m) × (Fin t → Fin m),
            Work.Peluse.prodCubeSum t (fun _ : Fin t => Work.Peluse.arithIcc c L')
              (Work.Peluse.symIcc N)
              (fun ω : Fin t → Bool => Work.Peluse.shift
                (Work.Peluse.cornerShift (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖ :=
        norm_mul_le _ _
    _ ≤ (((m : ℝ)) ^ (2 * t))⁻¹ *
          ∑ jj : (Fin t → Fin m) × (Fin t → Fin m),
            ‖Work.Peluse.prodCubeSum t (fun _ : Fin t => Work.Peluse.arithIcc c L')
              (Work.Peluse.symIcc N)
              (fun ω : Fin t → Bool => Work.Peluse.shift
                (Work.Peluse.cornerShift (fun i => c * L' * ((jj.1 i : ℤ) - (jj.2 i : ℤ))) 0 ω) f)‖ := by
        rw [hmn]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (((m : ℝ)) ^ (2 * t))⁻¹ *
          ∑ _jj : (Fin t → Fin m) × (Fin t → Fin m),
            Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c L')
              (Work.Peluse.symIcc N) f := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum (fun jj _ => hterm jj)
    _ = Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c L')
          (Work.Peluse.symIcc N) f := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ hmne), one_mul]

/-! ## The target theorem -/

theorem arithIcc_shrink_dvd_ge (t : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (c : ℤ) (hc : 0 < c) (L' L : ℕ), 1 ≤ L' → L' ∣ L → ∀ {N : ℕ} (f : ℤ → ℂ),
    Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
    C * Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c L) (Work.Peluse.symIcc N) f
      ≤ Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c L') (Work.Peluse.symIcc N) f := by
  refine ⟨1, one_pos, ?_⟩
  intro c hc L' L hL' hdvd N f hfN hfb
  rcases Nat.eq_zero_or_pos t with ht0 | ht
  · subst ht0
    have heq : (fun _ : Fin 0 => Work.Peluse.arithIcc c L)
        = (fun _ : Fin 0 => Work.Peluse.arithIcc c L') :=
      funext (fun i => Fin.elim0 i)
    rw [heq, one_mul]
  · rcases Nat.eq_zero_or_pos L with hL0 | hLpos
    · subst hL0
      rw [boxNormPow_arithIcc_zero_shrink ht c (Work.Peluse.symIcc N) f, one_mul]
      show (0 : ℝ) ≤ ‖Work.Peluse.boxSumPow t (fun _ : Fin t => Work.Peluse.arithIcc c L')
        (Work.Peluse.symIcc N) f‖
      exact norm_nonneg _
    · obtain ⟨k, hk⟩ := hdvd
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkp
        · rw [hk0, mul_zero] at hk
          omega
        · exact hkp
      have hk' : L = k * L' := by rw [hk, Nat.mul_comm]
      obtain ⟨e, he⟩ := arithIcc_blockEquiv_shrink (c := c) (ne_of_gt hc) (L' := L') (m := k)
        (L := k * L') rfl hL' hk1
      have hmain := shrink_of_data (N := N) ht (ne_of_gt hc) hL' hk1
        (Work.Peluse.FinSuppZ.of_supportIn hfN)
        (fun G h h' => tsum_cube_corner_eq_shrink G h h') e he
      rw [hk', one_mul]
      exact hmain

end

end Work.Peluse.Concat
