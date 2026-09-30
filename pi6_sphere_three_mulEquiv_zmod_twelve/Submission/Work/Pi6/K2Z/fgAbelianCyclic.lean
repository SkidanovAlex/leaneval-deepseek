import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.K2Z.finrank_zmodTensor_prod
import Submission.Work.Pi6.K2Z.finrankZModTensorQuot
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 1000000

namespace Work.Pi6.K2Z

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- Over a finite field, `finrank` is determined by the cardinality of the module. -/
lemma finrank_zmod_eq_of_natCard_eq (p : ℕ) (hp : p.Prime) (V W : Type*)
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (h : Nat.card V = Nat.card W) : Module.finrank (ZMod p) V = Module.finrank (ZMod p) W := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hV := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
  have hW := Module.natCard_eq_pow_finrank (K := ZMod p) (V := W)
  rw [hcard] at hV hW
  have key : p ^ Module.finrank (ZMod p) V = p ^ Module.finrank (ZMod p) W := by
    rw [← hV, ← hW, h]
  have hfac := congrArg (fun m : ℕ => m.factorization p) key
  simpa [Nat.Prime.factorization_pow hp] using hfac

/-- Every element of a quotient `ℤ ⧸ (q)` with `q ≠ 0` is torsion. -/
lemma zsmul_eq_zero_of_mem_span {I : Ideal ℤ} {a : ℤ} (ha : a ∈ I) (x : ℤ ⧸ I) :
    a • x = 0 := by
  have hmk : (Ideal.Quotient.mk I a : ℤ ⧸ I) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
  calc a • x = (Ideal.Quotient.mk I a : ℤ ⧸ I) * x := by rw [Algebra.smul_def]; rfl
    _ = 0 := by rw [hmk, zero_mul]

/-- Every element of `⨁ᵢ ℤ/qᵢ` (with `qᵢ ≠ 0`) is torsion. -/
lemma directSum_quot_isTorsion {ι : Type*} [Fintype ι] (q : ι → ℤ) (hq : ∀ i, q i ≠ 0) :
    ∀ x : DirectSum ι (fun i => ℤ ⧸ Ideal.span ({(q i)} : Set ℤ)),
      ∃ n : ℕ, 0 < n ∧ n • x = 0 := by
  classical
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | of i m =>
      have hmem : ((q i).natAbs : ℤ) ∈ Ideal.span ({(q i)} : Set ℤ) :=
        Ideal.mem_span_singleton.mpr (Int.dvd_natAbs.mpr dvd_rfl)
      have hzero : (q i).natAbs • m = 0 := by
        rw [← Nat.cast_smul_eq_nsmul ℤ ((q i).natAbs) m]
        exact zsmul_eq_zero_of_mem_span hmem m
      refine ⟨(q i).natAbs, Int.natAbs_pos.mpr (hq i), ?_⟩
      rw [← map_nsmul (DirectSum.of (fun i => ℤ ⧸ Ideal.span ({(q i)} : Set ℤ)) i)
        ((q i).natAbs) m, hzero, map_zero]
  | add x y hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
      have h1 : (a * b) • x = 0 := by rw [mul_comm a b, mul_smul, hax, smul_zero]
      have h2 : (a * b) • y = 0 := by rw [mul_smul, hby, smul_zero]
      rw [smul_add, h1, h2, add_zero]

/-- The `ZMod p`-rank of the extension of scalars object equals that of the plain tensor
product, for a finitely generated `ℤ`-module `A`. -/
lemma finrankExtendScalarsZMod_aux (A : Type) [AddCommGroup A] [Module ℤ A]
    [Module.Finite ℤ A] (p : ℕ) (hp : p.Prime) :
    Module.finrank (ZMod p) ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A))
      = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) A) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- the two underlying types differ only by the `ℤ`-module structure on `ZMod p`, which is unique
  have hinst : (inferInstance : Module ℤ (ZMod p)) = (Int.castRingHom (ZMod p)).toModule :=
    Subsingleton.elim _ _
  have hYX : (TensorProduct ℤ (ZMod p) A : Type)
      = ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A)) :=
    congrArg (fun i => @TensorProduct ℤ _ (ZMod p) A _ _ i _) hinst
  have hcard : Nat.card ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A))
      = Nat.card (TensorProduct ℤ (ZMod p) A) :=
    (Nat.card_congr (Equiv.cast hYX)).symm
  have hpcard : Nat.card (ZMod p) = p := by rw [Nat.card_eq_fintype_card, ZMod.card]
  -- the plain tensor product is finite dimensional
  haveI hYfin : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) A) := inferInstance
  have hYcard : Nat.card (TensorProduct ℤ (ZMod p) A)
      = p ^ Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) A) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) A), hpcard]
  -- hence the extension of scalars object is a finite set
  have hX0 : Nat.card ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A)) ≠ 0 := by
    rw [hcard, hYcard]
    exact pow_ne_zero _ hp.ne_zero
  haveI hXfin : Finite ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A)) :=
    (Nat.card_ne_zero.mp hX0).2
  have hXcard : Nat.card ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A))
      = p ^ Module.finrank (ZMod p) ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A))), hpcard]
  have key : p ^ Module.finrank (ZMod p)
        ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A))
      = p ^ Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) A) := by
    rw [← hXcard, ← hYcard, hcard]
  have hfac := congrArg (fun m : ℕ => m.factorization p) key
  simpa [Nat.Prime.factorization_pow hp] using hfac

theorem fgAbelianCyclic (A : Type) [AddCommGroup A] [Module.Finite ℤ A]
    (hr : Module.finrank ℚ ↥((ModuleCat.extendScalars (Int.castRingHom ℚ)).obj (ModuleCat.of ℤ A)) = 1)
    (hp : ∀ p : ℕ, p.Prime → Module.finrank (ZMod p)
      ↥((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of ℤ A)) ≤ 1) :
    Nonempty (A ≃+ ℤ) := by
  classical
  -- Step 1: structure theorem for the finitely generated `ℤ`-module `A`.
  obtain ⟨n, ι, instι, P, hP, E, ⟨Φ⟩⟩ := Module.equiv_free_prod_directSum (R := ℤ) (M := A)
  letI : Fintype ι := instι
  let T : Type := DirectSum ι fun i => ℤ ⧸ Ideal.span ({(P i) ^ (E i)} : Set ℤ)
  -- `Φ : A ≃ₗ[ℤ] (Fin n →₀ ℤ) × T`
  have hΦ : A ≃ₗ[ℤ] (Fin n →₀ ℤ) × T := Φ
  -- Step 2: the rank of `A` is one.
  have hrank : Module.rank ℤ A = 1 := by
    have h1 : Module.rank ℤ A = Module.rank ℤ (TensorProduct ℤ ℚ A) :=
      (IsLocalizedModule.rank_eq (p := nonZeroDivisors ℤ) le_rfl (TensorProduct.mk ℤ ℚ A 1)).symm
    have h2 : Module.rank ℤ (TensorProduct ℤ ℚ A) = Module.rank ℚ (TensorProduct ℤ ℚ A) :=
      (IsLocalization.rank_eq ℚ (p := nonZeroDivisors ℤ) le_rfl).symm
    have h3 : Module.rank ℚ (TensorProduct ℤ ℚ A) = 1 := by
      refine Cardinal.toNat_eq_one.mp ?_
      exact hr
    rw [h1, h2, h3]
  have hfrA : Module.finrank ℤ A = 1 := by
    show (Module.rank ℤ A).toNat = 1
    rw [hrank, Cardinal.toNat_eq_one]
  -- Step 3: `n ≤ 1`, by mapping `A` onto `Fin n →₀ ℤ`.
  have hn_le : n ≤ 1 := by
    have hsurj : Function.Surjective
        ((LinearMap.fst ℤ (Fin n →₀ ℤ) T).comp hΦ.toLinearMap) := by
      intro y
      obtain ⟨z, hz⟩ := hΦ.surjective (y, 0)
      exact ⟨z, by simp [hz]⟩
    have h := LinearMap.finrank_le_finrank_of_surjective
      (f := (LinearMap.fst ℤ (Fin n →₀ ℤ) T).comp hΦ.toLinearMap) hsurj
    simp only [Module.finrank_finsupp_self, Fintype.card_fin, hfrA] at h
    exact h
  -- Step 5 (aux): the direct sum `T` is a torsion module.
  have hTtors : ∀ x : T, ∃ k : ℕ, 0 < k ∧ k • x = 0 :=
    directSum_quot_isTorsion (fun i => (P i) ^ (E i)) (fun i => pow_ne_zero _ (hP i).ne_zero)
  -- Step 4: `n ≥ 1`, since `A` has an element of infinite order.
  have hn_ge : 1 ≤ n := by
    have hrank_ne : Module.rank ℤ A ≠ 0 := by rw [hrank]; exact one_ne_zero
    have : ∃ x : A, ∀ a : ℤ, a ≠ 0 → a • x ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hrank_ne ((rank_eq_zero_iff (R := ℤ) (M := A)).mpr hcon)
    obtain ⟨x, hx⟩ := this
    have hu : (hΦ x).1 ≠ 0 := by
      intro h0
      obtain ⟨k, hk, hk0⟩ := hTtors (hΦ x).2
      have hkA : k • x = 0 := by
        have hsm : k • hΦ x = 0 := by
          rw [Prod.smul_mk, h0, hk0, smul_zero]
          rfl
        have h1 : hΦ (k • x) = hΦ 0 := by rw [map_nsmul, hsm, map_zero]
        exact hΦ.injective h1
      exact hx (k : ℤ) (Nat.cast_ne_zero.mpr hk.ne')
        (by rw [Nat.cast_smul_eq_nsmul ℤ k x]; exact hkA)
    have hn0 : n ≠ 0 := by
      intro hn0
      have : Subsingleton (Fin n →₀ ℤ) := by
        subst hn0
        exact ⟨fun f g => Finsupp.ext fun i => i.elim0⟩
      exact hu (Subsingleton.elim _ _)
    omega
  have hn : n = 1 := le_antisymm hn_le hn_ge
  -- Step 6: `T` is finitely generated.
  haveI hTfin : Module.Finite ℤ T :=
    Module.Finite.of_surjective ((LinearMap.snd ℤ (Fin n →₀ ℤ) T).comp hΦ.toLinearMap) (by
      intro y
      obtain ⟨z, hz⟩ := hΦ.surjective (0, y)
      exact ⟨z, by simp [hz]⟩)
  haveI hprod_fin : Module.Finite ℤ ((Fin n →₀ ℤ) × T) :=
    Module.Finite.of_surjective (σ := RingHom.id ℤ) hΦ.toLinearMap hΦ.surjective
  -- Step 7: for every prime `p`, `ZMod p ⊗[ℤ] T` is trivial.
  have hsub (p : ℕ) (hpp : p.Prime) : Subsingleton (TensorProduct ℤ (ZMod p) T) := by
    haveI : Fact p.Prime := ⟨hpp⟩
    have hb : Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) A) ≤ 1 := by
      rw [← finrankExtendScalarsZMod_aux A p hpp]
      exact hp p hpp
    have hcard : Nat.card (TensorProduct ℤ (ZMod p) A)
        = Nat.card (TensorProduct ℤ (ZMod p) ((Fin n →₀ ℤ) × T)) :=
      Nat.card_congr (hΦ.lTensor (ZMod p)).toEquiv
    have htr : Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) A)
        = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) ((Fin n →₀ ℤ) × T)) :=
      finrank_zmod_eq_of_natCard_eq p hpp _ _ hcard
    have hsp := finrank_zmodTensor_prod p hpp (Fin n →₀ ℤ) T
    have hnf : Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (Fin n →₀ ℤ)) = n := by
      rw [Module.finrank_baseChange]
      simpa using Module.finrank_finsupp_self ℤ
    have hle : n + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) T) ≤ 1 := by
      calc n + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) T)
          = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) ((Fin n →₀ ℤ) × T)) := by
            rw [hsp, hnf, add_comm]
        _ = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) A) := htr.symm
        _ ≤ 1 := hb
    rw [hn] at hle
    have hzero : Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) T) = 0 := by omega
    exact Module.finrank_zero_iff.mp hzero
  -- Step 8: `T = 0`: every summand `ℤ ⧸ (P i)^(E i)` is trivial.
  have hTsub : Subsingleton T := by
    have hsum : ∀ i, Subsingleton (ℤ ⧸ Ideal.span ({(P i) ^ (E i)} : Set ℤ)) := by
      intro i
      by_contra hni
      have hnt : Nontrivial (ℤ ⧸ Ideal.span ({(P i) ^ (E i)} : Set ℤ)) :=
        not_subsingleton_iff_nontrivial.mp hni
      -- `E i ≠ 0`, else the summand would be `ℤ ⧸ ⊤`
      have hE : E i ≠ 0 := by
        intro h0
        have hsub : Subsingleton (ℤ ⧸ Ideal.span ({(P i) ^ (E i)} : Set ℤ)) := by
          rw [h0, pow_zero]
          exact Submodule.Quotient.subsingleton_iff.mpr Ideal.span_singleton_one
        exact (not_subsingleton_iff_nontrivial.mpr hnt) hsub
      -- `p := (P i).natAbs` is a prime dividing `(P i)^(E i)`
      have hpp : ((P i).natAbs).Prime :=
        Int.prime_iff_natAbs_prime.mp (hP i).prime
      have hdvd : ((P i).natAbs : ℤ) ∣ (P i) ^ (E i) :=
        dvd_pow (Int.natCast_dvd.mpr dvd_rfl) hE
      -- the `i`-th coordinate projection `T ↠ ℤ ⧸ (P i)^(E i)`
      let Mi : Type := ℤ ⧸ Ideal.span ({(P i) ^ (E i)} : Set ℤ)
      let proj : T →ₗ[ℤ] Mi :=
        { toFun := fun x => x i
          map_add' := fun x y => rfl
          map_smul' := fun r x => rfl }
      have hproj : Function.Surjective ⇑proj := by
        intro m
        refine ⟨DirectSum.of (fun i => ℤ ⧸ Ideal.span ({(P i) ^ (E i)} : Set ℤ)) i m, ?_⟩
        change ((DirectSum.of (fun i => ℤ ⧸ Ideal.span ({(P i) ^ (E i)} : Set ℤ)) i m : T) i) = m
        exact DirectSum.of_eq_same (β := fun i => ℤ ⧸ Ideal.span ({(P i) ^ (E i)} : Set ℤ)) i m
      -- tensoring this surjection with `ZMod p`
      have hsurj : Function.Surjective
          (LinearMap.lTensor (ZMod ((P i).natAbs)) proj) :=
        LinearMap.lTensor_surjective _ hproj
      -- the tensor of the summand is nontrivial (its `ZMod p`-dimension is one)
      have h1 : Nontrivial (TensorProduct ℤ (ZMod ((P i).natAbs)) Mi) := by
        haveI : Fact ((P i).natAbs).Prime := ⟨hpp⟩
        by_contra hc
        haveI := not_nontrivial_iff_subsingleton.mp hc
        have hfr := finrankZModTensorQuot ((P i).natAbs) hpp ((P i) ^ (E i)) hdvd
        have hz : Module.finrank (ZMod ((P i).natAbs))
            (TensorProduct ℤ (ZMod ((P i).natAbs)) Mi) = 0 :=
          Module.finrank_zero_of_subsingleton
        rw [hz] at hfr
        exact one_ne_zero hfr.symm
      have h2 : Nontrivial (TensorProduct ℤ (ZMod ((P i).natAbs)) T) := by
        obtain ⟨a, b, hab⟩ := h1
        obtain ⟨x, hx⟩ := hsurj a
        obtain ⟨y, hy⟩ := hsurj b
        exact ⟨x, y, fun hxy => hab (by rw [← hx, ← hy, hxy])⟩
      exact absurd (hsub ((P i).natAbs) hpp) (not_subsingleton_iff_nontrivial.mpr h2)
    exact ⟨fun x y => by ext i; exact (hsum i).elim (x i) (y i)⟩
  -- Step 9: `A ≅ ℤ`.
  rw [hn] at hΦ
  haveI : Unique T := ⟨⟨0⟩, fun a => hTsub.elim a 0⟩
  exact ⟨(hΦ.trans (LinearEquiv.prodUnique (R := ℤ) (M := Fin 1 →₀ ℤ) (M₂ := T))).trans
    ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin 1)).trans
      (LinearEquiv.funUnique (Fin 1) ℤ ℤ)) |>.toAddEquiv⟩

end

end Work.Pi6.K2Z
