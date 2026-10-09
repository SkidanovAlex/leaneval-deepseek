import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Tame

open Polynomial IntermediateField

/-- **An automorphism multiplying the Kummer generator by `ζ`.**  Let `F` be a field, `a ∈ F`,
`β` an element of an `F`-algebra `E` with `β ^ n = a`, and suppose `X ^ n - C a` is irreducible
over `F`; let `ζ` be a primitive `n`-th root of unity in `F`.  Then the simple extension `F⟮β⟯`
admits an `F`-automorphism sending `β` to `ζ * β`. -/
theorem kummerLayer_algEquiv_gen_smul {F E : Type*} [Field F] [Field E] [Algebra F E]
    {n : ℕ} (hn : 0 < n) {a : F} {β : E} (hβ : β ^ n = algebraMap F E a)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (hirr : Irreducible (X ^ n - C a)) :
    ∃ σ : F⟮β⟯ ≃ₐ[F] F⟮β⟯, σ (AdjoinSimple.gen F β) = ζ • AdjoinSimple.gen F β := by
  have hβint : IsIntegral F β := ⟨X ^ n - C a, monic_X_pow_sub_C a hn.ne', by simp [hβ]⟩
  haveI : FiniteDimensional F ↥F⟮β⟯ := IntermediateField.adjoin.finiteDimensional hβint
  have hminp : minpoly F β = X ^ n - C a :=
    (minpoly.eq_of_irreducible_of_monic hirr (by simp [hβ])
      (monic_X_pow_sub_C a hn.ne')).symm
  have hgen : ((AdjoinSimple.gen F β : F⟮β⟯) : E) ^ n = algebraMap F E a := by
    simpa using hβ
  have hgen' : (AdjoinSimple.gen F β : F⟮β⟯) ^ n = algebraMap F (↥F⟮β⟯) a := by
    apply Subtype.ext
    simpa using hgen
  have hζgen : (ζ • AdjoinSimple.gen F β : F⟮β⟯) ^ n = algebraMap F (↥F⟮β⟯) a := by
    rw [Algebra.smul_def, mul_pow, ← map_pow, hζ.pow_eq_one, map_one, one_mul, hgen']
  have hroot : (ζ • AdjoinSimple.gen F β : F⟮β⟯) ∈ (minpoly F β).aroots (↥F⟮β⟯) := by
    rw [mem_aroots]
    refine ⟨by rw [hminp]; exact (monic_X_pow_sub_C a hn.ne').ne_zero, ?_⟩
    rw [hminp]
    simp [hζgen]
  set σa : F⟮β⟯ →ₐ[F] F⟮β⟯ := (algHomAdjoinIntegralEquiv F hβint).symm ⟨_, hroot⟩ with hσa
  have hσagen : σa (AdjoinSimple.gen F β) = ζ • AdjoinSimple.gen F β :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen F hβint ⟨_, hroot⟩
  have hinj : Function.Injective σa := RingHom.injective (σa : F⟮β⟯ →+* F⟮β⟯)
  have hsurj : Function.Surjective σa :=
    LinearMap.injective_iff_surjective.mp (show Function.Injective σa.toLinearMap from hinj)
  refine ⟨AlgEquiv.ofBijective σa ⟨hinj, hsurj⟩, ?_⟩
  rw [← hσagen]
  rfl

/-- Elementary number theory: `n ∣ m * k` iff `n / gcd n m ∣ k`. -/
theorem kummerLayer_dvd_mul_iff_div_gcd_dvd (n m k : ℕ) (hn : 0 < n) :
    n ∣ m * k ↔ n / Nat.gcd n m ∣ k := by
  have hg : 0 < Nat.gcd n m := Nat.gcd_pos_of_pos_left m hn
  have hnr : Nat.gcd n m * (n / Nat.gcd n m) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)
  have hmr : Nat.gcd n m * (m / Nat.gcd n m) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_right n m)
  have h1 : (n ∣ m * k) ↔
      Nat.gcd n m * (n / Nat.gcd n m) ∣ Nat.gcd n m * ((m / Nat.gcd n m) * k) := by
    rw [hnr, ← mul_assoc, hmr]
  rw [h1, Nat.mul_dvd_mul_iff_left hg]
  exact (Nat.coprime_div_gcd_div_gcd hg).dvd_mul_left

/-- Transfer of a singleton adjoin along the inclusion `L ↪ E`. -/
theorem kummerLayer_mem_adjoin_singleton_lift_iff {F E : Type*} [Field F] [Field E]
    [Algebra F E] (L : IntermediateField F E) {y : E} (hy : y ∈ L) (x : L) :
    (x : E) ∈ IntermediateField.adjoin F ({y} : Set E) ↔
      x ∈ IntermediateField.adjoin F ({⟨y, hy⟩} : Set L) := by
  rw [← IntermediateField.lift_adjoin_simple (F := F) L ⟨y, hy⟩, IntermediateField.mem_lift]

/-- **The fixed points of the `m`-th powers on a Kummer layer.**  Let `F` be a field of
characteristic zero containing a primitive `n`-th root of unity, `a ∈ F`, `β` an element of an
`F`-algebra `E` with `β ^ n = a`, and suppose `X ^ n - C a` is irreducible over `F`.  Then an
element `x ∈ F⟮β⟯` which is fixed by the `m`-th power of every `F`-automorphism of `F⟮β⟯` already
lies in the subfield `F⟮β ^ (n / gcd n m)⟯`. -/
theorem kummerLayer_fixedField_pow {F E : Type*} [Field F] [CharZero F] [Field E]
    [Algebra F E] {n m : ℕ} (hn : 0 < n) {a : F} {β : E} (hβ : β ^ n = algebraMap F E a)
    (hζ : (primitiveRoots n F).Nonempty) (hirr : Irreducible (X ^ n - C a))
    {x : E} (hx : x ∈ IntermediateField.adjoin F {β})
    (hfix : ∀ τ : Gal(↥(IntermediateField.adjoin F {β}) / F),
      (τ ^ m) ⟨x, hx⟩ = ⟨x, hx⟩) :
    x ∈ IntermediateField.adjoin F {β ^ (n / Nat.gcd n m)} := by
  obtain ⟨ζ, hζmem⟩ := hζ
  have hζ : IsPrimitiveRoot ζ n := (mem_primitiveRoots hn).mp hζmem
  obtain ⟨σ, hσ⟩ := kummerLayer_algEquiv_gen_smul hn hβ hζ hirr
  have hβint : IsIntegral F β := ⟨X ^ n - C a, monic_X_pow_sub_C a hn.ne', by simp [hβ]⟩
  haveI : FiniteDimensional F ↥F⟮β⟯ := IntermediateField.adjoin.finiteDimensional hβint
  let pb : PowerBasis F ↥F⟮β⟯ := IntermediateField.adjoin.powerBasis hβint
  let y : ↥F⟮β⟯ := ⟨x, hx⟩
  have hyfix : (σ ^ m) y = y := hfix σ
  let c : Fin pb.dim → F := fun i => pb.basis.repr y i
  -- The automorphism `σ` acts on the generator by the `ζ`-multiple, hence on powers diagonally.
  have hσgen' : σ (AdjoinSimple.gen F β) =
      algebraMap F ↥F⟮β⟯ ζ * AdjoinSimple.gen F β := by
    rw [hσ, Algebra.smul_def]
  have hgenpow : ∀ k : ℕ, (σ ^ k) (AdjoinSimple.gen F β) =
      (algebraMap F ↥F⟮β⟯ ζ) ^ k * AdjoinSimple.gen F β := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, AlgEquiv.commutes, hσgen',
        pow_succ, mul_assoc]
  have hpg : pb.gen = AdjoinSimple.gen F β := rfl
  have hσm_basis : ∀ i : Fin pb.dim, (σ ^ m) (pb.basis i) =
      algebraMap F ↥F⟮β⟯ (ζ ^ (m * (i : ℕ))) * pb.basis i := by
    intro i
    rw [PowerBasis.basis_eq_pow, hpg, map_pow, hgenpow, mul_pow, ← pow_mul, ← map_pow]
  have hsum : y = ∑ i : Fin pb.dim, c i • pb.basis i := pb.basis.sum_repr y |>.symm
  have hT : (σ ^ m) y = ∑ i : Fin pb.dim, (c i * ζ ^ (m * (i : ℕ))) • pb.basis i := by
    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (σ ^ m) (c i • pb.basis i) = c i • (σ ^ m) (pb.basis i) from
      LinearEquiv.map_smul ((σ ^ m).toLinearEquiv) (c i) (pb.basis i)]
    rw [hσm_basis i, ← Algebra.smul_def, smul_smul]
  have hzero : ∑ i : Fin pb.dim, (c i * ζ ^ (m * (i : ℕ)) - c i) • pb.basis i = 0 := by
    rw [show (∑ i : Fin pb.dim, (c i * ζ ^ (m * (i : ℕ)) - c i) • pb.basis i)
      = ∑ i : Fin pb.dim, ((c i * ζ ^ (m * (i : ℕ))) • pb.basis i - c i • pb.basis i) from
      Finset.sum_congr rfl fun i _ => by rw [sub_smul]]
    rw [Finset.sum_sub_distrib, ← hT, hyfix, ← hsum, sub_self]
  have hcoeff : ∀ i : Fin pb.dim, c i * ζ ^ (m * (i : ℕ)) - c i = 0 :=
    Fintype.linearIndependent_iff.mp pb.basis.linearIndependent
      (fun i => c i * ζ ^ (m * (i : ℕ)) - c i) hzero
  have hc0 : ∀ i : Fin pb.dim, ¬ (n / Nat.gcd n m) ∣ (i : ℕ) → c i = 0 := by
    intro i hi
    have h2 : c i * ζ ^ (m * (i : ℕ)) = c i := sub_eq_zero.mp (hcoeff i)
    have h3 : ζ ^ (m * (i : ℕ)) ≠ 1 := fun h =>
      hi ((kummerLayer_dvd_mul_iff_div_gcd_dvd n m (i : ℕ) hn).mp
        ((hζ.pow_eq_one_iff_dvd _).mp h))
    have h4 : c i * (ζ ^ (m * (i : ℕ)) - 1) = 0 := by rw [mul_sub, mul_one, h2, sub_self]
    rcases mul_eq_zero.mp h4 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) h3
  -- Every remaining term of the power-basis expansion lies in `F⟮β ^ (n / gcd n m)⟯`.
  have hmemL : y ∈ IntermediateField.adjoin F
      ({AdjoinSimple.gen F β ^ (n / Nat.gcd n m)} : Set ↥F⟮β⟯) := by
    rw [hsum]
    refine Submodule.sum_mem
      ((IntermediateField.adjoin F
        ({AdjoinSimple.gen F β ^ (n / Nat.gcd n m)} : Set ↥F⟮β⟯)).toSubmodule)
      (fun i _ => ?_)
    by_cases hfi : (n / Nat.gcd n m) ∣ (i : ℕ)
    · have hi : (i : ℕ) = (n / Nat.gcd n m) * ((i : ℕ) / (n / Nat.gcd n m)) :=
        (Nat.mul_div_cancel' hfi).symm
      have hb : pb.basis i =
          (AdjoinSimple.gen F β ^ (n / Nat.gcd n m)) ^
            ((i : ℕ) / (n / Nat.gcd n m)) := by
        rw [PowerBasis.basis_eq_pow, hpg]
        conv_lhs => rw [hi]
        rw [pow_mul]
      rw [hb]
      exact Submodule.smul_mem _ _
        (pow_mem (IntermediateField.mem_adjoin_simple_self F _) _)
    · rw [hc0 i hfi, zero_smul]
      exact Submodule.zero_mem _
  -- Finally transfer the membership back to the ambient field `E`.
  have hγE : ((AdjoinSimple.gen F β ^ (n / Nat.gcd n m) : ↥F⟮β⟯) : E) =
      β ^ (n / Nat.gcd n m) := by simp
  have hgoal : (y : E) ∈ IntermediateField.adjoin F
      ({((AdjoinSimple.gen F β ^ (n / Nat.gcd n m) : ↥F⟮β⟯) : E)} : Set E) := by
    rw [kummerLayer_mem_adjoin_singleton_lift_iff (F := F) F⟮β⟯
      (AdjoinSimple.gen F β ^ (n / Nat.gcd n m)).2 y]
    exact hmemL
  simpa only [hγE] using hgoal

end NK.TameStructureDeep.Tame
