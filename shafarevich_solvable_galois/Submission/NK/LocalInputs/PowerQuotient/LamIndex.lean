import Submission.NK.LocalInputs.PowerQuotient.Lam
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero
open IsDedekindDomain

namespace NK.LocalInputs.PowerQuotient

variable {K : Type*} [Field K] [NumberField K]

noncomputable section

section Main

variable {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)} {p : ℕ} {M : ℕ}

/-- The residue field of the completion has `p ^ f` elements, `f` the inertia degree of `𝔭`. -/
lemma natCard_residueField_eq_pow (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) =
      p ^ 𝔭.asIdeal.inertiaDeg ℤ := by
  have hmem : (p : NumberField.RingOfIntegers ℚ) ∈
      (NK.LocalInputs.primeBelow K 𝔭).asIdeal := by
    rw [NK.LocalInputs.primeBelow_asIdeal, Ideal.mem_under]
    simpa using NK.LocalInputs.ResidueChar.ratPrime_mem_asIdeal_of_charP 𝔭 hp hres
  have h := Commons.NumberTheory.NumberField.Completion.card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
    (NK.LocalInputs.primeBelow K 𝔭) p hp hmem K 𝔭 (NK.LocalInputs.primeBelow_liesOver K 𝔭)
  rw [h, NK.LocalInputs.Degree.inertiaDeg_rat_eq 𝔭.asIdeal 𝔭.ne_bot]

/-- The "fractional level" `{x : v x ≤ exp S}`. -/
def fracLevel (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) (S : ℕ) :
    AddSubgroup (𝔭.adicCompletion K) where
  carrier := {x | vv 𝔭 x ≤ (WithZero.exp (S : ℤ) : Zstar)}
  zero_mem' := by
    show vv 𝔭 (0 : 𝔭.adicCompletion K) ≤ (WithZero.exp (S : ℤ) : Zstar)
    rw [map_zero]; exact zero_le
  add_mem' := by
    intro x y hx hy
    show vv 𝔭 (x + y) ≤ (WithZero.exp (S : ℤ) : Zstar)
    exact Valuation.map_add_le (v := vv 𝔭) hx hy
  neg_mem' := by
    intro x hx
    show vv 𝔭 (-x) ≤ (WithZero.exp (S : ℤ) : Zstar)
    rw [Valuation.map_neg]; exact hx

lemma mem_fracLevel_iff (S : ℕ) (x : 𝔭.adicCompletion K) :
    x ∈ fracLevel 𝔭 S ↔ vv 𝔭 x ≤ (WithZero.exp (S : ℤ) : Zstar) := Iff.rfl

lemma levelSub_le_fracLevel (S : ℕ) : levelSub 𝔭 0 ≤ fracLevel 𝔭 S := by
  intro x hx
  rw [mem_fracLevel_iff]
  have hx' : vv 𝔭 x ≤ (WithZero.exp (-(0 : ℤ)) : Zstar) :=
    (levelSub_eq_of_val (𝔭 := 𝔭) 0 x).mp hx
  have h1 : (WithZero.exp (-(0 : ℤ)) : Zstar) ≤ (WithZero.exp ((S : ℤ)) : Zstar) := by
    rw [show (-(0 : ℤ)) = (0 : ℤ) from by ring]
    exact WithZero.exp_le_exp.mpr (by positivity)
  exact le_trans hx' h1

lemma fracLevel_map_mul_pow (π : 𝔭.adicCompletionIntegers K)
    (hπ : vv 𝔭 ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) =
      (WithZero.exp (-(1 : ℤ)) : Zstar)) (S : ℕ) :
    (fracLevel 𝔭 S).map
        (AddMonoidHom.mulLeft (((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ^ S)) =
      levelSub 𝔭 0 := by
  have hπ0 : ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hval : vv 𝔭 (((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ^ S) =
      (WithZero.exp (-(S : ℤ)) : Zstar) := by
    rw [Valuation.map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  ext y
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hx' : vv 𝔭 x ≤ (WithZero.exp (S : ℤ) : Zstar) := (mem_fracLevel_iff (𝔭 := 𝔭) S x).mp hx
    refine (levelSub_eq_of_val (𝔭 := 𝔭) 0 y).mpr ?_
    rw [← hxy]
    change vv 𝔭 (((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ^ S * x) ≤
      (WithZero.exp (-(0 : ℤ)) : Zstar)
    rw [Valuation.map_mul, hval]
    calc (WithZero.exp (-(S : ℤ)) : Zstar) * vv 𝔭 x
        ≤ (WithZero.exp (-(S : ℤ)) : Zstar) * (WithZero.exp (S : ℤ) : Zstar) :=
          mul_le_mul' (le_refl _) hx'
      _ = 1 := by
          rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  · intro hy
    have hy' : vv 𝔭 y ≤ (WithZero.exp (0 : ℤ) : Zstar) :=
      (levelSub_eq_of_val (𝔭 := 𝔭) 0 y).mp hy
    refine ⟨y * (((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ^ S)⁻¹, ?_, ?_⟩
    · refine (mem_fracLevel_iff (𝔭 := 𝔭) S _).mpr ?_
      rw [Valuation.map_mul, Valuation.map_inv, hval]
      have h2 : ((WithZero.exp (-(S : ℤ)) : Zstar))⁻¹ = (WithZero.exp ((S : ℤ)) : Zstar) :=
        inv_eq_of_mul_eq_one_right (by
          rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero])
      rw [h2]
      calc vv 𝔭 y * (WithZero.exp (S : ℤ) : Zstar)
          ≤ (WithZero.exp (0 : ℤ) : Zstar) * (WithZero.exp (S : ℤ) : Zstar) :=
            mul_le_mul' hy' (le_refl _)
        _ = (WithZero.exp (S : ℤ) : Zstar) := one_mul _
    · change (((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ^ S) *
          (y * (((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ^ S)⁻¹) = y
      rw [← mul_assoc,
        mul_comm (((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ^ S) y,
        mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hπ0), mul_one]

/-- The index of the fractional level `{v ≤ exp S}` over the level `𝔪 ^ M`. -/
lemma relIndex_levelSub_fracLevel (π : 𝔭.adicCompletionIntegers K)
    (hπ : vv 𝔭 ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) =
      (WithZero.exp (-(1 : ℤ)) : Zstar)) (S : ℕ) :
    (levelSub 𝔭 M).relIndex (fracLevel 𝔭 S) =
      (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ (M + S) := by
  have hπ0 : ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hinj : Function.Injective
      (AddMonoidHom.mulLeft (((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ^ S)) :=
    fun a b hab => mul_left_cancel₀ (pow_ne_zero _ hπ0) hab
  have hval : vv 𝔭 (((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ^ S) =
      (WithZero.exp (-(S : ℤ)) : Zstar) := by
    rw [Valuation.map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have h := AddSubgroup.relIndex_map_map_of_injective
    (f := AddMonoidHom.mulLeft (((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ^ S))
    (levelSub 𝔭 M) (fracLevel 𝔭 S) hinj
  rw [levelSub_map_mulLeft_of_val hval M, fracLevel_map_mul_pow (𝔭 := 𝔭) π hπ S] at h
  rw [← h, relIndex_levelSub (𝔭 := 𝔭) (M := 0) (N := M + S) (Nat.zero_le _), Nat.sub_zero]

lemma Lam_le_fracLevel (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    Lam D hp hres ≤ fracLevel 𝔭 (lamK 𝔭 M * ram 𝔭 - M) := by
  rintro x ⟨u, rfl⟩
  rw [mem_fracLevel_iff]
  exact val_lamFun_le (K := K) (𝔭 := 𝔭) (M := M) (p := p) D hp hres u

/-- `Λ` has finite index over the level `𝔪 ^ M`. -/
lemma relIndex_levelSub_Lam_ne_zero (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (π : 𝔭.adicCompletionIntegers K)
    (hπ : vv 𝔭 ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) =
      (WithZero.exp (-(1 : ℤ)) : Zstar)) :
    (levelSub 𝔭 M).relIndex (Lam D hp hres) ≠ 0 := by
  intro h0
  have hΛ := Lam_le_fracLevel (K := K) (𝔭 := 𝔭) (M := M) (p := p) D hp hres
  have hB : (levelSub 𝔭 M).relIndex (fracLevel 𝔭 (lamK 𝔭 M * ram 𝔭 - M)) ≠ 0 := by
    rw [relIndex_levelSub_fracLevel (𝔭 := 𝔭) (M := M) π hπ]
    haveI hfin : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
      Commons.NumberTheory.NumberField.Completion.finite_residueField_adicCompletion K 𝔭
    haveI hne : Nonempty (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := ⟨0⟩
    exact pow_ne_zero _ (Nat.pos_iff_ne_zero.mp Nat.card_pos)
  exact hB ((AddSubgroup.relIndex_eq_zero_of_le_right hΛ) h0)

/-- The levels are antitone. -/
lemma levelSub_le_levelSub {M N : ℕ} (h : M ≤ N) : levelSub 𝔭 N ≤ levelSub 𝔭 M := by
  intro x hx
  rw [levelSub_eq_of_val] at hx ⊢
  refine le_trans hx ?_
  exact WithZero.exp_le_exp.mpr (by omega)

/-- **The index of `p Λ` in `Λ`**: `[Λ : pΛ] = p ^ [K_𝔭 : ℚ_p]`. -/
theorem relIndex_Lam_map_mul_p (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (π : 𝔭.adicCompletionIntegers K)
    (hπ : vv 𝔭 ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) =
      (WithZero.exp (-(1 : ℤ)) : Zstar)) :
    ((Lam D hp hres).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))).relIndex
      (Lam D hp hres) = p ^ NK.LocalInputs.localDegree K 𝔭 := by
  have hA : levelSub 𝔭 M ≤ Lam D hp hres :=
    levelSub_le_Lam (K := K) (𝔭 := 𝔭) (M := M) (p := p) D hp hres
  have hfin : (levelSub 𝔭 M).relIndex (Lam D hp hres) ≠ 0 :=
    relIndex_levelSub_Lam_ne_zero (K := K) (𝔭 := 𝔭) (M := M) (p := p) D hp hres π hπ
  haveI hchar : CharZero (𝔭.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔭
  have hp0 : ((p : ℕ) : 𝔭.adicCompletion K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hinj : Function.Injective (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K)) :=
    fun a b hab => mul_left_cancel₀ hp0 hab
  have hpA : (levelSub 𝔭 M).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K)) =
      levelSub 𝔭 (M + ram 𝔭) := levelSub_map_mul_p (K := K) (𝔭 := 𝔭) (p := p) hp hres M
  have hpA_le : (levelSub 𝔭 M).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K)) ≤
      levelSub 𝔭 M := by
    rw [hpA]
    exact levelSub_le_levelSub (𝔭 := 𝔭) (Nat.le_add_right M (ram 𝔭))
  have hpΛ_le : (Lam D hp hres).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K)) ≤
      Lam D hp hres := by
    rintro y ⟨x, hx, hxy⟩
    change ((p : ℕ) : 𝔭.adicCompletion K) * x = y at hxy
    rw [← hxy, show ((p : ℕ) : 𝔭.adicCompletion K) * x = p • x from (nsmul_eq_mul _ _).symm]
    exact (Lam D hp hres).nsmul_mem hx p
  -- the p-multiplication transfer
  have htrans : ((levelSub 𝔭 M).map
        (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))).relIndex
      ((Lam D hp hres).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))) =
      (levelSub 𝔭 M).relIndex (Lam D hp hres) :=
    AddSubgroup.relIndex_map_map_of_injective (H := levelSub 𝔭 M) (K := Lam D hp hres) hinj
  have e1 : ((levelSub 𝔭 M).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))).relIndex
        ((Lam D hp hres).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))) *
      ((Lam D hp hres).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))).relIndex
        (Lam D hp hres) =
      ((levelSub 𝔭 M).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))).relIndex
        (Lam D hp hres) :=
    AddSubgroup.relIndex_mul_relIndex (H := (levelSub 𝔭 M).map
      (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K)))
      (K := (Lam D hp hres).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K)))
      (L := Lam D hp hres) (AddSubgroup.map_mono hA) hpΛ_le
  have e2 : ((levelSub 𝔭 M).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))).relIndex
        (levelSub 𝔭 M) * (levelSub 𝔭 M).relIndex (Lam D hp hres) =
      ((levelSub 𝔭 M).map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))).relIndex
        (Lam D hp hres) :=
    AddSubgroup.relIndex_mul_relIndex (H := (levelSub 𝔭 M).map
      (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K)))
      (K := levelSub 𝔭 M) (L := Lam D hp hres) hpA_le hA
  have hkey : (AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
        (Lam D hp hres)).relIndex (Lam D hp hres) * (levelSub 𝔭 M).relIndex (Lam D hp hres) =
      (AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
        (levelSub 𝔭 M)).relIndex (levelSub 𝔭 M) * (levelSub 𝔭 M).relIndex (Lam D hp hres) := by
    calc (AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
            (Lam D hp hres)).relIndex (Lam D hp hres) * (levelSub 𝔭 M).relIndex (Lam D hp hres)
        = (AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
            (Lam D hp hres)).relIndex (Lam D hp hres) *
          ((AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
            (levelSub 𝔭 M)).relIndex
              (AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
                (Lam D hp hres))) := by rw [htrans]
      _ = (AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
            (levelSub 𝔭 M)).relIndex
              (AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
                (Lam D hp hres)) *
          (AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
            (Lam D hp hres)).relIndex (Lam D hp hres) := by rw [mul_comm]
      _ = (AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
            (levelSub 𝔭 M)).relIndex (Lam D hp hres) := e1
      _ = (AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
            (levelSub 𝔭 M)).relIndex (levelSub 𝔭 M) * (levelSub 𝔭 M).relIndex (Lam D hp hres) :=
          e2.symm
  have hcancel : (AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
        (Lam D hp hres)).relIndex (Lam D hp hres) =
      (AddSubgroup.map (AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K))
        (levelSub 𝔭 M)).relIndex (levelSub 𝔭 M) :=
    mul_right_cancel₀ hfin hkey
  rw [hcancel, hpA, relIndex_levelSub (𝔭 := 𝔭) (M := M) (N := M + ram 𝔭) (Nat.le_add_right M _),
    Nat.add_sub_cancel_left, natCard_residueField_eq_pow (K := K) (𝔭 := 𝔭) (p := p) hp hres,
    ← pow_mul, NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg 𝔭]
  congr 1
  rw [ram]
  ring

end Main

end

end NK.LocalInputs.PowerQuotient
