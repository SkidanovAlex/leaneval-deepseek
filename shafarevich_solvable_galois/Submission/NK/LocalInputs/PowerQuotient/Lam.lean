import Submission.NK.LocalInputs.PowerQuotient.Setup
import Submission.NK.LocalInputs.ResidueChar.primesEquiv_primeBelow
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

section LevelShift

variable {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)}

/-- Multiplication by an element of valuation `exp (-t)` shifts the filtration by `t`. -/
lemma levelSub_map_mulLeft_of_val {t : ℕ} {a : 𝔭.adicCompletion K}
    (ha : vv 𝔭 a = (WithZero.exp (-(t : ℤ)) : Zstar)) (m : ℕ) :
    (levelSub 𝔭 m).map (AddMonoidHom.mulLeft a) = levelSub 𝔭 (m + t) := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  ext y
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hx' := (levelSub_eq_of_val (𝔭 := 𝔭) m x).mp hx
    change a * x = y at hxy
    refine (levelSub_eq_of_val (𝔭 := 𝔭) (m + t) _).mpr ?_
    rw [← hxy, Valuation.map_mul, ha]
    calc (WithZero.exp (-(t : ℤ)) : Zstar) * vv 𝔭 x
        ≤ (WithZero.exp (-(t : ℤ)) : Zstar) * (WithZero.exp (-(m : ℤ)) : Zstar) :=
          mul_le_mul' (le_refl _) hx'
      _ = (WithZero.exp (-(m : ℤ)) : Zstar) * (WithZero.exp (-(t : ℤ)) : Zstar) := mul_comm _ _
      _ = (WithZero.exp (-(((m + t : ℕ) : ℤ)))) := (exp_neg_add m t).symm
  · intro hy
    refine ⟨y / a, ?_, ?_⟩
    · refine (levelSub_eq_of_val (𝔭 := 𝔭) m _).mpr ?_
      have hy' : vv 𝔭 y ≤ (WithZero.exp (-(((m + t : ℕ) : ℤ)))) :=
        (levelSub_eq_of_val (𝔭 := 𝔭) (m + t) y).mp hy
      rw [exp_neg_add m t] at hy'
      rw [Valuation.map_div, ha]
      exact (div_le_iff₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)).mpr hy'
    · change a * (y / a) = y
      rw [mul_div_cancel₀ _ ha0]

/-- The index of two levels of the filtration: `[𝔪 ^ M : 𝔪 ^ N] = |κ| ^ (N - M)`. -/
theorem relIndex_levelSub {M N : ℕ} (hMN : M ≤ N) :
    (levelSub 𝔭 N).relIndex (levelSub 𝔭 M) =
      (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ (N - M) := by
  have hinj : Function.Injective
      (RingHom.toAddMonoidHom (algebraMap (𝔭.adicCompletionIntegers K) (𝔭.adicCompletion K))) := by
    intro x y h
    exact Subtype.ext h
  have h := AddSubgroup.relIndex_map_map_of_injective
    (f := RingHom.toAddMonoidHom (algebraMap (𝔭.adicCompletionIntegers K) (𝔭.adicCompletion K)))
    ((maxId 𝔭 ^ N).toAddSubgroup) ((maxId 𝔭 ^ M).toAddSubgroup) hinj
  have hmapN : ((maxId 𝔭 ^ N).toAddSubgroup).map
      (RingHom.toAddMonoidHom (algebraMap (𝔭.adicCompletionIntegers K) (𝔭.adicCompletion K))) =
      levelSub 𝔭 N := rfl
  have hmapM : ((maxId 𝔭 ^ M).toAddSubgroup).map
      (RingHom.toAddMonoidHom (algebraMap (𝔭.adicCompletionIntegers K) (𝔭.adicCompletion K))) =
      levelSub 𝔭 M := rfl
  rw [hmapN, hmapM] at h
  rw [h]
  have hkey : ((maxId 𝔭 ^ N).toAddSubgroup).relIndex ((maxId 𝔭 ^ M).toAddSubgroup) =
      ((maxId 𝔭 ^ (M + (N - M))).toAddSubgroup).relIndex ((maxId 𝔭 ^ M).toAddSubgroup) :=
    congrArg (fun t => ((maxId 𝔭 ^ t).toAddSubgroup).relIndex ((maxId 𝔭 ^ M).toAddSubgroup))
      (show N = M + (N - M) from by omega)
  rw [hkey]
  change ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ (M + (N - M))).toAddSubgroup).relIndex
      ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ M).toAddSubgroup) =
    (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ (N - M)
  exact relIndex_maximalIdeal_pow 𝔭 M (N - M)

end LevelShift

section Lam

variable {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)} {p : ℕ} {M : ℕ}

/-- The exponent used to define the logarithm of a principal unit. -/
def lamK (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) (M : ℕ) : ℕ := ram 𝔭 + M

/-- **The logarithm of a principal unit**, as an element of the completion: for `u ∈ U_1` we set
`log u = lp (u ^ p ^ (e + M)) / p ^ (e + M)`, where `lp` is the logarithm of the common,
defined on the disk `1 + 𝔪 ^ M`. -/
noncomputable def lamFun (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (u : ↥(pu 𝔭 1)) : 𝔭.adicCompletion K :=
  D.log ((((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K) ^ (p ^ (lamK 𝔭 M)))) /
    (((p : ℕ) : 𝔭.adicCompletion K) ^ (lamK 𝔭 M))

lemma lamK_pos (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    0 < lamK 𝔭 M := by
  have h := pu_le_one (K := K) (𝔭 := 𝔭) hp hres
  simp only [lamK]
  omega

/-- The `p ^ (e + M)`-th power of a principal unit lies in the disk of the logarithm. -/
lemma deep_pow_mem' (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    {u : (𝔭.adicCompletionIntegers K)ˣ} (hu : u ∈ pu 𝔭 1) :
    u ^ p ^ (lamK 𝔭 M) ∈ pu 𝔭 M :=
  deep_pow_mem (K := K) (𝔭 := 𝔭) (p := p) hp hres M hu

/-- The valuation of `p`. -/
lemma val_p_eq (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    vv 𝔭 ((p : ℕ) : 𝔭.adicCompletion K) = (WithZero.exp (-(ram 𝔭 : ℤ)) : Zstar) := by
  have hpval := val_prime_adicCompletion (K := K) 𝔭 hp hres
  rw [hpval, ← WithZero.exp_nsmul]
  congr 1
  simp [ram]

lemma p_pow_lamK_ne_zero (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    ((p : ℕ) : 𝔭.adicCompletion K) ^ lamK 𝔭 M ≠ 0 := by
  have h := val_p_eq (K := K) (𝔭 := 𝔭) (p := p) hp hres
  refine pow_ne_zero _ ?_
  intro hz
  rw [hz, map_zero] at h
  exact WithZero.exp_ne_zero h.symm

/-- The logarithm of a principal unit is bounded in terms of the filtration: its value is at
most `exp (e * (e + M) - M)`. -/
lemma val_lamFun_le (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (u : ↥(pu 𝔭 1)) :
    vv 𝔭 (lamFun D hp hres u) ≤
      (WithZero.exp (((lamK 𝔭 M * ram 𝔭 - M : ℕ)) : ℤ)) := by
  have hu : (u : (𝔭.adicCompletionIntegers K)ˣ) ∈ pu 𝔭 1 := u.2
  set w : 𝔭.adicCompletion K :=
    (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K)) ^ p ^ (lamK 𝔭 M) with hw
  have hd : Disk 𝔭 M w := by
    have h := (mem_pu_iff_val (K := K) 𝔭 M
      ((u : (𝔭.adicCompletionIntegers K)ˣ) ^ p ^ (lamK 𝔭 M))).mp
      (deep_pow_mem' (K := K) (𝔭 := 𝔭) (M := M) (p := p) hp hres hu)
    rw [Units.val_pow_eq_pow_val] at h
    exact h
  have hlog := D.val_log w hd
  have hmul : vv 𝔭 (lamFun D hp hres u) =
      vv 𝔭 (D.log w) / ((WithZero.exp (-(ram 𝔭 : ℤ)) : Zstar) ^ lamK 𝔭 M) := by
    rw [lamFun, Valuation.map_div, Valuation.map_pow,
      val_p_eq (K := K) (𝔭 := 𝔭) (p := p) hp hres]
  rw [hmul, hlog]
  rw [div_le_iff₀ (zero_lt_iff.mpr (pow_ne_zero _ (WithZero.exp_ne_zero)))]
  have hMle : M ≤ lamK 𝔭 M * ram 𝔭 := by
    have h1 : 1 ≤ ram 𝔭 := pu_le_one (K := K) (𝔭 := 𝔭) hp hres
    simp only [lamK]
    nlinarith
  have harith : (WithZero.exp (((lamK 𝔭 M * ram 𝔭 - M : ℕ)) : ℤ)) *
      ((WithZero.exp (-(ram 𝔭 : ℤ)) : Zstar) ^ lamK 𝔭 M) =
      (WithZero.exp (-(M : ℤ)) : Zstar) := by
    rw [← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1
    rw [Nat.cast_sub hMle]
    push_cast
    ring
  rw [harith]
  exact hd

/-- The logarithm is additive on the principal units. -/
lemma lamFun_mul (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (u v : ↥(pu 𝔭 1)) :
    lamFun D hp hres (u * v) = lamFun D hp hres u + lamFun D hp hres v := by
  have hu : (u : (𝔭.adicCompletionIntegers K)ˣ) ∈ pu 𝔭 1 := u.2
  have hv : (v : (𝔭.adicCompletionIntegers K)ˣ) ∈ pu 𝔭 1 := v.2
  have hdu : Disk 𝔭 M (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K) ^
      p ^ (lamK 𝔭 M)) := by
    have h := (mem_pu_iff_val (K := K) 𝔭 M
      ((u : (𝔭.adicCompletionIntegers K)ˣ) ^ p ^ (lamK 𝔭 M))).mp
      (deep_pow_mem' (K := K) (𝔭 := 𝔭) (M := M) (p := p) hp hres hu)
    rwa [Units.val_pow_eq_pow_val] at h
  have hdv : Disk 𝔭 M (((v : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K) ^
      p ^ (lamK 𝔭 M)) := by
    have h := (mem_pu_iff_val (K := K) 𝔭 M
      ((v : (𝔭.adicCompletionIntegers K)ˣ) ^ p ^ (lamK 𝔭 M))).mp
      (deep_pow_mem' (K := K) (𝔭 := 𝔭) (M := M) (p := p) hp hres hv)
    rwa [Units.val_pow_eq_pow_val] at h
  have hcoe : (((u * v : ↥(pu 𝔭 1)) : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K) =
      (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K) *
        ((v : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K)) := by
    rw [Subgroup.coe_mul, Units.val_mul]
    rfl
  rw [lamFun, hcoe, mul_pow, log_mul D hdu hdv, lamFun, lamFun, add_div]

/-- The kernel of the logarithm on the principal units is the group of `p`-power roots of
unity. -/
lemma lamFun_eq_zero_iff (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (u : ↥(pu 𝔭 1)) :
    lamFun D hp hres u = 0 ↔
      (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K) ^ p ^ (lamK 𝔭 M)) = 1 := by
  have hu : (u : (𝔭.adicCompletionIntegers K)ˣ) ∈ pu 𝔭 1 := u.2
  have hd : Disk 𝔭 M (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K) ^
      p ^ (lamK 𝔭 M)) := by
    have h := (mem_pu_iff_val (K := K) 𝔭 M
      ((u : (𝔭.adicCompletionIntegers K)ˣ) ^ p ^ (lamK 𝔭 M))).mp
      (deep_pow_mem' (K := K) (𝔭 := 𝔭) (M := M) (p := p) hp hres hu)
    rwa [Units.val_pow_eq_pow_val] at h
  rw [lamFun, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact (log_eq_zero_iff D hd).mp h
    · exact absurd h (p_pow_lamK_ne_zero (K := K) (𝔭 := 𝔭) (p := p) hp hres)
  · intro h
    left
    exact (log_eq_zero_iff D hd).mpr h

/-- **The image `Λ = log (U_1)` of the logarithm**, as an additive subgroup of the completion. -/
noncomputable def Lam (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    AddSubgroup (𝔭.adicCompletion K) where
  carrier := Set.range (lamFun D hp hres)
  zero_mem' := ⟨1, (lamFun_eq_zero_iff D hp hres 1).mpr (by simp)⟩
  add_mem' := by
    rintro x y ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u * v, lamFun_mul D hp hres u v⟩
  neg_mem' := by
    rintro x ⟨u, rfl⟩
    refine ⟨u⁻¹, ?_⟩
    have h1 : lamFun D hp hres (u * u⁻¹) = lamFun D hp hres u + lamFun D hp hres u⁻¹ :=
      lamFun_mul D hp hres u u⁻¹
    rw [mul_inv_cancel, (lamFun_eq_zero_iff D hp hres 1).mpr (by simp)] at h1
    have h2 : lamFun D hp hres u⁻¹ + lamFun D hp hres u = 0 := by
      rw [add_comm (lamFun D hp hres u⁻¹)]; exact h1.symm
    exact eq_neg_of_add_eq_zero_left h2

lemma lamFun_mem_Lam (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (u : ↥(pu 𝔭 1)) : lamFun D hp hres u ∈ Lam D hp hres :=
  ⟨u, rfl⟩

lemma lamFun_inv (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (u : ↥(pu 𝔭 1)) :
    lamFun D hp hres u⁻¹ = -lamFun D hp hres u := by
  have h1 : lamFun D hp hres (u * u⁻¹) = lamFun D hp hres u + lamFun D hp hres u⁻¹ :=
    lamFun_mul D hp hres u u⁻¹
  rw [mul_inv_cancel, (lamFun_eq_zero_iff D hp hres 1).mpr (by simp)] at h1
  have h2 : lamFun D hp hres u⁻¹ + lamFun D hp hres u = 0 := by
    rw [add_comm (lamFun D hp hres u⁻¹)]; exact h1.symm
  exact eq_neg_of_add_eq_zero_left h2

end Lam

section LamProperties

variable {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)} {p : ℕ} {M : ℕ}

lemma edisk_nsmul {x : 𝔭.adicCompletion K} (hx : EDisk 𝔭 M x) (n : ℕ) :
    EDisk 𝔭 M (n • x) := by
  rw [EDisk] at hx ⊢
  rw [nsmul_eq_mul, Valuation.map_mul]
  calc vv 𝔭 ((n : ℕ)) * vv 𝔭 x ≤ 1 * vv 𝔭 x :=
        mul_le_mul' (Commons.Analysis.Nonarchimedean.val_natCast_le_one (vv 𝔭) n) le_rfl
    _ = vv 𝔭 x := one_mul _
    _ ≤ _ := hx

/-- `exp` turns multiples into powers. -/
lemma exp_nsmul (D : LogData 𝔭 M) {x : 𝔭.adicCompletion K} (hx : EDisk 𝔭 M x) (n : ℕ) :
    D.exp (n • x) = (D.exp x) ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; exact D.exp_zero
  | succ k ih => rw [succ_nsmul, D.exp_add _ _ (edisk_nsmul hx k) hx, ih, pow_succ]

set_option maxHeartbeats 4000000 in
lemma levelSub_le_Lam (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    levelSub 𝔭 M ≤ Lam D hp hres := by
  intro x hx
  have hM1 : 1 ≤ M := D.hM
  have hx' : vv 𝔭 x ≤ (WithZero.exp (-(M : ℤ)) : Zstar) := (levelSub_eq_of_val (𝔭 := 𝔭) M x).mp hx
  have hxED : EDisk 𝔭 M x := hx'
  have hneg : EDisk 𝔭 M (-x) := by
    rw [EDisk, Valuation.map_neg]; exact hx'
  have hdx : Disk 𝔭 M (D.exp x) := by
    rw [Disk, D.val_exp_sub_one x hx']; exact hx'
  have hval1 : vv 𝔭 (D.exp x) = 1 := disk_val_eq_one D.hM hdx
  have hexpR : D.exp x ∈ 𝔭.adicCompletionIntegers K := by
    change D.exp x ∈ (vv 𝔭).valuationSubring
    rw [Valuation.mem_valuationSubring_iff, hval1]
  have hdi : Disk 𝔭 M (D.exp (-x)) := by
    rw [Disk, D.val_exp_sub_one (-x) hneg]; exact hneg
  have hvali : vv 𝔭 (D.exp (-x)) = 1 := disk_val_eq_one D.hM hdi
  have hinvR : D.exp (-x) ∈ 𝔭.adicCompletionIntegers K := by
    change D.exp (-x) ∈ (vv 𝔭).valuationSubring
    rw [Valuation.mem_valuationSubring_iff, hvali]
  let eR : 𝔭.adicCompletionIntegers K := ⟨D.exp x, hexpR⟩
  let iR : 𝔭.adicCompletionIntegers K := ⟨D.exp (-x), hinvR⟩
  have hmul1 : eR * iR = 1 := by
    apply Subtype.ext
    show D.exp x * D.exp (-x) = 1
    rw [← D.exp_add x (-x) hxED hneg, add_neg_cancel, D.exp_zero]
  let u₀ : (𝔭.adicCompletionIntegers K)ˣ := Units.mkOfMulEqOne eR iR hmul1
  have hu₀coe : ((u₀ : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) = D.exp x := rfl
  have hmemU : u₀ ∈ pu 𝔭 1 := by
    rw [mem_pu_iff_val, hu₀coe, D.val_exp_sub_one x hx']
    refine le_trans hx' (WithZero.exp_le_exp.mpr ?_)
    omega
  refine ⟨⟨u₀, hmemU⟩, ?_⟩
  show lamFun D hp hres ⟨u₀, hmemU⟩ = x
  have hcoe : (((⟨u₀, hmemU⟩ : ↥(pu 𝔭 1)) : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K)
      = D.exp x := rfl
  have hpow : ((((⟨u₀, hmemU⟩ : ↥(pu 𝔭 1)) : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K))
        ^ p ^ (lamK 𝔭 M) = D.exp ((p ^ (lamK 𝔭 M)) • x) := by
    rw [hcoe, ← exp_nsmul D hxED]
  rw [lamFun, hpow, D.log_exp _ (edisk_nsmul hxED _)]
  have hcast : (((p ^ (lamK 𝔭 M) : ℕ)) : 𝔭.adicCompletion K) =
      ((p : ℕ) : 𝔭.adicCompletion K) ^ lamK 𝔭 M := Nat.cast_pow _ _
  have hp0' : ((p ^ (lamK 𝔭 M) : ℕ) : 𝔭.adicCompletion K) ≠ 0 := by
    rw [hcast]
    exact p_pow_lamK_ne_zero (K := K) (𝔭 := 𝔭) (p := p) hp hres
  have hsm : ((p ^ (lamK 𝔭 M)) • x) = (((p ^ (lamK 𝔭 M) : ℕ)) : 𝔭.adicCompletion K) * x :=
    nsmul_eq_mul _ _
  have hp0 : ((p : ℕ) : 𝔭.adicCompletion K) ^ lamK 𝔭 M ≠ 0 :=
    p_pow_lamK_ne_zero (K := K) (𝔭 := 𝔭) (p := p) hp hres
  rw [hsm, hcast]
  set a : 𝔭.adicCompletion K := ((p : ℕ) : 𝔭.adicCompletion K) ^ lamK 𝔭 M with ha
  rw [div_eq_mul_inv, mul_comm (a * x) a⁻¹, ← mul_assoc, mul_comm a⁻¹ a,
    mul_inv_cancel₀ (by rw [ha]; exact hp0), one_mul]

end LamProperties

end

end NK.LocalInputs.PowerQuotient
