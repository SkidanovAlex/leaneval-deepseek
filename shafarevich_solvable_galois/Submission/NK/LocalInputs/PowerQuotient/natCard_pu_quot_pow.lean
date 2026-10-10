import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.NK.LocalInputs.PowerQuotient.LamIndex
import Submission.NK.LocalInputs.PowerQuotient.natCard_torsionSubgroup_quot_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p`-power quotient of the principal units `U¹ = 1 + 𝔪` of a `p`-adic field

For a number field `K`, a finite prime `𝔭` and the prime `p` (the residue characteristic of `𝔭`),
the group of principal units `U¹ = 1 + 𝔪 ⊆ 𝒪_κˣ` of the completion `κ = K_𝔭` satisfies

  `#(U¹ / (U¹)^p) = p ^ ([κ : ℚ_p] + δ)`,  `δ = zetaIndicator p κ`,

i.e. `p ^ (localDegree K 𝔭 + zetaIndicator p (𝔭.adicCompletion K))`.  This is the classical
structure of `U¹` (`U¹` modulo its `p`-power torsion is a free `ℤ_p`-module of rank `[κ : ℚ_p]`).

The route: the `p`-adic logarithm `lamFun` identifies `U¹` modulo its `p`-power torsion with the
additive subgroup `Λ = log U¹ ⊆ κ` of rank `[κ : ℚ_p]` (`relIndex_Lam_map_mul_p`), and the
`p`-power torsion `μ_{p^∞}(κ)` contributes the factor `p ^ δ`
(`natCard_torsionSubgroup_quot_pow`).  The splitting of `U¹/(U¹)^p` along the surjection
`U¹ → Λ` is the general group-theoretic count `natCard_quot_powMonoidHom_eq_mul` of the commons.
-/

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero
open IsDedekindDomain

namespace NK.LocalInputs.PowerQuotient

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [NumberField K]
variable {𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}

/-! ## The `p`-power torsion lies in the principal units -/

/-- **Every `p`-power torsion unit of `𝒪_κ` is a principal unit.**  Indeed a `p`-power root of
unity of `κ` is `≡ 1` modulo `𝔪` (`val_one_sub_lt_one_of_pow_eq_one`). -/
lemma torsionSubgroup_le_pu_one (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    torsionSubgroup 𝔭 p ≤ pu 𝔭 1 := by
  intro u hu
  rw [mem_pu_iff_val]
  rw [mem_torsionSubgroup_iff] at hu
  obtain ⟨m, hm⟩ := hu
  have hval : (((coeUnit 𝔭 u : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K) ^ p ^ m) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hm, Units.val_one]
  have hlt := val_one_sub_lt_one_of_pow_eq_one (K := K) (𝔭 := 𝔭) hp hres ⟨m, hval⟩
  have hsub : (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) - 1
      = -(1 - ((coeUnit 𝔭 u : (𝔭.adicCompletion K)ˣ) : 𝔭.adicCompletion K)) := by
    simp [coeUnit]
  rw [hsub, Valuation.map_neg]
  have h1 : (-(↑(1:ℕ) : ℤ)) = (-1 : ℤ) := by norm_num
  rw [h1]
  exact lt_one_le_exp_neg_one hlt

/-! ## A root of unity in the disk of the logarithm is trivial -/

/-- **The only root of unity in the disk of the `p`-adic logarithm is `1`.**

Indeed if `w ^ n = 1` with `n ≠ 0` and `w` lies in the disk, then `n • log w = log (w ^ n) = 0`,
so `log w = 0` (`κ` has characteristic zero), and `w = exp (log w) = exp 0 = 1`. -/
lemma eq_one_of_pow_eq_one_of_mem_disk (D : LogData 𝔭 M) {w : 𝔭.adicCompletion K}
    (hw : Disk 𝔭 M w) {n : ℕ} (hn : n ≠ 0) (hwn : w ^ n = 1) : w = 1 := by
  haveI : CharZero (𝔭.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔭
  have h := log_pow D hw n
  rw [hwn, log_one] at h
  have hlog : D.log w = 0 := by
    have h2 : (n : 𝔭.adicCompletion K) * D.log w = 0 := by
      simpa [nsmul_eq_mul] using h.symm
    exact (mul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hn)
  rw [← D.exp_log w hw, hlog, D.exp_zero]

/-! ## The kernel of the logarithm: the `p`-power torsion of `U¹` -/

/-- The `p`-power torsion of `𝒪_κˣ` lies in the kernel of the `p`-adic logarithm on `U¹`. -/
lemma lamFun_eq_zero_of_mem_torsionSubgroup (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    {u : ↥(pu 𝔭 1)} (hu : (u : (𝔭.adicCompletionIntegers K)ˣ) ∈ torsionSubgroup 𝔭 p) :
    lamFun D hp hres u = 0 := by
  rw [mem_torsionSubgroup_iff] at hu
  obtain ⟨m, hm⟩ := hu
  have hζpow : (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K) ^ p ^ m) = 1 := by
    have h := congrArg (fun x : (𝔭.adicCompletion K)ˣ => (x : 𝔭.adicCompletion K)) hm
    simpa [coeUnit, Units.val_pow_eq_pow_val] using h
  set w : 𝔭.adicCompletion K :=
    ((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K) ^ p ^ (lamK 𝔭 M) with hw
  have hwDisk : Disk 𝔭 M w := by
    have hold := deep_pow_mem' (K := K) (𝔭 := 𝔭) (M := M) (p := p) hp hres u.2
    have hval := (mem_pu_iff_val (K := K) 𝔭 M
      ((u : (𝔭.adicCompletionIntegers K)ˣ) ^ p ^ lamK 𝔭 M)).mp hold
    have hcoe : ((↑((u : (𝔭.adicCompletionIntegers K)ˣ) ^ p ^ lamK 𝔭 M) : 𝔭.adicCompletion K)) = w := by
      rw [hw, Units.val_pow_eq_pow_val]
      simp
    rw [Disk, ← hcoe]
    exact hval
  have hwroot : w ^ p ^ m = 1 := by
    rw [hw, ← pow_mul, mul_comm (p ^ lamK 𝔭 M) (p ^ m), pow_mul, hζpow, one_pow]
  have hw1 : w = 1 :=
    eq_one_of_pow_eq_one_of_mem_disk D hwDisk (pow_ne_zero m hp.ne_zero) hwroot
  rw [lamFun_eq_zero_iff]
  rw [← hw]
  exact hw1

/-- A principal unit whose logarithm vanishes is a `p`-power torsion unit. -/
lemma mem_torsionSubgroup_of_lamFun_eq_zero (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    {u : ↥(pu 𝔭 1)} (h : lamFun D hp hres u = 0) :
    (u : (𝔭.adicCompletionIntegers K)ˣ) ∈ torsionSubgroup 𝔭 p := by
  rw [mem_torsionSubgroup_iff]
  refine ⟨lamK 𝔭 M, ?_⟩
  have h2 := (lamFun_eq_zero_iff D hp hres u).mp h
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val]
  simp only [coeUnit, Units.coe_map]
  exact h2

/-! ## The logarithm as a homomorphism -/

/-- **The `p`-adic logarithm of the principal units**, as a homomorphism of `U¹` onto the
additive group `Λ = log U¹`, written multiplicatively via `Multiplicative`. -/
noncomputable def lamFunHom (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    ↥(pu 𝔭 1) →* Multiplicative ↥(Lam D hp hres) where
  toFun u := Multiplicative.ofAdd ⟨lamFun D hp hres u, lamFun_mem_Lam D hp hres u⟩
  map_one' := by
    rw [ofAdd_eq_one]
    exact Subtype.ext ((lamFun_eq_zero_iff D hp hres 1).mpr (by simp))
  map_mul' u v := by
    rw [← ofAdd_add]
    congr 1
    exact Subtype.ext (lamFun_mul D hp hres u v)

lemma lamFunHom_surjective (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    Function.Surjective (lamFunHom D hp hres) := by
  rintro ⟨x, hx⟩
  obtain ⟨u, rfl⟩ := hx
  exact ⟨u, rfl⟩

/-- `Λ` is torsion free (it is an additive subgroup of the characteristic zero field `κ`), so the
`p`-th power map on `Multiplicative Λ` is injective. -/
lemma lamFunHom_pow_eq_one (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (x : Multiplicative ↥(Lam D hp hres)) (hx : x ^ p = 1) : x = 1 := by
  haveI : CharZero (𝔭.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔭
  have h1 : p • (x.toAdd : ↥(Lam D hp hres)) = 0 := by
    have h := toAdd_pow x p
    rw [hx, toAdd_one] at h
    exact h.symm
  have h2 : (x.toAdd : 𝔭.adicCompletion K) = 0 := by
    have h3 : (p : 𝔭.adicCompletion K) * ((x.toAdd : ↥(Lam D hp hres)) : 𝔭.adicCompletion K) = 0 := by
      have hc := congrArg (fun y : ↥(Lam D hp hres) => (y : 𝔭.adicCompletion K)) h1
      simpa [nsmul_eq_mul] using hc
    exact (mul_eq_zero.mp h3).resolve_left (Nat.cast_ne_zero.mpr hp.ne_zero)
  have h4 : (x.toAdd : ↥(Lam D hp hres)) = 0 := Subtype.ext h2
  calc x = Multiplicative.ofAdd x.toAdd := (ofAdd_toAdd x).symm
    _ = 1 := by rw [h4, ofAdd_zero]

/-- **The kernel of the logarithm on `U¹` is exactly the `p`-power torsion of `𝒪_κˣ`.** -/
lemma ker_lamFunHom_eq (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    (lamFunHom D hp hres).ker = (torsionSubgroup 𝔭 p).subgroupOf (pu 𝔭 1) := by
  ext u
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  constructor
  · intro h
    refine mem_torsionSubgroup_of_lamFun_eq_zero D hp hres ?_
    have h2 : Multiplicative.ofAdd (⟨lamFun D hp hres u, lamFun_mem_Lam D hp hres u⟩ :
        ↥(Lam D hp hres)) = 1 := h
    exact congrArg Subtype.val (ofAdd_eq_one.mp h2)
  · intro h
    have h2 := lamFun_eq_zero_of_mem_torsionSubgroup D hp hres h
    show Multiplicative.ofAdd (⟨lamFun D hp hres u, lamFun_mem_Lam D hp hres u⟩ :
      ↥(Lam D hp hres)) = 1
    rw [ofAdd_eq_one]
    exact Subtype.ext h2

/-! ## The `p`-power quotient of a `Multiplicative` group -/

/-- **The `p`-power quotient of `Multiplicative Λ` is the quotient of `Λ` by `p Λ`.**  Group
theoretically, `x ^ p` on `Multiplicative Λ` corresponds to `x ↦ p • x` on `Λ`, so the `p`-th
powers of `Multiplicative Λ` are the image of the multiplication-by-`p` map, and the quotient by
them is the quotient of `Λ` by that image. -/
lemma natCard_multiplicative_quot_powMonoidHom {A : Type*} [AddCommGroup A]
    (Λ : AddSubgroup A) (p : ℕ) :
    Nat.card (Multiplicative ↥Λ ⧸ (powMonoidHom p : Multiplicative ↥Λ →* Multiplicative ↥Λ).range)
      = (Λ.map (nsmulAddMonoidHom (α := A) p)).relIndex Λ := by
  have hhom : (powMonoidHom p : Multiplicative ↥Λ →* Multiplicative ↥Λ)
      = AddMonoidHom.toMultiplicative (nsmulAddMonoidHom (α := ↥Λ) p) := by
    ext x
    simp
  have hB : (Λ.map (nsmulAddMonoidHom (α := A) p)).comap Λ.subtype
      = (nsmulAddMonoidHom (α := ↥Λ) p).range := by
    ext x
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_map, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
    · rintro ⟨y, rfl⟩
      exact ⟨(y : A), y.2, rfl⟩
  rw [← Subgroup.index_eq_card, hhom]
  rw [show (AddMonoidHom.toMultiplicative (nsmulAddMonoidHom (α := ↥Λ) p)).range
      = AddSubgroup.toSubgroup ((nsmulAddMonoidHom (α := ↥Λ) p).range) from rfl]
  rw [AddSubgroup.index_toSubgroup, ← hB]
  rw [AddSubgroup.index_comap, AddSubgroup.range_subtype]

/-! ## The two factors -/

/-- A uniformizer of the completion has value `exp (-1)`. -/
lemma uniformizer_val_eq (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    vv 𝔭 ((Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K)
      (K := K) 𝔭 : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
  Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one 𝔭

/-- **The `p`-power quotient of `Λ = log U¹`** has order `p ^ [κ : ℚ_p]`, the index of `p Λ`
in `Λ`. -/
lemma natCard_Lam_quot_pow (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    Nat.card (Multiplicative ↥(Lam D hp hres) ⧸
        (powMonoidHom p : Multiplicative ↥(Lam D hp hres) →*
          Multiplicative ↥(Lam D hp hres)).range) =
      p ^ NK.LocalInputs.localDegree K 𝔭 := by
  rw [natCard_multiplicative_quot_powMonoidHom]
  have hhom : nsmulAddMonoidHom (α := 𝔭.adicCompletion K) p
      = AddMonoidHom.mulLeft ((p : ℕ) : 𝔭.adicCompletion K) := by
    ext x
    simp [nsmul_eq_mul]
  rw [hhom]
  exact relIndex_Lam_map_mul_p D hp hres _ (uniformizer_val_eq 𝔭)

/-- **The `p`-power quotient of the `p`-power torsion** has order `p ^ δ`. -/
lemma natCard_ker_lamFunHom_quot_pow (D : LogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    Nat.card (↥(lamFunHom D hp hres).ker ⧸
        (powMonoidHom p : ↥(lamFunHom D hp hres).ker →*
          ↥(lamFunHom D hp hres).ker).range) =
      p ^ NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K) := by
  have hker := ker_lamFunHom_eq D hp hres
  let e : ↥(lamFunHom D hp hres).ker ≃* ↥(torsionSubgroup 𝔭 p) :=
    hker ▸ Subgroup.subgroupOfEquivOfLe (torsionSubgroup_le_pu_one (K := K) (𝔭 := 𝔭) (p := p) hp hres)
  rw [natCard_quot_powMonoidHom_eq_of_mulEquiv p e]
  exact natCard_torsionSubgroup_quot_pow 𝔭 hp hres

/-! ## The main theorem -/

/-- **The `p`-power quotient of the principal units** of the completion `κ = K_𝔭`:
`#(U¹/(U¹)^p) = p ^ ([κ : ℚ_p] + δ)` where `δ = zetaIndicator p κ` is the indicator of `ζ_p ∈ κ`.

The logarithm splits `U¹` into its `p`-power torsion `μ_{p^∞}(κ)` and the torsion-free additive
group `Λ = log U¹`; both are compatible with the `p`-th power map, so the count is the product of
the two factors `p ^ δ` and `p ^ [κ : ℚ_p]`. -/
theorem natCard_pu_quot_pow {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p M : ℕ}
    (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (D : NK.LocalInputs.PowerQuotient.LogData 𝔭 M) :
    Nat.card (↥(NK.LocalInputs.PowerQuotient.pu 𝔭 1) ⧸
      (powMonoidHom p : ↥(NK.LocalInputs.PowerQuotient.pu 𝔭 1) →*
        ↥(NK.LocalInputs.PowerQuotient.pu 𝔭 1)).range) =
      p ^ (NK.LocalInputs.localDegree K 𝔭 +
        NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion K)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hmain := Commons.NumberTheory.NumberField.Completion.natCard_quot_powMonoidHom_eq_mul
    (lamFunHom D hp hres) (lamFunHom_surjective D hp hres) p (lamFunHom_pow_eq_one D hp hres)
  rw [hmain, natCard_Lam_quot_pow D hp hres, natCard_ker_lamFunHom_quot_pow D hp hres, pow_add]

end

end NK.LocalInputs.PowerQuotient
