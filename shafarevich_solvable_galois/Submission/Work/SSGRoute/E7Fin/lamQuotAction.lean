import Submission.Work.SSGRoute.E7Fin.localAutHomAt_valued
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Γ`-module `Λ/pΛ` of the `p`-adic logarithm at a finite place

Lane `Work.SSGRoute.coker_obstruction_pt`, lattice half of `(C-ISO)` (see
`E7Fin/PING_session24_engine_and_uniformity_reduction.md` §8).

`Λ = log U¹` is the `p`-adic logarithm lattice of the completion `𝔮.adicCompletion K`
(`NK.LocalInputs.PowerQuotient.Lam`) and `Γ = Gal(K/k)_𝔮` is the decomposition group at the finite
place `𝔮`.  This file gives `Λ/pΛ` its `Γ`-action, descended from the local Galois action on `Λ`
(`E7Fin.map_Lam_le_localAutHom`), as a `DistribMulAction`, and records the `p`-torsion fact that
makes the quotient an `𝔽_p`-module.  This is the carrier on which the arithmetic isomorphism
`Λ/pΛ ≅ 𝔽_p[Γ]^c` of Milne *ADT* I.2.11 runs.

## Main definitions and results

* `E7Fin.LamSub`, `E7Fin.pLamSub`, `E7Fin.LamQuot` — `Λ`, `pΛ ⊆ Λ` and `Λ/pΛ`;
* `E7Fin.lamActHom` — the action of `γ ∈ Γ` on `Λ` as an additive homomorphism;
* `E7Fin.lamQuotActHom` — the induced action on `Λ/pΛ` (`QuotientAddGroup.map`), with the
  computation rule `E7Fin.lamQuotActHom_mk`;
* **`E7Fin.lamQuotAction`** — the resulting `DistribMulAction Γ (Λ/pΛ)`;
* `E7Fin.lamQuot_p_nsmul_eq_zero` — `p • x = 0` on `Λ/pΛ`.
-/

namespace Work.SSGRoute.E7Fin

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {k : Type} [Field k] [NumberField k]
variable {K : Type} [Field K] [NumberField K] [Algebra k K] [IsGalois k K]

noncomputable section

/-- The lattice `Λ = log U¹` of the completion at `𝔮`. -/
abbrev LamSub {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p) :
    AddSubgroup (𝔮.adicCompletion K) :=
  NK.LocalInputs.PowerQuotient.Lam D.toLogData hp hres

/-- The subgroup `pΛ ⊆ Λ`. -/
def pLamSub {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p) :
    AddSubgroup ↥(LamSub D hp hres) :=
  (nsmulAddMonoidHom (α := ↥(LamSub D hp hres)) p).range

/-- **The quotient `Λ/pΛ`.** -/
abbrev LamQuot {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p) : Type :=
  ↥(LamSub D hp hres) ⧸ pLamSub D hp hres

/-- **The action of `γ ∈ Γ` on `Λ`** as an additive homomorphism: the restriction of the local
automorphism `localAutHomAt γ` to the `Γ`-stable lattice `Λ`
(`E7Fin.map_Lam_le_localAutHom`). -/
def lamActHom {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (γ : ↥(MulAction.stabilizer Gal(K/k) (NK.GlobalCFT.Place.ofFinite 𝔮))) :
    ↥(LamSub D hp hres) →+ ↥(LamSub D hp hres) where
  toFun x := ⟨(Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ) x,
    map_Lam_le_localAutHom D hp hres γ x x.2⟩
  map_zero' := by
    refine Subtype.ext ?_
    exact map_zero _
  map_add' x y := by
    refine Subtype.ext ?_
    exact map_add _ _ _

/-- **The induced action on `Λ/pΛ`.**  The map is well defined because `pΛ` — the range of
multiplication by `p` on `Λ` — is preserved by any additive endomorphism of `Λ`. -/
def lamQuotActHom
    {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (γ : ↥(MulAction.stabilizer Gal(K/k) (NK.GlobalCFT.Place.ofFinite 𝔮))) :
    LamQuot D hp hres →+ LamQuot D hp hres :=
  QuotientAddGroup.map (pLamSub D hp hres) (pLamSub D hp hres) (lamActHom D hp hres γ) (by
    intro x hx
    rw [AddSubgroup.mem_comap]
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hx
    refine AddMonoidHom.mem_range.mpr ⟨lamActHom D hp hres γ y, ?_⟩
    rw [nsmulAddMonoidHom_apply, nsmulAddMonoidHom_apply, map_nsmul])

/-- The computation rule for the induced action on `Λ/pΛ`. -/
lemma lamQuotActHom_mk
    {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (γ : ↥(MulAction.stabilizer Gal(K/k) (NK.GlobalCFT.Place.ofFinite 𝔮)))
    (x : ↥(LamSub D hp hres)) :
    lamQuotActHom D hp hres γ (QuotientAddGroup.mk x)
      = QuotientAddGroup.mk (lamActHom D hp hres γ x) :=
  QuotientAddGroup.map_mk (pLamSub D hp hres) (pLamSub D hp hres) (lamActHom D hp hres γ) _ x

/-- **The `Γ`-action on `Λ/pΛ`.**  The group `Γ = Gal(K/k)_𝔮` acts on the quotient `Λ/pΛ` by the
local Galois action on `Λ`, descended through `pΛ`. -/
instance lamQuotAction
    {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p) :
    DistribMulAction ↥(MulAction.stabilizer Gal(K/k) (NK.GlobalCFT.Place.ofFinite 𝔮))
      (LamQuot D hp hres) where
  smul γ := lamQuotActHom D hp hres γ
  one_smul x := by
    refine QuotientAddGroup.induction_on x (fun y => ?_)
    show lamQuotActHom D hp hres 1 (QuotientAddGroup.mk y) = QuotientAddGroup.mk y
    rw [lamQuotActHom_mk]
    refine congrArg QuotientAddGroup.mk (Subtype.ext ?_)
    show (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) 1)
      (y : 𝔮.adicCompletion K) = (y : 𝔮.adicCompletion K)
    rw [map_one]
    rfl
  mul_smul γ δ x := by
    refine QuotientAddGroup.induction_on x (fun y => ?_)
    show lamQuotActHom D hp hres (γ * δ) (QuotientAddGroup.mk y)
      = lamQuotActHom D hp hres γ (lamQuotActHom D hp hres δ (QuotientAddGroup.mk y))
    rw [lamQuotActHom_mk, lamQuotActHom_mk, lamQuotActHom_mk]
    refine congrArg QuotientAddGroup.mk (Subtype.ext ?_)
    show (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) (γ * δ))
        (y : 𝔮.adicCompletion K)
      = (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) γ)
        ((Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) δ)
          (y : 𝔮.adicCompletion K))
    rw [map_mul]
    rfl
  smul_zero γ := map_zero _
  smul_add γ x y := map_add _ _ _

/-- **`Λ/pΛ` is killed by `p`.**  The class of `p • y` lies in `pΛ`, hence is zero in the quotient;
this is what makes `Λ/pΛ` an `𝔽_p`-module. -/
lemma lamQuot_p_nsmul_eq_zero
    {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (x : LamQuot D hp hres) : p • x = 0 := by
  refine QuotientAddGroup.induction_on x (fun y => ?_)
  show p • (QuotientAddGroup.mk y : LamQuot D hp hres) = 0
  have h0 : (QuotientAddGroup.mk (p • y) : LamQuot D hp hres) = 0 :=
    (QuotientAddGroup.eq_zero_iff (p • y)).mpr (AddMonoidHom.mem_range.mpr ⟨y, rfl⟩)
  rw [← h0]
  simpa using (map_nsmul (QuotientAddGroup.mk' (pLamSub D hp hres)) p y).symm

/-- **The `𝔽_p`-module structure on `Λ/pΛ`.**  Since `p • x = 0`
(`E7Fin.lamQuot_p_nsmul_eq_zero`), the usual module structure of an abelian group of exponent `p`
(`AddCommGroup.zmodModule`) applies. -/
noncomputable instance lamQuotModule
    {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p) :
    Module (ZMod p) (LamQuot D hp hres) :=
  AddCommGroup.zmodModule (fun x => lamQuot_p_nsmul_eq_zero D hp hres x)

/-- **The `Γ`-action is `𝔽_p`-linear**, i.e. `Λ/pΛ` is an `𝔽_p[Γ]`-module: the local Galois action
commutes with the `𝔽_p`-scalars, because it is an additive map and `𝔽_p`-scalars act through the
canonical `ZMod`-action (`ZMod.map_smul`). -/
instance lamQuotSmulComm
    {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p) :
    SMulCommClass ↥(MulAction.stabilizer Gal(K/k) (NK.GlobalCFT.Place.ofFinite 𝔮)) (ZMod p)
      (LamQuot D hp hres) where
  smul_comm γ c x := by
    show (lamQuotActHom D hp hres γ) (c • x) = c • (lamQuotActHom D hp hres γ) x
    exact ZMod.map_smul (lamQuotActHom D hp hres γ) c x

end

end Work.SSGRoute.E7Fin
