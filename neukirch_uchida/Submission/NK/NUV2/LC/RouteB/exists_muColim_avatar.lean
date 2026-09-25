import Mathlib
import Submission.NK.NUV2.LC.RouteB.exists_unitsClass_of_isCyclic
import Submission.NK.NUV2.ABHN.kummerColim_surjective_pTorsion
import Submission.NK.HassePrinciple.kummerColim_injective
import Submission.NK.NUV2.ABHN.LocalBrauerAux

namespace NK.NUV2.LC.RouteB

open NK.HassePrinciple

/-! ## Additivity of the Kummer map on the colimits

The Kummer map `kummerColim p V : MuColim p V → H2Units V` is the `LevelSystem.lift` of the
compatible family of level-wise linear maps `kummerLevel p V L`.  On the colimit the additive
structure is the one chosen in `NK.NUV2.ABHN.instAddCommGroupMuColim` /
`NK.NUV2.ABHN.instAddCommGroupH2Units`, whose structure maps are additive; since every class of a
colimit is represented at a finite level, `kummerColim` is additive. -/

/-- **The Kummer map on the colimits is additive.** -/
lemma kummerColim_add {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup Gal(K'/K)) (x y : MuColim p V) :
    kummerColim p V (x + y) = kummerColim p V x + kummerColim p V y := by
  obtain ⟨L, a, ha⟩ :=
    NK.BrauerTwist.LevelSystem.ofLevel_surjective (S := muLevelSystem p V) x
  obtain ⟨L', b, hb⟩ :=
    NK.BrauerTwist.LevelSystem.ofLevel_surjective (S := muLevelSystem p V) y
  let M : FiniteGaloisIntermediateField K K' := L ⊔ L'
  have hLM : L ≤ M := le_sup_left
  have hL'M : L' ≤ M := le_sup_right
  let A : MuLevelH2 p V M := (muLevelSystem p V).map hLM a
  let B : MuLevelH2 p V M := (muLevelSystem p V).map hL'M b
  have hxM : x = MuColim.ofLevel p V M A :=
    ha.symm.trans (NK.BrauerTwist.LevelSystem.ofLevel_map hLM a).symm
  have hyM : y = MuColim.ofLevel p V M B :=
    hb.symm.trans (NK.BrauerTwist.LevelSystem.ofLevel_map hL'M b).symm
  rw [hxM, hyM, ← NK.NUV2.ABHN.MuColim.ofLevel_add, kummerColim_ofLevel, kummerColim_ofLevel,
    kummerColim_ofLevel, map_add, NK.NUV2.ABHN.H2Units.ofLevel_add]

/-- **The Kummer map on the colimits sends the zero to the zero.** -/
lemma kummerColim_zero {K K' : Type} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup Gal(K'/K)) :
    kummerColim p V (0 : MuColim p V) = 0 := by
  have h : kummerColim p V (0 : MuColim p V) =
      kummerColim p V (0 : MuColim p V) + kummerColim p V (0 : MuColim p V) := by
    simpa using kummerColim_add p V (0 : MuColim p V) 0
  exact (add_left_cancel (a := kummerColim p V (0 : MuColim p V)) (b := 0)
    (show kummerColim p V (0 : MuColim p V) + 0 =
      kummerColim p V (0 : MuColim p V) + kummerColim p V (0 : MuColim p V) from by
        rw [add_zero]; exact h)).symm

/-- **The `μ_p`-avatar of the cyclic-algebra class.**  Let `E/F` be a finite Galois extension of
number fields of prime degree `p` with `Gal(E/F)` cyclic.  Then the cyclic-algebra class
`γ : Fˣ → H2Units ⊤` of `NK.NUV2.LC.RouteB.exists_unitsClass_of_isCyclic` is `p`-torsion (its
level-`E` representative lies in `Br(E/F) = κˣ/N(Eˣ)`, a group of order `p`), hence has a preimage
`Y` under the (injective) Kummer map `kummerColim : MuColim p ⊤ → H2Units ⊤`
(`NK.NUV2.ABHN.kummerColim_surjective_pTorsion` for existence,
`NK.HassePrinciple.kummerColim_injective` for uniqueness).  `Y` is additive (built by the
colimit universal property from the additive `kummerLevel`, and injectivity of `kummerColim` lets
additivity transfer from `γ`), and detects the norm condition exactly as `γ` does.  This `Y` is the
`μ_p`-coefficient class whose image in `H2Profinite p ⊤` is the class `X` of the target statement. -/
theorem exists_muColim_avatar (p : ℕ) (hp : p.Prime)
    {F : Type} [Field F] [NumberField F] (F' : Type) [Field F'] [Algebra F F']
    [IsSepClosure F F'] (E : IntermediateField F F') [FiniteDimensional F E] [IsGalois F E]
    [NumberField ↥E] (hdeg : Module.finrank F E = p) (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E)) :
    ∃ (γ : Fˣ → NK.HassePrinciple.H2Units (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)))
      (Y : Fˣ → NK.HassePrinciple.MuColim (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F))),
      (∀ b₁ b₂ : Fˣ, γ (b₁ * b₂) = γ b₁ + γ b₂) ∧
      (∀ b : Fˣ, NK.HassePrinciple.kummerColim (K := F) (K' := F') p
        (⊤ : Subgroup Gal(F'/F)) (Y b) = γ b) ∧
      (∀ b₁ b₂ : Fˣ, Y (b₁ * b₂) = Y b₁ + Y b₂) ∧
      (∀ b : Fˣ, γ b = 0 ↔ b ∈ MonoidHom.range (Units.map (Algebra.norm F : ↥E →* F))) ∧
      (∀ b : Fˣ, Y b = 0 ↔ b ∈ MonoidHom.range (Units.map (Algebra.norm F : ↥E →* F))) := by
  classical
  obtain ⟨γ, hγadd, hγnorm⟩ :=
    exists_unitsClass_of_isCyclic p hp F' E hdeg hcyc
  -- `γ 1 = 0`, hence `γ` is additive for powers, hence `p • γ b = γ (b ^ p) = 0` because `b ^ p`
  -- is the norm of `algebraMap F E b` and `[E : F] = p`.
  have hγone : γ 1 = 0 := by
    have h := hγadd 1 1
    rw [mul_one] at h
    exact (add_left_cancel (a := γ 1) (b := 0)
      (show γ 1 + 0 = γ 1 + γ 1 from by rw [add_zero]; exact h)).symm
  have hγpow : ∀ (b : Fˣ) (n : ℕ), γ (b ^ n) = n • γ b := by
    intro b n
    induction n with
    | zero => simpa using hγone
    | succ k ih => rw [pow_succ, hγadd, ih, succ_nsmul]
  have hnorm : ∀ x : Fˣ, Units.map (Algebra.norm F : ↥E →* F)
      (Units.map (algebraMap F ↥E : F →* ↥E) x) = x ^ p := by
    intro x
    haveI : Module.Free F ↥E := Module.Free.of_divisionRing F ↥E
    have h := Algebra.norm_algebraMap (R := F) (S := ↥E) (x : F)
    rw [hdeg] at h
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.coe_map]
    exact h
  have hpγ : ∀ b : Fˣ, p • γ b = 0 := by
    intro b
    rw [← hγpow b p]
    exact (hγnorm (b ^ p)).mpr
      ⟨Units.map (algebraMap F ↥E : F →* ↥E) b, hnorm b⟩
  -- the `μ_p`-avatars, from exactness of the Kummer sequence in the limit
  choose Y hYspec using fun b =>
    NK.NUV2.ABHN.kummerColim_surjective_pTorsion p hp (γ b) (hpγ b)
  refine ⟨γ, Y, hγadd, ?_, ?_, hγnorm, ?_⟩
  · exact hYspec
  · -- `Y` is additive, by injectivity of `kummerColim` and additivity of `γ`
    intro b₁ b₂
    refine (NK.HassePrinciple.kummerColim_injective (K := F) (K' := F') p hp
      (⊤ : Subgroup Gal(F'/F))) ?_
    rw [kummerColim_add, hYspec b₁, hYspec b₂, hYspec (b₁ * b₂), hγadd b₁ b₂]
  · -- `Y` detects the norm condition exactly as `γ` does
    intro b
    have hz : NK.HassePrinciple.kummerColim (K := F) (K' := F') p
        (⊤ : Subgroup Gal(F'/F)) (0 : NK.HassePrinciple.MuColim (K := F) (K' := F') p
          (⊤ : Subgroup Gal(F'/F))) = 0 := kummerColim_zero p (⊤ : Subgroup Gal(F'/F))
    constructor
    · intro h
      refine (hγnorm b).mp ?_
      rw [← hYspec b, h, hz]
    · intro h
      exact (NK.HassePrinciple.kummerColim_injective (K := F) (K' := F') p hp
        (⊤ : Subgroup Gal(F'/F))) (by rw [hYspec b, hz]; exact (hγnorm b).mpr h)

end NK.NUV2.LC.RouteB
