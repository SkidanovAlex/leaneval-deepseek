import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.LF.classLevelMap_pTorsion_surj
import Submission.Work.SSGRoute.PT.exists_level_p_dvd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The coherent `p`-torsion invariant `χ` on the class-formation `H²`

For a finite Galois extension `k ⊆ K` of number fields, an algebraically closed `Ω ⊇ K` and a prime
`p`, we construct a *coherent* family of invariants `χ L : H²(Gal(L/k), C_L) → ZMod p`, one for each
finite Galois level `K ≤ L ≤ Ω`, additive and injective on the `p`-torsion and compatible with the
level inflation `inflCIn` along `L ≤ L'`.

The construction fixes one *anchor* level `L₀` with `p ∣ [L₀ : k]`
(`Work.SSGRoute.PT.exists_level_p_dvd`).  At `L₀` the `p`-torsion of `H²(Gal(L₀/k), C_{L₀})` is
cyclic of order `p` (`Work.SSGRoute.pt_char_pTorsion`), giving an additive bijection `χ₀` onto
`ZMod p`.  For a level `L`, the `p`-torsion classes at `L ⊔ L₀` are exactly the inflations of the
`p`-torsion classes at `L₀` (`Work.SSGRoute.LF.classLevelMap_pTorsion_surj`, using that inflation is
injective on `H²`, `Work.SSGRoute.SylowLevel.inflCIn_injective`, and both `p`-torsion subgroups have
order `p`); pulling back `χ₀` along this isomorphism and pushing forward along `L → L ⊔ L₀` yields
the coherent family.

The final theorem `coherent_pTorsion_chi` is exactly the coherent `χ` consumed by the Poitou–Tate
assembly.
-/

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.SSGRoute.PT

open SSGRoute.PTExt CategoryTheory

namespace Coherent

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω]

/-! ## The compositum of two levels -/

/-- The compositum of two levels of `Ω`, as a level. -/
noncomputable def lvlSup (L L' : Lvl k K Ω) : Lvl k K Ω :=
  letI : FiniteDimensional K ↥L.1 := FiniteDimensional.right k K ↥L.1
  letI : FiniteDimensional K ↥L'.1 := FiniteDimensional.right k K ↥L'.1
  haveI : FiniteDimensional K ↥(L.1 ⊔ L'.1) := IntermediateField.finiteDimensional_sup L.1 L'.1
  haveI : NumberField ↥(L.1 ⊔ L'.1) := NumberField.of_module_finite K ↥(L.1 ⊔ L'.1)
  haveI : FiniteDimensional k ↥(L.1 ⊔ L'.1) := FiniteDimensional.trans k K ↥(L.1 ⊔ L'.1)
  haveI : IsGalois k ↥(L.1 ⊔ L'.1) := isGalois_sup (L := L.1) (L' := L'.1)
  ⟨L.1 ⊔ L'.1, inferInstance, inferInstance, inferInstance⟩

theorem lvlLeSupLeft (L L' : Lvl k K Ω) : L ≤ lvlSup L L' := by
  show (L : IntermediateField K Ω) ≤ L.1 ⊔ L'.1
  exact le_sup_left

theorem lvlLeSupRight (L L' : Lvl k K Ω) : L' ≤ lvlSup L L' := by
  show (L' : IntermediateField K Ω) ≤ L.1 ⊔ L'.1
  exact le_sup_right

theorem lvlSupLeSup {L L' M M' : Lvl k K Ω} (h : L ≤ L') (h' : M ≤ M') :
    lvlSup L M ≤ lvlSup L' M' := by
  show (L.1 ⊔ M.1 : IntermediateField K Ω) ≤ L'.1 ⊔ M'.1
  exact sup_le_sup h h'

/-! ## Inflation on `H²(·, C_·)` -/

/-- Inflation of `H²(Gal(L/k), C_L)` along `L ≤ L'` is injective. -/
theorem classLevelMap_injective (L L' : Lvl k K Ω) (h : L ≤ L') :
    Function.Injective (classLevelMap (k := k) L L' h) := by
  intro x y hxy
  refine SylowLevel.inflCIn_injective (k := k) (K := K) (Ω := Ω) L.1 L'.1 h ?_
  simpa only [classLevelMap_apply] using hxy

/-- Inflation only depends on the *levels*, not on the proof of the inclusion: any two proofs of
`L ≤ M` are equal by proof irrelevance. -/
theorem classLevelMap_congr {L M : Lvl k K Ω} (h h' : L ≤ M) (u : ClassLevel L) :
    classLevelMap (k := k) L M h u = classLevelMap (k := k) L M h' u :=
  congrArg (fun hh : L ≤ M => classLevelMap (k := k) L M hh u) (Subsingleton.elim h h')

/-! ## The chosen `p`-torsion preimages at the anchor -/

section Chi

/-- **A `p`-torsion class at `L ⊔ L₀` is the inflation of a `p`-torsion class at `L₀`.**  Both
`p`-torsion subgroups are cyclic of order `p` and inflation is injective
(`Work.SSGRoute.LF.classLevelMap_pTorsion_surj`). -/
theorem exists_pre (p : ℕ) [Fact p.Prime] (Lv₀ : Lvl k K Ω)
    (hp₀ : p ∣ Module.finrank k ↥Lv₀.1) (L : Lvl k K Ω) (u : ClassLevel L) (hu : p • u = 0) :
    ∃ w : ClassLevel Lv₀, p • w = 0 ∧
      classLevelMap (k := k) L (lvlSup L Lv₀) (lvlLeSupLeft L Lv₀) u
        = classLevelMap (k := k) Lv₀ (lvlSup L Lv₀) (lvlLeSupRight L Lv₀) w := by
  obtain ⟨w, hw0, hw⟩ := LF.classLevelMap_pTorsion_surj p Lv₀ (lvlSup L Lv₀)
    (lvlLeSupRight L Lv₀) hp₀ (classLevelMap (k := k) L (lvlSup L Lv₀) (lvlLeSupLeft L Lv₀) u)
    (by rw [← map_nsmul, hu, map_zero])
  exact ⟨w, hw0, hw.symm⟩

/-- The chosen `p`-torsion preimage at the anchor level `Lv₀`. -/
noncomputable def pre (p : ℕ) [Fact p.Prime] (Lv₀ : Lvl k K Ω)
    (hp₀ : p ∣ Module.finrank k ↥Lv₀.1) (L : Lvl k K Ω) (u : ClassLevel L)
    (hu : p • u = 0) : ClassLevel Lv₀ :=
  Classical.choose (exists_pre p Lv₀ hp₀ L u hu)

/-- The defining property of the chosen preimage. -/
theorem pre_spec (p : ℕ) [Fact p.Prime] (Lv₀ : Lvl k K Ω)
    (hp₀ : p ∣ Module.finrank k ↥Lv₀.1) (L : Lvl k K Ω) (u : ClassLevel L) (hu : p • u = 0) :
    p • pre p Lv₀ hp₀ L u hu = 0 ∧
      classLevelMap (k := k) L (lvlSup L Lv₀) (lvlLeSupLeft L Lv₀) u
        = classLevelMap (k := k) Lv₀ (lvlSup L Lv₀) (lvlLeSupRight L Lv₀)
            (pre p Lv₀ hp₀ L u hu) :=
  Classical.choose_spec (exists_pre p Lv₀ hp₀ L u hu)

/-- **The chosen preimage is compatible with passing to a bigger level.**  This is transitivity of
inflation, together with the defining property of `pre`. -/
theorem pre_map_le (p : ℕ) [Fact p.Prime] (Lv₀ : Lvl k K Ω)
    (hp₀ : p ∣ Module.finrank k ↥Lv₀.1) (L M : Lvl k K Ω) (hM : lvlSup L Lv₀ ≤ M)
    (u : ClassLevel L) (hu : p • u = 0) :
    classLevelMap (k := k) L M ((lvlLeSupLeft L Lv₀).trans hM) u
      = classLevelMap (k := k) Lv₀ M ((lvlLeSupRight L Lv₀).trans hM)
          (pre p Lv₀ hp₀ L u hu) := by
  rw [← classLevelMap_map (k := k) Lv₀ (lvlSup L Lv₀) M (lvlLeSupRight L Lv₀) hM
      (pre p Lv₀ hp₀ L u hu),
    ← (pre_spec p Lv₀ hp₀ L u hu).2]
  exact (classLevelMap_map (k := k) L (lvlSup L Lv₀) M (lvlLeSupLeft L Lv₀) hM u).symm

/-! ## The coherent family -/

open Classical in
/-- **The coherent family of invariants**: at a level `L`, a `p`-torsion class is sent to the value
of `χ₀` at its chosen preimage at the anchor; non-`p`-torsion classes are sent to `0`. -/
noncomputable def chi (p : ℕ) [Fact p.Prime] (Lv₀ : Lvl k K Ω)
    (hp₀ : p ∣ Module.finrank k ↥Lv₀.1) (P : AddSubgroup (ClassLevel Lv₀))
    (χ₀ : P →+ ZMod p) (hP : ∀ v : ClassLevel Lv₀, v ∈ P ↔ p • v = 0)
    (hχ₀ : Function.Bijective χ₀) (L : Lvl k K Ω) (u : ClassLevel L) : ZMod p :=
  if hu : p • u = 0 then
    χ₀ ⟨pre p Lv₀ hp₀ L u hu, (hP _).mpr (pre_spec p Lv₀ hp₀ L u hu).1⟩
  else 0

theorem chi_apply_of (p : ℕ) [Fact p.Prime] (Lv₀ : Lvl k K Ω)
    (hp₀ : p ∣ Module.finrank k ↥Lv₀.1) (P : AddSubgroup (ClassLevel Lv₀))
    (χ₀ : P →+ ZMod p) (hP : ∀ v : ClassLevel Lv₀, v ∈ P ↔ p • v = 0)
    (hχ₀ : Function.Bijective χ₀) (L : Lvl k K Ω) (u : ClassLevel L) (hu : p • u = 0) :
    chi p Lv₀ hp₀ P χ₀ hP hχ₀ L u
      = χ₀ ⟨pre p Lv₀ hp₀ L u hu, (hP _).mpr (pre_spec p Lv₀ hp₀ L u hu).1⟩ :=
  dif_pos hu

/-- **`chi` is additive on `p`-torsion.** -/
theorem chi_add (p : ℕ) [Fact p.Prime] (Lv₀ : Lvl k K Ω)
    (hp₀ : p ∣ Module.finrank k ↥Lv₀.1) (P : AddSubgroup (ClassLevel Lv₀))
    (χ₀ : P →+ ZMod p) (hP : ∀ v : ClassLevel Lv₀, v ∈ P ↔ p • v = 0)
    (hχ₀ : Function.Bijective χ₀) (L : Lvl k K Ω) (u v : ClassLevel L)
    (hu : p • u = 0) (hv : p • v = 0) :
    chi p Lv₀ hp₀ P χ₀ hP hχ₀ L (u + v)
      = chi p Lv₀ hp₀ P χ₀ hP hχ₀ L u + chi p Lv₀ hp₀ P χ₀ hP hχ₀ L v := by
  have huv : p • (u + v) = 0 := by rw [smul_add, hu, hv, add_zero]
  have hval : (⟨pre p Lv₀ hp₀ L (u + v) huv,
        (hP _).mpr (pre_spec p Lv₀ hp₀ L (u + v) huv).1⟩ : P)
      = ⟨pre p Lv₀ hp₀ L u hu, (hP _).mpr (pre_spec p Lv₀ hp₀ L u hu).1⟩
        + ⟨pre p Lv₀ hp₀ L v hv, (hP _).mpr (pre_spec p Lv₀ hp₀ L v hv).1⟩ := by
    refine Subtype.ext ?_
    show pre p Lv₀ hp₀ L (u + v) huv = pre p Lv₀ hp₀ L u hu + pre p Lv₀ hp₀ L v hv
    have hinj := classLevelMap_injective Lv₀ (lvlSup L Lv₀) (lvlLeSupRight L Lv₀)
    apply hinj
    rw [map_add, ← (pre_spec p Lv₀ hp₀ L (u + v) huv).2, ← (pre_spec p Lv₀ hp₀ L u hu).2,
      ← (pre_spec p Lv₀ hp₀ L v hv).2, map_add]
  rw [chi_apply_of p Lv₀ hp₀ P χ₀ hP hχ₀ L (u + v) huv,
    chi_apply_of p Lv₀ hp₀ P χ₀ hP hχ₀ L u hu,
    chi_apply_of p Lv₀ hp₀ P χ₀ hP hχ₀ L v hv, hval, map_add]

/-- **`chi` is injective on `p`-torsion.** -/
theorem chi_injective (p : ℕ) [Fact p.Prime] (Lv₀ : Lvl k K Ω)
    (hp₀ : p ∣ Module.finrank k ↥Lv₀.1) (P : AddSubgroup (ClassLevel Lv₀))
    (χ₀ : P →+ ZMod p) (hP : ∀ v : ClassLevel Lv₀, v ∈ P ↔ p • v = 0)
    (hχ₀ : Function.Bijective χ₀) (L : Lvl k K Ω) (u : ClassLevel L) (hu : p • u = 0)
    (h0 : chi p Lv₀ hp₀ P χ₀ hP hχ₀ L u = 0) : u = 0 := by
  rw [chi_apply_of p Lv₀ hp₀ P χ₀ hP hχ₀ L u hu] at h0
  have h1 : (⟨pre p Lv₀ hp₀ L u hu, (hP _).mpr (pre_spec p Lv₀ hp₀ L u hu).1⟩ : P) = 0 :=
    hχ₀.1 (h0.trans (map_zero χ₀).symm)
  have h2 : pre p Lv₀ hp₀ L u hu = 0 := congrArg Subtype.val h1
  have h3 : classLevelMap (k := k) L (lvlSup L Lv₀) (lvlLeSupLeft L Lv₀) u = 0 := by
    rw [(pre_spec p Lv₀ hp₀ L u hu).2, h2, map_zero]
  exact classLevelMap_injective L (lvlSup L Lv₀) (lvlLeSupLeft L Lv₀)
    (h3.trans (map_zero (classLevelMap (k := k) L (lvlSup L Lv₀) (lvlLeSupLeft L Lv₀))).symm)

/-- **`chi` is compatible with inflation.** -/
theorem chi_compat (p : ℕ) [Fact p.Prime] (Lv₀ : Lvl k K Ω)
    (hp₀ : p ∣ Module.finrank k ↥Lv₀.1) (P : AddSubgroup (ClassLevel Lv₀))
    (χ₀ : P →+ ZMod p) (hP : ∀ v : ClassLevel Lv₀, v ∈ P ↔ p • v = 0)
    (hχ₀ : Function.Bijective χ₀) (L L' : Lvl k K Ω) (h : L ≤ L') (u : ClassLevel L)
    (hu : p • u = 0) :
    chi p Lv₀ hp₀ P χ₀ hP hχ₀ L' (classLevelMap (k := k) L L' h u)
      = chi p Lv₀ hp₀ P χ₀ hP hχ₀ L u := by
  have hu' : p • classLevelMap (k := k) L L' h u = 0 := by
    rw [← map_nsmul, hu, map_zero]
  have hval : (⟨pre p Lv₀ hp₀ L' (classLevelMap (k := k) L L' h u) hu',
        (hP _).mpr (pre_spec p Lv₀ hp₀ L' (classLevelMap (k := k) L L' h u) hu').1⟩ : P)
      = ⟨pre p Lv₀ hp₀ L u hu, (hP _).mpr (pre_spec p Lv₀ hp₀ L u hu).1⟩ := by
    refine Subtype.ext ?_
    show pre p Lv₀ hp₀ L' (classLevelMap (k := k) L L' h u) hu' = pre p Lv₀ hp₀ L u hu
    have hM : lvlSup L Lv₀ ≤ lvlSup L' Lv₀ := lvlSupLeSup h le_rfl
    have hinj := classLevelMap_injective Lv₀ (lvlSup L' Lv₀) (lvlLeSupRight L' Lv₀)
    apply hinj
    calc classLevelMap (k := k) Lv₀ (lvlSup L' Lv₀) (lvlLeSupRight L' Lv₀)
          (pre p Lv₀ hp₀ L' (classLevelMap (k := k) L L' h u) hu')
        = classLevelMap (k := k) L' (lvlSup L' Lv₀) (lvlLeSupLeft L' Lv₀)
            (classLevelMap (k := k) L L' h u) :=
          (pre_spec p Lv₀ hp₀ L' (classLevelMap (k := k) L L' h u) hu').2.symm
      _ = classLevelMap (k := k) L (lvlSup L' Lv₀) (h.trans (lvlLeSupLeft L' Lv₀)) u :=
          classLevelMap_map (k := k) L L' (lvlSup L' Lv₀) h (lvlLeSupLeft L' Lv₀) u
      _ = classLevelMap (k := k) L (lvlSup L' Lv₀) ((lvlLeSupLeft L Lv₀).trans hM) u :=
          classLevelMap_congr (h.trans (lvlLeSupLeft L' Lv₀)) ((lvlLeSupLeft L Lv₀).trans hM) u
      _ = classLevelMap (k := k) Lv₀ (lvlSup L' Lv₀) ((lvlLeSupRight L Lv₀).trans hM)
            (pre p Lv₀ hp₀ L u hu) :=
          pre_map_le p Lv₀ hp₀ L (lvlSup L' Lv₀) hM u hu
      _ = classLevelMap (k := k) Lv₀ (lvlSup L' Lv₀) (lvlLeSupRight L' Lv₀)
            (pre p Lv₀ hp₀ L u hu) :=
          classLevelMap_congr ((lvlLeSupRight L Lv₀).trans hM) (lvlLeSupRight L' Lv₀)
            (pre p Lv₀ hp₀ L u hu)
  rw [chi_apply_of p Lv₀ hp₀ P χ₀ hP hχ₀ L' (classLevelMap (k := k) L L' h u) hu',
    chi_apply_of p Lv₀ hp₀ P χ₀ hP hχ₀ L u hu, hval]

end Chi

end Coherent

/-- **The coherent `p`-torsion invariant.**  For a finite Galois extension `k ⊆ K` of number
fields, an algebraically closed `Ω ⊇ K` and a prime `p`, there is a family of functions
`χ L : H²(Gal(L/k), C_L) → ZMod p`, one for each finite Galois level `K ≤ L ≤ Ω`, which on the
`p`-torsion is additive, injective, and compatible with inflation. -/
theorem coherent_pTorsion_chi (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω] :
    ∃ χ : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2 → ZMod p,
      (∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
          p • u = 0 → p • v = 0 → χ L (u + v) = χ L u + χ L v) ∧
      (∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
          p • u = 0 → χ L u = 0 → u = 0) ∧
      (∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
          (hLL : L ≤ L') (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
          p • u = 0 → χ L' (SSGRoute.PTExt.inflCIn (k := k) hLL u) = χ L u) := by
  -- the anchor level `L₀` with `p ∣ [L₀ : k]`
  obtain ⟨L₀, hNF₀, hFD₀, hGal₀, hp₀⟩ := exists_level_p_dvd p k K Ω
  let Lv₀ : Lvl k K Ω := ⟨L₀, hNF₀, hFD₀, hGal₀⟩
  -- the additive bijection `χ₀` on the `p`-torsion at `L₀`
  obtain ⟨P, χ₀, hP, hχ₀⟩ := pt_char_pTorsion p k K (↥Lv₀.1) hp₀
  refine ⟨fun L i1 i2 i3 u => Coherent.chi p Lv₀ hp₀ P χ₀ hP hχ₀ ⟨L, i1, i2, i3⟩ u, ?_, ?_, ?_⟩
  · intro L i1 i2 i3 u v hu hv
    exact Coherent.chi_add p Lv₀ hp₀ P χ₀ hP hχ₀ ⟨L, i1, i2, i3⟩ u v hu hv
  · intro L i1 i2 i3 u hu h0
    exact Coherent.chi_injective p Lv₀ hp₀ P χ₀ hP hχ₀ ⟨L, i1, i2, i3⟩ u hu h0
  · intro L i1 i2 i3 L' i1' i2' i3' hLL u hu
    exact Coherent.chi_compat p Lv₀ hp₀ P χ₀ hP hχ₀ ⟨L, i1, i2, i3⟩ ⟨L', i1', i2', i3'⟩ hLL u hu

end Work.SSGRoute.PT
