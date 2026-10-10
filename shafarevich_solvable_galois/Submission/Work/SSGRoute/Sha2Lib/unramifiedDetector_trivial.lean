import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.Sha2Lib.coeffSES_extClass_generator
import Submission.Work.SSGRoute.Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg
import Submission.Work.SSGRoute.Sha2Lib.extH_class_of_character
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-! ## The algebraic core: the Yoneda pairing with the coefficient sequence `0 → ℤ → ℤ → 𝔽_p → 0`

The base case of the unramified detector is reduced to two facts about the coefficient sequence
`SSGRoute.Phi1.coeffSES H p` of a finite group `H`:

* the class `h ∈ H¹(H, 𝔽_p)` of a non-zero character has non-zero Bockstein
  `h ∘ extClass ∈ H²(H, ℤ)` (`coeffSES_comp_extClass_ne_zero`, from the injectivity of the
  connecting map `H¹(H, 𝔽_p) → H²(H, ℤ)` and `H¹(H, ℤ) = 0`); and
* the tautological class generates `Ext¹_H(𝔽_p, ℤ) ≅ ℤ/p`, so a non-zero `φ` in that group is a
  natural multiple `n • extClass` of it with `p ∤ n` — the gap recorded in the docstring of
  `Work.SSGRoute.Sha2Lib.coeffSES_extClass_generator`.

All the scalar reasoning below is in terms of *natural-number* multiples (`nsmul`), which are
canonical, so that no instance ambiguity between the `Coeff = ULift ℤ`-scalar structure and the
`ℤ`-scalar structure can arise. -/

/-- `(n : Coeff) • x = n • x`: a scalar multiple by a natural number in the coefficient ring
`Coeff = ULift ℤ` is the iterated sum. -/
theorem coeff_natCast_smul {M : Type*} [AddCommMonoid M] [Module SSGRoute.PTExt.Coeff M] (n : ℕ)
    (x : M) : (n : SSGRoute.PTExt.Coeff) • x = n • x := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, zero_nsmul]
  | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, succ_nsmul, ih]

/-- `Ext`-composition is `ℕ`-linear in its second argument. -/
theorem ext_comp_nsmul_right {C : Type*} [Category C] [Abelian C] [HasExt C] {X Y Z : C}
    {a b : ℕ} (α : Abelian.Ext X Y a) (n : ℕ) (β : Abelian.Ext Y Z b) {c : ℕ}
    (h : a + b = c) : α.comp (n • β) h = n • α.comp β h := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, Abelian.Ext.comp_zero]
  | succ k ih => rw [succ_nsmul, Abelian.Ext.comp_add, ih, succ_nsmul]

/-- `mk₀` is `ℕ`-linear. -/
theorem mk₀_nsmul {C : Type*} [Category C] [Abelian C] [HasExt C] {X Y : C} (n : ℕ)
    (f : X ⟶ Y) : Abelian.Ext.mk₀ (n • f) = n • Abelian.Ext.mk₀ f := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, Abelian.Ext.mk₀_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, Abelian.Ext.mk₀_add, ih]

/-- **`ℕ`-form of `Abelian.Ext.smul_eq_comp_mk₀`**: `n • y = y ∘ mk₀ (n • 𝟙 Y)`. -/
theorem ext_nsmul_eq_comp_mk₀ {C : Type*} [Category C] [Abelian C] [HasExt C] {X Y : C} {a : ℕ}
    (y : Abelian.Ext X Y a) (n : ℕ) :
    n • y = y.comp (Abelian.Ext.mk₀ (n • 𝟙 Y)) (add_zero a) := by
  rw [mk₀_nsmul, ext_comp_nsmul_right, Abelian.Ext.comp_mk₀_id]

/-- **The class of the coefficient sequence is `p`-torsion.**

`p • extClass = extClass ∘ mk₀ (p • 𝟙 ℤ)`, and `p • 𝟙 ℤ` is the first map of the sequence
(`Work.SSGRoute.extFp_unitMulByP_eq_smul`), so the composite is zero by
`ShortComplex.ShortExact.extClass_comp`. -/
theorem coeffSES_nsmul_extClass_eq_zero (p : ℕ) [Fact p.Prime] (H : Type) [Group H] :
    p • (SSGRoute.Phi1.coeffSES_shortExact H p).extClass = 0 := by
  have hf : p • 𝟙 (SSGRoute.Phi1.coeffSES H p).X₁ = (SSGRoute.Phi1.coeffSES H p).f := by
    rw [← coeff_natCast_smul p (𝟙 (SSGRoute.Phi1.coeffSES H p).X₁)]
    exact (Work.SSGRoute.extFp_unitMulByP_eq_smul p H).symm
  rw [ext_nsmul_eq_comp_mk₀ (SSGRoute.Phi1.coeffSES_shortExact H p).extClass p, hf]
  exact ShortComplex.ShortExact.extClass_comp (SSGRoute.Phi1.coeffSES_shortExact H p)

/-- **Non-vanishing of the Bockstein of a non-zero class.**  For a finite group `H`, the composition
of `0 ≠ h ∈ H¹(H, 𝔽_p)` with the class of `0 → ℤ --p--> ℤ → 𝔽_p → 0` is non-zero: the connecting
map `H¹(H, 𝔽_p) → H²(H, ℤ)` is injective because `H¹(H, ℤ) = 0`
(`Work.SSGRoute.E7cOmega.extH_unitRep_one_subsingleton`). -/
theorem coeffSES_comp_extClass_ne_zero {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Fintype H]
    (h : SSGRoute.PTExt.extH (Rep.trivial SSGRoute.PTExt.Coeff H (ZMod p)) 1) (hh : h ≠ 0) :
    h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass (by norm_num : (1 : ℕ) + 1 = 2)
      ≠ 0 := by
  intro h0
  haveI : Subsingleton (Abelian.Ext (SSGRoute.PTExt.unitRep H)
      ((SSGRoute.Phi1.coeffSES H p).X₂) 1) :=
    Work.SSGRoute.E7cOmega.extH_unitRep_one_subsingleton H
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ (SSGRoute.PTExt.unitRep H)
    (SSGRoute.Phi1.coeffSES_shortExact H p) h (n₁ := 2) (by norm_num : (1 : ℕ) + 1 = 2) h0
  have hx₂0 : x₂ = 0 := Subsingleton.elim x₂ 0
  have hzero : h = 0 := by
    rw [← hx₂, hx₂0]
    exact Abelian.Ext.zero_comp (SSGRoute.PTExt.unitRep H) 1
      (Abelian.Ext.mk₀ (SSGRoute.Phi1.coeffSES H p).g) 1 (by norm_num : (1 : ℕ) + 0 = 1)
  exact hh hzero

/-- **The Bockstein of any class is `p`-torsion**: `p • (h ∘ extClass) = h ∘ (p • extClass) = 0`
by `coeffSES_nsmul_extClass_eq_zero`. -/
theorem comp_extClass_nsmul_eq_zero (p : ℕ) [Fact p.Prime] (H : Type) [Group H]
    (h : SSGRoute.PTExt.extH (Rep.trivial Coeff H (ZMod p)) 1) :
    p • (h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass rfl) = 0 := by
  have hf : p • 𝟙 (SSGRoute.Phi1.coeffSES H p).X₁ = (SSGRoute.Phi1.coeffSES H p).f := by
    rw [← coeff_natCast_smul p (𝟙 (SSGRoute.Phi1.coeffSES H p).X₁)]
    exact (Work.SSGRoute.extFp_unitMulByP_eq_smul p H).symm
  have hinner : (SSGRoute.Phi1.coeffSES_shortExact H p).extClass.comp
      (Abelian.Ext.mk₀ (p • 𝟙 (SSGRoute.Phi1.coeffSES H p).X₁)) (add_zero 1) = 0 := by
    rw [hf]
    exact ShortComplex.ShortExact.extClass_comp (SSGRoute.Phi1.coeffSES_shortExact H p)
  calc p • (h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass rfl)
      = (h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass rfl).comp
          (Abelian.Ext.mk₀ (p • 𝟙 (SSGRoute.Phi1.coeffSES H p).X₁)) (add_zero 2) :=
        ext_nsmul_eq_comp_mk₀ _ p
    _ = h.comp ((SSGRoute.Phi1.coeffSES_shortExact H p).extClass.comp
          (Abelian.Ext.mk₀ (p • 𝟙 (SSGRoute.Phi1.coeffSES H p).X₁)) (add_zero 1)) rfl :=
        Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ rfl
    _ = h.comp 0 rfl := by rw [hinner]
    _ = 0 := Abelian.Ext.comp_zero _ _ _ _ _

/-- The level pairing is additive in the `Ext`-variable. -/
theorem levelPair_add_x {G H : Type} [Group G] [Group H] (f : H →* G) {M A : Rep.{0} Coeff G}
    {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {r s : ℕ} (x x' : Abelian.Ext M A r)
    (h : SSGRoute.PTExt.extH (Rep.res f M) s) :
    SSGRoute.PTExt.levelPair f ι (x + x') h
      = SSGRoute.PTExt.levelPair f ι x h + SSGRoute.PTExt.levelPair f ι x' h := by
  show h.comp ((Abelian.Ext.mapExactFunctor (Rep.resFunctor f) (x + x')).comp
      (Abelian.Ext.mk₀ ι) (add_zero r)) rfl
    = h.comp ((Abelian.Ext.mapExactFunctor (Rep.resFunctor f) x).comp
        (Abelian.Ext.mk₀ ι) (add_zero r)) rfl
      + h.comp ((Abelian.Ext.mapExactFunctor (Rep.resFunctor f) x').comp
        (Abelian.Ext.mk₀ ι) (add_zero r)) rfl
  rw [Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add]

/-- The level pairing is `ℕ`-linear in the `Ext`-variable. -/
theorem levelPair_nsmul_x {G H : Type} [Group G] [Group H] (f : H →* G) {M A : Rep.{0} Coeff G}
    {B : Rep.{0} Coeff H} (ι : Rep.res f A ⟶ B) {r s : ℕ} (n : ℕ) (x : Abelian.Ext M A r)
    (h : SSGRoute.PTExt.extH (Rep.res f M) s) :
    SSGRoute.PTExt.levelPair f ι (n • x) h = n • SSGRoute.PTExt.levelPair f ι x h := by
  induction n with
  | zero =>
      rw [zero_nsmul, zero_nsmul]
      show h.comp ((Abelian.Ext.mapExactFunctor (Rep.resFunctor f) 0).comp
          (Abelian.Ext.mk₀ ι) (add_zero r)) rfl = 0
      rw [Abelian.Ext.mapExactFunctor_zero, Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]
  | succ k ih => rw [succ_nsmul, levelPair_add_x, ih, succ_nsmul]

/-- **The level pairing with a non-zero `ℤ`-coefficient class is non-degenerate.**

For groups `H →f→ G` with `G`, `H` finite and a prime `p`: the level pairing of a non-zero
`φ ∈ Ext¹_G(𝔽_p, ℤ)` with a non-zero class `h ∈ H¹(H, res 𝔽_p)` is non-zero in `H²(H, ℤ)`.

By `coeffSES_extClass_generator`, `φ = n • extClass_G` with `p ∤ n`; the pairing is `ℕ`-linear in
`φ`, so it suffices to treat the tautological case `φ = extClass_G`.  There the pairing is
`h ∘ extClass_H` (`Abelian.Ext.mapExactFunctor_extClass` computes the restriction of the tautological
class, and `trivResInv f Coeff` is the identity), which is non-zero of order `p` by
`coeffSES_comp_extClass_ne_zero` and `comp_extClass_nsmul_eq_zero`.  Hence `n • (h ∘ extClass_H) ≠ 0`
because `p ∤ n`. -/
theorem levelPair_trivResInv_ne_zero {p : ℕ} [Fact p.Prime] {G H : Type} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : H →* G)
    (φ : Abelian.Ext (Rep.trivial Coeff G (ZMod p)) (unitRep G) 1) (hφ : φ ≠ 0)
    (h : extH (Rep.res f (Rep.trivial Coeff G (ZMod p))) 1) (hh : h ≠ 0) :
    levelPair f (trivResInv f Coeff) φ h ≠ 0 := by
  obtain ⟨n, hnp, hn⟩ :=
    coeffSES_extClass_generator (G := G) φ hφ
  have hn' : φ = n • (SSGRoute.Phi1.coeffSES_shortExact G p).extClass := by
    rw [hn, coeff_natCast_smul]
  have hkey : levelPair f (trivResInv f Coeff) φ h
      = n • levelPair f (trivResInv f Coeff) (SSGRoute.Phi1.coeffSES_shortExact G p).extClass h := by
    rw [hn', levelPair_nsmul_x]
  set z := levelPair f (trivResInv f Coeff) (SSGRoute.Phi1.coeffSES_shortExact G p).extClass h
    with hz
  have hz_eq : z = h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass
      (by norm_num : (1 : ℕ) + 1 = 2) := by
    have hext : extRes f (SSGRoute.Phi1.coeffSES_shortExact G p).extClass
        = (SSGRoute.Phi1.coeffSES_shortExact H p).extClass :=
      Abelian.Ext.mapExactFunctor_extClass (Rep.resFunctor f) (SSGRoute.Phi1.coeffSES_shortExact G p)
    have hι : trivResInv f Coeff = 𝟙 (unitRep H) := rfl
    have hinner : (SSGRoute.Phi1.coeffSES_shortExact H p).extClass.comp
        (Abelian.Ext.mk₀ (trivResInv f Coeff)) (add_zero 1)
        = (SSGRoute.Phi1.coeffSES_shortExact H p).extClass := by
      rw [hι]
      exact Abelian.Ext.comp_mk₀_id _
    calc z = h.comp ((extRes f (SSGRoute.Phi1.coeffSES_shortExact G p).extClass).comp
            (Abelian.Ext.mk₀ (trivResInv f Coeff)) (add_zero 1)) rfl := rfl
      _ = h.comp (((SSGRoute.Phi1.coeffSES_shortExact H p).extClass).comp
            (Abelian.Ext.mk₀ (trivResInv f Coeff)) (add_zero 1)) rfl := by rw [hext]
      _ = h.comp ((SSGRoute.Phi1.coeffSES_shortExact H p).extClass) rfl := by rw [hinner]
      _ = h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass
            (by norm_num : (1 : ℕ) + 1 = 2) := rfl
  have hz0 : z ≠ 0 := by
    rw [hz_eq]
    exact coeffSES_comp_extClass_ne_zero (p := p) h hh
  have hzord : addOrderOf z = p := by
    have hpz : p • z = 0 := by
      rw [hz_eq]
      exact comp_extClass_nsmul_eq_zero p H h
    have h1 : addOrderOf z ∣ p := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hpz
    have h2 : addOrderOf z ≠ 1 := fun h1' => hz0 (AddMonoid.addOrderOf_eq_one_iff.mp h1')
    exact ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ h1).resolve_left h2
  rw [hkey]
  intro h0
  exact hnp (by rw [← hzord]; exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0)

/-! ## The main theorem -/

/-- **Base case `M = F_p` (trivial action) of the global unramified detector.**  This is the
statement of `Work.SSGRoute.E7cOmega.unramifiedDetector_trivial` with its second conjunct *weakened*
from `e(q'/q) = 1` to `Nat.Coprime e p` (the form consumed downstream, and implied by `e = 1`);
the other clauses coincide.  Restated here in `Sha2Lib` because the missing ingredient lives here.

Ingredients (all on disk):
* the level with `e(q'/q) = 1` and `p ∣ f(q'/q)`, together with a character `χ : Gal(L/k) → ℤ/p`
  killing the inertia of `q'` and nontrivial on `D_{q'}`: **proved, axiom-clean**, as
  `Work.SSGRoute.Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg`;
* the class of a nonzero additive character is nonzero in `H¹`: **proved**, as
  `Work.SSGRoute.Sha2Lib.H1pi_character_ne_zero` (bridge to `extH`:
  `Work.SSGRoute.extH_groupCohomology_iso`); a class killing the inertia group is
  `IsUnramifiedClassAt` by definition (`SSGRoute.PTExt.IsUnramifiedClassAt`);
* `Ext¹_{D}(F_p, ℤ) ≅ ℤ/p` generated by the tautological class of `0 → ℤ →^p ℤ → F_p → 0`:
  `Work.SSGRoute.ext_zmod_prime_iso_corrected` (proved), or in the `Phi1.coeffSES` vocabulary
  `Work.SSGRoute.E7cC.exists_nat_smul_coeffSES_extClass` — so a nonzero `φ` is `n • extClass` with
  `p ∤ n`;
* the pairing of a nonzero `ℤ/p`-class with a nonzero `H¹(D, F_p)`-class is nonzero:
  **proved**, `Work.SSGRoute.E7cOmega.comp_intSES_extClass_ne_zero` together with
  `Work.SSGRoute.E7cOmega.extH_unitRep_one_subsingleton`.

(Only the tautological case of the third point is covered on disk; the prover must transfer it to an
arbitrary nonzero `φ`.  `hpq` is not needed by these ingredients but is kept to match the original
statement.) -/
theorem unramifiedDetector_trivial (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
        (Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p)))
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1)
    (hφ : φ ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L)
        (Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p))) 1),
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p ∧
      SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv
          (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff)
        φ
        (SSGRoute.PTExt.extHRestrict
          (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0 := by
  classical
  -- the level, the prime `q' | q` (`e(q'|q) = 1`, `p ∣ f(q'|q)`) and the residue character `χ`
  obtain ⟨L, hnfL, hfdL, hgalL, q', hq'lies, he, _hf, χ, hχinertia, hχne⟩ :=
    exists_unramified_character_with_p_dvd_residueDeg p k K Ω q
  letI : NumberField ↥L := hnfL
  letI : FiniteDimensional k ↥L := hfdL
  letI : IsGalois k ↥L := hgalL
  haveI hq'liesI : q'.asIdeal.LiesOver q.asIdeal := hq'lies
  haveI hfdKL : FiniteDimensional K ↥L := FiniteDimensional.right k K ↥L
  -- the place of `q'` lies over `w`
  have hq'w : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w := by
    rw [hwq]
    exact NK.GlobalCFT.Place.liesOver_ofFinite hq'lies
  -- the additive character `f` attached to `χ`
  let f : Additive (↥L ≃ₐ[k] ↥L) →+ ZMod p :=
    { toFun := fun a => Multiplicative.toAdd (χ (Additive.toMul a))
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hfker : ∀ σ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' σ →
      f (Additive.ofMul σ) = 0 := by
    intro σ hσ
    show Multiplicative.toAdd (χ (Additive.toMul (Additive.ofMul σ))) = 0
    rw [toMul_ofMul, hχinertia σ hσ]
    rfl
  have hfne : ∃ σ : ↥L ≃ₐ[k] ↥L,
      σ ∈ SSGRoute.PTExt.decompK (NK.GlobalCFT.Place.ofFinite q') ∧
        f (Additive.ofMul σ) ≠ 0 := by
    obtain ⟨σ, hσmem, hσχ⟩ := hχne
    refine ⟨σ, hσmem, ?_⟩
    show Multiplicative.toAdd (χ (Additive.toMul (Additive.ofMul σ))) ≠ 0
    rw [toMul_ofMul]
    intro h0
    exact hσχ ((Multiplicative.toAdd).injective (by rw [h0]; rfl))
  -- the detecting class, unramified at `q'` and non-zero on `D_{q'}`
  obtain ⟨h, hunram, hne⟩ : ∃ h : SSGRoute.PTExt.extH
      (Rep.res (SSGRoute.PTExt.galRes k K ↥L)
        (Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p))) 1,
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      SSGRoute.PTExt.extHRestrict
        (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h ≠ 0 :=
    extH_class_of_character (k := k) (K := K) (L := ↥L) p q' f hfker hfne
  -- `e(q'|q) = 1` makes the ramification index prime to `p`
  have hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx q.asIdeal q'.asIdeal q.ne_bot, he]
    exact Nat.coprime_one_left p
  refine ⟨L, hnfL, hfdL, hgalL, q', hq'w, h, hunram, hcop, ?_⟩
  -- the level pairing is non-zero
  haveI : Fintype (↥L ≃ₐ[k] ↥L) := Fintype.ofFinite _
  haveI : Fintype (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite q')) := Fintype.ofFinite _
  haveI : Fintype (SSGRoute.PTExt.decompK (k := k) (K := K) w) := Fintype.ofFinite _
  exact levelPair_trivResInv_ne_zero (p := p)
    (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq'w) φ hφ
    (SSGRoute.PTExt.extHRestrict
      (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) hne

end Work.SSGRoute.Sha2Lib
