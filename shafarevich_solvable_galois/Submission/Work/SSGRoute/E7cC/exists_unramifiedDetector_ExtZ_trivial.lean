import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.e7comega_defs
import Submission.Work.SSGRoute.local_duality_ext
import Submission.Work.SSGRoute.E7cC.exists_level_unramified_p_dvd_inertiaDeg
import Submission.Work.SSGRoute.E7cOmega.extH_unitRep_one_subsingleton
import Submission.Work.SSGRoute.nonempty_extGroupCohomologyBridge
import Submission.Work.SSGRoute.exists_H1_inflated_ne_zero
import Submission.Work.SSGRoute.E7cC.exists_nat_smul_coeffSES_extClass
import Submission.Work.SSGRoute.E7cC.coeffSES_nsmul_extClass
import Submission.Work.SSGRoute.Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg
import Submission.Work.SSGRoute.Sha2Lib.extH_class_of_character
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7cC

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 4000000

/-! ## Algebraic core: the Bockstein pairing against a nonzero class in `Ext¹(𝔽_p, ℤ)`

For a finite group `H`, the coefficient sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0`
(`Work.SSGRoute.Phi1.coeffSES` with `coeffSES_shortExact`) generates `Ext¹_H(𝔽_p, ℤ) ≅ ℤ/p`, and
the Yoneda pairing
`Ext¹_H(𝔽_p, ℤ) × H¹(H, 𝔽_p) → H²(H, ℤ)`,
`(φ, h) ↦ h ∘ φ`, is non-degenerate: both `φ ≠ 0` and `h ≠ 0` are needed for a nonzero value.

The proofs here use only the long exact sequences of `Abelian.Ext` and the vanishing
`H¹(H, ℤ) = 0` (`Work.SSGRoute.E7cOmega.extH_unitRep_one_subsingleton`); no `ℚ/ℤ`-coefficient
sequence is required (cf. the docstring of the target: "provable from `SSGRoute.Phi1.coeffSES`").
-/

/-! ### General form of the Bockstein injectivity, and the Yoneda pairing -/

/-- `ℕ`-linearity of `Ext.comp` in its second argument. -/
theorem comp_nsmul_right {C : Type*} [Category C] [Abelian C] [HasExt C] {X Y Z : C}
    {a b : ℕ} (α : Abelian.Ext X Y a) (n : ℕ) (β : Abelian.Ext Y Z b) {c : ℕ}
    (h : a + b = c) : α.comp (n • β) h = n • α.comp β h := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, Abelian.Ext.comp_zero]
  | succ k ih =>
      rw [succ_nsmul, Abelian.Ext.comp_add, ih, succ_nsmul]

/-- The `ℕ`-multiples of `Coeff` act as the natural number multiples. -/
theorem natCast_smul_coeff {M : Type*} [AddCommMonoid M] [Module Coeff M] (n : ℕ) (x : M) :
    (n : Coeff) • x = n • x := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, zero_nsmul]
  | succ k ih =>
      rw [Nat.cast_succ, add_smul, one_smul, succ_nsmul, ih]

/-- **Bockstein injectivity, general form.**  For a short exact sequence `S : 0 → A → B → C → 0`
of `Coeff`-representations of a finite group `H` whose middle term has `Ext¹_H(ℤ, B) = 0`, and for a
nonzero class `h ∈ H¹(H, C)`, the Yoneda composite of `h` with the class of `S` is nonzero. -/
theorem bockstein_ne_zero_of_subsingleton (p : ℕ) [Fact p.Prime] {H : Type} [Group H] [Fintype H]
    (S : ShortComplex (Rep Coeff H)) (hS : S.ShortExact)
    (h : extH S.X₃ 1) (hh : h ≠ 0)
    (hsub : Subsingleton (Abelian.Ext (unitRep H) S.X₂ 1)) :
    h.comp hS.extClass (by norm_num : (1 : ℕ) + 1 = 2) ≠ 0 := by
  intro h0
  haveI : Subsingleton (Abelian.Ext (unitRep H) S.X₂ 1) := hsub
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ (unitRep H) hS h (n₁ := 2)
    (by norm_num : (1 : ℕ) + 1 = 2) h0
  have hx₂0 : x₂ = 0 := Subsingleton.elim x₂ 0
  have hzero : h = 0 := by
    rw [← hx₂, hx₂0]
    exact Abelian.Ext.zero_comp (unitRep H) 1 (Abelian.Ext.mk₀ S.g) 1
      (by norm_num : (1 : ℕ) + 0 = 1)
  exact hh hzero

/-- **The Yoneda pairing with a nonzero class in `Ext¹_H(𝔽_p, ℤ)` is non-degenerate.**
If `φ = n • e.extClass` with `p ∤ n` for the coefficient sequence `e = 0 → ℤ →^p ℤ → 𝔽_p → 0`, and
if the Bockstein `h ∘ e.extClass` of a nonzero `h ∈ H¹(H, 𝔽_p)` is `p`-torsion, then `h ∘ φ ≠ 0`:
`h ∘ e.extClass` is nonzero of order `p`, and `n` is invertible mod `p`. -/
theorem ext_comp_ne_zero_of_ne_zero {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Fintype H]
    (h : extH (Rep.trivial Coeff H (ZMod p)) 1) (hh : h ≠ 0)
    (φ : Abelian.Ext (Rep.trivial Coeff H (ZMod p)) (unitRep H) 1) (hφ : φ ≠ 0)
    (hfac : ∃ n : ℕ, ¬ p ∣ n ∧
      φ = (n : Coeff) • (SSGRoute.Phi1.coeffSES_shortExact H p).extClass)
    (hpδ : p • (h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass
      (by norm_num : (1 : ℕ) + 1 = 2)) = 0) :
    h.comp φ (by norm_num : (1 : ℕ) + 1 = 2) ≠ 0 := by
  obtain ⟨n, hnp, hn⟩ := hfac
  set e := SSGRoute.Phi1.coeffSES_shortExact H p with he
  have hsub : Subsingleton (Abelian.Ext (SSGRoute.PTExt.unitRep H)
      ((SSGRoute.Phi1.coeffSES H p).X₂) 1) :=
    Work.SSGRoute.E7cOmega.extH_unitRep_one_subsingleton H
  have hδ : h.comp e.extClass (by norm_num : (1 : ℕ) + 1 = 2) ≠ 0 :=
    bockstein_ne_zero_of_subsingleton p (SSGRoute.Phi1.coeffSES H p)
      (SSGRoute.Phi1.coeffSES_shortExact H p) h hh hsub
  have hord : addOrderOf (h.comp e.extClass (by norm_num : (1 : ℕ) + 1 = 2)) = p := by
    have h1 : addOrderOf (h.comp e.extClass (by norm_num : (1 : ℕ) + 1 = 2)) ∣ p :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hpδ
    have h2 : addOrderOf (h.comp e.extClass (by norm_num : (1 : ℕ) + 1 = 2)) ≠ 1 := fun h1' =>
      hδ (AddMonoid.addOrderOf_eq_one_iff.mp h1')
    exact ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ h1).resolve_left h2
  have heq : h.comp ((n : Coeff) • e.extClass) (by norm_num : (1 : ℕ) + 1 = 2)
      = n • (h.comp e.extClass (by norm_num : (1 : ℕ) + 1 = 2)) := by
    rw [natCast_smul_coeff]
    exact comp_nsmul_right h n e.extClass (by norm_num : (1 : ℕ) + 1 = 2)
  have key : h.comp φ (by norm_num : (1 : ℕ) + 1 = 2)
      = n • (h.comp e.extClass (by norm_num : (1 : ℕ) + 1 = 2)) := by
    rw [hn]
    exact heq
  intro h0
  have h0' : n • (h.comp e.extClass (by norm_num : (1 : ℕ) + 1 = 2)) = 0 := by
    rw [← key]
    exact h0
  have hp_dvd : p ∣ n := by
    rw [← hord]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0'
  exact hnp hp_dvd

/-- `extRes` commutes with `ℕ`-multiples. -/
theorem resFunctor_nsmul {G H : Type} [Group G] [Group H] (f : H →* G)
    {X Y : Rep Coeff G} {r : ℕ} (n : ℕ) (x : Abelian.Ext X Y r) :
    (n • x).mapExactFunctor (Rep.resFunctor f)
      = n • x.mapExactFunctor (Rep.resFunctor f) := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, Abelian.Ext.mapExactFunctor_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, Abelian.Ext.mapExactFunctor_add, ih]

/-- `extRes` commutes with `ℕ`-multiples. -/
theorem extRes_nsmul {G H : Type} [Group G] [Group H] (f : H →* G) {X Y : Rep Coeff G} {r : ℕ}
    (n : ℕ) (x : Abelian.Ext X Y r) :
    SSGRoute.PTExt.extRes f (n • x) = n • SSGRoute.PTExt.extRes f x := by
  show (n • x).mapExactFunctor (Rep.resFunctor f)
    = n • x.mapExactFunctor (Rep.resFunctor f)
  exact resFunctor_nsmul f n x

/-- **The level pairing against a nonzero `ℤ`-coefficient class is non-degenerate.**  For finite
groups `H ≤ G` (via `f : H →* G`) and nonzero `φ ∈ Ext¹_G(𝔽_p, ℤ)`, `h ∈ H¹(H, 𝔽_p)`, the level
pairing `levelPair f (trivResInv f Coeff) φ h` is nonzero. -/
theorem levelPair_trivResInv_ne_zero {p : ℕ} [Fact p.Prime] {G H : Type} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : H →* G)
    (φ : Abelian.Ext (Rep.trivial Coeff G (ZMod p)) (unitRep G) 1) (hφ : φ ≠ 0)
    (h : extH (Rep.res f (Rep.trivial Coeff G (ZMod p))) 1) (hh : h ≠ 0) :
    SSGRoute.PTExt.levelPair f (SSGRoute.PTExt.trivResInv f Coeff) φ h ≠ 0 := by
  obtain ⟨n, hnp, hn⟩ :=
    exists_nat_smul_coeffSES_extClass (G := G) φ hφ
  -- the two degree proofs, as single syntactic terms
  let hdeg : (1 : ℕ) + 1 = 2 := by norm_num
  let hdeg1 : (1 : ℕ) + 0 = 1 := add_zero 1
  have hext : SSGRoute.PTExt.extRes f (SSGRoute.Phi1.coeffSES_shortExact G p).extClass
      = (SSGRoute.Phi1.coeffSES_shortExact H p).extClass :=
    Abelian.Ext.mapExactFunctor_extClass (Rep.resFunctor f)
      (SSGRoute.Phi1.coeffSES_shortExact G p)
  -- the coefficient morphism is the identity, so its `mk₀` is absorbed
  have hstep : ∀ (x : Abelian.Ext (Rep.trivial Coeff H (ZMod p)) (unitRep H) 1),
      x.comp (Abelian.Ext.mk₀ (SSGRoute.PTExt.trivResInv f Coeff)) hdeg1 = x := by
    intro x
    have hid : SSGRoute.PTExt.trivResInv f Coeff = 𝟙 (SSGRoute.PTExt.unitRep H) := rfl
    rw [hid]
    exact Abelian.Ext.comp_mk₀_id x
  have hcomp : SSGRoute.PTExt.extRes f φ
      = n • (SSGRoute.Phi1.coeffSES_shortExact H p).extClass := by
    have key1 : SSGRoute.PTExt.extRes f (n • (SSGRoute.Phi1.coeffSES_shortExact G p).extClass)
        = n • SSGRoute.PTExt.extRes f (SSGRoute.Phi1.coeffSES_shortExact G p).extClass :=
      extRes_nsmul f n ((SSGRoute.Phi1.coeffSES_shortExact G p).extClass)
    rw [hn, natCast_smul_coeff]
    exact key1.trans (congrArg (fun z => n • z) hext)
  have hkey : SSGRoute.PTExt.levelPair f (SSGRoute.PTExt.trivResInv f Coeff) φ h
      = n • (h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass hdeg) := by
    rw [SSGRoute.PTExt.levelPair, hcomp]
    have h4 : h.comp ((n • (SSGRoute.Phi1.coeffSES_shortExact H p).extClass).comp
        (Abelian.Ext.mk₀ (SSGRoute.PTExt.trivResInv f Coeff)) (add_zero 1)) hdeg
        = n • (h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass hdeg) := by
      rw [show (n • (SSGRoute.Phi1.coeffSES_shortExact H p).extClass).comp
          (Abelian.Ext.mk₀ (SSGRoute.PTExt.trivResInv f Coeff)) (add_zero 1)
          = n • (SSGRoute.Phi1.coeffSES_shortExact H p).extClass from
        hstep (n • (SSGRoute.Phi1.coeffSES_shortExact H p).extClass)]
      exact comp_nsmul_right h n (SSGRoute.Phi1.coeffSES_shortExact H p).extClass hdeg
    exact h4
  rw [hkey]
  intro h0
  have hδ : h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass hdeg ≠ 0 := by
    have hsub : Subsingleton (Abelian.Ext (SSGRoute.PTExt.unitRep H)
        ((SSGRoute.Phi1.coeffSES H p).X₂) 1) :=
      Work.SSGRoute.E7cOmega.extH_unitRep_one_subsingleton H
    exact bockstein_ne_zero_of_subsingleton p (SSGRoute.Phi1.coeffSES H p)
      (SSGRoute.Phi1.coeffSES_shortExact H p) h hh hsub
  have hpδ : p • (h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass hdeg) = 0 := by
    have h2 := comp_nsmul_right h p (SSGRoute.Phi1.coeffSES_shortExact H p).extClass hdeg
    have h3 : h.comp (p • (SSGRoute.Phi1.coeffSES_shortExact H p).extClass) hdeg = 0 := by
      rw [show p • (SSGRoute.Phi1.coeffSES_shortExact H p).extClass = 0 from
        coeffSES_nsmul_extClass p H]
      exact Abelian.Ext.comp_zero h (SSGRoute.PTExt.unitRep H) 1 2 hdeg
    exact h2.symm.trans h3
  have hord : addOrderOf (h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass hdeg) = p := by
    have h1 : addOrderOf (h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass hdeg) ∣ p :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hpδ
    have h2 : addOrderOf (h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass hdeg) ≠ 1 :=
      fun h1' => hδ (AddMonoid.addOrderOf_eq_one_iff.mp h1')
    exact ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ h1).resolve_left h2
  exact hnp (by
    rw [← hord]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h0)

/-- **The Bockstein of a nonzero class is nonzero.**  For a finite group `H` and `0 ≠ h ∈ H¹(H, 𝔽_p)`
(with trivial coefficients), composing with the class of `0 → ℤ --p--> ℤ → 𝔽_p → 0` gives a nonzero
class in `H²(H, ℤ)`.  (Otherwise `h` would lie in the image of `H¹(H, ℤ) = 0`.) -/
theorem bockstein_ne_zero {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Fintype H]
    (h : extH (Rep.trivial Coeff H (ZMod p)) 1) (hh : h ≠ 0) :
    h.comp (SSGRoute.Phi1.coeffSES_shortExact H p).extClass
      (by norm_num : (1 : ℕ) + 1 = 2) ≠ 0 := by
  intro h0
  haveI : Subsingleton (Abelian.Ext (SSGRoute.PTExt.unitRep H)
      ((SSGRoute.Phi1.coeffSES H p).X₂) 1) :=
    Work.SSGRoute.E7cOmega.extH_unitRep_one_subsingleton H
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ (unitRep H)
    (SSGRoute.Phi1.coeffSES_shortExact H p) h (n₁ := 2)
    (by norm_num : (1 : ℕ) + 1 = 2) h0
  have hx₂0 : x₂ = 0 := Subsingleton.elim x₂ 0
  have hzero : h = 0 := by
    rw [← hx₂, hx₂0]
    exact Abelian.Ext.zero_comp (unitRep H) 1
      (Abelian.Ext.mk₀ (SSGRoute.Phi1.coeffSES H p).g) 1 (by norm_num : (1 : ℕ) + 0 = 1)
  exact hh hzero


/-- **Base case (`M = 𝔽_p`, trivial action) of node C6.**

This is `Work.SSGRoute.E7cC.exists_unramifiedDetector_ExtZ` specialised to the trivial module
`M = Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)`, i.e. the first step of the corrected route in
`Submission/Work/SSGRoute/E7cC/NOTE_C6_residueCharacter_route.md` §2 (see also
`Submission/Work/SSGRoute/E7cOmega/NOTE_C6_session2.md` §4 for the two invalid routes to avoid: the
identity `res ∘ cor = [G:D]` is false — only `cor ∘ res = [G:D]` holds — and the corestriction
`cor_{Gal(L/K)}(χ_a ⊗ m)` lands in the norms).

The detector is realised by the **residue character**: at the level `L` and place `q' | q` of
`Work.SSGRoute.E7cC.exists_level_unramified_p_dvd_inertiaDeg` one has `e(q'|q) = 1` and
`p ∣ f(q'|q)`; the residue field extension `κ(q')/κ(q∩k)` is cyclic of order `f(q'|q)`, and the
natural map `Gal(L/k) → Gal(κ(q')/κ(q∩k)) → ℤ/p` is a global class
`h ∈ H¹(Gal(L/k), res 𝔽_p)`; it kills `I_{q'}` (it factors through the action on the residue field)
and is nonzero at `Frob_{q'}`, because `p ∣ f(q'|q) ∣ f(q'|q∩k)`.

Non-vacuity: `Ext¹_{D_w}(res 𝔽_p, ℤ) ≅ Hom_{D_w}(res 𝔽_p, ℚ/ℤ) = ℤ/p ≠ 0` (equivalently
`Work.SSGRoute.ext_zmod_prime_iso_corrected`), so `φ ≠ 0` is satisfiable; `hpq` is unused in this
specialisation (kept for uniformity with the general node).  Expected work: the bridge
`Place.ofFinite q' ↔ q'.asIdeal.LiesOver`, producing the residue character as an honest `extH` class,
`ramificationIdx' = 1 ⟹ Nat.Coprime _ p`, and the Yoneda-pairing identity
`levelPair = δ ∘ (μ ∘ res h)` (provable from `SSGRoute.Phi1.coeffSES` without any `ℚ/ℤ`-coefficient
SES). -/
theorem exists_unramifiedDetector_ExtZ_trivial (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
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
      (h : SSGRoute.PTExt.extH
        (Rep.res (SSGRoute.PTExt.galRes k K ↥L)
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
  -- ## The arithmetic input.  `Work.SSGRoute.Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg`
  -- produces a level `L ⊇ K`, a place `q' | q` with `e(q'|q) = 1` and `p ∣ f(q'|q)`, together with
  -- the residue character `χ : Gal(L/k) →* ℤ/p` at `q'`: it kills the inertia of `q'` (so its class is
  -- unramified there) and is non-trivial on the decomposition group of `q'` (so the class is not
  -- killed by the local pairing).
  obtain ⟨L, hnfL, hfdL, hgalL, q', hq'lies, he, _hpdvd, χ, hχinertia, hχne⟩ :=
    Work.SSGRoute.Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg p k K Ω q
  letI : NumberField ↥L := hnfL
  letI : FiniteDimensional k ↥L := hfdL
  letI : IsGalois k ↥L := hgalL
  haveI hq'liesI : q'.asIdeal.LiesOver q.asIdeal := hq'lies
  haveI hfdKL : FiniteDimensional K ↥L := FiniteDimensional.right k K ↥L
  -- the prime `q'` is a place of `L` over the place `w` of `K`
  have hq'w : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w := by
    rw [hwq]
    exact NK.GlobalCFT.Place.liesOver_ofFinite hq'lies
  -- ## the additive character attached to `χ`
  let f : Additive (↥L ≃ₐ[k] ↥L) →+ ZMod p :=
    { toFun := fun a => Multiplicative.toAdd (χ (Additive.toMul a))
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hfker : ∀ σ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' σ → f (Additive.ofMul σ) = 0 := by
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
  -- ## the detecting class: the class of the residue character, unramified at `q'` and non-zero on
  -- the decomposition group `D_{q'}`
  obtain ⟨h, hunram, hne⟩ : ∃ h : SSGRoute.PTExt.extH
      (Rep.res (SSGRoute.PTExt.galRes k K ↥L)
        (Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p))) 1,
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      SSGRoute.PTExt.extHRestrict
        (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h ≠ 0 :=
    Work.SSGRoute.Sha2Lib.extH_class_of_character (k := k) (K := K) (L := ↥L) p q' f hfker hfne
  -- ## `e(q'|q) = 1` makes the ramification index of `q'` over `q` prime to `p`
  have hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx q.asIdeal q'.asIdeal q.ne_bot, he]
    exact Nat.coprime_one_left p
  refine ⟨L, hnfL, hfdL, hgalL, q', hq'w, h, hunram, hcop, ?_⟩
  -- ## the Yoneda pairing of `φ` with the restricted detecting class is non-zero
  haveI : Fintype (↥L ≃ₐ[k] ↥L) := Fintype.ofFinite _
  haveI : Fintype (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite q')) := Fintype.ofFinite _
  haveI : Fintype (SSGRoute.PTExt.decompK (k := k) (K := K) w) := Fintype.ofFinite _
  exact levelPair_trivResInv_ne_zero (p := p)
    (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq'w) φ hφ
    (SSGRoute.PTExt.extHRestrict
      (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) hne

end Work.SSGRoute.E7cC
