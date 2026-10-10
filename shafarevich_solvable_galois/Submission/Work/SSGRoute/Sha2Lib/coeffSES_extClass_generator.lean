import Mathlib.Computability.Reduce
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Data.Int.Star
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Submission.Work.SSGRoute.E7cOmega.extH_unitRep_one_subsingleton
import Submission.Work.SSGRoute.ext_zmod_prime_iso_corrected

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory

/-- A `Coeff`-linear endomorphism of the trivial representation on `Coeff` is multiplication by
its value at `1`. -/
private lemma unitRep_end_eq_smul (G : Type) [Group G]
    (g : SSGRoute.PTExt.unitRep G ⟶ SSGRoute.PTExt.unitRep G) :
    g = (g.hom (1 : SSGRoute.PTExt.Coeff)) • 𝟙 (SSGRoute.PTExt.unitRep G) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext_ring
  rw [Rep.smul_hom, Rep.hom_id]
  rw [show (g.hom 1 : SSGRoute.PTExt.Coeff) = ULift.up (g.hom 1).down from ULift.ext rfl,
    ULift.smul_def]
  simp only [Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.coe_zsmul, Pi.smul_apply,
    Representation.IntertwiningMap.id_apply]
  rw [zsmul_eq_mul, mul_one]
  exact (ULift.ext rfl).symm

/-- `mk₀` is `ℤ`-linear. -/
private lemma mk₀_zsmul {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (m : ℤ) (f : X ⟶ Y) :
    CategoryTheory.Abelian.Ext.mk₀ (m • f) = m • CategoryTheory.Abelian.Ext.mk₀ f := by
  simpa using map_zsmul (CategoryTheory.Abelian.Ext.addEquiv₀ (X := X) (Y := Y)).symm m f

/-- `Ext.comp` is `ℤ`-linear in its second argument (in degree `0`). -/
private lemma comp_zsmul {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z : C} {n : ℕ} (α : CategoryTheory.Abelian.Ext X Y n) (m : ℤ)
    (β : CategoryTheory.Abelian.Ext Y Z 0) {k : ℕ} (h : n + 0 = k) :
    α.comp (m • β) h = m • α.comp β h := by
  simpa using map_zsmul (α.precomp Z h) m β

/-- In an additive commutative group, an element `r • e` which is annihilated by `p` and non-zero
is an integer multiple `n • e` with `n` a natural number not divisible by `p`. -/
private lemma exists_nat_zsmul_eq_of_ann (p : ℕ) (hp : p.Prime) {M : Type*} [AddCommGroup M]
    (e : M) (he : (p : ℤ) • e = 0) (r : ℤ) (hr : r • e ≠ 0) :
    ∃ n : ℕ, ¬ p ∣ n ∧ (n : ℤ) • e = r • e := by
  have hp0 : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hpr : ¬ (p : ℤ) ∣ r := by
    rintro ⟨q, hq⟩
    apply hr
    rw [hq, mul_comm, mul_zsmul, he, smul_zero]
  set n := (r % (p : ℤ)).toNat with hn
  have hnonneg : 0 ≤ r % (p : ℤ) := Int.emod_nonneg r (ne_of_gt hp0)
  have hncast : (n : ℤ) = r % (p : ℤ) := by
    rw [hn]; exact Int.toNat_of_nonneg hnonneg
  have hne : r % (p : ℤ) ≠ 0 := by
    intro h
    exact hpr (Int.dvd_of_emod_eq_zero h)
  have hlt : r % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos r hp0
  have hnpos : 0 < n := by
    have : (0 : ℤ) < (n : ℤ) := by rw [hncast]; exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    exact_mod_cast this
  have hnlt : n < p := by
    have : (n : ℤ) < (p : ℤ) := by rw [hncast]; exact hlt
    exact_mod_cast this
  refine ⟨n, Nat.not_dvd_of_pos_of_lt hnpos hnlt, ?_⟩
  have hdvd : (p : ℤ) ∣ (n : ℤ) - r := by
    have h : (p : ℤ) * (r / (p : ℤ)) = r - r % (p : ℤ) := by
      linarith [Int.mul_ediv_add_emod r (p : ℤ)]
    refine ⟨-(r / (p : ℤ)), ?_⟩
    rw [hncast, mul_neg, h]
    ring
  obtain ⟨q, hq⟩ := hdvd
  have hzero : ((n : ℤ) - r) • e = 0 := by
    rw [hq, mul_comm (p : ℤ) q, mul_zsmul, he, smul_zero]
  rw [sub_zsmul] at hzero
  have h := eq_neg_of_add_eq_zero_left hzero
  rwa [neg_neg] at h

/-- **The tautological class generates `Ext¹_G(𝔽_p, ℤ) ≅ ℤ/p`.**

For a finite group `G` and a prime `p`, every `φ ∈ Ext¹_G(𝔽_p, ℤ)` is a scalar multiple of the class
of the coefficient sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0` (written `SSGRoute.Phi1.coeffSES_shortExact`
in this workspace); if `φ ≠ 0` the multiplier is a natural number that is not divisible by `p`.

Suggested route.  Put `S := SSGRoute.Phi1.coeffSES G p` and `hS := SSGRoute.Phi1.coeffSES_shortExact G p`.
The contravariant long exact sequence of `hS` in the first variable gives that the connecting map
`a ↦ hS.extClass.comp a` from `Ext⁰(ℤ, ℤ) = SSGRoute.PTExt.extH (SSGRoute.PTExt.unitRep G) 0` to
`Ext¹(𝔽_p, ℤ)` (here `𝔽_p = Rep.trivial Coeff G (ZMod p)` and `ℤ = SSGRoute.PTExt.unitRep G`)
is surjective: this is `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃` applied to
`S`, `Y := SSGRoute.PTExt.unitRep G` and `hS`, whose hypothesis
`(Ext.mk₀ S.g).comp φ = 0` lies in `Ext¹(unitRep G, unitRep G) = H¹(G, ℤ)` and hence holds by
`Work.SSGRoute.E7cOmega.extH_unitRep_one_subsingleton G` (`G` is finite).  So `φ = hS.extClass.comp a`
for some `a`.  Now `CategoryTheory.Abelian.Ext.linearEquiv₀` (or `addEquiv₀`) identifies `a` with a
morphism `g : unitRep G ⟶ unitRep G` in `Rep Coeff G` with `a = Ext.mk₀ g`, and any such `g` is
`c • 𝟙` for `c := Rep.Hom.hom g 1` (a `Coeff`-linear endomorphism of `Coeff = ULift ℤ` is
multiplication by `g 1`, and the `G`-action on `Coeff` is trivial); hence, with
`Ext.mk₀_smul`, `Ext.comp_smul` and `Ext.comp_mk₀_id`,
`φ = c • hS.extClass`.  Finally `p • hS.extClass = 0`: rewrite the scalar with
`Ext.smul_eq_comp_mk₀` as a composition with `Ext.mk₀ ((p : Coeff) • 𝟙 (unitRep G))`, identify
`(p : Coeff) • 𝟙 (unitRep G)` with `S.f = Phi1.unitMulByP G p` by
`Work.SSGRoute.extFp_unitMulByP_eq_smul`, and use `ShortComplex.ShortExact.extClass_comp`.
This lets one convert the integer `c` into a natural number `n` with `p ∤ n`: if `c ≥ 0` take
`n = c`, and if `c < 0` use `(-m) • x = m • ((p-1) • x)` for `m > 0` together with
`p • hS.extClass = 0`.

The same statement (unproved) already exists on disk as
`Work.SSGRoute.E7cC.exists_nat_smul_coeffSES_extClass`; the present copy is asked for so that the
consumer can depend on a `sorry`-free module.  It is needed by the prover of
`Work.SSGRoute.Sha2Lib.unramifiedDetector_trivial` to transfer the Yoneda pairing with an arbitrary
nonzero `φ ∈ Ext¹(𝔽_p, ℤ)` to the tautological case. -/
theorem coeffSES_extClass_generator {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (φ : CategoryTheory.Abelian.Ext (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p))
      (SSGRoute.PTExt.unitRep G) 1) (hφ : φ ≠ 0) :
    ∃ n : ℕ, ¬ p ∣ n ∧
      φ = (n : SSGRoute.PTExt.Coeff) •
        (SSGRoute.Phi1.coeffSES_shortExact G p).extClass := by
  have hS : (SSGRoute.Phi1.coeffSES G p).ShortExact := SSGRoute.Phi1.coeffSES_shortExact G p
  have hp : p.Prime := Fact.out
  -- Step 1: the connecting map of the coefficient sequence is surjective.
  have hsub : Subsingleton (SSGRoute.PTExt.extH (SSGRoute.PTExt.unitRep G) 1) :=
    Work.SSGRoute.E7cOmega.extH_unitRep_one_subsingleton G
  have h0 : (CategoryTheory.Abelian.Ext.mk₀ (SSGRoute.Phi1.coeffSES G p).g).comp φ
      (zero_add 1) = 0 :=
    @Subsingleton.elim _ hsub _ _
  obtain ⟨a, ha⟩ := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃ hS
    (SSGRoute.PTExt.unitRep G) φ h0 (n₀ := 0) (by norm_num)
  -- Step 2: identify `a` with a scalar multiple of the class of `𝟙`.
  set g : SSGRoute.PTExt.unitRep G ⟶ SSGRoute.PTExt.unitRep G :=
    CategoryTheory.Abelian.Ext.linearEquiv₀ (R := SSGRoute.PTExt.Coeff) a with hgdef
  set c : SSGRoute.PTExt.Coeff := g.hom (1 : SSGRoute.PTExt.Coeff) with hcdef
  have hga : CategoryTheory.Abelian.Ext.mk₀ g = a := by
    rw [hgdef]
    exact CategoryTheory.Abelian.Ext.mk₀_linearEquiv₀_apply a
  have hgUL : g = c • 𝟙 ((SSGRoute.Phi1.coeffSES G p).X₁) := by
    rw [hcdef]
    exact unitRep_end_eq_smul G g
  have hgZ : g = c.down • 𝟙 ((SSGRoute.Phi1.coeffSES G p).X₁) := by
    rw [hgUL, show c = ULift.up c.down from ULift.ext rfl, ULift.smul_def]
  have haZ : a = (c.down : ℤ) •
      CategoryTheory.Abelian.Ext.mk₀ (𝟙 ((SSGRoute.Phi1.coeffSES G p).X₁)) := by
    rw [← hga, hgZ]
    exact mk₀_zsmul c.down (𝟙 ((SSGRoute.Phi1.coeffSES G p).X₁))
  have ha' : hS.extClass.comp a (add_zero 1) = φ := ha
  have hA : hS.extClass.comp a (add_zero 1)
      = hS.extClass.comp ((c.down : ℤ) • CategoryTheory.Abelian.Ext.mk₀
          (𝟙 ((SSGRoute.Phi1.coeffSES G p).X₁))) (add_zero 1) :=
    congrArg (fun x => hS.extClass.comp x (add_zero 1)) haZ
  have hB : hS.extClass.comp ((c.down : ℤ) • CategoryTheory.Abelian.Ext.mk₀
        (𝟙 ((SSGRoute.Phi1.coeffSES G p).X₁))) (add_zero 1)
      = (c.down : ℤ) • (hS.extClass.comp (CategoryTheory.Abelian.Ext.mk₀
          (𝟙 ((SSGRoute.Phi1.coeffSES G p).X₁))) (add_zero 1)) :=
    comp_zsmul hS.extClass c.down (CategoryTheory.Abelian.Ext.mk₀
      (𝟙 ((SSGRoute.Phi1.coeffSES G p).X₁))) (add_zero 1)
  have hC : (c.down : ℤ) • (hS.extClass.comp (CategoryTheory.Abelian.Ext.mk₀
        (𝟙 ((SSGRoute.Phi1.coeffSES G p).X₁))) (add_zero 1))
      = (c.down : ℤ) • hS.extClass :=
    congrArg (fun y => (c.down : ℤ) • y)
      (CategoryTheory.Abelian.Ext.comp_mk₀_id hS.extClass)
  have hφZ : φ = (c.down : ℤ) • hS.extClass := (ha'.symm.trans hA).trans (hB.trans hC)
  -- Step 3: the tautological class is `p`-torsion.
  have h1z : (p : ℤ) • (𝟙 ((SSGRoute.Phi1.coeffSES G p).X₁)) =
      (SSGRoute.Phi1.coeffSES G p).f := by
    rw [show (SSGRoute.Phi1.coeffSES G p).f = SSGRoute.Phi1.unitMulByP G p from rfl]
    exact ((ULift.smul_def (ULift.up (p : ℤ) : SSGRoute.PTExt.Coeff)
        (𝟙 (SSGRoute.PTExt.unitRep G))).symm.trans
      (Work.SSGRoute.extFp_unitMulByP_eq_smul p G).symm)
  have hpe : (p : SSGRoute.PTExt.Coeff) • hS.extClass = 0 := by
    rw [show (p : SSGRoute.PTExt.Coeff) = ULift.up (p : ℤ) from rfl, ULift.smul_def]
    rw [← @Int.cast_smul_eq_zsmul SSGRoute.PTExt.Coeff
      (CategoryTheory.Abelian.Ext ((SSGRoute.Phi1.coeffSES G p).X₃)
        ((SSGRoute.Phi1.coeffSES G p).X₁) 1)
      _ _ Abelian.Ext.instModule (p : ℤ) hS.extClass]
    rw [CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀]
    rw [@Int.cast_smul_eq_zsmul SSGRoute.PTExt.Coeff
      ((SSGRoute.Phi1.coeffSES G p).X₁ ⟶ (SSGRoute.Phi1.coeffSES G p).X₁)
      _ _ Rep.instModuleHom (p : ℤ) (𝟙 _)]
    rw [h1z]
    exact CategoryTheory.ShortComplex.ShortExact.extClass_comp hS
  have hpeZ : (p : ℤ) • hS.extClass = 0 := by
    have h := hpe
    rw [show (p : SSGRoute.PTExt.Coeff) = ULift.up (p : ℤ) from rfl,
      ULift.smul_def] at h
    exact h
  -- Step 4: reduce the integer scalar to a natural number coprime to `p`.
  have hc_ne : (c.down : ℤ) • hS.extClass ≠ 0 := by
    rw [← hφZ]
    exact hφ
  obtain ⟨n, hndvd, hn⟩ :=
    exists_nat_zsmul_eq_of_ann p hp hS.extClass hpeZ c.down hc_ne
  refine ⟨n, hndvd, ?_⟩
  rw [hφZ, ← hn]
  rw [show (n : SSGRoute.PTExt.Coeff) = ULift.up (n : ℤ) from rfl, ULift.smul_def]

end Work.SSGRoute.Sha2Lib
