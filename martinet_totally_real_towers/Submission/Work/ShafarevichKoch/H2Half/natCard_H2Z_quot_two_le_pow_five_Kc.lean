import Mathlib
import Submission.Work.ShafarevichKoch.RatCoeff
import Submission.Work.ShafarevichKoch.RatVanishing.subsingleton_H1_H2_rat
import Submission.Work.ShafarevichKoch.CountZ
import Submission.Work.ShafarevichKoch.TorsionCokernel.natCard_quot_two_le_natCard_twoTorsion
import Submission.Work.ShafarevichKoch.GeneratorRankKc
import Submission.Work.ConCohomology.TrivialAction
import Submission.Work.ShaBound.isProPGroup_two_maximalProP

/-!
# `Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc`

For `Kc = ℚ(√-30030)` and `G = G_∅ = Gal(Kc_∅/Kc)` the maximal unramified pro-`2` Galois group,

  `#(H²(G,ℤ) ⧸ 2·H²(G,ℤ)) ≤ 2^5 = 32`,

the `H²`-half of the Shafarevich--Koch crux for the benchmark field `Kc` (the other half being the
`ℤ/2`-coefficient count consumed in `Work.ShafarevichKoch.CountZ`).

The proof is *elementary* (no class field theory): the coefficient sequence `0 → ℤ → ℚ → ℚ/ℤ → 0`
identifies `H²(G,ℤ)` with `H¹(G,ℚ/ℤ)` through the connecting map `δ¹` (`Work.ShafarevichKoch.RatCoeff`
and the vanishing of `H¹(G,ℚ)`, `H²(G,ℚ)` supplied by
`Work.ShafarevichKoch.RatVanishing.subsingleton_H1_H2_rat`).  Since `G` is a pro-`2` group, `H¹(G,ℚ/ℤ)`
is `2`-primary torsion with finite `2`-torsion, so `#(H¹(G,ℚ/ℤ) ⧸ 2) ≤ #H¹(G,ℚ/ℤ)[2]` by the pure
algebra of `Work.ShafarevichKoch.TorsionCokernel.natCard_quot_two_le_natCard_twoTorsion`; and the
`2`-torsion of `H²(G,ℤ)` is the image of `H¹(G,ℤ/2) = H¹(G,𝔽₂) = ProTwoChar Kc M`, which has `32`
elements by item (1) of the deliverable (`Work.ShafarevichKoch.card_proTwoChar_Kc`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Classical

namespace Work.ShafarevichKoch.H2Half

open Work.ConCohomology Work.ShafarevichKoch

noncomputable section



/-! ## The connecting map `δ¹` computed with an arbitrary lift -/

section General

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
variable [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]

/-- The canonical lift of a `1`-cocycle with values in `C` to a `1`-cochain with values in `B`,
given by the chosen set-theoretic section of the projection `g`. -/
def canonU1 (S : CoeffSES G A B C) (z : Z1 G C) : Cochain1 G B :=
  ⟨fun σ => S.sect ((z : Cochain1 G C) σ), isLocallyConstant_sect_comp S (z : Cochain1 G C)⟩

@[simp] lemma canonU1_apply (S : CoeffSES G A B C) (z : Z1 G C) (σ : G) :
    canonU1 S z σ = S.sect ((z : Cochain1 G C) σ) := rfl

lemma g_canonU1 (S : CoeffSES G A B C) (z : Z1 G C) (σ : G) :
    S.g (canonU1 S z σ) = (z : Cochain1 G C) σ := S.g_sect _

/-- The `A`-valued `2`-cochain `S.invFun ∘ d¹u` attached to a `B`-valued `1`-cochain `u`. -/
def connCochain2 (S : CoeffSES G A B C) (u : Cochain1 G B) : Cochain2 G A :=
  coeffInvFun2 S (d1Hom G B u)

@[simp] lemma connCochain2_apply (S : CoeffSES G A B C) (u : Cochain1 G B) (p : G × G) :
    connCochain2 S u p = S.invFun (d1Fun (u : G → B) p) := by
  rw [connCochain2, coeffInvFun2_apply]
  rfl

/-- The `A`-valued `1`-cochain measuring the difference between the canonical section at `z` and
the lift `u`. -/
def connCochain1 (S : CoeffSES G A B C) (z : Z1 G C) (u : Cochain1 G B) : Cochain1 G A :=
  ⟨fun σ => S.invFun (S.sect ((z : Cochain1 G C) σ) - (u : G → B) σ),
    (((isLocallyConstant_sect_comp S (z : Cochain1 G C)).sub
      (u : Cochain1 G B).isLocallyConstant).comp S.invFun)⟩

@[simp] lemma connCochain1_apply (S : CoeffSES G A B C) (z : Z1 G C) (u : Cochain1 G B) (σ : G) :
    connCochain1 S z u σ = S.invFun (S.sect ((z : Cochain1 G C) σ) - (u : G → B) σ) := rfl

lemma f_connCochain1 (S : CoeffSES G A B C) (z : Z1 G C) (u : Cochain1 G B)
    (hu : ∀ σ : G, S.g (u σ) = (z : Cochain1 G C) σ) (ν : G) :
    S.f (connCochain1 S z u ν) = S.sect ((z : Cochain1 G C) ν) - (u : G → B) ν := by
  rw [connCochain1_apply]
  exact f_invFun_of_g_eq_zero S (by simp only [EqHom.map_sub, S.g_sect, hu ν, sub_self])

/-- **The connecting map `δ¹` computed with an arbitrary lift.**  If `z` is a `1`-cocycle with
values in `C` and `u : G → B` is any locally constant lift of `z` along the projection `g`, then
the connecting image `δ¹[z] ∈ H²(G,A)` is represented by the `A`-valued `2`-cocycle
`S.invFun ∘ d¹u`, whose `f`-image is `d¹u`. -/
theorem connecting1_spec (S : CoeffSES G A B C) (z : Z1 G C) (u : Cochain1 G B)
    (hu : ∀ σ : G, S.g (u σ) = (z : Cochain1 G C) σ) :
    ∃ w : Z2 G A, H2.mk w = connecting1 S (H1.mk z) ∧
      (∀ p : G × G, S.f ((w : G × G → A) p) = d1Fun (u : G → B) p) := by
  -- `g ∘ d¹u = d¹(g ∘ u) = d¹z = 0`, so `d¹u` takes values in `ker g = im f`
  have hgz : ∀ p : G × G, S.g (d1Fun (u : G → B) p) = 0 := by
    have hzu : (fun σ : G => S.g (u σ)) = (((z : Z1 G C) : Cochain1 G C) : G → C) := funext hu
    have hz0 : d1Fun (G := G) (M := C) ((((z : Z1 G C) : Cochain1 G C)) : G → C) = 0 :=
      (isCocycle1_iff_d1Fun _).mp (mem_Z1.mp z.2)
    have hfun : (fun p : G × G => S.g (d1Fun (u : G → B) p)) = 0 := by
      rw [← d1Fun_comp (G := G) S.g (u : G → B), hzu, hz0]
    intro p
    exact congrFun hfun p
  -- `wc := S.invFun ∘ d¹u` is a `2`-cocycle with `f ∘ wc = d¹u`
  have hwc : ∀ p : G × G, S.f (connCochain2 S u p) = d1Fun (u : G → B) p := by
    intro p
    rw [connCochain2_apply]
    exact f_invFun_of_g_eq_zero S (hgz p)
  have hcoc : connCochain2 S u ∈ Z2 G A := by
    rw [mem_Z2, isCocycle2_iff_d2Fun]
    funext p
    have h2 := congrFun (d2Fun_eqHom_comp (G := G) S.f
      ((connCochain2 S u : Cochain2 G A) : G × G → A)) p
    have h1 : d2Fun (G := G) (M := B) (fun q : G × G => S.f (connCochain2 S u q)) p = 0 := by
      rw [show (fun q : G × G => S.f (connCochain2 S u q)) = (d1Fun (u : G → B)) from funext hwc]
      exact congrFun (d2Fun_d1Fun (G := G) (u : G → B)) p
    have h4 : S.f (d2Fun (G := G) (M := A)
        ((connCochain2 S u : Cochain2 G A) : G × G → A) p) = 0 := by
      rw [← h2, h1]
    have h5 : S.f (d2Fun (G := G) (M := A)
        ((connCochain2 S u : Cochain2 G A) : G × G → A) p) = S.f 0 := by
      rw [h4, EqHom.map_zero]
    have h6 : d2Fun (G := G) (M := A) ((connCochain2 S u : Cochain2 G A) : G × G → A) p = 0 :=
      S.injective_f h5
    simpa using h6
  refine ⟨⟨connCochain2 S u, hcoc⟩, ?_, ?_⟩
  · -- `[S.invFun ∘ d¹u] = δ¹[z]`
    refine ((H2.mk_eq_mk_iff (connectingZ1 S z) ⟨connCochain2 S u, hcoc⟩).mpr ?_).symm
    rw [mem_B2', mem_B2]
    refine ⟨connCochain1 S z u, ?_⟩
    rw [AddSubgroup.coe_sub]
    refine LocallyConstant.ext fun p => ?_
    obtain ⟨σ, τ⟩ := p
    simp only [d1Hom_apply, LocallyConstant.sub_apply]
    have h1 : S.f ((connectingZ1 S z : Cochain2 G A) (σ, τ))
        = σ • S.sect ((z : Cochain1 G C) τ) - S.sect ((z : Cochain1 G C) (σ * τ))
          + S.sect ((z : Cochain1 G C) σ) := by
      rw [connectingZ1_coe]
      simp only [LocallyConstant.coe_mk]
      rw [CoeffSES.delta1Fun_apply]
      exact invFun_f_eq_delta1Fun_aux S ((S.exact _).mp (by
        simp only [EqHom.map_add, EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect]
        rw [mem_Z1.mp z.2 σ τ]
        abel))
    have h2 : S.f ((connCochain2 S u : Cochain2 G A) (σ, τ)) = d1Fun (u : G → B) (σ, τ) :=
      hwc (σ, τ)
    have h3 : S.f (σ • (connCochain1 S z u) τ - (connCochain1 S z u) (σ * τ)
          + (connCochain1 S z u) σ)
        = σ • (S.sect ((z : Cochain1 G C) τ) - (u : G → B) τ)
          - (S.sect ((z : Cochain1 G C) (σ * τ)) - (u : G → B) (σ * τ))
          + (S.sect ((z : Cochain1 G C) σ) - (u : G → B) σ) := by
      simp only [EqHom.map_add, EqHom.map_sub, EqHom.map_smul, f_connCochain1 S z u hu,
        smul_sub]
    apply S.injective_f
    rw [EqHom.map_sub, h3, h1, h2, d1Fun_apply]
    simp only [smul_sub]
    abel
  · intro p
    exact hwc p

/-- **Additivity of the connecting map `δ¹`.**  For a short exact sequence
`0 → A → B → C → 0` of discrete `G`-modules, the connecting map
`δ¹ : H¹(G,C) → H²(G,A)` is a group homomorphism. -/
theorem connecting1_add (S : CoeffSES G A B C) (x y : H1 G C) :
    connecting1 S (x + y) = connecting1 S x + connecting1 S y := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective y
  show connecting1 S (H1.mk (z + w)) = connecting1 S (H1.mk z) + connecting1 S (H1.mk w)
  have hsum : ∀ σ : G, S.g ((canonU1 S z + canonU1 S w) σ)
      = ((z + w : Z1 G C) : Cochain1 G C) σ := by
    intro σ
    simp only [LocallyConstant.coe_add, Pi.add_apply, EqHom.map_add, g_canonU1,
      AddSubgroup.coe_add]
  obtain ⟨r₁, hr₁, hs₁⟩ := connecting1_spec S z (canonU1 S z) (g_canonU1 S z)
  obtain ⟨r₂, hr₂, hs₂⟩ := connecting1_spec S w (canonU1 S w) (g_canonU1 S w)
  obtain ⟨r₁₂, hr₁₂, hs₁₂⟩ := connecting1_spec S (z + w) (canonU1 S z + canonU1 S w) hsum
  have heq : r₁₂ = r₁ + r₂ := by
    refine Subtype.ext (LocallyConstant.ext fun p => ?_)
    obtain ⟨σ, τ⟩ := p
    apply S.injective_f
    rw [hs₁₂ (σ, τ), LocallyConstant.coe_add, d1Fun_add]
    simp only [AddSubgroup.coe_add, LocallyConstant.add_apply, EqHom.map_add, Pi.add_apply,
      hs₁ (σ, τ), hs₂ (σ, τ)]
  rw [← hr₁₂, ← hr₁, ← hr₂, heq]
  exact map_add (QuotientAddGroup.mk' (B2' G A)) r₁ r₂

end General

/-! ## The comparison `ContAddHom G 𝔽₂ ≃ ProTwoChar Kc M` -/

/-- **Continuous additive homomorphisms `G → 𝔽₂` are continuous multiplicative homomorphisms
`G →* Multiplicative 𝔽₂`**: both conditions reduce, through `Multiplicative.ofAdd`/`toAdd`, to the
same pair (local constancy, additivity). -/
noncomputable def contAddHomEquivContinuousHom (G : Type*) [Group G] [TopologicalSpace G]
    (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] :
    ContAddHom G A ≃ {f : G →* Multiplicative A // Continuous f} where
  toFun φ := ⟨
    { toFun := fun σ => Multiplicative.ofAdd (φ σ)
      map_one' := by
        have h1 : φ (1 * 1) = φ 1 + φ 1 := ContAddHom.map_mul φ 1 1
        rw [one_mul] at h1
        have h2 : φ 1 + 0 = φ 1 + φ 1 := by rw [add_zero]; exact h1
        have h : φ 1 = 0 := (add_left_cancel h2).symm
        rw [h, ofAdd_zero]
      map_mul' := fun σ τ => by
        show Multiplicative.ofAdd (φ (σ * τ)) =
          Multiplicative.ofAdd (φ σ) * Multiplicative.ofAdd (φ τ)
        rw [ContAddHom.map_mul, ofAdd_add] },
    (IsLocallyConstant.iff_continuous _).mp
      ((ContAddHom.isLocallyConstant φ).comp (Multiplicative.ofAdd : A → Multiplicative A))⟩
  invFun χ := ⟨fun σ => Multiplicative.toAdd (χ.1 σ),
    ((IsLocallyConstant.iff_continuous (χ.1 : G → Multiplicative A)).mpr χ.2).comp
      (Multiplicative.toAdd : Multiplicative A → A),
    fun σ τ => by
      show Multiplicative.toAdd (χ.1 (σ * τ)) =
        Multiplicative.toAdd (χ.1 σ) + Multiplicative.toAdd (χ.1 τ)
      rw [map_mul, toAdd_mul]⟩
  left_inv φ := Subtype.ext (funext fun σ => toAdd_ofAdd (φ σ))
  right_inv χ := Subtype.ext (MonoidHom.ext fun σ => ofAdd_toAdd (χ.1 σ))

/-- The same equivalence, in the form used below: continuous additive homs `G_∅ → 𝔽₂` are the
continuous characters `G_∅ → ℤ/2`, i.e. the elements of `ProTwoChar Kc M`. -/
noncomputable def contAddHomEquivProTwoChar
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2) :
    ContAddHom (Work.ClassFieldTower.galoisGroup M) (ZMod 2) ≃
      ProTwoChar Work.ClassFieldTower.Kc M :=
  contAddHomEquivContinuousHom (Work.ClassFieldTower.galoisGroup M) (ZMod 2)

/-! ## `H¹(G,ℚ/ℤ)` is `2`-primary torsion when `G` is a pro-`2` group -/

/-- **The image of a continuous additive homomorphism `G → ℚ/ℤ` from a pro-`2` group is killed by a
power of `2`**.  A continuous additive homomorphism `φ : G → ℚ/ℤ` is locally constant, so its
kernel is open (and normal); the finite quotient `G ⧸ ker φ` is then a quotient of the pro-`2`
group `G`, hence a finite `2`-group, and `φ` factors through it. -/
theorem exists_two_pow_nsmul_eq_zero_of_isProPGroup {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (hG : Work.RelatorRank.IsProPGroup 2 G)
    (φ : ContAddHom G QZ) :
    ∃ k : ℕ, (2 : ℕ) ^ k • φ = 0 := by
  -- the multiplicative form of `φ`
  let f : G →* Multiplicative QZ :=
    { toFun := fun σ => Multiplicative.ofAdd (φ σ)
      map_one' := by
        have h1 : φ (1 * 1) = φ 1 + φ 1 := ContAddHom.map_mul φ 1 1
        rw [one_mul] at h1
        have h2 : φ 1 + 0 = φ 1 + φ 1 := by rw [add_zero]; exact h1
        have h : φ 1 = 0 := (add_left_cancel h2).symm
        rw [h, ofAdd_zero]
      map_mul' := fun σ τ => by
        show Multiplicative.ofAdd (φ (σ * τ)) =
          Multiplicative.ofAdd (φ σ) * Multiplicative.ofAdd (φ τ)
        rw [ContAddHom.map_mul, ofAdd_add] }
  have hf_apply : ∀ σ : G, f σ = Multiplicative.ofAdd (φ σ) := fun _ => rfl
  have hker : (f.ker : Set G) = {σ : G | φ σ = 0} := by
    ext σ
    change σ ∈ f.ker ↔ φ σ = 0
    rw [MonoidHom.mem_ker, hf_apply, ofAdd_eq_one]
  have hopen : IsOpen (f.ker : Set G) := by
    rw [hker]
    exact (ContAddHom.isLocallyConstant φ).isOpen_fiber 0
  haveI : Finite (G ⧸ f.ker) := Subgroup.quotient_finite_of_isOpen f.ker hopen
  have hpg : IsPGroup 2 (G ⧸ f.ker) :=
    hG (OpenNormalSubgroup.mk (OpenSubgroup.mk f.ker hopen) inferInstance)
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hpg
  have hQcard : ∀ q : G ⧸ f.ker, q ^ (2 : ℕ) ^ n = 1 := by
    haveI : Fintype (G ⧸ f.ker) := Fintype.ofFinite _
    have hcard : Fintype.card (G ⧸ f.ker) = (2 : ℕ) ^ n := by
      rw [← Nat.card_eq_fintype_card]; exact hn
    intro q
    simpa [hcard] using (pow_card_eq_one : q ^ Fintype.card (G ⧸ f.ker) = 1)
  let ψ : G ⧸ f.ker →* Multiplicative QZ := QuotientGroup.lift f.ker f le_rfl
  have hψ : ∀ σ : G, ψ (QuotientGroup.mk' f.ker σ) = f σ := fun σ =>
    QuotientGroup.lift_mk' f.ker le_rfl σ
  have hφσ : ∀ σ : G, (2 : ℕ) ^ n • φ σ = 0 := by
    intro σ
    have h := congrArg ψ (hQcard (QuotientGroup.mk' f.ker σ))
    rw [map_pow, map_one, hψ σ, hf_apply, ← ofAdd_nsmul, ofAdd_eq_one] at h
    exact h
  refine ⟨n, ?_⟩
  ext σ
  exact hφσ σ

/-! ## The cardinality of `H¹(G_∅, 𝔽₂)` -/

section Kc

open Work.ClassFieldTower

variable (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)

local instance instF2Action : DistribMulAction (Work.ClassFieldTower.galoisGroup M) (ZMod 2) :=
  Work.RelatorRank.f2TrivialAction _

local instance instF2Discrete : IsDiscreteGModule (Work.ClassFieldTower.galoisGroup M) (ZMod 2) :=
  Work.RelatorRank.f2Discrete _

/-- **`#H¹(G_∅, 𝔽₂) = 2^5 = 32`**, i.e. the generator rank of `G_∅` is `5`: the continuous
characters `G_∅ → ℤ/2` are the elements of `ProTwoChar Kc M`, of which there are
`2 ^ rank₂ Cl(Kc) = 32`. -/
theorem natCard_H1_zmodTwo_galoisGroup_Kc :
    Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) = 2 ^ 5 := by
  have htriv2 : ∀ (σ : Work.ClassFieldTower.galoisGroup M) (m : ZMod 2), σ • m = m :=
    fun σ m => smul_zmodTwo_eq σ m
  calc Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2))
      = Nat.card (ContAddHom (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) :=
        Nat.card_congr (H1EquivContAddHom htriv2)
    _ = Nat.card (ProTwoChar Work.ClassFieldTower.Kc M) :=
        Nat.card_congr (contAddHomEquivProTwoChar M)
    _ = 2 ^ 5 := by rw [card_proTwoChar_Kc M, classGroupTwoRank_Kc]

end Kc

/-! ## The main theorem -/

/-- **The `H²`-half of the Shafarevich--Koch crux for `Kc`**: the `2`-rank of `H²(G_∅,ℤ)` is at
most `5`, i.e. `#(H²(G_∅,ℤ) ⧸ 2H²(G_∅,ℤ)) ≤ 2^5`. -/
theorem natCard_H2Z_quot_two_le_pow_five_Kc
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2) :
    Nat.card (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
      Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M)) ≤ 2 ^ 5 := by
  letI : DistribMulAction (Work.ClassFieldTower.galoisGroup M) (ZMod 2) :=
    Work.RelatorRank.f2TrivialAction _
  letI : IsDiscreteGModule (Work.ClassFieldTower.galoisGroup M) (ZMod 2) :=
    Work.RelatorRank.f2Discrete _
  have htrivQ : ∀ (σ : Work.ClassFieldTower.galoisGroup M) (q : ℚ), σ • q = q := fun _ _ => rfl
  have htrivQZ : ∀ (σ : Work.ClassFieldTower.galoisGroup M) (m : QZ), σ • m = m := fun _ _ => rfl
  -- `G_∅` is a pro-`2` group
  have hpro : Work.RelatorRank.IsProPGroup 2 (Work.ClassFieldTower.galoisGroup M) :=
    Work.ShaBound.isProPGroup_of_forall_intermediateField_isPGroup
      (F := Work.ClassFieldTower.Kc) (K := M.K) M.proP
  -- `H¹(G,ℚ) = H²(G,ℚ) = 0` (compact totally disconnected group, divisible coefficients)
  obtain ⟨h1Q, h2Q⟩ :=
    Work.ShafarevichKoch.RatVanishing.subsingleton_H1_H2_rat
      (G := Work.ClassFieldTower.galoisGroup M) htrivQ
  haveI : Subsingleton (H2 (Work.ClassFieldTower.galoisGroup M) ℚ) := h2Q
  haveI : Subsingleton (H1 (Work.ClassFieldTower.galoisGroup M) ℚ) := h1Q
  -- the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0` is surjective and additive
  have hsurjδ : Function.Surjective
      (connecting1 (ratCoeffSES (Work.ClassFieldTower.galoisGroup M))) := by
    intro x
    refine (exact_H2_A (ratCoeffSES (Work.ClassFieldTower.galoisGroup M)) x).mp ?_
    exact Subsingleton.elim _ _
  let δ : H1 (Work.ClassFieldTower.galoisGroup M) QZ →+
      H2 (Work.ClassFieldTower.galoisGroup M) ℤ :=
    AddMonoidHom.mk' (connecting1 (ratCoeffSES (Work.ClassFieldTower.galoisGroup M)))
      (fun x y => connecting1_add _ x y)
  -- hence `H²(G,ℤ)` is `2`-primary torsion
  have htorQZ : ∀ y : H1 (Work.ClassFieldTower.galoisGroup M) QZ,
      ∃ k : ℕ, (2 : ℕ) ^ k • y = 0 := by
    intro y
    obtain ⟨k, hk⟩ :=
      exists_two_pow_nsmul_eq_zero_of_isProPGroup hpro (H1ToContAddHom htrivQZ y)
    refine ⟨k, ?_⟩
    apply (H1EquivContAddHom htrivQZ).injective
    change H1ToContAddHom htrivQZ ((2 : ℕ) ^ k • y) = H1ToContAddHom htrivQZ 0
    rw [map_nsmul, hk, map_zero]
  have htor : ∀ x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ,
      ∃ k : ℕ, (2 : ℕ) ^ k • x = 0 := by
    intro x
    obtain ⟨y, hy⟩ := hsurjδ x
    obtain ⟨k, hk⟩ := htorQZ y
    exact ⟨k, by rw [show x = δ y from hy.symm, ← map_nsmul, hk, map_zero]⟩
  -- its `2`-torsion is the image of `H¹(G,𝔽₂)`
  have hsurj2 : Function.Surjective (fun y : H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2) =>
      (⟨connecting1 (ZSES (Work.ClassFieldTower.galoisGroup M)) y, by
        rw [← H2Map_zModTwoCoeffSES_f]
        exact (exact_H2_A (ZSES (Work.ClassFieldTower.galoisGroup M))
          (connecting1 (ZSES (Work.ClassFieldTower.galoisGroup M)) y)).mpr
            ⟨y, rfl⟩⟩ :
        {x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ // (2 : ℕ) • x = 0})) := by
    intro x
    have h0 : H2Map (ZSES (Work.ClassFieldTower.galoisGroup M)).f x.1 = 0 := by
      rw [H2Map_zModTwoCoeffSES_f]
      exact x.2
    obtain ⟨y, hy⟩ := (exact_H2_A (ZSES (Work.ClassFieldTower.galoisGroup M)) x.1).mp h0
    exact ⟨y, Subtype.ext hy⟩
  haveI hfinH1 : Finite (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) :=
    (Nat.card_ne_zero.mp (by rw [natCard_H1_zmodTwo_galoisGroup_Kc M]; norm_num)).2
  haveI hfinite_tors : Finite {x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ //
      (2 : ℕ) • x = 0} := Finite.of_surjective _ hsurj2
  have htors_le : Nat.card {x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ //
      (2 : ℕ) • x = 0} ≤ 2 ^ 5 :=
    le_trans (Nat.card_le_card_of_surjective _ hsurj2)
      (le_of_eq (natCard_H1_zmodTwo_galoisGroup_Kc M))
  -- the pure-algebra count
  calc Nat.card (H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
        Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M))
      ≤ Nat.card {x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ // (2 : ℕ) • x = 0} :=
        Work.ShafarevichKoch.TorsionCokernel.natCard_quot_two_le_natCard_twoTorsion htor hfinite_tors
    _ ≤ 2 ^ 5 := htors_le

end

end Work.ShafarevichKoch.H2Half
