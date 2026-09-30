import Mathlib
import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.SSKit
import Submission.Work.Pi6.EMM2.SerreKit
import Submission.Work.Pi6.EMODD.kOneIntegralHomology
import Submission.Work.Pi6.EMZ.bocksteinSES
import Submission.Work.Pi6.K2Z.homBockstein
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.Pi6.EMM2.K4Kit
import Submission.Work.Pi6.EMM2.k4forcing9

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-!
# Area EMM2 — the `K(ℤ/2,3)` forcing at threshold `9`

This file proves `Work.Pi6.EMM2.k3forcing9` : `K3Facts9Statement`.

The proof runs the Serre spectral sequence of the path–loop fibration `ΩX → PX → X` of a range
model `X` of `K(ℤ/2,3)` through `N ≥ 9`, over `𝔽₂ = ZMod 2`:

* the fibre `F = ΩX` is a range model of `K(ℤ/2,2)` through `N - 1`, and the total space is
  contractible, so every `E_∞`-term of positive total degree vanishes (`conv_zero`, `conv_dim`);
* the fibre's low-degree mod-2 cohomology is produced here from the twisting fibration
  `K(ℤ,2) → mpath r → F` of `KZModelLowStatement` (`K(ℤ,2)`-range-model facts from
  `K2FieldLowStatement` and from the two-row telescoping `kTwoDimSix`).

The dimension bookkeeping is done with `CohSS.finrank_row0_le` (and its sharpened form
`row0Refined`, which uses the source of each differential on its own page) together with the
non-vanishing of the `E_2`-product `x · y` for `x ∈ E_2^{s,0}`, `y ∈ E_2^{0,q}` (`e2RowColMulNeZero`).
-/

namespace Work.Pi6.EMM2

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

/-! ## Small module-theoretic helpers -/

/-- The unit of `H⁰(X;𝕜)` is nonzero when `H⁰(X;𝕜)` is one-dimensional. -/
theorem one_ne_zero_of_finrank_one {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X]
    (h0 : Module.finrank 𝕜 (Coh 𝕜 X 0) = 1) : one 𝕜 X ≠ 0 := by
  intro hone
  have h1 : ∀ a : Coh 𝕜 X 0, cup 𝕜 X 0 0 (one 𝕜 X) a = a := fun a => by
    show ((Work.Cohomology.cupH' 𝕜 (TopCat.toSSet.obj (TopCat.of X)) 0 0)
      (Work.Cohomology.oneH 𝕜 (TopCat.toSSet.obj (TopCat.of X)))) a = a
    exact Work.Cohomology.cupH'_one_left 𝕜 (TopCat.toSSet.obj (TopCat.of X)) 0 a
  have hsub : Subsingleton (Coh 𝕜 X 0) := ⟨fun a b => by
    rw [← h1 a, ← h1 b, hone]
    simp⟩
  have hfd : FiniteDimensional 𝕜 (Coh 𝕜 X 0) :=
    FiniteDimensional.of_finrank_pos (by rw [h0]; norm_num)
  rw [Module.finrank_zero_iff.mpr hsub] at h0
  omega

/-- A module of dimension `0` is a subsingleton. -/
theorem subsingleton_of_finrank_zero {𝕜 : Type} [Field 𝕜] {M : Type} [AddCommGroup M]
    [Module 𝕜 M] [FiniteDimensional 𝕜 M] (h : Module.finrank 𝕜 M = 0) : Subsingleton M :=
  Module.finrank_zero_iff.mp h

/-- A module of dimension one has a nonzero element. -/
theorem exists_ne_zero_of_finrank_one {𝕜 : Type} [Field 𝕜] {M : Type} [AddCommGroup M]
    [Module 𝕜 M] (h : Module.finrank 𝕜 M = 1) : ∃ x : M, x ≠ 0 := by
  by_contra hc
  push_neg at hc
  have hsub : Subsingleton M := ⟨fun a b => by rw [hc a, hc b]⟩
  have hfd : FiniteDimensional 𝕜 M := FiniteDimensional.of_finrank_pos (by rw [h]; norm_num)
  rw [Module.finrank_zero_iff.mpr hsub] at h
  omega

/-- The dimension of a zero module is zero. -/
theorem finrank_eq_zero_of_isZero {𝕜 : Type} [Field 𝕜] {M : Type} [AddCommGroup M] [Module 𝕜 M]
    (h : IsZero (ModuleCat.of 𝕜 M)) : Module.finrank 𝕜 M = 0 := by
  haveI : Subsingleton (ModuleCat.of 𝕜 M) := ModuleCat.subsingleton_of_isZero h
  exact Module.finrank_eq_zero_of_subsingleton 𝕜 M

/-- `IsZero` of a `𝕜`-module from `IsZero` of the underlying type. -/
theorem isZero_moduleCat_of_subsingleton {𝕜 : Type} [Field 𝕜] {M : Type} [AddCommGroup M]
    [Module 𝕜 M] [Subsingleton M] : IsZero (ModuleCat.of 𝕜 M) :=
  ModuleCat.isZero_of_subsingleton _

/-- `IsZero` of a singular cohomology group from a vanishing dimension. -/
theorem isZero_cohom_of_finrank_eq_zero {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X]
    {n : ℕ} [FiniteDimensional 𝕜 (Coh 𝕜 X n)] (h : Module.finrank 𝕜 (Coh 𝕜 X n) = 0) :
    IsZero (Coh 𝕜 X n) := by
  haveI : Subsingleton (Coh 𝕜 X n) := Module.finrank_zero_iff.mp h
  exact ModuleCat.isZero_of_subsingleton _

/-- The dimension of a vanishing cohomology group is zero. -/
theorem finrank_eq_zero_of_isZero_cohom {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X] {n : ℕ}
    (h : IsZero (Coh 𝕜 X n)) : Module.finrank 𝕜 (Coh 𝕜 X n) = 0 := by
  haveI : Subsingleton (Coh 𝕜 X n) := ModuleCat.subsingleton_of_isZero h
  exact Module.finrank_eq_zero_of_subsingleton 𝕜 (Coh 𝕜 X n)

/-- Monotonicity of `IsEMSpaceUpTo` in the range. -/
theorem isEMSpaceUpTo_mono {A : Type} [AddCommGroup A] {m : ℕ} (hm : 0 < m) {M M' : ℕ}
    {X : Type} [TopologicalSpace X] {x : X} (h : Work.Serre.IsEMSpaceUpTo A m hm M X x)
    (hM : M' ≤ M) : Work.Serre.IsEMSpaceUpTo A m hm M' X x :=
  ⟨h.1, fun i hi hc => h.2 i hi (hc.imp id (fun hle => le_trans hle hM))⟩

/-! ## The sharpened telescoped row-`0` bound -/

/-- **The telescoped dimension bound along the row `q = 0`, with the sources on their own pages.**
If `E_2^{a}` is finite dimensional for every `a` in the box `0 ≤ a.1, 0 ≤ a.2, a.1 + a.2 ≤ N`, then
`dim E_2^{n,0} ≤ dim E_{n+2}^{n,0} + ∑_{r<n} dim E_{r+2}^{sr n (r+2)}`, where `sr n (r+2)` is the
source bidegree `(n - r - 2, r + 1)` of the differential into `(n,0)` on page `r + 2`. -/
theorem row0Refined {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (S : CohSS 𝕜) (N : ℕ)
    (hbox : ∀ a : ℤ × ℤ, 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ (N : ℤ) →
      FiniteDimensional 𝕜 (S.E 2 a)) :
    ∀ n ≤ N, Module.finrank 𝕜 (S.E 2 ((n : ℤ), 0)) ≤
      Module.finrank 𝕜 (S.E (n + 2) ((n : ℤ), 0)) +
        ∑ r ∈ Finset.range n, Module.finrank 𝕜 (S.E (r + 2) (CohSS.sr n (r + 2))) := by
  intro n hn
  have hfd := S.finiteDimensional_E N hbox
  have hfd' : ∀ k : ℕ, FiniteDimensional 𝕜 (S.E (k + 2) (CohSS.sr n (k + 2))) := by
    intro k
    by_cases h1 : 0 ≤ (CohSS.sr n (k + 2)).1
    · by_cases h2 : 0 ≤ (CohSS.sr n (k + 2)).2
      · exact hfd k _ h1 h2 (by
          simp only [CohSS.sr, Prod.fst_sub, Prod.snd_sub, Prod.fst_ofNat, Prod.snd_ofNat]
          omega)
      · exact S.finiteDimensional_of_neg (Or.inr (by omega))
    · exact S.finiteDimensional_of_neg (Or.inl (by omega))
  have hstep : ∀ k : ℕ, Module.finrank 𝕜 (S.E (k + 2) ((n : ℤ), 0)) ≤
      Module.finrank 𝕜 (S.E (k + 3) ((n : ℤ), 0)) +
        Module.finrank 𝕜 (S.E (k + 2) (CohSS.sr n (k + 2))) := by
    intro k
    have hout : IsZero (S.E (k + 2) (((n : ℤ), (0 : ℤ)) + vr (k + 2))) := by
      refine S.isZero_quad (k + 2) _ (Or.inr ?_)
      simp only [vr, Prod.snd_add, Prod.snd_ofNat]
      omega
    have hfin1 : FiniteDimensional 𝕜 (S.E (k + 2) ((n : ℤ), 0)) :=
      hfd k _ (by simp) (by simp) (by simp; omega)
    have hfin2' : FiniteDimensional 𝕜 (S.E (k + 2) (((n : ℤ), (0 : ℤ)) - vr (k + 2))) := by
      rw [CohSS.src_row0_eq n (k + 2)]
      exact hfd' k
    have hmain := S.finrank_le_next (r := k + 2) (by omega) (((n : ℤ), (0 : ℤ))) hfin1 hfin2' hout
    rw [CohSS.src_row0_eq] at hmain
    exact hmain
  have key : ∀ k : ℕ, Module.finrank 𝕜 (S.E 2 ((n : ℤ), 0)) ≤
      Module.finrank 𝕜 (S.E (k + 2) ((n : ℤ), 0)) +
        ∑ r ∈ Finset.range k, Module.finrank 𝕜 (S.E (r + 2) (CohSS.sr n (r + 2))) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hs := hstep k
        have hsum : ∑ r ∈ Finset.range (k + 1), Module.finrank 𝕜 (S.E (r + 2) (CohSS.sr n (r + 2))) =
            (∑ r ∈ Finset.range k, Module.finrank 𝕜 (S.E (r + 2) (CohSS.sr n (r + 2)))) +
              Module.finrank 𝕜 (S.E (k + 2) (CohSS.sr n (k + 2))) := Finset.sum_range_succ _ _
        have hidx : Module.finrank 𝕜 (S.E (k + 3) ((n : ℤ), 0)) =
            Module.finrank 𝕜 (S.E (k + 1 + 2) ((n : ℤ), 0)) := by norm_num
        rw [hidx] at hs
        rw [hsum]
        omega
  exact key n




/-! ## Interlude: the mod-`2` cohomology of a range model of `K(ℤ,1)` -/

/-- A linear equivalence underlying an isomorphism in `ModuleCat R`. -/
def linearEquivOfIso {R : Type} [Ring R] {A B : ModuleCat R} (e : A ≅ B) : ↥A ≃ₗ[R] ↥B where
  toFun := e.hom
  map_add' := (e.hom.hom).map_add
  map_smul' := (e.hom.hom).map_smul
  invFun := e.inv
  left_inv := fun x => by
    have h2 := congrArg (fun f : A ⟶ A => (ConcreteCategory.hom f) x) e.hom_inv_id
    simpa using h2
  right_inv := fun y => by
    have h2 := congrArg (fun f : B ⟶ B => (ConcreteCategory.hom f) y) e.inv_hom_id
    simpa using h2

/-- An additive equivalence between `ZMod p`-modules is `ZMod p`-linear. -/
def linearEquivOfAddEquiv (p : ℕ) {M N : Type} [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] (e : M ≃+ N) : M ≃ₗ[ZMod p] N where
  toFun := e
  map_add' := e.map_add
  map_smul' := fun c x => by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    simp only [Int.cast_smul_eq_zsmul (ZMod p) n, RingHom.id_apply]
    exact map_zsmul (e : M →+ N) n x
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv

/-- `H₀(X;R) ≅ R` for a path-connected space `X` (the augmentation). -/
theorem hZeroIso (R : Type) [CommRing R] (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : Nonempty (HR R X 0 ≅ ModuleCat.of R R) := by
  haveI hpc : PathConnectedSpace (TopCat.of X) := ‹PathConnectedSpace X›
  have hε : IsIso (TopCat.singularHomology₀ε (C := ModuleCat R) (TopCat.of X)
      (ModuleCat.of R R)) := inferInstance
  exact ⟨@asIso (ModuleCat R) _ (HR R X 0) (ModuleCat.of R R)
    (TopCat.singularHomology₀ε (C := ModuleCat R) (TopCat.of X) (ModuleCat.of R R)) hε⟩

/-- The `2`-torsion of a group isomorphic to `ℤ` is trivial. -/
theorem subsingleton_torsP_two_of_addEquiv_int {M : Type} [AddCommGroup M] (e : M ≃+ ℤ) :
    Subsingleton ↥(Work.Pi6.EMZ.torsP 2 M) := by
  have key : ∀ a : ↥(Work.Pi6.EMZ.torsP 2 M), (a : M) = 0 := by
    intro a
    have h1 : (2 : ℤ) • ((a : ↥(Work.Pi6.EMZ.torsP 2 M)) : M) = 0 :=
      Work.Pi6.EMZ.mem_torsP.mp a.2
    have h2 : (2 : ℤ) • e (a : M) = 0 := by rw [← map_zsmul, h1, map_zero]
    have h3 : (2 : ℤ) * e (a : M) = 0 := by simpa [zsmul_eq_mul] using h2
    have h4 : e (a : M) = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · norm_num at h
      · exact h
    exact e.injective (by rw [h4, map_zero])
  exact ⟨fun a b => Subtype.ext (by rw [key a, key b])⟩

/-- The `2`-torsion of a zero module is trivial. -/
theorem subsingleton_torsP_two_of_isZero {M : ModuleCat ℤ} (h : IsZero M) :
    Subsingleton ↥(Work.Pi6.EMZ.torsP 2 ↥M) := by
  haveI : Subsingleton ↥M := ModuleCat.subsingleton_of_isZero h
  exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩

/-- A quotient of a zero module is zero. -/
theorem subsingleton_quot_pH_two_of_isZero {M : ModuleCat ℤ} (h : IsZero M) :
    Subsingleton (↥M ⧸ Work.Pi6.EMZ.pH 2 ↥M) := by
  haveI : Subsingleton ↥M := ModuleCat.subsingleton_of_isZero h
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (Work.Pi6.EMZ.pH 2 ↥M) a
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (Work.Pi6.EMZ.pH 2 ↥M) b
  rw [Subsingleton.elim x y]

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- **The mod-`2` cohomology is the mod-`2` dual of the mod-`2` homology.** -/
theorem cohDualTwo (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    Nonempty (Coh (ZMod 2) Y n ≅
      ModuleCat.of (ZMod 2) (↥(HR (ZMod 2) Y n) →ₗ[ZMod 2] ZMod 2)) := by
  have hb := Work.Cohomology.kronH_bijective_field (ZMod 2)
    (TopCat.toSSet.obj (TopCat.of Y)) n
  exact ⟨LinearEquiv.toModuleIso (LinearEquiv.ofBijective (Work.Cohomology.kronH (ZMod 2)
    (TopCat.toSSet.obj (TopCat.of Y)) n) hb)⟩

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- The dimension of the mod-`2` cohomology equals that of the mod-`2` homology. -/
theorem coh_finrank_eq_hr (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    Module.finrank (ZMod 2) (Coh (ZMod 2) Y n) =
      Module.finrank (ZMod 2) (HR (ZMod 2) Y n) := by
  obtain ⟨d⟩ := cohDualTwo Y n
  rw [LinearEquiv.finrank_eq (linearEquivOfIso d), Subspace.dual_finrank_eq]

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- A vanishing mod-`2` homology group has vanishing mod-`2` cohomology. -/
theorem coh_isZero_of_hr_isZero (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (h : IsZero (HR (ZMod 2) Y n)) : IsZero (Coh (ZMod 2) Y n) := by
  obtain ⟨d⟩ := cohDualTwo Y n
  haveI : Subsingleton ↥(HR (ZMod 2) Y n) := ModuleCat.subsingleton_of_isZero h
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of (ZMod 2) (↥(HR (ZMod 2) Y n) →ₗ[ZMod 2] ZMod 2))) d

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- **The mod-`2` cohomology of a range model of `K(ℤ,1)`**: `H⁰ = H¹ = 𝔽₂` and `H^q = 0` for
`2 ≤ q ≤ N`. -/
theorem kOneModTwo (N : ℕ) (hN : 1 ≤ N) (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (hY : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) N Y y₀) :
    Module.finrank (ZMod 2) (Coh (ZMod 2) Y 0) = 1 ∧
      Module.finrank (ZMod 2) (Coh (ZMod 2) Y 1) = 1 ∧
      (∀ q : ℕ, 2 ≤ q → q ≤ N → IsZero (Coh (ZMod 2) Y q)) := by
  classical
  have hpc : PathConnectedSpace Y :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero y₀
      (hY.2 0 (by norm_num) (Or.inl (by norm_num)))
  haveI := hpc
  have hZ := Work.Pi6.EMODD.kOneIntegralHomology N Y y₀ hY
  obtain ⟨eI0⟩ := hZ.1 0 (by norm_num) (by omega)
  obtain ⟨eI1⟩ := hZ.1 1 (by norm_num) hN
  have hH0 : Nonempty (HR (ZMod 2) Y 0 ≅ ModuleCat.of (ZMod 2) (ZMod 2)) := hZeroIso (ZMod 2) Y
  have hH1 : Nonempty (HR (ZMod 2) Y 1 ≅ ModuleCat.of (ZMod 2) (ZMod 2)) := by
    obtain ⟨f, g, hf, hg, hex, -⟩ := Work.Pi6.EMZ.bocksteinSES 2 Nat.prime_two
      (Work.Pi6.K2Z.homBockstein 2 Nat.prime_two) Y 0
    haveI : Subsingleton ↥(Work.Pi6.EMZ.torsP 2 (HR ℤ Y 0)) :=
      subsingleton_torsP_two_of_addEquiv_int
        ((linearEquivOfIso (eI0 : HR ℤ Y 0 ≅ ModuleCat.of ℤ ℤ)).toAddEquiv)
    have hg0 : ∀ x : HR (ZMod 2) Y (0 + 1), g x = 0 := fun x => Subsingleton.elim _ _
    have hfsurj : Function.Surjective ⇑f := fun y => (hex y).mp (hg0 y)
    let e1 : HR (ZMod 2) Y (0 + 1) ≃+
        (HR ℤ Y (0 + 1) ⧸ Work.Pi6.EMZ.pH 2 (HR ℤ Y (0 + 1))) :=
      (AddEquiv.ofBijective f ⟨hf, hfsurj⟩).symm
    let φ : HR ℤ Y (0 + 1) →+ ZMod 2 :=
      { toFun := fun x => (((linearEquivOfIso eI1) x : ℤ) : ZMod 2)
        map_zero' := by show ((((linearEquivOfIso eI1) 0 : ℤ)) : ZMod 2) = 0; simp
        map_add' := by
          intro a b
          show ((((linearEquivOfIso eI1) (a + b) : ℤ)) : ZMod 2) =
            ((((linearEquivOfIso eI1) a : ℤ)) : ZMod 2) + ((((linearEquivOfIso eI1) b : ℤ)) : ZMod 2)
          rw [map_add]
          push_cast
          rfl }
    have hφsurj : Function.Surjective ⇑φ := by
      intro c
      obtain ⟨n, hn⟩ := ZMod.intCast_surjective c
      refine ⟨(linearEquivOfIso eI1).symm n, ?_⟩
      show ((((linearEquivOfIso eI1) ((linearEquivOfIso eI1).symm n) : ℤ)) : ZMod 2) = c
      rw [LinearEquiv.apply_symm_apply]
      exact hn
    have hφker : φ.ker = Work.Pi6.EMZ.pH 2 (HR ℤ Y (0 + 1)) := by
      ext x
      rw [AddMonoidHom.mem_ker, Work.Pi6.EMZ.mem_pH']
      constructor
      · intro hx
        have hx' : ((((linearEquivOfIso eI1) x : ℤ)) : ZMod 2) = 0 := hx
        obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hx'
        refine ⟨(linearEquivOfIso eI1).symm k, ?_⟩
        have hk' : (linearEquivOfIso eI1) x = k + k := by rw [hk]; ring
        rw [two_nsmul, ← map_add]
        rw [show k + k = (linearEquivOfIso eI1) x from hk'.symm, LinearEquiv.symm_apply_apply]
      · rintro ⟨y, hy⟩
        have h1 : (linearEquivOfIso eI1) x
            = (linearEquivOfIso eI1) y + (linearEquivOfIso eI1) y := by
          rw [← hy, two_nsmul, map_add]
        show ((((linearEquivOfIso eI1) x : ℤ)) : ZMod 2) = 0
        rw [h1]
        push_cast
        rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2) 2,
          show (((2 : ℕ)) : ZMod 2) = 0 from by decide, zero_smul]
    have e2' : (HR ℤ Y (0 + 1) ⧸ φ.ker) ≃+ ZMod 2 :=
      QuotientAddGroup.quotientKerEquivOfSurjective φ hφsurj
    have e2 : (HR ℤ Y (0 + 1) ⧸ Work.Pi6.EMZ.pH 2 (HR ℤ Y (0 + 1))) ≃+ ZMod 2 :=
      hφker ▸ e2'
    exact ⟨LinearEquiv.toModuleIso (linearEquivOfAddEquiv 2 (e1.trans e2))⟩
  have hHq : ∀ q : ℕ, 2 ≤ q → q ≤ N → IsZero (HR (ZMod 2) Y q) := by
    intro q hq2 hqN
    obtain ⟨f, g, hf, hg, hex, -⟩ := Work.Pi6.EMZ.bocksteinSES 2 Nat.prime_two
      (Work.Pi6.K2Z.homBockstein 2 Nat.prime_two) Y (q - 1)
    have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
    have hmain : IsZero (HR (ZMod 2) Y (q - 1 + 1)) := by
      have hz : IsZero (HR ℤ Y (q - 1 + 1)) := hq1.symm ▸ (hZ.2 q hq2 hqN)
      haveI hsubq : Subsingleton (HR ℤ Y (q - 1 + 1) ⧸
          Work.Pi6.EMZ.pH 2 (HR ℤ Y (q - 1 + 1))) :=
        subsingleton_quot_pH_two_of_isZero hz
      have hf0 : f = 0 := AddMonoidHom.ext fun x => by
        rw [show x = 0 from Subsingleton.elim x 0]
        exact map_zero f
      haveI hsub : Subsingleton ↥(Work.Pi6.EMZ.torsP 2 (HR ℤ Y (q - 1))) := by
        rcases Nat.lt_or_ge (q - 1) 2 with h | h
        · have hq2' : q = 2 := by omega
          subst hq2'
          exact subsingleton_torsP_two_of_addEquiv_int
            ((linearEquivOfIso eI1).toAddEquiv)
        · have hle : q - 1 ≤ N := by omega
          exact subsingleton_torsP_two_of_isZero (hZ.2 (q - 1) h hle)
      have hg0 : ∀ x : HR (ZMod 2) Y (q - 1 + 1), g x = 0 := fun x => Subsingleton.elim _ _
      have hzero : ∀ x : HR (ZMod 2) Y (q - 1 + 1), x = 0 := by
        intro x
        have hx : x ∈ AddMonoidHom.range f := (hex x).mp (hg0 x)
        rw [hf0, AddMonoidHom.range_zero, AddSubgroup.mem_bot] at hx
        exact hx
      haveI : Subsingleton (HR (ZMod 2) Y (q - 1 + 1)) := ⟨fun x y => by rw [hzero x, hzero y]⟩
      exact ModuleCat.isZero_of_subsingleton _
    rwa [hq1] at hmain
  refine ⟨?_, ?_, ?_⟩
  · rw [coh_finrank_eq_hr]
    exact (LinearEquiv.finrank_eq (linearEquivOfIso hH0.some)).trans (by simp)
  · rw [coh_finrank_eq_hr]
    exact (LinearEquiv.finrank_eq (linearEquivOfIso hH1.some)).trans (by simp)
  · exact fun q hq2 hqN => coh_isZero_of_hr_isZero Y q (hHq q hq2 hqN)


/-! ## The non-vanishing of the `E_2`-product of a row-`0` and a column-`0` class -/

/-- In a one-dimensional `𝕜`-module every element is a multiple of a fixed nonzero vector. -/
theorem smul_surjective_of_finrank_one {𝕜 : Type} [Field 𝕜] {V : Type} [AddCommGroup V]
    [Module 𝕜 V] (h : Module.finrank 𝕜 V = 1) (v : V) (hv : v ≠ 0) :
    ∀ w : V, ∃ k : 𝕜, w = k • v := by
  haveI : FiniteDimensional 𝕜 V :=
    FiniteDimensional.of_finrank_pos (by rw [h]; norm_num)
  have hspan : Submodule.span 𝕜 ({v} : Set V) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_singleton hv, h]
  intro w
  have hw : w ∈ Submodule.span 𝕜 ({v} : Set V) := by rw [hspan]; trivial
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hw
  exact ⟨k, hk.symm⟩

/-- If `H⁰(F;𝕜)` is one-dimensional then every element of `A ⊗ H⁰(F;𝕜)` is `u ⊗ 1`. -/
theorem tensor_decomp_right {𝕜 : Type} [Field 𝕜] {A F : Type} [AddCommGroup A] [Module 𝕜 A]
    [TopologicalSpace F] (h0 : Module.finrank 𝕜 (Coh 𝕜 F 0) = 1)
    (z : A ⊗[𝕜] Coh 𝕜 F 0) : ∃ u : A, z = u ⊗ₜ[𝕜] one 𝕜 F := by
  have hone : one 𝕜 F ≠ 0 := one_ne_zero_of_finrank_one h0
  have hspan : ∀ b : Coh 𝕜 F 0, ∃ k : 𝕜, b = k • one 𝕜 F :=
    smul_surjective_of_finrank_one h0 (one 𝕜 F) hone
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a b =>
      obtain ⟨k, hk⟩ := hspan b
      refine ⟨k • a, ?_⟩
      show a ⊗ₜ[𝕜] b = (k • a) ⊗ₜ[𝕜] one 𝕜 F
      rw [hk, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add z w hz hw =>
      obtain ⟨u, hu⟩ := hz
      obtain ⟨v, hv⟩ := hw
      exact ⟨u + v, by rw [hu, hv, TensorProduct.add_tmul]⟩

/-- If `H⁰(B;𝕜)` is one-dimensional then every element of `H⁰(B;𝕜) ⊗ C` is `1 ⊗ v`. -/
theorem tensor_decomp_left {𝕜 : Type} [Field 𝕜] {B C : Type} [TopologicalSpace B]
    [AddCommGroup C] [Module 𝕜 C] (h0 : Module.finrank 𝕜 (Coh 𝕜 B 0) = 1)
    (z : Coh 𝕜 B 0 ⊗[𝕜] C) : ∃ v : C, z = one 𝕜 B ⊗ₜ[𝕜] v := by
  have hone : one 𝕜 B ≠ 0 := one_ne_zero_of_finrank_one h0
  have hspan : ∀ b : Coh 𝕜 B 0, ∃ k : 𝕜, b = k • one 𝕜 B :=
    smul_surjective_of_finrank_one h0 (one 𝕜 B) hone
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul b c =>
      obtain ⟨k, hk⟩ := hspan b
      refine ⟨k • c, ?_⟩
      show b ⊗ₜ[𝕜] c = one 𝕜 B ⊗ₜ[𝕜] (k • c)
      rw [hk, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add z w hz hw =>
      obtain ⟨u, hu⟩ := hz
      obtain ⟨v, hv⟩ := hw
      exact ⟨u + v, by rw [hu, hv, TensorProduct.tmul_add]⟩

/-- **The `E_2`-product of a row-`0` and a column-`0` class is nonzero**, fibre degree `3`. -/
theorem e2RowColMulNeZero3 {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hS : IsSerreMSS S p e₀ N) (hco : Work.Pi6.EMM2.CupOneStatement)
    (hB0 : Module.finrank 𝕜 (Coh 𝕜 B 0) = 1)
    (hF0 : Module.finrank 𝕜 (Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 0) = 1)
    {s : ℕ} (hs : s ≤ N) (hq : 3 ≤ N)
    (x : S.E 2 ((s : ℤ), 0)) (y : S.E 2 ((0 : ℤ), (3 : ℤ))) (hx : x ≠ 0) (hy : y ≠ 0) :
    S.mul 2 ((s : ℤ), 0) ((0 : ℤ), (3 : ℤ)) ((s : ℤ), (3 : ℤ)) (by ext <;> simp) x y ≠ 0 := by
  classical
  obtain ⟨e2, hmul, -⟩ := hS
  obtain ⟨u, hu⟩ := tensor_decomp_right (F := Work.StemsB.fibre p (p e₀)) hF0
    ((e2 s 0 hs (by omega)).hom x)
  obtain ⟨v, hv⟩ := tensor_decomp_left (B := B) hB0 ((e2 0 3 (by omega) hq).hom y)
  have hu' : x = (e2 s 0 hs (by omega)).inv.hom (u ⊗ₜ[𝕜] one 𝕜 (Work.StemsB.fibre p (p e₀))) := by
    rw [← hu]
    exact ((linearEquivOfIso (e2 s 0 hs (by omega))).symm_apply_apply x).symm
  have hv' : y = (e2 0 3 (by omega) hq).inv.hom (one 𝕜 B ⊗ₜ[𝕜] v) := by
    rw [← hv]
    exact ((linearEquivOfIso (e2 0 3 (by omega) hq)).symm_apply_apply y).symm
  have hu0 : u ≠ 0 := by
    intro h0u
    exact hx (by rw [hu', h0u, TensorProduct.zero_tmul, map_zero])
  have hv0 : v ≠ 0 := by
    intro h0v
    exact hy (by rw [hv', h0v, TensorProduct.tmul_zero, map_zero])
  have key := hmul s 0 0 3 u (one 𝕜 (Work.StemsB.fibre p (p e₀))) (one 𝕜 B) v
    (by omega) (by omega)
  have hcB : cup 𝕜 B s 0 u (one 𝕜 B) = u := (hco 𝕜 s u).2
  have hcF : cup 𝕜 (Work.StemsB.fibre p (p e₀)) 0 3 (one 𝕜 (Work.StemsB.fibre p (p e₀))) v = v := by
    simpa using (hco 𝕜 3 v).1
  rw [hcB, hcF] at key
  rw [← hu', ← hv'] at key
  rw [show (-1 : 𝕜) ^ (0 * 0) = 1 from by norm_num, one_smul] at key
  change S.mul 2 (((s : ℕ) : ℤ), ((0 : ℕ) : ℤ)) (((0 : ℕ) : ℤ), ((3 : ℕ) : ℤ))
    ((((s + 0 : ℕ) : ℤ)), (((0 + 3 : ℕ) : ℤ))) (by ext <;> simp) x y ≠ 0
  rw [key]
  intro hzero
  have h2 : u ⊗ₜ[𝕜] v = 0 := by
    have h4 : (linearEquivOfIso (e2 s 3 hs hq)).symm (u ⊗ₜ[𝕜] v) = 0 := hzero
    exact (linearEquivOfIso (e2 s 3 hs hq)).symm.injective (by rw [h4, map_zero])
  exact tmul_ne_zero_of_ne_zero hu0 hv0 h2

/-- **The `E_2`-product of a row-`0` and a column-`0` class is nonzero**, fibre degree `2`. -/
theorem e2RowColMulNeZero2 {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hS : IsSerreMSS S p e₀ N) (hco : Work.Pi6.EMM2.CupOneStatement)
    (hB0 : Module.finrank 𝕜 (Coh 𝕜 B 0) = 1)
    (hF0 : Module.finrank 𝕜 (Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 0) = 1)
    {s : ℕ} (hs : s ≤ N) (hq : 2 ≤ N)
    (x : S.E 2 ((s : ℤ), 0)) (y : S.E 2 ((0 : ℤ), (2 : ℤ))) (hx : x ≠ 0) (hy : y ≠ 0) :
    S.mul 2 ((s : ℤ), 0) ((0 : ℤ), (2 : ℤ)) ((s : ℤ), (2 : ℤ)) (by ext <;> simp) x y ≠ 0 := by
  classical
  obtain ⟨e2, hmul, -⟩ := hS
  obtain ⟨u, hu⟩ := tensor_decomp_right (F := Work.StemsB.fibre p (p e₀)) hF0
    ((e2 s 0 hs (by omega)).hom x)
  obtain ⟨v, hv⟩ := tensor_decomp_left (B := B) hB0 ((e2 0 2 (by omega) hq).hom y)
  have hu' : x = (e2 s 0 hs (by omega)).inv.hom (u ⊗ₜ[𝕜] one 𝕜 (Work.StemsB.fibre p (p e₀))) := by
    rw [← hu]
    exact ((linearEquivOfIso (e2 s 0 hs (by omega))).symm_apply_apply x).symm
  have hv' : y = (e2 0 2 (by omega) hq).inv.hom (one 𝕜 B ⊗ₜ[𝕜] v) := by
    rw [← hv]
    exact ((linearEquivOfIso (e2 0 2 (by omega) hq)).symm_apply_apply y).symm
  have hu0 : u ≠ 0 := by
    intro h0u
    exact hx (by rw [hu', h0u, TensorProduct.zero_tmul, map_zero])
  have hv0 : v ≠ 0 := by
    intro h0v
    exact hy (by rw [hv', h0v, TensorProduct.tmul_zero, map_zero])
  have key := hmul s 0 0 2 u (one 𝕜 (Work.StemsB.fibre p (p e₀))) (one 𝕜 B) v
    (by omega) (by omega)
  have hcB : cup 𝕜 B s 0 u (one 𝕜 B) = u := (hco 𝕜 s u).2
  have hcF : cup 𝕜 (Work.StemsB.fibre p (p e₀)) 0 2 (one 𝕜 (Work.StemsB.fibre p (p e₀))) v = v := by
    simpa using (hco 𝕜 2 v).1
  rw [hcB, hcF] at key
  rw [← hu', ← hv'] at key
  rw [show (-1 : 𝕜) ^ (0 * 0) = 1 from by norm_num, one_smul] at key
  change S.mul 2 (((s : ℕ) : ℤ), ((0 : ℕ) : ℤ)) (((0 : ℕ) : ℤ), ((2 : ℕ) : ℤ))
    ((((s + 0 : ℕ) : ℤ)), (((0 + 2 : ℕ) : ℤ))) (by ext <;> simp) x y ≠ 0
  rw [key]
  intro hzero
  have h2 : u ⊗ₜ[𝕜] v = 0 := by
    have h4 : (linearEquivOfIso (e2 s 2 hs hq)).symm (u ⊗ₜ[𝕜] v) = 0 := hzero
    exact (linearEquivOfIso (e2 s 2 hs hq)).symm.injective (by rw [h4, map_zero])
  exact tmul_ne_zero_of_ne_zero hu0 hv0 h2

/-- **The `E_2`-product of a row-`0` and a column-`0` class is nonzero**, fibre degree `4`. -/
theorem e2RowColMulNeZero4 {𝕜 : Type} [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (S : CohSS 𝕜) (p : C(E, B)) (e₀ : E) (N : ℕ)
    (hS : IsSerreMSS S p e₀ N) (hco : Work.Pi6.EMM2.CupOneStatement)
    (hB0 : Module.finrank 𝕜 (Coh 𝕜 B 0) = 1)
    (hF0 : Module.finrank 𝕜 (Coh 𝕜 (Work.StemsB.fibre p (p e₀)) 0) = 1)
    {s : ℕ} (hs : s ≤ N) (hq : 4 ≤ N)
    (x : S.E 2 ((s : ℤ), 0)) (y : S.E 2 ((0 : ℤ), (4 : ℤ))) (hx : x ≠ 0) (hy : y ≠ 0) :
    S.mul 2 ((s : ℤ), 0) ((0 : ℤ), (4 : ℤ)) ((s : ℤ), (4 : ℤ)) (by ext <;> simp) x y ≠ 0 := by
  classical
  obtain ⟨e2, hmul, -⟩ := hS
  obtain ⟨u, hu⟩ := tensor_decomp_right (F := Work.StemsB.fibre p (p e₀)) hF0
    ((e2 s 0 hs (by omega)).hom x)
  obtain ⟨v, hv⟩ := tensor_decomp_left (B := B) hB0 ((e2 0 4 (by omega) hq).hom y)
  have hu' : x = (e2 s 0 hs (by omega)).inv.hom (u ⊗ₜ[𝕜] one 𝕜 (Work.StemsB.fibre p (p e₀))) := by
    rw [← hu]
    exact ((linearEquivOfIso (e2 s 0 hs (by omega))).symm_apply_apply x).symm
  have hv' : y = (e2 0 4 (by omega) hq).inv.hom (one 𝕜 B ⊗ₜ[𝕜] v) := by
    rw [← hv]
    exact ((linearEquivOfIso (e2 0 4 (by omega) hq)).symm_apply_apply y).symm
  have hu0 : u ≠ 0 := by
    intro h0u
    exact hx (by rw [hu', h0u, TensorProduct.zero_tmul, map_zero])
  have hv0 : v ≠ 0 := by
    intro h0v
    exact hy (by rw [hv', h0v, TensorProduct.tmul_zero, map_zero])
  have key := hmul s 0 0 4 u (one 𝕜 (Work.StemsB.fibre p (p e₀))) (one 𝕜 B) v
    (by omega) (by omega)
  have hcB : cup 𝕜 B s 0 u (one 𝕜 B) = u := (hco 𝕜 s u).2
  have hcF : cup 𝕜 (Work.StemsB.fibre p (p e₀)) 0 4 (one 𝕜 (Work.StemsB.fibre p (p e₀))) v = v := by
    simpa using (hco 𝕜 4 v).1
  rw [hcB, hcF] at key
  rw [← hu', ← hv'] at key
  rw [show (-1 : 𝕜) ^ (0 * 0) = 1 from by norm_num, one_smul] at key
  change S.mul 2 (((s : ℕ) : ℤ), ((0 : ℕ) : ℤ)) (((0 : ℕ) : ℤ), ((4 : ℕ) : ℤ))
    ((((s + 0 : ℕ) : ℤ)), (((0 + 4 : ℕ) : ℤ))) (by ext <;> simp) x y ≠ 0
  rw [key]
  intro hzero
  have h2 : u ⊗ₜ[𝕜] v = 0 := by
    have h4 : (linearEquivOfIso (e2 s 4 hs hq)).symm (u ⊗ₜ[𝕜] v) = 0 := hzero
    exact (linearEquivOfIso (e2 s 4 hs hq)).symm.injective (by rw [h4, map_zero])
  exact tmul_ne_zero_of_ne_zero hu0 hv0 h2

/-! ## The two-row telescoping for `K(ℤ,2)` range models -/

/-- A vanishing module is finite dimensional. -/
theorem finiteDimensional_of_subsingleton_module {𝕜 : Type} [Field 𝕜] {M : Type} [AddCommGroup M]
    [Module 𝕜 M] [Subsingleton M] : FiniteDimensional 𝕜 M :=
  FiniteDimensional.of_surjective (0 : 𝕜 →ₗ[𝕜] M) (fun y => ⟨0, Subsingleton.elim _ _⟩)

/-- **The two-row telescoping for a `K(ℤ,2)` range model**: if `W` is a `K(ℤ,2)` model through `M`
then the mod-`2` cohomology of `W` vanishes in degrees `3` and `5` and is at most one-dimensional in
degree `6`.  The path–loop fibration of `W` has a `K(ℤ,1)` fibre (`hOne`), whose cohomology is
`𝔽₂, 𝔽₂, 0, …`; the total space is contractible, so the row-`0` telescoping bound
(`Work.Pi6.EMM2.finrank_row0_bound`) gives `dim Hⁿ(W) ≤ dim Hⁿ⁻²(W)`. -/
theorem kTwoDimSix (hM : Work.Pi6.MSSHolds) (hPF : Work.Pi6.EMM2.PathFibStatement)
    (hft : Work.Pi6.EMM2.FiniteTypeStatement) (hLD : Work.Pi6.EMM2.LowDegreeStatement)
    (hOne : ∀ (N : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y),
      Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) N Y y₀ →
      Module.finrank (ZMod 2) (Coh (ZMod 2) Y 0) = 1 ∧
      Module.finrank (ZMod 2) (Coh (ZMod 2) Y 1) = 1 ∧
      (∀ q : ℕ, 2 ≤ q → q ≤ N → IsZero (Coh (ZMod 2) Y q)))
    {W : Type} [TopologicalSpace W] (w₀ : W) {M : ℕ} (hM7 : 7 ≤ M)
    (hW : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) M W w₀)
    (h4 : Module.finrank (ZMod 2) (Coh (ZMod 2) W 4) ≤ 1) :
    Module.finrank (ZMod 2) (Coh (ZMod 2) W 6) ≤ 1 ∧
      IsZero (Coh (ZMod 2) W 3) ∧ IsZero (Coh (ZMod 2) W 5) := by
  classical
  have hM1 : 1 ≤ M := by omega
  have hZfin : Module.Finite ℤ ℤ := inferInstance
  obtain ⟨hcontr, hfib, hΩ⟩ := hPF (A := ℤ) (m := 2) (by norm_num) (M := M) w₀ hW
  -- the fibre of the path fibration is a `K(ℤ,1)` model through `M - 1`
  have hOdd : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) (M - 1)
      (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀)) w₀)
      (Work.StemsB.fibrePoint (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀))
        (Work.Serre.mpathOf (ContinuousMap.const PUnit w₀) PUnit.unit)) := hΩ
  obtain ⟨hF0, hF1, hFq⟩ := hOne (M - 1) _ _ hOdd
  -- low-degree facts for the base
  have hB1 : IsZero (Coh (ZMod 2) W 1) := (hLD (ZMod 2) (A := ℤ) hZfin (m := 2)
    (by norm_num) (M := M) (by omega) w₀ hW).2.2 1 (by norm_num) (by norm_num)
  have hB0 : Module.finrank (ZMod 2) (Coh (ZMod 2) W 0) = 1 :=
    (hLD (ZMod 2) (A := ℤ) hZfin (m := 2) (by norm_num) (M := M) (by omega) w₀ hW).2.1
  -- finiteness
  have hfinF : ∀ q : ℕ, q ≤ M - 1 → FiniteDimensional (ZMod 2)
      (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀)) w₀) q) := by
    intro q hq
    by_cases hq0 : q = 0
    · subst hq0
      exact FiniteDimensional.of_finrank_pos (by rw [hF0]; norm_num)
    by_cases hq1 : q = 1
    · subst hq1
      exact FiniteDimensional.of_finrank_pos (by rw [hF1]; norm_num)
    · have hq2 : 2 ≤ q := by omega
      haveI : Subsingleton (Coh (ZMod 2)
          (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀)) w₀) q) :=
        ModuleCat.subsingleton_of_isZero (hFq q hq2 hq)
      exact finiteDimensional_of_subsingleton_module
  have hfinB : ∀ s : ℕ, s ≤ M - 1 → FiniteDimensional (ZMod 2) (Coh (ZMod 2) W s) := by
    intro s hs
    have hW' : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) (M - 1 + 1) W w₀ := by
      rw [Nat.sub_add_cancel hM1]
      exact hW
    exact hft (ZMod 2) (A := ℤ) hZfin (m := 2) (by norm_num) (N := M - 1) w₀ hW' s hs
  -- the spectral sequence of the path fibration
  obtain ⟨S, hS⟩ := hM (ZMod 2) (Work.Serre.mpath (ContinuousMap.const PUnit w₀)) W
    (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀))
    (Work.Serre.mpathOf (ContinuousMap.const PUnit w₀) PUnit.unit) (M - 1) hfib
    (hLD (ZMod 2) (A := ℤ) hZfin (m := 2) (by norm_num) (M := M) (by omega) w₀ hW).1
    hfinF hfinB
  -- the total space is contractible
  have htot : ∀ n : ℕ, 1 ≤ n → CategoryTheory.Limits.IsZero
      (Coh (ZMod 2) (Work.Serre.mpath (ContinuousMap.const PUnit w₀)) n) := by
    intro n hn
    haveI : ContractibleSpace (Work.Serre.mpath (ContinuousMap.const PUnit w₀)) := hcontr
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact Work.Cohomology.contractible (ZMod 2) (TopCat.of (Work.Serre.mpath
      (ContinuousMap.const PUnit w₀))) n'
  -- the telescoping bounds
  have key : ∀ n : ℕ, 1 ≤ n → n ≤ M - 1 → Module.finrank (ZMod 2) (Coh (ZMod 2) W n) ≤
      ∑ r ∈ Finset.range (n - 1), Module.finrank (ZMod 2) (Coh (ZMod 2) W (n - (r + 2))) *
        Module.finrank (ZMod 2)
          (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀)) w₀) (r + 1)) := by
    intro n hn1 hn
    have hb := Work.Pi6.EMM2.finrank_row0_bound S (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀))
      (Work.Serre.mpathOf (ContinuousMap.const PUnit w₀) PUnit.unit) (M - 1) hS hfinB hfinF hF0 n hn
    have hz : Module.finrank (ZMod 2) (Coh (ZMod 2)
        (Work.Serre.mpath (ContinuousMap.const PUnit w₀)) n) = 0 :=
      finrank_eq_zero_of_isZero_cohom (htot n hn1)
    rw [hz, zero_add] at hb
    exact hb
  have hF1' : Module.finrank (ZMod 2)
      (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀)) w₀) 1) = 1 :=
    hF1
  have hF2z : Module.finrank (ZMod 2)
      (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀)) w₀) 2) = 0 :=
    finrank_eq_zero_of_isZero_cohom (hFq 2 (by norm_num) (by omega))
  have hF3z : Module.finrank (ZMod 2)
      (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀)) w₀) 3) = 0 :=
    finrank_eq_zero_of_isZero_cohom (hFq 3 (by norm_num) (by omega))
  have hF4z : Module.finrank (ZMod 2)
      (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀)) w₀) 4) = 0 :=
    finrank_eq_zero_of_isZero_cohom (hFq 4 (by norm_num) (by omega))
  have hF5z : Module.finrank (ZMod 2)
      (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀)) w₀) 5) = 0 :=
    finrank_eq_zero_of_isZero_cohom (hFq 5 (by norm_num) (by omega))
  have hB1z : Module.finrank (ZMod 2) (Coh (ZMod 2) W 1) = 0 := finrank_eq_zero_of_isZero_cohom hB1
  have h3 : Module.finrank (ZMod 2) (Coh (ZMod 2) W 3) = 0 := by
    have h := key 3 (by norm_num) (by omega)
    have hsum : (∑ r ∈ Finset.range (3 - 1), Module.finrank (ZMod 2) (Coh (ZMod 2) W (3 - (r + 2))) *
        Module.finrank (ZMod 2) (Coh (ZMod 2)
          (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀)) w₀) (r + 1))) = 0 := by
      refine Finset.sum_eq_zero fun r hr => ?_
      have hr2 : r < 2 := Finset.mem_range.mp hr
      interval_cases r
      · rw [hB1z]; ring
      · rw [hF2z]; ring
    rw [hsum, Nat.le_zero] at h
    exact h
  have h3' : IsZero (Coh (ZMod 2) W 3) := by
    haveI : FiniteDimensional (ZMod 2) (Coh (ZMod 2) W 3) := hfinB 3 (by omega)
    exact isZero_cohom_of_finrank_eq_zero h3
  refine ⟨?_, h3', ?_⟩
  · have h := key 6 (by norm_num) (by omega)
    have hsum : (∑ r ∈ Finset.range (6 - 1), Module.finrank (ZMod 2) (Coh (ZMod 2) W (6 - (r + 2))) *
        Module.finrank (ZMod 2) (Coh (ZMod 2)
          (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀)) w₀) (r + 1))) =
        Module.finrank (ZMod 2) (Coh (ZMod 2) W 4) := by
      rw [Finset.sum_eq_single 0]
      · rw [hF1']
        rw [show (6 : ℕ) - (0 + 2) = 4 from rfl]
        ring
      · intro b hb hb0
        have hb5 : b < 5 := Finset.mem_range.mp hb
        interval_cases b
        · exact absurd rfl hb0
        · rw [h3]; ring
        · rw [hF3z]; ring
        · rw [hB1z]; ring
        · rw [hF5z]; ring
      · intro h0
        exact absurd (Finset.mem_range.mpr (by norm_num : 0 < 5)) h0
    rw [hsum] at h
    exact h.trans h4
  · have h := key 5 (by norm_num) (by omega)
    have hsum : (∑ r ∈ Finset.range (5 - 1), Module.finrank (ZMod 2) (Coh (ZMod 2) W (5 - (r + 2))) *
        Module.finrank (ZMod 2) (Coh (ZMod 2)
          (Work.StemsB.fibre (Work.Serre.mpathQ (ContinuousMap.const PUnit w₀)) w₀) (r + 1))) = 0 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      rw [h3, hF2z, hB1z, hF4z]
      ring
    rw [hsum, Nat.le_zero] at h
    haveI : FiniteDimensional (ZMod 2) (Coh (ZMod 2) W 5) := hfinB 5 (by omega)
    exact isZero_cohom_of_finrank_eq_zero h

/-- The `K(ℤ,1)` facts in the form (without a positivity hypothesis on the range). -/
theorem kOneModTwoAll (N : ℕ) (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (hY : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) N Y y₀) :
    Module.finrank (ZMod 2) (Coh (ZMod 2) Y 0) = 1 ∧
      Module.finrank (ZMod 2) (Coh (ZMod 2) Y 1) = 1 ∧
      (∀ q : ℕ, 2 ≤ q → q ≤ N → IsZero (Coh (ZMod 2) Y q)) := by
  by_cases hN : 1 ≤ N
  · exact kOneModTwo N hN Y y₀ hY
  · have hN0 : N = 0 := by omega
    have hY1 : Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) 1 Y y₀ :=
      ⟨hY.1, fun i hi hc => hY.2 i hi (hc.imp id (fun hle => by omega))⟩
    obtain ⟨h0, h1, hq⟩ := kOneModTwo 1 le_rfl Y y₀ hY1
    exact ⟨h0, h1, fun q hq2 hqN => hq q hq2 (by omega)⟩

/-- The tensor product of two finite-dimensional modules is finite-dimensional. -/
theorem finiteDimensional_tensor {𝕜 M N : Type} [Field 𝕜] [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] [FiniteDimensional 𝕜 M] [FiniteDimensional 𝕜 N] :
    FiniteDimensional 𝕜 (TensorProduct 𝕜 M N) :=
  (Module.Basis.tensorProduct (Module.finBasis 𝕜 M) (Module.finBasis 𝕜 N)).finiteDimensional_of_finite

/-- A tensor product with a subsingleton left factor is a subsingleton. -/
theorem subsingleton_tensor_of_subsingleton_left {R M N : Type} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Subsingleton M] :
    Subsingleton (TensorProduct R M N) := by
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ z : TensorProduct R M N, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim m 0, TensorProduct.zero_tmul]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [h0 x, h0 y]

/-- A tensor product with a subsingleton right factor is a subsingleton. -/
theorem subsingleton_tensor_of_subsingleton_right {R M N : Type} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Subsingleton N] :
    Subsingleton (TensorProduct R M N) := by
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ z : TensorProduct R M N, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [h0 x, h0 y]

/-! ## The low-degree mod-`2` cohomology of `K(ℤ/2,2)` range models -/

/-- **The mod-`2` low-degree cohomology of a `K(ℤ/2,2)` range model** through `N ≥ 8`: it is
one-dimensional in degrees `3` and (at most) two-dimensional in degrees `5` and `6`.

The proof uses the fibration `r : Kℤ → X` of `KZModelLowStatement` (`Kℤ` a `K(ℤ,2)` range model,
so with the `K(ℤ,2)`-tables of `K2FieldLowStatement` and `kTwoDimSix`) and the row-`0` telescoping
bound `Work.Pi6.EMM2.finrank_row0_bound` for its Serre spectral sequence. -/
theorem k2DimFacts (hM : Work.Pi6.MSSHolds) (hPF : Work.Pi6.EMM2.PathFibStatement)
    (hKZ : Work.Pi6.EMM2.KZModelLowStatement)
    (h2f : Work.Pi6.EMM2.K2FieldLowStatement) (hft : Work.Pi6.EMM2.FiniteTypeStatement)
    (hLD : Work.Pi6.EMM2.LowDegreeStatement) (h2c : Work.Pi6.EMM2.SecondCohZModTwoStatement)
    {X : Type} [TopologicalSpace X] (x₀ : X) {N : ℕ} (hN : 8 ≤ N)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X x₀) :
    Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) = 1 ∧
      Module.finrank (ZMod 2) (Coh (ZMod 2) X 5) ≤ 2 ∧
      Module.finrank (ZMod 2) (Coh (ZMod 2) X 6) ≤ 2 := by
  classical
  have hZfin : Module.Finite ℤ ℤ := inferInstance
  have h3N : (3 : ℤ) ≤ ((N - 2 : ℕ) : ℤ) := by
    have hcast : ((N - 2 : ℕ) : ℤ) = (N : ℤ) - 2 := Nat.cast_sub (by omega : (2 : ℕ) ≤ N)
    rw [hcast]
    have h8 : (8 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    linarith
  obtain ⟨KZ, tKZ, k₀, rd, hrk, hKZh, -, -, hGh⟩ := hKZ x₀ N (by omega) hX
  letI : TopologicalSpace KZ := tKZ
  -- the fibration `mpathQ r` and its fibre `G`
  have hfib : Work.StemsB.IsSerreFibration (Work.Serre.mpathQ rd) :=
    Work.Serre.mpathQ_isSerreFibration rd
  have hG : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) (N - 1)
      (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀))
      (Work.StemsB.fibrePoint (Work.Serre.mpathQ rd) (Work.Serre.mpathOf rd k₀)) := hGh
  -- the `K(ℤ,2)` tables for `KZ` and for the fibre `G`
  obtain ⟨wZ, hwZ, -, hZ2even, hZ2odd⟩ := h2f hM (ZMod 2) k₀ (M := N) (by omega) hKZh
  obtain ⟨wG, hwG, -, hG2even, hG2odd⟩ := h2f hM (ZMod 2)
    (Work.StemsB.fibrePoint (Work.Serre.mpathQ rd) (Work.Serre.mpathOf rd k₀)) (M := N - 1) (by omega) hG
  have hKZ1 : IsZero (Coh (ZMod 2) KZ 1) := by
    haveI : Subsingleton (Coh (ZMod 2) KZ 1) := hZ2odd 0 (by norm_num)
    exact ModuleCat.isZero_of_subsingleton _
  have hKZ3 : IsZero (Coh (ZMod 2) KZ 3) := by
    haveI : Subsingleton (Coh (ZMod 2) KZ 3) := hZ2odd 1 (by norm_num)
    exact ModuleCat.isZero_of_subsingleton _
  have hKZ5 : IsZero (Coh (ZMod 2) KZ 5) := by
    haveI : Subsingleton (Coh (ZMod 2) KZ 5) := hZ2odd 2 (by norm_num)
    exact ModuleCat.isZero_of_subsingleton _
  have hKZ0 : Module.finrank (ZMod 2) (Coh (ZMod 2) KZ 0) = 1 := hZ2even 0 (by norm_num)
  have hKZ2 : Module.finrank (ZMod 2) (Coh (ZMod 2) KZ 2) = 1 := hZ2even 1 (by norm_num)
  have hKZ4 : Module.finrank (ZMod 2) (Coh (ZMod 2) KZ 4) = 1 := hZ2even 2 (by norm_num)
  have hKZ6 : Module.finrank (ZMod 2) (Coh (ZMod 2) KZ 6) ≤ 1 :=
    (kTwoDimSix hM hPF hft hLD kOneModTwoAll k₀ (by omega) hKZh hKZ4.le).1
  have hG1 : IsZero (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 1) := by
    haveI : Subsingleton (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 1) := hG2odd 0 (by norm_num)
    exact ModuleCat.isZero_of_subsingleton _
  have hG3 : IsZero (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 3) := by
    haveI : Subsingleton (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 3) := hG2odd 1 (by norm_num)
    exact ModuleCat.isZero_of_subsingleton _
  have hG5 : IsZero (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 5) := by
    haveI : Subsingleton (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 5) := hG2odd 2 (by norm_num)
    exact ModuleCat.isZero_of_subsingleton _
  have hG0 : Module.finrank (ZMod 2) (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 0) = 1 :=
    hG2even 0 (by norm_num)
  have hG2' : Module.finrank (ZMod 2) (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 2) = 1 :=
    hG2even 1 (by norm_num)
  have hG4 : Module.finrank (ZMod 2) (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 4) = 1 :=
    hG2even 2 (by norm_num)
  -- `X`-facts
  have hX0 : Module.finrank (ZMod 2) (Coh (ZMod 2) X 0) = 1 :=
    (hLD (ZMod 2) (A := (ZMod 2)) (by infer_instance) (m := 2) (by norm_num) (M := N) (by omega) x₀ hX).2.1
  have hX1 : IsZero (Coh (ZMod 2) X 1) :=
    (hLD (ZMod 2) (A := (ZMod 2)) (by infer_instance) (m := 2) (by norm_num) (M := N) (by omega) x₀ hX).2.2 1
      (by norm_num) (by norm_num)
  have hX2 : Module.finrank (ZMod 2) (Coh (ZMod 2) X 2) = 1 :=
    h2c (ZMod 2) (inferInstance : CharP (ZMod 2) 2) x₀ (M := N) (by omega) hX
  have hX2z : Module.finrank (ZMod 2) (Coh (ZMod 2) X 2) ≠ 0 := by rw [hX2]; norm_num
  -- finiteness
  have hfinB : ∀ s : ℕ, s ≤ N - 2 → FiniteDimensional (ZMod 2) (Coh (ZMod 2) X s) := by
    intro s hs
    have hX' : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) ((N - 2) + 1) X x₀ :=
      isEMSpaceUpTo_mono (by norm_num) hX (by omega)
    exact hft (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 2) (by norm_num) (N := N - 2) x₀ hX' s hs
  have hfinF : ∀ q : ℕ, q ≤ N - 2 → FiniteDimensional (ZMod 2)
      (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) q) := by
    intro q hq
    have hG' : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) ((N - 2) + 1)
        (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀))
        (Work.StemsB.fibrePoint (Work.Serre.mpathQ rd) (Work.Serre.mpathOf rd k₀)) :=
      isEMSpaceUpTo_mono (by norm_num) hG (by omega)
    exact hft (ZMod 2) (A := ℤ) hZfin (m := 2) (by norm_num) (N := N - 2) _ hG' q hq
  have hfinKZ : ∀ s : ℕ, s ≤ N - 2 → FiniteDimensional (ZMod 2) (Coh (ZMod 2) KZ s) := by
    intro s hs
    have hKZ' : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) ((N - 2) + 1) KZ k₀ :=
      isEMSpaceUpTo_mono (by norm_num) hKZh (by omega)
    exact hft (ZMod 2) (A := ℤ) hZfin (m := 2) (by norm_num) (N := N - 2) k₀ hKZ' s hs
  -- the spectral sequence
  obtain ⟨S, hS⟩ := hM (ZMod 2) (Work.Serre.mpath rd) X (Work.Serre.mpathQ rd)
    (Work.Serre.mpathOf rd k₀) (N - 2) hfib
    (hrk.symm ▸ (hLD (ZMod 2) (A := (ZMod 2)) (by infer_instance) (m := 2) (by norm_num) (M := N)
      (by omega) x₀ hX).1)
    hfinF hfinB
  -- the total space's cohomology is that of `KZ`
  have htot : ∀ n : ℕ, Module.finrank (ZMod 2) (Coh (ZMod 2) (Work.Serre.mpath rd) n) =
      Module.finrank (ZMod 2) (Coh (ZMod 2) KZ n) := by
    intro n
    obtain ⟨e⟩ := Work.FGThm.mpathHomotopyEquiv rd
    haveI : CategoryTheory.IsIso (Work.Cohomology.singularCohomologyMap (ZMod 2)
        (TopCat.of (Work.Serre.mpath rd)) (TopCat.of KZ) (TopCat.ofHom e.toFun) n) :=
      Work.Cohomology.homotopyEquiv (ZMod 2) (TopCat.of (Work.Serre.mpath rd)) (TopCat.of KZ)
        (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun) e.left_inv.some e.right_inv.some n
    exact (LinearEquiv.finrank_eq (linearEquivOfIso
      (CategoryTheory.asIso (Work.Cohomology.singularCohomologyMap (ZMod 2)
        (TopCat.of (Work.Serre.mpath rd)) (TopCat.of KZ) (TopCat.ofHom e.toFun) n)))).symm
  -- the telescoping bounds
  have key : ∀ n : ℕ, n ≤ N - 2 → Module.finrank (ZMod 2) (Coh (ZMod 2) X n) ≤
      Module.finrank (ZMod 2) (Coh (ZMod 2) KZ n) +
        ∑ r ∈ Finset.range (n - 1), Module.finrank (ZMod 2) (Coh (ZMod 2) X (n - (r + 2))) *
          Module.finrank (ZMod 2)
            (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) (r + 1)) := by
    intro n hn
    have hb := Work.Pi6.EMM2.finrank_row0_bound S (Work.Serre.mpathQ rd)
      (Work.Serre.mpathOf rd k₀) (N - 2) hS hfinB hfinF hG0 n hn
    rw [htot n] at hb
    exact hb
  have hdimE2 : ∀ (s q : ℕ), s ≤ N - 2 → q ≤ N - 2 →
      Module.finrank (ZMod 2) (S.E 2 ((s : ℤ), (q : ℤ))) =
        Module.finrank (ZMod 2) (Coh (ZMod 2) X s) *
          Module.finrank (ZMod 2)
            (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) q) :=
    fun s q hs hq => Work.Pi6.EMM2.e2_finrank S _ _ (N - 2) hS s q hs hq
  have h3ub : Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) ≤ 1 := by
    have h := key 3 (by omega)
    have h0 : Module.finrank (ZMod 2) (Coh (ZMod 2) KZ 3) = 0 := finrank_eq_zero_of_isZero_cohom hKZ3
    have hs : (∑ rr ∈ Finset.range (3 - 1), Module.finrank (ZMod 2) (Coh (ZMod 2) X (3 - (rr + 2))) *
        Module.finrank (ZMod 2) (Coh (ZMod 2)
          (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) (rr + 1))) = 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      show Module.finrank (ZMod 2) (Coh (ZMod 2) X 1) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 1) +
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 0) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 2) = 1
      rw [finrank_eq_zero_of_isZero_cohom hX1, finrank_eq_zero_of_isZero_cohom hG1, hX0, hG2']
    rw [h0, hs, zero_add] at h
    exact h
  have h5ub : Module.finrank (ZMod 2) (Coh (ZMod 2) X 5) ≤ 2 := by
    have h := key 5 (by omega)
    have h0 : Module.finrank (ZMod 2) (Coh (ZMod 2) KZ 5) = 0 := finrank_eq_zero_of_isZero_cohom hKZ5
    have hs : (∑ rr ∈ Finset.range (5 - 1), Module.finrank (ZMod 2) (Coh (ZMod 2) X (5 - (rr + 2))) *
        Module.finrank (ZMod 2) (Coh (ZMod 2)
          (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) (rr + 1))) = 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      show Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 1) +
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 2) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 2) +
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 1) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 3) +
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 0) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 4) = 2
      rw [finrank_eq_zero_of_isZero_cohom hG1, hX2, hG2', finrank_eq_zero_of_isZero_cohom hX1,
        finrank_eq_zero_of_isZero_cohom hG3, hX0, hG4]
      ring
    rw [h0, hs, zero_add] at h
    exact h
  have h4ub : Module.finrank (ZMod 2) (Coh (ZMod 2) X 4) ≤ 1 := by
    have h := key 4 (by omega)
    have hs : (∑ rr ∈ Finset.range (4 - 1), Module.finrank (ZMod 2) (Coh (ZMod 2) X (4 - (rr + 2))) *
        Module.finrank (ZMod 2) (Coh (ZMod 2)
          (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) (rr + 1))) = 0 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      show Module.finrank (ZMod 2) (Coh (ZMod 2) X 2) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 1) +
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 1) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 2) +
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 0) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 3) = 0
      rw [finrank_eq_zero_of_isZero_cohom hG1, finrank_eq_zero_of_isZero_cohom hX1,
        finrank_eq_zero_of_isZero_cohom hG3]
      ring
    rw [hs, add_zero] at h
    exact h.trans hKZ4.le
  -- finiteness of the `E`-pages inside the box, from `e2_finrank`
  have hboxfin : ∀ a : ℤ × ℤ, 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ ((N - 2 : ℕ) : ℤ) →
      FiniteDimensional (ZMod 2) (S.E 2 a) := by
    rintro ⟨x, y⟩ h1 h2 h3
    obtain ⟨e2b, -⟩ := hS
    have hx : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg h1
    have hy : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg h2
    have hle : x.toNat + y.toNat ≤ N - 2 := by
      have hxy : ((x.toNat + y.toNat : ℕ) : ℤ) = x + y := by
        rw [Nat.cast_add, hx, hy]
      have h4 : ((x.toNat + y.toNat : ℕ) : ℤ) ≤ ((N - 2 : ℕ) : ℤ) := by
        rw [hxy]; exact h3
      exact_mod_cast h4
    have hxs : x.toNat ≤ N - 2 := by omega
    have hys : y.toNat ≤ N - 2 := by omega
    have hbase : FiniteDimensional (ZMod 2)
        (S.E 2 (((x.toNat : ℕ) : ℤ), ((y.toNat : ℕ) : ℤ))) := by
      haveI := hfinB x.toNat hxs
      haveI hFy : FiniteDimensional (ZMod 2) (Coh (ZMod 2)
          (Work.StemsB.fibre (Work.Serre.mpathQ rd)
            ((Work.Serre.mpathQ rd) (Work.Serre.mpathOf rd k₀))) y.toNat) := hfinF y.toNat hys
      haveI : FiniteDimensional (ZMod 2)
          (↥(ModuleCat.of (ZMod 2) (TensorProduct (ZMod 2) (Coh (ZMod 2) X x.toNat)
            (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd)
              ((Work.Serre.mpathQ rd) (Work.Serre.mpathOf rd k₀))) y.toNat)))) :=
        finiteDimensional_tensor
      exact FiniteDimensional.of_injective
        (linearEquivOfIso (e2b x.toNat y.toNat hxs hys)).toLinearMap
        (linearEquivOfIso (e2b x.toNat y.toNat hxs hys)).injective
    have hpair : (((x.toNat : ℕ) : ℤ), ((y.toNat : ℕ) : ℤ)) = (x, y) := Prod.ext hx hy
    rwa [hpair] at hbase
  have hfinpages := S.finiteDimensional_E (N - 2) hboxfin
  -- `proj` is an isomorphism from the cycles onto the next page when `d_r = 0` and nothing maps in
  have hprojIso : ∀ (r : ℕ) (a : ℤ × ℤ), 0 ≤ a.1 → 0 ≤ a.2 →
      a.1 + a.2 ≤ ((N - 2 : ℕ) : ℤ) → 2 ≤ r →
      IsZero (S.E r (a + vr r)) → IsZero (S.E r (a - vr r)) →
      Module.finrank (ZMod 2) (S.E (r + 1) a) = Module.finrank (ZMod 2) (S.E r a) := by
    intro r a h1 h2 h3 hr hout hin
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    haveI := hfinpages k a h1 h2 h3
    haveI := hfinpages (k + 1) a h1 h2 h3
    haveI : Subsingleton (S.E (k + 2) (a - vr (k + 2))) := ModuleCat.subsingleton_of_isZero hin
    have hd0 : (S.d (k + 2) a (a + vr (k + 2))).hom = 0 :=
      congrArg (fun f : S.E (k + 2) a ⟶ S.E (k + 2) (a + vr (k + 2)) => f.hom)
        (S.d_eq_zero_of_isZero hout)
    have hker : Module.finrank (ZMod 2) (S.E (k + 2) a) =
        Module.finrank (ZMod 2) ↥(LinearMap.ker (S.d (k + 2) a (a + vr (k + 2))).hom) := by
      have hk : LinearMap.ker (S.d (k + 2) a (a + vr (k + 2))).hom = ⊤ := by
        rw [hd0]
        exact LinearMap.ker_zero
      rw [hk]
      exact (finrank_top (ZMod 2) (S.E (k + 2) a)).symm
    have hinj : Function.Injective (S.proj (k + 2) a) := by
      intro x y hxy
      have h1' : (S.proj (k + 2) a) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have hmem := (S.proj_ker (k + 2) a (by omega) (x - y)).mp h1'
      obtain ⟨w, hw⟩ := hmem
      have hw0 : w = 0 := Subsingleton.elim w 0
      have hzero : ((x - y : ↥(LinearMap.ker (S.d (k + 2) a (a + vr (k + 2))).hom)) :
          S.E (k + 2) a) = 0 := by
        rw [← hw, hw0, map_zero]
      exact sub_eq_zero.mp (Subtype.ext hzero)
    have hiso : Module.finrank (ZMod 2) (S.E (k + 2 + 1) a) =
        Module.finrank (ZMod 2) ↥(LinearMap.ker (S.d (k + 2) a (a + vr (k + 2))).hom) := by
      refine le_antisymm ?_ ?_
      · exact LinearMap.finrank_le_finrank_of_surjective (S.proj_surj (k + 2) a (by omega))
      · exact LinearMap.finrank_le_finrank_of_injective hinj
    omega
  have h3eq : Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) = 1 := by
    obtain ⟨e2, -, -, hconv, -, -⟩ := hS
    -- vanishing at page `2` from a vanishing tensor factor
    have hIsZeroE2 : ∀ (s q : ℕ), s ≤ N - 2 → q ≤ N - 2 →
        (IsZero (Coh (ZMod 2) X s) ∨ IsZero (Coh (ZMod 2)
          (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) q)) →
        IsZero (S.E 2 ((s : ℤ), (q : ℤ))) := by
      intro s q hs hq h
      refine IsZero.of_iso ?_ (e2 s q hs hq)
      rcases h with h | h
      · haveI hX : Subsingleton (Coh (ZMod 2) X s) := ModuleCat.subsingleton_of_isZero h
        haveI : Subsingleton (TensorProduct (ZMod 2) (Coh (ZMod 2) X s)
            (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd)
              ((Work.Serre.mpathQ rd) (Work.Serre.mpathOf rd k₀))) q)) :=
          subsingleton_tensor_of_subsingleton_left
        exact isZero_moduleCat_of_subsingleton
      · haveI hF : Subsingleton (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd)
              ((Work.Serre.mpathQ rd) (Work.Serre.mpathOf rd k₀))) q) :=
          ModuleCat.subsingleton_of_isZero h
        haveI : Subsingleton (TensorProduct (ZMod 2) (Coh (ZMod 2) X s)
            (Coh (ZMod 2) (Work.StemsB.fibre (Work.Serre.mpathQ rd)
              ((Work.Serre.mpathQ rd) (Work.Serre.mpathOf rd k₀))) q)) :=
          subsingleton_tensor_of_subsingleton_right
        exact isZero_moduleCat_of_subsingleton
    have hI01 : IsZero (S.E 2 ((0 : ℤ), (1 : ℤ))) :=
      hIsZeroE2 0 1 (by omega) (by omega) (Or.inr hG1)
    have hI11 : IsZero (S.E 2 ((1 : ℤ), (1 : ℤ))) :=
      hIsZeroE2 1 1 (by omega) (by omega) (Or.inl hX1)
    have hI12 : IsZero (S.E 2 ((1 : ℤ), (2 : ℤ))) :=
      hIsZeroE2 1 2 (by omega) (by omega) (Or.inl hX1)
    have hI21 : IsZero (S.E 2 ((2 : ℤ), (1 : ℤ))) :=
      hIsZeroE2 2 1 (by omega) (by omega) (Or.inr hG1)
    have hIneg : ∀ (r : ℕ) (v : ℤ × ℤ), v.1 < 0 ∨ v.2 < 0 → IsZero (S.E r v) :=
      fun r v hv => S.isZero_quad r v hv
    -- `dim E_4^{2,0} = 1`
    have h42 : Module.finrank (ZMod 2) (S.E 4 ((2 : ℤ), (0 : ℤ))) = 1 := by
      have h20 : Module.finrank (ZMod 2) (S.E 2 ((2 : ℤ), (0 : ℤ))) = 1 := by
        have hh := hdimE2 2 0 (by omega) (by omega)
        rw [hX2, hG0, mul_one] at hh
        exact hh
      have e3 : Module.finrank (ZMod 2) (S.E 3 ((2 : ℤ), (0 : ℤ))) =
          Module.finrank (ZMod 2) (S.E 2 ((2 : ℤ), (0 : ℤ))) := by
        refine hprojIso 2 ((2 : ℤ), (0 : ℤ)) (by norm_num) (by norm_num) (by linarith)
          (by norm_num) ?_ ?_
        · rw [show ((2 : ℤ), (0 : ℤ)) + vr 2 = ((4 : ℤ), (-1 : ℤ)) from by ext <;> simp [vr]]
          exact hIneg 2 ((4 : ℤ), (-1 : ℤ)) (Or.inr (by norm_num))
        · rw [show ((2 : ℤ), (0 : ℤ)) - vr 2 = ((0 : ℤ), (1 : ℤ)) from by ext <;> simp [vr]]
          exact hI01
      have e4 : Module.finrank (ZMod 2) (S.E 4 ((2 : ℤ), (0 : ℤ))) =
          Module.finrank (ZMod 2) (S.E 3 ((2 : ℤ), (0 : ℤ))) := by
        refine hprojIso 3 ((2 : ℤ), (0 : ℤ)) (by norm_num) (by norm_num) (by linarith)
          (by norm_num) ?_ ?_
        · rw [show ((2 : ℤ), (0 : ℤ)) + vr 3 = ((5 : ℤ), (-2 : ℤ)) from by ext <;> simp [vr]]
          exact hIneg 3 ((5 : ℤ), (-2 : ℤ)) (Or.inr (by norm_num))
        · rw [show ((2 : ℤ), (0 : ℤ)) - vr 3 = ((-1 : ℤ), (2 : ℤ)) from by ext <;> simp [vr]]
          exact hIneg 3 ((-1 : ℤ), (2 : ℤ)) (Or.inl (by norm_num))
      rw [e4, e3, h20]
    have h41 : Module.finrank (ZMod 2) (S.E 4 ((1 : ℤ), (1 : ℤ))) = 0 := by
      haveI : Subsingleton (S.E 4 ((1 : ℤ), (1 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (S.isZero_two_of ((1 : ℤ), (1 : ℤ)) hI11 2)
      exact Module.finrank_zero_of_subsingleton
    -- `dim E_4^{0,2} = 0` from the convergence in total degree `2`
    have h40 : Module.finrank (ZMod 2) (S.E 4 ((0 : ℤ), (2 : ℤ))) = 0 := by
      have hc := hconv 2 (by omega)
      rw [htot 2, hKZ2] at hc
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hc
      have hc' : Module.finrank (ZMod 2) (S.E 4 ((0 : ℤ), (2 : ℤ))) +
          Module.finrank (ZMod 2) (S.E 4 ((1 : ℤ), (1 : ℤ))) +
          Module.finrank (ZMod 2) (S.E 4 ((2 : ℤ), (0 : ℤ))) = 1 := by
        simpa using hc
      omega
    -- `E_3^{0,2}` is one-dimensional
    have h302 : Module.finrank (ZMod 2) (S.E 3 ((0 : ℤ), (2 : ℤ))) = 1 := by
      have h02 : Module.finrank (ZMod 2) (S.E 2 ((0 : ℤ), (2 : ℤ))) = 1 := by
        have hh := hdimE2 0 2 (by omega) (by omega)
        rw [hX0, hG2', mul_one] at hh
        exact hh
      have e3 : Module.finrank (ZMod 2) (S.E 3 ((0 : ℤ), (2 : ℤ))) =
          Module.finrank (ZMod 2) (S.E 2 ((0 : ℤ), (2 : ℤ))) := by
        refine hprojIso 2 ((0 : ℤ), (2 : ℤ)) (by norm_num) (by norm_num) (by linarith)
          (by norm_num) ?_ ?_
        · rw [show ((0 : ℤ), (2 : ℤ)) + vr 2 = ((2 : ℤ), (1 : ℤ)) from by ext <;> simp [vr]]
          exact hI21
        · rw [show ((0 : ℤ), (2 : ℤ)) - vr 2 = ((-2 : ℤ), (3 : ℤ)) from by ext <;> simp [vr]]
          exact hIneg 2 ((-2 : ℤ), (3 : ℤ)) (Or.inl (by norm_num))
      rw [e3, h02]
    -- `E_3^{3,0}` is the cohomology of `X` in degree `3`
    have h330eq : Module.finrank (ZMod 2) (S.E 3 ((3 : ℤ), (0 : ℤ))) =
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) := by
      have h30 : Module.finrank (ZMod 2) (S.E 2 ((3 : ℤ), (0 : ℤ))) =
          Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) := by
        have hh := hdimE2 3 0 (by omega) (by omega)
        rw [hG0, mul_one] at hh
        exact hh
      rw [← h30]
      refine hprojIso 2 ((3 : ℤ), (0 : ℤ)) (by norm_num) (by norm_num) (by linarith)
        (by norm_num) ?_ ?_
      · rw [show ((3 : ℤ), (0 : ℤ)) + vr 2 = ((5 : ℤ), (-1 : ℤ)) from by ext <;> simp [vr]]
        exact hIneg 2 ((5 : ℤ), (-1 : ℤ)) (Or.inr (by norm_num))
      · rw [show ((3 : ℤ), (0 : ℤ)) - vr 2 = ((1 : ℤ), (1 : ℤ)) from by ext <;> simp [vr]]
        exact hI11
    -- `d_3` is nonzero on `E_3^{0,2}`, hence `E_3^{3,0}` (and `H³(X)`) is one-dimensional
    have hd3 : (S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)).hom ≠ 0 := by
      intro hzero
      haveI : FiniteDimensional (ZMod 2) (S.E 3 ((0 : ℤ), (2 : ℤ))) :=
        hfinpages 1 ((0 : ℤ), (2 : ℤ)) (by norm_num) (by norm_num) (by linarith)
      haveI : FiniteDimensional (ZMod 2) (S.E 4 ((0 : ℤ), (2 : ℤ))) :=
        hfinpages 2 ((0 : ℤ), (2 : ℤ)) (by norm_num) (by norm_num) (by linarith)
      haveI : Subsingleton (S.E 3 (((0 : ℤ), (2 : ℤ)) - vr 3)) := by
        rw [show ((0 : ℤ), (2 : ℤ)) - vr 3 = ((-3 : ℤ), (4 : ℤ)) from by ext <;> simp [vr]]
        exact ModuleCat.subsingleton_of_isZero (hIneg 3 ((-3 : ℤ), (4 : ℤ)) (Or.inl (by norm_num)))
      have hker1 : Module.finrank (ZMod 2) ↥(LinearMap.ker (S.d 3 ((0 : ℤ), (2 : ℤ))
          (((0 : ℤ), (2 : ℤ)) + vr 3)).hom) = 1 := by
        have hk : LinearMap.ker (S.d 3 ((0 : ℤ), (2 : ℤ))
            (((0 : ℤ), (2 : ℤ)) + vr 3)).hom = ⊤ := by
          rw [hzero]
          exact LinearMap.ker_zero
        rw [hk, finrank_top (ZMod 2) (S.E 3 ((0 : ℤ), (2 : ℤ)))]
        exact h302
      have hinj : Function.Injective (S.proj 3 ((0 : ℤ), (2 : ℤ))) := by
        intro x y hxy
        have h1' : (S.proj 3 ((0 : ℤ), (2 : ℤ))) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
        have hmem := (S.proj_ker 3 ((0 : ℤ), (2 : ℤ)) (by norm_num) (x - y)).mp h1'
        obtain ⟨w, hw⟩ := hmem
        have hw0 : w = 0 := Subsingleton.elim w 0
        have hzero' : ((x - y : ↥(LinearMap.ker (S.d 3 ((0 : ℤ), (2 : ℤ))
            (((0 : ℤ), (2 : ℤ)) + vr 3)).hom)) : S.E 3 ((0 : ℤ), (2 : ℤ))) = 0 := by
          rw [← hw, hw0, map_zero]
        exact sub_eq_zero.mp (Subtype.ext hzero')
      have hdim : Module.finrank (ZMod 2) (S.E 4 ((0 : ℤ), (2 : ℤ))) =
          Module.finrank (ZMod 2) ↥(LinearMap.ker (S.d 3 ((0 : ℤ), (2 : ℤ))
            (((0 : ℤ), (2 : ℤ)) + vr 3)).hom) := by
        refine le_antisymm ?_ ?_
        · exact LinearMap.finrank_le_finrank_of_surjective
            (S.proj_surj 3 ((0 : ℤ), (2 : ℤ)) (by norm_num))
        · exact LinearMap.finrank_le_finrank_of_injective hinj
      omega
    have h3ge : 1 ≤ Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) := by
      rw [← h330eq]
      have hpos3 : ((0 : ℤ), (2 : ℤ)) + vr 3 = ((3 : ℤ), (0 : ℤ)) := by ext <;> simp [vr]
      haveI : FiniteDimensional (ZMod 2) (S.E 3 (((0 : ℤ), (2 : ℤ)) + vr 3)) := by
        rw [hpos3]
        exact hfinpages 1 ((3 : ℤ), (0 : ℤ)) (by norm_num) (by norm_num) (by linarith)
      have hrng : LinearMap.range (S.d 3 ((0 : ℤ), (2 : ℤ))
          (((0 : ℤ), (2 : ℤ)) + vr 3)).hom ≠ ⊥ := by
        intro hbot
        exact hd3 (LinearMap.range_eq_bot.mp hbot)
      obtain ⟨z, hzp, hz0⟩ := (Submodule.ne_bot_iff (LinearMap.range (S.d 3 ((0 : ℤ), (2 : ℤ))
          (((0 : ℤ), (2 : ℤ)) + vr 3)).hom)).mp hrng
      have hspan : Submodule.span (ZMod 2) {z} ≤ LinearMap.range (S.d 3 ((0 : ℤ), (2 : ℤ))
          (((0 : ℤ), (2 : ℤ)) + vr 3)).hom :=
        Submodule.span_le.mpr (by rintro w rfl; exact hzp)
      calc (1 : ℕ) = Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {z}) :=
            (finrank_span_singleton hz0).symm
        _ ≤ Module.finrank (ZMod 2) ↥(LinearMap.range (S.d 3 ((0 : ℤ), (2 : ℤ))
              (((0 : ℤ), (2 : ℤ)) + vr 3)).hom) := Submodule.finrank_mono hspan
        _ ≤ Module.finrank (ZMod 2) (S.E 3 (((0 : ℤ), (2 : ℤ)) + vr 3)) :=
            Submodule.finrank_le _
    omega
  have h6ub : Module.finrank (ZMod 2) (Coh (ZMod 2) X 6) ≤ 2 := by
    have h := key 6 (by omega)
    have hs : (∑ rr ∈ Finset.range (6 - 1), Module.finrank (ZMod 2) (Coh (ZMod 2) X (6 - (rr + 2))) *
        Module.finrank (ZMod 2) (Coh (ZMod 2)
          (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) (rr + 1))) = 1 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_one]
      show Module.finrank (ZMod 2) (Coh (ZMod 2) X 4) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 1) +
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 2) +
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 2) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 3) +
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 1) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 4) +
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 0) *
          Module.finrank (ZMod 2) (Coh (ZMod 2)
            (Work.StemsB.fibre (Work.Serre.mpathQ rd) (rd k₀)) 5) = 1
      rw [finrank_eq_zero_of_isZero_cohom hG1, h3eq, hG2', finrank_eq_zero_of_isZero_cohom hG3,
        finrank_eq_zero_of_isZero_cohom hX1, hX0, finrank_eq_zero_of_isZero_cohom hG5]
      ring
    rw [hs] at h
    omega
  exact ⟨h3eq, h5ub, h6ub⟩


/-! ## The `K(ℤ/2,3)` forcing at threshold `9` -/

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
/-- **The `K(ℤ/2,3)` forcing** (`Work.Pi6.EMM2.K3Facts9Statement`): for a range model `X` of
`K(ℤ/2,3)` through `N ≥ 9`, the mod-`2` cohomology is one-dimensional in degrees `3` and `4`, at
most one-dimensional in degree `5`, at most two-dimensional in degrees `6` and `7`, and the square
of every nonzero class of degree `3` is nonzero.

The proof runs the Serre spectral sequence of the path–loop fibration `ΩX → PX → X` (`MSSHolds`,
`PathFibStatement`, `FiniteTypeStatement`, `LowDegreeStatement`, `CupOneStatement`) with
`N_ss = N - 2`.  The fibre `ΩX` is a `K(ℤ/2,2)` range model through `N - 1`, whose low-degree
cohomology is supplied by `k2DimFacts` (`H³ = 1`, `H⁵ ≤ 2`, `H⁶ ≤ 2`) together with `hK2`
(`H³ ≤ 1`, `H⁴ ≤ 1`, cup squares) and `SecondCohZModTwoStatement` (`H² = 1`).

The dimension bookkeeping is
* `row0Refined` (the telescoped row-`0` bound with the sources on their own pages), and
* the column bounds `dim E_6^{0,5} ≤ 1`, `dim E_7^{0,6} ≤ 1`, obtained by the non-vanishing of the
  products `ι · y₃`, `ι · ι²` (`e2RowColMulNeZero3`, `e2RowColMulNeZero4`). -/
theorem k3forcing9 : Work.Pi6.EMM2.K3Facts9Statement := by
  intro hM hKZ hFT hLD h2f h2c hmc hco hPF hk2 X tX x₀ N hN hX
  classical
  have hZfin : Module.Finite ℤ ℤ := inferInstance
  -- ## the path–loop fibration of `X` and its fibre `ΩX`
  obtain ⟨hcontr, hfib, hFibEM⟩ := hPF (A := ZMod 2) (m := 3) (by norm_num) (M := N) x₀ hX
  haveI : ContractibleSpace (k4PathSpace x₀) := hcontr
  have hFib : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) (N - 1)
      (k4LoopSpace x₀) (k4LoopBase x₀) := hFibEM
  -- ## the fibre's low-degree cohomology (a `K(ℤ/2,2)` model through `N - 1 ≥ 8`)
  have hK2 := hk2 hM hKZ hFT hLD h2f h2c hmc hco (k4LoopBase x₀) (N := N - 1) (by omega) hFib
  have h2dim := k2DimFacts hM hPF hKZ h2f hFT hLD h2c (k4LoopBase x₀) (N := N - 1) (by omega) hFib
  obtain ⟨-, hF0, hFodd⟩ := hLD (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 2) (M := N - 1)
    (by norm_num) (by omega) (X := k4LoopSpace x₀) (k4LoopBase x₀) hFib
  have hF1 : IsZero (Coh (ZMod 2) (k4LoopSpace x₀) 1) := hFodd 1 (by norm_num) (by norm_num)
  have hF2 : Module.finrank (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) 2) = 1 :=
    h2c (ZMod 2) (inferInstance : CharP (ZMod 2) 2) (k4LoopBase x₀) (M := N - 1) (by omega) hFib
  have hF3 : Module.finrank (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) 3) = 1 := h2dim.1
  have hF4 : Module.finrank (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) 4) ≤ 1 := hK2.2.1
  have hF5 : Module.finrank (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) 5) ≤ 2 := h2dim.2.1
  have hF6 : Module.finrank (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) 6) ≤ 2 := h2dim.2.2
  have hFsq2 : ∀ a : Coh (ZMod 2) (k4LoopSpace x₀) 2, a ≠ 0 →
      cup (ZMod 2) (k4LoopSpace x₀) 2 2 a a ≠ 0 := hK2.2.2.1
  -- ## low-degree facts for the base (a `K(ℤ/2,3)` model)
  obtain ⟨hSC, hB0, hBodd⟩ := hLD (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 3) (M := N)
    (by norm_num) (by omega) x₀ hX
  have hB1 : IsZero (Coh (ZMod 2) X 1) := hBodd 1 (by norm_num) (by norm_num)
  have hB2 : IsZero (Coh (ZMod 2) X 2) := hBodd 2 (by norm_num) (by norm_num)
  -- ## finiteness of the base and the fibre
  have hBfin : ∀ s : ℕ, s ≤ N - 2 → FiniteDimensional (ZMod 2) (Coh (ZMod 2) X s) := by
    intro s hs
    have hX' : Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) ((N - 2) + 1) X x₀ :=
      isEMSpaceUpTo_mono (by norm_num) hX (by omega)
    exact hFT (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 3) (by norm_num) (N := N - 2) x₀ hX' s hs
  have hFfin : ∀ q : ℕ, q ≤ N - 2 →
      FiniteDimensional (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) q) := by
    intro q hq
    have hG' : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) ((N - 2) + 1)
        (k4LoopSpace x₀) (k4LoopBase x₀) := isEMSpaceUpTo_mono (by norm_num) hFib (by omega)
    exact hFT (ZMod 2) (A := ZMod 2) (by infer_instance) (m := 2) (by norm_num) (N := N - 2)
      (k4LoopBase x₀) hG' q hq
  -- ## the spectral sequence
  have hSC' : Work.PiS.SimplyConn X ((k4PathFib x₀) (k4PathBase x₀)) := hSC
  have hSS := hM (ZMod 2) (k4PathSpace x₀) X (k4PathFib x₀) (k4PathBase x₀) (N - 2)
    hfib hSC' hFfin hBfin
  obtain ⟨S, hS⟩ := hSS
  have hIsS : IsSerreMSS S (k4PathFib x₀) (k4PathBase x₀) (N - 2) := hS
  obtain ⟨e2, hmul, hconv0, hconv, hbot, hcol⟩ := hS
  -- ## page-`2` bookkeeping
  have hdimE2 : ∀ (s q : ℕ), s ≤ N - 2 → q ≤ N - 2 →
      Module.finrank (ZMod 2) (S.E 2 ((s : ℤ), (q : ℤ))) =
        Module.finrank (ZMod 2) (Coh (ZMod 2) X s) *
          Module.finrank (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) q) :=
    fun s q hs hq => Work.Pi6.EMM2.e2_finrank S (k4PathFib x₀) (k4PathBase x₀) (N - 2) hIsS s q hs hq
  have hbox : ∀ a : ℤ × ℤ, 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ ((N - 2 : ℕ) : ℤ) →
      FiniteDimensional (ZMod 2) (S.E 2 a) := by
    rintro ⟨x, y⟩ h1 h2 h3
    obtain ⟨e2b, -⟩ := hIsS
    have hx : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg h1
    have hy : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg h2
    have hle : x.toNat + y.toNat ≤ N - 2 := by
      have hxy : ((x.toNat + y.toNat : ℕ) : ℤ) = x + y := by rw [Nat.cast_add, hx, hy]
      have h4 : ((x.toNat + y.toNat : ℕ) : ℤ) ≤ ((N - 2 : ℕ) : ℤ) := by rw [hxy]; exact h3
      exact_mod_cast h4
    have hxs : x.toNat ≤ N - 2 := by omega
    have hys : y.toNat ≤ N - 2 := by omega
    have hbase : FiniteDimensional (ZMod 2)
        (S.E 2 (((x.toNat : ℕ) : ℤ), ((y.toNat : ℕ) : ℤ))) := by
      haveI hB : FiniteDimensional (ZMod 2) (Coh (ZMod 2) X x.toNat) := hBfin x.toNat hxs
      haveI hF : FiniteDimensional (ZMod 2) (Coh (ZMod 2) (k4LoopSpace x₀) y.toNat) :=
        hFfin y.toNat hys
      haveI : FiniteDimensional (ZMod 2) (↥(ModuleCat.of (ZMod 2)
          (TensorProduct (ZMod 2) (Coh (ZMod 2) X x.toNat)
            (Coh (ZMod 2) (k4LoopSpace x₀) y.toNat)))) := finiteDimensional_tensor
      exact FiniteDimensional.of_injective
        (linearEquivOfIso (e2b x.toNat y.toNat hxs hys)).toLinearMap
        (linearEquivOfIso (e2b x.toNat y.toNat hxs hys)).injective
    have hpair : (((x.toNat : ℕ) : ℤ), ((y.toNat : ℕ) : ℤ)) = (x, y) := Prod.ext hx hy
    rwa [hpair] at hbase
  have hfin : ∀ (k : ℕ) (a : ℤ × ℤ), 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ ((N - 2 : ℕ) : ℤ) →
      FiniteDimensional (ZMod 2) (S.E (k + 2) a) := S.finiteDimensional_E (N - 2) hbox
  have hfin3 : FiniteDimensional (ZMod 2) (S.E 2 ((3 : ℤ), (0 : ℤ))) := hbox _ (by norm_num) (by norm_num) (by omega)
  have hfin0 : ∀ (k : ℕ) (a : ℤ × ℤ), 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ ((N - 2 : ℕ) : ℤ) →
      FiniteDimensional (ZMod 2) (S.E (k + 2) a) := S.finiteDimensional_E (N - 2) hbox
  -- ## vanishings at page `2`
  have hZ2B : ∀ (s : ℕ), s ≤ N - 2 → IsZero (Coh (ZMod 2) X s) → ∀ q ≤ N - 2,
      IsZero (S.E 2 ((s : ℤ), (q : ℤ))) :=
    fun s hs h q hq => k4_isZero_E2_left (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀)
      (N := N - 2) (hS := hIsS) hs hq h
  have hZ2F : ∀ (q : ℕ), q ≤ N - 2 → IsZero (Coh (ZMod 2) (k4LoopSpace x₀) q) → ∀ s ≤ N - 2,
      IsZero (S.E 2 ((s : ℤ), (q : ℤ))) :=
    fun q hq h s hs => k4_isZero_E2_right (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀)
      (N := N - 2) (hS := hIsS) hs hq h
  have h11 : IsZero (S.E 2 ((1 : ℤ), (1 : ℤ))) := hZ2B 1 (by omega) hB1 1 (by omega)
  have h12 : IsZero (S.E 2 ((1 : ℤ), (2 : ℤ))) := hZ2B 1 (by omega) hB1 2 (by omega)
  have h21 : IsZero (S.E 2 ((2 : ℤ), (1 : ℤ))) := hZ2B 2 (by omega) hB2 1 (by omega)
  have h01 : IsZero (S.E 2 ((0 : ℤ), (1 : ℤ))) := hZ2F 1 (by omega) hF1 0 (by omega)
  have hE : ∀ n : ℕ, 1 ≤ n → n ≤ N - 2 → IsZero (Coh (ZMod 2) (k4PathSpace x₀) n) := by
    intro n hn hNn
    have h := Work.Cohomology.contractible (ZMod 2) (TopCat.of (k4PathSpace x₀)) (n - 1)
    rwa [show n - 1 + 1 = n from by omega] at h
  -- ## the row-`0` upper bounds
  have htop0 : ∀ n : ℕ, 1 ≤ n → n ≤ N - 2 →
      Module.finrank (ZMod 2) (S.E (n + 2) ((n : ℤ), (0 : ℤ))) = 0 := by
    intro n hn hNn
    haveI : Subsingleton (S.E (n + 2) ((n : ℤ), (0 : ℤ))) :=
      ModuleCat.subsingleton_of_isZero (hconv0 n hn hNn
        (ModuleCat.subsingleton_of_isZero (hE n hn hNn)) n 0 (by omega))
    exact Module.finrank_zero_of_subsingleton
  have hlhs0 : ∀ n : ℕ, n ≤ N - 2 → Module.finrank (ZMod 2) (S.E 2 ((n : ℤ), (0 : ℤ))) =
      Module.finrank (ZMod 2) (Coh (ZMod 2) X n) := by
    intro n hn
    have hh := hdimE2 n 0 hn (by omega)
    rw [hF0, mul_one] at hh
    exact hh
  -- ## `dim H³(X) ≤ 1`
  have hB3le : Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) ≤ 1 := by
    have h := row0Refined (E := k4PathSpace x₀) (B := X) S (N - 2) hbox 3 (by omega)
    have h1 : Module.finrank (ZMod 2) (S.E (3 + 2) (((3 : ℕ) : ℤ), 0)) = 0 :=
      htop0 3 (by norm_num) (by omega)
    have h2 : Module.finrank (ZMod 2) (S.E 2 (((3 : ℕ) : ℤ), 0)) =
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) := hlhs0 3 (by omega)
    rw [h1, zero_add, h2] at h
    refine h.trans ?_
    have h0 : Module.finrank (ZMod 2) (S.E 2 (CohSS.sr 3 2)) = 0 := by
      rw [show CohSS.sr 3 2 = ((1 : ℤ), (1 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 2 ((1 : ℤ), (1 : ℤ))) := ModuleCat.subsingleton_of_isZero h11
      exact Module.finrank_zero_of_subsingleton
    have h3 : Module.finrank (ZMod 2) (S.E 3 (CohSS.sr 3 3)) ≤ 1 := by
      rw [show CohSS.sr 3 3 = ((0 : ℤ), (2 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      refine (k4_finrank_mono S ((0 : ℤ), (2 : ℤ)) 2 (by norm_num) 1 ?_).trans ?_
      · intro k hk1 hk2
        interval_cases k
        · exact hbox ((0 : ℤ), (2 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 1 ((0 : ℤ), (2 : ℤ)) (by norm_num) (by norm_num) (by omega)
      · have hh := hdimE2 0 2 (by omega) (by omega)
        rw [hB0, hF2, mul_one] at hh
        exact hh.le
    have h4 : Module.finrank (ZMod 2) (S.E 4 (CohSS.sr 3 4)) = 0 := by
      rw [show CohSS.sr 3 4 = ((-1 : ℤ), (3 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 4 ((-1 : ℤ), (3 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (S.isZero_quad 4 _ (Or.inl (by norm_num)))
      exact Module.finrank_zero_of_subsingleton
    rw [Finset.sum_range_succ (n := 2), Finset.sum_range_succ (n := 1),
      Finset.sum_range_succ (n := 0), Finset.sum_range_zero, h0, h4]
    simp only [zero_add, add_zero]
    exact h3
  -- ## the transgression: `dim H³(X) ≥ 1`
  obtain ⟨f2, hf2⟩ := k4_exists_ne_zero (𝕜 := ZMod 2) hF2
  let u : S.E 2 ((0 : ℤ), (2 : ℤ)) := (e2 0 2 (by omega) (by omega)).inv.hom
    (one (ZMod 2) X ⊗ₜ[ZMod 2] f2)
  have hu0 : u ≠ 0 := k4_e2_inv_tmul_ne_zero (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀)
    (e2 := e2 0 2 (by omega) (by omega)) (one_ne_zero_of_finrank_one hB0) hf2
  have hdu : (S.d 2 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 2)).hom u = 0 := by
    refine k4_d_apply_eq_zero S ?_ u
    rw [show ((0 : ℤ), (2 : ℤ)) + vr 2 = ((2 : ℤ), (1 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_left (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀) (N := N - 2)
      (hS := hIsS) (r := 2) (s := 2) (q := 1) (by norm_num) (by omega) (by omega) hB2
  let u1 : S.E 3 ((0 : ℤ), (2 : ℤ)) := S.proj 2 ((0 : ℤ), (2 : ℤ)) ⟨u, hdu⟩
  have hu10 : u1 ≠ 0 := by
    refine k4_proj_ne_zero S (r := 2) (by norm_num) ((0 : ℤ), (2 : ℤ)) hdu hu0 ?_
    rw [show ((0 : ℤ), (2 : ℤ)) - vr 2 = ((-2 : ℤ), (3 : ℤ)) from by ext <;> norm_num [vr]]
    exact S.isZero_quad 2 _ (Or.inl (by norm_num))
  have hd3u1 : (S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)).hom u1 ≠ 0 := by
    intro hzero
    have hE4 : IsZero (S.E 4 ((0 : ℤ), (2 : ℤ))) :=
      hconv0 2 (by norm_num) (by omega) (ModuleCat.subsingleton_of_isZero (hE 2 (by norm_num) (by omega))) 0 2 (by norm_num)
    have hmem : u1 ∈ LinearMap.range (S.d 3 (((0 : ℤ), (2 : ℤ)) - vr 3) ((0 : ℤ), (2 : ℤ))).hom := by
      haveI : Subsingleton (S.E 4 ((0 : ℤ), (2 : ℤ))) := ModuleCat.subsingleton_of_isZero hE4
      have h0 : S.proj 3 ((0 : ℤ), (2 : ℤ)) ⟨u1, hzero⟩ = 0 := Subsingleton.elim _ _
      exact (S.proj_ker 3 ((0 : ℤ), (2 : ℤ)) (by norm_num) ⟨u1, hzero⟩).mp h0
    obtain ⟨z, hz⟩ := hmem
    haveI : Subsingleton (S.E 3 (((0 : ℤ), (2 : ℤ)) - vr 3)) := by
      rw [show ((0 : ℤ), (2 : ℤ)) - vr 3 = ((-3 : ℤ), (4 : ℤ)) from by ext <;> norm_num [vr]]
      exact ModuleCat.subsingleton_of_isZero (S.isZero_quad 3 _ (Or.inl (by norm_num)))
    rw [Subsingleton.elim z 0, map_zero] at hz
    exact hu10 hz.symm
  have hB3ge : 1 ≤ Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) := by
    have hd3u1' : (S.d 3 ((0 : ℤ), (2 : ℤ)) ((3 : ℤ), (0 : ℤ))).hom u1 ≠ 0 := hd3u1
    haveI hfin30 : FiniteDimensional (ZMod 2) (S.E 3 ((3 : ℤ), (0 : ℤ))) :=
      hfin 1 ((3 : ℤ), (0 : ℤ)) (by norm_num) (by norm_num) (by omega)
    have h1 : 1 ≤ Module.finrank (ZMod 2) (S.E 3 ((3 : ℤ), (0 : ℤ))) :=
      k4_finrank_pos_of_ne_zero hd3u1'
    have hmono : Module.finrank (ZMod 2) (S.E 3 ((3 : ℤ), (0 : ℤ))) ≤
        Module.finrank (ZMod 2) (S.E 2 ((3 : ℤ), (0 : ℤ))) :=
      k4_finrank_mono S ((3 : ℤ), (0 : ℤ)) 2 (by norm_num) 1 (fun k hk1 hk2 => by
        interval_cases k
        · exact hbox ((3 : ℤ), (0 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 1 ((3 : ℤ), (0 : ℤ)) (by norm_num) (by norm_num) (by omega))
    have h2 : Module.finrank (ZMod 2) (S.E 2 ((3 : ℤ), (0 : ℤ))) =
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) := by
      have hh := hdimE2 3 0 (by omega) (by omega)
      rw [hF0, mul_one] at hh
      exact hh
    linarith
  have hB3 : Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) = 1 := le_antisymm hB3le hB3ge
  -- ## `dim H⁴(X) ≤ 1`
  have hB4le : Module.finrank (ZMod 2) (Coh (ZMod 2) X 4) ≤ 1 := by
    have h := row0Refined (E := k4PathSpace x₀) (B := X) S (N - 2) hbox 4 (by omega)
    have h1 : Module.finrank (ZMod 2) (S.E (4 + 2) (((4 : ℕ) : ℤ), 0)) = 0 :=
      htop0 4 (by norm_num) (by omega)
    have h2 : Module.finrank (ZMod 2) (S.E 2 (((4 : ℕ) : ℤ), 0)) =
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 4) := hlhs0 4 (by omega)
    rw [h1, zero_add, h2] at h
    refine h.trans ?_
    have h0 : Module.finrank (ZMod 2) (S.E 2 (CohSS.sr 4 2)) = 0 := by
      rw [show CohSS.sr 4 2 = ((2 : ℤ), (1 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 2 ((2 : ℤ), (1 : ℤ))) := ModuleCat.subsingleton_of_isZero h21
      exact Module.finrank_zero_of_subsingleton
    have h3 : Module.finrank (ZMod 2) (S.E 3 (CohSS.sr 4 3)) = 0 := by
      rw [show CohSS.sr 4 3 = ((1 : ℤ), (2 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 3 ((1 : ℤ), (2 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (S.isZero_succ (r := 2) (by norm_num) _ h12)
      exact Module.finrank_zero_of_subsingleton
    have h4 : Module.finrank (ZMod 2) (S.E 4 (CohSS.sr 4 4)) ≤ 1 := by
      rw [show CohSS.sr 4 4 = ((0 : ℤ), (3 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      refine (k4_finrank_mono S ((0 : ℤ), (3 : ℤ)) 2 (by norm_num) 2 ?_).trans ?_
      · intro k hk1 hk2
        interval_cases k
        · exact hbox ((0 : ℤ), (3 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 1 ((0 : ℤ), (3 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 2 _ (by norm_num) (by norm_num) (by omega)
      · have hh := hdimE2 0 3 (by omega) (by omega)
        rw [hB0, hF3, mul_one] at hh
        exact hh.le
    have h5 : Module.finrank (ZMod 2) (S.E 5 (CohSS.sr 4 5)) = 0 := by
      rw [show CohSS.sr 4 5 = ((-1 : ℤ), (4 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 5 ((-1 : ℤ), (4 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (S.isZero_quad 5 _ (Or.inl (by norm_num)))
      exact Module.finrank_zero_of_subsingleton
    rw [Finset.sum_range_succ (n := 3), Finset.sum_range_succ (n := 2),
      Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0),
      Finset.sum_range_zero, h0, h3, h5]
    simp only [zero_add, add_zero]
    exact h4
  -- ## `dim H⁴(X) ≥ 1`
  obtain ⟨g3, hg3⟩ := k4_exists_ne_zero (𝕜 := ZMod 2) hF3
  let y : S.E 2 ((0 : ℤ), (3 : ℤ)) := (e2 0 3 (by omega) (by omega)).inv.hom
    (one (ZMod 2) X ⊗ₜ[ZMod 2] g3)
  have hy0 : y ≠ 0 := k4_e2_inv_tmul_ne_zero (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀)
    (e2 := e2 0 3 (by omega) (by omega)) (one_ne_zero_of_finrank_one hB0) hg3
  have hdy : (S.d 2 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 2)).hom y = 0 := by
    refine k4_d_apply_eq_zero S ?_ y
    rw [show ((0 : ℤ), (3 : ℤ)) + vr 2 = ((2 : ℤ), (2 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_left (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀) (N := N - 2)
      (hS := hIsS) (r := 2) (s := 2) (q := 2) (by norm_num) (by omega) (by omega) hB2
  let y1 : S.E 3 ((0 : ℤ), (3 : ℤ)) := S.proj 2 ((0 : ℤ), (3 : ℤ)) ⟨y, hdy⟩
  have hy10 : y1 ≠ 0 := by
    refine k4_proj_ne_zero S (r := 2) (by norm_num) ((0 : ℤ), (3 : ℤ)) hdy hy0 ?_
    rw [show ((0 : ℤ), (3 : ℤ)) - vr 2 = ((-2 : ℤ), (4 : ℤ)) from by ext <;> norm_num [vr]]
    exact S.isZero_quad 2 _ (Or.inl (by norm_num))
  have hdy1 : (S.d 3 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 3)).hom y1 = 0 := by
    refine k4_d_apply_eq_zero S ?_ y1
    rw [show ((0 : ℤ), (3 : ℤ)) + vr 3 = ((3 : ℤ), (1 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_right (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀) (N := N - 2)
      (hS := hIsS) (r := 3) (s := 3) (q := 1) (by norm_num) (by omega) (by omega) hF1
  let y2 : S.E 4 ((0 : ℤ), (3 : ℤ)) := S.proj 3 ((0 : ℤ), (3 : ℤ)) ⟨y1, hdy1⟩
  have hy20 : y2 ≠ 0 := by
    refine k4_proj_ne_zero S (r := 3) (by norm_num) ((0 : ℤ), (3 : ℤ)) hdy1 hy10 ?_
    rw [show ((0 : ℤ), (3 : ℤ)) - vr 3 = ((-3 : ℤ), (5 : ℤ)) from by ext <;> norm_num [vr]]
    exact S.isZero_quad 3 _ (Or.inl (by norm_num))
  have hd4y2 : (S.d 4 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 4)).hom y2 ≠ 0 := by
    intro hzero
    have hE5 : IsZero (S.E 5 ((0 : ℤ), (3 : ℤ))) :=
      hconv0 3 (by norm_num) (by omega)
        (ModuleCat.subsingleton_of_isZero (hE 3 (by norm_num) (by omega))) 0 3 (by norm_num)
    have hmem : y2 ∈ LinearMap.range (S.d 4 (((0 : ℤ), (3 : ℤ)) - vr 4) ((0 : ℤ), (3 : ℤ))).hom := by
      haveI : Subsingleton (S.E 5 ((0 : ℤ), (3 : ℤ))) := ModuleCat.subsingleton_of_isZero hE5
      have h0 : S.proj 4 ((0 : ℤ), (3 : ℤ)) ⟨y2, hzero⟩ = 0 := Subsingleton.elim _ _
      exact (S.proj_ker 4 ((0 : ℤ), (3 : ℤ)) (by norm_num) ⟨y2, hzero⟩).mp h0
    obtain ⟨z, hz⟩ := hmem
    haveI : Subsingleton (S.E 4 (((0 : ℤ), (3 : ℤ)) - vr 4)) := by
      rw [show ((0 : ℤ), (3 : ℤ)) - vr 4 = ((-4 : ℤ), (6 : ℤ)) from by ext <;> norm_num [vr]]
      exact ModuleCat.subsingleton_of_isZero (S.isZero_quad 4 _ (Or.inl (by norm_num)))
    rw [Subsingleton.elim z 0, map_zero] at hz
    exact hy20 hz.symm
  have hB4ge : 1 ≤ Module.finrank (ZMod 2) (Coh (ZMod 2) X 4) := by
    have hle : Module.finrank (ZMod 2) (S.E 4 ((4 : ℤ), (0 : ℤ))) ≤
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 4) := by
      have hh := hdimE2 4 0 (by omega) (by omega)
      rw [hF0, mul_one] at hh
      rw [← hh]
      exact k4_finrank_mono S ((4 : ℤ), (0 : ℤ)) 2 (by norm_num) 2 (fun k hk1 hk2 => by
        interval_cases k
        · exact hbox ((4 : ℤ), (0 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 1 ((4 : ℤ), (0 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 2 _ (by norm_num) (by norm_num) (by omega))
    have him : 1 ≤ Module.finrank (ZMod 2) (S.E 4 ((4 : ℤ), (0 : ℤ))) := by
      haveI : FiniteDimensional (ZMod 2) (S.E 4 (((0 : ℤ), (3 : ℤ)) + vr 4)) := by
        rw [show ((0 : ℤ), (3 : ℤ)) + vr 4 = ((4 : ℤ), (0 : ℤ)) from by ext <;> norm_num [vr]]
        exact hfin 2 ((4 : ℤ), (0 : ℤ)) (by norm_num) (by norm_num) (by omega)
      have hrange : LinearMap.range (S.d 4 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 4)).hom ≠ ⊥ := by
        intro hbot
        exact hd4y2 (by rw [LinearMap.range_eq_bot.mp hbot]; simp)
      have hge : 1 ≤ Module.finrank (ZMod 2) ↥(LinearMap.range
          (S.d 4 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 4)).hom) := by
        obtain ⟨z, hz⟩ := (Submodule.ne_bot_iff (LinearMap.range
          (S.d 4 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 4)).hom)).mp hrange
        have hsub : Submodule.span (ZMod 2) ({z} : Set (S.E 4 (((0 : ℤ), (3 : ℤ)) + vr 4))) ≤
            LinearMap.range (S.d 4 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 4)).hom :=
          Submodule.span_le.mpr (by rintro w rfl; exact hz.1)
        calc (1 : ℕ) = Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) ({z} : Set _)) :=
              (finrank_span_singleton hz.2).symm
          _ ≤ _ := Submodule.finrank_mono hsub
      exact hge.trans (Submodule.finrank_le _)
    exact him.trans hle
  have hB4 : Module.finrank (ZMod 2) (Coh (ZMod 2) X 4) = 1 := le_antisymm hB4le hB4ge
  -- ## `dim H⁵(X) ≤ 1`
  have hB5le : Module.finrank (ZMod 2) (Coh (ZMod 2) X 5) ≤ 1 := by
    have h := row0Refined (E := k4PathSpace x₀) (B := X) S (N - 2) hbox 5 (by omega)
    have h1 : Module.finrank (ZMod 2) (S.E (5 + 2) (((5 : ℕ) : ℤ), 0)) = 0 :=
      htop0 5 (by norm_num) (by omega)
    have h2 : Module.finrank (ZMod 2) (S.E 2 (((5 : ℕ) : ℤ), 0)) =
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 5) := hlhs0 5 (by omega)
    rw [h1, zero_add, h2] at h
    refine h.trans ?_
    have h0 : Module.finrank (ZMod 2) (S.E 2 (CohSS.sr 5 2)) = 0 := by
      rw [show CohSS.sr 5 2 = ((3 : ℤ), (1 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 2 ((3 : ℤ), (1 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (k4_isZero_E2_right (S := S) (p := k4PathFib x₀)
          (e₀ := k4PathBase x₀) (N := N - 2) (hS := hIsS) (s := 3) (q := 1)
          (by omega) (by omega) hF1)
      exact Module.finrank_zero_of_subsingleton
    have h3 : Module.finrank (ZMod 2) (S.E 3 (CohSS.sr 5 3)) = 0 := by
      rw [show CohSS.sr 5 3 = ((2 : ℤ), (2 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 3 ((2 : ℤ), (2 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (k4_isZero_E_left (S := S) (p := k4PathFib x₀)
          (e₀ := k4PathBase x₀) (N := N - 2) (hS := hIsS) (r := 3) (s := 2) (q := 2)
          (by norm_num) (by omega) (by omega) hB2)
      exact Module.finrank_zero_of_subsingleton
    have h4 : Module.finrank (ZMod 2) (S.E 4 (CohSS.sr 5 4)) = 0 := by
      rw [show CohSS.sr 5 4 = ((1 : ℤ), (3 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 4 ((1 : ℤ), (3 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (k4_isZero_E_left (S := S) (p := k4PathFib x₀)
          (e₀ := k4PathBase x₀) (N := N - 2) (hS := hIsS) (r := 4) (s := 1) (q := 3)
          (by norm_num) (by omega) (by omega) hB1)
      exact Module.finrank_zero_of_subsingleton
    have h5 : Module.finrank (ZMod 2) (S.E 5 (CohSS.sr 5 5)) ≤ 1 := by
      rw [show CohSS.sr 5 5 = ((0 : ℤ), (4 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      refine (k4_finrank_mono S ((0 : ℤ), (4 : ℤ)) 2 (by norm_num) 3 ?_).trans ?_
      · intro k hk1 hk2
        interval_cases k
        · exact hbox ((0 : ℤ), (4 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 1 ((0 : ℤ), (4 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 2 _ (by norm_num) (by norm_num) (by omega)
        · exact hfin 3 _ (by norm_num) (by norm_num) (by omega)
      · have hh := hdimE2 0 4 (by omega) (by omega)
        rw [hB0, one_mul] at hh
        exact hh.le.trans hF4
    have h6 : Module.finrank (ZMod 2) (S.E 6 (CohSS.sr 5 6)) = 0 := by
      rw [show CohSS.sr 5 6 = ((-1 : ℤ), (5 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 6 ((-1 : ℤ), (5 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (S.isZero_quad 6 _ (Or.inl (by norm_num)))
      exact Module.finrank_zero_of_subsingleton
    rw [Finset.sum_range_succ (n := 4), Finset.sum_range_succ (n := 3),
      Finset.sum_range_succ (n := 2), Finset.sum_range_succ (n := 1),
      Finset.sum_range_succ (n := 0), Finset.sum_range_zero, h0, h3, h4, h6]
    simp only [zero_add, add_zero]
    exact h5
  -- ## the transgression class of `H³(X)` and the square of `u`
  have hfin30 : FiniteDimensional (ZMod 2) (S.E 3 (((0 : ℤ), (2 : ℤ)) + vr 3)) :=
    hfin 1 ((3 : ℤ), (0 : ℤ)) (by norm_num) (by norm_num) (by omega)
  have hd3u1'' : (S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)).hom u1 ≠ 0 := hd3u1
  obtain ⟨a, ha⟩ := k4_exists_ne_zero (𝕜 := ZMod 2) hB3
  let i3 : S.E 2 ((3 : ℤ), (0 : ℤ)) := (e2 3 0 (by omega) (by omega)).inv.hom
    (a ⊗ₜ[ZMod 2] one (ZMod 2) (k4LoopSpace x₀))
  have hi3 : i3 ≠ 0 := k4_e2_inv_tmul_ne_zero (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀)
    (e2 := e2 3 0 (by omega) (by omega)) ha (one_ne_zero_of_finrank_one hF0)
  have hdi3 : (S.d 2 ((3 : ℤ), (0 : ℤ)) (((3 : ℤ), (0 : ℤ)) + vr 2)).hom i3 = 0 := by
    refine k4_d_apply_eq_zero S ?_ i3
    rw [show ((3 : ℤ), (0 : ℤ)) + vr 2 = ((5 : ℤ), (-1 : ℤ)) from by ext <;> norm_num [vr]]
    exact S.isZero_quad 2 _ (Or.inr (by norm_num))
  let i3p : S.E 3 (((0 : ℤ), (2 : ℤ)) + vr 3) := S.proj 2 ((3 : ℤ), (0 : ℤ)) ⟨i3, hdi3⟩
  have hi3p : i3p ≠ 0 := by
    refine k4_proj_ne_zero S (r := 2) (by norm_num) ((3 : ℤ), (0 : ℤ)) hdi3 hi3 ?_
    rw [show ((3 : ℤ), (0 : ℤ)) - vr 2 = ((1 : ℤ), (1 : ℤ)) from by ext <;> norm_num [vr]]
    exact h11
  have hdim30 : Module.finrank (ZMod 2) (S.E 3 (((0 : ℤ), (2 : ℤ)) + vr 3)) = 1 := by
    refine le_antisymm ?_ (k4_finrank_pos_of_ne_zero hi3p)
    have hh : Module.finrank (ZMod 2) (S.E 3 ((3 : ℤ), (0 : ℤ))) ≤ 1 := by
      refine (k4_finrank_mono S ((3 : ℤ), (0 : ℤ)) 2 (by norm_num) 1 (fun k hk1 hk2 => by
        interval_cases k
        · exact hbox ((3 : ℤ), (0 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin30)).trans ?_
      have hh := hdimE2 3 0 (by omega) (by omega)
      rw [hB3, hF0, mul_one] at hh
      exact hh.le
    exact hh
  obtain ⟨c, hc0, hcu⟩ : ∃ c : ZMod 2, c ≠ 0 ∧
      (S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)).hom u1 =
        c • i3p := by
    haveI := hfin30
    have hspan : Submodule.span (ZMod 2) ({i3p} : Set (S.E 3 (((0 : ℤ), (2 : ℤ)) + vr 3))) = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [finrank_span_singleton hi3p, hdim30]
    have hmem : (S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)).hom u1 ∈
        Submodule.span (ZMod 2) ({i3p} : Set (S.E 3 (((0 : ℤ), (2 : ℤ)) + vr 3))) := by
      rw [hspan]; trivial
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c', fun h0 => hd3u1'' (by rw [← hc', h0, zero_smul]), hc'.symm⟩
  -- ## `u2 = u·u ∈ E₂^{0,4}` is nonzero; `W = proj₂ u2 ∈ E₃^{0,4}` is a cycle for `d₃`
  let u2 : S.E 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) :=
    S.mul 2 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (2 : ℤ))
      (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) (by ext <;> simp) u u
  have hu2 : u2 ≠ 0 := by
    have hcl := hmul 0 2 0 2 (one (ZMod 2) X) f2 (one (ZMod 2) X) f2 (by omega) (by omega)
    rw [show (-1 : ZMod 2) = 1 from by decide, one_pow, one_smul] at hcl
    have h1 : cup (ZMod 2) X 0 0 (one (ZMod 2) X) (one (ZMod 2) X) = one (ZMod 2) X := by
      simpa using (hco (ZMod 2) 0 (one (ZMod 2) X)).2
    rw [h1] at hcl
    intro h0
    have h2 : one (ZMod 2) X ⊗ₜ[ZMod 2] cup (ZMod 2) (k4LoopSpace x₀) 2 2 f2 f2 = 0 := by
      have h3 : (e2 (0 + 0) (2 + 2) (by omega) (by omega)).inv.hom
          (one (ZMod 2) X ⊗ₜ[ZMod 2] cup (ZMod 2) (k4LoopSpace x₀) 2 2 f2 f2) = 0 := by
        rw [← hcl]; exact h0
      rw [← k4_iso_hom_inv_hom_apply (e2 (0 + 0) (2 + 2) (by omega) (by omega))
        (one (ZMod 2) X ⊗ₜ[ZMod 2] cup (ZMod 2) (k4LoopSpace x₀) 2 2 f2 f2), h3, map_zero]
    exact tmul_ne_zero_of_ne_zero (one_ne_zero_of_finrank_one hB0) (hFsq2 f2 hf2) h2
  let u2' : S.E 2 ((0 : ℤ), (4 : ℤ)) := u2
  have hdu2 : (S.d 2 ((0 : ℤ), (4 : ℤ)) (((0 : ℤ), (4 : ℤ)) + vr 2)).hom u2' = 0 := by
    refine k4_d_apply_eq_zero S ?_ u2'
    rw [show ((0 : ℤ), (4 : ℤ)) + vr 2 = ((2 : ℤ), (3 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_left (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀) (N := N - 2)
      (hS := hIsS) (r := 2) (s := 2) (q := 3) (by norm_num) (by omega) (by omega) hB2
  let W : S.E 3 ((0 : ℤ), (4 : ℤ)) := S.proj 2 ((0 : ℤ), (4 : ℤ)) ⟨u2', hdu2⟩
  have hWu : W = S.mul 3 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (4 : ℤ))
      (by ext <;> simp) u1 u1 :=
    S.proj_mul 2 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (4 : ℤ))
      (by ext <;> simp) ⟨u, hdu⟩ ⟨u, hdu⟩ ⟨u2', hdu2⟩ (by norm_num) rfl
  have hcommd3 : S.mul 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)
      (((0 : ℤ), (4 : ℤ)) + vr 3) (by ext <;> simp [vr]) u1 ((S.d 3 ((0 : ℤ), (2 : ℤ))
        (((0 : ℤ), (2 : ℤ)) + vr 3)).hom u1) =
      S.mul 3 (((0 : ℤ), (2 : ℤ)) + vr 3) ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (4 : ℤ)) + vr 3)
        (by ext <;> simp [vr]) ((S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)).hom u1) u1 :=
    hmc (k4PathFib x₀) (k4PathBase x₀) (N - 2) S hIsS 3 ((0 : ℤ), (2 : ℤ))
      (((0 : ℤ), (2 : ℤ)) + vr 3) (((0 : ℤ), (4 : ℤ)) + vr 3) (by ext <;> simp [vr]) u1
      ((S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)).hom u1) (by norm_num)
      (by simp only [Prod.fst_add, Prod.snd_add, Prod.fst_ofNat, Prod.snd_ofNat, vr]; omega)
      (by simp only [Prod.fst_add, Prod.snd_add, Prod.fst_ofNat, Prod.snd_ofNat, vr]; omega)
      (by simp only [Prod.fst_add, Prod.snd_add, Prod.fst_ofNat, Prod.snd_ofNat, vr]; omega)
      (by simp only [Prod.fst_add, Prod.snd_add, Prod.fst_ofNat, Prod.snd_ofNat, vr]; omega)
      (by simp only [Prod.fst_add, Prod.snd_add, Prod.fst_ofNat, Prod.snd_ofNat, vr]; omega)
      (by simp only [Prod.fst_add, Prod.snd_add, Prod.fst_ofNat, Prod.snd_ofNat, vr]; omega)
  have hd3W : (S.d 3 ((0 : ℤ), (4 : ℤ)) (((0 : ℤ), (4 : ℤ)) + vr 3)).hom W = 0 := by
    rw [hWu]
    rw [S.leibniz 3 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (4 : ℤ))
      (by ext <;> simp [vr]) u1 u1 (by norm_num)]
    rw [show (-1 : ZMod 2) = 1 from by decide, one_pow, one_smul]
    rw [S.mul_congr 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3) (((0 : ℤ), (4 : ℤ)) + vr 3)
      _ (by ext <;> simp [vr]) u1 ((S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)).hom u1),
      S.mul_congr 3 (((0 : ℤ), (2 : ℤ)) + vr 3) ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (4 : ℤ)) + vr 3)
      _ (by ext <;> simp [vr]) ((S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)).hom u1) u1]
    rw [hcommd3]
    rw [← two_smul (ZMod 2) (S.mul 3 (((0 : ℤ), (2 : ℤ)) + vr 3) ((0 : ℤ), (2 : ℤ))
        (((0 : ℤ), (4 : ℤ)) + vr 3) (by ext <;> simp [vr])
        ((S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)).hom u1) u1),
      show (2 : ZMod 2) = 0 from by decide, zero_smul]
  -- ## the crux for the column `(0,5)`: `d₃^{0,5} ≠ 0`
  have hdy1z : (S.d 3 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 3)).hom y1 = 0 := by
    refine k4_d_apply_eq_zero S ?_ y1
    rw [show ((0 : ℤ), (3 : ℤ)) + vr 3 = ((3 : ℤ), (1 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_right (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀) (N := N - 2)
      (hS := hIsS) (r := 3) (s := 3) (q := 1) (by norm_num) (by omega) (by omega) hF1
  let P : S.E 2 ((3 : ℤ), (3 : ℤ)) := S.mul 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (3 : ℤ))
    ((3 : ℤ), (3 : ℤ)) (by ext <;> simp) i3 y
  have hP0 : P ≠ 0 := by
    refine e2RowColMulNeZero3 S (k4PathFib x₀) (k4PathBase x₀) (N - 2) hIsS hco hB0 hF0
      (s := 3) (by omega) (by omega) i3 y hi3 hy0
  have hdP : (S.d 2 ((3 : ℤ), (3 : ℤ)) (((3 : ℤ), (3 : ℤ)) + vr 2)).hom P = 0 := by
    rw [show P = S.mul 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (3 : ℤ)) ((3 : ℤ), (3 : ℤ))
      (by ext <;> simp) i3 y from rfl]
    rw [S.leibniz 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (3 : ℤ)) ((3 : ℤ), (3 : ℤ))
      (by ext <;> simp) i3 y (by norm_num)]
    have h1 : (S.d 2 ((3 : ℤ), (0 : ℤ)) (((3 : ℤ), (0 : ℤ)) + vr 2)).hom i3 = 0 := by
      refine k4_d_apply_eq_zero S ?_ i3
      rw [show ((3 : ℤ), (0 : ℤ)) + vr 2 = ((5 : ℤ), (-1 : ℤ)) from by ext <;> norm_num [vr]]
      exact S.isZero_quad 2 _ (Or.inr (by norm_num))
    have h2 : (S.d 2 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 2)).hom y = 0 := hdy
    rw [h1, h2]
    simp
  let P3 : S.E 3 ((3 : ℤ), (3 : ℤ)) := S.proj 2 ((3 : ℤ), (3 : ℤ)) ⟨P, hdP⟩
  have hP3ne : P3 ≠ 0 := by
    refine k4_proj_ne_zero S (r := 2) (by norm_num) ((3 : ℤ), (3 : ℤ)) hdP hP0 ?_
    rw [show ((3 : ℤ), (3 : ℤ)) - vr 2 = ((1 : ℤ), (4 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_left (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀) (N := N - 2)
      (hS := hIsS) (r := 2) (s := 1) (q := 4) (by norm_num) (by omega) (by omega) hB1
  have hP3eq : P3 = S.mul 3 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (3 : ℤ)) ((3 : ℤ), (3 : ℤ))
      (by ext <;> simp) i3p y1 :=
    S.proj_mul 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (3 : ℤ)) ((3 : ℤ), (3 : ℤ))
      (by ext <;> simp) ⟨i3, hdi3⟩ ⟨y, hdy⟩ ⟨P, hdP⟩ (by norm_num) rfl
  let x5 : S.E 3 ((0 : ℤ), (5 : ℤ)) := S.mul 3 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (3 : ℤ))
    ((0 : ℤ), (5 : ℤ)) (by ext <;> simp) u1 y1
  have hd3x5 : (S.d 3 ((0 : ℤ), (5 : ℤ)) (((0 : ℤ), (5 : ℤ)) + vr 3)).hom x5 = c • P3 := by
    rw [show x5 = S.mul 3 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (3 : ℤ)) ((0 : ℤ), (5 : ℤ))
      (by ext <;> simp) u1 y1 from rfl]
    rw [S.leibniz 3 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (3 : ℤ)) ((0 : ℤ), (5 : ℤ))
      (by ext <;> simp) u1 y1 (by norm_num)]
    rw [show (-1 : ZMod 2) = 1 from by decide, one_pow, one_smul]
    have hy1z : (S.d 3 ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (3 : ℤ)) + vr 3)).hom y1 = 0 := hdy1z
    rw [hy1z, map_zero, add_zero]
    have hcu' : (S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)).hom u1 = c • i3p := hcu
    rw [hcu']
    simp only [map_smul]
    have hP3eq' : P3 = S.mul 3 (((0 : ℤ), (2 : ℤ)) + vr 3) ((0 : ℤ), (3 : ℤ))
        (((0 : ℤ), (5 : ℤ)) + vr 3) (by ext <;> simp [vr]) i3p y1 := hP3eq
    rw [hP3eq']
    exact congrArg (fun z => c • z)
      (S.mul_congr 3 (((0 : ℤ), (2 : ℤ)) + vr 3) ((0 : ℤ), (3 : ℤ)) (((0 : ℤ), (5 : ℤ)) + vr 3)
        _ (by ext <;> simp [vr]) i3p y1)
  have hd305 : ∃ z : S.E 3 ((0 : ℤ), (5 : ℤ)),
      (S.d 3 ((0 : ℤ), (5 : ℤ)) (((0 : ℤ), (5 : ℤ)) + vr 3)).hom z ≠ 0 :=
    ⟨x5, by rw [hd3x5]; exact smul_ne_zero hc0 hP3ne⟩
  -- ## the crux for the column `(0,6)`: `d₃^{0,6} ≠ 0`
  let P6 : S.E 2 ((3 : ℤ), (4 : ℤ)) := S.mul 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (4 : ℤ))
    ((3 : ℤ), (4 : ℤ)) (by ext <;> simp) i3 u2'
  have hP6ne : P6 ≠ 0 := by
    refine e2RowColMulNeZero4 S (k4PathFib x₀) (k4PathBase x₀) (N - 2) hIsS hco hB0 hF0
      (s := 3) (by omega) (by omega) i3 u2' hi3 hu2
  have hdP6 : (S.d 2 ((3 : ℤ), (4 : ℤ)) (((3 : ℤ), (4 : ℤ)) + vr 2)).hom P6 = 0 := by
    rw [show P6 = S.mul 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (4 : ℤ)) ((3 : ℤ), (4 : ℤ))
      (by ext <;> simp) i3 u2' from rfl]
    rw [S.leibniz 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (4 : ℤ)) ((3 : ℤ), (4 : ℤ))
      (by ext <;> simp) i3 u2' (by norm_num)]
    have h1 : (S.d 2 ((3 : ℤ), (0 : ℤ)) (((3 : ℤ), (0 : ℤ)) + vr 2)).hom i3 = 0 := hdi3
    have h2 : (S.d 2 ((0 : ℤ), (4 : ℤ)) (((0 : ℤ), (4 : ℤ)) + vr 2)).hom u2' = 0 := hdu2
    rw [h1, h2]
    simp
  let P63 : S.E 3 ((3 : ℤ), (4 : ℤ)) := S.proj 2 ((3 : ℤ), (4 : ℤ)) ⟨P6, hdP6⟩
  have hP63ne : P63 ≠ 0 := by
    refine k4_proj_ne_zero S (r := 2) (by norm_num) ((3 : ℤ), (4 : ℤ)) hdP6 hP6ne ?_
    rw [show ((3 : ℤ), (4 : ℤ)) - vr 2 = ((1 : ℤ), (5 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_left (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀) (N := N - 2)
      (hS := hIsS) (r := 2) (s := 1) (q := 5) (by norm_num) (by omega) (by omega) hB1
  have hP63eq : P63 = S.mul 3 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (4 : ℤ)) ((3 : ℤ), (4 : ℤ))
      (by ext <;> simp) i3p W :=
    S.proj_mul 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (4 : ℤ)) ((3 : ℤ), (4 : ℤ))
      (by ext <;> simp) ⟨i3, hdi3⟩ ⟨u2', hdu2⟩ ⟨P6, hdP6⟩ (by norm_num) rfl
  let x6 : S.E 3 ((0 : ℤ), (6 : ℤ)) := S.mul 3 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (4 : ℤ))
    ((0 : ℤ), (6 : ℤ)) (by ext <;> simp) u1 W
  have hd3x6 : (S.d 3 ((0 : ℤ), (6 : ℤ)) (((0 : ℤ), (6 : ℤ)) + vr 3)).hom x6 = c • P63 := by
    rw [show x6 = S.mul 3 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (4 : ℤ)) ((0 : ℤ), (6 : ℤ))
      (by ext <;> simp) u1 W from rfl]
    rw [S.leibniz 3 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (4 : ℤ)) ((0 : ℤ), (6 : ℤ))
      (by ext <;> simp) u1 W (by norm_num)]
    rw [show (-1 : ZMod 2) = 1 from by decide, one_pow, one_smul]
    have hW0 : (S.d 3 ((0 : ℤ), (4 : ℤ)) (((0 : ℤ), (4 : ℤ)) + vr 3)).hom W = 0 := hd3W
    rw [hW0, map_zero, add_zero]
    have hcu' : (S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)).hom u1 = c • i3p := hcu
    rw [hcu']
    simp only [map_smul]
    have hP63eq' : P63 = S.mul 3 (((0 : ℤ), (2 : ℤ)) + vr 3) ((0 : ℤ), (4 : ℤ))
        (((0 : ℤ), (6 : ℤ)) + vr 3) (by ext <;> simp [vr]) i3p W := hP63eq
    rw [hP63eq']
    exact congrArg (fun z => c • z)
      (S.mul_congr 3 (((0 : ℤ), (2 : ℤ)) + vr 3) ((0 : ℤ), (4 : ℤ)) (((0 : ℤ), (6 : ℤ)) + vr 3)
        _ (by ext <;> simp [vr]) i3p W)
  have hd306 : ∃ z : S.E 3 ((0 : ℤ), (6 : ℤ)),
      (S.d 3 ((0 : ℤ), (6 : ℤ)) (((0 : ℤ), (6 : ℤ)) + vr 3)).hom z ≠ 0 :=
    ⟨x6, by rw [hd3x6]; exact smul_ne_zero hc0 hP63ne⟩
  -- ## `dim E₆^{0,5} ≤ 1` and `E₄^{3,3} = 0` (from `d₃^{0,5} ≠ 0`)
  have hE305fin : FiniteDimensional (ZMod 2) (S.E 3 ((0 : ℤ), (5 : ℤ))) :=
    hfin 1 ((0 : ℤ), (5 : ℤ)) (by norm_num) (by norm_num) (by omega)
  have hE605 : Module.finrank (ZMod 2) (S.E 6 ((0 : ℤ), (5 : ℤ))) ≤ 1 := by
    haveI := hE305fin
    have hle : Module.finrank (ZMod 2) (S.E 4 ((0 : ℤ), (5 : ℤ))) ≤
        Module.finrank (ZMod 2) ↥(LinearMap.ker
          (S.d 3 ((0 : ℤ), (5 : ℤ)) (((0 : ℤ), (5 : ℤ)) + vr 3)).hom) :=
      k4_finrank_next_le_ker S (by norm_num) _ hE305fin
    have hmono : Module.finrank (ZMod 2) (S.E 6 ((0 : ℤ), (5 : ℤ))) ≤
        Module.finrank (ZMod 2) (S.E 4 ((0 : ℤ), (5 : ℤ))) :=
      k4_finrank_mono S ((0 : ℤ), (5 : ℤ)) 4 (by norm_num) 2 (fun k hk1 hk2 => by
        interval_cases k
        · exact hfin 2 ((0 : ℤ), (5 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 3 ((0 : ℤ), (5 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 4 ((0 : ℤ), (5 : ℤ)) (by norm_num) (by norm_num) (by omega))
    have hrk := LinearMap.finrank_range_add_finrank_ker
      (S.d 3 ((0 : ℤ), (5 : ℤ)) (((0 : ℤ), (5 : ℤ)) + vr 3)).hom
    have htop : Module.finrank (ZMod 2) (S.E 3 ((0 : ℤ), (5 : ℤ))) ≤ 2 := by
      have hle' := k4_finrank_mono S ((0 : ℤ), (5 : ℤ)) 2 (by norm_num) 1 (fun k hk1 hk2 => by
        interval_cases k
        · exact hbox ((0 : ℤ), (5 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hE305fin)
      have hh := hdimE2 0 5 (by omega) (by omega)
      rw [hB0, one_mul] at hh
      exact hle'.trans (hh.le.trans hF5)
    obtain ⟨z5, hz5⟩ := hd305
    have hrg : 1 ≤ Module.finrank (ZMod 2) ↥(LinearMap.range
        (S.d 3 ((0 : ℤ), (5 : ℤ)) (((0 : ℤ), (5 : ℤ)) + vr 3)).hom) := by
      have hz : (⟨(S.d 3 ((0 : ℤ), (5 : ℤ)) (((0 : ℤ), (5 : ℤ)) + vr 3)).hom z5,
          ⟨z5, rfl⟩⟩ : ↥(LinearMap.range (S.d 3 ((0 : ℤ), (5 : ℤ))
            (((0 : ℤ), (5 : ℤ)) + vr 3)).hom)) ≠ 0 := by
        intro hh
        exact hz5 (congrArg (fun w : ↥(LinearMap.range (S.d 3 ((0 : ℤ), (5 : ℤ))
          (((0 : ℤ), (5 : ℤ)) + vr 3)).hom) => (w : S.E 3 (((0 : ℤ), (5 : ℤ)) + vr 3))) hh)
      exact k4_finrank_pos_of_ne_zero hz
    omega
  have hE433 : Module.finrank (ZMod 2) (S.E 4 ((3 : ℤ), (3 : ℤ))) = 0 := by
    have hb : (((0 : ℤ), (5 : ℤ)) + vr 3) = ((3 : ℤ), (3 : ℤ)) := by ext <;> norm_num [vr]
    rw [← hb]
    haveI : FiniteDimensional (ZMod 2) (S.E 3 (((0 : ℤ), (5 : ℤ)) + vr 3)) :=
      hfin 1 (((0 : ℤ), (5 : ℤ)) + vr 3)
        (by simp only [Prod.fst_add, Prod.fst_ofNat, vr, Prod.snd_add, Prod.snd_ofNat]; omega)
        (by simp only [Prod.fst_add, Prod.fst_ofNat, vr, Prod.snd_add, Prod.snd_ofNat]; omega)
        (by simp only [Prod.fst_add, Prod.fst_ofNat, vr, Prod.snd_add, Prod.snd_ofNat]; omega)
    have hd3x5ne : (S.d 3 ((0 : ℤ), (5 : ℤ)) (((0 : ℤ), (5 : ℤ)) + vr 3)).hom x5 ≠ 0 := by
      rw [hd3x5]; exact smul_ne_zero hc0 hP3ne
    have hspan : Submodule.span (ZMod 2) ({((S.d 3 ((0 : ℤ), (5 : ℤ))
        (((0 : ℤ), (5 : ℤ)) + vr 3)).hom x5)} :
        Set (S.E 3 (((0 : ℤ), (5 : ℤ)) + vr 3))) = ⊤ := by
      have ha : (0 : ℤ) ≤ ((((0 : ℤ), (5 : ℤ)) + vr 3)).1 := by
        simp only [Prod.fst_add, Prod.fst_ofNat, vr, Prod.snd_add, Prod.snd_ofNat]; omega
      have hb2 : (0 : ℤ) ≤ ((((0 : ℤ), (5 : ℤ)) + vr 3)).2 := by
        simp only [Prod.fst_add, Prod.fst_ofNat, vr, Prod.snd_add, Prod.snd_ofNat]; omega
      have hcc : ((((0 : ℤ), (5 : ℤ)) + vr 3)).1 + ((((0 : ℤ), (5 : ℤ)) + vr 3)).2 ≤ ((N - 2 : ℕ) : ℤ) := by
        simp only [Prod.fst_add, Prod.fst_ofNat, vr, Prod.snd_add, Prod.snd_ofNat]; omega
      have hdim3b : Module.finrank (ZMod 2) (S.E 3 (((0 : ℤ), (5 : ℤ)) + vr 3)) = 1 := by
        have hle' := k4_finrank_mono S (((0 : ℤ), (5 : ℤ)) + vr 3) 2 (by norm_num) 1
          (fun k hk1 hk2 => by
            interval_cases k
            · exact hbox (((0 : ℤ), (5 : ℤ)) + vr 3) ha hb2 hcc
            · exact hfin 1 (((0 : ℤ), (5 : ℤ)) + vr 3) ha hb2 hcc)
        have hh := hdimE2 3 3 (by omega) (by omega)
        rw [hB3, hF3, mul_one] at hh
        exact le_antisymm (hle'.trans hh.le) (k4_finrank_pos_of_ne_zero hd3x5ne)
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [finrank_span_singleton hd3x5ne]
      exact hdim3b.symm
    have hz : ∀ z : ↥(LinearMap.ker (S.d 3 (((0 : ℤ), (5 : ℤ)) + vr 3)
        ((((0 : ℤ), (5 : ℤ)) + vr 3) + vr 3)).hom),
        S.proj 3 (((0 : ℤ), (5 : ℤ)) + vr 3) z = 0 := by
      intro z
      refine (S.proj_ker 3 (((0 : ℤ), (5 : ℤ)) + vr 3) (by norm_num) z).mpr ?_
      have hmem : ((z : S.E 3 (((0 : ℤ), (5 : ℤ)) + vr 3))) ∈ Submodule.span (ZMod 2)
          ({((S.d 3 ((0 : ℤ), (5 : ℤ)) (((0 : ℤ), (5 : ℤ)) + vr 3)).hom x5)} : Set _) := by
        rw [hspan]; trivial
      obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hmem
      rw [← hcc]
      exact Submodule.smul_mem _ cc (⟨x5, rfl⟩ : ((S.d 3 ((((0 : ℤ), (5 : ℤ)) + vr 3) - vr 3)
        (((0 : ℤ), (5 : ℤ)) + vr 3)).hom x5) ∈ LinearMap.range (S.d 3
          ((((0 : ℤ), (5 : ℤ)) + vr 3) - vr 3) (((0 : ℤ), (5 : ℤ)) + vr 3)).hom)
    have hproj0 : S.proj 3 (((0 : ℤ), (5 : ℤ)) + vr 3) = 0 := LinearMap.ext hz
    have heq : Module.finrank (ZMod 2) (S.E 4 (((0 : ℤ), (5 : ℤ)) + vr 3)) =
        Module.finrank (ZMod 2) ↥(LinearMap.range (S.proj 3 (((0 : ℤ), (5 : ℤ)) + vr 3))) :=
      (LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _
        (LinearMap.range_eq_top.mpr (S.proj_surj 3 (((0 : ℤ), (5 : ℤ)) + vr 3) (by norm_num)))
        ≪≫ₗ Submodule.topEquiv)).symm
    rw [heq, hproj0, LinearMap.range_zero]
    exact finrank_bot (ZMod 2) (S.E 4 (((0 : ℤ), (5 : ℤ)) + vr 3))
  -- ## `dim E₇^{0,6} ≤ 1` (from `d₃^{0,6} ≠ 0`)
  have hE306fin : FiniteDimensional (ZMod 2) (S.E 3 ((0 : ℤ), (6 : ℤ))) :=
    hfin 1 ((0 : ℤ), (6 : ℤ)) (by norm_num) (by norm_num) (by omega)
  have hE706 : Module.finrank (ZMod 2) (S.E 7 ((0 : ℤ), (6 : ℤ))) ≤ 1 := by
    haveI := hE306fin
    have hle : Module.finrank (ZMod 2) (S.E 4 ((0 : ℤ), (6 : ℤ))) ≤
        Module.finrank (ZMod 2) ↥(LinearMap.ker
          (S.d 3 ((0 : ℤ), (6 : ℤ)) (((0 : ℤ), (6 : ℤ)) + vr 3)).hom) :=
      k4_finrank_next_le_ker S (by norm_num) _ hE306fin
    have hmono : Module.finrank (ZMod 2) (S.E 7 ((0 : ℤ), (6 : ℤ))) ≤
        Module.finrank (ZMod 2) (S.E 4 ((0 : ℤ), (6 : ℤ))) :=
      k4_finrank_mono S ((0 : ℤ), (6 : ℤ)) 4 (by norm_num) 3 (fun k hk1 hk2 => by
        interval_cases k
        · exact hfin 2 ((0 : ℤ), (6 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 3 ((0 : ℤ), (6 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 4 ((0 : ℤ), (6 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 5 ((0 : ℤ), (6 : ℤ)) (by norm_num) (by norm_num) (by omega))
    have hrk := LinearMap.finrank_range_add_finrank_ker
      (S.d 3 ((0 : ℤ), (6 : ℤ)) (((0 : ℤ), (6 : ℤ)) + vr 3)).hom
    have htop : Module.finrank (ZMod 2) (S.E 3 ((0 : ℤ), (6 : ℤ))) ≤ 2 := by
      have hle' := k4_finrank_mono S ((0 : ℤ), (6 : ℤ)) 2 (by norm_num) 1 (fun k hk1 hk2 => by
        interval_cases k
        · exact hbox ((0 : ℤ), (6 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hE306fin)
      have hh := hdimE2 0 6 (by omega) (by omega)
      rw [hB0, one_mul] at hh
      exact hle'.trans (hh.le.trans hF6)
    obtain ⟨z6, hz6⟩ := hd306
    have hrg : 1 ≤ Module.finrank (ZMod 2) ↥(LinearMap.range
        (S.d 3 ((0 : ℤ), (6 : ℤ)) (((0 : ℤ), (6 : ℤ)) + vr 3)).hom) := by
      have hz : (⟨(S.d 3 ((0 : ℤ), (6 : ℤ)) (((0 : ℤ), (6 : ℤ)) + vr 3)).hom z6,
          ⟨z6, rfl⟩⟩ : ↥(LinearMap.range (S.d 3 ((0 : ℤ), (6 : ℤ))
            (((0 : ℤ), (6 : ℤ)) + vr 3)).hom)) ≠ 0 := by
        intro hh
        exact hz6 (congrArg (fun w : ↥(LinearMap.range (S.d 3 ((0 : ℤ), (6 : ℤ))
          (((0 : ℤ), (6 : ℤ)) + vr 3)).hom) => (w : S.E 3 (((0 : ℤ), (6 : ℤ)) + vr 3))) hh)
      exact k4_finrank_pos_of_ne_zero hz
    omega
  have hB6le : Module.finrank (ZMod 2) (Coh (ZMod 2) X 6) ≤ 2 := by
    have h := row0Refined (E := k4PathSpace x₀) (B := X) S (N - 2) hbox 6 (by omega)
    have h1 : Module.finrank (ZMod 2) (S.E (6 + 2) (((6 : ℕ) : ℤ), 0)) = 0 :=
      htop0 6 (by norm_num) (by omega)
    have h2 : Module.finrank (ZMod 2) (S.E 2 (((6 : ℕ) : ℤ), 0)) =
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 6) := hlhs0 6 (by omega)
    have h1' : Module.finrank (ZMod 2) (S.E (6 + 2) (((6 : ℕ) : ℤ), 0)) = 0 := h1
    have h2' : Module.finrank (ZMod 2) (S.E 2 (((6 : ℕ) : ℤ), 0)) =
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 6) := h2
    rw [h1', zero_add, h2'] at h
    refine h.trans ?_
    have h0 : Module.finrank (ZMod 2) (S.E 2 (CohSS.sr 6 2)) = 0 := by
      rw [show CohSS.sr 6 2 = ((4 : ℤ), (1 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 2 ((4 : ℤ), (1 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (k4_isZero_E2_right (S := S) (p := k4PathFib x₀)
          (e₀ := k4PathBase x₀) (N := N - 2) (hS := hIsS) (s := 4) (q := 1)
          (by omega) (by omega) hF1)
      exact Module.finrank_zero_of_subsingleton
    have h3 : Module.finrank (ZMod 2) (S.E 3 (CohSS.sr 6 3)) ≤ 1 := by
      rw [show CohSS.sr 6 3 = ((3 : ℤ), (2 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      refine (k4_finrank_mono S ((3 : ℤ), (2 : ℤ)) 2 (by norm_num) 1 (fun k hk1 hk2 => by
        interval_cases k
        · exact hbox ((3 : ℤ), (2 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 1 ((3 : ℤ), (2 : ℤ)) (by norm_num) (by norm_num) (by omega))).trans ?_
      have hh := hdimE2 3 2 (by omega) (by omega)
      rw [hB3, hF2, mul_one] at hh
      exact hh.le
    have h4 : Module.finrank (ZMod 2) (S.E 4 (CohSS.sr 6 4)) = 0 := by
      rw [show CohSS.sr 6 4 = ((2 : ℤ), (3 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 4 ((2 : ℤ), (3 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (k4_isZero_E_left (S := S) (p := k4PathFib x₀)
          (e₀ := k4PathBase x₀) (N := N - 2) (hS := hIsS) (r := 4) (s := 2) (q := 3)
          (by norm_num) (by omega) (by omega) hB2)
      exact Module.finrank_zero_of_subsingleton
    have h5 : Module.finrank (ZMod 2) (S.E 5 (CohSS.sr 6 5)) = 0 := by
      rw [show CohSS.sr 6 5 = ((1 : ℤ), (4 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 5 ((1 : ℤ), (4 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (k4_isZero_E_left (S := S) (p := k4PathFib x₀)
          (e₀ := k4PathBase x₀) (N := N - 2) (hS := hIsS) (r := 5) (s := 1) (q := 4)
          (by norm_num) (by omega) (by omega) hB1)
      exact Module.finrank_zero_of_subsingleton
    have h6 : Module.finrank (ZMod 2) (S.E 6 (CohSS.sr 6 6)) ≤ 1 := by
      rw [show CohSS.sr 6 6 = ((0 : ℤ), (5 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      exact hE605
    have h7 : Module.finrank (ZMod 2) (S.E 7 (CohSS.sr 6 7)) = 0 := by
      rw [show CohSS.sr 6 7 = ((-1 : ℤ), (6 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 7 ((-1 : ℤ), (6 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (S.isZero_quad 7 _ (Or.inl (by norm_num)))
      exact Module.finrank_zero_of_subsingleton
    rw [Finset.sum_range_succ (n := 5), Finset.sum_range_succ (n := 4),
      Finset.sum_range_succ (n := 3), Finset.sum_range_succ (n := 2),
      Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0),
      Finset.sum_range_zero, h0, h4, h5, h7]
    simp only [zero_add, add_zero]
    linarith
  have hB7le : Module.finrank (ZMod 2) (Coh (ZMod 2) X 7) ≤ 2 := by
    have h := row0Refined (E := k4PathSpace x₀) (B := X) S (N - 2) hbox 7 (by omega)
    have h1 : Module.finrank (ZMod 2) (S.E (7 + 2) (((7 : ℕ) : ℤ), 0)) = 0 :=
      htop0 7 (by norm_num) (by omega)
    have h2 : Module.finrank (ZMod 2) (S.E 2 (((7 : ℕ) : ℤ), 0)) =
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 7) := hlhs0 7 (by omega)
    have h1' : Module.finrank (ZMod 2) (S.E (7 + 2) (((7 : ℕ) : ℤ), 0)) = 0 := h1
    have h2' : Module.finrank (ZMod 2) (S.E 2 (((7 : ℕ) : ℤ), 0)) =
        Module.finrank (ZMod 2) (Coh (ZMod 2) X 7) := h2
    rw [h1', zero_add, h2'] at h
    refine h.trans ?_
    have h0 : Module.finrank (ZMod 2) (S.E 2 (CohSS.sr 7 2)) = 0 := by
      rw [show CohSS.sr 7 2 = ((5 : ℤ), (1 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 2 ((5 : ℤ), (1 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (k4_isZero_E2_right (S := S) (p := k4PathFib x₀)
          (e₀ := k4PathBase x₀) (N := N - 2) (hS := hIsS) (s := 5) (q := 1)
          (by omega) (by omega) hF1)
      exact Module.finrank_zero_of_subsingleton
    have h3 : Module.finrank (ZMod 2) (S.E 3 (CohSS.sr 7 3)) ≤ 1 := by
      rw [show CohSS.sr 7 3 = ((4 : ℤ), (2 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      refine (k4_finrank_mono S ((4 : ℤ), (2 : ℤ)) 2 (by norm_num) 1 (fun k hk1 hk2 => by
        interval_cases k
        · exact hbox ((4 : ℤ), (2 : ℤ)) (by norm_num) (by norm_num) (by omega)
        · exact hfin 1 ((4 : ℤ), (2 : ℤ)) (by norm_num) (by norm_num) (by omega))).trans ?_
      have hh := hdimE2 4 2 (by omega) (by omega)
      rw [hB4, hF2, mul_one] at hh
      exact hh.le
    have h4 : Module.finrank (ZMod 2) (S.E 4 (CohSS.sr 7 4)) = 0 := by
      rw [show CohSS.sr 7 4 = ((3 : ℤ), (3 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      exact hE433
    have h5 : Module.finrank (ZMod 2) (S.E 5 (CohSS.sr 7 5)) = 0 := by
      rw [show CohSS.sr 7 5 = ((2 : ℤ), (4 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 5 ((2 : ℤ), (4 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (k4_isZero_E_left (S := S) (p := k4PathFib x₀)
          (e₀ := k4PathBase x₀) (N := N - 2) (hS := hIsS) (r := 5) (s := 2) (q := 4)
          (by norm_num) (by omega) (by omega) hB2)
      exact Module.finrank_zero_of_subsingleton
    have h6 : Module.finrank (ZMod 2) (S.E 6 (CohSS.sr 7 6)) = 0 := by
      rw [show CohSS.sr 7 6 = ((1 : ℤ), (5 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 6 ((1 : ℤ), (5 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (k4_isZero_E_left (S := S) (p := k4PathFib x₀)
          (e₀ := k4PathBase x₀) (N := N - 2) (hS := hIsS) (r := 6) (s := 1) (q := 5)
          (by norm_num) (by omega) (by omega) hB1)
      exact Module.finrank_zero_of_subsingleton
    have h7 : Module.finrank (ZMod 2) (S.E 7 (CohSS.sr 7 7)) ≤ 1 := by
      rw [show CohSS.sr 7 7 = ((0 : ℤ), (6 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      exact hE706
    have h8 : Module.finrank (ZMod 2) (S.E 8 (CohSS.sr 7 8)) = 0 := by
      rw [show CohSS.sr 7 8 = ((-1 : ℤ), (7 : ℤ)) from by ext <;> norm_num [CohSS.sr]]
      haveI : Subsingleton (S.E 8 ((-1 : ℤ), (7 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero (S.isZero_quad 8 _ (Or.inl (by norm_num)))
      exact Module.finrank_zero_of_subsingleton
    rw [Finset.sum_range_succ (n := 6), Finset.sum_range_succ (n := 5),
      Finset.sum_range_succ (n := 4), Finset.sum_range_succ (n := 3),
      Finset.sum_range_succ (n := 2), Finset.sum_range_succ (n := 1),
      Finset.sum_range_succ (n := 0), Finset.sum_range_zero, h0, h4, h5, h6, h8]
    simp only [zero_add, add_zero]
    linarith
  -- ## the cup square
  -- ### `E_3^{0,4}` is one-dimensional, spanned by the class `W = u · u`, and `d₃ W = 0`
  have hWne : W ≠ 0 := by
    refine k4_proj_ne_zero S (r := 2) (by norm_num) ((0 : ℤ), (4 : ℤ)) hdu2 hu2 ?_
    rw [show ((0 : ℤ), (4 : ℤ)) - vr 2 = ((-2 : ℤ), (5 : ℤ)) from by ext <;> norm_num [vr]]
    exact S.isZero_quad 2 _ (Or.inl (by norm_num))
  haveI hfd04 : FiniteDimensional (ZMod 2) (S.E 3 ((0 : ℤ), (4 : ℤ))) :=
    hfin 1 ((0 : ℤ), (4 : ℤ)) (by norm_num) (by norm_num) (by omega)
  have hdim04 : Module.finrank (ZMod 2) (S.E 3 ((0 : ℤ), (4 : ℤ))) = 1 := by
    refine le_antisymm ?_ (k4_finrank_pos_of_ne_zero hWne)
    have h2 : Module.finrank (ZMod 2) (S.E 2 ((0 : ℤ), (4 : ℤ))) ≤ 1 := by
      have hh := hdimE2 0 4 (by omega) (by omega)
      rw [hB0, one_mul] at hh
      exact hh.le.trans hF4
    exact (S.finrank_succ_le (r := 2) (by norm_num) ((0 : ℤ), (4 : ℤ))
      (hbox ((0 : ℤ), (4 : ℤ)) (by norm_num) (by norm_num) (by omega))).trans h2
  have hd3W' : (S.d 3 ((0 : ℤ), (4 : ℤ)) ((3 : ℤ), (2 : ℤ))).hom W = 0 := hd3W
  have hd3E04 : (S.d 3 ((0 : ℤ), (4 : ℤ)) ((3 : ℤ), (2 : ℤ))).hom = 0 := by
    have hspan04 : Submodule.span (ZMod 2) ({W} : Set (S.E 3 ((0 : ℤ), (4 : ℤ)))) = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [finrank_span_singleton hWne, hdim04]
    ext x
    have hx : x ∈ Submodule.span (ZMod 2) ({W} : Set (S.E 3 ((0 : ℤ), (4 : ℤ)))) := by
      rw [hspan04]; trivial
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [map_smul, hd3W', smul_zero, LinearMap.zero_apply]
  -- ### the nonzero cycle `Q = i3 · u ∈ E₂^{3,2}`
  let h32 : (((3 : ℤ), (0 : ℤ)) + ((0 : ℤ), (2 : ℤ))) = ((3 : ℤ), (2 : ℤ)) := by ext <;> simp
  let Q : S.E 2 ((3 : ℤ), (2 : ℤ)) :=
    S.mul 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (2 : ℤ)) ((3 : ℤ), (2 : ℤ)) h32 i3 u
  have hQne : Q ≠ 0 :=
    e2RowColMulNeZero2 S (k4PathFib x₀) (k4PathBase x₀) (N - 2) hIsS hco hB0 hF0
      (s := 3) (by omega) (by omega) i3 u hi3 hu0
  have hQcyc : (S.d 2 ((3 : ℤ), (2 : ℤ)) (((3 : ℤ), (2 : ℤ)) + vr 2)).hom Q = 0 := by
    rw [show Q = S.mul 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (2 : ℤ)) ((3 : ℤ), (2 : ℤ)) h32 i3 u
      from rfl, S.leibniz 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (2 : ℤ)) ((3 : ℤ), (2 : ℤ)) h32 i3 u
      (by norm_num), hdi3, hdu]
    simp
  let Q3 : S.E 3 ((3 : ℤ), (2 : ℤ)) := S.proj 2 ((3 : ℤ), (2 : ℤ)) ⟨Q, hQcyc⟩
  have hQ3ne : Q3 ≠ 0 := by
    refine k4_proj_ne_zero S (r := 2) (by norm_num) ((3 : ℤ), (2 : ℤ)) hQcyc hQne ?_
    rw [show ((3 : ℤ), (2 : ℤ)) - vr 2 = ((1 : ℤ), (3 : ℤ)) from by ext <;> norm_num [vr]]
    exact k4_isZero_E_left (S := S) (p := k4PathFib x₀) (e₀ := k4PathBase x₀) (N := N - 2)
      (hS := hIsS) (r := 2) (s := 1) (q := 3) (by norm_num) (by omega) (by omega) hB1
  have hQ3eq : Q3 = S.mul 3 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (2 : ℤ)) ((3 : ℤ), (2 : ℤ)) h32 i3p u1 :=
    S.proj_mul 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (2 : ℤ)) ((3 : ℤ), (2 : ℤ)) h32
      ⟨i3, hdi3⟩ ⟨u, hdu⟩ ⟨Q, hQcyc⟩ (by norm_num) rfl
  -- ### `d₃` is injective on `E₃^{3,2}`: nothing survives to `E₇^{3,2} = 0`
  have hd3Q3 : (S.d 3 ((3 : ℤ), (2 : ℤ)) (((3 : ℤ), (2 : ℤ)) + vr 3)).hom Q3 ≠ 0 := by
    intro h0
    have hQ4ne : S.proj 3 ((3 : ℤ), (2 : ℤ)) ⟨Q3, h0⟩ ≠ 0 := by
      intro hp0
      have hmem := (S.proj_ker 3 ((3 : ℤ), (2 : ℤ)) (by norm_num) ⟨Q3, h0⟩).mp hp0
      rw [show ((3 : ℤ), (2 : ℤ)) - vr 3 = ((0 : ℤ), (4 : ℤ)) from by ext <;> norm_num [vr]] at hmem
      rw [hd3E04, LinearMap.range_zero, Submodule.mem_bot] at hmem
      exact hQ3ne hmem
    have hsrc : ∀ k : ℕ, 4 ≤ k → IsZero (S.E k (((3 : ℤ), (2 : ℤ)) - vr k)) := by
      intro k hk
      refine S.isZero_quad k _ (Or.inl ?_)
      have hk' : (4 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
      simp only [vr, Prod.fst_sub, Prod.fst_ofNat, Prod.snd_sub, Prod.snd_ofNat]
      linarith
    have htgt : ∀ k : ℕ, 4 + 1 ≤ k → IsZero (S.E k (((3 : ℤ), (2 : ℤ)) + vr k)) := by
      intro k hk
      refine S.isZero_quad k _ (Or.inr ?_)
      have hk' : (4 : ℤ) ≤ (k : ℤ) := by exact_mod_cast (by omega : 4 ≤ k)
      simp only [vr, Prod.fst_add, Prod.fst_ofNat, Prod.snd_add, Prod.snd_ofNat]
      linarith
    have hcyc4 : (S.d 4 ((3 : ℤ), (2 : ℤ)) (((3 : ℤ), (2 : ℤ)) + vr 4)).hom
        (S.proj 3 ((3 : ℤ), (2 : ℤ)) ⟨Q3, h0⟩) = 0 := by
      refine k4_d_apply_eq_zero S ?_ _
      refine S.isZero_quad 4 _ (Or.inr ?_)
      simp only [vr, Prod.snd_add, Prod.snd_ofNat]
      norm_num
    exact S.not_isZero_of_survives (r := 4) (by norm_num) ((3 : ℤ), (2 : ℤ))
      (S.proj 3 ((3 : ℤ), (2 : ℤ)) ⟨Q3, h0⟩) hcyc4 hQ4ne hsrc htgt 3
      (hconv0 5 (by norm_num) (by omega)
        (ModuleCat.subsingleton_of_isZero (hE 5 (by norm_num) (by omega))) 3 2 (by norm_num))
  -- ### Leibniz: `d₃ Q3 = c • (i3p · i3p)`, hence `i3p · i3p ≠ 0`
  have hdi3p : (S.d 3 ((3 : ℤ), (0 : ℤ)) (((3 : ℤ), (0 : ℤ)) + vr 3)).hom i3p = 0 := by
    refine k4_d_apply_eq_zero S ?_ i3p
    rw [show ((3 : ℤ), (0 : ℤ)) + vr 3 = ((6 : ℤ), (-2 : ℤ)) from by ext <;> norm_num [vr]]
    exact S.isZero_quad 3 _ (Or.inr (by norm_num))
  have hd3Q3eq : (S.d 3 ((3 : ℤ), (2 : ℤ)) (((3 : ℤ), (2 : ℤ)) + vr 3)).hom Q3
      = c • S.mul 3 ((3 : ℤ), (0 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)
          (((3 : ℤ), (2 : ℤ)) + vr 3) (by ext <;> norm_num [vr]) i3p i3p := by
    rw [hQ3eq,
      S.leibniz 3 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (2 : ℤ)) ((3 : ℤ), (2 : ℤ)) h32 i3p u1 (by norm_num),
      hdi3p, hcu]
    simp only [map_zero, map_smul]
    rw [show (-1 : ZMod 2) = 1 from by decide, one_pow, one_smul]
    simp
  have hMne : S.mul 3 ((3 : ℤ), (0 : ℤ)) (((0 : ℤ), (2 : ℤ)) + vr 3)
      (((3 : ℤ), (2 : ℤ)) + vr 3) (by ext <;> norm_num [vr]) i3p i3p ≠ 0 := by
    intro h0
    exact hd3Q3 (hd3Q3eq.trans ((congrArg (fun z => c • z) h0).trans (smul_zero c)))
  let h33 : (((3 : ℤ), (0 : ℤ)) + ((3 : ℤ), (0 : ℤ))) = ((6 : ℤ), (0 : ℤ)) := by ext <;> simp
  have hii : S.mul 3 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ)) ((6 : ℤ), (0 : ℤ)) h33 i3p i3p ≠ 0 := by
    intro h0
    exact hMne ((S.mul_congr 3 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ)) ((6 : ℤ), (0 : ℤ))
      (by ext <;> simp) h33 i3p i3p).trans h0)
  -- ### `i3 · i3 ∈ E₂^{6,0}` is nonzero
  let W2 : S.E 2 ((6 : ℤ), (0 : ℤ)) :=
    S.mul 2 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ)) ((6 : ℤ), (0 : ℤ)) h33 i3 i3
  have hW2cyc : (S.d 2 ((6 : ℤ), (0 : ℤ)) (((6 : ℤ), (0 : ℤ)) + vr 2)).hom W2 = 0 := by
    rw [show W2 = S.mul 2 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ)) ((6 : ℤ), (0 : ℤ)) h33 i3 i3
        from rfl,
      S.leibniz 2 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ)) ((6 : ℤ), (0 : ℤ)) h33 i3 i3 (by norm_num),
      hdi3]
    simp
  have hW2ne : W2 ≠ 0 := by
    intro h0
    have hproj := S.proj_mul 2 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ)) ((6 : ℤ), (0 : ℤ)) h33
      ⟨i3, hdi3⟩ ⟨i3, hdi3⟩ ⟨W2, hW2cyc⟩ (by norm_num) rfl
    have hz : S.proj 2 ((6 : ℤ), (0 : ℤ)) ⟨W2, hW2cyc⟩ = 0 := by
      have hsub : (⟨W2, hW2cyc⟩ : LinearMap.ker (S.d 2 ((6 : ℤ), (0 : ℤ))
          (((6 : ℤ), (0 : ℤ)) + vr 2)).hom) = 0 := Subtype.ext h0
      rw [hsub]
      simp
    exact hii (hproj.symm.trans hz)
  -- ### transfer to cohomology: `a ⌣ a ≠ 0`
  have hcup : cup (ZMod 2) X 3 3 a a ≠ 0 := by
    intro hc
    have h1 : cup (ZMod 2) (k4LoopSpace x₀) 0 0 (one (ZMod 2) (k4LoopSpace x₀))
        (one (ZMod 2) (k4LoopSpace x₀)) = one (ZMod 2) (k4LoopSpace x₀) := by
      simpa using (hco (ZMod 2) 0 (one (ZMod 2) (k4LoopSpace x₀))).2
    have h2 : (e2 (3 + 3) (0 + 0) (by omega) (by omega)).inv.hom
        (cup (ZMod 2) X 3 3 a a ⊗ₜ[ZMod 2] cup (ZMod 2) (k4LoopSpace x₀) 0 0
          (one (ZMod 2) (k4LoopSpace x₀)) (one (ZMod 2) (k4LoopSpace x₀))) = 0 := by
      set_option backward.isDefEq.respectTransparency true in set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in set_option backward.isDefEq.respectTransparency.types true in  -- v435decl
      (rw [hc, h1]; simp)
    have h4 : (-1 : ZMod 2) ^ (0 * 3) • (e2 (3 + 3) (0 + 0) (by omega) (by omega)).inv.hom
        (cup (ZMod 2) X 3 3 a a ⊗ₜ[ZMod 2] cup (ZMod 2) (k4LoopSpace x₀) 0 0
          (one (ZMod 2) (k4LoopSpace x₀)) (one (ZMod 2) (k4LoopSpace x₀))) = 0 := by
      rw [show (-1 : ZMod 2) ^ (0 * 3) = 1 from by decide, one_smul]
      exact h2
    exact hW2ne ((hmul 3 0 3 0 a (one (ZMod 2) (k4LoopSpace x₀)) a
      (one (ZMod 2) (k4LoopSpace x₀)) (by omega) (by omega)).trans h4)
  -- ### every nonzero class of `H³(X)` has nonzero square
  have hcupGen : ∀ a' : Coh (ZMod 2) X 3, a' ≠ 0 → cup (ZMod 2) X 3 3 a' a' ≠ 0 := by
    intro a' ha'
    obtain ⟨k, hk⟩ := smul_surjective_of_finrank_one hB3 a ha a'
    have hk0 : k ≠ 0 := by
      intro hk0
      exact ha' (by rw [hk, hk0, zero_smul])
    have hsq : cup (ZMod 2) X 3 3 (k • a) (k • a) = (k * k) • cup (ZMod 2) X 3 3 a a := by
      have h1 : (cup (ZMod 2) X 3 3) (k • a) = k • ((cup (ZMod 2) X 3 3) a) :=
        map_smul (cup (ZMod 2) X 3 3) k a
      have h2 : (k • ((cup (ZMod 2) X 3 3) a)) (k • a)
          = k • (((cup (ZMod 2) X 3 3) a) (k • a)) :=
        LinearMap.smul_apply k ((cup (ZMod 2) X 3 3) a) (k • a)
      have h3 : ((cup (ZMod 2) X 3 3) a) (k • a) = k • (((cup (ZMod 2) X 3 3) a) a) :=
        map_smul ((cup (ZMod 2) X 3 3) a) k a
      rw [h1, h2, h3, ← smul_smul]
    rw [hk, hsq]
    exact smul_ne_zero (mul_ne_zero hk0 hk0) hcup
  exact ⟨hB3, hB4, hB5le, hB6le, hB7le, hcupGen⟩
