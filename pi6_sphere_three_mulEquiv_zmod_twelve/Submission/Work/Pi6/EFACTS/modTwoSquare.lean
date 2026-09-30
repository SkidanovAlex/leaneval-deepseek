import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EFACTS.Basic
import Submission.Work.Pi6.EFACTS.FibreRing
import Submission.Work.Pi6.EFACTS.WangExact
import Submission.Work.StemsB.WangSequenceShiftedR
import Submission.Work.StemsB.WangDerivationR
import Submission.Work.Pi6.EFACTS.MSSSetup
import Submission.Work.Pi6.EFACTS.sphModelSimplyConn
import Submission.Work.Pi6.BOCK.bocksteinLES
import Submission.Work.Pi6.K2Z.finiteDimCoh
import Submission.Work.Pi6.K2Z.transfer
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.FGThm.sphereFG
import Submission.Work.Pi6.EMM2.SSKit
import Submission.Work.Pi6.EMM2.SerreKit
import Submission.Work.Pi6.EMM2.twoRowKit
import Submission.Work.Pi6.EMM2.K4Kit
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.StemsB.HurewiczFibration
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The nonzero class of `H⁴(S³⟨3⟩; 𝔽₂)` has nonzero square

`Work.Pi6.EFACTS.modTwoSquare`: for `E = Ecov g3 = S³⟨3⟩` (the homotopy fibre of a Postnikov
section `g3 : S³ → P₃`), assuming

* `hM : MSSHolds` — the multiplicative Serre spectral sequence,
* `hfib` — the fibre `fib g3 = ΩP₃` is a `K(ℤ,2)`-model through degree `11`,
* `hZ : K2ZFacts` — the field cohomology of such a model, and
* `h4 : H⁴(E;𝔽₂) ≅ 𝔽₂`,

every nonzero `u ∈ H⁴(E;𝔽₂)` satisfies `u ⌣ u ≠ 0`.

The argument is the two-column computation of the Serre spectral sequence of
`proj g3 : E → SphModel 3 = S³` over `𝔽₂` in total degrees `≤ 4`:

* `E₂^{s,q} ≅ H^s(S³;𝔽₂) ⊗ H^q(F;𝔽₂)` with `H^q(F) = 𝔽₂` for `q = 0,2,4` and `0` for `q` odd,
  so `E₂^{0,4} = 𝔽₂` is the only contribution to `E₂` in total degree `4`;
* the dimension count `hconv` at `n = 4` together with `h4` (`dim H⁴(E) = 1`) and the vanishing of
  the four other summands (`E₆^{1,3}`, `E₆^{3,1}` from the vanishing of the fibre in odd degrees;
  `E₆^{2,2}`, `E₆^{4,0}` from the vanishing `H²(S³;𝔽₂) = H⁴(S³;𝔽₂) = 0`) gives `dim E₆^{0,4} = 1`;
* nothing hits `(0,4)` on any page (the sources have negative `s`-coordinate), so the column maps
  `colTo : E₆^{0,4} → E₂^{0,4}` are injective (they are sections of `proj`), and, both terms being
  one-dimensional, the nonzero class of `E₆^{0,4}` maps to the nonzero class
  `u₀ = e₂⁻¹(1 ⊗ x²) ∈ E₂^{0,4}` (up to the scalar `c ∈ 𝔽₂^×`);
* the column-`0` edge map (`hcoledge`) then exhibits `x²` as the restriction of a class
  `e ∈ H⁴(E;𝔽₂)`, so `e ≠ 0` and the restriction of `e ⌣ e` is `x² ⌣ x² = x⁴ ≠ 0` (naturality of
  the cup product, `cupNaturalH`), hence `e ⌣ e ≠ 0`;
* `H⁴(E;𝔽₂) ≅ 𝔽₂` finally forces every nonzero `u` to equal `e` (over `𝔽₂` the only nonzero
  scalar is `1`), so `u ⌣ u = e ⌣ e ≠ 0`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EFACTS

noncomputable section

set_option maxHeartbeats 1000000

section Aux

variable {P3 : Type} [TopologicalSpace P3]

/-- **The mod-2 cohomology of the fibre `mssFib g3` in degrees `≤ 4`, from `K2ZFacts`.**

The generator `w ∈ H²(F;𝔽₂)` of `K2ZFacts` has nonzero cup powers through `w⁴`, which we rewrite
into the explicitly nested form `(w ⌣ w) ⌣ (w ⌣ w)` using the unit and associativity laws of the
cup product. -/
theorem mssFibCohModTwoAux (g3 : C(Work.Pi6.S3, P3))
    (hX : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 11 (mssFib g3) (mssFibPt g3))
    (hZ : Work.Pi6.K2ZFacts) :
    Module.finrank (ZMod 2) (Coh (ZMod 2) (mssFib g3) 0) = 1 ∧
    Module.finrank (ZMod 2) (Coh (ZMod 2) (mssFib g3) 2) = 1 ∧
    Module.finrank (ZMod 2) (Coh (ZMod 2) (mssFib g3) 4) = 1 ∧
    IsZero (Coh (ZMod 2) (mssFib g3) 1) ∧
    IsZero (Coh (ZMod 2) (mssFib g3) 3) ∧
    (∀ q : ℕ, q ≤ 4 → FiniteDimensional (ZMod 2) (Coh (ZMod 2) (mssFib g3) q)) ∧
    (∃ x : Coh (ZMod 2) (mssFib g3) 2, x ≠ 0 ∧
      cup (ZMod 2) (mssFib g3) 2 2 x x ≠ 0 ∧
      cup (ZMod 2) (mssFib g3) 4 4 (cup (ZMod 2) (mssFib g3) 2 2 x x)
        (cup (ZMod 2) (mssFib g3) 2 2 x x) ≠ 0) := by
  obtain ⟨w, hw⟩ := (hZ (mssFib g3) (mssFibPt g3) 11 (by norm_num) hX).2 (ZMod 2)
  have hcpow1 : cpow w 1 = w := by
    show (Work.Cohomology.cupH' (ZMod 2)
      (TopCat.toSSet.obj (TopCat.of (mssFib g3))) 0 2)
      (Work.Cohomology.oneH (ZMod 2) (TopCat.toSSet.obj (TopCat.of (mssFib g3)))) w = w
    exact Work.Cohomology.cupH'_one_left (ZMod 2)
      (TopCat.toSSet.obj (TopCat.of (mssFib g3))) 2 w
  have hcpow2 : cpow w 2 = cup (ZMod 2) (mssFib g3) 2 2 w w := by
    show cup (ZMod 2) (mssFib g3) 2 2 (cpow w 1) w = cup (ZMod 2) (mssFib g3) 2 2 w w
    rw [hcpow1]
  have hcpow3 : cpow w 3 =
      cup (ZMod 2) (mssFib g3) 4 2 (cup (ZMod 2) (mssFib g3) 2 2 w w) w := by
    show cup (ZMod 2) (mssFib g3) 4 2 (cpow w 2) w =
      cup (ZMod 2) (mssFib g3) 4 2 (cup (ZMod 2) (mssFib g3) 2 2 w w) w
    rw [hcpow2]
  have hcpow4 : cpow w 4 = cup (ZMod 2) (mssFib g3) 6 2
      (cup (ZMod 2) (mssFib g3) 4 2 (cup (ZMod 2) (mssFib g3) 2 2 w w) w) w := by
    show cup (ZMod 2) (mssFib g3) 6 2 (cpow w 3) w = cup (ZMod 2) (mssFib g3) 6 2
      (cup (ZMod 2) (mssFib g3) 4 2 (cup (ZMod 2) (mssFib g3) 2 2 w w) w) w
    rw [hcpow3]
  have hquart : cpow w 4 = cup (ZMod 2) (mssFib g3) 4 4
      (cup (ZMod 2) (mssFib g3) 2 2 w w) (cup (ZMod 2) (mssFib g3) 2 2 w w) := by
    rw [hcpow4]
    exact Work.Cohomology.cupH'_assoc (ZMod 2)
      (TopCat.toSSet.obj (TopCat.of (mssFib g3))) 4 2 2
      (cup (ZMod 2) (mssFib g3) 2 2 w w) w w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨w, ?_, ?_, ?_⟩⟩
  · simpa using (hw 0 (by norm_num)).2.1
  · simpa using (hw 1 (by norm_num)).2.1
  · simpa using (hw 2 (by norm_num)).2.1
  · haveI : Subsingleton (Coh (ZMod 2) (mssFib g3) 1) := (hw 0 (by norm_num)).2.2
    exact ModuleCat.isZero_of_subsingleton _
  · haveI : Subsingleton (Coh (ZMod 2) (mssFib g3) 3) := (hw 1 (by norm_num)).2.2
    exact ModuleCat.isZero_of_subsingleton _
  · intro q hq
    interval_cases q
    · exact FiniteDimensional.of_finrank_pos (by rw [(hw 0 (by norm_num)).2.1]; norm_num)
    · haveI : Subsingleton (Coh (ZMod 2) (mssFib g3) 1) := (hw 0 (by norm_num)).2.2
      exact FiniteDimensional.of_surjective
        (0 : ZMod 2 →ₗ[ZMod 2] Coh (ZMod 2) (mssFib g3) 1)
        (fun y => ⟨0, Subsingleton.elim _ _⟩)
    · exact FiniteDimensional.of_finrank_pos (by rw [(hw 1 (by norm_num)).2.1]; norm_num)
    · haveI : Subsingleton (Coh (ZMod 2) (mssFib g3) 3) := (hw 1 (by norm_num)).2.2
      exact FiniteDimensional.of_surjective
        (0 : ZMod 2 →ₗ[ZMod 2] Coh (ZMod 2) (mssFib g3) 3)
        (fun y => ⟨0, Subsingleton.elim _ _⟩)
    · exact FiniteDimensional.of_finrank_pos (by rw [(hw 2 (by norm_num)).2.1]; norm_num)
  · intro h0
    exact (hw 1 (by norm_num)).1 (by rw [hcpow1]; exact h0)
  · intro h0
    exact (hw 2 (by norm_num)).1 (by rw [hcpow2]; exact h0)
  · intro h0
    exact (hw 4 (by norm_num)).1 (by rw [hquart]; exact h0)

end Aux

set_option maxHeartbeats 1000000

/-- The mod-`2` Bockstein sequence makes `H_n(X;𝔽₂)` a subsingleton when `H_n(X;ℤ) = 0` and
multiplication by `2` is injective on `H_{n-1}(X;ℤ)`. -/
theorem mts_subsingleton_hr_zmodTwo_of {X : Type} [TopologicalSpace X] (n m : ℕ) (hm : m + 1 = n)
    (hn0 : Subsingleton (Work.Pi6.HR ℤ X n))
    (htf : ∀ z : Work.Pi6.HR ℤ X m, (2 : ℤ) • z = 0 → z = 0) :
    Subsingleton (Work.Pi6.HR (ZMod 2) X n) := by
  subst hm
  obtain ⟨red, del, _hred, hrd, hdel, _hrn, _hdn⟩ := Work.Pi6.BOCK.bocksteinLES 2 (by norm_num)
  haveI := hn0
  have hex1 : Function.Exact (⇑(red (X := X) (m + 1))) (⇑(del (X := X) m)) := hrd X m
  have hex2 : Function.Exact (⇑(del (X := X) m)) (fun z : Work.Pi6.HR ℤ X m => (2 : ℤ) • z) :=
    hdel X m
  refine ⟨fun y₁ y₂ => ?_⟩
  have hdel0 : del (X := X) m (y₁ - y₂) = 0 := by
    have h2 : (2 : ℤ) • (del (X := X) m (y₁ - y₂)) = 0 :=
      (hex2 (del (X := X) m (y₁ - y₂))).mpr ⟨y₁ - y₂, rfl⟩
    exact htf _ h2
  obtain ⟨x, hx⟩ := (hex1 (y₁ - y₂)).mp hdel0
  have hy : y₁ - y₂ = 0 := by
    rw [← hx, show red (X := X) (m + 1) x = red (X := X) (m + 1) 0 from
      congrArg _ (Subsingleton.elim x 0), map_zero]
  exact sub_eq_zero.mp hy

/-- Over a field, vanishing of `H_n(X;𝕜)` implies vanishing of `H^n(X;𝕜)`. -/
theorem mts_isZero_coh_of_subsingleton_hr {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X] (n : ℕ)
    (h : Subsingleton (Work.Pi6.HR 𝕜 X n)) : IsZero (Work.Pi6.Coh 𝕜 X n) := by
  obtain ⟨e⟩ := Work.StemsB.fieldDualUCT (F := 𝕜)
    (Work.Cohomology.singularChains 𝕜 (TopCat.of X)) n
  haveI hdual : Subsingleton (↥(Work.Pi6.HR 𝕜 X n) →ₗ[𝕜] 𝕜) :=
    ⟨fun a b => LinearMap.ext (fun x => by rw [h.elim x 0, map_zero, map_zero])⟩
  haveI : Subsingleton ↥(Work.Pi6.Coh 𝕜 X n) :=
    ⟨fun a b => e.toLinearEquiv.injective (Subsingleton.elim _ _)⟩
  exact Work.Pi6.EMM2.k2f_isZero_of_subsingleton (𝕜 := 𝕜) (M := ↥(Work.Pi6.Coh 𝕜 X n))

/-- Finite dimensionality of the cohomology fields transfers across a homeomorphism. -/
theorem mts_finiteDimensional_coh_of_homeomorph {𝕜 : Type} [Field 𝕜] {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (n : ℕ)
    (h : FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 Y n)) :
    FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 X n) := by
  haveI := h
  let φ := Work.Cohomology.singularCohomologyMap 𝕜 (TopCat.of Y) (TopCat.of X)
    (TopCat.ofHom (e.symm : C(Y, X))) n
  have h1 : IsIso φ :=
    Work.Cohomology.homotopyEquiv 𝕜 (TopCat.of Y) (TopCat.of X)
      (TopCat.ofHom (e.symm : C(Y, X))) (TopCat.ofHom (e : C(X, Y)))
      (Homeomorph.toHomotopyEquiv e.symm).left_inv.some
      (Homeomorph.toHomotopyEquiv e.symm).right_inv.some n
  exact Module.Finite.equiv (asIso φ).symm.toLinearEquiv

/-- The mod-`2` cohomology of `SphModel 3 = S³` in degrees `≤ 4`. -/
theorem sphereModTwoLowAux :
    IsZero (Work.Pi6.Coh (ZMod 2) (Work.StemsB.SphModel 3) 2) ∧
    IsZero (Work.Pi6.Coh (ZMod 2) (Work.StemsB.SphModel 3) 4) ∧
    Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.StemsB.SphModel 3) 0) = 1 ∧
    (∀ s : ℕ, s ≤ 4 → FiniteDimensional (ZMod 2)
      (Work.Pi6.Coh (ZMod 2) (Work.StemsB.SphModel 3) s)) := by
  have hSph2 : Subsingleton (Work.Pi6.HR (ZMod 2) (Work.Pi6.S3) 2) := by
    haveI : Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.S3) 2) :=
      ModuleCat.subsingleton_of_isZero
        (Work.Cohomology.sphereHomologyZero 3 2 (by norm_num) (by norm_num) (by norm_num))
    haveI : Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.S3) 1) :=
      ModuleCat.subsingleton_of_isZero
        (Work.Cohomology.sphereHomologyZero 3 1 (by norm_num) (by norm_num) (by norm_num))
    exact mts_subsingleton_hr_zmodTwo_of 2 1 (by norm_num) inferInstance
      (fun z _ => Subsingleton.elim z 0)
  have hSph4 : Subsingleton (Work.Pi6.HR (ZMod 2) (Work.Pi6.S3) 4) := by
    haveI : Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.S3) 4) :=
      ModuleCat.subsingleton_of_isZero
        (Work.Cohomology.sphereHomologyZero 3 4 (by norm_num) (by norm_num) (by norm_num))
    have htf : ∀ z : Work.Pi6.HR ℤ (Work.Pi6.S3) 3, (2 : ℤ) • z = 0 → z = 0 := by
      intro z hz
      obtain ⟨e3⟩ := Work.Cohomology.sphereHomologyTop 3 (by norm_num)
      have h1 : e3.toLinearEquiv z = 0 := by
        have h : e3.toLinearEquiv ((2 : ℤ) • z) = 0 := by rw [hz, map_zero]
        rw [map_zsmul] at h
        have h3 : (2 : ℤ) * e3.toLinearEquiv z = 0 := by rwa [zsmul_eq_mul] at h
        rcases mul_eq_zero.mp h3 with h4 | h4
        · exact absurd h4 (by norm_num)
        · exact h4
      exact e3.toLinearEquiv.injective (by rw [h1, map_zero])
    exact mts_subsingleton_hr_zmodTwo_of 4 3 (by norm_num) inferInstance htf
  have hz2 : IsZero (Work.Pi6.Coh (ZMod 2) (Work.Pi6.S3) 2) :=
    mts_isZero_coh_of_subsingleton_hr 2 hSph2
  have hz4 : IsZero (Work.Pi6.Coh (ZMod 2) (Work.Pi6.S3) 4) :=
    mts_isZero_coh_of_subsingleton_hr 4 hSph4
  have hfin : ∀ s : ℕ, s ≤ 4 → FiniteDimensional (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.Pi6.S3) s) :=
    Work.Pi6.K2Z.finiteDimCoh (𝕜 := ZMod 2) (Work.Pi6.S3) 4
      (Work.FGThm.fgUpTo_sph 3 (by norm_num) 4)
  haveI : PathConnectedSpace (Work.StemsB.SphModel 3) :=
    ⟨⟨OnePoint.infty⟩, fun x y => (Work.StemsB.joined_infty_SphModel 3 (by norm_num) x).symm.trans
      (Work.StemsB.joined_infty_SphModel 3 (by norm_num) y)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Work.Pi6.isZero_coh_of_homeomorph sHomeo 2 hz2
  · exact Work.Pi6.isZero_coh_of_homeomorph sHomeo 4 hz4
  · exact Work.Pi6.finrank_coh_zero_of_pathConnected (ZMod 2) (Work.StemsB.SphModel 3)
  · intro s hs
    exact mts_finiteDimensional_coh_of_homeomorph sHomeo s (hfin s hs)


theorem modTwoSquare {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) (hM : Work.Pi6.MSSHolds) (hfib : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 11 (Work.Pi6.EFACTS.fib g3) (Work.Pi6.EFACTS.fibPt g3)) (hZ : Work.Pi6.K2ZFacts) (h4 : Nonempty (Work.Pi6.Coh (ZMod 2) (Work.Pi6.Ecov g3) 4 ≃ₗ[ZMod 2] ZMod 2)) : ∀ u : Work.Pi6.Coh (ZMod 2) (Work.Pi6.Ecov g3) 4, u ≠ 0 → Work.Pi6.cup (ZMod 2) (Work.Pi6.Ecov g3) 4 4 u u ≠ 0 := by
  -- the base and fibre facts (children of this lemma)
  obtain ⟨hB2, hB4, hB0, hBfin⟩ := sphereModTwoLowAux
  have hconn : Work.PiS.SimplyConn (Work.StemsB.SphModel 3) (proj g3 (mssPt g3)) :=
    sphModelSimplyConn (proj g3 (mssPt g3))
  obtain ⟨hF0, hF2, hF4, hF1z, hF3z, hFfin, x, hx0, hx2, hx4⟩ :=
    mssFibCohModTwoAux g3 (mssFibModel g3 hfib) hZ
  -- the Serre spectral sequence of `proj g3` in total degrees `≤ 4`
  have hserre : Work.StemsB.IsSerreFibration (proj g3) :=
    (isHurewiczFibration_proj g3).isSerreFibration
  obtain ⟨S, hS0⟩ := hM (ZMod 2) (Ecov g3) (Work.StemsB.SphModel 3) (proj g3) (mssPt g3) 4
    hserre hconn hFfin hBfin
  have hS : IsSerreMSS S (proj g3) (mssPt g3) 4 := hS0
  obtain ⟨e2, hmul, hvanish, hconv, hbot, hcol⟩ := hS0
  -- the total space in degree 4
  have hE4 : Module.finrank (ZMod 2) (Coh (ZMod 2) (Ecov g3) 4) = 1 := by
    obtain ⟨φ⟩ := h4
    rw [φ.finrank_eq, Module.finrank_self]
  -- the `E₂` dimensions
  have hfin_E2_04 : Module.finrank (ZMod 2) (S.E 2 ((0 : ℤ), (4 : ℤ))) = 1 := by
    have h := Work.Pi6.EMM2.e2_finrank S (proj g3) (mssPt g3) 4 hS 0 4 (by norm_num) (by norm_num)
    rw [hB0, hF4, mul_one] at h
    exact h
  -- the other summands of the `n = 4` dimension count vanish
  have hz13 : IsZero (S.E 6 ((1 : ℤ), (3 : ℤ))) :=
    Work.Pi6.EMM2.k4_isZero_E_of_isZero_E2 S
      (Work.Pi6.EMM2.k4_isZero_E2_right (proj g3) (mssPt g3) S 4 hS (s := 1) (q := 3)
        (by norm_num) (by norm_num) hF3z) (by norm_num)
  have hz31 : IsZero (S.E 6 ((3 : ℤ), (1 : ℤ))) :=
    Work.Pi6.EMM2.k4_isZero_E_of_isZero_E2 S
      (Work.Pi6.EMM2.k4_isZero_E2_right (proj g3) (mssPt g3) S 4 hS (s := 3) (q := 1)
        (by norm_num) (by norm_num) hF1z) (by norm_num)
  have hz22 : IsZero (S.E 6 ((2 : ℤ), (2 : ℤ))) :=
    Work.Pi6.EMM2.k4_isZero_E_of_isZero_E2 S
      (Work.Pi6.EMM2.k4_isZero_E2_left (proj g3) (mssPt g3) S 4 hS (s := 2) (q := 2)
        (by norm_num) (by norm_num) hB2) (by norm_num)
  have hz40 : IsZero (S.E 6 ((4 : ℤ), (0 : ℤ))) :=
    Work.Pi6.EMM2.k4_isZero_E_of_isZero_E2 S
      (Work.Pi6.EMM2.k4_isZero_E2_left (proj g3) (mssPt g3) S 4 hS (s := 4) (q := 0)
        (by norm_num) (by norm_num) hB4) (by norm_num)
  have h0_13 : Module.finrank (ZMod 2) (S.E 6 ((1 : ℤ), (3 : ℤ))) = 0 := by
    haveI : Subsingleton (S.E 6 ((1 : ℤ), (3 : ℤ))) := ModuleCat.subsingleton_of_isZero hz13
    exact Module.finrank_zero_of_subsingleton
  have h0_31 : Module.finrank (ZMod 2) (S.E 6 ((3 : ℤ), (1 : ℤ))) = 0 := by
    haveI : Subsingleton (S.E 6 ((3 : ℤ), (1 : ℤ))) := ModuleCat.subsingleton_of_isZero hz31
    exact Module.finrank_zero_of_subsingleton
  have h0_22 : Module.finrank (ZMod 2) (S.E 6 ((2 : ℤ), (2 : ℤ))) = 0 := by
    haveI : Subsingleton (S.E 6 ((2 : ℤ), (2 : ℤ))) := ModuleCat.subsingleton_of_isZero hz22
    exact Module.finrank_zero_of_subsingleton
  have h0_40 : Module.finrank (ZMod 2) (S.E 6 ((4 : ℤ), (0 : ℤ))) = 0 := by
    haveI : Subsingleton (S.E 6 ((4 : ℤ), (0 : ℤ))) := ModuleCat.subsingleton_of_isZero hz40
    exact Module.finrank_zero_of_subsingleton
  have hfr6_04 : Module.finrank (ZMod 2) (S.E 6 ((0 : ℤ), (4 : ℤ))) = 1 := by
    have hpoint : ∀ c ∈ Finset.range 5, c ≠ 0 →
        Module.finrank (ZMod 2) (S.E (4 + 2) ((c : ℤ), ((4 - c : ℕ) : ℤ))) = 0 := by
      intro c hc hc0
      have hc5 : c < 5 := Finset.mem_range.mp hc
      interval_cases c
      · exact absurd rfl hc0
      · exact h0_13
      · exact h0_22
      · exact h0_31
      · exact h0_40
    have hsum := hconv 4 (by norm_num)
    rw [Finset.sum_eq_single 0 hpoint (by
        intro h
        exact absurd (Finset.mem_range.mpr (by norm_num)) h), hE4] at hsum
    exact hsum
  -- a nonzero class on the last page
  obtain ⟨z, hz⟩ := Work.Pi6.EMM2.k2f_exists_ne_zero hfr6_04
  -- the col-injectivity
  have hcolinj : Function.Injective (S.colTo (4 : ℤ) 4).hom := CohSS.colTo_injective S 4 4
  have hzne : (S.colTo (4 : ℤ) 4).hom z ≠ 0 := by
    intro h0
    exact hz (hcolinj (by rw [h0, map_zero]))
  -- the class `u₀ = e₂⁻¹(1 ⊗ x²)` and its nonvanishing
  let f : Coh (ZMod 2) (mssFib g3) 4 := cup (ZMod 2) (mssFib g3) 2 2 x x
  let u₀ : S.E 2 ((0 : ℤ), (4 : ℤ)) :=
    (e2 0 4 (by norm_num) (by norm_num)).inv.hom
      (one (ZMod 2) (Work.StemsB.SphModel 3) ⊗ₜ f)
  have hu₀ne : u₀ ≠ 0 :=
    Work.Pi6.EMM2.k4_e2_inv_tmul_ne_zero (proj g3) (mssPt g3) S
      (e2 0 4 (by norm_num) (by norm_num))
      (Work.Pi6.EMM2.k2f_one_ne_zero hB0) hx2
  -- `colTo (c⁻¹ • z) = u₀`
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' u₀ hu₀ne).mp hfin_E2_04
    ((S.colTo (4 : ℤ) 4).hom z)
  have hcne : c ≠ 0 := fun h0 => hzne (by rw [← hc, h0, zero_smul])
  have hz' : (S.colTo (4 : ℤ) 4).hom (c⁻¹ • z) = (e2 0 4 (by norm_num) (by norm_num)).inv.hom
      (one (ZMod 2) (Work.StemsB.SphModel 3) ⊗ₜ f) := by
    rw [map_smul, ← hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  -- the edge map: `x²` is the restriction of a class of `H⁴(E;𝔽₂)`
  obtain ⟨e, he⟩ := (hcol 4 (by norm_num) f).mpr ⟨c⁻¹ • z, hz'⟩
  -- `e ≠ 0`
  have he0 : e ≠ 0 := by
    intro h0
    have h1 : (cmap (ZMod 2)
        (Work.StemsB.fibreIncl (proj g3) (proj g3 (mssPt g3))) 4).hom e = 0 := by
      rw [h0, map_zero]
    rw [he] at h1
    exact hx2 h1
  -- the restriction of `e ⌣ e` is `x⁴ ≠ 0`
  have hres : (cmap (ZMod 2)
      (Work.StemsB.fibreIncl (proj g3) (proj g3 (mssPt g3))) (4 + 4)).hom
        (cup (ZMod 2) (Ecov g3) 4 4 e e) = cup (ZMod 2) (mssFib g3) 4 4 f f := by
    have he' : (Work.Cohomology.singularCohomologyMap (ZMod 2)
          (TopCat.of (Work.StemsB.fibre (proj g3) (proj g3 (mssPt g3)))) (TopCat.of (Ecov g3))
          (TopCat.ofHom (Work.StemsB.fibreIncl (proj g3) (proj g3 (mssPt g3)))) 4).hom e = f := he
    have hnat := Work.Cohomology.cupNaturalH (ZMod 2)
      (TopCat.ofHom (Work.StemsB.fibreIncl (proj g3) (proj g3 (mssPt g3)))) 4 4 e e
    rw [he'] at hnat
    exact hnat
  have hee : cup (ZMod 2) (Ecov g3) 4 4 e e ≠ 0 := by
    intro h0
    have h1 : (cmap (ZMod 2)
        (Work.StemsB.fibreIncl (proj g3) (proj g3 (mssPt g3))) (4 + 4)).hom
          (cup (ZMod 2) (Ecov g3) 4 4 e e) = 0 := by
      rw [h0, map_zero]
    exact hx4 (hres ▸ h1)
  -- every nonzero class of `H⁴(E;𝔽₂)` is `e`
  intro u hu
  obtain ⟨φ⟩ := h4
  have hone : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by
    intro c hc
    fin_cases c
    · exact absurd rfl hc
    · rfl
  have hφe : φ e ≠ 0 := fun h0 => he0 (φ.injective (by rw [h0, map_zero]))
  have hφu : φ u ≠ 0 := fun h0 => hu (φ.injective (by rw [h0, map_zero]))
  have hue : u = e := φ.injective (by rw [hone (φ u) hφu, hone (φ e) hφe])
  rw [hue]
  exact hee

end

end Work.Pi6.EFACTS
