import Mathlib
import Submission.Work.ThomBordism.Grassmann.ThomTarget
import Submission.Work.Thom.ATools
import Submission.Work.ThomBordism.Grassmann.Torsion.ModelGeom
import Submission.Work.ThomBordism.Grassmann.Torsion.RadialDefs
import Submission.Work.ThomBordism.Grassmann.Torsion.DiscPairIso
import Submission.Work.ThomBordism.Grassmann.Torsion.ThomSpaceCohomologyCompare
import Submission.Work.ThomBordism.Grassmann.Torsion.spanExtract
import Submission.Work.ThomBordism.Grassmann.Torsion.contractibleFar
import Submission.Work.ThomBordism.Grassmann.Torsion.thomSpaceHomologyFinite
import Submission.Work.ThomBordism.Grassmann.Torsion.ExcisionCompat
import Submission.Work.Cohomology.kronH_kernel_eq_torsion
import Submission.Work.Algebra.span_pair_one_tmul
import Submission.Work.ThomBordism.Grassmann.degreeEightFinrankLeTwo
import Submission.Work.ThomBordism.Grassmann.lowDegreeVanishingAndRanks

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-!
# `ThomSpaceTorsionDetected`: two classes of the Thom space whose common annihilator is the torsion

The target `Work.ThomBordism.Grassmann.ThomSpaceTorsionDetected k m` (see `ThomTarget.lean`) is the
cohomological half of the Grassmann chapter: the existence of two integral classes in degree `k + 8`
of the Thom space `T = Th(γ)` whose common annihilator in `H_{k+8}(T;ℤ)` is exactly the torsion
subgroup.  Equivalently: `dim_ℚ H^{k+8}(T;ℚ) ≤ 2` **and** the two classes span the rational dual.

## Structure of the proof

* `thomSpaceCohomologyCompare` (`Torsion/ThomSpaceCohomologyCompare.lean`) identifies
  `H^{k+8}(T;ℤ)` with the relative cohomology of the Thom pair `(E, E∖0)`, hence — through
  `tautologicalThomEquiv` — with `H^8(G̃r_k(ℝ^{k+m});ℤ)`;
* `rank_tscoh` transports the rank bound `Module.rank ℚ H^8(G;ℚ) ≤ 2` of
  `lowDegreeVanishingAndRanks.rank_eight_le_two` to `ℚ ⊗[ℤ] H^{k+8}(T;ℤ)`;
* `exists_spanning_classes` extracts two integral classes whose images span `ℚ ⊗[ℤ] H^{k+8}(T;ℤ)`
  (`Torsion/spanExtract.lean`);
* `thomSpaceClassesDetect` is the resulting detection statement (the `Φ`-argument: the ℤ-bilinear
  Kronecker pairing extends to a `ℚ`-linear functional, which vanishes on a spanning pair only if it
  vanishes everywhere);
* `thomSpaceHomologyFinite` (`Torsion/thomSpaceHomologyFinite.lean`) supplies the finite generation
  of `H_n(T;ℤ)`, which turns `kronH_kernel_eq_torsion` into the required statement that the
  annihilator of *all* classes is the torsion;
* `thomSpaceTorsionDetected` is the target, assembled by `thomSpaceTorsionDetected_of_inputs`.
-/

namespace Work.ThomBordism.Grassmann

open scoped TensorProduct
open Work.ThomBordism.Grassmann.Torsion

noncomputable section

/-- The degree-`(k+8)` integral cohomology of the Thom space. -/
abbrev TSCoh (k m : ℕ) : Type :=
  (Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8)

/-- The degree-`(k+8)` integral homology of the Thom space. -/
abbrev THom (k m : ℕ) : Type :=
  (Work.Cohomology.chainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8)

/-! ## Transporting a `ℤ`-linear equivalence to the rationalisation -/

/-- A `ℤ`-linear equivalence acts `ℚ`-linearly on `ℚ ⊗[ℤ] ·`. -/
theorem ratCongr_smul {A Ag : Type} [AddCommGroup A] [AddCommGroup Ag] (e : A ≃ₗ[ℤ] Ag)
    (q : ℚ) (z : ℚ ⊗[ℤ] A) :
    TensorProduct.congr (LinearEquiv.refl ℤ ℚ) e (q • z) =
      q • TensorProduct.congr (LinearEquiv.refl ℤ ℚ) e z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [TensorProduct.smul_tmul', TensorProduct.congr_tmul, TensorProduct.congr_tmul,
        TensorProduct.smul_tmul']
      simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The `ℚ`-linear equivalence `ℚ ⊗[ℤ] A ≃ₗ[ℚ] ℚ ⊗[ℤ] Ag` induced by a `ℤ`-linear equivalence. -/
def ratCongr {A Ag : Type} [AddCommGroup A] [AddCommGroup Ag] (e : A ≃ₗ[ℤ] Ag) :
    (ℚ ⊗[ℤ] A) ≃ₗ[ℚ] (ℚ ⊗[ℤ] Ag) :=
{ TensorProduct.congr (LinearEquiv.refl ℤ ℚ) e with
  map_smul' := ratCongr_smul e }

@[simp] theorem ratCongr_tmul {A Ag : Type} [AddCommGroup A] [AddCommGroup Ag]
    (e : A ≃ₗ[ℤ] Ag) (q : ℚ) (a : A) : ratCongr e (q ⊗ₜ[ℤ] a) = q ⊗ₜ[ℤ] e a :=
  TensorProduct.congr_tmul _ _ q a

/-! ## The reduction: two spanning classes plus finite generation -/

/-- **The reduction of `ThomSpaceTorsionDetected` to its two inputs.**

Given

* `hmain`: two classes `a₁, a₂ : H^{k+8}(T;ℤ)` such that a class `y ∈ H_{k+8}(T;ℤ)` pairing to zero
  with both pairs to zero with *every* class of `H^{k+8}(T;ℤ)`, and
* `hfin`: `H_n(T;ℤ)` finitely generated in every degree,

the two classes detect exactly the torsion in `H_{k+8}(T;ℤ)`, i.e. `ThomSpaceTorsionDetected k m`. -/
theorem thomSpaceTorsionDetected_of_inputs (k m : ℕ)
    (hmain : ∃ a1 a2 : TSCoh k m, ∀ y : THom k m,
      Work.Cohomology.kronH ℤ (sset (TautologicalThomSpace k m)) (k + 8) a1 y = 0 →
      Work.Cohomology.kronH ℤ (sset (TautologicalThomSpace k m)) (k + 8) a2 y = 0 →
      ∀ a : TSCoh k m,
        Work.Cohomology.kronH ℤ (sset (TautologicalThomSpace k m)) (k + 8) a y = 0)
    (hfin : ∀ n : ℕ, Module.Finite ℤ
      ((Work.Cohomology.chainC ℤ (sset (TautologicalThomSpace k m))).homology n)) :
    ThomSpaceTorsionDetected k m := by
  obtain ⟨a1, a2, hmain⟩ := hmain
  refine ⟨a1, a2, fun y h1 h2 => ?_⟩
  exact (Work.Cohomology.kronH_kernel_eq_torsion (sset (TautologicalThomSpace k m)) hfin
    (k + 8) y).mp (hmain y h1 h2)

/-! ## The comparison with the Thom pair, in degree `k + 8` -/

/-- **The degree-`(k+8)` cohomology of the Thom space is that of the Thom pair**, i.e. of
`H^8(G̃r_k(ℝ^{k+m});ℤ)` by the Thom isomorphism. -/
theorem thomSpaceCohomologyCompareK (k m : ℕ) :
    Nonempty (TSCoh k m ≃ₗ[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (k + 8)) := by
  haveI : ContractibleSpace ↥(far k m 1) := contractibleFar k m
  have h1 : Subsingleton (Work.Thom.Coh ℤ (k + 7) ↥(far k m 1)) := by
    rw [show k + 7 = (k + 6) + 1 from by omega]
    exact Work.ThomBordism.Grassmann.subsingleton_cohomology_of_contractible
      (X := TopCat.of ↥(far k m 1)) (k + 6)
  have h2 : Subsingleton (Work.Thom.Coh ℤ ((k + 7) + 1) ↥(far k m 1)) :=
    Work.ThomBordism.Grassmann.subsingleton_cohomology_of_contractible
      (X := TopCat.of ↥(far k m 1)) (k + 7)
  obtain ⟨e⟩ := Work.ThomBordism.Grassmann.Torsion.thomSpaceCohomologyCompare k m h1 h2
  refine ⟨?_⟩
  have hcast : ((((Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology
        ((k + 7) + 1)) ≃ₗ[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) ((k + 7) + 1))
      = (((Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology (k + 8))
        ≃ₗ[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (k + 8))) :=
    congrArg (fun n : ℕ =>
      (((Work.Cohomology.cochainC ℤ (sset (TautologicalThomSpace k m))).homology n)
        ≃ₗ[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) n)) (by omega)
  exact hcast ▸ e

/-- **The rationalised degree-`(k+8)` cohomology of the Thom space has rank at most two.** -/
theorem rank_tscoh (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    Module.rank ℚ (ℚ ⊗[ℤ] TSCoh k m) ≤ 2 := by
  obtain ⟨e⟩ := thomSpaceCohomologyCompareK k m
  -- the Thom isomorphism `H^8(G;ℤ) ≃ H^{k+8}(D γ,S γ;ℤ)` (degrees `8+k` and `k+8`)
  have hcast2 : (((Work.Thom.Coh ℤ 8 (OG k m))
        ≃ₗ[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (8 + k))
      = ((Work.Thom.Coh ℤ 8 (OG k m))
        ≃ₗ[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (k + 8))) :=
    congrArg (fun n : ℕ => ((Work.Thom.Coh ℤ 8 (OG k m))
      ≃ₗ[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) n)) (by omega)
  have e2 : Work.Thom.Coh ℤ 8 (OG k m)
      ≃ₗ[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) (k + 8) :=
    hcast2 ▸ tautologicalThomEquiv k m 8
  have e3 : TSCoh k m ≃ₗ[ℤ] Work.Thom.Coh ℤ 8 (OG k m) := e.trans e2.symm
  calc Module.rank ℚ (ℚ ⊗[ℤ] TSCoh k m)
      = Module.rank ℚ (ℚ ⊗[ℤ] Work.Thom.Coh ℤ 8 (OG k m)) :=
        (e3.baseChange ℤ ℚ _ _).rank_eq
    _ = Module.rank ℚ (Work.SignatureBordism.ratCohomology 8 (sset (OG k m))) := rfl
    _ ≤ 2 := rank_eight_le_two k m hk hm

/-! ## The two spanning classes -/

/-- Every element of `ℚ ⊗[ℤ] H^{k+8}(T;ℤ)` is a `ℚ`-linear combination of the elements
`1 ⊗ a`. -/
theorem span_one_tmul_eq_top (k m : ℕ) :
    Submodule.span ℚ (Set.range (fun a : TSCoh k m => (1 : ℚ) ⊗ₜ[ℤ] a)) = ⊤ := by
  have hmem : ∀ z : ℚ ⊗[ℤ] TSCoh k m,
      z ∈ Submodule.span ℚ (Set.range (fun a : TSCoh k m => (1 : ℚ) ⊗ₜ[ℤ] a)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul q a =>
        have h : (q ⊗ₜ[ℤ] a : ℚ ⊗[ℤ] TSCoh k m) = q • ((1 : ℚ) ⊗ₜ[ℤ] a) := by
          rw [TensorProduct.smul_tmul']
          simp
        rw [h]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  exact le_antisymm le_top (fun z _ => hmem z)

/-- **Two classes of the Thom space span its rationalised degree-`(k+8)` cohomology.** -/
theorem exists_spanning_classes (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    ∃ a1 a2 : TSCoh k m,
      Submodule.span ℚ ({((1 : ℚ) ⊗ₜ[ℤ] a1), ((1 : ℚ) ⊗ₜ[ℤ] a2)} : Set (ℚ ⊗[ℤ] TSCoh k m))
        = ⊤ := by
  obtain ⟨v1, hv1, v2, hv2, hspan⟩ :=
    Work.ThomBordism.Grassmann.Torsion.exists_pair_span_eq_top_of_rank_le_two
      (span_one_tmul_eq_top k m) (Set.range_nonempty _) (rank_tscoh k m hk hm)
  obtain ⟨a1, ha1⟩ := hv1
  obtain ⟨a2, ha2⟩ := hv2
  have ha1' : (1 : ℚ) ⊗ₜ[ℤ] a1 = v1 := ha1
  have ha2' : (1 : ℚ) ⊗ₜ[ℤ] a2 = v2 := ha2
  refine ⟨a1, a2, ?_⟩
  rw [← ha1', ← ha2'] at hspan
  exact hspan

/-! ## The detection statement -/

/-- **The two classes detect the vanishing of all pairings**: if a class `y ∈ H_{k+8}(T;ℤ)` pairs to
zero with two classes spanning the rationalised cohomology, then it pairs to zero with *every*
class.

The proof is the `Φ`-argument: `(a, q) ↦ q · ⟨a, y⟩` is `ℤ`-bilinear, hence induces a `ℚ`-linear
functional `Φ : ℚ ⊗[ℤ] H^{k+8}(T;ℤ) → ℚ` with `Φ (1 ⊗ a) = ⟨a, y⟩`; a `ℚ`-linear functional
vanishing on a spanning pair vanishes identically.  Formally `Φ` is the base change of the
`ℤ`-linear functional `a ↦ ⟨a, y⟩` composed with the canonical identification
`ℚ ⊗[ℤ] ℤ ≅ ℚ`, which makes its `ℚ`-linearity automatic. -/
theorem thomSpaceClassesDetect (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    ∃ a1 a2 : TSCoh k m, ∀ y : THom k m,
      Work.Cohomology.kronH ℤ (sset (TautologicalThomSpace k m)) (k + 8) a1 y = 0 →
      Work.Cohomology.kronH ℤ (sset (TautologicalThomSpace k m)) (k + 8) a2 y = 0 →
      ∀ a : TSCoh k m,
        Work.Cohomology.kronH ℤ (sset (TautologicalThomSpace k m)) (k + 8) a y = 0 := by
  obtain ⟨a1, a2, hspan⟩ := exists_spanning_classes k m hk hm
  refine ⟨a1, a2, fun y hy1 hy2 => ?_⟩
  let K : TSCoh k m →ₗ[ℤ] THom k m →ₗ[ℤ] ℤ :=
    Work.Cohomology.kronH ℤ (sset (TautologicalThomSpace k m)) (k + 8)
  -- the `ℤ`-linear functional `a ↦ ⟨a, y⟩`
  let f : TSCoh k m →ₗ[ℤ] ℤ := K.flip y
  have hK1 : K a1 y = 0 := hy1
  have hK2 : K a2 y = 0 := hy2
  -- its `ℚ`-linear base change `ℚ ⊗[ℤ] H^{k+8}(T;ℤ) → ℚ ⊗[ℤ] ℤ ≅ ℚ`
  let Φ : (ℚ ⊗[ℤ] TSCoh k m) →ₗ[ℚ] ℚ :=
    { toFun := fun z => (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ) ((f.baseChange ℚ) z)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  have hΦ : ∀ (q : ℚ) (a : TSCoh k m), Φ (q ⊗ₜ[ℤ] a) = q * ((K a y : ℤ) : ℚ) := by
    intro q a
    change (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ) ((f.baseChange ℚ) (q ⊗ₜ[ℤ] a))
      = q * ((K a y : ℤ) : ℚ)
    rw [f.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul ℚ, zsmul_eq_mul]
    have hfa : f a = K a y := rfl
    rw [hfa]
    ring
  have hker : Submodule.span ℚ
      ({((1 : ℚ) ⊗ₜ[ℤ] a1), ((1 : ℚ) ⊗ₜ[ℤ] a2)} : Set (ℚ ⊗[ℤ] TSCoh k m)) ≤ LinearMap.ker Φ := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine LinearMap.mem_ker.mpr ?_
      rw [hΦ 1 a1, hK1]
      norm_num
    · refine LinearMap.mem_ker.mpr ?_
      rw [hΦ 1 a2, hK2]
      norm_num
  have hΦzero : Φ = 0 := by
    have htop : LinearMap.ker Φ = ⊤ := by
      rw [hspan] at hker
      exact le_antisymm le_top hker
    apply LinearMap.ext
    intro z
    have hz : z ∈ LinearMap.ker Φ := by rw [htop]; exact Submodule.mem_top
    exact LinearMap.mem_ker.mp hz
  intro a
  have h : ((K a y : ℤ) : ℚ) = 0 := by
    have h0 : Φ ((1 : ℚ) ⊗ₜ[ℤ] a) = 0 := by rw [hΦzero]; rfl
    rwa [hΦ 1 a, one_mul] at h0
  exact_mod_cast h

/-! ## The target -/

theorem thomSpaceTorsionDetected (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    Work.ThomBordism.Grassmann.ThomSpaceTorsionDetected k m :=
  thomSpaceTorsionDetected_of_inputs k m (thomSpaceClassesDetect k m hk hm)
    (fun n => Work.ThomBordism.Grassmann.Torsion.thomSpaceHomologyFinite k m n)

end

end Work.ThomBordism.Grassmann
