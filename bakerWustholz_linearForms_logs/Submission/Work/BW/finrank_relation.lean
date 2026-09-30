import Mathlib
import Submission.Work.BW.HilbSerreDefs
import Submission.Work.BW.graded_map_image

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dimension relation for the multigraded Hilbert–Serre recursion

Let `piece : (Fin (N+1) →₀ ℤ) → Submodule ℂ M` be a `ℤ^{N+1}`-grading of an `MR N`-module `M`
with finite dimensional pieces (`MR N = ℂ[X_{i,j}]` is the coordinate ring of `(P¹)^{N+1}`).
Fix a variable `X x`.  Multiplication by `X x` is a graded endomorphism of `M` of degree
`w := wZ N x`, hence restricts to a `ℂ`-linear map `piece (u - w) → piece u`.  Writing
`quoPiece` for the image of `piece u` in `M ⧸ (X x • ⊤)` and `kerPiece` for the kernel of the
restricted multiplication, the rank–nullity theorem applied to the two maps

* `piece u → M ⧸ (X x • ⊤)` (kernel `piece u ⊓ (X x • ⊤)`), and
* `piece (u - w) → M` (range `piece u ⊓ (X x • ⊤)`, by gradedness),

yields the identity

`finrank (piece u) - finrank (piece (u - w)) = finrank (quoPiece u) - finrank (kerPiece u)`.

This is the recursion step that drives the multigraded Hilbert–Serre theorem.
-/

namespace Work.BW

open MvPolynomial

/-- `mulX` viewed as a `ℂ`-linear map. -/
private noncomputable abbrev mXc (N : ℕ) (M : Type*) [AddCommGroup M] [Module ℂ M]
    [Module (MR N) M] [IsScalarTower ℂ (MR N) M] (x : Fin (N + 1) × Fin 2) : M →ₗ[ℂ] M :=
  (HilbSerre.mulX N M x : M →ₗ[ℂ] M)

/-- The submodule `X x • ⊤` of `M`, regarded as a `ℂ`-submodule (i.e. after restricting scalars). -/
private noncomputable abbrev XcSub (N : ℕ) (M : Type*) [AddCommGroup M] [Module ℂ M]
    [Module (MR N) M] [IsScalarTower ℂ (MR N) M] (x : Fin (N + 1) × Fin 2) : Submodule ℂ M :=
  Submodule.restrictScalars ℂ (HilbSerre.Xsub N M x)

/-- The range of multiplication by `X x` on `M` is `X x • ⊤`. -/
private theorem range_mXc {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (MR N) M]
    [IsScalarTower ℂ (MR N) M] (x : Fin (N + 1) × Fin 2) :
    LinearMap.range (mXc N M x) = XcSub N M x := by
  dsimp only [mXc, XcSub]
  rw [LinearMap.range_restrictScalars]
  congr 1
  rw [HilbSerre.mulX, HilbSerre.Xsub]
  ext m
  rw [LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, Submodule.mem_top, rfl⟩
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, rfl⟩

/-- Multiplication by `X x` shifts the grading by `wZ N x`. -/
private theorem grad_mXc {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (MR N) M]
    [IsScalarTower ℂ (MR N) M] (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M)
    (x : Fin (N + 1) × Fin 2) (hg : IsGrading N piece) :
    ∀ i, (piece i).map (mXc N M x) ≤ piece (i + wZ N x) := by
  intro i
  rintro m hm
  rw [Submodule.mem_map] at hm
  obtain ⟨n, hn, rfl⟩ := hm
  exact hg.smul_mem x i hn

/-- The kernel of multiplication by `X x`, as a `ℂ`-submodule. -/
private noncomputable abbrev KcSub (N : ℕ) (M : Type*) [AddCommGroup M] [Module ℂ M]
    [Module (MR N) M] [IsScalarTower ℂ (MR N) M] (x : Fin (N + 1) × Fin 2) : Submodule ℂ M :=
  Submodule.restrictScalars ℂ (LinearMap.ker (HilbSerre.mulX N M x))

theorem finrank_relation {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (MR N) M] [IsScalarTower ℂ (MR N) M] (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M)
    (x : Fin (N + 1) × Fin 2) (hg : IsGrading N piece) (hfd : ∀ u, Module.Finite ℂ ↥(piece u))
    (u : Fin (N + 1) →₀ ℤ) :
    (Module.finrank ℂ ↥(piece u) : ℚ) - (Module.finrank ℂ ↥(piece (u - wZ N x)) : ℚ)
      = (Module.finrank ℂ ↥(HilbSerre.quoPiece N M piece x u) : ℚ)
        - (Module.finrank ℂ ↥(HilbSerre.kerPiece N M piece x u) : ℚ) := by
  classical
  haveI hBfin : Module.Finite ℂ ↥(piece u) := hfd u
  haveI hAfin : Module.Finite ℂ ↥(piece (u - wZ N x)) := hfd (u - wZ N x)
  -- The image of `piece (u - w)` under multiplication by `X x` is `piece u ⊓ (X x • ⊤)`.
  have himg : (piece (u - wZ N x)).map (mXc N M x) = piece u ⊓ XcSub N M x := by
    have h := graded_map_image piece hg.isInternal (mXc N M x) (wZ N x)
      (grad_mXc piece x hg) (u - wZ N x)
    rw [range_mXc x, sub_add_cancel] at h
    exact h
  -- Rank–nullity for `piece u → M ⧸ (X x • ⊤)`.
  have hS1 : Module.finrank ℂ ↥(HilbSerre.quoPiece N M piece x u)
      + Module.finrank ℂ ↥(piece u ⊓ XcSub N M x) = Module.finrank ℂ ↥(piece u) := by
    let χ := ((Submodule.mkQ (HilbSerre.Xsub N M x) : M →ₗ[ℂ] M ⧸ HilbSerre.Xsub N M x)).comp
      (piece u).subtype
    have hrn := LinearMap.finrank_range_add_finrank_ker χ
    have hrange : χ.range = HilbSerre.quoPiece N M piece x u := by
      dsimp only [χ]
      rw [LinearMap.range_eq_map, Submodule.map_comp, Submodule.map_subtype_top]
      rfl
    have hker_eq : χ.ker = Submodule.comap (piece u).subtype (piece u ⊓ XcSub N M x) := by
      dsimp only [χ]
      rw [LinearMap.ker_comp, LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
      rw [show Submodule.comap (piece u).subtype (piece u ⊓ XcSub N M x)
          = Submodule.comap (piece u).subtype (XcSub N M x) from by
        rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]]
    have hkerfr : Module.finrank ℂ ↥χ.ker = Module.finrank ℂ ↥(piece u ⊓ XcSub N M x) := by
      rw [hker_eq]
      exact (Submodule.comapSubtypeEquivOfLe
        (inf_le_left : piece u ⊓ XcSub N M x ≤ piece u)).finrank_eq
    rw [hrange, hkerfr] at hrn
    exact hrn
  -- Rank–nullity for `piece (u - w) → M`.
  have hS2 : Module.finrank ℂ ↥(piece u ⊓ XcSub N M x)
      + Module.finrank ℂ ↥(HilbSerre.kerPiece N M piece x u)
      = Module.finrank ℂ ↥(piece (u - wZ N x)) := by
    let ψ := (mXc N M x).comp (piece (u - wZ N x)).subtype
    have hrn := LinearMap.finrank_range_add_finrank_ker ψ
    have hrange : ψ.range = piece u ⊓ XcSub N M x := by
      dsimp only [ψ]
      rw [LinearMap.range_eq_map, Submodule.map_comp, Submodule.map_subtype_top]
      exact himg
    have hψker : ψ.ker = Submodule.comap (piece (u - wZ N x)).subtype (KcSub N M x) := by
      dsimp only [ψ, mXc, KcSub]
      rw [LinearMap.ker_comp, LinearMap.ker_restrictScalars]
    have hψkerfr : Module.finrank ℂ ↥ψ.ker
        = Module.finrank ℂ ↥(piece (u - wZ N x) ⊓ KcSub N M x) := by
      rw [hψker]
      rw [show Submodule.comap (piece (u - wZ N x)).subtype (KcSub N M x)
          = Submodule.comap (piece (u - wZ N x)).subtype
              (piece (u - wZ N x) ⊓ KcSub N M x)
          from by rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]]
      exact (Submodule.comapSubtypeEquivOfLe
        (inf_le_left : piece (u - wZ N x) ⊓ KcSub N M x ≤ piece (u - wZ N x))).finrank_eq
    have hkPiece : Module.finrank ℂ ↥(HilbSerre.kerPiece N M piece x u)
        = Module.finrank ℂ ↥(piece (u - wZ N x) ⊓ KcSub N M x) := by
      have hker_eq : HilbSerre.kerPiece N M piece x u
          = Submodule.comap ((KcSub N M x).subtype) (piece (u - wZ N x)) := rfl
      rw [hker_eq]
      rw [show Submodule.comap ((KcSub N M x).subtype) (piece (u - wZ N x))
          = Submodule.comap ((KcSub N M x).subtype)
              (piece (u - wZ N x) ⊓ KcSub N M x)
          from by rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]]
      exact (Submodule.comapSubtypeEquivOfLe
        (inf_le_right : piece (u - wZ N x) ⊓ KcSub N M x ≤ KcSub N M x)).finrank_eq
    rw [hrange, hψkerfr, ← hkPiece] at hrn
    exact hrn
  -- Convert the two rank–nullity identities into the claimed difference of dimensions.
  have hb : (Module.finrank ℂ ↥(piece u) : ℚ)
      = (Module.finrank ℂ ↥(HilbSerre.quoPiece N M piece x u) : ℚ)
        + (Module.finrank ℂ ↥(piece u ⊓ XcSub N M x) : ℚ) := by
    rw [← hS1]; push_cast; ring
  have ha : (Module.finrank ℂ ↥(piece (u - wZ N x)) : ℚ)
      = (Module.finrank ℂ ↥(HilbSerre.kerPiece N M piece x u) : ℚ)
        + (Module.finrank ℂ ↥(piece u ⊓ XcSub N M x) : ℚ) := by
    have h2 := hS2
    rw [add_comm] at h2
    rw [← h2]; push_cast; ring
  rw [hb, ha]
  ring

end Work.BW
