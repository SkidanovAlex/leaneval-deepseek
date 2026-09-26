/-
# The odd-weight six-dimensional representation `σ`

CKMRV (Prop. 3.2(1) and Prop. 3.8) reduce the group algebra `R = ℂ[SL(2,ℤ)]` modulo the
defect ideal

  `𝓘_odd = (T-I)²R + S(T-I)²R + (1+z)R`,   `z = -I`,

using the six elements `Mp = (I, T⁻¹, STS, S, ST⁻¹, TS)` which tile the `Γ(2)`-fundamental
domain.  The reduction is governed by a six-dimensional representation `σ : SL(2,ℤ) → M₆(ℂ)`:

  `Mp_i · γ ≡ ∑_j σ(γ)_{ij} · Mp_j   (mod 𝓘_odd)`.

The construction below is coordinate-free.  Let `Q = R ⧸ 𝓘_odd` be the quotient, on which
`R` acts on the right, and let

  `Φ : ℂ⁶ → Q`,   `Φ e_i = [Mp_i]`

be the linear map sending the standard basis to the six classes.  The two ingredients are

* `Work.Asymptotics.spMp_all_mem`: the classes `[Mp_i]` span `Q` (the twelve base
  computations of the CKMRV propagation argument, proved in `spanning_Mp_idealIOdd`), which
  makes `Φ` surjective;
* the resulting monoid structure: any `ℂ`-linear section `d` of `Φ` gives a lift of the
  right action of `γ` on `Q` to `ℂ⁶`,

  `σ̂(γ) = d ∘ (· γ) ∘ Φ + (1 - d ∘ Φ)`,

which is an anti-homomorphism of monoids with `Φ ∘ σ̂(γ) = (· γ) ∘ Φ`.  Transposing gives
the monoid homomorphism `σ(γ) = σ̂(γ)ᵀ`, and the identity `Φ(σ̂(γ) e_i) = [Mp_i · γ]`
translates into `Mp_i · γ ≡ ∑_j σ(γ)_{ij} Mp_j (mod 𝓘_odd)`.

## Main result

* `Work.Asymptotics.exists_sigma_odd`
-/
import Mathlib
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.spanning_Mp_idealIOdd

noncomputable section

set_option maxHeartbeats 1000000

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Asymptotics

open Work.Kernels

/-! ## Elementary facts about `ofSL` -/

lemma ofSL_mul (γ δ : SL(2,ℤ)) : ofSL (γ * δ) = ofSL γ * ofSL δ := by
  show MonoidAlgebra.single (γ * δ) (1 : ℂ)
      = MonoidAlgebra.single γ 1 * MonoidAlgebra.single δ 1
  rw [MonoidAlgebra.single_mul_single, mul_one]

lemma ofSL_one : ofSL (1 : SL(2,ℤ)) = 1 := by
  show MonoidAlgebra.single (1 : SL(2,ℤ)) (1 : ℂ) = 1
  exact MonoidAlgebra.one_def.symm

/-! ## The quotient `R ⧸ 𝓘_odd` and the right action of `SL(2,ℤ)` -/

/-- The quotient of the group algebra by the odd-weight defect ideal. -/
abbrev Qodd : Type := R ⧸ idealIOdd

/-- Right multiplication by `x ∈ R` as a `ℂ`-linear map. -/
def mulRight (x : R) : R →ₗ[ℂ] R where
  toFun a := a * x
  map_add' a b := add_mul a b x
  map_smul' c a := smul_mul_assoc c a x

@[simp] lemma mulRight_apply (x a : R) : mulRight x a = a * x := rfl

/-- The right action of `γ ∈ SL(2,ℤ)` on `R ⧸ 𝓘_odd`, i.e. the map induced by right
multiplication by `ofSL γ` (well defined because `𝓘_odd` is a right ideal). -/
def act (γ : SL(2,ℤ)) : Qodd →ₗ[ℂ] Qodd :=
  Submodule.liftQ idealIOdd (Submodule.mkQ idealIOdd ∘ₗ mulRight (ofSL γ)) (by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, mulRight_apply]
    exact (Submodule.Quotient.mk_eq_zero idealIOdd).mpr (idealIOdd_mul_mem hx (ofSL γ)))

@[simp] lemma act_mkQ (γ : SL(2,ℤ)) (x : R) :
    act γ (Submodule.mkQ idealIOdd x) = Submodule.mkQ idealIOdd (x * ofSL γ) := by
  rw [Submodule.mkQ_apply, act, Submodule.liftQ_apply, LinearMap.comp_apply, mulRight_apply,
    Submodule.mkQ_apply]

/-- The right action is a right action: acting by `γ` and then by `δ` is acting by `γ * δ`. -/
lemma act_comp (γ δ : SL(2,ℤ)) : (act δ).comp (act γ) = act (γ * δ) := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective idealIOdd x
  simp only [LinearMap.comp_apply, act_mkQ, ofSL_mul, mul_assoc]

lemma act_one : act (1 : SL(2,ℤ)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective idealIOdd x
  rw [act_mkQ, ofSL_one, mul_one, LinearMap.id_apply]

/-! ## The map `Φ : ℂ⁶ → R ⧸ 𝓘_odd` -/

/-- The `ℂ`-linear map sending the `i`-th standard basis vector of `ℂ⁶` to the class of
`MpElem i`. -/
def Phi : (Fin 6 → ℂ) →ₗ[ℂ] Qodd where
  toFun v := ∑ i, v i • Submodule.mkQ idealIOdd (MpElem i)
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_assoc, Finset.smul_sum, RingHom.id_apply]

@[simp] lemma Phi_single (i : Fin 6) :
    Phi (Pi.single i (1 : ℂ)) = Submodule.mkQ idealIOdd (MpElem i) := by
  rw [Phi]
  show (∑ j : Fin 6, (Pi.single i (1 : ℂ) : Fin 6 → ℂ) j • Submodule.mkQ idealIOdd (MpElem j))
      = Submodule.mkQ idealIOdd (MpElem i)
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Pi.single_apply, if_neg hb, zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The classes of the six elements `Mp_i` span `R ⧸ 𝓘_odd`, so `Φ` is surjective. -/
lemma Phi_surjective : Function.Surjective Phi := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective idealIOdd q
  obtain ⟨v, hv, ξ, hξ, hsum⟩ := Submodule.mem_sup.mp (spMp_all_mem x)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  refine ⟨c, ?_⟩
  have hξ0 : Submodule.mkQ idealIOdd ξ = 0 := (Submodule.Quotient.mk_eq_zero idealIOdd).mpr hξ
  have hx : Submodule.mkQ idealIOdd x = Submodule.mkQ idealIOdd v := by
    rw [← hsum, map_add, hξ0, add_zero]
  rw [hx, ← hc, map_sum]
  simp only [map_smul]
  rw [Phi]
  rfl

lemma Phi_range : Phi.range = ⊤ := LinearMap.range_eq_top.mpr Phi_surjective

/-! ## A section of `Φ` and the resulting lift of the action -/

/-- A `ℂ`-linear section of `Φ` (it exists because `Φ` is surjective). -/
def sect : Qodd →ₗ[ℂ] (Fin 6 → ℂ) :=
  Classical.choose (Phi.exists_rightInverse_of_surjective Phi_range)

lemma sect_spec : Phi.comp sect = LinearMap.id :=
  Classical.choose_spec (Phi.exists_rightInverse_of_surjective Phi_range)

lemma Phi_sect_apply (y : Qodd) : Phi (sect y) = y := by
  rw [← LinearMap.comp_apply, sect_spec, LinearMap.id_apply]

/-- The idempotent `Λ = 1 - d ∘ Φ`. -/
def Lam : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) := LinearMap.id - sect.comp Phi

lemma Phi_comp_Lam : Phi.comp Lam = 0 := by
  rw [Lam, LinearMap.comp_sub, LinearMap.comp_id, ← LinearMap.comp_assoc, sect_spec,
    LinearMap.id_comp, sub_self]

lemma Lam_comp_sect : Lam.comp sect = 0 := by
  rw [Lam, LinearMap.sub_comp, LinearMap.id_comp, LinearMap.comp_assoc, sect_spec,
    LinearMap.comp_id, sub_self]

lemma Phi_Lam_apply (x : Fin 6 → ℂ) : Phi (Lam x) = 0 := by
  rw [← LinearMap.comp_apply, Phi_comp_Lam, LinearMap.zero_apply]

lemma Lam_sect_apply (y : Qodd) : Lam (sect y) = 0 := by
  rw [← LinearMap.comp_apply, Lam_comp_sect, LinearMap.zero_apply]

lemma Lam_apply_self (x : Fin 6 → ℂ) : Lam (Lam x) = Lam x := by
  have hx : Lam x = x - sect (Phi x) := rfl
  rw [hx, map_sub, hx, Lam_sect_apply, sub_zero]

/-- The lift of the right action of `γ` to `ℂ⁶`. -/
def sHat (γ : SL(2,ℤ)) : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) :=
  sect.comp ((act γ).comp Phi) + Lam

lemma sHat_comp_apply (γ δ : SL(2,ℤ)) (x : Fin 6 → ℂ) :
    sHat δ (sHat γ x) = sHat (γ * δ) x := by
  have hcomp : act δ (act γ (Phi x)) = act (γ * δ) (Phi x) := by
    rw [← act_comp γ δ, LinearMap.comp_apply]
  have hu : Phi (sect (act γ (Phi x)) + Lam x) = act γ (Phi x) := by
    rw [map_add, Phi_sect_apply, Phi_Lam_apply, add_zero]
  have hl : Lam (sect (act γ (Phi x)) + Lam x) = Lam x := by
    rw [map_add, Lam_sect_apply, Lam_apply_self, zero_add]
  simp only [sHat, LinearMap.add_apply, LinearMap.comp_apply]
  rw [hu, hl, hcomp]

lemma sHat_comp (γ δ : SL(2,ℤ)) : (sHat δ).comp (sHat γ) = sHat (γ * δ) :=
  LinearMap.ext (sHat_comp_apply γ δ)

/-! ## The representation `σ` -/

/-- The six-dimensional representation `σ` of `SL(2,ℤ)`, as a matrix. -/
def sigmaMat (γ : SL(2,ℤ)) : Matrix (Fin 6) (Fin 6) ℂ :=
  (LinearMap.toMatrix' (sHat γ)).transpose

lemma sigmaMat_row (γ : SL(2,ℤ)) (i : Fin 6) (j : Fin 6) :
    sigmaMat γ i j = sHat γ (Pi.single i 1) j := by
  rw [sigmaMat, Matrix.transpose_apply, LinearMap.toMatrix'_apply]

/-- `σ` is a monoid homomorphism. -/
def sigmaHom : Matrix.SpecialLinearGroup (Fin 2) ℤ →* Matrix (Fin 6) (Fin 6) ℂ where
  toFun := sigmaMat
  map_one' := by
    have h : sHat (1 : SL(2,ℤ)) = LinearMap.id := by
      rw [sHat, act_one, LinearMap.id_comp]
      apply LinearMap.ext
      intro x
      simp only [Lam, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.comp_apply]
      abel
    show sigmaMat 1 = 1
    rw [sigmaMat, h, LinearMap.toMatrix'_id, Matrix.transpose_one]
  map_mul' γ δ := by
    show sigmaMat (γ * δ) = sigmaMat γ * sigmaMat δ
    rw [sigmaMat, sigmaMat, sigmaMat, ← Matrix.transpose_mul, ← sHat_comp γ δ,
      LinearMap.toMatrix'_comp]

theorem exists_sigma_odd :
    ∃ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ →* Matrix (Fin 6) (Fin 6) ℂ,
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (i : Fin 6),
        Work.Asymptotics.MpElem i * Work.Asymptotics.ofSL γ -
          ∑ j, (σ γ) i j • Work.Asymptotics.MpElem j ∈ Work.Asymptotics.idealIOdd := by
  refine ⟨sigmaHom, ?_⟩
  intro γ i
  have hkey : Submodule.mkQ idealIOdd
      (MpElem i * ofSL γ - ∑ j, (sigmaMat γ) i j • MpElem j) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul]
    rw [← act_mkQ γ (MpElem i), ← Phi_single i]
    have hsum : (∑ j, (sigmaMat γ) i j • Submodule.mkQ idealIOdd (MpElem j))
        = Phi (sHat γ (Pi.single i 1)) := by
      rw [Phi]
      apply Finset.sum_congr rfl
      intro j _
      rw [sigmaMat_row]
    rw [hsum, sHat, LinearMap.add_apply, LinearMap.comp_apply, map_add, Phi_sect_apply,
      Phi_Lam_apply, add_zero, LinearMap.comp_apply, sub_self]
  exact (Submodule.Quotient.mk_eq_zero idealIOdd).mp hkey

end Work.Asymptotics
