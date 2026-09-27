import Mathlib
import Submission.Work.KT.FPatch

/-!
# Free patched modules have trivial gluing (`Work.KT.patched_free_units`)

Let `R = FiberProd ρ₁ ρ₂` be the fibre product of `A₁` and `A₂` over `A₀` (two rings glued along a
common quotient), and let `P = patched hcomm n γ` be the patched module of a gluing
`γ : Matrix (Fin n) (Fin n) A₀`, i.e. the `R`-module of pairs `(f,g)` with `ρ₁ f = γ · ρ₂ g`.

If `P` is free of rank `n` (an `R`-linear isomorphism `e : P ≃ₗ Rⁿ` is given) and `γ` is a unit,
then the two trivialisations of the glued bundle differ by units: there are `G₁ ∈ GL_n(A₁)`,
`G₂ ∈ GL_n(A₂)` with `ρ₁ G₁ = γ · ρ₂ G₂`.

The proof extracts the two component matrices `patchF`, `patchG` of `e.symm` and shows both are
units.  `patchF` is a unit because `e.symm` is surjective and `ρ₂` is surjective (so a preimage in
`P` can always be manufactured from a vector over `A₁`).  For `patchG`, its reduction modulo
`ker ρ₂ = ker(fstHom)` is `γ⁻¹ ρ₁ patchF`, hence a unit, and `e` restricts to a bijection between
`(ker fstHom)ⁿ ⊆ Rⁿ` and `{0} × (ker ρ₂)ⁿ ⊆ P`, which says exactly that `patchG` maps `(ker ρ₂)ⁿ`
onto `(ker ρ₂)ⁿ`; the two facts together force `patchG` to be surjective.
-/

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

variable {A₁ A₂ A₀ : Type} [Ring A₁] [Ring A₂] [Ring A₀]
    {ρ₁ : A₁ →+* A₀} {ρ₂ : A₂ →+* A₀}

/-! ## Elementary fibre-product calculus -/

section SmulCalc

variable {n : ℕ}

lemma FiberProd.smul_fst_apply (a : FiberProd ρ₁ ρ₂) (v : Fin n → A₁) (i : Fin n) :
    (a • v) i = a.1.1 * v i := by
  show (FiberProd.fstHom a • v) i = a.1.1 * v i
  rw [Pi.smul_apply, FiberProd.fstHom_apply, smul_eq_mul]

lemma FiberProd.smul_snd_apply (a : FiberProd ρ₁ ρ₂) (v : Fin n → A₂) (i : Fin n) :
    (a • v) i = a.1.2 * v i := by
  show (FiberProd.sndHom a • v) i = a.1.2 * v i
  rw [Pi.smul_apply, FiberProd.sndHom_apply, smul_eq_mul]

lemma FiberProd.eq_sum_single (x : Fin n → FiberProd ρ₁ ρ₂) :
    x = ∑ j, x j • Pi.single j (1 : FiberProd ρ₁ ρ₂) := by
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp [Pi.smul_apply]
  · intro b _ hb; simp only [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

end SmulCalc

/-! ## The two component matrices of an isomorphism -/

section Setup

variable {n : ℕ} (hcomm : ∀ x y : A₀, x * y = y * x)
    (γ : Matrix (Fin n) (Fin n) A₀)
    (e : FiberProd.patched (ρ₁ := ρ₁) (ρ₂ := ρ₂) hcomm n γ ≃ₗ[FiberProd ρ₁ ρ₂]
          (Fin n → FiberProd ρ₁ ρ₂))

/-- The `A₁`-component matrix of `e.symm`. -/
def patchF : Matrix (Fin n) (Fin n) A₁ :=
  fun i j => (e.symm (Pi.single j (1 : FiberProd ρ₁ ρ₂))).1.1 i

/-- The `A₂`-component matrix of `e.symm`. -/
def patchG : Matrix (Fin n) (Fin n) A₂ :=
  fun i j => (e.symm (Pi.single j (1 : FiberProd ρ₁ ρ₂))).1.2 i

lemma patchF_eq (j : Fin n) :
    (fun i => patchF hcomm γ e i j) = (e.symm (Pi.single j (1 : FiberProd ρ₁ ρ₂))).1.1 := rfl

lemma patchG_eq (j : Fin n) :
    (fun i => patchG hcomm γ e i j) = (e.symm (Pi.single j (1 : FiberProd ρ₁ ρ₂))).1.2 := rfl

/-- `e.symm` is given on the first factor by the matrix `patchF`. -/
lemma patch_component_fst (hA₁ : ∀ x y : A₁, x * y = y * x) (x : Fin n → FiberProd ρ₁ ρ₂) :
    (e.symm x).1.1 = (patchF hcomm γ e).mulVec (fun j => (x j).1.1) := by
  have hsum : e.symm x = ∑ j, x j • e.symm (Pi.single j (1 : FiberProd ρ₁ ρ₂)) := by
    conv_lhs => rw [show x = ∑ j, x j • Pi.single j (1 : FiberProd ρ₁ ρ₂)
      from FiberProd.eq_sum_single x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
  have h1 : ((∑ j, x j • e.symm (Pi.single j (1 : FiberProd ρ₁ ρ₂)) :
        FiberProd.patched (ρ₁ := ρ₁) (ρ₂ := ρ₂) hcomm n γ) : (Fin n → A₁) × (Fin n → A₂))
      = ∑ j, x j • (e.symm (Pi.single j (1 : FiberProd ρ₁ ρ₂)) : (Fin n → A₁) × (Fin n → A₂)) := by
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun j _ => Submodule.coe_smul _ _
  have hΦ : (e.symm x).1.1 = ∑ j, x j • (fun i => patchF hcomm γ e i j) := by
    rw [hsum, h1, Prod.fst_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Prod.smul_fst, patchF_eq]
  rw [hΦ]
  funext i
  rw [Finset.sum_apply, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by rw [FiberProd.smul_fst_apply, hA₁]

/-- `e.symm` is given on the second factor by the matrix `patchG`. -/
lemma patch_component_snd (hA₂ : ∀ x y : A₂, x * y = y * x) (x : Fin n → FiberProd ρ₁ ρ₂) :
    (e.symm x).1.2 = (patchG hcomm γ e).mulVec (fun j => (x j).1.2) := by
  have hsum : e.symm x = ∑ j, x j • e.symm (Pi.single j (1 : FiberProd ρ₁ ρ₂)) := by
    conv_lhs => rw [show x = ∑ j, x j • Pi.single j (1 : FiberProd ρ₁ ρ₂)
      from FiberProd.eq_sum_single x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
  have h1 : ((∑ j, x j • e.symm (Pi.single j (1 : FiberProd ρ₁ ρ₂)) :
        FiberProd.patched (ρ₁ := ρ₁) (ρ₂ := ρ₂) hcomm n γ) : (Fin n → A₁) × (Fin n → A₂))
      = ∑ j, x j • (e.symm (Pi.single j (1 : FiberProd ρ₁ ρ₂)) : (Fin n → A₁) × (Fin n → A₂)) := by
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun j _ => Submodule.coe_smul _ _
  have hΦ : (e.symm x).1.2 = ∑ j, x j • (fun i => patchG hcomm γ e i j) := by
    rw [hsum, h1, Prod.snd_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Prod.smul_snd, patchG_eq]
  rw [hΦ]
  funext i
  rw [Finset.sum_apply, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => by rw [FiberProd.smul_snd_apply, hA₂]

/-- The defining relation of the patched module, in matrix form. -/
lemma patchF_rho :
    RingHom.mapMatrix ρ₁ (patchF hcomm γ e)
      = γ * RingHom.mapMatrix ρ₂ (patchG hcomm γ e) := by
  ext i j
  have hrel : (fun i => ρ₁ (patchF hcomm γ e i j))
      = γ.mulVec (fun i => ρ₂ (patchG hcomm γ e i j)) :=
    (e.symm (Pi.single j (1 : FiberProd ρ₁ ρ₂))).2
  have hc := congrFun hrel i
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.mulVec,
    dotProduct] using hc

/-- Componentwise image of `mulVec` under a ring homomorphism. -/
lemma map_mulVec (M : Matrix (Fin n) (Fin n) A₂) (v : Fin n → A₂) :
    (fun i => ρ₂ (M.mulVec v i))
      = (RingHom.mapMatrix ρ₂ M).mulVec (fun j => ρ₂ (v j)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum,
    map_mul]

/-- A unit matrix annihilates only the zero vector. -/
lemma mulVec_eq_zero_of_isUnit {R : Type} [CommRing R] {m : ℕ}
    {M : Matrix (Fin m) (Fin m) R} (hM : IsUnit M) {u : Fin m → R} (hu : M.mulVec u = 0) :
    u = 0 := by
  obtain ⟨N, hN⟩ := hM.exists_left_inv
  calc u = (1 : Matrix (Fin m) (Fin m) R).mulVec u := (Matrix.one_mulVec u).symm
    _ = (N * M).mulVec u := by rw [hN]
    _ = N.mulVec (M.mulVec u) := (Matrix.mulVec_mulVec u N M).symm
    _ = 0 := by rw [hu, Matrix.mulVec_zero]

/-- The `A₁`-component of `e.symm` is a unit whenever `ρ₂` is surjective and `γ` is a unit. -/
lemma patchF_isUnit (hA₁ : ∀ x y : A₁, x * y = y * x) (hρ₂ : Function.Surjective ρ₂)
    (hγ : IsUnit γ) : IsUnit (patchF hcomm γ e) := by
  letI : CommRing A₀ := { ‹Ring A₀› with mul_comm := hcomm }
  letI : CommRing A₁ := { ‹Ring A₁› with mul_comm := hA₁ }
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  intro v
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hγ (fun i => ρ₁ (v i))
  choose y hy using fun j => hρ₂ (c j)
  have hp : (fun i => ρ₁ (v i)) = γ.mulVec (fun i => ρ₂ (y i)) := by
    rw [show (fun i => ρ₂ (y i)) = c from funext hy, hc]
  let z : FiberProd.patched (ρ₁ := ρ₁) (ρ₂ := ρ₂) hcomm n γ := ⟨(v, y), hp⟩
  refine ⟨fun j => ((e z) j).1.1, ?_⟩
  have hcomp := patch_component_fst hcomm γ e hA₁ (e z)
  rw [e.symm_apply_apply] at hcomp
  rw [← hcomp]

/-- Nakayama-style step: a square matrix whose reduction modulo an ideal `J` is surjective and
which maps `Jⁿ` onto `Jⁿ` has surjective `mulVec`. -/
lemma mulVec_surj_of_mod_ideal {R : Type} [CommRing R] (J : Ideal R) {m : ℕ}
    (M : Matrix (Fin m) (Fin m) R)
    (h₁ : ∀ v : Fin m → R, ∃ w : Fin m → R, ∀ i, v i - M.mulVec w i ∈ J)
    (h₂ : ∀ w : Fin m → R, (∀ i, w i ∈ J) →
      ∃ w' : Fin m → R, (∀ i, w' i ∈ J) ∧ M.mulVec w' = w) :
    ∀ v : Fin m → R, ∃ w : Fin m → R, M.mulVec w = v := by
  intro v
  obtain ⟨w₀, hw₀⟩ := h₁ v
  obtain ⟨w', hw'J, hw'⟩ := h₂ (fun i => v i - M.mulVec w₀ i) hw₀
  refine ⟨w₀ + w', ?_⟩
  rw [Matrix.mulVec_add, hw']
  funext i
  simp

/-- The `A₂`-component of `e.symm` is a unit whenever `ρ₂` is surjective, `γ` is a unit and the
patched module is free of rank `n`. -/
lemma patchG_isUnit (hA₁ : ∀ x y : A₁, x * y = y * x) (hA₂ : ∀ x y : A₂, x * y = y * x)
    (hρ₂ : Function.Surjective ρ₂) (hγ : IsUnit γ) : IsUnit (patchG hcomm γ e) := by
  letI : CommRing A₀ := { ‹Ring A₀› with mul_comm := hcomm }
  letI : CommRing A₁ := { ‹Ring A₁› with mul_comm := hA₁ }
  letI : CommRing A₂ := { ‹Ring A₂› with mul_comm := hA₂ }
  have hFunit : IsUnit (patchF hcomm γ e) := patchF_isUnit hcomm γ e hA₁ hρ₂ hγ
  have hunitG : IsUnit (RingHom.mapMatrix ρ₂ (patchG hcomm γ e)) := by
    have h1 : IsUnit (RingHom.mapMatrix ρ₁ (patchF hcomm γ e)) :=
      hFunit.map (RingHom.mapMatrix ρ₁)
    rw [patchF_rho hcomm γ e, IsUnit.mul_iff] at h1
    exact h1.2
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  refine mulVec_surj_of_mod_ideal (RingHom.ker ρ₂) (patchG hcomm γ e) ?_ ?_
  · intro v
    obtain ⟨w', hw'⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunitG (fun i => ρ₂ (v i))
    choose w hw using fun j => hρ₂ (w' j)
    refine ⟨w, fun i => ?_⟩
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    have hmap : (fun i => ρ₂ ((patchG hcomm γ e).mulVec w i)) = fun i => ρ₂ (v i) := by
      rw [map_mulVec, show (fun j => ρ₂ (w j)) = w' from funext hw, hw']
    exact (congrFun hmap i).symm
  · intro w hw
    have hw0 : (fun i => ρ₂ (w i)) = 0 := by
      funext i; simpa using hw i
    have hp : (fun i => ρ₁ ((0 : Fin n → A₁) i)) = γ.mulVec (fun i => ρ₂ (w i)) := by
      rw [hw0]; funext i; simp [Matrix.mulVec, dotProduct]
    let z : FiberProd.patched (ρ₁ := ρ₁) (ρ₂ := ρ₂) hcomm n γ := ⟨((0 : Fin n → A₁), w), hp⟩
    have hc1 := patch_component_fst hcomm γ e hA₁ (e z)
    rw [e.symm_apply_apply] at hc1
    have hc2 := patch_component_snd hcomm γ e hA₂ (e z)
    rw [e.symm_apply_apply] at hc2
    have hzero : (fun j => ((e z) j).1.1) = 0 := by
      refine mulVec_eq_zero_of_isUnit hFunit ?_
      rw [← hc1]
    refine ⟨fun j => ((e z) j).1.2, fun i => ?_, ?_⟩
    · rw [RingHom.mem_ker]
      have h2 := FiberProd.rho_fst ((e z) i)
      rw [show ((e z) i).1.1 = 0 from congrFun hzero i, map_zero] at h2
      exact h2.symm
    · rw [← hc2]

end Setup

/-- If the patched module of an *invertible* gluing `γ` is free of rank `n`, then the two
trivializations of the glued bundle differ by a *unit* over each of the two factors: there are
units `G₁`, `G₂` with `ρ₁ G₁ = γ * ρ₂ G₂` (equivalently `γ = ρ₁ G₁ * (ρ₂ G₂)⁻¹`).

(The invertibility of `γ` is needed: over `A₁ = A₂ = A₀ = ℤ`, `ρᵢ = id`, `γ = (2)` has free
patched module but is not a product of units.  Surjectivity of `ρ₂` supplies the lifts used in the
surjectivity argument, and commutativity of `A₁`, `A₂` makes a surjective square matrix
invertible.  The components of the isomorphism are `G₁`, `G₂`. -/
theorem patched_free_units {A₁ A₂ A₀ : Type} [Ring A₁] [Ring A₂] [Ring A₀]
    {ρ₁ : A₁ →+* A₀} {ρ₂ : A₂ →+* A₀} (hcomm : ∀ x y : A₀, x * y = y * x)
    (hA₁ : ∀ x y : A₁, x * y = y * x) (hA₂ : ∀ x y : A₂, x * y = y * x)
    (hρ₂ : Function.Surjective ρ₂) {n : ℕ} (γ : Matrix (Fin n) (Fin n) A₀) (hγ : IsUnit γ)
    (e : Work.KT.FiberProd.patched (ρ₁ := ρ₁) (ρ₂ := ρ₂) hcomm n γ
      ≃ₗ[Work.KT.FiberProd ρ₁ ρ₂] (Fin n → Work.KT.FiberProd ρ₁ ρ₂)) :
    ∃ (G₁ : (Matrix (Fin n) (Fin n) A₁)ˣ) (G₂ : (Matrix (Fin n) (Fin n) A₂)ˣ),
      RingHom.mapMatrix ρ₁ (↑G₁ : Matrix (Fin n) (Fin n) A₁) =
        γ * RingHom.mapMatrix ρ₂ (↑G₂ : Matrix (Fin n) (Fin n) A₂) := by
  have hF := patchF_isUnit hcomm γ e hA₁ hρ₂ hγ
  have hG := patchG_isUnit hcomm γ e hA₁ hA₂ hρ₂ hγ
  refine ⟨hF.unit, hG.unit, ?_⟩
  rw [hF.unit_spec, hG.unit_spec]
  exact patchF_rho hcomm γ e

end

end Work.KT
