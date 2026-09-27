import Mathlib
import Submission.Work.KT.ExtGen.Triple
import Submission.Work.KT.ExtGen.TripleBdry

/-!
# `Work.KT.ExtGen.bdry_aux` — chart projections used in the lift of `bdry_lift`

Support definitions for `Work.KT.ExtGen.bdry_lift`:

* `projVZ`, `pullProjVZ` — the "missing" chart inclusion `prodAlg V Z →ₐ[ℂ] tripleAlg V W Z`
  (pull-back along `(v,w,z) ↦ (v,z)`);
* `bdryFst`, `bdrySnd`, `bdryTrd` — the three components of the fibre product `bdryAlg`;
* `bdryRestZ`, `bdryRestW`, `bdryRestV` — the compositions with the chart restrictions to the
  base-point slices, giving matrices over `Kpair Z`, `Kpair W`, `Kpair V`;
* `bdryCornerZ`, `bdryCornerW`, `bdryCornerV` — the corner augmentations; they all agree on
  `bdryAlg` (the "corner value").
-/

namespace Work.KT.ExtGen

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

variable (V W Z : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-! ## The chart inclusion `prodAlg V Z → tripleAlg V W Z` -/

/-- The projection `(v,w,z) ↦ (v,z)`. -/
def projVZ : C(Ball (V × (W × Z)), Ball (V × Z)) where
  toFun x := ⟨((x : V × (W × Z)).1, (x : V × (W × Z)).2.2), by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Prod.norm_def]
    exact max_le (norm_fst_le' V W Z x) (norm_zc_le V W Z x)⟩
  continuous_toFun := by fun_prop

@[simp] lemma projVZ_apply (x : Ball (V × (W × Z))) :
    (projVZ V W Z x : V × Z) = ((x : V × (W × Z)).1, (x : V × (W × Z)).2.2) := rfl

/-- The chart inclusion `prodAlg V Z →ₐ[ℂ] tripleAlg V W Z` (pull-back along `(v,w,z) ↦ (v,z)`). -/
def pullProjVZ : prodAlg V Z →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict ((pullAlg (projVZ V W Z)).comp (prodAlg V Z).val) (tripleAlg V W Z) (by
    intro F
    obtain ⟨hF1, hF2⟩ := F.2
    refine ⟨fun z z' h1 h2 _ h4 => ?_, fun z z' _ _ h3 h4 => ?_, fun z z' h1 h2 h3 h4 => ?_⟩
    · exact hF1 _ _ h1 h2 h4
    · exact congrArg (fun y : Ball (V × Z) => (F : C(Ball (V × Z), ℂ)) y)
        (Subtype.ext (Prod.ext h4 h3))
    · exact hF2 _ _ h1 h2 h4)

@[simp] lemma pullProjVZ_apply (F : prodAlg V Z) :
    ((pullProjVZ V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (pullAlg (projVZ V W Z)) (F : C(Ball (V × Z), ℂ)) := rfl

/-! ## The three components of the fibre product -/

/-- The projection of `bdryAlg` onto the `(W,Z)`-chart. -/
def bdryFst (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg W Z :=
  (AlgHom.fst ℂ (prodAlg W Z) (prodAlg V Z × prodAlg V W)).comp
    (bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0).val

/-- The projection of `bdryAlg` onto the `(V,Z)`-chart. -/
def bdrySnd (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg V Z :=
  ((AlgHom.fst ℂ (prodAlg V Z) (prodAlg V W)).comp
    (AlgHom.snd ℂ (prodAlg W Z) (prodAlg V Z × prodAlg V W))).comp
    (bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0).val

/-- The projection of `bdryAlg` onto the `(V,W)`-chart. -/
def bdryTrd (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) :
    bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] prodAlg V W :=
  ((AlgHom.snd ℂ (prodAlg V Z) (prodAlg V W)).comp
    (AlgHom.snd ℂ (prodAlg W Z) (prodAlg V Z × prodAlg V W))).comp
    (bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0).val

@[simp] lemma bdryFst_apply (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W)
    (hw0 : w0 ∈ bdry W) (z0 : Ball Z) (hz0 : z0 ∈ bdry Z)
    (p : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0) :
    (bdryFst V W Z v0 hv0 w0 hw0 z0 hz0 p : prodAlg W Z) = p.1.1 := rfl

@[simp] lemma bdrySnd_apply (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W)
    (hw0 : w0 ∈ bdry W) (z0 : Ball Z) (hz0 : z0 ∈ bdry Z)
    (p : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0) :
    (bdrySnd V W Z v0 hv0 w0 hw0 z0 hz0 p : prodAlg V Z) = p.1.2.1 := rfl

@[simp] lemma bdryTrd_apply (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W)
    (hw0 : w0 ∈ bdry W) (z0 : Ball Z) (hz0 : z0 ∈ bdry Z)
    (p : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0) :
    (bdryTrd V W Z v0 hv0 w0 hw0 z0 hz0 p : prodAlg V W) = p.1.2.2 := rfl

/-! ## Restrictions of the fibre product to the three base-point faces -/

/-- Restriction of `bdryAlg` to the `z₀`-face, landing in `Kpair Z`. -/
def bdryRestZ (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] Kpair Z :=
  (sliceW W Z w0 hw0).comp (bdryFst V W Z v0 hv0 w0 hw0 z0 hz0)

/-- Restriction of `bdryAlg` to the `w₀`-face, landing in `Kpair W`. -/
def bdryRestW (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] Kpair W :=
  (sliceV W Z z0 hz0).comp (bdryFst V W Z v0 hv0 w0 hw0 z0 hz0)

/-- Restriction of `bdryAlg` to the `v₀`-face, landing in `Kpair V`. -/
def bdryRestV (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] Kpair V :=
  (sliceV V Z z0 hz0).comp (bdrySnd V W Z v0 hv0 w0 hw0 z0 hz0)

/-! ## The corner augmentations -/

/-- The corner augmentation of `bdryAlg` through the `Z`-face. -/
def bdryCornerZ (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] ℂ :=
  (augPair Z z0).comp (bdryRestZ V W Z v0 hv0 w0 hw0 z0 hz0)

/-- The corner augmentation of `bdryAlg` through the `W`-face. -/
def bdryCornerW (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] ℂ :=
  (augPair W w0).comp (bdryRestW V W Z v0 hv0 w0 hw0 z0 hz0)

/-- The corner augmentation of `bdryAlg` through the `V`-face. -/
def bdryCornerV (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
    (z0 : Ball Z) (hz0 : z0 ∈ bdry Z) : bdryAlg V W Z v0 hv0 w0 hw0 z0 hz0 →ₐ[ℂ] ℂ :=
  (augPair V v0).comp (bdryRestV V W Z v0 hv0 w0 hw0 z0 hz0)


/-! ## Composition of the chart inclusions with the three slices -/

section Slices

variable (v0 : Ball V) (hv0 : v0 ∈ bdry V) (w0 : Ball W) (hw0 : w0 ∈ bdry W)
  (z0 : Ball Z) (hz0 : z0 ∈ bdry Z)

/-! ### The slice at `v₀` -/

lemma sliceV0_comp_tripleInclWZ :
    (sliceV0 V W Z v0 hv0).comp (tripleInclWZ V W Z) = AlgHom.id ℂ (prodAlg W Z) := by
  ext F p
  rfl

lemma sliceV0_comp_triplePullZ :
    (sliceV0 V W Z v0 hv0).comp (triplePullZ V W Z) = pullSnd W Z := by
  ext F p
  rfl

lemma sliceV0_comp_pullProjVZ :
    (sliceV0 V W Z v0 hv0).comp (pullProjVZ V W Z)
      = (pullSnd W Z).comp (sliceW V Z v0 hv0) := by
  ext F p
  rfl

lemma sliceV0_comp_triplePullV :
    (sliceV0 V W Z v0 hv0).comp (triplePullV V W Z)
      = (Algebra.ofId ℂ (prodAlg W Z)).comp (augPair V v0) := by
  ext F p
  rfl

lemma sliceV0_comp_algebraMap :
    (sliceV0 V W Z v0 hv0).comp (Algebra.ofId ℂ (tripleAlg V W Z))
      = Algebra.ofId ℂ (prodAlg W Z) := by
  exact AlgHom.ext fun F => rfl

lemma sliceV0_comp_triplePullW :
    (sliceV0 V W Z v0 hv0).comp (triplePullW V W Z) = pullFst W Z := by
  ext F p
  rfl

lemma sliceV0_comp_tripleInclPW :
    (sliceV0 V W Z v0 hv0).comp (tripleInclPW V W Z)
      = (pullFst W Z).comp (sliceW V W v0 hv0) := by
  ext F p
  rfl

/-! ### The slice at `w₀` -/

lemma sliceW0_comp_tripleInclWZ :
    (sliceW0 V W Z w0 hw0).comp (tripleInclWZ V W Z)
      = (pullSnd V Z).comp (sliceW W Z w0 hw0) := by
  ext F p
  rfl

lemma sliceW0_comp_triplePullZ :
    (sliceW0 V W Z w0 hw0).comp (triplePullZ V W Z) = pullSnd V Z := by
  ext F p
  rfl

lemma sliceW0_comp_pullProjVZ :
    (sliceW0 V W Z w0 hw0).comp (pullProjVZ V W Z) = AlgHom.id ℂ (prodAlg V Z) := by
  ext F p
  rfl

lemma sliceW0_comp_triplePullV :
    (sliceW0 V W Z w0 hw0).comp (triplePullV V W Z) = pullFst V Z := by
  ext F p
  rfl

lemma sliceW0_comp_algebraMap :
    (sliceW0 V W Z w0 hw0).comp (Algebra.ofId ℂ (tripleAlg V W Z))
      = Algebra.ofId ℂ (prodAlg V Z) := by
  exact AlgHom.ext fun F => rfl

lemma sliceW0_comp_triplePullW :
    (sliceW0 V W Z w0 hw0).comp (triplePullW V W Z)
      = (Algebra.ofId ℂ (prodAlg V Z)).comp (augPair W w0) := by
  ext F p
  rfl

lemma sliceW0_comp_tripleInclPW :
    (sliceW0 V W Z w0 hw0).comp (tripleInclPW V W Z)
      = (pullFst V Z).comp (sliceV V W w0 hw0) := by
  ext F p
  rfl

/-! ### The slice at `z₀` -/

lemma sliceZ0_comp_tripleInclWZ :
    (sliceZ0 V W Z z0 hz0).comp (tripleInclWZ V W Z)
      = (pullSnd V W).comp (sliceV W Z z0 hz0) := by
  ext F p
  rfl

lemma sliceZ0_comp_triplePullZ :
    (sliceZ0 V W Z z0 hz0).comp (triplePullZ V W Z)
      = (Algebra.ofId ℂ (prodAlg V W)).comp (augPair Z z0) := by
  ext F p
  rfl

lemma sliceZ0_comp_pullProjVZ :
    (sliceZ0 V W Z z0 hz0).comp (pullProjVZ V W Z)
      = (pullFst V W).comp (sliceV V Z z0 hz0) := by
  ext F p
  rfl

lemma sliceZ0_comp_triplePullV :
    (sliceZ0 V W Z z0 hz0).comp (triplePullV V W Z) = pullFst V W := by
  ext F p
  rfl

lemma sliceZ0_comp_algebraMap :
    (sliceZ0 V W Z z0 hz0).comp (Algebra.ofId ℂ (tripleAlg V W Z))
      = Algebra.ofId ℂ (prodAlg V W) := by
  exact AlgHom.ext fun F => rfl

lemma sliceZ0_comp_triplePullW :
    (sliceZ0 V W Z z0 hz0).comp (triplePullW V W Z) = pullSnd V W := by
  ext F p
  rfl

lemma sliceZ0_comp_tripleInclPW :
    (sliceZ0 V W Z z0 hz0).comp (tripleInclPW V W Z) = AlgHom.id ℂ (prodAlg V W) := by
  ext F p
  rfl

/-! ## The projections out of `bdryAlg` and the restriction map -/

lemma bdryFst_comp_bdryProj :
    (bdryFst V W Z v0 hv0 w0 hw0 z0 hz0).comp (bdryProj V W Z v0 hv0 w0 hw0 z0 hz0)
      = sliceV0 V W Z v0 hv0 := rfl

lemma bdrySnd_comp_bdryProj :
    (bdrySnd V W Z v0 hv0 w0 hw0 z0 hz0).comp (bdryProj V W Z v0 hv0 w0 hw0 z0 hz0)
      = sliceW0 V W Z w0 hw0 := rfl

lemma bdryTrd_comp_bdryProj :
    (bdryTrd V W Z v0 hv0 w0 hw0 z0 hz0).comp (bdryProj V W Z v0 hv0 w0 hw0 z0 hz0)
      = sliceZ0 V W Z z0 hz0 := rfl

end Slices

/-! ## General matrix/unit helpers -/

section Helpers

variable {n : ℕ} {A B C : Type*} [Semiring A] [Semiring B] [Semiring C]

/-- `RingHom.mapMatrix` is compatible with composition of ring homs. -/
lemma RingHom.mapMatrix_comp (f : B →+* C) (g : A →+* B) :
    (RingHom.mapMatrix (m := Fin n) (f.comp g) :
        Matrix (Fin n) (Fin n) A →+* Matrix (Fin n) (Fin n) C)
      = ((RingHom.mapMatrix (m := Fin n) f).comp (RingHom.mapMatrix (m := Fin n) g)) := by
  ext M i j
  rfl

/-- Mapping a matrix along two successive ring homs is mapping along the composite. -/
lemma Matrix.map_map_comp (f : A →+* B) (g : B →+* C) (M : Matrix (Fin n) (Fin n) A) :
    (M.map ⇑f).map ⇑g = M.map ⇑(g.comp f) := by
  ext i j
  rfl

/-- The coercion of `Units.map (RingHom.mapMatrix f) u` is the matrix map of the coercion. -/
lemma Units.coe_mapMatrix (f : A →+* B) (u : (Matrix (Fin n) (Fin n) A)ˣ) :
    ((Units.map (RingHom.mapMatrix (m := Fin n) f) u : (Matrix (Fin n) (Fin n) B)ˣ) :
        Matrix (Fin n) (Fin n) B) = (↑u : Matrix (Fin n) (Fin n) A).map ⇑f := rfl

end Helpers

section Helpers2

variable {n : ℕ} {A B : Type*} [Ring A] [Ring B]

/-- The inverse of a matrix unit, mapped along a ring hom, multiplies against the image of the
unit to give `1`. -/
lemma Matrix.map_unit_inv_mul (f : A →+* B) (u : (Matrix (Fin n) (Fin n) A)ˣ) :
    ((↑(u⁻¹) : Matrix (Fin n) (Fin n) A).map ⇑f) * ((↑u : Matrix (Fin n) (Fin n) A).map ⇑f)
      = 1 := by
  rw [← Matrix.map_mul (f := f), Units.inv_mul]
  exact Matrix.map_one ⇑f f.map_zero f.map_one

end Helpers2


section Helpers3

variable {n : ℕ} {A B C : Type*} [Semiring A] [Semiring B] [Semiring C]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]

/-- Mapping a matrix along two composed algebra homs. -/
lemma Matrix.map_map_algHom (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] C) (M : Matrix (Fin n) (Fin n) A) :
    (M.map ⇑f).map ⇑g = M.map ⇑(g.comp f) := by
  ext i j
  rfl

end Helpers3

section Helpers4

variable {n : ℕ} {A B : Type*} [Ring A] [Ring B]

/-- A matrix unit, mapped along a ring hom, multiplies against the image of its inverse to give
`1`. -/
lemma Matrix.map_mul_unit_inv (f : A →+* B) (u : (Matrix (Fin n) (Fin n) A)ˣ) :
    ((↑u : Matrix (Fin n) (Fin n) A).map ⇑f) * ((↑(u⁻¹) : Matrix (Fin n) (Fin n) A).map ⇑f)
      = 1 := by
  rw [← Matrix.map_mul (f := f), Units.mul_inv]
  exact Matrix.map_one ⇑f f.map_zero f.map_one

end Helpers4

/-! ## Telescoping lemmas for products of seven factors -/

section Telescope

variable {M : Type*} [Monoid M]

/-- `a · b · b⁻¹ · c · c⁻¹ · d · d⁻¹ = a` (in multiplicative notation). -/
lemma mul_tele_a {a b c d b' c' d' : M} (hb : b * b' = 1) (hc : c * c' = 1) (hd : d * d' = 1) :
    a * b * b' * c * c' * d * d' = a := by
  rw [mul_assoc a b b', hb, mul_one, mul_assoc a c c', hc, mul_one, mul_assoc a d d', hd,
    mul_one]

/-- `a · a⁻¹ · c · b⁻¹ · d · d⁻¹ · b = c` (in multiplicative notation). -/
lemma mul_tele_b {a a' c b b' d d' : M} (ha : a * a' = 1) (hd : d * d' = 1)
    (hb : b' * b = 1) : a * a' * c * b' * d * d' * b = c := by
  rw [ha, one_mul, mul_assoc (c * b') d d', hd, mul_one, mul_assoc c b' b, hb, mul_one]

/-- `e · x⁻¹ · c · c⁻¹ · x · e⁻¹ · h = h` (in multiplicative notation). -/
lemma mul_tele_c {e e' x x' c c' h : M} (hc : c * c' = 1) (hx : x' * x = 1)
    (he : e * e' = 1) : e * x' * c * c' * x * e' * h = h := by
  rw [mul_assoc (e * x') c c', hc, mul_one, mul_assoc e x' x, hx, mul_one, he, one_mul]

end Telescope


section MatUnitMap

variable {n : ℕ} {A B C : Type*} [Semiring A] [Semiring B] [Semiring C]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]

/-- The map induced by an algebra homomorphism on matrix units. -/
def matUnitMap (φ : A →ₐ[ℂ] B) : (Matrix (Fin n) (Fin n) A)ˣ →* (Matrix (Fin n) (Fin n) B)ˣ :=
  Units.map (RingHom.mapMatrix (m := Fin n) φ.toRingHom)

lemma matUnitMap_apply (φ : A →ₐ[ℂ] B) (u : (Matrix (Fin n) (Fin n) A)ˣ) :
    (↑(matUnitMap φ u) : Matrix (Fin n) (Fin n) B)
      = (↑u : Matrix (Fin n) (Fin n) A).map ⇑φ := rfl

lemma matUnitMap_comp (f : B →ₐ[ℂ] C) (g : A →ₐ[ℂ] B) (u : (Matrix (Fin n) (Fin n) A)ˣ) :
    matUnitMap f (matUnitMap g u) = matUnitMap (f.comp g) u := rfl

end MatUnitMap

end

end Work.KT.ExtGen