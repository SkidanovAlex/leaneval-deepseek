import Submission.Grassmann.Assembly4
import Submission.Commons.LinearAlgebra.Matrix.map_comp_mulVecLin
import Submission.Commons.LinearAlgebra.Matrix.map_ker_mulVecLin

/-!
# The lift of a hybrid predicate to the big space

The switching-roles step of §8 of arXiv:2209.04243 applies the Prop
"switching the roles between the derivatives" **in the role space** `L(V/V₂, W₂)` of a triple
`t = (V₂,W₂,X)`.  Its summands carry the *role-space* hybrid predicate
`hybridPredSub p.1 p.2 (charMat t.1 t.2.1 Z)`, together with the big-space predicate
`hybridPredSub t.1 t.2.1 Z` inherited from `L_{V₂,W₂}`.

This file proves that the conjunction of the two is exactly the **big-space** hybrid predicate at
the *lifted* subspaces (`V₃ = π₂⁻¹(p.1)`, `W₃ = Ip(p.2)`):

  `hybridPredSub t.1 t.2.1 Z ∧ hybridPredSub p.1 p.2 (charMat t.1 t.2.1 Z)
     ↔ hybridPredSub (liftV t.1 p.1) (liftW t.2.1 p.2) Z`.

Equivalently, the big-space hybrid multiplier `L_{V₃,W₃}` is the composition of `L_{V₂,W₂}` with
the role-space multiplier `L_{p.1,p.2}`.

**This is the corrected form of the "identity (i)" of session 24**, which used the *intersection*
`V₃+V₁`, `W₃∩W₁` instead of the *lift* `V₃`; with the intersection the statement is **false**.
(For an `X`-derivative the *restriction maps* are the intersection-type pair — no predicate
condition on `W` is imposed there — while the hybrid **multiplier** `L_{V₃,W₃}` is the lift-type
pair.  The two play different roles and must not be confused.)
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## A `congr` lemma for Fourier multipliers -/

/-- Fourier multipliers with equivalent predicates agree. -/
theorem lapMul_congr {m n : ℕ} {P Q : Matrix (Fin n) (Fin m) (ZMod 2) → Prop}
    (h : ∀ X, P X ↔ Q X) (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    lapMul P f = lapMul Q f := by
  funext A
  rw [lapMul, lapMul]
  refine Finset.sum_congr rfl fun X _ => ?_
  by_cases hP : P X
  · rw [if_pos hP, if_pos ((h X).mp hP)]
  · rw [if_neg hP, if_neg (fun hQ => hP ((h X).mpr hQ))]

/-- The normalised Fourier multiplier also respects equivalence of predicates. -/
theorem lapMulN_congr {m n : ℕ} {P Q : Matrix (Fin n) (Fin m) (ZMod 2) → Prop}
    (h : ∀ X, P X ↔ Q X) (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    lapMulN P f = lapMulN Q f := by
  funext A
  rw [lapMulN, lapMulN, lapMul_congr h]

/-! ## Fourier multipliers are `L²`-contractions

(Note: the *restriction* `restr Q ι` is **not** an `L²`-contraction — it sends `u_Z` to
`u_{QZι}`, so `u_{Z₁} + u_{Z₂}` with `Z₁ ≠ Z₂` in the same fibre can *increase* `l2sq`.  The
correct statement for `restr` is `Prop56Main.l2sq_restr_shift_eq_homSub`: it is the average of
`|g|²` over the fibre `T + homSub(ker Q, range ι)`.  Fourier *projections*, on the other hand,
only remove coefficients and hence decrease `l2sq`.) -/

/-- A Fourier multiplier does not increase `l2sq`. -/
theorem l2sq_lapMulN_le {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    l2sq (lapMulN P f) ≤ l2sq f := by
  rw [l2sq_lapMulN_eq, ← sum_normSq_fcoeff f]
  refine Finset.sum_le_sum fun X _ => ?_
  by_cases hX : P X
  · rw [if_pos hX]
  · rw [if_neg hX]
    positivity

/-- A Fourier multiplier does not increase `(l2sq)²`. -/
theorem sq_l2sq_lapMulN_le {m n : ℕ} (P : Matrix (Fin n) (Fin m) (ZMod 2) → Prop)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    (l2sq (lapMulN P f)) ^ 2 ≤ (l2sq f) ^ 2 :=
  pow_le_pow_left₀ (l2sq_nonneg _) (l2sq_lapMulN_le P f) 2

/-! ## The range of a compressed matrix -/

/-- `Submodule.map` of a composite of matrix maps (the commons lemma `Commons.LinearAlgebra.Matrix.map_comp_mulVecLin`, specialised). -/
theorem map_comp_lin {N N' N'' : ℕ} (f : Matrix (Fin N') (Fin N) 𝔽₂)
    (g : Matrix (Fin N'') (Fin N') 𝔽₂) (S : Submodule 𝔽₂ (Fin N → 𝔽₂)) :
    Submodule.map (g.mulVecLin ∘ₗ f.mulVecLin) S
      = Submodule.map g.mulVecLin (Submodule.map f.mulVecLin S) := by
  ext x
  simp only [Submodule.mem_map, LinearMap.comp_apply]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨f.mulVecLin y, ⟨y, hy, rfl⟩, hxy⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, hxz⟩
    exact ⟨y, hy, hxz⟩

/-- The range of the compression `Qp V₂ * Z * Ip W₂` of a matrix `Z`. -/
theorem range_charMat {N M : ℕ} (V₂ : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin M → 𝔽₂)) (Z : Matrix (Fin N) (Fin M) 𝔽₂) :
    LinearMap.range (charMat V₂ W₂ Z).mulVecLin
      = Submodule.map (Qp V₂).mulVecLin (Submodule.map Z.mulVecLin W₂) := by
  rw [charMat, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.range_comp, range_Ip]
  exact map_comp_lin Z (Qp V₂) W₂

/-- The image of `Q.mulVecLin` on its kernel (the commons lemma `Commons.LinearAlgebra.Matrix.map_ker_mulVecLin`). -/
theorem map_ker_mulVecLin {N N' : ℕ} (Q : Matrix (Fin N') (Fin N) 𝔽₂) :
    Submodule.map Q.mulVecLin (LinearMap.ker Q.mulVecLin) = ⊥ :=
  Commons.LinearAlgebra.Matrix.map_ker_mulVecLin Q

/-- **A subspace is contained in the range of a surjection iff its preimage is contained in the
preimage of the target.** -/
theorem le_range_mul_iff {N N' : ℕ} (Q : Matrix (Fin N') (Fin N) 𝔽₂)
    (hQ : LinearMap.range Q.mulVecLin = ⊤)
    (p : Submodule 𝔽₂ (Fin N' → 𝔽₂)) (N'₀ : Submodule 𝔽₂ (Fin N → 𝔽₂)) :
    p ≤ Submodule.map Q.mulVecLin N'₀ ↔
      Submodule.comap Q.mulVecLin p ≤ N'₀ ⊔ LinearMap.ker Q.mulVecLin := by
  constructor
  · intro h
    have h1 : Submodule.comap Q.mulVecLin p ≤
        Submodule.comap Q.mulVecLin (Submodule.map Q.mulVecLin N'₀) :=
      Submodule.comap_mono h
    rwa [Submodule.comap_map_eq] at h1
  · intro h
    have h1 : Submodule.map Q.mulVecLin (Submodule.comap Q.mulVecLin p) ≤
        Submodule.map Q.mulVecLin (N'₀ ⊔ LinearMap.ker Q.mulVecLin) :=
      Submodule.map_mono h
    rw [Submodule.map_comap_eq, hQ, top_inf_eq] at h1
    have h2 : Submodule.map Q.mulVecLin (N'₀ ⊔ LinearMap.ker Q.mulVecLin) =
        Submodule.map Q.mulVecLin N'₀ := by
      rw [Submodule.map_sup, map_ker_mulVecLin, sup_bot_eq]
    rwa [h2] at h1

/-! ## The kernel condition of the role-space predicate -/

/-- The `∀`-conjunct of the role-space hybrid predicate, expressed with subspaces of the ambient
space. -/
theorem forall_mem_charMat_iff {N M : ℕ} (V₂ : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin M → 𝔽₂)) (Z : Matrix (Fin N) (Fin M) 𝔽₂)
    (p₁ : Submodule 𝔽₂ (Fin (N - Module.finrank 𝔽₂ V₂) → 𝔽₂))
    (p₂ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₂) → 𝔽₂)) :
    (∀ y, (charMat V₂ W₂ Z).mulVec y ∈ p₁ → y ∈ p₂) ↔
      ∀ w ∈ W₂, Z.mulVec w ∈ Submodule.comap (Qp V₂).mulVecLin p₁ →
        w ∈ Submodule.map (Ip W₂).mulVecLin p₂ := by
  constructor
  · intro h w hw hZw
    have hw' : w ∈ LinearMap.range (Ip W₂).mulVecLin := by rw [range_Ip]; exact hw
    rw [LinearMap.range_eq_map, Submodule.mem_map] at hw'
    obtain ⟨y, _, hyw⟩ := hw'
    rw [Matrix.mulVecLin_apply] at hyw
    have h1 : (charMat V₂ W₂ Z).mulVec y ∈ p₁ := by
      rw [charMat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at hZw
      rwa [← hyw] at hZw
    refine Submodule.mem_map.mpr ⟨y, h y h1, ?_⟩
    exact hyw
  · intro h y hy
    have h1 : Z.mulVec ((Ip W₂).mulVec y) ∈ Submodule.comap (Qp V₂).mulVecLin p₁ := by
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply]
      rw [charMat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hy
      exact hy
    have h2 := h _ (by simpa only [Matrix.mulVecLin_apply] using Ip_mem W₂ y) h1
    rw [Submodule.mem_map] at h2
    obtain ⟨y', hy', hyy'⟩ := h2
    rw [Matrix.mulVecLin_apply] at hyy'
    have hz : y' - y ∈ LinearMap.ker (Ip W₂).mulVecLin := by
      rw [LinearMap.mem_ker, map_sub, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
        hyy', sub_self]
    rw [ker_Ip W₂, Submodule.mem_bot] at hz
    rwa [sub_eq_zero.mp hz] at hy'

/-! ## Monotonicity of the hybrid predicate -/

/-- The hybrid predicate is monotone in the pair: a bigger `V` and a smaller `W` give a stronger
condition. -/
theorem hybridPredSub_mono {m n : ℕ} {V V' : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    {W W' : Submodule 𝔽₂ (Fin m → 𝔽₂)} (hV : V' ≤ V) (hW : W ≤ W')
    {X : Matrix (Fin n) (Fin m) 𝔽₂} (h : hybridPredSub V W X) : hybridPredSub V' W' X :=
  ⟨hV.trans h.1, fun w hw => hW (h.2 w (hV hw))⟩

/-! ## The main identity -/

/-- **The corrected identity (i)**: the big-space hybrid condition at `(t.1,t.2.1)` together with
the role-space hybrid condition at `(p.1,p.2)` is the big-space hybrid condition at the lifted
pair `(liftV t.1 p.1, liftW t.2.1 p.2)`. -/
theorem hybridPredSub_conj_iff (t : Triple m n) (p : QPair m n t)
    (Z : Matrix (Fin n) (Fin m) 𝔽₂) :
    (hybridPredSub t.1 t.2.1 Z ∧ hybridPredSub p.1 p.2 (charMat t.1 t.2.1 Z)) ↔
      hybridPredSub (liftV t.1 p.1) (liftW t.2.1 p.2) Z := by
  simp only [hybridPredSub]
  constructor
  · rintro ⟨⟨hV2range, hV2ker⟩, hprange, hpker⟩
    have hcomap : Submodule.comap (Qp t.1).mulVecLin p.1 ≤
        Submodule.map Z.mulVecLin t.2.1 ⊔ t.1 := by
      have h := (le_range_mul_iff (Qp t.1) (range_Qp t.1) p.1
        (Submodule.map Z.mulVecLin t.2.1)).mp (by rwa [range_charMat] at hprange)
      rwa [ker_Qp] at h
    have hker' : ∀ w ∈ t.2.1, Z.mulVec w ∈ Submodule.comap (Qp t.1).mulVecLin p.1 →
        w ∈ Submodule.map (Ip t.2.1).mulVecLin p.2 :=
      (forall_mem_charMat_iff t.1 t.2.1 Z p.1 p.2).mp hpker
    refine ⟨?_, ?_⟩
    · exact hcomap.trans (sup_le (by
        rw [LinearMap.range_eq_map]
        exact Submodule.map_mono le_top) hV2range)
    · intro w hw
      have hZw : Z.mulVec w ∈ Submodule.map Z.mulVecLin t.2.1 ⊔ t.1 := hcomap hw
      rw [Submodule.mem_sup] at hZw
      obtain ⟨a, ha, b, hb, hab⟩ := hZw
      obtain ⟨w₂, hw₂, hw₂a⟩ := Submodule.mem_map.mp ha
      rw [Matrix.mulVecLin_apply] at hw₂a
      obtain ⟨u, hu⟩ : ∃ u, Z.mulVec u = b := by
        have hb' : b ∈ LinearMap.range Z.mulVecLin := hV2range hb
        rw [LinearMap.range_eq_map, Submodule.mem_map] at hb'
        obtain ⟨u, -, hu⟩ := hb'
        rw [Matrix.mulVecLin_apply] at hu
        exact ⟨u, hu⟩
      have hu' : u ∈ t.2.1 := hV2ker u (by rw [hu]; exact hb)
      have hww : w - w₂ - u ∈ t.2.1 := by
        refine hV2ker (w - w₂ - u) ?_
        have h0 : Z *ᵥ (w - w₂ - u) = 0 := by
          rw [Matrix.mulVec_sub, Matrix.mulVec_sub, hw₂a, hu, ← hab]
          abel
        rw [h0]
        exact t.fst.zero_mem
      have hww' : w = w₂ + u + (w - w₂ - u) := by abel
      have hmem : w ∈ t.2.1 := by
        rw [hww']
        exact t.2.1.add_mem (t.2.1.add_mem hw₂ hu') hww
      exact hker' w hmem hw
  · rintro ⟨hrange, hker⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact (le_comap_Qp t.1 p.1).trans hrange
    · intro w hw
      exact map_Ip_le t.2.1 p.2 (hker w (le_comap_Qp t.1 p.1 hw))
    · rw [range_charMat]
      refine (le_range_mul_iff (Qp t.1) (range_Qp t.1) p.1
        (Submodule.map Z.mulVecLin t.2.1)).mpr ?_
      rw [ker_Qp]
      have hsub : Submodule.comap (Qp t.1).mulVecLin p.1 ≤
          Submodule.map Z.mulVecLin t.2.1 := by
        intro v hv
        have hv' : v ∈ LinearMap.range Z.mulVecLin := hrange hv
        rw [LinearMap.range_eq_map, Submodule.mem_map] at hv'
        obtain ⟨w, -, hw⟩ := hv'
        rw [Matrix.mulVecLin_apply] at hw
        refine Submodule.mem_map.mpr ⟨w, ?_, hw⟩
        refine map_Ip_le t.2.1 p.2 (hker w ?_)
        rw [hw]
        exact hv
      exact hsub.trans le_sup_left
    · refine (forall_mem_charMat_iff t.1 t.2.1 Z p.1 p.2).mpr ?_
      intro w _ hZw
      exact hker w hZw

/-! ## The kernel and range of the compressed `X` of a triple

For a triple `t = (V₂,W₂,X₀)` and a pair `p = (p.1,p.2)` on the `Fr`-locus, the *compressed* map
`X(W₃,V/V₃) = charMat p.1 p.2 (XtOf t.1 t.2.1 t.2.2)` has kernel `Ip p.2 ⁻¹ (ker X₀)` and range
`(p.1 + Im X₀)/p.1`.  These are the restriction data of the `X`-derivative
`D_{X(W₃,V/V₃)}` appearing in the switching-roles summands. -/

/-- The range of the `X`-map of a triple, in coordinates. -/
theorem range_XtOf_section (t : Triple m n) :
    LinearMap.range (XtOf t.1 t.2.1 t.2.2).mulVecLin = VrOf t := by
  rw [range_XtOf, range_section t]
  rfl

/-- The kernel of the `X`-map of a triple, in coordinates. -/
theorem ker_XtOf_section (t : Triple m n) :
    LinearMap.ker (XtOf t.1 t.2.1 t.2.2).mulVecLin = WrOf t := by
  rw [ker_XtOf, ker_section t]
  rfl

/-- **The range of the compressed `X`** on the `Fr`-locus is `(p.1 + Im X₀)/p.1`. -/
theorem range_charMat_XtOf (t : Triple m n) (p : QPair m n t)
    (h : p.2 ⊔ WrOf t = ⊤) :
    LinearMap.range ((charMat p.1 p.2 (XtOf t.1 t.2.1 t.2.2))).mulVecLin
      = Submodule.map (Qp p.1).mulVecLin (VrOf t) := by
  rw [range_charMat]
  have h2 : Submodule.map (XtOf t.1 t.2.1 t.2.2).mulVecLin p.2 = VrOf t := by
    have hsup : p.2 ⊔ LinearMap.ker (XtOf t.1 t.2.1 t.2.2).mulVecLin = ⊤ := by
      rw [ker_XtOf_section]; exact h
    calc Submodule.map (XtOf t.1 t.2.1 t.2.2).mulVecLin p.2
        = Submodule.map (XtOf t.1 t.2.1 t.2.2).mulVecLin
            (p.2 ⊔ LinearMap.ker (XtOf t.1 t.2.1 t.2.2).mulVecLin) := by
          rw [Submodule.map_sup, map_ker_mulVecLin, sup_bot_eq]
      _ = Submodule.map (XtOf t.1 t.2.1 t.2.2).mulVecLin ⊤ := by rw [hsup]
      _ = VrOf t := by rw [Submodule.map_top, range_XtOf_section]
  rw [h2]

/-- The value of a compressed matrix on a vector. -/
theorem charMat_mulVec {N M : ℕ} (V₂ : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₂ : Submodule 𝔽₂ (Fin M → 𝔽₂)) (Z : Matrix (Fin N) (Fin M) 𝔽₂)
    (y : Fin (Module.finrank 𝔽₂ W₂) → 𝔽₂) :
    (charMat V₂ W₂ Z).mulVec y = (Qp V₂).mulVec (Z.mulVec ((Ip W₂).mulVec y)) := by
  simp only [charMat, ← Matrix.mulVec_mulVec]

/-- **The kernel of the compressed `X`** on the `Fr`-locus is the preimage under `Ip p.2` of the
kernel of `X₀`. -/
theorem ker_charMat_XtOf (t : Triple m n) (p : QPair m n t)
    (h : p.1 ⊓ VrOf t = ⊥) :
    LinearMap.ker ((charMat p.1 p.2 (XtOf t.1 t.2.1 t.2.2))).mulVecLin
      = Submodule.comap (Ip p.2).mulVecLin (WrOf t) := by
  ext y
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
    charMat_mulVec (Z := XtOf t.1 t.2.1 t.2.2), Submodule.mem_comap,
    Matrix.mulVecLin_apply]
  constructor
  · intro hy
    have h1 : (XtOf t.1 t.2.1 t.2.2).mulVec ((Ip p.2).mulVec y) ∈ p.1 := by
      have hm : (XtOf t.1 t.2.1 t.2.2).mulVec ((Ip p.2).mulVec y)
          ∈ LinearMap.ker (Qp p.1).mulVecLin := by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact hy
      rwa [ker_Qp] at hm
    have h2 : (XtOf t.1 t.2.1 t.2.2).mulVec ((Ip p.2).mulVec y) ∈ VrOf t := by
      rw [← range_XtOf_section]
      exact LinearMap.mem_range.mpr ⟨(Ip p.2).mulVec y, rfl⟩
    have h3 : (XtOf t.1 t.2.1 t.2.2).mulVec ((Ip p.2).mulVec y)
        ∈ (⊥ : Submodule 𝔽₂ (Fin (n - Module.finrank 𝔽₂ t.1) → 𝔽₂)) := by
      rw [← h, Submodule.mem_inf]
      exact ⟨h1, h2⟩
    rw [Submodule.mem_bot] at h3
    rw [← ker_XtOf_section, LinearMap.mem_ker]
    exact h3
  · intro hy
    have h0 : (XtOf t.1 t.2.1 t.2.2).mulVec ((Ip p.2).mulVec y) = 0 := by
      rw [← ker_XtOf_section, LinearMap.mem_ker] at hy
      exact hy
    rw [h0, Matrix.mulVec_zero]

/-- **The one true direction of the session-24 statement**: the hybrid predicate at the
*intersection* pair `(V₃+V₁, W₃∩W₁)` implies the one at the *lift* pair `(V₃,W₃)` (which is what
the identity `hybridPredSub_conj_iff` produces). -/
theorem hybridPredSub_Vc_imp_lift (t : Triple m n) (p : QPair m n t)
    (Z : Matrix (Fin n) (Fin m) 𝔽₂) :
    hybridPredSub (liftV t.1 (p.1 ⊔ VrOf t)) (liftW t.2.1 (p.2 ⊓ WrOf t)) Z →
      hybridPredSub (liftV t.1 p.1) (liftW t.2.1 p.2) Z :=
  hybridPredSub_mono (Submodule.comap_mono le_sup_left) (Submodule.map_mono inf_le_left)

/-! ## The `cor:getting rid of D_X 4-norms` bound in the role space

The `cor`-route of the endgame needs the paper's `cor:getting rid of D_X 4-norms`
(`XNormSum.sum_inv_pow_sq_l2sq_plLE_le`) applied to the `X`-derivatives of the **role space**
`L(V/V₂, W₂)` of a triple, i.e. to `Dop0S t.1 t.2.1 T f`.  The degree bound is provided by
`degLe_Dop0S`; since `d - |(t.1,t.2.1)| ≤ d`, the weight `q^{-4d rank Y}` is even smaller than the
weight produced by the lemma. -/

/-- **`cor:getting rid of D_X 4-norms` for the role space of a triple.** -/
theorem sum_inv_pow_sq_l2sq_role_le (t : Triple m n) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) :
    (∑ Y : Matrix (Fin (n - Module.finrank 𝔽₂ t.1)) (Fin (Module.finrank 𝔽₂ t.2.1)) 𝔽₂,
        ((2 : ℝ) ^ (4 * d * Y.rank))⁻¹ *
          (l2sq (lapMulN (plLE Y) (Dop0S t.1 t.2.1 T f))) ^ 2) ≤
      2 * (l2sq (Dop0S t.1 t.2.1 T f)) ^ 2 := by
  have hle : (∑ Y : Matrix (Fin (n - Module.finrank 𝔽₂ t.1))
        (Fin (Module.finrank 𝔽₂ t.2.1)) 𝔽₂,
        ((2 : ℝ) ^ (4 * d * Y.rank))⁻¹ *
          (l2sq (lapMulN (plLE Y) (Dop0S t.1 t.2.1 T f))) ^ 2) ≤
      (∑ Y : Matrix (Fin (n - Module.finrank 𝔽₂ t.1))
        (Fin (Module.finrank 𝔽₂ t.2.1)) 𝔽₂,
        ((2 : ℝ) ^ (4 * (d - (Module.finrank 𝔽₂ t.1 +
          (m - Module.finrank 𝔽₂ t.2.1))) * Y.rank))⁻¹ *
          (l2sq (lapMulN (plLE Y) (Dop0S t.1 t.2.1 T f))) ^ 2) := by
    refine Finset.sum_le_sum fun Y _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
    refine pow_le_pow_right₀ (by norm_num) ?_
    have h1 : d - (Module.finrank 𝔽₂ t.1 + (m - Module.finrank 𝔽₂ t.2.1)) ≤ d :=
      Nat.sub_le _ _
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 h1)
  exact hle.trans (sum_inv_pow_sq_l2sq_plLE_le (degLe_Dop0S hf t.1 t.2.1 T))

/-! ## The multiplier identity for the switching-roles summands -/

/-- `PComb` together with the big-space hybrid predicate is the lifted hybrid predicate together
with the transported `plLE` conjunct. -/
theorem PComb_and_hybridPredSub (t : Triple m n) (p : QPair m n t)
    (Z : Matrix (Fin n) (Fin m) 𝔽₂) :
    (hybridPredSub t.1 t.2.1 Z ∧ PComb t p.1 p.2 Z) ↔
      (hybridPredSub (liftV t.1 p.1) (liftW t.2.1 p.2) Z ∧
        PTranspA t p.1 p.2 (charMat t.1 t.2.1 Z)) := by
  rw [PComb, PInA]
  constructor
  · rintro ⟨h1, h3, h2⟩
    exact ⟨(hybridPredSub_conj_iff t p Z).mp ⟨h1, h2⟩, h3⟩
  · rintro ⟨h1, h3⟩
    obtain ⟨h1', h2'⟩ := (hybridPredSub_conj_iff t p Z).mpr h1
    exact ⟨h1', h3, h2'⟩

/-- **The multiplier of a switching-roles summand is `L_{V₃,W₃}` composed with the transported
`X`-projection.** -/
theorem lapMulN_PComb_eq (t : Triple m n) (p : QPair m n t)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    lapMulN (fun Z => hybridPredSub t.1 t.2.1 Z ∧ PComb t p.1 p.2 Z) f
      = lapMulN (fun Z => PTranspA t p.1 p.2 (charMat t.1 t.2.1 Z))
          (lapMulN (fun Z => hybridPredSub (liftV t.1 p.1) (liftW t.2.1 p.2) Z) f) := by
  rw [lapMulN_comp]
  exact lapMulN_congr (fun Z => (PComb_and_hybridPredSub t p Z).trans and_comm) f

/-- The multiplier of the code's switching summand, applied to `Lsub t.1 t.2.1 f`, is the
transported `X`-projection applied to the big-space hybrid Laplacian `L_{V₃,W₃}[f]`. -/
theorem lapMulN_PComb_apply_Lsub (t : Triple m n) (p : QPair m n t)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    lapMulN (PComb t p.1 p.2) (Lsub t.1 t.2.1 f)
      = lapMulN (fun Z => PTranspA t p.1 p.2 (charMat t.1 t.2.1 Z))
          (Lsub (liftV t.1 p.1) (liftW t.2.1 p.2) f) := by
  rw [Lsub, Lsub, lapMulN_comp]
  exact (lapMulN_congr (fun Z => and_comm) f).trans (lapMulN_PComb_eq t p f)

end

end Submission.Grassmann
