import Submission.Grassmann.SwCollapse
import Submission.Commons.LinearAlgebra.LinearMap.card_hom_compress_le_pow
import Submission.Commons.LinearAlgebra.LinearMap.finrank_range_mapQ_comp_inclusion
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_le_finrank_eq_gb
import Submission.Commons.Combinatorics.QBinomial.gb_mul_gb_mul_pow_le
import Submission.Commons.LinearAlgebra.Submodule.card_superspace_codim_le_pow

/-!
# The fibre count of the §8 reindexing

The remaining step of §8 is a counting statement: the fibres of
`Φ₃ : (t,p) ↦ (liftV t.1 p.1, liftW t.2.1 p.2, XsOf t p)` are small.  This file starts the
project-side translation of the fibre conditions into the linear-algebraic conditions of
`Commons.LinearAlgebra.LinearMap.card_hom_compress_le_pow`:

* `p.1 ⊓ VrOf t = ⊥` is `(V/V₂) ⊓ range X = ⊥` (`Vco_inf_VrOf_eq_bot_iff`),
* `p.2 ⊔ WrOf t = ⊤` is `W + ker X = W₂` (`Wco_sup_WrOf_eq_top_iff`),

where `X = t.2.2 : ↥W₂ →ₗ 𝔽₂ⁿ ⧸ V₂`, together with the fact that `p` is determined by
`(t, V, W)` (`liftV`/`liftW` are injective, `liftV_injective`/`liftW_injective`).
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## `p` is determined by `(t,V,W)` -/

/-- `liftV` is injective (it has the left inverse `Vco V₁r`). -/
lemma liftV_injective {N : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂)) :
    Function.Injective (liftV V₁r) := fun a b h => by
  rw [← Vco_liftV V₁r a, ← Vco_liftV V₁r b, h]

/-- `liftW` is injective (it has the left inverse `Wco W₁r`). -/
lemma liftW_injective {M : ℕ} (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂)) :
    Function.Injective (liftW W₁r) := fun a b h => by
  rw [← Wco_liftW W₁r a, ← Wco_liftW W₁r b, h]

/-- If `liftV V₁r V₄ = V` then `V₄` is the coordinates of `V`. -/
lemma eq_Vco_of_liftV_eq {N : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    {V₄ : Submodule 𝔽₂ (Fin (N - Module.finrank 𝔽₂ V₁r) → 𝔽₂)}
    {V : Submodule 𝔽₂ (Fin N → 𝔽₂)} (h : liftV V₁r V₄ = V) : V₄ = Vco V₁r V := by
  rw [← Vco_liftV V₁r V₄, h]

/-- If `liftW W₁r W₄ = W` then `W₄` is the coordinates of `W`. -/
lemma eq_Wco_of_liftW_eq {M : ℕ} (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂))
    {W₄ : Submodule 𝔽₂ (Fin (Module.finrank 𝔽₂ W₁r) → 𝔽₂)}
    {W : Submodule 𝔽₂ (Fin M → 𝔽₂)} (h : liftW W₁r W₄ = W) : W₄ = Wco W₁r W := by
  rw [← Wco_liftW W₁r W₄, h]

/-- The lift of the coordinates of `V` is `V` (when `V₁r ≤ V`). -/
lemma liftV_Vco_of_le {N : ℕ} (V₁r : Submodule 𝔽₂ (Fin N → 𝔽₂))
    {V : Submodule 𝔽₂ (Fin N → 𝔽₂)} (h : V₁r ≤ V) : liftV V₁r (Vco V₁r V) = V := by
  rw [liftV_Vco, sup_eq_left.mpr h]

/-- The lift of the coordinates of `W` is `W` (when `W ≤ W₁r`). -/
lemma liftW_Wco_of_le {M : ℕ} (W₁r : Submodule 𝔽₂ (Fin M → 𝔽₂))
    {W : Submodule 𝔽₂ (Fin M → 𝔽₂)} (h : W ≤ W₁r) : liftW W₁r (Wco W₁r W) = W := by
  rw [liftW_Wco, inf_eq_left.mpr h]


/-! ## The coordinate bridge: `XsOf` is the compression of the triple's map -/

/-- The `codRestrict` of `Ip W` is `ecW W`. -/
lemma codRestrict_Ip_eq (W : Submodule 𝔽₂ (Fin m → 𝔽₂)) :
    LinearMap.codRestrict W (Ip W).mulVecLin (fun x => Ip_mem W x) = (ecW W).toLinearMap := by
  have h : (Ip W).mulVecLin = W.subtype.comp (ecW W).toLinearMap := Ip_mulVecLin W
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  show (Ip W).mulVecLin x = W.subtype.toFun ((ecW W).toLinearMap x)
  rw [h]
  rfl

/-- The coordinate matrix `XtOf` in terms of `toMatrix'` and `ecW`. -/
lemma XtOf_eq_toMatrix' (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) :
    XtOf V₂ W₂ X = LinearMap.toMatrix'
      ((Qe V₂).toLinearMap.comp (X.comp (ecW W₂).toLinearMap)) := by
  rw [XtOf, codRestrict_Ip_eq]

/-- The canonical linear map whose coordinate matrix is `Z`. -/
noncomputable def ZabsOf (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂) :
    ↥W →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₀) :=
  (Qe V₀).symm.toLinearMap.comp ((Matrix.toLin' Z).comp (ecW W).symm.toLinearMap)

lemma XtOf_ZabsOf (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂) :
    XtOf V₀ W (ZabsOf V₀ W Z) = Z := by
  rw [XtOf_eq_toMatrix', ZabsOf]
  simp only [LinearMap.comp_assoc]
  rw [LinearEquiv.symm_comp, LinearMap.comp_id, ← LinearMap.comp_assoc,
    LinearEquiv.comp_symm, LinearMap.id_comp]
  exact LinearMap.toMatrix'_toLin' Z

lemma ZabsOf_XtOf (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (X : ↥W →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₀)) :
    ZabsOf V₀ W (XtOf V₀ W X) = X := by
  rw [XtOf_eq_toMatrix', ZabsOf]
  rw [Matrix.toLin'_toMatrix']
  simp only [LinearMap.comp_assoc]
  rw [LinearEquiv.comp_symm, LinearMap.comp_id, ← LinearMap.comp_assoc,
    LinearEquiv.symm_comp, LinearMap.id_comp]

lemma XtOf_injective (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) :
    Function.Injective (XtOf V₂ W₂) := by
  intro X X' h
  rw [← ZabsOf_XtOf V₂ W₂ X, ← ZabsOf_XtOf V₂ W₂ X', h]

/-- The compression of a linear map `↥W₂ → V/V₂` to the pair `(W ⊆ W₂, V₂ ≤ V₀)`. -/
noncomputable def compressZ (V₂ V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (hVV : V₂ ≤ V₀) (hWW : W ≤ W₂)
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) : ↥W →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₀) :=
  (Submodule.mapQ V₂ V₀ LinearMap.id (by simpa using hVV)).comp
    (X.comp (Submodule.inclusion hWW))

/-- **The compression of a compression**: `Y|_{W}^{V/V₀}` is the compression of
`Y|_{W₂}^{V/V₂}`. -/
lemma YlinOf_eq_compression (V₂ V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (hVV : V₂ ≤ V₀) (hWW : W ≤ W₂)
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    YlinOf V₀ W Y = compressZ V₂ V₀ W W₂ hVV hWW (YlinOf V₂ W₂ Y) := by
  apply LinearMap.ext
  intro x
  simp only [YlinOf, compressZ, LinearMap.comp_apply]
  have h1 : (Submodule.mapQ V₂ V₀ LinearMap.id (by simpa using hVV))
      (V₂.mkQ (Y.mulVecLin (W₂.subtype (Submodule.inclusion hWW x))))
      = V₀.mkQ (Y.mulVecLin (W₂.subtype (Submodule.inclusion hWW x))) := by
    have h := Submodule.mapQ_mkQ V₂ V₀ (LinearMap.id) (h := by simpa using hVV)
    have hx := congrFun (congrArg DFunLike.coe h)
      (Y.mulVecLin (W₂.subtype (Submodule.inclusion hWW x)))
    simpa using hx
  rw [h1]
  have h2 : W₂.subtype (Submodule.inclusion hWW x) = W.subtype x :=
    congrFun (congrArg DFunLike.coe (Submodule.subtype_comp_inclusion W W₂ hWW)) x
  rw [h2]

/-- **The big-space matrix of a triple restricts to its map**: the compression of `bigMat t` is
`t.2.2`. -/
theorem YlinOf_bigMat (t : Triple m n) : YlinOf t.1 t.2.1 (bigMat t) = t.2.2 := by
  have h := charMat_bigMat t
  rw [charMat_eq_XtOf] at h
  exact XtOf_injective t.1 t.2.1 h

/-- **The compression bridge.**  The role-space matrix `XsOf t p` is the coordinate matrix of the
compression of the triple's map `t.2.2` to the pair `(W₃ ⊆ W₂, V₂ ≤ V₃)`, where
`V₃ = liftV t.1 p.1`, `W₃ = liftW t.2.1 p.2`. -/
theorem XsOf_eq_iff_compressZ (t : Triple m n) (p : QPair m n t)
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ (liftV t.1 p.1)))
      (Fin (Module.finrank 𝔽₂ (liftW t.2.1 p.2))) 𝔽₂) :
    (XsOf t p = Z) ↔
      compressZ t.1 (liftV t.1 p.1) (liftW t.2.1 p.2) t.2.1 (le_comap_Qp t.1 p.1)
        (map_Ip_le t.2.1 p.2) t.2.2
        = ZabsOf (liftV t.1 p.1) (liftW t.2.1 p.2) Z := by
  have hXs : XsOf t p = XtOf (liftV t.1 p.1) (liftW t.2.1 p.2)
      (compressZ t.1 (liftV t.1 p.1) (liftW t.2.1 p.2) t.2.1 (le_comap_Qp t.1 p.1)
        (map_Ip_le t.2.1 p.2) t.2.2) := by
    rw [XsOf_eq, charMat_eq_XtOf, YlinOf_eq_compression, YlinOf_bigMat]
  rw [hXs]
  constructor
  · intro h
    rw [← ZabsOf_XtOf (liftV t.1 p.1) (liftW t.2.1 p.2)
      (compressZ t.1 (liftV t.1 p.1) (liftW t.2.1 p.2) t.2.1 (le_comap_Qp t.1 p.1)
        (map_Ip_le t.2.1 p.2) t.2.2), h]
  · intro h
    rw [h, XtOf_ZabsOf]

/-! ## The Fr-conditions in terms of the linear map of the triple -/

/-- **The `V`-side Fr-condition** `p.1 ⊓ VrOf t = ⊥` is the linear-algebraic condition
`(V/V₂) ⊓ range X = ⊥` on the map `X = t.2.2` of the triple. -/
lemma Vco_inf_VrOf_eq_bot_iff (t : Triple m n) (V : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    (Vco t.1 V ⊓ VrOf t = ⊥) ↔
      Submodule.map (Submodule.mkQ t.1) V ⊓ LinearMap.range t.2.2 = ⊥ := by
  have hVr : VrOf t = Submodule.map (Qe t.1).toLinearMap (LinearMap.range t.2.2) := by
    rw [VrOf, Vco, range_section t]
  constructor
  · intro h
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    have hmem : (Qe t.1) x ∈ Vco t.1 V ⊓ VrOf t := by
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Vco]
        exact Submodule.mem_map.mpr ⟨x, hx1, rfl⟩
      · rw [hVr]
        exact Submodule.mem_map.mpr ⟨x, hx2, rfl⟩
    rw [h] at hmem
    exact (Qe t.1).injective (by simpa using hmem)
  · intro h
    have h1 : Vco t.1 V ⊓ VrOf t
        = Submodule.map (Qe t.1).toLinearMap
            (Submodule.map (Submodule.mkQ t.1) V ⊓ LinearMap.range t.2.2) := by
      rw [Vco, hVr, Submodule.map_inf (Qe t.1).toLinearMap (Qe t.1).injective]
    rw [h1, h, Submodule.map_bot]

/-- **The `W`-side Fr-condition** `p.2 ⊔ WrOf t = ⊤`, in the quotient coordinates. -/
lemma Wco_sup_WrOf_eq_top_iff (t : Triple m n) (W : Submodule 𝔽₂ (Fin m → 𝔽₂)) :
    (Wco t.2.1 W ⊔ WrOf t = ⊤) ↔
      Submodule.comap t.2.1.subtype W ⊔ LinearMap.ker t.2.2 = ⊤ := by
  rw [WrOf]
  unfold Wco
  rw [← Submodule.map_sup, Submodule.map_eq_top_iff, ← ker_section t]

/-- **The `W`-side Fr-condition** `p.2 ⊔ WrOf t = ⊤`, in the ambient space (for `W ≤ W₂`). -/
lemma Wco_sup_WrOf_eq_top_iff' (t : Triple m n) {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    (hW : W ≤ t.2.1) :
    (Wco t.2.1 W ⊔ WrOf t = ⊤) ↔
      W ⊔ Submodule.map t.2.1.subtype (LinearMap.ker t.2.2) = t.2.1 := by
  have hWr : W ≤ t.2.1.subtype.range := by rwa [Submodule.range_subtype]
  have hkerle : t.2.1.subtype.ker ≤
      (Submodule.comap t.2.1.subtype W ⊔ LinearMap.ker t.2.2) := by
    rw [Submodule.ker_subtype]; exact bot_le
  rw [Wco_sup_WrOf_eq_top_iff]
  constructor
  · intro h
    have h2 : Submodule.map t.2.1.subtype
        (Submodule.comap t.2.1.subtype W ⊔ LinearMap.ker t.2.2) = t.2.1 := by
      rw [h, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_sup, Submodule.map_comap_eq_self hWr] at h2
    exact h2
  · intro h
    have h2 : Submodule.comap t.2.1.subtype
        (Submodule.map t.2.1.subtype
          (Submodule.comap t.2.1.subtype W ⊔ LinearMap.ker t.2.2)) = ⊤ := by
      rw [Submodule.map_sup, Submodule.map_comap_eq_self hWr, h,
        Submodule.comap_subtype_self]
    rwa [Submodule.comap_map_eq_self hkerle] at h2


/-- `finrank (pV t p) = finrank p.1` on the `Fr`-locus. -/
lemma finrank_pV (t : Triple m n) (p : QPair m n t) (hp : p.1 ⊓ VrOf t = ⊥) :
    Module.finrank 𝔽₂ (pV t p) = Module.finrank 𝔽₂ p.1 := by
  have h1 : Module.finrank 𝔽₂ (liftV (VrOf t) (pV t p)) =
      Module.finrank 𝔽₂ (pV t p) + Module.finrank 𝔽₂ (VrOf t) := finrank_liftV _ _
  rw [liftV_pV t p] at h1
  have h2 : Module.finrank 𝔽₂ ↥(p.1 ⊔ VrOf t) + Module.finrank 𝔽₂ ↥(p.1 ⊓ VrOf t) =
      Module.finrank 𝔽₂ p.1 + Module.finrank 𝔽₂ (VrOf t) :=
    Submodule.finrank_sup_add_finrank_inf_eq (s := p.1) (t := VrOf t)
  rw [hp, finrank_bot, add_zero] at h2
  omega

/-- `finrank (pW t p) + dim W₂ = finrank p.2 + finrank (WrOf t)` on the `Fr`-locus. -/
lemma finrank_pW (t : Triple m n) (p : QPair m n t) (hp : p.2 ⊔ WrOf t = ⊤) :
    Module.finrank 𝔽₂ (pW t p) + Module.finrank 𝔽₂ t.2.1 =
      Module.finrank 𝔽₂ p.2 + Module.finrank 𝔽₂ (WrOf t) := by
  have h1 : Module.finrank 𝔽₂ (liftW (WrOf t) (pW t p)) = Module.finrank 𝔽₂ (pW t p) :=
    finrank_liftW _ _
  rw [liftW_pW t p] at h1
  have h2 : Module.finrank 𝔽₂ ↥(p.2 ⊔ WrOf t) + Module.finrank 𝔽₂ ↥(p.2 ⊓ WrOf t) =
      Module.finrank 𝔽₂ p.2 + Module.finrank 𝔽₂ (WrOf t) :=
    Submodule.finrank_sup_add_finrank_inf_eq (s := p.2) (t := WrOf t)
  have h4 : Module.finrank 𝔽₂ ↥(p.2 ⊔ WrOf t) = Module.finrank 𝔽₂ t.2.1 := by
    rw [hp, finrank_top, Module.finrank_fin_fun]
  rw [h4, h1] at h2
  omega

/-- **The guard identity.**  On the `Fr`-locus the switching guard is
`(dim V₃ - dim V₂) + (dim W₂ - dim W₃)` where `V₃ = liftV t.1 p.1`, `W₃ = liftW t.2.1 p.2`. -/
theorem SwGuard_iff (t : Triple m n) (p : QPair m n t) (d : ℕ)
    (hV : p.1 ⊓ VrOf t = ⊥) (hW : p.2 ⊔ WrOf t = ⊤) :
    SwGuard t d (pV t p) (pW t p) ↔
      (Module.finrank 𝔽₂ (liftV t.1 p.1) - Module.finrank 𝔽₂ t.1) +
        (Module.finrank 𝔽₂ t.2.1 - Module.finrank 𝔽₂ (liftW t.2.1 p.2)) ≤ d := by
  have key1 : Module.finrank 𝔽₂ (pV t p) = Module.finrank 𝔽₂ p.1 := finrank_pV t p hV
  have key2 : Module.finrank 𝔽₂ (liftV t.1 p.1) - Module.finrank 𝔽₂ t.1
      = Module.finrank 𝔽₂ p.1 := by
    rw [finrank_liftV]; omega
  have key3 : Module.finrank 𝔽₂ (WrOf t) - Module.finrank 𝔽₂ (pW t p) =
      Module.finrank 𝔽₂ t.2.1 - Module.finrank 𝔽₂ (liftW t.2.1 p.2) := by
    have h1 := finrank_pW t p hW
    have h2 : Module.finrank 𝔽₂ (liftW t.2.1 p.2) = Module.finrank 𝔽₂ p.2 :=
      finrank_liftW t.2.1 p.2
    have h3 : Module.finrank 𝔽₂ p.2 ≤ Module.finrank 𝔽₂ t.2.1 := by
      rw [← h2]; exact Submodule.finrank_mono (map_Ip_le t.2.1 p.2)
    omega
  simp only [SwGuard]
  rw [key1, key3, key2]

/-! ## The reindexing map of the switching sum -/

/-- The reindexing map `Φ₃ : (t,p) ↦ (V₃,W₃,XsOf t p)` of §8, with
`V₃ = liftV t.1 p.1` and `W₃ = liftW t.2.1 p.2`. -/
noncomputable def Phi3 {m n : ℕ} (x : Σ t : Triple m n, QPair m n t) :
    Σ (V : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂)),
      Matrix (Fin (n - Module.finrank 𝔽₂ V)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂ :=
  ⟨liftV x.1.1 x.2.1, liftW x.1.2.1 x.2.2, XsOf x.1 x.2⟩

@[simp] lemma Phi3_fst {m n : ℕ} (x : Σ t : Triple m n, QPair m n t) :
    (Phi3 x).1 = liftV x.1.1 x.2.1 := rfl
@[simp] lemma Phi3_snd_fst {m n : ℕ} (x : Σ t : Triple m n, QPair m n t) :
    (Phi3 x).2.1 = liftW x.1.2.1 x.2.2 := rfl
@[simp] lemma Phi3_snd_snd {m n : ℕ} (x : Σ t : Triple m n, QPair m n t) :
    (Phi3 x).2.2 = XsOf x.1 x.2 := rfl

/-- The `Fr`- and guard-conditions of the switching summand of `x = (t,p)`. -/
def ReindexGood {m n : ℕ} (d : ℕ) (x : Σ t : Triple m n, QPair m n t) : Prop :=
  (x.2.1 ⊓ VrOf x.1 = ⊥ ∧ x.2.2 ⊔ WrOf x.1 = ⊤) ∧
    SwGuard x.1 d (pV x.1 x.2) (pW x.1 x.2)

/-- The `X`-conditions of the compression fibre, for a fixed pair `(V₂,W₂)`. -/
structure XGood {m n : ℕ} (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (hVV : V₂ ≤ V₀) (hWW : W ≤ W₂)
    (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) : Prop where
  hkerV : Submodule.map (Submodule.mkQ V₂) V₀ ⊓ LinearMap.range X = ⊥
  hkerW : W ⊔ Submodule.map W₂.subtype (LinearMap.ker X) = W₂
  hcomp : compressZ V₂ V₀ W W₂ hVV hWW X = ZabsOf V₀ W Z

/-- The fibre count of §8: the type of `(V₂,W₂,X)` realising a summand in the fibre of `Phi3`. -/
abbrev SigType {m n : ℕ} (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d i j : ℕ) : Type :=
  Σ (V₂ : {V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂) // V₂ ≤ V₀ ∧ Module.finrank 𝔽₂ V₂ = i})
    (W₂ : {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂) //
      W ≤ W₂ ∧ m - Module.finrank 𝔽₂ W₂ = j ∧
      (Module.finrank 𝔽₂ V₀ - i) + (Module.finrank 𝔽₂ W₂ - Module.finrank 𝔽₂ W) ≤ d}),
  {X : ↥(W₂.1) →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ (V₂.1)) //
    XGood V₀ W Z V₂.1 W₂.1 V₂.2.1 W₂.2.1 X}

/-- The conditions on a triple for it to appear in the fibre of `Phi3` over `⟨V₀,W,Z⟩` at
stratum `(i,j)` (`i = dim V₂`, `j = codim W₂`). -/
structure TCond {m n : ℕ} (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d i j : ℕ) (t : Triple m n) : Prop where
  hleV : t.1 ≤ V₀
  hleW : W ≤ t.2.1
  hguard : Module.finrank 𝔽₂ V₀ - Module.finrank 𝔽₂ t.1 +
      (Module.finrank 𝔽₂ t.2.1 - Module.finrank 𝔽₂ W) ≤ d
  hkerV : Submodule.map (Submodule.mkQ t.1) V₀ ⊓ LinearMap.range t.2.2 = ⊥
  hkerW : W ⊔ Submodule.map t.2.1.subtype (LinearMap.ker t.2.2) = t.2.1
  hcomp : compressZ t.1 V₀ W t.2.1 hleV hleW t.2.2 = ZabsOf V₀ W Z
  hdimV : Module.finrank 𝔽₂ t.1 = i
  hdimW : m - Module.finrank 𝔽₂ t.2.1 = j

open Classical in
/-- The fibre over `⟨V₀,W,Z⟩` at stratum `(i,j)` is equivalent to the type of pairs `(V₂,W₂)`
of the stratum together with an `X` satisfying the compression conditions. -/
noncomputable def tCondEquiv {m n : ℕ} (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d i j : ℕ) :
    {t : Triple m n // TCond V₀ W Z d i j t} ≃ SigType V₀ W Z d i j where
  toFun t :=
    ⟨⟨t.1.1, t.2.hleV, t.2.hdimV⟩,
     ⟨t.1.2.1, t.2.hleW, t.2.hdimW, by
        simpa only [t.2.hdimV] using t.2.hguard⟩,
     ⟨t.1.2.2, ⟨t.2.hkerV, t.2.hkerW, t.2.hcomp⟩⟩⟩
  invFun s :=
    let t : Triple m n := ⟨s.1.1, s.2.1.1, s.2.2.1⟩
    ⟨t, ⟨s.1.2.1, s.2.1.2.1, (by
        show Module.finrank 𝔽₂ V₀ - Module.finrank 𝔽₂ (s.1.1) +
          (Module.finrank 𝔽₂ (s.2.1.1) - Module.finrank 𝔽₂ W) ≤ d
        rw [s.1.2.2]
        exact s.2.1.2.2.2),
      s.2.2.2.hkerV, s.2.2.2.hkerW, s.2.2.2.hcomp, s.1.2.2, s.2.1.2.2.1⟩⟩
  left_inv t := by
    refine Subtype.ext ?_
    rfl
  right_inv s := by
    rfl

/-- The rank of `ZabsOf` is the rank of `Z`. -/
lemma finrank_range_ZabsOf (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂) :
    Module.finrank 𝔽₂ (LinearMap.range (ZabsOf V₀ W Z)) = Z.rank := by
  rw [← rank_XtOf V₀ W (ZabsOf V₀ W Z), XtOf_ZabsOf]

/-- The `XGood`-condition is the hypothesis of `card_hom_compress_le_pow`. -/
lemma card_XGood_le (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (hVV : V₂ ≤ V₀) (hWW : W ≤ W₂) :
    Nat.card {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) // XGood V₀ W Z V₂ W₂ hVV hWW X}
      ≤ 2 ^ ((Module.finrank 𝔽₂ V₀ - Module.finrank 𝔽₂ V₂ +
          (Module.finrank 𝔽₂ W₂ - Module.finrank 𝔽₂ W)) * Z.rank) := by
  have h1 : Nat.card {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) // XGood V₀ W Z V₂ W₂ hVV hWW X}
      ≤ Nat.card {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) //
        (Submodule.map (Submodule.mkQ V₂) V₀) ⊓ LinearMap.range X = ⊥ ∧
        W ⊔ Submodule.map W₂.subtype (LinearMap.ker X) = W₂ ∧
        (∀ w : ↥W, (Submodule.mapQ V₂ V₀ LinearMap.id (by simpa using hVV))
          (X (Submodule.inclusion hWW w)) = ZabsOf V₀ W Z w)} := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_mono _ _ (fun x hx =>
      ⟨hx.hkerV, hx.hkerW, fun w => by
        simpa only [compressZ, LinearMap.comp_apply]
          using congrArg (fun g : ↥W →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₀) => g w) hx.hcomp⟩)
  have h2 := Commons.LinearAlgebra.LinearMap.card_hom_compress_le_pow V₂ V₀ W W₂ hVV hWW
    (ZabsOf V₀ W Z)
  rw [finrank_range_ZabsOf] at h2
  refine (h1.trans h2).trans (le_of_eq ?_)
  rw [show Nat.card 𝔽₂ = 2 by rw [Nat.card_eq_fintype_card, ZMod.card]]

/-! ## The fibre count of the §8 reindexing -/

/-- The `V₂`-part of the fibre type. -/
abbrev FibA (m n : ℕ) (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (i : ℕ) : Type :=
  {V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂) // V₂ ≤ V₀ ∧ Module.finrank 𝔽₂ V₂ = i}

/-- The `W₂`-part of the fibre type. -/
abbrev FibB (m n : ℕ) (W : Submodule 𝔽₂ (Fin m → 𝔽₂)) (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (d i j : ℕ) : Type :=
  {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂) //
    W ≤ W₂ ∧ m - Module.finrank 𝔽₂ W₂ = j ∧
    (Module.finrank 𝔽₂ V₀ - i) + (Module.finrank 𝔽₂ W₂ - Module.finrank 𝔽₂ W) ≤ d}

/-- **The fibre count.**  For a fixed triple `⟨V₀,W,Z⟩` the number of triples `t` that are
realised by a summand of the switching sum at stratum `(i,j)` is at most `2 ^ (2 (i+j+k) d)`,
where `k = rank Z`. -/
theorem card_TCond_le (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d i j : ℕ) (hi : i + j + Z.rank ≤ d) :
    Nat.card {t : Triple m n // TCond V₀ W Z d i j t} ≤ 2 ^ (2 * (i + j + Z.rank) * d) := by
  rw [Nat.card_congr (tCondEquiv V₀ W Z d i j)]
  have hstep : Nat.card (SigType V₀ W Z d i j) =
      ∑ V₂ : FibA m n V₀ i, ∑ W₂ : FibB m n W V₀ d i j,
        Nat.card {X : ↥(W₂.1) →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ (V₂.1)) //
          XGood V₀ W Z V₂.1 W₂.1 V₂.2.1 W₂.2.1 X} := by
    rw [Nat.card_sigma]
    exact Finset.sum_congr rfl (fun V₂ _ => Nat.card_sigma)
  rw [hstep]
  have hbound : ∀ (V₂ : FibA m n V₀ i) (W₂ : FibB m n W V₀ d i j),
      Nat.card {X : ↥(W₂.1) →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ (V₂.1)) //
        XGood V₀ W Z V₂.1 W₂.1 V₂.2.1 W₂.2.1 X} ≤ 2 ^ (Z.rank * d) := by
    intro V₂ W₂
    refine (card_XGood_le V₀ W Z V₂.1 W₂.1 V₂.2.1 W₂.2.1).trans ?_
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have hguard : Module.finrank 𝔽₂ V₀ - Module.finrank 𝔽₂ V₂.1 +
        (Module.finrank 𝔽₂ W₂.1 - Module.finrank 𝔽₂ W) ≤ d := by
      have h := W₂.2.2.2
      have hv := V₂.2.2
      omega
    calc (Module.finrank 𝔽₂ V₀ - Module.finrank 𝔽₂ V₂.1 +
          (Module.finrank 𝔽₂ W₂.1 - Module.finrank 𝔽₂ W)) * Z.rank
        = Z.rank * (Module.finrank 𝔽₂ V₀ - Module.finrank 𝔽₂ V₂.1 +
          (Module.finrank 𝔽₂ W₂.1 - Module.finrank 𝔽₂ W)) := Nat.mul_comm _ _
      _ ≤ Z.rank * d := Nat.mul_le_mul_left _ hguard
  calc (∑ V₂ : FibA m n V₀ i, ∑ W₂ : FibB m n W V₀ d i j,
        Nat.card {X : ↥(W₂.1) →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ (V₂.1)) //
          XGood V₀ W Z V₂.1 W₂.1 V₂.2.1 W₂.2.1 X})
      ≤ ∑ V₂ : FibA m n V₀ i, ∑ W₂ : FibB m n W V₀ d i j, 2 ^ (Z.rank * d) :=
        Finset.sum_le_sum (fun V₂ _ => Finset.sum_le_sum (fun W₂ _ => hbound V₂ W₂))
    _ = Nat.card (FibA m n V₀ i) * (Nat.card (FibB m n W V₀ d i j) * 2 ^ (Z.rank * d)) := by
        rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
          Finset.card_univ, Finset.card_univ, ← Nat.card_eq_fintype_card,
          ← Nat.card_eq_fintype_card]
    _ ≤ 2 ^ (2 * (i + j + Z.rank) * d) := by
        by_cases hne : Nonempty (FibB m n W V₀ d i j)
        · obtain ⟨W₂₀⟩ := hne
          have hgrd : Module.finrank 𝔽₂ V₀ - i ≤ d := by
            have h := W₂₀.2.2.2
            omega
          have hWd : m - Module.finrank 𝔽₂ W - j ≤ d := by
            have h := W₂₀.2.2.2
            have h2 := W₂₀.2.2.1
            have h3 : Module.finrank 𝔽₂ W₂₀.1 ≤ m := by
              have := Submodule.finrank_le W₂₀.1
              rwa [Module.finrank_fin_fun] at this
            omega
          have hA : Nat.card (FibA m n V₀ i) ≤ 2 ^ (i * (i + d)) := by
            rw [Commons.LinearAlgebra.Submodule.card_submodule_le_finrank_eq V₀ i]
            refine (Commons.LinearAlgebra.Submodule.card_submodule_finrank_le_pow
              (K := 𝔽₂) (V := ↥V₀) i).trans ?_
            rw [show Nat.card 𝔽₂ = 2 from by rw [Nat.card_eq_fintype_card, ZMod.card]]
            refine Nat.pow_le_pow_right (by norm_num) ?_
            calc i * (Module.finrank 𝔽₂ ↥V₀ - i) + i
                ≤ i * d + i := Nat.add_le_add_right (Nat.mul_le_mul_left i hgrd) i
              _ ≤ i * d + i * i := Nat.add_le_add_left (Nat.le_mul_self i) (i * d)
              _ = i * (i + d) := by ring
          have hB' : Nat.card (FibB m n W V₀ d i j) ≤ 2 ^ (j * (j + d)) := by
            have hmono : Nat.card (FibB m n W V₀ d i j) ≤
                Nat.card {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂) //
                  W ≤ W₂ ∧ Module.finrank 𝔽₂ W₂ = m - j} := by
              rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
              refine Fintype.card_subtype_mono
                (fun W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂) =>
                  W ≤ W₂ ∧ m - Module.finrank 𝔽₂ W₂ = j ∧
                  (Module.finrank 𝔽₂ V₀ - i) + (Module.finrank 𝔽₂ W₂ - Module.finrank 𝔽₂ W) ≤ d)
                (fun W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂) => W ≤ W₂ ∧ Module.finrank 𝔽₂ W₂ = m - j)
                (fun x hx => ⟨hx.1, by
                  have h3 : Module.finrank 𝔽₂ x ≤ m := by
                    have := Submodule.finrank_le x
                    rwa [Module.finrank_fin_fun] at this
                  omega⟩)
            refine hmono.trans ?_
            have hjm : j ≤ m := by
              have h := W₂₀.2.2.1
              have h3 : Module.finrank 𝔽₂ W₂₀.1 ≤ m := by
                have := Submodule.finrank_le W₂₀.1
                rwa [Module.finrank_fin_fun] at this
              omega
            refine (le_of_eq (Commons.LinearAlgebra.Submodule.card_superspace_codim_eq_gb_of_le
              m W j hjm)).trans ?_
            refine (Commons.Combinatorics.QBinomial.gb_le_two_pow_mul (m - Module.finrank 𝔽₂ W) j ?_).trans ?_
            · have h := W₂₀.2.2.1
              have h3 : Module.finrank 𝔽₂ W ≤ Module.finrank 𝔽₂ W₂₀.1 := Submodule.finrank_mono W₂₀.2.1
              omega
            · refine Nat.pow_le_pow_right (by norm_num) ?_
              have hWd2 : m - Module.finrank 𝔽₂ W ≤ j + d := by omega
              calc (m - Module.finrank 𝔽₂ W) * j ≤ (j + d) * j := Nat.mul_le_mul_right j hWd2
                _ = j * (j + d) := by ring
          calc Nat.card (FibA m n V₀ i) * (Nat.card (FibB m n W V₀ d i j) * 2 ^ (Z.rank * d))
              ≤ 2 ^ (i * (i + d)) * (2 ^ (j * (j + d)) * 2 ^ (Z.rank * d)) :=
                Nat.mul_le_mul hA (Nat.mul_le_mul_right _ hB')
            _ = 2 ^ (i * (i + d) + j * (j + d) + Z.rank * d) := by
                rw [← pow_add, ← pow_add, add_assoc]
            _ ≤ 2 ^ (2 * (i + j + Z.rank) * d) := by
                refine Nat.pow_le_pow_right (by norm_num) ?_
                have hi' : i ≤ d := by omega
                have hj' : j ≤ d := by omega
                have h1 : i * (i + d) ≤ 2 * i * d := by
                  rw [Nat.mul_add]
                  have := Nat.mul_le_mul_left i hi'
                  nlinarith [this]
                have h2 : j * (j + d) ≤ 2 * j * d := by
                  rw [Nat.mul_add]
                  have := Nat.mul_le_mul_left j hj'
                  nlinarith [this]
                nlinarith [h1, h2, Nat.zero_le (Z.rank * d)]
        · have hB : Nat.card (FibB m n W V₀ d i j) = 0 := by
            rw [Nat.card_eq_zero]
            exact Or.inl ⟨fun x => hne ⟨x⟩⟩
          rw [hB, zero_mul, mul_zero]
          exact Nat.zero_le _



/-! ## The rank of the triple's map on the fibre -/

/-- **On the fibre the rank of the triple's map is the rank of `Z`.** -/
lemma finrank_range_eq_rank_of_TCond {V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂}
    {d i j : ℕ} {t : Triple m n} (h : TCond V₀ W Z d i j t) :
    Module.finrank 𝔽₂ (LinearMap.range t.2.2) = Z.rank := by
  have hcomp : compressZ t.1 V₀ W t.2.1 h.hleV h.hleW t.2.2 = ZabsOf V₀ W Z := h.hcomp
  unfold compressZ at hcomp
  have h1 := Commons.LinearAlgebra.LinearMap.finrank_range_mapQ_comp_inclusion
    (K := 𝔽₂) t.1 V₀ W t.2.1 h.hleV h.hleW t.2.2 h.hkerV h.hkerW
  rw [hcomp, finrank_range_ZabsOf] at h1
  exact h1.symm


/-! ## Component extraction from the fibre condition -/

/-- The first component of the fibre condition `Phi3 x = ⟨V₀,W,Z⟩`. -/
lemma Phi3_eq_fst {V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂}
    {x : Σ t : Triple m n, QPair m n t} (hx : Phi3 x = ⟨V₀, W, Z⟩) :
    liftV x.1.1 x.2.1 = V₀ := by
  simpa using congrArg Sigma.fst hx

/-- The second component of the fibre condition. -/
lemma Phi3_eq_snd_fst {V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂}
    {x : Σ t : Triple m n, QPair m n t} (hx : Phi3 x = ⟨V₀, W, Z⟩) :
    liftW x.1.2.1 x.2.2 = W := by
  simpa using congrArg (fun s => s.2.1) hx

/-- The third component of the fibre condition (necessarily a `HEq`, since the type of the matrix
depends on the first two components).  The proof is `cases hx; rfl` — this is the cheap way to
extract a nested dependent component of a `Sigma` from an equality of the whole. -/
lemma Phi3_eq_snd_snd {V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂}
    {x : Σ t : Triple m n, QPair m n t} (hx : Phi3 x = ⟨V₀, W, Z⟩) :
    HEq (XsOf x.1 x.2) Z := by
  cases hx
  rfl

/-- **`p` is determined by `(t,V₀,W)`**: on the fibre, `x.2.1` is the coordinates of `V₀`. -/
lemma Phi3_eq_Vco {V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂}
    {x : Σ t : Triple m n, QPair m n t} (hx : Phi3 x = ⟨V₀, W, Z⟩) :
    Vco x.1.1 V₀ = x.2.1 := by
  rw [← Phi3_eq_fst hx, Vco_liftV]

/-- **`p` is determined by `(t,V₀,W)`**, `W`-side. -/
lemma Phi3_eq_Wco {V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂}
    {x : Σ t : Triple m n, QPair m n t} (hx : Phi3 x = ⟨V₀, W, Z⟩) :
    Wco x.1.2.1 W = x.2.2 := by
  rw [← Phi3_eq_snd_fst hx, Wco_liftW]


/-! ## From the fibre conditions to a `TCond`

This is the last bookkeeping step needed to transfer the fibre count `card_TCond_le` to the
fibre of `Phi3`.  The proof starts with `cases hx`, which replaces `V₀`, `W`, `Z` by the three
components of `Phi3 x` and thus makes all the transports of `XsOf_eq_iff_compressZ` vanish.
-/

/-- **The fibre conditions of `Phi3` give a `TCond`.** -/
lemma tCond_of_fiber {V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂}
    {d i j : ℕ} {x : Σ t : Triple m n, QPair m n t}
    (hx : Phi3 x = ⟨V₀, W, Z⟩) (hgood : ReindexGood d x)
    (hi : Module.finrank 𝔽₂ x.1.1 = i) (hj : m - Module.finrank 𝔽₂ x.1.2.1 = j) :
    TCond V₀ W Z d i j x.1 := by
  cases hx
  have hleV : x.1.1 ≤ liftV x.1.1 x.2.1 := by
    rw [liftV]
    intro y hy
    have h0 : (Qp x.1.1).mulVecLin y = 0 := by
      rw [← LinearMap.mem_ker, ker_Qp]
      exact hy
    show (Qp x.1.1).mulVecLin y ∈ x.2.1
    rw [h0]
    exact Submodule.zero_mem _
  have hleW : liftW x.1.2.1 x.2.2 ≤ x.1.2.1 := by
    rw [liftW]
    rintro z ⟨w, -, rfl⟩
    exact Ip_mem x.1.2.1 w
  have hguard : Module.finrank 𝔽₂ (liftV x.1.1 x.2.1) - Module.finrank 𝔽₂ x.1.1 +
      (Module.finrank 𝔽₂ x.1.2.1 - Module.finrank 𝔽₂ (liftW x.1.2.1 x.2.2)) ≤ d :=
    (SwGuard_iff x.1 x.2 d hgood.1.1 hgood.1.2).mp hgood.2
  exact ⟨hleV, hleW, hguard,
    (Vco_inf_VrOf_eq_bot_iff x.1 (liftV x.1.1 x.2.1)).mp (by rw [Vco_liftV]; exact hgood.1.1),
    (Wco_sup_WrOf_eq_top_iff' x.1 hleW).mp (by rw [Wco_liftW]; exact hgood.1.2),
    (XsOf_eq_iff_compressZ x.1 x.2 (XsOf x.1 x.2)).mp rfl,
    hi, hj⟩


/-- The fibre of `Phi3` at a stratum. -/
abbrev Fibre3 (m n : ℕ) (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d i j : ℕ) : Type :=
  {x : Σ t : Triple m n, QPair m n t // Phi3 x = ⟨V₀, W, Z⟩ ∧ ReindexGood d x ∧
    Module.finrank 𝔽₂ x.1.1 = i ∧ m - Module.finrank 𝔽₂ x.1.2.1 = j}

theorem card_fibre3_le (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d i j : ℕ) (hi : i + j + Z.rank ≤ d) :
    Nat.card (Fibre3 m n V₀ W Z d i j) ≤ 2 ^ (2 * (i + j + Z.rank) * d) := by
  refine (Nat.card_le_card_of_injective
    (fun x : Fibre3 m n V₀ W Z d i j =>
      (⟨x.1.1, tCond_of_fiber x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2⟩ :
        {t : Triple m n // TCond V₀ W Z d i j t})) ?_).trans
    (card_TCond_le V₀ W Z d i j hi)
  intro a b hab
  rcases a with ⟨⟨tx, px⟩, ha⟩
  rcases b with ⟨⟨ty, py⟩, hb⟩
  have h1 : tx = ty := congrArg (fun y : {t : Triple m n // TCond V₀ W Z d i j t} => y.1) hab
  subst h1
  have hEq : px = py := by
    have hpa : px.1 = py.1 := by rw [← Phi3_eq_Vco ha.1, ← Phi3_eq_Vco hb.1]
    have hpb : px.2 = py.2 := by rw [← Phi3_eq_Wco ha.1, ← Phi3_eq_Wco hb.1]
    exact Prod.ext hpa hpb
  exact Subtype.ext (congrArg (fun p => (⟨tx, p⟩ : Σ t : Triple m n, QPair m n t)) hEq)


/-! ## The fibre of `Phi3`: rank, total order and weight

These four lemmas are the input of the weighted fibre bound (P3 of `ROADMAP.md`, session 29).
**Component convention**: for `x : Σ t : Triple m n, QPair m n t` one has `x.1 : Triple m n`
(`x.1.1 = V₂`, `x.1.2.1 = W₂`, `x.1.2.2 = X`) and `x.2 : QPair m n x.1` (`x.2.1 = p.1`,
`x.2.2 = p.2`).  -/

/-- The fibre of `Phi3` over `⟨V₀,W,Z⟩`, restricted to the `Fr`/guard conditions and to the
degrees `1 ≤ totOrder ≤ d` (no stratum restriction). -/
abbrev FFib (m n : ℕ) (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d : ℕ) : Type :=
  {x : Σ t : Triple m n, QPair m n t // Phi3 x = ⟨V₀, W, Z⟩ ∧ ReindexGood d x ∧
    1 ≤ totOrder x.1 ∧ totOrder x.1 ≤ d}

/-- On the fibre, the role-space matrix of the summand has rank `rank Z`. -/
lemma rank_XsOf_of_fiber {V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂}
    {x : Σ t : Triple m n, QPair m n t} (hx : Phi3 x = ⟨V₀, W, Z⟩) :
    (XsOf x.1 x.2).rank = Z.rank := by
  cases hx
  rfl

/-- On the fibre, the rank of the triple's map is `rank Z`. -/
lemma finrank_range_of_fiber {V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂}
    {d i j : ℕ} {x : Σ t : Triple m n, QPair m n t} (hx : Phi3 x = ⟨V₀, W, Z⟩)
    (hgood : ReindexGood d x) (hi : Module.finrank 𝔽₂ x.1.1 = i)
    (hj : m - Module.finrank 𝔽₂ x.1.2.1 = j) :
    Module.finrank 𝔽₂ (LinearMap.range x.1.2.2) = Z.rank := by
  cases hx
  exact finrank_range_eq_rank_of_TCond (tCond_of_fiber rfl hgood hi hj)

/-- On the fibre the total order is `finrank V₂ + (m - finrank W₂) + rank Z`. -/
lemma totOrder_of_fiber {V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂}
    {d i j : ℕ} {x : Σ t : Triple m n, QPair m n t} (hx : Phi3 x = ⟨V₀, W, Z⟩)
    (hgood : ReindexGood d x) (hi : Module.finrank 𝔽₂ x.1.1 = i)
    (hj : m - Module.finrank 𝔽₂ x.1.2.1 = j) :
    totOrder x.1 = Module.finrank 𝔽₂ x.1.1 + (m - Module.finrank 𝔽₂ x.1.2.1) + Z.rank := by
  unfold totOrder
  rw [finrank_range_of_fiber hx hgood hi hj]

/-- **The summand weight on the fibre depends only on the stratum and `rank Z`.** -/
lemma weight_eq_of_fiber {V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂}
    {d C i j : ℕ} {x : Σ t : Triple m n, QPair m n t} (hx : Phi3 x = ⟨V₀, W, Z⟩)
    (hgood : ReindexGood d x) (hi : Module.finrank 𝔽₂ x.1.1 = i)
    (hj : m - Module.finrank 𝔽₂ x.1.2.1 = j) :
    (2 : ℝ) ^ (26 * d * totOrder x.1 + C * (d - totOrder x.1) ^ (2 : ℕ)
        + 3 * d * (XsOf x.1 x.2).rank + 4 * d * Module.finrank 𝔽₂ (LinearMap.range x.1.2.2))
      = (2 : ℝ) ^ (26 * d * (Module.finrank 𝔽₂ x.1.1 + (m - Module.finrank 𝔽₂ x.1.2.1) + Z.rank)
        + C * (d - (Module.finrank 𝔽₂ x.1.1 + (m - Module.finrank 𝔽₂ x.1.2.1) + Z.rank)) ^ (2 : ℕ)
        + 3 * d * Z.rank + 4 * d * Z.rank) := by
  have h1 : totOrder x.1 = Module.finrank 𝔽₂ x.1.1 + (m - Module.finrank 𝔽₂ x.1.2.1) + Z.rank :=
    totOrder_of_fiber hx hgood hi hj
  have h2 : (XsOf x.1 x.2).rank = Z.rank := rank_XsOf_of_fiber hx
  have h3 : Module.finrank 𝔽₂ (LinearMap.range x.1.2.2) = Z.rank :=
    finrank_range_of_fiber hx hgood hi hj
  rw [h1, h2, h3]

end
end Submission.Grassmann
