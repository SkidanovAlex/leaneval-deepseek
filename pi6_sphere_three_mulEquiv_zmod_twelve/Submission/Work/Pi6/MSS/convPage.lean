import Mathlib
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.convTelescope
import Submission.Work.Pi6.MSS.convPZ
import Submission.Work.Pi6.MSS.convPB
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

/-! # Convergence of the spectral sequence of a filtered cochain complex

For `W : CohFilt 𝕜` (a filtered cochain complex with a product, `MSS/CohFilt.lean`) and total degree
`n`, the page `E_{n+2}` in total degree `n` is `E_∞` there: no differential into or out of the
bidegree `(s, n-s)` survives beyond page `n+2`, since differentials out of `(s,n)` have
`r ≤ n - s + 1` and into `(s,n)` have `r ≤ s`.  The classical convergence theorem
`E_∞^{s,n-s} ≅ F^s H^n / F^{s+1} H^n` (where `F^s H^n ⊆ H^n` is the image of `H^n(F^s) → H^n(C)`)
then gives both the vanishing statement and the dimension identity.

The hypothesis `hfin` is needed for the dimension identity (without finiteness of `H^n` the sum of
`finrank`s is not the dimension of `H^n`, because `finrank` of an infinite-dimensional module is
`0`).

Hints: `pZ r s n = F^s C^n ∩ d^{-1}(F^{s+r}C^{n+1})`,
`pB r s n = F^s C^n ∩ d(F^{s+1-r}C^{n-1})` (with `F^0 = C`, the standard `B_r^s`),
`pDen = Z_{r-1}^{s+1} + B_r^s`, `pEraw r s n = Z_r^s/(Z_{r-1}^{s+1} + B_r^s)`.  `F^0 = ⊤` and
`F^{n+1}C^n = ⊥` give `F^0H^n = H^n`, `F^{n+1}H^n = 0`; the identification
`E_∞^s = Z_∞^s/(Z_∞^{s+1} + B_∞^s) → F^sH^n/F^{s+1}H^n` sends the class of a cocycle
`x ∈ F^sC^n` to its cohomology class.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## 1. The stable cycles and boundaries -/

/-- `F^s C^n ∩ ker d`: the `s`-th step of the induced filtration on the cycles. -/
def convZs (W : CohFilt 𝕜) (n s : ℕ) : Submodule 𝕜 (W.C.X n) := W.F s n ⊓ (W.d n).ker

/-- `F^s C^n ∩ im d`: the `s`-th step of the induced filtration on the boundaries. -/
def convBs (W : CohFilt 𝕜) (n s : ℕ) : Submodule 𝕜 (W.C.X n) := W.F s n ⊓ (W.dPrev n).range

/-- The filtration is decreasing. -/
lemma conv_F_anti (W : CohFilt 𝕜) {a b n : ℕ} (h : a ≤ b) : W.F b n ≤ W.F a n := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans (W.F_mono _ n) ih

/-- Above the `n`-th filtration step the degree-`n` part vanishes. -/
lemma conv_F_eq_bot (W : CohFilt 𝕜) {m n : ℕ} (h : n + 1 ≤ m) : W.F m n = ⊥ :=
  le_bot_iff.mp (le_trans (conv_F_anti W h) (le_of_eq (W.F_top n)))

/-- `d ∘ d = 0`, elementwise. -/
lemma conv_d_comp_d (W : CohFilt 𝕜) (n : ℕ) (z : W.C.X n) : W.d (n+1) (W.d n z) = 0 := by
  have h0 := congrArg (fun f : W.C.X n ⟶ W.C.X (n+2) => f.hom z)
    (HomologicalComplex.d_comp_d W.C n (n+1) (n+2))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, CohFilt.d] using h0

/-- `d ∘ d = 0` in the form `d (dPrev y) = 0`. -/
lemma conv_dPrev_d (W : CohFilt 𝕜) (n : ℕ) (y : W.C.X (n-1)) : W.d n (W.dPrev n y) = 0 := by
  have h0 := congrArg (fun f : W.C.X (n-1) ⟶ W.C.X (n+1) => f.hom y)
    (HomologicalComplex.d_comp_d W.C (n-1) n (n+1))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, CohFilt.d, CohFilt.dPrev] using h0

lemma convZs_mono (W : CohFilt 𝕜) (n s : ℕ) : convZs W n (s+1) ≤ convZs W n s :=
  inf_le_inf (W.F_mono s n) le_rfl

lemma convBs_mono (W : CohFilt 𝕜) (n s : ℕ) : convBs W n (s+1) ≤ convBs W n s :=
  inf_le_inf (W.F_mono s n) le_rfl

lemma convZs_zero (W : CohFilt 𝕜) (n : ℕ) : convZs W n 0 = (W.d n).ker := by
  simp [convZs, W.F_zero]

lemma convBs_zero (W : CohFilt 𝕜) (n : ℕ) : convBs W n 0 = (W.dPrev n).range := by
  simp [convBs, W.F_zero]

lemma convZs_bot (W : CohFilt 𝕜) (n : ℕ) : convZs W n (n+1) = ⊥ := by
  simp [convZs, W.F_top]

lemma convBs_bot (W : CohFilt 𝕜) (n : ℕ) : convBs W n (n+1) = ⊥ := by
  simp [convBs, W.F_top]

lemma convZs_le_zero (W : CohFilt 𝕜) (n s : ℕ) : convZs W n s ≤ convZs W n 0 := by
  rw [convZs_zero]; exact inf_le_right

lemma convBs_le_zero (W : CohFilt 𝕜) (n s : ℕ) : convBs W n s ≤ convBs W n 0 := by
  rw [convBs_zero]; exact inf_le_right

lemma convBs_le_ker (W : CohFilt 𝕜) (n : ℕ) : (W.dPrev n).range ≤ (W.d n).ker := by
  rintro _ ⟨y, rfl⟩
  exact conv_dPrev_d W n y

lemma convBs_le_convZs (W : CohFilt 𝕜) (n s : ℕ) : convBs W n s ≤ convZs W n s :=
  inf_le_inf le_rfl (convBs_le_ker W n)

/-- Inside `↥A`, the preimage of a supremum of submodules of `A` is the supremum of the
preimages. -/
lemma conv_comap_sup {V : Type} [AddCommGroup V] [Module 𝕜 V] {A S T : Submodule 𝕜 V}
    (hS : S ≤ A) (hT : T ≤ A) :
    (S ⊔ T).comap A.subtype = S.comap A.subtype ⊔ T.comap A.subtype := by
  refine le_antisymm ?_ (sup_le (Submodule.comap_mono le_sup_left)
    (Submodule.comap_mono le_sup_right))
  intro x hx
  rw [Submodule.mem_comap] at hx
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hx
  refine Submodule.mem_sup.mpr ⟨⟨s, hS hs⟩, hs, ⟨t, hT ht⟩, ht, ?_⟩
  exact Subtype.ext hst

/-! ## 2. The stable objects are `pZ`, `pB` in the stable range -/

lemma conv_pZ_eq (W : CohFilt 𝕜) (m t n : ℕ) (hm : n + 2 ≤ t + m) :
    pZ 𝕜 W m t n = convZs W n t :=
  convPZ 𝕜 W m t n hm

lemma conv_pB_eq (W : CohFilt 𝕜) (m t n : ℕ) (hm : t + 1 ≤ m) :
    pB 𝕜 W m t n = convBs W n t :=
  convPB 𝕜 W m t n hm

/-- The denominator of `E_{n+2}^{t,n}` is `Z^{t+1} + B^t`. -/
lemma conv_pDen_eq (W : CohFilt 𝕜) (n t : ℕ) (ht : t ≤ n) :
    pDen 𝕜 W (n+2) t n = convZs W n (t+1) ⊔ convBs W n t := by
  have h1 : n + 2 - 1 = n + 1 := by omega
  rw [pDen, h1, conv_pZ_eq W (n+1) (t+1) n (by omega), conv_pB_eq W (n+2) t n (by omega)]

/-! ## 3. The class map `Z^0 = ker d → H^n` -/

-- The statement of the child lemma `convHomology` (the concrete description of the homology of a
-- cochain complex of modules), kept as a hypothesis during the development.
variable (hom : ∀ (K : CochainComplex.{0, 1, 0} (ModuleCat 𝕜) ℕ) (m : ℕ),
    Nonempty (K.homology m ≃ₗ[𝕜] (↥(LinearMap.ker (K.d m (m+1)).hom) ⧸
      Submodule.comap (LinearMap.ker (K.d m (m+1)).hom).subtype
        (LinearMap.range (K.d (m-1) m).hom))))

/-- The quotient `Z^0 / B^0` of the cycles by the boundaries. -/
abbrev convCycQ (W : CohFilt 𝕜) (n : ℕ) : Type :=
  (↥(LinearMap.ker (W.d n))) ⧸
    Submodule.comap (LinearMap.ker (W.d n)).subtype (LinearMap.range (W.dPrev n))

/-- `H^n ≅ Z^0/B^0`. -/
noncomputable def convIso (W : CohFilt 𝕜) (n : ℕ) : W.C.homology n ≃ₗ[𝕜] convCycQ W n :=
  Classical.choice (hom W.C n)

/-- The class map `Z^0 = ker d → H^n`, via `Z^0/B^0 ≅ H^n`. -/
noncomputable def convClassMap (W : CohFilt 𝕜) (n : ℕ) :
    ↥(convZs W n 0) →ₗ[𝕜] W.C.homology n :=
  (convIso hom W n).symm.toLinearMap.comp
    ((Submodule.mkQ (Submodule.comap (LinearMap.ker (W.d n)).subtype
        (LinearMap.range (W.dPrev n)))).comp
      (LinearEquiv.ofEq (convZs W n 0) (LinearMap.ker (W.d n)) (convZs_zero W n)).toLinearMap)

lemma convClassMap_apply (W : CohFilt 𝕜) (n : ℕ) (x : ↥(convZs W n 0)) :
    convClassMap hom W n x =
      (convIso hom W n).symm (Submodule.mkQ (Submodule.comap (LinearMap.ker (W.d n)).subtype
        (LinearMap.range (W.dPrev n))) (LinearEquiv.ofEq _ _ (convZs_zero W n) x)) := rfl

lemma convClassMap_eq_zero_iff (W : CohFilt 𝕜) (n : ℕ) (x : ↥(convZs W n 0)) :
    convClassMap hom W n x = 0 ↔ (x : W.C.X n) ∈ (W.dPrev n).range := by
  rw [convClassMap_apply, ← (convIso hom W n).symm.map_zero,
    (convIso hom W n).symm.injective.eq_iff, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
    LinearEquiv.coe_ofEq_apply]

lemma convClassMap_ker (W : CohFilt 𝕜) (n : ℕ) :
    (convClassMap hom W n).ker = Submodule.comap (convZs W n 0).subtype (convBs W n 0) := by
  ext x
  rw [Submodule.mem_comap, LinearMap.mem_ker, convBs_zero]
  exact convClassMap_eq_zero_iff hom W n x

lemma convClassMap_range (W : CohFilt 𝕜) (n : ℕ) : (convClassMap hom W n).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  obtain ⟨w, hw⟩ := Submodule.mkQ_surjective (Submodule.comap (LinearMap.ker (W.d n)).subtype
    (LinearMap.range (W.dPrev n))) ((convIso hom W n) y)
  refine ⟨(LinearEquiv.ofEq (convZs W n 0) (LinearMap.ker (W.d n))
    (convZs_zero W n)).symm w, ?_⟩
  rw [convClassMap_apply, LinearEquiv.apply_symm_apply, hw, LinearEquiv.symm_apply_apply]

/-- The class map on the cycles lying in `F^s`. -/
noncomputable def convClass (W : CohFilt 𝕜) (n s : ℕ) :
    ↥(convZs W n s) →ₗ[𝕜] W.C.homology n :=
  (convClassMap hom W n).comp (Submodule.inclusion (convZs_le_zero W n s))

lemma convClass_apply (W : CohFilt 𝕜) (n s : ℕ) (x : ↥(convZs W n s)) :
    convClass hom W n s x = convClassMap hom W n (Submodule.inclusion (convZs_le_zero W n s) x) :=
  rfl

lemma convClass_eq_zero_iff (W : CohFilt 𝕜) (n s : ℕ) (x : ↥(convZs W n s)) :
    convClass hom W n s x = 0 ↔ (x : W.C.X n) ∈ (W.dPrev n).range :=
  convClassMap_eq_zero_iff hom W n (Submodule.inclusion (convZs_le_zero W n s) x)

lemma convClass_ker (W : CohFilt 𝕜) (n s : ℕ) :
    (convClass hom W n s).ker = Submodule.comap (convZs W n s).subtype (convBs W n s) := by
  ext x
  rw [Submodule.mem_comap, LinearMap.mem_ker, convBs, Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨x.2.1, (convClass_eq_zero_iff hom W n s x).mp h⟩
  · intro h
    exact (convClass_eq_zero_iff hom W n s x).mpr h.2

/-- `F^s H^n`, the image in `H^n` of the cycles lying in `F^s C^n`. -/
noncomputable def convCH (W : CohFilt 𝕜) (n s : ℕ) : Submodule 𝕜 (W.C.homology n) :=
  (convClass hom W n s).range

lemma convClass_succ (W : CohFilt 𝕜) (n s : ℕ) (x : ↥(convZs W n (s+1))) :
    convClass hom W n (s+1) x = convClass hom W n s ⟨x.1, convZs_mono W n s x.2⟩ := by
  rw [convClass_apply, convClass_apply]
  congr 1

lemma convCH_succ_le (W : CohFilt 𝕜) (n s : ℕ) : convCH hom W n (s+1) ≤ convCH hom W n s := by
  rintro y ⟨x, rfl⟩
  exact ⟨⟨x.1, convZs_mono W n s x.2⟩, (convClass_succ hom W n s x).symm⟩

lemma convCH_succ (W : CohFilt 𝕜) (n s : ℕ) :
    convCH hom W n (s+1) = Submodule.map (convClass hom W n s)
      (Submodule.comap (convZs W n s).subtype (convZs W n (s+1))) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine Submodule.mem_map.mpr ⟨(⟨x.1, convZs_mono W n s x.2⟩ : ↥(convZs W n s)), ?_, ?_⟩
    · rw [Submodule.mem_comap]
      exact x.2
    · exact (convClass_succ hom W n s x).symm
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.1, hx⟩, convClass_succ hom W n s ⟨x.1, hx⟩⟩

lemma convClass_zero (W : CohFilt 𝕜) (n : ℕ) : convClass hom W n 0 = convClassMap hom W n := by
  ext x
  rw [convClass_apply]
  congr 1

lemma convCH_zero (W : CohFilt 𝕜) (n : ℕ) : convCH hom W n 0 = ⊤ := by
  rw [convCH, convClass_zero, convClassMap_range]

lemma convZs_val_eq_zero (W : CohFilt 𝕜) (n : ℕ) (x : ↥(convZs W n (n+1))) :
    (x : W.C.X n) = 0 := by
  have h := Submodule.eq_zero_of_bot_submodule
    (LinearEquiv.ofEq (convZs W n (n+1)) ⊥ (convZs_bot W n) x)
  simpa using h

lemma convCH_bot (W : CohFilt 𝕜) (n : ℕ) : convCH hom W n (n+1) = ⊥ := by
  rw [convCH, Submodule.eq_bot_iff]
  rintro y ⟨x, rfl⟩
  rw [convClass_apply]
  have h0 : Submodule.inclusion (convZs_le_zero W n (n+1)) x = 0 := by
    refine Subtype.ext ?_
    simpa using convZs_val_eq_zero W n x
  rw [h0, map_zero]

/-! ## 4. The isomorphism with the associated graded piece -/

/-- `(Z^t ⧸ Z^{t+1})`-style denominator inside `↥(Z^t)`: the submodule
`Z^{t+1} + B^t` of `↥(Z^t)`. -/
noncomputable def convKer (W : CohFilt 𝕜) (n t : ℕ) : Submodule 𝕜 ↥(convZs W n t) :=
  Submodule.comap (convZs W n t).subtype (convZs W n (t+1)) ⊔
    Submodule.comap (convZs W n t).subtype (convBs W n t)

/-- The class of a cycle in `F^t` lies in `F^t H^n`. -/
lemma convClass_mem_CH (W : CohFilt 𝕜) (n t : ℕ) (x : ↥(convZs W n t)) :
    convClass hom W n t x ∈ convCH hom W n t :=
  LinearMap.mem_range.mpr ⟨x, rfl⟩

/-- The canonical map `Z^t → F^t H^n / F^{t+1} H^n`, sending a cycle to its class. -/
noncomputable def convG (W : CohFilt 𝕜) (n t : ℕ) :
    ↥(convZs W n t) →ₗ[𝕜] ((↥(convCH hom W n t)) ⧸
      Submodule.comap (convCH hom W n t).subtype (convCH hom W n (t+1))) :=
  (Submodule.mkQ _).comp ((convClass hom W n t).codRestrict (convCH hom W n t)
    (convClass_mem_CH hom W n t))

lemma convG_eq_zero_iff (W : CohFilt 𝕜) (n t : ℕ) (x : ↥(convZs W n t)) :
    convG hom W n t x = 0 ↔ convClass hom W n t x ∈ convCH hom W n (t+1) := by
  show Submodule.mkQ (Submodule.comap (convCH hom W n t).subtype (convCH hom W n (t+1)))
      (LinearMap.codRestrict (convCH hom W n t) (convClass hom W n t)
        (convClass_mem_CH hom W n t) x) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.subtype_apply, LinearMap.codRestrict_apply]

lemma convG_ker (W : CohFilt 𝕜) (n t : ℕ) :
    (convG hom W n t).ker = convKer W n t := by
  ext x
  rw [LinearMap.mem_ker, convKer, Submodule.mem_sup, convG_eq_zero_iff, convCH_succ]
  constructor
  · intro hx
    obtain ⟨y, hy, hcl⟩ := Submodule.mem_map.mp hx
    refine ⟨y, hy, x - y, ?_, ?_⟩
    · rw [Submodule.mem_comap, convBs, Submodule.mem_inf]
      exact ⟨(W.F t n).sub_mem x.2.1 y.2.1,
        (convClass_eq_zero_iff hom W n t (x - y)).mp (by rw [map_sub, hcl, sub_self])⟩
    · abel
  · rintro ⟨y, hy, z, hz, hyz⟩
    rw [Submodule.mem_comap, convBs, Submodule.mem_inf] at hz
    have hz0 : convClass hom W n t z = 0 :=
      (convClass_eq_zero_iff hom W n t z).mpr hz.2
    refine Submodule.mem_map.mpr ⟨y, hy, ?_⟩
    rw [show x = y + z from hyz.symm, map_add, hz0, add_zero]

lemma convG_range (W : CohFilt 𝕜) (n t : ℕ) : (convG hom W n t).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro y
  obtain ⟨w, hw⟩ := Submodule.mkQ_surjective (Submodule.comap (convCH hom W n t).subtype
    (convCH hom W n (t+1))) y
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp w.2
  refine ⟨x, ?_⟩
  show Submodule.mkQ (Submodule.comap (convCH hom W n t).subtype (convCH hom W n (t+1)))
      (LinearMap.codRestrict (convCH hom W n t) (convClass hom W n t)
        (convClass_mem_CH hom W n t) x) = y
  rw [show (LinearMap.codRestrict (convCH hom W n t) (convClass hom W n t)
      (convClass_mem_CH hom W n t)) x = w from Subtype.ext hx, hw]

/-- The `t`-th piece of the associated graded of `H^n`. -/
abbrev convGr (W : CohFilt 𝕜) (n t : ℕ) : Type :=
  (↥(convCH hom W n t)) ⧸ Submodule.comap (convCH hom W n t).subtype (convCH hom W n (t+1))

lemma convE (W : CohFilt 𝕜) (n t : ℕ) (ht : t ≤ n) :
    Nonempty (pEraw 𝕜 W (n+2) t n ≃ₗ[𝕜] convGr hom W n t) := by
  have hZ : pZ 𝕜 W (n+2) t n = convZs W n t := conv_pZ_eq W (n+2) t n (by omega)
  have hDen : pDen 𝕜 W (n+2) t n = convZs W n (t+1) ⊔ convBs W n t := conv_pDen_eq W n t ht
  have e3 := (Submodule.quotEquivOfEq (convKer W n t) (convG hom W n t).ker
      (convG_ker hom W n t).symm).trans
    ((LinearMap.quotKerEquivRange (convG hom W n t)).trans
      (LinearEquiv.ofTop _ (convG_range hom W n t)))
  have hK : convKer W n t
      = Submodule.comap (convZs W n t).subtype (convZs W n (t+1) ⊔ convBs W n t) :=
    (conv_comap_sup (convZs_mono W n t) (convBs_le_convZs W n t)).symm
  have hker : ((Submodule.mkQ (convKer W n t)).comp
      (LinearEquiv.ofEq (pZ 𝕜 W (n+2) t n) (convZs W n t) hZ).toLinearMap).ker
      = (pDen 𝕜 W (n+2) t n).comap (pZ 𝕜 W (n+2) t n).subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    show Submodule.mkQ (convKer W n t)
      ((LinearEquiv.ofEq (pZ 𝕜 W (n+2) t n) (convZs W n t) hZ) x) = 0
        ↔ (x : W.C.X n) ∈ pDen 𝕜 W (n+2) t n
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_comap,
      Submodule.subtype_apply, LinearEquiv.coe_ofEq_apply, hDen]
  have hsurj : Function.Surjective ((Submodule.mkQ (convKer W n t)).comp
      (LinearEquiv.ofEq (pZ 𝕜 W (n+2) t n) (convZs W n t) hZ).toLinearMap) := by
    intro y
    obtain ⟨w, hw⟩ := Submodule.mkQ_surjective (convKer W n t) y
    exact ⟨(LinearEquiv.ofEq (pZ 𝕜 W (n+2) t n) (convZs W n t) hZ).symm w, by
      show Submodule.mkQ (convKer W n t)
        ((LinearEquiv.ofEq (pZ 𝕜 W (n+2) t n) (convZs W n t) hZ)
          ((LinearEquiv.ofEq (pZ 𝕜 W (n+2) t n) (convZs W n t) hZ).symm w)) = y
      rw [LinearEquiv.apply_symm_apply, hw]⟩
  exact ⟨((Submodule.quotEquivOfEq _ _ hker).symm.trans
    ((LinearMap.quotKerEquivRange _).trans
      (LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr hsurj)))).trans e3⟩

/-! ## 5. Convergence in total degree `n` -/

-- `tel` is the statement of the child lemma `convTelescope`, kept as a hypothesis during the
-- development.
theorem convPageAux
    (hom : ∀ (K : CochainComplex.{0, 1, 0} (ModuleCat 𝕜) ℕ) (m : ℕ),
      Nonempty (K.homology m ≃ₗ[𝕜] (↥(LinearMap.ker (K.d m (m+1)).hom) ⧸
        Submodule.comap (LinearMap.ker (K.d m (m+1)).hom).subtype
          (LinearMap.range (K.d (m-1) m).hom))))
    (tel : ∀ {V : Type} [AddCommGroup V] [Module 𝕜 V] [Module.Finite 𝕜 V]
      (A : ℕ → Submodule 𝕜 V) (hmono : ∀ t : ℕ, A (t+1) ≤ A t) (m : ℕ) (hbot : A (m+1) = ⊥),
      (∑ t ∈ Finset.range (m+1),
        Module.finrank 𝕜 ((↥(A t)) ⧸ Submodule.comap (A t).subtype (A (t+1)))) =
        Module.finrank 𝕜 ↥(A 0))
    (W : CohFilt 𝕜) (n : ℕ) (hfin : Module.Finite 𝕜 (W.C.homology n)) :
    (∀ s : ℕ, s ≤ n → Subsingleton (W.C.homology n) →
        Subsingleton (pEraw 𝕜 W (n+2) s n)) ∧
    ((∑ t ∈ Finset.range (n+1), Module.finrank 𝕜 (pEraw 𝕜 W (n+2) t n))
      = Module.finrank 𝕜 (W.C.homology n)) := by
  constructor
  · intro s hs hsub
    haveI := hsub
    obtain ⟨e⟩ := convE hom W n s hs
    haveI : Subsingleton ↥(convCH hom W n s) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    haveI : Subsingleton (convGr hom W n s) :=
      ⟨fun a b => by
        obtain ⟨a', rfl⟩ := Submodule.mkQ_surjective _ a
        obtain ⟨b', rfl⟩ := Submodule.mkQ_surjective _ b
        rw [Subsingleton.elim a' b']⟩
    exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩
  · haveI := hfin
    have h1 : ∀ t ∈ Finset.range (n+1),
        Module.finrank 𝕜 (pEraw 𝕜 W (n+2) t n) = Module.finrank 𝕜 (convGr hom W n t) := by
      intro t ht
      have ht' : t ≤ n := by have := Finset.mem_range.mp ht; omega
      obtain ⟨e⟩ := convE hom W n t ht'
      exact LinearEquiv.finrank_eq e
    rw [Finset.sum_congr rfl h1,
      tel (fun t => convCH hom W n t) (fun t => convCH_succ_le hom W n t) n
        (convCH_bot hom W n),
      convCH_zero hom W n]
    exact LinearEquiv.finrank_eq Submodule.topEquiv

/-! ## 6. `H^n = Z^n/B^n` for a cochain complex of modules -/

/-- The homology of a cochain complex of modules in degree `n` is the cycles modulo the
boundaries, in the exact form needed by `convPageAux`. -/
lemma convHomologyLocal (R : Type) [Ring R] (K : CochainComplex.{0, 1, 0} (ModuleCat R) ℕ)
    (n : ℕ) :
    Nonempty (K.homology n ≃ₗ[R]
      (↥(LinearMap.ker (K.d n (n+1)).hom) ⧸
        Submodule.comap (LinearMap.ker (K.d n (n+1)).hom).subtype
          (LinearMap.range (K.d (n-1) n).hom))) := by
  have hi : (ComplexShape.up ℕ).prev n = n - 1 := by
    rcases n with _ | k
    · rw [(ComplexShape.up ℕ).prev_eq_self' 0
        (by rintro j hj; simp only [ComplexShape.up, ComplexShape.up'_Rel] at hj; omega)]
    · exact (ComplexShape.up ℕ).prev_eq' (i := k + 1) (j := k) rfl
  have hk : (ComplexShape.up ℕ).next n = n + 1 :=
    (ComplexShape.up ℕ).next_eq' (i := n) (j := n + 1) rfl
  have hden : (HomologicalComplex.sc' K (n-1) n (n+1)).moduleCatToCycles.range
      = Submodule.comap (LinearMap.ker ((HomologicalComplex.sc' K (n-1) n (n+1)).g.hom)).subtype
          (LinearMap.range ((HomologicalComplex.sc' K (n-1) n (n+1)).f.hom)) := by
    simp only [ShortComplex.moduleCatToCycles]
    exact LinearMap.range_codRestrict _ _ _
  exact ⟨((K.homologyIsoSc' (n-1) n (n+1) hi hk).trans
    (ShortComplex.moduleCatHomologyIso (K.sc' (n-1) n (n+1)))).toLinearEquiv.trans
    (Submodule.quotEquivOfEq _ _ hden)⟩

/-! ## 7. The convergence theorem -/

theorem convPage (𝕜 : Type) [Field 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜) (n : ℕ)
    (hfin : Module.Finite 𝕜 (W.C.homology n)) :
    (∀ s : ℕ, s ≤ n → Subsingleton (W.C.homology n) →
        Subsingleton (Work.Pi6.MSS.pEraw 𝕜 W (n+2) s n)) ∧
    ((∑ t ∈ Finset.range (n+1), Module.finrank 𝕜 (Work.Pi6.MSS.pEraw 𝕜 W (n+2) t n))
      = Module.finrank 𝕜 (W.C.homology n)) :=
  convPageAux (convHomologyLocal 𝕜) (convTelescope 𝕜) W n hfin

end

end Work.Pi6.MSS
