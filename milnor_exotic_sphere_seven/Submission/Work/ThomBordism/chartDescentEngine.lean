import Mathlib
import Submission.Work.Thom.chartCoeff_nonZeroDivisor
import Submission.Work.Thom.thomClass_of_finite_cover
import Submission.Work.Thom.localThom_union
import Submission.Work.ThomBordism.thomClassFibreDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Descent of local classes over a chart cover

`Work.ThomBordism.chartDataDescent`: a family of pairwise compatible local classes over the chart
pieces `Z.baseSet i` of a real bundle `Z` glues to a global class of the Thom pair.

The engines are
* `Work.ThomBordism.subGlue` — the two-piece Mayer–Vietoris glueing for arbitrary open subsets;
* `Work.ThomBordism.coherentExtend` — the transfinite union step (a compatible family of classes
  over an increasing well-ordered family of open sets glues, uniquely, to the union);
* `Work.ThomBordism.vanish_of_pieces` — its uniqueness half;
* `Work.ThomBordism.vanish_on_base_cover` — separation for the chart cover.
-/

open Work.TangentClasses
open scoped Topology

namespace Work.ThomBordism

open Work.Cohomology
open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The cumulative union `⋃_{β ≤ γ} P β` of a well-ordered family of pieces. -/
def cumul {Γ : Type} [Preorder Γ] {B : Type} (P : Γ → Set B) (γ : Γ) : Set B :=
  ⋃ β, ⋃ (_ : β ≤ γ), P β

theorem cumul_eq {Γ : Type} [Preorder Γ] {B : Type} (P : Γ → Set B) (γ : Γ) :
    cumul P γ = ⋃ β, ⋃ (_ : β ≤ γ), P β := rfl

/-- The union over a subtype below `γ₀`. -/
theorem iUnion_Iio_eq {Γ : Type} [Preorder Γ] (V : Γ → Set X) (γ : Γ) :
    (⋃ δ : ↥(Set.Iio γ), V (δ : Γ)) = ⋃ δ : Γ, ⋃ (_ : δ < γ), V δ := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨δ, hx⟩
    exact ⟨δ.1, δ.2, hx⟩
  · rintro ⟨δ, hδ, hx⟩
    exact ⟨⟨δ, hδ⟩, hx⟩

/-- The union of the initial segments inside a subtype. -/
theorem iUnion_Iio_initial {Γ : Type} [LinearOrder Γ] (V : Γ → Set X) {γ γ₀ : Γ} (h : γ < γ₀) :
    (⋃ δ : ↥(Set.Iio γ₀), ⋃ (_ : (δ : Γ) < γ), V (δ : Γ))
      = ⋃ δ : Γ, ⋃ (_ : δ < γ), V δ := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨δ, hδγ, hx⟩
    exact ⟨δ.1, hδγ, hx⟩
  · rintro ⟨δ, hδγ, hx⟩
    exact ⟨⟨δ, lt_trans hδγ h⟩, hδγ, hx⟩

/-- The underlying relative cochain of a relative cycle. -/
abbrev cycCoe {A : Set X} {U : Set X} {k : ℕ} (z : ↥((rcSet A U).cycles k)) : ↥(rcKern A U k) :=
  ((rcSet A U).iCycles k z : ↥(rcKern A U k))

/-- The cycle of a closed relative cochain. -/
noncomputable def cycOf {A : Set X} {U : Set X} {k : ℕ} (z : ↥(rcKern A U k))
    (hz : rcDiff A U k z = 0) : ↥((rcSet A U).cycles k) :=
  cocycleOfK (rcSet A U) (z : (rcSet A U).X k) (by rw [rcSet_d]; exact hz)

/-- The underlying cochain of `cycOf` is the closed cochain. -/
theorem iCycles_cycOf {A : Set X} {U : Set X} {k : ℕ} (z : ↥(rcKern A U k))
    (hz : rcDiff A U k z = 0) : cycCoe (cycOf z hz) = z :=
  iCycles_cocycleOfK (rcSet A U) (z : (rcSet A U).X k) (by rw [rcSet_d]; exact hz)

/-- `iCycles` is injective: two cycles with the same underlying cochain are equal. -/
theorem iCycles_injective {A : Set X} {U : Set X} {k : ℕ} :
    Function.Injective (cycCoe (A := A) (U := U) (k := k)) :=
  (ModuleCat.mono_iff_injective ((rcSet A U).iCycles k)).mp inferInstance

/-- Cycle extensionality. -/
theorem cycles_ext {A : Set X} {U : Set X} {k : ℕ} {a b : ↥((rcSet A U).cycles k)}
    (h : cycCoe a = cycCoe b) : a = b :=
  iCycles_injective h

/-- The underlying cochain of a difference of cycles. -/
theorem cycCoe_sub {A : Set X} {U : Set X} {k : ℕ} (a b : ↥((rcSet A U).cycles k)) :
    cycCoe (a - b) = cycCoe a - cycCoe b :=
  map_sub (ModuleCat.Hom.hom ((rcSet A U).iCycles k)) a b

/-- The underlying cochain of the restriction of a cycle. -/
theorem cycCoe_cyclesMap {A : Set X} {k : ℕ} {S T : Set X} (h : S ⊆ T)
    (z : ↥((rcSet A T).cycles k)) :
    cycCoe (HomologicalComplex.cyclesMap (rcRes A h) k z) = rcResLM A h k (cycCoe z) := by
  have hci := congrArg (fun (g : (rcSet A T).cycles k ⟶ (rcSet A S).X k) => g z)
    (HomologicalComplex.cyclesMap_i (rcRes A h) k)
  rw [rcRes_f] at hci
  exact hci

/-- A cycle is closed. -/
theorem rcDiff_cycCoe {A : Set X} {U : Set X} {k : ℕ} (z : ↥((rcSet A U).cycles k)) :
    rcDiff A U k (cycCoe z) = 0 :=
  relDiffLM_iCycles (TopCat.of U) {y : U | (y : X) ∈ A} k z

/-- The underlying cochain of a boundary. -/
theorem cycCoe_toCycles {A : Set X} {U : Set X} {k : ℕ} (v : ↥(rcKern A U k)) :
    cycCoe ((rcSet A U).toCycles k (k+1) v) = rcDiff A U k v := by
  show ((rcSet A U).iCycles (k+1) ((rcSet A U).toCycles k (k+1) v) : (rcSet A U).X (k+1))
    = (rcDiff A U k) v
  have h := congrArg (fun (f : (rcSet A U).X k ⟶ (rcSet A U).X (k+1)) => f v)
    (HomologicalComplex.toCycles_i (rcSet A U) k (k+1))
  erw [ModuleCat.comp_apply] at h
  rw [rcSet_d] at h
  exact h

/-- A boundary has vanishing class. -/
theorem homologyπ_toCycles {A : Set X} {U : Set X} {k : ℕ} (v : ↥(rcKern A U k)) :
    ((rcSet A U).homologyπ (k+1)) ((rcSet A U).toCycles k (k+1) v) = 0 := by
  have h := congrArg (fun (f : (rcSet A U).X k ⟶ (rcSet A U).homology (k+1)) => f v)
    (HomologicalComplex.toCycles_comp_homologyπ (rcSet A U) k (k+1))
  erw [ModuleCat.comp_apply] at h
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply] at h
  exact h

/-- The class of a restricted cycle. -/
theorem homologyπ_cyclesMap {C D : CochainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) (k : ℕ)
    (z : ↥(C.cycles k)) :
    ((D.homologyπ k) ((HomologicalComplex.cyclesMap φ k) z))
      = ((HomologicalComplex.homologyMap φ k).hom) ((C.homologyπ k) z) := by
  have h2 := congrArg (fun (f : C.cycles k ⟶ D.homology k) => f z)
    (HomologicalComplex.homologyπ_naturality φ k)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2.symm

/-- The restriction of a class to itself is the identity. -/
theorem pdCohMap_self {X : TopCat} (A U : Set X) (h : U ⊆ U) (k : ℕ)
    (x : pdCohSub X A U k) : (ModuleCat.Hom.hom (pdCohMap X A U U h k)) x = x := by
  have hrc : rcRes A h = 𝟙 (rcSet A U) := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [rcRes_f, HomologicalComplex.id_f]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change (rcResLM A h n) y = y
    exact rcResLM_self A h n y
  rw [show pdCohMap X A U U h k = HomologicalComplex.homologyMap (rcRes A h) k from rfl, hrc,
    HomologicalComplex.homologyMap_id]
  rfl

/-- **The two-piece Mayer–Vietoris glueing for open subsets.**  Two piece-classes agreeing on the
overlap are the two restrictions of a class on the union. -/
theorem subGlue {X : TopCat} (A : Set X) (n : ℕ) {W U : Set X} (hW : IsOpen W) (hU : IsOpen U)
    (cW : pdCohSub X A W n) (cU : pdCohSub X A U n)
    (h : (ModuleCat.Hom.hom (pdCohMap X A W (W ∩ U) Set.inter_subset_left n)) cW
      = (ModuleCat.Hom.hom (pdCohMap X A U (W ∩ U) Set.inter_subset_right n)) cU) :
    ∃ c : pdCohSub X A (W ∪ U) n,
      (ModuleCat.Hom.hom (pdCohMap X A (W ∪ U) W Set.subset_union_left n)) c = cW ∧
      (ModuleCat.Hom.hom (pdCohMap X A (W ∪ U) U Set.subset_union_right n)) c = cU := by
  have hWS : W ⊆ W ∪ U := Set.subset_union_left
  have hUS : U ⊆ W ∪ U := Set.subset_union_right
  have hWIS : W ∩ U ⊆ W ∪ U := Set.inter_subset_left.trans Set.subset_union_left
  have hcov : ((Subtype.val : ↥(W ∪ U) → X) ⁻¹' W) ∪ ((Subtype.val) ⁻¹' U) = Set.univ := by
    rw [← Set.preimage_union]
    exact Set.eq_univ_iff_forall.mpr (fun y => y.2)
  have hWo : IsOpen ((Subtype.val : ↥(W ∪ U) → X) ⁻¹' W) := hW.preimage continuous_subtype_val
  have hUo : IsOpen ((Subtype.val : ↥(W ∪ U) → X) ⁻¹' U) := hU.preimage continuous_subtype_val
  have hnatW := congrArg (fun f => (ModuleCat.Hom.hom f) cW)
    (luIso_natural X A hWS hWIS Set.inter_subset_left n)
  have hnatU := congrArg (fun f => (ModuleCat.Hom.hom f) cU)
    (luIso_natural X A hUS hWIS Set.inter_subset_right n)
  have hcompat : (ModuleCat.Hom.hom (pdCohMap (TopCat.of ↥(W ∪ U)) ((Subtype.val) ⁻¹' A)
        ((Subtype.val) ⁻¹' W) (((Subtype.val) ⁻¹' W) ∩ ((Subtype.val) ⁻¹' U)) Set.inter_subset_left n))
      ((luIso X A hWS n).hom cW)
    = (ModuleCat.Hom.hom (pdCohMap (TopCat.of ↥(W ∪ U)) ((Subtype.val) ⁻¹' A)
        ((Subtype.val) ⁻¹' U) (((Subtype.val) ⁻¹' W) ∩ ((Subtype.val) ⁻¹' U)) Set.inter_subset_right n))
      ((luIso X A hUS n).hom cU) := by
    have hc : (ModuleCat.Hom.hom (pdCohMap (TopCat.of ↥(W ∪ U)) ((Subtype.val) ⁻¹' A)
          ((Subtype.val) ⁻¹' W) ((Subtype.val) ⁻¹' (W ∩ U)) (Set.preimage_mono Set.inter_subset_left) n))
        ((luIso X A hWS n).hom cW)
      = (ModuleCat.Hom.hom (pdCohMap (TopCat.of ↥(W ∪ U)) ((Subtype.val) ⁻¹' A)
          ((Subtype.val) ⁻¹' U) ((Subtype.val) ⁻¹' (W ∩ U)) (Set.preimage_mono Set.inter_subset_right) n))
        ((luIso X A hUS n).hom cU) :=
      hnatW.trans ((congrArg (fun y => (luIso X A hWIS n).hom y) h).trans hnatU.symm)
    exact hc
  obtain ⟨c, hcW, hcU⟩ := lu_exists_glue (TopCat.of ↥(W ∪ U)) ((Subtype.val) ⁻¹' A) n hWo hUo hcov
      ((luIso X A hWS n).hom cW) ((luIso X A hUS n).hom cU) hcompat
  refine ⟨c, ?_, ?_⟩
  · have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (luIso_res X A hWS n)) c
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    erw [hcW] at h2
    exact (CategoryTheory.ConcreteCategory.bijective_of_isIso (luIso X A hWS n).hom).1 h2
  · have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (luIso_res X A hUS n)) c
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    erw [hcU] at h2
    exact (CategoryTheory.ConcreteCategory.bijective_of_isIso (luIso X A hUS n).hom).1 h2

/-- **The transfinite union step for relative cohomology, for classes.** -/
theorem coherentExtend {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) (hn : 1 ≤ n)
    {Γ : Type} [LinearOrder Γ] [WellFoundedLT Γ] (V : Γ → Set X)
    (hopen : ∀ γ, IsOpen (V γ)) (hmono : Monotone V)
    (hpiece : ∀ γ : Γ, Subsingleton (pdCohSub (TopCat.of X) A (V γ) (n - 1)))
    (hunion : ∀ γ : Γ, (∃ δ, δ < γ) →
      Subsingleton (pdCohSub (TopCat.of X) A (⋃ δ, ⋃ (_ : δ < γ), V δ) (n - 1)))
    (x : (γ : Γ) → pdCohSub (TopCat.of X) A (V γ) n)
    (hx : ∀ ⦃γ γ' : Γ⦄ (h : γ' ≤ γ),
      (ModuleCat.Hom.hom (pdCohMap (TopCat.of X) A (V γ) (V γ') (hmono h) n)) (x γ) = x γ') :
    ∃! xmax : pdCohSub (TopCat.of X) A (⋃ γ, V γ) n,
      ∀ γ : Γ, (ModuleCat.Hom.hom (pdCohMap (TopCat.of X) A (⋃ γ, V γ) (V γ)
        (Set.subset_iUnion V γ) n)) xmax = x γ := by
  classical
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  subst hm
  let P : Type := Σ γ : Γ, ↥((rcSet A (V γ)).cycles (m + 1))
  let Good : Set P → Prop := fun G =>
    (∀ (γ : Γ) (z z' : ↥((rcSet A (V γ)).cycles (m + 1))),
        (⟨γ, z⟩ : P) ∈ G → (⟨γ, z'⟩ : P) ∈ G → cycCoe z = cycCoe z') ∧
    (∀ (γ : Γ) (z : ↥((rcSet A (V γ)).cycles (m + 1))), (⟨γ, z⟩ : P) ∈ G →
        ∀ γ' : Γ, γ' ≤ γ → ∃ z' : ↥((rcSet A (V γ')).cycles (m + 1)), (⟨γ', z'⟩ : P) ∈ G) ∧
    (∀ (γ γ' : Γ) (h : γ' ≤ γ) (z : ↥((rcSet A (V γ)).cycles (m + 1)))
        (z' : ↥((rcSet A (V γ')).cycles (m + 1))),
        (⟨γ, z⟩ : P) ∈ G → (⟨γ', z'⟩ : P) ∈ G →
        (rcResLM A (hmono h) (m + 1)) (cycCoe z) = cycCoe z') ∧
    (∀ (γ : Γ) (z : ↥((rcSet A (V γ)).cycles (m + 1))), (⟨γ, z⟩ : P) ∈ G →
        ((rcSet A (V γ)).homologyπ (m + 1)) z = x γ)
  have hchain : ∀ c ⊆ {G | Good G}, IsChain (· ⊆ ·) c → ∃ ub ∈ {G | Good G}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hcc
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    have hcmp : ∀ ⦃s t⦄, s ∈ c → t ∈ c → s ⊆ t ∨ t ⊆ s := by
      intro s t hs ht
      rcases eq_or_ne s t with rfl | hne
      · exact Or.inl (Set.Subset.refl _)
      · exact hcc hs ht hne
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro γ z z' hz hz'
      obtain ⟨s, hsc, hzs⟩ := Set.mem_sUnion.mp hz
      obtain ⟨t, htc, hzt⟩ := Set.mem_sUnion.mp hz'
      rcases hcmp hsc htc with hst | hts
      · exact (hc htc).1 γ z z' (hst hzs) hzt
      · exact (hc hsc).1 γ z z' hzs (hts hzt)
    · intro γ z hz γ' hle
      obtain ⟨s, hsc, hzs⟩ := Set.mem_sUnion.mp hz
      obtain ⟨z', hz'⟩ := (hc hsc).2.1 γ z hzs γ' hle
      exact ⟨z', Set.subset_sUnion_of_mem hsc hz'⟩
    · intro γ γ' h z z' hz hz'
      obtain ⟨s, hsc, hzs⟩ := Set.mem_sUnion.mp hz
      obtain ⟨t, htc, hzt⟩ := Set.mem_sUnion.mp hz'
      rcases hcmp hsc htc with hst | hts
      · exact (hc htc).2.2.1 γ γ' h z z' (hst hzs) hzt
      · exact (hc hsc).2.2.1 γ γ' h z z' hzs (hts hzt)
    · intro γ z hz
      obtain ⟨s, hsc, hzs⟩ := Set.mem_sUnion.mp hz
      exact (hc hsc).2.2.2 γ z hzs
  obtain ⟨G₀, hG₀, hG₀max⟩ := zorn_subset {G | Good G} hchain
  have hdom : ∀ γ : Γ, ∃ z : ↥((rcSet A (V γ)).cycles (m + 1)), (⟨γ, z⟩ : P) ∈ G₀ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨γ₀, hγ₀, hγ₀min⟩ := WellFounded.has_min wellFounded_lt
      {γ : Γ | ∀ z : ↥((rcSet A (V γ)).cycles (m + 1)), (⟨γ, z⟩ : P) ∈ G₀ → False} hcon
    have hδ : ∀ δ, δ < γ₀ → ∃ z : ↥((rcSet A (V δ)).cycles (m + 1)), (⟨δ, z⟩ : P) ∈ G₀ := by
      intro δ hδ
      by_contra hh
      exact hγ₀min δ (fun z hz => hh ⟨z, hz⟩) hδ
    let zf : (δ : ↥(Set.Iio γ₀)) → ↥((rcSet A (V (δ : Γ))).cycles (m + 1)) :=
      fun δ => Classical.choose (hδ δ.1 δ.2)
    have hzf : ∀ δ : ↥(Set.Iio γ₀), (⟨(δ : Γ), zf δ⟩ : P) ∈ G₀ :=
      fun δ => Classical.choose_spec (hδ δ.1 δ.2)
    have hzfcomp : ∀ (i j : ↥(Set.Iio γ₀)) (hij : (i : Γ) ≤ j),
        (rcResLM A (hmono hij) (m + 1)) (cycCoe (zf j)) = cycCoe (zf i) :=
      fun i j hij => hG₀.2.2.1 j.1 i.1 hij (zf j) (zf i) (hzf j) (hzf i)
    have hzfcl : ∀ δ : ↥(Set.Iio γ₀),
        ((rcSet A (V (δ : Γ))).homologyπ (m + 1)) (zf δ) = x (δ : Γ) :=
      fun δ => hG₀.2.2.2 δ.1 (zf δ) (hzf δ)
    obtain ⟨g, hg, -⟩ := (rcKern_iUnion_limit A (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ))
      (fun δ => hopen δ.1) (fun a b hab => hmono hab) (m + 1) (fun δ => cycCoe (zf δ))).mpr hzfcomp
    have hgcl : rcDiff A (⋃ δ : ↥(Set.Iio γ₀), V (δ : Γ)) (m + 1) g = 0 := by
      apply rcRestrict_injective A (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ))
        (fun δ => hopen δ.1) (fun a b hab => hmono hab) (m + 2)
      intro δ
      rw [rcResLM_comm A (Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ)) δ) (m + 1) g,
        hg δ, rcDiff_cycCoe]
    obtain ⟨z₀, hz₀⟩ := Work.Thom.rcSet_exists_cycle A (V γ₀) m (x γ₀)
    have hUsub : (⋃ δ : ↥(Set.Iio γ₀), V (δ : Γ)) ⊆ V γ₀ := by
      intro y hy
      obtain ⟨δ, hyδ⟩ := Set.mem_iUnion.mp hy
      exact hmono (le_of_lt δ.2) hyδ
    let d : ↥(rcKern A (⋃ δ : ↥(Set.Iio γ₀), V (δ : Γ)) (m + 1)) :=
      rcResLM A hUsub (m + 1) (cycCoe z₀) - g
    have hd : rcDiff A (⋃ δ : ↥(Set.Iio γ₀), V (δ : Γ)) (m + 1) d = 0 := by
      show rcDiff A (⋃ δ : ↥(Set.Iio γ₀), V (δ : Γ)) (m + 1)
        (rcResLM A hUsub (m + 1) (cycCoe z₀) - g) = 0
      rw [map_sub, ← rcResLM_comm A hUsub (m + 1) (cycCoe z₀), rcDiff_cycCoe, map_zero, hgcl,
        sub_zero]
    have hprim : ∀ δ : ↥(Set.Iio γ₀), ∃ w : ↥(rcKern A (V (δ : Γ)) m),
        rcDiff A (V (δ : Γ)) m w =
          rcResLM A (Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ)) δ) (m + 1) d := by
      intro δ
      have hcoe : cycCoe (HomologicalComplex.cyclesMap (rcRes A
            ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ)) δ).trans hUsub)) (m + 1) z₀
            - zf δ)
          = rcResLM A (Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ)) δ) (m + 1) d := by
        rw [cycCoe_sub, cycCoe_cyclesMap]
        show rcResLM A ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ)) δ).trans hUsub)
              (m + 1) (cycCoe z₀) - cycCoe (zf δ) = rcResLM A (Set.subset_iUnion
              (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ)) δ) (m + 1)
              (rcResLM A hUsub (m + 1) (cycCoe z₀) - g)
        rw [map_sub, rcResLM_trans A (Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ)) δ)
          hUsub (m + 1) (cycCoe z₀), hg δ]
      have hzero : ((rcSet A (V (δ : Γ))).homologyπ (m + 1))
          (HomologicalComplex.cyclesMap (rcRes A
            ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ)) δ).trans hUsub)) (m + 1) z₀
            - zf δ) = 0 := by
        rw [map_sub, homologyπ_cyclesMap, hz₀, hzfcl δ]
        show ((HomologicalComplex.homologyMap (rcRes A
            ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ)) δ).trans hUsub)) (m + 1)).hom)
            (x γ₀) - x (δ : Γ) = 0
        rw [show (HomologicalComplex.homologyMap (rcRes A
              ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ)) δ).trans hUsub)) (m + 1))
            = pdCohMap (TopCat.of X) A (V γ₀) (V (δ : Γ)) (hmono (le_of_lt δ.2)) (m + 1)
            from rfl, hx (le_of_lt δ.2), sub_self]
      obtain ⟨w, hw⟩ := Work.Thom.rcSet_exists_primitive_of_homologyπ_eq_zero A (V (δ : Γ)) m
        (HomologicalComplex.cyclesMap (rcRes A
          ((Set.subset_iUnion (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ)) δ).trans hUsub)) (m + 1) z₀
          - zf δ) hzero
      exact ⟨w, hw.trans hcoe⟩
    have hvan : ∀ γ : ↥(Set.Iio γ₀), (∃ δ : ↥(Set.Iio γ₀), δ < γ) →
        Subsingleton ((rcSet A (⋃ δ : ↥(Set.Iio γ₀), ⋃ (_ : (δ : Γ) < (γ : Γ)),
          V (δ : Γ))).homology m) := by
      intro γ hγ
      have hγ' : ∃ δ : Γ, δ < (γ : Γ) := ⟨hγ.choose.1, hγ.choose_spec⟩
      exact (iUnion_Iio_initial V γ.2) ▸ hunion γ.1 hγ'
    obtain ⟨W, hW⟩ := Work.Thom.rcPrimitive_of_piece_primitives_union_vanishing A
      (fun δ : ↥(Set.Iio γ₀) => V (δ : Γ)) (fun δ => hopen δ.1)
      (fun a b hab => hmono hab) m hvan d hd hprim
    obtain ⟨W', hW'⟩ := rcResLM_surjective A hUsub m W
    let znew : ↥((rcSet A (V γ₀)).cycles (m + 1)) :=
      z₀ - (rcSet A (V γ₀)).toCycles m (m + 1) W'
    have hznewrestr : rcResLM A hUsub (m + 1) (cycCoe znew) = g := by
      show rcResLM A hUsub (m + 1) (cycCoe (z₀ - (rcSet A (V γ₀)).toCycles m (m + 1) W')) = g
      rw [cycCoe_sub, cycCoe_toCycles, map_sub, rcResLM_comm A hUsub m W', hW', hW]
      show rcResLM A hUsub (m + 1) (cycCoe z₀)
        - (rcResLM A hUsub (m + 1) (cycCoe z₀) - g) = g
      abel
    have hznewclass : ((rcSet A (V γ₀)).homologyπ (m + 1)) znew = x γ₀ := by
      show ((rcSet A (V γ₀)).homologyπ (m + 1))
        (z₀ - (rcSet A (V γ₀)).toCycles m (m + 1) W') = x γ₀
      rw [map_sub, homologyπ_toCycles, sub_zero, hz₀]
    have hext : Good (G₀ ∪ {(⟨γ₀, znew⟩ : P)}) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro γ z z' hz hz'
        rcases hz with hz | hz
        · rcases hz' with hz' | hz'
          · exact hG₀.1 γ z z' hz hz'
          · simp only [Set.mem_singleton_iff] at hz'
            obtain ⟨hγ, -⟩ := (Sigma.mk.injEq ..).mp hz'
            cases hγ
            exact absurd hz (hγ₀ z)
        · simp only [Set.mem_singleton_iff] at hz
          obtain ⟨hγ, hzeq⟩ := (Sigma.mk.injEq ..).mp hz
          cases hγ
          rcases hz' with hz' | hz'
          · exact absurd hz' (hγ₀ z')
          · simp only [Set.mem_singleton_iff] at hz'
            obtain ⟨-, hz'eq⟩ := (Sigma.mk.injEq ..).mp hz'
            exact congrArg cycCoe (eq_of_heq (hzeq.trans hz'eq.symm))
      · intro γ z hz γ' hle
        rcases hz with hz | hz
        · obtain ⟨z', hz'⟩ := hG₀.2.1 γ z hz γ' hle
          exact ⟨z', Or.inl hz'⟩
        · simp only [Set.mem_singleton_iff] at hz
          obtain ⟨hγ, -⟩ := (Sigma.mk.injEq ..).mp hz
          cases hγ
          rcases lt_or_eq_of_le hle with hlt | heq
          · exact ⟨zf ⟨γ', hlt⟩, Or.inl (hzf ⟨γ', hlt⟩)⟩
          · cases heq
            exact ⟨znew, Or.inr (Set.mem_singleton _)⟩
      · intro γ γ' h z z' hz hz'
        rcases hz with hz | hz
        · rcases hz' with hz' | hz'
          · exact hG₀.2.2.1 γ γ' h z z' hz hz'
          · simp only [Set.mem_singleton_iff] at hz'
            obtain ⟨hγ', -⟩ := (Sigma.mk.injEq ..).mp hz'
            cases hγ'
            obtain ⟨z'', hz''⟩ := hG₀.2.1 γ z hz γ₀ h
            exact absurd hz'' (hγ₀ z'')
        · simp only [Set.mem_singleton_iff] at hz
          obtain ⟨hγ, hzeq⟩ := (Sigma.mk.injEq ..).mp hz
          cases hγ
          rcases hz' with hz' | hz'
          · rcases lt_or_eq_of_le h with hlt | heq
            · have hsub : V γ' ⊆ (⋃ δ : ↥(Set.Iio γ₀), V (δ : Γ)) := fun x hx =>
                Set.mem_iUnion.mpr ⟨(⟨γ', hlt⟩ : ↥(Set.Iio γ₀)), hx⟩
              have hz'coe : cycCoe z' = cycCoe (zf ⟨γ', hlt⟩) :=
                hG₀.1 γ' z' (zf ⟨γ', hlt⟩) hz' (hzf ⟨γ', hlt⟩)
              rw [eq_of_heq hzeq,
                show rcResLM A (hmono h) (m + 1) = rcResLM A (hsub.trans hUsub) (m + 1)
                  from rcResLM_proof_irrel (hmono h) (hsub.trans hUsub) (m + 1),
                rcResLM_trans A hsub hUsub (m + 1) (cycCoe znew), hznewrestr, hg ⟨γ', hlt⟩,
                hz'coe]
            · cases heq
              exact absurd hz' (hγ₀ z')
          · simp only [Set.mem_singleton_iff] at hz'
            obtain ⟨hγ', hz'eq⟩ := (Sigma.mk.injEq ..).mp hz'
            cases hγ'
            rw [eq_of_heq hzeq, eq_of_heq hz'eq]
            exact rcResLM_self A (hmono h) (m + 1) (cycCoe znew)
      · intro γ z hz
        rcases hz with hz | hz
        · exact hG₀.2.2.2 γ z hz
        · simp only [Set.mem_singleton_iff] at hz
          obtain ⟨hγ, hzeq⟩ := (Sigma.mk.injEq ..).mp hz
          cases hγ
          rw [eq_of_heq hzeq]
          exact hznewclass
    have hle : G₀ ⊆ G₀ ∪ {(⟨γ₀, znew⟩ : P)} := Set.subset_union_left
    have hsub : G₀ ∪ {(⟨γ₀, znew⟩ : P)} ⊆ G₀ := hG₀max hext hle
    exact hγ₀ znew (hsub (Or.inr (Set.mem_singleton _)))
  have hzf : ∀ γ : Γ, (⟨γ, Classical.choose (hdom γ)⟩ : P) ∈ G₀ :=
    fun γ => Classical.choose_spec (hdom γ)
  have hzfcomp : ∀ (i j : Γ) (hij : i ≤ j),
      (rcResLM A (hmono hij) (m + 1)) (cycCoe (Classical.choose (hdom j)))
        = cycCoe (Classical.choose (hdom i)) :=
    fun i j hij => hG₀.2.2.1 j i hij _ _ (hzf j) (hzf i)
  have hzfcl : ∀ γ : Γ,
      ((rcSet A (V γ)).homologyπ (m + 1)) (Classical.choose (hdom γ)) = x γ :=
    fun γ => hG₀.2.2.2 γ _ (hzf γ)
  obtain ⟨zg, hzg, -⟩ := (rcKern_iUnion_limit A V hopen hmono (m + 1)
    (fun γ => cycCoe (Classical.choose (hdom γ)))).mpr hzfcomp
  have hzgcl : rcDiff A (⋃ γ, V γ) (m + 1) zg = 0 := by
    apply rcRestrict_injective A V hopen hmono (m + 2)
    intro γ
    rw [rcResLM_comm A (Set.subset_iUnion V γ) (m + 1) zg, hzg γ, rcDiff_cycCoe]
  refine ⟨((rcSet A (⋃ γ, V γ)).homologyπ (m + 1)) (cycOf zg hzgcl), ?_, ?_⟩
  · intro γ
    show ((HomologicalComplex.homologyMap (rcRes A (Set.subset_iUnion V γ)) (m + 1)).hom)
      (((rcSet A (⋃ γ, V γ)).homologyπ (m + 1)) (cycOf zg hzgcl)) = x γ
    rw [← homologyπ_cyclesMap]
    have hcm : HomologicalComplex.cyclesMap (rcRes A (Set.subset_iUnion V γ)) (m + 1)
        (cycOf zg hzgcl) = Classical.choose (hdom γ) := by
      apply cycles_ext
      rw [cycCoe_cyclesMap, iCycles_cycOf, hzg γ]
    rw [hcm, hzfcl γ]
  · intro y hy
    obtain ⟨zy, hzy⟩ := Work.Thom.rcSet_exists_cycle A (⋃ γ, V γ) m y
    have hdiff : ((rcSet A (⋃ γ, V γ)).homologyπ (m + 1))
        (zy - cycOf zg hzgcl) = 0 := by
      have hprim : ∀ γ : Γ, ∃ w : ↥(rcKern A (V γ) m),
          rcDiff A (V γ) m w
            = rcResLM A (Set.subset_iUnion V γ) (m + 1) (cycCoe (zy - cycOf zg hzgcl)) := by
        intro γ
        have hzero : ((rcSet A (V γ)).homologyπ (m + 1))
            (HomologicalComplex.cyclesMap (rcRes A (Set.subset_iUnion V γ)) (m + 1)
              (zy - cycOf zg hzgcl)) = 0 := by
          rw [homologyπ_cyclesMap, map_sub, map_sub, hzy, ← homologyπ_cyclesMap]
          have hcm : HomologicalComplex.cyclesMap (rcRes A (Set.subset_iUnion V γ)) (m + 1)
              (cycOf zg hzgcl) = Classical.choose (hdom γ) := by
            apply cycles_ext
            rw [cycCoe_cyclesMap, iCycles_cycOf, hzg γ]
          rw [hcm, hzfcl γ]
          show (ModuleCat.Hom.hom (pdCohMap (TopCat.of X) A (⋃ γ, V γ) (V γ)
            (Set.subset_iUnion V γ) (m + 1))) y - x γ = 0
          rw [hy γ, sub_self]
        obtain ⟨w, hw⟩ := Work.Thom.rcSet_exists_primitive_of_homologyπ_eq_zero A (V γ) m _
          hzero
        exact ⟨w, hw.trans (cycCoe_cyclesMap (Set.subset_iUnion V γ) (zy - cycOf zg hzgcl))⟩
      obtain ⟨wg, hwg⟩ := Work.Thom.rcPrimitive_of_piece_primitives_union_vanishing A V hopen hmono
        m (fun γ hγ => hunion γ hγ) (cycCoe (zy - cycOf zg hzgcl))
        (rcDiff_cycCoe (zy - cycOf zg hzgcl)) hprim
      exact Work.Thom.rcSet_homologyπ_eq_zero_of_exists_primitive A (⋃ γ, V γ) m _
        ⟨wg, hwg⟩
    have hsub : ((rcSet A (⋃ γ, V γ)).homologyπ (m + 1)) zy
        - ((rcSet A (⋃ γ, V γ)).homologyπ (m + 1)) (cycOf zg hzgcl) = 0 := by
      rw [← LinearMap.map_sub]
      exact hdiff
    have heq : ((rcSet A (⋃ γ, V γ)).homologyπ (m + 1)) zy
        = ((rcSet A (⋃ γ, V γ)).homologyπ (m + 1)) (cycOf zg hzgcl) := sub_eq_zero.mp hsub
    rw [← hzy, heq]

/-! ## Uniqueness of the extension over a well-ordered union -/

/-- **The uniqueness half of the transfinite union step.**  A class of the Thom pair over an
increasing well-ordered union of open sets whose restriction to every piece vanishes is zero. -/
theorem vanish_of_pieces {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) (hn : 1 ≤ n)
    {Γ : Type} [LinearOrder Γ] [WellFoundedLT Γ] (V : Γ → Set X)
    (hopen : ∀ γ, IsOpen (V γ)) (hmono : Monotone V)
    (hpiece : ∀ γ : Γ, Subsingleton (pdCohSub (TopCat.of X) A (V γ) (n - 1)))
    (hunion : ∀ γ : Γ, (∃ δ, δ < γ) →
      Subsingleton (pdCohSub (TopCat.of X) A (⋃ δ : ↥(Set.Iio γ), V (δ : Γ)) (n - 1)))
    (y : pdCohSub (TopCat.of X) A (⋃ γ, V γ) n)
    (hy : ∀ γ : Γ, (ModuleCat.Hom.hom (pdCohMap (TopCat.of X) A (⋃ γ, V γ) (V γ)
        (Set.subset_iUnion V γ) n)) y = 0) : y = 0 := by
  obtain ⟨xmax, -, huniq⟩ := coherentExtend A n hn V hopen hmono hpiece
    (fun γ hγ => by
      rw [← iUnion_Iio_eq V γ]
      exact hunion γ hγ)
    (x := fun _ => 0) (hx := fun γ γ' h => by simp)
  rw [huniq y hy, ← huniq 0 (fun γ => by simp)]

/-! ## Transport of restrictions -/

/-- The restriction map does not depend on the proof of the inclusion. -/
theorem pdCohMap_proof_irrel (X : TopCat) (A : Set X) {U W : Set X} (h h' : W ⊆ U) (k : ℕ) :
    pdCohMap X A U W h k = pdCohMap X A U W h' k := by
  show HomologicalComplex.homologyMap (rcRes A h) k
    = HomologicalComplex.homologyMap (rcRes A h') k
  have hrc : rcRes A h = rcRes A h' := by
    apply HomologicalComplex.hom_ext
    intro m
    show ModuleCat.ofHom (rcResLM A h m) = ModuleCat.ofHom (rcResLM A h' m)
    rw [rcResLM_proof_irrel h h' m]
  rw [hrc]

/-- The element form of `pdCohMap_proof_irrel`. -/
theorem pdCohMap_congr (X : TopCat) (A : Set X) {U W : Set X} (h h' : W ⊆ U) (k : ℕ)
    (x : pdCohSub X A U k) :
    (ModuleCat.Hom.hom (pdCohMap X A U W h k)) x
      = (ModuleCat.Hom.hom (pdCohMap X A U W h' k)) x := by
  rw [pdCohMap_proof_irrel X A h h' k]

/-- Restricting after transporting the *target* of the restriction along an equality of sets. -/
theorem pdCohMap_dcast_target_cast (X : TopCat) (A : Set X) {U W W' : Set X} (h : W = W')
    (hWU : W ⊆ U) (k : ℕ) (x : pdCohSub X A U k) :
    h ▸ ((ModuleCat.Hom.hom (pdCohMap X A U W hWU k)) x)
      = (ModuleCat.Hom.hom (pdCohMap X A U W' (h ▸ hWU) k)) x := by
  cases h
  rfl

/-- Transporting zero along an equality of pieces. -/
theorem dcast_zero {X : TopCat} {A S S' : Set X} {k : ℕ} (h : S = S') :
    h ▸ (0 : pdCohSub X A S k) = (0 : pdCohSub X A S' k) := by
  cases h
  rfl

/-- Restricting after transporting the *source* of the restriction along an equality of sets. -/
theorem pdCohMap_dcast_source_cast (X : TopCat) (A : Set X) {S S' W : Set X} (h : S = S')
    (hWS : W ⊆ S) (k : ℕ) (x : pdCohSub X A S' k) :
    (ModuleCat.Hom.hom (pdCohMap X A S' W (h ▸ hWS) k)) x
      = (ModuleCat.Hom.hom (pdCohMap X A S W hWS k)) (h.symm ▸ x) := by
  cases h
  rfl

/-- `Subsingleton` of a relative cohomology module transports along an equality of the piece. -/
theorem subsingleton_pdCohSub_cast {X : TopCat} {A : Set X} {S S' : Set X} {k : ℕ} (h : S = S')
    (hs : Subsingleton (pdCohSub X A S k)) : Subsingleton (pdCohSub X A S' k) := h ▸ hs

/-- Functoriality of the restriction, in element form. -/
theorem pdCohMap_comp_apply' (X : TopCat) (A : Set X) {V U W : Set X} (hVU : V ⊆ U)
    (hUW : U ⊆ W) (k : ℕ) (x : pdCohSub X A W k) :
    (ModuleCat.Hom.hom (pdCohMap X A U V hVU k))
        ((ModuleCat.Hom.hom (pdCohMap X A W U hUW k)) x)
      = (ModuleCat.Hom.hom (pdCohMap X A W V (hVU.trans hUW) k)) x := by
  rw [← ModuleCat.comp_apply, ← Work.Thom.pdCohMap_comp X A hVU hUW k]

/-! ## The cumulative pieces of a well-ordered family -/

/-- The cumulative union `⋃_{β ≤ γ} P β` is the union of the initial part and the last piece. -/
theorem cumulative_eq_union {ι : Type} [LinearOrder ι] {B : Type} (P : ι → Set B) (γ : ι) :
    (⋃ β, ⋃ (_ : β ≤ γ), P β) = (⋃ δ, ⋃ (_ : δ < γ), P δ) ∪ P γ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨β, hβ, hx⟩
    rcases lt_or_eq_of_le hβ with hlt | heq
    · exact Or.inl ⟨β, hlt, hx⟩
    · exact Or.inr (heq ▸ hx)
  · rintro (⟨δ, hδ, hx⟩ | hx)
    · exact ⟨δ, le_of_lt hδ, hx⟩
    · exact ⟨γ, le_rfl, hx⟩

/-- The cumulative union over a subtype is the union of the pieces of the subtype. -/
theorem cumulative_iUnion_Iio {ι : Type} [LinearOrder ι] {B : Type} (P : ι → Set B) (γ : ι) :
    (⋃ δ : ↥(Set.Iio γ), ⋃ β, ⋃ (_ : β ≤ (δ : ι)), P β)
      = ⋃ δ : ↥(Set.Iio γ), P (δ : ι) := by
  ext x
  constructor
  · intro hx
    obtain ⟨δ, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨β, h⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hβδ, hx⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨⟨β, lt_of_le_of_lt hβδ δ.2⟩, hx⟩
  · intro hx
    obtain ⟨δ, hx⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨δ, Set.mem_iUnion.mpr ⟨δ, Set.mem_iUnion.mpr ⟨le_rfl, hx⟩⟩⟩

/-- The union over the pieces below `γ` is the union over the subtype of the indices below `γ`. -/
theorem iUnion_Iio_collapse {Γ : Type} [LinearOrder Γ] {B : Type} (V : Γ → Set B) (γ : Γ) :
    (⋃ δ : Γ, ⋃ (_ : δ < γ), V δ) = ⋃ δ : ↥(Set.Iio γ), V (δ : Γ) := by
  ext z
  constructor
  · intro hz
    obtain ⟨δ, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hδ, hz⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨⟨δ, hδ⟩, hz⟩
  · intro hz
    obtain ⟨δ, hz⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨(δ : Γ), Set.mem_iUnion.mpr ⟨δ.2, hz⟩⟩

/-- The union of preimages of a family of pieces. -/
theorem iUnion_preimage {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) {κ : Type} (Q : κ → Set B) :
    (⋃ i, Z.proj ⁻¹' (Q i)) = Z.proj ⁻¹' (⋃ i, Q i) := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hz⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_preimage.mpr (Set.mem_iUnion.mpr ⟨i, Set.mem_preimage.mp hz⟩)
  · intro hz
    obtain ⟨i, hz⟩ := Set.mem_iUnion.mp (Set.mem_preimage.mp hz)
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_preimage.mpr hz⟩

/-- The union of preimages of the pieces `P i ∩ W₀`. -/
theorem iUnion_preimage_inter {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) {κ : Type} (Q : κ → Set B)
    (W₀ : Set B) : (⋃ i, Z.proj ⁻¹' (Q i ∩ W₀)) = Z.proj ⁻¹' ((⋃ i, Q i) ∩ W₀) := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨h1, h2⟩ := (Set.mem_preimage.mp hz : Z.proj z ∈ Q i ∧ Z.proj z ∈ W₀)
    exact Set.mem_preimage.mpr (⟨Set.mem_iUnion.mpr ⟨i, h1⟩, h2⟩ : Z.proj z ∈ (⋃ i, Q i) ∧ Z.proj z ∈ W₀)
  · intro hz
    obtain ⟨h1, h2⟩ := (Set.mem_preimage.mp hz : Z.proj z ∈ (⋃ i, Q i) ∧ Z.proj z ∈ W₀)
    obtain ⟨i, h1⟩ := Set.mem_iUnion.mp h1
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_preimage.mpr (⟨h1, h2⟩ : Z.proj z ∈ Q i ∧ Z.proj z ∈ W₀)⟩

/-! ## Separation for an open cover -/

/-- **Separation for an open cover of a piece.**  If `P : κ → Set B` is a well-ordered family of
open sets covering `W₀` and a class of the Thom pair over `W₀` restricts to zero on every
`P i ∩ W₀`, then it is zero. -/
theorem sep_of_cover {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    (hlow : ∀ W : Set B, Subsingleton (Work.Thom.PieceCoh Z W (n - 1)))
    {κ : Type} [LinearOrder κ] [WellFoundedLT κ] (P : κ → Set B) (hPopen : ∀ i, IsOpen (P i))
    {W₀ : Set B} (hW₀ : IsOpen W₀) (hcov : W₀ ⊆ ⋃ i, P i)
    (y : Work.Thom.PieceCoh Z W₀ n)
    (hy : ∀ i : κ, (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' W₀) (Z.proj ⁻¹' (P i ∩ W₀))
        (Set.preimage_mono Set.inter_subset_right) n)) y = 0) :
    y = 0 := by
  classical
  let Q : κ → Set B := fun γ => ⋃ β, ⋃ (_ : β ≤ γ), P β
  have hQopen : ∀ γ, IsOpen (Q γ) := fun γ =>
    isOpen_iUnion fun β => isOpen_iUnion fun _ : β ≤ γ => hPopen β
  have hQmono : Monotone Q := by
    intro a b hab z hz
    obtain ⟨β, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hβ, hz⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨β, Set.mem_iUnion.mpr ⟨le_trans hβ hab, hz⟩⟩
  have hVopen : ∀ γ : κ, IsOpen (Z.proj ⁻¹' (Q γ ∩ W₀)) :=
    fun γ => ((hQopen γ).inter hW₀).preimage Z.continuous_proj
  have hVM : Monotone (fun γ : κ => Z.proj ⁻¹' (Q γ ∩ W₀)) := by
    intro a b hab
    exact Set.preimage_mono (Set.inter_subset_inter (hQmono hab) (fun x hx => hx))
  have key : ∀ γ : κ, (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' W₀) (Z.proj ⁻¹' (Q γ ∩ W₀))
      (Set.preimage_mono Set.inter_subset_right) n)) y = 0 := by
    intro γ
    refine WellFoundedLT.induction (motive := fun γ : κ => (ModuleCat.Hom.hom (pdCohMap
      (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' W₀)
      (Z.proj ⁻¹' (Q γ ∩ W₀)) (Set.preimage_mono Set.inter_subset_right) n)) y = 0) γ ?_
    intro γ ih
    have hWQ0 : (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : κ) ∩ W₀)) ⊆ Z.proj ⁻¹' W₀ :=
      Set.iUnion_subset fun δ => Set.preimage_mono Set.inter_subset_right
    have step1 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' W₀)
        (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : κ) ∩ W₀)) hWQ0 n)) y = 0 := by
      by_cases hpred : ∃ δ : κ, δ < γ
      · have hmono : Monotone (fun δ : ↥(Set.Iio γ) => Z.proj ⁻¹' (Q (δ : κ) ∩ W₀)) := by
          intro a b hab
          exact Set.preimage_mono (Set.inter_subset_inter (hQmono hab) (fun x hx => hx))
        have hopen : ∀ δ : ↥(Set.Iio γ), IsOpen (Z.proj ⁻¹' (Q (δ : κ) ∩ W₀)) :=
          fun δ => hVopen (δ : κ)
        have hpI : ∀ δ : ↥(Set.Iio γ), Subsingleton (pdCohSub (TopCat.of Z.TotalSpace)
            (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Q (δ : κ) ∩ W₀)) (n - 1)) :=
          fun δ => hlow _
        have hUn : ∀ δ : ↥(Set.Iio γ), (∃ ε : ↥(Set.Iio γ), ε < δ) →
            Subsingleton (pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
              (⋃ ε : ↥(Set.Iio δ), Z.proj ⁻¹' (Q (ε.1.1) ∩ W₀))
              (n - 1)) := by
          intro δ _
          exact (iUnion_preimage_inter Z (fun ε : ↥(Set.Iio δ) => Q (ε.1.1)) W₀) ▸
            hlow ((⋃ ε : ↥(Set.Iio δ), Q (ε.1.1)) ∩ W₀)
        refine vanish_of_pieces (Work.Thom.zeroComplement Z) n hn
          (fun δ : ↥(Set.Iio γ) => Z.proj ⁻¹' (Q (δ : κ) ∩ W₀)) hopen hmono hpI hUn _ ?_
        intro δ
        have h1 : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
            (Work.Thom.zeroComplement Z)
            (⋃ δ' : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ' : κ) ∩ W₀))
            (Z.proj ⁻¹' (Q (δ : κ) ∩ W₀))
            (Set.subset_iUnion (fun δ' : ↥(Set.Iio γ) => Z.proj ⁻¹' (Q (δ' : κ) ∩ W₀)) δ) n))
              ((ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
                (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' W₀)
                (⋃ δ' : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ' : κ) ∩ W₀)) hWQ0 n)) y)
            = (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
                (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' W₀)
                (Z.proj ⁻¹' (Q (δ : κ) ∩ W₀))
                (Set.preimage_mono Set.inter_subset_right) n)) y := by
          rw [pdCohMap_comp_apply' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (Set.subset_iUnion (fun δ' : ↥(Set.Iio γ) => Z.proj ⁻¹' (Q (δ' : κ) ∩ W₀)) δ)
            hWQ0 n y]
        rw [h1]
        exact ih (δ : κ) δ.2
      · -- there is no piece below `γ`
        have hempty : (⋃ δ : ↥(Set.Iio γ), Q (δ : κ)) = (∅ : Set B) := by
          apply Set.Subset.antisymm
          · intro z hz
            obtain ⟨δ, hz⟩ := Set.mem_iUnion.mp hz
            obtain ⟨β, hz⟩ := Set.mem_iUnion.mp hz
            obtain ⟨hβδ, -⟩ := Set.mem_iUnion.mp hz
            exact hpred ⟨β, lt_of_le_of_lt hβδ δ.2⟩
          · exact Set.empty_subset _
        have hpiece : Subsingleton (Work.Thom.PieceCoh Z
            ((⋃ δ : ↥(Set.Iio γ), Q (δ : κ)) ∩ W₀) n) :=
          Work.Thom.subsingleton_PieceCoh_of_isEmpty Z n
            ⟨fun x => by
              have hx : (x : B) ∈ (⋃ δ : ↥(Set.Iio γ), Q (δ : κ)) :=
                ((Set.mem_inter_iff (x : B) (⋃ δ : ↥(Set.Iio γ), Q (δ : κ)) W₀).mp x.2).1
              obtain ⟨δ, hz⟩ := Set.mem_iUnion.mp hx
              obtain ⟨β, hz⟩ := Set.mem_iUnion.mp hz
              obtain ⟨hβδ, -⟩ := Set.mem_iUnion.mp hz
              exact hpred ⟨β, lt_of_le_of_lt hβδ δ.2⟩⟩
        haveI : Subsingleton (pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
            (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : κ) ∩ W₀)) n) :=
          subsingleton_pdCohSub_cast
            (iUnion_preimage_inter Z (fun δ : ↥(Set.Iio γ) => Q (δ : κ)) W₀).symm hpiece
        exact Subsingleton.elim _ _
    have hlast : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' W₀) (Z.proj ⁻¹' (P γ ∩ W₀))
        (Set.preimage_mono Set.inter_subset_right) n)) y = 0 := hy γ
    -- glue the initial part and the last piece
    have hQeq : Q γ = (⋃ δ : ↥(Set.Iio γ), Q (δ : κ)) ∪ P γ := by
      rw [show (⋃ δ : ↥(Set.Iio γ), Q (δ : κ)) = ⋃ δ, ⋃ (_ : δ < γ), P δ from
        (cumulative_iUnion_Iio P γ).trans (iUnion_Iio_eq P γ)]
      rw [← cumulative_eq_union P γ]
    have hUeq : (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : κ) ∩ W₀))
        = Z.proj ⁻¹' ((⋃ δ : ↥(Set.Iio γ), Q (δ : κ)) ∩ W₀) :=
      iUnion_preimage_inter Z (fun δ : ↥(Set.Iio γ) => Q (δ : κ)) W₀
    have hWQ' : Z.proj ⁻¹' (Q γ ∩ W₀) ⊆ Z.proj ⁻¹' W₀ :=
      Set.preimage_mono Set.inter_subset_right
    have hcov2 : (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : κ) ∩ W₀))
        ∪ Z.proj ⁻¹' (P γ ∩ W₀) = Z.proj ⁻¹' (Q γ ∩ W₀) := by
      rw [hUeq, ← Set.preimage_union, ← Set.union_inter_distrib_right, ← hQeq]
    have hsub2 : Subsingleton (pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        ((⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : κ) ∩ W₀))
          ∩ Z.proj ⁻¹' (P γ ∩ W₀)) (n - 1)) := by
      refine subsingleton_pdCohSub_cast ?_ (hlow (((⋃ δ : ↥(Set.Iio γ), Q (δ : κ)) ∩ P γ) ∩ W₀))
      rw [hUeq, ← Set.preimage_inter]
      congr 1
      ext z
      simp only [Set.mem_inter_iff]
      tauto
    have hUo : IsOpen (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : κ) ∩ W₀)) :=
      isOpen_iUnion fun δ => hVopen (δ : κ)
    have hVo : IsOpen (Z.proj ⁻¹' (P γ ∩ W₀)) :=
      ((hPopen γ).inter hW₀).preimage Z.continuous_proj
    have hUW : (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : κ) ∩ W₀)) ⊆ Z.proj ⁻¹' (Q γ ∩ W₀) := by
      rw [hUeq]
      exact Set.preimage_mono (Set.inter_subset_inter
        (Set.iUnion_subset fun δ => hQmono (le_of_lt (δ.2))) (fun x hx => hx))
    have hPQ : P γ ⊆ Q γ := fun x hx => by
      have h1 : x ∈ ⋃ (_ : γ ≤ γ), P γ := Set.mem_iUnion.mpr ⟨le_rfl, hx⟩
      show x ∈ ⋃ β, ⋃ (_ : β ≤ γ), P β
      exact Set.mem_iUnion.mpr ⟨γ, h1⟩
    have hVW : Z.proj ⁻¹' (P γ ∩ W₀) ⊆ Z.proj ⁻¹' (Q γ ∩ W₀) :=
      Set.preimage_mono (Set.inter_subset_inter hPQ (fun x hx => hx))
    have hinj := Work.Thom.pdCohSub_pdCohMap_biprod_injective
      (X := TopCat.of Z.TotalSpace) (A := Work.Thom.zeroComplement Z)
      (W := Z.proj ⁻¹' (Q γ ∩ W₀))
      (U := ⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : κ) ∩ W₀))
      (V := Z.proj ⁻¹' (P γ ∩ W₀)) hUo hVo hUW hVW hcov2 n hsub2
    set y0 : pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Q γ ∩ W₀)) n :=
      (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' W₀) (Z.proj ⁻¹' (Q γ ∩ W₀)) hWQ' n)) y with hy0def
    have hf : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Q γ ∩ W₀))
        (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : κ) ∩ W₀)) hUW n)) y0 = 0 := by
      rw [hy0def]
      rw [pdCohMap_comp_apply' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) hUW hWQ' n y]
      rw [pdCohMap_congr (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (hUW.trans hWQ') hWQ0 n y]
      exact step1
    have hg : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Q γ ∩ W₀))
        (Z.proj ⁻¹' (P γ ∩ W₀)) hVW n)) y0 = 0 := by
      rw [hy0def]
      rw [pdCohMap_comp_apply' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z) hVW hWQ' n y]
      rw [pdCohMap_congr (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (hVW.trans hWQ') (Set.preimage_mono Set.inter_subset_right) n y]
      exact hlast
    have hpair : ((ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' (Q γ ∩ W₀))
        (⋃ δ : ↥(Set.Iio γ), Z.proj ⁻¹' (Q (δ : κ) ∩ W₀)) hUW n)) y0,
        (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Z.proj ⁻¹' (Q γ ∩ W₀)) (Z.proj ⁻¹' (P γ ∩ W₀)) hVW n)) y0) = (0, 0) := by
      rw [hf, hg]
    exact hinj (hpair.trans (by simp only [map_zero]))
  -- the whole of `W₀` is covered
  have hWcov : W₀ ⊆ ⋃ γ : κ, Q γ := by
    refine hcov.trans (Set.iUnion_subset fun γ => ?_)
    intro z hz
    refine Set.mem_iUnion.mpr ⟨γ, ?_⟩
    have h1 : z ∈ ⋃ (_ : γ ≤ γ), P γ := Set.mem_iUnion.mpr ⟨le_rfl, hz⟩
    show z ∈ ⋃ β, ⋃ (_ : β ≤ γ), P β
    exact Set.mem_iUnion.mpr ⟨γ, h1⟩
  have hstep : (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
      (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' W₀)
      (⋃ γ : κ, Z.proj ⁻¹' (Q γ ∩ W₀)) (Set.iUnion_subset fun γ => Set.preimage_mono
        Set.inter_subset_right) n)) y = 0 := by
    refine vanish_of_pieces (Work.Thom.zeroComplement Z) n hn
      (fun γ : κ => Z.proj ⁻¹' (Q γ ∩ W₀)) hVopen hVM (fun γ => hlow _) ?_ _ ?_
    · intro γ _
      exact (iUnion_preimage_inter Z (fun δ : ↥(Set.Iio γ) => Q (δ : κ)) W₀) ▸
        hlow ((⋃ δ : ↥(Set.Iio γ), Q (δ : κ)) ∩ W₀)
    · intro γ
      rw [pdCohMap_comp_apply' (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        (Set.subset_iUnion (fun γ' : κ => Z.proj ⁻¹' (Q γ' ∩ W₀)) γ)
        (Set.iUnion_subset fun γ' => Set.preimage_mono Set.inter_subset_right) n y]
      rw [pdCohMap_congr (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
        _ (Set.preimage_mono Set.inter_subset_right) n y]
      exact key γ
  -- conclude `y = 0`
  have hUniv : (⋃ γ : κ, Z.proj ⁻¹' (Q γ ∩ W₀)) = Z.proj ⁻¹' W₀ := by
    rw [iUnion_preimage_inter Z Q W₀]
    congr 1
    exact Set.inter_eq_right.mpr hWcov
  have hUn2 : (⋃ γ : κ, Z.proj ⁻¹' (Q γ ∩ W₀)) ⊆ Z.proj ⁻¹' W₀ :=
    Set.iUnion_subset fun γ => Set.preimage_mono Set.inter_subset_right
  have hcov3 : (⋃ γ : κ, Z.proj ⁻¹' (Q γ ∩ W₀)) ∪ (⋃ γ : κ, Z.proj ⁻¹' (Q γ ∩ W₀))
      = Z.proj ⁻¹' W₀ := by
    rw [Set.union_self]
    exact hUniv
  have hsub3 : Subsingleton (pdCohSub (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      ((⋃ γ : κ, Z.proj ⁻¹' (Q γ ∩ W₀)) ∩ (⋃ γ : κ, Z.proj ⁻¹' (Q γ ∩ W₀))) (n - 1)) := by
    refine subsingleton_pdCohSub_cast ?_ (hlow ((⋃ γ : κ, Q γ) ∩ W₀))
    rw [Set.inter_self, hUniv, Set.inter_eq_right.mpr hWcov]
  have hinj2 := Work.Thom.pdCohSub_pdCohMap_biprod_injective
    (X := TopCat.of Z.TotalSpace) (A := Work.Thom.zeroComplement Z)
    (W := Z.proj ⁻¹' W₀) (U := ⋃ γ : κ, Z.proj ⁻¹' (Q γ ∩ W₀))
    (V := ⋃ γ : κ, Z.proj ⁻¹' (Q γ ∩ W₀))
    (isOpen_iUnion fun γ => hVopen γ) (isOpen_iUnion fun γ => hVopen γ) hUn2 hUn2 hcov3 n hsub3
  exact hinj2 (by simp only [hstep, map_zero])

/-- **A vanishing restriction stays zero when the piece is replaced by an equal piece.** -/
theorem pdCohMap_target_eq_zero (X : TopCat) (A : Set X) {U W W' : Set X} (h : W = W')
    (hWU : W ⊆ U) (hWU' : W' ⊆ U) (k : ℕ) (x : pdCohSub X A U k)
    (hx : (ModuleCat.Hom.hom (pdCohMap X A U W hWU k)) x = 0) :
    (ModuleCat.Hom.hom (pdCohMap X A U W' hWU' k)) x = 0 := by
  rw [pdCohMap_congr X A hWU' (h ▸ hWU) k x, ← pdCohMap_dcast_target_cast X A h hWU k x, hx]
  exact dcast_zero h

/-- **Restriction through an intermediate piece.**  The composite inclusion is an argument, so the
statement applies to a restriction whose inclusion proof is not syntactically the composite. -/
theorem pdCohMap_step (X : TopCat) (A : Set X) {V U W : Set X} (hVU : V ⊆ U) (hUW : U ⊆ W)
    (hVW : V ⊆ W) (k : ℕ) (x : pdCohSub X A W k) :
    (ModuleCat.Hom.hom (pdCohMap X A W V hVW k)) x
      = (ModuleCat.Hom.hom (pdCohMap X A U V hVU k))
          ((ModuleCat.Hom.hom (pdCohMap X A W U hUW k)) x) := by
  rw [pdCohMap_congr X A hVW (hVU.trans hUW) k x, ← pdCohMap_comp_apply' X A hVU hUW k x]

/-- Transport of a transported element. -/
theorem dcast_dcast {X : TopCat} {A S S' : Set X} {k : ℕ} (h : S = S') (z : pdCohSub X A S k) :
    h.symm ▸ (h ▸ z) = z := by
  cases h
  rfl

/-- **Separation for an open cover of a piece, pieces contained in the piece.**  If `P : κ → Set B`
is a well-ordered family of open sets, each contained in the open set `W₀`, covering `W₀`, and a
class of the Thom pair over `W₀` restricts to zero on every `P i`, then it is zero. -/
theorem sep_of_cover_sub {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} (Z : RealBundle B F ι) (n : ℕ) (hn : 1 ≤ n)
    (hlow : ∀ W : Set B, Subsingleton (Work.Thom.PieceCoh Z W (n - 1)))
    {κ : Type} [LinearOrder κ] [WellFoundedLT κ] (P : κ → Set B) (hPopen : ∀ i, IsOpen (P i))
    {W₀ : Set B} (hW₀ : IsOpen W₀) (hPW : ∀ i, P i ⊆ W₀) (hcov : W₀ ⊆ ⋃ i, P i)
    (y : Work.Thom.PieceCoh Z W₀ n)
    (hy : ∀ i : κ, (ModuleCat.Hom.hom (pdCohMap (TopCat.of Z.TotalSpace)
        (Work.Thom.zeroComplement Z) (Z.proj ⁻¹' W₀) (Z.proj ⁻¹' (P i))
        (Set.preimage_mono (hPW i)) n)) y = 0) :
    y = 0 :=
  sep_of_cover Z n hn hlow P hPopen hW₀ hcov y fun i =>
    pdCohMap_target_eq_zero (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
      (congrArg (Z.proj ⁻¹' ·) (Set.inter_eq_left.mpr (hPW i))).symm
      (Set.preimage_mono (hPW i)) (Set.preimage_mono Set.inter_subset_right) n y (hy i)

end

end Work.ThomBordism
