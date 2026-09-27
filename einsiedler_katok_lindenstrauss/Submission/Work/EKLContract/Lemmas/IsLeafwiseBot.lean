import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Diag
import Submission.Work.EKLContract.Lemmas.SL3Topology
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.V_open_one

open MeasureTheory Topology Set
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLContract.Lemmas

open Work.EKLContract


/-! ## The standard-Borel atoms lemma (proved here to keep the file self-contained) -/

/-- For a countably generated measurable space, `MeasurableSpace.mapNatBool` realises the
σ-algebra as the pullback of the product σ-algebra on `ℕ → Bool`. -/
theorem comap_mapNatBool_aux {α : Type*} [m : MeasurableSpace α]
    [h : MeasurableSpace.CountablyGenerated α] :
    MeasurableSpace.comap (MeasurableSpace.mapNatBool α)
      (inferInstance : MeasurableSpace (ℕ → Bool)) = m := by
  refine le_antisymm ?_ ?_
  · exact (MeasurableSpace.measurable_mapNatBool α).comap_le
  · have hm :
        MeasurableSpace.generateFrom (Set.range (MeasurableSpace.natGeneratingSequence α)) = m :=
      MeasurableSpace.generateFrom_natGeneratingSequence α
    have hle : MeasurableSpace.generateFrom (Set.range (MeasurableSpace.natGeneratingSequence α))
        ≤ MeasurableSpace.comap (MeasurableSpace.mapNatBool α)
            (inferInstance : MeasurableSpace (ℕ → Bool)) := by
      apply MeasurableSpace.generateFrom_le
      rintro s ⟨n, rfl⟩
      have hT : MeasurableSet ({f : ℕ → Bool | f n = true}) := by measurability
      have := (comap_measurable (MeasurableSpace.mapNatBool α)) hT
      convert this using 1
      ext x
      simp [MeasurableSpace.mapNatBool]
    exact (le_of_eq hm.symm).trans hle

/-- If `𝔪` is a countably generated sub-σ-algebra of the Borel σ-algebra of a standard Borel space
`β`, whose atoms at the points of a set `W` are singletons, and `ν` is a finite measure carried by
`W`, then every Borel set is `ν`-a.e. equal to an `𝔪`-measurable set. -/
theorem ae_eq_of_atoms_aux {β : Type*} [TopologicalSpace β] [mb : MeasurableSpace β]
    [BorelSpace β] [hsb : StandardBorelSpace β] (𝔪 : MeasurableSpace β) (hle : 𝔪 ≤ mb)
    (hgen : ∃ b : Set (Set β), b.Countable ∧ 𝔪 = MeasurableSpace.generateFrom b)
    (W : Set β) (hW : MeasurableSet[𝔪] W)
    (hsep : ∀ x ∈ W, ∀ y : β, (∀ s : Set β, MeasurableSet[𝔪] s → (x ∈ s ↔ y ∈ s)) → y = x)
    (ν : @MeasureTheory.Measure β mb) [_hfin : @MeasureTheory.IsFiniteMeasure β mb ν]
    (hν : ν Wᶜ = 0) :
    ∀ B : Set β, MeasurableSet[mb] B →
      ∃ S : Set β, MeasurableSet[𝔪] S ∧ ν (symmDiff B S) = 0 := by
  haveI hcgen : @MeasurableSpace.CountablyGenerated β 𝔪 := ⟨hgen⟩
  let φ : β → (ℕ → Bool) := @MeasurableSpace.mapNatBool β 𝔪 hcgen
  have hcomap : MeasurableSpace.comap φ (inferInstance : MeasurableSpace (ℕ → Bool)) = 𝔪 :=
    @comap_mapNatBool_aux β 𝔪 hcgen
  have hφmeas : Measurable[mb] φ :=
    (@MeasurableSpace.measurable_mapNatBool β 𝔪 hcgen).mono hle le_rfl
  have hWborel : MeasurableSet[mb] W := hle W hW
  have hφinjW : ∀ x ∈ W, ∀ y, φ x = φ y → y = x := by
    intro x hx y hxy
    refine hsep x hx y ?_
    intro s hs
    rw [← hcomap] at hs
    rw [MeasurableSpace.measurableSet_comap] at hs
    obtain ⟨T, -, hTs⟩ := hs
    rw [← hTs]
    simp only [Set.mem_preimage]
    rw [hxy]
  intro B hB
  have hBW : MeasurableSet[mb] (B ∩ W) := hB.inter hWborel
  have hinj : Set.InjOn φ (B ∩ W) := fun x hx y _ hxy => (hφinjW x hx.2 y hxy).symm
  have hT : @MeasurableSet (ℕ → Bool) (inferInstance : MeasurableSpace (ℕ → Bool))
      (φ '' (B ∩ W)) :=
    @MeasurableSet.image_of_measurable_injOn β (ℕ → Bool)
      (inferInstance : MeasurableSpace (ℕ → Bool)) (B ∩ W) φ
      (inferInstance : MeasurableSpace.CountablySeparated (ℕ → Bool)) mb hsb hBW hφmeas hinj
  refine ⟨φ ⁻¹' (φ '' (B ∩ W)), ?_, ?_⟩
  · rw [← hcomap]
    exact hT.preimage (comap_measurable φ)
  · apply le_antisymm _ zero_le
    refine (measure_mono ?_).trans_eq hν
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxW
    have key : x ∈ (φ ⁻¹' (φ '' (B ∩ W))) ↔ x ∈ B := by
      constructor
      · intro hxS
        simp only [Set.mem_preimage, Set.mem_image] at hxS
        obtain ⟨y, hy, hyx⟩ := hxS
        have : y = x := hφinjW x hxW y hyx.symm
        exact this ▸ hy.1
      · intro hxB
        exact ⟨x, ⟨hxB, hxW⟩, rfl⟩
    rw [Set.mem_symmDiff] at hx
    rcases hx with ⟨hxB, hxS⟩ | ⟨hxS, hxB⟩
    · exact hxS (key.mpr hxB)
    · exact hxB (key.mp hxS)

/-! ## A countable cover of `SL₃(ℝ)` by charts of the projection `SL₃(ℝ) → X₃` -/

/-- A countable cover of `SL3` by open sets on which `mkX` is injective. -/
structure X3Cover where
  D : ℕ → Set SL3
  isOpen : ∀ n, IsOpen (D n)
  injOn : ∀ n, Set.InjOn mkX (D n)
  exists_mem : ∀ s : SL3, ∃ n, s ∈ D n

/-- The saturation of a set under the projection `mkX`; it depends only on the image in `X₃`. -/
def sat (E : Set SL3) : Set SL3 := mkX ⁻¹' (mkX '' E)

theorem isOpen_sat {E : Set SL3} (hE : IsOpen E) : IsOpen (sat E) :=
  ((QuotientGroup.isOpenMap_coe : IsOpenMap (mkX : SL3 → X3)) E hE).preimage
    QuotientGroup.continuous_mk

theorem isOpen_iUnion_lt {D : ℕ → Set SL3} (hD : ∀ n, IsOpen (D n)) (n : ℕ) :
    IsOpen (⋃ m : {m // m < n}, D m) :=
  isOpen_iUnion fun m => hD m


/-- If every Borel set is `ν`-a.e. equal to an `𝔪`-measurable set, then a bounded Borel function is
its own `𝔪`-conditional expectation.  (Proved here to keep the file self-contained.) -/
theorem condExp_ae_eq_of_borel_ae_eq {α : Type*} [mα : MeasurableSpace α]
    (𝔪 : MeasurableSpace α) (hle : 𝔪 ≤ mα) (ν : @MeasureTheory.Measure α mα)
    [MeasureTheory.IsFiniteMeasure ν] (f : α → ℝ)
    (hfm : @Measurable α ℝ mα Real.measurableSpace f) (hfbdd : ∃ C, ∀ y, |f y| ≤ C)
    (h : ∀ B : Set α, @MeasurableSet α mα B →
      ∃ S : Set α, @MeasurableSet α 𝔪 S ∧ ν (symmDiff B S) = 0) :
    ∀ᵐ x ∂ν, @MeasureTheory.condExp α ℝ 𝔪 mα _ _ ν f x = f x := by
  obtain ⟨C, hC⟩ := hfbdd
  have hfi : MeasureTheory.Integrable f ν :=
    MeasureTheory.Integrable.of_bound hfm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa using hC x)
  refine MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq
    (MeasureTheory.condExp 𝔪 ν f) f MeasureTheory.integrable_condExp hfi ?_
  intro s hs _
  obtain ⟨S, hS𝔪, hSν⟩ := h s hs
  have hse : s =ᵐ[ν] S := MeasureTheory.measure_symmDiff_eq_zero_iff.mp hSν
  have h1 : ∫ x in s, MeasureTheory.condExp 𝔪 ν f x ∂ν
      = ∫ x in S, MeasureTheory.condExp 𝔪 ν f x ∂ν :=
    MeasureTheory.setIntegral_congr_set hse
  have h2 : ∫ x in S, MeasureTheory.condExp 𝔪 ν f x ∂ν = ∫ x in S, f x ∂ν :=
    MeasureTheory.setIntegral_condExp hle hfi hS𝔪
  have h3 : ∫ x in S, f x ∂ν = ∫ x in s, f x ∂ν :=
    (MeasureTheory.setIntegral_congr_set hse).symm
  exact h1.trans (h2.trans h3)

namespace X3Cover

theorem exists_meet (C : X3Cover) (x : X3) : ∃ n : ℕ, ∃ s ∈ C.D n, mkX s = x := by
  classical
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective x
  obtain ⟨n, hn⟩ := C.exists_mem s
  exact ⟨n, s, hn, hs⟩

/-- The least index `n` with `C.D n` meeting the fibre of `x`. -/
def cidx (C : X3Cover) (x : X3) : ℕ := by classical exact Nat.find (C.exists_meet x)

theorem cidx_spec (C : X3Cover) (x : X3) : ∃ s ∈ C.D (C.cidx x), mkX s = x := by
  classical exact Nat.find_spec (C.exists_meet x)

theorem cidx_min (C : X3Cover) (x : X3) {m : ℕ} (hm : m < C.cidx x) :
    ¬ (∃ s ∈ C.D m, mkX s = x) := by
  classical exact Nat.find_min (C.exists_meet x) hm

theorem cidx_le (C : X3Cover) (x : X3) {n : ℕ} (hn : ∃ s ∈ C.D n, mkX s = x) :
    C.cidx x ≤ n := by
  classical exact Nat.find_min' (C.exists_meet x) hn

/-- The selected representative of `x`. -/
def sect (C : X3Cover) (x : X3) : SL3 := by classical exact (C.cidx_spec x).choose

theorem sect_mem (C : X3Cover) (x : X3) : C.sect x ∈ C.D (C.cidx x) :=
  (C.cidx_spec x).choose_spec.1

theorem mkX_sect (C : X3Cover) (x : X3) : mkX (C.sect x) = x :=
  (C.cidx_spec x).choose_spec.2

theorem sect_eq (C : X3Cover) {x : X3} {s : SL3} (hs : s ∈ C.D (C.cidx x)) (hx : mkX s = x) :
    C.sect x = s :=
  C.injOn (C.cidx x) (C.sect_mem x) hs (by rw [C.mkX_sect x, hx])

theorem sect_sect (C : X3Cover) {s : SL3} (hs : s ∈ Set.range C.sect) : C.sect (mkX s) = s := by
  obtain ⟨x, rfl⟩ := hs
  rw [C.mkX_sect x]

theorem sect_injective (C : X3Cover) : Function.Injective C.sect := by
  intro x y h
  rw [← C.mkX_sect x, h, C.mkX_sect y]

theorem mem_range_sect_iff (C : X3Cover) (s : SL3) :
    s ∈ Set.range C.sect ↔ C.sect (mkX s) = s :=
  ⟨fun h => C.sect_sect h, fun h => ⟨mkX s, h⟩⟩

theorem range_sect (C : X3Cover) :
    Set.range C.sect =
      ⋃ n : ℕ, (C.D n \ sat (⋃ m : {m // m < n}, C.D m)) := by
  ext s
  constructor
  · intro hs
    obtain ⟨x, rfl⟩ := hs
    refine mem_iUnion.2 ⟨C.cidx x, C.sect_mem x, ?_⟩
    rintro ⟨t, ht, htx⟩
    rcases mem_iUnion.1 ht with ⟨m, hm⟩
    exact C.cidx_min x m.2 ⟨t, hm, by rw [htx, C.mkX_sect x]⟩
  · intro hs
    rcases mem_iUnion.1 hs with ⟨n, hsn, hnotin⟩
    have hmem : ∃ t ∈ C.D n, mkX t = mkX s := ⟨s, hsn, rfl⟩
    have hle := C.cidx_le (mkX s) hmem
    have hk : C.cidx (mkX s) = n := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · exfalso
        obtain ⟨t, ht, ht2⟩ := C.cidx_spec (mkX s)
        exact hnotin ⟨t, mem_iUnion.2 ⟨⟨C.cidx (mkX s), hlt⟩, ht⟩, ht2⟩
      · exact heq
    exact ⟨mkX s, C.sect_eq (by rw [hk]; exact hsn) rfl⟩

theorem measurableSet_range_sect (C : X3Cover) : MeasurableSet (Set.range C.sect) := by
  rw [C.range_sect]
  refine MeasurableSet.iUnion fun n => ?_
  exact (C.isOpen n).measurableSet.diff
    (isOpen_sat (isOpen_iUnion_lt C.isOpen n)).measurableSet

/-- `mkX` is injective on the range of a section. -/
theorem injOn_range_sect (C : X3Cover) : Set.InjOn mkX (Set.range C.sect) := by
  intro a ha b hb hab
  rw [← C.sect_sect ha, ← C.sect_sect hb, hab]

/-- The projection `SL3 → X3` is locally injective, since `Γ3` is discrete at `1`; hence, as `SL3`
is second countable, one can cover `SL3` by countably many open charts of `mkX`. -/
theorem nonempty_of (h2c : SecondCountableTopology SL3)
    (hV : ∃ V : Set SL3, IsOpen V ∧ (1 : SL3) ∈ V ∧
      ∀ a ∈ V, ∀ b ∈ V, a⁻¹ * b ∈ Γ3 → a = b) : Nonempty X3Cover := by
  classical
  haveI : SecondCountableTopology SL3 := h2c
  haveI : TopologicalSpace.SeparableSpace SL3 :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  obtain ⟨V, hVo, h1V, hVinj⟩ := hV
  set V' : Set SL3 := V ∩ (fun x : SL3 => x⁻¹) '' V with hV'def
  have hV'o : IsOpen V' := hVo.inter ((Homeomorph.inv SL3).isOpenMap V hVo)
  have h1V' : (1 : SL3) ∈ V' := ⟨h1V, ⟨1, h1V, by simp⟩⟩
  have hV'inj : ∀ a ∈ V', ∀ b ∈ V', a⁻¹ * b ∈ Γ3 → a = b :=
    fun a ha b hb h => hVinj a ha.1 b hb.1 h
  have hV'symm : ∀ x ∈ V', x⁻¹ ∈ V' := by
    rintro x ⟨hxV, y, hyV, hyx⟩
    have hxinv : x⁻¹ = y := by rw [← hyx]; simp
    exact ⟨hxinv ▸ hyV, ⟨x, hxV, rfl⟩⟩
  refine ⟨{ D := fun n => (fun y : SL3 => TopologicalSpace.denseSeq SL3 n * y) '' V',
            isOpen := ?_, injOn := ?_, exists_mem := ?_ }⟩
  · intro n
    exact (Homeomorph.mulLeft (TopologicalSpace.denseSeq SL3 n)).isOpenMap V' hV'o
  · intro n u hu v hv huv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    have h1 : ((TopologicalSpace.denseSeq SL3 n * a)⁻¹ *
        (TopologicalSpace.denseSeq SL3 n * b)) ∈ Γ3 := by
      change QuotientGroup.mk (TopologicalSpace.denseSeq SL3 n * a) =
        QuotientGroup.mk (TopologicalSpace.denseSeq SL3 n * b) at huv
      rwa [QuotientGroup.eq] at huv
    have h2 : ((TopologicalSpace.denseSeq SL3 n * a)⁻¹ *
        (TopologicalSpace.denseSeq SL3 n * b)) = a⁻¹ * b := by group
    rw [h2] at h1
    rw [hV'inj a ha b hb h1]
  · intro s
    have hmem : s ∈ (fun y : SL3 => s * y) '' V' := ⟨1, h1V', by simp⟩
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq (α := SL3)).exists_mem_open
      ((Homeomorph.mulLeft s).isOpenMap V' hV'o) ⟨s, hmem⟩
    obtain ⟨v, hv, hsv⟩ := hn
    refine ⟨n, v⁻¹, hV'symm v hv, ?_⟩
    have hmul : (Homeomorph.mulLeft s) v = s * v := rfl
    rw [hmul] at hsv
    rw [← hsv]
    group

/-! ## Measurability of the section, and transfer of measure-theoretic statements

The range of `sect` is a Borel subset of the standard Borel space `SL3` on which `mkX` is injective,
so it is Borel isomorphic to `X₃`.  This lets us transfer the "standard Borel atoms" statement to
`X₃`. -/

theorem measurable_sect (C : X3Cover) (hSB : StandardBorelSpace SL3)
    (hCS : @MeasurableSpace.CountablySeparated X3 instMeasurableSpaceX3) :
    @Measurable X3 SL3 instMeasurableSpaceX3 instMeasurableSpaceSL3 (fun x : X3 => C.sect x) := by
  haveI : MeasurableSpace.CountablySeparated X3 := hCS
  intro A' hA'
  have h : C.sect ⁻¹' A' = mkX '' (A' ∩ Set.range C.sect) := by
    ext x
    rw [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hx
      exact ⟨C.sect x, ⟨hx, ⟨x, rfl⟩⟩, C.mkX_sect x⟩
    · rintro ⟨s, ⟨hsA, hsrange⟩, hms⟩
      rw [← hms, C.sect_sect hsrange]
      exact hsA
  rw [h]
  exact MeasurableSet.image_of_measurable_injOn (hA'.inter C.measurableSet_range_sect)
    QuotientGroup.continuous_mk.measurable (C.injOn_range_sect.mono fun _ hx => hx.2)

/-- **Transfer to `X₃`.** If `𝔪` is a countably generated sub-σ-algebra of the Borel σ-algebra of
`X₃` whose atoms at the points of a set `Z` are singletons, and `ν` is a finite measure carried by
`Z`, then every Borel subset of `X₃` agrees with an `𝔪`-set up to a `ν`-null set. -/
theorem borel_ae_eq_of_atoms (C : X3Cover) (hSB : StandardBorelSpace SL3)
    (hCS : @MeasurableSpace.CountablySeparated X3 instMeasurableSpaceX3)
    (ν : MeasureTheory.Measure X3) [MeasureTheory.IsFiniteMeasure ν]
    (Z : Set X3) (m : MeasurableSpace X3) (hle : m ≤ instMeasurableSpaceX3)
    (hgen : ∃ b : Set (Set X3), b.Countable ∧ m = MeasurableSpace.generateFrom b)
    (hZ : @MeasurableSet X3 m Z)
    (hsep : ∀ x ∈ Z, ∀ y : X3, (∀ s : Set X3, @MeasurableSet X3 m s → (x ∈ s ↔ y ∈ s)) → y = x)
    (hν : ν Zᶜ = 0) :
    ∀ B : Set X3, @MeasurableSet X3 instMeasurableSpaceX3 B →
      ∃ S : Set X3, @MeasurableSet X3 m S ∧ ν (symmDiff B S) = 0 := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  haveI : StandardBorelSpace SL3 := hSB
  haveI : MeasurableSpace.CountablySeparated X3 := hCS
  haveI : StandardBorelSpace (Set.range C.sect) := C.measurableSet_range_sect.standardBorel
  -- the section, viewed as a map into its range
  let e : X3 → Set.range C.sect := fun x => ⟨C.sect x, ⟨x, rfl⟩⟩
  have he_meas : Measurable e := (measurable_sect C hSB hCS).subtype_mk
  -- the projection restricted to that range
  let g : Set.range C.sect → X3 := fun y => mkX (y : SL3)
  have hg_meas : Measurable g :=
    QuotientGroup.continuous_mk.measurable.comp continuous_subtype_val.measurable
  -- the pulled back σ-algebra
  have hle' : MeasurableSpace.comap g m ≤
      (inferInstance : MeasurableSpace (Set.range C.sect)) :=
    (MeasurableSpace.comap_mono hle).trans hg_meas.comap_le
  have hgen' : ∃ b : Set (Set (Set.range C.sect)), b.Countable ∧
      MeasurableSpace.comap g m = MeasurableSpace.generateFrom b := by
    obtain ⟨b, hbc, hb⟩ := hgen
    refine ⟨(fun s : Set X3 => g ⁻¹' s) '' b, hbc.image _, ?_⟩
    rw [hb, MeasurableSpace.comap_generateFrom]
  -- the "good" set
  let W' : Set (Set.range C.sect) := g ⁻¹' Z
  have hpre : ∀ (A : Set X3), @MeasurableSet X3 m A →
      @MeasurableSet (Set.range C.sect) (MeasurableSpace.comap g m) (g ⁻¹' A) := by
    intro A hA
    letI : MeasurableSpace (Set.range C.sect) := MeasurableSpace.comap g m
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨A, hA, rfl⟩
  have hW' : @MeasurableSet (Set.range C.sect) (MeasurableSpace.comap g m) W' :=
    hpre Z hZ
  -- the separating hypothesis transfers
  have hcomp : ∀ A : Set X3, e ⁻¹' (g ⁻¹' A) = A := by
    intro A
    ext x
    simp only [Set.mem_preimage, e, g]
    rw [C.mkX_sect x]
  have hsep' : ∀ x ∈ W', ∀ y : Set.range C.sect,
      (∀ s : Set (Set.range C.sect),
        @MeasurableSet (Set.range C.sect) (MeasurableSpace.comap g m) s → (x ∈ s ↔ y ∈ s)) →
      y = x := by
    intro x hx y hy
    have hxZ : g x ∈ Z := hx
    have hgxy : g y = g x := by
      refine hsep (g x) hxZ (g y) ?_
      intro s hs
      exact hy (g ⁻¹' s) (hpre s hs)
    have hx' : x = ⟨C.sect (g x), ⟨g x, rfl⟩⟩ := Subtype.ext (C.sect_sect x.2).symm
    have hy' : y = ⟨C.sect (g y), ⟨g y, rfl⟩⟩ := Subtype.ext (C.sect_sect y.2).symm
    rw [hy', hgxy, ← hx']
  -- the pushed forward measure
  let ν' : Measure (Set.range C.sect) := Measure.map e ν
  haveI : IsFiniteMeasure ν' := Measure.isFiniteMeasure_map ν e
  have hW'amb : MeasurableSet W' := hle' W' hW'
  have hν' : ν' W'ᶜ = 0 := by
    rw [Measure.map_apply he_meas hW'amb.compl]
    have h1 : e ⁻¹' W'ᶜ = (e ⁻¹' W')ᶜ := Set.preimage_compl
    rw [h1]
    have h2 : e ⁻¹' W' = Z := hcomp Z
    rw [h2, hν]
  -- the standard-Borel statement on the range of the section
  have key : ∀ B' : Set (Set.range C.sect), MeasurableSet B' →
      ∃ S' : Set (Set.range C.sect),
        @MeasurableSet (Set.range C.sect) (MeasurableSpace.comap g m) S' ∧
          ν' (symmDiff B' S') = 0 :=
    ae_eq_of_atoms_aux (mb := (inferInstance : MeasurableSpace (Set.range C.sect)))
      (𝔪 := MeasurableSpace.comap g m) hle' hgen' W' hW' hsep' ν' hν'
  intro B hB
  have hB' : MeasurableSet (g ⁻¹' B) := hg_meas hB
  obtain ⟨S', hS'm, hS'ν⟩ := key (g ⁻¹' B) hB'
  obtain ⟨S, hSm, hSeq⟩ : ∃ S : Set X3, @MeasurableSet X3 m S ∧ g ⁻¹' S = S' := by
    letI : MeasurableSpace (Set.range C.sect) := MeasurableSpace.comap g m
    rw [MeasurableSpace.measurableSet_comap] at hS'm
    exact hS'm
  refine ⟨S, hSm, ?_⟩
  have hsy : symmDiff B S = e ⁻¹' (symmDiff (g ⁻¹' B) S') := by
    rw [Set.preimage_symmDiff, hcomp B, ← hSeq, hcomp S]
  have hS'amb : MeasurableSet S' := hle' S' hS'm
  rw [hsy]
  have hmap : ν' (symmDiff (g ⁻¹' B) S') = ν (e ⁻¹' symmDiff (g ⁻¹' B) S') :=
    Measure.map_apply he_meas (hB'.symmDiff hS'amb)
  rw [← hmap, hS'ν]

end X3Cover

/-! ## The target lemma -/

set_option linter.unusedVariables false

/-- `X₃` is countably separated: it is a second countable T₁ space. -/
theorem countablySeparated_X3 (h2c : SecondCountableTopology SL3)
    (hcl : IsClosed (Γ3 : Set SL3)) :
    @MeasurableSpace.CountablySeparated X3 instMeasurableSpaceX3 := by
  haveI : SecondCountableTopology SL3 := h2c
  haveI : IsClosed (Γ3 : Set SL3) := hcl
  haveI : SecondCountableTopology X3 := QuotientGroup.instSecondCountableTopology (N := Γ3)
  haveI : T1Space X3 := QuotientGroup.instT1Space
  exact inferInstance

open scoped symmDiff

/-- **Leafwise measures for the trivial subgroup.** For any finite measure `μ` on `X₃`, the constant
family of Dirac masses at the identity of `SL₃(ℝ)` is a system of leafwise measures for the trivial
subgroup. -/
theorem IsLeafwiseBot (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsFiniteMeasure μ] : Work.EKLContract.IsLeafwise μ (⊥ : Subgroup Work.EKLContract.SL3) (fun _ : Work.EKLContract.X3 => MeasureTheory.Measure.dirac (1 : Work.EKLContract.SL3)) Set.univ := by
  haveI hSB : StandardBorelSpace SL3 := SL3Topology.1
  haveI h2c : SecondCountableTopology SL3 := SL3Topology.2
  have hΓ := Gamma3Facts
  haveI hΓct : Countable Γ3 := hΓ.1
  haveI hΓcl : IsClosed (Γ3 : Set SL3) := hΓ.2.1
  haveI hΓint : ∀ γ : SL3, γ ∈ Γ3 → ∀ i j : Fin 3, ∃ k : ℤ,
      (γ : Matrix (Fin 3) (Fin 3) ℝ) i j = k := hΓ.2.2.1
  haveI hCS : @MeasurableSpace.CountablySeparated X3 instMeasurableSpaceX3 :=
    countablySeparated_X3 h2c hΓcl
  obtain ⟨C⟩ := X3Cover.nonempty_of h2c hΓ.2.2.2
  refine ⟨MeasurableSet.univ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro x hx
    refine ⟨fun K hK => ?_⟩
    calc Measure.dirac (1 : SL3) K ≤ Measure.dirac (1 : SL3) Set.univ :=
          measure_mono (Set.subset_univ K)
      _ = 1 := Measure.dirac_apply_of_mem (Set.mem_univ 1)
      _ < ⊤ := ENNReal.one_lt_top
  · intro x hx
    rw [Measure.dirac_apply]
    simp
  · intro x hx
    have hBox : Box1 (⊥ : Subgroup SL3) = {1} := by
      ext g
      constructor
      · intro hg
        exact Set.mem_singleton_iff.mpr (Subgroup.mem_bot.mp hg.1)
      · intro hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        refine ⟨Subgroup.mem_bot.mpr rfl, ?_⟩
        intro i j
        simp
    rw [hBox]
    exact Measure.dirac_apply_of_mem (Set.mem_singleton 1)
  · intro f
    exact measurable_const
  · intro x hx δ hδ
    rw [Measure.dirac_apply_of_mem (V_open_one δ hδ).2]
    exact zero_lt_one
  · intro x hx u hu hux
    obtain hu1 : u = 1 := Subgroup.mem_bot.mp hu
    subst hu1
    refine ⟨1, one_ne_zero, ENNReal.one_ne_top, ?_⟩
    rw [one_smul, Measure.map_dirac]
    simp
  · intro Z m hpl f hfm hfbdd
    have hle : m ≤ instMeasurableSpaceX3 := hpl.1
    have hgen : ∃ b : Set (Set X3), b.Countable ∧ m = MeasurableSpace.generateFrom b := hpl.2.1
    have hZ : @MeasurableSet X3 m Z := hpl.2.2.1
    have hrest := hpl.2.2.2
    have hxatom : ∀ y : X3, y ∈ atom m y := fun y => by
      simp only [atom, Set.mem_sInter]
      intro s hs
      exact hs.2
    have hatom : ∀ x ∈ Z, atom m x = {x} := by
      intro x hx
      have himg : (fun u : SL3 => u • x) '' (⊥ : Subgroup SL3) = {x} := by
        ext y
        constructor
        · rintro ⟨u, hu, rfl⟩
          rw [Subgroup.mem_bot.mp hu]
          simp
        · intro hy
          rw [Set.mem_singleton_iff] at hy
          exact ⟨1, Subgroup.mem_bot.mpr rfl, by rw [hy]; simp⟩
      exact Set.Subset.antisymm ((Set.Subset.trans (hrest x hx).2.1 (le_of_eq himg)))
        (fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hxatom x)
    have hsep : ∀ x ∈ Z, ∀ y : X3,
        (∀ s : Set X3, @MeasurableSet X3 m s → (x ∈ s ↔ y ∈ s)) → y = x := by
      intro x hx y hy
      have hyatom : y ∈ atom m x := by
        simp only [atom, Set.mem_sInter]
        intro s hs
        exact (hy s hs.1).mp hs.2
      rw [hatom x hx] at hyatom
      exact Set.mem_singleton_iff.mp hyatom
    have hν : (μ.restrict Z) Zᶜ = 0 := by
      rw [Measure.restrict_apply ((hle Z hZ).compl)]
      simp
    have htr := X3Cover.borel_ae_eq_of_atoms C hSB hCS (μ.restrict Z) Z m hle hgen hZ hsep hν
    have hcond := condExp_ae_eq_of_borel_ae_eq (mα := instMeasurableSpaceX3) m hle
      (μ.restrict Z) f hfm hfbdd htr
    filter_upwards [hcond] with x hx
    rw [hx]
    have hshape : shape m (⊥ : Subgroup SL3) x = {1} := by
      ext u
      constructor
      · intro hu
        rw [Set.mem_singleton_iff]
        exact Subgroup.mem_bot.mp hu.1
      · intro hu
        rw [Set.mem_singleton_iff] at hu
        rw [hu]
        exact ⟨Subgroup.mem_bot.mpr rfl, by simpa using hxatom x⟩
    have hden : ((Measure.dirac (1 : SL3)) ({1} : Set SL3)).toReal = 1 := by
      rw [Measure.dirac_apply_of_mem (Set.mem_singleton 1)]
      simp
    rw [hshape, setIntegral_dirac, if_pos (Set.mem_singleton 1), hden, div_one]
    simp

end Work.EKLContract.Lemmas

end
